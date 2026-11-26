/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.Multigraph.MinimumSpanningForest
public import CslibFrontier.Algorithms.Lean.Query.Sort.LEQuery.KeyOracle
public import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

/-!
# Binary MSF Decision Trees, Bitmask Encodings, and Optimal Depth

Foundational comparison decision-tree infrastructure toward Theorem 5.8 of
[PettieRamachandran2002] (#8624), supporting Section 4.1 (p. 23) and Section 5.1 (pp. 25–26).
Defines binary comparison decision trees (`MSFTree`, `MSFDT`) for computing minimum spanning
forests (`Cslib.Multigraph.msf`) over edge-weight permutations, canonical bitmask-indexed simple
graphs (`maskEdgePairs`, `endsOfMask`), optimal comparison depth `optDepth`, complete normalized
trees (`MSFDT.padTo`), and the compilation `msfTreeOfFreeM` from any comparison-query algorithm
`FreeM (LEQuery (Fin e)) α`.

## Main definitions

* `Cslib.Query.MinimumSpanningForest.MSFTree`, `Cslib.Query.MinimumSpanningForest.MSFDT`:
  binary comparison decision trees over `Fin e` edges.
* `Cslib.Query.MinimumSpanningForest.MSFDT.Correct`: correctness against `Cslib.Multigraph.msf`
  for all edge-weight permutations.
* `Cslib.Query.MinimumSpanningForest.optDepth`: minimum worst-case comparison depth `T*(G)` of
  an MSF decision tree on a fixed multigraph `ends : Fin e → Sym2 (Fin n)`.
* `Cslib.Query.MinimumSpanningForest.maskEdgePairs`,
  `Cslib.Query.MinimumSpanningForest.endsOfMask`: canonical simple-graph encoding by edge-pair
  bitmasks.
* `Cslib.Query.MinimumSpanningForest.msfTreeOfFreeM`: compile a `FreeM (LEQuery (Fin e)) α`
  program into a decision tree evaluated under `Cslib.Query.LEQuery.keyOracle`.

## Main results

* `Cslib.Query.MinimumSpanningForest.exists_opt_msfDT`: existence of a depth-optimal MSF
  decision tree.
* `Cslib.Query.MinimumSpanningForest.exists_complete_correct_iff`: characterization of `optDepth`
  by complete decision trees of uniform depth.
* `Cslib.Query.MinimumSpanningForest.optDepth_le_of_freeM`: any comparison-query algorithm
  computing `Cslib.Multigraph.msf` with at most `D` queries yields `optDepth ends ≤ D`.
-/

public section

namespace Cslib.Query.MinimumSpanningForest

/-! ## Binary Decision Trees and Optimal Depth -/

/-- Binary comparison decision tree over `e` edges returning leaves of type `α`. -/
inductive MSFTree (e : ℕ) (α : Type) where
  /-- Leaf returning answer `ans`. -/
  | leaf (ans : α) : MSFTree e α
  /-- Internal node comparing edges `i` and `j`, branching on `w(i) < w(j)`. -/
  | node (i j : Fin e) (ltChild geChild : MSFTree e α) : MSFTree e α

/-- Binary MSF decision tree returning a spanning forest edge subset in `Fin e`. -/
abbrev MSFDT (e : ℕ) := MSFTree e (Finset (Fin e))

/-- Worst-case comparison depth of a decision tree. -/
@[expose] def MSFTree.depth {e : ℕ} {α : Type} : MSFTree e α → ℕ
  | .leaf _ => 0
  | .node _ _ l r => 1 + max l.depth r.depth

/-- Evaluate a decision tree on edge-weight permutation `p : Equiv.Perm (Fin e)`. -/
@[expose] def MSFTree.eval {e : ℕ} {α : Type} :
    MSFTree e α → Equiv.Perm (Fin e) → α
  | .leaf ans, _ => ans
  | .node i j l r, p => if (p i).val < (p j).val then l.eval p else r.eval p

/-- Map a leaf transformation across a decision tree without changing its comparisons. -/
@[expose] def MSFTree.mapLeaves {e : ℕ} {α β : Type} (f : α → β) :
    MSFTree e α → MSFTree e β
  | .leaf ans => .leaf (f ans)
  | .node i j l r => .node i j (l.mapLeaves f) (r.mapLeaves f)

@[simp]
theorem MSFTree.mapLeaves_depth {e : ℕ} {α β : Type} (f : α → β) (T : MSFTree e α) :
    (T.mapLeaves f).depth = T.depth := by
  induction T with
  | leaf _ => rfl
  | node _ _ _ _ ihl ihr => simp [MSFTree.mapLeaves, MSFTree.depth, ihl, ihr]

@[simp]
theorem MSFTree.mapLeaves_eval {e : ℕ} {α β : Type} (f : α → β) (T : MSFTree e α)
    (p : Equiv.Perm (Fin e)) :
    (T.mapLeaves f).eval p = f (T.eval p) := by
  induction T with
  | leaf _ => rfl
  | node i j l r ihl ihr =>
    simp only [MSFTree.mapLeaves, MSFTree.eval]
    split_ifs <;> assumption

/-- Lift edge comparisons of a decision tree along an edge index map `ι : Fin e₁ → Fin e₂`. -/
@[expose] def MSFTree.liftEmb {e₁ e₂ : ℕ} {α : Type} (ι : Fin e₁ → Fin e₂) :
    MSFTree e₁ α → MSFTree e₂ α
  | .leaf ans => .leaf ans
  | .node i j l r => .node (ι i) (ι j) (l.liftEmb ι) (r.liftEmb ι)

@[simp]
theorem MSFTree.liftEmb_depth {e₁ e₂ : ℕ} {α : Type} (ι : Fin e₁ → Fin e₂)
    (T : MSFTree e₁ α) : (T.liftEmb ι).depth = T.depth := by
  induction T with
  | leaf _ => rfl
  | node _ _ _ _ ihl ihr => simp [MSFTree.liftEmb, MSFTree.depth, ihl, ihr]

theorem MSFTree.liftEmb_eval {e₁ e₂ : ℕ} {α : Type} (ι : Fin e₁ → Fin e₂)
    (T : MSFTree e₁ α) (p₁ : Equiv.Perm (Fin e₁)) (p₂ : Equiv.Perm (Fin e₂))
    (hord : ∀ a b : Fin e₁, (p₁ a).val < (p₁ b).val ↔ (p₂ (ι a)).val < (p₂ (ι b)).val) :
    (T.liftEmb ι).eval p₂ = T.eval p₁ := by
  induction T with
  | leaf _ => rfl
  | node a b l r ihl ihr =>
    dsimp only [MSFTree.liftEmb, MSFTree.eval]
    have h := hord a b
    by_cases hp : (p₁ a).val < (p₁ b).val
    · have hp₂ : (p₂ (ι a)).val < (p₂ (ι b)).val := h.mp hp
      simp [hp, hp₂, ihl]
    · have hp₂ : ¬ ((p₂ (ι a)).val < (p₂ (ι b)).val) := fun x => hp (h.mpr x)
      simp [hp, hp₂, ihr]

/-- Correctness of `T : MSFTree e α` computing `f : Equiv.Perm (Fin e) → α` on `P`. -/
def MSFTree.AgreesOn {e : ℕ} {α : Type} (f : Equiv.Perm (Fin e) → α)
    (P : Finset (Equiv.Perm (Fin e))) (T : MSFTree e α) : Prop :=
  ∀ p ∈ P, T.eval p = f p

theorem MSFTree.agreesOn_iff {e : ℕ} {α : Type} (f : Equiv.Perm (Fin e) → α)
    (P : Finset (Equiv.Perm (Fin e))) (T : MSFTree e α) :
    T.AgreesOn f P ↔ ∀ p ∈ P, T.eval p = f p := Iff.rfl

/-- Correctness of an MSF decision tree `T` for multigraph `ends : Fin e → Sym2 (Fin n)`:
on each `p`, `T.eval p` equals `Cslib.Multigraph.msf ends p Finset.univ`. -/
def MSFDT.Correct {e n : ℕ} (ends : Fin e → Sym2 (Fin n)) (T : MSFDT e) : Prop :=
  ∀ p : Equiv.Perm (Fin e), T.eval p = Cslib.Multigraph.msf ends p Finset.univ

theorem MSFDT.correct_iff {e n : ℕ} (ends : Fin e → Sym2 (Fin n)) (T : MSFDT e) :
    T.Correct ends ↔ ∀ p : Equiv.Perm (Fin e), T.eval p = Cslib.Multigraph.msf ends p Finset.univ :=
  Iff.rfl

/-- `Cslib.Multigraph.msf` depends on edge weights only through their strict order relation. -/
theorem msf_congr_lt {E V W₁ W₂ : Type*} [LinearOrder W₁] [LinearOrder W₂]
    (ends : E → Sym2 V) (w₁ : E → W₁) (w₂ : E → W₂) (S : Finset E)
    (h : ∀ a b, w₁ a < w₁ b ↔ w₂ a < w₂ b) :
    Cslib.Multigraph.msf ends w₁ S = Cslib.Multigraph.msf ends w₂ S := by
  classical
  ext e
  induction he : ends e using Sym2.ind with
  | _ a b =>
    rw [Cslib.Multigraph.mem_msf_iff w₁ he, Cslib.Multigraph.mem_msf_iff w₂ he]
    have hset : {f | f ∈ S ∧ w₁ f < w₁ e} = {f | f ∈ S ∧ w₂ f < w₂ e} := by
      ext f
      simp only [Set.mem_ofPred_eq, h]
    rw [hset]

private noncomputable def orderRank {e : ℕ} {W : Type*} [LinearOrder W]
    (w : Fin e → W) (i : Fin e) : Fin e :=
  letI := Classical.propDecidable
  ⟨(Finset.univ.filter fun j : Fin e => w j < w i).card, by
    have hss : Finset.univ.filter (fun j : Fin e => w j < w i) ⊂ Finset.univ := by
      rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
      exact ⟨i, Finset.mem_univ i, by simp⟩
    simpa using Finset.card_lt_card hss⟩

private theorem orderRank_lt_iff {e : ℕ} {W : Type*} [LinearOrder W]
    (w : Fin e → W) (hw : Function.Injective w) (a b : Fin e) :
    orderRank w a < orderRank w b ↔ w a < w b := by
  have hlt_sub : ∀ {x y : Fin e}, w x < w y →
      (orderRank w x).val < (orderRank w y).val := fun {x y} hxy => by
    let _ := Classical.propDecidable
    have hsub : Finset.univ.filter (fun j => w j < w x) ⊂
        Finset.univ.filter (fun j => w j < w y) := by
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩, by simp⟩
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact lt_trans hj hxy
    exact Finset.card_lt_card hsub
  constructor
  · intro hlt
    change (orderRank w a).val < (orderRank w b).val at hlt
    by_contra hnot
    rcases lt_trichotomy (w a) (w b) with hab | heq | hba
    · exact hnot hab
    · have hne : a = b := hw heq
      subst hne
      exact absurd hlt (lt_irrefl _)
    · have hc := hlt_sub hba
      omega
  · exact hlt_sub

/-- Order-preserving rank permutation induced by an injective weight function `w : Fin e → W`. -/
noncomputable def orderPerm {e : ℕ} {W : Type*} [LinearOrder W]
    (w : Fin e → W) (hw : Function.Injective w) : Equiv.Perm (Fin e) :=
  Equiv.ofBijective (orderRank w) ((Fintype.bijective_iff_injective_and_card _).mpr ⟨fun a b hab =>
    by
    rcases lt_trichotomy (w a) (w b) with hlt | heq | hlt
    · exact absurd ((orderRank_lt_iff w hw a b).mpr hlt) (by rw [hab]; exact lt_irrefl _)
    · exact hw heq
    · exact absurd ((orderRank_lt_iff w hw b a).mpr hlt) (by rw [hab]; exact lt_irrefl _), rfl⟩)

theorem orderPerm_lt_iff {e : ℕ} {W : Type*} [LinearOrder W]
    (w : Fin e → W) (hw : Function.Injective w) (a b : Fin e) :
    orderPerm w hw a < orderPerm w hw b ↔ w a < w b := by
  dsimp only [orderPerm]
  simp only [Equiv.ofBijective_apply]
  exact orderRank_lt_iff w hw a b

/-! ## Bitmask Encoding of Edge Subsets -/

private def funToMask : ∀ {e : ℕ}, (Fin e → Bool) → ℕ
  | 0, _ => 0
  | _ + 1, f => (if f 0 then 1 else 0) + 2 * funToMask (fun j => f j.succ)

private theorem testBit_funToMask {e : ℕ} (f : Fin e → Bool) (k : ℕ) :
    (funToMask f).testBit k = if h : k < e then f ⟨k, h⟩ else false := by
  induction e generalizing k with
  | zero => simp [funToMask]
  | succ e ih =>
    cases k with
    | zero =>
      simp only [funToMask, Nat.zero_lt_succ, ↓reduceDIte]
      rw [Nat.testBit_zero]
      cases h0 : f 0 <;> simp [h0]
    | succ k =>
      have hdiv : (funToMask (e := e + 1) f).testBit (k + 1) =
          (funToMask (fun j => f j.succ)).testBit k := by
        dsimp only [funToMask]
        rw [Nat.testBit_succ]
        congr 1
        cases f 0
        · simp
        · simp; omega
      rw [hdiv, ih]
      by_cases hke : k < e
      · have hke' : k + 1 < e + 1 := Nat.succ_lt_succ hke
        simp [hke, hke', Fin.succ]
      · have hke' : ¬ (k + 1 < e + 1) := fun h => hke (Nat.lt_of_succ_lt_succ h)
        simp [hke, hke']

private theorem funToMask_lt {e : ℕ} (f : Fin e → Bool) : funToMask f < 2 ^ e := by
  induction e with
  | zero => simp [funToMask]
  | succ e ih =>
    have hrec := ih (fun j => f j.succ)
    dsimp only [funToMask]
    rw [pow_succ']
    cases f 0
    · simp; omega
    · simp; omega

private theorem sum_fin_ite_eq_funToMask {e : ℕ} (f : Fin e → Bool) :
    (∑ i : Fin e, if f i then (2 : ℕ) ^ i.val else 0) = funToMask f := by
  induction e with
  | zero => simp [funToMask]
  | succ e ih =>
    rw [Fin.sum_univ_succ, funToMask]
    have hrest : (∑ i : Fin e, if f i.succ then (2 : ℕ) ^ (i.succ).val else 0) =
        2 * ∑ i : Fin e, if f i.succ then (2 : ℕ) ^ i.val else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      cases f i.succ
      · simp
      · simp [Fin.val_succ, pow_succ']
    rw [hrest, ih]
    simp

/-- Bitmask `∑ i ∈ S, 2 ^ i.val` encoding `S : Finset (Fin e)` as a natural number `< 2 ^ e`. -/
@[expose] def maskOfFinset {e : ℕ} (S : Finset (Fin e)) : ℕ :=
  ∑ i ∈ S, 2 ^ i.val

private theorem maskOfFinset_eq_funToMask {e : ℕ} (S : Finset (Fin e)) :
    maskOfFinset S = funToMask (fun i => decide (i ∈ S)) := by
  rw [maskOfFinset, ← sum_fin_ite_eq_funToMask, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp

theorem testBit_maskOfFinset {e : ℕ} (S : Finset (Fin e)) (k : ℕ) :
    (maskOfFinset S).testBit k = decide (∃ h : k < e, ⟨k, h⟩ ∈ S) := by
  rw [maskOfFinset_eq_funToMask, testBit_funToMask]
  by_cases h : k < e <;> simp [h]

theorem maskOfFinset_lt {e : ℕ} (S : Finset (Fin e)) : maskOfFinset S < 2 ^ e := by
  rw [maskOfFinset_eq_funToMask]
  exact funToMask_lt _

/-! ## Pair Indexing and Canonical Enumeration of Unordered Pairs -/

/-- Index `b * (b - 1) / 2 + a` of unordered pair `{a, b}` with `a < b`. -/
@[expose] def pairIdx (a b : ℕ) : ℕ :=
  b * (b - 1) / 2 + a

theorem pairIdx_lt_choose_two {a b r : ℕ} (hab : a < b) (hb : b < r) :
    pairIdx a b < r.choose 2 := by
  have hmon : (b + 1).choose 2 ≤ r.choose 2 := Nat.choose_le_choose 2 hb
  have hsucc : (b + 1).choose 2 = b.choose 2 + b := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
  dsimp only [pairIdx]
  rw [hsucc, Nat.choose_two_right] at hmon
  omega

/-- Canonical ordered list of all `(a, b) : Fin r × Fin r` with `a.val < b.val`, ordered by
`pairIdx a.val b.val`. -/
@[expose] def allPairs (r : ℕ) : List (Fin r × Fin r) :=
  (List.finRange r).flatMap fun b => (List.finRange b.val).map fun a => (⟨a.val, by omega⟩, b)

private theorem allPairs_prefix_sum : ∀ (r k : ℕ), k ≤ r →
    (((List.finRange r).take k).map
      (fun b : Fin r => ((List.finRange b.val).map fun a =>
        ((⟨a.val, by omega⟩ : Fin r), b)).length)).sum = k.choose 2
  | r, 0, _ => by simp
  | r, k + 1, hk => by
    have htake : (List.finRange r).take (k + 1) =
        (List.finRange r).take k ++ [⟨k, hk⟩] := by
      have hlen : k < (List.finRange r).length := by simpa using hk
      rw [List.take_add_one, List.getElem?_eq_getElem hlen]
      simp [List.getElem_finRange]
    rw [htake, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      allPairs_prefix_sum r k (by omega), List.length_map, List.length_finRange]
    rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]

theorem length_allPairs (r : ℕ) : (allPairs r).length = r.choose 2 := by
  rw [allPairs, List.length_flatMap]
  have h := allPairs_prefix_sum r r le_rfl
  have htake : (List.finRange r).take r = List.finRange r :=
    List.take_of_length_le (by simp)
  rw [htake] at h
  exact h

theorem getElem_allPairs_pairIdx {r : ℕ} {a b : Fin r} (hab : a.val < b.val) :
    (allPairs r)[pairIdx a.val b.val]'(by
      rw [length_allPairs]; exact pairIdx_lt_choose_two hab b.isLt) = (a, b) := by
  let rowFn : Fin r → List (Fin r × Fin r) := fun b =>
    (List.finRange b.val).map fun a => (⟨a.val, by omega⟩, b)
  have hb_lt : b.val < (List.finRange r).length := by simp
  have hsplit : List.finRange r =
      (List.finRange r).take b.val ++ b :: (List.finRange r).drop (b.val + 1) := by
    have h := List.take_append_drop b.val (List.finRange r)
    rw [← List.getElem_cons_drop hb_lt] at h
    simpa [List.getElem_finRange] using h.symm
  have hflat : allPairs r =
      ((List.finRange r).take b.val).flatMap rowFn ++
        (rowFn b ++ ((List.finRange r).drop (b.val + 1)).flatMap rowFn) := by
    rw [allPairs]
    change (List.finRange r).flatMap rowFn = _
    conv_lhs => rw [hsplit]
    simp [List.flatMap_append]
  have hpre_len : (((List.finRange r).take b.val).flatMap rowFn).length =
      b.val * (b.val - 1) / 2 := by
    rw [List.length_flatMap, allPairs_prefix_sum r b.val b.isLt.le, Nat.choose_two_right]
  have hidx_eq : pairIdx a.val b.val =
      (((List.finRange r).take b.val).flatMap rowFn).length + a.val := by
    rw [hpre_len]; rfl
  have ha_len : a.val < (rowFn b).length := by simp [rowFn, hab]
  have hge :
      (((List.finRange r).take b.val).flatMap rowFn).length ≤ pairIdx a.val b.val := by
    omega
  rw [List.getElem_of_eq hflat]
  rw [List.getElem_append_right hge]
  have ha_sub : pairIdx a.val b.val -
      (((List.finRange r).take b.val).flatMap rowFn).length = a.val := by
    omega
  have ha_sub_lt : pairIdx a.val b.val -
      (((List.finRange r).take b.val).flatMap rowFn).length < (rowFn b).length := by
    rw [ha_sub]; exact ha_len
  rw [List.getElem_append_left ha_sub_lt]
  have hrow : (rowFn b)[a.val]'ha_len = (a, b) := by
    simp [rowFn, List.getElem_map, List.getElem_finRange]
  simp_rw [ha_sub]
  exact hrow

theorem mem_allPairs_iff {r : ℕ} {a b : Fin r} :
    (a, b) ∈ allPairs r ↔ a.val < b.val := by
  constructor
  · intro h
    rw [allPairs, List.mem_flatMap] at h
    obtain ⟨b', _, hrow⟩ := h
    rw [List.mem_map] at hrow
    obtain ⟨a', _, heq⟩ := hrow
    have ha' : a'.val = a.val := congrArg (fun p : Fin r × Fin r => p.1.val) heq
    have hb' : b' = b := congrArg Prod.snd heq
    rw [← hb', ← ha']
    exact a'.isLt
  · intro hab
    rw [← getElem_allPairs_pairIdx hab]
    exact List.getElem_mem _

theorem allPairs_lt {r : ℕ} {p : Fin r × Fin r} (hp : p ∈ allPairs r) : p.1.val < p.2.val :=
  mem_allPairs_iff.mp hp

theorem nodup_allPairs (r : ℕ) : (allPairs r).Nodup := by
  rw [allPairs, List.nodup_flatMap]
  refine ⟨fun b _ => (List.nodup_finRange b.val).map fun x y h =>
      Fin.ext (congrArg (fun p : Fin r × Fin r => p.1.val) h), ?_⟩
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij x hx1 hx2
  simp only [List.mem_map, List.mem_finRange] at hx1 hx2
  rcases hx1 with ⟨_, _, rfl⟩
  rcases hx2 with ⟨_, _, heq⟩
  have hfin := congrArg (fun p : Fin r × Fin r => p.2.val) heq
  dsimp only at hfin
  simp only [List.getElem_finRange, Fin.val_cast] at hfin
  exact Nat.ne_of_lt hij hfin.symm

theorem pairIdx_getElem_allPairs {r k : ℕ} (hk : k < (allPairs r).length) :
    pairIdx ((allPairs r)[k]).1.val ((allPairs r)[k]).2.val = k := by
  let p := (allPairs r)[k]
  have hp : p.1.val < p.2.val := allPairs_lt (List.getElem_mem hk)
  have hlt : pairIdx p.1.val p.2.val < (allPairs r).length := by
    rw [length_allPairs]
    exact pairIdx_lt_choose_two hp p.2.isLt
  have heq : (allPairs r)[pairIdx p.1.val p.2.val]'hlt = p := getElem_allPairs_pairIdx hp
  exact ((nodup_allPairs r).getElem_inj_iff (i := pairIdx p.1.val p.2.val) (j := k)).mp heq

/-! ## Canonical Bitmask Simple Graphs -/

private def filterMaskAux {α : Type} (mask : ℕ) : List α → ℕ → List α
  | [], _ => []
  | x :: xs, idx =>
    if mask.testBit idx then x :: filterMaskAux mask xs (idx + 1)
    else filterMaskAux mask xs (idx + 1)

private theorem filterMaskAux_eq_zipIdx {α : Type} (mask : ℕ) (xs : List α) (idx : ℕ) :
    filterMaskAux mask xs idx =
      ((xs.zipIdx idx).filter fun p => mask.testBit p.2).map Prod.fst := by
  induction xs generalizing idx with
  | nil => rfl
  | cons x xs ih =>
    simp only [filterMaskAux, List.zipIdx_cons, List.filter_cons]
    split_ifs <;> simp [ih]

/-- Edge pairs of the canonical simple graph on `r` vertices encoded by bitmask `mask`. -/
@[expose] def maskEdgePairs (r mask : ℕ) : List (Fin r × Fin r) :=
  ((allPairs r).zipIdx.filter fun p => mask.testBit p.2).map Prod.fst

private theorem maskEdgePairs_eq_filterMaskAux (r mask : ℕ) :
    maskEdgePairs r mask = filterMaskAux mask (allPairs r) 0 :=
  (filterMaskAux_eq_zipIdx mask (allPairs r) 0).symm

/-- Canonical simple multigraph on `r` vertices whose edge list corresponds to bitmask `mask`. -/
@[expose] def endsOfMask (r mask : ℕ) : Fin (maskEdgePairs r mask).length → Sym2 (Fin r) :=
  fun i => s((maskEdgePairs r mask)[i].1, (maskEdgePairs r mask)[i].2)

/-- Predicate asserting `ends : Fin e → Sym2 (Fin n)` defines a simple graph (no self-loops
and no parallel edges). -/
def IsSimple {e n : ℕ} (ends : Fin e → Sym2 (Fin n)) : Prop :=
  (∀ i : Fin e, ¬ (ends i).IsDiag) ∧ Function.Injective ends

theorem isSimple_iff {e n : ℕ} (ends : Fin e → Sym2 (Fin n)) :
    IsSimple ends ↔ (∀ i : Fin e, ¬ (ends i).IsDiag) ∧ Function.Injective ends := Iff.rfl

private theorem filterMaskAux_subset {α : Type} (mask : ℕ) (xs : List α) (idx : ℕ) :
    ∀ {x : α}, x ∈ filterMaskAux mask xs idx → x ∈ xs := by
  induction xs generalizing idx with
  | nil => simp [filterMaskAux]
  | cons y ys ih =>
    intro x hx
    dsimp only [filterMaskAux] at hx
    split_ifs at hx
    · rcases List.mem_cons.mp hx with rfl | hmem
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ hmem)
    · exact List.mem_cons_of_mem _ (ih _ hx)

private theorem filterMaskAux_nodup {α : Type} (mask : ℕ) {xs : List α} (hn : xs.Nodup) (idx : ℕ) :
    (filterMaskAux mask xs idx).Nodup := by
  induction xs generalizing idx with
  | nil => simp [filterMaskAux]
  | cons y ys ih =>
    obtain ⟨hy, hys⟩ := List.nodup_cons.mp hn
    dsimp only [filterMaskAux]
    split_ifs
    · exact List.nodup_cons.mpr ⟨fun hm => hy (filterMaskAux_subset mask ys _ hm), ih hys _⟩
    · exact ih hys _

private theorem filterMaskAux_zero_length {α : Type} (mask : ℕ) (xs : List α) (idx : ℕ)
    (h0 : mask = 0) :
    filterMaskAux mask xs idx = [] := by
  subst h0
  induction xs generalizing idx with
  | nil => rfl
  | cons _ _ ih => simp [filterMaskAux, ih]

theorem maskEdgePairs_zero (r : ℕ) : maskEdgePairs r 0 = [] := by
  rw [maskEdgePairs_eq_filterMaskAux]
  exact filterMaskAux_zero_length 0 (allPairs r) 0 rfl

private theorem length_filterMaskAux {α : Type} (mask : ℕ) (xs : List α) (idx : ℕ) :
    (filterMaskAux mask xs idx).length =
      ((Finset.range xs.length).filter fun j => mask.testBit (idx + j)).card := by
  induction xs generalizing idx with
  | nil => simp [filterMaskAux]
  | cons x xs ih =>
    have ih' := ih (idx + 1)
    dsimp only [filterMaskAux]
    let f : ℕ → ℕ := fun j => j + 1
    have hbij : ((Finset.range (xs.length + 1)).filter fun j => mask.testBit (idx + j)) =
        (if mask.testBit idx then {0} else ∅) ∪
          ((Finset.range xs.length).filter fun j => mask.testBit (idx + 1 + j)).image f := by
      ext m
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_image, f]
      constructor
      · rintro ⟨hm, htb⟩
        cases m with
        | zero =>
          left
          have h0 : mask.testBit idx = true := by simpa using htb
          simp [h0]
        | succ m =>
          right
          refine ⟨m, ⟨by omega, ?_⟩, rfl⟩
          rw [show idx + 1 + m = idx + (m + 1) by omega]
          exact htb
      · intro h
        rcases h with h0 | ⟨k, ⟨hk, htb⟩, rfl⟩
        · split_ifs at h0 with htrue
          · have hm0 : m = 0 := Finset.mem_singleton.mp h0
            subst hm0
            exact ⟨Nat.zero_lt_succ _, by simpa using htrue⟩
          · simp at h0
        · refine ⟨by omega, ?_⟩
          rw [show idx + (k + 1) = idx + 1 + k by omega]
          exact htb
    have hdisj : Disjoint (if mask.testBit idx then {0} else ∅)
        (((Finset.range xs.length).filter fun j => mask.testBit (idx + 1 + j)).image f) := by
      rw [Finset.disjoint_left]
      intro m hm1 hm2
      rw [Finset.mem_image] at hm2
      rcases hm2 with ⟨_, _, rfl⟩
      split_ifs at hm1 with ht
      · simp [f] at hm1
      · simp at hm1
    have hcard_img :
        (((Finset.range xs.length).filter fun j => mask.testBit (idx + 1 + j)).image f).card =
          ((Finset.range xs.length).filter fun j => mask.testBit (idx + 1 + j)).card :=
      Finset.card_image_of_injective _ fun _ _ h => Nat.succ_injective h
    rw [List.length_cons, hbij, Finset.card_union_of_disjoint hdisj, hcard_img]
    split_ifs with hb
    · rw [List.length_cons, ih', Finset.card_singleton, Nat.add_comm]
    · rw [ih', Finset.card_empty, Nat.zero_add]

private theorem filterMaskAux_map_append {α β : Type} (f : α → β) (mask : ℕ)
    (xs : List α) (ys : List β) (idx : ℕ)
    (hhi : ∀ k, idx + xs.length ≤ k → mask.testBit k = false) :
    filterMaskAux mask (xs.map f ++ ys) idx = (filterMaskAux mask xs idx).map f := by
  induction xs generalizing idx with
  | nil =>
    induction ys generalizing idx with
    | nil => simp [filterMaskAux]
    | cons y ys ihy =>
      have h0 : mask.testBit idx = false := hhi idx (by simp)
      simp only [List.map_nil, List.nil_append, filterMaskAux, h0, Bool.false_eq_true, ↓reduceIte]
      exact ihy (idx + 1) fun k hk => hhi k (by simp at hk ⊢; omega)
  | cons x xs ih =>
    have hhi' : ∀ k, idx + 1 + xs.length ≤ k → mask.testBit k = false := fun k hk =>
      hhi k (by simp [List.length_cons] at hk ⊢; omega)
    have hrec := ih (idx + 1) hhi'
    simp only [List.map_cons, List.cons_append, filterMaskAux]
    split_ifs
    · simp [List.map_cons, hrec]
    · exact hrec

private theorem filterMaskAux_bij {α : Type} (mask : ℕ) (xs : List α) (hnd : xs.Nodup) (idx : ℕ) :
    (∀ x ∈ filterMaskAux mask xs idx,
      ∃ j, ∃ hj : j < xs.length, xs[j]'hj = x ∧ mask.testBit (idx + j) = true)
    ∧ (∀ j (hj : j < xs.length), mask.testBit (idx + j) = true →
      xs[j]'hj ∈ filterMaskAux mask xs idx) := by
  induction xs generalizing idx with
  | nil => simp [filterMaskAux]
  | cons y ys ih =>
    obtain ⟨_, hys⟩ := List.nodup_cons.mp hnd
    have ih' := ih hys (idx + 1)
    dsimp only [filterMaskAux]
    constructor
    · intro x hx
      split_ifs at hx with hb
      · rcases List.mem_cons.mp hx with rfl | hmem
        · exact ⟨0, by simp, rfl, hb⟩
        · obtain ⟨j, hj, hget, htb⟩ := ih'.1 x hmem
          refine ⟨j + 1, by simp [hj], by simpa using hget, ?_⟩
          rw [show idx + (j + 1) = idx + 1 + j by omega]
          exact htb
      · obtain ⟨j, hj, hget, htb⟩ := ih'.1 x hx
        refine ⟨j + 1, by simp [hj], by simpa using hget, ?_⟩
        rw [show idx + (j + 1) = idx + 1 + j by omega]
        exact htb
    · intro j hj htb
      cases j with
      | zero =>
        simp only [Nat.add_zero] at htb
        simp [htb]
      | succ j =>
        have htb' : mask.testBit (idx + 1 + j) = true := by
          rw [show idx + 1 + j = idx + (j + 1) by omega]
          exact htb
        have hmem := ih'.2 j (by simpa using hj) htb'
        split_ifs
        · exact List.mem_cons_of_mem _ (by simpa using hmem)
        · simpa using hmem

theorem maskEdgePairs_nodup (r mask : ℕ) : (maskEdgePairs r mask).Nodup := by
  rw [maskEdgePairs_eq_filterMaskAux]
  exact filterMaskAux_nodup mask (nodup_allPairs r) 0

theorem length_maskEdgePairs (r mask : ℕ) :
    (maskEdgePairs r mask).length =
      ((Finset.range (r.choose 2)).filter fun j => mask.testBit j).card := by
  rw [maskEdgePairs_eq_filterMaskAux, length_filterMaskAux, length_allPairs]
  simp only [Nat.zero_add]

theorem mem_maskEdgePairs_iff {r mask : ℕ} {p : Fin r × Fin r} :
    p ∈ maskEdgePairs r mask ↔
      p.1.val < p.2.val ∧ mask.testBit (pairIdx p.1.val p.2.val) = true := by
  rw [maskEdgePairs_eq_filterMaskAux]
  have hspec := filterMaskAux_bij mask (allPairs r) (nodup_allPairs r) 0
  constructor
  · intro hp
    obtain ⟨j, hj, rfl, htb⟩ := hspec.1 p hp
    rw [Nat.zero_add] at htb
    have hlt := allPairs_lt (List.getElem_mem hj)
    have hidx := pairIdx_getElem_allPairs hj
    exact ⟨hlt, by simpa [hidx] using htb⟩
  · rintro ⟨hlt, htb⟩
    have hj : pairIdx p.1.val p.2.val < (allPairs r).length := by
      rw [length_allPairs]
      exact pairIdx_lt_choose_two hlt p.2.isLt
    have hget := getElem_allPairs_pairIdx hlt
    have hmem := hspec.2 (pairIdx p.1.val p.2.val) hj (by simpa using htb)
    rwa [hget] at hmem

theorem maskEdgePairs_cast {r₁ r₂ mask : ℕ} (hrr : r₁ ≤ r₂)
    (hmask : mask < 2 ^ r₁.choose 2) :
    maskEdgePairs r₂ mask =
      (maskEdgePairs r₁ mask).map (Prod.map (Fin.castLE hrr) (Fin.castLE hrr)) := by
  have hlen : r₁.choose 2 ≤ (allPairs r₂).length := by
    rw [length_allPairs]
    exact Nat.choose_le_choose 2 hrr
  have htake : (allPairs r₂).take (r₁.choose 2) =
      (allPairs r₁).map (Prod.map (Fin.castLE hrr) (Fin.castLE hrr)) := by
    refine List.ext_getElem ?_ fun k hk1 hk2 => ?_
    · simp only [List.length_take, List.length_map, length_allPairs]
      rw [length_allPairs] at hlen
      exact Nat.min_eq_left hlen
    · have hk_lt : k < (allPairs r₁).length := by simpa [List.length_map] using hk2
      let p := (allPairs r₁)[k]'hk_lt
      have hplt : p.1.val < p.2.val := allPairs_lt (List.getElem_mem hk_lt)
      have hpidx : pairIdx p.1.val p.2.val = k := pairIdx_getElem_allPairs hk_lt
      rw [List.getElem_take, List.getElem_map]
      have hget₂ := getElem_allPairs_pairIdx (r := r₂)
        (a := Fin.castLE hrr p.1) (b := Fin.castLE hrr p.2) (by simpa using hplt)
      dsimp only [p] at hget₂ hpidx
      simpa [hpidx, Prod.map] using hget₂
  have hsplit : allPairs r₂ =
      (allPairs r₁).map (Prod.map (Fin.castLE hrr) (Fin.castLE hrr)) ++
        (allPairs r₂).drop (r₁.choose 2) := by
    rw [← htake, List.take_append_drop]
  simp only [maskEdgePairs_eq_filterMaskAux]
  rw [hsplit]
  refine filterMaskAux_map_append _ mask (allPairs r₁) _ 0 fun k hk => ?_
  rw [length_allPairs] at hk
  exact Nat.testBit_eq_false_of_lt
    (hmask.trans_le (Nat.pow_le_pow_right (by omega) (by simpa using hk)))

theorem endsOfMask_isSimple (r mask : ℕ) : IsSimple (endsOfMask r mask) := by
  have hnd : (maskEdgePairs r mask).Nodup := maskEdgePairs_nodup r mask
  have hmem_all : ∀ x ∈ maskEdgePairs r mask, x ∈ allPairs r := by
    intro x hx
    rw [maskEdgePairs_eq_filterMaskAux] at hx
    exact filterMaskAux_subset mask (allPairs r) 0 hx
  refine ⟨fun i => ?_, fun i₁ i₂ he => ?_⟩
  · have hmem : (maskEdgePairs r mask)[i.val] ∈ allPairs r :=
      hmem_all _ (List.getElem_mem i.isLt)
    have hlt := allPairs_lt hmem
    simp only [endsOfMask, Sym2.mk_isDiag_iff]
    exact fun h => Nat.ne_of_lt hlt (congrArg Fin.val h)
  · have hmem₁ : (maskEdgePairs r mask)[i₁.val] ∈ allPairs r :=
      hmem_all _ (List.getElem_mem i₁.isLt)
    have hmem₂ : (maskEdgePairs r mask)[i₂.val] ∈ allPairs r :=
      hmem_all _ (List.getElem_mem i₂.isLt)
    have hlt₁ := allPairs_lt hmem₁
    have hlt₂ := allPairs_lt hmem₂
    dsimp only [endsOfMask] at he
    have heq : (maskEdgePairs r mask)[i₁.val] = (maskEdgePairs r mask)[i₂.val] := by
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext h1 h2
      · exfalso
        have v1 : (maskEdgePairs r mask)[i₁.val].1.val = (maskEdgePairs r mask)[i₂.val].2.val :=
          congrArg Fin.val h1
        have v2 : (maskEdgePairs r mask)[i₁.val].2.val = (maskEdgePairs r mask)[i₂.val].1.val :=
          congrArg Fin.val h2
        omega
    exact Fin.ext (hnd.getElem_inj_iff.mp heq)

/-! ## Existence and Optimality of MSF Decision Trees -/

private theorem perm_eq_of_forall_lt {e : ℕ} {p q : Equiv.Perm (Fin e)}
    (h : ∀ a b : Fin e, a.val < b.val → ((p a).val < (p b).val ↔ (q a).val < (q b).val)) :
    p = q := by
  have hall : ∀ a b : Fin e, (p a).val < (p b).val ↔ (q a).val < (q b).val := by
    intro a b
    rcases lt_trichotomy a.val b.val with hab | heq | hba
    · exact h a b hab
    · have : a = b := Fin.ext heq; subst this; simp
    · have hba' : b.val < a.val := hba
      have hne : a ≠ b := fun he => Nat.ne_of_lt hba' (congrArg Fin.val he.symm)
      have hpne : (p a).val ≠ (p b).val := fun he => hne (p.injective (Fin.ext he))
      have hqne : (q a).val ≠ (q b).val := fun he => hne (q.injective (Fin.ext he))
      have hswap := h b a hba'
      omega
  ext i
  have hrank : ∀ r : Equiv.Perm (Fin e),
      (r i).val = (Finset.univ.filter fun j : Fin e => (r j).val < (r i).val).card := by
    intro r
    have himg : (Finset.univ.filter fun j : Fin e => (r j).val < (r i).val).image r =
        Finset.univ.filter fun k : Fin e => k.val < (r i).val := by
      ext k
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact hj
      · intro hk; exact ⟨r.symm k, by simpa using hk, by simp⟩
    have hcard_lt : (Finset.univ.filter fun k : Fin e => k.val < (r i).val).card = (r i).val := by
      let emb : Fin (r i).val ↪ Fin e :=
        ⟨fun t => ⟨t.val, by omega⟩, fun _ _ ht => Fin.ext (by simpa using congrArg Fin.val ht)⟩
      have heq : (Finset.univ.filter fun k : Fin e => k.val < (r i).val) =
          Finset.univ.map emb := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, emb]
        constructor
        · intro hk; exact ⟨⟨k.val, hk⟩, Fin.ext rfl⟩
        · rintro ⟨t, rfl⟩; exact t.isLt
      rw [heq, Finset.card_map, Finset.card_fin]
    have hc1 : (Finset.univ.filter fun j : Fin e => (r j).val < (r i).val).card =
        (Finset.univ.filter fun k : Fin e => k.val < (r i).val).card := by
      rw [← himg, Finset.card_image_of_injective _ r.injective]
    exact (hc1.trans hcard_lt).symm
  rw [hrank p, hrank q]
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hall j i

private def buildTreeOfPairs {e : ℕ} {α : Type} (f : Equiv.Perm (Fin e) → α)
    (defaultAns : α) : List (Fin e × Fin e) → List (Equiv.Perm (Fin e)) → MSFTree e α
  | _, [] => .leaf defaultAns
  | [], q :: _ => .leaf (f q)
  | (a, b) :: rest, ps =>
    .node a b
      (buildTreeOfPairs f defaultAns rest (ps.filter fun q => decide ((q a).val < (q b).val)))
      (buildTreeOfPairs f defaultAns rest (ps.filter fun q => !decide ((q a).val < (q b).val)))

private theorem buildTreeOfPairs_depth_le {e : ℕ} {α : Type} (f : Equiv.Perm (Fin e) → α)
    (d0 : α) (pairs : List (Fin e × Fin e)) (ps : List (Equiv.Perm (Fin e))) :
    (buildTreeOfPairs f d0 pairs ps).depth ≤ pairs.length := by
  induction pairs generalizing ps with
  | nil => cases ps <;> simp [buildTreeOfPairs, MSFTree.depth]
  | cons p rest ih =>
    cases ps with
    | nil => simp [buildTreeOfPairs, MSFTree.depth]
    | cons q qs =>
      simp only [buildTreeOfPairs, MSFTree.depth, List.length_cons]
      have h1 := ih ((q :: qs).filter fun r => decide ((r p.1).val < (r p.2).val))
      have h2 := ih ((q :: qs).filter fun r => !decide ((r p.1).val < (r p.2).val))
      omega

private theorem buildTreeOfPairs_eval {e : ℕ} {α : Type} (f : Equiv.Perm (Fin e) → α)
    (d0 : α) (pairs : List (Fin e × Fin e)) (ps : List (Equiv.Perm (Fin e)))
    (p : Equiv.Perm (Fin e)) (hp : p ∈ ps)
    (hinv : ∀ a b : Fin e, a.val < b.val → (a, b) ∈ pairs ∨
      ∀ q ∈ ps, ((q a).val < (q b).val ↔ (p a).val < (p b).val)) :
    (buildTreeOfPairs f d0 pairs ps).eval p = f p := by
  induction pairs generalizing ps with
  | nil =>
    cases ps with
    | nil => simp at hp
    | cons q qs =>
      simp only [buildTreeOfPairs, MSFTree.eval]
      have hqp : q = p := perm_eq_of_forall_lt fun a b hab => by
        rcases hinv a b hab with hmem | hagree
        · simp at hmem
        · exact hagree q List.mem_cons_self
      rw [hqp]
  | cons ab rest ih =>
    rcases ab with ⟨a, b⟩
    cases ps with
    | nil => simp at hp
    | cons q qs =>
      simp only [buildTreeOfPairs, MSFTree.eval]
      split_ifs with hlt
      · refine ih _ (List.mem_filter.mpr ⟨hp, decide_eq_true hlt⟩) fun x y hxy => ?_
        by_cases hxyeq : (x, y) = (a, b)
        · right
          intro r hr
          rw [List.mem_filter] at hr
          have hx : x = a := congrArg Prod.fst hxyeq
          have hy : y = b := congrArg Prod.snd hxyeq
          subst hx hy
          exact ⟨fun _ => hlt, fun _ => of_decide_eq_true hr.2⟩
        · rcases hinv x y hxy with hmem | hagree
          · rcases List.mem_cons.mp hmem with hhead | htail
            · exact absurd hhead hxyeq
            · exact .inl htail
          · exact .inr fun r hr => hagree r (List.mem_filter.mp hr).1
      · refine ih _ (List.mem_filter.mpr ⟨hp, by simp [hlt]⟩) fun x y hxy => ?_
        by_cases hxyeq : (x, y) = (a, b)
        · right
          intro r hr
          rw [List.mem_filter] at hr
          have hxr : ¬ ((r x).val < (r y).val) := by
            have he := hr.2
            have ha : x = a := congrArg Prod.fst hxyeq
            have hb : y = b := congrArg Prod.snd hxyeq
            rw [ha, hb]
            simpa using he
          exact ⟨fun h => absurd h hxr, fun h => by
            have ha : x = a := congrArg Prod.fst hxyeq
            have hb : y = b := congrArg Prod.snd hxyeq
            rw [ha, hb] at h
            exact absurd h hlt⟩
        · rcases hinv x y hxy with hmem | hagree
          · rcases List.mem_cons.mp hmem with hhead | htail
            · exact absurd hhead hxyeq
            · exact .inl htail
          · exact .inr fun r hr => hagree r (List.mem_filter.mp hr).1

theorem exists_correct_msfTree {e : ℕ} {α : Type} (f : Equiv.Perm (Fin e) → α)
    (P : Finset (Equiv.Perm (Fin e))) :
    ∃ T : MSFTree e α, T.AgreesOn f P ∧ T.depth ≤ e.choose 2 := by
  classical
  let T := buildTreeOfPairs f (f (Equiv.refl _)) (allPairs e) (Finset.univ.toList)
  refine ⟨T, fun p _ => ?_, ?_⟩
  · refine buildTreeOfPairs_eval f (f (Equiv.refl _)) (allPairs e) _ p
      (Finset.mem_toList.mpr (Finset.mem_univ p)) fun x y hxy => .inl (mem_allPairs_iff.mpr hxy)
  · have hd := buildTreeOfPairs_depth_le f (f (Equiv.refl _)) (allPairs e) (Finset.univ.toList)
    rwa [length_allPairs] at hd

theorem exists_correct_msfDT {e n : ℕ} (ends : Fin e → Sym2 (Fin n)) :
    ∃ T : MSFDT e, T.Correct ends ∧ T.depth ≤ e.choose 2 := by
  obtain ⟨T, hAg, hd⟩ :=
    exists_correct_msfTree (fun p => Cslib.Multigraph.msf ends p Finset.univ) Finset.univ
  exact ⟨T, fun p => hAg p (Finset.mem_univ p), hd⟩

/-- Minimum worst-case comparison depth of a decision tree computing `f` on subset `P`. -/
noncomputable def optDepthOn {e : ℕ} {α : Type} (f : Equiv.Perm (Fin e) → α)
    (P : Finset (Equiv.Perm (Fin e))) : ℕ :=
  letI := Classical.propDecidable
  Nat.find (⟨e.choose 2, exists_correct_msfTree f P⟩ :
    ∃ d, ∃ T : MSFTree e α, T.AgreesOn f P ∧ T.depth ≤ d)

theorem exists_opt_msfTree {e : ℕ} {α : Type} (f : Equiv.Perm (Fin e) → α)
    (P : Finset (Equiv.Perm (Fin e))) :
    ∃ T : MSFTree e α, T.AgreesOn f P ∧ T.depth = optDepthOn f P := by
  classical
  have hspec := Nat.find_spec (⟨e.choose 2, exists_correct_msfTree f P⟩ :
    ∃ d, ∃ T : MSFTree e α, T.AgreesOn f P ∧ T.depth ≤ d)
  obtain ⟨T, hAg, hle⟩ := hspec
  have hge : optDepthOn f P ≤ T.depth := Nat.find_min' _ ⟨T, hAg, le_rfl⟩
  exact ⟨T, hAg, le_antisymm hle hge⟩

theorem optDepthOn_le_of_agrees {e : ℕ} {α : Type} {f : Equiv.Perm (Fin e) → α}
    {P : Finset (Equiv.Perm (Fin e))} {T : MSFTree e α} (h : T.AgreesOn f P) :
    optDepthOn f P ≤ T.depth := by
  classical
  exact Nat.find_le ⟨T, h, le_rfl⟩

theorem optDepthOn_mono {e : ℕ} {α : Type} (f : Equiv.Perm (Fin e) → α)
    {P₁ P₂ : Finset (Equiv.Perm (Fin e))} (h : P₁ ⊆ P₂) :
    optDepthOn f P₁ ≤ optDepthOn f P₂ := by
  obtain ⟨T, hAg, hd⟩ := exists_opt_msfTree f P₂
  exact (optDepthOn_le_of_agrees fun p hp => hAg p (h hp)).trans hd.le

/-- Optimal comparison decision-tree depth `T*(G)` for multigraph `ends : Fin e → Sym2 (Fin n)`. -/
noncomputable def optDepth {e n : ℕ} (ends : Fin e → Sym2 (Fin n)) : ℕ :=
  optDepthOn (fun p => Cslib.Multigraph.msf ends p Finset.univ) Finset.univ

theorem optDepth_eq_optDepthOn {e n : ℕ} (ends : Fin e → Sym2 (Fin n)) :
    optDepth ends = optDepthOn (fun p => Cslib.Multigraph.msf ends p Finset.univ) Finset.univ := by
  rfl

theorem exists_opt_msfDT {e n : ℕ} (ends : Fin e → Sym2 (Fin n)) :
    ∃ T : MSFDT e, T.Correct ends ∧ T.depth = optDepth ends := by
  obtain ⟨T, hAg, hd⟩ :=
    exists_opt_msfTree (fun p => Cslib.Multigraph.msf ends p Finset.univ) Finset.univ
  exact ⟨T, fun p => hAg p (Finset.mem_univ p), hd⟩

theorem optDepth_le_of_correct {e n : ℕ} {ends : Fin e → Sym2 (Fin n)} {T : MSFDT e}
    (h : T.Correct ends) : optDepth ends ≤ T.depth :=
  optDepthOn_le_of_agrees fun p _ => h p

theorem optDepth_le_pairs {e n : ℕ} (ends : Fin e → Sym2 (Fin n)) :
    optDepth ends ≤ e.choose 2 := by
  obtain ⟨T, hT, hd⟩ := exists_correct_msfDT ends
  exact (optDepth_le_of_correct hT).trans hd

theorem optDepth_eq_zero_of_le_one {e n : ℕ} (he : e ≤ 1) (ends : Fin e → Sym2 (Fin n)) :
    optDepth ends = 0 := by
  have hsub : Subsingleton (Equiv.Perm (Fin e)) := by
    refine ⟨fun p q => ?_⟩
    exact perm_eq_of_forall_lt fun x y _ => by
      exfalso
      have hy : y.val < e := y.isLt
      omega
  let T : MSFDT e := .leaf (Cslib.Multigraph.msf ends (Equiv.refl _) Finset.univ)
  have hcorr : T.Correct ends := fun p => by
    rw [Subsingleton.elim p (Equiv.refl _)]
    rfl
  exact Nat.eq_zero_of_le_zero (optDepth_le_of_correct hcorr)

/-! ## Complete Binary Trees (`IsComplete` and `padTo`) -/

/-- Complete binary decision tree of uniform depth `d` with ordered distinct comparisons `i < j`. -/
def MSFTree.IsComplete {e : ℕ} {α : Type} : ℕ → MSFTree e α → Prop
  | 0, .leaf _ => True
  | _ + 1, .leaf _ => False
  | 0, .node _ _ _ _ => False
  | d + 1, .node i j l r => i.val < j.val ∧ l.IsComplete d ∧ r.IsComplete d

theorem MSFTree.depth_of_isComplete {e : ℕ} {α : Type} :
    ∀ {d : ℕ} {T : MSFTree e α}, T.IsComplete d → T.depth = d
  | 0, .leaf _, _ => rfl
  | 0, .node _ _ _ _, h => False.elim h
  | _ + 1, .leaf _, h => False.elim h
  | d + 1, .node _ _ l r, ⟨_, hl, hr⟩ => by
    simp only [MSFTree.depth, depth_of_isComplete hl, depth_of_isComplete hr, max_self]
    omega

private def MSFTree.norm {e : ℕ} {α : Type} : MSFTree e α → MSFTree e α
  | .leaf a => .leaf a
  | .node i j l r =>
    if i.val < j.val then .node i j l.norm r.norm
    else if j.val < i.val then .node j i r.norm l.norm
    else r.norm

private def MSFTree.Ordered {e : ℕ} {α : Type} : MSFTree e α → Prop
  | .leaf _ => True
  | .node i j l r => i.val < j.val ∧ l.Ordered ∧ r.Ordered

private theorem MSFTree.norm_ordered {e : ℕ} {α : Type} (T : MSFTree e α) : T.norm.Ordered := by
  induction T with
  | leaf _ => trivial
  | node i j l r ihl ihr =>
    dsimp only [MSFTree.norm]
    split_ifs with h1 h2
    · exact ⟨h1, ihl, ihr⟩
    · exact ⟨h2, ihr, ihl⟩
    · exact ihr

private theorem MSFTree.norm_depth_le {e : ℕ} {α : Type} (T : MSFTree e α) :
    T.norm.depth ≤ T.depth := by
  induction T with
  | leaf _ => rfl
  | node i j l r ihl ihr =>
    dsimp only [MSFTree.norm]
    split_ifs <;> simp only [MSFTree.depth] <;> omega

private theorem MSFTree.norm_eval {e : ℕ} {α : Type} (T : MSFTree e α)
    (p : Equiv.Perm (Fin e)) :
    T.norm.eval p = T.eval p := by
  induction T with
  | leaf _ => rfl
  | node i j l r ihl ihr =>
    dsimp only [MSFTree.norm, MSFTree.eval]
    by_cases h1 : i.val < j.val
    · simp only [h1, ↓reduceIte, MSFTree.eval]
      split_ifs <;> assumption
    · by_cases h2 : j.val < i.val
      · simp only [h1, ↓reduceIte, h2, MSFTree.eval]
        have hne : (p i).val ≠ (p j).val := fun h =>
          Nat.ne_of_lt h2 (congrArg Fin.val (p.injective (Fin.ext h)).symm)
        by_cases hp : (p j).val < (p i).val
        · have hnot : ¬ ((p i).val < (p j).val) := by omega
          simp [hp, hnot, ihr]
        · have hyes : (p i).val < (p j).val := by omega
          simp [hp, hyes, ihl]
      · have hij : i = j := Fin.ext (by omega)
        subst hij
        simp only [Nat.lt_irrefl, ↓reduceIte]
        exact ihr

private def dummyTree {e : ℕ} (he : 2 ≤ e) {α : Type} (ans : α) : ℕ → MSFTree e α
  | 0 => .leaf ans
  | d + 1 => .node ⟨0, by omega⟩ ⟨1, by omega⟩ (dummyTree he ans d) (dummyTree he ans d)

private theorem dummyTree_isComplete {e : ℕ} (he : 2 ≤ e) {α : Type} (ans : α) (d : ℕ) :
    (dummyTree he ans d).IsComplete d := by
  induction d with
  | zero => trivial
  | succ d ih => exact ⟨by dsimp only; omega, ih, ih⟩

private theorem dummyTree_eval {e : ℕ} (he : 2 ≤ e) {α : Type} (ans : α) (d : ℕ)
    (p : Equiv.Perm (Fin e)) :
    (dummyTree he ans d).eval p = ans := by
  induction d with
  | zero => rfl
  | succ d ih =>
    dsimp only [dummyTree, MSFTree.eval]
    split_ifs <;> exact ih

private def padOrdered {e : ℕ} (he : 2 ≤ e) {α : Type} :
    ℕ → MSFTree e α → MSFTree e α
  | 0, .leaf a => .leaf a
  | d + 1, .leaf a => dummyTree he a (d + 1)
  | 0, .node _ _ l _ => padOrdered he 0 l
  | d + 1, .node i j l r => .node i j (padOrdered he d l) (padOrdered he d r)

private theorem padOrdered_isComplete {e : ℕ} (he : 2 ≤ e) {α : Type} :
    ∀ (d : ℕ) (T : MSFTree e α), T.Ordered → T.depth ≤ d → (padOrdered he d T).IsComplete d
  | 0, .leaf _, _, _ => trivial
  | d + 1, .leaf a, _, _ => dummyTree_isComplete he a (d + 1)
  | 0, .node _ _ _ _, _, hd => by simp [MSFTree.depth] at hd
  | d + 1, .node i j l r, ⟨hij, hl, hr⟩, hd => by
    simp only [MSFTree.depth] at hd
    exact ⟨hij, padOrdered_isComplete he d l hl (by omega),
      padOrdered_isComplete he d r hr (by omega)⟩

private theorem padOrdered_eval {e : ℕ} (he : 2 ≤ e) {α : Type} (p : Equiv.Perm (Fin e)) :
    ∀ (d : ℕ) (T : MSFTree e α), T.depth ≤ d → (padOrdered he d T).eval p = T.eval p
  | 0, .leaf _, _ => rfl
  | d + 1, .leaf a, _ => dummyTree_eval he a (d + 1) p
  | 0, .node _ _ _ _, hd => by simp [MSFTree.depth] at hd
  | d + 1, .node i j l r, hd => by
    simp only [MSFTree.depth] at hd
    dsimp only [padOrdered, MSFTree.eval]
    split_ifs
    · exact padOrdered_eval he p d l (by omega)
    · exact padOrdered_eval he p d r (by omega)

/-- Normalize and pad `T` into a complete decision tree of uniform depth `d`. -/
def MSFDT.padTo {e : ℕ} (he : 2 ≤ e) (d : ℕ) (T : MSFDT e) : MSFDT e :=
  padOrdered he d T.norm

theorem MSFDT.padTo_isComplete {e : ℕ} (he : 2 ≤ e) (d : ℕ) (T : MSFDT e)
    (hle : T.depth ≤ d) : (T.padTo he d).IsComplete d :=
  padOrdered_isComplete he d T.norm T.norm_ordered (T.norm_depth_le.trans hle)

theorem MSFDT.padTo_eval {e : ℕ} (he : 2 ≤ e) (d : ℕ) (T : MSFDT e)
    (hle : T.depth ≤ d) (p : Equiv.Perm (Fin e)) :
    (T.padTo he d).eval p = T.eval p := by
  rw [MSFDT.padTo, padOrdered_eval he p d T.norm (T.norm_depth_le.trans hle), T.norm_eval]

theorem exists_complete_correct_iff {e n : ℕ} (he : 2 ≤ e)
    (ends : Fin e → Sym2 (Fin n)) (d : ℕ) :
    (∃ T : MSFDT e, T.IsComplete d ∧ T.Correct ends) ↔ optDepth ends ≤ d := by
  constructor
  · rintro ⟨T, hcomp, hcorr⟩
    rw [← MSFTree.depth_of_isComplete hcomp]
    exact optDepth_le_of_correct hcorr
  · intro hle
    obtain ⟨T, hcorr, hd⟩ := exists_opt_msfDT ends
    refine ⟨T.padTo he d, T.padTo_isComplete he d (hd ▸ hle), fun p => ?_⟩
    rw [T.padTo_eval he d (hd ▸ hle) p, hcorr p]

/-! ## Compiling `FreeM (LEQuery (Fin e)) α` Programs to Decision Trees -/

private def permFilterLt {e : ℕ} (P : Finset (Equiv.Perm (Fin e))) (a b : Fin e) :
    Finset (Equiv.Perm (Fin e)) :=
  P.filter fun p => (p a).val < (p b).val

private def permFilterGe {e : ℕ} (P : Finset (Equiv.Perm (Fin e))) (a b : Fin e) :
    Finset (Equiv.Perm (Fin e)) :=
  P.filter fun p => ¬ ((p a).val < (p b).val)

private theorem keyOracle_perm_iff {e : ℕ} (p : Equiv.Perm (Fin e)) {a b : Fin e} (hab : a ≠ b) :
    LEQuery.keyOracle p (.le a b) = decide ((p a).val < (p b).val) := by
  simp only [LEQuery.keyOracle_le]
  have hne : (p a).val ≠ (p b).val := fun h => hab (p.injective (Fin.ext h))
  apply decide_eq_decide.mpr
  change (p a).val ≤ (p b).val ↔ (p a).val < (p b).val
  omega

/-- Compile a comparison-query algorithm `prog : FreeM (LEQuery (Fin e)) α` into a
binary decision tree `MSFTree e α` specialized to feasible permutation set `P`. -/
noncomputable def msfTreeOfFreeM {e : ℕ} {α : Type}
    (P : Finset (Equiv.Perm (Fin e))) :
    FreeM (LEQuery (Fin e)) α → MSFTree e α
  | .pure ans => .leaf ans
  | .liftBind op cont =>
    match op, cont with
    | .le a b, cont =>
      if a = b then
        msfTreeOfFreeM P (cont true)
      else
        let Pl := permFilterLt P a b
        let Pr := permFilterGe P a b
        if Pl = ∅ then
          msfTreeOfFreeM P (cont false)
        else if Pr = ∅ then
          msfTreeOfFreeM P (cont true)
        else
          .node a b (msfTreeOfFreeM Pl (cont true)) (msfTreeOfFreeM Pr (cont false))

theorem msfTreeOfFreeM_eval {e : ℕ} {α : Type} :
    ∀ (prog : FreeM (LEQuery (Fin e)) α) (P : Finset (Equiv.Perm (Fin e)))
      (p : Equiv.Perm (Fin e)), p ∈ P →
      (msfTreeOfFreeM P prog).eval p = prog.eval (LEQuery.keyOracle p)
  | .pure _, _, _, _ => rfl
  | .liftBind (.le a b) cont, P, p, hp => by
    dsimp only [msfTreeOfFreeM]
    have heval : FreeM.eval (LEQuery.keyOracle p) (FreeM.liftBind (.le a b) cont) =
        FreeM.eval (LEQuery.keyOracle p) (cont (LEQuery.keyOracle p (.le a b))) := rfl
    rw [heval]
    split_ifs with hab hPl hPr
    · subst hab
      have hor : LEQuery.keyOracle p (.le a a) = true := by simp [LEQuery.keyOracle_le]
      rw [hor]
      exact msfTreeOfFreeM_eval (cont true) P p hp
    · have hor : LEQuery.keyOracle p (.le a b) = false := by
        have hnotlt : ¬ ((p a).val < (p b).val) := fun hlt => by
          have hp_mem : p ∈ permFilterLt P a b := Finset.mem_filter.mpr ⟨hp, hlt⟩
          rw [hPl] at hp_mem
          simp at hp_mem
        rw [keyOracle_perm_iff p hab]
        exact decide_eq_false hnotlt
      rw [hor]
      exact msfTreeOfFreeM_eval (cont false) P p hp
    · have hor : LEQuery.keyOracle p (.le a b) = true := by
        have hlt : (p a).val < (p b).val := by
          by_contra hnot
          have hp_mem : p ∈ permFilterGe P a b := Finset.mem_filter.mpr ⟨hp, hnot⟩
          rw [hPr] at hp_mem
          simp at hp_mem
        rw [keyOracle_perm_iff p hab]
        exact decide_eq_true hlt
      rw [hor]
      exact msfTreeOfFreeM_eval (cont true) P p hp
    · simp only [MSFTree.eval, keyOracle_perm_iff p hab]
      by_cases hlt : (p a).val < (p b).val
      · simp only [hlt, ↓reduceIte, decide_true]
        exact msfTreeOfFreeM_eval (cont true) (permFilterLt P a b) p
          (Finset.mem_filter.mpr ⟨hp, hlt⟩)
      · simp only [hlt, ↓reduceIte, decide_false]
        exact msfTreeOfFreeM_eval (cont false) (permFilterGe P a b) p
          (Finset.mem_filter.mpr ⟨hp, hlt⟩)

theorem msfTreeOfFreeM_depth_le {e : ℕ} {α : Type} :
    ∀ (prog : FreeM (LEQuery (Fin e)) α) (P : Finset (Equiv.Perm (Fin e)))
      (D : ℕ), P.Nonempty →
      (∀ p ∈ P, prog.countQueries (LEQuery.keyOracle p) ≤ D) →
      (msfTreeOfFreeM P prog).depth ≤ D
  | .pure _, _, _, _, _ => Nat.zero_le _
  | .liftBind (.le a b) cont, P, D, hP, hD => by
    dsimp only [msfTreeOfFreeM]
    have hstep : ∀ (p : Equiv.Perm (Fin e)),
        FreeM.countQueries (LEQuery.keyOracle p) (FreeM.liftBind (.le a b) cont) =
          1 + FreeM.countQueries (LEQuery.keyOracle p)
            (cont (LEQuery.keyOracle p (.le a b))) :=
      fun p => FreeM.countQueries_liftBind (LEQuery.keyOracle p) (.le a b) cont
    split_ifs with hab hPl hPr
    · subst hab
      refine msfTreeOfFreeM_depth_le (cont true) P D hP fun p hp => ?_
      have hq := hD p hp
      rw [hstep] at hq
      have hor : LEQuery.keyOracle p (.le a a) = true := by simp [LEQuery.keyOracle_le]
      rw [hor] at hq
      omega
    · refine msfTreeOfFreeM_depth_le (cont false) P D hP fun p hp => ?_
      have hq := hD p hp
      rw [hstep] at hq
      have hor : LEQuery.keyOracle p (.le a b) = false := by
        have hnotlt : ¬ ((p a).val < (p b).val) := fun hlt => by
          have hp_mem : p ∈ permFilterLt P a b := Finset.mem_filter.mpr ⟨hp, hlt⟩
          rw [hPl] at hp_mem
          simp at hp_mem
        rw [keyOracle_perm_iff p hab]
        exact decide_eq_false hnotlt
      rw [hor] at hq
      omega
    · refine msfTreeOfFreeM_depth_le (cont true) P D hP fun p hp => ?_
      have hq := hD p hp
      rw [hstep] at hq
      have hor : LEQuery.keyOracle p (.le a b) = true := by
        have hlt : (p a).val < (p b).val := by
          by_contra hnot
          have hp_mem : p ∈ permFilterGe P a b := Finset.mem_filter.mpr ⟨hp, hnot⟩
          rw [hPr] at hp_mem
          simp at hp_mem
        rw [keyOracle_perm_iff p hab]
        exact decide_eq_true hlt
      rw [hor] at hq
      omega
    · obtain ⟨p0, hp0⟩ := hP
      have hq0 := hD p0 hp0
      rw [hstep] at hq0
      have hPl_ne : (permFilterLt P a b).Nonempty := Finset.nonempty_iff_ne_empty.mpr hPl
      have hPr_ne : (permFilterGe P a b).Nonempty := Finset.nonempty_iff_ne_empty.mpr hPr
      have hL := msfTreeOfFreeM_depth_le (cont true) (permFilterLt P a b) (D - 1) hPl_ne
        fun p hp => by
          have hp' := Finset.mem_filter.mp hp
          have hq := hD p hp'.1
          rw [hstep] at hq
          have hor : LEQuery.keyOracle p (.le a b) = true := by
            rw [keyOracle_perm_iff p hab]
            exact decide_eq_true hp'.2
          rw [hor] at hq
          omega
      have hR := msfTreeOfFreeM_depth_le (cont false) (permFilterGe P a b) (D - 1) hPr_ne
        fun p hp => by
          have hp' := Finset.mem_filter.mp hp
          have hq := hD p hp'.1
          rw [hstep] at hq
          have hor : LEQuery.keyOracle p (.le a b) = false := by
            rw [keyOracle_perm_iff p hab]
            exact decide_eq_false hp'.2
          rw [hor] at hq
          omega
      dsimp only [MSFTree.depth]
      omega

/-- Any `FreeM (LEQuery (Fin e)) (Finset (Fin e))` program computing `Cslib.Multigraph.msf`
using at most `D` queries under `Cslib.Query.LEQuery.keyOracle p` yields an MSF decision tree
of depth at most `D`. -/
theorem optDepth_le_of_freeM {e n : ℕ} (ends : Fin e → Sym2 (Fin n))
    (prog : FreeM (LEQuery (Fin e)) (Finset (Fin e))) (D : ℕ)
    (hcorr : ∀ p : Equiv.Perm (Fin e),
      prog.eval (LEQuery.keyOracle p) = Cslib.Multigraph.msf ends p Finset.univ)
    (hdepth : ∀ p : Equiv.Perm (Fin e),
      prog.countQueries (LEQuery.keyOracle p) ≤ D) :
    optDepth ends ≤ D := by
  let T := msfTreeOfFreeM Finset.univ prog
  have hTcorr : MSFDT.Correct ends T := fun p => by
    change (msfTreeOfFreeM Finset.univ prog).eval p = Cslib.Multigraph.msf ends p Finset.univ
    rw [msfTreeOfFreeM_eval prog Finset.univ p (Finset.mem_univ p), hcorr p]
  have hTd : T.depth ≤ D :=
    msfTreeOfFreeM_depth_le prog Finset.univ D Finset.univ_nonempty fun p _ => hdepth p
  exact (optDepth_le_of_correct hTcorr).trans hTd

end Cslib.Query.MinimumSpanningForest
