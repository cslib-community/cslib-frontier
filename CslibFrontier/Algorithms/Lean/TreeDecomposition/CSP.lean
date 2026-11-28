/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.TreeDecomposition.BagAssignment
public import CslibFrontier.Logics.Propositional.CSP.PrimalGraph
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Dynamic programming for CSPs on bounded treewidth

For a constraint satisfaction problem `F : CSP Rel V` over a finite inhabited domain `Fin q`
(`0 < q`), and a valid nice tree decomposition covering every constraint scope of `F` (from
`F.primalGraph` or `F.activePrimalGraph`), this module implements executable pure dynamic
programming procedures for both exact model counting (`cspCountNice`, `cspCountRooted`) and
satisfiability (`cspDecideNice`, `cspDecideRooted`).

Using `SimpleGraph.RootedTreeDecomposition.toNiceTreePruned`, any supplied rooted tree
decomposition `R` of width `w` is converted to a nice tree decomposition of width at most `w` and
size at most `(3 * w + 5) * (card V + 1)`. Machine-level running-time bounds charging bag list
construction and erasure, materialized constraint truth-table lookups, radix projections, and
bounded-word arithmetic live in `CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP`.

## Main definitions

* `Cslib.Algorithms.Lean.TreeDecomposition.bagList`: canonical vertex list order at each nice-tree
  node.
* `Cslib.Algorithms.Lean.TreeDecomposition.cspCountTree`,
  `Cslib.Algorithms.Lean.TreeDecomposition.cspDecideTree`: bottom-up DP tables over a `NiceTree`.
* `Cslib.Algorithms.Lean.TreeDecomposition.cspCountNice`,
  `Cslib.Algorithms.Lean.TreeDecomposition.cspDecideNice`: root answers on nice decompositions of
  `F.primalGraph` (and `cspCountActiveNice`, `cspDecideActiveNice` on `F.activePrimalGraph`).
* `Cslib.Algorithms.Lean.TreeDecomposition.cspCountRooted`,
  `Cslib.Algorithms.Lean.TreeDecomposition.cspDecideRooted`: wrappers over arbitrary rooted tree
  decompositions via `toNiceTreePruned` (and active counterparts).

## Main results

* `Cslib.Algorithms.Lean.TreeDecomposition.cspCountNice_eq_modelCount`,
  `Cslib.Algorithms.Lean.TreeDecomposition.cspDecideNice_eq_true_iff`: exact agreement with
  `CSP.modelCount` and `CSP.Satisfiable`.
* `Cslib.Algorithms.Lean.TreeDecomposition.cspCountRooted_eq_modelCount`,
  `Cslib.Algorithms.Lean.TreeDecomposition.cspDecideRooted_eq_true_iff` (and active counterparts):
  exact agreement on rooted tree decompositions via `toNiceTreePruned`.
* `Cslib.Algorithms.Lean.TreeDecomposition.modelCount_semFin`,
  `Cslib.Algorithms.Lean.TreeDecomposition.satisfiable_semFin_iff`: reduction from an arbitrary
  `[Fintype D] [Inhabited D]` domain to `Fin (Fintype.card D)`.
-/

public section

namespace Cslib.Algorithms.Lean.TreeDecomposition

open Cslib.Logic.PL SimpleGraph

section BagOrder

variable {V : Type*} [DecidableEq V]

/-- Canonical variable listing of each bag in a `NiceTree`. -/
@[expose] def bagList : NiceTree V → List V
  | .leaf => []
  | .introduce v child => v :: bagList child
  | .forget v child => (bagList child).erase v
  | .join left _ => bagList left

private theorem toFinset_erase_of_nodup {L : List V} (hL : L.Nodup) (v : V) :
    (L.erase v).toFinset = L.toFinset.erase v := by
  ext x
  simp only [List.mem_toFinset, Finset.mem_erase]
  exact hL.mem_erase_iff

theorem bagList_nodup_and_toFinset :
    ∀ {T : NiceTree V}, T.LocalValid → (bagList T).Nodup ∧ (bagList T).toFinset = T.bag
  | .leaf, _ => ⟨List.nodup_nil, rfl⟩
  | .introduce v child, hval => by
    obtain ⟨hnodup, hfin⟩ := bagList_nodup_and_toFinset hval.2
    have hvnot : v ∉ bagList child := fun hv =>
      hval.1 (child.bag_subset_subtreeVerts (hfin ▸ List.mem_toFinset.2 hv))
    refine ⟨List.nodup_cons.2 ⟨hvnot, hnodup⟩, ?_⟩
    simp only [bagList, List.toFinset_cons, NiceTree.bag, hfin]
  | .forget v child, hval => by
    obtain ⟨hnodup, hfin⟩ := bagList_nodup_and_toFinset hval.2
    refine ⟨hnodup.erase v, ?_⟩
    simp only [bagList, NiceTree.bag, toFinset_erase_of_nodup hnodup v, hfin]
  | .join left _, hval => by
    obtain ⟨hnodup, hfin⟩ := bagList_nodup_and_toFinset hval.2.2.1
    exact ⟨hnodup, hfin⟩

theorem bagList_nodup {T : NiceTree V} (hval : T.LocalValid) : (bagList T).Nodup :=
  (bagList_nodup_and_toFinset hval).1

theorem toFinset_bagList {T : NiceTree V} (hval : T.LocalValid) : (bagList T).toFinset = T.bag :=
  (bagList_nodup_and_toFinset hval).2

theorem length_bagList {T : NiceTree V} (hval : T.LocalValid) :
    (bagList T).length = T.bag.card := by
  rw [← List.toFinset_card_of_nodup (bagList_nodup hval), toFinset_bagList hval]

theorem length_bagList_le {T : NiceTree V} (hval : T.LocalValid) :
    (bagList T).length ≤ T.width + 1 := by
  rw [length_bagList hval]
  have h1 := T.card_bag_le_maxBagCard
  have h2 : T.width = T.maxBagCard - 1 := rfl
  omega

end BagOrder

/-! ### Shared DP engine and correctness against `specDPCount` and `specDPDecide` -/

section Engine

variable {Rel V : Type*} [DecidableEq V]

/-- Semiring-like operations used by `dpTree` for both counting and decision. -/
structure DPAlg (β : Type) where
  /-- Additive identity (`0` for counting, `false` for decision). -/
  zero : β
  /-- Multiplicative identity (`1` for counting, `true` for decision). -/
  one : β
  /-- Aggregation across values of a forgotten variable. -/
  add : β → β → β
  /-- Combination of two join-branch table entries. -/
  mul : β → β → β

/-- Fold `g 0, …, g (k - 1)` from the left using `add` and initial value `z`. -/
@[expose] def dpAlgFold {β : Type} (z : β) (add : β → β → β) : ℕ → (ℕ → β) → β
  | 0, _ => z
  | k + 1, g => add (dpAlgFold z add k g) (g k)

theorem dpAlgFold_congr {β : Type} {z : β} {add : β → β → β} {k : ℕ}
    {g₁ g₂ : ℕ → β} (h : ∀ d < k, g₁ d = g₂ d) :
    dpAlgFold z add k g₁ = dpAlgFold z add k g₂ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [dpAlgFold, ih fun d hd => h d (Nat.lt_succ_of_lt hd), h k (Nat.lt_succ_self k)]

theorem dpAlgFold_nat (k : ℕ) (g : ℕ → ℕ) :
    dpAlgFold 0 (· + ·) k g = ∑ d ∈ Finset.range k, g d := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [dpAlgFold, Finset.sum_range_succ, ih]

theorem dpAlgFold_bool (k : ℕ) (g : ℕ → Bool) :
    dpAlgFold false (· || ·) k g = decide (∃ d < k, g d = true) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [dpAlgFold, ih]
    rw [← Bool.decide_eq_true (b := g k), ← Bool.decide_or]
    refine decide_eq_decide.2 ⟨?_, ?_⟩
    · rintro (⟨d, hdk, hfd⟩ | hk)
      · exact ⟨d, Nat.lt_succ_of_lt hdk, hfd⟩
      · exact ⟨k, Nat.lt_succ_self k, hk⟩
    · rintro ⟨d, hdk, hfd⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hdk with hlt | rfl
      · exact Or.inl ⟨d, hlt, hfd⟩
      · exact Or.inr hfd

/-- Generic bottom-up DP engine over a `NiceTree`, parameterized by `DPAlg`. -/
@[expose] def dpTree {β : Type} (A : DPAlg β) (q : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) (vars : List V) :
    NiceTree V → Array β
  | .leaf =>
    let ok := F.all fun c => !decide (c.scope = []) || c.eval sem (fun _ => ⟨0, hq⟩)
    #[if ok then A.one else A.zero]
  | .introduce v child =>
    let childTbl := dpTree A q hq sem F vars child
    let LB := v :: bagList child
    Array.ofFn fun m : Fin (q ^ LB.length) =>
      let ok := F.all fun c =>
        !(decide (c.scope.toFinset ⊆ LB.toFinset) && decide (v ∈ c.scope)) ||
          c.eval sem (ofRadixFin q hq LB m.val)
      if ok then childTbl.getD (m.val / q) A.zero else A.zero
  | .forget v child =>
    let childTbl := dpTree A q hq sem F vars child
    let LB := (bagList child).erase v
    Array.ofFn fun m : Fin (q ^ LB.length) =>
      if v ∈ vars then
        dpAlgFold A.zero A.add q fun d =>
          let idx := toRadix q (bagList child) (Function.update (ofRadix q LB m.val) v d)
          childTbl.getD idx A.zero
      else
        let idx := toRadix q (bagList child) (Function.update (ofRadix q LB m.val) v 0)
        childTbl.getD idx A.zero
  | .join left right =>
    let leftTbl := dpTree A q hq sem F vars left
    let rightTbl := dpTree A q hq sem F vars right
    let LL := bagList left
    let LR := bagList right
    Array.ofFn fun m : Fin (q ^ LL.length) =>
      let mr := toRadix q LR (ofRadix q LL m.val)
      A.mul (leftTbl.getD m.val A.zero) (rightTbl.getD mr A.zero)

theorem size_dpTree {β : Type} (A : DPAlg β) (q : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) (vars : List V) (T : NiceTree V) :
    (dpTree A q hq sem F vars T).size = q ^ (bagList T).length := by
  cases T <;> simp [dpTree, bagList]

/-- `DPAlg` instance over `ℕ` for exact model counting. -/
@[expose] def dpCountAlg : DPAlg ℕ where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)

/-- `DPAlg` instance over `Bool` for satisfiability decision. -/
@[expose] def dpDecideAlg : DPAlg Bool where
  zero := false
  one := true
  add := (· || ·)
  mul := (· && ·)

/-- Compute the bottom-up exact-count DP table on a nice tree decomposition over `Fin q`. -/
@[expose] def cspCountTree (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (vars : List V) (T : NiceTree V) : Array ℕ :=
  dpTree dpCountAlg q hq sem F vars T

/-- Compute the bottom-up satisfiability DP table on a nice tree decomposition over `Fin q`. -/
@[expose] def cspDecideTree (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (vars : List V) (T : NiceTree V) : Array Bool :=
  dpTree dpDecideAlg q hq sem F vars T

private theorem getD_ofFn {β : Type} {n : ℕ} (f : Fin n → β) {s : ℕ} (hs : s < n) (z : β) :
    (Array.ofFn f).getD s z = f ⟨s, hs⟩ := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_eq_left hs, Option.getD_some]

private noncomputable def dpSpec {β : Type} (A : DPAlg β) (q : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) (U : Finset V) :
    NiceTree V → (V → Fin q) → β
  | .leaf, _ =>
    if F.all (fun c => !decide (c.scope = []) || c.eval sem (fun _ => ⟨0, hq⟩)) then
      A.one
    else A.zero
  | .introduce v child, α =>
    if F.all (fun c => !(decide (c.scope.toFinset ⊆ insert v child.bag) && decide (v ∈ c.scope)) ||
        c.eval sem α) then
      dpSpec A q hq sem F U child α
    else A.zero
  | .forget v child, α =>
    letI := Classical.propDecidable (v ∈ U)
    if v ∈ U then
      dpAlgFold A.zero A.add q fun d =>
        if hd : d < q then dpSpec A q hq sem F U child (Function.update α v ⟨d, hd⟩) else A.zero
    else
      dpSpec A q hq sem F U child (Function.update α v ⟨0, hq⟩)
  | .join left right, α =>
    A.mul (dpSpec A q hq sem F U left α) (dpSpec A q hq sem F U right α)

private theorem dpSpec_congr {β : Type} (A : DPAlg β) (q : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) (U : Finset V) :
    ∀ {T : NiceTree V}, T.LocalValid →
      ∀ {α₁ α₂ : V → Fin q}, (∀ v ∈ T.bag, α₁ v = α₂ v) →
        dpSpec A q hq sem F U T α₁ = dpSpec A q hq sem F U T α₂
  | .leaf, _, _, _, _ => rfl
  | .introduce v child, hval, α₁, α₂, h => by
    simp only [dpSpec]
    rw [List.all_congr rfl fun c => ?_,
      dpSpec_congr A q hq sem F U hval.2 fun u hu => h u (Finset.mem_insert_of_mem hu)]
    by_cases hc : c.scope.toFinset ⊆ insert v child.bag
    · rw [Constraint.eval_congr (τ := α₂) fun u hu => h u (hc (List.mem_toFinset.2 hu))]
    · simp [hc]
  | .forget v child, hval, α₁, α₂, h => by
    have hupd (d : Fin q) :
        dpSpec A q hq sem F U child (Function.update α₁ v d) =
          dpSpec A q hq sem F U child (Function.update α₂ v d) :=
      dpSpec_congr A q hq sem F U hval.2 fun u hu => by
        by_cases huv : u = v
        · simp [huv]
        · simp [huv, h u (Finset.mem_erase.2 ⟨huv, hu⟩)]
    simp only [dpSpec]
    split_ifs with hvU
    · refine dpAlgFold_congr fun d _ => ?_
      by_cases hd : d < q
      · simp only [hd, ↓reduceDIte, hupd]
      · simp [hd]
    · exact hupd ⟨0, hq⟩
  | .join left right, hval, α₁, α₂, h => by
    simp only [dpSpec]
    have hL : ∀ u ∈ left.bag, α₁ u = α₂ u := h
    have hR : ∀ u ∈ right.bag, α₁ u = α₂ u := fun u hu => h u (hval.1 ▸ hu)
    rw [dpSpec_congr A q hq sem F U hval.2.2.1 hL,
      dpSpec_congr A q hq sem F U hval.2.2.2 hR]

private theorem getD_dpTree {β : Type} (A : DPAlg β) (q : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) :
    ∀ {T : NiceTree V}, T.LocalValid →
      ∀ {m : ℕ}, m < q ^ (bagList T).length →
        (dpTree A q hq sem F F.vars T).getD m A.zero =
          dpSpec A q hq sem F F.vars.toFinset T (ofRadixFin q hq (bagList T) m)
  | .leaf, _, m, hm => by
    simp only [bagList, List.length_nil, Nat.pow_zero, Nat.lt_one_iff] at hm
    subst hm
    simp only [dpTree, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
      List.getElem?_cons_zero, Option.getD_some, dpSpec]
  | .introduce v child, hval, m, hm => by
    have hm' : m < q * q ^ (bagList child).length := by
      rw [Nat.mul_comm]
      simpa only [bagList, List.length_cons, Nat.pow_succ] using hm
    have hcongr : ∀ u ∈ child.bag,
        ofRadixFin q hq (bagList child) (m / q) u =
          ofRadixFin q hq (v :: bagList child) m u := fun u hu => by
      have huv : u ≠ v := fun h => hval.1 (child.bag_subset_subtreeVerts (h ▸ hu))
      ext
      exact (ofRadix_cons_ne huv (bagList child) m).symm
    dsimp only [dpTree]
    rw [getD_ofFn _ (by simpa only [bagList] using hm) A.zero]
    simp only [bagList, dpSpec]
    rw [getD_dpTree A q hq sem F hval.2 (Nat.div_lt_of_lt_mul hm'),
      dpSpec_congr A q hq sem F F.vars.toFinset hval.2 hcongr]
    exact if_congr (by simp [toFinset_bagList hval.2]) rfl rfl
  | .forget v child, hval, m, hm => by
    have hbagC : (bagList child).toFinset = child.bag := toFinset_bagList hval.2
    have hret : ∀ d (hd : d < q),
        let idx := toRadix q (bagList child)
          (Function.update (ofRadix q ((bagList child).erase v) m) v d)
        (dpTree A q hq sem F F.vars child).getD idx A.zero =
          dpSpec A q hq sem F F.vars.toFinset child
            (Function.update (ofRadixFin q hq ((bagList child).erase v) m) v
              ⟨d, hd⟩) := fun d hd => by
      intro idx
      have hidx : idx < q ^ (bagList child).length := toRadix_lt hq _ _
      have ih := getD_dpTree A q hq sem F hval.2 hidx
      have hagree : ∀ u ∈ child.bag,
          ofRadixFin q hq (bagList child) idx u =
            Function.update (ofRadixFin q hq ((bagList child).erase v) m) v
              ⟨d, hd⟩ u := fun u hu => by
        have huC : u ∈ bagList child := List.mem_toFinset.1 (hbagC ▸ hu)
        have hlt : ∀ w ∈ bagList child,
            Function.update (ofRadix q ((bagList child).erase v) m) v d w < q := by
          intro w _
          by_cases hwv : w = v
          · simpa [hwv] using hd
          · simpa [hwv] using ofRadix_lt hq ((bagList child).erase v) m w
        ext
        dsimp only [idx, ofRadixFin]
        rw [ofRadix_toRadix hq hlt huC]
        by_cases huv : u = v
        · simp only [huv, Function.update_self]
        · simp only [Function.update_of_ne huv]
          rfl
      rw [ih, dpSpec_congr A q hq sem F F.vars.toFinset hval.2 hagree]
    dsimp only [dpTree]
    rw [getD_ofFn _ (by simpa only [bagList] using hm) A.zero]
    simp only [bagList, dpSpec]
    by_cases hv : v ∈ F.vars
    · simp only [hv, ite_true, List.mem_toFinset]
      exact dpAlgFold_congr fun d hd => by simpa only [hd, ↓reduceDIte] using hret d hd
    · simp only [hv, ite_false, List.mem_toFinset]
      exact hret 0 hq
  | .join left right, hval, m, hm => by
    have ihL := getD_dpTree A q hq sem F hval.2.2.1 (m := m) (by simpa only [bagList] using hm)
    have ihR := getD_dpTree A q hq sem F hval.2.2.2
      (toRadix_lt hq (bagList right) (ofRadix q (bagList left) m))
    have hbagR : (bagList right).toFinset = right.bag := toFinset_bagList hval.2.2.2
    have hagree : ∀ u ∈ right.bag,
        ofRadixFin q hq (bagList right) (toRadix q (bagList right) (ofRadix q (bagList left) m)) u =
          ofRadixFin q hq (bagList left) m u := fun u hu => by
      have huR : u ∈ bagList right := List.mem_toFinset.1 (hbagR ▸ hu)
      ext
      dsimp only [ofRadixFin]
      exact ofRadix_toRadix hq (fun w _ => ofRadix_lt hq (bagList left) m w) huR
    dsimp only [dpTree]
    rw [getD_ofFn _ (by simpa only [bagList] using hm) A.zero]
    simp only [bagList, dpSpec]
    rw [ihL, ihR, dpSpec_congr A q hq sem F F.vars.toFinset hval.2.2.2 hagree]

private theorem dpSpec_dpCountAlg_eq {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (U : Finset V) :
    ∀ T α, dpSpec dpCountAlg q hq sem F U T α =
      @CSP.specDPCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩ sem F U T α
  | .leaf, α => by
    dsimp only [dpSpec, CSP.specDPCount, dpCountAlg]
    exact if_congr (by simp [List.all_eq_true, imp_iff_not_or]) rfl rfl
  | .introduce v child, α => by
    dsimp only [dpSpec, CSP.specDPCount]
    rw [dpSpec_dpCountAlg_eq hq sem F U child α]
    exact if_congr (by simp [List.all_eq_true, imp_iff_not_or, or_assoc]) rfl rfl
  | .forget v child, α => by
    dsimp only [dpSpec, CSP.specDPCount]
    split_ifs with hvU
    · dsimp only [dpCountAlg]
      rw [dpAlgFold_nat, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [dite_eq_left d.isLt, Fin.eta]
      exact dpSpec_dpCountAlg_eq hq sem F U child _
    · exact dpSpec_dpCountAlg_eq hq sem F U child _
  | .join left right, α => by
    dsimp only [dpSpec, CSP.specDPCount]
    rw [dpSpec_dpCountAlg_eq hq sem F U left α, dpSpec_dpCountAlg_eq hq sem F U right α]
    rfl

private theorem dpSpec_dpDecideAlg_eq {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (U : Finset V) :
    ∀ T α, dpSpec dpDecideAlg q hq sem F U T α =
      @CSP.specDPDecide _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩ sem F U T α
  | .leaf, α => by
    dsimp only [dpSpec, CSP.specDPDecide, dpDecideAlg]
    cases h : F.all fun c => !decide (c.scope = []) || c.eval sem (fun _ => ⟨0, hq⟩) <;> simp
  | .introduce v child, α => by
    dsimp only [dpSpec, CSP.specDPDecide]
    rw [dpSpec_dpDecideAlg_eq hq sem F U child α]
    have hall : (F.all fun c => !(decide (c.scope.toFinset ⊆ insert v child.bag) &&
        decide (v ∈ c.scope)) || c.eval sem α) =
      (F.all fun c => !decide (c.scope.toFinset ⊆ insert v child.bag) ||
        !decide (v ∈ c.scope) || c.eval sem α) := by
      simp only [Bool.not_and, Bool.or_assoc]
    rw [hall]
    dsimp only [dpDecideAlg]
    cases h : F.all fun c => !decide (c.scope.toFinset ⊆ insert v child.bag) ||
        !decide (v ∈ c.scope) || c.eval sem α <;> simp
  | .forget v child, α => by
    dsimp only [dpSpec, CSP.specDPDecide]
    split_ifs with hvU
    · rw [show dpAlgFold dpDecideAlg.zero dpDecideAlg.add = dpAlgFold false (· || ·) from rfl,
        dpAlgFold_bool]
      congr 1
      simp only [eq_iff_iff]
      refine ⟨fun ⟨d, hd, h⟩ => ⟨⟨d, hd⟩, ?_⟩, fun ⟨d, h⟩ => ⟨d.val, d.isLt, ?_⟩⟩
      · simpa only [dite_eq_left hd, dpSpec_dpDecideAlg_eq] using h
      · simpa only [dite_eq_left d.isLt, Fin.eta, dpSpec_dpDecideAlg_eq] using h
    · exact dpSpec_dpDecideAlg_eq hq sem F U child _
  | .join left right, α => by
    dsimp only [dpSpec, CSP.specDPDecide]
    rw [dpSpec_dpDecideAlg_eq hq sem F U left α, dpSpec_dpDecideAlg_eq hq sem F U right α]
    rfl

theorem getD_cspCountTree {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) {T : NiceTree V} (hval : T.LocalValid) {m : ℕ}
    (hm : m < q ^ (bagList T).length) :
    (cspCountTree q hq sem F F.vars T).getD m 0 =
      @CSP.specDPCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩
        sem F F.vars.toFinset T (ofRadixFin q hq (bagList T) m) :=
  (getD_dpTree dpCountAlg q hq sem F hval hm).trans (dpSpec_dpCountAlg_eq hq sem F _ _ _)

theorem getD_cspDecideTree {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) {T : NiceTree V} (hval : T.LocalValid) {m : ℕ}
    (hm : m < q ^ (bagList T).length) :
    (cspDecideTree q hq sem F F.vars T).getD m false =
      @CSP.specDPDecide _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩
        sem F F.vars.toFinset T (ofRadixFin q hq (bagList T) m) :=
  (getD_dpTree dpDecideAlg q hq sem F hval hm).trans (dpSpec_dpDecideAlg_eq hq sem F _ _ _)

end Engine

/-! ### Top-level CSP solvers on nice and rooted tree decompositions -/

section Wrappers

variable {Rel V : Type*} [DecidableEq V]

/-- Exact model count computed from a supplied nice tree `T`. -/
@[expose] def cspCountNiceTree (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (T : NiceTree V) : ℕ :=
  (cspCountTree q hq sem F F.vars T).getD 0 0

/-- Satisfiability decision computed from a supplied nice tree `T`. -/
@[expose] def cspDecideNiceTree (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (T : NiceTree V) : Bool :=
  (cspDecideTree q hq sem F F.vars T).getD 0 false

theorem cspCountNiceTree_eq_modelCount {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    {F : CSP Rel V} {T : NiceTree V} (hval : T.LocalValid) (hbag : T.bag = ∅)
    (hsub : F.vars.toFinset ⊆ T.subtreeVerts) (hcov : ∀ c ∈ F, T.CoversFinset c.scope.toFinset) :
    cspCountNiceTree q hq sem F T =
      @CSP.modelCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩ sem F := by
  have hm : 0 < q ^ (bagList T).length := Nat.one_le_pow _ _ hq
  rw [cspCountNiceTree, getD_cspCountTree hq sem F hval hm]
  exact @CSP.specDPCount_eq_modelCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩
    sem F T hval hbag hsub hcov _

theorem cspDecideNiceTree_eq_true_iff {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    {F : CSP Rel V} {T : NiceTree V} (hval : T.LocalValid) (hbag : T.bag = ∅)
    (hsub : F.vars.toFinset ⊆ T.subtreeVerts) (hcov : ∀ c ∈ F, T.CoversFinset c.scope.toFinset) :
    cspDecideNiceTree q hq sem F T = true ↔ CSP.Satisfiable sem F := by
  have hm : 0 < q ^ (bagList T).length := Nat.one_le_pow _ _ hq
  rw [cspDecideNiceTree, getD_cspDecideTree hq sem F hval hm]
  exact @CSP.specDPDecide_eq_true_iff_satisfiable _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩
    sem F T hval hbag hsub hcov _

/-- Exact model count on a nice tree decomposition of `F.primalGraph`. -/
@[expose] def cspCountNice (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (N : F.primalGraph.NiceTreeDecomposition) : ℕ :=
  cspCountNiceTree q hq sem F N.tree

/-- Satisfiability decision on a nice tree decomposition of `F.primalGraph`. -/
@[expose] def cspDecideNice (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (N : F.primalGraph.NiceTreeDecomposition) : Bool :=
  cspDecideNiceTree q hq sem F N.tree

theorem cspCountNice_eq_modelCount {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    {F : CSP Rel V} (N : F.primalGraph.NiceTreeDecomposition) :
    cspCountNice q hq sem F N =
      @CSP.modelCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩ sem F :=
  cspCountNiceTree_eq_modelCount hq sem N.localValid N.bag_root (fun v _ => N.exists_mem_bag v)
    (fun _ hc => F.exists_coversFinset_scope_of_mem N hc)

theorem cspDecideNice_eq_true_iff {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    {F : CSP Rel V} (N : F.primalGraph.NiceTreeDecomposition) :
    cspDecideNice q hq sem F N = true ↔ CSP.Satisfiable sem F :=
  cspDecideNiceTree_eq_true_iff hq sem N.localValid N.bag_root (fun v _ => N.exists_mem_bag v)
    (fun _ hc => F.exists_coversFinset_scope_of_mem N hc)

/-- Exact model count on a nice tree decomposition of `F.activePrimalGraph`. -/
@[expose] def cspCountActiveNice (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (N : F.activePrimalGraph.NiceTreeDecomposition) : ℕ :=
  cspCountNiceTree q hq sem F (CSP.liftActiveNiceTree N)

/-- Satisfiability decision on a nice tree decomposition of `F.activePrimalGraph`. -/
@[expose] def cspDecideActiveNice (q : ℕ) (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    (F : CSP Rel V) (N : F.activePrimalGraph.NiceTreeDecomposition) : Bool :=
  cspDecideNiceTree q hq sem F (CSP.liftActiveNiceTree N)

theorem cspCountActiveNice_eq_modelCount {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    {F : CSP Rel V} (N : F.activePrimalGraph.NiceTreeDecomposition) :
    cspCountActiveNice q hq sem F N =
      @CSP.modelCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩ sem F :=
  cspCountNiceTree_eq_modelCount hq sem (CSP.liftActiveNiceTree_localValid N)
    (CSP.liftActiveNiceTree_bag N) (by rw [CSP.liftActiveNiceTree_subtreeVerts])
    (fun _ hc => CSP.liftActiveNiceTree_coversFinset N hc)

theorem cspDecideActiveNice_eq_true_iff {q : ℕ} (hq : 0 < q) (sem : Rel → List (Fin q) → Bool)
    {F : CSP Rel V} (N : F.activePrimalGraph.NiceTreeDecomposition) :
    cspDecideActiveNice q hq sem F N = true ↔ CSP.Satisfiable sem F :=
  cspDecideNiceTree_eq_true_iff hq sem (CSP.liftActiveNiceTree_localValid N)
    (CSP.liftActiveNiceTree_bag N) (by rw [CSP.liftActiveNiceTree_subtreeVerts])
    (fun _ hc => CSP.liftActiveNiceTree_coversFinset N hc)

/-- Exact model count on a rooted tree decomposition of `F.primalGraph` via `toNiceTreePruned`. -/
@[expose] def cspCountRooted [LinearOrder V] (q : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) {n : ℕ}
    (R : F.primalGraph.RootedTreeDecomposition n) : ℕ :=
  cspCountNice q hq sem F R.toNiceTreePruned

/-- Satisfiability decision on a rooted tree decomposition of `F.primalGraph` via
`toNiceTreePruned`. -/
@[expose] def cspDecideRooted [LinearOrder V] (q : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) {n : ℕ}
    (R : F.primalGraph.RootedTreeDecomposition n) : Bool :=
  cspDecideNice q hq sem F R.toNiceTreePruned

theorem cspCountRooted_eq_modelCount [LinearOrder V] {q : ℕ} (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) {F : CSP Rel V} {n : ℕ}
    (R : F.primalGraph.RootedTreeDecomposition n) :
    cspCountRooted q hq sem F R =
      @CSP.modelCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩ sem F :=
  cspCountNice_eq_modelCount hq sem R.toNiceTreePruned

theorem cspDecideRooted_eq_true_iff [LinearOrder V] {q : ℕ} (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) {F : CSP Rel V} {n : ℕ}
    (R : F.primalGraph.RootedTreeDecomposition n) :
    cspDecideRooted q hq sem F R = true ↔ CSP.Satisfiable sem F :=
  cspDecideNice_eq_true_iff hq sem R.toNiceTreePruned

/-- Exact model count on a rooted tree decomposition of `F.activePrimalGraph` via
`toNiceTreePruned`. -/
@[expose] def cspCountActiveRooted [LinearOrder V] (q : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) {n : ℕ}
    (R : F.activePrimalGraph.RootedTreeDecomposition n) : ℕ :=
  cspCountActiveNice q hq sem F R.toNiceTreePruned

/-- Satisfiability decision on a rooted tree decomposition of `F.activePrimalGraph` via
`toNiceTreePruned`. -/
@[expose] def cspDecideActiveRooted [LinearOrder V] (q : ℕ) (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) (F : CSP Rel V) {n : ℕ}
    (R : F.activePrimalGraph.RootedTreeDecomposition n) : Bool :=
  cspDecideActiveNice q hq sem F R.toNiceTreePruned

theorem cspCountActiveRooted_eq_modelCount [LinearOrder V] {q : ℕ} (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) {F : CSP Rel V} {n : ℕ}
    (R : F.activePrimalGraph.RootedTreeDecomposition n) :
    cspCountActiveRooted q hq sem F R =
      @CSP.modelCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩ sem F :=
  cspCountActiveNice_eq_modelCount hq sem R.toNiceTreePruned

theorem cspDecideActiveRooted_eq_true_iff [LinearOrder V] {q : ℕ} (hq : 0 < q)
    (sem : Rel → List (Fin q) → Bool) {F : CSP Rel V} {n : ℕ}
    (R : F.activePrimalGraph.RootedTreeDecomposition n) :
    cspDecideActiveRooted q hq sem F R = true ↔ CSP.Satisfiable sem F :=
  cspDecideActiveNice_eq_true_iff hq sem R.toNiceTreePruned

end Wrappers

/-! ### Finite inhabited domain equivalence bridge -/

section DomainBridge

variable {Rel V D : Type*} [DecidableEq V] [Fintype D] [Inhabited D]

/-- Pull back constraint semantics across `e : D ≃ Fin q`. -/
@[expose] def semFin {q : ℕ} (sem : Rel → List D → Bool) (e : D ≃ Fin q) :
    Rel → List (Fin q) → Bool :=
  fun r xs => sem r (xs.map e.symm)

omit [DecidableEq V] [Fintype D] [Inhabited D] in
theorem eval_semFin {q : ℕ} (sem : Rel → List D → Bool) (e : D ≃ Fin q)
    (σ : V → Fin q) (F : CSP Rel V) :
    CSP.eval (semFin sem e) σ F = CSP.eval sem (fun v => e.symm (σ v)) F := by
  unfold CSP.eval Constraint.eval semFin
  simp only [List.map_map]
  rfl

omit [DecidableEq V] [Fintype D] [Inhabited D] in
theorem satisfiable_semFin_iff {q : ℕ} (sem : Rel → List D → Bool) (e : D ≃ Fin q)
    (F : CSP Rel V) :
    CSP.Satisfiable (semFin sem e) F ↔ CSP.Satisfiable sem F := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨fun v => e.symm (σ v), (eval_semFin sem e σ F).symm ▸ hσ⟩
  · rintro ⟨τ, hτ⟩
    refine ⟨fun v => e (τ v), ?_⟩
    rw [eval_semFin]
    simpa [Function.comp_def] using hτ

theorem modelCount_semFin {q : ℕ} (hq : 0 < q) (sem : Rel → List D → Bool) (e : D ≃ Fin q)
    (F : CSP Rel V) :
    @CSP.modelCount _ _ (Fin q) _ inferInstance ⟨⟨0, hq⟩⟩ (semFin sem e) F =
      CSP.modelCount sem F := by
  classical
  let _ : Inhabited (Fin q) := ⟨⟨0, hq⟩⟩
  unfold CSP.modelCount CSP.modelCountOn
  refine Finset.card_bij (fun σ _ v => e.symm (σ v)) ?_ (fun _ _ _ _ h => funext fun v =>
      e.symm.injective (congrFun h v)) ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [eval_semFin] at hσ
    exact (CSP.eval_congr fun v hv => by simp [List.mem_toFinset.2 hv]).trans hσ
  · intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
    refine ⟨fun v => e (τ v), Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, funext fun v => by simp⟩
    rw [eval_semFin]
    exact (CSP.eval_congr fun v hv => by simp [List.mem_toFinset.2 hv]).trans hτ

theorem cspCountNice_equiv (sem : Rel → List D → Bool) {F : CSP Rel V}
    (N : F.primalGraph.NiceTreeDecomposition) (e : D ≃ Fin (Fintype.card D)) :
    cspCountNice (Fintype.card D) Fintype.card_pos (semFin sem e) F N =
      CSP.modelCount sem F := by
  rw [cspCountNice_eq_modelCount Fintype.card_pos (semFin sem e) N,
    modelCount_semFin Fintype.card_pos sem e F]

theorem cspDecideNice_equiv (sem : Rel → List D → Bool) {F : CSP Rel V}
    (N : F.primalGraph.NiceTreeDecomposition) (e : D ≃ Fin (Fintype.card D)) :
    cspDecideNice (Fintype.card D) Fintype.card_pos (semFin sem e) F N = true ↔
      CSP.Satisfiable sem F :=
  (cspDecideNice_eq_true_iff Fintype.card_pos (semFin sem e) N).trans
    (satisfiable_semFin_iff sem e F)

end DomainBridge

end Cslib.Algorithms.Lean.TreeDecomposition
