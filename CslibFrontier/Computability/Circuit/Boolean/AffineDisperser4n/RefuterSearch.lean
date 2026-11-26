/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Refuter
import all CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.Refuter

/-!
# The refuter's final search finds a counterexample

`findCounterexample C f d S` enumerates `2^d` points of `Φ(Z(P))` built from the free parameters
of `S`. When `S` is a valid terminal state for the function of `C` (no refuter step applies) with
`d < S.a`, the output of `S` is constant on the enumerated `d`-dimensional affine subspace, so a
`d`-affine disperser `f` disagrees with `C` at one of the enumerated points.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser4n.findCounterexample_spec`: every returned point is a
  counterexample.
* `Cslib.Circuits.Boolean.AffineDisperser4n.findCounterexample_isSome`: on a valid terminal state
  with `d < S.a`, the search returns a point.
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Cslib.Circuits.Boolean.AffineDisperserCore
open Cslib.Circuits.Boolean.AffineDisperserCore.State
open Cslib.Circuits.Boolean.SemiCircuit
open Cslib.Complexity.XORSAT.Dense Cslib.Circuits Cslib.BitString

/-! ### List utilities -/

private theorem mem_allAssignments : ∀ {d : ℕ} {A : List Bool}, A.length = d → A ∈ allAssignments d
  | 0, A, h => by simp [allAssignments, List.eq_nil_of_length_eq_zero h]
  | d + 1, [], h => by simp at h
  | d + 1, b :: A, h => by
    have hA : A ∈ allAssignments d := mem_allAssignments (by simpa using h)
    cases b <;> simp [allAssignments, hA]

/-! ### `findPair` and `terminalVal` -/

variable {n : ℕ}

/-- A pair found by `findPair S x` is a pair of `S` containing `x`. -/
theorem findPair_spec {S : State n} {x : ℕ} {pr : ZeroPair} (h : findPair S x = some pr) :
    pr ∈ S.pairs ∧ (pr.fst = x ∨ pr.snd = x) := by
  obtain ⟨r, -, hr⟩ := List.exists_of_findSome?_eq_some h
  have hmem := List.mem_of_find?_eq_some hr
  have hp := List.find?_some hr
  refine ⟨by simpa using hp, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- On a valid state, `findPair S x` finds a pair whenever `x` belongs to one. -/
theorem findPair_isSome {f : BooleanFunction n} {S : State n} (hS : S.Valid f)
    {pr : ZeroPair}
    (hpr : pr ∈ S.pairs) {x : ℕ} (hx : pr.Contains x) : (findPair S x).isSome := by
  have hmem := hS.pair_mem pr hpr
  obtain ⟨fst, b₁, snd, b₂⟩ := pr
  rcases hx with hx | hx <;> simp only at hx <;> subst hx
  · refine List.findSome?_isSome_iff.2 ⟨snd, (Finset.mem_sort _).2 hmem.2.1, ?_⟩
    exact List.find?_isSome.2 ⟨⟨fst, b₁, snd, b₂⟩, by cases b₁ <;> cases b₂ <;> simp,
      by simpa using hpr⟩
  · refine List.findSome?_isSome_iff.2 ⟨fst, (Finset.mem_sort _).2 hmem.1, ?_⟩
    exact List.find?_isSome.2 ⟨⟨fst, b₁, snd, b₂⟩, by cases b₁ <;> cases b₂ <;> simp,
      by simpa using hpr⟩

private theorem eq_of_findPair_eq_some {f : BooleanFunction n} {S : State n} (hS : S.Valid f)
    {x : ℕ}
    {pr pr' : ZeroPair} (h : findPair S x = some pr') (hpr : pr ∈ S.pairs) (hx : pr.fst = x) :
    pr' = pr := by
  obtain ⟨hpr', hx'⟩ := findPair_spec h
  by_contra hne
  have := hS.pairs_disjoint pr' hpr' pr hpr hne
  rcases hx' with h' | h' <;> simp only at this <;> omega

private theorem isFstOfAnyPair_eq_true_iff {f : BooleanFunction n} {S : State n} (hS : S.Valid f)
    {x : ℕ} : isFstOfAnyPair S x = true ↔ ∃ pr ∈ S.pairs, pr.fst = x := by
  unfold isFstOfAnyPair
  rcases h : findPair S x with _ | pr
  · simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    exact fun pr hpr hx => by simpa [h] using findPair_isSome hS hpr (Or.inl hx)
  · simp only [decide_eq_true_eq]
    exact ⟨fun hx => ⟨pr, (findPair_spec h).1, hx⟩,
      fun ⟨pr', hpr', hx⟩ => eq_of_findPair_eq_some hS h hpr' hx ▸ hx⟩

private theorem terminalVal_fst {f : BooleanFunction n} {S : State n} (hS : S.Valid f) (L : List ℕ)
    (A : List Bool) {pr : ZeroPair} (hpr : pr ∈ S.pairs) :
    terminalVal S L A pr.fst = pr.fstBias := by
  obtain ⟨pr', h'⟩ := Option.isSome_iff_exists.1 (findPair_isSome hS hpr (Or.inl rfl))
  obtain rfl := eq_of_findPair_eq_some hS h' hpr rfl
  simp [terminalVal, h']

private theorem findIdx?_eq_some_of_nodup {L : List ℕ} (hL : L.Nodup) {j : ℕ} (hj : j < L.length) :
    L.findIdx? (· = L[j]) = some j := by
  rw [List.findIdx?_eq_some_iff_getElem]
  exact ⟨hj, decide_eq_true rfl, fun k hk =>
    mt of_decide_eq_true ((hL.getElem_inj_iff (hi := hk.trans hj) (hj := hj)).not.2 hk.ne)⟩

private theorem terminalVal_of_getElem {S : State n} {L : List ℕ} (hL : L.Nodup) (A : List Bool)
    {j : ℕ} (hj : j < L.length) (hfst : isFstOfAnyPair S L[j] = false) :
    terminalVal S L A L[j] = A.getD j false := by
  unfold terminalVal
  rw [findIdx?_eq_some_of_nodup hL hj]
  rcases h : findPair S L[j] with _ | pr
  · rfl
  · simp only [isFstOfAnyPair, h, decide_eq_false_iff_not] at hfst
    simp [hfst]

private theorem isAffine_getD_ofFn {d : ℕ} (i : ℕ) :
    IsAffine fun u : BitString d => (List.ofFn u).getD i false := by
  intro a b c
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases hi : i < d
  · simp [hi]
  · simp [hi]; rfl

private theorem isAffine_terminalVal {d : ℕ} (S : State n) (L : List ℕ) (x : ℕ) :
    IsAffine fun u : BitString d => terminalVal S L (List.ofFn u) x := by
  unfold terminalVal
  rcases findPair S x with _ | pr
  · cases L.findIdx? (· = x)
    exacts [isAffine_const Bool.xor_self false, isAffine_getD_ofFn _]
  · by_cases h : pr.fst = x
    · simpa [h] using isAffine_const Bool.xor_self pr.fstBias
    · simp only [h, ite_false]
      cases L.findIdx? (· = x)
      exacts [isAffine_const Bool.xor_self false, isAffine_getD_ofFn _]

/-! ### The free parameters -/

/-- The free parameters scanned by `findCounterexample`. -/
private abbrev freeParams (S : State n) : List ℕ :=
  (S.params.sort (· ≤ ·)).filter (fun x => !(isFstOfAnyPair S x))

private theorem nodup_freeParams (S : State n) : (freeParams S).Nodup :=
  (Finset.sort_nodup _ _).filter _

private theorem mem_freeParams {S : State n} {x : ℕ} :
    x ∈ freeParams S ↔ x ∈ S.params ∧ isFstOfAnyPair S x = false := by
  simp [freeParams]

private theorem length_freeParams {f : BooleanFunction n} {S : State n} (hS : S.Valid f) :
    (freeParams S).length = S.a := by
  rw [← List.toFinset_card_of_nodup (nodup_freeParams S),
    ← hS.card_sdiff_image ZeroPair.fst (fun _ _ => Or.inl rfl)]
  refine congrArg Finset.card (Finset.ext fun x => ?_)
  simp [← Bool.not_eq_true, isFstOfAnyPair_eq_true_iff hS]

/-! ### The generic search -/

private theorem inj_of_coords {d : ℕ} {S : State n} (σ : List Bool → ℕ → Bool) {L : List ℕ}
    (hLp : ∀ x ∈ L, x ∈ S.params) (hlen : L.length = d)
    (hcoord : ∀ A j (hj : j < L.length), σ A L[j] = A.getD j false) :
    ∀ u v : BitString d, (∀ j ∈ S.params, σ (List.ofFn u) j = σ (List.ofFn v) j) → u = v := by
  intro u v h
  funext ⟨j, hj⟩
  have hj' : j < L.length := hlen ▸ hj
  have := h L[j] (hLp _ (List.getElem_mem hj'))
  rw [hcoord _ _ hj', hcoord _ _ hj'] at this
  simpa [List.getD_eq_getElem?_getD, hj] using this

private theorem locus_of_fst {S : State n} {σ : ℕ → Bool}
    (hfst : ∀ pr ∈ S.pairs, σ pr.fst = pr.fstBias) : S.Locus σ := fun pr hpr =>
  ZeroPair.holds_of_eq_bias (x := pr.fst) (Or.inl rfl) (by simp [ZeroPair.bias, hfst pr hpr])

private theorem findSome_isSome_of_family {d : ℕ} (C : Circuit (fullSignature 2 Bool) n 1)
    (f : BitString n → Bool) (hf : IsAffineDisperser f d) {S : State n}
    (hS : S.Valid (fun x => C.eval fullInterpretation x 0)) (σ : List Bool → ℕ → Bool)
    (hσ : ∀ x, IsAffine fun u : BitString d => σ (List.ofFn u) x)
    {L : List ℕ} (hLp : ∀ x ∈ L, x ∈ S.params) (hlen : L.length = d)
    (hcoord : ∀ A j (hj : j < L.length), σ A L[j] = A.getD j false)
    (hlocus : ∀ A, S.Locus (σ A)) (b : Bool)
    (hout : ∀ A val, S.Consistent val → (∀ j ∈ S.params, val j = σ A j) → S.out.eval val = b) :
    ((allAssignments d).findSome? fun A =>
      let x_vec : BitString n := S.phi fun y =>
        if decide (y ∈ S.params) then σ A y else evaluateAux S y (σ A)
      if C.eval fullInterpretation x_vec 0 != f x_vec then some x_vec else none).isSome := by
  set g : BitString d → BitString n := fun u => S.phi (σ (List.ofFn u)) with hg_def
  have hgaff : IsAffine g := by
    have : IsAffine fun u : BitString d => σ (List.ofFn u) :=
      fun x y z => funext fun i => hσ i x y z
    exact hS.phi_affine.comp this
  have hginj : Function.Injective g := fun u v h =>
    inj_of_coords σ hLp hlen hcoord u v (hS.phi_injective _ _ h)
  have hval : ∀ w, C.eval fullInterpretation (g w) 0 = b := by
    intro w
    obtain ⟨val, hv, hcons⟩ := hS.wf.exists_consistent (σ (List.ofFn w))
    have hlv : S.Locus val := fun pr hpr =>
      (ZeroPair.holds_congr (hv _ (hS.pair_mem pr hpr).1)
        (hv _ (hS.pair_mem pr hpr).2.1)).2 (hlocus _ pr hpr)
    have := hS.computes val hcons hlv
    rw [hout _ val hcons hv, hS.phi_congr val _ hv] at this
    exact this.symm
  obtain ⟨u, v, huv⟩ := hf g hgaff hginj
  have hx : ∀ w, (S.phi fun y => if decide (y ∈ S.params) then σ (List.ofFn w) y else
      evaluateAux S y (σ (List.ofFn w))) = g w :=
    fun w => hS.phi_congr _ _ fun j hj => by simp [hj]
  obtain ⟨w, hw⟩ : ∃ w, C.eval fullInterpretation (g w) 0 ≠ f (g w) :=
    if hu : C.eval fullInterpretation (g u) 0 = f (g u) then
      ⟨v, fun hv => huv (by rw [← hu, ← hv, hval, hval])⟩
    else ⟨u, hu⟩
  refine List.findSome?_isSome_iff.2
    ⟨List.ofFn w, mem_allAssignments (A := List.ofFn w) (by simp), ?_⟩
  rw [hx w]
  simp [hw]

private theorem terminalVal_coord {S : State n} {L : List ℕ} (hLn : L.Nodup)
    (hLF : ∀ x ∈ L, x ∈ freeParams S) (A : List Bool) (j : ℕ) (hj : j < L.length) :
    terminalVal S L A L[j] = A.getD j false :=
  terminalVal_of_getElem hLn A hj (mem_freeParams.1 (hLF _ (List.getElem_mem hj))).2

private theorem take_props {S : State n} {L₀ : List ℕ} (hn : L₀.Nodup)
    (hF : ∀ x ∈ L₀, x ∈ freeParams S)
    {d : ℕ} (hd : d ≤ L₀.length) :
    (L₀.take d).Nodup ∧ (∀ x ∈ L₀.take d, x ∈ freeParams S) ∧ (L₀.take d).length = d :=
  ⟨hn.sublist (List.take_sublist _ _), fun x hx => hF x (List.mem_of_mem_take hx),
    by rw [List.length_take]; omega⟩

private theorem fst_ne_of_mem_freeParams {f : BooleanFunction n} {S : State n} (hS : S.Valid f)
    {p : ℕ} (hp : p ∈ freeParams S) {pr : ZeroPair} (hpr : pr ∈ S.pairs) : pr.fst ≠ p := by
  rintro rfl
  have := (mem_freeParams.1 hp).2
  rw [← Bool.not_eq_true, isFstOfAnyPair_eq_true_iff hS] at this
  exact this ⟨pr, hpr, rfl⟩

/-- The search over the free parameters `L` with `terminalVal` succeeds when the output is
constant on the corresponding consistent assignments. -/
private theorem findSome_isSome_terminalVal {d : ℕ} (C : Circuit (fullSignature 2 Bool) n 1)
    (f : BitString n → Bool) (hf : IsAffineDisperser f d) {S : State n}
    (hS : S.Valid (fun x => C.eval fullInterpretation x 0)) {L : List ℕ}
    (hL : L.Nodup ∧ (∀ x ∈ L, x ∈ freeParams S) ∧ L.length = d) (b : Bool)
    (hout : ∀ A val, S.Consistent val → (∀ j ∈ S.params, val j = terminalVal S L A j) →
      S.out.eval val = b) :
    ((allAssignments d).findSome? fun A =>
      let x_vec : BitString n := S.phi fun y =>
        if decide (y ∈ S.params) then terminalVal S L A y else evaluateAux S y (terminalVal S L A)
      if C.eval fullInterpretation x_vec 0 != f x_vec then some x_vec else none).isSome :=
  findSome_isSome_of_family C f hf hS (fun A => terminalVal S L A) (isAffine_terminalVal S L)
    (fun x hx => (mem_freeParams.1 (hL.2.1 x hx)).1) hL.2.2 (terminalVal_coord hL.1 hL.2.1)
    (fun A => locus_of_fst fun _ hpr => terminalVal_fst hS L A hpr) b hout

private theorem foldl_xor_eq_sum (g : ℕ → Bool) (T : Finset ℕ) :
    (T.sort (· ≤ ·)).foldl (fun acc y => acc ^^ g y) false = ∑ y ∈ T, g y := by
  change (T.sort (· ≤ ·)).foldl (fun acc y => acc + g y) 0 = ∑ y ∈ T, g y
  rw [← List.foldl_map, ← List.sum_eq_foldl, ← List.sum_toFinset _ (Finset.sort_nodup _ _)]
  rw [Finset.sort_toFinset]

private theorem filter_ne_take_props {f : BooleanFunction n} {S : State n} (hS : S.Valid f) {p : ℕ}
    (hp : p ∈ freeParams S) {d : ℕ} (hd : d < S.a) :
    ((((freeParams S).filter (fun x => decide (x ≠ p))).take d).Nodup ∧
      (∀ x ∈ ((freeParams S).filter (fun x => decide (x ≠ p))).take d, x ∈ freeParams S) ∧
      (((freeParams S).filter (fun x => decide (x ≠ p))).take d).length = d) ∧
      ∀ x ∈ ((freeParams S).filter (fun x => decide (x ≠ p))).take d, x ≠ p := by
  refine ⟨?_, fun x hx => by simpa using (List.mem_filter.1 (List.mem_of_mem_take hx)).2⟩
  refine take_props ((nodup_freeParams S).filter _) (fun x hx => (List.mem_filter.1 hx).1) ?_
  have hfe : (freeParams S).filter (fun x => decide (x ≠ p)) = (freeParams S).erase p := by
    rw [(nodup_freeParams S).erase_eq_filter]
    congr 1
  rw [hfe, List.length_erase_of_mem hp, length_freeParams hS]
  omega

/-- The search pinning the free parameter `t` to `c A`, and reading the other parameters with
`terminalVal` over `d` further free parameters, succeeds when the output is constant on the
corresponding consistent assignments. -/
private theorem findSome_isSome_pin {d : ℕ} (C : Circuit (fullSignature 2 Bool) n 1)
    (f : BitString n → Bool) (hf : IsAffineDisperser f d) {S : State n}
    (hS : S.Valid (fun x => C.eval fullInterpretation x 0)) {t : ℕ} (ht : t ∈ freeParams S)
    (ha : d < S.a) (c : List Bool → Bool) (hc : IsAffine fun u : BitString d => c (List.ofFn u))
    (b : Bool) (hout : ∀ A val, S.Consistent val → (∀ j ∈ S.params, val j =
      if j = t then c A else terminalVal S (((freeParams S).filter (· ≠ t)).take d) A j) →
      S.out.eval val = b) :
    ((allAssignments d).findSome? fun A =>
      let σ := fun y => if y = t then c A else
        terminalVal S (((freeParams S).filter (· ≠ t)).take d) A y
      let x_vec : BitString n := S.phi fun y =>
        if decide (y ∈ S.params) then σ y else evaluateAux S y σ
      if C.eval fullInterpretation x_vec 0 != f x_vec then some x_vec else none).isSome := by
  obtain ⟨hL, hLt⟩ := filter_ne_take_props hS ht ha
  refine findSome_isSome_of_family C f hf hS
    (fun A y => if y = t then c A else terminalVal S (((freeParams S).filter (· ≠ t)).take d) A y)
    (fun x => ?_) (fun x hx => (mem_freeParams.1 (hL.2.1 x hx)).1) hL.2.2 (fun A j hj => ?_)
    (fun A => locus_of_fst fun pr hpr => ?_) b hout
  · by_cases hx : x = t
    · simpa [hx] using hc
    · simpa [hx] using isAffine_terminalVal S _ x
  · rw [ite_eq_right (hLt _ (List.getElem_mem hj))]
    exact terminalVal_coord hL.1 hL.2.1 A j hj
  · rw [ite_eq_right (fst_ne_of_mem_freeParams hS ht hpr)]
    exact terminalVal_fst hS _ A hpr

private theorem op_const_of_not_isAffineOp :
    ∀ op : Bool → Bool → Bool, ¬ IsAffineOp op →
      op (decide ((op true false == op true true) = true)) false =
        op (decide ((op true false == op true true) = true)) true := by
  intro op h
  simp only [beq_iff_eq]
  rw [and_form_spec h (decide (op true false = op true true)) false,
    and_form_spec h (decide (op true false = op true true)) true]
  cases decide (op true false = op true true) <;>
    cases decide (op false true = op true true) <;> rfl

/-- `fixArg g w` fixes the argument `w` of a non-affine gate to a value making it constant. -/
theorem fixArg_spec {g : Gate} (hg : ¬ IsAffineOp g.op) {a w : ℕ} (haw : a ≠ w)
    (hargs : (g.left = .node a ∧ g.right = .node w) ∨ (g.left = .node w ∧ g.right = .node a))
    (val : ℕ → Bool) (hw : val w = (fixArg g w).1) : g.eval val = (fixArg g w).2 := by
  obtain ⟨α, β, γ, H⟩ := exists_and_form hg
  rcases hargs with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · simp only [fixArg, hr, ite_true] at hw ⊢
    rw [Gate.eval_of_args hl hr, hw, H false false, H true false, H, H]
    cases α <;> cases β <;> cases γ <;> cases val a <;> decide
  · have hr' : g.right ≠ .node w := by rw [hr]; simpa using haw
    simp only [fixArg, hr', ite_false] at hw ⊢
    rw [Gate.eval_of_args hl hr, hw, H false false, H false true, H, H]
    cases α <;> cases β <;> cases γ <;> cases val a <;> decide

/-- Inversion of `findAndOnPair S = some (G, p)`. -/
theorem findAndOnPair_eq_some {S : State n} {G p : ℕ} (h : findAndOnPair S = some (G, p)) :
    G ∈ S.gates ∧ ¬ IsAffineOp (S.gate G).op ∧ S.Paired p ∧ ∃ w, p ≠ w ∧ p ∈ S.params ∧
      w ∈ S.params ∧ (S.gate G).Reads p ∧ (S.gate G).Reads w ∧ otherArg (S.gate G) p = w := by
  obtain ⟨G', hx, hg⟩ := List.exists_of_findSome?_eq_some h
  have hG' : G' ∈ S.gates := (Finset.mem_sort (· ≤ ·)).1 hx
  split_ifs at hg with hna
  rcases hl : (S.gate G').left with _ | p'
  · simp [hl] at hg
  rcases hr : (S.gate G').right with _ | w'
  · simp [hl, hr] at hg
  simp only [hl, hr] at hg
  split_ifs at hg with hc hp hw
  · cases hg
    refine ⟨hG', hna, hp, w', hc.1, hc.2.1, hc.2.2, Or.inl hl, Or.inr hr, ?_⟩
    simp [otherArg, hl, hr]
  · cases hg
    refine ⟨hG', hna, hw, p', fun h => hc.1 h.symm, hc.2.2, hc.2.1, Or.inr hr, Or.inl hl, ?_⟩
    simp only [otherArg, hl, hr]
    exact ite_eq_right hc.1

private theorem terminal_andOnPair {S : State n} {u G p : ℕ} (hterm : chooseStep? S = none)
    (hu : S.out.arg = .node u) (hup : u ∉ S.params) (hAOP : findAndOnPair S = some (G, p)) :
    u = G := by
  unfold chooseStep? at hterm
  rw [hu] at hterm
  simp only [hup, ite_false, hAOP] at hterm
  repeat' split at hterm
  all_goals try (simp at hterm; done)
  exact ‹u = G›

private theorem terminal_gate {S : State n} {u : ℕ} (hterm : chooseStep? S = none)
    (hu : S.out.arg = .node u) (hup : u ∉ S.params) (hAOP : findAndOnPair S = none)
    (hne : S.gates.Nonempty) :
    findD1 S = none ∧ findMovable S = none ∧
      S.auxIn (S.gates.min' hne) = 0 ∧ u = S.gates.min' hne := by
  unfold chooseStep? at hterm
  rw [hu] at hterm
  simp only [hup, ite_false, hAOP] at hterm
  repeat' split at hterm
  all_goals try (simp at hterm; done)
  all_goals first
    | exact absurd hne ‹¬S.gates.Nonempty›
    | exact ⟨Option.eq_none_iff_forall_ne_some.2 fun p hp =>
          ‹∀ p, findD1 S = some p → False› p hp,
        Option.eq_none_iff_forall_ne_some.2 fun p hp =>
          ‹∀ p, findMovable S = some p → False› p hp,
        Nat.eq_zero_of_not_pos ‹_›, ‹u = S.gates.min' _›⟩

private theorem terminal_gate_shape {f : BooleanFunction n} {S : State n} (hS : S.Valid f) {u : ℕ}
    (hterm : chooseStep? S = none) (hu : S.out.arg = .node u) (hup : u ∉ S.params)
    (hAOP : findAndOnPair S = none) (hne : S.gates.Nonempty) :
    ∃ t₁ t₂, (S.gate (S.gates.min' hne)).left = .node t₁ ∧
      (S.gate (S.gates.min' hne)).right = .node t₂ ∧ t₁ ∈ S.params ∧ ¬ S.Paired t₁ ∧
      ¬ IsAffineOp (S.gate (S.gates.min' hne)).op ∧ u = S.gates.min' hne := by
  obtain ⟨h1, hm, haux, huG⟩ := terminal_gate hterm hu hup hAOP hne
  set G := S.gates.min' hne with hG_def
  have hG : G ∈ S.gates := Finset.min'_mem _ _
  have hGs : G ∈ S.gates.sort (· ≤ ·) := (Finset.mem_sort _).2 hG
  obtain ⟨t₁, t₂, hl, hr, h12⟩ :
      ∃ t₁ t₂, (S.gate G).left = .node t₁ ∧ (S.gate G).right = .node t₂ ∧ t₁ ≠ t₂ := by
    have hdeg := List.find?_eq_none.1 h1 G hGs
    unfold isDegenerate at hdeg
    rcases hl : (S.gate G).left with b₁ | t₁ <;> rcases hr : (S.gate G).right with b₂ | t₂ <;>
      simp only [hl, hr, not_true_eq_false, decide_eq_true_eq] at hdeg
    exact ⟨t₁, t₂, rfl, rfl, hdeg⟩
  have hnotgate : ∀ t, (S.gate G).Reads t → t ∉ S.gates := fun t ht htg =>
    absurd (hS.wf.reads_lt G hG t htg ht) (not_lt.2 (Finset.min'_le _ _ htg))
  have hparam {t : ℕ} (ht : (S.gate G).Reads t) : t ∈ S.params := by
    have hta : t ∉ S.aux := fun h => by
      rcases ht with ht | ht <;> simp [State.auxIn, State.auxArg, ht, h] at haux
    simpa [live, hnotgate t ht, hta] using hS.wf.reads_live G hG t ht
  have ht₁p := hparam (Or.inl hl)
  have ht₂p := hparam (Or.inr hr)
  have hnaff : ¬ IsAffineOp (S.gate G).op := by
    have := List.find?_eq_none.1 hm G hGs
    simpa [hl, hr, isGate, hnotgate t₁ (Or.inl hl), hnotgate t₂ (Or.inr hr)] using this
  have hpaired : ¬ S.Paired t₁ := fun hp => by
    have := List.findSome?_eq_none_iff.1 hAOP G hGs
    simp [hl, hr, hnaff, ht₁p, ht₂p, h12, hp] at this
  exact ⟨t₁, t₂, hl, hr, ht₁p, hpaired, hnaff, huG⟩

/-- On a valid terminal state of the refuter for the function of `C` with `d < S.a`, the final
search of `findCounterexample` succeeds. -/
theorem findCounterexample_isSome {d : ℕ} (C : Circuit (fullSignature 2 Bool) n 1)
    (f : BitString n → Bool) (hf : IsAffineDisperser f d) {S : State n}
    (hS : S.Valid (fun x => C.eval fullInterpretation x 0)) (hterm : chooseStep? S = none)
    (ha : d < S.a)
    (hrep : ∀ u ∈ S.aux, S.AffineIn u (findAffineRep S u).1 (findAffineRep S u).2) :
    (findCounterexample C f d S).isSome := by
  unfold findCounterexample
  split
  · rename_i b hb
    refine findSome_isSome_terminalVal C f hf hS
      (take_props (nodup_freeParams S) (fun _ h => h) (by rw [length_freeParams hS]; omega))
      (b ^^ S.out.neg) fun A val _ _ => ?_
    simp [Lit.eval, hb, Arg.eval]
  · rename_i u hu
    split
    · rename_i hcase
      split
      rename_i c_out T_out hpair
      have hAff : S.AffineIn u c_out T_out := by
        by_cases hup : u ∈ S.params
        · simp only [hup, decide_true, ite_true, Prod.mk.injEq] at hpair
          obtain ⟨rfl, rfl⟩ := hpair
          exact affineIn_param hup
        · simp only [hup, decide_false, Bool.false_eq_true, ite_false] at hpair
          have hg : S.gates = ∅ := by simpa [hup] using hcase
          have hu_aux : u ∈ S.aux := by simpa [live, hup, hg] using hS.wf.out_live u hu
          simpa only [hpair] using hrep u hu_aux
      dsimp only
      split
      · rename_i pivot hpiv
        have hpF : pivot ∈ freeParams S := List.mem_of_find?_eq_some hpiv
        have hpT : pivot ∈ T_out := by simpa using List.find?_some hpiv
        set L := ((freeParams S).filter (fun x => decide (x ≠ pivot))).take d with hL_def
        refine findSome_isSome_pin C f hf hS hpF ha (fun A => c_out ^^ S.out.neg ^^
            List.foldl (fun acc y => acc ^^ terminalVal S L A y) false
              ({x ∈ T_out | x ≠ pivot}.sort (· ≤ ·))) ?_ false ?_
        · simp only [foldl_xor_eq_sum]
          exact isAffine_const_add_sum
            (σ := fun u : BitString d => fun y => terminalVal S L (List.ofFn u) y)
            (fun a b c => funext fun y => isAffine_terminalVal S L y a b c)
            (c_out ^^ S.out.neg) {x ∈ T_out | x ≠ pivot}
        · intro A val hcons hval
          have h1 := hAff.2 val hcons.1
          simp only [Lit.eval, hu, Arg.eval, h1]
          rw [← Finset.add_sum_erase _ _ hpT, hval pivot (hAff.1 hpT), ite_eq_left rfl,
            foldl_xor_eq_sum, Finset.filter_ne',
            Finset.sum_congr rfl fun y hy => (hval y (hAff.1 (Finset.mem_of_mem_erase hy))).trans
              (ite_eq_right (Finset.ne_of_mem_erase hy))]
          generalize ∑ y ∈ T_out.erase pivot, terminalVal S L A y = X
          cases c_out <;> cases S.out.neg <;> cases X <;> rfl
      · rename_i hpiv
        have hnot : ∀ v ∈ freeParams S, v ∉ T_out := fun v hv => by
          simpa using List.find?_eq_none.1 hpiv v hv
        refine findSome_isSome_terminalVal C f hf hS
          (take_props (nodup_freeParams S) (fun _ h => h) (by rw [length_freeParams hS]; omega))
          ((c_out + ∑ y ∈ T_out, terminalVal S ((freeParams S).take d) [] y) ^^ S.out.neg)
          fun A val hcons hval => ?_
        have hsum : ∑ y ∈ T_out, val y =
            ∑ y ∈ T_out, terminalVal S ((freeParams S).take d) [] y := by
          refine Finset.sum_congr rfl fun y hy => ?_
          have hyp := hAff.1 hy
          obtain ⟨pr, hpr, rfl⟩ := (isFstOfAnyPair_eq_true_iff hS).1
            (Bool.eq_true_of_not_eq_false fun h => hnot y (mem_freeParams.2 ⟨hyp, h⟩) hy)
          rw [hval _ hyp, terminalVal_fst hS _ _ hpr, terminalVal_fst hS _ _ hpr]
        simp only [Lit.eval, hu, Arg.eval, hAff.2 val hcons.1, hsum]
    · rename_i hcase
      have hup : u ∉ S.params := fun h => by simp [h] at hcase
      split
      · rename_i G p hAOP
        have huG : u = G := terminal_andOnPair hterm hu hup hAOP
        obtain ⟨hG, hna, hp, w, hpw, hppar, -, hGp, hGw, -⟩ := findAndOnPair_eq_some hAOP
        obtain ⟨pr₀, hpr₀, hc₀⟩ := hp
        obtain ⟨pr, hpr_eq⟩ := Option.isSome_iff_exists.1 (findPair_isSome hS hpr₀ hc₀)
        obtain ⟨hprm, hprp⟩ := findPair_spec hpr_eq
        simp only [hpr_eq]
        have ⟨hpr_fst_par, hpr_snd_par, hpr_ne⟩ := hS.pair_mem pr hprm
        have hsndF : pr.snd ∈ freeParams S := mem_freeParams.2 ⟨hpr_snd_par, by
          rw [← Bool.not_eq_true, isFstOfAnyPair_eq_true_iff hS]
          rintro ⟨pr', hpr', heq⟩
          by_cases hsame : pr' = pr
          · exact hpr_ne (hsame ▸ heq)
          · exact (hS.pairs_disjoint pr' hpr' pr hprm hsame).2.1 heq⟩
        set L := ((freeParams S).filter (fun x => decide (x ≠ pr.snd))).take d
        obtain ⟨hLp, hLne⟩ := filter_ne_take_props hS hsndF ha
        have hL_not_pr : ∀ x ∈ L, x ≠ p ∧ x ≠ pr.partner p := fun x hx => by
          have hxf : x ≠ pr.fst := (fst_ne_of_mem_freeParams hS (hLp.2.1 x hx) hprm).symm
          have hxs : x ≠ pr.snd := hLne x hx
          exact ⟨hprp.elim (· ▸ hxf) (· ▸ hxs),
            (pr.contains_partner hprp).elim (· ▸ hxf) (· ▸ hxs)⟩
        have hr_ne_p : pr.partner p ≠ p := pr.partner_ne hpr_ne hprp
        refine findSome_isSome_of_family C f hf hS
          (fun A y => if y = p then (fixArg (S.gate G) p).1
            else if y = pr.partner p then pr.partnerBias p
            else terminalVal S L A y)
          ?_ (fun x hx => (mem_freeParams.1 (hLp.2.1 x hx)).1) hLp.2.2 ?_ ?_
          ((fixArg (S.gate G) p).2 ^^ S.out.neg) ?_
        · intro x
          by_cases hxp : x = p
          · simpa [hxp] using isAffine_const Bool.xor_self _
          · by_cases hxr : x = pr.partner p
            · simpa [hxr, hr_ne_p] using isAffine_const Bool.xor_self _
            · simpa [hxp, hxr] using isAffine_terminalVal S L x
        · intro A j hj
          obtain ⟨h1, h2⟩ := hL_not_pr _ (List.getElem_mem hj)
          rw [ite_eq_right h1, ite_eq_right h2]
          exact terminalVal_coord hLp.1 hLp.2.1 A j hj
        · intro A pr' hpr'
          by_cases hsame : pr' = pr
          · subst hsame
            exact ZeroPair.holds_of_eq_partnerBias hprp (by simp [hr_ne_p])
          · have hdisj := hS.pairs_disjoint pr' hpr' pr hprm hsame
            have h1 : pr'.fst ≠ p := hprp.elim (· ▸ hdisj.1) (· ▸ hdisj.2.1)
            have h2 : pr'.fst ≠ pr.partner p :=
              (pr.contains_partner hprp).elim (· ▸ hdisj.1) (· ▸ hdisj.2.1)
            refine ZeroPair.holds_of_eq_bias (x := pr'.fst) (Or.inl rfl) ?_
            rw [ite_eq_right h1, ite_eq_right h2, terminalVal_fst hS L A hpr']
            simp [ZeroPair.bias]
        · intro A val hcons hval
          have hvalG := hcons.2 G hG
          have hvp : val p = (fixArg (S.gate G) p).1 := by rw [hval p hppar, ite_eq_left rfl]
          have hGe : (S.gate G).eval val = (fixArg (S.gate G) p).2 :=
            fixArg_spec hna hpw.symm (Gate.args_of_reads hpw.symm hGw hGp) val hvp
          simp only [Lit.eval, hu, huG, Arg.eval, hvalG, hGe]
      · rename_i hAOP_not
        have hAOP : findAndOnPair S = none :=
          Option.eq_none_iff_forall_ne_some.2 fun x hx => hAOP_not x.1 x.2 hx
        split
        · rename_i hne
          obtain ⟨t₁, t₂, hl, hr, ht₁p, ht₁u, hnaff, huG⟩ :=
            terminal_gate_shape hS hterm hu hup hAOP hne
          have ht₁F : t₁ ∈ freeParams S := mem_freeParams.2 ⟨ht₁p, by
            rw [← Bool.not_eq_true, isFstOfAnyPair_eq_true_iff hS]
            rintro ⟨pr, hpr, rfl⟩
            exact ht₁u ⟨pr, hpr, Or.inl rfl⟩⟩
          simp only [hl]
          set op := (S.gate (S.gates.min' hne)).op with hop
          refine findSome_isSome_pin C f hf hS ht₁F ha
            (fun _ => decide ((op true false == op true true) = true))
            (Cslib.BitString.isAffine_const (fun b => Bool.xor_self b) _)
            (op (decide ((op true false == op true true) = true)) false ^^ S.out.neg)
            fun A val hcons hval => ?_
          have h1 : val t₁ = decide ((op true false == op true true) = true) := by
            rw [hval _ ht₁p, ite_eq_left rfl]
          simp only [Lit.eval, hu, Arg.eval, huG, hcons.2 _ (Finset.min'_mem _ hne), Gate.eval,
            hl, hr, h1, ← hop]
          congr 1
          cases val t₂ <;> [rfl; exact (op_const_of_not_isAffineOp op hnaff).symm]
        · rename_i hne
          exact (hne (Finset.card_pos.1 (Nat.pos_of_ne_zero fun h => by simp [h] at hcase))).elim

private theorem findSome_neq {d : ℕ} (C : Circuit (fullSignature 2 Bool) n 1)
    (f : BitString n → Bool)
    {g : List Bool → BitString n} {x : BitString n}
    (h : (allAssignments d).findSome? (fun A =>
      if C.eval fullInterpretation (g A) 0 != f (g A) then some (g A) else none) = some x) :
    C.eval fullInterpretation x 0 ≠ f x := by
  obtain ⟨A, -, hA⟩ := List.exists_of_findSome?_eq_some h
  split_ifs at hA with hne
  simpa [← Option.some_inj.mp hA] using hne

/-- Every input returned by `findCounterexample` is a counterexample. -/
theorem findCounterexample_spec {d : ℕ} (C : Circuit (fullSignature 2 Bool) n 1)
    (f : BitString n → Bool) (S : State n) {x : BitString n}
    (h : findCounterexample C f d S = some x) : C.eval fullInterpretation x 0 ≠ f x := by
  unfold findCounterexample at h
  repeat' (first | (dsimp only at h; split at h) | split at h)
  all_goals first | exact findSome_neq C f h | cases h

end Cslib.Circuits.Boolean.AffineDisperser4n
