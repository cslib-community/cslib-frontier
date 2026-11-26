/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackTrick
-- `import all`: the acceptance proof unfolds `stepTop`, `runTop`, the reification steps and the
-- emitter's definitions.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Reification
import all CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackDP
import all CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackTrick
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.GetD

/-!
# The two-equality knapsack propagator: acceptance and exactness

The checker accepts the proof of the two-equality knapsack propagator
(`CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackTrick`) on every instance, and the
propagator removes exactly the unsupported values: those of the items, of the weight and of the
profit. Both are proved, not checked when the proof runs.

**Acceptance** (`Cslib.Logic.PL.VeriPB.Knapsack.Trick.Inst.checkRed_propagate`). Each step is
shown to run from an invariant on the proof so far
(`Inst.Run`): the database keeps the formula, its numbers
and variables are below the next ones, and the extension variables are above the direct
literals. Each `rup` step is accepted by the completeness of unit propagation on constraints over
distinct variables (`CslibFrontier.Logics.Propositional.PseudoBoolean.RupComplete`), from the
meaning of the constraints its hints name; the sums of the partial states are over the direct
literals in their numbering, so the slack lemmas of the shared emitter
(`CslibFrontier.Logics.Propositional.PseudoBoolean.KnapsackDP`) apply to them:
* a transition (`Inst.trSteps_spec`) adds the forward half
  of each of the four partial states of a node to the backward half of that of its successor;
  under the item's at-most-one constraint, which makes the other values of the item false, the
  sum puts the successor in the partial state
  (`Inst.dim_trans`, from
  `trans_gen`, the transition lemma over a block of
  variables);
* a clause `S_t ⇒ [W ≠ u]` (`Inst.sSteps_spec`) adds the
  `↓` partial state of `t` to the inequality `∑ wⱼ v [xⱼ = v] ≥ ∑ u [W = u]` when `u` is above
  the weight of `t`, which bounds `W` from above, and the `↑` partial state to the converse
  inequality otherwise (`Inst.link_down`,
  `Inst.link_up`).

**Exactness** (`Cslib.Logic.PL.VeriPB.Knapsack.Trick.Inst.mem_removed_iff`,
`Cslib.Logic.PL.VeriPB.Knapsack.Trick.Inst.mem_removedW_iff`,
`Cslib.Logic.PL.VeriPB.Knapsack.Trick.Inst.mem_removedP_iff`). A value is *supported* when some
choice of values of the current domains of the items, with that value, has its weight and its
profit in theirs (`Cslib.Logic.PL.VeriPB.Knapsack.Trick.Inst.SupportedN`,
`Cslib.Logic.PL.VeriPB.Knapsack.Trick.Inst.SupportedS`). A removed value is unsupported because
the checker's soundness makes its derived clause `D ⇒ [x ≠ v]` hold at every solution of the
formula (`Inst.holds_of_run`), and a supported value gives
one, the direct literals of a choice (`Inst.asg`), agreeing
with the antecedent. An unsupported value is removed because the layers are exactly the states
reachable under the current domains (`Inst.mem_lay_iff`)
and the backward pass keeps exactly the states with a feasible completion
(`Inst.mem_alive_iff`). So the remaining values of `W` and
`P` are exactly the weights and profits of the feasible states of the last layer, and their
bounds, the least and greatest of them, are exact too.

## Main definitions

* `Cslib.Logic.PL.VeriPB.Knapsack.Trick.Inst.SupportedN`,
  `Cslib.Logic.PL.VeriPB.Knapsack.Trick.Inst.SupportedS`: supported values.

## Main results

* `Cslib.Logic.PL.VeriPB.Knapsack.Trick.Inst.checkRed_propagate`: the checker accepts every proof
  of the propagator.
* `Cslib.Logic.PL.VeriPB.Knapsack.Trick.Inst.mem_removed_iff`,
  `Cslib.Logic.PL.VeriPB.Knapsack.Trick.Inst.mem_removedW_iff`,
  `Cslib.Logic.PL.VeriPB.Knapsack.Trick.Inst.mem_removedP_iff`: the propagator removes exactly the
  unsupported values of the current domains.

## References

* [E. Demirović, C. McCreesh, M. J. McIlree, J. Nordström, A. Oertel, K. Sidorov, *Pseudo-Boolean
  Reasoning About States and Transitions to Certify Dynamic Programming and Decision Diagram
  Algorithms*][DemirovicMcCreeshMcIlreeNordstromOertelSidorov2024]
* [S. Gocht, C. McCreesh, J. Nordström, *An Auditable Constraint Programming
  Solver*][GochtMcCreeshNordstrom2022]
-/


namespace Cslib.Logic.PL.VeriPB.Knapsack.Trick

open PBConstr
open Knapsack.Inst (part part_succ part_add_part part_const lhs_sumTerms vars_sumTerms
  nodup_sumTerms holds_dimC holds_clause holds_negate_clause consistent_append lhs_map_negate
  nodup_impl_single slack_fwd slack_bwd runTop_append push_steps mem_of_lookup sub_cons vars_impl
  push_push rup_clause lit_of vars_add polEval_add vars_clause bit Sub Sub.refl Sub.trans)

/-! ### Sums over lists of positions -/

private theorem sum_range_single {m k : ℕ} (f : ℕ → ℕ) (hk : k < m)
    (h0 : ∀ j < m, j ≠ k → f j = 0) : ((List.range m).map f).sum = f k := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    by_cases hkm : k = m
    · subst hkm
      have : ((List.range k).map f).sum = 0 :=
        List.sum_eq_zero fun x hx => by
          obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
          exact h0 j (by simp at hj; omega) (by simp at hj; omega)
      simp [this]
    · rw [ih (by omega) (fun j hj hne => h0 j (by omega) hne)]
      simp [h0 m (by omega) (Ne.symm hkm)]

private theorem sum_range_add (m : ℕ) (f g : ℕ → ℕ) :
    ((List.range m).map fun j => f j + g j).sum =
      ((List.range m).map f).sum + ((List.range m).map g).sum := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [List.range_succ, List.map_append, List.sum_append, ih]; simp; omega

private theorem sum_range_le_card {m : ℕ} (f : ℕ → ℕ) (h1 : ∀ j < m, f j ≤ 1) :
    ((List.range m).map f).sum ≤ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    have := ih fun j hj => h1 j (by omega)
    have := h1 m (by omega)
    omega

/-- A zero among values at most `1` leaves the sum at most `m - 1`. -/
private theorem sum_range_one_zero {m j : ℕ} (f : ℕ → ℕ) (h1 : ∀ i < m, f i ≤ 1) (hj : j < m)
    (hfj : f j = 0) : ((List.range m).map f).sum + 1 ≤ m := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil]
    by_cases hjm : j = m
    · have := sum_range_le_card (m := m) f fun i hi => h1 i (by omega)
      have : f m = 0 := hjm ▸ hfj
      omega
    · have := ih (fun i hi => h1 i (by omega)) (by omega)
      have := h1 m (by omega)
      omega

/-- Two zeros among values at most `1` leave the sum at most `m - 2`. -/
private theorem sum_range_two_zero {m k k' : ℕ} (f : ℕ → ℕ) (h1 : ∀ j < m, f j ≤ 1)
    (hk : k < m) (hk' : k' < m) (hne : k ≠ k') (hfk : f k = 0) (hfk' : f k' = 0) :
    ((List.range m).map f).sum + 2 ≤ m := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    by_cases hm : k = m ∨ k' = m
    · have hz : f m = 0 := by rcases hm with rfl | rfl <;> assumption
      obtain ⟨j, hj, hfj⟩ : ∃ j < m, f j = 0 := by
        rcases hm with rfl | rfl
        · exact ⟨k', by omega, hfk'⟩
        · exact ⟨k, by omega, hfk⟩
      have := sum_range_one_zero f (fun i hi => h1 i (by omega)) hj hfj
      omega
    · push Not at hm
      have := ih (fun j hj => h1 j (by omega)) (by omega) (by omega)
      have := h1 m (by omega)
      omega

private theorem lhs_filterMap_range (σ : ℕ → Bool) (m : ℕ) (c lit : ℕ → ℕ) (pol : Bool) :
    lhs σ ((List.range m).filterMap fun k => if c k = 0 then none else some (c k, (lit k, pol))) =
      ((List.range m).map fun k => bit (σ (lit k)) pol (c k)).sum := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
      lhs_append, List.map_append, List.sum_append, ih]
    split_ifs with h
    · simp [bit, h]
    · simp only [lhs_cons, lhs_nil, termVal, Literal.eval_mk, bit, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil]
      cases σ (lit m) <;> cases pol <;> simp

private theorem vars_filterMap_range {m : ℕ} {c lit : ℕ → ℕ} {pol : Bool} {x : ℕ}
    (h : x ∈ ((List.range m).filterMap fun k =>
      if c k = 0 then none else some (c k, (lit k, pol))).map termVar) :
    ∃ k < m, lit k = x := by
  simp only [List.mem_map, List.mem_filterMap, List.mem_range] at h
  obtain ⟨t, ⟨k, hk, ht⟩, rfl⟩ := h
  split_ifs at ht
  cases ht
  exact ⟨k, hk, rfl⟩

private theorem nodup_filterMap_range (m : ℕ) (c lit : ℕ → ℕ) (pol : Bool)
    (hlit : ∀ k < m, ∀ k' < m, lit k = lit k' → k = k') :
    (((List.range m).filterMap fun k =>
      if c k = 0 then none else some (c k, (lit k, pol))).map termVar).Nodup := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : ((List.range (m + 1)).filterMap fun k =>
        if c k = 0 then none else some (c k, (lit k, pol))) =
        ((List.range m).filterMap fun k => if c k = 0 then none else some (c k, (lit k, pol))) ++
          (if c m = 0 then [] else [(c m, (lit m, pol))]) := by
      simp only [List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
      split_ifs <;> rfl
    rw [e, List.map_append, List.nodup_append]
    refine ⟨ih fun k hk k' hk' h => hlit k (by omega) k' (by omega) h, by split_ifs <;> simp, ?_⟩
    intro x hx y hy
    split_ifs at hy
    · simp at hy
    · simp only [List.map_cons, List.map_nil, List.mem_singleton, termVar_mk] at hy
      obtain ⟨k, hk, rfl⟩ := vars_filterMap_range hx
      intro hxy
      have := hlit k (by omega) m (by omega) (by rw [hxy, hy])
      omega

/-! ### The variables of the items -/

namespace Inst

variable (I : Inst)

theorem off_succ (j : ℕ) : I.off (j + 1) = I.off j + I.len j := by
  simp [off, List.range_succ]

theorem off_mono {i j : ℕ} (h : i ≤ j) : I.off i ≤ I.off j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [off_succ]; omega

/-- The coefficients of the items `j < i`. -/
private def coefsN (a : ℕ → ℕ → ℕ) (i : ℕ) : List ℕ :=
  (List.range i).flatMap fun j => (List.range (I.len j)).map (a j)

private theorem length_coefsN (a : ℕ → ℕ → ℕ) (i : ℕ) : (I.coefsN a i).length = I.off i := by
  induction i with
  | zero => rfl
  | succ i ih => simp [coefsN, List.range_succ, off_succ] at ih ⊢; omega

private theorem getD_coefsN (a : ℕ → ℕ → ℕ) {i j k : ℕ} (hj : j < i) (hk : k < I.len j) :
    (I.coefsN a i).getD (I.var j k) 0 = a j k := by
  induction i with
  | zero => omega
  | succ i ih =>
    have e : I.coefsN a (i + 1) = I.coefsN a i ++ (List.range (I.len i)).map (a i) := by
      simp [coefsN, List.range_succ]
    rw [e]
    by_cases hji : j < i
    · have hlt : I.var j k < (I.coefsN a i).length := by
        rw [length_coefsN, var]
        have := I.off_mono (show j + 1 ≤ i by omega)
        rw [off_succ] at this
        omega
      rw [List.getD_append _ _ _ _ hlt, ih hji]
    · have hji : j = i := by omega
      subst hji
      rw [List.getD_append_right _ _ _ _ (by rw [length_coefsN, var]; omega)]
      simp [length_coefsN, var, List.getD_eq_getElem?_getD, hk]

theorem flat_var (a : ℕ → ℕ → ℕ) {j k : ℕ} (hj : j < I.n) (hk : k < I.len j) :
    I.flat a (I.var j k) = a j k :=
  I.getD_coefsN a hj hk

/-- The variables of the items `j < i` are below `off i`. -/
theorem var_lt {i j k : ℕ} (hj : j < i) (hk : k < I.len j) : I.var j k < I.off i := by
  have := I.off_mono (show j + 1 ≤ i by omega)
  rw [off_succ] at this
  simp only [var]; omega

theorem var_inj {j k j' k' : ℕ} (hk : k < I.len j) (hk' : k' < I.len j')
    (h : I.var j k = I.var j' k') : j = j' ∧ k = k' := by
  rcases lt_trichotomy j j' with hlt | rfl | hlt
  · have := I.var_lt hlt hk; simp only [var] at this h; omega
  · simp only [var] at h; exact ⟨rfl, by omega⟩
  · have := I.var_lt hlt hk'; simp only [var] at this h; omega

theorem off_le_wBase {i : ℕ} (hi : i ≤ I.n) : I.off i ≤ I.wBase := I.off_mono hi

theorem wBase_le_M : I.wBase ≤ I.M := by simp only [M, pBase]; omega

/-- The sum over the positions of item `i`. -/
def rowPart (σ : ℕ → Bool) (a : ℕ → ℕ → ℕ) (pol : Bool) (i : ℕ) : ℕ :=
  ((List.range (I.len i)).map fun k => bit (σ (I.var i k)) pol (a i k)).sum

/-- The total over the positions of item `i`. -/
def rowTot (a : ℕ → ℕ → ℕ) (i : ℕ) : ℕ := ((List.range (I.len i)).map (a i)).sum

private theorem part_add_len (σ : ℕ → Bool) (A : ℕ → ℕ) (pol : Bool) (m l : ℕ) :
    part σ A pol (m + l) = part σ A pol m + ((List.range l).map fun t => bit (σ (m + t)) pol
      (A (m + t))).sum := by
  induction l with
  | zero => simp
  | succ l ih => rw [← Nat.add_assoc, part_succ, ih, List.range_succ]; simp; omega

private theorem tot_add_len (A : ℕ → ℕ) (m l : ℕ) :
    Knapsack.Inst.tot A (m + l) =
      Knapsack.Inst.tot A m + ((List.range l).map fun t => A (m + t)).sum := by
  induction l with
  | zero => simp
  | succ l ih => rw [← Nat.add_assoc, Knapsack.Inst.tot_succ, ih, List.range_succ]; simp; omega

theorem part_off_succ (σ : ℕ → Bool) (a : ℕ → ℕ → ℕ) (pol : Bool) {i : ℕ} (hi : i < I.n) :
    part σ (I.flat a) pol (I.off (i + 1)) =
      part σ (I.flat a) pol (I.off i) + I.rowPart σ a pol i := by
  rw [off_succ, part_add_len, rowPart]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  rw [show I.off i + t = I.var i t from rfl, I.flat_var a hi (by simpa using ht)]

theorem tot_succ (a : ℕ → ℕ → ℕ) {i : ℕ} (hi : i < I.n) :
    I.tot a (i + 1) = I.tot a i + I.rowTot a i := by
  rw [tot, tot, off_succ, tot_add_len, rowTot]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  rw [show I.off i + t = I.var i t from rfl, I.flat_var a hi (by simpa using ht)]

theorem rowPart_add (σ : ℕ → Bool) (a : ℕ → ℕ → ℕ) (pol : Bool) (i : ℕ) :
    I.rowPart σ a pol i + I.rowPart σ a (!pol) i = I.rowTot a i := by
  rw [rowPart, rowPart, ← sum_range_add, rowTot]
  refine congrArg List.sum (List.map_congr_left fun k _ => ?_)
  cases σ (I.var i k) <;> cases pol <;> simp [bit]

/-- **The assignment picks the position `k` of item `i`**: its direct literal is true and the
others of the item false. -/
def Picks (σ : ℕ → Bool) (i k : ℕ) : Prop :=
  k < I.len i ∧ σ (I.var i k) = true ∧ ∀ k' < I.len i, k' ≠ k → σ (I.var i k') = false

theorem rowPart_true {σ : ℕ → Bool} {i k : ℕ} (h : I.Picks σ i k) (a : ℕ → ℕ → ℕ) :
    I.rowPart σ a true i = a i k := by
  rw [rowPart, sum_range_single _ h.1 fun j hj hne => by simp [bit, h.2.2 j hj hne]]
  simp [bit, h.2.1]

theorem rowPart_false {σ : ℕ → Bool} {i k : ℕ} (h : I.Picks σ i k) (a : ℕ → ℕ → ℕ) :
    I.rowPart σ a false i + a i k = I.rowTot a i := by
  have := I.rowPart_add σ a false i
  rw [Bool.not_false, I.rowPart_true h] at this
  omega

theorem lhs_terms (σ : ℕ → Bool) (a : ℕ → ℕ → ℕ) (pol : Bool) (i : ℕ) :
    lhs σ (I.terms a pol i) = part σ (I.flat a) pol (I.off i) := lhs_sumTerms σ _ pol _

theorem vars_terms {a : ℕ → ℕ → ℕ} {pol : Bool} {i x : ℕ}
    (h : x ∈ (I.terms a pol i).map termVar) : x < I.off i := vars_sumTerms h

theorem nodup_terms (a : ℕ → ℕ → ℕ) (pol : Bool) (i : ℕ) :
    ((I.terms a pol i).map termVar).Nodup := nodup_sumTerms _ pol _

theorem holds_dimC' (σ : ℕ → Bool) (a : ℕ → ℕ → ℕ) (pol : Bool) (i d : ℕ) :
    (I.dimC a pol i d).Holds σ ↔ d ≤ part σ (I.flat a) pol (I.off i) := holds_dimC σ _ pol _ d

theorem vars_dimC {a : ℕ → ℕ → ℕ} {pol : Bool} {i d x : ℕ} (h : x ∈ (I.dimC a pol i d).vars) :
    x < I.off i := vars_sumTerms h

/-! ### The domains of the sums -/

theorem lhs_sTerms (σ : ℕ → Bool) (D : Dom) (base : ℕ) (pol : Bool) :
    lhs σ (sTerms D base pol) =
      ((List.range D.length).map fun k => bit (σ (base + k)) pol (dval D k)).sum :=
  lhs_filterMap_range σ _ (dval D) (base + ·) pol

theorem vars_sTerms {D : Dom} {base : ℕ} {pol : Bool} {x : ℕ}
    (h : x ∈ (sTerms D base pol).map termVar) : base ≤ x ∧ x < base + D.length := by
  obtain ⟨k, hk, rfl⟩ := vars_filterMap_range h
  omega

theorem nodup_sTerms (D : Dom) (base : ℕ) (pol : Bool) :
    ((sTerms D base pol).map termVar).Nodup :=
  nodup_filterMap_range _ _ _ pol fun k _ k' _ h => by simpa using h

/-- The sum of a domain at an assignment of its direct literals. -/
def sPart (σ : ℕ → Bool) (D : Dom) (base : ℕ) (pol : Bool) : ℕ :=
  ((List.range D.length).map fun k => bit (σ (base + k)) pol (dval D k)).sum

theorem sPart_add (σ : ℕ → Bool) (D : Dom) (base : ℕ) (pol : Bool) :
    sPart σ D base pol + sPart σ D base (!pol) = sTot D := by
  rw [sPart, sPart, ← sum_range_add, sTot]
  refine congrArg List.sum (List.map_congr_left fun k _ => ?_)
  cases σ (base + k) <;> cases pol <;> simp [bit]

/-- The assignment picks the position `k` of a domain. -/
def PicksD (σ : ℕ → Bool) (D : Dom) (base k : ℕ) : Prop :=
  k < D.length ∧ σ (base + k) = true ∧ ∀ k' < D.length, k' ≠ k → σ (base + k') = false

theorem sPart_true {σ : ℕ → Bool} {D : Dom} {base k : ℕ} (h : PicksD σ D base k) :
    sPart σ D base true = dval D k := by
  rw [sPart, sum_range_single _ h.1 fun j hj hne => by simp [bit, h.2.2 j hj hne]]
  simp [bit, h.2.1]

theorem holds_alo (σ : ℕ → Bool) (base m : ℕ) :
    (alo base m).Holds σ ↔ ∃ k < m, σ (base + k) = true := by
  simp only [alo, Holds, lhs, List.map_map]
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Function.comp_apply, termVal, Literal.eval_mk]
    constructor
    · intro h
      by_cases hm : σ (base + m) = true
      · exact ⟨m, by omega, hm⟩
      · obtain ⟨k, hk, hσ⟩ := ih.1 (by simp [hm] at h; omega)
        exact ⟨k, by omega, hσ⟩
    · rintro ⟨k, hk, hσ⟩
      by_cases hkm : k = m
      · subst hkm; simp [hσ]
      · have := ih.2 ⟨k, by omega, hσ⟩; omega

private theorem lhs_amo (σ : ℕ → Bool) (base m : ℕ) :
    lhs σ (amo base m).terms = ((List.range m).map fun k => (!σ (base + k)).toNat).sum := by
  simp only [amo, lhs, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun k _ => ?_)
  simp [termVal]

theorem eq_false_of_amo {σ : ℕ → Bool} {base m k : ℕ} (h : (amo base m).Holds σ) (hk : k < m)
    (hσ : σ (base + k) = true) {k' : ℕ} (hk' : k' < m) (hne : k' ≠ k) :
    σ (base + k') = false := by
  by_contra hc
  simp only [Bool.not_eq_false] at hc
  have := sum_range_two_zero (fun j => (!σ (base + j)).toNat)
    (fun j _ => by cases σ (base + j) <;> simp) hk hk' (Ne.symm hne) (by simp [hσ]) (by simp [hc])
  simp only [Holds] at h
  rw [lhs_amo] at h
  simp only [amo] at h
  omega

theorem holds_amo_of {σ : ℕ → Bool} {base m k : ℕ}
    (h : ∀ k' < m, k' ≠ k → σ (base + k') = false) : (amo base m).Holds σ := by
  simp only [Holds]
  rw [lhs_amo]
  simp only [amo]
  suffices ∀ m', m' ≤ m → (m' ≤ k → ((List.range m').map fun j => (!σ (base + j)).toNat).sum = m') ∧
      m' ≤ ((List.range m').map fun j => (!σ (base + j)).toNat).sum + 1 by
    have := (this m le_rfl).2; omega
  intro m' hm'
  induction m' with
  | zero => simp
  | succ m' ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (by omega)
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    rcases lt_trichotomy m' k with hlt | rfl | hgt
    · simp [h m' (by omega) (by omega), ih₁ (by omega)]
    · constructor
      · intro; omega
      · have := ih₁ le_rfl; omega
    · simp [h m' (by omega) (by omega)]; omega

theorem holds_cS (σ : ℕ → Bool) (v : ℕ) :
    (cS v).Holds σ ↔ σ v = true ∧ σ (v + 1) = true ∧ σ (v + 2) = true ∧ σ (v + 3) = true := by
  simp only [cS, Holds, lhs, List.range_succ, List.range_zero, List.nil_append,
    List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
    termVal, Literal.eval_mk, Nat.add_zero]
  cases σ v <;> cases σ (v + 1) <;> cases σ (v + 2) <;> cases σ (v + 3) <;> simp

/-! ### Running the proof -/

/-- The checker state with the database `db` and the next number `m`, all else as at the start. -/
def state (db : List (ℕ × PBConstr)) (m : ℕ) : State :=
  { State.init I.formula none (some I.pres) with db := db, next := m }

/-- **The proof so far runs** from the formula to the database `db`: the numbers of `db` are
below the next one, its variables below the next free one, which is not a direct literal, and
`db` keeps the formula. -/
def Run (e : ProofLog) (db : List (ℕ × PBConstr)) : Prop :=
  runTop I.formula none (State.init I.formula none (some I.pres)) e.steps.reverse =
      some (I.state db e.next) ∧
    (∀ x ∈ db, x.1 < e.next) ∧ (∀ x ∈ db, ∀ v ∈ x.2.vars, v < e.var) ∧ I.M ≤ e.var ∧
    Sub (initDb I.formula) db

theorem Run.sub {e : ProofLog} {db : List (ℕ × PBConstr)} (h : I.Run e db) :
    Sub (initDb I.formula) db := h.2.2.2.2

/-- **A step that is not a deletion runs** when it adds the constraint `c` at the next number,
by the Boolean emitter's `runTop_push_step`. -/
theorem Run.step {e : ProofLog} {db : List (ℕ × PBConstr)} (h : I.Run e db) {st : Step}
    (hst : ∀ ids, st ≠ .del ids) {c : PBConstr}
    (hr : runStep db e.next st = some ((e.next, c) :: db, e.next + 1))
    (hv : ∀ v ∈ c.vars, v < e.var) :
    I.Run (e.push [.step st] 1 0) ((e.next, c) :: db) ∧ Sub db ((e.next, c) :: db) := by
  have hs := sub_cons h.2.1 c
  obtain ⟨h1, h2, h3⟩ := Knapsack.Inst.runTop_push_step h.1 h.2.1 h.2.2.1 hst hr hv
  exact ⟨⟨h1, h2, h3, by simpa [ProofLog.push] using h.2.2.2.1, h.sub.trans hs⟩, hs⟩

/-- **A `pol` step runs.** -/
theorem Run.pol {e : ProofLog} {db : List (ℕ × PBConstr)} (h : I.Run e db) {ops : List PolOp}
    {c : PBConstr} (hp : polEval db ops [] = some [c]) (hv : ∀ v ∈ c.vars, v < e.var) :
    I.Run (e.push [.step (.pol ops)] 1 0) ((e.next, c) :: db) ∧ Sub db ((e.next, c) :: db) :=
  Run.step I h (by intro ids h; cases h) (by simp [runStep, hp]) hv

/-- **A `rup` step runs** when the checker accepts it. -/
theorem Run.rup {e : ProofLog} {db : List (ℕ × PBConstr)} (h : I.Run e db) {c : PBConstr}
    {hs : List Hint} (hr : rup db c hs = true) (hv : ∀ v ∈ c.vars, v < e.var) :
    I.Run (e.push [.step (.rup c hs)] 1 0) ((e.next, c.normalize) :: db) ∧
      Sub db ((e.next, c.normalize) :: db) :=
  Run.step I h (by intro ids h; cases h) (by simp [runStep, hr])
    fun v hv' => hv _ (mem_vars_of_mem_vars_normalize hv')

/-- The variables of the formula are direct literals. -/
theorem vars_formula : ∀ c ∈ I.formula, ∀ v ∈ c.vars, v < I.M := by
  intro c hc v hv
  have hW := I.wBase_le_M
  have hn := I.off_le_wBase (le_refl I.n)
  simp only [formula, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨j, hj, rfl | rfl⟩
  · simp only [linkW₁, PBConstr.vars, List.map_append, List.mem_append] at hv
    rcases hv with hv | hv
    · have := I.vars_terms hv; omega
    · have := vars_sTerms hv; simp only [M, pBase] at this ⊢; omega
  · simp only [linkW₂, PBConstr.vars, List.map_append, List.mem_append] at hv
    rcases hv with hv | hv
    · have := I.vars_terms hv; omega
    · have := vars_sTerms hv; simp only [M, pBase] at this ⊢; omega
  · simp only [linkP₁, PBConstr.vars, List.map_append, List.mem_append] at hv
    rcases hv with hv | hv
    · have := I.vars_terms hv; omega
    · have := vars_sTerms hv; simp only [M] at this ⊢; omega
  · simp only [linkP₂, PBConstr.vars, List.map_append, List.mem_append] at hv
    rcases hv with hv | hv
    · have := I.vars_terms hv; omega
    · have := vars_sTerms hv; simp only [M] at this ⊢; omega
  all_goals first
    | (simp only [alo, amo, PBConstr.vars, List.map_map, List.mem_map, List.mem_range,
        Function.comp_apply, termVar_mk] at hv
       obtain ⟨k, hk, rfl⟩ := hv
       simp only [M, pBase] at *
       omega)
    | (simp only [alo, amo, PBConstr.vars, List.map_map, List.mem_map, List.mem_range,
        Function.comp_apply, termVar_mk] at hv
       obtain ⟨k, hk, rfl⟩ := hv
       have := I.var_lt (i := I.n) hj hk
       simp only [var] at this
       omega)

theorem vars_initDb : ∀ x ∈ initDb I.formula, ∀ v ∈ x.2.vars, v < I.M := by
  intro x hx v hv
  simp only [initDb, List.mem_map] at hx
  obtain ⟨⟨c, i⟩, hci, rfl⟩ := hx
  exact I.vars_formula c (List.fst_mem_of_mem_zipIdx hci) v (mem_vars_of_mem_vars_normalize hv)

theorem length_formula : I.formula.length = 8 + 2 * I.n := by
  simp only [formula, List.length_append, List.length_cons, List.length_nil, List.length_flatMap,
    List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  omega

private theorem find_zipIdx (L : List PBConstr) : ∀ (k m : ℕ), k ≤ m →
    (((L.zipIdx k).map fun e => (e.2 + 1, e.1.normalize)).find? (·.1 == m + 1)).map (·.2) =
      (L[m - k]?).map normalize := by
  induction L with
  | nil => simp
  | cons a L ih =>
    intro k m hkm
    rw [List.zipIdx_cons, List.map_cons, List.find?_cons]
    by_cases hk : k = m
    · subst hk; simp
    · have : (k + 1 == m + 1) = false := by simp; omega
      simp only [this]
      rw [ih (k + 1) m (by omega), show m - k = (m - (k + 1)) + 1 by omega]
      simp

theorem lookup_initDb (L : List PBConstr) (m : ℕ) :
    lookup (initDb L) (m + 1) = (L[m]?).map normalize := by
  simpa [lookup, initDb] using find_zipIdx L 0 m (Nat.zero_le m)

/-- The proof starts at the formula. -/
theorem run_init : I.Run ⟨[], I.start, I.M⟩ (initDb I.formula) := by
  refine ⟨?_, ?_, fun x hx v hv => I.vars_initDb x hx v hv, le_rfl, Sub.refl _⟩
  · simp only [List.reverse_nil, runTop_nil, state]
    congr 1
    simp only [State.init, start, length_formula]
    congr 1
    omega
  · intro x hx
    simp only [initDb, List.mem_map] at hx
    obtain ⟨⟨c, i⟩, hci, rfl⟩ := hx
    have := (List.mem_zipIdx_iff_getElem?.1 hci)
    have hi : i < I.formula.length := by
      by_contra hc; simp [List.getElem?_eq_none (by omega : I.formula.length ≤ i)] at this
    rw [length_formula] at hi
    simp only [start]; omega

/-- **A reification by the next free variable runs**, for a satisfiable constraint over older
variables, by the Boolean emitter's `runTop_push_reify`. -/
theorem Run.reify {e : ProofLog} {db : List (ℕ × PBConstr)} (h : I.Run e db) {c : PBConstr}
    (hv : ∀ v ∈ c.vars, v < e.var) (hsat : ∃ σ, c.Holds σ) :
    I.Run (e.push (reify e.var c) 4 1)
        ((e.next + 3, (impl [(e.var, false)] c.negate).normalize) ::
          (e.next + 1, (impl [(e.var, true)] c).normalize) :: db) ∧
      Sub db ((e.next + 3, (impl [(e.var, false)] c.negate).normalize) ::
          (e.next + 1, (impl [(e.var, true)] c).normalize) :: db) := by
  obtain ⟨hrun, hid, hvar, hn, h0⟩ := h
  have hsub := Knapsack.Inst.sub_reify hid c
  have hfresh : (I.state db e.next).fresh e.var = true := by
    simp only [State.fresh, Bool.and_eq_true, List.all_eq_true, List.mem_append]
    refine ⟨fun x hx => ?_, ?_⟩
    · have : e.var ∉ x.2.vars := fun hm => by
        rcases hx with hx | hx
        · have := hvar x hx _ hm; omega
        · simp only [state, State.init] at hx
          have := I.vars_initDb x hx _ hm; omega
      simpa using this
    · simp [State.avoidsVar, state, State.init, pres]
      omega
  obtain ⟨r1, r2, r3⟩ := Knapsack.Inst.runTop_push_reify rfl hrun hid hvar hv hsat hfresh
  exact ⟨⟨r1, r2, r3, by simp [ProofLog.push]; omega, h0.trans hsub⟩, hsub⟩

theorem vars_of_lookup {e : ProofLog} {db : List (ℕ × PBConstr)} (h : I.Run e db) {k : ℕ}
    {c : PBConstr} (hk : lookup db k = some c) : ∀ v ∈ c.vars, v < e.var :=
  fun v hv => h.2.2.1 _ (mem_of_lookup hk) v hv

/-- A `pol` step adding two constraints of the database runs. -/
theorem Run.add {e : ProofLog} {db : List (ℕ × PBConstr)} (h : I.Run e db) {a b : ℕ}
    {c d : PBConstr} (ha : lookup db a = some c) (hb : lookup db b = some d) :
    I.Run (e.push [.step (.pol [.id a, .id b, .add])] 1 0) ((e.next, c.add d) :: db) ∧
      Sub db ((e.next, c.add d) :: db) :=
  Run.pol I h (polEval_add ha hb) fun v hv => (vars_add hv).elim
    (I.vars_of_lookup h ha v) (I.vars_of_lookup h hb v)

/-- The formula's constraint number `m + 1` is in the database. -/
theorem lookup_formula {e : ProofLog} {db : List (ℕ × PBConstr)} (h : I.Run e db) {m : ℕ}
    {c : PBConstr} (hm : I.formula[m]? = some c) : lookup db (m + 1) = some c.normalize :=
  by
  have := lookup_initDb I.formula m
  rw [hm, Option.map_some] at this
  exact Run.sub I h _ _ this

private theorem getElem?_flatMap_pair (a b : ℕ → PBConstr) : ∀ {n i : ℕ}, i < n →
    ((List.range n).flatMap fun j => [a j, b j])[2 * i]? = some (a i) ∧
      ((List.range n).flatMap fun j => [a j, b j])[2 * i + 1]? = some (b i)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    have hlen : ((List.range n).flatMap fun j => [a j, b j]).length = 2 * n := by
      simp [List.length_flatMap, List.map_const', List.sum_replicate]; ring
    rw [List.range_succ, List.flatMap_append]
    by_cases hi : i < n
    · obtain ⟨h1, h2⟩ := getElem?_flatMap_pair a b hi
      rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
      exact ⟨h1, h2⟩
    · have : i = n := by omega
      subst this
      rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hlen]
      simp

theorem lookup_item {e : ProofLog} {db : List (ℕ × PBConstr)} (h : I.Run e db) {i : ℕ}
    (hi : i < I.n) :
    lookup db (aloId i) = some (alo (I.off i) (I.len i)).normalize ∧
      lookup db (amoId i) = some (amo (I.off i) (I.len i)).normalize := by
  obtain ⟨h1, h2⟩ := getElem?_flatMap_pair (fun j => alo (I.off j) (I.len j))
    (fun j => amo (I.off j) (I.len j)) hi
  rw [show aloId i = 8 + 2 * i + 1 by simp only [aloId]; omega,
    show amoId i = 9 + 2 * i + 1 by simp only [amoId]; omega]
  constructor
  · refine I.lookup_formula h (m := 8 + 2 * i) ?_
    rw [formula,
      List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
    simpa using h1
  · refine I.lookup_formula h (m := 9 + 2 * i) ?_
    rw [formula,
      List.getElem?_append_right (by simp only [List.length_cons, List.length_nil]; omega)]
    simpa [show 9 + 2 * i - 8 = 2 * i + 1 by omega] using h2

theorem lookup_fixed {e : ProofLog} {db : List (ℕ × PBConstr)} (h : I.Run e db) :
    lookup db 1 = some I.linkW₁.normalize ∧ lookup db 2 = some I.linkW₂.normalize ∧
      lookup db 3 = some I.linkP₁.normalize ∧ lookup db 4 = some I.linkP₂.normalize ∧
      lookup db 5 = some (alo I.wBase I.wDom.length).normalize ∧
      lookup db 6 = some (amo I.wBase I.wDom.length).normalize ∧
      lookup db 7 = some (alo I.pBase I.pDom.length).normalize ∧
      lookup db 8 = some (amo I.pBase I.pDom.length).normalize :=
  ⟨I.lookup_formula h (m := 0) rfl, I.lookup_formula h (m := 1) rfl,
    I.lookup_formula h (m := 2) rfl, I.lookup_formula h (m := 3) rfl,
    I.lookup_formula h (m := 4) rfl, I.lookup_formula h (m := 5) rfl,
    I.lookup_formula h (m := 6) rfl, I.lookup_formula h (m := 7) rfl⟩

/-- A reification by the next free variable runs, with the numbers of its halves. -/
theorem Run.reify' {e : ProofLog} {db : List (ℕ × PBConstr)} (h : I.Run e db) {c : PBConstr}
    (hv : ∀ v ∈ c.vars, v < e.var) (hsat : ∃ σ, c.Holds σ) :
    ∃ db', I.Run (e.push (VeriPB.reify e.var c) 4 1) db' ∧ Sub db db' ∧
      lookup db' (e.next + 1) = some (impl [(e.var, true)] c).normalize ∧
      lookup db' (e.next + 3) = some (impl [(e.var, false)] c.negate).normalize := by
  obtain ⟨h', s'⟩ := Run.reify I h hv hsat
  exact ⟨_, h', s', by simp (disch := omega) only [lookup_cons, ite_eq_right, ↓reduceIte],
    ((lookup_cons _ _ _ _).trans (ite_eq_left rfl))⟩

/-! ### Nodes -/

theorem dimS_le {i : ℕ} {st : St} (h : st.1 ≤ I.tot I.cw i ∧ st.2 ≤ I.tot I.cp i) (d : ℕ) :
    dimS st d ≤ I.tot (I.dimA d) i := by
  simp only [dimS, dimA]; split_ifs <;> simp [h.1, h.2]

theorem sat_cD {i : ℕ} {st : St} (h : st.1 ≤ I.tot I.cw i ∧ st.2 ≤ I.tot I.cp i) (d : ℕ) :
    ∃ σ, (I.cD i st d).Holds σ := by
  refine ⟨fun _ => dimPol d, ?_⟩
  rw [cD, holds_dimC', part_const]
  have := I.dimS_le h d
  split_ifs
  · exact this
  · exact Nat.sub_le _ _

theorem vars_cD {i : ℕ} {st : St} {d x : ℕ} (h : x ∈ (I.cD i st d).vars) : x < I.off i :=
  I.vars_dimC h

/-- **The facts about a node** of layer `i` in the database `db`, its variables below `V`. -/
structure NodeOk (i : ℕ) (db : List (ℕ × PBConstr)) (V : ℕ) (u : Node) : Prop where
  /-- The state is within the totals. -/
  bnd : u.st.1 ≤ I.tot I.cw i ∧ u.st.2 ≤ I.tot I.cp i
  /-- The variables are extension variables. -/
  nv : I.M ≤ u.v
  /-- The variables are below `V`. -/
  lt : u.v + 4 < V
  /-- `z_d ⇒ …`. -/
  fw : ∀ d < 4, lookup db (u.fwd d) = some (impl [(u.z d, true)] (I.cD i u.st d)).normalize
  /-- `… ⇒ z_d`. -/
  bw : ∀ d < 4, lookup db (u.bwd d) = some (impl [(u.z d, false)] (I.cD i u.st d).negate).normalize
  /-- `S ⇒ …`. -/
  sf : lookup db (u.fwd 4) = some (impl [(u.S, true)] (cS u.v)).normalize
  /-- `… ⇒ S`. -/
  sb : lookup db (u.bwd 4) = some (impl [(u.S, false)] (cS u.v).negate).normalize

theorem NodeOk.mono {i : ℕ} {db db' : List (ℕ × PBConstr)} {V V' : ℕ} {u : Node}
    (h : I.NodeOk i db V u) (hs : Sub db db') (hV : V ≤ V') : I.NodeOk i db' V' u :=
  ⟨h.bnd, h.nv, by have := h.lt; omega, fun d hd => hs _ _ (h.fw d hd),
    fun d hd => hs _ _ (h.bw d hd), hs _ _ h.sf, hs _ _ h.sb⟩

/-- **Creating a layer runs**, and gives nodes with their facts. -/
theorem mkLayer_spec {i : ℕ} (hi : i ≤ I.n) : ∀ (sts : List St) (e : ProofLog)
    (db : List (ℕ × PBConstr)), I.Run e db →
    (∀ st ∈ sts, st.1 ≤ I.tot I.cw i ∧ st.2 ≤ I.tot I.cp i) →
    ∃ db', I.Run (I.mkLayer i e sts).1 db' ∧ Sub db db' ∧
      (I.mkLayer i e sts).2.map (·.st) = sts ∧
      (∀ u ∈ (I.mkLayer i e sts).2, I.NodeOk i db' (I.mkLayer i e sts).1.var u) ∧
      e.var ≤ (I.mkLayer i e sts).1.var ∧ e.next ≤ (I.mkLayer i e sts).1.next
  | [], e, db, h, _ => ⟨db, h, Sub.refl _, rfl, by simp [mkLayer], by simp [mkLayer],
      by simp [mkLayer]⟩
  | st :: sts, e, db, h, hst => by
    have hb := hst st List.mem_cons_self
    have hn := h.2.2.2.1
    have hoff := I.off_le_wBase hi
    have hW := I.wBase_le_M
    have hcv : ∀ d, ∀ k, ∀ v ∈ (I.cD i st d).vars, v < e.var + k := fun d k v hv => by
      have := I.vars_cD hv; omega
    obtain ⟨d₁, h₁, s₁, f₁, b₁⟩ := Run.reify' I h (c := I.cD i st 0) (hcv 0 0) (I.sat_cD hb 0)
    obtain ⟨d₂, h₂, s₂, f₂, b₂⟩ := Run.reify' I h₁ (c := I.cD i st 1) (hcv 1 1) (I.sat_cD hb 1)
    obtain ⟨d₃, h₃, s₃, f₃, b₃⟩ := Run.reify' I h₂ (c := I.cD i st 2) (hcv 2 2) (I.sat_cD hb 2)
    obtain ⟨d₄, h₄, s₄, f₄, b₄⟩ := Run.reify' I h₃ (c := I.cD i st 3) (hcv 3 3) (I.sat_cD hb 3)
    obtain ⟨d₅, h₅, s₅, f₅, b₅⟩ := Run.reify' I h₄ (c := cS e.var)
      (fun v hv => by
        simp only [cS, PBConstr.vars, List.map_map, List.mem_map, List.mem_range,
          Function.comp_apply, termVar_mk] at hv
        obtain ⟨d, hd, rfl⟩ := hv
        simp only [ProofLog.push]; omega)
      ⟨fun _ => true, by simp [cS, Holds, lhs, termVal, List.range_succ]⟩
    simp only [ProofLog.push] at f₁ b₁ f₂ b₂ f₃ b₃ f₄ b₄ f₅ b₅ h₂ h₃ h₄ h₅
    have he : I.nodeSteps i (mkNode e st) = VeriPB.reify e.var (I.cD i st 0) ++
        VeriPB.reify (e.var + 1) (I.cD i st 1) ++ VeriPB.reify (e.var + 1 + 1) (I.cD i st 2) ++
        VeriPB.reify (e.var + 1 + 1 + 1) (I.cD i st 3) ++
        VeriPB.reify (e.var + 1 + 1 + 1 + 1) (cS e.var) := by
      simp [nodeSteps, mkNode, Node.z, Node.S]
    have hpush : e.push (I.nodeSteps i (mkNode e st)) 20 5 =
        ⟨(VeriPB.reify (e.var + 1 + 1 + 1 + 1) (cS e.var)).reverse ++
          ((VeriPB.reify (e.var + 1 + 1 + 1) (I.cD i st 3)).reverse ++
          ((VeriPB.reify (e.var + 1 + 1) (I.cD i st 2)).reverse ++
          ((VeriPB.reify (e.var + 1) (I.cD i st 1)).reverse ++
          ((VeriPB.reify e.var (I.cD i st 0)).reverse ++ e.steps)))),
          e.next + 4 + 4 + 4 + 4 + 4, e.var + 1 + 1 + 1 + 1 + 1⟩ := by
      rw [he]; simp [ProofLog.push]
    rw [← hpush] at h₅
    obtain ⟨db', hr, hs, hmap, hok, hv, hnx⟩ := mkLayer_spec hi sts _ _ h₅
      (fun s hs => hst s (List.mem_cons_of_mem _ hs))
    have hsall := s₂.trans (s₃.trans (s₄.trans (s₅.trans hs)))
    refine ⟨db', hr, s₁.trans hsall, ?_, ?_, ?_, ?_⟩
    · simp only [mkLayer, List.map_cons, hmap]; rfl
    · simp only [mkLayer, List.mem_cons]
      rintro u (rfl | hu)
      · have hv' : e.var + 5 ≤ (I.mkLayer i (e.push (I.nodeSteps i ⟨st, e.var, e.next⟩) 20 5)
            sts).1.var := le_trans (by simp [ProofLog.push]) hv
        refine ⟨hb, by simp only [mkNode]; omega, by simp only [mkNode]; omega, ?_, ?_, ?_, ?_⟩
        · intro d hd
          simp only [Node.fwd, Node.z]
          rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl | rfl
          · exact hsall _ _ f₁
          · exact (s₃.trans (s₄.trans (s₅.trans hs))) _ _
              (by simpa [mkNode, Nat.add_assoc] using f₂)
          · exact (s₄.trans (s₅.trans hs)) _ _ (by simpa [mkNode, Nat.add_assoc] using f₃)
          · exact (s₅.trans hs) _ _ (by simpa [mkNode, Nat.add_assoc] using f₄)
        · intro d hd
          simp only [Node.bwd, Node.z]
          rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl | rfl
          · exact hsall _ _ b₁
          · exact (s₃.trans (s₄.trans (s₅.trans hs))) _ _
              (by simpa [mkNode, Nat.add_assoc] using b₂)
          · exact (s₄.trans (s₅.trans hs)) _ _ (by simpa [mkNode, Nat.add_assoc] using b₃)
          · exact (s₅.trans hs) _ _ (by simpa [mkNode, Nat.add_assoc] using b₄)
        · simp only [Node.fwd, Node.S]
          exact hs _ _ (by simpa [mkNode, Nat.add_assoc] using f₅)
        · simp only [Node.bwd, Node.S]
          exact hs _ _ (by simpa [mkNode, Nat.add_assoc] using b₅)
      · exact hok u hu
    · simp only [mkLayer]; exact le_trans (by simp [ProofLog.push]) hv
    · simp only [mkLayer]; exact le_trans (by simp [ProofLog.push]) hnx

/-! ### Transitions -/

/-- **The transition by addition** over a block of variables: the forward half of
`Z ⇔ ∑_{x<m} A x ℓₓ ≥ d` plus the backward half of `Z' ⇔ ∑_{x<m'} A x ℓₓ ≥ d'` gives `Z ⇒ Z'` at
every assignment adding at least `d' - d` on the variables `m ≤ x < m'`. -/
theorem trans_gen {A : ℕ → ℕ} {pol : Bool} {m m' d dt zu zt δ : ℕ} (hzu : m ≤ zu)
    (hzt : m' ≤ zt) {σ : ℕ → Bool} (hδ : part σ A pol m' = part σ A pol m + δ)
    (hdt : dt ≤ d + δ) (hd' : dt ≤ Knapsack.Inst.tot A m')
    (hA : ((impl [(zu, true)] (Knapsack.Inst.dimC A pol m d)).normalize.add
      (impl [(zt, false)] (Knapsack.Inst.dimC A pol m' dt).negate).normalize).Holds σ)
    (hu : σ zu = true) : σ zt = true := by
  have h1 := slack_fwd (c := Knapsack.Inst.dimC A pol m d) (z := zu)
    (fun h => by have := vars_sumTerms h; omega) (nodup_sumTerms A pol m) σ
  have h2 := slack_bwd (c := Knapsack.Inst.dimC A pol m' dt) (z := zt)
    (fun h => by have := vars_sumTerms h; omega) (nodup_sumTerms A pol m')
    ⟨fun _ => pol, by rw [holds_dimC, part_const]; exact hd'⟩ σ
  rw [holds_add_iff] at hA
  simp only [Knapsack.Inst.dimC, lhs_sumTerms, hδ, hu, ite_true] at h1 h2 hA
  cases hz : σ zt
  · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h2
    omega
  · rfl

theorem dimA_le_rowTot {i k : ℕ} (hk : k < I.len i) (a : ℕ → ℕ → ℕ) : a i k ≤ I.rowTot a i := by
  rw [rowTot]
  exact List.le_sum_of_mem (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)

/-- **A partial state follows the transition**: if `u` of layer `i` is in its partial state `d` and
the assignment picks the position `k` of item `i`, the sum of the two halves puts the successor
`t` in its partial state `d`. -/
theorem dim_trans {i k d : ℕ} (hi : i < I.n) (hd : d < 4) {u t : Node} {db : List (ℕ × PBConstr)}
    {V : ℕ} (hu : I.NodeOk i db V u) (ht : I.NodeOk (i + 1) db V t)
    (hst : t.st = I.succ i u.st k) {σ : ℕ → Bool} (hp : I.Picks σ i k)
    (hA : ((impl [(u.z d, true)] (I.cD i u.st d)).normalize.add
      (impl [(t.z d, false)] (I.cD (i + 1) t.st d).negate).normalize).Holds σ)
    (hz : σ (u.z d) = true) : σ (t.z d) = true := by
  have hoff := I.off_le_wBase (show i + 1 ≤ I.n by omega)
  have hoff' := I.off_mono (Nat.le_add_right i 1)
  have hW := I.wBase_le_M
  have hun := hu.nv
  have htn := ht.nv
  have hub := I.dimS_le hu.bnd d
  have htb := I.dimS_le ht.bnd d
  have hrow := I.dimA_le_rowTot hp.1 (I.dimA d)
  have htot := I.tot_succ (I.dimA d) hi
  have hsd : dimS t.st d = dimS u.st d + I.dimA d i k := by
    rw [hst]; simp only [dimS, succ, dimA]; split_ifs <;> rfl
  simp only [cD] at hA
  cases hpol : dimPol d
  · have hδ := I.part_off_succ σ (I.dimA d) false hi
    have hrp := I.rowPart_false hp (I.dimA d)
    simp only [hpol, Bool.false_eq_true, ↓reduceIte] at hA
    exact trans_gen (by simp only [Node.z]; omega) (by simp only [Node.z]; omega) hδ
      (by simp only [tot] at htot hub hsd ⊢; omega) (Nat.sub_le _ _) hA hz
  · have hδ := I.part_off_succ σ (I.dimA d) true hi
    rw [I.rowPart_true hp] at hδ
    simp only [hpol, ↓reduceIte] at hA
    exact trans_gen (by simp only [Node.z]; omega) (by simp only [Node.z]; omega) hδ
      (by omega) htb hA hz

/-- The literals that make the other positions of item `i` false. -/
def othersFalse (i k : ℕ) : List (Literal ℕ) :=
  ((List.range (I.len i)).filter (· != k)).map fun k' => (I.var i k', false)

theorem picks_of {σ : ℕ → Bool} {i k : ℕ} (hk : k < I.len i) (h1 : σ (I.var i k) = true)
    (h2 : Consistent σ (I.othersFalse i k)) : I.Picks σ i k :=
  ⟨hk, h1, fun k' hk' hne => by
    have := h2 (I.var i k', false)
      (List.mem_map.2 ⟨k', by simp [hk', hne], rfl⟩)
    simpa using this⟩

theorem consistent_othersFalse {σ : ℕ → Bool} {i k : ℕ} (hk : k < I.len i)
    (hamo : (amo (I.off i) (I.len i)).Holds σ) (h1 : σ (I.var i k) = true) :
    Consistent σ (I.othersFalse i k) := by
  intro l hl
  simp only [othersFalse, List.mem_map, List.mem_filter, List.mem_range, bne_iff_ne] at hl
  obtain ⟨k', ⟨hk', hne⟩, rfl⟩ := hl
  have := eq_false_of_amo (base := I.off i) hamo hk h1 hk' hne
  simpa [var] using this

theorem nodeSteps_vars {i : ℕ} {u : Node} {db : List (ℕ × PBConstr)} {V : ℕ}
    (hu : I.NodeOk i db V u) : u.S < V := by
  have := hu.lt; simp only [Node.S]; omega

/-- **A transition runs**: from a node `u` of layer `i` by the position `k` of item `i` to its
successor `t`, the four additions and the RUP step derive `S_u ∧ [xᵢ = v] ⇒ S_t`. -/
theorem trSteps_spec {i k : ℕ} (hi : i < I.n) (hk : k < I.len i) {e : ProofLog}
    {db : List (ℕ × PBConstr)} (h : I.Run e db) {u t : Node} (hu : I.NodeOk i db e.var u)
    (ht : I.NodeOk (i + 1) db e.var t) (hst : t.st = I.succ i u.st k) :
    ∃ db', I.Run (e.push (I.trSteps i k u t e) 5 0) db' ∧ Sub db db' ∧
      lookup db' (e.next + 4) = some (I.trClause i k u t).normalize := by
  obtain ⟨h₁, s₁⟩ := Run.add I h (hu.fw 0 (by omega)) (ht.bw 0 (by omega))
  obtain ⟨h₂, s₂⟩ := Run.add I h₁ (s₁ _ _ (hu.fw 1 (by omega))) (s₁ _ _ (ht.bw 1 (by omega)))
  obtain ⟨h₃, s₃⟩ := Run.add I h₂ (s₂ _ _ (s₁ _ _ (hu.fw 2 (by omega))))
    (s₂ _ _ (s₁ _ _ (ht.bw 2 (by omega))))
  obtain ⟨h₄, s₄⟩ := Run.add I h₃ (s₃ _ _ (s₂ _ _ (s₁ _ _ (hu.fw 3 (by omega)))))
    (s₃ _ _ (s₂ _ _ (s₁ _ _ (ht.bw 3 (by omega)))))
  simp only [ProofLog.push] at h₂ h₃ h₄ s₂ s₃ s₄
  set c := fun d => (impl [(u.z d, true)] (I.cD i u.st d)).normalize.add
    (impl [(t.z d, false)] (I.cD (i + 1) t.st d).negate).normalize with hc
  set db₄ := (e.next + 1 + 1 + 1, c 3) :: (e.next + 1 + 1, c 2) :: (e.next + 1, c 1) ::
    (e.next, c 0) :: db with hdb₄
  have hl : ∀ d < 4, lookup db₄ (e.next + d) = some (c d) := by
    intro d hd
    rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl | rfl <;>
      simp (disch := omega) only [hdb₄, lookup_cons, ite_eq_right, ↓reduceIte, Nat.add_zero]
  have hsub : Sub db db₄ := s₁.trans (s₂.trans (s₃.trans s₄))
  have hamo := (I.lookup_item h hi).2
  have hr : rup db₄ (I.trClause i k u t) [.neg, .id (amoId i), .id (u.fwd 4), .id e.next,
      .id (e.next + 1), .id (e.next + 2), .id (e.next + 3), .id (t.bwd 4)] = true := by
    refine rup_clause ?_
    simp only [List.map_cons, List.map_nil, Std.Sat.Literal.negate,
      Bool.not_false, Bool.not_true, List.append_nil]
    refine Knapsack.Inst.RupOk.id_imp (L := I.othersFalse i k) (hsub _ _ hamo)
      (nodup_termVar_normalize _) ?_ ?_
    · intro σ hσ hc'
      rw [holds_normalize] at hc'
      exact I.consistent_othersFalse hk hc' (lit_of hσ (by simp))
    refine Knapsack.Inst.RupOk.id_imp (L := [(u.z 0, true), (u.z 1, true), (u.z 2, true),
      (u.z 3, true)]) (hsub _ _ hu.sf) (nodup_termVar_normalize _) ?_ ?_
    · intro σ hσ hc'
      rw [holds_normalize, holds_impl] at hc'
      have := (holds_cS σ _).1 (hc' (by simp [lit_of hσ (v := u.S) (b := true) (by simp)]))
      simp only [Node.z, Nat.add_zero]
      simp [Consistent, this]
    have hpk : ∀ σ, Consistent σ ([(u.z 0, true), (u.z 1, true), (u.z 2, true), (u.z 3, true)] ++
        (I.othersFalse i k ++ [(u.S, true), (I.var i k, true), (t.S, false)])) → I.Picks σ i k :=
      fun σ hσ => I.picks_of hk (lit_of hσ (by simp)) (fun l hl => hσ l (by simp [hl]))
    have hstep : ∀ d < 4, ∀ σ, Consistent σ ([(u.z 0, true), (u.z 1, true), (u.z 2, true),
        (u.z 3, true)] ++ (I.othersFalse i k ++ [(u.S, true), (I.var i k, true), (t.S, false)])) →
        (c d).Holds σ → σ (t.z d) = true := fun d hd σ hσ hcd =>
      I.dim_trans hi hd hu ht hst (hpk σ hσ) hcd (lit_of hσ (by
        rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl | rfl <;> simp))
    have hone : ∀ d < 4, ∀ σ, Consistent σ ([(u.z 0, true), (u.z 1, true), (u.z 2, true),
        (u.z 3, true)] ++ (I.othersFalse i k ++ [(u.S, true), (I.var i k, true), (t.S, false)])) →
        (c d).Holds σ → Consistent σ [(t.z d, true)] := fun d hd σ hσ hcd l hl => by
      simp only [List.mem_singleton] at hl
      subst hl
      simpa using hstep d hd σ hσ hcd
    refine Knapsack.Inst.RupOk.id_imp (L := [(t.z 0, true)])
      (by have := hl 0 (by omega); rwa [Nat.add_zero] at this)
      (nodup_termVar_normalize _) (hone 0 (by omega)) ?_
    refine Knapsack.Inst.RupOk.id_imp (L := [(t.z 1, true)]) (hl 1 (by omega))
      (nodup_termVar_normalize _) (fun σ hσ => hone 1 (by omega) σ (consistent_append.1 hσ).2) ?_
    refine Knapsack.Inst.RupOk.id_imp (L := [(t.z 2, true)]) (hl 2 (by omega))
      (nodup_termVar_normalize _) (fun σ hσ => hone 2 (by omega) σ
        (consistent_append.1 (consistent_append.1 hσ).2).2) ?_
    refine Knapsack.Inst.RupOk.id_imp (L := [(t.z 3, true)]) (hl 3 (by omega))
      (nodup_termVar_normalize _) (fun σ hσ => hone 3 (by omega) σ
        (consistent_append.1 (consistent_append.1 (consistent_append.1 hσ).2).2).2) ?_
    refine Knapsack.Inst.RupOk.id_conflict (hsub _ _ ht.sb) (nodup_termVar_normalize _) ?_
    intro σ hσ hc'
    rw [holds_normalize, holds_impl_neg_negate] at hc'
    have h1 := hc' ((holds_cS σ _).2 ⟨lit_of hσ (v := t.z 0) (by simp),
      lit_of hσ (v := t.z 1) (by simp), lit_of hσ (v := t.z 2) (by simp),
      lit_of hσ (v := t.z 3) (by simp)⟩)
    have h2 := lit_of hσ (v := t.S) (b := false) (by simp)
    simp only [Node.S] at h1 h2
    simp [h1] at h2
  have hM := h.2.2.2.1
  have hvar : I.var i k < I.M := by
    have := I.var_lt (i := I.n) hi hk
    have := I.wBase_le_M
    simp only [wBase] at *; omega
  obtain ⟨h₅, s₅⟩ := Run.rup I h₄ hr (fun v hv => by
    obtain ⟨l, hl, rfl⟩ := vars_clause hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact I.nodeSteps_vars hu
    · simp only; omega
    · exact I.nodeSteps_vars ht)
  refine ⟨_, ?_, hsub.trans s₅, ?_⟩
  · simp only [ProofLog.push] at h₅ ⊢
    convert h₅ using 2
    simp [trSteps]
  · simp [show e.next + 1 + 1 + 1 + 1 = e.next + 4 by omega, lookup_cons]

theorem tgt_spec {L : List Node} {st : St} (h : ∃ t ∈ L, t.st = st) :
    tgt L st ∈ L ∧ (tgt L st).st = st := by
  obtain ⟨t, ht, hst⟩ := h
  rcases hf : L.find? (·.st == st) with _ | x
  · exact absurd (List.find?_eq_none.1 hf t ht) (by simp [hst])
  · have := List.find?_some hf
    simp only [beq_iff_eq] at this
    simp only [tgt, hf, Option.getD_some]
    exact ⟨List.mem_of_find?_eq_some hf, this⟩

theorem mem_livePos {D : Dom} {k : ℕ} : k ∈ livePos D ↔ k < D.length ∧ dlive D k = true := by
  simp [livePos]

/-- The facts about a transition out of `u` into `L'`. -/
def TrOk (i : ℕ) (db : List (ℕ × PBConstr)) (L' : List Node) (u : Node) (x : Tr) : Prop :=
  x.tgt ∈ L' ∧ x.tgt.st = I.succ i u.st x.pos ∧ x.pos < I.len i ∧
    lookup db x.id = some (I.trClause i x.pos u x.tgt).normalize

theorem trans1_spec {i : ℕ} (hi : i < I.n) {L' : List Node} {u : Node} :
    ∀ (ks : List ℕ) (e : ProofLog) (db : List (ℕ × PBConstr)), I.Run e db →
      I.NodeOk i db e.var u → (∀ t ∈ L', I.NodeOk (i + 1) db e.var t) →
      (∀ k ∈ ks, k < I.len i ∧ ∃ t ∈ L', t.st = I.succ i u.st k) →
      ∃ db', I.Run (I.trans1 i L' u e ks).1 db' ∧ Sub db db' ∧
        (I.trans1 i L' u e ks).2.map (·.pos) = ks ∧
        (∀ x ∈ (I.trans1 i L' u e ks).2, I.TrOk i db' L' u x) ∧
        (I.trans1 i L' u e ks).1.var = e.var
  | [], e, db, h, _, _, _ => ⟨db, h, Sub.refl _, rfl, by simp [trans1], rfl⟩
  | k :: ks, e, db, h, hu, hL', hks => by
    obtain ⟨hk, hcov⟩ := hks k List.mem_cons_self
    obtain ⟨htm, hts⟩ := tgt_spec hcov
    obtain ⟨db₁, h₁, s₁, hl₁⟩ := I.trSteps_spec hi hk h hu (hL' _ htm) hts
    obtain ⟨db', h', s', hmap, hall, hv⟩ := trans1_spec hi ks _ db₁ h₁
      (hu.mono I s₁ (by simp [ProofLog.push]))
      (fun t ht => (hL' t ht).mono I s₁ (by simp [ProofLog.push]))
      (fun k hk => hks k (List.mem_cons_of_mem _ hk))
    simp only [trans1]
    refine ⟨db', h', s₁.trans s', by simp [hmap], ?_, by rw [hv]; simp [ProofLog.push]⟩
    simp only [List.mem_cons]
    rintro x (rfl | hx)
    · exact ⟨htm, hts, hk, s' _ _ hl₁⟩
    · exact hall x hx

/-- **The facts about the transitions out of a node** of layer `i` into the layer `L'`. -/
structure OutOk (i : ℕ) (db : List (ℕ × PBConstr)) (V : ℕ) (L' : List Node) (o : Out) : Prop where
  /-- The node's facts. -/
  u : I.NodeOk i db V o.u
  /-- The positions. -/
  pos : o.tr.map (·.pos) = livePos (I.dom i)
  /-- The transitions' facts. -/
  tr : ∀ x ∈ o.tr, I.TrOk i db L' o.u x
  /-- `S ∧ D ⇒ ⋁ S'`. -/
  succ : lookup db o.succ = some (I.succClause i o.u o.tr).normalize

theorem OutOk.mono {i : ℕ} {db db' : List (ℕ × PBConstr)} {V V' : ℕ}
    {L' : List Node} {o : Out} (h : I.OutOk i db V L' o) (hs : Sub db db') (hV : V ≤ V') :
    I.OutOk i db' V' L' o :=
  ⟨h.u.mono I hs hV, h.pos, fun x hx => by
    obtain ⟨h1, h2, h3, h4⟩ := h.tr x hx
    exact ⟨h1, h2, h3, hs _ _ h4⟩, hs _ _ h.succ⟩

theorem holds_trClause {σ : ℕ → Bool} {i k : ℕ} {u t : Node} :
    (I.trClause i k u t).normalize.Holds σ ↔
      (σ u.S = true → σ (I.var i k) = true → σ t.S = true) := by
  rw [holds_normalize, trClause, holds_clause]
  cases hu : σ u.S <;> cases hi : σ (I.var i k) <;> cases ht : σ t.S <;> simp [hu, hi, ht]

theorem mem_negItem {i : ℕ} {l : Literal ℕ} :
    l ∈ I.negItem i ↔ ∃ k < I.len i, dlive (I.dom i) k = false ∧ l = (I.var i k, true) := by
  simp only [negItem, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨k, hk, h⟩
    by_cases hl : dlive (I.dom i) k = true
    · simp [hl] at h
    · simp only [hl, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      exact ⟨k, hk, by simpa using hl, h.symm⟩
  · rintro ⟨k, hk, hl, rfl⟩
    exact ⟨k, hk, by simp [hl]⟩

/-- **A node's transitions run**, then `S_u ∧ D ⇒ ⋁ S_t` by RUP. -/
theorem transOut_spec {i : ℕ} (hi : i < I.n) {L' : List Node} {e : ProofLog}
    {db : List (ℕ × PBConstr)} (h : I.Run e db) {u : Node} (hu : I.NodeOk i db e.var u)
    (hL' : ∀ t ∈ L', I.NodeOk (i + 1) db e.var t)
    (hks : ∀ k ∈ livePos (I.dom i), ∃ t ∈ L', t.st = I.succ i u.st k) :
    ∃ db', I.Run (I.transOut i L' e u).1 db' ∧ Sub db db' ∧
      (I.transOut i L' e u).2.u = u ∧
      I.OutOk i db' (I.transOut i L' e u).1.var L' (I.transOut i L' e u).2 ∧
      (I.transOut i L' e u).1.var = e.var := by
  obtain ⟨db₁, h₁, s₁, hmap, hall, hv⟩ := I.trans1_spec hi (livePos (I.dom i)) e db h hu hL'
    (fun k hk => ⟨(mem_livePos.1 hk).1, hks k hk⟩)
  have hvo : (I.transOut i L' e u).1.var = e.var := by
    simp only [transOut, ProofLog.push, Nat.add_zero]; exact hv
  set r := I.trans1 i L' u e (livePos (I.dom i)) with hr
  have hrup : rup db₁ (I.succClause i u r.2) (.neg :: r.2.map (fun x => .id x.id) ++
      [.id (aloId i)]) = true := by
    refine rup_clause ?_
    set K := ((u.S, false) :: I.negItem i ++ r.2.map fun x => (x.tgt.S, true)).map
      Std.Sat.Literal.negate ++ [] with hK
    have hSK : (u.S, true) ∈ K := by simp [hK, Std.Sat.Literal.negate]
    have hTK : ∀ x ∈ r.2, (x.tgt.S, false) ∈ K := fun x hx =>
      List.mem_append_left _ (List.mem_map.2 ⟨(x.tgt.S, true), List.mem_cons_of_mem _
        (List.mem_append_right _ (List.mem_map.2 ⟨x, hx, rfl⟩)), rfl⟩)
    have := RupOk.imps (db := db₁) (neg := (I.succClause i u r.2).negate)
      (K₀ := K) (rest := [.id (aloId i)])
      (r.2.map fun x => (Hint.id x.id, (I.var i x.pos, false))) K (fun l hl => hl) ?_ ?_
    · rw [List.map_map] at this; exact this
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      obtain ⟨-, -, -, hl⟩ := hall x hx
      refine ⟨_, hl, nodup_termVar_normalize _, fun σ hσ hc => ?_⟩
      have h1 := I.holds_trClause.1 hc (lit_of hσ hSK)
      have h2 := lit_of hσ (hTK x hx)
      by_contra hne
      simp only [Literal.eval_mk] at hne ⊢
      simp_all
    · refine Knapsack.Inst.RupOk.id_conflict ((I.lookup_item h₁ hi).1) (nodup_termVar_normalize _)
        fun σ hσ hc => ?_
      rw [holds_normalize, holds_alo] at hc
      obtain ⟨k, hk, hσk⟩ := hc
      by_cases hl : dlive (I.dom i) k = true
      · have hkm : k ∈ r.2.map (·.pos) := by rw [hmap]; exact mem_livePos.2 ⟨hk, hl⟩
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hkm
        have := lit_of hσ (v := I.var i x.pos) (b := false)
          (by simp only [List.map_map, List.mem_append, List.mem_map]; exact .inl ⟨x, hx, rfl⟩)
        simp [var] at this; simp [this] at hσk
      · have hm : (I.var i k, false) ∈ K :=
          List.mem_append_left _ (List.mem_map.2 ⟨(I.var i k, true), List.mem_cons_of_mem _
            (List.mem_append_left _ (I.mem_negItem.2 ⟨k, hk, by simpa using hl, rfl⟩)), rfl⟩)
        have := lit_of hσ (v := I.var i k) (b := false) (List.mem_append_right _ hm)
        simp [var] at this; simp [this] at hσk
  obtain ⟨h₂, s₂⟩ := Run.rup I h₁ hrup (fun v hv' => by
    obtain ⟨l, hl, rfl⟩ := vars_clause hv'
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hl
    rw [hv]
    rcases hl with (rfl | hl) | ⟨x, hx, rfl⟩
    · exact I.nodeSteps_vars hu
    · obtain ⟨k, hk, -, rfl⟩ := I.mem_negItem.1 hl
      have := I.var_lt (i := I.n) hi hk
      have := I.wBase_le_M
      have := h.2.2.2.1
      simp only [wBase] at *; omega
    · exact I.nodeSteps_vars (hL' _ (hall x hx).1))
  refine ⟨_, h₂, s₁.trans s₂, rfl, ⟨hu.mono I (s₁.trans s₂) hvo.ge, hmap, fun x hx => ?_, ?_⟩,
    hvo⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hall x hx
    exact ⟨h1, h2, h3, s₂ _ _ h4⟩
  · exact (lookup_cons _ _ _ _).trans (ite_eq_left rfl)

theorem trans_spec {i : ℕ} (hi : i < I.n) {L' : List Node} :
    ∀ (L : List Node) (e : ProofLog) (db : List (ℕ × PBConstr)), I.Run e db →
      (∀ u ∈ L, I.NodeOk i db e.var u) → (∀ t ∈ L', I.NodeOk (i + 1) db e.var t) →
      (∀ u ∈ L, ∀ k ∈ livePos (I.dom i), ∃ t ∈ L', t.st = I.succ i u.st k) →
      ∃ db', I.Run (I.trans i L' e L).1 db' ∧ Sub db db' ∧
        (I.trans i L' e L).2.map (·.u) = L ∧
        (∀ o ∈ (I.trans i L' e L).2, I.OutOk i db' (I.trans i L' e L).1.var L' o) ∧
        (I.trans i L' e L).1.var = e.var
  | [], e, db, h, _, _, _ => ⟨db, h, Sub.refl _, rfl, by simp [trans], rfl⟩
  | u :: L, e, db, h, hL, hL', hs => by
    obtain ⟨db₁, h₁, s₁, hu₁, hok₁, hv₁⟩ := I.transOut_spec hi h (hL u List.mem_cons_self) hL'
      (hs u List.mem_cons_self)
    obtain ⟨db', h', s', hmap, hall, hv⟩ := trans_spec hi L _ db₁ h₁
      (fun v hv => by rw [hv₁]; exact (hL v (List.mem_cons_of_mem _ hv)).mono I s₁ le_rfl)
      (fun t ht => by rw [hv₁]; exact (hL' t ht).mono I s₁ le_rfl)
      (fun v hv => hs v (List.mem_cons_of_mem _ hv))
    refine ⟨db', h', s₁.trans s', by simp [trans, hmap, hu₁], ?_, by simp [trans, hv, hv₁]⟩
    simp only [trans, List.mem_cons]
    rintro o (rfl | ho)
    · exact hok₁.mono I s' (by rw [hv, hv₁])
    · exact hall o ho

/-! ### The antecedent and the layers -/

theorem negate_negD : I.negD.map Std.Sat.Literal.negate = I.antecedent := by
  simp [negD, List.map_map, Function.comp_def, negate_negate]

/-- Under the antecedent, the literals of its negation are false. -/
theorem eval_negD {σ : ℕ → Bool} (h : Consistent σ I.antecedent) :
    ∀ l ∈ I.negD, Literal.eval σ l = false := by
  intro l hl
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hl
  simp [Literal.eval_negate, h m hm]

theorem vars_antecedent {l : Literal ℕ} (h : l ∈ I.antecedent) : l.1 < I.M := by
  have hW := I.wBase_le_M
  simp only [antecedent, List.mem_append, List.mem_flatMap, List.mem_filterMap,
    List.mem_range] at h
  rcases h with (⟨j, hj, k, hk, hl⟩ | ⟨k, hk, hl⟩) | ⟨k, hk, hl⟩ <;>
    split_ifs at hl <;> cases hl
  · have := I.var_lt (i := I.n) hj hk; simp only [wBase] at *; omega
  · simp only [M, pBase] at *; omega
  · simp only [M] at *; omega

theorem vars_negD {l : Literal ℕ} (h : l ∈ I.negD) : l.1 < I.M := by
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
  obtain ⟨v, b⟩ := m
  simpa [Std.Sat.Literal.negate] using I.vars_antecedent hm

theorem mem_nextL {i : ℕ} {L : List St} {t : St} :
    t ∈ I.nextL i L ↔ ∃ st ∈ L, ∃ k ∈ livePos (I.dom i), t = I.succ i st k := by
  simp only [nextL, List.mem_dedup, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨st, hst, k, hk, rfl⟩; exact ⟨st, hst, k, hk, rfl⟩
  · rintro ⟨st, hst, k, hk, rfl⟩; exact ⟨st, hst, k, hk, rfl⟩

theorem le_tot_of_mem_lay : ∀ {i : ℕ} {st : St}, i ≤ I.n → st ∈ I.lay i →
    st.1 ≤ I.tot I.cw i ∧ st.2 ≤ I.tot I.cp i
  | 0, st, _, h => by simp only [lay, List.mem_singleton] at h; subst h; simp
  | i + 1, st, hi, h => by
    obtain ⟨s, hs, k, hk, rfl⟩ := I.mem_nextL.1 h
    have := le_tot_of_mem_lay (by omega) hs
    have hk := (mem_livePos.1 hk).1
    rw [I.tot_succ _ (by omega), I.tot_succ _ (by omega)]
    have := I.dimA_le_rowTot hk I.cw
    have := I.dimA_le_rowTot hk I.cp
    simp only [succ]; omega

theorem negate_aloClause (L : List Node) :
    (I.negD ++ L.map fun u => (u.S, true)).map Std.Sat.Literal.negate ++ [] =
      I.antecedent ++ L.map fun u => (u.S, false) := by
  simp [List.map_append, negate_negD, List.map_map, Function.comp_def, Std.Sat.Literal.negate]

/-- Under the antecedent and the falsity of every node of `L'`, the clause `S_u ∧ D ⇒ ⋁ S_t`
of a node whose targets are in `L'` makes `S_u` false. -/
theorem succ_false {i : ℕ} (hi : i < I.n) {o : Out} {σ : ℕ → Bool}
    {K : List (Literal ℕ)} (hD : ∀ l ∈ I.antecedent, l ∈ K)
    (hL' : ∀ x ∈ o.tr, (x.tgt.S, false) ∈ K) (hσ : Consistent σ K)
    (hc : (I.succClause i o.u o.tr).normalize.Holds σ) : σ o.u.S = false := by
  rw [holds_normalize, succClause, holds_clause] at hc
  obtain ⟨l, hl, hev⟩ := hc
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hl
  rcases hl with (rfl | hl) | ⟨x, hx, rfl⟩
  · simpa using hev
  · obtain ⟨k, hk, hlv, rfl⟩ := I.mem_negItem.1 hl
    have hmem : (I.var i k, false) ∈ I.antecedent := by
      simp only [antecedent, List.mem_append, List.mem_flatMap, List.mem_filterMap,
        List.mem_range]
      exact .inl (.inl ⟨i, hi, k, hk, by simp [hlv]⟩)
    have := lit_of hσ (hD _ hmem)
    simp [this] at hev
  · have := lit_of hσ (hL' x hx)
    simp [this] at hev

/-- **The at-least-one constraint of the next layer runs.** -/
theorem rup_alo {i : ℕ} (hi : i < I.n) {db : List (ℕ × PBConstr)} {V : ℕ}
    {L L' : List Node} {outs : List Out} {a : ℕ} (hmap : outs.map (·.u) = L)
    (houts : ∀ o ∈ outs, I.OutOk i db V L' o)
    (halo : lookup db a = some (I.aloClause L).normalize) :
    rup db (I.aloClause L') (.neg :: outs.map (fun o => .id o.succ) ++ [.id a]) = true := by
  refine rup_clause ?_
  rw [negate_aloClause]
  have := RupOk.imps (db := db) (neg := (I.aloClause L').negate)
    (K₀ := I.antecedent ++ L'.map fun u => (u.S, false)) (rest := [.id a])
    (outs.map fun o => (Hint.id o.succ, (o.u.S, false))) _ (fun l hl => hl) ?_ ?_
  · rw [List.map_map] at this; exact this
  · intro x hx
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hx
    refine ⟨_, (houts o ho).succ, nodup_termVar_normalize _, fun σ hσ hc => ?_⟩
    have := I.succ_false hi (fun l hl => List.mem_append_left _ hl)
      (fun x hx => List.mem_append_right _ (List.mem_map.2 ⟨_, ((houts o ho).tr x hx).1, rfl⟩))
      hσ hc
    simp [this]
  · refine Knapsack.Inst.RupOk.id_conflict halo (nodup_termVar_normalize _) fun σ hσ hc => ?_
    rw [holds_normalize, aloClause, holds_clause] at hc
    obtain ⟨l, hl, hev⟩ := hc
    rcases List.mem_append.1 hl with hl | hl
    · have := I.eval_negD (fun m hm => hσ m (by simp [hm])) l hl
      simp [this] at hev
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hl
      rw [← hmap] at hu
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hu
      have := lit_of hσ (v := o.u.S) (b := false)
        (by simp only [List.map_map, List.mem_append, List.mem_map]; exact .inl ⟨o, ho, rfl⟩)
      simp [this] at hev

/-- **The facts about a layer** `i` of the forward pass. -/
structure LayOk (i : ℕ) (db : List (ℕ × PBConstr)) (V : ℕ) (r : Layer) : Prop where
  /-- The index. -/
  idx : r.i = i
  /-- The states are those of the layer. -/
  lay : r.nodes.map (·.st) = I.lay i
  /-- The nodes' facts. -/
  nodes : ∀ u ∈ r.nodes, I.NodeOk i db V u
  /-- The at-least-one constraint. -/
  alo : lookup db r.alo = some (I.aloClause r.nodes).normalize

theorem LayOk.mono {i : ℕ} {db db' : List (ℕ × PBConstr)} {V V' : ℕ}
    {r : Layer} (h : I.LayOk i db V r) (hs : Sub db db') (hV : V ≤ V') :
    I.LayOk i db' V' r :=
  ⟨h.idx, h.lay, fun u hu => (h.nodes u hu).mono I hs hV, hs _ _ h.alo⟩

/-- **The layers before layer `j`**, latest first, the nodes of layer `j` being `L'`: each with
its facts and its transitions into the layer after it. -/
def Chain (db : List (ℕ × PBConstr)) (V : ℕ) : ℕ → List Node → List Layer → Prop
  | _, _, [] => True
  | j, L', r :: rs => r.i + 1 = j ∧ I.LayOk r.i db V r ∧ r.outs.map (·.u) = r.nodes ∧
      (∀ o ∈ r.outs, I.OutOk r.i db V L' o) ∧ Chain db V r.i r.nodes rs

theorem Chain.mono {db db' : List (ℕ × PBConstr)} {V V' : ℕ} (hs : Sub db db')
    (hV : V ≤ V') : ∀ {j : ℕ} {L' : List Node} {rs : List Layer}, I.Chain db V j L' rs →
      I.Chain db' V' j L' rs
  | _, _, [], _ => trivial
  | _, _, _ :: _, ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨h1, h2.mono I hs hV, h3, fun o ho => (h4 o ho).mono I hs hV, Chain.mono hs hV h5⟩

/-- **The forward pass runs**: from layer `i`, the layers `i + 1, …, n` with their transitions and
at-least-one constraints. -/
theorem fwd_spec : ∀ (k i : ℕ) (e : ProofLog) (L : List Node) (a : ℕ)
    (recs : List Layer) (db : List (ℕ × PBConstr)), i + k = I.n → I.Run e db →
    I.LayOk i db e.var ⟨i, L, [], a⟩ → I.Chain db e.var i L recs →
    recs.map (·.i) = (List.range i).reverse →
    ∃ db', I.Run (I.fwd k i e L a recs).1 db' ∧ Sub db db' ∧
      ∃ rn rs, (I.fwd k i e L a recs).2 = rn :: rs ∧
        I.LayOk I.n db' (I.fwd k i e L a recs).1.var rn ∧
        I.Chain db' (I.fwd k i e L a recs).1.var I.n rn.nodes rs ∧
        rs.map (·.i) = (List.range I.n).reverse
  | 0, i, e, L, a, recs, db, hk, h, hL, hc, hidx => by
    simp only [Nat.add_zero] at hk
    subst hk
    exact ⟨db, h, Sub.refl _, _, recs, rfl, hL, hc, hidx⟩
  | k + 1, i, e, L, a, recs, db, hk, h, hL, hc, hidx => by
    have hi : i < I.n := by omega
    have hLl : L.map (·.st) = I.lay i := hL.lay
    obtain ⟨db₁, h₁, s₁, hmap₁, hok₁, hv₁, -⟩ := I.mkLayer_spec (i := i + 1) (by omega)
      (I.nextL i (L.map (·.st))) e db h (fun st hst => by
        rw [hLl] at hst; exact I.le_tot_of_mem_lay (i := i + 1) (by omega) hst)
    set r₁ := I.mkLayer (i + 1) e (I.nextL i (L.map (·.st))) with hr₁
    have hlay₁ : r₁.2.map (·.st) = I.lay (i + 1) := by rw [hmap₁, hLl]; rfl
    obtain ⟨db₂, h₂, s₂, hmap₂, hok₂, hv₂⟩ := I.trans_spec hi L r₁.1 db₁ h₁
      (fun u hu => (hL.nodes u hu).mono I s₁ hv₁)
      hok₁ (fun u hu k hk => by
        have : I.succ i u.st k ∈ r₁.2.map (·.st) := by
          rw [hmap₁]; exact I.mem_nextL.2 ⟨u.st, List.mem_map_of_mem hu, k, hk, rfl⟩
        obtain ⟨t, ht, hts⟩ := List.mem_map.1 this
        exact ⟨t, ht, hts⟩)
    set r₂ := I.trans i r₁.2 r₁.1 L with hr₂
    have hrup := I.rup_alo hi hmap₂ hok₂ (s₂ _ _ (s₁ _ _ hL.alo))
    obtain ⟨h₃, s₃⟩ := Run.rup I h₂ hrup (fun v hv => by
      obtain ⟨l, hl, rfl⟩ := vars_clause hv
      rcases List.mem_append.1 hl with hl | hl
      · have := I.vars_negD hl; have := h₂.2.2.2.1; omega
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hl
        rw [hv₂]; exact I.nodeSteps_vars (hok₁ t ht))
    have hV : r₁.1.var ≤ (r₂.1.push [.step (.rup (I.aloClause r₁.2)
        (.neg :: r₂.2.map (fun o => .id o.succ) ++ [.id a]))] 1 0).var := by
      simp [ProofLog.push, hv₂]
    have hs := s₁.trans (s₂.trans s₃)
    obtain ⟨db', h', s', rest⟩ := fwd_spec k (i + 1) _ r₁.2 r₂.1.next
      (⟨i, L, r₂.2, a⟩ :: recs) _ (by omega) h₃
      ⟨rfl, hlay₁, fun u hu => (hok₁ u hu).mono I (s₂.trans s₃) hV,
        ((lookup_cons _ _ _ _).trans (ite_eq_left rfl))⟩
      ⟨rfl, ⟨rfl, hLl, fun u hu => (hL.nodes u hu).mono I hs (le_trans hv₁ hV), hs _ _ hL.alo⟩,
        hmap₂, fun o ho => (hok₂ o ho).mono I s₃ (by rw [hv₂]; exact hV),
        hc.mono I hs (le_trans hv₁ hV)⟩
      (by simp [List.range_succ, hidx])
    exact ⟨db', h', s₁.trans (s₂.trans (s₃.trans s')), rest⟩

/-- **The forward pass from the start runs.** -/
theorem forward_spec :
    ∃ db, I.Run I.forward.1 db ∧ ∃ rn rs, I.forward.2 = rn :: rs ∧
      I.LayOk I.n db I.forward.1.var rn ∧
      I.Chain db I.forward.1.var I.n rn.nodes rs ∧
      rs.map (·.i) = (List.range I.n).reverse := by
  obtain ⟨db₁, h₀, s₀, hmap₀, hok₀, hv₀, -⟩ := I.mkLayer_spec (i := 0) (Nat.zero_le _)
    (I.lay 0) ⟨[], I.start, I.M⟩ _ I.run_init (fun st hst =>
      I.le_tot_of_mem_lay (Nat.zero_le _) hst)
  set r₀ := I.mkLayer 0 ⟨[], I.start, I.M⟩ (I.lay 0) with hr₀
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, r₀.2 = [u₀] := by
    rcases h : r₀.2 with _ | ⟨u, _ | _⟩ <;> rw [h] at hmap₀ <;> simp [lay] at hmap₀ ⊢
  have hst₀ : u₀.st = (0, 0) := by rw [hu₀] at hmap₀; simpa [lay] using hmap₀
  have hn₀ := hok₀ u₀ (by rw [hu₀]; simp)
  have hz : ∀ d < 4, ∀ σ, (I.cD 0 u₀.st d).Holds σ := fun d _ σ => by
    rw [cD, holds_dimC', hst₀]
    split_ifs
    · simp [dimS]
    · simp [dimS, tot, off, Knapsack.Inst.tot]
  have hrup : rup db₁ (I.aloClause r₀.2) [.neg, .id ((r₀.2.headD noNode).bwd 0),
      .id ((r₀.2.headD noNode).bwd 1), .id ((r₀.2.headD noNode).bwd 2),
      .id ((r₀.2.headD noNode).bwd 3), .id ((r₀.2.headD noNode).bwd 4)] = true := by
    rw [hu₀]
    refine rup_clause ?_
    rw [negate_aloClause]
    simp only [List.headD_cons, List.map_cons, List.map_nil]
    refine Knapsack.Inst.RupOk.id_imp (L := [(u₀.z 0, true)]) (hn₀.bw 0 (by omega))
      (nodup_termVar_normalize _) (fun σ _ hc => by
        rw [holds_normalize, holds_impl_neg_negate] at hc
        simp [Consistent, hc (hz 0 (by omega) σ)]) ?_
    refine Knapsack.Inst.RupOk.id_imp (L := [(u₀.z 1, true)]) (hn₀.bw 1 (by omega))
      (nodup_termVar_normalize _) (fun σ _ hc => by
        rw [holds_normalize, holds_impl_neg_negate] at hc
        simp [Consistent, hc (hz 1 (by omega) σ)]) ?_
    refine Knapsack.Inst.RupOk.id_imp (L := [(u₀.z 2, true)]) (hn₀.bw 2 (by omega))
      (nodup_termVar_normalize _) (fun σ _ hc => by
        rw [holds_normalize, holds_impl_neg_negate] at hc
        simp [Consistent, hc (hz 2 (by omega) σ)]) ?_
    refine Knapsack.Inst.RupOk.id_imp (L := [(u₀.z 3, true)]) (hn₀.bw 3 (by omega))
      (nodup_termVar_normalize _) (fun σ _ hc => by
        rw [holds_normalize, holds_impl_neg_negate] at hc
        simp [Consistent, hc (hz 3 (by omega) σ)]) ?_
    refine Knapsack.Inst.RupOk.id_conflict hn₀.sb (nodup_termVar_normalize _) fun σ hσ hc => ?_
    rw [holds_normalize, holds_impl_neg_negate] at hc
    have h1 := hc ((holds_cS σ _).2 ⟨lit_of hσ (v := u₀.z 0) (by simp),
      lit_of hσ (v := u₀.z 1) (by simp), lit_of hσ (v := u₀.z 2) (by simp),
      lit_of hσ (v := u₀.z 3) (by simp)⟩)
    have h2 := lit_of hσ (v := u₀.S) (b := false) (by simp)
    simp only [Node.S] at h1 h2
    simp [h1] at h2
  obtain ⟨h₁, s₁⟩ := Run.rup I h₀ hrup (fun v hv => by
    obtain ⟨l, hl, rfl⟩ := vars_clause hv
    rcases List.mem_append.1 hl with hl | hl
    · have := I.vars_negD hl; have := h₀.2.2.2.1; omega
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hl; exact I.nodeSteps_vars (hok₀ t ht))
  obtain ⟨db₂, h₂, s₂, rest⟩ := I.fwd_spec I.n 0 _ r₀.2 r₀.1.next [] _ (by omega) h₁
    ⟨rfl, hmap₀, fun u hu => (hok₀ u hu).mono I s₁ (by simp [ProofLog.push]),
      ((lookup_cons _ _ _ _).trans (ite_eq_left rfl))⟩ trivial rfl
  exact ⟨db₂, h₂, rest⟩

/-! ### The sums at the last layer -/

/-- The coefficients of the sum `s`. -/
def sA (s : Bool) : ℕ → ℕ → ℕ := if s then I.cp else I.cw

/-- The first inequality of the sum `s`: at least its sum over the items. -/
def sLink₁ (s : Bool) : PBConstr := if s then I.linkP₁ else I.linkW₁

/-- The second inequality of the sum `s`: at most its sum over the items. -/
def sLink₂ (s : Bool) : PBConstr := if s then I.linkP₂ else I.linkW₂

theorem cD_up (s : Bool) (i : ℕ) (st : St) :
    I.cD i st (sUp s) = I.dimC (I.sA s) true i (sCoord s st) := by
  cases s <;> rfl

theorem cD_down (s : Bool) (i : ℕ) (st : St) :
    I.cD i st (sUp s + 1) = I.dimC (I.sA s) false i (I.tot (I.sA s) i - sCoord s st) := by
  cases s <;> rfl

theorem sLink₁_eq (s : Bool) :
    I.sLink₁ s = ⟨I.terms (I.sA s) true I.n ++ sTerms (I.sDom s) (I.sBase s) false,
      sTot (I.sDom s)⟩ := by cases s <;> rfl

theorem sLink₂_eq (s : Bool) :
    I.sLink₂ s = ⟨I.terms (I.sA s) false I.n ++ sTerms (I.sDom s) (I.sBase s) true,
      I.tot (I.sA s) I.n⟩ := by cases s <;> rfl

theorem wBase_le_sBase (s : Bool) : I.wBase ≤ I.sBase s := by
  cases s <;> simp [sBase, pBase]

theorem sBase_add_le_M (s : Bool) : I.sBase s + (I.sDom s).length ≤ I.M := by
  cases s <;> simp [sBase, sDom, M, pBase]

theorem lookup_sums {e : ProofLog} {db : List (ℕ × PBConstr)} (h : I.Run e db) (s : Bool) :
    lookup db (if s then 3 else 1) = some (I.sLink₁ s).normalize ∧
      lookup db (if s then 4 else 2) = some (I.sLink₂ s).normalize ∧
      lookup db (sAlo s) = some (alo (I.sBase s) (I.sDom s).length).normalize ∧
      lookup db (sAmo s) = some (amo (I.sBase s) (I.sDom s).length).normalize := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := I.lookup_fixed h
  cases s
  · exact ⟨h1, h2, h5, h6⟩
  · exact ⟨h3, h4, h7, h8⟩

theorem nodup_link (a : ℕ → ℕ → ℕ) (pol pol' : Bool) (s : Bool) :
    ((I.terms a pol I.n ++ sTerms (I.sDom s) (I.sBase s) pol').map termVar).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨I.nodup_terms a pol I.n, nodup_sTerms _ _ _, fun x hx y hy => ?_⟩
  have h1 := I.vars_terms hx
  have h2 := (vars_sTerms hy).1
  have := I.wBase_le_sBase s
  simp only [wBase] at this
  omega

/-- The `↑` partial state of a node of the last layer plus the second inequality of the sum
bounds the sum's value from below. -/
theorem link_up (s : Bool) {σ : ℕ → Bool} {st : St} {z : ℕ} (hz : I.M ≤ z)
    (hA : ((impl [(z, true)] (I.dimC (I.sA s) true I.n (sCoord s st))).normalize.add
      (I.sLink₂ s).normalize).Holds σ) (hzσ : σ z = true) :
    sCoord s st ≤ sPart σ (I.sDom s) (I.sBase s) true := by
  have hoff := I.off_le_wBase (le_refl I.n)
  have hW := I.wBase_le_M
  have h1 := slack_fwd (c := I.dimC (I.sA s) true I.n (sCoord s st)) (z := z)
    (fun h => by have := I.vars_dimC h; omega) (I.nodup_terms _ true I.n) σ
  have h2 := slack_normalize (c := I.sLink₂ s) (by rw [sLink₂_eq]; exact I.nodup_link _ _ _ s) σ
  have h3 := part_add_part σ (I.flat (I.sA s)) true (I.off I.n)
  rw [holds_add_iff] at hA
  rw [sLink₂_eq] at h2 hA
  simp only [dimC, Knapsack.Inst.dimC, lhs_sumTerms, hzσ, ite_true, lhs_append, lhs_sTerms,
    terms] at h1 h2 hA
  simp only [Bool.not_true] at h3
  simp only [sPart, tot] at *
  omega

/-- The `↓` partial state of a node of the last layer plus the first inequality of the sum bounds
the sum's value from above. -/
theorem link_down (s : Bool) {σ : ℕ → Bool} {st : St} {z : ℕ} (hz : I.M ≤ z)
    (hb : sCoord s st ≤ I.tot (I.sA s) I.n)
    (hA : ((impl [(z, true)] (I.dimC (I.sA s) false I.n
      (I.tot (I.sA s) I.n - sCoord s st))).normalize.add (I.sLink₁ s).normalize).Holds σ)
    (hzσ : σ z = true) : sPart σ (I.sDom s) (I.sBase s) true ≤ sCoord s st := by
  have hoff := I.off_le_wBase (le_refl I.n)
  have hW := I.wBase_le_M
  have h1 := slack_fwd (c := I.dimC (I.sA s) false I.n (I.tot (I.sA s) I.n - sCoord s st))
    (z := z) (fun h => by have := I.vars_dimC h; omega) (I.nodup_terms _ false I.n) σ
  have h2 := slack_normalize (c := I.sLink₁ s) (by rw [sLink₁_eq]; exact I.nodup_link _ _ _ s) σ
  have h3 := part_add_part σ (I.flat (I.sA s)) true (I.off I.n)
  have h4 := sPart_add σ (I.sDom s) (I.sBase s) true
  rw [holds_add_iff] at hA
  rw [sLink₁_eq] at h2 hA
  simp only [dimC, Knapsack.Inst.dimC, lhs_sumTerms, hzσ, ite_true, lhs_append, lhs_sTerms,
    terms] at h1 h2 hA
  simp only [Bool.not_true] at h3
  simp only [sPart, tot, Bool.not_true] at *
  omega

/-- The literals that make the other positions of the sum `s` false. -/
def othersFalseS (s : Bool) (k : ℕ) : List (Literal ℕ) :=
  ((List.range (I.sDom s).length).filter (· != k)).map fun k' => (I.sBase s + k', false)

/-- **A clause `S_t ⇒ [s ≠ u]` runs**, for a node `t` of the last layer and a value `u` of the
current domain of the sum `s` other than its coordinate. -/
theorem sSteps_spec (s : Bool) {k : ℕ} {e : ProofLog} {db : List (ℕ × PBConstr)} (h : I.Run e db)
    {t : Node} (ht : I.NodeOk I.n db e.var t) (hk : k < (I.sDom s).length)
    (hne : dval (I.sDom s) k ≠ sCoord s t.st) :
    ∃ db', I.Run (e.push (I.sSteps s t k e) 2 0) db' ∧ Sub db db' ∧
      lookup db' (e.next + 1) = some (I.sClause s t k).normalize := by
  obtain ⟨hl₁, hl₂, -, hamo⟩ := I.lookup_sums h s
  have hb : sCoord s t.st ≤ I.tot (I.sA s) I.n := by
    have := ht.bnd; cases s
    · exact this.1
    · exact this.2
  -- The addition, and its meaning at an assignment picking `k`.
  have key : ∃ c d, polEval db (if sCoord s t.st < dval (I.sDom s) k then
        [PolOp.id (t.fwd (sUp s + 1)), .id (if s then 3 else 1), .add]
      else [PolOp.id (t.fwd (sUp s)), .id (if s then 4 else 2), .add]) [] = some [c] ∧
      d < 4 ∧ (∀ v ∈ c.vars, v < e.var) ∧ (c.terms.map termVar).Nodup ∧
      ∀ σ, σ (t.z d) = true → PicksD σ (I.sDom s) (I.sBase s) k → ¬ c.Holds σ := by
    by_cases hlt : sCoord s t.st < dval (I.sDom s) k
    · simp only [hlt, ↓reduceIte]
      have hf := ht.fw (sUp s + 1) (by cases s <;> simp [sUp])
      refine ⟨_, sUp s + 1, polEval_add hf hl₁, by cases s <;> simp [sUp],
        fun v hv => (vars_add hv).elim (I.vars_of_lookup h hf v) (I.vars_of_lookup h hl₁ v),
        nodup_termVar_normalize _, fun σ hz hp hA => ?_⟩
      rw [cD_down] at hA
      have := I.link_down s (z := t.z (sUp s + 1)) (by have := ht.nv; simp only [Node.z]; omega)
        hb hA hz
      rw [sPart_true hp] at this
      omega
    · simp only [hlt, ↓reduceIte]
      have hf := ht.fw (sUp s) (by cases s <;> simp [sUp])
      refine ⟨_, sUp s, polEval_add hf hl₂, by cases s <;> simp [sUp],
        fun v hv => (vars_add hv).elim (I.vars_of_lookup h hf v) (I.vars_of_lookup h hl₂ v),
        nodup_termVar_normalize _, fun σ hz hp hA => ?_⟩
      rw [cD_up] at hA
      have := I.link_up s (z := t.z (sUp s)) (by have := ht.nv; simp only [Node.z]; omega) hA hz
      rw [sPart_true hp] at this
      omega
  obtain ⟨c, d, hp, hd, hvc, hnd, hsem⟩ := key
  obtain ⟨h₁, s₁⟩ := Run.pol I h hp hvc
  have hr : rup ((e.next, c) :: db) (I.sClause s t k)
      [.neg, .id (sAmo s), .id (t.fwd 4), .id e.next] = true := by
    refine rup_clause ?_
    simp only [List.map_cons, List.map_nil, Std.Sat.Literal.negate, Bool.not_false,
      List.append_nil]
    refine Knapsack.Inst.RupOk.id_imp (L := I.othersFalseS s k) (s₁ _ _ hamo)
      (nodup_termVar_normalize _) (fun σ hσ hc l hl => ?_) ?_
    · rw [holds_normalize] at hc
      simp only [othersFalseS, List.mem_map, List.mem_filter, List.mem_range, bne_iff_ne] at hl
      obtain ⟨k', ⟨hk', hne'⟩, rfl⟩ := hl
      simpa using eq_false_of_amo hc hk (lit_of hσ (by simp)) hk' hne'
    refine Knapsack.Inst.RupOk.id_imp (L := [(t.z 0, true), (t.z 1, true), (t.z 2, true),
      (t.z 3, true)]) (s₁ _ _ ht.sf) (nodup_termVar_normalize _) ?_ ?_
    · intro σ hσ hc'
      rw [holds_normalize, holds_impl] at hc'
      have := (holds_cS σ _).1 (hc' (by simp [lit_of hσ (v := t.S) (b := true) (by simp)]))
      simp only [Node.z, Nat.add_zero]
      simp [Consistent, this]
    refine Knapsack.Inst.RupOk.id_conflict ((lookup_cons _ _ _ _).trans (ite_eq_left rfl)) hnd
      fun σ hσ hc => ?_
    refine hsem σ ?_ ⟨hk, lit_of hσ (by simp), fun k' hk' hne' => lit_of hσ ?_⟩ hc
    · rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl | rfl <;>
        exact lit_of hσ (by simp)
    · simp only [List.mem_append, othersFalseS, List.mem_map, List.mem_filter, List.mem_range,
        bne_iff_ne]
      exact .inr (.inl ⟨k', ⟨hk', hne'⟩, rfl⟩)
  obtain ⟨h₂, s₂⟩ := Run.rup I h₁ hr (fun v hv => by
    obtain ⟨l, hl, rfl⟩ := vars_clause hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    simp only [ProofLog.push]
    rcases hl with rfl | rfl
    · exact I.nodeSteps_vars ht
    · have := I.sBase_add_le_M s; have := h.2.2.2.1; simp only; omega)
  refine ⟨_, ?_, s₁.trans s₂, ?_⟩
  · simp only [ProofLog.push] at h₂ ⊢
    convert h₂ using 2
    simp [sSteps]
  · simp [ProofLog.push, lookup_cons]

/-- The clauses `S ⇒ [s ≠ u]` in the database. -/
private def SlOk (db : List (ℕ × PBConstr)) (sl : List ((ℕ × Bool × ℕ) × ℕ)) : Prop :=
  ∀ x ∈ sl,
    lookup db x.2 = some (clause [(x.1.1, false), (I.sBase x.1.2.1 + x.1.2.2, false)]).normalize

private theorem SlOk.mono {db db' : List (ℕ × PBConstr)} {sl : List ((ℕ × Bool × ℕ) × ℕ)}
    (h : I.SlOk db sl) (hs : Sub db db') : I.SlOk db' sl := fun x hx => hs _ _ (h x hx)

theorem slook_mem {sl : List ((ℕ × Bool × ℕ) × ℕ)} {x : ℕ × Bool × ℕ}
    (h : ∃ k, (x, k) ∈ sl) : (x, slook sl x) ∈ sl := by
  obtain ⟨k, hk⟩ := h
  rcases hf : sl.find? (·.1 == x) with _ | y
  · exact absurd (List.find?_eq_none.1 hf _ hk) (by simp)
  · have := List.find?_some hf
    simp only [beq_iff_eq] at this
    simp only [slook, hf, Option.map_some, Option.getD_some]
    rw [← this]
    exact List.mem_of_find?_eq_some hf

theorem mem_others {s : Bool} {t : Node} {k : ℕ} :
    k ∈ I.others s t ↔ k ∈ livePos (I.sDom s) ∧ dval (I.sDom s) k ≠ sCoord s t.st := by
  simp [others]

private theorem sAll_spec {t : Node} :
    ∀ (xs : List (Bool × ℕ)) (e : ProofLog) (db : List (ℕ × PBConstr)),
    I.Run e db → I.NodeOk I.n db e.var t → (∀ x ∈ xs, x.2 ∈ I.others x.1 t) →
    ∃ db', I.Run (I.sAll t e xs).1 db' ∧ Sub db db' ∧ I.SlOk db' (I.sAll t e xs).2 ∧
      (I.sAll t e xs).2.map (·.1) = xs.map (fun x => (t.S, x)) ∧ (I.sAll t e xs).1.var = e.var
  | [], e, db, h, _, _ => ⟨db, h, Sub.refl _, by simp [sAll, SlOk], by simp [sAll], rfl⟩
  | (s, k) :: xs, e, db, h, ht, hxs => by
    obtain ⟨hkl, hne⟩ := I.mem_others.1 (hxs (s, k) List.mem_cons_self)
    obtain ⟨db₁, h₁, s₁, hl₁⟩ := I.sSteps_spec s h ht (mem_livePos.1 hkl).1 hne
    obtain ⟨db', h', s', hsl, hmap, hv⟩ := sAll_spec xs _ db₁ h₁
      (ht.mono I s₁ (by simp [ProofLog.push])) (fun x hx => hxs x (List.mem_cons_of_mem _ hx))
    simp only [sAll]
    refine ⟨db', h', s₁.trans s', ?_, by simp [hmap], by rw [hv]; simp [ProofLog.push]⟩
    simp only [SlOk, List.mem_cons, forall_eq_or_imp]
    exact ⟨s' _ _ hl₁, hsl⟩

private theorem sLayer_spec : ∀ (ts : List Node) (e : ProofLog) (db : List (ℕ × PBConstr)),
    I.Run e db → (∀ t ∈ ts, I.NodeOk I.n db e.var t) →
    ∃ db', I.Run (I.sLayer e ts).1 db' ∧ Sub db db' ∧ I.SlOk db' (I.sLayer e ts).2 ∧
      (∀ t ∈ ts, ∀ s k, k ∈ I.others s t → ∃ m, ((t.S, s, k), m) ∈ (I.sLayer e ts).2) ∧
      (I.sLayer e ts).1.var = e.var
  | [], e, db, h, _ => ⟨db, h, Sub.refl _, by simp [sLayer, SlOk], by simp, rfl⟩
  | t :: ts, e, db, h, hts => by
    have ht := hts t List.mem_cons_self
    obtain ⟨db₁, h₁, s₁, hsl₁, hmap₁, hv₁⟩ := I.sAll_spec
      ((I.others false t).map (false, ·) ++ (I.others true t).map (true, ·)) e db h ht
      (fun x hx => by
        simp only [List.mem_append, List.mem_map] at hx
        rcases hx with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;> exact hk)
    obtain ⟨db', h', s', hsl, hcov, hv⟩ := sLayer_spec ts _ db₁ h₁
      (fun u hu => by rw [hv₁]; exact (hts u (List.mem_cons_of_mem _ hu)).mono I s₁ le_rfl)
    simp only [sLayer]
    refine ⟨db', h', s₁.trans s', fun x hx => ?_, ?_, by rw [hv, hv₁]⟩
    · rcases List.mem_append.1 hx with hx | hx
      · exact s' _ _ (hsl₁ x hx)
      · exact hsl x hx
    · simp only [List.mem_cons]
      rintro u (rfl | hu) s k hk
      · have : (u.S, s, k) ∈ (I.sAll u e ((I.others false u).map (false, ·) ++
            (I.others true u).map (true, ·))).2.map (·.1) := by
          rw [hmap₁]
          cases s <;> simp [hk]
        obtain ⟨y, hy, hy1⟩ := List.mem_map.1 this
        exact ⟨y.2, List.mem_append_left _ (by rw [← hy1]; exact hy)⟩
      · obtain ⟨m, hm⟩ := hcov u hu s k hk
        exact ⟨m, List.mem_append_right _ hm⟩

/-! ### The backward pass -/

/-- The refutations `dl` are in the database. -/
def DeadOk (db : List (ℕ × PBConstr)) (dl : List (ℕ × ℕ)) : Prop :=
  ∀ x ∈ dl, lookup db x.2 = some (I.deadClause x.1).normalize

theorem DeadOk.mono {db db' : List (ℕ × PBConstr)} {dl : List (ℕ × ℕ)}
    (h : I.DeadOk db dl) (hs : Sub db db') : I.DeadOk db' dl := fun x hx => hs _ _ (h x hx)

theorem dlook_mem {dl : List (ℕ × ℕ)} {S : ℕ} (h : ∃ k, (S, k) ∈ dl) :
    (S, dlook dl S) ∈ dl := by
  obtain ⟨k, hk⟩ := h
  rcases hf : dl.find? (·.1 == S) with _ | x
  · exact absurd (List.find?_eq_none.1 hf _ hk) (by simp)
  · have := List.find?_some hf
    simp only [beq_iff_eq] at this
    simp only [dlook, hf, Option.map_some, Option.getD_some]
    rw [← this]
    exact List.mem_of_find?_eq_some hf

theorem negate_deadClause (S : ℕ) :
    (I.negD ++ [(S, false)]).map Std.Sat.Literal.negate ++ [] = I.antecedent ++ [(S, true)] := by
  simp [List.map_append, negate_negD, Std.Sat.Literal.negate]

theorem holds_deadClause {σ : ℕ → Bool} (hD : Consistent σ I.antecedent) {S : ℕ}
    (h : (I.deadClause S).normalize.Holds σ) : σ S = false := by
  rw [holds_normalize, deadClause, holds_clause] at h
  obtain ⟨l, hl, hev⟩ := h
  rcases List.mem_append.1 hl with hl | hl
  · simp [I.eval_negD hD l hl] at hev
  · simp only [List.mem_singleton] at hl; subst hl; simpa using hev

theorem consistent_ante {σ : ℕ → Bool} {K : List (Literal ℕ)}
    (h : Consistent σ (I.antecedent ++ K)) : Consistent σ I.antecedent := (consistent_append.1 h).1

theorem mem_antecedent_sum (s : Bool) {k : ℕ} (hk : k < (I.sDom s).length)
    (hl : dlive (I.sDom s) k = false) : (I.sBase s + k, false) ∈ I.antecedent := by
  cases s
  · simp only [sDom, sBase, Bool.false_eq_true, ↓reduceIte] at hk hl ⊢
    simp only [antecedent, List.mem_append, List.mem_filterMap, List.mem_range]
    exact .inl (.inr ⟨k, hk, by simp [hl]⟩)
  · simp only [sDom, sBase, ↓reduceIte] at hk hl ⊢
    simp only [antecedent, List.mem_append, List.mem_filterMap, List.mem_range]
    exact .inr ⟨k, hk, by simp [hl]⟩

theorem mem_antecedent_item {j k : ℕ} (hj : j < I.n) (hk : k < I.len j)
    (hl : dlive (I.dom j) k = false) : (I.var j k, false) ∈ I.antecedent := by
  simp only [antecedent, List.mem_append, List.mem_flatMap, List.mem_filterMap, List.mem_range]
  exact .inl (.inl ⟨j, hj, k, hk, by simp [hl]⟩)

theorem deadSum_spec {st : St} (h : I.feasible st = false) :
    ∀ k ∈ livePos (I.sDom (I.deadSum st)), dval (I.sDom (I.deadSum st)) k ≠
      sCoord (I.deadSum st) st := by
  intro k hk
  cases hd : I.deadSum st
  · rw [hd] at hk
    simp only [deadSum, List.any_eq_false, beq_iff_eq] at hd
    exact hd k hk
  · rw [hd] at hk
    have hd' : (livePos I.wDom).any (fun k => dval I.wDom k == st.1) = true := hd
    simp only [feasible, hd', Bool.true_and, List.any_eq_false, beq_iff_eq] at h
    exact h k hk

/-- **The refutations of the infeasible states of the last layer run**, from their clauses
`S_t ⇒ [s ≠ u]` and the at-least-one constraint of the sum. -/
private theorem deadFinal_spec {sl : List ((ℕ × Bool × ℕ) × ℕ)} :
    ∀ (ts : List Node) (e : ProofLog) (db : List (ℕ × PBConstr)),
    I.Run e db → (∀ t ∈ ts, I.NodeOk I.n db e.var t) → I.SlOk db sl →
    (∀ t ∈ ts, ∀ s k, k ∈ I.others s t → ∃ m, ((t.S, s, k), m) ∈ sl) →
    ∃ db', I.Run (I.deadFinal sl e ts).1 db' ∧ Sub db db' ∧
      I.DeadOk db' (I.deadFinal sl e ts).2 ∧
      (∀ t ∈ ts, I.feasible t.st = false → ∃ k, (t.S, k) ∈ (I.deadFinal sl e ts).2) ∧
      (I.deadFinal sl e ts).1.var = e.var
  | [], e, db, h, _, _, _ => ⟨db, h, Sub.refl _, by simp [deadFinal, DeadOk], by simp, rfl⟩
  | t :: ts, e, db, h, hts, hsl, hcov => by
    have ht := hts t List.mem_cons_self
    by_cases hf : I.feasible t.st = true
    · obtain ⟨db', h', s', hd', hall, hv⟩ := deadFinal_spec ts e db h
        (fun u hu => hts u (List.mem_cons_of_mem _ hu)) hsl
        (fun u hu => hcov u (List.mem_cons_of_mem _ hu))
      refine ⟨db', by simpa [deadFinal, hf] using h', s', by simpa [deadFinal, hf] using hd', ?_,
        by simpa [deadFinal, hf] using hv⟩
      simp only [deadFinal, hf, ↓reduceIte, List.mem_cons]
      rintro u (rfl | hu) hu'
      · simp [hf] at hu'
      · exact hall u hu hu'
    · have hfF : I.feasible t.st = false := by simpa using hf
      set s := I.deadSum t.st with hs
      have hr : rup db (I.deadClause t.S) (.neg :: (I.others s t).map
          (fun k => .id (slook sl (t.S, s, k))) ++ [.id (sAlo s)]) = true := by
        refine rup_clause ?_
        rw [negate_deadClause]
        have := RupOk.imps (db := db) (neg := (I.deadClause t.S).negate)
          (K₀ := I.antecedent ++ [(t.S, true)]) (rest := [.id (sAlo s)])
          ((I.others s t).map fun k => (Hint.id (slook sl (t.S, s, k)), (I.sBase s + k, false)))
          _ (fun l hl => hl) ?_ ?_
        · rw [List.map_map] at this; exact this
        · intro y hy
          obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
          have hm := slook_mem (hcov t List.mem_cons_self s k hk)
          refine ⟨_, hsl _ hm, nodup_termVar_normalize _, fun σ hσ hc => ?_⟩
          rw [holds_normalize, holds_clause] at hc
          have hS := lit_of hσ (v := t.S) (b := true) (by simp)
          obtain ⟨l, hl, hev⟩ := hc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
          rcases hl with rfl | rfl
          · simp [hS] at hev
          · simpa using hev
        · refine Knapsack.Inst.RupOk.id_conflict (I.lookup_sums h s).2.2.1
            (nodup_termVar_normalize _) fun σ hσ hc => ?_
          rw [holds_normalize, holds_alo] at hc
          obtain ⟨k, hk, hσk⟩ := hc
          by_cases hl : dlive (I.sDom s) k = true
          · have hkl : k ∈ livePos (I.sDom s) := mem_livePos.2 ⟨hk, hl⟩
            have hko : k ∈ I.others s t := I.mem_others.2 ⟨hkl, I.deadSum_spec hfF k hkl⟩
            have := lit_of hσ (v := I.sBase s + k) (b := false) (by
              simp only [List.map_map, List.mem_append, List.mem_map]
              exact .inl ⟨k, hko, rfl⟩)
            simp [this] at hσk
          · have := lit_of hσ (v := I.sBase s + k) (b := false)
              (List.mem_append_right _ (List.mem_append_left _
                (I.mem_antecedent_sum s hk (by simpa using hl))))
            simp [this] at hσk
      obtain ⟨h₁, s₁⟩ := Run.rup I h hr (fun v hv => by
        obtain ⟨l, hl, rfl⟩ := vars_clause hv
        rcases List.mem_append.1 hl with hl | hl
        · have := I.vars_negD hl; have := h.2.2.2.1; omega
        · simp only [List.mem_singleton] at hl; subst hl; exact I.nodeSteps_vars ht)
      obtain ⟨db', h', s', hd', hall, hv⟩ := deadFinal_spec ts _ _ h₁
        (fun u hu => (hts u (List.mem_cons_of_mem _ hu)).mono I s₁ (by simp [ProofLog.push]))
        (hsl.mono I s₁) (fun u hu => hcov u (List.mem_cons_of_mem _ hu))
      refine ⟨db', by simpa [deadFinal, hfF, hs] using h', s₁.trans s', ?_, ?_, ?_⟩
      · simp only [deadFinal, hfF, Bool.false_eq_true, ↓reduceIte, DeadOk, List.mem_cons,
          forall_eq_or_imp]
        exact ⟨s' _ _ ((lookup_cons _ _ _ _).trans (ite_eq_left rfl)), hd'⟩
      · intro u hu hu'
        simp only [deadFinal, hfF, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
        rcases List.mem_cons.1 hu with rfl | hu
        · exact ⟨_, .inl rfl⟩
        · obtain ⟨k, hk⟩ := hall u hu hu'
          exact ⟨k, .inr hk⟩
      · simp only [deadFinal, hfF, Bool.false_eq_true, ↓reduceIte]
        simpa [ProofLog.push] using hv

/-- **The refutations of an earlier layer run**: a state all of whose targets are refuted is
refuted by RUP. -/
theorem deadLayer_spec {i : ℕ} (hi : i < I.n) {A : List St} {dl : List (ℕ × ℕ)}
    {L' : List Node} : ∀ (os : List Out) (e : ProofLog) (db : List (ℕ × PBConstr)), I.Run e db →
    (∀ o ∈ os, I.OutOk i db e.var L' o) → I.DeadOk db dl →
    (∀ t ∈ L', t.st ∉ A → ∃ k, (t.S, k) ∈ dl) →
    ∃ db', I.Run (I.deadLayer i A dl e os).1 db' ∧ Sub db db' ∧
      I.DeadOk db' (I.deadLayer i A dl e os).2 ∧
      (∀ o ∈ os, ((livePos (I.dom i)).any fun k => I.succ i o.u.st k ∈ A) = false →
        ∃ k, (o.u.S, k) ∈ (I.deadLayer i A dl e os).2) ∧
      (I.deadLayer i A dl e os).1.var = e.var
  | [], e, db, h, _, _, _ => ⟨db, h, Sub.refl _, by simp [deadLayer, DeadOk], by simp, rfl⟩
  | o :: os, e, db, h, hos, hdl, hL' => by
    have ho := hos o List.mem_cons_self
    by_cases hany : ((livePos (I.dom i)).any fun k => I.succ i o.u.st k ∈ A) = true
    · obtain ⟨db', h', s', hd', hall, hv⟩ := deadLayer_spec hi os e db h
        (fun u hu => hos u (List.mem_cons_of_mem _ hu)) hdl hL'
      refine ⟨db', by simpa [deadLayer, hany] using h', s', by simpa [deadLayer, hany] using hd',
        ?_, by simpa [deadLayer, hany] using hv⟩
      simp only [deadLayer, hany, ↓reduceIte, List.mem_cons]
      rintro u (rfl | hu) hu'
      · simp [hany] at hu'
      · exact hall u hu hu'
    · have hany' : ((livePos (I.dom i)).any fun k => I.succ i o.u.st k ∈ A) = false := by
        simpa using hany
      have hdead : ∀ x ∈ o.tr, (x.tgt.S, dlook dl x.tgt.S) ∈ dl := by
        intro x hx
        obtain ⟨htm, hts, -, -⟩ := ho.tr x hx
        refine dlook_mem (hL' _ htm fun hA => ?_)
        have hb : x.pos ∈ livePos (I.dom i) := ho.pos ▸ List.mem_map_of_mem hx
        simp only [List.any_eq_false, decide_eq_true_eq] at hany'
        exact hany' _ hb (hts ▸ hA)
      have hr : rup db (I.deadClause o.u.S)
          (.neg :: o.tr.map (fun x => .id (dlook dl x.tgt.S)) ++ [.id o.succ]) = true := by
        refine rup_clause ?_
        rw [negate_deadClause]
        have := RupOk.imps (db := db) (neg := (I.deadClause o.u.S).negate)
          (K₀ := I.antecedent ++ [(o.u.S, true)]) (rest := [.id o.succ])
          (o.tr.map fun x => (Hint.id (dlook dl x.tgt.S), (x.tgt.S, false))) _ (fun l hl => hl)
          ?_ ?_
        · rw [List.map_map] at this; exact this
        · intro y hy
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
          refine ⟨_, hdl _ (hdead x hx), nodup_termVar_normalize _, fun σ hσ hc => ?_⟩
          have := I.holds_deadClause (I.consistent_ante hσ) hc
          simp [this]
        · refine Knapsack.Inst.RupOk.id_conflict ho.succ (nodup_termVar_normalize _)
            fun σ hσ hc => ?_
          have := I.succ_false hi (o := o)
            (K := (o.tr.map fun x => (Hint.id (dlook dl x.tgt.S), (x.tgt.S, false))).map (·.2) ++
              (I.antecedent ++ [(o.u.S, true)])) (fun l hl => by simp [hl])
            (fun x hx => by
              simp only [List.mem_append, List.mem_map]; left; exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩) hσ hc
          have h2 := lit_of hσ (v := o.u.S) (b := true) (by simp)
          simp [this] at h2
      obtain ⟨h₁, s₁⟩ := Run.rup I h hr (fun v hv => by
        obtain ⟨l, hl, rfl⟩ := vars_clause hv
        rcases List.mem_append.1 hl with hl | hl
        · have := I.vars_negD hl; have := h.2.2.2.1; omega
        · simp only [List.mem_singleton] at hl; subst hl; exact I.nodeSteps_vars ho.u)
      obtain ⟨db', h', s', hd', hall, hv⟩ := deadLayer_spec hi os _ _ h₁
        (fun u hu => (hos u (List.mem_cons_of_mem _ hu)).mono I s₁ (by simp [ProofLog.push]))
        (hdl.mono I s₁) hL'
      refine ⟨db', by simpa [deadLayer, hany'] using h', s₁.trans s', ?_, ?_, ?_⟩
      · simp only [deadLayer, hany', Bool.false_eq_true, ↓reduceIte, DeadOk, List.mem_cons,
          forall_eq_or_imp]
        exact ⟨s' _ _ ((lookup_cons _ _ _ _).trans (ite_eq_left rfl)), hd'⟩
      · intro u hu hu'
        simp only [deadLayer, hany', Bool.false_eq_true, ↓reduceIte, List.mem_cons]
        rcases List.mem_cons.1 hu with rfl | hu
        · exact ⟨_, .inl rfl⟩
        · obtain ⟨k, hk⟩ := hall u hu hu'
          exact ⟨k, .inr hk⟩
      · simp only [deadLayer, hany', Bool.false_eq_true, ↓reduceIte]
        simpa [ProofLog.push] using hv

theorem alive_lt {i : ℕ} (hi : i < I.n) :
    I.alive i = (I.lay i).filter fun st =>
      (livePos (I.dom i)).any fun k => I.succ i st k ∈ I.alive (i + 1) := by
  simp only [alive]
  rw [show I.n - i = (I.n - (i + 1)) + 1 by omega]
  rfl

theorem alive_n : I.alive I.n = (I.lay I.n).filter I.feasible := by
  simp [alive, aliveAt]

/-- What the backward pass returns for a layer `r` before the last: its facts, the alive states
and the refutations of the layer `next` after it. -/
structure BackAt (db : List (ℕ × PBConstr)) (V : ℕ) (next : List Node) (x : Back) : Prop where
  /-- The index is that of an item. -/
  lt : x.layer.i < I.n
  /-- The layer's facts. -/
  lay : I.LayOk x.layer.i db V x.layer
  /-- The transitions are out of the nodes. -/
  outs : x.layer.outs.map (·.u) = x.layer.nodes
  /-- The transitions' facts. -/
  out : ∀ o ∈ x.layer.outs, I.OutOk x.layer.i db V next o
  /-- The alive states of the next layer. -/
  alive : x.alive = I.alive (x.layer.i + 1)
  /-- The refutations are in the database. -/
  dead : I.DeadOk db x.dead
  /-- Every node of the next layer that is not alive is refuted. -/
  cover : ∀ t ∈ next, t.st ∉ x.alive → ∃ k, (t.S, k) ∈ x.dead

theorem BackAt.mono {db db' : List (ℕ × PBConstr)} {V V' : ℕ} {next : List Node}
    {x : Back} (h : I.BackAt db V next x) (hs : Sub db db')
    (hV : V ≤ V') : I.BackAt db' V' next x :=
  ⟨h.lt, h.lay.mono I hs hV, h.outs, fun o ho => (h.out o ho).mono I hs hV, h.alive,
    h.dead.mono I hs, h.cover⟩

/-- **The backward pass runs.** -/
theorem backAll_spec : ∀ (rs : List Layer) (e : ProofLog) (A : List St)
    (dl : List (ℕ × ℕ)) (j : ℕ) (L' : List Node) (db : List (ℕ × PBConstr)), I.Run e db →
    I.Chain db e.var j L' rs → j ≤ I.n → A = I.alive j → I.DeadOk db dl →
    (∀ t ∈ L', t.st ∉ A → ∃ k, (t.S, k) ∈ dl) →
    ∃ db', I.Run (I.backAll e A dl rs).1 db' ∧ Sub db db' ∧
      (∀ x ∈ (I.backAll e A dl rs).2, ∃ next, I.BackAt db' e.var next x) ∧
      (I.backAll e A dl rs).2.map (·.layer) = rs ∧ (I.backAll e A dl rs).1.var = e.var
  | [], e, A, dl, j, L', db, h, _, _, _, _, _ =>
    ⟨db, h, Sub.refl _, by simp [backAll], rfl, rfl⟩
  | r :: rs, e, A, dl, j, L', db, h, ⟨hij, hlay, houts, hout, hc⟩, hj, hA, hdl, hcov => by
    have hi : r.i < I.n := by omega
    obtain ⟨db₁, h₁, s₁, hd₁, hall₁, hv₁⟩ := I.deadLayer_spec hi r.outs e db h hout hdl hcov
    set d := I.deadLayer r.i A dl e r.outs with hd
    have hA' : ((r.nodes.map (·.st)).filter fun st =>
        (livePos (I.dom r.i)).any fun k => I.succ r.i st k ∈ A) = I.alive r.i := by
      rw [I.alive_lt hi, hlay.lay, hA, hij]
    obtain ⟨db', h', s', hall, hmap, hv⟩ := backAll_spec rs d.1
      ((r.nodes.map (·.st)).filter fun st =>
        (livePos (I.dom r.i)).any fun k => I.succ r.i st k ∈ A) d.2 r.i r.nodes db₁ h₁
      (by rw [hv₁]; exact hc.mono I s₁ le_rfl) (by omega) hA' hd₁ (fun t ht hn => by
        rw [← houts] at ht
        obtain ⟨o, ho, rfl⟩ := List.mem_map.1 ht
        refine hall₁ o ho ?_
        have hst : o.u.st ∈ r.nodes.map (·.st) := by
          rw [← houts]; exact List.mem_map.2 ⟨o.u, List.mem_map.2 ⟨o, ho, rfl⟩, rfl⟩
        simpa [List.mem_filter, hst] using hn)
    refine ⟨db', h', s₁.trans s', ?_,
      by simp only [backAll, List.map_cons, List.cons.injEq, true_and]; exact hmap,
      by simp only [backAll]; exact hv.trans hv₁⟩
    simp only [backAll, List.mem_cons]
    rintro x (rfl | hx)
    · exact ⟨L', hi, hlay.mono I (s₁.trans s') le_rfl, houts,
        fun o ho => (hout o ho).mono I (s₁.trans s') le_rfl, by rw [hA, hij],
        hdl.mono I (s₁.trans s'), hcov⟩
    · obtain ⟨nx, hnx⟩ := hall x hx
      rw [hv₁] at hnx
      exact ⟨nx, hnx⟩

/-! ### The removals -/

theorem tgt_tau {o : Out} {k : ℕ} (hk : k ∈ o.tr.map (·.pos)) :
    ∃ x ∈ o.tr, x.pos = k ∧ o.tgtOf k = x.tgt ∧ o.tau k = x.id := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hk
  rcases hf : o.tr.find? (·.pos == x.pos) with _ | y
  · exact absurd (List.find?_eq_none.1 hf x hx) (by simp)
  · have := List.find?_some hf
    simp only [beq_iff_eq] at this
    exact ⟨y, List.mem_of_find?_eq_some hf, this, by simp [Out.tgtOf, hf],
      by simp [Out.tau, hf]⟩

theorem negate_remClause (i k : ℕ) :
    (I.negD ++ [(I.var i k, false)]).map Std.Sat.Literal.negate ++ [] =
      I.antecedent ++ [(I.var i k, true)] := by
  simp [List.map_append, negate_negD, Std.Sat.Literal.negate]

/-- Under the antecedent and the falsity of the states of a layer, its at-least-one constraint
fails. -/
theorem alo_conflict {L : List Node} {σ : ℕ → Bool} (hD : Consistent σ I.antecedent)
    (hL : ∀ u ∈ L, σ u.S = false) : ¬ (I.aloClause L).normalize.Holds σ := by
  intro hc
  rw [holds_normalize, aloClause, holds_clause] at hc
  obtain ⟨l, hl, hev⟩ := hc
  rcases List.mem_append.1 hl with hl | hl
  · have := I.eval_negD hD l hl
    simp [this] at hev
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hl
    simp [hL u hu] at hev

/-- **A removal of an item value runs**: if every transition by the position `k` out of layer `r`
leads to a refuted state, the refutations, the transitions and the at-least-one constraint of the
layer give `D ⇒ [xᵢ ≠ v]` by RUP. -/
theorem rup_rem {db : List (ℕ × PBConstr)} {V : ℕ} {next : List Node} {r : Layer}
    {A : List St} {dl : List (ℕ × ℕ)} (hx : I.BackAt db V next ⟨r, A, dl⟩) {k : ℕ}
    (hk : k ∈ livePos (I.dom r.i)) (hall : ∀ o ∈ r.outs, I.succ r.i o.u.st k ∉ A) :
    rup db (I.remClause r.i k) (.neg :: r.outs.map (fun o => .id (dlook dl (o.tgtOf k).S)) ++
      r.outs.map (fun o => .id (o.tau k)) ++ [.id r.alo]) = true := by
  have htr : ∀ o ∈ r.outs, ∃ y ∈ o.tr, y.pos = k ∧ o.tgtOf k = y.tgt ∧ o.tau k = y.id :=
    fun o ho => tgt_tau (by rw [(hx.out o ho).pos]; exact hk)
  have hdead : ∀ o ∈ r.outs, lookup db (dlook dl (o.tgtOf k).S) =
      some (I.deadClause (o.tgtOf k).S).normalize := by
    intro o ho
    obtain ⟨y, hy, rfl, ht, -⟩ := htr o ho
    obtain ⟨hym, hys, -, -⟩ := (hx.out o ho).tr y hy
    rw [ht]
    exact hx.dead _ (dlook_mem (hx.cover _ hym (by rw [hys]; exact hall o ho)))
  rw [show ∀ a b c : List Hint, (Hint.neg :: a) ++ b ++ c = .neg :: (a ++ (b ++ c)) from
    fun a b c => by simp]
  refine rup_clause ?_
  rw [negate_remClause]
  have h1 := RupOk.imps (db := db) (neg := (I.remClause r.i k).negate)
    (K₀ := I.antecedent ++ [(I.var r.i k, true)])
    (rest := r.outs.map (fun o => .id (o.tau k)) ++ [.id r.alo])
    (r.outs.map fun o => (Hint.id (dlook dl (o.tgtOf k).S), ((o.tgtOf k).S, false))) _
    (fun l hl => hl) ?_ ?_
  · rw [List.map_map] at h1; exact h1
  · intro y hy
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hy
    refine ⟨_, hdead o ho, nodup_termVar_normalize _, fun σ hσ hc => ?_⟩
    have := I.holds_deadClause (I.consistent_ante hσ) hc
    simp [this]
  have h2 := RupOk.imps (db := db) (neg := (I.remClause r.i k).negate)
    (K₀ := (r.outs.map fun o => (Hint.id (dlook dl (o.tgtOf k).S), ((o.tgtOf k).S, false))).map
      (·.2) ++ (I.antecedent ++ [(I.var r.i k, true)])) (rest := [.id r.alo])
    (r.outs.map fun o => (Hint.id (o.tau k), (o.u.S, false))) _ (fun l hl => hl) ?_ ?_
  · rw [List.map_map] at h2; exact h2
  · intro y hy
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hy
    obtain ⟨z, hz, hzk, ht, hτ⟩ := htr o ho
    obtain ⟨-, -, -, hzl⟩ := (hx.out o ho).tr z hz
    refine ⟨_, by rw [hτ]; exact hzl, nodup_termVar_normalize _, fun σ hσ hc => ?_⟩
    rw [hzk] at hc
    have h3 := lit_of hσ (v := (o.tgtOf k).S) (b := false)
      (by simp only [List.mem_append, List.mem_map]; left; exact ⟨_, ⟨o, ho, rfl⟩, rfl⟩)
    rw [ht] at h3
    have h4 := lit_of hσ (v := I.var r.i k) (b := true) (by simp)
    cases hu : σ o.u.S
    · simp [hu]
    · simp [I.holds_trClause.1 hc hu h4] at h3
  · refine Knapsack.Inst.RupOk.id_conflict hx.lay.alo (nodup_termVar_normalize _)
      fun σ hσ hc => I.alo_conflict (fun m hm => hσ m (by simp [hm])) (fun u hu => ?_) hc
    rw [← hx.outs] at hu
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hu
    exact lit_of hσ (v := o.u.S) (b := false)
      (by simp only [List.mem_append, List.mem_map]; left; exact ⟨_, ⟨o, ho, rfl⟩, rfl⟩)

private theorem remLayer_spec {next : List Node} {r : Layer} {A : List St}
    {dl : List (ℕ × ℕ)} : ∀ (ks : List ℕ) (e : ProofLog) (db : List (ℕ × PBConstr)),
    I.Run e db → I.BackAt db e.var next ⟨r, A, dl⟩ → (∀ k ∈ ks, k ∈ livePos (I.dom r.i)) →
    ∃ db', I.Run (I.remLayer r A dl e ks).1 db' ∧ Sub db db' ∧
      (∀ y ∈ (I.remLayer r A dl e ks).2, y.1.1 = r.i ∧ y.1.2 ∈ ks ∧
        lookup db' y.2 = some (I.remClause r.i y.1.2).normalize) ∧
      (∀ k ∈ ks, (r.outs.all fun o => I.succ r.i o.u.st k ∉ A) = true →
        ∃ m, ((r.i, k), m) ∈ (I.remLayer r A dl e ks).2) ∧
      (I.remLayer r A dl e ks).1.var = e.var
  | [], e, db, h, _, _ => ⟨db, h, Sub.refl _, by simp [remLayer], by simp, rfl⟩
  | k :: ks, e, db, h, hx, hks => by
    by_cases hall : (r.outs.all fun o => I.succ r.i o.u.st k ∉ A) = true
    · have hr := I.rup_rem hx (hks k List.mem_cons_self) (by simpa using hall)
      obtain ⟨h₁, s₁⟩ := Run.rup I h hr (fun v hv => by
        obtain ⟨l, hl, rfl⟩ := vars_clause hv
        rcases List.mem_append.1 hl with hl | hl
        · have := I.vars_negD hl; have := h.2.2.2.1; omega
        · simp only [List.mem_singleton] at hl; subst hl
          have := I.var_lt (i := I.n) hx.lt (mem_livePos.1 (hks k List.mem_cons_self)).1
          have := I.wBase_le_M
          have := h.2.2.2.1; simp only [wBase] at *; omega)
      obtain ⟨db', h', s', hys, hcov, hv⟩ := remLayer_spec ks _ _ h₁
        (hx.mono I s₁ (by simp [ProofLog.push])) (fun k hk => hks k (List.mem_cons_of_mem _ hk))
      simp only [remLayer, hall, ↓reduceIte]
      refine ⟨db', h', s₁.trans s', ?_, ?_, by simpa [ProofLog.push] using hv⟩
      · simp only [List.mem_cons, forall_eq_or_imp]
        refine ⟨⟨by simp, by simp, s' _ _ ((lookup_cons _ _ _ _).trans (ite_eq_left rfl))⟩,
          fun y hy => ?_⟩
        obtain ⟨h1, h2, h3⟩ := hys y hy
        exact ⟨h1, .inr h2, h3⟩
      · simp only [List.mem_cons]
        rintro k' (rfl | hk') hk''
        · exact ⟨_, .inl rfl⟩
        · obtain ⟨m, hm⟩ := hcov k' hk' hk''
          exact ⟨m, .inr hm⟩
    · obtain ⟨db', h', s', hys, hcov, hv⟩ := remLayer_spec ks e db h hx
        (fun k hk => hks k (List.mem_cons_of_mem _ hk))
      simp only [remLayer, hall, Bool.false_eq_true, ↓reduceIte]
      refine ⟨db', h', s', ?_, ?_, hv⟩
      · intro y hy
        obtain ⟨h1, h2, h3⟩ := hys y hy
        exact ⟨h1, List.mem_cons_of_mem _ h2, h3⟩
      · simp only [List.mem_cons]
        rintro k' (rfl | hk') hk''
        · exact absurd hk'' hall
        · exact hcov k' hk' hk''

private theorem remAll_spec : ∀ (xs : List Back) (e : ProofLog)
    (db : List (ℕ × PBConstr)), I.Run e db → (∀ x ∈ xs, ∃ next, I.BackAt db e.var next x) →
    ∃ db', I.Run (I.remAll e xs).1 db' ∧ Sub db db' ∧
      (∀ y ∈ (I.remAll e xs).2, y.1.2 ∈ livePos (I.dom y.1.1) ∧ y.1.1 < I.n ∧
        lookup db' y.2 = some (I.remClause y.1.1 y.1.2).normalize) ∧
      (∀ x ∈ xs, ∀ k ∈ livePos (I.dom x.layer.i),
        (x.layer.outs.all fun o => I.succ x.layer.i o.u.st k ∉ x.alive) = true →
        ∃ m, ((x.layer.i, k), m) ∈ (I.remAll e xs).2) ∧ (I.remAll e xs).1.var = e.var
  | [], e, db, h, _ => ⟨db, h, Sub.refl _, by simp [remAll], by simp, rfl⟩
  | x :: xs, e, db, h, hxs => by
    obtain ⟨nx, hx⟩ := hxs x List.mem_cons_self
    obtain ⟨db₁, h₁, s₁, hys₁, hcov₁, hv₁⟩ := I.remLayer_spec (r := x.layer) (A := x.alive)
      (dl := x.dead) (livePos (I.dom x.layer.i)) e db h hx (fun k hk => hk)
    obtain ⟨db', h', s', hys, hcov, hv⟩ := remAll_spec xs _ db₁ h₁ (fun y hy => by
      obtain ⟨n', hn'⟩ := hxs y (List.mem_cons_of_mem _ hy)
      rw [hv₁]
      exact ⟨n', hn'.mono I s₁ le_rfl⟩)
    refine ⟨db', h', s₁.trans s', ?_, ?_, by simp only [remAll]; rw [hv, hv₁]⟩
    · simp only [remAll, List.mem_append]
      rintro y (hy | hy)
      · obtain ⟨h1, h2, h3⟩ := hys₁ y hy
        exact ⟨h1 ▸ h2, h1 ▸ hx.lt, h1 ▸ s' _ _ h3⟩
      · exact hys y hy
    · simp only [remAll, List.mem_cons, List.mem_append]
      rintro y (rfl | hy) k hk hall
      · obtain ⟨m, hm⟩ := hcov₁ k hk hall
        exact ⟨m, .inl hm⟩
      · obtain ⟨m, hm⟩ := hcov y hy k hk hall
        exact ⟨m, .inr hm⟩

theorem negate_remSClause (s : Bool) (k : ℕ) :
    (I.negD ++ [(I.sBase s + k, false)]).map Std.Sat.Literal.negate ++ [] =
      I.antecedent ++ [(I.sBase s + k, true)] := by
  simp [List.map_append, negate_negD, Std.Sat.Literal.negate]

/-- **The removals of the values of the sum `s` run.** -/
private theorem remSum_spec (s : Bool) {L : List Node} {sl : List ((ℕ × Bool × ℕ) × ℕ)}
    {dl : List (ℕ × ℕ)} {a : ℕ} : ∀ (ks : List ℕ) (e : ProofLog) (db : List (ℕ × PBConstr)),
    I.Run e db → I.SlOk db sl → I.DeadOk db dl →
    lookup db a = some (I.aloClause L).normalize →
    (∀ t ∈ L, ∀ s k, k ∈ I.others s t → ∃ m, ((t.S, s, k), m) ∈ sl) →
    (∀ t ∈ L, I.feasible t.st = false → ∃ m, (t.S, m) ∈ dl) →
    (∀ k ∈ ks, k ∈ livePos (I.sDom s)) →
    ∃ db', I.Run (I.remSum s L sl dl a e ks).1 db' ∧ Sub db db' ∧
      (∀ y ∈ (I.remSum s L sl dl a e ks).2, y.1 ∈ ks ∧
        lookup db' y.2 = some (I.remSClause s y.1).normalize) ∧
      (∀ k ∈ ks, (L.all fun t => !(I.feasible t.st && sCoord s t.st == dval (I.sDom s) k)) =
        true → ∃ m, (k, m) ∈ (I.remSum s L sl dl a e ks).2) ∧
      (I.remSum s L sl dl a e ks).1.var = e.var
  | [], e, db, h, _, _, _, _, _, _ => ⟨db, h, Sub.refl _, by simp [remSum], by simp, rfl⟩
  | k :: ks, e, db, h, hsl, hdl, ha, hcov, hdc, hks => by
    have hk := hks k List.mem_cons_self
    by_cases hall : (L.all fun t => !(I.feasible t.st && sCoord s t.st == dval (I.sDom s) k)) =
      true
    · have hr : rup db (I.remSClause s k) (.neg :: L.map (fun t => .id (if I.feasible t.st
          then slook sl (t.S, s, k) else dlook dl t.S)) ++ [.id a]) = true := by
        refine rup_clause ?_
        rw [negate_remSClause]
        have := RupOk.imps (db := db) (neg := (I.remSClause s k).negate)
          (K₀ := I.antecedent ++ [(I.sBase s + k, true)]) (rest := [.id a])
          (L.map fun t => (Hint.id (if I.feasible t.st then slook sl (t.S, s, k)
            else dlook dl t.S), (t.S, false))) _ (fun l hl => hl) ?_ ?_
        · rw [List.map_map] at this; exact this
        · intro y hy
          obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hy
          by_cases hf : I.feasible t.st = true
          · simp only [hf, ↓reduceIte]
            have hne : dval (I.sDom s) k ≠ sCoord s t.st := by
              have := List.all_eq_true.1 hall t ht
              simp only [hf, Bool.true_and, Bool.not_eq_true', beq_eq_false_iff_ne] at this
              exact Ne.symm this
            have hm := slook_mem (hcov t ht s k (I.mem_others.2 ⟨hk, hne⟩))
            refine ⟨_, hsl _ hm, nodup_termVar_normalize _, fun σ hσ hc => ?_⟩
            rw [holds_normalize, holds_clause] at hc
            have hS := lit_of hσ (v := I.sBase s + k) (b := true) (by simp)
            obtain ⟨l, hl, hev⟩ := hc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
            rcases hl with rfl | rfl
            · simpa using hev
            · simp [hS] at hev
          · have hfF : I.feasible t.st = false := by simpa using hf
            simp only [hfF, Bool.false_eq_true, ↓reduceIte]
            refine ⟨_, hdl _ (dlook_mem (hdc t ht hfF)), nodup_termVar_normalize _,
              fun σ hσ hc => ?_⟩
            have := I.holds_deadClause (I.consistent_ante hσ) hc
            simp [this]
        · refine Knapsack.Inst.RupOk.id_conflict ha (nodup_termVar_normalize _)
            fun σ hσ hc => I.alo_conflict (fun m hm => hσ m (by simp [hm])) (fun t ht => ?_) hc
          exact lit_of hσ (v := t.S) (b := false)
            (by simp only [List.map_map, List.mem_append, List.mem_map]; exact .inl ⟨t, ht, rfl⟩)
      obtain ⟨h₁, s₁⟩ := Run.rup I h hr (fun v hv => by
        obtain ⟨l, hl, rfl⟩ := vars_clause hv
        rcases List.mem_append.1 hl with hl | hl
        · have := I.vars_negD hl; have := h.2.2.2.1; omega
        · simp only [List.mem_singleton] at hl; subst hl
          have := I.sBase_add_le_M s
          have := (mem_livePos.1 hk).1
          have := h.2.2.2.1; simp only; omega)
      obtain ⟨db', h', s', hys, hcv, hv⟩ := remSum_spec s ks _ _ h₁ (hsl.mono I s₁)
        (hdl.mono I s₁) (s₁ _ _ ha) hcov hdc (fun k hk => hks k (List.mem_cons_of_mem _ hk))
      simp only [remSum, hall, ↓reduceIte]
      refine ⟨db', h', s₁.trans s', ?_, ?_, by simpa [ProofLog.push] using hv⟩
      · simp only [List.mem_cons, forall_eq_or_imp]
        refine ⟨⟨by simp, s' _ _ ((lookup_cons _ _ _ _).trans (ite_eq_left rfl))⟩, fun y hy => ?_⟩
        obtain ⟨h1, h2⟩ := hys y hy
        exact ⟨.inr h1, h2⟩
      · simp only [List.mem_cons]
        rintro k' (rfl | hk') hk''
        · exact ⟨_, .inl rfl⟩
        · obtain ⟨m, hm⟩ := hcv k' hk' hk''
          exact ⟨m, .inr hm⟩
    · obtain ⟨db', h', s', hys, hcv, hv⟩ := remSum_spec s ks e db h hsl hdl ha hcov hdc
        (fun k hk => hks k (List.mem_cons_of_mem _ hk))
      simp only [remSum, hall, Bool.false_eq_true, ↓reduceIte]
      refine ⟨db', h', s', ?_, ?_, hv⟩
      · intro y hy
        obtain ⟨h1, h2⟩ := hys y hy
        exact ⟨List.mem_cons_of_mem _ h1, h2⟩
      · simp only [List.mem_cons]
        rintro k' (rfl | hk') hk''
        · exact absurd hk'' hall
        · exact hcv k' hk' hk''

/-! ### The whole proof -/

theorem remSum_cover {s : Bool} {L : List Node} {k : ℕ} (hL : L.map (·.st) = I.lay I.n)
    (h : ∀ st ∈ I.lay I.n, ¬ (I.feasible st = true ∧ sCoord s st = dval (I.sDom s) k)) :
    (L.all fun t => !(I.feasible t.st && sCoord s t.st == dval (I.sDom s) k)) = true := by
  simp only [List.all_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne]
  intro t ht
  have := h t.st (by rw [← hL]; exact List.mem_map_of_mem ht)
  by_cases hf : I.feasible t.st = true
  · exact .inr fun he => this ⟨hf, he⟩
  · exact .inl (by simpa using hf)

/-- **The whole proof runs**, and derives the removal clause of every removed value; every value
of a current domain without support in the diagram is removed. -/
private theorem emit_spec : ∃ db, I.Run I.emit.acc db ∧
    (∀ y ∈ I.emit.items, y.1.2 ∈ livePos (I.dom y.1.1) ∧ y.1.1 < I.n ∧
      lookup db y.2 = some (I.remClause y.1.1 y.1.2).normalize) ∧
    (∀ j < I.n, ∀ k ∈ livePos (I.dom j), (∀ st ∈ I.lay j, I.succ j st k ∉ I.alive (j + 1)) →
      ∃ m, ((j, k), m) ∈ I.emit.items) ∧
    (∀ s : Bool, ∀ y ∈ (if s then I.emit.ps else I.emit.ws), y.1 ∈ livePos (I.sDom s) ∧
      lookup db y.2 = some (I.remSClause s y.1).normalize) ∧
    (∀ s : Bool, ∀ k ∈ livePos (I.sDom s),
      (∀ st ∈ I.lay I.n, ¬ (I.feasible st = true ∧ sCoord s st = dval (I.sDom s) k)) →
      ∃ m, (k, m) ∈ (if s then I.emit.ps else I.emit.ws)) := by
  obtain ⟨db₂, h₂, rn, rs, hf, hrn, hc, hidx⟩ := I.forward_spec
  set f := I.forward with hfdef
  obtain ⟨db₃, h₃, s₃, hsl₃, hcov₃, hv₃⟩ := I.sLayer_spec rn.nodes f.1 db₂ h₂ hrn.nodes
  set sp := I.sLayer f.1 rn.nodes with hsp
  obtain ⟨db₄, h₄, s₄, hd₄, hall₄, hv₄⟩ := I.deadFinal_spec (sl := sp.2) rn.nodes sp.1 db₃ h₃
    (fun t ht => by rw [hv₃]; exact (hrn.nodes t ht).mono I s₃ le_rfl) hsl₃ hcov₃
  set dp := I.deadFinal sp.2 sp.1 rn.nodes with hdp
  have hA : (rn.nodes.map (·.st)).filter I.feasible = I.alive I.n := by rw [alive_n, hrn.lay]
  obtain ⟨db₅, h₅, s₅, hall₅, hmap₅, hv₅⟩ := I.backAll_spec rs dp.1
    ((rn.nodes.map (·.st)).filter I.feasible) dp.2 I.n rn.nodes db₄ h₄
    (by rw [hv₄, hv₃]; exact hc.mono I (s₃.trans s₄) le_rfl) le_rfl hA hd₄
    (fun t ht hn => hall₄ t ht (by
      have : t.st ∈ rn.nodes.map (·.st) := List.mem_map_of_mem ht
      simpa [List.mem_filter, this] using hn))
  set bp := I.backAll dp.1 ((rn.nodes.map (·.st)).filter I.feasible) dp.2 rs with hbp
  obtain ⟨db₆, h₆, s₆, hys₆, hcov₆, hv₆⟩ := I.remAll_spec _ _ db₅ h₅ (fun x hx => by
    rw [hv₅]; exact hall₅ x hx)
  set rp := I.remAll bp.1 bp.2 with hrp
  have hs₆ := s₄.trans (s₅.trans s₆)
  obtain ⟨db₇, h₇, s₇, hys₇, hcov₇, -⟩ := I.remSum_spec false (L := rn.nodes) (sl := sp.2)
    (dl := dp.2) (a := rn.alo) (livePos I.wDom) rp.1 db₆ h₆ (hsl₃.mono I hs₆)
    (hd₄.mono I (s₅.trans s₆)) (s₃.trans hs₆ _ _ hrn.alo) hcov₃ hall₄ (fun k hk => hk)
  set rw' := I.remSum false rn.nodes sp.2 dp.2 rn.alo rp.1 (livePos I.wDom) with hrw
  obtain ⟨db₈, h₈, s₈, hys₈, hcov₈, -⟩ := I.remSum_spec true (L := rn.nodes) (sl := sp.2)
    (dl := dp.2) (a := rn.alo) (livePos I.pDom) rw'.1 db₇ h₇ (hsl₃.mono I (hs₆.trans s₇))
    (hd₄.mono I (s₅.trans (s₆.trans s₇))) (s₃.trans (hs₆.trans s₇) _ _ hrn.alo) hcov₃ hall₄
    (fun k hk => hk)
  have he : I.emit = ⟨(I.remSum true rn.nodes sp.2 dp.2 rn.alo rw'.1 (livePos I.pDom)).1,
      rp.2, rw'.2, (I.remSum true rn.nodes sp.2 dp.2 rn.alo rw'.1 (livePos I.pDom)).2⟩ := by
    simp only [emit]
    rw [← hfdef, hf]
    rfl
  rw [he]
  refine ⟨db₈, h₈, fun y hy => ?_, fun j hj k hk hall => ?_, fun s => ?_, fun s => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hys₆ y hy
    exact ⟨h1, h2, s₇.trans s₈ _ _ h3⟩
  · have hjr : j ∈ rs.map (·.i) := by rw [hidx]; simpa using hj
    rw [← hmap₅, List.map_map] at hjr
    obtain ⟨x, hx, hxj⟩ := List.mem_map.1 hjr
    simp only [Function.comp_apply] at hxj
    obtain ⟨nx, hnx⟩ := hall₅ x hx
    refine hcov₆ x hx k (hxj ▸ hk) ?_ |>.imp fun m hm => hxj ▸ hm
    simp only [List.all_eq_true, decide_eq_true_eq]
    intro o ho
    have hu : o.u ∈ x.layer.nodes := by rw [← hnx.outs]; exact List.mem_map_of_mem ho
    have hst : o.u.st ∈ I.lay x.layer.i := by rw [← hnx.lay.lay]; exact List.mem_map_of_mem hu
    rw [hnx.alive, hxj]
    exact hall _ (hxj ▸ hst)
  · cases s
    · intro y hy
      obtain ⟨h1, h2⟩ := hys₇ y hy
      exact ⟨h1, s₈ _ _ h2⟩
    · exact hys₈
  · intro k hk hall
    have hcv := I.remSum_cover hrn.lay hall
    cases s
    · exact hcov₇ k hk hcv
    · exact hcov₈ k hk hcv

/-- **The checker accepts the propagator's proof**, with the direct literals preserved. -/
public theorem checkRed_propagate :
    checkRed I.formula none I.propagate.proof (some I.pres) = true := by
  obtain ⟨db, h, -⟩ := I.emit_spec
  have h1 := h.1
  simp [checkRed, propagate, h1, checkConclusion]

/-! ### The dynamic program is exact -/

/-- `∑_{j<i} a j (c j)`, the sum of a choice `c` of positions over the first `i` items. -/
def pre (a : ℕ → ℕ → ℕ) (c : ℕ → ℕ) (i : ℕ) : ℕ := ((List.range i).map fun j => a j (c j)).sum

/-- `∑_{i ≤ j < m} a j (c j)`. -/
def sfx (a : ℕ → ℕ → ℕ) (c : ℕ → ℕ) (i m : ℕ) : ℕ :=
  ((List.range' i (m - i)).map fun j => a j (c j)).sum

/-- The state of a choice after the first `i` items. -/
def stC (c : ℕ → ℕ) (i : ℕ) : St := (pre I.cw c i, pre I.cp c i)

/-- The last state reached from the state `st` of layer `i` along the choice `c`. -/
def finC (c : ℕ → ℕ) (i : ℕ) (st : St) : St := (st.1 + sfx I.cw c i I.n, st.2 + sfx I.cp c i I.n)

/-- The choice `c` picks positions of the current domains for the items `i ≤ j < m`. -/
def Allowed (c : ℕ → ℕ) (i m : ℕ) : Prop := ∀ j, i ≤ j → j < m → c j ∈ livePos (I.dom j)

theorem pre_succ (a : ℕ → ℕ → ℕ) (c : ℕ → ℕ) (i : ℕ) : pre a c (i + 1) = pre a c i + a i (c i) := by
  simp [pre, List.range_succ]

theorem pre_congr {c d : ℕ → ℕ} {i : ℕ} (h : ∀ j < i, c j = d j) (a : ℕ → ℕ → ℕ) :
    pre a c i = pre a d i := by
  simp only [pre]
  congr 1
  exact List.map_congr_left fun j hj => by rw [h j (List.mem_range.1 hj)]

theorem sfx_congr {c d : ℕ → ℕ} {i m : ℕ} (h : ∀ j, i ≤ j → j < m → c j = d j)
    (a : ℕ → ℕ → ℕ) : sfx a c i m = sfx a d i m := by
  simp only [sfx]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range'_1] at hj
  rw [h j hj.1 (by omega)]

theorem sfx_cons {a : ℕ → ℕ → ℕ} {c : ℕ → ℕ} {i m : ℕ} (h : i < m) :
    sfx a c i m = a i (c i) + sfx a c (i + 1) m := by
  simp only [sfx]
  rw [show m - i = (m - (i + 1)) + 1 by omega, List.range'_succ]
  simp

theorem sfx_self (a : ℕ → ℕ → ℕ) (c : ℕ → ℕ) (m : ℕ) : sfx a c m m = 0 := by simp [sfx]

theorem pre_eq_add_sfx (a : ℕ → ℕ → ℕ) (c : ℕ → ℕ) {i m : ℕ} (h : i ≤ m) :
    pre a c m = pre a c i + sfx a c i m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k generalizing i with
  | zero => simp [sfx]
  | succ k ih =>
    rw [sfx_cons (by omega), show i + (k + 1) = (i + 1) + k by omega, ih (by omega), pre_succ]
    omega

theorem stC_eq_finC (c : ℕ → ℕ) {i : ℕ} (h : i ≤ I.n) : I.stC c I.n = I.finC c i (I.stC c i) := by
  simp [stC, finC, pre_eq_add_sfx _ c h]

theorem finC_succ (c : ℕ → ℕ) {i : ℕ} (h : i < I.n) (st : St) :
    I.finC c i st = I.finC c (i + 1) (I.succ i st (c i)) := by
  simp only [finC, succ, sfx_cons h]
  ext <;> simp <;> omega

/-- **The layers are the reachable states**: the states of the choices allowed by the current
domains on the first `i` items. -/
theorem mem_lay_iff : ∀ {i : ℕ} {st : St}, st ∈ I.lay i ↔ ∃ c, I.Allowed c 0 i ∧ I.stC c i = st
  | 0, st => by
    simp only [lay, List.mem_singleton]
    exact ⟨fun h => ⟨fun _ => 0, fun j _ hj => absurd hj (Nat.not_lt_zero _),
      by simp [h, stC, pre]⟩, fun ⟨c, _, h⟩ => by rw [← h]; simp [stC, pre]⟩
  | i + 1, st => by
    simp only [lay]
    rw [mem_nextL]
    constructor
    · rintro ⟨st₀, h₀, k, hk, rfl⟩
      obtain ⟨c, hc, rfl⟩ := (mem_lay_iff (i := i)).1 h₀
      refine ⟨Function.update c i k, fun j _ hj => ?_, ?_⟩
      · by_cases hji : j = i
        · subst hji; simpa using hk
        · rw [Function.update_of_ne hji]; exact hc j (Nat.zero_le _) (by omega)
      · have hcon : ∀ j < i, Function.update c i k j = c j :=
          fun j hj => Function.update_of_ne (Nat.ne_of_lt hj) _ _
        simp only [stC, succ, pre_succ, Function.update_self, pre_congr hcon]
    · rintro ⟨c, hc, rfl⟩
      exact ⟨I.stC c i, (mem_lay_iff (i := i)).2 ⟨c, fun (j : ℕ) h0 (hj : j < i) =>
        hc j h0 (Nat.lt_succ_of_lt hj), rfl⟩, c i, hc i (Nat.zero_le _) (Nat.lt_succ_self i),
        by simp [stC, succ, pre_succ]⟩

theorem mem_nextLay {i : ℕ} {st : St} (hst : st ∈ I.lay i) {k : ℕ}
    (hk : k ∈ livePos (I.dom i)) : I.succ i st k ∈ I.lay (i + 1) := by
  simp only [lay]
  exact I.mem_nextL.2 ⟨st, hst, k, hk, rfl⟩

/-- **The alive states are those with a feasible completion.** -/
theorem mem_alive_iff : ∀ (k : ℕ) {i : ℕ} (_ : i + k = I.n) {st : St},
    st ∈ I.alive i ↔ st ∈ I.lay i ∧ ∃ c, I.Allowed c i I.n ∧ I.feasible (I.finC c i st) = true
  | 0, i, hk, st => by
    simp only [Nat.add_zero] at hk
    subst hk
    rw [alive_n, List.mem_filter]
    have hf : ∀ c : ℕ → ℕ, I.finC c I.n st = st := fun c => by simp [finC, sfx_self]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun _ => 0, fun (j : ℕ) (h1 : I.n ≤ j) (h2 : j < I.n) =>
        absurd h2 (Nat.not_lt.2 h1), by rw [hf]; exact h2⟩
    · rintro ⟨h1, c, -, h2⟩
      exact ⟨h1, by rw [hf] at h2; exact h2⟩
  | k + 1, i, hk, st => by
    have hi : i < I.n := by omega
    rw [I.alive_lt hi, List.mem_filter]
    simp only [List.any_eq_true, decide_eq_true_eq]
    refine and_congr_right fun hst => ⟨?_, ?_⟩
    · rintro ⟨b, hb, hA⟩
      obtain ⟨-, c, hc, hfin⟩ := (mem_alive_iff k (i := i + 1) (by omega)).1 hA
      refine ⟨Function.update c i b, fun j hij hj => ?_, ?_⟩
      · by_cases hji : j = i
        · subst hji; simpa using hb
        · rw [Function.update_of_ne hji]; exact hc j (by omega) hj
      · rw [finC_succ I _ hi, Function.update_self]
        rw [← hfin]
        simp only [finC]
        rw [sfx_congr (c := Function.update c i b) (d := c) (fun (j : ℕ) (hj : i + 1 ≤ j) _ =>
            Function.update_of_ne (Nat.ne_of_gt hj) _ _),
          sfx_congr (c := Function.update c i b) (d := c) (fun (j : ℕ) (hj : i + 1 ≤ j) _ =>
            Function.update_of_ne (Nat.ne_of_gt hj) _ _)]
    · rintro ⟨c, hc, hfin⟩
      refine ⟨c i, hc i le_rfl hi, (mem_alive_iff k (i := i + 1) (by omega)).2
        ⟨I.mem_nextLay hst (hc i le_rfl hi), c, fun j hj h' => hc j (by omega) h', ?_⟩⟩
      rw [← finC_succ I _ hi]; exact hfin

/-- **The value at position `k` of item `j` is supported**: some choice of positions of the
current domains, with `k` for item `j`, has its weight and profit in their current domains. -/
public def SupportedN (j k : ℕ) : Prop :=
  ∃ c, I.Allowed c 0 I.n ∧ c j = k ∧ I.feasible (I.stC c I.n) = true

/-- **Completeness of the dynamic program**: if no transition by the position `k` out of layer
`j` reaches an alive state, the value is unsupported, and conversely. -/
theorem forall_not_alive_iff {j : ℕ} (hj : j < I.n) {k : ℕ} (hk : k ∈ livePos (I.dom j)) :
    (∀ st ∈ I.lay j, I.succ j st k ∉ I.alive (j + 1)) ↔ ¬ I.SupportedN j k := by
  constructor
  · rintro hall ⟨c, hc, hcj, hfin⟩
    refine hall (I.stC c j) ((I.mem_lay_iff).2 ⟨c, fun x h0 hx => hc x h0 (by omega), rfl⟩) ?_
    rw [I.mem_alive_iff (I.n - (j + 1)) (by omega)]
    refine ⟨I.mem_nextLay ((I.mem_lay_iff).2 ⟨c, fun x h0 hx => hc x h0 (by omega), rfl⟩) hk,
      c, fun x h1 h2 => hc x (Nat.zero_le _) h2, ?_⟩
    rw [← hcj, ← finC_succ I _ hj, ← stC_eq_finC I c hj.le]
    exact hfin
  · rintro hns st hst hA
    obtain ⟨c₁, hc₁, rfl⟩ := (I.mem_lay_iff).1 hst
    obtain ⟨-, c₂, hc₂, hfin⟩ := (I.mem_alive_iff (I.n - (j + 1)) (by omega)).1 hA
    let c : ℕ → ℕ := fun x => if x < j then c₁ x else if x = j then k else c₂ x
    have h1 : ∀ x < j, c x = c₁ x := fun x hx => by simp [c, hx]
    have h2 : ∀ x, j + 1 ≤ x → x < I.n → c x = c₂ x := fun x hx _ => by
      simp [c, show ¬ x < j by omega, show x ≠ j by omega]
    have hcj : c j = k := by simp [c]
    refine hns ⟨c, fun x _ hx => ?_, hcj, ?_⟩
    · by_cases h : x < j
      · rw [h1 x h]; exact hc₁ x (Nat.zero_le _) h
      · by_cases h' : x = j
        · subst h'; rw [hcj]; exact hk
        · rw [h2 x (by omega) hx]; exact hc₂ x (by omega) hx
    · rw [stC_eq_finC I c hj.le, finC_succ I _ hj, hcj]
      have hst : I.stC c j = I.stC c₁ j := by
        simp only [stC]; rw [pre_congr h1, pre_congr h1]
      rw [hst, ← hfin]
      simp only [finC]
      rw [sfx_congr h2, sfx_congr h2]

/-- **The value at position `k` of the sum `s` is supported**: some allowed choice of positions
has its weight and profit in their current domains, the sum `s` being the value at `k`. -/
public def SupportedS (s : Bool) (k : ℕ) : Prop :=
  ∃ c, I.Allowed c 0 I.n ∧ I.feasible (I.stC c I.n) = true ∧
    sCoord s (I.stC c I.n) = dval (I.sDom s) k

theorem forall_not_final_iff (s : Bool) (k : ℕ) :
    (∀ st ∈ I.lay I.n, ¬ (I.feasible st = true ∧ sCoord s st = dval (I.sDom s) k)) ↔
      ¬ I.SupportedS s k := by
  constructor
  · rintro hall ⟨c, hc, hf, he⟩
    exact hall _ ((I.mem_lay_iff).2 ⟨c, hc, rfl⟩) ⟨hf, he⟩
  · rintro hns st hst ⟨hf, he⟩
    obtain ⟨c, hc, rfl⟩ := (I.mem_lay_iff).1 hst
    exact hns ⟨c, hc, hf, he⟩

/-! ### The assignment of a choice -/

/-- The assignment of the direct literals that picks the position `c j` of each item `j`, `kw`
of the weight and `kp` of the profit. -/
def asg (c : ℕ → ℕ) (kw kp : ℕ) (x : ℕ) : Bool :=
  if x < I.wBase then (List.range I.n).any (fun j => x == I.var j (c j))
  else if x < I.pBase then x - I.wBase == kw else x - I.pBase == kp

theorem asg_var {c : ℕ → ℕ} (hc : ∀ j < I.n, c j < I.len j) (kw kp : ℕ) {j k : ℕ}
    (hj : j < I.n) (hk : k < I.len j) : I.asg c kw kp (I.var j k) = (k == c j) := by
  have hlt : I.var j k < I.wBase := I.var_lt hj hk
  simp only [asg, hlt, ↓reduceIte]
  cases h : (k == c j)
  · simp only [List.any_eq_false, List.mem_range, beq_iff_eq]
    intro j' hj' he
    obtain ⟨rfl, rfl⟩ := I.var_inj hk (hc j' hj') he
    simp at h
  · simp only [beq_iff_eq] at h
    subst h
    simp only [List.any_eq_true, List.mem_range, beq_iff_eq]
    exact ⟨j, hj, rfl⟩

theorem asg_w (c : ℕ → ℕ) (kw kp : ℕ) {k : ℕ} (hk : k < I.wDom.length) :
    I.asg c kw kp (I.wBase + k) = (k == kw) := by
  simp [asg, pBase, hk]

theorem asg_p (c : ℕ → ℕ) (kw kp : ℕ) (k : ℕ) :
    I.asg c kw kp (I.pBase + k) = (k == kp) := by
  have : I.wBase ≤ I.pBase := by simp [pBase]
  simp only [asg, show ¬ I.pBase + k < I.wBase by omega, show ¬ I.pBase + k < I.pBase by omega,
    ↓reduceIte, Nat.add_sub_cancel_left]

theorem picks_asg {c : ℕ → ℕ} (hc : ∀ j < I.n, c j < I.len j) (kw kp : ℕ) {j : ℕ}
    (hj : j < I.n) : I.Picks (I.asg c kw kp) j (c j) :=
  ⟨hc j hj, by rw [I.asg_var hc kw kp hj (hc j hj)]; simp,
    fun k' hk' hne => by rw [I.asg_var hc kw kp hj hk']; simpa using hne⟩

theorem part_asg {c : ℕ → ℕ} (hc : ∀ j < I.n, c j < I.len j) (kw kp : ℕ) (a : ℕ → ℕ → ℕ) :
    ∀ {i : ℕ}, i ≤ I.n → part (I.asg c kw kp) (I.flat a) true (I.off i) = pre a c i
  | 0, _ => by simp [off, pre, part]
  | i + 1, hi => by
    rw [I.part_off_succ _ a true (by omega), part_asg hc kw kp a (by omega),
      I.rowPart_true (I.picks_asg hc kw kp (by omega)) a, pre_succ]

theorem picksD_w {c : ℕ → ℕ} {kw kp : ℕ} (hkw : kw < I.wDom.length) :
    PicksD (I.asg c kw kp) I.wDom I.wBase kw :=
  ⟨hkw, by rw [I.asg_w c kw kp hkw]; simp,
    fun k' hk' hne => by rw [I.asg_w c kw kp hk']; simpa using hne⟩

theorem picksD_p {c : ℕ → ℕ} {kw kp : ℕ} (hkp : kp < I.pDom.length) :
    PicksD (I.asg c kw kp) I.pDom I.pBase kp :=
  ⟨hkp, by rw [I.asg_p c kw kp kp]; simp,
    fun k' _ hne => by rw [I.asg_p c kw kp k']; simpa using hne⟩

/-- **The assignment of a choice solves the formula** when the weight and the profit are the
values it picks for `W` and `P`. -/
theorem holds_formula_asg {c : ℕ → ℕ} (hc : ∀ j < I.n, c j < I.len j) {kw kp : ℕ}
    (hkw : kw < I.wDom.length) (hkp : kp < I.pDom.length)
    (hw : dval I.wDom kw = pre I.cw c I.n) (hp : dval I.pDom kp = pre I.cp c I.n) :
    ∀ c' ∈ I.formula, c'.Holds (I.asg c kw kp) := by
  have hpw := I.part_asg hc kw kp I.cw le_rfl
  have hpp := I.part_asg hc kw kp I.cp le_rfl
  have aw := part_add_part (I.asg c kw kp) (I.flat I.cw) true (I.off I.n)
  have ap := part_add_part (I.asg c kw kp) (I.flat I.cp) true (I.off I.n)
  have sw := sPart_add (I.asg c kw kp) I.wDom I.wBase true
  have sp := sPart_add (I.asg c kw kp) I.pDom I.pBase true
  have tw := sPart_true (I.picksD_w (c := c) (kp := kp) hkw)
  have tp := sPart_true (I.picksD_p (c := c) (kw := kw) hkp)
  simp only [Bool.not_true] at aw ap sw sp
  intro c' hc'
  simp only [formula, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_range] at hc'
  rcases hc' with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨j, hj, rfl | rfl⟩
  · simp only [linkW₁, Holds, lhs_append, lhs_terms, lhs_sTerms]; simp only [sPart] at *; omega
  · simp only [linkW₂, Holds, lhs_append, lhs_terms, lhs_sTerms, tot]
    simp only [sPart] at *; omega
  · simp only [linkP₁, Holds, lhs_append, lhs_terms, lhs_sTerms]; simp only [sPart] at *; omega
  · simp only [linkP₂, Holds, lhs_append, lhs_terms, lhs_sTerms, tot]
    simp only [sPart] at *; omega
  · exact (holds_alo _ _ _).2 ⟨kw, hkw, (I.picksD_w hkw).2.1⟩
  · exact holds_amo_of (k := kw) (I.picksD_w hkw).2.2
  · exact (holds_alo _ _ _).2 ⟨kp, hkp, (I.picksD_p hkp).2.1⟩
  · exact holds_amo_of (k := kp) (I.picksD_p hkp).2.2
  · exact (holds_alo _ _ _).2 ⟨c j, hc j hj, (I.picks_asg hc kw kp hj).2.1⟩
  · exact holds_amo_of (k := c j) (I.picks_asg hc kw kp hj).2.2

/-- **The assignment of an allowed choice agrees with the antecedent.** -/
theorem consistent_asg {c : ℕ → ℕ} (hc : I.Allowed c 0 I.n) {kw kp : ℕ}
    (hkw : kw ∈ livePos I.wDom) (hkp : kp ∈ livePos I.pDom) :
    Consistent (I.asg c kw kp) I.antecedent := by
  have hc' : ∀ j < I.n, c j < I.len j := fun j hj => (mem_livePos.1 (hc j (Nat.zero_le _) hj)).1
  intro l hl
  simp only [antecedent, List.mem_append, List.mem_flatMap, List.mem_filterMap,
    List.mem_range] at hl
  rcases hl with (⟨j, hj, k, hk, hl⟩ | ⟨k, hk, hl⟩) | ⟨k, hk, hl⟩ <;>
    split_ifs at hl with hlv <;> cases hl
  · rw [Literal.eval_mk, I.asg_var hc' _ _ hj hk]
    have := (mem_livePos.1 (hc j (Nat.zero_le _) hj)).2
    have hne : k ≠ c j := fun h => by rw [h] at hlv; simp_all
    simp [hne]
  · rw [Literal.eval_mk, I.asg_w c _ _ hk]
    have := (mem_livePos.1 hkw).2
    have hne : k ≠ kw := fun h => by rw [h] at hlv; simp_all
    simp [hne]
  · rw [Literal.eval_mk, I.asg_p c _ _ k]
    have := (mem_livePos.1 hkp).2
    have hne : k ≠ kp := fun h => by rw [h] at hlv; simp_all
    simp [hne]

theorem exists_of_feasible {st : St} (h : I.feasible st = true) :
    (∃ kw ∈ livePos I.wDom, dval I.wDom kw = st.1) ∧
      ∃ kp ∈ livePos I.pDom, dval I.pDom kp = st.2 := by
  simpa [feasible, List.any_eq_true] using h

/-- A constraint of the database over the direct literals holds at every solution of the formula,
by the Boolean emitter's `holds_of_runTop`. -/
theorem holds_of_run {e : ProofLog} {db : List (ℕ × PBConstr)} (h : I.Run e db) {k : ℕ}
    {c : PBConstr} (hk : lookup db k = some c) (hv : ∀ x ∈ c.vars, x < I.M) {σ : ℕ → Bool}
    (hσ : ∀ c ∈ I.formula, c.Holds σ) : c.Holds σ :=
  Knapsack.Inst.holds_of_runTop (s := I.state db e.next) h.1 rfl rfl rfl hk
    (fun x hx => by simpa [pres] using hv x hx) hσ

/-! ### The removals are exactly the unsupported values -/

/-- **The removed values of the items are exactly the unsupported values of their current
domains.** The direction "removed ⇒ unsupported" holds because the checker accepts the proof,
which derives `D ⇒ [xⱼ ≠ v]`; the converse is the exactness of the dynamic program. -/
public theorem mem_removed_iff {j k : ℕ} :
    (j, k) ∈ I.propagate.removed ↔ j < I.n ∧ k ∈ livePos (I.dom j) ∧ ¬ I.SupportedN j k := by
  obtain ⟨db, h, hys, hcov, -, -⟩ := I.emit_spec
  constructor
  · intro hm
    simp only [propagate, List.mem_map] at hm
    obtain ⟨y, hy, hyk⟩ := hm
    obtain ⟨hb, hj, hl⟩ := hys y hy
    rw [hyk] at hb hj hl
    refine ⟨hj, hb, fun ⟨c, hc, hcj, hfin⟩ => ?_⟩
    obtain ⟨⟨kw, hkw, hw⟩, ⟨kp, hkp, hp⟩⟩ := I.exists_of_feasible hfin
    have hc' : ∀ j < I.n, c j < I.len j := fun j hj => (mem_livePos.1 (hc j (Nat.zero_le _) hj)).1
    have hcl := I.holds_of_run h hl (fun x hx => by
      obtain ⟨l, hl, rfl⟩ := vars_clause (mem_vars_of_mem_vars_normalize hx)
      rcases List.mem_append.1 hl with hl | hl
      · exact I.vars_negD hl
      · simp only [List.mem_singleton] at hl; subst hl
        have := I.var_lt (i := I.n) hj (mem_livePos.1 hb).1
        have := I.wBase_le_M; simp only [wBase] at *; omega)
      (I.holds_formula_asg hc' (kw := kw) (kp := kp) (mem_livePos.1 hkw).1 (mem_livePos.1 hkp).1
        hw hp)
    rw [holds_normalize, remClause, holds_clause] at hcl
    obtain ⟨l, hl, hev⟩ := hcl
    rcases List.mem_append.1 hl with hl | hl
    · simp [I.eval_negD (I.consistent_asg hc hkw hkp) l hl] at hev
    · simp only [List.mem_singleton] at hl; subst hl
      simp [I.asg_var hc' _ _ hj (mem_livePos.1 hb).1, hcj] at hev
  · rintro ⟨hj, hk, hns⟩
    obtain ⟨m, hm⟩ := hcov j hj k hk ((I.forall_not_alive_iff hj hk).2 hns)
    exact List.mem_map.2 ⟨_, hm, rfl⟩

private theorem mem_removedS_iff (s : Bool) {k : ℕ} :
    k ∈ (if s then I.propagate.removedP else I.propagate.removedW) ↔
      k ∈ livePos (I.sDom s) ∧ ¬ I.SupportedS s k := by
  obtain ⟨db, h, -, -, hys, hcov⟩ := I.emit_spec
  have hrem : (if s then I.propagate.removedP else I.propagate.removedW) =
      (if s then I.emit.ps else I.emit.ws).map (·.1) := by
    cases s <;> rfl
  rw [hrem]
  constructor
  · intro hm
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hm
    obtain ⟨hb, hl⟩ := hys s y hy
    refine ⟨hb, fun ⟨c, hc, hfin, he⟩ => ?_⟩
    obtain ⟨⟨kw, hkw, hw⟩, ⟨kp, hkp, hp⟩⟩ := I.exists_of_feasible hfin
    have hc' : ∀ j < I.n, c j < I.len j := fun j hj => (mem_livePos.1 (hc j (Nat.zero_le _) hj)).1
    -- The position `y.1` for the sum `s`, the found one for the other.
    obtain ⟨kw', kp', hkw', hkp', hw', hp', hsk⟩ : ∃ kw' kp', kw' ∈ livePos I.wDom ∧
        kp' ∈ livePos I.pDom ∧ dval I.wDom kw' = pre I.cw c I.n ∧
        dval I.pDom kp' = pre I.cp c I.n ∧ I.asg c kw' kp' (I.sBase s + y.1) = true := by
      cases s
      · refine ⟨y.1, kp, hb, hkp, ?_, hp, ?_⟩
        · simpa [sCoord, stC, sDom] using he.symm
        · simp [sBase, I.asg_w c _ _ (mem_livePos.1 hb).1]
      · refine ⟨kw, y.1, hkw, hb, hw, ?_, ?_⟩
        · simpa [sCoord, stC, sDom] using he.symm
        · simp [sBase, I.asg_p]
    have hcl := I.holds_of_run h hl (fun x hx => by
      obtain ⟨l, hl, rfl⟩ := vars_clause (mem_vars_of_mem_vars_normalize hx)
      rcases List.mem_append.1 hl with hl | hl
      · exact I.vars_negD hl
      · simp only [List.mem_singleton] at hl; subst hl
        have := I.sBase_add_le_M s; have := (mem_livePos.1 hb).1; simp only; omega)
      (I.holds_formula_asg hc' (mem_livePos.1 hkw').1 (mem_livePos.1 hkp').1 hw' hp')
    rw [holds_normalize, remSClause, holds_clause] at hcl
    obtain ⟨l, hl, hev⟩ := hcl
    rcases List.mem_append.1 hl with hl | hl
    · simp [I.eval_negD (I.consistent_asg hc hkw' hkp') l hl] at hev
    · simp only [List.mem_singleton] at hl; subst hl
      simp [hsk] at hev
  · rintro ⟨hk, hns⟩
    obtain ⟨m, hm⟩ := hcov s k hk ((I.forall_not_final_iff s k).2 hns)
    exact List.mem_map.2 ⟨_, hm, rfl⟩

/-- **The removed values of the weight are exactly the unsupported values of its current
domain**: the remaining ones are the weights of the feasible states of the last layer. -/
public theorem mem_removedW_iff {k : ℕ} :
    k ∈ I.propagate.removedW ↔ k ∈ livePos I.wDom ∧ ¬ I.SupportedS false k :=
  I.mem_removedS_iff false

/-- **The removed values of the profit are exactly the unsupported values of its current
domain.** -/
public theorem mem_removedP_iff {k : ℕ} :
    k ∈ I.propagate.removedP ↔ k ∈ livePos I.pDom ∧ ¬ I.SupportedS true k :=
  I.mem_removedS_iff true

end Inst

end Cslib.Logic.PL.VeriPB.Knapsack.Trick
