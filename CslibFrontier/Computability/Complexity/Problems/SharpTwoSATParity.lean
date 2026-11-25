/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SharpTwoSAT
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Logics.Propositional.CNF.Eval
import CslibFrontier.Logics.Propositional.CNF.ModelCount.Relabel
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Basic

/-!
# Linear-size parity queries for the two-query reduction to #2SAT

The queries implement the selector and parity-chain construction of
[BannachDemaineGomezHecher2026, §3, equation (3.3) and Theorem 3.8]. The formalization folds
the clause indicators into the parity selectors. We count extensions by fixing the source
assignment and summing over the parity chain. At each step, the difference between the numbers
of extensions that keep or flip the state is one for a satisfied clause and zero for a
falsified clause.

The output is an ordinary CNF with binary natural-variable labels. Its model count is over
occurring variables, and tautologies expose the same assignment universe in both queries.
The size and model-count results supply the combinatorial part of the #SH transfer in
[MITHardnessGroup2026SH, §6, Corollary 6.1].

## Main results

* `Cslib.Complexity.SharpTwoSATParity.sharpSAT_eq_parityQuery_sub`: the exact difference identity.
* `Cslib.Complexity.SharpTwoSATParity.size_parityQuery_le`: a linear bound for width-three inputs.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL
open scoped BigOperators

namespace SharpTwoSATParity

private abbrev State (φ : CNF ℕ) := Fin (φ.length + 1)
private abbrev Choice := Bool × Bool
private abbrev Var (φ : CNF ℕ) :=
  φ.vars.toFinset ⊕ (State φ ⊕ (Fin φ.length × Choice))

private def state {φ : CNF ℕ} (i : State φ) : Var φ := .inr (.inl i)

private def selector {φ : CNF ℕ} (i : Fin φ.length) (choice : Choice) : Var φ :=
  .inr (.inr (i, choice))

private def choices : List Choice :=
  [(false, false), (false, true), (true, false), (true, true)]

private theorem mem_choices (ab : Choice) : ab ∈ choices := by
  rcases ab with ⟨a, b⟩
  cases a <;> cases b <;> decide

private def declare {φ : CNF ℕ} (v : Var φ) : Clause (Var φ) := [(v, false), (v, true)]

private def declarations (φ : CNF ℕ) : CNF (Var φ) :=
  (φ.distinctVars.attach.map fun v =>
    declare (.inl ⟨v.1, List.mem_toFinset.mpr (CNF.mem_distinctVars.mp v.2)⟩)) ++
  ((List.finRange (φ.length + 1)).map (fun i => declare (state i)) ++
    (List.finRange φ.length).flatMap fun i => choices.map fun ab => declare (selector i ab))

private theorem declare_mem_declarations (φ : CNF ℕ) (v : Var φ) :
    declare v ∈ declarations φ := by
  rcases v with v | (i | ⟨i, ab⟩)
  · apply List.mem_append.mpr
    left
    apply List.mem_map.mpr
    exact ⟨⟨v, CNF.mem_distinctVars.mpr (List.mem_toFinset.mp v.2)⟩, List.mem_attach _ _, rfl⟩
  · apply List.mem_append.mpr
    right
    apply List.mem_append.mpr
    left
    exact List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩
  · apply List.mem_append.mpr
    right
    apply List.mem_append.mpr
    right
    exact List.mem_flatMap.mpr
      ⟨i, List.mem_finRange _, List.mem_map.mpr ⟨ab, mem_choices ab, rfl⟩⟩

private theorem eval_declarations (φ : CNF ℕ) (σ : Var φ → Bool) :
    (declarations φ).eval σ = true := by
  have h (v : Var φ) : (declare v).eval σ = true := by cases hv : σ v <;> simp [declare, hv]
  simp only [declarations, CNF.eval_append, Bool.and_eq_true, CNF.eval_map_eq_true_iff,
    CNF.eval_flatMap_eq_true_iff]
  exact ⟨fun _ _ => h _, fun _ _ => h _, fun _ _ _ _ => h _⟩

private def gate {φ : CNF ℕ} (s : Var φ) (l : Literal (Var φ)) : Clause (Var φ) :=
  [(s, false), l]

private theorem eval_gate_iff {φ : CNF ℕ} (σ : Var φ → Bool) (s : Var φ) (l : Literal (Var φ)) :
    (gate s l).eval σ = true ↔ (σ s = true → σ l.1 = l.2) := by
  cases hs : σ s <;> simp [gate, hs, Literal.eval_eq_true_iff]

private def sourceAssignment {φ : CNF ℕ} (σ : Var φ → Bool) : φ.vars.toFinset → Bool :=
  fun v => σ (.inl v)

private def sourceLiteral {φ : CNF ℕ} (i : Fin φ.length) (l : {l // l ∈ φ[i]}) : Literal (Var φ) :=
  (.inl ⟨l.1.1, List.mem_toFinset.mpr (CNF.mem_vars.mpr
    ⟨φ[i], List.getElem_mem _, l.1.2, l.2⟩)⟩, !l.1.2)

private def stepClauses (φ : CNF ℕ) (i : Fin φ.length) (ab : Choice) : CNF (Var φ) :=
  let s := selector i ab
  gate s (state i.castSucc, ab.1) :: gate s (state i.succ, ab.2) ::
    (if ab.1 = ab.2 then [] else (φ[i]).attach.map fun l => gate s (sourceLiteral i l))

private def typedQuery (φ : CNF ℕ) (odd : Bool) : CNF (Var φ) :=
  [(state 0, false)] :: [(state (Fin.last φ.length), odd)] ::
    (declarations φ ++ (List.finRange φ.length).flatMap fun i => choices.flatMap (stepClauses φ i))

private theorem vars_typedQuery (φ : CNF ℕ) (odd : Bool) :
    (typedQuery φ odd).vars.toFinset = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro v
  apply List.mem_toFinset.mpr
  apply CNF.mem_vars.mpr
  exact ⟨declare v, by simp [typedQuery, declare_mem_declarations], false, by simp [declare]⟩

private theorem eval_stepClauses_iff {φ : CNF ℕ} (σ : Var φ → Bool) (i : Fin φ.length)
    (ab : Choice) :
    (stepClauses φ i ab).eval σ = true ↔ σ (selector i ab) = true →
      σ (state i.castSucc) = ab.1 ∧ σ (state i.succ) = ab.2 ∧
        (ab.1 = ab.2 ∨ φ[i].eval (φ.extendAssignment (sourceAssignment σ)) = false) := by
  have h (l : {l // l ∈ φ[i]}) :
      σ (sourceLiteral i l).1 = (sourceLiteral i l).2 ↔
        φ.extendAssignment (sourceAssignment σ) l.1.1 = !l.1.2 := by
    rw [CNF.extendAssignment_of_mem _ (CNF.mem_vars.mpr
      ⟨φ[i], List.getElem_mem _, l.1.2, l.2⟩)]
    rfl
  simp only [stepClauses, CNF.eval_cons, Bool.and_eq_true, eval_gate_iff]
  split_ifs with ha
  · simp only [ha, true_or, and_true, CNF.eval_nil]
    tauto
  · simp only [ha, false_or, CNF.eval_map_eq_true_iff, List.mem_attach, true_implies, eval_gate_iff,
      h, Clause.eval_eq_false_iff, Subtype.forall]
    tauto

private def validChoices (b left right : Bool) (f : Choice → Bool) : Prop :=
  ∀ ab, f ab = true → left = ab.1 ∧ right = ab.2 ∧ (ab.1 = ab.2 ∨ b = false)

private theorem eval_typedQuery_iff (φ : CNF ℕ) (σ : Var φ → Bool) (odd : Bool) :
    (typedQuery φ odd).eval σ = true ↔
      σ (state 0) = false ∧ σ (state (Fin.last φ.length)) = odd ∧ ∀ i,
        validChoices (φ[i].eval (φ.extendAssignment (sourceAssignment σ)))
          (σ (state i.castSucc)) (σ (state i.succ)) (fun ab => σ (selector i ab)) := by
  rw [typedQuery]
  simp only [CNF.eval_cons, CNF.eval_append, Bool.and_eq_true, eval_declarations, true_and,
    Clause.eval_cons, Clause.eval_nil, Bool.or_false, Literal.eval_eq_true_iff]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  simp only [CNF.eval_flatMap_eq_true_iff, List.mem_finRange, mem_choices, true_implies,
    eval_stepClauses_iff, validChoices]

private instance decidableValidChoices (sat left right : Bool) (f : Choice → Bool) :
    Decidable (validChoices sat left right f) := by
  unfold validChoices
  infer_instance

/-- The inactive selectors give one extension. A single additional extension is available if
the transition keeps the state or the source clause is false. -/
private def transitionWeight (sat left right : Bool) : ℕ :=
  if left = right ∨ sat = false then 2 else 1

private theorem card_validChoices (sat left right : Bool) :
    Fintype.card {f : Choice → Bool // validChoices sat left right f} =
      transitionWeight sat left right := by
  cases sat <;> cases left <;> cases right <;> decide

private def paritySign (b : Bool) : ℤ := if b then -1 else 1

private def chain {m : ℕ} (start : Bool) (path : Fin m → Bool) : Fin (m + 1) → Bool :=
  Fin.cons start path

private def pathWeight {m : ℕ} (sat : Fin m → Bool) (start : Bool) (path : Fin m → Bool) : ℤ :=
  ∏ i, transitionWeight (sat i) (chain start path i.castSucc) (path i)

private theorem pathWeight_cons {m : ℕ} (sat : Fin (m + 1) → Bool) (start next : Bool)
    (path : Fin m → Bool) :
    pathWeight sat start (Fin.cons next path) =
      transitionWeight (sat 0) start next * pathWeight (Fin.tail sat) next path := by
  rw [pathWeight, Fin.prod_univ_succ, pathWeight]
  simp only [chain, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
  congr 1

private theorem signedPathSum {m : ℕ} (sat : Fin m → Bool) (start : Bool) :
    (∑ path : Fin m → Bool,
      pathWeight sat start path * paritySign (chain start path (Fin.last m))) =
      if ∀ i, sat i = true then paritySign start else 0 := by
  induction m generalizing start with
  | zero => simp [pathWeight, chain, show Fin.last 0 = 0 by rfl]
  | succ m ih =>
    rw [← (Fin.consEquiv fun _ : Fin (m + 1) => Bool).sum_comp, Fintype.sum_prod_type]
    have htail (b : Bool) :
        (∑ path : Fin m → Bool, pathWeight (Fin.tail sat) b path *
          paritySign (Fin.cons (α := fun _ => Bool) b path (Fin.last m))) =
        if ∀ i, (Fin.tail sat) i = true then paritySign b else 0 :=
      ih (Fin.tail sat) b
    have hlast : Fin.last (m + 1) = (Fin.last m).succ := rfl
    simp only [Fin.consEquiv_apply, pathWeight_cons, chain, hlast, Fin.cons_succ, mul_assoc,
      ← Finset.mul_sum, htail]
    simp only [Fin.forall_fin_succ, Fin.tail]
    by_cases hall : ∀ i : Fin m, sat i.succ = true
    · cases sat 0 <;> cases start <;> simp [hall, transitionWeight, paritySign]
    · simp [hall]

private def assignmentEquiv (φ : CNF ℕ) :
    ((φ.vars.toFinset → Bool) × (State φ → Bool) × (Fin φ.length → Choice → Bool)) ≃
      (Var φ → Bool) where
  toFun x := Sum.elim x.1 (Sum.elim x.2.1 fun a => x.2.2 a.1 a.2)
  invFun σ := (sourceAssignment σ, fun i => σ (state i), fun i ab => σ (selector i ab))
  left_inv _ := rfl
  right_inv σ := by
    funext v
    rcases v with v | (i | ab) <;> rfl

private theorem modelCount_typedQuery_filter (φ : CNF ℕ) (odd : Bool) :
    (typedQuery φ odd).modelCount =
      (Finset.univ.filter fun σ : Var φ → Bool => (typedQuery φ odd).eval σ = true).card := by
  refine CNF.modelCount_eq_card_filter id _ (fun σ τ _ _ => ?_) (fun σ => ?_)
  · constructor
    · intro h
      exact fun v _ => congrFun h v
    · intro h
      funext v
      apply h
      apply List.mem_toFinset.mp
      rw [vars_typedQuery]
      exact Finset.mem_univ _
  · exact ⟨fun hs => ⟨σ, hs, rfl⟩, by rintro ⟨τ, hτ, rfl⟩; exact hτ⟩

private theorem sum_validFlags {m : ℕ} (sat left right : Fin m → Bool) :
    (∑ f : Fin m → Choice → Bool, if ∀ i, validChoices (sat i) (left i) (right i) (f i)
      then (1 : ℤ) else 0) =
      ∏ i, (transitionWeight (sat i) (left i) (right i) : ℤ) := by
  classical
  have h := Fintype.card_congr
    (Equiv.subtypePiEquivPi (p := fun i => validChoices (sat i) (left i) (right i)))
  rw [Fintype.card_pi] at h
  simp_rw [card_validChoices] at h
  rw [← Nat.cast_prod, ← h, Fintype.card_subtype]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  simp

private theorem modelCount_typedQuery_paths (φ : CNF ℕ) (odd : Bool) :
    ((typedQuery φ odd).modelCount : ℤ) =
      ∑ source : φ.vars.toFinset → Bool, ∑ path : Fin φ.length → Bool,
        if chain false path (Fin.last φ.length) = odd then
          pathWeight (fun i => φ[i].eval (φ.extendAssignment source)) false path else 0 := by
  classical
  rw [modelCount_typedQuery_filter, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  simp only [Nat.cast_one]
  rw [← (assignmentEquiv φ).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun source _ => ?_
  rw [Fintype.sum_prod_type, ← (Fin.consEquiv fun _ : State φ => Bool).sum_comp,
    Fintype.sum_prod_type, Fintype.sum_bool]
  have hEval (b : Bool) (path : Fin φ.length → Bool) (flags : Fin φ.length → Choice → Bool) :
      (typedQuery φ odd).eval (assignmentEquiv φ (source, Fin.cons b path, flags)) = true ↔
        b = false ∧ chain b path (Fin.last φ.length) = odd ∧
          ∀ i, validChoices (φ[i].eval (φ.extendAssignment source)) (chain b path i.castSucc)
            (path i) (flags i) :=
    eval_typedQuery_iff φ _ odd
  simp only [Fin.consEquiv_apply, hEval, Bool.true_eq_false, false_and, ite_false,
    Finset.sum_const_zero, zero_add, true_and]
  refine Finset.sum_congr rfl fun path _ => ?_
  by_cases h : chain false path (Fin.last φ.length) = odd
  · simpa only [h, true_and, ite_true, pathWeight] using
      sum_validFlags (fun i => φ[i].eval (φ.extendAssignment source))
        (fun i => chain false path i.castSucc) path
  · simp [h]

private theorem modelCount_typedQuery_sub (φ : CNF ℕ) :
    ((typedQuery φ false).modelCount : ℤ) - (typedQuery φ true).modelCount = φ.modelCount := by
  classical
  rw [modelCount_typedQuery_paths, modelCount_typedQuery_paths, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ source : φ.vars.toFinset → Bool,
        if φ.eval (φ.extendAssignment source) = true then (1 : ℤ) else 0 := by
      refine Finset.sum_congr rfl fun source _ => ?_
      rw [← Finset.sum_sub_distrib]
      let sat (i : Fin φ.length) := φ[i].eval (φ.extendAssignment source)
      have h : (∀ i, sat i = true) ↔ φ.eval (φ.extendAssignment source) = true := by
        rw [CNF.eval_eq_true_iff]
        constructor
        · intro h c hc
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
          exact h ⟨i, hi⟩
        · intro h i
          exact h _ (List.getElem_mem _)
      simp only [← h]
      change _ = if ∀ i, sat i = true then paritySign false else 0
      rw [← signedPathSum sat false]
      refine Finset.sum_congr rfl fun path _ => ?_
      cases chain false path (Fin.last φ.length) <;> simp [paritySign, sat]
    _ = _ := by
      rw [CNF.modelCount, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
      simp only [Nat.cast_one]

/-- Original variables use residue zero, states use residue one, and the four selectors use
residues two through five. The quotient holds the source label or chain index. -/
private def label {φ : CNF ℕ} : Var φ → ℕ
  | .inl v => 6 * v.val
  | .inr (.inl i) => 6 * i.val + 1
  | .inr (.inr (i, a, b)) => 6 * i.val + 2 + 2 * a.toNat + b.toNat

private theorem label_injective (φ : CNF ℕ) : Function.Injective (label (φ := φ)) := by
  have hbit (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide
  rintro (v | (i | ⟨i, a, b⟩)) (w | (j | ⟨j, c, d⟩)) h <;> simp only [label] at h
  · exact congrArg Sum.inl (Subtype.ext (by omega))
  · omega
  · have := hbit c
    have := hbit d
    omega
  · omega
  · exact congrArg (Sum.inr ∘ Sum.inl) (Fin.ext (by omega))
  · have := hbit c
    have := hbit d
    omega
  · have := hbit a
    have := hbit b
    omega
  · have := hbit a
    have := hbit b
    omega
  · have ha := hbit a
    have hb := hbit b
    have hc := hbit c
    have hd := hbit d
    have hij : i = j := Fin.ext (by omega)
    subst j
    cases a <;> cases b <;> cases c <;> cases d <;> simp_all

private theorem length_clause_typedQuery (φ : CNF ℕ) (odd : Bool) {c : Clause (Var φ)}
    (hc : c ∈ typedQuery φ odd) : c.length ≤ 2 := by
  have hdeclare : ∀ c ∈ declarations φ, c.length ≤ 2 := by
    simp only [declarations, List.mem_append, List.mem_map, List.mem_flatMap]
    rintro _ (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, rfl⟩) <;> exact le_rfl
  have hstep (i : Fin φ.length) (ab : Choice) : ∀ c ∈ stepClauses φ i ab, c.length ≤ 2 := by
    simp only [stepClauses, List.mem_cons]
    rintro _ (rfl | rfl | hm)
    · exact le_rfl
    · exact le_rfl
    · split_ifs at hm with h
      · cases hm
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hm
        exact le_rfl
  simp only [typedQuery, List.mem_cons, List.mem_append, List.mem_flatMap] at hc
  rcases hc with rfl | rfl | hc | ⟨i, _, ab, _, hc⟩
  · exact Nat.le_succ 1
  · exact Nat.le_succ 1
  · exact hdeclare _ hc
  · exact hstep i ab _ hc

/-- The even or odd parity query, with the original variables and the chain auxiliaries assigned
disjoint natural-variable labels. `false` chooses even parity and `true` chooses odd parity. -/
def parityQuery (φ : CNF ℕ) (odd : Bool) : CNF ℕ :=
  (typedQuery φ odd).relabel label

/-- Every clause of a parity query has width at most two. -/
theorem width_parityQuery (φ : CNF ℕ) (odd : Bool) :
    ∀ c ∈ parityQuery φ odd, c.length ≤ 2 := by
  simp only [parityQuery, CNF.relabel, List.mem_map, forall_exists_index, and_imp]
  intro _ c hc rfl
  simpa only [Clause.relabel, List.length_map] using length_clause_typedQuery φ odd hc

private theorem sharpTwoSAT_parityQuery (φ : CNF ℕ) (odd : Bool) :
    SharpTwoSAT (parityQuery φ odd) = (typedQuery φ odd).modelCount := by
  have h : (parityQuery φ odd).all (fun c => decide (c.length ≤ 2)) = true :=
    List.all_eq_true.mpr fun c hc => decide_eq_true (width_parityQuery φ odd c hc)
  rw [SharpTwoSAT, ite_eq_left h, parityQuery, CNF.modelCount_relabel (label_injective φ)]

/-- Subtracting the odd query's exact count from the even query's exact count recovers the
original count. The integer difference is nonnegative, so natural subtraction is exact. -/
theorem sharpSAT_eq_parityQuery_sub (φ : CNF ℕ) :
    SharpSAT φ = SharpTwoSAT (parityQuery φ false) - SharpTwoSAT (parityQuery φ true) := by
  rw [SharpSAT, sharpTwoSAT_parityQuery, sharpTwoSAT_parityQuery]
  have h := modelCount_typedQuery_sub φ
  omega

private theorem length_declarations_le (φ : CNF ℕ) :
    (declarations φ).length ≤ φ.numVars + 5 * φ.length + 1 := by
  have h := List.length_flatMap_le (l := List.finRange φ.length)
    (f := fun i => choices.map fun ab => declare (selector i ab))
    (k := 4) (fun _ _ => by simp [choices])
  simp only [declarations, List.length_append, List.length_map, List.length_attach,
    CNF.length_distinctVars, List.length_finRange]
  rw [List.length_finRange] at h
  omega

private theorem length_parityQuery_le (φ : CNF ℕ) (odd : Bool)
    (hφ : ∀ c ∈ φ, c.length ≤ 3) :
    (parityQuery φ odd).length ≤ φ.numVars + 25 * φ.length + 3 := by
  have hblocks := List.length_flatMap_le
    (l := List.finRange φ.length) (f := fun i => choices.flatMap (stepClauses φ i))
    (k := 20) (fun i _ => by
      have h := List.length_flatMap_le (f := stepClauses φ i) (l := choices) (k := 5)
        (fun ab _ => by
          have hlen := hφ φ[i] (List.getElem_mem _)
          unfold stepClauses
          split_ifs <;> simp only [List.length_cons, List.length_nil, List.length_map,
            List.length_attach] <;> omega)
      exact h.trans (by decide))
  have hdecl := length_declarations_le φ
  simp only [parityQuery, typedQuery, CNF.relabel, List.length_map, List.length_cons,
    List.length_append]
  rw [List.length_finRange] at hblocks
  omega

/-- Both queries to count a width-three formula have linearly many vertices of the incidence
graph, measured as occurring variables plus clauses. The additive constant covers empty inputs. -/
theorem size_parityQuery_le (φ : CNF ℕ) (odd : Bool) (hφ : ∀ c ∈ φ, c.length ≤ 3) :
    (parityQuery φ odd).numVars + (parityQuery φ odd).length ≤
      80 * (φ.numVars + φ.length + 1) := by
  have hv := CNF.numVars_le_mul_length (width_parityQuery φ odd)
  have hc := length_parityQuery_le φ odd hφ
  omega

end SharpTwoSATParity

end Cslib.Complexity
