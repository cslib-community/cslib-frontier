/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SharpTwoSAT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Logics.Propositional.CNF.PolyTime
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Logics.Propositional.CNF.Eval
import CslibFrontier.Logics.Propositional.CNF.ModelCount.Relabel
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Basic

/-!
# Linear-size parity queries for the two-query reduction to #2SAT

The queries adapt the parity counter of [BannachDemaineGomezHecher2026, §3.1–3.2].
A selector names a pair of consecutive parity states, eliminating the separate clause
indicator. This changes the queries in (3.2) and can change their individual counts.
The proof recovers the difference identity of (3.3) using a signed sum over paths.
At each step, the difference between the numbers of extensions that keep or flip the
state is one for a satisfied clause and zero for a falsified clause.

The output is an ordinary CNF with binary natural-variable labels. Both queries count
assignments over their occurring variables, which include all source and auxiliary variables.
The size and model-count results supply the combinatorial part of the #SH transfer in
[MITHardnessGroup2026SH, §6, Corollary 6.1].

## Main results

* `Cslib.Complexity.SharpTwoSATParity.sharpSAT_eq_parityQuery_sub`: the exact difference identity.
* `Cslib.Complexity.SharpTwoSATParity.size_parityQuery_le`: a linear bound for width-three inputs.
* `Cslib.Complexity.SharpTwoSATParity.computableInPolyTime_parityQuery`: the multitape certificate.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM
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

private def gate {V : Type} (s : V) (l : Literal V) : Clause V :=
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
    (List.finRange φ.length).flatMap fun i => choices.flatMap (stepClauses φ i)

private theorem vars_typedQuery (φ : CNF ℕ) (odd : Bool) :
    (typedQuery φ odd).vars.toFinset = Finset.univ := by
  refine Finset.eq_univ_of_forall fun v => List.mem_toFinset.mpr (CNF.mem_vars.mpr ?_)
  have hstep (i : Fin φ.length) (ab : Choice) {c : Clause (Var φ)}
      (hc : c ∈ stepClauses φ i ab) : c ∈ typedQuery φ odd :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr
      ⟨i, List.mem_finRange _, List.mem_flatMap.mpr ⟨ab, mem_choices ab, hc⟩⟩))
  rcases v with v | (i | ⟨i, ab⟩)
  · obtain ⟨c, hc, b, hl⟩ := CNF.mem_vars.mp (List.mem_toFinset.mp v.property)
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc
    let idx : Fin φ.length := ⟨j, hj⟩
    let l : {l // l ∈ φ[idx]} := ⟨(v.val, b), hl⟩
    exact ⟨gate (selector idx (false, true)) (sourceLiteral idx l),
      hstep idx (false, true) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨l, List.mem_attach _ _, rfl⟩))),
      !b, List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)⟩
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · exact ⟨[(state (Fin.last φ.length), odd)], List.mem_cons_of_mem _ List.mem_cons_self,
        odd, List.mem_cons_self⟩
    · exact ⟨gate (selector j (false, false)) (state j.castSucc, false),
        hstep j (false, false) List.mem_cons_self, false, List.mem_cons_of_mem _ List.mem_cons_self⟩
  · exact ⟨gate (selector i ab) (state i.castSucc, ab.1),
      hstep i ab List.mem_cons_self, false, List.mem_cons_self⟩

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
  simp only [CNF.eval_cons, Bool.and_eq_true,
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
  | zero => simp [pathWeight, chain, Fin.last]
  | succ m ih =>
    rw [← (Fin.consEquiv fun _ : Fin (m + 1) => Bool).sum_comp, Fintype.sum_prod_type]
    have htail (b : Bool) := ih (Fin.tail sat) b
    simp only [chain] at htail
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
      (Finset.univ.filter fun σ : Var φ → Bool => (typedQuery φ odd).eval σ = true).card :=
  CNF.modelCount_eq_card_filter id _
    (fun _ _ _ _ => ⟨fun h v _ => congrFun h v, fun h => funext fun v =>
      h v (List.mem_toFinset.mp (vars_typedQuery φ odd ▸ Finset.mem_univ v))⟩)
    (fun σ => ⟨fun hs => ⟨σ, hs, rfl⟩, fun ⟨_, hτ, h⟩ => h ▸ hτ⟩)

private theorem sum_validFlags {m : ℕ} (sat left right : Fin m → Bool) :
    (∑ f : Fin m → Choice → Bool, if ∀ i, validChoices (sat i) (left i) (right i) (f i)
      then (1 : ℤ) else 0) =
      ∏ i, (transitionWeight (sat i) (left i) (right i) : ℤ) := by
  classical
  have h := Fintype.card_congr
    (Equiv.subtypePiEquivPi (p := fun i => validChoices (sat i) (left i) (right i)))
  simp only [Fintype.card_pi, card_validChoices] at h
  rw [← Nat.cast_prod, ← h, Fintype.card_subtype, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter]
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
        exact ⟨fun h c hc => (List.mem_iff_getElem.mp hc).elim fun i ⟨hi, hci⟩ => hci ▸ h ⟨i, hi⟩,
          fun h i => h _ (List.getElem_mem _)⟩
      simp only [← h]
      change _ = if ∀ i, sat i = true then paritySign false else 0
      rw [← signedPathSum sat false]
      refine Finset.sum_congr rfl fun path _ => ?_
      cases chain false path (Fin.last φ.length) <;> simp [paritySign, sat]
    _ = _ := by
      rw [CNF.modelCount, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
      simp only [Nat.cast_one]

private def blockLabel (i offset : ℕ) : ℕ := 6 * i + offset

private def selectorOffset (ab : Choice) : ℕ := 2 + 2 * ab.1.toNat + ab.2.toNat

/-- Original variables use residue zero, states use residue one, and the four selectors use
residues two through five. The quotient holds the source label or chain index. -/
private def label {φ : CNF ℕ} : Var φ → ℕ
  | .inl v => blockLabel v.val 0
  | .inr (.inl i) => blockLabel i.val 1
  | .inr (.inr (i, ab)) => blockLabel i.val (selectorOffset ab)

private theorem label_injective (φ : CNF ℕ) : Function.Injective (label (φ := φ)) := by
  have hoff (ab : Choice) : 2 ≤ selectorOffset ab ∧ selectorOffset ab ≤ 5 := by
    rcases ab with ⟨a, b⟩
    cases a <;> cases b <;> decide
  have hoff_inj : Function.Injective selectorOffset := by
    rintro ⟨a, b⟩ ⟨c, d⟩
    cases a <;> cases b <;> cases c <;> cases d <;> decide
  rintro (v | (i | ⟨i, ab⟩)) (w | (j | ⟨j, cd⟩)) h <;>
    simp only [label, blockLabel] at h
  · exact congrArg Sum.inl (Subtype.ext (by omega))
  · omega
  · have := hoff cd
    omega
  · omega
  · exact congrArg (Sum.inr ∘ Sum.inl) (Fin.ext (by omega))
  · have := hoff cd
    omega
  · have := hoff ab
    omega
  · have := hoff ab
    omega
  · have := hoff ab
    have := hoff cd
    have hij : i = j := Fin.ext (by omega)
    have hab : ab = cd := hoff_inj (by omega)
    subst hij hab
    rfl

private theorem length_clause_typedQuery (φ : CNF ℕ) (odd : Bool) {c : Clause (Var φ)}
    (hc : c ∈ typedQuery φ odd) : c.length ≤ 2 := by
  have hstep (i : Fin φ.length) (ab : Choice) : ∀ c ∈ stepClauses φ i ab, c.length ≤ 2 := by
    simp only [stepClauses, List.mem_cons]
    rintro _ (rfl | rfl | hm)
    · exact le_rfl
    · exact le_rfl
    · split_ifs at hm with h
      · cases hm
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hm
        exact le_rfl
  simp only [typedQuery, List.mem_cons, List.mem_flatMap] at hc
  rcases hc with rfl | rfl | ⟨i, _, ab, _, hc⟩
  exacts [Nat.le_succ 1, Nat.le_succ 1, hstep i ab _ hc]

/-- The even or odd parity query, with the original variables and the chain auxiliaries assigned
disjoint natural-variable labels. `false` chooses even parity and `true` chooses odd parity. -/
def parityQuery (φ : CNF ℕ) (odd : Bool) : CNF ℕ :=
  (typedQuery φ odd).relabel label

private def indexedStep (c : Clause ℕ) (i : ℕ) (ab : Choice) : CNF ℕ :=
  let s := blockLabel i (selectorOffset ab)
  gate s (blockLabel i 1, ab.1) :: gate s (blockLabel (i + 1) 1, ab.2) ::
    (if ab.1 = ab.2 then [] else c.map fun l => gate s (blockLabel l.1 0, !l.2))

private theorem relabel_stepClauses (φ : CNF ℕ) (i : Fin φ.length) (ab : Choice) :
    (stepClauses φ i ab).relabel label = indexedStep φ[i] i.val ab := by
  simp only [stepClauses, indexedStep, CNF.relabel, List.map_cons, Clause.relabel, gate,
    state, selector, List.map_nil]
  split_ifs
  · rfl
  · let s := blockLabel i.val (selectorOffset ab)
    have ht := congrArg (List.map (fun l : Literal ℕ => [(s, false), (blockLabel l.1 0, !l.2)]))
      (List.attach_map_subtype_val φ[i])
    simp only [List.map_map, Function.comp_def] at ht
    rw [List.map_map]
    exact congrArg (fun tail =>
      [(s, false), (blockLabel i.val 1, ab.1)] ::
        [(s, false), (blockLabel (i.val + 1) 1, ab.2)] :: tail) ht

private theorem parityQuery_eq_zipIdx (φ : CNF ℕ) (odd : Bool) :
    parityQuery φ odd =
      [(blockLabel 0 1, false)] :: [(blockLabel φ.length 1, odd)] ::
        φ.zipIdx.flatMap fun ci => choices.flatMap (indexedStep ci.1 ci.2) := by
  have hzip : (List.finRange φ.length).map (fun i => (φ[i], i.val)) = φ.zipIdx :=
    List.ext_getElem (by simp) fun _ _ _ => by simp
  change (typedQuery φ odd).relabel label = _
  simp only [typedQuery, CNF.relabel, List.map_cons, List.map_flatMap]
  rw [← hzip, List.flatMap_map]
  change [(blockLabel 0 1, false)] :: [(blockLabel φ.length 1, odd)] ::
    ((List.finRange φ.length).flatMap fun i => choices.flatMap fun ab =>
      (stepClauses φ i ab).relabel label) = _
  simp only [relabel_stepClauses]

private theorem computableInPolyTime_blockLabel (offset : ℕ) :
    ComputableInPolyTime (fun i => blockLabel i offset) encNat encNat := by
  unfold blockLabel
  apply ComputableInPolyTime.binary_add' _ (ComputableInPolyTime.const offset)
  exact ComputableInPolyTime.binary_mul.comp
    ((ComputableInPolyTime.const 6).prod ComputableInPolyTime.id')

open ComputableInPolyTime in
private theorem computableInPolyTime_gate {α : Type} {input : α ↪ List Bool}
    {s : α → ℕ} {l : α → Literal ℕ} (hs : ComputableInPolyTime s input encNat)
    (hl : ComputableInPolyTime l input (encPair encNat encBool)) :
    ComputableInPolyTime (fun x => gate (s x) (l x)) input (encClause encNat) :=
  cons' (hs.prod (const false)) (cons' hl (const []))

open ComputableInPolyTime in
private theorem computableInPolyTime_flipGate :
    ComputableInPolyTime
      (fun p : ℕ × Literal ℕ => gate p.1 (blockLabel p.2.1 0, !p.2.2))
      (encPair encNat (encPair encNat encBool)) (encClause encNat) := by
  have hl := (computableInPolyTime_blockLabel 0).comp ((snd encNat (encPair encNat encBool)).fst')
  have hnot : ComputableInPolyTime Bool.not encBool encBool := of_finite _
  have hb := hnot.comp ((snd encNat (encPair encNat encBool)).snd')
  exact computableInPolyTime_gate (fst encNat _) (hl.prod hb)

/-- Encode the clause with binary variable labels, followed by its unary position. -/
private abbrev encIndexedClause : (Clause ℕ × ℕ) ↪ List Bool :=
  encPair (encClause encNat) encUnary

open ComputableInPolyTime in
private theorem computableInPolyTime_indexedStep (ab : Choice) :
    ComputableInPolyTime (fun ci : Clause ℕ × ℕ => indexedStep ci.1 ci.2 ab)
      encIndexedClause encCNF := by
  have hi := unary_to_binary.comp (snd (encClause encNat) encUnary)
  have hs : ComputableInPolyTime (fun ci => blockLabel ci.2 (selectorOffset ab))
      encIndexedClause encNat :=
    (computableInPolyTime_blockLabel (selectorOffset ab)).comp hi
  have hstart := (computableInPolyTime_blockLabel 1).comp hi
  have hend : ComputableInPolyTime (fun ci => blockLabel (ci.2 + 1) 1) encIndexedClause encNat := by
    simpa only [Function.comp_def, blockLabel, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using
      (computableInPolyTime_blockLabel 7).comp hi
  have htail : ComputableInPolyTime
      (fun ci : Clause ℕ × ℕ =>
        if ab.1 = ab.2 then [] else ci.1.map fun l =>
          gate (blockLabel ci.2 (selectorOffset ab)) (blockLabel l.1 0, !l.2))
      encIndexedClause encCNF := by
    by_cases h : ab.1 = ab.2
    · simp only [ite_eq_left h]
      exact const []
    · simp only [ite_eq_right h]
      exact mapWith computableInPolyTime_flipGate hs (fst (encClause encNat) encUnary)
  unfold indexedStep
  exact cons' (computableInPolyTime_gate hs (hstart.prod (const ab.1)))
    (cons' (computableInPolyTime_gate hs (hend.prod (const ab.2))) htail)

open ComputableInPolyTime in
/-- Each parity query is computable in polynomial time on multitape machines with binary
CNF variable labels. Only positions introduced by the list traversal use unary counters. -/
@[fun_prop]
theorem computableInPolyTime_parityQuery (odd : Bool) :
    ComputableInPolyTime (fun φ => parityQuery φ odd) encCNF encCNF := by
  simp_rw [parityQuery_eq_zipIdx]
  have hblocks : ComputableInPolyTime
      (fun ci : Clause ℕ × ℕ => choices.flatMap (indexedStep ci.1 ci.2))
      encIndexedClause encCNF :=
    flatMapConst choices (fun ab _ => computableInPolyTime_indexedStep ab)
  have hbody : ComputableInPolyTime
      (fun φ : CNF ℕ => φ.zipIdx.flatMap fun ci => choices.flatMap (indexedStep ci.1 ci.2))
      encCNF encCNF :=
    flatMapWithInput (zipIdx (encClause encNat)) (hblocks.comp (snd encCNF _))
  have hlen : ComputableInPolyTime (fun φ : CNF ℕ => φ.length) encCNF encUnary :=
    CNF.computableInPolyTime_length (V := ℕ)
      (id' : ComputableInPolyTime (fun φ : CNF ℕ => φ) encCNF (encCNFOver encNat))
  have hnum := (computableInPolyTime_blockLabel 1).comp (unary_to_binary.comp hlen)
  have hend : ComputableInPolyTime (fun φ => [(blockLabel φ.length 1, odd)])
      encCNF (encClause encNat) :=
    cons' (hnum.prod (const odd)) (const [])
  exact cons' (const [(blockLabel 0 1, false)]) (cons' hend hbody)

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

private theorem length_parityQuery_le (φ : CNF ℕ) (odd : Bool)
    (hφ : ∀ c ∈ φ, c.length ≤ 3) :
    (parityQuery φ odd).length ≤ 20 * φ.length + 2 := by
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
  simp only [parityQuery, typedQuery, CNF.relabel, List.length_map, List.length_cons]
  rw [List.length_finRange] at hblocks
  omega

/-- Both queries to count a width-three formula have linearly many vertices of the incidence
graph, measured as occurring variables plus clauses. The additive constant covers empty inputs. -/
theorem size_parityQuery_le (φ : CNF ℕ) (odd : Bool) (hφ : ∀ c ∈ φ, c.length ≤ 3) :
    (parityQuery φ odd).numVars + (parityQuery φ odd).length ≤
      60 * φ.length + 6 := by
  have hv := CNF.numVars_le_mul_length (width_parityQuery φ odd)
  have hc := length_parityQuery_le φ odd hφ
  omega

end SharpTwoSATParity

end Cslib.Complexity
