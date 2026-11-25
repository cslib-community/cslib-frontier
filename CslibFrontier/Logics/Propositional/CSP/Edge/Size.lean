/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Occurrence
public import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.BigOperators
import CslibFrontier.Foundations.Data.List.Blocks
import CslibFrontier.Foundations.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite size accounting for edge CSPs

Every edge variable has two positional occurrences. Positive-scope constraints are therefore
bounded by twice the number of occurring variables. Nullary constraints are retained in the
instance but excluded from this count, as required for the recursion argument in Corollary 27
of [KazdaKolmogorovRolinek2018], arXiv:1602.03124v6, printed p. 13.
-/

public section

namespace Cslib.Logic.PL.CSP

open Finset

variable {Rel V : Type*} [DecidableEq V] {F : CSP Rel V}

/-- Constraints with positive scope, retaining positional multiplicity. -/
@[expose] def positiveCount (F : CSP Rel V) : ℕ :=
  (F.filter fun c => !c.scope.isEmpty).length

omit [DecidableEq V] in
/-- The number of positions is the cardinality of the original dependent occurrence type. -/
theorem card_occurrence (F : CSP Rel V) : Fintype.card (Occurrence F) = F.vars.length := by
  simp only [Occurrence, Fintype.card_sigma, Fintype.card_fin, ← List.sum_ofFn,
    List.ofFn_getElem_eq_map F (fun c => c.scope.length), vars, List.length_flatMap]

/-- Counting a variable in the occurrence list counts its actual positional fiber. -/
theorem card_occurrences_var (F : CSP Rel V) (v : V) :
    ((univ : Finset (Occurrence F)).filter fun o => o.var = v).card = F.vars.count v := by
  have hlocal (s : List V) : (∑ j : Fin s.length, if s[j.val] = v then 1 else 0) = s.count v := by
    have he : (List.ofFn fun j : Fin s.length => s[j.val]) = s := by simp
    simpa only [he, List.count_eq_countP, beq_iff_eq, card_filter] using
      (List.countP_ofFn (fun j : Fin s.length => s[j.val]) (· == v)).symm
  rw [card_filter, Fintype.sum_sigma]
  refine (sum_congr rfl fun i _ => hlocal _).trans ?_
  simp only [vars, List.count_flatMap, Function.comp_def,
    ← List.ofFn_getElem_eq_map F (fun c => c.scope.count v), List.sum_ofFn]

/-- The two endpoints are exactly the finite fiber over an occurring edge variable. -/
theorem EdgeInstance.card_occurrences_var (hF : EdgeInstance F) (v : V)
    (hv : v ∈ F.vars.toFinset) :
    ((univ : Finset (Occurrence F)).filter fun o => o.var = v).card = 2 := by
  obtain ⟨o, rfl⟩ := (exists_occurrence_iff v).mpr (List.mem_toFinset.mp hv)
  suffices ((univ : Finset (Occurrence F)).filter fun p => p.var = o.var) = {o, hF.partner o} by
    simp [this, hF.partner_ne o]
  ext p; simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  exact ⟨hF.eq_or_eq_partner, by rintro (rfl | rfl); exacts [rfl, (hF.partner_variable o).symm]⟩

/-- Every occurring edge variable appears exactly twice in the original occurrence list. -/
theorem EdgeInstance.count_vars (hF : EdgeInstance F) {v : V} (hv : v ∈ F.vars) :
    F.vars.count v = 2 := by
  rw [← Cslib.Logic.PL.CSP.card_occurrences_var F v]
  exact hF.card_occurrences_var v (List.mem_toFinset.mpr hv)

omit [DecidableEq V] in
/-- Every actual scope of an edge instance has distinct variable names. -/
theorem EdgeInstance.scope_nodup (hF : EdgeInstance F) (i : Fin F.length) :
    F[i.val].scope.Nodup :=
  List.nodup_iff_injective_get.mpr fun _ _ he =>
    eq_of_heq (Sigma.mk.inj_iff.mp (hF.eq_of_constraint_eq he rfl)).2

/-- Distinct scope names and exactly two occurrences characterize an edge instance.
The count ranges over the actual finite occurrence list, not a declared variable universe. -/
theorem edgeInstance_of_count_vars
    (hs : ∀ i : Fin F.length, F[i.val].scope.Nodup)
    (hc : ∀ v ∈ F.vars, F.vars.count v = 2) : EdgeInstance F := by
  have hinj : ∀ o p : Occurrence F, o.var = p.var → o.1 = p.1 → o = p := by
    rintro ⟨i, j⟩ ⟨_, l⟩ hv rfl
    exact congrArg (Sigma.mk i) ((hs i).injective_get hv)
  intro o
  obtain ⟨a, b, hab, he⟩ := card_eq_two.mp
    ((card_occurrences_var F o.var).trans (hc _ o.var_mem))
  have hmem (p : Occurrence F) : p ∈ ({a, b} : Finset _) ↔ p.var = o.var := by
    rw [← he]; simp
  have ha : a.var = o.var := (hmem a).mp (mem_insert_self a {b})
  have hb : b.var = o.var := (hmem b).mp (mem_insert_of_mem (mem_singleton_self b))
  rcases mem_insert.mp ((hmem o).mpr rfl) with rfl | ho
  · exact ⟨b, fun hi => hab (hinj o b hb.symm hi), hb.symm, fun p hp =>
      by simpa using (hmem p).mpr hp⟩
  · obtain rfl := mem_singleton.mp ho
    exact ⟨a, fun hi => hab (hinj a o ha hi.symm), ha.symm, fun p hp =>
      (by simpa using (hmem p).mpr hp : p = a ∨ p = o).symm⟩

/-- Exactly two occurrences per occurring variable, without a finite ambient universe. -/
theorem EdgeInstance.length_vars_eq_two_mul_numVars (hF : EdgeInstance F) :
    F.vars.length = 2 * F.numVars := by
  rw [← card_occurrence, ← card_univ,
    card_eq_sum_card_fiberwise fun a _ => List.mem_toFinset.mpr a.var_mem,
    sum_congr rfl hF.card_occurrences_var]
  simp [numVars, mul_comm]

omit [DecidableEq V] in
/-- Every positive-scope constraint spends at least one actual positional occurrence. -/
theorem positiveCount_le_length_vars (F : CSP Rel V) : F.positiveCount ≤ F.vars.length := by
  induction F with
  | nil => simp [positiveCount, vars]
  | cons c F ih =>
    by_cases he : c.scope = []
    · simpa [positiveCount, vars, he] using ih
    · have := List.length_pos_iff.mpr he
      simp only [positiveCount, List.filter_cons, vars, List.flatMap_cons, List.length_append,
        List.isEmpty_eq_false_iff.mpr he, Bool.not_false, ite_true, List.length_cons] at ih ⊢
      omega

/-- The positive constraint count is bounded even when nullary constraints are present. -/
theorem EdgeInstance.positiveCount_le (hF : EdgeInstance F) : F.positiveCount ≤ 2 * F.numVars :=
  (positiveCount_le_length_vars F).trans_eq hF.length_vars_eq_two_mul_numVars

/-- The finite recursion resource counts occurring variables and positive-scope constraints. -/
@[expose] def contractionMeasure (F : CSP Rel V) : ℕ := 2 * F.numVars - F.positiveCount

end Cslib.Logic.PL.CSP
