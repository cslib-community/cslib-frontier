/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.ExactThree
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Function.Basic

/-!
# Exact-three distinct-variable formulas with three occurrences are satisfiable

Hall's theorem chooses a different representative variable for every clause. Setting each
representative to satisfy its clause is consistent even with arbitrary literal signs.

This is Tovey's tractable boundary, recalled in [Berman, Karpinski and Scott, §1, pp. 1–2 of
the linked preprint][BermanKarpinskiScott2007]. The Lean version uses lists, counts repeated
clauses separately, permits unused variables, and assumes at most three occurrences per variable.
Each clause has exactly three distinct variables. No computational bound for constructing the
matching or satisfying assignment is asserted here.

## Main results

* `CNF.satisfiable_of_exactThreeDistinct_of_count_le_three`.
-/

public section

namespace Cslib.Logic.PL.CNF

variable {V : Type*} [DecidableEq V]

private theorem countP_mem_vars_le_count_vars (φ : CNF V) (v : V) :
    φ.countP (fun c => decide (v ∈ c.map Prod.fst)) ≤ φ.vars.count v := by
  induction φ with
  | nil => simp [CNF.vars]
  | cons c φ ih =>
    have hvars : (CNF.vars (c :: φ)).count v =
        (c.map Prod.fst).count v + (CNF.vars φ).count v := by
      simp [CNF.vars]
    rw [hvars]
    by_cases hv : v ∈ c.map Prod.fst
    · have := List.count_pos_iff.mpr hv
      simp only [List.countP_cons, hv, decide_true, ↓reduceIte]; omega
    · simp only [List.countP_cons, hv, decide_false, Bool.false_eq_true, ↓reduceIte]; omega

private theorem card_filter_get_mem_eq_countP (φ : CNF V) (v : V) :
    (Finset.univ.filter (fun i : Fin φ.length => v ∈ (φ.get i).map Prod.fst)).card =
      φ.countP (fun c => decide (v ∈ c.map Prod.fst)) := by
  calc
    _ = (List.finRange φ.length).countP (fun i => decide (v ∈ (φ.get i).map Prod.fst)) := by
      rw [← List.toFinset_finRange, (List.nodup_finRange φ.length).card_eq_countP]
    _ = φ.countP (fun c => decide (v ∈ c.map Prod.fst)) := by
      conv_rhs => rw [← List.ofFn_get φ, List.ofFn_eq_map, List.countP_map]
      rfl

/-- Exact-three clauses on distinct variables with at most three occurrences per variable
are always satisfiable. Binary clauses are excluded from this statement. -/
theorem satisfiable_of_exactThreeDistinct_of_count_le_three
    {φ : CNF V} (hw : φ.IsExactThreeDistinct) (ho : ∀ v, φ.vars.count v ≤ 3) :
    φ.Satisfiable := by
  classical
  let I := Fin φ.length
  let t : I → Finset V := fun i => ((φ.get i).map Prod.fst).toFinset
  let r : I → V → Prop := fun i v => v ∈ t i
  have ht (i : I) : (t i).card = 3 := by
    have hc := hw (φ.get i) (List.get_mem _ _)
    change ((φ.get i).map Prod.fst).toFinset.card = 3
    rw [List.toFinset_card_of_nodup hc.2, List.length_map, hc.1]
  have hall (s : Finset I) : s.card ≤ (s.biUnion t).card := by
    have hleft (i : I) (hi : i ∈ s) : 3 ≤ ((s.biUnion t).bipartiteAbove r i).card := by
      have he : (s.biUnion t).bipartiteAbove r i = t i := by
        ext v
        simp only [Finset.mem_bipartiteAbove, r, Finset.mem_biUnion]
        exact ⟨fun h => h.2, fun hv => ⟨⟨i, hi, hv⟩, hv⟩⟩
      rw [he]
      exact (ht i).symm.le
    have hright (v : V) (_ : v ∈ s.biUnion t) : (s.bipartiteBelow r v).card ≤ 3 :=
      calc
        (s.bipartiteBelow r v).card ≤ (Finset.univ.filter fun i : I => v ∈ t i).card :=
          Finset.card_le_card fun _ hi =>
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
        _ = φ.countP (fun c => decide (v ∈ c.map Prod.fst)) := by
          simpa only [t, List.mem_toFinset] using card_filter_get_mem_eq_countP φ v
        _ ≤ φ.vars.count v := countP_mem_vars_le_count_vars φ v
        _ ≤ 3 := ho v
    have := Finset.card_mul_le_card_mul r hleft hright
    omega
  obtain ⟨f, hf, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hall
  have hlit (i : I) : ∃ b : Bool, (f i, b) ∈ φ.get i := by
    obtain ⟨⟨v, b⟩, hb, hv⟩ := List.mem_map.mp (List.mem_toFinset.mp (hmem i))
    exact ⟨b, hv ▸ hb⟩
  choose b hb using hlit
  refine ⟨Function.extend f b fun _ => false, (CNF.eval_eq_true_iff _ φ).mpr fun c hc => ?_⟩
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hc
  exact (Clause.eval_eq_true_iff _ (φ.get i)).mpr ⟨(f i, b i), hb i, hf.extend_apply b _ i⟩

end Cslib.Logic.PL.CNF
