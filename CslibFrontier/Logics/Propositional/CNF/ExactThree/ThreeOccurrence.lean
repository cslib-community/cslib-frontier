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
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Card
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
    rw [List.countP_cons, hvars, Nat.add_comm ((c.map Prod.fst).count v)]
    refine Nat.add_le_add ih ?_
    split
    · rename_i hv
      exact List.count_pos_iff.mpr (of_decide_eq_true hv)
    · exact Nat.zero_le _

private theorem card_filter_get_mem_eq_countP (φ : CNF V) (v : V) :
    (Finset.univ.filter (fun i : Fin φ.length => v ∈ (φ.get i).map Prod.fst)).card =
      φ.countP (fun c => decide (v ∈ c.map Prod.fst)) := by
  simpa only [List.ofFn_get, decide_eq_true_eq] using
    (List.countP_ofFn φ.get (fun c => decide (v ∈ c.map Prod.fst))).symm

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
  have hall : ∀ s : Finset I, s.card ≤ (s.biUnion t).card := by
    intro s
    have hleft : ∀ i ∈ s, 3 ≤ ((s.biUnion t).bipartiteAbove r i).card := by
      intro i hi
      change 3 ≤ ((s.biUnion t).filter (· ∈ t i)).card
      rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (Finset.subset_biUnion_of_mem t hi)]
      exact (ht i).ge
    have hright : ∀ v ∈ s.biUnion t, (s.bipartiteBelow r v).card ≤ 3 := by
      intro v _
      calc
        (s.bipartiteBelow r v).card
            ≤ (Finset.univ.filter (fun i : I => v ∈ t i)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ s))
        _ = φ.countP (fun c => decide (v ∈ c.map Prod.fst)) :=
          by simpa only [t, List.mem_toFinset] using card_filter_get_mem_eq_countP φ v
        _ ≤ φ.vars.count v := countP_mem_vars_le_count_vars φ v
        _ ≤ 3 := ho v
    exact Nat.le_of_mul_le_mul_right (Finset.card_mul_le_card_mul r hleft hright) (by decide)
  obtain ⟨f, hf, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hall
  have hlit : ∀ i : I, ∃ b : Bool, (f i, b) ∈ φ.get i := by
    intro i
    have hm : f i ∈ (φ.get i).map Prod.fst := List.mem_toFinset.mp (hmem i)
    obtain ⟨⟨v, b⟩, hb, hv⟩ := List.mem_map.mp hm
    exact ⟨b, hv ▸ hb⟩
  choose b hb using hlit
  let σ : V → Bool := Function.extend f b (fun _ => false)
  refine ⟨σ, (CNF.eval_eq_true_iff σ φ).mpr ?_⟩
  intro c hc
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hc
  apply (Clause.eval_eq_true_iff σ (φ.get i)).mpr
  exact ⟨(f i, b i), hb i, hf.extend_apply b (fun _ => false) i⟩

end Cslib.Logic.PL.CNF
