/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.RewriteTable
import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Problem
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Finite-table compilation, both rule directions, and the standard finite-map PT interface. -/

open Cslib.Complexity.NCL HWord.RewriteGadget Cslib.PostCorrespondence

namespace CslibFrontierTests.RewriteTable

private def rules (d : Domino Bool) : Prop := d = ⟨[false, false], [true, false]⟩

private theorem rules_finite : {d | rules d}.Finite :=
  Set.finite_singleton _

private theorem rules_shape (d : Domino Bool) (hd : rules d) :
    ∃ a b c e, d.top = [a, b] ∧ d.bottom = [c, e] ∧ (a = c ∨ b = e) := by
  cases hd
  exact ⟨false, false, true, false, rfl, rfl, Or.inr rfl⟩

private noncomputable def table : RuleTable rules :=
  RuleTable.ofFinite rules rules_finite rules_shape

example : Relation.ReflTransGen (Rewrites (RuleSet table.entries))
    ([false, false].map (Fintype.equivFin Bool)) ([true, false].map (Fintype.equivFin Bool)) :=
  (table.reachable_iff _ _).mp (.single
    ⟨[], ⟨[false, false], [true, false]⟩, [], Or.inl rfl, rfl, rfl⟩)

example : Relation.ReflTransGen (Rewrites (RuleSet table.entries))
    ([true, false].map (Fintype.equivFin Bool)) ([false, false].map (Fintype.equivFin Bool)) :=
  (table.reachable_iff _ _).mp (.single
    ⟨[], ⟨[true, false], [false, false]⟩, [], Or.inr rfl, rfl, rfl⟩)

open _root_.Turing.MultiTapeTM

example : ComputableInPolyTime (List.map (Fintype.equivFin Bool))
    (encList (encFinite Bool)) (HWord.encWord (Fintype.card Bool)) :=
  (ComputableInPolyTime.of_finite _).map

end CslibFrontierTests.RewriteTable
