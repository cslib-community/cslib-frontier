/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.RelationAlgebra.Undecidable

/-!
# Undecidability of representability: a client

No computable Boolean function decides which tables present an atom structure whose complex
algebra is representable, with the predicate named by `AtomTable.IsRepresentable` rather than
written out as in the theorem.
-/

-- Regression examples add no public test API.
set_option linter.privateModule false

open Cslib.RelationAlgebra

example (f : AtomTable → Bool) (hf : Computable f) : ¬∀ t, f t = true ↔ t.IsRepresentable := by
  intro decides
  apply AtomTable.not_computablePred_representable_complexAlgebra
  have hp : ComputablePred fun t => f t = true := ⟨inferInstance, hf.of_eq fun _ => by simp⟩
  exact hp.of_eq decides
