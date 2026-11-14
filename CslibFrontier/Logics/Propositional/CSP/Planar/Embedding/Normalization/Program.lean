/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Normalization.Cap

/-!
# Ordered witnesses for the literal normalization program

Each instruction constructs the numerical witness of its exact existing interpreter body.
Rotation preserves chirality, adjacent reduction uses the explicit wrap map, and a guarded
cap hides exactly one port before the old auxiliaries. No target witness is supplied.
-/

public section

namespace Cslib.Logic.PL.CSP.Normalization

open Cslib.Complexity.CSP.OrderedBoundary

/-- Execute a normalization program on an actual source gadget witness. The result is
the witness of `Program.gadget` itself, with its original scope order and auxiliary layout.
The alphabet need not be finite; body occurrences may repeat and components may be disconnected. -/
noncomputable def Program.orderedWitness {Rel : Type} {ar : Rel → ℕ}
    {s : Rel → List Bool → Bool} :
    {n m : ℕ} → (p : Program n m) → {P : Set (Fin n → Bool)} →
      {g : PPGadget ar s P} → GadgetWitness g → GadgetWitness (p.gadget g)
  | _, _, .done _, _, _, w => w
  | _, _, .rotate e rest, _, _, w => rest.orderedWitness (w.normalizationRotate e)
  | _, _, .zero i rest, _, _, w => rest.orderedWitness (w.normalizationZero i)
  | _, _, .cap large rest, _, _, w => rest.orderedWitness (w.normalizationCap large)

end Cslib.Logic.PL.CSP.Normalization
