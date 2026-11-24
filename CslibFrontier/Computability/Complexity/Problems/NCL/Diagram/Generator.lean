/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Implements

/-!
# Changing the generator alphabet

## Main definitions

* `Cslib.Complexity.NCL.Diagram.OpenSim.genOfVerts`: the identity open simulation between
  generators with equal vertex data, even in different alphabets.
-/

public section

namespace Cslib.Complexity.NCL.Diagram

variable {Γ Γ' : List Color → List Color → Type} {I : Interp Γ} {I' : Interp Γ'}
  {a b : List Color}

/-- Generators with identical vertex data implement one another along the identity boundary map. -/
@[expose] def OpenSim.genOfVerts (g : Γ a b) (g' : Γ' a b) (hv : I.verts g = I'.verts g') :
    OpenSim I I' (gen g) (gen g') :=
  have hl : ∀ s : Fin a.length ⊕ Fin b.length → Bool,
      ((gen g).graph I).Legal s ↔ ((gen g').graph I').Legal s := fun s => by
    calc
      _ ↔ GenLegal I g s := (genLegal_iff g s).symm
      _ ↔ GenLegal I' g' s := by unfold GenLegal; rw [hv]
      _ ↔ _ := genLegal_iff g' s
  { ι := _root_.id
    ι_injective := Function.injective_id
    ι_top _ := rfl
    ι_bottom _ := rfl
    enc := _root_.id
    enc_ι _ _ := rfl
    sound ht := (hl _).2 ht
    legal_enc hs := (hl _).1 hs
    lift _ _ hs' := ⟨_, .refl, (hl _).1 hs', .refl⟩ }

end Cslib.Complexity.NCL.Diagram
