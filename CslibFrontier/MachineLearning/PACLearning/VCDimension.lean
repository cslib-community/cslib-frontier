/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.MachineLearning.PACLearning.VCDimension
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.ENat.Lattice

/-!
# Basic facts about the VC dimension

The VC dimension is the supremum of shattered cardinalities in `ℕ∞`
[ShalevShwartzBenDavid2014, Definition 6.5]. The definition `evcDim` and its order bounds
come from [cslib#966](https://github.com/leanprover/cslib/pull/966) at `18e0d4fc`.
On a class of finite VC dimension, `natCast_vcDim` identifies the natural number in the
pinned cslib API with this supremum.
-/

public section

namespace Cslib.MachineLearning.PACLearning

variable {α : Type*}

/-- The VC dimension is the supremum of the sizes of finite shattered sets. A class
shattering arbitrarily large sets has dimension `⊤` [ShalevShwartzBenDavid2014, Definition 6.5]. -/
@[expose] noncomputable def evcDim (C : ConceptClass α Bool) : ℕ∞ :=
  ⨆ W : Finset α, ⨆ _ : SetShatters C ↑W, (W.card : ℕ∞)

/-- Every shattered finite set has cardinality at most the extended VC dimension. -/
theorem SetShatters.card_le_evcDim {C : ConceptClass α Bool} {W : Finset α}
    (hW : SetShatters C ↑W) : (W.card : ℕ∞) ≤ evcDim C :=
  le_iSup₂_of_le W hW le_rfl

/-- Bounding the VC dimension amounts to bounding every finite shattered set. -/
theorem evcDim_le_iff {C : ConceptClass α Bool} {n : ℕ∞} :
    evcDim C ≤ n ↔ ∀ W : Finset α, SetShatters C ↑W → (W.card : ℕ∞) ≤ n :=
  iSup₂_le_iff

/-- A finite set shattered by a class of finite VC dimension has at most `vcDim C` elements. -/
theorem SetShatters.card_le_vcDim {C : ConceptClass α Bool} (hC : HasFiniteVCDim C)
    {W : Finset α} (hW : SetShatters C ↑W) : W.card ≤ vcDim C :=
  le_csSup hC ⟨W, rfl, hW⟩

/-- For a finite-dimensional class the natural and extended VC dimensions agree. -/
theorem natCast_vcDim {C : ConceptClass α Bool} (hC : HasFiniteVCDim C) :
    (vcDim C : ℕ∞) = evcDim C := by
  rw [vcDim, ENat.natCast_sSup hC]
  apply le_antisymm
  · exact iSup₂_le fun _ ⟨W, h, hW⟩ => h ▸ hW.card_le_evcDim
  · exact evcDim_le_iff.mpr fun W hW => le_iSup₂_of_le W.card ⟨W, rfl, hW⟩ le_rfl

/-- The extended VC dimension is infinite precisely when shattered cardinalities are unbounded. -/
theorem evcDim_eq_top_iff {C : ConceptClass α Bool} :
    evcDim C = ⊤ ↔ ¬ HasFiniteVCDim C := by
  constructor
  · intro h hC
    exact ENat.natCast_ne_top (vcDim C) ((natCast_vcDim hC).trans h)
  · contrapose!
    intro h
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
    exact hasFiniteVCDim_iff.mpr ⟨n, fun W hW => Nat.cast_le.mp (hn ▸ hW.card_le_evcDim)⟩

/-- Every class on a finite domain has finite VC dimension. -/
theorem hasFiniteVCDim_of_finite [Finite α] (C : ConceptClass α Bool) : HasFiniteVCDim C :=
  have := Fintype.ofFinite α
  hasFiniteVCDim_iff.mpr ⟨Fintype.card α, fun W _ => W.card_le_univ⟩

end Cslib.MachineLearning.PACLearning
