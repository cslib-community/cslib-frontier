/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Matrix.Block
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import CslibFrontier.Foundations.Data.ZMod.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Finite abelian Fourier blocks

A block records the splitting field hypothesis, an enumeration of the group and its
characters, and a forward or inverse transform. Independent blocks share one matrix format.
For a cyclic group, enumerating the characters by powers of a primitive root recovers the DFT.

Adapted from `Transform`, `Cyclic` and `Batched` of the Lean release accompanying
[OpenAI2026FiniteFourier], Theorem 1.1.
-/

public section

namespace Cslib.Circuit.Linear

universe u v

noncomputable section

section Characters

/-- A multiplicative character of a group written additively. -/
abbrev Character (G K : Type*) [AddCommGroup G] [Field K] := Multiplicative G →* Kˣ

variable (G K : Type*) [AddCommGroup G] [Field K]

/-- Fourier matrix in the positive-character convention. -/
@[expose] def fourierMatrix : Matrix (Character G K) G K :=
  Matrix.of fun χ g => (χ (Multiplicative.ofAdd g) : K)

variable [Fintype G]

/-- The order is invertible and the field contains a primitive root of the group exponent. -/
@[expose] def Admissible : Prop :=
  (Fintype.card G : K) ≠ 0 ∧ ∃ ζ : K, IsPrimitiveRoot ζ (AddMonoid.exponent G)

noncomputable instance characterFintype : Fintype (Character G K) := Fintype.ofFinite _

/-- The inverse Fourier matrix has negative-character entries scaled by `1/|G|`. -/
@[expose] def inverseFourierMatrix : Matrix G (Character G K) K :=
  Matrix.of fun g χ => (Fintype.card G : K)⁻¹ * (χ (Multiplicative.ofAdd (-g)) : K)

/-- Under the splitting hypothesis the character group has the same order as the group. -/
theorem card_character (h : Admissible G K) : Fintype.card (Character G K) = Fintype.card G := by
  let : HasEnoughRootsOfUnity K (Monoid.exponent (Multiplicative G)) :=
    ⟨h.2, rootsOfUnity.isCyclic _ _⟩
  simpa [Nat.card_eq_fintype_card] using
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Multiplicative G) K

end Characters

section Cyclic

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] {ζ : K}

/-- A primitive root of order `n` gives the manuscript's splitting hypothesis for `ZMod n`. -/
theorem admissible_zmod (hζ : IsPrimitiveRoot ζ n) : Admissible (ZMod n) K := by
  rw [Admissible, ZMod.card, ZMod.exponent]
  exact ⟨hζ.neZero'.out, ζ, hζ⟩

private noncomputable def cyclicCharacter (hζ : IsPrimitiveRoot ζ n) (j : Fin n) :
    Character (ZMod n) K :=
  (AddChar.zmodChar n ((mem_rootsOfUnity n hζ.toRootsOfUnity.val).mp
    hζ.toRootsOfUnity.property)).toMonoidHom ^ j.val

private theorem cyclicCharacter_natCast (hζ : IsPrimitiveRoot ζ n) (j : Fin n) (a : ℕ) :
    (cyclicCharacter hζ j (Multiplicative.ofAdd (a : ZMod n)) : K) = ζ ^ (j.val * a) := by
  simp only [cyclicCharacter, MonoidHom.pow_apply, AddChar.toMonoidHom_apply,
    toAdd_ofAdd, AddChar.zmodChar_apply', Units.val_pow_eq_pow_val,
    hζ.val_toRootsOfUnity_coe, ← pow_mul, Nat.mul_comm a j.val]

/-- Frequency `j` indexes the character `g ↦ ζ^(j*g)`. -/
noncomputable def cyclicCharacterEquiv (hζ : IsPrimitiveRoot ζ n) :
    Fin n ≃ Character (ZMod n) K :=
  Equiv.ofBijective (cyclicCharacter hζ) <|
    (Fintype.bijective_iff_injective_and_card _).2 ⟨by
      intro i j hij
      have he := congrArg (fun χ : Character (ZMod n) K =>
        (χ (Multiplicative.ofAdd ((1 : ℕ) : ZMod n)) : K)) hij
      rw [cyclicCharacter_natCast, cyclicCharacter_natCast, Nat.mul_one, Nat.mul_one] at he
      exact Fin.ext (hζ.pow_inj i.isLt j.isLt he), by
      rw [Fintype.card_fin, card_character _ _ (admissible_zmod hζ), ZMod.card]⟩

/-- The positive-sign Fourier matrix of order `n`, in the chosen primitive root. -/
@[expose] def dftMatrix {R : Type*} [Monoid R] (n : ℕ) (ζ : R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun j a => ζ ^ (j.val * a.val)

/-- In cyclic frequency order the character table is the positive-sign DFT. -/
theorem reindex_fourierMatrix_zmod (hζ : IsPrimitiveRoot ζ n) :
    Matrix.reindex (cyclicCharacterEquiv hζ).symm (ZMod.finEquiv n).toEquiv.symm
      (fourierMatrix (ZMod n) K) = dftMatrix n ζ := by
  ext j a
  change (cyclicCharacter hζ j (Multiplicative.ofAdd (ZMod.finEquiv n a)) : K) = _
  rw [ZMod.finEquiv_eq_natCast, cyclicCharacter_natCast]
  rfl

end Cyclic

/-- One order-`n` transform over a common splitting field, in arbitrary coordinates. -/
structure FourierBlock (K : Type v) [Field K] (n : ℕ) where
  /-- Underlying group. -/
  G : Type u
  /-- Addition on the group. -/
  [group : AddCommGroup G]
  /-- Enumeration of all group elements. -/
  [finiteGroup : Fintype G]
  /-- The scalar field splits the group and its order is invertible. -/
  admissible : Admissible G K
  /-- Coordinates of the group elements. -/
  points : Fin n ≃ G
  /-- Coordinates of the characters. -/
  frequencies : Fin n ≃ Character G K
  /-- Select the normalized inverse transform when true. -/
  inverse : Bool

attribute [instance] FourierBlock.group FourierBlock.finiteGroup

variable {K : Type v} [Field K] {n J : ℕ}

namespace FourierBlock

/-- The selected forward or normalized inverse transform in the given coordinates. -/
@[expose] def matrix (B : FourierBlock K n) : Matrix (Fin n) (Fin n) K :=
  if B.inverse then
    Matrix.reindex B.points.symm B.frequencies.symm (inverseFourierMatrix B.G K)
  else
    Matrix.reindex B.frequencies.symm B.points.symm (fourierMatrix B.G K)

end FourierBlock

/-- The direct sum of the selected transforms. Circuit gates may mix all batch indices. -/
@[expose] def batchMatrix (B : Fin J → FourierBlock K n) :
    Matrix (Fin n × Fin J) (Fin n × Fin J) K :=
  Matrix.blockDiagonal (fun j => (B j).matrix)

end

end Cslib.Circuit.Linear
