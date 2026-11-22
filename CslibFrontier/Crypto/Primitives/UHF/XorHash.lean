/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.HashFamily
import CslibFrontier.Probability.Uniform
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.Abel

/-!
# Position-tagged XOR hashing with a uniform table

XOR-hash looks up each block together with its position and adds the results in a commutative
group. Addition on bit strings is XOR. The position distinguishes repeated occurrences of a
block, and the list may be empty.

The uniform-table analysis is a step in the proof of Theorem 7.6. For two distinct messages,
there is a tagged block in exactly one of them. Translating that table entry translates the
digest difference by any desired amount. The resulting difference is uniform, giving the
optimal difference and collision bounds for the ideal table. The computational PRF reduction
is tracked in #5790.

## Main definitions

* `Cslib.Crypto.UHF.xorHash`: sum the table values at the position-tagged blocks.

## Main results

* `Cslib.Crypto.UHF.uniform_xorHash_sub`: the digest difference of distinct messages is uniform.
* `Cslib.Crypto.UHF.isDeltaUniversalHash_xorHash`: the ideal table gives difference universality
  with bound `1 / |Y|`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 7.2.3, Figure 7.2 and the ideal-game step of Theorem 7.6, printed pp. 260–262.
-/

public section

namespace Cslib.Crypto.UHF

open Cslib.Probability
open scoped ENNReal symmDiff

variable {X Y : Type} {ℓ : ℕ}

private def blockAt (m : {xs : List X // xs.length ≤ ℓ}) :
    Fin m.val.length ↪ X × Fin ℓ :=
  ⟨fun i => (m.val[i], i.castLE m.property), fun i j h =>
    Fin.ext (congrArg (fun block => block.2.val) h)⟩

/-- XOR-hash from Figure 7.2 ([BonehShoup2023], v0.6, §7.2.3), with zero-based position tags.
For a fixed table `f`, the hash sums `f (mᵢ, i)` over the positions of the message. This
uses any additive commutative monoid, with bit-string addition giving the source's XOR. -/
@[expose] def xorHash [AddCommMonoid Y] (f : X × Fin ℓ → Y)
    (m : {xs : List X // xs.length ≤ ℓ}) : Y :=
  ∑ i : Fin m.val.length, f (m.val[i], i.castLE m.property)

private def taggedBlocks (m : {xs : List X // xs.length ≤ ℓ}) : Finset (X × Fin ℓ) :=
  Finset.univ.map (blockAt m)

private theorem taggedBlocks_injective :
    Function.Injective (taggedBlocks (X := X) (ℓ := ℓ)) := by
  intro m m' h
  have hlen : m.val.length = m'.val.length := by
    simpa only [taggedBlocks, Finset.card_map, Finset.card_univ, Fintype.card_fin] using
      congrArg Finset.card h
  refine Subtype.ext (List.ext_getElem hlen fun i hi _ => ?_)
  have hm : blockAt m ⟨i, hi⟩ ∈ taggedBlocks m :=
    Finset.mem_map.mpr ⟨_, Finset.mem_univ _, rfl⟩
  rw [h] at hm
  obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hm
  have hjval : j.val = i := congrArg (fun block => block.2.val) hj
  have hblock : m'.val[j] = m.val[i] := congrArg Prod.fst hj
  simpa only [Fin.getElem_fin, hjval] using hblock.symm

/-- A step in the ideal-game analysis of Theorem 7.6 ([BonehShoup2023], v0.6, pp. 261–262).
With an independent uniform value at every tagged position, two distinct messages have a
uniform digest difference. This applies to arbitrary finite additive commutative digests. -/
theorem uniform_xorHash_sub [Fintype X] [DecidableEq X] [Fintype Y] [AddCommGroup Y]
    {m m' : {xs : List X // xs.length ≤ ℓ}} (hne : m ≠ m') :
    (PMF.uniformOfFintype (X × Fin ℓ → Y)).map
      (fun f => xorHash f m - xorHash f m') = PMF.uniformOfFintype Y := by
  let s := taggedBlocks m
  let t := taggedBlocks m'
  have hst : s ≠ t := taggedBlocks_injective.ne hne
  have hsum (f : X × Fin ℓ → Y) (msg : {xs : List X // xs.length ≤ ℓ}) :
      xorHash f msg = ∑ i ∈ taggedBlocks msg, f i := by
    rw [taggedBlocks, Finset.sum_map]
    rfl
  let difference : (X × Fin ℓ → Y) →+ Y :=
    { toFun := fun f => (∑ i ∈ s, f i) - ∑ i ∈ t, f i
      map_zero' := by simp
      map_add' := by
        intro f g
        simp only [Pi.add_apply, Finset.sum_add_distrib]
        abel }
  simp only [hsum]
  apply PMF.uniformOfFintype_map_addHom difference
  intro c
  obtain ⟨i, hi⟩ := Finset.symmDiff_nonempty.mpr hst
  refine ⟨Pi.single i (if i ∈ s then c else -c), ?_⟩
  rcases Finset.mem_symmDiff.mp hi with ⟨his, hit⟩ | ⟨hit, his⟩ <;>
    simp [difference, Finset.sum_pi_single', his, hit]

/-- An ideal uniform table gives XOR-hash difference universality with bound `1 / |Y|`. -/
theorem isDeltaUniversalHash_xorHash [Fintype X] [DecidableEq X] [Fintype Y] [AddCommGroup Y] :
    IsDeltaUniversalHash (PMF.uniformOfFintype (X × Fin ℓ → Y))
      xorHash (Fintype.card Y : ℝ≥0∞)⁻¹ :=
  IsDeltaUniversalHash.of_map_sub_eq_uniform fun _ _ hne => uniform_xorHash_sub hne

end Cslib.Crypto.UHF
