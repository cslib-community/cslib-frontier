/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.HashFamily
public import Mathlib.Data.ZMod.Basic

/-!
# Changing the digest group of a Δ-universal hash family

An injective additive map `f : Y →+ Z` applied to every digest preserves `ε`-Δ-universality: the
difference of two digests is `d'` exactly when the difference of their images is `f d'`, and a
difference outside the range of `f` never occurs. A hash proved Δ-universal over a field therefore
stays Δ-universal when its digests are written as bit strings by an additive encoding, where the
difference is XOR.

Reinterpreting canonical residues modulo a larger modulus also preserves the bound when each
target difference comes from at most one integer difference of source representatives.

## Main results

* `Cslib.Probability.IsDeltaUniversalHash.postcompose`: an injective additive map on digests
  preserves `ε`-Δ-universality.
* `Cslib.Probability.IsDeltaUniversalHash.zmod_cast`: a sufficiently large target modulus
  preserves `ε`-Δ-universality when canonical residues are reinterpreted in it.
-/

public section

namespace Cslib.Probability.IsDeltaUniversalHash

open scoped ENNReal

variable {ι X Y Z : Type*} [AddGroup Y] [AddGroup Z] {seed : PMF ι} {hash : ι → X → Y}
  {ε : ℝ≥0∞}

/-- An injective additive map on digests preserves `ε`-Δ-universality. -/
theorem postcompose (hh : IsDeltaUniversalHash seed hash ε) (f : Y →+ Z)
    (hf : Function.Injective f) :
    IsDeltaUniversalHash seed (fun i x => f (hash i x)) ε := fun x x' hx d => by
  by_cases hd : ∃ d', f d' = d
  · obtain ⟨d', rfl⟩ := hd
    have hset : {i | f (hash i x) - f (hash i x') = f d'} = {i | hash i x - hash i x' = d'} := by
      ext i
      simp only [Set.mem_ofPred_eq, ← map_sub]
      exact hf.eq_iff
    rw [hset]
    exact hh x x' hx d'
  · have hset : {i | f (hash i x) - f (hash i x') = d} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, ← map_sub]
      exact fun h => hd ⟨_, h⟩
    rw [hset]
    simp

/-- Transferring canonical residues from `ZMod p` to `ZMod N` preserves the difference bound
when `N` is greater than twice the largest source representative. This gives Exercise 7.22(a)
of [BonehShoup2023], v0.6, printed p. 283, under the slightly weaker condition
`2 * (p - 1) < N` and for an arbitrary seed law. -/
theorem zmod_cast {p N : ℕ} [NeZero p] {hash : ι → X → ZMod p}
    (hh : IsDeltaUniversalHash seed hash ε) (hN : 2 * (p - 1) < N) :
    IsDeltaUniversalHash seed (fun i x => (ZMod.cast (hash i x) : ZMod N)) ε := by
  intro x x' hne d
  let diff (i : ι) : ℤ := ((hash i x).val : ℤ) - (hash i x').val
  have cast_diff (q : ℕ) (i : ι) :
      (diff i : ZMod q) = ((hash i x).val : ZMod q) - (hash i x').val := by
    simp only [diff, Int.cast_sub, Int.cast_natCast]
  simp only [ZMod.cast_eq_val, ← cast_diff N]
  by_cases hd : ∃ i, (diff i : ZMod N) = d
  · obtain ⟨j, hj⟩ := hd
    refine (seed.toOuterMeasure.mono ?_).trans (hh x x' hne (hash j x - hash j x'))
    intro i hi
    change (diff i : ZMod N) = d at hi
    have hdiv : (N : ℤ) ∣ diff j - diff i :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (hi.trans hj.symm)
    have hbounds (k : ι) : -((p : ℤ) - 1) ≤ diff k ∧ diff k ≤ (p : ℤ) - 1 := by
      have hx := ZMod.val_lt (hash k x)
      have hx' := ZMod.val_lt (hash k x')
      dsimp only [diff]
      omega
    have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
    have hlt : |diff j - diff i| < (N : ℤ) := by
      obtain ⟨hil, hiu⟩ := hbounds i
      obtain ⟨hjl, hju⟩ := hbounds j
      exact abs_lt.mpr ⟨by omega, by omega⟩
    have heq : diff i = diff j := (sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hdiv hlt)).symm
    simpa only [Set.mem_ofPred_eq, cast_diff p, ZMod.natCast_zmod_val] using
      congrArg (fun z : ℤ => (z : ZMod p)) heq
  · have hempty : {i | (diff i : ZMod N) = d} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun i hi => hd ⟨i, hi⟩
    simp [hempty]

end Cslib.Probability.IsDeltaUniversalHash
