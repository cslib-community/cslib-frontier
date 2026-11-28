/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.HashFamily
public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Interval

/-!
# Changing the digest group of a Δ-universal hash family

An injective additive map `f : Y →+ Z` applied to every digest preserves `ε`-Δ-universality: the
difference of two digests is `d'` exactly when the difference of their images is `f d'`, and a
difference outside the range of `f` never occurs. A hash proved Δ-universal over a field therefore
stays Δ-universal when its digests are written as bit strings by an additive encoding, where the
difference is XOR.

Reinterpreting canonical residues modulo a larger modulus also preserves the bound when each
target difference comes from at most one integer difference of source representatives.
For a smaller modulus, a union bound counts the possible source differences.

## Main results

* `Cslib.Probability.IsDeltaUniversalHash.postcompose`: an injective additive map on digests
  preserves `ε`-Δ-universality.
* `Cslib.Probability.IsDeltaUniversalHash.zmod_cast`: a sufficiently large target modulus
  preserves `ε`-Δ-universality when canonical residues are reinterpreted in it.
* `Cslib.Probability.IsDeltaUniversalHash.zmod_cast_bound` and
  `Cslib.Probability.IsDeltaUniversalHash.zmod_cast_div`: bounds after reducing canonical
  source representatives modulo the target modulus.
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
    simpa only [← map_sub, hf.eq_iff] using hh x x' hx d'
  · simp [← map_sub, not_exists.mp hd]

private theorem intCast_val_sub {p q : ℕ} (a b : ZMod p) :
    (((a.val : ℤ) - b.val : ℤ) : ZMod q) = (a.val : ZMod q) - b.val := by
  simp only [Int.cast_sub, Int.cast_natCast]

private theorem val_sub_bounds {p : ℕ} [NeZero p] (a b : ZMod p) :
    -(p : ℤ) < (a.val : ℤ) - b.val ∧ (a.val : ℤ) - b.val < p := by
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  omega

/-- Transferring canonical residues from `ZMod p` to `ZMod N` preserves the difference bound
when `N` is greater than twice the largest source representative. This gives Exercise 7.22(a)
of [BonehShoup2023], v0.6, printed p. 283, under the slightly weaker condition
`2 * (p - 1) < N` and for an arbitrary seed law. -/
theorem zmod_cast {p N : ℕ} [NeZero p] {hash : ι → X → ZMod p}
    (hh : IsDeltaUniversalHash seed hash ε) (hN : 2 * (p - 1) < N) :
    IsDeltaUniversalHash seed (fun i x => (ZMod.cast (hash i x) : ZMod N)) ε := by
  intro x x' hne d
  let diff (i : ι) : ℤ := ((hash i x).val : ℤ) - (hash i x').val
  simp only [ZMod.cast_eq_val, ← intCast_val_sub]
  change seed.toOuterMeasure {i | (diff i : ZMod N) = d} ≤ ε
  by_cases hd : ∃ i, (diff i : ZMod N) = d
  · obtain ⟨j, hj⟩ := hd
    refine (seed.toOuterMeasure.mono ?_).trans (hh x x' hne (hash j x - hash j x'))
    intro i hi
    change (diff i : ZMod N) = d at hi
    have hdiv : (N : ℤ) ∣ diff j - diff i :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (hi.trans hj.symm)
    have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
    have hlt : |diff j - diff i| < (N : ℤ) := by
      obtain ⟨hil, hiu⟩ := val_sub_bounds (hash i x) (hash i x')
      obtain ⟨hjl, hju⟩ := val_sub_bounds (hash j x) (hash j x')
      dsimp only [diff]
      exact abs_lt.mpr ⟨by omega, by omega⟩
    have heq : diff i = diff j := (sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hdiv hlt)).symm
    simpa only [diff, Set.mem_ofPred_eq, intCast_val_sub, ZMod.natCast_zmod_val] using
      congrArg (fun z : ℤ => (z : ZMod p)) heq
  · simp [not_exists.mp hd]

/-- Reducing canonical residues modulo `N` scales the difference bound by at most
`2 * (p / N + 1)`. This is the first bound of Exercise 7.22(b) ([BonehShoup2023], v0.6,
printed p. 283). The proof allows any positive moduli and any seed law. -/
theorem zmod_cast_bound {p N : ℕ} [NeZero p] [NeZero N] {hash : ι → X → ZMod p}
    (hh : IsDeltaUniversalHash seed hash ε) :
    IsDeltaUniversalHash seed (fun i x => (ZMod.cast (hash i x) : ZMod N))
      (2 * ((p : ℝ≥0∞) / N + 1) * ε) := by
  intro x x' hne d
  let diff (i : ι) : ℤ := ((hash i x).val : ℤ) - (hash i x').val
  let q : ℕ := p / N + 1
  let quotients := Finset.Ico (-(q : ℤ)) (q : ℤ)
  let events (j : ℤ) := {i | hash i x - hash i x' = (((N : ℤ) * j + d.val : ℤ) : ZMod p)}
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hN' : 0 < (N : ℤ) := by exact_mod_cast hN
  have hstep : (p : ℤ) < (q : ℤ) * N := by
    exact_mod_cast (Nat.div_lt_iff_lt_mul hN).mp (Nat.lt_succ_self (p / N))
  have hsub : {i | (ZMod.cast (hash i x) : ZMod N) - ZMod.cast (hash i x') = d} ⊆
      ⋃ j ∈ quotients, events j := by
    intro i hi
    have hcast : (diff i : ZMod N) = d := by
      simpa only [diff, intCast_val_sub, ZMod.cast_eq_val, Set.mem_ofPred_eq] using hi
    have hrem : (d.val : ℤ) = diff i % N := by rw [← hcast, ZMod.val_intCast]
    refine Set.mem_iUnion₂.mpr ⟨diff i / N, Finset.mem_Ico.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [Int.le_ediv_iff_mul_le hN', neg_mul]
      exact (neg_lt_neg hstep).le.trans (val_sub_bounds (hash i x) (hash i x')).1.le
    · rw [Int.ediv_lt_iff_lt_mul hN']
      exact (val_sub_bounds (hash i x) (hash i x')).2.trans hstep
    · change hash i x - hash i x' = (((N : ℤ) * (diff i / N) + d.val : ℤ) : ZMod p)
      rw [hrem, Int.mul_ediv_add_emod]
      simp only [diff, intCast_val_sub, ZMod.natCast_zmod_val]
  have hcard : quotients.card = 2 * q := by
    rw [Int.card_Ico]
    omega
  have hdiv : ((p / N : ℕ) : ℝ≥0∞) ≤ (p : ℝ≥0∞) / N := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (Nat.cast_ne_zero.mpr hN.ne'))
      (Or.inl (ENNReal.natCast_ne_top N)), ← Nat.cast_mul]
    exact_mod_cast Nat.div_mul_le_self p N
  calc
    _ ≤ seed.toOuterMeasure (⋃ j ∈ quotients, events j) := seed.toOuterMeasure.mono hsub
    _ ≤ ∑ j ∈ quotients, seed.toOuterMeasure (events j) :=
      MeasureTheory.measure_biUnion_finset_le quotients events
    _ ≤ ∑ j ∈ quotients, ε := Finset.sum_le_sum fun j _ => hh x x' hne _
    _ = 2 * ((p / N : ℕ) + 1 : ℕ) * ε := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
      simp only [q, Nat.cast_mul, Nat.cast_ofNat]
    _ ≤ 2 * ((p : ℝ≥0∞) / N + 1) * ε := by
      rw [Nat.cast_add, Nat.cast_one]
      gcongr

/-- A difference bound `α / p` becomes `4 * α / N` when reducing to `N ≤ p`
([BonehShoup2023], v0.6, Exercise 7.22(b), printed p. 283). -/
theorem zmod_cast_div {p N : ℕ} [NeZero p] [NeZero N] {hash : ι → X → ZMod p}
    {α : ℝ≥0∞} (hh : IsDeltaUniversalHash seed hash (α / p)) (hNp : N ≤ p) :
    IsDeltaUniversalHash seed (fun i x => (ZMod.cast (hash i x) : ZMod N)) (4 * α / N) := by
  have hN : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hp : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hone : 1 ≤ (p : ℝ≥0∞) / N := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hN) (Or.inl (ENNReal.natCast_ne_top N)), one_mul]
    exact_mod_cast hNp
  refine hh.zmod_cast_bound.mono ?_
  calc
    _ ≤ 2 * ((p : ℝ≥0∞) / N + (p : ℝ≥0∞) / N) * (α / p) := by gcongr
    _ = (4 * α / N) * ((p : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹) := by
      simp only [div_eq_mul_inv]
      ring
    _ = 4 * α / N := by rw [ENNReal.mul_inv_cancel hp (ENNReal.natCast_ne_top p), mul_one]

end Cslib.Probability.IsDeltaUniversalHash
