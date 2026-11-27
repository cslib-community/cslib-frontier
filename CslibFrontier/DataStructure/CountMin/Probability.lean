/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.CountMin.Basic
public import CslibFrontier.Probability.UniversalHash
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Data.Finset.Sampling
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Count-Min fixed-query accuracy

For a fixed insertion-only weighted stream and a fixed queried item, independently sampled
universal-hash rows give Count-Min its one-sided additive-error guarantee
[CormodeMuthukrishnan2005], Section 4.1, Theorem 1. The stream and query are fixed before the
hash seeds are sampled. This theorem makes no claim about adaptively selected queries or updates.

The collision noise in one row has mean at most total stream mass divided by the bucket count.
Markov's inequality bounds one bad row; independent uniform row seeds raise its failure bound
to the number of rows. In particular, `2 ≤ w * ε` gives failure at most `2⁻ᵈ`.

## Main results

* `Cslib.DataStructure.CountMin.expect_noise_le`: expected single-row collision noise.
* `Cslib.DataStructure.CountMin.dens_noise_gt_le`: single-row tail bound.
* `Cslib.DataStructure.CountMin.dens_estimate_gt_le`: independent-row amplification at an
  absolute threshold.
* `Cslib.DataStructure.CountMin.dens_estimate_error_le`: relative additive error for a fixed query.
* `Cslib.DataStructure.CountMin.dens_estimate_error_le_inv_two_pow`: the base-two parameter
  guarantee.

## References

* [G. Cormode, S. Muthukrishnan, *An Improved Data Stream Summary: The Count-Min Sketch
  and its Applications*][CormodeMuthukrishnan2005], Section 4.1, Theorem 1.
-/

public section

namespace Cslib.DataStructure.CountMin

open Finset Probability
open scoped BigOperators

variable {X Seed : Type*} [DecidableEq X] [Fintype Seed] [Nonempty Seed] {d w : ℕ}

/-- The expected collision noise of one universal-hash row is at most total mass divided by
the number of buckets. No finiteness assumption on the item universe is needed. -/
theorem expect_noise_le (hash : Seed → X → Fin w)
    (hh : IsTwoUniversal (PMF.uniformOfFintype Seed) hash) (s : List (X × ℕ)) (x : X) :
    (𝔼 seed, (noise (hash seed) s x : ℝ)) ≤ (mass s : ℝ) / w := by
  induction s with
  | nil => simp [noise, mass]
  | cons event s ih =>
    rcases event with ⟨y, c⟩
    simp only [noise_cons, mass_cons, Nat.cast_add, expect_add_distrib, add_div]
    refine add_le_add ?_ ih
    rcases eq_or_ne y x with rfl | hy
    · simp only [ne_eq, not_true_eq_false, false_and, ite_false, Nat.cast_zero,
        Fintype.expect_const]
      positivity
    · have hcoll : (𝔼 seed, if hash seed y = hash seed x then (1 : ℝ) else 0) ≤ (w : ℝ)⁻¹ := by
        simpa only [Fintype.card_fin] using hh.expect_boole_le hy
      calc (𝔼 seed, ((if y ≠ x ∧ hash seed y = hash seed x then c else 0 : ℕ) : ℝ))
          = (c : ℝ) * 𝔼 seed, if hash seed y = hash seed x then (1 : ℝ) else 0 := by
            rw [mul_expect]
            exact expect_congr rfl fun _ _ => by simp [hy]
        _ ≤ (c : ℝ) / w := by
            simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hcoll (Nat.cast_nonneg c)

/-- Markov's inequality bounds the fraction of seeds whose collision noise exceeds `t`. -/
theorem dens_noise_gt_le (hash : Seed → X → Fin w)
    (hh : IsTwoUniversal (PMF.uniformOfFintype Seed) hash) (s : List (X × ℕ)) (x : X)
    {t : ℝ} (ht : 0 < t) :
    (dens {seed | t < (noise (hash seed) s x : ℝ)} : ℝ) ≤ (mass s : ℝ) / (w * t) := by
  classical
  have hsub : (dens {seed | t < (noise (hash seed) s x : ℝ)} : ℝ) ≤
      dens {seed | t ≤ (noise (hash seed) s x : ℝ)} := by
    exact_mod_cast dens_mono fun _ h => by
      simp only [mem_filter, mem_univ, true_and] at h ⊢
      exact h.le
  have hbound := ((mul_le_mul_of_nonneg_left hsub ht.le).trans
    (Fintype.mul_dens_filter_le_expect (fun _ => Nat.cast_nonneg _) t)).trans
    (expect_noise_le hash hh s x)
  calc
    _ ≤ ((mass s : ℝ) / w) / t :=
      (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hbound)
    _ = _ := div_div _ _ _

/-- Count-Min can exceed a fixed absolute additive threshold only when every independent
row exceeds that threshold. -/
theorem dens_estimate_gt_le [NeZero d] (hash : Seed → X → Fin w)
    (hh : IsTwoUniversal (PMF.uniformOfFintype Seed) hash) (s : List (X × ℕ)) (x : X)
    {t : ℝ} (ht : 0 < t) :
    (dens {seeds : Fin d → Seed |
      (frequency s x : ℝ) + t <
        (estimate (fun r => hash (seeds r)) (run (fun r => hash (seeds r)) s) x : ℝ)} : ℝ) ≤
      ((mass s : ℝ) / (w * t)) ^ d := by
  classical
  let bad : Finset Seed := {seed | t < (noise (hash seed) s x : ℝ)}
  have hsub : ({seeds : Fin d → Seed | (frequency s x : ℝ) + t <
      (estimate (fun r => hash (seeds r)) (run (fun r => hash (seeds r)) s) x : ℝ)} :
        Finset (Fin d → Seed)) ⊆ Fintype.piFinset fun _ : Fin d => bad := by
    intro seeds hseeds
    simp only [mem_filter, mem_univ, true_and] at hseeds
    refine Fintype.mem_piFinset.mpr fun r => ?_
    have hrow : (estimate (fun r => hash (seeds r)) (run (fun r => hash (seeds r)) s) x : ℝ) ≤
        bucket (hash (seeds r)) s (hash (seeds r) x) := by
      exact_mod_cast estimate_run_le_bucket (fun r => hash (seeds r)) s x r
    rw [bucket_hash_eq_frequency_add_noise, Nat.cast_add] at hrow
    simp only [bad, mem_filter, mem_univ, true_and]
    linarith
  calc
    _ ≤ (dens (Fintype.piFinset fun _ : Fin d => bad) : ℝ) := by exact_mod_cast dens_mono hsub
    _ = (dens bad : ℝ) ^ d := by rw [Fintype.dens_piFinset_const, Fintype.card_fin, NNRat.cast_pow]
    _ ≤ _ := pow_le_pow_left₀ (NNRat.cast_nonneg _) (dens_noise_gt_le hash hh s x ht) d

/-- A fixed Count-Min query has additive error at most `ε * mass s` except on a fraction
`(w * ε)⁻ᵈ` of the independently sampled uniform hash banks. -/
theorem dens_estimate_error_le [NeZero d] [NeZero w] (hash : Seed → X → Fin w)
    (hh : IsTwoUniversal (PMF.uniformOfFintype Seed) hash) (s : List (X × ℕ)) (x : X)
    {ε : ℝ} (hε : 0 < ε) :
    (dens {seeds : Fin d → Seed |
      (frequency s x : ℝ) + ε * mass s <
        (estimate (fun r => hash (seeds r)) (run (fun r => hash (seeds r)) s) x : ℝ)} : ℝ) ≤
      ((w : ℝ) * ε)⁻¹ ^ d := by
  classical
  rcases eq_or_ne (mass s) 0 with hm | hm
  · have hempty : ({seeds : Fin d → Seed | (frequency s x : ℝ) + ε * mass s <
        (estimate (fun r => hash (seeds r)) (run (fun r => hash (seeds r)) s) x : ℝ)} :
          Finset (Fin d → Seed)) = ∅ := eq_empty_of_forall_notMem fun seeds hseeds => by
      simp only [mem_filter, mem_univ, true_and, hm, Nat.cast_zero, mul_zero, add_zero] at hseeds
      have hz := Nat.eq_zero_of_le_zero (hm ▸ (estimate_run_le_bucket
        (fun r => hash (seeds r)) s x 0).trans (bucket_le_mass _ s _))
      rw [hz, Nat.cast_zero] at hseeds
      exact (not_lt_of_ge (Nat.cast_nonneg _)) hseeds
    rw [hempty, dens_empty, NNRat.cast_zero]
    positivity
  · have hmpos : (0 : ℝ) < mass s := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hwpos : (0 : ℝ) < w := by exact_mod_cast NeZero.pos w
    simpa only [show (mass s : ℝ) / (w * (ε * mass s)) = ((w : ℝ) * ε)⁻¹ by field_simp] using
      dens_estimate_gt_le (d := d) hash hh s x (mul_pos hε hmpos)

/-- With at least `2 / ε` buckets, each additional independent row halves the failure bound. -/
theorem dens_estimate_error_le_inv_two_pow [NeZero d] [NeZero w]
    (hash : Seed → X → Fin w) (hh : IsTwoUniversal (PMF.uniformOfFintype Seed) hash)
    (s : List (X × ℕ)) (x : X) {ε : ℝ} (hε : 0 < ε) (hw : 2 ≤ (w : ℝ) * ε) :
    (dens {seeds : Fin d → Seed |
      (frequency s x : ℝ) + ε * mass s <
        (estimate (fun r => hash (seeds r)) (run (fun r => hash (seeds r)) s) x : ℝ)} : ℝ) ≤
      (2 ^ d : ℝ)⁻¹ := by
  refine (dens_estimate_error_le hash hh s x hε).trans ?_
  rw [← inv_pow]
  exact pow_le_pow_left₀ (by positivity) (inv_anti₀ (by norm_num) hw) d

end Cslib.DataStructure.CountMin
