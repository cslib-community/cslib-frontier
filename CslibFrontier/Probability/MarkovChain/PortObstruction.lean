/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.MetricReplacement
public import CslibFrontier.Foundations.Geometry.CAT0.Basic
import CslibFrontier.Foundations.Combinatorics.Expander.LowerBound
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Probability.MarkovChain.RotationSmoothing

/-!
# A size obstruction for graphs without metric ports

An indexed family of target spaces admits ports if graphs of unbounded order and uniformly
bounded degree have one squared-distance Poincaré bound throughout the family. A single large
graph with too small a bound generates ports. Smooth a predecessor with a lazy walk, realize
the average on the prescribed label set, and put a copy of the given graph at every vertex.
The replacement estimate returns the same bound, while the order multiplies at every step.

This is a clean-room derivation of the finite amplification argument in
[OpenAI2026HamiltonianPermanent, Theorem 4.2]. The labels used to realize the averaged walk give
an explicit cardinal estimate with base `8 * d`. The class-of-spaces definition is that of
[OpenAI2026EuclideanSpectrum, Definition 11.1]. A common finite label set is equivalent to
uniformly bounded degree for a family of unbounded order, by the finite pigeonhole principle.
-/

public section

namespace Cslib.RotationMap

open Finset Cslib.Probability Cslib.Probability.MarkovChain
open scoped BigOperators

/-- An indexed family of spaces admits ports if regular graphs of arbitrarily large order
and one finite degree have a common squared-distance Poincaré bound in every member. -/
@[expose] def HasPorts {ι : Type*} (X : ι → Type*) [∀ i, MetricSpace (X i)] : Prop :=
  ∃ (D : Type) (_ : Fintype D) (_ : Nonempty D) (b : ℝ), 0 ≤ b ∧
    ∀ n : ℕ, ∃ (V : Type) (_ : Fintype V) (_ : Nonempty V) (G : RotationMap V D),
      n ≤ Fintype.card V ∧ ∀ i, G.HasPoincareBound (X i) b

private theorem crossEnergy_complete {V X : Type*} [Fintype V] [Nonempty V] [MetricSpace X]
    (f : V → X) :
    crossEnergy (PMF.uniformOfFintype V) (complete V).randomWalk f f =
      𝔼 i, 𝔼 j, dist (f i) (f j) ^ 2 := by
  rw [crossEnergy_uniform_randomWalk, Fintype.expect_prod_type]
  rfl

variable {ι : Type*} {X : ι → Type*} [∀ i, MetricSpace (X i)] [∀ i, CompleteCAT0Space (X i)]
  {S D : Type} [Fintype S] [Nonempty S] [Fintype D] [Nonempty D] (H : RotationMap S D)

/-- A regular graph of order at least `(8d)^(2s)` and uniform Poincaré bound `b` produces ports
for a family of complete CAT(0) spaces whenever `s ≥ 7000(1+b)`. -/
theorem hasPorts_of_card_ge_pow {s : ℕ} {b : ℝ} (hb : 0 ≤ b) (hS : 2 ≤ Fintype.card S)
    (hH : ∀ i, H.HasPoincareBound (X i) b) (ht : 7000 * (1 + b) ≤ (s : ℝ))
    (hcard : (8 * Fintype.card D) ^ (2 * s) ≤ Fintype.card S) : HasPorts X := by
  let c : ℝ := 6948 * (1 + b)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hs : 0 < s := by exact_mod_cast (by linarith : (0 : ℝ) < s)
  have hr : c / (2 * s) ≤ 2 := (div_le_iff₀ (by positivity)).mpr (by dsimp [c]; linarith)
  have hcap : (4 * Fintype.card (D ⊕ D)) ^ (s + s) ≤ Fintype.card S := by
    simpa only [Fintype.card_sum, ← two_mul, ← Nat.mul_assoc, Nat.reduceMul] using hcard
  have build (k : ℕ) : ∃ (V : Type) (_ : Fintype V) (_ : Nonempty V)
      (G : RotationMap V (D ⊕ D)), Fintype.card S ^ k ≤ Fintype.card V ∧
        ∀ i, G.HasPoincareBound (X i) c := by
    induction k with
    | zero =>
      refine ⟨Unit, inferInstance, inferInstance, loops Unit (D ⊕ D), by simp, fun i f => ?_⟩
      simp [loops]
    | succ k ih =>
      obtain ⟨V, iV, nV, G, hv, hG⟩ := ih
      obtain ⟨R, hR⟩ := G.exists_padded_lazy_cesaro (T := S) (by lia : 0 < s + s) hcap
      refine ⟨V × S, inferInstance, inferInstance, R.balancedReplacement H, ?_, fun i f => ?_⟩
      · rw [pow_succ, Fintype.card_prod]
        exact Nat.mul_le_mul_right _ hv
      have hR' : R.HasPoincareBound (X i) 192 := by
        intro y
        have hz (z : V → X i) : crossEnergy (PMF.uniformOfFintype V) (complete V).randomWalk z z ≤
            c * crossEnergy (PMF.uniformOfFintype V) G.randomWalk z z := by
          rw [crossEnergy_complete, G.crossEnergy_uniform_randomWalk]
          exact hG i z
        have h := G.comparison_of_padded_cesaro R hs hR G.isStationary_uniform_randomWalk
          (complete V).isStationary_uniform_randomWalk hz y
        rw [crossEnergy_complete, R.crossEnergy_uniform_randomWalk, max_eq_left hr] at h
        simpa only [show (96 : ℝ) * 2 = 192 by norm_num] using h
      exact (R.expect_dist_sq_balancedReplacement H (by norm_num) hb hR' (hH i) f).trans_eq
        (by dsimp [c]; ring)
  refine ⟨D ⊕ D, inferInstance, inferInstance, c, hc, fun n => ?_⟩
  obtain ⟨V, iV, nV, G, hv, hG⟩ := build n
  exact ⟨V, iV, nV, G, (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hS n)).trans hv, hG⟩

/-- Without ports, the order of a graph is at most exponential in its Poincaré bound times
the logarithm of its degree. This form retains the integer iteration scale exactly. -/
theorem card_lt_pow_of_not_hasPorts {b : ℝ} (hb : 0 ≤ b) (hS : 2 ≤ Fintype.card S)
    (hH : ∀ i, H.HasPoincareBound (X i) b) (hno : ¬HasPorts X) :
    Fintype.card S < (8 * Fintype.card D) ^ (2 * ⌈7000 * (1 + b)⌉₊) :=
  lt_of_not_ge fun h => hno (H.hasPorts_of_card_ge_pow hb hS hH (Nat.le_ceil _) h)

end Cslib.RotationMap
