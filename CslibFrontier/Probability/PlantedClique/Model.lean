/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Sign
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Matrix.Basic

/-!
# The planted-clique experiment

For a fixed planted set `S`, `sample S` reads independent fair bits indexed by ordered pairs,
using only the upper triangle, and makes every pair in `S` adjacent. This gives the conditional
law of `G(n, 1/2)` with `S` planted. The unused lower-triangular and diagonal bits are harmless
and allow the seed to have a simple finite product type.

`noise S` is the centered symmetric random matrix: it is zero on the diagonal and within `S`,
and otherwise equals `1` for an edge and `-1` for a nonedge.
-/

public section

namespace Cslib.Probability.PlantedClique

/-- Independent edge coins, of which only the upper triangle is read. -/
abbrev Coins (n : ℕ) := (Fin n × Fin n) → Bool

/-- Plant `S` in the graph whose independent upper-triangular edge bits are `ω`. -/
@[expose] def sample {n : ℕ} (S : Finset (Fin n)) (ω : Coins n) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ ((i ∈ S ∧ j ∈ S) ∨ ω (min i j, max i j) = true)
  symm := by
    constructor
    intro i j h
    simpa only [ne_comm, min_comm j i, max_comm j i,
      and_comm (a := j ∈ S) (b := i ∈ S)] using h
  loopless := by constructor; intro i; simp

instance {n : ℕ} (S : Finset (Fin n)) (ω : Coins n) : DecidableRel (sample S ω).Adj :=
  fun i j => inferInstanceAs (Decidable
    (i ≠ j ∧ ((i ∈ S ∧ j ∈ S) ∨ ω (min i j, max i j) = true)))

/-- The planted vertices are pairwise adjacent. -/
theorem sample_adj_of_mem {n : ℕ} (S : Finset (Fin n)) (ω : Coins n)
    {i j : Fin n} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    (sample S ω).Adj i j :=
  ⟨hij, Or.inl ⟨hi, hj⟩⟩

/-- The independent upper-triangular part of the centered noise matrix. -/
@[expose] def upperNoise {n : ℕ} (S : Finset (Fin n)) (ω : Coins n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i < j ∧ ¬(i ∈ S ∧ j ∈ S) then -BitString.signVal (ω (i, j)) else 0

/-- The centered symmetric noise, zero on the planted block and the diagonal. -/
@[expose] def noise {n : ℕ} (S : Finset (Fin n)) (ω : Coins n) :
    Matrix (Fin n) (Fin n) ℝ :=
  upperNoise S ω + (upperNoise S ω).transpose

/-- The noise is symmetric. -/
theorem noise_transpose {n : ℕ} (S : Finset (Fin n)) (ω : Coins n) :
    (noise S ω).transpose = noise S ω := by
  simp [noise, Matrix.transpose_add, add_comm]

/-- The noise diagonal vanishes. -/
@[simp] theorem noise_diag {n : ℕ} (S : Finset (Fin n)) (ω : Coins n) (i : Fin n) :
    noise S ω i i = 0 := by
  simp [noise, upperNoise]

/-- The noise vanishes on the planted block. -/
theorem noise_of_mem {n : ℕ} (S : Finset (Fin n)) (ω : Coins n)
    {i j : Fin n} (hi : i ∈ S) (hj : j ∈ S) : noise S ω i j = 0 := by
  simp [noise, upperNoise, hi, hj]

/-- Off the planted block, the centered noise reads the upper-triangular edge coin. -/
theorem noise_of_not_mem {n : ℕ} (S : Finset (Fin n)) (ω : Coins n)
    {i j : Fin n} (hij : i ≠ j) (hS : ¬(i ∈ S ∧ j ∈ S)) :
    noise S ω i j = -BitString.signVal (ω (min i j, max i j)) := by
  rcases lt_or_gt_of_ne hij with h | h
  · simp [noise, upperNoise, h, not_lt_of_ge h.le, hS, min_eq_left h.le, max_eq_right h.le]
  · have hS' : ¬(j ∈ S ∧ i ∈ S) := by simpa only [and_comm] using hS
    simp [noise, upperNoise, h, not_lt_of_ge h.le, hS', min_eq_right h.le, max_eq_left h.le]

end Cslib.Probability.PlantedClique
