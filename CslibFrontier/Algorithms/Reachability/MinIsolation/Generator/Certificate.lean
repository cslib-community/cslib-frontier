/-
Copyright (c) 2026 Christian Reitwiessner, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator.WeightDimensions
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Native min-isolating weight generator

Hoza's Justesen family uses a logarithmic-length seed and assigns polynomially bounded
vertex weights. The family contains a min-isolating assignment for every simple layered
digraph. One native deterministic machine computes the same weights in logarithmic space
from the dimensions, seed and vertex, without needing the graph as input.

## Main results

* `Cslib.Reachability.Hoza.generatedWeight_certified`: the joint isolation, size and
  native workspace guarantees of [Hoza2026NLUL, Theorem 1.3].
-/

public section

namespace Cslib.Reachability.Hoza

open Cslib.Code.JustesenFamily SeedWeight.Dimensions Turing Turing.MultiTapeTM

/-- Hoza's min-isolating generator [Theorem 1.3][Hoza2026NLUL] on a rectangular layered
vertex set `Fin (n + 1) × Fin w`. Each edge advances one layer, and path weights sum internal
vertices. For every graph there is a seed that min-isolates all reachable pairs. Every seed
has the same dimension-dependent length and gives polynomially bounded weights. One finite
deterministic multitape machine computes the weight at any valid vertex from binary dimensions
and coordinates and a seed in index order. Workspace counts visited work-tape cells. -/
theorem generatedWeight_certified :
    ∃ (seedFactor weightDegree spaceFactor : ℕ) (time : Input → ℕ) (k : ℕ)
      (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State),
      ∀ w n : ℕ,
        let N := w * (n + 1)
        codeLength w n ≤ seedFactor * (Nat.log2 N + 1) ∧
        (∀ (G : LayeredDigraph (Fin (n + 1) × Fin w)), (∀ z, G.layer z = z.1.val) →
          ∃ seed, G.IsMinIsolating (generatedWeight seed)) ∧
        ∀ (seed : Fin (codeLength w n) → Bool) (z : Fin (n + 1) × Fin w),
          let input := canonicalInput seed z
          generatedWeight seed z < (2 * (N + 1)) ^ weightDegree ∧
          tm.ComputesInTimeAndSpace (encInput input) (encNat (generatedWeight seed z))
            (time input) (spaceFactor * (Nat.log2 N + 1)) := by
  obtain ⟨degree, hweight⟩ := generatedWeight_polynomial
  obtain ⟨time, C, k, State, finite, tm, hrun⟩ := generatedWeight_computesInTimeAndSpace
  refine ⟨268435456, degree, C * 5, time, k, State, finite, tm, fun w n => ?_⟩
  intro N
  refine ⟨?_, exists_generatedWeight_isMinIsolating, fun seed z => ⟨hweight w n seed z, ?_⟩⟩
  · simpa only [N, Nat.log2_eq_log_two] using (codeLength_bounds w n).2
  have hw : w ≤ N := Nat.le_mul_of_pos_right _ (Nat.succ_pos n)
  have hn : n ≤ N := by
    have hpos : 0 < w := lt_of_le_of_lt (Nat.zero_le z.2.val) z.2.isLt
    calc
      n ≤ n + 1 := Nat.le_succ n
      _ ≤ N := Nat.le_mul_of_pos_left _ hpos
  have hdim : (encPair encNat encNat (w, n)).length + 1 ≤ 5 * (Nat.log2 N + 1) := by
    have hwLength := length_encNat_le_log2 hw
    have hnLength := length_encNat_le_log2 hn
    rw [length_encPair]
    change 2 * (encNat w).length + 1 + (encNat n).length + 1 ≤ _
    omega
  obtain ⟨⟨houtput, htime, hspace⟩, _⟩ := hrun seed z
  exact ⟨houtput, htime, hspace.mono (by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left C hdim)⟩

end Cslib.Reachability.Hoza
