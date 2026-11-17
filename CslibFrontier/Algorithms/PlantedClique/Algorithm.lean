/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Finset.TopSelection
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.CliqueRecovery
public import CslibFrontier.Algorithms.IntegerPower.Basic
import Mathlib.Data.List.FinRange

/-!
# An integer matrix-power algorithm for planted clique

This file implements an exact-integer power-growth variant developed for this formalization of
the spectral recovery method of [Alon, Krivelevich, Sudakov][AlonKrivelevichSudakov1998]. Its
input is a finite simple graph and the target clique size; the hidden set is unavailable to the
algorithm.

## Relation to the source

Algorithm A in [AlonKrivelevichSudakov1998], Section 2.1, p. 3, uses the adjacency matrix's second
eigenvector for `k ≥ 10 √n`, then selects the `k` largest absolute coordinates and keeps vertices
with at least `3 k / 4` neighbors among them. Section 2.2, Propositions 2.1 and 2.3 and Lemma 2.4
(pp. 4--6), supplies its spectral analysis. Algorithm B in Section 2.3 (pp. 7--8) enumerates small
vertex sets and restricts to their common neighbors to handle every fixed positive constant in
`k ≥ c √n`. These locators refer to the author-hosted manuscript linked in the bibliography.

Our implementation retains the coordinate-selection and degree-cleanup architecture. It uses
the centered signed matrix `M = 2 A - J + I`, with zero diagonal and off-diagonal entries `1`
for an edge and `-1` otherwise. It searches standard-basis orbits through the first `n + 1`
steps for a nonzero next iterate `z = M y` satisfying `k² ‖y‖² ≤ 4 ‖z‖²`. The squared norms in
this test are integer sums. `Algorithms.IntegerPower.Basic` stores every intermediate column in
an array-backed vector and proves that its entries agree with the mathematical matrix power.

The correctness argument establishes the existence of a growing iterate through traces of
positive operator powers. A rank-one residual bound then controls the normalized output's
distance from the planted indicator. The probability argument uses scalar Rademacher tails and
finite nets. Real normalization, spectral theory, and the hidden set occur only in these proofs;
the recovery computation uses integer operations and comparisons.

## Scope of the guarantee

The companion development in `Final` proves recovery for `k ≥ 1024 √n` with failure probability
at most `2 exp (-n) + n exp (-k / 32)`, under its explicit natural-number size hypotheses.
`CommonNeighborAsymptotics` extends this integer algorithm by seed enumeration to every fixed
`c > 0`, with one native polynomial-time program whose actual recovery failure tends to zero.
`Eigenvector` and `EigenvectorFinal` separately specify Algorithm A's literal raw-adjacency
second eigenvector and prove its probability guarantee in an explicit conservative regime;
that exact spectral choice has no native finite-precision implementation here.
`Algorithms.IntegerPower.Basic` proves bounds on entry magnitudes and their binary sizes.
`Program` supplies a uniform native multitape polynomial-time
realization on dense graph inputs and proves exact agreement with `recover`. `PolyTime` connects
that one program to the distributional-search guarantee, with both size parameters supplied
at runtime and signed integer arithmetic charged in binary.

## Main definitions

* `signedAdjacency`: the integer signed adjacency matrix.
* `recover`: the complete deterministic recovery algorithm.

## References

* [N. Alon, M. Krivelevich, B. Sudakov, *Finding a large hidden clique in a random
  graph*][AlonKrivelevichSudakov1998], Sections 2.1--2.3 of the author-hosted manuscript.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Finset Matrix IntegerPower

variable {n : ℕ}

/-- The zero-diagonal signed adjacency matrix of a finite simple graph. -/
@[expose] def signedAdjacency (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i = j then 0 else if G.Adj i j then 1 else -1

/-- The `k` largest absolute coordinates of the selected integer vector. -/
@[expose] def approximateSet (M : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) : Finset (Fin n) :=
  let v := recoveredVector M k
  List.selectLargest (fun i => (v i).natAbs) k (List.finRange n)

/-- Recover a planted clique using integer matrix powers, rounding, and degree cleanup. -/
@[expose] def recover (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) : Finset (Fin n) :=
  G.recoverCliqueByDegree k (approximateSet (signedAdjacency G) k)

/-- Recovery is unchanged when its adjacency decision procedure is normalized to classical
decidability. This transports recovery events across graph representations without unfolding
the integer computation to compare decision instances. -/
theorem recover_eq_classical (G : SimpleGraph (Fin n)) (d : DecidableRel G.Adj) (k : ℕ) :
    @recover n G d k = @recover n G (Classical.decRel _) k :=
  congrArg (fun d : DecidableRel G.Adj => @recover n G d k) (Subsingleton.elim _ _)

/-- Rounding always returns exactly `k` vertices when `k ≤ n`. -/
theorem card_approximateSet (M : Matrix (Fin n) (Fin n) ℤ) {k : ℕ} (hk : k ≤ n) :
    (approximateSet M k).card = k := by
  rw [approximateSet, List.card_selectLargest _ _ (List.nodup_finRange n),
    List.length_finRange, min_eq_left hk]

/-- Selected absolute coordinates dominate every omitted absolute coordinate. -/
theorem natAbs_le_of_notMem_approximateSet (M : Matrix (Fin n) (Fin n) ℤ) (k : ℕ)
    {i j : Fin n} (hi : i ∉ approximateSet M k) (hj : j ∈ approximateSet M k) :
    (recoveredVector M k i).natAbs ≤ (recoveredVector M k j).natAbs :=
  List.weight_le_of_notMem_selectLargest (fun i => (recoveredVector M k i).natAbs)
    k (List.finRange n) (List.mem_finRange i) hi hj

/-- Every signed adjacency entry has magnitude at most one. -/
theorem natAbs_signedAdjacency_le (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (i j : Fin n) : (signedAdjacency G i j).natAbs ≤ 1 := by
  simp only [signedAdjacency]
  split_ifs <;> decide


end Cslib.Algorithms.PlantedClique
