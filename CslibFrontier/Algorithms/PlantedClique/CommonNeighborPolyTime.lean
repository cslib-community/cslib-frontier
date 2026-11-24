/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.PlantedClique.CommonNeighborFinal
public import CslibFrontier.Computability.Probabilistic.DistributionalSearch
import Mathlib.Tactic.Positivity

/-!
# A native polynomial-time common-neighbor solver

For each fixed seed size `s`, the actual program `commonNeighborRecover recoverInput s` has one
native polynomial-time certificate on all dense inputs. This module combines that certificate
with the common-neighbor probability theorem. The input supplies both public dimensions and
all adjacency bits; the machine constructs and reads every induced graph, computes the reduced
answer, lifts its identifiers, verifies the candidate, and writes its output list.

The seed size is fixed before choosing the machine. Runtime is polynomial in the dense input
length for each such fixed choice, with no claim of a polynomial bound in a varying input seed
size. The target schedule is supplied as public input, so an arbitrary schedule does not need
its own efficient computation. The arbitrary prior in the semantic probability law is not a
sampling primitive granted to the program.

`commonNeighborFailureBound` is the proved finite bound on the numerical recovery regime and
one elsewhere, including at dimension zero. The companion asymptotic theorem chooses a fixed
seed size from a fixed positive planted-clique constant and proves that this budget tends to
zero.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Cslib.Probability Cslib.Probability.PlantedClique Turing.MultiTapeTM
open scoped ENNReal

open scoped Classical in
/-- The proved common-neighbor failure budget on its finite numerical regime, and one on all
remaining parameters. The two summands account for the planted seed and clique uniqueness. -/
@[expose] noncomputable def commonNeighborFailureBound (n k s : ℕ) : ℝ≥0∞ :=
  if 1 ≤ n ∧ 6 ≤ k - s ∧
      1024 * Real.sqrt ((k : ℝ) + 2 * n * (2 ^ s : ℝ)⁻¹) ≤ (k - s : ℕ) then
    ENNReal.ofReal
      ((Real.exp (-2 * n * ((2 ^ s : ℝ)⁻¹) ^ 2) +
        (2 * Real.exp (-((k - s : ℕ) : ℝ)) +
          n * Real.exp (-((k - s : ℕ) : ℝ) / 32))) +
        (n * Real.exp (-(k : ℝ) / 32) +
          n.choose (k / 4) * ((2 : ℝ) ^ ((k / 4).choose 2))⁻¹))
  else 1

/-- The same fixed executable wrapper attains the all-parameter budget under every prior on
hidden sets of the public target size. -/
theorem commonNeighborRecover_failure_le {n k : ℕ}
    (prior : PMF {S : Finset (Fin n) // S.card = k}) (s : ℕ) :
    (searchProblem prior).experiment
      (fun G => PMF.pure
        (vertexSet n (commonNeighborRecover recoverInput s (RecoveryInput.ofGraph G k))))
      false ≤ commonNeighborFailureBound n k s := by
  classical
  unfold commonNeighborFailureBound
  split_ifs with h
  · exact (ENNReal.le_ofReal_iff_toReal_le
      (((searchProblem prior).experiment _).apply_ne_top false) (by positivity)).mpr
        (searchProblem_commonNeighborRecover_failure_le prior s h.1 h.2.1 h.2.2)
  · exact PMF.coe_le_one _ _

/-- For every fixed seed size, one uniform strict PPT program solves the represented
planted-clique family with the stated all-parameter failure budget. The native machine is
`fun input => pure (commonNeighborRecover recoverInput s input)` for every target schedule and
every family of priors. -/
theorem searchProblem_commonNeighbor_hasPPTSolver (s : ℕ) (k : ℕ → ℕ)
    (prior : ∀ n, PMF {S : Finset (Fin n) // S.card = k n}) :
    DistributionalSearchProblem.HasSolver (fun n => searchProblem (prior n))
      (fun (program : RecoveryInput → ProbComp (List ℕ)) n G =>
        (ProbComp.eval (program (RecoveryInput.ofGraph G (k n)))).map (vertexSet n))
      (IsPPTOn encRecoveryInput (encList encUnary))
      (fun n => commonNeighborFailureBound n (k n) s) :=
  DistributionalSearchProblem.HasSolver.of_computableInPolyTime
    (fun n => searchProblem (prior n))
    (fun n G => RecoveryInput.ofGraph G (k n)) vertexSet
    (computableInPolyTime_commonNeighborRecover s computableInPolyTime_recoverInput)
    (fun n => commonNeighborRecover_failure_le (prior n) s)

end Cslib.Algorithms.PlantedClique
