/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.PlantedClique.Final
public import CslibFrontier.Algorithms.PlantedClique.Program
public import CslibFrontier.Algorithms.PlantedClique.Representation
public import CslibFrontier.Computability.Probabilistic.DistributionalSearch
import Mathlib.Tactic.Positivity

/-!
# A uniform polynomial-time solver for planted clique

The actual function `recoverInput` has one native `ComputableInPolyTime` certificate for all
dense inputs, including all runtime values of the vertex count and target size. This module
combines that certificate with its agreement with `recover` and the probability theorem from
`Final`. The resulting solver is the fixed program `fun input => pure (recoverInput input)`.
Neither the prior on hidden sets nor the parameter chooses a different program.

Runtime is measured in the dense encoded input: framed unary vertex count `n`, framed unary
public target size `k`, and raw adjacency bits. On a canonical graph this is exactly
`n² + 2n + 2k + 2` bits (`RecoveryInput.length_encRecoveryInput_ofGraph`), hence polynomial in
`n` when `k ≤ n`. The program computes and writes its list of vertex identifiers using
`encList encUnary`. `ofGraph` and `vertexSet` specify the meaning of these input and output
representations; they do not grant uncharged algorithms to the program.

The target schedule `k n` may be arbitrary because its value is supplied as public input. The
solver is not claimed to compute that schedule from `n`. Priors are semantic probability laws;
the result requires no efficient sampler for an arbitrary prior.

`recoveryFailureBound` is the proved exponential bound in the numerical recovery regime and
one elsewhere. Thus `searchProblem_hasPPTSolver` is a statement about every parameter, including
zero and other small dimensions. For the usual planted-clique problem, instantiate the prior
with `fun n => uniformPlantedSet n (k n) (hkn n)`, where `hkn : ∀ n, k n ≤ n`.

## Main definitions

* `recoveryFailureBound`: an all-parameter failure budget, exponential on the promise.

## Main results

* `recoverInput_failure_le`: the same represented recovery function satisfies the failure bound
  for every prior on hidden sets of the target size.
* `searchProblem_hasPPTSolver`: one uniform strict PPT program solves the whole problem family
  in the explicit dense-input and vertex-list model.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Cslib.Probability Cslib.Probability.PlantedClique Turing.MultiTapeTM
open scoped ENNReal

open scoped Classical in
/-- The proved failure bound when the numerical recovery conditions hold, and the universal
probability bound one otherwise. No incompatible assumptions are imposed on small dimensions. -/
@[expose] noncomputable def recoveryFailureBound (n k : ℕ) : ℝ≥0∞ :=
  if 1 ≤ n ∧ 6 ≤ k ∧ 1024 * Real.sqrt n ≤ (k : ℝ) then
    ENNReal.ofReal (2 * Real.exp (-(n : ℝ)) + n * Real.exp (-(k : ℝ) / 32))
  else 1

open scoped Classical in
/-- On a canonical graph input, the program's output identifiers represent exactly the set
returned by the integer matrix-power recovery algorithm. -/
theorem vertexSet_recoverInput_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    vertexSet n (recoverInput (RecoveryInput.ofGraph G k)) = recover G k := by
  have h := vertexSet_eq_of_toFinset_eq_image
    (toFinset_recoverInput (RecoveryInput.ofGraph G k))
  change vertexSet n (recoverInput (RecoveryInput.ofGraph G k)) =
    recover (RecoveryInput.ofGraph G k).graph k at h
  simp only [RecoveryInput.graph_ofGraph] at h
  exact h.trans (congrArg (fun d : DecidableRel G.Adj => @recover n G d k)
    (Subsingleton.elim _ _))

/-- The fixed executable recovery function attains the all-parameter failure budget under every
prior on hidden sets of size `k`. Only the graph and public target size are presented to it. -/
theorem recoverInput_failure_le {n k : ℕ}
    (prior : PMF {S : Finset (Fin n) // S.card = k}) :
    (searchProblem prior).experiment
      (fun G => PMF.pure (vertexSet n (recoverInput (RecoveryInput.ofGraph G k)))) false ≤
        recoveryFailureBound n k := by
  classical
  simp only [vertexSet_recoverInput_ofGraph]
  unfold recoveryFailureBound
  split_ifs with h
  · exact (ENNReal.le_ofReal_iff_toReal_le
      (((searchProblem prior).experiment _).apply_ne_top false) (by positivity)).mpr
        (searchProblem_recover_failure_le prior h.1 h.2.1 h.2.2)
  · exact PMF.coe_le_one _ _

/-- A whole planted-clique family has one uniform strict PPT solver in the dense-input and
vertex-list representation. The native certificate is uniform over both public size parameters;
the witness is `fun input => pure (recoverInput input)` for every family of priors. -/
theorem searchProblem_hasPPTSolver (k : ℕ → ℕ)
    (prior : ∀ n, PMF {S : Finset (Fin n) // S.card = k n}) :
    DistributionalSearchProblem.HasSolver (fun n => searchProblem (prior n))
      (fun (program : RecoveryInput → ProbComp (List ℕ)) n G =>
        (ProbComp.eval (program (RecoveryInput.ofGraph G (k n)))).map (vertexSet n))
      (IsPPTOn encRecoveryInput (encList encUnary))
      (fun n => recoveryFailureBound n (k n)) :=
  DistributionalSearchProblem.HasSolver.of_computableInPolyTime
    (fun n => searchProblem (prior n))
    (fun n G => RecoveryInput.ofGraph G (k n)) vertexSet
    computableInPolyTime_recoverInput (fun n => recoverInput_failure_le (prior n))

end Cslib.Algorithms.PlantedClique
