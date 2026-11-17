/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.CommunityDetection.Algorithm
public import CslibFrontier.Algorithms.IntegerPower.Program
public import CslibFrontier.Computability.PolyTime.Graph.Dense
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# A native integer-power program for community recovery

For each fixed pair of integer centering parameters, `recoverInput` is one program for every
runtime vertex count. It constructs the centered matrix in signed binary, searches integer power
columns, rounds their signs, and computes a weighted vote by stored integer matrix-vector
multiplication. Both sign decisions compare integers exactly with zero.

`recoverInput_eq_ofFn` proves that every output bit agrees with `recoverPower` on the decoded
graph. This includes malformed adjacency words, empty graphs, and the zero-vector fallback.
`computableInPolyTime_recoverInput` gives a native multitape polynomial-time certificate without
a spectral or probabilistic premise. It charges matrix construction, all growth tests and
intermediate binary integers, sign rounding, and the final vote.

The input encoding is a framed unary vertex count followed by raw adjacency bits; the output is
the framed list of Boolean labels. The fixed natural parameters are part of the chosen program,
and do not encode an uncharged real-number oracle.
-/

public section

namespace Cslib.Algorithms.CommunityDetection

open Turing.MultiTapeTM

private def integerEntry (params : PowerParameters) (x : DenseGraphInput) (i j : ℕ) : ℤ :=
  if i = j then 0 else
    if x.adjacent i j then (params.resolution : ℤ) ^ 2 - params.center else -(params.center : ℤ)

private def integerRows (params : PowerParameters) (x : DenseGraphInput) : List (List ℤ) :=
  tabulateTable x.vertexCount x.vertexCount (integerEntry params x)

private theorem integerRows_eq_ofFn (params : PowerParameters) (x : DenseGraphInput) :
    integerRows params x = List.ofFn fun i => List.ofFn (integerMatrix params x.graph i) := by
  simp only [integerRows, tabulateTable, List.map_range_eq_ofFn]
  congr 1
  funext i
  congr 1
  funext j
  simp only [integerEntry, integerMatrix, Fin.ext_iff]
  rfl

private theorem computableInPolyTime_integerRows (params : PowerParameters) :
    ComputableInPolyTime (integerRows params) encDenseGraphInput encIntTable := by
  unfold integerRows
  apply computableInPolyTime_tabulateTable
  · fun_prop
  · fun_prop
  · unfold integerEntry
    fun_prop

/-- Compute one Boolean community label per declared vertex, using exact integer powers and
one weighted-vote cleanup. The centering parameters are fixed before the input is supplied. -/
def recoverInput (params : PowerParameters) (x : DenseGraphInput) : List Bool :=
  let rows := integerRows params x
  let v := IntegerPower.recoveredIntegerVector rows (params.resolution * x.vertexCount)
  let signs := v.map fun z => if z < 0 then (-1 : ℤ) else 1
  (IntTable.mulVec rows signs).map fun z => decide (z < 0)

private theorem cast_integer_sign (z : ℤ) :
    ((if z < 0 then -1 else 1 : ℤ) : ℝ) =
      BitString.signVal (decide ((z : ℝ) < 0)) := by
  by_cases hz : z < 0 <;> simp [hz, BitString.signVal]

/-- Every native output bit equals the mathematical integer-power recovery label on the
decoded graph, without any promise on the input or parameters. -/
theorem recoverInput_eq_ofFn (params : PowerParameters) (x : DenseGraphInput) :
    recoverInput params x = List.ofFn (recoverPower params x.graph) := by
  rw [recoverInput, integerRows_eq_ofFn,
    IntegerPower.recoveredIntegerVector_ofFn (integerMatrix params x.graph), List.map_ofFn,
    IntTable.mulVec_ofFn, List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_def, recoverPower, cleanup_apply, powerLabels,
    BitString.signRound_apply]
  let M := integerMatrix params x.graph
  let v := IntegerPower.recoveredVector M (params.resolution * x.vertexCount)
  have hcast : ((∑ j, M i j * (if v j < 0 then -1 else 1 : ℤ) : ℤ) : ℝ) =
      ∑ j, (M i j : ℝ) * BitString.signVal (decide ((v j : ℝ) < 0)) := by
    simp only [Int.cast_sum, Int.cast_mul, cast_integer_sign]
  change decide ((∑ j, M i j * (if v j < 0 then -1 else 1 : ℤ)) < 0) =
    decide ((∑ j, (M i j : ℝ) * BitString.signVal (decide ((v j : ℝ) < 0))) < 0)
  rw [← hcast]
  norm_cast

/-- The program writes exactly one output bit for each declared vertex. -/
@[simp] theorem length_recoverInput (params : PowerParameters) (x : DenseGraphInput) :
    (recoverInput params x).length = x.vertexCount := by
  rw [recoverInput_eq_ofFn, List.length_ofFn]

open scoped Classical in
/-- On a canonical dense graph input, the actual output list enumerates the mathematical
recovery labels in vertex order. -/
theorem recoverInput_ofGraph (params : PowerParameters) {n : ℕ} (G : SimpleGraph (Fin n)) :
    recoverInput params (DenseGraphInput.ofGraph G) = List.ofFn (recoverPower params G) := by
  have h := recoverInput_eq_ofFn params (DenseGraphInput.ofGraph G)
  change recoverInput params (DenseGraphInput.ofGraph G) =
    List.ofFn (recoverPower params (DenseGraphInput.ofGraph G).graph) at h
  simp only [show (DenseGraphInput.ofGraph G).vertexCount = n from rfl,
    DenseGraphInput.graph_ofGraph] at h
  exact h.trans (congrArg (fun d : DecidableRel G.Adj =>
    List.ofFn (@recoverPower n params G d)) (Subsingleton.elim _ _))

/-- One native multitape machine computes community labels in polynomial time on every dense
input. Dimensions vary at runtime; matrix entries and every intermediate integer use binary
encodings, while the graph dimension and search counters use unary encodings. -/
@[fun_prop] theorem computableInPolyTime_recoverInput (params : PowerParameters) :
    ComputableInPolyTime (recoverInput params) encDenseGraphInput (encList encBool) := by
  have hrows := computableInPolyTime_integerRows params
  have hvector := IntegerPower.computableInPolyTime_recoveredIntegerVector hrows
    (show ComputableInPolyTime (fun x : DenseGraphInput => params.resolution * x.vertexCount)
      encDenseGraphInput encUnary by fun_prop)
  unfold recoverInput
  fun_prop

end Cslib.Algorithms.CommunityDetection
