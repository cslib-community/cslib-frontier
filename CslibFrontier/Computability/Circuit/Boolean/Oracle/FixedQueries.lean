/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Oracle.Selection
import CslibFrontier.Computability.Circuit.Boolean.Simps

/-!
# Oracle circuits with fixed queries

An oracle circuit makes *fixed queries* when the words it asks the oracle about do not depend on
its input. `Boolean.fixedQueryCircuit pts c` asks the oracle about the `N` fixed words `pts`, then
runs the De Morgan circuit `c` on the answers followed by its input
(`Boolean.eval_fixedQueryCircuit`). It has `N` oracle gates, all at oracle depth one, so it is
non-adaptive in the sense of the adaptivity measure of
[Chen et al., Definition 11, p. 13][ChenHiraharaOliveiraPichRajgopalSanthanam2020]:
no oracle gate reads the answer of another. Its other gates are the two constant gates of
`Boolean.constLayer` and the gates of `c`.

## Main definitions

* `Cslib.Circuits.Boolean.fixedQueryCircuit`: fixed oracle queries followed by a De Morgan circuit.

## Main results

* `Cslib.Circuits.Boolean.eval_fixedQueryCircuit`: the circuit runs `c` on the answers and the
  input.
* `Cslib.Circuits.Boolean.size_fixedQueryCircuit`,
  `Cslib.Circuits.Boolean.cost_program_fixedQueryCircuit`,
  `Cslib.Circuits.Boolean.depthWith_fixedQueryCircuit_le`,
  `Cslib.Circuits.Boolean.fanInAtMost_fixedQueryCircuit`: it has `c.size + N + 2` gates, `N` of
  them oracle gates, oracle depth at most one and fan-in at most `max w 2`.

## References

* [L. Chen, S. Hirahara, I. C. Oliveira, J. Pich, N. Rajgopal and R. Santhanam, *Beyond Natural
  Proofs: Hardness Magnification and Locality*][ChenHiraharaOliveiraPichRajgopalSanthanam2020]
-/

public section

namespace Cslib.Circuits.Boolean

variable {n N w : ℕ}

/-- **Fixed oracle queries**: ask the oracle about the words `pts`, then run the De Morgan circuit
`c` on the `N` answers followed by the input. -/
def fixedQueryCircuit (pts : Fin N → BitString w) (c : Circuit signature (N + n) 1) :
    Circuit oracleSignature n 1 :=
  (c.mapOp toOracle).comp
    (((queryLayer fun i a => .inr (pts i a)).append
      (Circuit.wiring oracleSignature fun i => Source.idx (K := n) (.inl i))).comp (constLayer n))

/-- Under the oracle `O`, `fixedQueryCircuit pts c` runs `c` on the answers of `O` at the words
`pts`, followed by the input. -/
@[simp] theorem eval_fixedQueryCircuit (pts : Fin N → BitString w) (c : Circuit signature (N + n) 1)
    (O : Language Bool) (x : BitString n) :
    (fixedQueryCircuit pts c).eval (oracleInterpretation O) x =
      c.eval interpretation (Fin.append (fun i => O.slice w (pts i)) x) := by
  simp only [circuit_simps, fixedQueryCircuit, Circuit.eval_mapOp (I := interpretation)]
  congr 1
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Fin.append_left, eval_queryLayer]
    rfl
  · simp only [Fin.append_right, Function.comp_apply, eval_constLayer_idx]
    rfl

@[simp] theorem size_fixedQueryCircuit (pts : Fin N → BitString w)
    (c : Circuit signature (N + n) 1) : (fixedQueryCircuit pts c).size = c.size + N + 2 := by
  simp only [circuit_simps, fixedQueryCircuit, size_queryLayer, size_constLayer]
  omega

/-- The circuit has `N` oracle gates. -/
@[simp] theorem cost_program_fixedQueryCircuit (pts : Fin N → BitString w)
    (c : Circuit signature (N + n) 1) :
    (fixedQueryCircuit pts c).program.cost OracleOp.queryWeight = N := by
  simp only [circuit_simps, fixedQueryCircuit]
  simp

/-- The circuit has at most one oracle gate on any path: its queries are fixed. -/
theorem depthWith_fixedQueryCircuit_le (pts : Fin N → BitString w)
    (c : Circuit signature (N + n) 1) :
    (fixedQueryCircuit pts c).depthWith OracleOp.queryWeight ≤ 1 := by
  circuit_bound [fixedQueryCircuit, depthWith_mapOp_toOracle, depthWith_constLayer]

/-- The circuit has fan-in at most `max w 2`: its oracle gates have `w` arguments. -/
theorem fanInAtMost_fixedQueryCircuit (pts : Fin N → BitString w)
    (c : Circuit signature (N + n) 1) : (fixedQueryCircuit pts c).FanInAtMost (max w 2) :=
  ((Circuit.fanInAtMost_mapOp _ _).2 ((Circuit.fanInAtMost_two _).mono (le_max_right _ _))).comp <|
    (((fanInAtMost_queryLayer _).mono (le_max_left _ _)).append
      (Circuit.fanInAtMost_wiring _ _)).comp (fanInAtMost_constLayer _ _)

end Cslib.Circuits.Boolean
