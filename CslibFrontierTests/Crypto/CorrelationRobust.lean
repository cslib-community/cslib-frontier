/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.CorrelationRobust
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Product
import CslibFrontier.Tactic.PPT

/-!
# Correlation robustness is not vacuous

The constant hash, which answers every word with `false`, is not correlation robust. With one
query per level, its real game hands a distinguisher the output bit `false`, while the ideal game
hands it a uniform bit. The distinguisher `firstBitZero` accepts when the first output bit is
`false`. It is PPT, and its advantage is `1 / 2` at every level.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.CorrelationRobust

open Cslib Cslib.Probability Cslib.Crypto Turing.MultiTapeTM

/-- The constant hash: every word hashes to `false`. -/
def constHash : List Bool → Bool := fun _ => false

/-- One query at every level. -/
abbrev oneQuery : ℕ → ℕ := fun _ => 1

theorem oneQuery_polynomiallyBounded : PolynomiallyBounded oneQuery :=
  ⟨0, Filter.Eventually.of_forall fun _ => le_rfl⟩

/-- Accept when the first output bit is `false`. -/
noncomputable def firstBitZero : CorrelationRobust.Distinguisher oneQuery :=
  fun _ p => pure !(p.2 0)

theorem firstBitZero_isPPT : firstBitZero.IsPPT := by
  have hout : ComputableInPolyTime
      (fun x : CorrelationRobust.Input oneQuery => encBitString (oneQuery x.level) x.outputs)
      (CorrelationRobust.encInput oneQuery) encBits :=
    CorrelationRobust.encInput_outputs_polyTime oneQuery .id'
  have hbit : ComputableInPolyTime
      (fun x : CorrelationRobust.Input oneQuery =>
        !((encBitString (oneQuery x.level) x.outputs).headD true))
      (CorrelationRobust.encInput oneQuery) encBool :=
    ComputableInPolyTime.bool_not.comp
      ((ComputableInPolyTime.headD (encA := encBool) (encL := encBits) true).comp hout)
  refine hbit.isPPTOn.congr fun x => ?_
  simp [firstBitZero, List.ofFn_succ]

/-- Against the constant hash `firstBitZero` always accepts. -/
theorem realGame_firstBitZero (k : ℕ) :
    CorrelationRobust.realGame (CorrelationRobust.atLevel constHash k (oneQuery k))
      (firstBitZero k) = PMF.pure true := by
  simp only [CorrelationRobust.realGame, CorrelationRobust.atLevel, constHash, firstBitZero,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, Bool.not_false, PMF.bind_const]

/-- Against uniform output bits `firstBitZero` accepts with probability `1 / 2`. -/
theorem idealGame_firstBitZero (k : ℕ) :
    CorrelationRobust.idealGame (firstBitZero k) = PMF.uniformOfFintype Bool := by
  have hbit : (PMF.uniformOfFintype (BitString (oneQuery k))).map (fun u => u 0) =
      PMF.uniformOfFintype Bool := by
    rw [← Cslib.Probability.PMF.pi_uniformOfFintype, Cslib.Probability.PMF.pi_map_eval]
  have hnot : (PMF.uniformOfFintype Bool).map Bool.not = PMF.uniformOfFintype Bool := by
    ext b
    cases b <;> simp [PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply]
  simp only [CorrelationRobust.idealGame, firstBitZero, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure, PMF.bind_const]
  rw [← hnot, ← hbit, PMF.map_comp, ← PMF.bind_pure_comp]
  rfl

/-- **The constant hash is not correlation robust**: with one query per level, `firstBitZero` is
PPT and its advantage is `1 / 2` at every level. -/
theorem not_correlationRobust_constHash : ¬ CorrelationRobust constHash := by
  intro h
  have hneg := h.secure oneQuery oneQuery_polynomiallyBounded firstBitZero firstBitZero_isPPT
  simp only [realGame_firstBitZero, idealGame_firstBitZero] at hneg
  refine not_negligible_const ?_ hneg
  norm_num [Game.advantage, Game.succProbability, PMF.uniformOfFintype_apply,
    ENNReal.toNNReal_ofNat]

end CslibFrontierTests.Crypto.CorrelationRobust
