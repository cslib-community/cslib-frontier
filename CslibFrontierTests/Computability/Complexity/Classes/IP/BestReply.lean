/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Classes.IP.AdviceProver
import CslibFrontier.Computability.Complexity.Classes.IP.BestReply

/-!
# Tests for best replies and provers computable from advice

* `Cslib.Complexity.Interaction.firstArgmax` breaks ties towards the first maximizer, returns
  `(0, 0)` on an empty range, and agrees with `Finset.sup` as `firstArgmax_snd` states;
* `Cslib.Complexity.mem_MA_of_adviceProver` has a satisfiable set of hypotheses: for the set
  `{true}` of `Bool`, the verifier `pure a` is efficient, sound against every prover (it rejects
  `false` outright), and complete for the empty-advice prover answering every message with `[]`.
  The conclusion is `{true} ∈ MA encBool`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Complexity.Classes.IP.BestReply

open Cslib.Complexity Cslib.Complexity.Interaction Cslib.Probability Turing.MultiTapeTM

/-! ### The first maximizer -/

/-- The first of two equal maxima wins: `[3, 5, 5, 1]` is maximal at index `1`, with value `5`. -/
example : firstArgmax (fun i => [3, 5, 5, 1].getD i 0) 4 = (1, 5) := by decide

/-- A later strict improvement replaces an earlier maximum. -/
example : firstArgmax (fun i => [3, 5, 5, 1, 7].getD i 0) 5 = (4, 7) := by decide

/-- The empty range gives `(0, 0)`, and a constant function is maximal at its first point. -/
example : firstArgmax (fun _ => 2) 0 = (0, 0) ∧ firstArgmax (fun _ => 2) 3 = (0, 2) := by decide

/-- The maximum of `[3, 5, 5, 1]` is that of `Finset.sup`. -/
example : (Finset.range 4).sup (fun i => [3, 5, 5, 1].getD i 0) = 5 := by
  rw [← firstArgmax_snd]
  decide

/-! ### A prover computable from advice: nonvacuity of `mem_MA_of_adviceProver` -/

/-- The verifier `pure a` accepts exactly `true`, whatever the prover answers. -/
private theorem acceptProb_pure_bool (a : Bool) (P : Prover Unit) :
    acceptProb (pure a : WordOracleComp Unit Bool) P = if a then 1 else 0 := by
  cases a
  · exact acceptProb_eq_zero P (by simp)
  · simp [acceptProb]

/-- **Every hypothesis of `mem_MA_of_adviceProver` holds** for `A = {true}`, the verifier
`pure a`, the constant prover `G = []` with empty advice, and `ℓ = ρ = 0`. -/
example : ({true} : Set Bool) ∈ MA encBool := by
  refine mem_MA_of_adviceProver (verifier := fun a => pure a) (G := fun _ => [])
    (ComputableInPolyTime.id'.isOraclePPTOn) ?_ (ComputableInPolyTime.const []) 0 0 ?_
  · intro a ha P
    obtain rfl : a = false := by simpa using ha
    simp [acceptProb_pure_bool]
  · intro a ha
    obtain rfl : a = true := ha
    refine ⟨[], by simp, by simp, ?_⟩
    simp only [acceptProb_pure_bool, ite_true]
    exact ENNReal.div_le_of_le_mul (by norm_num)

end CslibFrontierTests.Computability.Complexity.Classes.IP.BestReply
