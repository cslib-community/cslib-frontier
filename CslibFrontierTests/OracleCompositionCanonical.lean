/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
import CslibFrontier.Tactic.PolyTime

/-!
# Canonical plain numerical oracle-composition clients

The clients retain an arbitrary caller beside a fair bit, select whether to query a stateful
oracle, and run a captured-input loop with a concrete invariant and encoded-state bound.
-/

public section

namespace CslibFrontierTests.OracleCompositionCanonical

open Cslib Cslib.Probability Turing Turing.MultiTapeTM

-- No transitional callback spelling is part of this ordinary-module facade.
assert_not_exists Cslib.Probability.IsOraclePPTOn.query_take'
assert_not_exists Cslib.Probability.IsOraclePPTOn.map_with'
assert_not_exists Cslib.Probability.IsOraclePPTOn.iterateWith_spec'
assert_not_exists Cslib.Probability.IsTidyOraclePPTOn
assert_not_exists Turing.MultiTapePTM.Internal.Oracle.IsTidyOraclePPTOn

/-- A computed callback retains the entire caller beside the sampled bit. -/
noncomputable def retainedBit (word : List Bool) : WordOracleComp Unit (List Bool × Bool) :=
  (fun bit => (word, bit)) <$> ProbOracleComp.sample (ProbComp.uniform Bool)

example : IsOraclePPTOn encBits (encPair encBits encBool) retainedBit :=
  (isPPTOn_uniform_bool encBits).isOraclePPTOn.map_with
    (f := fun word bit => (word, bit)) ComputableInPolyTime.id'

/-- The first caller bit selects one external query or a pure empty result. -/
noncomputable def selectedRequest (word : List Bool) : WordOracleComp Unit (List Bool) :=
  if word.headD false then List.take 1 <$> ProbOracleComp.query ((), word) else pure []

example : IsOraclePPTOn encBits encBits selectedRequest :=
  IsOraclePPTOn.cond (by fun_prop)
    (IsOraclePPTOn.query_take () ComputableInPolyTime.id' (.const 1))
    (ComputableInPolyTime.const []).isOraclePPTOn

/-- A concrete stateful oracle counts the selected calls and echoes the request. -/
noncomputable def echoCount (request : Unit × List Bool) : StateT ℕ PMF (List Bool) :=
  fun calls => PMF.pure (request.2, calls + 1)

-- The unselected branch makes no call. The selected branch reads only the charged prefix and
-- keeps the updated external state; neither certificate assumes a global reply-length bound.
example : ProbOracleComp.runWith echoCount (selectedRequest []) 0 = PMF.pure ([], 0) := by
  simp [selectedRequest]

example : ProbOracleComp.runWith echoCount (selectedRequest [true, false]) 0 =
    PMF.pure ([true], 1) := by
  simp [selectedRequest, echoCount]

/-- A captured caller selects sampling or retention of the current loop state. -/
noncomputable def sampledStep (word : List Bool) (state : Bool) : WordOracleComp Unit Bool :=
  if word.headD false then ProbOracleComp.sample (ProbComp.uniform Bool) else pure state

theorem sampledStep_isOraclePPTOn : IsOraclePPTOn (encPair encBits encBool) encBool
    (fun pair => sampledStep pair.1 pair.2) :=
  IsOraclePPTOn.cond (by fun_prop)
    (isPPTOn_uniform_bool (encPair encBits encBool)).isOraclePPTOn
    (ComputableInPolyTime.snd encBits encBool).isOraclePPTOn

/-- Counted iteration keeps every state at the fixed one-bit encoding size. -/
noncomputable def sampledLoop (word : List Bool) : WordOracleComp Unit Bool :=
  OracleComp.iterate word.length (sampledStep word) false

example : IsOraclePPTOn encBits encBool sampledLoop := by
  exact (IsOraclePPTOn.iterateWith_spec ComputableInPolyTime.length_bits (.const false)
    sampledStep_isOraclePPTOn
    (fun word _ state => word.headD false = false → state = false)
    (fun _ _ => rfl) (by
      intro word _ state _ hstate next hnext hfalse
      have hstep : sampledStep word state = pure state := by
        unfold sampledStep
        rw [hfalse]
        rfl
      have hnext : next = state := by simpa [hstep] using hnext
      subst next
      exact hstate hfalse)
    (size := fun _ => 1) (.const 1) (fun _ _ _ _ _ => by simp)).1

-- Zero rounds return the initial state without private sampling or external queries.
example : sampledLoop [] = pure false := rfl

example : ProbOracleComp.runWith echoCount (sampledLoop []) 7 = PMF.pure (false, 7) := by
  simp [sampledLoop]

end CslibFrontierTests.OracleCompositionCanonical
