/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: local-only (test)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Crypto.Protocols.UC.PPT.Execution
import CslibFrontierTests.Crypto.UCPPTLink

/-!
# Tests for `UC.PPT.Execution`

End-to-end execution witness for `CslibFrontier.Crypto.Protocols.UC.PPT.Execution`:
`windowEnv` writes `(0, true)` and polls `(1, false)`, outputting `decide (polled ≠ some [])`.
`windowExec_isPPT` instantiates `isPPT_exec`, `Environment.IsPPT.isPPT_run`, and
`Machine.isReplyBounded_id`; `windowExec_eval` checks that the output law is
`PMF.pure (decide (0 < κ))`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.UCPPTExecution

open Cslib Cslib.Crypto.Protocols.UC Cslib.Probability Turing.MultiTapeTM
open CslibFrontierTests.Crypto.UCPPT CslibFrontierTests.Crypto.UCPPTLink

/-- Environment writing `(0, true)` and polling `(1, false)`, returning
`decide (polled ≠ some [])`. -/
private def windowEnv :
    Environment 2 Bool (List Bool) (RoutedNetQ 2 Bool Unit) (RoutedNetR (List Bool) Unit) :=
  fun _ _ => do
    let _ ← ProbOracleComp.query (Sum.inl ((0 : Fin 2), true))
    let polled ← ProbOracleComp.query (Sum.inl ((1 : Fin 2), false))
    return decide (polled ≠ some [])

/-- `windowEnv` is uniform strict oracle PPT (`Environment.IsPPT`). -/
theorem windowEnv_isPPT :
    windowEnv.IsPPT coinPartyPort (WordPort.sum coinPartyPort unitPort) := by
  let iE := WordInterface.exec coinPartyPort (WordPort.sum coinPartyPort unitPort)
  let sp := execSpec 2 Bool (List Bool) (RoutedNetQ 2 Bool Unit) (RoutedNetR (List Bool) Unit)
  have hq (q : (Fin 2 × Bool) ⊕ RoutedNetQ 2 Bool Unit) :
      IsOraclePPTOn encEnvParam encBits fun e : EnvParam =>
        iE.reply q <$> ProbOracleComp.lowerWith iE e.replyBound
          (ProbOracleComp.query (spec := sp) q) :=
    iE.isOraclePPTOn_lowerWith_query (query := fun _ => q) (limit := EnvParam.replyBound)
      (ComputableInPolyTime.const _) (ComputableInPolyTime.const _) (by fun_prop)
  have hpost : ComputableInPolyTime
      (fun w : List Bool => decide (coinPartyPort.replyDecoder.decode w ≠ some []))
      encBits encBool := by
    have hpos : ComputableInPolyTime (fun k : ℕ => decide (0 < k)) encUnary encBool := by fun_prop
    have hlist : ComputableInPolyTime
        (fun w : List Bool => (coinPartyPort.replyDecoder.decode w).getD [true]) encBits encBits :=
      (ComputableInPolyTime.optionGetD encBits).comp
        (coinPartyPort.replyDecoder.computableInPolyTime.prod (ComputableInPolyTime.const [true]))
    have heq : ((fun k : ℕ => decide (0 < k)) ∘ (fun l : List Bool => (encBits l).length) ∘
        fun w : List Bool => (coinPartyPort.replyDecoder.decode w).getD [true]) =
        fun w : List Bool => decide (coinPartyPort.replyDecoder.decode w ≠ some []) := by
      funext w; simp only [Function.comp_apply, encBits_apply, decide_eq_decide]
      rcases coinPartyPort.replyDecoder.decode w with _ | ⟨_ | ⟨_, _⟩⟩ <;> simp
    exact heq ▸ hpos.comp ((ComputableInPolyTime.encoding_length encBits).comp hlist)
  let qPoll : (Fin 2 × Bool) ⊕ RoutedNetQ 2 Bool Unit := Sum.inl ((1 : Fin 2), false)
  have h12 := (hq (Sum.inl ((0 : Fin 2), true))).bind_with
    (second := fun e _ => iE.reply qPoll <$> ProbOracleComp.lowerWith iE e.replyBound
      (ProbOracleComp.query qPoll))
    ((hq qPoll).preprocess (ComputableInPolyTime.fst encEnvParam encBits))
  have hdec (r : Option (List Bool)) :
      coinPartyPort.replyDecoder.decode (iE.reply (Sum.inl ((1 : Fin 2), false)) r) = r :=
    coinPartyPort.replyDecoder.decode_enc r
  refine (h12.map hpost).congr fun e State oracle s => ?_
  simp only [windowEnv, iE, qPoll, ProbOracleComp.lowerWith, ProbOracleComp.simulate_bind,
    ProbOracleComp.simulate_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, hdec]

/-- End-to-end execution of `windowProtocol`, `dummyAdversary`, and `windowEnv` is `IsPPT`. -/
theorem windowExec_isPPT :
    Cslib.Probability.IsPPT encBool
      (fun κ z => exec windowProtocol (dummyAdversary 2 _ _) ∅ windowEnv κ z) :=
  isPPT_exec (WordPort.computable_partyIndex coinInputPort) windowProtocol_isPPT
    windowProtocol_isReplyBounded (Adversary.isPPT_dummyAdversary 2 _)
    (Machine.isReplyBounded_id _) windowEnv_isPPT ∅

/-- Observable, `κ`-dependent execution output: party `0` stores `[true ^^ c]` and party `1` polls
`take κ [true ^^ c]`, which is non-empty iff `0 < κ`. -/
theorem windowExec_eval (κ : ℕ) (z : List Bool) :
    ProbComp.eval (exec windowProtocol (dummyAdversary 2 _ _) ∅ windowEnv κ z) =
      PMF.pure (decide (0 < κ)) := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  rw [exec_dummyAdversary]
  simp only [Machine.run, Machine.link, windowEnv, corruptRouter, windowProtocol,
    ProbOracleComp.sample_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, Machine.runFrom_bind, Machine.runFrom_query, Machine.runFrom_pure,
    StateT.run, Finset.notMem_empty, ↓reduceIte, h10, Machine.closeProgram_bind,
    Machine.closeProgram_sample, Machine.closeProgram_pure, ProbComp.eval_bind, ProbComp.eval_pure]
  have htake (c : Bool) : decide (some (List.take κ [true ^^ c]) ≠ some []) = decide (0 < κ) := by
    cases κ <;> rfl
  simp only [htake, PMF.bind_const]

end CslibFrontierTests.Crypto.UCPPTExecution
