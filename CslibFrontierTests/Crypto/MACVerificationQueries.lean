/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test suite)

import CslibFrontier.Crypto.Computational.MAC.VerificationQueries
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime.Init

set_option linter.privateModule false

/-!
# Tests for MAC security with verification queries

Exercises the finite (`Cslib.Crypto.vqForgeExperiment`) and computational
(`Cslib.Crypto.MACScheme.sufCmaVqGame`, `Cslib.Crypto.MACScheme.SUFCMAVq`) Attack Game 6.2,
Theorem 6.1, and Exercise 6.2 APIs as an ordinary `module` client, including concrete boundary
witnesses:

* **`Q_v = 0` boundary:** an adversary making signing queries and zero verification queries wins
  with probability `0` in both `vqForgeExperiment` and `sufCmaVqGame`, even when `verify` accepts
  every tag.
* **Replayed signed pair `(m, t) ∈ log`:** submitting a pair returned by an earlier signing query to
  the verification oracle returns `true` (`[true]`) without latching `won = true`; an adversary that
  branches on that `[true]` reply and would otherwise submit a fresh valid forgery still wins with
  probability `0`.
* **Randomized multi-tag MAC witness:** on a randomized MAC where every message has two valid 1-bit
  tags `[false]` and `[true]`, signing `0^n` and verifying the flipped tag bit wins `sufCmaVqGame`
  with probability `1`, and `vqToSufForger` at `Q_v = 1` wins `sufCmaGame` with probability `1`
  without access to `sk`.
* **Malformed wrong-length queries:** wrong-length signing queries return `[]` without logging,
  wrong-length verification messages return `[false]` without winning even when raw `verify` returns
  `true`, and wrong-length tags on `prfMAC` / `vqMacToPrfDistinguisher` are rejected locally with
  `0` PRF queries.
* **PRF MAC instantiation:** `PseudorandomFunction.sufCmaVq_prfMAC`,
  `succProbability_sufCmaVqGame_prfMAC_le`, and `MACScheme.sufCmaVq_iff_sufCma`.
-/

namespace CslibFrontierTests.Crypto.MACVerificationQueries

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-- Always-accepting test MAC scheme (`verify _ _ _ = true`). -/
private noncomputable def alwaysAcceptMAC : MACScheme where
  keyGen _ := pure []
  sign _ msg := pure msg
  verify _ _ _ := true
  keyGen_ppt := by ppt
  sign_ppt := by ppt
  verify_polyTime := by polytime
  verify_sign := by
    intro _ _ _ _ _ _ _
    rfl

/-- Concrete `prfMAC` on the message-echo family `fun _ msg => msg`. -/
private noncomputable def echoMAC : MACScheme :=
  prfMAC (fun _ msg => msg) (ComputableInPolyTime.snd _ _)

/-- Randomized test MAC whose `sign` samples a uniform 1-bit tag and whose `verify` accepts every
1-bit tag. -/
private noncomputable def twoTagMAC : MACScheme where
  keyGen _ := pure []
  sign _ _ := BitString.sampleList 1
  verify _ _ tag := tag.length == 1
  keyGen_ppt := by ppt
  sign_ppt := by ppt
  verify_polyTime := by polytime
  verify_sign := by
    intro _ _ _ _ _ tag htag
    rw [BitString.eval_sampleList] at htag
    simp [BitString.length_of_mem_support_uniformList htag]

/-! ### Boundary 1: `Q_v = 0` gives winning probability `0` -/

/-- Finite adversary making one signing query and `0` verification queries. -/
private def finiteSignOnlyAdversary : Unit → ProbOracleComp (forgeVqSpec Bool Bool) Unit :=
  fun () => do
    let _ ← ProbOracleComp.query (spec := forgeVqSpec Bool Bool) (Sum.inl false)
    return ()

example :
    Experiment.succProbability
      (vqForgeExperiment (pure ((), ())) (Signer.ofSign fun () m => pure m)
        (fun () () _ _ => true) finiteSignOnlyAdversary) = 0 := by
  refine succProbability_vqForgeExperiment_zero _ _ _ fun () => ?_
  exact (IsVerificationQueryBounded.query_sign false).bind fun _ => .pure () 0

/-- Word-level `VqForger` that signs `0^n` and makes `0` verification queries. -/
private def wordSignOnlyForger : VqForger :=
  fun n _ => do
    let _ ← List.take n <$> ProbOracleComp.query (false, List.replicate n false)
    return ()

example (n : ℕ) :
    Game.succProbability
      (ProbComp.eval (alwaysAcceptMAC.sufCmaVqGame wordSignOnlyForger n)) = 0 := by
  refine alwaysAcceptMAC.succProbability_sufCmaVqGame_zero ?_
  exact ((OracleComp.isCostBounded_map_iff _ _ _).mpr
    (IsWordVerificationQueryBounded.query_sign (List.replicate n false))).bind
    fun _ => .pure () 0

/-! ### Boundary 2: Replaying `(m, t) ∈ log` replies `[true]` without winning -/

-- Direct state-step check on `vqOracle`: a logged pair answers `true` while keeping `won = false`.
example :
    vqOracle (Signer.ofSign fun () (m : Bool) => pure m) (fun () () m t => m == t) () ()
      (Sum.inr (true, true)) ⟨[(true, true)], false⟩ =
      pure (true, ⟨[(true, true)], false⟩) := by
  rfl

-- Direct state-step check on `sufCmaVqOracle`: a logged pair answers `[true]` while keeping
-- `won = false`.
example :
    echoMAC.sufCmaVqOracle 2 [true, false]
      (true, encPair encBits encBits ([false, true], [false, true]))
      ⟨[([false, true], [false, true])], false⟩ =
      pure ([true], ⟨[([false, true], [false, true])], false⟩) := by
  rfl

/-- Adversary against `alwaysAcceptMAC` that signs `0^n` to obtain `tag`, submits `(0^n, tag)` to
the verification oracle, and submits a fresh valid forgery `(0^n, [true])` ONLY if the replayed
verification query did not answer `[true]`. Evaluating to `PMF.pure false` simultaneously witnesses
that the replayed pair answered `[true]` and did not latch `won = true`. -/
private def replayBranchForger : VqForger :=
  fun n _ => do
    let msg := List.replicate n false
    let tag ← List.take n <$> ProbOracleComp.query (false, msg)
    let reply ← List.take 1 <$> ProbOracleComp.query (true, encPair encBits encBits (msg, tag))
    if reply == [true] then
      return ()
    else
      let _ ← List.take 1 <$> ProbOracleComp.query (true, encPair encBits encBits (msg, [true]))
      return ()

theorem eval_sufCmaVqGame_alwaysAcceptMAC_replayBranchForger (n : ℕ) :
    ProbComp.eval (alwaysAcceptMAC.sufCmaVqGame replayBranchForger n) = PMF.pure false := by
  simp only [MACScheme.sufCmaVqGame, alwaysAcceptMAC, replayBranchForger,
    OracleComp.interpret_bind, OracleComp.interpret_map,
    ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_map,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_map, PMF.pure_bind, PMF.bind_map,
    Function.comp_def]
  dsimp only [MACScheme.sufCmaVqOracle, StateT.run]
  simp [List.take_of_length_le, encPair_apply, encBits_apply]
  dsimp only [pure, StateT.pure]
  simp [ProbComp.eval_pure]

/-! ### Boundary 3: Randomized multi-tag MAC and Theorem 6.1 reduction -/

/-- `VqForger` that queries `0^n` on `twoTagMAC`, receives a 1-bit `tag`, and submits the opposite
1-bit tag `[!tag.headD false]` on `0^n` to the verification oracle. -/
private def flipSignedTagVqForger : VqForger :=
  fun n _ => do
    let msg := List.replicate n false
    let tag ← List.take 1 <$> ProbOracleComp.query (false, msg)
    let _ ← List.take 0 <$>
      ProbOracleComp.query (true, encPair encBits encBits (msg, [!tag.headD false]))
    return ()

theorem isOraclePPT_flipSignedTagVqForger :
    IsOraclePPT (encFinEnum Unit) flipSignedTagVqForger := by
  have hsign : IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun p : ℕ × List Bool =>
        List.take 1 <$> ProbOracleComp.query (false, List.replicate p.1 false)) :=
    IsOraclePPTOn.query_take false (by polytime) (by polytime)
  have hvq : IsOraclePPTOn (encPair (encPair encUnary encBits) encBits) (encFinEnum Unit)
      (fun pair : (ℕ × List Bool) × List Bool => do
        let _ ← List.take 0 <$> ProbOracleComp.query
          (true, encPair encBits encBits (List.replicate pair.1.1 false, [!pair.2.headD false]))
        pure ()) := by
    ppt
  unfold flipSignedTagVqForger
  exact (hsign.bind_with hvq).isOraclePPT

theorem eval_sufCmaVqGame_twoTagMAC_flipSignedTagVqForger (n : ℕ) :
    ProbComp.eval (twoTagMAC.sufCmaVqGame flipSignedTagVqForger n) = PMF.pure true := by
  simp only [MACScheme.sufCmaVqGame, twoTagMAC, flipSignedTagVqForger,
    OracleComp.interpret_bind, OracleComp.interpret_pure, OracleComp.interpret_map,
    ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_pure, StateT.run_map,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_map, PMF.pure_bind, PMF.bind_map,
    Function.comp_def]
  dsimp only [MACScheme.sufCmaVqOracle, StateT.run]
  simp only [List.length_replicate, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, encPair_apply,
    encBits_apply, unframe_frame_append, dropFrame_frame_append, Bool.false_or]
  have hcongr :
      PMF.bind (ProbComp.eval (BitString.sampleList 1))
        (fun tag : List Bool =>
          PMF.pure
            ((true && ([!(tag.take 1).headD false].length == 1)) &&
              !([(List.replicate n false, tag)].contains
                (List.replicate n false, [!(tag.take 1).headD false])))) =
      PMF.bind (ProbComp.eval (BitString.sampleList 1)) (fun _ => PMF.pure true) := by
    refine PMF.bind_congr_on_support _ _ _ fun tag htag => ?_
    rw [BitString.eval_sampleList] at htag
    obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp
      (BitString.length_of_mem_support_uniformList htag)
    cases b <;> simp
  rw [hcongr, PMF.bind_const]

theorem not_sufCmaVq_twoTagMAC : ¬ twoTagMAC.SUFCMAVq := by
  intro hsec
  have hneg := hsec.negligible flipSignedTagVqForger isOraclePPT_flipSignedTagVqForger
  simp only [eval_sufCmaVqGame_twoTagMAC_flipSignedTagVqForger, Game.succProbability,
    PMF.pure_apply, ite_true, ENNReal.toNNReal_one] at hneg
  exact not_negligible_const one_ne_zero hneg

private theorem isWordVerificationQueryBounded_flipSignedTagVqForger (n : ℕ) :
    IsWordVerificationQueryBounded (flipSignedTagVqForger n []) 1 := by
  unfold flipSignedTagVqForger
  refine (((OracleComp.isCostBounded_map_iff (List.take 1) _ _).mpr
      (IsWordVerificationQueryBounded.query_sign (List.replicate n false))).bind
    fun (tag : List Bool) =>
      (((OracleComp.isCostBounded_map_iff (List.take 0) _ _).mpr
        (IsWordVerificationQueryBounded.query_verify
          (encPair encBits encBits (List.replicate n false, [!tag.headD false])))).bind
        fun _ => .pure () 0)).mono (by omega)

-- At `Q_v = 1` (`width = 0`), `twoTagMAC.vqToSufForger` wins `sufCmaGame` with probability `1`
-- without ever accessing `sk`, matching `succProbability_sufCmaVqGame_le_mul`.
theorem succProbability_sufCmaGame_vqToSufForger_twoTagMAC (n : ℕ) :
    Game.succProbability
      (ProbComp.eval
        (twoTagMAC.sufCmaGame
          (twoTagMAC.vqToSufForger (fun _ => 1) (fun _ => 0) (fun _ => 1)
            flipSignedTagVqForger) n)) = 1 := by
  have hle := twoTagMAC.succProbability_sufCmaVqGame_le_mul (tagBound := fun _ => 1)
    (fun _ => 0) (fun _ => 1) (adversary := flipSignedTagVqForger) (n := n)
    (fun _ _ _ _ tag htag => by
      simp only [twoTagMAC, BitString.eval_sampleList] at htag
      exact (BitString.length_of_mem_support_uniformList htag).le)
    (Or.inr ⟨1, rfl⟩)
    (isWordVerificationQueryBounded_flipSignedTagVqForger n)
  rw [eval_sufCmaVqGame_twoTagMAC_flipSignedTagVqForger] at hle
  simp only [Game.succProbability, PMF.pure_apply, ite_true, ENNReal.toNNReal_one,
    Nat.cast_one, one_mul] at hle
  have hle_one :
      ((ProbComp.eval
        (twoTagMAC.sufCmaGame
          (twoTagMAC.vqToSufForger (fun _ => 1) (fun _ => 0) (fun _ => 1)
            flipSignedTagVqForger) n)) true).toNNReal ≤ 1 := by
    simpa using ENNReal.toNNReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ true)
  exact le_antisymm hle_one hle

/-! ### Boundary 4: Malformed wrong-length signing and verification queries -/

-- Wrong-length signing query returns `[]` and leaves `log` unchanged.
example :
    echoMAC.sufCmaVqOracle 2 [true, false] (false, [true]) ⟨[], false⟩ =
      pure ([], ⟨[], false⟩) := by
  rfl

-- Even against `alwaysAcceptMAC` (`verify _ _ _ = true`), a wrong-length verification message at
-- parameter `n + 1` returns `[false]` and leaves `won = false`.
private def wrongMsgLenVqForger : VqForger :=
  fun _ _ => do
    let _ ← List.take 1 <$> ProbOracleComp.query (true, encPair encBits encBits ([], []))
    return ()

example (n : ℕ) :
    ProbComp.eval (alwaysAcceptMAC.sufCmaVqGame wrongMsgLenVqForger (n + 1)) = PMF.pure false := by
  simp only [MACScheme.sufCmaVqGame, alwaysAcceptMAC, wrongMsgLenVqForger,
    OracleComp.interpret_bind, OracleComp.interpret_pure, OracleComp.interpret_map,
    ProbOracleComp.interpret_query, StateT.run_bind, StateT.run_pure, StateT.run_map,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_map, PMF.pure_bind, PMF.bind_map,
    Function.comp_def]
  dsimp only [MACScheme.sufCmaVqOracle, StateT.run]
  simp [encPair_apply, encBits_apply, show unframe [false] = [] from rfl]

-- Wrong-length tag (`tag.length ≠ n`) on `vqMacToPrfDistinguisher` is rejected locally with `0`
-- external PRF queries.
private def wrongTagLenVqForger : VqForger :=
  fun _ _ => do
    let _ ← List.take 1 <$>
      ProbOracleComp.query (true, encPair encBits encBits ([false, true], [false]))
    return ()

example : (vqMacToPrfDistinguisher wrongTagLenVqForger 2 []).IsQueryBounded 0 := by
  refine isQueryBounded_vqMacToPrfDistinguisher_of_wellFormed ?_
  unfold wrongTagLenVqForger
  exact (((OracleComp.isCostBounded_map_iff (List.take 1) _ _).mpr
    (ProbOracleComp.isCostBounded_query _
      (true, encPair encBits encBits ([false, true], [false])))).bind
    fun _ => .pure () 0).mono (by decide)

/-! ### Asymptotic client instantiations -/

example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    (prfMAC family hprf.polyTime).SUFCMAVq :=
  hprf.sufCmaVq_prfMAC

example {M : MACScheme} : M.SUFCMAVq ↔ M.SUFCMA :=
  M.sufCmaVq_iff_sufCma

end CslibFrontierTests.Crypto.MACVerificationQueries
