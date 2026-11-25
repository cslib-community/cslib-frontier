/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module

import CslibFrontier.Crypto.Protocols.AnonymousToken.CRTHazard
import CslibFrontier.Crypto.Protocols.AnonymousToken.Unlinkability

/-!
# Regressions and instantiations for VOLE-ACT unlinkability and CRT witness-reuse hazard

Exercises `Cslib.Crypto.AnonymousToken.Unlinkability` and
`Cslib.Crypto.AnonymousToken.CRTHazard` through ordinary module imports:
* an honest-traffic positive execution witness showing `unlinkabilityExperiment` accepts honest
  issuance, pre-challenge spend, and challenge spend executions with probability `1`;
* concrete balance-partitioning attacks (`balancePartitionInitAdversary` with `T₀ ≠ T₁` and
  `balancePartitionRefundAdversary` with `T₀ = T₁` and `x'₀ ≠ x'₁`) proving `Game.advantage = 1`
  against `unguardedUnlinkabilityExperiment` and `Game.advantage = 0` under
  `unlinkabilityExperiment`, isolating the cross-branch non-abort guard;
* concrete `example`s instantiating `zkDistinguisher_isQueryBounded`,
  `unlinkabilityExperiment_advantage_le` (including the `preRounds = 0` specialization
  `2 * (2 + challengeSpends)`), `crtDecouple_identicalUntilBad`, `crtDecouple_advantage_le`
  (both type-level instantiation and a non-vacuous `advantage = 1 / 2` non-hiding separator),
  and `CommitMsg.bumpBal_ne`;
* concrete `5 × 3` and `6 × 4` `ZMod 2` parity-check matrix witnesses (`H * F = 0`, surjective
  `H.mulVecLin`), numeric instantiations of `sub_le_leftKernelDim` (`312 - 128 = 184`) and
  `multiMask_parityCheck_uniform_zero_prob` (`2⁻¹ ^ (12 * 14) = 2⁻¹ ^ 168`), strictly interior
  `(0, 1)` bounds for `crtIssueSpendAdversary` (`7 / 8`) and Spend `(t, r_lo)` prefix search
  (`1 / 2`), and the `r`-first witness-order repair (`advantage = 0` vs `15 / 16` witness-knowing
  break).
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.AnonymousTokenUnlinkability

open Cslib Cslib.Crypto Cslib.Crypto.AnonymousToken
open Cslib.Crypto.AnonymousToken.Unlinkability
open Cslib.Crypto.AnonymousToken.CRTHazard
open Probability
open Probability.PMF (uniformOfFintype)
open scoped Matrix ENNReal NNReal

/-- Deterministic commitment fixture packing `(nf, ctx, bal, r)` over `Fin 1 → ZMod 2`. -/
private noncomputable def testCom :
    OpeningCommitment Unit (CommitMsg ℕ ℕ) (CommitMsg ℕ ℕ × (Fin 1 → ZMod 2)) (Fin 1 → ZMod 2) where
  keyGen := pure ()
  openSample := ProbComp.uniform (Fin 1 → ZMod 2)
  eval _ m r := (m, r)

/-- Trivial deterministic tag combining commitment and refund integer. -/
private def testTag (c : CommitMsg ℕ ℕ × (Fin 1 → ZMod 2)) (x : ℕ) :
    (CommitMsg ℕ ℕ × (Fin 1 → ZMod 2)) × ℕ :=
  (c, x)

/-- Deterministic certifier accepting messages equal to signatures. -/
private def testSig :
    Signature.Scheme Unit Unit ((CommitMsg ℕ ℕ × (Fin 1 → ZMod 2)) × ℕ)
      ((CommitMsg ℕ ℕ × (Fin 1 → ZMod 2)) × ℕ) where
  keyGen := pure ((), ())
  sign _ m := pure m
  verify _ m s := decide (m = s)

/-- Trivial deterministic prover/simulator system emitting `()`. -/
private def testSys :
    ProverSystem Unit Unit (CommitMsg ℕ ℕ × (Fin 1 → ZMod 2)) ℕ ℕ (Fin 1 → ZMod 2)
      ((CommitMsg ℕ ℕ × (Fin 1 → ZMod 2)) × ℕ) Unit where
  prove _ _ _ := pure ()
  simulate _ _ := pure ()

/-- Honest issuance-and-spend client driver that always reports `true` after completing one
pre-challenge spend and one challenge spend within balance bounds. -/
private def honestUnlinkAdversary :
    UnlinkAdversary Unit Unit ℕ (CommitMsg ℕ ℕ × (Fin 1 → ZMod 2)) ℕ Unit
      ((CommitMsg ℕ ℕ × (Fin 1 → ZMod 2)) × ℕ) Unit 1 1 where
  init _ := pure ⟨(), 1, 3, 3, ()⟩
  issue _ c0 _ c1 _ := pure ⟨(c0, 0), (c1, 0), ()⟩
  choosePre _ _ := pure ⟨false, 1, ()⟩
  finalizePre _ _ _ _ cPrime _ := pure ⟨1, (cPrime, 1), ()⟩
  chooseChallenge _ _ := pure ⟨2, ()⟩
  finalizeChallenge _ _ _ _ cPrime _ := pure ⟨0, (cPrime, 0), ()⟩
  guess _ := pure true

/-- Positive execution witness: `unlinkabilityExperiment` accepts honest traffic with probability
`1` in both challenge-bit worlds (non-vacuity check). -/
example (b : Bool) :
    Game.succProbability
      (unlinkabilityExperiment testCom (pure 7) testTag testSig 10 testSys
        honestUnlinkAdversary b) = 1 := by
  have hrun :
      unlinkabilityExperiment testCom (pure 7) testTag testSig 10 testSys
        honestUnlinkAdversary b = PMF.pure true := by
    cases b <;>
      simp [unlinkabilityExperiment, unlinkOracleProgram, honestUnlinkAdversary, testCom,
        testTag, testSig, testSys, preLoopOracle, challengeLoopOracle, realProofOracle,
        validStatement, spendAdmissible, ProbOracleComp.run_bind, ProbOracleComp.run_sample,
        ProbOracleComp.run_query, ProbOracleComp.run_pure, ProbComp.eval_bind,
        ProbComp.eval_uniform, PMF.map, Function.comp_def, PMF.bind_const]
  rw [hrun]
  simp [Game.succProbability]

/-- `balancePartitionInitAdversary` breaks `unguardedUnlinkabilityExperiment` with advantage `1`
for `bound = 5`, while `unlinkabilityExperiment` neutralizes it to advantage `0`. -/
example :
    Game.advantage
      (unguardedUnlinkabilityExperiment testCom (pure 1) testTag testSig 5 testSys
        (balancePartitionInitAdversary testTag () 1 id) false)
      (unguardedUnlinkabilityExperiment testCom (pure 1) testTag testSig 5 testSys
        (balancePartitionInitAdversary testTag () 1 id) true) = 1 ∧
    Game.advantage
      (unlinkabilityExperiment testCom (pure 1) testTag testSig 5 testSys
        (balancePartitionInitAdversary testTag () 1 id) false)
      (unlinkabilityExperiment testCom (pure 1) testTag testSig 5 testSys
        (balancePartitionInitAdversary testTag () 1 id) true) = 0 := by
  refine ⟨?_, ?_⟩
  · exact balancePartitionInit_unguarded_advantage_eq_one testCom (pure 1) testTag testSig 5 testSys
      (by omega) () 1 id (fun m => by simp [testSig])
  · exact balancePartitionInit_guarded_advantage_eq_zero testCom (pure 1) testTag testSig 5 testSys
      (by omega) () 1 id (fun m => by simp [testSig])

/-- `balancePartitionRefundAdversary` (`T₀ = T₁ = 2`, unequal pre-challenge refunds) breaks
`unguardedUnlinkabilityExperiment` with advantage `1` for `bound = 5`, while
`unlinkabilityExperiment` collapses its advantage to `0`. -/
example :
    Game.advantage
      (unguardedUnlinkabilityExperiment testCom (pure 1) testTag testSig 5 testSys
        (balancePartitionRefundAdversary testTag () 1 id) false)
      (unguardedUnlinkabilityExperiment testCom (pure 1) testTag testSig 5 testSys
        (balancePartitionRefundAdversary testTag () 1 id) true) = 1 ∧
    Game.advantage
      (unlinkabilityExperiment testCom (pure 1) testTag testSig 5 testSys
        (balancePartitionRefundAdversary testTag () 1 id) false)
      (unlinkabilityExperiment testCom (pure 1) testTag testSig 5 testSys
        (balancePartitionRefundAdversary testTag () 1 id) true) = 0 := by
  refine ⟨?_, ?_⟩
  · exact balancePartitionRefund_unguarded_advantage_eq_one testCom (pure 1) testTag testSig 5
      testSys (by omega) () 1 id (fun m => by simp [testSig])
  · exact balancePartitionRefund_guarded_advantage_eq_zero testCom (pure 1) testTag testSig 5
      testSys (by omega) () 1 id (fun m => by simp [testSig])

/-- Instantiation of `unlinkabilityExperiment_advantage_le` and query bound
`zkDistinguisher_isQueryBounded` with `preRounds = 0` (`2 + 0 + 3 = 2 + 3`). -/
example
    (adv : UnlinkAdversary Unit Unit ℕ (CommitMsg ℕ ℕ × (Fin 1 → ZMod 2)) ℕ Unit
      ((CommitMsg ℕ ℕ × (Fin 1 → ZMod 2)) × ℕ) Unit 0 3) :
    ProbOracleComp.IsQueryBounded (zkDistinguisher testCom (pure 1) testTag testSig 10 adv ())
        (2 + 3) ∧
      (Game.advantage
        (unlinkabilityExperiment testCom (pure 1) testTag testSig 10 testSys adv false)
        (unlinkabilityExperiment testCom (pure 1) testTag testSig 10 testSys adv true) : ℝ) ≤
        2 * (Game.advantage
          (multiProofZKRealGame testCom testTag testSig 10 testSys
            (zkDistinguisher testCom (pure 1) testTag testSig 10 adv))
          (multiProofZKSimGame testCom testTag testSig 10 testSys
            (zkDistinguisher testCom (pure 1) testTag testSig 10 adv)) : ℝ) +
          2 * ((2 + 3 : ℕ) : ℝ) *
            (Experiment.advantage
              (testCom.toScheme.hidingExperiment
                (unlinkHidingReduction testCom (pure 1) testTag testSig 10 testSys adv) false)
              (testCom.toScheme.hidingExperiment
                (unlinkHidingReduction testCom (pure 1) testTag testSig 10 testSys adv) true) :
                  ℝ) := by
  refine ⟨?_, ?_⟩
  · simpa using zkDistinguisher_isQueryBounded testCom (pure 1) testTag testSig 10 adv ()
  · simpa using unlinkabilityExperiment_advantage_le testCom (pure 1) testTag testSig 10 testSys adv

/-- Concrete `G8 → G8.5` setup over `qTok = 2` tokens and `IV = Fin 4`, instantiating
`crtDecouple_identicalUntilBad`, `crtDecouple_advantage_le`, and `toScheme_correct`. -/
private noncomputable def testG85Setup :
    G85Setup Unit (CommitMsg ℕ ℕ × (Fin 1 → ZMod 2)) ℕ ℕ (Fin 4) 2 1 1 2 where
  Com := testCom
  msgs _ j := ⟨j.val, 1, 10⟩
  ivGen _ j := pure ⟨j.val, by omega⟩
  baseLabel _ _ _ _ := 0
  adv _ _ := pure true

example (iv : Fin 2 → Fin 4) (d r : Fin 2 → Fin 1 → ZMod 2)
    (cmult : Fin 2 → Fin 2 → Fin 1 → ZMod 2)
    (h5 : H5Query (Fin 4) 2 1 → Fin 1 → ZMod 2) :
    OracleComp.IdenticalUntilBad
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
        (g8Handler testG85Setup () iv d r cmult h5))
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n))
        (g85Handler testG85Setup () iv d r h5))
      (fun bad : Bool => bad = true) :=
  crtDecouple_identicalUntilBad testG85Setup () iv d r cmult h5

example :
    testCom.toScheme.Correct ∧
      (⟨1, 1, 10⟩ : CommitMsg ℕ ℕ).bumpBal ≠ ⟨1, 1, 10⟩ ∧
      (Game.advantage (g8Game testG85Setup) (g85Game testG85Setup) : ℝ) ≤
        (2 : ℝ) *
          ((Experiment.advantage
            (testCom.toScheme.hidingExperiment (badH5HidingReduction testG85Setup) false)
            (testCom.toScheme.hidingExperiment (badH5HidingReduction testG85Setup) true) : ℝ) +
            (Experiment.succProbability
              (testCom.toScheme.bindingExperiment (badH5BindingReduction testG85Setup)) : ℝ)) +
          g85IvCollisionProb testG85Setup :=
  ⟨testCom.toScheme_correct, CommitMsg.bumpBal_ne _, crtDecouple_advantage_le testG85Setup⟩

/-- Non-hiding `G8 → G8.5` distinguisher reading `r 0 = (tok 0).com.2`, querying `H5` at
`badH5Key`, and comparing the reply against `(tok 0).cmult 0`. -/
private noncomputable def testG85Distinguisher :
    Unit → (Fin 1 → CRTProofToken (CommitMsg ℕ ℕ × (Fin 1 → ZMod 2)) (Fin 1) 1 1 1) →
      ProbOracleComp (H5Spec (Fin 1) 1 1 1) Bool := fun _ tok => do
  let h ← ProbOracleComp.query ⟨(tok 0).iv, 0, (tok 0).d + (tok 0).com.2⟩
  return decide ((tok 0).cmult 0 = h)

/-- Concrete `qTok = 1`, `nMult = 1`, `lam = 1`, `nMask = 1` setup pairing non-hiding `testCom`
with `testG85Distinguisher`. -/
private noncomputable def testG85AttackSetup :
    G85Setup Unit (CommitMsg ℕ ℕ × (Fin 1 → ZMod 2)) ℕ ℕ (Fin 1) 1 1 1 1 where
  Com := testCom
  msgs _ _ := ⟨0, 1, 10⟩
  ivGen _ _ := pure 0
  baseLabel _ _ _ _ := 0
  adv := testG85Distinguisher

/-- Non-vacuity check for `G8 → G8.5`: with non-hiding `testCom`, `testG85Distinguisher` separates
`g8Game testG85AttackSetup` (`1`) from `g85Game testG85AttackSetup` (`1 / 2`) with
`Game.advantage = 1 / 2` (`0 < advantage`), bounded above by `crtDecouple_advantage_le`. -/
example :
    (0 : ℝ) < (Game.advantage (g8Game testG85AttackSetup) (g85Game testG85AttackSetup) : ℝ) ∧
      (Game.advantage (g8Game testG85AttackSetup) (g85Game testG85AttackSetup) : ℝ) = 1 / 2 ∧
      (Game.advantage (g8Game testG85AttackSetup) (g85Game testG85AttackSetup) : ℝ) ≤
        (1 : ℝ) *
          ((Experiment.advantage
            (testCom.toScheme.hidingExperiment
              (badH5HidingReduction testG85AttackSetup) false)
            (testCom.toScheme.hidingExperiment
              (badH5HidingReduction testG85AttackSetup) true) : ℝ) +
            (Experiment.succProbability
              (testCom.toScheme.bindingExperiment
                (badH5BindingReduction testG85AttackSetup)) : ℝ)) +
          g85IvCollisionProb testG85AttackSetup := by
  have hx : ∀ r u : Fin 1 → ZMod 2, (r + u) + r = u := by
    intro r u
    ext i
    exact (by decide : ∀ a b : ZMod 2, a + b + a = b) (r i) (u i)
  have hzl : ∀ u : Fin 1 → ZMod 2, (fun _ : Fin 1 => (0 : ZMod 2)) + u = u := fun u =>
    zero_add u
  have hg8 : g8Game testG85AttackSetup = PMF.pure true := by
    simp only [g8Game, testG85AttackSetup, testG85Distinguisher, testCom, samplePi,
      ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure, ProbOracleComp.run_bind,
      ProbOracleComp.run_query, ProbOracleComp.run_pure, PMF.pure_bind, Fin.isValue]
    simp only [hzl, hx, decide_true, PMF.bind_const]
  have hconst : ∀ {α : Type} (p : PMF α) (f : α → PMF Bool) (c : ℝ≥0∞),
      (∀ x, f x true = c) → (p.bind f) true = c := by
    intro α p f c hf
    simp [PMF.bind_apply, hf, ENNReal.tsum_mul_right, p.tsum_coe]
  have hcmult : ∀ a : Fin 1 → ZMod 2,
      ((uniformOfFintype (Fin 1 → Fin 1 → Fin 1 → ZMod 2)).map
        fun cm => decide (cm 0 0 = a)) true = (2 : ℝ≥0∞)⁻¹ := by
    intro a
    let e : (Fin 1 → Fin 1 → Fin 1 → ZMod 2) ≃ (Fin 1 → ZMod 2) :=
      { toFun := fun cm => cm 0 0
        invFun := fun v _ _ => v
        left_inv := fun cm => by
          ext i j k
          fin_cases i
          fin_cases j
          fin_cases k
          rfl
        right_inv := fun _ => rfl }
    have hmap := Probability.PMF.uniformOfFintype_map_equiv e
    change ((uniformOfFintype (Fin 1 → Fin 1 → Fin 1 → ZMod 2)).map
      fun cm => decide (e cm = a)) true = (2 : ℝ≥0∞)⁻¹
    rw [show (fun cm : Fin 1 → Fin 1 → Fin 1 → ZMod 2 => decide (e cm = a)) =
      (fun v => decide (v = a)) ∘ e from rfl, ← PMF.map_comp, hmap]
    simp only [PMF.map_apply, tsum_fintype]
    rw [Finset.sum_eq_single a]
    · simp [Probability.PMF.uniformOfFintype_apply, ZMod.card]
    · intro v _ hv; simp [hv]
    · intro ha; exact (ha (Finset.mem_univ a)).elim
  have hg85 : g85Game testG85AttackSetup true = (2 : ℝ≥0∞)⁻¹ := by
    simp only [g85Game, g85FullRun, testG85AttackSetup, testG85Distinguisher,
      ProbOracleComp.runState_bind, ProbOracleComp.runState_query, ProbOracleComp.runState_pure,
      StateT.run_bind, StateT.run_pure]
    simp only [testCom, samplePi, StateT.run, g85HandlerP, ProbComp.eval_bind,
      ProbComp.eval_uniform, ProbComp.eval_pure, PMF.map, Function.comp_def, PMF.bind_bind,
      PMF.pure_bind, Fin.isValue]
    refine hconst _ _ _ fun _ => hconst _ _ _ fun _ => hconst _ _ _ fun _ => ?_
    simpa only [PMF.map, Function.comp_def] using hcmult _
  have hadv : (Game.advantage (g8Game testG85AttackSetup) (g85Game testG85AttackSetup) : ℝ) =
      1 / 2 := by
    rw [Game.coe_advantage, hg8]
    simp [Game.succProbability, hg85, ENNReal.toNNReal_ofNat]
    norm_num
  refine ⟨by rw [hadv]; norm_num, hadv, ?_⟩
  rw [← Nat.cast_one (R := ℝ)]
  exact crtDecouple_advantage_le testG85AttackSetup

/-- Explicit `5 × 3` matrix over `ZMod 2` whose last two rows are `row0 + row1` and
`row1 + row2`, together with its `2 × 5` surjective parity-check matrix `testH`. -/
private def testF : Matrix (Fin 5) (Fin 3) (ZMod 2) :=
  !![1, 0, 0;
     0, 1, 0;
     0, 0, 1;
     1, 1, 0;
     0, 1, 1]

/-- Surjective `2 × 5` parity-check matrix witnessing `testH * testF = 0`. -/
private def testH : Matrix (Fin 2) (Fin 5) (ZMod 2) :=
  !![1, 1, 0, 1, 0;
     0, 1, 1, 0, 1]

private lemma testH_mul_testF : testH * testF = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private lemma testH_surjective : Function.Surjective testH.mulVecLin := by
  intro z
  refine ⟨![0, 0, 0, z 0, z 1], ?_⟩
  ext i
  fin_cases i <;> simp [testH, Matrix.mulVec, dotProduct, Fin.sum_univ_five]

/-- Concrete `5 × 3` left-kernel witness: `testH * testF = 0`, surjective `testH.mulVecLin`,
`leftKernelDim testF ≥ 2`, uniform single-mask rejection `(2⁻¹) ^ 2`, and `nMask = 2` rejection
`(2⁻¹) ^ 4`. -/
example (w : Fin 3 → ZMod 2) :
    2 ≤ leftKernelDim testF ∧
      testH *ᵥ (testF *ᵥ w) = 0 ∧
      ((uniformOfFintype (Fin 5 → ZMod 2)).map (fun y => decide (testH *ᵥ y = 0))) true =
        (2 : ℝ≥0∞)⁻¹ ^ 2 ∧
      ((uniformOfFintype (Fin 2 → Fin 5 → ZMod 2)).map
        (fun ys => decide (∀ mask, testH *ᵥ ys mask = 0))) true = (2 : ℝ≥0∞)⁻¹ ^ 4 := by
  refine ⟨?_, parityCheck_mulVec_of_eq_zero testH_mul_testF w, ?_, ?_⟩
  · simpa using sub_le_leftKernelDim testF
  · simpa [ZMod.card] using parityCheck_uniform_zero_prob testH_surjective
  · simpa using multiMask_parityCheck_uniform_zero_prob (nMask := 2) testH_surjective

/-- Concrete `testF` kernel dimension identity and parity-check matrix existence. -/
example :
    leftKernelDim testF + testF.rank = 5 ∧
      ∃ H : Matrix (Fin (leftKernelDim testF)) (Fin 5) (ZMod 2),
        H * testF = 0 ∧ Function.Surjective H.mulVecLin :=
  ⟨leftKernelDim_add_rank testF, exists_parityCheckMatrix testF⟩

/-- Illustrative CRT parameter check for `sub_le_leftKernelDim` (`m = 312`, `n = 128` implies
`dim(ker Fᵀ) ≥ 184`). -/
example (F : Matrix (Fin 312) (Fin 128) (ZMod 2)) : 184 ≤ leftKernelDim F := by
  simpa using sub_le_leftKernelDim F

/-- Illustrative CRT parity rejection probability (`kGates = 27`, `r = 14`, `nMask = 12` gives
`2⁻¹ ^ 168`). -/
example (H : Matrix (Fin 14) (Fin 27) (ZMod 2)) (hsurj : Function.Surjective H.mulVecLin) :
    ((uniformOfFintype (Fin 12 → Fin 27 → ZMod 2)).map
      (fun ys => decide (∀ mask, H *ᵥ ys mask = 0))) true = (2 : ℝ≥0∞)⁻¹ ^ 168 := by
  simpa using multiMask_parityCheck_uniform_zero_prob (nMask := 12) hsurj

/-- Explicit `6 × 4` gate matrix over `ZMod 2` (`4`-bit prefix, `rSub = 2` redundant rows) and its
surjective `2 × 6` parity-check matrix `testH6`. -/
private def testF6 : Matrix (Fin 6) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1;
     1, 1, 0, 0;
     0, 0, 1, 1]

/-- Surjective `2 × 6` parity-check matrix witnessing `testH6 * testF6 = 0`. -/
private def testH6 : Matrix (Fin 2) (Fin 6) (ZMod 2) :=
  !![1, 1, 0, 0, 1, 0;
     0, 0, 1, 1, 0, 1]

private lemma testH6_mul_testF6 : testH6 * testF6 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private lemma testH6_surjective : Function.Surjective testH6.mulVecLin := by
  intro z
  refine ⟨![0, 0, 0, 0, z 0, z 1], ?_⟩
  ext i
  fin_cases i <;> simp [testH6, Matrix.mulVec, dotProduct, Fin.sum_univ_six]

private lemma testH6_mul_sub_testF6 :
    testH6 * testF6.submatrix (Function.Embedding.refl (Fin 6)) id = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Concrete `H5` prefix distinguisher check (`crtPrefixTest_isQueryBounded`,
`crtPrefixTest_honest_true`, and `crtPrefixTest_wrong_guess_prob` at `lam = 4`, `nMask = 2`,
`rSub = 2`, `kGates = 6`). -/
example
    (L0 : Fin 6 → Fin 4 → ZMod 2) (active : Fin 6 → Bool) (maskInput : Fin 2 → Fin 4 → ZMod 2)
    (h5 : H5Query (Fin 2) 6 4 → Fin 2 → ZMod 2) :
    let sub := Function.Embedding.refl (Fin 6)
    let wP : Fin 4 → ZMod 2 := ![1, 0, 1, 0]
    let uP : Fin 4 → ZMod 2 := ![0, 1, 0, 1]
    let wBad : Fin 4 → ZMod 2 := ![0, 0, 0, 0]
    let tbl := honestCRTMaskTable (0 : Fin 2) L0 uP wP active testF6 maskInput h5
    let hAct : Fin 6 → Fin 2 → ZMod 2 := fun i => h5 ⟨0, sub i, tbl.activeLabel (sub i)⟩
    ProbOracleComp.IsQueryBounded (crtPrefixTest sub testH6 tbl hAct wBad) 6 ∧
      ProbComp.eval ((crtPrefixTest sub testH6 tbl hAct wP).run (fun q => pure (h5 q))) =
        PMF.pure true ∧
      ((uniformOfFintype (H5Query (Fin 2) 6 4 → Fin 2 → ZMod 2)).bind fun h =>
        let tbl' := honestCRTMaskTable (0 : Fin 2) L0 uP wP active testF6 maskInput h
        let hA' : Fin 6 → Fin 2 → ZMod 2 := fun i => h ⟨0, sub i, tbl'.activeLabel (sub i)⟩
        ProbComp.eval ((crtPrefixTest sub testH6 tbl' hA' wBad).run (fun q => pure (h q))))
          true = (2 : ℝ≥0∞)⁻¹ ^ 4 := by
  refine ⟨crtPrefixTest_isQueryBounded _ _ _ _ _, ?_, ?_⟩
  · exact crtPrefixTest_honest_true (Function.Embedding.refl (Fin 6)) testH6 testF6
      testH6_mul_sub_testF6 (0 : Fin 2) L0 ![0, 1, 0, 1] ![1, 0, 1, 0] active maskInput h5
  · refine crtPrefixTest_wrong_guess_prob (Function.Embedding.refl (Fin 6)) testH6 testH6_surjective
      (0 : Fin 2) L0 ![0, 1, 0, 1] ![1, 0, 1, 0] ![0, 0, 0, 0] active testF6 maskInput
      (by decide) (by decide)

/-- Strictly interior `(0, 1)` Issue-to-Spend CRT prefix break (`7 / 8 ≤ advantage`) and `6`-query
bound via `crtIssueSpendAdversary_isQueryBounded` and `crtIssueSpendAdversary_advantage_ge`. -/
example
    (L0₀ L0₁ : Fin 6 → Fin 4 → ZMod 2) (active₀ active₁ : Fin 6 → Bool)
    (maskInput₀ maskInput₁ : Fin 2 → Fin 4 → ZMod 2)
    (tbl₀ tbl₁ : CRTMaskTable (Fin 2) 6 4 2) (hAct₀ hAct₁ : Fin 6 → Fin 2 → ZMod 2) :
    let nf₀ : Fin 4 → ZMod 2 := ![0, 0, 0, 0]
    let nf₁ : Fin 4 → ZMod 2 := ![1, 0, 0, 0]
    let sub := Function.Embedding.refl (Fin 6)
    let g := crtIssueSpendGame sub (0 : Fin 2) 1 L0₀ L0₁ active₀ active₁ testF6
      maskInput₀ maskInput₁ nf₀ nf₁ (crtIssueSpendAdversary sub testH6)
    ProbOracleComp.IsQueryBounded (crtIssueSpendAdversary sub testH6 tbl₀ hAct₀ tbl₁ hAct₁ nf₁) 6 ∧
      (7 / 8 : ℝ) ≤ (Game.advantage (g false) (g true) : ℝ) := by
  refine ⟨crtIssueSpendAdversary_isQueryBounded _ _ _ _ _ _ _, ?_⟩
  have hge := crtIssueSpendAdversary_advantage_ge (Function.Embedding.refl (Fin 6)) testH6 testF6
    testH6_mul_sub_testF6 testH6_surjective
    (0 : Fin 2) 1 L0₀ L0₁ active₀ active₁ maskInput₀ maskInput₁
    (nf₀ := ![0, 0, 0, 0]) (nf₁ := ![1, 0, 0, 0]) (by decide)
  norm_num at hge
  exact hge

/-- Re-typed `6 × (2 + 2)` view of `testF6` for the Spend balance-prefix regression. -/
private def testF6_22 : Matrix (Fin 6) (Fin (2 + 2)) (ZMod 2) := testF6

private lemma testH6_mul_sub_testF6_22 :
    testH6 * testF6_22.submatrix (Function.Embedding.refl (Fin 6)) id = 0 :=
  testH6_mul_sub_testF6

/-- Strictly interior `(0, 1)` Spend-time `(t, r_lo)` prefix brute-force break (`1 / 2 ≤ advantage`)
and `2 ^ 2 * 6 = 24`-query bound via `crtSpendPrefixTest_isQueryBounded`,
`crtSpendPrefixTest_correct`, `crtSpendPrefixTest_wrong_t_le`, and
`crtSpendBalancePrefix_advantage_ge`. -/
example
    (L0 : Fin 6 → Fin (2 + 2) → ZMod 2) (active : Fin 6 → Bool)
    (maskInput : Fin 2 → Fin (2 + 2) → ZMod 2)
    (h5 : H5Query (Fin 2) 6 (2 + 2) → Fin 2 → ZMod 2) :
    let sub := Function.Embedding.refl (Fin 6)
    let t₀ : Fin 2 → ZMod 2 := ![0, 0]
    let t₁ : Fin 2 → ZMod 2 := ![1, 0]
    let rReal : Fin 2 → ZMod 2 := ![0, 1]
    let uP : Fin (2 + 2) → ZMod 2 := ![1, 1, 0, 0]
    let guesses := balancePrefixGuesses 2 2 t₀
    let tbl := honestCRTMaskTable (0 : Fin 2) L0 uP (packBalancePrefix t₀ rReal) active testF6_22
      maskInput h5
    let hAct : Fin 6 → Fin 2 → ZMod 2 := fun i => h5 ⟨0, sub i, tbl.activeLabel (sub i)⟩
    let g := crtSpendBalancePrefixGame sub testH6 (0 : Fin 2) L0 active testF6_22 maskInput t₀ t₁
      rReal
    ProbOracleComp.IsQueryBounded (crtSpendPrefixTest sub testH6 tbl hAct guesses) (4 * 6) ∧
      ProbComp.eval ((crtSpendPrefixTest sub testH6 tbl hAct guesses).run (fun q => pure (h5 q))) =
        PMF.pure true ∧
      ((uniformOfFintype (H5Query (Fin 2) 6 (2 + 2) → Fin 2 → ZMod 2)).bind fun h =>
        (uniformOfFintype (Fin (2 + 2) → ZMod 2)).bind fun u =>
          let wP := packBalancePrefix t₁ rReal
          let tbl' := honestCRTMaskTable (0 : Fin 2) L0 u wP active testF6_22 maskInput h
          let hA' : Fin 6 → Fin 2 → ZMod 2 := fun i => h ⟨0, sub i, tbl'.activeLabel (sub i)⟩
          ProbComp.eval ((crtSpendPrefixTest sub testH6 tbl' hA' guesses).run
            (fun q => pure (h q)))) true ≤ (1 / 2 : ℝ≥0∞) ∧
      (1 / 2 : ℝ) ≤ (Game.advantage (g false) (g true) : ℝ) := by
  intro sub t₀ t₁ rReal uP guesses tbl hAct g
  have hne : t₀ ≠ t₁ := by
    dsimp [t₀, t₁]
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hq := crtSpendPrefixTest_isQueryBounded sub testH6 tbl hAct guesses
    rw [length_balancePrefixGuesses] at hq
    norm_num at hq
    exact hq
  · exact crtSpendPrefixTest_correct sub testH6 testF6_22 testH6_mul_sub_testF6_22
      (0 : Fin 2) L0 uP t₀ rReal active maskInput h5
  · have hle := crtSpendPrefixTest_wrong_t_le sub testH6 testH6_surjective
      (0 : Fin 2) L0 t₁ rReal active testF6_22 maskInput guesses
      (mem_balancePrefixGuesses_ne hne rReal)
    rw [length_balancePrefixGuesses] at hle
    refine hle.trans ?_
    norm_num
    rw [show (4 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 4 + (2 : ℝ≥0∞)⁻¹ ^ 4) * 2 =
        (2 : ℝ≥0∞) ^ 4 * (2 : ℝ≥0∞)⁻¹ ^ 4 by ring,
      ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  · have hge := crtSpendBalancePrefix_advantage_ge sub testH6 testF6_22 testH6_mul_sub_testF6_22
      testH6_surjective (0 : Fin 2) L0 active maskInput (t₀ := t₀) (t₁ := t₁) hne rReal
    norm_num at hge
    exact hge

/-- Witness-order repair (`r`-first): unqueried CRT mask views are identical across distinct
metadata (`rFirstCRTMaskView_eq`), while a witness-knowing distinguisher given `r` still achieves
advantage `≥ 15 / 16` (`rFirst_breaks_witnessKnowingZK`). -/
example
    (L0 : Fin 6 → Fin 4 → ZMod 2) (active : Fin 6 → Bool)
    (maskInputMeta : Bool → Fin 2 → Fin 4 → ZMod 2)
    (uPrefix r : Fin 4 → ZMod 2) :
    let sub := Function.Embedding.refl (Fin 6)
    let gReal : Game :=
      (uniformOfFintype (H5Query (Fin 2) 6 4 → Fin 2 → ZMod 2)).bind fun h5 =>
        let tbl := honestCRTMaskTable (0 : Fin 2) L0 uPrefix r active testF6 (maskInputMeta false)
          h5
        let hActive : Fin 6 → Fin 2 → ZMod 2 :=
          fun i => h5 ⟨0, sub i, tbl.activeLabel (sub i)⟩
        ProbComp.eval ((crtPrefixTest sub testH6 tbl hActive r).run (fun q => pure (h5 q)))
    let gSim : Game :=
      (uniformOfFintype (Fin 2 → Fin 6 → ZMod 2)).bind fun cmultSim =>
        (uniformOfFintype (Fin 4 → ZMod 2)).bind fun dSim =>
          (uniformOfFintype (H5Query (Fin 2) 6 4 → Fin 2 → ZMod 2)).bind fun h5 =>
            let actL : Fin 6 → Fin 4 → ZMod 2 :=
              fun e => if active e then L0 e + uPrefix else L0 e
            let tbl : CRTMaskTable (Fin 2) 6 4 2 := ⟨0, actL, dSim, cmultSim⟩
            let hActive : Fin 6 → Fin 2 → ZMod 2 := fun i => h5 ⟨0, sub i, actL (sub i)⟩
            ProbComp.eval ((crtPrefixTest sub testH6 tbl hActive r).run (fun q => pure (h5 q)))
    rFirstCRTMaskView (0 : Fin 2) L0 active testF6 maskInputMeta false =
        (uniformOfFintype (Fin 4 → ZMod 2)).bind (fun u =>
          rFirstDecoupledView (0 : Fin 2) (fun e => if active e then L0 e + u else L0 e)) ∧
      rFirstCRTMaskView (0 : Fin 2) L0 active testF6 maskInputMeta false =
        rFirstCRTMaskView (0 : Fin 2) L0 active testF6 maskInputMeta true ∧
      (15 / 16 : ℝ) ≤ (Game.advantage gReal gSim : ℝ) := by
  refine ⟨rFirstCRTMaskView_eq_decoupled (0 : Fin 2) L0 active testF6 maskInputMeta false,
    rFirstCRTMaskView_eq (0 : Fin 2) L0 active testF6 maskInputMeta false true, ?_⟩
  have hge := rFirst_breaks_witnessKnowingZK (Function.Embedding.refl (Fin 6)) testH6 testF6
    testH6_mul_sub_testF6 testH6_surjective (0 : Fin 2) L0 uPrefix r active (maskInputMeta false)
  norm_num at hge
  exact hge

end CslibFrontierTests.Crypto.AnonymousTokenUnlinkability
