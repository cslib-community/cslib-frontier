/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module

import CslibFrontier.Crypto.Protocols.AnonymousToken.ACTMQ
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunLog
import Mathlib.Algebra.Field.ZMod

/-!
# Clients and boundary regressions for VOLE-ACT-MQ credit conservation

Exercises `Cslib.Crypto.AnonymousToken.ACTMQ` through ordinary module imports:
* disjoint-coordinate finite-field `Fin 4 → ZMod 257` instantiation `(nf, ctx, t, 0) + (0, 0, 0, x)`
  under `NoteInRange 256`: proves `Set.InjOn` via `actEmbed_injOn_of_disjoint`, demonstrates
  unbounded wraparound aliasing (`t = 0` vs `t = 257`), and instantiates
  `actMQConservation_succProbability_le` and `actMQClawReduction_queryBound`, alongside the
  unbounded `Fin 4 → ℤ` client (`actMQConservation_unbounded_succProbability_le`);
* concrete `actCom`/`actTag` credit-conservation witnesses (`= 0` honest, `= 1` forging, and `= 0`
  out-of-range `(V4)` spend rejection in `actMQConservationExperiment 5`);
* concrete `clawExperiment` budget and dedup-boundary witnesses: an honest `1`-query client
  (`= 0`), a `2`-query repeated-target adversary winning with `2` claims (confirming dedup budget
  cost `= 1`, `= 1`), and a `0`-query duplicate-target-claim adversary rejected by `Nodup` (`= 0`);
* concrete `G`-collision separation over `ZMod 5`: `gCollisionForger` wins `extractedExperiment`
  with probability `1` and triggers `gCollisionExperiment = 1` via `gCollisionReduction`, while
  `clawExperiment ... (clawReduction ... id (gCollisionForger ...)) = PMF.pure false`;
* concrete zero-opening scaling over `ZMod 5` (`scalars = [1, 2]`): wins `clawExperiment` with
  probability `1` when `G 0 = 0` via both `UOV.verify_scale_option_of_quadratic` (`leftSqMap`,
  `Option (ZMod 5)`) and the composed `Correct` quadratic fixture (`surjSqMap` /
  `clawExperiment_zeroOpeningClawAttack_option_eq_pure_true_of_quadratic`), and fails identically
  (`PMF.pure false`) for both optional and raw preimages when `G 0 = 1 ≠ 0`
  (`UOV.rescale_ne_zeroOpening_of_tail_ne_zero`).
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.AnonymousTokenACTMQ

open Cslib Cslib.Crypto Cslib.Crypto.AnonymousToken Cslib.Crypto.AnonymousToken.ACTMQ
open Probability
open scoped NNReal

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-! ### 1. Disjoint-slot finite-field `Fin 4 → ZMod 257` and infinite `Fin 4 → ℤ` clients -/

private def isRefundFin4 (i : Fin 4) : Bool := decide (i = 3)

/-- Finite-field state embedding `(nf, ctx, t) ↦ ![nf, ctx, ↑t, 0]` over `ZMod 257`. -/
private def encodeStateZMod (nf ctx : ZMod 257) (t : ℕ) : Fin 4 → ZMod 257 :=
  ![nf, ctx, (t : ZMod 257), 0]

/-- Finite-field refund embedding `x ↦ ![0, 0, 0, ↑x]` over `ZMod 257`. -/
private def refundEmbedZMod (x : ℕ) : Fin 4 → ZMod 257 :=
  ![0, 0, 0, (x : ZMod 257)]

private theorem zmod257_natCast_inj {a b : ℕ} (ha : a < 256) (hb : b < 256)
    (heq : (a : ZMod 257) = (b : ZMod 257)) : a = b := by
  have hval := congrArg ZMod.val heq
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at hval
  exact hval

private theorem actEmbed_fin4_zmod257_injOn :
    Set.InjOn (actEmbed encodeStateZMod refundEmbedZMod)
      {note : Credit.Note (ZMod 257) (ZMod 257) | NoteInRange 256 note} := by
  refine actEmbed_injOn_of_disjoint 256 isRefundFin4 encodeStateZMod refundEmbedZMod ?_ ?_ ?_ ?_
  · intro nf ctx t i hi
    simp only [isRefundFin4, decide_eq_true_eq] at hi
    subst hi
    rfl
  · intro x i hi
    simp only [isRefundFin4, decide_eq_false_iff_not] at hi
    rcases i with ⟨i, hi_lt⟩
    match i with
    | 0 | 1 | 2 => rfl
    | 3 => exact absurd rfl hi
  · intro nf₁ nf₂ ctx₁ ctx₂ t₁ t₂ ht₁ ht₂ h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp only [encodeStateZMod, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val] at h0 h1 h2
    exact ⟨h0, h1, zmod257_natCast_inj ht₁ ht₂ h2⟩
  · intro x₁ hx₁ x₂ hx₂ h
    have h3 := congrFun h 3
    simp only [refundEmbedZMod, Matrix.cons_val] at h3
    exact zmod257_natCast_inj hx₁ hx₂ h3

-- Without the range check, `ZMod 257` aliases `t = 0` and `t = 257`.
example :
    actEmbed encodeStateZMod refundEmbedZMod ⟨0, 0, 0, 0⟩ =
      actEmbed encodeStateZMod refundEmbedZMod ⟨0, 0, 257, 0⟩ := by
  decide

-- Finite-field `(V4)` range-bounded VOLE-ACT-MQ credit conservation over `Fin 4 → ZMod 257`.
example {R Tail PK SK Sig : Type}
    [DecidableEq Tail] [DecidableEq R] [Inhabited R] [Inhabited Sig]
    (F : R → Fin 4 → ZMod 257) (G : R → Tail)
    (S : Signature.Scheme PK SK ((Fin 4 → ZMod 257) × Tail) Sig)
    (A : Conservation.ExtractedAdversary (ZMod 257) (ZMod 257) R
      ((Fin 4 → ZMod 257) × Tail) PK Sig) :
    Experiment.succProbability
        (actMQConservationExperiment 256 (actCom F G encodeStateZMod)
          (actTag refundEmbedZMod) S A) ≤
      Experiment.succProbability
          (clawExperiment S (UOV.structuredTarget F G)
            (clawReduction S (UOV.structuredTarget F G) (actEmbed encodeStateZMod refundEmbedZMod)
              (Conservation.noteForger (actCom F G encodeStateZMod) (actTag refundEmbedZMod) S
                (rangeBoundedAdversary 256 A)))) +
        Experiment.succProbability
          (gCollisionExperiment G
            (gCollisionReduction S
              (Credit.target (actCom F G encodeStateZMod) (actTag refundEmbedZMod))
              (Conservation.noteForger (actCom F G encodeStateZMod) (actTag refundEmbedZMod) S
                (rangeBoundedAdversary 256 A)))) +
        Experiment.succProbability
          (invalidReplyExperiment S
            (Credit.target (actCom F G encodeStateZMod) (actTag refundEmbedZMod))
            (Conservation.noteForger (actCom F G encodeStateZMod) (actTag refundEmbedZMod) S
              (rangeBoundedAdversary 256 A))) :=
  actMQConservation_succProbability_le 256 F G encodeStateZMod refundEmbedZMod
    actEmbed_fin4_zmod257_injOn S A

example {R Tail PK SK Sig : Type}
    [DecidableEq Tail] [Inhabited R] [Inhabited Sig]
    (F : R → Fin 4 → ZMod 257) (G : R → Tail)
    (S : Signature.Scheme PK SK ((Fin 4 → ZMod 257) × Tail) Sig)
    (A : Conservation.ExtractedAdversary (ZMod 257) (ZMod 257) R
      ((Fin 4 → ZMod 257) × Tail) PK Sig)
    (pk : PK) {q : ℕ} (hA : (A pk).IsQueryBounded q) :
    (clawReduction S (UOV.structuredTarget F G) (actEmbed encodeStateZMod refundEmbedZMod)
      (Conservation.noteForger (actCom F G encodeStateZMod) (actTag refundEmbedZMod) S
        (rangeBoundedAdversary 256 A)) pk).IsQueryBounded q :=
  actMQClawReduction_queryBound 256 F G encodeStateZMod refundEmbedZMod S A pk hA

/-- State embedding `(nf, ctx, t) ↦ ![↑nf, ↑ctx, ↑t, 0]`, vanishing on the refund slot `3`. -/
private def encodeStateFin4 (nf ctx t : ℕ) : Fin 4 → ℤ :=
  ![(nf : ℤ), (ctx : ℤ), (t : ℤ), 0]

/-- Refund embedding `x ↦ ![0, 0, 0, ↑x]`, vanishing off slot `3`. -/
private def refundEmbedFin4 (x : ℕ) : Fin 4 → ℤ :=
  ![0, 0, 0, (x : ℤ)]

private theorem actEmbed_fin4_injective :
    Function.Injective (actEmbed encodeStateFin4 refundEmbedFin4) := by
  refine actEmbed_injective_of_disjoint isRefundFin4 encodeStateFin4 refundEmbedFin4 ?_ ?_ ?_ ?_
  · intro nf ctx t i hi
    simp only [isRefundFin4, decide_eq_true_eq] at hi
    subst hi
    rfl
  · intro x i hi
    simp only [isRefundFin4, decide_eq_false_iff_not] at hi
    rcases i with ⟨i, hi_lt⟩
    match i with
    | 0 | 1 | 2 => rfl
    | 3 => exact absurd rfl hi
  · intro nf₁ nf₂ ctx₁ ctx₂ t₁ t₂ h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp only [encodeStateFin4, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val] at h0 h1 h2
    exact ⟨Int.ofNat.inj h0, Int.ofNat.inj h1, Int.ofNat.inj h2⟩
  · intro x₁ x₂ h
    have h3 := congrFun h 3
    simp only [refundEmbedFin4, Matrix.cons_val] at h3
    exact Int.ofNat.inj h3

-- Disjoint-slot `actEmbed` preserves refund differences (nonzero refund cannot mimic zero refund).
example :
    actEmbed encodeStateFin4 refundEmbedFin4 ⟨1, 2, 3, 4⟩ ≠
      actEmbed encodeStateFin4 refundEmbedFin4 ⟨1, 2, 3, 5⟩ := by
  intro h
  have := actEmbed_fin4_injective h
  contradiction

example {R Tail : Type} (F : R → Fin 4 → ℤ) (G : R → Tail)
    (note : Credit.Note ℕ ℕ) (r : R) :
    Credit.target (actCom F G encodeStateFin4) (actTag refundEmbedFin4) note r =
      UOV.structuredTarget F G (actEmbed encodeStateFin4 refundEmbedFin4 note) r :=
  credit_target_actCom_actTag F G encodeStateFin4 refundEmbedFin4 note r

-- Unbounded extracted-conservation client on the infinite `Fin 4 → ℤ` block split.
example {R Tail PK SK Sig : Type}
    [DecidableEq Tail] [DecidableEq R] [Inhabited R] [Inhabited Sig]
    (F : R → Fin 4 → ℤ) (G : R → Tail)
    (S : Signature.Scheme PK SK ((Fin 4 → ℤ) × Tail) Sig)
    (A : Conservation.ExtractedAdversary ℕ ℕ R ((Fin 4 → ℤ) × Tail) PK Sig) :
    Experiment.succProbability
        (Conservation.extractedConservationExperiment
          (actCom F G encodeStateFin4) (actTag refundEmbedFin4) S A) ≤
      Experiment.succProbability
          (clawExperiment S (UOV.structuredTarget F G)
            (clawReduction S (UOV.structuredTarget F G) (actEmbed encodeStateFin4 refundEmbedFin4)
              (Conservation.noteForger (actCom F G encodeStateFin4) (actTag refundEmbedFin4)
                S A))) +
        Experiment.succProbability
          (gCollisionExperiment G
            (gCollisionReduction S
              (Credit.target (actCom F G encodeStateFin4) (actTag refundEmbedFin4))
              (Conservation.noteForger (actCom F G encodeStateFin4) (actTag refundEmbedFin4)
                S A))) +
        Experiment.succProbability
          (invalidReplyExperiment S
            (Credit.target (actCom F G encodeStateFin4) (actTag refundEmbedFin4))
            (Conservation.noteForger
              (actCom F G encodeStateFin4) (actTag refundEmbedFin4) S A)) :=
  actMQConservation_unbounded_succProbability_le F G encodeStateFin4 refundEmbedFin4
    actEmbed_fin4_injective S A

/-! ### 2. Concrete `actCom`/`actTag` conservation and `clawExperiment` non-vacuity witnesses -/

private def zeroF : ℕ → Fin 4 → ℤ := fun _ => 0

private def zeroG : ℕ → ZMod 5 := fun _ => 0

private def vecSig :
    Signature.Scheme Unit Unit ((Fin 4 → ℤ) × ZMod 5) ((Fin 4 → ℤ) × ZMod 5) where
  keyGen := pure ((), ())
  sign _ target := pure target
  verify _ target σ := decide (target = σ)

private def actHonestIssue : Conservation.IssueRequest ℕ ℕ ℕ ((Fin 4 → ℤ) × ZMod 5) where
  ctx := 1
  amount := 10
  commitment := actCom zeroF zeroG encodeStateFin4 1 1 10 0
  nullifier := 1
  opening := 0

private def honestActAdversary :
    Conservation.ExtractedAdversary ℕ ℕ ℕ ((Fin 4 → ℤ) × ZMod 5) Unit ((Fin 4 → ℤ) × ZMod 5) :=
  fun _ => do
    let _ ← ProbOracleComp.query (.issue actHonestIssue)
    return 1

example :
    Experiment.succProbability
        (Conservation.extractedConservationExperiment
          (actCom zeroF zeroG encodeStateFin4) (actTag refundEmbedFin4) vecSig
          honestActAdversary) = 0 := by
  simp [Conservation.extractedConservationExperiment, Conservation.runExtractedConservation,
    ProbOracleComp.runLogWith, honestActAdversary, Conservation.extractedIssuerOracle,
    Conservation.acceptRequest, Conservation.acceptLocal,
    Conservation.Request.signedMessage, actHonestIssue, actCom, actTag, zeroF, zeroG,
    encodeStateFin4, refundEmbedFin4, vecSig, Conservation.extractedConservationAccept,
    Conservation.spentDebit, Conservation.spendsIn, Conservation.spends,
    Conservation.issuedAmount, Conservation.issuesIn, Conservation.grantedRefund,
    Experiment.succProbability, Game.succProbability]

private def actForgedSpend :
    Conservation.SpendRequest ℕ ℕ ℕ ((Fin 4 → ℤ) × ZMod 5) ((Fin 4 → ℤ) × ZMod 5) where
  ctx := 1
  nullifier := 1
  debit := 5
  refund := 0
  changeCommitment := actCom zeroF zeroG encodeStateFin4 2 1 0 0
  oldCredit := 5
  oldOpening := 0
  oldRefund := 0
  signature := actTag refundEmbedFin4 (actCom zeroF zeroG encodeStateFin4 1 1 5 0) 0
  newNullifier := 2
  newCredit := 0
  newOpening := 0

private def forgingActAdversary :
    Conservation.ExtractedAdversary ℕ ℕ ℕ ((Fin 4 → ℤ) × ZMod 5) Unit ((Fin 4 → ℤ) × ZMod 5) :=
  fun _ => do
    let _ ← ProbOracleComp.query (.spend actForgedSpend)
    return 1

-- Winnability witness (`= 1`) when the adversary fabricates an input-note signature directly.
example :
    Experiment.succProbability
        (Conservation.extractedConservationExperiment
          (actCom zeroF zeroG encodeStateFin4) (actTag refundEmbedFin4) vecSig
          forgingActAdversary) = 1 := by
  simp [Conservation.extractedConservationExperiment, Conservation.runExtractedConservation,
    ProbOracleComp.runLogWith, forgingActAdversary, Conservation.extractedIssuerOracle,
    Conservation.acceptRequest, Conservation.acceptLocal, Conservation.hasSpentNullifier,
    Conservation.SpendRequest.inputNote, Credit.target,
    Conservation.Request.signedMessage, actForgedSpend, actCom, actTag, zeroF, zeroG,
    encodeStateFin4, refundEmbedFin4, vecSig, Conservation.extractedConservationAccept,
    Conservation.spentDebit, Conservation.spendsIn, Conservation.spends,
    Conservation.issuedAmount, Conservation.issuesIn, Conservation.grantedRefund,
    Experiment.succProbability, Game.succProbability]

-- Enforcing `bound = 5` rejects `actForgedSpend` (`oldCredit = 5 ≥ 5`), giving `= 0`.
example :
    Experiment.succProbability
        (actMQConservationExperiment 5
          (actCom zeroF zeroG encodeStateFin4) (actTag refundEmbedFin4) vecSig
          forgingActAdversary) = 0 := by
  simp [actMQConservationExperiment, rangeBoundedAdversary, requestInRange, actForgedSpend,
    Conservation.extractedConservationExperiment, Conservation.runExtractedConservation,
    ProbOracleComp.runLogWith, forgingActAdversary, Conservation.extractedConservationAccept,
    Conservation.spentDebit, Conservation.spendsIn, Conservation.spends,
    Conservation.issuedAmount, Conservation.issuesIn, Conservation.grantedRefund,
    Experiment.succProbability, Game.succProbability]

private def honestClawAdversary :
    ClawAdversary Unit (Fin 4 → ℤ) ℕ ((Fin 4 → ℤ) × ZMod 5) := fun _ => do
  let σ ← ProbOracleComp.query (encodeStateFin4 1 1 10, (0 : ℕ))
  return [⟨encodeStateFin4 1 1 10, 0, σ⟩]

example :
    Experiment.succProbability
        (clawExperiment vecSig (UOV.structuredTarget zeroF zeroG) honestClawAdversary) = 0 := by
  have hev :
      ProbComp.eval
          (clawExperiment vecSig (UOV.structuredTarget zeroF zeroG) honestClawAdversary) =
        PMF.pure false := by
    simp only [clawExperiment, runClaw, honestClawAdversary,
      ProbOracleComp.runLog_query_bind_pure, vecSig, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_pure, PMF.pure_bind, PMF.pure_map]
    refine congrArg PMF.pure ?_
    simp [clawAccept]
  simp [Experiment.succProbability, Game.succProbability, hev]

-- Repeated queries at the same `J`-target cost `1` under `dedup`: `2` queries on `1` target plus
-- `2` distinct-target claims wins (`= 1`).
private def repeatedQueryClawAdversary :
    ClawAdversary Unit (Fin 4 → ℤ) ℕ ((Fin 4 → ℤ) × ZMod 5) := fun _ => do
  let σ₁ ← ProbOracleComp.query (encodeStateFin4 1 1 10, (0 : ℕ))
  let _ ← ProbOracleComp.query (encodeStateFin4 1 1 10, (0 : ℕ))
  return [⟨encodeStateFin4 1 1 10, 0, σ₁⟩,
    ⟨encodeStateFin4 2 1 10, 0, (encodeStateFin4 2 1 10, 0)⟩]

example :
    Experiment.succProbability
        (clawExperiment vecSig (UOV.structuredTarget zeroF zeroG)
          repeatedQueryClawAdversary) = 1 := by
  have hev :
      ProbComp.eval
          (clawExperiment vecSig (UOV.structuredTarget zeroF zeroG)
            repeatedQueryClawAdversary) =
        PMF.pure true := by
    simp only [clawExperiment, runClaw, repeatedQueryClawAdversary, ProbOracleComp.runLog,
      ProbOracleComp.runState_bind, ProbOracleComp.runState_query, ProbOracleComp.runState_pure,
      StateT.run_bind, StateT.run_pure]
    simp only [StateT.run, vecSig, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
      PMF.pure_bind, PMF.pure_map]
    refine congrArg PMF.pure ?_
    simp [clawAccept, UOV.structuredTarget, zeroF, zeroG, encodeStateFin4]
  simp [Experiment.succProbability, Game.succProbability, hev]

-- Duplicate `J`-target claims with `0` queries are rejected (`Nodup` enforced, `= 0`).
private def dupTargetClawAdversary :
    ClawAdversary Unit (Fin 4 → ℤ) ℕ ((Fin 4 → ℤ) × ZMod 5) := fun _ =>
  return [⟨encodeStateFin4 1 1 10, 0, (encodeStateFin4 1 1 10, 0)⟩,
    ⟨encodeStateFin4 1 1 10, 1, (encodeStateFin4 1 1 10, 0)⟩]

example :
    ProbComp.eval
        (clawExperiment vecSig (UOV.structuredTarget zeroF zeroG) dupTargetClawAdversary) =
      PMF.pure false := by
  simp only [clawExperiment, runClaw, dupTargetClawAdversary, ProbOracleComp.runLog,
    ProbOracleComp.runState_pure, StateT.run_pure, vecSig, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_pure, PMF.pure_bind, PMF.pure_map]
  refine congrArg PMF.pure ?_
  simp [clawAccept, UOV.structuredTarget, zeroF, zeroG, encodeStateFin4]

/-! ### 3. Concrete `G`-collision separation over `ZMod 5` -/

private def colF (r : ZMod 5) : ZMod 5 := r

private def colG (r : ZMod 5) : ZMod 5 := r * r

private def colSig :
    Signature.Scheme Unit Unit (ZMod 5 × ZMod 5) (ZMod 5 × ZMod 5) where
  keyGen := pure ((), ())
  sign _ target := pure target
  verify _ target σ := decide (σ = target)

private theorem colSig_correct : colSig.Correct := by
  intro _ _ target σ hσ
  simp only [colSig, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hσ
  subst hσ
  simp [colSig]

-- `colG 1 = colG 4` with `colF 1 ≠ colF 4` gives `extractedExperiment = 1` and
-- `gCollisionExperiment = 1`, yet zero claw advantage (`clawExperiment = PMF.pure false`).
example :
    Experiment.succProbability
        (extractedExperiment colSig (UOV.structuredTarget colF colG)
          (gCollisionForger colF 1 4 0)) = 1 := by
  have hev := gCollisionForger_extractedExperiment_eq_pure_true
    colSig_correct colF colG (0 : ZMod 5) (r₁ := 1) (r₂ := 4) (by decide) (by decide)
  simp [Experiment.succProbability, Game.succProbability, hev]

example :
    ProbComp.eval
        (clawExperiment colSig (UOV.structuredTarget colF colG)
          (clawReduction colSig (UOV.structuredTarget colF colG) id
            (gCollisionForger colF 1 4 0))) =
      PMF.pure false :=
  clawExperiment_clawReduction_gCollisionForger_eq_pure_false
    colSig colF colG (0 : ZMod 5) (r₁ := 1) (r₂ := 4) (by decide)

example :
    Experiment.succProbability
        (clawExperiment colSig (UOV.structuredTarget colF colG)
          (clawReduction colSig (UOV.structuredTarget colF colG) id
            (gCollisionForger colF 1 4 0))) = 0 := by
  have hev := clawExperiment_clawReduction_gCollisionForger_eq_pure_false
    colSig colF colG (0 : ZMod 5) (r₁ := 1) (r₂ := 4) (by decide)
  simp [Experiment.succProbability, Game.succProbability, hev]

example :
    Experiment.succProbability
        (gCollisionExperiment colG
          (gCollisionReduction colSig (UOV.structuredTarget colF colG)
            (gCollisionForger colF 1 4 0))) = 1 := by
  have hev :
      ProbComp.eval
          (gCollisionExperiment colG
            (gCollisionReduction colSig (UOV.structuredTarget colF colG)
              (gCollisionForger colF 1 4 0))) =
        PMF.pure true := by
    simp only [gCollisionExperiment, gCollisionReduction, bindingReduction, runExtracted,
      gCollisionForger, ProbOracleComp.runLog_query_bind_pure, colSig,
      ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.pure_bind, PMF.pure_map]
    refine congrArg PMF.pure ?_
    simp only [zero_add]
    decide
  simp [Experiment.succProbability, Game.succProbability, hev]

/-! ### 4. Zero-opening quadratic scaling attack and nonzero-tail boundary -/

private noncomputable def leftSqMap : QuadraticMap (ZMod 5) (ZMod 5) (ZMod 5 × ZMod 5) :=
  (LinearMap.inl (ZMod 5) (ZMod 5) (ZMod 5)).compQuadraticMap QuadraticMap.sq

private theorem leftSqMap_apply (x : ZMod 5) : leftSqMap x = (x * x, 0) := by
  simp [leftSqMap, QuadraticMap.sq_apply]

private noncomputable def zeroTailOptionScheme :
    Signature.Scheme Unit Unit (ZMod 5 × ZMod 5) (Option (ZMod 5)) where
  keyGen := pure ((), ())
  sign _ target := pure (if target = (1, 0) then some 1 else none)
  verify _ target opt := match opt with
    | none => false
    | some s => decide (leftSqMap s = target)

private def zeroTailF : ZMod 5 → ZMod 5 := id
private def zeroTailG : ZMod 5 → ZMod 5 := fun _ => 0

-- When `F 0 = 0` and `G 0 = 0`, one query on `(1, 0)` yields a probability-1 claw across `[1, 2]`.
example :
    Experiment.succProbability
        (clawExperiment zeroTailOptionScheme (UOV.structuredTarget zeroTailF zeroTailG)
          (zeroOpeningClawAttack (fun a => Option.map (a • ·)) [(1 : ZMod 5), 2] 1)) = 1 := by
  refine clawExperiment_zeroOpeningClawAttack_succProbability_eq_one zeroTailOptionScheme
    zeroTailF zeroTailG rfl (fun a => Option.map (a • ·)) [(1 : ZMod 5), 2] (by decide)
    (by decide) (1 : ZMod 5) (by decide) ?_
  intro keys hkeys opt hopt a _
  simp only [zeroTailOptionScheme, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hkeys hopt
  have htarget : UOV.structuredTarget zeroTailF zeroTailG (1 : ZMod 5) 0 = (1, 0) := by
    simp [UOV.structuredTarget, zeroTailF, zeroTailG]
  simp only [htarget, ↓reduceIte] at hopt
  subst hopt
  refine UOV.verify_scale_option_of_quadratic (fun _ => leftSqMap) zeroTailOptionScheme
    (fun _ _ opt => by cases opt <;> rfl) zeroTailF zeroTailG rfl rfl ?_ a
  simp [zeroTailOptionScheme, htarget, leftSqMap_apply]

private noncomputable def quadForm5 : QuadraticMap (ZMod 5) (ZMod 5 × ZMod 5) (ZMod 5) :=
  QuadraticMap.sq.comp (LinearMap.fst (ZMod 5) (ZMod 5) (ZMod 5)) +
    (2 : ZMod 5) • QuadraticMap.sq.comp (LinearMap.snd (ZMod 5) (ZMod 5) (ZMod 5))

private theorem quadForm5_apply (x : ZMod 5 × ZMod 5) :
    quadForm5 x = x.1 * x.1 + 2 * (x.2 * x.2) := by
  simp [quadForm5, QuadraticMap.sq_apply]

private noncomputable def surjSqMap :
    QuadraticMap (ZMod 5) ((ZMod 5 × ZMod 5) × (ZMod 5 × ZMod 5)) (ZMod 5 × ZMod 5) :=
  (LinearMap.inl (ZMod 5) (ZMod 5) (ZMod 5)).compQuadraticMap
      (quadForm5.comp (LinearMap.fst (ZMod 5) (ZMod 5 × ZMod 5) (ZMod 5 × ZMod 5))) +
    (LinearMap.inr (ZMod 5) (ZMod 5) (ZMod 5)).compQuadraticMap
      (quadForm5.comp (LinearMap.snd (ZMod 5) (ZMod 5 × ZMod 5) (ZMod 5 × ZMod 5)))

private theorem surjSqMap_apply (x : (ZMod 5 × ZMod 5) × (ZMod 5 × ZMod 5)) :
    surjSqMap x = (quadForm5 x.1, quadForm5 x.2) := by
  simp [surjSqMap]

private def inv5 (t : ZMod 5) : ZMod 5 × ZMod 5 :=
  match (t : Fin 5) with
  | 0 => (0, 0)
  | 1 => (1, 0)
  | 2 => (0, 1)
  | 3 => (1, 1)
  | 4 => (2, 0)

private theorem quadForm5_inv5 (t : ZMod 5) : quadForm5 (inv5 t) = t := by
  fin_cases t <;> (simp [quadForm5_apply, inv5]; rfl)

private noncomputable def surjZeroTailScheme :
    Signature.Scheme Unit Unit (ZMod 5 × ZMod 5) (Option ((ZMod 5 × ZMod 5) × (ZMod 5 × ZMod 5)))
    where
  keyGen := pure ((), ())
  sign _ target := pure (some (inv5 target.1, inv5 target.2))
  verify _ target opt := match opt with
    | none => false
    | some s => decide (surjSqMap s = target)

private theorem surjZeroTailScheme_correct : surjZeroTailScheme.Correct := by
  intro _ _ target opt hopt
  simp only [surjZeroTailScheme, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hopt
  subst hopt
  simp [surjZeroTailScheme, surjSqMap_apply, quadForm5_inv5]

-- Composed optional-preimage theorem: `F 0 = 0`, `G 0 = 0`, and `Correct` imply `PMF.pure true`.
example :
    ProbComp.eval
        (clawExperiment surjZeroTailScheme (UOV.structuredTarget zeroTailF zeroTailG)
          (zeroOpeningClawAttack (fun a => Option.map (a • ·)) [(1 : ZMod 5), 2] 1)) =
      PMF.pure true :=
  clawExperiment_zeroOpeningClawAttack_option_eq_pure_true_of_quadratic
    (fun _ => surjSqMap) surjZeroTailScheme surjZeroTailScheme_correct
    (fun _ _ opt => by cases opt <;> rfl) zeroTailF zeroTailG rfl rfl
    [(1 : ZMod 5), 2] (by decide) (by decide) (1 : ZMod 5) (by decide)

private noncomputable def diagSqMap : QuadraticMap (ZMod 5) (ZMod 5) (ZMod 5 × ZMod 5) :=
  (LinearMap.inl (ZMod 5) (ZMod 5) (ZMod 5) +
    LinearMap.inr (ZMod 5) (ZMod 5) (ZMod 5)).compQuadraticMap QuadraticMap.sq

private theorem diagSqMap_apply (x : ZMod 5) : diagSqMap x = (x * x, x * x) := by
  simp [diagSqMap, QuadraticMap.sq_apply]

private noncomputable def constTailOptionScheme :
    Signature.Scheme Unit Unit (ZMod 5 × ZMod 5) (Option (ZMod 5)) where
  keyGen := pure ((), ())
  sign _ target := pure (if target = (1, 1) then some 1 else none)
  verify _ target opt := match opt with
    | none => false
    | some s => decide (diagSqMap s = target)

private noncomputable def constTailRawScheme :
    Signature.Scheme Unit Unit (ZMod 5 × ZMod 5) (ZMod 5) where
  keyGen := pure ((), ())
  sign _ _ := pure (1 : ZMod 5)
  verify _ target s := decide (diagSqMap s = target)

private def constTailG : ZMod 5 → ZMod 5 := fun _ => 1

-- Direct target separation: when `G 0 = 1 ≠ 0`, `diagSqMap (2 • 1)` cannot hit `(4 • 1, G 0)`.
example :
    diagSqMap ((2 : ZMod 5) • (1 : ZMod 5)) ≠
      UOV.structuredTarget zeroTailF constTailG (((2 : ZMod 5) * 2) • 1) 0 := by
  refine UOV.rescale_ne_zeroOpening_of_tail_ne_zero diagSqMap zeroTailF constTailG (by decide)
    (2 : ZMod 5) (by decide) (answer := (1 : ZMod 5)) (message := (1 : ZMod 5)) ?_ ((2 * 2) • 1)
  simp [diagSqMap_apply, UOV.structuredTarget, zeroTailF, constTailG]

-- With optional preimages (`Option (ZMod 5)`) and `G 0 = 1 ≠ 0`, `zeroOpeningClawAttack` fails.
example :
    ProbComp.eval
        (clawExperiment constTailOptionScheme (UOV.structuredTarget zeroTailF constTailG)
          (zeroOpeningClawAttack (fun a => Option.map (a • ·)) [(1 : ZMod 5), 2] 1)) =
      PMF.pure false := by
  refine clawExperiment_zeroOpeningClawAttack_option_eq_false_of_tail_ne_zero
    (fun _ => diagSqMap) constTailOptionScheme (fun _ _ opt => by cases opt <;> rfl) zeroTailF
    constTailG (by decide) [(1 : ZMod 5), 2] (by decide) (by decide) (1 : ZMod 5) ?_
  intro keys _ opt hopt s hs
  simp only [constTailOptionScheme, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hopt
  have htarget : UOV.structuredTarget zeroTailF constTailG (1 : ZMod 5) 0 = (1, 1) := by
    simp [UOV.structuredTarget, zeroTailF, constTailG]
  simp only [htarget, ↓reduceIte] at hopt
  subst hopt
  cases hs
  simp [diagSqMap_apply, htarget]

-- With raw preimages (`ZMod 5`) and `G 0 = 1 ≠ 0`, `zeroOpeningClawAttack` fails identically.
example :
    ProbComp.eval
        (clawExperiment constTailRawScheme (UOV.structuredTarget zeroTailF constTailG)
          (zeroOpeningClawAttack (fun a s => a • s) [(1 : ZMod 5), 2] 1)) =
      PMF.pure false := by
  refine clawExperiment_zeroOpeningClawAttack_eq_false_of_tail_ne_zero
    (fun _ => diagSqMap) constTailRawScheme (fun _ _ _ => rfl) zeroTailF constTailG
    (by decide) [(1 : ZMod 5), 2] (by decide) (by decide) (1 : ZMod 5) ?_
  intro keys _ s hs
  simp only [constTailRawScheme, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hs
  subst hs
  simp [diagSqMap_apply, UOV.structuredTarget, zeroTailF, constTailG]

end CslibFrontierTests.Crypto.AnonymousTokenACTMQ
