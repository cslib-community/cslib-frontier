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
* disjoint-coordinate `Fin 4 → ℤ` instantiation `(nf, ctx, t, 0) + (0, 0, 0, x)` proving
  `actEmbed` injectivity via `actEmbed_injective_of_disjoint` and instantiating
  `actMQConservation_succProbability_le` and `actMQClawReduction_queryBound`;
* concrete `actCom`/`actTag` credit-conservation witnesses (`= 0` honest run and `= 1` forging
  run) and an honest `1`-query `clawExperiment` witness (`= 0`);
* concrete `G`-collision separation over `ZMod 5`: `gCollisionForger` wins `extractedExperiment`
  with probability `1` and triggers `gCollisionExperiment = 1` via `gCollisionReduction`, while
  `clawExperiment ... (clawReduction ... id (gCollisionForger ...)) = PMF.pure false`;
* concrete zero-opening scaling over `ZMod 5` (`Sig = Option (ZMod 5)` matching
  `UOV.idealRawScheme`, `pubMap = QuadraticMap.sq` on the first coordinate, `scalars = [1, 2]`):
  wins `clawExperiment` with probability `1` when `G 0 = 0` (`verify_scale_option_of_quadratic`),
  and fails identically (`PMF.pure false`) for both optional and raw preimages when `G 0 = 1 ≠ 0`
  (`UOV.rescale_ne_zeroOpening_of_tail_ne_zero`);
* `[VOLEACT2026]` `#mq-commitment` arithmetic regressions (`131 - 32 - 83 = 16`,
  `256 ^ 16 = 2 ^ 128`).
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.AnonymousTokenACTMQ

open Cslib Cslib.Crypto Cslib.Crypto.AnonymousToken Cslib.Crypto.AnonymousToken.ACTMQ
open Probability
open scoped NNReal

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-! ### 1. Disjoint-slot `Fin 4 → ℤ` embedding and Theorem 3 client -/

/-- State embedding `(nf, ctx, t) ↦ ![↑nf, ↑ctx, ↑t, 0]`, vanishing on the refund slot `3`. -/
private def encodeStateFin4 (nf ctx t : ℕ) : Fin 4 → ℤ :=
  ![(nf : ℤ), (ctx : ℤ), (t : ℤ), 0]

/-- Refund embedding `x ↦ ![0, 0, 0, ↑x]`, vanishing off slot `3`. -/
private def refundEmbedFin4 (x : ℕ) : Fin 4 → ℤ :=
  ![0, 0, 0, (x : ℤ)]

private def isRefundFin4 (i : Fin 4) : Bool := decide (i = 3)

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

-- Generic Theorem 3 client on the disjoint `Fin 4 → ℤ` block split.
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
  actMQConservation_succProbability_le F G encodeStateFin4 refundEmbedFin4
    actEmbed_fin4_injective S A

example {R Tail PK SK Sig : Type}
    [DecidableEq Tail] [Inhabited R] [Inhabited Sig]
    (F : R → Fin 4 → ℤ) (G : R → Tail)
    (S : Signature.Scheme PK SK ((Fin 4 → ℤ) × Tail) Sig)
    (A : Conservation.ExtractedAdversary ℕ ℕ R ((Fin 4 → ℤ) × Tail) PK Sig)
    (pk : PK) {q : ℕ} (hA : (A pk).IsQueryBounded q) :
    (clawReduction S (UOV.structuredTarget F G) (actEmbed encodeStateFin4 refundEmbedFin4)
      (Conservation.noteForger (actCom F G encodeStateFin4) (actTag refundEmbedFin4) S A)
        pk).IsQueryBounded q :=
  actMQClawReduction_queryBound F G encodeStateFin4 refundEmbedFin4 S A pk hA

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
  refine zeroOpeningClawAttack_succProbability_eq_one zeroTailOptionScheme zeroTailF zeroTailG rfl
    (fun a => Option.map (a • ·)) [(1 : ZMod 5), 2] (by decide) (by decide) (1 : ZMod 5)
    (by decide) ?_
  intro keys hkeys opt hopt a _
  simp only [zeroTailOptionScheme, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hkeys hopt
  have htarget : UOV.structuredTarget zeroTailF zeroTailG (1 : ZMod 5) 0 = (1, 0) := by
    simp [UOV.structuredTarget, zeroTailF, zeroTailG]
  simp only [htarget, ↓reduceIte] at hopt
  subst hopt
  refine verify_scale_option_of_quadratic (fun _ => leftSqMap) zeroTailOptionScheme
    (fun _ _ opt => by cases opt <;> rfl) zeroTailF zeroTailG rfl rfl ?_ a
  simp [zeroTailOptionScheme, htarget, leftSqMap_apply]

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

/-! ### 5. `[VOLEACT2026]` `#mq-commitment` parameter arithmetic regressions -/

-- `m_com - k - r_len = 131 - 32 - 83 = 16` coordinates in `GF(2^8)` (`256^16 = 2^128`).
example : (131 : ℕ) - 32 - 83 = 16 := by decide
example : (256 : ℕ) ^ 16 = 2 ^ 128 := by decide

-- Semantic message width `nf_len + ctx_len + 2 * 1 = 16 + 12 + 2 + 2 = 32` bytes.
example : (16 : ℕ) + 12 + 2 + 2 = 32 := by decide

end CslibFrontierTests.Crypto.AnonymousTokenACTMQ
