/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module

import CslibFrontier.Crypto.Protocols.UOV.Attacks
import CslibFrontier.Crypto.Protocols.UOV.HashAndSign
import Mathlib.Algebra.Field.ZMod

/-!
# Clients and boundary regressions for classical ROM hash-and-sign UOV

Exercises `Cslib.Crypto.UOV.HashAndSign` through an ordinary module import:
* `idealUOVSystem` over arbitrary finite fields (`idealUOVSystem_toRawScheme`) and `ZMod 5`
  (`v = 1, o = 1`), verifying equality of `.toRawScheme` with `UOV.idealRawScheme` and explicit
  rejection of `none` preimages;
* a concrete invertible `TrapdoorPreimageSystem` (`bijectiveSys` over `ZMod 5`) demonstrating
  completeness (`detScheme_correct`, `saltedScheme_correct`) together with probability-one
  acceptance/winnability witnesses for `detScheme`, `saltedScheme`, and
  `romExtractedConservationExperiment`, plus a probability-zero honest conservation run;
* negative boundary 1: without the random-oracle `Tag` layer, raw `idealUOVSystem.toRawScheme` is
  broken with probability `1` by `UOV.eval_rawZeroForger` (zero queries) and unhashed quadratic
  maps are broken by `UOV.rescaleAttack_freshTarget` (one query);
* negative boundary 2: with `Salt = Unit` (`|Salt| = 1`), `unitSaltForger` instantiates
  `saltedRomWorldEufCma_succProbability_le` with salt-collision slack `1` (making the bound
  trivial at `|Salt| = 1`), whereas `Salt = Fin 64` reduces the slack term to `1 / 64`;
* concrete `idealUOVSystem` (`ZMod 5`, `v = 1, o = 1`) clients instantiating
  `eufCmaGame_detScheme_succProbability_le`, `eufCmaGame_saltedScheme_succProbability_le`,
  `romExtractedConservationExperiment_detScheme_succProbability_le`, and
  `romExtractedConservationExperiment_saltedScheme_succProbability_le`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.UOVHashAndSign

open Cslib Cslib.Crypto Cslib.Crypto.UOV Cslib.Crypto.UOV.HashAndSign
open Cslib.Crypto.AnonymousToken Cslib.Crypto.AnonymousToken.Conservation
open Cslib.Crypto.Protocols Probability
open scoped NNReal

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-! ### 1. `idealUOVSystem` bridge and explicit failure -/

example {F : Type} [Field F] [Fintype F] [DecidableEq F] (v o : ℕ)
    (derive : IdealKeyMaterial F v o → (Fin o → F) → ProbComp (Option (Fin (v + o) → F))) :
    (idealUOVSystem F v o derive).toRawScheme = UOV.idealRawScheme derive :=
  idealUOVSystem_toRawScheme F v o derive

example (derive : IdealKeyMaterial (ZMod 5) 1 1 → (Fin 1 → ZMod 5) →
    ProbComp (Option (Fin (1 + 1) → ZMod 5))) :
    (idealUOVSystem (ZMod 5) 1 1 derive).toRawScheme = UOV.idealRawScheme derive :=
  idealUOVSystem_toRawScheme (ZMod 5) 1 1 derive

example (derive : IdealKeyMaterial (ZMod 5) 1 1 → (Fin 1 → ZMod 5) →
    ProbComp (Option (Fin (1 + 1) → ZMod 5)))
    (P : MultivariateQuadraticMap (ZMod 5) (Fin (1 + 1)) (Fin 1)) (y : Fin 1 → ZMod 5) :
    (idealUOVSystem (ZMod 5) 1 1 derive).check P y none = false := rfl

/-! ### 2. Concrete invertible system, completeness, and winnability witnesses -/

/-- A trivial bijective `TrapdoorPreimageSystem` on `ZMod 5` (`eval () x = x`,
`invert () y = some y`) used to witness completeness, forgery acceptance, and
conservation-game winnability. -/
private noncomputable def bijectiveSys : TrapdoorPreimageSystem Unit Unit (ZMod 5) (ZMod 5) where
  keyGen := pure ((), ())
  eval _ x := x
  invert _ y := pure (some y)
  samplePreimage _ := ProbComp.uniform (ZMod 5)

private theorem bijectiveSys_invertCorrect : bijectiveSys.InvertCorrect := by
  intro _ _ y xOpt hx
  simp only [bijectiveSys, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hx
  subst hx
  exact ⟨y, rfl, rfl⟩

example : (detScheme (M := ℕ) bijectiveSys).Correct :=
  detScheme_correct bijectiveSys_invertCorrect

example : (saltedScheme (M := ℕ) bijectiveSys (ZMod 5)).Correct :=
  saltedScheme_correct bijectiveSys_invertCorrect

/-- Zero-sign, one-hash forger against `detScheme bijectiveSys`: queries `H 0` and outputs
`(0, some y)`. -/
private def bijectiveDetForger :
    Unit → ProbOracleComp (ROMSignature.ForgerSpec ℕ ℕ (Option (ZMod 5)) (ZMod 5))
      (ℕ × Option (ZMod 5)) := fun _ => do
  let y ← ProbOracleComp.query
    (spec := ROMSignature.ForgerSpec ℕ ℕ (Option (ZMod 5)) (ZMod 5)) (.inr 0)
  return (0, some y)

example : ProbForgerCallBounded bijectiveDetForger 0 1 := by
  intro _
  refine ⟨?_, ?_⟩
  · exact (OracleComp.IsCostBounded.query
      (cost := Sum.elim (fun _ => 0) ROMSignature.signingCost) (Sum.inr (.inr 0))).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0
  · exact (OracleComp.IsCostBounded.query
      (cost := Sum.elim (fun _ => 0) ROMSignature.hashCost) (Sum.inr (.inr 0))).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0

/-- `bijectiveDetForger` wins `detScheme bijectiveSys` with probability `1`. -/
example :
    Game.succProbability
      (ROMSignature.worldGame (detScheme bijectiveSys) bijectiveDetForger eufCmaAccept) = 1 := by
  have h :
      ROMSignature.worldGame (detScheme bijectiveSys) bijectiveDetForger eufCmaAccept =
        PMF.pure true := by
    simp only [ROMSignature.worldGame, detScheme, bijectiveSys, ProbComp.eval_pure,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind]
    have hconst : ∀ f : ZMod 5 → Option (ZMod 5),
        Interactive.World.eval (ROMSignature.world (detScheme bijectiveSys) ((), f))
          (ROMSignature.worldRealize (detScheme bijectiveSys) () (bijectiveDetForger ())
            eufCmaAccept) = PMF.pure true := by
      intro f
      rw [ROMSignature.eval_world_worldRealize, ROMSignature.runLoggedForger,
        ProbOracleComp.runWith_run_interpret]
      simp only [bijectiveDetForger, detScheme, bijectiveSys, TrapdoorPreimageSystem.check,
        eufCmaAccept, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
        ProbOracleComp.runWith_pure, ROMSignature.logSigning, ROMSignature.forgerWorldImpl,
        OracleComp.sumHandler, StateT.run, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
        PMF.map_bind, PMF.bind_bind, PMF.pure_bind, PMF.pure_map]
      change ((ROMSignature.oracle (ZMod 5) 0).run []).bind _ = _
      rw [ROMSignature.run_oracle_of_lookup_eq_none (by rfl), PMF.bind_bind]
      have hstep : ∀ y : ZMod 5,
          ((OracleComp.interpret (ROMSignature.oracle (ZMod 5))
              (do let y' ← OracleComp.query 0; pure (decide (y = y')))).run [(0, y)]).bind
            (fun verified => PMF.pure verified.1) = PMF.pure true := by
        intro y
        change (((ROMSignature.oracle (ZMod 5) 0).run [(0, y)]).bind
          (fun x => PMF.pure (decide (y = x.1), x.2))).bind _ = _
        rw [ROMSignature.run_oracle_of_lookup_eq_some (c := y) (by simp)]
        simp [PMF.pure_bind]
      simp only [List.map_nil, List.contains_nil, Bool.not_false, Bool.and_true, PMF.pure_bind]
      trans ((PMF.uniformOfFintype (ZMod 5)).bind fun _ => PMF.pure true)
      · congr 1; funext y; exact hstep y
      · exact PMF.bind_const _ _
    rw [PMF.bind_bind]
    simp only [PMF.pure_bind]
    trans ((PMF.pi fun y : ZMod 5 => PMF.pure (some y)).bind fun _ => PMF.pure true)
    · congr 1; funext f; exact hconst f
    · exact PMF.bind_const _ _
  simp [Game.succProbability, h]

/-- Zero-sign, one-hash forger against `saltedScheme bijectiveSys (ZMod 5)`. -/
private def bijectiveSaltedForger :
    Unit → ProbOracleComp
      (ROMSignature.ForgerSpec ℕ (ℕ × ZMod 5) (ZMod 5 × Option (ZMod 5)) (ZMod 5))
      (ℕ × (ZMod 5 × Option (ZMod 5))) := fun _ => do
  let y ← ProbOracleComp.query
    (spec := ROMSignature.ForgerSpec ℕ (ℕ × ZMod 5) (ZMod 5 × Option (ZMod 5)) (ZMod 5))
    (.inr (0, 0))
  return (0, (0, some y))

/-- `bijectiveSaltedForger` wins `saltedScheme bijectiveSys (ZMod 5)` with probability `1`. -/
example :
    Game.succProbability
      (ROMSignature.worldGame (saltedScheme bijectiveSys (ZMod 5))
        bijectiveSaltedForger eufCmaAccept) = 1 := by
  have h :
      ROMSignature.worldGame (saltedScheme bijectiveSys (ZMod 5))
        bijectiveSaltedForger eufCmaAccept = PMF.pure true := by
    simp only [ROMSignature.worldGame, saltedScheme, bijectiveSys, ProbComp.eval_pure,
      PMF.monad_bind_eq_bind, PMF.pure_bind]
    rw [ROMSignature.eval_world_worldRealize, ROMSignature.runLoggedForger,
      ProbOracleComp.runWith_run_interpret]
    simp only [bijectiveSaltedForger, TrapdoorPreimageSystem.check,
      eufCmaAccept, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
      ProbOracleComp.runWith_pure, ROMSignature.logSigning, ROMSignature.forgerWorldImpl,
      OracleComp.sumHandler, StateT.run, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.map_bind, PMF.bind_bind, PMF.pure_bind, PMF.pure_map]
    change ((ROMSignature.oracle (ZMod 5) (0, 0)).run []).bind _ = _
    rw [ROMSignature.run_oracle_of_lookup_eq_none (by rfl), PMF.bind_bind]
    have hstep : ∀ y : ZMod 5,
        ((OracleComp.interpret (ROMSignature.oracle (ZMod 5))
            (do
              let y' ← OracleComp.query ((0 : ℕ), (0 : ZMod 5))
              pure (decide (y = y')))).run
          [(((0 : ℕ), (0 : ZMod 5)), y)]).bind
          (fun verified => PMF.pure verified.1) = PMF.pure true := by
      intro y
      change (((ROMSignature.oracle (ZMod 5) ((0 : ℕ), (0 : ZMod 5))).run
          [(((0 : ℕ), (0 : ZMod 5)), y)]).bind
        (fun x => PMF.pure (decide (y = x.1), x.2))).bind _ = _
      rw [ROMSignature.run_oracle_of_lookup_eq_some (c := y) (by simp)]
      simp [PMF.pure_bind]
    simp only [List.map_nil, List.contains_nil, Bool.not_false, Bool.and_true, PMF.pure_bind]
    trans ((PMF.uniformOfFintype (ZMod 5)).bind fun _ => PMF.pure true)
    · congr 1; funext y; exact hstep y
    · exact PMF.bind_const _ _
  simp [Game.succProbability, h]

/-- Keyless injective commitment `(nf, ctx, credit)` ignoring opening randomness. -/
private def testCom (nf ctx t _r : ℕ) : ℕ × ℕ × ℕ := (nf, ctx, t)

/-- Keyless `Crypto.Commitment.Scheme` wrapping `testCom`. -/
private def testComScheme :
    Crypto.Commitment.Scheme Unit (ℕ × ℕ × ℕ) (ℕ × ℕ × ℕ) ℕ where
  keyGen := pure ()
  commit _ m := pure (m, 0)
  verify _ m c _ := decide (m = c)

/-- Conservation adversary against `detScheme bijectiveSys`: queries `H ((1, 1, 10), 0)` directly
without issuing, then submits a forged spend of debit `5`, winning conservation (`0 + 0 < 5`). -/
private def bijectiveConsForger :
    ROMExtractedAdversary ℕ ℕ ℕ (ℕ × ℕ × ℕ) Unit (Option (ZMod 5))
      ((ℕ × ℕ × ℕ) × ℕ) (ZMod 5) := fun _ => do
  let y ← ProbOracleComp.query
    (spec := (fun _ : Request ℕ ℕ ℕ (ℕ × ℕ × ℕ) (Option (ZMod 5)) => Option (Option (ZMod 5))) ⊕ₒ
      (fun _ : (ℕ × ℕ × ℕ) × ℕ => ZMod 5))
    (.inr ((1, 1, 10), 0))
  let _ ← ProbOracleComp.query
    (spec := (fun _ : Request ℕ ℕ ℕ (ℕ × ℕ × ℕ) (Option (ZMod 5)) => Option (Option (ZMod 5))) ⊕ₒ
      (fun _ : (ℕ × ℕ × ℕ) × ℕ => ZMod 5))
    (.inl (.spend
      { ctx := 1, nullifier := 1, debit := 5, refund := 0, changeCommitment := (2, 1, 5),
        oldCredit := 10, oldOpening := 0, oldRefund := 0, signature := some y,
        newNullifier := 2, newCredit := 5, newOpening := 0 }))
  return 1

/-- `bijectiveConsForger` wins `romExtractedConservationExperiment` with probability `1`
(non-vacuity / winnability witness). -/
example :
    Game.succProbability
      (romExtractedConservationExperiment testCom (detScheme bijectiveSys)
        bijectiveConsForger) = 1 := by
  have h :
      romExtractedConservationExperiment testCom (detScheme bijectiveSys)
        bijectiveConsForger = PMF.pure true := by
    simp only [romExtractedConservationExperiment, runROMExtractedConservation, detScheme,
      bijectiveSys, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.map_bind, PMF.pure_bind]
    have hconst : ∀ f : ZMod 5 → Option (ZMod 5),
        (ProbOracleComp.runWith
          (romExtractedIssuerHandler testCom (detScheme bijectiveSys) ((), (), f))
          (bijectiveConsForger ()) ([], [])).map
          (fun (targetCtx, _, accepted) =>
            decide (issuedAmount accepted targetCtx + grantedRefund accepted targetCtx <
              spentDebit accepted targetCtx)) = PMF.pure true := by
      intro f
      simp only [bijectiveConsForger, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
        ProbOracleComp.runWith_pure, romExtractedIssuerHandler, detScheme, bijectiveSys,
        TrapdoorPreimageSystem.check, testCom, Credit.target, SpendRequest.inputNote,
        hasSpentNullifier, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind,
        PMF.bind_bind, PMF.pure_bind, PMF.pure_map]
      rw [ROMSignature.run_oracle_of_lookup_eq_none (by rfl), PMF.bind_bind]
      have hstep : ∀ y : ZMod 5,
          (((((ROMSignature.oracle (ZMod 5) ((1, 1, 10), 0)).run [(((1, 1, 10), 0), y)]).bind
              fun x => PMF.pure (decide (y = x.1), x.2)).bind fun x =>
            if x.1 = true then
              (((ROMSignature.oracle (ZMod 5) ((2, 1, 5), 0)).run x.2).bind
                fun x' => PMF.pure (f x'.1, x'.2)).bind fun x' =>
                PMF.pure (some x'.1, x'.2, [Request.spend
                  { ctx := 1, nullifier := 1, debit := 5, refund := 0,
                    changeCommitment := (2, 1, 5), oldCredit := 10, oldOpening := 0,
                    oldRefund := 0, signature := some y, newNullifier := 2, newCredit := 5,
                    newOpening := 0 }])
            else PMF.pure (none, x.2, [])).bind fun (_, _, accepted) =>
              PMF.pure (decide (issuedAmount accepted 1 + grantedRefund accepted 1 <
                spentDebit accepted 1))) = PMF.pure true := by
        intro y
        rw [ROMSignature.run_oracle_of_lookup_eq_some (c := y) (by rfl)]
        simp only [PMF.pure_bind, decide_true, ↓reduceIte, PMF.bind_bind]
        rw [ROMSignature.run_oracle_of_lookup_eq_none (by simp)]
        simp only [PMF.bind_bind, PMF.pure_bind, issuedAmount, grantedRefund, spentDebit,
          issuesIn, spendsIn, spends]
        exact PMF.bind_const (PMF.uniformOfFintype (ZMod 5)) (PMF.pure true)
      simp only [PMF.pure_bind]
      trans ((PMF.uniformOfFintype (ZMod 5)).bind fun _ => PMF.pure true)
      · congr 1; funext y; exact hstep y
      · exact PMF.bind_const _ _
    rw [PMF.bind_bind]
    simp only [PMF.pure_bind]
    trans ((PMF.pi fun y : ZMod 5 => PMF.pure (some y)).bind fun _ => PMF.pure true)
    · congr 1; funext f; exact hconst f
    · exact PMF.bind_const _ _
  simp [Game.succProbability, h]

/-- Honest non-overspending adversary: issues `10` in context `1` and does not overspend. -/
private def honestConsAdversary :
    ROMExtractedAdversary ℕ ℕ ℕ (ℕ × ℕ × ℕ) Unit (Option (ZMod 5))
      ((ℕ × ℕ × ℕ) × ℕ) (ZMod 5) := fun _ => do
  let _ ← ProbOracleComp.query
    (spec := (fun _ : Request ℕ ℕ ℕ (ℕ × ℕ × ℕ) (Option (ZMod 5)) => Option (Option (ZMod 5))) ⊕ₒ
      (fun _ : (ℕ × ℕ × ℕ) × ℕ => ZMod 5))
    (.inl (.issue
      { ctx := 1, amount := 10, commitment := (1, 1, 10), nullifier := 1, opening := 0 }))
  return 1

example :
    Game.succProbability
      (romExtractedConservationExperiment testCom (detScheme bijectiveSys)
        honestConsAdversary) = 0 := by
  have h :
      romExtractedConservationExperiment testCom (detScheme bijectiveSys)
        honestConsAdversary = PMF.pure false := by
    simp only [romExtractedConservationExperiment, runROMExtractedConservation, detScheme,
      bijectiveSys, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.map_bind, PMF.pure_bind]
    have hconst : ∀ f : ZMod 5 → Option (ZMod 5),
        (ProbOracleComp.runWith
          (romExtractedIssuerHandler testCom (detScheme bijectiveSys) ((), (), f))
          (honestConsAdversary ()) ([], [])).map
          (fun (targetCtx, _, accepted) =>
            decide (issuedAmount accepted targetCtx + grantedRefund accepted targetCtx <
              spentDebit accepted targetCtx)) = PMF.pure false := by
      intro f
      simp only [honestConsAdversary, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
        ProbOracleComp.runWith_pure, romExtractedIssuerHandler, detScheme, bijectiveSys, testCom,
        decide_true, ↓reduceIte, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind,
        PMF.bind_bind, PMF.pure_bind, PMF.pure_map]
      change (((ROMSignature.oracle (ZMod 5) ((1, 1, 10), 0)).run []).bind
        fun x => PMF.pure (f x.1, x.2)).bind _ = _
      rw [ROMSignature.run_oracle_of_lookup_eq_none (by rfl)]
      simp only [PMF.bind_bind, PMF.pure_bind, issuedAmount, grantedRefund, spentDebit,
        issuesIn, spendsIn, spends]
      exact PMF.bind_const (PMF.uniformOfFintype (ZMod 5)) (PMF.pure false)
    rw [PMF.bind_bind]
    simp only [PMF.pure_bind]
    trans ((PMF.pi fun y : ZMod 5 => PMF.pure (some y)).bind fun _ => PMF.pure false)
    · congr 1; funext f; exact hconst f
    · exact PMF.bind_const _ _
  simp [Game.succProbability, h]

/-! ### 3. Negative boundary 1: unhashed raw UOV breaks with probability `1` -/

example (derive : IdealKeyMaterial (ZMod 5) 1 1 → (Fin 1 → ZMod 5) →
    ProbComp (Option (Fin (1 + 1) → ZMod 5))) :
    ProbComp.eval
        ((idealUOVSystem (ZMod 5) 1 1 derive).toRawScheme.eufCmaExperiment UOV.rawZeroForger) =
      PMF.pure true :=
  UOV.eval_rawZeroForger derive

private def testSquare : QuadraticMap (ZMod 5) (ZMod 5) (ZMod 5) := QuadraticMap.sq

example :
    (ProbComp.eval ((UOV.rescaleAttack (X := ZMod 5) (2 : ZMod 5)
      (((2 : ZMod 5) * 2)⁻¹ • (1 : ZMod 5))).runLog (fun _ => pure 2))).map
      (fun result => decide (testSquare result.1 = 1 ∧
        (1 : ZMod 5) ∉ result.2.map Prod.fst ∧ result.2.length = 1)) = PMF.pure true := by
  apply UOV.rescaleAttack_freshTarget testSquare 2 1 (by decide) (by decide) (by decide)
  intro answer hmem
  simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hmem
  subst answer
  norm_num [testSquare, QuadraticMap.sq_apply, smul_eq_mul]
  exact (inv_eq_of_mul_eq_one_left (by decide : (4 : ZMod 5) * 4 = 1)).symm

/-! ### 4. Negative boundary 2: small salt space `Salt = Unit` makes the slack trivial (`1`) -/

/-- A `1`-sign, `1`-hash forger against `saltedScheme sys Unit`: every signing call uses the sole
salt `() : Unit`, colliding with its prior `H (0, ())` query with probability `1`. -/
private def unitSaltForger {PK Preimage Target : Type} :
    PK → ProbOracleComp
      (ROMSignature.ForgerSpec ℕ (ℕ × Unit) (Unit × Option Preimage) Target)
      (ℕ × (Unit × Option Preimage)) := fun _ => do
  let _ ← ProbOracleComp.query
    (spec := ROMSignature.ForgerSpec ℕ (ℕ × Unit) (Unit × Option Preimage) Target) (.inr (0, ()))
  let sig ← ProbOracleComp.query
    (spec := ROMSignature.ForgerSpec ℕ (ℕ × Unit) (Unit × Option Preimage) Target) (.inl 0)
  return (1, sig)

private theorem unitSaltForger_callBounded {PK Preimage Target : Type} :
    ProbForgerCallBounded (unitSaltForger (PK := PK) (Preimage := Preimage) (Target := Target))
      1 1 := by
  intro _
  refine ⟨?_, ?_⟩
  · exact (OracleComp.IsCostBounded.query
      (cost := Sum.elim (fun _ => 0) ROMSignature.signingCost) (Sum.inr (.inr (0, ())))).bind
      fun _ => (OracleComp.IsCostBounded.query
        (cost := Sum.elim (fun _ => 0) ROMSignature.signingCost) (Sum.inr (.inl 0))).bind
        fun _ => OracleComp.IsCostBounded.pure _ 0
  · exact (OracleComp.IsCostBounded.query
      (cost := Sum.elim (fun _ => 0) ROMSignature.hashCost) (Sum.inr (.inr (0, ())))).bind
      fun _ => (OracleComp.IsCostBounded.query
        (cost := Sum.elim (fun _ => 0) ROMSignature.hashCost) (Sum.inr (.inl 0))).bind
        fun _ => OracleComp.IsCostBounded.pure _ 0

/-- At `|Salt| = 1` (`Salt = Unit`) and `q_S = 1, q_H = 1`, the slack term equals `1`, so the
bound is trivial at `|Salt| = 1`. -/
example {PK SK Preimage Target : Type} [DecidableEq Target] [Fintype Target] [Nonempty Target]
    [Finite Preimage] (sys : TrapdoorPreimageSystem PK SK Target Preimage) :
    Game.succProbability
        (ROMSignature.worldGame (saltedScheme sys Unit) unitSaltForger eufCmaAccept) ≤
      (1 + 1 : ℝ≥0) *
        Experiment.succProbability
          (Signature.targetExperiment sys.toRawScheme (fun _ => ProbComp.uniform Target)
            (saltedInverter sys Unit 1 unitSaltForger)) +
      Experiment.advantage
        (psExperimentReal sys (saltedPSDistinguisher sys Unit unitSaltForger))
        (psExperimentSim sys (saltedPSDistinguisher sys Unit unitSaltForger)) + 1 := by
  have := saltedRomWorldEufCma_succProbability_le sys unitSaltForger unitSaltForger_callBounded
  simpa using this

/-- Increasing the salt space to `Fin 64` reduces the same `(q_S = 1, q_H = 1)` slack term to
`1 / 64`. -/
example {PK SK M Preimage Target : Type} [DecidableEq M] [DecidableEq Target] [Fintype Target]
    [Nonempty Target] [Finite Preimage] (sys : TrapdoorPreimageSystem PK SK Target Preimage)
    (forger : PK → ProbOracleComp
      (ROMSignature.ForgerSpec M (M × Fin 64) (Fin 64 × Option Preimage) Target)
      (M × (Fin 64 × Option Preimage)))
    (h : ProbForgerCallBounded forger 1 1) :
    Game.succProbability
        (ROMSignature.worldGame (saltedScheme sys (Fin 64)) forger eufCmaAccept) ≤
      (1 + 1 : ℝ≥0) *
        Experiment.succProbability
          (Signature.targetExperiment sys.toRawScheme (fun _ => ProbComp.uniform Target)
            (saltedInverter sys (Fin 64) 1 forger)) +
      Experiment.advantage
        (psExperimentReal sys (saltedPSDistinguisher sys (Fin 64) forger))
        (psExperimentSim sys (saltedPSDistinguisher sys (Fin 64) forger)) + (64 : ℝ≥0)⁻¹ := by
  have := saltedRomWorldEufCma_succProbability_le sys forger h
  simpa using this

/-! ### 5. End-to-end ROM EUF-CMA and extracted+ROM credit-conservation clients -/

example (derive : IdealKeyMaterial (ZMod 5) 1 1 → (Fin 1 → ZMod 5) →
      ProbComp (Option (Fin (1 + 1) → ZMod 5)))
    (A : ROMSignature.Forger
      (MultivariateQuadraticMap (ZMod 5) (Fin (1 + 1)) (Fin 1))
      ℕ (Fin 64 × Option (Fin (1 + 1) → ZMod 5)) (ℕ × Fin 64) (Fin 1 → ZMod 5))
    (coinSampler : ProbComp A.Coins) (hcoins : A.coins = ProbComp.eval coinSampler)
    {q_S q_H : ℕ} (hA : A.CallBounded q_S q_H) :
    Game.succProbability
        (ROMSignature.eufCmaGame (saltedScheme (idealUOVSystem (ZMod 5) 1 1 derive) (Fin 64)) A) ≤
      (q_H + 1 : ℝ≥0) *
        Experiment.succProbability
          (Signature.targetExperiment (idealUOVSystem (ZMod 5) 1 1 derive).toRawScheme
            (fun _ => ProbComp.uniform (Fin 1 → ZMod 5))
            (saltedInverter (idealUOVSystem (ZMod 5) 1 1 derive) (Fin 64) q_H
              (liftForger A coinSampler))) +
      Experiment.advantage
        (psExperimentReal (idealUOVSystem (ZMod 5) 1 1 derive)
          (saltedPSDistinguisher (idealUOVSystem (ZMod 5) 1 1 derive) (Fin 64)
            (liftForger A coinSampler)))
        (psExperimentSim (idealUOVSystem (ZMod 5) 1 1 derive)
          (saltedPSDistinguisher (idealUOVSystem (ZMod 5) 1 1 derive) (Fin 64)
            (liftForger A coinSampler))) +
      ((q_S * q_H + q_S.choose 2 : ℕ) : ℝ≥0) * (Fintype.card (Fin 64) : ℝ≥0)⁻¹ :=
  eufCmaGame_saltedScheme_succProbability_le (idealUOVSystem (ZMod 5) 1 1 derive)
    A coinSampler hcoins hA

example (derive : IdealKeyMaterial (ZMod 5) 1 1 → (Fin 1 → ZMod 5) →
      ProbComp (Option (Fin (1 + 1) → ZMod 5)))
    (A : ROMSignature.Forger
      (MultivariateQuadraticMap (ZMod 5) (Fin (1 + 1)) (Fin 1))
      ℕ (Option (Fin (1 + 1) → ZMod 5)) ℕ (Fin 1 → ZMod 5))
    (coinSampler : ProbComp A.Coins) (hcoins : A.coins = ProbComp.eval coinSampler)
    {q_S q_H : ℕ} (hA : A.CallBounded q_S q_H) :
    Game.succProbability
        (ROMSignature.eufCmaGame (detScheme (idealUOVSystem (ZMod 5) 1 1 derive)) A) ≤
      (q_H + 1 : ℝ≥0) *
        (Experiment.succProbability
          (Signature.targetExperiment (idealUOVSystem (ZMod 5) 1 1 derive).toRawScheme
            (fun _ => ProbComp.uniform (Fin 1 → ZMod 5))
            (detInverter (idealUOVSystem (ZMod 5) 1 1 derive) q_H (liftForger A coinSampler))) +
        Experiment.advantage
          (psExperimentReal (idealUOVSystem (ZMod 5) 1 1 derive)
            (detPSOneDistinguisher (idealUOVSystem (ZMod 5) 1 1 derive) q_H
              (liftForger A coinSampler)))
          (psExperimentSim (idealUOVSystem (ZMod 5) 1 1 derive)
            (detPSOneDistinguisher (idealUOVSystem (ZMod 5) 1 1 derive) q_H
              (liftForger A coinSampler)))) +
      Experiment.advantage
        (psExperimentReal (idealUOVSystem (ZMod 5) 1 1 derive)
          (detPSDistinguisher (idealUOVSystem (ZMod 5) 1 1 derive) (liftForger A coinSampler)))
        (psExperimentSim (idealUOVSystem (ZMod 5) 1 1 derive)
          (detPSDistinguisher (idealUOVSystem (ZMod 5) 1 1 derive) (liftForger A coinSampler))) +
      ((q_S + q_H).choose 2 : ℝ≥0) * (Fintype.card (Fin 1 → ZMod 5) : ℝ≥0)⁻¹ :=
  eufCmaGame_detScheme_succProbability_le (idealUOVSystem (ZMod 5) 1 1 derive)
    A coinSampler hcoins hA

/-- End-to-end extracted+ROM credit conservation instantiated on `idealUOVSystem` (deterministic
unsalted `Tag`) and keyless `testComScheme`. -/
example (derive : IdealKeyMaterial (ZMod 5) 1 1 → (Fin 1 → ZMod 5) →
      ProbComp (Option (Fin (1 + 1) → ZMod 5)))
    (A : ROMExtractedAdversary ℕ ℕ ℕ (ℕ × ℕ × ℕ)
      (MultivariateQuadraticMap (ZMod 5) (Fin (1 + 1)) (Fin 1))
      (Option (Fin (1 + 1) → ZMod 5)) ((ℕ × ℕ × ℕ) × ℕ) (Fin 1 → ZMod 5))
    {q_R q_H : ℕ} (hA : ROMExtractedCallBounded A q_R q_H) :
    Game.succProbability
        (romExtractedConservationExperiment testCom
          (detScheme (idealUOVSystem (ZMod 5) 1 1 derive)) A) ≤
      (q_H + q_R + 1 : ℝ≥0) *
        (Experiment.succProbability
          (Signature.targetExperiment (idealUOVSystem (ZMod 5) 1 1 derive).toRawScheme
            (fun _ => ProbComp.uniform (Fin 1 → ZMod 5))
            (detInverter (idealUOVSystem (ZMod 5) 1 1 derive) (q_H + q_R)
              (romTargetForger testCom (detScheme (idealUOVSystem (ZMod 5) 1 1 derive)) A))) +
        Experiment.advantage
          (psExperimentReal (idealUOVSystem (ZMod 5) 1 1 derive)
            (detPSOneDistinguisher (idealUOVSystem (ZMod 5) 1 1 derive) (q_H + q_R)
              (romTargetForger testCom (detScheme (idealUOVSystem (ZMod 5) 1 1 derive)) A)))
          (psExperimentSim (idealUOVSystem (ZMod 5) 1 1 derive)
            (detPSOneDistinguisher (idealUOVSystem (ZMod 5) 1 1 derive) (q_H + q_R)
              (romTargetForger testCom (detScheme (idealUOVSystem (ZMod 5) 1 1 derive)) A)))) +
      Experiment.advantage
        (psExperimentReal (idealUOVSystem (ZMod 5) 1 1 derive)
          (detPSDistinguisher (idealUOVSystem (ZMod 5) 1 1 derive)
            (romTargetForger testCom (detScheme (idealUOVSystem (ZMod 5) 1 1 derive)) A)))
        (psExperimentSim (idealUOVSystem (ZMod 5) 1 1 derive)
          (detPSDistinguisher (idealUOVSystem (ZMod 5) 1 1 derive)
            (romTargetForger testCom (detScheme (idealUOVSystem (ZMod 5) 1 1 derive)) A))) +
      ((q_R + (q_H + q_R)).choose 2 : ℝ≥0) * (Fintype.card (Fin 1 → ZMod 5) : ℝ≥0)⁻¹ +
      Experiment.succProbability
        (testComScheme.bindingExperiment
          (detCommitmentBindingReduction testCom (idealUOVSystem (ZMod 5) 1 1 derive) A)) :=
  romExtractedConservationExperiment_detScheme_succProbability_le testCom testComScheme
    (fun _ _ _ _ _ _ => rfl) (idealUOVSystem (ZMod 5) 1 1 derive) A hA

/-- End-to-end extracted+ROM credit conservation instantiated on `idealUOVSystem` (salted `Tag`
with `Salt = Fin 64`) and keyless `testComScheme`. -/
example (derive : IdealKeyMaterial (ZMod 5) 1 1 → (Fin 1 → ZMod 5) →
      ProbComp (Option (Fin (1 + 1) → ZMod 5)))
    (A : ROMExtractedAdversary ℕ ℕ ℕ (ℕ × ℕ × ℕ)
      (MultivariateQuadraticMap (ZMod 5) (Fin (1 + 1)) (Fin 1))
      (Fin 64 × Option (Fin (1 + 1) → ZMod 5))
      (((ℕ × ℕ × ℕ) × ℕ) × Fin 64) (Fin 1 → ZMod 5))
    {q_R q_H : ℕ} (hA : ROMExtractedCallBounded A q_R q_H) :
    Game.succProbability
        (romExtractedConservationExperiment testCom
          (saltedScheme (idealUOVSystem (ZMod 5) 1 1 derive) (Fin 64)) A) ≤
      (q_H + q_R + 1 : ℝ≥0) *
        Experiment.succProbability
          (Signature.targetExperiment (idealUOVSystem (ZMod 5) 1 1 derive).toRawScheme
            (fun _ => ProbComp.uniform (Fin 1 → ZMod 5))
            (saltedInverter (idealUOVSystem (ZMod 5) 1 1 derive) (Fin 64) (q_H + q_R)
              (romTargetForger testCom
                (saltedScheme (idealUOVSystem (ZMod 5) 1 1 derive) (Fin 64)) A))) +
      Experiment.advantage
        (psExperimentReal (idealUOVSystem (ZMod 5) 1 1 derive)
          (saltedPSDistinguisher (idealUOVSystem (ZMod 5) 1 1 derive) (Fin 64)
            (romTargetForger testCom
              (saltedScheme (idealUOVSystem (ZMod 5) 1 1 derive) (Fin 64)) A)))
        (psExperimentSim (idealUOVSystem (ZMod 5) 1 1 derive)
          (saltedPSDistinguisher (idealUOVSystem (ZMod 5) 1 1 derive) (Fin 64)
            (romTargetForger testCom
              (saltedScheme (idealUOVSystem (ZMod 5) 1 1 derive) (Fin 64)) A))) +
      ((q_R * (q_H + q_R) + q_R.choose 2 : ℕ) : ℝ≥0) * (Fintype.card (Fin 64) : ℝ≥0)⁻¹ +
      Experiment.succProbability
        (testComScheme.bindingExperiment
          (saltedCommitmentBindingReduction (Salt := Fin 64) testCom
            (idealUOVSystem (ZMod 5) 1 1 derive) A)) :=
  romExtractedConservationExperiment_saltedScheme_succProbability_le testCom testComScheme
    (fun _ _ _ _ _ _ => rfl) (idealUOVSystem (ZMod 5) 1 1 derive) A hA

end CslibFrontierTests.Crypto.UOVHashAndSign
