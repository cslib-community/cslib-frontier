/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Crypto.Computational.TrapdoorFunction.RSA
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.UniformPoint

/-!
# Trapdoor function schemes and RSA key exchange: checked instances

Checks for `CslibFrontier/Crypto/Computational/TrapdoorFunction.lean` and
`CslibFrontier/Crypto/Computational/TrapdoorFunction/RSA.lean`:

* `keGuesserToInverter` and `inverterToKEGuesser` are definitionally mutually inverse,
  `encTranscript` has the framed `(pk, y)` bit layout, and `TrapdoorFunction.Inverter` at RSA types
  is definitionally `RSAInverter`.
* `not_oneWay_idScheme`: the identity scheme on `Bool` is `Correct` and fails
  `TrapdoorFunction.OneWay` (and `KeyExchange.AnonKESecure` for its key exchange).
* `oneWay_hidingScheme`: the hiding scheme on `Fin (2 ^ k)` (`PK = SK = ℕ`, `Y _ = Unit`) satisfies
  `TrapdoorFunction.OneWay` even though `Correct` fails; without `Correct`, `anonKEGame` and
  `owGame` disagree and `(keyExchange hidingScheme)` fails `AnonKESecure`.
* `RSAPublicKey` shows why `domain_nonempty` quantifies over secret keys rather than all public
  keys.
* Universal RSA checks: `rsaTrapdoor` evaluates and inverts via `rsaEval` and `rsaInvert`,
  evaluates in polynomial time on encoded transcripts, and for every fixed `desc : RSADesc`,
  `rsaKeyExchange (fun _ => PMF.pure desc)` fails `AnonKESecure` via
  `rsaKeyExchange_anonKESecure_iff_rsaOneWay` and the constant-zero PPT `RSAInverter`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.TrapdoorFunction

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped ENNReal NNReal Cslib.Probability.PMF

/-! ### Adversary conversions, transcript layout, and RSA inverter type -/

example {PK : Type} {X Y : PK → Type} (inverter : TrapdoorFunction.Inverter PK X Y) :
    TrapdoorFunction.keGuesserToInverter (TrapdoorFunction.inverterToKEGuesser inverter) =
      inverter :=
  rfl

example {PK : Type} {X Y : PK → Type}
    (adversary :
      KeyExchange.KeyGuesser (TrapdoorFunction.Transcript PK Y) (fun t => X t.publicKey)) :
    TrapdoorFunction.inverterToKEGuesser (TrapdoorFunction.keGuesserToInverter adversary) =
      adversary :=
  rfl

example {PK : Type} {Y : PK → Type} (encPK : PK ↪ List Bool)
    (encY : (pk : PK) → Y pk ↪ List Bool) (t : TrapdoorFunction.Transcript PK Y) :
    TrapdoorFunction.encTranscript encPK encY t =
      encPair encPK encBits (t.publicKey, encY t.publicKey t.ciphertext) :=
  rfl

example :
    TrapdoorFunction.Inverter RSAPublicKey (fun pk => Fin pk.N) (fun pk => Fin pk.N) =
      RSAInverter :=
  rfl

/-! ### Nonvacuity: the identity scheme fails `TrapdoorFunction.OneWay` -/

private noncomputable def idScheme :
    TrapdoorFunction Unit Unit (fun _ => Bool) (fun _ => Bool) where
  keyGen := PMF.pure ()
  publicKey := id
  eval _ x := x
  invert _ y := y
  domain_nonempty _ := ⟨false⟩

private theorem idScheme_correct : idScheme.Correct :=
  fun _ _ _ => rfl

private def idInverter : TrapdoorFunction.Inverter Unit (fun _ => Bool) (fun _ => Bool) :=
  fun _ _ y => pure y

private theorem isPPT_idInverter :
    idInverter.IsPPT encUnit (fun _ => encBool) (fun _ => encBool) := by
  have hcmp : ComputableInPolyTime
      (fun input : ℕ × TrapdoorFunction.Transcript Unit (fun _ => Bool) =>
        encBool input.2.ciphertext)
      (encPair encUnary (TrapdoorFunction.encTranscript encUnit fun _ => encBool)) encBits :=
    TrapdoorFunction.encTranscript_ciphertext_polyTime encUnit (fun _ => encBool) (.snd _ _)
  refine hcmp.isPPTOn.congr fun input => ?_
  simp only [idInverter, ProbComp.eval_map, ProbComp.eval_pure, PMF.pure_map]

private theorem owGame_idScheme (n : ℕ) :
    idScheme.owGame (idInverter n) = PMF.pure true := by
  simp only [TrapdoorFunction.owGame, idScheme, idInverter, ProbComp.eval_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind, eq_self, decide_true,
    PMF.bind_const]

theorem not_oneWay_idScheme :
    ¬ TrapdoorFunction.OneWay (fun _ => idScheme) encUnit (fun _ => encBool)
      (fun _ => encBool) := by
  intro h
  have hneg := h idInverter isPPT_idInverter
  simp only [owGame_idScheme, Game.succProbability, PMF.pure_apply, ite_true,
    ENNReal.toNNReal_one] at hneg
  exact not_negligible_const one_ne_zero hneg

example :
    ¬ (TrapdoorFunction.keyExchange fun _ => idScheme).AnonKESecure
      (TrapdoorFunction.encTranscript encUnit fun _ => encBool) (fun _ => encBool) :=
  fun h => not_oneWay_idScheme
    ((TrapdoorFunction.keyExchange_anonKESecure_iff_oneWay (fun _ => idScheme_correct)
      encUnit (fun _ => encBool) (fun _ => encBool)).mp h)

/-! ### Satisfying instance and necessity of `Correct`: the hiding scheme -/

private noncomputable def hidingScheme (n : ℕ) :
    TrapdoorFunction ℕ ℕ (fun k => Fin (2 ^ k)) (fun _ => Unit) where
  keyGen := PMF.pure n
  publicKey := id
  eval _ _ := ()
  invert k _ := ⟨0, Nat.two_pow_pos k⟩
  domain_nonempty k := ⟨⟨0, Nat.two_pow_pos k⟩⟩

private theorem succProbability_owGame_hidingScheme (n : ℕ)
    (step : (k : ℕ) → Unit → ProbComp (Fin (2 ^ k))) :
    Game.succProbability ((hidingScheme n).owGame step) = ((2 : ℝ≥0) ^ n)⁻¹ := by
  have h : (hidingScheme n).owGame step =
      (ProbComp.eval (step n ())).bind fun x' =>
        (PMF.uniformOfFintype (Fin (2 ^ n))).bind fun x => PMF.pure (decide (x' = x)) := by
    simp only [TrapdoorFunction.owGame, hidingScheme, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.pure_bind]
    exact PMF.bind_comm _ _ _
  rw [Game.succProbability, h, PMF.bind_apply]
  simp only [PMF.uniformOfFintype_bind_decide_eq_apply_true, ENNReal.tsum_mul_right, PMF.tsum_coe,
    one_mul, Fintype.card_fin]
  rw [show ((2 ^ n : ℕ) : ℝ≥0∞) = (((2 : ℝ≥0) ^ n : ℝ≥0) : ℝ≥0∞) by push_cast; rfl,
    ← ENNReal.coe_inv (pow_ne_zero n two_ne_zero), ENNReal.toNNReal_coe]

theorem oneWay_hidingScheme :
    TrapdoorFunction.OneWay hidingScheme encNat (fun _ => Fin.valEmbedding.trans encNat)
      (fun _ => encUnit) := by
  intro inverter _
  simp only [succProbability_owGame_hidingScheme]
  exact negligible_inv_two_pow

example : ¬ (hidingScheme 1).Correct := by
  intro h
  have h1 := h 1 (by simp [hidingScheme]) ⟨1, by decide⟩
  exact absurd (congrArg Fin.val h1) (by decide)

private def zeroHidingGuesser :
    KeyExchange.KeyGuesser (TrapdoorFunction.Transcript ℕ fun _ => Unit)
      (fun t => Fin (2 ^ t.publicKey)) :=
  fun _ t => pure ⟨0, Nat.two_pow_pos t.publicKey⟩

private theorem anonKEGame_hidingScheme_zeroHidingGuesser (n : ℕ) :
    (TrapdoorFunction.keyExchange hidingScheme).anonKEGame zeroHidingGuesser n =
      PMF.pure true := by
  simp only [KeyExchange.anonKEGame, TrapdoorFunction.keyExchange, Game.withSetup,
    TrapdoorFunction.keyExchangeExecution, hidingScheme, zeroHidingGuesser, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
    PMF.pure_bind, eq_self, decide_true, PMF.bind_const]

/-- Without `Correct`, `anonKEGame` and `owGame` disagree (`1 ≠ 1 / 2` at `n = 1`). -/
example :
    (TrapdoorFunction.keyExchange hidingScheme).anonKEGame zeroHidingGuesser 1 ≠
      (hidingScheme 1).owGame (TrapdoorFunction.keGuesserToInverter zeroHidingGuesser 1) := by
  intro heq
  have hprob := congrArg Game.succProbability heq
  rw [anonKEGame_hidingScheme_zeroHidingGuesser, succProbability_owGame_hidingScheme] at hprob
  norm_num [Game.succProbability] at hprob

/-- Without `Correct`, `OneWay` does not imply `AnonKESecure` for `keyExchange`: `zeroHidingGuesser`
guesses Alice's constant-`0` output key with probability `1`. -/
example :
    ¬ (TrapdoorFunction.keyExchange hidingScheme).AnonKESecure
      (TrapdoorFunction.encTranscript encNat fun _ => encUnit)
      (fun _ => Fin.valEmbedding.trans encNat) := by
  intro h
  have hPPT : zeroHidingGuesser.IsPPT
      (TrapdoorFunction.encTranscript encNat fun _ => encUnit)
      (fun _ => Fin.valEmbedding.trans encNat) := by
    refine (ComputableInPolyTime.const (encNat 0)).isPPTOn.congr fun input => ?_
    simp only [zeroHidingGuesser, ProbComp.eval_map, ProbComp.eval_pure, PMF.pure_map]
    rfl
  have hneg := h zeroHidingGuesser hPPT
  simp only [anonKEGame_hidingScheme_zeroHidingGuesser, Game.succProbability, PMF.pure_apply,
    ite_true, ENNReal.toNNReal_one] at hneg
  exact not_negligible_const one_ne_zero hneg

/-! ### Why `domain_nonempty` quantifies over secret keys -/

example : ¬ ∀ pk : RSAPublicKey, Nonempty (Fin pk.N) :=
  fun h => (h ⟨0, 3⟩).elim Fin.elim0

/-! ### RSA trapdoor permutation and universal fixed-key nonvacuity -/

private def zeroRSAInverter : RSAInverter :=
  fun _ _ y => pure ⟨0, y.pos⟩

private theorem isPPT_zeroRSAInverter : zeroRSAInverter.IsPPT := by
  refine (ComputableInPolyTime.const 0).isPPTOn.congr fun x => ?_
  simp only [zeroRSAInverter, ProbComp.eval_map, ProbComp.eval_pure, PMF.pure_map]

private theorem succProbability_rsaInversionGame_zeroRSAInverter (desc : RSADesc) (n : ℕ) :
    Game.succProbability (rsaInversionGame (fun _ => PMF.pure desc) zeroRSAInverter n) =
      (desc.modulus : ℝ≥0)⁻¹ := by
  rw [Game.succProbability, rsaInversionGame_eq]
  simp only [zeroRSAInverter, ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.pure_bind]
  change ENNReal.toNNReal (((PMF.uniformOfFintype (Fin desc.modulus)).bind fun x =>
      PMF.pure (decide ((⟨0, desc.modulus_pos⟩ : Fin desc.modulus) = x))) true) =
      (desc.modulus : ℝ≥0)⁻¹
  rw [PMF.uniformOfFintype_bind_decide_eq_apply_true, Fintype.card_fin, ENNReal.toNNReal_inv,
    ENNReal.toNNReal_natCast]

theorem not_anonKESecure_rsaKeyExchange_const (desc : RSADesc) :
    ¬ (rsaKeyExchange fun _ => PMF.pure desc).AnonKESecure
      (TrapdoorFunction.encTranscript encRSAPublicKey RSAPublicKey.encResidue)
      (fun t => t.publicKey.encResidue) := by
  intro h
  have hrsa := (rsaKeyExchange_anonKESecure_iff_rsaOneWay (fun _ => PMF.pure desc)).mp h
  have hneg := hrsa zeroRSAInverter isPPT_zeroRSAInverter
  simp only [succProbability_rsaInversionGame_zeroRSAInverter] at hneg
  exact not_negligible_const (inv_ne_zero (Nat.cast_ne_zero.mpr desc.modulus_pos.ne')) hneg

example (gen : PMF RSADesc) (pk : RSAPublicKey) (x : Fin pk.N) :
    ((rsaTrapdoor gen).eval pk x : ℕ) = rsaEval pk.N pk.e x :=
  rfl

example (gen : PMF RSADesc) (desc : RSADesc) (y : Fin desc.publicKey.N) :
    ((rsaTrapdoor gen).invert desc y : ℕ) = rsaInvert desc.modulus desc.d y :=
  rfl

example (gen : PMF RSADesc) :
    ComputableInPolyTime
      (fun t : TrapdoorFunction.Transcript RSAPublicKey (fun pk => Fin pk.N) =>
        ((rsaTrapdoor gen).eval t.publicKey t.ciphertext : ℕ))
      (TrapdoorFunction.encTranscript encRSAPublicKey RSAPublicKey.encResidue) encNat := by
  open scoped TrapdoorFunction in
  exact computableInPolyTime_rsaEval (by fun_prop) (by fun_prop)
    ((TrapdoorFunction.encTranscript_ciphertext_polyTime encRSAPublicKey
      RSAPublicKey.encResidue (by fun_prop)).of_enc_eq fun _ => rfl)
    fun t => t.ciphertext.pos

end CslibFrontierTests.Crypto.TrapdoorFunction
