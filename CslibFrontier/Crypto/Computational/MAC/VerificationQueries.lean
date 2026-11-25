/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Crypto.Computational.MAC
public import CslibFrontier.Crypto.Game.Forgery.VerificationQueries
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.UniformNat.ModIndex
import CslibFrontier.Crypto.Computational.PseudorandomFunction.Finite
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime.Init

/-!
# MAC security with verification queries

This module formalizes [BonehShoup2023], Section 6.2 (Attack Game 6.2 and Theorem 6.1,
pp. 220–223) and Section 6.14 (Exercise 6.2, p. 246), in the computational word-level `MACScheme`
model against uniform strict `IsOraclePPT` adversaries.

In Attack Game 6.2 (`MACScheme.sufCmaVqGame`), an adversary `VqForger` interacts over a
`Bool`-tagged word channel:
* `(false, msg)` is a signing query: if `msg.length == M.msgLen n`, the challenger runs `M.sign sk
  msg`, prepends `(msg, tag)` to its query log, and returns `tag`; otherwise it returns `[]` without
  signing or logging (matching `MACScheme.signingPairOracle`).
* `(true, raw)` is a verification query, decoding `(msg, tag) := (unframe raw, dropFrame raw)`: the
  challenger evaluates `ok := (msg.length == M.msgLen n) && M.verify sk msg tag`, latches `won` when
  `ok && !log.contains (msg, tag)` holds, and replies `[ok]`. As in
  `CslibFrontier.Crypto.Game.Forgery.VerificationQueries`, replaying a previously signed pair
  `(msg, tag) ∈ log` returns `[true]` (by `M.verify_sign`) without counting as a fresh forgery, and
  wrong-length messages return `[false]` without latching `won`.

## Main definitions

* `Cslib.Crypto.VqForger`, `Cslib.Crypto.VqForger.toTyped`,
  `Cslib.Crypto.IsWordSigningQueryBounded`, `Cslib.Crypto.IsWordVerificationQueryBounded`:
  word-level Attack Game 6.2 adversaries, typed view adapter, and pathwise signing/verification
  query budgets.
* `Cslib.Crypto.encVqState`: multi-tape encoding of `VqOracleState (List Bool) (List Bool)` as the
  framed pair `(log, won)` under `encPair (encList (encPair encBits encBits)) encBool`.
* `Cslib.Crypto.MACScheme.sufCmaVqOracle`, `Cslib.Crypto.MACScheme.sufCmaVqGame`,
  `Cslib.Crypto.MACScheme.SUFCMAVq`: the Attack Game 6.2 challenger, experiment, and security
  predicate on `MACScheme`.
* `Cslib.Crypto.sufToVqForger`: embeds a `Forger` into `VqForger` using one verification query.
* `Cslib.Crypto.MACScheme.vqToSufForger`: the uniform guessing reduction of Theorem 6.1, sampling
  its planted verification-query index via `ProbComp.sampleModIndex (width n) (Qv n)` and truncating
  external signing replies to `tagBound n` bits.
* `Cslib.Crypto.vqMacToPrfDistinguisher`: the direct PRF distinguisher of Exercise 6.2 for `prfMAC`.

## Main results

* `Cslib.Crypto.MACScheme.sufCmaVqGame_eq_vqForgeExperiment`: `sufCmaVqGame` has the exact law of
  `vqForgeExperiment` with `PK = Unit` and `(Signer.ofSign M.sign).restrict (·.length == M.msgLen
  n)`.
* `Cslib.Crypto.isOraclePPT_sufToVqForger`, `Cslib.Crypto.MACScheme.SUFCMAVq.sufCma`: Attack Game
  6.2 security implies `SUFCMA`.
* `Cslib.Crypto.MACScheme.isOraclePPT_vqToSufForger`,
  `Cslib.Crypto.MACScheme.isQueryBounded_vqToSufForger`,
  `Cslib.Crypto.MACScheme.succProbability_sufCmaVqGame_le_mul_add`,
  `Cslib.Crypto.MACScheme.succProbability_sufCmaVqGame_le_mul`,
  `Cslib.Crypto.MACScheme.SUFCMA.sufCmaVq`,
  `Cslib.Crypto.MACScheme.sufCmaVq_iff_sufCma`: Theorem 6.1 (efficiency certificate, signing-query
  bound, concrete fair-coin and exact dyadic loss bounds, and `M.SUFCMAVq ↔ M.SUFCMA`).
* `Cslib.Crypto.isOraclePPT_vqMacToPrfDistinguisher`,
  `Cslib.Crypto.isQueryBounded_vqMacToPrfDistinguisher`,
  `Cslib.Crypto.succProbability_sufCmaVqGame_prfMAC_le`,
  `Cslib.Crypto.PseudorandomFunction.sufCmaVq_prfMAC`: Exercise 6.2 (`prfMAC` security with
  verification queries with concrete bound `prfAdv + Q_v / 2 ^ n`, avoiding a `Q_v` factor on the
  PRF advantage).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 6.2 (Attack Game 6.2 and Theorem 6.1, pp. 220–223) and Section 6.14 (Exercise 6.2,
  p. 246).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

/-! ### Word-level Attack Game 6.2 adversaries and query budgets -/

/-- Word-level adversary for Attack Game 6.2: given unary security parameter `n` and auxiliary
input, interacts with a `Bool`-tagged word channel (`false` for signing, `true` for verification)
and returns `Unit`. -/
abbrev VqForger : Type := ℕ → List Bool → WordOracleComp Bool Unit

/-- Pathwise budget of at most `Q_s` signing queries (`(false, msg)`) on a `Bool`-tagged word
channel. -/
abbrev IsWordSigningQueryBounded {α : Type} (program : WordOracleComp Bool α) (Q_s : ℕ) : Prop :=
  OracleComp.IsCostBounded
    (Sum.elim (fun _ => 0) (fun req => if req.1 then 0 else 1)) program Q_s

/-- Pathwise budget of at most `Q_v` verification queries (`(true, raw)`) on a `Bool`-tagged word
channel. -/
abbrev IsWordVerificationQueryBounded {α : Type} (program : WordOracleComp Bool α)
    (Q_v : ℕ) : Prop :=
  OracleComp.IsCostBounded
    (Sum.elim (fun _ => 0) (fun req => if req.1 then 1 else 0)) program Q_v

/-- One word-level signing query `(false, msg)` costs `1` signing query. -/
theorem IsWordSigningQueryBounded.query_sign (msg : List Bool) :
    IsWordSigningQueryBounded
      (ProbOracleComp.query (spec := fun _ : Bool × List Bool => List Bool) (false, msg)) 1 :=
  ProbOracleComp.isCostBounded_query _ (false, msg)

/-- One word-level verification query `(true, raw)` costs `0` signing queries. -/
theorem IsWordSigningQueryBounded.query_verify (raw : List Bool) :
    IsWordSigningQueryBounded
      (ProbOracleComp.query (spec := fun _ : Bool × List Bool => List Bool) (true, raw)) 0 :=
  ProbOracleComp.isCostBounded_query _ (true, raw)

/-- One word-level signing query `(false, msg)` costs `0` verification queries. -/
theorem IsWordVerificationQueryBounded.query_sign (msg : List Bool) :
    IsWordVerificationQueryBounded
      (ProbOracleComp.query (spec := fun _ : Bool × List Bool => List Bool) (false, msg)) 0 :=
  ProbOracleComp.isCostBounded_query _ (false, msg)

/-- One word-level verification query `(true, raw)` costs `1` verification query. -/
theorem IsWordVerificationQueryBounded.query_verify (raw : List Bool) :
    IsWordVerificationQueryBounded
      (ProbOracleComp.query (spec := fun _ : Bool × List Bool => List Bool) (true, raw)) 1 :=
  ProbOracleComp.isCostBounded_query _ (true, raw)

/-- A total external query budget bounds the number of signing queries. -/
theorem IsWordSigningQueryBounded.of_isQueryBounded {α : Type} {program : WordOracleComp Bool α}
    {Q : ℕ} (h : program.IsQueryBounded Q) : IsWordSigningQueryBounded program Q :=
  h.of_le fun q => by cases q with
    | inl _ => simp
    | inr req =>
      rcases req with ⟨b, _⟩
      cases b <;> simp

/-- A total external query budget bounds the number of verification queries. -/
theorem IsWordVerificationQueryBounded.of_isQueryBounded {α : Type}
    {program : WordOracleComp Bool α} {Q : ℕ} (h : program.IsQueryBounded Q) :
    IsWordVerificationQueryBounded program Q :=
  h.of_le fun q => by cases q with
    | inl _ => simp
    | inr req =>
      rcases req with ⟨b, _⟩
      cases b <;> simp

/-- Separate word signing and verification query budgets yield a total external query budget of
`Q_s + Q_v`. -/
theorem IsQueryBounded.of_word_signing_and_verification {α : Type}
    {program : WordOracleComp Bool α} {Q_s Q_v : ℕ}
    (hs : IsWordSigningQueryBounded program Q_s)
    (hv : IsWordVerificationQueryBounded program Q_v) :
    program.IsQueryBounded (Q_s + Q_v) :=
  (hs.add hv).of_le fun q => by cases q with
    | inl _ => simp
    | inr req =>
      rcases req with ⟨b, _⟩
      cases b <;> simp

/-- Adapt a word-level `VqForger` at `(n, aux)` into a typed Attack Game 6.2 program over
`forgeVqSpec (List Bool) (List Bool)`: `(false, msg)` becomes `Sum.inl msg`, and `(true, raw)`
becomes `Sum.inr (unframe raw, dropFrame raw)` with its `Bool` verdict encoded as `[ok]`. -/
@[expose] def VqForger.toTyped (adversary : VqForger) (n : ℕ) (aux : List Bool) :
    ProbOracleComp (forgeVqSpec (List Bool) (List Bool)) Unit :=
  OracleComp.interpret
    (OracleComp.sumHandler
      (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
      (fun req : Bool × List Bool =>
        if req.1 then
          (fun ok : Bool => [ok]) <$>
            ProbOracleComp.query (spec := forgeVqSpec (List Bool) (List Bool))
              (Sum.inr (unframe req.2, dropFrame req.2))
        else
          ProbOracleComp.query (spec := forgeVqSpec (List Bool) (List Bool)) (Sum.inl req.2)))
    (adversary n aux)

/-- `VqForger.toTyped` preserves signing query budgets. -/
theorem VqForger.isSigningQueryBounded_toTyped {adversary : VqForger} {n : ℕ} {aux : List Bool}
    {Q_s : ℕ} (h : IsWordSigningQueryBounded (adversary n aux) Q_s) :
    IsSigningQueryBounded (adversary.toTyped n aux) Q_s := by
  refine h.interpret fun q => ?_
  cases q with
  | inl k => exact ProbOracleComp.isCostBounded_sample _ (ProbComp.unifFin k)
  | inr req =>
    rcases req with ⟨b, raw⟩
    cases b
    · exact IsSigningQueryBounded.query_sign raw
    · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
        (IsSigningQueryBounded.query_verify (unframe raw, dropFrame raw))

/-- `VqForger.toTyped` preserves verification query budgets. -/
theorem VqForger.isVerificationQueryBounded_toTyped {adversary : VqForger} {n : ℕ}
    {aux : List Bool} {Q_v : ℕ} (h : IsWordVerificationQueryBounded (adversary n aux) Q_v) :
    IsVerificationQueryBounded (adversary.toTyped n aux) Q_v := by
  refine h.interpret fun q => ?_
  cases q with
  | inl k => exact ProbOracleComp.isCostBounded_sample _ (ProbComp.unifFin k)
  | inr req =>
    rcases req with ⟨b, raw⟩
    cases b
    · exact IsVerificationQueryBounded.query_sign raw
    · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
        (IsVerificationQueryBounded.query_verify (unframe raw, dropFrame raw))

/-- Multi-tape encoding of `VqOracleState (List Bool) (List Bool)` as the framed pair
`encPair (encList (encPair encBits encBits)) encBool` of the chronological `(msg, tag)` signing
`log` and the `won` latch. -/
enc_structure encVqState : VqOracleState (List Bool) (List Bool) where
  log : (encList (encPair encBits encBits)),
  won : encBool

private enc_structure encMsgTagPlanted : ProbOracleComp.PlantedState (List Bool × List Bool) where
  rem : encUnary,
  hasCaptured : encBool,
  candidate : (encPair encBits encBits)

private enc_structure encVqPlantedState :
    ProbOracleComp.PlantedOracleState (List Bool × List Bool) (List (List Bool × List Bool)) where
  planted : encMsgTagPlanted,
  oracleState : (encList (encPair encBits encBits))

/-! ### Attack Game 6.2 on `MACScheme` (`sufCmaVqGame`, `SUFCMAVq`) -/

namespace MACScheme

/-- Stateful Attack Game 6.2 challenger oracle for `M` at security parameter `n` under secret key
`sk` ([BonehShoup2023], Section 6.2, p. 221):
* `(false, msg)`: if `msg.length == M.msgLen n`, signs `msg` under `sk`, prepends `(msg, tag)` to
  `st.log`, and returns `tag`; otherwise returns `[]` without signing or logging.
* `(true, raw)`: decodes `(msg, tag) := (unframe raw, dropFrame raw)`, checks
  `ok := (msg.length == M.msgLen n) && M.verify sk msg tag`, latches `st.won` when
  `ok && !st.log.contains (msg, tag)` holds, and replies `[ok]`. -/
@[expose] noncomputable def sufCmaVqOracle (M : MACScheme) (n : ℕ) (sk : List Bool)
    (request : Bool × List Bool) :
    StateT (VqOracleState (List Bool) (List Bool)) ProbComp (List Bool) :=
  fun st =>
    if request.1 then
      let msg := unframe request.2
      let tag := dropFrame request.2
      let ok := (msg.length == M.msgLen n) && M.verify sk msg tag
      let fresh := !st.log.contains (msg, tag)
      pure ([ok], ⟨st.log, st.won || (ok && fresh)⟩)
    else
      if request.2.length == M.msgLen n then do
        let tag ← M.sign sk request.2
        return (tag, ⟨(request.2, tag) :: st.log, st.won⟩)
      else
        return ([], st)

/-- The strong MAC experiment with verification queries ([BonehShoup2023], Section 6.2, Attack Game
6.2, p. 221): draw `sk ← M.keyGen n`, run `adversary n []` against `M.sufCmaVqOracle n sk` from
`⟨[], false⟩`, and accept iff `won` latched `true` on some fresh valid verification query. -/
@[expose] noncomputable def sufCmaVqGame (M : MACScheme) (adversary : VqForger) (n : ℕ) :
    ProbComp Bool := do
  let sk ← M.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (M.sufCmaVqOracle n sk)) (adversary n [])).run ⟨[], false⟩
  return out.2.won

/-- Running an oracle-PPT `VqForger` against `sufCmaVqOracle` is uniformly strict PPT in the unary
security parameter and secret key. -/
@[program_certificate]
theorem isPPTOn_run_sufCmaVqOracle (M : MACScheme) {adversary : VqForger}
    (hadversary : IsOraclePPT (encFinEnum Unit) adversary) :
    IsPPTOn (encPair encUnary encBits)
      (encPair (encFinEnum Unit) encVqState)
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (M.sufCmaVqOracle caller.1 caller.2)) (adversary caller.1 [])).run ⟨[], false⟩) := by
  obtain ⟨c, d, hlen⟩ := M.sign_ppt.length_le
  have hhandler : IsPPTOn
      (encPair (encPair encUnary encBits)
        (encPair (encPair encBool encBits) encVqState))
      (encPair encBits encVqState)
      (fun pair : (ℕ × List Bool) × ((Bool × List Bool) × VqOracleState (List Bool) (List Bool)) =>
        M.sufCmaVqOracle pair.1.1 pair.1.2 pair.2.1 pair.2.2) := by
    unfold sufCmaVqOracle
    exact IsPPTOn.ite (by fun_prop)
      (ComputableInPolyTime.isPPTOn (by
        simp only [List.contains_eq_mem]
        fun_prop))
      (IsPPTOn.ite (by fun_prop)
        ((M.isPPTOn_sign_comp (by fun_prop) (by fun_prop)).bind_with
          (ComputableInPolyTime.isPPTOn (by fun_prop)))
        (ComputableInPolyTime.isPPTOn (by fun_prop)))
  apply hadversary.run_interpret_preprocess
    (operationEncoding := encBool)
    (stateEncoding := encVqState)
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (initial := fun _ => (⟨[], false⟩ : VqOracleState (List Bool) (List Bool)))
    (resources := fun caller query =>
      4 * (c * (2 * caller.2.length + query.length + 2) ^ d) + 8 * query.length + 12)
    (by fun_prop) hhandler
    (by fun_prop)
    (fun _ _ => True) (fun _ => trivial) (by fun_prop)
  intro caller request st _ result hresult
  dsimp only [sufCmaVqOracle] at hresult
  split_ifs at hresult
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
    subst result
    refine ⟨trivial, ?_, ?_⟩
    · simp
    · enc_len [encVqState_apply, encVqStateFields]
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hresult
    obtain ⟨tag, htag, rfl⟩ := hresult
    have htagLen := hlen (caller.2, request.2) tag htag
    simp only [encBits_apply, length_encPair] at htagLen
    have htag_le : tag.length ≤ c * (2 * caller.2.length + request.2.length + 2) ^ d :=
      htagLen.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d))
    refine ⟨trivial, by dsimp only; omega, ?_⟩
    enc_len [encVqState_apply, encVqStateFields]
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
    subst result
    exact ⟨trivial, by simp, by lia⟩

/-- Run the complete MAC Attack Game 6.2 experiment on its unary security parameter for any
oracle-PPT adversary. -/
@[program_certificate]
theorem isPPTOn_sufCmaVqGame (M : MACScheme) {adversary : VqForger}
    (hadversary : IsOraclePPT (encFinEnum Unit) adversary) :
    IsPPTOn encUnary encBool (M.sufCmaVqGame adversary) :=
  M.keyGen_ppt.bind_with ((M.isPPTOn_run_sufCmaVqOracle hadversary).bind_with
    (ComputableInPolyTime.isPPTOn (by fun_prop)))

/-- The MAC Attack Game 6.2 experiment is uniformly strict PPT, independently of unused auxiliary
input. -/
@[program_certificate]
theorem isPPT_sufCmaVqGame (M : MACScheme) {adversary : VqForger}
    (hadversary : IsOraclePPT (encFinEnum Unit) adversary) :
    IsPPT encBool (fun n _ => M.sufCmaVqGame adversary n) :=
  ((M.isPPTOn_sufCmaVqGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Strong MAC unforgeability under adaptive chosen-message and verification-query attack
(`SUFCMAVq`) against uniform strict oracle-PPT adversaries ([BonehShoup2023], Section 6.2, Attack
Game 6.2, p. 221), on `M.msgLen n`-bit messages:
* signing queries `(false, msg)` with `msg.length ≠ M.msgLen n` return `[]` without signing or
  recording `msg` in `log`;
* verification queries `(true, raw)` decode `(msg, tag) := (unframe raw, dropFrame raw)`, return
  `[false]` without latching `won` when `msg.length ≠ M.msgLen n`, and return `[true]` (by
  `M.verify_sign`) without latching `won` when `(msg, tag) ∈ log`. -/
def SUFCMAVq (M : MACScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (M.sufCmaVqGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encFinEnum Unit))

/-- `SUFCMAVq` security gives negligible `sufCmaVqGame` winning probability for every oracle-PPT
`VqForger`. -/
theorem SUFCMAVq.negligible {M : MACScheme} (h : M.SUFCMAVq)
    (adversary : VqForger) (hadversary : IsOraclePPT (encFinEnum Unit) adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (M.sufCmaVqGame adversary n))) :=
  Game.Indistinguishable.negligible_succProbability h adversary hadversary

/-- Establish `SUFCMAVq` security by bounding every oracle-PPT `VqForger`'s winning probability. -/
theorem SUFCMAVq.of_negligible {M : MACScheme}
    (h : ∀ adversary, IsOraclePPT (encFinEnum Unit) adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (M.sufCmaVqGame adversary n)))) :
    M.SUFCMAVq :=
  Game.Indistinguishable.of_negligible_succProbability h

/-- At each security parameter `n`, `M.sufCmaVqGame adversary n` has the exact Boolean law of
`vqForgeExperiment` with `PK = Unit`, policy `(Signer.ofSign M.sign).restrict (·.length == M.msgLen
n)`, and verifier `fun () sk msg tag => (msg.length == M.msgLen n) && M.verify sk msg tag`. -/
theorem sufCmaVqGame_eq_vqForgeExperiment (M : MACScheme) (adversary : VqForger) (n : ℕ) :
    ProbComp.eval (M.sufCmaVqGame adversary n) =
      ProbComp.eval
        (vqForgeExperiment (((), ·) <$> M.keyGen n)
          ((Signer.ofSign M.sign).restrict (·.length == M.msgLen n))
          (fun () sk msg tag => (msg.length == M.msgLen n) && M.verify sk msg tag)
          (fun () => adversary.toTyped n [])) := by
  simp only [sufCmaVqGame, vqForgeExperiment, pmf_norm]
  refine PMF.bind_congr_on_support _ _ _ fun sk _ => ?_
  rw [ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.eval_runState]
  dsimp only [VqForger.toTyped]
  rw [ProbOracleComp.runWith_interpret_sumHandler]
  let represent : VqOracleState (List Bool) (List Bool) → VqOracleState (List Bool) (List Bool) :=
    fun st => ⟨st.log.reverse, st.won⟩
  have hsim := ProbOracleComp.runWith_map_state
    (oracle := fun req : Bool × List Bool =>
      ProbOracleComp.runWith
        (fun q st => ProbComp.eval
          (vqOracle ((Signer.ofSign M.sign).restrict (·.length == M.msgLen n))
            (fun () sk' msg tag => (msg.length == M.msgLen n) && M.verify sk' msg tag) () sk q st))
        (if req.1 then
          (fun ok : Bool => [ok]) <$>
            ProbOracleComp.query (spec := forgeVqSpec (List Bool) (List Bool))
              (Sum.inr (unframe req.2, dropFrame req.2))
        else
          ProbOracleComp.query (spec := forgeVqSpec (List Bool) (List Bool)) (Sum.inl req.2)))
    (oracle' := fun req st => ProbComp.eval (M.sufCmaVqOracle n sk req st))
    (represent := represent)
    (step := fun ⟨b, raw⟩ st => by
      cases b
      · dsimp only [sufCmaVqOracle, vqOracle, represent, StateT.run]
        simp only [Bool.false_eq_true, ↓reduceIte, ProbOracleComp.runWith_query, Signer.restrict,
          Signer.ofSign]
        by_cases hlen : raw.length = M.msgLen n
        · simp [hlen, ProbComp.eval_map, PMF.map_comp, Function.comp_def]
        · simp [beq_eq_false_iff_ne.mpr hlen, show (default : List Bool) = [] from rfl]
      · dsimp only [sufCmaVqOracle, vqOracle, represent, StateT.run]
        simp [ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, freshPair])
    (adversary n []) ⟨[], false⟩
  change ((ProbOracleComp.runWith _ (adversary n []) (represent ⟨[], false⟩)).bind _) = _
  rw [← hsim, PMF.bind_map]
  rfl

/-- An adversary making `0` verification queries at security parameter `n` wins `sufCmaVqGame` with
probability `0`. -/
theorem succProbability_sufCmaVqGame_zero (M : MACScheme) {adversary : VqForger} {n : ℕ}
    (hQv : IsWordVerificationQueryBounded (adversary n []) 0) :
    Game.succProbability (ProbComp.eval (M.sufCmaVqGame adversary n)) = 0 := by
  rw [M.sufCmaVqGame_eq_vqForgeExperiment]
  exact succProbability_vqForgeExperiment_zero _ _ _ fun () =>
    adversary.isVerificationQueryBounded_toTyped hQv

end MACScheme

/-! ### Direction 1: `SUFCMAVq` implies `SUFCMA` (`sufToVqForger`) -/

private def sufToVqStep (tagCap : ℕ) (request : Unit × List Bool) :
    StateT Unit (WordOracleComp Bool) (List Bool) :=
  fun u => (·, u) <$> (List.take tagCap <$> ProbOracleComp.query (false, request.2))

/-- Embed a standard Attack Game 6.1 `Forger` into Attack Game 6.2 (`VqForger`): forward every
signing query `((), msg)` to `(false, msg)` (truncating the reply to `tagBound n` bits) and submit
the final candidate `(msg, tag)` as a single verification query `(true, encPair encBits encBits
(msg, tag))`. -/
def sufToVqForger (tagBound : ℕ → ℕ) (adversary : Forger) : VqForger :=
  fun n aux => do
    let out ← (OracleComp.interpret
      (OracleComp.sumHandler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (sufToVqStep (tagBound n)))
      (adversary n aux)).run ()
    let _ ← List.take 0 <$> ProbOracleComp.query (true, encPair encBits encBits out.1)
    return ()

/-- `sufToVqForger tagBound adversary` is uniformly strict oracle-PPT whenever `tagBound` is
polynomial-time computable in unary and `adversary` is oracle-PPT. -/
theorem isOraclePPT_sufToVqForger {tagBound : ℕ → ℕ}
    (htagBound : ComputableInPolyTime tagBound encUnary encUnary)
    {adversary : Forger} (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPT (encFinEnum Unit) (sufToVqForger tagBound adversary) := by
  let ECaller := encPair encUnary encBits
  have hhandler : IsOraclePPTOn
      (encPair ECaller (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit)))
      (encPair encBits (encFinEnum Unit))
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × Unit) =>
        sufToVqStep (tagBound pair.1.1) pair.2.1 pair.2.2) := by
    ppt [sufToVqStep]
  have hrun : IsOraclePPTOn ECaller
      (encPair (encPair encBits encBits) (encFinEnum Unit))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (sufToVqStep (tagBound caller.1)))
          (adversary caller.1 caller.2)).run ()) := by
    apply hadversary.run_interpret_preprocess_open
      (operationEncoding := encFinEnum Unit)
      (stateEncoding := encFinEnum Unit)
      (prepare := id)
      (initial := fun _ => ())
      (resources := fun caller _ => tagBound caller.1)
      (by polytime) hhandler (ComputableInPolyTime.const ())
      (fun _ _ => True) (fun _ => trivial) (by polytime)
    intro caller request _ _ result hresult
    unfold sufToVqStep at hresult
    obtain ⟨tag, htag, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
    obtain ⟨rawTag, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp htag
    exact ⟨trivial, List.length_take_le _ _, by simp⟩
  have hcheck : IsOraclePPTOn
      (encPair (encPair encBits encBits) (encFinEnum Unit))
      (encFinEnum Unit)
      (fun out : (List Bool × List Bool) × Unit => do
        let _ ← List.take 0 <$> ProbOracleComp.query (true, encPair encBits encBits out.1)
        pure ()) := by
    ppt
  unfold sufToVqForger
  exact (hrun.bind hcheck).isOraclePPT

namespace MACScheme

/-- When `tagBound n` upper-bounds honest tag lengths on `M.msgLen n`-bit messages, running
`sufToVqForger tagBound adversary` in `M.sufCmaVqGame` has the exact Boolean law of
`M.sufCmaGame adversary n` (and of `vqForgeExperiment ... (forgerToVq ...)`). -/
theorem eval_sufCmaVqGame_sufToVqForger (M : MACScheme) {tagBound : ℕ → ℕ} {n : ℕ}
    (htagBound : ∀ sk ∈ (ProbComp.eval (M.keyGen n)).support,
      ∀ msg, msg.length = M.msgLen n →
      ∀ tag ∈ (ProbComp.eval (M.sign sk msg)).support, tag.length ≤ tagBound n)
    (adversary : Forger) :
    ProbComp.eval (M.sufCmaVqGame (sufToVqForger tagBound adversary) n) =
      ProbComp.eval (M.sufCmaGame adversary n) := by
  simp only [sufCmaVqGame, sufCmaGame, sufToVqForger, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun sk hsk => ?_
  rw [ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.eval_run_interpret_eq_runWith]
  rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_run_interpret, PMF.bind_map]
  have hsim := ProbOracleComp.runWith_map_state
    (oracle := fun req s => ProbComp.eval (M.signingPairOracle n sk req s))
    (oracle' := fun req state =>
      (ProbOracleComp.runWith (fun q st => ProbComp.eval (M.sufCmaVqOracle n sk q st))
        ((sufToVqStep (tagBound n) req).run state.1) state.2).map
        (fun ⟨⟨a, b⟩, c⟩ => (a, b, c)))
    (represent := fun pairs : List (List Bool × List Bool) => ((), (⟨pairs, false⟩ : VqOracleState
      (List Bool) (List Bool))))
    (step := fun ⟨⟨⟩, msg⟩ pairs => by
      dsimp only [sufToVqStep, sufCmaVqOracle, signingPairOracle, signingPairOracleOn, StateT.run]
      by_cases hmsg : msg.length = M.msgLen n
      · simp only [hmsg, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte,
          ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, Prod.map, pmf_norm]
        refine PMF.bind_congr_on_support _ _ _ fun tag htag => ?_
        rw [List.take_of_length_le (htagBound sk hsk msg hmsg tag htag)]
        rfl
      · simp [hmsg, beq_eq_false_iff_ne.mpr hmsg, ProbOracleComp.runWith_map,
          ProbOracleComp.runWith_query])
    (adversary n []) []
  change (((ProbOracleComp.runWith _ (adversary n [])
      ((fun pairs : List (List Bool × List Bool) =>
        ((), (⟨pairs, false⟩ : VqOracleState (List Bool) (List Bool)))) [])).bind _).bind _) = _
  rw [← hsim, PMF.bind_map, PMF.bind_bind]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨msg, tag⟩, pairs⟩ _ => ?_
  simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
    sufCmaVqOracle, ↓reduceIte, ProbOracleComp.runWith_pure, Bool.false_or, encPair_apply,
    encBits_apply, unframe_frame_append, dropFrame_frame_append, pmf_norm]
  cases msg.length == M.msgLen n <;> cases !pairs.contains (msg, tag) <;>
    cases M.verify sk msg tag <;> rfl

/-- Attack Game 6.2 security (`SUFCMAVq`) implies standard strong unforgeability (`SUFCMA`). -/
theorem SUFCMAVq.sufCma {M : MACScheme} (h : M.SUFCMAVq) : M.SUFCMA := by
  obtain ⟨tagBound, htagPoly, htagValid⟩ := M.exists_tag_length_bound_of_length_eq
  apply SUFCMA.of_negligible
  intro adversary hadversary
  refine (h.negligible (sufToVqForger tagBound adversary)
    (isOraclePPT_sufToVqForger htagPoly hadversary)).congr fun n => ?_
  rw [M.eval_sufCmaVqGame_sufToVqForger (htagValid n) adversary]

/-! ### Direction 2: Theorem 6.1 (`SUFCMA` implies `SUFCMAVq`, `vqToSufForger`) -/

private def vqToSufHandler (M : MACScheme) (n tagBound : ℕ) (request : Bool × List Bool) :
    StateT
      (ProbOracleComp.PlantedOracleState (List Bool × List Bool) (List (List Bool × List Bool)))
      (WordOracleComp Unit) (List Bool) :=
  fun st =>
    if st.planted.hasCaptured then
      if request.1 then
        pure ([false], st)
      else
        pure ([], st)
    else if request.1 then
      let cand := (unframe request.2, dropFrame request.2)
      if st.planted.rem == 0 then
        pure ([false], ⟨⟨0, true, cand⟩, st.oracleState⟩)
      else
        pure ([st.oracleState.contains cand],
          ⟨⟨st.planted.rem - 1, false, ([], [])⟩, st.oracleState⟩)
    else
      if request.2.length == M.msgLen n then
        (fun tag => (tag, ⟨st.planted, (request.2, tag) :: st.oracleState⟩)) <$>
          (List.take tagBound <$> ProbOracleComp.query ((), request.2))
      else
        pure ([], st)

/-- Uniform Attack Game 6.2 to Attack Game 6.1 reduction ([BonehShoup2023], Section 6.2, Theorem
6.1, pp. 221–223): sample a target verification-query index `j` via
`ProbComp.sampleModIndex (width n) (Qv n)`, simulate `adversary n []`, and output the captured
`(msg, tag)` candidate. -/
noncomputable def vqToSufForger (M : MACScheme) (tagBound width Qv : ℕ → ℕ)
    (adversary : VqForger) : Forger :=
  fun n _ => do
    let j ← ProbOracleComp.sample (ProbComp.sampleModIndex (width n) (Qv n))
    let out ← (OracleComp.interpret
      (OracleComp.sumHandler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (M.vqToSufHandler n (tagBound n)))
      (adversary n [])).run (ProbOracleComp.PlantedOracleState.init j ([], []) [])
    return out.2.planted.candidate

/-- `M.vqToSufForger tagBound width Qv adversary` preserves uniform strict oracle-PPT admissibility
(`IsOraclePPT`) whenever `tagBound`, `width`, and `Qv` are computable in polynomial time in unary
and `adversary` is oracle-PPT. -/
theorem isOraclePPT_vqToSufForger (M : MACScheme) {tagBound width Qv : ℕ → ℕ}
    (htagBound : ComputableInPolyTime tagBound encUnary encUnary)
    (hwidth : ComputableInPolyTime width encUnary encUnary)
    (hQv : ComputableInPolyTime Qv encUnary encUnary)
    {adversary : VqForger} (hadversary : IsOraclePPT (encFinEnum Unit) adversary) :
    IsOraclePPT (encPair encBits encBits) (M.vqToSufForger tagBound width Qv adversary) := by
  have hmsgLen := M.msgLen_polyTime
  have hsample := (isPPTOn_sampleModIndex (input := encPair encUnary encBits)
    (width := fun p : ℕ × List Bool => width p.1)
    (bound := fun p : ℕ × List Bool => Qv p.1)
    (by polytime) (by polytime)).isOraclePPTOn (Operation := Unit)
  let ECaller := encPair (encPair encUnary encBits) encUnary
  have hinit : ComputableInPolyTime
      (fun caller : (ℕ × List Bool) × ℕ =>
        ProbOracleComp.PlantedOracleState.init caller.2
          (([], []) : List Bool × List Bool) ([] : List (List Bool × List Bool)))
      ECaller encVqPlantedState := by
    dsimp only [ECaller, ProbOracleComp.PlantedOracleState.init, ProbOracleComp.PlantedState.init]
    fun_prop
  have hhandler : IsOraclePPTOn
      (encPair ECaller
        (encPair (encPair encBool encBits) encVqPlantedState))
      (encPair encBits encVqPlantedState)
      (fun pair : ((ℕ × List Bool) × ℕ) ×
          ((Bool × List Bool) ×
            ProbOracleComp.PlantedOracleState (List Bool × List Bool)
              (List (List Bool × List Bool))) =>
        M.vqToSufHandler pair.1.1.1 (tagBound pair.1.1.1) pair.2.1 pair.2.2) := by
    have hcontains : ComputableInPolyTime
        (fun pair : ((ℕ × List Bool) × ℕ) ×
            ((Bool × List Bool) ×
              ProbOracleComp.PlantedOracleState (List Bool × List Bool)
                (List (List Bool × List Bool))) =>
          pair.2.2.oracleState.contains (unframe pair.2.1.2, dropFrame pair.2.1.2))
        (encPair ECaller (encPair (encPair encBool encBits) encVqPlantedState))
        encBool := by
      simp only [List.contains_eq_mem]
      fun_prop
    ppt [vqToSufHandler]
  have hrun : IsOraclePPTOn ECaller
      (encPair (encFinEnum Unit) encVqPlantedState)
      (fun caller : (ℕ × List Bool) × ℕ =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (M.vqToSufHandler caller.1.1 (tagBound caller.1.1)))
          (adversary caller.1.1 [])).run
          (ProbOracleComp.PlantedOracleState.init caller.2 ([], []) [])) := by
    apply hadversary.run_interpret_preprocess_open
      (operationEncoding := encBool)
      (stateEncoding := encVqPlantedState)
      (prepare := fun caller : (ℕ × List Bool) × ℕ => (caller.1.1, ([] : List Bool)))
      (initial := fun caller : (ℕ × List Bool) × ℕ =>
        ProbOracleComp.PlantedOracleState.init caller.2 ([], []) [])
      (resources := fun caller query =>
        4 * tagBound caller.1.1 + 8 * query.length + 16)
      (by polytime) hhandler hinit
      (fun _ _ => True) (fun _ => trivial) (by polytime)
    intro caller request st _ result hresult
    unfold vqToSufHandler at hresult
    have hframe := length_unframe_add_dropFrame_le request.2
    split_ifs at hresult
    pick_goal 5
    · obtain ⟨tag, htag, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
      obtain ⟨rawTag, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp htag
      have htake := List.length_take_le (tagBound caller.1.1) rawTag
      refine ⟨trivial, htake.trans (by lia), ?_⟩
      enc_len [encVqPlantedState_apply, encVqPlantedStateFields,
        encMsgTagPlanted_apply, encMsgTagPlantedFields]
    all_goals
      rw [OracleComp.eq_of_mem_supportWith_pure hresult]
      refine ⟨trivial, by simp, ?_⟩
      enc_len [encVqPlantedState_apply, encVqPlantedStateFields,
        encMsgTagPlanted_apply, encMsgTagPlantedFields]
  have hpost : ComputableInPolyTime
      (fun out : Unit ×
          ProbOracleComp.PlantedOracleState (List Bool × List Bool)
            (List (List Bool × List Bool)) =>
        out.2.planted.candidate)
      (encPair (encFinEnum Unit) encVqPlantedState)
      (encPair encBits encBits) := by
    fun_prop
  unfold vqToSufForger
  exact (hsample.bind_with
    (hrun.bind (hpost.isPPTOn.isOraclePPTOn (Operation := Unit)))).isOraclePPT

/-- `M.vqToSufForger` makes at most `Q_s` signing queries whenever `adversary n []` makes at most
`Q_s` signing queries. -/
theorem isQueryBounded_vqToSufForger (M : MACScheme) (tagBound width Qv : ℕ → ℕ)
    {adversary : VqForger} {n Q_s : ℕ}
    (hs : IsWordSigningQueryBounded (adversary n []) Q_s) :
    (M.vqToSufForger tagBound width Qv adversary n []).IsQueryBounded Q_s := by
  unfold vqToSufForger
  have hsample := ProbOracleComp.IsQueryBounded.sample
    (spec := fun _ : Unit × List Bool => List Bool)
    (ProbComp.sampleModIndex (width n) (Qv n))
  have hrun : ∀ j, (((OracleComp.interpret
      (OracleComp.sumHandler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (M.vqToSufHandler n (tagBound n)))
      (adversary n [])).run (ProbOracleComp.PlantedOracleState.init j ([], []) []))).IsQueryBounded
        Q_s := by
    intro j
    refine OracleComp.IsCostBounded.run_interpret (fun q s => ?_) hs _
    cases q with
    | inl k =>
      change ((ProbOracleComp.sample (ProbComp.unifFin k) >>= fun a => pure (a, s)) :
        WordOracleComp Unit _).IsQueryBounded 0
      exact ((ProbOracleComp.IsQueryBounded.sample (ProbComp.unifFin k)).bind
        fun a => .pure (a, s) 0).mono (by omega)
    | inr req =>
      rcases req with ⟨b, raw⟩
      change ((M.vqToSufHandler n (tagBound n) (b, raw)).run s).IsQueryBounded
        (if b then 0 else 1)
      dsimp only [vqToSufHandler, StateT.run]
      cases s.planted.hasCaptured
      · cases b
        · simp only [Bool.false_eq_true, ↓reduceIte]
          split_ifs
          · simp only [map_eq_bind_pure_comp]
            exact ((ProbOracleComp.IsQueryBounded.query ((), raw)).bind
              fun _ => .pure _ 0).mono (by omega)
          · exact .pure _ 1
        · simp only [Bool.false_eq_true, ↓reduceIte]
          split_ifs <;> exact .pure _ 0
      · cases b <;> exact .pure _ _
  exact (hsample.bind fun j => (hrun j).bind fun _ => .pure _ 0).mono (by omega)

/-- Equality witness linking `M.vqToSufForger` in `M.sufCmaGame` to the finite planted-query
reduction `vqToForgerOn` in `forgeExperiment`. -/
theorem eval_sufCmaGame_vqToSufForger_eq_forgeExperiment (M : MACScheme)
    {tagBound : ℕ → ℕ} (width Qv : ℕ → ℕ) {n : ℕ}
    (htagBound : ∀ sk ∈ (ProbComp.eval (M.keyGen n)).support,
      ∀ msg, msg.length = M.msgLen n →
      ∀ tag ∈ (ProbComp.eval (M.sign sk msg)).support, tag.length ≤ tagBound n)
    (adversary : VqForger) :
    ProbComp.eval (M.sufCmaGame (M.vqToSufForger tagBound width Qv adversary) n) =
      ProbComp.eval
        (forgeExperiment (((), ·) <$> M.keyGen n)
          ((Signer.ofSign M.sign).restrict (·.length == M.msgLen n))
          (fun () sk msg tag => (msg.length == M.msgLen n) && M.verify sk msg tag)
          freshPair
          (vqToForgerOn (fun _ msg => msg.length == M.msgLen n)
            (ProbComp.sampleModIndex (width n) (Qv n))
            (fun () => adversary.toTyped n []))) := by
  simp only [sufCmaGame, forgeExperiment, pmf_norm]
  refine PMF.bind_congr_on_support _ _ _ fun sk hsk => ?_
  rw [ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.runLogWith,
    ProbOracleComp.eval_runState]
  dsimp only [vqToSufForger, vqToForgerOn]
  rw [ProbOracleComp.runWith_sample_bind, ProbOracleComp.runWith_sample_bind,
    PMF.bind_bind, PMF.bind_bind]
  refine PMF.bind_congr_on_support _ _ _ fun j _ => ?_
  rw [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_run_interpret, ProbOracleComp.runWith_run_interpret,
    PMF.bind_map, PMF.bind_map]
  dsimp only [VqForger.toTyped]
  rw [ProbOracleComp.runWith_interpret_sumHandler]
  let represent :
      ProbOracleComp.PlantedOracleState (List Bool × List Bool) (List (List Bool × List Bool)) ×
        List (List Bool × List Bool) →
      ProbOracleComp.PlantedOracleState (List Bool × List Bool) (List (List Bool × List Bool)) ×
        List (List Bool × List Bool) :=
    fun ⟨st, extLog⟩ => (⟨st.planted, st.oracleState.reverse⟩, extLog.reverse)
  have hinit :
      (ProbOracleComp.PlantedOracleState.init j (([], []) : List Bool × List Bool)
          ([] : List (List Bool × List Bool)), ([] : List (List Bool × List Bool))) =
      represent (ProbOracleComp.PlantedOracleState.init j default [], []) := rfl
  have hsim := ProbOracleComp.runWith_map_state
    (oracle := fun req : Bool × List Bool =>
      ProbOracleComp.runWith
        (fun q state =>
          (ProbOracleComp.runWith
            (fun m l => ProbComp.eval
              (ProbOracleComp.logOracle
                ((Signer.ofSign M.sign).restrict (·.length == M.msgLen n) sk) m l))
            ((vqToForgerHandler (fun _ msg => msg.length == M.msgLen n) q).run state.1)
            state.2).map (fun ⟨⟨a, b⟩, c⟩ => (a, b, c)))
        (if req.1 then
          (fun ok : Bool => [ok]) <$>
            ProbOracleComp.query (spec := forgeVqSpec (List Bool) (List Bool))
              (Sum.inr (unframe req.2, dropFrame req.2))
        else
          ProbOracleComp.query (spec := forgeVqSpec (List Bool) (List Bool)) (Sum.inl req.2)))
    (oracle' := fun req state =>
      (ProbOracleComp.runWith (fun q s => ProbComp.eval (M.signingPairOracle n sk q s))
        ((M.vqToSufHandler n (tagBound n) req).run state.1) state.2).map
        (fun ⟨⟨a, b⟩, c⟩ => (a, b, c)))
    (represent := represent)
    (step := fun ⟨b, raw⟩ ⟨st, extLog⟩ => by
      dsimp only [represent, vqToSufHandler, vqToForgerHandler, StateT.run]
      cases hcap : st.planted.hasCaptured
      · cases b
        · simp only [hcap, Bool.false_eq_true, ↓reduceIte, ProbOracleComp.runWith_query]
          by_cases hmsg : raw.length = M.msgLen n
          · simp only [hmsg, beq_self_eq_true, ↓reduceIte, Functor.map_map,
              ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, ProbOracleComp.logOracle,
              Signer.restrict, Signer.ofSign, signingPairOracle, signingPairOracleOn, Prod.map,
              pmf_norm]
            rw [← PMF.bind_pure_comp]
            refine PMF.bind_congr_on_support _ _ _ fun tag htag => ?_
            rw [List.take_of_length_le (htagBound sk hsk raw hmsg tag htag)]
            simp
          · simp [beq_eq_false_iff_ne.mpr hmsg,
              show (default : List Bool) = [] from rfl]
        · simp only [hcap, Bool.false_eq_true, ↓reduceIte, ProbOracleComp.runWith_map,
            ProbOracleComp.runWith_query]
          cases st.planted.rem == 0
          · simp only [Bool.false_eq_true, ↓reduceIte, ProbOracleComp.runWith_pure, PMF.pure_map,
              Prod.map, List.contains_eq_mem, List.mem_reverse,
              show (default : List Bool × List Bool) = ([], []) from rfl]
            congr 3
            exact decide_eq_decide.mpr Iff.rfl
          · simp
      · cases b <;>
          simp [hcap, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
            show (default : List Bool) = [] from rfl])
    (adversary n []) (ProbOracleComp.PlantedOracleState.init j default [], [])
  rw [hinit, ← hsim, PMF.bind_map, PMF.bind_bind, PMF.bind_bind]
  refine PMF.bind_congr_on_support _ _ _ fun x _ => ?_
  rcases x with ⟨⟨⟩, st, extLog⟩
  dsimp only [represent, Function.comp_def]
  simp only [ProbOracleComp.runWith_pure, PMF.pure_bind, freshPair,
    List.contains_eq_mem, List.mem_reverse, Prod.mk.eta, decide_not]
  cases st.planted.candidate.1.length == M.msgLen n <;>
    cases M.verify sk st.planted.candidate.1 st.planted.candidate.2 <;>
    cases decide (st.planted.candidate ∈ extLog) <;> rfl

private theorem signer_restrict_admit (M : MACScheme) (n : ℕ)
    (keys : Unit × List Bool) (_ : keys ∈ (ProbComp.eval (((), ·) <$> M.keyGen n)).support)
    (log : List (List Bool × List Bool)) (msg : List Bool) :
    (((Signer.ofSign M.sign).restrict (·.length == M.msgLen n)) keys.2 log msg).isSome =
      (msg.length == M.msgLen n) := by
  by_cases h : msg.length = M.msgLen n <;> simp [Signer.restrict_apply, Signer.ofSign_apply, h]

private theorem signer_restrict_verify (M : MACScheme) (n : ℕ)
    (keys : Unit × List Bool) (hkeys : keys ∈ (ProbComp.eval (((), ·) <$> M.keyGen n)).support)
    (log : List (List Bool × List Bool)) (msg : List Bool)
    (program : ProbComp (List Bool))
    (hprog : ((Signer.ofSign M.sign).restrict (·.length == M.msgLen n)) keys.2 log msg =
      some program)
    (tag : List Bool) (htag : tag ∈ (ProbComp.eval program).support) :
    ((msg.length == M.msgLen n) && M.verify keys.2 msg tag) = true := by
  simp only [ProbComp.eval_map, PMF.mem_support_map_iff] at hkeys
  obtain ⟨sk, hsk, rfl⟩ := hkeys
  simp only [Signer.restrict_apply, Signer.ofSign_apply] at hprog
  split_ifs at hprog with hlen
  simp only [Option.some.injEq] at hprog
  subst hprog
  have hlen_eq : msg.length = M.msgLen n := beq_iff_eq.mp hlen
  simp [hlen, M.verify_sign n sk hsk msg hlen_eq tag htag]

/-- **Theorem 6.1, quantitative fair-coin loss bound** ([BonehShoup2023], Section 6.2, Theorem 6.1,
pp. 221–223): when `tagBound n` bounds honest tag lengths on `M.msgLen n`-bit messages and
`adversary n []` makes at most `Qv n` verification queries, `M.sufCmaVqGame adversary n` succeeds
with probability at most `Qv n` times the `sufCmaGame` success probability of
`M.vqToSufForger tagBound width Qv adversary`, plus the fair-coin residue bias
`Qv n / 2 ^ width n`. -/
theorem succProbability_sufCmaVqGame_le_mul_add (M : MACScheme)
    {tagBound : ℕ → ℕ} (width Qv : ℕ → ℕ) {adversary : VqForger} {n : ℕ}
    (htagBound : ∀ sk ∈ (ProbComp.eval (M.keyGen n)).support,
      ∀ msg, msg.length = M.msgLen n →
      ∀ tag ∈ (ProbComp.eval (M.sign sk msg)).support, tag.length ≤ tagBound n)
    (hQv : IsWordVerificationQueryBounded (adversary n []) (Qv n)) :
    Game.succProbability (ProbComp.eval (M.sufCmaVqGame adversary n)) ≤
      Qv n * Game.succProbability
          (ProbComp.eval (M.sufCmaGame (M.vqToSufForger tagBound width Qv adversary) n)) +
        Qv n / 2 ^ width n := by
  have hle : ProbComp.eval (M.sufCmaVqGame adversary n) true ≤
      (Qv n : ℝ≥0∞) *
          ProbComp.eval (M.sufCmaGame (M.vqToSufForger tagBound width Qv adversary) n) true +
        (Qv n : ℝ≥0∞) / 2 ^ width n := by
    rw [M.sufCmaVqGame_eq_vqForgeExperiment,
      M.eval_sufCmaGame_vqToSufForger_eq_forgeExperiment width Qv htagBound]
    exact eval_vqForgeExperiment_le_mul_sampleModIndex_add
      (((), ·) <$> M.keyGen n)
      ((Signer.ofSign M.sign).restrict (·.length == M.msgLen n))
      (fun () sk msg tag => (msg.length == M.msgLen n) && M.verify sk msg tag)
      (fun _ msg => msg.length == M.msgLen n)
      (M.signer_restrict_admit n)
      (M.signer_restrict_verify n)
      (width n) (Qv n)
      (fun () => adversary.isVerificationQueryBounded_toTyped hQv)
  simp only [Game.succProbability]
  rw [← ENNReal.coe_le_coe]
  push_cast [ENNReal.coe_toNNReal (PMF.apply_ne_top _ _),
    ENNReal.coe_div (pow_ne_zero _ two_ne_zero)]
  exact hle

/-- **Theorem 6.1, exact dyadic loss bound** ([BonehShoup2023], Section 6.2, Theorem 6.1,
pp. 221–223): proves the textbook bound `≤ Qv n * succProbability (M.sufCmaGame ...)` with no
additive error term when `Qv n = 0` (where `0` verification queries give winning probability `0`
via `M.succProbability_sufCmaVqGame_zero`) or when `Qv n` divides `2 ^ width n` (for instance a
power of two at most `2 ^ width n`, where `0 < Qv n` and
`ProbComp.sampleModIndex (width n) (Qv n)` is uniform below `Qv n`). -/
theorem succProbability_sufCmaVqGame_le_mul (M : MACScheme)
    {tagBound : ℕ → ℕ} (width Qv : ℕ → ℕ) {adversary : VqForger} {n : ℕ}
    (htagBound : ∀ sk ∈ (ProbComp.eval (M.keyGen n)).support,
      ∀ msg, msg.length = M.msgLen n →
      ∀ tag ∈ (ProbComp.eval (M.sign sk msg)).support, tag.length ≤ tagBound n)
    (hdvd : Qv n = 0 ∨ Qv n ∣ 2 ^ width n)
    (hQv : IsWordVerificationQueryBounded (adversary n []) (Qv n)) :
    Game.succProbability (ProbComp.eval (M.sufCmaVqGame adversary n)) ≤
      Qv n * Game.succProbability
        (ProbComp.eval (M.sufCmaGame (M.vqToSufForger tagBound width Qv adversary) n)) := by
  have hle : ProbComp.eval (M.sufCmaVqGame adversary n) true ≤
      (Qv n : ℝ≥0∞) *
        ProbComp.eval (M.sufCmaGame (M.vqToSufForger tagBound width Qv adversary) n) true := by
    rw [M.sufCmaVqGame_eq_vqForgeExperiment,
      M.eval_sufCmaGame_vqToSufForger_eq_forgeExperiment width Qv htagBound]
    exact eval_vqForgeExperiment_le_mul_sampleModIndex_of_dvd
      (((), ·) <$> M.keyGen n)
      ((Signer.ofSign M.sign).restrict (·.length == M.msgLen n))
      (fun () sk msg tag => (msg.length == M.msgLen n) && M.verify sk msg tag)
      (fun _ msg => msg.length == M.msgLen n)
      (M.signer_restrict_admit n)
      (M.signer_restrict_verify n)
      (width n) (Qv n) hdvd
      (fun () => adversary.isVerificationQueryBounded_toTyped hQv)
  simp only [Game.succProbability]
  rw [← ENNReal.toNNReal_natCast, ← ENNReal.toNNReal_mul]
  exact ENNReal.toNNReal_mono
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (PMF.apply_ne_top _ _)) hle

/-- **Verification queries do not weaken a strong MAC** ([BonehShoup2023], Section 6.2, Theorem 6.1,
pp. 221–223): every `SUFCMA`-secure `MACScheme` is `SUFCMAVq`-secure. -/
theorem SUFCMA.sufCmaVq {M : MACScheme} (h : M.SUFCMA) : M.SUFCMAVq := by
  obtain ⟨tagBound, htagPoly, htagValid⟩ := M.exists_tag_length_bound_of_length_eq
  apply SUFCMAVq.of_negligible
  intro adversary hadversary
  obtain ⟨cq, dq, hqbounds⟩ := hadversary.query_bounds
  let Qv : ℕ → ℕ := fun n => cq * (n + 2) ^ dq
  have hQvPoly : ComputableInPolyTime Qv encUnary encUnary := by
    dsimp only [Qv]
    fun_prop
  have hforger := h.negligible
    (M.vqToSufForger tagBound (fun n => n) Qv adversary)
    (M.isOraclePPT_vqToSufForger htagPoly .id' hQvPoly hadversary)
  have hbound : ∀ n,
      Game.succProbability (ProbComp.eval (M.sufCmaVqGame adversary n)) ≤
        Qv n * Game.succProbability
            (ProbComp.eval
              (M.sufCmaGame (M.vqToSufForger tagBound (fun n => n) Qv adversary) n)) +
          Qv n / 2 ^ n := by
    intro n
    have hq : (adversary n []).IsQueryBounded (Qv n) := by
      simpa [Qv] using (hqbounds n []).1
    exact M.succProbability_sufCmaVqGame_le_mul_add (fun m => m) Qv (htagValid n)
      (IsWordVerificationQueryBounded.of_isQueryBounded hq)
  dsimp only [Qv] at hforger hbound
  negligible using hbound

/-- **Equivalence of MAC security with and without verification queries** ([BonehShoup2023],
Section 6.2, Theorem 6.1, pp. 221–223): for every `MACScheme`, strong unforgeability with
verification queries (`SUFCMAVq`, Attack Game 6.2) is equivalent to strong unforgeability without
verification queries (`SUFCMA`, Attack Game 6.1). -/
theorem sufCmaVq_iff_sufCma (M : MACScheme) : M.SUFCMAVq ↔ M.SUFCMA :=
  ⟨SUFCMAVq.sufCma, SUFCMA.sufCmaVq⟩

end MACScheme

/-! ### Exercise 6.2: `prfMAC` security with verification queries (`vqMacToPrfDistinguisher`) -/

private def vqMacToPrfStep (n : ℕ) (request : Bool × List Bool) :
    StateT (VqOracleState (List Bool) (List Bool)) (WordOracleComp Unit) (List Bool) :=
  fun st =>
    if request.1 then
      let msg := unframe request.2
      let tag := dropFrame request.2
      if (msg.length == n) && (tag.length == n) then
        if st.log.contains (msg, tag) then
          pure ([true], st)
        else
          (fun realTag =>
            let ok := realTag == tag
            ([ok], ⟨st.log, st.won || ok⟩)) <$>
            (List.take n <$> ProbOracleComp.query ((), msg))
      else
        pure ([false], st)
    else
      if request.2.length == n then
        (fun tag => (tag, ⟨(request.2, tag) :: st.log, st.won⟩)) <$>
          (List.take n <$> ProbOracleComp.query ((), request.2))
      else
        pure ([], st)

/-- Direct oracle reduction turning a `VqForger` against `prfMAC family` into a PRF
`OracleDistinguisher` ([BonehShoup2023], Section 6.14, Exercise 6.2, p. 246): forwards `n`-bit
signing queries `(false, msg)` and fresh `(n, n)`-bit verification queries `(true, raw)` directly to
the PRF oracle (truncating replies to `n` bits), answers replayed `(msg, tag) ∈ log` pairs with
`[true]` and wrong-length requests with `[]` / `[false]` locally, and outputs `won`. -/
def vqMacToPrfDistinguisher (adversary : VqForger) : OracleDistinguisher :=
  fun n _ => do
    let out ← (OracleComp.interpret
      (OracleComp.sumHandler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (vqMacToPrfStep n))
      (adversary n [])).run ⟨[], false⟩
    return out.2.won

/-- `vqMacToPrfDistinguisher` preserves uniform strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_vqMacToPrfDistinguisher {adversary : VqForger}
    (hadversary : IsOraclePPT (encFinEnum Unit) adversary) :
    IsOraclePPT encBool (vqMacToPrfDistinguisher adversary) := by
  let ECaller := encPair encUnary encBits
  have hhandler : IsOraclePPTOn
      (encPair ECaller (encPair (encPair encBool encBits) encVqState))
      (encPair encBits encVqState)
      (fun pair : (ℕ × List Bool) ×
          ((Bool × List Bool) × VqOracleState (List Bool) (List Bool)) =>
        vqMacToPrfStep pair.1.1 pair.2.1 pair.2.2) := by
    have hcontains : ComputableInPolyTime
        (fun pair : (ℕ × List Bool) ×
            ((Bool × List Bool) × VqOracleState (List Bool) (List Bool)) =>
          pair.2.2.log.contains (unframe pair.2.1.2, dropFrame pair.2.1.2))
        (encPair ECaller (encPair (encPair encBool encBits) encVqState))
        encBool := by
      simp only [List.contains_eq_mem]
      fun_prop
    ppt [vqMacToPrfStep]
  have hinit : ComputableInPolyTime
      (fun _ : ℕ × List Bool => (⟨[], false⟩ : VqOracleState (List Bool) (List Bool)))
      ECaller encVqState := by
    fun_prop
  have hrun : IsOraclePPTOn ECaller
      (encPair (encFinEnum Unit) encVqState)
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (vqMacToPrfStep caller.1))
          (adversary caller.1 [])).run ⟨[], false⟩) := by
    apply hadversary.run_interpret_preprocess_open
      (operationEncoding := encBool)
      (stateEncoding := encVqState)
      (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
      (initial := fun _ => ⟨[], false⟩)
      (resources := fun caller query => 8 * caller.1 + 8 * query.length + 12)
      (by polytime) hhandler hinit
      (fun _ _ => True) (fun _ => trivial) (by polytime)
    intro caller request st _ result hresult
    dsimp only [vqMacToPrfStep] at hresult
    split_ifs at hresult
    any_goals
      rw [OracleComp.eq_of_mem_supportWith_pure hresult]
      exact ⟨trivial, by simp, by lia⟩
    · obtain ⟨_, htag, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
      obtain ⟨_, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp htag
      refine ⟨trivial, by simp, ?_⟩
      enc_len [encVqState_apply, encVqStateFields]
    · obtain ⟨tag, htag, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
      obtain ⟨rawTag, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp htag
      have htake := List.length_take_le caller.1 rawTag
      refine ⟨trivial, htake.trans (by lia), ?_⟩
      enc_len [encVqState_apply, encVqStateFields]
  have hpost : ComputableInPolyTime
      (fun out : Unit × VqOracleState (List Bool) (List Bool) => out.2.won)
      (encPair (encFinEnum Unit) encVqState) encBool := by
    fun_prop
  unfold vqMacToPrfDistinguisher
  exact (hrun.bind (hpost.isPPTOn.isOraclePPTOn (Operation := Unit))).isOraclePPT

/-- `vqMacToPrfDistinguisher` queries the external PRF oracle only on `n`-bit signing messages and
`(n, n)`-bit verification pairs, so its PRF query count is bounded by any budget `Q` on those
well-formed requests. -/
theorem isQueryBounded_vqMacToPrfDistinguisher_of_wellFormed {adversary : VqForger} {n Q : ℕ}
    (h : OracleComp.IsCostBounded
      (Sum.elim (fun _ => 0) fun req : Bool × List Bool =>
        if req.1 then
          if (unframe req.2).length == n && (dropFrame req.2).length == n then 1 else 0
        else
          if req.2.length == n then 1 else 0)
      (adversary n []) Q) :
    (vqMacToPrfDistinguisher adversary n []).IsQueryBounded Q := by
  unfold vqMacToPrfDistinguisher
  have hrun : (((OracleComp.interpret
      (OracleComp.sumHandler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (vqMacToPrfStep n))
      (adversary n [])).run ⟨[], false⟩)).IsQueryBounded Q := by
    refine OracleComp.IsCostBounded.run_interpret (fun q s => ?_) h _
    cases q with
    | inl k =>
      change ((ProbOracleComp.sample (ProbComp.unifFin k) >>= fun a => pure (a, s)) :
        WordOracleComp Unit _).IsQueryBounded 0
      exact ((ProbOracleComp.IsQueryBounded.sample (ProbComp.unifFin k)).bind
        fun a => .pure (a, s) 0).mono (by omega)
    | inr req =>
      rcases req with ⟨b, raw⟩
      dsimp only [OracleComp.sumHandler, vqMacToPrfStep, StateT.run, Sum.elim_inr]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split_ifs <;>
        first
        | exact .pure _ _
        | exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
            ((OracleComp.isCostBounded_map_iff _ _ _).mpr (ProbOracleComp.IsQueryBounded.query _))
  exact (hrun.bind fun _ => .pure _ 0).mono (by omega)

/-- `vqMacToPrfDistinguisher` makes at most `Q_s + Q_v` PRF queries when `adversary n []` makes at
most `Q_s` signing queries and at most `Q_v` verification queries. -/
theorem isQueryBounded_vqMacToPrfDistinguisher {adversary : VqForger} {n Q_s Q_v : ℕ}
    (hs : IsWordSigningQueryBounded (adversary n []) Q_s)
    (hv : IsWordVerificationQueryBounded (adversary n []) Q_v) :
    (vqMacToPrfDistinguisher adversary n []).IsQueryBounded (Q_s + Q_v) := by
  refine isQueryBounded_vqMacToPrfDistinguisher_of_wellFormed
    ((IsQueryBounded.of_word_signing_and_verification hs hv).of_le fun q => ?_)
  cases q with
  | inl _ => simp
  | inr req =>
    rcases req with ⟨b, _⟩
    cases b <;> dsimp only [Sum.elim_inr] <;> split_ifs <;> omega

private def toBitStringVq (n : ℕ) (prog : WordOracleComp Bool Unit) :
    ProbOracleComp (forgeVqSpec (BitString n) (BitString n)) Unit :=
  OracleComp.interpret
    (OracleComp.sumHandler
      (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
      (fun req : Bool × List Bool =>
        if req.1 then
          let msg := unframe req.2
          let tag := dropFrame req.2
          if (msg.length == n) && (tag.length == n) then
            (fun ok : Bool => [ok]) <$>
              ProbOracleComp.query (spec := forgeVqSpec (BitString n) (BitString n))
                (Sum.inr (BitString.ofList n msg, BitString.ofList n tag))
          else
            pure [false]
        else
          if req.2.length == n then
            List.ofFn <$>
              ProbOracleComp.query (spec := forgeVqSpec (BitString n) (BitString n))
                (Sum.inl (BitString.ofList n req.2))
          else
            pure []))
    prog

private theorem isVerificationQueryBounded_toBitStringVq {n Q_v : ℕ}
    {prog : WordOracleComp Bool Unit} (h : IsWordVerificationQueryBounded prog Q_v) :
    IsVerificationQueryBounded (toBitStringVq n prog) Q_v := by
  unfold IsVerificationQueryBounded toBitStringVq
  refine h.interpret fun q => ?_
  cases q with
  | inl k => exact ProbOracleComp.isCostBounded_sample _ (ProbComp.unifFin k)
  | inr req =>
    rcases req with ⟨b, raw⟩
    cases b <;> dsimp only [OracleComp.sumHandler] <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;> split_ifs <;>
      first
      | exact .pure _ _
      | rw [map_eq_bind_pure_comp]
        exact ((ProbOracleComp.isCostBounded_query _ _).bind fun _ => .pure _ 0).mono (by simp)

private theorem eval_adapt_vqMacToPrfDistinguisher_run_pure (adversary : VqForger) (n : ℕ)
    (table : BitString n → BitString n) :
    ProbComp.eval
        (((OracleCodec.bitString n).adapt (vqMacToPrfDistinguisher adversary n [])).run
          fun x => pure (table x)) =
      ProbComp.eval
        ((vqMacToPrfAdversary (fun _ => toBitStringVq n (adversary n []))).run
          fun x => pure (table x)) := by
  rw [OracleCodec.run_adapt, wordOracle_bitString]
  let handler : Bool × List Bool →
      ProbOracleComp (forgeVqSpec (BitString n) (BitString n)) (List Bool) := fun req =>
    if req.1 then
      let msg := unframe req.2
      let tag := dropFrame req.2
      if (msg.length == n) && (tag.length == n) then
        (fun ok : Bool => [ok]) <$>
          ProbOracleComp.query (spec := forgeVqSpec (BitString n) (BitString n))
            (Sum.inr (BitString.ofList n msg, BitString.ofList n tag))
      else
        pure [false]
    else
      if req.2.length == n then
        List.ofFn <$>
          ProbOracleComp.query (spec := forgeVqSpec (BitString n) (BitString n))
            (Sum.inl (BitString.ofList n req.2))
      else
        pure []
  have hrun_word :
      ProbComp.eval ((vqMacToPrfDistinguisher adversary n []).run
        fun request => pure (randomFunctionOracle n table request.2)) =
      (ProbOracleComp.runWith
        (fun req st =>
          (ProbOracleComp.runWith
            (fun r (u : Unit) => (PMF.pure (randomFunctionOracle n table r.2)).map (·, u))
            ((vqMacToPrfStep n req).run st.1) st.2).map (fun ⟨⟨a, b⟩, c⟩ => (a, b, c)))
        (adversary n []) (⟨[], false⟩, ())).bind (fun x => PMF.pure x.2.1.won) := by
    unfold vqMacToPrfDistinguisher
    simp only [ProbOracleComp.run, OracleComp.interpret_bind, OracleComp.interpret_pure,
      ProbComp.eval_bind, ProbComp.eval_pure]
    have hfst := congrArg (PMF.map Prod.fst) (ProbOracleComp.runWith_readOnly
      (fun request (_ : Unit) => PMF.pure (randomFunctionOracle n table request.2))
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (vqMacToPrfStep n))
        (adversary n [])).run ⟨[], false⟩) ())
    simp only [PMF.map_comp, Function.comp_def,
      show (fun x : Unit × VqOracleState (List Bool) (List Bool) => x) = id from rfl,
      PMF.map_id] at hfst
    rw [ProbOracleComp.eval_interpret]
    simp only [ProbComp.eval_pure]
    rw [← OracleComp.evalWith_eq_interpret, ← hfst, ProbOracleComp.runWith_run_interpret,
      PMF.bind_map, PMF.bind_map]
    rfl
  have hrun_typed :
      ProbComp.eval ((vqMacToPrfAdversary (fun _ => toBitStringVq n (adversary n []))).run
        fun x => pure (table x)) =
      (ProbOracleComp.runWith
        (fun req : Bool × List Bool =>
          ProbOracleComp.runWith
            (fun q state =>
              (ProbOracleComp.runWith (fun x (u : Unit) => (PMF.pure (table x)).map (·, u))
                ((vqMacToPrfHandler q).run state.1) state.2).map
                (fun ⟨⟨a, b⟩, c⟩ => (a, b, c)))
            (handler req))
        (adversary n []) (⟨[], false⟩, ())).bind (fun x => PMF.pure x.2.1.won) := by
    unfold vqMacToPrfAdversary
    simp only [ProbOracleComp.run, OracleComp.interpret_bind, OracleComp.interpret_pure,
      ProbComp.eval_bind, ProbComp.eval_pure]
    have hfst := congrArg (PMF.map Prod.fst) (ProbOracleComp.runWith_readOnly
      (fun x (_ : Unit) => PMF.pure (table x))
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          vqMacToPrfHandler)
        (toBitStringVq n (adversary n []))).run ⟨[], false⟩) ())
    simp only [PMF.map_comp, Function.comp_def,
      show (fun x : Unit × VqOracleState (BitString n) (BitString n) => x) = id from rfl,
      PMF.map_id] at hfst
    rw [ProbOracleComp.eval_interpret]
    simp only [ProbComp.eval_pure]
    rw [← OracleComp.evalWith_eq_interpret, ← hfst, ProbOracleComp.runWith_run_interpret]
    dsimp only [toBitStringVq]
    rw [ProbOracleComp.runWith_interpret_sumHandler, PMF.bind_map, PMF.bind_map]
    rfl
  rw [hrun_word, hrun_typed]
  let represent :
      VqOracleState (BitString n) (BitString n) × Unit →
      VqOracleState (List Bool) (List Bool) × Unit :=
    fun ⟨st, u⟩ => (⟨(st.log.map fun p => (List.ofFn p.1, List.ofFn p.2)).reverse, st.won⟩, u)
  have hinit : ((⟨[], false⟩ : VqOracleState (List Bool) (List Bool)), ()) =
      represent (⟨[], false⟩, ()) := rfl
  have hsim := ProbOracleComp.runWith_map_state
    (oracle := fun req : Bool × List Bool =>
      ProbOracleComp.runWith
        (fun q state =>
          (ProbOracleComp.runWith (fun x (u : Unit) => (PMF.pure (table x)).map (·, u))
            ((vqMacToPrfHandler q).run state.1) state.2).map
            (fun ⟨⟨a, b⟩, c⟩ => (a, b, c)))
        (handler req))
    (oracle' := fun req st =>
      (ProbOracleComp.runWith
        (fun r (u : Unit) => (PMF.pure (randomFunctionOracle n table r.2)).map (·, u))
        ((vqMacToPrfStep n req).run st.1) st.2).map (fun ⟨⟨a, b⟩, c⟩ => (a, b, c)))
    (represent := represent)
    (step := fun ⟨b, raw⟩ ⟨st, ⟨⟩⟩ => by
      dsimp only [represent, vqMacToPrfStep, vqMacToPrfHandler, handler, StateT.run]
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hmsg : raw.length = n
        · have hofFn_msg : List.ofFn (BitString.ofList n raw) = raw := BitString.ofFn_ofList hmsg
          have htake : (List.ofFn (table (BitString.ofList n raw))).take n =
              List.ofFn (table (BitString.ofList n raw)) :=
            List.take_of_length_le (List.length_ofFn).le
          simp [hmsg, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
            randomFunctionOracle, htake, hofFn_msg]
        · simp [beq_eq_false_iff_ne.mpr hmsg]
      · simp only [↓reduceIte]
        by_cases hboth : ((unframe raw).length == n && (dropFrame raw).length == n) = true
        · obtain ⟨hmsg, htag⟩ : (unframe raw).length = n ∧ (dropFrame raw).length = n := by
            simpa [Bool.and_eq_true, beq_iff_eq] using hboth
          have hofFn_msg : List.ofFn (BitString.ofList n (unframe raw)) = unframe raw :=
            BitString.ofFn_ofList hmsg
          have hofFn_tag : List.ofFn (BitString.ofList n (dropFrame raw)) = dropFrame raw :=
            BitString.ofFn_ofList htag
          have hmem_iff :
              ((BitString.ofList n (unframe raw), BitString.ofList n (dropFrame raw)) ∈ st.log) ↔
                ((st.log.map fun p => (List.ofFn p.1, List.ofFn p.2)).reverse.contains
                  (unframe raw, dropFrame raw) = true) := by
            rw [List.contains_reverse, List.contains_iff_mem, List.mem_map]
            constructor
            · intro hm
              exact ⟨_, hm, by simp [hofFn_msg, hofFn_tag]⟩
            · rintro ⟨⟨p1, p2⟩, hp, heq⟩
              rcases Prod.mk.inj heq with ⟨h1, h2⟩
              have hp1 : p1 = BitString.ofList n (unframe raw) :=
                List.ofFn_injective (h1.trans hofFn_msg.symm)
              have hp2 : p2 = BitString.ofList n (dropFrame raw) :=
                List.ofFn_injective (h2.trans hofFn_tag.symm)
              rwa [← hp1, ← hp2]
          by_cases hmem :
              (BitString.ofList n (unframe raw), BitString.ofList n (dropFrame raw)) ∈ st.log
          · have hcont : (st.log.map fun p => (List.ofFn p.1, List.ofFn p.2)).reverse.contains
                (unframe raw, dropFrame raw) = true := hmem_iff.mp hmem
            simp only [hmsg, htag, beq_self_eq_true, Bool.and_self, hcont, ↓reduceIte,
              ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, hmem,
              ProbOracleComp.runWith_pure, PMF.pure_map, Prod.map]
            rfl
          · have hcont : (st.log.map fun p => (List.ofFn p.1, List.ofFn p.2)).reverse.contains
                (unframe raw, dropFrame raw) = false :=
              Bool.eq_false_iff.mpr (mt hmem_iff.mpr hmem)
            have htake : (List.ofFn (table (BitString.ofList n (unframe raw)))).take n =
                List.ofFn (table (BitString.ofList n (unframe raw))) :=
              List.take_of_length_le (List.length_ofFn).le
            have hbeq : (List.ofFn (table (BitString.ofList n (unframe raw))) == dropFrame raw) =
                decide (table (BitString.ofList n (unframe raw)) =
                  BitString.ofList n (dropFrame raw)) := by
              refine Bool.eq_iff_iff.mpr ⟨fun h => ?_, fun h => ?_⟩
              · rw [beq_iff_eq, ← hofFn_tag] at h
                exact decide_eq_true (List.ofFn_injective h)
              · rw [decide_eq_true_eq] at h
                exact beq_iff_eq.mpr ((congrArg List.ofFn h).trans hofFn_tag)
            simp only [hmsg, htag, beq_self_eq_true, Bool.and_self, hcont, Bool.false_eq_true,
              ↓reduceIte, Functor.map_map, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
              hmem, randomFunctionOracle, PMF.pure_map, Prod.map, htake, hbeq]
            rfl
        · have hbothF : ((unframe raw).length == n && (dropFrame raw).length == n) = false :=
            Bool.eq_false_iff.mpr hboth
          simp [hbothF])
    (adversary n []) (⟨[], false⟩, ())
  rw [hinit, ← hsim, PMF.bind_map]
  rfl

/-- Running `vqMacToPrfDistinguisher adversary` in `prfRealGame id family` produces the exact same
Boolean law as `(prfMAC family hpoly).sufCmaVqGame adversary n`. -/
theorem eval_prfRealGame_vqMacToPrfDistinguisher
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (adversary : VqForger) (n : ℕ) :
    ProbComp.eval (prfRealGame id family (vqMacToPrfDistinguisher adversary) n) =
      ProbComp.eval ((prfMAC family hpoly).sufCmaVqGame adversary n) := by
  simp only [prfRealGame, id_eq, MACScheme.sufCmaVqGame, vqMacToPrfDistinguisher,
    ProbOracleComp.run, OracleComp.interpret_bind, OracleComp.interpret_pure,
    ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun sk hsk => ?_
  have hsk' : sk ∈ (ProbComp.eval (BitString.sampleList n)).support := hsk
  rw [BitString.eval_sampleList] at hsk'
  have hskLen : sk.length = n := BitString.length_of_mem_support_uniformList hsk'
  let ValidState := {st : VqOracleState (List Bool) (List Bool) //
    ∀ p ∈ st.log, p.1.length = n ∧ p.2 = family sk p.1}
  let validStep : Bool × List Bool → StateT ValidState PMF (List Bool) :=
    fun req s =>
      if req.1 then
        let msg := unframe req.2
        let tag := dropFrame req.2
        let ok := (msg.length == n) && (family sk msg == tag)
        let fresh := !s.val.log.contains (msg, tag)
        PMF.pure ([ok], ⟨⟨s.val.log, s.val.won || (ok && fresh)⟩, s.property⟩)
      else
        if hmsg : req.2.length = n then
          let tag := family sk req.2
          PMF.pure (tag, ⟨⟨(req.2, tag) :: s.val.log, s.val.won⟩, fun p hp => by
            rcases List.mem_cons.mp hp with rfl | hp
            · exact ⟨hmsg, rfl⟩
            · exact s.property p hp⟩)
        else
          PMF.pure ([], s)
  have hlhs :
      ProbComp.eval (OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifFin fun req => pure (prfOracle family n sk req.2))
        ((OracleComp.interpret
          (OracleComp.sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (vqMacToPrfStep n))
          (adversary n [])).run ⟨[], false⟩)) =
      (ProbOracleComp.runWith validStep (adversary n []) ⟨⟨[], false⟩, by simp⟩).map
        (fun x => (x.1, x.2.val)) := by
    have hfst := congrArg (PMF.map Prod.fst) (ProbOracleComp.runWith_readOnly
      (fun req (_ : Unit) => PMF.pure (prfOracle family n sk req.2))
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (vqMacToPrfStep n))
        (adversary n [])).run ⟨[], false⟩) ())
    simp only [PMF.map_comp, Function.comp_def,
      show (fun x : Unit × VqOracleState (List Bool) (List Bool) => x) = id from rfl,
      PMF.map_id] at hfst
    rw [ProbOracleComp.eval_interpret]
    simp only [ProbComp.eval_pure]
    rw [← OracleComp.evalWith_eq_interpret, ← hfst, ProbOracleComp.runWith_run_interpret]
    have hinit : ((⟨[], false⟩ : VqOracleState (List Bool) (List Bool)), ()) =
        (fun s : ValidState => (s.val, ())) ⟨⟨[], false⟩, by simp⟩ := rfl
    have hsim := ProbOracleComp.runWith_map_state
      (oracle := validStep)
      (oracle' := fun req state =>
        (ProbOracleComp.runWith (fun r (u : Unit) => (PMF.pure (prfOracle family n sk r.2)).map
            (·, u))
          ((vqMacToPrfStep n req).run state.1) state.2).map (fun ⟨⟨a, b⟩, c⟩ => (a, b, c)))
      (represent := fun s : ValidState => (s.val, ()))
      (step := fun ⟨b, raw⟩ s => by
        dsimp only [validStep, vqMacToPrfStep, StateT.run]
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases hmsg : raw.length = n
          · have hfamLen : (family sk raw).length = n :=
              hskLen ▸ hlen sk raw (hmsg.trans hskLen.symm)
            simp [hmsg, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, prfOracle,
              List.take_of_length_le hfamLen.le]
          · simp [hmsg, beq_eq_false_iff_ne.mpr hmsg]
        · simp only [↓reduceIte]
          by_cases hmsg : (unframe raw).length = n
          · have hfamLen : (family sk (unframe raw)).length = n :=
              hskLen ▸ hlen sk (unframe raw) (hmsg.trans hskLen.symm)
            by_cases htag : (dropFrame raw).length = n
            · by_cases hcont : s.val.log.contains (unframe raw, dropFrame raw) = true
              · have hprop := s.property (unframe raw, dropFrame raw)
                  (List.contains_iff_mem.mp hcont)
                have heq : (family sk (unframe raw) == dropFrame raw) = true :=
                  beq_iff_eq.mpr hprop.2.symm
                simp only [hmsg, htag, beq_self_eq_true, Bool.and_self, ↓reduceIte, hcont, heq,
                  Bool.not_true, Bool.and_false, Bool.or_false,
                  ProbOracleComp.runWith_pure, PMF.pure_map]
              · have hcontF : s.val.log.contains (unframe raw, dropFrame raw) = false :=
                  Bool.eq_false_iff.mpr hcont
                simp only [hmsg, htag, beq_self_eq_true, Bool.and_self, hcontF,
                  Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.and_true, Bool.true_and,
                  Functor.map_map, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
                  prfOracle, PMF.pure_map, Prod.map, id_eq,
                  List.take_of_length_le hfamLen.le]
            · have hneq : (family sk (unframe raw) == dropFrame raw) = false :=
                beq_eq_false_iff_ne.mpr fun heq => htag (heq ▸ hfamLen)
              simp [hmsg, beq_eq_false_iff_ne.mpr htag, hneq]
          · simp [beq_eq_false_iff_ne.mpr hmsg])
      (adversary n []) ⟨⟨[], false⟩, by simp⟩
    rw [hinit, ← hsim, PMF.map_comp, PMF.map_comp]
    rfl
  have hrhs :
      ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
          ((prfMAC family hpoly).sufCmaVqOracle n sk)) (adversary n [])).run ⟨[], false⟩) =
      (ProbOracleComp.runWith validStep (adversary n []) ⟨⟨[], false⟩, by simp⟩).map
        (fun x => (x.1, x.2.val)) := by
    rw [ProbOracleComp.eval_run_interpret_eq_runWith]
    exact (ProbOracleComp.runWith_map_state
      (oracle := validStep)
      (oracle' := fun req st => ProbComp.eval ((prfMAC family hpoly).sufCmaVqOracle n sk req st))
      (represent := Subtype.val)
      (step := fun ⟨b, raw⟩ s => by
        dsimp only [validStep, MACScheme.sufCmaVqOracle, prfMAC, StateT.run]
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases hmsg : raw.length = n
          · simp [hmsg, hskLen, prfOracle]
          · simp [hmsg, beq_eq_false_iff_ne.mpr hmsg]
        · simp [hskLen])
      (adversary n []) ⟨⟨[], false⟩, by simp⟩).symm
  rw [hlhs, hrhs]

private theorem advantage_vqMacToPrfDistinguisher_eq_atLevel
    {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (adversary : VqForger) (n : ℕ) :
    Game.advantage
        (ProbComp.eval (prfRealGame id family (vqMacToPrfDistinguisher adversary) n))
        (ProbComp.eval (prfIdealGame id id (vqMacToPrfDistinguisher adversary) n)) =
      PRF.advantage (PRF.atLevel family n)
        (vqMacToPrfAdversary (fun _ => toBitStringVq n (adversary n []))) := by
  rw [← PRF.advantage_atLevel_adapt hlen (vqMacToPrfDistinguisher adversary) n]
  unfold PRF.advantage
  have hreal :
      ProbComp.eval (PRF.realExperiment (PRF.atLevel family n)
        ((OracleCodec.bitString n).adapt (vqMacToPrfDistinguisher adversary n []))) =
      ProbComp.eval (PRF.realExperiment (PRF.atLevel family n)
        (vqMacToPrfAdversary (fun _ => toBitStringVq n (adversary n [])))) := by
    simp only [PRF.realExperiment, ProbComp.eval_bind]
    refine PMF.bind_congr_on_support _ _ _ fun key _ => ?_
    exact eval_adapt_vqMacToPrfDistinguisher_run_pure adversary n (PRF.atLevel family n key)
  have hideal :
      ProbComp.eval (PRF.idealExperiment
        ((OracleCodec.bitString n).adapt (vqMacToPrfDistinguisher adversary n []))) =
      ProbComp.eval (PRF.idealExperiment
        (vqMacToPrfAdversary (fun _ => toBitStringVq n (adversary n [])))) := by
    simp only [PRF.idealExperiment, ProbComp.eval_bind]
    refine PMF.bind_congr_on_support _ _ _ fun table _ => ?_
    exact eval_adapt_vqMacToPrfDistinguisher_run_pure adversary n table
  rw [hreal, hideal]

/-- **Quantitative PRF-to-SUFCMAVq bound for `prfMAC`** ([BonehShoup2023], Section 6.14, Exercise
6.2, p. 246): for every length-preserving keyed function `family` and every `VqForger` making at
most `Q_v` verification queries at security parameter `n`, the `sufCmaVqGame` winning probability
against `prfMAC family` is at most the PRF distinguishing advantage of
`vqMacToPrfDistinguisher adversary` plus `Q_v / 2 ^ n` (without a `Q_v` factor on the PRF
advantage). -/
theorem succProbability_sufCmaVqGame_prfMAC_le
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    {adversary : VqForger} {n Q_v : ℕ}
    (hQv : IsWordVerificationQueryBounded (adversary n []) Q_v) :
    Game.succProbability (ProbComp.eval ((prfMAC family hpoly).sufCmaVqGame adversary n)) ≤
      Game.advantage
        (ProbComp.eval (prfRealGame id family (vqMacToPrfDistinguisher adversary) n))
        (ProbComp.eval (prfIdealGame id id (vqMacToPrfDistinguisher adversary) n)) +
      (Q_v : ℝ≥0) / 2 ^ n := by
  have hreal_eq :
      ProbComp.eval ((prfMAC family hpoly).sufCmaVqGame adversary n) =
        ProbComp.eval
          (vqForgeExperiment (((), ·) <$> ProbComp.uniform (BitString n))
            (Signer.ofSign fun k m => pure (PRF.atLevel family n k m))
            (fun _ k m σ => decide (PRF.atLevel family n k m = σ))
            (fun _ => toBitStringVq n (adversary n []))) := by
    rw [← eval_prfRealGame_vqMacToPrfDistinguisher hpoly hlen adversary n,
      ← PRF.eval_realExperiment_atLevel_adapt hlen (vqMacToPrfDistinguisher adversary) n,
      ← eval_realExperiment_vqMacToPrfAdversary]
    simp only [PRF.realExperiment, ProbComp.eval_bind]
    refine PMF.bind_congr_on_support _ _ _ fun key _ => ?_
    exact eval_adapt_vqMacToPrfDistinguisher_run_pure adversary n (PRF.atLevel family n key)
  rw [hreal_eq, advantage_vqMacToPrfDistinguisher_eq_atLevel hlen adversary n]
  have hfin := succProbability_vqForgeExperiment_prf_le (PRF.atLevel family n) Q_v
    (A := fun _ => toBitStringVq n (adversary n []))
    (isVerificationQueryBounded_toBitStringVq hQv)
  have hcard : (Fintype.card (BitString n) : ℝ≥0) = 2 ^ n := by
    simp [BitString]
  rwa [hcard] at hfin

/-- **Every pseudorandom function yields an `SUFCMAVq`-secure MAC via Exercise 6.2**
([BonehShoup2023], Section 6.14, Exercise 6.2, p. 246): proved directly via
`vqMacToPrfDistinguisher` and `succProbability_sufCmaVqGame_prfMAC_le` without incurring a `Q_v`
factor on the PRF advantage. -/
theorem PseudorandomFunction.sufCmaVq_prfMAC
    {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family) :
    (prfMAC family hprf.polyTime).SUFCMAVq := by
  apply MACScheme.SUFCMAVq.of_negligible
  intro adversary hadversary
  obtain ⟨cq, dq, hqbounds⟩ := hadversary.query_bounds
  have hdist := hprf.secure (vqMacToPrfDistinguisher adversary)
    (isOraclePPT_vqMacToPrfDistinguisher hadversary)
  have hbound : ∀ n,
      Game.succProbability
          (ProbComp.eval ((prfMAC family hprf.polyTime).sufCmaVqGame adversary n)) ≤
        Game.advantage
          (ProbComp.eval (prfRealGame id family (vqMacToPrfDistinguisher adversary) n))
          (ProbComp.eval (prfIdealGame id id (vqMacToPrfDistinguisher adversary) n)) +
        ((cq * (n + 2) ^ dq : ℕ) : ℝ≥0) / 2 ^ n := by
    intro n
    have hq : (adversary n []).IsQueryBounded (cq * (n + 2) ^ dq) := by
      simpa using (hqbounds n []).1
    exact succProbability_sufCmaVqGame_prfMAC_le hprf.polyTime hprf.length_eq
      (IsWordVerificationQueryBounded.of_isQueryBounded hq)
  negligible using hbound

end Cslib.Crypto
