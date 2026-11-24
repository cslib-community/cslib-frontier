/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Encoding
public import CslibFrontier.Crypto.Game
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation.Handler
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.PolyTime.Init

/-!
# Uniform digital signature schemes and existential unforgeability

A uniform digital signature scheme (`SignatureScheme`) consists of a strict probabilistic
polynomial-time key generator `keyGen`, a strict probabilistic polynomial-time signing algorithm
`sign`, and a deterministic polynomial-time verification algorithm `verify` that accepts every
signature produced by `sign` on an `n`-bit message under a key pair sampled at security parameter
`n`. The message space at parameter `n` is exactly the `n`-bit words; this module does not
claim security for arbitrary polynomial-length message families.

We formalize two adaptive chosen-message security notions against uniform strict oracle-PPT forgers
(`IsOraclePPT`):

* **Existential unforgeability under adaptive chosen-message attack (`eufCmaGame`, `EUFCMA`)**:
  the forger receives the unary security parameter `n` and public verification key `pk`, has
  adaptive oracle access to `signingOracle n sk` on `n`-bit messages, and wins by outputting a valid
  `(msg, sig)` pair with `msg.length = n` such that `msg` was never queried to the signing oracle.
  The oracle answers a query of any other length with the empty word, without signing or recording
  it, so signing queries lie in the message space as in the source.
* **Existential unforgeability under one-time adaptive chosen-message attack (`eufOneTimeGame`,
  `OneTimeEUFCMA`)**: the signing oracle `oneTimeSigningOracle n sk` answers at most the first
  `n`-bit signing query and returns the empty word on any other query. Every `EUFCMA`-secure scheme
  is a fortiori `OneTimeEUFCMA`-secure (`SignatureScheme.EUFCMA.oneTimeEUFCMA`).

## Main definitions

* `Cslib.Crypto.Forger`: adaptive oracle adversary outputting a `(message, signature)` pair.
* `Cslib.Crypto.encForgeryLog`: the encoding of a forgery with the list of queried messages.
* `Cslib.Crypto.SignatureScheme`: uniform digital signature scheme on `n`-bit messages.
* `Cslib.Crypto.SignatureScheme.signingOracleOn`, `Cslib.Crypto.SignatureScheme.signingOracleOf`,
  `Cslib.Crypto.SignatureScheme.signingOracle`, `eufCmaGame`, `EUFCMA`: message-logging signing
  oracle on a message space and on every word, and full adaptive EUF-CMA experiment and security
  predicate.
* `Cslib.Crypto.SignatureScheme.oneTimeSigningOracleOn`,
  `Cslib.Crypto.SignatureScheme.oneTimeSigningOracle`, `eufOneTimeGame`, `OneTimeEUFCMA`: one-time
  message-logging signing oracle on a message space and one-time adaptive EUF-CMA experiment and
  security predicate.

## Main results

* `Cslib.Crypto.SignatureScheme.exists_sign_length_bound`,
  `Cslib.Crypto.SignatureScheme.exists_sign_length_bound_of_length_eq`: plain polynomial-time bounds
  on signature lengths, in the security parameter and the message length or on `n`-bit messages.
* `Cslib.Crypto.SignatureScheme.isPPTOn_run_signingOracleOn`,
  `Cslib.Crypto.SignatureScheme.isPPTOn_run_signingOracleOf`,
  `Cslib.Crypto.SignatureScheme.isPPTOn_run_signingOracle`,
  `Cslib.Crypto.SignatureScheme.isPPTOn_eufCmaGame`, `isPPT_eufCmaGame`: strict PPT certificates
  for the message-logging signing oracle and full EUF-CMA experiment.
* `Cslib.Crypto.SignatureScheme.isPPTOn_run_oneTimeSigningOracleOn`,
  `Cslib.Crypto.SignatureScheme.isPPTOn_run_oneTimeSigningOracle`,
  `Cslib.Crypto.SignatureScheme.isPPTOn_eufOneTimeGame`, `isPPT_eufOneTimeGame`: strict PPT
  certificates for the one-time signing oracle and one-time EUF-CMA experiment.
* `Cslib.Crypto.SignatureScheme.run_limitToOneQuery_eq_oneTimeSigningOracleOn`,
  `Cslib.Crypto.SignatureScheme.EUFCMA.oneTimeEUFCMA`: one-query filter simulation and implication
  from full EUF-CMA security to one-time EUF-CMA security. The filter forwards only queries in the
  message space, so a refused query does not use up the one forwarded query.
* `Cslib.Crypto.SignatureScheme.restrictQueries`,
  `Cslib.Crypto.SignatureScheme.isOraclePPT_restrictQueries`,
  `Cslib.Crypto.SignatureScheme.run_restrictQueries_eq_signingOracleOn`: the forger that answers
  queries outside the message space itself, so that a bound against the oracle on every word
  transfers to the oracle on the message space.

## References

* [S. Goldwasser, S. Micali, R. L. Rivest, *A Digital Signature Scheme Secure Against Adaptive
  Chosen-Message Attacks*][GoldwasserMicaliRivest1988]
* [L. Lamport, *Constructing Digital Signatures from a One-Way Function*][Lamport1979]
* [J. Rompel, *One-Way Functions are Necessary and Sufficient for Secure Signatures*][Rompel1990]
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

/-- An adaptive forger receives a unary security parameter and a public verification key, queries a
signing oracle on chosen messages, and outputs a candidate `(message, signature)` pair. -/
abbrev Forger := ℕ → List Bool → WordOracleComp Unit (List Bool × List Bool)

/-- Output `((msg, sig), queried)` of a forger run against a message-logging signing oracle: the
candidate forgery `(msg, sig)` as bit words, then the list of queried messages. The forgery is
framed, with `msg` framed again inside it, and so is each queried message. -/
abbrev encForgeryLog : (List Bool × List Bool) × List (List Bool) ↪ List Bool :=
  encPair (encPair encBits encBits) (encList encBits)

/-- A uniform digital signature scheme on `n`-bit messages at security parameter `n`, with strict
polynomial-time key generation and signing, deterministic polynomial-time verification, and perfect
completeness on supported key pairs, `n`-bit messages, and signatures. -/
structure SignatureScheme where
  /-- Sample a public verification key and secret signing key `(pk, sk)` at unary parameter `n`. -/
  keyGen : ℕ → ProbComp (List Bool × List Bool)
  /-- Sign a message `msg` using the secret signing key `sk`. -/
  sign : List Bool → List Bool → ProbComp (List Bool)
  /-- Deterministically verify a candidate signature `sig` on `msg` under public key `pk`. -/
  verify : List Bool → List Bool → List Bool → Bool
  /-- Key generation is uniformly strict PPT in the unary security parameter. -/
  keyGen_ppt : IsPPTOn encUnary (encPair encBits encBits) keyGen
  /-- Signing is uniformly strict PPT in the encoded secret key and message. -/
  sign_ppt : IsPPTOn (encPair encBits encBits) encBits (fun p => sign p.1 p.2)
  /-- Verification is computable in plain polynomial time on `(pk, msg, sig)`. -/
  verify_polyTime : ComputableInPolyTime
    (fun p : List Bool × List Bool × List Bool => verify p.1 p.2.1 p.2.2)
    (encPair encBits (encPair encBits encBits)) encBool
  /-- Every signature produced by `sign` on an `n`-bit message under a supported key pair at
  security parameter `n` is accepted by `verify`. -/
  verify_sign : ∀ n keys, keys ∈ (ProbComp.eval (keyGen n)).support →
    ∀ msg, msg.length = n →
    ∀ sig, sig ∈ (ProbComp.eval (sign keys.2 msg)).support →
    verify keys.1 msg sig = true

namespace SignatureScheme

attribute [program_certificate] keyGen_ppt sign_ppt verify_polyTime

@[program_certificate, fun_prop]
theorem isPPTOn_keyGen_comp (S : SignatureScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableInPolyTime n encIn encUnary) :
    IsPPTOn encIn (encPair encBits encBits) (fun a => S.keyGen (n a)) :=
  S.keyGen_ppt.preprocess hn

@[program_certificate, fun_prop]
theorem isPPTOn_sign_comp (S : SignatureScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {sk msg : γ → List Bool}
    (hsk : ComputableInPolyTime sk encIn encBits)
    (hmsg : ComputableInPolyTime msg encIn encBits) :
    IsPPTOn encIn encBits (fun a => S.sign (sk a) (msg a)) :=
  S.sign_ppt.preprocess (hsk.prod hmsg)

@[program_certificate, fun_prop]
theorem computableInPolyTime_verify_comp (S : SignatureScheme)
    {γ : Type} {encIn : γ ↪ List Bool} {pk msg sig : γ → List Bool}
    (hpk : ComputableInPolyTime pk encIn encBits)
    (hmsg : ComputableInPolyTime msg encIn encBits)
    (hsig : ComputableInPolyTime sig encIn encBits) :
    ComputableInPolyTime (fun a => S.verify (pk a) (msg a) (sig a)) encIn encBool :=
  S.verify_polyTime.comp (hpk.prod (hmsg.prod hsig))

/-- Signatures have polynomially bounded length: some plain polynomial-time `bound n L` bounds
every signature on a message of length `L` under a key pair sampled at parameter `n`. -/
theorem exists_sign_length_bound (S : SignatureScheme) :
    ∃ bound : ℕ → ℕ → ℕ,
      ComputableInPolyTime (fun p : ℕ × ℕ => bound p.1 p.2) (encPair encUnary encUnary) encUnary ∧
      ∀ n, ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ msg sig,
        sig ∈ (ProbComp.eval (S.sign keys.2 msg)).support → sig.length ≤ bound n msg.length := by
  obtain ⟨ck, dk, hlenk⟩ := S.keyGen_ppt.length_le
  obtain ⟨cs, ds, hlens⟩ := S.sign_ppt.length_le
  refine ⟨fun n L => cs * (2 * (ck * (n + 1) ^ dk) + L + 2) ^ ds, by fun_prop,
    fun n keys hkeys msg sig hsig => ?_⟩
  have hkeyLen := hlenk n keys hkeys
  simp only [encUnary_apply, List.length_replicate, length_encPair, encBits_apply] at hkeyLen
  have hsigLen := hlens (keys.2, msg) sig hsig
  simp only [length_encPair, encBits_apply] at hsigLen
  exact hsigLen.trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (by lia) ds))

/-- `exists_sign_length_bound` on the scheme's own message space: some plain polynomial-time
`bound n` bounds every signature on an `n`-bit message under a key pair sampled at parameter `n`. -/
theorem exists_sign_length_bound_of_length_eq (S : SignatureScheme) :
    ∃ bound : ℕ → ℕ, ComputableInPolyTime bound encUnary encUnary ∧
      ∀ n, ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ msg, msg.length = n →
        ∀ sig ∈ (ProbComp.eval (S.sign keys.2 msg)).support, sig.length ≤ bound n := by
  obtain ⟨bound, hpoly, hbound⟩ := S.exists_sign_length_bound
  exact ⟨fun n => bound n n, by fun_prop, fun n keys hkeys msg hmsg sig hsig => by
    simpa only [hmsg] using hbound n keys hkeys msg sig hsig⟩

private theorem computableInPolyTime_signResources (c d : ℕ) :
    ComputableInPolyTime
      (fun pair : (ℕ × (List Bool × List Bool)) × List Bool =>
        c * (2 * pair.1.2.2.length + pair.2.length + 2) ^ d + 2 * pair.2.length + 2)
      (encPair encKeyPairInput encBits) encUnary := by
  fun_prop

private theorem computableInPolyTime_eufPost (S : SignatureScheme) :
    ComputableInPolyTime
      (fun pair : (ℕ × (List Bool × List Bool)) × ((List Bool × List Bool) × List (List Bool)) =>
        (pair.2.1.1.length == pair.1.1) && !pair.2.2.contains pair.2.1.1 &&
          S.verify pair.1.2.1 pair.2.1.1 pair.2.1.2)
      (encPair encKeyPairInput encForgeryLog) encBool := by
  have hcaller := ComputableInPolyTime.fst
    (encPair encUnary (encPair encBits encBits))
    (encPair (encPair encBits encBits) (encList encBits))
  have hout := ComputableInPolyTime.snd
    (encPair encUnary (encPair encBits encBits))
    (encPair (encPair encBits encBits) (encList encBits))
  have hmsg := hout.fst'.fst'
  have hcontains : (fun pair :
      (ℕ × (List Bool × List Bool)) × ((List Bool × List Bool) × List (List Bool)) =>
      pair.2.2.contains pair.2.1.1) =
      (fun pair => pair.2.2.any (fun x => pair.2.1.1 == x)) := by
    funext a
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.any_eq_true]
    simp only [beq_iff_eq]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨_, h, heq⟩ => heq ▸ h⟩
  exact (((ComputableInPolyTime.length_bits.comp hmsg).beq hcaller.fst').bool_and'
    (ComputableInPolyTime.bool_not.comp (hcontains ▸
      ComputableInPolyTime.anyWithInput (test := fun pair x => pair.2.1.1 == x) hout.snd'
        ((hmsg.comp (.fst _ _)).beq (.snd _ _))))).bool_and'
    (S.verify_polyTime.comp (hcaller.snd'.fst'.prod (hmsg.prod hout.fst'.snd')))

/-! ### Full adaptive chosen-message security (`EUFCMA`) -/

/-- Stateful signing/tagging oracle on the message space `adm`: it signs an admissible requested
message with `sign sk` and prepends it to the list of queried messages, and it answers any other
request with the empty word, without signing or recording it (`Signer.restrict`). -/
abbrev signingOracleOn (adm : List Bool → Bool)
    (sign : List Bool → List Bool → ProbComp (List Bool)) (sk : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queried =>
    if adm request.2 then do
      let sig ← sign sk request.2
      return (sig, request.2 :: queried)
    else
      return ([], queried)

/-- Stateful signing/tagging oracle that invokes `sign sk` on every requested message and prepends
the message to the list of queried messages: `signingOracleOn` on every word. -/
abbrev signingOracleOf (sign : List Bool → List Bool → ProbComp (List Bool)) (sk : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  signingOracleOn (fun _ => true) sign sk request

/-- Stateful signing oracle at parameter `n`: it signs an `n`-bit requested message under `sk` and
prepends the message to the list of queried messages, and it answers a request of any other length
with the empty word without signing or recording it: `signingOracleOn` on the `n`-bit words,
instantiated at `S.sign`. -/
def signingOracle (S : SignatureScheme) (n : ℕ) (sk : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  signingOracleOn (·.length == n) S.sign sk request

/-- The EUF-CMA experiment: sample `(pk, sk) ← S.keyGen n`, run the adaptive forger on `(n, pk)`
with oracle access to `S.signingOracle n sk`, which signs `n`-bit messages only, and accept when the
forger outputs a valid signature on an `n`-bit message that was never queried to the signing
oracle. -/
def eufCmaGame (S : SignatureScheme) (adversary : Forger) (n : ℕ) :
    ProbComp Bool := do
  let keys ← S.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (S.signingOracle n keys.2)) (adversary n keys.1)).run []
  let ⟨⟨msg, sig⟩, queried⟩ := out
  return (msg.length == n) && !queried.contains msg &&
    S.verify keys.1 msg sig

/-- The common certificate of the guarded signing oracles: running an oracle-PPT forger against the
oracle that signs a request and prepends it to the log when `admit n msg queried` holds, and
otherwise answers the empty word without recording anything, is uniformly strict PPT whenever the
admission test is decidable in polynomial time. -/
private theorem isPPTOn_run_guardedSigningOracle
    {admit : ℕ → List Bool → List (List Bool) → Bool}
    (hadmit : ComputableInPolyTime
      (fun p : ℕ × List Bool × List (List Bool) => admit p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits (encList encBits))) encBool)
    {sign : List Bool → List Bool → ProbComp (List Bool)}
    (hsign : IsPPTOn (encPair encBits encBits) encBits (fun p => sign p.1 p.2))
    {adversary : Forger} (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encKeyPairInput encForgeryLog
      (fun caller : ℕ × (List Bool × List Bool) =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (fun (request : Unit × List Bool) (queried : List (List Bool)) =>
              if admit caller.1 request.2 queried then do
                let sig ← sign caller.2.2 request.2
                return (sig, request.2 :: queried)
              else
                return ([], queried)))
          (adversary caller.1 caller.2.1)).run []) := by
  obtain ⟨c, d, hlen⟩ := hsign.length_le
  have hcaller := ComputableInPolyTime.fst
    (encPair encUnary (encPair encBits encBits))
    (encPair (encPair (encFinEnum Unit) encBits) (encList encBits))
  have hstate := ComputableInPolyTime.snd
    (encPair encUnary (encPair encBits encBits))
    (encPair (encPair (encFinEnum Unit) encBits) (encList encBits))
  apply hadversary.run_interpret_preprocess (operationEncoding := encFinEnum Unit)
    (prepare := fun caller : ℕ × (List Bool × List Bool) => (caller.1, caller.2.1))
    (initial := fun _ => ([] : List (List Bool)))
    (resources := fun caller query =>
      c * (2 * caller.2.2.length + query.length + 2) ^ d + 2 * query.length + 2)
    ((ComputableInPolyTime.fst _ _).prod (ComputableInPolyTime.snd _ _).fst')
    (IsPPTOn.cond (hadmit.comp (hcaller.fst'.prod (hstate.fst'.snd'.prod hstate.snd')))
      ((hsign.preprocess
        (hcaller.snd'.snd'.prod hstate.fst'.snd')).bind_with
        (ComputableInPolyTime.prod (.snd _ _)
          (ComputableInPolyTime.cons' (hstate.fst'.snd'.comp (.fst _ _))
            (hstate.snd'.comp (.fst _ _)))).isPPTOn)
      ((ComputableInPolyTime.const ([] : List Bool)).prod hstate.snd').isPPTOn)
    (.const []) (fun _ _ => True) (fun _ => trivial)
    (computableInPolyTime_signResources c d)
  intro caller request queried _ result hresult
  split_ifs at hresult
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
    obtain ⟨sig, hsig, rfl⟩ := hresult
    have hsigLen := hlen (caller.2.2, request.2) sig hsig
    simp only [encBits_apply, length_encPair] at hsigLen
    refine ⟨trivial, by lia, ?_⟩
    simp only [encList_cons, List.length_append, length_frame, encBits_apply]
    lia
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
    subst result
    exact ⟨trivial, by simp, by lia⟩

/-- Running an oracle-PPT forger against `signingOracleOn (adm n) sign` is uniformly strict PPT in
the unary security parameter `n`, public/auxiliary input, and secret key, when the message space
`adm` is decidable in polynomial time. -/
@[program_certificate]
theorem isPPTOn_run_signingOracleOn {adm : ℕ → List Bool → Bool}
    (hadm : ComputableInPolyTime (fun p : ℕ × List Bool => adm p.1 p.2)
      (encPair encUnary encBits) encBool)
    {sign : List Bool → List Bool → ProbComp (List Bool)}
    (hsign : IsPPTOn (encPair encBits encBits) encBits (fun p => sign p.1 p.2))
    {adversary : Forger} (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encKeyPairInput encForgeryLog
      (fun caller : ℕ × (List Bool × List Bool) =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (signingOracleOn (adm caller.1) sign caller.2.2))
          (adversary caller.1 caller.2.1)).run []) :=
  isPPTOn_run_guardedSigningOracle (admit := fun n msg _ => adm n msg)
    (hadm.comp ((ComputableInPolyTime.fst _ _).prod (ComputableInPolyTime.snd _ _).fst'))
    hsign hadversary

/-- Running an oracle-PPT forger against `signingOracleOf sign` is uniformly strict PPT in the
unary security parameter, public/auxiliary input, and secret key. -/
@[program_certificate]
theorem isPPTOn_run_signingOracleOf {sign : List Bool → List Bool → ProbComp (List Bool)}
    (hsign : IsPPTOn (encPair encBits encBits) encBits (fun p => sign p.1 p.2))
    {adversary : Forger} (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encKeyPairInput encForgeryLog
      (fun caller : ℕ × (List Bool × List Bool) =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (signingOracleOf sign caller.2.2)) (adversary caller.1 caller.2.1)).run []) :=
  isPPTOn_run_signingOracleOn (adm := fun _ _ => true) (.const true) hsign hadversary

/-- Running an oracle-PPT forger against `S.signingOracle` is uniformly strict PPT in the unary
security parameter, public key, and secret key. -/
@[program_certificate]
theorem isPPTOn_run_signingOracle (S : SignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encKeyPairInput encForgeryLog
      (fun caller : ℕ × (List Bool × List Bool) =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (S.signingOracle caller.1 caller.2.2)) (adversary caller.1 caller.2.1)).run []) :=
  isPPTOn_run_signingOracleOn (adm := fun n m => m.length == n) (by fun_prop)
    S.sign_ppt hadversary

/-- Run the complete EUF-CMA experiment on its unary security parameter for any oracle-PPT
forger. -/
@[program_certificate]
theorem isPPTOn_eufCmaGame (S : SignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encUnary encBool (S.eufCmaGame adversary) :=
  S.keyGen_ppt.bind_with
    ((S.isPPTOn_run_signingOracle hadversary).bind_with
      (computableInPolyTime_eufPost S).isPPTOn)

/-- The EUF-CMA experiment is uniformly strict PPT, independently of unused auxiliary input. -/
@[program_certificate]
theorem isPPT_eufCmaGame (S : SignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPT encBool (fun n _ => S.eufCmaGame adversary n) :=
  ((S.isPPTOn_eufCmaGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Existential unforgeability under adaptive chosen-message attack (EUF-CMA) against uniform
strict oracle-PPT adversaries: [BonehShoup2023], Attack Game 13.1 and Definition 13.2
(pp. 529–530), for the message space of `n`-bit words. Signing queries and the forgery both lie in
that space: the signing oracle answers a query of any other length with the empty word, without
signing or recording it. -/
def EUFCMA (S : SignatureScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (S.eufCmaGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair encBits encBits))

/-- Full EUF-CMA security gives negligible forgery probability for every oracle-PPT forger. -/
theorem EUFCMA.negligible {S : SignatureScheme} (h : S.EUFCMA)
    (adversary : Forger) (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (S.eufCmaGame adversary n))) :=
  Game.Indistinguishable.negligible_succProbability h adversary hadversary

/-- Establish EUF-CMA security by bounding every oracle-PPT forger's success probability. -/
theorem EUFCMA.of_negligible {S : SignatureScheme}
    (h : ∀ adversary, IsOraclePPT (encPair encBits encBits) adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (S.eufCmaGame adversary n)))) :
    S.EUFCMA :=
  Game.Indistinguishable.of_negligible_succProbability h

/-! ### One-time adaptive chosen-message security (`OneTimeEUFCMA`) -/

/-- One-time signing/tagging oracle on the message space `adm`: it answers the first admissible
query using `sign sk` and records it, and it returns the empty word without signing or recording on
every other query. A query outside `adm` is refused without using up the one answer
(`(Signer.restrict _ adm).oneTime`). -/
abbrev oneTimeSigningOracleOn (adm : List Bool → Bool)
    (sign : List Bool → List Bool → ProbComp (List Bool)) (sk : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queried =>
    if adm request.2 && queried.isEmpty then do
      let sig ← sign sk request.2
      return (sig, [request.2])
    else
      return ([], queried)

/-- One-time signing oracle at parameter `n` that answers at most the first `n`-bit signing query
using `S.sign sk` and returns the empty word without signing on any other query:
`oneTimeSigningOracleOn` on the `n`-bit words, instantiated at `S.sign`. -/
def oneTimeSigningOracle (S : SignatureScheme) (n : ℕ) (sk : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  oneTimeSigningOracleOn (·.length == n) S.sign sk request

/-- The one-time EUF-CMA experiment: sample `(pk, sk) ← S.keyGen n`, run the adaptive forger on
`(n, pk)` with oracle access to `S.oneTimeSigningOracle n sk` (which answers at most one signing
query, on an `n`-bit message), and accept when the forger outputs a valid signature on an `n`-bit
message distinct from the queried message (if any). -/
def eufOneTimeGame (S : SignatureScheme) (adversary : Forger) (n : ℕ) :
    ProbComp Bool := do
  let keys ← S.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (S.oneTimeSigningOracle n keys.2)) (adversary n keys.1)).run []
  let ⟨⟨msg, sig⟩, queried⟩ := out
  return (msg.length == n) && !queried.contains msg &&
    S.verify keys.1 msg sig

/-- The one-time oracle on `adm` is the guarded signing oracle whose admission test also asks
for an empty log: on an admitted query the log is empty, so `[msg] = msg :: queried`. -/
private theorem oneTimeSigningOracleOn_eq_guarded (adm : List Bool → Bool)
    (sign : List Bool → List Bool → ProbComp (List Bool)) (sk : List Bool) :
    oneTimeSigningOracleOn adm sign sk = fun request queried =>
      if adm request.2 && queried.isEmpty then do
        let sig ← sign sk request.2
        return (sig, request.2 :: queried)
      else
        return ([], queried) := by
  funext request queried
  cases queried with
  | nil => rfl
  | cons head tail =>
    simp only [oneTimeSigningOracleOn, List.isEmpty_cons, Bool.and_false, Bool.false_eq_true,
      ↓reduceIte]

/-- Running an oracle-PPT forger against `oneTimeSigningOracleOn (adm n) sign` is uniformly strict
PPT in the unary security parameter `n`, public/auxiliary input, and secret key, when the message
space `adm` is decidable in polynomial time. -/
@[program_certificate]
theorem isPPTOn_run_oneTimeSigningOracleOn {adm : ℕ → List Bool → Bool}
    (hadm : ComputableInPolyTime (fun p : ℕ × List Bool => adm p.1 p.2)
      (encPair encUnary encBits) encBool)
    {sign : List Bool → List Bool → ProbComp (List Bool)}
    (hsign : IsPPTOn (encPair encBits encBits) encBits (fun p => sign p.1 p.2))
    {adversary : Forger} (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encKeyPairInput encForgeryLog
      (fun caller : ℕ × (List Bool × List Bool) =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (oneTimeSigningOracleOn (adm caller.1) sign caller.2.2))
          (adversary caller.1 caller.2.1)).run []) := by
  simpa only [oneTimeSigningOracleOn_eq_guarded] using
    isPPTOn_run_guardedSigningOracle (admit := fun n msg queried => adm n msg && queried.isEmpty)
      ((hadm.comp ((ComputableInPolyTime.fst _ _).prod
          (ComputableInPolyTime.snd _ _).fst')).bool_and'
        ((ComputableInPolyTime.listIsEmpty (encA := encBits)).comp
          (ComputableInPolyTime.snd _ _).snd'))
      hsign hadversary

/-- Running an oracle-PPT forger against `oneTimeSigningOracle` is uniformly strict PPT in the
unary security parameter, public key, and secret key. -/
@[program_certificate]
theorem isPPTOn_run_oneTimeSigningOracle (S : SignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encKeyPairInput encForgeryLog
      (fun caller : ℕ × (List Bool × List Bool) =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (S.oneTimeSigningOracle caller.1 caller.2.2))
          (adversary caller.1 caller.2.1)).run []) :=
  isPPTOn_run_oneTimeSigningOracleOn (adm := fun n m => m.length == n)
    (by fun_prop) S.sign_ppt hadversary

/-- Run the complete one-time EUF-CMA experiment on its unary security parameter for any oracle-PPT
forger. -/
@[program_certificate]
theorem isPPTOn_eufOneTimeGame (S : SignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encUnary encBool (S.eufOneTimeGame adversary) :=
  S.keyGen_ppt.bind_with
    ((S.isPPTOn_run_oneTimeSigningOracle hadversary).bind_with
      (computableInPolyTime_eufPost S).isPPTOn)

/-- The one-time EUF-CMA experiment is uniformly strict PPT, independently of unused auxiliary
input. -/
@[program_certificate]
theorem isPPT_eufOneTimeGame (S : SignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPT encBool (fun n _ => S.eufOneTimeGame adversary n) :=
  ((S.isPPTOn_eufOneTimeGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Existential unforgeability under one-time adaptive chosen-message attack against uniform strict
oracle-PPT adversaries: a secure one-time signature in the sense of [BonehShoup2023],
Definition 14.1 (p. 583), that is, Attack Game 13.1 (pp. 529–530) with at most one signing query,
for the message space of `n`-bit words. Signing queries and the forgery both lie in that space: the
oracle answers only the first `n`-bit query, and it answers a query of any other length with the
empty word without signing or recording it, so such a query does not use up the one answer. -/
def OneTimeEUFCMA (S : SignatureScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (S.eufOneTimeGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair encBits encBits))

/-- One-time EUF-CMA security gives negligible forgery probability for every oracle-PPT forger. -/
theorem OneTimeEUFCMA.negligible {S : SignatureScheme} (h : S.OneTimeEUFCMA)
    (adversary : Forger) (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (S.eufOneTimeGame adversary n))) :=
  Game.Indistinguishable.negligible_succProbability h adversary hadversary

/-- Establish one-time EUF-CMA security by bounding every oracle-PPT forger's success
probability. -/
theorem OneTimeEUFCMA.of_negligible {S : SignatureScheme}
    (h : ∀ adversary, IsOraclePPT (encPair encBits encBits) adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (S.eufOneTimeGame adversary n)))) :
    S.OneTimeEUFCMA :=
  Game.Indistinguishable.of_negligible_succProbability h

/-- Starting from the empty query log, `oneTimeSigningOracle` records at most one queried
message. -/
theorem length_le_one_of_mem_support_run_oneTimeSigningOracle (S : SignatureScheme) {α : Type}
    (n : ℕ) (sk : List Bool) (prog : WordOracleComp Unit α) {result : α}
    {queried : List (List Bool)}
    (h : (result, queried) ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun q s => ProbComp.eval (S.oneTimeSigningOracle n sk q s))) prog).run []).support) :
    queried.length ≤ 1 := by
  rw [← ProbOracleComp.runWith_eq_run_interpret] at h
  refine ProbOracleComp.runWith_invariant
    (fun q s => ProbComp.eval (S.oneTimeSigningOracle n sk q s))
    (fun s => s.length ≤ 1) ?_ prog [] (by simp) result queried h
  intro ⟨⟨⟩, req⟩ s hs a s' hmem
  rw [oneTimeSigningOracle, oneTimeSigningOracleOn] at hmem
  split_ifs at hmem with hempty
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hmem
    obtain ⟨_, _, heq⟩ := hmem
    cases heq
    simp
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hmem
    exact (Prod.mk.inj hmem).2 ▸ hs

private theorem run_oneTimeSigningOracle_apply_eq_zero_of_not_agree (S : SignatureScheme)
    {α : Type} (n : ℕ) (sk : List Bool) {agree : List Bool → Prop} (prog : WordOracleComp Unit α)
    {s queried' : List (List Bool)} (hs : ¬ ∀ r ∈ s, agree r) (hq' : ∀ r ∈ queried', agree r)
    (a : α) :
    (ProbOracleComp.runWith (fun q s => ProbComp.eval (S.oneTimeSigningOracle n sk q s)) prog s)
      (a, queried') = 0 := by
  rw [PMF.apply_eq_zero_iff]
  intro hmem
  refine ProbOracleComp.runWith_invariant
    (fun q s => ProbComp.eval (S.oneTimeSigningOracle n sk q s))
    (fun state => ¬ ∀ r ∈ state, agree r) ?_ prog s hs a queried' hmem hq'
  intro ⟨⟨⟩, req⟩ state hstate val next hnext
  rw [oneTimeSigningOracle, oneTimeSigningOracleOn] at hnext
  split_ifs at hnext with hempty
  · rw [Bool.and_eq_true, List.isEmpty_iff] at hempty
    obtain ⟨-, rfl⟩ := hempty
    exact absurd (fun _ h => nomatch h) hstate
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hnext
    exact (Prod.mk.inj hnext).2 ▸ hstate

/-- If `S.sign sk₁` and `S.sign sk₂` agree on all requests satisfying `agree`, then running any
adaptive program against `oneTimeSigningOracle` under `sk₁` and `sk₂` assigns the same probability
to every outcome `(a, queried')` whose recorded query log satisfies `agree`. -/
theorem run_oneTimeSigningOracle_apply_eq_of_agree (S : SignatureScheme) {α : Type} (n : ℕ)
    (sk₁ sk₂ : List Bool) {agree : List Bool → Prop}
    (hagree : ∀ req, agree req → S.sign sk₁ req = S.sign sk₂ req)
    (prog : WordOracleComp Unit α) (s : List (List Bool)) (a : α)
    (queried' : List (List Bool)) (hq' : ∀ r ∈ queried', agree r) :
    ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun q s => ProbComp.eval (S.oneTimeSigningOracle n sk₁ q s))) prog).run s)
        (a, queried') =
    ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun q s => ProbComp.eval (S.oneTimeSigningOracle n sk₂ q s))) prog).run s)
      (a, queried') := by
  induction prog using PFunctor.FreeM.induction generalizing s with
  | pure x => rfl
  | lift_bind q cont ih =>
    change (((OracleComp.interpret (m := StateT (List (List Bool)) PMF) _
        (OracleComp.query q >>= cont)).run s) (a, queried')) =
      (((OracleComp.interpret (m := StateT (List (List Bool)) PMF) _
        (OracleComp.query q >>= cont)).run s) (a, queried'))
    simp only [OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
      PMF.monad_bind_eq_bind]
    cases q with
    | inl k =>
      change (((ProbComp.unifOracle k).map (·, s)).bind _) (a, queried') =
        (((ProbComp.unifOracle k).map (·, s)).bind _) (a, queried')
      simp only [PMF.bind_map, Function.comp_def, PMF.bind_apply]
      exact tsum_congr fun r => congrArg _ (ih r s)
    | inr req =>
      rcases req with ⟨⟨⟩, msg⟩
      change ((ProbComp.eval (S.oneTimeSigningOracle n sk₁ ((), msg) s)).bind _) (a, queried') =
        ((ProbComp.eval (S.oneTimeSigningOracle n sk₂ ((), msg) s)).bind _) (a, queried')
      rw [oneTimeSigningOracle, oneTimeSigningOracle, oneTimeSigningOracleOn,
        oneTimeSigningOracleOn]
      split_ifs with hempty
      · by_cases hmsg : agree msg
        · rw [hagree msg hmsg]
          simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind,
            PMF.bind_apply]
          exact tsum_congr fun sig => congrArg _ (ih sig [msg])
        · have hnot : ¬ ∀ r ∈ [msg], agree r := fun h => hmsg (h msg (List.mem_singleton_self _))
          have hzero (sk : List Bool) (sig : List Bool) :
              ((OracleComp.interpret
                (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
                  (fun q s => ProbComp.eval (S.oneTimeSigningOracle n sk q s)))
                (cont sig)).run [msg]) (a, queried') = 0 :=
            by
              rw [← ProbOracleComp.runWith_eq_run_interpret]
              exact run_oneTimeSigningOracle_apply_eq_zero_of_not_agree
                S n sk (cont sig) hnot hq' a
          simp [PMF.bind_apply, hzero]
      · simp only [ProbComp.eval_pure, PMF.pure_bind]
        exact ih [] s

/-! ### Reduction from one-time EUF-CMA to full EUF-CMA -/

/-- Open stateful handler at parameter `n` that forwards at most the first signing request in the
message space `adm n` to the external signing oracle (truncating the reply to
`bound n msg.length`), and answers every other request with `[]` itself. A request outside the
message space does not use up the one forwarded query. -/
def oneTimeFilterHandler (adm : ℕ → List Bool → Bool) (bound : ℕ → ℕ → ℕ)
    (caller : ℕ × List Bool) (request : Unit × List Bool) :
    StateT Bool (WordOracleComp Unit) (List Bool) :=
  fun alreadyQueried =>
    if alreadyQueried then
      pure ([], true)
    else if adm caller.1 request.2 then
      (fun sig => (sig, true)) <$> (List.take (bound caller.1 request.2.length) <$>
        ProbOracleComp.query ((), request.2))
    else
      pure ([], false)

/-- Wrap an adaptive forger so that it issues at most one external signing query, on a message in
the message space `adm n`. -/
def limitToOneQuery (adm : ℕ → List Bool → Bool) (bound : ℕ → ℕ → ℕ) (adversary : Forger) :
    Forger :=
  fun n pk =>
    Prod.fst <$> (OracleComp.interpret
      (OracleComp.sumHandler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (oneTimeFilterHandler adm bound (n, pk)))
      (adversary n pk)).run false

theorem isOraclePPT_limitToOneQuery {adm : ℕ → List Bool → Bool}
    (hadm : ComputableInPolyTime (fun p : ℕ × List Bool => adm p.1 p.2)
      (encPair encUnary encBits) encBool)
    {bound : ℕ → ℕ → ℕ}
    (hbound : ComputableInPolyTime (fun p : ℕ × ℕ => bound p.1 p.2)
      (encPair encUnary encUnary) encUnary)
    {adversary : Forger} (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPT (encPair encBits encBits) (limitToOneQuery adm bound adversary) := by
  have hcaller := ComputableInPolyTime.fst (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Unit) encBits) encBool)
  have hstate := ComputableInPolyTime.snd (encPair encUnary encBits)
    (encPair (encPair (encFinEnum Unit) encBits) encBool)
  have hreq := hstate.fst'.snd'
  have hrun : IsOraclePPTOn (encPair encUnary encBits)
      (encPair (encPair encBits encBits) encBool)
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (oneTimeFilterHandler adm bound caller))
          (adversary caller.1 caller.2)).run false) := by
    apply hadversary.run_interpret_preprocess_open (operationEncoding := encFinEnum Unit)
      (handler := oneTimeFilterHandler adm bound)
      (prepare := id)
      (initial := fun _ => false)
      (resources := fun caller query => bound caller.1 query.length + 1)
      ComputableInPolyTime.id'
      (IsOraclePPTOn.cond hstate.snd'
        ((ComputableInPolyTime.const ([], true)).isOraclePPTOn (Operation := Unit))
        (IsOraclePPTOn.cond (hadm.comp' (hcaller.fst'.prod hreq))
          ((IsOraclePPTOn.query_take () hreq
            (hbound.comp' (hcaller.fst'.prod (ComputableInPolyTime.length_bits.comp' hreq)))).map
            (ComputableInPolyTime.id'.prod (.const true)))
          ((ComputableInPolyTime.const ([], false)).isOraclePPTOn (Operation := Unit))))
      (.const false)
      (fun _ _ => True) (fun _ => trivial)
      (ComputableInPolyTime.unary_add.comp'
        ((hbound.comp' ((ComputableInPolyTime.fst (encPair encUnary encBits) encBits).fst'.prod
          (ComputableInPolyTime.length_bits.comp'
            (ComputableInPolyTime.snd (encPair encUnary encBits) encBits)))).prod
          (.const 1)))
    intro caller request state _ result hresult
    unfold oneTimeFilterHandler at hresult
    split_ifs at hresult with hstate hadmit
    · have heq := OracleComp.eq_of_mem_supportWith_pure hresult
      subst heq
      simp [encBool_apply]
    · obtain ⟨sig, hsig, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hresult
      obtain ⟨rawSig, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hsig
      refine ⟨trivial, (List.length_take_le _ _).trans (by lia), ?_⟩
      simp [encBool_apply]
    · have heq := OracleComp.eq_of_mem_supportWith_pure hresult
      subst heq
      simp [encBool_apply]
  exact (hrun.map (ComputableInPolyTime.fst _ _)).isOraclePPT

/-- Running an adaptive program filtered through `oneTimeFilterHandler adm` against
`signingOracleOn (adm n) sign` produces the same distribution as running it against
`oneTimeSigningOracleOn (adm n) sign` whenever all outputs of `sign sk msg` have length at most
`bound n msg.length`. -/
theorem run_limitToOneQuery_eq_oneTimeSigningOracleOn (adm : ℕ → List Bool → Bool)
    (sign : List Bool → List Bool → ProbComp (List Bool))
    (bound : ℕ → ℕ → ℕ) (n : ℕ) (pk sk : List Bool)
    (hbound : ∀ msg sig, sig ∈ (ProbComp.eval (sign sk msg)).support →
      sig.length ≤ bound n msg.length)
    (prog : WordOracleComp Unit (List Bool × List Bool)) :
    ProbComp.eval (Prod.map Prod.fst id <$> ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (signingOracleOn (adm n) sign sk))
      ((OracleComp.interpret
        (OracleComp.sumHandler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (oneTimeFilterHandler adm bound (n, pk)))
        prog).run false)).run [])) =
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (oneTimeSigningOracleOn (adm n) sign sk)) prog).run []) := by
  rw [ProbComp.eval_map, ProbOracleComp.eval_run_interpret_eq_runWith,
    ProbOracleComp.eval_run_interpret_eq_runWith]
  -- Reconstruct the filter flag from the query log, so no state invariant is needed.
  refine (congrArg (PMF.map _) (ProbOracleComp.runWith_run_interpret_map
    (oneTimeFilterHandler adm bound (n, pk))
    (fun q s => ProbComp.eval (signingOracleOn (adm n) sign sk q s))
    (fun q s => ProbComp.eval (oneTimeSigningOracleOn (adm n) sign sk q s))
    (fun queried => !queried.isEmpty) (fun queried => queried) (by
      intro ⟨⟨⟩, msg⟩ queried
      rw [ProbOracleComp.runWith_eq_run_interpret]
      change _ = ((OracleComp.interpret (m := StateT (List (List Bool)) PMF) _
        (oneTimeFilterHandler adm bound (n, pk) ((), msg) (!queried.isEmpty))).run queried).map _
      cases queried with
      | nil =>
        by_cases hadm : adm n msg = true
        · simp only [oneTimeSigningOracleOn, hadm, List.isEmpty_nil, Bool.and_self, ↓reduceIte,
            Bool.not_true, oneTimeFilterHandler, Bool.false_eq_true, Functor.map_map,
            OracleComp.interpret_map, StateT.run_map, ProbOracleComp.interpret_query,
            PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def, signingOracleOn,
            ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind]
          simp only [StateT.run, PMF.map_bind]
          refine PMF.bind_congr_on_support _ _ _ fun sig hsig => ?_
          simp [List.take_of_length_le (hbound msg sig hsig)]
        · simp [oneTimeSigningOracleOn, oneTimeFilterHandler, hadm, OracleComp.interpret_pure,
            StateT.run_pure, ProbComp.eval_pure]
      | cons head tail =>
        simp [oneTimeSigningOracleOn, oneTimeFilterHandler, OracleComp.interpret_pure,
          StateT.run_pure, ProbComp.eval_pure])
    prog [])).trans ?_
  rw [PMF.map_comp]
  exact (congrArg (PMF.map · _) (funext fun _ => rfl : _ = id)).trans (PMF.map_id _)

/-! ### Refusing signing queries outside the message space in the forger -/

/-- The forger that runs `adversary` at parameter `n`, forwards each signing request in the message
space `adm n` to the external signing oracle (truncating the reply to `bound n msg.length`), and
answers every other request with `[]` itself, as the signing oracle on `adm n` does. Against the
signing oracle on every word it plays the game of `adversary` against the oracle on `adm n`
(`run_restrictQueries_eq_signingOracleOn`), so a bound proved for the unrestricted oracle transfers
to the restricted one. -/
def restrictQueries (adm : ℕ → List Bool → Bool) (bound : ℕ → ℕ → ℕ) (adversary : Forger) :
    Forger := fun n pk =>
  OracleComp.interpret
    (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
      (fun request : Unit × List Bool =>
        if adm n request.2 then
          List.take (bound n request.2.length) <$> ProbOracleComp.query ((), request.2)
        else pure []))
    (adversary n pk)

theorem isOraclePPT_restrictQueries {adm : ℕ → List Bool → Bool}
    (hadm : ComputableInPolyTime (fun p : ℕ × List Bool => adm p.1 p.2)
      (encPair encUnary encBits) encBool)
    {bound : ℕ → ℕ → ℕ}
    (hbound : ComputableInPolyTime (fun p : ℕ × ℕ => bound p.1 p.2)
      (encPair encUnary encUnary) encUnary)
    {adversary : Forger} (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPT (encPair encBits encBits) (restrictQueries adm bound adversary) := by
  have hcaller := ComputableInPolyTime.fst (encPair encUnary encBits)
    (encPair (encFinEnum Unit) encBits)
  have hreq := (ComputableInPolyTime.snd (encPair encUnary encBits)
    (encPair (encFinEnum Unit) encBits)).snd'
  refine (hadversary.on.interpret_preprocess_open' (operationEncoding := encFinEnum Unit)
    (handler := fun (caller : ℕ × List Bool) (request : Unit × List Bool) =>
      if adm caller.1 request.2 then
        List.take (bound caller.1 request.2.length) <$> ProbOracleComp.query ((), request.2)
      else pure [])
    (prepare := id) (resources := fun caller w => bound caller.1 w.length)
    ComputableInPolyTime.id'
    (IsOraclePPTOn.cond (hadm.comp' (hcaller.fst'.prod hreq))
      (IsOraclePPTOn.query_take () hreq
        (hbound.comp' (hcaller.fst'.prod (ComputableInPolyTime.length_bits.comp' hreq))))
      ((ComputableInPolyTime.const ([] : List Bool)).isOraclePPTOn (Operation := Unit)))
    (hbound.comp' ((ComputableInPolyTime.fst (encPair encUnary encBits) encBits).fst'.prod
      (ComputableInPolyTime.length_bits.comp'
        (ComputableInPolyTime.snd (encPair encUnary encBits) encBits))))
    fun caller request reply hreply => ?_).isOraclePPT
  split_ifs at hreply
  · obtain ⟨raw, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
    exact List.length_take_le _ _
  · rw [OracleComp.eq_of_mem_supportWith_pure hreply]
    exact Nat.zero_le _

/-- Running `restrictQueries adm bound adversary` against the signing oracle on every word is
running `adversary` against the signing oracle on `adm n`, whenever every output of `sign sk msg`
has length at most `bound n msg.length`. -/
theorem run_restrictQueries_eq_signingOracleOn (adm : ℕ → List Bool → Bool)
    (sign : List Bool → List Bool → ProbComp (List Bool)) (bound : ℕ → ℕ → ℕ) (n : ℕ)
    (pk sk : List Bool)
    (hbound : ∀ msg sig, sig ∈ (ProbComp.eval (sign sk msg)).support →
      sig.length ≤ bound n msg.length)
    (adversary : Forger) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (signingOracleOf sign sk)) (restrictQueries adm bound adversary n pk)).run []) =
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
        (signingOracleOn (adm n) sign sk)) (adversary n pk)).run []) := by
  rw [ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.eval_run_interpret_eq_runWith,
    restrictQueries, ProbOracleComp.runWith_interpret_sumHandler]
  congr 1
  funext request queried
  by_cases hadm : adm n request.2 = true
  · simp only [hadm, ↓reduceIte, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
      signingOracleOf, signingOracleOn, ProbComp.eval_bind, ProbComp.eval_pure]
    rw [PMF.map_bind]
    refine PMF.bind_congr_on_support _ _ _ fun sig hsig => ?_
    simp [List.take_of_length_le (hbound _ sig hsig)]
  · simp [hadm, signingOracleOn]

/-- Full EUF-CMA security implies one-time EUF-CMA security. -/
theorem EUFCMA.oneTimeEUFCMA {S : SignatureScheme} (h : S.EUFCMA) : S.OneTimeEUFCMA := by
  obtain ⟨bound, hbound_poly, hbound⟩ := S.exists_sign_length_bound
  refine h.of_succProbability_reduction (limitToOneQuery (fun n m => m.length == n) bound)
    (fun _ => isOraclePPT_limitToOneQuery (by fun_prop) hbound_poly)
    fun adversary _ n => ?_
  refine le_of_eq (congrArg Game.succProbability ?_)
  simp only [eufOneTimeGame, eufCmaGame, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_
  have hrun := run_limitToOneQuery_eq_oneTimeSigningOracleOn (fun n m => m.length == n) S.sign
    bound n keys.1 keys.2 (hbound n keys hkeys) (adversary n keys.1)
  dsimp only [limitToOneQuery]
  rw [OracleComp.interpret_map, StateT.run_map]
  exact (congrArg (fun p : PMF ((List Bool × List Bool) × List (List Bool)) =>
    p.bind fun x => PMF.pure
      ((x.1.1.length == n) && !x.2.contains x.1.1 && S.verify keys.1 x.1.1 x.1.2)) hrun).symm

end SignatureScheme

end Cslib.Crypto
