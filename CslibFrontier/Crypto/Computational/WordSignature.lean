/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Signature
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PPT

/-!
# Stateless digital signature schemes on arbitrary-length bit words

`SignatureScheme` fixes the message space at security parameter `n` to exact `n`-bit words
(`msg.length = n`). Mirroring `Encryption.WordINDCPA`, this module defines uniform stateless
digital signature schemes (`WordSignatureScheme`) whose signing algorithm, verification algorithm,
and adaptive EUF-CMA experiment (`WordSignatureScheme.eufCmaGame`, `WordSignatureScheme.EUFCMA`)
operate on **unrestricted bit strings** (`msg : List Bool`), with no message-length restriction at
any security parameter:

* **Completeness (`WordSignatureScheme.verify_sign`)**: for every security parameter `n`, supported
  key pair `(pk, sk) ∈ (ProbComp.eval (S.keyGen n)).support`, arbitrary bit string
  `msg : List Bool`, and signature `sig ∈ (ProbComp.eval (S.sign sk msg)).support`,
  `S.verify pk msg sig = true`.
* **Adaptive chosen-message security (`WordSignatureScheme.eufCmaGame`,
  `WordSignatureScheme.EUFCMA`)**: an adaptive `IsOraclePPT` forger receives unary `n` and `pk`,
  queries `S.signingOracle sk` on arbitrary messages, and wins by outputting any valid `(msg, sig)`
  pair whose message `msg` was never queried to the signing oracle
  (`[GoldwasserMicaliRivest1988]`, Section 3; `[Rompel1990]`; `[BonehShoup2023]`, Section 13.1,
  Attack Game 13.1 and Definition 13.1).
* **Restriction to `n`-bit messages (`WordSignatureScheme.toSignatureScheme`,
  `WordSignatureScheme.EUFCMA.toSignatureScheme`)**: every `WordSignatureScheme` restricts to a
  `SignatureScheme` with the same `keyGen`, `sign`, and `verify`. `SignatureScheme.eufCmaGame`
  signs and accepts only `n`-bit messages, so a forger in it succeeds at most as often as the
  forger that refuses the other signing queries itself (`SignatureScheme.restrictQueries`) does in
  `WordSignatureScheme.eufCmaGame`, and `WordSignatureScheme.EUFCMA` implies
  `SignatureScheme.EUFCMA`.

## Main definitions

* `Cslib.Crypto.WordSignatureScheme`: uniform stateless digital signature scheme on arbitrary
  `List Bool` messages.
* `Cslib.Crypto.WordSignatureScheme.signingOracle`, `Cslib.Crypto.WordSignatureScheme.eufCmaGame`,
  `Cslib.Crypto.WordSignatureScheme.EUFCMA`: adaptive chosen-message security experiment and
  security predicate for unrestricted `List Bool` messages.
* `Cslib.Crypto.WordSignatureScheme.toSignatureScheme`: restriction of a `WordSignatureScheme` to
  `SignatureScheme`'s `n`-bit message interface.

## Main results

* `Cslib.Crypto.WordSignatureScheme.isPPTOn_run_signingOracle`,
  `Cslib.Crypto.WordSignatureScheme.isPPTOn_eufCmaGame`,
  `Cslib.Crypto.WordSignatureScheme.isPPT_eufCmaGame`: uniform strict PPT certificates for the
  signing-oracle execution and full EUF-CMA experiment, in the plain polynomial-time calculus. The
  execution certificate is `SignatureScheme.isPPTOn_run_signingOracleOf` applied to `sign_ppt`.
* `Cslib.Crypto.WordSignatureScheme.succProbability_toSignatureScheme_eufCmaGame_le`,
  `Cslib.Crypto.WordSignatureScheme.EUFCMA.toSignatureScheme`: `WordSignatureScheme.EUFCMA` implies
  `SignatureScheme.EUFCMA` on the induced `n`-bit `SignatureScheme`.

## References

* [S. Goldwasser, S. Micali, R. L. Rivest, *A Digital Signature Scheme Secure Against Adaptive
  Chosen-Message Attacks*][GoldwasserMicaliRivest1988]
* [J. Rompel, *One-Way Functions are Necessary and Sufficient for Secure Signatures*][Rompel1990]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 13.1 (Attack Game 13.1 and Definition 13.1) and Section 13.2.1.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- A uniform stateless digital signature scheme on arbitrary bit strings (`List Bool`), with
strict polynomial-time key generation and signing, deterministic polynomial-time verification, and
perfect completeness on all supported key pairs, arbitrary `List Bool` messages, and signatures. -/
structure WordSignatureScheme where
  /-- Sample a public verification key and secret signing key `(pk, sk)` at unary parameter `n`. -/
  keyGen : ℕ → ProbComp (List Bool × List Bool)
  /-- Sign an arbitrary bit-string message `msg` using the secret signing key `sk`. -/
  sign : List Bool → List Bool → ProbComp (List Bool)
  /-- Deterministically verify a candidate signature `sig` on `msg` under public key `pk`. -/
  verify : List Bool → List Bool → List Bool → Bool
  /-- Key generation is uniformly strict PPT in the unary security parameter. -/
  keyGen_ppt : IsPPTOn encUnary (encPair encBits encBits) keyGen
  /-- Signing is uniformly strict PPT in the encoded secret key and message. -/
  sign_ppt : IsPPTOn (encPair encBits encBits) encBits (fun ⟨sk, msg⟩ => sign sk msg)
  /-- Verification is computable in plain polynomial time on `(pk, msg, sig)`. -/
  verify_polyTime : ComputableInPolyTime
    (fun ⟨pk, msg, sig⟩ => verify pk msg sig)
    (encPair encBits (encPair encBits encBits)) encBool
  /-- Every signature produced by `sign` on any bit-string message under a supported key pair at
  security parameter `n` is accepted by `verify`. -/
  verify_sign : ∀ n pk sk, (pk, sk) ∈ (ProbComp.eval (keyGen n)).support →
    ∀ msg sig, sig ∈ (ProbComp.eval (sign sk msg)).support →
    verify pk msg sig = true

namespace WordSignatureScheme

attribute [program_certificate] keyGen_ppt sign_ppt verify_polyTime

@[program_certificate, fun_prop]
theorem isPPTOn_keyGen_comp (S : WordSignatureScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableInPolyTime n encIn encUnary) :
    IsPPTOn encIn (encPair encBits encBits) (fun a => S.keyGen (n a)) :=
  S.keyGen_ppt.preprocess hn

@[program_certificate, fun_prop]
theorem isPPTOn_sign_comp (S : WordSignatureScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {sk msg : γ → List Bool}
    (hsk : ComputableInPolyTime sk encIn encBits)
    (hmsg : ComputableInPolyTime msg encIn encBits) :
    IsPPTOn encIn encBits (fun a => S.sign (sk a) (msg a)) :=
  S.sign_ppt.preprocess (hsk.prod hmsg)

@[program_certificate, fun_prop]
theorem computableInPolyTime_verify_comp (S : WordSignatureScheme)
    {γ : Type} {encIn : γ ↪ List Bool} {pk msg sig : γ → List Bool}
    (hpk : ComputableInPolyTime pk encIn encBits)
    (hmsg : ComputableInPolyTime msg encIn encBits)
    (hsig : ComputableInPolyTime sig encIn encBits) :
    ComputableInPolyTime (fun a => S.verify (pk a) (msg a) (sig a)) encIn encBool :=
  S.verify_polyTime.comp (hpk.prod (hmsg.prod hsig))

/-! ### Adaptive chosen-message security on unrestricted bit words (`EUFCMA`) -/

/-- Stateful signing oracle that signs any requested `List Bool` message under `sk` and prepends
the message to the list of queried messages: `SignatureScheme.signingOracleOf` instantiated at
`S.sign`. -/
def signingOracle (S : WordSignatureScheme) (sk : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  SignatureScheme.signingOracleOf S.sign sk request

/-- The unrestricted-message EUF-CMA experiment: sample `(pk, sk) ← S.keyGen n`, run the adaptive
forger on `(n, pk)` with oracle access to `S.signingOracle sk`, and accept when the forger outputs
a valid signature on any `List Bool` message that was never queried to the signing oracle. -/
def eufCmaGame (S : WordSignatureScheme) (adversary : Forger) (n : ℕ) :
    ProbComp Bool := do
  let keys ← S.keyGen n
  let out ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (S.signingOracle keys.2)) (adversary n keys.1)).run []
  let (msg, sig) := out.1
  return !out.2.contains msg && S.verify keys.1 msg sig

/-- Running an oracle-PPT forger against `signingOracle` is uniformly strict PPT in `(n, (pk, sk))`.
-/
@[program_certificate]
theorem isPPTOn_run_signingOracle (S : WordSignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn (encPair encUnary (encPair encBits encBits))
      (encPair (encPair encBits encBits) (encList encBits))
      (fun ⟨n, pk, sk⟩ =>
        (OracleComp.interpret
          (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
            (S.signingOracle sk)) (adversary n pk)).run []) :=
  SignatureScheme.isPPTOn_run_signingOracleOf S.sign_ppt hadversary

/-- Run the complete unrestricted-message EUF-CMA experiment on its unary security parameter for
any oracle-PPT forger. -/
@[program_certificate]
theorem isPPTOn_eufCmaGame (S : WordSignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encUnary encBool (S.eufCmaGame adversary) := by
  let P := (ℕ × (List Bool × List Bool)) × ((List Bool × List Bool) × List (List Bool))
  let encP : P ↪ List Bool :=
    encPair (encPair encUnary (encPair encBits encBits))
      (encPair (encPair encBits encBits) (encList encBits))
  have hfresh : ComputableInPolyTime (fun pair : P => !pair.2.2.contains pair.2.1.1)
      encP encBool := by
    refine (ComputableInPolyTime.decide_not (ComputableInPolyTime.decide_mem
      (encIn := encP) (encA := encBits) (list := fun p : P => p.2.2)
      (value := fun p : P => p.2.1.1) (by fun_prop) (by fun_prop))).of_enc_eq fun _ => ?_
    simp
  exact S.keyGen_ppt.bind_with ((S.isPPTOn_run_signingOracle hadversary).bind_with
    (hfresh.bool_and' (by fun_prop)).isPPTOn)

/-- The unrestricted-message EUF-CMA experiment is uniformly strict PPT, independently of unused
auxiliary input. -/
@[program_certificate]
theorem isPPT_eufCmaGame (S : WordSignatureScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPT encBool (fun n _ => S.eufCmaGame adversary n) :=
  ((S.isPPTOn_eufCmaGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Existential unforgeability under adaptive chosen-message attack (`EUFCMA`) on arbitrary
`List Bool` messages against uniform strict oracle-PPT adversaries: [BonehShoup2023], Attack
Game 13.1 and Definition 13.2 (pp. 529–530), with every bit string a message. The source's message
space is a finite set of words of polynomially bounded length; a strict PPT forger queries and
outputs only words of polynomially bounded length, so this is security on every such message space
at once. -/
def EUFCMA (S : WordSignatureScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (S.eufCmaGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair encBits encBits))

/-- Unrestricted-message EUF-CMA security gives negligible forgery probability for every oracle-PPT
forger. -/
theorem EUFCMA.negligible {S : WordSignatureScheme} (h : S.EUFCMA)
    (adversary : Forger) (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (S.eufCmaGame adversary n))) := by
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Establish unrestricted-message EUF-CMA security by bounding every oracle-PPT forger's success
probability. -/
theorem EUFCMA.of_negligible {S : WordSignatureScheme}
    (h : ∀ adversary, IsOraclePPT (encPair encBits encBits) adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (S.eufCmaGame adversary n)))) :
    S.EUFCMA := by
  intro adversary hadversary
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-! ### Restriction to fixed-length `SignatureScheme` -/

/-- Restrict a `WordSignatureScheme` to `SignatureScheme`'s `n`-bit message interface. -/
def toSignatureScheme (S : WordSignatureScheme) : SignatureScheme where
  keyGen := S.keyGen
  sign := S.sign
  verify := S.verify
  keyGen_ppt := S.keyGen_ppt
  sign_ppt := S.sign_ppt
  verify_polyTime := S.verify_polyTime
  verify_sign n keys hkeys msg _ sig hsig := S.verify_sign n keys.1 keys.2 hkeys msg sig hsig

@[simp] theorem toSignatureScheme_keyGen (S : WordSignatureScheme) :
    S.toSignatureScheme.keyGen = S.keyGen := rfl

@[simp] theorem toSignatureScheme_sign (S : WordSignatureScheme) :
    S.toSignatureScheme.sign = S.sign := rfl

@[simp] theorem toSignatureScheme_verify (S : WordSignatureScheme) :
    S.toSignatureScheme.verify = S.verify := rfl

/-- A forger against `S.toSignatureScheme`, whose signing oracle signs `n`-bit messages only and
which also checks `msg.length == n`, succeeds at most as often as the forger that refuses the other
queries itself (`SignatureScheme.restrictQueries`) succeeds against `S`, whenever `bound` bounds
signature lengths. -/
theorem succProbability_toSignatureScheme_eufCmaGame_le (S : WordSignatureScheme)
    {bound : ℕ → ℕ → ℕ}
    (hbound : ∀ n, ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ msg sig,
      sig ∈ (ProbComp.eval (S.sign keys.2 msg)).support → sig.length ≤ bound n msg.length)
    (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (S.toSignatureScheme.eufCmaGame adversary n)) ≤
      Game.succProbability (ProbComp.eval (S.eufCmaGame
        (SignatureScheme.restrictQueries (fun n m => m.length == n) bound adversary) n)) := by
  apply Game.succProbability_mono
  simp only [SignatureScheme.eufCmaGame, eufCmaGame, toSignatureScheme_keyGen,
    toSignatureScheme_verify, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_apply_mono_on_support _ _ fun keys hkeys => ?_
  rw [show S.signingOracle keys.2 = SignatureScheme.signingOracleOf S.sign keys.2 from rfl,
    SignatureScheme.run_restrictQueries_eq_signingOracleOn _ S.sign bound n keys.1 keys.2
      (hbound n keys hkeys)]
  refine PMF.bind_apply_mono_on_support _ _ fun ⟨⟨msg, sig⟩, queried⟩ _ => ?_
  dsimp only
  cases msg.length == n <;> simp

/-- Unrestricted-message `EUFCMA` security implies `SignatureScheme.EUFCMA` security on `n`-bit
messages. -/
theorem EUFCMA.toSignatureScheme {S : WordSignatureScheme} (h : S.EUFCMA) :
    S.toSignatureScheme.EUFCMA := by
  obtain ⟨bound, hbound_poly, hbound⟩ := S.toSignatureScheme.exists_sign_length_bound
  apply SignatureScheme.EUFCMA.of_negligible
  intro adversary hadversary
  exact negligible_of_le (h.negligible _ (SignatureScheme.isOraclePPT_restrictQueries
      (adm := fun n m => m.length == n) (by fun_prop)
      hbound_poly hadversary))
    (S.succProbability_toSignatureScheme_eufCmaGame_le hbound adversary)

end WordSignatureScheme

end Cslib.Crypto
