/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.FIPS204ResponseBinding
public import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import Batteries.Data.Vector.Lemmas
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Vector

/-!
# Definitions of FIPS 204 signing and the strong chosen-message forgery experiment

[FIPS 204][NISTFIPS204], Algorithms 2, 6 and 7. The external signer accepts the encoded
private key, a bit-string message, a byte context and 32 bytes of randomness. A zero randomness
string selects deterministic signing. The bounded loop uses the 814-attempt option of Appendix C.
The adaptive strong-unforgeability experiment draws fresh hedging randomness for each signature
and records the context, message and exact bytes of every successful reply. Its sole external
service is signing. The `sufCmaGame` specialization evaluates FIPS 202 SHAKE in both signing and
verification. Its zero-signing-query lemma recovers the byte-level key-only experiment.

`verify_of_sign` proves that every successful signature under a generated key passes
Algorithm 3. On a fresh verifying triple whose digest occurs in the log, the extractor
finds a previous reply and computes two colliding SHAKE256 inputs or an integer MSIS vector.

`refreshFirstRequest_sufCmaGame` gives a classical resampling identity for the first request
and its first internal attempt. The requester may use the known SHAKE256 prefix at every raw
address. The signer consumes the refreshed Algorithm 29 bytes and uses the resulting table
through its retries, later signing requests and final verification.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability

/-- Bytes consumed by Algorithm 34 for one mask polynomial, 576 at ML-DSA-44 and
640 at ML-DSA-65 and ML-DSA-87. -/
abbrev maskPolyBytes (s : Level) := 32 * (s.params.γ₁.log2 + 1)

private def expandMaskFrom (s : Level) (κ : ℕ) (read : ℕ → List Byte) :
    Vector (Vector (ZMod 8380417) 256) s.params.ℓ :=
  Vector.ofFn fun i : Fin s.params.ℓ =>
    (unpackSigned 1 (s.params.γ₁.log2 + 1) s.params.γ₁ (read (κ + i.val))).get 0

/-- The Algorithm 34 mask at counter `κ` from private bytes indexed by its two-byte nonce. -/
def maskFromRow (s : Level) (row : FixedBytes 2 → FixedBytes (maskPolyBytes s)) (κ : ℕ) :
    Vector (Vector (ZMod 8380417) 256) s.params.ℓ :=
  expandMaskFrom s κ fun nonce => (row (nonceSuffix nonce)).toList

/-- ExpandMask (Algorithm 34). Each mask polynomial absorbs the same seed and its own
two-byte little-endian counter, and decodes 256 coefficients in [1 − γ₁, γ₁]. -/
def Xofs.expandMask (H : Xofs) (s : Level) (seed : List Byte) (κ : ℕ) :
    Vector (Vector (ZMod 8380417) 256) s.params.ℓ :=
  expandMaskFrom s κ fun nonce => H.h256.readBytes (nonceInput seed nonce) (maskPolyBytes s)

/-- FIPS 202 specialization of `Xofs.expandMask`. -/
abbrev expandMask := Xofs.expandMask Xofs.shake

/-- The mask and materialized module product computed before the Algorithm 7 challenge. -/
private structure AttemptCommitment (s : Level) where
  /-- The mask vector produced by Algorithm 34. -/
  mask : Fin s.params.ℓ → Poly
  /-- The full commitment before taking its high bits. -/
  product : Fin s.params.k → Poly

private def AttemptCommitment.ofMask (s : Level) (A : PublicMatrix s)
    (y : Fin s.params.ℓ → Poly) : AttemptCommitment s :=
  ⟨y, ringVectorCoeffs (tabulateRingVector (moduleSISMap A y))⟩

/-- Prepare an actual signing attempt from its mask seed, retry counter and public matrix. -/
private def Xofs.prepareAttempt (H : Xofs) (s : Level) (A : PublicMatrix s) (maskSeed : List Byte)
    (κ : ℕ) : AttemptCommitment s :=
  AttemptCommitment.ofMask s A (ringVectorCoeffs (H.expandMask s maskSeed κ))

/-- Complete Algorithm 7 using the sampled challenge and digest. XOF exhaustion is fatal,
a failed norm or hint check rejects the mask, and success returns the encoded signature. -/
def finishSigningAttempt (s : Level) (sk : PrivateKey s) (y : Fin s.params.ℓ → Poly)
    (w : Fin s.params.k → Poly) (digest : List Byte) (challenge : Option Poly) :
    Option (Option (List Byte)) := do
  let c ← challenge
  let response := compressedResponse s.params (hintLimit s) sk.s₁ sk.s₂ sk.t₀ y w
    (Vector.ofFn c).get
  return response.map (fun σ => encodeSignature s ⟨digest, σ.z, σ.h⟩)

private def Xofs.attemptWithMask (H : Xofs) (s : Level) (sk : PrivateKey s)
    (matrix : PublicMatrix s) (μ : List Bool) (y : Fin s.params.ℓ → Poly) :
    Option (Option (List Byte)) :=
  let prep := AttemptCommitment.ofMask s matrix y
  let digest := H.commitmentDigest s (highBitsVec s.params prep.product) μ
  finishSigningAttempt s sk prep.mask prep.product digest (H.sampleInBall s digest)

private def Xofs.attempt (H : Xofs) (s : Level) (sk : PrivateKey s) (matrix : PublicMatrix s)
    (μ : List Bool) (maskSeed : List Byte) (κ : ℕ) : Option (Option (List Byte)) :=
  H.attemptWithMask s sk matrix μ (ringVectorCoeffs (H.expandMask s maskSeed κ))

private def firstAccepted (stride : ℕ) (tryAt : ℕ → Option (Option (List Byte))) :
    ℕ → ℕ → Option (List Byte)
  | 0, _ => none
  | fuel + 1, κ => do
    let result ← tryAt κ
    match result with
    | some sig => return sig
    | none => firstAccepted stride tryAt fuel (κ + stride)

/-- Algorithm 7's 814-attempt loop with an explicit mask at each retry counter. The ambient XOF
supplies the commitment digests and sparse challenges. -/
def Xofs.signingRetries (H : Xofs) (s : Level) (sk : PrivateKey s) (A : PublicMatrix s)
    (μ : List Bool) (mask : ℕ → Vector (Vector (ZMod 8380417) 256) s.params.ℓ) :
    Option (List Byte) :=
  firstAccepted s.params.ℓ (fun nonce => H.attemptWithMask s sk A μ
    (ringVectorCoeffs (mask nonce))) 814 0

private structure SigningState (s : Level) where
  sk : PrivateKey s
  A : PublicMatrix s
  μ : List Bool
  maskSeed : List Byte

/-- Raw SHAKE256 input for the private mask seed in Algorithm 7, line 7. -/
@[expose] def maskSeedInput (key : List Byte) (rnd : FixedBytes 32) (μ : List Bool) : List Bool :=
  Keccak.bytesToBitsLE (key ++ rnd.toList) ++ μ

/-- The 32-byte hedge contributes 256 bits between the key and representative. -/
theorem length_maskSeedInput (key : List Byte) (rnd : FixedBytes 32) (μ : List Bool) :
    (maskSeedInput key rnd μ).length = 8 * (key.length + 32) + μ.length := by
  rw [maskSeedInput, List.length_append, Keccak.length_bytesToBitsLE, List.length_append,
    FixedBytes.length_toList]

private def Xofs.startSigningWithSeed (H : Xofs) (s : Level) (bytes : List Byte)
    (formatted : List Bool) (derive : PrivateKey s → List Bool → List Byte) :
    Option (SigningState s) := do
  let sk ← decodePrivate s bytes
  let A ← H.expandA s sk.rho
  let μ := H.representativeFromTr sk.tr formatted
  return ⟨sk, A, μ, derive sk μ⟩

private def Xofs.startSigning (H : Xofs) (s : Level) (bytes : List Byte) (formatted : List Bool)
    (rnd : FixedBytes 32) : Option (SigningState s) :=
  H.startSigningWithSeed s bytes formatted fun sk μ => H.h256.read (maskSeedInput sk.key rnd μ) 64

private def Xofs.runSigning (H : Xofs) (s : Level) (setup : Option (SigningState s)) :
    Option (List Byte) := do
  let st ← setup
  H.signingRetries s st.sk st.A st.μ (H.expandMask s st.maskSeed)

/-- Algorithm 7 on encoded secret keys, formatted bit-string messages and 32 hedging bytes.
The signer distinguishes a rejected attempt (advance κ by ℓ) from XOF exhaustion (abort).
After 814 rejected attempts it returns the single error of Appendix C. -/
def Xofs.signInternal (H : Xofs) (s : Level) (bytes : List Byte) (formatted : List Bool)
    (rnd : FixedBytes 32) : Option (List Byte) :=
  H.runSigning s (H.startSigning s bytes formatted rnd)

/-- FIPS 202 specialization of `Xofs.signInternal`. -/
abbrev signInternal := Xofs.signInternal Xofs.shake

/-- Pure ML-DSA.Sign (Algorithm 2) with explicit hedging randomness. The deterministic
variant uses 32 zero bytes. Contexts longer than 255 bytes return an error. -/
def Xofs.sign (H : Xofs) (s : Level) (sk : List Byte) (message : List Bool) (ctx : List Byte)
    (rnd : FixedBytes 32) : Option (List Byte) := do
  guard (ctx.length ≤ 255)
  H.signInternal s sk (formatMessage message ctx) rnd

/-- FIPS 202 specialization of `Xofs.sign`. -/
abbrev sign := Xofs.sign Xofs.shake

private theorem attempt_of_firstAccepted {stride fuel start : ℕ}
    {f : ℕ → Option (Option (List Byte))} {sig : List Byte}
    (h : firstAccepted stride f fuel start = some sig) : ∃ κ, f κ = some (some sig) := by
  induction fuel generalizing start with
  | zero => simp [firstAccepted] at h
  | succ fuel ih =>
    cases hf : f start with
    | none => simp [firstAccepted, hf] at h
    | some v =>
      cases v with
      | none => exact ih (by simpa [firstAccepted, hf] using h)
      | some bytes =>
        have he : bytes = sig := by simpa [firstAccepted, hf] using h
        exact ⟨start, he ▸ hf⟩

private theorem verified_of_attempt {H : Xofs} {s : Level} (sk : MLDSA.SecretKey s.params)
    (rho : FixedBytes 32) {key tr maskSeed : List Byte} {κ : ℕ} {f : Forgery}
    (hA : H.expandA s rho.toList = some sk.A) (hctx : f.context.length ≤ 255)
    (hs₂ : ∀ i j, |(sk.s₂ i j).valMinAbs| ≤ s.params.η)
    (hs : H.attempt s ⟨rho.toList, key, tr, sk.s₁, sk.s₂, publicKeyLowPart s.params 13 sk.publicKey⟩
      sk.A (H.messageRepresentative (encodePublic s rho.toList sk.publicKey.t) (formattedMessage f))
        maskSeed κ = some (some f.signature)) :
    H.verify s (encodePublic s rho.toList sk.publicKey.t) f.message f.context f.signature =
      some true := by
  let y := ringVectorCoeffs (H.expandMask s maskSeed κ)
  let w := moduleSISMap sk.A y
  let μ := H.messageRepresentative (encodePublic s rho.toList sk.publicKey.t) (formattedMessage f)
  let digest := H.commitmentDigest s (highBitsVec s.params w) μ
  have vecGet {n : ℕ} {α : Type} (g : Fin n → α) : (Vector.ofFn g).get = g :=
    funext (Vector.get_ofFn g)
  cases hc : H.sampleInBall s digest with
  | none =>
    simp only [Xofs.attempt, Xofs.attemptWithMask, AttemptCommitment.ofMask, finishSigningAttempt,
      tabulateRingVector_eq] at hs
    change (H.sampleInBall s digest).bind _ = _ at hs
    simp [hc] at hs
  | some c =>
    let resp := compressedResponse s.params (hintLimit s) sk.s₁ sk.s₂
      (publicKeyLowPart s.params 13 sk.publicKey) y w c
    have out : resp.map (fun σ => encodeSignature s ⟨digest, σ.z, σ.h⟩) = some f.signature := by
      simp only [Xofs.attempt, Xofs.attemptWithMask, AttemptCommitment.ofMask, finishSigningAttempt,
        tabulateRingVector_eq,
        vecGet] at hs
      change ((H.sampleInBall s digest).bind _) = _ at hs
      simpa [hc, resp, y, w] using hs
    cases he : resp with
    | none => simp [he] at out
    | some σ =>
      have enc : encodeSignature s ⟨digest, σ.z, σ.h⟩ = f.signature := by simpa [he] using out
      have valid : s.params.Valid := by
        cases s
        · exact Params.valid_mldsa44
        · exact Params.valid_mldsa65
        · exact Params.valid_mldsa87
      obtain ⟨hz, hw, hchallenge, recovers⟩ := recovered_of_compressedResponse s.params valid
        (by cases s <;> decide) (inBall_of_sampleInBall hc) hs₂ he
      have dec := sigDecode_encodeSignature s ⟨digest, σ.z, σ.h⟩
        (length_commitmentDigest (H := H) ..) hz hw
      rw [enc] at dec
      apply verifyWithExpansion_of_recovered (f := f) (c := c) hA hctx dec hc hz
      change H.commitmentDigest s _ μ = digest
      rw [← hchallenge]
      exact congrArg (fun high => H.commitmentDigest s high μ) recovers

/-- For any fixed pair of XOFs, Algorithm 3 accepts every successful signature produced
under a key generated with those same XOFs. This includes deterministic and hedged randomness. -/
theorem verify_of_sign {H : Xofs} {s : Level} {seed : FixedBytes 32} {keys : KeyPair} {f : Forgery}
    {rnd : FixedBytes 32} (hg : H.keyGen s seed = some keys)
    (hs : H.sign s keys.secretKey f.message f.context rnd = some f.signature) :
    H.verify s keys.publicKey f.message f.context f.signature = some true := by
  obtain ⟨rho, sk, hA, pk, decoded, _, short⟩ := privateKey_of_keyGen hg
  have ctx : f.context.length ≤ 255 := by
    by_contra h
    simp [Xofs.sign, guard, h] at hs
  simp only [Xofs.sign, guard, ctx, ↓reduceIte, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some, Xofs.signInternal, Xofs.runSigning, Xofs.signingRetries, Xofs.startSigning,
    Xofs.startSigningWithSeed, decoded, hA] at hs
  obtain ⟨κ, htry⟩ := attempt_of_firstAccepted hs
  rw [pk] at htry ⊢
  exact verified_of_attempt sk rho hA ctx short htry

/-- A context and bit-string message chosen by an external signing caller. -/
structure SigningQuery where
  /-- The external context bytes. -/
  context : List Byte
  /-- The original message bits. -/
  message : List Bool

/-- An adaptive randomized adversary whose signing calls may return the FIPS error. -/
abbrev SigningForger :=
  List Byte → ProbOracleComp (fun _ : SigningQuery => Option (List Byte)) Forgery

/-- Keep each successful signature with the exact context and message presented to the signer. -/
@[expose] def SigningQuery.logReply (q : SigningQuery) (sig : Option (List Byte))
    (log : List Forgery) : List Forgery :=
  match sig with
  | none => log
  | some bytes => ⟨q.context, q.message, bytes⟩ :: log

/-- FIPS verifies the output triple and no signing call returned that triple. -/
@[expose] def Xofs.winsForgery (H : Xofs) (s : Level) (pk : List Byte) (f : Forgery)
    (log : List Forgery) : Bool :=
  (H.verify s pk f.message f.context f.signature).getD false && !log.contains f

private def Xofs.signAndLog (H : Xofs) (s : Level) (sk : List Byte) (q : SigningQuery)
    (log : List Forgery) (rnd : FixedBytes 32) : Option (List Byte) × List Forgery :=
  let sig := H.sign s sk q.message q.context rnd
  (sig, q.logReply sig log)

/-- Sign with fresh hedging randomness and log the context and message of a successful reply. -/
noncomputable def Xofs.signingOracle (H : Xofs) (s : Level) (sk : List Byte) (q : SigningQuery)
    (log : List Forgery) : PMF (Option (List Byte) × List Forgery) :=
  (PMF.uniformOfFintype (FixedBytes 32)).map (H.signAndLog s sk q log)

/-- Run the forger against the actual signed responses with 32 independent byte draws per
request. The program returns the adversary's output and the full successful signing log. -/
def Xofs.runSigningForger (H : Xofs) (s : Level) (keys : KeyPair) (adv : SigningForger) :
    ProbComp (Forgery × List Forgery) :=
  let handler (q : SigningQuery) (log : List Forgery) :=
    H.signAndLog s keys.secretKey q log <$> OracleComp.replicateFin 32 (ProbComp.unifFin 255)
  (OracleComp.interpret (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifFin n)) handler)
    (adv keys.publicKey)).run []

/-- The closed program produces the same joint transcript as the signing oracle in the
strong chosen-message experiment. -/
theorem eval_runSigningForger (H : Xofs) (s : Level) (keys : KeyPair) (adv : SigningForger) :
    (H.runSigningForger s keys adv).eval =
      ProbOracleComp.runWith (H.signingOracle s keys.secretKey) (adv keys.publicKey) [] := by
  unfold Xofs.runSigningForger
  rw [ProbOracleComp.eval_run_interpret_eq_runWith]
  simp only [ProbComp.eval_map, ProbComp.eval_replicateFin, ProbComp.eval_unifFin,
    PMF.pi_uniformOfFintype]
  rfl

/-- Signing service with the FIPS 202 XOFs. -/
noncomputable abbrev signingOracle := Xofs.signingOracle Xofs.shake

/-- A hedged signing call under a generated key preserves verification of every logged triple. -/
theorem signingOracle_preserves_verified {H : Xofs} {s : Level} {seed : FixedBytes 32}
    {keys : KeyPair} (hg : H.keyGen s seed = some keys) (q : SigningQuery) (hist : List Forgery)
    (ih : ∀ g ∈ hist, H.verify s keys.publicKey g.message g.context g.signature = some true)
    {reply : Option (List Byte)} {next : List Forgery}
    (hs : (reply, next) ∈ (H.signingOracle s keys.secretKey q hist).support) :
    ∀ g ∈ next, H.verify s keys.publicKey g.message g.context g.signature = some true := by
  obtain ⟨rnd, _, hr⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
  dsimp only [Xofs.signAndLog] at hr
  cases sig : H.sign s keys.secretKey q.message q.context rnd with
  | none =>
    simp only [sig, SigningQuery.logReply, Prod.mk.injEq] at hr
    exact hr.2 ▸ ih
  | some bytes =>
    simp only [sig, SigningQuery.logReply, Prod.mk.injEq] at hr
    rw [← hr.2]
    intro g hg'
    rcases List.mem_cons.mp hg' with rfl | htail
    · exact verify_of_sign hg sig
    · exact ih g htail

/-- Every signature in the actual adaptive signing transcript passes the FIPS byte verifier
under the public key returned by the same seed. -/
theorem verify_of_mem_signingTranscript {H : Xofs} {s : Level} {seed : FixedBytes 32}
    {keys : KeyPair} {adv : SigningForger} {out f : Forgery} {log : List Forgery}
    (hg : H.keyGen s seed = some keys)
    (hrun : (out, log) ∈ (ProbOracleComp.runWith (H.signingOracle s keys.secretKey)
      (adv keys.publicKey) []).support) (hf : f ∈ log) :
    H.verify s keys.publicKey f.message f.context f.signature = some true := by
  let inv (history : List Forgery) := ∀ g ∈ history,
    H.verify s keys.publicKey g.message g.context g.signature = some true
  suffices maintained : inv log from maintained f hf
  apply ProbOracleComp.runWith_invariant _ inv ?_ _ [] (by simp [inv]) out log hrun
  exact fun q hist ih _ _ hs => signingOracle_preserves_verified hg q hist ih hs

/-- Search the actual signing log for a reply sharing the forgery's digest, then extract from
the two triples using the public bytes and the matrix supplied to the solver. -/
def Xofs.extractLoggedDigest (H : Xofs) (s : Level) (bytes : List Byte) (A : PublicMatrix s)
    (f : Forgery) (log : List Forgery) : Option (RepeatedDigestWitness s) := do
  let old ← log.find? fun g => g.signature.take (digestBytes s) == f.signature.take (digestBytes s)
  H.extractRepeatedDigest s bytes A f old

/-- A fresh verifying triple and a verified signing log at the same public matrix give a
computed witness whenever the full challenge digest occurs in the log. -/
theorem extractLoggedDigest_of_verifiedLog {H : Xofs} {s : Level} {pk : List Byte}
    {A : PublicMatrix s} {out : Forgery} {log : List Forgery}
    (matrix : H.expandA s (pk.take 32) = some A)
    (logged : ∀ g ∈ log, H.verify s pk g.message g.context g.signature = some true)
    (fresh : out ∉ log)
    (repeated : ∃ g ∈ log, g.signature.take (digestBytes s) = out.signature.take (digestBytes s))
    (valid : H.verify s pk out.message out.context out.signature = some true) :
    ∃ w, H.extractLoggedDigest s pk A out log = some w ∧ w.Valid H A := by
  let same (g : Forgery) := g.signature.take (digestBytes s) == out.signature.take (digestBytes s)
  cases h : log.find? same with
  | none =>
    obtain ⟨g, hg', eq⟩ := repeated
    have bad := List.find?_eq_none.mp h g hg'
    simp [same, eq] at bad
  | some old =>
    have prior := List.mem_of_find?_eq_some h
    have distinct : out ≠ old := fun e => fresh (e ▸ prior)
    have digest : old.signature.take (digestBytes s) = out.signature.take (digestBytes s) :=
      beq_iff_eq.mp (List.find?_some (p := same) h)
    obtain ⟨w, hw, good⟩ :=
      extractRepeatedDigest_of_verify matrix distinct digest.symm valid (logged old prior)
    refine ⟨w, ?_, good⟩
    change (log.find? same >>= _) = some w
    rwa [h, Option.bind_eq_bind, Option.bind_some]

/-- Every fresh accepted forgery with a previously signed digest yields a valid computed witness.
Key generation, the adaptive hedged signing service, verification and extraction use one XOF pair.
The public matrix is the one obtained from the seed in the generated public key. -/
theorem extractLoggedDigest_of_signingTranscript {H : Xofs} {s : Level} {seed : FixedBytes 32}
    {keys : KeyPair} {adv : SigningForger} {out : Forgery} {log : List Forgery}
    (hg : H.keyGen s seed = some keys)
    (hrun : (out, log) ∈ (ProbOracleComp.runWith (H.signingOracle s keys.secretKey)
      (adv keys.publicKey) []).support) (fresh : out ∉ log)
    (repeated : ∃ g ∈ log, g.signature.take (digestBytes s) = out.signature.take (digestBytes s))
    (valid : H.verify s keys.publicKey out.message out.context out.signature = some true) :
    ∃ A w, H.expandA s (keys.publicKey.take 32) = some A ∧
      H.extractLoggedDigest s keys.publicKey A out log = some w ∧ w.Valid H A := by
  obtain ⟨rho, sk, hA, hpk, _, _⟩ := privateKey_of_keyGen hg
  have matrix : H.expandA s (keys.publicKey.take 32) = some sk.A := by
    rwa [hpk, take_encodePublic]
  obtain ⟨w, he, good⟩ := extractLoggedDigest_of_verifiedLog matrix
    (fun _ h => verify_of_mem_signingTranscript hg hrun h) fresh repeated valid
  exact ⟨sk.A, w, matrix, he, good⟩

/-- The strong chosen-message forgery experiment for FIPS 204's finite parameter sets:
generate both keys from one uniform seed, answer adaptive signing calls with the secret key,
and accept a verifying triple precisely when the signer never returned it. -/
noncomputable def Xofs.sufCmaGame (H : Xofs) (s : Level) (adv : SigningForger) : Game :=
  H.keyExperiment s fun keys =>
    (ProbOracleComp.runWith (H.signingOracle s keys.secretKey) (adv keys.publicKey) []).map
      fun (f, log) => H.winsForgery s keys.publicKey f log

/-- FIPS 202 specialization of the strong chosen-message game. -/
noncomputable abbrev sufCmaGame := Xofs.sufCmaGame Xofs.shake

/-- Restricting the strong chosen-message experiment to a forger that makes no signing calls
recovers the byte-verifier key-only experiment exactly, including key-generation failure. -/
theorem sufCmaGame_sample_eq_keyOnlyGame (s : Level) (adv : List Byte → ProbComp Forgery) :
    sufCmaGame s (fun pk => ProbOracleComp.sample (adv pk)) = keyOnlyGame s adv := by
  unfold sufCmaGame Xofs.sufCmaGame keyOnlyGame Xofs.winsForgery
  congr 1
  funext keys
  rw [ProbOracleComp.runWith_sample, PMF.map_comp]
  congr 1
  funext f
  simp

/-- The finite set of actual Algorithm 29 raw inputs at the parameter set's digest width. -/
def digestRows (s : Level) : Finset (List Bool) :=
  Finset.univ.image (fun d : FixedBytes (digestBytes s) => Keccak.bytesToBitsLE d.toList)

private def expansionRow (s : Level) (d : List Byte) (hd : d.length = digestBytes s) :
    digestRows s :=
  ⟨Keccak.bytesToBitsLE d, by
    obtain ⟨v, hv⟩ := FixedBytes.exists_toList hd
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, congrArg _ hv⟩⟩

/-- A 221-byte suffix window after the previous read prefix at each SHAKE256 digest input.
SHAKE128 and all other SHAKE256 words retain their background streams. -/
@[expose] def Xofs.withExpansionRows (H : Xofs) (s : Level) (seen : List Bool → ℕ)
    (table : digestRows s → FixedBytes 221) : Xofs := { H with h256 := H.h256.fill seen table }

private theorem read_off_rows (H : Xofs) {s : Level} (seen : List Bool → ℕ)
    (table : digestRows s → FixedBytes 221) (x : List Bool)
    (hx : x.length ≠ 8 * digestBytes s) (n : ℕ) :
    (H.withExpansionRows s seen table).h256.read x n = H.h256.read x n := by
  apply H.h256.read_fill_of_notMem
  intro h
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp h
  exact hx (by rw [Keccak.length_bytesToBitsLE, FixedBytes.length_toList])

private theorem setup_off_rows (H : Xofs) (s : Level) (seen : List Bool → ℕ)
    (table : digestRows s → FixedBytes 221) (seed : FixedBytes 32) :
    (H.withExpansionRows s seen table).keyGen s seed = H.keyGen s seed :=
  Xofs.keyGen_congr_off_digest s seed rfl (read_off_rows H seen table)

private theorem startSigning_off_rows {H : Xofs} {s : Level} {seed : FixedBytes 32} {keys : KeyPair}
    (hg : H.keyGen s seed = some keys) (seen : List Bool → ℕ)
    (table : digestRows s → FixedBytes 221) (q : SigningQuery) (rnd : FixedBytes 32) :
    let K := H.withExpansionRows s seen table
    let fmt := formatMessage q.message q.context
    K.startSigning s keys.secretKey fmt rnd = H.startSigning s keys.secretKey fmt rnd ∧
      ∀ st, H.startSigning s keys.secretKey fmt rnd = some st →
        st.μ.length = 512 ∧ st.maskSeed.length = 64 := by
  intro K fmt
  obtain ⟨rho, sk, hA, _, dec, _⟩ := privateKey_of_keyGen hg
  let tr := H.h256.readBytes keys.publicKey 64
  have trlen : tr.length = 64 := H.h256.length_read ..
  have bound : 8 * digestBytes s ≤ 512 := by cases s <;> decide
  have formatted : 16 ≤ fmt.length := by
    simp only [fmt, formatMessage, List.length_append, Keccak.length_bytesToBitsLE,
      List.length_cons]
    omega
  have rep : K.representativeFromTr tr fmt = H.representativeFromTr tr fmt := by
    unfold Xofs.representativeFromTr
    rw [read_off_rows H seen table _ (by
      rw [representativeInput, List.length_append, Keccak.length_bytesToBitsLE, trlen]; omega)]
  let μ := H.representativeFromTr tr fmt
  have mlen : μ.length = 512 := by
    simp only [μ, Xofs.representativeFromTr, Keccak.length_bytesToBitsLE]
    rw [H.h256.length_read]
  let key := (H.expandKeySeed s seed).drop 96
  have mask : K.h256.read (maskSeedInput key rnd μ) 64 =
      H.h256.read (maskSeedInput key rnd μ) 64 := by
    apply read_off_rows
    rw [length_maskSeedInput, mlen]
    omega
  have matrix : K.expandA s rho.toList = some sk.A :=
    (Xofs.expandA_congr (K := K) (H := H) rfl s rho.toList).trans hA
  simp only [Xofs.startSigning, Xofs.startSigningWithSeed, dec, Option.bind_eq_bind,
    Option.bind_some, matrix, hA,
    Option.pure_def]
  change some _ = some _ ∧ _
  constructor
  · rw [rep, mask]
  · intro st he
    cases he
    exact ⟨mlen, H.h256.length_read ..⟩

private theorem prepare_off_rows (H : Xofs) {s : Level} (seen : List Bool → ℕ)
    (table : digestRows s → FixedBytes 221) (A : PublicMatrix s) {seed : List Byte}
    (hlen : seed.length = 64) (κ : ℕ) :
    (H.withExpansionRows s seen table).prepareAttempt s A seed κ = H.prepareAttempt s A seed κ := by
  obtain ⟨v, rfl⟩ := FixedBytes.exists_toList hlen
  have raw (nonce n : ℕ) : (H.withExpansionRows s seen table).h256.readBytes
      (nonceInput v.toList nonce) n = H.h256.readBytes (nonceInput v.toList nonce) n := by
    apply H.h256.read_fill_of_notMem
    intro h
    obtain ⟨d, _, he⟩ := Finset.mem_image.mp h
    exact nonceInput_ne_digestInput v nonce (FixedBytes.length_toList d) he.symm
  simp only [Xofs.prepareAttempt, Xofs.expandMask, raw]

private theorem digest_off_rows (H : Xofs) {s : Level} (seen : List Bool → ℕ)
    (table : digestRows s → FixedBytes 221) (w : Fin s.params.k → Fin 256 → ℤ)
    {μ : List Bool} (hm : μ.length = 512) :
    (H.withExpansionRows s seen table).commitmentDigest s w μ = H.commitmentDigest s w μ := by
  apply H.h256.read_fill_of_notMem
  intro h
  obtain ⟨d, _, he⟩ := Finset.mem_image.mp h
  exact commitmentInput_ne_digestInput w hm (FixedBytes.length_toList d) he.symm

private def afterAttempt {s : Level} (K : Xofs) (st : SigningState s)
    (result : Option (Option (List Byte))) : Option (List Byte) := do
  let answer ← result
  match answer with
  | some sig => return sig
  | none => firstAccepted s.params.ℓ (K.attempt s st.sk st.A st.μ st.maskSeed) 813 s.params.ℓ

private theorem firstAccepted_initial (K : Xofs) {s : Level} (st : SigningState s) :
    firstAccepted s.params.ℓ (K.attempt s st.sk st.A st.μ st.maskSeed) 814 0 =
      afterAttempt K st (K.attempt s st.sk st.A st.μ st.maskSeed 0) := by
  rw [firstAccepted]
  simp only [afterAttempt, Nat.zero_add]

/-- Answer the distinguished first request by feeding fresh bytes into its actual first
Algorithm 29 expansion. The returned table is used by all later signing calls and verification.
Malformed requests return the FIPS error. A rejected response retries with the next counter. -/
noncomputable def Xofs.refreshFirstSign (H : Xofs) (s : Level) (seen : List Bool → ℕ)
    (bytes : List Byte) (q : SigningQuery) (rnd : FixedBytes 32)
    (table : digestRows s → FixedBytes 221) :
    PMF ((digestRows s → FixedBytes 221) × Option (List Byte)) :=
  if q.context.length ≤ 255 then
    match H.startSigning s bytes (formatMessage q.message q.context) rnd with
    | none => PMF.pure (table, none)
    | some st =>
      let prep := H.prepareAttempt s st.A st.maskSeed 0
      let w := highBitsVec s.params prep.product
      let d := H.commitmentDigest s w st.μ
      let key := expansionRow s d (length_commitmentDigest (H := H) s w st.μ)
      (PMF.uniformOfFintype (FixedBytes 221)).map fun fresh =>
        let updated := Function.update table key fresh
        let K := H.withExpansionRows s seen updated
        let tape := (H.h256.read key (seen key) ++ List.ofFn fresh).take 221
        let result :=
          finishSigningAttempt s st.sk prep.mask prep.product d (sampleInBallBytes s tape)
        (updated, afterAttempt K st result)
  else PMF.pure (table, none)

private theorem refreshFirstSign_bind {α : Type} {H : Xofs} {s : Level} {seed : FixedBytes 32}
    {keys : KeyPair} (hg : H.keyGen s seed = some keys) (seen : List Bool → ℕ)
    (q : SigningQuery) (rnd : FixedBytes 32)
    (post : (digestRows s → FixedBytes 221) → Option (List Byte) → PMF α) :
    ((PMF.uniformOfFintype _).bind fun table =>
      (H.refreshFirstSign s seen keys.secretKey q rnd table).bind fun (t, ans) => post t ans) =
      (PMF.uniformOfFintype _).bind fun t => post t ((H.withExpansionRows s seen t).sign s
        keys.secretKey q.message q.context rnd) := by
  by_cases hc : q.context.length ≤ 255
  · cases hs : H.startSigning s keys.secretKey (formatMessage q.message q.context) rnd with
    | none =>
      apply congrArg (PMF.bind _)
      funext t
      have hk := (startSigning_off_rows hg seen t q rnd).1.trans hs
      simp [Xofs.refreshFirstSign, hc, hs, Xofs.sign, Xofs.signInternal, Xofs.runSigning, hk]
    | some st =>
      let prep := H.prepareAttempt s st.A st.maskSeed 0
      let w := highBitsVec s.params prep.product
      let d := H.commitmentDigest s w st.μ
      let key := expansionRow s d (length_commitmentDigest (H := H) s w st.μ)
      let run := fun t => post t ((H.withExpansionRows s seen t).sign s
        keys.secretKey q.message q.context rnd)
      have uniform := PMF.uniformOfFintype_bind_bind_adaptiveUpdate (fun _ => key)
        (fun _ _ => rfl) run
      refine Eq.trans ?_ uniform
      apply congrArg (PMF.bind _)
      funext t
      simp only [Xofs.refreshFirstSign, hc, ite_true, hs, PMF.bind_map]
      apply congrArg (PMF.bind _)
      funext fresh
      let updated := Function.update t key fresh
      let K := H.withExpansionRows s seen updated
      obtain ⟨hk, shape⟩ := startSigning_off_rows hg seen updated q rnd
      have start : K.startSigning s keys.secretKey (formatMessage q.message q.context) rnd =
          some st := hk.trans hs
      obtain ⟨hμ, hmask⟩ := shape st hs
      have prepared : K.prepareAttempt s st.A st.maskSeed 0 = prep :=
        prepare_off_rows H seen updated st.A hmask 0
      have dg : K.commitmentDigest s w st.μ = d := digest_off_rows H seen updated w hμ
      have sample : K.sampleInBall s d = sampleInBallBytes s
          ((H.h256.read key (seen key) ++ List.ofFn fresh).take 221) := by
        apply congrArg (sampleInBallBytes s)
        have h := H.h256.read_fill_window seen updated key (n := 221) (Nat.le_add_left ..)
        rw [show updated key = fresh from Function.update_self ..] at h
        exact h
      apply congrArg (post updated)
      symm
      change K.sign s keys.secretKey q.message q.context rnd = afterAttempt K st
        (finishSigningAttempt s st.sk prep.mask prep.product d (sampleInBallBytes s
          ((H.h256.read key (seen key) ++ List.ofFn fresh).take 221)))
      simp only [Xofs.sign, hc, guard, ↓reduceIte, Option.pure_def, Option.bind_eq_bind,
        Option.bind_some, Xofs.signInternal, Xofs.runSigning, Xofs.signingRetries, start]
      change firstAccepted s.params.ℓ (K.attempt s st.sk st.A st.μ st.maskSeed) 814 0 = _
      rw [firstAccepted_initial]
      change afterAttempt K st (let p := K.prepareAttempt s st.A st.maskSeed 0
        let c := K.commitmentDigest s (highBitsVec s.params p.product) st.μ
        finishSigningAttempt s st.sk p.mask p.product c (K.sampleInBall s c)) = _
      rw [prepared]
      change afterAttempt K st
        (finishSigningAttempt s st.sk prep.mask prep.product (K.commitmentDigest s w st.μ)
          (K.sampleInBall s (K.commitmentDigest s w st.μ))) = _
      rw [dg, sample]
  · apply congrArg (PMF.bind _)
    funext t
    simp [Xofs.refreshFirstSign, hc, Xofs.sign]

/-- The continuation of an actual signing request. It receives the byte reply or failure
and can make more randomized, adaptive signing requests before returning its forgery. -/
abbrev SigningContinuation := Xofs → List Byte → Option (List Byte) →
  ProbOracleComp (fun _ : SigningQuery => Option (List Byte)) Forgery

/-- Deliver the first signing reply, log its successful triple, then run the remaining
chosen-message program and check freshness and verification under the same XOFs. -/
@[expose] noncomputable def Xofs.continueFirstSigning (K : Xofs) (s : Level) (keys : KeyPair)
    (q : SigningQuery) (ans : Option (List Byte)) (next : SigningContinuation) : Game :=
  (ProbOracleComp.runWith (K.signingOracle s keys.secretKey) (next K keys.publicKey ans)
    (q.logReply ans [])).map fun (f, log) => K.winsForgery s keys.publicKey f log

private theorem first_request {State : Type} (K : Xofs) (s : Level)
    (choose : List Byte → ProbComp (SigningQuery × State)) (next : State → SigningContinuation) :
    K.sufCmaGame s (fun pk => do
      let (q, st) ← ProbOracleComp.sample (choose pk)
      let reply ← ProbOracleComp.query q
      next st K pk reply) =
    K.keyExperiment s fun keys => (choose keys.publicKey).eval.bind fun (q, st) =>
      (PMF.uniformOfFintype (FixedBytes 32)).bind fun rnd =>
        K.continueFirstSigning s keys q (K.sign s keys.secretKey q.message q.context rnd)
          (next st) := by
  apply congrArg (K.keyExperiment s)
  funext keys
  simp only [ProbOracleComp.runWith_sample_bind, PMF.map_bind]
  apply congrArg (PMF.bind _)
  funext ⟨q, st⟩
  simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, Xofs.signingOracle,
    PMF.bind_map, PMF.map_bind, Xofs.continueFirstSigning, Xofs.signAndLog, Function.comp_def]

/-- Refresh the Algorithm 29 row in the first signing request of a chosen-message run.
The adversary chooses the query from the generated public key and earlier raw SHAKE256
prefixes. The oracle draws a uniform hedge. The refreshed bytes drive the first attempt
with counter zero. Rejection executes the remaining 813 attempts; success or failure is
delivered to the continuation with the actual signing log. Subsequent signing and final
verification use the updated table. The raw-prefix view is classical. -/
theorem refreshFirstRequest_sufCmaGame {State : Type} (H : Xofs) (s : Level) (seen : List Bool → ℕ)
    (choose : (List Bool → List Byte) → List Byte → ProbComp (SigningQuery × State))
    (next : State → SigningContinuation) :
    (H.keyExperiment s fun keys => do
      let (q, st) ← (choose (fun x => H.h256.read x (seen x)) keys.publicKey).eval
      let rnd ← PMF.uniformOfFintype (FixedBytes 32)
      let table ← PMF.uniformOfFintype (digestRows s → FixedBytes 221)
      let (updated, ans) ← H.refreshFirstSign s seen keys.secretKey q rnd table
      (H.withExpansionRows s seen updated).continueFirstSigning s keys q ans (next st)) =
    ((PMF.uniformOfFintype _).bind fun table =>
      let K := H.withExpansionRows s seen table
      K.sufCmaGame s fun pk => do
        let (q, st) ← ProbOracleComp.sample (choose (fun x => K.h256.read x (seen x)) pk)
        let reply ← ProbOracleComp.query q
        next st K pk reply) := by
  let prior := fun x => H.h256.read x (seen x)
  have same (t : digestRows s → FixedBytes 221) :
      (fun x => (H.withExpansionRows s seen t).h256.read x (seen x)) = prior :=
    funext fun _ => H.h256.read_fill_of_le seen t le_rfl
  have expand (t : digestRows s → FixedBytes 221) :=
    first_request (H.withExpansionRows s seen t) s (choose prior) next
  simp only [same, expand, Xofs.keyExperiment, setup_off_rows, PMF.monad_bind_eq_bind]
  rw [PMF.bind_comm (PMF.uniformOfFintype (digestRows s → FixedBytes 221))
    (PMF.uniformOfFintype (FixedBytes 32))]
  apply congrArg (PMF.bind _)
  funext seed
  cases hg : H.keyGen s seed with
  | none => simp
  | some keys =>
    rw [PMF.bind_comm (PMF.uniformOfFintype (digestRows s → FixedBytes 221))
      (choose prior keys.publicKey).eval]
    apply congrArg (PMF.bind _)
    funext ⟨q, st⟩
    rw [PMF.bind_comm (PMF.uniformOfFintype (digestRows s → FixedBytes 221))
      (PMF.uniformOfFintype (FixedBytes 32))]
    apply congrArg (PMF.bind _)
    funext rnd
    exact refreshFirstSign_bind hg seen q rnd
      (fun t ans => (H.withExpansionRows s seen t).continueFirstSigning s keys q ans (next st))

end Cslib.Crypto.MLDSA.FIPS204
