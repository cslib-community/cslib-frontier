/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.FIPS204ResponseBinding
public import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
import Batteries.Data.Vector.Lemmas
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation

/-!
# Definitions of FIPS 204 signing and the strong chosen-message forgery experiment

[FIPS 204][NISTFIPS204], Algorithms 2, 6 and 7. The external signer accepts the encoded
private key, a bit-string message, a byte context and 32 bytes of randomness. A zero randomness
string selects deterministic signing. The bounded loop uses the 814-attempt option of Appendix C.
The adaptive strong-unforgeability experiment draws fresh hedging randomness for each signature
and records the context, message and exact bytes of every successful reply. Its sole external
service is signing. Both signing and final verification evaluate the concrete FIPS 202 SHAKE
functions. Its zero-signing-query lemma recovers the byte-level key-only experiment.

`verify_of_sign` proves that every successful signature under a generated key passes
Algorithm 3. On a fresh verifying triple whose digest occurs in the log, the extractor
finds a previous reply and computes two colliding SHAKE256 inputs or an integer MSIS vector.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability

/-- ExpandMask (Algorithm 34). Each mask polynomial absorbs the same seed and its own
two-byte little-endian counter, and decodes 256 coefficients in [1 − γ₁, γ₁]. -/
def Xofs.expandMask (H : Xofs) (s : Level) (seed : List Byte) (κ : ℕ) :
    Vector (Vector (ZMod 8380417) 256) s.params.ℓ :=
  let width := s.params.γ₁.log2 + 1
  Vector.ofFn fun i : Fin s.params.ℓ =>
    let nonce := κ + i.val
    let bytes := H.h256.readBytes (nonceInput seed nonce) (32 * width)
    (unpackSigned 1 width s.params.γ₁ bytes).get 0

/-- FIPS 202 specialization of `Xofs.expandMask`. -/
abbrev expandMask := Xofs.expandMask Xofs.shake

private def Xofs.attempt (H : Xofs) (s : Level) (sk : PrivateKey s)
    (matrix : Matrix (Fin s.params.k) (Fin s.params.ℓ) Poly)
    (μ : List Bool) (maskSeed : List Byte) (κ : ℕ) : Option (Option (List Byte)) := do
  let y := ringVectorCoeffs (H.expandMask s maskSeed κ)
  let w := ringVectorCoeffs (tabulateRingVector (moduleSISMap matrix y))
  let digest := H.commitmentDigest s (highBitsVec s.params w) μ
  let c ← H.sampleInBall s digest
  let challenge := Vector.ofFn c
  let response := compressedResponse s.params (hintLimit s) sk.s₁ sk.s₂ sk.t₀ y w challenge.get
  return response.map (fun σ => encodeSignature s ⟨digest, σ.z, σ.h⟩)

private def firstAccepted (stride : ℕ) (tryAt : ℕ → Option (Option (List Byte))) :
    ℕ → ℕ → Option (List Byte)
  | 0, _ => none
  | fuel + 1, κ => do
    let result ← tryAt κ
    match result with
    | some sig => return sig
    | none => firstAccepted stride tryAt fuel (κ + stride)

/-- Algorithm 7 on encoded secret keys, formatted bit-string messages and 32 hedging bytes.
The signer distinguishes a rejected attempt (advance κ by ℓ) from XOF exhaustion (abort).
After 814 rejected attempts it returns the single error of Appendix C. -/
def Xofs.signInternal (H : Xofs) (s : Level) (bytes : List Byte) (formatted : List Bool)
    (rnd : FixedBytes 32) : Option (List Byte) := do
  let sk ← decodePrivate s bytes
  let matrix ← H.expandA s sk.rho
  let μ := H.representativeFromTr sk.tr formatted
  let maskSeed := H.h256.read
    (Keccak.bytesToBitsLE (sk.key ++ rnd.toList) ++ μ) 64
  firstAccepted s.params.ℓ (H.attempt s sk matrix μ maskSeed) 814 0

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
    simp only [Xofs.attempt, tabulateRingVector_eq] at hs
    change (H.sampleInBall s digest).bind _ = _ at hs
    simp [hc] at hs
  | some c =>
    let resp := compressedResponse s.params (hintLimit s) sk.s₁ sk.s₂
      (publicKeyLowPart s.params 13 sk.publicKey) y w c
    have out : resp.map (fun σ => encodeSignature s ⟨digest, σ.z, σ.h⟩) = some f.signature := by
      simp only [Xofs.attempt, tabulateRingVector_eq, vecGet] at hs
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
  obtain ⟨rho, sk, key, hA, pk, decoded, short⟩ := privateKey_of_keyGen hg
  have ctx : f.context.length ≤ 255 := by
    by_contra h
    simp [Xofs.sign, guard, h] at hs
  simp only [Xofs.sign, guard, ctx, ↓reduceIte, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some, Xofs.signInternal, decoded, hA] at hs
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

/-- Sign with fresh hedging randomness and log the context and message of a successful reply. -/
noncomputable def Xofs.signingOracle (H : Xofs) (s : Level) (sk : List Byte) (q : SigningQuery)
    (log : List Forgery) : PMF (Option (List Byte) × List Forgery) :=
  (PMF.uniformOfFintype (FixedBytes 32)).map fun rnd =>
    let sig := H.sign s sk q.message q.context rnd
    (sig, q.logReply sig log)

/-- Signing service with the FIPS 202 XOFs. -/
noncomputable abbrev signingOracle := Xofs.signingOracle Xofs.shake

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
  intro q hist ih reply next hs
  obtain ⟨rnd, _, hr⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
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

/-- Search the actual signing log for a reply sharing the forgery's digest, then extract from
the two triples using the public bytes and the matrix supplied to the solver. -/
def Xofs.extractLoggedDigest (H : Xofs) (s : Level) (bytes : List Byte) (A : PublicMatrix s)
    (f : Forgery) (log : List Forgery) : Option (RepeatedDigestWitness s) := do
  let old ← log.find? fun g => g.signature.take (digestBytes s) == f.signature.take (digestBytes s)
  H.extractRepeatedDigest s bytes A f old

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
  obtain ⟨rho, sk, _, hA, hpk, _, _⟩ := privateKey_of_keyGen hg
  have matrix : H.expandA s (keys.publicKey.take 32) = some sk.A := by
    rwa [hpk, take_encodePublic]
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
    have signed := verify_of_mem_signingTranscript hg hrun prior
    obtain ⟨w, hw, good⟩ := extractRepeatedDigest_of_verify matrix distinct digest.symm valid signed
    refine ⟨sk.A, w, matrix, ?_, good⟩
    change (log.find? same >>= _) = some w
    rwa [h, Option.bind_eq_bind, Option.bind_some]

/-- The classical strong chosen-message experiment with concrete SHAKE. Both keys come from one
uniform seed. The signer answers adaptive requests with the secret key. An accepted forgery
must be fresh among the returned context, message and signature triples. -/
noncomputable def sufCmaGame (s : Level) (adv : SigningForger) : Game :=
  keyExperiment s fun keys =>
    (ProbOracleComp.runWith (signingOracle s keys.secretKey) (adv keys.publicKey) []).map
      fun (f, log) => Xofs.shake.winsForgery s keys.publicKey f log

/-- Restricting the strong chosen-message experiment to a forger that makes no signing calls
recovers the byte-verifier key-only experiment exactly, including key-generation failure. -/
theorem sufCmaGame_sample_eq_keyOnlyGame (s : Level) (adv : List Byte → ProbComp Forgery) :
    sufCmaGame s (fun pk => ProbOracleComp.sample (adv pk)) = keyOnlyGame s adv := by
  unfold sufCmaGame keyOnlyGame Xofs.winsForgery
  congr 1
  funext keys
  rw [ProbOracleComp.runWith_sample, PMF.map_comp]
  congr 1
  funext f
  simp

end Cslib.Crypto.MLDSA.FIPS204
