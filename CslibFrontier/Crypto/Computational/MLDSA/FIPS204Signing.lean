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
Algorithm 3. For a fresh verifying signature that repeats a logged context, message and
challenge digest, `digestCollision_or_msis_of_signingTranscript` derives the SHAKE256 collision
or the short integer kernel witness from the two signatures.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability

/-- ExpandMask (Algorithm 34). Each mask polynomial absorbs the same seed and its own
two-byte little-endian counter, and decodes 256 coefficients in [1 − γ₁, γ₁]. -/
def expandMask (s : Level) (seed : List Byte) (κ : ℕ) :
    Vector (Vector (ZMod 8380417) 256) s.params.ℓ :=
  let width := s.params.γ₁.log2 + 1
  Vector.ofFn fun i : Fin s.params.ℓ =>
    let nonce := κ + i.val
    let bytes := Keccak.shake256 (seed ++ [Fin.ofNat 256 nonce, Fin.ofNat 256 (nonce / 256)])
      (32 * width)
    (unpackSigned 1 width s.params.γ₁ bytes).get 0

private def attempt (s : Level) (sk : PrivateKey s)
    (matrix : Matrix (Fin s.params.k) (Fin s.params.ℓ) Poly)
    (μ : List Bool) (maskSeed : List Byte) (κ : ℕ) : Option (Option (List Byte)) := do
  let y := ringVectorCoeffs (expandMask s maskSeed κ)
  let w := ringVectorCoeffs (tabulateRingVector (moduleSISMap matrix y))
  let digest := commitmentDigest s (highBitsVec s.params w) μ
  let c ← sampleInBall s digest
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
def signInternal (s : Level) (bytes : List Byte) (formatted : List Bool) (rnd : FixedBytes 32) :
    Option (List Byte) := do
  let sk ← decodePrivate s bytes
  let matrix ← expandA s sk.rho
  let μ := representativeFromTr sk.tr formatted
  let maskSeed := Keccak.bitSponge Keccak.shake256Layout [true, true, true, true]
    (Keccak.bytesToBitsLE (sk.key ++ rnd.toList) ++ μ) 64
  firstAccepted s.params.ℓ (attempt s sk matrix μ maskSeed) 814 0

/-- Pure ML-DSA.Sign (Algorithm 2) with explicit hedging randomness. The deterministic
variant uses 32 zero bytes. Contexts longer than 255 bytes return an error. -/
def sign (s : Level) (sk : List Byte) (message : List Bool) (ctx : List Byte)
    (rnd : FixedBytes 32) : Option (List Byte) := do
  guard (ctx.length ≤ 255)
  signInternal s sk (formatMessage message ctx) rnd

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

private theorem verified_of_attempt {s : Level} (sk : MLDSA.SecretKey s.params)
    (rho : FixedBytes 32) {key tr maskSeed : List Byte} {κ : ℕ} {f : Forgery}
    (hA : expandA s rho.toList = some sk.A) (hctx : f.context.length ≤ 255)
    (hs₂ : ∀ i j, |(sk.s₂ i j).valMinAbs| ≤ s.params.η)
    (hs : attempt s ⟨rho.toList, key, tr, sk.s₁, sk.s₂, publicKeyLowPart s.params 13 sk.publicKey⟩
      sk.A (messageRepresentative (encodePublic s rho.toList sk.publicKey.t) (formattedMessage f))
        maskSeed κ = some (some f.signature)) :
    verify s (encodePublic s rho.toList sk.publicKey.t) f.message f.context f.signature =
      some true := by
  let y := ringVectorCoeffs (expandMask s maskSeed κ)
  let w := moduleSISMap sk.A y
  let μ := messageRepresentative (encodePublic s rho.toList sk.publicKey.t) (formattedMessage f)
  let digest := commitmentDigest s (highBitsVec s.params w) μ
  have vecGet {n : ℕ} {α : Type} (g : Fin n → α) : (Vector.ofFn g).get = g :=
    funext (Vector.get_ofFn g)
  cases hc : sampleInBall s digest with
  | none =>
    simp only [attempt, tabulateRingVector_eq] at hs
    change (sampleInBall s digest).bind _ = _ at hs
    simp [hc] at hs
  | some c =>
    let resp := compressedResponse s.params (hintLimit s) sk.s₁ sk.s₂
      (publicKeyLowPart s.params 13 sk.publicKey) y w c
    have out : resp.map (fun σ => encodeSignature s ⟨digest, σ.z, σ.h⟩) = some f.signature := by
      simp only [attempt, tabulateRingVector_eq, vecGet] at hs
      change ((sampleInBall s digest).bind _) = _ at hs
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
      have dec := sigDecode_encodeSignature s ⟨digest, σ.z, σ.h⟩ (length_commitmentDigest ..) hz hw
      rw [enc] at dec
      apply verifyWithExpansion_of_recovered (f := f) (c := c) hA hctx dec hc hz
      change commitmentDigest s _ μ = digest
      rw [← hchallenge]
      exact congrArg (fun high => commitmentDigest s high μ) recovers

/-- Every successfully returned signature under a generated FIPS 204 key passes Algorithm 3
for the same context and bit-string message. This includes deterministic and hedged randomness. -/
theorem verify_of_sign {s : Level} {seed : FixedBytes 32} {keys : KeyPair} {f : Forgery}
    {rnd : FixedBytes 32} (hg : keyGen s seed = some keys)
    (hs : sign s keys.secretKey f.message f.context rnd = some f.signature) :
    verify s keys.publicKey f.message f.context f.signature = some true := by
  obtain ⟨rho, sk, key, hA, pk, decoded, short⟩ := privateKey_of_keyGen hg
  have ctx : f.context.length ≤ 255 := by
    by_contra h
    simp [sign, guard, h] at hs
  simp only [sign, guard, ctx, ↓reduceIte, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
    signInternal, decoded, hA] at hs
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

/-- Sign with fresh hedging randomness and log the context and message of a successful reply. -/
noncomputable def signingOracle (s : Level) (sk : List Byte) (q : SigningQuery)
    (log : List Forgery) : PMF (Option (List Byte) × List Forgery) :=
  (PMF.uniformOfFintype (FixedBytes 32)).map fun rnd =>
    let sig := sign s sk q.message q.context rnd
    (sig, match sig with
      | none => log
      | some bytes => ⟨q.context, q.message, bytes⟩ :: log)

/-- Every signature in the actual adaptive signing transcript passes the FIPS byte verifier
under the public key returned by the same seed. -/
theorem verify_of_mem_signingTranscript {s : Level} {seed : FixedBytes 32} {keys : KeyPair}
    {adv : SigningForger} {out f : Forgery} {log : List Forgery}
    (hg : keyGen s seed = some keys)
    (hrun : (out, log) ∈ (ProbOracleComp.runWith (signingOracle s keys.secretKey)
      (adv keys.publicKey) []).support) (hf : f ∈ log) :
    verify s keys.publicKey f.message f.context f.signature = some true := by
  let inv (history : List Forgery) := ∀ g ∈ history,
    verify s keys.publicKey g.message g.context g.signature = some true
  suffices maintained : inv log from maintained f hf
  apply ProbOracleComp.runWith_invariant _ inv ?_ _ [] (by simp [inv]) out log hrun
  intro q hist ih reply next hs
  obtain ⟨rnd, _, hr⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
  cases sig : sign s keys.secretKey q.message q.context rnd with
  | none =>
    simp only [sig, Prod.mk.injEq] at hr
    exact hr.2 ▸ ih
  | some bytes =>
    simp only [sig, Prod.mk.injEq] at hr
    rw [← hr.2]
    intro g hg'
    rcases List.mem_cons.mp hg' with rfl | htail
    · exact verify_of_sign hg sig
    · exact ih g htail

/-- In a supported chosen-message run, an accepted fresh forgery that repeats a logged
context, message and digest yields either two distinct SHAKE256 inputs with equal output or
a short nonzero ordinary MSIS vector for the public matrix. -/
theorem digestCollision_or_msis_of_signingTranscript {s : Level} {seed : FixedBytes 32}
    {keys : KeyPair} {adv : SigningForger} {out old : Forgery} {log : List Forgery}
    (hg : keyGen s seed = some keys)
    (hrun : (out, log) ∈ (ProbOracleComp.runWith (signingOracle s keys.secretKey)
      (adv keys.publicKey) []).support)
    (prior : old ∈ log) (fresh : out ∉ log)
    (msg : out.message = old.message) (ctx : out.context = old.context)
    (digest : out.signature.take (digestBytes s) = old.signature.take (digestBytes s))
    (valid : verify s keys.publicKey out.message out.context out.signature = some true) :
    ∃ (rho : FixedBytes 32) (A : PublicMatrix s) (t : Fin s.params.k → Poly)
      (a b : Signature s) (c : Poly), expandA s rho.toList = some A ∧
      keys.publicKey = encodePublic s rho.toList t ∧
      sigDecode s out.signature = some a ∧ sigDecode s old.signature = some b ∧
      sampleInBall s a.digest = some c ∧
      let x : CompressedSignature s.params := ⟨a.z, a.h, c⟩
      let y : CompressedSignature s.params := ⟨b.z, b.h, c⟩
      let pk : PublicKey s.params := ⟨A, t⟩
      let μ := messageRepresentative keys.publicKey (formattedMessage out)
      ((commitmentInput s (x.recover 13 pk) μ ≠ commitmentInput s (y.recover 13 pk) μ ∧
        commitmentDigest s (x.recover 13 pk) μ = commitmentDigest s (y.recover 13 pk) μ) ∨
        ModuleSIS.IsSolution (ModuleSIS.hermiteMatrix A)
          (max (2 * (s.params.γ₁ - s.params.β)) (4 * s.params.γ₂ + 2))
          (responseDifference 13 pk x y)) := by
  have signed := verify_of_mem_signingTranscript hg hrun prior
  have distinct : out.signature ≠ old.signature := by
    intro same
    have he : out = old := by cases out; cases old; congr
    exact fresh (he ▸ prior)
  obtain ⟨rho, sk, _, hA, pk, _, _⟩ := privateKey_of_keyGen hg
  rw [pk] at valid signed
  rw [← msg, ← ctx] at signed
  obtain ⟨a, b, c, ha, hb, hc, result⟩ := digestCollision_or_isSolution_of_verifyWithExpansion
    (f := out) hA distinct digest valid signed
  exact ⟨rho, sk.A, sk.publicKey.t, a, b, c, hA, pk, ha, hb, hc, pk ▸ result⟩

/-- The classical strong chosen-message experiment with concrete SHAKE. Both keys come from one
uniform seed. The signer answers adaptive requests with the secret key. An accepted forgery
must be fresh among the returned context, message and signature triples. -/
noncomputable def sufCmaGame (s : Level) (adv : SigningForger) : Game :=
  keyExperiment s fun keys =>
    (ProbOracleComp.runWith (signingOracle s keys.secretKey) (adv keys.publicKey) []).map
      fun (f, log) =>
        (verify s keys.publicKey f.message f.context f.signature).getD false && !log.contains f

/-- Restricting the strong chosen-message experiment to a forger that makes no signing calls
recovers the byte-verifier key-only experiment exactly, including key-generation failure. -/
theorem sufCmaGame_sample_eq_keyOnlyGame (s : Level) (adv : List Byte → ProbComp Forgery) :
    sufCmaGame s (fun pk => ProbOracleComp.sample (adv pk)) = keyOnlyGame s adv := by
  unfold sufCmaGame keyOnlyGame
  congr 1
  funext keys
  rw [ProbOracleComp.runWith_sample, PMF.map_comp]
  congr 1
  funext f
  simp

end Cslib.Crypto.MLDSA.FIPS204
