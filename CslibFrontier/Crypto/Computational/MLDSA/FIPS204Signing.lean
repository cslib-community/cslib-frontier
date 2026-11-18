/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.FIPS204
public import CslibFrontier.Crypto.Computational.MLDSA.Signing
public import CslibFrontier.Languages.Probabilistic.Oracle.Interaction

/-!
# Definitions of FIPS 204 signing and the strong chosen-message forgery experiment

[FIPS 204][NISTFIPS204], Algorithms 2, 6 and 7. The external signer accepts the encoded
private key, a bit-string message, a byte context and 32 bytes of randomness. A zero randomness
string selects deterministic signing. The bounded loop uses the 814-attempt option of Appendix C.
The adaptive strong-unforgeability experiment draws fresh hedging randomness for each signature
and records the context, message and exact bytes of every successful reply. Its sole external
service is signing. Both signing and final verification evaluate the concrete FIPS 202 SHAKE
functions. Its zero-signing-query lemma recovers the byte-level key-only experiment.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability

private def unpackSigned (n width upper : ℕ) (bytes : List Byte) :
    Vector (Vector (ZMod 8380417) 256) n :=
  let coeff := ((Keccak.bytesToBitsLE (bytes.take (32 * width * n))).toChunks width).map
    fun bits => (upper : ZMod 8380417) - (BitString.lsbValue bits : ZMod 8380417)
  let a := coeff.toArray
  tabulateRingVector fun i j => a[256 * i.val + j.val]!

/-- The decoded fields of a FIPS 204 private key (Algorithm 25). -/
private structure PrivateKey (s : Level) where
  rho : List Byte
  key : List Byte
  tr : List Byte
  s₁ : Fin s.params.ℓ → Poly
  s₂ : Fin s.params.k → Poly
  t₀ : Fin s.params.k → Poly

private def decodePrivate (s : Level) (bytes : List Byte) : Option (PrivateKey s) := do
  let width := (2 * s.params.η).log2 + 1
  let off₂ := 128 + 32 * width * s.params.ℓ
  let off₀ := off₂ + 32 * width * s.params.k
  guard (bytes.length = off₀ + 32 * 13 * s.params.k)
  return ⟨bytes.take 32, (bytes.drop 32).take 32, (bytes.drop 64).take 64,
    ringVectorCoeffs (unpackSigned _ width s.params.η (bytes.drop 128)),
    ringVectorCoeffs (unpackSigned _ width s.params.η (bytes.drop off₂)),
    ringVectorCoeffs (unpackSigned _ 13 4096 (bytes.drop off₀))⟩

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

private def encodeSignature (s : Level) (σ : Signature s) : List Byte :=
  let rows := (List.finRange s.params.k).map fun i => (List.finRange 256).filter (σ.h i)
  let indices := rows.flatten
  let ends := (rows.scanl (fun total row => total + row.length) 0).drop 1
  σ.digest ++ packSigned (s.params.γ₁.log2 + 1) s.params.γ₁ σ.z ++
    indices ++ List.replicate (hintLimit s - indices.length) 0 ++ ends.map (Fin.ofNat 256)

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
