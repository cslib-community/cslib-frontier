/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.FIPS204ResponseBinding
public import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
public import CslibFrontier.Languages.Probabilistic.Oracle.EvalPure
public import CslibFrontier.Languages.Probabilistic.QueryCount
import Batteries.Data.Vector.Lemmas
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation

/-!
# FIPS 204 signing and the strong chosen-message forgery experiment

[FIPS 204][NISTFIPS204], Algorithms 2, 6 and 7. The external signer accepts the encoded
private key, a bit-string message, a byte context and 32 bytes of randomness. A zero randomness
string selects deterministic signing. The bounded loop uses the 814-attempt option of Appendix C.
The adaptive strong-unforgeability experiment draws fresh hedging randomness for each signature
and records the context, message and exact bytes of every successful reply.

`verify_of_sign` proves that every successful signature under a generated key passes
Algorithm 3. For a fresh verifying signature that repeats a logged context, message and
challenge digest, `digestCollision_or_msis_of_signingTranscript` derives the SHAKE256 collision
or the short integer kernel witness from the two signatures.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability

/-- ExpandMask (Algorithm 34). Each of the ℓ rows queries the same seed with its own
two-byte little-endian counter. All rows share their raw XOF with every other signing role. -/
@[expose] def expandMaskReads (s : Level) (seed : List Byte) (κ : ℕ) :
    ExtendableOutput.Reads (Vector (Vector (ZMod 8380417) 256) s.params.ℓ) :=
  let width := s.params.γ₁.log2 + 1
  Vector.ofFnM fun i : Fin s.params.ℓ => do
    let nonce := κ + i.val
    let addr := Keccak.bytesToBitsLE (nonceInput seed nonce)
    let bytes ← OracleComp.query ⟨addr, 32 * width⟩
    return (unpackSigned 1 width s.params.γ₁ bytes).get 0

/-- Algorithm 34 evaluated against the selected SHAKE256 stream. -/
@[expose] def Xofs.expandMask (H : Xofs) (s : Level) (seed : List Byte) (κ : ℕ) :=
  OracleComp.evalPure (ExtendableOutput.Request.answer H.h256) (expandMaskReads s seed κ)

/-- FIPS 202 specialization of `Xofs.expandMask`. -/
abbrev expandMask := Xofs.expandMask Xofs.shake

/-- Complete Algorithm 7 using the sampled challenge and digest. XOF exhaustion is fatal,
a failed norm or hint check rejects the mask, and success returns the encoded signature. -/
def finishSigningAttempt (s : Level) (sk : PrivateKey s) (y : Fin s.params.ℓ → Poly)
    (w : Fin s.params.k → Poly) (digest : List Byte) (challenge : Option Poly) :
    Option (Option (List Byte)) := do
  let c ← challenge
  let response := compressedResponse s.params (hintLimit s) sk.s₁ sk.s₂ sk.t₀ y w
    (Vector.ofFn c).get
  return response.map (fun σ => encodeSignature s ⟨digest, σ.z, σ.h⟩)

/-- The length of every successful reply, including for decoded keys outside KeyGen's image. -/
theorem length_finishSigningAttempt {s : Level} {sk : PrivateKey s} {y w digest challenge sig}
    (hd : digest.length = digestBytes s)
    (h : finishSigningAttempt s sk y w digest challenge = some (some sig)) :
    sig.length = signatureBytes s := by
  unfold finishSigningAttempt at h
  cases challenge with
  | none => contradiction
  | some c =>
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
    dsimp only [compressedResponse] at h
    split_ifs at h with hz hh
    · simp only [Option.map_some, Option.some.injEq] at h
      obtain rfl := h
      exact length_encodeSignature _ _ hd hh.2
    · contradiction
    · contradiction

private def Xofs.attempt (H : Xofs) (s : Level) (sk : PrivateKey s) (matrix : PublicMatrix s)
    (μ : List Bool) (seed : List Byte) (κ : ℕ) : Option (Option (List Byte)) :=
  let y := ringVectorCoeffs (H.expandMask s seed κ)
  let w := ringVectorCoeffs (tabulateRingVector (moduleSISMap matrix y))
  let digest := H.commitmentDigest s (highBitsVec s.params w) μ
  finishSigningAttempt s sk y w digest (H.sampleInBall s digest)

/-- The capped signing loop. Each attempt reads all ExpandMask rows, the commitment digest
and the 221 SampleInBall bytes. Every request goes to one raw SHAKE256 interface. -/
@[expose] def signingQueries {R : Type} (s : Level) (sk : PrivateKey s) (A : PublicMatrix s)
    (μ : List Bool) (seed : List Byte) (reply : Option (List Byte) → R) :
    ℕ → ℕ → ExtendableOutput.Reads R
  | 0, _ => pure (reply none)
  | fuel + 1, κ => do
    let masks ← expandMaskReads s seed κ
    let y := ringVectorCoeffs masks
    let w := ringVectorCoeffs (tabulateRingVector (moduleSISMap A y))
    let digest ← OracleComp.query ⟨commitmentInput s (highBitsVec s.params w) μ, digestBytes s⟩
    let stream ← OracleComp.query ⟨Keccak.bytesToBitsLE digest, 221⟩
    match finishSigningAttempt s sk y w digest (sampleInBallBytes s stream) with
    | none => pure (reply none)
    | some (some sig) => pure (reply (some sig))
    | some none => signingQueries s sk A μ seed reply fuel (κ + s.params.ℓ)

/-- The full internal signer. Matrix expansion uses SHAKE128; every use of SHAKE256, from
the message representative and masking seed through the rejection loop, is an oracle call. -/
@[expose] def Xofs.signInternalReads {R : Type} (H : Xofs) (s : Level) (key : List Byte)
    (formatted : List Bool) (rnd : FixedBytes 32) (reply : Option (List Byte) → R) :
    ExtendableOutput.Reads R :=
  match decodePrivate s key with
  | none => pure (reply none)
  | some sk =>
    match H.expandA s sk.rho with
    | none => pure (reply none)
    | some A => do
      let representative ← OracleComp.query ⟨Keccak.bytesToBitsLE sk.tr ++ formatted, 64⟩
      let μ := Keccak.bytesToBitsLE representative
      let seed ← OracleComp.query ⟨Keccak.bytesToBitsLE (sk.key ++ rnd.toList) ++ μ, 64⟩
      signingQueries s sk A μ seed reply 814 0

/-- Algorithm 7 on encoded keys, formatted message and 32 hedging bytes, with Appendix C's
814-attempt limit. -/
@[expose] def Xofs.signInternal (H : Xofs) (s : Level) (key : List Byte) (formatted : List Bool)
    (rnd : FixedBytes 32) : Option (List Byte) :=
  OracleComp.evalPure (ExtendableOutput.Request.answer H.h256)
    (H.signInternalReads s key formatted rnd id)

/-- FIPS 202 specialization of `Xofs.signInternal`. -/
abbrev signInternal := Xofs.signInternal Xofs.shake

/-- Algorithm 2, including the 255-byte context bound and explicit randomness. -/
@[expose] def Xofs.sign (H : Xofs) (s : Level) (key : List Byte) (message : List Bool)
    (ctx : List Byte) (rnd : FixedBytes 32) : Option (List Byte) := do
  guard (ctx.length ≤ 255)
  H.signInternal s key (formatMessage message ctx) rnd

/-- FIPS 202 specialization of `Xofs.sign`. -/
abbrev sign := Xofs.sign Xofs.shake

private theorem bounded_vector_reads {α : Type} {n : ℕ} (f : Fin n → ExtendableOutput.Reads α)
    (h : ∀ i, (f i).IsQueryBounded 1) : (Vector.ofFnM f).IsQueryBounded n := by
  induction n with
  | zero => rw [Vector.ofFnM_zero]; exact .pure _ _
  | succ n ih =>
    rw [Vector.ofFnM_succ]
    apply (ih _ (fun i => h i.castSucc)).bind
    intro _
    simpa only [Nat.add_zero] using (h (Fin.last n)).bind (m := 0) (fun _ => .pure _ _)

/-- Each FIPS trial uses ℓ mask-row reads, one commitment read and one challenge-expansion read.
Rejection and fatal expansion consume these reads before the result is examined. -/
theorem signingQueries_bounded {R : Type} (s : Level) (sk : PrivateKey s) (A : PublicMatrix s)
    (μ : List Bool) (seed : List Byte) (reply : Option (List Byte) → R) (fuel κ : ℕ) :
    (signingQueries s sk A μ seed reply fuel κ).IsQueryBounded ((s.params.ℓ + 2) * fuel) := by
  induction fuel generalizing κ with
  | zero => exact .pure _ _
  | succ n ih =>
    have masks : (expandMaskReads s seed κ).IsQueryBounded s.params.ℓ := by
      apply bounded_vector_reads
      intro i
      exact .liftBind _ _ 0 fun _ => .pure _ _
    rw [show (s.params.ℓ + 2) * (n + 1) = s.params.ℓ + ((s.params.ℓ + 2) * n + 1 + 1) by ring]
    apply masks.bind
    intro y
    apply OracleComp.IsCostBounded.liftBind
    intro d
    apply OracleComp.IsCostBounded.liftBind
    intro stream
    split <;> first | exact .pure _ _ | apply ih

/-- Two prelude reads for the representative and hedging seed, followed by at most 814 trials. -/
theorem Xofs.signInternalReads_bounded {R : Type} (H : Xofs) (s : Level) (key : List Byte)
    (formatted : List Bool) (rnd : FixedBytes 32) (reply : Option (List Byte) → R) :
    (H.signInternalReads s key formatted rnd reply).IsQueryBounded
      ((s.params.ℓ + 2) * 814 + 2) := by
  unfold signInternalReads
  split <;> first | exact .pure _ _ | split
  all_goals try exact .pure _ _
  apply OracleComp.IsCostBounded.liftBind
  intro _
  apply OracleComp.IsCostBounded.liftBind
  intro _
  apply signingQueries_bounded

private theorem attempt_of_signingQueries (H : Xofs) (s : Level) (sk : PrivateKey s)
    (A : PublicMatrix s) (μ : List Bool) (seed : List Byte) (fuel κ : ℕ) {sig : List Byte}
    (hs : OracleComp.evalPure (ExtendableOutput.Request.answer H.h256)
      (signingQueries s sk A μ seed id fuel κ) = some sig) :
    ∃ nonce, H.attempt s sk A μ seed nonce = some (some sig) := by
  induction fuel generalizing κ with
  | zero => contradiction
  | succ n ih =>
    simp only [signingQueries, OracleComp.evalPure_bind, OracleComp.evalPure_query, id_eq] at hs
    split at hs
    · contradiction
    · rename_i bytes he
      exact ⟨κ, (Option.some.inj hs) ▸ he⟩
    · exact ih _ hs

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
    simp only [Xofs.attempt, finishSigningAttempt, tabulateRingVector_eq] at hs
    change (H.sampleInBall s digest).bind _ = _ at hs
    simp [hc] at hs
  | some c =>
    let resp := compressedResponse s.params (hintLimit s) sk.s₁ sk.s₂
      (publicKeyLowPart s.params 13 sk.publicKey) y w c
    have out : resp.map (fun σ => encodeSignature s ⟨digest, σ.z, σ.h⟩) = some f.signature := by
      simp only [Xofs.attempt, finishSigningAttempt, tabulateRingVector_eq,
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
  obtain ⟨rho, sk, key, hA, pk, decoded, short⟩ := privateKey_of_keyGen hg
  have ctx : f.context.length ≤ 255 := by
    by_contra h
    simp [Xofs.sign, guard, h] at hs
  simp only [Xofs.sign, guard, ctx, ↓reduceIte, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some, Xofs.signInternal, Xofs.signInternalReads, decoded, hA,
    OracleComp.evalPure_bind, OracleComp.evalPure_query] at hs
  obtain ⟨κ, htry⟩ := attempt_of_signingQueries _ _ _ _ _ _ _ _ hs
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
noncomputable def Xofs.signingOracle (H : Xofs) (s : Level) (sk : List Byte) (q : SigningQuery)
    (log : List Forgery) : PMF (Option (List Byte) × List Forgery) :=
  (PMF.uniformOfFintype (FixedBytes 32)).map fun rnd =>
    let sig := H.sign s sk q.message q.context rnd
    (sig, match sig with
      | none => log
      | some bytes => ⟨q.context, q.message, bytes⟩ :: log)

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

/-- The strong chosen-message forgery experiment for FIPS 204's finite parameter sets:
generate both keys from one uniform seed, answer adaptive signing calls with the secret key,
and accept a verifying triple precisely when the signer never returned it. -/
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
