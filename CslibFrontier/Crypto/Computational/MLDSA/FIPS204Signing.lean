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
import CslibFrontier.Probability.PMF.Uniform
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

/-- The mask and materialized module product computed before the Algorithm 7 challenge. -/
structure AttemptCommitment (s : Level) where
  /-- The mask vector produced by Algorithm 34. -/
  mask : Fin s.params.ℓ → Poly
  /-- The full commitment before taking its high bits. -/
  product : Fin s.params.k → Poly

/-- Prepare an actual signing attempt from its mask seed, retry counter and public matrix. -/
def Xofs.prepareAttempt (H : Xofs) (s : Level) (A : PublicMatrix s) (maskSeed : List Byte)
    (κ : ℕ) : AttemptCommitment s :=
  let y := ringVectorCoeffs (H.expandMask s maskSeed κ)
  ⟨y, ringVectorCoeffs (tabulateRingVector (moduleSISMap A y))⟩

private def Xofs.attempt (H : Xofs) (s : Level) (sk : PrivateKey s)
    (matrix : Matrix (Fin s.params.k) (Fin s.params.ℓ) Poly)
    (μ : List Bool) (maskSeed : List Byte) (κ : ℕ) : Option (Option (List Byte)) := do
  let prep := H.prepareAttempt s matrix maskSeed κ
  let y := prep.mask
  let w := prep.product
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
    simp only [Xofs.attempt, Xofs.prepareAttempt, tabulateRingVector_eq] at hs
    change (H.sampleInBall s digest).bind _ = _ at hs
    simp [hc] at hs
  | some c =>
    let resp := compressedResponse s.params (hintLimit s) sk.s₁ sk.s₂
      (publicKeyLowPart s.params 13 sk.publicKey) y w c
    have out : resp.map (fun σ => encodeSignature s ⟨digest, σ.z, σ.h⟩) = some f.signature := by
      simp only [Xofs.attempt, Xofs.prepareAttempt, tabulateRingVector_eq, vecGet] at hs
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
noncomputable def Xofs.sufCmaGame (H : Xofs) (s : Level) (adv : SigningForger) : Game :=
  H.keyExperiment s fun keys =>
    (ProbOracleComp.runWith (H.signingOracle s keys.secretKey) (adv keys.publicKey) []).map
      fun (f, log) =>
        (H.verify s keys.publicKey f.message f.context f.signature).getD false && !log.contains f

/-- FIPS 202 specialization of the strong chosen-message game. -/
noncomputable abbrev sufCmaGame := Xofs.sufCmaGame Xofs.shake

/-- Restricting the strong chosen-message experiment to a forger that makes no signing calls
recovers the byte-verifier key-only experiment exactly, including key-generation failure. -/
theorem sufCmaGame_sample_eq_keyOnlyGame (s : Level) (adv : List Byte → ProbComp Forgery) :
    sufCmaGame s (fun pk => ProbOracleComp.sample (adv pk)) = keyOnlyGame s adv := by
  unfold sufCmaGame Xofs.sufCmaGame keyOnlyGame
  congr 1
  funext keys
  rw [ProbOracleComp.runWith_sample, PMF.map_comp]
  congr 1
  funext f
  simp

/-- SHAKE256 rows receiving fresh suffixes. Every possible digest seed is included; callers
can include commitment preimages or any other raw words in the same finite table. -/
def challengeRows (s : Level) (extra : Finset (List Bool)) : Finset (List Bool) :=
  extra ∪ Finset.univ.image (fun d : FixedBytes (digestBytes s) => Keccak.bytesToBitsLE d.toList)

/-- The raw Algorithm 29 input selected by the digest at a fixed Algorithm 7 commitment. -/
def Xofs.challengeRow (H : Xofs) (s : Level) (extra : Finset (List Bool))
    (w : Fin s.params.k → Fin 256 → ℤ) (μ : List Bool) : challengeRows s extra :=
  ⟨Keccak.bytesToBitsLE (H.commitmentDigest s w μ), by
    obtain ⟨d, hd⟩ := FixedBytes.exists_toList (length_commitmentDigest (H := H) s w μ)
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨d, Finset.mem_univ _, congrArg _ hd⟩)⟩

/-- Install random suffix bytes in the shared SHAKE256 raw rows, retaining all prior prefixes. -/
def Xofs.fill256 (H : Xofs) {rows : Finset (List Bool)} {width : ℕ} (seen : List Bool → ℕ)
    (table : rows → FixedBytes width) : Xofs := { H with h256 := H.h256.fill seen table }

/-- The selected Algorithm 29 read contains exactly the exposed prefix and enough fresh
bytes to fill its 221-byte buffer. A previously exhausted row keeps its rejection outcome. -/
theorem sampleInBall_fill256 (H : Xofs) {s : Level} {extra : Finset (List Bool)}
    (seen : List Bool → ℕ) (table : challengeRows s extra → FixedBytes 221)
    (w : Fin s.params.k → Fin 256 → ℤ) (μ : List Bool) :
    let K := H.fill256 seen table
    let d := K.commitmentDigest s w μ
    let x := K.challengeRow s extra w μ
    K.sampleInBall s d = sampleInBallFromBytes s
      ((H.h256.read x (seen x) ++ List.ofFn (table x)).take 221) := by
  dsimp only
  apply congrArg (sampleInBallFromBytes s)
  exact H.h256.read_fill_window seen table ((H.fill256 seen table).challengeRow s extra w μ)
    (n := 221) (Nat.le_add_left ..)

private theorem prepareAttempt_fill_update (H : Xofs) {s : Level} {extra : Finset (List Bool)}
    (seen : List Bool → ℕ) (table : challengeRows s extra → FixedBytes 221)
    (A : PublicMatrix s) (seed : FixedBytes 64) (κ : ℕ)
    (key : challengeRows s extra) {d : List Byte} (hd : d.length = digestBytes s)
    (hkey : key.val = Keccak.bytesToBitsLE d) (fresh : FixedBytes 221) :
    (H.fill256 seen (Function.update table key fresh)).prepareAttempt s A seed.toList κ =
      (H.fill256 seen table).prepareAttempt s A seed.toList κ := by
  have same (nonce n : ℕ) :
      (H.fill256 seen (Function.update table key fresh)).h256.readBytes
          (nonceInput seed.toList nonce) n =
        (H.fill256 seen table).h256.readBytes (nonceInput seed.toList nonce) n := by
    apply H.h256.read_fill_update_ne
    rw [hkey]
    exact nonceInput_ne_digestInput seed nonce hd
  simp only [Xofs.prepareAttempt, Xofs.expandMask, same]

/-- For a FIPS signing round with its matrix, 64-byte mask seed and counter, refreshing the
unread SHAKE256 window at the digest-selected Algorithm 29 input preserves the signed game.
The signer computes the mask and commitment from the same table. The observer receives the
XOFs, the complete digest, its possibly failing sparse expansion, and the strong chosen-message
verdict. It can retain aliases and distinguish digest words with the same polynomial. Key
generation, signing and verification all use the installed table. The background XOF and
all previously read prefix lengths are fixed before sampling the suffix table. -/
theorem refresh_expansionRow_sufCmaGame {α : Type} (H : Xofs) (s : Level)
    (extra : Finset (List Bool)) (seen : List Bool → ℕ) (A : PublicMatrix s) (seed : FixedBytes 64)
    (κ : ℕ)
    (μ : List Bool) (hμ : μ.length = 512) (adv : Xofs → SigningForger)
    (observe : Xofs → List Byte → Option Poly → Bool → α) :
    let install := H.fill256 (rows := challengeRows s extra) (width := 221) seen
    let high := fun K : Xofs => highBitsVec s.params (K.prepareAttempt s A seed.toList κ).product
    let run := fun table =>
      let K := install table
      let d := K.commitmentDigest s (high K) μ
      (K.sufCmaGame s (adv K)).map (observe K d (K.sampleInBall s d))
    ((PMF.uniformOfFintype _).bind fun table =>
      let K := install table
      let d := K.commitmentDigest s (high K) μ
      let key := K.challengeRow s extra (high K) μ
      (PMF.uniformOfFintype (FixedBytes 221)).bind fun fresh =>
        let K' := install (Function.update table key fresh)
        let tape := (H.h256.read key (seen key) ++ List.ofFn fresh).take 221
        (K'.sufCmaGame s (adv K')).map (observe K' d (sampleInBallFromBytes s tape))) =
      (PMF.uniformOfFintype _).bind run := by
  intro install high run
  let select := fun table => (install table).challengeRow s extra (high (install table)) μ
  have high_fixed table fresh : high (install (Function.update table (select table) fresh)) =
      high (install table) :=
    congrArg (fun prep : AttemptCommitment s => highBitsVec s.params prep.product)
      (prepareAttempt_fill_update H seen table A seed κ (select table)
        (length_commitmentDigest (H := install table) s (high (install table)) μ) rfl fresh)
  have digest_fixed table (fresh : FixedBytes 221) :
      let K' := install (Function.update table (select table) fresh)
      K'.commitmentDigest s (high K') μ =
        (install table).commitmentDigest s (high (install table)) μ := by
    dsimp only
    rw [high_fixed table fresh]
    exact H.h256.read_fill_update_ne seen table (select table) fresh
      (commitmentInput_ne_digestInput (high (install table)) hμ
        (length_commitmentDigest (H := install table) s (high (install table)) μ)) _
  have stable table fresh : select (Function.update table (select table) fresh) = select table :=
    Subtype.ext (congrArg Keccak.bytesToBitsLE (digest_fixed table fresh))
  rw [← PMF.uniformOfFintype_bind_bind_adaptiveUpdate select stable run]
  apply congrArg (PMF.bind _)
  funext table
  apply congrArg (PMF.bind _)
  funext fresh
  dsimp only [run]
  let updated := Function.update table (select table) fresh
  rw [sampleInBall_fill256 H seen updated (high (install updated)) μ,
    show (install updated).challengeRow s extra (high (install updated)) μ = select table from
      stable table fresh, show updated (select table) = fresh from Function.update_self ..,
    digest_fixed table fresh]

end Cslib.Crypto.MLDSA.FIPS204
