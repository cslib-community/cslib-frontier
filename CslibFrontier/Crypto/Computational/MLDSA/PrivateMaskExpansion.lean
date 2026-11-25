/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.AdaptiveKeySeed
-- Reads private `Test`, `hit`, `changed`, `gap`, and `gap_bind_le`.
import all CslibFrontier.Crypto.Computational.MLDSA.SigningQueryComparison
import CslibFrontier.Probability.PMF.UniformExtend
import CslibFrontier.Tactic.PMFSwap

/-!
# Private mask expansion in the signed ML-DSA game

[FIPS 204][NISTFIPS204], Algorithms 7 and 34, expand each call's 64-byte mask seed at
two-byte little-endian nonces. Draw the mask seeds and their raw expansion bytes before
the quantum execution, retaining the same SHAKE stream for signing, key generation,
coherent queries and verification. The strong-forgery bound charges for repeated private seeds,
for overlap with the actual key-generation or message-digest reads, and for coherent queries to
the reserved rows. Its reference signer draws the Algorithm 34 expansion bytes privately and
uses the original shared commitment hash throughout the rejection loop.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability Cslib.Quantum ExtendableOutput
open scoped Cslib.Probability.PMF ENNReal

private abbrev MaskInput (n : ℕ) := Fin n × FixedBytes 2

private def maskWord {n : ℕ} (t : Fin n ↪ FixedBytes 64) (p : MaskInput n) : List Bool :=
  Keccak.bytesToBitsLE ((t p.1).toList ++ p.2.toList)

private theorem maskWord_length {n : ℕ} (t : Fin n ↪ FixedBytes 64) (p : MaskInput n) :
    (maskWord t p).length = 528 := by
  simp [maskWord, Keccak.length_bytesToBitsLE, FixedBytes.toList]

private theorem maskWord_injective {n : ℕ} (t : Fin n ↪ FixedBytes 64) :
    Function.Injective (maskWord t) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ eq
  have he := List.append_inj (Keccak.bytesToBitsLE_injective eq) (by simp [FixedBytes.toList])
  exact Prod.ext (t.injective (List.ofFn_inj.mp he.1)) (List.ofFn_inj.mp he.2)

private def maskCells {a b n : ℕ} (ha : 528 ≤ a) (t : Fin n ↪ FixedBytes 64) :
    MaskInput n × Fin b ↪ RawWord a × Fin b where
  toFun p := (word (maskWord t p.1) ((maskWord_length ..).le.trans ha), p.2)
  inj' := by
    intro p q h
    apply Prod.ext (maskWord_injective t (word_inj (hx := (maskWord_length t p.1).le.trans ha)
      (hy := (maskWord_length t q.1).le.trans ha) (congrArg Prod.fst h)))
    exact congrArg (fun v : RawWord a × Fin b => v.2) h

private noncomputable def maskStreams {a b n : ℕ} (base : Xofs) (ha : 528 ≤ a)
    (t : Fin n ↪ FixedBytes 64) (T₁ T₂ : Table a b) (rows : MaskInput n × Fin b → Byte) :
    Xofs := streams base T₁ (Function.extend (maskCells ha t) rows T₂)

-- At every private seed, the actual SHAKE stream supplies the reserved bytes at every nonce.
private theorem maskStreams_byteAt {a b n : ℕ} (base : Xofs) (ha : 528 ≤ a)
    (t : Fin n ↪ FixedBytes 64) (T₁ T₂ : Table a b) (rows : MaskInput n × Fin b → Byte)
    (slot : MaskInput n) (j : Fin b) :
    byteAt (maskStreams base ha t T₁ T₂ rows).h256 (maskWord t slot) j = rows (slot, j) := by
  let e := maskCells (b := b) ha t
  have len : (maskWord t slot).length ≤ a := (maskWord_length t slot).le.trans ha
  change byteAt (install base.h256 (Function.extend e rows T₂)) (maskWord t slot) j = _
  rw [byteAt_install, dite_eq_left ⟨len, j.isLt⟩]
  exact e.injective.extend_apply rows T₂ (slot, j)

private theorem maskStreams_off {a b n : ℕ} (base : Xofs) (ha : 528 ≤ a)
    (t : Fin n ↪ FixedBytes 64) (T₁ T₂ : Table a b) (rows : MaskInput n × Fin b → Byte)
    (x : List Bool) (miss : ∀ p, maskWord t p ≠ x) (k : ℕ) :
    (maskStreams base ha t T₁ T₂ rows).h256.read x k = (streams base T₁ T₂).h256.read x k := by
  apply read_eq_of_byteAt_eq
  intro i _
  simp only [maskStreams, streams, byteAt_install]
  split
  · rename_i length
    apply Function.extend_apply'
    rintro ⟨p, hp⟩
    exact miss p.1 (word_inj (hx := (maskWord_length ..).le.trans ha) (hy := length.1)
      (congrArg Prod.fst hp))
  · rfl

private theorem maskStreams_off_length {a b n : ℕ} (base : Xofs) (ha : 528 ≤ a)
    (t : Fin n ↪ FixedBytes 64) (T₁ T₂ : Table a b) (rows : MaskInput n × Fin b → Byte) :
    Unchanged (maskStreams base ha t T₁ T₂ rows) (streams base T₁ T₂) 528 :=
  fun x len => maskStreams_off base ha t T₁ T₂ rows x fun p h => len (h ▸ maskWord_length t p)

-- A fixed raw word can intersect the reserved rows at only one 64-byte seed.
private noncomputable def prefixSeed (x : List Bool) : FixedBytes 64 := by
  classical
  exact if h : ∃ r : FixedBytes 64, ∃ y, Keccak.bytesToBitsLE r.toList ++ y = x
  then h.choose else 0

private theorem prefixSeed_append (r : FixedBytes 64) (y : List Bool) :
    prefixSeed (Keccak.bytesToBitsLE r.toList ++ y) = r := by
  classical
  let h : ∃ v : FixedBytes 64, ∃ tail, Keccak.bytesToBitsLE v.toList ++ tail =
      Keccak.bytesToBitsLE r.toList ++ y := ⟨r, y, rfl⟩
  rw [prefixSeed, dite_eq_left h]
  obtain ⟨rest, eq⟩ := h.choose_spec
  exact List.ofFn_inj.mp (Keccak.bytesToBitsLE_injective (List.append_inj eq
    (by simp only [Keccak.length_bytesToBitsLE, FixedBytes.toList, List.length_ofFn])).1)

private theorem maskStreams_off_prefix {a b n : ℕ} (base : Xofs) (ha : 528 ≤ a)
    (t : Fin n ↪ FixedBytes 64) (T₁ T₂ : Table a b) (rows : MaskInput n × Fin b → Byte)
    (x : List Bool) (miss : prefixSeed x ∉ Set.range t) (k : ℕ) :
    (maskStreams base ha t T₁ T₂ rows).h256.read x k = (streams base T₁ T₂).h256.read x k := by
  apply maskStreams_off
  rintro ⟨i, nonce⟩ rfl
  apply miss
  have eq : maskWord t (i, nonce) =
      Keccak.bytesToBitsLE (t i).toList ++ Keccak.bytesToBitsLE nonce.toList :=
    List.flatMap_append ..
  rw [eq, prefixSeed_append]
  exact ⟨i, rfl⟩

private def secretSeed (H : Xofs) (s : Level) (seed : FixedBytes 32) : List Byte :=
  ((H.expandKeySeed s seed).drop 32).take 64

private theorem secretSeed_length (H : Xofs) (s : Level) (seed : FixedBytes 32) :
    (secretSeed H s seed).length = 64 := by
  simp [secretSeed, Xofs.expandKeySeed, H.h256.length_read]

private theorem keyGen_maskStreams {a b n : ℕ} (base : Xofs) (ha : 528 ≤ a)
    (t : Fin n ↪ FixedBytes 64) (T₁ T₂ : Table a b) (rows : MaskInput n × Fin b → Byte)
    (s : Level) (seed : FixedBytes 32) (miss : ∀ i, (t i).toList ≠
      secretSeed (streams base T₁ T₂) s seed) :
    (maskStreams base ha t T₁ T₂ rows).keyGen s seed = (streams base T₁ T₂).keyGen s seed := by
  have raw := maskStreams_off_length base ha t T₁ T₂ rows
  apply Xofs.keyGen_congr_of_reads (H := streams base T₁ T₂)
    (G := maskStreams base ha t T₁ T₂ rows) s seed rfl
  · rw [Xofs.expandKeySeed, Xofs.expandKeySeed]
    exact raw _ (by rw [length_keySeedInput]; decide) _
  · intro nonce
    dsimp only [ExtendableOutput.readBytes]
    apply maskStreams_off
    rintro ⟨i, suf⟩ eq
    have bs : (t i).toList ++ suf.toList = nonceInput (secretSeed (streams base T₁ T₂) s seed)
        nonce := Keccak.bytesToBitsLE_injective eq
    exact miss i (List.append_inj bs (by rw [FixedBytes.length_toList, secretSeed_length])).1
  · intro pk len
    apply raw
    rw [Keccak.length_bytesToBitsLE, len]
    cases s <;> decide

private abbrev ExpansionRow (b : ℕ) := FixedBytes 2 → Fin b → Byte

private def slotRow {n b : ℕ} {s : Level} (hb : maskPolyBytes s ≤ b)
    (rows : MaskInput n × Fin b → Byte) (i : Fin n) : ExpansionRow (maskPolyBytes s) :=
  fun suffix j => rows ((i, suffix), j.castLE hb)

private theorem expandMask_maskStreams {a b n : ℕ} (base : Xofs) (ha : 528 ≤ a)
    (s : Level) (hb : maskPolyBytes s ≤ b) (t : Fin n ↪ FixedBytes 64) (T₁ T₂ : Table a b)
    (rows : MaskInput n × Fin b → Byte) (i : Fin n) (counter : ℕ) :
    ringVectorCoeffs ((maskStreams base ha t T₁ T₂ rows).expandMask s (t i).toList counter) =
      ringVectorCoeffs (maskFromRow s (slotRow hb rows i) counter) := by
  let G := maskStreams base ha t T₁ T₂ rows
  have read (v : ℕ) : G.h256.readBytes (nonceInput (t i).toList v) (maskPolyBytes s) =
      List.ofFn (slotRow hb rows i (nonceSuffix v)) := by
    have raw : Keccak.bytesToBitsLE (nonceInput (t i).toList v) =
        maskWord t (i, nonceSuffix v) := by
      simp [nonceInput, maskWord, FixedBytes.toList, List.ofFn_succ]
    change G.h256.read _ _ = _
    rw [raw]
    apply List.ext_getElem
    · rw [G.h256.length_read, List.length_ofFn]
    · intro j hj _
      have small : j < maskPolyBytes s := hj.trans_le (G.h256.length_read ..).le
      rw [getElem_read _ _ small, List.getElem_ofFn]
      exact maskStreams_byteAt base ha t T₁ T₂ rows (i, nonceSuffix v) ⟨j, small.trans_le hb⟩
  simp only [Xofs.expandMask, ← show G = maskStreams base ha t T₁ T₂ rows from rfl,
    maskFromRow, read]
  rfl

private def Xofs.signWithExpansionRow (H : Xofs) (s : Level) (key : List Byte)
    (q : SigningQuery) (row : ExpansionRow (maskPolyBytes s)) : Option (List Byte) := do
  guard (q.context.length ≤ 255)
  let sk ← decodePrivate s key
  let A ← H.expandA s sk.rho
  let μ := H.representativeFromTr sk.tr (formatMessage q.message q.context)
  H.signingRetries s sk A μ (maskFromRow s row)

private theorem nonce_commitment_ne (s : Level)
    (w : Fin s.params.k → Fin 256 → ℤ) {μ : List Bool} (len : μ.length = 512) :
    (commitmentInput s w μ).length ≠ 528 := by
  rw [commitmentInput_length s w len]
  cases s <;> decide

-- Every commitment and sparse challenge read in an attempt has a different length from
-- the 66-byte nonce input, at each of the three FIPS levels.
private theorem maskStreams_attempt {a b n : ℕ} (base : Xofs) (ha : 528 ≤ a)
    (s : Level) (hb : maskPolyBytes s ≤ b) (t : Fin n ↪ FixedBytes 64) (T₁ T₂ : Table a b)
    (rows : MaskInput n × Fin b → Byte) (sk : PrivateKey s) (A : PublicMatrix s)
    {μ : List Bool} (hμ : μ.length = 512) (i : Fin n) (counter : ℕ) :
    (maskStreams base ha t T₁ T₂ rows).attempt s sk A μ (t i).toList counter =
      (streams base T₁ T₂).attemptWithMask s sk A μ
        (ringVectorCoeffs (maskFromRow s (slotRow hb rows i) counter)) := by
  let G := maskStreams base ha t T₁ T₂ rows
  let H := streams base T₁ T₂
  have raw := maskStreams_off_length base ha t T₁ T₂ rows
  have digest w : G.commitmentDigest s w μ = H.commitmentDigest s w μ :=
    raw _ (nonce_commitment_ne s w hμ) _
  have challenge w : G.sampleInBall s (H.commitmentDigest s w μ) =
      H.sampleInBall s (H.commitmentDigest s w μ) :=
    challenge_unchanged raw s (by rw [length_commitmentDigest]; cases s <;> decide)
  rw [Xofs.attempt, expandMask_maskStreams base ha s hb]
  simp only [Xofs.attemptWithMask,
    ← show G = maskStreams base ha t T₁ T₂ rows from rfl,
    ← show H = streams base T₁ T₂ from rfl, digest, challenge]

private noncomputable def trSeed (H : Xofs) (keys : Option KeyPair) : FixedBytes 64 :=
  prefixSeed (Keccak.bytesToBitsLE
    ((keys.map fun key => H.h256.readBytes key.publicKey 64).getD []))

private theorem prefixSeed_toList (xs : List Byte) (len : xs.length = 64) :
    (prefixSeed (Keccak.bytesToBitsLE xs)).toList = xs := by
  obtain ⟨r, rfl⟩ := FixedBytes.exists_toList len
  rw [← List.append_nil (Keccak.bytesToBitsLE _), prefixSeed_append]

private theorem rep_maskStreams {a b n : ℕ} (base : Xofs) (ha : 528 ≤ a)
    (t : Fin n ↪ FixedBytes 64) (T₁ T₂ : Table a b) (rows : MaskInput n × Fin b → Byte)
    (tr : List Byte) (len : tr.length = 64)
    (miss : prefixSeed (Keccak.bytesToBitsLE tr) ∉ Set.range t) (m : List Bool) :
    (maskStreams base ha t T₁ T₂ rows).representativeFromTr tr m =
      (streams base T₁ T₂).representativeFromTr tr m := by
  obtain ⟨r, rfl⟩ := FixedBytes.exists_toList len
  apply congrArg Keccak.bytesToBitsLE
  apply maskStreams_off_prefix
  rw [representativeInput, prefixSeed_append]
  rwa [← List.append_nil (Keccak.bytesToBitsLE r.toList), prefixSeed_append] at miss


private theorem sign_maskStreams {a b n : ℕ} (base : Xofs) (ha : 528 ≤ a)
    (s : Level) (hb : maskPolyBytes s ≤ b) (t : Fin n ↪ FixedBytes 64) (T₁ T₂ : Table a b)
    (rows : MaskInput n × Fin b → Byte) {seed : FixedBytes 32} {keys : KeyPair}
    (hk : (streams base T₁ T₂).keyGen s seed = some keys)
    (miss : trSeed (streams base T₁ T₂) (some keys) ∉ Set.range t) (i : Fin n) (q : SigningQuery) :
    (maskStreams base ha t T₁ T₂ rows).signWithRow s keys.secretKey q (fun _ => t i) =
      (streams base T₁ T₂).signWithExpansionRow s keys.secretKey q
        (slotRow hb rows i) := by
  let G := maskStreams base ha t T₁ T₂ rows
  let H := streams base T₁ T₂
  obtain ⟨rho, sk, matrix, _, dec, _⟩ := privateKey_of_keyGen hk
  let tr := H.h256.readBytes keys.publicKey 64
  let msg := formatMessage q.message q.context
  change H.expandA s rho.toList = some sk.A at matrix
  change decodePrivate s keys.secretKey = some ⟨rho.toList, (H.expandKeySeed s seed).drop 96, tr,
    sk.s₁, sk.s₂, publicKeyLowPart s.params 13 sk.publicKey⟩ at dec
  have ht : tr.length = 64 := H.h256.length_read ..
  have rep : G.representativeFromTr tr msg = H.representativeFromTr tr msg :=
    rep_maskStreams base ha t T₁ T₂ rows tr ht miss msg
  have mat : G.expandA s rho.toList = some sk.A :=
    (Xofs.expandA_congr (K := G) (H := H) rfl s rho.toList).trans matrix
  change G.signWithRow s keys.secretKey q (fun _ => t i) = H.signWithExpansionRow s _ q _
  by_cases ctx : q.context.length ≤ 255
  · simp only [Xofs.signWithRow, Xofs.runSigning, Xofs.startSigningWithSeed,
      Xofs.startDecodedSigning, Xofs.signWithExpansionRow, ctx, guard, ↓reduceIte,
      Option.pure_def, Option.bind_eq_bind, Option.bind_some, dec, mat, matrix,
      ← show msg = formatMessage q.message q.context from rfl, rep]
    apply congrArg (fun f => firstAccepted s.params.ℓ f 814 0)
    funext counter
    exact maskStreams_attempt base ha s hb t T₁ T₂ rows _ sk.A
      (length_messageRepresentative H keys.publicKey msg) i counter
  · simp [Xofs.signWithRow, Xofs.signWithExpansionRow, guard, ctx]

private theorem verify_maskStreams {a b n : ℕ} (base : Xofs) (ha : 528 ≤ a)
    (s : Level) (t : Fin n ↪ FixedBytes 64) (T₁ T₂ : Table a b) (rows : MaskInput n × Fin b → Byte)
    {seed : FixedBytes 32} {keys : KeyPair} (hk : (streams base T₁ T₂).keyGen s seed = some keys)
    (miss : trSeed (streams base T₁ T₂) (some keys) ∉ Set.range t) (f : Forgery) :
    (maskStreams base ha t T₁ T₂ rows).verify s keys.publicKey f.message f.context f.signature =
      (streams base T₁ T₂).verify s keys.publicKey f.message f.context f.signature := by
  let H := streams base T₁ T₂
  have raw := maskStreams_off_length base ha t T₁ T₂ rows
  have pk : (maskStreams base ha t T₁ T₂ rows).h256.readBytes keys.publicKey 64 =
      H.h256.readBytes keys.publicKey 64 := by
    apply raw
    obtain ⟨rho, sk, _, enc, _, _⟩ := privateKey_of_keyGen hk
    rw [Keccak.length_bytesToBitsLE, enc, length_encodePublic, FixedBytes.length_toList]
    cases s <;> decide
  refine verify_eq_of_reads (G := maskStreams base ha t T₁ T₂ rows) (H := H) s keys.publicKey
    rfl raw (by decide) (nonce_commitment_ne s) ?_ f
  intro m
  simp only [Xofs.messageRepresentative, pk]
  exact rep_maskStreams base ha t T₁ T₂ rows _ (H.h256.length_read ..) miss m

private theorem uniform_maskStreams {a b n : ℕ} (base : Xofs) (ha : 528 ≤ a)
    (t : Fin n ↪ FixedBytes 64) {α : Type} (run : Xofs → PMF α) :
    ((PMF.uniformOfFintype (Table a b)).bind fun T₁ =>
      (PMF.uniformOfFintype (Table a b)).bind fun T₂ =>
      (PMF.uniformOfFintype (MaskInput n × Fin b → Byte)).bind fun rows =>
      run (maskStreams base ha t T₁ T₂ rows)) = (base.uniformPrefixes a b).bind run := by
  rw [← sample_streams, PMF.bind_bind]
  refine congrArg (PMF.bind _ ·) (funext fun T₁ => ?_)
  rw [PMF.bind_map]
  exact PMF.uniformOfFintype_bind_bind_extend (maskCells ha t) (fun T₂ => run (streams base T₁ T₂))

namespace QuantumSigningForger

private theorem card_maskSeed : Fintype.card (FixedBytes 64) = 2 ^ 512 := by
  change Fintype.card (Fin 64 → Fin 256) = _
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  rw [show (256 : ℕ) = 2 ^ 8 by decide, ← pow_mul]

private theorem maskSeedEmbedding {n : ℕ} (h : n ≤ 2 ^ 512) :
    Nonempty (Fin n ↪ FixedBytes 64) :=
  Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin, card_maskSeed] using h)

private noncomputable def seedTapeTranscript (C : QuantumSigningForger) (H : Xofs) (s : Level)
    (keys : KeyPair) (tape : List (FixedBytes 64)) : PMF (Forgery × List Forgery) :=
  C.signingTapeTranscript H keys.publicKey
    (fun r q => H.signWithRow s keys.secretKey q (fun _ => r)) tape

private theorem uniform_seedTapeTranscript (C : QuantumSigningForger) (H : Xofs) (s : Level)
    (keys : KeyPair) {n : ℕ} (hn : C.SigningCallsLe n) :
    ((PMF.uniformOfFintype (Fin n → FixedBytes 64)).bind fun t =>
      C.seedTapeTranscript H s keys (List.ofFn t)) = C.privateTranscript H s keys :=
  C.uniform_signingTapeTranscript H keys.publicKey
    (fun (r : FixedBytes 64) q => H.signWithRow s keys.secretKey q (fun _ => r)) hn

private noncomputable def maskTapeScore (C : QuantumSigningForger) (H : Xofs) (s : Level)
    (tape : List (FixedBytes 64)) : Game :=
  (PMF.uniformOfFintype (FixedBytes 32)).bind fun seed =>
    scoreTranscript H s SignedMatrixTrial.newDigestWin (H.keyGen s seed)
      (fun keys => C.seedTapeTranscript H s keys tape)

private noncomputable def expansionTranscript (C : QuantumSigningForger) (device H : Xofs)
    (s : Level) (keys : KeyPair) (tape : List (ExpansionRow (maskPolyBytes s))) :
    PMF (Forgery × List Forgery) :=
  C.signingTapeTranscript device keys.publicKey
    (fun row q => H.signWithExpansionRow s keys.secretKey q row) tape

private noncomputable def expansionScore (C : QuantumSigningForger) (device H : Xofs)
    (s : Level) (seed : FixedBytes 32) (tape : List (ExpansionRow (maskPolyBytes s))) : Game :=
  scoreTranscript H s SignedMatrixTrial.newDigestWin (H.keyGen s seed)
    (fun keys => C.expansionTranscript device H s keys tape)

private def goodForSetup {n : ℕ} (H : Xofs) (s : Level) (seed : FixedBytes 32)
    (t : Fin n ↪ FixedBytes 64) : Prop :=
  prefixSeed (Keccak.bytesToBitsLE (secretSeed H s seed)) ∉ Set.range t ∧
    trSeed H (H.keyGen s seed) ∉ Set.range t

private theorem maskScore_eq {a b n : ℕ} (C : QuantumSigningForger) (s : Level)
    (base : Xofs) (ha : 528 ≤ a) (hb : maskPolyBytes s ≤ b) (hn : C.SigningCallsLe n)
    (t : Fin n ↪ FixedBytes 64) (T₁ T₂ : Table a b) (rows : MaskInput n × Fin b → Byte)
    (seed : FixedBytes 32) (good : goodForSetup (streams base T₁ T₂) s seed t) :
    let G := maskStreams base ha t T₁ T₂ rows
    let H := streams base T₁ T₂
    scoreTranscript G s SignedMatrixTrial.newDigestWin (G.keyGen s seed)
      (fun keys => C.seedTapeTranscript G s keys (List.ofFn t)) =
      C.expansionScore G H s seed (List.ofFn (slotRow hb rows)) := by
  intro G H
  have kg : G.keyGen s seed = H.keyGen s seed :=
    keyGen_maskStreams base ha t T₁ T₂ rows s seed fun i eq => good.1 ⟨i, List.ofFn_inj.mp
      (eq.trans (prefixSeed_toList (secretSeed H s seed) (secretSeed_length ..)).symm)⟩
  simp only [expansionScore, scoreTranscript, withTrialSetup, kg, Xofs.expandA_congr
    (H := H) (K := G) rfl]
  cases hk : H.keyGen s seed with
  | none => rfl
  | some keys =>
    have miss : trSeed H (some keys) ∉ Set.range t := hk ▸ good.2
    dsimp only
    cases hA : H.expandA s (keys.publicKey.take 32) with
    | none => rfl
    | some A =>
      let fs := fun r => C.rowCommand G s keys (fun _ => r)
      let gs := fun (row : ExpansionRow (maskPolyBytes s)) =>
        C.signingCommand G fun q => H.signWithExpansionRow s keys.secretKey q row
      let tape := List.ofFn (slotRow hb rows)
      have run := OracleComp.IsCostBounded.run_interpret_sampleListWhen_congr isSigningCall
        (hn keys.publicKey) (0 : FixedBytes 64) (0 : ExpansionRow (maskPolyBytes s)) fs gs (by
          rintro (k | cmd | ask) h
          iterate 2 simp only [fs, gs, rowCommand, signingCommand, OracleComp.sumHandler]
          contradiction) (List.ofFn t) tape (by simp) (by
            apply List.forall₂_of_length_eq_of_get (by simp [tape])
            rintro j h₁ h₂ (coin | cmd | ask) on
            iterate 2 contradiction
            simp only [tape, List.get_ofFn, Fin.cast_mk, fs, gs, rowCommand, signingCommand,
              OracleComp.sumHandler]
            rw [show ∀ i, G.signWithRow s keys.secretKey ask (fun _ => t i) =
              H.signWithExpansionRow s keys.secretKey ask (slotRow hb rows i)
              from fun i => sign_maskStreams base ha s hb t T₁ T₂ rows hk miss i ask])
        C.initial
      have transcripts : C.seedTapeTranscript G s keys (List.ofFn t) =
          C.expansionTranscript G H s keys tape := by
        simpa only [seedTapeTranscript, expansionTranscript, signingTapeTranscript, rowCommand,
          PMF.map_comp, Function.comp_def, fs, gs, Width, probOracleSpec]
          using congrArg (PMF.map fun x => (x.1, x.2.2)) run
      dsimp only
      rw [transcripts]
      exact congrArg (PMF.map · _) (funext fun ⟨f, log⟩ =>
        congrArg (fun v : Option Bool => (v.getD false && !log.contains f) &&
          !log.any (fun g => g.signature.take (digestBytes s) == f.signature.take (digestBytes s)))
          (verify_maskStreams base ha s t T₁ T₂ rows hk miss f))

private theorem prob_maskSeed_mem {n : ℕ} [Nonempty (Fin n ↪ FixedBytes 64)] (x : FixedBytes 64) :
    ((PMF.uniformOfFintype (Fin n ↪ FixedBytes 64)).toOuterMeasure
      {t | x ∈ Set.range t}).toReal = n / 2 ^ 512 := by
  simpa only [Fintype.card_fin, card_maskSeed, Nat.cast_pow, Nat.cast_ofNat] using
    prob_uniformOfFintype_embedding_mem_range (ι := Fin n) x

private theorem setup_advantage_le {a b n : ℕ} [Nonempty (Fin n ↪ FixedBytes 64)]
    (C : QuantumSigningForger) (s : Level) (base : Xofs) (ha : 528 ≤ a) (hb : maskPolyBytes s ≤ b)
    (hn : C.SigningCallsLe n) (T₁ T₂ : Table a b) (rows : MaskInput n × Fin b → Byte)
    (seed : FixedBytes 32) :
    let tapes := PMF.uniformOfFintype (Fin n ↪ FixedBytes 64)
    let H := streams base T₁ T₂
    let G := fun t => maskStreams base ha t T₁ T₂ rows
    (Game.advantage (tapes.bind fun t => scoreTranscript (G t) s SignedMatrixTrial.newDigestWin
      ((G t).keyGen s seed) (fun keys => C.seedTapeTranscript (G t) s keys (List.ofFn t)))
      (tapes.bind fun t => C.expansionScore (G t) H s seed
        (List.ofFn (slotRow hb rows))) : ℝ) ≤ 2 * n / 2 ^ 512 := by
  intro tapes H G
  let hit (x : FixedBytes 64) := {t : Fin n ↪ FixedBytes 64 | x ∈ Set.range t}
  let short := prefixSeed (Keccak.bytesToBitsLE (secretSeed H s seed))
  let tr := trSeed H (H.keyGen s seed)
  have close := Interactive.CloseTo.bind_of_eq_on tapes _ _ (hit short ∪ hit tr)
    fun t _ h => maskScore_eq C s base ha hb hn t T₁ T₂ rows seed
      ⟨fun hs => h (Or.inl hs), fun ht => h (Or.inr ht)⟩
  have union := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨PMF.toOuterMeasure_ne_top _ _, PMF.toOuterMeasure_ne_top _ _⟩)
    (MeasureTheory.measure_union_le (μ := tapes.toOuterMeasure) (hit short) (hit tr))
  rw [ENNReal.toReal_add (PMF.toOuterMeasure_ne_top _ _) (PMF.toOuterMeasure_ne_top _ _),
    prob_maskSeed_mem short, prob_maskSeed_mem tr] at union
  exact (ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _)
    (Game.closeTo_iff_coe_advantage_le.mp close)).trans
    (union.trans_eq (by rw [← add_div, two_mul]))

private noncomputable def addressSeed (C : QuantumSigningForger) (a : Option (Address C)) :
    FixedBytes 64 :=
  prefixSeed ((a.bind fun addr => Xofs.unpad
    (List.ofFn (fun i : Fin (C.addressBits + 1) => addr i.succ))).getD [])

private theorem changed_implies_seed {a b n : ℕ} (C : QuantumSigningForger) (base : Xofs)
    (ha : 528 ≤ a) (t : Fin n ↪ FixedBytes 64) (T₁ T₂ : Table a b)
    (rows : MaskInput n × Fin b → Byte) (addr : Option (Address C))
    (changeAt : addr.any (changed C (maskStreams base ha t T₁ T₂ rows) (streams base T₁ T₂))) :
    addressSeed C addr ∈ Set.range t := by
  cases addr with
  | none => contradiction
  | some v =>
    by_contra miss
    simp only [Option.any_some, changed, decide_eq_true_eq] at changeAt
    apply changeAt
    rw [Xofs.queryTable, Xofs.queryTable]
    cases hx : Xofs.unpad (List.ofFn fun i : Fin (C.addressBits + 1) => v i.succ) with
    | none => rfl
    | some x =>
      cases tag : v 0 with
      | false => rfl
      | true =>
        have h : prefixSeed x ∉ Set.range t := by
          simpa only [addressSeed, Option.bind_some, hx, Option.getD_some] using miss
        simp only [↓reduceIte, maskStreams_off_prefix base ha t T₁ T₂ rows x h]

private theorem fixedHit_le {a b n : ℕ} [Nonempty (Fin n ↪ FixedBytes 64)]
    (C : QuantumSigningForger) (base : Xofs) (ha : 528 ≤ a) (T₁ T₂ : Table a b)
    (rows : MaskInput n × Fin b → Byte) (addr : Option (Address C)) :
    let tapes := PMF.uniformOfFintype (Fin n ↪ FixedBytes 64)
    let H := streams base T₁ T₂
    (tapes.bind fun t => PMF.pure (addr.any
      (changed C (maskStreams base ha t T₁ T₂ rows) H))) true ≤ ENNReal.ofReal (n / 2 ^ 512) := by
  classical
  intro tapes H
  let f := fun t => addr.any (changed C (maskStreams base ha t T₁ T₂ rows) H)
  have eq : (tapes.bind fun t => PMF.pure (f t)) =
      tapes.bind fun t => PMF.pure (decide (f t = true)) :=
    congrArg (tapes.bind ·) (funext fun t => by cases f t <;> rfl)
  rw [eq, PMF.bind_pure_decide_apply_true]
  exact (tapes.toOuterMeasure.mono fun t ht =>
    changed_implies_seed C base ha t T₁ T₂ rows addr ht).trans
    ((ENNReal.le_ofReal_iff_toReal_le (PMF.toOuterMeasure_ne_top _ _) (by positivity)).mpr
      (prob_maskSeed_mem (addressSeed C addr)).le)

private theorem expansionScore_gap_le {a b n m : ℕ} [Nonempty (Fin n ↪ FixedBytes 64)]
    (C : QuantumSigningForger) (s : Level) (base : Xofs) (ha : 528 ≤ a) (hb : maskPolyBytes s ≤ b)
    (hm : C.XofCallsLe m)
    (T₁ T₂ : Table a b) (rows : MaskInput n × Fin b → Byte) (seed : FixedBytes 32) :
    let H := streams base T₁ T₂
    let G := fun t => maskStreams base ha t T₁ T₂ rows
    let tape := List.ofFn (slotRow hb rows)
    gap ((PMF.uniformOfFintype (Fin n ↪ FixedBytes 64)).bind fun t =>
      C.expansionScore (G t) H s seed tape) (C.expansionScore H H s seed tape) ≤
      4 * m * m * (n / 2 ^ 512) := by
  classical
  intro H G tape
  let tapes := PMF.uniformOfFintype (Fin n ↪ FixedBytes 64)
  simp only [expansionScore, scoreTranscript, withTrialSetup]
  cases hkey : H.keyGen s seed with
  | none => simp only [PMF.bind_const, gap, sub_self, zero_pow (by decide : 2 ≠ 0)]; positivity
  | some keys =>
    dsimp only
    cases hA : H.expandA s (keys.publicKey.take 32) with
    | none => simp only [PMF.bind_const, gap, sub_self, zero_pow (by decide : 2 ≠ 0)]; positivity
    | some A =>
      let prog := C.program keys.publicKey
      let sign := fun (row : ExpansionRow (maskPolyBytes s)) (q : SigningQuery) =>
        H.signWithExpansionRow s keys.secretKey q row
      let test := fun (f : Forgery) (log : List Forgery)
          (_ : List (ExpansionRow (maskPolyBytes s))) =>
        (POVM.const (SignedMatrixTrial.newDigestWin ⟨H, A, keys.publicKey, f, log⟩) : Test C)
      have law (T : Xofs) :
          (C.expansionTranscript T H s keys tape).map (fun (f, log) =>
            SignedMatrixTrial.newDigestWin ⟨H, A, keys.publicKey, f, log⟩) =
          scored prog T sign test C.initial.1 C.initial.2 tape := by
        simp only [expansionTranscript, signingTapeTranscript, scored, test,
          POVM.measureDensity_const, PMF.map_comp, Function.comp_def]
        rfl
      let run (T : Xofs) := scored prog T sign test C.initial.1 C.initial.2 tape
      let hits t j := hit prog (G t) H sign C.initial.1 C.initial.2 tape j
      have comparison := gap_bind_le tapes (fun t => run (G t)) (fun _ => run H) hits m
        fun t => scored_gap_le (hm keys.publicKey) (G t) H sign test C.initial.1 C.initial.2 tape
      rw [PMF.bind_const] at comparison
      simp only [law]
      apply comparison.trans
      calc
        _ ≤ 4 * m * ∑ _j ∈ Finset.range m, (n / 2 ^ 512 : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine Finset.sum_le_sum fun j _ => ?_
          have h := hit_mean_le tapes G H prog sign C.initial.1 C.initial.2 tape j
            (fixedHit_le C base ha T₁ T₂ rows)
          simpa only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ n / 2 ^ 512)]
            using ENNReal.toReal_mono ENNReal.ofReal_ne_top h
        _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc]

private theorem privateMaskSeedGame_eq_tape (C : QuantumSigningForger) (s : Level)
    (base : Xofs) (a b : ℕ) {n : ℕ} (hn : C.SigningCallsLe n) :
    C.privateMaskSeedGame s base a b =
      (PMF.uniformOfFintype (Fin n → FixedBytes 64)).bind fun t =>
        (base.uniformPrefixes a b).bind fun H => C.maskTapeScore H s (List.ofFn t) := by
  simp only [privateMaskSeedGame, maskTapeScore, PMF.monad_bind_eq_bind]
  symm
  pmf_swap with H
  pmf_swap with seed
  simp only [scoreTranscript, withTrialSetup]
  cases hg : H.keyGen s seed with
  | none => simp
  | some keys =>
    dsimp only
    cases hA : H.expandA s (keys.publicKey.take 32) with
    | none => simp
    | some A =>
      simpa only [PMF.map_bind] using congrArg
        (PMF.map fun (f, log) => SignedMatrixTrial.newDigestWin ⟨H, A, keys.publicKey, f, log⟩)
        (C.uniform_seedTapeTranscript H s keys hn)

/-- Fresh-digest forgery with distinct private mask seeds and independently sampled SHAKE256
rows at those seeds and all two-byte nonces. The keys, actual signer, quantum device and
verifier all use the oracle containing the reserved rows. -/
private noncomputable def maskExpansionGame (C : QuantumSigningForger) (s : Level) (base : Xofs)
    {a b n : ℕ} (ha : 528 ≤ a) (hsize : n ≤ 2 ^ 512) : Game :=
  let _ : Nonempty (Fin n ↪ FixedBytes 64) := maskSeedEmbedding hsize
  do
    let t ← PMF.uniformOfFintype (Fin n ↪ FixedBytes 64)
    let T₁ ← PMF.uniformOfFintype (Table a b)
    let T₂ ← PMF.uniformOfFintype (Table a b)
    let rows ← PMF.uniformOfFintype (MaskInput n × Fin b → Byte)
    C.maskTapeScore (maskStreams base ha t T₁ T₂ rows) s (List.ofFn t)

/-- Reserving the private mask expansions in the whole shared-XOF forgery game costs at most
the probability of a collision among the 512-bit per-call mask seeds. -/
private theorem dist_privateMaskSeedGame_maskExpansionGame (C : QuantumSigningForger) (s : Level)
    (base : Xofs) {a b n : ℕ} (ha : 528 ≤ a) (hn : C.SigningCallsLe n)
    (hsize : n ≤ 2 ^ 512) :
    dist (C.privateMaskSeedGame s base a b) (C.maskExpansionGame s base (b := b) ha hsize) ≤
      ((n * (n - 1) : ℕ) : ℝ) / 2 ^ 513 := by
  classical
  let _ := maskSeedEmbedding hsize
  let run (t : Fin n → FixedBytes 64) := (base.uniformPrefixes a b).bind fun H =>
    C.maskTapeScore H s (List.ofFn t)
  have eq : C.maskExpansionGame s base (b := b) ha hsize =
      ((PMF.uniformOfFintype (Fin n ↪ FixedBytes 64)).map DFunLike.coe).bind run := by
    simp only [maskExpansionGame, PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def]
    exact congrArg (PMF.bind _ ·) (funext fun t =>
      uniform_maskStreams base ha t fun H => C.maskTapeScore H s (List.ofFn t))
  rw [C.privateMaskSeedGame_eq_tape s base a b hn, eq, dist_comm]
  simpa only [Fintype.card_fin, card_maskSeed, Nat.cast_pow, Nat.cast_ofNat, ← pow_succ'] using
    (PMF.dist_bind_le _ _ run).trans
      (dist_uniform_embedding_to_fun (by simpa only [Fintype.card_fin, card_maskSeed] using hsize))

private noncomputable def freshExpansionTranscript (C : QuantumSigningForger) (s : Level)
    (H : Xofs) (keys : KeyPair) : PMF (Forgery × List Forgery) :=
  C.sampledSigningTranscript H keys.publicKey
    (fun row q => H.signWithExpansionRow s keys.secretKey q row)

/-- Fresh-digest forgery when the signer draws the raw Algorithm 34 expansion bytes
independently for each signing call and two-byte nonce, at the width of the parameter set.
All retries use the FIPS decoder and commitment hash. The device and verifier use the same XOFs. -/
noncomputable def freshExpansionGame (C : QuantumSigningForger) (s : Level)
    (base : Xofs) (a b : ℕ) : Game := do
  let H ← base.uniformPrefixes a b
  let seed ← PMF.uniformOfFintype (FixedBytes 32)
  scoreTranscript H s SignedMatrixTrial.newDigestWin (H.keyGen s seed)
    (C.freshExpansionTranscript s H)

private def slotRows {n b : ℕ} : (MaskInput n × Fin b → Byte) ≃ (Fin n → ExpansionRow b) where
  toFun f i suffix j := f ((i, suffix), j)
  invFun f p := f p.1.1 p.1.2 p.2
  left_inv _ := rfl
  right_inv _ := rfl

private theorem uniform_expansionTranscript (C : QuantumSigningForger) (s : Level) (H : Xofs)
    {n b : ℕ} (hb : maskPolyBytes s ≤ b) (keys : KeyPair) (hn : C.SigningCallsLe n) :
    ((PMF.uniformOfFintype (MaskInput n × Fin b → Byte)).bind fun rows =>
      C.expansionTranscript H H s keys (List.ofFn (slotRow hb rows))) =
      C.freshExpansionTranscript s H keys := by
  have law := C.uniform_signingTapeTranscript H keys.publicKey
    (fun row q => H.signWithExpansionRow s keys.secretKey q row) hn
  let restrict := (Function.Embedding.refl (MaskInput n)).prodMap (Fin.castLEEmb hb)
  have project (r : MaskInput n × Fin b → Byte) :
      slotRows (fun v => r (restrict v)) = slotRow hb r := rfl
  rw [← PMF.uniformOfFintype_map_equiv (slotRows (n := n) (b := maskPolyBytes s)),
    ← PMF.uniformOfFintype_pi_map_comp_embedding (α := Byte) restrict,
    PMF.map_comp, PMF.bind_map] at law
  simpa only [expansionTranscript, freshExpansionTranscript, Function.comp_def, project] using law

private noncomputable def expansionSetup {α : Type} {a b n : ℕ}
    (run : Table a b → Table a b → (MaskInput n × Fin b → Byte) → FixedBytes 32 → PMF α) :
    PMF α := do
  let T₁ ← PMF.uniformOfFintype (Table a b)
  let T₂ ← PMF.uniformOfFintype (Table a b)
  let rows ← PMF.uniformOfFintype (MaskInput n × Fin b → Byte)
  let seed ← PMF.uniformOfFintype (FixedBytes 32)
  run T₁ T₂ rows seed

private theorem freshExpansionGame_eq_setup (C : QuantumSigningForger) (s : Level)
    (base : Xofs) {a b n : ℕ} (hb : maskPolyBytes s ≤ b) (hn : C.SigningCallsLe n) :
    C.freshExpansionGame s base a b =
      expansionSetup (a := a) (b := b) (n := n) fun T₁ T₂ rows seed =>
        let H := streams base T₁ T₂
        C.expansionScore H H s seed (List.ofFn (slotRow hb rows)) := by
  simp only [freshExpansionGame, expansionSetup, PMF.monad_bind_eq_bind, ← sample_streams,
    PMF.bind_bind, PMF.bind_map, Function.comp_def]
  refine congrArg (PMF.bind (PMF.uniformOfFintype (Table a b)) ·) (funext fun T₁ =>
    congrArg (PMF.bind (PMF.uniformOfFintype (Table a b)) ·) (funext fun T₂ => ?_))
  symm
  pmf_swap with seed
  simp only [expansionScore, scoreTranscript, withTrialSetup]
  let H := streams base T₁ T₂
  cases hkey : (streams base T₁ T₂).keyGen s seed with
  | none => simp
  | some keys =>
    dsimp only
    cases hA : (streams base T₁ T₂).expandA s (keys.publicKey.take 32) with
    | none => simp
    | some A =>
      simpa only [PMF.map_bind] using congrArg
        (PMF.map fun (f, log) => SignedMatrixTrial.newDigestWin ⟨H, A, keys.publicKey, f, log⟩)
        (C.uniform_expansionTranscript s H hb keys hn)

private theorem gap_bind_const {ι : Type} [Finite ι] (p : PMF ι) (f g : ι → PMF Bool) {B : ℝ}
    (h : ∀ i, gap (f i) (g i) ≤ B) : gap (p.bind f) (p.bind g) ≤ B := by
  let _ := Fintype.ofFinite ι
  apply (gap_bind_mean p f g (fun _ => B) h).trans_eq
  rw [← Finset.sum_mul, PMF.sum_toReal, one_mul]

/-- Changing Algorithm 34 from a private seeded SHAKE expansion to independent private rows
for each call costs a coherent-query amplitude loss, two shared-input collision terms, and
the birthday probability of the 512-bit mask seeds. The reference game still computes
commitment digests and sparse challenges using the shared FIPS hash stream. -/
theorem privateMaskSeedGame_le_freshExpansionGame (C : QuantumSigningForger) (s : Level)
    (base : Xofs) {a b n m : ℕ} (ha : 528 ≤ a) (hb : 32 * (s.params.γ₁.log2 + 1) ≤ b)
    (hn : C.SigningCallsLe n) (hsize : n ≤ 2 ^ 512) (hm : C.XofCallsLe m) :
    (Game.succProbability (C.privateMaskSeedGame s base a b) : ℝ) ≤
      (√(Game.succProbability (C.freshExpansionGame s base a b) : ℝ) +
        2 * m * √(n / 2 ^ 512)) ^ 2 + 2 * n / 2 ^ 512 +
        ((n * (n - 1) : ℕ) : ℝ) / 2 ^ 513 := by
  let _ := maskSeedEmbedding hsize
  let tapes := PMF.uniformOfFintype (Fin n ↪ FixedBytes 64)
  let ideal := C.freshExpansionGame s base a b
  let shared := C.maskExpansionGame s base (b := b) ha hsize
  let middle := expansionSetup (n := n) fun (T₁ T₂ : Table a b) rows seed =>
    let H := streams base T₁ T₂
    tapes.bind fun t => C.expansionScore (maskStreams base ha t T₁ T₂ rows) H s seed
      (List.ofFn (slotRow hb rows))
  have collide : dist (C.privateMaskSeedGame s base a b) shared ≤ _ :=
    C.dist_privateMaskSeedGame_maskExpansionGame s base ha hn hsize
  have setup : (Game.advantage shared middle : ℝ) ≤ 2 * n / 2 ^ 512 := by
    have reord : shared = expansionSetup (a := a) (b := b) (n := n) fun T₁ T₂ rows seed =>
        tapes.bind fun t =>
          let G := maskStreams base ha t T₁ T₂ rows
          scoreTranscript G s SignedMatrixTrial.newDigestWin (G.keyGen s seed)
            (fun keys => C.seedTapeTranscript G s keys (List.ofFn t)) := by
      simp only [shared, maskExpansionGame, maskTapeScore, expansionSetup, PMF.monad_bind_eq_bind]
      pmf_swap
    rw [reord]
    simp only [middle, expansionSetup, PMF.monad_bind_eq_bind]
    exact Game.advantage_bind_le _ _ _ fun T₁ => Game.advantage_bind_le _ _ _ fun T₂ =>
      Game.advantage_bind_le _ _ _ fun rows => Game.advantage_bind_le _ _ _ fun seed =>
        setup_advantage_le C s base ha hb hn T₁ T₂ rows seed
  let loss : ℝ := 2 * m * √(n / 2 ^ 512)
  have sq : gap middle ideal ≤ loss ^ 2 := by
    rw [show ideal = _ from C.freshExpansionGame_eq_setup (a := a) s base hb hn]
    simp only [middle, expansionSetup, PMF.monad_bind_eq_bind]
    refine gap_bind_const _ _ _ fun T₁ => gap_bind_const _ _ _ fun T₂ =>
      gap_bind_const _ _ _ fun rows => gap_bind_const _ _ _ fun seed => ?_
    apply (expansionScore_gap_le C s base ha hb hm T₁ T₂ rows seed).trans_eq
    let rate : ℝ := n / 2 ^ 512
    change 4 * m * m * rate = (2 * m * √rate) ^ 2
    simp only [mul_pow, Real.sq_sqrt (show 0 ≤ rate by dsimp [rate]; positivity)]
    rw [show (2 : ℝ) ^ 2 = 4 by norm_num, pow_two, ← mul_assoc]
  have hl : 0 ≤ loss := by dsimp [loss]; positivity
  have root : √(Game.succProbability middle : ℝ) ≤ √(Game.succProbability ideal : ℝ) + loss := by
    apply sub_le_iff_le_add'.mp
    rw [Game.coe_succProbability, Game.coe_succProbability]
    exact (le_abs_self _).trans ((sq_le_sq₀ (abs_nonneg _) hl).mp
      (by simpa only [sq_abs, gap] using sq))
  have prob := pow_le_pow_left₀ (Real.sqrt_nonneg _) root 2
  rw [Real.sq_sqrt (NNReal.coe_nonneg _)] at prob
  rw [← coe_nndist, ← Game.advantage_eq_nndist] at collide
  exact (Game.coe_succProbability_le_add_of_advantage_le collide).trans
    (add_le_add ((Game.coe_succProbability_le_add_of_advantage_le setup).trans
      (add_le_add prob le_rfl)) le_rfl)

/-- Strong-forgery bound for the original finite random-XOF ML-DSA experiment, with both
Algorithm 7's private mask seed and Algorithm 34's secondary expansions removed from the
fresh-digest term. Signing in that term still reads its commitment digest from the shared
oracle and retains all 814 retry attempts. -/
theorem randomPrefixGame_forgery_le_freshExpansionGame (C : QuantumSigningForger) (s : Level)
    (base : Xofs) {a b n m : ℕ} (ha : 1024 ≤ a) (hb : 894 ≤ b)
    (hn : C.SigningCallsLe n) (hsize : n ≤ 2 ^ 256) (hm : C.XofCallsLe m) :
    let R := base.uniformPrefixes a b
    let trial := R.bind (C.matrixTrial s)
    let expansion : ℝ := (√(Game.succProbability (C.freshExpansionGame s base a b) : ℝ) +
      2 * m * √(n / 2 ^ 512)) ^ 2 + 2 * n / 2 ^ 512 + ((n * (n - 1) : ℕ) : ℝ) / 2 ^ 513
    let seedLoss : ℝ := 2 * m * √(2 * n / 2 ^ 256) * (√(2 / 2 ^ 256) + m * (2 / 2 ^ 128))
    (Game.succProbability (C.randomPrefixGame s base a b) : ℝ) ≤
      (√(expansion + n / 2 ^ 256) + seedLoss) ^ 2 + ((n * (n - 1) : ℕ) : ℝ) / 2 ^ 257 +
      Game.succProbability (trial.map (·.any SignedMatrixTrial.hashCollision)) +
      Game.succProbability ((PMF.uniformOfFintype (PublicMatrix s)).bind fun A =>
        (R.bind fun H => C.matrixSolver s H A).map fun v => decide (ModuleSIS.IsSolution
          (ModuleSIS.hermiteMatrix A)
          (max (2 * (s.params.γ₁ - s.params.β)) (4 * s.params.γ₂ + 2)) v)) := by
  intro R trial expansion seedLoss
  have width : 32 * (s.params.γ₁.log2 + 1) ≤ 894 := by cases s <;> decide
  have grow (i j : ℕ) (h : i ≤ j) : (2 : ℕ) ^ i ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) h
  have seedSize : n ≤ 2 ^ 512 := hsize.trans (grow 256 512 (by decide))
  have fresh : (Game.succProbability (C.privateMaskSeedGame s base a b) : ℝ) ≤ expansion :=
    C.privateMaskSeedGame_le_freshExpansionGame s base ((by decide : 528 ≤ 1024).trans ha)
      (width.trans hb) hn seedSize hm
  apply (C.randomPrefixGame_forgery_le_of_query_budget s base ha hb hn hsize hm).trans
  gcongr

end QuantumSigningForger

end Cslib.Crypto.MLDSA.FIPS204
