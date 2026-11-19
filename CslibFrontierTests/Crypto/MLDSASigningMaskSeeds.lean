/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import all CslibFrontier.Crypto.Computational.MLDSA.PrivateMaskExpansion
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204Signing
import all CslibFrontier.Crypto.Computational.MLDSA.PrivateMaskSeedGame
import all CslibFrontier.Crypto.Computational.MLDSA.SigningHedges
import all CslibFrontier.Crypto.Computational.MLDSA.KeySeedSearch
import all CslibFrontier.Crypto.Computational.MLDSA.MaskSeedQuery
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
meta import CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Uniform

/-! # Mask-seed coupling at the Algorithm 7 and quantum XOR interfaces -/

set_option linter.privateModule false

open Cslib Cslib.Crypto Cslib.Crypto.MLDSA.FIPS204 Cslib.Probability
open scoped Cslib.Probability.PMF

-- The address formed from the decoded private signing seed K and the actual formatted message
-- representative gives the assigned seed both to the signer and to the coherent device.
-- A query extending one byte beyond the seed reads the original suffix.
example (base : Xofs) (s : Level) (seed : FixedBytes 32) {a b n : ℕ}
    (t : Fin n ↪ FixedBytes 32) (ha : 1024 ≤ a) (hb : 64 ≤ b) (rows : SigningMaskSeeds n)
    {pair : SigningMaskSeedOracles}
    (hp : pair ∈ (base.sampleSigningMaskSeeds s seed t ha hb rows).support)
    {keys : KeyPair} {sk : PrivateKey s} (hg : pair.shared.keyGen s seed = some keys)
    (hd : decodePrivate s keys.secretKey = some sk) (i : Fin n) (q : SigningQuery) :
    let μ := pair.shared.representativeFromTr sk.tr (formatMessage q.message q.context)
    let x := maskSeedInput sk.key (t i) μ
    let row := (rows (i, BitString.ofList 512 μ)).toList
    pair.shared.h256.read x 64 = row ∧
      (∃ hx : x.length ≤ a,
        List.ofFn (pair.shared.queryTable a 64 (Xofs.queryAddress a true x hx)) =
          Keccak.bytesToBitsLE row) ∧
      pair.shared.h256.byteAt x 64 = pair.background.h256.byteAt x 64 := by
  obtain ⟨rho, short, _, _, decoded, _⟩ := privateKey_of_keyGen hg
  rw [hd] at decoded
  cases Option.some.inj decoded
  intro μ x row
  have len : μ.length = 512 :=
    length_messageRepresentative pair.shared keys.publicKey (formatMessage q.message q.context)
  have read := read_of_mem_sampleSigningMaskSeeds hp i (BitString.ofList 512 μ)
  rw [BitString.ofFn_ofList len] at read
  have keyLen : ((pair.shared.expandKeySeed s seed).drop 96).length = 32 := by
    have hlen : (pair.shared.expandKeySeed s seed).length = 128 := pair.shared.h256.length_read ..
    simp [hlen]
  have hx : x.length ≤ a := by
    simpa only [x, length_maskSeedInput, keyLen, len] using ha
  refine ⟨read, ⟨hx, ?_⟩, (agree_off_sampleSigningMaskSeeds hp).2 x 64 (.inl le_rfl)⟩
  rw [Xofs.queryTable_queryAddress]
  exact congrArg Keccak.bytesToBitsLE read

-- The public device can use the shared table in the precise fresh-digest term of the existing
-- reduction. This composes the entire signed interaction, including scoring on setup failure.
example (C : QuantumSigningForger) (s : Level) (base : Xofs) {a b n : ℕ}
    (ha : 1024 ≤ a) (hb : 894 ≤ b) (hn : C.SigningCallsLe n) (hsize : n ≤ 2 ^ 256) :
    dist (((base.uniformPrefixes a b).bind (C.matrixTrial s)).map
      (·.any SignedMatrixTrial.newDigestWin))
      (C.maskSeedGame s base ha ((by decide : 64 ≤ 894).trans hb) hn hsize true
        SignedMatrixTrial.newDigestWin) ≤
      ((n * (n - 1) : ℕ) : ℝ) / 2 ^ 257 := by
  rw [C.shared_maskSeedGame_eq_distinctHedgeGame]
  exact C.dist_matrixTrial_distinctHedges s base ((by decide : 272 ≤ 1024).trans ha) hb hn hsize _

-- An empty context and a 496-bit message produce a legitimate 512-bit formatted input.
-- A public-key hash equal to K followed by a selected hedge makes the two addresses coincide.
set_option linter.hashCommand false in
#guard (formatMessage (List.replicate 496 false) []).length == 512

example (key rnd : FixedBytes 32) :
    let m := formatMessage (List.replicate 496 false) []
    representativeInput (key.toList ++ rnd.toList) m = maskSeedInput key.toList rnd m := rfl

-- Select a final forgery using the whole pair of oracles and generated keys. Its message
-- representative can change only on the event already bounded for all messages at once.
example (base : Xofs) (s : Level) (seed : FixedBytes 32) {a b : ℕ} (ha : 1024 ≤ a) (hb : 64 ≤ b)
    (rows : SigningMaskSeeds (2 ^ 64)) (choose : SigningMaskSeedOracles → KeyPair → Forgery)
    [Nonempty (Fin (2 ^ 64) ↪ FixedBytes 32)] :
    (((PMF.uniformOfFintype (Fin (2 ^ 64) ↪ FixedBytes 32)).bind fun t =>
      base.sampleSigningMaskSeeds s seed t ha hb rows).toOuterMeasure
        {p | ∃ keys, p.background.keyGen s seed = some keys ∧
          let m := formattedMessage (choose p keys)
          p.shared.messageRepresentative keys.publicKey m ≠
            p.background.messageRepresentative keys.publicKey m}).toReal ≤ 1 / 2 ^ 192 := by
  have bound := base.prob_representative_ne_sampleSigningMaskSeeds s seed ha hb (by decide) rows
  refine (Cslib.Probability.PMF.toOuterMeasure_toReal_mono _ ?_).trans (bound.trans ?_)
  · rintro p ⟨keys, hg, hne⟩
    exact ⟨keys, hg, formattedMessage (choose p keys), hne⟩
  · norm_num

-- With no signing calls, the two full games agree even when the forger uses the quantum device.
example (C : QuantumSigningForger) (s : Level) (base : Xofs) {a b : ℕ}
    (ha : 1024 ≤ a) (hb : 64 ≤ b) (hn : C.SigningCallsLe 0) :
    C.maskSeedGame s base ha hb hn (by decide) false SignedMatrixTrial.newDigestWin =
      C.privateMaskSeedGame s base a b := by
  apply dist_le_zero.mp
  simpa using C.dist_maskSeedGame_privateMaskSeedGame s base ha hb hn (by decide)

-- The mask-seed replacement in the scored game costs at most 2⁻¹⁹² at 2⁶⁴ signing calls,
-- for every FIPS level, including adaptive signing and interleaved coherent queries.
example (C : QuantumSigningForger) (s : Level) (base : Xofs) {a b : ℕ}
    (ha : 1024 ≤ a) (hb : 64 ≤ b) (hn : C.SigningCallsLe (2 ^ 64)) :
    dist (C.maskSeedGame s base ha hb hn (by decide) false SignedMatrixTrial.newDigestWin)
      (C.privateMaskSeedGame s base a b) ≤ 1 / 2 ^ 192 := by
  exact (C.dist_maskSeedGame_privateMaskSeedGame s base ha hb hn (by decide)).trans (by norm_num)

-- The second probe follows an observed signing result. It stops before the second query,
-- and a failed signature ends this branch without measuring the address.
open Cslib.Quantum QuantumSigningForger in
example (C : QuantumSigningForger) (q : SigningQuery) :
    queryPrefix (C := C) (α := Unit) (do
      let _ ← OracleComp.query (.inr (.inl .query))
      let sig ← (OracleComp.query (Sum.inr (Sum.inr q) : ℕ ⊕
        DeviceRequest (Width C) Empty ⊕ SigningQuery) : Program C (Option (List Byte)))
      match sig with
      | none => pure ()
      | some _ =>
        let _ ← OracleComp.query (.inr (.inl (.gate (false, true, 0, []))))
        let _ ← OracleComp.query (.inr (.inl .query))
        pure ()) 1 = (do
      let _ ← OracleComp.query (.inr (.inl .query))
      let sig ← (OracleComp.query (Sum.inr (Sum.inr q) : ℕ ⊕
        DeviceRequest (Width C) Empty ⊕ SigningQuery) : Program C (Option (List Byte)))
      match sig with
      | none => pure false
      | some _ =>
        let _ ← OracleComp.query (.inr (.inl (.gate (false, true, 0, []))))
        pure true) := by
  change (.liftBind _ _ : Program C Bool) = .liftBind _ _
  congr 1
  funext _
  change (.liftBind _ _ : Program C Bool) = .liftBind _ _
  congr 1
  funext sig
  cases sig <;> rfl

-- For any pre-query density, including a superposition correlated with the response or work
-- wires, the observed address is the marginal of its computational-basis Born distribution.
open Cslib.Quantum QuantumSigningForger in
example (C : QuantumSigningForger) (st : C.State) :
    C.addressRead (true, st) =
      (st.1.measure (fun z => fun i : Fin (C.addressBits + 2) =>
        z ⟨i.val, i.isLt.trans_le (by dsimp only [Width]; lia)⟩)).map (some ∘ Prod.fst) := by
  unfold addressRead
  simp only [ite_true]
  rw [← PMF.map_comp, DeviceState.measure_map_fst, PMF.map_comp]
  congr 1
  funext z
  simp only [Function.comp_apply, Option.some.injEq]
  rw [queryRegisters_apply (a := C.addressBits + 2) (b := 8 * C.responseBytes)]
  rfl

-- A per-query detection probability, at any of the three FIPS levels.
example (C : QuantumSigningForger) (s : Level) (base : Xofs) {a b : ℕ}
    (ha : 1024 ≤ a) (hb : 64 ≤ b) (hn : C.SigningCallsLe (2 ^ 64)) (j : ℕ) :
    (Game.succProbability (C.maskSeedQueryHit s base (n := 2 ^ 64) ha hb (by decide) j) : ℝ) ≤
      1 / 2 ^ 191 :=
  (C.maskSeedQueryHit_le s base ha hb hn (by decide) j).trans (by norm_num)

-- At a large signing budget the entire measured-query loss scales with the chance of
-- predicting the private signing seed K, including the public-key-hash candidate.
example (C : QuantumSigningForger) (s : Level) (base : Xofs) {a b : ℕ} (ha : 1024 ≤ a)
    (hb : 64 ≤ b) (hn : C.SigningCallsLe (2 ^ 64)) (j : ℕ) :
    (Game.succProbability (C.maskSeedQueryHit s base (n := 2 ^ 64) ha hb (by decide) j) : ℝ) ≤
      (1 / 2 ^ 191) * Game.succProbability (C.signingSeedPredictionGame s base a b (2 ^ 64) j) := by
  have h := C.maskSeedQueryHit_le_signingSeedPrediction s base ha hb hn (by decide) j
  convert h using 2
  norm_num

-- Decode the candidate from the raw SHAKE256 input. SHAKE128 has no candidate.
open QuantumSigningForger in
example (C : QuantumSigningForger) (x : List Bool) (hx : x.length ≤ C.addressBits)
    (strength : Bool) :
    queryKeyPrefix (C := C) (some (Xofs.queryAddress C.addressBits strength x hx)) =
      if strength then some (x.take 256) else none := by
  have len : (List.replicate (C.addressBits - x.length) false ++ true :: x).length =
      C.addressBits + 1 := by
    simp only [List.length_append, List.length_replicate, List.length_cons]
    lia
  cases strength with
  | false => rfl
  | true =>
    simp only [queryKeyPrefix, Xofs.queryAddress, Option.bind_eq_bind, Option.bind_some,
      Fin.cons_zero, guard, ↓reduceIte, Option.pure_def, Fin.cons_succ, BitString.ofFn_ofList len,
      Xofs.unpad_word]

-- If the forger stops early, only the public-key hash can predict the private signing seed K.
open QuantumSigningForger in
example (C : QuantumSigningForger) (H : Xofs) (s : Level) (seed : FixedBytes 32) (keys : KeyPair)
    (hg : H.keyGen s seed = some keys) :
    signingSeedCandidates (C := C) (publicHash H ((H.keyGen s seed).map KeyPair.publicKey)) none =
      [Keccak.bytesToBitsLE ((H.h256.readBytes keys.publicKey 64).take 32)] := by
  simp [signingSeedCandidates, publicHash, hg, queryKeyPrefix]

-- At the first query, even after signing, the original response-change bound gains 255 bits.
example (C : QuantumSigningForger) (s : Level) (base : Xofs) {a b : ℕ}
    (ha : 1024 ≤ a) (hb : 128 ≤ b) (hn : C.SigningCallsLe (2 ^ 64)) :
    (Game.succProbability (C.maskSeedQueryHit s base ha ((by decide : 64 ≤ 128).trans hb)
      (n := 2 ^ 64) (by decide) 0) : ℝ) ≤ 1 / 2 ^ 446 := by
  have hit := C.maskSeedQueryHit_le_signingSeedPrediction s base ha
    ((by decide : 64 ≤ 128).trans hb) hn (by decide) 0
  have pred := C.signingSeedPredictionGame_le s base ((by decide : 272 ≤ 1024).trans ha)
    hb (2 ^ 64) 0
  simp only [Nat.cast_zero, zero_mul, add_zero,
    Real.sq_sqrt (show 0 ≤ 2 / (2 : ℝ) ^ 256 by positivity)] at pred
  apply hit.trans (le_trans (mul_le_mul_of_nonneg_left pred (by positivity)) _)
  rw [show (446 : ℕ) = 223 + 223 by decide, pow_add]
  norm_num

-- With up to 2^64 earlier coherent calls and 2^64 signing calls, the measured query hits a
-- changed mask-seed response with probability at most 2^-316.
example (C : QuantumSigningForger) (s : Level) (base : Xofs) {a b j : ℕ}
    (ha : 1024 ≤ a) (hb : 128 ≤ b) (hn : C.SigningCallsLe (2 ^ 64)) (hj : j ≤ 2 ^ 64) :
    (Game.succProbability (C.maskSeedQueryHit s base ha ((by decide : 64 ≤ 128).trans hb)
      (n := 2 ^ 64) (by decide) j) : ℝ) ≤ 1 / 2 ^ 316 := by
  have hit := C.maskSeedQueryHit_le_signingSeedPrediction s base ha
    ((by decide : 64 ≤ 128).trans hb) hn (by decide) j
  have pred := C.signingSeedPredictionGame_le s base ((by decide : 272 ≤ 1024).trans ha)
    hb (2 ^ 64) j
  have root : √(2 / (2 : ℝ) ^ 256) ≤ 2 / 2 ^ 128 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    norm_num
  have size : (j : ℝ) * (2 / 2 ^ 128) ≤ (2 : ℝ) ^ 64 * (2 / 2 ^ 128) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (by positivity)
  have p := pred.trans (pow_le_pow_left₀ (by positivity) (add_le_add root size) 2)
  apply hit.trans ((mul_le_mul_of_nonneg_left p (by positivity)).trans ?_)
  rw [show (316 : ℕ) = 158 + 158 by decide, pow_add]
  norm_num

-- Both SHAKE variants parse the same raw word. Only SHAKE256 owns the key-generation row.
open QuantumSigningForger in
example (C : QuantumSigningForger) (s : Level) (seed : FixedBytes 32) (tag : Bool)
    (h : 272 ≤ C.addressBits) :
    let x := keySeedInput s seed
    queriesKeySeed (C := C) s seed
      (some (Xofs.queryAddress C.addressBits tag x ((length_keySeedInput ..).le.trans h))) =
      tag := by
  intro x
  have len : (List.replicate (C.addressBits - x.length) false ++ true :: x).length =
      C.addressBits + 1 := by
    simp only [List.length_append, List.length_replicate, List.length_cons]
    have := (length_keySeedInput s seed).le.trans h
    dsimp only [x] at *
    lia
  simp only [queriesKeySeed, Xofs.queryAddress, Fin.cons_zero, Fin.cons_succ,
    BitString.ofFn_ofList len, Xofs.unpad_word, x, beq_self_eq_true, Bool.and_true]

-- A single execution can exercise both budgets and return the signing reply after a coherent call.
example (q : SigningQuery) :
    let C : QuantumSigningForger := ⟨2, 1, 0, fun _ => do
      let r ← OracleComp.query (Sum.inr (Sum.inr q) : ℕ ⊕
        Cslib.Quantum.DeviceRequest 12 Empty ⊕ SigningQuery)
      let _ ← OracleComp.query (Sum.inr (Sum.inl .query) : ℕ ⊕
        Cslib.Quantum.DeviceRequest 12 Empty ⊕ SigningQuery)
      return ⟨q.context, q.message, (r : Option (List Byte)).getD []⟩⟩
    C.SigningCallsLe 1 ∧ C.XofCallsLe 1 := by
  constructor
  · intro pk
    exact .liftBind _ _ 0 fun _ => .liftBind _ _ 0 fun _ => .pure _ 0
  · intro pk
    exact .liftBind _ _ 1 fun _ => .liftBind _ _ 0 fun _ => .pure _ 0

-- For 2^64 signing and coherent queries, this is a loss in the square root of the final
-- success probability, including when the reference game can already forge.
example (C : QuantumSigningForger) (s : Level) (base : Xofs) {a b : ℕ}
    (ha : 1024 ≤ a) (hb : 128 ≤ b) (hn : C.SigningCallsLe (2 ^ 64))
    (hm : C.XofCallsLe (2 ^ 64)) (score : SignedMatrixTrial s → Bool) :
    let view := C.maskSeedGame s base ha ((by decide : 64 ≤ 128).trans hb) hn (by decide)
    √(Game.succProbability (view true score) : ℝ) ≤
      √(Game.succProbability (view false score) : ℝ) + 1 / 2 ^ 93 := by
  intro view
  apply (C.sqrt_maskSeedGame_le s base ha hb hn (by decide) hm score).trans
  apply add_le_add le_rfl
  push_cast
  have root : √(2 / (2 : ℝ) ^ 256) ≤ 2 / 2 ^ 128 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    norm_num
  apply (mul_le_mul_of_nonneg_left (add_le_add root le_rfl) (by positivity)).trans
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow]
  norm_num

-- Replacing every Algorithm 34 expansion at all three levels, with a full quantum/signing budget.
example (C : QuantumSigningForger) (s : Level) (base : Xofs) {a b : ℕ}
    (ha : 528 ≤ a) (hb : 640 ≤ b) (hn : C.SigningCallsLe (2 ^ 64))
    (hm : C.XofCallsLe (2 ^ 64)) :
    (Game.succProbability (C.privateMaskSeedGame s base a b) : ℝ) ≤
      (√(Game.succProbability (C.freshExpansionGame s base a b) : ℝ) + 1 / 2 ^ 159) ^ 2 +
      1 / 2 ^ 447 + 1 / 2 ^ 385 := by
  have width : 32 * (s.params.γ₁.log2 + 1) ≤ 640 := by cases s <;> decide
  have grow (i j : ℕ) (h : i ≤ j) : (2 : ℕ) ^ i ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) h
  apply (C.privateMaskSeedGame_le_freshExpansionGame s base ha (width.trans hb) hn
    (grow 64 512 (by decide)) hm).trans
  have pow512 : (2 : ℝ) ^ 512 = 2 ^ 256 * 2 ^ 256 := pow_add 2 256 256
  have pow513 : (2 : ℝ) ^ 513 = 2 ^ 256 * 2 ^ 256 * 2 := by rw [← pow512, ← pow_succ]
  have pow447 : (2 : ℝ) ^ 447 = 2 ^ 224 * 2 ^ 223 := pow_add 2 224 223
  have pow385 : (2 : ℝ) ^ 385 = 2 ^ 193 * 2 ^ 192 := pow_add 2 193 192
  rw [pow512, pow513, pow447, pow385]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul]
  have root : √((2 : ℝ) ^ 64 / (2 ^ 256 * 2 ^ 256)) = 1 / 2 ^ 224 := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
    norm_num
  rw [root]
  norm_num

-- The signer still draws all 576 private bytes per nonce when no public output is randomized.
open QuantumSigningForger in
example (C : QuantumSigningForger) (base : Xofs) :
    C.freshExpansionGame .mlDSA44 base 528 0 = (do
      let H ← base.uniformPrefixes 528 0
      let seed ← PMF.uniformOfFintype (FixedBytes 32)
      scoreTranscript H .mlDSA44 SignedMatrixTrial.newDigestWin (H.keyGen .mlDSA44 seed)
        (fun keys => C.sampledSigningTranscript H keys.publicKey
          (fun (row : FixedBytes 2 → FixedBytes 576) q =>
            H.signWithExpansionRow .mlDSA44 keys.secretKey q row))) := rfl
