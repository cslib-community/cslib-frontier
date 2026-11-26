/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Languages.Probabilistic.QueryCount.Congr
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
import all CslibFrontier.Crypto.Computational.MLDSA.RandomXof
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204Signing
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204

/-!
# Finite random-oracle coverage of the Appendix C capped ML-DSA strong-forgery game

The implementation of [FIPS 204][NISTFIPS204], Algorithms 2, 3 and 6–8, selects the
minimum permitted Appendix C caps on signing and rejection sampling. It allows 814 signing
attempts and up to 894 bytes for RejNTTPoly, 481 for RejBoundedPoly and 221 for SampleInBall.
For this choice, a fixed message budget suffices to cover every raw read, including hashing the
public key and the framed external bit-string message.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability

/-- Bits needed to address every honest raw SHAKE input when external messages have at most
`m` bits. The two terms cover the encoded public key and the representative input with the
largest legal context (64 hash bytes, two framing bytes and 255 context bytes). -/
@[expose] def honestAddressBits (s : Level) (m : ℕ) : ℕ :=
  max (8 * (32 + 320 * s.params.k)) (8 * (64 + 2 + 255) + m)

private structure Agreement (H G : Xofs) (a b : ℕ) : Prop where
  shake128 : ∀ x, x.length ≤ a → ∀ n, n ≤ b → H.h128.read x n = G.h128.read x n
  shake256 : ∀ x, x.length ≤ a → ∀ n, n ≤ b → H.h256.read x n = G.h256.read x n

namespace Agreement

variable {H G : Xofs} {a b m : ℕ} {s : Level}

private theorem bytes256 (h : Agreement H G a b) {xs : List Byte} (hx : 8 * xs.length ≤ a)
    {n : ℕ} (hn : n ≤ b) : H.h256.readBytes xs n = G.h256.readBytes xs n :=
  h.shake256 _ (by simpa only [Keccak.length_bytesToBitsLE] using hx) n hn

private theorem fixedWidth (s : Level) : 8704 ≤ 8 * (32 + 320 * s.params.k) := by
  cases s <;> decide

private theorem fixedInputs (ha : honestAddressBits s m ≤ a) : 8704 ≤ a :=
  (fixedWidth s).trans ((le_max_left ..).trans ha)

private theorem matrix (h : Agreement H G a b) (ha : honestAddressBits s m ≤ a) (hb : 894 ≤ b)
    {rho : List Byte} (hr : rho.length ≤ 32) : H.expandA s rho = G.expandA s rho := by
  have hfa := fixedInputs ha
  have raw (i j : Byte) :
      H.h128.readBytes (rho ++ [i, j]) 894 = G.h128.readBytes (rho ++ [i, j]) 894 :=
    h.shake128 _ (by
      simp only [Keccak.length_bytesToBitsLE, List.length_append, List.length_cons, List.length_nil]
      lia) _ hb
  simp only [Xofs.expandA, raw]; rfl

private theorem keyGen (h : Agreement H G a b) (ha : honestAddressBits s m ≤ a) (hb : 894 ≤ b)
    (seed : FixedBytes 32) : H.keyGen s seed = G.keyGen s seed := by
  have af := fixedInputs ha
  have exp : H.expandKeySeed s seed = G.expandKeySeed s seed := h.bytes256
    (by
      simp only [List.length_append, FixedBytes.length_toList, List.length_cons, List.length_nil]
      lia)
    (by lia)
  set e := G.expandKeySeed s seed with he
  have secret (i : ℕ) :
      H.secretPoly s ((e.drop 32).take 64) i = G.secretPoly s ((e.drop 32).take 64) i :=
    congrArg _ (h.bytes256 (n := 481) (by
      simp only [nonceInput, List.length_append, List.length_take, List.length_cons,
        List.length_nil]
      lia) (by lia))
  have pk (t : Fin s.params.k → Poly) :
      H.h256.readBytes (encodePublic s (e.take 32) t) 64 =
        G.h256.readBytes (encodePublic s (e.take 32) t) 64 := by
    have := (le_max_left (8 * (32 + 320 * s.params.k)) _).trans ha
    refine h.bytes256 ?_ (by lia)
    simp only [length_encodePublic, List.length_take]
    lia
  simp only [Xofs.keyGen, Xofs.expandS, exp, ← he,
    h.matrix ha hb (rho := e.take 32) (by simp), secret, pk]

private theorem representative (h : Agreement H G a b) (ha : honestAddressBits s m ≤ a)
    (hb : 894 ≤ b) {tr ctx : List Byte} {msg : List Bool} (ht : tr.length ≤ 64)
    (hc : ctx.length ≤ 255) (hm : msg.length ≤ m) :
    H.representativeFromTr tr (formatMessage msg ctx) =
      G.representativeFromTr tr (formatMessage msg ctx) := by
  unfold Xofs.representativeFromTr
  rw [h.shake256 _ _ 64 (by lia)]
  have := (le_max_right _ (8 * (64 + 2 + 255) + m)).trans ha
  simp only [representativeInput, formatMessage, List.length_append, Keccak.length_bytesToBitsLE,
    List.length_cons]
  lia

private theorem commitment (h : Agreement H G a b) (ha : honestAddressBits s m ≤ a)
    (hb : 894 ≤ b) {μ : List Bool} (hm : μ.length = 512) (w : Fin s.params.k → Fin 256 → ℤ) :
    H.commitmentDigest s w μ = G.commitmentDigest s w μ :=
  h.shake256 _ (by
    rw [commitmentInput, List.length_append, hm, Keccak.length_bytesToBitsLE, length_packCoeffs]
    exact le_trans (by cases s <;> decide) (fixedInputs ha)) _
    (le_trans (by cases s <;> decide) hb)

private theorem challenge (h : Agreement H G a b) (ha : honestAddressBits s m ≤ a)
    (hb : 894 ≤ b) {d : List Byte} (hd : d.length ≤ digestBytes s) :
    H.sampleInBall s d = G.sampleInBall s d := by
  have := fixedInputs ha
  have : digestBytes s ≤ 64 := by cases s <;> decide
  exact congrArg _ (h.bytes256 (xs := d) (by lia)
    (n := 221) (by lia))

private theorem mask (h : Agreement H G a b) (ha : honestAddressBits s m ≤ a)
    (hb : 894 ≤ b) {seed : List Byte} (hr : seed.length = 64) (κ : ℕ) :
    H.expandMask s seed κ = G.expandMask s seed κ := by
  have := fixedInputs ha
  have raw (i : ℕ) := h.bytes256 (xs := nonceInput seed i)
    (by
      simp only [nonceInput, List.length_append, hr, List.length_cons, List.length_nil]
      lia)
    ((show 32 * (s.params.γ₁.log2 + 1) ≤ 894 by cases s <;> decide).trans hb)
  simp only [Xofs.expandMask, raw]

private theorem attempt (h : Agreement H G a b) (ha : honestAddressBits s m ≤ a)
    (hb : 894 ≤ b) (sk : PrivateKey s) (A : PublicMatrix s) {μ : List Bool} (hm : μ.length = 512)
    {seed : List Byte} (hr : seed.length = 64) :
    H.attempt s sk A μ seed = G.attempt s sk A μ seed := by
  funext κ
  simp only [Xofs.attempt, Xofs.attemptWithMask, h.mask ha hb hr, h.commitment ha hb hm,
    h.challenge ha hb (le_of_eq (length_commitmentDigest ..))]

private theorem signAttempts (h : Agreement H G a b) (ha : honestAddressBits s m ≤ a)
    (hb : 894 ≤ b) (sk : PrivateKey s) (A : PublicMatrix s) {msg : List Bool}
    (hm : msg.length ≤ m) {ctx : List Byte} (hc : ctx.length ≤ 255) (rnd : FixedBytes 32)
    (ht : sk.tr.length ≤ 64) (hk : sk.key.length ≤ 32) :
    (let μ := H.representativeFromTr sk.tr (formatMessage msg ctx)
     H.attempt s sk A μ (H.h256.read (Keccak.bytesToBitsLE (sk.key ++ rnd.toList) ++ μ) 64)) =
    (let μ := G.representativeFromTr sk.tr (formatMessage msg ctx)
     G.attempt s sk A μ (G.h256.read (Keccak.bytesToBitsLE (sk.key ++ rnd.toList) ++ μ) 64)) := by
  dsimp only
  rw [h.representative ha hb ht hc hm]
  let μ := G.representativeFromTr sk.tr (formatMessage msg ctx)
  have len : μ.length = 512 := by
    simp only [μ, Xofs.representativeFromTr, Keccak.length_bytesToBitsLE, G.h256.length_read]
  have := fixedInputs ha
  rw [h.shake256 (Keccak.bytesToBitsLE (sk.key ++ rnd.toList) ++ μ)
    (by
      rw [List.length_append, Keccak.length_bytesToBitsLE, List.length_append,
        FixedBytes.length_toList, len]
      lia) 64 (by lia)]
  exact h.attempt ha hb sk A len (G.h256.length_read ..)

private theorem signInternal (h : Agreement H G a b) (ha : honestAddressBits s m ≤ a)
    (hb : 894 ≤ b) (key : List Byte) {msg : List Bool} (hm : msg.length ≤ m)
    {ctx : List Byte} (hc : ctx.length ≤ 255) (rnd : FixedBytes 32) :
    H.signInternal s key (formatMessage msg ctx) rnd =
      G.signInternal s key (formatMessage msg ctx) rnd := by
  simp only [Xofs.signInternal, Xofs.runSigning, Xofs.startSigning, Xofs.startSigningWithSeed,
    Xofs.startDecodedSigning, bind_assoc, pure_bind]
  refine Option.bind_congr fun sk hsk => ?_
  obtain ⟨hr, hk, ht⟩ := lengths_of_decodePrivate hsk
  rw [h.matrix ha hb hr]
  exact Option.bind_congr fun A _ => congrArg (fun f => firstAccepted s.params.ℓ f 814 0)
    (h.signAttempts ha hb sk A hm hc rnd ht hk)

private theorem sign (h : Agreement H G a b) (ha : honestAddressBits s m ≤ a)
    (hb : 894 ≤ b) (key : List Byte) {msg : List Bool} (hm : msg.length ≤ m)
    (ctx : List Byte) (rnd : FixedBytes 32) :
    H.sign s key msg ctx rnd = G.sign s key msg ctx rnd := by
  by_cases hc : ctx.length ≤ 255
  · simpa only [Xofs.sign, guard, hc, ↓reduceIte, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some] using h.signInternal ha hb key hm hc rnd
  · simp [Xofs.sign, hc, guard]

private theorem verify (h : Agreement H G a b) (ha : honestAddressBits s m ≤ a)
    (hb : 894 ≤ b) (key : List Byte) {msg : List Bool} (hm : msg.length ≤ m)
    (ctx sig : List Byte) : H.verify s key msg ctx sig = G.verify s key msg ctx sig := by
  apply Xofs.verify_congr_of_reads
  · exact h.matrix ha hb (by simp)
  · exact fun _ hd => h.challenge ha hb hd.le
  · intro hc hk
    have hash := h.bytes256 (xs := key)
      (hk ▸ (le_max_left (8 * (32 + 320 * s.params.k)) _).trans ha) (n := 64) (by lia)
    simp only [Xofs.messageRepresentative, hash]
    exact h.representative ha hb (G.h256.length_read ..).le hc hm
  · exact h.commitment ha hb (length_messageRepresentative ..)

end Agreement

namespace QuantumSigningForger

/-- Every requested signing message and every possible final forgery message has at most
`m` bits. Device responses and private coins may determine both kinds of message. -/
@[expose] def MessagesFit (C : QuantumSigningForger) (m : ℕ) : Prop :=
  ∀ pk, ProbOracleComp.QueriesSatisfy (Sum.elim (fun _ => True)
    (fun q : SigningQuery => q.message.length ≤ m)) (C.program pk) ∧
    ∀ f ∈ OracleComp.support (C.program pk), f.message.length ≤ m

private theorem unpad_length {x : List Bool} : ∀ w : List Bool,
    Xofs.unpad w = some x → x.length < w.length
  | [], h => by simp [Xofs.unpad] at h
  | true :: w, h => Option.some.inj h ▸ Nat.lt_succ_self _
  | false :: w, h => (unpad_length w h).trans (Nat.lt_succ_self _)

private theorem queryTable_eq (C : QuantumSigningForger) {H G : Xofs} {a b : ℕ}
    (h : Agreement H G a b) (ha : C.addressBits ≤ a) (hb : C.responseBytes ≤ b) :
    H.queryTable C.addressBits C.responseBytes = G.queryTable C.addressBits C.responseBytes := by
  funext q
  unfold Xofs.queryTable
  cases hx : Xofs.unpad (List.ofFn (fun i : Fin (C.addressBits + 1) => q i.succ)) with
  | none => rfl
  | some x =>
    have hxa : x.length ≤ a := Nat.le_of_lt_succ
      ((List.length_ofFn .. ▸ unpad_length _ hx).trans_le (Nat.succ_le_succ ha))
    cases q 0 <;> simp [h.shake128 x hxa _ hb, h.shake256 x hxa _ hb]

private theorem forgeryGame_eq (C : QuantumSigningForger) {m a b : ℕ} {s : Level}
    (fit : C.MessagesFit m) {H G : Xofs} (h : Agreement H G a b)
    (hc : C.addressBits ≤ a) (hd : C.responseBytes ≤ b)
    (ha : honestAddressBits s m ≤ a) (hb : 894 ≤ b) : C.forgeryGame H s = C.forgeryGame G s := by
  have run (keys : KeyPair) :
      ProbOracleComp.runWith (C.commands H s keys.secretKey) (C.program keys.publicKey) C.initial =
      ProbOracleComp.runWith (C.commands G s keys.secretKey) (C.program keys.publicKey)
        C.initial := by
    simp only [ProbOracleComp.runWith_eq_run_interpret]
    refine congrArg (fun z : StateT (State C) PMF _ => z.run C.initial)
      (OracleComp.QueriesSatisfy.interpret_congr (fit keys.publicKey).1 fun q hq => ?_)
    rcases q with n | dev | req
    · rfl
    · funext st
      simp only [OracleComp.sumHandler, commands, deviceCommand, C.queryTable_eq h hc hd]
    · funext st
      have eq : H.signAndLog s keys.secretKey req st.2 =
          G.signAndLog s keys.secretKey req st.2 :=
        funext fun rnd => by simp only [Xofs.signAndLog, h.sign ha hb keys.secretKey hq]
      change ((H.signingOracle s keys.secretKey req st.2).map _) =
        ((G.signingOracle s keys.secretKey req st.2).map _)
      simp only [Xofs.signingOracle, eq]
  unfold forgeryGame Xofs.keyExperiment
  congr 1
  funext seed
  rw [h.keyGen ha hb seed]
  cases G.keyGen s seed with
  | none => rfl
  | some keys =>
    simp only [transcript, run, PMF.map_comp, Function.comp_def]
    apply PMF.map_congr_on_support
    rintro ⟨f, st⟩ hr
    simp only [Xofs.winsForgery,
      h.verify ha hb _ ((fit keys.publicKey).2 f (ProbOracleComp.mem_support_of_mem _ hr))]

private def cellEmbedding {a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B) :
    RawWord a × Fin b ↪ RawWord A × Fin B :=
  (Function.Embedding.sigmaMap (β := fun i : Fin (a + 1) => BitString i.val)
    (β' := fun i : Fin (A + 1) => BitString i.val) (Fin.castLEEmb (Nat.succ_le_succ ha))
    (fun _ => Function.Embedding.refl _)).prodMap (Fin.castLEEmb hb)

private theorem read_restrict {a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B)
    (t : Table A B) (lo hi : ExtendableOutput) (x : List Bool) (hx : x.length ≤ a)
    (n : ℕ) (hn : n ≤ b) :
    (install lo (fun i => t (cellEmbedding ha hb i))).read x n = (install hi t).read x n := by
  refine List.ext_getElem (by simp only [ExtendableOutput.length_read]) fun i hlen _ => ?_
  have hin : i < n := by simpa only [ExtendableOutput.length_read] using hlen
  rw [ExtendableOutput.getElem_read _ _ hin, ExtendableOutput.getElem_read _ _ hin]
  simp only [byteAt_install, hx, hx.trans ha, hin.trans_le hn, (hin.trans_le hn).trans_le hb,
    and_self, ↓reduceDIte]
  rfl

private theorem restrict_game {a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B)
    (lo hi : Xofs) (play : Xofs → Game)
    (congr : ∀ H G, Agreement H G a b → play H = play G) :
    (lo.uniformPrefixes a b).bind play = (hi.uniformPrefixes A B).bind play := by
  classical
  have unif : (PMF.uniformOfFintype (Table A B)).map (fun t i => t (cellEmbedding ha hb i)) =
      PMF.uniformOfFintype (Table a b) :=
    PMF.uniformOfFintype_pi_map_comp_embedding (cellEmbedding ha hb)
  rw [independent_tables, independent_tables]
  simp only [PMF.bind_bind, PMF.bind_map, ← unif, Function.comp_def]
  refine congrArg _ (funext fun t₂ => congrArg _ (funext fun t₁ => congr _ _
    ⟨read_restrict ha hb t₁ lo.h128 hi.h128, read_restrict ha hb t₂ lo.h256 hi.h256⟩))

/-- The Appendix C capped strong-forgery game has the same law at every larger address or
output width and for every background outside the sampled SHAKE streams. The smaller widths
cover the coherent register, the message budget and the selected minimum permitted caps.
Both widths and the resource budget are fixed before key generation. -/
theorem randomPrefixGame_stable (C : QuantumSigningForger) (s : Level) {m a b A B : ℕ}
    (fit : C.MessagesFit m) (ha : max C.addressBits (honestAddressBits s m) ≤ a)
    (hb : max C.responseBytes 894 ≤ b) (ha' : a ≤ A) (hb' : b ≤ B) (lo hi : Xofs) :
    C.randomPrefixGame s lo a b = C.randomPrefixGame s hi A B := by
  exact restrict_game ha' hb' lo hi (fun H => C.forgeryGame H s)
    fun _ _ h => C.forgeryGame_eq fit h ((le_max_left ..).trans ha) ((le_max_left ..).trans hb)
      ((le_max_right ..).trans ha) ((le_max_right ..).trans hb)

end QuantumSigningForger

end Cslib.Crypto.MLDSA.FIPS204
