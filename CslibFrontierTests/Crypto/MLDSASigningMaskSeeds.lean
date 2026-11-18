/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Crypto.Computational.MLDSA.SigningMaskSeeds

/-! # Mask-seed coupling at the Algorithm 7 and quantum XOR interfaces -/

set_option linter.privateModule false

open Cslib Cslib.Crypto Cslib.Crypto.MLDSA.FIPS204
open scoped Cslib.Probability.PMF

-- The address formed from the actual decoded signing key and the actual formatted message
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
