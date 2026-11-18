/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import all CslibFrontier.Crypto.Computational.MLDSA.QuantumCommitment
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigningPrefix
import all CslibFrontier.Computability.QueryComplexity.Quantum.MeasuredPrefix
meta import CslibFrontier.Crypto.Computational.MLDSA.FIPS204Signing

/-!
# ML-DSA byte keys, signing and verification

Exercise Algorithm 29's signed shuffle and rejection stream, Algorithm 27's digest boundary,
and Algorithm 21's rejection of noncanonical hint encodings.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

open Cslib.Crypto Cslib.Crypto.MLDSA.FIPS204

-- NIST ACVP-Server, ML-DSA-keyGen-FIPS204/internalProjection.json, tgId 1, tcId 1
-- (commit 975de31eb83d87039ec88934fdc47d8c312b892d). Compare a SHAKE256 fingerprint of
-- the complete expected public-key bytes to keep the 1312-byte fixture out of the source.
private def keyGenSeed : List Byte := [
    0x71, 0x94, 0xb1, 0x3c, 0x95, 0x23, 0x10, 0x10, 0xaf, 0xd2, 0xc9, 0x09,
    0x99, 0x2b, 0xd2, 0x00, 0x3b, 0xa6, 0xf4, 0x37, 0xc3, 0x88, 0x6b, 0xdb,
    0xe3, 0xf6, 0xb8, 0x67, 0xa1, 0x4b, 0xa1, 0x61]

private def publicKeyFingerprint : List Byte := [
    0x0d, 0xb3, 0x22, 0x35, 0x94, 0xa1, 0xfc, 0xe8, 0xdb, 0x48, 0xc8, 0xf1,
    0x79, 0x36, 0x11, 0xa1, 0x7f, 0xcc, 0x00, 0x06, 0xff, 0xea, 0x26, 0xcf,
    0x70, 0x94, 0xd8, 0x32, 0x50, 0x37, 0x28, 0x8f]

private def secretKeyFingerprint : List Byte := [
    0xb2, 0xfc, 0xe5, 0xa6, 0xc1, 0xc6, 0xa3, 0x65, 0x20, 0x6e, 0xdc, 0x65,
    0x52, 0x20, 0x41, 0x45, 0x9d, 0xbd, 0xcd, 0x23, 0xde, 0x69, 0x8d, 0x5b,
    0x8b, 0xa9, 0x61, 0x04, 0x3c, 0x1f, 0x13, 0x62]

-- Use a message ending mid-byte and a nonempty context; changing the context must invalidate it.
private def keyAndSigningChecks : Option Bool := do
  let keys ← keyGen .mlDSA44 fun i => keyGenSeed[i.val]!
  let msg := [true, false, true]
  let ctx := [11, 22]
  let σ ← sign .mlDSA44 keys.secretKey msg ctx (fun _ => 0)
  return Keccak.shake256 keys.publicKey 32 == publicKeyFingerprint &&
    Keccak.shake256 keys.secretKey 32 == secretKeyFingerprint &&
    verify .mlDSA44 keys.publicKey msg ctx σ == some true &&
    verify .mlDSA44 keys.publicKey msg [11] σ == some false

#guard keyAndSigningChecks == some true
#guard (sign .mlDSA44 [] [] [] (fun _ => 0)).isNone
#guard (sign .mlDSA44 [] [] (List.replicate 256 0) (fun _ => 0)).isNone

-- Independent SHAKE256(0^256) expansion followed by the FIPS 204 Algorithm 29 shuffle.
private def zeroDigestSupport (value : ZMod 8380417) : Option (List ℕ) := do
  let c ← sampleInBall .mlDSA44 (List.replicate 32 0)
  return ((List.finRange 256).filter fun i => c i == value).map Fin.val

#guard zeroDigestSupport 1 ==
  some [5, 17, 23, 29, 30, 34, 51, 54, 59, 67, 88, 113, 127, 141, 147, 231, 233, 236, 248]
#guard zeroDigestSupport (-1) == some
  [18, 25, 38, 48, 70, 79, 86, 87, 98, 100, 114, 116, 129, 173, 195, 213, 219, 242, 244, 253]

private def signature (digest : List Byte) (hint : List Byte) : List Byte :=
  digest ++ List.replicate 2304 0 ++ hint

private def digest44 : List Byte := (List.finRange 32).map (fun i => Fin.ofNat 256 i.val)

#guard (sigDecode .mlDSA44 (signature digest44 (List.replicate 84 0))).map (·.digest) ==
  some digest44
#guard (sigDecode .mlDSA44 (signature digest44 (List.replicate 83 0))).isNone
-- Index 7 is used twice in the first row. A nonzero unused byte is also invalid.
#guard (sigDecode .mlDSA44 (signature digest44
  ([7, 7] ++ List.replicate 78 0 ++ [2, 2, 2, 2]))).isNone
#guard (sigDecode .mlDSA44 (signature digest44 (1 :: List.replicate 83 0))).isNone

#guard verify .mlDSA44 [] [] [] [] == some false
#guard verify .mlDSA44 [] [] (List.replicate 256 0) [] == none

-- The ten-bit coefficients 0, 1, 1023 and 2 cross byte boundaries. The first two
-- distinguish the rounding tie at 4096 from its successor.
#guard ((encodePublic .mlDSA44 (List.replicate 32 0) fun _ i =>
    match i.val with
    | 0 => 4096 | 1 => 4097 | 2 => -1 | 3 => 16384 | _ => 0).drop 32).take 5 ==
  [0, 4, 240, 191, 0]

-- Every mask reaches the same encoded address at the zero matrix. A useful
-- reprogramming estimate therefore has to account for the law of the public matrix.
example (s : Level) (extra : Finset (List Bool)) (μ : Cslib.BitString 512) :
    (signingAddressLaw s extra 0 μ).support.Subsingleton := by
  have hz (y : Fin s.params.ℓ → Poly) : moduleSISMap (0 : PublicMatrix s) y = 0 := by
    funext i
    simp [moduleSISMap]
  unfold signingAddressLaw
  simp_rw [hz]
  change (PMF.map (Function.const _ _) _).support.Subsingleton
  rw [PMF.map_const, PMF.support_pure]
  exact Set.subsingleton_singleton

-- One update at the quantum hash-query budgets in Fallahpour–Fehr–Huang, Table 3.
-- The three exponents bound its additive loss before any later signing calls.
example (s : Level) :
    let queries : ℕ := match s with | .mlDSA44 => 128 | .mlDSA65 => 192 | .mlDSA87 => 256
    let bits : ℕ := match s with | .mlDSA44 => 106 | .mlDSA65 => 447 | .mlDSA87 => 639
    2 * (2 : ℝ) ^ queries * ((11 / 10) / Real.sqrt (2 ^ s.commitmentBoxBits)) ≤ 1 / 2 ^ bits := by
  intro queries bits
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  apply (Real.le_sqrt (by positivity) (by positivity)).2
  have cert : (22 * 2 ^ queries * 2 ^ bits) ^ 2 ≤ 100 * 2 ^ s.commitmentBoxBits := by
    cases s <;> decide +kernel
  have bound : ((22 : ℝ) * 2 ^ queries * 2 ^ bits) ^ 2 ≤ 100 * 2 ^ s.commitmentBoxBits := by
    exact_mod_cast cert
  nlinarith only [bound]

-- If the ExpandS and ExpandMask seeds and counters coincide, their requests share the
-- first 481 SHAKE256 bytes at every FIPS level, including nonstandard XOF instances.
example (H : Xofs) (s : Level) (seed : FixedBytes 64) (nonce : ℕ) :
    let addr := seed.toList ++ [Fin.ofNat 256 nonce, Fin.ofNat 256 (nonce / 256)]
    (H.h256.readBytes addr (32 * (s.params.γ₁.log2 + 1))).take 481 =
      H.h256.readBytes addr 481 := by
  apply H.h256.take_read
  cases s <;> decide

-- An XOF returning 0xff on every stream makes the matrix and the Algorithm 29 sampler
-- exhaust their bounded reads. Both failures must propagate through the FIPS code.
private def allOnesXof : ExtendableOutput where
  read _ n := List.replicate n 255
  length_read _ _ := List.length_replicate
  take_read _ _ _ h := by simp [Nat.min_eq_left h]

#guard ((Xofs.mk allOnesXof allOnesXof).keyGen .mlDSA44 (fun _ => 0)).isNone
#guard ((Xofs.mk allOnesXof allOnesXof).sampleInBall .mlDSA87 []).isNone


-- Reading the actual SHAKE bytes through the common register recovers every byte of Algorithm 2.
example (s : Level) (extra : Finset (List Bool)) (key : List Byte) (q : SigningQuery)
    (rnd : FixedBytes 32) :
    (Cslib.OracleComp.evalPure (Xofs.shake.digestTable s extra)
      (signingRequestQueries s extra Xofs.shake key q rnd)).map FixedBytes.toList =
      sign s key q.message q.context rnd := by
  rw [evalPure_signingRequestQueries, sharedXofs_digestTable]

-- The second measured request consumes the complete returned bytes of the first. Only
-- the classical signing read budgets and the single intervening coherent XOR call are charged.
example (s : Level) (extra : Finset (List Bool)) (H : Xofs) (key : List Byte)
    (q : SigningQuery) (follow : SigningReply s → SigningQuery) (rnd : FixedBytes 32) :
    let emptyCircuit : SigningInteraction s extra Unit Unit := .start
    let first := measuredSigningCall s extra emptyCircuit H (fun _ => key) (fun _ => q)
      (fun _ => rnd)
    let oracle := first.coherent (fun _ => true) (fun _ => LinearIsometry.id)
    let second := measuredSigningCall s extra oracle H (fun _ => key) (fun b => follow b.2)
      (fun _ => rnd)
    second.updateCost = 2 * Real.sqrt (2 * (((s.params.ℓ + 2) * 814 + 2 : ℕ) : ℝ)) + 2 := by
  simp [measuredSigningCall, Cslib.Quantum.MeasuredPrefix.updateCost]
  ring
