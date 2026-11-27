/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Crypto.Computational.MLDSA.SignedExtraction
import CslibFrontier.Crypto.Computational.MLDSA.FullPairMLWE
import all CslibFrontier.Crypto.Computational.MLDSA.CompressedKeyOnly
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import all CslibFrontier.Crypto.Computational.MLDSA.PublicPairSigning
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumCommitment
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
import CslibFrontier.Crypto.Computational.MLDSA.RejNTTExhaustion
import CslibFrontier.Crypto.Computational.MLDSA.RepresentativeOverlap
meta import CslibFrontier.Crypto.Computational.MLDSA.FIPS204
meta import CslibFrontier.Crypto.Computational.MLDSA.FullPairMLWE
meta import CslibFrontier.Crypto.Computational.MLDSA.AmbientVerification
meta import CslibFrontier.Crypto.Computational.MLDSA.PublicPairSigning
meta import CslibFrontier.Crypto.Computational.MLDSA.RandomXof
meta import CslibFrontier.Crypto.Computational.MLDSA.RepresentativeOverlap
meta import CslibFrontier.Crypto.Computational.MLDSA.SignedMatrix
meta import CslibFrontier.Crypto.Computational.MLDSA.FIPS204Signing
meta import CslibFrontier.Crypto.Computational.MLDSA.ExpandAProgramming

/-!
# ML-DSA byte keys, signing and verification

Exercise Algorithm 29's signed shuffle and rejection stream, Algorithm 27's digest boundary,
and Algorithm 21's rejection of noncanonical hint encodings.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

open Cslib.Crypto Cslib.Crypto.MLDSA.FIPS204

-- Check low-before-high nibble order, the last accepted coefficient, and exhaustion with
-- 255 accepted coefficients after the final high nibble is rejected.
private def secretPrefixChecks (s : Level) : Bool :=
  let sample : Option (ZMod 8380417 × ZMod 8380417 × ZMod 8380417) :=
    (rejBoundedPoly s (16 :: List.replicate 127 0)).map fun p => (p 0, p 1, p 255)
  let eta : ZMod 8380417 := s.params.η
  sample == some (eta, eta - 1, eta) &&
    (rejBoundedPoly s (List.replicate 127 0 ++ [240])).isNone

#guard secretPrefixChecks .mlDSA44
#guard secretPrefixChecks .mlDSA65
#guard secretPrefixChecks .mlDSA87

-- Start with q itself (rejected), then accept a high-bit-set zero. The byte after the
-- last swapped triple is a sentinel. The shorter prefix contains only 255 accepted triples.
private def matrixStream (n : ℕ) : FixedBytes n := fun i =>
  match i.val with
  | 0 => 1
  | 1 => 224
  | 2 => 127
  | 5 => 128
  | 771 => 99
  | _ => 0

private def matrixStreamCheck : Bool := Id.run do
  let target : Poly := fun _ => 66051
  let (stream, saved) := exchangeRejNTT 894 (matrixStream 894, target)
  let first := (List.ofFn stream).take 9
  let (short, partialSaved) := exchangeRejNTT 768 (matrixStream 768, target)
  return first == [1, 224, 127, 3, 2, 129, 3, 2, 1] && saved 0 == 0 &&
    stream 771 == 99 && (rejNTTPoly (List.ofFn stream)).map (· 255) == some 66051 &&
    (rejNTTPoly (List.ofFn short)).isNone && partialSaved 254 == 0 && partialSaved 255 == 66051

#guard matrixStreamCheck

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

-- Sign a message ending mid-byte at the 255-byte context limit. One more byte must fail.
private def keyAndSigningChecks : Option Bool := do
  let keys ← keyGen .mlDSA44 fun i => keyGenSeed[i.val]!
  let msg := [true, false, true]
  let ctx := List.replicate 255 11
  let σ ← sign .mlDSA44 keys.secretKey msg ctx (fun _ => 0)
  let request : SigningQuery := ⟨[], [true]⟩
  let reply ← sign .mlDSA44 keys.secretKey request.message request.context (fun _ => 0)
  let log := request.logReply (some reply) []
  let A ← Xofs.shake.expandA .mlDSA44 (keys.publicKey.take 32)
  let fresh : Forgery := ⟨ctx, msg, σ⟩
  let repeated : Forgery := ⟨request.context, request.message, reply⟩
  let wins (f : Forgery) := SignedMatrixTrial.newDigestWin ⟨Xofs.shake, A, keys.publicKey, f, log⟩
  -- The one-request controller probes these two full-length SHAKE256 words in superposition.
  -- Their first wire responses select opposite candidates on the actual signing-success branch.
  let afterRead (bit : Bool) := Id.run do
    let address (wire : Fin (6656 + 2)) := decide (wire.val < 2) || (bit && decide (wire.val = 2))
    let measured := Xofs.shake.queryTable 6656 1 address 0
    return if measured = (some reply).isSome then fresh else repeated
  return Keccak.shake256 keys.publicKey 32 == publicKeyFingerprint &&
    Keccak.shake256 keys.secretKey 32 == secretKeyFingerprint &&
    wins fresh && !wins repeated && wins (afterRead false) && !wins (afterRead true) &&
    verify .mlDSA44 keys.publicKey msg [11] σ == some false &&
    (sign .mlDSA44 keys.secretKey msg (11 :: ctx) (fun _ => 0)).isNone

#guard keyAndSigningChecks == some true
#guard (sign .mlDSA44 [] [] [] (fun _ => 0)).isNone

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

-- Under this XOF, seed expansion makes ρ′ all zero, and a single SHAKE256 address
-- returns 0x01 throughout. A swapped nonce byte or an extra role tag changes the two
-- coefficients below. Both are read through the actual protocol algorithms.
private def constantStream (value : List Bool → Byte) : ExtendableOutput where
  read x n := List.replicate n (value x)
  length_read _ _ := List.length_replicate
  take_read _ _ _ h := by simp [Nat.min_eq_left h]

-- In the independent expansion game the private parser exhausts while the public streams
-- accept every nibble. The key-seed read and SHAKE128 remain on the ambient table.
private def independentSecretCheck (s : Level) : Bool :=
  let ambient := constantStream fun _ => 0
  let privateRows := constantStream fun _ => 255
  let H : Xofs := ⟨ambient, ambient⟩
  let G := H.withExpandSStream ⟨privateRows, privateRows⟩
  let r := List.replicate 64 (0 : Byte)
  (H.expandS s r).isSome && (G.expandS s r).isNone &&
    G.expandKeySeed s (fun _ => 0) == List.replicate 128 0 &&
    G.h128.read (List.replicate 528 false) 1 == [0]

#guard independentSecretCheck .mlDSA44
#guard independentSecretCheck .mlDSA65
#guard independentSecretCheck .mlDSA87

-- At every standard level the bound counts the public-key rounding correction.
example (s : Level) : MLDSA.compressedSelfTargetRadius s.params 13 =
    match s with
    | .mlDSA44 => 350209
    | .mlDSA65 => 724481
    | .mlDSA87 => 769537 := by
  cases s <;> decide

-- The full t has ring unit 1 in every row, so its rounded public part vanishes and the
-- extracted low vector is c. Different digest bytes can give exactly the same sparse c.
private def rawOpeningCheck : Bool := Id.run do
  let s := Level.mlDSA44
  let zero := constantStream fun _ => 0
  let H : Xofs := ⟨zero, constantStream fun x => if x.length > 512 then 7 else 0⟩
  let rho : FixedBytes 32 := fun _ => 0
  let pk : MLDSA.PublicKey s.params := ⟨fun _ _ _ => 0, fun _ j => if j.val = 0 then 1 else 0⟩
  let d := List.replicate (digestBytes s) (7 : Byte)
  let other := List.replicate (digestBytes s) (9 : Byte)
  let bytes := encodePublic s rho.toList pk.t
  let sig (digest : List Byte) := encodeSignature s ⟨digest, fun _ _ => 0, fun _ _ => false⟩
  let f : Forgery := ⟨[], [true, false, true], sig d⟩
  let some y := H.extractFull s rho pk.A pk.t f | return false
  let some c := H.sampleInBall s other | return false
  let failed := H.writeCommitment (Keccak.bytesToBitsLE d) (List.replicate 221 255)
  let low := Vector.ofFn fun i => Vector.ofFn (y.u i)
  let response := Vector.ofFn fun i => Vector.ofFn (y.z i)
  let point := {y with u := fun i j => (low.get i).get j,
                       z := fun i j => (response.get i).get j}
  let off := {point with u := fun i j => point.u i j + 1}
  let first := low.get ⟨0, by decide⟩
  return H.verify s bytes f.message f.context f.signature == some true &&
    H.verify s bytes f.message f.context (sig other) == some false &&
    y.msg == H.messageRepresentative bytes (formattedMessage f) &&
    Vector.ofFn c == Vector.ofFn y.c && first == Vector.ofFn y.c && first.toList.any (· != 0) &&
    H.openFullWitness s pk point == some d && (failed.sampleInBall s d).isNone &&
    (failed.openFullWitness s pk point).isNone &&
    MLDSA.highBits s.params.q s.params.γ₂ 1 == MLDSA.highBits s.params.q s.params.γ₂ 0 &&
    (H.openFullWitness s pk off).isNone

#guard rawOpeningCheck

-- A fatal expansion ends a request with a terminal write and no successful log entry.
#guard
  let zero := constantStream fun _ => 0
  let H : Xofs := ⟨zero, zero⟩
  let w : TerminalSigningWrite .mlDSA44 := ⟨⟨[], [true]⟩, fun _ _ => 0, [], fun _ => 0, none⟩
  !(H.terminalRepresentativeMatch (s := .mlDSA44) [] []) &&
    H.terminalRepresentativeMatch [] [w]

-- The final commitment read is necessary. Under this legitimate XOF and encoded key the
-- zero response is accepted, writing a different digest rejects it, and a second write at
-- the same input restores acceptance. A prior signature for a different message allows a
-- strong forgery while excluding it from the fresh-digest branch.
private def checkVerifierWrite (s : Level) : Bool := Id.run do
  let zero := constantStream fun _ => 0
  let H : Xofs := ⟨zero, zero⟩
  let pk := encodePublic s (List.replicate 32 0) (fun _ _ => 0)
  let digest := List.replicate (digestBytes s) (0 : Byte)
  let sig := encodeSignature s ⟨digest, fun _ _ => 0, fun _ _ => false⟩
  let f : Forgery := ⟨[], [true, false, true], sig⟩
  let x := commitmentInput s (fun _ _ => 0) (H.messageRepresentative pk (formattedMessage f))
  let changed := H.writeCommitment x (List.replicate (digestBytes s) 1)
  let restored := changed.writeCommitment x digest
  let prior := {f with message := [false]}
  let trial (G : Xofs) (log : List Forgery) : SignedMatrixTrial s :=
    ⟨G, fun _ _ _ => 0, pk, f, log⟩
  return (trial H []).newDigestWin && !(trial changed []).newDigestWin &&
    (trial restored []).newDigestWin && (trial restored [prior]).wins &&
    !(trial restored [prior]).newDigestWin

#guard checkVerifierWrite .mlDSA44
#guard checkVerifierWrite .mlDSA65
#guard checkVerifierWrite .mlDSA87

-- The same raw word is a legal representative and a commitment input. Short inputs in
-- Algorithm 6 return zeros, so the public key starts with zeros. Its own 64-byte hash and
-- the one-bit message's representative consist of 0x01 bytes; the empty message misses.
private def representativeOverlapCheck (s : Level) (messageBits : ℕ) : Bool := Id.run do
  let zero := constantStream fun _ => 0
  let H : Xofs := ⟨zero, constantStream (fun x => if x.length > 528 then 1 else 0)⟩
  let some keys := H.keyGen s (fun _ => 0) | return false
  let pk := keys.publicKey
  let tr := H.h256.readBytes pk 64
  let empty : Forgery := ⟨[], [], []⟩
  let one : Forgery := ⟨[], [false], []⟩
  let y := representativeInput tr (formattedMessage one)
  let final := representativeInput tr (formatMessage (List.replicate messageBits false) [])
  let signed := commitmentInput s (fun _ _ => 0) (H.messageRepresentative pk (formattedMessage one))
  -- A second stream tests the equal-input outcome on the generated all-zero public key.
  let Z : Xofs := ⟨zero, zero⟩
  let self : Forgery := ⟨[], List.replicate (8 * pk.length - 528) false, []⟩
  return final == signed && H.matchingRepresentativeInput pk [empty] == none &&
    H.matchingRepresentativeInput pk [empty, one] == some y && Keccak.bytesToBitsLE pk != y &&
    H.h256.read y 64 == tr && tr != pk.take 64 &&
    Z.matchingRepresentativeInput pk [self] == some (Keccak.bytesToBitsLE pk) &&
    Z.h256.readBytes pk 64 == pk.take 64

#guard representativeOverlapCheck .mlDSA44 6128
#guard representativeOverlapCheck .mlDSA65 6128
#guard representativeOverlapCheck .mlDSA87 8176

-- Algorithm 32 appends the column before the row. Adjacent addresses, bit-length variants
-- and longer reads exercise the same XOF that the verifier and an outside caller receive.
private def matrixAddressChecks : Bool := Id.run do
  let rho : List Byte := List.replicate 32 11
  let base := Xofs.mk (constantStream fun _ => 77) (constantStream fun _ => 88)
  let H := base.withMatrixPrefixes .mlDSA65 rho fun i j _ => Fin.ofNat 256 (16 * i.val + j.val)
  let input := rho ++ [2, 5]
  let x := Keccak.bytesToBitsLE input
  return (H.h128.readBytes input 896).drop 893 == [82, 77, 77] &&
    H.h128.readBytes (rho ++ [5, 2]) 1 == [77] &&
    H.h128.readBytes (rho ++ [2, 3]) 1 == [50] &&
    H.h128.read (x ++ [false]) 1 == [77] && H.h256.read x 1 == [88]

#guard matrixAddressChecks

-- One expansion samples 16, 30 or 56 entries at the respective FIPS levels.
open Cslib.Probability in
example (H : Xofs) (s : Level) (rho : List Byte) :
    ((PMF.uniformOfFintype (MatrixPrefixes s)).toOuterMeasure
      {t | (H.withMatrixPrefixes s rho t).expandA s rho = none}).toReal <
      1 / (2 : ℝ) ^ (match s with | .mlDSA44 => 252 | .mlDSA65 => 251 | .mlDSA87 => 250) := by
  apply (prob_expandA_exhaustion H s rho).trans_le
  cases s
  · change (16 : ℝ) / 2 ^ 256 ≤ 1 / 2 ^ 252
    norm_num
  · change (30 : ℝ) / 2 ^ 256 ≤ 1 / 2 ^ 251
    norm_num
  · change (56 : ℝ) / 2 ^ 256 ≤ 1 / 2 ^ 250
    norm_num

private def markedNonce : Xofs :=
  let address := Keccak.bytesToBitsLE (List.replicate 64 0 ++ [1, 0])
  ⟨constantStream (fun _ => 0), constantStream (fun x => if x = address then 1 else 0)⟩

private def secretAtNonceOne : Option (ZMod 8380417) := do
  let keys ← markedNonce.keyGen .mlDSA44 (fun _ => 0)
  let sk ← decodePrivate .mlDSA44 keys.secretKey
  return sk.s₁ ⟨1, by decide⟩ 0

#guard secretAtNonceOne == some 1
#guard ((markedNonce.expandMask .mlDSA44 (List.replicate 64 0) 1).get ⟨0, by decide⟩).get 0 ==
  65279

-- An XOF returning 0xff on every stream makes the matrix and the Algorithm 29 sampler
-- exhaust their bounded reads. Both failures must propagate through the FIPS code.
private def allOnesXof := constantStream (fun _ => 255)

#guard ((Xofs.mk allOnesXof allOnesXof).keyGen .mlDSA44 (fun _ => 0)).isNone
#guard ((Xofs.mk allOnesXof allOnesXof).sampleInBall .mlDSA87 []).isNone

-- With a collision in the message representative, the exact bytes returned by the signer
-- can verify on a different request. Recover the two raw message inputs from the log.
private def repeatedAcrossMessages : Bool := Id.run do
  let H := Xofs.mk (constantStream fun _ => 0)
    (constantStream fun x => if x.length = 528 then 85 else 0)
  let some keys := H.keyGen .mlDSA44 (fun _ => 0) | return false
  let some sig := H.sign .mlDSA44 keys.secretKey [true] [7] (fun _ => 0) | return false
  let some A := H.expandA .mlDSA44 (keys.publicKey.take 32) | return false
  let signed : Forgery := ⟨[7], [true], sig⟩
  let forged : Forgery := ⟨[], [true, false, true], sig⟩
  let some (.collision x y) := H.extractLoggedDigest .mlDSA44 keys.publicKey A forged [signed]
    | return false
  let tr := H.h256.readBytes keys.publicKey 64
  return H.verify .mlDSA44 keys.publicKey forged.message forged.context sig == some true &&
    x != y && x == representativeInput tr (formattedMessage forged) &&
    y == representativeInput tr (formattedMessage signed) && H.h256.read x 32 == H.h256.read y 32

#guard repeatedAcrossMessages

-- Different 32-byte seeds can expand to the same sparse polynomial. Preserve their
-- eight exposed sign bytes while filling each rejection tape with zero bytes.
private def collidingExpansionRows : Option Bool := do
  let a := List.replicate 32 (0 : Byte)
  let b := (1 : Byte) :: List.replicate 31 0
  let rows : Finset (List Bool) := {Keccak.bytesToBitsLE a, Keccak.bytesToBitsLE b}
  let background := constantStream (fun _ => 247)
  let H : Xofs := ⟨background, background.fill (rows := rows) (width := 221)
    (fun _ => 8) (fun _ _ => 0)⟩
  let c ← H.sampleInBall .mlDSA44 a
  let c' ← H.sampleInBall .mlDSA44 b
  return a != b && c == c' && H.h256.readBytes a 9 == List.replicate 8 247 ++ [0] &&
    H.h256.readBytes [] 9 == List.replicate 9 247

#guard collidingExpansionRows == some true

-- Once all 221 input bytes have been read, reprogramming the suffix cannot alter
-- the actual signature challenge, including exhaustion.
example (H : Xofs) (s : Level) (d : List Byte) (seen : List Bool → ℕ)
    (table : digestRows s → FixedBytes 221) (h : 221 ≤ seen (Keccak.bytesToBitsLE d)) :
    (H.withExpansionRows s seen table).sampleInBall s d = H.sampleInBall s d := by
  apply congrArg (sampleInBallBytes s)
  exact H.h256.read_fill_of_le seen table h

-- The first reply is actually passed to the continuation. Returning exactly those bytes as
-- the forgery is rejected, even when they verify, because the genuine reply was logged.
example (K : Xofs) (s : Level) (keys : KeyPair) (q : SigningQuery) (sig : List Byte) :
    K.continueFirstSigning s keys q (some sig) (fun _ _ ans =>
      pure ⟨q.context, q.message, ans.getD []⟩) = PMF.pure false := by
  simp [Xofs.continueFirstSigning, Xofs.winsForgery, SigningQuery.logReply,
    Cslib.ProbOracleComp.runWith_pure]

-- The forger selects the signing context from SHAKE128, then uses the actual signing reply
-- as its SHAKE256 input. Both public reads use the same oracle pair as the protocol.
private def readSignRead (msg : List Bool) : ClassicalForger := fun _ => do
  let ctx ← Cslib.ProbOracleComp.query (spec := PublicQuery.Reply) (.shake128 msg 2)
  let reply ← Cslib.ProbOracleComp.query (spec := PublicQuery.Reply) (.sign ⟨ctx, msg⟩)
  let sig ← Cslib.ProbOracleComp.query (spec := PublicQuery.Reply)
    (.shake256 (Keccak.bytesToBitsLE (reply.getD [])) 32)
  return ⟨ctx, msg, sig⟩

example (H : Xofs) (msg : List Bool) :
    H.answerPublicReads (readSignRead msg) [] = (do
      let ctx := H.h128.read msg 2
      let reply ← Cslib.ProbOracleComp.query (spec := fun _ : SigningQuery => Option (List Byte))
        ⟨ctx, msg⟩
      return ⟨ctx, msg, H.h256.read (Keccak.bytesToBitsLE (reply.getD [])) 32⟩) := by
  simp only [Xofs.answerPublicReads, readSignRead, Cslib.ProbOracleComp.simulate_bind,
    Cslib.ProbOracleComp.simulate_pure, Cslib.ProbOracleComp.simulate_query]
  rfl

namespace Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger
open Cslib.Quantum Cslib.Probability

-- The output bit records whether the single signing request returned the public error.
private def signingProbe (q : SigningQuery) : QuantumSigningForger where
  addressBits := 2
  responseBytes := 1
  workQubits := 0
  program _ := do
    let answer ← ProbOracleComp.query (spec := OracleSpec.sum
      (fun _ : DeviceRequest 12 Empty => List Bool) (fun _ : SigningQuery => Option (List Byte)))
      (Sum.inr q)
    return ⟨[], [answer.isNone], []⟩

-- Every candidate byte exceeds Algorithm 29's initial acceptance threshold 217 at ML-DSA-44.
private theorem allOnesExhausts (other : ExtendableOutput) (d : List Byte) :
    (Xofs.mk other allOnesXof).sampleInBall .mlDSA44 d = none := by
  have rejected (n : ℕ) : ChallengeRow.parse 217 39 (List.replicate n 255) = none := by
    induction n with
    | zero => rw [List.replicate_zero, ChallengeRow.parse]
    | succ n ih =>
      rw [List.replicate_succ, ChallengeRow.parse, dite_eq_left (by decide), ih]
      rfl
  unfold Xofs.sampleInBall sampleInBallBytes
  change (ChallengeRow.parse 217 39 (List.replicate 213 255)).bind _ = none
  rw [rejected]
  rfl

-- Every digest on the all-255 stream exhausts Algorithm 29, independently of the public pair.
private theorem fatalDraw (other : ExtendableOutput) (pair : MLDSA.PublicKey Level.mlDSA44.params) :
    publicDraw .mlDSA44 pair ⟨other, allOnesXof⟩ =
      (PMF.uniformOfFintype (FixedBytes (digestBytes .mlDSA44))).bind fun d =>
      (signingMaskLaw Level.mlDSA44.params (by decide)).bind fun y =>
        PMF.pure (some ⟨highBitsVec Level.mlDSA44.params (moduleSISMap pair.A y), d, none,
          fun _ => allOnesExhausts other d.toList, by simp⟩) := by
  unfold publicDraw draw
  congr 1
  funext d
  split
  · rfl
  · next h => simp [allOnesExhausts] at h

example (other : ExtendableOutput) (rho : FixedBytes 32)
    (pair : MLDSA.PublicKey Level.mlDSA44.params) :
    let q : SigningQuery := ⟨[], [true]⟩
    (((signingProbe q).publicPairSigning .mlDSA44 ⟨other, allOnesXof⟩ rho pair).map fun result =>
      (result.trial.forgery.message, result.writes.map (fun w => (w.request, w.reply)),
        result.trial.log)) = PMF.pure ([true], [(q, none)], []) := by
  intro q
  simp only [publicPairSigning, runProgrammed, runSigningProgram, programmedCommands,
    statefulSigningCommands, signingProbe, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, OracleComp.sumHandler, signingCall,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, q,
    List.length_nil, Nat.not_lt_zero, ite_false]
  rw [show List.range 814 = 0 :: List.range' 1 813 by rw [List.range_eq_range', List.range'_succ],
    List.findSomeM?_cons]
  simp only [fatalDraw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind, PMF.bind_const, PMF.map_bind, PMF.pure_map,
    SigningQuery.logReply, List.nil_append, List.map_cons, List.map_nil, Option.isNone_none]

-- The context check precedes the first attempt and even the shared raw XOFs stay identical.
example (s : Level) (H : Xofs) (rho : FixedBytes 32) (pair : MLDSA.PublicKey s.params) :
    let q : SigningQuery := ⟨List.replicate 256 0, [true]⟩
    (((signingProbe q).publicPairSigning s H rho pair).map fun result =>
      (result.trial.forgery.message, result.writes, result.trial.log, result.trial.xofs)) =
      PMF.pure ([true], [], [], H) := by
  intro q
  simp only [publicPairSigning, runProgrammed, runSigningProgram, programmedCommands,
    statefulSigningCommands, signingProbe, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, OracleComp.sumHandler, signingCall,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, q,
    List.length_replicate, show 255 < 256 by decide, ite_true, PMF.pure_map, PMF.pure_bind,
    Option.isNone_none]

end Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger

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

-- The classical comparison permits 814 attempts on each of 2^64 signing requests.
-- At the three hash-query budgets its statistical-distance contribution remains below one.
example (s : Level) :
    let h : ℕ := match s with | .mlDSA44 => 128 | .mlDSA65 => 192 | .mlDSA87 => 256
    let bits : ℕ := match s with | .mlDSA44 => 32 | .mlDSA65 => 373 | .mlDSA87 => 566
    let t := 2 ^ 64 * 814
    ((2 * t * 2 ^ h + t.choose 2 : ℕ) : ℝ) *
      ((11 / 10) / Real.sqrt (2 ^ s.commitmentBoxBits)) ≤ 1 / 2 ^ bits := by
  intro h bits t
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  apply (Real.le_sqrt (by positivity) (by positivity)).2
  let count := 2 * t * 2 ^ h + t.choose 2
  have cert : (11 * count * 2 ^ bits) ^ 2 ≤ 100 * 2 ^ s.commitmentBoxBits := by
    dsimp only [count, t]
    rw [Nat.choose_two_right]
    cases s <;> decide +kernel
  have bound : ((11 : ℝ) * count * 2 ^ bits) ^ 2 ≤ 100 * 2 ^ s.commitmentBoxBits := by
    exact_mod_cast cert
  change ((count : ℝ) * (11 / 10) * 2 ^ bits) ^ 2 ≤ _
  nlinarith only [bound]
