/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Crypto.Computational.MLDSA.SignedMatrix
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import all CslibFrontier.Crypto.Computational.MLDSA.PublicPairSigning
import CslibFrontier.Crypto.Computational.MLDSA.RejNTTExhaustion
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
  return Keccak.shake256 keys.publicKey 32 == publicKeyFingerprint &&
    Keccak.shake256 keys.secretKey 32 == secretKeyFingerprint &&
    verify .mlDSA44 keys.publicKey msg ctx σ == some true &&
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
  simp only [publicPairSigning, runProgrammed, signingProbe, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, OracleComp.sumHandler, signingCall,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, q, List.length_nil, Nat.not_lt_zero, ite_false]
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
  simp only [publicPairSigning, runProgrammed, signingProbe, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure, OracleComp.sumHandler, signingCall,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, q, List.length_replicate,
    show 255 < 256 by decide, ite_true, PMF.pure_map, PMF.pure_bind, Option.isNone_none]

end Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger
