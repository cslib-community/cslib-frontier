/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.ChallengeRowProgramming
public import CslibFrontier.Crypto.Computational.MLDSA.RandomXof
public import CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.ValueQuery
import all CslibFrontier.Crypto.Computational.MLDSA.ChallengeRowProgramming
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import all CslibFrontier.Crypto.Computational.MLDSA.RandomXof
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning

/-!
# Sparse challenges at the digest inputs of the ML-DSA random oracle

[FIPS 204][NISTFIPS204], Algorithm 29 reads a SHAKE256 prefix at the digest in the signature.
Exchange these 221-byte rows with independent signed sparse polynomials simultaneously at every
digest. The whole pair of raw oracles has its original distribution, so the exchange applies
before key generation and also to coherent queries, including longer reads at the same addresses.
The sparse table here is indexed by digest. In [Dilithium v3.1][BaiEtAl2021Dilithium], §6.1,
SelfTargetMSIS indexes challenges by the full lattice product and message.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability Cslib.Quantum

private abbrev DigestWord (s : Level) := BitString (8 * digestBytes s)

/-- Install the sparse oracle's signed challenges in the 221-byte expansion prefixes at digest
addresses. Exhausted rows retain their bytes. All uses of each raw address see one stream. -/
def Xofs.withSparseDigestChallenges (H : Xofs) (s : Level)
    (rows : BitString (8 * digestBytes s) → FixedBytes 221)
    (challenges : BitString (8 * digestBytes s) → ChallengeRow.Target s) : Xofs :=
  H.withPrefixLists (8 * digestBytes s) fun x =>
    let digest := (Vector.ofFn x).get
    let row : FixedBytes 221 := (Vector.ofFn (rows digest)).get
    (ChallengeRow.exchangeSampleInBall s (row, challenges digest)).1.toList

/-- Native Algorithm 29 on the modified raw SHAKE256 oracle returns the supplied sparse
challenge whenever the original byte row succeeds, with exactly the original exhaustion event. -/
theorem Xofs.sampleInBall_withSparseDigestChallenges (H : Xofs) (s : Level)
    (rows : BitString (8 * digestBytes s) → FixedBytes 221)
    (challenges : BitString (8 * digestBytes s) → ChallengeRow.Target s)
    (digest : FixedBytes (digestBytes s)) :
    let d := Keccak.fixedBytesEquivBitsLE _ digest
    (H.withSparseDigestChallenges s rows challenges).sampleInBall s digest.toList =
      (sampleInBallBytes s (rows d).toList).map fun _ => (challenges d).val := by
  intro d
  have bits := Keccak.ofFn_fixedBytesEquivBitsLE digest
  change List.ofFn d = _ at bits
  have read : (H.withSparseDigestChallenges s rows challenges).h256.readBytes digest.toList 221 =
      (ChallengeRow.exchangeSampleInBall s (rows d, challenges d)).1.toList := by
    simp only [withSparseDigestChallenges, withPrefixLists, ExtendableOutput.readBytes,
      ← bits, List.length_ofFn, ↓reduceIte, BitString.ofList_ofFn,
      funext (Vector.get_ofFn _),
      ExtendableOutput.withPrefixes, ExtendableOutput.readWithPrefix,
      List.take_of_length_le (FixedBytes.length_toList _).le, FixedBytes.length_toList,
      List.drop_eq_nil_of_le (H.h256.length_read ..).le, List.append_nil]
  unfold Xofs.sampleInBall
  rw [read]
  cases h : sampleInBallBytes s (rows d).toList with
  | none => rw [ChallengeRow.exchangeSampleInBall_of_none h, h]; rfl
  | some c => exact (ChallengeRow.exchangeSampleInBall_of_some h _).1

private theorem uniform_exchangedRowBits (s : Level) :
    (PMF.uniformOfFintype (DigestWord s → FixedBytes 221)).bind (fun rows =>
      (PMF.uniformOfFintype (DigestWord s → ChallengeRow.Target s)).map fun c x =>
        Keccak.fixedBytesEquivBitsLE 221
          (ChallengeRow.exchangeSampleInBall s (rows x, c x)).1) =
      PMF.uniformOfFintype (DigestWord s → BitString (8 * 221)) := by
  let split := Equiv.arrowProdEquivProdArrow (DigestWord s)
    (fun _ => FixedBytes 221) (fun _ => ChallengeRow.Target s)
  let swap := Equiv.piCongrRight (fun _ : DigestWord s => ChallengeRow.exchangeSampleInBall s)
  let pack := Equiv.piCongrRight (fun _ : DigestWord s => Keccak.fixedBytesEquivBitsLE 221)
  exact PMF.uniformOfFintype_bind_map_fst_equiv
    ((split.symm.trans (swap.trans split)).trans (Equiv.prodCongr pack (Equiv.refl _)))

/-- With independent uniform seed rows and sparse challenges at all digest addresses,
the complete programmed raw oracle pair is distributed as the original finite random XOFs. -/
theorem Xofs.uniformPrefixes_sparseDigestChallenges (base : Xofs) (s : Level) {a b : ℕ}
    (ha : 8 * digestBytes s ≤ a) (hb : 221 ≤ b) :
    ((base.uniformPrefixes a b).bind fun H =>
      (PMF.uniformOfFintype (BitString (8 * digestBytes s) → FixedBytes 221)).bind fun rows =>
        (PMF.uniformOfFintype (BitString (8 * digestBytes s) → ChallengeRow.Target s)).map fun c =>
          H.withSparseDigestChallenges s rows c) = base.uniformPrefixes a b := by
  have law := congrArg (PMF.map Prod.snd)
    (base.uniformPrefixes_prefixRegister (8 * digestBytes s) 221 ha hb)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at law
  rw [show (fun x : Xofs => x) = id from rfl, PMF.map_id] at law
  refine Eq.trans ?_ law
  apply congrArg (PMF.bind _ ·)
  funext H
  have e := congrArg (PMF.map (H.withPrefixRegister (8 * digestBytes s) 221))
    (uniform_exchangedRowBits s)
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, withSparseDigestChallenges,
    funext (Vector.get_ofFn _), withPrefixLists_toList] using e

/-- The entire strong-forgery experiment can draw the digest-indexed sparse challenges before
setup. The key generator, signing service, coherent raw queries and verifier use the same XOFs. -/
theorem QuantumSigningForger.randomPrefixGame_eq_sparseDigestChallenges (C : QuantumSigningForger)
    (base : Xofs) (s : Level) {a b : ℕ} (ha : 8 * digestBytes s ≤ a) (hb : 221 ≤ b) :
    C.randomPrefixGame s base a b =
      (base.uniformPrefixes a b).bind fun H =>
        (PMF.uniformOfFintype (BitString (8 * digestBytes s) → FixedBytes 221)).bind fun rows =>
          (PMF.uniformOfFintype (BitString (8 * digestBytes s) → ChallengeRow.Target s)).bind
            fun c => C.forgeryGame (H.withSparseDigestChallenges s rows c) s := by
  have law := congrArg (PMF.bind · (fun H => C.forgeryGame H s))
    (base.uniformPrefixes_sparseDigestChallenges s ha hb)
  simpa only [randomPrefixGame, PMF.bind_bind, PMF.bind_map, Function.comp_def] using law.symm

/-- A sparse challenge in an XOR response register. The first 256 bits mark its nonzero
coefficients and the next 256 bits mark its negative coefficients, both in coefficient order. -/
def ChallengeRow.Target.responseBits {s : Level} (c : ChallengeRow.Target s) : BitString 512 :=
  Fin.append (fun i : Fin 256 => decide (c.val i ≠ 0))
    (fun i : Fin 256 => decide (c.val i = -1))

private def responsePolynomial (v : BitString 512) : Poly := fun i =>
  if v (Fin.castAdd 256 i) then if v (Fin.natAdd 256 i) then -1 else 1 else 0

private theorem responsePolynomial_bits {s : Level} (c : ChallengeRow.Target s) :
    responsePolynomial c.responseBits = c.val := by
  funext i
  simp only [responsePolynomial, ChallengeRow.Target.responseBits, Fin.append_left,
    Fin.append_right, decide_eq_true_eq]
  by_cases h : c.val i = 0
  · simp [h]
  · simpa only [h, ne_eq, not_false_eq_true, ↓reduceIte] using c.coeff_of_ne i h

private def asTarget (s : Level) (p : Poly) : Option (ChallengeRow.Target s) :=
  if h : InBall s.params.τ p then some ⟨p, h⟩ else none

private theorem asTarget_val {s : Level} (c : ChallengeRow.Target s) :
    asTarget s c.val = some c := dite_eq_left c.property

/-- Compute a native raw SHAKE reply from the value loaded from the sparse digest oracle.
Rows, the background XOFs and the wire address determine the rest of the response. -/
def Xofs.sparseDigestResponse (H : Xofs) (s : Level)
    (rows : BitString (8 * digestBytes s) → FixedBytes 221) (a b : ℕ)
    (x : BitString (a + 2)) (v : BitString 512) : BitString (8 * b) :=
  (H.withPrefixLists (8 * digestBytes s) fun _ =>
    -- Reading the decoded digest at many indices can traverse the raw address repeatedly.
    let address := (Vector.ofFn x).get
    let digest := (Vector.ofFn (Xofs.prefixLookup (8 * digestBytes s) address)).get
    let row : FixedBytes 221 := (Vector.ofFn (rows digest)).get
    let bits := (Vector.ofFn v).get
    match asTarget s (responsePolynomial bits) with
    | none => row.toList
    | some c => (ChallengeRow.exchangeSampleInBall s (row, c)).1.toList).queryTable a b x

/-- Two coherent XOR queries to the digest-indexed sparse polynomial oracle implement a
placed native raw SHAKE query on arbitrary superpositions and clean both scratch registers. -/
theorem Xofs.xorQuery_withSparseDigestChallenges (H : Xofs) (s : Level)
    (rows : BitString (8 * digestBytes s) → FixedBytes 221)
    (c : BitString (8 * digestBytes s) → ChallengeRow.Target s) (a b m : ℕ)
    (wires : Fin (a + 2 + 8 * b) ↪ Fin m) (ψ : Qubits m) :
    runValue addStep (lookupXorSteps wires (Xofs.prefixLookup (8 * digestBytes s))
      (H.sparseDigestResponse s rows a b)) (cleanLookupState ψ) (fun d => (c d).responseBits) 2 =
      cleanLookupState ((xorQuery ((H.withSparseDigestChallenges s rows c).queryTable a b)
        wires).eval ψ) := by
  rw [runValue_lookupXorSteps]
  unfold Xofs.withSparseDigestChallenges
  rw [Xofs.queryTable_withPrefixLists H]
  simp only [sparseDigestResponse, funext (Vector.get_ofFn _),
    responsePolynomial_bits, asTarget_val]

end Cslib.Crypto.MLDSA.FIPS204
