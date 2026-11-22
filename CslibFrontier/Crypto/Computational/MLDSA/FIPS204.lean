/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.Signing
public import CslibFrontier.Crypto.Computational.SIS.SelfTargetFork
public import CslibFrontier.Crypto.Primitives.Hash.ExtendableOutput
public import CslibFrontier.Crypto.Primitives.Hash.Keccak.SHAKE128
public import CslibFrontier.Probability.PMF
import all CslibFrontier.Crypto.Computational.MLDSA.CompressedKeyOnly
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Crypto.Game.Order
import Batteries.Data.Vector.Lemmas
import Mathlib.Data.List.Sort
import Mathlib.Order.Interval.Finset.Fin
import CslibFrontier.Foundations.Data.List.Flatten
import CslibFrontier.Foundations.Data.BitString.List

/-!
# ML-DSA verification on byte keys and signatures

[FIPS 204][NISTFIPS204], Algorithms 3, 6 and 8, with the Appendix C output limits for SHAKE
rejection sampling. Verification distinguishes a malformed signature (`some false`) from XOF
exhaustion (`none`). The signing digest and the challenge polynomial have distinct types.
The ring products use the coefficient form of Algorithm 8, line 9.

The key-only reduction retains the matrix seed and the verifier's SHAKE-derived message
representative. Its setup samples the Algorithm 6 key-generation seed. The resulting
self-target experiment has that same seeded setup. For challenges supplying a full vector and a
matrix at the published seed, `decode_encodePublic` recovers the rounded high term, and
`verifiedSignature_of_verifyWithExpansion` recovers the full digest check for that vector.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability

/-- The two XOFs used by FIPS 204. Each SHAKE variant has a single raw-bit input space,
shared by key generation, signing, verification and external queries. -/
@[ext] structure Xofs where
  /-- The XOF used to expand the public matrix. -/
  h128 : ExtendableOutput
  /-- The XOF used for secret expansion, masks, message representatives and challenges. -/
  h256 : ExtendableOutput

/-- FIPS 202 instantiation of the two FIPS 204 XOFs. -/
def Xofs.shake : Xofs :=
  let xof (layout : Keccak.SpongeLayout) : ExtendableOutput :=
    { read := Keccak.bitSponge layout [true, true, true, true]
      length_read := Keccak.length_bitSponge layout _
      take_read := fun x _ _ h => Keccak.take_bitSponge layout _ x h }
  ⟨xof Keccak.shake128Layout, xof Keccak.shake256Layout⟩

/-- The parameter choices from FIPS 204, Table 1. -/
inductive Level where
  | mlDSA44 | mlDSA65 | mlDSA87
deriving DecidableEq

/-- Ring and shortness parameters for the selected standard parameter set. -/
abbrev Level.params (s : Level) : Params :=
  let p := match s with
    | .mlDSA44 => Params.mldsa44
    | .mlDSA65 => Params.mldsa65
    | .mlDSA87 => Params.mldsa87
  { p with n := 256, q := 8380417 }

/-- Each FIPS parameter set satisfies the ring, challenge and rounding conditions. -/
theorem Level.valid (s : Level) : s.params.Valid := by
  cases s
  · exact Params.valid_mldsa44
  · exact Params.valid_mldsa65
  · exact Params.valid_mldsa87

/-- Byte length of the commitment digest (FIPS 204, Table 1, `2λ` bits). -/
@[expose] def digestBytes : Level → ℕ
  | .mlDSA44 => 32 | .mlDSA65 => 48 | .mlDSA87 => 64

/-- Maximum Hamming weight of the complete hint vector (Table 1). -/
def hintLimit : Level → ℕ
  | .mlDSA44 => 80 | .mlDSA65 => 55 | .mlDSA87 => 75

/-- A coefficient polynomial in the FIPS 204 negacyclic ring. -/
abbrev Poly := Fin 256 → ZMod 8380417

/-- The coefficient representation of the public module matrix for the selected parameter set. -/
abbrev PublicMatrix (s : Level) := Matrix (Fin s.params.k) (Fin s.params.ℓ) Poly

/-- Pack fixed-width nonnegative coefficients in row-major, low-bit-first order. -/
def packCoeffs {rows : ℕ} (width : ℕ) (coeff : Fin rows → Fin 256 → ℕ) : List Byte :=
  let bits := (List.finRange rows).flatMap fun i =>
    (List.finRange 256).flatMap fun j => BitString.lowBits width (coeff i j)
  (bits.toChunks 8).map Keccak.bitsToByteLE

private def unpackCoeff (bits : List Bool) (width index : ℕ) : ℕ :=
  BitString.lsbValue ((bits.drop (width * index)).take width)

/-- Fixed-width packing uses exactly 32 times the field width bytes per polynomial. -/
@[simp] theorem length_packCoeffs {rows width : ℕ} (coeff : Fin rows → Fin 256 → ℕ) :
    (packCoeffs width coeff).length = 32 * width * rows := by
  let bits := (List.finRange rows).flatMap fun i =>
    (List.finRange 256).flatMap fun j => BitString.lowBits width (coeff i j)
  have len : bits.length = rows * (256 * width) := by
    simp only [bits, List.length_flatMap, BitString.length_lowBits, List.map_const',
      List.length_finRange, List.sum_replicate_nat]
  have hdiv : 8 ∣ bits.length := ⟨rows * (32 * width), by rw [len]; ring⟩
  have he := congrArg List.length (Keccak.bytesToBitsLE_toChunks hdiv)
  rw [Keccak.length_bytesToBitsLE, len] at he
  change ((bits.toChunks 8).map Keccak.bitsToByteLE).length = _
  nlinarith

private theorem unpack_packCoeffs {rows width : ℕ} (coeff : Fin rows → Fin 256 → ℕ)
    (hc : ∀ i j, coeff i j < 2 ^ width) (i : Fin rows) (j : Fin 256) :
    unpackCoeff (Keccak.bytesToBitsLE (packCoeffs width coeff)) width (256 * i + j) =
      coeff i j := by
  let flat : Fin (rows * 256) → List Bool := fun a =>
    BitString.lowBits width (coeff ⟨a / 256, by have := a.isLt; omega⟩ ⟨a % 256, by omega⟩)
  have hflat (a : Fin (rows * 256)) : (flat a).length = width := BitString.length_lowBits _ _
  have hbits : ((List.finRange rows).flatMap fun i => (List.finRange 256).flatMap
      fun j => BitString.lowBits width (coeff i j)) = (List.ofFn flat).flatten := by
    rw [List.ofFn_mul flat]
    simp only [List.flatMap_def, ← List.ofFn_eq_map, List.flatten_flatten, List.map_ofFn,
      Function.comp_def]
    congr 1
    apply congrArg List.ofFn
    funext a
    congr 1
    apply congrArg List.ofFn
    funext b
    have hdiv : (a.val * 256 + b.val) / 256 = a.val := by omega
    have hmod : (a.val * 256 + b.val) % 256 = b.val := by omega
    simp only [flat, hdiv, hmod, Fin.eta]
  have hlen : (List.ofFn flat).flatten.length = rows * 256 * width := by
    simp [List.length_flatten, List.map_ofFn, Function.comp_def, hflat]
  let idx : Fin (rows * 256) := ⟨256 * i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩
  have hrow := BitString.listRow_flatten_ofFn flat hflat idx
  have hremaining : width ≤ ((List.ofFn flat).flatten.drop (idx.val * width)).length := by
    rw [List.length_drop, hlen]
    have hmul := Nat.mul_le_mul_right width (Nat.succ_le_of_lt idx.isLt)
    rw [Nat.succ_mul] at hmul
    omega
  rw [BitString.listRow, List.take_append_of_le_length hremaining] at hrow
  simp only [packCoeffs, hbits,
    Keccak.bytesToBitsLE_toChunks (by rw [hlen]; exact ⟨rows * 32 * width, by ring⟩),
    unpackCoeff]
  rw [show width * (256 * (i : ℕ) + j) = idx.val * width by exact Nat.mul_comm .., hrow]
  have hi : idx.val / 256 = i.val := by dsimp [idx]; omega
  have hj : idx.val % 256 = j.val := by dsimp [idx]; omega
  simpa only [flat, hi, hj, Fin.eta] using BitString.lsbValue_lowBits (hc i j)

/-- FIPS 204 Algorithm 14 reads the low 23 bits of three little-endian bytes. -/
@[expose] def nttCandidate (a b c : Byte) : ℕ :=
  a.val + 256 * b.val + 65536 * (c.val % 128)

/-- The successive accepted coefficients of Algorithm 30 on a finite XOF prefix. -/
@[expose] def rejNTTCoefficients : List Byte → List (ZMod 8380417)
  | a :: b :: c :: rest =>
    let x := nttCandidate a b c
    if x < 8380417 then (x : ZMod 8380417) :: rejNTTCoefficients rest else rejNTTCoefficients rest
  | _ => []

private def asPoly (coeffs : List (ZMod 8380417)) : Option Poly :=
  let a := coeffs.toArray
  if a.size < 256 then none else some (fun j => a[j.val]!)

/-- Algorithm 30 on a finite SHAKE128 stream, failing if it supplies fewer than 256
accepted coefficients. The result is still in NTT order. -/
def rejNTTPoly (bytes : List Byte) : Option Poly :=
  asPoly (rejNTTCoefficients bytes)

/-- Exhaustion occurs exactly when fewer than 256 coefficients were accepted. -/
theorem rejNTTPoly_eq_none_iff (bytes : List Byte) :
    rejNTTPoly bytes = none ↔ (rejNTTCoefficients bytes).length < 256 := by
  simp [rejNTTPoly, asPoly]

/-- The sampled NTT vector consists of the first 256 accepted coefficients in stream order. -/
theorem rejNTTPoly_eq_some_iff (bytes : List Byte) (v : Poly) :
    rejNTTPoly bytes = some v ↔ (rejNTTCoefficients bytes).take 256 = List.ofFn v := by
  let xs := rejNTTCoefficients bytes
  change asPoly xs = some v ↔ xs.take 256 = List.ofFn v
  by_cases h : xs.length < 256
  · have hne : xs.take 256 ≠ List.ofFn v := by
      intro he
      have := congrArg List.length he
      simp only [List.length_take, List.length_ofFn] at this
      omega
    simp only [asPoly, List.size_toArray, h, ite_true, reduceCtorEq, hne]
  · simp only [asPoly, List.size_toArray, ite_eq_right h, Option.some.injEq]
    constructor
    · rintro rfl
      apply List.ext_getElem
      · simp only [List.length_take, List.length_ofFn]; omega
      · intro i hi _
        have hx : i < xs.toArray.size := by
          simp only [List.length_take] at hi
          rw [List.size_toArray]
          omega
        simp only [List.getElem_take, List.getElem_ofFn, getElem!_pos xs.toArray i hx,
          List.getElem_toArray]
    · intro hv
      funext i
      have ha : i.val < xs.toArray.size := by rw [List.size_toArray]; omega
      have ht : i.val < (xs.take 256).length := by rw [List.length_take]; omega
      have hv' : i.val < (List.ofFn v).length := by simpa only [List.length_ofFn] using i.isLt
      have he : (xs.take 256)[i.val] = (List.ofFn v)[i.val] := by simp only [hv]
      simpa only [getElem!_pos xs.toArray i.val ha, List.getElem_toArray, List.getElem_take,
        List.getElem_ofFn]
        using he

/-- Reverse the eight bits of the FIPS evaluation index (§§2.5 and 7.5). -/
@[expose] def bitRev8 (i : Fin 256) : Fin 256 :=
  ⟨BitString.lsbValue (BitString.lowBits 8 i.val).reverse, by
    simpa using BitString.lsbValue_lt (BitString.lowBits 8 i.val).reverse⟩

/-- The coefficient of degree `j` in the inverse NTT, using the evaluation points
`ζ^(2 BitRev8(i)+1)` (FIPS 204 §2.5, equation (2.1)). The inverse of 256 modulo q is 8347681. -/
@[expose] def fromNTT (values : Poly) : Vector (ZMod 8380417) 256 :=
  let roots := Vector.ofFn fun a : Fin 512 => (1753 : ZMod 8380417) ^ a.val
  let inversePowers := Vector.ofFn fun i : Fin 256 =>
    511 - 2 * (bitRev8 i).val
  Vector.ofFn fun j : Fin 256 =>
    8347681 * ∑ i, values i * roots.get (Fin.ofNat 512 (inversePowers.get i * j.val))

private def tabulate {α : Type} (n : ℕ) (f : Fin n → Option α) : Option (Fin n → α) :=
  (fun v : Vector α n => v.get) <$> Vector.ofFnM f

/-- Algorithms 30 and 32, returning the matrix in coefficient representation. Each SHAKE128
stream absorbs `ρ || column || row` and may consume 894 bytes (Appendix C, Table 3). -/
def Xofs.expandA (H : Xofs) (s : Level) (rho : List Byte) :
    Option (PublicMatrix s) := do
  let matrix ← Vector.ofFnM fun row : Fin s.params.k =>
    Vector.ofFnM fun col : Fin s.params.ℓ =>
      fromNTT <$> rejNTTPoly (H.h128.readBytes
        (rho ++ [Fin.ofNat 256 col.val, Fin.ofNat 256 row.val]) 894)
  return fun i j => ((matrix.get i).get j).get

/-- Algorithm 32 depends only on SHAKE128. -/
theorem Xofs.expandA_congr {H K : Xofs} (ha : K.h128 = H.h128) (s : Level) (rho : List Byte) :
    K.expandA s rho = H.expandA s rho := by
  cases H
  cases K
  cases ha
  rfl

/-- FIPS 202 specialization of `Xofs.expandA`. -/
abbrev expandA := Xofs.expandA Xofs.shake

private def boundedCoeff (η halfByte : ℕ) : Option (ZMod 8380417) :=
  if η = 2 then
    if halfByte < 15 then some ((2 : ZMod 8380417) - ↑(halfByte % 5)) else none
  else if halfByte < 9 then some (4 - (halfByte : ZMod 8380417)) else none

/-- The two counter bytes absorbed by Algorithms 33 and 34, least significant byte first. -/
def nonceSuffix (i : ℕ) : FixedBytes 2 := ![Fin.ofNat 256 i, Fin.ofNat 256 (i / 256)]

/-- Algorithms 33 and 34 append the two-byte little-endian counter to the 64-byte seed. -/
@[expose] def nonceInput (seed : List Byte) (nonce : ℕ) : List Byte :=
  seed ++ [nonceSuffix nonce 0, nonceSuffix nonce 1]

/-- A nonce-tagged 64-byte expansion seed occupies 528 SHAKE input bits. -/
theorem length_nonceInput_bits (seed : FixedBytes 64) (nonce : ℕ) :
    (Keccak.bytesToBitsLE (nonceInput seed.toList nonce)).length = 528 := by
  rw [Keccak.length_bytesToBitsLE, nonceInput, List.length_append, FixedBytes.length_toList seed]
  rfl

/-- For a fixed seed, the two-byte little-endian suffix recovers any counter below 65536. -/
theorem eq_of_nonceInput_eq {seed : List Byte} {i j : ℕ} (hi : i < 65536) (hj : j < 65536)
    (eq : nonceInput seed i = nonceInput seed j) : i = j := by
  simp only [nonceInput, List.append_cancel_left_eq, List.cons.injEq, and_true] at eq
  have lo := congrArg Fin.val eq.1
  have high := congrArg Fin.val eq.2
  simp only [nonceSuffix, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_ofNat] at lo high
  lia

/-- An Algorithm 34 mask row has a 64-byte seed and two counter bytes. It cannot alias
the SHAKE input at the 32-, 48-, or 64-byte digest consumed by Algorithm 29. -/
theorem nonceInput_ne_digestInput {s : Level} (seed : FixedBytes 64) (nonce : ℕ)
    {d : List Byte} (hd : d.length = digestBytes s) :
    Keccak.bytesToBitsLE (nonceInput seed.toList nonce) ≠ Keccak.bytesToBitsLE d := by
  intro he
  have h := congrArg List.length he
  simp only [Keccak.length_bytesToBitsLE, nonceInput, List.length_append,
    List.length_cons, List.length_nil, hd] at h
  rw [FixedBytes.length_toList seed] at h
  cases s <;> revert h <;> decide

/-- FIPS 204 Algorithm 31 on a finite SHAKE256 output. The low nibble precedes the high nibble
of each byte. Exhaustion returns `none` when fewer than 256 coefficients were accepted. -/
def rejBoundedPoly (s : Level) (bytes : List Byte) : Option Poly :=
  asPoly (bytes.flatMap fun b =>
    ([b.val % 16, b.val / 16].filterMap (boundedCoeff s.params.η)))

private def Xofs.secretPoly (H : Xofs) (s : Level) (seed : List Byte) (nonce : ℕ) : Option Poly :=
  rejBoundedPoly s (H.h256.readBytes (nonceInput seed nonce) 481)

private theorem boundedCoeff_short {s : Level} {u : ℕ} {z : ZMod 8380417}
    (h : boundedCoeff s.params.η u = some z) : |z.valMinAbs| ≤ s.params.η := by
  have subShort (upper a : ℕ) (ha : a ≤ 2 * upper) (hu : upper ≤ 4) :
      |((upper : ZMod 8380417) - a).valMinAbs| ≤ upper := by
    rw [((ZMod.valMinAbs_spec _ ((upper : ℤ) - a)).2 ⟨by push_cast; rfl, by
      constructor <;> omega⟩)]
    exact abs_le.mpr ⟨by omega, by omega⟩
  have eta : s.params.η = 2 ∨ s.params.η = 4 := by cases s <;> decide
  rcases eta with he | he <;> rw [he] at h ⊢
  · simp only [boundedCoeff, ↓reduceIte] at h
    split_ifs at h
    cases h
    exact subShort 2 (u % 5) (by omega) (by decide)
  · simp only [boundedCoeff, ite_eq_right (by decide : ¬(4 : ℕ) = 2)] at h
    split_ifs at h
    cases h
    exact subShort 4 u (by omega) (by decide)

private theorem secretPoly_short {H : Xofs} {s : Level} {seed : List Byte} {nonce : ℕ} {v : Poly}
    (h : H.secretPoly s seed nonce = some v) (j : Fin 256) : |(v j).valMinAbs| ≤ s.params.η := by
  let bytes := H.h256.readBytes (nonceInput seed nonce) 481
  let entries := bytes.flatMap fun b =>
    [b.val % 16, b.val / 16].filterMap (boundedCoeff s.params.η)
  have short {z : ZMod 8380417} (hz : z ∈ entries) : |z.valMinAbs| ≤ s.params.η := by
    obtain ⟨_, _, hmem⟩ := List.mem_flatMap.mp hz
    obtain ⟨_, _, hval⟩ := List.mem_filterMap.mp hmem
    exact boundedCoeff_short hval
  change asPoly entries = some v at h
  dsimp only [asPoly] at h
  split_ifs at h with hlen
  cases h
  have hj : j.val < entries.toArray.size := by have := j.isLt; omega
  change |(entries.toArray[j.val]!).valMinAbs| ≤ _
  rw [getElem!_pos entries.toArray j.val hj]
  apply short
  exact List.getElem_mem _

private theorem lookup_of_tabulate {α : Type} {n : ℕ} {f : Fin n → Option α}
    {v : Fin n → α} (h : tabulate n f = some v) (i : Fin n) : f i = some (v i) := by
  have lookup {n : ℕ} (f : Fin n → Option α) (arr : Vector α n)
      (ha : Vector.ofFnM f = some arr) (i : Fin n) : f i = some (arr.get i) := by
    induction n with
    | zero => exact i.elim0
    | succ n ih =>
      rw [Vector.ofFnM_succ] at ha
      cases hpre : Vector.ofFnM (fun i => f i.castSucc) with
      | none => simp [hpre] at ha
      | some pref =>
        cases hlast : f (Fin.last n) with
        | none => simp [hpre, hlast] at ha
        | some last =>
          simp only [hpre, hlast, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at ha
          subst arr
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa only [Vector.get_push_last] using hlast
          · simpa only [Vector.get_push_castSucc] using
              ih _ pref hpre j
  cases hv : Vector.ofFnM f with
  | none => simp [tabulate, hv] at h
  | some arr =>
    have he : arr.get = v := by simpa [tabulate, hv] using h
    exact he ▸ lookup f arr hv i

/-- Public-key bytes of Algorithm 6, lines 6–8: concatenate the matrix seed and the ten
high bits of each coefficient of the full public vector, in row and coefficient order. -/
def encodePublic (s : Level) (rho : List Byte) (t : Fin s.params.k → Poly) : List Byte :=
  rho ++ packCoeffs 10 (fun i j => (power2Round 8380417 13 (t i j)).1.toNat)

/-- Algorithm 22 appends 320 bytes per rounded polynomial to the supplied matrix seed. -/
@[simp] theorem length_encodePublic (s : Level) (rho : List Byte) (t : Fin s.params.k → Poly) :
    (encodePublic s rho t).length = rho.length + 320 * s.params.k := by
  simp [encodePublic]

/-- The seed used to expand the matrix can be read from the published bytes. -/
@[simp] theorem take_encodePublic (s : Level) (rho : FixedBytes 32) (t : Fin s.params.k → Poly) :
    (encodePublic s rho.toList t).take 32 = rho.toList := by
  simp [encodePublic]

/-- Algorithm 6's two encoded output keys. -/
structure KeyPair where
  /-- The public key, including the matrix seed. -/
  publicKey : List Byte
  /-- The private key containing the signing seed, public-key hash and three short vectors. -/
  secretKey : List Byte

/-- Algorithms 17 and 24: pack signed coefficients as fixed-width offsets from their upper bound. -/
def packSigned {rows : ℕ} (width upper : ℕ) (v : Fin rows → Poly) : List Byte :=
  packCoeffs width fun i j => ((upper : ℤ) - (v i j).valMinAbs).toNat

/-- Algorithm 18 reads fixed-width signed offsets from the first field in a byte string.
Array slices keep each coefficient lookup linear in its own width. -/
def unpackSigned (rows width upper : ℕ) (bytes : List Byte) :
    Vector (Vector (ZMod 8380417) 256) rows :=
  let bits := (Keccak.bytesToBitsLE (bytes.take (32 * width * rows))).toArray
  Vector.ofFn fun i : Fin rows => Vector.ofFn fun j : Fin 256 =>
    let start := width * (256 * i.val + j.val)
    (upper : ZMod 8380417) - ↑(BitString.lsbValue (bits.extract start (start + width)).toList)

/-- The signed field round trip, even when other fields follow it in the input. -/
theorem unpackSigned_packSigned {rows width upper : ℕ} (v : Fin rows → Poly) (tail : List Byte)
    (hr : ∀ i j, let off := (upper : ℤ) - (v i j).valMinAbs
      0 ≤ off ∧ off < (2 ^ width : ℕ)) (i : Fin rows) (j : Fin 256) :
    ((unpackSigned rows width upper (packSigned width upper v ++ tail)).get i).get j = v i j := by
  have hu := unpack_packCoeffs (width := width) (fun i j => ((upper : ℤ) - (v i j).valMinAbs).toNat)
    (fun i j => by have := hr i j; omega) i j
  have hlen : (packSigned width upper v).length = 32 * width * rows := length_packCoeffs ..
  simp only [unpackSigned, Vector.get_ofFn, ← hlen, List.take_left, Array.toList_extract,
    List.toList_toArray, List.extract_eq_take_drop, Nat.add_sub_cancel_left]
  change (upper : ZMod 8380417) -
    ↑(unpackCoeff (Keccak.bytesToBitsLE (packSigned width upper v)) width (256 * i.val + j.val)) = _
  rw [packSigned, hu]
  have cast : (((upper : ℤ) - (v i j).valMinAbs).toNat : ZMod 8380417) =
      (upper : ZMod 8380417) - v i j := by
    calc
      _ = ((((upper : ℤ) - (v i j).valMinAbs).toNat : ℤ) : ZMod 8380417) := by push_cast; rfl
      _ = _ := by rw [Int.toNat_of_nonneg (hr i j).1]; push_cast; rfl
  rw [cast, sub_sub_cancel]

/-- The six fields of the FIPS 204 private-key encoding (Algorithms 24 and 25). -/
structure PrivateKey (s : Level) where
  /-- The seed for the public matrix. -/
  rho : List Byte
  /-- The secret signing seed. -/
  key : List Byte
  /-- The public-key hash. -/
  tr : List Byte
  /-- The short secret vector. -/
  s₁ : Fin s.params.ℓ → Poly
  /-- The short error vector. -/
  s₂ : Fin s.params.k → Poly
  /-- The low public vector from Power2Round. -/
  t₀ : Fin s.params.k → Poly

private def PrivateKey.encode {s : Level} (v : PrivateKey s) : List Byte :=
  let width := (2 * s.params.η).log2 + 1
  v.rho ++ (v.key ++ (v.tr ++ (packSigned width s.params.η v.s₁ ++
    (packSigned width s.params.η v.s₂ ++ packSigned 13 4096 v.t₀))))

private theorem PrivateKey.length_encode {s : Level} (w : PrivateKey s)
    (hr : w.rho.length = 32) (hk : w.key.length = 32) (ht : w.tr.length = 64) :
    w.encode.length = 128 +
      32 * ((2 * s.params.η).log2 + 1) * s.params.ℓ +
      32 * ((2 * s.params.η).log2 + 1) * s.params.k + 32 * 13 * s.params.k := by
  simp only [PrivateKey.encode, List.length_append, hr, hk, ht, packSigned, length_packCoeffs]
  lia

/-- Algorithm 25 decodes the stored private-key fields from their fixed-width encodings. -/
def decodePrivate (s : Level) (bytes : List Byte) : Option (PrivateKey s) := do
  let width := (2 * s.params.η).log2 + 1
  let len₁ := 32 * width * s.params.ℓ
  let len₂ := 32 * width * s.params.k
  guard (bytes.length = 128 + len₁ + len₂ + 32 * 13 * s.params.k)
  let key := bytes.drop 32
  let tr := key.drop 32
  let first := tr.drop 64
  let second := first.drop len₁
  let low := second.drop len₂
  return ⟨bytes.take 32, key.take 32, tr.take 64,
    ringVectorCoeffs (unpackSigned _ width s.params.η first),
    ringVectorCoeffs (unpackSigned _ width s.params.η second),
    ringVectorCoeffs (unpackSigned _ 13 4096 low)⟩

/-- Decoded seed, key and public-key hash lengths are bounded by their FIPS byte widths. -/
theorem lengths_of_decodePrivate {s : Level} {sk : PrivateKey s} {key : List Byte}
    (hd : decodePrivate s key = some sk) :
    sk.rho.length ≤ 32 ∧ sk.key.length ≤ 32 ∧ sk.tr.length ≤ 64 := by
  simp only [decodePrivate, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hd
  obtain ⟨_, _, rfl⟩ := hd
  simp

private theorem decodePrivate_encode {s : Level} (v : PrivateKey s) (hr : v.rho.length = 32)
    (hk : v.key.length = 32) (ht : v.tr.length = 64)
    (h₁ : ∀ i j, |(v.s₁ i j).valMinAbs| ≤ s.params.η)
    (h₂ : ∀ i j, |(v.s₂ i j).valMinAbs| ≤ s.params.η)
    (h₀ : ∀ i j, -4096 < (v.t₀ i j).valMinAbs ∧ (v.t₀ i j).valMinAbs ≤ 4096) :
    decodePrivate s v.encode = some v := by
  let w := (2 * s.params.η).log2 + 1
  have fieldLen {n} (width upper : ℕ) (f : Fin n → Poly) :
      (packSigned width upper f).length = 32 * width * n := length_packCoeffs ..
  have offBound {z : ZMod 8380417} (hz : |z.valMinAbs| ≤ s.params.η) :
      0 ≤ (s.params.η : ℤ) - z.valMinAbs ∧ (s.params.η : ℤ) - z.valMinAbs < (2 ^ w : ℕ) := by
    have small : 2 * s.params.η < 2 ^ w := by cases s <;> decide
    obtain ⟨_, _⟩ := abs_le.mp hz
    omega
  have first := List.drop_left' (l₂ := packSigned w s.params.η v.s₂ ++ packSigned 13 4096 v.t₀)
    (fieldLen w s.params.η v.s₁)
  have second := List.drop_left' (l₂ := packSigned 13 4096 v.t₀) (fieldLen w s.params.η v.s₂)
  unfold decodePrivate
  dsimp only
  rw [v.length_encode hr hk ht]
  dsimp only [w] at first second ⊢
  simp only [guard, ↓reduceIte, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some, PrivateKey.encode, List.take_left' hr, List.drop_left' hr, List.take_left' hk,
    List.drop_left' hk, List.take_left' ht, List.drop_left' ht, first, second, Option.some.injEq]
  obtain ⟨rho, key, tr, a, b, c⟩ := v
  congr 1
  · funext i j
    exact unpackSigned_packSigned _ _ (fun i j => offBound (h₁ i j)) i j
  · funext i j
    exact unpackSigned_packSigned _ _ (fun i j => offBound (h₂ i j)) i j
  · funext i j
    simpa only [List.append_nil, ringVectorCoeffs] using
      unpackSigned_packSigned (width := 13) (upper := 4096) c []
      (fun i j => by have := h₀ i j; norm_num at *; omega) i j

/-- Raw SHAKE256 input of FIPS 204 Algorithm 6, line 1. The 32-byte seed is followed by
the one-byte matrix dimensions in row then column order. -/
@[expose] def keySeedInput (s : Level) (seed : FixedBytes 32) : List Bool :=
  Keccak.bytesToBitsLE (seed.toList ++ [Fin.ofNat 256 s.params.k, Fin.ofNat 256 s.params.ℓ])

/-- The Algorithm 6 key expansion uses a 272-bit input at each standardized level. -/
theorem length_keySeedInput (s : Level) (seed : FixedBytes 32) :
    (keySeedInput s seed).length = 272 := by
  rw [keySeedInput, Keccak.length_bytesToBitsLE, List.length_append, FixedBytes.length_toList]
  rfl

/-- Algorithm 6 reads the public matrix seed, the short-vector seed and the signing key
in one 128-byte SHAKE256 expansion of the seed and the two dimension bytes. -/
@[expose] def Xofs.expandKeySeed (H : Xofs) (s : Level) (seed : FixedBytes 32) : List Byte :=
  H.h256.read (keySeedInput s seed) 128

/-- FIPS 204 Algorithm 33 samples both short vectors from SHAKE256. The nonces of the
error vector start immediately after the last nonce of the secret vector. -/
def Xofs.expandS (H : Xofs) (s : Level) (rho' : List Byte) :
    Option ((Fin s.params.ℓ → Poly) × (Fin s.params.k → Poly)) := do
  let s₁ ← tabulate _ fun i : Fin s.params.ℓ => H.secretPoly s rho' i.val
  let s₂ ← tabulate _ fun i : Fin s.params.k => H.secretPoly s rho' (s.params.ℓ + i.val)
  return (s₁, s₂)

/-- Algorithm 6, from the 32-byte seed to both encoded keys (Algorithms 22, 24).
Rejection exhaustion during the matrix or short-vector expansion yields an error. -/
def Xofs.keyGen (H : Xofs) (s : Level) (seed : FixedBytes 32) : Option KeyPair := do
  let expanded := H.expandKeySeed s seed
  let rho := expanded.take 32
  let rho' := (expanded.drop 32).take 64
  let matrix ← H.expandA s rho
  let (s₁, s₂) ← H.expandS s rho'
  let full := Vector.ofFn fun i => Vector.ofFn ((moduleSISMap matrix s₁ + s₂) i)
  let t := fun i => (full.get i).get
  let pk := encodePublic s rho t
  let sk : PrivateKey s := ⟨rho, expanded.drop 96, H.h256.readBytes pk 64, s₁, s₂,
    fun i j => ((power2Round 8380417 13 (t i j)).2 : ZMod 8380417)⟩
  return ⟨pk, sk.encode⟩

/-- Algorithm 6 gives the same keys or failure when the matrix stream, key expansion,
secret-vector nonce reads at the generated secret seed, and encoded-public-key hash reads agree. -/
theorem Xofs.keyGen_congr_of_reads {H G : Xofs} (s : Level) (seed : FixedBytes 32)
    (matrixStream : G.h128 = H.h128) (seedRead : G.expandKeySeed s seed = H.expandKeySeed s seed)
    (nonceRead : ∀ i : ℕ,
      let x := nonceInput (((H.expandKeySeed s seed).drop 32).take 64) i
      G.h256.readBytes x 481 = H.h256.readBytes x 481)
    (publicRead : ∀ x : List Byte, x.length = 32 + 320 * s.params.k →
      G.h256.readBytes x 64 = H.h256.readBytes x 64) : G.keyGen s seed = H.keyGen s seed := by
  let ex := H.expandKeySeed s seed
  have len : ex.length = 128 := H.h256.length_read ..
  have matrix := Xofs.expandA_congr matrixStream s (ex.take 32)
  have short (i : ℕ) : G.secretPoly s ((ex.drop 32).take 64) i =
      H.secretPoly s ((ex.drop 32).take 64) i := by
    unfold Xofs.secretPoly
    rw [nonceRead i]
  have pk (v : Fin s.params.k → Poly) :
      G.h256.readBytes (encodePublic s (ex.take 32) v) 64 =
        H.h256.readBytes (encodePublic s (ex.take 32) v) 64 := by
    apply publicRead
    simp only [length_encodePublic, List.length_take, len]
    rfl
  simp only [Xofs.keyGen, Xofs.expandS, seedRead, ← show ex = H.expandKeySeed s seed from rfl,
    matrix, short, pk]

/-- The seed recovered from a successful public key is precisely the prefix used to index
the SHAKE128 matrix streams during this execution of Algorithm 6. -/
theorem publicSeed_of_keyGen {H : Xofs} {s : Level} {seed : FixedBytes 32} {keys : KeyPair}
    (h : H.keyGen s seed = some keys) :
    keys.publicKey.take 32 = (H.expandKeySeed s seed).take 32 := by
  simp only [Xofs.keyGen, Xofs.expandS, Option.bind_eq_bind, Option.pure_def,
    Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨_, _, _, _, _, _, rfl⟩ := h
  have len : (H.expandKeySeed s seed).length = 128 := H.h256.length_read ..
  rw [encodePublic, List.take_left' (by simp [len])]

/-- Algorithm 6 is unchanged if SHAKE128 is unchanged and the two SHAKE256 streams agree
on all words outside the parameter set's digest-seed length. The key-seed input is 34 bytes,
secret nonce inputs are 66 bytes, and every encoded public key is longer than a digest. -/
theorem Xofs.keyGen_congr_off_digest {H K : Xofs} (s : Level) (seed : FixedBytes 32)
    (ha : K.h128 = H.h128)
    (agree : ∀ (x : List Bool), x.length ≠ 8 * digestBytes s →
      ∀ n, K.h256.read x n = H.h256.read x n) :
    K.keyGen s seed = H.keyGen s seed := by
  have raw (x : List Byte) (hx : x.length ≠ digestBytes s) (n : ℕ) :
      K.h256.readBytes x n = H.h256.readBytes x n := by
    apply agree
    rw [Keccak.length_bytesToBitsLE]
    omega
  apply Xofs.keyGen_congr_of_reads s seed ha
  · apply raw
    simp only [List.length_append, FixedBytes.length_toList, List.length_cons, List.length_nil]
    cases s <;> decide
  · intro nonce
    apply raw
    simp only [nonceInput, List.length_append, List.length_take, List.length_drop,
      Xofs.expandKeySeed, H.h256.length_read, List.length_cons, List.length_nil]
    cases s <;> decide
  · intro x hx
    apply raw
    rw [hx]
    cases s <;> decide

/-- FIPS 202 specialization of `Xofs.keyGen`. -/
abbrev keyGen := Xofs.keyGen Xofs.shake

/-- A generated private key decodes to the same matrix seed, last 32 key-expansion bytes,
short vectors, public-key hash and rounded low part used by Algorithm 6. -/
theorem privateKey_of_keyGen {H : Xofs} {s : Level} {seed : FixedBytes 32} {keys : KeyPair}
    (hg : H.keyGen s seed = some keys) :
    ∃ (rho : FixedBytes 32) (sk : MLDSA.SecretKey s.params),
      H.expandA s rho.toList = some sk.A ∧
      keys.publicKey = encodePublic s rho.toList sk.publicKey.t ∧
      decodePrivate s keys.secretKey = some ⟨rho.toList, (H.expandKeySeed s seed).drop 96,
        H.h256.readBytes keys.publicKey 64,
        sk.s₁, sk.s₂, publicKeyLowPart s.params 13 sk.publicKey⟩ ∧
      (∀ i j, |(sk.s₁ i j).valMinAbs| ≤ s.params.η) ∧
      (∀ i j, |(sk.s₂ i j).valMinAbs| ≤ s.params.η) ∧
      H.expandS s (((H.expandKeySeed s seed).drop 32).take 64) = some (sk.s₁, sk.s₂) := by
  unfold Xofs.keyGen Xofs.expandS Xofs.expandKeySeed at hg
  generalize hh : H.h256.read (keySeedInput s seed) 128 = expanded at hg
  have hex : expanded.length = 128 := by rw [← hh]; exact H.h256.length_read ..
  have hr : (expanded.take 32).length = 32 := by simp [hex]
  obtain ⟨rho, hrho⟩ := FixedBytes.exists_toList hr
  cases ha : H.expandA s (expanded.take 32) with
  | none => simp [ha] at hg
  | some A =>
    cases h₁ : tabulate s.params.ℓ (fun i => H.secretPoly s ((expanded.drop 32).take 64) i.val) with
    | none => simp [ha, h₁] at hg
    | some a =>
      cases h₂ : tabulate s.params.k (fun i =>
          H.secretPoly s ((expanded.drop 32).take 64) (s.params.ℓ + i.val)) with
      | none => simp [ha, h₁, h₂] at hg
      | some b =>
        let sk : MLDSA.SecretKey s.params := ⟨A, a, b⟩
        have sa (i j) := secretPoly_short (lookup_of_tabulate h₁ i) j
        have sb (i j) := secretPoly_short (lookup_of_tabulate h₂ i) j
        have ht : moduleSISMap A a + b = sk.publicKey.t := (SecretKey.publicKey_t s.params sk).symm
        have low (i j) : -4096 < (publicKeyLowPart s.params 13 sk.publicKey i j).valMinAbs ∧
            (publicKeyLowPart s.params 13 sk.publicKey i j).valMinAbs ≤ 4096 := by
          let t := (power2Round 8380417 13 (sk.publicKey.t i j)).2
          have hb : -4096 < t ∧ t ≤ 4096 := power2Round_low_mem_Ioc (by decide : 0 < 13) _
          change -4096 < (t : ZMod 8380417).valMinAbs ∧ (t : ZMod 8380417).valMinAbs ≤ 4096
          rw [(ZMod.valMinAbs_spec _ t).2 ⟨rfl, by constructor <;> omega⟩]
          exact hb
        have materialized {n : ℕ} {α : Type} (f : Fin n → α) : (Vector.ofFn f).get = f :=
          funext (Vector.get_ofFn f)
        simp only [ha, h₁, h₂, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          materialized, Option.some.injEq, ht] at hg
        subst keys
        refine ⟨rho, sk, hrho ▸ ha, ?_, ?_, sa, sb, ?_⟩
        · rw [hrho]
        · rw [hrho]
          simp only [Xofs.expandKeySeed, hh]
          apply decodePrivate_encode
          · exact hr
          · simp [hex]
          · exact H.h256.length_read ..
          · exact sa
          · exact sb
          · exact low
        · rw [show H.expandKeySeed s seed = expanded from hh]
          simp only [Xofs.expandS, h₁, h₂, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
          rfl

/-- The encoded public key from Algorithm 6. -/
def keyGenPublic (s : Level) (seed : FixedBytes 32) : Option (List Byte) :=
  KeyPair.publicKey <$> keyGen s seed

namespace ChallengeRow

-- Retaining each rejected byte and the unconsumed suffix also permits programming the raw row.
private inductive Trace : ℕ → ℕ → Type where
  | done {i : ℕ} (tail : List Byte) : Trace i 0
  | reject {i n : ℕ} (b : Byte) (h : i < b.val) (rest : Trace i (n + 1)) : Trace i (n + 1)
  | accept {i n : ℕ} (b : Byte) (h : b.val ≤ i) (rest : Trace (i + 1) n) : Trace i (n + 1)

private def Trace.perm {i n : ℕ} : Trace i n → Equiv.Perm Byte
  | .done _ => Equiv.refl _
  | .reject _ _ t => t.perm
  | .accept (i := j) b _ t => (Equiv.swap (Fin.ofNat 256 j) b).trans t.perm

private def parse (i n : ℕ) (bytes : List Byte) : Option (Trace i n) :=
  match n, bytes with
  | 0, tail => some (.done tail)
  | _ + 1, [] => none
  | k + 1, b :: rest =>
    if h : i < b.val then (parse i (k + 1) rest).map (.reject b h)
    else (parse (i + 1) k rest).map (.accept b (Nat.le_of_not_gt h))
termination_by bytes.length

end ChallengeRow

private def signedTail (s : Level) (signs : List Bool) (i : Fin 256) : ZMod 8380417 :=
  if i.val < 256 - s.params.τ then 0
  else if signs[i.val - (256 - s.params.τ)]! then -1 else 1

/-- Algorithm 29. Preload the last τ positions with the SHAKE sign bits and exchange each
with its chosen position in increasing order. Future sign positions remain untouched because an
accepted index is at most the current position. The caller supplies the SHAKE256 bytes. The FIPS
wrapper below chooses the minimum permitted 221-byte bound from Appendix C, Table 3. -/
def sampleInBallBytes (s : Level) (bytes : List Byte) : Option Poly := do
  let t ← ChallengeRow.parse (256 - s.params.τ) s.params.τ (bytes.drop 8)
  return signedTail s (Keccak.bytesToBitsLE (bytes.take 8)) ∘ t.perm.symm

/-- Bounded Algorithm 29 reads 221 bytes at the challenge digest. This implementation chooses
the minimum cap permitted by FIPS 204, Appendix C, Table 3. -/
@[expose] def Xofs.sampleInBall (H : Xofs) (s : Level) (digest : List Byte) : Option Poly :=
  sampleInBallBytes s (H.h256.readBytes digest 221)

/-- FIPS 202 specialization of `Xofs.sampleInBall`. -/
abbrev sampleInBall := Xofs.sampleInBall Xofs.shake

private theorem inBall_signedTail (s : Level) (signs : List Bool) (e : Equiv.Perm (Fin 256)) :
    InBall s.params.τ (signedTail s signs ∘ e.symm) := by
  constructor
  · intro i
    by_cases hi : (e.symm i).val < 256 - s.params.τ
    · simp [Function.comp_apply, signedTail, hi]
    · by_cases hsign : signs[(e.symm i).val - (256 - s.params.τ)]! = true
      · simp only [Function.comp_apply, signedTail, hi, hsign, ↓reduceIte]
        decide
      · simp only [Function.comp_apply, signedTail, hi, hsign, ↓reduceIte]
        decide
  · let start : Fin 256 := ⟨256 - s.params.τ, by cases s <;> decide⟩
    have hs : (Finset.univ.filter fun i => (signedTail s signs ∘ e.symm) i ≠ 0) =
        (Finset.Ici start).map e.toEmbedding := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
        signedTail, Finset.mem_map_equiv, Finset.mem_Ici]
      by_cases hi : (e.symm i).val < 256 - s.params.τ
      · simp [hi, start, Fin.le_def, Nat.not_le_of_gt hi]
      · simp only [hi, ↓reduceIte, start, Fin.le_def, Nat.le_of_not_gt hi]
        by_cases hsign : signs[(e.symm i).val - (256 - s.params.τ)]! = true <;>
          simp only [hsign, ↓reduceIte, iff_true] <;> decide
    rw [hs, Finset.card_map, Fin.card_Ici]
    cases s <;> rfl

/-- Every successful Algorithm 29 byte row yields a signed challenge of weight τ. -/
theorem inBall_of_sampleInBallBytes {s : Level} {bytes : List Byte} {c : Poly}
    (h : sampleInBallBytes s bytes = some c) : InBall s.params.τ c := by
  cases ht : ChallengeRow.parse (256 - s.params.τ) s.params.τ (bytes.drop 8) with
  | none => simp [sampleInBallBytes, ht] at h
  | some t =>
    rw [sampleInBallBytes, ht] at h
    exact (Option.some.inj h) ▸ inBall_signedTail s _ t.perm

/-- Every successful FIPS expansion gives exactly τ signed unit coefficients. -/
theorem inBall_of_sampleInBall {H : Xofs} {s : Level} {digest : List Byte} {c : Poly}
    (h : H.sampleInBall s digest = some c) : InBall s.params.τ c :=
  inBall_of_sampleInBallBytes h

/-- The components of a FIPS 204 signature after Algorithm 27 has checked its encoding. -/
structure Signature (s : Level) where
  /-- The complete λ/4-byte commitment hash. -/
  digest : List Byte
  /-- The response polynomials decoded from their signed range. -/
  z : Fin s.params.ℓ → Poly
  /-- The decoded hint bits. -/
  h : Fin s.params.k → Fin 256 → Bool

private def hintEnd (ω : ℕ) (bytes : List Byte) : ℕ → ℕ
  | 0 => 0
  | i + 1 => ((bytes.drop ω)[i]?.getD 0).val

private def hintRow (ω : ℕ) (bytes : List Byte) (i : ℕ) : List Byte :=
  (bytes.drop (hintEnd ω bytes i)).take (hintEnd ω bytes (i + 1) - hintEnd ω bytes i)

private def unpackHint (s : Level) (bytes : List Byte) :
    Option (Fin s.params.k → Fin 256 → Bool) :=
  let endAt := hintEnd (hintLimit s) bytes
  let row := hintRow (hintLimit s) bytes
  if ((List.range s.params.k).all fun i =>
      decide (endAt i ≤ endAt (i + 1) ∧ endAt (i + 1) ≤ hintLimit s ∧ (row i).Pairwise (· < ·))) &&
      ((bytes.take (hintLimit s)).drop (endAt s.params.k)).all (· == 0) then
    some fun i j => (row i.val).contains j
  else none

private def hintRows {s : Level} (h : Fin s.params.k → Fin 256 → Bool) : List (List Byte) :=
  List.ofFn fun i => (List.finRange 256).filter (h i)

private theorem hintRows_weight {s : Level} (h : Fin s.params.k → Fin 256 → Bool) :
    (hintRows h).flatten.length = hintWeight s.params h := by
  simp only [hintRows, List.length_flatten, List.map_ofFn, Function.comp_def,
    ← List.countP_eq_length_filter, ← Fin.countP_eq_countP_map_finRange, List.sum_ofFn, hintWeight]

private def encodeHint {s : Level} (h : Fin s.params.k → Fin 256 → Bool) : List Byte :=
  let rows := hintRows h
  let ends := List.ofFn fun i : Fin s.params.k =>
    Fin.ofNat 256 (rows.take (i.val + 1)).flatten.length
  rows.flatten ++ List.replicate (hintLimit s - rows.flatten.length) 0 ++ ends

private theorem length_encodeHint {s : Level} (h : Fin s.params.k → Fin 256 → Bool)
    (hw : hintWeight s.params h ≤ hintLimit s) :
    (encodeHint h).length = hintLimit s + s.params.k := by
  simp only [encodeHint, List.length_append, List.length_replicate, List.length_ofFn,
    hintRows_weight]
  omega

private theorem unpackHint_encodeHint {s : Level} (h : Fin s.params.k → Fin 256 → Bool)
    (hw : hintWeight s.params h ≤ hintLimit s) : unpackHint s (encodeHint h) = some h := by
  let ω := hintLimit s
  let k := s.params.k
  let rows := hintRows h
  let stop (i : ℕ) := (rows.take i).flatten.length
  let ends := List.ofFn fun i : Fin k => Fin.ofNat 256 (stop (i.val + 1))
  let pad := List.replicate (ω - rows.flatten.length) (0 : Byte)
  have lk : rows.length = k := List.length_ofFn ..
  have weight : rows.flatten.length ≤ ω := (hintRows_weight h) ▸ hw
  have bound (i : ℕ) : stop i ≤ ω := by
    refine le_trans ?_ weight
    exact (List.take_sublist i rows).flatten.length_le
  have small : ω < 256 := by cases s <;> decide
  have used : (rows.flatten ++ pad).length = ω := by
    simp only [List.length_append, pad, List.length_replicate]
    omega
  have packed : encodeHint h = (rows.flatten ++ pad) ++ ends := rfl
  have stopEq (i : ℕ) (hi : i ≤ k) : hintEnd ω (encodeHint h) i = stop i := by
    cases i with
    | zero => rfl
    | succ i =>
      have hlen : i < ends.length := by simpa [ends] using hi
      simp only [hintEnd, packed, List.drop_left' used, List.getElem?_eq_getElem hlen,
        Option.getD_some,
        ends, List.getElem_ofFn, Fin.val_ofNat, Nat.mod_eq_of_lt (lt_of_le_of_lt (bound _) small)]
  have rowEq (i : ℕ) (hi : i < k) : hintRow ω (encodeHint h) i = rows[i]'(lk ▸ hi) := by
    have hir : i < rows.length := lk ▸ hi
    have diff : stop (i + 1) - stop i = rows[i].length := by
      simp only [stop, List.length_flatten_take_succ rows hir, Nat.add_sub_cancel_left]
    have usedRow := List.drop_flatten_take rows hir
    rw [hintRow, stopEq i (by omega), stopEq (i + 1) hi, diff, packed, List.append_assoc,
      List.drop_append_of_le_length (List.take_sublist i rows).flatten.length_le]
    rw [usedRow, List.append_assoc, List.take_left]
  have rowBits (i : Fin k) : rows[i.val]'(by rw [lk]; exact i.isLt) =
      (List.finRange 256).filter (h i) := by
    simp [rows, hintRows]
  have valid : ∀ i < k, hintEnd ω (encodeHint h) i ≤ hintEnd ω (encodeHint h) (i + 1) ∧
      hintEnd ω (encodeHint h) (i + 1) ≤ ω ∧ (hintRow ω (encodeHint h) i).Pairwise (· < ·) := by
    intro i hi
    rw [stopEq i (by omega), stopEq (i + 1) hi, rowEq i hi, rowBits ⟨i, hi⟩]
    refine ⟨?_, bound _, (List.pairwise_lt_finRange 256).filter _⟩
    simpa only [stop, List.length_flatten_take_succ rows (lk ▸ hi)] using
      Nat.le_add_right (stop i) (rows[i]'(lk ▸ hi)).length
  have padding : ((encodeHint h).take ω).drop (hintEnd ω (encodeHint h) k) = pad := by
    rw [stopEq k le_rfl, packed, List.take_left' used]
    change (rows.flatten ++ pad).drop (rows.take k).flatten.length = pad
    rw [← lk, List.take_length, List.drop_left]
  unfold unpackHint
  dsimp only
  rw [show ((List.range k).all _) = true by
    simpa only [List.all_eq_true, List.mem_range, decide_eq_true_eq] using valid]
  rw [padding]
  have zeros : pad.all (· == 0) = true := by simp [pad]
  rw [zeros]
  simp only [Bool.and_self, ↓reduceIte, Option.some.injEq]
  funext i j
  rw [rowEq i i.isLt, rowBits i]
  simp

private theorem unpackHint_inj {s : Level} {a b : List Byte} {h : Fin s.params.k → Fin 256 → Bool}
    (la : a.length = hintLimit s + s.params.k) (lb : b.length = a.length)
    (ha : unpackHint s a = some h) (hb : unpackHint s b = some h) : a = b := by
  let ω := hintLimit s
  let k := s.params.k
  have parsed {x : List Byte} (hx : unpackHint s x = some h) :
      (∀ i < k, hintEnd ω x i ≤ hintEnd ω x (i + 1) ∧ hintEnd ω x (i + 1) ≤ ω ∧
        (hintRow ω x i).Pairwise (· < ·)) ∧
      (∀ u ∈ (x.take ω).drop (hintEnd ω x k), u = 0) ∧
      (∀ (i : Fin k) j, ((hintRow ω x i).contains j) = h i j) := by
    dsimp only [unpackHint] at hx
    split_ifs at hx with ok
    · simp only [Bool.decide_and, Fin.isValue, Bool.and_eq_true, List.all_eq_true, List.mem_range,
        decide_eq_true_eq, beq_iff_eq] at ok
      exact ⟨ok.1, ok.2, fun i j => congrFun (congrFun (Option.some.inj hx) i) j⟩
  obtain ⟨va, pa, da⟩ := parsed ha
  obtain ⟨vb, pb, db⟩ := parsed hb
  have rowEq (i : ℕ) (hi : i < k) : hintRow ω a i = hintRow ω b i := by
    apply (va i hi).2.2.eq_of_mem_iff (vb i hi).2.2
    intro u
    exact (by simpa using congrArg (· = true) ((da ⟨i, hi⟩ u).trans (db ⟨i, hi⟩ u).symm))
  have pref (n : ℕ) (hn : n ≤ k) : hintEnd ω a n = hintEnd ω b n ∧
      a.take (hintEnd ω a n) = b.take (hintEnd ω b n) := by
    induction n with
    | zero => exact ⟨rfl, by simp [hintEnd]⟩
    | succ i ih =>
      have hi : i < k := hn
      obtain ⟨prev, before⟩ := ih (by omega)
      obtain ⟨am, aw, _⟩ := va i hi
      obtain ⟨bm, bw, _⟩ := vb i hi
      have rowLen (x : List Byte) (hx : ω ≤ x.length) (he : hintEnd ω x (i + 1) ≤ ω) :
          (hintRow ω x i).length = hintEnd ω x (i + 1) - hintEnd ω x i := by
        simp only [hintRow, List.length_take, List.length_drop]
        exact Nat.min_eq_left (by omega)
      have rows := rowEq i hi
      have lens := congrArg List.length rows
      rw [rowLen a (by dsimp [ω]; omega) aw, rowLen b (by dsimp [ω]; omega) bw] at lens
      refine ⟨by omega, ?_⟩
      have recov (x : List Byte) (hm : hintEnd ω x i ≤ hintEnd ω x (i + 1)) :
          x.take (hintEnd ω x (i + 1)) = x.take (hintEnd ω x i) ++ hintRow ω x i := by
        rw [hintRow, ← List.take_add]
        congr 1
        omega
      rw [recov a am, recov b bm, before, rows]
  obtain ⟨lastEq, used⟩ := pref k le_rfl
  have left : a.take ω = b.take ω := by
    have leω : hintEnd ω a k ≤ ω := by
      cases hk : k with
      | zero => simp [hintEnd]
      | succ i => exact (va i (by omega)).2.1
    have pads : (a.take ω).drop (hintEnd ω a k) = (b.take ω).drop (hintEnd ω b k) := by
      rw [List.eq_replicate_of_mem pa, List.eq_replicate_of_mem pb]
      simp [lb, lastEq]
    rw [← List.take_append_drop (hintEnd ω a k) (a.take ω),
      ← List.take_append_drop (hintEnd ω b k) (b.take ω)]
    simpa only [List.take_take, Nat.min_eq_left leω, Nat.min_eq_left (lastEq ▸ leω)] using
      congrArg₂ (· ++ ·) used pads
  have ends : a.drop ω = b.drop ω := by
    apply List.ext_getElem (by simp [lb])
    intro i hi hj
    have hik : i < k := by simpa [la, ω, k] using hi
    have eqEnd := (pref (i + 1) hik).1
    simpa [hintEnd, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Fin.ext_iff]
      using eqEnd
  exact (List.take_append_drop ω a).symm.trans <| (congrArg₂ (· ++ ·) left ends).trans
    (List.take_append_drop ω b)

private theorem responseBytes_inj {s : Level} {x y : List Byte}
    (w : ℕ) (hw : w = s.params.γ₁.log2 + 1)
    (hx : 32 * w * s.params.ℓ ≤ x.length) (hy : 32 * w * s.params.ℓ ≤ y.length)
    (he : ∀ (i : Fin s.params.ℓ) (j : Fin 256),
      ((unpackCoeff (Keccak.bytesToBitsLE x) w (256 * i.val + j.val) : ℕ) : ZMod 8380417) =
        ↑(unpackCoeff (Keccak.bytesToBitsLE y) w (256 * i.val + j.val))) :
    x.take (32 * w * s.params.ℓ) = y.take (32 * w * s.params.ℓ) := by
  let n := 256 * s.params.ℓ
  have cover (l : List Byte) (hl : 32 * w * s.params.ℓ ≤ l.length) :
      w * n ≤ (Keccak.bytesToBitsLE l).length := by
    rw [Keccak.length_bytesToBitsLE]
    convert Nat.mul_le_mul_left 8 hl using 1
    dsimp [n]
    ring
  have eqBlock (u : ℕ) (hu : u < n) :
      ((Keccak.bytesToBitsLE x).drop (w * u)).take w =
        ((Keccak.bytesToBitsLE y).drop (w * u)).take w := by
    let i : Fin s.params.ℓ := ⟨u / 256, by change u < 256 * s.params.ℓ at hu; omega⟩
    let j : Fin 256 := ⟨u % 256, by omega⟩
    have index : 256 * i.val + j.val = u := by dsimp [i, j]; omega
    have len (l : List Byte) (hl : 32 * w * s.params.ℓ ≤ l.length) :
        (((Keccak.bytesToBitsLE l).drop (w * u)).take w).length = w := by
      have hn := cover l hl
      have hm := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hu)
      rw [Nat.mul_succ] at hm
      simp only [List.length_take, List.length_drop]
      exact Nat.min_eq_left (by omega)
    have bound (l : List Byte) (hl : 32 * w * s.params.ℓ ≤ l.length) :
        unpackCoeff (Keccak.bytesToBitsLE l) w u < 8380417 := by
      have small : 2 ^ w ≤ 8380417 := by rw [hw]; cases s <;> decide
      apply Nat.lt_of_lt_of_le _ small
      simpa only [unpackCoeff, len l hl] using
        BitString.lsbValue_lt (((Keccak.bytesToBitsLE l).drop (w * u)).take w)
    have valEq := congrArg ZMod.val (he i j)
    simp only [index, ZMod.val_natCast, Nat.mod_eq_of_lt (bound x hx),
      Nat.mod_eq_of_lt (bound y hy)] at valEq
    exact BitString.lsbValue_injective ((len x hx).trans (len y hy).symm) valEq
  have words (n' : ℕ) (hn' : n' ≤ n) :
      (Keccak.bytesToBitsLE x).take (w * n') = (Keccak.bytesToBitsLE y).take (w * n') := by
    induction n' with
    | zero => simp
    | succ u ih =>
      rw [Nat.mul_succ, List.take_add, List.take_add, ih (by omega), eqBlock u hn']
  apply Keccak.bytesToBitsLE_injective
  rw [Keccak.bytesToBitsLE_take, Keccak.bytesToBitsLE_take]
  convert words n le_rfl using 2 <;> dsimp [n] <;> ring

/-- Algorithm 27, including the prescribed total length, increasing hint indices within each
row, monotone row ends, the hint-weight bound, and zero padding (Algorithm 21). -/
def sigDecode (s : Level) (bytes : List Byte) : Option (Signature s) := do
  let width := s.params.γ₁.log2 + 1
  let hintOffset := digestBytes s + 32 * width * s.params.ℓ
  guard (bytes.length == hintOffset + hintLimit s + s.params.k)
  let hints ← unpackHint s (bytes.drop hintOffset)
  let bits := Keccak.bytesToBitsLE (bytes.drop (digestBytes s))
  let response := Vector.ofFn fun i : Fin s.params.ℓ => Vector.ofFn fun j : Fin 256 =>
    (s.params.γ₁ : ZMod 8380417) - ↑(unpackCoeff bits width (256 * i.val + j.val))
  return ⟨bytes.take (digestBytes s), fun i j => response[i.val][j.val], hints⟩

private theorem sigDecode_parts {s : Level} {x : List Byte} {σ : Signature s}
    (hx : sigDecode s x = some σ) :
    let d := digestBytes s
    let w := s.params.γ₁.log2 + 1
    let r := 32 * w * s.params.ℓ
    let t := d + r
    x.length = t + hintLimit s + s.params.k ∧
      x.take d = σ.digest ∧ unpackHint s (x.drop t) = some σ.h ∧
      ∀ (i : Fin s.params.ℓ) (j : Fin 256),
        (s.params.γ₁ : ZMod 8380417) -
          ↑(unpackCoeff (Keccak.bytesToBitsLE (x.drop d)) w (256 * i.val + j.val)) = σ.z i j := by
  intro d w r t
  have hl : x.length = t + hintLimit s + s.params.k := by
    by_contra hn
    simp [sigDecode, guard, show x.length ≠ _ from hn, t, d, r, w] at hx
  dsimp only [t, d, r, w] at hl
  cases hh : unpackHint s (x.drop t) with
  | none =>
    dsimp only [t, d, r, w] at hh
    simp [sigDecode, guard, hl, hh] at hx
  | some h =>
    dsimp only [t, d, r, w] at hh
    simp only [sigDecode, guard, hl, BEq.rfl, ↓reduceIte, Option.pure_def, hh, Vector.getElem_ofFn,
      Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hx
    subst σ
    exact ⟨hl, rfl, rfl, fun i j => by simp [d, w]⟩

/-- The commitment digest occupies the first bytes of a successfully decoded signature. -/
theorem digest_of_sigDecode {s : Level} {x : List Byte} {σ : Signature s}
    (hx : sigDecode s x = some σ) : x.take (digestBytes s) = σ.digest :=
  (sigDecode_parts hx).2.1

/-- FIPS 204 Algorithms 21 and 27 give each successfully decoded signature exactly one byte
representation. The hint rows determine their cumulative ends and their zero padding. -/
theorem eq_of_sigDecode {s : Level} {a b : List Byte} {σ : Signature s}
    (ha : sigDecode s a = some σ) (hb : sigDecode s b = some σ) : a = b := by
  let d := digestBytes s
  let w := s.params.γ₁.log2 + 1
  let r := 32 * w * s.params.ℓ
  let t := d + r
  obtain ⟨la, da, ha', za⟩ := sigDecode_parts ha
  obtain ⟨lb, db, hb', zb⟩ := sigDecode_parts hb
  change a.length = t + hintLimit s + s.params.k at la
  change b.length = t + hintLimit s + s.params.k at lb
  have hints := unpackHint_inj (a := a.drop t) (b := b.drop t)
    (by rw [List.length_drop, la]; omega) (by simp [la, lb]) ha' hb'
  have resp := responseBytes_inj (x := a.drop d) (y := b.drop d) w rfl
    (by rw [List.length_drop, la]; change r ≤ d + r + _ + _ - d; omega)
    (by rw [List.length_drop, lb]; change r ≤ d + r + _ + _ - d; omega)
    (fun i j => sub_right_inj.mp ((za i j).trans (zb i j).symm))
  have hdr : a.take t = b.take t := by
    rw [show t = d + r from rfl, List.take_add, List.take_add, da.trans db.symm, resp]
  exact (List.take_append_drop t a).symm.trans <| (congrArg₂ (· ++ ·) hdr hints).trans
    (List.take_append_drop t b)

/-- Consecutive little-endian bytes in a commitment digest register. -/
def registerBytes (s : Level) (d : BitString (8 * digestBytes s)) : List Byte :=
  ((Keccak.fixedBytesEquivBitsLE (digestBytes s)).symm d).toList

/-- A coherent commitment digest register supplies exactly the required number of bytes. -/
@[simp] theorem length_registerBytes (s : Level) (d : BitString (8 * digestBytes s)) :
    (registerBytes s d).length = digestBytes s := by
  simp [registerBytes]

/-- A literal digest of the prescribed length round-trips through the XOR register. -/
theorem registerBytes_ofList (s : Level) (bytes : List Byte) (h : bytes.length = digestBytes s) :
    registerBytes s (BitString.ofList (8 * digestBytes s) (Keccak.bytesToBitsLE bytes)) =
      bytes := by
  obtain ⟨v, rfl⟩ := FixedBytes.exists_toList h
  have hbits : BitString.ofList (8 * digestBytes s) (Keccak.bytesToBitsLE v.toList) =
      Keccak.fixedBytesEquivBitsLE (digestBytes s) v := by
    rw [← Keccak.ofFn_fixedBytesEquivBitsLE, BitString.ofList_ofFn]
  simp [registerBytes, hbits]

/-- Algorithm 26 serializes the commitment digest, signed response and sparse hint. -/
def encodeSignature (s : Level) (σ : Signature s) : List Byte :=
  σ.digest ++ packSigned (s.params.γ₁.log2 + 1) s.params.γ₁ σ.z ++ encodeHint σ.h

/-- Length in bytes of an encoded signature (FIPS 204, Table 2). -/
def signatureBytes (s : Level) : ℕ :=
  digestBytes s + 32 * (s.params.γ₁.log2 + 1) * s.params.ℓ + hintLimit s + s.params.k

/-- Encoding a signature satisfying the hint and digest bounds has its prescribed length. -/
theorem length_encodeSignature (s : Level) (σ : Signature s)
    (hd : σ.digest.length = digestBytes s) (hh : hintWeight s.params σ.h ≤ hintLimit s) :
    (encodeSignature s σ).length = signatureBytes s := by
  simp [encodeSignature, signatureBytes, packSigned, hd, length_encodeHint σ.h hh, Nat.add_assoc]

/-- Algorithms 26 and 27 round-trip every signature with the prescribed digest length,
an accepted response norm, and at most `ω` hint bits. -/
theorem sigDecode_encodeSignature (s : Level) (σ : Signature s)
    (hd : σ.digest.length = digestBytes s) (hz : ResponseShort s.params σ.z)
    (hh : hintWeight s.params σ.h ≤ hintLimit s) :
    sigDecode s (encodeSignature s σ) = some σ := by
  let w := s.params.γ₁.log2 + 1
  let resp := packSigned w s.params.γ₁ σ.z
  let hints := encodeHint σ.h
  have plen : resp.length = 32 * w * s.params.ℓ := length_packCoeffs ..
  have tlen : (σ.digest ++ resp).length = digestBytes s + 32 * w * s.params.ℓ := by
    rw [List.length_append, hd, plen]
  have len := length_encodeSignature s σ hd hh
  change _ = digestBytes s + 32 * w * s.params.ℓ + hintLimit s + s.params.k at len
  have hdr : (encodeSignature s σ).take (digestBytes s) = σ.digest := by
    change ((σ.digest ++ resp) ++ hints).take _ = _
    rw [List.append_assoc, ← hd, List.take_left]
  have fields : (encodeSignature s σ).drop (digestBytes s) = resp ++ hints := by
    change ((σ.digest ++ resp) ++ hints).drop _ = _
    rw [List.append_assoc, ← hd, List.drop_left]
  have tail : (encodeSignature s σ).drop (digestBytes s + 32 * w * s.params.ℓ) = hints := by
    change ((σ.digest ++ resp) ++ hints).drop _ = _
    rw [← tlen, List.drop_left]
  have two : 2 ^ w = 2 * s.params.γ₁ := by cases s <;> decide
  have bounds (i j) : 0 ≤ (s.params.γ₁ : ℤ) - (σ.z i j).valMinAbs ∧
      (s.params.γ₁ : ℤ) - (σ.z i j).valMinAbs < (2 ^ w : ℕ) := by
    obtain ⟨lo, hi⟩ := abs_lt.mp (hz i j)
    rw [two]
    lia
  have coeff (i : Fin s.params.ℓ) (j : Fin 256) :
      (s.params.γ₁ : ZMod 8380417) -
        ↑(unpackCoeff (Keccak.bytesToBitsLE (resp ++ hints)) w (256 * i.val + j.val)) =
        σ.z i j := by
    have decoded := unpackSigned_packSigned (width := w) (upper := s.params.γ₁)
      σ.z hints bounds i j
    have raw : (s.params.γ₁ : ZMod 8380417) -
        ↑(unpackCoeff (Keccak.bytesToBitsLE resp) w (256 * i.val + j.val)) = σ.z i j := by
      simpa only [unpackSigned, Vector.get_ofFn, ← plen, List.take_left,
        Array.toList_extract, List.toList_toArray, List.extract_eq_take_drop,
        Nat.add_sub_cancel_left, resp, unpackCoeff] using decoded
    have idx : 256 * i.val + j.val + 1 ≤ 256 * s.params.ℓ := by
      have := i.isLt
      have := j.isLt
      lia
    have room : w * (256 * i.val + j.val) + w ≤ (Keccak.bytesToBitsLE resp).length := by
      rw [Keccak.length_bytesToBitsLE, plen, ← Nat.mul_succ]
      calc w * (256 * i.val + j.val).succ ≤ w * (256 * s.params.ℓ) := Nat.mul_le_mul_left w idx
        _ = 8 * (32 * w * s.params.ℓ) := by ring
    have bits : Keccak.bytesToBitsLE (resp ++ hints) =
        Keccak.bytesToBitsLE resp ++ Keccak.bytesToBitsLE hints := List.flatMap_append ..
    rw [bits, unpackCoeff, List.drop_append_of_le_length (by lia : w * (256 * i.val + j.val) ≤ _),
      List.take_append_of_le_length (by rw [List.length_drop]; lia)]
    exact raw
  dsimp only [w] at len tail coeff
  simp only [sigDecode, len, BEq.rfl, guard, ↓reduceIte, Option.pure_def,
    tail, hints, unpackHint_encodeHint σ.h hh, Option.bind_eq_bind, Option.bind_some, hdr,
    fields, Vector.getElem_ofFn]
  congr 2
  exact funext fun i => funext fun j => coeff i j


private def decodeRounded (s : Level) (bytes : List Byte) (i : Fin s.params.k) (j : Fin 256) :
    Fin 1024 :=
  Fin.ofNat 1024 (unpackCoeff (Keccak.bytesToBitsLE (bytes.drop 32)) 10 (256 * i.val + j.val))

/-- Decode the rounded public coefficients and lift them by the FIPS factor `2^13`. -/
def publicKey (s : Level) (bytes : List Byte)
    (matrix : PublicMatrix s) : MLDSA.PublicKey s.params :=
  let t := Vector.ofFn fun i : Fin s.params.k => Vector.ofFn fun j : Fin 256 =>
    ((decodeRounded s bytes i j).val : ZMod 8380417) * 8192
  ⟨matrix, fun i j => t[i.val][j.val]⟩

private theorem highPart_range (r : ZMod 8380417) :
    0 ≤ (power2Round 8380417 13 r).1 ∧ (power2Round 8380417 13 r).1 < 1024 := by
  have h := power2Round_high_mul_add_low (d := 13) r
  have hlo := power2Round_low_mem_Ioc (by decide : 0 < 13) r
  have hr := r.val_lt
  change (power2Round 8380417 13 r).1 * 8192 + (power2Round 8380417 13 r).2 = (r.val : ℤ) at h
  change -4096 < (power2Round 8380417 13 r).2 ∧ (power2Round 8380417 13 r).2 ≤ 4096 at hlo
  omega

/-- Decoding the public-key bytes recovers the dilated high vector `2^13 t₁` coefficientwise,
including the upper endpoint 1023 in the ten-bit encoding. -/
theorem decode_encodePublic (s : Level) (rho : FixedBytes 32) (A : PublicMatrix s)
    (t : Fin s.params.k → Poly) :
    (publicKey s (encodePublic s rho.toList t) A).t = publicKeyHighTerm s.params 13 ⟨A, t⟩ := by
  funext i j
  have bounds (a b) := highPart_range (t a b)
  have hbits := unpack_packCoeffs (width := 10)
    (fun a b => (power2Round 8380417 13 (t a b)).1.toNat)
    (fun a b => by have := bounds a b; norm_num; omega) i j
  simp only [publicKey, Vector.getElem_ofFn, decodeRounded, encodePublic,
    List.drop_left' (by simp : rho.toList.length = 32), hbits, Fin.val_ofNat,
    publicKeyHighTerm, power2RoundVec]
  have hb : (power2Round 8380417 13 (t i j)).1.toNat < 1024 := by have := bounds i j; omega
  rw [Nat.mod_eq_of_lt hb]
  push_cast
  rw [← Int.cast_natCast (R := ZMod 8380417), Int.toNat_of_nonneg (bounds i j).1]

/-- A decoded public coefficient lies in [0,1023]. Multiplication by 2^13 preserves the
canonical lift, so rounding this lifted key recovers exactly Algorithm 8's public term. -/
private theorem highTerm_publicKey (s : Level) (bytes : List Byte) (matrix) :
    publicKeyHighTerm s.params 13 (publicKey s bytes matrix) =
      (publicKey s bytes matrix).t := by
  funext i j
  have coef (v : Fin 1024) :
      (((power2Round 8380417 13 ((v.val : ZMod 8380417) * 8192)).1 *
        (2 ^ (13 : ℕ) : ℕ) : ℤ) : ZMod 8380417) = (v.val : ZMod 8380417) * 8192 := by
    have hv : v.val * 8192 < 8380417 := by have := v.isLt; lia
    have hval : (((v.val : ZMod 8380417) * 8192)).val = v.val * 8192 := by
      have hcast : ((v.val * 8192 : ℕ) : ZMod 8380417) = (v.val : ZMod 8380417) * 8192 := by
        norm_num
      rw [← hcast, ZMod.val_natCast, Nat.mod_eq_of_lt hv]
    have hrem : ((((v.val * 8192 : ℕ) : ℤ) : ZMod (2 ^ 13))).valMinAbs = 0 := by
      have hz : (8192 : ZMod (2 ^ 13)) = 0 := by decide
      push_cast
      rw [hz, mul_zero, ZMod.valMinAbs_zero]
    simp only [power2Round, hval, hrem, sub_zero]
    push_cast
    norm_num
  simp only [publicKey, publicKeyHighTerm, power2RoundVec, Vector.getElem_ofFn]
  exact coef (decodeRounded s bytes i j)

/-- The raw SHAKE256 input for the message representative, with its public-key hash prefix. -/
@[expose] def representativeInput (tr : List Byte) (formatted : List Bool) : List Bool :=
  Keccak.bytesToBitsLE tr ++ formatted

/-- The 64-byte representative of a formatted bit string given the public-key hash tr. -/
@[expose] def Xofs.representativeFromTr (H : Xofs) (tr : List Byte) (formatted : List Bool) :
    List Bool :=
  Keccak.bytesToBitsLE (H.h256.read
    (representativeInput tr formatted) 64)

/-- FIPS 202 specialization of `Xofs.representativeFromTr`. -/
abbrev representativeFromTr := Xofs.representativeFromTr Xofs.shake

/-- The message representative fits exactly in the 512-bit measured register. -/
@[simp] theorem length_representativeFromTr {H : Xofs} (tr : List Byte) (formatted : List Bool) :
    (H.representativeFromTr tr formatted).length = 512 := by
  rw [Xofs.representativeFromTr, Keccak.length_bytesToBitsLE, H.h256.length_read]

/-- SHAKE256 on `BytesToBits(H(pk,64)) || M'`. In particular a formatted message may end
between two byte boundaries (Algorithm 8, lines 6–7). -/
@[expose] def Xofs.messageRepresentative (H : Xofs) (pk : List Byte)
    (formatted : List Bool) : List Bool :=
  H.representativeFromTr (H.h256.readBytes pk 64) formatted

/-- FIPS 202 specialization of `Xofs.messageRepresentative`. -/
abbrev messageRepresentative := Xofs.messageRepresentative Xofs.shake

namespace SharedDigest

/-- A module product on the canonical FIPS commitment grid is determined by its high bits. -/
@[expose] def OnCommitmentGrid (s : Level) (v : Fin s.params.k → Poly) : Prop :=
  ∀ i j, v i j = ((highBitsVec s.params v i j * (2 * s.params.γ₂ : ℕ) : ℤ) : ZMod 8380417)

instance (s : Level) (v : Fin s.params.k → Poly) : Decidable (OnCommitmentGrid s v) :=
  by unfold OnCommitmentGrid; infer_instance

end SharedDigest

/-- SHAKE256 input in Algorithm 8, line 12, including the message representative and
the fixed-width packing of the recovered high bits. -/
def commitmentInput (s : Level) (w : Fin s.params.k → Fin 256 → ℤ) (μ : List Bool) : List Bool :=
  let width := ((s.params.q - 1) / (2 * s.params.γ₂) - 1).log2 + 1
  μ ++ Keccak.bytesToBitsLE (packCoeffs width fun i j => (w i j).toNat)

/-- Bit length of the 512-bit representative followed by FIPS 204's packed high bits.
It is 6656 at ML-DSA-44 and -65, and 8704 at ML-DSA-87. -/
@[expose] def Level.commitmentInputBits (s : Level) : ℕ :=
  512 + 8 * (32 * (((s.params.q - 1) / (2 * s.params.γ₂) - 1).log2 + 1) * s.params.k)

/-- Packing a commitment after a full message representative has the parameter-set bit width. -/
theorem commitmentInput_length (s : Level) (w : Fin s.params.k → Fin 256 → ℤ)
    {μ : List Bool} (hμ : μ.length = 512) :
    (commitmentInput s w μ).length = s.commitmentInputBits := by
  simp only [commitmentInput, List.length_append, hμ, Keccak.length_bytesToBitsLE,
    Level.commitmentInputBits]
  exact congrArg (fun n => 512 + 8 * n)
    (length_packCoeffs (rows := s.params.k) (width := _) fun i j => (w i j).toNat)

/-- The two SHAKE256 inputs in the FIPS challenge computation have different lengths:
the 512-bit message representative is followed by a nonempty packed commitment, whereas the
digest seed for Algorithm 29 occupies at most 512 bits. -/
theorem commitmentInput_ne_digestInput {s : Level} (w : Fin s.params.k → Fin 256 → ℤ)
    {μ : List Bool} (hμ : μ.length = 512) {d : List Byte} (hd : d.length = digestBytes s) :
    commitmentInput s w μ ≠ Keccak.bytesToBitsLE d := by
  intro he
  have h := congrArg List.length he
  simp only [commitmentInput, List.length_append, hμ, Keccak.length_bytesToBitsLE, hd] at h
  rw [length_packCoeffs] at h
  cases s <;> revert h <;> decide

/-- Fixed-width packing distinguishes all high-bit vectors in the range of UseHint. -/
theorem eq_of_commitmentInput_eq {s : Level} {w v : Fin s.params.k → Fin 256 → ℤ} {μ : List Bool}
    (hw : ∀ i j, 0 ≤ w i j ∧ w i j < (((s.params.q - 1) / (2 * s.params.γ₂) : ℕ) : ℤ))
    (hv : ∀ i j, 0 ≤ v i j ∧ v i j < (((s.params.q - 1) / (2 * s.params.γ₂) : ℕ) : ℤ))
    (he : commitmentInput s w μ = commitmentInput s v μ) : w = v := by
  let width := ((s.params.q - 1) / (2 * s.params.γ₂) - 1).log2 + 1
  have size : (s.params.q - 1) / (2 * s.params.γ₂) ≤ 2 ^ width := by cases s <;> decide
  funext i j
  have strict {z : ℤ} (hz : z < (((s.params.q - 1) / (2 * s.params.γ₂) : ℕ) : ℤ)) :
      z.toNat < 2 ^ width := by
    have pos : 0 < 2 ^ width := by positivity
    omega
  have values := congrArg (fun bits => unpackCoeff bits width (256 * i.val + j.val))
    (List.append_cancel_left he)
  rw [unpack_packCoeffs _ (fun i j => strict (hw i j).2),
    unpack_packCoeffs _ (fun i j => strict (hv i j).2)] at values
  have := (hw i j).1
  have := (hv i j).1
  omega

/-- The full FIPS hash of the message representative and packed reconstructed commitment. -/
@[expose] def Xofs.commitmentDigest (H : Xofs) (s : Level) (w : Fin s.params.k → Fin 256 → ℤ)
    (μ : List Bool) : List Byte :=
  H.h256.read
    (commitmentInput s w μ) (digestBytes s)

/-- FIPS 202 specialization of `Xofs.commitmentDigest`. -/
abbrev commitmentDigest := Xofs.commitmentDigest Xofs.shake

/-- The commitment hash has the parameter set's exact digest length. -/
@[simp] theorem length_commitmentDigest {H : Xofs} (s : Level) (w : Fin s.params.k → Fin 256 → ℤ)
    (μ : List Bool) : (H.commitmentDigest s w μ).length = digestBytes s :=
  H.h256.length_read ..

private def hintedCommitment (s : Level) (pk : MLDSA.PublicKey s.params)
    (σ : Signature s) (c : Poly) : Fin s.params.k → Fin 256 → ℤ :=
  fun i => useHintVec s.params.q s.params.γ₂ (σ.h i)
    (moduleSISMap pk.A σ.z i - negacyclicMul c (pk.t i))

private abbrev Signature.acceptDigest {s : Level} (σ : Signature s) (digest : Unit → List Byte) :
    Bool :=
  decide (ResponseShort s.params σ.z) && decide (digest () = σ.digest)

/-- Algorithm 8 after successful parsing and expansion. The digest from the signature must match
the full SHAKE output byte for byte. -/
private def Xofs.check (H : Xofs) (s : Level) (pk : MLDSA.PublicKey s.params) (μ : List Bool)
    (σ : Signature s) (c : Poly) : Bool :=
  σ.acceptDigest fun _ => H.commitmentDigest s (hintedCommitment s pk σ c) μ

private abbrev check := Xofs.check Xofs.shake

private def Xofs.verifyInternalWith (H : Xofs) (s : Level)
    (expand : List Byte → Option (PublicMatrix s))
    (pk : List Byte) (formatted : List Bool) (signature : List Byte) :
    Option Bool := do
  if pk.length != 32 + 320 * s.params.k then return false
  let some σ := sigDecode s signature | return false
  let matrix ← expand (pk.take 32)
  let c ← H.sampleInBall s σ.digest
  return H.check s (publicKey s pk matrix) (H.messageRepresentative pk formatted) σ c

private abbrev verifyInternalWith := Xofs.verifyInternalWith Xofs.shake

/-- The pure-mode prefix in Algorithms 2 and 3, including the context length. -/
@[expose] def formatMessage (message : List Bool) (ctx : List Byte) : List Bool :=
  Keccak.bytesToBitsLE (0 :: Fin.ofNat 256 ctx.length :: ctx) ++ message

/-- Equal 512-bit representatives give equal full SHAKE256 outputs at the two raw inputs. -/
theorem read_eq_of_messageRepresentative_eq (H : Xofs) (pk : List Byte) {m n : List Bool}
    (h : H.messageRepresentative pk m = H.messageRepresentative pk n) :
    H.h256.read (representativeInput (H.h256.readBytes pk 64) m) 64 =
      H.h256.read (representativeInput (H.h256.readBytes pk 64) n) 64 :=
  Keccak.bytesToBitsLE_injective h

/-- The byte verifier places exactly 512 message-representative bits before the commitment. -/
@[simp] theorem length_messageRepresentative (H : Xofs) (pk : List Byte) (m : List Bool) :
    (H.messageRepresentative pk m).length = 512 := by
  rw [Xofs.messageRepresentative, Xofs.representativeFromTr, Keccak.length_bytesToBitsLE,
    H.h256.length_read]

/-- On the contexts allowed by Algorithm 3, the pure-mode prefix determines both the external
context and the entire bit-string message, including a final incomplete byte. -/
theorem formatMessage_inj {m n : List Bool} {c d : List Byte} (hc : c.length ≤ 255)
    (hd : d.length ≤ 255) (h : formatMessage m c = formatMessage n d) : c = d ∧ m = n := by
  let L (x : List Byte) := Keccak.byteBitsLE (Fin.ofNat 256 x.length)
  have h' : L c ++ (Keccak.bytesToBitsLE c ++ m) = L d ++ (Keccak.bytesToBitsLE d ++ n) := by
    apply List.append_cancel_left (as := Keccak.byteBitsLE 0)
    simpa only [formatMessage, Keccak.bytesToBitsLE, List.flatMap_cons, List.append_assoc, L]
      using h
  obtain ⟨ht, hb⟩ := List.append_inj h' (by simp [L, Keccak.byteBitsLE])
  have hv := congrArg (fun v => (Keccak.bitsToByteLE v).val) ht
  simp only [L, Keccak.bitsToByteLE_byteBitsLE, Fin.val_ofNat] at hv
  have hlen : c.length = d.length := by omega
  obtain ⟨hctx, hmsg⟩ := List.append_inj hb (by simp only [Keccak.length_bytesToBitsLE, hlen])
  exact ⟨Keccak.bytesToBitsLE_injective hctx, hmsg⟩

/-- Algorithm 8 for a formatted message. Invalid encodings return `some false`, and the
uniform Appendix C error for an exhausted SHAKE rejection stream is `none`. -/
def verifyInternal (s : Level) := verifyInternalWith s (expandA s)

/-- Algorithm 3 with the public matrix expansion supplied at its call site. The context and
signature checks, message hashing, challenge expansion, and full digest comparison are shared
with the concrete verifier. -/
def Xofs.verifyWithExpansion (H : Xofs) (s : Level) (expand : List Byte → Option (PublicMatrix s))
    (pk : List Byte) (message : List Bool) (ctx signature : List Byte) : Option Bool := do
  guard (ctx.length ≤ 255)
  H.verifyInternalWith s expand pk (formatMessage message ctx) signature

/-- FIPS 202 specialization of `Xofs.verifyWithExpansion`. -/
abbrev verifyWithExpansion := Xofs.verifyWithExpansion Xofs.shake

/-- On freshly encoded public bytes, the verifier reads exactly the published seed. Once its
matrix has been obtained from the shared oracle it can be reused in the digest check. -/
theorem verifyWithExpansion_encodePublic (s : Level) (expand : List Byte → Option (PublicMatrix s))
    (rho : FixedBytes 32) (t : Fin s.params.k → Poly) (A : PublicMatrix s)
    (hA : expand rho.toList = some A) (msg : List Bool) (ctx sig : List Byte) :
    verifyWithExpansion s expand (encodePublic s rho.toList t) msg ctx sig =
      verifyWithExpansion s (fun _ => some A) (encodePublic s rho.toList t) msg ctx sig := by
  simp only [verifyWithExpansion, Xofs.verifyWithExpansion, Xofs.verifyInternalWith,
    take_encodePublic, hA]

/-- Pure ML-DSA verification (Algorithm 3): format the context and the bit-string message,
then run Algorithm 8. Contexts longer than 255 bytes return the specified error. -/
@[expose] def Xofs.verify (H : Xofs) (s : Level) := H.verifyWithExpansion s (H.expandA s)

/-- The two verifiers return the same Boolean or error if their matrix, bounded sparse
challenge, message representative and final commitment digest agree. The representative
needs to agree only for a well-formed context and public-key length. -/
theorem Xofs.verify_congr_of_reads {H G : Xofs} (s : Level) (pk : List Byte)
    (msg : List Bool) (ctx sig : List Byte)
    (matrix : H.expandA s (pk.take 32) = G.expandA s (pk.take 32))
    (challenge : ∀ d : List Byte, d.length = digestBytes s →
      H.sampleInBall s d = G.sampleInBall s d)
    (rep : ctx.length ≤ 255 → pk.length = 32 + 320 * s.params.k →
      H.messageRepresentative pk (formatMessage msg ctx) =
        G.messageRepresentative pk (formatMessage msg ctx))
    (digest : ∀ w, H.commitmentDigest s w (G.messageRepresentative pk (formatMessage msg ctx)) =
      G.commitmentDigest s w (G.messageRepresentative pk (formatMessage msg ctx))) :
    H.verify s pk msg ctx sig = G.verify s pk msg ctx sig := by
  by_cases hc : ctx.length ≤ 255
  · simp only [Xofs.verify, Xofs.verifyWithExpansion, guard, hc, ↓reduceIte, Option.pure_def,
      Option.bind_eq_bind, Option.bind_some, Xofs.verifyInternalWith]
    by_cases hk : pk.length = 32 + 320 * s.params.k
    · simp only [hk, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      cases hd : sigDecode s sig with
      | none => rfl
      | some σ =>
        have short : σ.digest.length = digestBytes s := by
          rw [← digest_of_sigDecode hd, List.length_take, (sigDecode_parts hd).1]
          exact Nat.min_eq_left (by lia)
        simp only [matrix, challenge _ short, rep hc hk, Xofs.check, digest]
    · simp [hk, bne_iff_ne]
  · simp [Xofs.verify, Xofs.verifyWithExpansion, guard, hc]

/-- FIPS 202 specialization of `Xofs.verify`. -/
abbrev verify := Xofs.verify Xofs.shake

/-- Expand the concrete FIPS commitment digest to a sparse challenge. The zero value on
exhaustion is outside the challenge ball for every standard set. -/
def Xofs.algebraicHash (H : Xofs) (s : Level) : Hash s.params :=
  fun ⟨w, μ⟩ => (H.sampleInBall s (H.commitmentDigest s w μ)).getD 0

/-- FIPS 202 specialization of `Xofs.algebraicHash`. -/
private abbrev algebraicHash := Xofs.algebraicHash Xofs.shake

private theorem compressedVerify_of_check {s : Level} {bytes : List Byte} {matrix}
    {μ : List Bool} {σ : Signature s} {c : Poly} (hc : sampleInBall s σ.digest = some c)
    (hv : check s (publicKey s bytes matrix) μ σ c) :
    compressedVerify s.params 13 (algebraicHash s) (publicKey s bytes matrix) μ ⟨σ.z, σ.h, c⟩ := by
  simp only [check, Xofs.check, Bool.and_eq_true, decide_eq_true_eq] at hv
  simp only [compressedVerify, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hv.1, inBall_of_sampleInBall hc⟩, ?_⟩
  change (sampleInBall s (commitmentDigest s _ μ)).getD 0 = c
  simp only [compressedVerifierCommitment, highTerm_publicKey, Pi.sub_apply]
  change (sampleInBall s (Xofs.shake.commitmentDigest s
    (hintedCommitment s (publicKey s bytes matrix) σ c) μ)).getD 0 = c
  rw [hv.2, hc]
  rfl

/-- The byte-level forger chooses the context, message, and signature after seeing only the
published key. -/
structure Forgery where
  /-- External context of at most 255 bytes for an accepted forgery. -/
  context : List Byte
  /-- Original bit-string message. -/
  message : List Bool
  /-- Byte encoding of the purported signature. -/
  signature : List Byte
deriving DecidableEq

/-- Algorithm 3 frames the context before the bit-string message. -/
@[expose] def formattedMessage (f : Forgery) : List Bool :=
  formatMessage f.message f.context

private def candidate (s : Level) (pk : MLDSA.PublicKey s.params) (μ : List Bool)
    (σ : Signature s) (c : Poly) : SelfTargetCandidate s.params :=
  SelfTargetCandidate.ofCompressedForgery s.params 13 pk μ ⟨σ.z, σ.h, c⟩

private theorem parsed_of_verifyWithExpansion {H : Xofs} {s : Level} {bytes : List Byte}
    {expand : List Byte → Option (PublicMatrix s)} {f : Forgery}
    (hv : H.verifyWithExpansion s expand bytes f.message f.context f.signature = some true) :
    ∃ A σ c, expand (bytes.take 32) = some A ∧ sigDecode s f.signature = some σ ∧
      H.sampleInBall s σ.digest = some c ∧
      H.check s (publicKey s bytes A) (H.messageRepresentative bytes (formattedMessage f)) σ c := by
  simp only [Xofs.verifyWithExpansion, Xofs.verifyInternalWith] at hv
  have hctx : f.context.length ≤ 255 := by by_contra h; simp [guard, h] at hv
  have hlen : bytes.length = 32 + 320 * s.params.k := by
    by_contra h
    simp [guard, hctx, h] at hv
  cases hσ : sigDecode s f.signature with
  | none => simp [guard, hctx, hlen, hσ] at hv
  | some σ =>
    cases hA : expand (bytes.take 32) with
    | none => simp [guard, hctx, hlen, hσ, hA] at hv
    | some A =>
      cases hc : H.sampleInBall s σ.digest with
      | none => simp [guard, hctx, hlen, hσ, hA, hc] at hv
      | some c =>
        exact ⟨A, σ, c, rfl, rfl, hc, by
          simpa [guard, hctx, hlen, hσ, hA, hc, formattedMessage] using hv⟩

/-- A verifying byte string determines a short response and the precise digest equality for
the public vector decoded from the bytes. The calculation needs only that key and its matrix. -/
theorem recovered_of_verifyWithExpansion {H : Xofs} {s : Level} {bytes : List Byte}
    {expand : List Byte → Option (PublicMatrix s)} {A : PublicMatrix s} {f : Forgery}
    (hA : expand (bytes.take 32) = some A)
    (hv : H.verifyWithExpansion s expand bytes f.message f.context f.signature = some true) :
    ∃ σ c, sigDecode s f.signature = some σ ∧ H.sampleInBall s σ.digest = some c ∧
      ResponseShort s.params σ.z ∧
      H.commitmentDigest s (fun i => useHintVec s.params.q s.params.γ₂ (σ.h i)
        (compressedVerifierCommitment s.params 13 (publicKey s bytes A) σ.z c i))
        (H.messageRepresentative bytes (formattedMessage f)) = σ.digest := by
  obtain ⟨A', σ, c, hA', hσ, hc, hcheck⟩ := parsed_of_verifyWithExpansion hv
  rw [hA, Option.some.injEq] at hA'
  subst A'
  simp only [Xofs.check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  refine ⟨σ, c, hσ, hc, hcheck.1, ?_⟩
  simp only [compressedVerifierCommitment, highTerm_publicKey, Pi.sub_apply]
  exact hcheck.2

private theorem hintedCommitment_encodePublic {s : Level} (rho : FixedBytes 32)
    (A : PublicMatrix s) (t : Fin s.params.k → Poly) (σ : Signature s) (c : Poly) :
    hintedCommitment s (publicKey s (encodePublic s rho.toList t) A) σ c =
      fun i => useHintVec s.params.q s.params.γ₂ (σ.h i)
        (compressedVerifierCommitment s.params 13 ⟨A, t⟩ σ.z c i) := by
  unfold hintedCommitment compressedVerifierCommitment
  rw [decode_encodePublic]
  rfl

/-- A successful byte verification on a published `(ρ,t₁)` determines the parsed signature,
its sparse challenge, the response bound, and the complete FIPS digest equality, expressed
using the rounded high term of the original full vector `t`. -/
theorem verifiedSignature_of_verifyWithExpansion {H : Xofs} {s : Level}
    {expand : List Byte → Option (PublicMatrix s)} {rho : FixedBytes 32}
    {A : PublicMatrix s} {t : Fin s.params.k → Poly} {f : Forgery}
    (hA : expand rho.toList = some A)
    (hv : H.verifyWithExpansion s expand (encodePublic s rho.toList t)
      f.message f.context f.signature = some true) :
    ∃ σ c, sigDecode s f.signature = some σ ∧ H.sampleInBall s σ.digest = some c ∧
      ResponseShort s.params σ.z ∧
      H.commitmentDigest s (fun i => useHintVec s.params.q s.params.γ₂ (σ.h i)
        (compressedVerifierCommitment s.params 13 ⟨A, t⟩ σ.z c i))
        (H.messageRepresentative (encodePublic s rho.toList t) (formattedMessage f)) =
        σ.digest := by
  obtain ⟨σ, c, hσ, hc, hz, hd⟩ := recovered_of_verifyWithExpansion (f := f)
    (by rwa [take_encodePublic]) hv
  refine ⟨σ, c, hσ, hc, hz, ?_⟩
  rw [← hintedCommitment_encodePublic rho A t σ c]
  simp only [compressedVerifierCommitment, highTerm_publicKey, Pi.sub_apply] at hd
  exact hd

/-- Positive verification direction for an encoded public key and the verifier's exact
digest check. This also covers fixed, externally supplied matrix expansions. -/
theorem verifyWithExpansion_of_recovered {H : Xofs} {s : Level}
    {expand : List Byte → Option (PublicMatrix s)}
    {rho : FixedBytes 32} {A : PublicMatrix s} {t : Fin s.params.k → Poly} {f : Forgery}
    {σ : Signature s} {c : Poly} (hA : expand rho.toList = some A) (hctx : f.context.length ≤ 255)
    (hσ : sigDecode s f.signature = some σ) (hc : H.sampleInBall s σ.digest = some c)
    (hz : ResponseShort s.params σ.z)
    (hd : H.commitmentDigest s (fun i => useHintVec s.params.q s.params.γ₂ (σ.h i)
      (compressedVerifierCommitment s.params 13 ⟨A, t⟩ σ.z c i))
      (H.messageRepresentative (encodePublic s rho.toList t) (formattedMessage f)) = σ.digest) :
    H.verifyWithExpansion s expand (encodePublic s rho.toList t)
      f.message f.context f.signature = some true := by
  have len : (encodePublic s rho.toList t).length = 32 + 320 * s.params.k := by
    simp [encodePublic]
  change H.commitmentDigest s _
    (H.messageRepresentative _ (formatMessage f.message f.context)) = _ at hd
  simp [Xofs.verifyWithExpansion, Xofs.verifyInternalWith, guard, len, hctx, hσ, hc, hA, Xofs.check,
    hz, hintedCommitment_encodePublic, hd]

private theorem solution_of_compressed {s : Level} {hash : Hash s.params}
    {pk : MLDSA.PublicKey s.params} {μ : List Bool} {σ : Signature s} {c : Poly}
    (hv : compressedVerify s.params 13 hash pk μ ⟨σ.z, σ.h, c⟩) :
    IsSelfTargetSolution s.params (selfTargetHash s.params hash)
      (compressedSelfTargetRadius s.params 13) pk (candidate s pk μ σ c) := by
  exact isSelfTargetSolution_of_compressedVerify s.valid
    (by cases s <;> decide : 4 * s.params.γ₂ < s.params.q) (by decide : 0 < 13) hv

/-- Extraction for a full challenge `(A,t)`. The published bytes and message representative
use the rounded key, while the witness computed from the full key includes the term `c t₀`
in the low vector (Dilithium v3.1, §6.2.1, equation (10)). -/
def Xofs.extractFull (H : Xofs) (s : Level) (rho : FixedBytes 32) (A : PublicMatrix s)
    (t : Fin s.params.k → Poly) (f : Forgery) : Option (SelfTargetCandidate s.params) := do
  let σ ← sigDecode s f.signature
  let c ← H.sampleInBall s σ.digest
  return candidate s ⟨A, t⟩ (H.messageRepresentative (encodePublic s rho.toList t)
    (formattedMessage f)) σ c

/-- Check a corrected short witness on the original raw FIPS streams. Recover the complete
commitment digest only when the representative is 512 bits, the product is on the commitment
grid, the low part and response obey the extraction bound, and Algorithm 29 returns the
witness challenge. An exhausted expansion fails the check. -/
def Xofs.openFullWitness (H : Xofs) (s : Level) (pk : MLDSA.PublicKey s.params)
    (y : SelfTargetCandidate s.params) : Option (List Byte) := do
  let v := selfTargetMap s.params pk y.u y.z y.c
  let w := highBitsVec s.params v
  let radius := compressedSelfTargetRadius s.params 13
  guard (y.msg.length = 512)
  guard (ModuleSIS.inInfNormBound radius y.u ∧ ModuleSIS.inInfNormBound radius y.z)
  guard (SharedDigest.OnCommitmentGrid s v)
  let digest := H.commitmentDigest s w y.msg
  guard (H.sampleInBall s digest = some y.c)
  return digest

/-- A raw opening is equivalent to a short-vector solution on the canonical grid, with
the exact commitment digest and a successful sparse expansion at that digest. -/
theorem openFullWitness_eq_some_iff {H : Xofs} {s : Level}
    {pk : MLDSA.PublicKey s.params} {y : SelfTargetCandidate s.params} {d : List Byte} :
    H.openFullWitness s pk y = some d ↔
      let v := selfTargetMap s.params pk y.u y.z y.c
      y.msg.length = 512 ∧ SharedDigest.OnCommitmentGrid s v ∧
        H.commitmentDigest s (highBitsVec s.params v) y.msg = d ∧
        H.sampleInBall s d = some y.c ∧
        IsSelfTargetSolution s.params (selfTargetHash s.params (H.algebraicHash s))
          (compressedSelfTargetRadius s.params 13) pk y := by
  simp only [Xofs.openFullWitness, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.guard_eq_some', Option.pure_def, Option.some.injEq, exists_const]
  constructor
  · rintro ⟨len, ⟨hu, hz⟩, grid, hc, rfl⟩
    refine ⟨len, grid, rfl, hc, hu, hz, inBall_of_sampleInBall hc, ?_⟩
    exact congrArg (fun x => Option.getD x 0) hc
  · rintro ⟨len, grid, rfl, hc, sol⟩
    exact ⟨len, ⟨sol.1, sol.2.1⟩, grid, hc, rfl⟩

/-- An accepting byte signature gives a short witness whose raw opening recovers exactly the
digest bytes in that signature. The matrix at the public seed and the full public vector are
those of the lattice pair supplied to the extractor. -/
theorem opening_extractFull_of_verifyWithExpansion {H : Xofs} {s : Level}
    {expand : List Byte → Option (PublicMatrix s)} {rho : FixedBytes 32}
    {pk : MLDSA.PublicKey s.params} {f : Forgery} (hA : expand rho.toList = some pk.A)
    (hv : H.verifyWithExpansion s expand (encodePublic s rho.toList pk.t)
      f.message f.context f.signature = some true) :
    ∃ y, H.extractFull s rho pk.A pk.t f = some y ∧
      H.openFullWitness s pk y = some (f.signature.take (digestBytes s)) := by
  obtain ⟨σ, c, hs, hc, hz, hd⟩ := verifiedSignature_of_verifyWithExpansion hA hv
  let μ := H.messageRepresentative (encodePublic s rho.toList pk.t) (formattedMessage f)
  let sig : CompressedSignature s.params := ⟨σ.z, σ.h, c⟩
  let u := compressedForgeryLowPart s.params 13 pk sig
  have accepted : compressedVerify s.params 13 (H.algebraicHash s) pk μ sig := by
    simp only [compressedVerify, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hz, inBall_of_sampleInBall hc⟩, by simp [Xofs.algebraicHash, μ, sig, hd, hc]⟩
  refine ⟨candidate s pk μ σ c, by simp [Xofs.extractFull, hs, hc, μ], ?_⟩
  have high := highBits_selfTargetMap_compressedForgeryLowPart s.valid
    (by cases s <;> decide) 13 pk sig
  have grid : SharedDigest.OnCommitmentGrid s (selfTargetMap s.params pk u σ.z c) := by
    intro i j
    rw [show highBitsVec s.params (selfTargetMap s.params pk u σ.z c) = _ from high]
    exact congrFun (congrFun (selfTargetMap_compressedForgeryLowPart 13 pk sig) i) j
  have digest : H.commitmentDigest s
      (highBitsVec s.params (selfTargetMap s.params pk u σ.z c)) μ = σ.digest := by
    rw [show highBitsVec s.params (selfTargetMap s.params pk u σ.z c) = _ from high]
    exact hd
  rw [openFullWitness_eq_some_iff, digest_of_sigDecode hs]
  exact ⟨length_messageRepresentative .., grid, digest, hc, solution_of_compressed accepted⟩

/-- Every accepted byte forgery yields a solution on the full vector supplied by the challenge. -/
theorem extractFull_of_verifyWithExpansion {H : Xofs} {s : Level}
    {expand : List Byte → Option (PublicMatrix s)} {rho : FixedBytes 32}
    {A : PublicMatrix s} {t : Fin s.params.k → Poly} {f : Forgery}
    (hA : expand rho.toList = some A)
    (hv : H.verifyWithExpansion s expand (encodePublic s rho.toList t)
      f.message f.context f.signature = some true) :
    ∃ y, H.extractFull s rho A t f = some y ∧
      IsSelfTargetSolution s.params (selfTargetHash s.params (H.algebraicHash s))
        (compressedSelfTargetRadius s.params 13) ⟨A, t⟩ y := by
  obtain ⟨y, get, opened⟩ := opening_extractFull_of_verifyWithExpansion (pk := ⟨A, t⟩) hA hv
  exact ⟨y, get, (openFullWitness_eq_some_iff.mp opened).2.2.2.2⟩

/-- For each fixed published byte key, the solver parses the forgery and extracts a self-target
candidate. The hash input contains its actual public-key-bound message representative. -/
def extract (s : Level) (bytes : List Byte)
    (matrix : PublicMatrix s)
    (f : Forgery) : Option (SelfTargetCandidate s.params) := do
  let σ ← sigDecode s f.signature
  let c ← sampleInBall s σ.digest
  return candidate s (publicKey s bytes matrix)
    (messageRepresentative bytes (formattedMessage f)) σ c

/-- Self-target acceptance for a solver on a published byte key. The experiment constructs its
own challenge matrix from that key's seed and rounded coefficients. -/
def solves (s : Level) (bytes : List Byte)
    (solver : PublicMatrix s →
      Option (SelfTargetCandidate s.params)) : Bool :=
  (do
    let matrix ← expandA s (bytes.take 32)
    let sol ← solver matrix
    return decide (IsSelfTargetSolution s.params (selfTargetHash s.params (algebraicHash s))
      (compressedSelfTargetRadius s.params 13) (publicKey s bytes matrix) sol)).getD false

/-- Acceptance by the FIPS byte verifier implies self-target acceptance for the extracted
candidate on the same published key, including its matrix seed. -/
theorem solves_extract_of_verify {s : Level} {bytes : List Byte} {f : Forgery}
    (hv : verify s bytes f.message f.context f.signature = some true) :
    solves s bytes (fun matrix => extract s bytes matrix f) = true := by
  obtain ⟨A, σ, c, hA, hσ, hc, hcheck⟩ := parsed_of_verifyWithExpansion hv
  have hs := solution_of_compressed (compressedVerify_of_check hc hcheck)
  simpa [solves, hA, extract, hσ, hc] using hs

/-- Draw one uniform 32-byte seed and run an experiment under the resulting Algorithm 6
key pair. A key-generation failure is an unsuccessful trial. -/
@[expose] noncomputable def Xofs.keyExperiment (H : Xofs) (s : Level) (run : KeyPair → Game) :
    Game :=
  (PMF.uniformOfFintype (FixedBytes 32)).bind fun seed =>
    match H.keyGen s seed with
    | none => PMF.pure false
    | some keys => run keys

/-- Seeded key-generation experiment with the FIPS 202 XOFs. -/
noncomputable abbrev keyExperiment := Xofs.keyExperiment Xofs.shake

/-- FIPS 204 key-only forgery: draw the uniform key-generation seed, give the generated
public-key bytes to the adversary, and run Algorithm 3 on its context, message and signature. -/
@[expose] noncomputable def keyOnlyGame (s : Level) (adv : List Byte → ProbComp Forgery) : Game :=
  keyExperiment s fun keys => (adv keys.publicKey).eval.map fun f =>
    (verify s keys.publicKey f.message f.context f.signature).getD false

/-- Self-target success for the solver extracted from the byte-key forger, on the seeded
matrix and lifted public vector that the verifier can compute from the published key. -/
noncomputable def extractedSelfTargetGame (s : Level) (adv : List Byte → ProbComp Forgery) : Game :=
  keyExperiment s fun keys => (adv keys.publicKey).eval.map fun f =>
    solves s keys.publicKey fun matrix => extract s keys.publicKey matrix f

/-- The finite success bound under the Algorithm 6 seed law and Algorithm 3 verification.
The right-hand game tests the actual extracted candidate under that same seeded public key.
Replacing this seeded target by standard uniform-matrix hardness is a separate reduction. -/
theorem succProbability_verify_le_seededSelfTarget (s : Level)
    (adv : List Byte → ProbComp Forgery) :
    (keyOnlyGame s adv).succProbability ≤ (extractedSelfTargetGame s adv).succProbability := by
  apply Game.succProbability_mono
  unfold keyOnlyGame extractedSelfTargetGame keyExperiment Xofs.keyExperiment
  apply Probability.PMF.bind_apply_mono_on_support
  intro seed _
  cases hk : Xofs.shake.keyGen s seed with
  | none => exact le_rfl
  | some keys =>
    simp only [PMF.map]
    apply Probability.PMF.bind_apply_mono_on_support
    intro f _
    cases hv : verify s keys.publicKey f.message f.context f.signature with
    | none => simp [hv]
    | some b =>
      cases b
      · simp [hv]
      · simp [hv, solves_extract_of_verify hv]

/-- Expand an oracle's fixed-length commitment digest by Algorithm 29, including XOF
exhaustion at the Appendix C limit. -/
def expandDigest (s : Level) (digest : FixedBytes (digestBytes s)) : Option Poly :=
  sampleInBall s digest.toList

open ModuleSIS.SelfTarget in
/-- Classical self-target forking for the three FIPS parameter sets, in the model where a fresh
commitment query returns a uniform digest. Algorithm 29 acts on those digest bytes. The
collision term is the largest distinct-digest collision probability of the fixed SHAKE256
expansion; the library gives it only the trivial bound of one. -/
theorem selfTarget_digest_fork (s : Level) (Q : ℕ) {Coins : Type}
    (matrices : PMF (Matrix (Fin s.params.k) (Fin (s.params.k + s.params.ℓ + 1)) Poly))
    (coins : PMF Coins) (adv : Adversary s.params.k (s.params.k + s.params.ℓ) 256 8380417
      (FixedBytes (digestBytes s)) Coins)
    (hQ : ∀ A r, (adv A r).IsQueryBounded Q) :
    let radius := compressedSelfTargetRadius s.params 13
    ((matrices.bind (game (expandDigest s) radius coins adv)) true).toReal ≤
      (Q + 1 : ℕ) / ((256 : ℝ) ^ digestBytes s) + Real.sqrt ((Q + 1 : ℕ) *
        ((matrices.bind fun A => (reductionLaw 0 (expandDigest s) radius Q coins adv A).map
          fun w => decide (ModuleSIS.IsSolution A (2 * radius) w)) true +
            collisionMass (expandDigest s)).toReal) := by
  have hbyte : (2 : ℝ) ^ 8 = 256 := by norm_num
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, hbyte] using
    success_le_fork_digest (expandDigest s) (compressedSelfTargetRadius s.params 13) Q
      matrices coins adv hQ 0

end Cslib.Crypto.MLDSA.FIPS204
