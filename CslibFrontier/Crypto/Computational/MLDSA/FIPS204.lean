/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.CompressedKeyOnly
public import CslibFrontier.Crypto.Primitives.ByteString
public import CslibFrontier.Crypto.Primitives.Hash.Keccak.SHAKE128
public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Crypto.Game.Order
import Mathlib.Data.List.Sort
import Mathlib.Order.Interval.Finset.Fin
import CslibFrontier.Foundations.Data.BitString.List
import all Batteries.Data.List.Basic

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
`extractFull_of_verifyWithExpansion` constructs the candidate for the full vector.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability

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

/-- Length in bytes of the FIPS challenge digest for each parameter set (Table 1). -/
def digestBytes : Level → ℕ
  | .mlDSA44 => 32 | .mlDSA65 => 48 | .mlDSA87 => 64

/-- Maximum Hamming weight of the complete hint vector (Table 1). -/
def hintLimit : Level → ℕ
  | .mlDSA44 => 80 | .mlDSA65 => 55 | .mlDSA87 => 75

/-- A coefficient polynomial in the FIPS 204 negacyclic ring. -/
abbrev Poly := Fin 256 → ZMod 8380417

/-- The coefficient representation of the public module matrix for the selected parameter set. -/
abbrev PublicMatrix (s : Level) := Matrix (Fin s.params.k) (Fin s.params.ℓ) Poly

private def packCoeffs {rows : ℕ} (width : ℕ) (coeff : Fin rows → Fin 256 → ℕ) : List Byte :=
  let bits := (List.finRange rows).flatMap fun i =>
    (List.finRange 256).flatMap fun j => BitString.lowBits width (coeff i j)
  (bits.toChunks 8).map Keccak.bitsToByteLE

private def unpackCoeff (bits : List Bool) (width index : ℕ) : ℕ :=
  BitString.lsbValue ((bits.drop (width * index)).take width)

private theorem bitsOfChunks {bits : List Bool} (h : 8 ∣ bits.length) :
    Keccak.bytesToBitsLE ((bits.toChunks 8).map Keccak.bitsToByteLE) = bits := by
  let decode (chunks : List (List Bool)) :=
    Keccak.bytesToBitsLE (chunks.map Keccak.bitsToByteLE)
  have snoc (chunks : Array (List Bool)) (chunk : Array Bool) (hlen : chunk.size = 8) :
      decode (chunks.push chunk.toList).toList = decode chunks.toList ++ chunk.toList := by
    simp [decode, Keccak.bytesToBitsLE, hlen, Keccak.byteBitsLE_bitsToByteLE]
  have go (tail : List Bool) (cur : Array Bool) (done : Array (List Bool))
      (hp : 0 < cur.size) (hb : cur.size ≤ 8) (hdiv : 8 ∣ cur.size + tail.length) :
      decode (List.toChunks.go 8 tail cur done) = decode done.toList ++ cur.toList ++ tail := by
    induction tail generalizing cur done with
    | nil =>
      have hl : cur.size = 8 := by simp at hdiv; omega
      simp only [List.toChunks.go, List.append_nil]
      exact snoc done cur hl
    | cons x xs ih =>
      rw [List.toChunks.go]
      split
      · rename_i hc
        have hl : cur.size = 8 := beq_iff_eq.mp hc
        rw [ih _ _ (by simp) (by simp) (by simp_all; omega), snoc _ _ hl]
        simp
      · rename_i hn
        have hl : cur.size ≠ 8 := by simpa using hn
        rw [ih _ _ (by simp) (by simp; omega) (by simpa [Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hdiv)]
        simp
  cases bits with
  | nil => rfl
  | cons x xs =>
    change decode (List.toChunks.go 8 xs #[x] #[]) = x :: xs
    simpa [decode, Keccak.bytesToBitsLE] using
      go xs #[x] #[] (by simp) (by simp) (by simpa [Nat.add_comm] using h)

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
  simp only [packCoeffs, hbits, bitsOfChunks (by rw [hlen]; exact ⟨rows * 32 * width, by ring⟩),
    unpackCoeff]
  rw [show width * (256 * (i : ℕ) + j) = idx.val * width by exact Nat.mul_comm .., hrow]
  have hi : idx.val / 256 = i.val := by dsimp [idx]; omega
  have hj : idx.val % 256 = j.val := by dsimp [idx]; omega
  simpa only [flat, hi, hj, Fin.eta] using BitString.lsbValue_lowBits (hc i j)

private def uniformCoeffs : List Byte → List (ZMod 8380417)
  | a :: b :: c :: rest =>
    let x := a.val + 256 * b.val + 65536 * (c.val % 128)
    if x < 8380417 then (x : ZMod 8380417) :: uniformCoeffs rest else uniformCoeffs rest
  | _ => []

private def asPoly (coeffs : List (ZMod 8380417)) : Option Poly :=
  let a := coeffs.toArray
  if a.size < 256 then none else some (fun j => a[j.val]!)

/-- The coefficient of degree `j` in the inverse NTT, using the evaluation points
`ζ^(2 BitRev8(i)+1)` (FIPS 204 §2.5, equation (2.1)). The inverse of 256 modulo q is 8347681. -/
private def fromNTT (values : Poly) : Vector (ZMod 8380417) 256 :=
  let roots := Vector.ofFn fun a : Fin 512 => (1753 : ZMod 8380417) ^ a.val
  let inversePowers := Vector.ofFn fun i : Fin 256 =>
    511 - 2 * BitString.lsbValue (BitString.lowBits 8 i.val).reverse
  Vector.ofFn fun j : Fin 256 =>
    8347681 * ∑ i, values i * roots.get (Fin.ofNat 512 (inversePowers.get i * j.val))

private def tabulate {α : Type} (n : ℕ) (f : Fin n → Option α) : Option (Fin n → α) :=
  (fun v : Vector α n => v.get) <$> Vector.ofFnM f

/-- Algorithms 30 and 32, returning the matrix in coefficient representation. Each SHAKE128
stream absorbs `ρ || column || row` and may consume 894 bytes (Appendix C, Table 3). -/
def expandA (s : Level) (rho : List Byte) :
    Option (PublicMatrix s) := do
  let matrix ← Vector.ofFnM fun row : Fin s.params.k =>
    Vector.ofFnM fun col : Fin s.params.ℓ =>
      fromNTT <$> asPoly (uniformCoeffs (Keccak.shake128
        (rho ++ [Fin.ofNat 256 col.val, Fin.ofNat 256 row.val]) 894))
  return fun i j => ((matrix.get i).get j).get

private def boundedCoeff (η halfByte : ℕ) : Option (ZMod 8380417) :=
  if η = 2 then
    if halfByte < 15 then some ((2 : ZMod 8380417) - ↑(halfByte % 5)) else none
  else if halfByte < 9 then some (4 - (halfByte : ZMod 8380417)) else none

private def secretPoly (s : Level) (seed : List Byte) (nonce : ℕ) : Option Poly :=
  let bytes := Keccak.shake256 (seed ++ [Fin.ofNat 256 nonce, Fin.ofNat 256 (nonce / 256)]) 481
  asPoly (bytes.flatMap fun b =>
    ([b.val % 16, b.val / 16].filterMap (boundedCoeff s.params.η)))

/-- Public-key bytes of Algorithm 6, lines 6–8: concatenate the matrix seed and the ten
high bits of each coefficient of the full public vector, in row and coefficient order. -/
def encodePublic (s : Level) (rho : List Byte) (t : Fin s.params.k → Poly) : List Byte :=
  rho ++ packCoeffs 10 (fun i j => (power2Round 8380417 13 (t i j)).1.toNat)

/-- The seed used to expand the matrix can be read from the published bytes. -/
@[simp] theorem take_encodePublic (s : Level) (rho : FixedBytes 32) (t : Fin s.params.k → Poly) :
    (encodePublic s rho.toList t).take 32 = rho.toList := by
  simp [encodePublic]

/-- Algorithm 6, public-key output. The 32-byte seed expands into the matrix seed and the
secret-polynomial seed in a single SHAKE256 call. Rejection exhaustion yields `none`. -/
def keyGenPublic (s : Level) (seed : FixedBytes 32) : Option (List Byte) := do
  let expanded := Keccak.shake256
    (seed.toList ++ [Fin.ofNat 256 s.params.k, Fin.ofNat 256 s.params.ℓ]) 128
  let rho := expanded.take 32
  let rho' := (expanded.drop 32).take 64
  let matrix ← expandA s rho
  let s₁ ← tabulate _ fun i : Fin s.params.ℓ => secretPoly s rho' i.val
  let s₂ ← tabulate _ fun i : Fin s.params.k => secretPoly s rho' (s.params.ℓ + i.val)
  let t := moduleSISMap matrix s₁ + s₂
  return encodePublic s rho t

private def swaps (first count : ℕ) (bytes : List Byte) :
    Option (Equiv.Perm (Fin 256)) :=
  match count with
  | 0 => some (Equiv.refl _)
  | count + 1 => do
    let choices := bytes.dropWhile (fun b => decide (first < b.val))
    let b ← choices.head?
    let rest ← swaps (first + 1) count (choices.drop 1)
    return (Equiv.swap (Fin.ofNat 256 first) b).trans rest

private def signedTail (s : Level) (signs : List Bool) (i : Fin 256) : ZMod 8380417 :=
  if i.val < 256 - s.params.τ then 0
  else if signs[i.val - (256 - s.params.τ)]! then -1 else 1

/-- Algorithm 29. Preload the last τ positions with the SHAKE sign bits and exchange each
with its chosen position in increasing order. Future sign positions remain untouched because an
accepted index is at most the current position. The SHAKE256 limit is 221 bytes. -/
def sampleInBall (s : Level) (digest : List Byte) : Option Poly := do
  let bytes := Keccak.shake256 digest 221
  let e ← swaps (256 - s.params.τ) s.params.τ (bytes.drop 8)
  return signedTail s (Keccak.bytesToBitsLE (bytes.take 8)) ∘ e.symm

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

/-- Every successful FIPS expansion gives exactly τ signed unit coefficients. -/
theorem inBall_of_sampleInBall {s : Level} {digest : List Byte} {c : Poly}
    (h : sampleInBall s digest = some c) : InBall s.params.τ c := by
  cases he : swaps (256 - s.params.τ) s.params.τ ((Keccak.shake256 digest 221).drop 8) with
  | none => simp [sampleInBall, he] at h
  | some e =>
    rw [sampleInBall, he] at h
    exact (Option.some.inj h) ▸ inBall_signedTail s _ e

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

private theorem takeBytes_eq_of_bits {x y : List Byte} (n : ℕ) (hx : n ≤ x.length)
    (hy : n ≤ y.length)
    (he : (Keccak.bytesToBitsLE x).take (8 * n) = (Keccak.bytesToBitsLE y).take (8 * n)) :
    x.take n = y.take n := by
  induction n generalizing x y with
  | zero => simp
  | succ n ih =>
    cases x with
    | nil => simp at hx
    | cons a x =>
      cases y with
      | nil => simp at hy
      | cons b y =>
        have step (c : Byte) (l : List Byte) :
            (Keccak.bytesToBitsLE (c :: l)).take (8 * (n + 1)) =
              Keccak.byteBitsLE c ++ (Keccak.bytesToBitsLE l).take (8 * n) := by
          change ((Keccak.byteBitsLE c) ++ Keccak.bytesToBitsLE l).take _ = _
          rw [List.take_append, List.take_of_length_le (by simp [Keccak.byteBitsLE])]
          simp [Keccak.byteBitsLE, Nat.mul_succ]
        rw [step, step] at he
        obtain ⟨head, tail⟩ := List.append_inj he (by simp [Keccak.byteBitsLE])
        have hab : a = b := by simpa using congrArg Keccak.bitsToByteLE head
        simpa [hab] using ih (by simpa using hx) (by simpa using hy) tail

private theorem responseBytes_inj {s : Level} {x y : List Byte}
    (w : ℕ) (hw : w = s.params.γ₁.log2 + 1)
    (hx : 32 * w * s.params.ℓ ≤ x.length) (hy : 32 * w * s.params.ℓ ≤ y.length)
    (he : ∀ (i : Fin s.params.ℓ) (j : Fin 256),
      ((unpackCoeff (Keccak.bytesToBitsLE x) w (256 * i.val + j.val) : ℕ) : ZMod 8380417) =
        ↑(unpackCoeff (Keccak.bytesToBitsLE y) w (256 * i.val + j.val))) :
    x.take (32 * w * s.params.ℓ) = y.take (32 * w * s.params.ℓ) := by
  let n := 256 * s.params.ℓ
  have bitsLength (l : List Byte) : (Keccak.bytesToBitsLE l).length = 8 * l.length := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      change (Keccak.byteBitsLE a ++ Keccak.bytesToBitsLE l).length = _
      simp only [List.length_append, Keccak.byteBitsLE, BitString.length_lowBits, ih,
        List.length_cons, Nat.mul_succ]
      omega
  have cover (l : List Byte) (hl : 32 * w * s.params.ℓ ≤ l.length) :
      w * n ≤ (Keccak.bytesToBitsLE l).length := by
    rw [bitsLength]
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
  apply takeBytes_eq_of_bits _ hx hy
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

/-- SHAKE256 on `BytesToBits(H(pk,64)) || M'`. In particular a formatted message may end
between two byte boundaries (Algorithm 8, lines 6–7). -/
def messageRepresentative (pk : List Byte) (formatted : List Bool) : List Bool :=
  Keccak.bytesToBitsLE (Keccak.bitSponge Keccak.shake256Layout [true, true, true, true]
    (Keccak.bytesToBitsLE (Keccak.shake256 pk 64) ++ formatted) 64)

/-- SHAKE256 input in Algorithm 8, line 12, including the message representative and
the fixed-width packing of the recovered high bits. -/
def commitmentInput (s : Level) (w : Fin s.params.k → Fin 256 → ℤ) (μ : List Bool) : List Bool :=
  let width := ((s.params.q - 1) / (2 * s.params.γ₂) - 1).log2 + 1
  μ ++ Keccak.bytesToBitsLE (packCoeffs width fun i j => (w i j).toNat)

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
def commitmentDigest (s : Level) (w : Fin s.params.k → Fin 256 → ℤ) (μ : List Bool) :
    List Byte :=
  Keccak.bitSponge Keccak.shake256Layout [true, true, true, true]
    (commitmentInput s w μ) (digestBytes s)

private def hintedCommitment (s : Level) (pk : MLDSA.PublicKey s.params)
    (σ : Signature s) (c : Poly) : Fin s.params.k → Fin 256 → ℤ :=
  fun i => useHintVec s.params.q s.params.γ₂ (σ.h i)
    (moduleSISMap pk.A σ.z i - negacyclicMul c (pk.t i))

/-- Algorithm 8 after successful parsing and expansion. The digest from the signature must match
the full SHAKE output byte for byte. -/
private def check (s : Level) (pk : MLDSA.PublicKey s.params) (μ : List Bool)
    (σ : Signature s) (c : Poly) : Bool :=
  decide (ResponseShort s.params σ.z) &&
    decide (commitmentDigest s (hintedCommitment s pk σ c) μ = σ.digest)

private def verifyInternalWith (s : Level) (expand : List Byte → Option (PublicMatrix s))
    (pk : List Byte) (formatted : List Bool) (signature : List Byte) :
    Option Bool := do
  if pk.length != 32 + 320 * s.params.k then return false
  let some σ := sigDecode s signature | return false
  let matrix ← expand (pk.take 32)
  let c ← sampleInBall s σ.digest
  return check s (publicKey s pk matrix) (messageRepresentative pk formatted) σ c

/-- Algorithm 8 for a formatted message. Invalid encodings return `some false`, and the
uniform Appendix C error for an exhausted SHAKE rejection stream is `none`. -/
def verifyInternal (s : Level) := verifyInternalWith s (expandA s)

/-- Algorithm 3 with the public matrix expansion supplied at its call site. The context and
signature checks, message hashing, challenge expansion, and full digest comparison are shared
with the concrete verifier. -/
def verifyWithExpansion (s : Level) (expand : List Byte → Option (PublicMatrix s))
    (pk : List Byte) (message : List Bool) (ctx signature : List Byte) : Option Bool := do
  guard (ctx.length ≤ 255)
  let formatted := Keccak.bytesToBitsLE (0 :: Fin.ofNat 256 ctx.length :: ctx) ++ message
  verifyInternalWith s expand pk formatted signature

/-- On freshly encoded public bytes, the verifier reads exactly the published seed. Once its
matrix has been obtained from the shared oracle it can be reused in the digest check. -/
theorem verifyWithExpansion_encodePublic (s : Level) (expand : List Byte → Option (PublicMatrix s))
    (rho : FixedBytes 32) (t : Fin s.params.k → Poly) (A : PublicMatrix s)
    (hA : expand rho.toList = some A) (msg : List Bool) (ctx sig : List Byte) :
    verifyWithExpansion s expand (encodePublic s rho.toList t) msg ctx sig =
      verifyWithExpansion s (fun _ => some A) (encodePublic s rho.toList t) msg ctx sig := by
  simp only [verifyWithExpansion, verifyInternalWith, take_encodePublic, hA]

/-- Pure ML-DSA verification (Algorithm 3): format the context and the bit-string message,
then run Algorithm 8. Contexts longer than 255 bytes return the specified error. -/
def verify (s : Level) := verifyWithExpansion s (expandA s)

/-- Expand the concrete FIPS commitment digest to a sparse challenge. The zero value on
exhaustion is outside the challenge ball for every standard set. -/
def algebraicHash (s : Level) : Hash s.params :=
  fun ⟨w, μ⟩ => (sampleInBall s (commitmentDigest s w μ)).getD 0

private theorem compressedVerify_of_check {s : Level} {bytes : List Byte} {matrix}
    {μ : List Bool} {σ : Signature s} {c : Poly} (hc : sampleInBall s σ.digest = some c)
    (hv : check s (publicKey s bytes matrix) μ σ c) :
    compressedVerify s.params 13 (algebraicHash s) (publicKey s bytes matrix) μ ⟨σ.z, σ.h, c⟩ := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hv
  simp only [compressedVerify, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hv.1, inBall_of_sampleInBall hc⟩, ?_⟩
  change (sampleInBall s (commitmentDigest s _ μ)).getD 0 = c
  simp only [compressedVerifierCommitment, highTerm_publicKey, Pi.sub_apply]
  change (sampleInBall s (commitmentDigest s
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

/-- Algorithm 3 frames the context before the bit-string message. -/
@[expose] def formattedMessage (f : Forgery) : List Bool :=
  Keccak.bytesToBitsLE (0 :: Fin.ofNat 256 f.context.length :: f.context) ++ f.message

private def candidate (s : Level) (pk : MLDSA.PublicKey s.params) (μ : List Bool)
    (σ : Signature s) (c : Poly) : SelfTargetCandidate s.params :=
  SelfTargetCandidate.ofCompressedForgery s.params 13 pk μ ⟨σ.z, σ.h, c⟩

private theorem parsed_of_verifyWithExpansion {s : Level} {bytes : List Byte}
    {expand : List Byte → Option (PublicMatrix s)} {f : Forgery}
    (hv : verifyWithExpansion s expand bytes f.message f.context f.signature = some true) :
    ∃ A σ c, expand (bytes.take 32) = some A ∧ sigDecode s f.signature = some σ ∧
      sampleInBall s σ.digest = some c ∧
      check s (publicKey s bytes A) (messageRepresentative bytes (formattedMessage f)) σ c := by
  simp only [verifyWithExpansion, verifyInternalWith] at hv
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
      cases hc : sampleInBall s σ.digest with
      | none => simp [guard, hctx, hlen, hσ, hA, hc] at hv
      | some c =>
        exact ⟨A, σ, c, rfl, rfl, hc, by
          simpa [guard, hctx, hlen, hσ, hA, hc, formattedMessage] using hv⟩

/-- A successful byte verification on a published `(ρ,t₁)` determines the parsed signature,
its sparse challenge, the response bound, and the complete FIPS digest equality, expressed
using the rounded high term of the original full vector `t`. -/
theorem verifiedSignature_of_verifyWithExpansion {s : Level}
    {expand : List Byte → Option (PublicMatrix s)} {rho : FixedBytes 32}
    {A : PublicMatrix s} {t : Fin s.params.k → Poly} {f : Forgery}
    (hA : expand rho.toList = some A)
    (hv : verifyWithExpansion s expand (encodePublic s rho.toList t)
      f.message f.context f.signature = some true) :
    ∃ σ c, sigDecode s f.signature = some σ ∧ sampleInBall s σ.digest = some c ∧
      ResponseShort s.params σ.z ∧
      commitmentDigest s (fun i => useHintVec s.params.q s.params.γ₂ (σ.h i)
        (compressedVerifierCommitment s.params 13 ⟨A, t⟩ σ.z c i))
        (messageRepresentative (encodePublic s rho.toList t) (formattedMessage f)) = σ.digest := by
  obtain ⟨A', σ, c, hA', hσ, hc, hcheck⟩ := parsed_of_verifyWithExpansion hv
  rw [take_encodePublic, hA, Option.some.injEq] at hA'
  subst A'
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  refine ⟨σ, c, hσ, hc, hcheck.1, ?_⟩
  have hw : hintedCommitment s (publicKey s (encodePublic s rho.toList t) A) σ c =
      fun i => useHintVec s.params.q s.params.γ₂ (σ.h i)
        (compressedVerifierCommitment s.params 13 ⟨A, t⟩ σ.z c i) := by
    unfold hintedCommitment compressedVerifierCommitment
    rw [decode_encodePublic s rho A t]
    rfl
  rw [← hw]
  exact hcheck.2

private theorem solution_of_compressed {s : Level} {pk : MLDSA.PublicKey s.params}
    {μ : List Bool} {σ : Signature s} {c : Poly}
    (hv : compressedVerify s.params 13 (algebraicHash s) pk μ ⟨σ.z, σ.h, c⟩) :
    IsSelfTargetSolution s.params (selfTargetHash s.params (algebraicHash s))
      (compressedSelfTargetRadius s.params 13) pk (candidate s pk μ σ c) := by
  have hvalid : s.params.Valid := by
    cases s
    · exact Params.valid_mldsa44
    · exact Params.valid_mldsa65
    · exact Params.valid_mldsa87
  exact isSelfTargetSolution_of_compressedVerify hvalid
    (by cases s <;> decide : 4 * s.params.γ₂ < s.params.q) (by decide : 0 < 13) hv

/-- Extraction for a full challenge `(A,t)`. The published bytes and message representative
use the rounded key, while the witness computed from the full key includes the term `c t₀`
in the low vector (Dilithium v3.1, §6.2.1, equation (10)). -/
def extractFull (s : Level) (rho : FixedBytes 32) (A : PublicMatrix s)
    (t : Fin s.params.k → Poly) (f : Forgery) : Option (SelfTargetCandidate s.params) := do
  let σ ← sigDecode s f.signature
  let c ← sampleInBall s σ.digest
  return candidate s ⟨A, t⟩ (messageRepresentative (encodePublic s rho.toList t)
    (formattedMessage f)) σ c

/-- Every accepted byte forgery yields a solution on the full vector supplied by the challenge. -/
theorem extractFull_of_verifyWithExpansion {s : Level}
    {expand : List Byte → Option (PublicMatrix s)} {rho : FixedBytes 32}
    {A : PublicMatrix s} {t : Fin s.params.k → Poly} {f : Forgery}
    (hA : expand rho.toList = some A)
    (hv : verifyWithExpansion s expand (encodePublic s rho.toList t)
      f.message f.context f.signature = some true) :
    ∃ y, extractFull s rho A t f = some y ∧
      IsSelfTargetSolution s.params (selfTargetHash s.params (algebraicHash s))
        (compressedSelfTargetRadius s.params 13) ⟨A, t⟩ y := by
  obtain ⟨σ, c, hσ, hc, hz, hd⟩ := verifiedSignature_of_verifyWithExpansion hA hv
  let μ := messageRepresentative (encodePublic s rho.toList t) (formattedMessage f)
  have hv' : compressedVerify s.params 13 (algebraicHash s) ⟨A, t⟩ μ ⟨σ.z, σ.h, c⟩ := by
    simp only [compressedVerify, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hz, inBall_of_sampleInBall hc⟩, by simp [algebraicHash, μ, hd, hc]⟩
  exact ⟨_, by simp [extractFull, hσ, hc, μ], solution_of_compressed hv'⟩

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

/-- Run the supplied byte-key forger after generating the published key from a uniform 32-byte
seed, treating a key-generation failure as an unsuccessful trial. -/
private noncomputable def withForgery (s : Level) (adv : List Byte → ProbComp Forgery)
    (wins : List Byte → Forgery → Bool) : Game :=
  (PMF.uniformOfFintype (FixedBytes 32)).bind fun seed =>
    match keyGenPublic s seed with
    | none => PMF.pure false
    | some pk => (adv pk).eval.map (wins pk)

/-- FIPS 204 key-only forgery: draw the uniform key-generation seed, give the generated
public-key bytes to the adversary, and run Algorithm 3 on its context, message and signature. -/
noncomputable def keyOnlyGame (s : Level) (adv : List Byte → ProbComp Forgery) : Game :=
  withForgery s adv fun pk f => (verify s pk f.message f.context f.signature).getD false

/-- Self-target success for the solver extracted from the byte-key forger, on the seeded
matrix and lifted public vector that the verifier can compute from the published key. -/
noncomputable def extractedSelfTargetGame (s : Level) (adv : List Byte → ProbComp Forgery) : Game :=
  withForgery s adv fun pk f => solves s pk fun matrix => extract s pk matrix f

/-- The finite success bound under the Algorithm 6 seed law and Algorithm 3 verification.
The right-hand game tests the actual extracted candidate under that same seeded public key.
Replacing this seeded target by standard uniform-matrix hardness is a separate reduction. -/
theorem succProbability_verify_le_seededSelfTarget (s : Level)
    (adv : List Byte → ProbComp Forgery) :
    (keyOnlyGame s adv).succProbability ≤ (extractedSelfTargetGame s adv).succProbability := by
  apply Game.succProbability_mono
  unfold keyOnlyGame extractedSelfTargetGame withForgery
  apply Probability.PMF.bind_apply_mono_on_support
  intro seed _
  cases hk : keyGenPublic s seed with
  | none => exact le_rfl
  | some pk =>
    simp only [PMF.map]
    apply Probability.PMF.bind_apply_mono_on_support
    intro f _
    cases hv : verify s pk f.message f.context f.signature with
    | none => simp [hv]
    | some b =>
      cases b
      · simp [hv]
      · simp [hv, solves_extract_of_verify hv]

end Cslib.Crypto.MLDSA.FIPS204
