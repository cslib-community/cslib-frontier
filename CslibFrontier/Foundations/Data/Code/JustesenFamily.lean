/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.Justesen
public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryField
public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryFieldArithmetic
public import CslibFrontier.Foundations.FieldTheory.Finite.HornerCoordinates
import CslibFrontier.Foundations.Data.BitString.Binary
import Mathlib.Data.Nat.Bitwise
import Mathlib.LinearAlgebra.Lagrange

/-!
# Justesen codewords for finite labels

Pack the binary digits of each label into the coefficients of a Reed–Solomon polynomial over
the explicit binary field. Apply the Justesen encoder to its evaluations at the nonzero
field elements. For the coding step of [Hoza2026NLUL, §2.1], we take the least field degree in the
Justesen family whose message capacity is at least 512 times the bit count
`1 + log₂ (w * (n + 1))`. Consecutive capacities have bounded ratio, so the block length
is proportional to that bit count. The relative distance bound gives at least four times
that bit count in differing coordinates for each pair of distinct labels.

The executable coordinate evaluators use Horner's rule over lists of field coefficient bits.
`indexedCodewordMod` computes the same indexed bits using modular shifts, without building a
multiplication table.
A native logspace implementation is tracked in cslib-frontier #6747.

## Main definitions

* `Cslib.Code.JustesenFamily.codeword`: the binary word for a label in `Fin w`.
* `Cslib.Code.JustesenFamily.codewordBit`: executable evaluation of a coordinate given the
  binary representation of its field point.
* `Cslib.Code.JustesenFamily.indexedCodewordMod`: indexed evaluation by modular shifts.

## Main results

* `Cslib.Code.JustesenFamily.length_bounds`: logarithmic block length at the chosen scale.
* `Cslib.Code.JustesenFamily.length_le_mul_hammingDist`: relative distance at least `1 / 128`.
* `Cslib.Code.JustesenFamily.log_le_hammingDist`: the logarithmic separation used in the
  tie-event union bound.
* `Cslib.Code.JustesenFamily.codewordBit_eq`: executable coordinate evaluation agrees with the
  algebraic codeword.
* `Cslib.Code.JustesenFamily.indexedCodewordMod_eq`: agreement with the table-based evaluator.
-/

public section

namespace Cslib.Code.JustesenFamily

open Polynomial

/-- The binary field degree at scale `s`. -/
@[expose] def scaleDegree (s : ℕ) : ℕ := 16 * (s + 1)

/-- The number of field coefficients in a message at scale `s`. -/
@[expose] def dimension (s : ℕ) : ℕ := 2 ^ (scaleDegree s - 1)
private def capacity (s : ℕ) : ℕ := dimension s * scaleDegree s

private theorem scaleDegree_ne_zero (s : ℕ) : scaleDegree s ≠ 0 := by
  unfold scaleDegree
  omega

private theorem le_capacity (s : ℕ) : s ≤ capacity s := by
  calc s
      ≤ scaleDegree s := by
        unfold scaleDegree
        omega
    _ ≤ capacity s := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)

/-- Moving to the next scale multiplies the message dimension by `2 ^ 16`. -/
theorem dimension_succ (s : ℕ) : dimension (s + 1) = dimension s * 65536 := by
  have he : scaleDegree (s + 1) - 1 = scaleDegree s - 1 + 16 := by
    unfold scaleDegree
    omega
  rw [dimension, dimension, he, pow_add]
  rfl

private theorem capacity_succ_le (s : ℕ) : capacity (s + 1) ≤ 131072 * capacity s := by
  have hb : scaleDegree (s + 1) ≤ 2 * scaleDegree s := by
    unfold scaleDegree
    omega
  simp only [capacity, dimension_succ]
  calc dimension s * 65536 * scaleDegree (s + 1)
      ≤ dimension s * 65536 * (2 * scaleDegree s) := Nat.mul_le_mul_left _ hb
    _ = 131072 * (dimension s * scaleDegree s) := by ring

private def target (w n : ℕ) : ℕ := Nat.log 2 (w * (n + 1)) + 1

private theorem exists_scale (w n : ℕ) : ∃ s, 512 * target w n ≤ capacity s :=
  ⟨512 * target w n, le_capacity _⟩

private def scale (w n : ℕ) : ℕ := Nat.find (exists_scale w n)

private theorem target_le_capacity (w n : ℕ) : 512 * target w n ≤ capacity (scale w n) :=
  Nat.find_spec (exists_scale w n)

private theorem capacity_le (w n : ℕ) : capacity (scale w n) ≤ 67108864 * target w n := by
  cases hs : scale w n with
  | zero =>
    change 524288 ≤ 67108864 * (Nat.log 2 (w * (n + 1)) + 1)
    omega
  | succ s =>
    have hlt : s < scale w n := by rw [hs]; omega
    have hprev := Nat.lt_of_not_ge (Nat.find_min (exists_scale w n) hlt)
    exact (capacity_succ_le s).trans (by omega)

/-- There are twice as many field elements as coefficients in the message at this scale. -/
theorem pow_scaleDegree (s : ℕ) : 2 ^ scaleDegree s = 2 * dimension s := by
  unfold dimension
  rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (scaleDegree_ne_zero s))]

private theorem dimension_le (s : ℕ) : dimension s ≤ 2 ^ scaleDegree s - 1 := by
  have h : 0 < dimension s := Nat.two_pow_pos _
  rw [pow_scaleDegree]
  omega

/-- Degree of the binary field at the least scale with sufficient message capacity. -/
def fieldDegree (w n : ℕ) : ℕ :=
  scaleDegree (scale w n)

/-- The selected field has positive degree. -/
theorem fieldDegree_ne_zero (w n : ℕ) : fieldDegree w n ≠ 0 :=
  scaleDegree_ne_zero _

/-- The chosen degree is the first `16 * (s + 1)` whose message capacity meets the
required threshold. The threshold also bounds the number of unsuccessful scales. -/
theorem fieldDegree_spec (w n : ℕ) :
    let threshold := 512 * (Nat.log2 (w * (n + 1)) + 1)
    ∃ s ≤ threshold, fieldDegree w n = scaleDegree s ∧
      threshold ≤ dimension s * scaleDegree s ∧
      ∀ j < s, dimension j * scaleDegree j < threshold := by
  simpa only [target, ← Nat.log2_eq_log_two, capacity] using
    (⟨scale w n, Nat.find_min' (exists_scale w n) (le_capacity (512 * target w n)), rfl,
      target_le_capacity w n,
      fun _ hj => Nat.lt_of_not_ge (Nat.find_min (exists_scale w n) hj)⟩ :
      ∃ s ≤ 512 * target w n, fieldDegree w n = scaleDegree s ∧
        512 * target w n ≤ capacity s ∧ ∀ j < s, capacity j < 512 * target w n)

/-- Number of coefficient blocks in the outer Reed–Solomon message at the selected scale. -/
def coefficientCount (w n : ℕ) : ℕ := dimension (scale w n)

/-- The coefficient count is the power of two retained by the capacity loop. -/
theorem coefficientCount_eq (w n : ℕ) :
    coefficientCount w n = 2 ^ (fieldDegree w n - 1) := by
  unfold coefficientCount dimension fieldDegree
  rfl

/-- Code coordinates are a nonzero evaluation point, a Wozencraft half, and a bit within it. -/
abbrev Coordinate (w n : ℕ) : Type :=
  (BinaryField (fieldDegree w n))ˣ × (Fin 2 × Fin (fieldDegree w n))

private def coefficientBits {w n : ℕ} (v : Fin w) (i : Fin (coefficientCount w n)) :
    BitString (fieldDegree w n) :=
  fun j => v.val.testBit (finProdFinEquiv (i, j))

private noncomputable def message {w n : ℕ} (v : Fin w) :
    degreeLT (BinaryField (fieldDegree w n)) (coefficientCount w n) :=
  (degreeLTEquiv _ _).symm fun i =>
    (BinaryField.equivBits (fieldDegree_ne_zero w n)).symm (coefficientBits v i)

/-- The Justesen encoding of the binary digits of a label, in least-significant-first order. -/
noncomputable def codeword {w n : ℕ} (v : Fin w) : Coordinate w n → Bool :=
  justesen (BinaryField.equivBits (fieldDegree_ne_zero w n))
    fun u => (message (n := n) v).val.eval (u : BinaryField (fieldDegree w n))

private theorem message_injective (w n : ℕ) :
    Function.Injective (message (w := w) (n := n)) := fun v v' h => Fin.ext <|
  Nat.eq_of_testBit_eq fun j => by
    by_cases hj : j < capacity (scale w n)
    · obtain ⟨⟨i, k⟩, hik⟩ :=
        (finProdFinEquiv (m := coefficientCount w n) (n := fieldDegree w n)).surjective ⟨j, hj⟩
      have hi := (BinaryField.equivBits (fieldDegree_ne_zero w n)).symm.injective
        (congrFun ((degreeLTEquiv _ _).symm.injective h) i)
      simpa only [coefficientBits, congrArg Fin.val hik] using congrFun hi k
    · have hcap := target_le_capacity w n
      have hj' : Nat.log 2 (w * (n + 1)) + 1 ≤ j := by
        unfold target at hcap
        omega
      have hp : w * (n + 1) < 2 ^ j :=
        (Nat.lt_pow_succ_log_self (by decide) _).trans_le (Nat.pow_le_pow_right (by decide) hj')
      have hw : w ≤ w * (n + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      rw [Nat.testBit_eq_false_of_lt (v.isLt.trans_le hw |>.trans hp),
        Nat.testBit_eq_false_of_lt (v'.isLt.trans_le hw |>.trans hp)]

/-- Different finite labels give different Justesen words. -/
theorem codeword_injective (w n : ℕ) : Function.Injective (codeword (w := w) (n := n)) :=
  fun v v' h => message_injective w n <| Subtype.ext <| by
    have he := justesen_injective (BinaryField.equivBits (fieldDegree_ne_zero w n)) h
    refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq
      (Finset.univ.image (Units.val : (BinaryField (fieldDegree w n))ˣ → _)) ?_ ?_
    · rw [Finset.card_image_of_injective _ Units.val_injective, Finset.card_univ,
        Fintype.card_units, BinaryField.card (fieldDegree_ne_zero w n)]
      exact (mem_degreeLT.1 ((degreeLT _ _).sub_mem (message v).2 (message v').2)).trans_le
        (Nat.cast_le.2 (dimension_le _))
    · intro x hx
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hx
      exact congrFun he u

private theorem card_coordinate (w n : ℕ) :
    Fintype.card (Coordinate w n) =
      (2 ^ scaleDegree (scale w n) - 1) * (2 * scaleDegree (scale w n)) := by
  rw [Fintype.card_prod, Fintype.card_units, BinaryField.card (fieldDegree_ne_zero w n),
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, fieldDegree]

/-- The block length is bounded above and below by constant multiples of the target bit count. -/
theorem length_bounds (w n : ℕ) :
    512 * (Nat.log 2 (w * (n + 1)) + 1) ≤ Fintype.card (Coordinate w n) ∧
      Fintype.card (Coordinate w n) ≤ 268435456 * (Nat.log 2 (w * (n + 1)) + 1) := by
  change 512 * target w n ≤ _ ∧ _ ≤ 268435456 * target w n
  rw [card_coordinate]
  set s := scale w n
  constructor
  · refine (target_le_capacity w n).trans ?_
    calc
      capacity s ≤ (2 ^ scaleDegree s - 1) * scaleDegree s :=
        Nat.mul_le_mul_right _ (dimension_le s)
      _ ≤ (2 ^ scaleDegree s - 1) * (2 * scaleDegree s) := Nat.mul_le_mul_left _ (by omega)
  · calc
      (2 ^ scaleDegree s - 1) * (2 * scaleDegree s) ≤ 2 ^ scaleDegree s * (2 * scaleDegree s) :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = 4 * capacity s := by rw [pow_scaleDegree, capacity]; ring
      _ ≤ 268435456 * target w n := by
        have h : capacity s ≤ 67108864 * target w n := capacity_le w n
        omega

/-- Distinct labels differ on at least one hundred twenty-eighth of the coordinates. -/
theorem length_le_mul_hammingDist {w n : ℕ} {v v' : Fin w} (hne : v ≠ v') :
    Fintype.card (Coordinate w n) ≤ 128 * hammingDist (codeword (n := n) v) (codeword v') := by
  let s := scale w n
  let φ := BinaryField.equivBits (fieldDegree_ne_zero w n)
  have hmem (x : Fin w) : codeword (n := n) x ∈ justesenCode φ (dimension s) :=
    ⟨_, eval_mem_reedSolomon _ (mem_degreeLT.1 (message x).2), rfl⟩
  have hd := minDist_le_hammingDist (hmem v) (hmem v') (codeword_injective w n |>.ne hne)
  have h := card_le_mul_minDist_justesenCode (Nat.succ_pos s) φ
  refine Nat.cast_le.1 (h.trans ?_)
  rw [Nat.cast_mul, Nat.cast_ofNat]
  gcongr
  exact hd

/-- Distinct codewords have enough separation for the union bound over the tie events in
[Hoza2026NLUL, §2.2]. -/
theorem log_le_hammingDist {w n : ℕ} {v v' : Fin w} (hne : v ≠ v') :
    4 * (Nat.log 2 (w * (n + 1)) + 1) ≤ hammingDist (codeword (n := n) v) (codeword v') := by
  have hd := (length_bounds w n).1.trans (length_le_mul_hammingDist (n := n) hne)
  omega

private theorem lowBits_coefficient_eq {w n : ℕ} (v : Fin w)
    (i : Fin (dimension (scale w n))) :
    BitString.lowBits (fieldDegree w n) (v.val >>> (fieldDegree w n * i.val)) =
      List.ofFn (coefficientBits (n := n) v i) := by
  rw [BitString.lowBits_eq_ofFn]
  apply congrArg List.ofFn
  funext j
  rw [Nat.testBit_shiftRight]
  change v.val.testBit (fieldDegree w n * i.val + j.val) =
    v.val.testBit (j.val + fieldDegree w n * i.val)
  rw [Nat.add_comm]

private def codewordBitWith {w n : ℕ} (mul : List Bool → List Bool → List Bool)
    (v : Fin w) (point : BitString (fieldDegree w n)) (half : Fin 2)
    (j : Fin (fieldDegree w n)) : Bool :=
  let x := List.ofFn point
  let a := BinaryField.hornerBits (fieldDegree w n) mul x
    fun i : Fin (dimension (scale w n)) =>
      BitString.lowBits (fieldDegree w n) (v.val >>> (fieldDegree w n * i.val))
  wozencraftBitWith mul x a half j

open BinaryField in
/-- Evaluate one coordinate using the power-basis bits of its field point. Half zero returns the
Reed–Solomon evaluation, and half one returns the evaluation multiplied by the point. -/
def codewordBit {w n : ℕ} (v : Fin w) (point : BitString (fieldDegree w n)) (half : Fin 2)
    (j : Fin (fieldDegree w n)) : Bool :=
  codewordBitWith (fieldMul (fieldTable (fieldDegree w n))) v point half j

open BinaryField in
private theorem fieldOfBits_evalBits {w n : ℕ} {mul : List Bool → List Bool → List Bool}
    (hmul : ∀ a b, fieldOfBits (basis (fieldDegree_ne_zero w n)) (mul a b) =
      fieldOfBits (basis (fieldDegree_ne_zero w n)) a *
        fieldOfBits (basis (fieldDegree_ne_zero w n)) b)
    (v : Fin w) (point : BitString (fieldDegree w n)) :
    fieldOfBits (basis (fieldDegree_ne_zero w n))
        (hornerBits (fieldDegree w n) mul (List.ofFn point)
          fun i : Fin (dimension (scale w n)) =>
            BitString.lowBits (fieldDegree w n) (v.val >>> (fieldDegree w n * i.val))) =
      (message (n := n) v).val.eval ((equivBits (fieldDegree_ne_zero w n)).symm point) := by
  rw [fieldOfBits_hornerBits _ hmul,
    eval_eq_sum_degreeLTEquiv (message (n := n) v).2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lowBits_coefficient_eq, fieldOfBits_ofFn, fieldOfBits_ofFn, message,
    LinearEquiv.apply_symm_apply]

open BinaryField in
private theorem codewordBitWith_eq {w n : ℕ} {mul : List Bool → List Bool → List Bool}
    (hmul : ∀ a b, fieldOfBits (basis (fieldDegree_ne_zero w n)) (mul a b) =
      fieldOfBits (basis (fieldDegree_ne_zero w n)) a *
        fieldOfBits (basis (fieldDegree_ne_zero w n)) b)
    (v : Fin w) (u : (BinaryField (fieldDegree w n))ˣ)
    (half : Fin 2) (j : Fin (fieldDegree w n)) :
    codewordBitWith mul v (equivBits (fieldDegree_ne_zero w n) u) half j =
      codeword v (u, (half, j)) := by
  let hb := fieldDegree_ne_zero w n
  let point := equivBits hb (u : BinaryField (fieldDegree w n))
  have ha := fieldOfBits_evalBits hmul v point
  rw [AddEquiv.symm_apply_apply] at ha
  unfold codewordBitWith wozencraftBitWith codeword justesen concat wozencraft
  dsimp only
  simp only [Fin.val_eq_zero_iff]
  split_ifs with h
  · rw [← equivBits_fieldOfBits hb, ha]
  · rw [← equivBits_fieldOfBits hb, hmul,
      fieldOfBits_ofFn, AddEquiv.symm_apply_apply, ha]

open BinaryField in
/-- Executable coordinate evaluation agrees with the algebraic Justesen word. -/
theorem codewordBit_eq {w n : ℕ} (v : Fin w) (u : (BinaryField (fieldDegree w n))ˣ)
    (half : Fin 2) (j : Fin (fieldDegree w n)) :
    codewordBit v (equivBits (fieldDegree_ne_zero w n) u) half j = codeword v (u, (half, j)) :=
  codewordBitWith_eq (fieldOfBits_fieldMul (isMulTable_fieldTable _)) v u half j

/-- Length of the coordinate list in evaluation-point, half, and bit order. -/
@[expose] def codeLength (w n : ℕ) : ℕ :=
  (2 ^ fieldDegree w n - 1) * (2 * fieldDegree w n)

private def unrankCoordinate (points degree : ℕ) :
    Fin (points * (2 * degree)) ≃ Fin points × (Fin 2 × Fin degree) :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv.symm)

/-- Unrank an executable codeword index in point, half, then bit order. -/
def decodeCoordinate (w n : ℕ) :
    Fin (codeLength w n) ≃ Fin (2 ^ fieldDegree w n - 1) × (Fin 2 × Fin (fieldDegree w n)) :=
  unrankCoordinate (2 ^ fieldDegree w n - 1) (fieldDegree w n)

/-- The numeric fields of one executable Justesen codeword coordinate. -/
structure CoordinateNumbers where
  /-- The positive binary number of the field point. -/
  point : ℕ
  /-- The zero-based Wozencraft half. -/
  half : ℕ
  /-- The zero-based bit within that half. -/
  bit : ℕ

/-- Decode a binary index at the supplied degree. The index runs through all bits in a half,
then both halves at a point, before advancing to the next nonzero point. -/
@[expose] def decodeIndex (degree index : ℕ) : CoordinateNumbers :=
  let block := 2 * degree
  let withinPoint := index % block
  ⟨index / block + 1, withinPoint / degree, withinPoint % degree⟩

private theorem decodeIndex_eq_unrankCoordinate {points degree : ℕ}
    (j : Fin (points * (2 * degree))) :
    decodeIndex degree j.val =
      let (point, half, bit) := unrankCoordinate points degree j
      ⟨point.val + 1, half.val, bit.val⟩ := by
  dsimp only [decodeIndex, unrankCoordinate]
  simp only [Equiv.trans_apply, finProdFinEquiv_symm_apply, Equiv.prodCongr_apply, Prod.map,
    Equiv.refl_apply, Fin.coe_divNat, Fin.coe_modNat]

/-- On valid indices the numeric decoder reads the same coordinate as the equivalence used
by the indexed evaluator. The point field uses the positive numbering of the field words. -/
theorem decodeIndex_eq_decodeCoordinate {w n : ℕ} (j : Fin (codeLength w n)) :
    decodeIndex (fieldDegree w n) j.val =
      let (point, half, bit) := decodeCoordinate w n j
      ⟨point.val + 1, half.val, bit.val⟩ :=
  decodeIndex_eq_unrankCoordinate
    (show Fin ((2 ^ fieldDegree w n - 1) * (2 * fieldDegree w n)) from j)

/-- The power-basis bits of the positively numbered field point at zero-based rank `i`. -/
def nonzeroPointBits {b : ℕ} (i : Fin (2 ^ b - 1)) : BitString b :=
  (BitString.equivFin b).symm ⟨i.val + 1, by have := i.isLt; omega⟩

/-- On a valid index the little-endian word of the decoded point is the exact power-basis
word passed to the indexed evaluator. -/
theorem lowBits_decodeIndex_point {w n : ℕ} (j : Fin (codeLength w n)) :
    BitString.lowBits (fieldDegree w n) (decodeIndex (fieldDegree w n) j.val).point =
      List.ofFn (nonzeroPointBits (decodeCoordinate w n j).1) := by
  rw [decodeIndex_eq_decodeCoordinate j]
  obtain ⟨point, half, bit⟩ := decodeCoordinate w n j
  exact BitString.lowBits_eq_ofFn_equivFin_symm (fieldDegree w n)
    ⟨point.val + 1, by have := point.isLt; omega⟩

/-- The codeword in executable coordinate order. Points are numbered as positive binary
integers in power-basis coordinates. -/
def indexedCodeword {w n : ℕ} (v : Fin w) (j : Fin (codeLength w n)) : Bool :=
  let (point, half, bit) := decodeCoordinate w n j
  codewordBit v (nonzeroPointBits point) half bit

open BinaryField in
/-- Evaluate one indexed coordinate with modular shifts and XORs, holding only the modulus
and individual field words. The multiplication kernel uses no precomputed table. -/
def indexedCodewordMod {w n : ℕ} (v : Fin w) : Fin (codeLength w n) → Bool :=
  let g := modulusBitsScan (fieldDegree w n)
  fun j =>
    let (point, half, bit) := decodeCoordinate w n j
    codewordBitWith (fieldMulMod g) v (nonzeroPointBits point) half bit

open BinaryField in
/-- The table-free indexed bit selects a Wozencraft bit of the Horner evaluation of the binary
label's fixed-width coefficient blocks. -/
theorem indexedCodewordMod_eq_hornerBits {w n : ℕ} (v : Fin w) (j : Fin (codeLength w n)) :
    indexedCodewordMod v j =
      let (point, half, bit) := decodeCoordinate w n j
      let mul := fieldMulMod (modulusBitsScan (fieldDegree w n))
      let x := List.ofFn (nonzeroPointBits point)
      let y := hornerBits (fieldDegree w n) mul x (fun i : Fin (coefficientCount w n) =>
        BitString.lowBits (fieldDegree w n) (v.val >>> (fieldDegree w n * i.val)))
      wozencraftBitWith mul x y half.val bit.val := by
  unfold indexedCodewordMod
  obtain ⟨point, half, bit⟩ := decodeCoordinate w n j
  rfl

private theorem nonzeroPointBits_ne_zero {b : ℕ} (i : Fin (2 ^ b - 1)) :
    nonzeroPointBits i ≠ 0 := by
  intro h
  have h' := congrArg (fun x => (BitString.equivFin b x).val) h
  have hzero : (BitString.equivFin b (0 : BitString b)).val = 0 :=
    BitString.val_equivFin_false b
  rw [hzero] at h'
  simp [nonzeroPointBits] at h'

private noncomputable def pointUnit {b : ℕ} (hb : b ≠ 0) (i : Fin (2 ^ b - 1)) :
    (BinaryField b)ˣ :=
  Units.mk0 ((BinaryField.equivBits hb).symm (nonzeroPointBits i)) (by
    intro h
    apply nonzeroPointBits_ne_zero i
    simpa using congrArg (BinaryField.equivBits hb) h)

private theorem unitBits_pos {b : ℕ} (hb : b ≠ 0) (u : (BinaryField b)ˣ) :
    0 < (BitString.equivFin b (BinaryField.equivBits hb u)).val :=
  Nat.pos_of_ne_zero fun h => u.ne_zero <| (BinaryField.equivBits hb).injective <|
    (BitString.equivFin b).injective <| Fin.ext <| by
      rw [map_zero]
      exact h.trans (BitString.val_equivFin_false b).symm

private noncomputable def pointEquiv {b : ℕ} (hb : b ≠ 0) :
    Fin (2 ^ b - 1) ≃ (BinaryField b)ˣ where
  toFun := pointUnit hb
  invFun u :=
    let r := BitString.equivFin b (BinaryField.equivBits hb u)
    ⟨r.val - 1, by have := r.isLt; have := unitBits_pos hb u; dsimp [r] at *; omega⟩
  left_inv i := by
    apply Fin.ext
    simp [pointUnit, nonzeroPointBits]
  right_inv u := by
    apply Units.ext
    simp only [pointUnit, Units.val_mk0, nonzeroPointBits]
    have hr := unitBits_pos hb u
    rw [show (⟨(BitString.equivFin b (BinaryField.equivBits hb ↑u)).val - 1 + 1, _⟩ : Fin (2 ^ b)) =
      BitString.equivFin b (BinaryField.equivBits hb ↑u) from Fin.ext (by dsimp only; omega)]
    simp

private noncomputable def coordinateEquiv (w n : ℕ) :
    Fin (codeLength w n) ≃ Coordinate w n :=
  (decodeCoordinate w n).trans
    (Equiv.prodCongr (pointEquiv (fieldDegree_ne_zero w n)) (Equiv.refl _))

private theorem indexedCodeword_eq {w n : ℕ} (v : Fin w) (j : Fin (codeLength w n)) :
    indexedCodeword v j = codeword v (coordinateEquiv w n j) := by
  simp only [indexedCodeword, coordinateEquiv, Equiv.trans_apply]
  generalize decodeCoordinate w n j = coord
  obtain ⟨i, half, bit⟩ := coord
  simpa [pointEquiv, pointUnit] using
    codewordBit_eq v (pointUnit (fieldDegree_ne_zero w n) i) half bit

open BinaryField in
/-- Table-free evaluation returns the same bit in the existing indexed coordinate order. -/
theorem indexedCodewordMod_eq {w n : ℕ} (v : Fin w) (j : Fin (codeLength w n)) :
    indexedCodewordMod v j = indexedCodeword v j := by
  unfold indexedCodewordMod indexedCodeword
  obtain ⟨i, half, bit⟩ := decodeCoordinate w n j
  let hb := fieldDegree_ne_zero w n
  let u := pointUnit hb i
  have hpoint : equivBits hb u = nonzeroPointBits i := by simp [u, pointUnit]
  dsimp only
  rw [modulusBitsScan_eq, ← hpoint, codewordBit_eq v u,
    codewordBitWith_eq (fieldOfBits_fieldMulMod hb) v u]

/-- The executable block length has the same quantitative bounds as the algebraic one. -/
theorem codeLength_bounds (w n : ℕ) :
    512 * (Nat.log 2 (w * (n + 1)) + 1) ≤ codeLength w n ∧
      codeLength w n ≤ 268435456 * (Nat.log 2 (w * (n + 1)) + 1) := by
  rw [← Fintype.card_fin (codeLength w n), Fintype.card_congr (coordinateEquiv w n)]
  exact length_bounds w n

/-- The executable coordinate order preserves the distance needed for Hoza's union bound. -/
theorem log_le_hammingDist_indexedCodeword {w n : ℕ} {v v' : Fin w} (hne : v ≠ v') :
    4 * (Nat.log 2 (w * (n + 1)) + 1) ≤
      hammingDist (indexedCodeword (n := n) v) (indexedCodeword v') := by
  have h : hammingDist (indexedCodeword (n := n) v) (indexedCodeword v') =
      hammingDist (codeword (n := n) v) (codeword v') :=
    Finset.card_bij (fun j _ => coordinateEquiv w n j)
      (fun j hj => by simpa [indexedCodeword_eq] using (Finset.mem_filter.mp hj).2)
      (fun _ _ _ _ h => (coordinateEquiv w n).injective h)
      (fun j hj => ⟨(coordinateEquiv w n).symm j, by
        simpa [indexedCodeword_eq] using (Finset.mem_filter.mp hj).2,
        (coordinateEquiv w n).apply_symm_apply j⟩)
  exact h.symm ▸ log_le_hammingDist hne

end Cslib.Code.JustesenFamily
