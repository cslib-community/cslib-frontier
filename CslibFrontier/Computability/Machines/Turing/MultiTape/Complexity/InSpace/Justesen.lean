/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import CslibFrontier.Foundations.Data.Code.JustesenFamily
public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryFieldArithmetic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BinaryModulus
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Bit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSize
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Foundations.Data.Nat.BinarySize

/-!
# Justesen dimensions and coordinate decoding in native space

The input consists of the binary width and horizon of a layered graph. Starting at degree
sixteen, a counted loop raises the degree by sixteen and multiplies the retained power of two
by a fixed factor, holding the state once the capacity suffices. The final degree and
power give the field degree and exact seed length of the existing Justesen generator. Native
space is linear in the encoded dimensions, including every live loop state. The binary degree
and index suffice to decode a coordinate. From the dimensions and index we can also produce
the little-endian power-basis word of the nonzero field point in linear space. The same
capacity run supplies the degree and coefficient count for a retained field context. A caller
with that context can prepare the point word, half and bit without recomputing the parameters.
-/

public section

namespace Cslib.Code.JustesenFamily

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

private abbrev encDimensions : ℕ × ℕ ↪ List Bool := encPair encNat encNat

private structure CapacityState where
  threshold : ℕ
  degree : ℕ
  power : ℕ

private enc_structure encCapacityState : CapacityState where
  threshold : encNat, degree : encNat, power : encNat

private def threshold (p : ℕ × ℕ) : ℕ :=
  512 * (Nat.log2 (p.1 * (p.2 + 1)) + 1)

private def atScale (T s : ℕ) : CapacityState :=
  ⟨T, scaleDegree s, dimension s⟩

private def advance (s : CapacityState) : CapacityState :=
  if s.power * s.degree < s.threshold then
    ⟨s.threshold, s.degree + 16, s.power * 65536⟩
  else s

private theorem advance_atScale_of_lt {T i : ℕ}
    (h : (atScale T i).power * (atScale T i).degree < T) :
    advance (atScale T i) = atScale T (i + 1) := by
  have h' : (atScale T i).power * (atScale T i).degree < (atScale T i).threshold := h
  rw [advance, ite_eq_left h']
  simp only [atScale, dimension_succ]
  congr 1

private theorem iterate_advance {T s : ℕ}
    (hok : T ≤ (atScale T s).power * (atScale T s).degree)
    (hsmall : ∀ i < s, (atScale T i).power * (atScale T i).degree < T) (i : ℕ) :
    advance^[i] (atScale T 0) = atScale T (min i s) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hi : i < s
    · rw [Nat.min_eq_left (Nat.le_of_lt hi), Nat.min_eq_left (Nat.succ_le_of_lt hi),
        advance_atScale_of_lt (hsmall i hi)]
    · rw [Nat.min_eq_right (Nat.le_of_not_gt hi), Nat.min_eq_right (by omega)]
      exact ite_eq_right (Nat.not_lt_of_ge hok)

private def computed (p : ℕ × ℕ) : CapacityState :=
  advance^[threshold p] (atScale (threshold p) 0)

private theorem logCapacity_le (p : ℕ × ℕ) :
    Nat.log2 (p.1 * (p.2 + 1)) + 1 ≤ (encDimensions p).length + 1 := by
  have hm := Nat.size_mul_le p.1 (p.2 + 1)
  have hsucc := Nat.size_add_le_max p.2 1
  change (p.2 + 1).size ≤ max p.2.size 1 + 1 at hsucc
  simp only [Nat.log2_eq_size_sub_one, encDimensions, length_encPair,
    length_encNat_eq_size]
  omega

private theorem length_threshold_le (p : ℕ × ℕ) :
    threshold p ≤ 512 * ((encDimensions p).length + 1) :=
  Nat.mul_le_mul_left 512 (logCapacity_le p)

/-- The numeric seed length is linear in the binary encoding of its graph dimensions. -/
theorem codeLength_le_encodedDimensions (p : ℕ × ℕ) :
    codeLength p.1 p.2 ≤ 268435456 * ((encPair encNat encNat p).length + 1) := by
  have hc := (codeLength_bounds p.1 p.2).2
  rw [← Nat.log2_eq_log_two] at hc
  exact hc.trans (Nat.mul_le_mul_left _ (logCapacity_le p))

private theorem power_le {T s : ℕ}
    (hsmall : ∀ i < s, (atScale T i).power * (atScale T i).degree < T) (j : ℕ)
    (hj : j ≤ s) : (atScale T j).power ≤ 65536 * (T + 1) := by
  cases j with
  | zero => change 32768 ≤ _; omega
  | succ i =>
    have h := hsmall i (by omega)
    have hp : (atScale T i).power ≤ (atScale T i).power * (atScale T i).degree :=
      Nat.le_mul_of_pos_right _ (by simp [atScale, scaleDegree])
    simp only [atScale] at h hp ⊢
    rw [dimension_succ]
    omega

private theorem length_iterate_le (p : ℕ × ℕ) (i : ℕ) :
    (encCapacityState (advance^[i] (atScale (threshold p) 0))).length ≤
      40000000 * ((encDimensions p).length + 1) := by
  obtain ⟨s, hs, -, hpass, hsmall⟩ := fieldDegree_spec p.1 p.2
  change s ≤ threshold p at hs
  change threshold p ≤ (atScale (threshold p) s).power * (atScale (threshold p) s).degree at hpass
  change ∀ j < s, (atScale (threshold p) j).power * (atScale (threshold p) j).degree <
    threshold p at hsmall
  rw [iterate_advance hpass hsmall]
  have hj := Nat.min_le_right i s
  have hT := length_threshold_le p
  simp only [encDimensions, length_encPair] at hT
  have hp := power_le hsmall (min i s) hj
  have hlen (n : ℕ) : (encNat n).length ≤ n :=
    length_encNat_eq_size n ▸ Nat.size_le_self n
  have hpower := (hlen _).trans hp
  simp only [encCapacityState_apply, encCapacityStateFields, length_encPair]
  dsimp only [atScale, scaleDegree] at *
  have hd := hlen (16 * (min i s + 1))
  have ht := hlen (threshold p)
  omega

private theorem threshold_inSpace : ComputableInSpace threshold encDimensions encNat
    (fun p => (encDimensions p).length) := by
  have hm := budget_natMul (fst encNat encNat) (budget_natSucc (snd encNat encNat))
  have hsize := budget_comp_linear natSize hm
  exact (budget_natMul (budget_const 512)
    (budget_natSucc (budget_natPred hsize))).of_enc_eq fun p => by
      simp only [threshold, Nat.log2_eq_size_sub_one]

private theorem advance_inSpace :
    ComputableInSpace advance encCapacityState encCapacityState
      (fun s => (encCapacityState s).length) := by
  have h := budget_id (BigOLe.refl fun s => (encCapacityState s).length)
  have ht := encCapacityState_threshold_budget h
  have hd := encCapacityState_degree_budget h
  have hp := encCapacityState_power_budget h
  have hnext : ComputableInSpace
      (fun s => CapacityState.mk s.threshold (s.degree + 16) (s.power * 65536))
      encCapacityState encCapacityState (fun s => (encCapacityState s).length) :=
    encCapacityState_mk_budget ht (budget_natAdd hd (budget_const 16))
      (budget_natMul hp (budget_const 65536))
  exact (budget_ite (budget_natLt (budget_natMul hp hd) ht) hnext h).of_enc_eq fun s => by
    simp only [advance, decide_eq_true_eq]

private theorem computed_inSpace :
    ComputableInSpace computed encDimensions encCapacityState
      (fun p => (encDimensions p).length) := by
  let : Inhabited CapacityState := ⟨atScale 0 0⟩
  exact budget_iterate threshold_inSpace
    (encCapacityState_mk_budget threshold_inSpace (budget_const 16)
      (budget_const 32768)) advance_inSpace
    (fun p i _ => length_iterate_le p i)
    (.of_le_linear 40000000 40000000 fun _ => by omega)

private theorem computed_eq_atScale (p : ℕ × ℕ) :
    ∃ s, computed p = atScale (threshold p) s ∧ fieldDegree p.1 p.2 = scaleDegree s := by
  obtain ⟨s, hs, hd, hpass, hsmall⟩ := fieldDegree_spec p.1 p.2
  change s ≤ threshold p at hs
  refine ⟨s, ?_, hd⟩
  rw [computed, iterate_advance (T := threshold p) hpass hsmall, Nat.min_eq_right hs]

/-- Compute the generator's chosen field degree in space linear in the binary width and
horizon. -/
theorem fieldDegree_inSpace :
    ComputableInSpace (fun p : ℕ × ℕ => fieldDegree p.1 p.2) (encPair encNat encNat) encNat
      (fun p => (encPair encNat encNat p).length) :=
  (encCapacityState_degree_budget computed_inSpace).of_enc_eq fun p => by
    obtain ⟨s, hs, hd⟩ := computed_eq_atScale p
    rw [hs, hd]
    rfl

/-- Compute the exact Justesen seed length in space linear in the binary width and horizon. -/
theorem codeLength_inSpace :
    ComputableInSpace (fun p : ℕ × ℕ => codeLength p.1 p.2) (encPair encNat encNat) encNat
      (fun p => (encPair encNat encNat p).length) := by
  have hin := BigOLe.refl fun s => (encCapacityState s).length
  have h := budget_id hin
  have hd := encCapacityState_degree_budget h
  have hp := encCapacityState_power_budget h
  have htwo :=
    budget_const (encIn := encCapacityState) (Bs := fun s => (encCapacityState s).length)
      (encB := encNat) 2
  have hlength := budget_natMul (budget_natPred (budget_natMul htwo hp)) (budget_natMul htwo hd)
  refine (budget_comp_linear hlength computed_inSpace).of_enc_eq ?_
  intro p
  obtain ⟨s, hs, hds⟩ := computed_eq_atScale p
  rw [hs, codeLength, hds, pow_scaleDegree]
  rfl

/-- Framed binary point number and half, followed by the unframed binary bit position. -/
enc_structure encCoordinateNumbers : CoordinateNumbers where
  point : encNat, half : encNat, bit : encNat

/-- Decoding one Justesen coordinate costs space linear in the binary degree and index. -/
theorem decodeIndex_inSpace :
    ComputableInSpace (fun p : ℕ × ℕ => decodeIndex p.1 p.2) (encPair encNat encNat)
      encCoordinateNumbers (fun p => (encPair encNat encNat p).length) := by
  have hdegree := fst encNat encNat
  have hindex := snd encNat encNat
  have hblock := budget_natMul (budget_const 2) hdegree
  have hwithin := budget_natMod hindex hblock
  exact encCoordinateNumbers_mk_budget (budget_natSucc (budget_natDiv hindex hblock))
    (budget_natDiv hwithin hdegree) (budget_natMod hwithin hdegree)

/-- A decoded coordinate with the field point materialized as a coefficient word. -/
structure CoordinateWord where
  /-- The little-endian coefficients of the field point. -/
  point : List Bool
  /-- The selected Wozencraft half as a binary natural. -/
  half : ℕ
  /-- The bit position in the selected half as a binary natural. -/
  bit : ℕ

/-- Framed Boolean coefficient list and binary half, followed by the binary bit index. -/
enc_structure encCoordinateWord : CoordinateWord where
  point : (encList encBool), half : encNat, bit : encNat

private def decodeCoordinateWord (degree index : ℕ) : CoordinateWord :=
  let coord := decodeIndex degree index
  ⟨BitString.lowBits degree coord.point, coord.half, coord.bit⟩

private theorem decodeCoordinateWord_inSpace :
    ComputableInSpace (fun p : ℕ × ℕ => decodeCoordinateWord p.1 p.2)
      (encPair encNat encNat) encCoordinateWord
      (fun p => p.1 + (encPair encNat encNat p).length) := by
  let encDecoded := encPair encNat encCoordinateNumbers
  let budget (p : ℕ × CoordinateNumbers) := p.1 + (encDecoded p).length
  have hin : (fun p => (encDecoded p).length) ≼ budget := .of_le fun p => by
    change _ ≤ p.1 + _
    omega
  have hd := (fst encNat encCoordinateNumbers).weaken hin
  have hc := (snd encNat encCoordinateNumbers).weaken hin
  have hargs := budget_prod hd (encCoordinateNumbers_point_budget hc)
  have hwidth : (fun p : ℕ × CoordinateNumbers => p.1) ≼ budget := .of_le fun p => by
    change p.1 ≤ p.1 + _
    omega
  have hpoint := budget_comp lowBits_inSpace hargs (hwidth.add hargs.length_le)
  have hword := encCoordinateWord_mk_budget hpoint (encCoordinateNumbers_half_budget hc)
    (encCoordinateNumbers_bit_budget hc)
  have hin : (fun p : ℕ × ℕ => (encPair encNat encNat p).length) ≼
      fun p => p.1 + (encPair encNat encNat p).length := .of_le fun _ => by omega
  have hin' : (fun p : ℕ × ℕ => p.1) ≼
      fun p => p.1 + (encPair encNat encNat p).length := .of_le fun _ => by omega
  have hdecoded := (budget_prod (fst encNat encNat) decodeIndex_inSpace).weaken hin
  exact (budget_comp hword hdecoded (hin'.add hdecoded.length_le)).of_enc_eq fun _ => rfl

private theorem fieldDegree_le_codeLength_size (w n : ℕ) :
    fieldDegree w n ≤ (codeLength w n).size := by
  let b := fieldDegree w n
  have hb : 1 ≤ b := Nat.one_le_iff_ne_zero.2 (fieldDegree_ne_zero w n)
  have hpow : 2 ^ (b - 1) ≤ 2 ^ b - 1 := by
    have hpos : 0 < 2 ^ (b - 1) := by positivity
    have he : 2 ^ b = 2 ^ (b - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel hb]
    omega
  have hlen : 2 ^ (b - 1) ≤ codeLength w n :=
    hpow.trans (by
      change 2 ^ b - 1 ≤ (2 ^ b - 1) * (2 * b)
      simpa only [mul_one] using Nat.mul_le_mul_left (2 ^ b - 1) (show 1 ≤ 2 * b by omega))
  exact Nat.le_of_pred_lt (Nat.lt_size.2 hlen)

private theorem fieldDegree_le_linear :
    (fun p : ℕ × ℕ => fieldDegree p.1 p.2) ≼ fun p => (encDimensions p).length :=
  (BigOLe.of_le fun p => by
    rw [length_encNat_eq_size]
    exact fieldDegree_le_codeLength_size p.1 p.2).trans codeLength_inSpace.length_le

/-- Produce the decoded field point as a little-endian coefficient word. The generator's
degree is bounded by the binary length of its code length, so the complete live state fits
space linear in the binary dimensions and index. -/
theorem decodePointWord_inSpace :
    ComputableInSpace
      (fun (p : (ℕ × ℕ) × ℕ) =>
        BitString.lowBits (fieldDegree p.1.1 p.1.2)
          (decodeIndex (fieldDegree p.1.1 p.1.2) p.2).point)
      (encPair (encPair encNat encNat) encNat) (encList encBool)
      (fun p => (encPair (encPair encNat encNat) encNat p).length) := by
  have hdims := fst (encPair encNat encNat) encNat
  have hdegree := budget_comp_linear fieldDegree_inSpace hdims
  have hindex := snd (encPair encNat encNat) encNat
  have hargs := budget_prod hdegree hindex
  have hdegreeLength :
      (fun p : (ℕ × ℕ) × ℕ => fieldDegree p.1.1 p.1.2) ≼
        fun p => (encPair (encPair encNat encNat) encNat p).length :=
    (fieldDegree_le_linear.comp Prod.fst).trans (.of_le fun p => by
      simp only [encDimensions, length_encPair]
      omega)
  have hcoord := budget_comp decodeCoordinateWord_inSpace hargs
    (hdegreeLength.add hargs.length_le)
  exact (encCoordinateWord_point_budget hcoord).of_enc_eq fun _ => rfl

/-- The parameters shared by coordinate decoding and all field evaluations for a graph. -/
structure FieldContext where
  /-- Degree of the binary field. -/
  degree : ℕ
  /-- Number of outer Reed–Solomon coefficients. -/
  count : ℕ
  /-- Little-endian coefficient word of the field modulus. -/
  modulus : List Bool

/-- Framed binary degree and coefficient count, followed by the raw modulus word. -/
enc_structure encFieldContext : FieldContext where
  degree : encNat, count : encNat, modulus : encBits

/-- Retained field parameters for the existing Justesen generator. -/
def fieldContext (w n : ℕ) : FieldContext :=
  let degree := fieldDegree w n
  ⟨degree, coefficientCount w n, BinaryField.modulusBitsScan degree⟩

/-- The retained context supplies the same degree, coefficient count and modulus as the
table-free generator. -/
theorem fieldContext_eq (w n : ℕ) :
    fieldContext w n =
      ⟨fieldDegree w n, coefficientCount w n, BinaryField.modulusBitsScan (fieldDegree w n)⟩ := by
  rw [fieldContext]

/-- The native initializer uses workspace linear in the encoded binary dimensions.
One capacity run supplies the degree and coefficient count, and the native modulus search
uses workspace linear in that degree. -/
theorem fieldContext_inSpace :
    ComputableInSpace (fun p : ℕ × ℕ => fieldContext p.1 p.2)
      (encPair encNat encNat) encFieldContext (fun p => (encPair encNat encNat p).length) := by
  have hstate := budget_id (BigOLe.refl fun s => (encCapacityState s).length)
  have hselect := budget_prod (encCapacityState_degree_budget hstate)
    (encCapacityState_power_budget hstate)
  have hparams : ComputableInSpace (fun p : ℕ × ℕ => (fieldDegree p.1 p.2,
      coefficientCount p.1 p.2)) encDimensions encDimensions (fun p => (encDimensions p).length) :=
    (budget_comp_linear hselect computed_inSpace).of_enc_eq fun p => by
      obtain ⟨s, hs, hd⟩ := computed_eq_atScale p
      rw [hs, coefficientCount_eq, hd]
      rfl
  let B (p : ℕ × ℕ) := p.1 + (encDimensions p).length
  have hin : (fun p => (encDimensions p).length) ≼ B := .of_le fun p => by
    change _ ≤ p.1 + _
    omega
  have hd := (fst encNat encNat).weaken hin
  have hc := (snd encNat encNat).weaken hin
  have hm := budget_comp Turing.BinaryField.modulusBitsScan_inSpace hd
    (.of_le_linear 1 1 fun p => by
      simp only [one_mul, B]
      omega)
  exact (budget_comp (encFieldContext_mk_budget hd hc hm) hparams
    (fieldDegree_le_linear.add hparams.length_le)).of_enc_eq fun _ => rfl

/-- The prepared modulus stores one bit per coefficient, including the leading term. -/
theorem length_fieldContext_modulus (w n : ℕ) :
    (fieldContext w n).modulus.length = fieldDegree w n + 1 := by
  change (BinaryField.modulusBitsScan (fieldDegree w n)).length = _
  rw [BinaryField.modulusBitsScan_eq, BinaryField.length_modulusBits (fieldDegree_ne_zero w n)]

/-- The prepared field context, including the modulus word, has linear encoded length
in the binary graph dimensions. -/
theorem length_fieldContext_le_encodedDimensions :
    (fun p : ℕ × ℕ => (encFieldContext (fieldContext p.1 p.2)).length) ≼
      fun p => (encPair encNat encNat p).length :=
  fieldContext_inSpace.length_le

/-- Prepare one coordinate from a retained field context. The point width uses the stored
modulus word, as in the field multiplication and Horner routines. -/
def FieldContext.decodeWord (ctx : FieldContext) (index : ℕ) : CoordinateWord :=
  decodeCoordinateWord (ctx.modulus.length - 1) index

/-- The prepared point word and both indexes agree with the existing Justesen coordinate. -/
theorem fieldContext_decodeWord_eq {w n : ℕ} (j : Fin (codeLength w n)) :
    (fieldContext w n).decodeWord j.val =
      let (point, half, bit) := decodeCoordinate w n j
      ⟨List.ofFn (nonzeroPointBits point), half.val, bit.val⟩ := by
  unfold FieldContext.decodeWord
  rw [length_fieldContext_modulus, Nat.add_sub_cancel]
  have hpoint := lowBits_decodeIndex_point j
  have hcoord := decodeIndex_eq_decodeCoordinate j
  unfold decodeCoordinateWord
  dsimp only at hpoint hcoord ⊢
  rw [hpoint, hcoord]

/-- Preparing a point word and its indexes fits space linear in the retained context and binary
index. The stored modulus pays for all coefficients of the point word. -/
theorem fieldContext_decodeWord_inSpace :
    ComputableInSpace (fun p : FieldContext × ℕ => p.1.decodeWord p.2)
      (encPair encFieldContext encNat) encCoordinateWord
      (fun p => (encPair encFieldContext encNat p).length) := by
  have hctx := fst encFieldContext encNat
  have hm := encFieldContext_modulus_budget hctx
  have hwidth := budget_natPred (budget_comp_linear (of_inO ComputableInO.lengthNat) hm)
  have hbound :
      (fun p : FieldContext × ℕ => p.1.modulus.length - 1) ≼
        fun p => (encPair encFieldContext encNat p).length :=
    (BigOLe.of_le fun p : FieldContext × ℕ => Nat.sub_le p.1.modulus.length 1).trans hm.length_le
  have hargs := budget_prod hwidth (snd encFieldContext encNat)
  exact (budget_comp decodeCoordinateWord_inSpace hargs (hbound.add hargs.length_le)).of_enc_eq
    fun _ => rfl

end Cslib.Code.JustesenFamily
