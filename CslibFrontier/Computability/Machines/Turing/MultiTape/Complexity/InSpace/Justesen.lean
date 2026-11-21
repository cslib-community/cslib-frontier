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
capacity run supplies the degree and coefficient count for a retained field context.
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
  exact (budget_natMul (budget_const 512 (.refl _))
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
    encCapacityState_mk_budget ht (budget_natAdd hd (budget_const 16 (.refl _)))
      (budget_natMul hp (budget_const 65536 (.refl _)))
  exact (budget_ite (budget_natLt (budget_natMul hp hd) ht) hnext h).of_enc_eq fun s => by
    simp only [advance, decide_eq_true_eq]

private theorem computed_inSpace :
    ComputableInSpace computed encDimensions encCapacityState
      (fun p => (encDimensions p).length) := by
  let : Inhabited CapacityState := ⟨atScale 0 0⟩
  exact budget_iterate threshold_inSpace
    (encCapacityState_mk_budget threshold_inSpace (budget_const 16 (.refl _))
      (budget_const 32768 (.refl _))) advance_inSpace
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
  have htwo := budget_const (encB := encNat) 2 hin
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
  have hblock := budget_natMul (budget_const 2 (.refl _)) hdegree
  have hwithin := budget_natMod hindex hblock
  exact encCoordinateNumbers_mk_budget (budget_natSucc (budget_natDiv hindex hblock))
    (budget_natDiv hwithin hdegree) (budget_natMod hwithin hdegree)

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
  have hnum := budget_comp_linear decodeIndex_inSpace (budget_prod hdegree hindex)
  have hargs := budget_prod hdegree (encCoordinateNumbers_point_budget hnum)
  have hdegreeLength :
      (fun p : (ℕ × ℕ) × ℕ => fieldDegree p.1.1 p.1.2) ≼
        fun p => (encPair (encPair encNat encNat) encNat p).length :=
    (fieldDegree_le_linear.comp Prod.fst).trans (.of_le fun p => by
      simp only [encDimensions, length_encPair]
      omega)
  exact budget_comp lowBits_inSpace hargs (hdegreeLength.add hargs.length_le)

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

/-- Initialize the retained degree, coefficient count and modulus from the binary graph
dimensions. The degree and count come from one capacity run. A modulus routine with space
linear in the degree fits the same encoded-dimension budget. -/
theorem fieldContext_inSpace_of_modulus
    (hmodulus : ComputableInSpace BinaryField.modulusBitsScan encNat encBits (fun d => d + 1)) :
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
  have hm := budget_comp hmodulus hd (.of_le_linear 1 1 fun p => by
    simp only [one_mul, B]
    omega)
  exact (budget_comp (encFieldContext_mk_budget hd hc hm) hparams
    (fieldDegree_le_linear.add hparams.length_le)).of_enc_eq fun _ => rfl

end Cslib.Code.JustesenFamily
