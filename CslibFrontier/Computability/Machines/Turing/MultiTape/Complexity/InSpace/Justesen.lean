/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import CslibFrontier.Foundations.Data.Code.JustesenFamily
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Foundations.Data.Nat.BinarySize

/-!
# Justesen field degree and seed length in native space

The input consists of the binary width and horizon of a layered graph. Starting at degree
sixteen, a counted loop raises the degree by sixteen and multiplies the retained power of two
by a fixed factor, holding the state once the capacity suffices. The final degree and
power give the field degree and exact seed length of the existing Justesen generator. Native
space is linear in the encoded dimensions, including every live loop state.
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

private theorem length_threshold_le (p : ℕ × ℕ) :
    threshold p ≤ 512 * ((encDimensions p).length + 1) := by
  have hm := Nat.size_mul_le p.1 (p.2 + 1)
  have hsucc := Nat.size_add_le_max p.2 1
  change (p.2 + 1).size ≤ max p.2.size 1 + 1 at hsucc
  simp only [threshold, Nat.log2_eq_size_sub_one, encDimensions, length_encPair,
    length_encNat_eq_size]
  omega

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

end Cslib.Code.JustesenFamily
