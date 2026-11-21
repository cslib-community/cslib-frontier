/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.MinIsolation.Weights
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Foundations.Data.Nat.BinarySize
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Native layer scaling for Hoza's weights

Once a caller has accumulated the masked seed digits, each factor of two in the layer
contributes one factor of six to the weight. A counted halving loop certifies the exact
scaling function in space linear in the binary layer and accumulator. The complete live
state fits this bound at every iteration.
-/

public section

namespace Cslib.Reachability.Hoza

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

private structure ScaleState where
  remaining : ℕ
  value : ℕ

private enc_structure encScaleState : ScaleState where
  remaining : encNat, value : encNat

private abbrev encArguments : ℕ × ℕ ↪ List Bool := encPair encNat encNat

private def advance (s : ScaleState) : ScaleState :=
  if s.remaining ≠ 0 ∧ 2 ∣ s.remaining then
    ⟨s.remaining / 2, 6 * s.value⟩
  else s

private theorem advance_spec (s : ScaleState) :
    (advance s).remaining ≤ s.remaining ∧
      multiplicity 2 (advance s).remaining = multiplicity 2 s.remaining - 1 ∧
      scaleAccumulatedWeight (advance s).remaining (advance s).value =
        scaleAccumulatedWeight s.remaining s.value := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [advance]
  split_ifs with h
  · have hdiv := Nat.multiplicity_div h.2
    have hpos := one_le_multiplicity_of_dvd h.1 h.2
    refine ⟨Nat.div_le_self _ _, hdiv, ?_⟩
    simp only [scaleAccumulatedWeight, Nat.padicValNat_def, hdiv, ← mul_assoc, ← pow_succ,
      Nat.sub_add_cancel hpos]
  · have hzero : multiplicity 2 s.remaining = 0 := by
      rw [Nat.multiplicity_eq_zero_iff]
      by_cases hz : s.remaining = 0
      · exact Or.inr (Or.inl hz)
      · exact Or.inr (Or.inr fun hd => h ⟨hz, hd⟩)
    exact ⟨le_rfl, by simp [hzero], rfl⟩

private def run (p : ℕ × ℕ) (j : ℕ) : ScaleState :=
  advance^[j] ⟨p.1, p.2⟩

private theorem run_spec (p : ℕ × ℕ) (j : ℕ) :
    (run p j).remaining ≤ p.1 ∧
      multiplicity 2 (run p j).remaining = multiplicity 2 p.1 - j ∧
      scaleAccumulatedWeight (run p j).remaining (run p j).value =
        scaleAccumulatedWeight p.1 p.2 := by
  induction j with
  | zero => exact ⟨le_rfl, (Nat.sub_zero _).symm, rfl⟩
  | succ j ih =>
    have hstep : run p (j + 1) = advance (run p j) := by
      simp only [run, Function.iterate_succ_apply']
    rw [hstep]
    obtain ⟨hle, hval, hweight⟩ := advance_spec (run p j)
    exact ⟨hle.trans ih.1, by rw [hval, ih.2.1, Nat.sub_sub], hweight.trans ih.2.2⟩

private theorem multiplicity_le_size (layer : ℕ) :
    multiplicity 2 layer ≤ layer.size := by
  have h := multiplicity_le_nat_log (p := 2) layer
  rw [← Nat.log2_eq_log_two] at h
  exact h.trans (Nat.log2_le_size layer)

private theorem length_run_le (p : ℕ × ℕ) (j : ℕ) :
    (encScaleState (run p j)).length ≤ 3 * ((encArguments p).length + 1) := by
  obtain ⟨hrem, -, hweight⟩ := run_spec p j
  have hv : (run p j).value ≤ scaleAccumulatedWeight p.1 p.2 := by
    rw [← hweight]
    exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))
  have hremSize := Nat.size_le_size hrem
  have hvalueSize := Nat.size_le_size hv
  have hpow := Nat.size_pow_le 6 (multiplicity 2 p.1)
  have hmul := Nat.size_mul_le (6 ^ multiplicity 2 p.1) p.2
  have hval := multiplicity_le_size p.1
  simp only [scaleAccumulatedWeight, Nat.padicValNat_def] at hvalueSize
  change (6 ^ multiplicity 2 p.1).size ≤ multiplicity 2 p.1 * 3 + 1 at hpow
  simp only [encScaleState_apply, encScaleStateFields, encArguments, length_encPair,
    length_encNat_eq_size]
  omega

private theorem advance_inSpace :
    ComputableInSpace advance encScaleState encScaleState (fun s => (encScaleState s).length) := by
  have hin := BigOLe.refl fun s => (encScaleState s).length
  have hid := budget_id hin
  have hrem := encScaleState_remaining_budget hid
  have hv := encScaleState_value_budget hid
  have htwo := budget_const (encB := encNat) 2 hin
  have hcond := budget_boolAnd (budget_boolNot (budget_natIsZero hrem))
    (budget_natIsZero (budget_natMod hrem htwo))
  have hnext := encScaleState_mk_budget (budget_natDiv hrem htwo)
    (budget_natMul (budget_const 6 hin) hv)
  exact (budget_ite hcond hnext hid).of_enc_eq fun s => by
    simp [advance, Nat.dvd_iff_mod_eq_zero]

/-- Compute the exact layer scaling in space linear in the binary layer and accumulator. -/
theorem scaleAccumulatedWeight_inSpace :
    ComputableInSpace (fun p : ℕ × ℕ => scaleAccumulatedWeight p.1 p.2)
      (encPair encNat encNat) encNat (fun p => (encPair encNat encNat p).length) := by
  let : Inhabited ScaleState := ⟨⟨0, 0⟩⟩
  have hsize := budget_comp_linear natSize (fst encNat encNat)
  have hinit := encScaleState_mk_budget (fst encNat encNat) (snd encNat encNat)
  have hrun : ComputableInSpace (fun p => run p p.1.size) encArguments encScaleState
      (fun p => (encArguments p).length) :=
    budget_iterate hsize hinit advance_inSpace (fun p j _ => length_run_le p j)
      (.of_le_linear 3 3 fun _ => by omega)
  refine (encScaleState_value_budget hrun).of_enc_eq fun p => congrArg encNat ?_
  obtain ⟨-, hval, hweight⟩ := run_spec p p.1.size
  rw [Nat.sub_eq_zero_of_le (multiplicity_le_size p.1)] at hval
  simpa only [scaleAccumulatedWeight, Nat.padicValNat_def, hval, pow_zero, one_mul]
    using hweight.symm

end Cslib.Reachability.Hoza
