/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarrySave
public import CslibFrontier.Foundations.Data.BitString.Threshold
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.FinCases

/-!
# Exact thresholds from approximate thresholds and a residue

The reconstruction step in [Sergeev2025Symmetric], §2, equation (2), printed p. 10, combines two
approximate comparisons with a modular interval test. The first comparison is false at weights
`w + 2 * t ≤ k` and true at weights `k ≤ w`; the second is false at `w ≤ k` and true at
`k + 2 * t ≤ w`. Values between the respective boundaries are unrestricted. A majority of the
two comparisons and the modular test recovers the exact threshold `k ≤ w` when `4 * t ≤ R`.

The modular test uses the image of the integer interval `[k, k + 2 * t]` modulo `R`. It therefore
works when that interval crosses a multiple of `R`. The lower-zero condition uses `w + 2 * t ≤ k`,
so it also handles `k < 2 * t` without interpreting a negative endpoint as truncated subtraction.

`ThresholdReconstruction.circuit` composes native De Morgan circuits for the three input bits
with the existing five-gate majority formula. The composition costs exactly five additional gates
and at most three additional levels. This is the reconstruction step of Claim 2, not its
Chinese-remainder conversion or the full asymptotic formula bounds; those remain in issue #7708.

## Main definitions

* `Cslib.Circuits.Boolean.ThresholdReconstruction.residueTest`: membership in the modular image of
  the threshold window.
* `Cslib.Circuits.Boolean.ThresholdReconstruction.circuit`: the native majority composition.

## Main results

* `Cslib.Circuits.Boolean.ThresholdReconstruction.maj3_eq_threshold_of_approx`: scalar correctness
  of the reconstruction from the four approximation promises.
* `Cslib.Circuits.Boolean.ThresholdReconstruction.computes_threshold_of_approx`: the composed
  circuit computes the exact threshold on every input.
* `Cslib.Circuits.Boolean.ThresholdReconstruction.size_circuit`,
  `Cslib.Circuits.Boolean.ThresholdReconstruction.depth_circuit_le`: composition costs.

## References

* [I. S. Sergeev, *Economical formulae for symmetric boolean functions*][Sergeev2025Symmetric],
  preprint of 1 May 2025, §2, Claim 2, equation (2), printed pp. 9–10.
-/

public section

namespace Cslib.Circuits.Boolean.ThresholdReconstruction

/-- The weight residue belongs to the image of `[k, k + 2 * t]` modulo `R`. -/
@[expose] def residueTest (k t R w : ℕ) : Bool :=
  decide (w % R ∈ (Finset.Icc k (k + 2 * t)).image (fun j => j % R))

private theorem residueTest_eq_true {k t R w : ℕ} (hlo : k ≤ w) (hhi : w ≤ k + 2 * t) :
    residueTest k t R w = true := by
  simp only [residueTest, decide_eq_true_eq]
  exact Finset.mem_image.mpr ⟨w, Finset.mem_Icc.mpr ⟨hlo, hhi⟩, rfl⟩

private theorem residueTest_eq_false {k t R w : ℕ}
    (hR : 4 * t ≤ R) (hlo : k < w + 2 * t) (hhi : w < k) :
    residueTest k t R w = false := by
  simp only [residueTest, decide_eq_false_iff_not, Finset.mem_image, Finset.mem_Icc]
  rintro ⟨j, ⟨hjlo, hjhi⟩, hmod⟩
  have := (Nat.ModEq.symm hmod).add_le_of_lt (hhi.trans_le hjlo)
  omega

/-- The majority reconstruction step of [Sergeev2025Symmetric], §2, equation (2). It is a
finite composition identity, not the paper's asymptotic depth bound. The approximation promises
are stated only at this weight, and place no conditions on either bit inside its uncertainty
interval. -/
theorem maj3_eq_threshold_of_approx {k t R w : ℕ} (lower upper : Bool)
    (hR : 4 * t ≤ R)
    (hlower_zero : w + 2 * t ≤ k → lower = false)
    (hlower_one : k ≤ w → lower = true)
    (hupper_zero : w ≤ k → upper = false)
    (hupper_one : k + 2 * t ≤ w → upper = true) :
    maj3 lower upper (residueTest k t R w) = decide (k ≤ w) := by
  by_cases hw : k ≤ w
  · by_cases hfar : k + 2 * t ≤ w
    · simp [maj3, hlower_one hw, hupper_one hfar, hw]
    · simp [maj3, hlower_one hw, residueTest_eq_true (t := t) (R := R) hw (by omega), hw]
  · by_cases hfar : w + 2 * t ≤ k
    · simp [maj3, hlower_zero hfar, hupper_zero (not_le.mp hw).le, hw]
    · simp [maj3, hupper_zero (not_le.mp hw).le,
        residueTest_eq_false hR (by omega) (not_le.mp hw), hw]

variable {n : ℕ}

/-- Run the two approximate comparisons and the residue test, then take their majority.
All three component circuits run on the same `n` input bits. -/
@[expose] def circuit (lower upper residue : Circuit signature n 1) : Circuit signature n 1 :=
  (maj3Formula (0 : Fin 3) 1 2).toCircuit.comp (Circuit.pi ![lower, upper, residue])

/-- The reconstruction circuit takes the majority of the three component outputs. -/
@[simp] theorem eval_circuit (lower upper residue : Circuit signature n 1) (x : BitString n)
    (o : Fin 1) :
    (circuit lower upper residue).eval interpretation x o =
      maj3 (lower.eval interpretation x 0) (upper.eval interpretation x 0)
        (residue.eval interpretation x 0) := by
  simp [circuit, Formula.eval_toCircuit, eval_maj3Formula]

/-- Reconstruction adds exactly five De Morgan gates to the three component circuits. -/
@[simp] theorem size_circuit (lower upper residue : Circuit signature n 1) :
    (circuit lower upper residue).size = lower.size + upper.size + residue.size + 5 := by
  simp [circuit, size_maj3Formula, Fin.sum_univ_succ, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc]

/-- Reconstruction adds at most three levels to the largest component depth. -/
theorem depth_circuit_le (lower upper residue : Circuit signature n 1) :
    (circuit lower upper residue).depth ≤ max (max lower.depth upper.depth) residue.depth + 3 := by
  have hmajority : (maj3Formula (0 : Fin 3) 1 2).toCircuit.depth ≤ 3 :=
    (Formula.depth_toCircuit_le _).trans (depth_maj3Formula_le _ _ _)
  have hparallel : (Circuit.pi ![lower, upper, residue]).depth ≤
      max (max lower.depth upper.depth) residue.depth :=
    Circuit.depth_pi_le _ fun i => by fin_cases i <;> dsimp <;> omega
  exact (Circuit.depth_comp_le _ _).trans (by omega)

/-- Correctness of the native reconstruction step. The supplied circuits may behave arbitrarily
inside their uncertainty intervals; the resulting circuit computes the total exact threshold.
The residue circuit must compute the modular interval test, including wraparound. This is the
finite composition step of Claim 2, not construction of its three prerequisite circuits. -/
theorem computes_threshold_of_approx (lower upper residue : Circuit signature n 1)
    {k t R : ℕ} (hR : 4 * t ≤ R)
    (hlower_zero : ∀ x, BitString.weight x + 2 * t ≤ k → lower.eval interpretation x 0 = false)
    (hlower_one : ∀ x, k ≤ BitString.weight x → lower.eval interpretation x 0 = true)
    (hupper_zero : ∀ x, BitString.weight x ≤ k → upper.eval interpretation x 0 = false)
    (hupper_one : ∀ x, k + 2 * t ≤ BitString.weight x → upper.eval interpretation x 0 = true)
    (hresidue : ∀ x, residue.eval interpretation x 0 = residueTest k t R (BitString.weight x)) :
    (circuit lower upper residue).Computes interpretation (single (threshold n k)) := by
  intro x
  funext o
  rw [eval_circuit, hresidue]
  exact maj3_eq_threshold_of_approx _ _ hR (hlower_zero x) (hlower_one x)
    (hupper_zero x) (hupper_one x)

end Cslib.Circuits.Boolean.ThresholdReconstruction
