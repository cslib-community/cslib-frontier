/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Classical
public import CslibFrontier.Computability.Circuit.Quantum.PathSum
public import CslibFrontier.Foundations.Data.BitString.List.Positions
import CslibFrontier.Foundations.Data.List.EraseDupsBy
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Probability.PMF.Map

/-!
# Quantum output support on target wires

Hadamard, NOT, CNOT and Toffoli gates change only their target bit along each computational
path. Every wire never targeted by a circuit therefore retains its computational-basis input
bit on the support of the final measurement. The number of distinct target wires is at most
the number of gates; a wire used only as a control does not need to be sampled.

Reading the measurement on any list covering the target wires and restoring all other bits
from the explicit input register recovers the complete joint output distribution. This identity
includes circuits with no gates, registers of width zero, and registers with arbitrarily many
untargeted wires.

## Main definitions

* `Cslib.Quantum.GateCode.targets`: distinct target wires in order of first occurrence.

## Main results

* `Cslib.Quantum.GateCode.targets_length_le`: at most one distinct target per gate.
* `Cslib.Quantum.getD_pathRun_of_not_mem_targets`: paths preserve untargeted input bits.
* `Cslib.Quantum.run_ofCodes_apply_eq_zero_of_not_mem_targets`: an amplitude vanishes when an
  untargeted output bit differs from its input bit.
* `Cslib.Quantum.eq_of_mem_support_measure_of_not_mem_targets`: measurement support preserves
  untargeted bits.
* `Cslib.Quantum.measure_map_restorePositions`: target marginals reconstruct the full output law.
-/

public section

namespace Cslib.Quantum

open Probability

variable {m : ℕ}

namespace GateCode

/-- Distinct target wires, in order of their first occurrence in the circuit. -/
@[expose] def targets (gs : List GateCode) : List ℕ :=
  (gs.map target).eraseDupsBy fun a b => decide (a = b)

/-- A circuit's target list has no duplicates. -/
theorem targets_nodup (gs : List GateCode) : (targets gs).Nodup :=
  List.nodup_eraseDupsBy_eq _

/-- There are at most as many distinct target wires as gates. -/
theorem targets_length_le (gs : List GateCode) : (targets gs).length ≤ gs.length := by
  exact (List.eraseDupsBy_sublist (r := fun a b : ℕ => decide (a = b))
    (gs.map target)).length_le.trans_eq (List.length_map ..)

/-- A wire occurs in the target list exactly when some gate targets it. -/
@[simp] theorem mem_targets_iff {gs : List GateCode} {j : ℕ} :
    j ∈ targets gs ↔ ∃ g ∈ gs, target g = j := by
  simp only [targets, List.mem_eraseDupsBy_eq, List.mem_map]

/-- Every gate's target belongs to the target list of its circuit. -/
theorem target_mem_targets {gs : List GateCode} {g : GateCode} (hg : g ∈ gs) :
    target g ∈ targets gs :=
  mem_targets_iff.mpr ⟨g, hg, rfl⟩

/-- Every target of a well-formed circuit is a valid register position. -/
theorem lt_of_mem_targets {gs : List GateCode} (hgs : ∀ g ∈ gs, g.WellFormed m)
    {j : ℕ} (hj : j ∈ targets gs) : j < m := by
  obtain ⟨⟨b, t, cs⟩, hg, rfl⟩ := mem_targets_iff.mp hj
  cases b
  · exact (hgs _ hg).2.2 t List.mem_cons_self
  · exact (hgs _ hg).1

end GateCode

private theorem getD_foldl_pathStep_of_forall_ne (gs : List GateCode) (j : ℕ)
    (s path : List Bool) (sign : Bool) (havoid : ∀ g ∈ gs, GateCode.target g ≠ j) :
    (gs.foldl pathStep (s, path, sign)).1.getD j false = s.getD j false := by
  induction gs generalizing s path sign with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨b, t, cs⟩ := g
    have hg : t ≠ j := havoid _ List.mem_cons_self
    cases b <;> simp only [List.foldl_cons, pathStep] <;>
      rw [ih _ _ _ (fun g hg => havoid g (List.mem_cons_of_mem _ hg)), List.getD_set_ne hg]

/-- A path preserves every input bit that no gate targets, for arbitrary path words and codes. -/
theorem getD_pathRun_of_not_mem_targets (gs : List GateCode) (x path : List Bool) (j : ℕ)
    (hj : j ∉ GateCode.targets gs) :
    (pathRun gs x path).1.getD j false = x.getD j false := by
  exact getD_foldl_pathStep_of_forall_ne gs j x path false
    fun g hg heq => hj (GateCode.mem_targets_iff.mpr ⟨g, hg, heq⟩)

/-- A path contributes zero to an output that disagrees with an untargeted input bit. -/
theorem pathTerm_eq_zero_of_not_mem_targets (gs : List GateCode) (x y path : List Bool)
    (j : ℕ) (hj : j ∉ GateCode.targets gs) (hne : y.getD j false ≠ x.getD j false) :
    pathTerm gs x y path = 0 := by
  change (if (pathRun gs x path).1 = y then (if (pathRun gs x path).2 then -1 else 1) else 0) = 0
  exact ite_eq_right_iff.mpr fun heq =>
    absurd (heq ▸ getD_pathRun_of_not_mem_targets gs x path j hj) hne

/-- An amplitude is zero when an untargeted output wire differs from the input basis state. -/
theorem run_ofCodes_apply_eq_zero_of_not_mem_targets {gs : List GateCode}
    (hgs : ∀ g ∈ gs, g.WellFormed m) (x y : Fin m → Bool) (j : Fin m)
    (hj : j.val ∉ GateCode.targets gs) (hne : y j ≠ x j) :
    (Circuit.run (Circuit.ofCodes m gs) x).ofLp y = 0 := by
  have hgap : pathGap gs (List.ofFn x) (List.ofFn y) = 0 :=
    Finset.sum_eq_zero fun path _ => pathTerm_eq_zero_of_not_mem_targets gs _ _ _ j.val hj
      (by simpa only [List.getD_ofFn] using hne)
  simp [run_ofCodes_apply gs hgs, hgap]

/-- Every supported measurement outcome agrees with the input at an untargeted wire. -/
theorem eq_of_mem_support_measure_of_not_mem_targets {gs : List GateCode}
    (hgs : ∀ g ∈ gs, g.WellFormed m) {x y : Fin m → Bool}
    (hy : y ∈ (Circuit.measure (Circuit.ofCodes m gs) x).support) (j : Fin m)
    (hj : j.val ∉ GateCode.targets gs) : y j = x j := by
  by_contra hne
  exact hy (by simp [Circuit.measure_apply,
    run_ofCodes_apply_eq_zero_of_not_mem_targets hgs x y j hj hne])

/-- Reading any positions covering all gate targets and restoring the remaining input bits
recovers the entire joint measurement law as a list. The input register is explicitly supplied. -/
theorem measure_map_restorePositions {gs : List GateCode} (X : List Bool)
    (hgs : ∀ g ∈ gs, g.WellFormed X.length) (positions : List ℕ)
    (hcover : GateCode.targets gs ⊆ positions) :
    (((Circuit.measure (Circuit.ofCodes X.length gs) (inputState X.length X)).map
      (fun y => positions.map (readBit y))).map (BitString.restorePositions positions X)) =
      (Circuit.measure (Circuit.ofCodes X.length gs) (inputState X.length X)).map List.ofFn := by
  rw [PMF.map_comp]
  apply PMF.map_congr_on_support
  intro y hy
  refine BitString.restorePositions_readPositions positions X (List.ofFn y) (by simp)
    fun j hj hnot => ?_
  rw [List.getD_ofFn_of_lt _ hj false]
  exact eq_of_mem_support_measure_of_not_mem_targets hgs hy ⟨j, hj⟩ (mt (hcover ·) hnot)

end Cslib.Quantum
