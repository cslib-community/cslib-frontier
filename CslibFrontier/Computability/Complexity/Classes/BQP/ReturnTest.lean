/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Uniform
import CslibFrontier.Computability.Circuit.Quantum.PhaseOracle
import CslibFrontier.Computability.Complexity.Classes.BQP.Amplification
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Measuring the return probability of a uniform circuit

A CNOT layer saves the initial register, including its zero padding. After the circuit runs,
the same layer adds its final register to the saved copy. A reversible zero test detects whether
all the differences vanish. The resulting uniform circuit accepts with probability equal to the
squared norm of the diagonal entry at the input basis state.

## Main definitions

* `Cslib.Quantum.UniformCircuitFamily.returnTest` tests return to the entire padded input register.

## Main results

* `Cslib.Quantum.UniformCircuitFamily.acceptProb_returnTest` gives its acceptance probability.
-/

public section

namespace Cslib.Quantum

open Finset GateCode Turing.MultiTapeTM

namespace ReturnTest

private abbrev width (w : ℕ) := 3 * w + 1

private abbrev copyBits (w : ℕ) := Amplify.copyCodes w w 1

private theorem copy_fits (w : ℕ) : Amplify.base w 1 ≤ width w := by
  simp [Amplify.base, width]; omega

private theorem classical_copy (w : ℕ) : IsClassical (width w) (copyBits w) :=
  Amplify.isClassical_copyCodes le_rfl (copy_fits w)

private theorem copy_at (w : ℕ) (X : Fin (width w) → Bool) {i : ℕ} (hi : i < w) :
    readBit (classicalRun (copyBits w) X) (i + w) = (readBit X (i + w) ^^ readBit X i) := by
  rw [Amplify.readBit_classicalRun_copyCodes le_rfl (copy_fits w), ite_eq_left]
  · simp [Nat.mod_eq_of_lt hi]
  · exact ⟨0, Nat.zero_lt_one, i, hi, by simp⟩

private theorem copy_off (w : ℕ) (X : Fin (width w) → Bool) {i : ℕ}
    (hi : i < w ∨ 2 * w ≤ i) :
    readBit (classicalRun (copyBits w) X) i = readBit X i := by
  rw [Amplify.readBit_classicalRun_copyCodes le_rfl (copy_fits w), ite_eq_right]
  rintro ⟨j, hj, b, hb, rfl⟩
  have : j = 0 := by omega
  subst j
  simp only [zero_add, one_mul] at hi
  omega

private abbrev savedWires (w : ℕ) := (List.range w).map (fun i => i + w)

private theorem savedWires_lt {c w : ℕ} (hc : c ∈ savedWires w) : c < 2 * w := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
  have := List.mem_range.mp hi
  omega

private abbrev suffix (w : ℕ) : List GateCode :=
  copyBits w ++ (zeroTestCodes (savedWires w) (2 * w) ++ swapCodes (2 * w))

private theorem classical_suffix {w : ℕ} (hw : 0 < w) : IsClassical (width w) (suffix w) :=
  IsClassical.append.mpr ⟨classical_copy w, IsClassical.append.mpr
    ⟨isClassical_zeroTestCodes (fun _ => savedWires_lt)
      (by simp [savedWires, width]; omega),
      isClassical_swapCodes (by omega) (by unfold width; omega)⟩⟩

private theorem accepts_suffix {w : ℕ} (hw : 0 < w) (Y : Fin (width w) → Bool)
    (hY : ∀ i, 2 * w ≤ i → readBit Y i = false) :
    classicalRun (suffix w) Y ∈ accepting (width w) ↔
      ∀ i < w, readBit Y (i + w) = readBit Y i := by
  have h0 : 0 < width w := by simp [width]
  rw [mem_accepting h0, ← readBit_fin (classicalRun (suffix w) Y) (⟨0, h0⟩ : Fin (width w)),
    suffix, classicalRun_append, classicalRun_append, readBit_classicalRun_swapCodes (by omega)
      (by unfold width; omega), readBit_classicalRun_zeroTestCodes]
  · simp only [savedWires, List.all_map, Function.comp_apply, List.all_eq_true, List.mem_range,
      Bool.not_eq_true']
    exact forall_congr' fun i => forall_congr' fun hi => (copy_at w Y hi) ▸ bne_eq_false_iff_eq
  · exact List.nodup_range.map (by intro a b h; exact Nat.add_right_cancel h)
  · exact fun _ => savedWires_lt
  · simp [savedWires, width]; omega
  · exact fun i hi _ => (copy_off w Y (.inr hi)).trans (hY i hi)

private abbrev codes (w : ℕ) (gs : List GateCode) : List GateCode :=
  copyBits w ++ (gs ++ suffix w)

private theorem wellFormed_codes {w : ℕ} (hw : 0 < w) {gs : List GateCode}
    (hgs : ∀ g ∈ gs, WellFormed w g) : ∀ g ∈ codes w gs, WellFormed (width w) g := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact (classical_copy w g h).2
  rcases List.mem_append.mp h with h | h
  · simpa only [GateCode.shift_zero] using (hgs g h).shift (o := 0) (N := width w)
      (by unfold width; omega)
  · exact (classical_suffix hw g h).2

private theorem uniform_codes (F : UniformCircuitFamily) :
    ComputableInPolyTime (fun n => codes (F.width n) (F.gates n)) encUnary
      (encList encGateCode) := by
  have hw := F.computableInPolyTime_width
  have hg := F.computableInPolyTime_gates
  have hcopy := Amplify.computableInPolyTime_copyCodes hw hw
    (ComputableInPolyTime.const 1 (encIn := encUnary) (encOut := encUnary))
  have hswap : ComputableInPolyTime (fun n => swapCodes (2 * F.width n)) encUnary
      (encList encGateCode) := by
    simp only [swapCodes, swapWireCodes]
    fun_prop
  simp only [codes, suffix, copyBits, savedWires]
  fun_prop

private theorem acceptProb_codes {w : ℕ} (hw : 0 < w) {gs : List GateCode}
    (hgs : ∀ g ∈ gs, WellFormed w g) {x : List Bool} (hx : x.length ≤ w) :
    acceptProb (width w) (codes w gs) x =
      ‖(Circuit.run (Circuit.ofCodes w gs) (inputState w x)).ofLp (inputState w x)‖ ^ 2 := by
  classical
  let N := width w
  have hN : 0 + w ≤ N := by dsimp [N, width]; omega
  let e := blockEmb 0 hN
  let X := classicalRun (copyBits w) (inputState N x)
  have hXlo (i : ℕ) (hi : i < w) :
      readBit X i = x.getD i false :=
    (copy_off w _ (.inl hi)).trans (readBit_inputState (by dsimp [N, width]; omega) i)
  have hXcopy (i : ℕ) (hi : i < w) : readBit X (i + w) = readBit X i := by
    rw [show readBit X (i + w) = _ from copy_at w _ hi, copy_off w _ (.inl hi),
      readBit_inputState_of_le (by omega : x.length ≤ i + w), Bool.false_xor]
  have hXhigh (i : ℕ) (hi : 2 * w ≤ i) : readBit X i = false :=
    (copy_off w _ (.inr hi)).trans (readBit_inputState_of_le (by omega))
  have hxblock : X ∘ e = inputState w x := by
    funext i
    change X (e i) = x.getD i.val false
    rw [← readBit_fin X (e i)]
    simpa only [e, blockEmb_apply_val, Nat.add_zero] using hXlo i i.isLt
  have hacc (Y : Fin N → Bool) (hY : AgreeOff e Y X) :
      classicalRun (suffix w) Y ∈ accepting N ↔ Y = X := by
    have hsame (i : ℕ) (hi : w ≤ i) : readBit Y i = readBit X i := by
      by_cases h : i < N
      · rw [readBit_of_lt Y h, readBit_of_lt X h]
        apply hY
        intro j he
        have : j.val + 0 = i := congrArg Fin.val he
        omega
      · rw [readBit_of_le Y (by omega), readBit_of_le X (by omega)]
    rw [accepts_suffix hw Y (fun i hi => (hsame i (by omega)).trans (hXhigh i hi))]
    constructor
    · intro heq
      apply funext_readBit
      intro i
      by_cases hi : i < w
      · rw [← heq i hi, hsame (i + w) (by omega), hXcopy i hi]
      · exact hsame i (by omega)
    · rintro rfl
      exact hXcopy
  have hcircuit : Circuit.ofCodes N gs = (Circuit.ofCodes w gs).mapWires e := by
    simpa only [show shift 0 = id from funext shift_zero, List.map_id] using
      Circuit.ofCodes_map_shift hN hgs
  unfold Quantum.acceptProb
  rw [codes, Circuit.ofCodes_append, Circuit.ofCodes_append, Circuit.run, Circuit.eval_append,
    Circuit.eval_append, Circuit.eval_ofCodes_ket (classical_copy w),
    Circuit.measureProb_eval_ofCodes (classical_suffix hw)]
  change (∑ Y, if classicalRun (suffix w) Y ∈ accepting N then
    ‖(Circuit.eval (Circuit.ofCodes N gs) (ket X)).ofLp Y‖ ^ 2 else 0) = _
  rw [Finset.sum_eq_single X]
  · rw [ite_eq_left ((hacc X (.refl e X)).2 rfl), Circuit.eval_ket_apply, hcircuit,
      Circuit.matrix_mapWires, ite_eq_left (AgreeOff.refl e X), hxblock, Circuit.run,
      Circuit.eval_ket_apply]
  · intro Y _ hne
    by_cases ho : AgreeOff e Y X
    · rw [ite_eq_right (fun h => hne ((hacc Y ho).1 h))]
    · rw [Circuit.eval_ket_apply, hcircuit, Circuit.matrix_mapWires, ite_eq_right ho]
      simp
  · simp

end ReturnTest

namespace UniformCircuitFamily

/-- The uniform circuit family that accepts exactly the mass of the initial basis state
after running the original circuit. -/
def returnTest (F : UniformCircuitFamily) : UniformCircuitFamily where
  width n := ReturnTest.width (F.width n)
  gates n := ReturnTest.codes (F.width n) (F.gates n)
  computableInPolyTime_width := by
    have := F.computableInPolyTime_width
    unfold ReturnTest.width
    fun_prop
  computableInPolyTime_gates := ReturnTest.uniform_codes F
  le_width n := by have := F.le_width n; unfold ReturnTest.width; omega
  width_pos n := by simp [ReturnTest.width]
  wellFormed n := ReturnTest.wellFormed_codes (F.width_pos n) (F.wellFormed n)

/-- Measuring the designated output of the return test gives the squared norm of the
diagonal matrix entry indexed by the padded input. -/
theorem acceptProb_returnTest (F : UniformCircuitFamily) (x : List Bool) :
    F.returnTest.acceptProb x =
      ‖(Circuit.run (Circuit.ofCodes (F.width x.length) (F.gates x.length))
        (inputState _ x)).ofLp (inputState _ x)‖ ^ 2 :=
  ReturnTest.acceptProb_codes (F.width_pos _) (F.wellFormed _) (F.le_width _)

end UniformCircuitFamily
end Cslib.Quantum
