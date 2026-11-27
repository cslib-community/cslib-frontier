/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Uniform
import CslibFrontier.Computability.Complexity.Classes.BQP.Amplification
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Measuring the return probability of a uniform circuit

A CNOT layer saves the initial register, including its zero padding. After the circuit runs,
the same layer adds its final register to the saved copy. A reversible counter detects whether
all the differences vanish. The resulting uniform circuit accepts with probability equal to the
squared norm of the diagonal entry at the input basis state.
-/

public section

namespace Cslib.Quantum

open Finset GateCode Turing.MultiTapeTM

namespace ReturnTest

private abbrev width (w : ℕ) := 3 * w + 2

private abbrev copyBits (w : ℕ) := Amplify.copyCodes w w 1

private theorem copyBits_eq (w : ℕ) :
    copyBits w = (List.range w).map fun i => ((false, i + w, [i]) : GateCode) := by
  simp [copyBits, Amplify.copyCodes, List.range_one]

private theorem classical_copy (w : ℕ) : IsClassical (width w) (copyBits w) := by
  intro g hg
  rw [copyBits_eq] at hg
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
  have hi' := List.mem_range.mp hi
  simp [WellFormed, width]; omega

private theorem copy_at (w : ℕ) (X : Fin (width w) → Bool) {i : ℕ} (hi : i < w) :
    readBit (classicalRun (copyBits w) X) (i + w) =
      (readBit X (i + w) ^^ readBit X i) := by
  rw [copyBits_eq]
  let gs := (List.range w).map fun j => ((false, j + w, [j]) : GateCode)
  have hmem : ((false, i + w, [i]) : GateCode) ∈ gs :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  have hlt : ∀ g ∈ gs, target g < width w := by
    rintro _ hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
    have := List.mem_range.mp hj
    dsimp only [target, width]
    omega
  have hnd : (gs.map target).Nodup := by
    change (((List.range w).map fun j => ((false, j + w, [j]) : GateCode)).map target).Nodup
    rw [List.map_map]
    exact List.nodup_range.map (f := fun j => j + w) (by intro a b h; exact Nat.add_right_cancel h)
  have hread : ∀ g ∈ gs, ∀ g' ∈ gs, target g ∉ controls g' := by
    rintro _ hg _ hg'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
    obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hg'
    have := List.mem_range.mp hj'
    simp only [target, controls, List.mem_singleton]
    omega
  simpa using readBit_classicalRun_of_mem hlt hnd hread X hmem

private theorem copy_off (w : ℕ) (X : Fin (width w) → Bool) {i : ℕ}
    (hi : i < w ∨ 2 * w ≤ i) :
    readBit (classicalRun (copyBits w) X) i = readBit X i := by
  apply readBit_classicalRun_of_forall_ne
  intro g hg
  rw [copyBits_eq] at hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
  have := List.mem_range.mp hj
  dsimp only [target]
  omega

private abbrev counter (w : ℕ) :=
  Counter.codes (2 * w) 1 (fun j => j + w) w

private abbrev answer (w : ℕ) := Counter.level (2 * w) 1 w 0

private abbrev suffix (w : ℕ) : List GateCode :=
  copyBits w ++ (counter w ++ (swapCodes (answer w) ++ [(false, 0, [])]))

private theorem classical_suffix (w : ℕ) : IsClassical (width w) (suffix w) := by
  have hcounter : IsClassical (width w) (counter w) :=
    Counter.isClassical_codes (by intro s hs; omega) (by simp [width]; omega)
  have haswap : IsClassical (width w) (swapCodes (answer w)) :=
    isClassical_swapCodes (by simp [answer, Counter.level])
      (by simp [answer, width, Counter.level]; omega)
  exact IsClassical.append.mpr ⟨classical_copy w, IsClassical.append.mpr ⟨hcounter,
    IsClassical.append.mpr ⟨haswap, fun g hg => by
      simp only [List.mem_singleton] at hg
      subst g
      simp [WellFormed, width]⟩⟩⟩

private theorem accepts_suffix (w : ℕ) (Y : Fin (width w) → Bool)
    (hY : ∀ i, 2 * w ≤ i → readBit Y i = false) :
    classicalRun (suffix w) Y ∈ accepting (width w) ↔
      ∀ i < w, readBit Y (i + w) = readBit Y i := by
  let Z := classicalRun (copyBits w) Y
  have hZ (i : ℕ) (hi : 2 * w ≤ i) : readBit Z i = false :=
    (copy_off w Y (.inr hi)).trans (hY i hi)
  have hc := (Counter.readBit_classicalRun_codes (base := 2 * w) (T := 1) (k := w)
    (src := fun j => j + w) (by intro j hj; omega) (by simp [width]; omega) Z hZ).2 0 (by omega)
  have h0 : 0 < width w := by simp [width]
  rw [mem_accepting h0, ← readBit_fin (classicalRun (suffix w) Y) (⟨0, h0⟩ : Fin (width w))]
  simp only [suffix, classicalRun_append, classicalRun_cons, classicalRun_nil]
  change readBit (classicalStep _ _) 0 = true ↔ _
  rw [readBit_classicalStep]
  simp only [target, controls, and_self, h0, decide_true, List.all_nil, Bool.and_self,
    Bool.xor_true, Bool.not_eq_true']
  rw [readBit_classicalRun_swapCodes (by simp [answer, Counter.level])
    (by simp [width, answer, Counter.level]; omega), hc]
  simp only [decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero, Counter.count,
    Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_range]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  rw [show readBit Z (i + w) = _ from copy_at w Y hi]
  cases readBit Y (i + w) <;> cases readBit Y i <;> decide

private abbrev codes (w : ℕ) (gs : List GateCode) : List GateCode :=
  copyBits w ++ (gs ++ suffix w)

private theorem wellFormed_codes {w : ℕ} {gs : List GateCode}
    (hgs : ∀ g ∈ gs, WellFormed w g) : ∀ g ∈ codes w gs, WellFormed (width w) g := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact (classical_copy w g h).2
  rcases List.mem_append.mp h with h | h
  · simpa only [GateCode.shift_zero] using (hgs g h).shift (o := 0) (N := width w)
      (by unfold width; omega)
  · exact (classical_suffix w g h).2

private theorem uniform_codes (F : UniformCircuitFamily) :
    ComputableInPolyTime (fun n => codes (F.width n) (F.gates n)) encUnary
      (encList encGateCode) := by
  have hw := F.computableInPolyTime_width
  have hg := F.computableInPolyTime_gates
  have hcopy := Amplify.computableInPolyTime_copyCodes hw hw
    (ComputableInPolyTime.const 1 (encIn := encUnary) (encOut := encUnary))
  have hstage := Amplify.computableInPolyTime_stage (enc := encPair encUnary encUnary)
    (base := fun p => 2 * F.width p.1) (T := fun _ => 1)
    (b := fun p => p.2 + F.width p.1) (s := fun p => p.2)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have hcounter : ComputableInPolyTime (fun n => counter (F.width n)) encUnary
      (encList encGateCode) := by
    unfold counter Counter.codes
    fun_prop
  have hswap : ComputableInPolyTime (fun n => swapCodes (answer (F.width n))) encUnary
      (encList encGateCode) := by
    simp only [swapCodes, swapWireCodes, answer, Counter.level]
    fun_prop
  simp only [codes, suffix, copyBits]
  fun_prop

private theorem acceptProb_codes {w : ℕ} {gs : List GateCode}
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
    rw [accepts_suffix w Y (fun i hi => (hsame i (by omega)).trans (hXhigh i hi))]
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
    Circuit.measureProb_eval_ofCodes (classical_suffix w)]
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
  wellFormed n := ReturnTest.wellFormed_codes (F.wellFormed n)

/-- Measuring the designated output of the return test gives the squared norm of the
diagonal matrix entry indexed by the padded input. -/
theorem acceptProb_returnTest (F : UniformCircuitFamily) (x : List Bool) :
    F.returnTest.acceptProb x =
      ‖(Circuit.run (Circuit.ofCodes (F.width x.length) (F.gates x.length))
        (inputState _ x)).ofLp (inputState _ x)‖ ^ 2 :=
  ReturnTest.acceptProb_codes (F.wellFormed _) (F.le_width _)

end UniformCircuitFamily
end Cslib.Quantum
