/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Decode
import CslibFrontier.Foundations.Data.List.GetD

/-!
# Soundness of the quasilinear formula

An assignment satisfying every constraint of the quasilinear formula of `ntm` on `x` reads back as a
valid sequence of step records (`valid_of_sat`), so `ntm` accepts `x`
(`accepts_of_sat`).

The finite parts of consecutive records form allowed pairs, the first record is initial and the last
has halted with output `[true]`. The input head moves as the finite part says, and the symbol it
reads is the input symbol there. The work heads move by one cell at most, so their offset positions
stay away from `0` and `2 ^ (τ + 2)` and the binary additions do not wrap. Finally the network of
each work tape permutes the records, its sorted end has increasing keys, and each symbol read is
what the predecessor in the sorted order left, when it visits the same cell, and blank otherwise;
by `StepRecord.tapeAt_of_sorted` this is what the tape holds.

## Main results

* `Cslib.Complexity.CookLevin.Quasilinear.valid_of_sat`.
* `Cslib.Complexity.CookLevin.Quasilinear.accepts_of_sat`.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin.Quasilinear

open Turing Cslib.BitonicSort

private theorem decSym_false : decSym (fun _ => false) = none := rfl

/-- Staying put leaves the input head where it is. -/
theorem moveIn_zero {n p : ℕ} (hp : p ≤ n + 1) : StepRecord.moveIn n p 0 = p := by
  unfold StepRecord.moveIn
  simp only [SignType.coe_zero, add_zero]
  omega

/-- The code of a move. -/
private def moveIdx : SignType → ℕ
  | .zero => 0
  | .pos => 1
  | .neg => 2

private theorem moveIdx_lt (m : SignType) : moveIdx m < 3 := by cases m <;> decide

private theorem moveCode_moveIdx (m : SignType) : Layout.moveCode (moveIdx m) = m := by
  cases m <;> rfl

namespace Layout

variable (Λ : Layout) (D : MachineData) (x : List Bool)

/-! ### Constraint statements from a satisfying assignment -/

/-- The gates of a constraint of a satisfying assignment hold. -/
private theorem holds_of_sat {σ : ℕ → Bool} (h : Λ.Sat D x σ) {fam : Family} {inst : ℕ}
    (hinst : inst < Λ.count fam) :
    (∀ g ∈ Λ.famDefs D x fam inst, g.Holds σ) ∧ ∀ g ∈ Λ.famCons D x fam inst, g.Holds σ :=
  ⟨fun g hg => h fam inst hinst g (List.mem_append_left _ hg),
    fun g hg => h fam inst hinst g (List.mem_append_right _ hg)⟩

/-- A satisfying assignment makes `vTT` true and `vFF` false. -/
private theorem consts_of_sat {σ : ℕ → Bool} (h : Λ.Sat D x σ) : σ vTT = true ∧ σ vFF = false := by
  obtain ⟨hd, hc⟩ := Λ.holds_of_sat D x h (fam := .consts) (inst := 0) (by simp [count])
  have := (Λ.forall_famCons_iff D x σ .consts 0 hd (fun h => absurd rfl h)).1 hc
  simpa [Meaning] using this

/-- A satisfying assignment satisfies the statement of every constraint. -/
private theorem meaning_of_sat {σ : ℕ → Bool} (h : Λ.Sat D x σ) {fam : Family} {inst : ℕ}
    (hinst : inst < Λ.count fam) : Λ.Meaning D x σ fam inst := by
  obtain ⟨hd, hc⟩ := Λ.holds_of_sat D x h hinst
  exact (Λ.forall_famCons_iff D x σ fam inst hd fun _ => Λ.consts_of_sat D x h).1 hc

end Layout

/-! ### Payloads of the sorting networks -/

namespace Layout

variable (Λ : Layout)

/-- The payload at position `w` after `ℓ` layers of the network of tape `j`. -/
def payload (σ : ℕ → Bool) (j ℓ w : ℕ) : ℕ → Bool :=
  fun b => if b < Λ.P then σ (Λ.arrAt j ℓ w b) else false

private theorem payload_zero_time {σ : ℕ → Bool} (htt : σ vTT = true) (hff : σ vFF = false)
    {j t b : ℕ} (hb : b < Λ.τ) : Λ.payload σ j 0 t b = t.testBit b := by
  unfold payload arrAt pay0
  rw [ite_eq_left (by unfold P; omega), ite_eq_left rfl, ite_eq_left hb]
  split_ifs with hbit
  · rw [htt, hbit]
  · rw [hff]
    simpa using hbit

private theorem payload_zero_pos {σ : ℕ → Bool} {j t i : ℕ} (hi : i < Λ.W) :
    Λ.payload σ j 0 t (Λ.τ + i) = σ (Λ.vRec t (Λ.offPos j + i)) := by
  unfold payload arrAt pay0
  rw [ite_eq_left (by unfold P; omega), ite_eq_left rfl, ite_eq_right (by omega),
    ite_eq_left (by omega), Nat.add_sub_cancel_left]

private theorem payload_zero_read {σ : ℕ → Bool} {j t i : ℕ} (hi : i < 2) :
    Λ.payload σ j 0 t (Λ.τ + Λ.W + i) = σ (Λ.vRec t (Λ.offTape j + i)) := by
  unfold payload arrAt pay0
  rw [ite_eq_left (by unfold P; omega), ite_eq_left rfl, ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]

private theorem payload_zero_after {σ : ℕ → Bool} {j t i : ℕ} (hi : i < 2) :
    Λ.payload σ j 0 t (Λ.τ + Λ.W + 2 + i) = σ (Λ.vRec t (Λ.offTape j + 6 + i)) := by
  unfold payload arrAt pay0
  rw [ite_eq_left (by unfold P; omega), ite_eq_left rfl, ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel_left]

private theorem key_payload_zero {σ : ℕ → Bool} (htt : σ vTT = true) (hff : σ vFF = false) {j t : ℕ}
    (ht : t < Λ.N) :
    bitsVal (Λ.payload σ j 0 t) (Λ.τ + Λ.W) = t + 2 ^ Λ.τ * Λ.posVal σ t j := by
  rw [bitsVal_add]
  congr 1
  · rw [bitsVal_congr fun b hb => Λ.payload_zero_time htt hff hb, bitsVal_testBit _ _ ht]
  · congr 1
    exact bitsVal_congr fun i hi => Λ.payload_zero_pos hi

private theorem payload_lt {σ : ℕ → Bool} {j ℓ w b : ℕ} (hb : b < Λ.P) :
    Λ.payload σ j ℓ w b = σ (Λ.arrAt j ℓ w b) := by
  unfold payload
  rw [ite_eq_left hb]

end Layout

/-! ### The machine-specific part -/

section Soundness

variable {k : ℕ} {State : Type} [Fintype State] {ntm : MultiTapeNTM k Bool State} {κ : ℕ}
  {x : List Bool} {σ : ℕ → Bool}

local notation "Λ" => layoutOf k State κ x.length
local notation "D" => machineData ntm

/-- The width of the finite part of `layoutOf` is that of a finite part. -/
theorem layoutOf_C : (Λ).C = ctrlWidth k State := rfl

/-- The layout of an input has the length of the input. -/
@[simp] theorem layoutOf_n : (Λ).n = x.length := rfl

/-- The layout of a machine has its number of work tapes. -/
@[simp] theorem layoutOf_k : (Λ).k = k := rfl

/-- The layout of a machine has the width of its state code. -/
@[simp] theorem layoutOf_S : (Λ).S = stWidth State := rfl

/-- The offset of a work tape in the layout of a machine. -/
theorem layoutOf_offTape (j : ℕ) : (Λ).offTape j = tapeOff State j := rfl

/-- **Consecutive finite parts form allowed pairs.** -/
private theorem pair_of_sat (h : (Λ).Sat D x σ) {t : ℕ} (ht : t + 1 < (Λ).N) :
    ∃ c c' : Ctrl k State, Ctrl.Allowed ntm c c' ∧
      (∀ i < ctrlWidth k State, σ ((Λ).vRec t i) = ctrlBit c i) ∧
      ∀ i < ctrlWidth k State, σ ((Λ).vRec (t + 1) i) = ctrlBit c' i := by
  have hm := (Λ).meaning_of_sat D x h (fam := .step) (inst := t)
    (by simp [Layout.count]; omega)
  simp only [Layout.Meaning] at hm
  obtain ⟨π, hπ, hlits⟩ := hm
  simp only [Layout.stepPats, machineData, List.map_map, List.mem_map] at hπ
  obtain ⟨⟨c, c'⟩, hcc, rfl⟩ := hπ
  refine ⟨c, c', mem_allowedPairs.1 hcc, fun i hi => ?_, fun i hi => ?_⟩
  · have := hlits _ (List.mem_map.2 ⟨i, List.mem_range.2 (by rw [layoutOf_C]; omega), rfl⟩)
    simp only [layoutOf_C, ite_eq_left hi, pairBits,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega : i < 2 *
        ctrlWidth k State), Option.map_some, Option.getD_some] at this
    simpa [hi] using this
  · have := hlits _ (List.mem_map.2 ⟨ctrlWidth k State + i, List.mem_range.2
      (by rw [layoutOf_C]; omega), rfl⟩)
    simp only [layoutOf_C, show ¬ ctrlWidth k State + i < ctrlWidth k State by omega, ite_false,
      pairBits, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by omega : ctrlWidth k State + i < 2 * ctrlWidth k State),
      Option.map_some, Option.getD_some, Nat.add_sub_cancel_left] at this
    exact this

private theorem ctrlOf_eq {t : ℕ} {c : Ctrl k State}
    (h : ∀ i < ctrlWidth k State, σ ((Λ).vRec t i) = ctrlBit c i) : (Λ).ctrlOf σ t = c := by
  unfold Layout.ctrlOf
  rw [decCtrl_congr h, decCtrl_ctrlBit]

private theorem allowed_of_sat (h : (Λ).Sat D x σ) {t : ℕ} (ht : t + 1 < (Λ).N) :
    Ctrl.Allowed ntm ((Λ).ctrlOf σ t) ((Λ).ctrlOf σ (t + 1)) := by
  obtain ⟨c, c', hcc, h1, h2⟩ := pair_of_sat h ht
  rw [ctrlOf_eq h1, ctrlOf_eq h2]
  exact hcc

/-- The bits of the finite part of every record are those of its decoding. -/
private theorem ctrlBits_of_sat (h : (Λ).Sat D x σ) {t : ℕ} (ht : t < (Λ).N) :
    ∀ i < ctrlWidth k State, σ ((Λ).vRec t i) = ctrlBit ((Λ).ctrlOf σ t : Ctrl k State) i := by
  have h2 := (Λ).two_le_N
  rcases Nat.lt_or_ge (t + 1) (Λ).N with ht' | ht'
  · obtain ⟨c, c', -, h1, -⟩ := pair_of_sat h ht'
    rw [ctrlOf_eq h1]
    exact h1
  · obtain ⟨c, c', -, -, h1⟩ := pair_of_sat h (t := t - 1) (by omega)
    rw [show t - 1 + 1 = t by omega] at h1
    rw [ctrlOf_eq h1]
    exact h1

/-! ### The first and the last record -/

private theorem init_of_sat (h : (Λ).Sat D x σ) :
    ((Λ).ctrlOf σ 0 : Ctrl k State).state = some ntm.q₀ ∧ (Λ).inPosOf σ 0 = 1 ∧
      (∀ j < k, (Λ).posVal σ 0 j = (Λ).N) ∧ ((Λ).ctrlOf σ 0 : Ctrl k State).out = .empty := by
  have hm := (Λ).meaning_of_sat D x h (fam := .init) (inst := 0) (by simp [Layout.count])
  simp only [Layout.Meaning, Layout.initLits,
    List.forall_mem_append] at hm
  obtain ⟨⟨⟨hq, hin⟩, hpos⟩, hout⟩ := hm
  have hb := ctrlBits_of_sat h (t := 0) (by have := (Λ).two_le_N; omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply stateBit_injective
    intro i hi
    have h1 := ((Λ).litsHold_fieldLits).1 hq i (by simpa [machineData] using hi)
    have h1' : σ ((Λ).vRec 0 i) = stateBit (some ntm.q₀) i := by
      simpa [machineData, List.getD_eq_getElem?_getD, hi] using h1
    have h2 := hb i (by unfold ctrlWidth; omega)
    rw [ctrlBit_state _ hi] at h2
    rw [← h2, h1']
  · rw [Layout.inPosOf,
      ← Layout.digits_iff (by unfold Layout.I; exact Nat.one_lt_two_pow (by omega))]
    intro i hi
    have := ((Λ).litsHold_fieldLits).1 hin i (by simpa using hi)
    rw [this, Layout.getD_lowBits hi]
  · intro j hj
    have hj' := ((Λ).litsHold_fieldLits (t := 0) (off := (Λ).offPos j)
      (bs := BitString.lowBits (Λ).W (Λ).N)).1 fun l hl =>
        hpos l (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, hl⟩)
    have hN4 : (Λ).N < 2 ^ (Λ).W := by
      rw [← (Λ).four_mul_N_eq_two_pow_W]; have := (Λ).two_le_N; omega
    rw [Layout.posVal, ← Layout.digits_iff hN4]
    intro i hi
    rw [hj' i (by simpa using hi), Layout.getD_lowBits hi]
  · apply outBit_injective
    intro i hi
    have h1 := ((Λ).litsHold_fieldLits).1 hout i (by simpa using hi)
    have h2 := hb (stWidth State + 6 + i) (by unfold ctrlWidth; omega)
    rw [ctrlBit_out _ hi] at h2
    rw [← h2]
    rw [layoutOf_S, Layout.getD_two _ hi] at h1
    exact h1

private theorem final_of_sat (h : (Λ).Sat D x σ) :
    ((Λ).ctrlOf σ ((Λ).N - 1) : Ctrl k State).state = none ∧
      ((Λ).ctrlOf σ ((Λ).N - 1) : Ctrl k State).out = .one true := by
  have hm := (Λ).meaning_of_sat D x h (fam := .final) (inst := 0) (by simp [Layout.count])
  simp only [Layout.Meaning,
    Layout.finalLits, List.forall_mem_append] at hm
  obtain ⟨hq, hout⟩ := hm
  have hb := ctrlBits_of_sat h (t := (Λ).N - 1) (by have := (Λ).two_le_N; omega)
  refine ⟨?_, ?_⟩
  · apply stateBit_injective
    intro i hi
    have h1 := ((Λ).litsHold_fieldLits).1 hq i (by simpa [machineData] using hi)
    have h1' : σ ((Λ).vRec ((Λ).N - 1) i) = stateBit (none : Option State) i := by
      simpa [machineData, List.getD_eq_getElem?_getD, hi] using h1
    have h2 := hb i (by unfold ctrlWidth; omega)
    rw [ctrlBit_state _ hi] at h2
    rw [← h2, h1']
  · apply outBit_injective
    intro i hi
    have h1 := ((Λ).litsHold_fieldLits).1 hout i (by simpa using hi)
    have h2 := hb (stWidth State + 6 + i) (by unfold ctrlWidth; omega)
    rw [ctrlBit_out _ hi] at h2
    rw [← h2]
    rw [layoutOf_S, Layout.getD_two _ hi] at h1
    exact h1

/-! ### The input head -/

private theorem inSym_of_sat (h : (Λ).Sat D x σ) {t : ℕ} (ht : t < (Λ).N)
    (hz : (Λ).inPosOf σ t < (Λ).I) :
    ((Λ).ctrlOf σ t : Ctrl k State).inSym = StepRecord.inSym x ((Λ).inPosOf σ t) := by
  set z := (Λ).inPosOf σ t with hzdef
  have hinst := Nat.mul_add_div_mod_of_lt (t) hz
  have hm := (Λ).meaning_of_sat D x h (fam := .inSym) (inst := t * (Λ).I + z)
    (by simp only [Layout.count]; exact Nat.mul_add_lt_mul_of_lt ht hz)
  simp only [Layout.Meaning, hinst.1, hinst.2] at hm
  have hant : Layout.LitsHold σ ((Λ).inAtLits t z) := by
    rw [Layout.inAtLits, Layout.litsHold_fieldLits]
    intro i hi
    rw [BitString.length_lowBits] at hi
    rw [Layout.getD_lowBits hi]
    have := (Layout.digits_iff (f := fun i => σ ((Λ).vRec t ((Λ).offIn + i)))
      (lt_of_lt_of_le hz (Nat.lt_two_pow_self).le)).2 hzdef.symm
    exact this i hi
  have hcon := hm hant
  rw [Layout.inSymLits, Layout.litsHold_fieldLits] at hcon
  have hb := ctrlBits_of_sat h ht
  apply symBit_injective
  intro i hi
  have h1 := hcon i (by simpa using hi)
  have h2 := hb (stWidth State + i) (by unfold ctrlWidth; omega)
  rw [ctrlBit_inSym _ hi] at h2
  rw [← h2]
  rw [Layout.getD_two _ hi] at h1
  exact h1

private theorem inPos_succ_of_sat (h : (Λ).Sat D x σ) {t : ℕ} (ht : t + 1 < (Λ).N)
    (hz : (Λ).inPosOf σ t ≤ x.length + 1) :
    (Λ).inPosOf σ (t + 1) =
      StepRecord.moveIn x.length ((Λ).inPosOf σ t) ((Λ).ctrlOf σ t : Ctrl k State).inMove := by
  set z := (Λ).inPosOf σ t with hzdef
  set m := moveIdx ((Λ).ctrlOf σ t : Ctrl k State).inMove with hmdef
  have hm3 : m < 3 := moveIdx_lt _
  have hzI : z < (Λ).I := by unfold Layout.I; simp only [layoutOf_n]; omega
  have h1 := Nat.mul_add_div_mod_of_lt (t) hzI
  have h2 := Nat.mul_add_div_mod_of_lt (t * (Λ).I + z) hm3
  have hm := (Λ).meaning_of_sat D x h (fam := .inMove) (inst := (t * (Λ).I + z) * 3 + m)
    (by
      simp only [Layout.count]
      exact Nat.mul_add_lt_mul_of_lt (Nat.mul_add_lt_mul_of_lt (by omega) hzI) hm3)
  simp only [Layout.Meaning, h2.1, h2.2,
    h1.1, h1.2] at hm
  have hb := ctrlBits_of_sat h (t := t) (by omega)
  have hant : Layout.LitsHold σ ((Λ).inMoveLits t z m) := by
    simp only [Layout.inMoveLits, List.forall_mem_append, Layout.litsHold_fieldLits]
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [BitString.length_lowBits] at hi
      rw [Layout.getD_lowBits hi]
      exact (Layout.digits_iff (f := fun i => σ ((Λ).vRec t ((Λ).offIn + i)))
        (lt_of_lt_of_le hzI (Nat.lt_two_pow_self).le)).2 hzdef.symm i hi
    · rw [Layout.length_two] at hi
      rw [Layout.getD_two _ hi, hmdef, moveCode_moveIdx]
      have := hb (stWidth State + 2 + i) (by unfold ctrlWidth; omega)
      rw [ctrlBit_inMove _ hi] at this
      exact this
  have hcon := hm hant
  rw [Layout.inNextLits, Layout.litsHold_fieldLits] at hcon
  rw [hmdef, moveCode_moveIdx] at hcon
  have hle := StepRecord.moveIn_le x.length z ((Λ).ctrlOf σ t : Ctrl k State).inMove
  rw [Layout.inPosOf, ← Layout.digits_iff (lt_of_lt_of_le (show _ < (Λ).I by
    unfold Layout.I; simp only [layoutOf_n]; omega) (Nat.lt_two_pow_self).le)]
  intro i hi
  have := hcon i (by simpa using hi)
  rw [Layout.getD_lowBits hi] at this
  exact this

/-! ### The work heads -/

/-- The target of an increment depends only on the digits up to its position. -/
theorem addTarget_congr {P Q : Bool} {f f' : ℕ → Bool} {i : ℕ} (h : ∀ j ≤ i, f j = f' j) :
    addTarget P Q f i = addTarget P Q f' i := by
  unfold addTarget incDigit decDigit
  have h1 : (∀ j < i, f j = true) ↔ (∀ j < i, f' j = true) :=
    ⟨fun h' j hj => (h j hj.le) ▸ h' j hj, fun h' j hj => (h j hj.le).symm ▸ h' j hj⟩
  have h2 : (∀ j < i, f j = false) ↔ (∀ j < i, f' j = false) :=
    ⟨fun h' j hj => (h j hj.le) ▸ h' j hj, fun h' j hj => (h j hj.le).symm ▸ h' j hj⟩
  simp only [h i le_rfl, decide_eq_decide.2 h1, decide_eq_decide.2 h2]

/-- The `i`-th pair of positions of work head `j` in records `t` and `t + 1`. -/
theorem getD_posPairs {t j i : ℕ} (hi : i < (Λ).W) :
    ((Λ).posPairs t j).getD i (0, 0) =
      ((Λ).vRec t ((Λ).offPos j + i), (Λ).vRec (t + 1) ((Λ).offPos j + i)) := by
  simp [Layout.posPairs, List.getD_eq_getElem?_getD, hi]

/-- **A work head moves as its finite part says**, while its offset position stays inside
`[1, 2 ^ (τ + 2) - 2]`. -/
private theorem pos_succ_of_sat (h : (Λ).Sat D x σ) {t : ℕ} (ht : t + 1 < (Λ).N) (j : Fin k)
    (hlo : 1 ≤ (Λ).posVal σ t j) (hhi : (Λ).posVal σ t j + 2 ≤ 2 ^ (Λ).W) :
    ((Λ).posVal σ (t + 1) j : ℤ) =
      (Λ).posVal σ t j + ((((Λ).ctrlOf σ t : Ctrl k State).move j : SignType) : ℤ) := by
  have hpk := Nat.mul_add_div_mod_of_lt t (m := k) j.isLt
  have hm := (Λ).meaning_of_sat D x h (fam := .workMove) (inst := t * k + j)
    (by
      simp only [Layout.count, layoutOf_k]
      exact Nat.mul_add_lt_mul_of_lt (by omega) j.isLt)
  simp only [Layout.Meaning, layoutOf_k, hpk.1, hpk.2,
    Layout.length_posPairs] at hm
  set f := fun i => σ ((Λ).vRec t ((Λ).offPos j + i)) with hf
  set g := fun i => σ ((Λ).vRec (t + 1) ((Λ).offPos j + i)) with hg
  have hb := ctrlBits_of_sat h (t := t) (by omega)
  set m := ((Λ).ctrlOf σ t : Ctrl k State).move j with hmv
  have hP : σ ((Λ).vRec t ((Λ).offTape j + 4)) = moveBit m 0 := by
    have := hb (tapeOff State j + 4 + 0) (by unfold ctrlWidth tapeOff; have := j.isLt; omega)
    rw [ctrlBit_move _ j (by omega)] at this
    simpa [layoutOf_offTape] using this
  have hQ : σ ((Λ).vRec t ((Λ).offTape j + 5)) = moveBit m 1 := by
    have := hb (tapeOff State j + 4 + 1) (by unfold ctrlWidth tapeOff; have := j.isLt; omega)
    rw [ctrlBit_move _ j (by omega)] at this
    simpa [layoutOf_offTape] using this
  have hgf : ∀ i < (Λ).W, g i = addTarget (moveBit m 0) (moveBit m 1) f i := by
    intro i hi
    have := hm i hi
    rw [getD_posPairs hi, hP, hQ] at this
    change σ ((Λ).vRec (t + 1) ((Λ).offPos j + i)) = _
    rw [this]
    exact addTarget_congr fun j' hj' => by
      change σ (((Λ).posPairs t j).getD j' (0, 0)).1 = σ ((Λ).vRec t ((Λ).offPos j + j'))
      rw [getD_posPairs (by omega)]
  have hpos : (Λ).posVal σ t j = bitsVal f (Λ).W := rfl
  have hpos' : (Λ).posVal σ (t + 1) j = bitsVal g (Λ).W := rfl
  rw [hpos', hpos]
  rw [hpos] at hlo hhi
  rcases hm' : m with _ | _ | _
  · -- stay
    have hgf' : ∀ i < (Λ).W, g i = f i := fun i hi => by
      rw [hgf i hi, hm']
      simp [addTarget, moveBit]
    rw [bitsVal_congr hgf']
    have hc : ((SignType.zero : SignType) : ℤ) = 0 := rfl
    rw [hc]
    simp
  · -- left
    have hgf' : ∀ i < (Λ).W, g i = decDigit f i := fun i hi => by
      rw [hgf i hi, hm']
      simp [addTarget, moveBit]
    have hd := bitsVal_decDigit_add_one f (Λ).W
    rw [bitsVal_congr hgf']
    have hne : ¬ ∀ j < (Λ).W, f j = false := fun hall => by
      rw [bitsVal_congr hall, bitsVal_false] at hlo
      omega
    rw [ite_eq_right hne] at hd
    have hc : ((SignType.neg : SignType) : ℤ) = -1 := rfl
    rw [hc]
    omega
  · -- right
    have hgf' : ∀ i < (Λ).W, g i = incDigit f i := fun i hi => by
      rw [hgf i hi, hm']
      simp [addTarget, moveBit]
    have hd := bitsVal_incDigit f (Λ).W
    rw [bitsVal_congr hgf', hd, Nat.mod_eq_of_lt (by omega)]
    have hc : ((SignType.pos : SignType) : ℤ) = 1 := rfl
    rw [hc]
    push_cast
    ring

/-- **The heads stay in range.** The input head stays on the input or next to it, and the offset
work-head position of record `t` is within `t` of `N`. -/
private theorem bounds_of_sat (h : (Λ).Sat D x σ) :
    ∀ t < (Λ).N, (Λ).inPosOf σ t ≤ x.length + 1 ∧
      ∀ j : Fin k, (Λ).N - t ≤ (Λ).posVal σ t j ∧ (Λ).posVal σ t j ≤ (Λ).N + t := by
  intro t ht
  induction t with
  | zero =>
    obtain ⟨-, hin, hpos, -⟩ := init_of_sat h
    exact ⟨by omega, fun j => by rw [hpos j j.isLt]; omega⟩
  | succ t ih =>
    obtain ⟨hin, hpos⟩ := ih (by omega)
    refine ⟨?_, fun j => ?_⟩
    · rw [inPos_succ_of_sat h ht hin]
      exact StepRecord.moveIn_le _ _ _
    · obtain ⟨h1, h2⟩ := hpos j
      have hW := (Λ).four_mul_N_eq_two_pow_W
      have := pos_succ_of_sat h ht j (by omega) (by omega)
      rcases hmv : (((Λ).ctrlOf σ t : Ctrl k State).move j) with _ | _ | _ <;>
        rw [hmv] at this
      · have hc : ((SignType.zero : SignType) : ℤ) = 0 := rfl
        rw [hc] at this
        omega
      · have hc : ((SignType.neg : SignType) : ℤ) = -1 := rfl
        rw [hc] at this
        omega
      · have hc : ((SignType.pos : SignType) : ℤ) = 1 := rfl
        rw [hc] at this
        omega

/-! ### The work tapes -/

private theorem payload_succ (h : (Λ).Sat D x σ) {j ℓ w : ℕ} (hj : j < k) (hℓ : ℓ < (Λ).L)
    (hw : w < (Λ).N) :
    (Λ).payload σ j (ℓ + 1) w =
      swapLayer ((Λ).expo ℓ) (fun w' => σ ((Λ).vFlag j ℓ w')) ((Λ).payload σ j ℓ) w := by
  funext b
  unfold Layout.payload swapLayer
  by_cases hb : b < (Λ).P
  · have hP := Nat.mul_add_div_mod_of_lt ((j * (Λ).L + ℓ) * (Λ).N + w) hb
    have hN := Nat.mul_add_div_mod_of_lt (j * (Λ).L + ℓ) hw
    have hL := Nat.mul_add_div_mod_of_lt (j) hℓ
    have hm := (Λ).meaning_of_sat D x h (fam := .switch)
      (inst := ((j * (Λ).L + ℓ) * (Λ).N + w) * (Λ).P + b)
      (by
        simp only [Layout.count, layoutOf_k]
        exact Nat.mul_add_lt_mul_of_lt
          (Nat.mul_add_lt_mul_of_lt (Nat.mul_add_lt_mul_of_lt hj hℓ) hw) hb)
    simp only [Layout.Meaning, hP.1, hP.2,
      hN.1, hN.2, hL.1, hL.2] at hm
    rw [ite_eq_left hb, hm]
    by_cases hf : σ ((Λ).vFlag j ℓ (low ((Λ).expo ℓ) w)) = true <;>
      simp [hf, hb, swapSource]
  · rw [ite_eq_right hb]
    simp [hb]

private theorem payload_stage (h : (Λ).Sat D x σ) {j : ℕ} (hj : j < k) :
    ∀ ℓ ≤ (Λ).L, ∀ w < (Λ).N, (Λ).payload σ j ℓ w =
      stage (schedule (Λ).τ) (fun ℓ w' => σ ((Λ).vFlag j ℓ w')) ((Λ).payload σ j 0) ℓ w := by
  intro ℓ hℓ
  induction ℓ with
  | zero => intro w _; rfl
  | succ ℓ ih =>
    intro w hw
    have he := (Λ).expo_lt (ℓ := ℓ) (by omega)
    rw [payload_succ h hj (by omega) hw, stage]
    unfold swapLayer
    have hpw := partner_lt he hw
    have hs : swapSource ((Λ).expo ℓ) (fun w' => σ ((Λ).vFlag j ℓ w')) w < (Λ).N := by
      unfold swapSource
      split_ifs
      exacts [hpw, hw]
    rw [ih (by omega) _ hs]
    rfl

/-- **Every symbol read is what the tape holds.** -/
private theorem reads_eq_of_sat (h : (Λ).Sat D x σ) {t : ℕ} (ht : t < (Λ).N) (j : Fin k) :
    ((Λ).recOf σ t : StepRecord k State).reads j =
      StepRecord.tapeAt ((Λ).recOf (State := State) σ) j t
        (((Λ).recOf σ t : StepRecord k State).pos j) := by
  obtain ⟨htt, hff⟩ := (Λ).consts_of_sat D x h
  have hsch : ∀ p ∈ schedule (Λ).τ, p.2 < (Λ).τ := fun p hp => by
    have := mem_schedule hp
    omega
  obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin (Λ).N), ∀ w : Fin (Λ).N,
      stage (schedule (Λ).τ) (fun ℓ w' => σ ((Λ).vFlag j ℓ w')) ((Λ).payload σ j 0) (Λ).L w =
        (Λ).payload σ j 0 (π w) :=
    exists_perm_stage hsch (fun ℓ w' => σ ((Λ).vFlag j ℓ w')) ((Λ).payload σ j 0) (Λ).L le_rfl
  have hL : ∀ w : Fin (Λ).N, (Λ).payload σ j (Λ).L w = (Λ).payload σ j 0 (π w) := fun w =>
    (payload_stage h j.isLt (Λ).L le_rfl w w.isLt).trans (hπ w)
  set p : ℕ → ℕ := fun s => (Λ).posVal σ s j with hp
  have hBv : ∀ w b, b < (Λ).P → σ ((Λ).arrAt j (Λ).L w b) = (Λ).payload σ j (Λ).L w b :=
    fun w b hb => ((Λ).payload_lt hb).symm
  -- the sorted keys increase
  have hkey : ∀ u (hu : u < (Λ).N), 0 < u →
      (π ⟨u - 1, by omega⟩ : ℕ) + 2 ^ (Λ).τ * p (π ⟨u - 1, by omega⟩) <
        π ⟨u, hu⟩ + 2 ^ (Λ).τ * p (π ⟨u, hu⟩) := by
    intro u hu h0
    have hj := Nat.mul_add_div_mod_of_lt ((j : ℕ)) hu
    have hm := (Λ).meaning_of_sat D x h (fam := .sorted) (inst := j * (Λ).N + u)
      (by simp only [Layout.count, layoutOf_k]; exact Nat.mul_add_lt_mul_of_lt j.isLt hu)
    simp only [Layout.Meaning, ite_false, hj.1, hj.2, show u ≠ 0 by omega,
      Layout.length_keyPairs] at hm
    have hk1 := hm.1
    have e1 : ∀ i < (Λ).τ + (Λ).W,
        σ (((Λ).keyPairs j u).getD i (0, 0)).1 = (Λ).payload σ j (Λ).L (u - 1) i := fun i hi => by
      simp only [Layout.keyPairs, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hi, Option.map_some, Option.getD_some]
      exact hBv _ _ (by unfold Layout.P; omega)
    have e2 : ∀ i < (Λ).τ + (Λ).W,
        σ (((Λ).keyPairs j u).getD i (0, 0)).2 = (Λ).payload σ j (Λ).L u i := fun i hi => by
      simp only [Layout.keyPairs, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hi, Option.map_some, Option.getD_some]
      exact hBv _ _ (by unfold Layout.P; omega)
    rw [bitsVal_congr e1, bitsVal_congr e2, hL ⟨u - 1, by omega⟩, hL ⟨u, hu⟩,
      (Λ).key_payload_zero htt hff (π _).isLt, (Λ).key_payload_zero htt hff (π _).isLt] at hk1
    exact hk1
  have hpeq : ∀ s < (Λ).N, ∀ t < (Λ).N, ((Λ).recOf σ s : StepRecord k State).pos j =
      ((Λ).recOf σ t : StepRecord k State).pos j ↔ p s = p t := by
    intro s _ t _
    simp only [Layout.recOf, hp]
    omega
  have hsorted := StepRecord.tapeAt_of_sorted ((Λ).recOf σ) j le_rfl π p hpeq hkey ⟨t, ht⟩
  simp only at hsorted
  rw [hsorted]
  set u : ℕ := (π.symm ⟨t, ht⟩ : ℕ) with hu
  have huN : u < (Λ).N := (π.symm ⟨t, ht⟩).isLt
  have hπu : π ⟨u, huN⟩ = ⟨t, ht⟩ := by simp [hu]
  have hb := ctrlBits_of_sat h ht
  -- the bits read at time `t` are the read bits of the sorted payload at `u`
  have hread : ∀ i < 2, (Λ).payload σ j (Λ).L u ((Λ).τ + (Λ).W + i) =
      symBit (((Λ).ctrlOf σ t : Ctrl k State).read j) i := by
    intro i hi
    rw [hL ⟨u, huN⟩, hπu, (Λ).payload_zero_read hi, layoutOf_offTape,
      hb _ (by unfold ctrlWidth tapeOff; have := j.isLt; omega), ctrlBit_read _ j hi]
  have hj := Nat.mul_add_div_mod_of_lt ((j : ℕ)) huN
  have hmeaning := (Λ).meaning_of_sat D x h (fam := .sorted) (inst := j * (Λ).N + u)
    (by simp only [Layout.count, layoutOf_k]; exact Nat.mul_add_lt_mul_of_lt j.isLt huN)
  simp only [Layout.Meaning, hj.1, hj.2] at hmeaning
  have hposbits : ∀ (a b : Fin (Λ).N), p a = p b → ∀ i < (Λ).W,
      σ ((Λ).vRec a ((Λ).offPos j + i)) = σ ((Λ).vRec b ((Λ).offPos j + i)) :=
    fun a b hab => bitsVal_injective (f := fun i => σ ((Λ).vRec a ((Λ).offPos j + i)))
      (g := fun i => σ ((Λ).vRec b ((Λ).offPos j + i))) hab
  have hposeq : ∀ (a b : Fin (Λ).N), (∀ i < (Λ).W,
      σ ((Λ).vRec a ((Λ).offPos j + i)) = σ ((Λ).vRec b ((Λ).offPos j + i))) → p a = p b :=
    fun a b hab => bitsVal_congr hab
  have hsameGet : ∀ i < (Λ).W, ((Λ).samePairs j u).getD i (0, 0) =
      ((Λ).arrAt j (Λ).L (u - 1) ((Λ).τ + i), (Λ).arrAt j (Λ).L u ((Λ).τ + i)) := fun i hi => by
    simp [Layout.samePairs, List.getD_eq_getElem?_getD, hi]
  split_ifs with hc
  · -- the predecessor visits the same cell
    obtain ⟨h0, hpp⟩ := hc
    set t' := π ⟨u - 1, by omega⟩ with ht'
    have hlt : (t' : ℕ) < t := by
      have := hkey u huN h0
      rw [hπu] at this
      exact (StepRecord.lt_of_key_lt t'.isLt ht this).2 hpp
    rw [ite_eq_right (by omega)] at hmeaning
    have hsame : ∀ q ∈ (Λ).samePairs j u, σ q.1 = σ q.2 := by
      rw [forall_mem_iff_getD (d := (0, 0)) (P := fun q => σ q.1 = σ q.2),
        Layout.length_samePairs]
      intro i hi
      rw [hsameGet i hi]
      change σ ((Λ).arrAt j (Λ).L (u - 1) ((Λ).τ + i)) = σ ((Λ).arrAt j (Λ).L u ((Λ).τ + i))
      rw [hBv _ _ (by unfold Layout.P; omega), hBv _ _ (by unfold Layout.P; omega),
        hL ⟨u - 1, by omega⟩, hL ⟨u, huN⟩, hπu, ← ht', (Λ).payload_zero_pos hi,
        (Λ).payload_zero_pos hi]
      exact hposbits t' ⟨t, ht⟩ hpp i hi
    obtain ⟨h0', h1'⟩ := hmeaning.2.1 hsame
    have hb' := ctrlBits_of_sat h t'.isLt
    have hafter : ((Λ).ctrlOf σ t : Ctrl k State).read j =
        ((Λ).ctrlOf σ t' : Ctrl k State).after j := by
      apply symBit_injective
      intro i hi
      rw [← hread i hi, ← hBv _ _ (by unfold Layout.P; omega)]
      have ha : ∀ i < 2, (Λ).payload σ j (Λ).L (u - 1) ((Λ).τ + (Λ).W + 2 + i) =
          symBit (((Λ).ctrlOf σ t' : Ctrl k State).after j) i := by
        intro i hi
        rw [hL ⟨u - 1, by omega⟩, ← ht', (Λ).payload_zero_after hi, layoutOf_offTape,
          hb' _ (by unfold ctrlWidth tapeOff; have := j.isLt; omega), ctrlBit_after _ j hi]
      interval_cases i
      · rw [Nat.add_zero, h0', hBv _ _ (by unfold Layout.P; omega)]
        simpa using ha 0 (by omega)
      · rw [h1', hBv _ _ (by unfold Layout.P; omega)]
        exact ha 1 (by omega)
    -- what the predecessor left
    have hal := allowed_of_sat h (t := t') (by omega)
    change ((Λ).ctrlOf σ t : Ctrl k State).read j = StepRecord.cellAfter ((Λ).recOf σ t') j
    rw [hafter]
    unfold Ctrl.Allowed at hal
    unfold StepRecord.cellAfter
    simp only [Layout.recOf]
    rcases hs : ((Λ).ctrlOf σ t' : Ctrl k State).state with _ | q
    · rw [hs] at hal
      exact (hal.2.2.2.2 j).2.2
    · rw [hs] at hal
      exact hal.2.2 j
  · -- no earlier visit: the bits read are blank
    have hblank : ∀ i < 2, (Λ).payload σ j (Λ).L u ((Λ).τ + (Λ).W + i) = false := by
      intro i hi
      by_cases hu0 : u = 0
      · rw [ite_eq_left hu0] at hmeaning
        rw [← hBv _ _ (by unfold Layout.P; omega)]
        interval_cases i
        · simpa [hu0] using hmeaning.1
        · simpa [hu0] using hmeaning.2
      · rw [ite_eq_right hu0] at hmeaning
        have hne : ¬ ∀ q ∈ (Λ).samePairs j u, σ q.1 = σ q.2 := by
          intro hsame
          apply hc
          refine ⟨by omega, ?_⟩
          refine hposeq _ ⟨t, ht⟩ fun i hi => ?_
          have := hsame _ (List.getD_mem (0, 0) (by rw [Layout.length_samePairs]; exact hi))
          rw [hsameGet i hi] at this
          change σ ((Λ).arrAt j (Λ).L (u - 1) ((Λ).τ + i)) =
            σ ((Λ).arrAt j (Λ).L u ((Λ).τ + i)) at this
          rw [hBv _ _ (by unfold Layout.P; omega), hBv _ _ (by unfold Layout.P; omega),
            hL ⟨u - 1, by omega⟩, hL ⟨u, huN⟩, hπu, (Λ).payload_zero_pos hi,
            (Λ).payload_zero_pos hi] at this
          exact this
        rw [← hBv _ _ (by unfold Layout.P; omega)]
        interval_cases i
        · by_contra hr
          exact hne (hmeaning.2.2.1 (by simpa using hr))
        · by_contra hr
          exact hne (hmeaning.2.2.2 (by simpa using hr))
    change ((Λ).ctrlOf σ t : Ctrl k State).read j = none
    apply symBit_injective
    intro i hi
    rw [← hread i hi, hblank i hi]
    rfl

/-! ### Soundness -/

/-- **A satisfying assignment reads back as a valid sequence of records.** -/
theorem valid_of_sat (h : (Λ).Sat D x σ) :
    StepRecord.Valid ntm x (Λ).N ((Λ).recOf σ) := by
  have hN := (Λ).two_le_N
  obtain ⟨hq0, hin0, hpos0, hout0⟩ := init_of_sat h
  obtain ⟨hhalt, hacc⟩ := final_of_sat h
  have hbd := bounds_of_sat h
  refine ⟨hq0, hin0, fun j => ?_, hout0, fun t ht => ?_, fun t ht q hq => ?_,
    fun t ht j => reads_eq_of_sat h ht j, hhalt, hacc⟩
  · change ((Λ).posVal σ 0 j : ℤ) - (Λ).N = 0
    rw [hpos0 j j.isLt]
    simp
  · have hal := allowed_of_sat h ht
    obtain ⟨hin, hpos⟩ := hbd t (by omega)
    have hinS := inPos_succ_of_sat h ht hin
    have hW := (Λ).four_mul_N_eq_two_pow_W
    have hposS : ∀ j : Fin k, ((Λ).posVal σ (t + 1) j : ℤ) =
        (Λ).posVal σ t j + ((((Λ).ctrlOf σ t : Ctrl k State).move j : SignType) : ℤ) :=
      fun j => pos_succ_of_sat h ht j (by have := hpos j; omega) (by have := hpos j; omega)
    unfold StepRecord.Follows
    unfold Ctrl.Allowed at hal
    simp only [Layout.recOf]
    rcases hs : ((Λ).ctrlOf σ t : Ctrl k State).state with _ | q
    · rw [hs] at hal
      obtain ⟨hs', hmv, -, hout, hw⟩ := hal
      refine ⟨hs', ?_, ?_, hout⟩
      · rw [hinS, hmv, moveIn_zero hin]
      · funext j
        rw [hposS j, (hw j).2.1]
        have hc : ((0 : SignType) : ℤ) = 0 := rfl
        rw [hc]
        ring
    · rw [hs] at hal
      obtain ⟨-, hout, -⟩ := hal
      refine ⟨rfl, hinS, ?_, hout⟩
      funext j
      rw [hposS j]
      simp only [Ctrl.action]
      ring
  · rcases Nat.lt_or_ge (t + 1) (Λ).N with ht' | ht'
    · have hal := allowed_of_sat h ht'
      have hin := (hbd t ht).1
      unfold Ctrl.Allowed at hal
      simp only [Layout.recOf] at hq ⊢
      rw [hq] at hal
      rw [← inSym_of_sat h ht (by unfold Layout.I; simp only [layoutOf_n]; omega)]
      exact hal.1
    · have : t = (Λ).N - 1 := by omega
      subst this
      simp only [Layout.recOf, hhalt] at hq
      cases hq

/-- **Soundness of the quasilinear formula**: a satisfying assignment gives an accepting run. -/
theorem accepts_of_sat (h : (Λ).Sat D x σ) : ntm.Accepts x :=
  StepRecord.accepts_of_valid (valid_of_sat h) (by have := (Λ).two_le_N; omega)

end Soundness

end Cslib.Complexity.CookLevin.Quasilinear
