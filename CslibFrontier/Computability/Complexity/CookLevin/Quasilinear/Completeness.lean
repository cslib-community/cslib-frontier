/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Soundness
public import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Defining
public import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Bounds
public import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Structure

/-!
# Completeness of the quasilinear formula

A valid sequence of records of `ntm` on `x` gives an assignment satisfying every constraint of the
quasilinear formula (`Layout.exists_sat_of_valid`), so an accepting machine running within fewer
than `N` steps has a satisfiable formula (`Layout.exists_sat_of_accepts`).

The assignment writes the records in the variables of the records, runs Batcher's comparator
network on the payloads of each work tape, using its comparisons as flags, and gives every fresh
variable of a gadget the value its defining gate computes. The comparator network sorts, so the
predecessor of each record in the sorted order is the latest earlier visit of its cell
(`StepRecord.tapeAt_of_sorted`), which is what the record read there.

## Main results

* `Cslib.Complexity.CookLevin.Quasilinear.Layout.exists_sat_of_valid`.
* `Cslib.Complexity.CookLevin.Quasilinear.Layout.exists_sat_of_accepts`.
* `Cslib.Complexity.CookLevin.Quasilinear.Layout.sat_iff_accepts`: the formula is satisfiable
  exactly when the machine accepts.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin.Quasilinear

open Turing Cslib.BitonicSort

variable {k : ℕ} {State : Type} [Fintype State]

namespace StepRecord

end StepRecord

/-! ### The records written as bits -/

namespace Layout

variable (x : List Bool) (R : ℕ → StepRecord k State)

/-- The finite part of record `t`. -/
def ctrlRec (t : ℕ) : Ctrl k State :=
  match (R t).state with
  | none => ⟨none, StepRecord.inSym x (R t).inPos, 0, none, (R t).out, (R t).reads,
      fun _ => none, fun _ => 0, (R t).reads⟩
  | some q => ⟨some q, StepRecord.inSym x (R t).inPos, (R t).action.inputTape,
      (R t).action.output, (R t).out, (R t).reads, fun j => ((R t).action.workTapes j).1,
      fun j => ((R t).action.workTapes j).2, fun j => (R t).cellAfter j⟩

omit [Fintype State] in
private theorem ctrlRec_state (t : ℕ) : (ctrlRec x R t).state = (R t).state := by
  unfold ctrlRec; split <;> simp_all

omit [Fintype State] in
private theorem ctrlRec_inSym (t : ℕ) : (ctrlRec x R t).inSym = StepRecord.inSym x (R t).inPos := by
  unfold ctrlRec; split <;> rfl

omit [Fintype State] in
private theorem ctrlRec_out (t : ℕ) : (ctrlRec x R t).out = (R t).out := by
  unfold ctrlRec; split <;> rfl

omit [Fintype State] in
private theorem ctrlRec_read (t : ℕ) : (ctrlRec x R t).read = (R t).reads := by
  unfold ctrlRec; split <;> rfl

omit [Fintype State] in
private theorem ctrlRec_after (t : ℕ) (j : Fin k) :
    (ctrlRec x R t).after j = (R t).cellAfter j := by
  unfold ctrlRec StepRecord.cellAfter
  split <;> rename_i h <;> simp [h]

variable (Λ : Layout)

/-- The offset position of work head `j` in record `t`, as a natural number. -/
def posNat (t j : ℕ) : ℕ := if h : j < k then ((R t).pos ⟨j, h⟩ + Λ.N).toNat else 0

/-- Bit `f` of record `t`. -/
noncomputable def recBit (t f : ℕ) : Bool :=
  if f < Λ.C then ctrlBit (ctrlRec x R t) f
  else if f < Λ.C + Λ.I then (R t).inPos.testBit (f - Λ.C)
  else (Λ.posNat R t ((f - Λ.C - Λ.I) / Λ.W)).testBit ((f - Λ.C - Λ.I) % Λ.W)

/-- The assignment of the constants and the record bits. -/
noncomputable def σR (v : ℕ) : Bool :=
  if v = 0 then true
  else if v = 1 then false
  else if v % 8 = 2 then Λ.recBit x R ((v - 2) / 8 / Λ.RB) ((v - 2) / 8 % Λ.RB)
  else false

/-- The payloads before the first layer of the network of tape `j`. -/
noncomputable def pay0Val (j t b : ℕ) : Bool :=
  if b < Λ.P then Λ.σR x R (Λ.pay0 j t b) else false

/-- The sorting key of a payload: its time and position. -/
def keyOf (p : ℕ → Bool) : ℕ := bitsVal p (Λ.τ + Λ.W)

/-- The arrays of the comparator network of tape `j`. -/
noncomputable def netArr (j ℓ : ℕ) : ℕ → ℕ → Bool :=
  cmpRun Λ.keyOf (dirFn Λ.τ true) ((schedule Λ.τ).take ℓ) (Λ.pay0Val x R j)

/-- The flags of the comparator network of tape `j`. -/
noncomputable def netFlag (j : ℕ) : ℕ → ℕ → Bool :=
  cmpFlags Λ.keyOf (dirFn Λ.τ true) (schedule Λ.τ) (Λ.pay0Val x R j)

/-- The assignment of every variable below the fresh ones. -/
noncomputable def σ₀ (v : ℕ) : Bool :=
  if 3 ≤ v ∧ v % 8 = 3 then
    let i := (v - 3) / 8
    Λ.netArr x R (i / Λ.P / Λ.N / Λ.L) (i / Λ.P / Λ.N % Λ.L + 1) (i / Λ.P % Λ.N) (i % Λ.P)
  else if 4 ≤ v ∧ v % 8 = 4 then
    let i := (v - 4) / 8
    Λ.netFlag x R (i / Λ.N / Λ.L) (i / Λ.N % Λ.L) (i % Λ.N)
  else Λ.σR x R v

private theorem σ₀_vTT : Λ.σ₀ x R vTT = true := by
  simp [σ₀, σR, vTT]

private theorem σ₀_vFF : Λ.σ₀ x R vFF = false := by
  simp [σ₀, σR, vFF]

private theorem σR_vRec {t f : ℕ} (hf : f < Λ.RB) : Λ.σR x R (Λ.vRec t f) = Λ.recBit x R t f := by
  have h := Nat.mul_add_div_mod_of_lt (t) hf
  unfold σR vRec
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
  rw [show (2 + 8 * (t * Λ.RB + f) - 2) / 8 = t * Λ.RB + f by omega, h.1, h.2]

private theorem σ₀_vRec {t f : ℕ} (hf : f < Λ.RB) : Λ.σ₀ x R (Λ.vRec t f) = Λ.recBit x R t f := by
  unfold σ₀
  rw [ite_eq_right (by unfold vRec; omega), ite_eq_right (by unfold vRec; omega), σR_vRec x R Λ hf]

private theorem σ₀_vArr {j ℓ w b : ℕ} (hℓ : ℓ < Λ.L) (hw : w < Λ.N) (hb : b < Λ.P) :
    Λ.σ₀ x R (Λ.vArr j ℓ w b) = Λ.netArr x R j (ℓ + 1) w b := by
  have hP := Nat.mul_add_div_mod_of_lt ((j * Λ.L + ℓ) * Λ.N + w) hb
  have hN := Nat.mul_add_div_mod_of_lt (j * Λ.L + ℓ) hw
  have hL := Nat.mul_add_div_mod_of_lt (j) hℓ
  unfold σ₀ vArr
  rw [ite_eq_left (by omega)]
  simp only
  rw [show (3 + 8 * (((j * Λ.L + ℓ) * Λ.N + w) * Λ.P + b) - 3) / 8 =
    ((j * Λ.L + ℓ) * Λ.N + w) * Λ.P + b by omega, hP.1, hP.2, hN.1, hN.2, hL.1, hL.2]

private theorem σ₀_vFlag {j ℓ w : ℕ} (hℓ : ℓ < Λ.L) (hw : w < Λ.N) :
    Λ.σ₀ x R (Λ.vFlag j ℓ w) = Λ.netFlag x R j ℓ w := by
  have hN := Nat.mul_add_div_mod_of_lt (j * Λ.L + ℓ) hw
  have hL := Nat.mul_add_div_mod_of_lt (j) hℓ
  unfold σ₀ vFlag
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  simp only
  rw [show (4 + 8 * ((j * Λ.L + ℓ) * Λ.N + w) - 4) / 8 = (j * Λ.L + ℓ) * Λ.N + w by omega,
    hN.1, hN.2, hL.1, hL.2]

private theorem σ₀_pay0 {j t b : ℕ} : Λ.σ₀ x R (Λ.pay0 j t b) = Λ.σR x R (Λ.pay0 j t b) := by
  unfold σ₀
  have : Λ.pay0 j t b % 8 ≠ 3 ∧ Λ.pay0 j t b % 8 ≠ 4 := by
    unfold pay0
    split_ifs <;> simp [vTT, vFF, vRec]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

private theorem netArr_zero (j : ℕ) : Λ.netArr x R j 0 = Λ.pay0Val x R j := rfl

/-- The variables of the networks hold the arrays of the comparator networks. -/
private theorem σ₀_arrAt {j ℓ w b : ℕ} (hℓ : ℓ ≤ Λ.L) (hw : w < Λ.N) (hb : b < Λ.P) :
    Λ.σ₀ x R (Λ.arrAt j ℓ w b) = Λ.netArr x R j ℓ w b := by
  unfold arrAt
  split_ifs with h0
  · subst h0
    rw [σ₀_pay0, netArr_zero]
    unfold pay0Val
    rw [ite_eq_left hb]
  · rw [σ₀_vArr x R Λ (by omega) hw hb, Nat.sub_add_cancel (by omega)]

end Layout

namespace Layout

/-! ### The statements of the constraints hold -/

section Meanings

variable {ntm : MultiTapeNTM k Bool State} {κ : ℕ} {x : List Bool} {R : ℕ → StepRecord k State}
  {σ : ℕ → Bool}

local notation "Λ" => layoutOf k State κ x.length
local notation "D" => machineData ntm

private theorem layoutOf_RB : (Λ).RB = ctrlWidth k State + (x.length + 2) + k * (Λ).W := rfl

private theorem offTape_add_lt_C {j : ℕ} (hj : j < k) {r : ℕ} (hr : r < 8) :
    (Λ).offTape j + r < (Λ).C := by
  unfold Layout.offTape Layout.C
  simp only [layoutOf_k, layoutOf_S]
  omega

private theorem offPos_add_lt_RB {j : ℕ} (hj : j < k) {i : ℕ} (hi : i < (Λ).W) :
    (Λ).offPos j + i < (Λ).RB := by
  have : (Λ).W * j + (Λ).W ≤ (Λ).W * k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  unfold Layout.offPos Layout.RB
  simp only [layoutOf_k]
  rw [Nat.mul_comm k] at *
  omega

variable (hσ : ∀ v < (layoutOf k State κ x.length).AUX,
  σ v = (layoutOf k State κ x.length).σ₀ x R v)
include hσ

/-- The constant `true` is true under a satisfying assignment. -/
theorem σ_vTT : σ vTT = true := by
  rw [hσ _ (by unfold vTT Layout.AUX; omega), Layout.σ₀_vTT]

/-- The constant `false` is false under a satisfying assignment. -/
theorem σ_vFF : σ vFF = false := by
  rw [hσ _ (by unfold vFF Layout.AUX; omega), Layout.σ₀_vFF]

private theorem σ_vRec {t f : ℕ} (ht : t < (Λ).N) (hf : f < (Λ).RB) :
    σ ((Λ).vRec t f) = (Λ).recBit x R t f := by
  rw [hσ _ ((Λ).vRec_lt_AUX ht hf), Layout.σ₀_vRec x R _ hf]

private theorem σ_ctrl {t f : ℕ} (ht : t < (Λ).N) (hf : f < (Λ).C) :
    σ ((Λ).vRec t f) = ctrlBit (Layout.ctrlRec x R t) f := by
  rw [σ_vRec hσ ht (lt_of_lt_of_le hf (Λ).C_le_RB)]
  unfold Layout.recBit
  rw [ite_eq_left hf]

private theorem σ_inPos {t i : ℕ} (ht : t < (Λ).N) (hi : i < (Λ).I) :
    σ ((Λ).vRec t ((Λ).offIn + i)) = (R t).inPos.testBit i := by
  rw [σ_vRec hσ ht (by unfold Layout.offIn Layout.RB; omega)]
  unfold Layout.recBit Layout.offIn
  rw [ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left]

private theorem σ_pos {t j i : ℕ} (ht : t < (Λ).N) (hj : j < k) (hi : i < (Λ).W) :
    σ ((Λ).vRec t ((Λ).offPos j + i)) = ((Λ).posNat R t j).testBit i := by
  rw [σ_vRec hσ ht (offPos_add_lt_RB hj hi)]
  unfold Layout.recBit Layout.offPos
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have h := Nat.mul_add_div_mod_of_lt (j) hi
  rw [show (Λ).C + (Λ).I + (Λ).W * j + i - (Λ).C - (Λ).I = j * (Λ).W + i by
    rw [Nat.mul_comm]; omega, h.1, h.2]

private theorem σ_arrAt {j ℓ w b : ℕ} (hj : j < k) (hℓ : ℓ ≤ (Λ).L) (hw : w < (Λ).N)
    (hb : b < (Λ).P) :
    σ ((Λ).arrAt j ℓ w b) = (Λ).netArr x R j ℓ w b := by
  rw [hσ _ ((Λ).arrAt_lt_AUX hj hℓ hw hb), Layout.σ₀_arrAt x R _ hℓ hw hb]

private theorem σ_vFlag {j ℓ w : ℕ} (hj : j < k) (hℓ : ℓ < (Λ).L) (hw : w < (Λ).N) :
    σ ((Λ).vFlag j ℓ w) = (Λ).netFlag x R j ℓ w := by
  rw [hσ _ ((Λ).vFlag_lt_AUX hj hℓ hw), Layout.σ₀_vFlag x R _ hℓ hw]

omit hσ in
private theorem posNat_bounds (hR : StepRecord.Valid ntm x (Λ).N R) {t j : ℕ} (ht : t < (Λ).N)
    (hj : j < k) : (Λ).N - t ≤ (Λ).posNat R t j ∧ (Λ).posNat R t j ≤ (Λ).N + t ∧
      ((Λ).posNat R t j : ℤ) = (R t).pos ⟨j, hj⟩ + (Λ).N := by
  have h := StepRecord.abs_pos_le hR t ht ⟨j, hj⟩
  rw [abs_le] at h
  unfold Layout.posNat
  rw [dite_eq_left hj]
  omega

end Meanings

section Families

variable {ntm : MultiTapeNTM k Bool State} {κ : ℕ} {x : List Bool} {R : ℕ → StepRecord k State}
  {σ : ℕ → Bool}

local notation "Λ" => layoutOf k State κ x.length
local notation "D" => machineData ntm

omit [Fintype State] in
private theorem action_eta (a : Action k Bool State) :
    (⟨a.inputTape, fun j => ((a.workTapes j).1, (a.workTapes j).2), a.output, a.state⟩ :
      Action k Bool State) = a := by
  cases a
  rfl

omit [Fintype State] in
private theorem ctrlRec_none {t : ℕ} (hs : (R t).state = none) :
    Layout.ctrlRec x R t = ⟨none, StepRecord.inSym x (R t).inPos, 0, none, (R t).out, (R t).reads,
      fun _ => none, fun _ => 0, (R t).reads⟩ := by
  unfold Layout.ctrlRec
  rw [hs]

omit [Fintype State] in
private theorem ctrlRec_some {t : ℕ} {q : State} (hs : (R t).state = some q) :
    Layout.ctrlRec x R t = ⟨some q, StepRecord.inSym x (R t).inPos, (R t).action.inputTape,
      (R t).action.output, (R t).out, (R t).reads, fun j => ((R t).action.workTapes j).1,
      fun j => ((R t).action.workTapes j).2, fun j => (R t).cellAfter j⟩ := by
  unfold Layout.ctrlRec
  rw [hs]

variable (hR : StepRecord.Valid ntm x (layoutOf k State κ x.length).N R)
include hR

/-- **Consecutive records form allowed pairs of finite parts.** -/
private theorem allowed_ctrlRec {t : ℕ} (ht : t + 1 < (Λ).N) :
    Ctrl.Allowed ntm (Layout.ctrlRec x R t) (Layout.ctrlRec x R (t + 1)) := by
  have hf := hR.follows t ht
  unfold StepRecord.Follows at hf
  unfold Ctrl.Allowed
  rcases hs : (R t).state with _ | q
  · simp only [hs] at hf
    rw [ctrlRec_none hs]
    exact ⟨by rw [Layout.ctrlRec_state]; exact hf.1, rfl, rfl,
      by rw [Layout.ctrlRec_out]; exact hf.2.2.2, fun _ => ⟨rfl, rfl, rfl⟩⟩
  · simp only [hs] at hf
    rw [ctrlRec_some hs]
    refine ⟨?_, ?_, fun j => ?_⟩
    · have htr := hR.trans t (by omega) q hs
      simp only [Ctrl.action]
      rw [Layout.ctrlRec_state, hf.1, action_eta]
      exact htr
    · rw [Layout.ctrlRec_out]
      exact hf.2.2.2
    · simp only [StepRecord.cellAfter, hs]

private theorem inPos_succ_ctrlRec {t : ℕ} (ht : t + 1 < (Λ).N) :
    (R (t + 1)).inPos = StepRecord.moveIn x.length (R t).inPos (Layout.ctrlRec x R t).inMove := by
  have hf := hR.follows t ht
  unfold StepRecord.Follows at hf
  rcases hs : (R t).state with _ | q
  · simp only [hs] at hf
    rw [ctrlRec_none hs, hf.2.1]
    exact (moveIn_zero (StepRecord.inPos_le hR t (by omega))).symm
  · simp only [hs] at hf
    rw [ctrlRec_some hs, hf.2.1]

private theorem pos_succ_ctrlRec {t : ℕ} (ht : t + 1 < (Λ).N) (j : Fin k) :
    (R (t + 1)).pos j = (R t).pos j + (((Layout.ctrlRec x R t).move j : SignType) : ℤ) := by
  have hf := hR.follows t ht
  unfold StepRecord.Follows at hf
  rcases hs : (R t).state with _ | q
  · simp only [hs] at hf
    rw [ctrlRec_none hs, hf.2.2.1]
    simp
  · simp only [hs] at hf
    rw [ctrlRec_some hs, hf.2.2.1]

variable (hσ : ∀ v < (layoutOf k State κ x.length).AUX,
  σ v = (layoutOf k State κ x.length).σ₀ x R v)
include hσ

private theorem meaning_init : (Λ).Meaning D x σ .init 0 := by
  simp only [Layout.Meaning, Layout.initLits,
    List.forall_mem_append, Layout.litsHold_fieldLits]
  have hN := (Λ).two_le_N
  refine ⟨⟨⟨fun i hi => ?_, fun i hi => ?_⟩, fun l hl => ?_⟩, fun i hi => ?_⟩
  · have hS : i < stWidth State := by simpa [machineData] using hi
    rw [Nat.zero_add, σ_ctrl hσ (by omega) (by unfold Layout.C; simp; omega), ctrlBit_state _ hS,
      Layout.ctrlRec_state, hR.init_state]
    simp [machineData, List.getD_eq_getElem?_getD, hS]
  · rw [BitString.length_lowBits] at hi
    rw [σ_inPos hσ (by omega) hi, hR.init_inPos, Layout.getD_lowBits hi]
  · obtain ⟨j, hj, hl⟩ := List.mem_flatMap.1 hl
    rw [List.mem_range, layoutOf_k] at hj
    refine ((Λ).litsHold_fieldLits.2 fun i hi => ?_) l hl
    rw [BitString.length_lowBits] at hi
    rw [σ_pos hσ (by omega) hj hi, Layout.getD_lowBits hi]
    obtain ⟨-, -, he⟩ := posNat_bounds hR (t := 0) (by omega) hj
    rw [hR.init_pos] at he
    rw [show (Λ).posNat R 0 j = (Λ).N by omega]
  · rw [Layout.length_two] at hi
    rw [σ_ctrl hσ (by omega) (by unfold Layout.C; simp; omega), layoutOf_S,
      ctrlBit_out _ hi, Layout.ctrlRec_out, hR.init_out, Layout.getD_two _ hi]

private theorem meaning_final : (Λ).Meaning D x σ .final 0 := by
  simp only [Layout.Meaning,
    Layout.finalLits, List.forall_mem_append, Layout.litsHold_fieldLits]
  have hN := (Λ).two_le_N
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have hS : i < stWidth State := by simpa [machineData] using hi
    rw [Nat.zero_add, σ_ctrl hσ (by omega) (by unfold Layout.C; simp; omega), ctrlBit_state _ hS,
      Layout.ctrlRec_state, hR.final_state]
    simp [machineData, List.getD_eq_getElem?_getD, hS]
  · rw [Layout.length_two] at hi
    rw [σ_ctrl hσ (by omega) (by unfold Layout.C; simp; omega), layoutOf_S,
      ctrlBit_out _ hi, Layout.ctrlRec_out, hR.final_out, Layout.getD_two _ hi]

private theorem meaning_step {t : ℕ} (ht : t + 1 < (Λ).N) : (Λ).Meaning D x σ .step t := by
  simp only [Layout.Meaning]
  set c := Layout.ctrlRec x R t
  set c' := Layout.ctrlRec x R (t + 1)
  refine ⟨_, List.mem_map.2 ⟨pairBits c c', List.mem_map.2 ⟨(c, c'),
    mem_allowedPairs.2 (allowed_ctrlRec hR ht), rfl⟩, rfl⟩, ?_⟩
  intro l hl
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hl
  rw [List.mem_range, layoutOf_C] at hi
  simp only [layoutOf_C, pairBits, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]
  by_cases hiC : i < ctrlWidth k State
  · simp only [hiC, ite_true]
    exact σ_ctrl hσ (by omega) (by rw [layoutOf_C]; exact hiC)
  · simp only [hiC, ite_false]
    exact σ_ctrl hσ ht (by rw [layoutOf_C]; omega)

private theorem meaning_inMove {inst : ℕ} (hinst : inst < (Λ).count .inMove) :
    (Λ).Meaning D x σ .inMove inst := by
  simp only [Layout.count] at hinst
  simp only [Layout.Meaning]
  set t := inst / 3 / (Λ).I
  set z := inst / 3 % (Λ).I
  set m := inst % 3
  have hI : 0 < (Λ).I := by unfold Layout.I; omega
  have ht : t + 1 < (Λ).N := by
    have h1 : inst / 3 < ((Λ).N - 1) * (Λ).I := (Nat.div_lt_iff_lt_mul (by norm_num)).2 hinst
    have h2 : t < (Λ).N - 1 := (Nat.div_lt_iff_lt_mul hI).2 h1
    have := (Λ).two_le_N
    omega
  have hz : z < (Λ).I := Nat.mod_lt _ hI
  intro hant
  simp only [Layout.inMoveLits, List.forall_mem_append, Layout.litsHold_fieldLits] at hant
  obtain ⟨h1, h2⟩ := hant
  have hinz : (R t).inPos = z := by
    have hle := StepRecord.inPos_le hR t (by omega)
    have e : ∀ i < (Λ).I, (R t).inPos.testBit i = z.testBit i := fun i hi => by
      have := h1 i (by simpa using hi)
      rwa [σ_inPos hσ (by omega) hi, Layout.getD_lowBits hi] at this
    rw [← bitsVal_testBit (R t).inPos (Λ).I (lt_of_lt_of_le (by unfold Layout.I; simp; omega)
      (Nat.lt_two_pow_self).le), bitsVal_congr e,
      bitsVal_testBit _ _ (lt_of_lt_of_le hz (Nat.lt_two_pow_self).le)]
  have hmv : (Layout.ctrlRec x R t).inMove = Layout.moveCode m := by
    apply moveBit_injective
    intro i hi
    have := h2 i (by simpa using hi)
    rwa [σ_ctrl hσ (by omega) (by unfold Layout.C; simp; omega), layoutOf_S, ctrlBit_inMove _ hi,
      Layout.getD_two _ hi] at this
  rw [Layout.inNextLits, Layout.litsHold_fieldLits]
  intro i hi
  rw [BitString.length_lowBits] at hi
  rw [σ_inPos hσ ht hi, Layout.getD_lowBits hi, inPos_succ_ctrlRec hR ht, hinz, hmv]
  rfl

private theorem meaning_inSym {inst : ℕ} (hinst : inst < (Λ).count .inSym) :
    (Λ).Meaning D x σ .inSym inst := by
  simp only [Layout.count] at hinst
  simp only [Layout.Meaning]
  set t := inst / (Λ).I
  set z := inst % (Λ).I
  have hI : 0 < (Λ).I := by unfold Layout.I; omega
  have ht : t < (Λ).N := (Nat.div_lt_iff_lt_mul hI).2 hinst
  have hz : z < (Λ).I := Nat.mod_lt _ hI
  intro hant
  rw [Layout.inAtLits, Layout.litsHold_fieldLits] at hant
  have hinz : (R t).inPos = z := by
    have hle := StepRecord.inPos_le hR t ht
    have e : ∀ i < (Λ).I, (R t).inPos.testBit i = z.testBit i := fun i hi => by
      have := hant i (by simpa using hi)
      rwa [σ_inPos hσ ht hi, Layout.getD_lowBits hi] at this
    rw [← bitsVal_testBit (R t).inPos (Λ).I (lt_of_lt_of_le (by unfold Layout.I; simp; omega)
      (Nat.lt_two_pow_self).le), bitsVal_congr e,
      bitsVal_testBit _ _ (lt_of_lt_of_le hz (Nat.lt_two_pow_self).le)]
  rw [Layout.inSymLits, Layout.litsHold_fieldLits]
  intro i hi
  rw [Layout.length_two] at hi
  rw [σ_ctrl hσ ht (by unfold Layout.C; simp; omega), layoutOf_S, ctrlBit_inSym _ hi,
    Layout.ctrlRec_inSym, hinz, Layout.getD_two _ hi]

private theorem meaning_head {inst : ℕ} (hinst : inst < (Λ).count .workMove) :
    (Λ).Meaning D x σ .workMove inst := by
  simp only [Layout.count] at hinst
  simp only [Layout.Meaning, layoutOf_k, Layout.length_posPairs]
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [h] at hinst
    · exact h
  set t := inst / k
  set j := inst % k
  have ht : t + 1 < (Λ).N := by
    have h1 : t < (Λ).N - 1 := (Nat.div_lt_iff_lt_mul hk).2 hinst
    have := (Λ).two_le_N
    omega
  have hj : j < k := Nat.mod_lt _ hk
  have hW := (Λ).four_mul_N_eq_two_pow_W
  obtain ⟨hlo, hhi, he⟩ := posNat_bounds hR (t := t) (by omega) hj
  obtain ⟨-, -, he'⟩ := posNat_bounds hR (t := t + 1) ht hj
  have hpos := pos_succ_ctrlRec hR ht ⟨j, hj⟩
  set m := (Layout.ctrlRec x R t).move ⟨j, hj⟩ with hm
  set f := fun i => ((Λ).posNat R t j).testBit i with hf
  have hP : σ ((Λ).vRec t ((Λ).offTape j + 4)) = moveBit m 0 := by
    rw [σ_ctrl hσ (by omega) (offTape_add_lt_C hj (by omega))]
    have := ctrlBit_move (Layout.ctrlRec x R t) ⟨j, hj⟩ (i := 0) (by omega)
    simpa [layoutOf_offTape] using this
  have hQ : σ ((Λ).vRec t ((Λ).offTape j + 5)) = moveBit m 1 := by
    rw [σ_ctrl hσ (by omega) (offTape_add_lt_C hj (by omega))]
    have := ctrlBit_move (Layout.ctrlRec x R t) ⟨j, hj⟩ (i := 1) (by omega)
    simpa [layoutOf_offTape] using this
  intro i hi
  rw [getD_posPairs hi, hP, hQ]
  simp only
  rw [σ_pos hσ ht hj hi]
  rw [addTarget_congr (f' := f) fun j' hj' => by
    show σ (((Λ).posPairs t j).getD j' (0, 0)).1 = _
    rw [getD_posPairs (by omega), σ_pos hσ (by omega) hj (by omega)]]
  have hfv : bitsVal f (Λ).W = (Λ).posNat R t j := bitsVal_testBit _ _ (by omega)
  -- the new position in binary
  rcases hmc : m with _ | _ | _
  · have hnew : (Λ).posNat R (t + 1) j = (Λ).posNat R t j := by
      rw [hmc] at hpos
      have hc : ((SignType.zero : SignType) : ℤ) = 0 := rfl
      rw [hc] at hpos
      omega
    rw [hnew]
    simp [addTarget, moveBit, hf]
  · have hnew : (Λ).posNat R (t + 1) j + 1 = (Λ).posNat R t j := by
      rw [hmc] at hpos
      have hc : ((SignType.neg : SignType) : ℤ) = -1 := rfl
      rw [hc] at hpos
      omega
    have hd := bitsVal_decDigit_add_one f (Λ).W
    have hne : ¬ ∀ j' < (Λ).W, f j' = false := fun hall => by
      rw [bitsVal_congr hall, bitsVal_false] at hfv
      omega
    rw [ite_eq_right hne, hfv] at hd
    have := (Layout.digits_iff (f := decDigit f) (by omega : (Λ).posNat R (t + 1) j <
      2 ^ (Λ).W)).2 (by omega)
    simp only [addTarget, moveBit]
    norm_num
    exact (this i hi).symm
  · have hnew : (Λ).posNat R (t + 1) j = (Λ).posNat R t j + 1 := by
      rw [hmc] at hpos
      have hc : ((SignType.pos : SignType) : ℤ) = 1 := rfl
      rw [hc] at hpos
      omega
    have hd := bitsVal_incDigit f (Λ).W
    rw [hfv, Nat.mod_eq_of_lt (by omega)] at hd
    have := (Layout.digits_iff (f := incDigit f) (by omega : (Λ).posNat R (t + 1) j <
      2 ^ (Λ).W)).2 (by omega)
    simp only [addTarget, moveBit]
    norm_num
    exact (this i hi).symm

omit hR in
private theorem meaning_switch {inst : ℕ} (hinst : inst < (Λ).count .switch) :
    (Λ).Meaning D x σ .switch inst := by
  simp only [Layout.count] at hinst
  simp only [Layout.Meaning]
  have hP : 0 < (Λ).P := by unfold Layout.P; omega
  have hN : 0 < (Λ).N := by have := (Λ).two_le_N; omega
  have hL : 0 < (Λ).L := by
    rcases Nat.eq_zero_or_pos (Λ).L with h | h
    · simp [h] at hinst
    · exact h
  set b := inst % (Λ).P
  set w := inst / (Λ).P % (Λ).N
  set ℓ := inst / (Λ).P / (Λ).N % (Λ).L
  set j := inst / (Λ).P / (Λ).N / (Λ).L
  have hb : b < (Λ).P := Nat.mod_lt _ hP
  have hw : w < (Λ).N := Nat.mod_lt _ hN
  have hℓ : ℓ < (Λ).L := Nat.mod_lt _ hL
  have hj : j < k := by
    have h1 := (Nat.div_lt_iff_lt_mul hP).2 hinst
    have h2 := (Nat.div_lt_iff_lt_mul hN).2 h1
    exact (Nat.div_lt_iff_lt_mul hL).2 h2
  have he := (Λ).expo_lt hℓ
  rw [σ_arrAt hσ hj (by omega) hw hb, σ_arrAt hσ hj (by omega) (partner_lt he hw) hb,
    σ_arrAt hσ hj (by omega) hw hb,
    σ_vFlag hσ hj hℓ (lt_of_le_of_lt (low_le _ _) hw)]
  unfold Layout.netArr Layout.netFlag
  rw [cmpRun_take_succ _ _ _ hℓ]
  unfold swapLayer swapSource
  simp only [Layout.expo]
  generalize cmpFlags (Λ).keyOf (dirFn (Λ).τ true) (schedule (Λ).τ) ((Λ).pay0Val x R j) ℓ _ = c
  cases c <;> rfl

end Families

/-! ### The sorted records -/

section Sorted

variable {ntm : MultiTapeNTM k Bool State} {κ : ℕ} {x : List Bool} {R : ℕ → StepRecord k State}
  {σ : ℕ → Bool}

local notation "Λ" => layoutOf k State κ x.length
local notation "D" => machineData ntm

private theorem recBit_ctrl {t f : ℕ} (hf : f < (Λ).C) :
    (Λ).recBit x R t f = ctrlBit (Layout.ctrlRec x R t) f := by
  unfold Layout.recBit
  rw [ite_eq_left hf]

private theorem recBit_pos {t j i : ℕ} (hi : i < (Λ).W) :
    (Λ).recBit x R t ((Λ).offPos j + i) = ((Λ).posNat R t j).testBit i := by
  unfold Layout.recBit Layout.offPos
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have h := Nat.mul_add_div_mod_of_lt (j) hi
  rw [show (Λ).C + (Λ).I + (Λ).W * j + i - (Λ).C - (Λ).I = j * (Λ).W + i by
    rw [Nat.mul_comm]; omega, h.1, h.2]

private theorem pay0Val_time {j t b : ℕ} (hb : b < (Λ).τ) :
    (Λ).pay0Val x R j t b = t.testBit b := by
  unfold Layout.pay0Val Layout.pay0
  rw [ite_eq_left (by unfold Layout.P; omega), ite_eq_left hb]
  split_ifs with h <;> simp [Layout.σR, vTT, vFF, h]

private theorem pay0Val_pos {j t i : ℕ} (hj : j < k) (_ht : t < (Λ).N) (hi : i < (Λ).W) :
    (Λ).pay0Val x R j t ((Λ).τ + i) = ((Λ).posNat R t j).testBit i := by
  unfold Layout.pay0Val Layout.pay0
  rw [ite_eq_left (by unfold Layout.P; omega), ite_eq_right (by omega), ite_eq_left (by omega),
    Nat.add_sub_cancel_left, Layout.σR_vRec x R _ (offPos_add_lt_RB hj hi), recBit_pos hi]

private theorem pay0Val_read {j t i : ℕ} (hj : j < k) (hi : i < 2) :
    (Λ).pay0Val x R j t ((Λ).τ + (Λ).W + i) = symBit ((R t).reads ⟨j, hj⟩) i := by
  have hC : (Λ).offTape j + i < (Λ).C := offTape_add_lt_C hj (by omega)
  have hRB : (Λ).offTape j + i < (Λ).RB := lt_of_lt_of_le hC (Λ).C_le_RB
  unfold Layout.pay0Val Layout.pay0
  rw [ite_eq_left (by unfold Layout.P; omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_left (by omega), Nat.add_sub_cancel_left, Layout.σR_vRec x R _ hRB, recBit_ctrl hC,
    layoutOf_offTape, ctrlBit_read _ ⟨j, hj⟩ hi, Layout.ctrlRec_read]

private theorem pay0Val_after {j t i : ℕ} (hj : j < k) (hi : i < 2) :
    (Λ).pay0Val x R j t ((Λ).τ + (Λ).W + 2 + i) = symBit ((R t).cellAfter ⟨j, hj⟩) i := by
  have h' : (Λ).offTape j + (6 + i) < (Λ).C := offTape_add_lt_C hj (by omega)
  have hC : (Λ).offTape j + 6 + i < (Λ).C := by omega
  have hRB : (Λ).offTape j + 6 + i < (Λ).RB := lt_of_lt_of_le hC (Λ).C_le_RB
  unfold Layout.pay0Val Layout.pay0
  rw [ite_eq_left (by unfold Layout.P; omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), Nat.add_sub_cancel_left, Layout.σR_vRec x R _ hRB, recBit_ctrl hC,
    layoutOf_offTape, ctrlBit_after _ ⟨j, hj⟩ hi, Layout.ctrlRec_after]

variable (hR : StepRecord.Valid ntm x (layoutOf k State κ x.length).N R)
include hR

private theorem keyOf_pay0Val {j t : ℕ} (hj : j < k) (ht : t < (Λ).N) :
    (Λ).keyOf ((Λ).pay0Val x R j t) = t + 2 ^ (Λ).τ * (Λ).posNat R t j := by
  unfold Layout.keyOf
  rw [bitsVal_add]
  have hW := (Λ).four_mul_N_eq_two_pow_W
  obtain ⟨-, h2, -⟩ := posNat_bounds hR ht hj
  congr 1
  · rw [bitsVal_congr fun b hb => pay0Val_time hb, bitsVal_testBit _ _ ht]
  · congr 1
    rw [bitsVal_congr fun i hi => pay0Val_pos hj ht hi, bitsVal_testBit _ _ (by omega)]

/-- The end of the comparator network of tape `j` permutes the records, with increasing keys. -/
private theorem netArr_sorted {j : ℕ} (hj : j < k) :
    ∃ π : Equiv.Perm (Fin (Λ).N), (∀ w : Fin (Λ).N,
      (Λ).netArr x R j (Λ).L w = (Λ).pay0Val x R j (π w)) ∧
      ∀ u (hu : u < (Λ).N), 0 < u →
        (π ⟨u - 1, by omega⟩ : ℕ) + 2 ^ (Λ).τ * (Λ).posNat R (π ⟨u - 1, by omega⟩) j <
          π ⟨u, hu⟩ + 2 ^ (Λ).τ * (Λ).posNat R (π ⟨u, hu⟩) j := by
  have hsch : ∀ p ∈ schedule (Λ).τ, p.2 < (Λ).τ := fun p hp => by
    have := mem_schedule hp
    omega
  obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin (Λ).N), ∀ w : Fin (Λ).N,
      stage (schedule (Λ).τ) (cmpFlags (Λ).keyOf (dirFn (Λ).τ true) (schedule (Λ).τ)
        ((Λ).pay0Val x R j)) ((Λ).pay0Val x R j) (Λ).L w = (Λ).pay0Val x R j (π w) :=
    exists_perm_stage hsch _ _ _ le_rfl
  have hfinal : ∀ w : Fin (Λ).N, (Λ).netArr x R j (Λ).L w = (Λ).pay0Val x R j (π w) := by
    intro w
    rw [← hπ w, stage_cmpFlags _ _ _ _ (Λ).L le_rfl]
    rfl
  refine ⟨π, hfinal, fun u hu h0 => ?_⟩
  have hmono := monotone_cmpRun_schedule (Λ).keyOf (Λ).τ ((Λ).pay0Val x R j)
  have hcmp : cmpRun (Λ).keyOf (dirFn (Λ).τ true) (schedule (Λ).τ) ((Λ).pay0Val x R j) =
      (Λ).netArr x R j (Λ).L := by
    unfold Layout.netArr Layout.L
    rw [List.take_length]
  rw [hcmp] at hmono
  have hτ : arity (Λ).τ = (Λ).N := arity_eq_two_pow _
  have hle := hmono (show (⟨u - 1, by rw [hτ]; omega⟩ : Fin (arity (Λ).τ)) ≤ ⟨u, by rw [hτ]; omega⟩
    from Fin.mk_le_mk.2 (by omega))
  simp only [Function.comp_apply] at hle
  have e1 : (Λ).netArr x R j (Λ).L (u - 1) = (Λ).pay0Val x R j (π ⟨u - 1, by omega⟩) :=
    hfinal ⟨u - 1, by omega⟩
  have e2 : (Λ).netArr x R j (Λ).L u = (Λ).pay0Val x R j (π ⟨u, hu⟩) := hfinal ⟨u, hu⟩
  rw [e1, e2, keyOf_pay0Val hR hj (π _).isLt, keyOf_pay0Val hR hj (π _).isLt] at hle
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    have hne : (π ⟨u - 1, by omega⟩ : ℕ) ≠ π ⟨u, hu⟩ := fun e =>
      absurd (π.injective (Fin.ext e)) (by simp [Fin.ext_iff]; omega)
    have h1 := congrArg (· % 2 ^ (Λ).τ) heq
    simp only [Nat.add_mul_mod_self_left] at h1
    rw [Nat.mod_eq_of_lt (show ((π ⟨u - 1, by omega⟩ : Fin (Λ).N) : ℕ) < 2 ^ (Λ).τ from
      (π _).isLt), Nat.mod_eq_of_lt (show ((π ⟨u, hu⟩ : Fin (Λ).N) : ℕ) < 2 ^ (Λ).τ from
      (π _).isLt)] at h1
    exact hne h1

variable (hσ : ∀ v < (layoutOf k State κ x.length).AUX,
  σ v = (layoutOf k State κ x.length).σ₀ x R v)
include hσ

private theorem meaning_sorted {inst : ℕ} (hinst : inst < (Λ).count .sorted) :
    (Λ).Meaning D x σ .sorted inst := by
  simp only [Layout.count] at hinst
  simp only [Layout.Meaning]
  have hN : 0 < (Λ).N := by have := (Λ).two_le_N; omega
  set j := inst / (Λ).N
  set u := inst % (Λ).N
  have hj : j < k := (Nat.div_lt_iff_lt_mul hN).2 hinst
  have hu : u < (Λ).N := Nat.mod_lt _ hN
  obtain ⟨π, hfinal, hkey⟩ := netArr_sorted hR hj
  have hP : ∀ b, b < (Λ).τ + (Λ).W + 4 → b < (Λ).P := fun b hb => by unfold Layout.P; omega
  have hσA : ∀ w (hw : w < (Λ).N) b, b < (Λ).τ + (Λ).W + 4 →
      σ ((Λ).arrAt j (Λ).L w b) = (Λ).pay0Val x R j (π ⟨w, hw⟩) b := fun w hw b hb => by
    rw [σ_arrAt hσ hj le_rfl hw (hP b hb)]
    exact congrFun (hfinal ⟨w, hw⟩) b
  set t := π ⟨u, hu⟩ with ht
  -- what the record at sorted position `u` read
  have hpeq : ∀ s < (Λ).N, ∀ s' < (Λ).N, (R s).pos ⟨j, hj⟩ = (R s').pos ⟨j, hj⟩ ↔
      (Λ).posNat R s j = (Λ).posNat R s' j := by
    intro s hs s' hs'
    obtain ⟨-, -, e1⟩ := posNat_bounds hR hs hj
    obtain ⟨-, -, e2⟩ := posNat_bounds hR hs' hj
    omega
  have hsorted := StepRecord.tapeAt_of_sorted R ⟨j, hj⟩ (show (Λ).N ≤ 2 ^ (Λ).τ from le_rfl) π
    (fun s => (Λ).posNat R s j) hpeq hkey t
  have hsymm : (π.symm t : ℕ) = u := by simp [ht]
  have hreads := hR.reads_eq t t.isLt ⟨j, hj⟩
  rw [hsorted] at hreads
  have hreadBit : ∀ i < 2, σ ((Λ).arrAt j (Λ).L u ((Λ).τ + (Λ).W + i)) =
      symBit ((R t).reads ⟨j, hj⟩) i := fun i hi => by
    rw [hσA u hu _ (by omega), pay0Val_read hj hi]
  have hr0 : σ ((Λ).arrAt j (Λ).L u ((Λ).τ + (Λ).W)) = symBit ((R t).reads ⟨j, hj⟩) 0 := by
    simpa using hreadBit 0 (by omega)
  have hr1 := hreadBit 1 (by omega)
  have hposBit : ∀ w (hw : w < (Λ).N), ∀ i < (Λ).W, σ ((Λ).arrAt j (Λ).L w ((Λ).τ + i)) =
      ((Λ).posNat R (π ⟨w, hw⟩) j).testBit i := fun w hw i hi => by
    rw [hσA w hw _ (by omega), pay0Val_pos hj (π _).isLt hi]
  have hsameGet : ∀ i < (Λ).W, ((Λ).samePairs j u).getD i (0, 0) =
      ((Λ).arrAt j (Λ).L (u - 1) ((Λ).τ + i), (Λ).arrAt j (Λ).L u ((Λ).τ + i)) := fun i hi => by
    simp [Layout.samePairs, List.getD_eq_getElem?_getD, hi]
  have hW := (Λ).four_mul_N_eq_two_pow_W
  split_ifs with hu0
  · -- the first sorted record read a blank
    have hnone : (R t).reads ⟨j, hj⟩ = none := by
      rw [hreads, dite_eq_right]
      intro h
      have := h.1
      rw [hsymm] at this
      omega
    rw [hnone] at hr0 hr1
    simp only [hu0] at hr0 hr1
    exact ⟨hr0, hr1⟩
  · have hu1 : u - 1 < (Λ).N := by omega
    set t' := π ⟨u - 1, hu1⟩ with ht'
    -- equal positions in the payloads mean the same cell
    have hsame_iff : (∀ q ∈ (Λ).samePairs j u, σ q.1 = σ q.2) ↔
        (Λ).posNat R t' j = (Λ).posNat R t j := by
      rw [forall_mem_iff_getD (d := (0, 0)) (P := fun q => σ q.1 = σ q.2),
        Layout.length_samePairs]
      obtain ⟨-, h1, -⟩ := posNat_bounds hR t'.isLt hj
      obtain ⟨-, h2, -⟩ := posNat_bounds hR t.isLt hj
      constructor
      · intro h
        rw [← bitsVal_testBit ((Λ).posNat R t' j) (Λ).W (by omega),
          ← bitsVal_testBit ((Λ).posNat R t j) (Λ).W (by omega)]
        refine bitsVal_congr fun i hi => ?_
        have := h i hi
        rw [hsameGet i hi] at this
        change σ ((Λ).arrAt j (Λ).L (u - 1) ((Λ).τ + i)) =
          σ ((Λ).arrAt j (Λ).L u ((Λ).τ + i)) at this
        rwa [hposBit _ hu1 i hi, hposBit _ hu i hi] at this
      · intro h i hi
        rw [hsameGet i hi]
        change σ ((Λ).arrAt j (Λ).L (u - 1) ((Λ).τ + i)) = σ ((Λ).arrAt j (Λ).L u ((Λ).τ + i))
        rw [hposBit _ hu1 i hi, hposBit _ hu i hi]
        exact congrArg (fun v => Nat.testBit v i) h
    have hkeys := hkey u hu (by omega)
    have hidx : ∀ h, π ⟨(π.symm t : ℕ) - 1, h⟩ = t' := fun h => by
      rw [ht']
      congr 1
      ext
      simp only
      rw [hsymm]
    have hcase : (Λ).posNat R t' j = (Λ).posNat R t j →
        (R t).reads ⟨j, hj⟩ = (R t').cellAfter ⟨j, hj⟩ := fun hp => by
      rw [hreads, dite_eq_left ⟨by rw [hsymm]; omega, by rw [hidx]; exact hp⟩, hidx]
    have hcase' : (Λ).posNat R t' j ≠ (Λ).posNat R t j → (R t).reads ⟨j, hj⟩ = none :=
      fun hp => by
        rw [hreads, dite_eq_right]
        intro h
        have := h.2
        rw [hidx] at this
        exact hp this
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- the keys increase
      have e1 : ∀ b < (Λ).τ + (Λ).W, σ (((Λ).keyPairs j u).getD b (0, 0)).1 =
          (Λ).pay0Val x R j t' b := fun b hb => by
        simp only [Layout.keyPairs, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hb, Option.map_some, Option.getD_some]
        exact hσA _ hu1 b (by omega)
      have e2 : ∀ b < (Λ).τ + (Λ).W, σ (((Λ).keyPairs j u).getD b (0, 0)).2 =
          (Λ).pay0Val x R j t b := fun b hb => by
        simp only [Layout.keyPairs, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hb, Option.map_some, Option.getD_some]
        exact hσA _ hu b (by omega)
      rw [Layout.length_keyPairs, bitsVal_congr e1, bitsVal_congr e2]
      have k1 := keyOf_pay0Val hR hj t'.isLt
      have k2 := keyOf_pay0Val hR hj t.isLt
      unfold Layout.keyOf at k1 k2
      rw [k1, k2]
      exact hkeys
    · -- the same cell: what the previous visit left
      intro hsame
      have hcell := hcase (hsame_iff.1 hsame)
      have ha0 : σ ((Λ).arrAt j (Λ).L (u - 1) ((Λ).τ + (Λ).W + 2)) =
          symBit ((R t').cellAfter ⟨j, hj⟩) 0 := by
        rw [hσA _ hu1 _ (by omega)]
        simpa using pay0Val_after (x := x) (R := R) (κ := κ) (t := t') hj (i := 0) (by omega)
      have ha1 : σ ((Λ).arrAt j (Λ).L (u - 1) ((Λ).τ + (Λ).W + 3)) =
          symBit ((R t').cellAfter ⟨j, hj⟩) 1 := by
        rw [hσA _ hu1 _ (by omega)]
        exact pay0Val_after (x := x) (R := R) (κ := κ) (t := t') hj (i := 1) (by omega)
      rw [hr0, hr1, ha0, ha1, hcell]
      exact ⟨rfl, rfl⟩
    · -- a symbol read means the same cell
      intro hr
      rw [hsame_iff]
      by_contra hne
      rw [hr0, hcase' hne] at hr
      simp [symBit] at hr
    · intro hr
      rw [hsame_iff]
      by_contra hne
      rw [hr1, hcase' hne] at hr
      simp [symBit] at hr

end Sorted

/-! ### Every statement -/

section AllMeanings

variable {ntm : MultiTapeNTM k Bool State} {κ : ℕ} {x : List Bool} {R : ℕ → StepRecord k State}
  {σ : ℕ → Bool}

local notation "Λ" => layoutOf k State κ x.length
local notation "D" => machineData ntm

variable (hR : StepRecord.Valid ntm x (layoutOf k State κ x.length).N R)
  (hσ : ∀ v < (layoutOf k State κ x.length).AUX, σ v = (layoutOf k State κ x.length).σ₀ x R v)
include hR hσ

/-- **The assignment of a valid sequence of records makes every statement true.** -/
theorem meaning_of_valid {fam : Family} {inst : ℕ} (hinst : inst < (Λ).count fam) :
    (Λ).Meaning D x σ fam inst := by
  cases fam
  · have : inst = 0 := by simp [Layout.count] at hinst; omega
    subst this
    simp only [Layout.Meaning]
    exact ⟨σ_vTT hσ, σ_vFF hσ⟩
  · have : inst = 0 := by simp [Layout.count] at hinst; omega
    subst this
    exact meaning_init hR hσ
  · have : inst = 0 := by simp [Layout.count] at hinst; omega
    subst this
    exact meaning_final hR hσ
  · have := (Λ).two_le_N
    exact meaning_step hR hσ (by simp [Layout.count] at hinst; omega)
  · exact meaning_inMove hR hσ hinst
  · exact meaning_inSym hR hσ hinst
  · exact meaning_head hR hσ hinst
  · exact meaning_switch hσ hinst
  · exact meaning_sorted hR hσ hinst

end AllMeanings

end Layout

end Cslib.Complexity.CookLevin.Quasilinear
