/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.NetGraphTerm

/-!
# The data of an interval from the letter numbers

Numeric forms of the data that `intervalEntryNum` passes to
`localIntervalCount`, read from the letter numbers `L` of the edges: the
control records entering and leaving the interval, the window cells, the
block indices and the moves. Each is stated in the shape the interval count
term needs (codes, offsets by head index, cells by `h * 3b + c`), and proved
to agree with Complexitylib's definitions.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.LocalSim

open Cslib.Turing _root_.Turing _root_.Turing.MultiTapePTM _root_.Turing.MultiTapeNTM.ChoiceTable

variable {k s : ℕ} {State : Type} (e : State ≃ Fin s)

/-- The radix of control records, `b^(k+1) * 3`. -/
def cradix (k b : ℕ) : ℕ := b ^ (k + 1) * 3

/-- The state code of the control record numbered `n`. -/
def ctlSt (k s b n : ℕ) : ℕ := min s (n / cradix k b) % (s + 1)
/-- The offset of head index `c` in the control record numbered `n`. -/
def ctlOff (k b n c : ℕ) : ℕ := n % cradix k b / 3 / b ^ c % b
/-- The track code of the control record numbered `n`. -/
def ctlTr (k b n : ℕ) : ℕ := n % cradix k b % 3

/-- The code of cell `r` of the block contents numbered `n` (blank for a control record). -/
def contCell (k s b n r : ℕ) : ℕ :=
  if n < controlCount k s b then 0 else (n - controlCount k s b) / 3 ^ r % 3

theorem stc_stateOfFin (x : Fin (s + 1)) : stc e (stateOfFin e x) = x := by
  unfold stc stateOfFin; simp

theorem trc_equivFin_symm (x : Fin 3) : trc (OutputTrack.equivFin.symm x) = x := by
  unfold trc; simp

theorem cc_contentsCellNum (b n r : ℕ) :
    cc (contentsCellNum k s b n r) = contCell k s b n r := by
  unfold contentsCellNum contCell
  split_ifs
  · rfl
  · unfold cc; simp

theorem decodeControlData_codes (b n : ℕ) :
    stc e (decodeControlData (k := k) e b n).1 = ctlSt k s b n ∧
      (∀ head : Option (Fin k), (decodeControlData (k := k) e b n).2.1 head =
        ctlOff k b n ((finSuccEquiv k).symm head)) ∧
      trc (decodeControlData (k := k) e b n).2.2 = ctlTr k b n := by
  refine ⟨stc_stateOfFin e _, fun _ => rfl, trc_equivFin_symm _⟩

/-! ### Entering control records -/

/-- The state code entering interval `i`. -/
def inSt (k s b init : ℕ) (L : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i = 0 then init else if L (i - 1) < controlCount k s b then ctlSt k s b (L (i - 1)) else 0
/-- The offset of head index `c` entering interval `i`. -/
def inOff (k s b : ℕ) (L : ℕ → ℕ) (i c : ℕ) : ℕ :=
  if i = 0 then 0 else if L (i - 1) < controlCount k s b then ctlOff k b (L (i - 1)) c else 0
/-- The track code entering interval `i`. -/
def inTr (k s b : ℕ) (L : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i = 0 then 0 else if L (i - 1) < controlCount k s b then ctlTr k b (L (i - 1)) else 0

theorem inControl_codes (b : ℕ) (initial : State) (L : ℕ → ℕ) (i : ℕ) :
    stc e (inControlNum (k := k) e b initial L i).1 = inSt k s b (stc e (some initial)) L i ∧
      (∀ head : Option (Fin k), (inControlNum (k := k) e b initial L i).2.1 head =
        inOff k s b L i ((finSuccEquiv k).symm head)) ∧
      trc (inControlNum (k := k) e b initial L i).2.2 = inTr k s b L i := by
  unfold inControlNum inSt inOff inTr
  by_cases hi : i = 0
  · simp only [hi, ite_true]
    exact ⟨by trivial, fun _ => by trivial, by rfl⟩
  · simp only [hi, ite_false]
    unfold controlDataOfNum
    by_cases hc : L (i - 1) < controlCount k s b
    · simp only [hc, ite_true]; exact decodeControlData_codes e b _
    · simp only [hc, ite_false]
      exact ⟨by rfl, fun _ => by trivial, by rfl⟩

/-! ### Window cells -/

/-- The code of cell `c` of the window of work tape `h` entering interval `i`. -/
def inCell (k q s b σ : ℕ) (L : ℕ → ℕ) (i h c : ℕ) : ℕ :=
  let lb := optCode (lastBeforeNum k σ (h + 1) i (c / b))
  if lb = 0 then 0
  else contCell k s b (L (q + (portOfNum k σ (h + 1) i (lb - 1) (c / b) + 3 * h + k * 3 *
      (lb - 1))))
    (c % b)

/-- The code of cell `c` of the window of work tape `h` leaving interval `i`. -/
def outCell (k q s b : ℕ) (L : ℕ → ℕ) (i h c : ℕ) : ℕ :=
  contCell k s b (L (q + (c / b + 3 * h + k * 3 * i))) (c % b)

theorem inCellsNum_getD (k q s b σ : ℕ) (L : ℕ → ℕ) (i h c : ℕ) (hc : c < 3 * b) :
    cc ((inCellsNum k q s b σ L i h).getD c none) = inCell k q s b σ L i h c := by
  unfold inCellsNum inCell
  rw [List.getD_eq_getElem _ _ (by simpa using hc)]
  simp only [List.getElem_map, List.getElem_range]
  cases hl : lastBeforeNum k σ (h + 1) i (c / b) with
  | none => rfl
  | some i' => simp [optCode, cc_contentsCellNum]

theorem outCellsNum_getD (k q s b : ℕ) (L : ℕ → ℕ) (i h c : ℕ) (hc : c < 3 * b) :
    cc ((outCellsNum k q s b L i h).getD c none) = outCell k q s b L i h c := by
  unfold outCellsNum outCell
  rw [List.getD_eq_getElem _ _ (by simpa using hc)]
  simp only [List.getElem_map, List.getElem_range, cc_contentsCellNum]

theorem length_inCellsNum (k q s b σ : ℕ) (L : ℕ → ℕ) (i h : ℕ) :
    (inCellsNum k q s b σ L i h).length = 3 * b := by simp [inCellsNum]

theorem length_outCellsNum (k q s b : ℕ) (L : ℕ → ℕ) (i h : ℕ) :
    (outCellsNum k q s b L i h).length = 3 * b := by simp [outCellsNum]

/-! ### Block indices and moves -/

theorem blockIndexNum_none (σ i : ℕ) :
    blockIndexNum k σ i none = (digitCount k σ 0 2 i : ℤ) - digitCount k σ 0 0 i := by
  simp [blockIndexNum]

theorem sgnCode_blockMoveNum (σ i : ℕ) (head : Option (Fin k)) :
    sgnCode (blockMoveNum k σ i head) =
      σ / 3 ^ (((finSuccEquiv k).symm head : ℕ) + (k + 1) * i) % 3 := by
  unfold blockMoveNum
  have key : ∀ x : Fin 3, sgnCode (signEquiv.symm x) = x := by
    intro x; fin_cases x <;> rfl
  exact key _

theorem finSuccEquiv_symm_none : (((finSuccEquiv k).symm none : Fin (k + 1)) : ℕ) = 0 := by simp

theorem finSuccEquiv_symm_some (h : Fin k) :
    (((finSuccEquiv k).symm (some h) : Fin (k + 1)) : ℕ) = h + 1 := by simp

theorem inOff_lt {b : ℕ} (hb : 0 < b) (L : ℕ → ℕ) (i c : ℕ) : inOff k s b L i c < b := by
  unfold inOff ctlOff
  split_ifs
  · exact hb
  · exact Nat.mod_lt _ hb
  · exact hb

end Cslib.Complexity.NtimeDspace.LocalSim
