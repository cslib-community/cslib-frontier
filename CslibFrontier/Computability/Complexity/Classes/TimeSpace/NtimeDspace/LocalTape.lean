/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ExplicitBlockNetwork.Table

/-!
# Work tapes as three numbers

A finite tape (`Cslib.Turing.BiTape Bool`) is represented by three natural
numbers: the code of the head cell, and the cells to the left and to the right
of the head as base-3 digits (nearest cell first). Blank is code `0`, so cells
beyond the stored digits read as blank, and the representation needs no range
invariant. Writes and moves act on the three numbers by a few arithmetic
operations (`NTape.step`), and `Rep.step` shows they track `BiTape.step`
exactly. `NTape.ofCells` is the representation of `BiTape.ofCells`.

`packDigits` (digits `a i` in radix `R`) and its digit extraction lemma are
used both here and to pack whole configurations.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.LocalSim

open Cslib.Turing _root_.Turing.MultiTapePTM

/-! ### Digits -/

/-- The number with digits `a 0, …, a (m-1)` in radix `R`. -/
def packDigits (R : ℕ) (a : ℕ → ℕ) (m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, a i * R ^ i

theorem packDigits_succ' (R : ℕ) (a : ℕ → ℕ) (m : ℕ) :
    packDigits R a (m + 1) = a 0 + R * packDigits R (fun i => a (i + 1)) m := by
  unfold packDigits
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, mul_one, pow_succ]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Digit extraction.** -/
theorem packDigits_div_pow_mod {R : ℕ} (hR : 0 < R) :
    ∀ (m : ℕ) (a : ℕ → ℕ), (∀ i < m, a i < R) → ∀ p,
      packDigits R a m / R ^ p % R = if p < m then a p else 0 := by
  intro m
  induction m with
  | zero => intro a _ p; simp [packDigits]
  | succ m ih =>
    intro a ha p
    rw [packDigits_succ']
    have ha' : ∀ i < m, a (i + 1) < R := fun i hi => ha (i + 1) (by omega)
    cases p with
    | zero =>
      simp only [pow_zero, Nat.div_one, Nat.add_mul_mod_self_left]
      rw [Nat.mod_eq_of_lt (ha 0 (by omega))]
      simp
    | succ p =>
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
      rw [show (a 0 + R * packDigits R (fun i => a (i + 1)) m) / R =
          packDigits R (fun i => a (i + 1)) m by
        rw [Nat.add_mul_div_left _ _ hR, Nat.div_eq_of_lt (ha 0 (by omega)), zero_add]]
      rw [ih _ ha' p]
      by_cases hp : p < m
      · simp [hp]
      · simp [hp]

theorem packDigits_lt {R : ℕ} (_hR : 0 < R) :
    ∀ (m : ℕ) (a : ℕ → ℕ), (∀ i < m, a i < R) → packDigits R a m < R ^ m := by
  intro m
  induction m with
  | zero => intro a _; simp [packDigits]
  | succ m ih =>
    intro a ha
    rw [packDigits_succ', pow_succ']
    have h1 := ih (fun i => a (i + 1)) fun i hi => ha (i + 1) (by omega)
    have h0 := ha 0 (by omega)
    nlinarith

/-! ### Cell codes -/

/-- The code of a cell: blank `0`, `false` `1`, `true` `2`. -/
def cc (c : Option Bool) : ℕ := (Turing.MultiTapePTM.cellEquiv c : ℕ)

@[simp] theorem cc_none : cc none = 0 := rfl
@[simp] theorem cc_false : cc (some false) = 1 := rfl
@[simp] theorem cc_true : cc (some true) = 2 := rfl

theorem cc_lt (c : Option Bool) : cc c < 3 := (Turing.MultiTapePTM.cellEquiv c).isLt

theorem cc_inj {c c' : Option Bool} (h : cc c = cc c') : c = c' := by
  rcases c with _ | _ | _ <;> rcases c' with _ | _ | _ <;> simp_all

/-! ### Numeric tapes -/

/-- A tape as the head code and the left and right cells as base-3 numbers. -/
abbrev NTape := ℕ × ℕ × ℕ

/-- The code of the cell at displacement `d`. -/
def NTape.read (t : NTape) : ℤ → ℕ
  | .ofNat 0 => t.1
  | .ofNat (p + 1) => t.2.2 / 3 ^ p % 3
  | .negSucc p => t.2.1 / 3 ^ p % 3

/-- Write a cell code under the head. -/
def NTape.write (t : NTape) (c : ℕ) : NTape := (c, t.2.1, t.2.2)

def NTape.moveRight (t : NTape) : NTape := (t.2.2 % 3, t.2.1 * 3 + t.1, t.2.2 / 3)

def NTape.moveLeft (t : NTape) : NTape := (t.2.1 % 3, t.2.1 / 3, t.2.2 * 3 + t.1)

/-- The numeric form of `BiTape.step`. -/
def NTape.step (t : NTape) (action : Option (Option Bool) × SignType) : NTape :=
  let written := action.1.elim t fun c => t.write (cc c)
  match action.2 with
  | .neg => written.moveLeft
  | .zero => written
  | .pos => written.moveRight

/-- A numeric tape represents a tape when every cell has its code. -/
def Rep (tape : BiTape Bool) (t : NTape) : Prop := ∀ d, cc (tape.read d) = t.read d

theorem Rep.head_lt {tape : BiTape Bool} {t : NTape} (h : Rep tape t) : t.1 < 3 := by
  have := h 0
  simp only [NTape.read] at this
  rw [← this]; exact cc_lt _

theorem Rep.moveRight {tape : BiTape Bool} {t : NTape} (h : Rep tape t) :
    Rep tape.moveRight t.moveRight := by
  have h3 := h.head_lt
  intro d
  rw [BiTape.read_moveRight, h]
  rcases d with (_ | p) | p
  · simp [NTape.read, NTape.moveRight]
  · change t.2.2 / 3 ^ (p + 1) % 3 = t.2.2 / 3 / 3 ^ p % 3
    rw [Nat.div_div_eq_div_mul, pow_succ']
  · cases p with
    | zero =>
      change t.read 0 = (t.2.1 * 3 + t.1) / 3 ^ 0 % 3
      simp only [NTape.read, pow_zero, Nat.div_one]
      omega
    | succ p =>
      have : Int.negSucc (p + 1) + 1 = Int.negSucc p := by omega
      rw [this]
      change t.2.1 / 3 ^ p % 3 = (t.2.1 * 3 + t.1) / 3 ^ (p + 1) % 3
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
      congr 2
      omega

theorem Rep.moveLeft {tape : BiTape Bool} {t : NTape} (h : Rep tape t) :
    Rep tape.moveLeft t.moveLeft := by
  have h3 := h.head_lt
  intro d
  rw [BiTape.read_moveLeft, h]
  rcases d with (_ | p) | p
  · change t.read (-1) = t.2.1 % 3
    change t.2.1 / 3 ^ 0 % 3 = t.2.1 % 3
    simp
  · cases p with
    | zero =>
      change t.read 0 = (t.2.2 * 3 + t.1) / 3 ^ 0 % 3
      simp only [NTape.read, pow_zero, Nat.div_one]
      omega
    | succ p =>
      have : Int.ofNat (p + 1 + 1) - 1 = Int.ofNat (p + 1) := by
        simp only [Int.ofNat_eq_natCast]; omega
      rw [this]
      change t.2.2 / 3 ^ p % 3 = (t.2.2 * 3 + t.1) / 3 ^ (p + 1) % 3
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
      congr 2
      omega
  · have : Int.negSucc p - 1 = Int.negSucc (p + 1) := by omega
    rw [this]
    change t.2.1 / 3 ^ (p + 1) % 3 = t.2.1 / 3 / 3 ^ p % 3
    rw [Nat.div_div_eq_div_mul, pow_succ']

theorem Rep.write {tape : BiTape Bool} {t : NTape} (h : Rep tape t) (c : Option Bool) :
    Rep (tape.write c) (t.write (cc c)) := by
  intro d
  rw [BiTape.read_write]
  split_ifs with hd
  · subst hd; rfl
  · rw [h]
    rcases d with (_ | p) | p
    · exact absurd rfl hd
    · rfl
    · rfl

/-- **Numeric steps track tape steps.** -/
theorem Rep.step {tape : BiTape Bool} {t : NTape} (h : Rep tape t)
    (action : Option (Option Bool) × SignType) : Rep (tape.step action) (t.step action) := by
  rcases action with ⟨w, m⟩
  have hw : Rep (w.elim tape tape.write) (w.elim t fun c => t.write (cc c)) := by
    cases w with
    | none => exact h
    | some c => exact h.write c
  cases m
  · exact hw
  · exact hw.moveLeft
  · exact hw.moveRight

/-- The numeric form of `BiTape.ofCells`. -/
def NTape.ofCells (cells : List (Option Bool)) (pos : ℕ) : NTape :=
  (cc (cells.getD pos none),
    packDigits 3 (fun i => cc (cells.getD (pos - 1 - i) none)) pos,
    packDigits 3 (fun i => cc (cells.getD (pos + 1 + i) none)) cells.length)

theorem rep_ofCells (cells : List (Option Bool)) (pos : ℕ) :
    Rep (BiTape.ofCells cells pos) (NTape.ofCells cells pos) := by
  intro d
  rw [BiTape.read_ofCells]
  rcases d with (_ | p) | p
  · simp [NTape.read, NTape.ofCells]
  · change _ = packDigits 3 (fun i => cc (cells.getD (pos + 1 + i) none)) cells.length / 3 ^ p % 3
    rw [packDigits_div_pow_mod (by norm_num) _ _ (fun i _ => cc_lt _)]
    have h0 : 0 ≤ (pos : ℤ) + Int.ofNat (p + 1) := by simp only [Int.ofNat_eq_natCast]; omega
    have ht : ((pos : ℤ) + Int.ofNat (p + 1)).toNat = pos + 1 + p := by
      simp only [Int.ofNat_eq_natCast]; omega
    rw [ite_eq_left h0, ht]
    split_ifs with hp
    · rfl
    · rw [List.getD_eq_default _ _ (by omega)]; rfl
  · change _ = packDigits 3 (fun i => cc (cells.getD (pos - 1 - i) none)) pos / 3 ^ p % 3
    rw [packDigits_div_pow_mod (by norm_num) _ _ (fun i _ => cc_lt _)]
    by_cases hp : p < pos
    · have h0 : 0 ≤ (pos : ℤ) + Int.negSucc p := by simp only [Int.negSucc_eq]; omega
      have ht : ((pos : ℤ) + Int.negSucc p).toNat = pos - 1 - p := by
        simp only [Int.negSucc_eq]; omega
      rw [ite_eq_left h0, ht, ite_eq_left hp]
    · have h0 : ¬ 0 ≤ (pos : ℤ) + Int.negSucc p := by simp only [Int.negSucc_eq]; omega
      rw [ite_eq_right h0, ite_eq_right hp]; rfl

/-- Bounds: the stored numbers grow by at most one digit per step. -/
theorem NTape.step_bound {t : NTape} {W : ℕ} (h1 : t.1 < 3) (hl : t.2.1 < 3 ^ W)
    (hr : t.2.2 < 3 ^ W) (action : Option (Option Bool) × SignType) :
    (t.step action).1 < 3 ∧ (t.step action).2.1 < 3 ^ (W + 1) ∧
      (t.step action).2.2 < 3 ^ (W + 1) := by
  rcases action with ⟨w, m⟩
  have hw : (w.elim t fun c => t.write (cc c)).1 < 3 ∧
      (w.elim t fun c => t.write (cc c)).2.1 = t.2.1 ∧
      (w.elim t fun c => t.write (cc c)).2.2 = t.2.2 := by
    cases w with
    | none => exact ⟨h1, rfl, rfl⟩
    | some c => exact ⟨cc_lt c, rfl, rfl⟩
  obtain ⟨a, b, c⟩ := hw
  have hW : 3 ^ W ≤ 3 ^ (W + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hW3 : 3 ^ (W + 1) = 3 ^ W * 3 := pow_succ 3 W
  cases m <;> simp only [NTape.step, NTape.moveLeft, NTape.moveRight]
  · exact ⟨a, by omega, by omega⟩
  · refine ⟨Nat.mod_lt _ (by norm_num), by omega, by omega⟩
  · refine ⟨Nat.mod_lt _ (by norm_num), by omega, by omega⟩

end Cslib.Complexity.NtimeDspace.LocalSim
