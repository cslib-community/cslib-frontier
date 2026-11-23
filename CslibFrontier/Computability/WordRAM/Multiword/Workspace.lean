/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Multiword.Digits
public import CslibFrontier.Tactic.WramOmega.Init
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Tactic.FinIndex

/-!
# Shared workspace for multiword operations

Register zero stores an arithmetic total, register one a carry, register two the half-word
radix, and register three a preserved zero. All operand digits lie outside this workspace.
Multiplication, transfers, bitwise operations and shifts share this layout.

## Main definitions

* `Workspace.total`, `Workspace.carry`, `Workspace.base`, `Workspace.zero`: the four reserved
  workspace registers.
* `Workspace.IsDigit`: a register outside the four reserved registers.
* `Workspace.Frame`: memory and registers outside destinations and arithmetic scratch are kept.
* `Workspace.setup`, `Workspace.setupResult`: initialize the radix and zero in six checked
  instructions, and the resulting machine state.

## Main results

* `Workspace.Frame.digit_regs`, `Workspace.Frame.base_regs`, `Workspace.Frame.zero_regs`,
  `Workspace.Frame.value_eq`, `Workspace.Frame.value_eq_of_digits`,
  `Workspace.Frame.bounded_of_digits`: register and digit-list preservation across a routine frame.
* `Workspace.Frame.cons_step`, `Workspace.Frame.step_cons`: composing a single-digit step with a
  tail routine on `d :: ds` in low-to-high or high-to-low order.
* `Workspace.exec_setup`: exact initialization at every physical width at least two.
* `Workspace.setup_digit`: initialization leaves operand digits unchanged.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword.Workspace

variable {r : ℕ}

/-- Arithmetic total and partial-sum workspace. -/
abbrev total : Fin (r + 4) := ⟨0, by omega⟩
/-- Carry workspace. -/
abbrev carry : Fin (r + 4) := ⟨1, by omega⟩
/-- Half-word radix. -/
abbrev base : Fin (r + 4) := ⟨2, by omega⟩
/-- A preserved zero, used for padding and shifts. -/
abbrev zero : Fin (r + 4) := ⟨3, by omega⟩

/-- Registers outside the four reserved workspace registers. -/
@[wram_arith]
def IsDigit (i : Fin (r + 4)) : Prop := 4 ≤ i.val

/-- Digit registers are disjoint from the four reserved workspace registers. -/
theorem digit_ne {i : Fin (r + 4)} (hi : IsDigit i) :
    i ≠ total ∧ i ≠ carry ∧ i ≠ base ∧ i ≠ zero := by
  fin_index [IsDigit]

/-- A routine changes only its destination digits and the total and carry workspace. -/
def Frame (x y : Data (r + 4)) (ds : List (Fin (r + 4))) : Prop :=
  y.mem = x.mem ∧ ∀ i, i ∉ ds → i ≠ total → i ≠ carry → y.regs i = x.regs i

/-- Enlarging the destination set weakens the preservation requirement. -/
theorem frame_mono {x y : Data (r + 4)} {ds es : List (Fin (r + 4))}
    (h : Frame x y ds) (hsub : ds ⊆ es) : Frame x y es :=
  ⟨h.1, fun i hi ht hc => h.2 i (fun hm => hi (hsub hm)) ht hc⟩

/-- Two routines with the same frame compose. -/
theorem frame_trans {x y z : Data (r + 4)} {ds : List (Fin (r + 4))}
    (h : Frame x y ds) (h' : Frame y z ds) : Frame x z ds :=
  ⟨h'.1.trans h.1, fun i hi ht hc => (h'.2 i hi ht hc).trans (h.2 i hi ht hc)⟩

/-- A routine frame preserves any digit register outside its destination list. -/
theorem Frame.digit_regs {x y : Data (r + 4)} {ds : List (Fin (r + 4))}
    (hf : Frame x y ds) {i : Fin (r + 4)} (hi : IsDigit i) (hid : i ∉ ds) :
    y.regs i = x.regs i :=
  hf.2 i hid (digit_ne hi).1 (digit_ne hi).2.1

/-- A routine whose destinations are all digit registers preserves `base`. -/
theorem Frame.base_regs {x y : Data (r + 4)} {ds : List (Fin (r + 4))}
    (hf : Frame x y ds) (hds : ∀ d ∈ ds, IsDigit d) :
    y.regs base = x.regs base :=
  hf.2 base (fun hm => (digit_ne (hds base hm)).2.2.1 rfl)
    (by simp [base, total]) (by simp [base, carry])

/-- A routine whose destinations are all digit registers preserves `zero`. -/
theorem Frame.zero_regs {x y : Data (r + 4)} {ds : List (Fin (r + 4))}
    (hf : Frame x y ds) (hds : ∀ d ∈ ds, IsDigit d) :
    y.regs zero = x.regs zero :=
  hf.2 zero (fun hm => (digit_ne (hds zero hm)).2.2.2 rfl)
    (by simp [zero, total]) (by simp [zero, carry])

/-- A routine frame preserves the reconstructed value of any register list disjoint from its
destinations and the `total` and `carry` scratch registers. -/
theorem Frame.value_eq {β : ℕ} {x y : Data (r + 4)}
    {ds as : List (Fin (r + 4))} (hf : Frame x y ds)
    (has : ∀ i ∈ as, i ∉ ds ∧ i ≠ total ∧ i ≠ carry) :
    value β y as = value β x as :=
  value_congr fun i hi => hf.2 i (has i hi).1 (has i hi).2.1 (has i hi).2.2

/-- A routine frame preserves the reconstructed value of any disjoint list of digit registers. -/
theorem Frame.value_eq_of_digits {β : ℕ} {x y : Data (r + 4)}
    {ds as : List (Fin (r + 4))} (hf : Frame x y ds)
    (has : ∀ i ∈ as, IsDigit i) (hdis : ∀ i ∈ as, i ∉ ds) :
    value β y as = value β x as :=
  hf.value_eq fun i hi => ⟨hdis i hi, (digit_ne (has i hi)).1, (digit_ne (has i hi)).2.1⟩

/-- A routine frame preserves digit bounds on any disjoint list of digit registers. -/
theorem Frame.bounded_of_digits {β : ℕ} {x y : Data (r + 4)}
    {ds as : List (Fin (r + 4))} (hf : Frame x y ds)
    (has : ∀ i ∈ as, IsDigit i) (hdis : ∀ i ∈ as, i ∉ ds)
    (hb : Bounded β x as) : Bounded β y as :=
  fun i hi => (hf.digit_regs (has i hi) (hdis i hi)).symm ▸ hb i hi

/-- Composing a single-digit step on `d` with a tail routine on `ds` yields a framed, bounded
result on `d :: ds` while preserving `d` across the tail and `ds` across the head step. -/
theorem Frame.cons_step {β : ℕ} {x z y : Data (r + 4)}
    {d : Fin (r + 4)} {ds : List (Fin (r + 4))}
    (hzf : Frame x z [d]) (hyf : Frame z y ds)
    (hd : IsDigit d) (hds : ∀ i ∈ ds, IsDigit i) (hdnot : d ∉ ds)
    (hzd : z.regs d < β) (hyd : Bounded β y ds) :
    y.regs d = z.regs d ∧ value β z ds = value β x ds ∧
      Bounded β y (d :: ds) ∧ Frame x y (d :: ds) := by
  have hyd0 : y.regs d = z.regs d := hyf.digit_regs hd hdnot
  have hdis : ∀ i ∈ ds, i ∉ [d] := fun _ hi hm => hdnot (List.mem_singleton.mp hm ▸ hi)
  refine ⟨hyd0, hzf.value_eq_of_digits hds hdis, fun i hi => ?_,
    frame_trans (frame_mono hzf (by simp)) (frame_mono hyf (by simp))⟩
  rcases List.mem_cons.mp hi with rfl | hi
  · exact hyd0 ▸ hzd
  · exact hyd i hi

/-- Composing a tail routine on `ds` with a single-digit step on `d` yields a framed, bounded
result on `d :: ds` while preserving `ds` across the final step. -/
theorem Frame.step_cons {β : ℕ} {x z y : Data (r + 4)}
    {d : Fin (r + 4)} {ds : List (Fin (r + 4))}
    (hzf : Frame x z ds) (hyf : Frame z y [d])
    (hds : ∀ i ∈ ds, IsDigit i) (hdnot : d ∉ ds)
    (hzb : Bounded β z ds) (hyd : y.regs d < β) :
    Bounded β y (d :: ds) ∧ value β y ds = value β z ds ∧ Frame x y (d :: ds) := by
  have hdis : ∀ i ∈ ds, i ∉ [d] := fun _ hi hm => hdnot (List.mem_singleton.mp hm ▸ hi)
  refine ⟨fun i hi => ?_, hyf.value_eq_of_digits hds hdis,
    frame_trans (frame_mono hzf (by simp)) (frame_mono hyf (by simp))⟩
  rcases List.mem_cons.mp hi with rfl | hi
  · exact hyd
  · exact (hyf.bounded_of_digits hds hdis hzb) i hi

/-- Compute the half-word radix and a preserved zero in six standard instructions. -/
def setup : Code .standard (r + 4) := ram[
  total ← width%;
  carry ← #2;
  base ← total / carry;
  carry ← #1;
  base ← carry <<< base;
  zero ← #0 ]

/-- Exact workspace contents after initialization. -/
def setupResult (w : ℕ) (x : Data (r + 4)) : Data (r + 4) :=
  let y := (((x.set total w).set carry 2).set base (w / 2)).set carry 1
  (y.set base (radix w)).set zero 0

/-- Initialization executes in exactly six instructions for every width at least two. -/
theorem exec_setup {w : ℕ} (hw : 2 ≤ w) (x : Data (r + 4)) :
    Exec w setup x (setupResult w x) 6 := by
  have h2 : Fits w 2 :=
    lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) hw)
  have hshift : 1 <<< (w / 2) = radix w := by rw [Nat.shiftLeft_eq, one_mul]; rfl
  refine WP.Exact.exec ?_
  unfold setup setupResult
  wram_exec [fits_self w, h2, radix_fits hw, hshift]
  rfl

/-- Initialization preserves every register outside the reserved workspace. -/
theorem setup_digit (w : ℕ) (x : Data (r + 4)) {i : Fin (r + 4)}
    (hi : IsDigit i) : (setupResult w x).regs i = x.regs i := by
  obtain ⟨ht, hc, hb, hz⟩ := digit_ne hi
  simp only [setupResult, Data.set_regs, Function.update_apply, ht, hc, hb, hz, ↓reduceIte]

/-- Setting the `total` workspace register preserves the routine frame. -/
theorem frame_set_total (x : Data (r + 4)) (v : ℕ) (ds : List (Fin (r + 4))) :
    Frame x (x.set total v) ds :=
  ⟨rfl, fun _ _ ht _ => by simp only [Data.set_regs, Function.update_of_ne ht]⟩

/-- Setting the `carry` workspace register preserves the routine frame. -/
theorem frame_set_carry (x : Data (r + 4)) (v : ℕ) (ds : List (Fin (r + 4))) :
    Frame x (x.set carry v) ds :=
  ⟨rfl, fun _ _ _ hc => by simp only [Data.set_regs, Function.update_of_ne hc]⟩

/-- Setting a listed destination register preserves the routine frame. -/
theorem frame_set_mem {d : Fin (r + 4)} {ds : List (Fin (r + 4))} (x : Data (r + 4)) (v : ℕ)
    (hd : d ∈ ds := by simp) : Frame x (x.set d v) ds :=
  ⟨rfl, fun i hi _ _ => by
    have hne : i ≠ d := fun h => hi (h ▸ hd)
    simp only [Data.set_regs, Function.update_of_ne hne]⟩

end Cslib.WordRAM.Multiword.Workspace
