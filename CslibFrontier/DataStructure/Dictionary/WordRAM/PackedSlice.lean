/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.BitPackedArray

/-!
# Parametric view and frame lemmas for disjoint bit-packed slices

Companion to `BitPackedArray.lean` giving reusable congruence and disjoint-region frame lemmas
for bounded bit-packed array views `fun i => if i < len then readPacked base k w mem i else 0`,
together with `readPacked_writePacked_bounded` in `BitPackedArray.lean`.

Keeping these theorems parameterized by `(base, k, w, len)` lets metadata layout files such as
`ResizableSuccinct.MetaSync` collapse repeated `write*_effect` theorems into compact instantiations
instead of repeating `funext`/`split_ifs`/`writePacked_outside` boilerplate.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.WriteOutside`:
  witnesses that a memory update leaves all words outside `[lo, hi)` unchanged.
* `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.DisjointIntervals`:
  two half-open word intervals `[lo₁, hi₁)` and `[lo₂, hi₂)` do not overlap.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.writePacked_writeOutside`:
  `writePacked` at `idx < len` writes only within `[lo, hi)` when
  `[base, base + packedWords len k w) ⊆ [lo, hi)`.
* `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.packedView_congr`:
  a bounded packed view depends only on `[base, base + packedWords len k w)`.
* `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray.packedView_writePacked_disjoint`:
  writing inside a disjoint packed slice preserves a read-only view.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray

/-- A word-memory write whose effect is confined to the half-open interval `[lo, hi)`. -/
structure WriteOutside (lo hi : ℕ) (mem mem' : ℕ → ℕ) : Prop where
  /-- Every word outside `[lo, hi)` is preserved. -/
  eq_outside : ∀ a, ¬(lo ≤ a ∧ a < hi) → mem' a = mem a

/-- Two half-open word intervals `[lo₁, hi₁)` and `[lo₂, hi₂)` are disjoint. -/
@[expose]
def DisjointIntervals (lo₁ hi₁ lo₂ hi₂ : ℕ) : Prop :=
  hi₁ ≤ lo₂ ∨ hi₂ ≤ lo₁

/-- Symmetry of `DisjointIntervals`. -/
theorem DisjointIntervals.symm {lo₁ hi₁ lo₂ hi₂ : ℕ}
    (h : DisjointIntervals lo₁ hi₁ lo₂ hi₂) : DisjointIntervals lo₂ hi₂ lo₁ hi₁ :=
  Or.symm h

/-- A write confined to `[lo, hi)` agrees with the original memory across any disjoint interval
`[lo', hi')`. -/
theorem WriteOutside.eq_on_disjoint {lo hi lo' hi' : ℕ} {mem mem' : ℕ → ℕ}
    (h : WriteOutside lo hi mem mem') (hdisj : DisjointIntervals lo hi lo' hi') :
    ∀ a, lo' ≤ a ∧ a < hi' → mem' a = mem a := fun a ⟨_, _⟩ =>
  h.eq_outside a fun ⟨_, _⟩ => by rcases hdisj with hd | hd <;> omega

/-- Writing at `idx < len` in a packed array at `base` is confined to any `[lo, hi)` containing
`[base, base + packedWords len k w)`. -/
theorem writePacked_writeOutside {base len k w idx val lo hi : ℕ}
    (hw : 0 < w) (hidx : idx < len) (hlo : lo ≤ base)
    (hhi : base + packedWords len k w ≤ hi) (mem : ℕ → ℕ) :
    WriteOutside lo hi mem (writePacked base k w mem idx val) :=
  ⟨fun _ ha => writePacked_outside hw mem hidx val fun _ => ha ⟨by omega, by omega⟩⟩

/-- A bounded `k`-bit packed array view `if i < len then readPacked base k w mem i else 0` depends
only on the half-open word interval `[base, base + packedWords len k w)`. -/
theorem packedView_congr {base k w len : ℕ} (hw : 0 < w) {mem₁ mem₂ : ℕ → ℕ}
    (h : ∀ addr, base ≤ addr ∧ addr < base + packedWords len k w → mem₁ addr = mem₂ addr) :
    (fun i => if i < len then readPacked base k w mem₁ i else 0) =
      (fun i => if i < len then readPacked base k w mem₂ i else 0) := by
  funext i
  split_ifs with hi
  · exact readPacked_congr hw h hi
  · rfl

/-- Writing inside a packed slice disjoint from `[base₁, base₁ + packedWords len₁ k₁ w)` leaves the
bounded view at `base₁` unchanged. -/
theorem packedView_writePacked_disjoint {base₁ k₁ len₁ base₂ k₂ len₂ w idx val : ℕ}
    (hw : 0 < w) (hidx : idx < len₂)
    (hdisj : DisjointIntervals base₁ (base₁ + packedWords len₁ k₁ w)
      base₂ (base₂ + packedWords len₂ k₂ w))
    (mem : ℕ → ℕ) :
    (fun i => if i < len₁ then
        readPacked base₁ k₁ w (writePacked base₂ k₂ w mem idx val) i else 0) =
      (fun i => if i < len₁ then readPacked base₁ k₁ w mem i else 0) :=
  packedView_congr hw <|
    (writePacked_writeOutside hw hidx le_rfl le_rfl mem).eq_on_disjoint hdisj.symm

end Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray

end
