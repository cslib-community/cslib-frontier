/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.PacketPacking
public import CslibFrontier.Foundations.Combinatorics.SeededPackingRank
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# Native packet and slot from binary seed labels and rank

One edge's two seeded labels are integers with six bits per alphabet-64 coordinate.
Expanding just those two labels and using the binary class rank recovers the original
packing's packet and slot numbers. The work is polynomial in the number of coordinates
and the bit lengths of the labels and rank.
-/

public section

namespace Cslib.SeededPacketLocation

open PacketPacking BalancedSchedules Turing.MultiTapeTM ComputableInPolyTime

/-- The two integer label codes, together with their coordinate count and the edge's rank. -/
structure Input where
  /-- Number of alphabet-64 coordinates in each label. -/
  labelLength : ℕ
  /-- Row label code. -/
  row : ℕ
  /-- Column label code. -/
  column : ℕ
  /-- Class rank from the verified predecessor count. -/
  rank : ℕ

/-- Unary coordinate count, binary row, column and rank. -/
enc_structure encInput : Input where
  labelLength : encUnary, row : encNat, column : encNat, rank : encNat

/-- On two genuine labels and a `w`-bit rank guess, the complete local word has length
linear in the label and rank widths. -/
theorem length_encInput_le (p : Input) {w : ℕ} (hr : p.row < 2 ^ (6 * p.labelLength))
    (hc : p.column < 2 ^ (6 * p.labelLength)) (hg : p.rank < 2 ^ w) :
    (encInput p).length ≤ 26 * p.labelLength + w + 3 := by
  have hx := Nat.size_le.mpr hr
  have hy := Nat.size_le.mpr hc
  have hz := Nat.size_le.mpr hg
  simp [encInput_apply, encInputFields, encNat_apply, Nat.size_eq_bits_len]
  omega

/-- Least-significant radix-64 coordinates of the supplied code, including zero padding. -/
@[expose] def digits (a value : ℕ) : List ℕ :=
  (List.range a).map fun i => value / 64 ^ i % 64

/-- Compute the exact packet and slot used by the ordinary packing from its two local words. -/
@[expose] def run (p : Input) : ℕ × ℕ :=
  let row := digits p.labelLength p.row
  let col := digits p.labelLength p.column
  (packetOf p.labelLength 64 row col p.rank, slotOf p.labelLength row col p.rank)

/-- Decoding an in-range label code gives the packing's label digits in the same order. -/
theorem digits_wordEquiv (a : ℕ) (v : Fin (2 ^ (6 * a))) :
    digits a v.val = scheduleToWord (Seeded.wordEquiv a v) := by
  apply List.ext_getElem (by simp [digits, scheduleToWord])
  intro i h₁ h₂
  simp [digits, scheduleToWord, Seeded.wordEquiv, finFunctionFinEquiv_symm_apply_val]

/-- The two output numbers are exactly the ordered packing's packet and slot, on any
finite linearly ordered edge universe and any pair of endpoint code maps. -/
theorem run_of_codes {E R C : Type*} [Fintype E] [LinearOrder E]
    (a : ℕ) (rows : E → R) (cols : E → C)
    (ρ : R → Fin (2 ^ (6 * a))) (κ : C → Fin (2 ^ (6 * a))) (e : E) :
    let row := fun v => Seeded.wordEquiv a (ρ v)
    let col := fun v => Seeded.wordEquiv a (κ v)
    run ⟨a, (ρ (rows e)).val, (κ (cols e)).val, classIndex rows cols row col e⟩ =
      (((Packing.ofLabels rows cols row col).packet e).val,
        ((Packing.ofLabels rows cols row col).slot e).val) := by
  dsimp only [run]
  rw [digits_wordEquiv a (ρ (rows e)), digits_wordEquiv a (κ (cols e))]
  let row : R → Fin a → Fin 64 := fun v => Seeded.wordEquiv a (ρ v)
  let col : C → Fin a → Fin 64 := fun v => Seeded.wordEquiv a (κ v)
  exact congrArg₂ Prod.mk (packetOf_eq (a := a) (r := 64) rows cols row col e)
    (slotOf_eq (a := a) (r := 64) rows cols row col e)

private theorem digits_polyTime {α : Type} {enc : α ↪ List Bool} {a value : α → ℕ}
    (hw : ComputableInPolyTime a enc encUnary) (hv : ComputableInPolyTime value enc encNat) :
    ComputableInPolyTime (fun p => digits (a p) (value p)) enc (encList encNat) := by
  apply mapWithInput (range.comp hw)
  have hi := ComputableInPolyTime.snd enc encUnary
  have hx := hv.comp (ComputableInPolyTime.fst enc encUnary)
  exact binary_mod' (binary_div' hx (binary_pow' (const 64) hi)) (const 64)

/-- Both local placements have native polynomial cost even for numerically large class ranks. -/
theorem computableInPolyTime_run : ComputableInPolyTime run encInput (encPair encNat encNat) := by
  have ha := encInput_labelLength_deg.computableInPolyTime
  have hr := digits_polyTime ha encInput_row_deg.computableInPolyTime
  have hc := digits_polyTime ha encInput_column_deg.computableInPolyTime
  let argument (p : Input) : ((ℕ × ℕ) × (List ℕ × List ℕ)) × ℕ :=
    (((p.labelLength, 64), (digits p.labelLength p.row, digits p.labelLength p.column)), p.rank)
  have harg : ComputableInPolyTime argument encInput encEdgeIn :=
    ((ha.prod (const 64)).prod (hr.prod hc)).prod encInput_rank_deg.computableInPolyTime
  have hp := PacketPacking.computableInPolyTime_packetOf.comp (g := argument) harg
  have hs := PacketPacking.computableInPolyTime_slotOf.comp (g := argument) harg
  exact (hp.prod hs).of_enc_eq (fun _ => rfl)

end Cslib.SeededPacketLocation
