/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.PolyTime.ConvolutionOperand.Signed
public import CslibFrontier.Computability.PolyTime.CountingLeaf.Raw
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds

/-!
# Signed correction on physical leaf words

`rawCorrection` reads a most-significant-first path, a carry selector and a possibly padded
least-significant-first bit index from the existing counting-leaf encoding. Its native
resource certificate charges the context, count and precision words linearly. Only the path
and bit-index lengths enter the polynomial term.
-/

public section

namespace Cslib.ConvolutionOperand.Signed

open Turing.MultiTapeTM CountingLeaf

/-- The signed correction on raw physical fields; the other query parameters are irrelevant. -/
@[expose] def rawCorrection (x : RawInput) : Bool :=
  correction ⟨0, 0, 0, x.path, ofBits x.bit, x.carry, false⟩

private def localQuery (x : RawInput) : RawInput :=
  ⟨[], [], [], x.path, x.carry, x.bit⟩

private theorem localQuery_inO : ComputableInO localQuery encRawInput encRawInput
    (fun x => (encRawInput x).length) (fun x => (encRawInput x).length) := by
  have h := encRawInput_mk_inO (ComputableInO.const ([] : List Bool))
    (ComputableInO.const ([] : List Bool)) (ComputableInO.const ([] : List Bool))
    encRawInput_path_inO encRawInput_carry_inO encRawInput_bit_inO
  exact h.mono 6 (fun _ => by omega) (fun _ => by omega)

private theorem rawCorrection_polyTime : ComputableInPolyTime rawCorrection encRawInput encBool :=
  computableInPolyTime_correction.comp (encQuery_mk_polyTime
    (ComputableInPolyTime.const 0) (ComputableInPolyTime.const 0) (ComputableInPolyTime.const 0)
    encRawInput_path_deg.computableInPolyTime
    (ComputableInPolyTime.bitsToNat.comp encRawInput_bit_deg.computableInPolyTime)
    encRawInput_carry_deg.computableInPolyTime (ComputableInPolyTime.const false))

/-- One native correction computation has a linear charge for the three unused long fields
and a fixed polynomial charge for the path and raw bit index. The bound includes extraction
and binary normalization, uniformly over all physical words and both carry selectors. -/
theorem computableInO_rawCorrection : ∃ d, ComputableInO rawCorrection encRawInput encBool
    (fun x => x.context.length + x.count.length + x.width.length +
      (x.path.length + x.bit.length + 2) ^ d)
    (fun x => x.context.length + x.count.length + x.width.length +
      (x.path.length + x.bit.length + 2) ^ d) := by
  obtain ⟨dg, eg, hg⟩ := rawCorrection_polyTime.exists_degree
  have h := hg.inO.comp localQuery_inO
  let d := dg + 1
  have hcost (x : RawInput) :
      (encRawInput x).length + ((encRawInput (localQuery x)).length + 1) ^ dg ≤
        (4 ^ dg + 6) * (x.context.length + x.count.length + x.width.length +
          (x.path.length + x.bit.length + 2) ^ d + 1) := by
    let long := x.context.length + x.count.length + x.width.length
    let short := x.path.length + x.bit.length + 2
    have hbase : 1 ≤ short := by dsimp [short]; omega
    have hshort : short ≤ short ^ d := by
      simpa only [pow_one] using Nat.pow_le_pow_right hbase (show 1 ≤ d by dsimp [d]; omega)
    have hfull : (encRawInput x).length ≤ 2 * long + 4 * short := by
      simp only [length_encRawInput, long, short]
      omega
    have hlocal : (encRawInput (localQuery x)).length + 1 ≤ 4 * short := by
      simp only [length_encRawInput, localQuery, List.length_nil, short]
      omega
    have hpow : ((encRawInput (localQuery x)).length + 1) ^ dg ≤ 4 ^ dg * short ^ d := by
      calc
        _ ≤ (4 * short) ^ dg := Nat.pow_le_pow_left hlocal dg
        _ = 4 ^ dg * short ^ dg := mul_pow _ _ _
        _ ≤ _ := Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right hbase (by dsimp [d]; omega))
    change _ ≤ (4 ^ dg + 6) * (long + short ^ d + 1)
    calc
      _ ≤ 2 * long + 4 * short + 4 ^ dg * short ^ d := Nat.add_le_add hfull hpow
      _ ≤ 2 * long + (4 ^ dg + 4) * short ^ d := by
        have hs := Nat.mul_le_mul_left 4 hshort
        rw [Nat.add_mul]
        omega
      _ ≤ (4 ^ dg + 6) * long + (4 ^ dg + 6) * short ^ d :=
        Nat.add_le_add (Nat.mul_le_mul_right long
          ((by decide : 2 ≤ 6).trans (Nat.le_add_left 6 (4 ^ dg))))
          (Nat.mul_le_mul_right (short ^ d) (Nat.add_le_add_left (by decide : 4 ≤ 6) _))
      _ = (4 ^ dg + 6) * (long + short ^ d) := (Nat.mul_add _ _ _).symm
      _ ≤ (4 ^ dg + 6) * (long + short ^ d + 1) :=
        Nat.mul_le_mul_left _ (Nat.le_succ _)
  refine ⟨d, h.mono (4 ^ dg + 6) hcost hcost⟩

end Cslib.ConvolutionOperand.Signed
