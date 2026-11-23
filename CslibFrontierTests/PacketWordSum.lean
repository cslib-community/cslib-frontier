/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.PacketWordSum

/-!
Ordinary-import clients of the packet binary sum. The row example distinguishes the two row
positions, includes an excluded dense mode and a padding code, and checks a nontrivial coefficient.
Empty rows must still enforce the requested exponents. The final examples use the existing
succinct circuit at actual packet coefficient-list outputs.
-/

public section

namespace Cslib.Circuits.Frontier.NativePacket.PacketWordSum.Tests

open Cslib Cslib.Circuits Cslib.Circuits.Frontier TensorNetwork NativePacket FastContraction

private def rowTerm (j : Fin 2) : Option (Fin 2) → ℤ
  | none => if j = 0 then 2 else 7
  | some k => if j = 0 then (if k = 0 then 3 else 5) else (if k = 0 then 11 else 13)

example :
    (∑ a ∈ Finset.range (2 ^ (2 * 2)),
      ∏ v ∈ Finset.range 3, CoeffWordSum.factor 2 2 2 {0} rowTerm (fun _ => 1) a v) = 43 := by
  rw [CoeffWordSum.sum_factor 2 2 2 (by decide)]
  norm_num [listCoeff, List.ofFn_succ, rowTerm, Fin.forall_fin_succ]

-- Both row fields equal code1: choosing the same target twice is legitimate only at exponent2.
/-- Two uses of the same target are counted separately. -/
theorem repeated_target_is_valid : CoeffWordSum.Valid 2 2 2 {0} (fun _ => 2) 5 := by
  unfold CoeffWordSum.Valid
  decide

example : ¬ CoeffWordSum.Valid 2 2 2 {0} (fun _ => 1) 5 := by
  unfold CoeffWordSum.Valid
  decide

-- Code2 selects a nontarget; code3 is padding, even though its decoder returns none.
example : ¬ CoeffWordSum.Valid 2 2 2 {0} (fun _ => 1) 6 := by
  unfold CoeffWordSum.Valid
  decide

example : ¬ CoeffWordSum.Valid 2 2 2 {0} (fun _ => 1) 7 := by
  unfold CoeffWordSum.Valid
  decide

example :
    (∑ a ∈ Finset.range (2 ^ (0 * 1)),
      ∏ v ∈ Finset.range 1,
        CoeffWordSum.factor 1 0 1 {0} (fun j => Fin.elim0 j) (fun _ => 1) a v : ℤ) = 0 := by
  rw [CoeffWordSum.sum_factor 1 0 1 (by decide)]
  norm_num [listCoeff]

example :
    (∑ a ∈ Finset.range (2 ^ (0 * 1)),
      ∏ v ∈ Finset.range 1,
        CoeffWordSum.factor 1 0 1 {0} (fun j => Fin.elim0 j) (fun _ => 0) a v : ℤ) = 1 := by
  rw [CoeffWordSum.sum_factor 1 0 1 (by decide)]
  norm_num [listCoeff]

private def packet : PacketCtx :=
  ⟨1, modulus 0, 1, 2, 0, 2, -1, 1, true, false, true, [], []⟩

-- With no rows, the coefficient of a positive target exponent is zero.
example :
    StoppingQuery.value 0 1 0 2 (PacketWordSum.factor packet [] [1])
      (StoppingQuery.root 0 1 0 2 ⟨0, by decide⟩ ⟨0, by decide⟩) = false := by
  have h := PacketWordSum.value_root 0 packet rfl [] [1] ⟨0, by decide⟩ ⟨0, by decide⟩
  change _ = false at h
  exact h

-- The zero-exponent empty product returns one; it is not removed by an empty row list.
example :
    StoppingQuery.value 0 1 0 2 (PacketWordSum.factor packet [] [])
      (StoppingQuery.root 0 1 0 2 ⟨0, by decide⟩ ⟨0, by decide⟩) = true := by
  have h := PacketWordSum.value_root 0 packet rfl [] [] ⟨0, by decide⟩ ⟨0, by decide⟩
  change _ = true at h
  exact h

-- Arbitrary coefficient queries use the native default zero outside the modulus.
example :
    (Boolean.carryLookaheadAdd 1).eval Boolean.interpretation
      (Boolean.CarrySaveQuery.tree
        (StoppingQuery.WordSum.leaves 0 1 2 (PacketWordSum.factor packet [] []) 100) 0 [])
      ⟨0, by decide⟩ = false := by
  have h := PacketWordSum.bit_sum 0 packet rfl [] [] 100 ⟨0, by decide⟩
  change _ = false at h
  exact h

end Cslib.Circuits.Frontier.NativePacket.PacketWordSum.Tests
