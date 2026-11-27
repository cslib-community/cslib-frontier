/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.SaksZhou.SweepSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.InputBit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.StoredBind
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.BitsGetElem
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Read-only access to the Saks–Zhou base matrix

The source ID determines the sole input position read by both fair-coin transitions.
Storing its binary index lets the machine read the selected input symbol without charging
the whole input word. At positive precision each matching transition contributes half of the
dyadic denominator.
-/

public section

namespace Turing.MultiTapePTM.ConfigurationGraph

open MultiTapeNTM.ConfigurationGraph MultiTapeTM ComputableInSpace Cslib.Turing

variable {α : Type} {enc : α ↪ List Bool}

/-- The scaled fair-coin entry, extended by zero outside the configuration box. The workspace
covers the four short arguments and the precision in bits, plus a logarithmic position on the
read-only input. -/
theorem saksZhouBaseCounts_inSpace {k : ℕ} {State : Type} [Fintype State]
    (M : MultiTapePTM k Bool State) {S B d row col : α × List Bool → ℕ}
    (hB : ComputableInSpace B (encPair enc encBits) encNat S)
    (hd : ComputableInSpace d (encPair enc encBits) encNat S)
    (hr : ComputableInSpace row (encPair enc encBits) encNat S)
    (hc : ComputableInSpace col (encPair enc encBits) encNat S)
    (hprec : d ≼ S)
    (hlog : (fun p => Nat.log2 (encPair enc encBits p).length) ≼ S) :
    ComputableInSpace (fun p =>
      if hi : row p < vertexBound (k := k) (B p) then
        if hj : col p < vertexBound (k := k) (B p) then
          saksZhouBaseCounts M (d p) (B p) p.2 ⟨_, hi⟩ ⟨_, hj⟩
        else 0
      else 0) (encPair enc encBits) encNat S := by
  let e := encPair enc encBits
  have hn : ComputableInSpace (fun p : α × List Bool => p.2.length) e encNat S :=
    ((computableInLogSpace_bitsLength.comp'
      (ComputableInLogSpace.snd enc encBits)).inSpace_of_length_log ⟨1, fun p => by
        simpa only [one_mul, encBits_apply] using
          length_encNat_le_log2 (length_le_encPair_right enc encBits p)⟩).weaken hlog
  have hi := queryIndex_budget (k := k) hB hr
  have hread : ComputableInSpace (fun p : ℕ × (α × List Bool) => p.2.2[p.1]?)
      (encPair encNat e) (encOption encBool)
      (fun p => (encNat p.1).length + Nat.log2 (e p.2).length) :=
    (inputBit encBits).comp_logSpace_context
      (f := fun p : ℕ × (α × List Bool) => (p.1, p.2.2)) (by fun_prop)
      (.of_le fun p => Nat.add_le_add_left (by
        simp only [Nat.log2_eq_log_two]
        exact Nat.log_mono_right (length_le_encPair_right enc encBits p.2)) _) fun _ => le_rfl
  have hs := (bindWith hi hread).weaken (.add (.add (.refl _) hlog) hlog)
  have hcount := coinCountWithSymbol_budget M hB hn hr hc hs
  have hpow := budget_twoPow (budget_natPred hd)
    ((BigOLe.of_le fun p => Nat.pred_le (d p)).trans hprec)
  refine (budget_natMul hcount hpow).of_enc_eq fun p => ?_
  split_ifs with hi hj
  · rfl
  · simp [coinCountWithSymbol_eq_zero_of_target_ge M (Nat.le_of_not_gt hj)]
  · simp [coinCountWithSymbol_eq_zero_of_source_ge M (Nat.le_of_not_gt hi)]

/-- A base entry at the actual Saks–Zhou radix and precision. When the two IDs are read
from a stored query, the query and a logarithmic input-position counter cover all workspace. -/
theorem saksZhouBaseCounts_inSpace_context {k : ℕ} {State : Type} [Fintype State]
    (M : MultiTapePTM k Bool State) (c clk : ℕ) {row col : α → ℕ}
    (hr : ComputableInSpace row enc encNat fun a => (enc a).length)
    (hc : ComputableInSpace col enc encNat fun a => (enc a).length) :
    ComputableInSpace (fun p : α × List Bool =>
      let B := radix (radixExponent State c) p.2.length
      if hi : row p.1 < vertexBound (k := k) B then
        if hj : col p.1 < vertexBound (k := k) B then
          saksZhouBaseCounts M (saksZhouPrecision clk p.2.length) B p.2 ⟨_, hi⟩ ⟨_, hj⟩
        else 0
      else 0) (encPair enc encBits) encNat fun p => (enc p.1).length + Nat.log2 p.2.length := by
  have hsize := saksZhouSweepSize_inSpace_context enc k State c clk
  have hreg := (ComputableInLogSpace.fst enc encBits).inSpace_context
    (BigOLe.of_le fun p => Nat.le_add_right _ _)
  refine saksZhouBaseCounts_inSpace M (encSaksZhouSweepSize_radix_budget hsize)
    (encSaksZhouSweepSize_precision_budget hsize) (budget_comp_linear hr hreg)
    (budget_comp_linear hc hreg) ?_ ?_
  · refine ⟨10 * clk + 10, fun p => (saksZhouPrecision_le clk p.2.length).trans ?_⟩
    exact Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.le_add_left _ _))
  · refine ⟨2, fun p => (log2_length_encPair_le enc encBits p).trans ?_⟩
    simp only [encBits_apply]
    omega

end Turing.MultiTapePTM.ConfigurationGraph
