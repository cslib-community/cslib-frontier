/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.SaksZhou.Parameters
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.StoredLoop
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.BitsGetElem
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Binary counters for the Saks–Zhou matrix sweep

All dimensions of one sweep fit in logarithmic space. The sweep tries each possible starting
block, takes as many generator steps as there are leaves and examines every matrix column
per step. The certificate materializes these dimensions together while the word stays read-only.
-/

public section

namespace Turing.MultiTapePTM.ConfigurationGraph

open MultiTapeNTM.ConfigurationGraph MultiTapeTM ComputableInSpace Cslib.Turing

/-- Binary dimensions used by every job of the same matrix sweep. -/
structure SaksZhouSweepSize where
  /-- Base of the packed configuration registers. -/
  radix : ℕ
  /-- Number of compact configuration IDs. -/
  vertices : ℕ
  /-- Fractional bits kept after rounding. -/
  precision : ℕ
  /-- Generator depth and number of rounding rounds. -/
  levels : ℕ
  /-- Bits per generator block. -/
  blockWidth : ℕ
  /-- Denominator of the dyadic matrix entries. -/
  denominator : ℕ
  /-- Number of choices of the starting block. -/
  starts : ℕ
  /-- Generator steps from one starting block. -/
  steps : ℕ
  /-- Factor converting a matrix numerator to a number of block labels. -/
  scale : ℕ
  /-- Number of iterations in the sweep. -/
  rounds : ℕ

/-- The ten binary fields in declaration order, with each field except the last framed. -/
enc_structure encSaksZhouSweepSize : SaksZhouSweepSize where
  radix : encNat, vertices : encNat, precision : encNat, levels : encNat, blockWidth : encNat,
  denominator : encNat, starts : encNat, steps : encNat, scale : encNat, rounds : encNat

/-- Prepare all sweep dimensions from the input length and the machine's two fixed bounds. -/
@[expose] def saksZhouSweepSize (k : ℕ) (State : Type) [Fintype State] (c clk n : ℕ) :
    SaksZhouSweepSize :=
  let B := radix (radixExponent State c) n
  let N := vertexBound (k := k) B
  let d := saksZhouPrecision clk n
  let s := saksZhouLevels clk n
  let b := 2 * (5 * d)
  let starts := 2 ^ b
  let steps := 2 ^ s
  ⟨B, N, d, s, b, 2 ^ d, starts, steps, 2 ^ (b - d), starts * ((N + 2) * steps + 1)⟩

/-- All sweep parameters fit in logarithmic workspace on the read-only word, including the
binary counters for all starting blocks and all iterations of the sweep. -/
theorem saksZhouSweepSize_inSpace (k : ℕ) (State : Type) [Fintype State] (c clk : ℕ) :
    ComputableInSpace (fun w : List Bool => saksZhouSweepSize k State c clk w.length)
      encBits encSaksZhouSweepSize (fun w => Nat.log2 w.length) := by
  have hn : ComputableInSpace List.length encBits encNat (fun w => Nat.log2 w.length) := by
    simpa only [encBits_apply] using computableInLogSpace_bitsLength.inSpace_of_length_log
      ⟨1, fun w => by
        simpa only [one_mul, encBits_apply] using length_encNat_le_log2 (le_refl w.length)⟩
  have hd := saksZhouPrecision_inSpace clk
  have hs := saksZhouLevels_inSpace clk
  have hdb : (fun w : List Bool => saksZhouPrecision clk w.length) ≼ fun w => Nat.log2 w.length :=
    ⟨10 * clk + 10, fun w => saksZhouPrecision_le clk w.length⟩
  have hB := radix_budget (radixExponent State c) hn
  have hN := vertexBound_budget (k := k) hB
  have hb := budget_natMul (budget_const 2) (budget_natMul (budget_const 5) hd)
  have hbb := (hdb.const_mul 5).const_mul 2
  have hstarts := budget_twoPow hb hbb
  have hsteps := budget_twoPow hs ((BigOLe.of_le fun w => by
    dsimp only [saksZhouLevels, saksZhouPrecision]
    have := Nat.sqrt_le_self (clk * (Nat.log2 w.length + 2) + 1)
    omega).trans hdb)
  have hscale := budget_twoPow (budget_natSub hb hd)
    ((BigOLe.of_le fun w => Nat.sub_le _ _).trans hbb)
  have hrounds := budget_natMul hstarts
    (budget_natSucc (budget_natMul (budget_natAdd hN (budget_const 2)) hsteps))
  exact encSaksZhouSweepSize_mk_budget hB hN hd hs hb (saksZhouDenominator_inSpace clk)
    hstarts hsteps hscale hrounds

/-- Read the dimensions in the presence of a stored query, using its length plus logarithmic
workspace in the word length. -/
theorem saksZhouSweepSize_inSpace_context {α : Type} (enc : α ↪ List Bool)
    (k : ℕ) (State : Type) [Fintype State] (c clk : ℕ) :
    ComputableInSpace (fun p : α × List Bool => saksZhouSweepSize k State c clk p.2.length)
      (encPair enc encBits) encSaksZhouSweepSize fun p => (enc p.1).length + Nat.log2 p.2.length :=
  (saksZhouSweepSize_inSpace k State c clk).comp_logSpace_context
    (S := fun w => Nat.log2 w.length) (ComputableInLogSpace.snd enc encBits)
    (.of_le fun p => Nat.le_add_left _ _) fun w => by simp [encBits_apply]

end Turing.MultiTapePTM.ConfigurationGraph
