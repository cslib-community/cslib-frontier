/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.RootContractionSchedule
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log

/-!
# Generating the protected root metadata from a binary source clock

The outer carry-save leaf stores only the root graph parameters, with an empty schedule and
zero coefficients and indices. The actual path and bit are supplied by the outer ATM. Computing
the template is polynomial in the binary length of the source clock.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open _root_.Turing _root_.Turing.MultiTapeTM ComputableInPolyTime
open Circuits.Frontier.ContractionSchedule

/-- Candidate-independent root metadata in the carry-save leaf's protected context field. -/
@[expose] def outerRootTemplate (k states t : ℕ) : RootBalanceRequest.Public :=
  let U := rootVertices k states t
  let n := rootEdges k states t
  (⟨[], rootCopies k states t, ⟨U, slotBits n 0, 0, 0, 0, 0, 0, 0⟩⟩, n)

/-- Compute the block length from a binary source clock. -/
theorem binary_blockLength : ComputableInPolyTime blockLength encNat encNat :=
  binary_clog_two_nat.comp (binary_add' (.id' : ComputableInPolyTime id encNat encNat) (const 2))

/-- Compute the number of blocks without expanding the source clock into unary. -/
theorem binary_numBlocks : ComputableInPolyTime numBlocks encNat encNat := by
  have ht : ComputableInPolyTime id encNat encNat := .id'
  have h := binary_div' (binary_sub' (binary_add' ht binary_blockLength) (const 1))
    binary_blockLength
  change ComputableInPolyTime (fun t => t ⌈/⌉ blockLength t) encNat encNat
  simpa only [Nat.ceilDiv_eq_add_pred_div, Function.comp_apply, id_eq] using h

/-- Native short setup from the binary clock. The unary label length is logarithmically sized. -/
theorem computableInPolyTime_outerRootTemplate (k states : ℕ) :
    ComputableInPolyTime (outerRootTemplate k states) encNat RootBalanceRequest.encPublic := by
  have hb := binary_blockLength
  have hq := binary_numBlocks
  have hm : ComputableInPolyTime (rootCopies k states) encNat encNat :=
    binary_mul' (const (states + k + 4)) hb
  have hcopied := binary_mul' (binary_mul' hq (const (3 * k + 1))) hm
  have hn : ComputableInPolyTime (rootEdges k states) encNat encNat := binary_mul' (const 2) hcopied
  have hu : ComputableInPolyTime (rootVertices k states) encNat encNat :=
    binary_add' (binary_mul' hq (const (3 * k + 2))) hcopied
  have ha : ComputableInPolyTime (fun t => slotBits (rootEdges k states t) 0) encNat encUnary := by
    have h := unary_mul' (const 2) ((unary_div_const 131072).comp (binary_log_two.comp hn))
    simpa [slotBits, prefixBits, taper] using h
  have hz : ComputableInPolyTime (fun _ : ℕ => 0) encNat encNat := const 0
  exact ((RootPredecessorQuery.encInput_mk_polyTime (const []) hm
    (SeededPredecessor.encContext_mk_polyTime hu ha hz hz hz hz hz hz)).prod hn)

/-- The actual protected encoding is produced in short polynomial time. -/
theorem computableInPolyTime_outerRootContext (k states : ℕ) :
    ComputableInPolyTime (fun t => RootBalanceRequest.encPublic (outerRootTemplate k states t))
      encNat encBits :=
  (computableInPolyTime_outerRootTemplate k states).of_enc_eq (fun _ => rfl)

end Cslib.Complexity.CountingSimulation
