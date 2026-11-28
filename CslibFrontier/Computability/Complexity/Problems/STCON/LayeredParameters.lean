/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON.Layered
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.Recompute
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary

/-!
# Binary initialization of the layered configuration graph

A fixed source machine and its space constant determine the radix, width, and initial
column from the original word length. The width includes the accepting sink and is also
the number of layers. The initializer uses logarithmic native space on the original word
and emits only the encoded parameters. Its arithmetic stage can also start from an
already counted binary input length, as in a read-only query-machine caller.
-/

public section

namespace Cslib.Complexity.STCON

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeTM.ComputableInSpace
  _root_.Turing.MultiTapeNTM.ConfigurationGraph

/-- Binary parameters shared by queries to one layered configuration graph. -/
structure LayeredParameters where
  /-- Length of the original read-only input. -/
  inputLength : ℕ
  /-- Radix used to pack configuration registers. -/
  radix : ℕ
  /-- The number of columns including the sink, also the number of layers. -/
  width : ℕ
  /-- The source column in layer zero. -/
  source : ℕ

/-- Four binary naturals in field order. The first three are framed; the source is unframed. -/
enc_structure encLayeredParameters : LayeredParameters where
  inputLength : encNat, radix : encNat, width : encNat, source : encNat

variable {k : ℕ} {State : Type} [Fintype State]

/-- Initialize the layered configuration graph from the counted input length. The sink
column and final layer are both the predecessor of the width. -/
@[expose] noncomputable def layeredParameters (ntm : MultiTapeNTM k Bool State) (c n : ℕ) :
    LayeredParameters :=
  let B := radix (radixExponent State c) n
  ⟨n, B, vertexBound (k := k) B + 1, startID ntm B⟩

/-- Once the input length has been counted, computing the parameters costs space linear
in its binary encoding, with a constant depending only on the fixed machine and exponent. -/
theorem layeredParameters_inSpace (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ComputableInSpace (layeredParameters ntm c) encNat encLayeredParameters
      (fun n => (encNat n).length) := by
  have hin : (fun n => (encNat n).length) ≼ (fun n => (encNat n).length) := .refl _
  have hn := budget_id hin
  have hB := radix_budget (radixExponent State c) hn
  exact encLayeredParameters_mk_budget hn hB
    (budget_natSucc (vertexBound_budget (k := k) hB)) (startID_budget ntm hB)

/-- The parameters can be computed by a native logspace machine from the raw word. -/
theorem layeredParameters_inLogSpace (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ComputableInLogSpace (fun w : List Bool => layeredParameters ntm c w.length)
      encBits encLayeredParameters :=
  comp_logSpace_of_length_log computableInLogSpace_bitsLength length_bitsLength_log
    (layeredParameters_inSpace ntm c)

/-- The retained binary parameters fit in logarithmic space in the length of the raw word. -/
theorem length_layeredParameters_le_log (ntm : MultiTapeNTM k Bool State) (c : ℕ) :
    ∃ C, ∀ w : List Bool,
      (encLayeredParameters (layeredParameters ntm c w.length)).length ≤
        C * (Nat.log2 w.length + 1) :=
  length_log_of_inSpace length_bitsLength_log (layeredParameters_inSpace ntm c)

end Cslib.Complexity.STCON
