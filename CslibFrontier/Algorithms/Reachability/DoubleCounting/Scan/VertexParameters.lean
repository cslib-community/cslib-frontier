/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan.VertexReader
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.Call
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Uniform native parameter processing for the vertex-ID reader

This is a parameter-processing certificate, not a uniform decoder for a combined raw
parameter/choice input. Binary dimension and claimed width are runtime data. `prepare` measures
the dimension using the existing native `Nat.size` routine, rejects an incorrect width, and
initializes the reader's cursor, accumulator and truncation flag. No choice word is stored.

## Main results

* `prepare_inSpace`: uniform native validation and initialization in encoded-parameter space.
* `runFrom_prepare`: loading the returned state into the existing reader gives exactly its
  fixed-dimension run, using one reader transition function for all dimensions.
* `runFrom_length_le`: logarithmic encoded state at every reader clock after valid preparation.
* `result_prepare`: exact agreement with the canonical ID codec after the initialized run.

The checked ordinary-import client is `CslibFrontierTests.DoubleCountingVertexParameters`.
The parameter encoding uses standard binary `encNat` registers; the ID choice encoding remains
unchanged at `Nat.size N` bits, most significant first, including the extra zero digit when
`N` is a power of two.

Uniform native composition of parameter processing with the read-only choice-source query
loop, input dispatch, and genuine nondeterministic choice production remain open in
[#6747](https://github.com/cslib-community/cslib-frontier/issues/6747). The certificates here
establish the actual native parameter computation and semantic loading boundary, not that
composed scanner or the full first-halting scan correspondence.
-/

public section

namespace Turing.DoubleCounting.VertexParameters

open MultiTapeTM ComputableInSpace VertexReader

/-- Runtime dimension and claimed fixed-width ID length. -/
structure Parameters where
  /-- Number of valid vertex IDs. Zero is permitted and has no valid IDs. -/
  dimension : ℕ
  /-- Claimed number of bits, checked against the measured binary size of `dimension`. -/
  width : ℕ

/-- Binary dimension, framed, followed by the binary claimed width. -/
enc_structure encParameters : Parameters where dimension : encNat, width : encNat

/-- Runtime parameter storage is logarithmic in the supplied numeric values, even when the
claimed width is invalid. Together with `prepare_inSpace` this bounds native preparation space. -/
theorem length_encParameters_le (p : Parameters) :
    (encParameters p).length ≤ 3 * (Nat.log2 (p.dimension + p.width) + 1) + 1 := by
  have hn := length_encNat_le_log2 (Nat.le_add_right p.dimension p.width)
  have hw := length_encNat_le_log2 (Nat.le_add_left p.width p.dimension)
  simp only [encParameters_apply, encParametersFields, length_encPair]
  omega

/-- Compute the actual width, validate the claimed width, and initialize scalar registers.
An invalid width rejects before the reader can query the choice source. -/
@[expose] def prepare (p : Parameters) : Option State :=
  if p.width = p.dimension.size then some (machine p.dimension).init else none

/-- Successful preparation supplies both the checked width and the canonical initial state. -/
theorem prepare_eq_some_iff (p : Parameters) (s : State) :
    prepare p = some s ↔ p.width = p.dimension.size ∧ s = (machine p.dimension).init := by
  by_cases h : p.width = p.dimension.size <;> simp [prepare, machine, h, eq_comm]

/-- Width measurement, comparison and initialized-state construction all have actual native
linear-space certificates on the runtime binary parameter encoding. -/
theorem prepare_inSpace :
    ComputableInSpace prepare encParameters (encOption encState)
      (fun p => (encParameters p).length) := by
  have hid := of_inO
    (ComputableInO.of_eq (encIn := encParameters) (encMid := encParameters) fun _ => rfl)
  have hn := encParameters_dimension_budget hid
  have hw := budget_comp_linear natSize hn
  have hz := budget_const (Bs := fun a => (encParameters a).length)
    (encIn := encParameters) (encB := encNat) 0
  exact (budget_ite (budget_natEq (encParameters_width_budget hid) hw)
    (budget_optionSome (encState_mk_budget hn hw hz hz (budget_const false)))
    (budget_const none)).of_enc_eq fun p => by simp [prepare, machine]

/-- A valid preparation loads the existing reader; the machine's transition code is independent
of the dimension, so no new scan or alternative ID implementation is introduced. -/
theorem runFrom_prepare (p : Parameters) (s : State) (h : prepare p = some s)
    (w : List Bool) (t : ℕ) :
    (machine 0).runFrom w s t = (machine p.dimension).run w t := by
  obtain ⟨_, rfl⟩ := (prepare_eq_some_iff p s).mp h
  rfl

/-- Validated runtime parameters give a logarithmic state bound for every reader clock,
including invalid IDs, truncated choices and clocks after halt. All retained registers count. -/
theorem runFrom_length_le (p : Parameters) (s : State) (h : prepare p = some s)
    (w : List Bool) (t : ℕ) :
    (encState ((machine 0).runFrom w s t)).length ≤
      8 * (Nat.log2 p.dimension + 1) + 9 := by
  rw [runFrom_prepare p s h]
  have hlen := length_run_le p.dimension w t
  have hs : p.dimension.size ≤ Nat.log2 p.dimension + 1 :=
    Nat.size_le.mpr Nat.lt_log2_self
  have hl : Nat.log2 p.dimension.size ≤ p.dimension.size := Nat.log2_le_self _
  omega

/-- The prepared reader decodes the same canonical prefix as the original codec.
The optional binary rank is its `Fin.val` view, without wraparound on invalid IDs. -/
theorem result_prepare (p : Parameters) (s : State) (h : prepare p = some s)
    (w : List Bool) :
    result ((machine 0).runFrom w s p.width) =
      (Cslib.DoubleCounting.Scan.Binary.decodeVertex (N := p.dimension)
        (w.take p.dimension.size)).map Fin.val := by
  rw [runFrom_prepare p s h, (prepare_eq_some_iff p s).mp h |>.1]
  exact result_eq_decodeVertex p.dimension w

end Turing.DoubleCounting.VertexParameters
