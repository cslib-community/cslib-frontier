/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TFNP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.NondeterministicOutput
import CslibFrontier.Computability.Complexity.Classes.NPMV.Graph
import CslibFrontier.Computability.Complexity.Classes.NPMV.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting.Verifier
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# The machine characterization of NPMV

A partial multivalued relation belongs to `NPMV` exactly when it is the relation of tagged outputs
on halted paths of one polynomial-time nondeterministic machine
[Glaßer, Reitwießner and Selivanov, Definition 2.6][GlasserReitwiessnerSelivanov2008].
The graph verifier checks a path
and its output. Conversely, the machine guesses an output and a certificate for membership of
the pair in the graph. The clock depends on the original input length in both directions.

## Main results

* `Cslib.Complexity.mem_NPMV_iff_computesRelationInPolyTime`
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeNTM Turing.MultiTapeTM

/-- Polynomially balanced NP graphs are exactly the output relations of finite polynomial-time
nondeterministic machines. -/
theorem mem_NPMV_iff_computesRelationInPolyTime {α : Type} {enc : α ↪ List Bool}
    {R : α → List Bool → Prop} :
    R ∈ NPMV enc ↔ ComputesRelationInPolyTime R enc := by
  constructor
  · intro h
    obtain ⟨q, f, hf, hspec⟩ := exists_outputVerifier_of_mem_NPMV h
    obtain ⟨k, State, hfinite, M, clock, hM⟩ := exists_guess_output_machine enc q f hf
    refine ⟨k, State, hfinite, M, clock, fun a => ⟨(hM a).1, fun y => ?_⟩⟩
    change R a y ↔ ∃ path : M.ComputationPath (enc a),
      path.last.Halted ∧ path.last.output = true :: y
    rw [(hM a).2]
    exact (hspec a y).trans ⟨fun ⟨w, hw, hout⟩ => ⟨w, hw, hout.symm⟩,
      fun ⟨w, hw, hout⟩ => ⟨w, hw, hout.symm⟩⟩
  · rintro ⟨k, State, hfinite, M, clock, hM⟩
    let : Finite State := hfinite
    have hR : R = fun a w => M.Produces (enc a) w :=
      funext fun a => funext fun w => propext ((hM a).2 w)
    rw [hR]
    exact mem_NPMV_of_runsInPolyTime (ntm := M)
      ((ComputableInPolyTime.unary_eval clock).comp
        (ComputableInPolyTime.encoding_length enc)).polyBounded (fun a => (hM a).1)

end Cslib.Complexity
