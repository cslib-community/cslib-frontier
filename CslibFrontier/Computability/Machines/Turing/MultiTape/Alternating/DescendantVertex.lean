/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantVertexGame
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantVertexCorrect
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantVertexTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Native

/-!
# A fixed native verifier of compressed vertex origins

The single stored input contains the ancestry frames, exact current vertex count, current
vertex number, and proposed birth stage and index. One finite machine prepares the complete
quantifier word, checks each selected retained rank, and follows earlier frames. Neither the
network's vertex list nor a parent-rank oracle is an input.

`exists_evaluator` applies to every encoded query. `NativeAncestry` gives its interpretation for
a represented sequence of actual native children: every valid vertex has exactly one accepted
origin, whose descriptor is the original descriptor or the exact packet descriptor at birth.
The theorem does not claim to recognize the exact-count or label-agreement premises, retrieve
the packet's incident assignment, or evaluate the packet entry.

## Main results

* `Turing.MultiTapeATM.DescendantVertex.exists_evaluator`: one finite alternating machine
  verifies numerical provenance from the compressed query within polynomial time.
-/

public section

namespace Turing.MultiTapeATM.DescendantVertex

open MultiTapeTM MultiTapeTM.DescendantVertex

/-- One finite alternating machine verifies numerical vertex provenance from a single encoded
query. The machine and polynomial constants precede every frame stack, current count, vertex,
and proposed origin. The clock includes preparation and the deterministic terminal program. -/
theorem exists_evaluator :
    ∃ (K : ℕ) (source : Fin K) (S : Type) (_ : Finite S)
      (atm : MultiTapeATM K Bool S) (C D : ℕ),
      ∀ (input : List Bool) (q : Query),
        let start := WordGameLeaf.config source (some atm.toPTM.initial) (encQuery q) 0
          (TwoWordLoad.blank K input)
        let time := C * ((encQuery q).length + 1) ^ D
        atm.HaltsWithin time start ∧
          (atm.AcceptsWithin time start ↔ HasOrigin q.vertices q.vertex q.origin q.frames) := by
  have hflags : ComputableInPolyTime (fun q : Query => flags q.frames) encQuery encBits :=
    flags_polyTime.comp encQuery_frames_deg.computableInPolyTime
  obtain ⟨K, source, S, hS, atm, C, D, h⟩ :=
    QuantifiedWord.exists_evaluator encQuery (fun q => flags q.frames) program
      hflags program_polyTime
  refine ⟨K, source, S, hS, atm, C, D, ?_⟩
  intro input q
  exact ⟨(h input q).1, (h input q).2.trans (plays_program q)⟩

end Turing.MultiTapeATM.DescendantVertex
