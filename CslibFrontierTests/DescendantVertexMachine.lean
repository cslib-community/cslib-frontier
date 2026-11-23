/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.DescendantVertex

/-!
# Clients of the fixed native compressed vertex verifier

The tests choose one machine before every encoded query. They check root boundary cases,
reject birth stages beyond the frame stack, and couple physical acceptance to the unique
origin and exact birth descriptor of an arbitrary genuine native ancestry.
-/

public section

namespace Turing.MultiTapeATM.DescendantVertex.Tests

open MultiTapeTM MultiTapeTM.DescendantVertex
open Cslib Circuits.Frontier NativeChild

/-- The verifier is fixed before the root size and queried vertex. Empty ancestry accepts
the matching original vertex, rejects a different original number and the exact length,
and every frame stack rejects a birth stage beyond its depth. -/
theorem uniform_boundaries :
    ∃ (K : ℕ) (source : Fin K) (S : Type) (_ : Finite S)
      (atm : MultiTapeATM K Bool S) (C D : ℕ),
      ∀ (input : List Bool) (n : ℕ),
        let accepts := fun q : Query =>
          atm.AcceptsWithin (C * ((encQuery q).length + 1) ^ D)
            (WordGameLeaf.config source (some atm.toPTM.initial) (encQuery q) 0
              (TwoWordLoad.blank K input))
        (∀ q : Query,
          atm.HaltsWithin (C * ((encQuery q).length + 1) ^ D)
            (WordGameLeaf.config source (some atm.toPTM.initial) (encQuery q) 0
              (TwoWordLoad.blank K input))) ∧
        accepts ⟨[], n + 1, n, ⟨0, n⟩⟩ ∧
        ¬ accepts ⟨[], n + 1, n, ⟨0, n + 1⟩⟩ ∧
        ¬ accepts ⟨[], n, n, ⟨0, n⟩⟩ ∧
        ∀ q : Query, q.frames.length < q.origin.stage → ¬ accepts q := by
  obtain ⟨K, source, S, hS, atm, C, D, h⟩ := exists_evaluator
  refine ⟨K, source, S, hS, atm, C, D, ?_⟩
  intro input n accepts
  refine ⟨fun q => (h input q).1, ?_, ?_, ?_, ?_⟩
  · exact (h input ⟨[], n + 1, n, ⟨0, n⟩⟩).2.mpr ⟨Nat.lt_succ_self n, rfl, rfl⟩
  · intro hacc
    have ho := (h input ⟨[], n + 1, n, ⟨0, n + 1⟩⟩).2.mp hacc
    have hi : n + 1 = n := ho.2.2
    omega
  · intro hacc
    exact Nat.lt_irrefl n ((h input ⟨[], n, n, ⟨0, n⟩⟩).2.mp hacc).1
  · intro q hstage hacc
    exact (Nat.not_le_of_lt hstage) ((h input q).2.mp hacc).stage_le

/-- A uniform physical verifier has exactly one accepting origin for each valid vertex in
every actual native ancestry. Its descriptor agrees with the descriptor at that birth. -/
theorem uniform_native_ancestry :
    ∃ (K : ℕ) (source : Fin K) (S : Type) (_ : Finite S)
      (atm : MultiTapeATM K Bool S) (C D : ℕ),
      ∀ (input : List Bool) (T : Type) (root network : DescribedNetwork (VertexDesc T))
        (frames : List DescendantEndpoint.Frame)
        (ancestry : NativeAncestry root frames network)
        (vertex : ℕ), vertex < network.vertices.length →
        let query := fun origin : Origin =>
          (⟨frames, network.vertices.length, vertex, origin⟩ : Query)
        let start := fun origin => WordGameLeaf.config source (some atm.toPTM.initial)
          (encQuery (query origin)) 0 (TwoWordLoad.blank K input)
        let time := fun origin => C * ((encQuery (query origin)).length + 1) ^ D
        (∃! origin, atm.AcceptsWithin (time origin) (start origin)) ∧
          ∀ origin, atm.HaltsWithin (time origin) (start origin) ∧
            (atm.AcceptsWithin (time origin) (start origin) →
              (network.vertices[vertex]?).map Prod.snd = ancestry.birthDescriptor origin) := by
  obtain ⟨K, source, S, hS, atm, C, D, h⟩ := exists_evaluator
  refine ⟨K, source, S, hS, atm, C, D, ?_⟩
  intro input T root network frames ancestry vertex hvertex query start time
  refine ⟨?_, ?_⟩
  · obtain ⟨origin, horigin, hunique⟩ := ancestry.existsUnique_origin hvertex
    refine ⟨origin, (h input (query origin)).2.mpr horigin, ?_⟩
    intro candidate hc
    exact hunique candidate ((h input (query candidate)).2.mp hc)
  · intro origin
    have hm := h input (query origin)
    exact ⟨hm.1, fun hacc => ancestry.descriptor_eq_birthDescriptor (hm.2.mp hacc)⟩

end Turing.MultiTapeATM.DescendantVertex.Tests
