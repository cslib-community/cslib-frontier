/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SeededChildWitness.Dispatch
public import CslibFrontier.Computability.PolyTime.SeededChildWitness.CountingRequest
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.TwoWordLoad
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime

/-!
# Loading a recursive count request from one short work word

The finite initializer puts the retained context and selected count code on one tape and the
actual carry-lookahead counting parameters on another. The original external input is unchanged
and its length does not occur in the preparation clock. Additional persistent tapes can be
kept outside this work-tape layout by the surrounding machine.
-/

public section

namespace Turing.MultiTapeATM.SeededChildCounts

open MultiTapeTM Cslib SeededChildWitness Dispatch
open Cslib.Circuits.Boolean.CarryLookahead.Query

/-- Packed local work record on a genuine count branch. The context contains only the path and
seed metadata held by the local arithmetic controller. -/
abbrev Work := List Bool × (Public × BitQuery)

/-- The seed/path word, public graph fields, and single selected count query. -/
abbrev encWork := encPair encBits (encPair encPublic encBitQuery)

/-- The counting continuation retains the branch's selected request in its context. -/
@[expose] def contextWord (x : Work) : List Bool :=
  let (context, _, count, _, _) := x
  encPair encBits encCount (context, count)

/-- A routed request uses the precise summation limit in the geometric recurrence. -/
theorem count_eq_size {q : Circuits.Frontier.NativeChild.EndpointQuery}
    {l : Circuits.Frontier.NativeChild.EndpointQuery.Labels}
    (b : Public) (r : BitQuery) (h₁ : b.edges = q.size) (h₂ : b.vertices = l.vertices) :
    (params b r).count = (request r.1).size q l := by
  rcases r with ⟨c, j, claim⟩
  rcases c with v | ⟨col, bound⟩ | ⟨e, ends⟩ <;>
    simp [params, termCount, request, Request.size, h₁, h₂]

/-- A work-tape initializer prepares both actual count tapes, charges a polynomial only in the
packed short word, and adds the continuation clock with coefficient one. -/
theorem exists_count_load {K : ℕ} {S : Type} [Finite S] (i j : Fin K) (hne : i ≠ j)
    (leaf : MultiTapeATM K Bool S) :
    ∃ (u : ℕ) (src : Fin u) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM u Bool Q) (c d : ℕ),
      ∀ (input : List Bool) (x : Work) (t : ℕ),
        let cfg := (TwoWordInput.ready i j input (contextWord x)
          (CountingInput.encInput (Function.uncurry params x.2))).withState
          (some leaf.toPTM.initial)
        let start := WordGameLeaf.config src (some atm.toPTM.initial) (encWork x) (encWork x).length
          (TwoWordLoad.blank u input)
        let time := c * ((encWork x).length + 1) ^ d + t
        leaf.HaltsWithin t cfg → atm.HaltsWithin time start ∧
          (atm.AcceptsWithin time start ↔ leaf.AcceptsWithin t cfg) := by
  have hs := ComputableInPolyTime.snd encBits (encPair encPublic encBitQuery)
  have hctx : ComputableInPolyTime contextWord encWork encBits :=
    ((ComputableInPolyTime.fst encBits (encPair encPublic encBitQuery)).prod hs.snd'.fst').of_enc_eq
      fun _ => rfl
  have hp := computableInPolyTime_params.comp hs
  obtain ⟨T₁, S₁, hT₁, hS₁, hf⟩ := hctx.exists_computableInO
  obtain ⟨T₂, S₂, hT₂, hS₂, hg⟩ := hp.exists_computableInO
  let T (x : Work) := T₁ x + S₁ x + T₂ x + S₂ x
  have hT : PolyBounded (fun x : Work => (encWork x).length) T :=
    ((hT₁.add hS₁).add hT₂).add hS₂
  have hf' := hf.mono (T' := T) (S' := T) 1 (by dsimp [T]; omega) (by dsimp [T]; omega)
  have hg' := hg.mono (T' := T) (S' := T) 1 (by dsimp [T]; omega) (by dsimp [T]; omega)
  obtain ⟨u, src, Q, hQ, atm, A, h⟩ := TwoWordLoad.exists_load hf' hg'
    i j hne leaf
  obtain ⟨C, D, hD⟩ := ((PolyBounded.self.add ((PolyBounded.const A).mul
    (hT.add (.const 1)))).add (.const 8)).exists_le
  refine ⟨u, src, Q, hQ, atm, C, D, ?_⟩
  intro input x t cfg start time hh
  obtain ⟨ht, ha⟩ := h input x t hh
  have hle := Nat.add_le_add_right (hD x) t
  exact ⟨ht.mono hle, ⟨fun hacc => ha.mp (hacc.of_halted_stepCoins ht),
    fun hv => (ha.mpr hv).mono hle⟩⟩

end Turing.MultiTapeATM.SeededChildCounts
