/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantEndpoint
import Mathlib.Data.List.GetD

/-!
# Correctness of the compressed descendant endpoint game

The stored frames contain only graph sizes and actual seed coefficients. `Represents` relates
such a newest-first stack to the genuine numbered child edge lists, tracking the exact vertex
count through retained vertices and all packet vertices. Under that representation,
`accepts_iff_of_represents` proves that the short runtime game accepts precisely the requested
edge's endpoints, including rejection of every out-of-range edge.

`value_iff_next` and `terminal_value` give the Boolean game interface used by the native
controller. No semantic decoder or circuit-navigation assumption is supplied by that controller.
-/

public section

namespace Turing.MultiTapeTM.DescendantEndpoint

open Cslib BalancedSchedules Circuits.Frontier.NativeChild EndpointQuery
open MultiTapeATM SeededChildCounts QuantifiedWord

/-- Finite local games compose by sending their sole recursive request to the preceding frames. -/
@[expose] noncomputable def accepts (base : EndpointQuery) : List Frame → ℕ → ℕ × ℕ → Prop
  | [], edge, answer => base.accepts edge answer
  | f :: fs, edge, answer =>
    plays (fun xs => Joined.holds ⟨f.edges, accepts base fs⟩
      (Joined.program (f.header edge answer, xs))) [] f.flags

/-- Interpretation of a partially completed local word with its original choice order. -/
@[expose] noncomputable def value (base : EndpointQuery) (p : Position) : Prop :=
  match p.verdict with
  | some verdict => verdict = true
  | none => match p.frames with
    | [] => base.accepts p.edge (p.row, p.column)
    | f :: fs => plays (fun xs => Joined.holds ⟨f.edges, accepts base fs⟩
        (Joined.program (f.header p.edge (p.row, p.column), xs))) p.choices p.pending

/-- Starting a frame stack has exactly the recursively composed endpoint meaning. -/
@[simp] theorem value_root (base : EndpointQuery) (copies : ℕ) (frames : List Frame)
    (edge : ℕ) (answer : ℕ × ℕ) :
    value base (root copies frames edge answer) ↔ accepts base frames edge answer := by
  cases frames <;> rfl

/-- At a blank game header only a Boolean verdict or the original root query remains. -/
theorem terminal_value (base : EndpointQuery) (p : Position) (hp : player p = none) :
    Joined.holds base (terminal p) ↔ value base p := by
  cases hv : p.verdict with
  | some verdict => simp [terminal, value, hv, Joined.holds]
  | none =>
    cases hf : p.frames with
    | nil => simp [terminal, value, hv, hf, Joined.holds]
    | cons f fs => simp [player, hv, hf] at hp

/-- A single quantified choice, or the deterministic local dispatch, preserves the game value. -/
theorem value_iff_next (base : EndpointQuery) (p : Position) (owner : Bool)
    (hp : player p = some owner) :
    value base p ↔ if owner then ∀ bit, value base (next p bit)
      else ∃ bit, value base (next p bit) := by
  cases hv : p.verdict with
  | some verdict => simp [player, hv] at hp
  | none =>
    cases hf : p.frames with
    | nil => simp [player, hv, hf] at hp
    | cons f fs =>
      cases hg : p.pending with
      | cons flag flags =>
        have ho : owner = flag := by simpa [player, hv, hf, hg] using hp.symm
        subst owner
        cases flag <;> simp [value, next, hv, hf, hg, plays]
      | nil =>
        have ho : owner = false := by simpa [player, hv, hf, hg] using hp.symm
        subst owner
        cases hrun : Joined.program (f.header p.edge (p.row, p.column), p.choices) with
        | inl verdict => simp [value, next, hv, hf, hg, plays, hrun, Joined.holds, root]
        | inr query =>
          simp only [value, hv, hf, hg, plays, hrun, Joined.holds,
            Bool.false_eq_true, ↓reduceIte, next, Option.isSome_none]
          simp only [exists_const]
          change accepts base fs query.1 query.2 ↔
            value base (root p.copies fs query.1 query.2)
          exact (value_root base p.copies fs query.1 query.2).symm

/-- A frame stack records actual split seeds and exact parent vertex and edge counts. Each
child has the selected parent vertices followed by every vertex of its native packing,
including isolated packet vertices. No edge table is part of the encoded input. -/
inductive Represents (rootVertices : ℕ) (rootEdges : List (ℕ × ℕ)) :
    List Frame → ℕ → List (ℕ × ℕ) → Prop
  | nil : Represents rootVertices rootEdges [] rootVertices rootEdges
  | cons {frames : List Frame} {edges : List (ℕ × ℕ)} {U a : ℕ}
      (parent : Represents rootVertices rootEdges frames U edges)
      (seed : SeededLabels.Seed U (6 * a)) (coordinate : Fin a) (group : ℕ)
      (keys : ∀ p ∈ edges, p.1 < U ∧ p.2 < U) :
      Represents rootVertices rootEdges (Frame.ofSeed edges.length seed coordinate group :: frames)
        ((Labels.ofSeed U a seed coordinate group).groups.count group +
          ((Labels.ofSeed U a seed coordinate group).packing edges).numPackets)
        ((Labels.ofSeed U a seed coordinate group).edges edges)

/-- The composed compressed game has exactly the genuine numbered descendant endpoints.
The equivalence also excludes invalid edge indices even if their default pair is genuine. -/
theorem accepts_iff_of_represents {rootVertices vertices : ℕ}
    {rootEdges edges : List (ℕ × ℕ)} {frames : List Frame}
    (base : EndpointQuery) (hbase : base.Represents rootEdges)
    (hframes : Represents rootVertices rootEdges frames vertices edges)
    (edge : ℕ) (answer : ℕ × ℕ) :
    accepts base frames edge answer ↔ edge < edges.length ∧ edges.getD edge (0, 0) = answer := by
  induction hframes generalizing edge answer with
  | nil => exact hbase.2 edge answer
  | @cons frames edges U a hframes seed coordinate group keys ih =>
    let q : EndpointQuery := ⟨edges.length, accepts base frames⟩
    have hq : q.Represents edges := ⟨rfl, ih⟩
    have hkeys : ∀ e p, q.accepts e p → p.1 < U ∧ p.2 < U := by
      intro e p hp
      obtain ⟨he, rfl⟩ := (hq.2 e p).mp hp
      apply keys
      rw [List.getD_eq_getElem _ _ he]
      exact List.getElem_mem _
    let l := Labels.ofSeed U a seed coordinate group
    let header := Joined.headerOf seed coordinate group q.size edge answer
    let check (p : SeededChildWitness.Proposal) := SeededChildWitness.run
      ⟨⟨U, a, seed 0, seed 1, seed 2, seed 3, p.edge, 0⟩, coordinate.val, group,
        edge, p.ends, answer, p.counts⟩ = true
    change plays (fun xs => Joined.holds q (Joined.program (header, xs))) []
      (Joined.flags ⟨q.size, U, edge⟩) ↔ _
    have hprogram := plays_congr_length
      (fun xs => Joined.holds q (Joined.program (header, xs)))
      (Joined.value q l ⟨q.size, U, edge⟩ check) [] (Joined.flags ⟨q.size, U, edge⟩)
      (fun xs _ => Joined.program_spec seed coordinate group q edge answer xs)
    exact hprogram.trans ((Joined.plays_child seed coordinate group hq hkeys edge answer).trans
      ((hq.seededChild l).2 edge answer))

end Turing.MultiTapeTM.DescendantEndpoint
