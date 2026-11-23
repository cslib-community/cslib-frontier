/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SeededChildWitness.Program
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootEndpointQuery

/-!
# Short runtime positions for descendant endpoint queries

One frame stores the parent sizes and four coefficients of the seed used for a split. Frames
are newest first. Each local quantified word ends in a Boolean verdict or one endpoint query
on the preceding frames. The marked root schedule is absent from the mutable position.

`next` consumes one choice flag, then executes the existing seeded-child program in a separate
deterministic round. `rank_next_lt` bounds the complete traversal by the sum of the frame-word
lengths, independently of the root schedule's length.
-/

public section

namespace Turing.MultiTapeTM.DescendantEndpoint

open Cslib BalancedSchedules MultiTapeATM SeededChildCounts

/-- Runtime data of one packing split. No parent edge or vertex table is stored. -/
structure Frame where
  /-- Number of parent edges, in binary. -/
  edges : ℕ
  /-- Size of the parent vertex universe, in binary. -/
  vertices : ℕ
  /-- Number of radix-64 coordinates, in unary. -/
  coordinates : ℕ
  /-- Selected coordinate, in unary. -/
  coordinate : ℕ
  /-- Selected radix-64 group, in binary. -/
  group : ℕ
  /-- Constant seed coefficient, in binary. -/
  c0 : ℕ
  /-- Linear seed coefficient, in binary. -/
  c1 : ℕ
  /-- Quadratic seed coefficient, in binary. -/
  c2 : ℕ
  /-- Cubic seed coefficient, in binary. -/
  c3 : ℕ
  deriving DecidableEq

/-- Framed fields in declaration order, with unary coordinate counts and binary other fields. -/
enc_structure encFrame : Frame where
  edges : encNat, vertices : encNat, coordinates : encUnary, coordinate : encUnary,
  group : encNat, c0 : encNat, c1 : encNat, c2 : encNat, c3 : encNat

/-- Populate a local query header using the frame's single shared seed. -/
@[expose] def Frame.header (f : Frame) (edge : ℕ) (answer : ℕ × ℕ) : Joined.Header :=
  ⟨⟨f.edges, f.vertices, edge⟩,
    ⟨f.vertices, f.coordinates, f.c0, f.c1, f.c2, f.c3, 0, 0⟩,
    f.coordinate, f.group, answer⟩

/-- Every endpoint query at a fixed frame has the same quantified-word shape. -/
@[expose] def Frame.flags (f : Frame) : List Bool := Joined.flags ⟨f.edges, f.vertices, 0⟩

/-- Store an actual finite seed and split coordinate, with the exact parent edge count. -/
@[expose] def Frame.ofSeed {U a : ℕ} (edges : ℕ)
    (seed : SeededLabels.Seed U (6 * a)) (i : Fin a) (group : ℕ) : Frame :=
  ⟨edges, U, a, i.val, group, seed 0, seed 1, seed 2, seed 3⟩

/-- Mutable endpoint state; the root schedule is stored on a separate protected tape. -/
structure Position where
  /-- Number of Boolean copies per root edge. -/
  copies : ℕ
  /-- Unprocessed split frames, newest first. -/
  frames : List Frame
  /-- Requested edge in the current descendant. -/
  edge : ℕ
  /-- Proposed row endpoint. -/
  row : ℕ
  /-- Proposed column endpoint. -/
  column : ℕ
  /-- Remaining existential and universal choices of the current frame. -/
  pending : List Bool
  /-- Choices already made, in their original order. -/
  choices : List Bool
  /-- A completed local verdict; `none` continues to the frames or the root schedule. -/
  verdict : Option Bool
  deriving DecidableEq

/-- Binary copy and query indices, a framed list of split frames, raw choice words, and a
tagged Boolean verdict, in declaration order. The root schedule is not encoded here. -/
enc_structure encPosition : Position where
  copies : encNat, frames : (encList encFrame), edge : encNat, row : encNat, column : encNat,
  pending : encBits, choices : encBits, verdict : (encOption encBool)

/-- Initialize one query using the top frame's flags, or prepare a root lookup at an empty stack. -/
@[expose] def root (copies : ℕ) (frames : List Frame) (edge : ℕ) (answer : ℕ × ℕ) : Position :=
  ⟨copies, frames, edge, answer.1, answer.2, frames.head?.elim [] Frame.flags, [], none⟩

/-- A completed verdict or an empty ancestry is terminal. Exhausted choices use one
deterministic round to execute the local program. -/
@[expose] def player (p : Position) : Option Bool :=
  if p.verdict.isSome then none else
    match p.frames with
    | [] => none
    | _ :: _ => some (p.pending.headD false)

/-- Consume a choice, or dispatch the completed local word to its verdict or parent query. -/
@[expose] def next (p : Position) (bit : Bool) : Position :=
  if p.verdict.isSome then p else
    match p.frames with
    | [] => p
    | f :: fs => match p.pending with
      | _ :: flags => { p with pending := flags, choices := p.choices ++ [bit] }
      | [] => match Joined.program (f.header p.edge (p.row, p.column), p.choices) with
        | .inl verdict => { root p.copies [] 0 (0, 0) with verdict := some verdict }
        | .inr (edge, answer) => root p.copies fs edge answer

/-- At a terminal, return the closed verdict or the single root endpoint request. -/
@[expose] def terminal (p : Position) : Joined.Instruction :=
  p.verdict.elim (.inr (p.edge, (p.row, p.column))) .inl

/-- One native round returns the successor's player and encoded short position. -/
@[expose] def step (x : Bool × Position) : Option Bool × Position :=
  let p := next x.2 x.1
  (player p, p)

/-- Unconsumed quantified choices and one deterministic dispatch per remaining frame. -/
@[expose] def rank (p : Position) : ℕ :=
  if p.verdict.isSome then 0 else
    match p.frames with
    | [] => 0
    | _ :: fs => p.pending.length + 1 + (fs.map (fun f => f.flags.length + 1)).sum

/-- Initial rank is the total number of frame choices and local dispatches. -/
theorem rank_root (copies : ℕ) (frames : List Frame) (edge : ℕ) (answer : ℕ × ℕ) :
    rank (root copies frames edge answer) =
      (frames.map (fun f => f.flags.length + 1)).sum := by
  cases frames <;> simp [rank, root]

/-- Native routing leaves the root's Boolean copy count unchanged. -/
@[simp] theorem next_copies (p : Position) (bit : Bool) : (next p bit).copies = p.copies := by
  unfold next
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl

/-- Every live move strictly decreases the remaining frame-word rank. -/
theorem rank_next_lt (p : Position) (owner bit : Bool) (hp : player p = some owner) :
    rank (next p bit) < rank p := by
  cases hv : p.verdict with
  | some verdict => simp [player, hv] at hp
  | none =>
    cases hf : p.frames with
    | nil => simp [player, hv, hf] at hp
    | cons f fs =>
      cases hg : p.pending with
      | cons flag flags => simp [rank, next, hv, hf, hg]
      | nil =>
        cases hrun : Joined.program (f.header p.edge (p.row, p.column), p.choices) with
        | inl verdict => simp [rank, next, hv, hf, hg, hrun, root]
        | inr query =>
          simp only [next, hv, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hf, hg, hrun]
          rw [rank_root]
          simp [rank, hv, hf, hg]

end Turing.MultiTapeTM.DescendantEndpoint
