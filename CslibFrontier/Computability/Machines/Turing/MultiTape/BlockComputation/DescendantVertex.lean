/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantEndpoint
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SeededVertexRank
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.QuantifiedWord.Append

/-!
# Compressed numbered-vertex provenance

An origin consists of a birth stage and the vertex's number at birth. Stage zero names an
original vertex; a positive stage names a packet introduced by that split, counting from the
root. A retained vertex keeps the same origin while its current number changes to its group
prefix rank.

The quantified word contains one fixed block per ancestry frame. A block guesses a parent
vertex, then universally checks either its seeded prefix rank or its remaining ancestry. At
the claimed birth stage it checks the total retained count instead. The complete word is fixed
by the stored frames, including branches that finish early. No descendant vertex list is
constructed by the program.

## Main definitions

* `Turing.MultiTapeTM.DescendantVertex.Origin`: the birth stage and original or packet index.
* `Turing.MultiTapeTM.DescendantVertex.Query`: the compressed frame stack and proposed origin.
* `Turing.MultiTapeTM.DescendantVertex.program`: the terminal interpreter of a completed word.
* `Turing.MultiTapeTM.DescendantVertex.HasOrigin`: exact numerical ancestry semantics.
-/

public section

namespace Turing.MultiTapeTM.DescendantVertex

open Cslib Cslib.BitString MultiTapeATM QuantifiedWord
open DescendantEndpoint (Frame encFrame)

/-- A vertex's birth stage and its number within the original vertices or the birth packets. -/
structure Origin where
  /-- Zero for an original vertex; otherwise the split number counted from the root. -/
  stage : ℕ
  /-- Original vertex number at stage zero, or packet number at a positive birth stage. -/
  index : ℕ
  deriving DecidableEq

/-- Binary birth stage followed by binary original-vertex or packet number. -/
enc_structure encOrigin : Origin where stage : encNat, index : encNat

/-- A compressed ancestry and one proposed origin, with the current vertex count. -/
structure Query where
  /-- Seeded ancestry frames, newest first. -/
  frames : List Frame
  /-- Exact current vertex count in the semantic application, encoded in binary. -/
  vertices : ℕ
  /-- Current vertex number, encoded in binary. -/
  vertex : ℕ
  /-- Proposed birth information, unchanged while retained vertices are traced upward. -/
  origin : Origin
  deriving DecidableEq

/-- Framed ancestry, binary current count and vertex, then the binary origin record. -/
enc_structure encQuery : Query where frames : (encList encFrame), vertices : encNat,
  vertex : encNat, origin : encOrigin

/-- The exact-count query for a frame's own shared seed. -/
@[expose] def rankQuery (f : Frame) (bound value : ℕ) : SeededVertexRank.Query :=
  ⟨⟨f.vertices, f.coordinates, f.c0, f.c1, f.c2, f.c3, 0, 0⟩,
    f.coordinate, f.group, bound, value⟩

/-- The group assigned to a binary parent key by the frame's native seed arithmetic. -/
@[expose] def symbol (f : Frame) (v : ℕ) : ℕ :=
  RootPortFinish.symbol (rankQuery f 0 0).context f.coordinate v

/-- The mathematical retained prefix counted by the native rank word. -/
@[expose] def retained (f : Frame) (bound : ℕ) : ℕ :=
  (List.range (min bound f.vertices)).countP fun v => decide (symbol f v = f.group)

/-- One bounded parent proposal, a universal continuation selector, and a seeded count word. -/
@[expose] def frameFlags (f : Frame) : List Bool :=
  List.replicate f.vertices.size false ++ true :: SeededVertexRank.flags f.vertices

/-- All frame words are prepared before any proposal is chosen. -/
@[expose] def flags (frames : List Frame) : List Bool := frames.flatMap frameFlags

/-- One local block either gives a Boolean verdict or proposes one parent vertex number. -/
@[expose] def dispatch (q : Query) (xs : List Bool) : Bool ⊕ ℕ :=
  if q.vertex < q.vertices ∧ q.origin.stage ≤ q.frames.length then
    match q.frames with
    | [] => .inl (decide (q.origin.index = q.vertex))
    | f :: fs =>
      let parent := ofBits (xs.take f.vertices.size)
      let rest := xs.drop f.vertices.size
      if q.origin.stage = fs.length + 1 then
        .inl (decide (q.origin.index ≤ q.vertex) &&
          SeededVertexRank.program (rankQuery f f.vertices (q.vertex - q.origin.index), rest.tail))
      else if rest.headD false then .inr parent
      else .inl (decide (parent < f.vertices ∧ symbol f parent = f.group) &&
        SeededVertexRank.program (rankQuery f parent q.vertex, rest.tail))
  else .inl false

/-- Follow a completed word through its frame blocks. Unused suffixes have no effect after a
Boolean verdict; each parent continuation consumes exactly one frame. -/
@[expose] def run (vertices vertex : ℕ) (origin : Origin) :
    List Frame → List Bool → Bool
  | [], xs => (dispatch ⟨[], vertices, vertex, origin⟩ xs).elim id (fun _ => false)
  | f :: fs, xs =>
    let cut := (frameFlags f).length
    (dispatch ⟨f :: fs, vertices, vertex, origin⟩ (xs.take cut)).elim id
      (fun parent => run f.vertices parent origin fs (xs.drop cut))

/-- The native terminal's input is the compressed query and its completed quantified word. -/
@[expose] def program (p : Query × List Bool) : Bool :=
  run p.1.vertices p.1.vertex p.1.origin p.1.frames p.2

/-- Numerical ancestry semantics, including invalid-index rejection. Packet births use the
total retained count, while retention requires both membership and the exact prefix rank. -/
@[expose] def HasOrigin (vertices vertex : ℕ) (origin : Origin) : List Frame → Prop
  | [] => vertex < vertices ∧ origin.stage = 0 ∧ origin.index = vertex
  | f :: fs => vertex < vertices ∧
      ((origin.stage = fs.length + 1 ∧ vertex = retained f f.vertices + origin.index) ∨
        (origin.stage ≤ fs.length ∧ ∃ parent, parent < f.vertices ∧
          symbol f parent = f.group ∧ vertex = retained f parent ∧
          HasOrigin f.vertices parent origin fs))

end Turing.MultiTapeTM.DescendantVertex
