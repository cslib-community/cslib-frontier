/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.SeededPredecessor
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Seeded predecessor comparison from two optional endpoint pairs

The two endpoint queries share one seed and their original edge indices. Either lookup can
reject a padded edge. Once both return a row and a column, the existing seeded predecessor
test checks strict precedence and equality of both labels. All arithmetic runs on this short
input. Its label length is unary and the four endpoint keys are binary.
-/

public section

namespace Cslib.SeededPredecessor

open Turing.MultiTapeTM

/-- The seed and edge indices shared by both endpoint lookups. -/
structure Context where
  /-- Size of the tagged vertex universe. -/
  universeSize : ℕ
  /-- Length of a label in alphabet-64 symbols. -/
  labelLength : ℕ
  /-- Constant coefficient. -/
  c0 : ℕ
  /-- Linear coefficient. -/
  c1 : ℕ
  /-- Quadratic coefficient. -/
  c2 : ℕ
  /-- Cubic coefficient. -/
  c3 : ℕ
  /-- Edge whose rank is requested. -/
  edge : ℕ
  /-- Candidate earlier edge. -/
  candidate : ℕ

/-- Binary seed and indices with the label length supplied in unary. -/
enc_structure encContext : Context where
  universeSize : encNat, labelLength : encUnary, c0 : encNat, c1 : encNat,
  c2 : encNat, c3 : encNat, edge : encNat, candidate : encNat

/-- Retain the common metadata from a fully populated predecessor input. -/
@[expose] def Input.context (a : Input) : Context :=
  ⟨a.universeSize, a.labelLength, a.c0, a.c1, a.c2, a.c3, a.edge, a.candidate⟩

/-- Install both actual endpoints in the original flat comparison record. -/
@[expose] def Context.withEndpoints (a : Context) (e f : ℕ × ℕ) : Input :=
  ⟨a.universeSize, a.labelLength, a.c0, a.c1, a.c2, a.c3, a.edge, a.candidate,
    e.1, e.2, f.1, f.2⟩

@[simp] theorem withEndpoints_context (a : Input) :
    a.context.withEndpoints (a.edgeRow, a.edgeCol) (a.candidateRow, a.candidateCol) = a := rfl

end Cslib.SeededPredecessor

namespace Cslib.SeededPredecessorFinish

open Turing.MultiTapeTM

/-- A shared seed context and the two checked lookup answers. -/
structure Input where
  /-- Seed, universe, and edge indices. -/
  context : SeededPredecessor.Context
  /-- Endpoint lookup for the edge being ranked. -/
  edge : Option (ℕ × ℕ)
  /-- Endpoint lookup for the candidate predecessor. -/
  candidate : Option (ℕ × ℕ)

/-- Empty on rejection, or a tag followed by a framed binary row and a binary column. -/
abbrev encEnds := encOption (encPair encNat encNat)

/-- Frame the common context and first answer, followed by the second answer. -/
enc_structure encInput : Input where
  context : SeededPredecessor.encContext, edge : encEnds, candidate : encEnds

/-- Invalid lookups reject before the seeded comparison. Both valid pairs share the seed. -/
@[expose] def run (a : Input) : Bool :=
  if a.edge.isSome then
    if a.candidate.isSome then
      SeededPredecessor.test (a.context.withEndpoints (a.edge.getD (0, 0))
        (a.candidate.getD (0, 0)))
    else false
  else false

@[simp] theorem run_some (c : SeededPredecessor.Context) (e f : ℕ × ℕ) :
    run ⟨c, some e, some f⟩ = SeededPredecessor.test (c.withEndpoints e f) := rfl

@[simp] theorem run_missing_edge (c : SeededPredecessor.Context) (f : Option (ℕ × ℕ)) :
    run ⟨c, none, f⟩ = false := rfl

@[simp] theorem run_missing_candidate (c : SeededPredecessor.Context) (e : Option (ℕ × ℕ)) :
    run ⟨c, e, none⟩ = false := by cases e <;> rfl

/-- The computed comparison charges only the shared metadata and both returned pairs. -/
theorem computableInPolyTime_run : ComputableInPolyTime run encInput encBool := by
  have hc := encInput_context_deg.computableInPolyTime
  have he := encInput_edge_deg.computableInPolyTime
  have hf := encInput_candidate_deg.computableInPolyTime
  have h₁ := ComputableInPolyTime.optionGetDWithInput he (.const (0, 0))
  have h₂ := ComputableInPolyTime.optionGetDWithInput hf (.const (0, 0))
  have hp : ComputableInPolyTime (fun a : Input => a.context.withEndpoints
        (a.edge.getD (0, 0)) (a.candidate.getD (0, 0))) encInput SeededPredecessor.encInput := by
    exact SeededPredecessor.encInput_mk_polyTime
      (SeededPredecessor.encContext_universeSize_polyTime hc)
      (SeededPredecessor.encContext_labelLength_polyTime hc)
      (SeededPredecessor.encContext_c0_polyTime hc) (SeededPredecessor.encContext_c1_polyTime hc)
      (SeededPredecessor.encContext_c2_polyTime hc) (SeededPredecessor.encContext_c3_polyTime hc)
      (SeededPredecessor.encContext_edge_polyTime hc)
      (SeededPredecessor.encContext_candidate_polyTime hc) h₁.fst' h₁.snd' h₂.fst' h₂.snd'
  unfold run
  exact ComputableInPolyTime.ite he.optionIsSome
    (ComputableInPolyTime.ite hf.optionIsSome
      (SeededPredecessor.computableInPolyTime_test.comp hp) (.const false)) (.const false)

/-- Evaluation with the four actual keys recovers the original predicate on its flat record. -/
theorem run_input (a : SeededPredecessor.Input) :
    run ⟨a.context, some (a.edgeRow, a.edgeCol), some (a.candidateRow, a.candidateCol)⟩ =
      SeededPredecessor.test a := rfl

end Cslib.SeededPredecessorFinish
