/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Prim
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.CompilePolyTime
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Compile
public import Mathlib.Data.FinEnum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Polynomial-time compilation for finite fragment alphabets

Each instruction places one of finitely many primitive diagrams at a unary wire offset.
Expanding the finite fragment table emits the structural primitive word in polynomial time.
The uniform word compiler then produces graph data.

## Main definitions

* `Cslib.Complexity.NCL.Word.Fixed.Language`: a finite fragment table.
* `Cslib.Complexity.NCL.Word.Fixed.Language.Program`: instructions with wire offsets.
* `Cslib.Complexity.NCL.Word.Fixed.Language.run`,
  `Cslib.Complexity.NCL.Word.Fixed.Language.compile`: execute and compile an instruction stream.

## Main results

* `Cslib.Complexity.NCL.Word.Fixed.Language.run_eq_expand`,
  `Cslib.Complexity.NCL.Word.Fixed.Language.compile_eq_expand`: primitive word agreement.
* `Cslib.Complexity.NCL.Word.Fixed.Language.computableInPolyTime_compile`: complexity bounds.
-/

public section

namespace Cslib.Complexity.NCL.Word.Fixed

open _root_.Turing.MultiTapeTM

/-- A finite instruction alphabet with one fixed primitive diagram for each tag. -/
structure Language where
  /-- The instruction tags. -/
  Opcode : Type
  /-- A fixed finite enumeration of the tags. -/
  enumeration : FinEnum Opcode
  /-- The diagram executed by each instruction tag. -/
  fragment : Opcode → Σ a b : List Color, Diagram Prim a b

attribute [instance] Language.enumeration

namespace Language
variable (F : Language)

/-- An instruction stream: unary wire offsets paired with finite fragment tags. -/
abbrev Program := List (ℕ × F.Opcode)
/-- Encode a tag by its finite enumeration rank. -/
@[expose] def encOpcode : F.Opcode ↪ List Bool := encFinEnum F.Opcode
/-- Encode instructions by unary offsets and finite tags. -/
@[expose] def encProgram : F.Program ↪ List Bool := encList (encPair encUnary F.encOpcode)
/-- Expand one fixed fragment at a wire offset. -/
@[expose] def word (op : F.Opcode) (k : ℕ) : Word :=
  let ⟨_, _, diagram⟩ := F.fragment op
  diagram.toWord Prim.interp k
/-- Expand all instructions in order. -/
@[expose] def expand (p : F.Program) : Word := p.flatMap fun i => F.word i.2 i.1
/-- Execute fixed fragments in order, retaining the wire stack and emitted vertices. -/
@[expose] def run (p : F.Program) (st : Word.State) : Word.State :=
  p.foldl (fun st i => Word.run (F.word i.2 i.1) st) st

/-- Executing instructions agrees exactly with executing their primitive expansion. -/
theorem run_eq_expand (p : F.Program) (st : Word.State) :
    F.run p st = Word.run (F.expand p) st := by
  induction p generalizing st with
  | nil => rfl
  | cons i p ih =>
    simp only [run, List.foldl_cons, expand, List.flatMap_cons, Word.run_append]
    exact ih _

/-- Expand a fixed instruction alphabet to its structural primitive word in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_expand :
    ComputableInPolyTime F.expand F.encProgram encWord := by
  have ht : ComputableInPolyTime (fun p : F.Program × (ℕ × F.Opcode) => p.2.2)
      (encPair F.encProgram (encPair encUnary F.encOpcode)) F.encOpcode := by fun_prop
  have hk : ComputableInPolyTime (fun p : F.Program × (ℕ × F.Opcode) => p.2.1)
      (encPair F.encProgram (encPair encUnary F.encOpcode)) encUnary := by fun_prop
  have hw : ComputableInPolyTime (fun p : F.Program × (ℕ × F.Opcode) => F.word p.2.2 p.2.1)
      (encPair F.encProgram (encPair encUnary F.encOpcode)) encWord := by
    apply ht.finite_cases (branch := fun op p => F.word op p.2.1)
    intro op
    exact (Diagram.computableInPolyTime_toWord Prim.interp (F.fragment op).2.2).comp hk
  unfold expand encProgram
  exact ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.of_eq (fun _ => rfl)) hw

/-- Compile instructions to the vertex list and binary edge count of a graph instance. -/
@[expose] def compile (p : F.Program) : AndOrGraph :=
  let st := F.run p ⟨[], 0, []⟩
  ⟨st.verts, st.next⟩

/-- Instruction compilation agrees with primitive word compilation. -/
theorem compile_eq_expand (p : F.Program) : F.compile p = Word.compile (F.expand p) := by
  unfold compile Word.compile
  rw [run_eq_expand]

/-- Compile instruction lists to ordinary binary graph data in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_compile :
    ComputableInPolyTime F.compile F.encProgram encAndOrGraph := by
  have h := Word.computableInPolyTime_compile.comp F.computableInPolyTime_expand
  change ComputableInPolyTime (fun p => Word.compile (F.expand p)) _ _ at h
  simpa only [← compile_eq_expand] using h

end Language
end Cslib.Complexity.NCL.Word.Fixed
