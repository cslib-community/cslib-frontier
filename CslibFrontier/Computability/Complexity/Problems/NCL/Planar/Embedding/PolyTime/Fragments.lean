/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.Cells
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.Fixed
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Bits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Fixed planar fragments for incidence drawings

The finite instruction alphabet records the boundary colors and orientation bits of one source,
cap, or crossing. Its primitive expansion is the actual embedding template; its configuration
table records the canonical created-edge bits of that same template.

## Main definitions

* `Planar.Embedding.PolyTime.Opcode`: the finite source, cap, and crossover instructions.
* `Planar.Embedding.PolyTime.fragments`: their fixed primitive diagram table.
* `Planar.Embedding.PolyTime.configurationBits`: concatenated canonical fragment bits.

## Main results

* `Planar.Embedding.PolyTime.computableInPolyTime_configurationBits`: standard PT serialization.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Planar.Embedding.PolyTime

open Diagram _root_.Turing.MultiTapeTM

/-- One constant planar fragment and its boundary orientation parameters. -/
inductive Opcode
  /-- A three-port source, in the original port order. -/
  | source (first second third : Color) (firstBit secondBit thirdBit : Bool)
  /-- A same-color cap, with its two top incidence directions. -/
  | cap (color : Color) (firstBit secondBit : Bool)
  /-- A crossing, with its top directions in wire order. -/
  | cross (first second : Color) (firstBit secondBit : Bool)
  deriving @[expose] DecidableEq

instance : FinEnum Opcode :=
  FinEnum.ofSurjective
    (fun p : Fin 3 × (Fin 6 → Bool) =>
      let c := fun b => if b then Color.blue else Color.red
      match p.1.val with
      | 0 => .source (c (p.2 0)) (c (p.2 1)) (c (p.2 2)) (p.2 3) (p.2 4) (p.2 5)
      | 1 => .cap (c (p.2 0)) (p.2 1) (p.2 2)
      | _ => .cross (c (p.2 0)) (c (p.2 1)) (p.2 2) (p.2 3))
    (by
      intro op
      cases op with
      | source c d e x y z =>
        refine ⟨(0, ![c == .blue, d == .blue, e == .blue, x, y, z]), ?_⟩
        cases c <;> cases d <;> cases e <;> rfl
      | cap c x y =>
        refine ⟨(1, ![c == .blue, x, y, false, false, false]), ?_⟩
        cases c <;> rfl
      | cross c d x y =>
        refine ⟨(2, ![c == .blue, d == .blue, x, y, false, false]), ?_⟩
        cases c <;> cases d <;> rfl)

/-- The exact source, cap, and crossover diagrams used in canonical planarization. -/
@[expose] def fragments : Word.Fixed.Language where
  Opcode := Opcode
  enumeration := inferInstance
  fragment op := match op with
    | .source c d e _ _ _ => ⟨[], [c, d, e], .gen [genVertex [] [c, d, e] 2]⟩
    | .cap c _ _ => ⟨[c, c], [], Gadgets.Wire.cap c⟩
    | .cross c d _ _ => ⟨[c, d], [d, c], Crossover.diagram c d⟩

/-- The fixed-language instruction format, with each fragment tag paired with a wire offset. -/
abbrev Program := List (ℕ × Opcode)

/-- Expand the fixed planar template table on a concrete instruction stream. -/
@[expose] def expand (p : Program) : Word := fragments.expand p

/-- Frame instructions using unary offsets and the fragment table's fixed finite tag encoding. -/
abbrev encProgram : Program ↪ List Bool := fragments.encProgram

/-- Canonical created-edge directions of a fixed instruction. -/
@[expose] def Opcode.configuration : Opcode → List Bool
  | .source _ _ _ x y z => [x, y, z]
  | .cap c x y =>
      (Cell.expandOpenSim (.cap c)).bits (Sum.elim (fun i => ![x, y] i) Fin.elim0)
  | .cross c d x y =>
      (Crossover.openSim c d).bits (Sum.elim (fun i => ![x, y] i) (fun i => ![y, x] i))

/-- Serialize the canonical fragment extensions in instruction order. -/
@[expose] def configurationBits (p : Program) : List Bool :=
  p.flatMap fun instruction => instruction.2.configuration

/-- Sequential instruction streams expand by concatenation. -/
theorem expand_append (p q : Program) :
    expand (p ++ q) = expand p ++ expand q := by
  dsimp only [expand, Word.Fixed.Language.expand, fragments]
  exact List.flatMap_append

/-- Sequential instruction streams serialize by concatenation. -/
theorem configurationBits_append (p q : Program) :
    configurationBits (p ++ q) = configurationBits p ++ configurationBits q :=
  List.flatMap_append

/-- One crossover instruction is the actual fixed crossover word at that offset. -/
theorem expand_cross (k : ℕ) (c d : Color) (x y : Bool) :
    expand [(k, Opcode.cross c d x y)] =
      (Crossover.diagram c d).toWord Prim.interp k := by
  dsimp only [expand, Word.Fixed.Language.expand, Word.Fixed.Language.word, fragments]
  exact List.append_nil _

/-- A single instruction serializes its canonical created-edge bits. -/
theorem configurationBits_singleton (k : ℕ) (op : Opcode) :
    configurationBits [(k, op)] = op.configuration := List.append_nil _

/-- Emit the first fragment before the remaining stream. -/
theorem expand_cons (i : ℕ × Opcode) (p : Program) :
    expand (i :: p) = fragments.word i.2 i.1 ++ expand p := by
  dsimp only [expand, Word.Fixed.Language.expand, fragments]
  exact List.flatMap_cons

/-- Serialize the first fragment before the remaining stream. -/
theorem configurationBits_cons (i : ℕ × Opcode) (p : Program) :
    configurationBits (i :: p) = i.2.configuration ++ configurationBits p :=
  List.flatMap_cons

/-- Expand the concrete incidence instruction format in standard polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_expand :
    ComputableInPolyTime expand encProgram encWord := fragments.computableInPolyTime_expand

private instance : Finite Color := Finite.of_injective (fun c : Color => c == .blue)
  (by intro c d h; cases c <;> cases d <;> simp_all)

private abbrev encSignal := encPair encColor encBool

/-- Assemble a source instruction from computed colors and boundary directions. -/
@[fun_prop]
theorem Opcode.computableInPolyTime_source {α : Type} {input : α ↪ List Bool}
    {c d e : α → Color} {x y z : α → Bool}
    (hc : ComputableInPolyTime c input encColor) (hd : ComputableInPolyTime d input encColor)
    (he : ComputableInPolyTime e input encColor) (hx : ComputableInPolyTime x input encBool)
    (hy : ComputableInPolyTime y input encBool) (hz : ComputableInPolyTime z input encBool) :
    ComputableInPolyTime (fun a => Opcode.source (c a) (d a) (e a) (x a) (y a) (z a))
      input fragments.encOpcode := by
  simpa only [Function.comp_def] using (ComputableInPolyTime.of_finite
    (fun p : (Color × Bool) × (Color × Bool) × (Color × Bool) =>
      Opcode.source p.1.1 p.2.1.1 p.2.2.1 p.1.2 p.2.1.2 p.2.2.2)).comp
    ((hc.prod hx).prod ((hd.prod hy).prod (he.prod hz)))

/-- Assemble a cap instruction from its computed color and boundary directions. -/
@[fun_prop]
theorem Opcode.computableInPolyTime_cap {α : Type} {input : α ↪ List Bool}
    {c : α → Color} {x y : α → Bool} (hc : ComputableInPolyTime c input encColor)
    (hx : ComputableInPolyTime x input encBool) (hy : ComputableInPolyTime y input encBool) :
    ComputableInPolyTime (fun a => Opcode.cap (c a) (x a) (y a)) input fragments.encOpcode := by
  simpa only [Function.comp_def] using (ComputableInPolyTime.of_finite
    (fun p : Color × Bool × Bool => Opcode.cap p.1 p.2.1 p.2.2)).comp (hc.prod (hx.prod hy))

/-- Assemble a crossing instruction from its computed colors and top directions. -/
@[fun_prop]
theorem Opcode.computableInPolyTime_cross {α : Type} {input : α ↪ List Bool}
    {c d : α → Color} {x y : α → Bool} (hc : ComputableInPolyTime c input encColor)
    (hd : ComputableInPolyTime d input encColor) (hx : ComputableInPolyTime x input encBool)
    (hy : ComputableInPolyTime y input encBool) :
    ComputableInPolyTime (fun a => Opcode.cross (c a) (d a) (x a) (y a))
      input fragments.encOpcode := by
  simpa only [Function.comp_def] using (ComputableInPolyTime.of_finite
    (fun p : (Color × Bool) × (Color × Bool) => Opcode.cross p.1.1 p.2.1 p.1.2 p.2.2)).comp
    ((hc.prod hx).prod (hd.prod hy))

/-- Finite-table lookup and list concatenation serialize configurations in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_configurationBits :
    ComputableInPolyTime configurationBits encProgram (encList encBool) := by
  exact .flatMapWithInput .id' ((ComputableInPolyTime.of_finite
    (encIn := fragments.encOpcode) Opcode.configuration).comp
    ((ComputableInPolyTime.snd _ _).snd'))

end Cslib.Complexity.NCL.Planar.Embedding.PolyTime
