/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.SelectorNetwork.Template
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.DPi
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Data.Fintype.Pi

/-!
# Polynomial-time tables at fixed local arity

For a fixed arity budget there are finitely many cell shapes and boundary orientations. Their
actual implementation templates and canonical private directions therefore admit constant-size
lookup tables. Reading the bounded boundary prefix uses the standard `encFinFn` table encoding.

## Main results

* `SelectorNetwork.AndOr.Cell.computableInPolyTime_template`: portable templates at fixed arity.
* `SelectorNetwork.AndOr.Cell.computableInPolyTime_privateBits`: canonical private directions.
-/

public section

attribute [local implicit_reducible] Cslib.Complexity.NCL.Diagram.Inner

namespace Cslib.Complexity.NCL.SelectorNetwork.AndOr

open Diagram _root_.Turing.MultiTapeTM

/-- Cell shapes use the ordinary framed sum encoding, with unary arities. -/
@[expose] def encCell : Cell ↪ List Bool :=
  (show Cell ↪ ℕ ⊕ ℕ ⊕ Bool from
    ⟨fun
      | .row n => .inl n
      | .character n => .inr (.inl n)
      | .relation b => .inr (.inr b), by
        intro c d h
        cases c <;> cases d <;> simp_all⟩).trans
    (encSum encUnary (encSum encUnary encBool))

namespace Cell

/-- The finite set of implementation shapes below one fixed input-arity budget. -/
abbrev Bounded (budget : ℕ) := {c : Cell // c.top.length ≤ budget}

instance (budget : ℕ) : Finite (Bounded budget) := by
  let f : Bounded budget → Fin (budget + 1) ⊕ Fin (budget + 1) ⊕ Bool := fun c =>
    match c with
    | ⟨.row n, h⟩ => .inl ⟨n, by
        simpa only [top, Gadgets.OrTree.length_bundle] using Nat.lt_succ_of_le h⟩
    | ⟨.character n, h⟩ => .inr (.inl ⟨n, by
        simpa only [top, Gadgets.OrTree.length_bundle] using Nat.lt_succ_of_le h⟩)
    | ⟨.relation b, _⟩ => .inr (.inr b)
  apply Finite.of_injective f
  rintro ⟨c, hc⟩ ⟨d, hd⟩ h
  apply Subtype.ext
  cases c <;> cases d <;> simp_all [f]

/-- Restrict the standard shape encoding to a fixed finite arity budget. -/
abbrev encBounded (budget : ℕ) : Bounded budget ↪ List Bool :=
  (Function.Embedding.subtype (fun c : Cell => c.top.length ≤ budget)).trans encCell

/-- Actual portable templates are polynomial-time lookup tables at every fixed arity budget. -/
theorem computableInPolyTime_template (budget : ℕ) :
    ComputableInPolyTime (fun c : Bounded budget => c.val.template)
      (encBounded budget) encTemplate :=
  ComputableInPolyTime.of_finite _

/-- Canonical directions of every private wire, with missing boundary bits read as false. -/
@[expose] def privateBits (c : Cell) (bits : List Bool) : List Bool :=
  (Diagram.Replacement.innerList c.openSim).map fun e =>
    c.openSim.enc (fun x => bits.getD (finSumFinEquiv x).val false) e.val

private theorem computableInPolyTime_boundaryPrefix (count : ℕ) :
    ComputableInPolyTime (fun bits : List Bool => fun i : Fin count => bits.getD i.val false)
      (encList encBool) (encFinFn count encBool) := by
  have hi : ComputableInPolyTime (fun p : List Bool × Fin count => p.2.val)
      (encPair (encList encBool) (encFinEnum (Fin count))) encUnary :=
    (ComputableInPolyTime.of_finite (fun i : Fin count => i.val)).comp
      (ComputableInPolyTime.snd (encList encBool) (encFinEnum (Fin count)))
  have hread : ComputableInPolyTime (fun p : List Bool × Fin count => p.1.getD p.2.val false)
      (encPair (encList encBool) (encFinEnum (Fin count))) encBool := by fun_prop
  exact (ComputableInPolyTime.mapWithInput (f := fun bits (i : Fin count) => bits.getD i.val false)
    (ComputableInPolyTime.const (List.finRange count)) hread).of_enc_eq
      fun bits => by simp only [encFinFn_apply, List.ofFn_eq_map]

private theorem boundary_length_le {budget : ℕ} (c : Bounded budget) :
    c.val.top.length + c.val.bottom.length ≤ budget + 2 :=
  Nat.add_le_add c.property (by cases c.val <;> simp [bottom])

/-- Canonical private directions are polynomial-time at each fixed local arity budget. -/
theorem computableInPolyTime_privateBits (budget : ℕ) :
    ComputableInPolyTime (fun p : Bounded budget × List Bool => p.1.val.privateBits p.2)
      (encPair (encBounded budget) (encList encBool)) (encList encBool) := by
  let lookup : Bounded budget × (Fin (budget + 2) → Bool) → List Bool := fun p =>
    (Diagram.Replacement.innerList p.1.val.openSim).map fun e =>
      p.1.val.openSim.enc (fun x => p.2
        ((finSumFinEquiv x).castLE (boundary_length_le p.1))) e.val
  have hs := (computableInPolyTime_boundaryPrefix (budget + 2)).comp
    (ComputableInPolyTime.snd (encBounded budget) (encList encBool))
  simpa only [lookup, privateBits, Function.comp_def, Fin.val_castLE] using
    (ComputableInPolyTime.of_finite lookup).comp
      ((ComputableInPolyTime.fst (encBounded budget) (encList encBool)).prod hs)

end Cell
end Cslib.Complexity.NCL.SelectorNetwork.AndOr
