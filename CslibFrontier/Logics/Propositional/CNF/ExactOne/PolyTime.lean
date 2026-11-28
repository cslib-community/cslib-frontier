/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.ExactOne
public import CslibFrontier.Logics.Propositional.CNF.ExactOne.Compile
public import CslibFrontier.Logics.Propositional.CNF.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum

/-!
# Polynomial-time exact-one encoding

The ordinary CNF encoding of exact-one semantics enumerates pairs of literal positions. Its
construction is polynomial-time under the existing list and literal encodings. This is a
semantic bridge, separate from the positive exact-three reduction.

## Main results

* `Clause.computableInPolyTime_oneEncoding`: encode one exact-one clause.
* `CNF.computableInPolyTime_oneEncoding`: encode an exact-one formula.

## References

These are original computational certificates for the existing positional encoding.
-/

@[expose] public section

namespace Cslib.Logic.PL

open Turing.MultiTapeTM

variable {V : Type}

/-- Enumerate each later literal position after its first position. -/
theorem Clause.atMostOneOccurrences_eq_flatMap (c : Clause V) :
    c.atMostOneOccurrences = c.zipIdx.flatMap fun p =>
      (c.drop (p.2 + 1)).map fun l => [Std.Sat.Literal.negate p.1, Std.Sat.Literal.negate l] := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    simp only [Clause.atMostOneOccurrences, List.zipIdx_cons', List.flatMap_cons,
      List.flatMap_map, List.drop_succ_cons, List.drop_zero]
    rw [ih]
    rfl

/-- The positional pair clauses can be emitted in polynomial time. -/
@[fun_prop]
theorem Clause.computableInPolyTime_atMostOneOccurrences (enc : V ↪ List Bool) :
    ComputableInPolyTime (Clause.atMostOneOccurrences (V := V))
      (encClause enc) (encCNFOver enc) := by
  rw [funext Clause.atMostOneOccurrences_eq_flatMap]
  fun_prop

/-- Exact-one clause encoding is polynomial-time for any fixed variable encoding. -/
@[fun_prop]
theorem Clause.computableInPolyTime_oneEncoding (enc : V ↪ List Bool) :
    ComputableInPolyTime (Clause.oneEncoding (V := V))
      (encClause enc) (encCNFOver enc) := by
  unfold Clause.oneEncoding
  fun_prop

/-- Exact-one formula encoding is polynomial-time for any fixed variable encoding. -/
@[fun_prop]
theorem CNF.computableInPolyTime_oneEncoding (enc : V ↪ List Bool) :
    ComputableInPolyTime (CNF.oneEncoding (V := V))
      (encCNFOver enc) (encCNFOver enc) := by
  unfold CNF.oneEncoding
  fun_prop

end Cslib.Logic.PL

namespace Cslib.Logic.PL.CNF.FromSAT

open Turing.MultiTapeTM

variable {V : Type}

/-- Source labels retain their encoding; local clause and slot indices are unary. -/
def encVariable (enc : V ↪ List Bool) : Variable V ↪ List Bool :=
  encSum enc (encPair encUnary encUnary)

private def selectedLiteral (i k : ℕ) (c : Clause V) : Literal (Variable V) :=
  if k < c.length then (c.map lift).getD k (padding 0 0) else padding i k

private theorem clause_eq_selected (i : ℕ) (c : Clause V) :
    clause i c = core i (selectedLiteral i 0 c) (selectedLiteral i 1 c)
      (selectedLiteral i 2 c) ++
      (if c.length < 1 then forcePadding i 0 else []) ++
      (if c.length < 2 then forcePadding i 1 else []) ++
      (if c.length < 3 then forcePadding i 2 else []) := by
  rcases c with _ | ⟨p, _ | ⟨q, _ | ⟨r, rest⟩⟩⟩ <;>
    simp [clause, selectedLiteral, List.getD]

@[local fun_prop]
private theorem computableInPolyTime_aux {α : Type} {encA : α ↪ List Bool}
    (enc : V ↪ List Bool) {i : α → ℕ} (k : ℕ) (hi : ComputableInPolyTime i encA encUnary) :
    ComputableInPolyTime (fun a => aux (V := V) (i a) k) encA (encVariable enc) := by
  unfold aux encVariable
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_selectedLiteral (enc : V ↪ List Bool) (k : ℕ) :
    ComputableInPolyTime (fun p : ℕ × Clause V => selectedLiteral p.1 k p.2)
      (encPair encUnary (encList (encPair enc encBool)))
      (encPair (encVariable enc) encBool) := by
  fun_prop [lift, padding, aux, selectedLiteral]

attribute [local irreducible] encVariable

@[local fun_prop]
private theorem computableInPolyTime_core (enc : V ↪ List Bool) :
    ComputableInPolyTime
      (fun p : ℕ × Literal (Variable V) × Literal (Variable V) × Literal (Variable V) =>
        core p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair (encPair (encVariable enc) encBool)
        (encPair (encPair (encVariable enc) encBool) (encPair (encVariable enc) encBool))))
      (encList (encList (encPair (encVariable enc) encBool))) := by
  unfold core ExactOneGadget.disjunctionClauses Std.Sat.Literal.negate
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_forcePadding (enc : V ↪ List Bool) (k : ℕ) :
    ComputableInPolyTime (fun i : ℕ => forcePadding (V := V) i k) encUnary
      (encList (encList (encPair (encVariable enc) encBool))) := by
  unfold forcePadding ExactOneGadget.forceFalseClauses
  fun_prop

/-- One ordinary-clause replacement is native polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_clause (enc : V ↪ List Bool) :
    ComputableInPolyTime (fun p : ℕ × Clause V => clause p.1 p.2)
      (encPair encUnary (encClause enc)) (encCNFOver (encVariable enc)) := by
  rw [funext fun p : ℕ × Clause V => clause_eq_selected p.1 p.2]
  refine ComputableInPolyTime.listAppend'
    (ComputableInPolyTime.listAppend'
      (ComputableInPolyTime.listAppend' ?_ ?_) ?_) ?_ <;> fun_prop

/-- The ordinary clause replacements are polynomial-time under the original label encoding. -/
@[fun_prop]
theorem computableInPolyTime_formula (enc : V ↪ List Bool) :
    ComputableInPolyTime (formula (V := V))
      (encCNFOver enc) (encCNFOver (encVariable enc)) := by
  unfold formula
  fun_prop

end Cslib.Logic.PL.CNF.FromSAT

namespace Cslib.Logic.PL.CNF.PositiveExactOne

open Turing.MultiTapeTM

variable {V : Type}

/-- Source labels retain their encoding; clause, literal, and auxiliary positions are unary. -/
def encVariable (enc : V ↪ List Bool) : Variable V ↪ List Bool :=
  encSum enc (encPair (encPair encUnary encUnary) encUnary)

@[local fun_prop]
private theorem computableInPolyTime_inl {α : Type} {encA : α ↪ List Bool}
    (enc : V ↪ List Bool) {f : α → V} (hf : ComputableInPolyTime f encA enc) :
    ComputableInPolyTime (fun a => (Sum.inl (f a) : Variable V)) encA (encVariable enc) := by
  unfold encVariable
  fun_prop

@[local fun_prop]
private theorem computableInPolyTime_auxiliary {α : Type} {encA : α ↪ List Bool}
    (enc : V ↪ List Bool) {i j : α → ℕ} (k : ℕ)
    (hi : ComputableInPolyTime i encA encUnary) (hj : ComputableInPolyTime j encA encUnary) :
    ComputableInPolyTime (fun a => auxiliary (V := V) (i a) (j a) k) encA (encVariable enc) := by
  unfold auxiliary encVariable
  fun_prop

attribute [local irreducible] encVariable

private theorem computableInPolyTime_positiveLiteral (enc : V ↪ List Bool) :
    ComputableInPolyTime
      (fun p : (ℕ × Clause V) × (Literal V × ℕ) => positiveLiteral p.1.1 p.2.2 p.2.1)
      (encPair (encPair encUnary (encList (encPair enc encBool)))
        (encPair (encPair enc encBool) encUnary))
      (encPair (encVariable enc) encBool) := by
  unfold positiveLiteral
  fun_prop

private theorem computableInPolyTime_complementBlock (enc : V ↪ List Bool) :
    ComputableInPolyTime
      (fun p : (ℕ × Clause V) × (Literal V × ℕ) => complementBlock p.1.1 p.2.2 p.2.1)
      (encPair (encPair encUnary (encList (encPair enc encBool)))
        (encPair (encPair enc encBool) encUnary))
      (encList (encList (encPair (encVariable enc) encBool))) := by
  unfold complementBlock ExactOneGadget.complementClauses ExactOneGadget.forceFalseClauses
  fun_prop

private theorem computableInPolyTime_clauseClauses (enc : V ↪ List Bool) :
    ComputableInPolyTime (fun p : ℕ × Clause V => clauseClauses p.1 p.2)
      (encPair encUnary (encList (encPair enc encBool)))
      (encList (encList (encPair (encVariable enc) encBool))) := by
  have hzip := (ComputableInPolyTime.zipIdx (encPair enc encBool)).comp'
    (ComputableInPolyTime.snd encUnary (encList (encPair enc encBool)))
  exact ComputableInPolyTime.listAppend'
    (ComputableInPolyTime.cons'
      (ComputableInPolyTime.mapWithInput hzip (computableInPolyTime_positiveLiteral enc))
      (ComputableInPolyTime.const []))
    (ComputableInPolyTime.flatMapWithInput hzip (computableInPolyTime_complementBlock enc))

/-- Eliminating all negative occurrences is native polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_formula (enc : V ↪ List Bool) :
    ComputableInPolyTime (formula (V := V))
      (encCNFOver enc) (encCNFOver (encVariable enc)) := by
  have hswap : ComputableInPolyTime (fun p : CNF V × (Clause V × ℕ) => (p.2.2, p.2.1))
      (encPair (encList (encList (encPair enc encBool)))
        (encPair (encList (encPair enc encBool)) encUnary))
      (encPair encUnary (encList (encPair enc encBool))) := by fun_prop
  exact ComputableInPolyTime.flatMapWithInput
    (ComputableInPolyTime.zipIdx (encList (encPair enc encBool)))
    ((computableInPolyTime_clauseClauses enc).comp' hswap)

end Cslib.Logic.PL.CNF.PositiveExactOne

namespace Cslib.Logic.PL.CNF.PositiveExactOneCompile

open Turing.MultiTapeTM

variable {V : Type}

/-- The two local auxiliary families use unary indices and retain the source label encoding. -/
def encVariable (enc : V ↪ List Bool) : Variable V ↪ List Bool :=
  PositiveExactOne.encVariable (FromSAT.encVariable enc)

/-- Composing the two local replacements is native polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_rawFormula (enc : V ↪ List Bool) :
    ComputableInPolyTime (rawFormula (V := V))
      (encCNFOver enc) (encCNFOver (encVariable enc)) :=
  (PositiveExactOne.computableInPolyTime_formula (FromSAT.encVariable enc)).comp
    (FromSAT.computableInPolyTime_formula enc)

/-- Compact output labels are computed as bounded unary ranks, then encoded in binary. -/
@[fun_prop]
theorem computableInPolyTime_formula [DecidableEq V] (enc : V ↪ List Bool) :
    ComputableInPolyTime (formula (V := V))
      (encCNFOver enc) (encCNFOver encNat) := by
  have hr := (CNF.computableInPolyTime_relabel ComputableInPolyTime.unary_to_binary).comp
    ((CNF.isPolyTime_compact (encVariable enc)).comp (computableInPolyTime_rawFormula enc))
  have he (ψ : CNF ℕ) : ψ.relabel (fun n => n) = ψ := CNF.relabel_id ψ
  change ComputableInPolyTime (fun φ => (rawFormula φ).compact) _ _
  simpa only [Function.comp_def, he] using hr

end Cslib.Logic.PL.CNF.PositiveExactOneCompile
