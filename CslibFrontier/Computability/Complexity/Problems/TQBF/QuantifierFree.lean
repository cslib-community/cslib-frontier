/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Space.TQBF.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Quantifier-free Boolean formulas and their polynomial-time evaluation

`QBF.QuantifierFree` identifies Boolean formulas within the existing QBF syntax. A scan of the
prefix tokens from right to left evaluates such formulas with a stack of truth values. Both
quantifier-freeness and evaluation under the indicator of a list of variables are polynomial-time
on the existing `encQBF` encoding. This common API serves TAUTOLOGY and bounded quantified SAT.

## Main results

* `Cslib.Logic.PL.QBF.quantifierFree_iff_tokens`: recognize quantifier-free syntax.
* `Cslib.Logic.PL.QBF.foldl_evalStep`: correctness of the evaluating scan.
* `Cslib.Complexity.computableInPolyTime_decide_quantifierFree`.
* `Cslib.Complexity.computableInPolyTime_evalTokens`.

Boolean formulas are as in [Arora–Barak, Section 2.3][AroraBarak09]. The scan is adapted from
Samuel Schlesinger's free-variable scan, with truth values in place of variable lists.
-/

public section

namespace Cslib.Logic.PL.QBF

variable {V : Type*}

/-- A formula is *quantifier-free*, a Boolean formula, when it has no quantifier. -/
def QuantifierFree : QBF V → Prop
  | .var _ => True
  | .top => True
  | .bot => True
  | .not φ => φ.QuantifierFree
  | .and φ ψ => φ.QuantifierFree ∧ ψ.QuantifierFree
  | .or φ ψ => φ.QuantifierFree ∧ ψ.QuantifierFree
  | .ex _ _ => False
  | .all _ _ => False

@[simp] theorem quantifierFree_var (v : V) : (var v).QuantifierFree := trivial

@[simp] theorem quantifierFree_top : (top : QBF V).QuantifierFree := trivial

@[simp] theorem quantifierFree_bot : (bot : QBF V).QuantifierFree := trivial

@[simp] theorem quantifierFree_not {φ : QBF V} : φ.not.QuantifierFree ↔ φ.QuantifierFree :=
  Iff.rfl

@[simp] theorem quantifierFree_and {φ ψ : QBF V} :
    (φ.and ψ).QuantifierFree ↔ φ.QuantifierFree ∧ ψ.QuantifierFree := Iff.rfl

@[simp] theorem quantifierFree_or {φ ψ : QBF V} :
    (φ.or ψ).QuantifierFree ↔ φ.QuantifierFree ∧ ψ.QuantifierFree := Iff.rfl

@[simp] theorem not_quantifierFree_ex (v : V) (φ : QBF V) : ¬(ex v φ).QuantifierFree := id

@[simp] theorem not_quantifierFree_all (v : V) (φ : QBF V) : ¬(all v φ).QuantifierFree := id

/-- Embedding a conjunctive normal form produces a quantifier-free Boolean formula. -/
@[simp] theorem quantifierFree_ofCNF (φ : CNF V) : (ofCNF φ).QuantifierFree := by
  have hc (c : Clause V) : (ofClause c).QuantifierFree := by
    induction c with
    | nil => trivial
    | cons l c ih => exact ⟨by cases l.2 <;> trivial, ih⟩
  induction φ with
  | nil => trivial
  | cons c φ ih => exact ⟨hc c, ih⟩

/-- A formula is quantifier-free exactly when none of its tokens is a quantifier. -/
theorem quantifierFree_iff_tokens {φ : QBF ℕ} :
    φ.QuantifierFree ↔ ∀ t ∈ φ.tokens, t.1.isQuantifier = false := by
  induction φ with
  | var v => simp [QuantifierFree, tokens, Kind.isQuantifier]
  | top => simp [QuantifierFree, tokens, Kind.isQuantifier]
  | bot => simp [QuantifierFree, tokens, Kind.isQuantifier]
  | not φ ih => simp [QuantifierFree, tokens, Kind.isQuantifier, ih]
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp only [QuantifierFree, tokens, ihφ, ihψ, List.mem_cons, List.mem_append]
    refine ⟨fun ⟨h₁, h₂⟩ t ht => ?_, fun h => ⟨fun t ht => h t (.inr (.inl ht)),
      fun t ht => h t (.inr (.inr ht))⟩⟩
    rcases ht with rfl | ht | ht
    exacts [rfl, h₁ t ht, h₂ t ht]
  | ex v φ => simp [QuantifierFree, tokens, Kind.isQuantifier]
  | all v φ => simp [QuantifierFree, tokens, Kind.isQuantifier]

instance : DecidablePred (QuantifierFree : QBF ℕ → Prop) := fun _ =>
  decidable_of_iff _ quantifierFree_iff_tokens.symm

/-- A free variable of a formula occurs as a variable token. -/
theorem mem_tokens_of_mem_freeVars {φ : QBF ℕ} {x : ℕ} (hx : x ∈ φ.freeVars) :
    (Kind.var, x) ∈ φ.tokens := by
  induction φ with
  | var v => simp_all [tokens]
  | top => simp at hx
  | bot => simp at hx
  | not φ ih => exact List.mem_cons_of_mem _ (ih hx)
  | and φ ψ ihφ ihψ =>
    rw [freeVars_and, Finset.mem_union] at hx
    simp only [tokens, List.mem_cons, List.mem_append]
    exact .inr (hx.imp ihφ ihψ)
  | or φ ψ ihφ ihψ =>
    rw [freeVars_or, Finset.mem_union] at hx
    simp only [tokens, List.mem_cons, List.mem_append]
    exact .inr (hx.imp ihφ ihψ)
  | ex v φ ih => exact List.mem_cons_of_mem _ (ih (Finset.mem_of_mem_erase hx))
  | all v φ ih => exact List.mem_cons_of_mem _ (ih (Finset.mem_of_mem_erase hx))

/-- One step of the evaluating scan of the tokens from right to left, for a token of kind `k` and
variable `v`, on the stack of the values of the subformulas read so far. Quantifiers leave the
stack unchanged; the scan is meant for quantifier-free formulas. -/
def evalStepAt (σ : ℕ → Bool) : Kind → ℕ → List Bool → List Bool
  | .var, v, stack => σ v :: stack
  | .top, _, stack => true :: stack
  | .bot, _, stack => false :: stack
  | .not, _, stack => (!stack.headD false) :: stack.tail
  | .and, _, stack => (stack.headD false && stack.tail.headD false) :: stack.tail.tail
  | .or, _, stack => (stack.headD false || stack.tail.headD false) :: stack.tail.tail
  | .ex, _, stack => stack
  | .all, _, stack => stack

/-- One step of the evaluating scan of the tokens from right to left. -/
def evalStep (σ : ℕ → Bool) (stack : List Bool) (t : Kind × ℕ) : List Bool :=
  evalStepAt σ t.1 t.2 stack

/-- **The scan of the tokens** of a quantifier-free formula pushes its value. -/
theorem foldl_evalStep {φ : QBF ℕ} (hφ : φ.QuantifierFree) (σ : ℕ → Bool) (stack : List Bool) :
    φ.tokens.reverse.foldl (evalStep σ) stack = φ.eval σ :: stack := by
  induction φ generalizing stack with
  | var v => rfl
  | top => rfl
  | bot => rfl
  | not φ ih =>
    simp only [tokens, List.reverse_cons, List.foldl_append, ih hφ, List.foldl_cons,
      List.foldl_nil]
    rfl
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp only [tokens, List.reverse_cons, List.reverse_append, List.foldl_append, ihψ hφ.2,
      ihφ hφ.1, List.foldl_cons, List.foldl_nil]
    rfl
  | ex v φ => exact hφ.elim
  | all v φ => exact hφ.elim

end Cslib.Logic.PL.QBF

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM Cslib.Logic.PL ComputableInPolyTime TQBF

/-- Deciding quantifier-freeness is polynomial-time. -/
theorem computableInPolyTime_decide_quantifierFree :
    ComputableInPolyTime (fun φ : QBF ℕ => decide φ.QuantifierFree) encQBF encBool := by
  have h (φ : QBF ℕ) : decide φ.QuantifierFree = φ.tokens.all fun t => !t.1.isQuantifier := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, QBF.quantifierFree_iff_tokens, List.all_eq_true]
    simp
  simp only [h]
  have hk : ComputableInPolyTime (fun p : QBF ℕ × (QBF.Kind × ℕ) => !p.2.1.isQuantifier)
      (encPair encQBF encToken) encBool :=
    (of_finite (encIn := encKind) (encOut := encBool) fun k : QBF.Kind => !k.isQuantifier).comp
      (by fun_prop)
  fun_prop

open Turing.MultiTapeTM.ComputableInPolyTime in
/-- A step of the scan for a fixed kind of token, with the indicator of a list of variables as the
assignment, is polynomial-time. -/
private theorem evalStepAt_pt (k : QBF.Kind) :
    ComputableInPolyTime (fun p : (List ℕ × List Bool) × (QBF.Kind × ℕ) =>
      QBF.evalStepAt (fun v => p.1.1.contains v) k p.2.2 p.1.2)
      (encPair (encPair (encList encNat) (encList encBool)) encToken) (encList encBool) := by
  have hstack := (fst (encPair (encList encNat) (encList encBool)) encToken).snd'
  have hvars := (fst (encPair (encList encNat) (encList encBool)) encToken).fst'
  have hv := (snd (encPair (encList encNat) (encList encBool)) encToken).snd'
  have hmem : ComputableInPolyTime
      (fun p : (List ℕ × List Bool) × (QBF.Kind × ℕ) => p.1.1.contains p.2.2)
      (encPair (encPair (encList encNat) (encList encBool)) encToken) encBool := by fun_prop
  have htail : ComputableInPolyTime
      (fun p : (List ℕ × List Bool) × (QBF.Kind × ℕ) => p.1.2.tail)
      (encPair (encPair (encList encNat) (encList encBool)) encToken)
      (encList encBool) := by fun_prop
  have hhead := (headD (encA := encBool) (encL := encList encBool) false).comp hstack
  have hnext := (headD (encA := encBool) (encL := encList encBool) false).comp htail
  cases k <;> simp only [QBF.evalStepAt]
  · exact hmem.cons' hstack
  · exact (const true).cons' hstack
  · exact (const false).cons' hstack
  · exact (bool_not.comp hhead).cons' htail
  · exact (bool_and' hhead hnext).cons' (by fun_prop)
  · exact (bool_or.comp (hhead.prod hnext)).cons' (by fun_prop)
  · exact hstack
  · exact hstack

/-- A step of the scan is polynomial-time. -/
private theorem evalStep_pt :
    ComputableInPolyTime (fun p : (List ℕ × List Bool) × (QBF.Kind × ℕ) =>
      QBF.evalStep (fun v => p.1.1.contains v) p.1.2 p.2)
      (encPair (encPair (encList encNat) (encList encBool)) encToken) (encList encBool) :=
  finite_cases (tagEncoding := encKind)
    (tag := fun p : (List ℕ × List Bool) × (QBF.Kind × ℕ) => p.2.1)
    (branch := fun k p => QBF.evalStepAt (fun v => p.1.1.contains v) k p.2.2 p.1.2)
    (by fun_prop) evalStepAt_pt

/-- One step of the scan adds at most one value to the stack. -/
private theorem length_evalStep_le (σ : ℕ → Bool) (stack : List Bool) (t : QBF.Kind × ℕ) :
    (encList encBool (QBF.evalStep σ stack t)).length ≤ (encList encBool stack).length + 4 := by
  obtain ⟨k, v⟩ := t
  simp only [QBF.evalStep]
  cases k <;> simp only [QBF.evalStepAt] <;>
    rcases stack with _ | ⟨a, _ | ⟨b, stack⟩⟩ <;>
    simp only [encList_cons, List.length_append, length_frame, encList_nil, List.length_nil,
      List.headD_nil, List.headD_cons, List.tail_nil, List.tail_cons, encBool_apply,
      List.length_singleton] <;> omega

/-- **Evaluating a formula from its tokens is polynomial-time**, under the assignment making
exactly the listed variables true. On a quantifier-free formula the scan returns its value
(`Cslib.Logic.PL.QBF.foldl_evalStep`). -/
theorem computableInPolyTime_evalTokens :
    ComputableInPolyTime (fun p : QBF ℕ × List ℕ =>
      (p.1.tokens.reverse.foldl (QBF.evalStep fun v => p.2.contains v) []).headD false)
      (encPair encQBF (encList encNat)) encBool := by
  have hfold : ComputableInPolyTime (fun p : QBF ℕ × List ℕ =>
      p.1.tokens.reverse.foldl (QBF.evalStep fun v => p.2.contains v) [])
      (encPair encQBF (encList encNat)) (encList encBool) :=
    foldlWith_of_bounded_growth (encA := encToken) (encL := encList encToken)
      (step := fun (l : List ℕ) => QBF.evalStep fun v => l.contains v)
      (par := Prod.snd) (by fun_prop) (by fun_prop) (const []) evalStep_pt
      (growth := fun _ => 4) (.const 4) fun _ stack t _ => length_evalStep_le _ stack t
  fun_prop

end Cslib.Complexity
