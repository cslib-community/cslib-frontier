/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.VeriPB
public import CslibFrontier.Logics.Propositional.CuttingPlanes
import CslibFrontier.Logics.Propositional.CuttingPlanes.Completeness
import CslibFrontier.Logics.Propositional.PseudoBoolean.Fast
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# VeriPB `pol` proofs are cutting planes proofs

A pseudo-Boolean constraint `∑ aᵢ ℓᵢ ≥ d` is the integer linear inequality
`∑ aᵢ ℓᵢ ≥ d` with `ℓᵢ` read as `xᵥ` or `1 - xᵥ` (`Cslib.Logic.PL.PBConstr.toIneq`): the sum of the
literal axioms `aᵢ • ℓᵢ ≥ 0` of `Cslib.Logic.PL.Literal.toIneq` and `0 ≥ d`. It has the same
solutions (`Cslib.Logic.PL.PBConstr.holds_toIneq_iff`), and a clause's constraint is its cutting
planes inequality (`Cslib.Logic.PL.Clause.toIneq_toPB`). By refutation completeness of cutting
planes, the inequalities of a list of constraints are refutable iff the constraints have no common
0/1 solution (`Cslib.Logic.PL.PBConstr.exists_refutableInSize_toIneq_iff`), and by implicational
completeness the inequality of a constraint is derivable from them iff it holds at all their
common 0/1 solutions (`Cslib.Logic.PL.PBConstr.exists_derivableInSize_toIneq_iff`).

A VeriPB proof whose steps are `pol` steps without saturation, and deletions, translates into a
cutting planes proof (`Cslib.Logic.PL.CuttingPlanes.IsProof`) of the same contradiction: if the
checker accepts it, the inequalities of the formula have a cutting planes refutation
(`Cslib.Logic.PL.VeriPB.exists_isProof_contra_of_check`). Each step is a cutting planes
derivation:

* addition and multiplication are the rules of the same name;
* normalization cancels `aᵢ xᵥ` against `aⱼ (1 - xᵥ)`, which changes the inequality not at all, or
  produces a constraint of degree `0`, the sum of literal axioms;
* VeriPB's division rounds every coefficient up: adding the literal axioms
  `(k ⌈aᵢ / k⌉ - aᵢ) • ℓᵢ ≥ 0` makes every coefficient a multiple of `k`, and rounded division
  then gives the result;
* weakening on `xᵥ` adds `aᵢ • ¬ℓᵢ ≥ 0` to the terms on `xᵥ`;
* a contradiction `∑ aᵢ ℓᵢ ≥ d` with `∑ aᵢ < d` plus `∑ aᵢ • ¬ℓᵢ ≥ 0` is `0 ≥ d - ∑ aᵢ`, and
  `0 ≥ 1` follows by lowering the bound with `xᵥ ≥ 0` plus `-xᵥ ≥ -1`.

Saturation is not a rule of cutting planes, so proofs using it are excluded.

**Sizes.** The translation derives each constraint of the database once, as a line that later
steps reference again: a cutting planes proof is a list of lines whose premises are any earlier
lines (`Cslib.Logic.PL.CuttingPlanes.IsProof`). A proof with `m` operations on the constraints `F`
gives a refutation with at most `16 (|S| + 1) (|F| + m + 1)` lines, when the variables of `F` and
of the literal axioms of the proof are in `S` (`Cslib.Logic.PL.VeriPB.refutableInSize_of_check`).
The factor `|S| + 1` bounds the number of terms of a normalized constraint: rounding-up division,
weakening, a normalization that clamps the degree at `0`, and the final contradiction each add a
literal axiom per term. It cannot be dropped: no bound in `|F|`, the number of steps and the number
of operations alone exists (`Cslib.Logic.PL.VeriPB.not_exists_refutableInSize_of_check`). The
kernel refutes `x₀ + ⋯ + x_{w-1} ≥ w + 1` with no steps, since the constraint is a contradiction,
while every cutting planes refutation of it uses each axiom `-xᵥ ≥ -1` for `v < w`
(`Cslib.Logic.PL.VeriPB.le_of_refutableInSize_wideContra`). Coefficient sizes are not measured.

## Main definitions

* `Cslib.Logic.PL.PBConstr.toIneq`: a constraint as an inequality.
* `Cslib.Logic.PL.VeriPB.Step.IsCP`: a `pol` step without saturation, or a deletion.
* `Cslib.Logic.PL.VeriPB.Step.opCount`, `Cslib.Logic.PL.VeriPB.opCount`: the number of `pol`
  operations of a step and of a list of steps.
* `Cslib.Logic.PL.VeriPB.wideContra`: the constraint `x₀ + ⋯ + x_{w-1} ≥ w + 1`.

## Main results

* `Cslib.Logic.PL.PBConstr.holds_toIneq_iff`: the translation is faithful.
* `Cslib.Logic.PL.PBConstr.exists_refutableInSize_toIneq_iff`: cutting planes refute a list of
  constraints iff it has no 0/1 solution.
* `Cslib.Logic.PL.PBConstr.exists_derivableInSize_toIneq_iff`: cutting planes derive a
  constraint from a list iff the list implies it over 0/1 assignments.
* `Cslib.Logic.PL.VeriPB.refutableInSize_of_check`,
  `Cslib.Logic.PL.VeriPB.exists_isProof_contra_of_check`: a checked proof of `UNSAT` made of
  such steps gives a cutting planes refutation, with at most `16 (|S| + 1) (|F| + m + 1)` lines.
* `Cslib.Logic.PL.VeriPB.check_wideContra`,
  `Cslib.Logic.PL.VeriPB.le_of_refutableInSize_wideContra`: the kernel refutes `wideContra w` with
  no steps, cutting planes need at least `w` lines.
* `Cslib.Logic.PL.VeriPB.not_exists_refutableInSize_of_check`: no line count in the number of
  constraints, steps and operations alone.
* `Cslib.Logic.PL.VeriPB.exists_isProof_contra_of_check_cnf`: the same for the clauses of a CNF.
-/

public section

namespace Cslib.Logic.PL

open Ineq PBConstr

/-! ### Operation counts -/

namespace VeriPB

mutual

/-- The number of operations of a step: those of a `pol` step, and those of the steps of a `pbc`
subproof. -/
@[expose] def Step.opCount : Step → ℕ
  | .pol ops => ops.length
  | .pbc _ sub _ => VeriPB.opCount sub
  | _ => 0

/-- The number of `pol` operations of a list of steps, including those of `pbc` subproofs
(`Cslib.Logic.PL.VeriPB.Step.opCount`). -/
@[expose] def opCount : List Step → ℕ
  | [] => 0
  | s :: ss => s.opCount + VeriPB.opCount ss

end

@[simp] theorem opCount_nil : opCount [] = 0 := rfl

@[simp] theorem opCount_cons (s : Step) (ss : List Step) :
    opCount (s :: ss) = s.opCount + opCount ss := rfl

end VeriPB

noncomputable section

/-! ### Constraints as inequalities -/

/-- The inequality of a term `a ℓ`: `a` times the literal axiom `ℓ ≥ 0`. -/
@[expose] def PBConstr.termIneq (t : ℕ × Literal ℕ) : Ineq ℕ := t.1 • t.2.toIneq

/-- A constraint `∑ aᵢ ℓᵢ ≥ d` as the inequality `∑ aᵢ ℓᵢ ≥ d`, with `ℓᵢ` read as `xᵥ` or
`1 - xᵥ`. -/
@[expose] def PBConstr.toIneq (c : PBConstr) : Ineq ℕ := (c.terms.map termIneq).sum + ⟨0, c.degree⟩

theorem PBConstr.coeff_termIneq (t : ℕ × Literal ℕ) :
    (termIneq t).coeff = Finsupp.single (termVar t) (termCoeff t) := by
  obtain ⟨a, v, b⟩ := t
  cases b <;> simp [termIneq, Literal.toIneq, termVar_mk, termCoeff, termPos_mk]

theorem PBConstr.bound_termIneq (t : ℕ × Literal ℕ) :
    (termIneq t).bound = -(if termPos t then 0 else (t.1 : ℤ)) := by
  obtain ⟨a, v, b⟩ := t
  cases b <;> simp [termIneq, Literal.toIneq, termPos_mk]

theorem PBConstr.coeff_sum_termIneq (ts : List (ℕ × Literal ℕ)) :
    (ts.map termIneq).sum.coeff =
      (ts.map fun t => Finsupp.single (termVar t) (termCoeff t)).sum := by
  induction ts with
  | nil => simp only [List.map_nil, List.sum_nil, coeff_zero]
  | cons t ts ih => simp only [List.map_cons, List.sum_cons, coeff_add, ih, coeff_termIneq]

theorem PBConstr.bound_sum_termIneq (ts : List (ℕ × Literal ℕ)) :
    (ts.map termIneq).sum.bound = -(negSum ts : ℤ) := by
  induction ts with
  | nil => simp only [List.map_nil, List.sum_nil, bound_zero, negSum, Nat.cast_zero, neg_zero]
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, bound_add, ih, bound_termIneq, negSum]
    split <;> simp only [Nat.cast_add, zero_add] <;> ring

theorem PBConstr.coeff_toIneq (c : PBConstr) :
    c.toIneq.coeff = (c.terms.map fun t => Finsupp.single (termVar t) (termCoeff t)).sum := by
  simp only [toIneq, coeff_add, coeff_sum_termIneq, add_zero]

theorem PBConstr.bound_toIneq (c : PBConstr) :
    c.toIneq.bound = (c.degree : ℤ) - negSum c.terms := by
  simp only [toIneq, bound_add, bound_sum_termIneq]
  ring

theorem Literal.lhs_sub_bound_toIneq (σ : ℕ → Bool) (l : Literal ℕ) :
    l.toIneq.lhs σ - l.toIneq.bound = ((Literal.eval σ l).toNat : ℤ) := by
  obtain ⟨v, b⟩ := l
  cases b <;> cases h : σ v <;>
    simp [Literal.toIneq, Ineq.leOne, Ineq.nonneg, lhs_mk_single, Literal.eval, h,
      -Finsupp.single_neg]

theorem PBConstr.lhs_sub_bound_sum (σ : ℕ → Bool) (ts : List (ℕ × Literal ℕ)) :
    (ts.map termIneq).sum.lhs σ - (ts.map termIneq).sum.bound = (PBConstr.lhs σ ts : ℤ) := by
  induction ts with
  | nil => simp only [List.map_nil, List.sum_nil, lhs_zero, bound_zero, sub_zero,
      Nat.cast_zero, PBConstr.lhs_nil]
  | cons t ts ih =>
    have h := Literal.lhs_sub_bound_toIneq σ t.2
    simp only [List.map_cons, List.sum_cons, lhs_add, bound_add, PBConstr.lhs_cons,
      Nat.cast_add, termIneq, lhs_nsmul, bound_nsmul, nsmul_eq_mul, termVal] at ih h ⊢
    push_cast
    linear_combination ih + (t.1 : ℤ) * h

/-- **The translation is faithful.** -/
theorem PBConstr.holds_toIneq_iff (σ : ℕ → Bool) (c : PBConstr) :
    c.toIneq.Holds σ ↔ c.Holds σ := by
  have h := lhs_sub_bound_sum σ c.terms
  rw [bound_sum_termIneq] at h
  have h0 : (⟨0, c.degree⟩ : Ineq ℕ).lhs σ = 0 := by
    rw [lhs_of_coeff_eq_smul σ (I := ⟨0, c.degree⟩) (J := 0) (c := 1) (by rw [one_smul]; rfl),
      lhs_zero, mul_zero]
  simp only [Ineq.Holds, PBConstr.Holds, toIneq, lhs_add, h0, add_zero, bound_add,
    bound_sum_termIneq]
  omega

/-- A clause's constraint is its cutting planes inequality. -/
theorem Clause.toIneq_toPB (c : Clause ℕ) : c.toPB.toIneq = c.toIneq := by
  rw [show Clause.toIneq c = Clause.toIneq c.dedup by
      simp only [Clause.toIneq, List.toFinset_dedup],
    Clause.toIneq_of_nodup (List.nodup_dedup c)]
  simp only [Clause.toPB, PBConstr.toIneq, List.map_map, Function.comp_def, termIneq, one_nsmul]
  exact add_comm _ _

/-- The inequalities of the constraints of the clauses of `φ` are its clause inequalities. -/
theorem CNF.toIneqs_eq_toPB (φ : CNF ℕ) :
    {I | ∃ c ∈ φ.map Clause.toPB, c.toIneq = I} = φ.toIneqs := by
  ext I
  simp only [Set.mem_ofPred_eq, List.mem_map, CNF.toIneqs]
  exact ⟨fun ⟨_, ⟨cl, hcl, rfl⟩, hI⟩ => ⟨cl, hcl, Clause.toIneq_toPB cl ▸ hI⟩,
    fun ⟨cl, hcl, hI⟩ => ⟨cl.toPB, ⟨cl, hcl, rfl⟩, (Clause.toIneq_toPB cl).symm ▸ hI⟩⟩

/-- **Refutation completeness of cutting planes for pseudo-Boolean constraints**: the
inequalities of a list of constraints have a cutting planes refutation iff the constraints have no
common 0/1 solution. This is
`Cslib.Logic.PL.CuttingPlanes.exists_refutableInSize_iff_not_exists_holds` read through the
faithful translation `Cslib.Logic.PL.PBConstr.holds_toIneq_iff`. -/
theorem PBConstr.exists_refutableInSize_toIneq_iff {F : List PBConstr} :
    (∃ s, CuttingPlanes.RefutableInSize {I | ∃ c ∈ F, c.toIneq = I} s) ↔
      ¬ ∃ σ : ℕ → Bool, ∀ c ∈ F, c.Holds σ := by
  simp only [CuttingPlanes.exists_refutableInSize_iff_not_exists_holds, Set.mem_ofPred_eq,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, holds_toIneq_iff]

/-- **Implicational completeness of cutting planes for pseudo-Boolean constraints**: the
inequality of a constraint `d` is derivable from the inequalities of a list of constraints iff
every common 0/1 solution of the list satisfies `d`. This is
`Cslib.Logic.PL.CuttingPlanes.exists_derivableInSize_iff_forall_holds` read through the faithful
translation `Cslib.Logic.PL.PBConstr.holds_toIneq_iff`. -/
theorem PBConstr.exists_derivableInSize_toIneq_iff {F : List PBConstr} {d : PBConstr} :
    (∃ s, CuttingPlanes.DerivableInSize {I | ∃ c ∈ F, c.toIneq = I} d.toIneq s) ↔
      ∀ σ : ℕ → Bool, (∀ c ∈ F, c.Holds σ) → d.Holds σ := by
  simp only [CuttingPlanes.exists_derivableInSize_iff_forall_holds, Set.mem_ofPred_eq,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, holds_toIneq_iff]

/-! ### Coefficients and bounds of term lists -/

namespace PBConstr

/-- The coefficients of a list of terms. -/
@[expose] def cf (ts : List (ℕ × Literal ℕ)) : ℕ →₀ ℤ :=
  (ts.map fun t => Finsupp.single (termVar t) (termCoeff t)).sum

@[simp] theorem cf_nil : cf [] = 0 := rfl

@[simp] theorem cf_cons (t : ℕ × Literal ℕ) (ts : List (ℕ × Literal ℕ)) :
    cf (t :: ts) = Finsupp.single (termVar t) (termCoeff t) + cf ts := by
  simp only [cf, List.map_cons, List.sum_cons]

@[simp] theorem cf_append (ts us : List (ℕ × Literal ℕ)) : cf (ts ++ us) = cf ts + cf us := by
  simp only [cf, List.map_append, List.sum_append]

@[simp] theorem negSum_nil : negSum [] = 0 := rfl

@[simp] theorem negSum_cons (t : ℕ × Literal ℕ) (ts : List (ℕ × Literal ℕ)) :
    negSum (t :: ts) = (if termPos t then 0 else t.1) + negSum ts := by
  simp only [negSum, List.map_cons, List.sum_cons]

@[simp] theorem negSum_append (ts us : List (ℕ × Literal ℕ)) :
    negSum (ts ++ us) = negSum ts + negSum us := by
  simp only [negSum, List.map_append, List.sum_append]

theorem termCoeff_negate (a : ℕ) (l : Literal ℕ) :
    termCoeff (a, Std.Sat.Literal.negate l) = -termCoeff (a, l) := by
  obtain ⟨v, b⟩ := l
  cases b <;> simp [termCoeff, termPos, Std.Sat.Literal.negate]

theorem cf_map_negate (ts : List (ℕ × Literal ℕ)) :
    cf (ts.map fun t => (t.1, Std.Sat.Literal.negate t.2)) = -cf ts := by
  induction ts with
  | nil => simp only [List.map_nil, cf_nil, neg_zero]
  | cons t ts ih =>
    obtain ⟨a, v, b⟩ := t
    simp only [List.map_cons, cf_cons, ih, termCoeff_negate, Finsupp.single_neg, neg_add, termVar]
    rfl

theorem negSum_add_negSum_negate (ts : List (ℕ × Literal ℕ)) :
    negSum ts + negSum (ts.map fun t => (t.1, Std.Sat.Literal.negate t.2)) = coeffSum ts := by
  induction ts with
  | nil => simp only [List.map_nil, negSum_nil, add_zero, coeffSum_nil]
  | cons t ts ih =>
    obtain ⟨a, v, false | true⟩ := t <;>
      simp only [List.map_cons, negSum_cons, coeffSum_cons, Std.Sat.Literal.negate, termPos,
        Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ih ⊢ <;>
      omega

theorem cf_filter_add (p : ℕ × Literal ℕ → Bool) (ts : List (ℕ × Literal ℕ)) :
    cf (ts.filter p) + cf (ts.filter fun t => !p t) = cf ts := by
  induction ts with
  | nil => simp only [List.filter_nil, cf_nil, add_zero]
  | cons t ts ih =>
    cases h : p t <;> simp only [List.filter_cons, h, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ↓reduceIte, cf_cons] <;> rw [← ih] <;> abel

theorem negSum_filter_add (p : ℕ × Literal ℕ → Bool) (ts : List (ℕ × Literal ℕ)) :
    negSum (ts.filter p) + negSum (ts.filter fun t => !p t) = negSum ts := by
  induction ts with
  | nil => simp only [List.filter_nil, negSum_nil, add_zero]
  | cons t ts ih =>
    cases h : p t <;> simp only [List.filter_cons, h, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ↓reduceIte, negSum_cons] <;> omega

theorem toIneq_eq (c : PBConstr) :
    c.toIneq = ⟨cf c.terms, (c.degree : ℤ) - negSum c.terms⟩ := by
  ext
  · rw [coeff_toIneq]; rfl
  · rw [bound_toIneq]

theorem cf_eq_lin (ts : List (ℕ × Literal ℕ)) :
    cf ts = ((toLinear ts).map fun e => Finsupp.single e.1 e.2).sum := by
  induction ts with
  | nil => simp only [cf_nil, toLinear, List.foldr_nil, List.map_nil, List.sum_nil]
  | cons t ts ih =>
    rw [cf_cons, ih,
      show toLinear (t :: ts) = insertCoeff (termVar t) (termCoeff t) (toLinear ts) from rfl]
    generalize toLinear ts = L
    induction L with
    | nil => simp only [insertCoeff, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
    | cons e L ihL =>
      obtain ⟨u, b⟩ := e
      by_cases h : u = termVar t
      · subst h
        simp only [insertCoeff, ↓reduceIte, List.map_cons, List.sum_cons, Finsupp.single_add]
        abel
      · simp only [insertCoeff, h, ↓reduceIte, List.map_cons, List.sum_cons]
        rw [← ihL]; abel

theorem entryTerm_cases (v : ℕ) (c : ℤ) :
    (0 < c ∧ entryTerm (v, c) = some (c.toNat, (v, true))) ∨
      (c < 0 ∧ entryTerm (v, c) = some ((-c).toNat, (v, false))) ∨
      (c = 0 ∧ entryTerm (v, c) = none) := by
  rcases lt_trichotomy c 0 with h | rfl | h
  · exact Or.inr (Or.inl ⟨h, by
      simp only [entryTerm, h, ↓reduceIte, not_lt.mpr h.le]⟩)
  · exact Or.inr (Or.inr ⟨rfl, by simp only [entryTerm, lt_irrefl, ↓reduceIte]⟩)
  · exact Or.inl ⟨h, by simp only [entryTerm, h, ↓reduceIte]⟩

theorem cf_fromLinear (L : List (ℕ × ℤ)) (D : ℤ) :
    cf (fromLinear L D).terms = (L.map fun e => Finsupp.single e.1 e.2).sum := by
  simp only [fromLinear]
  induction L with
  | nil => simp only [List.filterMap_nil, cf_nil, List.map_nil, List.sum_nil]
  | cons e L ih =>
    obtain ⟨v, c⟩ := e
    rw [List.filterMap_cons]
    rcases entryTerm_cases v c with ⟨h, he⟩ | ⟨h, he⟩ | ⟨rfl, he⟩
    · rw [he]; simp only [cf_cons, ih, termCoeff, termVar_mk, termPos_mk, List.map_cons,
        List.sum_cons, ↓reduceIte]
      congr 2; omega
    · rw [he]; simp only [cf_cons, ih, termCoeff, termVar_mk, termPos_mk, List.map_cons,
        List.sum_cons, Bool.false_eq_true, ↓reduceIte]
      congr 2; omega
    · rw [he]; simp only [ih, List.map_cons, List.sum_cons, Finsupp.single_zero, zero_add]

theorem negSum_fromLinear (L : List (ℕ × ℤ)) (D : ℤ) :
    negSum (fromLinear L D).terms = negMass L := by
  simp only [fromLinear]
  induction L with
  | nil => simp only [List.filterMap_nil, negSum_nil, negMass, List.map_nil, List.sum_nil]
  | cons e L ih =>
    obtain ⟨v, c⟩ := e
    simp only [negMass, List.map_cons, List.sum_cons] at ih ⊢
    rw [List.filterMap_cons]
    rcases entryTerm_cases v c with ⟨h, he⟩ | ⟨h, he⟩ | ⟨rfl, he⟩
    · rw [he]; simp only [negSum_cons, ih, termPos_mk, ↓reduceIte]; omega
    · rw [he]; simp only [negSum_cons, ih, termPos_mk, Bool.false_eq_true, ↓reduceIte]
    · rw [he]; simp only [ih, neg_zero, Int.toNat_zero, zero_add]

/-- Normalization keeps the coefficients. -/
theorem cf_normalize (c : PBConstr) : cf c.normalize.terms = cf c.terms := by
  rw [PBConstr.normalize, cf_fromLinear, cf_eq_lin]

/-- Normalization keeps the coefficients of the inequality. -/
theorem coeff_toIneq_normalize (c : PBConstr) : c.normalize.toIneq.coeff = c.toIneq.coeff := by
  rw [toIneq_eq, toIneq_eq]
  exact cf_normalize c

/-- Normalization can only raise the bound of the inequality: it clamps the degree at `0`. -/
theorem bound_toIneq_le_normalize (c : PBConstr) : c.toIneq.bound ≤ c.normalize.toIneq.bound := by
  rw [toIneq_eq, toIneq_eq]
  simp only [PBConstr.normalize]
  rw [negSum_fromLinear]
  simp only [fromLinear]
  omega

/-- The inequality of the sum of two constraints, before normalization, is the sum of their
inequalities. -/
theorem toIneq_append (c d : PBConstr) :
    (⟨c.terms ++ d.terms, c.degree + d.degree⟩ : PBConstr).toIneq = c.toIneq + d.toIneq := by
  rw [toIneq_eq, toIneq_eq, toIneq_eq]
  ext <;> simp only [coeff_add, cf_append, bound_add, Nat.cast_add, negSum_append]; ring

/-! ### Coefficients of terms on distinct variables -/

/-- A variable without terms has coefficient `0`. -/
theorem cf_apply_of_notMem {ts : List (ℕ × Literal ℕ)} {v : ℕ} (h : v ∉ ts.map termVar) :
    cf ts v = 0 := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp [cf_cons, Ne.symm h.1, ih h.2]

/-- On distinct variables, the coefficient of a term's variable is the term's signed
coefficient. -/
theorem cf_apply_of_nodup {ts : List (ℕ × Literal ℕ)} (h : (ts.map termVar).Nodup)
    {t : ℕ × Literal ℕ} (ht : t ∈ ts) : cf ts (termVar t) = termCoeff t := by
  induction ts with
  | nil => cases ht
  | cons t' ts ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 ht with rfl | ht
    · simp [cf_cons, cf_apply_of_notMem h.1]
    · have hne : termVar t' ≠ termVar t := fun he => h.1 (by rw [he]; exact List.mem_map_of_mem ht)
      simp [cf_cons, hne, ih h.2 ht]

/-! ### Multiplying the terms of a constraint -/

theorem cf_map_mul (k : ℕ) (ts : List (ℕ × Literal ℕ)) :
    cf (ts.map fun t => (k * t.1, t.2)) = (k : ℤ) • cf ts := by
  induction ts with
  | nil => simp only [List.map_nil, cf_nil, smul_zero]
  | cons t ts ih =>
    obtain ⟨a, v, b⟩ := t
    simp only [List.map_cons, cf_cons, ih, smul_add, Finsupp.smul_single]
    cases b <;> simp only [termVar, termCoeff, termPos, Bool.false_eq_true, ↓reduceIte,
      smul_eq_mul, Nat.cast_mul, mul_neg]

theorem negSum_map_mul (k : ℕ) (ts : List (ℕ × Literal ℕ)) :
    negSum (ts.map fun t => (k * t.1, t.2)) = k * negSum ts := by
  induction ts with
  | nil => simp only [List.map_nil, negSum_nil, mul_zero]
  | cons t ts ih =>
    obtain ⟨a, v, b⟩ := t
    simp only [List.map_cons, negSum_cons, ih]
    cases b <;> simp only [termPos, Bool.false_eq_true, ↓reduceIte] <;> ring

/-- The inequality of a constraint multiplied by `k`, before normalization, is `k` times its
inequality. -/
theorem toIneq_map_mul (k : ℕ) (c : PBConstr) :
    (⟨c.terms.map fun t => (k * t.1, t.2), k * c.degree⟩ : PBConstr).toIneq = k • c.toIneq := by
  rw [toIneq_eq, toIneq_eq]
  ext
  · simp only [cf_map_mul, coeff_nsmul]
    rfl
  · simp only [negSum_map_mul, bound_nsmul, nsmul_eq_mul, Nat.cast_mul]
    ring

end PBConstr

/-! ### Derivations with a line count -/

namespace VeriPB

open CuttingPlanes

/-- **At most `k` more lines** extend the cutting planes proof `ls` from `Γ` to a proof `ls'` with
the property `p`: `ls` is a suffix of `ls'`. The lines of `ls` stay lines of `ls'`, so a line is
derived once and referenced again at no cost, as the premises of
`Cslib.Logic.PL.CuttingPlanes.IsProof` are any earlier lines. -/
private def Reach (Γ : Set (Ineq ℕ)) (ls : List (Ineq ℕ)) (k : ℕ)
    (p : List (Ineq ℕ) → Prop) : Prop :=
  ∃ ls', IsProof Γ ls' ∧ ls <:+ ls' ∧ ls'.length ≤ ls.length + k ∧ p ls'

variable {Γ : Set (Ineq ℕ)} {ls : List (Ineq ℕ)} {I J : Ineq ℕ} {k k' : ℕ}
  {p q : List (Ineq ℕ) → Prop}

theorem ceilDiv_zero_right (a : ℕ) : ceilDiv a 0 = 0 := by
  simp only [ceilDiv, add_zero, Nat.div_zero]

theorem mul_ceilDiv_lt (a : ℕ) {k : ℕ} (hk : 0 < k) : k * ceilDiv a k < a + k := by
  unfold ceilDiv
  have := Nat.div_mul_le_self (a + k - 1) k
  rw [Nat.mul_comm]; omega

theorem cf_add_cf_round (k : ℕ) (hk : 0 < k) (ts : List (ℕ × Literal ℕ)) :
    cf ts + cf (ts.map fun t => (k * ceilDiv t.1 k - t.1, t.2)) =
      (k : ℤ) • cf (ts.map fun t => (ceilDiv t.1 k, t.2)) := by
  induction ts with
  | nil => simp only [cf_nil, add_zero, List.map_nil, smul_zero]
  | cons t ts ih =>
    obtain ⟨a, v, b⟩ := t
    have hle := le_mul_ceilDiv a hk
    simp only [List.map_cons, cf_cons, smul_add, Finsupp.smul_single, termVar_mk, ← ih]
    have : Finsupp.single v (termCoeff (a, v, b)) +
        Finsupp.single v (termCoeff (k * ceilDiv a k - a, v, b)) =
        Finsupp.single v ((k : ℤ) • termCoeff (ceilDiv a k, v, b)) := by
      rw [← Finsupp.single_add]
      congr 1
      cases b <;> simp only [termCoeff, termPos_mk, Bool.false_eq_true, ↓reduceIte, smul_eq_mul] <;>
        (push_cast [hle]; ring)
    rw [← this]; abel

theorem negSum_add_negSum_round (k : ℕ) (hk : 0 < k) (ts : List (ℕ × Literal ℕ)) :
    negSum ts + negSum (ts.map fun t => (k * ceilDiv t.1 k - t.1, t.2)) =
      k * negSum (ts.map fun t => (ceilDiv t.1 k, t.2)) := by
  induction ts with
  | nil => simp only [negSum_nil, add_zero, List.map_nil, mul_zero]
  | cons t ts ih =>
    obtain ⟨a, v, b⟩ := t
    have hle := le_mul_ceilDiv a hk
    simp only [List.map_cons, negSum_cons]
    cases b
    · simp only [termPos_mk, Bool.false_eq_true, ↓reduceIte, Nat.mul_add, ← ih]; omega
    · simpa only [termPos_mk, ↓reduceIte, zero_add, Nat.mul_add, mul_zero] using ih

theorem filter_not_bne (v : ℕ) (ts : List (ℕ × Literal ℕ)) :
    (ts.filter fun t => !(termVar t != v)) = ts.filter (termVar · == v) := by
  congr 1; funext t; simp only [bne, Bool.not_not]

namespace Reach

private theorem refl (h : IsProof Γ ls) (hp : p ls) : Reach Γ ls k p :=
  ⟨ls, h, List.suffix_refl ls, Nat.le_add_right _ _, hp⟩

private theorem le (h : Reach Γ ls k p) (hk : k ≤ k') : Reach Γ ls k' p :=
  let ⟨ls', h', hs, hl, hp⟩ := h
  ⟨ls', h', hs, hl.trans (Nat.add_le_add_left hk _), hp⟩

private theorem bind (h : Reach Γ ls k p)
    (f : ∀ ls', IsProof Γ ls' → ls <:+ ls' → p ls' → Reach Γ ls' k' q) :
    Reach Γ ls (k + k') q := by
  obtain ⟨ls₁, h₁, hs₁, hl₁, hp₁⟩ := h
  obtain ⟨ls₂, h₂, hs₂, hl₂, hq₂⟩ := f ls₁ h₁ hs₁ hp₁
  exact ⟨ls₂, h₂, hs₁.trans hs₂, by omega, hq₂⟩

/-- New lines on top of `ls`. -/
private theorem append (new : List (Ineq ℕ)) (h : IsProof Γ (new ++ ls)) (hk : new.length ≤ k)
    (hp : p (new ++ ls)) : Reach Γ ls k p :=
  ⟨_, h, List.suffix_append new ls, by rw [List.length_append]; omega, hp⟩

private theorem of_eq (h : Reach Γ ls k (I ∈ ·)) (hIJ : I = J) : Reach Γ ls k (J ∈ ·) := hIJ ▸ h

/-! #### The rules of cutting planes -/

private theorem hyp (h : IsProof Γ ls) (hI : I ∈ Γ) : Reach Γ ls 1 (I ∈ ·) :=
  append [I] (h.hyp hI) le_rfl List.mem_cons_self

private theorem add (h : IsProof Γ ls) (hI : I ∈ ls) (hJ : J ∈ ls) : Reach Γ ls 1 (I + J ∈ ·) :=
  append [_] (h.add hI hJ) le_rfl List.mem_cons_self

private theorem smul (h : IsProof Γ ls) {c : ℕ} (hc : 0 < c) (hI : I ∈ ls) :
    Reach Γ ls 1 (c • I ∈ ·) :=
  append [_] (h.smul c hc hI) le_rfl List.mem_cons_self

private theorem div (h : IsProof Γ ls) {c : ℕ} (hc : 0 < c) (hdvd : ∀ v, (c : ℤ) ∣ I.coeff v)
    (hI : I ∈ ls) : Reach Γ ls 1 (I.div c ∈ ·) :=
  append [_] (h.div c hc hdvd hI) le_rfl List.mem_cons_self

/-- `0 ≥ -1`, in three lines. -/
private theorem negContra (h : IsProof Γ ls) : Reach Γ ls 3 (-Ineq.contra ∈ ·) := by
  have h' := ((h.nonneg 0).leOne 0).add (I := Ineq.nonneg 0) (J := Ineq.leOne 0)
    (by simp) (by simp)
  rw [Ineq.nonneg_add_leOne] at h'
  exact append [_, _, _] h' le_rfl List.mem_cons_self

private theorem div_neg_contra_two : (-Ineq.contra : Ineq ℕ).div 2 = 0 :=
  Ineq.div_eq_of Nat.zero_lt_two
    (by simp only [coeff_neg, coeff_contra, coeff_zero, smul_zero, neg_zero])
    (by simp only [bound_neg, bound_contra, bound_zero]; decide) (by decide)

/-- `0 ≥ 0`, in four lines. -/
private theorem zero (h : IsProof Γ ls) : Reach Γ ls 4 ((0 : Ineq ℕ) ∈ ·) := by
  have h₁ := ((h.nonneg 0).leOne 0).add (I := Ineq.nonneg 0) (J := Ineq.leOne 0)
    (by simp) (by simp)
  rw [Ineq.nonneg_add_leOne] at h₁
  have h₂ := h₁.div 2 Nat.zero_lt_two (fun _ => by simp) List.mem_cons_self
  rw [div_neg_contra_two] at h₂
  exact append [_, _, _, _] h₂ le_rfl List.mem_cons_self

/-- **Lowering the bound**, in five lines. -/
private theorem lower (h : IsProof Γ ls) (hI : I ∈ ls) (hc : J.coeff = I.coeff)
    (hb : J.bound ≤ I.bound) :
    Reach Γ ls 5 (J ∈ ·) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, I.bound = J.bound + k := ⟨(I.bound - J.bound).toNat, by omega⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · obtain rfl : I = J := Ineq.ext hc.symm (by simpa only [Nat.cast_zero, add_zero] using hk)
    exact refl h hI
  · refine ((negContra h).bind fun ls₁ h₁ hs₁ hn => (smul h₁ hk0 hn).bind
      fun ls₂ h₂ hs₂ hm => (add h₂ ((hs₁.trans hs₂).subset hI) hm).of_eq (Ineq.ext ?_ ?_)).le
      le_rfl
    · simp only [smul_neg, coeff_add, coeff_neg, coeff_nsmul, coeff_contra, nsmul_zero, neg_zero,
        add_zero, hc]
    · simp only [smul_neg, bound_add, hk, bound_neg, bound_nsmul, bound_contra, Int.nsmul_eq_mul,
        mul_one, add_neg_cancel_right]

/-! #### Constraints -/

/-- The inequality of a term, in at most four lines. -/
private theorem term (h : IsProof Γ ls) (t : ℕ × Literal ℕ) : Reach Γ ls 4 (termIneq t ∈ ·) := by
  obtain ⟨a, v, b⟩ := t
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact (zero h).of_eq (by simp only [PBConstr.termIneq, zero_smul])
  · have h' : IsProof Γ (a • Literal.toIneq (v, b) :: Literal.toIneq (v, b) :: ls) := by
      cases b
      exacts [(h.leOne v).smul a ha List.mem_cons_self, (h.nonneg v).smul a ha List.mem_cons_self]
    exact append [_, _] h' (by simp) List.mem_cons_self

/-- **A constraint of degree `0` is a sum of literal axioms**: at most five lines per term. -/
private theorem degreeZero (h : IsProof Γ ls) :
    ∀ ts : List (ℕ × Literal ℕ), Reach Γ ls (5 * ts.length + 4) ((⟨ts, 0⟩ : PBConstr).toIneq ∈ ·)
  | [] => (zero h).of_eq (by ext <;>
      simp only [PBConstr.toIneq, List.map_nil, List.sum_nil, zero_add, coeff_zero, bound_zero,
        Nat.cast_zero])
  | t :: ts => by
    refine (((degreeZero h ts).bind fun ls₁ h₁ _ hd => (term h₁ t).bind fun ls₂ h₂ hs₂ ht =>
      (add h₂ ht (hs₂.subset hd)).of_eq ?_).le (by simp only [List.length_cons]; omega))
    simp only [PBConstr.toIneq, List.map_cons, List.sum_cons, add_assoc]

/-- **Normalization**, in at most five lines per term of the normal form, plus five. -/
private theorem normalize (h : IsProof Γ ls) {c : PBConstr} (hc : c.toIneq ∈ ls) :
    Reach Γ ls (5 * c.normalize.terms.length + 5) (c.normalize.toIneq ∈ ·) := by
  by_cases hd : c.normalize.degree = 0
  · have e : (⟨c.normalize.terms, 0⟩ : PBConstr) = c.normalize := by rw [← hd]
    exact ((degreeZero h c.normalize.terms).of_eq (congrArg PBConstr.toIneq e)).le (by omega)
  · refine (lower h hc (coeff_toIneq_normalize c) (le_of_eq ?_)).le (by omega)
    rw [toIneq_eq, toIneq_eq]
    simp only [PBConstr.normalize, negSum_fromLinear] at hd ⊢
    simp only [fromLinear] at hd ⊢
    omega

/-- Addition, then normalization. -/
private theorem pbAdd (h : IsProof Γ ls) {c d : PBConstr} (hc : c.toIneq ∈ ls)
    (hd : d.toIneq ∈ ls) :
    Reach Γ ls (5 * (c.add d).terms.length + 6) ((c.add d).toIneq ∈ ·) :=
  ((add h hc hd).bind fun _ h₁ _ hs =>
    (normalize h₁ (c := ⟨c.terms ++ d.terms, c.degree + d.degree⟩) (by rwa [toIneq_append]) :
      Reach Γ _ (5 * (c.add d).terms.length + 5) ((c.add d).toIneq ∈ ·))).le (by
    have : (c.add d).terms.length =
      (PBConstr.normalize ⟨c.terms ++ d.terms, c.degree + d.degree⟩).terms.length := rfl
    omega)

/-- Multiplication by a positive `k`, then normalization. -/
private theorem pbMul (h : IsProof Γ ls) {c : PBConstr} (hc : c.toIneq ∈ ls) {k : ℕ} (hk : 0 < k) :
    Reach Γ ls (5 * (c.mul k).terms.length + 6) ((c.mul k).toIneq ∈ ·) :=
  ((smul h hk hc).bind fun _ h₁ _ hs =>
    (normalize h₁ (c := ⟨c.terms.map fun t => (k * t.1, t.2), k * c.degree⟩)
      (by rwa [toIneq_map_mul]) :
      Reach Γ _ (5 * (c.mul k).terms.length + 5) ((c.mul k).toIneq ∈ ·))).le (by
    have : (c.mul k).terms.length = (PBConstr.normalize
      ⟨c.terms.map fun t => (k * t.1, t.2), k * c.degree⟩).terms.length := rfl
    omega)

/-- Rounding-up division by a positive `k`: normalize, add the literal axioms
`(k ⌈aᵢ / k⌉ - aᵢ) • ℓᵢ ≥ 0`, divide, and normalize. -/
private theorem pbDiv (h : IsProof Γ ls) {c : PBConstr} (hc : c.toIneq ∈ ls) {k : ℕ} (hk : 0 < k) :
    Reach Γ ls (10 * c.normalize.terms.length + 5 * (c.div k).terms.length + 16)
      ((c.div k).toIneq ∈ ·) := by
  simp only [PBConstr.div]
  refine ((normalize h hc).bind (k' := 5 * c.normalize.terms.length + 4 + (1 + (1 +
    (5 * (PBConstr.normalize ⟨c.normalize.terms.map fun t => (ceilDiv t.1 k, t.2),
      ceilDiv c.normalize.degree k⟩).terms.length + 5)))) fun ls₁ h₁ _ hn => ?_).le (by omega)
  generalize c.normalize = c' at hn ⊢
  obtain ⟨ts, d⟩ := c'
  dsimp only
  set E := ts.map fun t => (k * ceilDiv t.1 k - t.1, t.2)
  set u := ts.map fun t => (ceilDiv t.1 k, t.2)
  have hcf := cf_add_cf_round k hk ts
  have hns := negSum_add_negSum_round k hk ts
  have hcoeff : ((⟨ts, d⟩ : PBConstr).toIneq + (⟨E, 0⟩ : PBConstr).toIneq).coeff =
      (k : ℤ) • (⟨u, ceilDiv d k⟩ : PBConstr).toIneq.coeff := by
    simp only [toIneq_eq, coeff_add, hcf, E, u]
  have hbound : ((⟨ts, d⟩ : PBConstr).toIneq + (⟨E, 0⟩ : PBConstr).toIneq).bound =
      (d : ℤ) - k * negSum u := by
    simp only [toIneq_eq, bound_add]
    have : ((negSum ts : ℕ) : ℤ) + negSum E = k * negSum u := mod_cast hns
    push_cast; linarith
  have hdiv : ((⟨ts, d⟩ : PBConstr).toIneq + (⟨E, 0⟩ : PBConstr).toIneq).div k =
      (⟨u, ceilDiv d k⟩ : PBConstr).toIneq := by
    have h1 : (d : ℤ) ≤ k * ceilDiv d k := by exact_mod_cast le_mul_ceilDiv d hk
    have h2 : (k : ℤ) * ceilDiv d k < d + k := by exact_mod_cast mul_ceilDiv_lt d hk
    refine Ineq.div_eq_of hk hcoeff ?_ ?_ <;>
      (rw [hbound, toIneq_eq]; dsimp only; simp only [mul_sub, mul_one]; linarith)
  have hlen : E.length = ts.length := List.length_map _
  refine ((degreeZero h₁ E).bind fun ls₂ h₂ hs₂ hE => (add h₂ (hs₂.subset hn) hE).bind
    fun ls₃ h₃ _ hsum => (div h₃ hk (fun v => ?_) hsum).bind fun ls₄ h₄ _ hq =>
      normalize h₄ (hdiv ▸ hq)).le (by rw [hlen])
  rw [hcoeff]
  exact dvd_mul_right _ _

/-- Weakening on `v`: normalize, add `aᵢ • ¬ℓᵢ ≥ 0` for the terms on `v`, and normalize. -/
private theorem pbWeaken (h : IsProof Γ ls) {c : PBConstr} (hc : c.toIneq ∈ ls) (v : ℕ) :
    Reach Γ ls (10 * c.normalize.terms.length + 5 * (c.weaken v).terms.length + 15)
      ((c.weaken v).toIneq ∈ ·) := by
  simp only [PBConstr.weaken]
  refine ((normalize h hc).bind (k' := 5 * c.normalize.terms.length + 5 + (5 * (PBConstr.normalize
    ⟨c.normalize.terms.filter (termVar · != v), c.normalize.degree -
      coeffSum (c.normalize.terms.filter (termVar · == v))⟩).terms.length + 5))
    fun ls₁ h₁ _ hn => ?_).le (by omega)
  generalize c.normalize = c' at hn ⊢
  obtain ⟨ts, d⟩ := c'
  dsimp only
  refine (Reach.bind (k := 5 * ts.length + 5) ?_ fun ls₂ h₂ _ hX => normalize h₂ hX)
  set rem := ts.filter (termVar · == v)
  set rest := ts.filter (termVar · != v)
  have hrem : rem.length ≤ ts.length := List.length_filter_le _ _
  have hrest : rest.length ≤ ts.length := List.length_filter_le _ _
  have hcf := cf_filter_add (fun t => termVar t != v) ts
  have hns := negSum_filter_add (fun t => termVar t != v) ts
  rw [filter_not_bne] at hcf hns
  have hneg := negSum_add_negSum_negate rem
  by_cases hd : coeffSum rem ≤ d
  · refine ((degreeZero h₁ (rem.map fun t => (t.1, Std.Sat.Literal.negate t.2))).bind
      fun ls₂ h₂ hs₂ hE => (add h₂ (hs₂.subset hn) hE).of_eq ?_).le
      (by simp only [List.length_map]; omega)
    rw [toIneq_eq, toIneq_eq, toIneq_eq]
    refine Ineq.ext ?_ ?_
    · simp only [coeff_add, cf_map_negate, ← hcf, rem, rest]; abel
    · simp only [bound_add, rem, rest] at hneg hd ⊢
      omega
  · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hd)]
    exact (degreeZero h₁ _).le (by omega)

/-- **A contradiction gives `0 ≥ 1`**, in at most five lines per term, plus ten. -/
private theorem contra (h : IsProof Γ ls) {c : PBConstr} (hc : c.toIneq ∈ ls)
    (hcon : c.IsContradiction) :
    Reach Γ ls (5 * c.terms.length + 10) (Ineq.contra ∈ ·) := by
  have hneg := negSum_add_negSum_negate c.terms
  unfold IsContradiction at hcon
  refine ((degreeZero h (c.terms.map fun t => (t.1, Std.Sat.Literal.negate t.2))).bind
    fun ls₁ h₁ hs₁ hE => (add h₁ (hs₁.subset hc) hE).bind fun ls₂ h₂ _ hs =>
      lower h₂ hs ?_ ?_).le (by simp only [List.length_map]; omega)
  · rw [toIneq_eq, toIneq_eq]
    simp only [coeff_add, cf_map_negate, add_neg_cancel, coeff_contra]
  · rw [toIneq_eq, toIneq_eq]
    simp only [bound_add, bound_contra]
    omega

/-- A literal axiom, in nine lines. -/
private theorem litAxiom (h : IsProof Γ ls) (l : Literal ℕ) :
    Reach Γ ls 9 ((litAxiom l).toIneq ∈ ·) :=
  degreeZero h [(1, l)]

end Reach

/-! #### Widths -/

/-- The terms of `c` are on variables of `S`, and there are at most `|S|` of them. -/
private def Fits (S : Finset ℕ) (c : PBConstr) : Prop :=
  (∀ t ∈ c.terms, termVar t ∈ S) ∧ c.terms.length ≤ S.card

/-- **A normal form on the variables of `S` has at most `|S|` terms**: its variables are those of
the constraint with a nonzero coefficient, each once. -/
private theorem fits_normalize {S : Finset ℕ} {c : PBConstr} (h : ∀ t ∈ c.terms, termVar t ∈ S) :
    Fits S c.normalize := by
  have hnd := nodup_termVar_normalize c
  have hvar : ∀ t ∈ c.normalize.terms, termVar t ∈ S := by
    intro t ht
    have hne : cf c.terms (termVar t) ≠ 0 := by
      rw [← cf_normalize, cf_apply_of_nodup hnd ht]
      have := pos_of_mem_normalize ht
      unfold termCoeff
      split <;> omega
    by_contra hS
    exact hne (cf_apply_of_notMem fun hm => by
      obtain ⟨t', ht', he⟩ := List.mem_map.1 hm
      exact hS (he ▸ h t' ht'))
  refine ⟨hvar, ?_⟩
  rw [← List.length_map (f := termVar), ← List.toFinset_card_of_nodup hnd]
  exact Finset.card_le_card fun v hv => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hv)
    exact hvar t ht

/-! ### Proofs made of cutting-planes steps -/

/-- A `pol` operation other than saturation. -/
@[expose] def PolOp.IsCP : PolOp → Bool
  | .sat => false
  | _ => true

/-- A `pol` step without saturation, or a deletion. -/
@[expose] def Step.IsCP : Step → Bool
  | .pol ops => ops.all PolOp.IsCP
  | .del _ => true
  | _ => false

/-- **The operations of a `pol` step derive their constraints** in at most `16 (|S| + 1)` lines
each, when the literal axioms are on variables of `S` and the constraints of the database and of
the stack fit `S`. -/
private theorem polEval_reach {S : Finset ℕ} {db : List (ℕ × PBConstr)} :
    ∀ (ops : List PolOp) (st st' : List PBConstr) (ls : List (Ineq ℕ)), IsProof Γ ls →
      ops.all PolOp.IsCP → (∀ l, PolOp.lit l ∈ ops → l.1 ∈ S) →
      (∀ e ∈ db, e.2.toIneq ∈ ls ∧ Fits S e.2) → (∀ c ∈ st, c.toIneq ∈ ls ∧ Fits S c) →
      polEval db ops st = some st' →
      Reach Γ ls (16 * (S.card + 1) * ops.length) fun ls' => ∀ c ∈ st', c.toIneq ∈ ls' ∧ Fits S c
  | [], st, st', ls, hls, _, _, _, hst, h => by
    simp only [polEval, Option.some.injEq] at h
    exact Reach.refl hls (h ▸ hst)
  | op :: ops, st, st', ls, hls, hops, hlit, hdb, hst, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hops
    have step {c : PBConstr} {st₁ : List PBConstr} {K : ℕ} (hK : K ≤ 16 * (S.card + 1))
        (hc : Reach Γ ls K (c.toIneq ∈ ·)) (hfc : Fits S c)
        (hst₁ : ∀ d ∈ st₁, d.toIneq ∈ ls ∧ Fits S d) (h' : polEval db ops (c :: st₁) = some st') :
        Reach Γ ls (16 * (S.card + 1) * (op :: ops).length)
          fun ls' => ∀ c ∈ st', c.toIneq ∈ ls' ∧ Fits S c := by
      refine (hc.bind fun ls₁ h₁ hs₁ hc₁ => polEval_reach ops (c :: st₁) st' ls₁ h₁ hops.2
        (fun l hl => hlit l (List.mem_cons_of_mem _ hl))
        (fun e he => ⟨hs₁.subset (hdb e he).1, (hdb e he).2⟩)
        (List.forall_mem_cons.2 ⟨⟨hc₁, hfc⟩,
          fun d hd => ⟨hs₁.subset (hst₁ d hd).1, (hst₁ d hd).2⟩⟩) h').le ?_
      generalize 16 * (S.card + 1) = B at hK ⊢
      rw [List.length_cons, Nat.mul_succ]
      omega
    have hfits {c : PBConstr} (hc : Fits S c) : Fits S c.normalize := fits_normalize hc.1
    cases op with
    | id n =>
      simp only [polEval, Option.bind_eq_some_iff] at h
      obtain ⟨c, hc, h⟩ := h
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hc
      have he' := hdb e (List.mem_of_find?_eq_some he)
      exact step (Nat.zero_le _) (Reach.refl hls he'.1) he'.2 hst h
    | lit l =>
      have hl := hlit l List.mem_cons_self
      refine step (by omega) (Reach.litAxiom hls l) ⟨?_, ?_⟩ hst h
      · simp only [PBConstr.litAxiom, List.mem_singleton, forall_eq]
        exact hl
      · simp only [PBConstr.litAxiom, List.length_singleton]
        exact Finset.card_pos.2 ⟨_, hl⟩
    | sat => simp [PolOp.IsCP] at hops
    | add =>
      match st, h with
      | c₂ :: c₁ :: st, h =>
        simp only [List.forall_mem_cons] at hst
        have hf : Fits S (c₁.add c₂) := fits_normalize fun t ht => by
          rcases List.mem_append.1 ht with ht | ht
          exacts [hst.2.1.2.1 t ht, hst.1.2.1 t ht]
        exact step (by have := hf.2; omega) (Reach.pbAdd hls hst.2.1.1 hst.1.1) hf hst.2.2 h
    | mul k =>
      match k, st, h with
      | k + 1, c :: st, h =>
        simp only [List.forall_mem_cons] at hst
        have hf : Fits S (c.mul (k + 1)) := fits_normalize fun t ht => by
          obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
          exact hst.1.2.1 t' ht'
        exact step (by have := hf.2; omega) (Reach.pbMul hls hst.1.1 (by omega : 0 < k + 1)) hf
          hst.2 h
    | div k =>
      match k, st, h with
      | k + 1, c :: st, h =>
        simp only [List.forall_mem_cons] at hst
        have hn := hfits hst.1.2
        have hf : Fits S (c.div (k + 1)) := fits_normalize fun t ht => by
          obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
          exact hn.1 t' ht'
        exact step (by have := hf.2; have := hn.2; omega)
          (Reach.pbDiv hls hst.1.1 (by omega : 0 < k + 1)) hf hst.2 h
    | weaken v =>
      match st, h with
      | c :: st, h =>
        simp only [List.forall_mem_cons] at hst
        have hn := hfits hst.1.2
        have hf : Fits S (c.weaken v) :=
          fits_normalize fun t ht => hn.1 t (List.mem_of_mem_filter ht)
        exact step (by have := hf.2; have := hn.2; omega) (Reach.pbWeaken hls hst.1.1 v) hf hst.2 h

/-- **The steps derive the database**, in at most `16 (|S| + 1)` lines per operation. -/
private theorem runSteps_reach {S : Finset ℕ} :
    ∀ (db : List (ℕ × PBConstr)) (n : ℕ) (ss : List Step) (db' : List (ℕ × PBConstr)) (n' : ℕ)
    (ls : List (Ineq ℕ)), IsProof Γ ls →
    ss.all Step.IsCP → (∀ ops, Step.pol ops ∈ ss → ∀ l, PolOp.lit l ∈ ops → l.1 ∈ S) →
    (∀ e ∈ db, e.2.toIneq ∈ ls ∧ Fits S e.2) → runSteps db n ss = some (db', n') →
    Reach Γ ls (16 * (S.card + 1) * opCount ss) fun ls' => ∀ e ∈ db', e.2.toIneq ∈ ls' ∧ Fits S e.2
  | db, n, [], db', n', ls, hls, _, _, hdb, h => by
    simp only [runSteps, Option.some.injEq, Prod.mk.injEq] at h
    exact Reach.refl hls (h.1 ▸ hdb)
  | db, n, s :: ss, db', n', ls, hls, hss, hlit, hdb, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hss
    have hlit' : ∀ ops, Step.pol ops ∈ ss → ∀ l, PolOp.lit l ∈ ops → l.1 ∈ S :=
      fun ops hops => hlit ops (List.mem_cons_of_mem _ hops)
    simp only [runSteps] at h
    split at h
    · rename_i db₁ n₁ h₁
      rw [opCount_cons, Nat.mul_add]
      cases s with
      | pol ops =>
        simp only [runStep] at h₁
        split at h₁
        · rename_i c hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h₁
          obtain ⟨rfl, rfl⟩ := h₁
          refine (polEval_reach ops [] [c] ls hls (by simpa only [Step.IsCP] using hss.1)
            (hlit ops List.mem_cons_self) hdb (fun _ hm => absurd hm List.not_mem_nil) hc).bind
            fun ls₁ h₁ hs₁ hc₁ => runSteps_reach _ _ ss db' n' ls₁ h₁ hss.2 hlit' ?_ h
          refine List.forall_mem_cons.2 ⟨hc₁ c List.mem_cons_self, fun e he => ?_⟩
          exact ⟨hs₁.subset (hdb e he).1, (hdb e he).2⟩
        · cases h₁
      | del ids =>
        simp only [runStep] at h₁
        split at h₁
        · simp only [Option.some.injEq, Prod.mk.injEq] at h₁
          obtain ⟨rfl, rfl⟩ := h₁
          exact (runSteps_reach _ _ ss db' n' ls hls hss.2 hlit'
            (fun e he => hdb e (List.mem_of_mem_filter he)) h).le (by simp [Step.opCount])
        · cases h₁
      | rup | rupSearch | pbc => simp only [Step.IsCP, Bool.false_eq_true, false_and] at hss
    · cases h

/-- The hypotheses `F`, normalized, in at most `5 |S| + 6` lines each. -/
private theorem reach_normalize_hyps {S : Finset ℕ} :
    ∀ (F : List PBConstr), (∀ c ∈ F, c.toIneq ∈ Γ) → (∀ c ∈ F, ∀ t ∈ c.terms, termVar t ∈ S) →
    ∀ {ls : List (Ineq ℕ)}, IsProof Γ ls →
      Reach Γ ls ((5 * S.card + 6) * F.length)
        fun ls' => ∀ c ∈ F, c.normalize.toIneq ∈ ls' ∧ Fits S c.normalize
  | [], _, _, _, hls => Reach.refl hls fun _ hc => absurd hc List.not_mem_nil
  | c :: F, hΓ, hS, ls, hls => by
    have hf := fits_normalize (hS c List.mem_cons_self)
    refine (((Reach.hyp hls (hΓ c List.mem_cons_self)).bind fun ls₁ h₁ _ hc₁ =>
      ((Reach.normalize h₁ hc₁).le (k' := 5 * S.card + 5) (by have := hf.2; omega)).bind
        fun ls₂ h₂ _ hc₂ =>
          (reach_normalize_hyps F (fun d hd => hΓ d (List.mem_cons_of_mem _ hd))
            (fun d hd => hS d (List.mem_cons_of_mem _ hd)) h₂).bind (k' := 0)
            fun ls₃ h₃ hs₃ hF₃ =>
              Reach.refl h₃ (List.forall_mem_cons.2 ⟨⟨hs₃.subset hc₂, hf⟩, hF₃⟩))).le ?_
    rw [List.length_cons, Nat.mul_succ]
    omega

/-- **Cutting-planes proofs with a line count**: a checked VeriPB proof of `UNSAT` on `F` made of
`pol` steps without saturation and of deletions, whose literal axioms are on variables of `S`
when the constraints of `F` are, gives a cutting planes refutation of the inequalities of `F` with
at most `16 (|S| + 1) (|F| + m + 1)` lines, where `m` is the number of `pol` operations. A line
derived once is referenced again for free; the factor `|S| + 1` pays for the operations whose
translation adds a literal axiom per term: rounding-up division, weakening, a normalization that
clamps the degree at `0`, and the final contradiction. -/
theorem refutableInSize_of_check {F : List PBConstr} {P : Proof} {S : Finset ℕ}
    (h : check F P = true) (hP : P.steps.all Step.IsCP)
    (hF : ∀ c ∈ F, ∀ t ∈ c.terms, termVar t ∈ S)
    (hS : ∀ ops, Step.pol ops ∈ P.steps → ∀ l, PolOp.lit l ∈ ops → l.1 ∈ S) :
    RefutableInSize {I | ∃ c ∈ F, c.toIneq = I}
      (16 * (S.card + 1) * (F.length + opCount P.steps + 1)) := by
  unfold check at h
  split at h
  · rename_i db n hrun
    obtain ⟨c, hc, hcon⟩ := (Option.any_eq_true _ _).mp h
    unfold lookup at hc
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hc
    have he' := List.mem_of_find?_eq_some he
    obtain ⟨ls, hls, -, hlen, hcontra⟩ :=
      (reach_normalize_hyps (Γ := {I | ∃ c ∈ F, c.toIneq = I}) F (fun c hc => ⟨c, hc, rfl⟩) hF
        IsProof.nil).bind fun ls₁ h₁ _ hF₁ =>
        (runSteps_reach _ _ _ db n ls₁ h₁ hP hS (fun e he => by
          obtain ⟨⟨c, i⟩, hci, rfl⟩ := List.mem_map.mp he
          exact hF₁ c (List.fst_mem_of_mem_zipIdx hci)) hrun).bind (k' := 5 * S.card + 10)
          fun ls₂ h₂ _ hdb => (Reach.contra h₂ (hdb e he').1 (of_decide_eq_true hcon)).le
            (by have := (hdb e he').2.2; omega)
    refine ⟨ls, hls, hcontra, hlen.trans ?_⟩
    generalize hB : 16 * (S.card + 1) = B at *
    have h1 : (5 * S.card + 6) * F.length ≤ B * F.length := Nat.mul_le_mul_right _ (by omega)
    rw [List.length_nil, Nat.zero_add, Nat.mul_add, Nat.mul_add, Nat.mul_one]
    omega
  · cases h

/-- The variables of the literal axioms of a step. -/
private def Step.litVars : Step → List ℕ
  | .pol ops => ops.filterMap fun
    | .lit l => some l.1
    | _ => none
  | _ => []

/-- **Cutting-planes proofs**: a checked VeriPB proof of `UNSAT` made of `pol` steps without
saturation and of deletions gives a cutting planes refutation of the inequalities of the
formula, with the line count of `Cslib.Logic.PL.VeriPB.refutableInSize_of_check` for the variables
of the formula and of the literal axioms of the proof. -/
theorem exists_isProof_contra_of_check {F : List PBConstr} {P : Proof} (h : check F P = true)
    (hP : P.steps.all Step.IsCP) :
    ∃ s, RefutableInSize {I | ∃ c ∈ F, c.toIneq = I} s :=
  ⟨_, refutableInSize_of_check (S := (F.flatMap fun c => c.terms.map termVar).toFinset ∪
      (P.steps.flatMap Step.litVars).toFinset) h hP
    (fun c hc _ ht => Finset.mem_union_left _ (List.mem_toFinset.2
      (List.mem_flatMap.2 ⟨c, hc, List.mem_map_of_mem ht⟩)))
    (fun _ hops _ hl => Finset.mem_union_right _ (List.mem_toFinset.2
      (List.mem_flatMap.2 ⟨_, hops, List.mem_filterMap.2 ⟨_, hl, rfl⟩⟩)))⟩

/-- **Cutting-planes proofs of CNFs**: for the clauses of a CNF, the refutation is one of
`φ.toIneqs`. -/
theorem exists_isProof_contra_of_check_cnf {φ : CNF ℕ} {P : Proof}
    (h : check (φ.map Clause.toPB) P = true) (hP : P.steps.all Step.IsCP) :
    ∃ s, RefutableInSize φ.toIneqs s :=
  CNF.toIneqs_eq_toPB φ ▸ exists_isProof_contra_of_check h hP

/-! ### No bound in steps and operations alone -/

/-- The constraint `x₀ + ⋯ + x_{w-1} ≥ w + 1`, a contradiction on `w` variables. -/
@[expose] def wideContra (w : ℕ) : PBConstr := ⟨(List.range w).map fun j => (1, (j, true)), w + 1⟩

private theorem nodup_termVar_wideContra (w : ℕ) : ((wideContra w).terms.map termVar).Nodup := by
  simpa [wideContra, List.map_map, Function.comp_def] using List.nodup_range

/-- **The kernel checker refutes `x₀ + ⋯ + x_{w-1} ≥ w + 1` with no steps**: the conclusion names
the constraint itself, a contradiction. -/
theorem check_wideContra (w : ℕ) : check [wideContra w] ⟨[], 1⟩ = true := by
  have hn := normalize_of_nodup (nodup_termVar_wideContra w) fun t ht => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 ht
    exact Nat.one_pos
  have hcon : (wideContra w).normalize.IsContradiction := by
    rw [hn]
    simp [IsContradiction, coeffSum, wideContra, Function.comp_def]
  simp [check, runSteps, initDb, namesContra, lookup, hcon]

private theorem negSum_wideContra (w : ℕ) : negSum (wideContra w).terms = 0 := by
  simp [negSum, wideContra, Function.comp_def]

private theorem bound_toIneq_wideContra (w : ℕ) : (wideContra w).toIneq.bound = w + 1 := by
  rw [bound_toIneq, negSum_wideContra]
  simp [wideContra]

private theorem lhs_toIneq_wideContra (w : ℕ) :
    (wideContra w).toIneq.lhs (fun _ => true) = w := by
  have h := lhs_sub_bound_sum (fun _ => true) (wideContra w).terms
  rw [bound_sum_termIneq, negSum_wideContra] at h
  have hL : PBConstr.lhs (fun _ => true) (wideContra w).terms = w := by
    simp [PBConstr.lhs, termVal, Literal.eval, wideContra, Function.comp_def]
  have h0 : (⟨0, (wideContra w).degree⟩ : Ineq ℕ).lhs (fun _ => true) = 0 := by
    simp [lhs_eq_finsuppSum]
  rw [hL] at h
  simp only [PBConstr.toIneq, lhs_add, h0, add_zero]
  push_cast at h
  omega

private theorem coeff_toIneq_wideContra {w v : ℕ} (hv : v < w) :
    (wideContra w).toIneq.coeff v = 1 := by
  have := cf_apply_of_nodup (nodup_termVar_wideContra w) (t := (1, (v, true)))
    (List.mem_map.2 ⟨v, List.mem_range.2 hv, rfl⟩)
  rw [toIneq_eq]
  simpa [termCoeff] using this

/-- Without the axiom `-x_v ≥ -1`, every line of a cutting planes proof from
`x₀ + ⋯ + x_{w-1} ≥ w + 1` holds at the integer point with `x_v = 2` and every other variable
`1`, whose value is the value at the all-ones point plus the coefficient of `x_v`. -/
private theorem bound_le_of_isProof {w v : ℕ} (hv : v < w) {ls : List (Ineq ℕ)} :
    IsProof {I | ∃ c ∈ [wideContra w], c.toIneq = I} ls → Ineq.leOne v ∉ ls →
      ∀ I ∈ ls, I.bound ≤ I.lhs (fun _ => true) + I.coeff v := by
  intro h
  induction h with
  | nil => simp
  | hyp _ hI ih =>
    intro hnot I' hI'
    rcases List.mem_cons.1 hI' with rfl | hI'
    · obtain ⟨c, hc, rfl⟩ := hI
      rw [List.mem_singleton] at hc
      subst hc
      rw [bound_toIneq_wideContra, lhs_toIneq_wideContra, coeff_toIneq_wideContra hv]
    · exact ih (fun hm => hnot (List.mem_cons_of_mem _ hm)) I' hI'
  | nonneg _ u ih =>
    intro hnot I' hI'
    rcases List.mem_cons.1 hI' with rfl | hI'
    · simp only [Ineq.nonneg, lhs_mk_single, Finsupp.single_apply]
      split_ifs <;> simp
    · exact ih (fun hm => hnot (List.mem_cons_of_mem _ hm)) I' hI'
  | leOne _ u ih =>
    intro hnot I' hI'
    have hu : u ≠ v := by
      rintro rfl
      exact hnot List.mem_cons_self
    rcases List.mem_cons.1 hI' with rfl | hI'
    · rw [show Ineq.leOne u = (⟨Finsupp.single u (-1), -1⟩ : Ineq ℕ) from rfl, lhs_mk_single]
      simp [hu]
    · exact ih (fun hm => hnot (List.mem_cons_of_mem _ hm)) I' hI'
  | add _ hI hJ ih =>
    intro hnot I' hI'
    have ih' := ih (fun hm => hnot (List.mem_cons_of_mem _ hm))
    rcases List.mem_cons.1 hI' with rfl | hI'
    · have := ih' _ hI
      have := ih' _ hJ
      simp only [bound_add, lhs_add, coeff_add, Finsupp.add_apply]
      linarith
    · exact ih' I' hI'
  | smul _ c hc hI ih =>
    intro hnot I' hI'
    have ih' := ih (fun hm => hnot (List.mem_cons_of_mem _ hm))
    rcases List.mem_cons.1 hI' with rfl | hI'
    · have := ih' _ hI
      simp only [bound_nsmul, lhs_nsmul, coeff_nsmul, Finsupp.smul_apply, nsmul_eq_mul,
        ← mul_add]
      exact mul_le_mul_of_nonneg_left this (Int.natCast_nonneg c)
    · exact ih' I' hI'
  | div _ c hc hdvd hI ih =>
    intro hnot I' hI'
    have ih' := ih (fun hm => hnot (List.mem_cons_of_mem _ hm))
    rcases List.mem_cons.1 hI' with rfl | hI'
    · have := ih' _ hI
      rw [bound_div_le_iff hc, mul_add, ← lhs_of_coeff_eq_smul _ (smul_coeff_div hdvd).symm,
        coeff_div, Int.mul_ediv_cancel' (hdvd v)]
      exact this
    · exact ih' I' hI'

/-- **Every cutting planes refutation of `x₀ + ⋯ + x_{w-1} ≥ w + 1` has at least `w` lines**: it
uses the axiom `-x_v ≥ -1` for every `v < w`, since otherwise every line holds at the integer
point with `x_v = 2` and every other variable `1`, which satisfies the constraint and the other
axioms, and `0 ≥ 1` does not. -/
theorem le_of_refutableInSize_wideContra {w s : ℕ}
    (h : RefutableInSize {I | ∃ c ∈ [wideContra w], c.toIneq = I} s) : w ≤ s := by
  obtain ⟨ls, hls, hc, hlen⟩ := h
  have hsub : (List.range w).map Ineq.leOne ⊆ ls := by
    intro I hI
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hI
    by_contra hnot
    have := bound_le_of_isProof (List.mem_range.1 hv) hls hnot _ hc
    simp [lhs_eq_finsuppSum] at this
  have hnd : ((List.range w).map (Ineq.leOne (V := ℕ))).Nodup :=
    List.nodup_range.map fun u v huv =>
      (Finsupp.single_left_inj (by norm_num : (-1 : ℤ) ≠ 0)).1 (congrArg Ineq.coeff huv)
  have := (hnd.subperm hsub).length_le
  simp only [List.length_map, List.length_range] at this
  omega

/-- **No size bound in steps and operations alone**: no function `g` bounds the number of lines of
a cutting planes refutation by `g (|F| + s + m)`, for every checked VeriPB proof of `UNSAT` on `F`
with `s` steps and `m` operations made of `pol` steps without saturation and of deletions. The
proof with no steps refuting `x₀ + ⋯ + x_{w-1} ≥ w + 1` needs `w` lines. So the line count of
`Cslib.Logic.PL.VeriPB.refutableInSize_of_check` must grow with the variables; on this family,
with `S = {0, …, w - 1}`, it is `32 (w + 1)` against the lower bound `w`. -/
theorem not_exists_refutableInSize_of_check :
    ¬ ∃ g : ℕ → ℕ, ∀ (F : List PBConstr) (P : Proof), check F P = true →
      P.steps.all Step.IsCP →
      RefutableInSize {I | ∃ c ∈ F, c.toIneq = I} (g (F.length + P.steps.length + opCount P.steps))
  := by
  rintro ⟨g, hg⟩
  have := le_of_refutableInSize_wideContra
    (hg [wideContra (g 1 + 1)] ⟨[], 1⟩ (check_wideContra _) rfl)
  simp only [List.length_singleton, List.length_nil, opCount_nil, Nat.add_zero] at this
  omega

end VeriPB

end

end Cslib.Logic.PL

end
