/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.VeriPB
public import CslibFrontier.Logics.Propositional.CuttingPlanes
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
planes inequality (`Cslib.Logic.PL.Clause.toIneq_toPB`).

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

## Main definitions

* `Cslib.Logic.PL.PBConstr.toIneq`: a constraint as an inequality.
* `Cslib.Logic.PL.VeriPB.Step.IsCP`: a `pol` step without saturation, or a deletion.

## Main results

* `Cslib.Logic.PL.PBConstr.holds_toIneq_iff`: the translation is faithful.
* `Cslib.Logic.PL.VeriPB.exists_isProof_contra_of_check`: a checked proof of `UNSAT` made of
  such steps gives a cutting planes refutation.
* `Cslib.Logic.PL.VeriPB.exists_isProof_contra_of_check_cnf`: the same for the clauses of a CNF.
-/

public section

namespace Cslib.Logic.PL

open Ineq PBConstr

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
    obtain ⟨a, v, b⟩ := t
    simp only [List.map_cons, negSum_cons, coeffSum_cons,
      show Std.Sat.Literal.negate (v, b) = (v, !b) from rfl]
    cases b <;>
      simp only [termPos, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;>
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

/-! ### Derivability -/

namespace VeriPB

open CuttingPlanes

/-- `I` has a cutting planes derivation from `Γ` of some size: the size bounds of
`Cslib.Logic.PL.CuttingPlanes.DerivableInSize` forgotten. -/
abbrev Der (Γ : Set (Ineq ℕ)) (I : Ineq ℕ) : Prop := ∃ s, DerivableInSize Γ I s

variable {Γ : Set (Ineq ℕ)} {I J : Ineq ℕ}

theorem Der.hyp (h : I ∈ Γ) : Der Γ I := ⟨_, .hyp h⟩

theorem Der.nonneg (v : ℕ) : Der Γ (Ineq.nonneg v) := ⟨_, .nonneg v⟩

theorem Der.leOne (v : ℕ) : Der Γ (Ineq.leOne v) := ⟨_, .leOne v⟩

theorem Der.add (hI : Der Γ I) (hJ : Der Γ J) : Der Γ (I + J) :=
  let ⟨_, hI⟩ := hI; let ⟨_, hJ⟩ := hJ; ⟨_, hI.add hJ⟩

theorem Der.smul (hI : Der Γ I) {k : ℕ} (hk : 0 < k) : Der Γ (k • I) :=
  let ⟨_, hI⟩ := hI; ⟨_, hI.smul k hk⟩

theorem Der.div (hI : Der Γ I) {k : ℕ} (hk : 0 < k) (hdvd : ∀ v, (k : ℤ) ∣ I.coeff v) :
    Der Γ (I.div k) :=
  let ⟨_, hI⟩ := hI; ⟨_, hI.div k hk hdvd⟩

theorem Der.of_eq (hI : Der Γ I) (h : I = J) : Der Γ J := h ▸ hI

/-- `0 ≥ -1`. -/
theorem Der.negContra : Der Γ (-Ineq.contra) :=
  (Der.nonneg 0).add (Der.leOne 0) |>.of_eq (Ineq.nonneg_add_leOne 0)

theorem Der.zero : Der Γ 0 := by
  refine (Der.negContra.div (k := 2) Nat.zero_lt_two fun _ => by
      simp only [coeff_neg, coeff_contra, neg_zero, Finsupp.zero_apply, dvd_zero]).of_eq ?_
  refine Ineq.div_eq_of Nat.zero_lt_two
    (by simp only [coeff_neg, coeff_contra, coeff_zero, smul_zero, neg_zero])
    (by simp only [bound_neg, bound_contra, bound_zero]; decide)
    (by decide)

/-- Lowering the bound. -/
theorem Der.lower (hI : Der Γ I) (hc : J.coeff = I.coeff) (hb : J.bound ≤ I.bound) : Der Γ J := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, I.bound = J.bound + k := ⟨(I.bound - J.bound).toNat, by omega⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact hI.of_eq (Ineq.ext hc.symm (by simpa only [Nat.cast_zero, add_zero] using hk))
  · refine (hI.add (Der.negContra.smul hk0)).of_eq (Ineq.ext ?_ ?_)
    · simp only [smul_neg, coeff_add, coeff_neg, coeff_nsmul, coeff_contra, nsmul_zero, neg_zero,
        add_zero, hc]
    · simp only [smul_neg, bound_add, hk, bound_neg, bound_nsmul, bound_contra, Int.nsmul_eq_mul,
        mul_one, add_neg_cancel_right]

theorem Der.termIneq (t : ℕ × Literal ℕ) : Der Γ (termIneq t) := by
  obtain ⟨a, v, b⟩ := t
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact Der.zero.of_eq (by simp only [PBConstr.termIneq, zero_smul])
  · cases b
    exacts [(Der.leOne v).smul ha, (Der.nonneg v).smul ha]

/-- A constraint of degree `0` is a sum of literal axioms. -/
theorem Der.degree_zero (ts : List (ℕ × Literal ℕ)) : Der Γ (⟨ts, 0⟩ : PBConstr).toIneq := by
  induction ts with
  | nil => exact Der.zero.of_eq (by ext <;>
      simp only [PBConstr.toIneq, List.map_nil, List.sum_nil, zero_add, coeff_zero, bound_zero,
        Nat.cast_zero])
  | cons t ts ih =>
    refine ((Der.termIneq t).add ih).of_eq ?_
    simp only [PBConstr.toIneq, List.map_cons, List.sum_cons, add_assoc]

theorem Der.normalize {c : PBConstr} (h : Der Γ c.toIneq) : Der Γ c.normalize.toIneq := by
  have hcoeff := coeff_toIneq_normalize c
  by_cases hd : c.normalize.degree = 0
  · rw [show c.normalize = ⟨c.normalize.terms, 0⟩ by rw [← hd]]
    exact Der.degree_zero _
  · refine h.lower hcoeff (le_of_eq ?_)
    rw [toIneq_eq, toIneq_eq]
    simp only [PBConstr.normalize, negSum_fromLinear] at hd ⊢
    simp only [fromLinear] at hd ⊢
    omega

theorem Der.add' {c d : PBConstr} (hc : Der Γ c.toIneq) (hd : Der Γ d.toIneq) :
    Der Γ (c.add d).toIneq :=
  Der.normalize ((hc.add hd).of_eq (toIneq_append c d).symm)

theorem Der.mul' {c : PBConstr} (hc : Der Γ c.toIneq) (k : ℕ) : Der Γ (c.mul k).toIneq := by
  refine Der.normalize ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa only [PBConstr.mul, Nat.zero_mul, ↓reduceIte] using
      Der.degree_zero (Γ := Γ) (c.terms.map fun t => (0 * t.1, t.2))
  · exact (hc.smul hk).of_eq (toIneq_map_mul k c).symm

theorem Der.litAxiom' (l : Literal ℕ) : Der Γ (litAxiom l).toIneq := Der.degree_zero _

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

theorem Der.div' {c : PBConstr} (hc : Der Γ c.toIneq) (k : ℕ) : Der Γ (c.div k).toIneq := by
  refine Der.normalize ?_
  have hc' := Der.normalize hc
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa only [PBConstr.div, ceilDiv_zero_right] using
      Der.degree_zero (Γ := Γ) (c.normalize.terms.map fun t => (ceilDiv t.1 0, t.2))
  generalize c.normalize = c' at hc' ⊢
  obtain ⟨ts, d⟩ := c'
  simp only
  -- Add the literal axioms `(k ⌈a / k⌉ - a) ℓ ≥ 0`.
  have hE := Der.degree_zero (Γ := Γ) (ts.map fun t => (k * ceilDiv t.1 k - t.1, t.2))
  have hsum := hc'.add hE
  have hcf := cf_add_cf_round k hk ts
  have hns := negSum_add_negSum_round k hk ts
  set u := ts.map fun t => (ceilDiv t.1 k, t.2)
  set E := ts.map fun t => (k * ceilDiv t.1 k - t.1, t.2)
  have hcoeff : ((⟨ts, d⟩ : PBConstr).toIneq + (⟨E, 0⟩ : PBConstr).toIneq).coeff =
      (k : ℤ) • (⟨u, ceilDiv d k⟩ : PBConstr).toIneq.coeff := by
    simp only [toIneq_eq, coeff_add, hcf]
  have hbound : ((⟨ts, d⟩ : PBConstr).toIneq + (⟨E, 0⟩ : PBConstr).toIneq).bound =
      (d : ℤ) - k * negSum u := by
    simp only [toIneq_eq, bound_add]
    have : ((negSum ts : ℕ) : ℤ) + negSum E = k * negSum u := mod_cast hns
    push_cast; linarith
  refine (hsum.div hk fun v => ?_).of_eq ?_
  · rw [hcoeff]
    exact dvd_mul_right _ _
  · have h1 : (d : ℤ) ≤ k * ceilDiv d k := by exact_mod_cast le_mul_ceilDiv d hk
    have h2 : (k : ℤ) * ceilDiv d k < d + k := by exact_mod_cast mul_ceilDiv_lt d hk
    refine Ineq.div_eq_of hk hcoeff ?_ ?_ <;>
      (rw [hbound, toIneq_eq]; dsimp only; simp only [mul_sub, mul_one]; linarith)

theorem filter_not_bne (v : ℕ) (ts : List (ℕ × Literal ℕ)) :
    (ts.filter fun t => !(termVar t != v)) = ts.filter (termVar · == v) := by
  congr 1; funext t; simp only [bne, Bool.not_not]

theorem Der.weaken' {c : PBConstr} (hc : Der Γ c.toIneq) (v : ℕ) :
    Der Γ (c.weaken v).toIneq := by
  refine Der.normalize ?_
  have hc' := Der.normalize hc
  generalize c.normalize = c' at hc' ⊢
  obtain ⟨ts, d⟩ := c'
  simp only
  set rem := ts.filter (termVar · == v)
  set rest := ts.filter (termVar · != v)
  have hE := Der.degree_zero (Γ := Γ) (rem.map fun t => (t.1, Std.Sat.Literal.negate t.2))
  have hcf := cf_filter_add (fun t => termVar t != v) ts
  have hns := negSum_filter_add (fun t => termVar t != v) ts
  rw [filter_not_bne] at hcf hns
  have hneg := negSum_add_negSum_negate rem
  by_cases hd : coeffSum rem ≤ d
  · refine (hc'.add hE).of_eq ?_
    rw [toIneq_eq, toIneq_eq, toIneq_eq]
    refine Ineq.ext ?_ ?_
    · simp only [coeff_add, cf_map_negate, ← hcf, rem, rest]; abel
    · simp only [bound_add, rem, rest] at hneg hd ⊢
      omega
  · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hd)]
    exact Der.degree_zero _

/-- A contradiction derives `0 ≥ 1`. -/
theorem Der.contra {c : PBConstr} (hc : Der Γ c.toIneq) (h : c.IsContradiction) :
    Der Γ Ineq.contra := by
  have hE := Der.degree_zero (Γ := Γ) (c.terms.map fun t => (t.1, Std.Sat.Literal.negate t.2))
  have hneg := negSum_add_negSum_negate c.terms
  unfold IsContradiction at h
  refine (hc.add hE).lower ?_ ?_
  · rw [toIneq_eq, toIneq_eq]
    simp only [coeff_add, cf_map_negate, add_neg_cancel, coeff_contra]
  · rw [toIneq_eq, toIneq_eq]
    simp only [bound_add, bound_contra]
    omega

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

theorem polEval_der {db : List (ℕ × PBConstr)} (hdb : ∀ e ∈ db, Der Γ e.2.toIneq) :
    ∀ (ops : List PolOp) (st st' : List PBConstr), ops.all PolOp.IsCP →
      (∀ c ∈ st, Der Γ c.toIneq) → polEval db ops st = some st' → ∀ c ∈ st', Der Γ c.toIneq
  | [], st, st', _, hst, h => by cases h; exact hst
  | op :: ops, st, st', hops, hst, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hops
    have step {c : PBConstr} {st₁ : List PBConstr} (hc : Der Γ c.toIneq)
        (hst₁ : ∀ d ∈ st₁, Der Γ d.toIneq) (h' : polEval db ops (c :: st₁) = some st') :
        ∀ d ∈ st', Der Γ d.toIneq :=
      polEval_der hdb ops (c :: st₁) st' hops.2 (List.forall_mem_cons.2 ⟨hc, hst₁⟩) h'
    cases op with
    | id n =>
      simp only [polEval, Option.bind_eq_some_iff] at h
      obtain ⟨c, hc, h⟩ := h
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hc
      exact step (hdb e (List.mem_of_find?_eq_some he)) hst h
    | lit l => exact step (Der.litAxiom' l) hst h
    | sat => exact absurd hops.1 (by simp [PolOp.IsCP])
    | add =>
      match st with
      | c₂ :: c₁ :: st =>
        simp only [List.forall_mem_cons] at hst
        exact step (hst.2.1.add' hst.1) hst.2.2 h
      | [] | [_] => cases h
    | mul k =>
      match k, st with
      | k + 1, c :: st =>
        simp only [List.forall_mem_cons] at hst
        exact step (hst.1.mul' (k + 1)) hst.2 h
      | 0, _ | _ + 1, [] => cases h
    | div k =>
      match k, st with
      | k + 1, c :: st =>
        simp only [List.forall_mem_cons] at hst
        exact step (hst.1.div' (k + 1)) hst.2 h
      | 0, _ | _ + 1, [] => cases h
    | weaken v =>
      match st with
      | c :: st =>
        simp only [List.forall_mem_cons] at hst
        exact step (hst.1.weaken' v) hst.2 h
      | [] => cases h

theorem runSteps_der : ∀ (db : List (ℕ × PBConstr)) (n : ℕ) (ss : List Step)
    (db' : List (ℕ × PBConstr)) (n' : ℕ), ss.all Step.IsCP → (∀ e ∈ db, Der Γ e.2.toIneq) →
    runSteps db n ss = some (db', n') → ∀ e ∈ db', Der Γ e.2.toIneq
  | db, n, [], db', n', _, hdb, h => by
    simp only [runSteps, Option.some.injEq, Prod.mk.injEq] at h
    exact h.1 ▸ hdb
  | db, n, s :: ss, db', n', hss, hdb, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hss
    simp only [runSteps] at h
    split at h
    · rename_i db₁ n₁ h₁
      refine runSteps_der db₁ n₁ ss db' n' hss.2 ?_ h
      cases s with
      | pol ops =>
        simp only [runStep] at h₁
        split at h₁
        · rename_i c hc
          cases h₁
          have := polEval_der hdb ops [] [c] (by simpa only [Step.IsCP] using hss.1)
            (fun _ hmem => absurd hmem List.not_mem_nil) hc
          exact List.forall_mem_cons.2 ⟨this c List.mem_cons_self, hdb⟩
        · cases h₁
      | del ids =>
        simp only [runStep] at h₁
        split at h₁
        · simp only [Option.some.injEq, Prod.mk.injEq] at h₁
          exact h₁.1 ▸ fun e he => hdb e (List.mem_of_mem_filter he)
        · cases h₁
      | rup | rupSearch | pbc => simp only [Step.IsCP, Bool.false_eq_true, false_and] at hss
    · cases h

/-- **Cutting-planes proofs**: a checked VeriPB proof of `UNSAT` made of `pol` steps without
saturation and of deletions gives a cutting planes refutation of the inequalities of the
formula. -/
theorem exists_isProof_contra_of_check {F : List PBConstr} {P : Proof} (h : check F P = true)
    (hP : P.steps.all Step.IsCP) :
    ∃ s, RefutableInSize {I | ∃ c ∈ F, c.toIneq = I} s := by
  have hF : ∀ e ∈ initDb F, Der {I | ∃ c ∈ F, c.toIneq = I} e.2.toIneq := by
    intro e he
    obtain ⟨⟨c, i⟩, hci, rfl⟩ := List.mem_map.mp he
    refine Der.normalize (Der.hyp ⟨c, ?_, rfl⟩)
    obtain ⟨j, hj, hji⟩ := List.mem_iff_getElem.1 hci
    rw [List.getElem_zipIdx, Prod.mk.injEq] at hji
    exact hji.1 ▸ List.getElem_mem (by simpa only [List.length_zipIdx] using hj)
  unfold check at h
  split at h
  · rename_i db n hrun
    have hall := runSteps_der _ _ _ db n hP hF hrun
    obtain ⟨c, hc, hcon⟩ := (Option.any_eq_true _ _).mp h
    unfold lookup at hc
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hc
    exact (hall e (List.mem_of_find?_eq_some he)).contra (of_decide_eq_true hcon)
  · cases h

/-- **Cutting-planes proofs of CNFs**: for the clauses of a CNF, the refutation is one of
`φ.toIneqs`. -/
theorem exists_isProof_contra_of_check_cnf {φ : CNF ℕ} {P : Proof}
    (h : check (φ.map Clause.toPB) P = true) (hP : P.steps.all Step.IsCP) :
    ∃ s, RefutableInSize φ.toIneqs s :=
  CNF.toIneqs_eq_toPB φ ▸ exists_isProof_contra_of_check h hP

end VeriPB

end

end Cslib.Logic.PL

end
