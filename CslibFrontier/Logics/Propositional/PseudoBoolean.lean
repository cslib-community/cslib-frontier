/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.Propositional.CNF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Pseudo-Boolean constraints

A *pseudo-Boolean constraint* `∑ᵢ aᵢ ℓᵢ ≥ d` has natural coefficients `aᵢ` on literals `ℓᵢ` and a
natural degree `d`; a literal counts `1` when true and `0` when false
(`Cslib.Logic.PL.PBConstr`). This is the normalized form in which the VeriPB proof checker
[Bogaerts, Gocht, McCreesh and Nordström][BogaertsGochtMcCreeshNordstrom2023] stores constraints.
The definitions here are computable and written with structural recursion on lists, so that the
kernel can evaluate them.

A constraint is *normalized* (`Cslib.Logic.PL.PBConstr.normalize`) through its linear form: the
literal `¬x` is `1 - x`, so the constraint is `∑ᵥ cᵥ xᵥ ≥ D` with integer `cᵥ` and `D`
(`Cslib.Logic.PL.PBConstr.toLinear`); terms on the same variable are merged and terms with
coefficient `0` dropped, and the result is turned back into literals with positive coefficients,
the degree rising by the coefficients of the negative literals and clamped at `0`. Normalization
changes no satisfying assignment (`Cslib.Logic.PL.PBConstr.holds_normalize`) and introduces no
variable (`Cslib.Logic.PL.PBConstr.mem_vars_of_mem_vars_normalize`).

The rules of the cutting-planes fragment of VeriPB [Gocht and Nordström][GochtNordstrom2021] are
sound (`Cslib.Logic.PL.PBConstr.Holds.add`, …): addition, multiplication by a natural, division by
a positive natural with every coefficient and the degree rounded up, saturation of every
coefficient at the degree, weakening (dropping a variable and lowering the degree by its
coefficients), and the literal axioms `ℓ ≥ 0`. The negation of `∑ aᵢ ℓᵢ ≥ d` is
`∑ aᵢ ¬ℓᵢ ≥ ∑ aᵢ - d + 1` (`Cslib.Logic.PL.PBConstr.holds_negate`).

## Main definitions

* `Cslib.Logic.PL.PBConstr`, `Cslib.Logic.PL.PBConstr.Holds`: constraints and their satisfaction.
* `Cslib.Logic.PL.PBConstr.normalize`: the normal form.
* `Cslib.Logic.PL.PBConstr.vars`: the variables of the terms of a constraint.
* `Cslib.Logic.PL.PBConstr.add`, `Cslib.Logic.PL.PBConstr.mul`, `Cslib.Logic.PL.PBConstr.div`,
  `Cslib.Logic.PL.PBConstr.saturate`, `Cslib.Logic.PL.PBConstr.weaken`,
  `Cslib.Logic.PL.PBConstr.litAxiom`, `Cslib.Logic.PL.PBConstr.negate`: the rules.
* `Cslib.Logic.PL.PBConstr.IsContradiction`: a constraint whose coefficients sum to less than its
  degree, which no assignment satisfies.
* `Cslib.Logic.PL.Clause.toPB`: a clause as the constraint `∑ ℓ ≥ 1` over its distinct literals.

## References

* [B. Bogaerts, S. Gocht, C. McCreesh, J. Nordström, *Certified Dominance and Symmetry Breaking for
  Combinatorial Optimisation*][BogaertsGochtMcCreeshNordstrom2023]
* [S. Gocht, J. Nordström, *Certifying Parity Reasoning Efficiently Using Pseudo-Boolean
  Proofs*][GochtNordstrom2021]
-/

@[expose] public section

namespace Cslib.Logic.PL

/-- A **pseudo-Boolean constraint** `∑ᵢ aᵢ ℓᵢ ≥ d` over the variables `ℕ`: a list of terms, each a
natural coefficient and a literal, and a natural degree. -/
structure PBConstr where
  /-- The terms `aᵢ ℓᵢ`. -/
  terms : List (ℕ × Literal ℕ)
  /-- The degree `d`. -/
  degree : ℕ
  deriving DecidableEq, Repr

namespace PBConstr

/-! ### Semantics -/

/-- The variable of a term. -/
def termVar : ℕ × Literal ℕ → ℕ
  | (_, v, _) => v

/-- The sign of the literal of a term: `true` for `x`, `false` for `¬x`. -/
def termPos : ℕ × Literal ℕ → Bool
  | (_, _, b) => b

@[simp] theorem termVar_mk (a v : ℕ) (b : Bool) : termVar (a, v, b) = v := rfl

@[simp] theorem termPos_mk (a v : ℕ) (b : Bool) : termPos (a, v, b) = b := rfl

/-- The value of a term: its coefficient if its literal is true, and `0` otherwise. -/
def termVal (σ : ℕ → Bool) (t : ℕ × Literal ℕ) : ℕ := t.1 * (Literal.eval σ t.2).toNat

/-- The value `∑ᵢ aᵢ ℓᵢ` of a list of terms. -/
def lhs (σ : ℕ → Bool) (ts : List (ℕ × Literal ℕ)) : ℕ := (ts.map (termVal σ)).sum

/-- `σ` satisfies the constraint. -/
def Holds (σ : ℕ → Bool) (c : PBConstr) : Prop := c.degree ≤ lhs σ c.terms

instance (σ : ℕ → Bool) (c : PBConstr) : Decidable (c.Holds σ) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- The sum of the coefficients. -/
def coeffSum (ts : List (ℕ × Literal ℕ)) : ℕ := (ts.map (·.1)).sum

@[simp] theorem lhs_nil (σ : ℕ → Bool) : lhs σ [] = 0 := rfl

@[simp] theorem lhs_cons (σ : ℕ → Bool) (t : ℕ × Literal ℕ) (ts : List (ℕ × Literal ℕ)) :
    lhs σ (t :: ts) = termVal σ t + lhs σ ts := by simp [lhs]

@[simp] theorem lhs_append (σ : ℕ → Bool) (ts us : List (ℕ × Literal ℕ)) :
    lhs σ (ts ++ us) = lhs σ ts + lhs σ us := by simp [lhs]

@[simp] theorem coeffSum_nil : coeffSum [] = 0 := rfl

@[simp] theorem coeffSum_cons (t : ℕ × Literal ℕ) (ts : List (ℕ × Literal ℕ)) :
    coeffSum (t :: ts) = t.1 + coeffSum ts := by simp [coeffSum]

theorem termVal_le (σ : ℕ → Bool) (t : ℕ × Literal ℕ) : termVal σ t ≤ t.1 := by
  unfold termVal
  cases Literal.eval σ t.2 <;> simp

theorem lhs_le_coeffSum (σ : ℕ → Bool) (ts : List (ℕ × Literal ℕ)) : lhs σ ts ≤ coeffSum ts := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp only [lhs_cons, coeffSum_cons]; have := termVal_le σ t; omega

/-- A constraint holds at `σ` exactly when it holds at an assignment agreeing with `σ` on the
variables of its terms. -/
theorem holds_congr {σ τ : ℕ → Bool} {c : PBConstr}
    (h : ∀ t ∈ c.terms, σ (termVar t) = τ (termVar t)) : c.Holds σ ↔ c.Holds τ := by
  suffices lhs σ c.terms = lhs τ c.terms by simp only [Holds, this]
  exact congrArg List.sum <| List.map_congr_left fun ⟨a, v, b⟩ ht =>
    congrArg (fun x => a * (x == b).toNat) (h _ ht)

/-- A term and the term of the negated literal sum to the coefficient. -/
theorem termVal_add_negate (σ : ℕ → Bool) (a : ℕ) (l : Literal ℕ) :
    termVal σ (a, l) + termVal σ (a, Std.Sat.Literal.negate l) = a := by
  obtain ⟨v, b⟩ := l
  unfold termVal
  cases b <;> cases h : σ v <;> simp [Literal.eval, Std.Sat.Literal.negate, h]

/-! ### The linear form -/

/-- The signed coefficient of a term on its variable: `a` for `x`, `-a` for `¬x`. -/
def termCoeff (t : ℕ × Literal ℕ) : ℤ := if termPos t then t.1 else -t.1

/-- The coefficients of the negative literals, whose `1`s move to the right-hand side. -/
def negSum (ts : List (ℕ × Literal ℕ)) : ℕ := (ts.map fun t => if termPos t then 0 else t.1).sum

/-- Add `a` to the coefficient of `v` in a list of variables and integer coefficients. -/
def insertCoeff (v : ℕ) (a : ℤ) : List (ℕ × ℤ) → List (ℕ × ℤ)
  | [] => [(v, a)]
  | (u, b) :: L => if u = v then (u, b + a) :: L else (u, b) :: insertCoeff v a L

/-- The linear form `∑ᵥ cᵥ xᵥ` of a list of terms, one entry per variable. -/
def toLinear (ts : List (ℕ × Literal ℕ)) : List (ℕ × ℤ) :=
  ts.foldr (fun t L => insertCoeff (termVar t) (termCoeff t) L) []

/-- The value `∑ᵥ cᵥ xᵥ` of a linear form. -/
def linVal (σ : ℕ → Bool) (L : List (ℕ × ℤ)) : ℤ := (L.map fun e => e.2 * ((σ e.1).toNat : ℤ)).sum

/-- The sum of the magnitudes of the negative coefficients of a linear form. -/
def negMass (L : List (ℕ × ℤ)) : ℕ := (L.map fun e => (-e.2).toNat).sum

@[simp] theorem linVal_nil (σ : ℕ → Bool) : linVal σ [] = 0 := rfl

@[simp] theorem linVal_cons (σ : ℕ → Bool) (e : ℕ × ℤ) (L : List (ℕ × ℤ)) :
    linVal σ (e :: L) = e.2 * ((σ e.1).toNat : ℤ) + linVal σ L := by simp [linVal]

/-- Negating every coefficient negates the value. -/
theorem linVal_map_neg (σ : ℕ → Bool) (L : List (ℕ × ℤ)) :
    linVal σ (L.map fun e => (e.1, -e.2)) = -linVal σ L := by
  induction L with
  | nil => simp
  | cons e L ih => rw [List.map_cons, linVal_cons, linVal_cons, ih, neg_add, neg_mul]

/-- A linear form has the same value at assignments agreeing on its variables. -/
theorem linVal_congr {σ τ : ℕ → Bool} {L : List (ℕ × ℤ)} (h : ∀ e ∈ L, σ e.1 = τ e.1) :
    linVal σ L = linVal τ L := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [linVal_cons, h e List.mem_cons_self, ih fun e he => h e (List.mem_cons_of_mem _ he)]

theorem linVal_insertCoeff (σ : ℕ → Bool) (v : ℕ) (a : ℤ) (L : List (ℕ × ℤ)) :
    linVal σ (insertCoeff v a L) = a * ((σ v).toNat : ℤ) + linVal σ L := by
  fun_induction insertCoeff v a L with
  | case1 => simp -- []: new entry
  | case2 => simp; ring -- u = v: add to coefficient
  | case3 u b L hne ih => simp [ih]; ring -- u ≠ v: recurse

/-- Adding a coefficient for a variable not in the linear form appends it. -/
theorem insertCoeff_of_not_mem {v : ℕ} {a : ℤ} {L : List (ℕ × ℤ)} (h : v ∉ L.map Prod.fst) :
    insertCoeff v a L = L ++ [(v, a)] := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    obtain ⟨u, b⟩ := e
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp [insertCoeff, Ne.symm h.1, ih h.2]

theorem mem_map_fst_insertCoeff {x v : ℕ} {a : ℤ} {L : List (ℕ × ℤ)} :
    x ∈ (insertCoeff v a L).map Prod.fst ↔ x = v ∨ x ∈ L.map Prod.fst := by
  induction L with
  | nil => simp [insertCoeff]
  | cons e L ih =>
    obtain ⟨u, b⟩ := e
    by_cases h : u = v
    · subst h; simp only [insertCoeff, ↓reduceIte, List.map_cons, List.mem_cons]; tauto
    · simp only [insertCoeff, h, ↓reduceIte, List.map_cons, List.mem_cons] at ih ⊢
      rw [ih]; tauto

theorem nodup_map_fst_insertCoeff {v : ℕ} {a : ℤ} {L : List (ℕ × ℤ)}
    (h : (L.map Prod.fst).Nodup) : ((insertCoeff v a L).map Prod.fst).Nodup := by
  induction L with
  | nil => simp [insertCoeff]
  | cons e L ih =>
    obtain ⟨u, b⟩ := e
    simp only [List.map_cons, List.nodup_cons] at h
    by_cases huv : u = v
    · subst huv; simpa [insertCoeff] using h
    · simp only [insertCoeff, huv, ↓reduceIte, List.map_cons, List.nodup_cons]
      exact ⟨fun hm => (mem_map_fst_insertCoeff.1 hm).elim huv h.1, ih h.2⟩

/-- The linear form of terms has one entry per variable. -/
theorem nodup_map_fst_toLinear (ts : List (ℕ × Literal ℕ)) :
    ((toLinear ts).map Prod.fst).Nodup := by
  induction ts with
  | nil => simp [toLinear]
  | cons t ts ih => exact nodup_map_fst_insertCoeff ih

/-- The linear form of terms has no variable other than theirs. -/
theorem fst_mem_of_mem_toLinear {ts : List (ℕ × Literal ℕ)} {e : ℕ × ℤ} (h : e ∈ toLinear ts) :
    e.1 ∈ ts.map termVar := by
  induction ts generalizing e with
  | nil => simp [toLinear] at h
  | cons t ts ih =>
    rcases mem_map_fst_insertCoeff.1 (List.mem_map_of_mem (f := Prod.fst) h) with h | h
    · simp [h]
    · obtain ⟨e', he', heq⟩ := List.mem_map.1 h
      exact List.mem_cons_of_mem _ (heq ▸ ih he')

/-- The value of a term is its signed coefficient times its variable, plus its coefficient if
its literal is negative. -/
theorem termVal_eq (σ : ℕ → Bool) (t : ℕ × Literal ℕ) :
    (termVal σ t : ℤ) =
      termCoeff t * ((σ (termVar t)).toNat : ℤ) + if termPos t then 0 else (t.1 : ℤ) := by
  obtain ⟨a, v, b⟩ := t
  unfold termVal termCoeff
  cases b <;> cases h : σ v <;> simp [Literal.eval, h]

/-- **The linear form**: `∑ aᵢ ℓᵢ = ∑ᵥ cᵥ xᵥ + ∑_{ℓᵢ negative} aᵢ`. -/
theorem lhs_eq_linVal (σ : ℕ → Bool) (ts : List (ℕ × Literal ℕ)) :
    (lhs σ ts : ℤ) = linVal σ (toLinear ts) + negSum ts := by
  induction ts with
  | nil => simp [toLinear, negSum]
  | cons t ts ih =>
    have hneg : (negSum (t :: ts) : ℤ) = (if termPos t then 0 else (t.1 : ℤ)) + negSum ts := by
      cases h : termPos t <;> simp [negSum, h]
    rw [toLinear, List.foldr_cons, ← toLinear, lhs_cons, Nat.cast_add, linVal_insertCoeff,
      termVal_eq, ih, hneg]
    ring

theorem neg_negMass_le_linVal (σ : ℕ → Bool) (L : List (ℕ × ℤ)) :
    -(negMass L : ℤ) ≤ linVal σ L := by
  induction L with
  | nil => simp [negMass]
  | cons e L ih =>
    simp only [negMass, List.map_cons, List.sum_cons, Nat.cast_add, linVal_cons] at ih ⊢
    have : -((-e.2).toNat : ℤ) ≤ e.2 * ((σ e.1).toNat : ℤ) := by
      cases σ e.1 <;> simp; omega
    linarith

/-- The term of a linear-form entry: `c x` for `c > 0`, `|c| ¬x` for `c < 0`, none for `0`. -/
def entryTerm (e : ℕ × ℤ) : Option (ℕ × Literal ℕ) :=
  if 0 < e.2 then some (e.2.toNat, (e.1, true))
  else if e.2 < 0 then some ((-e.2).toNat, (e.1, false)) else none

/-- The constraint `∑ᵥ cᵥ xᵥ ≥ D` of a linear form, with positive coefficients on literals. -/
def fromLinear (L : List (ℕ × ℤ)) (D : ℤ) : PBConstr :=
  ⟨L.filterMap entryTerm, (D + negMass L).toNat⟩

theorem lhs_entryTerm (σ : ℕ → Bool) (e : ℕ × ℤ) :
    (lhs σ (entryTerm e).toList : ℤ) = e.2 * ((σ e.1).toNat : ℤ) + ((-e.2).toNat : ℤ) := by
  obtain ⟨v, c⟩ := e
  unfold entryTerm
  split_ifs with h1 h2 <;> cases h : σ v <;> simp [termVal, Literal.eval, h] <;> omega

theorem lhs_fromLinear (σ : ℕ → Bool) (L : List (ℕ × ℤ)) (D : ℤ) :
    (lhs σ (fromLinear L D).terms : ℤ) = linVal σ L + negMass L := by
  simp only [fromLinear]
  induction L with
  | nil => simp [negMass]
  | cons e L ih =>
    have hc : lhs σ (List.filterMap entryTerm (e :: L)) =
        lhs σ (entryTerm e).toList + lhs σ (List.filterMap entryTerm L) := by
      cases h : entryTerm e <;> simp [h]
    simp only [negMass, List.map_cons, List.sum_cons, Nat.cast_add] at ih ⊢
    rw [hc, Nat.cast_add, lhs_entryTerm, ih, linVal_cons]
    ring

theorem holds_fromLinear_iff (σ : ℕ → Bool) (L : List (ℕ × ℤ)) (D : ℤ) :
    (fromLinear L D).Holds σ ↔ D ≤ linVal σ L := by
  have h1 := lhs_fromLinear σ L D
  have h2 := neg_negMass_le_linVal σ L
  simp only [Holds, fromLinear, ← Int.ofNat_le] at h1 ⊢
  omega

/-! ### Normalization -/

/-- **The normal form**: merge the terms on each variable, drop zero coefficients, and move the
constants of negative literals into the degree, clamped at `0`. -/
def normalize (c : PBConstr) : PBConstr :=
  fromLinear (toLinear c.terms) ((c.degree : ℤ) - negSum c.terms)

theorem holds_iff_linVal (σ : ℕ → Bool) (c : PBConstr) :
    c.Holds σ ↔ (c.degree : ℤ) - negSum c.terms ≤ linVal σ (toLinear c.terms) := by
  have := lhs_eq_linVal σ c.terms
  simp only [Holds, ← Int.ofNat_le]
  omega

/-- **Normalization changes no satisfying assignment.** -/
@[simp] theorem holds_normalize (σ : ℕ → Bool) (c : PBConstr) :
    c.normalize.Holds σ ↔ c.Holds σ := by
  rw [normalize, holds_fromLinear_iff, holds_iff_linVal]

/-- The variables of the terms of a constraint. -/
def vars (c : PBConstr) : List ℕ := c.terms.map termVar

/-- **Normalization introduces no variable.** -/
theorem mem_vars_of_mem_vars_normalize {c : PBConstr} {x : ℕ} (h : x ∈ c.normalize.vars) :
    x ∈ c.vars := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
  obtain ⟨e, he, het⟩ := List.mem_filterMap.1 ht
  have hv : termVar t = e.1 := by
    unfold entryTerm at het
    split_ifs at het <;> cases het <;> rfl
  exact hv ▸ fst_mem_of_mem_toLinear he

/-! ### The rules -/

/-- **Addition**: the sum of two constraints, normalized. -/
def add (c d : PBConstr) : PBConstr := normalize ⟨c.terms ++ d.terms, c.degree + d.degree⟩

/-- **Multiplication** by a natural `k`, normalized. -/
def mul (k : ℕ) (c : PBConstr) : PBConstr :=
  normalize ⟨c.terms.map fun t => (k * t.1, t.2), k * c.degree⟩

/-- `⌈a / k⌉`, and `0` for `k = 0`. -/
def ceilDiv (a k : ℕ) : ℕ := (a + k - 1) / k

/-- **Division** by `k`: normalize, then round every coefficient and the degree up. -/
def div (k : ℕ) (c : PBConstr) : PBConstr :=
  let n := c.normalize
  normalize ⟨n.terms.map fun t => (ceilDiv t.1 k, t.2), ceilDiv n.degree k⟩

/-- **Saturation**: normalize, then cap every coefficient at the degree. -/
def saturate (c : PBConstr) : PBConstr :=
  let n := c.normalize
  normalize ⟨n.terms.map fun t => (min t.1 n.degree, t.2), n.degree⟩

/-- **Weakening** on the variable `v`: normalize, drop the terms on `v`, and lower the degree by
their coefficients. -/
def weaken (v : ℕ) (c : PBConstr) : PBConstr :=
  let n := c.normalize
  normalize ⟨n.terms.filter (termVar · != v), n.degree - coeffSum (n.terms.filter (termVar · == v))⟩

/-- **The literal axiom** `ℓ ≥ 0`. -/
def litAxiom (l : Literal ℕ) : PBConstr := ⟨[(1, l)], 0⟩

/-- **The negation** of the normal form of `∑ aᵢ ℓᵢ ≥ d`: `∑ aᵢ ¬ℓᵢ ≥ ∑ aᵢ - d + 1`. -/
def negate (c : PBConstr) : PBConstr :=
  let n := c.normalize
  ⟨n.terms.map fun t => (t.1, Std.Sat.Literal.negate t.2), coeffSum n.terms + 1 - n.degree⟩

/-- A constraint whose coefficients sum to less than its degree: no assignment satisfies it. -/
def IsContradiction (c : PBConstr) : Prop := coeffSum c.terms < c.degree

instance (c : PBConstr) : Decidable c.IsContradiction := inferInstanceAs (Decidable (_ < _))

theorem IsContradiction.not_holds {c : PBConstr} (h : c.IsContradiction) (σ : ℕ → Bool) :
    ¬ c.Holds σ := fun hc => by
  have := lhs_le_coeffSum σ c.terms
  unfold Holds at hc; unfold IsContradiction at h; omega

/-! ### Soundness of the rules -/

variable {σ : ℕ → Bool} {c d : PBConstr}

theorem lhs_map_mul (σ : ℕ → Bool) (k : ℕ) (ts : List (ℕ × Literal ℕ)) :
    lhs σ (ts.map fun t => (k * t.1, t.2)) = k * lhs σ ts := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [ih, termVal, Nat.mul_add, Nat.mul_assoc]

theorem Holds.add (hc : c.Holds σ) (hd : d.Holds σ) : (c.add d).Holds σ := by
  rw [PBConstr.add, holds_normalize]
  unfold Holds at hc hd ⊢
  simp only [lhs_append]; omega

theorem Holds.mul (hc : c.Holds σ) (k : ℕ) : (c.mul k).Holds σ := by
  rw [PBConstr.mul, holds_normalize]
  unfold Holds at hc ⊢
  rw [lhs_map_mul]; exact Nat.mul_le_mul_left k hc

theorem le_mul_ceilDiv (a : ℕ) {k : ℕ} (hk : 0 < k) : a ≤ k * ceilDiv a k := by
  unfold ceilDiv
  have h1 := Nat.div_add_mod (a + k - 1) k
  have h2 := Nat.mod_lt (a + k - 1) hk
  generalize k * ((a + k - 1) / k) = p at *
  omega

theorem ceilDiv_le_of_le_mul {a k x : ℕ} (hk : 0 < k) (h : a ≤ k * x) : ceilDiv a k ≤ x := by
  unfold ceilDiv
  rw [Nat.div_le_iff_le_mul_add_pred hk]
  generalize k * x = p at *
  omega

theorem lhs_le_mul_lhs_ceilDiv (σ : ℕ → Bool) {k : ℕ} (hk : 0 < k) (ts : List (ℕ × Literal ℕ)) :
    lhs σ ts ≤ k * lhs σ (ts.map fun t => (ceilDiv t.1 k, t.2)) := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have : termVal σ t ≤ k * termVal σ (ceilDiv t.1 k, t.2) := by
      unfold termVal
      cases Literal.eval σ t.2 <;> simp [le_mul_ceilDiv _ hk]
    simp only [List.map_cons, lhs_cons, Nat.mul_add]
    generalize k * termVal σ (ceilDiv t.1 k, t.2) = p at *
    generalize k * lhs σ (ts.map fun t => (ceilDiv t.1 k, t.2)) = q at *
    omega

theorem Holds.div (hc : c.Holds σ) (k : ℕ) : (c.div k).Holds σ := by
  rw [PBConstr.div, holds_normalize]
  rw [← holds_normalize] at hc
  unfold Holds at hc ⊢
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [ceilDiv]
  · exact ceilDiv_le_of_le_mul hk (hc.trans (lhs_le_mul_lhs_ceilDiv σ hk _))

theorem Holds.saturate (hc : c.Holds σ) : c.saturate.Holds σ := by
  rw [PBConstr.saturate, holds_normalize]
  rw [← holds_normalize] at hc
  unfold Holds at hc ⊢
  generalize c.normalize.degree = D at hc ⊢
  generalize c.normalize.terms = ts at hc ⊢
  suffices ∀ ts : List (ℕ × Literal ℕ),
      min (lhs σ ts) D ≤ lhs σ (ts.map fun t => (min t.1 D, t.2)) by
    dsimp only; have := this ts; omega
  intro ts
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, lhs_cons]
    unfold termVal at *
    cases Literal.eval σ t.2 <;> simp <;> omega

theorem lhs_le_filter (σ : ℕ → Bool) (v : ℕ) (ts : List (ℕ × Literal ℕ)) :
    lhs σ ts ≤ lhs σ (ts.filter (termVar · != v)) + coeffSum (ts.filter (termVar · == v)) := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [List.filter_cons, List.filter_cons]
    have := termVal_le σ t
    by_cases h : termVar t = v
    · simp only [h, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
        lhs_cons, coeffSum_cons]
      omega
    · simp only [bne_iff_ne.2 h, beq_eq_false_iff_ne.2 h, ↓reduceIte, Bool.false_eq_true,
        lhs_cons]
      omega

theorem Holds.weaken (hc : c.Holds σ) (v : ℕ) : (c.weaken v).Holds σ := by
  rw [PBConstr.weaken, holds_normalize]
  rw [← holds_normalize] at hc
  unfold Holds at hc ⊢
  generalize c.normalize.degree = D at hc ⊢
  generalize c.normalize.terms = ts at hc ⊢
  have := lhs_le_filter σ v ts
  dsimp only; omega

theorem holds_litAxiom (σ : ℕ → Bool) (l : Literal ℕ) : (litAxiom l).Holds σ := by
  simp [Holds, litAxiom]

/-- **The negation is exact.** -/
theorem holds_negate (σ : ℕ → Bool) (c : PBConstr) : c.negate.Holds σ ↔ ¬ c.Holds σ := by
  rw [← holds_normalize σ c]
  unfold Holds negate
  dsimp only
  generalize c.normalize.degree = D
  generalize c.normalize.terms = ts
  have hsum : lhs σ (ts.map fun t => (t.1, Std.Sat.Literal.negate t.2)) + lhs σ ts =
      coeffSum ts := by
    induction ts with
    | nil => simp
    | cons t ts ih =>
      obtain ⟨a, l⟩ := t
      simp only [List.map_cons, lhs_cons, coeffSum_cons]
      have := termVal_add_negate σ a l
      omega
  omega

/-! ### Clauses -/

end PBConstr

/-- A clause as the constraint `∑ ℓ ≥ 1` over its distinct literals. -/
def Clause.toPB (c : Clause ℕ) : PBConstr := ⟨c.dedup.map fun l => (1, l), 1⟩

theorem Clause.holds_toPB_iff (σ : ℕ → Bool) (c : Clause ℕ) :
    c.toPB.Holds σ ↔ c.eval σ = true := by
  rw [Clause.eval_eq_true_iff]
  unfold Clause.toPB PBConstr.Holds
  simp only
  have : ∀ ls : List (Literal ℕ), 1 ≤ PBConstr.lhs σ (ls.map fun l => (1, l)) ↔
      ∃ l ∈ ls, Literal.eval σ l = true := by
    intro ls
    induction ls with
    | nil => simp
    | cons l ls ih =>
      simp only [List.map_cons, PBConstr.lhs_cons, List.mem_cons, exists_eq_or_imp, ← ih]
      unfold PBConstr.termVal
      cases Literal.eval σ l <;> simp
  rw [this]
  simp [List.mem_dedup]

end Cslib.Logic.PL

end
