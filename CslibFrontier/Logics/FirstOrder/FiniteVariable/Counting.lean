/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.FiniteVariable.Basic
public import Mathlib.Data.Set.Card

/-!
# Finite-variable counting logic

The `k`-variable counting logic `C^k` extends `FO^k` by the counting quantifiers
`∃^{≥ m} xᵢ φ`, "at least `m` values of the variable `xᵢ` satisfy `φ`" ([CaiFurerImmerman1992],
Section 3.2). Over a fixed number of variables, counting quantifiers add expressive power: the
sentence `∃^{≥ 3} x₀ ⊤` uses one variable, but no one-variable first-order sentence separates a
three-element set from a two-element one.

`Cslib.Logic.FO.FiniteVariable.CountingFormula L k` instantiates `GenFormula` at `CountingQuant`,
inheriting its derived connectives, quantifier rank, free variables and congruence from
`Basic.lean`. Truth uses `Set.encard`, so it is meaningful in infinite structures too:
`atLeast m i φ` holds when the set of values of `xᵢ` satisfying `φ` has at least `m` elements.
The existential and universal quantifiers are derived from `atLeast 1`, and `Formula.toCounting`
embeds `FO^k` into `C^k` preserving truth, quantifier rank and free variables.

## Main definitions

* `Cslib.Logic.FO.FiniteVariable.CountingQuant`: the counting quantifier tags `∃^{≥ m}`.
* `Cslib.Logic.FO.FiniteVariable.CountingFormula`: formulas of `C^k` over the relation symbols of
  `L` (`GenFormula CountingQuant L k`).
* `Cslib.Logic.FO.FiniteVariable.GenFormula.atLeast`,
  `Cslib.Logic.FO.FiniteVariable.GenFormula.exactly`: counting quantifiers `∃^{≥ m}` and `∃^{= m}`.
* `Cslib.Logic.FO.FiniteVariable.GenFormula.toCounting`: the embedding of `FO^k` into `C^k`
  (exported as `Formula.toCounting`).

## Main results

* `Cslib.Logic.FO.FiniteVariable.GenFormula.realize_exactly`: `exactly m i φ` holds when
  exactly `m` values of `xᵢ` satisfy `φ`.
* `Cslib.Logic.FO.FiniteVariable.GenFormula.realize_toCounting`,
  `Cslib.Logic.FO.FiniteVariable.GenFormula.quantifierRank_toCounting`,
  `Cslib.Logic.FO.FiniteVariable.GenFormula.freeVars_toCounting`: the embedding preserves truth,
  quantifier rank and free variables.

## References

* [J.-Y. Cai, M. Fürer, N. Immerman, *An optimal lower bound on the number of variables for graph
  identification*][CaiFurerImmerman1992], Section 3.2.
* [N. Immerman, *Descriptive Complexity*][Immerman1999], Section 12.3 (unverified locator).
-/

public section

universe u v w

open FirstOrder Language Structure

namespace Cslib.Logic.FO.FiniteVariable

/-! ### Counting quantifiers `∃^{≥ m}` -/

/-- Quantifier tags `∃^{≥ m}` of counting logics `C^k` and `C^k_{∞ω}`. -/
structure CountingQuant : Type where
  /-- At least `m` domain elements satisfy the formula. -/
  atLeast ::
  /-- Minimum witness count `m`. -/
  minCount : ℕ

instance {M : Type w} : Quantifier CountingQuant M where
  eval q p := (q.minCount : ℕ∞) ≤ {c | p c}.encard
  eval_congr _ {_ _} h := by rw [Set.ext h]

@[simp] theorem CountingQuant.eval_atLeast {M : Type w} (m : ℕ) (p : M → Prop) :
    Quantifier.eval (CountingQuant.atLeast m) p ↔ (m : ℕ∞) ≤ {c | p c}.encard := by
  rfl

instance : FirstOrderQuantTag CountingQuant where
  primQuant := .inr (.atLeast 1)

instance {M : Type w} : LawfulFirstOrderQuant CountingQuant M where
  eval_primQuant p := by
    dsimp only [FirstOrderQuantTag.primQuant]
    rw [CountingQuant.eval_atLeast, Nat.cast_one, Set.one_le_encard_iff_nonempty]
    rfl

/-- Having `encard` at least `m` and not at least `m + 1` characterizes `encard = m`. -/
theorem CountingQuant.le_and_not_succ_le_encard_iff {α : Type w} (s : Set α) (m : ℕ) :
    ((m : ℕ∞) ≤ s.encard ∧ ¬((m + 1 : ℕ) : ℕ∞) ≤ s.encard) ↔ s.encard = m := by
  generalize s.encard = e
  induction e using ENat.recTopCoe with
  | top => simp only [le_top, not_true_eq_false, and_false, ENat.top_ne_natCast]
  | coe e =>
    norm_cast
    omega

/-! ### Counting operations on `GenFormula CountingQuant` -/

namespace GenFormula

variable {L : Language.{u, v}} {k : ℕ} {M : Type w} [L.Structure M]

/-- The counting quantifier `∃^{≥ m} xᵢ φ`: at least `m` values of `xᵢ` satisfy `φ`. -/
def atLeast (m : ℕ) (i : Fin k) (φ : GenFormula CountingQuant L k) :
    GenFormula CountingQuant L k :=
  quant (.atLeast m) i φ

/-- Exactly `m` values of the variable `xᵢ` satisfy `φ`. -/
def exactly (m : ℕ) (i : Fin k) (φ : GenFormula CountingQuant L k) :
    GenFormula CountingQuant L k :=
  atLeast m i φ ⊓ (atLeast (m + 1) i φ).not

@[simp] theorem realize_atLeast (m : ℕ) (i : Fin k) (φ : GenFormula CountingQuant L k)
    (a : Fin k → M) :
    (atLeast m i φ).Realize a ↔
      (m : ℕ∞) ≤ {c : M | φ.Realize (Function.update a i c)}.encard := by
  rw [atLeast, realize_quant, CountingQuant.eval_atLeast]

@[simp] theorem realize_exactly (m : ℕ) (i : Fin k) (φ : GenFormula CountingQuant L k)
    (a : Fin k → M) :
    (exactly m i φ).Realize a ↔
      {c : M | φ.Realize (Function.update a i c)}.encard = m := by
  rw [exactly, realize_inf, realize_not, realize_atLeast, realize_atLeast]
  exact CountingQuant.le_and_not_succ_le_encard_iff _ m

/-- On a finite structure, `atLeast m i φ` holds when at least `m` values of `xᵢ` satisfy `φ`,
counted by `Set.ncard`. -/
theorem realize_atLeast_iff_ncard [Finite M] (m : ℕ) (i : Fin k)
    (φ : GenFormula CountingQuant L k) (a : Fin k → M) :
    (atLeast m i φ).Realize a ↔ m ≤ {c : M | φ.Realize (Function.update a i c)}.ncard := by
  rw [realize_atLeast, ← (Set.toFinite _).cast_ncard_eq, Nat.cast_le]

/-- On a finite structure, `exactly m i φ` holds when exactly `m` values of `xᵢ` satisfy `φ`,
counted by `Set.ncard`. -/
theorem realize_exactly_iff_ncard [Finite M] (m : ℕ) (i : Fin k)
    (φ : GenFormula CountingQuant L k) (a : Fin k → M) :
    (exactly m i φ).Realize a ↔ {c : M | φ.Realize (Function.update a i c)}.ncard = m := by
  rw [realize_exactly, ← (Set.toFinite _).cast_ncard_eq, Nat.cast_inj]

@[simp] theorem quantifierRank_atLeast (m : ℕ) (i : Fin k) (φ : GenFormula CountingQuant L k) :
    (atLeast m i φ).quantifierRank = φ.quantifierRank + 1 := by
  rw [atLeast, quantifierRank_quant]

@[simp] theorem quantifierRank_exactly (m : ℕ) (i : Fin k) (φ : GenFormula CountingQuant L k) :
    (exactly m i φ).quantifierRank = φ.quantifierRank + 1 := by
  rw [exactly, quantifierRank_inf, quantifierRank_not, quantifierRank_atLeast,
    quantifierRank_atLeast, max_self]

@[simp] theorem freeVars_atLeast (m : ℕ) (i : Fin k) (φ : GenFormula CountingQuant L k) :
    (atLeast m i φ).freeVars = φ.freeVars.erase i := by
  rw [atLeast, freeVars_quant]

@[simp] theorem freeVars_exactly (m : ℕ) (i : Fin k) (φ : GenFormula CountingQuant L k) :
    (exactly m i φ).freeVars = φ.freeVars.erase i := by
  rw [exactly, freeVars_inf, freeVars_not, freeVars_atLeast, freeVars_atLeast, Finset.union_self]

end GenFormula

/-! ### `C^k`: finite-variable counting logic -/

/-- Formulas of the `k`-variable counting logic `C^k` over the relation symbols of `L`. The
variables are `Fin k`, and `atLeast m i φ` quantifies the variable `i`, which may already be bound
or free in an enclosing formula. -/
abbrev CountingFormula (L : Language.{u, v}) (k : ℕ) : Type v :=
  GenFormula CountingQuant L k

namespace CountingFormula

/-- Atomic relation `R(x_{f 0}, …)` in `C^k`. -/
@[match_pattern] abbrev rel {L : Language.{u, v}} {k l : ℕ} (R : L.Relations l)
    (f : Fin l → Fin k) : CountingFormula L k :=
  GenFormula.rel R f

export GenFormula (falsum equal quant all ex atLeast exactly iInf iSup
  realize_falsum realize_equal realize_rel realize_imp realize_quant
  realize_not realize_all realize_ex realize_atLeast realize_exactly
  realize_atLeast_iff_ncard realize_exactly_iff_ncard
  realize_bot realize_top realize_inf realize_sup realize_iInf realize_iSup
  quantifierRank_falsum quantifierRank_equal quantifierRank_rel
  quantifierRank_imp quantifierRank_quant quantifierRank_not quantifierRank_all
  quantifierRank_ex quantifierRank_atLeast quantifierRank_exactly
  quantifierRank_bot quantifierRank_top quantifierRank_inf quantifierRank_sup
  quantifierRank_iInf_le quantifierRank_iSup_le
  freeVars_falsum freeVars_equal freeVars_rel freeVars_imp freeVars_quant
  freeVars_not freeVars_all freeVars_ex freeVars_atLeast freeVars_exactly
  freeVars_bot freeVars_top freeVars_inf freeVars_sup
  freeVars_iInf_subset freeVars_iSup_subset)

end CountingFormula

/-! ### `FO^k` is a fragment of `C^k` -/

namespace GenFormula

variable {L : Language.{u, v}} {k : ℕ} {M : Type w} [L.Structure M]

/-- The embedding of `FO^k` into `C^k`: the universal quantifier `all i φ` becomes
`CountingFormula.all i φ`, that is, "no value of `xᵢ` satisfies `¬φ`". -/
def toCounting : Formula L k → CountingFormula L k
  | falsum => .falsum
  | equal i j => .equal i j
  | rel R f => .rel R f
  | imp φ ψ => .imp φ.toCounting ψ.toCounting
  | quant .all i φ => .all i φ.toCounting

/-- The embedding preserves truth. -/
@[simp] theorem realize_toCounting (φ : Formula L k) (a : Fin k → M) :
    φ.toCounting.Realize a ↔ φ.Realize a := by
  induction φ generalizing a with
  | falsum => rw [toCounting, realize_falsum, realize_falsum]
  | equal i j => rw [toCounting, realize_equal, realize_equal]
  | rel R f => rw [toCounting, realize_rel, realize_rel]
  | imp _ _ ihφ ihψ => rw [toCounting, realize_imp, realize_imp, ihφ, ihψ]
  | quant q i _ ih =>
    cases q
    simp only [toCounting, CountingFormula.realize_all, realize_quant, UniversalQuant.eval_all, ih]

/-- The embedding preserves quantifier rank. -/
@[simp] theorem quantifierRank_toCounting (φ : Formula L k) :
    φ.toCounting.quantifierRank = φ.quantifierRank := by
  induction φ with
  | falsum => rw [toCounting, quantifierRank_falsum, quantifierRank_falsum]
  | equal i j => rw [toCounting, quantifierRank_equal, quantifierRank_equal]
  | rel R f => rw [toCounting, quantifierRank_rel, quantifierRank_rel]
  | imp _ _ ihφ ihψ => rw [toCounting, quantifierRank_imp, quantifierRank_imp, ihφ, ihψ]
  | quant q i _ ih =>
    cases q
    rw [toCounting, CountingFormula.quantifierRank_all, quantifierRank_quant, ih]

/-- The embedding preserves free variables. -/
@[simp] theorem freeVars_toCounting (φ : Formula L k) :
    φ.toCounting.freeVars = φ.freeVars := by
  induction φ with
  | falsum => rw [toCounting, freeVars_falsum, freeVars_falsum]
  | equal i j => rw [toCounting, freeVars_equal, freeVars_equal]
  | rel R f => rw [toCounting, freeVars_rel, freeVars_rel]
  | imp _ _ ihφ ihψ => rw [toCounting, freeVars_imp, freeVars_imp, ihφ, ihψ]
  | quant q i _ ih =>
    cases q
    rw [toCounting, CountingFormula.freeVars_all, freeVars_quant, ih]

end GenFormula

namespace Formula

export GenFormula (toCounting realize_toCounting quantifierRank_toCounting freeVars_toCounting)

end Formula

end Cslib.Logic.FO.FiniteVariable
