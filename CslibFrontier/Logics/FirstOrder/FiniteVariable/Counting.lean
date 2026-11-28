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
`CountingFormula.atLeast m i φ` holds when the set of values of `xᵢ` satisfying `φ` has at least
`m` elements. The existential and universal quantifiers are derived from `atLeast 1`, and
`Formula.toCounting` embeds `FO^k` into `C^k` preserving truth, quantifier rank and free variables.

## Main definitions

* `Cslib.Logic.FO.FiniteVariable.CountingQuant`: the counting quantifier tags `∃^{≥ m}`.
* `Cslib.Logic.FO.FiniteVariable.CountingFormula`: formulas of `C^k` over the relation symbols of
  `L` (`GenFormula CountingQuant L k`), with `CountingFormula.atLeast` and
  `CountingFormula.exactly`.
* `Cslib.Logic.FO.FiniteVariable.Formula.toCounting`: the embedding of `FO^k` into `C^k`.

## Main results

* `Cslib.Logic.FO.FiniteVariable.CountingQuant.eval_iff_of_equiv`: bijections preserve counting
  quantifiers.
* `Cslib.Logic.FO.FiniteVariable.CountingFormula.realize_exactly`: `exactly m i φ` holds when
  exactly `m` values of `xᵢ` satisfy `φ`.
* `Cslib.Logic.FO.FiniteVariable.Formula.realize_toCounting`,
  `Cslib.Logic.FO.FiniteVariable.Formula.quantifierRank_toCounting`,
  `Cslib.Logic.FO.FiniteVariable.Formula.freeVars_toCounting`: the embedding preserves truth,
  quantifier rank and free variables.

## References

* [J.-Y. Cai, M. Fürer, N. Immerman, *An optimal lower bound on the number of variables for graph
  identification*][CaiFurerImmerman1992], Section 3.2.
* [N. Immerman, *Descriptive Complexity*][Immerman1999], Section 12.3 (unverified locator).
-/

public section

universe u v w w'

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
    Quantifier.eval (CountingQuant.atLeast m) p ↔ (m : ℕ∞) ≤ {c | p c}.encard :=
  Iff.rfl

/-- A bijection matching the witnesses of `pM` and `pN` preserves every counting quantifier. -/
theorem CountingQuant.eval_iff_of_equiv {M : Type w} {N : Type w'} (q : CountingQuant)
    {pM : M → Prop} {pN : N → Prop} (f : M ≃ N) (hf : ∀ c, pM c ↔ pN (f c)) :
    Quantifier.eval q pM ↔ Quantifier.eval q pN := by
  rcases q with ⟨m⟩
  rw [CountingQuant.eval_atLeast, CountingQuant.eval_atLeast]
  suffices f '' {c | pM c} = {d | pN d} by rw [← this, f.injective.encard_image]
  ext d
  exact ⟨fun ⟨c, hc, hcd⟩ => hcd ▸ (hf c).1 hc,
    fun hd => ⟨f.symm d, (hf _).2 (by rwa [f.apply_symm_apply]), f.apply_symm_apply d⟩⟩

instance : ExQuantTag CountingQuant where
  exQuant := .atLeast 1

instance {M : Type w} : LawfulExQuant CountingQuant M where
  eval_exQuant p := by
    dsimp only [ExQuantTag.exQuant]
    rw [CountingQuant.eval_atLeast, Nat.cast_one, Set.one_le_encard_iff_nonempty]
    rfl

/-! ### `C^k`: finite-variable counting logic -/

/-- Formulas of the `k`-variable counting logic `C^k` over the relation symbols of `L`. The
variables are `Fin k`, and `CountingFormula.atLeast m i φ` quantifies the variable `i`, which may
already be bound or free in an enclosing formula. -/
abbrev CountingFormula (L : Language.{u, v}) (k : ℕ) : Type v :=
  GenFormula CountingQuant L k

namespace CountingFormula

variable {L : Language.{u, v}} {k : ℕ} {M : Type w} [L.Structure M]

/-- The counting quantifier `∃^{≥ m} xᵢ φ`: at least `m` values of `xᵢ` satisfy `φ`. -/
def atLeast (m : ℕ) (i : Fin k) (φ : CountingFormula L k) : CountingFormula L k :=
  .quant (.atLeast m) i φ

/-- Exactly `m` values of the variable `xᵢ` satisfy `φ`. -/
def exactly (m : ℕ) (i : Fin k) (φ : CountingFormula L k) : CountingFormula L k :=
  atLeast m i φ ⊓ (atLeast (m + 1) i φ).not

@[simp] theorem realize_atLeast (m : ℕ) (i : Fin k) (φ : CountingFormula L k) (a : Fin k → M) :
    (atLeast m i φ).Realize a ↔
      (m : ℕ∞) ≤ {c : M | φ.Realize (Function.update a i c)}.encard := by
  rw [atLeast, GenFormula.realize_quant, CountingQuant.eval_atLeast]

@[simp] theorem realize_exactly (m : ℕ) (i : Fin k) (φ : CountingFormula L k) (a : Fin k → M) :
    (exactly m i φ).Realize a ↔
      {c : M | φ.Realize (Function.update a i c)}.encard = m := by
  rw [exactly, GenFormula.realize_inf, GenFormula.realize_not, realize_atLeast, realize_atLeast,
    Nat.cast_add_one, ENat.add_one_le_iff (ENat.natCast_ne_top m), not_lt, and_comm,
    ← le_antisymm_iff]

/-- On a finite structure, `atLeast m i φ` holds when at least `m` values of `xᵢ` satisfy `φ`,
counted by `Set.ncard`. -/
theorem realize_atLeast_iff_ncard [Finite M] (m : ℕ) (i : Fin k) (φ : CountingFormula L k)
    (a : Fin k → M) :
    (atLeast m i φ).Realize a ↔ m ≤ {c : M | φ.Realize (Function.update a i c)}.ncard := by
  rw [realize_atLeast, ← (Set.toFinite _).cast_ncard_eq, Nat.cast_le]

/-- On a finite structure, `exactly m i φ` holds when exactly `m` values of `xᵢ` satisfy `φ`,
counted by `Set.ncard`. -/
theorem realize_exactly_iff_ncard [Finite M] (m : ℕ) (i : Fin k) (φ : CountingFormula L k)
    (a : Fin k → M) :
    (exactly m i φ).Realize a ↔ {c : M | φ.Realize (Function.update a i c)}.ncard = m := by
  rw [realize_exactly, ← (Set.toFinite _).cast_ncard_eq, Nat.cast_inj]

@[simp] theorem quantifierRank_atLeast (m : ℕ) (i : Fin k) (φ : CountingFormula L k) :
    (atLeast m i φ).quantifierRank = φ.quantifierRank + 1 := by
  rw [atLeast, GenFormula.quantifierRank_quant]

@[simp] theorem quantifierRank_exactly (m : ℕ) (i : Fin k) (φ : CountingFormula L k) :
    (exactly m i φ).quantifierRank = φ.quantifierRank + 1 := by
  rw [exactly, GenFormula.quantifierRank_inf, GenFormula.quantifierRank_not,
    quantifierRank_atLeast, quantifierRank_atLeast, max_self]

@[simp] theorem freeVars_atLeast (m : ℕ) (i : Fin k) (φ : CountingFormula L k) :
    (atLeast m i φ).freeVars = φ.freeVars.erase i := by
  rw [atLeast, GenFormula.freeVars_quant]

@[simp] theorem freeVars_exactly (m : ℕ) (i : Fin k) (φ : CountingFormula L k) :
    (exactly m i φ).freeVars = φ.freeVars.erase i := by
  rw [exactly, GenFormula.freeVars_inf, GenFormula.freeVars_not, freeVars_atLeast,
    freeVars_atLeast, Finset.union_self]

end CountingFormula

/-! ### `FO^k` is a fragment of `C^k` -/

namespace Formula

variable {L : Language.{u, v}} {k : ℕ} {M : Type w} [L.Structure M]

/-- The embedding of `FO^k` into `C^k`: the existential quantifier `ex i φ` becomes
`CountingFormula.atLeast 1 i φ`. -/
def toCounting : Formula L k → CountingFormula L k
  | .falsum => .falsum
  | .equal i j => .equal i j
  | .rel R f => .rel R f
  | .imp φ ψ => .imp (toCounting φ) (toCounting ψ)
  | .quant .ex i φ => CountingFormula.atLeast 1 i (toCounting φ)

/-- The embedding preserves truth. -/
@[simp] theorem realize_toCounting (φ : Formula L k) (a : Fin k → M) :
    φ.toCounting.Realize a ↔ φ.Realize a := by
  induction φ generalizing a with
  | falsum | equal _ _ | rel _ _ => simp [toCounting]
  | imp _ _ ihφ ihψ => rw [toCounting, GenFormula.realize_imp, GenFormula.realize_imp, ihφ, ihψ]
  | quant q i _ ih =>
    cases q
    simp only [toCounting, CountingFormula.realize_atLeast, Nat.cast_one,
      Set.one_le_encard_iff_nonempty, Set.Nonempty, Set.mem_ofPred_eq, GenFormula.realize_quant,
      ExistentialQuant.eval_ex, ih]

/-- The embedding preserves quantifier rank. -/
@[simp] theorem quantifierRank_toCounting (φ : Formula L k) :
    φ.toCounting.quantifierRank = φ.quantifierRank := by
  induction φ with
  | falsum | equal _ _ | rel _ _ => simp [toCounting]
  | imp _ _ ihφ ihψ =>
    rw [toCounting, GenFormula.quantifierRank_imp, GenFormula.quantifierRank_imp, ihφ, ihψ]
  | quant q _ _ ih =>
    cases q
    rw [toCounting, CountingFormula.quantifierRank_atLeast, GenFormula.quantifierRank_quant, ih]

/-- The embedding preserves free variables. -/
@[simp] theorem freeVars_toCounting (φ : Formula L k) :
    φ.toCounting.freeVars = φ.freeVars := by
  induction φ with
  | falsum | equal _ _ | rel _ _ => simp [toCounting]
  | imp _ _ ihφ ihψ => rw [toCounting, GenFormula.freeVars_imp, GenFormula.freeVars_imp, ihφ, ihψ]
  | quant q _ _ ih =>
    cases q
    rw [toCounting, CountingFormula.freeVars_atLeast, GenFormula.freeVars_quant, ih]

end Formula

end Cslib.Logic.FO.FiniteVariable
