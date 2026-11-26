/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.QuantifierRank
public import Mathlib.Data.Fintype.Basic
public import Mathlib.ModelTheory.Semantics
import CslibFrontier.Foundations.Data.List.FoldrForall

/-!
# Finite-variable first-order logic

The `k`-variable fragment `FO^k` of first-order logic consists of the formulas that use at most `k`
distinct variable names, each of which may be quantified again inside its own scope. Reusing names
gives these formulas more power than their number of variables suggests: on linear orders, a
formula with two variables can say that there are at least `n` elements, for every `n`
([Libkin2004], formula (11.4)).

Mathlib's `FirstOrder.Language.BoundedFormula` gives every quantifier a fresh de Bruijn index, so
it cannot say that two quantifiers bind the same variable. This file introduces a quantifier-generic
syntax `Cslib.Logic.FO.FiniteVariable.GenFormula Q L k` whose variables are `Fin k` and whose
single-variable quantifiers come from `Q` (`Quantifier`), and instantiates it at `ExistentialQuant`
to obtain `Cslib.Logic.FO.FiniteVariable.Formula L k` (`FO^k`). In `Counting.lean`, instantiating
the same syntax at `CountingQuant` yields `CountingFormula L k` (`C^k`) without duplicating derived
connectives, semantics, quantifier rank, free variables or congruence. The translation
`Formula.toFormula` into Mathlib's `L.Formula (Fin k)` preserves truth (`Formula.realize_toFormula`)
and quantifier rank (`Formula.quantifierRank_toFormula`), so `FO^k` is a fragment of ordinary
first-order logic.

As in [Libkin2004] and [Immerman1999], the vocabulary is relational: atomic formulas are equations
between variables and relation symbols applied to variables. Function and constant symbols of `L`
are simply not used, so the language need not be relational.

## Main definitions

* `Cslib.Logic.FO.FiniteVariable.Quantifier`: extensional semantics for single-variable quantifiers.
* `Cslib.Logic.FO.FiniteVariable.GenFormula`: `k`-variable formulas parameterized by a quantifier
  kind `Q`, with `GenFormula.Realize`, `GenFormula.quantifierRank`, `GenFormula.freeVars`,
  `GenFormula.not`, `GenFormula.ex`, `GenFormula.all`, `GenFormula.iInf`, and `GenFormula.iSup`.
* `Cslib.Logic.FO.FiniteVariable.Formula`: formulas of `FO^k` over the relation symbols of `L`.
* `Cslib.Logic.FO.FiniteVariable.Formula.toFormula`: the translation of `Formula` to Mathlib's
  formulas.

## Main results

* `Cslib.Logic.FO.FiniteVariable.GenFormula.realize_congr`: truth depends only on the values of the
  free variables.
* `Cslib.Logic.FO.FiniteVariable.Formula.realize_toFormula`,
  `Cslib.Logic.FO.FiniteVariable.Formula.quantifierRank_toFormula`: the translation preserves
  truth and quantifier rank.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Section 11.1, Definition 11.1.
* [N. Immerman, *Descriptive Complexity*][Immerman1999], Definition 6.9.
-/

public section

universe u v w w'

open FirstOrder Language Structure

namespace Cslib.Logic.FO.FiniteVariable

/-! ### Extensional single-variable quantifiers -/

/-- Semantics of a single-variable quantifier kind `Q` over a domain `M`. Each quantifier
evaluates a unary predicate on `M` and respects extensionality. -/
class Quantifier (Q : Type) (M : Type w) where
  /-- Whether the predicate `p : M → Prop` satisfies the quantifier `q`. -/
  eval : Q → (M → Prop) → Prop
  /-- Quantifiers depend only on the extension of the predicate. -/
  eval_congr (q : Q) {p p' : M → Prop} :
    (∀ c, p c ↔ p' c) → (eval q p ↔ eval q p')

/-- Distinguished existential quantifier tag equipping `GenFormula Q L k` and
`InfinitaryGenFormula Q L k` with `ex` and `all`. -/
class ExQuantTag (Q : Type) where
  /-- The quantifier tag representing `∃`. -/
  exQuant : Q

/-- Semantic lawfulness for `ExQuantTag`: `exQuant` evaluates as `∃`. -/
class LawfulExQuant (Q : Type) (M : Type w) [Quantifier Q M] [ExQuantTag Q] : Prop where
  /-- `ExQuantTag.exQuant` holds of `p` iff some element satisfies `p`. -/
  eval_exQuant (p : M → Prop) : Quantifier.eval (ExQuantTag.exQuant (Q := Q)) p ↔ ∃ c, p c

/-! ### Quantifier-parameterized `k`-variable syntax -/

/-- Formulas of a `k`-variable relational logic over `L` with single-variable quantifiers `Q`.
Variables are `Fin k`, and `quant q i φ` rebinds `xᵢ` inside its scope. -/
inductive GenFormula (Q : Type) (L : Language.{u, v}) (k : ℕ) : Type v
  /-- Falsity. -/
  | falsum : GenFormula Q L k
  /-- The equation `xᵢ = xⱼ`. -/
  | equal (i j : Fin k) : GenFormula Q L k
  /-- The relation `R` applied to the variables `x_{f 0}, …, x_{f (l - 1)}`. -/
  | rel {l : ℕ} (R : L.Relations l) (f : Fin l → Fin k) : GenFormula Q L k
  /-- Implication. -/
  | imp (φ ψ : GenFormula Q L k) : GenFormula Q L k
  /-- Quantification of `xᵢ` by `q : Q`. -/
  | quant (q : Q) (i : Fin k) (φ : GenFormula Q L k) : GenFormula Q L k

namespace GenFormula

variable {Q : Type} {L : Language.{u, v}} {k : ℕ}

/-- Negation. -/
def not (φ : GenFormula Q L k) : GenFormula Q L k :=
  imp φ falsum

/-- Existential quantification of the variable `xᵢ`. -/
def ex [ExQuantTag Q] (i : Fin k) (φ : GenFormula Q L k) : GenFormula Q L k :=
  quant ExQuantTag.exQuant i φ

/-- Universal quantification of the variable `xᵢ`, as `¬∃ xᵢ ¬φ`. -/
def all [ExQuantTag Q] (i : Fin k) (φ : GenFormula Q L k) : GenFormula Q L k :=
  (ex i φ.not).not

instance : Bot (GenFormula Q L k) :=
  ⟨falsum⟩

instance : Top (GenFormula Q L k) :=
  ⟨falsum.not⟩

instance : Min (GenFormula Q L k) :=
  ⟨fun φ ψ => (φ.imp ψ.not).not⟩

instance : Max (GenFormula Q L k) :=
  ⟨fun φ ψ => φ.not.imp ψ⟩

/-- The conjunction of a finite family of formulas. Like Mathlib's
`FirstOrder.Language.BoundedFormula.iInf`, it is defined through an arbitrary enumeration of the
index type, so only its truth, rank and free variables are determined. -/
noncomputable def iInf {β : Type*} [Finite β] (f : β → GenFormula Q L k) : GenFormula Q L k :=
  let _ := Fintype.ofFinite β
  ((Finset.univ : Finset β).toList.map f).foldr (· ⊓ ·) ⊤

/-- The disjunction of a finite family of formulas, as the negation of the conjunction of the
negations. -/
noncomputable def iSup {β : Type*} [Finite β] (f : β → GenFormula Q L k) : GenFormula Q L k :=
  (iInf fun b => (f b).not).not

/-- A property of formulas that holds of `⊤` and distributes over `⊓` holds of a finite
conjunction exactly when it holds of every conjunct. -/
private theorem apply_iInf_iff {β : Type*} [Finite β] {p : GenFormula Q L k → Prop}
    (hinf : ∀ φ ψ, p (φ ⊓ ψ) ↔ p φ ∧ p ψ) (htop : p ⊤) (f : β → GenFormula Q L k) :
    p (iInf f) ↔ ∀ b, p (f b) := by
  let := Fintype.ofFinite β
  exact List.apply_foldr_map_univ_toList_iff hinf htop f

/-! #### Semantics -/

/-- Truth of a formula in `M` under the assignment `a` of elements to the `k` variables. -/
def Realize {M : Type w} [L.Structure M] [Quantifier Q M] :
    GenFormula Q L k → (Fin k → M) → Prop
  | falsum, _ => False
  | equal i j, a => a i = a j
  | rel R f, a => RelMap R (a ∘ f)
  | imp φ ψ, a => φ.Realize a → ψ.Realize a
  | quant q i φ, a => Quantifier.eval q fun c : M => φ.Realize (Function.update a i c)

section Semantics

variable {M : Type w} [L.Structure M] [Quantifier Q M]

@[simp] theorem realize_falsum (a : Fin k → M) :
    (falsum : GenFormula Q L k).Realize a ↔ False := by
  rw [Realize]

@[simp] theorem realize_equal (i j : Fin k) (a : Fin k → M) :
    (equal i j : GenFormula Q L k).Realize a ↔ a i = a j := by
  rw [Realize]

@[simp] theorem realize_rel {l : ℕ} (R : L.Relations l) (f : Fin l → Fin k) (a : Fin k → M) :
    (rel R f : GenFormula Q L k).Realize a ↔ RelMap R (a ∘ f) := by
  rw [Realize]

@[simp] theorem realize_imp (φ ψ : GenFormula Q L k) (a : Fin k → M) :
    (imp φ ψ).Realize a ↔ (φ.Realize a → ψ.Realize a) := by
  rw [Realize]

@[simp] theorem realize_quant (q : Q) (i : Fin k) (φ : GenFormula Q L k) (a : Fin k → M) :
    (quant q i φ).Realize a ↔
      Quantifier.eval q fun c : M => φ.Realize (Function.update a i c) := by
  rw [Realize]

@[simp] theorem realize_not (φ : GenFormula Q L k) (a : Fin k → M) :
    φ.not.Realize a ↔ ¬φ.Realize a := by
  rw [not, realize_imp, realize_falsum]

@[simp] theorem realize_ex [ExQuantTag Q] [LawfulExQuant Q M]
    (i : Fin k) (φ : GenFormula Q L k) (a : Fin k → M) :
    (ex i φ).Realize a ↔ ∃ c : M, φ.Realize (Function.update a i c) :=
  (realize_quant _ i φ a).trans (LawfulExQuant.eval_exQuant _)

@[simp] theorem realize_all [ExQuantTag Q] [LawfulExQuant Q M]
    (i : Fin k) (φ : GenFormula Q L k) (a : Fin k → M) :
    (all i φ).Realize a ↔ ∀ c : M, φ.Realize (Function.update a i c) := by
  simp only [all, realize_not, realize_ex, not_exists, not_not]

@[simp] theorem realize_bot (a : Fin k → M) : (⊥ : GenFormula Q L k).Realize a ↔ False :=
  realize_falsum a

@[simp] theorem realize_top (a : Fin k → M) : (⊤ : GenFormula Q L k).Realize a ↔ True :=
  (realize_not _ a).trans (by simp only [realize_falsum, not_false_eq_true])

@[simp] theorem realize_inf (φ ψ : GenFormula Q L k) (a : Fin k → M) :
    (φ ⊓ ψ).Realize a ↔ φ.Realize a ∧ ψ.Realize a := by
  simp only [Min.min, realize_not, realize_imp, not_imp, not_not]

@[simp] theorem realize_sup (φ ψ : GenFormula Q L k) (a : Fin k → M) :
    (φ ⊔ ψ).Realize a ↔ φ.Realize a ∨ ψ.Realize a := by
  simp only [Max.max, realize_imp, realize_not, or_iff_not_imp_left]

@[simp] theorem realize_iInf {β : Type*} [Finite β] (f : β → GenFormula Q L k)
    (a : Fin k → M) : (iInf f).Realize a ↔ ∀ b, (f b).Realize a :=
  apply_iInf_iff (p := fun φ => φ.Realize a) (fun φ ψ => realize_inf φ ψ a)
    ((realize_top a).2 trivial) f

@[simp] theorem realize_iSup {β : Type*} [Finite β] (f : β → GenFormula Q L k)
    (a : Fin k → M) : (iSup f).Realize a ↔ ∃ b, (f b).Realize a := by
  simp only [iSup, realize_not, realize_iInf, not_forall, not_not]

end Semantics

/-! #### Quantifier rank -/

/-- The quantifier rank of a formula: the maximal nesting depth of its quantifiers. -/
def quantifierRank : GenFormula Q L k → ℕ
  | falsum => 0
  | equal _ _ => 0
  | rel _ _ => 0
  | imp φ ψ => max φ.quantifierRank ψ.quantifierRank
  | quant _ _ φ => φ.quantifierRank + 1

@[simp] theorem quantifierRank_falsum : (falsum : GenFormula Q L k).quantifierRank = 0 := by
  rw [quantifierRank]

@[simp] theorem quantifierRank_equal (i j : Fin k) :
    (equal i j : GenFormula Q L k).quantifierRank = 0 := by
  rw [quantifierRank]

@[simp] theorem quantifierRank_rel {l : ℕ} (R : L.Relations l) (f : Fin l → Fin k) :
    (rel R f : GenFormula Q L k).quantifierRank = 0 := by
  rw [quantifierRank]

@[simp] theorem quantifierRank_imp (φ ψ : GenFormula Q L k) :
    (imp φ ψ).quantifierRank = max φ.quantifierRank ψ.quantifierRank := by
  rw [quantifierRank]

@[simp] theorem quantifierRank_quant (q : Q) (i : Fin k) (φ : GenFormula Q L k) :
    (quant q i φ).quantifierRank = φ.quantifierRank + 1 := by
  rw [quantifierRank]

@[simp] theorem quantifierRank_not (φ : GenFormula Q L k) :
    φ.not.quantifierRank = φ.quantifierRank := by
  rw [not, quantifierRank_imp, quantifierRank_falsum, Nat.max_zero]

@[simp] theorem quantifierRank_ex [ExQuantTag Q] (i : Fin k) (φ : GenFormula Q L k) :
    (ex i φ).quantifierRank = φ.quantifierRank + 1 :=
  quantifierRank_quant _ i φ

@[simp] theorem quantifierRank_all [ExQuantTag Q] (i : Fin k) (φ : GenFormula Q L k) :
    (all i φ).quantifierRank = φ.quantifierRank + 1 := by
  simp only [all, quantifierRank_not, quantifierRank_ex]

@[simp] theorem quantifierRank_bot : (⊥ : GenFormula Q L k).quantifierRank = 0 :=
  quantifierRank_falsum

@[simp] theorem quantifierRank_top : (⊤ : GenFormula Q L k).quantifierRank = 0 :=
  (quantifierRank_not _).trans quantifierRank_falsum

@[simp] theorem quantifierRank_inf (φ ψ : GenFormula Q L k) :
    (φ ⊓ ψ).quantifierRank = max φ.quantifierRank ψ.quantifierRank := by
  simp only [Min.min, quantifierRank_not, quantifierRank_imp]

@[simp] theorem quantifierRank_sup (φ ψ : GenFormula Q L k) :
    (φ ⊔ ψ).quantifierRank = max φ.quantifierRank ψ.quantifierRank := by
  simp only [Max.max, quantifierRank_imp, quantifierRank_not]

/-- A finite conjunction has quantifier rank at most `m` when each conjunct does. -/
theorem quantifierRank_iInf_le {β : Type*} [Finite β] {f : β → GenFormula Q L k} {m : ℕ}
    (h : ∀ b, (f b).quantifierRank ≤ m) : (iInf f).quantifierRank ≤ m :=
  (apply_iInf_iff (p := fun φ => φ.quantifierRank ≤ m)
    (fun φ ψ => by rw [quantifierRank_inf, max_le_iff])
    (quantifierRank_top.trans_le (Nat.zero_le m)) f).2 h

/-- A finite disjunction has quantifier rank at most `m` when each disjunct does. -/
theorem quantifierRank_iSup_le {β : Type*} [Finite β] {f : β → GenFormula Q L k} {m : ℕ}
    (h : ∀ b, (f b).quantifierRank ≤ m) : (iSup f).quantifierRank ≤ m := by
  rw [iSup, quantifierRank_not]
  exact quantifierRank_iInf_le fun b => (quantifierRank_not _).trans_le (h b)

/-! #### Free variables -/

/-- The free variables of a formula. -/
def freeVars : GenFormula Q L k → Finset (Fin k)
  | falsum => ∅
  | equal i j => {i, j}
  | rel _ f => Finset.univ.image f
  | imp φ ψ => φ.freeVars ∪ ψ.freeVars
  | quant _ i φ => φ.freeVars.erase i

@[simp] theorem freeVars_falsum : (falsum : GenFormula Q L k).freeVars = ∅ := by
  rw [freeVars]

@[simp] theorem freeVars_equal (i j : Fin k) :
    (equal i j : GenFormula Q L k).freeVars = {i, j} := by
  rw [freeVars]

@[simp] theorem freeVars_rel {l : ℕ} (R : L.Relations l) (f : Fin l → Fin k) :
    (rel R f : GenFormula Q L k).freeVars = Finset.univ.image f := by
  rw [freeVars]

@[simp] theorem freeVars_imp (φ ψ : GenFormula Q L k) :
    (imp φ ψ).freeVars = φ.freeVars ∪ ψ.freeVars := by
  rw [freeVars]

@[simp] theorem freeVars_quant (q : Q) (i : Fin k) (φ : GenFormula Q L k) :
    (quant q i φ).freeVars = φ.freeVars.erase i := by
  rw [freeVars]

@[simp] theorem freeVars_not (φ : GenFormula Q L k) : φ.not.freeVars = φ.freeVars := by
  rw [not, freeVars_imp, freeVars_falsum, Finset.union_empty]

@[simp] theorem freeVars_ex [ExQuantTag Q] (i : Fin k) (φ : GenFormula Q L k) :
    (ex i φ).freeVars = φ.freeVars.erase i :=
  freeVars_quant _ i φ

@[simp] theorem freeVars_all [ExQuantTag Q] (i : Fin k) (φ : GenFormula Q L k) :
    (all i φ).freeVars = φ.freeVars.erase i := by
  simp only [all, freeVars_not, freeVars_ex]

@[simp] theorem freeVars_bot : (⊥ : GenFormula Q L k).freeVars = ∅ :=
  freeVars_falsum

@[simp] theorem freeVars_top : (⊤ : GenFormula Q L k).freeVars = ∅ :=
  (freeVars_not _).trans freeVars_falsum

@[simp] theorem freeVars_inf (φ ψ : GenFormula Q L k) :
    (φ ⊓ ψ).freeVars = φ.freeVars ∪ ψ.freeVars := by
  simp only [Min.min, freeVars_not, freeVars_imp]

@[simp] theorem freeVars_sup (φ ψ : GenFormula Q L k) :
    (φ ⊔ ψ).freeVars = φ.freeVars ∪ ψ.freeVars := by
  simp only [Max.max, freeVars_imp, freeVars_not]

/-- The free variables of a finite conjunction lie in `S` when those of each conjunct do. -/
theorem freeVars_iInf_subset {β : Type*} [Finite β] {f : β → GenFormula Q L k} {S : Set (Fin k)}
    (h : ∀ b, ↑(f b).freeVars ⊆ S) : ↑(iInf f).freeVars ⊆ S :=
  (apply_iInf_iff (p := fun φ => ↑φ.freeVars ⊆ S)
    (fun φ ψ => by rw [freeVars_inf, Finset.coe_union, Set.union_subset_iff])
    (by rw [freeVars_top, Finset.coe_empty]; exact Set.empty_subset S) f).2 h

/-- The free variables of a finite disjunction lie in `S` when those of each disjunct do. -/
theorem freeVars_iSup_subset {β : Type*} [Finite β] {f : β → GenFormula Q L k} {S : Set (Fin k)}
    (h : ∀ b, ↑(f b).freeVars ⊆ S) : ↑(iSup f).freeVars ⊆ S := by
  rw [iSup, freeVars_not]
  exact freeVars_iInf_subset fun b => (freeVars_not (f b)).symm ▸ h b

/-- The truth of a formula depends only on the values of its free variables. -/
theorem realize_congr {M : Type w} [L.Structure M] [Quantifier Q M] {φ : GenFormula Q L k}
    {a a' : Fin k → M} (h : ∀ i ∈ φ.freeVars, a i = a' i) :
    φ.Realize a ↔ φ.Realize a' := by
  induction φ generalizing a a' with
  | falsum => exact Iff.rfl
  | equal i j => simp_all
  | rel R f => simp [show a ∘ f = a' ∘ f from funext fun _ => h _ (by simp)]
  | imp φ ψ ihφ ihψ =>
    exact imp_congr (ihφ fun i hi => h i (Finset.mem_union_left _ hi))
      (ihψ fun i hi => h i (Finset.mem_union_right _ hi))
  | quant q i φ ih =>
    refine Quantifier.eval_congr q fun c => ih fun j hj => ?_
    by_cases hji : j = i
    · simp [hji]
    · simp [hji, h j (Finset.mem_erase.mpr ⟨hji, hj⟩)]

end GenFormula

/-! ### `FO^k`: finite-variable first-order logic -/

/-- The single existential quantifier tag of `FO^k` and `L^k_{∞ω}`. -/
inductive ExistentialQuant : Type
  /-- Existential quantification `∃`. -/
  | ex : ExistentialQuant

instance {M : Type w} : Quantifier ExistentialQuant M where
  eval _ p := ∃ c, p c
  eval_congr _ {_ _} h := exists_congr h

@[simp] theorem ExistentialQuant.eval_ex {M : Type w} (p : M → Prop) :
    Quantifier.eval ExistentialQuant.ex p ↔ ∃ c, p c :=
  Iff.rfl

instance : ExQuantTag ExistentialQuant where
  exQuant := .ex

instance {M : Type w} : LawfulExQuant ExistentialQuant M where
  eval_exQuant _ := Iff.rfl

/-- Formulas of the `k`-variable fragment `FO^k` over the relation symbols of `L`. The variables
are `Fin k`, and `ex i φ` / `all i φ` quantify the variable `i`, which may already be bound or free
in an enclosing formula. -/
abbrev Formula (L : Language.{u, v}) (k : ℕ) : Type v :=
  GenFormula ExistentialQuant L k

namespace Formula

/-! #### Translation of `FO^k` to Mathlib's first-order formulas -/

variable {L : Language.{u, v}} {k : ℕ} {M : Type w} [L.Structure M]

/-- The translation of a formula of `FO^k` into Mathlib's `L.Formula (Fin k)`: the variable `i`
becomes the free variable `i`, and `ex i φ` quantifies over a fresh bound variable which replaces
`i` in the translation of `φ`. -/
def toFormula : Formula L k → L.Formula (Fin k)
  | .falsum => ⊥
  | .equal i j => Term.equal (.var i) (.var j)
  | .rel R f => R.formula fun t => .var (f t)
  | .imp φ ψ => (toFormula φ).imp (toFormula ψ)
  | .quant .ex i φ =>
    (BoundedFormula.relabel (fun j : Fin k => if j = i then (Sum.inr 0 : Fin k ⊕ Fin 1) else
      Sum.inl j) (toFormula φ) : L.BoundedFormula (Fin k) 1).ex

private theorem toFormula_ex_assignment (i : Fin k) (a : Fin k → M) (c : M) :
    Sum.elim a (((Fin.snoc (default : Fin 0 → M) c : Fin 1 → M)) ∘ Fin.castAdd 0) ∘
        (fun j : Fin k => if j = i then (Sum.inr 0 : Fin k ⊕ Fin 1) else Sum.inl j) =
      Function.update a i c := by
  funext j
  by_cases hj : j = i
  · simp only [hj, Function.comp_apply, ↓reduceIte, Sum.elim_inr, Function.update_self]
    rfl
  · simp [hj]

/-- The translation of a formula holds of an assignment exactly when the formula does. -/
@[simp] theorem realize_toFormula (φ : Formula L k) (a : Fin k → M) :
    (toFormula φ).Realize a ↔ φ.Realize a := by
  induction φ generalizing a with
  | falsum => simp [toFormula]
  | equal i j => simp [toFormula]
  | rel R f => simp [toFormula]; rfl
  | imp φ ψ ihφ ihψ => simp [toFormula, ihφ, ihψ]
  | quant q i φ ih =>
    cases q
    rw [GenFormula.realize_quant, ExistentialQuant.eval_ex, toFormula, Language.Formula.Realize,
      BoundedFormula.realize_ex]
    refine exists_congr fun c => ?_
    rw [BoundedFormula.realize_relabel, toFormula_ex_assignment, ← ih]
    exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))

/-- The translation preserves quantifier rank. -/
@[simp] theorem quantifierRank_toFormula (φ : Formula L k) :
    FO.quantifierRank (toFormula φ) = φ.quantifierRank := by
  induction φ with
  | falsum => simp [toFormula]
  | equal i j => simp [toFormula, Term.equal]
  | rel R f => simp [toFormula, Relations.formula, FO.quantifierRank_relations_boundedFormula]
  | imp φ ψ ihφ ihψ => simp [toFormula, ihφ, ihψ]
  | quant q i φ ih =>
    cases q
    simp [toFormula, ih]

end Formula

end Cslib.Logic.FO.FiniteVariable
