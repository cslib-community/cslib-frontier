/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Part

/-!
# Partial combinatory algebras

A *partial combinatory algebra* (pca) is a set `A` with a partial binary application, written
`a ⬝ b`, and two elements `k` and `s` such that, for all `a`, `b` and `c`,
`k ⬝ a ⬝ b = a`, `s ⬝ a ⬝ b` is defined, and `s ⬝ a ⬝ b ⬝ c ≃ (a ⬝ c) ⬝ (b ⬝ c)`, where `≃` is
Kleene equality: one side is defined exactly when the other is, and then they are equal.
Application associates to the left, and an application is defined only when its two arguments are.
Pcas are the models of realizability: Kleene's first model on the natural numbers (indices of
partial recursive functions) and his second model on Baire space are the standard examples.

Application is a function `A → A → Part A`, and Kleene equality is equality in `Part A`. The
application of two partial values, `ap app x y`, is defined when `x` and `y` are and `app` is
defined at their values.

The main property is *combinatory completeness*: every term built from variables, constants and
application can be abstracted over its last variable. `PartialCombinatoryAlgebra.abs` is the
bracket abstraction, and `PartialCombinatoryAlgebra.dom_eval_abs` and
`PartialCombinatoryAlgebra.ap_eval_abs` say that the abstraction always denotes, and that applying
it to `a` evaluates the term with `a` in place of the last variable.

## Main definitions

* `Cslib.PartialCombinatoryAlgebra`: a carrier's partial application with combinators `k`, `s`.
* `Cslib.PartialCombinatoryAlgebra.ap`: application of partial values.
* `Cslib.PartialCombinatoryAlgebra.i`: the identity combinator, the value of `s ⬝ k ⬝ k`.
* `Cslib.PartialCombinatoryAlgebra.Term`, `Cslib.PartialCombinatoryAlgebra.eval`: terms with
  variables in `Fin n` and constants in the carrier, and their partial values.
* `Cslib.PartialCombinatoryAlgebra.abs`: bracket abstraction of the last variable.
* `Cslib.PartialCombinatoryAlgebra.sub`: the sub-pca on a subset containing `k` and `s` and closed
  under application.

## Main results

* `Cslib.PartialCombinatoryAlgebra.app_i`: `i ⬝ a = a`.
* `Cslib.PartialCombinatoryAlgebra.dom_eval_abs`, `Cslib.PartialCombinatoryAlgebra.ap_eval_abs`:
  combinatory completeness.

## Implementation notes

A pca is a `structure` on its carrier rather than a class, because realizability uses many pcas
on one carrier: Kleene's first model relative to each oracle lives on `ℕ`, and sub-pcas share the
application of the ambient pca. The axioms follow the definition in [vanOosten2008], Chapter 1,
§1.1, which (unlike some sources) does not require `k ≠ s`.

`Cslib.SKI.Polynomial.toSKI` in cslib is bracket abstraction for the closed SKI calculus. It
cannot be used here: a pca's terms have constants from the carrier, and its abstraction theorem
is a Kleene equality, in which definedness of either side gives definedness of the other, rather
than a reduction.

## References

* [J. van Oosten, *Realizability: An Introduction to its Categorical Side*][vanOosten2008],
  Chapter 1, §1.1 (the definition of a pca, and combinatory completeness; the numbers of the
  definition and theorem are to be checked).
-/

public section

namespace Cslib

namespace PartialCombinatoryAlgebra

variable {A : Type*}

/-- Application of partial values: `ap app x y` is defined when `x` and `y` are defined, with
values `a` and `b`, and `app a b` is defined; its value is then that of `app a b`. -/
@[expose] def ap (app : A → A → Part A) (x y : Part A) : Part A :=
  x.bind fun a => y.bind (app a)

@[simp]
theorem ap_some_some (app : A → A → Part A) (a b : A) :
    ap app (Part.some a) (Part.some b) = app a b := by
  simp [ap]

/-- Applying the value of a defined partial value `x` is applying `x`. -/
theorem app_get_eq_ap (app : A → A → Part A) {x : Part A} (h : x.Dom) (b : A) :
    app (x.get h) b = ap app x (Part.some b) := by
  conv_rhs => rw [← Part.some_get h, ap_some_some]

end PartialCombinatoryAlgebra

open PartialCombinatoryAlgebra in
/-- A partial combinatory algebra on the carrier `A`: a partial application `app` with
combinators `k` and `s` satisfying `k ⬝ a ⬝ b = a`, `s ⬝ a ⬝ b` defined and
`s ⬝ a ⬝ b ⬝ c ≃ (a ⬝ c) ⬝ (b ⬝ c)` ([vanOosten2008], §1.1). -/
structure PartialCombinatoryAlgebra (A : Type*) where
  /-- Partial application. -/
  app : A → A → Part A
  /-- The combinator `k`. -/
  k : A
  /-- The combinator `s`. -/
  s : A
  /-- `k ⬝ a ⬝ b = a`. -/
  ap_ap_k (a b : A) : ap app (app k a) (Part.some b) = Part.some a
  /-- `s ⬝ a ⬝ b` is defined. -/
  dom_ap_s (a b : A) : (ap app (app s a) (Part.some b)).Dom
  /-- `s ⬝ a ⬝ b ⬝ c ≃ (a ⬝ c) ⬝ (b ⬝ c)`. -/
  ap_ap_ap_s (a b c : A) :
    ap app (ap app (app s a) (Part.some b)) (Part.some c) = ap app (app a c) (app b c)

namespace PartialCombinatoryAlgebra

variable {A : Type*} (P : PartialCombinatoryAlgebra A)

/-- `k ⬝ a` is defined. -/
theorem dom_app_k (a : A) : (P.app P.k a).Dom := by
  have h := congrArg Part.Dom (P.ap_ap_k a a)
  simp only [ap, Part.some_dom, eq_iff_iff, iff_true, Part.bind_dom] at h
  exact h.1

/-- The identity combinator `i`, the value of `s ⬝ k ⬝ k`. -/
noncomputable def i : A :=
  (ap P.app (P.app P.s P.k) (Part.some P.k)).get (P.dom_ap_s P.k P.k)

/-- `i ⬝ a = a`. -/
@[simp]
theorem app_i (a : A) : P.app P.i a = Part.some a := by
  rw [i, app_get_eq_ap P.app, P.ap_ap_ap_s, ← Part.some_get (P.dom_app_k a), ap_some_some,
    app_get_eq_ap P.app, P.ap_ap_k]

/-- Terms over the carrier `A` with variables in `Fin n`: variables, constants and application. -/
inductive Term (A : Type*) (n : ℕ) : Type _
  /-- The variable `xᵢ`. -/
  | var : Fin n → Term A n
  /-- A constant of the carrier. -/
  | const : A → Term A n
  /-- Application of terms. -/
  | app : Term A n → Term A n → Term A n

/-- The partial value of a term when the variables take the values `ρ`. -/
@[expose] def eval {n : ℕ} : Term A n → (Fin n → A) → Part A
  | .var j, ρ => Part.some (ρ j)
  | .const a, _ => Part.some a
  | .app t u, ρ => ap P.app (eval t ρ) (eval u ρ)

/-- Bracket abstraction of the last variable `xₙ` of a term: `xₙ` becomes `i`, another variable
or a constant `t` becomes `k ⬝ t`, and an application `t ⬝ u` becomes `s ⬝ ⟨xₙ⟩t ⬝ ⟨xₙ⟩u`. -/
noncomputable def abs {n : ℕ} : Term A (n + 1) → Term A n
  | .var j => Fin.lastCases (.const P.i) (fun j => .app (.const P.k) (.var j)) j
  | .const a => .app (.const P.k) (.const a)
  | .app t u => .app (.app (.const P.s) (abs t)) (abs u)

/-- The abstracted term carries the value of the original one once applied: the combined
statement behind `dom_eval_abs` and `ap_eval_abs`. -/
private theorem eval_abs {n : ℕ} (t : Term A (n + 1)) (ρ : Fin n → A) :
    ∃ f, P.eval (P.abs t) ρ = Part.some f ∧
      ∀ a, P.app f a = P.eval t (Fin.snoc ρ a) := by
  induction t with
  | var j =>
    induction j using Fin.lastCases with
    | last => exact ⟨P.i, by simp [abs, eval]⟩
    | cast j =>
      refine ⟨(P.app P.k (ρ j)).get (P.dom_app_k _), by simp [abs, eval], fun a => ?_⟩
      rw [app_get_eq_ap P.app, P.ap_ap_k]
      simp [eval]
  | const c =>
    refine ⟨(P.app P.k c).get (P.dom_app_k _), by simp [abs, eval], fun a => ?_⟩
    rw [app_get_eq_ap P.app, P.ap_ap_k]
    rfl
  | app t u iht ihu =>
    obtain ⟨f, hf, hfa⟩ := iht
    obtain ⟨g, hg, hga⟩ := ihu
    refine ⟨(ap P.app (P.app P.s f) (Part.some g)).get (P.dom_ap_s f g),
      by simp [abs, eval, hf, hg], fun a => ?_⟩
    rw [app_get_eq_ap P.app, P.ap_ap_ap_s, hfa, hga]
    rfl

/-- **Combinatory completeness**, definedness: the bracket abstraction of a term always has a
value ([vanOosten2008], §1.1). -/
theorem dom_eval_abs {n : ℕ} (t : Term A (n + 1)) (ρ : Fin n → A) :
    (P.eval (P.abs t) ρ).Dom := by
  obtain ⟨_, hf, _⟩ := P.eval_abs t ρ
  simp [hf]

/-- **Combinatory completeness**: applying the bracket abstraction `⟨xₙ⟩t` of a term to `a` is
Kleene equal to evaluating `t` with `a` for its last variable ([vanOosten2008], §1.1). -/
theorem ap_eval_abs {n : ℕ} (t : Term A (n + 1)) (ρ : Fin n → A) (a : A) :
    ap P.app (P.eval (P.abs t) ρ) (Part.some a) = P.eval t (Fin.snoc ρ a) := by
  obtain ⟨_, hf, hfa⟩ := P.eval_abs t ρ
  rw [hf, ap_some_some, hfa]


/-! ### Sub-pcas -/

section Sub

variable (S : A → Prop) (hk : S P.k) (hs : S P.s)
  (happ : ∀ a b c, S a → S b → c ∈ P.app a b → S c)

/-- Application restricted to the elements satisfying `S`, for `S` closed under application. -/
private def subApp (a b : Subtype S) : Part (Subtype S) :=
  ⟨(P.app a b).Dom, fun h => ⟨(P.app a b).get h, happ _ _ _ a.property b.property (Part.get_mem h)⟩⟩

private theorem map_val_subApp (a b : Subtype S) :
    (subApp P S happ a b).map Subtype.val = P.app a b :=
  rfl

private theorem map_val_injective {x y : Part (Subtype S)}
    (h : x.map Subtype.val = y.map Subtype.val) : x = y :=
  Part.ext fun c => by
    have := congrArg (c.val ∈ ·) h
    simpa [Part.mem_map_iff, Subtype.val_inj] using this

private theorem map_val_ap (x y : Part (Subtype S)) :
    (ap (subApp P S happ) x y).map Subtype.val =
      ap P.app (x.map Subtype.val) (y.map Subtype.val) := by
  simp only [ap, Part.map_bind, Part.bind_map, map_val_subApp]

/-- The sub-pca of `P` on the elements satisfying `S`, when `S` contains `k` and `s` and is closed
under application. Its application is that of `P` (`map_val_sub_app`). -/
def sub : PartialCombinatoryAlgebra (Subtype S) where
  app := subApp P S happ
  k := ⟨P.k, hk⟩
  s := ⟨P.s, hs⟩
  ap_ap_k a b := map_val_injective S <| by
    simp only [map_val_ap, map_val_subApp, Part.map_some, P.ap_ap_k]
  dom_ap_s a b := by
    have h : ((ap (subApp P S happ) (subApp P S happ ⟨P.s, hs⟩ a) (Part.some b)).map
        Subtype.val).Dom := by
      simp only [map_val_ap, map_val_subApp, Part.map_some]
      exact P.dom_ap_s a b
    exact h
  ap_ap_ap_s a b c := map_val_injective S <| by
    simp only [map_val_ap, map_val_subApp, Part.map_some, P.ap_ap_ap_s]

/-- Application in a sub-pca is application in the ambient pca. -/
@[simp]
theorem map_val_sub_app (a b : Subtype S) :
    ((P.sub S hk hs happ).app a b).map Subtype.val = P.app a b :=
  map_val_subApp P S happ a b

end Sub

end PartialCombinatoryAlgebra

end Cslib
