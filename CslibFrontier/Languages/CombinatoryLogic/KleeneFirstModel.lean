/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Languages.CombinatoryLogic.PartialCombinatoryAlgebra
public import Mathlib.Computability.PartrecCode

/-!
# Kleene's first model

Kleene's first model `K₁` is the partial combinatory algebra on `ℕ` in which `e ⬝ n` is the value
of the `e`-th partial recursive function at `n`: with Mathlib's numbering of codes,
`e ⬝ n = (ofNat Nat.Partrec.Code e).eval n`.

Its combinators come from two facts about the numbering. The s-m-n theorem gives indices that
specialize the first of two paired arguments, and specialization is itself computable. The
universal function `(e, n) ↦ eₙ` is partial recursive. `PartialCombinatoryAlgebra.ofSmn` builds a
pca from these two facts for any numbering of partial functions on `ℕ`, so that relativized
versions of `K₁` reuse the construction. In it, `k` specializes the first projection, so
`k ⬝ a` is an index of `b ↦ a`; and `s ⬝ a ⬝ b` is an index of `c ↦ (a ⬝ c) ⬝ (b ⬝ c)`, obtained
by specializing a universal program twice.

## Main definitions

* `Cslib.PartialCombinatoryAlgebra.ofSmn`: the pca on `ℕ` given by a numbering with a computable
  s-m-n operation and a universal index.
* `Cslib.PartialCombinatoryAlgebra.kleeneOne`: Kleene's first model `K₁`.

## Main results

* `Cslib.PartialCombinatoryAlgebra.kleeneOne_app`: application in `K₁` is evaluation of codes.

## References

* [J. van Oosten, *Realizability: An Introduction to its Categorical Side*][vanOosten2008],
  Chapter 1 (Kleene's first model `K₁`; the section number is to be checked).
* [S. C. Kleene, *Introduction to Metamathematics*][Kleene1952], §65 (the s-m-n theorem).
-/

public section

open Encodable Denumerable

namespace Cslib.PartialCombinatoryAlgebra

/-- The pca on `ℕ` given by a numbering `φ` of partial functions with a computable s-m-n operation
and a universal index:

* `curry e m` is an index of `n ↦ φ e ⟨m, n⟩`;
* `lift e` is an index of `m ↦ curry e m`;
* `fst` is an index of the first projection `⟨a, b⟩ ↦ a`;
* `u` is an index of `⟨⟨a, b⟩, c⟩ ↦ (φ a c) ⬝ (φ b c)`, applying the value of `a` at `c` to that
  of `b` at `c`.

Its combinators are `k = lift fst` and `s = lift (lift u)`. -/
@[expose] def ofSmn (φ : ℕ → ℕ → Part ℕ) (curry : ℕ → ℕ → ℕ) (lift : ℕ → ℕ) (fst u : ℕ)
    (eval_curry : ∀ e m n, φ (curry e m) n = φ e (Nat.pair m n))
    (eval_lift : ∀ e m, φ (lift e) m = Part.some (curry e m))
    (eval_fst : ∀ a b, φ fst (Nat.pair a b) = Part.some a)
    (eval_u : ∀ a b c, φ u (Nat.pair (Nat.pair a b) c) = ap φ (φ a c) (φ b c)) :
    PartialCombinatoryAlgebra ℕ where
  app := φ
  k := lift fst
  s := lift (lift u)
  ap_ap_k a b := by rw [eval_lift, ap_some_some, eval_curry, eval_fst]
  dom_ap_s a b := by simp only [eval_lift, ap_some_some, eval_curry, Part.some_dom]
  ap_ap_ap_s a b c := by
    rw [eval_lift, ap_some_some, eval_curry, eval_lift, ap_some_some, eval_curry, eval_u]

open Nat.Partrec Nat.Partrec.Code

/-- Specialization of Mathlib codes is computable in the parameter: for each index `e` there is an
index of `m ↦ encode (curry e m)`. -/
private theorem exists_lift :
    ∃ lift : ℕ → ℕ, ∀ e m,
      (ofNat Code (lift e)).eval m = Part.some (encode (curry (ofNat Code e) m)) := by
  have h : ∀ e, ∃ c : Code, c.eval = fun m => Part.some (encode (curry (ofNat Code e) m)) :=
    fun e => exists_code.1 (Partrec.nat_iff.1
      (Primrec.encode.comp (primrec₂_curry.comp (Primrec.const _) Primrec.id)).to_comp.partrec)
  choose c hc using h
  exact ⟨fun e => encode (c e), fun e m => by simp [hc]⟩

/-- A universal Mathlib code: on `⟨⟨a, b⟩, c⟩` it applies the value of the `a`-th function at `c`
to that of the `b`-th function at `c`. -/
private theorem exists_univ :
    ∃ u : ℕ, ∀ a b c, (ofNat Code u).eval (Nat.pair (Nat.pair a b) c) =
      ap (fun e => (ofNat Code e).eval) ((ofNat Code a).eval c) ((ofNat Code b).eval c) := by
  have hE : Partrec₂ fun e n : ℕ => (ofNat Code e).eval n :=
    eval_part.comp ((Primrec.ofNat Code).to_comp.comp Computable.fst) Computable.snd
  have hunpair : Computable Nat.unpair := Primrec.unpair.to_comp
  have ha : Computable fun x : ℕ => x.unpair.1.unpair.1 :=
    Computable.fst.comp (hunpair.comp (Computable.fst.comp hunpair))
  have hb : Computable fun x : ℕ => x.unpair.1.unpair.2 :=
    Computable.snd.comp (hunpair.comp (Computable.fst.comp hunpair))
  have hc : Computable fun x : ℕ => x.unpair.2 := Computable.snd.comp hunpair
  have hF : Partrec fun x : ℕ =>
      ap (fun e => (ofNat Code e).eval) ((ofNat Code x.unpair.1.unpair.1).eval x.unpair.2)
        ((ofNat Code x.unpair.1.unpair.2).eval x.unpair.2) :=
    (hE.comp ha hc).bind <| (hE.comp (hb.comp Computable.fst) (hc.comp Computable.fst)).bind <|
      hE.comp (Computable.snd.comp Computable.fst) Computable.snd
  obtain ⟨c, hc⟩ := exists_code.1 (Partrec.nat_iff.1 hF)
  exact ⟨encode c, fun a b c => by simp [hc]⟩

/-- **Kleene's first model** `K₁`: the pca on `ℕ` in which `e ⬝ n` is the value of the `e`-th
partial recursive function, in Mathlib's numbering of `Nat.Partrec.Code`, at `n`. -/
noncomputable def kleeneOne : PartialCombinatoryAlgebra ℕ :=
  ofSmn (fun e => (ofNat Code e).eval) (fun e m => encode (curry (ofNat Code e) m))
    (Classical.choose exists_lift) (encode Code.left) (Classical.choose exists_univ)
    (fun e m n => by simp [eval_curry]) (Classical.choose_spec exists_lift)
    (fun a b => by simp [Code.eval]) (Classical.choose_spec exists_univ)

/-- Application in `K₁` is evaluation of the code with the given index. -/
@[simp]
theorem kleeneOne_app (e n : ℕ) : kleeneOne.app e n = (ofNat Code e).eval n := by
  unfold kleeneOne
  rfl

end Cslib.PartialCombinatoryAlgebra
