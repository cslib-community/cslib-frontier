/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Computability.RecursiveInSmn
public import CslibFrontier.Foundations.Computability.RecursiveInUniversal
public import CslibFrontier.Languages.CombinatoryLogic.KleeneFirstModel

/-!
# Kleene's first model relative to an oracle

For a total oracle `f : ℕ → ℕ`, the pca `K₁ᶠ` on `ℕ` applies `e` to `n` by evaluating the oracle
code with index `e` at `n` relative to `f`: `e ⬝ n = eval f (ofNat Nat.RecursiveIn.Code e) n`.
It is built by `PartialCombinatoryAlgebra.ofSmn` from the oracle-uniform s-m-n theorem
(`Nat.RecursiveIn.Code.curry`) and the universal oracle code
(`Nat.RecursiveIn.Code.exists_universal`).

The combinators do not depend on the oracle (`kleeneOneRel_k`, `kleeneOneRel_s`): `k` and `s` are
indices of oracle codes that run the same program against every oracle, so a realizer built from
them in `K₁ᶠ` is the same number for every `f`.

## Main definitions

* `Cslib.PartialCombinatoryAlgebra.kleeneOneRel`: Kleene's first model relative to a total oracle.

## Main results

* `Cslib.PartialCombinatoryAlgebra.kleeneOneRel_app`: application is evaluation of oracle codes.
* `Cslib.PartialCombinatoryAlgebra.kleeneOneRel_k`,
  `Cslib.PartialCombinatoryAlgebra.kleeneOneRel_s`: the combinators are the same for all oracles.

## Implementation notes

The oracle is total because the universal code `Nat.RecursiveIn.Code.exists_universal` is proved
only for total oracles; a universal code for partial oracles is part of #6829. Mathlib's
numbering of `Nat.Partrec.Code` and the numbering of `Nat.RecursiveIn.Code` differ (the latter has
the extra atomic code `oracle`), so `K₁ = kleeneOne` is not literally `K₁ᶠ` for a computable `f`.

## References

* [J. van Oosten, *Realizability: An Introduction to its Categorical Side*][vanOosten2008],
  Chapter 1 (relativized Kleene's first model; the section number is to be checked).
-/

public section

open Encodable Denumerable Nat.RecursiveIn Nat.RecursiveIn.Code

namespace Cslib.PartialCombinatoryAlgebra

/-- Specialization of oracle codes is computable in the parameter, uniformly in the oracle: for
each index `e` there is an index of `m ↦ encode (curry e m)` relative to every oracle. -/
private theorem exists_liftRel :
    ∃ lift : ℕ → ℕ, ∀ (f : ℕ → ℕ) e m,
      Code.eval (f : ℕ →. ℕ) (ofNat Code (lift e)) m =
        Part.some (encode (curry (ofNat Code e) m)) := by
  have h : ∀ e, ∃ c : Code, ∀ f : ℕ → ℕ,
      Code.eval (f : ℕ →. ℕ) c = fun m => Part.some (encode (curry (ofNat Code e) m)) :=
    fun e => HasUniformCode.of_computable
      (Primrec.encode.comp (primrec₂_curry.comp (Primrec.const _) Primrec.id)).to_comp
  choose c hc using h
  exact ⟨fun e => encode (c e), fun f e m => by simp [hc]⟩

/-- An oracle code that, relative to every total oracle, applies the value of the `a`-th function
at `c` to that of the `b`-th function at `c`, on input `⟨⟨a, b⟩, c⟩`. -/
private theorem exists_univRel :
    ∃ u : ℕ, ∀ (f : ℕ → ℕ) a b c,
      Code.eval (f : ℕ →. ℕ) (ofNat Code u) (Nat.pair (Nat.pair a b) c) =
        ap (fun e => Code.eval (f : ℕ →. ℕ) (ofNat Code e))
          (Code.eval (f : ℕ →. ℕ) (ofNat Code a) c) (Code.eval (f : ℕ →. ℕ) (ofNat Code b) c) := by
  obtain ⟨U, hU⟩ := exists_universal
  have hUc : HasUniformCode (fun f : ℕ → ℕ => (f : ℕ →. ℕ)) fun f p =>
      Code.eval (f : ℕ →. ℕ) (ofNat Code p.unpair.1) p.unpair.2 :=
    ⟨U, fun f => funext fun p => by
      have h := hU f p.unpair.1 p.unpair.2
      rwa [Nat.pair_unpair] at h⟩
  have hproj {g : ℕ → ℕ} (hg : Primrec g) :
      HasUniformCode (fun f : ℕ → ℕ => (f : ℕ →. ℕ)) fun _ x => Part.some (g x) :=
    HasUniformCode.of_computable hg.to_comp
  have ha := hproj (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
  have hb := hproj (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
  have hc := hproj (Primrec.snd.comp Primrec.unpair)
  obtain ⟨u, hu⟩ := (hUc.comp ((hUc.comp (ha.pair hc)).pair (hUc.comp (hb.pair hc))))
  refine ⟨encode u, fun f a b c => ?_⟩
  rw [ofNat_encode, hu f]
  simp [Seq.seq, ap, Part.bind_assoc]

/-- **Kleene's first model relative to the total oracle `f`**: the pca on `ℕ` in which `e ⬝ n` is
the value at `n` of the oracle code with index `e`, evaluated relative to `f`. -/
noncomputable def kleeneOneRel (f : ℕ → ℕ) : PartialCombinatoryAlgebra ℕ :=
  ofSmn (fun e => Code.eval (f : ℕ →. ℕ) (ofNat Code e))
    (fun e m => encode (curry (ofNat Code e) m))
    (Classical.choose exists_liftRel) (encode Code.left) (Classical.choose exists_univRel)
    (fun e m n => by simp) (Classical.choose_spec exists_liftRel f)
    (fun a b => by simp [Code.eval]) (Classical.choose_spec exists_univRel f)

/-- Application in `K₁ᶠ` is evaluation of oracle codes relative to `f`. -/
@[simp]
theorem kleeneOneRel_app (f : ℕ → ℕ) (e n : ℕ) :
    (kleeneOneRel f).app e n = Code.eval (f : ℕ →. ℕ) (ofNat Code e) n := by
  unfold kleeneOneRel
  rfl

/-- The combinator `k` of `K₁ᶠ` does not depend on the oracle. -/
theorem kleeneOneRel_k (f g : ℕ → ℕ) : (kleeneOneRel f).k = (kleeneOneRel g).k := by
  unfold kleeneOneRel
  rfl

/-- The combinator `s` of `K₁ᶠ` does not depend on the oracle. -/
theorem kleeneOneRel_s (f g : ℕ → ℕ) : (kleeneOneRel f).s = (kleeneOneRel g).s := by
  unfold kleeneOneRel
  rfl

end Cslib.PartialCombinatoryAlgebra
