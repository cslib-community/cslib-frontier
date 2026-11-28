/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cuts.Play
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Contraction of tables with code words

Roles are joined by channels; a channel has two ends (`h ν false`, `h ν true`), as the units of
the play have two holders (`Play.Holds`). Every role has a table `G p i g` that depends on an
index `i` and on data `g ν : S i ν` on each of its channels. Suppose the data on a channel,
together with the index, are written as a *code word* in a common alphabet `Z`, injectively. Then
a role can be given the code words of its channels instead (`Cut.codeTable`), and summing the
product of these tables over the code words on all channels gives the sum, over one index for all
roles and over the data on all channels, of the product of the tables (`Cut.sum_prod_codeTable`),
provided that the channels connect the roles.

This is how the moves of the cutting argument of [AnthropicVPVNP2026] (module `Nc.G.Contract`)
replace the strings of a law by units.

## Main definitions

* `Cut.codeTable`: the table of a role with code words on its channels.

## Main results

* `Cut.codeTable_congr`: only the code words on the channels of the role matter.
* `Cut.sum_prod_codeTable`: contraction.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Appendix H.2; module `Nc.G.Contract`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Cut

open Finset Play

variable {F : Type*} [CommSemiring F] {Ro Cn ι : Type*} [DecidableEq Ro]
  [Fintype Cn] [DecidableEq Cn] [Fintype ι] {S : ι → Cn → Type*} [∀ i ν, Fintype (S i ν)]
  {Z : Type*} [DecidableEq Z] (h : Cn → Bool → Ro) (code : (ν : Cn) → (i : ι) → S i ν → Z)

/-- The table of a role with code words on its channels: the sum of the table over the indices
and the data whose code words are the given ones. -/
def codeTable (p : Ro) (G : (i : ι) → ((ν : {ν // Holds h p ν}) → S i ν) → F) (z : Cn → Z) : F :=
  ∑ i, ∑ g : (ν : {ν // Holds h p ν}) → S i ν,
    if ∀ ν : {ν // Holds h p ν}, code ν i (g ν) = z ν then G i g else 0

theorem codeTable_eq_sum_sigma (p : Ro) (G : (i : ι) → ((ν : {ν // Holds h p ν}) → S i ν) → F)
    (z : Cn → Z) : codeTable h code p G z = ∑ q : Σ i, (ν : {ν // Holds h p ν}) → S i ν,
      if ∀ ν : {ν // Holds h p ν}, code ν q.1 (q.2 ν) = z ν then G q.1 q.2 else 0 := by
  rw [codeTable, Fintype.sum_sigma]

/-- Only the code words on the channels of the role matter. -/
theorem codeTable_congr {p : Ro} {G : (i : ι) → ((ν : {ν // Holds h p ν}) → S i ν) → F}
    {z z' : Cn → Z} (hz : ∀ ν, Holds h p ν → z ν = z' ν) :
    codeTable h code p G z = codeTable h code p G z' := by
  unfold codeTable
  exact sum_congr rfl fun i _ => sum_congr rfl fun g _ =>
    if_congr (forall_congr' fun ν => by rw [hz ν.val ν.property]) rfl rfl

variable {h code}

/-- **Contraction.** Tables with code words, summed over the code words on all channels, give the
sum, over one index and over the data on all channels, of the products of the tables. The code
words determine the index and the data, and indices that agree along all channels are equal. -/
theorem sum_prod_codeTable [Fintype Ro] [Nonempty Ro] [Fintype Z]
    (hcode : ∀ ν, Function.Injective fun q : Σ i, S i ν => code ν q.1 q.2)
    (hconn : ∀ f : Ro → ι, (∀ ν, f (h ν false) = f (h ν true)) → ∀ p q, f p = f q)
    (G : (p : Ro) → (i : ι) → ((ν : {ν // Holds h p ν}) → S i ν) → F) :
    ∑ z : Cn → Z, ∏ p, codeTable h code p (G p) z =
      ∑ i, ∑ g : ∀ ν, S i ν, ∏ p, G p i fun ν => g ν := by
  have p₀ : Ro := Classical.arbitrary Ro
  have hL (z : Cn → Z) : ∏ p, codeTable h code p (G p) z =
      ∑ f : (p : Ro) → Σ i, (ν : {ν // Holds h p ν}) → S i ν,
        if ∀ p, ∀ ν : {ν // Holds h p ν}, code ν (f p).1 ((f p).2 ν) = z ν then
          ∏ p, G p (f p).1 (f p).2 else 0 := by
    simp only [codeTable_eq_sum_sigma]
    rw [prod_univ_sum, Fintype.piFinset_univ]
    refine sum_congr rfl fun f _ => ?_
    rw [prod_ite_zero]
    simp only [mem_univ, true_imp_iff]
  simp only [hL]
  rw [← Fintype.sum_prod_type',
    ← Fintype.sum_sigma (fun q : Σ i, ∀ ν, S i ν => ∏ p, G p q.1 fun ν => q.2 ν)]
  symm
  refine sum_bij_ne_zero
    (fun q _ _ => (fun ν => code ν q.1 (q.2 ν), fun p => ⟨q.1, fun ν => q.2 ν⟩))
    (fun _ _ _ => mem_univ _) ?_ ?_ ?_
  · rintro ⟨i, g⟩ - - ⟨i', g'⟩ - - heq
    have h2 := congrArg Prod.snd heq
    obtain rfl : i = i' := congrArg Sigma.fst (congrFun h2 p₀)
    congr 1
    funext ν
    have h4 := congrFun h2 (h ν false)
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h4
    exact congrFun h4 ⟨ν, false, rfl⟩
  · rintro ⟨z, f⟩ - hne
    have hcond : ∀ p, ∀ ν : {ν // Holds h p ν}, code ν (f p).1 ((f p).2 ν) = z ν :=
      of_not_not fun hc => hne (ite_eq_right hc)
    rw [ite_eq_left hcond] at hne
    have hpair (ν : Cn) : (⟨(f (h ν false)).1, (f (h ν false)).2 ⟨ν, false, rfl⟩⟩ : Σ i, S i ν) =
        ⟨(f (h ν true)).1, (f (h ν true)).2 ⟨ν, true, rfl⟩⟩ :=
      hcode ν ((hcond _ ⟨ν, false, rfl⟩).trans (hcond _ ⟨ν, true, rfl⟩).symm)
    have hall (p : Ro) : (f p).1 = (f p₀).1 :=
      hconn (fun p => (f p).1) (fun ν => congrArg Sigma.fst (hpair ν)) p p₀
    obtain ⟨i, hi⟩ : ∃ i, i = (f p₀).1 := ⟨_, rfl⟩
    have hex (p : Ro) : ∃ gp : (ν : {ν // Holds h p ν}) → S i ν, f p = ⟨i, gp⟩ := by
      rcases hfp : f p with ⟨i', g'⟩
      obtain rfl : i' = i := by rw [hi, ← hall p, hfp]
      exact ⟨g', rfl⟩
    choose gp hgp using hex
    have hg (p : Ro) : (fun ν : {ν // Holds h p ν} => gp (h ν false) ⟨ν, false, rfl⟩) = gp p := by
      funext ⟨ν, hν⟩
      obtain ⟨d, rfl⟩ := hν
      cases d
      · rfl
      · have := hpair ν
        rw [hgp (h ν false), hgp (h ν true)] at this
        simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using this
    refine ⟨⟨i, fun ν => gp (h ν false) ⟨ν, false, rfl⟩⟩, mem_univ _, ?_, ?_⟩
    · refine fun h0 => hne (h0 ▸ (prod_congr rfl fun p _ => ?_).symm)
      dsimp only
      rw [hgp p, hg p]
    · refine Prod.ext (funext fun ν => ?_) (funext fun p => ?_)
      · have := hcond (h ν false) ⟨ν, false, rfl⟩
        rwa [hgp (h ν false)] at this
      · change (⟨i, fun ν => gp (h ν false) ⟨ν, false, rfl⟩⟩ :
          Σ i, (ν : {ν // Holds h p ν}) → S i ν) = f p
        rw [hgp p, hg p]
  · rintro ⟨i, g⟩ - -
    exact (ite_eq_left fun p ν => rfl).symm

end Cslib.Circuits.Arithmetic.Separation.Cut
