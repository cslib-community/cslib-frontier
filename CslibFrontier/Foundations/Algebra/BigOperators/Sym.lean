/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.BigOperators

/-!
# Sums over ordered and over unordered pairs

`Fintype.sum_sum_ite_eq_two_nsmul_sum_sym2`: summing a function of the unordered pair `s(a, b)`
over the ordered pairs `(a, b)` of distinct elements counts every unordered pair that is not on
the diagonal twice. `Fintype.sum_subtype_not_isDiag`: a sum over the unordered pairs off the
diagonal, as a subtype, is a sum over all unordered pairs that leaves out the diagonal.

## Main results

* `Fintype.sum_sum_ite_eq_two_nsmul_sum_sym2`, `Fintype.sum_subtype_not_isDiag`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  modules `Nc.Tow.FromPrice` (`sum_off`) and `Paper.Laws`
-/

public section

open Finset

/-- A sum over the ordered pairs of distinct elements of a function of the unordered pair is twice
the sum over the unordered pairs off the diagonal. -/
theorem Fintype.sum_sum_ite_eq_two_nsmul_sum_sym2 {α M : Type*} [Fintype α] [DecidableEq α]
    [AddCommMonoid M] (f : Sym2 α → M) :
    ∑ a, ∑ b, (if a = b then 0 else f s(a, b)) = 2 • ∑ q : Sym2 α, if q.IsDiag then 0 else f q := by
  rw [← Fintype.sum_prod_type' (f := fun a b => if a = b then 0 else f s(a, b)),
    ← Finset.sum_fiberwise (s := univ) (g := fun p : α × α => s(p.1, p.2)), ← sum_nsmul]
  refine Finset.sum_congr rfl fun q _ => ?_
  induction q with | h a b => ?_
  by_cases hab : a = b
  · subst hab
    rw [ite_eq_left (Sym2.mk_isDiag_iff.2 rfl), nsmul_zero]
    refine Finset.sum_eq_zero fun p hp => ite_eq_left ?_
    obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := Sym2.eq_iff.1 (mem_filter.1 hp).2 <;> exact h1.trans h2.symm
  · have hf : univ.filter (fun p : α × α => s(p.1, p.2) = s(a, b)) = {(a, b), (b, a)} := by
      ext ⟨x, y⟩
      simp [or_comm]
    rw [hf, Finset.sum_pair (by simp [hab]), ite_eq_right hab, ite_eq_right (Ne.symm hab),
      ite_eq_right (mt Sym2.mk_isDiag_iff.1 hab), Sym2.eq_swap, two_nsmul]

/-- A sum over the unordered pairs off the diagonal, as a subtype, is the sum over all unordered
pairs that leaves out the diagonal. -/
theorem Fintype.sum_subtype_not_isDiag {α M : Type*} [Fintype α] [DecidableEq α]
    [AddCommMonoid M] (f : Sym2 α → M) :
    ∑ e : {q : Sym2 α // ¬ q.IsDiag}, f e = ∑ q : Sym2 α, if q.IsDiag then 0 else f q := by
  rw [← Finset.sum_subtype (univ.filter fun q : Sym2 α => ¬ q.IsDiag) (by simp) f, sum_filter]
  simp only [ite_not]
