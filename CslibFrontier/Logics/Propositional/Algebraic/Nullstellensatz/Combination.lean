/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Algebraic.Nullstellensatz.Proof

/-!
# Nullstellensatz certificates from finite combinations

A Nullstellensatz proof (`Cslib.Logic.PL.NS.IsProof`) assigns one multiplier to each position of
the input list. Certificates are often easier to write as a finite sum `∑ t ∈ s, f t * g t` with
every `f t` an input, where the same input may occur for several `t`.
`Cslib.Logic.PL.NS.exists_isProof_of_sum` turns such a sum into a certificate. If every term with
a nonzero multiplier has `deg (f t) + deg (g t) ≤ d`, the certificate has degree at most `d`
(`Cslib.Logic.PL.NS.degree`). Each multiplier `g t` is added at one position holding `f t`.
In particular, refutability in degree `d` is monotone in the input list
(`Cslib.Logic.PL.NS.RefutableInDegree.mono`).

## Main results

* `Cslib.Logic.PL.NS.exists_isProof_of_sum`: a certificate from a finite combination of inputs.
* `Cslib.Logic.PL.NS.RefutableInDegree.mono`: monotonicity in the inputs and the degree.
-/

public section

namespace Cslib.Logic.PL.NS

open MvPolynomial

variable {V R : Type*} [CommSemiring R]

/-- **A certificate from a finite combination.** If `q = ∑ t ∈ s, f t * g t` with every `f t` in
`F`, and every term with `g t ≠ 0` has `deg (f t) + deg (g t) ≤ d`, then `q` has a
Nullstellensatz proof from `F` of degree at most `d`. -/
theorem exists_isProof_of_sum {κ : Type*} {F : List (MvPolynomial V R)} (s : Finset κ)
    (f g : κ → MvPolynomial V R) (hf : ∀ t ∈ s, f t ∈ F) {d : ℕ}
    (hd : ∀ t ∈ s, g t ≠ 0 → (f t).totalDegree + (g t).totalDegree ≤ d) :
    ∃ P, IsProof F P (∑ t ∈ s, f t * g t) ∧ degree F P ≤ d := by
  classical
  choose index hindex using fun t : s => List.get_of_mem (hf t.val t.property)
  let supported := s.attach.filter fun t => g t.val ≠ 0
  let fiber (i : Fin F.length) := supported.filter fun t => index t = i
  let P (i : Fin F.length) := ∑ t ∈ fiber i, g t.val
  refine ⟨P, ?_, degree_le_iff.2 ?_⟩
  · change ∑ i, F.get i * P i = _
    calc
      _ = ∑ i, ∑ t ∈ fiber i, f t.val * g t.val := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [P, Finset.mul_sum]
        exact Finset.sum_congr rfl fun t ht => by
          rw [← (Finset.mem_filter.mp ht).2, hindex t]
      _ = ∑ t ∈ supported, f t.val * g t.val := Finset.sum_fiberwise _ _ _
      _ = ∑ t ∈ s.attach, f t.val * g t.val := by
        refine Finset.sum_subset (Finset.filter_subset _ _) fun t ht hnot => ?_
        have hz : g t.val = 0 := Classical.not_not.mp fun h => hnot (Finset.mem_filter.mpr ⟨ht, h⟩)
        rw [hz, mul_zero]
      _ = _ := Finset.sum_attach s (fun t => f t * g t)
  · intro i hi
    have hb (t) (ht : t ∈ fiber i) : (F.get i).totalDegree + (g t.val).totalDegree ≤ d := by
      obtain ⟨ht', rfl⟩ := Finset.mem_filter.mp ht
      rw [hindex t]
      exact hd t.val t.property (Finset.mem_filter.mp ht').2
    have hn : (fiber i).Nonempty := Finset.nonempty_of_ne_empty fun h => hi (by simp [P, h])
    obtain ⟨t, ht, hmax⟩ := (fiber i).exists_mem_eq_sup hn (fun u => (g u.val).totalDegree)
    have hP := (totalDegree_finsetSum (fiber i) (fun u => g u.val)).trans_eq hmax
    exact (Nat.add_le_add_left hP _).trans (hb t ht)

/-- Nullstellensatz refutability in degree `d` is monotone in the input list and in `d`. -/
theorem RefutableInDegree.mono {F G : List (MvPolynomial V R)} {d e : ℕ}
    (h : RefutableInDegree F d) (hFG : F ⊆ G) (hde : d ≤ e) : RefutableInDegree G e := by
  obtain ⟨P, hP, hd⟩ := h
  rw [degree_le_iff] at hd
  obtain ⟨Q, hQ, hQd⟩ := exists_isProof_of_sum (F := G) Finset.univ (fun i => F.get i) P
    (fun i _ => hFG (List.get_mem F i)) (fun i _ hi => (hd i hi).trans hde)
  exact ⟨Q, hQ.trans hP, hQd⟩

end Cslib.Logic.PL.NS
