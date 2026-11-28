/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, next to `LinearAlgebra/Matrix/Permanent`)

public import CslibFrontier.Init
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# The Hamiltonian cycle sum of a matrix

The *Hamiltonian cycle sum* of a square matrix `M` over a commutative semiring is
`∑ σ, ∏ i, M i (σ i)`, the sum over the permutations `σ` that are one cycle through all indices.
Read `M i j` as the weight of the edge from `i` to `j` of a complete directed graph; the sum is
then the total weight of its Hamiltonian cycles. Like the permanent, which sums over all
permutations, it is unchanged by renaming the indices (`hamiltonianCycleSum_submatrix_equiv`)
and commutes with ring homomorphisms. Over `Fin (k + 1)`, a cycle through all indices is the order
in which it visits them from `0` on (`hamiltonianCycleSum_eq_sum_orders`).

## Main definitions

* `Matrix.hamiltonianCycleSum`: the Hamiltonian cycle sum.

## Main results

* `RingHom.map_hamiltonianCycleSum`, `AlgHom.map_hamiltonianCycleSum`: compatibility with
  homomorphisms.
* `Matrix.hamiltonianCycleSum_submatrix_equiv`: invariance under renaming the indices.
* `Matrix.hamiltonianCycleSum_eq_sum_orders`: the sum over the orders that start at `0`.

## References

* [Claude, *VP ≠ VNP over every field*][AnthropicVPVNP2026]
-/

public section

namespace Matrix

open Equiv Finset

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {R : Type*} [CommSemiring R]

open Classical in
/-- The *Hamiltonian cycle sum* of a square matrix: the sum, over the permutations `σ` that form a
single cycle through all indices, of `∏ i, M i (σ i)`. -/
@[expose] noncomputable def hamiltonianCycleSum (M : Matrix n n R) : R :=
  ∑ σ : Perm n with σ.IsCycleOn Set.univ, ∏ i, M i (σ i)

/-- Applying a ring homomorphism to the Hamiltonian cycle sum of a matrix is the Hamiltonian cycle
sum of the mapped matrix. -/
theorem _root_.RingHom.map_hamiltonianCycleSum {S : Type*} [CommSemiring S] (f : R →+* S)
    (M : Matrix n n R) : f M.hamiltonianCycleSum = (M.map f).hamiltonianCycleSum := by
  simp [hamiltonianCycleSum, map_sum, map_prod]

/-- Applying an algebra homomorphism to the Hamiltonian cycle sum of a matrix is the Hamiltonian
cycle sum of the mapped matrix. -/
theorem _root_.AlgHom.map_hamiltonianCycleSum {R₀ A B : Type*} [CommSemiring R₀] [CommSemiring A]
    [CommSemiring B] [Algebra R₀ A] [Algebra R₀ B] (f : A →ₐ[R₀] B) (M : Matrix n n A) :
    f M.hamiltonianCycleSum = (M.map f).hamiltonianCycleSum :=
  f.toRingHom.map_hamiltonianCycleSum M

/-- Renaming the indices of a square matrix does not change its Hamiltonian cycle sum. -/
@[simp] theorem hamiltonianCycleSum_submatrix_equiv (e : m ≃ n) (M : Matrix n n R) :
    (M.submatrix e e).hamiltonianCycleSum = M.hamiltonianCycleSum := by
  classical
  unfold hamiltonianCycleSum
  refine Finset.sum_equiv e.permCongr (fun σ => ?_) fun σ _ => ?_
  · simp only [mem_filter, mem_univ, true_and]
    have hz (k : ℤ) (a : m) : (e.permCongr σ ^ k) (e a) = e ((σ ^ k) a) := by
      rw [show e.permCongr σ ^ k = e.permCongr (σ ^ k) from (map_zpow e.permCongrHom σ k).symm,
        Equiv.permCongr_apply, Equiv.symm_apply_apply]
    constructor
    · refine fun h => ⟨Set.bijOn_univ.2 (Equiv.bijective _), fun a _ b _ => ?_⟩
      obtain ⟨k, hk⟩ := h.2 (Set.mem_univ (e.symm a)) (Set.mem_univ (e.symm b))
      exact ⟨k, by rw [← e.apply_symm_apply a, hz, hk, e.apply_symm_apply]⟩
    · refine fun h => ⟨Set.bijOn_univ.2 (Equiv.bijective _), fun a _ b _ => ?_⟩
      obtain ⟨k, hk⟩ := h.2 (Set.mem_univ (e a)) (Set.mem_univ (e b))
      exact ⟨k, e.injective ((hz k a).symm.trans hk)⟩
  · exact Fintype.prod_equiv e _ _ fun a => by simp [Equiv.permCongr_apply]

section Orders

variable {k : ℕ}

/-- The cycle that visits the indices in the order `π`. -/
private def cycleOf (π : Perm (Fin (k + 1))) : Perm (Fin (k + 1)) :=
  π * finRotate (k + 1) * π⁻¹

private theorem cycleOf_apply (π : Perm (Fin (k + 1))) (i : Fin (k + 1)) :
    cycleOf π (π i) = π (finRotate (k + 1) i) := by
  simp [cycleOf]

private theorem cycleOf_pow (π : Perm (Fin (k + 1))) {i : ℕ} (hi : i < k + 1) :
    (cycleOf π ^ i) (π 0) = π ⟨i, hi⟩ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ', Perm.mul_apply, ih (by omega), cycleOf_apply, finRotate_apply]
    exact congrArg π (Fin.ext (Fin.val_add_one_of_lt (by simp [Fin.lt_def]; omega)))

private theorem cycleOf_isCycleOn (π : Perm (Fin (k + 1))) : (cycleOf π).IsCycleOn Set.univ := by
  refine ⟨Set.bijOn_univ.2 (Equiv.bijective _), fun u _ v _ => ?_⟩
  have key (v : Fin (k + 1)) : (cycleOf π).SameCycle (π 0) v := by
    obtain ⟨i, rfl⟩ := π.surjective v
    exact ⟨(i : ℕ), by rw [zpow_natCast, cycleOf_pow π i.2]⟩
  exact (key u).symm.trans (key v)

/-- **A Hamiltonian cycle is an order of the indices.** Over `Fin (k + 1)`, every cycle through
all indices visits them in exactly one order `π` with `π 0 = 0`, and the cycle sends `π i` to
`π (i + 1)`. -/
theorem hamiltonianCycleSum_eq_sum_orders (M : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    M.hamiltonianCycleSum =
      ∑ π : Perm (Fin (k + 1)) with π 0 = 0, ∏ i, M (π i) (π (finRotate (k + 1) i)) := by
  classical
  unfold hamiltonianCycleSum
  symm
  refine Finset.sum_bij (fun π _ => cycleOf π)
    (fun π _ => mem_filter.2 ⟨mem_univ _, cycleOf_isCycleOn π⟩) ?_ ?_ ?_
  · intro π hπ π' hπ' e
    refine Equiv.ext fun i => ?_
    have h := cycleOf_pow π i.2
    have h' := cycleOf_pow π' i.2
    rwa [(mem_filter.1 hπ').2, ← e, ← (mem_filter.1 hπ).2, h] at h'
  · intro σ hσ
    have hc : σ.IsCycleOn ((univ : Finset (Fin (k + 1))) : Set (Fin (k + 1))) := by
      simpa only [Finset.coe_univ] using (mem_filter.1 hσ).2
    have hsur : Function.Surjective fun i : Fin (k + 1) => (σ ^ (i : ℕ)) 0 := fun v => by
      obtain ⟨i, hi, e⟩ := hc.exists_pow_eq (mem_univ (0 : Fin (k + 1))) (mem_univ v)
      exact ⟨⟨i, by simpa only [Finset.card_univ, Fintype.card_fin] using hi⟩, e⟩
    let π := Equiv.ofBijective _ (Finite.surjective_iff_bijective.1 hsur)
    refine ⟨π, mem_filter.2 ⟨mem_univ _, rfl⟩, Equiv.ext fun v => ?_⟩
    obtain ⟨i, rfl⟩ := π.surjective v
    rw [cycleOf_apply]
    change (σ ^ (finRotate (k + 1) i : ℕ)) 0 = σ ((σ ^ (i : ℕ)) 0)
    rw [← Perm.mul_apply, ← pow_succ', finRotate_apply, Fin.val_add_one]
    split_ifs with h
    · simpa only [Finset.card_univ, Fintype.card_fin, h, Fin.val_last, pow_zero, Perm.one_apply]
        using (hc.pow_card_apply (mem_univ (0 : Fin (k + 1)))).symm
    · rfl
  · intro π _
    rw [← Equiv.prod_comp π (fun u => M u (cycleOf π u))]
    exact Finset.prod_congr rfl fun i _ => by rw [cycleOf_apply]

end Orders

end Matrix
