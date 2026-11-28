/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.ClauseSum
public import CslibFrontier.Computability.Circuit.Arithmetic.ComputedWithin
public import CslibFrontier.Computability.Circuit.Arithmetic.HamiltonianCycle
import CslibFrontier.Foundations.Data.Matrix.HamiltonianCycle.Grid
import CslibFrontier.Foundations.Data.Matrix.Permanent.Blocks
import CslibFrontier.Foundations.Data.Matrix.Permanent.Grid

/-!
# Grid sums are affine projections of the permanent and of the Hamiltonian cycle polynomial

A *grid sum* sums over two families of bits, `x : V → Bool` and `r : W' → Bool`, a product of
weights, one for each incidence `n : N` between a bit `v n` of the first family and a bit `w n`
of the second: `∑ x, ∑ r, ∏ n, W n (x (v n)) (r (w n))`. A family `G` of polynomials is *complete
for grid sums* with blow-up `κ` (`GridComplete G κ`) when every grid sum whose weights at the
incidences of one bit `r b` are affine in one common variable is an affine projection of
`G.poly S` for every `S ≥ κ * |N|`.

The permanent is complete for grid sums with blow-up `3` when `2 ≠ 0`
(`gridComplete_permFamily`), and the Hamiltonian cycle polynomial with blow-up `40` in every
characteristic (`gridComplete_hcFamily`), by the matrix forms
`Matrix.exists_permanent_eq_gridSum` and `Matrix.exists_hamiltonianCycleSum_eq_gridSum`. Sums of
products of *clauses*, weights that apply when all their literals hold (`clauseSum`), are grid
sums, hence affine projections of every family complete for grid sums
(`GridComplete.isAffineProjection_clauseSum`).

## Main definitions

* `Cslib.Circuits.Arithmetic.affineIn`: the polynomials affine in a given variable.
* `Cslib.Circuits.Arithmetic.GridComplete`: completeness for grid sums.

## Main results

* `Cslib.Circuits.Arithmetic.gridComplete_permFamily`: the permanent, when `2 ≠ 0`.
* `Cslib.Circuits.Arithmetic.gridComplete_hcFamily`: the Hamiltonian cycle polynomial.
* `Cslib.Circuits.Arithmetic.GridComplete.isAffineProjection_clauseSum`: clause sums.

## References

* [Claude, *VP ≠ VNP over every field*][AnthropicVPVNP2026], Proposition prop:grid,
  Corollary cor:clauses, Proposition prop:hc-grid
-/

public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial Finset

variable {K : Type} [Field K] {ι : Type*}

/-- The polynomials affine in the variable `o`: the constants for `o = none`, and the span of
the constants and `X i` for `o = some i`. -/
@[expose] noncomputable def affineIn : Option ι → Submodule K (MvPolynomial ι K)
  | none => Submodule.span K {1}
  | some i => Submodule.span K {X i, 1}

/-- The constant `1` is affine in every variable. -/
theorem one_mem_affineIn (o : Option ι) : (1 : MvPolynomial ι K) ∈ affineIn o := by
  cases o <;> exact Submodule.subset_span (by simp)

/-- Constants are affine in every variable. -/
theorem C_mem_affineIn (o : Option ι) (b : K) : (C b : MvPolynomial ι K) ∈ affineIn o := by
  simpa [smul_eq_C_mul] using (affineIn o).smul_mem b (one_mem_affineIn o)

/-- A polynomial affine in one variable is affine. -/
theorem IsAffine.of_mem_affineIn {o : Option ι} {P : MvPolynomial ι K} (h : P ∈ affineIn o) :
    IsAffine P := by
  cases o with
  | none =>
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 h
    exact Or.inl ⟨b, by rw [smul_eq_C_mul, mul_one]⟩
  | some i =>
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 h
    exact Or.inr ⟨i, a, b, by rw [smul_eq_C_mul, smul_eq_C_mul, mul_one]⟩

/-- A family `G` of polynomials is *complete for grid sums* with blow-up `κ`: a grid sum
`∑ x, ∑ r, ∏ n, W n (x (v n)) (r (w n))` over surjections `v` and `w`, whose weights at the
incidences `n` with one value `w n = b` are affine in the variable `o b`, is an affine projection
of `G.poly S` for every `S ≥ κ * |N|`. -/
@[expose] def GridComplete (G : PolynomialFamily K) (κ : ℕ) : Prop :=
  ∀ {ι N V W' : Type} [Fintype N] [Fintype V] [DecidableEq V] [Fintype W'] [DecidableEq W']
    (v : N → V) (w : N → W'), Function.Surjective v → Function.Surjective w →
    ∀ (W : N → Bool → Bool → MvPolynomial ι K) (o : W' → Option ι),
      (∀ n x r, W n x r ∈ affineIn (o (w n))) → ∀ S : ℕ, κ * Fintype.card N ≤ S →
        IsAffineProjection (∑ x : V → Bool, ∑ r : W' → Bool, ∏ n, W n (x (v n)) (r (w n)))
          (G.poly S)

/-- The entries of a matrix, in the row-major order of the variables of `genericMatrix`. -/
private def entries {A : Type*} {S : ℕ} (M : Matrix (Fin S) (Fin S) A) : Fin (S * S) → A :=
  fun k => M (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

private theorem map_aeval_genericMatrix {S : ℕ} (M : Matrix (Fin S) (Fin S) (MvPolynomial ι K)) :
    (genericMatrix K S).map (aeval (entries M)) = M := by
  ext i j
  simp [genericMatrix, entries]

/-- **The permanent is complete for grid sums** with blow-up `3` when `2 ≠ 0`
[Claude, *VP ≠ VNP over every field*][AnthropicVPVNP2026], Proposition prop:grid. -/
theorem gridComplete_permFamily (h2 : (2 : K) ≠ 0) : GridComplete (permFamily K) 3 := by
  intro ι N V W' _ _ _ _ _ v w hv hw W o hW S hS
  have hC2 : (C (2⁻¹ : K) : MvPolynomial ι K) * 2 = 1 := by
    rw [← map_ofNat C 2, ← map_mul, inv_mul_cancel₀ h2, map_one]
  obtain ⟨M, hM, hp⟩ := Matrix.exists_permanent_eq_gridSum _ hC2 v w hv hw W hS
  refine ⟨entries M, fun q => ?_, by
    change aeval _ (genericMatrix K S).permanent = _
    rw [AlgHom.map_permanent, map_aeval_genericMatrix, hp]⟩
  rcases hM (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2 with h | ⟨k, h⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h | h | h
    exacts [Or.inl ⟨0, h.trans C_0.symm⟩, Or.inl ⟨1, h.trans C_1.symm⟩,
      Or.inl ⟨-1, h.trans (by rw [map_neg, C_1])⟩, Or.inl ⟨2⁻¹, h⟩,
      Or.inl ⟨-2⁻¹, h.trans (map_neg C _).symm⟩]
  · refine IsAffine.of_mem_affineIn (o := o k)
      ((AddSubmonoid.closure_le (S := (affineIn (o k)).toAddSubmonoid)).2 ?_ h)
    rintro _ ⟨n, x, r, rfl, rfl⟩
    exact hW n x r

/-- **The Hamiltonian cycle polynomial is complete for grid sums** with blow-up `40` in every
characteristic [Claude, *VP ≠ VNP over every field*][AnthropicVPVNP2026], Proposition
prop:hc-grid. -/
theorem gridComplete_hcFamily : GridComplete (hcFamily K) 40 := by
  intro ι N V W' _ _ _ _ _ v w hv hw W o hW S hS
  obtain ⟨M, hM, hp⟩ := Matrix.exists_hamiltonianCycleSum_eq_gridSum v w hv hw W hS
  refine ⟨entries M, fun q => ?_, by
    change aeval _ (genericMatrix K S).hamiltonianCycleSum = _
    rw [AlgHom.map_hamiltonianCycleSum, map_aeval_genericMatrix, hp]⟩
  dsimp only [entries]
  rcases hM (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2 with h | h | ⟨n, x, r, h⟩
  exacts [Or.inl ⟨0, h.trans C_0.symm⟩, Or.inl ⟨1, h.trans C_1.symm⟩,
    h ▸ IsAffine.of_mem_affineIn (hW n x r)]

/-! ### Clause sums -/

/-- **Clause sums are affine projections** of every family complete for grid sums
[Claude, *VP ≠ VNP over every field*][AnthropicVPVNP2026], Corollary cor:clauses. Let every clause
have a literal, every bit occur in a literal, and every weight be a variable or a constant. Then
the clause sum is an affine projection of `G.poly S` for every `S ≥ κ * N`, where `N` is the total
number of literals. Each literal is an incidence between its bit and its clause. -/
theorem GridComplete.isAffineProjection_clauseSum {G : PolynomialFamily K} {c : ℕ}
    (hG : GridComplete G c) {ι V Θ : Type} [Fintype V] [DecidableEq V] [Fintype Θ]
    (lits : Θ → List (V × Bool)) (hne : ∀ κ, lits κ ≠ [])
    (hocc : ∀ b, ∃ κ, ∃ l ∈ lits κ, l.1 = b) (wt : Θ → MvPolynomial ι K)
    (hwt : ∀ κ, (∃ i, wt κ = X i) ∨ ∃ a, wt κ = C a) {S : ℕ}
    (hS : c * ∑ κ, (lits κ).length ≤ S) : IsAffineProjection (clauseSum lits wt) (G.poly S) := by
  classical
  let N := Σ κ, Fin (lits κ).length
  let v : N → V := fun n => ((lits n.1).get n.2).1
  let W : N → Bool → Bool → MvPolynomial ι K := fun n x r =>
    if r then (if x = ((lits n.1).get n.2).2 then (if n.2.val = 0 then wt n.1 - 1 else 1) else 0)
    else 1
  let o : Θ → Option ι := fun κ => if h : ∃ i, wt κ = X i then some h.choose else none
  have hwt' (κ : Θ) : wt κ ∈ affineIn (o κ) := by
    by_cases h : ∃ i, wt κ = X i
    · simp only [o, h, ↓reduceDIte]
      exact Submodule.subset_span (Set.mem_insert_iff.2 (.inl h.choose_spec))
    · obtain ⟨a, ha⟩ := (hwt κ).resolve_left h
      rw [ha]
      exact C_mem_affineIn _ _
  have hv : Function.Surjective v := fun b => by
    obtain ⟨κ, l, hl, rfl⟩ := hocc b
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hl
    exact ⟨⟨κ, i⟩, rfl⟩
  have hW (n : N) (x r : Bool) : W n x r ∈ affineIn (o n.1) := by
    simp only [W]
    split_ifs
    exacts [Submodule.sub_mem _ (hwt' _) (one_mem_affineIn _), one_mem_affineIn _,
      Submodule.zero_mem _, one_mem_affineIn _]
  obtain ⟨M, hM, he⟩ := hG v (fun n : N => n.1) hv
    (fun κ => ⟨⟨κ, ⟨0, List.length_pos_iff.2 (hne κ)⟩⟩, rfl⟩) W o hW S (by simpa [N] using hS)
  refine ⟨M, hM, he.trans (Finset.sum_congr rfl fun x _ => ?_)⟩
  have hprod (r : Θ → Bool) : ∏ n : N, W n (x (v n)) (r n.1) =
      ∏ κ, ∏ i : Fin (lits κ).length, W ⟨κ, i⟩ (x (v ⟨κ, i⟩)) (r κ) :=
    Fintype.prod_sigma _
  simp only [hprod]
  rw [← Fintype.prod_sum fun κ b => ∏ i : Fin (lits κ).length, W ⟨κ, i⟩ (x (v ⟨κ, i⟩)) b]
  refine Finset.prod_congr rfl fun κ _ => ?_
  rw [Fintype.sum_bool]
  simp only [W, Bool.false_eq_true, ↓reduceIte, Finset.prod_const_one]
  by_cases hall : ∀ l ∈ lits κ, x l.1 = l.2
  · rw [ite_eq_left hall]
    simp only [v, fun i => hall _ (List.get_mem (lits κ) i), ↓reduceIte]
    rw [Finset.prod_eq_single (⟨0, List.length_pos_iff.2 (hne κ)⟩ : Fin (lits κ).length)]
    exacts [by simp, fun i _ hi => ite_eq_right fun h => hi (Fin.ext h), by simp]
  · rw [ite_eq_right hall]
    push Not at hall
    obtain ⟨l, hl, hne'⟩ := hall
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hl
    rw [Finset.prod_eq_zero (mem_univ i) (ite_eq_right hne'), zero_add]

end Cslib.Circuits.Arithmetic
