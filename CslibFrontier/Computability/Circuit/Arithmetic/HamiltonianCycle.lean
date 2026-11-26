/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Determinant
public import CslibFrontier.Computability.Circuit.Arithmetic.VNP
public import CslibFrontier.Foundations.Data.Matrix.HamiltonianCycle
import CslibFrontier.Computability.Circuit.Arithmetic.ComputedWithin
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import Mathlib.Algebra.MvPolynomial.CommRing
import CslibFrontier.Foundations.Data.MvPolynomial.Degrees

/-!
# The Hamiltonian cycle polynomial belongs to VNP

The *Hamiltonian cycle polynomial* `HC_n` is the Hamiltonian cycle sum
(`Matrix.hamiltonianCycleSum`) of the generic `n × n` matrix: the sum, over the cycles `σ` through
all of `Fin n`, of `∏ i, X (i, σ i)`. The family `hcFamily K` of these polynomials belongs to
`VNP K` over every commutative ring `K`.

The witness writes a cycle as the order in which it visits the vertices from `0` on, with a bit
for every position `i` and vertex `u` meaning "position `i` holds `u`". A product of local tests,
`1 - b * b'` for every pair of bits of one position or one vertex and `∑ u, b (i, u)` for every
position, is `1` on the bit tables of bijections and `0` on all others. The witness multiplies
it by the bit "position `0` holds `0`" and, for every position `i`, by
`∑ (u, v), b (i, u) * b (i + 1, v) * X (u, v)`, the edge between consecutive positions. It has
`n ^ 2 + n ^ 2` variables, degree and circuits of size `O(n ^ 4)`.

## Main definitions

* `Cslib.Circuits.Arithmetic.hcFamily`: the family of Hamiltonian cycle polynomials.

## Main results

* `Cslib.Circuits.Arithmetic.isPFamily_hcFamily`: it is a p-family.
* `Cslib.Circuits.Arithmetic.map_hamiltonianCycleSum_genericMatrix`: change of coefficients.
* `Cslib.Circuits.Arithmetic.hcFamily_mem_VNP`: it belongs to `VNP` over every commutative ring.

## References

* [L. G. Valiant, *Completeness classes in algebra*][Valiant1979Algebra]
* [Claude, *VP ≠ VNP over every field*][AnthropicVPVNP2026]
-/

public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial Finset

universe u

/-- The family of Hamiltonian cycle polynomials over `K`: its `n`-th member is the Hamiltonian
cycle sum of the generic `n × n` matrix, a polynomial in `n * n` variables. -/
@[expose] noncomputable def hcFamily (K : Type u) [CommSemiring K] : PolynomialFamily K where
  vars n := n * n
  poly n := (genericMatrix K n).hamiltonianCycleSum

/-- The Hamiltonian cycle polynomial has total degree at most `n`. -/
theorem totalDegree_hamiltonianCycleSum_genericMatrix_le {K : Type u} [CommSemiring K] (n : ℕ) :
    (genericMatrix K n).hamiltonianCycleSum.totalDegree ≤ n := by
  rw [Matrix.hamiltonianCycleSum]
  refine totalDegree_finsetSum_le fun σ _ => (totalDegree_finsetProd _ _).trans ?_
  calc _ ≤ ∑ _i : Fin n, 1 :=
        Finset.sum_le_sum fun i _ => (totalDegree_monomial_le _ _).trans (by simp)
    _ = n := by simp

/-- The Hamiltonian cycle family is a p-family. -/
theorem isPFamily_hcFamily {K : Type u} [CommSemiring K] : (hcFamily K).IsPFamily :=
  ⟨PolynomiallyBounded.id.mul PolynomiallyBounded.id,
    PolynomiallyBounded.id.mono_of_le (totalDegree_hamiltonianCycleSum_genericMatrix_le (K := K))⟩

/-- Mapping the coefficients of the generic Hamiltonian cycle polynomial along `f` gives the
generic Hamiltonian cycle polynomial. -/
theorem map_hamiltonianCycleSum_genericMatrix {R : Type u} {S : Type*} [CommSemiring R]
    [CommSemiring S] (f : R →+* S) (n : ℕ) :
    MvPolynomial.map f (genericMatrix R n).hamiltonianCycleSum =
      (genericMatrix S n).hamiltonianCycleSum := by
  rw [RingHom.map_hamiltonianCycleSum, map_genericMatrix]

variable {K : Type u} [CommRing K] (n : ℕ)

/-- The witness polynomials have the `n * n` matrix entries first and then the `n * n` bits. -/
private abbrev W (K : Type u) [CommRing K] (n : ℕ) := MvPolynomial (Fin (n * n + n * n)) K

/-- The bit "position `i` holds vertex `u`". -/
private noncomputable def pos (i u : Fin n) : W K n :=
  X (Fin.natAdd (n * n) (finProdFinEquiv (i, u)))

/-- The matrix entry `(u, v)`. -/
private noncomputable def entry (u v : Fin n) : W K n :=
  X (Fin.castAdd (n * n) (finProdFinEquiv (u, v)))

/-- The pairs of bits that exclude each other: two of one position or two of one vertex. -/
private def clash : Finset ((Fin n × Fin n) × (Fin n × Fin n)) :=
  univ.filter fun p => p.1 ≠ p.2 ∧ (p.1.1 = p.2.1 ∨ p.1.2 = p.2.2)

/-- The test that the bits are the table of a bijection between positions and vertices. -/
private noncomputable def orderTest : W K n :=
  (∏ p ∈ clash n, (1 - pos n p.1.1 p.1.2 * pos n p.2.1 p.2.2)) * ∏ i, ∑ u, pos n i u

/-- The edges between consecutive positions. -/
private noncomputable def orderEdges : W K n :=
  ∏ i, ∑ p : Fin n × Fin n, pos n i p.1 * pos n (finRotate n i) p.2 * entry n p.1 p.2

/-- The witness: the test, vertex `0` at position `0`, and the edges. -/
private noncomputable def hcWitness : W K n :=
  if h : 0 < n then orderTest (K := K) n * pos n ⟨0, h⟩ ⟨0, h⟩ * orderEdges n else 1

/-! ### Summing the witness over the bits -/

/-- The bit table of an order `π`: position `i` holds `π i`. -/
private def orderBits (π : Equiv.Perm (Fin n)) : Fin (n * n) → Bool :=
  fun q => decide (π (finProdFinEquiv.symm q).1 = (finProdFinEquiv.symm q).2)

private theorem orderBits_injective : Function.Injective (orderBits n) := by
  intro π π' e
  exact Equiv.ext fun i => Eq.symm (of_decide_eq_true <| by
    simpa only [orderBits, Equiv.symm_apply_apply, decide_true] using
      (congrFun e (finProdFinEquiv (i, π i))).symm)

/-- Substituting the bits `e` into a bit. -/
private theorem projection_pos (e : Fin (n * n) → Bool) (i u : Fin n) :
    projection (booleanAssignment e) (pos (K := K) n i u) =
      C (bif e (finProdFinEquiv (i, u)) then 1 else 0) := by
  simp only [pos, projection_X, booleanAssignment, Fin.append_right, Sum.elim_inr]

private theorem projection_entry (e : Fin (n * n) → Bool) (u v : Fin n) :
    projection (booleanAssignment e) (entry (K := K) n u v) =
      (genericMatrix K n) u v := by
  rw [entry, projection_X]
  simp only [booleanAssignment, Fin.append_left, Sum.elim_inl, genericMatrix, Matrix.of_apply]

private theorem projection_pos_orderBits (π : Equiv.Perm (Fin n)) (i u : Fin n) :
    projection (booleanAssignment (orderBits n π)) (pos (K := K) n i u) =
      if π i = u then 1 else 0 := by
  rw [projection_pos]
  by_cases h : π i = u <;> simp [orderBits, h]

private theorem projection_orderTest_orderBits (π : Equiv.Perm (Fin n)) :
    projection (booleanAssignment (orderBits n π)) (orderTest (K := K) n) = 1 := by
  simp only [orderTest, map_mul, map_prod, map_sub, map_one, map_sum, projection_pos_orderBits]
  rw [Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · simp
  · intro p hp
    obtain ⟨hne, h⟩ := (mem_filter.1 hp).2
    have : ¬ (π p.1.1 = p.1.2 ∧ π p.2.1 = p.2.2) := fun ⟨h1, h2⟩ =>
      hne <| h.elim (fun e => Prod.ext e (h1.symm.trans ((congrArg π e).trans h2))) fun e =>
        Prod.ext (π.injective (h1.trans (e.trans h2.symm))) e
    split_ifs with h1 h2 <;> simp_all

/-- Bits pass the test only if they are the table of a bijection between positions and
vertices. -/
private theorem exists_orderBits_of_ne_zero (e : Fin (n * n) → Bool)
    (h : projection (booleanAssignment e) (orderTest (K := K) n) ≠ 0) :
    ∃ π, orderBits n π = e := by
  simp only [orderTest, map_mul, map_prod, map_sub, map_one, map_sum, projection_pos] at h
  have h1 (p) (hp : p ∈ clash n) : ¬ (e (finProdFinEquiv p.1) ∧ e (finProdFinEquiv p.2)) :=
    fun ⟨a, b⟩ => h (mul_eq_zero_of_left (Finset.prod_eq_zero hp (by simp [a, b])) _)
  have h2 (i : Fin n) : ∃ u, e (finProdFinEquiv (i, u)) = true := by
    by_contra! hc
    exact h (mul_eq_zero_of_right _ (Finset.prod_eq_zero (mem_univ i)
      (Finset.sum_eq_zero fun u _ => by simp [hc u])))
  choose f hf using h2
  have hinj : Function.Injective f := fun i j hij => by_contra fun hne =>
    h1 ((i, f i), (j, f j))
      (mem_filter.2 ⟨mem_univ _, fun q => hne (Prod.mk.inj q).1, .inr hij⟩) ⟨hf i, hf j⟩
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), funext fun q => ?_⟩
  obtain ⟨⟨i, u⟩, rfl⟩ := finProdFinEquiv.surjective q
  rw [Bool.eq_iff_iff]
  simp only [orderBits, Equiv.symm_apply_apply, decide_eq_true_iff, Equiv.ofBijective_apply]
  exact ⟨fun hu => hu ▸ hf i, fun hu => by_contra fun hne =>
    h1 ((i, f i), (i, u))
      (mem_filter.2 ⟨mem_univ _, fun q => hne (Prod.mk.inj q).2, .inl rfl⟩) ⟨hf i, hu⟩⟩

private theorem projection_orderEdges_orderBits (π : Equiv.Perm (Fin n)) :
    projection (booleanAssignment (orderBits n π)) (orderEdges (K := K) n) =
      ∏ i, genericMatrix K n (π i) (π (finRotate n i)) := by
  simp only [orderEdges, map_prod, map_sum, map_mul, projection_pos_orderBits, projection_entry]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (π i, π (finRotate n i))
    (fun p _ hp => by split_ifs <;> simp_all [Prod.ext_iff])
    (by simp)]
  simp

/-- **Summing the witness over all bit tables gives the Hamiltonian cycle polynomial.** -/
private theorem booleanSum_hcWitness :
    booleanSum (n * n) (hcWitness (K := K) n) = (genericMatrix K n).hamiltonianCycleSum := by
  classical
  rcases n with _ | k
  · have : IsEmpty (Fin (0 * 0)) := ⟨fun i => i.elim0⟩
    rw [booleanSum, hcWitness, dite_eq_right_of_eq_false (by simp), Fintype.sum_unique, map_one,
      Matrix.hamiltonianCycleSum, Finset.sum_eq_single_of_mem 1
        (mem_filter.2 ⟨mem_univ _, Set.bijOn_univ.2 (Equiv.bijective _), fun i => i.elim0⟩)
        fun σ _ hne => absurd (Subsingleton.elim _ _) hne]
    simp
  have hsum (g : W K (k + 1)) :
      ∑ e, projection (booleanAssignment e) (orderTest (K := K) (k + 1) * g) =
        ∑ π, projection (booleanAssignment (orderBits (k + 1) π)) g := by
    rw [← Finset.sum_subset (subset_univ (univ.image (orderBits (k + 1)))),
      Finset.sum_image (orderBits_injective (k + 1)).injOn]
    · exact Finset.sum_congr rfl fun π _ => by rw [map_mul, projection_orderTest_orderBits, one_mul]
    · refine fun e _ he => by_contra fun h => ?_
      obtain ⟨π, rfl⟩ := exists_orderBits_of_ne_zero (k + 1) e
        (left_ne_zero_of_mul (by rwa [map_mul] at h))
      exact he (mem_image_of_mem _ (mem_univ _))
  rw [booleanSum, hcWitness, dite_eq_left_of_eq_true (eq_true k.succ_pos)]
  simp only [mul_assoc]
  rw [hsum]
  simp only [map_mul, projection_pos_orderBits, projection_orderEdges_orderBits, ite_mul, one_mul,
    zero_mul, ← Finset.sum_filter, Matrix.hamiltonianCycleSum_eq_sum_orders]
  rfl

/-! ### Size and degree of the witness -/

private theorem card_clash_le : (clash n).card ≤ n ^ 4 :=
  (Finset.card_le_univ _).trans (le_of_eq (by simp [Fintype.card_prod]; ring))

private theorem computedWithin_hcWitness :
    ComputedWithin (hcWitness (K := K) n) (40 * (n + 1) ^ 4) := by
  unfold hcWitness
  split_ifs with h
  · have hpos (i u : Fin n) : ComputedWithin (pos (K := K) n i u) 1 := computedWithin_X _
    have h1 := ComputedWithin.prod (clash n) (s := 7) fun p _ => by
      have := (computedWithin_C (σ := Fin (n * n + n * n)) (1 : K)).add
        ((computedWithin_C (-1 : K)).mul ((hpos p.1.1 p.1.2).mul (hpos p.2.1 p.2.2)))
      rwa [C_1, map_neg, C_1, neg_one_mul, ← sub_eq_add_neg] at this
    have h2 := ComputedWithin.prod univ fun i _ => ComputedWithin.sum univ fun u _ => hpos i u
    have h3 := ComputedWithin.prod univ fun i _ =>
        ComputedWithin.sum univ fun (p : Fin n × Fin n) _ =>
      ((hpos i p.1).mul (hpos (finRotate n i) p.2)).mul (computedWithin_X (K := K)
        (Fin.castAdd (n * n) (finProdFinEquiv (p.1, p.2))))
    refine (((h1.mul h2).mul (hpos _ _)).mul h3).mono ?_
    have := card_clash_le n
    simp only [card_univ, Fintype.card_prod, Fintype.card_fin]
    nlinarith [Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2)]
  · exact (computedWithin_C 1).mono (by have := Nat.one_le_pow 4 (n + 1) (by omega); omega)

private theorem totalDegree_hcWitness_le :
    (hcWitness (K := K) n).totalDegree ≤ 40 * (n + 1) ^ 4 := by
  unfold hcWitness
  split_ifs with h
  · have h1 : (orderTest (K := K) n).totalDegree ≤ (clash n).card * 2 + n * 1 := by
      refine (totalDegree_mul _ _).trans (add_le_add ?_ ?_)
      · refine (totalDegree_finsetProd _ _).trans ((Finset.sum_le_sum (g := fun _ => 2)
          fun p _ => (totalDegree_sub _ _).trans (max_le (by simp) ?_)).trans (by simp))
        exact (totalDegree_mul _ _).trans (add_le_add (totalDegree_X_le _) (totalDegree_X_le _))
      · exact (totalDegree_finsetProd _ _).trans ((Finset.sum_le_sum (g := fun _ => 1)
          fun i _ => totalDegree_finsetSum_le fun u _ => totalDegree_X_le _).trans (by simp))
    have h3 : (orderEdges (K := K) n).totalDegree ≤ n * 3 := by
      refine (totalDegree_finsetProd _ _).trans ((Finset.sum_le_sum (g := fun _ => 3)
        fun i _ => totalDegree_finsetSum_le fun p _ => ?_).trans (by simp))
      exact (totalDegree_mul _ _).trans (add_le_add ((totalDegree_mul _ _).trans
        (add_le_add (totalDegree_X_le _) (totalDegree_X_le _))) (totalDegree_X_le _))
    refine (totalDegree_mul _ _).trans ((add_le_add
      ((totalDegree_mul _ _).trans (add_le_add h1 (totalDegree_X_le _))) h3).trans ?_)
    have := card_clash_le n
    nlinarith [Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2)]
  · simp

/-- **The Hamiltonian cycle family belongs to `VNP`** over every commutative ring `K`
[Claude, *VP ≠ VNP over every field*][AnthropicVPVNP2026]. The witness sums over `n * n` bits a
polynomial with circuits of `O(n ^ 4)` nodes. -/
theorem hcFamily_mem_VNP : hcFamily K ∈ VNP K := by
  have hb : PolynomiallyBounded fun n => 40 * (n + 1) ^ 4 :=
    PolynomiallyBounded.of_forall_le 40 4 fun _ => le_rfl
  have hsq := PolynomiallyBounded.id.mul PolynomiallyBounded.id
  exact ⟨fun n => n * n, hcWitness (K := K), mem_VP_iff.2 ⟨⟨hsq.add hsq, hb.mono_of_le
    (totalDegree_hcWitness_le (K := K))⟩, _, hb, computedWithin_hcWitness (K := K)⟩,
    fun n => (booleanSum_hcWitness n).symm⟩

end Cslib.Circuits.Arithmetic
