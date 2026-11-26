/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/Convex/PiecewiseQuadratic.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Geometry.Polyhedra.PiecewiseLinear
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Piecewise-quadratic functions on compact polyhedra

This file develops real-valued quadratic functions on subsets of real vector spaces and
piecewise-quadratic (PQ) functions on compact polyhedra in the style of [RourkeSanderson1982].

## Main definitions

* `Cslib.Polyhedra.IsQuadraticOn`: `f : E → ℝ` agrees on `S` with a finite sum of products of
  pairs of real-valued affine maps.
* `Cslib.Polyhedra.IsPQOn`: `f : E → ℝ` is piecewise-quadratic on a compact polyhedron `P` if `P`
  is the space of a finite polytopal complex on every cell of which `f` is quadratic.

## Main results

* `Cslib.Polyhedra.isQuadraticOn_iff_quadraticMap_add_affineMap`: on finite-dimensional spaces,
  `IsQuadraticOn` agrees with `QuadraticMap + AffineMap`.
* `Cslib.Polyhedra.isQuadraticOn_iff_mvPolynomial_basis`: with respect to a finite basis,
  `IsQuadraticOn` is equivalent to agreement with an `MvPolynomial` of `totalDegree ≤ 2`.
* Closure of `IsPQOn` under restriction, finite closed covers, piecewise union, real linear
  combinations, products of PL functions (`IsPQOn.mul_of_isPLOn`), and precomposition with PL
  maps (`IsPQOn.comp_isPLOn`).
* `Cslib.Polyhedra.IsPQOn.exists_cell_list_mvPolynomial`,
  `Cslib.Polyhedra.IsPQOn.exists_cell_list_mvPolynomial_pi`, and
  `Cslib.Polyhedra.IsPQOn.exists_triangulation_mvPolynomial_basis`: finite cell lists and
  triangulations on whose cells a PQ function equals an `MvPolynomial` of `totalDegree ≤ 2`.

## References

* [RourkeSanderson1982] (background reference cited by issue #4325; specific chapter and theorem
  locators have not been verified against the original book).
* Issue #4325 notes (`STOC 1056 Lemma 3.1` label; unverified against the primary manuscript).
-/

public section

open scoped BigOperators
open Set

namespace Cslib.Polyhedra

section BasicQuadratic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A function `f : E → ℝ` is **quadratic on `S`** (meaning a polynomial of total degree at most
`2`) if it agrees on `S` with a finite sum of products of pairs of real-valued affine maps. -/
@[expose] def IsQuadraticOn (f : E → ℝ) (S : Set E) : Prop :=
  ∃ (n : ℕ) (a b : Fin n → E →ᵃ[ℝ] ℝ),
    Set.EqOn f (fun x => ∑ i, a i x * b i x) S

theorem IsQuadraticOn.congr {f f' : E → ℝ} {S : Set E} (hf : IsQuadraticOn f S)
    (heq : Set.EqOn f' f S) : IsQuadraticOn f' S := by
  rcases hf with ⟨n, a, b, h⟩
  exact ⟨n, a, b, heq.trans h⟩

theorem IsQuadraticOn.mono {f : E → ℝ} {S T : Set E} (hf : IsQuadraticOn f S)
    (hTS : T ⊆ S) : IsQuadraticOn f T := by
  rcases hf with ⟨n, a, b, h⟩
  exact ⟨n, a, b, h.mono hTS⟩

theorem IsQuadraticOn.of_isAffineOn {f : E → ℝ} {S : Set E} (hf : IsAffineOn f S) :
    IsQuadraticOn f S :=
  hf.elim fun g hg => ⟨1, fun _ => g, fun _ => AffineMap.const ℝ E 1, fun _ hx => by simp [hg hx]⟩

theorem IsQuadraticOn.affineMap (g : E →ᵃ[ℝ] ℝ) (S : Set E) : IsQuadraticOn g S :=
  IsQuadraticOn.of_isAffineOn (IsAffineOn.affineMap g S)

theorem IsQuadraticOn.const (S : Set E) (c : ℝ) : IsQuadraticOn (fun _ => c) S :=
  IsQuadraticOn.of_isAffineOn (IsAffineOn.const S c)

theorem IsQuadraticOn.add {f g : E → ℝ} {S : Set E}
    (hf : IsQuadraticOn f S) (hg : IsQuadraticOn g S) :
    IsQuadraticOn (fun x => f x + g x) S := by
  rcases hf with ⟨n₁, a₁, b₁, hf'⟩
  rcases hg with ⟨n₂, a₂, b₂, hg'⟩
  exact ⟨n₁ + n₂, Fin.addCases a₁ a₂, Fin.addCases b₁ b₂, fun x hx => by
    simp [hf' hx, hg' hx, Fin.sum_univ_add]⟩

theorem IsQuadraticOn.neg {f : E → ℝ} {S : Set E} (hf : IsQuadraticOn f S) :
    IsQuadraticOn (fun x => -f x) S := by
  rcases hf with ⟨n, a, b, hf'⟩
  exact ⟨n, fun i => -(a i), b, fun x hx => by simp [hf' hx]⟩

theorem IsQuadraticOn.sub {f g : E → ℝ} {S : Set E}
    (hf : IsQuadraticOn f S) (hg : IsQuadraticOn g S) :
    IsQuadraticOn (fun x => f x - g x) S :=
  (hf.add hg.neg).congr fun _ _ => sub_eq_add_neg _ _

theorem IsQuadraticOn.smul (c : ℝ) {f : E → ℝ} {S : Set E} (hf : IsQuadraticOn f S) :
    IsQuadraticOn (fun x => c * f x) S := by
  rcases hf with ⟨n, a, b, hf'⟩
  exact ⟨n, fun i => c • a i, b, fun x hx => by simp [hf' hx, mul_assoc, Finset.mul_sum]⟩

theorem IsQuadraticOn.sum {ι : Type*} (s : Finset ι) {f : ι → E → ℝ} {S : Set E}
    (hf : ∀ i ∈ s, IsQuadraticOn (f i) S) :
    IsQuadraticOn (fun x => ∑ i ∈ s, f i x) S := by
  classical
  induction s using Finset.induction with
  | empty =>
    exact (IsQuadraticOn.const S 0).congr fun _ _ => Finset.sum_empty
  | @insert a s ha ih =>
    exact ((hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))).congr fun _ _ => Finset.sum_insert ha

theorem IsQuadraticOn.mul_of_isAffineOn {f g : E → ℝ} {S : Set E}
    (hf : IsAffineOn f S) (hg : IsAffineOn g S) :
    IsQuadraticOn (fun x => f x * g x) S := by
  rcases hf, hg with ⟨⟨af, haf⟩, ⟨ag, hag⟩⟩
  exact ⟨1, fun _ => af, fun _ => ag, fun x hx => by simp [haf hx, hag hx]⟩

theorem IsQuadraticOn.comp_affineMap {g : F → ℝ} {T : Set F}
    (hg : IsQuadraticOn g T) (a : E →ᵃ[ℝ] F) {S : Set E} (hmaps : MapsTo a S T) :
    IsQuadraticOn (g ∘ a) S := by
  rcases hg with ⟨n, u, v, hu⟩
  exact ⟨n, fun i => (u i).comp a, fun i => (v i).comp a, fun _ hx => hu (hmaps hx)⟩

end BasicQuadratic

section PolynomialAndQuadraticMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsQuadraticOn.continuousOn [FiniteDimensional ℝ E] {f : E → ℝ} {S : Set E}
    (hf : IsQuadraticOn f S) : ContinuousOn f S := by
  obtain ⟨n, a, b, h⟩ := hf
  exact (continuousOn_finsetSum Finset.univ fun i _ =>
    ((a i).continuous_of_finiteDimensional.mul
      (b i).continuous_of_finiteDimensional).continuousOn).congr h

private lemma isQuadraticOn_of_quadraticMap [FiniteDimensional ℝ E]
    (Q : QuadraticMap ℝ E ℝ) (S : Set E) : IsQuadraticOn Q S := by
  obtain ⟨B, hB⟩ := Q.exists_companion
  have hQB (x : E) : Q x = (1 / 2 : ℝ) * B x x := by
    have h := hB x x
    rw [← two_smul ℝ x, Q.map_smul, smul_eq_mul] at h
    linarith
  let b := Module.finBasis ℝ E
  refine (IsQuadraticOn.sum Finset.univ fun i _ => IsQuadraticOn.sum Finset.univ fun j _ =>
    IsQuadraticOn.mul_of_isAffineOn
      (IsAffineOn.affineMap (((1 / 2 : ℝ) * B (b j) (b i)) • (b.coord i).toAffineMap) S)
      (IsAffineOn.affineMap (b.coord j).toAffineMap S)).congr fun x _ => ?_
  rw [hQB x]
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    FunLike.coe_smul, LinearMap.coe_toAffineMap, Module.Basis.coord_apply,
    Pi.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- On a finite-dimensional real normed space, `IsQuadraticOn f S` holds if and only if `f` agrees
on `S` with the sum of a `QuadraticMap` and an `AffineMap`. -/
theorem isQuadraticOn_iff_quadraticMap_add_affineMap [FiniteDimensional ℝ E]
    {f : E → ℝ} {S : Set E} :
    IsQuadraticOn f S ↔
      ∃ (Q : QuadraticMap ℝ E ℝ) (L : E →ᵃ[ℝ] ℝ), Set.EqOn f (fun x => Q x + L x) S := by
  constructor
  · rintro ⟨n, a, b, hf⟩
    let B : LinearMap.BilinMap ℝ E ℝ :=
      LinearMap.mk₂ ℝ (fun x y => ∑ i : Fin n, (a i).linear x * (b i).linear y)
        (fun _ _ _ => by simp only [map_add, add_mul, Finset.sum_add_distrib])
        (fun _ _ _ => by simp only [map_smul, smul_eq_mul, Finset.mul_sum, mul_assoc])
        (fun _ _ _ => by simp only [map_add, mul_add, Finset.sum_add_distrib])
        (fun _ _ _ => by
          simp only [map_smul, smul_eq_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _)
    let Llin : E →ₗ[ℝ] ℝ :=
      ∑ i : Fin n, (b i 0 • (a i).linear + a i 0 • (b i).linear)
    let L : E →ᵃ[ℝ] ℝ := Llin.toAffineMap + AffineMap.const ℝ E (∑ i : Fin n, a i 0 * b i 0)
    refine ⟨B.toQuadraticMap, L, fun x hx => ?_⟩
    rw [hf hx]
    simp only [LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.mk₂_apply,
      FunLike.coe_add, Pi.add_apply, LinearMap.coe_toAffineMap, LinearMap.sum_apply,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, AffineMap.const_apply, B, L, Llin]
    rw [← add_assoc, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [congrFun (AffineMap.decomp (a i)) x, congrFun (AffineMap.decomp (b i)) x]
    simp only [Pi.add_apply]
    ring
  · rintro ⟨Q, L, hQL⟩
    exact ((isQuadraticOn_of_quadraticMap Q S).add (IsQuadraticOn.affineMap L S)).congr hQL

private lemma finsupp_sum_le_two {ι : Type*} {m : ι →₀ ℕ}
    (hm : m.sum (fun _ k => k) ≤ 2) :
    m = 0 ∨ (∃ i, m = Finsupp.single i 1) ∨
      (∃ i j, m = Finsupp.single i 1 + Finsupp.single j 1) := by
  classical
  rw [← Finsupp.toMultiset_toFinsupp m]
  have hc : Multiset.card (Finsupp.toMultiset m) ≤ 2 := (Finsupp.card_toMultiset m).trans_le hm
  obtain h | h | h : Multiset.card (Finsupp.toMultiset m) = 0 ∨
      Multiset.card (Finsupp.toMultiset m) = 1 ∨ Multiset.card (Finsupp.toMultiset m) = 2 := by
    omega
  · simp [Multiset.card_eq_zero.1 h]
  · obtain ⟨a, ha⟩ := Multiset.card_eq_one.1 h
    exact Or.inr (Or.inl ⟨a, by rw [ha, Multiset.toFinsupp_singleton]⟩)
  · obtain ⟨a, b, ha⟩ := Multiset.card_eq_two.1 h
    refine Or.inr (Or.inr ⟨a, b, ?_⟩)
    rw [ha, Multiset.insert_eq_cons, ← Multiset.singleton_add, Multiset.toFinsupp_add,
      Multiset.toFinsupp_singleton, Multiset.toFinsupp_singleton]

private lemma affineMap_eq_mvPolynomial_basis {ι : Type*} [Finite ι]
    (e : Module.Basis ι ℝ E) (a : E →ᵃ[ℝ] ℝ) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 1 ∧
      ∀ x, MvPolynomial.eval (e.equivFun x) p = a x := by
  classical
  let := Fintype.ofFinite ι
  let p : MvPolynomial ι ℝ :=
    (∑ i : ι, MvPolynomial.C (a.linear (e i)) * MvPolynomial.X i) + MvPolynomial.C (a 0)
  refine ⟨p, ?_, fun x => ?_⟩
  · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ (by simp))
    exact MvPolynomial.totalDegree_finsetSum_le fun i _ =>
      (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  · simp only [p, map_add, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      Module.Basis.equivFun_apply]
    conv_rhs => rw [congrFun (AffineMap.decomp a) x, ← e.sum_repr x]
    simp only [Pi.add_apply, map_sum, map_smul, smul_eq_mul, mul_comm]

/-- On a finite-dimensional real normed space equipped with a finite basis `e`, `f` is quadratic on
`S` if and only if it agrees on `S` with a multivariate polynomial of `totalDegree ≤ 2` in the
`e`-coordinates. -/
theorem isQuadraticOn_iff_mvPolynomial_basis {ι : Type*} [Finite ι]
    (e : Module.Basis ι ℝ E) {f : E → ℝ} {S : Set E} :
    IsQuadraticOn f S ↔ ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 ∧
      Set.EqOn f (fun x => MvPolynomial.eval (e.equivFun x) p) S := by
  classical
  let := Fintype.ofFinite ι
  constructor
  · rintro ⟨n, a, b, hf⟩
    choose pa hpa hpa_eq using fun i => affineMap_eq_mvPolynomial_basis e (a i)
    choose pb hpb hpb_eq using fun i => affineMap_eq_mvPolynomial_basis e (b i)
    refine ⟨∑ i : Fin n, pa i * pb i, ?_, fun x hx => ?_⟩
    · refine MvPolynomial.totalDegree_finsetSum_le fun i _ => ?_
      exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hpa i) (hpb i))
    · simp only [hf hx, map_sum, map_mul, hpa_eq, hpb_eq]
  · rintro ⟨p, hp, hpf⟩
    refine IsQuadraticOn.congr (IsQuadraticOn.sum p.support
      (f := fun m x => MvPolynomial.eval (e.equivFun x) (MvPolynomial.monomial m (p.coeff m)))
      fun m hm => ?_) ?_
    · have hmdeg : m.sum (fun _ k => k) ≤ 2 :=
        (Finset.le_sup (f := fun s : ι →₀ ℕ => s.sum fun _ k => k) hm).trans hp
      rcases finsupp_sum_le_two hmdeg with rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩
      · exact (IsQuadraticOn.const S (p.coeff 0)).congr fun x _ => by simp
      · exact (IsQuadraticOn.affineMap
          (p.coeff (Finsupp.single i 1) • (e.coord i).toAffineMap) S).congr fun x _ => by
            simp [MvPolynomial.eval_monomial]
      · exact (IsQuadraticOn.mul_of_isAffineOn
          (IsAffineOn.affineMap
            (p.coeff (Finsupp.single i 1 + Finsupp.single j 1) • (e.coord i).toAffineMap) S)
          (IsAffineOn.affineMap (e.coord j).toAffineMap S)).congr fun x _ => by
            simp [MvPolynomial.eval_monomial, Finsupp.prod_add_index', pow_add, mul_assoc]
    · exact fun x hx => (hpf hx).trans <| by
        simpa only [map_sum] using congrArg (MvPolynomial.eval (e.equivFun x)) p.as_sum

/-- Variant of `isQuadraticOn_iff_mvPolynomial_basis` using `Module.finBasis ℝ E`. -/
theorem isQuadraticOn_iff_mvPolynomial [FiniteDimensional ℝ E] {f : E → ℝ} {S : Set E} :
    IsQuadraticOn f S ↔ ∃ p : MvPolynomial (Fin (Module.finrank ℝ E)) ℝ, p.totalDegree ≤ 2 ∧
      Set.EqOn f (fun x => MvPolynomial.eval ((Module.finBasis ℝ E).equivFun x) p) S :=
  isQuadraticOn_iff_mvPolynomial_basis (Module.finBasis ℝ E)

/-- On `Fin d → ℝ`, `IsQuadraticOn f S` is equivalent to agreeing on `S` with an
`MvPolynomial (Fin d) ℝ` of `totalDegree ≤ 2`. -/
theorem isQuadraticOn_iff_mvPolynomial_pi {d : ℕ} {f : (Fin d → ℝ) → ℝ} {S : Set (Fin d → ℝ)} :
    IsQuadraticOn f S ↔ ∃ p : MvPolynomial (Fin d) ℝ, p.totalDegree ≤ 2 ∧
      Set.EqOn f (fun x => MvPolynomial.eval x p) S :=
  isQuadraticOn_iff_mvPolynomial_basis (Pi.basisFun ℝ (Fin d))

end PolynomialAndQuadraticMap

section GeneralPQ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function `f : E → ℝ` is **piecewise-quadratic on `P`** (`IsPQOn P f`) if `P` is a compact
polyhedron admitted as the space of a finite polytopal complex on every cell of which `f` agrees
with a polynomial of degree at most `2`. -/
@[expose] def IsPQOn (P : Set E) (f : E → ℝ) : Prop :=
  IsPiecewiseOn IsQuadraticOn P f

theorem IsPQOn.congr {P : Set E} {f f' : E → ℝ} (hf : IsPQOn P f) (heq : Set.EqOn f' f P) :
    IsPQOn P f' :=
  isPiecewiseOn_congr (fun heq hq => hq.congr heq) hf heq

theorem IsPQOn.of_isPLOn {P : Set E} {f : E → ℝ} (hf : IsPLOn P f) : IsPQOn P f :=
  hf.elim fun C ⟨hC, haff⟩ => ⟨C, hC, fun Q hQ => IsQuadraticOn.of_isAffineOn (haff Q hQ)⟩

theorem IsPQOn.neg {P : Set E} {f : E → ℝ} (hf : IsPQOn P f) : IsPQOn P (fun x => -f x) :=
  hf.elim fun C ⟨hC, hquad⟩ => ⟨C, hC, fun Q hQ => (hquad Q hQ).neg⟩

theorem IsPQOn.smul (c : ℝ) {P : Set E} {f : E → ℝ} (hf : IsPQOn P f) :
    IsPQOn P (fun x => c * f x) :=
  hf.elim fun C ⟨hC, hquad⟩ => ⟨C, hC, fun Q hQ => (hquad Q hQ).smul c⟩

theorem isPQOn_empty (f : E → ℝ) : IsPQOn (∅ : Set E) f :=
  isPiecewiseOn_empty IsQuadraticOn f

end GeneralPQ

section FiniteDimPQ

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPQOn.isPolyhedron {P : Set E} {f : E → ℝ} (hf : IsPQOn P f) : IsPolyhedron P :=
  let ⟨C, hC, _⟩ := hf
  isPolyhedron_iff_exists_polytopalComplex.2 ⟨C, hC⟩

theorem isPQOn_iff_simplicialComplex {P : Set E} {f : E → ℝ} :
    IsPQOn P f ↔ ∃ K : Geometry.SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = P ∧
      ∀ s ∈ K.faces, IsQuadraticOn f (convexHull ℝ (s : Set E)) :=
  isPiecewiseOn_iff_simplicialComplex (fun hsub hq => hq.mono hsub)

theorem isPQOn_iff_finite_polytope_cover {P : Set E} {f : E → ℝ} :
    IsPQOn P f ↔ ∃ ℱ : Set (Set E), ℱ.Finite ∧
      (∀ Q ∈ ℱ, IsPolytope Q ∧ IsQuadraticOn f Q) ∧ P = ⋃ Q ∈ ℱ, Q :=
  isPiecewiseOn_iff_finite_polytope_cover (fun hsub hq => hq.mono hsub)

theorem IsPQOn.affineMap {P : Set E} (hP : IsPolyhedron P) (g : E →ᵃ[ℝ] ℝ) : IsPQOn P g :=
  IsPQOn.of_isPLOn (IsPLOn.affineMap hP g)

theorem IsPQOn.const {P : Set E} (hP : IsPolyhedron P) (c : ℝ) : IsPQOn P (fun _ => c) :=
  IsPQOn.of_isPLOn (IsPLOn.const hP c)

theorem IsPQOn.quadraticMap {P : Set E} (hP : IsPolyhedron P) (Q : QuadraticMap ℝ E ℝ) :
    IsPQOn P Q := by
  obtain ⟨C, hC⟩ := isPolyhedron_iff_exists_polytopalComplex.1 hP
  exact ⟨C, hC, fun R _ => isQuadraticOn_of_quadraticMap Q R⟩

theorem IsPQOn.continuousOn {P : Set E} {f : E → ℝ} (hf : IsPQOn P f) : ContinuousOn f P :=
  isPiecewiseOn_continuousOn (fun h => h.continuousOn) hf

theorem IsPQOn.of_finiteCover {ι : Type*} [Finite ι] {P : Set E} {Q : ι → Set E}
    {f : E → ℝ} (hcov : (⋃ i, Q i) = P) (hf : ∀ i, IsPQOn (Q i) f) : IsPQOn P f :=
  isPiecewiseOn_of_finiteCover (fun hsub hq => hq.mono hsub) hcov hf

open Classical in
theorem IsPQOn.piecewise_union {P Q : Set E} {f g : E → ℝ} (hf : IsPQOn P f) (hg : IsPQOn Q g)
    (hagree : ∀ x ∈ P ∩ Q, f x = g x) :
    IsPQOn (P ∪ Q) (fun x => if x ∈ P then f x else g x) :=
  isPiecewiseOn_piecewise_union (fun hsub hq => hq.mono hsub)
    (fun heq hq => hq.congr heq) hf hg hagree

theorem IsPQOn.restrict {P Q : Set E} {f : E → ℝ} (hf : IsPQOn P f)
    (hQ : IsPolyhedron Q) (hQP : Q ⊆ P) : IsPQOn Q f :=
  isPiecewiseOn_restrict (fun hsub hq => hq.mono hsub) hf hQ hQP

theorem IsPQOn.exists_common_complex {P : Set E} {f g : E → ℝ}
    (hf : IsPQOn P f) (hg : IsPQOn P g) :
    ∃ C : PolytopalComplex E, C.space = P ∧
      (∀ Q ∈ C.cells, IsQuadraticOn f Q) ∧ (∀ Q ∈ C.cells, IsQuadraticOn g Q) :=
  isPiecewiseOn_exists_common_complex (fun hsub hu => hu.mono hsub)
    (fun hsub hv => hv.mono hsub) hf hg

theorem IsPQOn.add {P : Set E} {f g : E → ℝ} (hf : IsPQOn P f) (hg : IsPQOn P g) :
    IsPQOn P (fun x => f x + g x) := by
  obtain ⟨C, hC, hqf, hqg⟩ := hf.exists_common_complex hg
  exact ⟨C, hC, fun Q hQ => (hqf Q hQ).add (hqg Q hQ)⟩

theorem IsPQOn.sub {P : Set E} {f g : E → ℝ} (hf : IsPQOn P f) (hg : IsPQOn P g) :
    IsPQOn P (fun x => f x - g x) :=
  (hf.add hg.neg).congr fun _ _ => sub_eq_add_neg _ _

theorem IsPQOn.sum {ι : Type*} (s : Finset ι) {P : Set E} (hP : IsPolyhedron P)
    {f : ι → E → ℝ} (hf : ∀ i ∈ s, IsPQOn P (f i)) :
    IsPQOn P (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction with
  | empty => exact (IsPQOn.const hP 0).congr fun _ _ => Finset.sum_empty
  | @insert a s ha ih =>
    exact ((hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))).congr fun _ _ => Finset.sum_insert ha

/-- The pointwise product of two real-valued PL functions on `P` is PQ on `P` (cited in issue #4325
notes as `STOC 1056 Lemma 3.1`, unverified against the primary manuscript). -/
theorem IsPQOn.mul_of_isPLOn {P : Set E} {f g : E → ℝ}
    (hf : IsPLOn P f) (hg : IsPLOn P g) : IsPQOn P (fun x => f x * g x) := by
  obtain ⟨C, hC, haff_f, haff_g⟩ := hf.exists_common_complex hg
  exact ⟨C, hC, fun Q hQ =>
    IsQuadraticOn.mul_of_isAffineOn (haff_f Q hQ) (haff_g Q hQ)⟩

/-- Any finite sum of pairwise products of real-valued PL functions on `P` is PQ on `P`. -/
theorem IsPQOn.sum_mul_of_isPLOn {ι : Type*} (s : Finset ι) {P : Set E} (hP : IsPolyhedron P)
    {f g : ι → E → ℝ} (hf : ∀ i ∈ s, IsPLOn P (f i)) (hg : ∀ i ∈ s, IsPLOn P (g i)) :
    IsPQOn P (fun x => ∑ i ∈ s, f i x * g i x) :=
  IsPQOn.sum s hP fun i hi => IsPQOn.mul_of_isPLOn (hf i hi) (hg i hi)

/-- Precomposing a PQ map with a PL map preserves piecewise-quadraticity. -/
theorem IsPQOn.comp_isPLOn [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {P : Set E} {T : Set F} {f : E → F} {g : F → ℝ}
    (hf : IsPLOn P f) (hg : IsPQOn T g) (hmaps : MapsTo f P T) :
    IsPQOn P (g ∘ f) := by
  rcases hg with ⟨CT, hCT, hq_g⟩
  obtain ⟨D, hDsp, hDcell⟩ := hf.exists_preimage_complex CT
  refine ⟨D, hDsp.trans (hCT ▸ Set.inter_eq_left.2 hmaps), fun S hS => ?_⟩
  obtain ⟨⟨a, ha⟩, R, hR, hsubR⟩ := hDcell S hS
  exact ((hq_g R hR).comp_affineMap a fun x hx => hsubR ⟨x, hx, ha hx⟩).congr
    fun x hx => by simp only [Function.comp_apply, ha hx]

/-- Every PQ function admits a finite triangulation on each simplex of which it agrees with an
`MvPolynomial` of `totalDegree ≤ 2` in the coordinates of a given basis `e`. -/
theorem IsPQOn.exists_triangulation_mvPolynomial_basis {ι : Type*} [Finite ι]
    (e : Module.Basis ι ℝ E) {P : Set E} {f : E → ℝ} (hf : IsPQOn P f) :
    ∃ K : Geometry.SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = P ∧
      ∃ p : Finset E → MvPolynomial ι ℝ,
        ∀ s ∈ K.faces, (p s).totalDegree ≤ 2 ∧
          Set.EqOn f (fun x => MvPolynomial.eval (e.equivFun x) (p s))
            (convexHull ℝ (s : Set E)) := by
  classical
  obtain ⟨K, hfin, hsp, hquad⟩ := isPQOn_iff_simplicialComplex.1 hf
  choose! p hp heq using fun s hs => (isQuadraticOn_iff_mvPolynomial_basis e).1 (hquad s hs)
  exact ⟨K, hfin, hsp, p, fun s hs => ⟨hp s hs, heq s hs⟩⟩

/-- Specialization of `IsPQOn.exists_triangulation_mvPolynomial_basis` to `Fin d → ℝ`. -/
theorem IsPQOn.exists_triangulation_mvPolynomial_pi {d : ℕ} {P : Set (Fin d → ℝ)}
    {f : (Fin d → ℝ) → ℝ} (hf : IsPQOn P f) :
    ∃ K : Geometry.SimplicialComplex ℝ (Fin d → ℝ), K.faces.Finite ∧ K.space = P ∧
      ∃ p : Finset (Fin d → ℝ) → MvPolynomial (Fin d) ℝ,
        ∀ s ∈ K.faces, (p s).totalDegree ≤ 2 ∧
          Set.EqOn f (fun x => MvPolynomial.eval x (p s))
            (convexHull ℝ (s : Set (Fin d → ℝ))) :=
  hf.exists_triangulation_mvPolynomial_basis (Pi.basisFun ℝ (Fin d))

/-- Every PQ function on `P` can be presented as a finite list of convex polytope cells covering
`P` together with a multivariate polynomial of `totalDegree ≤ 2` (in coordinates of basis `e`)
matching `f` on each cell. -/
theorem IsPQOn.exists_cell_list_mvPolynomial_basis {ι : Type*} [Finite ι]
    (e : Module.Basis ι ℝ E) {P : Set E} {f : E → ℝ} (hf : IsPQOn P f) :
    ∃ L : List (Set E × MvPolynomial ι ℝ),
      (∀ S p, (S, p) ∈ L → IsPolytope S ∧ p.totalDegree ≤ 2 ∧
        Set.EqOn f (fun x => MvPolynomial.eval (e.equivFun x) p) S) ∧
      (⋃ S ∈ L.map Prod.fst, S) = P := by
  classical
  obtain ⟨K, hfin, hsp, p, hp⟩ := hf.exists_triangulation_mvPolynomial_basis e
  refine ⟨hfin.toFinset.toList.map (fun s : Finset E => (convexHull ℝ (s : Set E), p s)), ?_, ?_⟩
  · rintro _ _ hSq
    rcases List.mem_map.1 hSq with ⟨s, hs, ⟨⟩⟩
    exact ⟨isPolytope_convexHull s.finite_toSet, hp s (by simpa using hs)⟩
  · ext x
    simp [← hsp, Geometry.SimplicialComplex.space]

/-- Specialization of `IsPQOn.exists_cell_list_mvPolynomial_basis` to `Module.finBasis ℝ E`. -/
theorem IsPQOn.exists_cell_list_mvPolynomial {P : Set E} {f : E → ℝ} (hf : IsPQOn P f) :
    ∃ L : List (Set E × MvPolynomial (Fin (Module.finrank ℝ E)) ℝ),
      (∀ S p, (S, p) ∈ L → IsPolytope S ∧ p.totalDegree ≤ 2 ∧
        Set.EqOn f (fun x => MvPolynomial.eval ((Module.finBasis ℝ E).equivFun x) p) S) ∧
      (⋃ S ∈ L.map Prod.fst, S) = P :=
  hf.exists_cell_list_mvPolynomial_basis (Module.finBasis ℝ E)

/-- On `Fin d → ℝ`, every PQ function on `P` admits a finite list of convex polytope cells
covering `P` on each of which `f` agrees with an `MvPolynomial (Fin d) ℝ` of `totalDegree ≤ 2`. -/
theorem IsPQOn.exists_cell_list_mvPolynomial_pi {d : ℕ} {P : Set (Fin d → ℝ)}
    {f : (Fin d → ℝ) → ℝ} (hf : IsPQOn P f) :
    ∃ L : List (Set (Fin d → ℝ) × MvPolynomial (Fin d) ℝ),
      (∀ S p, (S, p) ∈ L → IsPolytope S ∧ p.totalDegree ≤ 2 ∧
        Set.EqOn f (fun x => MvPolynomial.eval x p) S) ∧
      (⋃ S ∈ L.map Prod.fst, S) = P :=
  hf.exists_cell_list_mvPolynomial_basis (Pi.basisFun ℝ (Fin d))

/-- Coordinate-free finite cell list for a PQ function: a finite list of polytopes covering `P`
together with pairs `(Q, L)` of a `QuadraticMap` and an `AffineMap` agreeing with `f` on each
cell. -/
theorem IsPQOn.exists_cell_list_quadraticMap {P : Set E} {f : E → ℝ} (hf : IsPQOn P f) :
    ∃ L : List (Set E × QuadraticMap ℝ E ℝ × (E →ᵃ[ℝ] ℝ)),
      (∀ S Q L', (S, Q, L') ∈ L → IsPolytope S ∧ Set.EqOn f (fun x => Q x + L' x) S) ∧
      (⋃ S ∈ L.map Prod.fst, S) = P := by
  classical
  rcases hf with ⟨C, hC, hquad⟩
  choose! Q L hQL using fun S hS => isQuadraticOn_iff_quadraticMap_add_affineMap.1 (hquad S hS)
  refine ⟨C.finite_cells.toFinset.toList.map (fun S : Set E => (S, Q S, L S)), ?_, ?_⟩
  · rintro _ _ _ hmem
    obtain ⟨S₀, hS₀, rfl, rfl, rfl⟩ := List.mem_map.1 hmem
    exact ⟨C.isPolytope_of_mem (by simpa using hS₀), hQL _ (by simpa using hS₀)⟩
  · exact Set.ext fun _ => by simp [← hC, PolytopalComplex.mem_space_iff]

end FiniteDimPQ

end Cslib.Polyhedra
