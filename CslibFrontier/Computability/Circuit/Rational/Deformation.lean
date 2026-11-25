/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Rational.BlockDivision

/-!
# Polynomial deformation of the quantum lift

The finite Fourier (quantum) lift of a `d × d` matrix, written with the Weyl basis, is turned
into an honest polynomial matrix: the Fourier frequencies become exponents of two commuting
indeterminates. Evaluating at `(1, 1)` recovers the original matrix, while embedding into Hahn
series recovers the division-ring representation of `QuantumMatrices`. The rank gap of
`BlockDivision` then shows that the determinant of the polynomial lift of a block matrix of
large rank is a nonzero polynomial. A third indeterminate carries the Taylor parameter of the
padded test matrices, giving the three-variable pencil polynomial whose determinant the
generator must avoid.

## Main definitions

* `Rational.QuantumLift.polynomialLift`: the two-parameter polynomial Fourier lift.
* `Rational.QuantumLift.blockPolynomial`, `Rational.QuantumLift.blockOriginal`: the flattened
  lifted and original block matrices.
* `Rational.ThreeLift.coeffP`, `Rational.ThreeLift.uni`, `Rational.ThreeLift.lift`: the
  three-parameter lift of a matrix of univariate polynomials and its Fourier coefficients.
* `Rational.ThreeLift.specialize`: specialization of the first parameter into a field.
* `Rational.ThreeLift.linear`: the three-parameter lift as a `K`-linear map.
* `Rational.PencilDeformation.test`, `Rational.PencilDeformation.polyBlocks`,
  `Rational.PencilDeformation.polynomial`: the polynomial test blocks and three-variable
  pencil matrix.

## Main results

* `Rational.QuantumLift.blockPolynomial_det_ne_zero`: large rank forces a nonzero determinant
  of the polynomial lift.
* `Rational.PencilDeformation.det_ne_zero`: the three-variable pencil determinant is nonzero.
* `Rational.PencilDeformation.entry_degree`: its entries have total degree at most `3 * M`.

## References

* Adapted from OpenAI's formalization [OpenAI2026RationalHitting] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Computability/RationalHitting/Deformation.lean), via the complexitylib port
  [Schlesinger2026RationalHitting] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.Circuits

namespace Rational.QuantumLift
open HahnSeries Matrix MvPolynomial
open Rational.QuantumMatrices Rational.PolynomialHahn
open Rational.BlockDivision
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K)

/-- The two-parameter polynomial lift. -/
def polynomialLift (R : Matrix (ZMod d) (ZMod d) K) :
    Matrix (ZMod d) (ZMod d) (MvPolynomial (Fin 2) K) := fun i j =>
  ∑ a : ZMod d, ∑ b : ZMod d,
    monomial (Finsupp.single 0 a.val + Finsupp.single 1 b.val)
      (fourierCoeff χ R a b * weyl χ a b i j)

omit [CharZero K] in
/-- Embedding `polynomialLift χ R` entrywise into Hahn series yields
`representation χ (liftD χ R)`. -/
lemma polynomialLift_embed (R : Matrix (ZMod d) (ZMod d) K) :
    PolynomialHahn.embed.mapMatrix (polynomialLift χ R) = representation χ (liftD χ R) := by
  ext i j g
  change (PolynomialHahn.embed (polynomialLift χ R i j)).coeff g = (lift χ R).coeff g i j
  simp only [polynomialLift, map_sum, HahnSeries.coeff_sum, embed_monomial, lift,
    Matrix.sum_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [show exponent (Finsupp.single 0 a.val + Finsupp.single 1 b.val) =
    toLex ((a.val : ℤ), (b.val : ℤ)) by simp [exponent]]
  simp only [HahnSeries.coeff_single]; split_ifs <;> rfl

/-- Evaluating `polynomialLift χ R` at `(1, 1)` recovers `R` when `χ` is primitive. -/
lemma polynomialLift_specialize (hχ : χ.IsPrimitive) (R : Matrix (ZMod d) (ZMod d) K) :
    (MvPolynomial.aeval (fun _ : Fin 2 => (1 : K))).toRingHom.mapMatrix
      (polynomialLift χ R) = R := by
  ext i j
  simpa [polynomialLift, eval_monomial, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using
    congrFun (congrFun (fourier_reconstruction χ hχ R) i) j

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Flatten a block matrix after applying the polynomial lift to each block. -/
def blockPolynomial (A : Matrix m m (Matrix (ZMod d) (ZMod d) K)) :
    Matrix (m × ZMod d) (m × ZMod d) (MvPolynomial (Fin 2) K) :=
  fun i j => polynomialLift χ (A i.1 j.1) i.2 j.2

/-- Flatten the original block matrix over the coefficient field. -/
def blockOriginal (A : Matrix m m (Matrix (ZMod d) (ZMod d) K)) :
    Matrix (m × ZMod d) (m × ZMod d) K := fun i j => A i.1 j.1 i.2 j.2

omit [CharZero K] in
private lemma blockPolynomial_embed (A : Matrix m m (Matrix (ZMod d) (ZMod d) K)) :
    PolynomialHahn.embed.mapMatrix (blockPolynomial χ A) =
      blockEmbedding (representation χ) (fun i j => liftD χ (A i j)) := by
  funext ⟨i, a⟩ ⟨j, b⟩
  exact congrFun (congrFun (polynomialLift_embed χ (A i j)) a) b

private lemma blockPolynomial_specialize (hχ : χ.IsPrimitive)
    (A : Matrix m m (Matrix (ZMod d) (ZMod d) K)) :
    (MvPolynomial.aeval (fun _ : Fin 2 => (1 : K))).toRingHom.mapMatrix
      (blockPolynomial χ A) = blockOriginal A := by
  funext ⟨i, a⟩ ⟨j, b⟩
  exact congrFun (congrFun (polynomialLift_specialize χ hχ (A i j)) a) b

/-- The rank gap forces the determinant of the actual polynomial lift to be
nonzero. The Hahn division ring is only a proof device; the resulting polynomial
is the original finite Fourier lift, not a new generator. -/
theorem blockPolynomial_det_ne_zero (hχ : χ.IsPrimitive)
    (A : Matrix m m (Matrix (ZMod d) (ZMod d) K))
    (hm : 1 ≤ Fintype.card m)
    (hA : (Fintype.card m - 1) * d < (blockOriginal A).rank) :
    (blockPolynomial χ A).det ≠ 0 := by
  have hrank := Rational.RankSpecialization.rank_le
    (MvPolynomial.aeval (fun _ : Fin 2 => (1 : K))) PolynomialHahn.embed
    PolynomialHahn.embed_injective (blockPolynomial χ A)
  rw [blockPolynomial_specialize χ hχ, blockPolynomial_embed] at hrank
  have hu := isUnit_of_rank_gt (representation χ) (fun i j => liftD χ (A i j)) hm
    (by simpa [ZMod.card] using hA.trans_le hrank)
  exact fun hz => ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
    (by rw [← blockPolynomial_embed, ← RingHom.map_det, hz, map_zero])

end
end Rational.QuantumLift

namespace Rational.ThreeLift
open Matrix Polynomial MvPolynomial
open QuantumMatrices QuantumLift
open scoped BigOperators
noncomputable section
variable {K E : Type*} [Field K] [Field E] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K)

/-- Coefficient polynomials for the exact cyclic-diagonal Fourier transform. -/
def coeffP (R : Matrix (ZMod d) (ZMod d) K[X]) (a b : ZMod d) : K[X] :=
  Polynomial.C ((d : K)⁻¹) * ∑ j, Polynomial.C (χ (-a * j)) * R j (j - b)

/-- Embed the univariate parameter as the first of three polynomial variables. -/
def uni : K[X] →+* MvPolynomial (Fin 3) K :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)

/-- The three-parameter polynomial lift, before specialization. -/
def lift (R : Matrix (ZMod d) (ZMod d) K[X]) :
    Matrix (ZMod d) (ZMod d) (MvPolynomial (Fin 3) K) := fun i j =>
  ∑ a : ZMod d, ∑ b : ZMod d,
    uni (coeffP χ R a b) * MvPolynomial.C (weyl χ a b i j) *
      MvPolynomial.X 1 ^ a.val * MvPolynomial.X 2 ^ b.val

/-- Embed t into a coefficient field, leaving p,r polynomial indeterminates. -/
def specialize (φ : K →+* E) (t : E) :
    MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 2) E :=
  eval₂Hom (MvPolynomial.C.comp φ) (Fin.cases (MvPolynomial.C t) MvPolynomial.X)

private lemma specialize_uni (φ : K →+* E) (t : E) (p : K[X]) :
    specialize φ t (uni p) = MvPolynomial.C (p.eval₂ φ t) :=
  congrFun (congrArg DFunLike.coe <| Polynomial.ringHom_ext
    (f := (specialize φ t).comp uni) (g := MvPolynomial.C.comp (Polynomial.eval₂RingHom φ t))
    (fun _ => by simp [specialize, uni]) (by simp [specialize, uni])) p

/-- Evaluating `coeffP χ R a b` at `t` along `φ` gives the `(a, b)` Fourier coefficient of `R`
evaluated at `t`. -/
lemma coeffP_eval (φ : K →+* E) (t : E)
    (R : Matrix (ZMod d) (ZMod d) K[X]) (a b : ZMod d) :
    (coeffP χ R a b).eval₂ φ t =
      QuantumMatrices.fourierCoeff (φ.toMonoidHom.compAddChar χ)
        ((Polynomial.eval₂RingHom φ t).mapMatrix R) a b := by
  simp [coeffP, QuantumMatrices.fourierCoeff, Polynomial.eval₂_mul, Polynomial.eval₂_finsetSum]

omit [NeZero d] in
private lemma weyl_map (φ : K →+* E) (a b i j : ZMod d) :
    φ (weyl χ a b i j) = weyl (φ.toMonoidHom.compAddChar χ) a b i j := by
  by_cases h : i = j + b <;> simp [weyl, h]

private lemma specialize_lift (φ : K →+* E) (t : E)
    (R : Matrix (ZMod d) (ZMod d) K[X]) :
    (specialize φ t).mapMatrix (lift χ R) =
      polynomialLift (φ.toMonoidHom.compAddChar χ) ((Polynomial.eval₂RingHom φ t).mapMatrix R) := by
  ext1 i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, lift, map_sum, map_mul, map_pow,
    specialize_uni, coeffP_eval]
  simp only [specialize, eval₂Hom_X', eval₂Hom_C, RingHom.comp_apply, weyl_map, polynomialLift]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [MvPolynomial.monomial_add_single, ← MvPolynomial.C_mul_X_pow_eq_monomial, map_mul]
  rfl

private lemma uni_totalDegree_le (p : K[X]) : (uni p).totalDegree ≤ p.natDegree := by
  classical
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow]
  simp only [map_sum, map_mul, map_pow, uni, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
    Polynomial.eval₂_X]
  refine totalDegree_finsetSum_le fun j hj => (totalDegree_mul _ _).trans ?_
  exact (Nat.add_le_add (totalDegree_C _).le (totalDegree_pow _ _)).trans
    (by simp [Nat.le_of_lt_succ (Finset.mem_range.mp hj)])

private lemma coeffP_natDegree_le (R : Matrix (ZMod d) (ZMod d) K[X]) (D : ℕ)
    (hR : ∀ i j, (R i j).natDegree ≤ D) (a b : ZMod d) :
    (coeffP χ R a b).natDegree ≤ D :=
  (Polynomial.natDegree_C_mul_le _ _).trans <|
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun _ _ =>
      (Polynomial.natDegree_C_mul_le _ _).trans (hR _ _)

private lemma lift_totalDegree_le (R : Matrix (ZMod d) (ZMod d) K[X]) (D : ℕ)
    (hR : ∀ i j, (R i j).natDegree ≤ D) (i j : ZMod d) :
    (lift χ R i j).totalDegree ≤ D + 2 * (d - 1) := by
  refine totalDegree_finsetSum_le fun a _ => totalDegree_finsetSum_le fun b _ => ?_
  refine (totalDegree_mul _ _).trans ((Nat.add_le_add
    ((totalDegree_mul _ _).trans (Nat.add_le_add
      ((totalDegree_mul _ _).trans (Nat.add_le_add ((uni_totalDegree_le _).trans
        (coeffP_natDegree_le χ R D hR a b)) (totalDegree_C _).le))
      (totalDegree_pow _ _)))
    (totalDegree_pow _ _)).trans ?_)
  simp only [totalDegree_X, Nat.mul_one, Nat.add_zero]
  have := ZMod.val_lt a; have := ZMod.val_lt b; omega

end
end Rational.ThreeLift

namespace Rational.PencilDeformation
open Matrix Polynomial MvPolynomial
open TestPolynomial LaurentReduction
open scoped BigOperators Rational.PolynomialHahn
noncomputable section
variable {K E : Type*} [Field K] [CharZero K] [Field E] [CharZero E]
variable {w q M N : ℕ} [NeZero M]

/-- The truncated polynomial test matrix, reindexed by cyclic indices. -/
def test (M N : ℕ) [NeZero M] (a : K) : Matrix (ZMod M) (ZMod M) K[X] :=
  (padded M N a).reindex (ZMod.finEquiv M).toEquiv (ZMod.finEquiv M).toEquiv

/-- Combine coefficient matrices with polynomial test blocks. -/
def polyBlocks (A : Fin w → Matrix (Fin q) (Fin q) K) (points : Fin w → K) :
    Matrix (Fin q) (Fin q) (Matrix (ZMod M) (ZMod M) K[X]) :=
  fun α β => ∑ i, A i α β • test M N (points i)

/-- The polynomial matrix obtained by applying the three-parameter lift. -/
def polynomial (χ : AddChar (ZMod M) K)
    (A : Fin w → Matrix (Fin q) (Fin q) K) (points : Fin w → K) :
    Matrix (Fin q × ZMod M) (Fin q × ZMod M) (MvPolynomial (Fin 3) K) :=
  fun a b => ThreeLift.lift χ (polyBlocks (M := M) (N := N) A points a.1 b.1) a.2 b.2

omit [CharZero K] [CharZero E] in
private lemma specialize (χ : AddChar (ZMod M) K)
    (φ : K →+* E) (t : E) (A : Fin w → Matrix (Fin q) (Fin q) K) (points : Fin w → K) :
    (ThreeLift.specialize φ t).mapMatrix (polynomial (N := N) χ A points) =
      QuantumLift.blockPolynomial (φ.toMonoidHom.compAddChar χ)
        (fun α β => (Polynomial.eval₂RingHom φ t).mapMatrix
          (polyBlocks (M := M) (N := N) A points α β)) := by
  funext ⟨α, i⟩ ⟨β, j⟩
  exact congrFun (congrFun (ThreeLift.specialize_lift χ φ t (polyBlocks A points α β)) i) j

omit [CharZero K] [CharZero E] in
private lemma raw_specialize (φ : K →+* E)
    (A : Fin w → Matrix (Fin q) (Fin q) K) (points : Fin w → K) :
    QuantumLift.blockOriginal
        (fun α β => (Polynomial.eval₂RingHom ((HahnSeries.C : E →+* F E).comp φ)
          (HahnSeries.single 1 1)).mapMatrix (polyBlocks (M := M) (N := N) A points α β)) =
      (PaddedRank.raw (fun i => ((HahnSeries.C : E →+* F E).comp φ).mapMatrix (A i))
        (fun i => embed.mapMatrix (padded M N (φ (points i))))).reindex
          (Equiv.prodCongr (Equiv.refl (Fin q)) (ZMod.finEquiv M).toEquiv)
          (Equiv.prodCongr (Equiv.refl (Fin q)) (ZMod.finEquiv M).toEquiv) := by
  funext ⟨α, j⟩ ⟨β, k⟩
  simp only [QuantumLift.blockOriginal, polyBlocks, Matrix.sum_apply, Matrix.smul_apply,
    Polynomial.smul_eq_C_mul, RingHom.mapMatrix_apply, Matrix.map_apply,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Matrix.reindex_apply, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Equiv.refl_symm, test]
  exact Finset.sum_congr rfl fun i _ => congrArg (_ * ·) (eval₂_padded ..)

omit [CharZero K] in
/-- The three-variable determinant is nonzero. The witness can lie over an
extension field and is never an input to the generator. -/
theorem det_ne_zero (χ : AddChar (ZMod M) K) (hχ : χ.IsPrimitive)
    (φ : K →+* E) (points : Fin w → K) (hp : Function.Injective points)
    (A : Fin w → Matrix (Fin q) (Fin q) K)
    (B e : ℕ) (hw : 1 ≤ w) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hN : 1 ≤ N) (hMN : M = N + 2 * w ^ 3 * B) (hM : B * (2 * w ^ 3 * B) < M) (he : 0 < e)
    (X : Fin w → Matrix (Fin e) (Fin e) (F E))
    (hX : Function.Injective (Rectangular.blockEval
      (fun i => ((HahnSeries.C : E →+* F E).comp φ).mapMatrix (A i)) X)) :
    (polynomial (N := N) χ A points).det ≠ 0 := by
  let ψ : K →+* F E := (HahnSeries.C : E →+* F E).comp φ
  let τ : F E := HahnSeries.single 1 1
  have hr := PaddedRank.rank_ge w B M N q e hw hN hMN hqB he
    (fun i => φ (points i)) (φ.injective.comp hp) (fun i => ψ.mapMatrix (A i)) X hX
  have hd := QuantumLift.blockPolynomial_det_ne_zero (ψ.toMonoidHom.compAddChar χ)
    (hχ.compMulHom_of_isPrimitive ψ.injective)
    (fun α β => (Polynomial.eval₂RingHom ψ τ).mapMatrix
      (polyBlocks (M := M) (N := N) A points α β))
    (by simpa using hq) (by
      rw [Fintype.card_fin, raw_specialize φ A points, Matrix.rank_reindex]
      exact (PaddedRank.numeric_gap w B M N q hq hqB hMN hM).trans_le hr)
  exact fun hz => hd (by rw [← specialize χ ψ τ, ← RingHom.map_det, hz, map_zero])

omit [CharZero K] in
private lemma polyBlocks_degree (A : Fin w → Matrix (Fin q) (Fin q) K) (points : Fin w → K)
    (α β : Fin q) (i j : ZMod M) :
    (polyBlocks (M := M) (N := N) A points α β i j).natDegree ≤ M - 1 := by
  simp only [polyBlocks, Matrix.sum_apply, Matrix.smul_apply, Polynomial.smul_eq_C_mul]
  exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun r _ =>
    (Polynomial.natDegree_C_mul_le _ _).trans (padded_natDegree_le M N (points r) _ _)

omit [CharZero K] in
/-- Every entry of `polynomial χ A points` has total degree at most `3 * M`. -/
lemma entry_degree (χ : AddChar (ZMod M) K)
    (A : Fin w → Matrix (Fin q) (Fin q) K) (points : Fin w → K)
    (a b : Fin q × ZMod M) :
    (polynomial (N := N) χ A points a b).totalDegree ≤ 3 * M :=
  (ThreeLift.lift_totalDegree_le χ (polyBlocks (M := M) (N := N) A points a.1 b.1)
    (M - 1) (polyBlocks_degree A points a.1 b.1) a.2 b.2).trans (by omega)

end
end Rational.PencilDeformation

namespace Rational.ThreeLift
open Matrix Polynomial MvPolynomial
open QuantumMatrices
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K)

private lemma coeffP_smul (c : K) (R : Matrix (ZMod d) (ZMod d) K[X]) (a b : ZMod d) :
    coeffP χ (c • R) a b = Polynomial.C c * coeffP χ R a b := by
  simp only [coeffP, Matrix.smul_apply, Polynomial.smul_eq_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The three-parameter lift of the zero matrix is zero. -/
lemma lift_zero : lift χ 0 = 0 := by
  funext i j
  simp [lift, coeffP]

/-- The three-parameter lift is additive. -/
lemma lift_add (R S : Matrix (ZMod d) (ZMod d) K[X]) :
    lift χ (R + S) = lift χ R + lift χ S := by
  funext i j
  simp [lift, coeffP, map_add, add_mul, mul_add, Finset.sum_add_distrib]

/-- The three-parameter lift commutes with scalar multiplication by constants in `K`. -/
lemma lift_smul (c : K) (R : Matrix (ZMod d) (ZMod d) K[X]) :
    lift χ (c • R) = c • lift χ R := by
  funext i j
  simp only [lift, coeffP_smul, map_mul, uni, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
    Matrix.smul_apply, MvPolynomial.smul_eq_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The three-parameter lift `lift χ` as a `K`-linear map. -/
def linear : Matrix (ZMod d) (ZMod d) K[X] →ₗ[K]
    Matrix (ZMod d) (ZMod d) (MvPolynomial (Fin 3) K) where
  toFun := lift χ
  map_add' := lift_add χ
  map_smul' c R := by simpa using lift_smul χ c R

/-- The three-parameter lift commutes with finite sums. -/
lemma lift_sum {ι : Type*} (S : Finset ι) (R : ι → Matrix (ZMod d) (ZMod d) K[X]) :
    lift χ (∑ i ∈ S, R i) = ∑ i ∈ S, lift χ (R i) := map_sum (linear χ) R S

end

end Rational.ThreeLift

end Cslib.Circuits
