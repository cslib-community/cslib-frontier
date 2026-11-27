/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Rational.SmallExpansion
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rectangular kernels of block evaluations

Block evaluations of `∑ᵢ Aᵢ ⊗ Xᵢ`, built from coefficient matrices `Aᵢ` and square witness
matrices `Xᵢ`. If such an evaluation is injective, the matrices `Aᵢ` cannot map a subspace into a
smaller one. Combined with small-subspace expansion, this shows that the reverse-Taylor tests
have no nonzero kernel family of bounded support whenever the same coefficients admit an
invertible block witness.

## Main definitions

* `Rectangular.blockEval`: the block evaluation map on `Fin e → Fin q → F`.
* `Rectangular.blockMatrix`: the corresponding sum of Kronecker products.
* `Rectangular.componentSpace`, `Rectangular.component`, `Rectangular.coefficientMatrix`: the span
  of a family, its members in that span, and their coordinates in a basis of that span.
* `Rectangular.imageCombination`, `Rectangular.concatMatrix`: the combined images under several
  maps, and the concatenated coefficient matrix.

## Main results

* `Rectangular.no_shrunk_subspace`: an injective block evaluation forbids shrinking subspaces.
* `Rectangular.kernel_impossible`: an expanding kernel family contradicts injectivity.
* `Rectangular.blockEval_injective_of_isUnit`: an invertible block matrix gives an injective
  block evaluation.
* `RectangularExpansion.rectangular_kernel_zero`: the reverse-Taylor tests have trivial
  bounded-support kernel families.

## References

* Adapted from OpenAI's formalization [OpenAI2026RationalHitting] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Computability/RationalHitting/Rectangular.lean), via the complexitylib port
  [Schlesinger2026RationalHitting] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.Circuits

namespace Rational.Rectangular
open Module Matrix
open scoped BigOperators Kronecker
noncomputable section
variable {F : Type*} [Field F]

/-- The ordinary Kronecker evaluation, with the two vector indices curried in
reverse order. This is only a coordinate convention. -/
def blockEval {w q e : ℕ} (A : Fin w → Matrix (Fin q) (Fin q) F)
    (X : Fin w → Matrix (Fin e) (Fin e) F) :
    (Fin e → Fin q → F) →ₗ[F] (Fin e → Fin q → F) where
  toFun v β := ∑ i, ∑ δ, X i β δ • (A i).mulVec (v δ)
  map_add' v u := by
    funext β
    simp only [Pi.add_apply, Matrix.mulVec_add, smul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    funext β
    simp only [Pi.smul_apply, RingHom.id_apply, Matrix.mulVec_smul,
      Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro δ _
    rw [mul_comm]

/-- If `blockEval A X` is injective with `0 < e` and every `A i` maps `V` into `W`, then
`finrank F V ≤ finrank F W`. -/
lemma no_shrunk_subspace {w q e : ℕ} (he : 0 < e)
    (A : Fin w → Matrix (Fin q) (Fin q) F)
    (X : Fin w → Matrix (Fin e) (Fin e) F)
    (hX : Function.Injective (blockEval A X))
    (V W : Submodule F (Fin q → F))
    (hVW : ∀ i, V.map (A i).mulVecLin ≤ W) : finrank F V ≤ finrank F W := by
  let g : (Fin e → V) →ₗ[F] (Fin e → W) :=
    { toFun := fun v β => ⟨∑ i, ∑ δ, X i β δ • (A i).mulVec (v δ),
        W.sum_mem fun i _ => W.sum_mem fun δ _ => W.smul_mem _ (hVW i ⟨v δ, (v δ).2, rfl⟩)⟩
      map_add' := fun v u => funext fun β => Subtype.ext <| by
        simp only [Submodule.coe_add, Pi.add_apply, Matrix.mulVec_add, smul_add,
          Finset.sum_add_distrib]
      map_smul' := fun c v => funext fun β => Subtype.ext <| by
        simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, Matrix.mulVec_smul,
          Finset.smul_sum, smul_smul]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
          congrArg (· • _) (mul_comm _ _) }
  have hd := LinearMap.finrank_le_finrank_of_injective (f := g) fun v u h => funext fun δ =>
    Subtype.ext <| congrFun (hX <| funext fun β => congrArg Subtype.val (congrFun h β)) δ
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hd
  exact Nat.le_of_mul_le_mul_left hd he

variable {P Q : Type*} [AddCommGroup P] [Module F P]
  [AddCommGroup Q] [Module F Q]

/-- The subspace spanned by the components of a vector. -/
def componentSpace {q : ℕ} (f : Fin q → P) : Submodule F P :=
  Submodule.span F (Set.range f)

/-- A component regarded as a vector in the component span. -/
def component {q : ℕ} (f : Fin q → P) (α : Fin q) : componentSpace (F := F) f :=
  ⟨f α, Submodule.subset_span ⟨α, rfl⟩⟩

/-- Coordinates of each component in a basis of their span. -/
def coefficientMatrix {q k : ℕ} (f : Fin q → P)
    (b : Basis (Fin k) F (componentSpace (F := F) f)) : Matrix (Fin q) (Fin k) F :=
  fun α => b.equivFun (component (F := F) f α)

private lemma span_component_top {q : ℕ} (f : Fin q → P) :
    Submodule.span F (Set.range (component (F := F) f)) = ⊤ := by
  apply Submodule.map_injective_of_injective (componentSpace (F := F) f).injective_subtype
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
  rfl

private lemma rank_coefficientMatrix {q k : ℕ} (f : Fin q → P)
    (b : Basis (Fin k) F (componentSpace (F := F) f)) : (coefficientMatrix f b).rank = k := by
  have hh := congrArg (Submodule.map b.equivFun.toLinearMap) (span_component_top f)
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
    LinearMap.range_eq_top.mpr b.equivFun.surjective] at hh
  rw [Matrix.rank_eq_finrank_span_row]
  change finrank F (Submodule.span F (Set.range (b.equivFun.toLinearMap ∘ component f))) = k
  rw [hh]
  simp

private lemma coefficientMatrix_expansion {q k : ℕ} (f : Fin q → P)
    (b : Basis (Fin k) F (componentSpace (F := F) f)) (α : Fin q) :
    ∑ j, (coefficientMatrix f b) α j • (b j : P) = f α := by
  simpa only [coefficientMatrix, Basis.equivFun_apply, Submodule.coe_sum,
    Submodule.coe_smul, component] using congrArg Subtype.val (b.sum_repr (component (F := F) f α))

/-- The combined output map of the `w * k` component images. -/
def imageCombination {w k : ℕ} (T : Fin w → P →ₗ[F] Q) (u : Fin k → P) :
    (Fin w × Fin k → F) →ₗ[F] Q :=
  Fintype.linearCombination F (fun ij => T ij.1 (u ij.2))

/-- The concatenated coefficient matrix. -/
def concatMatrix {w q k : ℕ} (A : Fin w → Matrix (Fin q) (Fin q) F)
    (P : Matrix (Fin q) (Fin k) F) : Matrix (Fin q) (Fin w × Fin k) F :=
  fun α ij => (A ij.1 * P) α ij.2

private lemma concat_row_relation {w q k : ℕ}
    (A : Fin w → Matrix (Fin q) (Fin q) F) (T : Fin w → P →ₗ[F] Q)
    (f : Fin q → P) (b : Basis (Fin k) F (componentSpace (F := F) f))
    (hker : ∀ α, ∑ i, ∑ γ, A i α γ • T i (f γ) = 0) (α : Fin q) :
    (concatMatrix A (coefficientMatrix f b)).row α ∈
      (imageCombination T (fun j => (b j : P))).ker := by
  rw [LinearMap.mem_ker]
  change (∑ ij : Fin w × Fin k,
    (∑ γ, A ij.1 α γ * coefficientMatrix f b γ ij.2) • T ij.1 (b ij.2 : P)) = 0
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_smul]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  simp_rw [mul_smul, ← Finset.smul_sum, ← map_smul, ← map_sum,
    coefficientMatrix_expansion]
  exact hker α

private lemma rank_concat_lt {w q k : ℕ}
    (A : Fin w → Matrix (Fin q) (Fin q) F) (T : Fin w → P →ₗ[F] Q)
    (f : Fin q → P) (b : Basis (Fin k) F (componentSpace (F := F) f))
    (hker : ∀ α, ∑ i, ∑ γ, A i α γ • T i (f γ) = 0)
    (hex : (w - 1) * k < finrank F (imageCombination T (fun j => (b j : P))).range)
    (hw : 1 ≤ w) : (concatMatrix A (coefficientMatrix f b)).rank < k := by
  let H := imageCombination T (fun j => (b j : P))
  have hle : Submodule.span F (Set.range (concatMatrix A (coefficientMatrix f b)).row) ≤ H.ker :=
    Submodule.span_le.mpr fun _ ⟨α, h⟩ => h ▸ concat_row_relation A T f b hker α
  have hr := Submodule.finrank_mono hle
  rw [← Matrix.rank_eq_finrank_span_row] at hr
  have hd := H.finrank_range_add_finrank_ker
  simp only [Module.finrank_pi, Fintype.card_prod, Fintype.card_fin] at hd
  have hw' : (w - 1) * k + k = w * k := by rw [← Nat.add_one_mul, Nat.sub_add_cancel hw]
  change (w - 1) * k < finrank F H.range at hex
  omega

private lemma coefficient_image_le_concat {w q k : ℕ}
    (A : Fin w → Matrix (Fin q) (Fin q) F) (P : Matrix (Fin q) (Fin k) F) (i : Fin w) :
    (Submodule.span F (Set.range P.col)).map (A i).mulVecLin ≤
      Submodule.span F (Set.range (concatMatrix A P).col) := by
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨v, ⟨j, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨(i, j), funext fun α => by
    simp [concatMatrix, Matrix.mulVec, Matrix.mul_apply, dotProduct]⟩

private lemma component_image_le_range {w q k : ℕ} (T : Fin w → P →ₗ[F] Q)
    (f : Fin q → P) (b : Basis (Fin k) F (componentSpace (F := F) f)) (i : Fin w) :
    (componentSpace (F := F) f).map (T i) ≤
      (imageCombination T (fun j => (b j : P))).range := by
  rw [imageCombination, Fintype.range_linearCombination]
  rintro _ ⟨x, hx, rfl⟩
  have he : (∑ j, (b.repr ⟨x, hx⟩) j • (b j : P)) = x := by
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using
      congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
  rw [← he, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)

/-- A kernel vector with sufficiently expansive component span contradicts
any invertible block evaluation of the same coefficient matrices. -/
theorem kernel_impossible {w q k e : ℕ} (hw : 1 ≤ w) (he : 0 < e)
    (A : Fin w → Matrix (Fin q) (Fin q) F) (T : Fin w → P →ₗ[F] Q)
    (X : Fin w → Matrix (Fin e) (Fin e) F)
    (hX : Function.Injective (blockEval A X))
    (f : Fin q → P) (b : Basis (Fin k) F (componentSpace (F := F) f))
    (hker : ∀ α, ∑ i, ∑ γ, A i α γ • T i (f γ) = 0)
    (hex : (w - 1) * k < finrank F (imageCombination T (fun j => (b j : P))).range) :
    False := by
  have hd := no_shrunk_subspace he A X hX
    (Submodule.span F (Set.range (coefficientMatrix f b).col))
    (Submodule.span F (Set.range (concatMatrix A (coefficientMatrix f b)).col))
    (coefficient_image_le_concat A (coefficientMatrix f b))
  rw [← Matrix.rank_eq_finrank_span_cols, ← Matrix.rank_eq_finrank_span_cols,
    rank_coefficientMatrix f b] at hd
  exact absurd (rank_concat_lt A T f b hker hex hw) (by omega)

/-- The block matrix obtained as a sum of Kronecker products. -/
def blockMatrix {w q e : ℕ} (A : Fin w → Matrix (Fin q) (Fin q) F)
    (X : Fin w → Matrix (Fin e) (Fin e) F) :
    Matrix (Fin q × Fin e) (Fin q × Fin e) F := ∑ i, A i ⊗ₖ X i

private lemma blockMatrix_mulVec {w q e : ℕ} (A : Fin w → Matrix (Fin q) (Fin q) F)
    (X : Fin w → Matrix (Fin e) (Fin e) F) (v : Fin e → Fin q → F)
    (α : Fin q) (β : Fin e) :
    (blockMatrix A X).mulVec (fun j => v j.2 j.1) (α, β) = blockEval A X v β α := by
  classical
  simp only [blockMatrix, Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Matrix.kronecker_apply, Finset.sum_mul, Fintype.sum_prod_type,
    blockEval, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext δ; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

/-- If `blockMatrix A X` is a unit, then `blockEval A X` is injective. -/
lemma blockEval_injective_of_isUnit {w q e : ℕ}
    (A : Fin w → Matrix (Fin q) (Fin q) F)
    (X : Fin w → Matrix (Fin e) (Fin e) F) (h : IsUnit (blockMatrix A X)) :
    Function.Injective (blockEval A X) := fun v u hv => by
  have hflat : (fun j : Fin q × Fin e => v j.2 j.1) = fun j => u j.2 j.1 :=
    Matrix.mulVec_injective_iff_isUnit.mpr h <| funext fun j => by
      rw [blockMatrix_mulVec, blockMatrix_mulVec]
      exact congrFun (congrFun hv j.2) j.1
  exact funext fun β => funext fun α => congrFun hflat (α, β)

end
end Rational.Rectangular

namespace Rational.RectangularExpansion
open Module Matrix
open scoped BigOperators
open LaurentReduction SmallExpansion Rectangular
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- The rectangular Taylor tests have no nonzero kernel component family when
the same coefficients have an invertible matrix witness. -/
theorem rectangular_kernel_zero (w B M N q e : ℕ) (hw : 1 ≤ w) (hN : 1 ≤ N)
    (hMN : M = N + 2 * w ^ 3 * B) (hq : q ≤ B) (he : 0 < e)
    (points : Fin w → K) (hp : Function.Injective points)
    (A : Fin w → Matrix (Fin q) (Fin q) (F K))
    (X : Fin w → Matrix (Fin e) (Fin e) (F K))
    (hX : Function.Injective (blockEval A X))
    (f : Fin q → Fin M → F K)
    (hf : ∀ α j, N ≤ j.val → f α j = 0)
    (hker : ∀ α, ∑ i, ∑ γ, A i α γ • testMap M (points i) (f γ) = 0) : f = 0 := by
  classical
  by_contra hn
  obtain ⟨α, hα⟩ : ∃ α, f α ≠ 0 := by
    by_contra! hh
    exact hn (funext hh)
  let U := componentSpace (F := F K) f
  let b := Module.finBasis (F K) U
  let T := fun i => testMap M (points i)
  have hk : 1 ≤ finrank (F K) U := finrank_pos_iff_exists_ne_zero.mpr
    ⟨component (F := F K) f α, fun hz => hα (congrArg Subtype.val hz)⟩
  have hkq : finrank (F K) U ≤ q := by
    simpa using finrank_le_of_span_eq_top (span_component_top (F := F K) f)
  have hU (x : Fin M → F K) (hx : x ∈ U) : ∀ j : Fin M, N ≤ j.val → x j = 0 := by
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨α, rfl⟩ := hx; exact hf α
    | zero => exact fun _ _ => rfl
    | add _ _ _ _ hx hy => exact fun j hj => by simp [hx j hj, hy j hj]
    | smul _ _ _ hx => exact fun j hj => by simp [hx j hj]
  exact kernel_impossible hw he A T X hX f b hker <|
    small_expansion w B M N hw hN hMN points hp U
      (imageCombination T fun j => (b j : Fin M → F K)).range hU
      (component_image_le_range T f b) hk (hkq.trans hq)

end
end Rational.RectangularExpansion

end Cslib.Circuits
