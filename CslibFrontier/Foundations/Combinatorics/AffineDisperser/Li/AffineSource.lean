/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Basic
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.AffineSubspace
public import CslibFrontier.Foundations.Data.BitString.AffineSubspace
public import CslibFrontier.Probability.MinEntropy
public import CslibFrontier.Probability.Product
public import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Foundations.Data.BitString.ZModTwo
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith

/-!
# Affine sources, conditioning, block decomposition, and disperser bridges

This module provides the foundational theory of affine sources over `𝔽₂` (`Bool`) needed for
explicit affine condensers and extractors ([Li2023], [LiZhong2024]):

* `Cslib.AffineDisperser.Li.uniformAffine`: the uniform distribution on a nonempty affine subspace
  of `BitString n`.
* `Cslib.AffineDisperser.Li.IsAffineSource`: an `(n, k)` affine source (`[Li2023, Def. 3.1]`,
  `[LiZhong2024, Def. 15]`).
* `Cslib.AffineDisperser.Li.blockEquiv`: canonical isomorphism between `BitString (∑ i, b i)`
  and partitioned bit-blocks `∀ i : Fin t, BitString (b i)`.
* `Cslib.AffineDisperser.Li.IsAffineExtractor`: seedless `(k, ε)`-affine extractors.
* `Cslib.AffineDisperser.Li.IsSumsetExtractor`: `(k₁, k₂, ε)`-sumset extractors
  (`[Li2023, Thm. 7.13]`).

## Main results

* `Cslib.AffineDisperser.Li.minEntropy_of_isAffineSource`: an `(n, k)` affine source has
  min-entropy `k`.
* `Cslib.AffineDisperser.Li.isAffineSource_map_of_isAffine`: any affine image of an affine source
  is an affine source whose dimension is the rank of the linear part on its direction.
* `Cslib.AffineDisperser.Li.affineConditioning`: **Affine Conditioning Lemma**
  (`[Li2023, Lemma 3.9]`, `[LiZhong2024, Lemma 8]`), decomposing `X = A + B` for any affine map
  `L` so that `A` and `B` are independent affine sources, `L` is constant on `B`, `A` is
  affinely recoverable from `L(A)`, and conditioning `X` on `L(x) = ℓ` yields a translate of `B`.
* `Cslib.AffineDisperser.Li.affineBlockDecomposition`: **Affine Block Decomposition**
  (`[Li2023, Lemma 3.10]`), expressing an affine source of codimension `≤ r` on partitioned blocks
  as a mixture of independent product affine sources (`PMF.pi`) of codimension `≤ r` in every
  block.
* `Cslib.AffineDisperser.Li.isAffineDisperser_of_isAffineExtractor`,
  `Cslib.AffineDisperser.Li.isAffineExtractor_of_isSumsetExtractor`,
  `Cslib.AffineDisperser.Li.isAffineDisperser_of_isSumsetExtractor`: bridges from sumset and affine
  extractors to `Cslib.BitString.IsAffineDisperser` (`[Li2023, Cor. 7.14]`).

## References

* [X. Li, *Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More*][Li2023],
  Section 3 (Definition 3.1, Lemma 3.9, Lemma 3.10) and Section 7 (Theorem 7.13, Corollary 7.14)
* [X. Li and Y. Zhong, *Explicit Directional Affine Extractors and Improved Hardness for Linear
  Branching Programs*][LiZhong2024], Section 3 and Appendix B (Lemma 8, Definition 15)
-/

public section

namespace Cslib.AffineDisperser.Li

open Cslib.BitString Cslib.Probability Cslib.Probability.PMF Module

/-! ### Transfer between `Bool`-modules and `(ZMod 2)`-vector spaces -/

section BoolVectorSpace

private def toZModBits (ι : Type*) : (ι → Bool) ≃+ (ι → ZMod 2) where
  toFun v i := bitEquiv.symm (v i)
  invFun v i := bitEquiv (v i)
  left_inv v := funext fun i => bitEquiv.apply_symm_apply (v i)
  right_inv v := funext fun i => bitEquiv.symm_apply_apply (v i)
  map_add' u v := funext fun i => map_add bitEquiv.symm (u i) (v i)

private theorem toZModBits_smul {ι : Type*} (c : Bool) (v : ι → Bool) :
    toZModBits ι (c • v) = bitEquiv.symm c • toZModBits ι v :=
  funext fun i => map_mul bitEquiv.symm c (v i)

private theorem symm_toZModBits_smul {ι : Type*} (c : ZMod 2) (v : ι → ZMod 2) :
    (toZModBits ι).symm (c • v) = bitEquiv c • (toZModBits ι).symm v := by
  apply (toZModBits ι).injective
  rw [toZModBits_smul, (toZModBits ι).apply_symm_apply, (toZModBits ι).apply_symm_apply,
    bitEquiv.symm_apply_apply]

private def toZModSub {ι : Type*} (V : Submodule Bool (ι → Bool)) :
    Submodule (ZMod 2) (ι → ZMod 2) where
  carrier := toZModBits ι '' (V : Set (ι → Bool))
  zero_mem' := ⟨0, V.zero_mem, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, V.add_mem hx hy, map_add _ x y⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    refine ⟨bitEquiv c • x, V.smul_mem _ hx, ?_⟩
    rw [toZModBits_smul, bitEquiv.symm_apply_apply]

private def ofZModSub {ι : Type*} (W : Submodule (ZMod 2) (ι → ZMod 2)) :
    Submodule Bool (ι → Bool) where
  carrier := (toZModBits ι).symm '' (W : Set (ι → ZMod 2))
  zero_mem' := ⟨0, W.zero_mem, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, W.add_mem hx hy, map_add _ x y⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    refine ⟨bitEquiv.symm c • x, W.smul_mem _ hx, ?_⟩
    rw [symm_toZModBits_smul, bitEquiv.apply_symm_apply]

private theorem mem_toZModSub {ι : Type*} {V : Submodule Bool (ι → Bool)} {x : ι → Bool} :
    toZModBits ι x ∈ toZModSub V ↔ x ∈ V :=
  ⟨fun ⟨_, hy, hyx⟩ => (toZModBits ι).injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

private theorem mem_ofZModSub {ι : Type*} {W : Submodule (ZMod 2) (ι → ZMod 2)} {x : ι → Bool} :
    x ∈ ofZModSub W ↔ toZModBits ι x ∈ W :=
  ⟨fun ⟨_, hy, hyx⟩ => hyx ▸ ((toZModBits ι).apply_symm_apply _).symm ▸ hy,
    fun hx => ⟨_, hx, (toZModBits ι).symm_apply_apply x⟩⟩

private theorem toZModSub_ofZModSub {ι : Type*} (W : Submodule (ZMod 2) (ι → ZMod 2)) :
    toZModSub (ofZModSub W) = W := by
  ext y; obtain ⟨x, rfl⟩ := (toZModBits ι).surjective y
  rw [mem_toZModSub, mem_ofZModSub]

private theorem toZModSub_le_iff {ι : Type*} {U V : Submodule Bool (ι → Bool)} :
    toZModSub U ≤ toZModSub V ↔ U ≤ V :=
  ⟨fun h _ hx => mem_toZModSub.mp (h (mem_toZModSub.mpr hx)),
    fun h _ ⟨_, hx, h'⟩ => h' ▸ mem_toZModSub.mpr (h hx)⟩

private theorem toZModSub_inf {ι : Type*} (U V : Submodule Bool (ι → Bool)) :
    toZModSub (U ⊓ V) = toZModSub U ⊓ toZModSub V := by
  ext y; obtain ⟨x, rfl⟩ := (toZModBits ι).surjective y
  simp only [Submodule.mem_inf, mem_toZModSub]

private theorem toZModSub_sup {ι : Type*} (U V : Submodule Bool (ι → Bool)) :
    toZModSub (U ⊔ V) = toZModSub U ⊔ toZModSub V :=
  le_antisymm (by
    rintro _ ⟨_, hz, rfl⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hz
    exact map_add (toZModBits ι) u v ▸
      Submodule.add_mem_sup (mem_toZModSub.mpr hu) (mem_toZModSub.mpr hv))
    (sup_le (toZModSub_le_iff.mpr le_sup_left) (toZModSub_le_iff.mpr le_sup_right))

private def toZModLinear {ι₁ ι₂ : Type*} (f : (ι₁ → Bool) →ₗ[Bool] (ι₂ → Bool)) :
    (ι₁ → ZMod 2) →ₗ[ZMod 2] (ι₂ → ZMod 2) where
  toFun z := toZModBits ι₂ (f ((toZModBits ι₁).symm z))
  map_add' _ _ := by simp only [map_add]
  map_smul' c a := by
    rw [symm_toZModBits_smul, map_smul, toZModBits_smul, bitEquiv.symm_apply_apply]; rfl

private def toZModSubEquiv {ι : Type*} (V : Submodule Bool (ι → Bool)) :
    V ≃+ toZModSub V where
  toFun v := ⟨toZModBits ι v.1, mem_toZModSub.mpr v.2⟩
  invFun w := ⟨(toZModBits ι).symm w.1, by
    rw [← mem_toZModSub, (toZModBits ι).apply_symm_apply]; exact w.2⟩
  left_inv v := Subtype.ext ((toZModBits ι).symm_apply_apply v.1)
  right_inv w := Subtype.ext ((toZModBits ι).apply_symm_apply w.1)
  map_add' u v := Subtype.ext (map_add (toZModBits ι) u.1 v.1)

private theorem finrank_bool_eq_finrank_toZMod {ι : Type*} (V : Submodule Bool (ι → Bool)) :
    finrank Bool V = finrank (ZMod 2) (toZModSub V) :=
  congrArg Cardinal.toNat <|
    rank_eq_of_equiv_equiv (R := Bool) (R' := ZMod 2) (M := V) (M₁ := toZModSub V)
      bitEquiv.symm (toZModSubEquiv V) bitEquiv.symm.bijective
      fun c v => Subtype.ext (toZModBits_smul c v.1)

private theorem natCard_submodule_bool {ι : Type*} [Finite ι] (V : Submodule Bool (ι → Bool)) :
    Nat.card V = 2 ^ finrank Bool V := by
  have eV := (toZModSubEquiv V).toEquiv
  have : Finite (toZModSub V) := Finite.of_equiv V eV
  let _ : Fintype (toZModSub V) := Fintype.ofFinite _
  rw [Nat.card_congr eV, Nat.card_eq_fintype_card,
    Fintype.card_congr (Module.finBasis (ZMod 2) (toZModSub V)).equivFun.toEquiv,
    Fintype.card_fun, Fintype.card_fin, ZMod.card, finrank_bool_eq_finrank_toZMod]

/-- Complementing a `Bool`-submodule inside another `Bool`-submodule of `ι → Bool`. -/
theorem exists_isCompl_submodule {ι : Type*} (K V : Submodule Bool (ι → Bool))
    (hKV : K ≤ V) :
    ∃ U : Submodule Bool (ι → Bool), U ≤ V ∧ U ⊓ K = ⊥ ∧ U ⊔ K = V := by
  let KZ := (toZModSub K).comap (toZModSub V).subtype
  obtain ⟨UZ, hUZ⟩ := Submodule.exists_isCompl KZ
  have hle : UZ.map (toZModSub V).subtype ≤ toZModSub V := Submodule.map_subtype_le _ _
  refine ⟨ofZModSub (UZ.map (toZModSub V).subtype), ?_, ?_, ?_⟩
  · rwa [← toZModSub_le_iff, toZModSub_ofZModSub]
  · rw [eq_bot_iff, ← toZModSub_le_iff, toZModSub_inf, toZModSub_ofZModSub]
    rintro y ⟨hy1, hy2⟩
    obtain ⟨⟨w, hwV⟩, hwU, rfl⟩ := Submodule.mem_map.mp hy1
    have hmem : (⟨w, hwV⟩ : toZModSub V) ∈ KZ ⊓ UZ := ⟨hy2, hwU⟩
    rw [hUZ.inf_eq_bot, Submodule.mem_bot] at hmem
    have h0 : w = 0 := congrArg Subtype.val hmem
    subst h0; exact (toZModSub ⊥).zero_mem
  · refine le_antisymm (sup_le (by rwa [← toZModSub_le_iff, toZModSub_ofZModSub]) hKV) ?_
    rw [← toZModSub_le_iff, toZModSub_sup, toZModSub_ofZModSub, sup_comm]
    intro w hw
    obtain ⟨k, hk, u, hu, hku⟩ :=
      Submodule.mem_sup.mp (hUZ.sup_eq_top ▸ Submodule.mem_top : (⟨w, hw⟩ : toZModSub V) ∈ _)
    exact Submodule.mem_sup.mpr ⟨k.1, hk, u.1, Submodule.mem_map.mpr ⟨u, hu, rfl⟩,
      congrArg Subtype.val hku⟩

/-- Dimension formula for the sum and intersection of two `Bool`-submodules of `ι → Bool`. -/
theorem finrank_sup_add_finrank_inf_bitString {ι : Type*} [Finite ι]
    (U K : Submodule Bool (ι → Bool)) :
    finrank Bool ↥(U ⊔ K) + finrank Bool ↥(U ⊓ K) =
      finrank Bool U + finrank Bool K := by
  have : Finite (ι → ZMod 2) := Finite.of_equiv (ι → Bool) (toZModBits ι).toEquiv
  simp_rw [finrank_bool_eq_finrank_toZMod]
  rw [toZModSub_sup, toZModSub_inf]
  exact Submodule.finrank_sup_add_finrank_inf_eq (toZModSub U) (toZModSub K)

/-- Rank-nullity for linear maps between `Bool`-vector spaces `ι₁ → Bool` and `ι₂ → Bool`. -/
theorem finrank_range_add_finrank_ker_bitString {ι₁ ι₂ : Type*} [Finite ι₁]
    (f : (ι₁ → Bool) →ₗ[Bool] (ι₂ → Bool)) (V : Submodule Bool (ι₁ → Bool)) :
    finrank Bool ↥(V.map f) + finrank Bool ↥(V ⊓ LinearMap.ker f) = finrank Bool V := by
  let fZ := toZModLinear f
  have hmap : toZModSub (V.map f) = LinearMap.range (fZ.domRestrict (toZModSub V)) := by
    ext y; obtain ⟨w, rfl⟩ := (toZModBits ι₂).surjective y
    simp only [mem_toZModSub, Submodule.mem_map, LinearMap.mem_range, LinearMap.domRestrict_apply,
      Subtype.exists, fZ, toZModLinear, LinearMap.coe_mk, AddHom.coe_mk]
    exact ⟨fun ⟨x, hx, h⟩ => ⟨toZModBits ι₁ x, mem_toZModSub.mpr hx,
        by rw [(toZModBits ι₁).symm_apply_apply, h]⟩,
      fun ⟨_, ⟨x, hx, rfl⟩, h⟩ => ⟨x, hx, (toZModBits ι₂).injective
        (by simpa only [(toZModBits ι₁).symm_apply_apply] using h)⟩⟩
  have hker : toZModSub (V ⊓ LinearMap.ker f) = toZModSub V ⊓ LinearMap.ker fZ := by
    ext z; obtain ⟨x, rfl⟩ := (toZModBits ι₁).surjective z
    simp only [Submodule.mem_inf, mem_toZModSub, LinearMap.mem_ker, fZ, toZModLinear,
      LinearMap.coe_mk, AddHom.coe_mk, (toZModBits ι₁).symm_apply_apply,
      (toZModBits ι₂).map_eq_zero_iff]
  let eK : LinearMap.ker (fZ.domRestrict (toZModSub V)) ≃ₗ[ZMod 2]
      ↥(toZModSub V ⊓ LinearMap.ker fZ) :=
    { toFun := fun v => ⟨v.1.1, v.1.2, LinearMap.mem_ker.mpr v.2⟩
      invFun := fun w => ⟨⟨w.1, w.2.1⟩, LinearMap.mem_ker.mpr w.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have : Finite (ι₁ → ZMod 2) := Finite.of_equiv (ι₁ → Bool) (toZModBits ι₁).toEquiv
  simp_rw [finrank_bool_eq_finrank_toZMod]
  rw [hmap, hker, ← eK.finrank_eq]
  exact LinearMap.finrank_range_add_finrank_ker (fZ.domRestrict (toZModSub V))

/-- Existence of a `k₁`-dimensional `Bool`-submodule inside any `Bool`-submodule of `ι → Bool`
of dimension at least `k₁`. -/
theorem exists_submodule_finrank_eq_bitString {ι : Type*} [Finite ι]
    (V : Submodule Bool (ι → Bool)) (k₁ : ℕ) (hk₁ : k₁ ≤ finrank Bool V) :
    ∃ U : Submodule Bool (ι → Bool), U ≤ V ∧ finrank Bool U = k₁ := by
  have : Finite (ι → ZMod 2) := Finite.of_equiv (ι → Bool) (toZModBits ι).toEquiv
  rw [finrank_bool_eq_finrank_toZMod] at hk₁
  let B0 := Module.finBasis (ZMod 2) (toZModSub V)
  let g : Fin k₁ → ι → ZMod 2 := fun i => B0 (Fin.castLE hk₁ i)
  let UZ := Submodule.span (ZMod 2) (Set.range g)
  have hli : LinearIndependent (ZMod 2) g :=
    (B0.linearIndependent.comp _ (Fin.castLE_injective hk₁)).map'
      (toZModSub V).subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  refine ⟨ofZModSub UZ,
    toZModSub_le_iff.mp (by
      rw [toZModSub_ofZModSub]
      exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (B0 _).2)),
    by rw [finrank_bool_eq_finrank_toZMod, toZModSub_ofZModSub, finrank_span_eq_card hli,
      Fintype.card_fin]⟩

end BoolVectorSpace

/-! ### Uniform distributions on affine subspaces -/

section AffineSource

/-- The uniform distribution on a nonempty affine subspace of `BitString n`. -/
@[expose] noncomputable def uniformAffine {n : ℕ} (A : AffineSubspace Bool (BitString n))
    (hA : (A : Set (BitString n)).Nonempty) : PMF (BitString n) :=
  PMF.uniformOfFinset (Set.toFinite (A : Set (BitString n))).toFinset
    (by
      obtain ⟨x, hx⟩ := hA
      exact ⟨x, (Set.Finite.mem_toFinset _).mpr hx⟩)

/-- An **`(n, k)` affine source** over `𝔽₂`: the uniform distribution on an affine subspace of
`BitString n` of dimension `k` ([Li2023, Def. 3.1], [LiZhong2024, Def. 15]). -/
@[expose] def IsAffineSource {n : ℕ} (X : PMF (BitString n)) (k : ℕ) : Prop :=
  ∃ (A : AffineSubspace Bool (BitString n)) (hA : (A : Set (BitString n)).Nonempty),
    finrank Bool A.direction = k ∧ X = uniformAffine A hA

private def uniformAffine_direction_equiv {n : ℕ} (A : AffineSubspace Bool (BitString n))
    {x₀ : BitString n} (hx₀ : x₀ ∈ A) :
    A.direction ≃ (Set.toFinite (A : Set (BitString n))).toFinset where
  toFun v := ⟨v.1 +ᵥ x₀, (Set.Finite.mem_toFinset _).mpr
    (AffineSubspace.vadd_mem_of_mem_direction v.2 hx₀)⟩
  invFun y := ⟨y.1 -ᵥ x₀, AffineSubspace.vsub_mem_direction
    ((Set.Finite.mem_toFinset _).mp y.2) hx₀⟩
  left_inv v := Subtype.ext (vadd_vsub v.1 x₀)
  right_inv y := Subtype.ext (vsub_vadd y.1 x₀)

/-- The cardinality of the `Finset` of points of a nonempty affine subspace of `BitString n` equals
`2 ^ finrank Bool A.direction`. -/
theorem card_affineSubspace_toFinset {n : ℕ}
    (A : AffineSubspace Bool (BitString n)) (hA : (A : Set (BitString n)).Nonempty) :
    (Set.toFinite (A : Set (BitString n))).toFinset.card = 2 ^ finrank Bool A.direction := by
  obtain ⟨x₀, hx₀⟩ := hA
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card,
    Nat.card_congr (uniformAffine_direction_equiv A hx₀).symm, natCard_submodule_bool]

/-- Pointwise mass of `uniformAffine A hA`. -/
@[simp]
theorem uniformAffine_apply {n : ℕ} (A : AffineSubspace Bool (BitString n))
    (hA : (A : Set (BitString n)).Nonempty) (x : BitString n) :
    uniformAffine A hA x =
      @ite ENNReal (x ∈ A) (Classical.propDecidable (x ∈ A))
        ((2 ^ finrank Bool A.direction : ℕ) : ENNReal)⁻¹ 0 := by
  classical
  rw [uniformAffine, PMF.uniformOfFinset_apply, card_affineSubspace_toFinset A hA]
  simp only [Set.Finite.mem_toFinset]
  convert rfl

/-- The uniform distribution on a nonempty affine subspace `A` has min-entropy `dim(A)`. -/
theorem minEntropy_uniformAffine {n : ℕ} (A : AffineSubspace Bool (BitString n))
    (hA : (A : Set (BitString n)).Nonempty) :
    minEntropy (uniformAffine A hA) = (finrank Bool A.direction : ℝ) := by
  rw [uniformAffine, minEntropy_uniformOfFinset, card_affineSubspace_toFinset A hA]
  push_cast
  rw [Real.logb_two_pow]

/-- Every `(n, k)` affine source has min-entropy `k`. -/
theorem minEntropy_of_isAffineSource {n k : ℕ} {X : PMF (BitString n)}
    (hX : IsAffineSource X k) : minEntropy X = (k : ℝ) := by
  rcases hX with ⟨A, hA, hdim, rfl⟩
  rw [minEntropy_uniformAffine, hdim]

/-- Support of `uniformAffine A hA` is `A`. -/
theorem mem_support_uniformAffine_iff {n : ℕ} (A : AffineSubspace Bool (BitString n))
    (hA : (A : Set (BitString n)).Nonempty) (x : BitString n) :
    x ∈ (uniformAffine A hA).support ↔ x ∈ A := by
  rw [uniformAffine, mem_support_uniformOfFinset_iff, Set.Finite.mem_toFinset]
  rfl

private theorem uniformAffine_eq_map_direction {n : ℕ} (A : AffineSubspace Bool (BitString n))
    {x₀ : BitString n} (hx₀ : x₀ ∈ A) [Fintype A.direction] :
    uniformAffine A ⟨x₀, hx₀⟩ =
      (PMF.uniformOfFintype A.direction).map fun v => x₀ + v.1 := by
  let S := (Set.toFinite (A : Set (BitString n))).toFinset
  have : Nonempty S := ⟨⟨x₀, (Set.Finite.mem_toFinset _).mpr hx₀⟩⟩
  change PMF.uniformOfFinset S _ = _
  rw [← uniformOfFintype_finset_map_val S,
    ← uniformOfFintype_map_equiv (uniformAffine_direction_equiv A hx₀), PMF.map_comp]
  exact congrArg (PMF.map · _) (funext fun v => add_comm v.1 x₀)

private theorem uniformAffine_mk'_eq_map {n : ℕ} (x₀ : BitString n)
    (V : Submodule Bool (BitString n)) [Fintype V] :
    uniformAffine (AffineSubspace.mk' x₀ V) ⟨x₀, AffineSubspace.self_mem_mk' x₀ V⟩ =
      (PMF.uniformOfFintype V).map fun v => x₀ + v.1 := by
  classical
  let e : V ≃ (AffineSubspace.mk' x₀ V).direction :=
    Equiv.subtypeEquivRight fun v => by rw [AffineSubspace.direction_mk']
  rw [uniformAffine_eq_map_direction _ (AffineSubspace.self_mem_mk' x₀ V),
    ← uniformOfFintype_map_equiv e, PMF.map_comp]; rfl

/-- Helper: a direct-sum decomposition `U ⊓ K = ⊥ ∧ U ⊔ K = V` gives a bijection `U × K ≃ V`. -/
private noncomputable def isCompl_prodEquiv {ι : Type*}
    {U K V : Submodule Bool (ι → Bool)} (hU : U ≤ V) (hK : K ≤ V)
    (hcompl : U ⊓ K = ⊥ ∧ U ⊔ K = V) : U × K ≃ V :=
  Equiv.ofBijective (fun p => ⟨p.1.1 + p.2.1, V.add_mem (hU p.1.2) (hK p.2.2)⟩)
    ⟨fun ⟨u₁, k₁⟩ ⟨u₂, k₂⟩ h => by
      have hv : u₁.1 + k₁.1 = u₂.1 + k₂.1 := congrArg Subtype.val h
      have h0 : u₁.1 - u₂.1 = k₂.1 - k₁.1 := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm k₂.1 u₂.1, hv]
      have hu : u₁.1 - u₂.1 ∈ U ⊓ K := ⟨U.sub_mem u₁.2 u₂.2, h0 ▸ K.sub_mem k₂.2 k₁.2⟩
      rw [hcompl.1, Submodule.mem_bot] at hu
      exact Prod.ext (Subtype.ext (sub_eq_zero.mp hu))
        (Subtype.ext (sub_eq_zero.mp (hu ▸ h0.symm)).symm),
    fun v => by
      have hv : v.1 ∈ U ⊔ K := hcompl.2.symm ▸ v.2
      obtain ⟨u, hu, k, hk, huk⟩ := Submodule.mem_sup.mp hv
      exact ⟨(⟨u, hu⟩, ⟨k, hk⟩), Subtype.ext huk⟩⟩

/-- Helper: decomposing an affine subspace `A = x₀ + (U ⊕ K)` expresses `uniformAffine A` as the
independent sum `uniformAffine (x₀ + U) + uniformAffine (0 + K)`. -/
private theorem uniformAffine_eq_bind_add_of_isCompl {n : ℕ}
    (A : AffineSubspace Bool (BitString n)) {x₀ : BitString n} (hx₀ : x₀ ∈ A)
    {U K : Submodule Bool (BitString n)} (hU : U ≤ A.direction) (hK : K ≤ A.direction)
    (hcompl : U ⊓ K = ⊥ ∧ U ⊔ K = A.direction) :
    uniformAffine A ⟨x₀, hx₀⟩ =
      (uniformAffine (AffineSubspace.mk' x₀ U) ⟨x₀, AffineSubspace.self_mem_mk' x₀ U⟩).bind
        fun a => (uniformAffine (AffineSubspace.mk' 0 K) ⟨0, AffineSubspace.self_mem_mk' 0 K⟩).map
          fun b => a + b := by
  classical
  let e := isCompl_prodEquiv hU hK hcompl
  rw [uniformAffine_eq_map_direction A hx₀, ← uniformOfFintype_map_equiv e, PMF.map_comp,
    show (fun v : A.direction => x₀ + v.1) ∘ e = fun p : U × K => x₀ + (e (p.1, p.2)).1 from rfl,
    ← uniformOfFintype_bind_map (fun u k => x₀ + (e (u, k)).1),
    uniformAffine_mk'_eq_map x₀ U, PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun u => ?_)
  dsimp only [Function.comp_def]
  rw [uniformAffine_mk'_eq_map 0 K, PMF.map_comp]
  exact congrArg (PMF.map · _) (funext fun k => by
    change x₀ + (u.1 + k.1) = x₀ + u.1 + (0 + k.1); rw [zero_add, add_assoc])

/-- An affine map pushes `uniformAffine A hA` forward to `uniformAffine (A.map L.toAffineMap)`. -/
theorem uniformAffine_map_of_isAffine {n m : ℕ} (A : AffineSubspace Bool (BitString n))
    (hA : (A : Set (BitString n)).Nonempty) {L : BitString n → BitString m} (hL : IsAffine L) :
    (uniformAffine A hA).map L =
      uniformAffine (A.map hL.toAffineMap) (by
        obtain ⟨x₀, hx₀⟩ := hA
        exact ⟨L x₀, AffineSubspace.mem_map.mpr ⟨x₀, hx₀, rfl⟩⟩) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hA
  set A' := A.map hL.toAffineMap
  have hLx₀ : L x₀ ∈ A' := AffineSubspace.mem_map.mpr ⟨x₀, hx₀, rfl⟩
  have hdir' : A'.direction = A.direction.map hL.linearMap := AffineSubspace.map_direction _ _
  let K : Submodule Bool (BitString n) := A.direction ⊓ LinearMap.ker hL.linearMap
  obtain ⟨U, hU_le, hinf, hsup⟩ := exists_isCompl_submodule K A.direction inf_le_left
  let eUA' : U ≃ A'.direction := Equiv.ofBijective
    (fun u => ⟨hL.linearMap u.1, hdir'.symm ▸ Submodule.mem_map.mpr ⟨u.1, hU_le u.2, rfl⟩⟩)
    ⟨fun u₁ u₂ h => Subtype.ext <| sub_eq_zero.mp <| by
      have hd : u₁.1 - u₂.1 ∈ U ⊓ K := ⟨U.sub_mem u₁.2 u₂.2, A.direction.sub_mem
        (hU_le u₁.2) (hU_le u₂.2), LinearMap.mem_ker.mpr <| by
          rw [map_sub, sub_eq_zero]; exact congrArg Subtype.val h⟩
      rwa [hinf, Submodule.mem_bot] at hd,
    fun y => by
      have hy : y.1 ∈ A.direction.map hL.linearMap := hdir' ▸ y.2
      obtain ⟨v, hv, hvy⟩ := Submodule.mem_map.mp hy
      have hv' : v ∈ U ⊔ K := hsup.symm ▸ hv
      obtain ⟨u, hu, k, hk, huk⟩ := Submodule.mem_sup.mp hv'
      exact ⟨⟨u, hu⟩, Subtype.ext (by
        rw [← hvy, ← huk, map_add, LinearMap.mem_ker.mp hk.2, add_zero])⟩⟩
  have hL_add : ∀ (u : U) (k : K), L (x₀ + u.1 + (0 + k.1)) = L x₀ + hL.linearMap u.1 :=
    fun u k => by
      have h := hL.toAffineMap.map_vadd x₀ (u.1 + k.1)
      simp only [IsAffine.coe_toAffineMap, vadd_eq_add, map_add] at h
      have hker : hL.toAffineMap.linear k.1 = 0 := k.2.2
      rw [show x₀ + u.1 + (0 + k.1) = u.1 + k.1 + x₀ by abel, h, hker, add_zero, add_comm]
      rfl
  rw [uniformAffine_eq_bind_add_of_isCompl A hx₀ hU_le inf_le_left ⟨hinf, hsup⟩,
    PMF.map_bind, uniformAffine_mk'_eq_map x₀ U, PMF.bind_map,
    uniformAffine_eq_map_direction A' hLx₀, ← uniformOfFintype_map_equiv eUA', PMF.map_comp]
  rw [show PMF.map ((fun v : A'.direction => L x₀ + v.1) ∘ eUA') (PMF.uniformOfFintype U) =
      (PMF.uniformOfFintype U).bind fun u => PMF.pure (L x₀ + hL.linearMap u.1) from rfl]
  refine congrArg (PMF.bind _) (funext fun u => ?_)
  dsimp only [Function.comp_def]
  rw [uniformAffine_mk'_eq_map 0 K, PMF.map_comp, PMF.map_comp]
  have hfun : ((L ∘ fun b => x₀ + u.1 + b) ∘ fun v : K => 0 + v.1) =
      Function.const K (L x₀ + hL.linearMap u.1) := funext fun k => hL_add u k
  rw [hfun]; exact PMF.map_const ..

/-- An affine image of an affine source is an affine source whose dimension is the dimension of the
pushed-forward subspace. -/
theorem isAffineSource_map_of_isAffine {n m k : ℕ} {X : PMF (BitString n)}
    (hX : IsAffineSource X k) {L : BitString n → BitString m} (hL : IsAffine L) :
    ∃ k', k' ≤ k ∧ k' ≤ m ∧ IsAffineSource (X.map L) k' := by
  rcases hX with ⟨A, ⟨x₀, hx₀⟩, hdim, rfl⟩
  have hle_k : finrank Bool (A.direction.map hL.linearMap) ≤ k := by
    rw [← hdim]
    exact (Nat.le_add_right _ _).trans_eq (finrank_range_add_finrank_ker_bitString hL.linearMap _)
  have hle_m : finrank Bool (A.direction.map hL.linearMap) ≤ m := by
    rw [finrank_bool_eq_finrank_toZMod]
    exact (Submodule.finrank_le _).trans (by simp)
  exact ⟨finrank Bool (A.direction.map hL.linearMap), hle_k, hle_m, A.map hL.toAffineMap,
    ⟨L x₀, AffineSubspace.mem_map.mpr ⟨x₀, hx₀, rfl⟩⟩,
    by rw [AffineSubspace.map_direction]; rfl, uniformAffine_map_of_isAffine A ⟨x₀, hx₀⟩ hL⟩

/-! ### Affine Conditioning Lemma ([Li2023, Lemma 3.9], [LiZhong2024, Lemma 8]) -/

/-- **Affine Conditioning Lemma** ([Li2023, Lemma 3.9], [LiZhong2024, Lemma 8]):
for any `(n, k)` affine source `X` on `BitString n` and affine map `L : BitString n → BitString m`,
there exist independent affine sources `A` and `B` of dimensions `kA` and `kB` with `k = kA + kB`,
`k ≤ kB + m`, a constant `c`, and an affine map `L_inv` such that `X = A + B`, `L b = c` for all
`b ∈ B.support`, `L_inv (L a) = a` for all `a ∈ A.support`, and every fiber
`{x ∈ X.support | L x = ℓ}` is an affine subspace of dimension `kB`. -/
theorem affineConditioning {n m k : ℕ} {X : PMF (BitString n)} (hX : IsAffineSource X k)
    {L : BitString n → BitString m} (hL : IsAffine L) :
    ∃ (kA kB : ℕ) (A B : PMF (BitString n)) (c : BitString m)
      (L_inv : BitString m → BitString n),
      IsAffineSource A kA ∧ IsAffineSource B kB ∧
      k = kA + kB ∧ k ≤ kB + m ∧
      X = (A.bind fun a => B.map fun b => a + b) ∧
      (∀ b ∈ B.support, L b = c) ∧
      IsAffine L_inv ∧ (∀ a ∈ A.support, L_inv (L a) = a) ∧
      (∀ ℓ ∈ (X.map L).support, ∃ Aℓ : AffineSubspace Bool (BitString n),
        (Aℓ : Set (BitString n)).Nonempty ∧
        finrank Bool Aℓ.direction = kB ∧
        (Aℓ : Set (BitString n)) = {x ∈ X.support | L x = ℓ}) := by
  classical
  rcases hX with ⟨Asub, ⟨x₀, hx₀⟩, hdim, rfl⟩
  let K := Asub.direction ⊓ LinearMap.ker hL.linearMap
  obtain ⟨U, hU_le, hcompl_inf, hcompl_sup⟩ :=
    exists_isCompl_submodule K Asub.direction inf_le_left
  let fU := (toZModLinear hL.linearMap).domRestrict (toZModSub U)
  have hfU_inj : Function.Injective fU := (injective_iff_map_eq_zero fU).mpr fun ⟨z, hz⟩ hfz => by
    obtain ⟨u, hu, rfl⟩ := hz
    have hLu : hL.linearMap u = 0 := (toZModBits (Fin m)).injective <| by
      simpa only [fU, toZModLinear, LinearMap.domRestrict_apply, LinearMap.coe_mk, AddHom.coe_mk,
        (toZModBits (Fin n)).symm_apply_apply, map_zero] using hfz
    have huK : u ∈ U ⊓ K := ⟨hu, hU_le hu, LinearMap.mem_ker.mpr hLu⟩
    rw [hcompl_inf, Submodule.mem_bot] at huK
    exact Subtype.ext (by simp [huK])
  let eU := LinearEquiv.ofInjective fU hfU_inj
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range fU)
  let TZ := ((toZModSub U).subtype.comp eU.symm.toLinearMap).comp (Submodule.projectionOnto _ _ hW)
  let T : BitString m → BitString n := fun y => (toZModBits _).symm (TZ (toZModBits _ y))
  have T_add (a b : BitString m) : T (a + b) = T a + T b := by simp only [T, map_add]
  let L_inv : BitString m → BitString n := fun y => x₀ + T (y + L x₀)
  have hL_inv : IsAffine L_inv := fun y₁ y₂ y₃ => by
    simp only [L_inv]
    rw [show x₀ + T (y₁ + L x₀) + (x₀ + T (y₂ + L x₀)) + (x₀ + T (y₃ + L x₀)) =
      x₀ + (x₀ + x₀) + (T (y₁ + L x₀) + T (y₂ + L x₀) + T (y₃ + L x₀)) by abel,
      BitString.add_self x₀, add_zero, ← T_add, ← T_add]
    congr 1; rw [show (y₁ + L x₀) + (y₂ + L x₀) + (y₃ + L x₀) =
      (y₁ + y₂ + y₃) + (L x₀ + L x₀) + L x₀ by abel, BitString.add_self, add_zero]
  have hkdim := finrank_sup_add_finrank_inf_bitString U K
  rw [hcompl_inf, hcompl_sup, finrank_bot, add_zero] at hkdim
  have hU_le_m : finrank Bool U ≤ m := by
    rw [finrank_bool_eq_finrank_toZMod, eU.finrank_eq]
    exact (Submodule.finrank_le _).trans (by simp)
  refine ⟨finrank Bool U, finrank Bool K,
    uniformAffine (AffineSubspace.mk' x₀ U) ⟨x₀, AffineSubspace.self_mem_mk' x₀ U⟩,
    uniformAffine (AffineSubspace.mk' (0 : BitString n) K) ⟨0, AffineSubspace.self_mem_mk' 0 K⟩,
    L 0, L_inv,
    ⟨_, _, by rw [AffineSubspace.direction_mk'], rfl⟩,
    ⟨_, _, by rw [AffineSubspace.direction_mk'], rfl⟩,
    by rw [← hdim, hkdim], by omega,
    uniformAffine_eq_bind_add_of_isCompl Asub hx₀ hU_le inf_le_left ⟨hcompl_inf, hcompl_sup⟩,
    ?_, hL_inv, ?_, ?_⟩
  · intro b hb
    have hbK : b ∈ K := by
      simpa [AffineSubspace.mem_mk', vsub_eq_sub] using
        (mem_support_uniformAffine_iff (AffineSubspace.mk' 0 K) _ b).mp hb
    have hLb := hL.toAffineMap.map_vadd (0 : BitString n) b
    have hker : hL.toAffineMap.linear b = 0 := hbK.2
    rw [vadd_eq_add, add_zero, vadd_eq_add, IsAffine.coe_toAffineMap, hker, zero_add] at hLb
    exact hLb
  · intro a ha
    have haU : a -ᵥ x₀ ∈ U := by
      simpa [AffineSubspace.mem_mk'] using
        (mem_support_uniformAffine_iff (AffineSubspace.mk' x₀ U) _ a).mp ha
    have hLa := hL.toAffineMap.map_vadd x₀ (a -ᵥ x₀)
    rw [vsub_vadd, IsAffine.coe_toAffineMap, vadd_eq_add] at hLa
    have hproj : Submodule.projectionOnto _ _ hW
        (fU ⟨toZModBits _ (a -ᵥ x₀), mem_toZModSub.mpr haU⟩) =
        eU ⟨toZModBits _ (a -ᵥ x₀), mem_toZModSub.mpr haU⟩ :=
      Submodule.projectionOnto_apply_left hW ⟨_, LinearMap.mem_range_self fU _⟩
    have hadd : L a + L x₀ = hL.linearMap (a -ᵥ x₀) := by
      rw [hLa, add_assoc, BitString.add_self, add_zero]; rfl
    simp only [L_inv, T, hadd]
    have hyZ : toZModBits (Fin m) (hL.linearMap (a -ᵥ x₀)) =
        fU ⟨toZModBits _ (a -ᵥ x₀), mem_toZModSub.mpr haU⟩ := by
      simp only [fU, toZModLinear, LinearMap.domRestrict_apply, LinearMap.coe_mk, AddHom.coe_mk,
        (toZModBits _).symm_apply_apply]
    rw [hyZ, show TZ (fU ⟨toZModBits _ (a -ᵥ x₀), mem_toZModSub.mpr haU⟩) = toZModBits _ (a -ᵥ x₀)
      by simp only [TZ, LinearMap.comp_apply, LinearEquiv.coe_coe, hproj,
        LinearEquiv.symm_apply_apply, Submodule.coe_subtype],
      (toZModBits _).symm_apply_apply, vsub_eq_sub]; abel
  · intro ℓ hℓ
    obtain ⟨xℓ, hxℓ, rfl⟩ : ∃ x ∈ Asub, L x = ℓ := by
      obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hℓ
      exact ⟨x, (mem_support_uniformAffine_iff Asub ⟨x₀, hx₀⟩ x).mp hx, rfl⟩
    refine ⟨AffineSubspace.mk' xℓ K, ⟨xℓ, AffineSubspace.self_mem_mk' xℓ K⟩,
      by rw [AffineSubspace.direction_mk'], ?_⟩
    ext x
    simp only [SetLike.mem_coe, AffineSubspace.mem_mk', Set.mem_ofPred_eq,
      mem_support_uniformAffine_iff Asub ⟨x₀, hx₀⟩ x, K, Submodule.mem_inf, LinearMap.mem_ker]
    have hv := hL.toAffineMap.linear_apply_vsub x xℓ
    rw [IsAffine.coe_toAffineMap] at hv
    exact ⟨fun ⟨hxA, hker⟩ => ⟨vsub_vadd x xℓ ▸ AffineSubspace.vadd_mem_of_mem_direction hxA hxℓ,
        eq_of_vsub_eq_zero (hv ▸ hker)⟩,
      fun ⟨hxA, hLx⟩ => ⟨AffineSubspace.vsub_mem_direction hxA hxℓ,
        by change hL.toAffineMap.linear (x -ᵥ xℓ) = 0; rw [hv, hLx, vsub_self]⟩⟩

/-! ### Affine Block Decomposition ([Li2023, Lemma 3.10]) -/

/-- Canonical additive equivalence between flat bit strings `BitString (∑ i, b i)` and
partitioned bit-blocks `∀ i : Fin t, BitString (b i)`. -/
@[expose] def blockEquiv {t : ℕ} (b : Fin t → ℕ) :
    BitString (∑ i, b i) ≃+ (∀ i : Fin t, BitString (b i)) where
  toFun x i j := x (finSigmaFinEquiv ⟨i, j⟩)
  invFun g k := g (finSigmaFinEquiv.symm k).1 (finSigmaFinEquiv.symm k).2
  left_inv x := funext fun k => by simp
  right_inv g := funext fun i => funext fun j => by
    change g (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨i, j⟩)).1
      (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨i, j⟩)).2 = g i j
    rw [finSigmaFinEquiv.symm_apply_apply]
  map_add' _ _ := rfl

private theorem blockSlice_codim_le {t r : ℕ} {b : Fin t → ℕ}
    (V_flat : Submodule Bool (BitString (∑ i, b i)))
    (eB : (∀ i : Fin t, BitString (b i)) ≃ₗ[Bool] BitString (∑ i, b i))
    (hr : (∑ i, b i) ≤ finrank Bool V_flat + r) (i : Fin t) :
    b i ≤ finrank Bool
      ↥(V_flat.comap (eB.toLinearMap.comp (LinearMap.single Bool (fun j => BitString (b j)) i))) +
      r := by
  let sfl := eB.toLinearMap.comp (LinearMap.single Bool (fun j => BitString (b j)) i)
  let gZ := (toZModSub V_flat).mkQ.comp (toZModLinear sfl)
  have hker : LinearMap.ker gZ = toZModSub (V_flat.comap sfl) := by
    ext z; obtain ⟨x, rfl⟩ := (toZModBits _).surjective z
    simp only [gZ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, toZModLinear, LinearMap.coe_mk, AddHom.coe_mk,
      (toZModBits _).symm_apply_apply, mem_toZModSub, Submodule.mem_comap]
  have hrank : finrank (ZMod 2) (LinearMap.range gZ) + finrank (ZMod 2) (LinearMap.ker gZ) =
      b i := (LinearMap.finrank_range_add_finrank_ker gZ).trans (by simp)
  have hquot : finrank (ZMod 2) ((Fin (∑ j, b j) → ZMod 2) ⧸ toZModSub V_flat) +
      finrank (ZMod 2) (toZModSub V_flat) = ∑ j, b j :=
    (Submodule.finrank_quotient_add_finrank (toZModSub V_flat)).trans (by simp)
  have hker_dim : finrank (ZMod 2) (LinearMap.ker gZ) =
      finrank Bool ↥(V_flat.comap sfl) := by
    rw [hker, ← finrank_bool_eq_finrank_toZMod]
  have hrange_le : finrank (ZMod 2) (LinearMap.range gZ) ≤
      finrank (ZMod 2) ((Fin (∑ j, b j) → ZMod 2) ⧸ toZModSub V_flat) := Submodule.finrank_le _
  have hvf : finrank (ZMod 2) (toZModSub V_flat) = finrank Bool V_flat :=
    (finrank_bool_eq_finrank_toZMod V_flat).symm
  dsimp only [sfl] at hker_dim
  omega

private theorem blockSlice_mem_of_iSup {t : ℕ} {b : Fin t → ℕ}
    (W : ∀ i : Fin t, Submodule Bool (BitString (b i)))
    {x : ∀ i : Fin t, BitString (b i)}
    (hx : x ∈ ⨆ i : Fin t, (W i).map (LinearMap.single Bool (fun j => BitString (b j)) i)) :
    ∀ i : Fin t, x i ∈ W i := by
  induction hx using Submodule.iSup_induction' with
  | mem j z hz =>
    obtain ⟨z₀, hz₀, rfl⟩ := Submodule.mem_map.mp hz
    intro i; rcases eq_or_ne i j with rfl | hne
    · simpa only [LinearMap.single_apply, Pi.single_eq_same] using hz₀
    · rw [LinearMap.single_apply, Pi.single_eq_of_ne hne]; exact (W i).zero_mem
  | zero => exact fun i => (W i).zero_mem
  | add _ _ _ _ ihx ihy => exact fun i => (W i).add_mem (ihx i) (ihy i)

private def blockEquivLin {t : ℕ} (b : Fin t → ℕ) :
    (∀ i : Fin t, BitString (b i)) ≃ₗ[Bool] BitString (∑ i, b i) :=
  { toAddEquiv := (blockEquiv b).symm
    map_smul' := fun _ _ => rfl }

/-- **Affine Block Decomposition** ([Li2023, Lemma 3.10]):
if `X` is an affine source over `t` bit-blocks `∀ i : Fin t, BitString (b i)` of codimension
`≤ r` (i.e. `(∑ i, b i) - r ≤ k`), then `X` is a convex mixture (`μ.bind`) of independent
product affine sources `PMF.pi (P c)` whose `i`-th block `P c i` is an affine source on
`BitString (b i)` of dimension at least `b i - r`. -/
theorem affineBlockDecomposition {t r k : ℕ} {b : Fin t → ℕ}
    {X : PMF (∀ i : Fin t, BitString (b i))}
    (hX : IsAffineSource (X.map (blockEquiv b).symm) k)
    (hr : (∑ i, b i) ≤ k + r) :
    ∃ (C : Type) (_ : Fintype C) (μ : PMF C)
      (P : C → ∀ i : Fin t, PMF (BitString (b i))),
      (∀ c i, ∃ kᵢ, b i ≤ kᵢ + r ∧ IsAffineSource (P c i) kᵢ) ∧
      X = μ.bind fun c => PMF.pi (P c) := by
  classical
  rcases hX with ⟨A_flat, ⟨x₀_flat, hx₀_flat⟩, hdim_flat, hX_flat⟩
  let eB := blockEquivLin b
  let V_flat := A_flat.direction
  let x₀ := blockEquiv b x₀_flat
  let W : ∀ i : Fin t, Submodule Bool (BitString (b i)) := fun i =>
    V_flat.comap (eB.toLinearMap.comp (LinearMap.single Bool (fun j => BitString (b j)) i))
  let Wprod := ⨆ i : Fin t, (W i).map (LinearMap.single Bool (fun j => BitString (b j)) i)
  let Wprod_flat := Wprod.map eB.toLinearMap
  have hWprod_flat_le : Wprod_flat ≤ V_flat := by
    refine Submodule.map_le_iff_le_comap.mpr (iSup_le fun i => ?_)
    exact Submodule.map_le_iff_le_comap.mpr le_rfl
  obtain ⟨C_flat, hC_le, hC_inf, hC_sup⟩ :=
    exists_isCompl_submodule Wprod_flat V_flat hWprod_flat_le
  have hsum_single : ∀ (f : ∀ i : Fin t, BitString (b i)),
      (∑ i : Fin t, Pi.single i (f i)) = f := fun f => funext fun i => by
    simp [Finset.sum_apply]
  have heW : ∀ w : ∀ i : Fin t, W i, eB (fun i => (w i).1) ∈ Wprod_flat := fun w =>
    Submodule.mem_map.mpr ⟨_, hsum_single (fun i => (w i).1) ▸ Submodule.sum_mem Wprod fun i _ =>
      Submodule.mem_iSup_of_mem i (Submodule.mem_map.mpr ⟨(w i).1, (w i).2, rfl⟩), rfl⟩
  let e_dir : C_flat × (∀ i : Fin t, W i) ≃ V_flat :=
    (Equiv.prodCongr (Equiv.refl C_flat)
      { toFun := fun w => ⟨eB (fun i => (w i).1), heW w⟩
        invFun := fun wf => fun i => ⟨(eB.symm wf.1) i,
          by obtain ⟨u, hu, huf⟩ := Submodule.mem_map.mp wf.2
             have heq : eB.symm wf.1 = u := eB.injective (by
               change eB (eB.symm wf.1) = eB u; rw [eB.apply_symm_apply]; exact huf.symm)
             exact heq ▸ blockSlice_mem_of_iSup W hu i⟩
        left_inv := fun w => funext fun i => Subtype.ext (congrFun (eB.symm_apply_apply _) i)
        right_inv := fun wf => Subtype.ext (eB.apply_symm_apply wf.1) }).trans
      (isCompl_prodEquiv hC_le hWprod_flat_le ⟨hC_inf, hC_sup⟩)
  let P : C_flat → ∀ i : Fin t, PMF (BitString (b i)) := fun c i =>
    uniformAffine (AffineSubspace.mk' (x₀ i + (blockEquiv b c.1) i) (W i))
      ⟨_, AffineSubspace.self_mem_mk' _ _⟩
  have hX_eq : X = (uniformAffine A_flat ⟨x₀_flat, hx₀_flat⟩).map (blockEquiv b) := by
    rw [← hX_flat, PMF.map_comp,
      show (⇑(blockEquiv b) ∘ ⇑(blockEquiv b).symm) = id from
        funext (blockEquiv b).apply_symm_apply, PMF.map_id]
  refine ⟨C_flat, inferInstance, PMF.uniformOfFintype C_flat, P,
    fun c i => ⟨finrank Bool (W i), blockSlice_codim_le V_flat eB (hdim_flat ▸ hr) i,
      _, _, by rw [AffineSubspace.direction_mk'], rfl⟩, ?_⟩
  have hbind : ((PMF.uniformOfFintype (C_flat × (∀ i : Fin t, W i))).map
      fun p => blockEquiv b (x₀_flat + (e_dir p).1)) =
      (PMF.uniformOfFintype C_flat).bind fun c =>
        (PMF.uniformOfFintype (∀ i : Fin t, W i)).map fun w =>
          blockEquiv b (x₀_flat + (e_dir (c, w)).1) :=
    (uniformOfFintype_bind_map fun c w => blockEquiv b (x₀_flat + (e_dir (c, w)).1)).symm
  rw [hX_eq, uniformAffine_eq_map_direction A_flat hx₀_flat, ← uniformOfFintype_map_equiv e_dir,
    PMF.map_comp, PMF.map_comp]
  change (PMF.uniformOfFintype (C_flat × (∀ i : Fin t, W i))).map
    (fun p => blockEquiv b (x₀_flat + (e_dir p).1)) = _
  rw [hbind]
  refine congrArg (PMF.bind _) (funext fun c => ?_)
  have hpi : PMF.pi (P c) = (PMF.uniformOfFintype (∀ i : Fin t, W i)).map
      fun w i => x₀ i + blockEquiv b c.1 i + (w i).1 := by
    have : P c = fun i => (PMF.uniformOfFintype (W i)).map
        fun w => x₀ i + blockEquiv b c.1 i + w.1 :=
      funext fun i => uniformAffine_mk'_eq_map _ (W i)
    rw [this, PMF.pi_map, PMF.pi_uniformOfFintype]
  rw [hpi]
  exact congrArg (PMF.map · _) (funext fun w => funext fun i => by
    change (blockEquiv b (x₀_flat + (c.1 + (blockEquiv b).symm fun j => (w j).1))) i = _
    simp only [map_add, (blockEquiv b).apply_symm_apply, Pi.add_apply, x₀, add_assoc])

/-! ### Bridges from affine and sumset extractors to `IsAffineDisperser` ([Li2023, Cor. 7.14]) -/

/-- A seedless **`(k, ε)` affine extractor** maps every `(n, k)` affine source to within statistical
distance `ε` of the uniform distribution on `BitString m` ([Li2023]). -/
@[expose] def IsAffineExtractor {n m : ℕ} (ext : BitString n → BitString m)
    (k : ℕ) (ε : ℝ) : Prop :=
  ∀ X : PMF (BitString n), IsAffineSource X k →
    dist (X.map ext) (PMF.uniformOfFintype (BitString m)) ≤ ε

/-- A **`(k₁, k₂, ε)` sumset extractor** maps the XOR-sum `A + B` of any two independent sources
`A, B` of min-entropy at least `k₁` and `k₂` to within statistical distance `ε` of uniform
([Li2023, Thm. 7.13]). -/
@[expose] def IsSumsetExtractor {n m : ℕ} (ext : BitString n → BitString m) (k₁ k₂ : ℕ)
    (ε : ℝ) : Prop :=
  ∀ A B : PMF (BitString n), (k₁ : ℝ) ≤ minEntropy A → (k₂ : ℝ) ≤ minEntropy B →
    dist ((A.bind fun a => B.map fun b => a + b).map ext)
      (PMF.uniformOfFintype (BitString m)) ≤ ε

/-- Extracting one bit of an `m`-bit affine extractor with error `< 1 / 2` gives an
`IsAffineDisperser` for dimension `k`. -/
theorem isAffineDisperser_of_isAffineExtractor {n m k : ℕ} {ε : ℝ}
    {ext : BitString n → BitString m} (hm : 0 < m) (hε : ε < 1 / 2)
    (hext : IsAffineExtractor ext k ε) :
    IsAffineDisperser (fun x => ext x ⟨0, hm⟩) k := by
  have hproj : (PMF.uniformOfFintype (BitString m)).map (fun y => y ⟨0, hm⟩) =
      PMF.uniformOfFintype Bool := by
    rw [← pi_uniformOfFintype (α := fun _ : Fin m => Bool), pi_map_eval]
  have hnot_const : ∀ (A : AffineSubspace Bool (BitString n))
      (hA : (A : Set (BitString n)).Nonempty),
      finrank Bool A.direction = k →
      ¬∃ c : Bool, ∀ x ∈ A, ext x ⟨0, hm⟩ = c := by
    rintro A ⟨x₀, hx₀⟩ hdim ⟨c, hc⟩
    have hdist : dist ((uniformAffine A ⟨x₀, hx₀⟩).map fun x => ext x ⟨0, hm⟩)
        (PMF.uniformOfFintype Bool) ≤ ε := by
      have hd := (dist_map_le ((uniformAffine A ⟨x₀, hx₀⟩).map ext)
        (PMF.uniformOfFintype (BitString m)) (fun y => y ⟨0, hm⟩)).trans
        (hext _ ⟨A, ⟨x₀, hx₀⟩, hdim, rfl⟩)
      rwa [PMF.map_comp, hproj] at hd
    have hpure : (uniformAffine A ⟨x₀, hx₀⟩).map (fun x => ext x ⟨0, hm⟩) = PMF.pure c := by
      classical
      rw [uniformAffine_eq_map_direction A hx₀, PMF.map_comp]
      rw [show ((fun x => ext x ⟨0, hm⟩) ∘ fun v : A.direction => x₀ + v.1) =
        Function.const A.direction c from funext fun v => hc _ (by
          dsimp only; rw [add_comm]; exact AffineSubspace.vadd_mem_of_mem_direction v.2 hx₀)]
      exact PMF.map_const ..
    rw [hpure, dist_uniformOfFintype_bool] at hdist
    cases c <;> simp at hdist <;> norm_num at hdist <;> linarith
  have hk_pos : 0 < k := Nat.pos_of_ne_zero fun hk => hnot_const (AffineSubspace.mk' 0 ⊥)
    ⟨0, AffineSubspace.self_mem_mk' 0 ⊥⟩ (by rw [AffineSubspace.direction_mk', finrank_bot, hk])
    ⟨ext 0 ⟨0, hm⟩, fun x hx => by
      have : x = 0 := by simpa [AffineSubspace.mem_mk', vsub_eq_sub] using hx
      subst this; rfl⟩
  refine isAffineDisperser_of_forall_exists_ne fun A hdim => by
    have hA : (A : Set (BitString n)).Nonempty := Set.nonempty_iff_ne_empty.mpr fun he => by
      have hbot : A = ⊥ := SetLike.coe_injective he
      rw [hbot, AffineSubspace.direction_bot, finrank_bot] at hdim; omega
    by_contra hconst; push Not at hconst
    obtain ⟨x₀, hx₀⟩ := hA
    exact hnot_const A ⟨x₀, hx₀⟩ hdim ⟨ext x₀ ⟨0, hm⟩, fun x hx => hconst x hx x₀ hx₀⟩

/-- Splitting an `(n, k)` affine source with `k₁ + k₂ ≤ k` into a sum `A + B` of two
independent affine sources of dimensions `k₁` and `k - k₁ ≥ k₂`. -/
theorem exists_independent_affine_sum_of_isAffineSource {n k k₁ k₂ : ℕ}
    {X : PMF (BitString n)} (hX : IsAffineSource X k) (hk : k₁ + k₂ ≤ k) :
    ∃ A B : PMF (BitString n), IsAffineSource A k₁ ∧ IsAffineSource B (k - k₁) ∧
      (k₂ : ℝ) ≤ minEntropy B ∧ X = A.bind fun a => B.map fun b => a + b := by
  rcases hX with ⟨Asub, ⟨x₀, hx₀⟩, hdim, rfl⟩
  obtain ⟨V₁, hV₁_le, hV₁_dim⟩ :=
    exists_submodule_finrank_eq_bitString Asub.direction k₁ (by omega)
  obtain ⟨V₂, hV₂_le, hcompl_inf, hcompl_sup⟩ :=
    exists_isCompl_submodule V₁ Asub.direction hV₁_le
  have hV₂_dim : finrank Bool V₂ = k - k₁ := by
    have hsum := finrank_sup_add_finrank_inf_bitString V₂ V₁
    rw [hcompl_inf, hcompl_sup, finrank_bot, add_zero, hdim, hV₁_dim] at hsum; omega
  refine ⟨uniformAffine (AffineSubspace.mk' x₀ V₁) ⟨x₀, AffineSubspace.self_mem_mk' x₀ V₁⟩,
    uniformAffine (AffineSubspace.mk' (0 : BitString n) V₂) ⟨0, AffineSubspace.self_mem_mk' 0 V₂⟩,
    ⟨_, _, by rw [AffineSubspace.direction_mk', hV₁_dim], rfl⟩,
    ⟨_, _, by rw [AffineSubspace.direction_mk', hV₂_dim], rfl⟩, ?_,
    uniformAffine_eq_bind_add_of_isCompl Asub hx₀ hV₁_le hV₂_le
      ⟨by rw [inf_comm]; exact hcompl_inf, by rw [sup_comm]; exact hcompl_sup⟩⟩
  calc (k₂ : ℝ) ≤ ((k - k₁ : ℕ) : ℝ) := by exact_mod_cast (by omega : k₂ ≤ k - k₁)
    _ = finrank Bool (AffineSubspace.mk' (0 : BitString n) V₂).direction := by
        rw [AffineSubspace.direction_mk', hV₂_dim]
    _ = minEntropy _ :=
        (minEntropy_uniformAffine (AffineSubspace.mk' (0 : BitString n) V₂) _).symm

/-- A `(k₁, k₂, ε)` sumset extractor is a `(k, ε)` affine extractor whenever `k₁ + k₂ ≤ k`
([Li2023, Cor. 7.14]). -/
theorem isAffineExtractor_of_isSumsetExtractor {n m k k₁ k₂ : ℕ} {ε : ℝ}
    {ext : BitString n → BitString m} (hk : k₁ + k₂ ≤ k)
    (hext : IsSumsetExtractor ext k₁ k₂ ε) :
    IsAffineExtractor ext k ε := fun _ hX => by
  obtain ⟨A, B, hA, _, hkB, rfl⟩ := exists_independent_affine_sum_of_isAffineSource hX hk
  exact hext A B (minEntropy_of_isAffineSource hA).ge hkB

/-- A `(k₁, k₂, ε)` sumset extractor outputting at least one bit with `ε < 1 / 2` yields an
`IsAffineDisperser` for dimension `k ≥ k₁ + k₂` ([Li2023, Cor. 7.14]). -/
theorem isAffineDisperser_of_isSumsetExtractor {n m k k₁ k₂ : ℕ} {ε : ℝ}
    {ext : BitString n → BitString m} (hm : 0 < m) (hε : ε < 1 / 2) (hk : k₁ + k₂ ≤ k)
    (hext : IsSumsetExtractor ext k₁ k₂ ε) :
    IsAffineDisperser (fun x => ext x ⟨0, hm⟩) k :=
  isAffineDisperser_of_isAffineExtractor hm hε (isAffineExtractor_of_isSumsetExtractor hk hext)

end AffineSource

end Cslib.AffineDisperser.Li
