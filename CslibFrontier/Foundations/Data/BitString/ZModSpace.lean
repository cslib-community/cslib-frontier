/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.ZModTwo
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Linear algebra of bit-string spaces via `ZMod 2`

Mathlib equips `Bool` with a `BooleanRing` instance (addition is `xor`, multiplication is `and`), so
`ι → Bool` and `BitString n` are `Bool`-modules, whereas field-level linear algebra (`Basis`,
`Submodule.exists_isCompl`, `Matrix.rank`, rank-nullity, and orthogonal duality) requires a `Field`
instance such as `ZMod 2`.

Building on the computable ring isomorphism `Cslib.BitString.bitEquiv : ZMod 2 ≃+* Bool`, this
module constructs the coordinatewise semilinear isomorphism `Cslib.BitString.toZModSpace`, the
induced submodule lattice isomorphism `Cslib.BitString.submoduleZModIso`, the linear-map equivalence
`Cslib.BitString.linearMapZModEquiv`, and the standard dot-product orthogonal complement
`Cslib.BitString.orthogonal`, transferring dimension, complements, rank-nullity, and dual-code
dimension between `Bool` and `ZMod 2`.

## Main definitions

* `Cslib.BitString.toZModSpace`: coordinatewise semilinear isomorphism
  `(ι → Bool) ≃ₛₗ[bitEquiv.symm.toRingHom] (ι → ZMod 2)`.
* `Cslib.BitString.submoduleZModIso`: order isomorphism
  `Submodule Bool (ι → Bool) ≃o Submodule (ZMod 2) (ι → ZMod 2)`.
* `Cslib.BitString.linearMapZModEquiv`: additive equivalence between `Bool`-linear maps and
  `(ZMod 2)`-linear maps on coordinate spaces.
* `Cslib.BitString.orthogonal`: orthogonal complement `{y | ∀ x ∈ V, x ⬝ᵥ y = 0}` under
  `dotProduct`.

## Main results

* `Cslib.BitString.finrank_submoduleZModIso`, `Cslib.BitString.natCard_submodule_bool`: preservation
  of `Module.finrank` and `Nat.card V = 2 ^ finrank Bool V`.
* `Cslib.BitString.exists_isCompl_bool`, `Cslib.BitString.exists_isCompl_submodule_bool`: complement
  existence for `Bool`-submodules of `ι → Bool`.
* `Cslib.BitString.finrank_sup_add_finrank_inf_bool`,
  `Cslib.BitString.finrank_map_add_finrank_inf_ker_bool`,
  `Cslib.BitString.finrank_range_add_finrank_ker_bool`,
  `Cslib.BitString.finrank_comap_codim_le_bool`,
  `Cslib.BitString.exists_submodule_finrank_eq_bool`: modular dimension law, rank-nullity, slice
  codimension bound, and existence of subspaces of prescribed dimension over `Bool`.
* `Cslib.BitString.linearMapZModEquiv_mulVecLin`, `Cslib.BitString.submoduleZModIso_ker`: matrix
  multiplication and kernel compatibility across `Bool` and `ZMod 2`.
* `Cslib.BitString.finrank_orthogonal_add_finrank`, `Cslib.BitString.orthogonal_orthogonal`,
  `Cslib.BitString.finrank_orthogonal_add_finrank_bool`,
  `Cslib.BitString.orthogonal_orthogonal_bool`: dual orthogonal dimension and double-orthogonal
  involution over fields and over `Bool`.
-/

public section

namespace Cslib.BitString

open Matrix Module

instance instRingHomInvPairBitEquiv :
    RingHomInvPair bitEquiv.toRingHom bitEquiv.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv bitEquiv

instance instRingHomInvPairBitEquivSymm :
    RingHomInvPair bitEquiv.symm.toRingHom bitEquiv.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm bitEquiv

/-! ### Coordinatewise and submodule isomorphisms -/

/-- Coordinatewise semilinear isomorphism `(ι → Bool) ≃ₛₗ[bitEquiv.symm] (ι → ZMod 2)`, reading
`false` as `0` and `true` as `1`. -/
@[expose] def toZModSpace (ι : Type*) :
    (ι → Bool) ≃ₛₗ[bitEquiv.symm.toRingHom] (ι → ZMod 2) where
  toFun v i := bitEquiv.symm (v i)
  invFun v i := bitEquiv (v i)
  left_inv v := funext fun i => bitEquiv.apply_symm_apply (v i)
  right_inv v := funext fun i => bitEquiv.symm_apply_apply (v i)
  map_add' u v := funext fun i => map_add bitEquiv.symm (u i) (v i)
  map_smul' c v := funext fun i => map_mul bitEquiv.symm c (v i)

@[simp]
theorem toZModSpace_apply {ι : Type*} (v : ι → Bool) (i : ι) :
    toZModSpace ι v i = bitEquiv.symm (v i) :=
  rfl

@[simp]
theorem toZModSpace_symm_apply {ι : Type*} (v : ι → ZMod 2) (i : ι) :
    (toZModSpace ι).symm v i = bitEquiv (v i) :=
  rfl

/-- `toZModSpace` intertwines standard dot products via `bitEquiv.symm`. -/
theorem toZModSpace_dotProduct {ι : Type*} [Fintype ι] (u v : ι → Bool) :
    toZModSpace ι u ⬝ᵥ toZModSpace ι v = bitEquiv.symm (u ⬝ᵥ v) := by
  simp only [dotProduct, toZModSpace_apply, map_sum, map_mul]

/-- Order isomorphism between `Bool`-submodules of `ι → Bool` and `(ZMod 2)`-subspaces of
`ι → ZMod 2`. -/
def submoduleZModIso (ι : Type*) :
    Submodule Bool (ι → Bool) ≃o Submodule (ZMod 2) (ι → ZMod 2) :=
  Submodule.orderIsoMapComap (toZModSpace ι)

@[simp]
theorem mem_submoduleZModIso {ι : Type*} {V : Submodule Bool (ι → Bool)} {z : ι → ZMod 2} :
    z ∈ submoduleZModIso ι V ↔ (toZModSpace ι).symm z ∈ V := by
  rw [submoduleZModIso, Submodule.orderIsoMapComap_apply, Submodule.mem_map]
  exact ⟨fun ⟨x, hx, hxz⟩ => hxz ▸ ((toZModSpace ι).symm_apply_apply x).symm ▸ hx,
    fun hz => ⟨(toZModSpace ι).symm z, hz, (toZModSpace ι).apply_symm_apply z⟩⟩

theorem toZModSpace_mem_submoduleZModIso {ι : Type*} {V : Submodule Bool (ι → Bool)}
    {x : ι → Bool} :
    toZModSpace ι x ∈ submoduleZModIso ι V ↔ x ∈ V := by
  rw [mem_submoduleZModIso, (toZModSpace ι).symm_apply_apply]

@[simp]
theorem mem_submoduleZModIso_symm {ι : Type*} {W : Submodule (ZMod 2) (ι → ZMod 2)}
    {x : ι → Bool} :
    x ∈ (submoduleZModIso ι).symm W ↔ toZModSpace ι x ∈ W :=
  Iff.rfl

/-- `submoduleZModIso` maps `Bool`-spans to `(ZMod 2)`-spans of the translated generators. -/
theorem submoduleZModIso_span (ι : Type*) (s : Set (ι → Bool)) :
    submoduleZModIso ι (Submodule.span Bool s) = Submodule.span (ZMod 2) (toZModSpace ι '' s) :=
  Submodule.map_span (toZModSpace ι : (ι → Bool) →ₛₗ[bitEquiv.symm.toRingHom] (ι → ZMod 2)) s

/-! ### Linear map conjugation -/

/-- Additive equivalence between `Bool`-linear maps `(ι₁ → Bool) →ₗ[Bool] (ι₂ → Bool)` and
`(ZMod 2)`-linear maps `(ι₁ → ZMod 2) →ₗ[ZMod 2] (ι₂ → ZMod 2)`. -/
def linearMapZModEquiv (ι₁ ι₂ : Type*) :
    ((ι₁ → Bool) →ₗ[Bool] (ι₂ → Bool)) ≃+ ((ι₁ → ZMod 2) →ₗ[ZMod 2] (ι₂ → ZMod 2)) where
  toFun f :=
    { toFun := fun z => toZModSpace ι₂ (f ((toZModSpace ι₁).symm z))
      map_add' := fun _ _ => by simp only [map_add]
      map_smul' := fun c z => by
        rw [(toZModSpace ι₁).symm.map_smulₛₗ, map_smul, (toZModSpace ι₂).map_smulₛₗ]
        simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, bitEquiv.symm_apply_apply,
          RingHom.id_apply] }
  invFun g :=
    { toFun := fun x => (toZModSpace ι₂).symm (g (toZModSpace ι₁ x))
      map_add' := fun _ _ => by simp only [map_add]
      map_smul' := fun c x => by
        rw [(toZModSpace ι₁).map_smulₛₗ, map_smul, (toZModSpace ι₂).symm.map_smulₛₗ]
        simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, bitEquiv.apply_symm_apply,
          RingHom.id_apply] }
  left_inv f := LinearMap.ext fun x => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.symm_apply_apply]
  right_inv g := LinearMap.ext fun z => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply]
  map_add' f₁ f₂ := LinearMap.ext fun z => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add]

@[simp]
theorem linearMapZModEquiv_apply {ι₁ ι₂ : Type*}
    (f : (ι₁ → Bool) →ₗ[Bool] (ι₂ → Bool)) (z : ι₁ → ZMod 2) :
    linearMapZModEquiv ι₁ ι₂ f z = toZModSpace ι₂ (f ((toZModSpace ι₁).symm z)) := by
  rfl

theorem linearMapZModEquiv_toZModSpace {ι₁ ι₂ : Type*}
    (f : (ι₁ → Bool) →ₗ[Bool] (ι₂ → Bool)) (x : ι₁ → Bool) :
    linearMapZModEquiv ι₁ ι₂ f (toZModSpace ι₁ x) = toZModSpace ι₂ (f x) := by
  rw [linearMapZModEquiv_apply, (toZModSpace ι₁).symm_apply_apply]

@[simp]
theorem linearMapZModEquiv_symm_apply {ι₁ ι₂ : Type*}
    (g : (ι₁ → ZMod 2) →ₗ[ZMod 2] (ι₂ → ZMod 2)) (x : ι₁ → Bool) :
    (linearMapZModEquiv ι₁ ι₂).symm g x = (toZModSpace ι₂).symm (g (toZModSpace ι₁ x)) := by
  rfl

theorem submoduleZModIso_map {ι₁ ι₂ : Type*} (f : (ι₁ → Bool) →ₗ[Bool] (ι₂ → Bool))
    (V : Submodule Bool (ι₁ → Bool)) :
    submoduleZModIso ι₂ (V.map f) = (submoduleZModIso ι₁ V).map (linearMapZModEquiv ι₁ ι₂ f) := by
  ext y
  obtain ⟨w, rfl⟩ := (toZModSpace ι₂).surjective y
  simp only [toZModSpace_mem_submoduleZModIso, Submodule.mem_map]
  refine ⟨fun ⟨x, hx, h⟩ => ⟨toZModSpace ι₁ x, toZModSpace_mem_submoduleZModIso.mpr hx,
      by rw [linearMapZModEquiv_toZModSpace, h]⟩,
    fun ⟨z, hz, h⟩ => ⟨(toZModSpace ι₁).symm z, mem_submoduleZModIso.mp hz,
      (toZModSpace ι₂).injective (by rwa [← linearMapZModEquiv_apply])⟩⟩

theorem submoduleZModIso_comap {ι₁ ι₂ : Type*} (f : (ι₁ → Bool) →ₗ[Bool] (ι₂ → Bool))
    (W : Submodule Bool (ι₂ → Bool)) :
    submoduleZModIso ι₁ (W.comap f) =
      (submoduleZModIso ι₂ W).comap (linearMapZModEquiv ι₁ ι₂ f) := by
  ext z
  obtain ⟨x, rfl⟩ := (toZModSpace ι₁).surjective z
  simp only [toZModSpace_mem_submoduleZModIso, Submodule.mem_comap, linearMapZModEquiv_toZModSpace]

theorem submoduleZModIso_ker {ι₁ ι₂ : Type*} (f : (ι₁ → Bool) →ₗ[Bool] (ι₂ → Bool)) :
    submoduleZModIso ι₁ (LinearMap.ker f) = LinearMap.ker (linearMapZModEquiv ι₁ ι₂ f) := by
  rw [← Submodule.comap_bot, submoduleZModIso_comap, map_bot]
  rfl

theorem submoduleZModIso_range {ι₁ ι₂ : Type*} (f : (ι₁ → Bool) →ₗ[Bool] (ι₂ → Bool)) :
    submoduleZModIso ι₂ (LinearMap.range f) = LinearMap.range (linearMapZModEquiv ι₁ ι₂ f) := by
  rw [← Submodule.map_top, submoduleZModIso_map, map_top, Submodule.map_top]

/-- Conjugating `H.mulVecLin` along `toZModSpace` yields `(H.map bitEquiv.symm).mulVecLin`. -/
theorem linearMapZModEquiv_mulVecLin {ι₁ ι₂ : Type*} [Fintype ι₁] (H : Matrix ι₂ ι₁ Bool) :
    linearMapZModEquiv ι₁ ι₂ H.mulVecLin = (H.map bitEquiv.symm).mulVecLin := by
  ext z i
  obtain ⟨x, rfl⟩ := (toZModSpace ι₁).surjective z
  simp only [linearMapZModEquiv_toZModSpace, mulVecLin_apply, mulVec, dotProduct, toZModSpace_apply,
    Matrix.map_apply, map_sum, map_mul]

/-! ### Dimension, cardinality, complements, and rank-nullity over `Bool` -/

/-- `submoduleZModIso` preserves `Module.finrank`. -/
@[simp]
theorem finrank_submoduleZModIso {ι : Type*} (V : Submodule Bool (ι → Bool)) :
    finrank (ZMod 2) (submoduleZModIso ι V) = finrank Bool V :=
  (congrArg Cardinal.toNat <|
    rank_eq_of_equiv_equiv (R := Bool) (R' := ZMod 2) (M := V) (M₁ := submoduleZModIso ι V)
      bitEquiv.symm ((toZModSpace ι).submoduleMap V).toAddEquiv bitEquiv.symm.bijective
      fun c v => Subtype.ext (map_smulₛₗ (toZModSpace ι) c v.val)).symm

/-- A `Bool`-submodule `V` of a finite coordinate space `ι → Bool` has `2 ^ finrank Bool V`
elements. -/
theorem natCard_submodule_bool {ι : Type*} [Finite ι] (V : Submodule Bool (ι → Bool)) :
    Nat.card V = 2 ^ finrank Bool V := by
  have eV : V ≃ submoduleZModIso ι V := ((toZModSpace ι).submoduleMap V).toEquiv
  have : Finite (submoduleZModIso ι V) := Finite.of_equiv V eV
  rw [Nat.card_congr eV, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    finrank_submoduleZModIso]

/-- Every `Bool`-submodule of `ι → Bool` has a direct-sum complement. -/
theorem exists_isCompl_bool {ι : Type*} (U : Submodule Bool (ι → Bool)) :
    ∃ W : Submodule Bool (ι → Bool), IsCompl U W := by
  obtain ⟨WZ, hWZ⟩ := Submodule.exists_isCompl (submoduleZModIso ι U)
  exact ⟨(submoduleZModIso ι).symm WZ, by
    simpa only [(submoduleZModIso ι).symm_apply_apply] using
      (submoduleZModIso ι).symm.isCompl_iff.mp hWZ⟩

/-- Relative complement existence inside a `Bool`-submodule `V` of `ι → Bool`. -/
theorem exists_isCompl_submodule_bool {ι : Type*} {K V : Submodule Bool (ι → Bool)}
    (hKV : K ≤ V) :
    ∃ U : Submodule Bool (ι → Bool), U ≤ V ∧ U ⊓ K = ⊥ ∧ U ⊔ K = V := by
  let VZ := submoduleZModIso ι V
  obtain ⟨UZ, hUZ⟩ := Submodule.exists_isCompl ((submoduleZModIso ι K).comap VZ.subtype)
  refine ⟨(submoduleZModIso ι).symm (UZ.map VZ.subtype), ?_, ?_, ?_⟩
  · rw [← (submoduleZModIso ι).le_iff_le, (submoduleZModIso ι).apply_symm_apply]
    exact Submodule.map_subtype_le _ _
  · rw [eq_bot_iff, ← (submoduleZModIso ι).le_iff_le, map_inf,
      (submoduleZModIso ι).apply_symm_apply, map_bot]
    rintro y ⟨hy1, hy2⟩
    obtain ⟨⟨w, hwV⟩, hwU, rfl⟩ := Submodule.mem_map.mp hy1
    have hmem : (⟨w, hwV⟩ : VZ) ∈ (submoduleZModIso ι K).comap VZ.subtype ⊓ UZ := ⟨hy2, hwU⟩
    rw [hUZ.inf_eq_bot, Submodule.mem_bot] at hmem
    rcases congrArg Subtype.val hmem with rfl
    exact Submodule.zero_mem _
  · refine le_antisymm (sup_le (by
      rw [← (submoduleZModIso ι).le_iff_le, (submoduleZModIso ι).apply_symm_apply]
      exact Submodule.map_subtype_le _ _) hKV) ?_
    rw [← (submoduleZModIso ι).le_iff_le, map_sup, (submoduleZModIso ι).apply_symm_apply, sup_comm]
    intro w hw
    obtain ⟨k, hk, u, hu, hku⟩ := Submodule.mem_sup.mp
      (hUZ.sup_eq_top ▸ Submodule.mem_top : (⟨w, hw⟩ : VZ) ∈ _)
    exact Submodule.mem_sup.mpr ⟨k.val, hk, u.val, Submodule.mem_map.mpr ⟨u, hu, rfl⟩,
      congrArg Subtype.val hku⟩

/-- Modular dimension identity for the sum and intersection of two `Bool`-submodules of `ι → Bool`.
-/
theorem finrank_sup_add_finrank_inf_bool {ι : Type*} [Finite ι]
    (U K : Submodule Bool (ι → Bool)) :
    finrank Bool ↥(U ⊔ K) + finrank Bool ↥(U ⊓ K) = finrank Bool U + finrank Bool K := by
  have : Finite (ι → ZMod 2) := Finite.of_equiv (ι → Bool) (toZModSpace ι).toEquiv
  simp_rw [← finrank_submoduleZModIso]
  rw [map_sup, map_inf]
  exact Submodule.finrank_sup_add_finrank_inf_eq _ _

/-- Rank-nullity for a `Bool`-linear map restricted to a submodule `V` of `ι₁ → Bool`. -/
theorem finrank_map_add_finrank_inf_ker_bool {ι₁ ι₂ : Type*} [Finite ι₁]
    (f : (ι₁ → Bool) →ₗ[Bool] (ι₂ → Bool)) (V : Submodule Bool (ι₁ → Bool)) :
    finrank Bool ↥(V.map f) + finrank Bool ↥(V ⊓ LinearMap.ker f) = finrank Bool V := by
  let fZ := linearMapZModEquiv ι₁ ι₂ f
  let VZ := submoduleZModIso ι₁ V
  have hmap : submoduleZModIso ι₂ (V.map f) = LinearMap.range (fZ.domRestrict VZ) := by
    rw [submoduleZModIso_map, LinearMap.range_domRestrict]
  have hker : submoduleZModIso ι₁ (V ⊓ LinearMap.ker f) = VZ ⊓ LinearMap.ker fZ := by
    rw [map_inf, submoduleZModIso_ker]
  let eK : LinearMap.ker (fZ.domRestrict VZ) ≃ₗ[ZMod 2] ↥(VZ ⊓ LinearMap.ker fZ) :=
    { toFun := fun v => ⟨v.val.val, v.val.property, LinearMap.mem_ker.mpr v.property⟩
      invFun := fun w => ⟨⟨w.val, w.property.1⟩, LinearMap.mem_ker.mpr w.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have : Finite (ι₁ → ZMod 2) := Finite.of_equiv (ι₁ → Bool) (toZModSpace ι₁).toEquiv
  simp_rw [← finrank_submoduleZModIso]
  rw [hmap, hker, ← eK.finrank_eq]
  exact LinearMap.finrank_range_add_finrank_ker (fZ.domRestrict VZ)

/-- Rank-nullity on the full coordinate space `ι₁ → Bool`. -/
theorem finrank_range_add_finrank_ker_bool {ι₁ ι₂ : Type*} [Fintype ι₁]
    (f : (ι₁ → Bool) →ₗ[Bool] (ι₂ → Bool)) :
    finrank Bool (LinearMap.range f) + finrank Bool (LinearMap.ker f) = Fintype.card ι₁ := by
  have h := finrank_map_add_finrank_inf_ker_bool f ⊤
  rwa [Submodule.map_top, top_inf_eq, ← finrank_submoduleZModIso ⊤, map_top, finrank_top,
    Module.finrank_fintype_fun_eq_card] at h

/-- Preimage codimension bound: pulling back a `Bool`-submodule `V` of `ι₂ → Bool` along any
`Bool`-linear map `f : (ι₁ → Bool) →ₗ[Bool] (ι₂ → Bool)` increases codimension by at most `0`, i.e.
`codim (V.comap f) ≤ codim V`. -/
theorem finrank_comap_codim_le_bool {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (f : (ι₁ → Bool) →ₗ[Bool] (ι₂ → Bool)) (V : Submodule Bool (ι₂ → Bool)) :
    Fintype.card ι₁ + finrank Bool V ≤ finrank Bool ↥(V.comap f) + Fintype.card ι₂ := by
  let VZ := submoduleZModIso ι₂ V
  let gZ := VZ.mkQ.comp (linearMapZModEquiv ι₁ ι₂ f)
  have hker : LinearMap.ker gZ = submoduleZModIso ι₁ (V.comap f) := by
    rw [submoduleZModIso_comap]
    ext z
    simp only [gZ, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, VZ]
  have hrank := (LinearMap.finrank_range_add_finrank_ker gZ).trans
    (Module.finrank_fintype_fun_eq_card _)
  have hquot := (Submodule.finrank_quotient_add_finrank VZ).trans
    (Module.finrank_fintype_fun_eq_card _)
  have hle : finrank (ZMod 2) (LinearMap.range gZ) ≤ finrank (ZMod 2) ((ι₂ → ZMod 2) ⧸ VZ) :=
    Submodule.finrank_le _
  rw [hker, finrank_submoduleZModIso] at hrank
  rw [finrank_submoduleZModIso] at hquot
  omega

/-- Every `Bool`-submodule `V` of `ι → Bool` of dimension at least `k` contains a `k`-dimensional
`Bool`-submodule. -/
theorem exists_submodule_finrank_eq_bool {ι : Type*} [Finite ι]
    (V : Submodule Bool (ι → Bool)) (k : ℕ) (hk : k ≤ finrank Bool V) :
    ∃ U : Submodule Bool (ι → Bool), U ≤ V ∧ finrank Bool U = k := by
  have : Finite (ι → ZMod 2) := Finite.of_equiv (ι → Bool) (toZModSpace ι).toEquiv
  rw [← finrank_submoduleZModIso] at hk
  let B0 := Module.finBasis (ZMod 2) (submoduleZModIso ι V)
  let g : Fin k → ι → ZMod 2 := fun i => B0 (Fin.castLE hk i)
  let UZ := Submodule.span (ZMod 2) (Set.range g)
  have hli : LinearIndependent (ZMod 2) g :=
    (B0.linearIndependent.comp _ (Fin.castLE_injective hk)).map'
      (submoduleZModIso ι V).subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  refine ⟨(submoduleZModIso ι).symm UZ, ?_, ?_⟩
  · rw [← (submoduleZModIso ι).le_iff_le, (submoduleZModIso ι).apply_symm_apply]
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (B0 _).property)
  · rw [← finrank_submoduleZModIso, (submoduleZModIso ι).apply_symm_apply, finrank_span_eq_card hli,
      Fintype.card_fin]

/-! ### Orthogonal complement (dual code) over fields and `Bool` -/

section Orthogonal

/-- The standard dot-product orthogonal complement (dual code) `{y | ∀ x ∈ V, x ⬝ᵥ y = 0}` of a
submodule `V` of `ι → R`. -/
def orthogonal {R ι : Type*} [CommRing R] [Fintype ι] (V : Submodule R (ι → R)) :
    Submodule R (ι → R) where
  carrier := {y | ∀ x ∈ V, x ⬝ᵥ y = 0}
  zero_mem' x _ := dotProduct_zero x
  add_mem' {y₁ y₂} hy₁ hy₂ x hx := by rw [dotProduct_add, hy₁ x hx, hy₂ x hx, add_zero]
  smul_mem' c y hy x hx := by rw [dotProduct_smul, hy x hx, smul_zero]

@[simp]
theorem mem_orthogonal {R ι : Type*} [CommRing R] [Fintype ι] {V : Submodule R (ι → R)}
    {y : ι → R} :
    y ∈ orthogonal V ↔ ∀ x ∈ V, x ⬝ᵥ y = 0 :=
  Iff.rfl

theorem le_orthogonal_orthogonal {R ι : Type*} [CommRing R] [Fintype ι]
    (V : Submodule R (ι → R)) :
    V ≤ orthogonal (orthogonal V) := fun x hx y hy => by
  rw [dotProduct_comm]
  exact hy x hx

/-- Over any commutative ring, the orthogonal complement of the row space `range Hᵀ.mulVecLin` is
the kernel `ker H.mulVecLin`. -/
theorem orthogonal_range_transpose_mulVecLin {R κ ι : Type*} [CommRing R] [Fintype κ] [Fintype ι]
    (H : Matrix κ ι R) :
    orthogonal (LinearMap.range H.transpose.mulVecLin) = LinearMap.ker H.mulVecLin := by
  ext y
  simp only [mem_orthogonal, LinearMap.mem_range, mulVecLin_apply, forall_exists_index,
    forall_apply_eq_imp_iff, LinearMap.mem_ker]
  refine ⟨fun h => funext fun i => ?_, fun hy c => ?_⟩
  · classical
    change H i ⬝ᵥ y = 0
    simpa only [mulVec_transpose, single_vecMul, one_smul, Pi.zero_apply, row_def] using
      h (Pi.single i 1)
  · rw [mulVec_transpose, ← dotProduct_mulVec, hy, dotProduct_zero]

/-- Over a field `K`, `dim K (orthogonal W) + dim K W = |ι|`. -/
theorem finrank_orthogonal_add_finrank {K ι : Type*} [Field K] [Fintype ι]
    (W : Submodule K (ι → K)) :
    finrank K (orthogonal W) + finrank K W = Fintype.card ι := by
  let b := Module.finBasis K W
  let M : Matrix (Fin (finrank K W)) ι K := Matrix.of fun i j => (b i).val j
  have hker : orthogonal W = LinearMap.ker M.mulVecLin := by
    ext y
    simp only [mem_orthogonal, LinearMap.mem_ker, funext_iff, mulVecLin_apply, mulVec, M, of_apply,
      Pi.zero_apply]
    refine ⟨fun hy i => hy (b i).val (b i).property, fun hy x hx => ?_⟩
    have hrepr : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i).val := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using
        congrArg Subtype.val (b.sum_repr ⟨x, hx⟩).symm
    rw [hrepr, sum_dotProduct]
    exact Finset.sum_eq_zero fun i _ => by rw [smul_dotProduct, hy i, smul_zero]
  have hinj : Function.Injective M.transpose.mulVecLin :=
    (injective_iff_map_eq_zero M.transpose.mulVecLin).mpr fun c hc => by
      have hsum : ∑ i, c i • b i = 0 := Subtype.ext <| funext fun j => by
        have hj := congrFun hc j
        simp only [mulVecLin_apply, mulVec, dotProduct, transpose_apply, M, of_apply, Pi.zero_apply,
          Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul, mul_comm (c _)] at hj ⊢
        exact hj
      exact funext (Fintype.linearIndependent_iff.mp b.linearIndependent c hsum)
  have hrankT : M.transpose.rank = finrank K W := by
    have h := LinearMap.finrank_range_add_finrank_ker M.transpose.mulVecLin
    rwa [Matrix.finrank_range_mulVecLin, LinearMap.ker_eq_bot.mpr hinj, finrank_bot, add_zero,
      Module.finrank_fin_fun] at h
  have hnull := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Matrix.finrank_range_mulVecLin] at hnull
  rwa [← rank_transpose, hrankT, ← hker, Module.finrank_fintype_fun_eq_card, add_comm] at hnull

/-- Over a field `K`, the double orthogonal complement of a subspace `W` of `ι → K` is `W`. -/
@[simp]
theorem orthogonal_orthogonal {K ι : Type*} [Field K] [Fintype ι] (W : Submodule K (ι → K)) :
    orthogonal (orthogonal W) = W := by
  have h1 := finrank_orthogonal_add_finrank W
  have h2 := finrank_orthogonal_add_finrank (orthogonal W)
  exact (Submodule.eq_of_le_of_finrank_eq (le_orthogonal_orthogonal W) (by omega)).symm

/-- Over a field `K`, the orthogonal complement of `ker H.mulVecLin` is the row space
`range Hᵀ.mulVecLin`. -/
theorem orthogonal_ker_mulVecLin {K κ ι : Type*} [Field K] [Fintype κ] [Fintype ι]
    (H : Matrix κ ι K) :
    orthogonal (LinearMap.ker H.mulVecLin) = LinearMap.range H.transpose.mulVecLin := by
  rw [← orthogonal_range_transpose_mulVecLin, orthogonal_orthogonal]

/-- `submoduleZModIso` commutes with `orthogonal`. -/
theorem submoduleZModIso_orthogonal {ι : Type*} [Fintype ι] (V : Submodule Bool (ι → Bool)) :
    submoduleZModIso ι (orthogonal V) = orthogonal (submoduleZModIso ι V) := by
  ext y
  obtain ⟨w, rfl⟩ := (toZModSpace ι).surjective y
  simp only [toZModSpace_mem_submoduleZModIso, mem_orthogonal]
  refine ⟨fun hw z hz => ?_, fun hw x hx => ?_⟩
  · obtain ⟨x, rfl⟩ := (toZModSpace ι).surjective z
    rw [toZModSpace_dotProduct, hw x (toZModSpace_mem_submoduleZModIso.mp hz), map_zero]
  · exact bitEquiv.symm.injective <| by
      rw [← toZModSpace_dotProduct, map_zero]
      exact hw (toZModSpace ι x) (toZModSpace_mem_submoduleZModIso.mpr hx)

/-- Dual-code dimension identity over `Bool`: `dim Bool (orthogonal V) + dim Bool V = |ι|`. -/
theorem finrank_orthogonal_add_finrank_bool {ι : Type*} [Fintype ι]
    (V : Submodule Bool (ι → Bool)) :
    finrank Bool (orthogonal V) + finrank Bool V = Fintype.card ι := by
  rw [← finrank_submoduleZModIso, ← finrank_submoduleZModIso V, submoduleZModIso_orthogonal]
  exact finrank_orthogonal_add_finrank (submoduleZModIso ι V)

/-- Double-orthogonal involution over `Bool`: `orthogonal (orthogonal V) = V`. -/
@[simp]
theorem orthogonal_orthogonal_bool {ι : Type*} [Fintype ι] (V : Submodule Bool (ι → Bool)) :
    orthogonal (orthogonal V) = V :=
  (submoduleZModIso ι).injective <| by
    rw [submoduleZModIso_orthogonal, submoduleZModIso_orthogonal, orthogonal_orthogonal]

/-- Over `Bool`, the orthogonal complement of `ker H.mulVecLin` is the row space
`range Hᵀ.mulVecLin`. -/
theorem orthogonal_ker_mulVecLin_bool {κ ι : Type*} [Fintype κ] [Fintype ι] (H : Matrix κ ι Bool) :
    orthogonal (LinearMap.ker H.mulVecLin) = LinearMap.range H.transpose.mulVecLin :=
  (submoduleZModIso ι).injective <| by
    have hT : (H.map bitEquiv.symm).transpose = H.transpose.map bitEquiv.symm := rfl
    rw [submoduleZModIso_orthogonal, submoduleZModIso_ker, linearMapZModEquiv_mulVecLin,
      orthogonal_ker_mulVecLin, submoduleZModIso_range, linearMapZModEquiv_mulVecLin, hT]

end Orthogonal

end Cslib.BitString
