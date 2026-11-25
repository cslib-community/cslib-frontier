/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.FieldTheory.Finite.Coordinates
public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser
public import CslibFrontier.Foundations.Data.BitString.ZModTwo
public import Cslib.Foundations.Data.BitString
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
import CslibFrontier.Foundations.Data.BitString.ZModSpace
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Affine dispersers on bit strings

Ben-Sasson and Kopparty's function `traceSym` reads `r` elements of a field `F` with `2 ^ n`
elements. On bit strings it reads them from `r * n` of the `N` input bits: element `i` has
coordinate `x (pos (i, j))` on the vector `b j` of an `𝔽₂`-basis `b` of `F`
(`Cslib.AffineDisperser.readField`), and the output is the trace as a bit
(`Cslib.AffineDisperser.traceSymBits`).

Bits form the two-element field (Mathlib's `BooleanRing Bool`), identified with `ZMod 2` by
`Cslib.BitString.bitEquiv`, so the affine subspaces of the cube `BitString N` are Mathlib's
`AffineSubspace Bool (BitString N)`. Reading field elements is `𝔽₂`-linear and forgets only the
`N - r n` unread bits, so it maps an affine subspace of dimension `d` onto one of dimension at
least `d - (N - r n)`, and `Cslib.AffineDisperser.exists_traceSym_ne` transfers to bit strings
(`Cslib.AffineDisperser.exists_traceSymBits_ne`).

## Main definitions

* `Cslib.AffineDisperser.readField`: `r` field elements read from a bit string.
* `Cslib.AffineDisperser.traceSymBits`: `traceSym` on bit strings.

## Main results

* `Cslib.AffineDisperser.exists_traceSymBits_ne`: `traceSymBits` is nonconstant on every affine
  subspace of `BitString N` of dimension greater than
  `N - r n + r * max (r + 1) s + r * (r + 1) + n * t + n * r / t`.

## References

* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
-/

@[expose] public section

open Cslib.BinaryField

namespace Cslib.AffineDisperser

open BitString Module

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {ι : Type*} [Fintype ι] {r N : ℕ}

/-- The `r` elements of `F` read from the bits of `x`: element `i` has coordinate `x (pos (i, j))`
on the basis vector `b j`. -/
noncomputable def readField (b : Basis ι (ZMod 2) F) (pos : Fin r × ι → Fin N) (x : BitString N) :
    Fin r → F :=
  fun i => ofBits b fun j => x (pos (i, j))

/-- Ben-Sasson and Kopparty's function `traceSym μ r t` on bit strings: the trace, as a bit, at the
`r` field elements read from `x` by `readField b pos`. -/
noncomputable def traceSymBits (μ : F) (r t : ℕ) (b : Basis ι (ZMod 2) F)
    (pos : Fin r × ι → Fin N) (x : BitString N) : Bool :=
  bitEquiv (traceSym μ r t (readField b pos x))

/-- Reading field elements as an `𝔽₂`-linear map. -/
private noncomputable def readLinear (b : Basis ι (ZMod 2) F) (pos : Fin r × ι → Fin N) :
    (Fin N → ZMod 2) →ₗ[ZMod 2] Fin r → F :=
  LinearMap.pi fun i => (b.equivFun.symm : (ι → ZMod 2) →ₗ[ZMod 2] F) ∘ₗ
    LinearMap.funLeft (ZMod 2) (ZMod 2) fun j => pos (i, j)

private theorem readField_eq (b : Basis ι (ZMod 2) F) (pos : Fin r × ι → Fin N)
    (x : BitString N) : readField b pos x = readLinear b pos (toZModSpace (Fin N) x) := by
  funext i
  simp only [readField, ofBits, readLinear, LinearMap.pi_apply, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, Basis.equivFun_symm_apply]
  rfl

/-- Reading forgets at most `N - r n` dimensions. -/
private theorem finrank_ker_readLinear_le (b : Basis ι (ZMod 2) F) {pos : Fin r × ι → Fin N}
    (hpos : Function.Injective pos) :
    finrank (ZMod 2) (LinearMap.ker (readLinear b pos)) ≤ N - r * Fintype.card ι := by
  set ρ := LinearMap.funLeft (ZMod 2) (ZMod 2) pos
  have hker : LinearMap.ker (readLinear b pos) ≤ LinearMap.ker ρ := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    funext q
    have hi : (fun j => c (pos (q.1, j))) = 0 :=
      b.equivFun.symm.injective (by simpa [readLinear] using congrFun hc q.1)
    simpa [ρ] using congrFun hi q.2
  have hrange : LinearMap.range ρ = ⊤ :=
    LinearMap.range_eq_top.2 (LinearMap.funLeft_surjective_of_injective _ _ _ hpos)
  have h := LinearMap.finrank_range_add_finrank_ker ρ
  rw [hrange, finrank_top, Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card,
    Fintype.card_prod, Fintype.card_fin] at h
  have := Submodule.finrank_mono hker
  omega

/-- **Affine dispersers on bit strings** [BenSassonKopparty2012, Theorem 7.3]: if `F` has `2 ^ n`
elements, its proper subfields at most `2 ^ s`, `μ ≠ 0`, `0 < t` and the reading positions `pos`
are distinct, then `traceSymBits μ r t b pos` is nonconstant on every affine subspace `A` of
`BitString N` of dimension greater than
`N - r * n + (r * max (r + 1) s + r * (r + 1) + n * t + n * r / t)`. -/
theorem exists_traceSymBits_ne [Finite F] {n s t : ℕ} (hn : finrank (ZMod 2) F = n)
    (hs : ∀ K : Subfield F, K ≠ ⊤ → Nat.card K ≤ 2 ^ s) {μ : F} (hμ : μ ≠ 0) (ht : 0 < t)
    (b : Basis ι (ZMod 2) F) {pos : Fin r × ι → Fin N} (hpos : Function.Injective pos)
    (A : AffineSubspace Bool (BitString N))
    (hA : N - r * n + (r * max (r + 1) s + r * (r + 1) + n * t + n * r / t) <
      finrank Bool A.direction) :
    ∃ x ∈ A, ∃ y ∈ A, traceSymBits μ r t b pos x ≠ traceSymBits μ r t b pos y := by
  classical
  have hcard : Fintype.card ι = n := (finrank_eq_card_basis b).symm.trans hn
  have hAne : (A : Set (BitString N)).Nonempty := by
    rw [AffineSubspace.nonempty_iff_ne_bot]
    rintro rfl
    rw [AffineSubspace.direction_bot, finrank_bot] at hA
    exact Nat.not_lt_zero _ hA
  obtain ⟨p, hp⟩ := hAne
  set W := A.direction
  set E := toZModSpace (Fin N)
  set WZ := submoduleZModIso (Fin N) W
  have hWZ : finrank (ZMod 2) WZ = finrank Bool W := finrank_submoduleZModIso W
  set ψ := readLinear b pos
  set A' : AffineSubspace (ZMod 2) (Fin r → F) := AffineSubspace.mk' (ψ (E p)) (WZ.map ψ)
  have hdim : finrank Bool W - (N - r * n) ≤ finrank (ZMod 2) A'.direction := by
    rw [AffineSubspace.direction_mk']
    have h1 := LinearMap.finrank_range_add_finrank_ker (ψ.domRestrict WZ)
    rw [LinearMap.range_domRestrict] at h1
    have h2 : finrank (ZMod 2) (LinearMap.ker (ψ.domRestrict WZ)) ≤
        finrank (ZMod 2) (LinearMap.ker ψ) := by
      rw [LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq,
        Submodule.map_comap_subtype]
      exact Submodule.finrank_mono inf_le_right
    have h3 : finrank (ZMod 2) (LinearMap.ker ψ) ≤ N - r * n := by
      have := finrank_ker_readLinear_le b hpos
      rwa [hcard] at this
    omega
  obtain ⟨x', hx', y', hy', hne⟩ := exists_traceSym_ne hn hs hμ ht A' (by omega)
  -- the points of `A'` are read from points of `A`
  have hlift : ∀ z ∈ A', ∃ x ∈ A, readField b pos x = z := by
    intro z hz
    rw [AffineSubspace.mem_mk'] at hz
    obtain ⟨wZ, hwZ, hwz⟩ := Submodule.mem_map.mp hz
    refine ⟨E.symm wZ +ᵥ p,
      AffineSubspace.vadd_mem_of_mem_direction (mem_submoduleZModIso.mp hwZ) hp, ?_⟩
    rw [readField_eq, vadd_eq_add, map_add, E.apply_symm_apply, map_add, hwz, vsub_eq_sub,
      sub_add_cancel]
  obtain ⟨x, hx, rfl⟩ := hlift x' hx'
  obtain ⟨y, hy, rfl⟩ := hlift y' hy'
  exact ⟨x, hx, y, hy, fun h => hne (bitEquiv.injective h)⟩

end Cslib.AffineDisperser
