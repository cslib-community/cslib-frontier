/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Geometry.CAT0.Toolkit
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flag.Len

/-!
# Finite groups of isometries of complete CAT(0) spaces: projections to fixed points

`Flag.IsoAct G Z`: an action of `G` on `Z` by isometries, as a homomorphism `G →* (Z ≃ᵢ Z)`. For a
finite group acting on a
complete CAT(0) space, the barycenter of an orbit (`Flag.IsoAct.P`, from
`Cslib.CAT0.exists_isBarycenter`) is a fixed point (`Flag.IsoAct.P_fix`), and it commutes with every
surjective isometry of `Z` that commutes with all group elements (`Flag.IsoAct.P_comm`).

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Flag.Act`.

## Main definitions

* `Flag.IsoAct G Z`: `G →* (Z ≃ᵢ Z)`; pullbacks are `MonoidHom.comp`.
* `Flag.IsoAct.len`, `Flag.IsoAct.Fix`, `Flag.IsoAct.P`.

## Main results

* `Flag.IsoAct.P_spec`, `Flag.IsoAct.P_fix`, `Flag.IsoAct.P_comm`.
-/

public section

open Finset

namespace Cslib.Circuits.Arithmetic.Separation.Flag

open Cslib.CAT0

/-- An action of `G` on `Z` by isometries: a homomorphism into the isometries of `Z`. -/
abbrev IsoAct (G Z : Type*) [Group G] [MetricSpace Z] := G →* (Z ≃ᵢ Z)

namespace IsoAct
variable {G H Z : Type*} [Group G] [Group H] [MetricSpace Z] (A : IsoAct G Z)

theorem act_mul (g h : G) (z : Z) : A (g * h) z = A g (A h z) := by
  rw [map_mul, IsometryEquiv.mul_apply]

theorem act_one (z : Z) : A 1 z = z := by
  rw [map_one, IsometryEquiv.coe_one, id]

/-- The displacement `g ↦ dist z (g • z)` of a point, a length function. -/
def len (z : Z) : Len G where
  toFun g := dist z (A g z)
  map_one' := by rw [act_one, dist_self]
  inv' g := by
    rw [← (A g).dist_eq, ← act_mul, mul_inv_cancel, act_one, dist_comm]
  mul_le' g h := by
    rw [act_mul]
    refine (dist_triangle z (A g z) _).trans ?_
    rw [(A g).dist_eq]

theorem len_apply (z : Z) (g : G) : A.len z g = dist z (A g z) := by rfl

/-- Fixed points. -/
@[expose] def Fix (z : Z) : Prop := ∀ g, A g z = z

section proj
variable [CompleteCAT0Space Z] [Fintype G]

theorem exists_proj (z : Z) : ∃ b, IsBarycenter (fun _ : G => (1 : ℝ)) (fun g => A g z) b := by
  have : Nonempty Z := ⟨z⟩
  exact exists_isBarycenter _ (fun _ => zero_le_one) _

/-- The projection to the fixed points: the barycentre of the orbit. -/
noncomputable def P (z : Z) : Z := Classical.choose (A.exists_proj z)

theorem P_spec (z : Z) : IsBarycenter (fun _ : G => (1 : ℝ)) (fun g => A g z) (A.P z) :=
  Classical.choose_spec (A.exists_proj z)

theorem card_pos' : (0 : ℝ) < ∑ _g : G, (1 : ℝ) := by
  rw [sum_const, card_univ, nsmul_eq_mul, mul_one]
  exact_mod_cast Fintype.card_pos

/-- A surjective isometry `f` that commutes with every group element commutes with the
projection. -/
theorem P_comm (f : Z → Z) (hf : Isometry f) (hs : Function.Surjective f)
    (hc : ∀ g z, f (A g z) = A g (f z)) (z : Z) : f (A.P z) = A.P (f z) := by
  have h1 := (A.P_spec z).map hf hs
  simp only [hc] at h1
  exact h1.unique card_pos' (A.P_spec (f z))

theorem P_fix (z : Z) : A.Fix (A.P z) := by
  intro g
  have h1 := (A.P_spec z).map (A g).isometry (A g).surjective
  have h2 := (A.P_spec z).comp_equiv (Equiv.mulLeft g)
  refine h1.unique card_pos' ?_
  have e : (fun i => A g (A i z)) = (fun g => A g z) ∘ Equiv.mulLeft g :=
    funext fun k => (A.act_mul g k z).symm
  rw [e]
  exact h2

end proj
end IsoAct

/-- The arithmetic at the end of the proof of Lemma lem:angle (a quadrangle with two right angles).
-/
theorem angle_num {r r' α β Q A c : ℝ} (hr : 0 < r) (hr' : 0 < r') (hα : 0 < α) (hβ : 0 < β)
    (hA1 : r ^ 2 + α ^ 2 ≤ A) (hA2 : r' ^ 2 + β ^ 2 ≤ A)
    (hQ : α ^ 2 + β ^ 2 - 2 * c * (α * β) ≤ Q)
    (hbox : ∀ s t : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 →
      t * (1 - t) * A + s * (1 - s) * Q ≤ (1 - t) * (1 - s) * r ^ 2 + (1 - t) * s * r' ^ 2 +
        t * (1 - s) * α ^ 2 + t * s * β ^ 2) :
    Q ≤ r ^ 2 + r' ^ 2 + 2 * c * (r * r') := by
  set T := r * α + r' * β with hT
  set S := r * β + r' * α with hS
  set N := r * r' + α * β with hN
  have hT0 : 0 < T := by positivity
  have hN0 : 0 < N := by positivity
  set s := r * α / T with hs
  set t := r * r' / N with ht
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := (div_le_one hT0).mpr (by rw [hT]; linarith [mul_nonneg hr'.le hβ.le])
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := (div_le_one hN0).mpr (by rw [hN]; linarith [mul_nonneg hα.le hβ.le])
  have hb := hbox s t hs0 hs1 ht0 ht1
  have hA : (1 - s) * (r ^ 2 + α ^ 2) + s * (r' ^ 2 + β ^ 2) ≤ A := by
    linarith [mul_le_mul_of_nonneg_left hA1 (sub_nonneg.mpr hs1),
      mul_le_mul_of_nonneg_left hA2 hs0]
  have hA' := mul_le_mul_of_nonneg_left hA (mul_nonneg ht0 (sub_nonneg.mpr ht1))
  have h1 : s * (1 - s) * Q ≤ (1 - t) ^ 2 * ((1 - s) * r ^ 2 + s * r' ^ 2) +
      t ^ 2 * ((1 - s) * α ^ 2 + s * β ^ 2) := by linarith
  have e1 : 1 - s = r' * β / T := by rw [hs, hT]; field_simp; ring
  have e2 : 1 - t = α * β / N := by rw [ht, hN]; field_simp; ring
  have e3 : (1 - s) * r ^ 2 + s * r' ^ 2 = r * r' * S / T := by
    rw [e1, hs, hS]; field_simp
  have e4 : (1 - s) * α ^ 2 + s * β ^ 2 = α * β * S / T := by
    rw [e1, hs, hS]; field_simp; ring
  have e5 : (1 - t) ^ 2 * (r * r' * S / T) + t ^ 2 * (α * β * S / T) =
      (r * r' * (α * β)) * (S / (T * N)) := by
    rw [e2, ht]; field_simp; rw [hN]; ring
  have e6 : s * (1 - s) = (r * r' * (α * β)) * (1 / T ^ 2) := by
    rw [e1, hs]; field_simp
  rw [e3, e4, e5, e6, mul_assoc] at h1
  have h2 := le_of_mul_le_mul_left h1 (by positivity)
  have h3 : Q * N ≤ T * S := by
    calc Q * N = T ^ 2 * N * (1 / T ^ 2 * Q) := by field_simp
      _ ≤ T ^ 2 * N * (S / (T * N)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = T * S := by field_simp
  have h4 : r * r' * (α ^ 2 + β ^ 2) ≤ r * r' * (Q + 2 * c * (α * β)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e9 : T * S = α * β * (r ^ 2 + r' ^ 2) + r * r' * (α ^ 2 + β ^ 2) := by rw [hT, hS]; ring
  rw [e9, hN] at h3
  exact le_of_mul_le_mul_left (a := α * β) (by linarith) (by positivity)

end Cslib.Circuits.Arithmetic.Separation.Flag
