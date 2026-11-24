/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flag.Act
public import CslibFrontier.Foundations.Geometry.CAT0.Basic

/-!
# Translations of maps of a group into a complete CAT(0) space

The action of a group by translation on the maps from the group into a finite `ℓ²` product
(`Flag.transAct`), an isometric action, from *VP ≠ VNP over every field* [AnthropicVPVNP2026],
module `Nc.Flag.Main`.

## Main definitions

* `Flag.transIso`, `Flag.transAct`.

## Main results

* `Flag.transAct_dist`.
-/

public section

open Finset Matrix

namespace Cslib.Circuits.Arithmetic.Separation.Flag

open Cslib.CAT0

/-! ### Maps of a group into a complete CAT(0) space -/

section Maps
variable {G : Type} [Group G] [Fintype G] {Y : Type} [MetricSpace Y]

/-- The translation of maps `z ↦ (k ↦ z (g⁻¹ k))`, an isometry of the `ℓ²` product. -/
@[expose] def transIso (G Y : Type) [Group G] [Fintype G] [MetricSpace Y] (g : G) :
    (PiLp 2 fun _ : G => Y) ≃ᵢ (PiLp 2 fun _ : G => Y) where
  toFun z := WithLp.toLp 2 fun k => z (g⁻¹ * k)
  invFun z := WithLp.toLp 2 fun k => z (g * k)
  left_inv z := by ext k; simp
  right_inv z := by ext k; simp
  isometry_toFun := Isometry.of_dist_eq fun z z' => by
    have h1 : dist (WithLp.toLp 2 fun k => z (g⁻¹ * k) : PiLp 2 fun _ : G => Y)
        (WithLp.toLp 2 fun k => z' (g⁻¹ * k)) ^ 2 = dist z z' ^ 2 := by
      rw [PiLp.dist_sq_eq_sum, PiLp.dist_sq_eq_sum]
      exact Equiv.sum_comp (Equiv.mulLeft g⁻¹) (fun k => dist (z k) (z' k) ^ 2)
    exact (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).1 h1

/-- The action of `G` on maps by translation. -/
@[expose] def transAct (G Y : Type) [Group G] [Fintype G] [MetricSpace Y] :
    IsoAct G (PiLp 2 fun _ : G => Y) where
  toFun := transIso G Y
  map_one' := by ext z k; simp [transIso]
  map_mul' g h := by ext z k; simp [transIso, IsometryEquiv.mul_apply, mul_assoc]

theorem transAct_dist (z : PiLp 2 fun _ : G => Y) (g : G) :
    dist z (transAct G Y g z) ^ 2 = ∑ k, dist (z (g * k)) (z k) ^ 2 := by
  rw [PiLp.dist_sq_eq_sum, ← Equiv.sum_comp (Equiv.mulLeft g)]
  refine sum_congr rfl fun k _ => ?_
  change dist (z (g * k)) (z (g⁻¹ * (g * k))) ^ 2 = _
  rw [inv_mul_cancel_left]

end Maps

end Cslib.Circuits.Arithmetic.Separation.Flag
