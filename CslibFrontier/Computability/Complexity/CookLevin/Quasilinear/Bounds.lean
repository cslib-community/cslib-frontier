/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Decode

/-!
# The variables of the quasilinear formula are below the fresh ones

The constants, the bits of the records, the arrays and the flags of the sorting networks of
`Cslib.Complexity.CookLevin.Quasilinear.Layout` are numbered below `Layout.AUX`, the first fresh
variable of the gadgets, as long as their parameters are in range.

## Main results

* `Cslib.Complexity.CookLevin.Quasilinear.Layout.vRec_lt_AUX`, `Layout.vFlag_lt_AUX`,
  `Layout.arrAt_lt_AUX`.
-/

public section

namespace Cslib.Complexity.CookLevin.Quasilinear

namespace Layout

variable (Λ : Layout)


/-- The bits of the records are below the fresh variables. -/
theorem vRec_lt_AUX {t f : ℕ} (ht : t < Λ.N) (hf : f < Λ.RB) : Λ.vRec t f < Λ.AUX := by
  have : t * Λ.RB + f < Λ.N * Λ.RB := Nat.mul_add_lt_mul_of_lt ht hf
  unfold vRec AUX inner
  omega

/-- The arrays of the sorting networks are below the fresh variables. -/
private theorem vArr_lt_AUX {j ℓ w b : ℕ} (hj : j < Λ.k) (hℓ : ℓ < Λ.L) (hw : w < Λ.N)
    (hb : b < Λ.P) :
    Λ.vArr j ℓ w b < Λ.AUX := by
  have h1 : ((j * Λ.L + ℓ) * Λ.N + w) * Λ.P + b < Λ.k * Λ.L * Λ.N * Λ.P :=
    Nat.mul_add_lt_mul_of_lt (Nat.mul_add_lt_mul_of_lt (Nat.mul_add_lt_mul_of_lt hj hℓ) hw) hb
  have h2 : Λ.k * Λ.L * Λ.N * Λ.P ≤ (Λ.k * Λ.L + 1) * Λ.N * (Λ.P + 1) := by
    apply Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) (by omega)
  unfold vArr AUX inner
  omega

/-- The flags of the sorting networks are below the fresh variables. -/
theorem vFlag_lt_AUX {j ℓ w : ℕ} (hj : j < Λ.k) (hℓ : ℓ < Λ.L) (hw : w < Λ.N) :
    Λ.vFlag j ℓ w < Λ.AUX := by
  have h1 : (j * Λ.L + ℓ) * Λ.N + w < Λ.k * Λ.L * Λ.N :=
    Nat.mul_add_lt_mul_of_lt (Nat.mul_add_lt_mul_of_lt hj hℓ) hw
  have h2 : Λ.k * Λ.L * Λ.N ≤ (Λ.k * Λ.L + 1) * Λ.N * (Λ.P + 1) := by
    rw [Nat.mul_assoc (Λ.k * Λ.L + 1)]
    calc Λ.k * Λ.L * Λ.N ≤ (Λ.k * Λ.L + 1) * Λ.N := Nat.mul_le_mul_right _ (by omega)
      _ = (Λ.k * Λ.L + 1) * (Λ.N * 1) := by rw [Nat.mul_one]
      _ ≤ (Λ.k * Λ.L + 1) * (Λ.N * (Λ.P + 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  unfold vFlag AUX inner
  omega

/-- The payloads before the first layer are below the fresh variables. -/
private theorem pay0_lt_AUX {j t b : ℕ} (hj : j < Λ.k) (ht : t < Λ.N) (hb : b < Λ.P) :
    Λ.pay0 j t b < Λ.AUX := by
  have hpos : Λ.offPos j + (Λ.W - 1) < Λ.RB := by
    have : Λ.W * j + Λ.W ≤ Λ.W * Λ.k := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
    unfold offPos RB
    have : 0 < Λ.W := by unfold W; omega
    rw [Nat.mul_comm Λ.k] at *
    omega
  have htape : Λ.offTape j + 7 < Λ.RB := by
    unfold offTape RB C
    have : 8 * j + 8 ≤ 8 * Λ.k := by omega
    omega
  have hAUX : 1 < Λ.AUX := by unfold AUX; omega
  unfold pay0
  split_ifs
  · unfold vTT; omega
  · unfold vFF; omega
  · exact Λ.vRec_lt_AUX ht (by unfold P at hb; omega)
  · exact Λ.vRec_lt_AUX ht (by omega)
  · exact Λ.vRec_lt_AUX ht (by unfold P at hb; omega)

/-- The arrays after `ℓ ≤ L` layers are below the fresh variables. -/
theorem arrAt_lt_AUX {j ℓ w b : ℕ} (hj : j < Λ.k) (hℓ : ℓ ≤ Λ.L) (hw : w < Λ.N)
    (hb : b < Λ.P) : Λ.arrAt j ℓ w b < Λ.AUX := by
  unfold arrAt
  split_ifs with h0
  · exact Λ.pay0_lt_AUX hj hw hb
  · exact Λ.vArr_lt_AUX hj (by omega) hw hb

end Layout

end Cslib.Complexity.CookLevin.Quasilinear
