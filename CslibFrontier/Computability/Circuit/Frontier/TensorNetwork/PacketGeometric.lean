/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.PacketEvaluator
import Mathlib.Algebra.Ring.GeomSum

/-!
# Finite geometric expansions of packet inverses

An element `x = 1 + 2 w` of `(ℤ / 2 ^ p)[U] / (f)` has inverse
`∑ j < p, (1 - x) ^ j`: the omitted remainder `(1 - x) ^ p` vanishes. This identifies the
existing coefficient-list inverse with a finite sum of powers, including precision zero.

The kernel denominator is of this form for every grid length. The cross-ratio denominator is
of this form when `i ≤ a` and `2 ^ (i + 1)` does not divide `t - d₀`, the hypotheses already used
by its correctness theorem. These algebraic expansions express the two packet inversions using
sums and products; the statements concern their ring values and make no running-time claim.

## Main results

* `Cslib.Circuits.Frontier.NativePacket.val_inv_eq_sum_pow`: geometric expansion of an element
  equal to one modulo two.
* `Cslib.Circuits.Frontier.NativePacket.val_kernelUnitList_eq_sum_pow`: expansion for the
  kernel's odd denominator.
* `Cslib.Circuits.Frontier.NativePacket.val_crossRatioList_eq_sum_pow`: expansion for a
  cross ratio under its valuation hypotheses.

The reduction is original library mathematics, using the finite geometric-sum identity.
-/

public section

namespace Cslib.Circuits.Frontier.NativePacket

open Finset GaloisRingArith

variable {p : ℕ} {fl : List ℕ}

/-- Inverse of an element equal to one modulo two, as a sum of `p` powers. No positivity or
irreducibility assumption is needed: at precision zero both sides are zero in the zero ring. -/
theorem val_inv_eq_sum_pow (c : List ℕ) {w : Ring p fl}
    (h : val p fl c = 1 + 2 * w) :
    val p fl (inv p fl c) = ∑ j ∈ range p, (1 - val p fl c) ^ j := by
  have hn : (1 - val p fl c) ^ p = 0 := by
    rw [h, show 1 - (1 + 2 * w) = 2 * (-w) by ring, mul_pow, two_pow_eq_zero, zero_mul]
  apply inv_unique (val_mul_inv_of_eq c h)
  simpa only [sub_sub_cancel, hn, sub_zero] using mul_neg_geom_sum (1 - val p fl c) p

/-- The kernel unit is a finite geometric sum for every grid length, including an empty grid. -/
theorem val_kernelUnitList_eq_sum_pow (L : ℕ) :
    val p fl (kernelUnitList p fl L) =
      ∑ j ∈ range p, (1 - val p fl (kernelUnitDen p fl L)) ^ j := by
  obtain ⟨w, hw⟩ := exists_val_kernelUnitDen_eq (p := p) (fl := fl) L
  exact val_inv_eq_sum_pow _ hw

/-- A cross ratio is a scalar times a finite geometric sum whenever its denominator has odd
constant term and positive power of two on the variable term. -/
theorem val_crossRatioList_eq_sum_pow {a i : ℕ} (hia : i ≤ a) {t d₀ : ℤ}
    (hcross : ¬ (2 : ℤ) ^ (i + 1) ∣ t - d₀) (ζ : List ℕ) :
    val p fl (crossRatioList p fl a i t d₀ ζ) =
      (2 : Ring p fl) ^ (i + 1 - twoVal (t - d₀)) *
        ∑ j ∈ range p,
          (1 - val p fl (linFactor p fl ((t - d₀) / 2 ^ twoVal (t - d₀))
            (a + 1 - twoVal (t - d₀)) ζ)) ^ j := by
  have hv := padicValInt_le_of_not_dvd hcross
  have hn : t - d₀ ≠ 0 := by rintro h; exact hcross (h ▸ dvd_zero _)
  obtain ⟨w, hw⟩ := exists_val_linFactor_eq (p := p) (fl := fl) (odd_ediv_two_pow hn)
    (show 1 ≤ a + 1 - padicValInt 2 (t - d₀) by omega) ζ
  simp only [crossRatioList, twoVal_eq, val_mul, val_intConst, Int.cast_pow, Int.cast_ofNat]
  rw [val_inv_eq_sum_pow _ hw]

end Cslib.Circuits.Frontier.NativePacket
