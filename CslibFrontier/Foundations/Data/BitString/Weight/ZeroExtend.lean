/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Foundations.Data.BitString.Weight

/-!
# Hamming weight under zero extension

`Cslib.BitString.weight_zeroExtend` shows that zero padding preserves the number of ones.
-/

public section

namespace Cslib.BitString

/-- Padding a bit string with false bits preserves its Hamming weight. -/
theorem weight_zeroExtend {n m : ℕ} (h : n ≤ m) (x : BitString n) :
    weight (zeroExtend (d' := m) x) = weight x := by
  rw [weight, weight]
  have hlt (i : Fin m) (hi : i ∈ Finset.univ.filter fun j => zeroExtend x j = true) :
      i.val < n := by
    by_contra hn
    simpa [zeroExtend, hn] using (Finset.mem_filter.mp hi).2
  refine Finset.card_bij (fun i hi => (⟨i.val, hlt i hi⟩ : Fin n))
    (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa only [zeroExtend, dite_eq_left (hlt i hi)] using (Finset.mem_filter.mp hi).2⟩)
    (fun _ _ _ _ hij => Fin.ext (Fin.mk.inj hij)) fun i hi =>
    ⟨⟨i.val, i.isLt.trans_le h⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa [zeroExtend, i.isLt] using (Finset.mem_filter.mp hi).2⟩, rfl⟩

end Cslib.BitString
