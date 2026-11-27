/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ModGates
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Modular gates at coprime factors

The gate `modGate` outputs true when the Hamming weight is not divisible by the
modulus. For a product of pairwise coprime moduli, this gives a disjunction of
the factor gates, including for an empty family.

## Main results

* `Cslib.Circuits.Boolean.modGate_coprime_factors` gives the disjunction for two factors.
* `Cslib.Circuits.Boolean.modGate_prod_eq_true_iff` handles a finite pairwise coprime family.
-/

public section

namespace Cslib.Circuits.Boolean

open scoped BigOperators

/-- A product-modulus gate is an OR of both factor tests when the factors are coprime. -/
theorem modGate_coprime_factors {a b : ℕ} (h : a.Coprime b) {m : ℕ} (x : Fin m → Bool) :
    modGate (a * b) m x = (modGate a m x || modGate b m x) := by
  let w := (Finset.univ.filter fun i => x i = true).card
  have dvd : a * b ∣ w ↔ a ∣ w ∧ b ∣ w :=
    ⟨fun hw => ⟨(dvd_mul_right a b).trans hw, (dvd_mul_left b a).trans hw⟩,
      fun hw => h.mul_dvd_of_dvd_of_dvd hw.1 hw.2⟩
  rw [Bool.eq_iff_iff]
  change decide (w % (a * b) ≠ 0) = true ↔
    (decide (w % a ≠ 0) || decide (w % b ≠ 0)) = true
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  have hd (q : ℕ) : w % q ≠ 0 ↔ ¬ q ∣ w := not_congr Nat.dvd_iff_mod_eq_zero.symm
  rw [hd (a * b), hd a, hd b, dvd, not_and_or]

/-- The product gate is true precisely when at least one factor gate is true. -/
theorem modGate_prod_eq_true_iff {ι : Type*} (s : Finset ι) (q : ι → ℕ)
    (hq : Set.Pairwise (↑s : Set ι) (fun i j => (q i).Coprime (q j)))
    {m : ℕ} (x : Fin m → Bool) :
    modGate (∏ i ∈ s, q i) m x = true ↔ ∃ i ∈ s, modGate (q i) m x = true := by
  let w := (Finset.univ.filter fun i => x i = true).card
  have dvd : (∏ i ∈ s, q i) ∣ w ↔ ∀ i ∈ s, q i ∣ w :=
    ⟨fun h i hi => (Finset.dvd_prod_of_mem q hi).trans h,
      fun h => Finset.prod_dvd_of_isRelPrime (t := s)
        (fun _ hi _ hj hij => Nat.coprime_iff_isRelPrime.mp (hq hi hj hij)) h⟩
  simp only [modGate, decide_eq_true_eq]
  change w % (∏ i ∈ s, q i) ≠ 0 ↔ ∃ i ∈ s, w % q i ≠ 0
  simp only [ne_eq, ← Nat.dvd_iff_mod_eq_zero, dvd, not_forall, exists_prop]

end Cslib.Circuits.Boolean
