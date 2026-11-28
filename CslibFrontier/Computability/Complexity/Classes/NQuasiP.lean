/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Time
public import CslibFrontier.Computability.Complexity.Reduction

/-!
# Nondeterministic quasi-polynomial time

`Cslib.Complexity.NQuasiP enc` is the union of the classes
`Cslib.Complexity.NTIME enc (2 ^ (Nat.log 2 n + 1) ^ k)` over `k`: the problems decided by a
nondeterministic machine in time `2 ^ O((log n) ^ k)` for some `k`, on instances whose encoding
under `enc` has length `n` [MurrayWilliams2018]. It contains `NP`.

## Main definitions

* `Cslib.Complexity.NQuasiP`: nondeterministic quasi-polynomial time.

## Main results

* `Cslib.Complexity.NTIME_subset_NQuasiP`: each of the defining classes is within `NQuasiP`.
* `Cslib.Complexity.NP_subset_NQuasiP`, `Cslib.Complexity.P_subset_NQuasiP`: `P ⊆ NP ⊆ NQuasiP`.
* `Cslib.Complexity.pow_succ_le_mul_two_pow_log`: a polynomial is within quasi-polynomial time.

## References

* [C. D. Murray, R. R. Williams, *Circuit lower bounds for nondeterministic quasi-polytime: an
  easy witness lemma for NP and NQP*][MurrayWilliams2018]
-/

public section

namespace Cslib.Complexity

open Filter

variable {α : Type*} {enc : α ↪ List Bool} {A : Set α}

/-- The problems decidable by a nondeterministic machine within time `O(2 ^ (log₂ n + 1) ^ k)`
for some `k`, on instances whose encoding under `enc` has length `n`
[MurrayWilliams2018]. Murray and Williams write it NQP; `Cslib.Complexity.NQP` is the quantum
class. -/
def NQuasiP (enc : α ↪ List Bool) : Set (Set α) :=
  ⋃ k, NTIME enc fun n => 2 ^ (Nat.log 2 n + 1) ^ k

/-- A problem is in `NQuasiP` when it is in `NTIME (2 ^ (log₂ n + 1) ^ k)` for some `k`. -/
theorem mem_NQuasiP_iff : A ∈ NQuasiP enc ↔ ∃ k, A ∈ NTIME enc fun n => 2 ^ (Nat.log 2 n + 1) ^ k :=
  Set.mem_iUnion

/-- Each class `NTIME (2 ^ (log₂ n + 1) ^ k)` is within `NQuasiP`. -/
theorem NTIME_subset_NQuasiP (k : ℕ) :
    (NTIME enc fun n => 2 ^ (Nat.log 2 n + 1) ^ k) ⊆ NQuasiP enc :=
  Set.subset_iUnion (fun k => NTIME enc fun n => 2 ^ (Nat.log 2 n + 1) ^ k) k

/-- A linear term in `L` is within `L ^ (d + 1)` up to the additive constant `d`. -/
private theorem mul_le_add_pow_succ (d : ℕ) {L : ℕ} (hL : 1 ≤ L) : d * L ≤ d + L ^ (d + 1) := by
  rcases Nat.eq_or_lt_of_le hL with rfl | hL2
  · simp
  · calc d * L ≤ 2 ^ d * L := Nat.mul_le_mul_right L Nat.lt_two_pow_self.le
      _ ≤ L ^ d * L := Nat.mul_le_mul_right L (Nat.pow_le_pow_left hL2 d)
      _ = L ^ (d + 1) := (pow_succ L d).symm
      _ ≤ d + L ^ (d + 1) := Nat.le_add_left _ _

/-- **A polynomial is within quasi-polynomial time.** For every `n`,
`(n + 1) ^ d ≤ 2 ^ d * 2 ^ ((log₂ n + 1) ^ (d + 1))`. -/
theorem pow_succ_le_mul_two_pow_log (d n : ℕ) :
    (n + 1) ^ d ≤ 2 ^ d * 2 ^ (Nat.log 2 n + 1) ^ (d + 1) := by
  have h1 : n + 1 ≤ 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two n
  calc (n + 1) ^ d ≤ (2 ^ (Nat.log 2 n + 1)) ^ d := Nat.pow_le_pow_left h1 d
    _ = 2 ^ (d * (Nat.log 2 n + 1)) := by rw [← pow_mul, mul_comm]
    _ ≤ 2 ^ (d + (Nat.log 2 n + 1) ^ (d + 1)) :=
        Nat.pow_le_pow_right (by norm_num) (mul_le_add_pow_succ d (Nat.le_add_left 1 _))
    _ = _ := pow_add _ _ _

/-- **Nondeterministic polynomial time is within nondeterministic quasi-polynomial time.** -/
theorem NP_subset_NQuasiP {α : Type} {enc : α ↪ List Bool} : NP enc ⊆ NQuasiP enc := fun _ hA =>
  let ⟨k, hk⟩ := mem_NP_iff_exists_mem_NTIME.mp hA
  mem_NQuasiP_iff.mpr ⟨k + 1, NTIME_mono_of_le_mul_add (C := 2 ^ k) (fun n =>
    ((Nat.pow_le_pow_left (Nat.le_succ n) k).trans (pow_succ_le_mul_two_pow_log k n)).trans
      (Nat.le_add_right _ _)) hk⟩

/-- **Polynomial time is within nondeterministic quasi-polynomial time.** -/
theorem P_subset_NQuasiP {α : Type} {enc : α ↪ List Bool} : P enc ⊆ NQuasiP enc :=
  P_subset_NP.trans NP_subset_NQuasiP

end Cslib.Complexity
