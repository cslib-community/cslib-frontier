/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.CookLevin.Parsimonious

/-!
# A polynomial bound on the numbers of determined tableau variables

The Cook–Levin reduction numbers the variables of the tableau injectively through `Var.index`
(`CslibFrontier/Computability/Complexity/CookLevin/Reduction.lean`). Every variable that a
satisfying assignment determines from its certificate (`Determined`,
`CslibFrontier/Computability/Complexity/CookLevin/Parsimonious.lean`) has a number that is
polynomial in the input length, the certificate length and the number of steps, with the
polynomial depending on the number of work tapes and the state type only.

## Main results

* `Cslib.Complexity.CookLevin.exists_index_lt_of_determined`: the number of a determined variable
  is at most `c * (n + L + T + 1) ^ c` for a constant `c`.
-/

public section

namespace Cslib.Complexity.CookLevin

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Feature

variable {k : ℕ} {State : Type} [Fintype State]

/-- The numbers entering `featureIndex` of a feature, other than the constructor tag, are below
`A`. -/
private def Small (A : ℕ) : Feature k State → Prop
  | .state q => stateIndex q < A
  | .inPos j => j < A
  | .head i z => (i : ℕ) < A ∧ Equiv.intEquivNat z < A
  | .cell i z s => (i : ℕ) < A ∧ Equiv.intEquivNat z < A ∧ Encodable.encode s < A
  | .out _ => True
  | .read i s => (i : ℕ) < A ∧ Encodable.encode s < A
  | .inRead s => Encodable.encode s < A
  | .sit y => Fintype.equivFin (Situation k State) y < A

/-- The pairing of two numbers below `A ^ i` is below `A ^ j` when `2 * i ≤ j`. -/
private theorem pair_lt_pow {a b A i j : ℕ} (hA : 1 ≤ A) (ha : a < A ^ i) (hb : b < A ^ i)
    (hij : 2 * i ≤ j) : Nat.pair a b < A ^ j :=
  calc Nat.pair a b < (max a b + 1) ^ 2 := Nat.pair_lt_max_add_one_sq a b
    _ ≤ (A ^ i) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    _ = A ^ (2 * i) := by rw [← pow_mul, mul_comm]
    _ ≤ A ^ j := Nat.pow_le_pow_right hA hij

/-- A number below `A` is below `A ^ j` for `j ≥ 1`. -/
private theorem lt_pow_of_lt {a A j : ℕ} (ha : a < A) (hj : 1 ≤ j) : a < A ^ j :=
  ha.trans_le (Nat.le_self_pow (by omega) A)

/-- The number of a feature with small components is below `A ^ 8`. -/
private theorem featureIndex_lt {A : ℕ} (hA : 8 ≤ A) {φ : Feature k State} (h : Small A φ) :
    featureIndex φ < A ^ 8 := by
  have hA1 : 1 ≤ A := by omega
  have u : ∀ {a j : ℕ}, a < A → 1 ≤ j → a < A ^ j := fun ha hj => lt_pow_of_lt ha hj
  have p2 : ∀ {a b : ℕ}, a < A → b < A → Nat.pair a b < A ^ 2 := fun ha hb =>
    pair_lt_pow hA1 (i := 1) (by simpa using ha) (by simpa using hb) le_rfl
  cases φ with
  | state q =>
    exact pair_lt_pow hA1 (i := 1) (by simpa using (by omega : 0 < A)) (lt_pow_of_lt h le_rfl)
      (by norm_num)
  | inPos j =>
    exact pair_lt_pow hA1 (i := 1) (by simpa using (by omega : 1 < A)) (lt_pow_of_lt h le_rfl)
      (by norm_num)
  | head i z =>
    exact pair_lt_pow hA1 (i := 2) (u (by omega) (by norm_num)) (p2 h.1 h.2) (by norm_num)
  | cell i z s =>
    exact pair_lt_pow hA1 (i := 4) (u (by omega) (by norm_num))
      (pair_lt_pow hA1 (i := 2) (u h.1 (by norm_num)) (p2 h.2.1 h.2.2) (by norm_num))
      (by norm_num)
  | out o =>
    exact pair_lt_pow hA1 (i := 2) (u (by omega) (by norm_num))
      (u (lt_of_lt_of_le o.index_lt (by omega)) (by norm_num)) (by norm_num)
  | read i s =>
    exact pair_lt_pow hA1 (i := 2) (u (by omega) (by norm_num)) (p2 h.1 h.2) (by norm_num)
  | inRead s =>
    exact pair_lt_pow hA1 (i := 1) (by simpa using (by omega : 6 < A)) (lt_pow_of_lt h le_rfl)
      (by norm_num)
  | sit y =>
    exact pair_lt_pow hA1 (i := 1) (by simpa using (by omega : 7 < A)) (lt_pow_of_lt h le_rfl)
      (by norm_num)

/-- **The number of a determined variable is polynomial** in `n + L + T + 1`, with an exponent and
a coefficient depending only on the number of work tapes and the state type. -/
theorem exists_index_lt_of_determined (k : ℕ) (State : Type) [Fintype State] :
    ∃ c : ℕ, ∀ n L T : ℕ, ∀ v : Var k State, Determined n L T v →
      Var.index v < c * (n + L + T + 1) ^ c := by
  obtain ⟨K, hK⟩ : ∃ K, K = Fintype.card State + k + Fintype.card (Situation k State) + 8 :=
    ⟨_, rfl⟩
  refine ⟨K ^ 32 + 32, fun n L T v hv => ?_⟩
  obtain ⟨M, hM⟩ : ∃ M, M = n + L + T + 1 := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A, A = K * M := ⟨_, rfl⟩
  rw [← hM]
  have hM1 : 1 ≤ M := by omega
  have hMA : 8 * M ≤ A := by
    rw [hAdef]
    exact Nat.mul_le_mul_right M (by omega)
  have hKA : K ≤ A := by
    rw [hAdef]
    exact Nat.le_mul_of_pos_right K hM1
  have hA : 8 ≤ A := by omega
  have hA1 : 1 ≤ A := by omega
  have hsym : ∀ s : Option Bool, Encodable.encode s < A := by
    intro s
    have : Encodable.encode s < 3 := by
      rcases s with _ | _ | _ <;> decide
    omega
  have hint : ∀ z : ℤ, |z| ≤ T → Equiv.intEquivNat z < A := by
    intro z hz
    have : Equiv.intEquivNat z ≤ 2 * z.natAbs + 1 := by
      rcases z with m | m
      · have : Equiv.intEquivNat (Int.ofNat m) = 2 * m := rfl
        have h2 : (Int.ofNat m).natAbs = m := rfl
        omega
      · have : Equiv.intEquivNat (Int.negSucc m) = 2 * m + 1 := rfl
        have h2 : (Int.negSucc m).natAbs = m + 1 := rfl
        omega
    have hz' : z.natAbs ≤ T := by
      have := Int.abs_eq_natAbs z
      omega
    omega
  have hsit : ∀ y, Fintype.equivFin (Situation k State) y < A := fun y => by
    have := (Fintype.equivFin (Situation k State) y).2
    omega
  have hik : ∀ i : Fin k, (i : ℕ) < A := fun i => by
    have := i.2
    omega
  have hstate : ∀ q : Option State, stateIndex q < A := by
    intro q
    rcases q with _ | q
    · simp only [stateIndex, Option.elim_none]; omega
    · have := (Fintype.equivFin State q).2
      simp only [stateIndex, Option.elim_some]
      omega
  have hholds : ∀ {t : ℕ} {φ : Feature k State}, t < A → Small A φ →
      Var.index (.holds t φ) < A ^ 32 := fun {t φ} ht hφ => by
    change Nat.pair 0 (Nat.pair t (featureIndex φ)) < A ^ 32
    exact pair_lt_pow hA1 (i := 16) (lt_pow_of_lt (by omega) (by norm_num))
      (pair_lt_pow hA1 (i := 8) (lt_pow_of_lt ht (by norm_num)) (featureIndex_lt hA hφ)
        (by norm_num))
      (by norm_num)
  have key : Var.index v < A ^ 32 := by
    rcases hv with ⟨j, hj, rfl⟩ | ⟨t, ht, φ, hφ, rfl⟩ |
      ⟨t, ht, ⟨i, s, rfl⟩ | ⟨s, rfl⟩ | ⟨y, rfl⟩⟩
    · exact pair_lt_pow hA1 (i := 16) (lt_pow_of_lt (by omega) (by norm_num))
        (lt_pow_of_lt (by omega) (by norm_num)) (by norm_num)
    · refine hholds (by omega) ?_
      rcases mem_basic.1 hφ with ⟨q, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨i, z, hz, rfl⟩ |
        ⟨i, z, s, hz, rfl⟩ | ⟨o, rfl⟩
      · exact hstate q
      · change j < A
        omega
      · exact ⟨hik i, hint z hz⟩
      · exact ⟨hik i, hint z hz, hsym s⟩
      · trivial
    · exact hholds (by omega) ⟨hik i, hsym s⟩
    · exact hholds (by omega) (hsym s)
    · exact hholds (by omega) (hsit y)
  calc Var.index v < A ^ 32 := key
    _ = K ^ 32 * M ^ 32 := by rw [hAdef, mul_pow]
    _ ≤ (K ^ 32 + 32) * M ^ (K ^ 32 + 32) :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hM1 (by omega))

end Cslib.Complexity.CookLevin
