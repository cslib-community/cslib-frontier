/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.PRG.Nisan.Bits
public import CslibFrontier.Probability.SaksZhou
public import CslibFrontier.Probability.SaksZhou.Walk
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Saks–Zhou iteration instantiated with Nisan's generator

Combines the sink-augmented walk realization of dyadic substochastic matrices
(`Cslib.Probability.SaksZhou.walkStep`, `dens_foldl_walkStep_eq`) with Nisan's good-hash-seeds
lemma (`Cslib.Crypto.PRG.Nisan.dens_hashSeeds_far_le`) to instantiate the Saks–Zhou randomized
rounding iteration (`Cslib.Probability.SaksZhou.dens_snapIter_far_le_of_two_le`) using one shared
hash-seed tuple `hs : Fin k → H` and `n₂` independent rounding shifts `z : Fin n₂ → Fin (2 ^ d)`
([Chattopadhyay and Liao, Appendix A.1][ChattopadhyayLiao2020];
[Hoza, Appendix A][Hoza2021]; [Nisan][Nisan1992]; [Saks and Zhou][SaksZhou1999], internal
numbering of the publisher copy not consulted).

For any substochastic matrix `A` whose entries are multiples of `1 / |X|` and any pairwise
independent hash family `h : H → X → X`, `nisanPow h k A hs` averages the `2 ^ k`-block run of
`walkStep A` driven by `Nisan.blocks h k x hs` over a uniform single block `x : X`. Since every
reference iterate of `snapIter` is dyadic substochastic at precision `d`
(`isDyadicSubstochastic_snapIter`), when `2 ^ d ∣ |X|` each iterate has entries in `ℤ / |X|` and
therefore admits an exact walk over `Option ι`.

Specializing to Boolean Toeplitz hashing (`Cslib.Probability.toeplitzHash`) on blocks of even
length `2 * m` gives `bitNisanPow` and the square-root-free bound `dens_snapIter_bitNisanPow_far_le`
over seeds of `k * (3 * (2 * m) - 1) + n₂ * d` bits.

## Main definitions

* `Cslib.Probability.SaksZhou.nisanPow`: approximate `(2 ^ k)`-th power computed by Nisan's
  generator on the sink-augmented walk of `A`.
* `Cslib.Probability.SaksZhou.NisanShiftSeed`: shared Toeplitz hash seeds plus `n₂` rounding shifts.
* `Cslib.Probability.SaksZhou.bitNisanPow`: `nisanPow` specialized to `toeplitzHash` on bit strings.

## Main results

* `Cslib.Probability.SaksZhou.dens_entryFarSet_nisanPow_le`: most hash seeds make `nisanPow h k A`
  entrywise `ε`-close to `A ^ (2 ^ k)`.
* `Cslib.Probability.SaksZhou.dens_snapIter_nisanPow_far_le`: Saks–Zhou iteration bound for
  `nisanPow`.
* `Cslib.Probability.SaksZhou.dens_snapIter_bitNisanPow_far_le`: specialization to `toeplitzHash` on
  `2 * m`-bit blocks.

## References

* [N. Nisan, *Pseudorandom generators for space-bounded computation*][Nisan1992]
* [M. Saks and S. Zhou, *BP_H SPACE(S) ⊆ DSPACE(S^{3/2})*][SaksZhou1999]: publisher copy not
  consulted.
* [E. Chattopadhyay and J.-J. Liao, *Optimal Error Pseudodistributions for Read-Once Branching
  Programs*][ChattopadhyayLiao2020], arXiv v4, Appendix A.1
* [W. M. Hoza, *Better Pseudodistributions and Derandomization for Space-Bounded
  Computation*][Hoza2021], Appendix A
-/

public section

namespace Cslib.Probability.SaksZhou

open Cslib.BitString Cslib.Crypto.PRG Finset

private theorem foldlIdx_const {α β : Type*} (f : α → β → α) (l : List β) (s : α) (t : ℕ) :
    l.foldlIdx (fun _ => f) s t = l.foldl f s := by
  induction l generalizing s t with
  | nil => rfl
  | cons x l ih => simp only [List.foldlIdx_cons, List.foldl_cons, ih]

/-- Approximate `(2 ^ k)`-th power of a matrix `A` computed by averaging Nisan's generator
`Cslib.Crypto.PRG.Nisan.blocks h k x hs` on `walkStep A` over a single uniform block `x : X`,
keeping the hash seeds `hs : Fin k → H` fixed. -/
noncomputable def nisanPow {H X ι : Type*} [Fintype X] [Fintype ι] [DecidableEq ι]
    (h : H → X → X) (k : ℕ) (A : Matrix ι ι ℝ) (hs : Fin k → H) : Matrix ι ι ℝ :=
  Matrix.of fun i j =>
    (dens {x : X | (List.ofFn (Nisan.blocks h k x hs)).foldl (walkStep A) (some i) = some j} : ℝ)

@[simp] theorem nisanPow_apply {H X ι : Type*} [Fintype X] [Fintype ι] [DecidableEq ι]
    (h : H → X → X) (k : ℕ) (A : Matrix ι ι ℝ) (hs : Fin k → H) (i j : ι) :
    nisanPow h k A hs i j =
      (dens {x : X |
        (List.ofFn (Nisan.blocks h k x hs)).foldl (walkStep A) (some i) = some j} : ℝ) := by
  rw [nisanPow, Matrix.of_apply]

/-- **Most hash seeds make `nisanPow` close to `A ^ (2 ^ k)`**: for a pairwise independent hash
family `h : H → X → X` and a substochastic matrix `A` with entries in `ℤ / |X|`, the density of
hash seeds `hs` for which some entry of `nisanPow h k A hs - A ^ (2 ^ k)` exceeds `ε` in
magnitude is at most `(|ι| + 1) * ((2 ^ k - 1) * (|ι| + 1) / √|X|) / ε`. -/
theorem dens_entryFarSet_nisanPow_le {H X ι : Type*} [Fintype H] [Fintype X] [DecidableEq X]
    [Nonempty X] [Fintype ι] [DecidableEq ι] {h : H → X → X} (hh : IsPairwiseIndependentHash h)
    (k : ℕ) {A : Matrix ι ι ℝ} (h0 : ∀ i j, 0 ≤ A i j) (h1 : ∀ i, ∑ j, A i j ≤ 1)
    (hA : ∀ i j, ∃ c : ℕ, A i j * Fintype.card X = c) {ε : ℝ} (hε : 0 < ε) :
    ((entryFarSet ε (nisanPow h k A) (A ^ 2 ^ k)).dens : ℝ) ≤
      (Fintype.card ι + 1) * ((2 ^ k - 1) * (Fintype.card ι + 1) / √(Fintype.card X)) / ε := by
  classical
  let δ : ℕ → Option ι → X → Option ι := fun _ => walkStep A
  let bad : Finset (Fin k → H) :=
    {hs : Fin k → H | ∃ s : Option ι, ε < ∑ s' : Option ι,
      |(dens {x : X | (List.ofFn (Nisan.blocks h k x hs)).foldlIdx δ s = s'} : ℝ) -
        dens {u : Fin (2 ^ k) → X | (List.ofFn u).foldlIdx δ s = s'}|}
  have hsub : entryFarSet ε (nisanPow h k A) (A ^ 2 ^ k) ⊆ bad := fun hs hhs => by
    obtain ⟨i, j, hij⟩ := mem_entryFarSet.1 hhs
    rw [nisanPow_apply, ← dens_foldl_walkStep_eq h0 h1 hA (2 ^ k) i j] at hij
    refine mem_filter.2 ⟨mem_univ _, some i, hij.trans_le ?_⟩
    refine (le_of_eq ?_).trans (single_le_sum (fun _ _ => abs_nonneg _) (mem_univ (some j)))
    simp only [δ, foldlIdx_const]
  calc ((entryFarSet ε (nisanPow h k A) (A ^ 2 ^ k)).dens : ℝ)
      ≤ (bad.dens : ℝ) := NNRat.cast_le.2 (dens_le_dens hsub)
    _ ≤ Fintype.card (Option ι) * ((2 ^ k - 1) * Fintype.card (Option ι) / √(Fintype.card X)) /
          ε := Nisan.dens_hashSeeds_far_le hh δ k hε
    _ = (Fintype.card ι + 1) * ((2 ^ k - 1) * (Fintype.card ι + 1) / √(Fintype.card X)) /
          ε := by rw [Fintype.card_option, Nat.cast_add, Nat.cast_one]

/-- If `A` is dyadic substochastic at precision `d` and `2 ^ d ∣ |X|`, then every entry `A i j`
is a nonnegative integer multiple of `1 / |X|`. -/
private theorem exists_mul_card_eq_of_isDyadicSubstochastic {X ι : Type*} [Fintype X] [Fintype ι]
    {d : ℕ} {A : Matrix ι ι ℝ} (hA : IsDyadicSubstochastic d A) (hdiv : 2 ^ d ∣ Fintype.card X)
    (i j : ι) : ∃ c : ℕ, A i j * Fintype.card X = c := by
  obtain ⟨k, hk⟩ := hA.dyadic i j
  obtain ⟨q, hq⟩ := hdiv
  refine ⟨k * q, ?_⟩
  have h2 : (2 : ℝ) ^ d ≠ 0 := by positivity
  rw [hk, hq, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]; field_simp

/-- **Saks–Zhou iteration with Nisan's generator**: for a substochastic matrix `M` over `ι` with
entries in `ℤ / |X|`, `2 ^ d ∣ |X|`, and `1 ≤ k`, when `(|ι| + 1) * ((2 ^ k - 1) * (|ι| + 1) /
√|X|) ≤ ε ^ 2`, all but an `n₂ * (ε + |ι| ^ 2 * (2 ^ d * ε + 2 ^ (-d)))` fraction of pairs
`(hs, z)` satisfy `‖snapIter d (nisanPow h k · hs) M n₂ z - M ^ (2 ^ (k * n₂))‖_∞ ≤
2 ^ (k * n₂) * |ι| * 2 ^ (1 - d)`. -/
theorem dens_snapIter_nisanPow_far_le {H X ι : Type*} [Fintype H] [Fintype X] [DecidableEq X]
    [Nonempty X] [Fintype ι] [DecidableEq ι] {h : H → X → X} (hh : IsPairwiseIndependentHash h)
    (d k n₂ : ℕ) (hk : 1 ≤ k) (hdiv : 2 ^ d ∣ Fintype.card X) {M : Matrix ι ι ℝ} {ε : ℝ}
    (h0 : ∀ i j, 0 ≤ M i j) (h1 : ∀ i, ∑ j, M i j ≤ 1)
    (hM : ∀ i j, ∃ c : ℕ, M i j * Fintype.card X = c) (hε : 0 < ε)
    (herr : (Fintype.card ι + 1) * ((2 ^ k - 1) * (Fintype.card ι + 1) / √(Fintype.card X)) ≤
      ε ^ 2) :
    ((rowFarSet ((2 : ℝ) ^ (k * n₂) * (Fintype.card ι * (2 / 2 ^ d)))
        (fun p : (Fin k → H) × (Fin n₂ → Fin (2 ^ d)) =>
          snapIter d (fun A => nisanPow h k A p.1) M n₂ p.2)
        (M ^ 2 ^ (k * n₂))).dens : ℝ) ≤
      n₂ * (ε + Fintype.card ι ^ 2 * (2 ^ d * ε + (2 ^ d)⁻¹)) := by
  have hn₁ : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  have hpow (A : Matrix ι ι ℝ) (hA : A = M ∨ IsDyadicSubstochastic d A) :
      ((entryFarSet ε (nisanPow h k A) (A ^ 2 ^ k)).dens : ℝ) ≤ ε := by
    rcases hA with rfl | hdy
    · exact (dens_entryFarSet_nisanPow_le hh k h0 h1 hM hε).trans
        ((div_le_iff₀ hε).2 (by simpa only [sq] using herr))
    · exact (dens_entryFarSet_nisanPow_le hh k hdy.nonneg hdy.sum_le_one
        (exists_mul_card_eq_of_isDyadicSubstochastic hdy hdiv) hε).trans
        ((div_le_iff₀ hε).2 (by simpa only [sq] using herr))
  simpa only [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul] using
    dens_snapIter_far_le_of_two_le d n₂ hn₁ (nisanPow h k) h0 h1 hε.le hpow

/-! ### Specialization to Boolean Toeplitz hashing -/

/-- A single-level hash seed for `Cslib.Probability.toeplitzHash` on `b`-bit blocks: a `b × b`
Boolean Toeplitz matrix encoded in `2 b - 1` bits together with a `b`-bit shift vector. -/
abbrev ToeplitzSeed (b : ℕ) : Type := (Fin (b + b - 1) → Bool) × BitString b

/-- Combined randomness for `n₂` Saks–Zhou rounds using `k`-level Toeplitz-Nisan powering on
`b`-bit blocks and `d`-bit rounding shifts: `k * (3 * b - 1) + n₂ * d` bits total. -/
abbrev NisanShiftSeed (b k n₂ d : ℕ) : Type := (Fin k → ToeplitzSeed b) × (Fin n₂ → Fin (2 ^ d))

/-- Total cardinality of `NisanShiftSeed b k n₂ d` is `2 ^ (k * (3 * b - 1) + n₂ * d)`. -/
theorem card_nisanShiftSeed (b k n₂ d : ℕ) :
    Fintype.card (NisanShiftSeed b k n₂ d) = 2 ^ (k * (3 * b - 1) + n₂ * d) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    ← pow_mul, ← pow_add]
  rw [show b + b - 1 + b = 3 * b - 1 by omega, Nat.mul_comm (3 * b - 1) k, Nat.mul_comm d n₂]

/-- `nisanPow` specialized to `Cslib.Probability.toeplitzHash` on `b`-bit blocks. -/
noncomputable def bitNisanPow {ι : Type*} [Fintype ι] [DecidableEq ι] (b k : ℕ)
    (A : Matrix ι ι ℝ) (hs : Fin k → ToeplitzSeed b) : Matrix ι ι ℝ :=
  nisanPow Cslib.Probability.toeplitzHash k A hs

@[simp] theorem bitNisanPow_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (b k : ℕ)
    (A : Matrix ι ι ℝ) (hs : Fin k → ToeplitzSeed b) (i j : ι) :
    bitNisanPow b k A hs i j =
      (dens {x : BitString b | (List.ofFn
        (Nisan.blocks Cslib.Probability.toeplitzHash k x hs)).foldl (walkStep A) (some i) =
          some j} : ℝ) :=
  nisanPow_apply Cslib.Probability.toeplitzHash k A hs i j

/-- A rounded entry of Nisan powering can be computed from the number of starting blocks whose
walk ends at the requested column, using natural arithmetic for the final rounding. -/
theorem snapMatrix_bitNisanPow_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (b k d : ℕ)
    (A : Matrix ι ι ℝ) (hs : Fin k → ToeplitzSeed b) (y : Fin (2 ^ d)) (i j : ι) :
    snapMatrix d (bitNisanPow b k A hs) y i j =
      (snapCount (2 ^ d) #{x : BitString b | (List.ofFn
        (Nisan.blocks Cslib.Probability.toeplitzHash k x hs)).foldl (walkStep A) (some i) =
          some j} (2 ^ b) y : ℝ) / 2 ^ d := by
  rw [snapMatrix_apply, bitNisanPow_apply, Finset.dens, NNRat.cast_div, NNRat.cast_natCast,
    NNRat.cast_natCast]
  simp only [BitString, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  exact snap_frequency _ _ _ (Nat.two_pow_pos _) _

/-- **Saks–Zhou iteration with Boolean Toeplitz Nisan powering**: on blocks of `2 * m` bits with
`d ≤ 2 * m` and `1 ≤ k`, if `(|ι| + 1) * ((2 ^ k - 1) * (|ι| + 1) / 2 ^ m) ≤ ε ^ 2`, all but an
`n₂ * (ε + |ι| ^ 2 * (2 ^ d * ε + 2 ^ (-d)))` fraction of `NisanShiftSeed (2 * m) k n₂ d` pairs
produce a matrix whose every row sums within `2 ^ (k * n₂) * |ι| * 2 ^ (1 - d)` of
`M ^ (2 ^ (k * n₂))`. -/
theorem dens_snapIter_bitNisanPow_far_le {ι : Type*} [Fintype ι] [DecidableEq ι] (d m k n₂ : ℕ)
    (hk : 1 ≤ k) (hdm : d ≤ 2 * m) {M : Matrix ι ι ℝ} {ε : ℝ}
    (h0 : ∀ i j, 0 ≤ M i j) (h1 : ∀ i, ∑ j, M i j ≤ 1)
    (hM : ∀ i j, ∃ c : ℕ, M i j * Fintype.card (BitString (2 * m)) = c) (hε : 0 < ε)
    (herr : (Fintype.card ι + 1 : ℝ) * ((2 ^ k - 1) * (Fintype.card ι + 1) / 2 ^ m) ≤ ε ^ 2) :
    ((rowFarSet ((2 : ℝ) ^ (k * n₂) * (Fintype.card ι * (2 / 2 ^ d)))
        (fun p : NisanShiftSeed (2 * m) k n₂ d =>
          snapIter d (fun A => bitNisanPow (2 * m) k A p.1) M n₂ p.2)
        (M ^ 2 ^ (k * n₂))).dens : ℝ) ≤
      n₂ * (ε + Fintype.card ι ^ 2 * (2 ^ d * ε + (2 ^ d)⁻¹)) := by
  have hcard : Fintype.card (BitString (2 * m)) = 2 ^ (2 * m) := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hsqrt : √(Fintype.card (BitString (2 * m)) : ℝ) = (2 : ℝ) ^ m := by
    rw [hcard, Nat.cast_pow, Nat.cast_ofNat, mul_comm, pow_mul]
    exact Real.sqrt_sq (by positivity)
  exact dens_snapIter_nisanPow_far_le isPairwiseIndependentHash_toeplitzHash_bool d k n₂ hk
    (hcard ▸ Nat.pow_dvd_pow 2 hdm) h0 h1 hM hε (by rwa [hsqrt])

end Cslib.Probability.SaksZhou
