/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.FieldTheory.Finite.Coordinates
public import CslibFrontier.Init
public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryFieldTable
public import CslibFrontier.Computability.Complexity.AffineDisperser.Coordinates
public import CslibFrontier.Computability.Complexity.AffineDisperser.Li.Berlekamp
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Basic
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Bits
public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryField
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import CslibFrontier.Foundations.Combinatorics.AffineDisperser.AffineSubspace
import CslibFrontier.Foundations.Data.BitString.ZModTwo
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.FieldTheory.Finite.Subfield
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.NumberTheory.Bertrand
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.Tactic.Linarith

/-!
# Shoup's deterministic irreducible polynomials and an unconditional `O(N^(4/5))` affine disperser

For every input length `N`, this module chooses an odd prime `q = primeDeg N ∈ (M, 2M]` with
`M = (max 2 (fifthRoot N)) ^ 3 ≈ N ^ (3 / 5)`, constructs an explicit irreducible polynomial
`shoupIrreducibleBits q : List Bool` of degree `q` over `𝔽₂` deterministically using Shoup's
algorithm [Shoup1990], and evaluates Ben-Sasson and Kopparty's `traceSym 1 r t` over the single
prime-degree field `𝔽_{2 ^ q}` (`r = ⌊N / q⌋`, `t = max 1 (fifthRoot N)`).

Because `𝔽_{2 ^ q}` (`q` prime) has only `𝔽₂` (`2 ^ 1` elements) as a proper subfield, applying
`Cslib.AffineDisperser.exists_traceSymBits_ne` yields an unconditional explicit affine disperser
`primeDisperser N : BitString N → Bool` for dimension `primeThreshold N + 1 = O(N ^ (4 / 5))`.

This implements Milestone 1 of Issue #4323 (replacing `O(N / log N)` with `O(N ^ (4 / 5))` in `P`
via Shoup's deterministic single-prime irreducible construction). Reducing the dimension threshold
further from `O(N ^ (4 / 5))` to `O(log N)` [Li2023] remains open.

## Main definitions

* `Cslib.AffineDisperser.Li.fifthRoot`, `primeThresholdBound`, `primeDeg`: single-prime parameter
  selection (`q ≈ N ^ (3 / 5)`).
* `Cslib.AffineDisperser.Li.ordTwoMod`, `qAdicValTwoPowSubOne`, `shoupCyclicFactor`,
  `shoupBeta`, `shoupPowers`, `shoupMinPolyMatrix`, `shoupIrreducibleBits`: Shoup's deterministic
  irreducible polynomial algorithm over `𝔽₂`.
* `Cslib.AffineDisperser.Li.primeDisperserBits`, `primeDisperser`,
  `primeThreshold`: the single-prime affine disperser and its dimension threshold.

## Main results

* `Cslib.AffineDisperser.Li.irreducible_polyOfBits_shoupIrreducibleBits` and
  `Cslib.AffineDisperser.Li.natDegree_polyOfBits_shoupIrreducibleBits`: correctness of Shoup's
  irreducible polynomial of degree `q` for every odd prime `q`.
* `Cslib.AffineDisperser.Li.isAffineDisperser_primeDisperser`: `primeDisperser N` is an affine
  disperser for dimension `primeThreshold N + 1`.
* `Cslib.AffineDisperser.Li.eventually_primeThreshold_le` and
  `Cslib.AffineDisperser.Li.isBigO_primeThreshold`: `primeThreshold N = O(N ^ (4 / 5))`.

## References

* [V. Shoup, *New algorithms for finding irreducible polynomials over finite fields*][Shoup1990]
* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
* [X. Li, *Two source extractors for asymptotically optimal entropy, and (many) more*][Li2023]
-/

public section

open Cslib.BinaryField

namespace Cslib.AffineDisperser.Li

open Asymptotics BitString Filter Module Polynomial
open scoped Matrix

private theorem polyOfBits_false_cons (p : List Bool) :
    polyOfBits (false :: p) = X * polyOfBits p := by
  rw [polyOfBits_cons, show bitEquiv.symm false = 0 by rfl, map_zero, zero_add]

/-! ### Antitone counting helper and parameter selection -/

private theorem countP_range_true_lt {P : ℕ → Bool}
    (hanti : ∀ {a b}, a ≤ b → P b = true → P a = true) {n k : ℕ}
    (hk : k < (List.range n).countP P) : P k = true := by
  by_contra hnt
  suffices (List.range n).countP P ≤ k by omega
  clear hk
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, List.countP_singleton]
    by_cases hkn : k ≤ n
    · simp [Bool.eq_false_iff.mpr fun hP => hnt (hanti hkn hP), ih]
    · have : (List.range n).countP P ≤ n := by
        simpa only [List.length_range] using List.countP_le_length (p := P) (l := List.range n)
      split_ifs <;> omega

private theorem le_countP_range_of_forall_true (P : ℕ → Bool) {m n : ℕ} (hmn : m ≤ n)
    (htrue : ∀ j < m, P j = true) :
    m ≤ (List.range n).countP P := by
  induction hmn with
  | refl =>
    suffices (List.range m).countP P = m from this.ge
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range_succ, List.countP_append, List.countP_singleton,
        ite_eq_left (htrue m (Nat.lt_succ_self m)), ih fun j hj => htrue j (by omega)]
  | step _ ih =>
    rw [List.range_succ, List.countP_append]
    exact ih.trans (Nat.le_add_right _ _)

/-- Floor fifth root `⌊N ^ (1 / 5)⌋`. -/
@[expose] def fifthRoot (N : ℕ) : ℕ :=
  (List.range N).countP fun m => decide ((m + 1) ^ 5 ≤ N)

/-- `fifthRoot N ≤ N`. -/
theorem fifthRoot_le (N : ℕ) : fifthRoot N ≤ N := by
  simpa only [fifthRoot, List.length_range] using
    List.countP_le_length (p := fun m => decide ((m + 1) ^ 5 ≤ N)) (l := List.range N)

/-- `fifthRoot N` is the exact floor fifth root `⌊N ^ (1 / 5)⌋`. -/
theorem fifthRoot_spec (N : ℕ) :
    (fifthRoot N) ^ 5 ≤ N ∧ N < (fifthRoot N + 1) ^ 5 := by
  set P : ℕ → Bool := fun m => decide ((m + 1) ^ 5 ≤ N)
  refine ⟨?_, by_contra fun hle => ?_⟩
  · cases hr : fifthRoot N with
    | zero => simp
    | succ k =>
      exact of_decide_eq_true (countP_range_true_lt (P := P)
        (fun hab hb => decide_eq_true ((Nat.pow_le_pow_left (by omega) 5).trans
          (of_decide_eq_true hb)))
        (hr ▸ Nat.lt_succ_self k : k < fifthRoot N))
  · have hle' := Nat.not_lt.mp hle
    have hcount : fifthRoot N + 1 ≤ fifthRoot N := le_countP_range_of_forall_true P
      ((Nat.le_self_pow (by decide : 5 ≠ 0) _).trans hle') fun j hj =>
        decide_eq_true ((Nat.pow_le_pow_left hj 5).trans hle')
    omega

/-- Lower bound `M = (max 2 ⌊N ^ (1 / 5)⌋) ^ 3` on the field prime degree. -/
@[expose] def primeThresholdBound (N : ℕ) : ℕ :=
  (max 2 (fifthRoot N)) ^ 3

private theorem eight_le_primeThresholdBound (N : ℕ) : 8 ≤ primeThresholdBound N :=
  Nat.pow_le_pow_left (le_max_left 2 _) 3

/-- The least prime in `(M, 2M]` where `M = primeThresholdBound N`. -/
@[expose] def primeDeg (N : ℕ) : ℕ :=
  let M := primeThresholdBound N
  (((List.range M).map fun i => M + 1 + i).find? Nat.Prime).getD (2 * M)

/-- `primeDeg N` is a prime in `(primeThresholdBound N, 2 * primeThresholdBound N]`. -/
theorem primeDeg_spec (N : ℕ) :
    (primeDeg N).Prime ∧ primeThresholdBound N < primeDeg N ∧
      primeDeg N ≤ 2 * primeThresholdBound N := by
  set M := primeThresholdBound N
  have hM : 8 ≤ M := eight_le_primeThresholdBound N
  obtain ⟨q, hqp, hMq, hq2M⟩ := Nat.exists_prime_lt_and_le_two_mul M (by omega)
  let L := (List.range M).map fun i => M + 1 + i
  have hsome : (L.find? Nat.Prime).isSome = true :=
    List.find?_isSome.mpr ⟨q, List.mem_map.mpr
      ⟨q - (M + 1), List.mem_range.mpr (by omega), by omega⟩, by simp [hqp]⟩
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hp)
  have hi_lt := List.mem_range.mp hi
  have hdeg : primeDeg N = M + 1 + i := by
    change (L.find? Nat.Prime).getD (2 * M) = _
    rw [hp, Option.getD_some]
  rw [hdeg]
  exact ⟨by simpa using List.find?_some hp, by omega, by omega⟩

/-- `9 ≤ primeDeg N` for every `N`. -/
theorem nine_le_primeDeg (N : ℕ) : 9 ≤ primeDeg N := by
  have := eight_le_primeThresholdBound N; have := (primeDeg_spec N).2.1; omega

/-- `3 ≤ primeDeg N` for every `N`. -/
theorem three_le_primeDeg (N : ℕ) : 3 ≤ primeDeg N :=
  le_trans (by decide) (nine_le_primeDeg N)

/-! ### Multiplicative order and `q`-adic valuation of `2 ^ m - 1` -/

/-- Multiplicative order of `2` modulo `q` (returning `0` when `q ≤ 2` or `Even q`). -/
@[expose] def ordTwoMod (q : ℕ) : ℕ :=
  (((List.range (q - 1)).find? fun i => 2 ^ (i + 1) % q == 1).map (· + 1)).getD 0

/-- `q`-adic valuation of `2 ^ m - 1` capped at `q` (`max {j ≤ q | q ^ j ∣ 2 ^ m - 1}`). -/
@[expose] def qAdicValTwoPowSubOne (q m : ℕ) : ℕ :=
  (List.range q).countP fun j => decide (2 ^ m % q ^ (j + 1) == 1)

private theorem dvd_two_pow_sub_one_iff_modEq {m M : ℕ} (hM : 1 < M) :
    M ∣ 2 ^ m - 1 ↔ 2 ^ m % M = 1 := by
  rw [← Nat.modEq_iff_dvd' Nat.one_le_two_pow, Nat.ModEq, Nat.mod_eq_of_lt hM, eq_comm]

private theorem not_two_dvd_prime_pow {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) (t : ℕ) :
    ¬ 2 ∣ q ^ t := fun ht => by
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp (Nat.prime_two.dvd_of_dvd_pow ht)
  omega

private theorem zmod_unit_two_pow_eq_one_iff {M : ℕ} (hM : 1 < M)
    (hcop : Nat.Coprime 2 M) (j : ℕ) :
    (ZMod.unitOfCoprime 2 hcop) ^ j = 1 ↔ 2 ^ j % M = 1 := by
  have : NeZero M := ⟨by omega⟩
  rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, ZMod.coe_unitOfCoprime,
    ← Nat.cast_pow]
  conv_rhs => rw [← Nat.mod_eq_of_lt hM]
  rw [← Nat.ModEq, ← ZMod.natCast_eq_natCast_iff, Nat.cast_one]

private theorem natDegree_eq_orderOf_of_dvd_cyclotomic_prime_pow {q t : ℕ}
    (hq : q.Prime) (hq3 : 3 ≤ q) {p : (ZMod 2)[X]}
    (hdvd : p ∣ cyclotomic (q ^ t) (ZMod 2)) (hirr : Irreducible p) :
    p.natDegree = orderOf (ZMod.unitOfCoprime 2
      (Nat.prime_two.coprime_iff_not_dvd.mpr (not_two_dvd_prime_pow hq hq3 t))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop := Nat.prime_two.coprime_iff_not_dvd.mpr (not_two_dvd_prime_pow hq hq3 t)
  have hcard : Fintype.card (ZMod 2) = 2 ^ 1 := (ZMod.card 2).trans (pow_one 2).symm
  simpa only [pow_one] using
    Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible (K := ZMod 2) (f := 1) hcard hcop
      hdvd hirr

private theorem natDegree_dvd_of_dvd_cyclotomic_prime_pow {q t m : ℕ}
    (hq : q.Prime) (hq3 : 3 ≤ q) (ht : 1 ≤ t) {p : (ZMod 2)[X]}
    (hdvd : p ∣ cyclotomic (q ^ t) (ZMod 2)) (hirr : Irreducible p)
    (hm : q ^ t ∣ 2 ^ m - 1) : p.natDegree ∣ m := by
  have hqt : 1 < q ^ t := Nat.one_lt_pow (by omega) (by omega)
  rw [natDegree_eq_orderOf_of_dvd_cyclotomic_prime_pow hq hq3 hdvd hirr,
    orderOf_dvd_iff_pow_eq_one, zmod_unit_two_pow_eq_one_iff hqt]
  exact (dvd_two_pow_sub_one_iff_modEq hqt).mp hm

/-- `ordTwoMod q` equals the multiplicative order of `2` modulo an odd prime `q`. -/
theorem ordTwoMod_spec {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    let m := ordTwoMod q
    2 ≤ m ∧ m < q ∧ q ∣ 2 ^ m - 1 ∧ (∀ j, 0 < j → j < m → 2 ^ j % q ≠ 1) ∧
      m = orderOf (ZMod.unitOfCoprime 2 (Nat.prime_two.coprime_iff_not_dvd.mpr fun h2 => by
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h2
        omega)) := by
  have hcop : Nat.Coprime 2 q := Nat.prime_two.coprime_iff_not_dvd.mpr
    (by simpa only [pow_one] using not_two_dvd_prime_pow hq hq3 1)
  have : NeZero q := ⟨by omega⟩
  set u : (ZMod q)ˣ := ZMod.unitOfCoprime 2 hcop
  set d := orderOf u
  have hu_pow : ∀ j, 2 ^ j % q = 1 ↔ u ^ j = 1 :=
    fun j => (zmod_unit_two_pow_eq_one_iff (by omega) hcop j).symm
  have hd_pos : 0 < d := orderOf_pos u
  have hd_le : d ≤ q - 1 := Nat.le_of_dvd (by omega)
    (by simpa [ZMod.card_units_eq_totient, Nat.totient_prime hq] using orderOf_dvd_card (x := u))
  have hd_ge2 : 2 ≤ d := by_contra fun hlt => by
    have h1 := (hu_pow 1).mpr (show d = 1 by omega ▸ pow_orderOf_eq_one u)
    rw [pow_one, Nat.mod_eq_of_lt (by omega)] at h1; omega
  let L := List.range (q - 1)
  have hsome : (L.find? fun i => 2 ^ (i + 1) % q == 1).isSome = true :=
    List.find?_isSome.mpr ⟨d - 1, List.mem_range.mpr (by omega),
      beq_iff_eq.mpr (by rw [Nat.sub_add_cancel hd_pos, hu_pow]; exact pow_orderOf_eq_one u)⟩
  obtain ⟨r, hr_eq⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨hr_pred, k, hk_lt, hk_get, hk_min⟩ := List.find?_eq_some_iff_getElem.mp hr_eq
  simp only [L, List.length_range, List.getElem_range] at hk_lt hk_get
  subst hk_get
  have hmod : 2 ^ (k + 1) % q = 1 := beq_iff_eq.mp hr_pred
  have hnot_lt : ∀ j, 0 < j → j < k + 1 → 2 ^ j % q ≠ 1 := fun j hj0 hjl hm => by
    have := hk_min (j - 1) (by omega)
    simp [L, Nat.sub_add_cancel hj0, hm] at this
  have hkd : k + 1 = d := Nat.le_antisymm
    (by_contra fun hlt => hnot_lt d hd_pos (by omega) ((hu_pow d).mpr (pow_orderOf_eq_one u)))
    (Nat.le_of_dvd (by omega) (orderOf_dvd_iff_pow_eq_one.mpr ((hu_pow _).mp hmod)))
  have hm_eq : ordTwoMod q = k + 1 := by
    change ((L.find? _).map (· + 1)).getD 0 = k + 1; rw [hr_eq]; rfl
  rw [hm_eq]
  exact ⟨by omega, by omega, (dvd_two_pow_sub_one_iff_modEq (by omega)).mpr hmod, hnot_lt, hkd⟩

/-- `qAdicValTwoPowSubOne q m` gives the exact `q`-adic valuation `k ≥ 1` dividing `2 ^ m - 1`. -/
theorem qAdicValTwoPowSubOne_spec {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    let m := ordTwoMod q
    let k := qAdicValTwoPowSubOne q m
    1 ≤ k ∧ k < q ∧ q ^ k ∣ 2 ^ m - 1 ∧ ¬ q ^ (k + 1) ∣ 2 ^ m - 1 := by
  set m := ordTwoMod q; set k := qAdicValTwoPowSubOne q m
  obtain ⟨hm2, hmq, hq_dvd, -, -⟩ := ordTwoMod_spec hq hq3
  set P : ℕ → Bool := fun j => decide (2 ^ m % q ^ (j + 1) == 1)
  have hP_iff : ∀ j, P j = true ↔ q ^ (j + 1) ∣ 2 ^ m - 1 := fun j => by
    simp only [P, decide_eq_true_eq, beq_iff_eq]
    exact (dvd_two_pow_sub_one_iff_modEq (Nat.one_lt_pow (by omega) (by omega))).symm
  have hanti : ∀ {a b}, a ≤ b → P b = true → P a = true := fun hab hb =>
    (hP_iff _).mpr ((Nat.pow_dvd_pow q (by omega)).trans ((hP_iff _).mp hb))
  have hk_ge1 : 1 ≤ k := le_countP_range_of_forall_true P (by omega) fun j hj => by
    obtain rfl : j = 0 := by omega
    simpa only [zero_add, pow_one, hP_iff] using hq_dvd
  have hdvd_of_le : ∀ t, 1 ≤ t → t ≤ k → q ^ t ∣ 2 ^ m - 1 := fun t ht1 htk => by
    simpa only [Nat.sub_add_cancel ht1, hP_iff] using
      countP_range_true_lt hanti (show t - 1 < k by omega)
  have hk_lt : k < q := by_contra fun hge => by
    have h1 := Nat.le_of_dvd (Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) one_lt_two))
      (hdvd_of_le q (by omega) (by omega))
    have h2 : 2 ^ m - 1 < 2 ^ q :=
      (Nat.sub_lt Nat.one_le_two_pow one_pos).trans_le (Nat.pow_le_pow_right two_pos hmq.le)
    have h3 : 2 ^ q < q ^ q := Nat.pow_lt_pow_left (by omega) (by omega)
    omega
  refine ⟨hk_ge1, hk_lt, hdvd_of_le k hk_ge1 le_rfl, fun hdvd => ?_⟩
  have hcount : k + 1 ≤ k := le_countP_range_of_forall_true P hk_lt fun j hj =>
    (hP_iff j).mpr ((Nat.pow_dvd_pow q (by omega)).trans hdvd)
  omega

/-! ### Cyclotomic factor chain -/

/-- Step `k - 1` times from an irreducible factor of `Φ_q` to an irreducible factor of
`Φ_{q ^ max 1 k}` over `𝔽₂`. -/
@[expose] def shoupCyclicFactor (q k : ℕ) : List Bool :=
  (fun f => berlekampIrreducibleFactor (polyComposePow q f))^[k - 1]
    (berlekampIrreducibleFactor (List.replicate q true))

private theorem polyOfBits_replicate_true_eq_cyclotomic {q : ℕ} (hq : q.Prime) :
    polyOfBits (List.replicate q true) = cyclotomic q (ZMod 2) := by
  have : Fact q.Prime := ⟨hq⟩
  rw [cyclotomic_prime]; ext i
  rw [coeff_polyOfBits, finsetSum_coeff]; simp_rw [coeff_X_pow]
  by_cases hi : i < q
  · rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_replicate, Finset.sum_eq_single i]
    · simp [bitEquiv_symm_true]
    · intro j _ hj; simp [hj.symm]
    · exact fun hm => absurd (Finset.mem_range.mpr hi) hm
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    exact (Finset.sum_eq_zero fun j hj =>
      ite_eq_right (by have := Finset.mem_range.mp hj; omega)).symm

private theorem cyclotomic_prime_pow_comp_X_pow {q j : ℕ} (hq : q.Prime) :
    (cyclotomic (q ^ (j + 1)) (ZMod 2)).comp (X ^ q) = cyclotomic (q ^ (j + 2)) (ZMod 2) := by
  have : Fact q.Prime := ⟨hq⟩
  have hc : ∀ s, cyclotomic (q ^ (s + 1)) (ZMod 2) = (cyclotomic q (ZMod 2)).comp (X ^ (q ^ s)) :=
    fun s => by
      rw [cyclotomic_prime_pow_eq_geom_sum hq, cyclotomic_prime, sum_comp]
      exact Finset.sum_congr rfl fun _ _ => X_pow_comp.symm
  rw [hc j, hc (j + 1), comp_assoc, X_pow_comp, ← pow_mul, mul_comm q (q ^ j), ← pow_succ]

/-- Invariant for iterating Berlekamp factoring under `polyComposePow q` in Shoup's step. -/
theorem shoupCyclicFactor_iterate_spec {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) (s : ℕ) :
    let f := (fun g => berlekampIrreducibleFactor (polyComposePow q g))^[s]
      (berlekampIrreducibleFactor (List.replicate q true))
    polyTrim f = f ∧ polyOfBits f ∣ cyclotomic (q ^ (s + 1)) (ZMod 2) ∧
      Irreducible (polyOfBits f) ∧ 0 < (polyOfBits f).natDegree := by
  have hne2 : ∀ t, NeZero ((q ^ t : ℕ) : ZMod 2) := fun t =>
    ⟨fun h => not_two_dvd_prime_pow hq hq3 t ((CharP.cast_eq_zero_iff (ZMod 2) 2 _).mp h)⟩
  induction s with
  | zero =>
    have hrep := polyOfBits_replicate_true_eq_cyclotomic hq
    have : NeZero (q : ZMod 2) := by simpa only [pow_one] using hne2 1
    have hdeg : 0 < (polyOfBits (List.replicate q true)).natDegree := by
      rw [hrep, natDegree_cyclotomic, Nat.totient_prime hq]; omega
    obtain ⟨hdvd, hirr, hdeg'⟩ :=
      polyOfBits_berlekampIrreducibleFactor_dvd (hrep ▸ squarefree_cyclotomic q (ZMod 2)) hdeg
    exact ⟨polyTrim_berlekampIrreducibleFactor _,
      by simpa only [Function.iterate_zero, id_eq, zero_add, pow_one, hrep] using hdvd,
      hirr, hdeg'⟩
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨_, hdvd, _, hdeg⟩ := ih
    set g := (fun g => berlekampIrreducibleFactor (polyComposePow q g))^[s]
      (berlekampIrreducibleFactor (List.replicate q true))
    have hdvd_c : polyOfBits (polyComposePow q g) ∣ cyclotomic (q ^ (s + 2)) (ZMod 2) := by
      rcases hdvd with ⟨r, hr⟩
      rw [polyOfBits_polyComposePow (by omega), ← cyclotomic_prime_pow_comp_X_pow hq]
      exact ⟨r.comp (X ^ q), by rw [hr, mul_comp]⟩
    have := hne2 (s + 2)
    have hdeg_c : 0 < (polyOfBits (polyComposePow q g)).natDegree := by
      rw [polyOfBits_polyComposePow (by omega), natDegree_comp, natDegree_X_pow]
      exact Nat.mul_pos hdeg (by omega)
    obtain ⟨hdvd', hirr', hdeg'⟩ := polyOfBits_berlekampIrreducibleFactor_dvd
      (Squarefree.squarefree_of_dvd hdvd_c (squarefree_cyclotomic (q ^ (s + 2)) (ZMod 2))) hdeg_c
    exact ⟨polyTrim_berlekampIrreducibleFactor _, hdvd'.trans hdvd_c, hirr', hdeg'⟩

/-- `shoupCyclicFactor q k` produces an irreducible factor of degree `m = ordTwoMod q` dividing
`cyclotomic (q ^ k) (ZMod 2)`, so its root generates `𝔽_{2 ^ m}` and has multiplicative order
`q ^ k`. -/
theorem shoupCyclicFactor_spec {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    let m := ordTwoMod q
    let k := qAdicValTwoPowSubOne q m
    let f := shoupCyclicFactor q k
    polyTrim f = f ∧ polyOfBits f ∣ cyclotomic (q ^ k) (ZMod 2) ∧
      Irreducible (polyOfBits f) ∧ (polyOfBits f).natDegree = m ∧ f.length = m + 1 := by
  set m := ordTwoMod q; set k := qAdicValTwoPowSubOne q m
  obtain ⟨_, _, _, -, hm_ord⟩ := ordTwoMod_spec hq hq3
  obtain ⟨hk1, -, hk_dvd, -⟩ := qAdicValTwoPowSubOne_spec hq hq3
  obtain ⟨ht, hdvd, hirr, hdeg⟩ := shoupCyclicFactor_iterate_spec hq hq3 (k - 1)
  change polyTrim (shoupCyclicFactor q k) = _ at ht
  change 0 < (polyOfBits (shoupCyclicFactor q k)).natDegree at hdeg
  change polyOfBits (shoupCyclicFactor q k) ∣ cyclotomic (q ^ (k - 1 + 1)) (ZMod 2) at hdvd
  rw [Nat.sub_add_cancel hk1] at hdvd
  have hdeg_m : (polyOfBits (shoupCyclicFactor q k)).natDegree = m := by
    refine Nat.dvd_antisymm
      (natDegree_dvd_of_dvd_cyclotomic_prime_pow hq hq3 hk1 hdvd hirr hk_dvd) ?_
    have hcop := Nat.prime_two.coprime_iff_not_dvd.mpr (not_two_dvd_prime_pow hq hq3 k)
    have hqk : 1 < q ^ k := Nat.one_lt_pow (Nat.ne_of_gt hk1) (by omega)
    have hu : (ZMod.unitOfCoprime 2 hcop) ^ (polyOfBits (shoupCyclicFactor q k)).natDegree = 1 := by
      rw [natDegree_eq_orderOf_of_dvd_cyclotomic_prime_pow hq hq3 hdvd hirr, pow_orderOf_eq_one]
    have hdvd_q := (dvd_pow_self q (Nat.ne_of_gt hk1)).trans
      ((dvd_two_pow_sub_one_iff_modEq hqk).mpr ((zmod_unit_two_pow_eq_one_iff hqk hcop _).mp hu))
    dsimp only [m]
    rw [hm_ord, orderOf_dvd_iff_pow_eq_one, zmod_unit_two_pow_eq_one_iff (by omega)]
    exact (dvd_two_pow_sub_one_iff_modEq (by omega : 1 < q)).mp hdvd_q
  have hne : shoupCyclicFactor q k ≠ [] := fun h => by simp [h] at hdeg
  have := natDegree_polyOfBits_of_polyTrim ht hne
  have := List.length_pos_of_ne_nil hne
  exact ⟨ht, hdvd, hirr, hdeg_m, by dsimp only [m, k] at *; omega⟩

/-- Length bound along iterations of `shoupCyclicFactor`. -/
theorem length_shoupCyclicFactor_iterate_le {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) {s : ℕ}
    (hs : s ≤ qAdicValTwoPowSubOne q (ordTwoMod q) - 1) :
    ((fun g => berlekampIrreducibleFactor (polyComposePow q g))^[s]
      (berlekampIrreducibleFactor (List.replicate q true))).length ≤ q := by
  obtain ⟨hm2, hmq, -, -, -⟩ := ordTwoMod_spec hq hq3
  obtain ⟨_, -, hk_dvd, -⟩ := qAdicValTwoPowSubOne_spec hq hq3
  obtain ⟨ht, hdvd, hirr, hdeg_pos⟩ := shoupCyclicFactor_iterate_spec hq hq3 s
  have hdeg_le := Nat.le_of_dvd (by omega)
    (natDegree_dvd_of_dvd_cyclotomic_prime_pow hq hq3 (Nat.succ_pos s) hdvd hirr
      ((Nat.pow_dvd_pow q (by omega)).trans hk_dvd))
  have := natDegree_polyOfBits_of_polyTrim ht fun h => by simp [h] at hdeg_pos
  omega

/-! ### Irreducibility of `Y ^ q - ζ` over `K = 𝔽₂[Z] / (f)` -/

private theorem orderOf_of_pow_prime {G : Type*} [Group G] {q k : ℕ} (hq : q.Prime) (hk1 : 1 ≤ k)
    {η ζ : G} (hpow : η ^ q = ζ) (hord : orderOf ζ = q ^ k) :
    orderOf η = q ^ (k + 1) := by
  have hdvd : orderOf η ∣ q ^ (k + 1) := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_succ', pow_mul, hpow, ← hord, pow_orderOf_eq_one]
  have hndvd : ¬ orderOf η ∣ q ^ k := fun h => by
    have h2 : ζ ^ (q ^ (k - 1)) = 1 := by
      rw [← hpow, ← pow_mul, ← pow_succ', Nat.sub_add_cancel hk1]
      exact orderOf_dvd_iff_pow_eq_one.mp h
    have hle := Nat.le_of_dvd (pow_pos hq.pos _) (hord ▸ orderOf_dvd_iff_pow_eq_one.mpr h2)
    have := Nat.pow_lt_pow_right hq.one_lt (Nat.sub_lt hk1 zero_lt_one)
    omega
  obtain ⟨j, hj_le, hj_eq⟩ := (Nat.dvd_prime_pow hq).mp hdvd
  rw [hj_eq] at hndvd ⊢
  rcases eq_or_lt_of_le hj_le with rfl | hlt
  · rfl
  · exact absurd (Nat.pow_dvd_pow q (by omega)) hndvd

private theorem irreducible_X_pow_sub_C_of_orderOf {q k m : ℕ} {f : (ZMod 2)[X]}
    (hq : q.Prime) (hq3 : 3 ≤ q) (hk1 : 1 ≤ k) (hirr : Irreducible f)
    (hdeg : f.natDegree = m)
    (hdvd : f ∣ cyclotomic (q ^ k) (ZMod 2))
    (hk1_ndvd : ¬ q ^ (k + 1) ∣ 2 ^ m - 1) :
    let : Fact (Irreducible f) := ⟨hirr⟩
    Irreducible (X ^ q - C (AdjoinRoot.root f)) := by
  have : Fact (Irreducible f) := ⟨hirr⟩
  set K := AdjoinRoot f; set ζ : K := AdjoinRoot.root f; set G : K[X] := X ^ q - C ζ
  let hpb := AdjoinRoot.powerBasis hirr.ne_zero
  have : Module.Finite (ZMod 2) K := hpb.finite
  have : Finite K := Module.finite_of_finite (ZMod 2)
  let : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 2 ^ m := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := K), ZMod.card, hpb.finrank,
      AdjoinRoot.powerBasis_dim, hdeg]
  have : NeZero ((q ^ k : ℕ) : K) := ⟨fun h =>
    not_two_dvd_prime_pow hq hq3 k ((CharP.cast_eq_zero_iff (ZMod 2) 2 _).mp
      ((algebraMap (ZMod 2) K).injective (by rwa [map_natCast, map_zero])))⟩
  have hζ_prim : IsPrimitiveRoot ζ (q ^ k) := Polynomial.isRoot_cyclotomic_iff.mp <| by
    simpa [Polynomial.map_cyclotomic] using
      (AdjoinRoot.isRoot_root f).dvd (map_dvd (algebraMap (ZMod 2) K) hdvd)
  have hζ_ne : ζ ≠ 0 := hζ_prim.ne_zero (pow_ne_zero k hq.ne_zero)
  have hG_deg : G.natDegree = q := by dsimp only [G]; rw [natDegree_X_pow_sub_C]
  have hG_ne : G ≠ 0 := (monic_X_pow_sub_C ζ hq.ne_zero).ne_zero
  by_contra hnirr
  obtain ⟨g, hg_mem⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors hG_ne
    (not_isUnit_of_natDegree_pos G (hG_deg ▸ hq.pos))
  have hg_irr := UniqueFactorizationMonoid.irreducible_of_normalized_factor g hg_mem
  have hg_dvd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem
  have hg_lt : g.natDegree < q := lt_of_not_ge fun hge => hnirr <|
    (associated_of_dvd_of_natDegree_le hg_dvd hG_ne (hG_deg ▸ hge)).irreducible hg_irr
  set d := g.natDegree
  have : Fact (Irreducible g) := ⟨hg_irr⟩
  set L₀ := AdjoinRoot g; set θ : L₀ := AdjoinRoot.root g
  let hpb0 := AdjoinRoot.powerBasis hg_irr.ne_zero
  have : Module.Finite K L₀ := hpb0.finite
  have hθ_pow : θ ^ q = algebraMap K L₀ ζ := by
    rcases hg_dvd with ⟨r, hr⟩
    have hg0 : g.eval₂ (algebraMap K L₀) θ = 0 := AdjoinRoot.eval₂_root g
    simpa [G, hg0, sub_eq_zero] using congrArg (eval₂ (algebraMap K L₀) θ) hr
  set β : K := Algebra.norm K θ
  have hβ_pow : β ^ q = ζ ^ d := by
    rw [← map_pow, hθ_pow, Algebra.norm_algebraMap, hpb0.finrank, AdjoinRoot.powerBasis_dim]
  have hβ_ne : β ≠ 0 := fun h0 => pow_ne_zero d hζ_ne (by simpa [h0, hq.ne_zero] using hβ_pow.symm)
  obtain ⟨u, _, hu_mod⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hg_irr.natDegree_pos hg_lt)).symm)
    hq.one_lt
  set v := u * d / q
  have hud_eq : u * d = v * q + 1 := by
    rw [mul_comm v q, ← show (u * d) % q = 1 by simpa [mul_comm] using hu_mod, Nat.div_add_mod]
  set η : K := β ^ u * (ζ ^ v)⁻¹
  have hη_ne : η ≠ 0 := mul_ne_zero (pow_ne_zero u hβ_ne) (inv_ne_zero (pow_ne_zero v hζ_ne))
  have hη_pow : η ^ q = ζ := by
    rw [mul_pow, ← pow_mul, mul_comm u q, pow_mul, hβ_pow, ← pow_mul, mul_comm d u, inv_pow,
      ← pow_mul, hud_eq, pow_add, pow_one, mul_right_comm (ζ ^ (v * q)) ζ,
      mul_inv_cancel₀ (pow_ne_zero (v * q) hζ_ne), one_mul]
  have hord := orderOf_of_pow_prime hq hk1 (Units.ext (by simp [hη_pow]) :
      (Units.mk0 η hη_ne) ^ q = Units.mk0 ζ hζ_ne) <| by
    rw [← orderOf_injective (Units.coeHom K) Units.coeHom_injective]
    exact hζ_prim.eq_orderOf.symm
  exact hk1_ndvd <| by
    simpa only [hord, Fintype.card_units, hcardK] using orderOf_dvd_card (x := Units.mk0 η hη_ne)

/-! ### Explicit arithmetic in `L = K[Y] / (Y ^ q - Z)` and Shoup's irreducible polynomial -/

/-- Addition in `L = K[Y] / (Y ^ q - Z)`. -/
@[expose] def shoupLAdd (q : ℕ) (a b : List (List Bool)) : List (List Bool) :=
  (List.range q).map fun i => polyAdd (a.getD i []) (b.getD i [])

/-- Multiplication in `L = K[Y] / (Y ^ q - Z)` with modulus `f` for `K = 𝔽₂[Z] / (f)`. -/
@[expose] def shoupLMul (q : ℕ) (f : List Bool) (a b : List (List Bool)) : List (List Bool) :=
  (List.range q).map fun k =>
    let low := (List.range (k + 1)).foldl
      (fun acc i => polyAdd acc (polyMul (a.getD i []) (b.getD (k - i) []))) []
    let high := (List.range (q - 1 - k)).foldl
      (fun acc t =>
        let i := k + 1 + t
        polyAdd acc (polyMul (a.getD i []) (b.getD (q + k - i) []))) []
    polyMod (polyAdd low (false :: high)) f

/-- Frobenius power `a ^ (2 ^ q)` in `L = K[Y] / (Y ^ q - Z)`. -/
@[expose] def shoupLFrobQ (q : ℕ) (f : List Bool) (a : List (List Bool)) :
    List (List Bool) :=
  (fun x => shoupLMul q f x x)^[q] a

/-- Element `β = ∑_{s=0}^{m-1} Y ^ (2 ^ (s * q))` in `L`. -/
@[expose] def shoupBeta (q : ℕ) (f : List Bool) : List (List Bool) :=
  let m := f.length - 1
  let y := (List.range q).map fun i => if i == 1 then [true] else []
  ((List.range m).foldl
    (fun st _ => (shoupLAdd q st.1 st.2, shoupLFrobQ q f st.2))
    (List.replicate q [], y)).1

/-- Powers `[1, β, …, β ^ q]` in `L`. -/
@[expose] def shoupPowers (q : ℕ) (f : List Bool) (β : List (List Bool)) :
    List (List (List Bool)) :=
  let one := (List.range q).map fun i => if i == 0 then [true] else []
  ((List.range (q + 1)).foldl
    (fun st _ => (st.1 ++ [st.2], shoupLMul q f st.2 β)) ([], one)).1

/-- `(q * m) × (q + 1)` Boolean matrix whose columns are `[1, β, …, β ^ q]` in basis `{Z^j Y^i}`. -/
@[expose] def shoupMinPolyMatrix (q m : ℕ) (pows : List (List (List Bool))) :
    List (List Bool) :=
  (List.range (q * m)).map fun idx =>
    let i := idx / m
    let j := idx % m
    pows.map fun v => (v.getD i []).getD j false

/-- Deterministic Shoup algorithm returning an irreducible binary polynomial of degree `q`
over `𝔽₂` (for every odd prime `q`). -/
@[expose] def shoupIrreducibleBits (q : ℕ) : List Bool :=
  if q.Prime ∧ 3 ≤ q then
    let m := ordTwoMod q
    let k := qAdicValTwoPowSubOne q m
    let f := shoupCyclicFactor q k
    let β := shoupBeta q f
    let pows := shoupPowers q f β
    kernelVecBits (q + 1) (shoupMinPolyMatrix q m pows)
  else []

section FieldInterpretation

private noncomputable def evalL {K L : Type*} [CommRing K] [CommRing L]
    [Algebra (ZMod 2) K] [Algebra K L] (ζ : K) (y : L) (q : ℕ)
    (v : List (List Bool)) : L :=
  ∑ i : Fin q, algebraMap K L ((polyOfBits (v.getD i.1 [])).aeval ζ) * y ^ i.1

private theorem evalL_shoupLAdd {K L : Type*} [Field K] [Field L]
    [Algebra (ZMod 2) K] [Algebra K L] (ζ : K) (y : L) (q : ℕ)
    (a b : List (List Bool)) :
    evalL ζ y q (shoupLAdd q a b) = evalL ζ y q a + evalL ζ y q b := by
  simp only [evalL, shoupLAdd, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [List.getD_map_range _ _ i.2, polyOfBits_polyAdd, map_add, map_add, add_mul]

private theorem evalL_shoupLMul {K L : Type*} [Field K] [Field L]
    [Algebra (ZMod 2) K] [Algebra K L] {ζ : K} {y : L} {q : ℕ} (hq0 : 0 < q)
    {f : List Bool} (hf_ne : polyOfBits f ≠ 0)
    (hζ : (polyOfBits f).aeval ζ = 0) (hy : y ^ q = algebraMap K L ζ)
    (a b : List (List Bool)) :
    evalL ζ y q (shoupLMul q f a b) = evalL ζ y q a * evalL ζ y q b := by
  have : NeZero q := ⟨hq0.ne'⟩
  have hmod : ∀ p, (polyOfBits (polyMod p f)).aeval ζ = (polyOfBits p).aeval ζ := fun p => by
    have := congrArg (aeval ζ) (polyOfBits_polyDivMod_spec (a := p) hf_ne).1
    simpa only [map_add, map_mul, hζ, mul_zero, zero_add] using this
  have hfold : ∀ n (g : ℕ → List Bool),
      (polyOfBits ((List.range n).foldl (fun acc x => polyAdd acc (g x)) [])).aeval ζ =
        ∑ x ∈ Finset.range n, (polyOfBits (g x)).aeval ζ := fun n g => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        polyOfBits_polyAdd, map_add, ih, Finset.sum_range_succ]
  let T : ℕ → ℕ → L := fun i j =>
    algebraMap K L ((polyOfBits (polyMul (a.getD i []) (b.getD j []))).aeval ζ) * y ^ (i + j)
  have hprod : evalL ζ y q a * evalL ζ y q b = ∑ p : Fin q × Fin q, T p.1.1 p.2.1 := by
    rw [evalL, evalL, Finset.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      simp only [T, polyOfBits_polyMul, map_mul, pow_add]; ring
  let e : Fin q × Fin q ≃ Fin q × Fin q :=
    ⟨fun p => (p.1, p.2 - p.1), fun p => (p.1, p.1 + p.2),
      fun p => by ext <;> simp, fun p => by ext <;> simp⟩
  rw [hprod, ← Equiv.sum_comp e, Fintype.sum_prod_type, Finset.sum_comm, evalL]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [shoupLMul, List.getD_map_range _ _ k.2, hmod, polyOfBits_polyAdd, map_add,
    polyOfBits_false_cons, map_mul, aeval_X, hfold, hfold, map_add, map_sum, map_mul,
    map_sum, add_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
  have hsub : ∀ i : Fin q,
      T i.1 (k - i).1 = if i.1 ≤ k.1 then T i.1 (k.1 - i.1) else T i.1 (q + k.1 - i.1) := by
    intro i; split_ifs with hik
    · rw [Fin.sub_val_of_le hik]
    · rw [show (k - i).1 = q + k.1 - i.1 by rw [Fin.val_sub, Nat.mod_eq_of_lt (by omega)]; omega]
  simp_rw [e, Equiv.coe_fn_mk, hsub]
  rw [Fin.sum_univ_eq_sum_range (fun i =>
    if i ≤ k.1 then T i (k.1 - i) else T i (q + k.1 - i)) q]
  conv_rhs =>
    rw [congrArg Finset.range (show q = k.1 + 1 + (q - 1 - k.1) by omega), Finset.sum_range_add]
  refine congrArg₂ (· + ·)
    (Finset.sum_congr rfl fun i hi => by
      have hi' : i ≤ k.1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [ite_eq_left hi']; simp only [T, Nat.add_sub_cancel' hi'])
    (Finset.sum_congr rfl fun t ht => by
      have ht' := Finset.mem_range.mp ht
      rw [ite_eq_right (by omega : ¬ k.1 + 1 + t ≤ k.1)]
      dsimp only [T]
      rw [show k.1 + 1 + t + (q + k.1 - (k.1 + 1 + t)) = q + k.1 by omega, pow_add, hy]; ring)

private theorem evalL_shoupLFrobQ {K L : Type*} [Field K] [Field L]
    [Algebra (ZMod 2) K] [Algebra K L] {ζ : K} {y : L} {q : ℕ} (hq0 : 0 < q)
    {f : List Bool} (hf_ne : polyOfBits f ≠ 0)
    (hζ : (polyOfBits f).aeval ζ = 0) (hy : y ^ q = algebraMap K L ζ)
    (a : List (List Bool)) :
    evalL ζ y q (shoupLFrobQ q f a) = (evalL ζ y q a) ^ (2 ^ q) := by
  suffices ∀ s, evalL ζ y q ((fun x => shoupLMul q f x x)^[s] a) = (evalL ζ y q a) ^ (2 ^ s) from
    this q
  intro s; induction s with
  | zero => simp
  | succ s ih =>
    rw [Function.iterate_succ_apply', evalL_shoupLMul hq0 hf_ne hζ hy, ih, ← sq, ← pow_mul,
      ← pow_succ]

private theorem evalL_single {K L : Type*} [Field K] [Field L]
    [Algebra (ZMod 2) K] [Algebra K L] (ζ : K) (y : L) {q idx : ℕ} (hidx : idx < q) :
    evalL ζ y q ((List.range q).map fun i => if i == idx then [true] else []) = y ^ idx := by
  rw [evalL, Finset.sum_eq_single ⟨idx, hidx⟩]
  · rw [List.getD_map_range _ _ hidx]; simp [bitEquiv_symm_true]
  · intro i _ hi
    rw [List.getD_map_range _ _ i.2, beq_false_of_ne fun h => hi (Fin.ext h)]; simp
  · exact fun hm => absurd (Finset.mem_univ (⟨idx, hidx⟩ : Fin q)) hm

private theorem evalL_shoupBeta {K L : Type*} [Field K] [Field L]
    [Algebra (ZMod 2) K] [Algebra K L] {ζ : K} {y : L} {q : ℕ} (hq : 2 ≤ q)
    {f : List Bool} (hf_ne : polyOfBits f ≠ 0)
    (hζ : (polyOfBits f).aeval ζ = 0) (hy : y ^ q = algebraMap K L ζ) :
    evalL ζ y q (shoupBeta q f) = ∑ s ∈ Finset.range (f.length - 1), y ^ (2 ^ (s * q)) := by
  have hinv : ∀ k,
      let st := (List.range k).foldl
        (fun st _ => (shoupLAdd q st.1 st.2, shoupLFrobQ q f st.2))
        (List.replicate q [], (List.range q).map fun i => if i == 1 then [true] else [])
      evalL ζ y q st.1 = (∑ s ∈ Finset.range k, y ^ (2 ^ (s * q))) ∧
        evalL ζ y q st.2 = y ^ (2 ^ (k * q)) := fun k => by
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp only [List.range_zero, List.foldl_nil, Finset.range_zero, Finset.sum_empty, evalL]
        exact Finset.sum_eq_zero fun i _ => by
          rw [List.getD_eq_getElem _ _ (by simp), List.getElem_replicate]; simp [polyOfBits_nil]
      · simpa only [List.range_zero, List.foldl_nil, zero_mul, pow_zero, pow_one] using
          evalL_single ζ y (by omega : 1 < q)
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact ⟨by rw [evalL_shoupLAdd, ih.1, ih.2, Finset.sum_range_succ],
        by rw [evalL_shoupLFrobQ (by omega) hf_ne hζ hy, ih.2, ← pow_mul, ← pow_add,
          Nat.succ_mul]⟩
  exact (hinv (f.length - 1)).1

private theorem shoupPowers_foldl {α : Type*} (step : α → α) (init : α) (n : ℕ) :
    (List.range n).foldl (fun st _ => (st.1 ++ [st.2], step st.2)) ([], init) =
      ((List.range n).map fun c => step^[c] init, step^[n] init) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      List.map_append, List.map_singleton, Function.iterate_succ_apply']

private theorem shoupPowers_getD (q : ℕ) (f : List Bool) (β : List (List Bool))
    {c : ℕ} (hc : c < q + 1) :
    (shoupPowers q f β).getD c [] =
      (fun x => shoupLMul q f x β)^[c]
        ((List.range q).map fun i => if i == 0 then [true] else []) := by
  unfold shoupPowers
  dsimp only
  rw [shoupPowers_foldl (fun x => shoupLMul q f x β)]
  exact List.getD_map_range _ _ hc

private theorem shoupPowers_spec {K L : Type*} [Field K] [Field L]
    [Algebra (ZMod 2) K] [Algebra K L] {ζ : K} {y : L} {q : ℕ} (hq : 0 < q)
    {f : List Bool} (hf_ne : polyOfBits f ≠ 0)
    (hζ : (polyOfBits f).aeval ζ = 0) (hy : y ^ q = algebraMap K L ζ)
    (β : List (List Bool)) :
    (shoupPowers q f β).length = q + 1 ∧
      ∀ c < q + 1, evalL ζ y q ((shoupPowers q f β).getD c []) = (evalL ζ y q β) ^ c := by
  refine ⟨?_, fun c hc => ?_⟩
  · unfold shoupPowers
    dsimp only
    rw [shoupPowers_foldl (fun x => shoupLMul q f x β)]
    simp
  · rw [shoupPowers_getD q f β hc]
    clear hc
    induction c with
    | zero => simpa only [Function.iterate_zero, id_eq, pow_zero] using evalL_single ζ y hq
    | succ c ih =>
      rw [Function.iterate_succ_apply', evalL_shoupLMul hq hf_ne hζ hy, ih, pow_succ]

private theorem shoupMinPolyMatrix_length (q m : ℕ) (pows : List (List (List Bool)))
    (hpows : pows.length = q + 1) :
    (shoupMinPolyMatrix q m pows).length = q * m ∧
      ∀ row ∈ shoupMinPolyMatrix q m pows, row.length = q + 1 := by
  refine ⟨by simp [shoupMinPolyMatrix], fun row hrow => ?_⟩
  obtain ⟨_, -, rfl⟩ := List.mem_map.mp hrow
  simp [hpows]

private theorem two_pow_mod_pow_eq {q : ℕ} (hq : q.Prime) (s : ℕ) :
    2 ^ (s * q) % q = 2 ^ s % q := by
  have : Fact q.Prime := ⟨hq⟩
  rw [← ZMod.natCast_eq_natCast_iff']
  calc ((2 ^ (s * q) : ℕ) : ZMod q)
      = ((2 : ZMod q) ^ q) ^ s := by rw [Nat.cast_pow, Nat.cast_ofNat, mul_comm, pow_mul]
    _ = (2 : ZMod q) ^ s := by rw [ZMod.pow_card]
    _ = ((2 ^ s : ℕ) : ZMod q) := by rw [Nat.cast_pow, Nat.cast_ofNat]

private theorem shoupMinPolyMatrix_mulVec_zero_iff {K L : Type*} [Field K] [Field L]
    [Algebra (ZMod 2) K] [Algebra K L] [Algebra (ZMod 2) L] [IsScalarTower (ZMod 2) K L]
    {q m : ℕ} (hm0 : 0 < m) (ζ : K) (y βL : L)
    (pbK : PowerBasis (ZMod 2) K) (pbL : PowerBasis K L)
    (hpbK_dim : pbK.dim = m) (hpbL_dim : pbL.dim = q)
    (hpbK_coe : ∀ idx : Fin pbK.dim, pbK.basis idx = ζ ^ idx.1)
    (hpbL_coe : ∀ idx : Fin pbL.dim, pbL.basis idx = y ^ idx.1)
    (pows : List (List (List Bool))) (hpows_len : pows.length = q + 1)
    (hpows_eval : ∀ c < q + 1, evalL ζ y q (pows.getD c []) = βL ^ c)
    (hpows_entry_len : ∀ c < q + 1, ∀ i < q, ((pows.getD c []).getD i []).length ≤ m)
    (v : Fin (q + 1) → ZMod 2) :
    rowsToZModMatrix (q * m) (q + 1) (shoupMinPolyMatrix q m pows) *ᵥ v = 0 ↔
      ∑ c : Fin (q + 1), v c • βL ^ c.1 = 0 := by
  let bL : Basis (Fin q) K L := pbL.basis.reindex (finCongr hpbL_dim)
  let bK : Basis (Fin m) (ZMod 2) K := pbK.basis.reindex (finCongr hpbK_dim)
  have hbL : ∀ i : Fin q, bL i = y ^ i.1 := fun i => by rw [Basis.reindex_apply, hpbL_coe]; rfl
  have hbK : ∀ j : Fin m, bK j = ζ ^ j.1 := fun j => by rw [Basis.reindex_apply, hpbK_coe]; rfl
  let d : Fin q → Fin m → ZMod 2 := fun i j =>
    ∑ c : Fin (q + 1), v c * bitEquiv.symm (((pows.getD c.1 []).getD i.1 []).getD j.1 false)
  have heq : (∑ c : Fin (q + 1), v c • βL ^ c.1) =
      ∑ i : Fin q, (∑ j : Fin m, d i j • bK j) • bL i := by
    have hterm : ∀ c : Fin (q + 1), v c • βL ^ c.1 = ∑ i : Fin q,
        (∑ j : Fin m, (v c * bitEquiv.symm (((pows.getD c.1 []).getD i.1 []).getD j.1 false)) •
          bK j) • bL i := fun c => by
      rw [← hpows_eval c.1 c.2, evalL, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← smul_mul_assoc, Algebra.smul_def (R := ZMod 2),
        IsScalarTower.algebraMap_apply (ZMod 2) K L, ← map_mul,
        ← Algebra.smul_def (R := ZMod 2), ← hbL i, ← Algebra.smul_def]
      refine congrArg (· • bL i) ?_
      rw [aeval_polyOfBits, Finset.smul_sum]
      trans ∑ j ∈ Finset.range m,
          (v c * bitEquiv.symm (((pows.getD c.1 []).getD i.1 []).getD j false)) • ζ ^ j
      · rw [← Finset.sum_subset (Finset.range_mono (hpows_entry_len c.1 c.2 i.1 i.2))]
        · exact Finset.sum_congr rfl fun _ _ => smul_smul ..
        · intro j _ hj
          rw [List.getD_eq_default _ _ (not_lt.mp (Finset.mem_range.not.mp hj)),
            bitEquiv_symm_false, mul_zero, zero_smul]
      · simp_rw [hbK]; exact (Fin.sum_univ_eq_sum_range _ m).symm
    simp_rw [hterm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul, Finset.sum_comm]
    exact congrArg (· • bL i) (Finset.sum_congr rfl fun j _ => (Finset.sum_smul ..).symm)
  have hmul : ∀ idx : Fin (q * m),
      (rowsToZModMatrix (q * m) (q + 1) (shoupMinPolyMatrix q m pows) *ᵥ v) idx =
        d ⟨idx.1 / m, Nat.div_lt_of_lt_mul (mul_comm q m ▸ idx.2)⟩
          ⟨idx.1 % m, Nat.mod_lt _ hm0⟩ := fun idx => by
    simp only [Matrix.mulVec, dotProduct, rowsToZModMatrix, bitsToZModVec]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hc : c.1 < pows.length := by
      rw [hpows_len]
      exact c.2
    rw [shoupMinPolyMatrix, List.getD_map_range _ _ idx.2,
      List.getD_eq_getElem _ _ (by simp [hc]), List.getElem_map,
      ← List.getD_eq_getElem pows [] hc, mul_comm]
  rw [heq]
  constructor
  · intro h0
    refine Finset.sum_eq_zero fun i _ => ?_
    suffices ∀ j, d i j = 0 by simp [this]
    intro j
    have hidx : m * i.1 + j.1 < q * m := by nlinarith [i.2, j.2]
    simpa [Nat.mul_add_div hm0, Nat.div_eq_of_lt j.2, Nat.mul_add_mod, Nat.mod_eq_of_lt j.2] using
      (hmul ⟨m * i.1 + j.1, hidx⟩).symm.trans (congrFun h0 ⟨m * i.1 + j.1, hidx⟩)
  · intro h0; funext idx; rw [hmul, Pi.zero_apply]
    let i : Fin q := ⟨idx.1 / m, Nat.div_lt_of_lt_mul (mul_comm q m ▸ idx.2)⟩
    have hci := (linearIndependent_iff'.mp bL.linearIndependent Finset.univ
      (fun i => ∑ j : Fin m, d i j • bK j) h0) i (Finset.mem_univ _)
    exact (linearIndependent_iff'.mp bK.linearIndependent Finset.univ (d i) hci) _
      (Finset.mem_univ _)

private theorem shoupBeta_minpoly_natDegree {K L : Type*} [Field K] [Field L]
    [Algebra (ZMod 2) K] [Algebra K L] [Algebra (ZMod 2) L] [IsScalarTower (ZMod 2) K L]
    [Module.Finite (ZMod 2) L] [CharP L 2]
    {q m : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) (hm2 : 2 ≤ m)
    (hm_min : ∀ j, 0 < j → j < m → 2 ^ j % q ≠ 1)
    (ζ : K) (y : L) (f : List Bool) (hf_ne : polyOfBits f ≠ 0) (hf_len : f.length = m + 1)
    (hζ_root : (polyOfBits f).aeval ζ = 0) (hy_pow : y ^ q = algebraMap K L ζ)
    (hy_card : y ^ (2 ^ (m * q)) = y)
    (pbL : PowerBasis K L) (hpbL_dim : pbL.dim = q)
    (hpbL_coe : ∀ idx : Fin pbL.dim, pbL.basis idx = y ^ idx.1) :
    let βL : L := evalL ζ y q (shoupBeta q f)
    (∀ a : ZMod 2, βL ≠ algebraMap (ZMod 2) L a) ∧ (minpoly (ZMod 2) βL).natDegree = q := by
  set βL : L := evalL ζ y q (shoupBeta q f)
  have hβL_eq : βL = ∑ s ∈ Finset.range m, y ^ (2 ^ (s * q)) := by
    simpa only [hf_len, Nat.add_sub_cancel] using
      evalL_shoupBeta (by omega : 2 ≤ q) hf_ne hζ_root hy_pow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hβ_frob : βL ^ (2 ^ q) = βL := by
    rw [hβL_eq, sum_pow_char_pow, ← Nat.sub_add_cancel (by omega : 1 ≤ m),
      Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [zero_mul, pow_zero, pow_one, add_comm]
    refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun s _ => by
      rw [← pow_mul, ← pow_add, Nat.succ_mul])
    rw [← pow_mul, ← pow_add, show (m - 1) * q + q = m * q by
      rw [← add_one_mul, Nat.sub_add_cancel (by omega)], hy_card]
  have hβ_notin : ∀ a : ZMod 2, βL ≠ algebraMap (ZMod 2) L a := fun a heq => by
    let bL : Basis (Fin q) K L := pbL.basis.reindex (finCongr hpbL_dim)
    have hbL : ∀ i : Fin q, bL i = y ^ i.1 := fun i => by rw [Basis.reindex_apply, hpbL_coe]; rfl
    have hLHS : bL.repr βL ⟨1, by omega⟩ = 1 := by
      rw [hβL_eq, map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single 0]
      · rw [zero_mul, pow_zero, pow_one, ← (hbL ⟨1, by omega⟩).trans (pow_one y),
          Basis.repr_self, Finsupp.single_eq_same]
      · intro s hs hs0
        have hy_s : y ^ (2 ^ (s * q)) =
            (ζ ^ (2 ^ (s * q) / q)) • bL ⟨2 ^ (s * q) % q, Nat.mod_lt _ (by omega)⟩ := by
          nth_rw 1 [← Nat.div_add_mod (2 ^ (s * q)) q]
          rw [pow_add, pow_mul, hy_pow, ← map_pow, ← Algebra.smul_def, hbL]
        rw [hy_s, map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_apply,
          ite_eq_right fun hfin => hm_min s (Nat.pos_of_ne_zero hs0) (Finset.mem_range.mp hs)
            (two_pow_mod_pow_eq hq s ▸ congrArg Fin.val hfin), smul_zero]
      · exact fun hm0 => absurd (Finset.mem_range.mpr (by omega : 0 < m)) hm0
    have hRHS : bL.repr (algebraMap (ZMod 2) L a) ⟨1, by omega⟩ = 0 := by
      have ha : algebraMap (ZMod 2) L a = algebraMap (ZMod 2) K a • bL ⟨0, by omega⟩ := by
        rw [Algebra.smul_def, hbL, pow_zero, mul_one, IsScalarTower.algebraMap_apply (ZMod 2) K L]
      rw [ha, map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_apply,
        ite_eq_right fun h => absurd (congrArg Fin.val h) Nat.zero_ne_one, smul_zero]
    exact one_ne_zero (hLHS.symm.trans (heq ▸ hRHS))
  have hβ_int := IsIntegral.of_finite (ZMod 2) βL
  refine ⟨hβ_notin, ?_⟩
  let E := IntermediateField.adjoin (ZMod 2) ({βL} : Set L)
  set d := (minpoly (ZMod 2) βL).natDegree
  have : Module.Finite (ZMod 2) E :=
    FiniteDimensional.of_finrank_pos (IntermediateField.adjoin.finrank hβ_int ▸
      minpoly.natDegree_pos hβ_int)
  have : Finite E := Module.finite_of_finite (ZMod 2)
  classical
  let : Fintype E := Fintype.ofFinite E
  let S_if : IntermediateField (ZMod 2) L :=
    { carrier := {x : L | x ^ (2 ^ q) = x}
      mul_mem' := fun hx hy => by
        dsimp at hx hy ⊢
        rw [mul_pow, hx, hy]
      one_mem' := one_pow _
      add_mem' := fun hx hy => by
        dsimp at hx hy ⊢
        rw [add_pow_char_pow, hx, hy]
      zero_mem' := zero_pow (by positivity)
      algebraMap_mem' := fun c => by
        dsimp
        rw [← map_pow]
        congr 1
        fin_cases c <;> [exact zero_pow (by positivity); exact one_pow _]
      inv_mem' := fun {x} hx => by
        dsimp at hx ⊢
        rw [inv_pow, hx] }
  have hE_le : E ≤ S_if :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hβ_frob)
  obtain ⟨w, hw⟩ := IsCyclic.exists_generator (α := Eˣ)
  have hw_ord : orderOf w = 2 ^ d - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hw, Nat.card_eq_fintype_card, Fintype.card_units,
      Module.card_eq_pow_finrank (K := ZMod 2) (V := E), ZMod.card,
      IntermediateField.adjoin.finrank hβ_int]
  have hw_pow : w ^ (2 ^ q - 1) = 1 := by
    rw [← mul_left_inj w, ← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, one_mul]
    exact Units.ext (Subtype.ext (by
      simpa only [Units.val_pow_eq_pow_val, IntermediateField.coe_pow] using
        show ((w : E) : L) ^ (2 ^ q) = ((w : E) : L) from hE_le (w : E).2))
  rcases hq.eq_one_or_self_of_dvd d ((Nat.pow_sub_one_dvd_pow_sub_one_iff one_lt_two).mp
      (hw_ord ▸ orderOf_dvd_iff_pow_eq_one.mpr hw_pow)) with h1 | hq_eq
  · obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.mp h1; exact absurd hc.symm (hβ_notin c)
  · exact hq_eq

private theorem shoupPowers_entry_length {q m : ℕ} (hm1 : 1 ≤ m) (f : List Bool)
    (hf_trim : polyTrim f = f) (hf_len : f.length = m + 1) (hf_ne : polyOfBits f ≠ 0)
    (β : List (List Bool)) :
    ∀ c < q + 1, ∀ i < q, (((shoupPowers q f β).getD c []).getD i []).length ≤ m := by
  intro c hc i hi
  rw [shoupPowers_getD q f β hc]
  cases c with
  | zero =>
    simp only [Function.iterate_zero, id_eq]
    rw [List.getD_map_range _ _ hi]
    split_ifs <;> simp [hm1]
  | succ c =>
    rw [Function.iterate_succ_apply', shoupLMul, List.getD_map_range _ _ hi]
    exact Nat.lt_add_one_iff.mp
      (lt_of_lt_of_eq (polyOfBits_polyDivMod_spec hf_ne).2.1 (by rw [hf_trim, hf_len]))

private theorem kernelVecBits_eq_minpoly {L : Type*} [Field L] [Algebra (ZMod 2) L]
    {q r : ℕ} {βL : L} (hβ_int : IsIntegral (ZMod 2) βL)
    (hmin_deg : (minpoly (ZMod 2) βL).natDegree = q)
    {M : List (List Bool)} (hM_len : M.length = r) (hM_mem : ∀ row ∈ M, row.length = q + 1)
    (hmul_iff : ∀ v : Fin (q + 1) → ZMod 2,
      rowsToZModMatrix r (q + 1) M *ᵥ v = 0 ↔ ∑ c : Fin (q + 1), v c • βL ^ c.1 = 0) :
    let kv := kernelVecBits (q + 1) M
    Irreducible (polyOfBits kv) ∧ (polyOfBits kv).natDegree = q ∧
      polyTrim kv = kv ∧ kv.length = q + 1 := by
  set P := minpoly (ZMod 2) βL; set kv := kernelVecBits (q + 1) M
  have hP_monic : P.Monic := minpoly.monic hβ_int
  have hv0_ne : (fun c : Fin (q + 1) => P.coeff c.1) ≠ 0 := fun h0 => by
    have hq0 := congrFun h0 ⟨q, Nat.lt_succ_self q⟩
    simp only [Pi.zero_apply, ← hmin_deg, hP_monic.coeff_natDegree] at hq0
    exact one_ne_zero hq0
  have hv0_mul : rowsToZModMatrix r (q + 1) M *ᵥ (fun c => P.coeff c.1) = 0 := by
    rw [hmul_iff]
    have hev := minpoly.aeval (ZMod 2) βL
    rw [aeval_def, eval₂_eq_sum_range, hmin_deg, ← Fin.sum_univ_eq_sum_range] at hev
    simpa only [Algebra.smul_def] using hev
  obtain ⟨b, hb, hb'⟩ := List.any_eq_true.mp
    (kernelVecBits_any_of_exists M hM_len hM_mem ⟨_, hv0_ne, hv0_mul⟩)
  have hkv_len : kv.length = q + 1 := length_kernelVecBits (q + 1) M
  have hkv_ne0 : polyOfBits kv ≠ 0 := polyOfBits_ne_zero_of_mem (by simpa using hb' ▸ hb)
  have hkv_eval : (polyOfBits kv).aeval βL = 0 := by
    rw [aeval_polyOfBits, hkv_len, ← Fin.sum_univ_eq_sum_range]
    exact (hmul_iff _).mp (mulVec_kernelVecBits M hM_len hM_mem)
  have hkv_deg : (polyOfBits kv).natDegree ≤ q := by
    have hlt := degree_polyOfBits_lt kv
    rw [degree_eq_natDegree hkv_ne0, Nat.cast_lt] at hlt; omega
  have hpoly_eq : polyOfBits kv = P :=
    (eq_of_monic_of_associated hP_monic (Cslib.monic_of_ne_zero hkv_ne0)
      (associated_of_dvd_of_natDegree_le (minpoly.dvd (ZMod 2) βL hkv_eval) hkv_ne0
        (hmin_deg ▸ hkv_deg))).symm
  have hkv_last : kv.getD q false = true := by
    have hcq : bitEquiv.symm (kv.getD q false) = 1 := by
      rw [← coeff_polyOfBits, hpoly_eq, ← hmin_deg, hP_monic.coeff_natDegree]
    cases hqb : kv.getD q false <;> simp_all
  have hne : kv ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hdrop : kv = kv.dropLast ++ [true] := by
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    rw [List.getLast_eq_getElem, ← List.getD_eq_getElem kv false (by omega), hkv_len,
      Nat.add_sub_cancel, hkv_last]
  exact ⟨hpoly_eq ▸ minpoly.irreducible hβ_int, hpoly_eq ▸ hmin_deg,
    hdrop ▸ polyTrim_append_true _, hkv_len⟩

/-- Correctness of Shoup's deterministic algorithm: `shoupIrreducibleBits q` is trimmed and
represents an irreducible binary polynomial of degree `q`. -/
theorem shoupIrreducibleBits_spec {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    Irreducible (polyOfBits (shoupIrreducibleBits q)) ∧
      (polyOfBits (shoupIrreducibleBits q)).natDegree = q ∧
      polyTrim (shoupIrreducibleBits q) = shoupIrreducibleBits q ∧
      (shoupIrreducibleBits q).length = q + 1 := by
  set m := ordTwoMod q; set k := qAdicValTwoPowSubOne q m; set f := shoupCyclicFactor q k
  obtain ⟨hm2, _, -, hm_min, -⟩ := ordTwoMod_spec hq hq3
  obtain ⟨hk1, -, _, hk1_ndvd⟩ := qAdicValTwoPowSubOne_spec hq hq3
  obtain ⟨hf_trim, hf_cyc, hf_irr, hf_deg, hf_len⟩ := shoupCyclicFactor_spec hq hq3
  have : Fact (Irreducible (polyOfBits f)) := ⟨hf_irr⟩
  set K := AdjoinRoot (polyOfBits f); set ζ : K := AdjoinRoot.root (polyOfBits f)
  set G : K[X] := X ^ q - C ζ
  have hG_irr := irreducible_X_pow_sub_C_of_orderOf hq hq3 hk1 hf_irr hf_deg hf_cyc hk1_ndvd
  have : Fact (Irreducible G) := ⟨hG_irr⟩
  set L := AdjoinRoot G; set y : L := AdjoinRoot.root G
  let pbK := AdjoinRoot.powerBasis hf_irr.ne_zero
  let pbL := AdjoinRoot.powerBasis hG_irr.ne_zero
  have hpbK_dim : pbK.dim = m := (AdjoinRoot.powerBasis_dim _).trans hf_deg
  have hpbL_dim : pbL.dim = q := by
    simp only [pbL, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]
  have : Module.Finite (ZMod 2) K := pbK.finite
  have : Module.Finite K L := pbL.finite
  have : Module.Finite (ZMod 2) L := Module.Finite.trans K L
  have : Finite L := Module.finite_of_finite (ZMod 2)
  let : Fintype L := Fintype.ofFinite L
  have hcardL : Fintype.card L = 2 ^ (m * q) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := L), ZMod.card,
      ← Module.finrank_mul_finrank (ZMod 2) K L, pbK.finrank, pbL.finrank, hpbK_dim, hpbL_dim]
  have hζ_root : (polyOfBits f).aeval ζ = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hy_pow : y ^ q = algebraMap K L ζ := by
    have hy0 := AdjoinRoot.eval₂_root G
    simp only [G, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at hy0
    exact hy0
  set βbits := shoupBeta q f; set βL : L := evalL ζ y q βbits
  have hmin_deg := (shoupBeta_minpoly_natDegree hq hq3 hm2 hm_min ζ y f hf_irr.ne_zero hf_len
    hζ_root hy_pow (hcardL ▸ FiniteField.pow_card y) pbL hpbL_dim
    fun _ => by rw [pbL.coe_basis, AdjoinRoot.powerBasis_gen]).2
  obtain ⟨hpows_len, hpows_eval⟩ :=
    shoupPowers_spec (by omega : 0 < q) hf_irr.ne_zero hζ_root hy_pow βbits
  obtain ⟨hM_len, hM_mem⟩ := shoupMinPolyMatrix_length q m (shoupPowers q f βbits) hpows_len
  have hkv_eq : shoupIrreducibleBits q = kernelVecBits (q + 1)
      (shoupMinPolyMatrix q m (shoupPowers q f βbits)) := by
    simp only [shoupIrreducibleBits, hq, hq3, and_self, ↓reduceIte]; rfl
  rw [hkv_eq]
  exact kernelVecBits_eq_minpoly (IsIntegral.of_finite (ZMod 2) βL) hmin_deg hM_len hM_mem
    (shoupMinPolyMatrix_mulVec_zero_iff (by omega) ζ y βL pbK pbL hpbK_dim hpbL_dim
      (fun _ => by rw [pbK.coe_basis, AdjoinRoot.powerBasis_gen])
      (fun _ => by rw [pbL.coe_basis, AdjoinRoot.powerBasis_gen])
      (shoupPowers q f βbits) hpows_len hpows_eval
      (shoupPowers_entry_length (by omega) f hf_trim hf_len hf_irr.ne_zero βbits))

end FieldInterpretation

/-- `polyOfBits (shoupIrreducibleBits q)` is irreducible for any odd prime `q`. -/
theorem irreducible_polyOfBits_shoupIrreducibleBits {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    Irreducible (polyOfBits (shoupIrreducibleBits q)) :=
  (shoupIrreducibleBits_spec hq hq3).1

/-- `(polyOfBits (shoupIrreducibleBits q)).natDegree = q` for any odd prime `q`. -/
theorem natDegree_polyOfBits_shoupIrreducibleBits {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    (polyOfBits (shoupIrreducibleBits q)).natDegree = q :=
  (shoupIrreducibleBits_spec hq hq3).2.1

/-! ### Single-prime multiplication table and `O(N ^ (4 / 5))` affine disperser -/

/-- Symmetric-polynomial degree `t = max 1 ⌊N ^ (1 / 5)⌋` for the single-prime disperser. -/
@[expose] def primeSymDeg (N : ℕ) : ℕ := max 1 (fifthRoot N)

/-- Raw-bit evaluator for `primeDisperser` on a bit list of length `N`. -/
@[expose] def primeDisperserBits (N : ℕ) (x : List Bool) : Bool :=
  let q := primeDeg N
  let g := shoupIrreducibleBits q
  traceSymCoords (powerMulTable g) (N / q) (primeSymDeg N) x

/-- Unconditional explicit affine disperser for dimension `O(N ^ (4 / 5))`, evaluating
Ben-Sasson and Kopparty's `traceSym 1 r t` over `𝔽_{2 ^ q}` (`q = primeDeg N ≈ N ^ (3 / 5)`). -/
@[expose] def primeDisperser (N : ℕ) (x : BitString N) : Bool :=
  primeDisperserBits N (List.ofFn x)

/-- Explicit dimension threshold (`primeThreshold N + 1 = O(N ^ (4 / 5))`) at which
`primeDisperser N` is guaranteed to be an affine disperser. -/
@[expose] def primeThreshold (N : ℕ) : ℕ :=
  let q := primeDeg N
  let r := N / q
  let t := primeSymDeg N
  (N - r * q) + (r * (r + 1) + r * (r + 1) + q * t + q * r / t)

/-- `powerMulTable g` satisfies `IsMulTable` for the power basis of `𝔽₂[X] / (polyOfBits g)`. -/
private theorem primeDisperser_isMulTable {g : List Bool} {q : ℕ}
    [Fact (Irreducible (polyOfBits g))] (_hdeg : (polyOfBits g).natDegree = q)
    (htrim : polyTrim g = g) (hlen : g.length = q + 1)
    (b : Basis (Fin q) (ZMod 2) (AdjoinRoot (polyOfBits g)))
    (hb : ∀ i : Fin q, b i = AdjoinRoot.root (polyOfBits g) ^ i.1) :
    IsMulTable b (powerMulTable g) := by
  obtain h | ⟨l, hl⟩ := polyTrim_eq_nil_or_append_true g
  · simp [htrim ▸ h] at hlen
  · rw [htrim] at hl
    have hα : (polyOfBits (l ++ [true])).aeval (AdjoinRoot.root (polyOfBits g)) = 0 := by
      rw [← hl, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    rw [congrArg powerMulTable hl]
    exact isMulTable_powerMulTable (by simpa [hl] using hlen) _ hα b hb

/-- `primeDisperser N` is an affine disperser for dimension `primeThreshold N + 1`. -/
theorem isAffineDisperser_primeDisperser (N : ℕ) :
    IsAffineDisperser (primeDisperser N) (primeThreshold N + 1) := by
  set q := primeDeg N; have hq := (primeDeg_spec N).1; have hq3 := three_le_primeDeg N
  set g := shoupIrreducibleBits q
  obtain ⟨hirr, hdeg, htrim, hlen⟩ := shoupIrreducibleBits_spec hq hq3
  have : Fact (Irreducible (polyOfBits g)) := ⟨hirr⟩
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  have hpb_dim : pb.dim = q := (AdjoinRoot.powerBasis_dim _).trans hdeg
  let b : Basis (Fin q) (ZMod 2) (AdjoinRoot (polyOfBits g)) :=
    pb.basis.reindex (finCongr hpb_dim)
  have hb : ∀ i : Fin q, b i = AdjoinRoot.root (polyOfBits g) ^ i.1 := fun i => by
    rw [Basis.reindex_apply, pb.coe_basis, AdjoinRoot.powerBasis_gen]; rfl
  have hmul : IsMulTable b (powerMulTable g) := primeDisperser_isMulTable hdeg htrim hlen b hb
  have ht : 0 < primeSymDeg N := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hrn := Nat.div_mul_le_self N q
  have : Module.Finite (ZMod 2) (AdjoinRoot (polyOfBits g)) := pb.finite
  have : Finite (AdjoinRoot (polyOfBits g)) := Module.finite_of_finite (ZMod 2)
  have hfinrank : finrank (ZMod 2) (AdjoinRoot (polyOfBits g)) = q := pb.finrank.trans hpb_dim
  have hsub : ∀ K : Subfield (AdjoinRoot (polyOfBits g)), K ≠ ⊤ → Nat.card K ≤ 2 ^ 1 :=
    fun K hK => by
      have hcard := Cslib.card_subfield_le_of_lt_prime (n := q) (L := q - 1) hfinrank
        (fun p hp hpq => by rw [(Nat.prime_dvd_prime_iff_eq hp hq).mp hpq]; omega) K hK
      rwa [Nat.sub_add_cancel hq.one_lt.le, Nat.div_self hq.pos] at hcard
  have heq_fn : primeDisperser N =
      traceSymBits 1 (N / q) (primeSymDeg N) b (blockPos (N := N) hrn) := funext fun x => by
    unfold primeDisperser primeDisperserBits
    rw [traceSymCoords_eq hmul ht hrn, ofList_ofFn]
  rw [heq_fn]
  refine isAffineDisperser_of_forall_exists_ne fun V hV =>
    exists_traceSymBits_ne hfinrank hsub one_ne_zero ht b (pos := blockPos (N := N) hrn)
      (fun _ _ h => finProdFinEquiv.injective (Fin.ext (by
        have hv := congrArg Fin.val h; rwa [blockPos, blockPos] at hv))) V ?_
  rw [hV]
  change _ + (_ * max (_ + 1) 1 + _ + _ + _) < _ + (_ * (_ + 1) + _ + _ + _) + 1
  rw [max_eq_left (Nat.le_add_left 1 _)]
  exact Nat.lt_succ_self _

/-- For all sufficiently large `N`, `primeThreshold N + 1 ≤ 2148 * (fifthRoot N) ^ 4`. -/
theorem eventually_primeThreshold_le :
    ∀ᶠ N in atTop, primeThreshold N + 1 ≤ 2148 * (fifthRoot N) ^ 4 := by
  refine eventually_atTop.mpr ⟨32, fun N hN => ?_⟩
  set u := fifthRoot N; set q := primeDeg N; set r := N / q
  have hN_lt : N < (u + 1) ^ 5 := (fifthRoot_spec N).2
  have hu2 : 2 ≤ u := by_contra fun hlt => by
    have := Nat.pow_le_pow_left (show u + 1 ≤ 2 by omega) 5
    omega
  obtain ⟨_, hq_low, hq_high⟩ := primeDeg_spec N
  rw [show primeThresholdBound N = u ^ 3 by rw [primeThresholdBound, max_eq_right hu2]]
    at hq_low hq_high
  have hN_ub : N ≤ 32 * u ^ 5 := by
    have := Nat.pow_le_pow_left (show u + 1 ≤ 2 * u by omega) 5
    linarith [show (2 * u) ^ 5 = 32 * u ^ 5 by ring]
  have hr_ub : r ≤ 32 * u ^ 2 := Nat.div_le_of_le_mul <|
    hN_ub.trans ((by ring : 32 * u ^ 5 = u ^ 3 * (32 * u ^ 2)) ▸
      Nat.mul_le_mul_right _ hq_low.le)
  have hu2_pos : 1 ≤ u ^ 2 := Nat.pow_pos (by omega)
  have hrr1_ub : r * (r + 1) ≤ 1056 * u ^ 4 :=
    (Nat.mul_le_mul hr_ub (show r + 1 ≤ 33 * u ^ 2 by nlinarith)).trans_eq (by ring)
  have hq_u4 : q ≤ u ^ 4 :=
    hq_high.trans ((Nat.mul_le_mul_right _ hu2).trans_eq (by ring))
  have hwaste : N - r * q ≤ u ^ 4 := by
    have hdiv : q * r + N % q = N := Nat.div_add_mod N q
    have hmod : N % q < q := Nat.mod_lt N (by omega)
    rw [mul_comm r q]; omega
  have hqt_ub : q * u ≤ 2 * u ^ 4 :=
    (Nat.mul_le_mul_right u hq_high).trans_eq (by ring)
  have hqr_t_ub : q * r / u ≤ 32 * u ^ 4 := Nat.div_le_of_le_mul <|
    (Nat.mul_div_le N q).trans (hN_ub.trans_eq (by ring))
  have h1_u4 : 1 ≤ u ^ 4 := Nat.pow_pos (by omega)
  change (N - r * q) + (r * (r + 1) + r * (r + 1) + q * primeSymDeg N +
      q * r / primeSymDeg N) + 1 ≤ 2148 * u ^ 4
  rw [show primeSymDeg N = u from max_eq_right (by omega)]; omega

/-- Real-valued bound `primeThreshold N + 1 ≤ 2148 * N ^ (4 / 5)` for all large `N`. -/
theorem eventually_primeThreshold_real_le :
    ∀ᶠ N in atTop, ((primeThreshold N + 1 : ℕ) : ℝ) ≤ 2148 * (N : ℝ) ^ ((4 : ℝ) / 5) := by
  filter_upwards [eventually_primeThreshold_le] with N hle
  have hu5 : (fifthRoot N : ℝ) ^ 5 ≤ N := by exact_mod_cast (fifthRoot_spec N).1
  have hu0 : (0 : ℝ) ≤ fifthRoot N := Nat.cast_nonneg _
  have hu4 : (fifthRoot N : ℝ) ^ 4 ≤ (N : ℝ) ^ ((4 : ℝ) / 5) := calc
    (fifthRoot N : ℝ) ^ 4 = ((fifthRoot N : ℝ) ^ (5 : ℕ)) ^ ((4 : ℝ) / 5) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hu0]; norm_num
    _ ≤ (N : ℝ) ^ ((4 : ℝ) / 5) := Real.rpow_le_rpow (pow_nonneg hu0 5) hu5 (by norm_num)
  exact ((Nat.cast_le (α := ℝ)).mpr hle).trans (by push_cast; gcongr)

/-- Asymptotic threshold bound `primeThreshold N + 1 = O(N ^ (4 / 5))`. -/
theorem isBigO_primeThreshold :
    (fun N => ((primeThreshold N + 1 : ℕ) : ℝ)) =O[atTop] fun N => (N : ℝ) ^ ((4 : ℝ) / 5) := by
  refine IsBigO.of_bound 2148 ?_
  filter_upwards [eventually_primeThreshold_real_le] with N hrhs
  rwa [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]

/-- `primeThreshold N + 1 < N` for all sufficiently large `N`. -/
theorem eventually_primeThreshold_lt : ∀ᶠ N in atTop, primeThreshold N + 1 < N := by
  filter_upwards [eventually_primeThreshold_le, eventually_ge_atTop (2149 ^ 5)] with N hle hN
  set u := fifthRoot N
  have hltN : N < (u + 1) ^ 5 := (fifthRoot_spec N).2
  have hu2149 : 2149 ≤ u := by_contra fun hlt => by
    have := Nat.pow_le_pow_left (show u + 1 ≤ 2149 by omega) 5; omega
  have hlt : 2148 * u ^ 4 < u ^ 5 :=
    calc 2148 * u ^ 4
        < 2149 * u ^ 4 := by
          nlinarith [Nat.pow_pos (by omega : 0 < u) (n := 4)]
      _ ≤ u * u ^ 4 := Nat.mul_le_mul_right _ hu2149
      _ = u ^ 5 := by ring
  exact hle.trans_lt (hlt.trans_le (fifthRoot_spec N).1)

end Cslib.AffineDisperser.Li
