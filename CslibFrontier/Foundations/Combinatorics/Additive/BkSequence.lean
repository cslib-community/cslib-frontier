/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Foundations.Data.ZMod.NatCast
import CslibFrontier.Foundations.NumberTheory.PrimeCounting
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.List.GetD
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic.Ring

/-!
# Explicit finite `B_k`-sequences

A subset `B` of a commutative additive monoid is a **`B_k`-set** (or `B_k`-sequence, also called a
Sidon set at `k = 2`) when every `k`-fold sum of elements of `B` determines its multiset of
summands (`Cslib.IsBkSet`). Any `B_k`-subset `B` of a finite commutative additive monoid `M`
satisfies `(|B| + k - 1).choose k ≤ |M|` (`Cslib.IsBkSet.choose_le_card`), giving
`(|B| + k - 1).choose k ≤ N` in `ZMod N`.

Following [Sergeev2023BkSequence], we construct an explicit size-`n` `B_k`-sequence `H[n, k]`
(`Cslib.sergeevBkSequence`) whose elements are bounded by `((n + 2) * (2 * ⌊log₂(n + 2)⌋ + 4)) ^ k`
(`= n ^ (k + o(k))`) and whose entries can be computed in time `(n + k) ^ O(1)` (certified in
`CslibFrontier.Computability.Complexity.BkSequencePolyTime`):

1. **2-adic unit decomposition and bit-by-bit discrete logarithm** (pp. 2–3): for `r ≥ 3`, every
   odd integer `x` has a unique representation `x ≡ (-1) ^ j · 5 ^ h (mod 2 ^ r)` with `j ∈ Fin 2`
   and `h < 2 ^ (r - 2)` (`Cslib.existsUnique_neg_one_pow_mul_five_pow_eq`). After normalizing `x`
   modulo `4`, the `r - 2` binary digits of `h` are extracted sequentially in the order-`2`
   subgroup `⟨5 ^ (2 ^ (r - 3))⟩ = {1, 2 ^ (r - 1) + 1}` (`Cslib.dlogFiveModTwoPow`,
   `Cslib.zmod_eq_neg_one_pow_mul_five_pow_dlogFiveModTwoPow`).
2. **Prime factor base and `B_k` correctness** (p. 2): taking `p₁ < ⋯ < pₙ` to be the first `n` odd
   primes (`Cslib.firstOddPrimes`, found below `Cslib.primeSearchBound n` via
   `Nat.le_card_primesLE_mul_log`) and `r = max 3 (1 + ⌈log₂(pₙ ^ k)⌉)`
   (`Cslib.sergeevModulusExp`), distinct `k`-multisets of odd primes have distinct products strictly
   below `2 ^ (r - 1)`. Hence any collision of `k`-sums modulo `2 ^ (r - 2)` would force `P ≡ ±Q
   (mod 2 ^ r)` with `0 < P, Q < 2 ^ (r - 1)`, forcing `P = Q` in `ℕ` and identical prime
   multisets (`Cslib.isBkSequence_map_zmod_sergeevBkSequence`,
   `Cslib.isBkSequence_sergeevBkSequence`).

## Main definitions

* `Cslib.IsBkSet`: `B_k`-sets in a commutative additive monoid (distinct `k`-multiset sums).
* `Cslib.IsBkSequence`: finite `B_k`-sequences (`List.Nodup` together with `IsBkSet` on entries).
* `Cslib.dlogFiveStep`, `Cslib.dlogFiveModTwoPow`: bit-by-bit discrete logarithm `log₅(±x)` modulo
  `2 ^ r`.
* `Cslib.primeSearchBound`, `Cslib.firstOddPrimes`: explicit search bound and list of the first `n`
  odd primes.
* `Cslib.sergeevModulusExp`, `Cslib.sergeevBkSequence`: modulus exponent `r` and Sergeev's explicit
  `B_k`-sequence `H[n, k]`.

## Main results

* `Cslib.IsBkSet.choose_le_card`: counting lower bound `(#B + k - 1).choose k ≤ Fintype.card M`.
* `Cslib.IsBkSet.of_injOn_map`, `Cslib.IsBkSequence.of_map`: homomorphic pullback of `B_k`-sets and
  `B_k`-sequences (modular lift from `ZMod m` to `ℕ`).
* `Cslib.dlogFiveModTwoPow_lt`, `Cslib.zmod_eq_neg_one_pow_mul_five_pow_dlogFiveModTwoPow`,
  `Cslib.existsUnique_neg_one_pow_mul_five_pow_eq`: range, correctness, and uniqueness of the
  `(-1) ^ j · 5 ^ h (mod 2 ^ r)` decomposition of odd residues for `r ≥ 3`.
* `Cslib.isBkSequence_map_zmod_sergeevBkSequence`, `Cslib.isBkSequence_sergeevBkSequence`:
  `sergeevBkSequence n k` is a `B_k`-sequence in `ZMod (2 ^ (r - 2))` and in `ℕ` for `1 ≤ k`.
* `Cslib.two_pow_sergeevModulusExp_sub_two_lt`, `Cslib.mem_sergeevBkSequence_lt`: explicit
  `((n + 2) * (2 * Nat.log 2 (n + 2) + 4)) ^ k` upper bound on `2 ^ (r - 2)` and on every element
  of `sergeevBkSequence n k`.

## References

* [I. S. Sergeev, *An Explicit Finite $B_k$-Sequence*][Sergeev2023BkSequence], arXiv:2304.03988v1,
  pp. 1–3.
-/

public section

namespace Cslib

open Finset

/-! ### `B_k`-sets and `B_k`-sequences -/

/-- A subset `B` of a commutative additive monoid is a **`B_k`-set** (or `B_k`-sequence; a Sidon
set when `k = 2`) if `k`-element sums from `B` uniquely determine their multiset of summands
([Sergeev2023BkSequence], p. 1). -/
@[expose] def IsBkSet {M : Type*} [AddCommMonoid M] (k : ℕ) (B : Set M) : Prop :=
  ∀ ⦃s t : Multiset M⦄,
    (∀ a ∈ s, a ∈ B) → (∀ b ∈ t, b ∈ B) → s.card = k → t.card = k → s.sum = t.sum → s = t

/-- A list `L` in a commutative additive monoid is a finite **`B_k`-sequence** if its entries are
pairwise distinct and form a `B_k`-set ([Sergeev2023BkSequence], p. 1). -/
@[expose] def IsBkSequence {M : Type*} [AddCommMonoid M] (k : ℕ) (L : List M) : Prop :=
  L.Nodup ∧ IsBkSet k {x | x ∈ L}

/-- Counting lower bound for finite `B_k`-sets ([Sergeev2023BkSequence], p. 1): the `k`-element
multisets drawn from `B` have pairwise distinct sums in `M`, so `(#B + k - 1).choose k ≤ |M|`.
Specializing `M = ZMod N` (`[NeZero N]`) gives `(#B + k - 1).choose k ≤ N`. -/
theorem IsBkSet.choose_le_card {M : Type*} [AddCommMonoid M] [Fintype M] {k : ℕ}
    {B : Finset M} (hB : IsBkSet k (B : Set M)) :
    (#B + k - 1).choose k ≤ Fintype.card M := by
  classical
  have hinj : Function.Injective (fun s : Sym ↥B k => ((s : Multiset ↥B).map Subtype.val).sum) := by
    intro s₁ s₂ hsum
    have heq : (s₁ : Multiset ↥B).map Subtype.val = (s₂ : Multiset ↥B).map Subtype.val := by
      apply hB
      · intro a ha
        obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp ha
        exact x.property
      · intro b hb
        obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp hb
        exact x.property
      · rw [Multiset.card_map, Sym.card_coe]
      · rw [Multiset.card_map, Sym.card_coe]
      · exact hsum
    exact Sym.ext (Multiset.map_injective Subtype.val_injective heq)
  simpa only [Sym.card_sym_eq_choose, Fintype.card_coe] using Fintype.card_le_of_injective _ hinj

/-- Pulling back a `B_k`-set along an additive monoid homomorphism that is injective on `B` yields
a `B_k`-set. -/
theorem IsBkSet.of_injOn_map {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    (φ : M →+ N) {k : ℕ} {B : Set M} (hinj : Set.InjOn φ B) (hB : IsBkSet k (φ '' B)) :
    IsBkSet k B := by
  intro s t hs ht hsc htc hsum
  have hmap : s.map φ = t.map φ := by
    apply hB
    · intro a' ha'
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp ha'
      exact ⟨a, hs a ha, rfl⟩
    · intro b' hb'
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp hb'
      exact ⟨b, ht b hb, rfl⟩
    · rw [Multiset.card_map, hsc]
    · rw [Multiset.card_map, htc]
    · rw [← map_multiset_sum, ← map_multiset_sum, hsum]
  let s' : Multiset B := s.pmap Subtype.mk hs
  let t' : Multiset B := t.pmap Subtype.mk ht
  have hu : Function.Injective (fun x : B => φ x.val) := fun x y hxy =>
    Subtype.ext (hinj x.property y.property hxy)
  have hs' : s'.map Subtype.val = s := by
    simp only [s', Multiset.map_pmap, Multiset.pmap_eq_map, Multiset.map_id']
  have ht' : t'.map Subtype.val = t := by
    simp only [t', Multiset.map_pmap, Multiset.pmap_eq_map, Multiset.map_id']
  have hst' : s' = t' := by
    apply Multiset.map_injective hu
    calc s'.map (fun x : B => φ x.val)
        = (s'.map Subtype.val).map φ := (Multiset.map_map φ Subtype.val s').symm
      _ = s.map φ := by rw [hs']
      _ = t.map φ := hmap
      _ = (t'.map Subtype.val).map φ := by rw [ht']
      _ = t'.map (fun x : B => φ x.val) := Multiset.map_map φ Subtype.val t'
  rw [← hs', ← ht', hst']

/-- If the homomorphic image `L.map φ` is a `B_k`-sequence, then `L` itself is a `B_k`-sequence
(since `(L.map φ).Nodup` already forces `φ` to be injective on the entries of `L`). -/
theorem IsBkSequence.of_map {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    (φ : M →+ N) {k : ℕ} {L : List M} (hL : IsBkSequence k (L.map φ)) :
    IsBkSequence k L := by
  refine ⟨hL.1.of_map φ, ?_⟩
  have hinj : Set.InjOn φ {x | x ∈ L} := by
    intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    have hij : i = j := (hL.1.getElem_inj_iff (hi := by simpa using hi)
      (hj := by simpa using hj)).mp (by simpa using hxy)
    subst hij
    rfl
  refine IsBkSet.of_injOn_map φ hinj ?_
  have himg : φ '' {x | x ∈ L} = {y | y ∈ L.map φ} := by
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_map]
  rw [himg]
  exact hL.2

/-! ### 2-adic unit decomposition and bit-by-bit discrete logarithm -/

/-- One bit-extraction step of Sergeev's base-`5` discrete logarithm modulo `2 ^ r`
([Sergeev2023BkSequence], p. 3): given `(r, x')`, accumulator `a < 2 ^ i` with
`x' ≡ 5 ^ a (mod 2 ^ (i + 2))`, and bit index `i < r - 2`, test whether
`(5 ^ (-a) * x') ^ (2 ^ (r - 3 - i)) ≡ 2 ^ (r - 1) + 1 (mod 2 ^ r)` in the order-`2` subgroup. -/
@[expose] def dlogFiveStep (r x' a i : ℕ) : ℕ :=
  if Nat.powMod (Nat.powMod 5 (2 ^ (r - 2) - a) (2 ^ r) * x' % 2 ^ r) (2 ^ (r - 3 - i)) (2 ^ r) =
      2 ^ (r - 1) + 1 then
    a + 2 ^ i
  else
    a

/-- Base-`5` discrete logarithm of `±x` modulo `2 ^ r` ([Sergeev2023BkSequence], pp. 2–3):
normalizes `x` modulo `4` so that odd inputs satisfy `x' ≡ 1 (mod 4)`, then extracts the `r - 2`
binary digits of `h < 2 ^ (r - 2)` sequentially. -/
@[expose] def dlogFiveModTwoPow (r x : ℕ) : ℕ :=
  let x' := if x % 4 = 1 then x % 2 ^ r else (2 ^ r - x % 2 ^ r) % 2 ^ r
  (List.range (r - 2)).foldl (dlogFiveStep r x') 0

private lemma exists_five_pow_two_pow_eq (m : ℕ) :
    ∃ y : ℕ, 5 ^ (2 ^ m) = 1 + 2 ^ (m + 2) * (1 + 2 * y) := by
  obtain ⟨y, hy⟩ := ZMod.exists_one_add_mul_pow_prime_pow_eq (R := ℕ) (u := 4) (v := 2)
    Nat.prime_two (by decide) (by decide) 1 m
  refine ⟨y, ?_⟩
  calc 5 ^ (2 ^ m) = (1 + 4 * 1) ^ (2 ^ m) := rfl
    _ = 1 + 2 ^ m * 4 * (1 + 2 * y) := hy
    _ = 1 + 2 ^ (m + 2) * (1 + 2 * y) := by ring

private lemma orderOf_five_zmod_two_pow {r : ℕ} (hr : 2 ≤ r) :
    orderOf (5 : ZMod (2 ^ r)) = 2 ^ (r - 2) := by
  have hord := ZMod.orderOf_five (r - 2)
  rwa [Nat.sub_add_cancel hr] at hord

private lemma five_pow_two_pow_sub_two_zmod {r : ℕ} (hr : 2 ≤ r) :
    (5 : ZMod (2 ^ r)) ^ (2 ^ (r - 2)) = 1 := by
  rw [← orderOf_five_zmod_two_pow hr, pow_orderOf_eq_one]

/-- After `j ≤ m` bit-extraction steps over `List.range m`, the base-`5` discrete-logarithm
accumulator is strictly less than `2 ^ j`. -/
theorem foldl_dlogFiveStep_take_lt (r x' m j : ℕ) (hj : j ≤ m) :
    ((List.range m).take j).foldl (dlogFiveStep r x') 0 < 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj' : j < m := Nat.lt_of_succ_le hj
    have htake : (List.range m).take (j + 1) = (List.range m).take j ++ [j] := by
      rw [List.take_add_one, List.getElem?_range hj', Option.toList_some]
    rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hprev := ih hj'.le
    dsimp only [dlogFiveStep]
    split_ifs <;> rw [Nat.pow_succ] <;> omega

/-- `dlogFiveModTwoPow r x` always lies strictly below `2 ^ (r - 2)`. -/
theorem dlogFiveModTwoPow_lt (r x : ℕ) :
    dlogFiveModTwoPow r x < 2 ^ (r - 2) := by
  have h := foldl_dlogFiveStep_take_lt r
    (if x % 4 = 1 then x % 2 ^ r else (2 ^ r - x % 2 ^ r) % 2 ^ r) (r - 2) (r - 2) le_rfl
  have htake : (List.range (r - 2)).take (r - 2) = List.range (r - 2) := by simp
  rwa [htake] at h

private lemma dlogFiveStep_preserves {r x' a i : ℕ} (hr : 3 ≤ r) (hi : i < r - 2) (ha : a < 2 ^ i)
    (hcong : (x' : ZMod (2 ^ (i + 2))) = (5 : ZMod (2 ^ (i + 2))) ^ a) :
    dlogFiveStep r x' a i < 2 ^ (i + 1) ∧
      (x' : ZMod (2 ^ (i + 3))) = (5 : ZMod (2 ^ (i + 3))) ^ dlogFiveStep r x' a i := by
  have ha_lt : a < 2 ^ (r - 2) := ha.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  set w := 5 ^ (2 ^ (r - 2) - a) % 2 ^ r * x' % 2 ^ r
  -- `w ≡ 5 ^ (-a) * x' (mod 2 ^ k)` for every `k ≤ r`.
  have hw_zmod (k : ℕ) (hk : k ≤ r) :
      (w : ZMod (2 ^ k)) * (5 : ZMod (2 ^ k)) ^ a = (x' : ZMod (2 ^ k)) := by
    have hdvd : 2 ^ k ∣ 2 ^ r := Nat.pow_dvd_pow 2 hk
    have hwr : (w : ZMod (2 ^ r)) * (5 : ZMod (2 ^ r)) ^ a = (x' : ZMod (2 ^ r)) := by
      simp only [w, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel ha_lt.le,
        five_pow_two_pow_sub_two_zmod (by omega), one_mul]
    simpa only [map_mul, map_pow, map_ofNat, ZMod.castHom_apply, ZMod.cast_natCast hdvd]
      using congrArg (ZMod.castHom hdvd (ZMod (2 ^ k))) hwr
  have hw_mod_i2 : w % 2 ^ (i + 2) = 1 := by
    have hunit : IsUnit ((5 : ZMod (2 ^ (i + 2))) ^ a) :=
      ((ZMod.isUnit_iff_coprime 5 _).mpr ((by decide : Nat.Coprime 5 2).pow_right _)).pow a
    have hw1 : (w : ZMod (2 ^ (i + 2))) = ((1 : ℕ) : ZMod (2 ^ (i + 2))) :=
      hunit.mul_right_cancel (by rw [hw_zmod (i + 2) (by omega), hcong, Nat.cast_one, one_mul])
    exact ((ZMod.natCast_eq_natCast_iff' w 1 _).mp hw1).trans
      (Nat.mod_eq_of_lt (one_lt_pow₀ (by decide) (by omega)))
  obtain ⟨q, hw_decomp⟩ : ∃ q, w = 1 + 2 ^ (i + 2) * q :=
    ⟨w / 2 ^ (i + 2), by have := Nat.div_add_mod w (2 ^ (i + 2)); omega⟩
  obtain ⟨y, hy⟩ := ZMod.exists_one_add_mul_pow_prime_pow_eq (R := ℕ) (u := 2 ^ (i + 2)) (v := 2)
    Nat.prime_two (dvd_pow_self 2 (by omega))
    (show 2 * 2 ^ (i + 2) * 2 ∣ (2 ^ (i + 2)) ^ 2 from ⟨2 ^ i, by ring⟩) q (r - 3 - i)
  have hpow_eq : w ^ (2 ^ (r - 3 - i)) = 1 + 2 ^ (r - 1) * (q + 2 * y) := by
    rw [hw_decomp, hy, Nat.cast_id, ← pow_add, show r - 3 - i + (i + 2) = r - 1 by omega]
  have h2r_split : 2 ^ r = 2 * 2 ^ (r - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ r)]
  have h1lt_half : 1 < 2 ^ (r - 1) := one_lt_pow₀ (by decide) (by omega)
  -- The bit `q % 2` decides whether `w ≡ 1` or `w ≡ 5 ^ (2 ^ i) (mod 2 ^ (i + 3))`.
  have h0 : (2 : ZMod (2 ^ (i + 3))) ^ (i + 3) = 0 := by
    exact_mod_cast ZMod.natCast_self (2 ^ (i + 3))
  have hwR : (w : ZMod (2 ^ (i + 3))) = 1 + 2 ^ (i + 2) * q := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ZMod (2 ^ (i + 3))) hw_decomp
  rw [← hw_zmod (i + 3) (by omega), hwR]
  rcases Nat.even_or_odd q with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · have hne : w ^ (2 ^ (r - 3 - i)) % 2 ^ r ≠ 2 ^ (r - 1) + 1 := by
      rw [hpow_eq, h2r_split, show 1 + 2 ^ (r - 1) * (s + s + 2 * y) =
        1 + 2 * 2 ^ (r - 1) * (s + y) by ring, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega)]
      omega
    have hstep : dlogFiveStep r x' a i = a := by
      simp only [dlogFiveStep, Nat.powMod_def, w, hne, ↓reduceIte]
    refine ⟨by rw [hstep, Nat.pow_succ]; omega, ?_⟩
    rw [hstep]
    push_cast
    linear_combination (5 : ZMod (2 ^ (i + 3))) ^ a * s * h0
  · have hu_mod : w ^ (2 ^ (r - 3 - i)) % 2 ^ r = 2 ^ (r - 1) + 1 := by
      rw [hpow_eq, h2r_split, show 1 + 2 ^ (r - 1) * (2 * s + 1 + 2 * y) =
        (2 ^ (r - 1) + 1) + 2 * 2 ^ (r - 1) * (s + y) by ring, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega)]
    have hstep : dlogFiveStep r x' a i = a + 2 ^ i := by
      simp only [dlogFiveStep, Nat.powMod_def, w, hu_mod, ↓reduceIte]
    refine ⟨by rw [hstep, Nat.pow_succ]; omega, ?_⟩
    obtain ⟨y', hy'⟩ := exists_five_pow_two_pow_eq i
    have h5 : (5 : ZMod (2 ^ (i + 3))) ^ 2 ^ i = 1 + 2 ^ (i + 2) * (1 + 2 * y') := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod (2 ^ (i + 3))) hy'
    rw [hstep, pow_add (5 : ZMod (2 ^ (i + 3))) a (2 ^ i), h5]
    push_cast
    linear_combination (5 : ZMod (2 ^ (i + 3))) ^ a * (s - y') * h0

private lemma foldl_dlogFiveStep_spec {r x' : ℕ} (hr : 3 ≤ r)
    (hx' : (x' : ZMod 4) = 1) (j : ℕ) (hj : j ≤ r - 2) :
    ((List.range (r - 2)).take j).foldl (dlogFiveStep r x') 0 < 2 ^ j ∧
      (x' : ZMod (2 ^ (j + 2))) =
        (5 : ZMod (2 ^ (j + 2))) ^ (((List.range (r - 2)).take j).foldl (dlogFiveStep r x') 0) := by
  induction j with
  | zero =>
    simpa only [List.take_zero, List.foldl_nil, Nat.zero_add, pow_zero, show 2 ^ 2 = 4 from rfl]
      using And.intro Nat.one_pos hx'
  | succ j ih =>
    have hj_lt : j < r - 2 := Nat.lt_of_succ_le hj
    obtain ⟨hlt, hcong⟩ := ih hj_lt.le
    have htake : (List.range (r - 2)).take (j + 1) = (List.range (r - 2)).take j ++ [j] := by
      rw [List.take_add_one, List.getElem?_range hj_lt, Option.toList_some]
    rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact dlogFiveStep_preserves hr hj_lt hlt hcong

/-- Correctness of Sergeev's bit-by-bit discrete logarithm ([Sergeev2023BkSequence], pp. 2–3):
for `r ≥ 3` and odd `x`, `x ≡ (-1) ^ j · 5 ^ (dlogFiveModTwoPow r x) (mod 2 ^ r)` where
`j = 0` when `x % 4 = 1` and `j = 1` when `x % 4 = 3`. -/
theorem zmod_eq_neg_one_pow_mul_five_pow_dlogFiveModTwoPow {r x : ℕ} (hr : 3 ≤ r) (hx : Odd x) :
    (x : ZMod (2 ^ r)) =
      (-1 : ZMod (2 ^ r)) ^ (if x % 4 = 1 then 0 else 1) *
        (5 : ZMod (2 ^ r)) ^ dlogFiveModTwoPow r x := by
  set x' := if x % 4 = 1 then x % 2 ^ r else (2 ^ r - x % 2 ^ r) % 2 ^ r
  have : NeZero (2 ^ r) := ⟨(Nat.two_pow_pos r).ne'⟩
  have h4dvd : 4 ∣ 2 ^ r := Nat.pow_dvd_pow 2 (by omega : 2 ≤ r)
  have hx_mod4 : x % 4 = 1 ∨ x % 4 = 3 := by have := Nat.odd_iff.mp hx; omega
  have hx'_cast : (x' : ZMod (2 ^ r)) =
      (-1 : ZMod (2 ^ r)) ^ (if x % 4 = 1 then 0 else 1) * (x : ZMod (2 ^ r)) := by
    rcases hx_mod4 with h1 | h3
    · simp only [x', h1, ↓reduceIte, ZMod.natCast_mod, pow_zero, one_mul]
    · simp only [x', show x % 4 ≠ 1 by omega, ↓reduceIte, ZMod.natCast_mod,
        ZMod.natCast_sub_mod_eq_neg, pow_one, neg_one_mul]
  have hx'_mod4 : (x' : ZMod 4) = 1 := by
    have hmap := congrArg (ZMod.castHom h4dvd (ZMod 4)) hx'_cast
    simp only [map_mul, map_pow, map_neg, map_one, ZMod.castHom_apply,
      ZMod.cast_natCast h4dvd] at hmap
    rw [hmap, ← ZMod.natCast_mod x 4]
    rcases hx_mod4 with h | h <;> rw [h] <;> decide
  have hdlog : (x' : ZMod (2 ^ r)) = (5 : ZMod (2 ^ r)) ^ dlogFiveModTwoPow r x := by
    have hfold := (foldl_dlogFiveStep_spec hr hx'_mod4 (r - 2) le_rfl).2
    rwa [show (List.range (r - 2)).take (r - 2) = List.range (r - 2) by simp,
      Nat.sub_add_cancel (by omega : 2 ≤ r)] at hfold
  rw [← hdlog, hx'_cast, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

/-- Unique `(-1) ^ j · 5 ^ h` representation of odd residues modulo `2 ^ r` for `r ≥ 3`
([Sergeev2023BkSequence], p. 2): every odd integer `x` has a unique pair
`(j, h) : Fin 2 × Fin (2 ^ (r - 2))` with `x ≡ (-1) ^ j · 5 ^ h (mod 2 ^ r)`. -/
theorem existsUnique_neg_one_pow_mul_five_pow_eq {r x : ℕ} (hr : 3 ≤ r) (hx : Odd x) :
    ∃! p : Fin 2 × Fin (2 ^ (r - 2)),
      (x : ZMod (2 ^ r)) = (-1) ^ (p.1 : ℕ) * (5 : ZMod (2 ^ r)) ^ (p.2 : ℕ) := by
  let j₀ : Fin 2 := if x % 4 = 1 then 0 else 1
  let h₀ : Fin (2 ^ (r - 2)) := ⟨dlogFiveModTwoPow r x, dlogFiveModTwoPow_lt r x⟩
  have hex : (x : ZMod (2 ^ r)) = (-1) ^ (j₀ : ℕ) * (5 : ZMod (2 ^ r)) ^ (h₀ : ℕ) := by
    rw [show (j₀ : ℕ) = if x % 4 = 1 then 0 else 1 by dsimp only [j₀]; split_ifs <;> rfl]
    exact zmod_eq_neg_one_pow_mul_five_pow_dlogFiveModTwoPow hr hx
  refine ⟨(j₀, h₀), hex, ?_⟩
  rintro ⟨j, h⟩ hjh
  have heq : (-1 : ZMod (2 ^ r)) ^ (j : ℕ) * (5 : ZMod (2 ^ r)) ^ (h : ℕ) =
      (-1 : ZMod (2 ^ r)) ^ (j₀ : ℕ) * (5 : ZMod (2 ^ r)) ^ (h₀ : ℕ) := hjh.symm.trans hex
  have h4dvd : 4 ∣ 2 ^ r := Nat.pow_dvd_pow 2 (by omega : 2 ≤ r)
  have hj_eq : j = j₀ := by
    have hmap := congrArg (ZMod.castHom h4dvd (ZMod 4)) heq
    simp only [map_mul, map_pow, map_neg, map_one, map_ofNat, show (5 : ZMod 4) = 1 by decide,
      one_pow, mul_one] at hmap
    have hfin2 : ∀ a b : Fin 2, (-1 : ZMod 4) ^ (a : ℕ) = (-1 : ZMod 4) ^ (b : ℕ) → a = b := by
      decide
    exact hfin2 j j₀ hmap
  subst hj_eq
  have hpow_eq : (5 : ZMod (2 ^ r)) ^ (h : ℕ) = (5 : ZMod (2 ^ r)) ^ (h₀ : ℕ) :=
    (isUnit_one.neg.pow _).mul_left_cancel heq
  have hord := orderOf_five_zmod_two_pow (by omega : 2 ≤ r)
  have hh_eq : (h : ℕ) = (h₀ : ℕ) :=
    pow_injOn_Iio_orderOf (x := (5 : ZMod (2 ^ r))) (by rw [Set.mem_Iio, hord]; exact h.isLt)
      (by rw [Set.mem_Iio, hord]; exact h₀.isLt) hpow_eq
  exact Prod.ext rfl (Fin.ext hh_eq)

/-! ### Prime factor base -/

/-- Upper bound `(n + 2) * (2 * ⌊log₂(n + 2)⌋ + 4)` guaranteed by `Nat.le_card_primesLE_mul_log`
to exceed at least `n + 1` primes (and hence at least `n` odd primes). -/
@[expose] def primeSearchBound (n : ℕ) : ℕ :=
  (n + 2) * (2 * Nat.log 2 (n + 2) + 4)

/-- The first `n` odd prime numbers in strictly increasing order. -/
@[expose] def firstOddPrimes (n : ℕ) : List ℕ :=
  ((List.range (primeSearchBound n + 1)).filter fun p => decide (2 < p) && decide p.Prime).take n

/-- `firstOddPrimes n` has length `n` for every `n`. -/
@[simp]
theorem length_firstOddPrimes (n : ℕ) : (firstOddPrimes n).length = n := by
  set M := primeSearchBound n
  set cand := (List.range (M + 1)).filter fun p => decide (2 < p) && decide p.Prime
  have hnodup : cand.Nodup := List.nodup_range.filter _
  let oddSet : Finset ℕ := (Finset.range (M + 1)).filter fun p => 2 < p ∧ p.Prime
  have hsub : Nat.primesLE M ⊆ insert 2 oddSet := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    rcases eq_or_lt_of_le hp.2.two_le with rfl | h2lt
    · exact Finset.mem_insert_self 2 oddSet
    · exact Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h2lt, hp.2⟩)
  have hcard_le : n + 1 ≤ #oddSet + 1 := by
    calc n + 1 ≤ #(Nat.primesLE M) := Nat.le_card_primesLE_mul_log (n + 1)
      _ ≤ #(insert 2 oddSet) := Finset.card_le_card hsub
      _ ≤ #oddSet + 1 := Finset.card_insert_le 2 oddSet
  have htoFinset : cand.toFinset = oddSet := by
    ext p
    simp only [cand, oddSet, List.mem_toFinset, List.mem_filter, List.mem_range, Bool.and_eq_true,
      decide_eq_true_eq, Finset.mem_filter, Finset.mem_range]
  have hlen : n ≤ cand.length := by
    rw [← List.toFinset_card_of_nodup hnodup, htoFinset]
    omega
  exact List.length_take_of_le hlen

/-- `firstOddPrimes n` is strictly increasing. -/
theorem pairwise_lt_firstOddPrimes (n : ℕ) : (firstOddPrimes n).Pairwise (· < ·) :=
  (List.pairwise_lt_range.filter _).take

/-- Every entry of `firstOddPrimes n` is an odd prime (`p.Prime ∧ 2 < p`). -/
theorem prime_and_two_lt_of_mem_firstOddPrimes {n p : ℕ} (hp : p ∈ firstOddPrimes n) :
    p.Prime ∧ 2 < p := by
  have hmem := List.mem_of_mem_take hp
  simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hmem
  exact ⟨hmem.2.2, hmem.2.1⟩

/-- Every entry of `firstOddPrimes n` is bounded by `primeSearchBound n`. -/
theorem le_primeSearchBound_of_mem_firstOddPrimes {n p : ℕ} (hp : p ∈ firstOddPrimes n) :
    p ≤ primeSearchBound n := by
  have hmem := List.mem_of_mem_take hp
  simp only [List.mem_filter, List.mem_range] at hmem
  exact Nat.lt_succ_iff.mp hmem.1

/-! ### Sergeev's `H[n, k]` construction, correctness, and density -/

/-- Modulus exponent `r = max 3 (1 + ⌈log₂(pₙ ^ k)⌉)` of Sergeev's construction
([Sergeev2023BkSequence], p. 2), using default base `3` when `n = 0`. -/
@[expose] def sergeevModulusExp (n k : ℕ) : ℕ :=
  max 3 (1 + Nat.clog 2 (((firstOddPrimes n).getD (n - 1) 3) ^ k))

/-- **Sergeev's explicit `B_k`-sequence `H[n, k]`** ([Sergeev2023BkSequence], p. 2): the base-`5`
discrete logarithms modulo `2 ^ r` of the first `n` odd primes. -/
@[expose] def sergeevBkSequence (n k : ℕ) : List ℕ :=
  let r := sergeevModulusExp n k
  (firstOddPrimes n).map (dlogFiveModTwoPow r)

/-- `sergeevBkSequence n k` has length `n`. -/
@[simp]
theorem length_sergeevBkSequence (n k : ℕ) : (sergeevBkSequence n k).length = n := by
  simp only [sergeevBkSequence, List.length_map, length_firstOddPrimes]

/-- Every element of `sergeevBkSequence n k` is strictly less than
`2 ^ (sergeevModulusExp n k - 2)`. -/
theorem mem_sergeevBkSequence_lt_two_pow (n k : ℕ) {h : ℕ} (hh : h ∈ sergeevBkSequence n k) :
    h < 2 ^ (sergeevModulusExp n k - 2) := by
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hh
  exact dlogFiveModTwoPow_lt (sergeevModulusExp n k) p

private lemma lastPrime_properties (n : ℕ) :
    let pLast := (firstOddPrimes n).getD (n - 1) 3
    2 < pLast ∧ Odd pLast ∧ pLast ≤ primeSearchBound n ∧
      ∀ p ∈ firstOddPrimes n, p ≤ pLast := by
  intro pLast
  rcases n.eq_zero_or_pos with rfl | hn
  · have hp0 : pLast = 3 := by
      simp only [pLast, firstOddPrimes, List.take_zero, Nat.zero_sub, List.getD_nil]
    rw [hp0]
    refine ⟨by decide, by decide, ?_, ?_⟩
    · simp only [primeSearchBound]
      omega
    · intro p hp
      simp only [firstOddPrimes, List.take_zero, List.not_mem_nil] at hp
  · have hlen : (firstOddPrimes n).length = n := length_firstOddPrimes n
    have hidx : n - 1 < (firstOddPrimes n).length := by omega
    have hp_eq : pLast = (firstOddPrimes n)[n - 1] := List.getD_eq_getElem _ _ hidx
    have hp_mem : pLast ∈ firstOddPrimes n := hp_eq ▸ List.getElem_mem hidx
    obtain ⟨hprime, h2lt⟩ := prime_and_two_lt_of_mem_firstOddPrimes hp_mem
    refine ⟨h2lt, hprime.odd_of_ne_two (by omega), le_primeSearchBound_of_mem_firstOddPrimes hp_mem,
      ?_⟩
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    rw [hp_eq]
    rcases eq_or_lt_of_le (by omega : i ≤ n - 1) with rfl | hilt
    · exact le_rfl
    · exact (List.pairwise_iff_getElem.mp (pairwise_lt_firstOddPrimes n) i (n - 1) hi hidx hilt).le

private lemma sergeevModulusExp_bounds (n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    let pLast := (firstOddPrimes n).getD (n - 1) 3
    let r := sergeevModulusExp n k
    3 ≤ r ∧ pLast ^ k < 2 ^ (r - 1) ∧ 2 ^ (r - 2) < pLast ^ k := by
  intro pLast r
  obtain ⟨h2lt, hodd, _, _⟩ := lastPrime_properties n
  have h2lt_pow : 2 < pLast ^ k := lt_of_lt_of_le h2lt (Nat.le_self_pow (by omega) pLast)
  have h1lt_clog : 1 < Nat.clog 2 (pLast ^ k) :=
    (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by simpa only [pow_one] using h2lt_pow)
  have hr_eq : r = 1 + Nat.clog 2 (pLast ^ k) := by
    change sergeevModulusExp n k = 1 + Nat.clog 2 (((firstOddPrimes n).getD (n - 1) 3) ^ k)
    unfold sergeevModulusExp
    dsimp only [pLast] at h1lt_clog
    exact max_eq_right (by omega)
  have hr3 : 3 ≤ r := by omega
  have hr1 : r - 1 = Nat.clog 2 (pLast ^ k) := by omega
  have hr2 : r - 2 = Nat.clog 2 (pLast ^ k) - 1 := by omega
  have hpow_le : pLast ^ k ≤ 2 ^ (r - 1) := by
    rw [hr1]
    exact Nat.le_pow_clog (by decide) _
  have hpow_ne : pLast ^ k ≠ 2 ^ (r - 1) := by
    intro heq
    have hodd_pow : Odd (pLast ^ k) := hodd.pow
    have heven_pow : Even (2 ^ (r - 1)) := Even.pow_of_ne_zero even_two (by omega)
    exact (Nat.not_even_iff_odd.mpr hodd_pow) (heq ▸ heven_pow)
  have hlt_pow : 2 ^ (r - 2) < pLast ^ k := by
    rw [hr2]
    exact (Nat.lt_clog_iff_pow_lt (by decide)).mp (by omega)
  exact ⟨hr3, lt_of_le_of_ne hpow_le hpow_ne, hlt_pow⟩

/-- Explicit upper bound on the modulus `2 ^ (r - 2)` of Sergeev's `B_k`-sequence
([Sergeev2023BkSequence], p. 2): `2 ^ (r - 2) < pₙ ^ k ≤ ((n + 2) * (2 * ⌊log₂(n + 2)⌋ + 4)) ^ k`
for all `n` and `1 ≤ k`. -/
theorem two_pow_sergeevModulusExp_sub_two_lt (n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    2 ^ (sergeevModulusExp n k - 2) < ((n + 2) * (2 * Nat.log 2 (n + 2) + 4)) ^ k := by
  obtain ⟨_, _, hlt⟩ := sergeevModulusExp_bounds n hk
  obtain ⟨_, _, hle, _⟩ := lastPrime_properties n
  exact hlt.trans_le (Nat.pow_le_pow_left hle k)

/-- Every element of `sergeevBkSequence n k` (`1 ≤ k`) is strictly bounded by
`((n + 2) * (2 * Nat.log 2 (n + 2) + 4)) ^ k` (`= n ^ (k + o(k))`, [Sergeev2023BkSequence],
Abstract and p. 2). -/
theorem mem_sergeevBkSequence_lt (n : ℕ) {k : ℕ} (hk : 1 ≤ k) {h : ℕ}
    (hh : h ∈ sergeevBkSequence n k) :
    h < ((n + 2) * (2 * Nat.log 2 (n + 2) + 4)) ^ k :=
  (mem_sergeevBkSequence_lt_two_pow n k hh).trans (two_pow_sergeevModulusExp_sub_two_lt n hk)

private lemma multiset_primes_eq_of_dlog_sum_zmod_eq {n k : ℕ} (hk : 1 ≤ k)
    {s t : Multiset ℕ} (hs : ∀ p ∈ s, p ∈ firstOddPrimes n) (ht : ∀ q ∈ t, q ∈ firstOddPrimes n)
    (hsc : s.card = k) (htc : t.card = k)
    (hsum : ((s.map (dlogFiveModTwoPow (sergeevModulusExp n k))).sum :
        ZMod (2 ^ (sergeevModulusExp n k - 2))) =
      ((t.map (dlogFiveModTwoPow (sergeevModulusExp n k))).sum :
        ZMod (2 ^ (sergeevModulusExp n k - 2)))) :
    s = t := by
  set r := sergeevModulusExp n k
  set pLast := (firstOddPrimes n).getD (n - 1) 3
  obtain ⟨hr3, hpLast_pow_lt, _⟩ := sergeevModulusExp_bounds n hk
  obtain ⟨_, _, _, hle_pLast⟩ := lastPrime_properties n
  set S := (s.map (dlogFiveModTwoPow r)).sum
  set T := (t.map (dlogFiveModTwoPow r)).sum
  have hmod_ST : S % 2 ^ (r - 2) = T % 2 ^ (r - 2) :=
    (ZMod.natCast_eq_natCast_iff' S T (2 ^ (r - 2))).mp hsum
  have hord := orderOf_five_zmod_two_pow (by omega : 2 ≤ r)
  have h5_ST : (5 : ZMod (2 ^ r)) ^ S = (5 : ZMod (2 ^ r)) ^ T := by
    rw [← pow_mod_orderOf (x := (5 : ZMod (2 ^ r))) S,
      ← pow_mod_orderOf (x := (5 : ZMod (2 ^ r))) T, hord, hmod_ST]
  let sgn : ℕ → ℕ := fun p => if p % 4 = 1 then 0 else 1
  have hprod_dlog : ∀ {u : Multiset ℕ}, (∀ p ∈ u, p ∈ firstOddPrimes n) →
      (u.prod : ZMod (2 ^ r)) =
        (-1 : ZMod (2 ^ r)) ^ (u.map sgn).sum *
          (5 : ZMod (2 ^ r)) ^ (u.map (dlogFiveModTwoPow r)).sum := by
    intro u hu
    induction u using Multiset.induction_on with
    | empty => simp
    | @cons p u ih =>
      have hp_mem := hu p (Multiset.mem_cons_self p u)
      obtain ⟨hp_prime, hp_gt2⟩ := prime_and_two_lt_of_mem_firstOddPrimes hp_mem
      have hp_odd : Odd p := hp_prime.odd_of_ne_two (by omega)
      have hp_eq := zmod_eq_neg_one_pow_mul_five_pow_dlogFiveModTwoPow hr3 hp_odd
      rw [Multiset.prod_cons, Nat.cast_mul, ih (fun q hq => hu q (Multiset.mem_cons_of_mem hq)),
        hp_eq, Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons,
        pow_add, pow_add]
      dsimp only [sgn]
      ring
  have hs_zmod := hprod_dlog hs
  have ht_zmod := hprod_dlog ht
  have hpm_prod : (s.prod : ZMod (2 ^ r)) = (t.prod : ZMod (2 ^ r)) ∨
      ((s.prod + t.prod : ℕ) : ZMod (2 ^ r)) = 0 := by
    rw [Nat.cast_add, hs_zmod, ht_zmod, h5_ST]
    rcases neg_one_pow_eq_or (ZMod (2 ^ r)) (s.map sgn).sum with h1 | h1 <;>
      rcases neg_one_pow_eq_or (ZMod (2 ^ r)) (t.map sgn).sum with h2 | h2 <;> rw [h1, h2] <;>
      first | exact Or.inl rfl | (right; ring)
  have hpos {u : Multiset ℕ} (hu : ∀ p ∈ u, p ∈ firstOddPrimes n) : 0 < u.prod :=
    Multiset.prod_pos fun p hp => (prime_and_two_lt_of_mem_firstOddPrimes (hu p hp)).1.pos
  have hlt {u : Multiset ℕ} (hu : ∀ p ∈ u, p ∈ firstOddPrimes n) (huc : u.card = k) :
      u.prod < 2 ^ (r - 1) :=
    (Multiset.prod_le_pow_card u pLast fun p hp => hle_pLast p (hu p hp)).trans_lt
      (huc ▸ hpLast_pow_lt)
  have hs_pos := hpos hs
  have ht_pos := hpos ht
  have hs_lt := hlt hs hsc
  have ht_lt := hlt ht htc
  have h2r_split : 2 ^ r = 2 ^ (r - 1) + 2 ^ (r - 1) := by
    rw [← two_mul, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ r)]
  have hprod_eq : s.prod = t.prod := by
    rcases hpm_prod with heq | hsum0
    · have hmod := (ZMod.natCast_eq_natCast_iff' s.prod t.prod (2 ^ r)).mp heq
      rwa [Nat.mod_eq_of_lt (by omega : s.prod < 2 ^ r),
        Nat.mod_eq_of_lt (by omega : t.prod < 2 ^ r)] at hmod
    · exfalso
      have hdvd : 2 ^ r ∣ s.prod + t.prod := (ZMod.natCast_eq_zero_iff _ _).mp hsum0
      have hle := Nat.le_of_dvd (by omega) hdvd
      omega
  rw [← Nat.factors_multiset_prod_of_irreducible
      (fun p hp => (prime_and_two_lt_of_mem_firstOddPrimes (hs p hp)).1),
    ← Nat.factors_multiset_prod_of_irreducible
      (fun q hq => (prime_and_two_lt_of_mem_firstOddPrimes (ht q hq)).1),
    hprod_eq]

/-- **Sergeev's modular `B_k`-sequence theorem** ([Sergeev2023BkSequence], p. 2): for every `n`
and `1 ≤ k`, the residues of `sergeevBkSequence n k` form a size-`n` `B_k`-sequence in
`ZMod (2 ^ (sergeevModulusExp n k - 2))`. -/
theorem isBkSequence_map_zmod_sergeevBkSequence (n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    IsBkSequence k ((sergeevBkSequence n k).map
      (Nat.cast : ℕ → ZMod (2 ^ (sergeevModulusExp n k - 2)))) := by
  set r := sergeevModulusExp n k
  set f : ℕ → ZMod (2 ^ (r - 2)) := fun p => (dlogFiveModTwoPow r p : ZMod (2 ^ (r - 2)))
  have hmap_eq : (sergeevBkSequence n k).map (Nat.cast : ℕ → ZMod (2 ^ (r - 2))) =
      (firstOddPrimes n).map f := by
    simp only [sergeevBkSequence, List.map_map, Function.comp_def, r, f]
  rw [hmap_eq]
  refine ⟨?_, ?_⟩
  · rw [List.nodup_map_iff_inj_on (pairwise_lt_firstOddPrimes n).nodup]
    intro p hp q hq hpq
    let sp : Multiset ℕ := p ::ₘ Multiset.replicate (k - 1) p
    let sq : Multiset ℕ := q ::ₘ Multiset.replicate (k - 1) p
    have hrep : ∀ x ∈ Multiset.replicate (k - 1) p, x ∈ firstOddPrimes n :=
      fun x hx => (Multiset.eq_of_mem_replicate hx).symm ▸ hp
    have hsp_eq_sq : sp = sq := by
      refine multiset_primes_eq_of_dlog_sum_zmod_eq hk (Multiset.forall_mem_cons.mpr ⟨hp, hrep⟩)
        (Multiset.forall_mem_cons.mpr ⟨hq, hrep⟩)
        (by simp only [sp, Multiset.card_cons, Multiset.card_replicate]; omega)
        (by simp only [sq, Multiset.card_cons, Multiset.card_replicate]; omega) ?_
      simp only [sp, sq, Multiset.map_cons, Multiset.sum_cons, Nat.cast_add]
      exact congrArg (· + ((Multiset.map (dlogFiveModTwoPow r)
        (Multiset.replicate (k - 1) p)).sum : ZMod (2 ^ (r - 2)))) hpq
    rcases Multiset.mem_cons.mp (hsp_eq_sq ▸ Multiset.mem_cons_self q _ : q ∈ sp) with hqp | hq_rep
    · exact hqp.symm
    · exact (Multiset.eq_of_mem_replicate hq_rep).symm
  · intro u v hu hv huc hvc hsum
    have hex_pre : ∀ z : {z : ZMod (2 ^ (r - 2)) // z ∈ (firstOddPrimes n).map f},
        ∃ p ∈ firstOddPrimes n, f p = z.val := fun z => List.mem_map.mp z.property
    choose pre hpre_mem hpre_eq using hex_pre
    have hmap_pre : ∀ (w : Multiset (ZMod (2 ^ (r - 2))))
        (hw : ∀ z ∈ w, z ∈ (firstOddPrimes n).map f),
        ((w.pmap Subtype.mk hw).map pre).map f = w := fun w hw => by
      simp only [hpre_eq, Multiset.map_pmap, Multiset.pmap_eq_map, Multiset.map_id']
    let s : Multiset ℕ := (u.pmap Subtype.mk hu).map pre
    let t : Multiset ℕ := (v.pmap Subtype.mk hv).map pre
    have hs_f : s.map f = u := hmap_pre u hu
    have ht_f : t.map f = v := hmap_pre v hv
    have hst : s = t := by
      refine multiset_primes_eq_of_dlog_sum_zmod_eq hk
        (Multiset.forall_mem_map_iff.mpr fun z _ => hpre_mem z)
        (Multiset.forall_mem_map_iff.mpr fun z _ => hpre_mem z)
        (by simp only [s, Multiset.card_map, Multiset.card_pmap, huc])
        (by simp only [t, Multiset.card_map, Multiset.card_pmap, hvc]) ?_
      · have hcast_sum : ∀ w : Multiset ℕ,
            ((w.map (dlogFiveModTwoPow r)).sum : ZMod (2 ^ (r - 2))) = (w.map f).sum := by
          intro w
          rw [Nat.cast_multiset_sum, Multiset.map_map]
          rfl
        rw [hcast_sum s, hcast_sum t, hs_f, ht_f, hsum]
    rw [← hs_f, ← ht_f, hst]

/-- **Sergeev's integer `B_k`-sequence theorem** ([Sergeev2023BkSequence], Abstract and p. 2):
for every `n` and `1 ≤ k`, `sergeevBkSequence n k` is a size-`n` `B_k`-sequence in `ℕ`. -/
theorem isBkSequence_sergeevBkSequence (n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    IsBkSequence k (sergeevBkSequence n k) :=
  IsBkSequence.of_map (Nat.castAddMonoidHom (ZMod (2 ^ (sergeevModulusExp n k - 2))))
    (isBkSequence_map_zmod_sergeevBkSequence n hk)

end Cslib

end
