/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ExactClocked

/-!
# Tests on the clocked bits

Programs over `[τ, n]` that read bits of a clocked accept count through a bits program `P` over
`[τ, n, j]` (the conclusion of `ClockedBits`):

* `bitAtPad P`: bit `paddedTime τ` (the halting test: an accept count `Z ≤ 2^T` equals `2^T`
  exactly when bit `T` is set, `eq_two_pow_iff_bit`);
* `majorityProg P`: positive exactly when `2^T < 2 Z` (`two_pow_lt_two_mul_iff`);
* `bitProg P j`: bit `j` for a fixed `j`;
* `modProg P q`: `Z mod q`, by Horner's rule over the bits `T, T-1, …, 0`;
* `eqBitsProg P P'`: `1` when two counts below `2^(T+1)` have the same bits.

Each has a value lemma and a value bound.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross.Exact

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term NtimeDspace.SumProduct Finset
  Cslib.Complexity Cslib.Complexity.CountingSimulation

variable {w : List Bool} {env : List ℕ} {M : ℕ}

/-! ### Arithmetic facts -/

theorem eq_two_pow_iff_bit {Z T : ℕ} (hZ : Z ≤ 2 ^ T) : Z = 2 ^ T ↔ 0 < Z / 2 ^ T % 2 := by
  rcases Nat.lt_or_ge Z (2 ^ T) with h | h
  · rw [Nat.div_eq_of_lt h]; simp; omega
  · have : Z = 2 ^ T := le_antisymm hZ h
    subst this; simp

theorem sum_bits_pos_iff (Z m : ℕ) : 0 < ∑ i ∈ range m, Z / 2 ^ i % 2 ↔ 0 < Z % 2 ^ m := by
  rw [← sum_bits_eq_mod, Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _),
    Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  refine exists_congr fun i => and_congr_right fun _ => ?_
  constructor
  · intro h; exact Nat.mul_pos h (Nat.two_pow_pos _)
  · intro h; exact Nat.pos_of_mul_pos_right h

/-- Strict majority from three bits and a test on the lower bits. -/
theorem two_pow_lt_two_mul_iff {Z m : ℕ} (hZ : Z ≤ 2 ^ (m + 1)) :
    2 ^ (m + 1) < 2 * Z ↔
      0 < Z / 2 ^ (m + 1) % 2 + Z / 2 ^ m % 2 *
        (if 0 < ∑ i ∈ range m, Z / 2 ^ i % 2 then 1 else 0) := by
  simp only [sum_bits_pos_iff]
  rcases Nat.lt_or_ge Z (2 ^ (m + 1)) with h | h
  · rw [Nat.div_eq_of_lt h, Nat.zero_mod, zero_add]
    have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
    have hd : Z / 2 ^ m < 2 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; omega
    have hZ' := Nat.div_add_mod Z (2 ^ m)
    have he := Nat.mod_lt Z (Nat.two_pow_pos m)
    rw [h2]
    generalize Z / 2 ^ m = d at hd hZ' ⊢
    generalize Z % 2 ^ m = e at he hZ' ⊢
    rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl
    · simp only [Nat.zero_mod, zero_mul, lt_irrefl, iff_false, not_lt]
      omega
    · simp only [Nat.one_mod, one_mul, mul_one] at hZ' ⊢
      by_cases he0 : 0 < e
      · simp only [he0, ite_true]; omega
      · simp only [he0, ite_false]; omega
  · have : Z = 2 ^ (m + 1) := le_antisymm hZ h
    subst this
    simp only [Nat.div_self (Nat.two_pow_pos _), Nat.one_mod]
    constructor
    · intro _; omega
    · intro _; rw [pow_succ]; have := Nat.two_pow_pos m; omega

/-- Horner's rule on the bits from the top. -/
theorem horner_bits (Z q T : ℕ) (hZ : Z < 2 ^ (T + 1)) :
    (List.range (T + 1)).foldl (fun acc i => (2 * acc + Z / 2 ^ (T - i) % 2) % q) 0 = Z % q := by
  have key : ∀ k ≤ T + 1,
      (List.range k).foldl (fun acc i => (2 * acc + Z / 2 ^ (T - i) % 2) % q) 0 =
        Z / 2 ^ (T + 1 - k) % q := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [Nat.div_eq_of_lt hZ]
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega)]
      have e : T + 1 - k = (T - k) + 1 := by omega
      rw [e, pow_succ, ← Nat.div_div_eq_div_mul, show T + 1 - (k + 1) = T - k by omega]
      set Y := Z / 2 ^ (T - k)
      have h1 : 2 * (Y / 2 % q) + Y % 2 ≡ 2 * (Y / 2) + Y % 2 [MOD q] :=
        Nat.ModEq.add_right _ (Nat.ModEq.mul_left _ (Nat.mod_modEq _ _))
      rw [Nat.div_add_mod Y 2] at h1
      exact h1
  rw [key _ le_rfl, Nat.sub_self, pow_zero, Nat.div_one]

/-! ### Programs over `[τ, n]` -/

/-- The padded time of the clock `τ = lvl 1`, at depth `2`. -/
def padAt : Term := call1 padProg (lvl 1)

/-- Bit `j` of the clocked count, at depth `2` (`τ = lvl 1`, `n = lvl 0`). -/
def bitAt (P : Prog) (j : Term) : Term := call3 P (lvl 1) (lvl 0) j

/-- The halting test: bit `paddedTime τ`. -/
def bitAtPad (P : Prog) : Prog := closeAt 2 (bitAt P padAt 2)

/-- The majority test: `bit T + bit (T-1) · [some lower bit]` for `T = paddedTime τ`. -/
def majorityProg (P : Prog) : Prog :=
  closeAt 2 (letT padAt (fun T => letT (sub T (const 1)) fun m =>
    add (bitAt P (add m (const 1))) (mul (bitAt P m)
      (lt (const 0) (sumT m fun i => bitAt P i)))) 2)

/-- Bit `j` of the clocked count, for a fixed `j`. -/
def bitProg (P : Prog) (j : ℕ) : Prog := closeAt 2 (bitAt P (const j) 2)

/-- `Z mod q` by Horner's rule over the bits `T, …, 0`. -/
def modProg (P : Prog) (q : ℕ) : Prog :=
  closeAt 2 (letT padAt (fun T => foldT (add T (const 1)) (const 0) fun acc i =>
    mod (add (mul (const 2) acc) (bitAt P (sub T i))) (const q)) 2)

/-- `1` when the bits `0, …, T` of two clocked counts agree. -/
def eqBitsProg (P P' : Prog) : Prog :=
  closeAt 2 (letT padAt (fun T => lt (sumT (add T (const 1)) fun i =>
    add (sub (bitAt P i) (bitAt P' i)) (sub (bitAt P' i) (bitAt P i))) (const 1)) 2)

/-! ### Values and bounds -/

section

variable {P : Prog} {τ n : ℕ} {Z : ℕ} {B : ℕ}

/-- The bits program computes the bits of `Z` and is bounded by `B`. -/
def BitsOK (w : List Bool) (P : Prog) (τ n Z B : ℕ) : Prop :=
  ∀ j, P.eval w [τ, n, j] = Z / 2 ^ j % 2 ∧ P.Bounded w B [τ, n, j]

theorem env2_τ : Val w (lvl 1) [τ, n] τ := val_lvl (by simp)
theorem env2_n : Val w (lvl 0) [τ, n] n := val_lvl (by simp)

theorem val_padAt : Val w padAt [τ, n] (paddedTime τ) := by
  have := val_call1 closed_padProg (env2_τ (w := w) (τ := τ) (n := n))
  rw [eval_padProg] at this
  exact this

theorem bd_padAt (hτ : 2 ≤ τ) (hB : 2 * τ + 2 ≤ B) : Bd w B padAt [τ, n] :=
  bd_call1 closed_padProg env2_τ (bd_lvl _ _) (bounded_padProg hτ hB)

theorem val_bitAt (hP : Prog'.closed 3 P = true) (hok : BitsOK w P τ n Z B) {j : Term} {a : ℕ}
    {e : List ℕ} (he : Val w (lvl 1) e τ) (hn : Val w (lvl 0) e n) (hj : Val w j e a) :
    Val w (bitAt P j) e (Z / 2 ^ a % 2) := by
  have := val_call3 hP he hn hj
  rwa [(hok a).1] at this

theorem bd_bitAt (hP : Prog'.closed 3 P = true) (hok : BitsOK w P τ n Z B) {j : Term} {a : ℕ}
    {e : List ℕ} (he : Val w (lvl 1) e τ) (hn : Val w (lvl 0) e n) (hj : Val w j e a)
    (hbj : Bd w B j e) : Bd w B (bitAt P j) e :=
  bd_call3 hP he hn hj (bd_lvl _ _) (bd_lvl _ _) hbj (hok a).2

theorem eval_bitAtPad (hP : Prog'.closed 3 P = true) (hok : BitsOK w P τ n Z B) :
    (bitAtPad P).eval w [τ, n] = Z / 2 ^ paddedTime τ % 2 := by
  rw [bitAtPad, eval_closeAt _ 2 _ rfl]
  exact (val_bitAt hP hok env2_τ env2_n val_padAt).eq

theorem bounded_bitAtPad (hP : Prog'.closed 3 P = true) (hok : BitsOK w P τ n Z B)
    (hτ : 2 ≤ τ) (hB : 2 * τ + 2 ≤ B) : (bitAtPad P).Bounded w B [τ, n] := by
  rw [bitAtPad, bounded_closeAt _ 2 _ rfl]
  exact (bd_bitAt hP hok env2_τ env2_n val_padAt (bd_padAt hτ hB)).bnd

theorem eval_bitProg (hP : Prog'.closed 3 P = true) (hok : BitsOK w P τ n Z B) (j : ℕ) :
    (bitProg P j).eval w [τ, n] = Z / 2 ^ j % 2 := by
  rw [bitProg, eval_closeAt _ 2 _ rfl]
  exact (val_bitAt hP hok env2_τ env2_n (val_const j _)).eq

theorem bounded_bitProg (hP : Prog'.closed 3 P = true) (hok : BitsOK w P τ n Z B) {j : ℕ}
    (hj : j ≤ B) : (bitProg P j).Bounded w B [τ, n] := by
  rw [bitProg, bounded_closeAt _ 2 _ rfl]
  exact (bd_bitAt hP hok env2_τ env2_n (val_const j _) (bd_const hj _)).bnd

theorem eval_majorityProg (hP : Prog'.closed 3 P = true) (hok : BitsOK w P τ n Z B) :
    (majorityProg P).eval w [τ, n] =
      Z / 2 ^ (paddedTime τ - 1 + 1) % 2 + Z / 2 ^ (paddedTime τ - 1) % 2 *
        (if 0 < ∑ i ∈ range (paddedTime τ - 1), Z / 2 ^ i % 2 then 1 else 0) := by
  rw [majorityProg, eval_closeAt _ 2 _ rfl]
  refine (val_letT (val_padAt (w := w) (τ := τ) (n := n)) fun p1 T hT => ?_).eq
  refine val_letT (val_sub hT (val_const 1 _)) fun p2 m hm => ?_
  have hτ' := (env2_τ (w := w) (τ := τ) (n := n)).ext p1 |>.ext p2
  have hn' := (env2_n (w := w) (τ := τ) (n := n)).ext p1 |>.ext p2
  refine val_add (val_bitAt hP hok hτ' hn' (val_add hm (val_const 1 _)))
    (val_mul (val_bitAt hP hok hτ' hn' hm) (val_lt (val_const 0 _)
      (val_sumT hm fun pre u b hu => val_bitAt hP hok (hτ'.ext pre) (hn'.ext pre) hu)))

theorem bounded_majorityProg (hP : Prog'.closed 3 P = true) (hok : BitsOK w P τ n Z B)
    (hτ : 2 ≤ τ) (hB : 2 * τ + 2 ≤ B) : (majorityProg P).Bounded w B [τ, n] := by
  rw [majorityProg, bounded_closeAt _ 2 _ rfl]
  have hpad : paddedTime τ + 1 ≤ 2 * τ := paddedTime_add_one_le hτ
  refine (bd_letT val_padAt (bd_padAt hτ hB) fun p1 T hT hbT => ?_).bnd
  refine bd_letT (val_sub hT (val_const 1 _)) (bd_sub hbT (bd_const (by omega) _))
    fun p2 m hm hbm => ?_
  have hτ' := (env2_τ (w := w) (τ := τ) (n := n)).ext p1 |>.ext p2
  have hn' := (env2_n (w := w) (τ := τ) (n := n)).ext p1 |>.ext p2
  have hbit : ∀ i, Z / 2 ^ i % 2 ≤ 1 := fun i => by omega
  refine bd_add (bd_bitAt hP hok hτ' hn' (val_add hm (val_const 1 _))
    (bd_add hbm (bd_const (by omega) _) hm (val_const 1 _) (by omega)))
    (bd_mul (bd_bitAt hP hok hτ' hn' hm hbm) (bd_lt (bd_const (Nat.zero_le _) _)
      (bd_sumT hm (fun pre u b hu => val_bitAt hP hok (hτ'.ext pre) (hn'.ext pre) hu) hbm
        (by omega) ((sum_le_sum fun i _ => hbit i).trans (by simp; omega))
        fun pre u b _ hu hbu => bd_bitAt hP hok (hτ'.ext pre) (hn'.ext pre) hu hbu))
      (val_bitAt hP hok hτ' hn' hm) (val_lt (val_const 0 _)
        (val_sumT hm fun pre u b hu => val_bitAt hP hok (hτ'.ext pre) (hn'.ext pre) hu))
      (by have := hbit (paddedTime τ - 1); split_ifs <;> omega))
    (val_bitAt hP hok hτ' hn' (val_add hm (val_const 1 _)))
    (val_mul (val_bitAt hP hok hτ' hn' hm) (val_lt (val_const 0 _)
      (val_sumT hm fun pre u b hu => val_bitAt hP hok (hτ'.ext pre) (hn'.ext pre) hu)))
    (by have := hbit (paddedTime τ - 1 + 1); have := hbit (paddedTime τ - 1)
        split_ifs <;> omega)

theorem eval_modProg (hP : Prog'.closed 3 P = true) (hok : BitsOK w P τ n Z B) (q : ℕ) :
    (modProg P q).eval w [τ, n] =
      (List.range (paddedTime τ + 1)).foldl
        (fun acc i => (2 * acc + Z / 2 ^ (paddedTime τ - i) % 2) % q) 0 := by
  rw [modProg, eval_closeAt _ 2 _ rfl]
  refine (val_letT (val_padAt (w := w) (τ := τ) (n := n)) fun p1 T hT => ?_).eq
  have hτ' := (env2_τ (w := w) (τ := τ) (n := n)).ext p1
  have hn' := (env2_n (w := w) (τ := τ) (n := n)).ext p1
  exact val_foldT (val_add hT (val_const 1 _)) (val_const 0 _) _ fun pre u u' a i hu hu' =>
    val_mod (val_add (val_mul (val_const 2 _) hu) (val_bitAt hP hok (hτ'.ext pre) (hn'.ext pre)
      (val_sub (hT.ext pre) hu'))) (val_const q _)

theorem bounded_modProg (hP : Prog'.closed 3 P = true) (hok : BitsOK w P τ n Z B) {q : ℕ}
    (hq : 1 ≤ q) (hτ : 2 ≤ τ) (hB : 2 * τ + 2 ≤ B) (hqB : 2 * q + 2 ≤ B) :
    (modProg P q).Bounded w B [τ, n] := by
  rw [modProg, bounded_closeAt _ 2 _ rfl]
  have hpad : paddedTime τ + 1 ≤ 2 * τ := paddedTime_add_one_le hτ
  refine (bd_letT val_padAt (bd_padAt hτ hB) fun p1 T hT hbT => ?_).bnd
  have hτ' := (env2_τ (w := w) (τ := τ) (n := n)).ext p1
  have hn' := (env2_n (w := w) (τ := τ) (n := n)).ext p1
  refine bd_foldT (val_add hT (val_const 1 _)) (val_const 0 _)
    (fun acc i => (2 * acc + Z / 2 ^ (paddedTime τ - i) % 2) % q)
    (fun pre u u' a i hu hu' => val_mod (val_add (val_mul (val_const 2 _) hu)
      (val_bitAt hP hok (hτ'.ext pre) (hn'.ext pre) (val_sub (hT.ext pre) hu'))) (val_const q _))
    (bd_add hbT (bd_const (by omega) _) hT (val_const 1 _) (by omega)) (bd_const (Nat.zero_le _) _)
    (by omega) fun pre u u' a i hi ha hu hu' hbu hbu' => ?_
  have hal : a < q := by
    rw [ha]
    rcases i with _ | i
    · simp; omega
    · rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact Nat.mod_lt _ (by omega)
  refine bd_mod (bd_add (bd_mul (bd_const (by omega) _) hbu (val_const 2 _) hu (by omega))
    (bd_bitAt hP hok (hτ'.ext pre) (hn'.ext pre) (val_sub (hT.ext pre) hu')
      (bd_sub (hbT.ext pre) hbu')) (val_mul (val_const 2 _) hu)
    (val_bitAt hP hok (hτ'.ext pre) (hn'.ext pre) (val_sub (hT.ext pre) hu'))
    (by have : Z / 2 ^ (paddedTime τ - i) % 2 ≤ 1 := by omega
        omega)) (bd_const (by omega) _)

end

section Eq

variable {P P' : Prog} {τ n Z Z' B : ℕ}

theorem eval_eqBitsProg (hP : Prog'.closed 3 P = true) (hP' : Prog'.closed 3 P' = true)
    (hok : BitsOK w P τ n Z B) (hok' : BitsOK w P' τ n Z' B) :
    (eqBitsProg P P').eval w [τ, n] =
      if ∑ i ∈ range (paddedTime τ + 1),
          ((Z / 2 ^ i % 2 - Z' / 2 ^ i % 2) + (Z' / 2 ^ i % 2 - Z / 2 ^ i % 2)) < 1
      then 1 else 0 := by
  rw [eqBitsProg, eval_closeAt _ 2 _ rfl]
  refine (val_letT (val_padAt (w := w) (τ := τ) (n := n)) fun p1 T hT => ?_).eq
  have hτ' := (env2_τ (w := w) (τ := τ) (n := n)).ext p1
  have hn' := (env2_n (w := w) (τ := τ) (n := n)).ext p1
  refine val_lt (val_sumT (val_add hT (val_const 1 _)) fun pre u b hu => ?_) (val_const 1 _)
  exact val_add (val_sub (val_bitAt hP hok (hτ'.ext pre) (hn'.ext pre) hu)
      (val_bitAt hP' hok' (hτ'.ext pre) (hn'.ext pre) hu))
    (val_sub (val_bitAt hP' hok' (hτ'.ext pre) (hn'.ext pre) hu)
      (val_bitAt hP hok (hτ'.ext pre) (hn'.ext pre) hu))

theorem bounded_eqBitsProg (hP : Prog'.closed 3 P = true) (hP' : Prog'.closed 3 P' = true)
    (hok : BitsOK w P τ n Z B) (hok' : BitsOK w P' τ n Z' B) (hτ : 2 ≤ τ)
    (hB : 2 * τ + 2 ≤ B) : (eqBitsProg P P').Bounded w B [τ, n] := by
  rw [eqBitsProg, bounded_closeAt _ 2 _ rfl]
  have hpad : paddedTime τ + 1 ≤ 2 * τ := paddedTime_add_one_le hτ
  refine (bd_letT val_padAt (bd_padAt hτ hB) fun p1 T hT hbT => ?_).bnd
  have hτ' := (env2_τ (w := w) (τ := τ) (n := n)).ext p1
  have hn' := (env2_n (w := w) (τ := τ) (n := n)).ext p1
  have hbit : ∀ (Y i : ℕ), Y / 2 ^ i % 2 ≤ 1 := fun Y i => by omega
  refine bd_lt (bd_sumT (val_add hT (val_const 1 _))
    (F := fun i => (Z / 2 ^ i % 2 - Z' / 2 ^ i % 2) + (Z' / 2 ^ i % 2 - Z / 2 ^ i % 2))
    (fun pre u b hu => ?_)
    (bd_add hbT (bd_const (by omega) _) hT (val_const 1 _) (by omega)) (by omega) ?_
    fun pre u b _ hu hbu => ?_) (bd_const (by omega) _)
  · exact val_add (val_sub (val_bitAt hP hok (hτ'.ext pre) (hn'.ext pre) hu)
      (val_bitAt hP' hok' (hτ'.ext pre) (hn'.ext pre) hu))
      (val_sub (val_bitAt hP' hok' (hτ'.ext pre) (hn'.ext pre) hu)
        (val_bitAt hP hok (hτ'.ext pre) (hn'.ext pre) hu))
  · calc _ ≤ ∑ _i ∈ range (paddedTime τ + 1), 1 := sum_le_sum fun i _ => by
          have := hbit Z i; have := hbit Z' i; omega
      _ ≤ B := by simp; omega
  · exact bd_add (bd_sub (bd_bitAt hP hok (hτ'.ext pre) (hn'.ext pre) hu hbu)
      (bd_bitAt hP' hok' (hτ'.ext pre) (hn'.ext pre) hu hbu))
      (bd_sub (bd_bitAt hP' hok' (hτ'.ext pre) (hn'.ext pre) hu hbu)
        (bd_bitAt hP hok (hτ'.ext pre) (hn'.ext pre) hu hbu))
      (val_sub (val_bitAt hP hok (hτ'.ext pre) (hn'.ext pre) hu)
        (val_bitAt hP' hok' (hτ'.ext pre) (hn'.ext pre) hu))
      (val_sub (val_bitAt hP' hok' (hτ'.ext pre) (hn'.ext pre) hu)
        (val_bitAt hP hok (hτ'.ext pre) (hn'.ext pre) hu))
      (by have := hbit Z b; have := hbit Z' b; omega)

/-- Two numbers below `2^(T+1)` are equal exactly when their bits `0, …, T` agree. -/
theorem eq_iff_bits {Z Z' T : ℕ} (hZ : Z < 2 ^ (T + 1)) (hZ' : Z' < 2 ^ (T + 1)) :
    Z = Z' ↔ ∑ i ∈ range (T + 1),
      ((Z / 2 ^ i % 2 - Z' / 2 ^ i % 2) + (Z' / 2 ^ i % 2 - Z / 2 ^ i % 2)) < 1 := by
  rw [Nat.lt_one_iff, Finset.sum_eq_zero_iff]
  constructor
  · rintro rfl i _; simp
  · intro h
    have hb : ∀ i ∈ range (T + 1), Z / 2 ^ i % 2 = Z' / 2 ^ i % 2 := fun i hi => by
      have := h i hi; omega
    rw [← sum_bits_eq hZ, ← sum_bits_eq hZ']
    exact sum_congr rfl fun i hi => by rw [hb i hi]

end Eq

end Cslib.Complexity.NtimeDspace.Cross.Exact
