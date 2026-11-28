/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.TribesInfluence
import CslibFrontier.Foundations.Data.BitString.AgreeExpect
import CslibFrontier.Foundations.Data.Hamming
import CslibFrontier.Tactic.LinarithCast

/-!
# Tribes is far from every small junta

Every Boolean function `g` on the `n = s w` bits of the nearly balanced Tribes function
`Tribes_{w,s}`, `s = tribesSize w`, that depends only on a set `J` of at most `3 n / 4` coordinates
is `1 / 256`-far from Tribes (`Cslib.BitString.one_div_256_le_hammingDist_tribes_div`). This is
[O'Donnell, Exercise 4.15][ODonnell2014], which asks for some universal constant `ε₀ > 0`; the
constant `1 / 256` and the following proof are ours.

At least a quarter of the tribes, say the set `T`, have a coordinate `c j` outside `J`. For
`j ∈ T`, consider the event that the other bits of tribe `j` are `true`, every other tribe of `T`
has a `false` bit off its free coordinate, and every tribe outside `T` has a `false` bit. On it,
Tribes is the bit `c j`; flipping that bit keeps the event and `g`, and flips Tribes, so `g`
disagrees with Tribes on half of it. The events for distinct tribes of `T` are disjoint, and each
has probability `2 ^ (-(w - 1)) (1 - 2 ^ (-(w - 1))) ^ (|T| - 1) (1 - 2 ^ (-w)) ^ (s - |T|)` by the
independence of the tribes (`Cslib.BitString.expect_prod_tribe`). Bernoulli's inequality and
`2 ^ (w - 1) ≤ s ≤ 4 |T|`, `s < 2 ^ w` bound the total disagreement below by `1 / 256`.

Since Tribes has total influence at most `2 w` (`Cslib.BitString.totalInfluence_tribes_le`), this
shows that the exponential junta size in Friedgut's junta theorem is necessary
[O'Donnell, Exercise 9.26][ODonnell2014] [Friedgut1998]: for every `K ≥ 4` there is a Boolean
function of total influence at most `K` that is `1 / 256`-close to no function of at most
`(3 / 16) 2 ^ (K / 2)` coordinates
(`Cslib.BitString.exists_totalInfluence_le_lt_card_of_dependsOn`), against the
`3 · 2 ^ (8 K / ε)` coordinates of
`Cslib.BitString.exists_card_le_three_mul_two_rpow_dependsOn_hammingDist_div_le`. The explicit
constants are ours.

## Main results

* `Cslib.BitString.one_div_256_le_hammingDist_tribes_div`: Tribes is `1 / 256`-far from every
  function of at most `3 n / 4` of its `n` coordinates.
* `Cslib.BitString.exists_totalInfluence_le_lt_card_of_dependsOn`: the exponential junta size in
  Friedgut's junta theorem is necessary.

## References

* [E. Friedgut, *Boolean functions with low average sensitivity depend on few
  coordinates*][Friedgut1998]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset Function
open scoped BigOperators

variable {w s : ℕ}

/-- **The pivotal-flip pairing**: if a weight `P` and a function `g` are unchanged by flipping the
coordinate `k`, while `f` flips wherever `P` is nonzero, then `f` and `g` disagree on exactly half
of the `P`-mass. -/
private theorem two_mul_expect_mul_ite_ne_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : (ι → Bool) → ℝ) (f g : (ι → Bool) → Bool) (k : ι)
    (hP : ∀ x, P (update x k (!x k)) = P x) (hg : ∀ x, g (update x k (!x k)) = g x)
    (hf : ∀ x, P x ≠ 0 → f (update x k (!x k)) = !f x) :
    2 * 𝔼 x, P x * (if f x ≠ g x then 1 else 0) = 𝔼 x, P x := by
  let σ (x : ι → Bool) := update x k (!x k)
  have hinv : Involutive σ := fun x => by simp [σ]
  have he := Fintype.expect_equiv (hinv.toPerm σ)
    (fun x => P (σ x) * (if f (σ x) ≠ g (σ x) then (1 : ℝ) else 0))
    (fun x => P x * (if f x ≠ g x then (1 : ℝ) else 0)) (fun _ => rfl)
  have hpt (x : ι → Bool) : P (σ x) * (if f (σ x) ≠ g (σ x) then (1 : ℝ) else 0) =
      P x - P x * (if f x ≠ g x then 1 else 0) := by
    simp only [σ, hP, hg]
    by_cases h0 : P x = 0
    · simp [h0]
    · rw [hf x h0]
      cases f x <;> cases g x <;> simp
  simp only [hpt, expect_sub_distrib] at he
  linarith

section Junta

variable {J : Finset (Fin (s * w))}

/-- The tribes not entirely inside `J`. -/
private def looseTribes (w : ℕ) (J : Finset (Fin (s * w))) : Finset (Fin s) :=
  univ.filter fun j => ∃ i, finProdFinEquiv (j, i) ∉ J

/-- If `J` has at most `3 / 4` of the coordinates, then at least a quarter of the tribes are not
inside `J`. -/
private theorem le_four_mul_card_looseTribes (hw : 0 < w) (hJ : 4 * #J ≤ 3 * (s * w)) :
    s ≤ 4 * #(looseTribes w J) := by
  set T := looseTribes w J with hT
  set U : Finset (Fin s) := univ.filter fun j => ¬ ∃ i, finProdFinEquiv (j, i) ∉ J with hU
  have hTU : #T + #U = s := by
    rw [hT, looseTribes, hU, card_filter_add_card_filter_not, card_univ, Fintype.card_fin]
  have hUJ : #U * w ≤ #J := by
    have hsub : (U ×ˢ (univ : Finset (Fin w))).map finProdFinEquiv.toEmbedding ⊆ J := fun _ hk => by
      obtain ⟨⟨j, i⟩, hj, rfl⟩ := mem_map.1 hk
      exact (by simpa [hU] using hj : ∀ x, finProdFinEquiv (j, x) ∈ J) i
    simpa [card_product] using card_le_card hsub
  have h4 : #U ≤ 3 * #T := Nat.le_of_mul_le_mul_right (by nlinarith) hw
  omega

/-- The per-tribe factors of the event that bit `c j` of tribe `j` is pivotal: the other bits of
tribe `j` are `true`, each other tribe of `T` has a `false` bit off its own free bit, and each tribe
outside `T` has a `false` bit. -/
private def pivFactor (T : Finset (Fin s)) (c : Fin s → Fin w) (j j' : Fin s)
    (z : Fin w → Bool) : ℝ :=
  if j' = j then (if ∀ i ∈ univ.erase (c j), z i = true then 1 else 0)
  else if j' ∈ T then (if ∃ i ∈ univ.erase (c j'), z i = false then 1 else 0)
  else (if ∃ i ∈ univ, z i = false then 1 else 0)

/-- The indicator of the event that bit `c j` of tribe `j` is pivotal. -/
private def pivWeight (T : Finset (Fin s)) (c : Fin s → Fin w) (j : Fin s)
    (x : BitString (s * w)) : ℝ :=
  ∏ j', pivFactor T c j j' (fun i => x (finProdFinEquiv (j', i)))

variable {T : Finset (Fin s)} {c : Fin s → Fin w}

private theorem pivFactor_nonneg (j j' : Fin s) (z : Fin w → Bool) :
    0 ≤ pivFactor T c j j' z := by
  unfold pivFactor
  split_ifs <;> norm_num

private theorem pivFactor_le_one (j j' : Fin s) (z : Fin w → Bool) :
    pivFactor T c j j' z ≤ 1 := by
  unfold pivFactor
  split_ifs <;> norm_num

private theorem pivWeight_le_one (j : Fin s) (x : BitString (s * w)) : pivWeight T c j x ≤ 1 :=
  prod_le_one₀ (fun _ _ => pivFactor_nonneg ..) fun _ _ => pivFactor_le_one ..

private theorem pivWeight_ne_zero_self {j : Fin s} {x : BitString (s * w)}
    (hx : pivWeight T c j x ≠ 0) : ∀ i ≠ c j, x (finProdFinEquiv (j, i)) = true := by
  simpa only [pivFactor, ite_true, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not,
    mem_erase, mem_univ, and_true] using prod_ne_zero_iff.1 hx j (mem_univ _)

private theorem pivWeight_ne_zero_other {j : Fin s} {x : BitString (s * w)}
    (hx : pivWeight T c j x ≠ 0) {j' : Fin s} (hj' : j' ≠ j) :
    ∃ i, x (finProdFinEquiv (j', i)) = false := by
  by_cases hT : j' ∈ T
  · obtain ⟨i, _, hi⟩ := by simpa [pivFactor, hj', hT] using prod_ne_zero_iff.1 hx j' (mem_univ _)
    exact ⟨i, hi⟩
  · simpa [pivFactor, hj', hT] using prod_ne_zero_iff.1 hx j' (mem_univ _)

/-- The pivotality events of distinct tribes of `T` are disjoint. -/
private theorem pivWeight_eq_zero_of_ne {j₁ j₂ : Fin s} (hj₁ : j₁ ∈ T) (hj : j₂ ≠ j₁)
    {x : BitString (s * w)} (hx : pivWeight T c j₁ x ≠ 0) : pivWeight T c j₂ x = 0 := by
  by_contra hx₂
  obtain ⟨i, hi, hxi⟩ := by
    simpa [pivFactor, Ne.symm hj, hj₁] using prod_ne_zero_iff.1 hx₂ j₁ (mem_univ _)
  exact Bool.false_ne_true (hxi.symm.trans (pivWeight_ne_zero_self hx i hi))

/-- Setting the free bit of tribe `j` keeps its pivotality event. -/
private theorem pivWeight_update (j : Fin s) (x : BitString (s * w)) (b : Bool) :
    pivWeight T c j (update x (finProdFinEquiv (j, c j)) b) = pivWeight T c j x := by
  refine prod_congr rfl fun j' _ => ?_
  rcases eq_or_ne j' j with rfl | hj'
  · simp only [pivFactor, ite_true]
    refine if_congr (forall₂_congr fun i hi => ?_) rfl rfl
    rw [update_of_ne fun h => ne_of_mem_erase hi (by simpa using finProdFinEquiv.injective h)]
  · exact congrArg (pivFactor T c j j') (funext fun i =>
      update_of_ne (fun h => hj' (congrArg Prod.fst (finProdFinEquiv.injective h))) b x)

/-- On its pivotality event, Tribes is the free bit of tribe `j`. -/
private theorem tribes_eq_of_pivWeight_ne_zero {j : Fin s} {x : BitString (s * w)}
    (hx : pivWeight T c j x ≠ 0) : tribes w s x = x (finProdFinEquiv (j, c j)) := by
  rw [tribes]
  cases hb : x (finProdFinEquiv (j, c j))
  · refine decide_eq_false fun ⟨j', hj'⟩ => ?_
    rcases eq_or_ne j' j with rfl | hjj
    · exact Bool.false_ne_true (hb.symm.trans (hj' (c j')))
    · obtain ⟨i, hi⟩ := pivWeight_ne_zero_other hx hjj
      exact Bool.false_ne_true (hi.symm.trans (hj' i))
  · exact decide_eq_true ⟨j, fun i =>
      if hi : i = c j then hi ▸ hb else pivWeight_ne_zero_self hx i hi⟩

/-- The probability of the pivotality event of a tribe of `T`. -/
private theorem expect_pivWeight {j : Fin s} (hj : j ∈ T) :
    𝔼 x, pivWeight T c j x =
      2⁻¹ ^ (w - 1) * ((1 - 2⁻¹ ^ (w - 1)) ^ (#T - 1) * (1 - 2⁻¹ ^ w) ^ (s - #T)) := by
  unfold pivWeight
  rw [expect_prod_tribe, ← mul_prod_erase univ _ (mem_univ j),
    ← prod_filter_mul_prod_filter_not _ (· ∈ T)]
  have e0 : 𝔼 z, pivFactor T c j j z = 2⁻¹ ^ (w - 1) := by
    simp only [pivFactor, ite_true]
    rw [expect_ite_forall_mem_eq, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  have e1 : ∀ j' ∈ (univ.erase j).filter (· ∈ T),
      𝔼 z, pivFactor T c j j' z = 1 - 2⁻¹ ^ (w - 1) := fun j' hj' => by
    rcases mem_filter.1 hj' with ⟨hj'e, hj'T⟩
    simp only [pivFactor, ne_of_mem_erase hj'e, hj'T, ite_false, ite_true,
      expect_ite_exists_mem_eq, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  have e2 : ∀ j' ∈ (univ.erase j).filter (· ∉ T),
      𝔼 z, pivFactor T c j j' z = 1 - 2⁻¹ ^ w := fun j' hj' => by
    rcases mem_filter.1 hj' with ⟨hj'e, hj'T⟩
    simp only [pivFactor, ne_of_mem_erase hj'e, hj'T, ite_false,
      expect_ite_exists_mem_eq, card_univ, Fintype.card_fin]
  have c1 : #((univ.erase j).filter (· ∈ T)) = #T - 1 :=
    (congrArg card (Finset.ext fun _ => by simp)).trans (card_erase_of_mem hj)
  have c2 : #((univ.erase j).filter (· ∉ T)) = s - #T := by
    have hTc : (univ.erase j).filter (· ∉ T) = Tᶜ :=
      Finset.ext fun k => by by_cases hk : k = j <;> simp [hk, hj]
    rw [hTc, card_compl, Fintype.card_fin]
  rw [e0, prod_congr rfl e1, prod_congr rfl e2, prod_const, prod_const, c1, c2]

/-- A function of the coordinates `J` disagrees with Tribes on half of each pivotality event of a
tribe of `T` whose free bit is outside `J`, and these events are disjoint. -/
private theorem card_mul_le_hammingDist_tribes_div {g : BitString (s * w) → Bool}
    (hc : ∀ j ∈ T, finProdFinEquiv (j, c j) ∉ J) (hg : DependsOn g (J : Set (Fin (s * w)))) :
    #T * (2⁻¹ ^ (w - 1) * ((1 - 2⁻¹ ^ (w - 1)) ^ (#T - 1) * (1 - 2⁻¹ ^ w) ^ (s - #T)) / 2) ≤
      (hammingDist (tribes w s) g : ℝ) / 2 ^ (s * w) := by
  have hhalf (j : Fin s) (hj : j ∈ T) :
      2 * 𝔼 x, pivWeight T c j x * (if tribes w s x ≠ g x then 1 else 0) =
        𝔼 x, pivWeight T c j x := by
    refine two_mul_expect_mul_ite_ne_eq (pivWeight T c j) (tribes w s) g
      (finProdFinEquiv (j, c j)) (fun x => pivWeight_update j x _) (fun x => ?_)
      (fun x hx => ?_)
    · exact hg fun k hk => update_of_ne (by rintro rfl; exact hc j hj hk) ..
    · rw [tribes_eq_of_pivWeight_ne_zero (by rwa [pivWeight_update]),
        tribes_eq_of_pivWeight_ne_zero hx, update_self]
  have hdist : (hammingDist (tribes w s) g : ℝ) / 2 ^ (s * w) =
      𝔼 x, (if tribes w s x ≠ g x then (1 : ℝ) else 0) := by
    simpa using hammingDist_div_eq_expect (𝕜 := ℝ) (tribes w s) g
  rw [hdist]
  calc (#T : ℝ) *
        (2⁻¹ ^ (w - 1) * ((1 - 2⁻¹ ^ (w - 1)) ^ (#T - 1) * (1 - 2⁻¹ ^ w) ^ (s - #T)) / 2)
      = ∑ j ∈ T, 𝔼 x, pivWeight T c j x * (if tribes w s x ≠ g x then 1 else 0) := by
        rw [← nsmul_eq_mul, ← sum_const]
        refine sum_congr rfl fun j hj => ?_
        linarith [hhalf j hj, expect_pivWeight (T := T) (c := c) hj]
    _ = 𝔼 x, ∑ j ∈ T, pivWeight T c j x * (if tribes w s x ≠ g x then 1 else 0) :=
        (expect_sum_comm ..).symm
    _ ≤ 𝔼 x, (if tribes w s x ≠ g x then (1 : ℝ) else 0) := by
        refine expect_le_expect fun x _ => ?_
        have hD : (0 : ℝ) ≤ if tribes w s x ≠ g x then 1 else 0 := by split_ifs <;> norm_num
        by_cases hx : ∃ j ∈ T, pivWeight T c j x ≠ 0
        · obtain ⟨j, hj, hjx⟩ := hx
          rw [sum_eq_single_of_mem j hj fun j' _ hj' => by
            rw [pivWeight_eq_zero_of_ne hj hj' hjx, zero_mul]]
          exact mul_le_of_le_one_left hD (pivWeight_le_one j x)
        · simp only [not_exists, not_and, not_not] at hx
          exact (sum_eq_zero fun j hj => by rw [hx j hj, zero_mul]).trans_le hD

/-- The numerical estimate: with `2 ^ (w - 1) ≤ s ≤ 4 t`, `t ≤ s < 2 ^ w` and
`(1 - 2 ^ (-w)) ^ s ≥ 1 / 2`, the disagreement bound is at least `1 / 256`. -/
private theorem one_div_256_le_card_mul (hw : 1 ≤ w) (hs₁ : 2 ^ (w - 1) ≤ s) (hs₂ : s < 2 ^ w)
    (hq : 1 / 2 ≤ (1 - (2⁻¹ : ℝ) ^ w) ^ s) {t : ℕ} (ht : s ≤ 4 * t) (hts : t ≤ s) :
    (1 / 256 : ℝ) ≤
      t * (2⁻¹ ^ (w - 1) * ((1 - 2⁻¹ ^ (w - 1)) ^ (t - 1) * (1 - 2⁻¹ ^ w) ^ (s - t)) / 2) := by
  set y : ℝ := 2⁻¹ ^ (w - 1) with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hq0 : 0 ≤ 1 - (2⁻¹ : ℝ) ^ w := sub_nonneg.2 (pow_le_one₀ (by norm_num) (by norm_num))
  have hq1 : 1 - (2⁻¹ : ℝ) ^ w ≤ 1 := sub_le_self _ (by positivity)
  have hA : 1 / 2 ≤ (1 - (2⁻¹ : ℝ) ^ w) ^ (s - t) :=
    hq.trans (pow_le_pow_of_le_one hq0 hq1 (Nat.sub_le _ _))
  have hB : 1 / 4 ≤ t * y := by
    rw [hy, inv_pow, le_mul_inv_iff₀ (by positivity)]
    cast_linarith [hs₁.trans ht]
  have hC : 1 / 16 ≤ (1 - y) ^ (t - 1) := by
    rcases Nat.lt_or_ge w 2 with hw2 | hw2
    · obtain rfl : w = 1 := by omega
      norm_num [Nat.sub_eq_zero_of_le (Nat.lt_succ_iff.mp (hts.trans_lt hs₂))]
    · set n₀ : ℕ := 2 ^ (w - 2) with hn₀
      have hny : (n₀ : ℝ) * y = 1 / 2 := by
        have hw1 : w - 1 = w - 2 + 1 := by omega
        rw [hy, hn₀, Nat.cast_pow, Nat.cast_ofNat, inv_pow, ← div_eq_mul_inv,
          div_eq_iff (by positivity), hw1, pow_succ]
        ring
      -- Bernoulli's inequality
      have hpow : 1 / 2 ≤ (1 - y) ^ n₀ := by
        linarith [sub_eq_add_neg (1 : ℝ) y ▸ one_add_mul_le_pow (a := -y) (by linarith) n₀]
      have hTn : t - 1 ≤ 4 * n₀ := by
        have : 2 ^ w = 2 ^ (w - 2) * 2 ^ 2 := by rw [← pow_add, Nat.sub_add_cancel hw2]
        omega
      calc (1 / 16 : ℝ) = (1 / 2) ^ 4 := by norm_num
        _ ≤ ((1 - y) ^ n₀) ^ 4 := pow_le_pow_left₀ (by norm_num) hpow 4
        _ = (1 - y) ^ (4 * n₀) := by rw [← pow_mul, mul_comm]
        _ ≤ (1 - y) ^ (t - 1) := pow_le_pow_of_le_one (by linarith) (by linarith) hTn
  have hB0 : 0 ≤ (t : ℝ) * y := mul_nonneg (Nat.cast_nonneg _) hy0
  have hC0 : 0 ≤ (1 - y) ^ (t - 1) := pow_nonneg (by linarith) _
  calc (1 / 256 : ℝ) = (1 / 4) * (1 / 16) * (1 / 2) / 2 := by norm_num
    _ ≤ (t * y) * (1 - y) ^ (t - 1) * (1 - 2⁻¹ ^ w) ^ (s - t) / 2 := div_le_div_of_nonneg_right
        (mul_le_mul (mul_le_mul hB hC (by norm_num) hB0) hA (by norm_num) (mul_nonneg hB0 hC0))
        (by norm_num)
    _ = t * (y * ((1 - y) ^ (t - 1) * (1 - 2⁻¹ ^ w) ^ (s - t)) / 2) := by ring

/-- The junta-distance bound for every nearly balanced number `s` of tribes. -/
private theorem one_div_256_le_hammingDist_tribes_div_of {g : BitString (s * w) → Bool}
    (hw : 1 ≤ w) (hs₁ : 2 ^ (w - 1) ≤ s) (hs₂ : s < 2 ^ w)
    (hq : 1 / 2 ≤ (1 - (2⁻¹ : ℝ) ^ w) ^ s) (hJ : 4 * #J ≤ 3 * (s * w))
    (hg : DependsOn g (J : Set (Fin (s * w)))) :
    1 / 256 ≤ (hammingDist (tribes w s) g : ℝ) / 2 ^ (s * w) := by
  have : Nonempty (Fin w) := ⟨⟨0, hw⟩⟩
  choose! c hc using fun j (hj : j ∈ looseTribes w J) => (mem_filter.1 hj).2
  exact (one_div_256_le_card_mul hw hs₁ hs₂ hq (le_four_mul_card_looseTribes hw hJ)
    (by simpa using card_le_univ (looseTribes w J))).trans
    (card_mul_le_hammingDist_tribes_div hc hg)

end Junta

/-- **Tribes is far from every `(3 / 4) n`-junta** [O'Donnell, Exercise 4.15][ODonnell2014]: on
`n = s w` bits with `s = tribesSize w` and `w ≥ 1`, every Boolean function that depends only on a
set `J` of at most `3 n / 4` coordinates disagrees with Tribes on at least a `1 / 256` fraction of
the inputs. O'Donnell asks for some universal constant; the constant `1 / 256` and its proof are
ours. -/
theorem one_div_256_le_hammingDist_tribes_div {J : Finset (Fin (tribesSize w * w))}
    {g : BitString (tribesSize w * w) → Bool} (hw : 1 ≤ w)
    (hJ : 4 * #J ≤ 3 * (tribesSize w * w))
    (hg : DependsOn g (J : Set (Fin (tribesSize w * w)))) :
    1 / 256 ≤ (hammingDist (tribes w (tribesSize w)) g : ℝ) / 2 ^ (tribesSize w * w) :=
  one_div_256_le_hammingDist_tribes_div_of hw (two_pow_sub_one_le_tribesSize hw)
    (tribesSize_lt_two_pow w) (one_div_two_le_pow_tribesSize w) hJ hg

/-- **The exponential in Friedgut's junta theorem is necessary**
[O'Donnell, Exercise 9.26][ODonnell2014] [Friedgut1998]: for every `K ≥ 4` there is a Boolean
function of total influence at most `K` such that every function of a set `J` of coordinates that
is `1 / 256`-close to it has `|J| > (3 / 16) 2 ^ (K / 2)`. The witness is the nearly balanced
Tribes with `w = ⌊K / 2⌋`. Compare the upper bound `3 · 2 ^ (8 K / ε)` of
`Cslib.BitString.exists_card_le_three_mul_two_rpow_dependsOn_hammingDist_div_le`. The explicit
constants are ours. -/
theorem exists_totalInfluence_le_lt_card_of_dependsOn {K : ℝ} (hK : 4 ≤ K) :
    ∃ (n : ℕ) (f : BitString n → Bool), totalInfluence (fun x => signVal (f x)) ≤ K ∧
      ∀ (J : Finset (Fin n)) (g : BitString n → Bool), DependsOn g (J : Set (Fin n)) →
        (hammingDist f g : ℝ) / 2 ^ n < 1 / 256 → 3 / 16 * (2 : ℝ) ^ (K / 2) < #J := by
  set w : ℕ := ⌊K / 2⌋₊
  have hw1 : (w : ℝ) ≤ K / 2 := Nat.floor_le (by linarith)
  have hw2 : K / 2 < w + 1 := Nat.lt_floor_add_one _
  have hw2' : 2 ≤ w := Nat.le_floor (by linarith)
  refine ⟨tribesSize w * w, tribes w (tribesSize w),
    (totalInfluence_tribes_le w).trans (by linarith), fun J g hg hdist => ?_⟩
  by_contra! hJ
  refine absurd (one_div_256_le_hammingDist_tribes_div (by omega) ?_ hg) (not_le.2 hdist)
  have hs₁ : 2 ^ (w - 1) ≤ tribesSize w := two_pow_sub_one_le_tribesSize (by omega)
  have h1 : (2 : ℝ) ^ (K / 2) ≤ 2 ^ ((w : ℝ) + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hw2.le
  rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_one] at h1
  have hpow : (2 : ℝ) ^ w = 2 * 2 ^ (w - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ w)]
  exact_mod_cast (show (4 * #J : ℝ) ≤ 3 * (tribesSize w * w) by cast_nlinarith [hw2', hs₁])

end Cslib.BitString
