/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Parity
public import CslibFrontier.Logics.Propositional.CNF.Coding
public import CslibFrontier.Logics.Propositional.CNF.Parity
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Depth-three formulas for parity

Each formula in an OR of formulas in conjunctive normal form computing a function `g` has its
solutions among the true inputs of `g`, so an isolated true input of `g` is an isolated solution of
one of the formulas. The satisfiability coding lemma bounds those, and so the formulas in an OR for
parity, whose `2 ^ (n - 1)` true inputs are all isolated.

*Bottom fan-in `k`.* A formula of width `k` has at most `2 ^ ((1 - 1 / k) n)` isolated solutions,
so an OR of such formulas needs a formula per `2 ^ ((1 - 1 / k) n)` isolated true inputs
(`CNF.card_isolatedInputs_mul_two_rpow_le_of_any`), as in the proof of
[Paturi, Pudlák and Zane, Theorem 6][PaturiPudlakZane1999]. For parity this is `2 ^ (n / k - 1)`
(`CNF.two_rpow_le_length_of_any_eval_eq_parity`), and the bound is attained when `k` divides `n`:
split the variables into blocks of `k` and take one formula for each pattern of block parities
with odd total (`CNF.exists_any_eval_eq_parity`), as in the example after
[Paturi, Pudlák and Zane, Lemma 4][PaturiPudlakZane1999].

*Unbounded bottom fan-in* [Paturi, Pudlák and Zane, Theorem 6][PaturiPudlakZane1999]. Weigh a
solution `x` of a formula by `w(x) = ∑ᵢ 1 / ℓᵢ`, where `ℓᵢ` is the number of variables of a
shortest clause critical for the direction `i` at `x`. At most `2 ^ (n - μ)` solutions of a formula
have weight at least `μ` (`CNF.card_filter_le_sum_inv_critWidth_mul_two_rpow_le`). A clause with
`ℓ` variables is critical for at most `ℓ 2 ^ (n - ℓ)` pairs of an input and a direction
(`CNF.card_filter_critical_prod_le`), and `t ↦ t 2 ^ (1 / t)` is convex and decreasing up to
`log 2`, so the shortest critical clauses of the inputs of weight below `μ ≤ n log 2` number at
least `μ 2 ^ (n / μ) / 2 ^ n` per input (`CNF.mul_two_rpow_div_le_two_pow_mul_sum_critWidth`). So
an OR of `m` formulas with `K` distinct clauses computing a function with `s` isolated true inputs
has `s min (2 ^ μ) (μ 2 ^ (n / μ)) ≤ 2 ^ n (m + K)` (`CNF.card_isolatedInputs_mul_min_le`). With
Paturi, Pudlák and Zane's `μ = √n + (log₂ n) / 4`, both `2 ^ μ` and `μ 2 ^ (n / μ)` are at least
`n ^ (1 / 4) 2 ^ √n` (`CNF.card_isolatedInputs_mul_rpow_mul_two_rpow_sqrt_le`), so ORs of formulas
in conjunctive normal form for the parity of `n ≥ 4` bits have `m + K ≥ n ^ (1 / 4) 2 ^ (√n - 1)`
(`CNF.rpow_mul_two_rpow_sqrt_sub_one_le_of_any_eval_eq_parity`). Dually, ANDs of formulas in
disjunctive normal form for parity negate to ORs for its negation, all of whose `2 ^ (n - 1)` true
inputs are isolated too, and need as many formulas and terms
(`DNF.rpow_mul_two_rpow_sqrt_sub_one_le_of_all_eval_eq_parity`). The simpler `μ = √n` gives
`m + K ≥ 2 ^ (√n - 1)` already for `n ≥ 3` (`CNF.two_rpow_sqrt_sub_one_le_of_any_eval_eq_parity`).

## Main results

* `Cslib.Logic.PL.CNF.card_isolatedInputs_mul_two_rpow_le_of_any`: ORs of formulas of width `k`
  need a formula per `2 ^ ((1 - 1 / k) n)` isolated true inputs.
* `Cslib.Logic.PL.CNF.two_rpow_le_length_of_any_eval_eq_parity`,
  `Cslib.Logic.PL.CNF.exists_any_eval_eq_parity`: parity is an OR of `2 ^ (n / k - 1)` but no
  fewer formulas of width `k`, when `k` divides `n`.
* `Cslib.Logic.PL.CNF.mul_two_rpow_div_le_two_pow_mul_sum_critWidth`: per-input critical-width
  exponential weight bound for an input of weight at most `μ`.
* `Cslib.Logic.PL.CNF.card_isolatedInputs_mul_min_le`,
  `Cslib.Logic.PL.CNF.card_isolatedInputs_mul_rpow_mul_two_rpow_sqrt_le`: ORs of formulas need
  `n ^ (1 / 4) 2 ^ √n / 2 ^ n` formulas and clauses per isolated true input.
* `Cslib.Logic.PL.CNF.rpow_mul_two_rpow_sqrt_sub_one_le_of_any_eval_eq_parity`,
  `Cslib.Logic.PL.DNF.rpow_mul_two_rpow_sqrt_sub_one_le_of_all_eval_eq_parity`: depth-three
  formulas for parity need `n ^ (1 / 4) 2 ^ (√n - 1)` gates.
* `Cslib.Logic.PL.CNF.two_pow_mul_min_le_of_any_eval_eq_parity`,
  `Cslib.Logic.PL.CNF.two_rpow_sqrt_sub_one_le_of_any_eval_eq_parity`: the bound for parity at
  every `μ`, and at `μ = √n`.

## References

* [R. Paturi, P. Pudlák, F. Zane, *Satisfiability Coding Lemma*][PaturiPudlakZane1999]
-/

public section

namespace Cslib.Logic.PL

open Finset Function

variable {n : ℕ}

/-- Dividing `2 ^ (n - 1) a ≤ 2 ^ n b` by `2 ^ n`. -/
private theorem div_two_le_of_two_pow_sub_one_mul_le (hn : 1 ≤ n) {a b : ℝ}
    (h : 2 ^ (n - 1) * a ≤ 2 ^ n * b) : a / 2 ≤ b := by
  rw [show (2 : ℝ) ^ n = 2 ^ (n - 1) * 2 by rw [← pow_succ]; congr 1; omega, mul_assoc] at h
  linarith [le_of_mul_le_mul_left h (by positivity)]

/-- Summing per-formula bounds `#(A φ) c ≤ 2 ^ n` over a cover of `S` by the sets `A φ`. -/
private theorem card_mul_le_length_mul_two_pow {α β : Type*} [DecidableEq α] [DecidableEq β]
    {S : Finset α} {Fs : List β} {A : β → Finset α} {c : ℝ} (hc : 0 ≤ c)
    (hS : S ⊆ Fs.toFinset.biUnion A) (hA : ∀ φ ∈ Fs, #(A φ) * c ≤ 2 ^ n) :
    #S * c ≤ Fs.length * 2 ^ n := by
  have h := sum_le_card_nsmul Fs.toFinset (fun φ => (#(A φ) : ℝ) * c) _
    fun φ hφ => hA φ (List.mem_toFinset.1 hφ)
  rw [← sum_mul, nsmul_eq_mul] at h
  calc (#S : ℝ) * c ≤ (∑ φ ∈ Fs.toFinset, (#(A φ) : ℝ)) * c := by
        gcongr
        exact_mod_cast (card_le_card hS).trans card_biUnion_le
    _ ≤ _ := h.trans (by gcongr; exact_mod_cast List.toFinset_card_le Fs)

/-! ### Bottom fan-in `k` -/

/-- **ORs of formulas of width `k` in conjunctive normal form need many formulas**, by the argument
of [Paturi, Pudlák and Zane, Theorem 6][PaturiPudlakZane1999]: if an OR of formulas whose clauses
have at most `k ≥ 1` literals computes `g`, then each isolated true input of `g` is a solution of
one of them, isolated in every direction, and each of them has at most `2 ^ ((1 - 1 / k) n)` such
solutions (`CNF.card_isolatedInputs_mul_two_rpow_le`). -/
theorem CNF.card_isolatedInputs_mul_two_rpow_le_of_any {k : ℕ} (hk1 : 1 ≤ k)
    {g : BitString n → Bool} {Fs : List (CNF (Fin n))} (hk : ∀ φ ∈ Fs, ∀ c ∈ φ, c.length ≤ k)
    (hFs : ∀ x, (Fs.any fun φ => φ.eval x) = g x) :
    (#(BitString.isolatedInputs g true) : ℝ) *
      2 ^ ((n : ℝ) / k) ≤ Fs.length * 2 ^ n := by
  -- each isolated true input of `g` is a solution of some `φ` isolated in every direction
  refine card_mul_le_length_mul_two_pow (by positivity) (fun x hx => ?_)
    fun φ hφ => CNF.card_isolatedInputs_mul_two_rpow_le hk1 (hk φ hφ)
  obtain ⟨hgx, hiso⟩ := BitString.mem_isolatedInputs.1 hx
  obtain ⟨φ, hφ, hφx⟩ := List.any_eq_true.1 ((hFs x).trans hgx)
  exact mem_biUnion.2 ⟨φ, List.mem_toFinset.2 hφ, BitString.mem_isolatedInputs.2
    ⟨hφx, fun i => Bool.eq_false_iff.2 (List.any_eq_false.1 ((hFs _).trans (hiso i)) φ hφ)⟩⟩

/-- **ORs of formulas of width `k` in conjunctive normal form for parity** of `n ≥ 1` bits have at
least `2 ^ (n / k - 1)` formulas. -/
theorem CNF.two_rpow_le_length_of_any_eval_eq_parity (hn : 1 ≤ n) {k : ℕ} (hk1 : 1 ≤ k)
    {Fs : List (CNF (Fin n))} (hk : ∀ φ ∈ Fs, ∀ c ∈ φ, c.length ≤ k)
    (hFs : ∀ x, (Fs.any fun φ => φ.eval x) = parity n x) :
    (2 : ℝ) ^ ((n : ℝ) / k - 1) ≤ Fs.length := by
  have h := CNF.card_isolatedInputs_mul_two_rpow_le_of_any hk1 hk hFs
  rw [BitString.card_isolatedInputs_parity hn, Nat.cast_pow, Nat.cast_ofNat,
    mul_comm (Fs.length : ℝ)] at h
  rw [Real.rpow_sub_one two_ne_zero]
  exact div_two_le_of_two_pow_sub_one_mul_le hn h

/-- **Parity is an OR of `2 ^ (n / k - 1)` formulas of width `k` in conjunctive normal form** when
`k` divides `n`, after [Paturi, Pudlák and Zane, Lemma 4][PaturiPudlakZane1999]: split the variables
into `n / k` blocks of `k`; for each pattern of block parities with odd total, a formula of width
`k` says that the blocks have these parities. So `two_rpow_le_length_of_any_eval_eq_parity` is
attained. -/
theorem CNF.exists_any_eval_eq_parity {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ∣ n) (hn : 1 ≤ n) :
    ∃ Fs : List (CNF (Fin n)), Fs.length = 2 ^ (n / k - 1) ∧
      (∀ φ ∈ Fs, ∀ c ∈ φ, c.length ≤ k) ∧ ∀ x, (Fs.any fun φ => φ.eval x) = parity n x := by
  have hm : 1 ≤ n / k := (Nat.one_le_div_iff hk1).2 (Nat.le_of_dvd hn hkn)
  -- the blocks of `k` consecutive variables
  let B : Fin (n / k) → Finset (Fin n) := fun j => {i | i.val / k = j.val}
  have hBcard (j : Fin (n / k)) : #(B j) ≤ k :=
    (card_le_card_of_injOn (fun i => ⟨i.val % k, Nat.mod_lt _ hk1⟩) (fun _ _ => mem_univ _)
      fun i hi i' hi' h => Fin.ext <| by
        rw [← Nat.div_add_mod i.val k, ← Nat.div_add_mod i'.val k, (mem_filter.1 hi).2,
          (mem_filter.1 hi').2, Fin.mk.inj h]).trans_eq (card_fin k)
  have hBdisj : ((univ : Finset (Fin (n / k))) : Set (Fin (n / k))).PairwiseDisjoint B :=
    fun j _ j' _ hjj' => disjoint_left.2 fun i hi hi' =>
      hjj' (Fin.ext ((mem_filter.1 hi).2.symm.trans (mem_filter.1 hi').2))
  have hBunion : univ.biUnion B = univ := eq_univ_of_forall fun i =>
    mem_biUnion.2 ⟨⟨i.val / k, Nat.div_lt_div_of_lt_of_dvd hkn i.isLt⟩, mem_univ _,
      mem_filter.2 ⟨mem_univ _, rfl⟩⟩
  -- the formula saying that the blocks have the parities `b`
  let F : BitString (n / k) → CNF (Fin n) := fun b =>
    (List.finRange (n / k)).flatMap fun j => CNF.parityOnEq (B j) (b j)
  have hF (b : BitString (n / k)) (x : BitString n) :
      (F b).eval x = true ↔ ∀ j, parityOn (B j) x = b j := by
    simp [F, CNF.eval_flatMap_eq_true_iff, CNF.eval_parityOnEq_eq_true_iff]
  refine ⟨({b : BitString (n / k) | parity (n / k) b = true} : Finset _).toList.map F, ?_,
    fun φ hφ c hc => ?_, fun x => ?_⟩
  · rw [List.length_map, length_toList, card_filter_parity_eq_true hm]
  · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hφ
    obtain ⟨j, -, hc⟩ := List.mem_flatMap.1 hc
    exact (CNF.length_of_mem_parityOnEq hc).trans_le (hBcard j)
  · change _ = parityOn univ x
    rw [← hBunion, parityOn_biUnion hBdisj, Bool.eq_iff_iff]
    simp only [List.any_map, List.any_eq_true, mem_toList, mem_filter, mem_univ,
      true_and, Function.comp_def, hF, ← funext_iff, exists_eq_right']
    rfl

/-! ### Unbounded bottom fan-in -/

/-- For positive `t₁, …, tₘ` summing to at most `m a` with `0 < a ≤ log 2`, the sum of the
`tᵢ 2 ^ (1 / tᵢ)` is at least `m a 2 ^ (1 / a)`: the tangent to the convex function
`t ↦ t 2 ^ (1 / t)` at `a` has slope `2 ^ (1 / a) (1 - log 2 / a) ≤ 0`. -/
private theorem card_mul_mul_two_rpow_inv_le_sum {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    (ht : ∀ i ∈ s, 0 < t i) {a : ℝ} (ha : 0 < a) (ha2 : a ≤ Real.log 2)
    (hsum : ∑ i ∈ s, t i ≤ #s * a) :
    #s * a * 2 ^ (1 / a) ≤ ∑ i ∈ s, t i * 2 ^ (1 / t i) := by
  set L := Real.log 2
  -- the tangent at `a`, from `exp y ≥ 1 + y`
  have htan : ∀ i ∈ s, 2 ^ (1 / a) * (t i + L - L / a * t i) ≤ t i * 2 ^ (1 / t i) :=
    fun i hi => by
    have hti := ht i hi
    have h1 : (2 : ℝ) ^ (1 / t i) = 2 ^ (1 / a) * 2 ^ (1 / t i - 1 / a) := by
      rw [← Real.rpow_add two_pos]
      ring_nf
    have h2 : 1 + L * (1 / t i - 1 / a) ≤ (2 : ℝ) ^ (1 / t i - 1 / a) := by
      rw [Real.rpow_def_of_pos two_pos]
      linarith [Real.add_one_le_exp (L * (1 / t i - 1 / a))]
    have h3 : t i * (1 + L * (1 / t i - 1 / a)) = t i + L - L / a * t i := by
      field_simp
      ring
    rw [h1, ← h3, mul_left_comm (t i)]
    gcongr
  have hLa : 0 ≤ L / a - 1 := by
    rw [sub_nonneg, le_div_iff₀ ha]
    linarith
  have hkey : (#s : ℝ) * a ≤ ∑ i ∈ s, t i + #s * L - L / a * ∑ i ∈ s, t i := by
    have h := mul_le_mul_of_nonneg_left hsum hLa
    have e : (L / a - 1) * (#s * a) = #s * L - #s * a := by
      field_simp
    nlinarith
  calc #s * a * 2 ^ (1 / a) ≤ 2 ^ (1 / a) * (∑ i ∈ s, t i + #s * L - L / a * ∑ i ∈ s, t i) := by
        rw [mul_comm]
        gcongr
    _ = ∑ i ∈ s, 2 ^ (1 / a) * (t i + L - L / a * t i) := by
        rw [← mul_sum, sum_sub_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
    _ ≤ _ := sum_le_sum htan

/-- For an input `x` of critical-width weight `∑ᵢ 1 / ℓᵢ ≤ μ` (with `0 < μ ≤ n log 2`), the
weighted critical-clause sum `∑ᵢ 1 / (ℓᵢ 2 ^ (n - ℓᵢ))` is at least `μ 2 ^ (n / μ) / 2 ^ n`. -/
theorem CNF.mul_two_rpow_div_le_two_pow_mul_sum_critWidth
    {μ : ℝ} (hμ : 0 < μ) (hμn : μ ≤ n * Real.log 2)
    {φ : CNF (Fin n)} {x : BitString n}
    (hcrit : ∀ i, ∃ c ∈ φ, CNF.Critical x c i)
    (hw : ∑ i, 1 / (φ.critWidth x i : ℝ) ≤ μ) :
    μ * 2 ^ (n / μ) ≤
      2 ^ n * ∑ i : Fin n, 1 / ((φ.critWidth x i : ℝ) * 2 ^ (n - φ.critWidth x i)) := by
  have hn0 : (0 : ℝ) < n :=
    (mul_pos_iff_of_pos_right (Real.log_pos one_lt_two)).1 (hμ.trans_le hμn)
  have hpos : ∀ i, 0 < φ.critWidth x i := fun i => CNF.critWidth_pos (hcrit i)
  have hle : ∀ i, φ.critWidth x i ≤ n := fun i => by
    obtain ⟨c, -, -, hc⟩ := CNF.exists_critical_card_eq_critWidth (hcrit i)
    rw [← hc]
    exact (card_le_univ _).trans_eq (Fintype.card_fin n)
  have htan := card_mul_mul_two_rpow_inv_le_sum (univ : Finset (Fin n))
    (fun i => 1 / (φ.critWidth x i : ℝ)) (fun i _ => one_div_pos.2 (Nat.cast_pos.2 (hpos i)))
    (a := μ / n) (by positivity)
    (by rw [div_le_iff₀ hn0]; linarith)
    (by rw [card_univ, Fintype.card_fin, mul_div_cancel₀ _ hn0.ne']; exact hw)
  rw [card_univ, Fintype.card_fin, mul_div_cancel₀ _ hn0.ne', one_div_div] at htan
  rw [mul_sum]
  refine htan.trans_eq (sum_congr rfl fun i _ => ?_)
  have h2 : (2 : ℝ) ^ n = 2 ^ φ.critWidth x i * 2 ^ (n - φ.critWidth x i) := by
    rw [← pow_add, Nat.add_sub_cancel' (hle i)]
  have hp : (0 : ℝ) < φ.critWidth x i := by exact_mod_cast hpos i
  simp only [one_div_one_div, Real.rpow_natCast, h2]
  field_simp

/-- For any set `P` of input–direction pairs `(x, i)` where `F x ∈ Fs` has a clause critical for `i`
at `x`, the critical-width weights `1 / (ℓ(x, i) 2 ^ (n - ℓ(x, i)))` sum to at most the number of
distinct clauses (as sets of literals) across `Fs`: the pairs sharing a shortest critical clause of
width `v` number at most `v 2 ^ (n - v)` (`CNF.card_filter_critical_prod_le`). -/
private theorem sum_inv_critWidth_mul_two_pow_le_card_clauses
    {Fs : List (CNF (Fin n))} {P : Finset (BitString n × Fin n)}
    {F : BitString n → CNF (Fin n)} (hF : ∀ p ∈ P, F p.1 ∈ Fs)
    (hcrit : ∀ p ∈ P, ∃ c ∈ F p.1, CNF.Critical p.1 c p.2) :
    (∑ p ∈ P,
      1 / (((F p.1).critWidth p.1 p.2 : ℝ) * 2 ^ (n - (F p.1).critWidth p.1 p.2))) ≤
      #(Fs.flatten.map List.toFinset).toFinset := by
  have hcl : ∀ p ∈ P, ∃ c ∈ F p.1, CNF.Critical p.1 c p.2 ∧
      (c.map Prod.fst).toFinset.card = (F p.1).critWidth p.1 p.2 := fun p hp =>
    CNF.exists_critical_card_eq_critWidth (hcrit p hp)
  choose! cl hclF hclc hclw using hcl
  have hvars (c : Clause (Fin n)) : (c.map Prod.fst).toFinset = c.toFinset.image Prod.fst := by
    ext
    simp
  have hmaps : ∀ p ∈ P, (cl p).toFinset ∈ (Fs.flatten.map List.toFinset).toFinset := fun p hp =>
    List.mem_toFinset.2 (List.mem_map.2 ⟨cl p, List.mem_flatten.2 ⟨F p.1, hF p hp, hclF p hp⟩, rfl⟩)
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine (sum_le_sum fun C _ => ?_).trans_eq (by rw [sum_const, nsmul_eq_mul, mul_one])
  rcases ({p ∈ P | (cl p).toFinset = C} : Finset _).eq_empty_or_nonempty with he | ⟨p₀, hp₀⟩
  · rw [he, sum_empty]; exact zero_le_one
  obtain ⟨hp₀P, hp₀C⟩ := mem_filter.1 hp₀
  set v := ((cl p₀).map Prod.fst).toFinset.card
  have hℓ : ∀ p ∈ ({p ∈ P | (cl p).toFinset = C} : Finset _),
      (F p.1).critWidth p.1 p.2 = v := fun p hp => by
    obtain ⟨hpP, hpC⟩ := mem_filter.1 hp
    rw [← hclw p hpP, hvars, hpC, ← hp₀C, ← hvars]
  have hv : 0 < v := hℓ p₀ hp₀ ▸ CNF.critWidth_pos (hcrit p₀ hp₀P)
  have hfib : #{p ∈ P | (cl p).toFinset = C} ≤ v * 2 ^ (n - v) := by
    refine (card_le_card fun p hp => ?_).trans (CNF.card_filter_critical_prod_le (cl p₀))
    obtain ⟨hpP, hpC⟩ := mem_filter.1 hp
    refine mem_filter.2 ⟨mem_univ _, (CNF.critical_congr fun l => ?_).1 (hclc p hpP)⟩
    rw [← List.mem_toFinset, ← List.mem_toFinset (l := cl p₀), hpC, hp₀C]
  rw [sum_congr rfl fun p hp => show
      1 / (((F p.1).critWidth p.1 p.2 : ℝ) * 2 ^ (n - (F p.1).critWidth p.1 p.2)) =
        1 / ((v : ℝ) * 2 ^ (n - v)) by rw [hℓ p hp],
    sum_const, nsmul_eq_mul, mul_one_div,
    div_le_one (mul_pos (Nat.cast_pos.2 hv) (by positivity))]
  exact_mod_cast hfib

/-- **ORs of formulas in conjunctive normal form need many gates per isolated true input**, by the
argument of [Paturi, Pudlák and Zane, Theorem 6][PaturiPudlakZane1999]: if an OR of `m` formulas
with `K` distinct clauses (as sets of literals) computes `g`, then each isolated true input of `g`
is a solution of one of them, isolated in every direction, and if there are `s` of them then
`s min (2 ^ μ) (μ 2 ^ (n / μ)) ≤ 2 ^ n (m + K)` for every `0 < μ ≤ n log 2`. A depth-three circuit
with an OR at the top, AND gates in the middle and OR gates of literals at the bottom has at least
`m + K` gates, as sharing bottom gates only lowers `K`. -/
theorem CNF.card_isolatedInputs_mul_min_le {μ : ℝ} (hμ : 0 < μ) (hμn : μ ≤ n * Real.log 2)
    {g : BitString n → Bool} {Fs : List (CNF (Fin n))}
    (hFs : ∀ x, (Fs.any fun φ => φ.eval x) = g x) :
    (#(BitString.isolatedInputs g true) : ℝ) *
      min (2 ^ μ) (μ * 2 ^ (n / μ)) ≤
      2 ^ n * (Fs.length + #(Fs.flatten.map List.toFinset).toFinset) := by
  set S := BitString.isolatedInputs g true
  -- each isolated true input is a solution of one of the formulas, isolated in every direction
  have hchoose : ∀ x ∈ S, ∃ φ ∈ Fs, φ.eval x = true := fun x hx =>
    List.any_eq_true.1 ((hFs x).trans (BitString.mem_isolatedInputs.1 hx).1)
  choose! F hF hFx using hchoose
  have hcrit : ∀ x ∈ S, ∀ i, ∃ c ∈ F x, CNF.Critical x c i := fun x hx i =>
    CNF.exists_critical (hFx x hx) <| Bool.eq_false_iff.2 <| List.any_eq_false.1
      ((hFs _).trans ((BitString.mem_isolatedInputs.1 hx).2 i)) _ (hF x hx)
  set w : BitString n → ℝ := fun x => ∑ i, 1 / ((F x).critWidth x i : ℝ)
  set S₁ := S.filter fun x => μ ≤ w x
  set S₂ := S.filter fun x => ¬ μ ≤ w x
  set Cl := (Fs.flatten.map List.toFinset).toFinset
  -- inputs of weight at least `μ`: each formula has few solutions of large weight
  have h₁ : (#S₁ : ℝ) * 2 ^ μ ≤ Fs.length * 2 ^ n :=
    card_mul_le_length_mul_two_pow (by positivity)
      (fun x hx => mem_biUnion.2 ⟨F x, List.mem_toFinset.2 (hF x (mem_filter.1 hx).1),
        mem_filter.2 ⟨mem_univ _, hFx x (mem_filter.1 hx).1, (mem_filter.1 hx).2⟩⟩)
      fun φ _ => CNF.card_filter_le_sum_inv_critWidth_mul_two_rpow_le φ μ
  -- inputs of weight below `μ`: their shortest critical clauses are many
  have h₂ : (#S₂ : ℝ) * (μ * 2 ^ (n / μ)) ≤ #Cl * 2 ^ n := by
    have ha := sum_inv_critWidth_mul_two_pow_le_card_clauses (P := S₂ ×ˢ univ) (F := F)
      (fun p hp => hF p.1 (mem_filter.1 (mem_product.1 hp).1).1)
      (fun p hp => hcrit p.1 (mem_filter.1 (mem_product.1 hp).1).1 p.2)
    have hb := card_nsmul_le_sum S₂ _ _ fun x hx =>
      CNF.mul_two_rpow_div_le_two_pow_mul_sum_critWidth hμ hμn (hcrit x (mem_filter.1 hx).1)
        (not_le.1 (mem_filter.1 hx).2).le
    rw [sum_product] at ha
    rw [nsmul_eq_mul, ← mul_sum] at hb
    rw [mul_comm (#Cl : ℝ)]
    exact hb.trans (mul_le_mul_of_nonneg_left ha (by positivity))
  -- the isolated true inputs split into the two kinds
  have hS : (#S₁ : ℝ) + #S₂ = #S := by
    exact_mod_cast card_filter_add_card_filter_not (s := S) (fun x => μ ≤ w x)
  rw [← hS, add_mul]
  linarith [mul_le_mul_of_nonneg_left (min_le_left (2 ^ μ) (μ * 2 ^ (n / μ))) (#S₁).cast_nonneg,
    mul_le_mul_of_nonneg_left (min_le_right (2 ^ μ) (μ * 2 ^ (n / μ))) (#S₂).cast_nonneg]

/-- **ORs of formulas in conjunctive normal form for parity need many gates**: if an OR of `m`
formulas with `K` distinct clauses computes the parity of `n ≥ 1` bits, all of whose `2 ^ (n - 1)`
true inputs are isolated, then `2 ^ (n - 1) min (2 ^ μ) (μ 2 ^ (n / μ)) ≤ 2 ^ n (m + K)` for every
`0 < μ ≤ n log 2`. -/
theorem CNF.two_pow_mul_min_le_of_any_eval_eq_parity (hn : 1 ≤ n) {μ : ℝ} (hμ : 0 < μ)
    (hμn : μ ≤ n * Real.log 2) {Fs : List (CNF (Fin n))}
    (hFs : ∀ x, (Fs.any fun φ => φ.eval x) = parity n x) :
    (2 : ℝ) ^ (n - 1) * min (2 ^ μ) (μ * 2 ^ (n / μ)) ≤
      2 ^ n * (Fs.length + #(Fs.flatten.map List.toFinset).toFinset) := by
  have h := CNF.card_isolatedInputs_mul_min_le hμ hμn hFs
  rwa [BitString.card_isolatedInputs_parity hn, Nat.cast_pow, Nat.cast_ofNat] at h

/-- **ORs of formulas in conjunctive normal form for parity need `2 ^ (√n - 1)` gates**, taking
`μ = √n` in `CNF.two_pow_mul_min_le_of_any_eval_eq_parity`: an OR of `m` formulas with `K` distinct
clauses computing the parity of `n ≥ 3` bits has `2 ^ (√n - 1) ≤ m + K`. For `n ≥ 4` this is
weaker than `CNF.rpow_mul_two_rpow_sqrt_sub_one_le_of_any_eval_eq_parity` by the factor
`n ^ (1 / 4)`. -/
theorem CNF.two_rpow_sqrt_sub_one_le_of_any_eval_eq_parity (hn : 3 ≤ n)
    {Fs : List (CNF (Fin n))} (hFs : ∀ x, (Fs.any fun φ => φ.eval x) = parity n x) :
    (2 : ℝ) ^ (√(n : ℝ) - 1) ≤ Fs.length + #(Fs.flatten.map List.toFinset).toFinset := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsqsq : √(n : ℝ) * √n = n := Real.mul_self_sqrt (by linarith)
  have h1 : 1 ≤ √(n : ℝ) := Real.one_le_sqrt.2 (by linarith)
  -- `√n ≤ n log 2`, as `√n ≥ 1.7` and `log 2 > 0.69`
  have hμn : √(n : ℝ) ≤ n * Real.log 2 := by
    have h17 : (1.7 : ℝ) ≤ √n := (Real.le_sqrt (by norm_num) (by linarith)).2 (by linarith)
    nlinarith [Real.log_two_gt_d9]
  have h := CNF.two_pow_mul_min_le_of_any_eval_eq_parity (by omega) hsq hμn hFs
  rw [Real.div_sqrt, min_eq_left (le_mul_of_one_le_left (by positivity) h1)] at h
  rw [Real.rpow_sub_one two_ne_zero]
  exact div_two_le_of_two_pow_sub_one_mul_le (by omega) h

/-- **An OR of formulas in conjunctive normal form spends `n ^ (1 / 4) 2 ^ √n / 2 ^ n` gates per
isolated true input**, as in [Paturi, Pudlák and Zane, Theorem 6][PaturiPudlakZane1999]: an OR of
`m` formulas with `K` distinct clauses computing a function `g` of `n ≥ 4` bits with `s` isolated
true inputs has `s n ^ (1 / 4) 2 ^ √n ≤ 2 ^ n (m + K)`. Take `μ = √n + (log₂ n) / 4` in
`CNF.card_isolatedInputs_mul_min_le`: then `2 ^ μ = n ^ (1 / 4) 2 ^ √n`, and
`n / μ ≥ √n - (log₂ n) / 4` gives `μ 2 ^ (n / μ) ≥ √n 2 ^ √n / n ^ (1 / 4) = n ^ (1 / 4) 2 ^ √n`. -/
theorem CNF.card_isolatedInputs_mul_rpow_mul_two_rpow_sqrt_le (hn : 4 ≤ n)
    {g : BitString n → Bool} {Fs : List (CNF (Fin n))}
    (hFs : ∀ x, (Fs.any fun φ => φ.eval x) = g x) :
    (#(BitString.isolatedInputs g true) : ℝ) *
      (n ^ (1 / 4 : ℝ) * 2 ^ √(n : ℝ)) ≤
      2 ^ n * (Fs.length + #(Fs.flatten.map List.toFinset).toFinset) := by
  have hL := Real.log_two_gt_d9
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hs2 : 2 ≤ √(n : ℝ) := (Real.le_sqrt (by norm_num) (by positivity)).2 (by linarith)
  have hss : √(n : ℝ) * √n = n := Real.mul_self_sqrt (by positivity)
  -- `b = (log₂ n) / 4`, with `2 ^ b = n ^ (1 / 4)` and `(n ^ (1 / 4)) ^ 2 = √n`
  set b := Real.log n / (4 * Real.log 2)
  have hbL : b * (4 * Real.log 2) = Real.log n := div_mul_cancel₀ _ (by positivity)
  have hb0 : 0 ≤ b := div_nonneg (Real.log_nonneg (by linarith)) (by positivity)
  have h2b : (2 : ℝ) ^ b = n ^ (1 / 4 : ℝ) := by
    rw [Real.rpow_def_of_pos two_pos, Real.rpow_def_of_pos (by positivity), ← hbL]
    ring_nf
  have hsq : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = √n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by positivity)]
    norm_num
  -- `μ ≤ n log 2`, as `log n = 2 log √n ≤ 2 (√n - 1)`
  have hlog : Real.log n ≤ 2 * (√n - 1) := by
    have h := Real.log_le_sub_one_of_pos (x := √(n : ℝ)) (by positivity)
    rw [Real.log_sqrt (by positivity)] at h
    linarith
  have hμn : √(n : ℝ) + b ≤ n * Real.log 2 := by
    have hf : 0 ≤ 2 * Real.log 2 ^ 2 * (√n + 2) - 2 * Real.log 2 - 1 := by nlinarith
    have := mul_nonneg (sub_nonneg.2 hs2) hf
    refine le_of_mul_le_mul_left ?_ (mul_pos zero_lt_four (Real.log_pos one_lt_two))
    conv_rhs => rw [← hss]
    nlinarith
  have h := CNF.card_isolatedInputs_mul_min_le (μ := √n + b) (by positivity) hμn hFs
  refine le_trans ?_ h
  gcongr
  refine le_min (by rw [Real.rpow_add two_pos, h2b, mul_comm]) ?_
  have hexp : √(n : ℝ) - b ≤ n / (√n + b) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  calc (n : ℝ) ^ (1 / 4 : ℝ) * 2 ^ √(n : ℝ)
      = (n ^ (1 / 4 : ℝ)) ^ 2 * (2 ^ √(n : ℝ) / n ^ (1 / 4 : ℝ)) := by
        field_simp
    _ = √n * 2 ^ (√n - b) := by rw [hsq, Real.rpow_sub two_pos, h2b]
    _ ≤ (√n + b) * 2 ^ (n / (√n + b)) := by
        gcongr <;> linarith

/-- **ORs of formulas in conjunctive normal form for parity need `n ^ (1 / 4) 2 ^ (√n - 1)`
gates**, [Paturi, Pudlák and Zane, Theorem 6][PaturiPudlakZane1999]: an OR of `m` formulas with
`K` distinct clauses computing the parity of `n ≥ 4` bits has `n ^ (1 / 4) 2 ^ (√n - 1) ≤ m + K`,
as all `2 ^ (n - 1)` true inputs of parity are isolated. -/
theorem CNF.rpow_mul_two_rpow_sqrt_sub_one_le_of_any_eval_eq_parity (hn : 4 ≤ n)
    {Fs : List (CNF (Fin n))} (hFs : ∀ x, (Fs.any fun φ => φ.eval x) = parity n x) :
    (n : ℝ) ^ (1 / 4 : ℝ) * 2 ^ (√(n : ℝ) - 1) ≤
      Fs.length + #(Fs.flatten.map List.toFinset).toFinset := by
  have h := CNF.card_isolatedInputs_mul_rpow_mul_two_rpow_sqrt_le hn hFs
  rw [BitString.card_isolatedInputs_parity (by omega), Nat.cast_pow, Nat.cast_ofNat] at h
  rw [Real.rpow_sub_one two_ne_zero, ← mul_div_assoc]
  exact div_two_le_of_two_pow_sub_one_mul_le (by omega) h

/-- **ANDs of formulas in disjunctive normal form for parity need `n ^ (1 / 4) 2 ^ (√n - 1)`
gates**, the dual case of [Paturi, Pudlák and Zane, Theorem 6][PaturiPudlakZane1999]: an AND of
`m` formulas with `K` distinct terms computing the parity of `n ≥ 4` bits has
`n ^ (1 / 4) 2 ^ (√n - 1) ≤ m + K`. Negating it gives an OR of `m` formulas in conjunctive normal
form with at most `K` distinct clauses computing the negation of parity, all of whose
`2 ^ (n - 1)` true inputs are isolated. -/
theorem DNF.rpow_mul_two_rpow_sqrt_sub_one_le_of_all_eval_eq_parity (hn : 4 ≤ n)
    {Gs : List (DNF (Fin n))} (hGs : ∀ x, (Gs.all fun ψ => ψ.eval x) = parity n x) :
    (n : ℝ) ^ (1 / 4 : ℝ) * 2 ^ (√(n : ℝ) - 1) ≤
      Gs.length + #(Gs.flatten.map List.toFinset).toFinset := by
  have hFs (x : BitString n) : ((Gs.map DNF.negate).any fun φ => φ.eval x) = !parity n x := by
    rw [← hGs x, List.any_map, Bool.eq_iff_iff]
    simp [List.any_eq_true]
  have h := CNF.card_isolatedInputs_mul_rpow_mul_two_rpow_sqrt_le hn hFs
  rw [BitString.isolatedInputs_not, BitString.card_isolatedInputs_parity (by omega), Nat.cast_pow,
    Nat.cast_ofNat] at h
  -- negating the terms does not merge them
  have hK : #((Gs.map DNF.negate).flatten.map List.toFinset).toFinset ≤
      #(Gs.flatten.map List.toFinset).toFinset := by
    refine (card_le_card fun C hC => ?_).trans (card_image_le (f := image fun l => (l.1, !l.2)))
    simp only [List.mem_toFinset, List.mem_map, List.mem_flatten, DNF.negate] at hC
    obtain ⟨_, ⟨_, ⟨ψ, hψ, rfl⟩, hc⟩, rfl⟩ := hC
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hc
    exact mem_image.2 ⟨t.toFinset, List.mem_toFinset.2 (List.mem_map.2
      ⟨t, List.mem_flatten.2 ⟨ψ, hψ, ht⟩, rfl⟩), by ext; simp [Term.negate]⟩
  rw [Real.rpow_sub_one two_ne_zero, ← mul_div_assoc]
  refine (div_two_le_of_two_pow_sub_one_mul_le (by omega) h).trans ?_
  rw [List.length_map]
  gcongr

end Cslib.Logic.PL
