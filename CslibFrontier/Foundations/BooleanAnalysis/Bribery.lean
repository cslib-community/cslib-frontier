/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Resilience
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CslibFrontier.Foundations.BooleanAnalysis.CoalitionalInfluence
import CslibFrontier.Foundations.BooleanAnalysis.Decomposition
import CslibFrontier.Foundations.BooleanAnalysis.KahnKalaiLinial
import CslibFrontier.Foundations.BooleanAnalysis.Monotone
import CslibFrontier.Foundations.BooleanAnalysis.Variance
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Tactic.Linarith

/-!
# Bribing monotone elections

A monotone Boolean function `f` on `n` voters is an election scheme. Read as signs, its mean is the
bias of the election, and bribing a set `J` of voters to vote `false` (the sign `1`) replaces `f` by
`x ↦ f(J.piecewise (fun _ => false) x)`, which the book writes `f_{J̄|(1,…,1)}` (its
Definition 3.18, with the complement `J̄` free). Fixing one voter `i` to `false` moves
the mean of any function by its Fourier coefficient on `{i}` (`BitString.expect_update_false`),
which for a monotone function is the influence `Infᵢ[f]`, and the variance of a function with values
`±1` and mean `μ` is `1 - μ²` (`BitString.expect_sub_expect_sq_signVal`). Bribing voters of maximum
influence one at a time, the Kahn–Kalai–Linial theorem shows that `O(n / log n)` voters suffice to
push a mean of at least `-a` up to at least `a`, for any constant `0 ≤ a < 1`
(`BitString.exists_card_le_and_le_expect_signVal_piecewise_false`), and symmetrically for bribes to
vote `true` (`BitString.exists_card_le_and_expect_signVal_piecewise_true_le`)
[O'Donnell, Proposition 9.27][ODonnell2014]. The book takes `a = .99`. Each bribe of a voter of
maximum influence raises the mean `m` by at least `(1 - m²) log n / (4 n)`
(`BitString.exists_add_le_expect_signVal_piecewise_insert`). Tracking `1 + m` while `m < 0` and
`1 - m` once `m ≥ 0`, which grow and shrink geometrically, `O(log (2 / (ε δ)) n / log n)` bribes
make the mean at least `1 - ε` for a function of variance at least `δ`
(`BitString.exists_card_le_and_one_sub_le_expect_signVal_piecewise_false`)
[O'Donnell, Exercise 9.27(a)][ODonnell2014]. The book asks for `0 < ε < 1 / 2` and
`O(log (1 / (ε δ)) n / log n)` bribes; the bounds here are explicit, hold for `0 < ε ≤ 1`, use
`log (2 / (ε δ))` so that they stay true up to `ε = δ = 1`, and need `n ≥ 2` so that `log n > 0`.

Joining a coalition that forces `false` and one that forces `true` gives a coalition of
`O(log (2 / (ε δ)) n / log n)` voters whose coalitional influence (`BitString.coalitionInfluence`,
see `BitString.coalitionInfluenceToward`) is at least `1 - ε`
(`BitString.exists_card_le_and_one_sub_le_coalitionInfluence`)
[O'Donnell, Exercise 9.27(b)][ODonnell2014].

## Main results

* `Cslib.BitString.exists_add_le_expect_signVal_piecewise_insert`: one bribe.
* `Cslib.BitString.exists_card_le_and_le_expect_signVal_piecewise_false`,
  `Cslib.BitString.exists_card_le_and_expect_signVal_piecewise_true_le`: Proposition 9.27.
* `Cslib.BitString.exists_card_le_and_one_sub_le_expect_signVal_piecewise_false`,
  `Cslib.BitString.exists_card_le_and_expect_signVal_piecewise_true_le_sub_one`: Exercise 9.27(a).
* `Cslib.BitString.exists_card_le_and_one_sub_le_coalitionInfluence`: Exercise 9.27(b).

## Usage

Open `Cslib.BitString` and write `n` for `Fintype.card ι`. An election is a function
`f : (ι → Bool) → Bool` that is `Monotone` for Mathlib's coordinatewise order with
`false < true`, read as signs through `fun x => signVal (f x)` (`signVal true = -1`); the book's
vote `1` is `false`. Bribing `J` to vote `false` is `fun x => f (J.piecewise (fun _ => false) x)`.
Every theorem takes `hf : Monotone f`, and all but the one-bribe step take
`hn : 2 ≤ Fintype.card ι`.

* Proposition 9.27: for `0 ≤ a < 1` and `-a ≤ 𝔼 x, signVal (f x)`,
  `Cslib.BitString.exists_card_le_and_le_expect_signVal_piecewise_false` gives `J` with
  `#J ≤ 8 a n / ((1 - a²) log n) + 1` after which the mean is at least `a`; the book's case is
  `a = .99`. `Cslib.BitString.exists_card_le_and_expect_signVal_piecewise_true_le` bribes toward
  `true`.
* The step `Cslib.BitString.exists_add_le_expect_signVal_piecewise_insert` raises a mean `m` by
  `(1 - m²) log n / (4 n)`. The constant `1/4` is that of the Kahn–Kalai–Linial theorem
  `Cslib.BitString.exists_expect_sub_expect_sq_mul_log_card_div_le_influence` in
  `CslibFrontier.Foundations.BooleanAnalysis.KahnKalaiLinial`, and fixing one voter moves the mean
  by its coefficient on `{i}` (`Cslib.BitString.expect_update_false` in
  `CslibFrontier.Foundations.BooleanAnalysis.Decomposition`).
* Exercise 9.27(a): with `0 < δ ≤ 𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2` and
  `0 < ε ≤ 1`, `Cslib.BitString.exists_card_le_and_one_sub_le_expect_signVal_piecewise_false` and
  `Cslib.BitString.exists_card_le_and_expect_signVal_piecewise_true_le_sub_one` reach mean
  `1 - ε` or `ε - 1` with at most `8 n log (2 / (ε δ)) / log n + 2` bribes.
* Exercise 9.27(b): `Cslib.BitString.exists_card_le_and_one_sub_le_coalitionInfluence` joins the
  two bribed sets into a coalition of at most `16 n log (2 / (ε δ)) / log n + 4` voters whose
  `coalitionInfluence (Probability.PMF.uniformOfFintype (ι → Bool)) J f` (from
  `CslibFrontier.Probability.Resilience`) is at least `1 - ε`. The directed influences it adds up
  are in `CslibFrontier.Foundations.BooleanAnalysis.CoalitionalInfluence`.

The checked client
[CslibFrontierTests/BooleanAnalysisBribery.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisBribery.lean)
applies every theorem to the conjunction of two voters `threshold 2 2` and the majority of three
voters, and checks for each bribed set or coalition that the empty set fails, so the set provided
is nonempty.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Duality -/

omit [Fintype ι] [DecidableEq ι] in
/-- The dual `x ↦ ¬f(¬x)` of a monotone function is monotone. -/
private theorem monotone_dual {f : (ι → Bool) → Bool} (hf : Monotone f) :
    Monotone fun x : ι → Bool => !f fun j => !x j :=
  fun _ _ hxy => compl_le_compl (hf fun j => compl_le_compl (hxy j))

omit [Fintype ι] in
/-- Bribing `J` to vote `false` in the dual is bribing `J` to vote `true` in `f`. -/
private theorem dual_piecewise_false (f : (ι → Bool) → Bool) (J : Finset ι) (x : ι → Bool) :
    (!f fun j => !(J.piecewise (fun _ => false) x) j) =
      !f (J.piecewise (fun _ => true) fun j => !x j) := by
  congr 2
  funext j
  by_cases hj : j ∈ J <;> simp [piecewise, hj]

/-- **One bribe**, from the proof of [O'Donnell, Proposition 9.27][ODonnell2014]: for monotone `f`
on `n` voters and any bribed set `J`, writing `m(J)` for the mean of `f` read as signs after `J`
votes `false`, some voter `i` has `m(J ∪ {i}) ≥ m(J) + (1 - m(J)²) log n / (4 n)`. Fixing `i`
raises the mean by the influence of `i`, and the Kahn–Kalai–Linial theorem gives a voter of
influence at least the variance `1 - m(J)²` times `log n / (4 n)`. -/
theorem exists_add_le_expect_signVal_piecewise_insert [Nonempty ι] {f : (ι → Bool) → Bool}
    (hf : Monotone f) (J : Finset ι) :
    ∃ i, (𝔼 x, signVal (f (J.piecewise (fun _ => false) x))) +
        (1 - (𝔼 x, signVal (f (J.piecewise (fun _ => false) x))) ^ 2) *
          log (Fintype.card ι) / (4 * Fintype.card ι) ≤
      𝔼 x, signVal (f ((insert i J).piecewise (fun _ => false) x)) := by
  set g : (ι → Bool) → Bool := fun x => f (J.piecewise (fun _ => false) x)
  have hg : Monotone g := fun x y hxy => hf fun j => by
    by_cases hj : j ∈ J <;> simp [piecewise, hj, hxy j]
  obtain ⟨i, hi⟩ := exists_expect_sub_expect_sq_mul_log_card_div_le_influence g
  rw [expect_sub_expect_sq_signVal] at hi
  have hpw (x : ι → Bool) : (insert i J).piecewise (fun _ => false) x =
      J.piecewise (fun _ => false) (Function.update x i false) := by
    funext j
    by_cases hji : j = i
    · subst hji
      simp [piecewise]
    · by_cases hj : j ∈ J <;> simp [piecewise, hj, hji]
  refine ⟨i, ?_⟩
  simp only [hpw]
  rw [expect_update_false (fun x => signVal (g x)) i,
    ← influence_eq_fourierCoeff_singleton_of_monotone hg]
  linarith

/-- **Bribing a monotone election** [O'Donnell, Proposition 9.27][ODonnell2014]: let `f` be
monotone on `n ≥ 2` voters, read as signs, with mean `𝔼 f ≥ -a` for some `0 ≤ a < 1`. Then some
set `J` of at most `8 a n / ((1 - a²) log n) + 1 = O(n / log n)` voters, when bribed to vote
`false` (the sign `1`), makes the mean at least `a`. Bribe a voter of maximum influence, one at a
time: while the mean lies in `[-a, a)` the variance is at least `1 - a²`, so each bribe raises the
mean by at least `(1 - a²) log n / (4 n)` (`exists_add_le_expect_signVal_piecewise_insert`). -/
theorem exists_card_le_and_le_expect_signVal_piecewise_false {f : (ι → Bool) → Bool}
    (hf : Monotone f) (hn : 2 ≤ Fintype.card ι) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hμ : -a ≤ 𝔼 x, signVal (f x)) :
    ∃ J : Finset ι, (#J : ℝ) ≤ 8 * a * Fintype.card ι / ((1 - a ^ 2) * log (Fintype.card ι)) + 1 ∧
      a ≤ 𝔼 x, signVal (f (J.piecewise (fun _ => false) x)) := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  set n : ℝ := (Fintype.card ι : ℝ)
  have hlog : 0 < log n := log_pos (Nat.one_lt_cast.2 hn)
  have ha2 : 0 < 1 - a ^ 2 := by nlinarith
  set c := (1 - a ^ 2) * log n / (4 * n)
  have hc : 0 < c := by positivity
  set m : Finset ι → ℝ := fun J => 𝔼 x, signVal (f (J.piecewise (fun _ => false) x))
  have hstep (k : ℕ) : ∃ J : Finset ι, #J ≤ k ∧ (a ≤ m J ∨ -a + k * c ≤ m J) := by
    induction k with
    | zero => exact ⟨∅, by simp, Or.inr (by simpa [m] using hμ)⟩
    | succ k ih =>
      obtain ⟨J, hJ, hJm⟩ := ih
      by_cases haJ : a ≤ m J
      · exact ⟨J, hJ.trans k.le_succ, Or.inl haJ⟩
      have hlow : -a + k * c ≤ m J := hJm.resolve_left haJ
      replace haJ := not_le.1 haJ
      obtain ⟨i, hi⟩ := exists_add_le_expect_signVal_piecewise_insert hf J
      have hci : c ≤ (1 - m J ^ 2) * log n / (4 * n) := by
        have hmsq : m J ^ 2 ≤ a ^ 2 := by nlinarith [mul_nonneg (k.cast_nonneg (α := ℝ)) hc.le]
        simp only [c]
        gcongr
      refine ⟨insert i J, (card_insert_le i J).trans (by omega), Or.inr ?_⟩
      push_cast
      linarith
  obtain ⟨J, hJ, hJm⟩ := hstep ⌈2 * a / c⌉₊
  have hk : 2 * a ≤ ⌈2 * a / c⌉₊ * c := by
    rw [← div_le_iff₀ hc]
    exact Nat.le_ceil _
  refine ⟨J, ?_, hJm.elim id fun h => by linarith⟩
  calc (#J : ℝ) ≤ ⌈2 * a / c⌉₊ := by exact_mod_cast hJ
    _ ≤ 2 * a / c + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    _ = _ := by
        simp only [c]
        field_simp
        ring

/-- **Bribing a monotone election the other way** [O'Donnell, Proposition 9.27][ODonnell2014]: if
`f` is monotone on `n ≥ 2` voters with mean `𝔼 f ≤ a` for some `0 ≤ a < 1`, then some set `J` of at
most `8 a n / ((1 - a²) log n) + 1` voters, when bribed to vote `true` (the sign `-1`), makes the
mean at most `-a`. This is `exists_card_le_and_le_expect_signVal_piecewise_false` for the dual
`x ↦ ¬f(¬x)`. -/
theorem exists_card_le_and_expect_signVal_piecewise_true_le {f : (ι → Bool) → Bool}
    (hf : Monotone f) (hn : 2 ≤ Fintype.card ι) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hμ : 𝔼 x, signVal (f x) ≤ a) :
    ∃ J : Finset ι, (#J : ℝ) ≤ 8 * a * Fintype.card ι / ((1 - a ^ 2) * log (Fintype.card ι)) + 1 ∧
      𝔼 x, signVal (f (J.piecewise (fun _ => true) x)) ≤ -a := by
  obtain ⟨J, hJ, hJm⟩ := exists_card_le_and_le_expect_signVal_piecewise_false (monotone_dual hf)
    hn ha0 ha1 (by simpa [Fintype.expect_comp_not (fun x => signVal (f x))] using neg_le_neg hμ)
  refine ⟨J, hJ, ?_⟩
  simp only [dual_piecewise_false, signVal_not, expect_neg_distrib,
    Fintype.expect_comp_not (fun x => signVal (f (J.piecewise (fun _ => true) x)))] at hJm
  linarith

omit [Fintype ι] in
/-- The first phase of the proof of [O'Donnell, Exercise 9.27(a)][ODonnell2014]: if every
bribe can raise a mean `m ≥ -1` to at least `m + (1 - m²) c`, then while `m < 0` each bribe
multiplies `1 + m` by at least `1 + c`, so from `1 + m ≥ δ / 2` at most `2 log (2 / δ) / c + 1`
bribes make `m ≥ 0`. -/
private theorem exists_card_le_and_nonneg_of_step {m : Finset ι → ℝ} {c δ : ℝ} (hc : 0 < c)
    (hc1 : c ≤ 1) (hm : ∀ J, -1 ≤ m J)
    (hstep : ∀ J, ∃ i, m J + (1 - m J ^ 2) * c ≤ m (insert i J)) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hstart : δ / 2 ≤ 1 + m ∅) :
    ∃ J : Finset ι, (#J : ℝ) ≤ 2 * log (2 / δ) / c + 1 ∧ 0 ≤ m J := by
  have hA (k : ℕ) : ∃ J : Finset ι, #J ≤ k ∧ (0 ≤ m J ∨ (1 + c) ^ k * (1 + m ∅) ≤ 1 + m J) := by
    induction k with
    | zero => exact ⟨∅, by simp, Or.inr (by simp)⟩
    | succ k ih =>
      obtain ⟨J, hJ, hJm⟩ := ih
      by_cases h0 : 0 ≤ m J
      · exact ⟨J, hJ.trans k.le_succ, Or.inl h0⟩
      have hlow := hJm.resolve_left h0
      obtain ⟨i, hi⟩ := hstep J
      refine ⟨insert i J, (card_insert_le i J).trans (by omega), Or.inr ?_⟩
      have h1 := hm J
      have hgrow : (1 + m J) * (1 + c) ≤ 1 + m (insert i J) := by
        nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + m J) (by linarith : 0 ≤ -m J)]
      calc (1 + c) ^ (k + 1) * (1 + m ∅) = (1 + c) ^ k * (1 + m ∅) * (1 + c) := by ring
        _ ≤ (1 + m J) * (1 + c) := by gcongr
        _ ≤ _ := hgrow
  have hlogc : c / 2 ≤ log (1 + c) := by
    have := one_sub_inv_le_log_of_pos (show 0 < 1 + c by linarith)
    have hc' : c / 2 ≤ 1 - (1 + c)⁻¹ := by
      rw [show 1 - (1 + c)⁻¹ = c / (1 + c) by field_simp; ring]
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith
    linarith
  have hlc : 0 < log (1 + c) := by linarith
  set k := ⌈log (2 / δ) / log (1 + c)⌉₊
  have hlogδ : 0 ≤ log (2 / δ) := log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  obtain ⟨J, hJ, hJm⟩ := hA k
  refine ⟨J, ?_, hJm.elim id fun h => ?_⟩
  · refine (Nat.cast_le.2 hJ).trans <| (Nat.ceil_lt_add_one (div_nonneg hlogδ hlc.le)).le.trans ?_
    have : log (2 / δ) / log (1 + c) ≤ 2 * log (2 / δ) / c := by
      rw [div_le_div_iff₀ hlc hc]
      nlinarith [mul_le_mul_of_nonneg_left hlogc hlogδ]
    linarith
  · have hpow : 2 / δ ≤ (1 + c) ^ k := by
      rw [← exp_log (show 0 < 2 / δ by positivity), ← exp_log (show 0 < (1 + c) by linarith),
        ← exp_natCast_mul]
      refine exp_le_exp.2 ?_
      rw [← div_le_iff₀ hlc]
      exact Nat.le_ceil _
    have : 1 ≤ (1 + c) ^ k * (1 + m ∅) := by
      calc (1 : ℝ) = 2 / δ * (δ / 2) := by field_simp
        _ ≤ _ := by gcongr
    linarith

omit [Fintype ι] in
/-- The second phase of the proof of [O'Donnell, Exercise 9.27(a)][ODonnell2014]: if every
bribe can raise a mean `m ≤ 1` to at least `m + (1 - m²) c`, then once `m ≥ 0` each bribe
multiplies `1 - m` by at most `1 - c`, so at most `log (1 / ε) / c + 1` more bribes make
`m ≥ 1 - ε`. -/
private theorem exists_card_le_and_one_sub_le_of_step {m : Finset ι → ℝ} {c ε : ℝ} (hc : 0 < c)
    (hc1 : c ≤ 1) (hm : ∀ J, m J ≤ 1)
    (hstep : ∀ J, ∃ i, m J + (1 - m J ^ 2) * c ≤ m (insert i J)) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {J₀ : Finset ι} (hJ₀ : 0 ≤ m J₀) :
    ∃ J : Finset ι, (#J : ℝ) ≤ #J₀ + (log (1 / ε) / c + 1) ∧ 1 - ε ≤ m J := by
  have hB (k : ℕ) : ∃ J : Finset ι, #J ≤ #J₀ + k ∧ 0 ≤ m J ∧ 1 - m J ≤ (1 - c) ^ k := by
    induction k with
    | zero => exact ⟨J₀, by simp, hJ₀, by simpa using hJ₀⟩
    | succ k ih =>
      obtain ⟨J, hJ, hJ0, hJm⟩ := ih
      obtain ⟨i, hi⟩ := hstep J
      have h1 := hm J
      refine ⟨insert i J, (card_insert_le i J).trans (by omega), ?_, ?_⟩
      · nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - m J) (by linarith : 0 ≤ 1 + m J)]
      · have hshrink : 1 - m (insert i J) ≤ (1 - m J) * (1 - c) := by
          nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - m J) hJ0]
        calc 1 - m (insert i J) ≤ (1 - m J) * (1 - c) := hshrink
          _ ≤ (1 - c) ^ k * (1 - c) := by gcongr
          _ = _ := by ring
  set k := ⌈log (1 / ε) / c⌉₊
  obtain ⟨J, hJ, -, hJm⟩ := hB k
  have hpow : (1 - c) ^ k ≤ ε := by
    calc (1 - c) ^ k ≤ exp (-c) ^ k :=
          pow_le_pow_left₀ (by linarith) (by linarith [add_one_le_exp (-c)]) k
      _ = exp (-(c * k)) := by rw [← exp_natCast_mul]; ring_nf
      _ ≤ exp (-log (1 / ε)) := by
          refine exp_le_exp.2 (neg_le_neg ?_)
          rw [mul_comm, ← div_le_iff₀ hc]
          exact Nat.le_ceil _
      _ = ε := by rw [one_div, log_inv, neg_neg, exp_log hε]
  have hlogε : 0 ≤ log (1 / ε) := log_nonneg (by rw [le_div_iff₀ hε]; linarith)
  refine ⟨J, ?_, by linarith⟩
  calc (#J : ℝ) ≤ #J₀ + k := by exact_mod_cast hJ
    _ ≤ _ := by gcongr; exact (Nat.ceil_lt_add_one (by positivity)).le

/-- **Bribing a monotone election to near-unanimity** [O'Donnell, Exercise 9.27(a)][ODonnell2014]:
let `f` be monotone on `n ≥ 2` voters with variance at least `δ > 0`, read as signs, and let
`0 < ε ≤ 1`. Then some set `J` of at most `8 n log (2 / (ε δ)) / log n + 2` voters, when bribed to
vote `false`, makes the mean at least `1 - ε`. Write `c = log n / (4 n)` and `m` for the mean.
While `m < 0`, each bribe multiplies `1 + m` by at least `1 + c`, starting from
`1 + m ≥ δ / 2`; once `m ≥ 0`, each bribe multiplies `1 - m` by at most `1 - c`. -/
theorem exists_card_le_and_one_sub_le_expect_signVal_piecewise_false {f : (ι → Bool) → Bool}
    (hf : Monotone f) (hn : 2 ≤ Fintype.card ι) {δ ε : ℝ} (hδ : 0 < δ)
    (hV : δ ≤ 𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ J : Finset ι,
      (#J : ℝ) ≤ 8 * Fintype.card ι * log (2 / (ε * δ)) / log (Fintype.card ι) + 2 ∧
        1 - ε ≤ 𝔼 x, signVal (f (J.piecewise (fun _ => false) x)) := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  set n : ℝ := (Fintype.card ι : ℝ)
  have hlog : 0 < log n := log_pos (Nat.one_lt_cast.2 hn)
  set c := log n / (4 * n)
  have hc : 0 < c := by positivity
  have hc1 : c ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [log_le_sub_one_of_pos (show 0 < n by positivity)]
  set m : Finset ι → ℝ := fun J => 𝔼 x, signVal (f (J.piecewise (fun _ => false) x))
  have hm (J : Finset ι) : -1 ≤ m J ∧ m J ≤ 1 :=
    abs_le.1 (by simpa using abs_fourierCoeff_signVal_le_one _ ∅)
  have hstep (J : Finset ι) : ∃ i, m J + (1 - m J ^ 2) * c ≤ m (insert i J) := by
    obtain ⟨i, hi⟩ := exists_add_le_expect_signVal_piecewise_insert hf J
    exact ⟨i, by simpa [m, c, mul_div_assoc] using hi⟩
  have hm0 : m ∅ = 𝔼 x, signVal (f x) := by simp [m]
  rw [expect_sub_expect_sq_signVal, ← hm0] at hV
  have hδ1 : δ ≤ 1 := by nlinarith [sq_nonneg (m ∅)]
  have hstart : δ / 2 ≤ 1 + m ∅ := by nlinarith [(hm ∅).1, (hm ∅).2]
  obtain ⟨JA, hJA, hJA0⟩ := exists_card_le_and_nonneg_of_step hc hc1 (fun J => (hm J).1) hstep
    hδ hδ1 hstart
  obtain ⟨J, hJ, hJm⟩ := exists_card_le_and_one_sub_le_of_step hc hc1 (fun J => (hm J).2) hstep
    hε hε1 hJA0
  refine ⟨J, ?_, hJm⟩
  have hlogε : 0 ≤ log (1 / ε) := log_nonneg (by rw [le_div_iff₀ hε]; linarith)
  have hsplit : log (2 / (ε * δ)) = log (2 / δ) + log (1 / ε) := by
    rw [← log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  calc (#J : ℝ) ≤ 2 * log (2 / δ) / c + 1 + (log (1 / ε) / c + 1) := by linarith
    _ ≤ 2 * log (2 / (ε * δ)) / c + 2 := by
        rw [hsplit, mul_add, add_div, mul_div_assoc 2 (log (1 / ε))]
        linarith [div_nonneg hlogε hc.le]
    _ = _ := by
        simp only [c]
        field_simp
        ring

/-- **Bribing a monotone election to near-unanimity the other way**
[O'Donnell, Exercise 9.27(a)][ODonnell2014]: under the hypotheses of
`exists_card_le_and_one_sub_le_expect_signVal_piecewise_false`, a set of at most
`8 n log (2 / (ε δ)) / log n + 2` voters bribed to vote `true` makes the mean at most `ε - 1`.
This is that theorem for the dual `x ↦ ¬f(¬x)`, which has the same variance. -/
theorem exists_card_le_and_expect_signVal_piecewise_true_le_sub_one {f : (ι → Bool) → Bool}
    (hf : Monotone f) (hn : 2 ≤ Fintype.card ι) {δ ε : ℝ} (hδ : 0 < δ)
    (hV : δ ≤ 𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ J : Finset ι,
      (#J : ℝ) ≤ 8 * Fintype.card ι * log (2 / (ε * δ)) / log (Fintype.card ι) + 2 ∧
        𝔼 x, signVal (f (J.piecewise (fun _ => true) x)) ≤ ε - 1 := by
  have hmean : 𝔼 x : ι → Bool, signVal (!f fun j => !x j) = -𝔼 x, signVal (f x) := by
    simp only [signVal_not, expect_neg_distrib, Fintype.expect_comp_not (fun x => signVal (f x))]
  have hV' : δ ≤ 𝔼 x : ι → Bool,
      (signVal (!f fun j => !x j) - 𝔼 y : ι → Bool, signVal (!f fun j => !y j)) ^ 2 := by
    rw [expect_sub_expect_sq_signVal, hmean, neg_sq, ← expect_sub_expect_sq_signVal]
    exact hV
  obtain ⟨J, hJ, hJm⟩ :=
    exists_card_le_and_one_sub_le_expect_signVal_piecewise_false (monotone_dual hf) hn hδ hV' hε hε1
  refine ⟨J, hJ, ?_⟩
  simp only [dual_piecewise_false, signVal_not, expect_neg_distrib,
    Fintype.expect_comp_not (fun x => signVal (f (J.piecewise (fun _ => true) x)))] at hJm
  linarith

/-- **A small coalition controls a monotone election** [O'Donnell, Exercise 9.27(b)]
[ODonnell2014]: if `f` is monotone on `n ≥ 2` voters with variance at least `δ > 0`, read as signs,
and `0 < ε ≤ 1`, then some coalition `J` of at most `16 n log (2 / (ε δ)) / log n + 4` voters has
coalitional influence at least `1 - ε`. It is the union of a coalition that can force `false` and
one that can force `true`, each with probability at least `1 - ε / 2`
(Exercises 9.25(c)–(d) and 9.27(a)). -/
theorem exists_card_le_and_one_sub_le_coalitionInfluence {f : (ι → Bool) → Bool}
    (hf : Monotone f) (hn : 2 ≤ Fintype.card ι) {δ ε : ℝ} (hδ : 0 < δ)
    (hV : δ ≤ 𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ J : Finset ι,
      (#J : ℝ) ≤ 16 * Fintype.card ι * log (2 / (ε * δ)) / log (Fintype.card ι) + 4 ∧
        1 - ε ≤ coalitionInfluence (Probability.PMF.uniformOfFintype (ι → Bool)) J f := by
  obtain ⟨J₁, hJ₁, hm₁⟩ :=
    exists_card_le_and_one_sub_le_expect_signVal_piecewise_false hf hn hδ hV hε hε1
  obtain ⟨J₂, hJ₂, hm₂⟩ :=
    exists_card_le_and_expect_signVal_piecewise_true_le_sub_one hf hn hδ hV hε hε1
  refine ⟨J₁ ∪ J₂, ?_, ?_⟩
  · have h2 : 16 * (Fintype.card ι : ℝ) * log (2 / (ε * δ)) / log (Fintype.card ι) =
        2 * (8 * Fintype.card ι * log (2 / (ε * δ)) / log (Fintype.card ι)) := by ring
    calc (#(J₁ ∪ J₂) : ℝ) ≤ #J₁ + #J₂ := by exact_mod_cast card_union_le J₁ J₂
      _ ≤ _ := by linarith
  have hfalse (b : Bool) : (if b = false then (1 : ℝ) else 0) = (1 + signVal b) / 2 := by
    cases b <;> norm_num
  have htrue (b : Bool) : (if b = true then (1 : ℝ) else 0) = (1 - signVal b) / 2 := by
    cases b <;> norm_num
  have h1 : 1 - ε ≤ coalitionInfluenceToward true J₂ f + coalitionInfluenceToward false J₁ f := by
    rw [coalitionInfluenceToward_eq_of_monotone hf, coalitionInfluenceToward_eq_of_monotone hf]
    simp only [hfalse, htrue, ← expect_div, expect_add_distrib, expect_sub_distrib,
      Fintype.expect_const]
    linarith
  calc 1 - ε ≤ coalitionInfluenceToward true J₂ f + coalitionInfluenceToward false J₁ f := h1
    _ ≤ _ := by
        rw [coalitionInfluence_eq_add]
        exact add_le_add (coalitionInfluenceToward_mono true subset_union_right f)
          (coalitionInfluenceToward_mono false subset_union_left f)

end Cslib.BitString
