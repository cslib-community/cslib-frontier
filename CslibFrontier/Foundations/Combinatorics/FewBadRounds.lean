/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A schedule with few bad rounds for every history

Let each element `i` of a finset `I` (an edge) be assigned a round `ρ i` among `T` rounds, and let
every `h` of a finite family `𝓗` (the histories) declare a set `bad h i` of at most `B` bad rounds
for each `i`. Some schedule `ρ` simultaneously keeps, for every `h ∈ 𝓗`, the number of `i ∈ I` with
`ρ i ∈ bad h i` at most `(log #𝓗 + #I * B / T) / log 2`.

This is a step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026], tracked in #8325: the
counting form of the paper's Lemma 3.11 (§3.4, p. 21), abstracted from the certificate procedure.
The source's proof draws `ρ` uniformly and bounds `𝔼 2 ^ X_h(ρ)`. Here the expectation is a finite
double count over all `T ^ #I` schedules: `∑_ρ 2 ^ X_h(ρ) = ∏_i (T + #(bad h i)) ≤ (T + B) ^ #I`, so
some schedule has `T ^ #I * ∑_h 2 ^ X_h(ρ) ≤ #𝓗 * (T + B) ^ #I`. Taking logarithms and
`log (1 + B / T) ≤ B / T` gives the bound. The source's case is `T = t²` and `B = 2t`, where
`#I * B / T = 2 #I / t`.

## Main results

* `Cslib.exists_schedule_few_bad_rounds`: a schedule with few bad rounds for every history, a step
  in the proof of Theorem 4.1 of [KhannaPuttermanSong2026] (the paper's Lemma 3.11, abstracted).

## References

* [S. Khanna, A. Putterman, J. Song, *A Deterministic Linear Time Algorithm for Minimum Spanning
  Tree*][KhannaPuttermanSong2026]
-/

public section

namespace Cslib

open Finset

variable {ι R H : Type*} [Fintype R] [DecidableEq R]

/-- The double count over all schedules of a finite index type, in natural numbers. -/
private theorem exists_schedule_pow_mul_le {κ : Type*} [Fintype κ] [Nonempty R]
    (𝓗 : Finset H) (bad : H → κ → Finset R) {B : ℕ} (hB : ∀ h ∈ 𝓗, ∀ i, #(bad h i) ≤ B) :
    ∃ ρ : κ → R, Fintype.card R ^ Fintype.card κ * ∑ h ∈ 𝓗, 2 ^ #{i | ρ i ∈ bad h i} ≤
      #𝓗 * (Fintype.card R + B) ^ Fintype.card κ := by
  classical
  set T := Fintype.card R
  -- `2 ^ X_h(ρ)` is a product over the coordinates of `ρ`, so its sum over `ρ` factors
  have hsum (h : H) : ∑ ρ : κ → R, 2 ^ #{i | ρ i ∈ bad h i} = ∏ i, (T + #(bad h i)) := by
    calc ∑ ρ : κ → R, 2 ^ #{i | ρ i ∈ bad h i}
        = ∑ ρ : κ → R, ∏ i, (if ρ i ∈ bad h i then 2 else 1) :=
          sum_congr rfl fun ρ _ => by rw [prod_ite, prod_const, prod_const_one, mul_one]
      _ = ∏ i, ∑ r, (if r ∈ bad h i then 2 else 1) :=
          (Fintype.prod_sum fun i r => if r ∈ bad h i then 2 else 1).symm
      _ = ∏ i, (T + #(bad h i)) := prod_congr rfl fun i _ => by
          rw [show (fun r => if r ∈ bad h i then 2 else 1) =
              fun r => 1 + if r ∈ bad h i then 1 else 0 from funext fun r => by split_ifs <;> rfl,
            sum_add_distrib, sum_boole, sum_const, card_univ, smul_eq_mul, mul_one,
            filter_mem_eq_inter, univ_inter, Nat.cast_id]
  have htotal : ∑ ρ : κ → R, ∑ h ∈ 𝓗, 2 ^ #{i | ρ i ∈ bad h i} ≤
      #𝓗 * (T + B) ^ Fintype.card κ := by
    rw [sum_comm, ← smul_eq_mul, ← sum_const]
    refine sum_le_sum fun h hh => ?_
    rw [hsum, ← card_univ, ← prod_const]
    exact prod_le_prod fun i _ => Nat.add_le_add_left (hB h hh i) T
  -- averaging over the `T ^ card κ` schedules
  have hle : ∑ ρ : κ → R, T ^ Fintype.card κ * ∑ h ∈ 𝓗, 2 ^ #{i | ρ i ∈ bad h i} ≤
      ∑ _ρ : κ → R, #𝓗 * (T + B) ^ Fintype.card κ := by
    rw [← mul_sum, sum_const, card_univ, Fintype.card_fun, smul_eq_mul]
    exact Nat.mul_le_mul_left _ htotal
  exact (exists_le_of_sum_le univ_nonempty hle).imp fun _ h => h.2

/-- **A schedule with few bad rounds**, a step in the proof of Theorem 4.1 of
[KhannaPuttermanSong2026] (the paper's Lemma 3.11, §3.4, p. 21, abstracted from the certificate
procedure). Let `bad h i` be a set of at most `B` of the `T = Fintype.card R ≥ 1` rounds, for every
history `h ∈ 𝓗` and element `i ∈ I`. Then one schedule `ρ : ι → R` puts, for every `h ∈ 𝓗` at once,
at most `(log #𝓗 + #I * B / T) / log 2` elements of `I` into one of their bad rounds.

The source's bound `(log |𝓗| + 2m / t) / log 2` is the case `T = t²`, `B = 2t`, `#I = m`; the
source passes through `m log (1 + B / T) ≤ m B / T`. Values of `ρ` outside `I` are irrelevant. -/
theorem exists_schedule_few_bad_rounds [Nonempty R] (I : Finset ι) (𝓗 : Finset H)
    (bad : H → ι → Finset R) {B : ℕ} (hB : ∀ h ∈ 𝓗, ∀ i ∈ I, #(bad h i) ≤ B) :
    ∃ ρ : ι → R, ∀ h ∈ 𝓗, (#{i ∈ I | ρ i ∈ bad h i} : ℝ) * Real.log 2 ≤
      Real.log #𝓗 + #I * B / Fintype.card R := by
  classical
  obtain ⟨ρ', hρ'⟩ := exists_schedule_pow_mul_le 𝓗 (fun h (i : I) => bad h i)
    (fun h hh i => hB h hh i i.property)
  rw [Fintype.card_coe] at hρ'
  set T := Fintype.card R
  let ρ : ι → R := fun i => if hi : i ∈ I then ρ' ⟨i, hi⟩ else Classical.arbitrary R
  refine ⟨ρ, fun h hh => ?_⟩
  have hX : #{i ∈ I | ρ i ∈ bad h i} = #{i : I | ρ' i ∈ bad h i} := by
    rw [card_filter, card_filter, ← sum_coe_sort I]
    refine sum_congr rfl fun i _ => ?_
    simp [ρ]
  -- one history's term of the sum
  have hone : T ^ #I * 2 ^ #{i ∈ I | ρ i ∈ bad h i} ≤ #𝓗 * (T + B) ^ #I := by
    rw [hX]
    exact le_trans (Nat.mul_le_mul_left _ (single_le_sum
      (f := fun h => 2 ^ #{i : I | ρ' i ∈ bad h i}) (fun _ _ => Nat.zero_le _) hh)) hρ'
  have hT : (0 : ℝ) < T := by exact_mod_cast Fintype.card_pos
  have hH : (0 : ℝ) < #𝓗 := by exact_mod_cast card_pos.2 ⟨h, hh⟩
  have hone' : (T : ℝ) ^ #I * 2 ^ #{i ∈ I | ρ i ∈ bad h i} ≤ #𝓗 * (T + B) ^ #I := by
    exact_mod_cast hone
  have hlog := Real.log_le_log (by positivity) hone'
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hH.ne' (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  -- `log (T + B) - log T = log (1 + B / T) ≤ B / T`
  have hratio : Real.log (T + B) - Real.log T ≤ B / T := by
    rw [← Real.log_div (by positivity) hT.ne', add_div, div_self hT.ne']
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + B / T by positivity)
    linarith
  have hI : (0 : ℝ) ≤ #I := Nat.cast_nonneg _
  rw [mul_div_assoc]
  nlinarith [mul_le_mul_of_nonneg_left hratio hI]

end Cslib
