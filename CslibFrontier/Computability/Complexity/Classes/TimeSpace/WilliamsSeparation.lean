/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Space
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.Williams
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Computability.Complexity.Classes.Constructible.Space
import CslibFrontier.Foundations.Data.Nat.AffineBound
import CslibFrontier.Foundations.Data.Nat.Asymptotics
import CslibFrontier.Foundations.Data.Nat.LogRpow
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Time–space separation corollaries from Williams's simulation

Combining Williams's square-root-space simulation of deterministic time
(`Cslib.Complexity.DTIME_subset_DSPACE_sqrt`, Theorem 1.1 of [Williams2025]) with the
deterministic space hierarchy theorem (`Cslib.Complexity.DSPACE_ssubset_DSPACE`, [Stearns,
Hartmanis and Lewis][StearnsHartmanisLewis1965]) separates deterministic space from smaller
deterministic time classes on bit words.

Specifically, whenever `s` is space-constructible (`Cslib.Complexity.SpaceConstructible`) with
`⌊log₂ n⌋ ≤ s n` eventually, any time bound `t` satisfying
`√(max n (t n) · (⌊log₂ (max n (t n))⌋ + 1)) = o(s n)` satisfies
`DTIME encBits t ⊂ DSPACE encBits s` and `¬ DSPACE encBits s ⊆ DTIME encBits t`
(`Cslib.Complexity.DTIME_ssubset_DSPACE_of_sqrt`, with squared and little-o sufficient conditions).
In particular, when `s n ≥ n` eventually:

* for every real `ε > 0`, `DTIME encBits (fun n => ⌊(s n : ℝ) ^ (2 - ε)⌋₊) ⊂ DSPACE encBits s`
  (`Cslib.Complexity.DTIME_rpow_sub_ssubset_DSPACE`), and in particular for linear space `s n = n`,
  `¬ DSPACE encBits (fun n => n) ⊆ DTIME encBits (fun n => ⌊(n : ℝ) ^ (2 - ε)⌋₊)`
  (`Cslib.Complexity.DSPACE_id_not_subset_DTIME_rpow_sub`);
* for `a, b : ℕ` with `1 ≤ b` and `a < 2 * b`,
  `DTIME encBits (· ^ a) ⊂ DSPACE encBits (· ^ b)`
  (`Cslib.Complexity.DTIME_pow_ssubset_DSPACE_pow`);
* with the sharper polylogarithmic gap `n ^ 2 / (⌊log₂ n⌋ + 1) ^ 2`,
  `DTIME encBits (fun n => s n ^ 2 / (Nat.log2 (s n) + 1) ^ 2) ⊂ DSPACE encBits s`
  (`Cslib.Complexity.DTIME_sq_div_log2_sq_ssubset_DSPACE`), and likewise for linear space.

The separating problem can be taken to be the explicit budgeted diagonal language
`{x | spaceDiagonal (fun n => 4 * s n) x = true}` when `⌊log₂ n⌋ ≤ s n` holds pointwise
(`Cslib.Complexity.setOf_spaceDiagonal_id_mem_DSPACE`,
`Cslib.Complexity.setOf_spaceDiagonal_id_notMem_DTIME_rpow_sub`).

Note on sources: `[Williams2025]` Theorem 1.1 is established by
`Cslib.Complexity.DTIME_subset_DSPACE_sqrt`
(`CslibFrontier/Computability/Complexity/Classes/TimeSpace/Williams.lean`). The separation
corollaries below are proved directly from it and `Cslib.Complexity.DSPACE_ssubset_DSPACE`;
only Theorem 1.1's verified statement in the repository (not a separate PDF inspection of later
numbered corollaries) is relied upon.

## Main results

* `Cslib.Complexity.DTIME_subset_DSPACE_sqrt_max`,
  `Cslib.Complexity.DTIME_subset_DSPACE_sqrt_of_eventually_le`: square-root-space simulation
  without a pointwise `n ≤ t n` hypothesis.
* `Cslib.Complexity.DTIME_ssubset_DSPACE_of_sqrt`,
  `Cslib.Complexity.DTIME_ssubset_DSPACE_of_mul_log2_le_sq`,
  `Cslib.Complexity.DTIME_ssubset_DSPACE_of_isLittleO`: general time–space separations and their
  negated-containment forms.
* `Cslib.Complexity.DTIME_rpow_sub_ssubset_DSPACE`,
  `Cslib.Complexity.DTIME_rpow_lt_two_ssubset_DSPACE`,
  `Cslib.Complexity.DSPACE_not_subset_DTIME_rpow_sub`: `DTIME (⌊s(n) ^ (2 - ε)⌋) ⊂ DSPACE (s)`
  and `DSPACE (s) ⊄ DTIME (⌊s(n) ^ (2 - ε)⌋)` for every `ε > 0`.
* `Cslib.Complexity.DTIME_pow_ssubset_DSPACE_pow`,
  `Cslib.Complexity.DTIME_sq_div_log2_sq_ssubset_DSPACE`,
  `Cslib.Complexity.DTIME_id_ssubset_DSPACE_id`: polynomial-exponent,
  `s(n) ^ 2 / (⌊log₂ (s n)⌋ + 1) ^ 2`, and linear-space (`s n = n`) separations.
* `Cslib.Complexity.setOf_spaceDiagonal_notMem_DTIME`,
  `Cslib.Complexity.setOf_spaceDiagonal_id_mem_DSPACE`,
  `Cslib.Complexity.setOf_spaceDiagonal_id_notMem_DTIME_rpow_sub`,
  `Cslib.Complexity.setOf_spaceDiagonal_id_notMem_DTIME_sq_div_log2_sq`: explicit diagonal
  separating witnesses.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Theorem 4.8][AroraBarak09]
* [R. E. Stearns, J. Hartmanis, P. M. Lewis II, *Hierarchies of memory limited
  computations*][StearnsHartmanisLewis1965]
* [R. Williams, *Simulating Time With Square-Root Space*, Theorem 1.1][Williams2025]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Filter Asymptotics

/-! ### Extensions of the square-root-space inclusion -/

/-- **Williams's square-root-space simulation for arbitrary time bounds**: replacing `t n` by
`max n (t n)` removes the pointwise `n ≤ t n` condition from `DTIME_subset_DSPACE_sqrt`. -/
theorem DTIME_subset_DSPACE_sqrt_max {α : Type*} (enc : α ↪ List Bool) (t : ℕ → ℕ) :
    DTIME enc t ⊆ DSPACE enc (fun n => Nat.sqrt (max n (t n) * (Nat.log2 (max n (t n)) + 1))) :=
  (DTIME_mono fun n => le_max_right n (t n)).trans
    (DTIME_subset_DSPACE_sqrt enc (fun n => max n (t n)) fun n => le_max_left n (t n))

/-- **Williams's square-root-space simulation for eventually linear-or-larger time bounds**:
if `n ≤ t n` for all sufficiently large `n`, `DTIME enc t` lies in
`DSPACE enc (fun n => Nat.sqrt (t n * (Nat.log2 (t n) + 1)))`. -/
theorem DTIME_subset_DSPACE_sqrt_of_eventually_le {α : Type*} (enc : α ↪ List Bool) {t : ℕ → ℕ}
    (ht : ∀ᶠ n in atTop, n ≤ t n) :
    DTIME enc t ⊆ DSPACE enc (fun n => Nat.sqrt (t n * (Nat.log2 (t n) + 1))) :=
  (DTIME_subset_DSPACE_sqrt_max enc t).trans
    (DSPACE_mono_of_eventually_le (ht.mono fun _ hn => by simp only [max_eq_right hn, le_rfl]))

/-! ### Arithmetic and shift helpers -/

/-- Eventual domination in `g ^ 2` implies eventual domination of `Nat.sqrt f` in `g`. -/
private theorem eventually_mul_sqrt_add_le_of_mul_add_le_sq {f g : ℕ → ℕ}
    (h : ∀ c, ∀ᶠ n in atTop, c * f n + c ≤ g n ^ 2) :
    ∀ c, ∀ᶠ n in atTop, c * Nat.sqrt (f n) + c ≤ g n := by
  intro c
  filter_upwards [h (2 * c ^ 2)] with n hn
  refine (Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).mp ?_
  have hsqrt : Nat.sqrt (f n) ^ 2 ≤ f n := by simpa only [sq] using Nat.sqrt_le (f n)
  have hsq : (c * Nat.sqrt (f n) + c) ^ 2 ≤ 2 * c ^ 2 * Nat.sqrt (f n) ^ 2 + 2 * c ^ 2 := by
    rcases le_total (c * Nat.sqrt (f n)) c with hle | hle <;> nlinarith
  nlinarith [Nat.mul_le_mul_left (2 * c ^ 2) hsqrt]

/-- If `Nat.log2 n ≤ s n` holds eventually, adding `Nat.log2 N` preserves `SpaceConstructible`,
preserves `DSPACE`, and ensures the logarithmic lower bound holds pointwise. -/
private theorem exists_shift_of_eventually_log2_le {s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hlog : ∀ᶠ n in atTop, Nat.log2 n ≤ s n) :
    ∃ c₀ : ℕ, SpaceConstructible (fun n => s n + c₀) ∧
      (∀ n, Nat.log2 n ≤ s n + c₀) ∧
      DSPACE encBits (fun n => s n + c₀) = DSPACE encBits s := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlog
  refine ⟨Nat.log2 N, hs.add (spaceConstructible_const (Nat.log2 N)), fun n => ?_, ?_⟩
  · rcases le_or_gt N n with hn | hn
    · exact (hN n hn).trans (Nat.le_add_right _ _)
    · rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
      exact (Nat.log_mono_right hn.le).trans (Nat.le_add_left _ _)
  · exact Set.Subset.antisymm
      (DSPACE_mono_of_le_mul_add (C := 1 + Nat.log2 N) fun n => by
        nlinarith [Nat.zero_le (s n * Nat.log2 N)])
      (DSPACE_mono fun n => Nat.le_add_right _ _)

private theorem eventually_log2_le_of_eventually_le {s : ℕ → ℕ} (hn : ∀ᶠ n in atTop, n ≤ s n) :
    ∀ᶠ n in atTop, Nat.log2 n ≤ s n :=
  hn.mono fun _ h => (Nat.log2_le_self _).trans h

private theorem log2_le_two_mul_log2_add_one {m k : ℕ} (hk : 1 ≤ k) (hm : m ≤ k ^ 2) :
    Nat.log2 m ≤ 2 * Nat.log2 k + 1 := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  have hpow := Nat.log_mono_right (b := 2) hm
  have hlt : k ^ 2 < 2 ^ (2 * Nat.log 2 k + 2) := by
    have hk_lt : k < 2 ^ (Nat.log 2 k + 1) := Nat.lt_pow_succ_log_self one_lt_two k
    calc k ^ 2 < (2 ^ (Nat.log 2 k + 1)) ^ 2 := Nat.pow_lt_pow_left hk_lt (by norm_num)
      _ = 2 ^ (2 * Nat.log 2 k + 2) := by rw [← pow_mul]; ring_nf
  exact hpow.trans (Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow (pow_ne_zero 2 (by omega)) hlt))

private theorem tendsto_of_eventually_log2_le {s : ℕ → ℕ} (hlog : ∀ᶠ n in atTop, Nat.log2 n ≤ s n) :
    Tendsto s atTop atTop :=
  tendsto_atTop_atTop.mpr fun k => by
    obtain ⟨M, hM⟩ := eventually_atTop.mp ((Nat.eventually_le_log k one_lt_two).and hlog)
    exact ⟨M, fun n hn => (Nat.log2_eq_log_two.symm ▸ (hM n hn).1).trans (hM n hn).2⟩

/-! ### General time–space separation theorems -/

/-- **General Williams + space-hierarchy separation.** When `s` is space-constructible with
`⌊log₂ n⌋ ≤ s n` eventually and `√(max n (t n) · (⌊log₂ (max n (t n))⌋ + 1)) = o(s n)`,
`DTIME encBits t` is strictly contained in `DSPACE encBits s`. -/
theorem DTIME_ssubset_DSPACE_of_sqrt {t s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hlog : ∀ᶠ n in atTop, Nat.log2 n ≤ s n)
    (hdom : ∀ c, ∀ᶠ n in atTop,
      c * Nat.sqrt (max n (t n) * (Nat.log2 (max n (t n)) + 1)) + c ≤ s n) :
    DTIME encBits t ⊂ DSPACE encBits s := by
  obtain ⟨c₀, hs', hlog', hEq⟩ := exists_shift_of_eventually_log2_le hs hlog
  exact (DTIME_subset_DSPACE_sqrt_max encBits t).trans_ssubset (lt_of_lt_of_eq
    (DSPACE_ssubset_DSPACE hs' hlog' fun c =>
      (hdom c).mono fun _ h => h.trans (Nat.le_add_right _ _)) hEq)

/-- **Containment failure form of the general separation**: `DSPACE encBits s` is not contained in
`DTIME encBits t`. -/
theorem DSPACE_not_subset_DTIME_of_sqrt {t s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hlog : ∀ᶠ n in atTop, Nat.log2 n ≤ s n)
    (hdom : ∀ c, ∀ᶠ n in atTop,
      c * Nat.sqrt (max n (t n) * (Nat.log2 (max n (t n)) + 1)) + c ≤ s n) :
    ¬ DSPACE encBits s ⊆ DTIME encBits t :=
  fun h => (DTIME_ssubset_DSPACE_of_sqrt hs hlog hdom).not_superset h

/-- **Explicit separating diagonal witness**: when `⌊log₂ n⌋ ≤ s n` holds pointwise and
`√(max n (t n) · (⌊log₂ (max n (t n))⌋ + 1)) = o(s n)`, the diagonal problem
`{x | spaceDiagonal (fun n => 4 * s n) x = true}` is outside `DTIME encBits t`. -/
theorem setOf_spaceDiagonal_notMem_DTIME {t s : ℕ → ℕ} (hlog : ∀ n, Nat.log2 n ≤ s n)
    (hdom : ∀ c, ∀ᶠ n in atTop,
      c * Nat.sqrt (max n (t n) * (Nat.log2 (max n (t n)) + 1)) + c ≤ s n) :
    {x | spaceDiagonal (fun n => 4 * s n) x = true} ∉ DTIME encBits t := by
  intro hmem
  exact setOf_spaceDiagonal_notMem_DSPACE
    (G := fun n => 4 * s n) (fun n => Nat.mul_le_mul_left 4 (hlog n))
    (fun c => (hdom c).mono fun _ h => by omega)
    (DTIME_subset_DSPACE_sqrt_max encBits t hmem)

/-- **Explicit separating witness membership**: for space-constructible `s` with
`⌊log₂ n⌋ ≤ s n` pointwise, `{x | spaceDiagonal (fun n => 4 * s n) x = true}` lies in
`DSPACE encBits s`. -/
theorem setOf_spaceDiagonal_four_mul_mem_DSPACE {s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hlog : ∀ n, Nat.log2 n ≤ s n) :
    {x | spaceDiagonal (fun n => 4 * s n) x = true} ∈ DSPACE encBits s :=
  DSPACE_mono_of_le_mul_add (C := 4) (fun _ => Nat.le_add_right _ _)
    (setOf_spaceDiagonal_mem_DSPACE (hs.const_mul 4) fun n =>
      (hlog n).trans (Nat.le_mul_of_pos_left _ (by norm_num)))

/-- **Squared-domination form of Williams's separation**: if every affine multiple of
`max n (t n) · (⌊log₂ (max n (t n))⌋ + 1)` is eventually at most `s n ^ 2`, then
`DTIME encBits t ⊂ DSPACE encBits s`. -/
theorem DTIME_ssubset_DSPACE_of_mul_log2_le_sq {t s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hlog : ∀ᶠ n in atTop, Nat.log2 n ≤ s n)
    (hsq : ∀ c, ∀ᶠ n in atTop, c * (max n (t n) * (Nat.log2 (max n (t n)) + 1)) + c ≤ s n ^ 2) :
    DTIME encBits t ⊂ DSPACE encBits s :=
  DTIME_ssubset_DSPACE_of_sqrt hs hlog (eventually_mul_sqrt_add_le_of_mul_add_le_sq hsq)

/-- **Squared-domination containment failure**: `¬ DSPACE encBits s ⊆ DTIME encBits t`. -/
theorem DSPACE_not_subset_DTIME_of_mul_log2_le_sq {t s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hlog : ∀ᶠ n in atTop, Nat.log2 n ≤ s n)
    (hsq : ∀ c, ∀ᶠ n in atTop, c * (max n (t n) * (Nat.log2 (max n (t n)) + 1)) + c ≤ s n ^ 2) :
    ¬ DSPACE encBits s ⊆ DTIME encBits t :=
  fun h => (DTIME_ssubset_DSPACE_of_mul_log2_le_sq hs hlog hsq).not_superset h

/-- **Little-o form of Williams's separation**: if
`max n (t n) · (⌊log₂ (max n (t n))⌋ + 1) = o(s n ^ 2)`, then
`DTIME encBits t ⊂ DSPACE encBits s`. -/
theorem DTIME_ssubset_DSPACE_of_isLittleO {t s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hlog : ∀ᶠ n in atTop, Nat.log2 n ≤ s n)
    (ho : (fun n => ((max n (t n) * (Nat.log2 (max n (t n)) + 1) : ℕ) : ℝ)) =o[atTop]
      (fun n => ((s n ^ 2 : ℕ) : ℝ))) :
    DTIME encBits t ⊂ DSPACE encBits s := by
  refine DTIME_ssubset_DSPACE_of_mul_log2_le_sq hs hlog fun c => ?_
  filter_upwards [Asymptotics.isLittleO_iff_nat_mul_le.mp ho (2 * c),
    (tendsto_of_eventually_log2_le hlog).eventually_ge_atTop (2 * c + 1)] with n hn hsc
  simp only [Real.norm_natCast] at hn
  set m := max n (t n) * (Nat.log2 (max n (t n)) + 1)
  have h1 : 2 * c * m ≤ s n ^ 2 := mod_cast hn
  rcases Nat.eq_zero_or_pos m with hm | hm <;> nlinarith

/-- **Little-o containment failure**: `¬ DSPACE encBits s ⊆ DTIME encBits t`. -/
theorem DSPACE_not_subset_DTIME_of_isLittleO {t s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hlog : ∀ᶠ n in atTop, Nat.log2 n ≤ s n)
    (ho : (fun n => ((max n (t n) * (Nat.log2 (max n (t n)) + 1) : ℕ) : ℝ)) =o[atTop]
      (fun n => ((s n ^ 2 : ℕ) : ℝ))) :
    ¬ DSPACE encBits s ⊆ DTIME encBits t :=
  fun h => (DTIME_ssubset_DSPACE_of_isLittleO hs hlog ho).not_superset h

/-! ### Subquadratic-exponent and polylogarithmic separations -/

/-- Shared domination proof for `t n = ⌊(s n : ℝ) ^ (2 - ε)⌋₊` when `n ≤ s n` eventually and
`0 < ε`. -/
private theorem eventually_rpow_sub_mul_log2_le_sq {s : ℕ → ℕ} (hn : ∀ᶠ n in atTop, n ≤ s n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ c, ∀ᶠ n in atTop,
      c * (max n ⌊(s n : ℝ) ^ (2 - ε)⌋₊ * (Nat.log2 (max n ⌊(s n : ℝ) ^ (2 - ε)⌋₊) + 1)) + c ≤
        s n ^ 2 := by
  let α : ℝ := max 1 (2 - ε)
  have hα1 : 1 ≤ α := le_max_left 1 (2 - ε)
  have hα2 : α < 2 := max_lt (by norm_num) (by linarith)
  have hδ : 0 < 2 - α := sub_pos.mpr hα2
  have hten : Tendsto s atTop atTop :=
    tendsto_atTop_mono' atTop hn tendsto_id
  intro c
  let K : ℝ := (4 * c + 2 : ℕ)
  have hK : 0 < K := by positivity
  have hlog_rpowK := hten.eventually
    (Nat.eventually_mul_log_add_pow_le_rpow (b := 2) one_lt_two 0 2 1 hK hδ)
  filter_upwards [eventually_ge_atTop 1, hn, hten.eventually_ge_atTop 2, hlog_rpowK]
    with n hn1 hns hs2 hKbd
  have hKbd' : K * ((Nat.log 2 (s n) : ℝ) + 2) ≤ (s n : ℝ) ^ (2 - α) := by
    simpa only [add_zero, pow_one, Nat.cast_ofNat] using hKbd
  have hsR1 : (1 : ℝ) ≤ s n := by exact_mod_cast (by omega : 1 ≤ s n)
  have hsR0 : (0 : ℝ) < s n := by positivity
  set m := max n ⌊(s n : ℝ) ^ (2 - ε)⌋₊ with hm
  have hm_le_rpow : (m : ℝ) ≤ (s n : ℝ) ^ α := by
    rw [hm, Nat.cast_max]
    refine max_le ((Nat.cast_le.mpr hns).trans ?_)
      ((Nat.floor_le (Real.rpow_nonneg hsR0.le _)).trans ?_)
    · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hsR1 hα1
    · exact Real.rpow_le_rpow_of_exponent_le hsR1 (le_max_right 1 (2 - ε))
  have hm_le_sq : m ≤ s n ^ 2 := by
    exact_mod_cast (hm_le_rpow.trans (Real.rpow_le_rpow_of_exponent_le hsR1 hα2.le)).trans_eq
      (Real.rpow_two _)
  have hlogR : ((Nat.log2 m : ℝ) + 1) ≤ 2 * ((Nat.log 2 (s n) : ℝ) + 2) := by
    have hlog_sq := log2_le_two_mul_log2_add_one (by omega) hm_le_sq
    simp only [Nat.log2_eq_log_two] at hlog_sq ⊢
    exact_mod_cast (by omega : Nat.log 2 m + 1 ≤ 2 * (Nat.log 2 (s n) + 2))
  have hnat_bd : 2 * c * (m * (Nat.log2 m + 1)) ≤ s n ^ 2 := by
    have hK_le : (2 : ℝ) * (2 * (c : ℝ)) ≤ K := by dsimp only [K]; push_cast; linarith
    rw [← @Nat.cast_le ℝ]
    push_cast
    calc (2 : ℝ) * c * ((m : ℝ) * ((Nat.log2 m : ℝ) + 1))
        ≤ 2 * c * ((s n : ℝ) ^ α * (2 * ((Nat.log 2 (s n) : ℝ) + 2))) := by gcongr
      _ = (s n : ℝ) ^ α * ((2 * (2 * (c : ℝ))) * ((Nat.log 2 (s n) : ℝ) + 2)) := by ring
      _ ≤ (s n : ℝ) ^ α * (K * ((Nat.log 2 (s n) : ℝ) + 2)) := by gcongr
      _ ≤ (s n : ℝ) ^ α * (s n : ℝ) ^ (2 - α) := by gcongr
      _ = (s n : ℝ) ^ 2 := by rw [← Real.rpow_add hsR0, add_sub_cancel, Real.rpow_two]
  have hone : 1 ≤ m * (Nat.log2 m + 1) :=
    Nat.mul_pos (lt_of_lt_of_le hn1 (le_max_left _ _)) (Nat.succ_pos _)
  nlinarith

/-- **Subquadratic-time vs. constructible-space separation** ([Williams2025], Theorem 1.1
consequence): for any space-constructible `s` satisfying `n ≤ s n` eventually and any real
`ε > 0`, `DTIME encBits (fun n => ⌊(s n : ℝ) ^ (2 - ε)⌋₊)` is strictly contained in
`DSPACE encBits s`. -/
theorem DTIME_rpow_sub_ssubset_DSPACE {s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hn : ∀ᶠ n in atTop, n ≤ s n) {ε : ℝ} (hε : 0 < ε) :
    DTIME encBits (fun n => ⌊(s n : ℝ) ^ (2 - ε)⌋₊) ⊂ DSPACE encBits s :=
  DTIME_ssubset_DSPACE_of_mul_log2_le_sq hs (eventually_log2_le_of_eventually_le hn)
    (eventually_rpow_sub_mul_log2_le_sq hn hε)

/-- **Exponent-below-two form** of the constructible-space separation: for any real `α < 2`,
`DTIME encBits (fun n => ⌊(s n : ℝ) ^ α⌋₊) ⊂ DSPACE encBits s`. -/
theorem DTIME_rpow_lt_two_ssubset_DSPACE {s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hn : ∀ᶠ n in atTop, n ≤ s n) {α : ℝ} (hα : α < 2) :
    DTIME encBits (fun n => ⌊(s n : ℝ) ^ α⌋₊) ⊂ DSPACE encBits s := by
  simpa only [sub_sub_cancel] using DTIME_rpow_sub_ssubset_DSPACE hs hn (sub_pos.mpr hα)

/-- **Williams's separation in containment-failure form**: for any space-constructible `s` with
`n ≤ s n` eventually and any `ε > 0`, `DSPACE encBits s` is not contained in
`DTIME encBits (fun n => ⌊(s n : ℝ) ^ (2 - ε)⌋₊)`. -/
theorem DSPACE_not_subset_DTIME_rpow_sub {s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hn : ∀ᶠ n in atTop, n ≤ s n) {ε : ℝ} (hε : 0 < ε) :
    ¬ DSPACE encBits s ⊆ DTIME encBits (fun n => ⌊(s n : ℝ) ^ (2 - ε)⌋₊) :=
  fun h => (DTIME_rpow_sub_ssubset_DSPACE hs hn hε).not_superset h

/-- Shared domination proof for `t n = s n ^ 2 / (Nat.log2 (s n) + 1) ^ 2` when `n ≤ s n`
eventually. -/
private theorem eventually_sq_div_log2_sq_mul_log2_le_sq {s : ℕ → ℕ}
    (hn : ∀ᶠ n in atTop, n ≤ s n) :
    ∀ c, ∀ᶠ n in atTop,
      c * (max n (s n ^ 2 / (Nat.log2 (s n) + 1) ^ 2) *
          (Nat.log2 (max n (s n ^ 2 / (Nat.log2 (s n) + 1) ^ 2)) + 1)) + c ≤ s n ^ 2 := by
  have hten : Tendsto s atTop atTop := tendsto_atTop_mono' atTop hn tendsto_id
  have hlog2 : ∀ k : ℕ, ∀ᶠ n in atTop, k ≤ Nat.log2 (s n) := fun k =>
    (hten.eventually (Nat.eventually_le_log k one_lt_two)).mono fun _ => by
      simp only [Nat.log2_eq_log_two, imp_self]
  have hsq_vs_log : ∀ᶠ n in atTop, (Nat.log2 (s n) + 1) ^ 2 ≤ s n :=
    (hten.eventually (Nat.eventually_mul_log_add_pow_le_rpow (b := 2) one_lt_two 0 1 2
      one_pos one_pos)).mono fun n h' => by
      simp only [add_zero, one_mul, Real.rpow_one, ← Nat.log2_eq_log_two] at h'
      exact_mod_cast h'
  intro c
  filter_upwards [hn, hlog2 (8 * c + 8), hsq_vs_log, hten.eventually_ge_atTop (4 * c + 4)]
    with n hns hL hL2 hsmin
  set L := Nat.log2 (s n) + 1
  set t := s n ^ 2 / L ^ 2 with ht
  have hLpos : 0 < L := Nat.succ_pos _
  have hL_ge : 8 * c + 9 ≤ L := by omega
  have hns_le_t : s n ≤ t := (Nat.le_div_iff_mul_le (pow_pos hLpos 2)).mpr
    ((Nat.mul_le_mul_left _ hL2).trans_eq (sq (s n)).symm)
  have hmax : max n t = t := max_eq_right (hns.trans hns_le_t)
  have ht_le_sq : t ≤ s n ^ 2 := Nat.div_le_self _ _
  have hlogt : Nat.log2 t + 1 ≤ 2 * L := by
    have := log2_le_two_mul_log2_add_one (by omega) ht_le_sq
    dsimp only [L]; omega
  have ht_log : t * (Nat.log2 t + 1) ≤ 2 * (s n ^ 2 / L) := by
    have ht_mul_L : t * L ≤ s n ^ 2 / L := by
      rw [ht, sq L, ← Nat.div_div_eq_div_mul]
      exact Nat.div_mul_le_self _ L
    linarith [Nat.mul_le_mul_left t hlogt]
  have hc_mul : (c + 1) * (2 * (s n ^ 2 / L)) ≤ s n ^ 2 := by
    linarith [Nat.mul_le_mul_right (s n ^ 2 / L) (show 2 * (c + 1) ≤ L by omega),
      Nat.mul_div_le (s n ^ 2) L]
  have hsdiv : c ≤ s n ^ 2 / L := (Nat.le_div_iff_mul_le hLpos).mpr
    ((Nat.mul_le_mul_right _ (by omega)).trans
      ((sq L).symm.trans_le (hL2.trans (Nat.le_self_pow (by decide) _))))
  rw [hmax]
  nlinarith [Nat.mul_le_mul_left c ht_log]

/-- **Logarithmic-factor sharpening for constructible space**: for any space-constructible `s`
with `n ≤ s n` eventually, `DTIME encBits (fun n => s n ^ 2 / (Nat.log2 (s n) + 1) ^ 2)` is
strictly contained in `DSPACE encBits s`. -/
theorem DTIME_sq_div_log2_sq_ssubset_DSPACE {s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hn : ∀ᶠ n in atTop, n ≤ s n) :
    DTIME encBits (fun n => s n ^ 2 / (Nat.log2 (s n) + 1) ^ 2) ⊂ DSPACE encBits s :=
  DTIME_ssubset_DSPACE_of_mul_log2_le_sq hs (eventually_log2_le_of_eventually_le hn)
    (eventually_sq_div_log2_sq_mul_log2_le_sq hn)

/-- **Containment failure for the `s(n) ^ 2 / (⌊log₂ (s n)⌋ + 1) ^ 2` time bound**. -/
theorem DSPACE_not_subset_DTIME_sq_div_log2_sq {s : ℕ → ℕ} (hs : SpaceConstructible s)
    (hn : ∀ᶠ n in atTop, n ≤ s n) :
    ¬ DSPACE encBits s ⊆ DTIME encBits (fun n => s n ^ 2 / (Nat.log2 (s n) + 1) ^ 2) :=
  fun h => (DTIME_sq_div_log2_sq_ssubset_DSPACE hs hn).not_superset h

/-- **Polynomial time–space separation**: for `1 ≤ b` and `a < 2 * b`, deterministic time
`n ^ a` is strictly contained in deterministic space `n ^ b`. In particular, linear time
(`a = 1`, `b = 1`) is strictly contained in linear space. -/
theorem DTIME_pow_ssubset_DSPACE_pow {a b : ℕ} (hb : 1 ≤ b) (hab : a < 2 * b) :
    DTIME encBits (· ^ a) ⊂ DSPACE encBits (· ^ b) := by
  have hEq : DSPACE encBits (fun n => (n + 1) ^ b) = DSPACE encBits (· ^ b) :=
    Set.Subset.antisymm (DSPACE_mono_of_le_mul_add (Nat.add_one_pow_le_two_pow_mul_add b))
      (DSPACE_mono fun n => Nat.pow_le_pow_left (Nat.le_succ n) b)
  refine (DTIME_mono_of_eventually_le ?_).trans_ssubset (lt_of_lt_of_eq
    (DTIME_rpow_sub_ssubset_DSPACE (spaceConstructible_succ_pow b)
      (Eventually.of_forall fun n => (Nat.le_succ n).trans (Nat.le_self_pow (by omega) _))
      (one_div_pos.mpr (Nat.cast_pos.mpr hb))) hEq)
  filter_upwards [eventually_ge_atTop 2] with n _
  have hab' : (a : ℝ) + 1 ≤ 2 * (b : ℝ) := mod_cast hab
  have hexp : (a : ℝ) ≤ (b : ℝ) * (2 - 1 / (b : ℝ)) := by
    rw [mul_sub, mul_div_cancel₀ _ (by positivity : (b : ℝ) ≠ 0)]
    linarith [hab']
  have hreal : ((n ^ a : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ ((b : ℝ) * (2 - 1 / (b : ℝ))) := by
    calc ((n ^ a : ℕ) : ℝ) = (n : ℝ) ^ (a : ℝ) := by rw [Nat.cast_pow, ← Real.rpow_natCast]
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ (a : ℝ) :=
            Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast Nat.le_succ n)
              (Nat.cast_nonneg a)
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ ((b : ℝ) * (2 - 1 / (b : ℝ))) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.le_add_left 1 n) hexp
  refine Nat.le_floor (hreal.trans_eq ?_)
  push_cast
  rw [← Real.rpow_natCast ((n : ℝ) + 1) b, ← Real.rpow_mul (by positivity)]

/-- **Polynomial containment failure**: deterministic space `n ^ b` (`b ≥ 1`) is not contained in
deterministic time `n ^ a` when `a < 2 * b`. -/
theorem DSPACE_pow_not_subset_DTIME_pow {a b : ℕ} (hb : 1 ≤ b) (hab : a < 2 * b) :
    ¬ DSPACE encBits (· ^ b) ⊆ DTIME encBits (· ^ a) :=
  fun h => (DTIME_pow_ssubset_DSPACE_pow hb hab).not_superset h

/-! ### Linear-space separations -/

/-- **Linear space vs. subquadratic time**: for every real `ε > 0`,
`DTIME encBits (fun n => ⌊(n : ℝ) ^ (2 - ε)⌋₊) ⊂ DSPACE encBits (fun n => n)`. -/
theorem DTIME_rpow_sub_ssubset_DSPACE_id {ε : ℝ} (hε : 0 < ε) :
    DTIME encBits (fun n => ⌊(n : ℝ) ^ (2 - ε)⌋₊) ⊂ DSPACE encBits (fun n => n) :=
  DTIME_rpow_sub_ssubset_DSPACE spaceConstructible_id (Eventually.of_forall fun _ => le_rfl) hε

/-- **Exponent-below-two form for linear space**: for every real `α < 2`,
`DTIME encBits (fun n => ⌊(n : ℝ) ^ α⌋₊) ⊂ DSPACE encBits (fun n => n)`. -/
theorem DTIME_rpow_lt_two_ssubset_DSPACE_id {α : ℝ} (hα : α < 2) :
    DTIME encBits (fun n => ⌊(n : ℝ) ^ α⌋₊) ⊂ DSPACE encBits (fun n => n) :=
  DTIME_rpow_lt_two_ssubset_DSPACE spaceConstructible_id (Eventually.of_forall fun _ => le_rfl) hα

/-- **Linear time is strictly contained in linear space**:
`DTIME encBits (fun n => n) ⊂ DSPACE encBits (fun n => n)`. -/
theorem DTIME_id_ssubset_DSPACE_id :
    DTIME encBits (fun n => n) ⊂ DSPACE encBits (fun n => n) := by
  simpa only [pow_one] using DTIME_pow_ssubset_DSPACE_pow (a := 1) (b := 1) le_rfl (by decide)

/-- **Linear space is not contained in subquadratic deterministic time**: for every real `ε > 0`,
`¬ DSPACE encBits (fun n => n) ⊆ DTIME encBits (fun n => ⌊(n : ℝ) ^ (2 - ε)⌋₊)`. -/
theorem DSPACE_id_not_subset_DTIME_rpow_sub {ε : ℝ} (hε : 0 < ε) :
    ¬ DSPACE encBits (fun n => n) ⊆ DTIME encBits (fun n => ⌊(n : ℝ) ^ (2 - ε)⌋₊) :=
  fun h => (DTIME_rpow_sub_ssubset_DSPACE_id hε).not_superset h

/-- **Sharper linear-space separation**:
`DTIME encBits (fun n => n ^ 2 / (Nat.log2 n + 1) ^ 2) ⊂ DSPACE encBits (fun n => n)`. -/
theorem DTIME_sq_div_log2_sq_ssubset_DSPACE_id :
    DTIME encBits (fun n => n ^ 2 / (Nat.log2 n + 1) ^ 2) ⊂ DSPACE encBits (fun n => n) :=
  DTIME_sq_div_log2_sq_ssubset_DSPACE spaceConstructible_id (Eventually.of_forall fun _ => le_rfl)

/-- **Linear space is not contained in `DTIME (n ^ 2 / (⌊log₂ n⌋ + 1) ^ 2)`**. -/
theorem DSPACE_id_not_subset_DTIME_sq_div_log2_sq :
    ¬ DSPACE encBits (fun n => n) ⊆ DTIME encBits (fun n => n ^ 2 / (Nat.log2 n + 1) ^ 2) :=
  fun h => DTIME_sq_div_log2_sq_ssubset_DSPACE_id.not_superset h

/-- The explicit linear-space diagonal problem `{x | spaceDiagonal (fun n => 4 * n) x = true}`
belongs to `DSPACE encBits (fun n => n)`. -/
theorem setOf_spaceDiagonal_id_mem_DSPACE :
    {x | spaceDiagonal (fun n => 4 * n) x = true} ∈ DSPACE encBits (fun n => n) :=
  setOf_spaceDiagonal_four_mul_mem_DSPACE spaceConstructible_id Nat.log2_le_self

/-- The explicit linear-space diagonal problem `{x | spaceDiagonal (fun n => 4 * n) x = true}`
is outside `DTIME encBits (fun n => ⌊(n : ℝ) ^ (2 - ε)⌋₊)` for every `ε > 0`. -/
theorem setOf_spaceDiagonal_id_notMem_DTIME_rpow_sub {ε : ℝ} (hε : 0 < ε) :
    {x | spaceDiagonal (fun n => 4 * n) x = true} ∉
      DTIME encBits (fun n => ⌊(n : ℝ) ^ (2 - ε)⌋₊) :=
  setOf_spaceDiagonal_notMem_DTIME Nat.log2_le_self
    (eventually_mul_sqrt_add_le_of_mul_add_le_sq
      (eventually_rpow_sub_mul_log2_le_sq (Eventually.of_forall fun _ => le_rfl) hε))

/-- The explicit linear-space diagonal problem `{x | spaceDiagonal (fun n => 4 * n) x = true}`
is outside `DTIME encBits (fun n => n ^ 2 / (Nat.log2 n + 1) ^ 2)`. -/
theorem setOf_spaceDiagonal_id_notMem_DTIME_sq_div_log2_sq :
    {x | spaceDiagonal (fun n => 4 * n) x = true} ∉
      DTIME encBits (fun n => n ^ 2 / (Nat.log2 n + 1) ^ 2) :=
  setOf_spaceDiagonal_notMem_DTIME Nat.log2_le_self
    (eventually_mul_sqrt_add_le_of_mul_add_le_sq
      (eventually_sq_div_log2_sq_mul_log2_le_sq (Eventually.of_forall fun _ => le_rfl)))

end Cslib.Complexity
