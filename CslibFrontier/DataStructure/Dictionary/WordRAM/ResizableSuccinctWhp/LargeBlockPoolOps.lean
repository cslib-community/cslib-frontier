/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeBlockPoolBalanced
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Deamortized Hysteresis, Top-Boundary Lyapunov Debt, and `O(1)` `BlockPoolState` Operations

This module completes the pure mathematical correctness and worst-case `O(1)` rebalance invariants
of `BlockPoolState` (`LargeBlockPoolState`, `LargeBlockPoolBalanced`) for the SOSA 2024 resizable
succinct dictionary ([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 4–6][BenderFarachColtonKuszmaulKuszmaul2024]).

## Main definitions

* `BlockPoolState.BktHyst`: per-bucket hysteresis invariant parameterized by remaining ticks
  `t ≤ 16`.
* `BlockPoolState.blkWork`, `BlockPoolState.topDebt`: top-boundary Lyapunov debt at
  `P = B_full - 2`, decreasing by `1` per `topCleanOne` step whenever `0 < topDebt`.
* `BlockPoolState.Balanced`: full resting invariant (`CoreValid`, `BktHyst · 0`,
  `P + 2 ≤ B_full` on non-`UnreservedTail` and `TopSwap` blocks, `topDebt ≤ 16 * rem`, and
  `bktCount b ≤ maxSlabs * K`).
* `BlockPoolState.bktTickOne`, `BlockPoolState.runBktTicks`, `BlockPoolState.runTopCleanTicks`,
  `BlockPoolState.rawPostAppend`, `BlockPoolState.prepPopBktBack`,
  `BlockPoolState.commitPopBktBack`: `O(1)` step primitives used by `LargeBlockPool`.

## Main results

* `BlockPoolState.empty_balanced`: `empty M K maxSlabs` is `Balanced`.
* `BlockPoolState.Balanced.rawPostAppend_spec`, `BlockPoolState.StepInv.bktTickOne_spec`,
  `BlockPoolState.Balanced.postAppend_runBktTicks_balanced`: `rawPostAppend` followed by `16`
  `bktTickOne` steps restores `Balanced`.
* `BlockPoolState.Balanced.prepPopBktBack_spec`, `BlockPoolState.Balanced.commitPopBktBack_spec`,
  `BlockPoolState.StepInv.topCleanOne_debt_spec`,
  `BlockPoolState.Balanced.popBktBack_rebalance_balanced`:
  `prepPopBktBack` + `commitPopBktBack` followed by `16` `bktTickOne` steps and `16` `topCleanOne`
  steps restores `Balanced`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 4–6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

open scoped BigOperators

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.DataStructure.WordRAM.Resizable.Randomized
open Finset

namespace BlockPoolState

/-! ## Section 1: Per-Bucket Hysteresis `BktHyst` and Unreserved-Block Supply Bounds -/

/-- Per-bucket hysteresis invariant with `t ≤ 16` remaining rebalance ticks (`t = 0` at rest):
* Idle (`actCode b = 0`): `r b < 5 * K` (or `t = 16 ∧ r b = 5 * K`), and when `0 < q b`,
  `7 * K < 2 * r b` (or `t = 16 ∧ 7 * K ≤ 2 * (r b + 1) ∧ 2 * r b ≤ 7 * K`).
* `Promote` (`1 ≤ actCode b ≤ K`, `cur = actCur b < K`):
  `80 * K ≤ 16 * r b + cur + t ∧ 16 * r b ≤ 80 * K + cur + t`.
* `Demote` (`K < actCode b`, `1 ≤ cur = actCur b ≤ K`):
  `71 * K + cur ≤ 16 * r b + t ∧ 16 * r b + cur ≤ 73 * K + t`. -/
@[expose] def BktHyst (bp : BlockPoolState) (b t : ℕ) : Prop :=
  if bp.actCode b = 0 then
    (bp.r b < 5 * bp.K ∨ (t = 16 ∧ bp.r b = 5 * bp.K)) ∧
    (0 < bp.q b →
      7 * bp.K < 2 * bp.r b ∨
      (t = 16 ∧ 7 * bp.K ≤ 2 * (bp.r b + 1) ∧ 2 * bp.r b ≤ 7 * bp.K))
  else if bp.actCode b ≤ bp.K then
    80 * bp.K ≤ 16 * bp.r b + bp.actCur b + t ∧
    16 * bp.r b ≤ 80 * bp.K + bp.actCur b + t
  else
    71 * bp.K + bp.actCur b ≤ 16 * bp.r b + t ∧
    16 * bp.r b + bp.actCur b ≤ 73 * bp.K + t

theorem BktHyst.r_bounds {bp : BlockPoolState} {b t : ℕ} (hK : 64 ≤ bp.K)
    (hc_le : bp.actCode b ≤ 2 * bp.K) (ht : t ≤ 16) (hh : bp.BktHyst b t) :
    bp.r b < 6 * bp.K ∧
    (bp.actCode b ≠ 0 → 4 * bp.K ≤ bp.r b ∧ bp.actCur b + 1 ≤ bp.r b) := by
  have hcur_le := actCur_le_K hc_le
  unfold BktHyst at hh
  by_cases hc0 : bp.actCode b = 0
  · rw [ite_eq_left hc0] at hh
    exact ⟨by omega, fun hne => absurd hc0 hne⟩
  · rw [ite_eq_right hc0] at hh
    by_cases hcK : bp.actCode b ≤ bp.K
    · rw [ite_eq_left hcK] at hh
      have hcur_lt : bp.actCur b < bp.K := by
        unfold actCur; rw [ite_eq_right hc0, ite_eq_left hcK]; omega
      exact ⟨by omega, fun _ => ⟨by omega, by omega⟩⟩
    · rw [ite_eq_right hcK] at hh
      exact ⟨by omega, fun _ => ⟨by omega, by omega⟩⟩

theorem BktHyst.pos_r_and_actCur_lt {bp : BlockPoolState} {b : ℕ} (hK : 64 ≤ bp.K)
    (hc_le : bp.actCode b ≤ 2 * bp.K) (hh : bp.BktHyst b 0) (hcnt : 0 < bp.bktCount b) :
    1 ≤ bp.r b ∧ bp.actCur b ≤ bp.r b - 1 := by
  by_cases hc0 : bp.actCode b = 0
  · unfold BktHyst at hh
    rw [ite_eq_left hc0] at hh
    have hac0 : bp.actCur b = 0 := by unfold actCur; rw [ite_eq_left hc0]
    rw [hac0]
    by_cases hq0 : bp.q b = 0
    · unfold bktCount at hcnt; rw [hq0] at hcnt; omega
    · have h2 := hh.2 (Nat.pos_of_ne_zero hq0)
      omega
  · obtain ⟨_, hact⟩ := hh.r_bounds hK hc_le (Nat.zero_le 16)
    obtain ⟨_, hlt⟩ := hact hc0
    omega

/-- Active-bucket lower bound on `∑ b ∈ S, bp.r b` when every active bucket has `r ≥ 4 * K`. -/
private theorem sum_r_act_ge {bp : BlockPoolState}
    (hact_ge : ∀ b < bp.M, bp.actCode b ≠ 0 → 4 * bp.K ≤ bp.r b) :
    bp.actBucketCount * (4 * bp.K) ≤
      ∑ b ∈ (Finset.range bp.M).filter (fun b => bp.actCode b ≠ 0), bp.r b := by
  unfold actBucketCount
  rw [← smul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum fun b hb => by
    obtain ⟨h1, h2⟩ := mem_filter.mp hb
    exact hact_ge b (mem_range.mp h1) h2

/-- Supply guarantee for `Promote`: if `bp.CoreValid`, every active bucket satisfies `BktHyst · t'`
(`t' ≤ 16`), and idle bucket `b < M` has `5 * bp.K ≤ bp.r b`, then `5 ≤ bp.unresLen`. -/
theorem CoreValid.unresLen_ge_five_of_promote {bp : BlockPoolState} (hv : bp.CoreValid)
    {b : ℕ} (hb : b < bp.M) (hc0 : bp.actCode b = 0) (hr5 : 5 * bp.K ≤ bp.r b)
    (hact : ∀ b' < bp.M, bp.actCode b' ≠ 0 → ∃ t' ≤ 16, bp.BktHyst b' t') :
    5 ≤ bp.unresLen := by
  have hK64 := hv.K_ge
  have hK : 0 < bp.K := hv.K_pos
  have hrem_lt : bp.rem < bp.K := Nat.mod_lt bp.nSide hK
  have hact_ge : ∀ b' < bp.M, bp.actCode b' ≠ 0 → 4 * bp.K ≤ bp.r b' := fun b' hb' hne => by
    obtain ⟨t', ht', hh'⟩ := hact b' hb' hne
    exact ((hh'.r_bounds hK64 (hv.bkt_bounds b' hb').2.2.2.1 ht').2 hne).1
  set S_act := (Finset.range bp.M).filter (fun b' => bp.actCode b' ≠ 0)
  have hb_not : b ∉ S_act := fun hm => (mem_filter.mp hm).2 hc0
  have hsub : insert b S_act ⊆ Finset.range bp.M := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx'
    · exact mem_range.mpr hb
    · exact (mem_filter.mp hx').1
  have hsum_ge : 5 * bp.K + bp.actBucketCount * (4 * bp.K) ≤ ∑ x ∈ Finset.range bp.M, bp.r x := by
    calc 5 * bp.K + bp.actBucketCount * (4 * bp.K)
        ≤ bp.r b + ∑ x ∈ S_act, bp.r x := Nat.add_le_add hr5 (sum_r_act_ge hact_ge)
      _ = ∑ x ∈ insert b S_act, bp.r x := (Finset.sum_insert hb_not).symm
      _ ≤ ∑ x ∈ Finset.range bp.M, bp.r x := Finset.sum_le_sum_of_subset hsub
  rw [hv.sum_r_eq_tail_supply] at hsum_ge
  by_contra hlt5
  have hmul : (bp.unresLen + bp.actBucketCount) * bp.K ≤ (4 + bp.actBucketCount) * bp.K :=
    Nat.mul_le_mul_right bp.K (by omega)
  rw [Nat.add_mul] at hmul
  nlinarith

/-- Supply guarantee for `TopSwap`: if `bp.CoreValid`, every bucket satisfies `BktHyst · 0`, and
some block `P < bp.B_full` has `bp.blkTag P = 1`, then `3 ≤ bp.unresLen`. -/
theorem CoreValid.unresLen_ge_three_of_slab {bp : BlockPoolState} (hv : bp.CoreValid)
    {P : ℕ} (hP : P < bp.B_full) (htag1 : bp.blkTag P = 1)
    (hhyst : ∀ b' < bp.M, bp.BktHyst b' 0) :
    3 ≤ bp.unresLen := by
  have hK64 := hv.K_ge
  have hK : 0 < bp.K := hv.K_pos
  have hrem_lt : bp.rem < bp.K := Nat.mod_lt bp.nSide hK
  obtain ⟨hb₀, hvp₀, _⟩ := hv.slab_bwd P hP htag1
  set b₀ := bp.blkMeta1 P
  have hq₀ : 0 < bp.q b₀ := Nat.zero_lt_of_lt hvp₀
  have hact_ge : ∀ b' < bp.M, bp.actCode b' ≠ 0 → 4 * bp.K ≤ bp.r b' := fun b' hb' hne =>
    (((hhyst b' hb').r_bounds hK64 (hv.bkt_bounds b' hb').2.2.2.1 (Nat.zero_le 16)).2 hne).1
  set S_act := (Finset.range bp.M).filter (fun b' => bp.actCode b' ≠ 0)
  by_cases hc₀ : bp.actCode b₀ = 0
  · have hh₀ := hhyst b₀ hb₀
    unfold BktHyst at hh₀
    rw [ite_eq_left hc₀] at hh₀
    have hr₀ : 3 * bp.K + 1 ≤ bp.r b₀ := by have := hh₀.2 hq₀; omega
    have hb_not : b₀ ∉ S_act := fun hm => (mem_filter.mp hm).2 hc₀
    have hsub : insert b₀ S_act ⊆ Finset.range bp.M := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx'
      · exact mem_range.mpr hb₀
      · exact (mem_filter.mp hx').1
    have hsum_ge : (3 * bp.K + 1) + bp.actBucketCount * (4 * bp.K) ≤
        ∑ x ∈ Finset.range bp.M, bp.r x := by
      calc (3 * bp.K + 1) + bp.actBucketCount * (4 * bp.K)
          ≤ bp.r b₀ + ∑ x ∈ S_act, bp.r x := Nat.add_le_add hr₀ (sum_r_act_ge hact_ge)
        _ = ∑ x ∈ insert b₀ S_act, bp.r x := (Finset.sum_insert hb_not).symm
        _ ≤ ∑ x ∈ Finset.range bp.M, bp.r x := Finset.sum_le_sum_of_subset hsub
    rw [hv.sum_r_eq_tail_supply] at hsum_ge
    by_contra hlt3
    have hmul : (bp.unresLen + bp.actBucketCount) * bp.K ≤ (2 + bp.actBucketCount) * bp.K :=
      Nat.mul_le_mul_right bp.K (by omega)
    rw [Nat.add_mul] at hmul
    nlinarith
  · have hpos_act : 1 ≤ bp.actBucketCount := by
      unfold actBucketCount
      exact Finset.card_pos.mpr ⟨b₀, mem_filter.mpr ⟨mem_range.mpr hb₀, hc₀⟩⟩
    have hsub : S_act ⊆ Finset.range bp.M := filter_subset _ _
    have hsum_ge : bp.actBucketCount * (4 * bp.K) ≤ ∑ x ∈ Finset.range bp.M, bp.r x :=
      (sum_r_act_ge hact_ge).trans (Finset.sum_le_sum_of_subset hsub)
    rw [hv.sum_r_eq_tail_supply] at hsum_ge
    by_contra hlt3
    have hmul : (bp.unresLen + bp.actBucketCount) * bp.K ≤ (2 + bp.actBucketCount) * bp.K :=
      Nat.mul_le_mul_right bp.K (by omega)
    nlinarith

/-! ## Section 2: Top-Boundary Debt `blkWork` / `topDebt` and Resting `Balanced` Invariant -/

/-- Remaining single-step evacuations needed to turn physical block `P` into `blkTag P = 0`
(assuming `TopSwap` is idle; bounded by `2 * K`). -/
@[expose] def blkWork (bp : BlockPoolState) (P : ℕ) : ℕ :=
  if bp.blkTag P = 0 then 0
  else if bp.blkTag P = 1 then bp.K
  else
    let b := bp.blkMeta1 P
    if bp.K < bp.actCode b then bp.actCur b
    else (bp.K - bp.actCur b) + bp.K

theorem CoreValid.blkWork_le_two_K {bp : BlockPoolState} (hv : bp.CoreValid) {P : ℕ}
    (hP : P < bp.B_full) :
    bp.blkWork P ≤ 2 * bp.K := by
  unfold blkWork
  by_cases ht0 : bp.blkTag P = 0
  · simp [ht0]
  · rw [ite_eq_right ht0]
    by_cases ht1 : bp.blkTag P = 1
    · rw [ite_eq_left ht1]; omega
    · rw [ite_eq_right ht1]; dsimp only
      have ht2 : bp.blkTag P = 2 := by have := hv.blkTag_lt P hP; omega
      obtain ⟨hb, _, _⟩ := hv.act_bwd P hP ht2
      have hcur_le := actCur_le_K (hv.bkt_bounds (bp.blkMeta1 P) hb).2.2.2.1
      split_ifs <;> omega

theorem CoreValid.blkWork_eq_zero_iff {bp : BlockPoolState} (hv : bp.CoreValid) {P : ℕ}
    (hP : P < bp.B_full) :
    bp.blkWork P = 0 ↔ bp.blkTag P = 0 := by
  have hK := hv.K_pos
  unfold blkWork
  by_cases ht0 : bp.blkTag P = 0
  · simp [ht0]
  · rw [ite_eq_right ht0]
    suffices hpos : 0 <
        (if bp.blkTag P = 1 then bp.K
         else
           let b := bp.blkMeta1 P
           if bp.K < bp.actCode b then bp.actCur b
           else (bp.K - bp.actCur b) + bp.K) by
      exact ⟨fun h => by omega, fun h => absurd h ht0⟩
    by_cases ht1 : bp.blkTag P = 1
    · rw [ite_eq_left ht1]; exact hK
    · rw [ite_eq_right ht1]; dsimp only
      have ht2 : bp.blkTag P = 2 := by have := hv.blkTag_lt P hP; omega
      obtain ⟨_, hc_ne, _⟩ := hv.act_bwd P hP ht2
      by_cases hgt : bp.K < bp.actCode (bp.blkMeta1 P)
      · rw [ite_eq_left hgt]
        unfold actCur; rw [ite_eq_right hc_ne, ite_eq_right (by omega)]; omega
      · rw [ite_eq_right hgt]; omega

/-- Oscillation-proof Lyapunov debt measuring remaining `topCleanOne` steps needed to clear
`P = B_full - 2` (`≤ 3 * K`). -/
@[expose] def topDebt (bp : BlockPoolState) : ℕ :=
  if bp.B_full < 2 then 0
  else
    let P := bp.B_full - 2
    if bp.topSwapAct = 0 then
      bp.blkWork P
    else if bp.topSwapSrc = P then
      bp.K - bp.topSwapCur
    else if bp.topSwapDst = P then
      (bp.K - bp.topSwapCur) + bp.blkWork bp.topSwapSrc
    else if bp.blkTag P = 0 then
      0
    else
      (bp.K - bp.topSwapCur) + bp.blkWork P

theorem CoreValid.topDebt_le_three_K {bp : BlockPoolState} (hv : bp.CoreValid) :
    bp.topDebt ≤ 3 * bp.K := by
  unfold topDebt
  by_cases hlt2 : bp.B_full < 2
  · rw [ite_eq_left hlt2]; exact Nat.zero_le _
  · rw [ite_eq_right hlt2]; dsimp only
    have hP_lt : bp.B_full - 2 < bp.B_full := by omega
    by_cases ha0 : bp.topSwapAct = 0
    · rw [ite_eq_left ha0]; exact (hv.blkWork_le_two_K hP_lt).trans (by omega)
    · rw [ite_eq_right ha0]
      have ha1 : bp.topSwapAct = 1 := by have := hv.topSwap_act_le; omega
      obtain ⟨_, hsrc_lt, _, _, _⟩ := hv.topSwap_valid ha1
      have hbw_s := hv.blkWork_le_two_K hsrc_lt
      have hbw_p := hv.blkWork_le_two_K hP_lt
      split_ifs <;> omega

theorem CoreValid.topDebt_eq_zero_iff {bp : BlockPoolState} (hv : bp.CoreValid) :
    bp.topDebt = 0 ↔
    (2 ≤ bp.B_full →
      bp.blkTag (bp.B_full - 2) = 0 ∧
      (bp.topSwapAct = 1 → bp.topSwapSrc ≠ bp.B_full - 2 ∧ bp.topSwapDst ≠ bp.B_full - 2)) := by
  have hK := hv.K_pos
  unfold topDebt
  by_cases hlt2 : bp.B_full < 2
  · rw [ite_eq_left hlt2]
    exact ⟨fun _ h => absurd h (not_le_of_gt hlt2), fun _ => rfl⟩
  · rw [ite_eq_right hlt2]; dsimp only
    have hge2 : 2 ≤ bp.B_full := by omega
    set P := bp.B_full - 2
    have hP_lt : P < bp.B_full := by dsimp only [P]; omega
    by_cases ha0 : bp.topSwapAct = 0
    · rw [ite_eq_left ha0, hv.blkWork_eq_zero_iff hP_lt]
      exact ⟨fun ht0 _ => ⟨ht0, fun h1 => by omega⟩, fun h => (h hge2).1⟩
    · rw [ite_eq_right ha0]
      have ha1 : bp.topSwapAct = 1 := by have := hv.topSwap_act_le; omega
      obtain ⟨hcur_lt, _, _, _, _⟩ := hv.topSwap_valid ha1
      by_cases hs : bp.topSwapSrc = P
      · rw [ite_eq_left hs]
        exact ⟨fun h => by omega, fun h => absurd hs (h hge2 |>.2 ha1 |>.1)⟩
      · rw [ite_eq_right hs]
        by_cases hd : bp.topSwapDst = P
        · rw [ite_eq_left hd]
          exact ⟨fun h => by omega, fun h => absurd hd (h hge2 |>.2 ha1 |>.2)⟩
        · rw [ite_eq_right hd]
          by_cases ht0 : bp.blkTag P = 0
          · rw [ite_eq_left ht0]
            exact ⟨fun _ _ => ⟨ht0, fun _ => ⟨hs, hd⟩⟩, fun _ => rfl⟩
          · rw [ite_eq_right ht0]
            exact ⟨fun h => by omega, fun h => absurd (h hge2).1 ht0⟩

/-- Full resting invariant of the deamortized `M`-bucket `BlockPoolState`. -/
structure Balanced (bp : BlockPoolState) : Prop where
  core : bp.CoreValid
  bktCount_le : ∀ b < bp.M, bp.bktCount b ≤ bp.maxSlabs * bp.K
  hyst : ∀ b < bp.M, bp.BktHyst b 0
  low_blk : ∀ P, bp.blkTag P ≠ 0 → P + 2 ≤ bp.B_full
  low_swap : bp.topSwapAct = 1 →
    bp.topSwapSrc + 2 ≤ bp.B_full ∧ bp.topSwapDst + 2 ≤ bp.B_full
  debt_le : bp.topDebt ≤ 16 * bp.rem

theorem empty_balanced {M K maxSlabs : ℕ} (hM : 1 ≤ M) (hK : 64 ≤ K) :
    (empty M K maxSlabs).Balanced where
  core := empty_coreValid hM hK
  bktCount_le := fun _ _ => by simp [bktCount, empty]
  hyst := fun _ _ => by
    unfold BktHyst; simp [empty]; omega
  low_blk := fun _ h => absurd rfl h
  low_swap := fun h => by simp [empty] at h
  debt_le := by simp [topDebt, empty, B_full]

theorem CoreValid.prom_q_lt_of_bktCount_le {bp : BlockPoolState} (hv : bp.CoreValid)
    {b : ℕ} (hb : b < bp.M) (hle : bp.bktCount b ≤ bp.maxSlabs * bp.K)
    (h_or : 5 * bp.K ≤ bp.r b ∨ bp.actCode b = bp.K) :
    bp.q b < bp.maxSlabs := by
  obtain ⟨_, _, _, _, hcur_le_r⟩ := hv.bkt_bounds b hb
  have hr1 : 1 ≤ bp.r b := by
    rcases h_or with h5 | hcK
    · have := hv.K_ge; omega
    · have hcur : bp.actCur b = bp.K - 1 := by
        unfold actCur; rw [hcK, ite_eq_right (by have := hv.K_ge; omega), ite_eq_left le_rfl]
      have := hv.K_ge; omega
  unfold bktCount at hle
  by_contra hge
  have hmul : bp.maxSlabs * bp.K ≤ bp.q b * bp.K :=
    Nat.mul_le_mul_right _ (Nat.le_of_not_lt hge)
  linarith

/-! ## Section 3: Stepwise Preservation of `BktHyst`, `low_blk`, `low_swap`, and `topDebt` -/

/-- Intermediate multi-tick state invariant parameterized by active tick bucket `b_tick` and
remaining bucket ticks `t ≤ 16`. -/
structure StepInv (bp : BlockPoolState) (b_tick t : ℕ) : Prop where
  core : bp.CoreValid
  bktCount_le : ∀ b < bp.M, bp.bktCount b ≤ bp.maxSlabs * bp.K
  t_le : t ≤ 16
  hyst_tick : b_tick < bp.M → bp.BktHyst b_tick t
  hyst_other : ∀ b < bp.M, b ≠ b_tick → bp.BktHyst b 0
  low_blk : ∀ P, bp.blkTag P ≠ 0 → P + 2 ≤ bp.B_full
  low_swap : bp.topSwapAct = 1 →
    bp.topSwapSrc + 2 ≤ bp.B_full ∧ bp.topSwapDst + 2 ≤ bp.B_full

/-- Single bucket rebalance tick: `maybeStartBktJob` followed by `actStepOne`. -/
@[expose] def bktTickOne (bp : BlockPoolState) (b : ℕ) : BlockPoolState × Option PhysSwap :=
  (bp.maybeStartBktJob b).actStepOne b

/-- Exact effect of `actStepOne` on `blkWork`, `blkTag`, `topSwap`, `B_full`, and `BktHyst` for
other buckets. -/
private theorem actStepOne_blkWork_and_hyst {bp : BlockPoolState} (hv : bp.CoreValid)
    {b : ℕ} (hb : b < bp.M) (hc_ne : bp.actCode b ≠ 0)
    (hcur_lt_r : bp.actCode b ≤ bp.K → bp.actCode b - 1 < bp.r b) :
    let bp' := (bp.actStepOne b).1
    (∀ P < bp.B_full,
      bp'.blkWork P = if P = bp.actBlk b then bp.blkWork P - 1 else bp.blkWork P) ∧
    0 < bp.blkWork (bp.actBlk b) ∧
    (∀ P, bp'.blkTag P ≠ 0 → bp.blkTag P ≠ 0) ∧
    bp'.M = bp.M ∧
    bp'.K = bp.K ∧
    bp'.maxSlabs = bp.maxSlabs ∧
    bp'.B_full = bp.B_full ∧
    bp'.topSwapAct = bp.topSwapAct ∧
    bp'.topSwapSrc = bp.topSwapSrc ∧
    bp'.topSwapDst = bp.topSwapDst ∧
    bp'.topSwapCur = bp.topSwapCur ∧
    (∀ b' ≠ b, ∀ t', bp.BktHyst b' t' → bp'.BktHyst b' t') := by
  have hK := hv.K_pos
  obtain ⟨_, _, _, hc_le, _⟩ := hv.bkt_bounds b hb
  obtain ⟨hP_lt, hP_tag2, hP_m1⟩ := hv.act_fwd b hb hc_ne
  have hbw_pos : 0 < bp.blkWork (bp.actBlk b) := by
    by_contra hz
    have h0 := (hv.blkWork_eq_zero_iff hP_lt).mp (by omega)
    rw [hP_tag2] at h0; exact absurd h0 (by decide)
  unfold actStepOne
  rw [ite_eq_right hc_ne]
  by_cases hcK : bp.actCode b ≤ bp.K
  · rw [ite_eq_left hcK]; dsimp only
    rw [ite_eq_right (not_le_of_gt (hcur_lt_r hcK))]
    rcases hsw : bp.swapTailCoords (bp.tailRing b ((bp.head b + (bp.actCode b - 1)) % (6 * bp.K)))
      (bp.blkMeta2 (bp.actBlk b) * bp.K + (bp.actCode b - 1)) with ⟨bp₁, osw⟩
    have hbp₁_eq : bp₁.M = bp.M ∧ bp₁.K = bp.K ∧ bp₁.maxSlabs = bp.maxSlabs ∧
        bp₁.nSide = bp.nSide ∧ bp₁.q = bp.q ∧ bp₁.r = bp.r ∧ bp₁.actCode = bp.actCode ∧
        bp₁.blkTag = bp.blkTag ∧ bp₁.blkMeta1 = bp.blkMeta1 ∧
        bp₁.topSwapAct = bp.topSwapAct ∧ bp₁.topSwapSrc = bp.topSwapSrc ∧
        bp₁.topSwapDst = bp.topSwapDst ∧ bp₁.topSwapCur = bp.topSwapCur := by
      unfold swapTailCoords at hsw
      split_ifs at hsw <;>
        (injection hsw with h1 _; rw [← h1]
         exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
    obtain ⟨hM₁, hK₁, hms₁, hn₁, hq₁, hr₁, hac₁, hbt₁, hbm1₁, htsa₁, htss₁, htsd₁, htsc₁⟩ :=
      hbp₁_eq
    have hcur_b : bp.actCur b = bp.actCode b - 1 := by
      unfold actCur; rw [ite_eq_right hc_ne, ite_eq_left hcK]
    by_cases hmid : (bp.actCode b - 1) + 1 < bp.K
    · rw [ite_eq_left hmid]; dsimp only
      set bp' : BlockPoolState := { bp₁ with actCode := set1 bp₁.actCode b (bp.actCode b + 1) }
      have hac'_b : bp'.actCur b = (bp.actCode b - 1) + 1 := by
        unfold actCur
        rw [show bp'.actCode b = bp.actCode b + 1 from set1_self _ _ _,
          show bp'.K = bp.K from hK₁, ite_eq_right (by omega), ite_eq_left (by omega)]
        omega
      have hac'_ne : ∀ b' ≠ b, bp'.actCur b' = bp.actCur b' := fun b' hne => by
        unfold actCur
        rw [show bp'.actCode b' = bp.actCode b' from
          (set1_of_ne _ _ _ _ hne).trans (congrFun hac₁ b'), show bp'.K = bp.K from hK₁]
      refine ⟨fun P hP => ?_, hbw_pos,
        fun P h => by rwa [show bp'.blkTag = bp.blkTag from hbt₁] at h,
        hM₁, hK₁, hms₁,
        by dsimp only [B_full]; rw [show bp'.nSide = bp.nSide from hn₁, show bp'.K = bp.K from hK₁],
        htsa₁, htss₁, htsd₁, htsc₁, fun b' hne t' hh => ?_⟩
      · unfold blkWork
        rw [show bp'.blkTag = bp.blkTag from hbt₁, show bp'.K = bp.K from hK₁,
          show bp'.blkMeta1 = bp.blkMeta1 from hbm1₁]
        by_cases hp : P = bp.actBlk b
        · subst hp
          rw [ite_eq_left rfl, hP_tag2, hP_m1]; dsimp only
          rw [hac'_b, hcur_b]
          simp only [show (2 : ℕ) = 0 ↔ False by decide, show (2 : ℕ) = 1 ↔ False by decide,
            ↓reduceIte, show bp'.actCode b = bp.actCode b + 1 from set1_self _ _ _]
          rw [ite_eq_right (by omega), ite_eq_right (by omega)]; omega
        · rw [ite_eq_right hp]
          by_cases ht0 : bp.blkTag P = 0
          · simp [ht0]
          · by_cases ht1 : bp.blkTag P = 1
            · simp [ht1]
            · simp only [ht0, ht1, ↓reduceIte]
              have ht2 : bp.blkTag P = 2 := by have := hv.blkTag_lt P hP; omega
              have hbe : bp.blkMeta1 P ≠ b := fun he =>
                hp ((hv.act_bwd P hP ht2).2.2.symm.trans (by rw [he]))
              rw [hac'_ne _ hbe,
                show bp'.actCode (bp.blkMeta1 P) = bp.actCode (bp.blkMeta1 P) from
                  (set1_of_ne _ _ _ _ hbe).trans (congrFun hac₁ _)]
      · unfold BktHyst at hh ⊢
        rw [hac'_ne b' hne,
          show bp'.actCode b' = bp.actCode b' from
            (set1_of_ne _ _ _ _ hne).trans (congrFun hac₁ b'),
          show bp'.K = bp.K from hK₁, show bp'.r b' = bp.r b' from congrFun hr₁ b',
          show bp'.q b' = bp.q b' from congrFun hq₁ b']
        exact hh
    · rw [ite_eq_right hmid]; dsimp only
      set bp₂ := bp₁.freeTb (bp₁.blkMeta2 (bp.actBlk b))
      set bp' : BlockPoolState :=
        { bp₂ with
          q := set1 bp₂.q b (bp₁.q b + 1)
          r := set1 bp₂.r b (bp₂.r b - bp.K)
          head := set1 bp₂.head b ((bp₂.head b + bp.K) % (6 * bp.K))
          actCode := set1 bp₂.actCode b 0
          slabOf := set2 bp₂.slabOf b (bp₁.q b) (bp.actBlk b)
          blkTag := set1 bp₂.blkTag (bp.actBlk b) 1
          blkMeta2 := set1 bp₂.blkMeta2 (bp.actBlk b) (bp₁.q b) }
      have hac'_ne : ∀ b' ≠ b, bp'.actCur b' = bp.actCur b' := fun b' hne => by
        unfold actCur
        rw [show bp'.actCode b' = bp.actCode b' from
          (set1_of_ne _ _ _ _ hne).trans (congrFun hac₁ b'), show bp'.K = bp.K from hK₁]
      refine ⟨fun P hP => ?_, hbw_pos, fun P h => ?_, hM₁, hK₁, hms₁,
        by dsimp only [B_full]; rw [show bp'.nSide = bp.nSide from hn₁, show bp'.K = bp.K from hK₁],
        htsa₁, htss₁, htsd₁, htsc₁, fun b' hne t' hh => ?_⟩
      · unfold blkWork
        rw [show bp'.K = bp.K from hK₁, show bp'.blkMeta1 = bp.blkMeta1 from hbm1₁,
          show bp'.blkTag = set1 bp.blkTag (bp.actBlk b) 1 from congrArg (set1 · _ 1) hbt₁]
        by_cases hp : P = bp.actBlk b
        · subst hp
          rw [ite_eq_left rfl, set1_self, hP_tag2, hP_m1]; dsimp only
          rw [hcur_b]
          simp only [show (1 : ℕ) = 0 ↔ False by decide, show (2 : ℕ) = 0 ↔ False by decide,
            show (2 : ℕ) = 1 ↔ False by decide, ↓reduceIte]
          rw [ite_eq_right (not_lt.mpr hcK)]
          omega
        · rw [ite_eq_right hp, set1_of_ne _ _ _ _ hp]
          by_cases ht0 : bp.blkTag P = 0
          · simp [ht0]
          · by_cases ht1 : bp.blkTag P = 1
            · simp [ht1]
            · simp only [ht0, ht1, ↓reduceIte]
              have ht2 : bp.blkTag P = 2 := by have := hv.blkTag_lt P hP; omega
              have hbe : bp.blkMeta1 P ≠ b := fun he =>
                hp ((hv.act_bwd P hP ht2).2.2.symm.trans (by rw [he]))
              rw [hac'_ne _ hbe,
                show bp'.actCode (bp.blkMeta1 P) = bp.actCode (bp.blkMeta1 P) from
                  (set1_of_ne _ _ _ _ hbe).trans (congrFun hac₁ _)]
      · dsimp only [bp', bp₂, freeTb] at h
        rw [hbt₁] at h
        by_cases hp : P = bp.actBlk b
        · subst hp; rw [hP_tag2]; decide
        · rwa [set1_of_ne _ _ _ _ hp] at h
      · unfold BktHyst at hh ⊢
        rw [hac'_ne b' hne,
          show bp'.actCode b' = bp.actCode b' from
            (set1_of_ne _ _ _ _ hne).trans (congrFun hac₁ b'),
          show bp'.K = bp.K from hK₁,
          show bp'.r b' = bp.r b' from (set1_of_ne _ _ _ _ hne).trans (congrFun hr₁ b'),
          show bp'.q b' = bp.q b' from (set1_of_ne _ _ _ _ hne).trans (congrFun hq₁ b')]
        exact hh
  · -- Demote step (`K < actCode b`)
    rw [ite_eq_right hcK]; dsimp only
    set cur := bp.actCode b - bp.K
    have hcur_b : bp.actCur b = cur := by unfold actCur; rw [ite_eq_right hc_ne, ite_eq_right hcK]
    set bp₁ : BlockPoolState :=
      { bp with
        tailRing := set2 bp.tailRing b ((bp.head b + (cur - 1)) % (6 * bp.K))
          (bp.blkMeta2 (bp.actBlk b) * bp.K + (cur - 1))
        tailOwnerBkt := set1 bp.tailOwnerBkt (bp.blkMeta2 (bp.actBlk b) * bp.K + (cur - 1)) b
        tailOwnerRing := set1 bp.tailOwnerRing (bp.blkMeta2 (bp.actBlk b) * bp.K + (cur - 1))
          ((bp.head b + (cur - 1)) % (6 * bp.K)) }
    by_cases hgt1 : 1 < cur
    · rw [ite_eq_left hgt1]; dsimp only
      set bp' : BlockPoolState := { bp₁ with actCode := set1 bp₁.actCode b (bp.actCode b - 1) }
      have hac'_b : bp'.actCur b = cur - 1 := by
        unfold actCur
        rw [show bp'.actCode b = bp.actCode b - 1 from set1_self _ _ _,
          show bp'.K = bp.K from rfl, ite_eq_right (by dsimp only [cur] at hgt1; omega),
          ite_eq_right (by dsimp only [cur] at hgt1; omega)]
        dsimp only [cur]; omega
      have hac'_ne : ∀ b' ≠ b, bp'.actCur b' = bp.actCur b' := fun b' hne => by
        unfold actCur
        rw [show bp'.actCode b' = bp.actCode b' from set1_of_ne _ _ _ _ hne,
          show bp'.K = bp.K from rfl]
      refine ⟨fun P hP => ?_, hbw_pos, fun P h => h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        fun b' hne t' hh => ?_⟩
      · unfold blkWork
        rw [show bp'.blkTag = bp.blkTag from rfl, show bp'.K = bp.K from rfl,
          show bp'.blkMeta1 = bp.blkMeta1 from rfl]
        by_cases hp : P = bp.actBlk b
        · subst hp
          rw [ite_eq_left rfl, hP_tag2, hP_m1]; dsimp only
          rw [hac'_b, hcur_b]
          simp only [show (2 : ℕ) = 0 ↔ False by decide, show (2 : ℕ) = 1 ↔ False by decide,
            ↓reduceIte, show bp'.actCode b = bp.actCode b - 1 from set1_self _ _ _]
          rw [ite_eq_left (by dsimp only [cur] at hgt1; omega), ite_eq_left (by omega)]
        · rw [ite_eq_right hp]
          by_cases ht0 : bp.blkTag P = 0
          · simp [ht0]
          · by_cases ht1 : bp.blkTag P = 1
            · simp [ht1]
            · simp only [ht0, ht1, ↓reduceIte]
              have ht2 : bp.blkTag P = 2 := by have := hv.blkTag_lt P hP; omega
              have hbe : bp.blkMeta1 P ≠ b := fun he =>
                hp ((hv.act_bwd P hP ht2).2.2.symm.trans (by rw [he]))
              rw [hac'_ne _ hbe,
                show bp'.actCode (bp.blkMeta1 P) = bp.actCode (bp.blkMeta1 P) from
                  set1_of_ne _ _ _ _ hbe]
      · unfold BktHyst at hh ⊢
        rw [hac'_ne b' hne, show bp'.actCode b' = bp.actCode b' from set1_of_ne _ _ _ _ hne,
          show bp'.K = bp.K from rfl, show bp'.r = bp.r from rfl, show bp'.q = bp.q from rfl]
        exact hh
    · rw [ite_eq_right hgt1]; dsimp only
      have hcur1 : cur = 1 := by dsimp only [cur] at hgt1 ⊢; omega
      set bp' : BlockPoolState :=
        { (bp₁.unresPush (bp.actBlk b)) with
          actCode := set1 (bp₁.unresPush (bp.actBlk b)).actCode b 0 }
      have hac'_ne : ∀ b' ≠ b, bp'.actCur b' = bp.actCur b' := fun b' hne => by
        unfold actCur
        rw [show bp'.actCode b' = bp.actCode b' from set1_of_ne _ _ _ _ hne,
          show bp'.K = bp.K from rfl]
      refine ⟨fun P hP => ?_, hbw_pos, fun P h => ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        fun b' hne t' hh => ?_⟩
      · unfold blkWork
        rw [show bp'.K = bp.K from rfl,
          show bp'.blkTag = set1 bp.blkTag (bp.actBlk b) 0 from rfl,
          show bp'.blkMeta1 = set1 bp.blkMeta1 (bp.actBlk b) bp.unresLen from rfl]
        by_cases hp : P = bp.actBlk b
        · subst hp
          rw [ite_eq_left rfl, set1_self, ite_eq_left rfl, hP_tag2, hP_m1]; dsimp only
          rw [hcur_b, hcur1]
          simp only [show (2 : ℕ) = 0 ↔ False by decide, show (2 : ℕ) = 1 ↔ False by decide,
            ↓reduceIte]
          rw [ite_eq_left (by omega)]
        · rw [ite_eq_right hp, set1_of_ne _ _ _ _ hp, set1_of_ne _ _ _ _ hp]
          by_cases ht0 : bp.blkTag P = 0
          · simp [ht0]
          · by_cases ht1 : bp.blkTag P = 1
            · simp [ht1]
            · simp only [ht0, ht1, ↓reduceIte]
              have ht2 : bp.blkTag P = 2 := by have := hv.blkTag_lt P hP; omega
              have hbe : bp.blkMeta1 P ≠ b := fun he =>
                hp ((hv.act_bwd P hP ht2).2.2.symm.trans (by rw [he]))
              rw [hac'_ne _ hbe,
                show bp'.actCode (bp.blkMeta1 P) = bp.actCode (bp.blkMeta1 P) from
                  set1_of_ne _ _ _ _ hbe]
      · rw [show bp'.blkTag = set1 bp.blkTag (bp.actBlk b) 0 from rfl] at h
        by_cases hp : P = bp.actBlk b
        · subst hp; rw [set1_self] at h; exact absurd rfl h
        · rwa [set1_of_ne _ _ _ _ hp] at h
      · unfold BktHyst at hh ⊢
        rw [hac'_ne b' hne, show bp'.actCode b' = bp.actCode b' from set1_of_ne _ _ _ _ hne,
          show bp'.K = bp.K from rfl, show bp'.r = bp.r from rfl, show bp'.q = bp.q from rfl]
        exact hh

/-- Monotonicity of `topDebt` whenever `B_full`, `K`, and `topSwap` are unchanged and `blkWork`
is pointwise non-increasing on `< B_full`. -/
private theorem topDebt_le_of_blkWork_le {bp bp' : BlockPoolState}
    (hBf : bp'.B_full = bp.B_full) (hK : bp'.K = bp.K)
    (htsa : bp'.topSwapAct = bp.topSwapAct) (htss : bp'.topSwapSrc = bp.topSwapSrc)
    (htsd : bp'.topSwapDst = bp.topSwapDst) (htsc : bp'.topSwapCur = bp.topSwapCur)
    (hsrc_lt : bp.topSwapAct ≠ 0 → bp.topSwapSrc < bp.B_full)
    (htag0 : ∀ P, bp'.blkTag P ≠ 0 → bp.blkTag P ≠ 0)
    (hbw : ∀ P < bp.B_full, bp'.blkWork P ≤ bp.blkWork P) :
    bp'.topDebt ≤ bp.topDebt := by
  unfold topDebt
  rw [hBf, hK, htsa, htss, htsd, htsc]
  by_cases hlt2 : bp.B_full < 2
  · rw [ite_eq_left hlt2, ite_eq_left hlt2]
  · rw [ite_eq_right hlt2, ite_eq_right hlt2]; dsimp only
    have hP_lt : bp.B_full - 2 < bp.B_full := by omega
    by_cases ha0 : bp.topSwapAct = 0
    · rw [ite_eq_left ha0, ite_eq_left ha0]; exact hbw _ hP_lt
    · rw [ite_eq_right ha0, ite_eq_right ha0]
      by_cases hs : bp.topSwapSrc = bp.B_full - 2
      · rw [ite_eq_left hs, ite_eq_left hs]
      · rw [ite_eq_right hs, ite_eq_right hs]
        by_cases hd : bp.topSwapDst = bp.B_full - 2
        · rw [ite_eq_left hd, ite_eq_left hd]
          exact Nat.add_le_add_left (hbw _ (hsrc_lt ha0)) _
        · rw [ite_eq_right hd, ite_eq_right hd]
          by_cases ht'0 : bp'.blkTag (bp.B_full - 2) = 0
          · rw [ite_eq_left ht'0]; exact Nat.zero_le _
          · rw [ite_eq_right ht'0, ite_eq_right (htag0 _ ht'0)]
            exact Nat.add_le_add_left (hbw _ hP_lt) _

/-- Active `BktHyst b t` (`t ≤ 16`, including `t = 0` for `topCleanOne`) advances cleanly under
`actStepOne b`. -/
private theorem actStepOne_bktHyst {bp : BlockPoolState} (hv : bp.CoreValid)
    {b t : ℕ} (hb : b < bp.M) (hc_ne : bp.actCode b ≠ 0)
    (ht : t ≤ 16) (hh : bp.BktHyst b t) :
    (bp.actStepOne b).1.BktHyst b (t - 1) := by
  have hK64 := hv.K_ge
  obtain ⟨_, _, _, hc_le, _⟩ := hv.bkt_bounds b hb
  obtain ⟨_, hact_bds⟩ := hh.r_bounds hK64 hc_le ht
  obtain ⟨_, hcur_lt_r⟩ := hact_bds hc_ne
  unfold BktHyst at hh
  rw [ite_eq_right hc_ne] at hh
  unfold actStepOne
  rw [ite_eq_right hc_ne]
  by_cases hcK : bp.actCode b ≤ bp.K
  · rw [ite_eq_left hcK] at hh ⊢; dsimp only
    have hcur_eq : bp.actCur b = bp.actCode b - 1 := by
      unfold actCur; rw [ite_eq_right hc_ne, ite_eq_left hcK]
    rw [hcur_eq] at hcur_lt_r hh
    rw [ite_eq_right (not_le_of_gt hcur_lt_r)]
    rcases hsw : bp.swapTailCoords (bp.tailRing b ((bp.head b + (bp.actCode b - 1)) % (6 * bp.K)))
      (bp.blkMeta2 (bp.actBlk b) * bp.K + (bp.actCode b - 1)) with ⟨bp₁, osw⟩
    have hbp₁_eq : bp₁.K = bp.K ∧ bp₁.q = bp.q ∧ bp₁.r = bp.r ∧ bp₁.actCode = bp.actCode := by
      unfold swapTailCoords at hsw
      split_ifs at hsw <;> (injection hsw with h1 _; rw [← h1]; exact ⟨rfl, rfl, rfl, rfl⟩)
    obtain ⟨hK₁, hq₁, hr₁, hac₁⟩ := hbp₁_eq
    by_cases hmid : (bp.actCode b - 1) + 1 < bp.K
    · rw [ite_eq_left hmid]; dsimp only
      set bp' : BlockPoolState := { bp₁ with actCode := set1 bp₁.actCode b (bp.actCode b + 1) }
      have hac'_b : bp'.actCur b = (bp.actCode b - 1) + 1 := by
        unfold actCur
        rw [show bp'.actCode b = bp.actCode b + 1 from set1_self _ _ _,
          show bp'.K = bp.K from hK₁, ite_eq_right (by omega), ite_eq_left (by omega)]
        omega
      unfold BktHyst
      rw [show bp'.actCode b = bp.actCode b + 1 from set1_self _ _ _,
        show bp'.K = bp.K from hK₁, show bp'.r b = bp.r b from congrFun hr₁ b,
        hac'_b, ite_eq_right (by omega), ite_eq_left (by omega)]
      omega
    · rw [ite_eq_right hmid]; dsimp only
      set bp₂ := bp₁.freeTb (bp₁.blkMeta2 (bp.actBlk b))
      set bp' : BlockPoolState :=
        { bp₂ with
          q := set1 bp₂.q b (bp₁.q b + 1)
          r := set1 bp₂.r b (bp₂.r b - bp.K)
          head := set1 bp₂.head b ((bp₂.head b + bp.K) % (6 * bp.K))
          actCode := set1 bp₂.actCode b 0
          slabOf := set2 bp₂.slabOf b (bp₁.q b) (bp.actBlk b)
          blkTag := set1 bp₂.blkTag (bp.actBlk b) 1
          blkMeta2 := set1 bp₂.blkMeta2 (bp.actBlk b) (bp₁.q b) }
      unfold BktHyst
      rw [show bp'.actCode b = 0 from set1_self _ _ _, ite_eq_left rfl,
        show bp'.K = bp.K from hK₁,
        show bp'.r b = bp.r b - bp.K by
          change set1 bp₂.r b (bp₂.r b - bp.K) b = _; rw [set1_self]; dsimp only [bp₂, freeTb]
          rw [hr₁]]
      exact ⟨Or.inl (by omega), fun _ => Or.inl (by omega)⟩
  · rw [ite_eq_right hcK] at hh ⊢; dsimp only
    set cur := bp.actCode b - bp.K
    have hcur_eq : bp.actCur b = cur := by unfold actCur; rw [ite_eq_right hc_ne, ite_eq_right hcK]
    rw [hcur_eq] at hh
    have hcur_pos : 1 ≤ cur := by dsimp only [cur]; omega
    set bp₁ : BlockPoolState :=
      { bp with
        tailRing := set2 bp.tailRing b ((bp.head b + (cur - 1)) % (6 * bp.K))
          (bp.blkMeta2 (bp.actBlk b) * bp.K + (cur - 1))
        tailOwnerBkt := set1 bp.tailOwnerBkt (bp.blkMeta2 (bp.actBlk b) * bp.K + (cur - 1)) b
        tailOwnerRing := set1 bp.tailOwnerRing (bp.blkMeta2 (bp.actBlk b) * bp.K + (cur - 1))
          ((bp.head b + (cur - 1)) % (6 * bp.K)) }
    by_cases hgt1 : 1 < cur
    · rw [ite_eq_left hgt1]; dsimp only
      set bp' : BlockPoolState := { bp₁ with actCode := set1 bp₁.actCode b (bp.actCode b - 1) }
      have hac'_b : bp'.actCur b = cur - 1 := by
        unfold actCur
        rw [show bp'.actCode b = bp.actCode b - 1 from set1_self _ _ _,
          show bp'.K = bp.K from rfl, ite_eq_right (by dsimp only [cur] at hgt1; omega),
          ite_eq_right (by dsimp only [cur] at hgt1; omega)]
        dsimp only [cur]; omega
      unfold BktHyst
      rw [show bp'.actCode b = bp.actCode b - 1 from set1_self _ _ _,
        show bp'.K = bp.K from rfl, show bp'.r b = bp.r b from rfl, hac'_b,
        ite_eq_right (by dsimp only [cur] at hgt1; omega),
        ite_eq_right (by dsimp only [cur] at hgt1; omega)]
      omega
    · rw [ite_eq_right hgt1]; dsimp only
      have hcur1 : cur = 1 := by omega
      set bp' : BlockPoolState :=
        { (bp₁.unresPush (bp.actBlk b)) with
          actCode := set1 (bp₁.unresPush (bp.actBlk b)).actCode b 0 }
      unfold BktHyst
      rw [show bp'.actCode b = 0 from set1_self _ _ _, ite_eq_left rfl,
        show bp'.K = bp.K from rfl, show bp'.r b = bp.r b from rfl]
      exact ⟨Or.inl (by omega), fun _ => Or.inl (by omega)⟩

/-- `maybeStartBktJob` preserves `StepInv` and never increases `topDebt`. -/
private theorem StepInv.maybeStartBktJob_step {bp : BlockPoolState} {b t : ℕ}
    (hsi : bp.StepInv b t) (hb : b < bp.M) :
    let bp_m := bp.maybeStartBktJob b
    bp_m.StepInv b t ∧
    bp_m.M = bp.M ∧
    bp_m.K = bp.K ∧
    bp_m.nSide = bp.nSide ∧
    (∀ b', bp_m.bktCount b' = bp.bktCount b') ∧
    bp_m.topDebt ≤ bp.topDebt ∧
    (∀ b' < bp.M, ∀ loc' < bp.bktCount b', bp_m.toPhys b' loc' = bp.toPhys b' loc') := by
  have hv := hsi.core
  have hK64 := hv.K_ge
  obtain ⟨hcv_m, hn_m, hbc_m, htp_m⟩ := hv.maybeStartBktJob_spec hb
  have hh_b := hsi.hyst_tick hb
  unfold maybeStartBktJob
  by_cases hc_nz : bp.actCode b ≠ 0
  · rw [ite_eq_left hc_nz]
    exact ⟨hsi, rfl, rfl, rfl, fun _ => rfl, le_rfl, fun _ _ _ _ => rfl⟩
  · rw [ite_eq_right hc_nz]
    push Not at hc_nz
    unfold BktHyst at hh_b
    rw [ite_eq_left hc_nz] at hh_b
    by_cases hr5 : 5 * bp.K ≤ bp.r b
    · have ht16 : t = 16 ∧ bp.r b = 5 * bp.K := by
        rcases hh_b.1 with hlt | h16
        · omega
        · exact h16
      have hq_lt : bp.q b < bp.maxSlabs :=
        hv.prom_q_lt_of_bktCount_le hb (hsi.bktCount_le b hb) (Or.inl hr5)
      have h5_ul : 5 ≤ bp.unresLen := hv.unresLen_ge_five_of_promote hb hc_nz hr5
        (fun b' hb' hne => by
          have hb_ne : b' ≠ b := fun he => by subst he; exact hne hc_nz
          exact ⟨0, Nat.zero_le 16, hsi.hyst_other b' hb' hb_ne⟩)
      have hprom : 5 * bp.K ≤ bp.r b ∧ bp.q b < bp.maxSlabs ∧ 5 ≤ bp.unresLen :=
        ⟨hr5, hq_lt, h5_ul⟩
      rw [ite_eq_left hprom]; dsimp only
      obtain ⟨_, hidx_lt, hP_add3, hP_avoids⟩ := hv.findPromoteIdx_spec h5_ul
      set idx := bp.findPromoteIdx
      set P_act := bp.unresStack idx
      set bp_m : BlockPoolState :=
        { (bp.unresRemoveAt idx) with
          blkTag := set1 (bp.unresRemoveAt idx).blkTag P_act 2
          blkMeta1 := set1 (bp.unresRemoveAt idx).blkMeta1 P_act b
          actBlk := set1 (bp.unresRemoveAt idx).actBlk b P_act
          actCode := set1 (bp.unresRemoveAt idx).actCode b 1 }
      have hcv_m' : bp_m.CoreValid := by
        unfold maybeStartBktJob at hcv_m
        rwa [ite_eq_right (not_not.mpr hc_nz), ite_eq_left hprom] at hcv_m
      have hac_m_b : bp_m.actCur b = 0 := by
        unfold actCur
        rw [show bp_m.actCode b = 1 from set1_self _ _ _, show bp_m.K = bp.K from rfl,
          ite_eq_right Nat.one_ne_zero, ite_eq_left (by omega)]
      have hac_m_ne : ∀ b' ≠ b, bp_m.actCur b' = bp.actCur b' := fun b' hne => by
        unfold actCur
        rw [show bp_m.actCode b' = bp.actCode b' from set1_of_ne _ _ _ _ hne,
          show bp_m.K = bp.K from rfl]
      have hsi_m : bp_m.StepInv b t :=
        { core := hcv_m'
          bktCount_le := fun b' hb' => hsi.bktCount_le b' hb'
          t_le := hsi.t_le
          hyst_tick := fun _ => by
            unfold BktHyst
            rw [show bp_m.actCode b = 1 from set1_self _ _ _, show bp_m.K = bp.K from rfl,
              show bp_m.r b = bp.r b from rfl, hac_m_b,
              ite_eq_right Nat.one_ne_zero, ite_eq_left (by omega), ht16.1, ht16.2]
            omega
          hyst_other := fun b' hb' hne => by
            have hh' := hsi.hyst_other b' hb' hne
            unfold BktHyst at hh' ⊢
            rw [hac_m_ne b' hne, show bp_m.actCode b' = bp.actCode b' from set1_of_ne _ _ _ _ hne,
              show bp_m.K = bp.K from rfl, show bp_m.r = bp.r from rfl, show bp_m.q = bp.q from rfl]
            exact hh'
          low_blk := fun P htag => by
            rw [show bp_m.blkTag = set1 bp.blkTag P_act 2 from rfl] at htag
            by_cases hp : P = P_act
            · subst hp; change P_act + 2 ≤ bp.B_full; omega
            · rw [set1_of_ne _ _ _ _ hp] at htag; exact hsi.low_blk P htag
          low_swap := hsi.low_swap }
      have hdebt_eq : bp_m.topDebt = bp.topDebt := by
        unfold topDebt
        rw [show bp_m.B_full = bp.B_full from rfl, show bp_m.K = bp.K from rfl,
          show bp_m.topSwapAct = bp.topSwapAct from rfl,
          show bp_m.topSwapSrc = bp.topSwapSrc from rfl,
          show bp_m.topSwapDst = bp.topSwapDst from rfl,
          show bp_m.topSwapCur = bp.topSwapCur from rfl]
        by_cases hlt2 : bp.B_full < 2
        · rw [ite_eq_left hlt2, ite_eq_left hlt2]
        · rw [ite_eq_right hlt2, ite_eq_right hlt2]; dsimp only
          set P := bp.B_full - 2
          have hP_ne_act : P ≠ P_act := by dsimp only [P]; omega
          have hP_lt_Bf : P < bp.B_full := by dsimp only [P]; omega
          have hbw_eq : ∀ Q < bp.B_full, Q ≠ P_act → bp_m.blkWork Q = bp.blkWork Q :=
            fun Q hQ hneQ => by
              unfold blkWork
              rw [show bp_m.K = bp.K from rfl,
                show bp_m.blkTag Q = bp.blkTag Q from set1_of_ne _ _ _ _ hneQ]
              by_cases ht0 : bp.blkTag Q = 0
              · simp [ht0]
              · by_cases ht1 : bp.blkTag Q = 1
                · simp [ht1]
                · simp only [ht0, ht1, ↓reduceIte]
                  have ht2 : bp.blkTag Q = 2 := by have := hv.blkTag_lt Q hQ; omega
                  have hPl : Q ≠ bp.unresStack (bp.unresLen - 1) := fun he => by
                    have ht0_l := (hv.unres_fwd (bp.unresLen - 1) (by omega)).2.1
                    rw [he, ht0_l] at ht2; exact absurd ht2 (by decide)
                  have hm1_Q : bp_m.blkMeta1 Q = bp.blkMeta1 Q := by
                    change set1 (if idx < bp.unresLen - 1 then
                      set1 bp.blkMeta1 (bp.unresStack (bp.unresLen - 1)) idx
                      else bp.blkMeta1) P_act b Q = _
                    rw [set1_of_ne _ _ _ _ hneQ]
                    split_ifs
                    · exact set1_of_ne _ _ _ _ hPl
                    · rfl
                  have hbe : bp.blkMeta1 Q ≠ b := fun he => by
                    have hne_c := (hv.act_bwd Q hQ ht2).2.1
                    rw [he, hc_nz] at hne_c; exact hne_c rfl
                  rw [hm1_Q, hac_m_ne _ hbe,
                    show bp_m.actCode (bp.blkMeta1 Q) = bp.actCode (bp.blkMeta1 Q) from
                      set1_of_ne _ _ _ _ hbe]
          by_cases ha0 : bp.topSwapAct = 0
          · rw [ite_eq_left ha0, ite_eq_left ha0, hbw_eq P hP_lt_Bf hP_ne_act]
          · rw [ite_eq_right ha0, ite_eq_right ha0]
            have ha1 : bp.topSwapAct = 1 := by have := hv.topSwap_act_le; omega
            obtain ⟨_, hS_lt, _, _, _⟩ := hv.topSwap_valid ha1
            have hS_ne_act : bp.topSwapSrc ≠ P_act :=
              (hP_avoids.resolve_left (by omega)).2.symm
            rw [show bp_m.blkTag P = bp.blkTag P from set1_of_ne _ _ _ _ hP_ne_act,
              hbw_eq bp.topSwapSrc hS_lt hS_ne_act, hbw_eq P hP_lt_Bf hP_ne_act]
      have htp_m' : ∀ b' < bp.M, ∀ loc' < bp.bktCount b',
          bp_m.toPhys b' loc' = bp.toPhys b' loc' := by
        unfold maybeStartBktJob at htp_m
        rwa [ite_eq_right (not_not.mpr hc_nz), ite_eq_left hprom] at htp_m
      exact ⟨hsi_m, rfl, rfl, rfl, fun _ => rfl, hdebt_eq.le, htp_m'⟩
    · have hnot_prom : ¬(5 * bp.K ≤ bp.r b ∧ bp.q b < bp.maxSlabs ∧ 5 ≤ bp.unresLen) :=
        fun h => hr5 h.1
      rw [ite_eq_right hnot_prom]
      by_cases hdem : 0 < bp.q b ∧ 2 * bp.r b ≤ 7 * bp.K
      · rw [ite_eq_left hdem]; dsimp only
        have ht16 : t = 16 ∧ 7 * bp.K ≤ 2 * (bp.r b + 1) ∧ 2 * bp.r b ≤ 7 * bp.K := by
          rcases hh_b.2 hdem.1 with hgt | h16
          · omega
          · exact h16
        set vp := bp.q b - 1
        have hvp_lt : vp < bp.q b := by dsimp only [vp]; omega
        obtain ⟨_, hP_tag1, _, _⟩ := hv.slab_fwd b hb vp hvp_lt
        set P_act := bp.slabOf b vp
        set bp₁ := bp.allocTbFor P_act
        set bp_m : BlockPoolState :=
          { bp₁ with
            q := set1 bp₁.q b vp
            r := set1 bp₁.r b (bp.r b + bp.K)
            head := set1 bp₁.head b ((bp.head b + 5 * bp.K) % (6 * bp.K))
            actBlk := set1 bp₁.actBlk b P_act
            actCode := set1 bp₁.actCode b (2 * bp.K)
            blkTag := set1 bp₁.blkTag P_act 2
            blkMeta1 := set1 bp₁.blkMeta1 P_act b }
        have hbp₁_eq : bp₁.M = bp.M ∧ bp₁.K = bp.K ∧ bp₁.maxSlabs = bp.maxSlabs ∧
            bp₁.nSide = bp.nSide ∧ bp₁.q = bp.q ∧ bp₁.r = bp.r ∧ bp₁.actCode = bp.actCode ∧
            bp₁.blkTag = bp.blkTag ∧ bp₁.blkMeta1 = bp.blkMeta1 ∧
            bp₁.topSwapAct = bp.topSwapAct ∧ bp₁.topSwapSrc = bp.topSwapSrc ∧
            bp₁.topSwapDst = bp.topSwapDst ∧ bp₁.topSwapCur = bp.topSwapCur := by
          dsimp only [bp₁]; unfold allocTbFor; split_ifs <;>
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        obtain ⟨hM₁, hK₁, hms₁, hn₁, hq₁, hr₁, hac₁, hbt₁, hbm1₁, htsa₁, htss₁, htsd₁, htsc₁⟩ :=
          hbp₁_eq
        have hcv_m' : bp_m.CoreValid := by
          unfold maybeStartBktJob at hcv_m
          rwa [ite_eq_right (not_not.mpr hc_nz), ite_eq_right hnot_prom, ite_eq_left hdem] at hcv_m
        have hbc_m' : ∀ b', bp_m.bktCount b' = bp.bktCount b' := by
          unfold maybeStartBktJob at hbc_m
          rwa [ite_eq_right (not_not.mpr hc_nz), ite_eq_right hnot_prom, ite_eq_left hdem] at hbc_m
        have htp_m' : ∀ b' < bp.M, ∀ loc' < bp.bktCount b',
            bp_m.toPhys b' loc' = bp.toPhys b' loc' := by
          unfold maybeStartBktJob at htp_m
          rwa [ite_eq_right (not_not.mpr hc_nz), ite_eq_right hnot_prom, ite_eq_left hdem] at htp_m
        have hac_m_b : bp_m.actCur b = bp.K := by
          unfold actCur
          rw [show bp_m.actCode b = 2 * bp.K from set1_self _ _ _, show bp_m.K = bp.K from hK₁,
            ite_eq_right (by omega), ite_eq_right (by omega)]
          omega
        have hac_m_ne : ∀ b' ≠ b, bp_m.actCur b' = bp.actCur b' := fun b' hne => by
          unfold actCur
          rw [show bp_m.actCode b' = bp.actCode b' from
            (set1_of_ne _ _ _ _ hne).trans (congrFun hac₁ b'), show bp_m.K = bp.K from hK₁]
        have hBf_m : bp_m.B_full = bp.B_full := by dsimp only [B_full]; rw [hn₁, hK₁]
        have hsi_m : bp_m.StepInv b t :=
          { core := hcv_m'
            bktCount_le := fun b' hb' => by
              rw [show bp_m.M = bp.M from hM₁] at hb'
              rw [hbc_m' b', show bp_m.maxSlabs = bp.maxSlabs from hms₁,
                show bp_m.K = bp.K from hK₁]
              exact hsi.bktCount_le b' hb'
            t_le := hsi.t_le
            hyst_tick := fun _ => by
              unfold BktHyst
              rw [show bp_m.actCode b = 2 * bp.K from set1_self _ _ _,
                show bp_m.K = bp.K from hK₁,
                show bp_m.r b = bp.r b + bp.K from set1_self _ _ _, hac_m_b,
                ite_eq_right (by omega), ite_eq_right (by omega), ht16.1]
              omega
            hyst_other := fun b' hb' hne => by
              rw [show bp_m.M = bp.M from hM₁] at hb'
              have hh' := hsi.hyst_other b' hb' hne
              unfold BktHyst at hh' ⊢
              rw [hac_m_ne b' hne,
                show bp_m.actCode b' = bp.actCode b' from
                  (set1_of_ne _ _ _ _ hne).trans (congrFun hac₁ b'),
                show bp_m.K = bp.K from hK₁,
                show bp_m.r b' = bp.r b' from (set1_of_ne _ _ _ _ hne).trans (congrFun hr₁ b'),
                show bp_m.q b' = bp.q b' from (set1_of_ne _ _ _ _ hne).trans (congrFun hq₁ b')]
              exact hh'
            low_blk := fun P htag => by
              rw [hBf_m]
              rw [show bp_m.blkTag = set1 bp.blkTag P_act 2 from congrArg (set1 · P_act 2) hbt₁]
                at htag
              by_cases hp : P = P_act
              · subst hp; exact hsi.low_blk P_act (by rw [hP_tag1]; decide)
              · rw [set1_of_ne _ _ _ _ hp] at htag; exact hsi.low_blk P htag
            low_swap := fun ha => by
              rw [hBf_m, htss₁, htsd₁]
              exact hsi.low_swap (htsa₁ ▸ ha) }
        have hbw_eq : ∀ Q < bp.B_full, bp_m.blkWork Q = bp.blkWork Q := fun Q hQ => by
          unfold blkWork
          rw [show bp_m.K = bp.K from hK₁,
            show bp_m.blkTag = set1 bp.blkTag P_act 2 from congrArg (set1 · P_act 2) hbt₁,
            show bp_m.blkMeta1 = set1 bp.blkMeta1 P_act b from congrArg (set1 · P_act b) hbm1₁]
          by_cases hp : Q = P_act
          · subst hp
            rw [set1_self, set1_self]; dsimp only
            rw [hac_m_b, hP_tag1,
              show bp_m.actCode b = 2 * bp.K from set1_self _ _ _]
            simp only [show (2 : ℕ) = 0 ↔ False by decide, show (2 : ℕ) = 1 ↔ False by decide,
              show (1 : ℕ) = 0 ↔ False by decide, ↓reduceIte]
            rw [ite_eq_left (by omega)]
          · rw [set1_of_ne _ _ _ _ hp, set1_of_ne _ _ _ _ hp]
            by_cases ht0 : bp.blkTag Q = 0
            · simp [ht0]
            · by_cases ht1 : bp.blkTag Q = 1
              · simp [ht1]
              · simp only [ht0, ht1, ↓reduceIte]
                have ht2 : bp.blkTag Q = 2 := by have := hv.blkTag_lt Q hQ; omega
                have hbe : bp.blkMeta1 Q ≠ b := fun he => by
                  have hne_c := (hv.act_bwd Q hQ ht2).2.1
                  rw [he, hc_nz] at hne_c; exact hne_c rfl
                rw [hac_m_ne _ hbe,
                  show bp_m.actCode (bp.blkMeta1 Q) = bp.actCode (bp.blkMeta1 Q) from
                    (set1_of_ne _ _ _ _ hbe).trans (congrFun hac₁ _)]
        have hdebt_le : bp_m.topDebt ≤ bp.topDebt :=
          topDebt_le_of_blkWork_le hBf_m hK₁ htsa₁ htss₁ htsd₁ htsc₁
            (fun ha => (hv.topSwap_valid (by have := hv.topSwap_act_le; omega)).2.1)
            (fun P htag => by
              rw [show bp_m.blkTag = set1 bp.blkTag P_act 2 from congrArg (set1 · P_act 2) hbt₁]
                at htag
              by_cases hp : P = P_act
              · subst hp; rw [hP_tag1]; decide
              · rwa [set1_of_ne _ _ _ _ hp] at htag)
            (fun Q hQ => (hbw_eq Q hQ).le)
        exact ⟨hsi_m, hM₁, hK₁, hn₁, hbc_m', hdebt_le, htp_m'⟩
      · rw [ite_eq_right hdem]
        exact ⟨hsi, rfl, rfl, rfl, fun _ => rfl, le_rfl, fun _ _ _ _ => rfl⟩

/-- One `bktTickOne` step advances `StepInv b t` to `StepInv b (t - 1)`, never increases `topDebt`,
emits at most 1 swap `< nSide`, and preserves all item lookups. -/
theorem StepInv.bktTickOne_spec {bp : BlockPoolState} {b t : ℕ}
    (hsi : bp.StepInv b t) (hb : b < bp.M) :
    let (bp', osw) := bp.bktTickOne b
    bp'.StepInv b (t - 1) ∧
    bp'.M = bp.M ∧
    bp'.K = bp.K ∧
    bp'.nSide = bp.nSide ∧
    (∀ b', bp'.bktCount b' = bp.bktCount b') ∧
    bp'.topDebt ≤ bp.topDebt ∧
    (∀ sw, osw = some sw → sw.p₁ < bp.nSide ∧ sw.p₂ < bp.nSide) ∧
    (∀ {α : Type*} (arr : ℕ → α) (b' loc' : ℕ),
      b' < bp.M → loc' < bp.bktCount b' →
      applyOptSwap osw arr (bp'.toPhys b' loc') = arr (bp.toPhys b' loc')) := by
  obtain ⟨hsi_m, hM_m, hK_m, hn_m, hbc_m, hdebt_m, htp_m⟩ := hsi.maybeStartBktJob_step hb
  set bp_m := bp.maybeStartBktJob b
  have hv_m := hsi_m.core
  have hb_m : b < bp_m.M := hM_m.symm ▸ hb
  have hprom_q : bp_m.actCode b = bp_m.K → bp_m.q b < bp_m.maxSlabs := fun hcK =>
    hv_m.prom_q_lt_of_bktCount_le hb_m (hsi_m.bktCount_le b hb_m) (Or.inr hcK)
  have hact_spec := hv_m.actStepOne_spec hb_m hprom_q
  rcases hstep : bp_m.actStepOne b with ⟨bp', osw⟩
  rw [hstep] at hact_spec
  obtain ⟨hcv', hn', hbc', hsw', harr'⟩ := hact_spec
  have hbp'_fst : bp' = (bp_m.actStepOne b).1 := by rw [hstep]
  by_cases hc0_m : bp_m.actCode b = 0
  · have hbp'_eq : bp' = bp_m ∧ osw = none := by
      unfold actStepOne at hstep; rw [ite_eq_left hc0_m] at hstep
      exact ⟨(Prod.mk.inj hstep).1.symm, (Prod.mk.inj hstep).2.symm⟩
    rw [show bp.bktTickOne b = (bp', osw) from hstep, hbp'_eq.1, hbp'_eq.2]
    have hh_sub : bp_m.BktHyst b (t - 1) := by
      have hv := hsi.core
      have h_bp_c0 : bp.actCode b = 0 := by
        by_contra hne
        have h_eq : bp_m = bp := by unfold bp_m maybeStartBktJob; rw [ite_eq_left hne]
        rw [h_eq] at hc0_m; exact hne hc0_m
      have hnot_r5 : ¬(5 * bp.K ≤ bp.r b) := fun hr5 => by
        have hq_lt := hv.prom_q_lt_of_bktCount_le hb (hsi.bktCount_le b hb) (Or.inl hr5)
        have h5_ul := hv.unresLen_ge_five_of_promote hb h_bp_c0 hr5
          (fun b' hb' hne => ⟨0, Nat.zero_le 16,
            hsi.hyst_other b' hb' (fun he => by subst he; exact hne h_bp_c0)⟩)
        have hm_act : bp_m.actCode b = 1 := by
          unfold bp_m maybeStartBktJob
          rw [ite_eq_right (not_not.mpr h_bp_c0), ite_eq_left ⟨hr5, hq_lt, h5_ul⟩]
          exact set1_self _ _ _
        rw [hm_act] at hc0_m; exact absurd hc0_m (by decide)
      have hnp : ¬(5 * bp.K ≤ bp.r b ∧ bp.q b < bp.maxSlabs ∧ 5 ≤ bp.unresLen) :=
        fun h => hnot_r5 h.1
      have hnot_dem : ¬(0 < bp.q b ∧ 2 * bp.r b ≤ 7 * bp.K) := fun hdem => by
        have hm_act : bp_m.actCode b = 2 * bp.K := by
          unfold bp_m maybeStartBktJob
          rw [ite_eq_right (not_not.mpr h_bp_c0), ite_eq_right hnp, ite_eq_left hdem]
          exact set1_self _ _ _
        have := hv.K_ge; rw [hm_act] at hc0_m; omega
      have h_eq : bp_m = bp := by
        unfold bp_m maybeStartBktJob
        rw [ite_eq_right (not_not.mpr h_bp_c0), ite_eq_right hnp, ite_eq_right hnot_dem]
      rw [h_eq]
      unfold BktHyst; rw [ite_eq_left h_bp_c0]
      exact ⟨Or.inl (by omega),
        fun hq0 => Or.inl (by by_contra hle; exact hnot_dem ⟨hq0, by omega⟩)⟩
    refine ⟨{ hsi_m with t_le := by have := hsi_m.t_le; omega, hyst_tick := fun _ => hh_sub },
      hM_m, hK_m, hn_m, hbc_m, hdebt_m, fun _ h => by simp at h,
      fun arr b' loc' hb' hloc' => congrArg arr (htp_m b' hb' loc' hloc')⟩
  · rw [show bp.bktTickOne b = (bp', osw) from hstep]
    have hh_m := hsi_m.hyst_tick hb_m
    obtain ⟨_, hact_bds⟩ := hh_m.r_bounds hv_m.K_ge (hv_m.bkt_bounds b hb_m).2.2.2.1 hsi_m.t_le
    obtain ⟨_, hcur_lt_r_m⟩ := hact_bds hc0_m
    have hcur_imp : bp_m.actCode b ≤ bp_m.K → bp_m.actCode b - 1 < bp_m.r b := fun hcK => by
      have hc_eq : bp_m.actCur b = bp_m.actCode b - 1 := by
        unfold actCur; rw [ite_eq_right hc0_m, ite_eq_left hcK]
      omega
    obtain ⟨hbw_step, _, htag_imp, hM', hK', hms', hBf', htsa', htss', htsd', htsc', hh_oth⟩ :=
      actStepOne_blkWork_and_hyst hv_m hb_m hc0_m hcur_imp
    rw [← hbp'_fst] at hbw_step htag_imp hM' hK' hms' hBf' htsa' htss' htsd' htsc' hh_oth
    have hh_sub : bp'.BktHyst b (t - 1) := by
      rw [hbp'_fst]; exact actStepOne_bktHyst hv_m hb_m hc0_m hsi_m.t_le hh_m
    have hdebt' : bp'.topDebt ≤ bp_m.topDebt :=
      topDebt_le_of_blkWork_le hBf' hK' htsa' htss' htsd' htsc'
        (fun ha => (hv_m.topSwap_valid (by have := hv_m.topSwap_act_le; omega)).2.1) htag_imp
        (fun P hP => by rw [hbw_step P hP]; split_ifs <;> omega)
    have hsi' : bp'.StepInv b (t - 1) :=
      { core := hcv'
        bktCount_le := fun b' hb' => by
          rw [hM'] at hb'
          rw [hbc' b', hms', hK']
          exact hsi_m.bktCount_le b' hb'
        t_le := by have := hsi_m.t_le; omega
        hyst_tick := fun _ => hh_sub
        hyst_other := fun b' hb' hne => by
          rw [hM'] at hb'
          exact hh_oth b' hne 0 (hsi_m.hyst_other b' hb' hne)
        low_blk := fun P htag => by
          rw [hBf']; exact hsi_m.low_blk P (htag_imp P htag)
        low_swap := fun ha => by
          rw [hBf', htss', htsd']; exact hsi_m.low_swap (htsa' ▸ ha) }
    refine ⟨hsi', hM'.trans hM_m, hK'.trans hK_m, hn'.trans hn_m,
      fun b' => (hbc' b').trans (hbc_m b'), hdebt'.trans hdebt_m,
      fun sw hsw => ?_, fun arr b' loc' hb' hloc' => ?_⟩
    · rw [← hn_m]; exact hsw' sw hsw
    · have hb_m' : b' < bp_m.M := hM_m.symm ▸ hb'
      have hloc_m' : loc' < bp_m.bktCount b' := (hbc_m b').symm ▸ hloc'
      exact (harr' arr b' loc' hb_m' hloc_m').trans (congrArg arr (htp_m b' hb' loc' hloc'))

/-- Run `t` bucket ticks on `(bp, arr)` synchronously. -/
def runBktTicks {α : Type*} (b : ℕ) :
    ℕ → BlockPoolState × (ℕ → α) → BlockPoolState × (ℕ → α)
  | 0, st => st
  | t + 1, (bp, arr) =>
    let (bp₁, osw) := bp.bktTickOne b
    runBktTicks b t (bp₁, applyOptSwap osw arr)

theorem StepInv.runBktTicks_spec {α : Type*} {b : ℕ} :
    ∀ t {bp : BlockPoolState} (_hb : b < bp.M), bp.StepInv b t → ∀ (arr : ℕ → α),
      let res := runBktTicks b t (bp, arr)
      res.1.StepInv b 0 ∧
      res.1.M = bp.M ∧
      res.1.K = bp.K ∧
      res.1.nSide = bp.nSide ∧
      (∀ b', res.1.bktCount b' = bp.bktCount b') ∧
      res.1.topDebt ≤ bp.topDebt ∧
      (∀ b' < bp.M, ∀ loc' < bp.bktCount b',
        res.2 (res.1.toPhys b' loc') = arr (bp.toPhys b' loc'))
  | 0, _, _hb, hsi, _ => ⟨hsi, rfl, rfl, rfl, fun _ => rfl, le_rfl, fun _ _ _ _ => rfl⟩
  | t + 1, bp, hb, hsi, arr => by
    have hstep := hsi.bktTickOne_spec hb
    rcases heq : bp.bktTickOne b with ⟨bp₁, osw⟩
    rw [heq] at hstep
    obtain ⟨hsi₁, hM₁, hK₁, hn₁, hbc₁, hdebt₁, _, harr₁⟩ := hstep
    unfold runBktTicks
    dsimp only; rw [heq]; dsimp only
    have ih := hsi₁.runBktTicks_spec t (hM₁.symm ▸ hb) (applyOptSwap osw arr)
    obtain ⟨hsi', hM', hK', hn', hbc', hdebt', harr'⟩ := ih
    refine ⟨hsi', hM'.trans hM₁, hK'.trans hK₁, hn'.trans hn₁,
      fun b' => (hbc' b').trans (hbc₁ b'), hdebt'.trans hdebt₁,
      fun b' hb' loc' hloc' => ?_⟩
    exact (harr' b' (hM₁.symm ▸ hb') loc' ((hbc₁ b').symm ▸ hloc')).trans
      (harr₁ arr b' loc' hb' hloc')

/-! ## Section 4: `topCleanOne` Strict Debt Descent and `runTopCleanTicks` -/

/-- Exact debt and invariant preservation for `topSwapStepOne` when `topSwapAct = 1` and
`low_blk` / `low_swap` hold. -/
private theorem StepInv.topSwapStepOne_debt_and_inv {bp : BlockPoolState} {b₀ : ℕ}
    (hsi : bp.StepInv b₀ 0) (ha1 : bp.topSwapAct = 1) :
    let bp' := (bp.topSwapStepOne).1
    bp'.StepInv b₀ 0 ∧
    bp'.M = bp.M ∧
    bp'.K = bp.K ∧
    bp'.nSide = bp.nSide ∧
    (∀ b', bp'.bktCount b' = bp.bktCount b') ∧
    (2 ≤ bp.B_full →
      (bp.topSwapSrc = bp.B_full - 2 ∨ bp.topSwapDst = bp.B_full - 2 ∨
        bp.blkTag (bp.B_full - 2) ≠ 0) →
      bp'.topDebt = bp.topDebt - 1) := by
  have hv := hsi.core
  have hK := hv.K_pos
  have hts_spec := hv.topSwapStepOne_spec.{0}
  rcases hts : bp.topSwapStepOne with ⟨bp_ts, osw_ts⟩
  rw [hts] at hts_spec
  obtain ⟨hcv_ts, _, _, _, _⟩ := hts_spec
  obtain ⟨hcur_lt, hS_lt, hD_lt, hD_tag0, hSD⟩ := hv.topSwap_valid ha1
  obtain ⟨hS_low, hD_low⟩ := hsi.low_swap ha1
  dsimp only
  unfold topSwapStepOne at hts
  rw [ite_eq_right (by omega : bp.topSwapAct ≠ 0)] at hts; dsimp only at hts
  by_cases hmid : bp.topSwapCur + 1 < bp.K
  · rw [ite_eq_left hmid] at hts
    injection hts with hts_eq _
    rw [← hts_eq]
    set bp' : BlockPoolState := { bp with topSwapCur := bp.topSwapCur + 1 }
    have hcv_m : bp'.CoreValid := hts_eq ▸ hcv_ts
    have hsi' : bp'.StepInv b₀ 0 :=
      { hsi with core := hcv_m }
    refine ⟨hsi', rfl, rfl, rfl, fun _ => rfl, fun hge2 hcond => ?_⟩
    unfold topDebt
    have hnot2 : ¬(bp.B_full < 2) := not_lt.mpr hge2
    have hbw_eq : ∀ Q, bp'.blkWork Q = bp.blkWork Q := fun _ => rfl
    simp only [show bp'.B_full = bp.B_full from rfl, show bp'.K = bp.K from rfl,
      show bp'.topSwapAct = 1 from ha1, ha1, show bp'.topSwapSrc = bp.topSwapSrc from rfl,
      show bp'.topSwapDst = bp.topSwapDst from rfl,
      show bp'.topSwapCur = bp.topSwapCur + 1 from rfl,
      show bp'.blkTag = bp.blkTag from rfl, hbw_eq, hnot2,
      show (1 : ℕ) = 0 ↔ False by decide, ↓reduceIte]
    set P := bp.B_full - 2
    by_cases hs : bp.topSwapSrc = P
    · rw [ite_eq_left hs, ite_eq_left hs]; omega
    · rw [ite_eq_right hs, ite_eq_right hs]
      by_cases hd : bp.topSwapDst = P
      · rw [ite_eq_left hd, ite_eq_left hd]; omega
      · rw [ite_eq_right hd, ite_eq_right hd]
        have htP : bp.blkTag P ≠ 0 := by
          rcases hcond with h | h | h
          · exact absurd h hs
          · exact absurd h hd
          · exact h
        rw [ite_eq_right htP, ite_eq_right htP]; omega
  · rw [ite_eq_right hmid] at hts
    injection hts with hts_eq _
    rw [← hts_eq]
    have hcur_top : bp.topSwapCur + 1 = bp.K := by omega
    set bp' := bp.commitTopSwap
    have hcv_c : bp'.CoreValid := hts_eq ▸ hcv_ts
    set S := bp.topSwapSrc
    set D := bp.topSwapDst
    have hcore_fields : bp'.M = bp.M ∧ bp'.K = bp.K ∧ bp'.maxSlabs = bp.maxSlabs ∧
        bp'.nSide = bp.nSide ∧ bp'.q = bp.q ∧ bp'.r = bp.r ∧ bp'.actCode = bp.actCode ∧
        bp'.topSwapAct = 0 ∧
        bp'.blkTag = set1 (set1 bp.blkTag S 0) D (bp.blkTag S) ∧
        bp'.blkMeta1 = set1 (set1 bp.blkMeta1 S (bp.blkMeta1 D)) D (bp.blkMeta1 S) := by
      dsimp only [bp']; unfold commitTopSwap; dsimp only
      split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨hM', hK', hms', hn_c, hq', hr', hac', htsa', hbt', hbm1'⟩ := hcore_fields
    have hBf' : bp'.B_full = bp.B_full := by dsimp only [B_full]; rw [hn_c, hK']
    have hacur' : ∀ x, bp'.actCur x = bp.actCur x := fun x => by
      unfold actCur; rw [hac', hK']
    have hhyst' : ∀ x, bp'.BktHyst x = bp.BktHyst x := fun x => by
      ext t; unfold BktHyst; rw [hac', hK', hr', hq', hacur']
    have hsi' : bp'.StepInv b₀ 0 :=
      { core := hcv_c
        bktCount_le := fun b' hb' => by
          rw [hM'] at hb'; unfold bktCount; rw [hq', hK', hr', hms']
          exact hsi.bktCount_le b' hb'
        t_le := Nat.zero_le 16
        hyst_tick := fun hb0 => by rw [hhyst']; exact hsi.hyst_tick (hM' ▸ hb0)
        hyst_other := fun b' hb' hne => by rw [hhyst']; exact hsi.hyst_other b' (hM' ▸ hb') hne
        low_blk := fun P htag => by
          rw [hBf']; rw [hbt'] at htag
          by_cases pd : P = D
          · subst pd; exact hD_low
          · rw [set1_of_ne _ _ _ _ pd] at htag
            by_cases ps : P = S
            · subst ps; rw [set1_self] at htag; exact absurd rfl htag
            · rw [set1_of_ne _ _ _ _ ps] at htag; exact hsi.low_blk P htag
        low_swap := fun h1 => by rw [htsa'] at h1; exact absurd h1 (by decide) }
    refine ⟨hsi', hM', hK', hn_c, fun b' => by unfold bktCount; rw [hq', hK', hr'],
      fun hge2 hcond => ?_⟩
    unfold topDebt
    have hnot2 : ¬(bp.B_full < 2) := not_lt.mpr hge2
    rw [hBf', hK', htsa', ha1, ite_eq_right hnot2, ite_eq_right hnot2]; dsimp only
    rw [ite_eq_left rfl, ite_eq_right (by decide : (1 : ℕ) ≠ 0)]
    set P := bp.B_full - 2
    by_cases hs : S = P
    · rw [ite_eq_left hs]
      unfold blkWork
      rw [hbt', ← hs, set1_of_ne _ _ _ _ hSD, set1_self, ite_eq_left rfl]
      omega
    · rw [ite_eq_right hs]
      by_cases hd : D = P
      · rw [ite_eq_left hd]
        have hbw_DP : bp'.blkWork P = bp.blkWork bp.topSwapSrc := by
          unfold blkWork
          rw [hK', ← hd, show bp'.blkTag D = bp.blkTag S by rw [hbt', set1_self],
            show bp'.blkMeta1 D = bp.blkMeta1 S by rw [hbm1', set1_self]]; dsimp only
          rw [hacur', hac']
        rw [hbw_DP]; omega
      · rw [ite_eq_right hd]
        have htP : bp.blkTag P ≠ 0 := by
          rcases hcond with h | h | h
          · exact absurd h hs
          · exact absurd h hd
          · exact h
        rw [ite_eq_right htP]
        have hbw_P : bp'.blkWork P = bp.blkWork P := by
          unfold blkWork
          rw [hK',
            show bp'.blkTag P = bp.blkTag P by
              rw [hbt', set1_of_ne _ _ _ _ (Ne.symm hd), set1_of_ne _ _ _ _ (Ne.symm hs)],
            show bp'.blkMeta1 P = bp.blkMeta1 P by
              rw [hbm1', set1_of_ne _ _ _ _ (Ne.symm hd), set1_of_ne _ _ _ _ (Ne.symm hs)]]
          dsimp only; rw [hacur', hac']
        rw [hbw_P]; omega

/-- When every bucket is at rest (`StepInv b₀ 0`), `topCleanOne` preserves `StepInv b₀ 0`, emits at
most 1 swap `< nSide`, preserves all item lookups, and decreases `topDebt` to `topDebt - 1`! -/
theorem StepInv.topCleanOne_debt_spec {bp : BlockPoolState} {b₀ : ℕ}
    (hsi : bp.StepInv b₀ 0) :
    let (bp', osw) := bp.topCleanOne
    bp'.StepInv b₀ 0 ∧
    bp'.M = bp.M ∧
    bp'.K = bp.K ∧
    bp'.nSide = bp.nSide ∧
    (∀ b', bp'.bktCount b' = bp.bktCount b') ∧
    bp'.topDebt = bp.topDebt - 1 ∧
    (∀ sw, osw = some sw → sw.p₁ < bp.nSide ∧ sw.p₂ < bp.nSide) ∧
    (∀ {α : Type*} (arr : ℕ → α) (b' loc' : ℕ),
      b' < bp.M → loc' < bp.bktCount b' →
      applyOptSwap osw arr (bp'.toPhys b' loc') = arr (bp.toPhys b' loc')) := by
  have hv := hsi.core
  have hK := hv.K_pos
  have hh_all : ∀ b' < bp.M, bp.BktHyst b' 0 := fun b' hb' => by
    by_cases he : b' = b₀
    · subst he; exact hsi.hyst_tick hb'
    · exact hsi.hyst_other b' hb' he
  have hprom_q : ∀ b < bp.M, bp.actCode b = bp.K → bp.q b < bp.maxSlabs := fun b hb hcK =>
    hv.prom_q_lt_of_bktCount_le hb (hsi.bktCount_le b hb) (Or.inr hcK)
  have htc_core := hv.topCleanOne_spec hprom_q
  rcases htc : bp.topCleanOne with ⟨bp', osw⟩
  rw [htc] at htc_core
  obtain ⟨hcv', hn', hbc', hsw', harr'⟩ := htc_core
  unfold topCleanOne at htc
  by_cases hlt2 : bp.B_full < 2
  · rw [ite_eq_left hlt2] at htc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj htc
    have hd0 : bp.topDebt = 0 := by unfold topDebt; rw [ite_eq_left hlt2]
    exact ⟨hsi, rfl, rfl, rfl, fun _ => rfl, by rw [hd0], fun _ h => by simp at h,
      fun _ _ _ _ _ => rfl⟩
  · rw [ite_eq_right hlt2] at htc; dsimp only at htc
    have hge2 : 2 ≤ bp.B_full := by omega
    set P := bp.B_full - 2
    have hP_lt : P < bp.B_full := by dsimp only [P]; omega
    by_cases ha1 : bp.topSwapAct = 1
    · rw [ite_eq_left ha1] at htc
      by_cases hcond : bp.topSwapSrc = P ∨ bp.topSwapDst = P ∨ bp.blkTag P ≠ 0
      · rw [ite_eq_left hcond] at htc
        obtain ⟨hsi_s, hM_s, hK_s, hn_s, hbc_s, hdebt_s⟩ := hsi.topSwapStepOne_debt_and_inv ha1
        have hbp'_eq : bp' = (bp.topSwapStepOne).1 := by rw [htc]
        rw [← hbp'_eq] at hsi_s hM_s hK_s hn_s hbc_s hdebt_s
        exact ⟨hsi_s, hM_s, hK_s, hn', hbc', hdebt_s hge2 hcond, hsw', harr'⟩
      · rw [ite_eq_right hcond] at htc
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj htc
        push Not at hcond
        have hd0 : bp.topDebt = 0 := by
          unfold topDebt
          rw [ite_eq_right hlt2]; dsimp only
          rw [ite_eq_right (by omega), ite_eq_right hcond.1, ite_eq_right hcond.2.1,
            ite_eq_left hcond.2.2]
        exact ⟨hsi, rfl, rfl, rfl, fun _ => rfl, by rw [hd0], fun _ h => by simp at h,
          fun _ _ _ _ _ => rfl⟩
    · rw [ite_eq_right ha1] at htc
      have ha0 : bp.topSwapAct = 0 := by have := hv.topSwap_act_le; omega
      by_cases ht0 : bp.blkTag P = 0
      · rw [ite_eq_left ht0] at htc
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj htc
        have hd0 : bp.topDebt = 0 := by
          unfold topDebt; rw [ite_eq_right hlt2]; dsimp only
          rw [ite_eq_left ha0, (hv.blkWork_eq_zero_iff hP_lt).mpr ht0]
        exact ⟨hsi, rfl, rfl, rfl, fun _ => rfl, by rw [hd0], fun _ h => by simp at h,
          fun _ _ _ _ _ => rfl⟩
      · rw [ite_eq_right ht0] at htc
        by_cases ht2 : bp.blkTag P = 2
        · rw [ite_eq_left ht2] at htc
          obtain ⟨hb_P, hc_ne_P, hab_P⟩ := hv.act_bwd P hP_lt ht2
          set b_P := bp.blkMeta1 P
          have hh_bP := hh_all b_P hb_P
          obtain ⟨_, hact_bds⟩ := hh_bP.r_bounds hv.K_ge
            (hv.bkt_bounds b_P hb_P).2.2.2.1 (Nat.zero_le 16)
          obtain ⟨_, hcur_lt_r⟩ := hact_bds hc_ne_P
          have hcur_imp : bp.actCode b_P ≤ bp.K → bp.actCode b_P - 1 < bp.r b_P := fun hcK => by
            have hc_eq : bp.actCur b_P = bp.actCode b_P - 1 := by
              unfold actCur; rw [ite_eq_right hc_ne_P, ite_eq_left hcK]
            omega
          obtain ⟨hbw_step, hbw_pos, htag_imp, hM', hK', hms', hBf', htsa', htss', htsd',
            htsc', hh_oth⟩ := actStepOne_blkWork_and_hyst hv hb_P hc_ne_P hcur_imp
          have hh_bP' : (bp.actStepOne b_P).1.BktHyst b_P 0 :=
            actStepOne_bktHyst hv hb_P hc_ne_P (Nat.zero_le 16) hh_bP
          have hbp'_eq : bp' = (bp.actStepOne b_P).1 := by rw [htc]
          rw [← hbp'_eq] at hbw_step htag_imp hM' hK' hms' hBf' htsa' htss' htsd' htsc'
          rw [← hbp'_eq] at hh_oth hh_bP'
          have hh_all' : ∀ b' < bp'.M, bp'.BktHyst b' 0 := fun b' hb' => by
            rw [hM'] at hb'
            by_cases he : b' = b_P
            · subst he; exact hh_bP'
            · exact hh_oth b' he 0 (hh_all b' hb')
          have hsi' : bp'.StepInv b₀ 0 :=
            { core := hcv'
              bktCount_le := fun b' hb' => by
                rw [hM'] at hb'; rw [hbc' b', hms', hK']
                exact hsi.bktCount_le b' hb'
              t_le := Nat.zero_le 16
              hyst_tick := fun hb0 => hh_all' b₀ hb0
              hyst_other := fun b' hb' _ => hh_all' b' hb'
              low_blk := fun Q htag => by rw [hBf']; exact hsi.low_blk Q (htag_imp Q htag)
              low_swap := fun ha => by rw [hBf', htss', htsd']; exact hsi.low_swap (htsa' ▸ ha) }
          have hdebt' : bp'.topDebt = bp.topDebt - 1 := by
            unfold topDebt
            rw [hBf', hK', htsa', ha0, ite_eq_right hlt2, ite_eq_right hlt2]; dsimp only
            rw [ite_eq_left rfl, ite_eq_left rfl, hbw_step P hP_lt, ite_eq_left hab_P.symm]
          exact ⟨hsi', hM', hK', hn', hbc', hdebt', hsw', harr'⟩
        · rw [ite_eq_right ht2] at htc
          have ht1 : bp.blkTag P = 1 := by have := hv.blkTag_lt P hP_lt; omega
          have h3_ul : 3 ≤ bp.unresLen := hv.unresLen_ge_three_of_slab hP_lt ht1 hh_all
          rw [ite_eq_left h3_ul] at htc
          obtain ⟨_, hidx_lt, hD_add3⟩ := hv.findTopSwapIdx_spec h3_ul
          obtain ⟨hD_lt, hD_tag0, _⟩ := hv.unres_fwd bp.findTopSwapIdx hidx_lt
          set D := bp.unresStack bp.findTopSwapIdx
          have hPD : P ≠ D := by dsimp only [P, D] at hD_add3 ⊢; omega
          set bp_s : BlockPoolState :=
            { bp with topSwapAct := 1, topSwapSrc := P, topSwapDst := D, topSwapCur := 0 }
          have hsi_s : bp_s.StepInv b₀ 0 :=
            { core :=
                { hv with
                  topSwap_act_le := le_rfl
                  topSwap_valid := fun _ => ⟨hK, hP_lt, hD_lt, hD_tag0, hPD⟩ }
              bktCount_le := hsi.bktCount_le
              t_le := Nat.zero_le 16
              hyst_tick := hsi.hyst_tick
              hyst_other := hsi.hyst_other
              low_blk := hsi.low_blk
              low_swap := fun _ => by
                change P + 2 ≤ bp.B_full ∧ D + 2 ≤ bp.B_full
                exact ⟨by dsimp only [P]; omega, by omega⟩ }
          obtain ⟨hsi', hM', hK', hn_s, hbc_s, hdebt_s⟩ :=
            hsi_s.topSwapStepOne_debt_and_inv (rfl : bp_s.topSwapAct = 1)
          have hbp'_eq : bp' = (bp_s.topSwapStepOne).1 := by rw [htc]
          rw [← hbp'_eq] at hsi' hM' hK' hn_s hbc_s hdebt_s
          have hdebt_bps : bp_s.topDebt = bp.topDebt := by
            unfold topDebt
            rw [show bp_s.B_full = bp.B_full from rfl, show bp_s.K = bp.K from rfl,
              show bp_s.topSwapAct = 1 from rfl, show bp_s.topSwapSrc = P from rfl,
              show bp_s.topSwapCur = 0 from rfl, ha0]
            rw [ite_eq_right hlt2, ite_eq_right hlt2]; dsimp only
            rw [ite_eq_right (by decide : (1 : ℕ) ≠ 0), ite_eq_left rfl, ite_eq_left rfl]
            unfold blkWork; rw [ite_eq_right ht0, ite_eq_left ht1]; omega
          have hdebt' : bp'.topDebt = bp.topDebt - 1 := by
            rw [hdebt_s hge2 (Or.inl rfl), hdebt_bps]
          exact ⟨hsi', hM', hK', hn', hbc', hdebt', hsw', harr'⟩

/-- Run `t` `topCleanOne` steps on `(bp, arr)` synchronously. -/
def runTopCleanTicks {α : Type*} :
    ℕ → BlockPoolState × (ℕ → α) → BlockPoolState × (ℕ → α)
  | 0, st => st
  | t + 1, (bp, arr) =>
    let (bp₁, osw) := bp.topCleanOne
    runTopCleanTicks t (bp₁, applyOptSwap osw arr)

theorem StepInv.runTopCleanTicks_spec {α : Type*} {b₀ : ℕ} :
    ∀ t {bp : BlockPoolState}, bp.StepInv b₀ 0 → ∀ (arr : ℕ → α),
      let res := runTopCleanTicks t (bp, arr)
      res.1.StepInv b₀ 0 ∧
      res.1.M = bp.M ∧
      res.1.K = bp.K ∧
      res.1.nSide = bp.nSide ∧
      (∀ b', res.1.bktCount b' = bp.bktCount b') ∧
      res.1.topDebt = bp.topDebt - t ∧
      (∀ b' < bp.M, ∀ loc' < bp.bktCount b',
        res.2 (res.1.toPhys b' loc') = arr (bp.toPhys b' loc'))
  | 0, _, hsi, _ =>
    ⟨hsi, rfl, rfl, rfl, fun _ => rfl, (Nat.sub_zero _).symm, fun _ _ _ _ => rfl⟩
  | t + 1, bp, hsi, arr => by
    have hstep := hsi.topCleanOne_debt_spec
    rcases heq : bp.topCleanOne with ⟨bp₁, osw⟩
    rw [heq] at hstep
    obtain ⟨hsi₁, hM₁, hK₁, hn₁, hbc₁, hdebt₁, _, harr₁⟩ := hstep
    unfold runTopCleanTicks
    dsimp only; rw [heq]; dsimp only
    have ih := hsi₁.runTopCleanTicks_spec t (applyOptSwap osw arr)
    obtain ⟨hsi', hM', hK', hn', hbc', hdebt', harr'⟩ := ih
    refine ⟨hsi', hM'.trans hM₁, hK'.trans hK₁, hn'.trans hn₁,
      fun b' => (hbc' b').trans (hbc₁ b'), by rw [hdebt', hdebt₁]; omega,
      fun b' hb' loc' hloc' => ?_⟩
    exact (harr' b' (hM₁.symm ▸ hb') loc' ((hbc₁ b').symm ▸ hloc')).trans
      (harr₁ arr b' loc' hb' hloc')

theorem runBktTicks_zero {α : Type*} (b : ℕ) (st : BlockPoolState × (ℕ → α)) :
    runBktTicks b 0 st = st := by
  unfold runBktTicks; rfl

theorem runBktTicks_succ {α : Type*} (b t : ℕ) (bp : BlockPoolState) (arr : ℕ → α) :
    runBktTicks b (t + 1) (bp, arr) =
      let (bp₁, osw) := bp.bktTickOne b
      runBktTicks b t (bp₁, applyOptSwap osw arr) := by
  conv_lhs => unfold runBktTicks

theorem runTopCleanTicks_zero {α : Type*} (st : BlockPoolState × (ℕ → α)) :
    runTopCleanTicks 0 st = st := by
  unfold runTopCleanTicks; rfl

theorem runTopCleanTicks_succ {α : Type*} (t : ℕ) (bp : BlockPoolState) (arr : ℕ → α) :
    runTopCleanTicks (t + 1) (bp, arr) =
      let (bp₁, osw) := bp.topCleanOne
      runTopCleanTicks t (bp₁, applyOptSwap osw arr) := by
  conv_lhs => unfold runTopCleanTicks

attribute [local irreducible] runBktTicks runTopCleanTicks

/-! ## Section 5: `rawPostAppend`, `prepPopBktBack`, and `commitPopBktBack` -/

private theorem head_add_sub_mod {hd rk K : ℕ} (hhd : hd < 6 * K) (hrk : rk < 6 * K) :
    (hd + (rk + 6 * K - hd) % (6 * K)) % (6 * K) = rk := by
  by_cases hle : hd ≤ rk
  · have h1 : (rk + 6 * K - hd) % (6 * K) = rk - hd := by
      rw [show rk + 6 * K - hd = 6 * K + (rk - hd) by omega, Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1, show hd + (rk - hd) = rk by omega, Nat.mod_eq_of_lt hrk]
  · have h1 : (rk + 6 * K - hd) % (6 * K) = rk + 6 * K - hd :=
      Nat.mod_eq_of_lt (by omega)
    rw [h1, show hd + (rk + 6 * K - hd) = 6 * K + rk by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt hrk]

private def rawAppendCase1 (bp : BlockPoolState) (b : ℕ) : BlockPoolState :=
  let t_new := bp.blkMeta2 bp.B_full * bp.K + bp.rem
  let rk_new := (bp.head b + bp.r b) % (6 * bp.K)
  { bp with
    nSide := bp.nSide + 1
    r := set1 bp.r b (bp.r b + 1)
    tailRing := set2 bp.tailRing b rk_new t_new
    tailOwnerBkt := set1 bp.tailOwnerBkt t_new b
    tailOwnerRing := set1 bp.tailOwnerRing t_new rk_new }

private def rawAppendCase2 (bp : BlockPoolState) (b : ℕ) : BlockPoolState :=
  let bp_alloc := ((bp.rawAppendCase1 b).unresPush bp.B_full).allocTbFor (bp.B_full + 1)
  { bp_alloc with blkTag := set1 bp_alloc.blkTag (bp.B_full + 1) 0 }

/-- Assign newly appended physical slot `bp.nSide` to `(b, bp.bktCount b)` (`0` swaps), pushing
`bp.B_full` onto `unresStack` and allocating a fresh tail-block ID for `bp.B_full + 1` whenever
`bp.rem + 1 = bp.K`. -/
def rawPostAppend (bp : BlockPoolState) (b : ℕ) : BlockPoolState :=
  if bp.rem + 1 < bp.K then
    bp.rawAppendCase1 b
  else
    bp.rawAppendCase2 b

theorem rawPostAppend_apply (bp : BlockPoolState) (b : ℕ) :
    bp.rawPostAppend b =
      let t_new := bp.blkMeta2 bp.B_full * bp.K + bp.rem
      let rk_new := (bp.head b + bp.r b) % (6 * bp.K)
      let bp₁ : BlockPoolState :=
        { bp with
          nSide := bp.nSide + 1
          r := set1 bp.r b (bp.r b + 1)
          tailRing := set2 bp.tailRing b rk_new t_new
          tailOwnerBkt := set1 bp.tailOwnerBkt t_new b
          tailOwnerRing := set1 bp.tailOwnerRing t_new rk_new }
      if bp.rem + 1 < bp.K then
        bp₁
      else
        let bp_alloc := (bp₁.unresPush bp.B_full).allocTbFor (bp.B_full + 1)
        { bp_alloc with blkTag := set1 bp_alloc.blkTag (bp.B_full + 1) 0 } := by
  unfold rawPostAppend rawAppendCase1 rawAppendCase2
  split_ifs <;> rfl

theorem Balanced.rawPostAppend_spec {bp : BlockPoolState} (hbal : bp.Balanced)
    {b : ℕ} (hb : b < bp.M) (hcap : bp.bktCount b < bp.maxSlabs * bp.K) :
    let bp' := bp.rawPostAppend b
    bp'.StepInv b 16 ∧
    bp'.M = bp.M ∧
    bp'.K = bp.K ∧
    bp'.nSide = bp.nSide + 1 ∧
    bp'.bktCount b = bp.bktCount b + 1 ∧
    (∀ b' ≠ b, bp'.bktCount b' = bp.bktCount b') ∧
    bp'.topDebt ≤ 16 * bp'.rem ∧
    bp'.toPhys b (bp.bktCount b) = bp.nSide ∧
    (∀ b' < bp.M, ∀ loc' < bp.bktCount b', bp'.toPhys b' loc' = bp.toPhys b' loc') := by
  have hv := hbal.core
  have hK64 := hv.K_ge
  have hK := hv.K_pos
  have hM := hv.M_pos
  obtain ⟨hq_le, hr_lt, hhd_lt, hc_le, hcur_le_r⟩ := hv.bkt_bounds b hb
  have hh_b := hbal.hyst b hb
  have hr_add_lt : bp.r b + 1 < 6 * bp.K := by
    unfold BktHyst at hh_b
    have hcur_le := actCur_le_K hc_le
    split_ifs at hh_b <;> omega
  set P_top := bp.B_full
  set off_top := bp.rem
  have hoff_lt : off_top < bp.K := Nat.mod_lt bp.nSide hK
  have htag_top : bp.blkTag P_top = 0 := hv.blkTag_top
  obtain ⟨htb_top_lt, htb_top_eq⟩ := hv.tb_fwd P_top le_rfl (Or.inl htag_top)
  set t_new := bp.blkMeta2 P_top * bp.K + off_top
  set rk_new := (bp.head b + bp.r b) % (6 * bp.K)
  have ht_div : t_new / bp.K = bp.blkMeta2 P_top := by
    dsimp only [t_new]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hoff_lt, zero_add]
  have ht_mod : t_new % bp.K = off_top := by
    dsimp only [t_new]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff_lt]
  have ht_lt_8MK : t_new < 8 * bp.M * bp.K := by
    have hlt8 : bp.blkMeta2 P_top < 8 * bp.M := htb_top_lt.trans_le hv.tbHighWater_le_max
    have hle1 : (bp.blkMeta2 P_top + 1) * bp.K ≤ (8 * bp.M) * bp.K :=
      Nat.mul_le_mul_right bp.K hlt8
    rw [Nat.add_one_mul] at hle1; dsimp only [t_new]; omega
  have ht_not_live : ∀ b' < bp.M, ∀ k, bp.actCur b' ≤ k → k < bp.r b' →
      bp.tailRing b' ((bp.head b' + k) % (6 * bp.K)) ≠ t_new := fun b' hb' k hk_ge hk_lt hte => by
    have htf := hv.tail_fwd b' hb' k hk_ge hk_lt
    dsimp only at htf
    rw [hte, ht_div, ht_mod, htb_top_eq] at htf
    rcases htf.2.2.2.1 with ⟨_, hlt_or⟩ | ⟨hPlt, _, _⟩
    · rcases hlt_or with h1 | h2 <;> omega
    · omega
  have hrk_not_live : ∀ k, bp.actCur b ≤ k → k < bp.r b →
      (bp.head b + k) % (6 * bp.K) ≠ rk_new := fun k _ hk_lt hrke => by
    have h1 := (hv.bkt_bounds b hb).2.2.1
    -- `add_sub_head_mod`: `((hd + k) % 6K + 6K - hd) % 6K = k`
    have mod_inv : ∀ x < 6 * bp.K, ((bp.head b + x) % (6 * bp.K) + 6 * bp.K - bp.head b) %
        (6 * bp.K) = x := fun x hx => by
      by_cases hlt : bp.head b + x < 6 * bp.K
      · rw [Nat.mod_eq_of_lt hlt, show bp.head b + x + 6 * bp.K - bp.head b = 6 * bp.K + x by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt hx]
      · have hm : (bp.head b + x) % (6 * bp.K) = bp.head b + x - 6 * bp.K := by
          conv_lhs => rw [show bp.head b + x = 6 * bp.K + (bp.head b + x - 6 * bp.K) by omega]
          rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        rw [hm, show bp.head b + x - 6 * bp.K + 6 * bp.K - bp.head b = x by omega,
          Nat.mod_eq_of_lt hx]
    have e1 := mod_inv k (hk_lt.trans hr_lt)
    have e2 := mod_inv (bp.r b) hr_lt
    rw [hrke] at e1
    have := e1.symm.trans e2; omega
  have hh_b16 : ∀ (bp_x : BlockPoolState),
      bp_x.actCode b = bp.actCode b → bp_x.K = bp.K → bp_x.q b = bp.q b →
      bp_x.r b = bp.r b + 1 → bp_x.BktHyst b 16 := fun bp_x hc_x hk_x hq_x hr_x => by
    have hac_x : bp_x.actCur b = bp.actCur b := by unfold actCur; rw [hc_x, hk_x]
    unfold BktHyst at hh_b ⊢
    rw [hc_x, hk_x, hq_x, hr_x, hac_x]
    by_cases hc0 : bp.actCode b = 0
    · rw [ite_eq_left hc0] at hh_b ⊢
      refine ⟨by rcases hh_b.1 with h | ⟨h0, _⟩ <;> omega, fun hq0 => ?_⟩
      rcases hh_b.2 hq0 with h | ⟨h0, _⟩ <;> omega
    · rw [ite_eq_right hc0] at hh_b ⊢
      split_ifs at hh_b ⊢ <;> omega
  dsimp only
  unfold rawPostAppend
  by_cases hmid : bp.rem + 1 < bp.K
  · -- Case 1: `off_top + 1 < K`, so `B_full' = P_top` and `rem' = off_top + 1`!
    rw [ite_eq_left hmid]
    set bp' := bp.rawAppendCase1 b
    have hmid' : bp.rem + 1 < bp.K := hmid
    have hBf' : bp'.B_full = bp.B_full := by
      change (bp.nSide + 1) / bp.K = bp.B_full
      rw [← hv.nSide_eq, show bp.B_full * bp.K + bp.rem + 1 =
        (bp.rem + 1) + bp.B_full * bp.K by omega,
        Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hmid', zero_add]
    have hrem' : bp'.rem = bp.rem + 1 := by
      change (bp.nSide + 1) % bp.K = bp.rem + 1
      rw [← hv.nSide_eq, show bp.B_full * bp.K + bp.rem + 1 =
        (bp.rem + 1) + bp.B_full * bp.K by omega,
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hmid']
    have hac' : ∀ x, bp'.actCur x = bp.actCur x := fun _ => rfl
    have htp_new : bp'.toPhys b (bp.bktCount b) = bp.nSide := by
      unfold toPhys bktCount
      have hnot_slab : ¬(bp.q b * bp.K + bp.r b < bp.q b * bp.K) := by omega
      have hsub_r : bp.q b * bp.K + bp.r b - bp.q b * bp.K = bp.r b := Nat.add_sub_cancel_left _ _
      have hnot_cur : ¬(bp.r b < bp.actCur b) := not_lt.mpr hcur_le_r
      rw [show bp'.K = bp.K from rfl, show bp'.q = bp.q from rfl, hac',
        show bp'.head = bp.head from rfl, ite_eq_right hnot_slab, hsub_r, ite_eq_right hnot_cur]
      change bp'.physOfTail (set2 bp.tailRing b rk_new t_new b rk_new) = bp.nSide
      rw [set2_self]
      unfold physOfTail
      rw [show bp'.K = bp.K from rfl, show bp'.tbPhysBlk = bp.tbPhysBlk from rfl,
        show bp'.effBlk = bp.effBlk from rfl, ht_div, ht_mod, htb_top_eq,
        hv.effBlk_B_full, hv.nSide_eq]
    have htp_old : ∀ b' < bp.M, ∀ loc' < bp.bktCount b', bp'.toPhys b' loc' = bp.toPhys b' loc' :=
      fun b' hb' loc' hloc' => by
        unfold toPhys
        rw [show bp'.K = bp.K from rfl, show bp'.q = bp.q from rfl,
          show bp'.slabOf = bp.slabOf from rfl, hac', show bp'.actBlk = bp.actBlk from rfl,
          show bp'.head = bp.head from rfl, show bp'.effBlk = bp.effBlk from rfl,
          show bp'.physOfTail = bp.physOfTail from rfl]
        by_cases hslab : loc' < bp.q b' * bp.K
        · rw [ite_eq_left hslab, ite_eq_left hslab]
        · rw [ite_eq_right hslab, ite_eq_right hslab]
          set k := loc' - bp.q b' * bp.K
          have hk_lt_r : k < bp.r b' := by unfold bktCount at hloc'; omega
          by_cases hact : k < bp.actCur b'
          · rw [ite_eq_left hact, ite_eq_left hact]
          · rw [ite_eq_right hact, ite_eq_right hact]
            have hne2 : ¬(b' = b ∧ (bp.head b' + k) % (6 * bp.K) = rk_new) := by
              rintro ⟨rfl, hrke⟩
              exact hrk_not_live k (Nat.le_of_not_lt hact) hk_lt_r hrke
            exact congrArg bp.physOfTail (set2_of_ne _ _ _ _ _ _ hne2)
    have hcv' : bp'.CoreValid :=
      { M_pos := hv.M_pos
        K_ge := hv.K_ge
        bkt_bounds := fun b' hb' => by
          rw [hac']; dsimp only [bp', rawAppendCase1]
          by_cases hbe : b' = b
          · subst b'; rw [set1_self]
            exact ⟨hq_le, hr_add_lt, hhd_lt, hc_le, hcur_le_r.trans (Nat.le_succ _)⟩
          · rw [set1_of_ne _ _ _ _ hbe]; exact hv.bkt_bounds b' hb'
        blkTag_lt := fun P hP => hv.blkTag_lt P (hBf' ▸ hP)
        blkTag_top := by rw [hBf']; exact hv.blkTag_top
        unres_fwd := fun i hi => by rw [hBf']; exact hv.unres_fwd i hi
        unres_bwd := fun P hP h0 => hv.unres_bwd P (hBf' ▸ hP) h0
        slab_fwd := fun b' hb' v hvp => by rw [hBf']; exact hv.slab_fwd b' hb' v hvp
        slab_bwd := fun P hP h1 => hv.slab_bwd P (hBf' ▸ hP) h1
        act_fwd := fun b' hb' hne => by rw [hBf']; exact hv.act_fwd b' hb' hne
        act_bwd := fun P hP h2 => hv.act_bwd P (hBf' ▸ hP) h2
        tb_fwd := fun P hP hor => hv.tb_fwd P (hBf' ▸ hP) hor
        freeTb_valid := fun i hi => by
          obtain ⟨h1, h2⟩ := hv.freeTb_valid i hi
          exact ⟨h1, fun P hP hor => h2 P (hBf' ▸ hP) hor⟩
        freeTb_inj := hv.freeTb_inj
        tbHighWater_supply := by rw [hBf']; exact hv.tbHighWater_supply
        tbHighWater_le_max := hv.tbHighWater_le_max
        topSwap_act_le := hv.topSwap_act_le
        topSwap_valid := fun ha => by rw [hBf']; exact hv.topSwap_valid ha
        tail_fwd := fun b' hb' k hk_ge hk_lt => by
          dsimp only
          rw [hBf', hrem']
          rw [hac'] at hk_ge
          rw [show bp'.M = bp.M from rfl] at hb'
          rw [show bp'.r = set1 bp.r b (bp.r b + 1) from rfl] at hk_lt
          rw [show bp'.M = bp.M from rfl, show bp'.K = bp.K from rfl,
            show bp'.head = bp.head from rfl, show bp'.tbPhysBlk = bp.tbPhysBlk from rfl,
            show bp'.blkMeta2 = bp.blkMeta2 from rfl, show bp'.blkTag = bp.blkTag from rfl,
            show bp'.blkMeta1 = bp.blkMeta1 from rfl,
            show bp'.tailRing = set2 bp.tailRing b rk_new t_new from rfl,
            show bp'.tailOwnerBkt = set1 bp.tailOwnerBkt t_new b from rfl,
            show bp'.tailOwnerRing = set1 bp.tailOwnerRing t_new rk_new from rfl]
          by_cases hbe : b' = b
          · subst b'
            rw [set1_self] at hk_lt
            by_cases hke : k = bp.r b
            · subst hke
              rw [set2_self, ht_div, ht_mod, htb_top_eq, set1_self, set1_self]
              exact ⟨ht_lt_8MK, le_rfl, rfl, Or.inl ⟨htag_top, Or.inr (Nat.lt_succ_self _)⟩,
                rfl, rfl⟩
            · have hk_lt_old : k < bp.r b := by omega
              rw [set2_of_ne _ _ _ _ _ _ (fun h => hrk_not_live k hk_ge hk_lt_old h.2)]
              have htf := hv.tail_fwd b hb k hk_ge hk_lt_old
              dsimp only at htf
              have hne_t := ht_not_live b hb k hk_ge hk_lt_old
              rw [set1_of_ne _ _ _ _ hne_t, set1_of_ne _ _ _ _ hne_t]
              obtain ⟨ha, hbl, hcm, hkd, hob, hor⟩ := htf
              refine ⟨ha, hbl, hcm, ?_, hob, hor⟩
              rcases hkd with ⟨h0, hlt_or⟩ | h2
              · exact Or.inl ⟨h0, hlt_or.imp id (fun hr => Nat.lt_succ_of_lt hr)⟩
              · exact Or.inr h2
          · rw [set1_of_ne _ _ _ _ hbe] at hk_lt
            rw [set2_of_ne _ _ _ _ _ _ (fun h => hbe h.1)]
            have htf := hv.tail_fwd b' hb' k hk_ge hk_lt
            dsimp only at htf
            have hne_t := ht_not_live b' hb' k hk_ge hk_lt
            rw [set1_of_ne _ _ _ _ hne_t, set1_of_ne _ _ _ _ hne_t]
            obtain ⟨ha, hbl, hcm, hkd, hob, hor⟩ := htf
            refine ⟨ha, hbl, hcm, ?_, hob, hor⟩
            rcases hkd with ⟨h0, hlt_or⟩ | h2
            · exact Or.inl ⟨h0, hlt_or.imp id (fun hr => Nat.lt_succ_of_lt hr)⟩
            · exact Or.inr h2
        tail_bwd := fun P hP_le off hoff hlt hor => by
          dsimp only
          rw [hBf'] at hP_le; rw [hBf', hrem'] at hlt
          rw [show bp'.blkMeta2 P = bp.blkMeta2 P from rfl, show bp'.K = bp.K from rfl]
          set t := bp.blkMeta2 P * bp.K + off
          by_cases hte : t = t_new
          · rw [show bp'.tailOwnerBkt t = b by
            dsimp only [bp', rawAppendCase1]; rw [hte, set1_self],
              show bp'.tailOwnerRing t = rk_new by
            dsimp only [bp', rawAppendCase1]; rw [hte, set1_self],
              show bp'.M = bp.M from rfl, show bp'.head b = bp.head b from rfl, hac',
              show bp'.r b = bp.r b + 1 from set1_self _ _ _]
            have hrk_lt : rk_new < 6 * bp.K := Nat.mod_lt _ (by omega)
            have hk_re : (rk_new + 6 * bp.K - bp.head b) % (6 * bp.K) = bp.r b := by
              dsimp only [rk_new]
              by_cases hlt_h : bp.head b + bp.r b < 6 * bp.K
              · rw [Nat.mod_eq_of_lt hlt_h,
                  show bp.head b + bp.r b + 6 * bp.K - bp.head b = 6 * bp.K + bp.r b by omega,
                  Nat.add_mod_left, Nat.mod_eq_of_lt hr_lt]
              · have hm : (bp.head b + bp.r b) % (6 * bp.K) = bp.head b + bp.r b - 6 * bp.K := by
                  conv_lhs =>
                    rw [show bp.head b + bp.r b = 6 * bp.K + (bp.head b + bp.r b - 6 * bp.K)
                      by omega]
                  rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
                rw [hm,
                  show bp.head b + bp.r b - 6 * bp.K + 6 * bp.K - bp.head b = bp.r b by omega,
                  Nat.mod_eq_of_lt hr_lt]
            rw [hk_re, show bp'.tailRing b rk_new = t_new from set2_self _ _ _ _]
            exact ⟨hb, hrk_lt, hcur_le_r, Nat.lt_succ_self _, hte.symm⟩
          · have hlt_old : P < bp.B_full ∨ off < bp.rem := by
              rcases hlt with h1 | h2
              · exact Or.inl h1
              · by_cases hp_top : P = bp.B_full
                · subst hp_top
                  have hoff_ne : off ≠ off_top := fun hoe =>
                    hte (by dsimp only [t, t_new]; rw [hoe])
                  exact Or.inr (by dsimp only [off_top] at hoff_ne; omega)
                · exact Or.inl (by omega)
            obtain ⟨hbo, hrko, hk_ge, hk_lt, htr⟩ := hv.tail_bwd P hP_le off hoff hlt_old hor
            rw [show bp'.tailOwnerBkt t = bp.tailOwnerBkt t from set1_of_ne _ _ _ _ hte,
              show bp'.tailOwnerRing t = bp.tailOwnerRing t from set1_of_ne _ _ _ _ hte,
              show bp'.M = bp.M from rfl, show bp'.head = bp.head from rfl, hac']
            have hne2 : ¬(bp.tailOwnerBkt t = b ∧ bp.tailOwnerRing t = rk_new) := by
              rintro ⟨hbo_eq, hrke⟩
              have hmod_re := head_add_sub_mod (hv.bkt_bounds _ hbo).2.2.1 hrko
              rw [hbo_eq] at hk_ge hk_lt hmod_re
              exact hrk_not_live _ hk_ge hk_lt (hmod_re.trans hrke)
            rw [show bp'.tailRing (bp.tailOwnerBkt t) (bp.tailOwnerRing t) =
                bp.tailRing (bp.tailOwnerBkt t) (bp.tailOwnerRing t) from
                set2_of_ne _ _ _ _ _ _ hne2]
            refine ⟨hbo, hrko, hk_ge, ?_, htr⟩
            dsimp only [bp', rawAppendCase1]
            by_cases hbe : bp.tailOwnerBkt t = b
            · rw [hbe, set1_self]; rw [hbe] at hk_lt; exact Nat.lt_succ_of_lt hk_lt
            · rw [set1_of_ne _ _ _ _ hbe]; exact hk_lt }
    have hbc_b : bp'.bktCount b = bp.bktCount b + 1 := by
      unfold bktCount; dsimp only [bp', rawAppendCase1]; rw [set1_self]; omega
    have hbc_ne : ∀ b' ≠ b, bp'.bktCount b' = bp.bktCount b' := fun b' hne => by
      unfold bktCount; dsimp only [bp', rawAppendCase1]; rw [set1_of_ne _ _ _ _ hne]
    have hdebt_eq : bp'.topDebt = bp.topDebt := by
      unfold topDebt; rw [hBf']; rfl
    have hsi' : bp'.StepInv b 16 :=
      { core := hcv'
        bktCount_le := fun b' hb' => by
          by_cases hbe : b' = b
          · subst b'; rw [hbc_b]; exact hcap
          · rw [hbc_ne b' hbe]; exact hbal.bktCount_le b' hb'
        t_le := le_rfl
        hyst_tick := fun _ => hh_b16 bp' rfl rfl rfl (set1_self _ _ _)
        hyst_other := fun b' hb' hne => by
          have hh' := hbal.hyst b' hb'
          unfold BktHyst at hh' ⊢
          rw [hac', show bp'.actCode b' = bp.actCode b' from rfl, show bp'.K = bp.K from rfl,
            show bp'.q b' = bp.q b' from rfl,
            show bp'.r b' = bp.r b' from set1_of_ne _ _ _ _ hne]
          exact hh'
        low_blk := fun P htag => by rw [hBf']; exact hbal.low_blk P htag
        low_swap := fun ha => by rw [hBf']; exact hbal.low_swap ha }
    exact ⟨hsi', rfl, rfl, rfl, hbc_b, hbc_ne,
      by rw [hdebt_eq, hrem']; exact hbal.debt_le.trans (by omega), htp_new, htp_old⟩
  · -- Case 2: `off_top + 1 = bp.K`, so `B_full' = P_top + 1` and `rem' = 0`!
    rw [ite_eq_right hmid]
    have hoff_eq : off_top + 1 = bp.K := by dsimp only [off_top]; omega
    set bp' := bp.rawAppendCase2 b
    have hns_eq : bp.nSide + 1 = (P_top + 1) * bp.K := by
      have h := hv.nSide_eq
      dsimp only [P_top, off_top] at hoff_eq ⊢
      rw [Nat.add_one_mul]; omega
    have hBf_a : bp'.nSide = bp.nSide + 1 ∧ bp'.K = bp.K ∧ bp'.M = bp.M ∧
        bp'.maxSlabs = bp.maxSlabs ∧ bp'.q = bp.q ∧
        bp'.r = set1 bp.r b (bp.r b + 1) ∧ bp'.head = bp.head ∧
        bp'.actCode = bp.actCode ∧ bp'.actBlk = bp.actBlk ∧
        bp'.slabOf = bp.slabOf ∧
        bp'.tailRing = set2 bp.tailRing b rk_new t_new ∧
        bp'.blkMeta1 = set1 bp.blkMeta1 P_top bp.unresLen ∧
        bp'.unresLen = bp.unresLen + 1 ∧
        bp'.unresStack = set1 bp.unresStack bp.unresLen P_top ∧
        bp'.tailOwnerBkt = set1 bp.tailOwnerBkt t_new b ∧
        bp'.tailOwnerRing = set1 bp.tailOwnerRing t_new rk_new ∧
        bp'.topSwapAct = bp.topSwapAct ∧ bp'.topSwapSrc = bp.topSwapSrc ∧
        bp'.topSwapDst = bp.topSwapDst ∧ bp'.topSwapCur = bp.topSwapCur ∧
        bp'.freeTbStack = bp.freeTbStack ∧
        bp'.freeTbTop = (if 0 < bp.freeTbTop then bp.freeTbTop - 1 else bp.freeTbTop) ∧
        bp'.tbHighWater = (if 0 < bp.freeTbTop then bp.tbHighWater else bp.tbHighWater + 1) := by
      dsimp only [bp', rawAppendCase2, allocTbFor, unresPush, rawAppendCase1, P_top, t_new, rk_new]
      split_ifs <;>
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨hn_a, hK_a, hM_a, hms_a, hq_a, hr_a, hhd_a, hac_a, hab_a, hsl_a, htr_a,
      hbm1_a, hul_a, hus_a, htob_a, htor_a, htsa_a, htss_a, htsd_a, htsc_a,
      hfts_a, hftt_a, hthw_a⟩ := hBf_a
    have hBf' : bp'.B_full = P_top + 1 := by
      dsimp only [B_full]; rw [hn_a, hK_a, hns_eq, Nat.mul_div_cancel _ hK]
    have hrem' : bp'.rem = 0 := by
      dsimp only [rem]; rw [hn_a, hK_a, hns_eq, Nat.mul_mod_left]
    have hac' : ∀ x, bp'.actCur x = bp.actCur x := fun x => by
      unfold actCur; rw [show bp'.actCode = bp.actCode from hac_a, show bp'.K = bp.K from hK_a]
    set tb_next := if 0 < bp.freeTbTop then bp.freeTbStack (bp.freeTbTop - 1) else bp.tbHighWater
    have htb_not_used : ∀ P ≤ P_top, (bp.blkTag P = 0 ∨ bp.blkTag P = 2) →
        bp.blkMeta2 P ≠ tb_next := fun P hP hor => by
      dsimp only [tb_next]
      by_cases hft : 0 < bp.freeTbTop
      · rw [ite_eq_left hft]
        exact (hv.freeTb_valid (bp.freeTbTop - 1) (by omega)).2 P hP hor
      · rw [ite_eq_right hft]
        exact ne_of_lt (hv.tb_fwd P hP hor).1
    have hbm2_a : bp'.blkMeta2 = set1 bp.blkMeta2 (P_top + 1) tb_next ∧
        bp'.tbPhysBlk = set1 bp.tbPhysBlk tb_next (P_top + 1) ∧
        bp'.blkTag = set1 (set1 bp.blkTag P_top 0) (P_top + 1) 0 := by
      dsimp only [bp', rawAppendCase2, allocTbFor, unresPush, rawAppendCase1, P_top, tb_next]
      split_ifs <;> exact ⟨rfl, rfl, rfl⟩
    have hbt_eq_bp : set1 (set1 bp.blkTag P_top 0) (P_top + 1) 0 =
        set1 bp.blkTag (P_top + 1) 0 := by
      ext Q
      by_cases h1 : Q = P_top + 1
      · subst h1; simp
      · rw [set1_of_ne _ _ _ _ h1, set1_of_ne _ _ _ _ h1]
        by_cases h2 : Q = P_top
        · subst h2; rw [set1_self, htag_top]
        · rw [set1_of_ne _ _ _ _ h2]
    have hbt' : bp'.blkTag = set1 bp.blkTag (P_top + 1) 0 :=
      hbm2_a.2.2.trans hbt_eq_bp
    have heff' : ∀ E o, bp'.effBlk E o = bp.effBlk E o := fun E o => by
      unfold effBlk; rw [show bp'.topSwapAct = bp.topSwapAct from htsa_a,
        show bp'.topSwapCur = bp.topSwapCur from htsc_a,
        show bp'.topSwapSrc = bp.topSwapSrc from htss_a,
        show bp'.topSwapDst = bp.topSwapDst from htsd_a]
    have htp_new : bp'.toPhys b (bp.bktCount b) = bp.nSide := by
      unfold toPhys bktCount
      have hnot_slab : ¬(bp.q b * bp.K + bp.r b < bp.q b * bp.K) := by omega
      have hsub_r : bp.q b * bp.K + bp.r b - bp.q b * bp.K = bp.r b := Nat.add_sub_cancel_left _ _
      have hnot_cur : ¬(bp.r b < bp.actCur b) := not_lt.mpr hcur_le_r
      rw [show bp'.K = bp.K from hK_a, show bp'.q = bp.q from hq_a, hac',
        show bp'.head = bp.head from hhd_a, show bp'.tailRing = _ from htr_a,
        ite_eq_right hnot_slab, hsub_r, ite_eq_right hnot_cur, set2_self]
      unfold physOfTail
      have htb_ne : bp.blkMeta2 P_top ≠ tb_next :=
        htb_not_used P_top le_rfl (Or.inl htag_top)
      rw [show bp'.K = bp.K from hK_a, hbm2_a.2.1, ht_div, ht_mod,
        set1_of_ne _ _ _ _ htb_ne, htb_top_eq, heff', hv.effBlk_B_full, hv.nSide_eq]
    have htp_old : ∀ b' < bp.M, ∀ loc' < bp.bktCount b', bp'.toPhys b' loc' = bp.toPhys b' loc' :=
      fun b' hb' loc' hloc' => by
        unfold toPhys
        rw [show bp'.K = bp.K from hK_a, show bp'.q = bp.q from hq_a,
          show bp'.slabOf = bp.slabOf from hsl_a, hac',
          show bp'.actBlk = bp.actBlk from hab_a, show bp'.head = bp.head from hhd_a,
          show bp'.tailRing = _ from htr_a]
        simp only [heff']
        by_cases hslab : loc' < bp.q b' * bp.K
        · rw [ite_eq_left hslab, ite_eq_left hslab]
        · rw [ite_eq_right hslab, ite_eq_right hslab]
          set k := loc' - bp.q b' * bp.K
          have hk_lt_r : k < bp.r b' := by unfold bktCount at hloc'; omega
          by_cases hact : k < bp.actCur b'
          · rw [ite_eq_left hact, ite_eq_left hact]
          · rw [ite_eq_right hact, ite_eq_right hact]
            have hne2 : ¬(b' = b ∧ (bp.head b' + k) % (6 * bp.K) = rk_new) := by
              rintro ⟨rfl, hrke⟩
              exact hrk_not_live k (Nat.le_of_not_lt hact) hk_lt_r hrke
            rw [set2_of_ne _ _ _ _ _ _ hne2]
            unfold physOfTail
            have htf := hv.tail_fwd b' hb' k (Nat.le_of_not_lt hact) hk_lt_r
            dsimp only at htf
            obtain ⟨_, hP_le, hm2_eq, hkd, _, _⟩ := htf
            have hne_tb : bp.tailRing b' ((bp.head b' + k) % (6 * bp.K)) / bp.K ≠ tb_next := by
              rw [← hm2_eq]
              exact htb_not_used _ hP_le (hkd.imp And.left (fun h => h.2.1))
            rw [show bp'.K = bp.K from hK_a, hbm2_a.2.1, set1_of_ne _ _ _ _ hne_tb, heff']
    -- Upper bound `tbHighWater' ≤ 8 * bp.M`:
    have hthw_le : bp'.tbHighWater ≤ 8 * bp.M := by
      rw [hthw_a]
      by_cases hft : 0 < bp.freeTbTop
      · simp only [hft, ↓reduceIte]; exact hv.tbHighWater_le_max
      · simp only [hft, ↓reduceIte]
        have hft0 : bp.freeTbTop = 0 := by omega
        have hsup := hv.tbHighWater_supply
        obtain ⟨hcard_eq, _⟩ := hv.tail_block_card_lt
        rw [hft0, zero_add, hcard_eq] at hsup
        -- Also `unresLen + actBucketCount + 1 < 6 * M` because `sum r + 1 < 6 * M * K`!
        have hsum_r := hv.sum_r_eq_tail_supply
        have hsum_lt : (∑ x ∈ Finset.range bp.M, bp.r x) + 1 ≤ bp.M * (6 * bp.K) := by
          have hlt1 : ∑ x ∈ Finset.range bp.M, bp.r x < ∑ _x ∈ Finset.range bp.M, (6 * bp.K) :=
            Finset.sum_lt_sum_of_nonempty ⟨0, mem_range.mpr (by omega)⟩
              fun x hx => (hv.bkt_bounds x (mem_range.mp hx)).2.1
          rw [Finset.sum_const, card_range, smul_eq_mul] at hlt1; omega
        rw [hsum_r] at hsum_lt
        dsimp only [off_top] at hoff_eq
        have hlt_6M : bp.unresLen + bp.actBucketCount + 1 ≤ 6 * bp.M := by
          by_contra hgt
          have hmul : (6 * bp.M + 1) * bp.K ≤ (bp.unresLen + bp.actBucketCount + 1) * bp.K :=
            Nat.mul_le_mul_right bp.K (by omega)
          rw [Nat.add_one_mul, Nat.add_one_mul] at hmul; linarith
        omega
    have hcv' : bp'.CoreValid :=
      { M_pos := hM_a ▸ hv.M_pos
        K_ge := hK_a ▸ hv.K_ge
        bkt_bounds := fun b' hb' => by
          rw [hM_a] at hb'; rw [hac', hms_a, hK_a, hq_a, hr_a, hhd_a, hac_a]
          by_cases hbe : b' = b
          · subst b'; rw [set1_self]
            exact ⟨hq_le, hr_add_lt, hhd_lt, hc_le, hcur_le_r.trans (Nat.le_succ _)⟩
          · rw [set1_of_ne _ _ _ _ hbe]; exact hv.bkt_bounds b' hb'
        blkTag_lt := fun P hP => by
          rw [hBf'] at hP; rw [hbt']
          rw [set1_of_ne _ _ _ _ (ne_of_lt hP)]
          by_cases hp : P = P_top
          · subst hp; rw [htag_top]; decide
          · exact hv.blkTag_lt P (by omega)
        blkTag_top := by rw [hBf', hbt', set1_self]
        unres_fwd := fun i hi => by
          rw [show bp'.unresLen = bp.unresLen + 1 from hul_a] at hi
          rw [hBf', show bp'.unresStack = set1 bp.unresStack bp.unresLen P_top from hus_a,
            hbt', show bp'.blkMeta1 = set1 bp.blkMeta1 P_top bp.unresLen from hbm1_a]
          by_cases hie : i = bp.unresLen
          · subst hie
            rw [set1_self, set1_of_ne _ _ _ _ (by omega), set1_self]
            exact ⟨Nat.lt_succ_self _, htag_top, rfl⟩
          · obtain ⟨h1, h2, h3⟩ := hv.unres_fwd i (by omega)
            rw [set1_of_ne _ _ _ _ hie, set1_of_ne _ _ _ _ (by omega),
              set1_of_ne _ _ _ _ (ne_of_lt h1)]
            exact ⟨Nat.lt_succ_of_lt h1, h2, h3⟩
        unres_bwd := fun P hP h0 => by
          rw [hBf'] at hP; rw [hbt', set1_of_ne _ _ _ _ (ne_of_lt hP)] at h0
          rw [show bp'.unresLen = bp.unresLen + 1 from hul_a,
            show bp'.unresStack = set1 bp.unresStack bp.unresLen P_top from hus_a,
            show bp'.blkMeta1 = set1 bp.blkMeta1 P_top bp.unresLen from hbm1_a]
          by_cases hp : P = P_top
          · subst hp; rw [set1_self, set1_self]; exact ⟨Nat.lt_succ_self _, rfl⟩
          · obtain ⟨h1, h2⟩ := hv.unres_bwd P (by omega) h0
            rw [set1_of_ne _ _ _ _ hp, set1_of_ne _ _ _ _ (ne_of_lt h1)]
            exact ⟨Nat.lt_succ_of_lt h1, h2⟩
        slab_fwd := fun b' hb' v hvp => by
          rw [hM_a] at hb'; rw [hq_a] at hvp
          obtain ⟨h1, h2, h3, h4⟩ := hv.slab_fwd b' hb' v hvp
          rw [hBf', hsl_a, hbt', hbm1_a, hbm2_a.1,
            set1_of_ne _ _ _ _ (by omega), set1_of_ne _ _ _ _ (ne_of_lt h1),
            set1_of_ne _ _ _ _ (by omega)]
          exact ⟨Nat.lt_succ_of_lt h1, h2, h3, h4⟩
        slab_bwd := fun P hP h1 => by
          rw [hBf'] at hP; rw [hbt', set1_of_ne _ _ _ _ (ne_of_lt hP)] at h1
          have hp : P ≠ P_top := fun he => by rw [he, htag_top] at h1; exact absurd h1 (by decide)
          rw [hM_a, hq_a, hsl_a, hbm1_a, hbm2_a.1, set1_of_ne _ _ _ _ hp,
            set1_of_ne _ _ _ _ (ne_of_lt hP)]
          exact hv.slab_bwd P (by omega) h1
        act_fwd := fun b' hb' hne => by
          rw [hM_a] at hb'; rw [hac_a] at hne
          obtain ⟨h1, h2, h3⟩ := hv.act_fwd b' hb' hne
          rw [hBf', hab_a, hbt', hbm1_a, set1_of_ne _ _ _ _ (by omega),
            set1_of_ne _ _ _ _ (ne_of_lt h1)]
          exact ⟨Nat.lt_succ_of_lt h1, h2, h3⟩
        act_bwd := fun P hP h2 => by
          rw [hBf'] at hP; rw [hbt', set1_of_ne _ _ _ _ (ne_of_lt hP)] at h2
          have hp : P ≠ P_top := fun he => by rw [he, htag_top] at h2; exact absurd h2 (by decide)
          rw [hM_a, hac_a, hab_a, hbm1_a, set1_of_ne _ _ _ _ hp]
          exact hv.act_bwd P (by omega) h2
        tb_fwd := fun P hP hor => by
          rw [hBf'] at hP; rw [hbt'] at hor; rw [hbm2_a.1, hbm2_a.2.1, hthw_a]
          by_cases hp1 : P = P_top + 1
          · subst hp1; rw [set1_self, set1_self]
            refine ⟨?_, rfl⟩
            dsimp only [tb_next]
            by_cases hft : 0 < bp.freeTbTop
            · simp only [hft, ↓reduceIte]
              exact (hv.freeTb_valid (bp.freeTbTop - 1) (by omega)).1
            · simp only [hft, ↓reduceIte]; omega
          · have hP_le : P ≤ P_top := by omega
            rw [set1_of_ne _ _ _ _ hp1] at hor ⊢
            obtain ⟨h1, h2⟩ := hv.tb_fwd P hP_le hor
            rw [set1_of_ne _ _ _ _ (htb_not_used P hP_le hor)]
            refine ⟨?_, h2⟩
            by_cases hft : 0 < bp.freeTbTop
            · simp only [hft, ↓reduceIte]; exact h1
            · simp only [hft, ↓reduceIte]; exact Nat.lt_succ_of_lt h1
        freeTb_valid := fun i hi => by
          rw [hBf', hbt', hbm2_a.1, hthw_a, hfts_a]
          rw [hftt_a] at hi
          dsimp only [tb_next]
          by_cases hft : 0 < bp.freeTbTop
          · simp only [hft, ↓reduceIte] at hi ⊢
            obtain ⟨h1, h2⟩ := hv.freeTb_valid i (by omega)
            refine ⟨h1, fun P hP hor => ?_⟩
            by_cases hp1 : P = P_top + 1
            · subst hp1; rw [set1_self]
              intro heq
              exact absurd (hv.freeTb_inj (bp.freeTbTop - 1) (by omega) i (by omega) heq)
                (ne_of_gt hi)
            · rw [set1_of_ne _ _ _ _ hp1] at hor ⊢
              exact h2 P (by omega) hor
          · simp only [hft, ↓reduceIte] at hi; omega
        freeTb_inj := fun i hi j hj heq => by
          rw [hftt_a] at hi hj; rw [hfts_a] at heq
          by_cases hft : 0 < bp.freeTbTop
          · simp only [hft, ↓reduceIte] at hi hj
            exact hv.freeTb_inj i (by omega) j (by omega) heq
          · simp only [hft, ↓reduceIte] at hi; omega
        tbHighWater_supply := by
          rw [hBf', hbt', hthw_a, hftt_a]
          have hcard_split : ((Finset.range (P_top + 1 + 1)).filter
              (fun P => set1 bp.blkTag (P_top + 1) 0 P = 0 ∨
                set1 bp.blkTag (P_top + 1) 0 P = 2)).card =
              ((Finset.range (P_top + 1)).filter
                (fun P => bp.blkTag P = 0 ∨ bp.blkTag P = 2)).card + 1 := by
            rw [Finset.range_add_one, Finset.filter_insert]
            simp only [set1_self, true_or, ↓reduceIte]
            have hnot : P_top + 1 ∉ (Finset.range (P_top + 1)).filter
                (fun P => set1 bp.blkTag (P_top + 1) 0 P = 0 ∨
                  set1 bp.blkTag (P_top + 1) 0 P = 2) := by simp
            rw [Finset.card_insert_of_notMem hnot]
            refine congrArg (· + 1) (congrArg Finset.card ?_)
            ext P; simp only [mem_filter, mem_range]
            refine and_congr_right fun hlt => ?_
            rw [set1_of_ne _ _ _ _ (ne_of_lt hlt)]
          rw [hcard_split]
          have hsup := hv.tbHighWater_supply
          by_cases hft : 0 < bp.freeTbTop
          · simp only [hft, ↓reduceIte]; dsimp only [P_top]; omega
          · simp only [hft, ↓reduceIte]; dsimp only [P_top]; omega
        tbHighWater_le_max := hM_a ▸ hthw_le
        topSwap_act_le := htsa_a ▸ hv.topSwap_act_le
        topSwap_valid := fun ha => by
          rw [htsa_a] at ha
          obtain ⟨h1, h2, h3, h4, h5⟩ := hv.topSwap_valid ha
          rw [hBf', hK_a, htsc_a, htss_a, htsd_a, hbt',
            set1_of_ne _ _ _ _ (by dsimp only [P_top]; omega)]
          exact ⟨h1, Nat.lt_succ_of_lt h2, Nat.lt_succ_of_lt h3, h4, h5⟩
        tail_fwd := fun b' hb' k hk_ge hk_lt => by
          dsimp only
          rw [hBf', hrem']
          rw [hac'] at hk_ge
          rw [hM_a] at hb'; rw [hr_a] at hk_lt
          rw [hM_a, hK_a, hhd_a, htr_a, hbm2_a.2.1, hbm2_a.1, hbt', hbm1_a, htob_a, htor_a]
          by_cases hbe : b' = b
          · subst b'
            rw [set1_self] at hk_lt
            by_cases hke : k = bp.r b
            · subst hke
              have htb_ne : bp.blkMeta2 P_top ≠ tb_next :=
                htb_not_used P_top le_rfl (Or.inl htag_top)
              rw [set2_self, ht_div, ht_mod, set1_of_ne _ _ _ _ htb_ne, htb_top_eq,
                set1_of_ne _ _ _ _ (by omega), set1_of_ne _ _ _ _ (by omega),
                set1_self, set1_self, set1_self]
              exact ⟨ht_lt_8MK, Nat.le_succ _, rfl,
                Or.inl ⟨htag_top, Or.inl (Nat.lt_succ_self _)⟩, rfl, rfl⟩
            · have hk_lt_old : k < bp.r b := by omega
              rw [set2_of_ne _ _ _ _ _ _ (fun h => hrk_not_live k hk_ge hk_lt_old h.2)]
              have htf := hv.tail_fwd b hb k hk_ge hk_lt_old
              dsimp only at htf
              have hne_t := ht_not_live b hb k hk_ge hk_lt_old
              rw [set1_of_ne _ _ _ _ hne_t, set1_of_ne _ _ _ _ hne_t]
              obtain ⟨ha, hbl, hcm, hkd, hob, hor⟩ := htf
              have hne_tb : bp.tailRing b ((bp.head b + k) % (6 * bp.K)) / bp.K ≠ tb_next := by
                rw [← hcm]; exact htb_not_used _ hbl (hkd.imp And.left (fun h => h.2.1))
              rw [set1_of_ne _ _ _ _ hne_tb]
              set Pt := bp.tbPhysBlk (bp.tailRing b ((bp.head b + k) % (6 * bp.K)) / bp.K)
              have hPt_ne1 : Pt ≠ P_top + 1 := by dsimp only [P_top] at hbl ⊢; omega
              rw [set1_of_ne _ _ _ _ hPt_ne1, set1_of_ne _ _ _ _ hPt_ne1]
              refine ⟨ha, Nat.le_succ_of_le hbl, hcm, ?_, hob, hor⟩
              rcases hkd with ⟨h0, _⟩ | ⟨hPlt, h2, hge_m⟩
              · exact Or.inl ⟨h0, Or.inl (by omega)⟩
              · have hPt_ne0 : Pt ≠ P_top := ne_of_lt hPlt
                rw [set1_of_ne _ _ _ _ hPt_ne0, hac']
                exact Or.inr ⟨Nat.lt_succ_of_lt hPlt, h2, hge_m⟩
          · rw [set1_of_ne _ _ _ _ hbe] at hk_lt
            rw [set2_of_ne _ _ _ _ _ _ (fun h => hbe h.1)]
            have htf := hv.tail_fwd b' hb' k hk_ge hk_lt
            dsimp only at htf
            have hne_t := ht_not_live b' hb' k hk_ge hk_lt
            rw [set1_of_ne _ _ _ _ hne_t, set1_of_ne _ _ _ _ hne_t]
            obtain ⟨ha, hbl, hcm, hkd, hob, hor⟩ := htf
            have hne_tb : bp.tailRing b' ((bp.head b' + k) % (6 * bp.K)) / bp.K ≠ tb_next := by
              rw [← hcm]; exact htb_not_used _ hbl (hkd.imp And.left (fun h => h.2.1))
            rw [set1_of_ne _ _ _ _ hne_tb]
            set Pt := bp.tbPhysBlk (bp.tailRing b' ((bp.head b' + k) % (6 * bp.K)) / bp.K)
            have hPt_ne1 : Pt ≠ P_top + 1 := by dsimp only [P_top] at hbl ⊢; omega
            rw [set1_of_ne _ _ _ _ hPt_ne1, set1_of_ne _ _ _ _ hPt_ne1]
            refine ⟨ha, Nat.le_succ_of_le hbl, hcm, ?_, hob, hor⟩
            rcases hkd with ⟨h0, _⟩ | ⟨hPlt, h2, hge_m⟩
            · exact Or.inl ⟨h0, Or.inl (by omega)⟩
            · have hPt_ne0 : Pt ≠ P_top := ne_of_lt hPlt
              rw [set1_of_ne _ _ _ _ hPt_ne0, hac']
              exact Or.inr ⟨Nat.lt_succ_of_lt hPlt, h2, hge_m⟩
        tail_bwd := fun P hP_le off hoff hlt hor => by
          dsimp only
          rw [hBf'] at hP_le; rw [hBf', hrem'] at hlt
          rw [hK_a] at hoff
          have hP_lt_next : P < P_top + 1 := by
            rcases hlt with h1 | h2
            · exact h1
            · omega
          have hp_ne1 : P ≠ P_top + 1 := ne_of_lt hP_lt_next
          have hm2_P : bp'.blkMeta2 P = bp.blkMeta2 P := by
            rw [hbm2_a.1, set1_of_ne _ _ _ _ hp_ne1]
          rw [hm2_P, hK_a]
          set t := bp.blkMeta2 P * bp.K + off
          by_cases hte : t = t_new
          · rw [show bp'.tailOwnerBkt t = b by rw [htob_a, hte, set1_self],
              show bp'.tailOwnerRing t = rk_new by rw [htor_a, hte, set1_self],
              hM_a, hhd_a, hac', show bp'.r b = bp.r b + 1 by rw [hr_a, set1_self]]
            have hrk_lt : rk_new < 6 * bp.K := Nat.mod_lt _ (by omega)
            have hk_re : (rk_new + 6 * bp.K - bp.head b) % (6 * bp.K) = bp.r b := by
              dsimp only [rk_new]
              by_cases hlt_h : bp.head b + bp.r b < 6 * bp.K
              · rw [Nat.mod_eq_of_lt hlt_h,
                  show bp.head b + bp.r b + 6 * bp.K - bp.head b = 6 * bp.K + bp.r b by omega,
                  Nat.add_mod_left, Nat.mod_eq_of_lt hr_lt]
              · have hm : (bp.head b + bp.r b) % (6 * bp.K) = bp.head b + bp.r b - 6 * bp.K := by
                  conv_lhs =>
                    rw [show bp.head b + bp.r b = 6 * bp.K + (bp.head b + bp.r b - 6 * bp.K)
                      by omega]
                  rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
                rw [hm,
                  show bp.head b + bp.r b - 6 * bp.K + 6 * bp.K - bp.head b = bp.r b by omega,
                  Nat.mod_eq_of_lt hr_lt]
            rw [hk_re, show bp'.tailRing b rk_new = t_new by rw [htr_a, set2_self]]
            exact ⟨hb, hrk_lt, hcur_le_r, Nat.lt_succ_self _, hte.symm⟩
          · have hP_le_old : P ≤ bp.B_full := by omega
            have hlt_old : P < bp.B_full ∨ off < bp.rem := by
              by_cases hp_top : P = P_top
              · subst hp_top
                have hoff_ne : off ≠ off_top := fun hoe => hte (by dsimp only [t, t_new]; rw [hoe])
                exact Or.inr (by dsimp only [off_top] at hoff_ne hoff_eq; omega)
              · exact Or.inl (by dsimp only [P_top] at hp_top; omega)
            have hor_old : bp.blkTag P = 0 ∨
                (bp.blkTag P = 2 ∧ bp.actCur (bp.blkMeta1 P) ≤ off) := by
              rw [hbt', set1_of_ne _ _ _ _ hp_ne1] at hor
              rcases hor with h0 | ⟨h2, hge⟩
              · exact Or.inl h0
              · have hp_ne0 : P ≠ P_top := fun he => by
                  rw [he, htag_top] at h2; exact absurd h2 (by decide)
                rw [hbm1_a, set1_of_ne _ _ _ _ hp_ne0, hac'] at hge
                exact Or.inr ⟨h2, hge⟩
            obtain ⟨hbo, hrko, hk_ge, hk_lt, htr⟩ :=
              hv.tail_bwd P hP_le_old off hoff hlt_old hor_old
            rw [show bp'.tailOwnerBkt t = bp.tailOwnerBkt t by rw [htob_a, set1_of_ne _ _ _ _ hte],
              show bp'.tailOwnerRing t = bp.tailOwnerRing t by rw [htor_a, set1_of_ne _ _ _ _ hte],
              hM_a, hhd_a, hac']
            have hne2 : ¬(bp.tailOwnerBkt t = b ∧ bp.tailOwnerRing t = rk_new) := by
              rintro ⟨hbo_eq, hrke⟩
              have hmod_re := head_add_sub_mod (hv.bkt_bounds _ hbo).2.2.1 hrko
              rw [hbo_eq] at hk_ge hk_lt hmod_re
              exact hrk_not_live _ hk_ge hk_lt (hmod_re.trans hrke)
            rw [show bp'.tailRing (bp.tailOwnerBkt t) (bp.tailOwnerRing t) =
                bp.tailRing (bp.tailOwnerBkt t) (bp.tailOwnerRing t) by
                  rw [htr_a, set2_of_ne _ _ _ _ _ _ hne2], hr_a]
            refine ⟨hbo, hrko, hk_ge, ?_, htr⟩
            by_cases hbe : bp.tailOwnerBkt t = b
            · rw [hbe, set1_self]; rw [hbe] at hk_lt; exact Nat.lt_succ_of_lt hk_lt
            · rw [set1_of_ne _ _ _ _ hbe]; exact hk_lt }
    have hbc_b : bp'.bktCount b = bp.bktCount b + 1 := by
      unfold bktCount; rw [hq_a, hK_a, hr_a, set1_self]; omega
    have hbc_ne : ∀ b' ≠ b, bp'.bktCount b' = bp.bktCount b' := fun b' hne => by
      unfold bktCount; rw [hq_a, hK_a, hr_a, set1_of_ne _ _ _ _ hne]
    have hdebt0 : bp'.topDebt = 0 := by
      rw [hcv'.topDebt_eq_zero_iff, hBf']
      intro hge2
      have hne_next : P_top + 1 - 2 ≠ P_top + 1 := by omega
      have ht_pm1 : bp.blkTag (P_top + 1 - 2) = 0 := by
        by_contra hne0
        have := hbal.low_blk _ hne0
        dsimp only [P_top] at this ⊢; omega
      refine ⟨by rw [hbt', set1_of_ne _ _ _ _ hne_next, ht_pm1], fun ha1 => ?_⟩
      rw [htsa_a] at ha1
      obtain ⟨hs2, hd2⟩ := hbal.low_swap ha1
      rw [htss_a, htsd_a]
      dsimp only [P_top] at hs2 hd2 ⊢
      exact ⟨by omega, by omega⟩
    have hsi' : bp'.StepInv b 16 :=
      { core := hcv'
        bktCount_le := fun b' hb' => by
          rw [hM_a] at hb'; rw [hms_a, hK_a]
          by_cases hbe : b' = b
          · subst b'; rw [hbc_b]; exact hcap
          · rw [hbc_ne b' hbe]; exact hbal.bktCount_le b' hb'
        t_le := le_rfl
        hyst_tick := fun _ => hh_b16 bp' (congrFun hac_a b) hK_a (congrFun hq_a b)
          (by rw [hr_a, set1_self])
        hyst_other := fun b' hb' hne => by
          rw [hM_a] at hb'
          have hh' := hbal.hyst b' hb'
          unfold BktHyst at hh' ⊢
          rw [hac', hac_a, hK_a, hq_a, hr_a, set1_of_ne _ _ _ _ hne]
          exact hh'
        low_blk := fun P htag => by
          rw [hBf']; rw [hbt'] at htag
          by_cases hp1 : P = P_top + 1
          · subst hp1; rw [set1_self] at htag; exact absurd rfl htag
          · rw [set1_of_ne _ _ _ _ hp1] at htag
            have := hbal.low_blk P htag; dsimp only [P_top]; omega
        low_swap := fun ha => by
          rw [htsa_a] at ha
          obtain ⟨hs2, hd2⟩ := hbal.low_swap ha
          rw [hBf', htss_a, htsd_a]; dsimp only [P_top]; exact ⟨by omega, by omega⟩ }
    exact ⟨hsi', hM_a, hK_a, hn_a, hbc_b, hbc_ne,
      by rw [hdebt0]; exact Nat.zero_le _, htp_new, htp_old⟩

/-- End-to-end `Balanced` theorem for `rawPostAppend` followed by `16` `bktTickOne` steps. -/
theorem Balanced.postAppend_runBktTicks_balanced {α : Type*} {bp : BlockPoolState}
    (hbal : bp.Balanced) {b : ℕ} (hb : b < bp.M) (hcap : bp.bktCount b < bp.maxSlabs * bp.K)
    (arr : ℕ → α) :
    let res := runBktTicks b 16 (bp.rawPostAppend b, arr)
    res.1.Balanced ∧
    res.1.nSide = bp.nSide + 1 ∧
    res.1.bktCount b = bp.bktCount b + 1 ∧
    (∀ b' ≠ b, res.1.bktCount b' = bp.bktCount b') ∧
    res.2 (res.1.toPhys b (bp.bktCount b)) = arr bp.nSide ∧
    (∀ b' < bp.M, ∀ loc' < bp.bktCount b',
      res.2 (res.1.toPhys b' loc') = arr (bp.toPhys b' loc')) := by
  obtain ⟨hsi0, hM0, hK0, hn0, hbc_b0, hbc_ne0, hdebt0, htp_new0, htp_old0⟩ :=
    hbal.rawPostAppend_spec hb hcap
  have hrun_spec := hsi0.runBktTicks_spec 16 (hM0.symm ▸ hb) arr
  set res := runBktTicks b 16 (bp.rawPostAppend b, arr)
  set bp' := res.1
  set arr' := res.2
  obtain ⟨hsi', hM', hK', hn', hbc', hdebt', harr'⟩ := hrun_spec
  have hrem_eq : bp'.rem = (bp.rawPostAppend b).rem := by
    dsimp only [rem]; rw [hn', hK']
  have hbal' : bp'.Balanced :=
    { core := hsi'.core
      bktCount_le := hsi'.bktCount_le
      hyst := fun b' hb' => by
        by_cases hbe : b' = b
        · subst b'; exact hsi'.hyst_tick hb'
        · exact hsi'.hyst_other b' hb' hbe
      low_blk := hsi'.low_blk
      low_swap := hsi'.low_swap
      debt_le := by rw [hrem_eq]; exact hdebt'.trans hdebt0 }
  refine ⟨hbal', hn'.trans hn0, (hbc' b).trans hbc_b0,
    fun b' hne => (hbc' b').trans (hbc_ne0 b' hne), ?_, fun b' hb' loc' hloc' => ?_⟩
  · have hlt : bp.bktCount b < (bp.rawPostAppend b).bktCount b := by rw [hbc_b0]; omega
    exact (harr' b (hM0.symm ▸ hb) (bp.bktCount b) hlt).trans (congrArg arr htp_new0)
  · have hlt : loc' < (bp.rawPostAppend b).bktCount b' := by
      by_cases hbe : b' = b
      · subst b'; rw [hbc_b0]; omega
      · rw [hbc_ne0 b' hbe]; exact hloc'
    exact (harr' b' (hM0.symm ▸ hb') loc' hlt).trans (congrArg arr (htp_old0 b' hb' loc' hloc'))

private def popEndCoord (bp : BlockPoolState) (b : ℕ) : ℕ :=
  bp.tailRing b ((bp.head b + (bp.r b - 1)) % (6 * bp.K))

private def popTopCoord (bp : BlockPoolState) : ℕ :=
  if 0 < bp.rem then
    bp.blkMeta2 bp.B_full * bp.K + (bp.rem - 1)
  else
    bp.blkMeta2 (bp.B_full - 1) * bp.K + (bp.K - 1)

/-- Pre-pop tail swap (`≤ 1` physical swap `< bp.nSide`): moves `(b, bp.bktCount b - 1)`'s tail
coordinate to the physical top slot `bp.nSide - 1` without changing any `(b', loc')` index. -/
def prepPopBktBack (bp : BlockPoolState) (b : ℕ) : BlockPoolState × Option PhysSwap :=
  bp.swapTailCoords (bp.popEndCoord b) bp.popTopCoord

theorem prepPopBktBack_apply (bp : BlockPoolState) (b : ℕ) :
    bp.prepPopBktBack b =
      bp.swapTailCoords
        (bp.tailRing b ((bp.head b + (bp.r b - 1)) % (6 * bp.K)))
        (if 0 < bp.rem then bp.blkMeta2 bp.B_full * bp.K + (bp.rem - 1)
         else bp.blkMeta2 (bp.B_full - 1) * bp.K + (bp.K - 1)) := by
  unfold prepPopBktBack popEndCoord popTopCoord; rfl

private theorem swapTailCoords_fields (bp : BlockPoolState) (t₁ t₂ : ℕ) :
    let bp₁ := (bp.swapTailCoords t₁ t₂).1
    bp₁.M = bp.M ∧ bp₁.K = bp.K ∧ bp₁.maxSlabs = bp.maxSlabs ∧
    bp₁.nSide = bp.nSide ∧ bp₁.q = bp.q ∧ bp₁.r = bp.r ∧ bp₁.head = bp.head ∧
    bp₁.actCode = bp.actCode ∧ bp₁.blkTag = bp.blkTag ∧ bp₁.blkMeta1 = bp.blkMeta1 ∧
    bp₁.tbPhysBlk = bp.tbPhysBlk ∧ bp₁.topSwapAct = bp.topSwapAct ∧
    bp₁.topSwapSrc = bp.topSwapSrc ∧ bp₁.topSwapDst = bp.topSwapDst ∧
    bp₁.topSwapCur = bp.topSwapCur := by
  dsimp only; unfold swapTailCoords
  split_ifs <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem swapTailCoords_tailRing_fst {bp : BlockPoolState} (hv : bp.CoreValid)
    {b rk_e t₁ t₂ : ℕ} (hb : b < bp.M) (hr_pos : 1 ≤ bp.r b)
    (hcur_le : bp.actCur b ≤ bp.r b - 1) (hrk_def : rk_e = (bp.head b + (bp.r b - 1)) % (6 * bp.K))
    (ht₁_def : t₁ = bp.tailRing b rk_e) (hlive₂ : bp.LiveTail t₂) :
    ((bp.swapTailCoords t₁ t₂).1).tailRing b rk_e = t₂ := by
  unfold swapTailCoords
  by_cases he : t₁ = t₂
  · rw [ite_eq_left he]; exact ht₁_def.symm.trans he
  · rw [ite_eq_right he]; dsimp only
    obtain ⟨_, hr_lt, _, _, _⟩ := hv.bkt_bounds b hb
    have htf := hv.tail_fwd b hb (bp.r b - 1) hcur_le (by omega)
    dsimp only at htf
    rw [← hrk_def, ← ht₁_def] at htf
    obtain ⟨_, _, _, _, hob_e, hor_e⟩ := htf
    obtain ⟨b₂, hb₂, k₂, hge₂, hlt₂, htr₂⟩ := hlive₂
    have htf2 := hv.tail_fwd b₂ hb₂ k₂ hge₂ hlt₂
    dsimp only at htf2; rw [htr₂] at htf2
    have hbrk_ne : ¬(b = bp.tailOwnerBkt t₂ ∧ rk_e = bp.tailOwnerRing t₂) := by
      rintro ⟨he1, he2⟩
      rw [htf2.2.2.2.2.1] at he1; rw [htf2.2.2.2.2.2] at he2
      subst he1
      exact he (ht₁_def.trans (by rw [he2, htr₂]))
    rw [hob_e, hor_e, set2_of_ne _ _ _ _ _ _ hbrk_ne, set2_self]

private def commitPopCase1 (bp₁ : BlockPoolState) (b : ℕ) : BlockPoolState :=
  { bp₁ with
    nSide := bp₁.nSide - 1
    r := set1 bp₁.r b (bp₁.r b - 1) }

private def commitPopCase2 (bp₁ : BlockPoolState) (b : ℕ) : BlockPoolState :=
  let P_prev := bp₁.B_full - 1
  let idx_prev := bp₁.blkMeta1 P_prev
  let tb_empty := bp₁.blkMeta2 bp₁.B_full
  let bp₂ := (bp₁.freeTb tb_empty).unresRemoveAt idx_prev
  { bp₂ with
    nSide := bp₁.nSide - 1
    r := set1 bp₁.r b (bp₁.r b - 1) }

/-- Commit the `nSide - 1` metadata shrink (`0` swaps) immediately after `prepPopBktBack` and
`slotIoPopBackProg`. -/
def commitPopBktBack (bp₁ : BlockPoolState) (b : ℕ) : BlockPoolState :=
  if 0 < bp₁.rem then
    bp₁.commitPopCase1 b
  else
    bp₁.commitPopCase2 b

theorem commitPopBktBack_apply (bp₁ : BlockPoolState) (b : ℕ) :
    bp₁.commitPopBktBack b =
      if 0 < bp₁.rem then
        { bp₁ with
          nSide := bp₁.nSide - 1
          r := set1 bp₁.r b (bp₁.r b - 1) }
      else
        let bp₂ :=
          (bp₁.freeTb (bp₁.blkMeta2 bp₁.B_full)).unresRemoveAt (bp₁.blkMeta1 (bp₁.B_full - 1))
        { bp₂ with
          nSide := bp₁.nSide - 1
          r := set1 bp₂.r b (bp₁.r b - 1) } := by
  unfold commitPopBktBack commitPopCase1 commitPopCase2
  split_ifs <;> rfl

attribute [local irreducible] swapTailCoords

theorem Balanced.prepPopBktBack_spec {bp : BlockPoolState} (hbal : bp.Balanced)
    {b : ℕ} (hb : b < bp.M) (hcnt : 0 < bp.bktCount b) :
    let res := bp.prepPopBktBack b
    res.1.Balanced ∧
    res.1.M = bp.M ∧
    res.1.K = bp.K ∧
    res.1.nSide = bp.nSide ∧
    (∀ b', res.1.bktCount b' = bp.bktCount b') ∧
    0 < bp.nSide ∧
    res.1.toPhys b (bp.bktCount b - 1) = bp.nSide - 1 ∧
    (∀ sw, res.2 = some sw → sw.p₁ < bp.nSide ∧ sw.p₂ < bp.nSide) ∧
    (∀ {α : Type*} (arr : ℕ → α) (b' loc' : ℕ),
      b' < bp.M → loc' < bp.bktCount b' →
      applyOptSwap res.2 arr (res.1.toPhys b' loc') = arr (bp.toPhys b' loc')) := by
  have hv := hbal.core
  have hK64 := hv.K_ge
  have hK := hv.K_pos
  have hn_pos : 0 < bp.nSide := by
    have hsum := hv.sum_bktCount_eq_nSide
    have hle : bp.bktCount b ≤ ∑ x ∈ Finset.range bp.M, bp.bktCount x :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.mpr hb)
    omega
  obtain ⟨hr_pos, hcur_le_rm1⟩ :=
    (hbal.hyst b hb).pos_r_and_actCur_lt hK64 (hv.bkt_bounds b hb).2.2.2.1 hcnt
  set rk_end := (bp.head b + (bp.r b - 1)) % (6 * bp.K)
  have hlive_end : bp.LiveTail (bp.popEndCoord b) :=
    ⟨b, hb, bp.r b - 1, hcur_le_rm1, by omega, rfl⟩
  have htop_facts : bp.LiveTail bp.popTopCoord ∧ bp.physOfTail bp.popTopCoord = bp.nSide - 1 := by
    unfold popTopCoord
    by_cases hrem : 0 < bp.rem
    · rw [ite_eq_left hrem]
      have hoff : bp.rem - 1 < bp.K := by
        have : bp.rem < bp.K := Nat.mod_lt bp.nSide hK; omega
      obtain ⟨hbo, hrko, hk_ge, hk_lt, htr⟩ :=
        hv.tail_bwd bp.B_full le_rfl (bp.rem - 1) hoff (Or.inr (by omega)) (Or.inl hv.blkTag_top)
      obtain ⟨_, _, hhdo, _, _⟩ := hv.bkt_bounds _ hbo
      have hrk_re := head_add_sub_mod hhdo hrko
      refine ⟨⟨_, hbo, _, hk_ge, hk_lt, by rwa [hrk_re]⟩, ?_⟩
      unfold physOfTail
      have hdiv : (bp.blkMeta2 bp.B_full * bp.K + (bp.rem - 1)) / bp.K = bp.blkMeta2 bp.B_full := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hoff, zero_add]
      have hmod : (bp.blkMeta2 bp.B_full * bp.K + (bp.rem - 1)) % bp.K = bp.rem - 1 := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff]
      rw [hdiv, hmod, (hv.tb_fwd bp.B_full le_rfl (Or.inl hv.blkTag_top)).2, hv.effBlk_B_full]
      have := hv.nSide_eq; omega
    · rw [ite_eq_right hrem]
      have hrem0 : bp.rem = 0 := by omega
      have hBf_pos : 1 ≤ bp.B_full := by
        have := hv.nSide_eq; rw [hrem0, add_zero] at this
        by_contra h0
        have he0 : bp.B_full = 0 := by omega
        rw [he0, zero_mul] at this; omega
      set P_prev := bp.B_full - 1
      have hP_lt : P_prev < bp.B_full := by dsimp only [P_prev]; omega
      have hP_tag0 : bp.blkTag P_prev = 0 := by
        by_contra hne0
        have := hbal.low_blk P_prev hne0; dsimp only [P_prev] at this; omega
      have hP_eff : bp.effBlk P_prev (bp.K - 1) = P_prev := by
        by_cases ha1 : bp.topSwapAct = 1
        · obtain ⟨hs2, hd2⟩ := hbal.low_swap ha1
          exact effBlk_eq_self_of_ne (by dsimp only [P_prev]; omega)
            (by dsimp only [P_prev]; omega)
        · unfold effBlk; simp [ha1]
      have hoff : bp.K - 1 < bp.K := by omega
      obtain ⟨hbo, hrko, hk_ge, hk_lt, htr⟩ :=
        hv.tail_bwd P_prev hP_lt.le (bp.K - 1) hoff (Or.inl hP_lt) (Or.inl hP_tag0)
      obtain ⟨_, _, hhdo, _, _⟩ := hv.bkt_bounds _ hbo
      have hrk_re := head_add_sub_mod hhdo hrko
      refine ⟨⟨_, hbo, _, hk_ge, hk_lt, by rwa [hrk_re]⟩, ?_⟩
      unfold physOfTail
      have hdiv : (bp.blkMeta2 P_prev * bp.K + (bp.K - 1)) / bp.K = bp.blkMeta2 P_prev := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hoff, zero_add]
      have hmod : (bp.blkMeta2 P_prev * bp.K + (bp.K - 1)) % bp.K = bp.K - 1 := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff]
      rw [hdiv, hmod, (hv.tb_fwd P_prev hP_lt.le (Or.inl hP_tag0)).2, hP_eff]
      have hns := hv.nSide_eq
      rw [hrem0, add_zero] at hns
      have hmul_eq : bp.B_full * bp.K = P_prev * bp.K + bp.K := by
        have h1 : bp.B_full = P_prev + 1 := by dsimp only [P_prev]; omega
        rw [h1, Nat.add_one_mul]
      omega
  dsimp only
  unfold prepPopBktBack
  have hsw_spec := hv.swapTailCoords_spec hlive_end htop_facts.1
  have hflds := swapTailCoords_fields bp (bp.popEndCoord b) bp.popTopCoord
  dsimp only at hflds
  set bp₁ := (bp.swapTailCoords (bp.popEndCoord b) bp.popTopCoord).1
  obtain ⟨hv₁, hsw_lt, harr₁⟩ := hsw_spec
  obtain ⟨hM₁, hK₁, hms₁, hn₁, hq₁, hr₁, hhd₁, hac₁, hbt₁, hbm1₁, htpb₁,
    htsa₁, htss₁, htsd₁, htsc₁⟩ := hflds
  have htr₁_end : bp₁.tailRing b rk_end = bp.popTopCoord :=
    swapTailCoords_tailRing_fst hv hb hr_pos hcur_le_rm1 rfl rfl htop_facts.1
  have hBf₁ : bp₁.B_full = bp.B_full := by dsimp only [B_full]; rw [hn₁, hK₁]
  have hrem₁ : bp₁.rem = bp.rem := by dsimp only [rem]; rw [hn₁, hK₁]
  have hacur₁ : ∀ x, bp₁.actCur x = bp.actCur x := fun x => by unfold actCur; rw [hac₁, hK₁]
  have hdebt₁ : bp₁.topDebt = bp.topDebt := by
    have hbw₁ : ∀ Q, bp₁.blkWork Q = bp.blkWork Q := fun Q => by
      unfold blkWork; rw [hbt₁, hK₁, hbm1₁]; dsimp only; rw [hac₁, hacur₁]
    unfold topDebt; simp only [hBf₁, hK₁, htsa₁, htss₁, htsd₁, htsc₁, hbt₁, hbw₁]
  have hbal₁ : bp₁.Balanced :=
    { core := hv₁
      bktCount_le := fun b' hb' => by
        rw [hM₁] at hb'; unfold bktCount; rw [hq₁, hK₁, hr₁, hms₁]
        exact hbal.bktCount_le b' hb'
      hyst := fun b' hb' => by
        rw [hM₁] at hb'; have hh' := hbal.hyst b' hb'
        unfold BktHyst at hh' ⊢; rwa [hac₁, hK₁, hr₁, hq₁, hacur₁]
      low_blk := fun P htag => by rw [hBf₁]; rw [hbt₁] at htag; exact hbal.low_blk P htag
      low_swap := fun ha => by rw [hBf₁, htss₁, htsd₁]; exact hbal.low_swap (htsa₁ ▸ ha)
      debt_le := by rw [hdebt₁, hrem₁]; exact hbal.debt_le }
  have htp₁_end : bp₁.toPhys b (bp.bktCount b - 1) = bp.nSide - 1 := by
    unfold toPhys bktCount
    rw [hq₁, hK₁, hacur₁, hhd₁]
    have hnot_slab : ¬(bp.q b * bp.K + bp.r b - 1 < bp.q b * bp.K) := by omega
    have hsub : bp.q b * bp.K + bp.r b - 1 - bp.q b * bp.K = bp.r b - 1 := by omega
    rw [ite_eq_right hnot_slab, hsub, ite_eq_right (not_lt.mpr hcur_le_rm1), htr₁_end]
    unfold physOfTail
    rw [hK₁, htpb₁, show bp₁.effBlk = bp.effBlk by
      ext E o; unfold effBlk; rw [htsa₁, htsc₁, htss₁, htsd₁]]
    exact htop_facts.2
  exact ⟨hbal₁, hM₁, hK₁, hn₁,
    fun b' => by unfold bktCount; rw [hq₁, hK₁, hr₁],
    hn_pos, htp₁_end, hsw_lt, fun arr b' loc' hb' hloc' => harr₁ arr b' loc' hb' hloc'⟩

private theorem pop_bktHyst16 {bp₁ : BlockPoolState} (hbal₁ : bp₁.Balanced)
    {b : ℕ} (hb : b < bp₁.M) (bp_x : BlockPoolState)
    (hc_x : bp_x.actCode b = bp₁.actCode b) (hk_x : bp_x.K = bp₁.K)
    (hq_x : bp_x.q b = bp₁.q b) (hr_x : bp_x.r b = bp₁.r b - 1) :
    bp_x.BktHyst b 16 := by
  have hh_b := hbal₁.hyst b hb
  have hac_x : bp_x.actCur b = bp₁.actCur b := by unfold actCur; rw [hc_x, hk_x]
  unfold BktHyst at hh_b ⊢
  rw [hc_x, hk_x, hq_x, hr_x, hac_x]
  by_cases hc0 : bp₁.actCode b = 0
  · rw [ite_eq_left hc0] at hh_b ⊢
    refine ⟨Or.inl (by rcases hh_b.1 with h | ⟨h0, _⟩ <;> omega), fun hq0 => ?_⟩
    rcases hh_b.2 hq0 with h | ⟨h0, _⟩
    · by_cases hgt : 7 * bp₁.K < 2 * (bp₁.r b - 1)
      · exact Or.inl hgt
      · exact Or.inr ⟨rfl, by omega, by omega⟩
    · omega
  · rw [ite_eq_right hc0] at hh_b ⊢
    split_ifs at hh_b ⊢ <;> omega

private theorem pop_physOfTail_end {bp₁ : BlockPoolState} (hbal₁ : bp₁.Balanced)
    {b : ℕ} (hb : b < bp₁.M) (hcnt : 0 < bp₁.bktCount b)
    (htp_end : bp₁.toPhys b (bp₁.bktCount b - 1) = bp₁.nSide - 1) :
    1 ≤ bp₁.r b ∧ bp₁.actCur b ≤ bp₁.r b - 1 ∧
    bp₁.physOfTail (bp₁.tailRing b ((bp₁.head b + (bp₁.r b - 1)) % (6 * bp₁.K))) =
      bp₁.nSide - 1 := by
  have hv₁ := hbal₁.core
  obtain ⟨hr_pos, hcur_le_rm1⟩ :=
    (hbal₁.hyst b hb).pos_r_and_actCur_lt hv₁.K_ge (hv₁.bkt_bounds b hb).2.2.2.1 hcnt
  refine ⟨hr_pos, hcur_le_rm1, ?_⟩
  have h := htp_end
  unfold toPhys bktCount at h
  have hns : ¬(bp₁.q b * bp₁.K + bp₁.r b - 1 < bp₁.q b * bp₁.K) := by omega
  have hsb : bp₁.q b * bp₁.K + bp₁.r b - 1 - bp₁.q b * bp₁.K = bp₁.r b - 1 := by omega
  rw [ite_eq_right hns, hsb, ite_eq_right (not_lt.mpr hcur_le_rm1)] at h
  exact h

private theorem commitPopCase1_spec {bp₁ : BlockPoolState} (hbal₁ : bp₁.Balanced)
    {b : ℕ} (hb : b < bp₁.M) (hcnt : 0 < bp₁.bktCount b) (hn_pos : 0 < bp₁.nSide)
    (htp_end : bp₁.toPhys b (bp₁.bktCount b - 1) = bp₁.nSide - 1) (hrem : 0 < bp₁.rem) :
    let bp' := bp₁.commitPopCase1 b
    bp'.StepInv b 16 ∧
    bp'.M = bp₁.M ∧
    bp'.K = bp₁.K ∧
    bp'.nSide = bp₁.nSide - 1 ∧
    bp'.bktCount b = bp₁.bktCount b - 1 ∧
    (∀ b' ≠ b, bp'.bktCount b' = bp₁.bktCount b') ∧
    bp'.topDebt ≤ 16 * bp'.rem + 16 ∧
    (∀ b' < bp₁.M, ∀ loc' < bp'.bktCount b',
      bp'.toPhys b' loc' = bp₁.toPhys b' loc' ∧ bp'.toPhys b' loc' < bp₁.nSide - 1) := by
  dsimp only
  have hv₁ := hbal₁.core
  have hK := hv₁.K_pos
  obtain ⟨hq_le, hr_lt, hhd_lt, hc_le, _⟩ := hv₁.bkt_bounds b hb
  obtain ⟨hr_pos, hcur_le_rm1, hphys_end⟩ := pop_physOfTail_end hbal₁ hb hcnt htp_end
  have hh_b16 := pop_bktHyst16 hbal₁ hb
  set rk_end := (bp₁.head b + (bp₁.r b - 1)) % (6 * bp₁.K)
  set t_end := bp₁.tailRing b rk_end
  set bp' := bp₁.commitPopCase1 b
  have hrem_lt1 : bp₁.rem < bp₁.K := Nat.mod_lt bp₁.nSide hK
  have hBf' : bp'.B_full = bp₁.B_full := by
    change (bp₁.nSide - 1) / bp₁.K = bp₁.B_full
    have hns := hv₁.nSide_eq
    rw [show bp₁.nSide - 1 = (bp₁.rem - 1) + bp₁.B_full * bp₁.K by omega,
      Nat.add_mul_div_right _ _ hK,
      Nat.div_eq_of_lt (by omega), zero_add]
  have hrem' : bp'.rem = bp₁.rem - 1 := by
    change (bp₁.nSide - 1) % bp₁.K = bp₁.rem - 1
    have hns := hv₁.nSide_eq
    rw [show bp₁.nSide - 1 = (bp₁.rem - 1) + bp₁.B_full * bp₁.K by omega,
      Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (by omega)]
  have hac' : ∀ x, bp'.actCur x = bp₁.actCur x := fun _ => rfl
  have hbc_b : bp'.bktCount b = bp₁.bktCount b - 1 := by
    unfold bktCount; dsimp only [bp', commitPopCase1]; rw [set1_self]; omega
  have hbc_ne : ∀ b' ≠ b, bp'.bktCount b' = bp₁.bktCount b' := fun b' hne => by
    unfold bktCount; dsimp only [bp', commitPopCase1]; rw [set1_of_ne _ _ _ _ hne]
  have htp_eq : ∀ b' < bp₁.M, ∀ loc' < bp'.bktCount b',
      bp'.toPhys b' loc' = bp₁.toPhys b' loc' ∧ bp'.toPhys b' loc' < bp₁.nSide - 1 :=
    fun b' hb' loc' hloc' => by
      have htp : bp'.toPhys b' loc' = bp₁.toPhys b' loc' := rfl
      rw [htp]
      have hloc1 : loc' < bp₁.bktCount b' := by
        by_cases hbe : b' = b
        · subst b'; rw [hbc_b] at hloc'; omega
        · rwa [hbc_ne b' hbe] at hloc'
      have hlt_ns := hv₁.toPhys_lt hb' hloc1
      have hne_end : bp₁.toPhys b' loc' ≠ bp₁.nSide - 1 := fun heq => by
        rw [← htp_end] at heq
        obtain ⟨rfl, hl_eq⟩ := hv₁.toPhys_inj hb' hloc1 hb (by omega) heq
        rw [hbc_b] at hloc'; omega
      exact ⟨rfl, by omega⟩
  have hcv' : bp'.CoreValid :=
    { M_pos := hv₁.M_pos
      K_ge := hv₁.K_ge
      bkt_bounds := fun b' hb' => by
        rw [hac']; dsimp only [bp', commitPopCase1]
        by_cases hbe : b' = b
        · subst b'; rw [set1_self]
          exact ⟨hq_le, by omega, hhd_lt, hc_le, hcur_le_rm1⟩
        · rw [set1_of_ne _ _ _ _ hbe]; exact hv₁.bkt_bounds b' hb'
      blkTag_lt := fun P hP => hv₁.blkTag_lt P (hBf' ▸ hP)
      blkTag_top := by rw [hBf']; exact hv₁.blkTag_top
      unres_fwd := fun i hi => by rw [hBf']; exact hv₁.unres_fwd i hi
      unres_bwd := fun P hP h0 => hv₁.unres_bwd P (hBf' ▸ hP) h0
      slab_fwd := fun b' hb' v hvp => by rw [hBf']; exact hv₁.slab_fwd b' hb' v hvp
      slab_bwd := fun P hP h1 => hv₁.slab_bwd P (hBf' ▸ hP) h1
      act_fwd := fun b' hb' hne => by rw [hBf']; exact hv₁.act_fwd b' hb' hne
      act_bwd := fun P hP h2 => hv₁.act_bwd P (hBf' ▸ hP) h2
      tb_fwd := fun P hP hor => hv₁.tb_fwd P (hBf' ▸ hP) hor
      freeTb_valid := fun i hi => by
        obtain ⟨h1, h2⟩ := hv₁.freeTb_valid i hi
        exact ⟨h1, fun P hP hor => h2 P (hBf' ▸ hP) hor⟩
      freeTb_inj := hv₁.freeTb_inj
      tbHighWater_supply := by rw [hBf']; exact hv₁.tbHighWater_supply
      tbHighWater_le_max := hv₁.tbHighWater_le_max
      topSwap_act_le := hv₁.topSwap_act_le
      topSwap_valid := fun ha => by rw [hBf']; exact hv₁.topSwap_valid ha
      tail_fwd := fun b' hb' k hk_ge hk_lt => by
        dsimp only
        rw [hBf', hrem']
        rw [hac'] at hk_ge
        rw [show bp'.M = bp₁.M from rfl] at hb'
        rw [show bp'.r = set1 bp₁.r b (bp₁.r b - 1) from rfl] at hk_lt
        rw [show bp'.M = bp₁.M from rfl, show bp'.K = bp₁.K from rfl,
          show bp'.head = bp₁.head from rfl, show bp'.tailRing = bp₁.tailRing from rfl,
          show bp'.tbPhysBlk = bp₁.tbPhysBlk from rfl,
          show bp'.blkMeta2 = bp₁.blkMeta2 from rfl,
          show bp'.blkTag = bp₁.blkTag from rfl,
          show bp'.blkMeta1 = bp₁.blkMeta1 from rfl,
          show bp'.tailOwnerBkt = bp₁.tailOwnerBkt from rfl,
          show bp'.tailOwnerRing = bp₁.tailOwnerRing from rfl, hac']
        have hk_lt_old : k < bp₁.r b' := by
          by_cases hbe : b' = b
          · subst b'; rw [set1_self] at hk_lt; omega
          · rwa [set1_of_ne _ _ _ _ hbe] at hk_lt
        have htf := hv₁.tail_fwd b' hb' k hk_ge hk_lt_old
        dsimp only at htf
        obtain ⟨ha, hbl, hcm, hkd, hob, hor⟩ := htf
        refine ⟨ha, hbl, hcm, ?_, hob, hor⟩
        rcases hkd with ⟨h0, hlt_or⟩ | h2
        · refine Or.inl ⟨h0, ?_⟩
          rcases hlt_or with hPlt | hoff_lt
          · exact Or.inl hPlt
          · by_cases hp_top : bp₁.tbPhysBlk
                (bp₁.tailRing b' ((bp₁.head b' + k) % (6 * bp₁.K)) / bp₁.K) = bp₁.B_full
            · right
              -- Its physical slot is `< bp₁.nSide - 1`!
              have hloc'_lt : bp₁.q b' * bp₁.K + k < bp'.bktCount b' := by
                unfold bktCount; dsimp only [bp', commitPopCase1]; omega
              have hp_lt := (htp_eq b' hb' (bp₁.q b' * bp₁.K + k) hloc'_lt).2
              change bp₁.toPhys b' (bp₁.q b' * bp₁.K + k) < bp₁.nSide - 1 at hp_lt
              unfold toPhys at hp_lt
              rw [ite_eq_right (by omega), Nat.add_sub_cancel_left,
                ite_eq_right (not_lt.mpr hk_ge)] at hp_lt
              unfold physOfTail at hp_lt
              rw [hp_top, hv₁.effBlk_B_full] at hp_lt
              have := hv₁.nSide_eq; omega
            · exact Or.inl (by omega)
        · exact Or.inr h2
      tail_bwd := fun P hP_le off hoff hlt hor => by
        dsimp only
        change off < bp₁.K at hoff
        rw [hBf'] at hP_le; rw [hBf', hrem'] at hlt
        have hlt_old : P < bp₁.B_full ∨ off < bp₁.rem :=
          hlt.imp id (fun h => by omega)
        obtain ⟨hbo, hrko, hk_ge, hk_lt, htr⟩ := hv₁.tail_bwd P hP_le off hoff hlt_old hor
        rw [show bp'.M = bp₁.M from rfl, show bp'.K = bp₁.K from rfl,
          show bp'.blkMeta2 = bp₁.blkMeta2 from rfl,
          show bp'.tailOwnerBkt = bp₁.tailOwnerBkt from rfl,
          show bp'.tailOwnerRing = bp₁.tailOwnerRing from rfl,
          show bp'.head = bp₁.head from rfl, show bp'.tailRing = bp₁.tailRing from rfl, hac']
        refine ⟨hbo, hrko, hk_ge, ?_, htr⟩
        dsimp only [bp', commitPopCase1]
        set t := bp₁.blkMeta2 P * bp₁.K + off
        by_cases hbe : bp₁.tailOwnerBkt t = b
        · rw [hbe, set1_self]; rw [hbe] at hk_ge hk_lt htr
          -- Show `k ≠ bp₁.r b - 1` because `physOfTail t < bp₁.nSide - 1`!
          have hne_k : (bp₁.tailOwnerRing t + 6 * bp₁.K - bp₁.head b) % (6 * bp₁.K) ≠
              bp₁.r b - 1 := fun hke => by
            have hrk_eq : bp₁.tailOwnerRing t = rk_end := by
              rw [← head_add_sub_mod hhd_lt hrko, hke]
            have ht_eq_end : t = t_end := htr.symm.trans (by dsimp only [t_end]; rw [hrk_eq])
            have hp_t : bp₁.physOfTail t = bp₁.effBlk P off * bp₁.K + off := by
              unfold physOfTail
              have hdiv : t / bp₁.K = bp₁.blkMeta2 P := by
                dsimp only [t]
                rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hoff, zero_add]
              have hmod : t % bp₁.K = off := by
                dsimp only [t]
                rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff]
              rw [hdiv, hmod, (hv₁.tb_fwd P hP_le (hor.imp id And.left)).2]
            rw [ht_eq_end, hphys_end] at hp_t
            by_cases hPlt : P < bp₁.B_full
            · have heff_lt := hv₁.effBlk_lt_B_full hPlt off
              have h1 : (bp₁.effBlk P off + 1) * bp₁.K ≤ bp₁.B_full * bp₁.K :=
                Nat.mul_le_mul_right _ heff_lt
              rw [Nat.add_one_mul] at h1
              have := hv₁.nSide_eq; omega
            · have hp_eq : P = bp₁.B_full := by omega
              rw [hp_eq, hv₁.effBlk_B_full] at hp_t
              have := hv₁.nSide_eq; omega
          omega
        · rw [set1_of_ne _ _ _ _ hbe]; exact hk_lt }
  have hdebt_eq : bp'.topDebt = bp₁.topDebt := by
    unfold topDebt; rw [hBf']; rfl
  have hsi' : bp'.StepInv b 16 :=
    { core := hcv'
      bktCount_le := fun b' hb' => by
        by_cases hbe : b' = b
        · subst b'; rw [hbc_b]; exact (Nat.sub_le _ 1).trans (hbal₁.bktCount_le b hb')
        · rw [hbc_ne b' hbe]; exact hbal₁.bktCount_le b' hb'
      t_le := le_rfl
      hyst_tick := fun _ => hh_b16 bp' rfl rfl rfl (set1_self _ _ _)
      hyst_other := fun b' hb' hne => by
        have hh' := hbal₁.hyst b' hb'
        unfold BktHyst at hh' ⊢
        rw [hac', show bp'.actCode b' = bp₁.actCode b' from rfl,
          show bp'.K = bp₁.K from rfl, show bp'.q b' = bp₁.q b' from rfl,
          show bp'.r b' = bp₁.r b' from set1_of_ne _ _ _ _ hne]
        exact hh'
      low_blk := fun P htag => by rw [hBf']; exact hbal₁.low_blk P htag
      low_swap := fun ha => by rw [hBf']; exact hbal₁.low_swap ha }
  exact ⟨hsi', rfl, rfl, rfl, hbc_b, hbc_ne,
    by rw [hdebt_eq, hrem']; have := hbal₁.debt_le; omega, htp_eq⟩

private theorem commitPopCase2_tail_bwd {bp₁ : BlockPoolState} (hbal₁ : bp₁.Balanced)
    {b : ℕ} (hb : b < bp₁.M) (hcnt : 0 < bp₁.bktCount b) (hn_pos : 0 < bp₁.nSide)
    (htp_end : bp₁.toPhys b (bp₁.bktCount b - 1) = bp₁.nSide - 1) (hrem : ¬0 < bp₁.rem) :
    let bp' := bp₁.commitPopCase2 b
    ∀ P ≤ bp'.B_full, ∀ off < bp'.K, (P < bp'.B_full ∨ off < bp'.rem) →
      (bp'.blkTag P = 0 ∨ (bp'.blkTag P = 2 ∧ bp'.actCur (bp'.blkMeta1 P) ≤ off)) →
      let t := bp'.blkMeta2 P * bp'.K + off
      let b' := bp'.tailOwnerBkt t
      let rk := bp'.tailOwnerRing t
      let k := (rk + 6 * bp'.K - bp'.head b') % (6 * bp'.K)
      b' < bp'.M ∧ rk < 6 * bp'.K ∧ bp'.actCur b' ≤ k ∧ k < bp'.r b' ∧
      bp'.tailRing b' rk = t := by
  dsimp only
  intro P hP_le off hoff hlt hor
  have hv₁ := hbal₁.core
  have hK := hv₁.K_pos
  obtain ⟨_, _, hhd_lt, _, _⟩ := hv₁.bkt_bounds b hb
  obtain ⟨hr_pos, _, hphys_end⟩ := pop_physOfTail_end hbal₁ hb hcnt htp_end
  set rk_end := (bp₁.head b + (bp₁.r b - 1)) % (6 * bp₁.K)
  set t_end := bp₁.tailRing b rk_end
  have hrem0 : bp₁.rem = 0 := by omega
  have hBf_pos : 1 ≤ bp₁.B_full := by
    have hns := hv₁.nSide_eq; rw [hrem0, add_zero] at hns
    by_contra h0
    have he0 : bp₁.B_full = 0 := by omega
    rw [he0, zero_mul] at hns; omega
  set P_prev := bp₁.B_full - 1
  have hP_lt : P_prev < bp₁.B_full := by dsimp only [P_prev]; omega
  have hP_tag0 : bp₁.blkTag P_prev = 0 := by
    by_contra hne0
    have := hbal₁.low_blk P_prev hne0; dsimp only [P_prev] at this; omega
  obtain ⟨hidx_lt, _⟩ := hv₁.unres_bwd P_prev hP_lt hP_tag0
  set bp' := bp₁.commitPopCase2 b
  have hns_sub : bp₁.nSide - 1 = P_prev * bp₁.K + (bp₁.K - 1) := by
    have hns := hv₁.nSide_eq; rw [hrem0, add_zero] at hns
    have hmul : bp₁.B_full * bp₁.K = P_prev * bp₁.K + bp₁.K := by
      have h1 : bp₁.B_full = P_prev + 1 := by dsimp only [P_prev]; omega
      rw [h1, Nat.add_one_mul]
    omega
  have hBf' : bp'.B_full = P_prev := by
    change (bp₁.nSide - 1) / bp₁.K = P_prev
    rw [hns_sub, Nat.add_comm, Nat.add_mul_div_right _ _ hK,
      Nat.div_eq_of_lt (by omega), zero_add]
  have hrem' : bp'.rem = bp₁.K - 1 := by
    change (bp₁.nSide - 1) % bp₁.K = bp₁.K - 1
    rw [hns_sub, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have hac' : ∀ x, bp'.actCur x = bp₁.actCur x := fun _ => rfl
  set lastIdx := bp₁.unresLen - 1
  obtain ⟨_, hPl_tag0, _⟩ := hv₁.unres_fwd lastIdx (by omega)
  set P_last := bp₁.unresStack lastIdx
  change off < bp₁.K at hoff
  rw [hBf'] at hP_le; rw [hBf', hrem'] at hlt
  have hP_lt_Bf : P < bp₁.B_full := hP_le.trans_lt hP_lt
  have hor_old : bp₁.blkTag P = 0 ∨
      (bp₁.blkTag P = 2 ∧ bp₁.actCur (bp₁.blkMeta1 P) ≤ off) := by
    rcases hor with h0 | ⟨h2, hge⟩
    · exact Or.inl h0
    · change bp₁.blkTag P = 2 at h2
      have hne_l : P ≠ P_last := fun he => by
        rw [he, hPl_tag0] at h2; exact absurd h2 (by decide)
      have hm1_P : bp'.blkMeta1 P = bp₁.blkMeta1 P := by
        dsimp only [bp', commitPopCase2, unresRemoveAt, freeTb]
        split_ifs
        · exact set1_of_ne _ _ _ _ hne_l
        · rfl
      rw [hm1_P, hac'] at hge
      exact Or.inr ⟨h2, hge⟩
  obtain ⟨hbo, hrko, hk_ge, hk_lt, htr⟩ :=
    hv₁.tail_bwd P hP_lt_Bf.le off hoff (Or.inl hP_lt_Bf) hor_old
  rw [show bp'.M = bp₁.M from rfl, show bp'.K = bp₁.K from rfl,
    show bp'.blkMeta2 = bp₁.blkMeta2 from rfl,
    show bp'.tailOwnerBkt = bp₁.tailOwnerBkt from rfl,
    show bp'.tailOwnerRing = bp₁.tailOwnerRing from rfl,
    show bp'.head = bp₁.head from rfl, show bp'.tailRing = bp₁.tailRing from rfl, hac']
  refine ⟨hbo, hrko, hk_ge, ?_, htr⟩
  dsimp only [bp', commitPopCase2, unresRemoveAt, freeTb]
  set t := bp₁.blkMeta2 P * bp₁.K + off
  by_cases hbe : bp₁.tailOwnerBkt t = b
  · rw [hbe, set1_self]; rw [hbe] at hk_ge hk_lt htr
    have hne_k : (bp₁.tailOwnerRing t + 6 * bp₁.K - bp₁.head b) % (6 * bp₁.K) ≠
        bp₁.r b - 1 := fun hke => by
      have hrk_eq : bp₁.tailOwnerRing t = rk_end := by
        rw [← head_add_sub_mod hhd_lt hrko, hke]
      have ht_eq_end : t = t_end := htr.symm.trans (by dsimp only [t_end]; rw [hrk_eq])
      have hp_t : bp₁.physOfTail t = bp₁.effBlk P off * bp₁.K + off := by
        unfold physOfTail
        have hdiv : t / bp₁.K = bp₁.blkMeta2 P := by
          dsimp only [t]
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hoff, zero_add]
        have hmod : t % bp₁.K = off := by
          dsimp only [t]
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff]
        rw [hdiv, hmod, (hv₁.tb_fwd P hP_lt_Bf.le (hor_old.imp id And.left)).2]
      rw [ht_eq_end, hphys_end, hns_sub] at hp_t
      by_cases hPlt : P < P_prev
      · have heff_le : bp₁.effBlk P off < P_prev := by
          by_cases ha1 : bp₁.topSwapAct = 1
          · obtain ⟨_, _, _, _, _⟩ := hv₁.topSwap_valid ha1
            obtain ⟨hs2, hd2⟩ := hbal₁.low_swap ha1
            unfold effBlk; split_ifs <;> dsimp only [P_prev] at * <;> omega
          · unfold effBlk; simp only [ha1, false_and, ↓reduceIte]; exact hPlt
        have h1 : (bp₁.effBlk P off + 1) * bp₁.K ≤ P_prev * bp₁.K :=
          Nat.mul_le_mul_right _ heff_le
        rw [Nat.add_one_mul] at h1; omega
      · have hp_eq : P = P_prev := by omega
        have heff_p : bp₁.effBlk P_prev off = P_prev := by
          by_cases ha1 : bp₁.topSwapAct = 1
          · obtain ⟨hs2, hd2⟩ := hbal₁.low_swap ha1
            exact effBlk_eq_self_of_ne (by dsimp only [P_prev]; omega)
              (by dsimp only [P_prev]; omega)
          · unfold effBlk; simp [ha1]
        rw [hp_eq, heff_p] at hp_t; omega
    omega
  · rw [set1_of_ne _ _ _ _ hbe]; exact hk_lt

private theorem commitPopCase2_spec {bp₁ : BlockPoolState} (hbal₁ : bp₁.Balanced)
    {b : ℕ} (hb : b < bp₁.M) (hcnt : 0 < bp₁.bktCount b) (hn_pos : 0 < bp₁.nSide)
    (htp_end : bp₁.toPhys b (bp₁.bktCount b - 1) = bp₁.nSide - 1) (hrem : ¬0 < bp₁.rem) :
    let bp' := bp₁.commitPopCase2 b
    bp'.StepInv b 16 ∧
    bp'.M = bp₁.M ∧
    bp'.K = bp₁.K ∧
    bp'.nSide = bp₁.nSide - 1 ∧
    bp'.bktCount b = bp₁.bktCount b - 1 ∧
    (∀ b' ≠ b, bp'.bktCount b' = bp₁.bktCount b') ∧
    bp'.topDebt ≤ 16 * bp'.rem + 16 ∧
    (∀ b' < bp₁.M, ∀ loc' < bp'.bktCount b',
      bp'.toPhys b' loc' = bp₁.toPhys b' loc' ∧ bp'.toPhys b' loc' < bp₁.nSide - 1) := by
  dsimp only
  have hv₁ := hbal₁.core
  have hK := hv₁.K_pos
  obtain ⟨hq_le, hr_lt, hhd_lt, hc_le, _⟩ := hv₁.bkt_bounds b hb
  obtain ⟨hr_pos, hcur_le_rm1, _⟩ := pop_physOfTail_end hbal₁ hb hcnt htp_end
  have hh_b16 := pop_bktHyst16 hbal₁ hb
  have hrem0 : bp₁.rem = 0 := by omega
  have hBf_pos : 1 ≤ bp₁.B_full := by
    have hns := hv₁.nSide_eq; rw [hrem0, add_zero] at hns
    by_contra h0
    have he0 : bp₁.B_full = 0 := by omega
    rw [he0, zero_mul] at hns; omega
  have hdebt0 : bp₁.topDebt = 0 := by
    have h := hbal₁.debt_le; rw [hrem0] at h; omega
  have hclean2 := (hv₁.topDebt_eq_zero_iff.mp hdebt0)
  set P_prev := bp₁.B_full - 1
  have hP_lt : P_prev < bp₁.B_full := by dsimp only [P_prev]; omega
  have hP_tag0 : bp₁.blkTag P_prev = 0 := by
    by_contra hne0
    have := hbal₁.low_blk P_prev hne0; dsimp only [P_prev] at this; omega
  obtain ⟨hidx_lt, hidx_eq⟩ := hv₁.unres_bwd P_prev hP_lt hP_tag0
  set idx_prev := bp₁.blkMeta1 P_prev
  set tb_empty := bp₁.blkMeta2 bp₁.B_full
  obtain ⟨htb_e_lt, htb_e_eq⟩ := hv₁.tb_fwd bp₁.B_full le_rfl (Or.inl hv₁.blkTag_top)
  set bp' := bp₁.commitPopCase2 b
  have hns_sub : bp₁.nSide - 1 = P_prev * bp₁.K + (bp₁.K - 1) := by
    have hns := hv₁.nSide_eq; rw [hrem0, add_zero] at hns
    have hmul : bp₁.B_full * bp₁.K = P_prev * bp₁.K + bp₁.K := by
      have h1 : bp₁.B_full = P_prev + 1 := by dsimp only [P_prev]; omega
      rw [h1, Nat.add_one_mul]
    omega
  have hBf' : bp'.B_full = P_prev := by
    change (bp₁.nSide - 1) / bp₁.K = P_prev
    rw [hns_sub, Nat.add_comm, Nat.add_mul_div_right _ _ hK,
      Nat.div_eq_of_lt (by omega), zero_add]
  have hrem' : bp'.rem = bp₁.K - 1 := by
    change (bp₁.nSide - 1) % bp₁.K = bp₁.K - 1
    rw [hns_sub, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have hac' : ∀ x, bp'.actCur x = bp₁.actCur x := fun _ => rfl
  have hbc_b : bp'.bktCount b = bp₁.bktCount b - 1 := by
    unfold bktCount
    dsimp only [bp', commitPopCase2, unresRemoveAt, freeTb]; rw [set1_self]; omega
  have hbc_ne : ∀ b' ≠ b, bp'.bktCount b' = bp₁.bktCount b' := fun b' hne => by
    unfold bktCount
    dsimp only [bp', commitPopCase2, unresRemoveAt, freeTb]
    rw [set1_of_ne _ _ _ _ hne]
  have htp_eq : ∀ b' < bp₁.M, ∀ loc' < bp'.bktCount b',
      bp'.toPhys b' loc' = bp₁.toPhys b' loc' ∧ bp'.toPhys b' loc' < bp₁.nSide - 1 :=
    fun b' hb' loc' hloc' => by
      have htp : bp'.toPhys b' loc' = bp₁.toPhys b' loc' := rfl
      rw [htp]
      have hloc1 : loc' < bp₁.bktCount b' := by
        by_cases hbe : b' = b
        · subst b'; rw [hbc_b] at hloc'; omega
        · rwa [hbc_ne b' hbe] at hloc'
      have hlt_ns := hv₁.toPhys_lt hb' hloc1
      have hne_end : bp₁.toPhys b' loc' ≠ bp₁.nSide - 1 := fun heq => by
        rw [← htp_end] at heq
        obtain ⟨rfl, _⟩ := hv₁.toPhys_inj hb' hloc1 hb (by omega) heq
        rw [hbc_b] at hloc'; omega
      exact ⟨rfl, by omega⟩
  set lastIdx := bp₁.unresLen - 1
  obtain ⟨hPl_lt, hPl_tag0, hPl_m1⟩ := hv₁.unres_fwd lastIdx (by omega)
  set P_last := bp₁.unresStack lastIdx
  have hPl_ne_prev : idx_prev < lastIdx → P_last ≠ P_prev := fun hlt he => by
    have h : bp₁.blkMeta1 P_last = lastIdx := hPl_m1
    rw [he] at h; dsimp only [idx_prev] at hlt; omega
  have hcv' : bp'.CoreValid :=
    { M_pos := hv₁.M_pos
      K_ge := hv₁.K_ge
      bkt_bounds := fun b' hb' => by
        rw [hac']; dsimp only [bp', commitPopCase2, unresRemoveAt, freeTb]
        by_cases hbe : b' = b
        · subst b'; rw [set1_self]
          exact ⟨hq_le, by omega, hhd_lt, hc_le, hcur_le_rm1⟩
        · rw [set1_of_ne _ _ _ _ hbe]; exact hv₁.bkt_bounds b' hb'
      blkTag_lt := fun P hP => by
        rw [hBf'] at hP; exact hv₁.blkTag_lt P (hP.trans hP_lt)
      blkTag_top := by rw [hBf']; exact hP_tag0
      unres_fwd := fun i hi => by
        rw [hBf']
        dsimp only [bp', commitPopCase2, unresRemoveAt, freeTb] at hi ⊢
        by_cases hie : i = idx_prev
        · subst hie
          have hne := hPl_ne_prev hi
          rw [set1_self, ite_eq_left hi, set1_self]
          exact ⟨by dsimp only [P_last, lastIdx, P_prev] at hPl_lt hne ⊢; omega, hPl_tag0, rfl⟩
        · rw [set1_of_ne _ _ _ _ hie]
          obtain ⟨h1, h2, h3⟩ := hv₁.unres_fwd i (by omega)
          have hne_p : bp₁.unresStack i ≠ P_prev := fun he => by
            rw [he] at h3; exact hie h3.symm
          have hne_l : bp₁.unresStack i ≠ P_last := fun he => by
            rw [he, hPl_m1] at h3; omega
          split_ifs
          · rw [set1_of_ne _ _ _ _ hne_l]
            exact ⟨by dsimp only [P_prev] at hne_p ⊢; omega, h2, h3⟩
          · exact ⟨by dsimp only [P_prev] at hne_p ⊢; omega, h2, h3⟩
      unres_bwd := fun P hP h0 => by
        rw [hBf'] at hP
        have hp_ne : P ≠ P_prev := ne_of_lt hP
        obtain ⟨hm_lt, hm_eq⟩ := hv₁.unres_bwd P (hP.trans hP_lt) h0
        dsimp only [bp', commitPopCase2, unresRemoveAt, freeTb]
        by_cases hPl : P = P_last
        · subst hPl
          have hilt : idx_prev < lastIdx := by
            by_contra hge
            have he_i : idx_prev = lastIdx := by omega
            exact hp_ne (by dsimp only [P_last]; rw [← he_i, hidx_eq])
          rw [ite_eq_left hilt, set1_self, set1_self]
          exact ⟨hilt, rfl⟩
        · have hm_ne_l : bp₁.blkMeta1 P ≠ lastIdx := fun he =>
            hPl (hm_eq.symm.trans (congrArg _ he))
          have hm_ne_i : bp₁.blkMeta1 P ≠ idx_prev := fun he =>
            hp_ne (hm_eq.symm.trans ((congrArg _ he).trans hidx_eq))
          split_ifs
          · rw [set1_of_ne _ _ _ _ hPl, set1_of_ne _ _ _ _ hm_ne_i]
            exact ⟨by omega, hm_eq⟩
          · rw [set1_of_ne _ _ _ _ hm_ne_i]
            exact ⟨by omega, hm_eq⟩
      slab_fwd := fun b' hb' v hvp => by
        obtain ⟨h1, h2, h3, h4⟩ := hv₁.slab_fwd b' hb' v hvp
        have hlow := hbal₁.low_blk _ (by rw [h2]; decide)
        have hne_l : bp₁.slabOf b' v ≠ P_last := fun he => by
          rw [he, hPl_tag0] at h2; exact absurd h2 (by decide)
        rw [hBf']; dsimp only [bp', commitPopCase2, unresRemoveAt, freeTb]
        split_ifs
        · rw [set1_of_ne _ _ _ _ hne_l]
          exact ⟨by dsimp only [P_prev]; omega, h2, h3, h4⟩
        · exact ⟨by dsimp only [P_prev]; omega, h2, h3, h4⟩
      slab_bwd := fun P hP h1 => by
        change bp₁.blkTag P = 1 at h1
        rw [hBf'] at hP
        have hne_l : P ≠ P_last := fun he => by
          rw [he, hPl_tag0] at h1; exact absurd h1 (by decide)
        dsimp only [bp', commitPopCase2, unresRemoveAt, freeTb]
        split_ifs
        · rw [set1_of_ne _ _ _ _ hne_l]; exact hv₁.slab_bwd P (hP.trans hP_lt) h1
        · exact hv₁.slab_bwd P (hP.trans hP_lt) h1
      act_fwd := fun b' hb' hne => by
        obtain ⟨h1, h2, h3⟩ := hv₁.act_fwd b' hb' hne
        have hlow := hbal₁.low_blk _ (by rw [h2]; decide)
        have hne_l : bp₁.actBlk b' ≠ P_last := fun he => by
          rw [he, hPl_tag0] at h2; exact absurd h2 (by decide)
        rw [hBf']; dsimp only [bp', commitPopCase2, unresRemoveAt, freeTb]
        split_ifs
        · rw [set1_of_ne _ _ _ _ hne_l]
          exact ⟨by dsimp only [P_prev]; omega, h2, h3⟩
        · exact ⟨by dsimp only [P_prev]; omega, h2, h3⟩
      act_bwd := fun P hP h2 => by
        change bp₁.blkTag P = 2 at h2
        rw [hBf'] at hP
        have hne_l : P ≠ P_last := fun he => by
          rw [he, hPl_tag0] at h2; exact absurd h2 (by decide)
        dsimp only [bp', commitPopCase2, unresRemoveAt, freeTb]
        split_ifs
        · rw [set1_of_ne _ _ _ _ hne_l]; exact hv₁.act_bwd P (hP.trans hP_lt) h2
        · exact hv₁.act_bwd P (hP.trans hP_lt) h2
      tb_fwd := fun P hP hor => by
        rw [hBf'] at hP
        exact hv₁.tb_fwd P (hP.trans hP_lt.le) hor
      freeTb_valid := fun i hi => by
        rw [hBf']
        dsimp only [bp', commitPopCase2, unresRemoveAt, freeTb] at hi ⊢
        by_cases hit : i = bp₁.freeTbTop
        · subst hit; rw [set1_self]
          refine ⟨htb_e_lt, fun P hP hor hme => ?_⟩
          have htbP := (hv₁.tb_fwd P (hP.trans hP_lt.le) hor).2
          rw [hme, htb_e_eq] at htbP
          dsimp only [P_prev] at hP; omega
        · obtain ⟨h1, h2⟩ := hv₁.freeTb_valid i (by omega)
          rw [set1_of_ne _ _ _ _ hit]
          exact ⟨h1, fun P hP hor => h2 P (hP.trans hP_lt.le) hor⟩
      freeTb_inj := fun i hi j hj heq => by
        dsimp only [bp', commitPopCase2, unresRemoveAt, freeTb] at hi hj heq ⊢
        have hnot_in : ∀ idx < bp₁.freeTbTop, bp₁.freeTbStack idx ≠ tb_empty :=
          fun idx hidx => ((hv₁.freeTb_valid idx hidx).2 bp₁.B_full le_rfl
            (Or.inl hv₁.blkTag_top)).symm
        by_cases hi_t : i = bp₁.freeTbTop
        · by_cases hj_t : j = bp₁.freeTbTop
          · exact hi_t.trans hj_t.symm
          · rw [hi_t, set1_self, set1_of_ne _ _ _ _ hj_t] at heq
            exact absurd heq.symm (hnot_in j (by omega))
        · by_cases hj_t : j = bp₁.freeTbTop
          · rw [hj_t, set1_of_ne _ _ _ _ hi_t, set1_self] at heq
            exact absurd heq (hnot_in i (by omega))
          · rw [set1_of_ne _ _ _ _ hi_t, set1_of_ne _ _ _ _ hj_t] at heq
            exact hv₁.freeTb_inj i (by omega) j (by omega) heq
      tbHighWater_supply := by
        rw [hBf']
        have hBf_add1 : P_prev + 1 = bp₁.B_full := by dsimp only [P_prev]; omega
        have hcard_old : ((Finset.range (bp₁.B_full + 1)).filter
            (fun P => bp₁.blkTag P = 0 ∨ bp₁.blkTag P = 2)).card =
            ((Finset.range (P_prev + 1)).filter
              (fun P => bp₁.blkTag P = 0 ∨ bp₁.blkTag P = 2)).card + 1 := by
          rw [hBf_add1, Finset.range_add_one, Finset.filter_insert]
          simp only [hv₁.blkTag_top, true_or, ↓reduceIte]
          have hnot : bp₁.B_full ∉ (Finset.range bp₁.B_full).filter
              (fun P => bp₁.blkTag P = 0 ∨ bp₁.blkTag P = 2) := by simp
          exact Finset.card_insert_of_notMem hnot
        have hsup := hv₁.tbHighWater_supply
        rw [hcard_old] at hsup
        change bp₁.tbHighWater ≤ (bp₁.freeTbTop + 1) +
          ((Finset.range (P_prev + 1)).filter
            (fun P => bp₁.blkTag P = 0 ∨ bp₁.blkTag P = 2)).card
        omega
      tbHighWater_le_max := hv₁.tbHighWater_le_max
      topSwap_act_le := hv₁.topSwap_act_le
      topSwap_valid := fun ha => by
        change bp₁.topSwapAct = 1 at ha
        obtain ⟨h1, _, _, h4, h5⟩ := hv₁.topSwap_valid ha
        obtain ⟨hs2, hd2⟩ := hbal₁.low_swap ha
        rw [hBf']
        change bp₁.topSwapCur < bp₁.K ∧ bp₁.topSwapSrc < P_prev ∧ bp₁.topSwapDst < P_prev ∧
          bp₁.blkTag bp₁.topSwapDst = 0 ∧ bp₁.topSwapSrc ≠ bp₁.topSwapDst
        by_cases hge2 : 2 ≤ bp₁.B_full
        · obtain ⟨hs_ne, hd_ne⟩ := (hclean2 hge2).2 ha
          exact ⟨h1, by dsimp only [P_prev]; omega, by dsimp only [P_prev]; omega, h4, h5⟩
        · omega
      tail_fwd := fun b' hb' k hk_ge hk_lt => by
        dsimp only
        rw [hBf', hrem']
        rw [hac'] at hk_ge
        rw [show bp'.M = bp₁.M from rfl] at hb'
        rw [show bp'.r = set1 bp₁.r b (bp₁.r b - 1) from rfl] at hk_lt
        rw [show bp'.M = bp₁.M from rfl, show bp'.K = bp₁.K from rfl,
          show bp'.head = bp₁.head from rfl, show bp'.tailRing = bp₁.tailRing from rfl,
          show bp'.tbPhysBlk = bp₁.tbPhysBlk from rfl,
          show bp'.blkMeta2 = bp₁.blkMeta2 from rfl,
          show bp'.blkTag = bp₁.blkTag from rfl,
          show bp'.tailOwnerBkt = bp₁.tailOwnerBkt from rfl,
          show bp'.tailOwnerRing = bp₁.tailOwnerRing from rfl, hac']
        have hk_lt_old : k < bp₁.r b' := by
          by_cases hbe : b' = b
          · subst b'; rw [set1_self] at hk_lt; omega
          · rwa [set1_of_ne _ _ _ _ hbe] at hk_lt
        have htf := hv₁.tail_fwd b' hb' k hk_ge hk_lt_old
        dsimp only at htf
        obtain ⟨ha, hbl, hcm, hkd, hob, hor⟩ := htf
        set t' := bp₁.tailRing b' ((bp₁.head b' + k) % (6 * bp₁.K))
        set Pt := bp₁.tbPhysBlk (t' / bp₁.K)
        have hPt_le : Pt ≤ P_prev := by
          rcases hkd with ⟨_, hPlt | hoff_r⟩ | ⟨hPlt, _, _⟩
          · dsimp only [P_prev]; omega
          · rw [hrem0] at hoff_r; exact absurd hoff_r (Nat.not_lt_zero _)
          · dsimp only [P_prev]; omega
        refine ⟨ha, hPt_le, hcm, ?_, hob, hor⟩
        rcases hkd with ⟨h0, _⟩ | ⟨_, h2, hge_m⟩
        · refine Or.inl ⟨h0, ?_⟩
          by_cases hp_prev : Pt = P_prev
          · right
            have hloc'_lt : bp₁.q b' * bp₁.K + k < bp'.bktCount b' := by
              unfold bktCount
              dsimp only [bp', commitPopCase2, unresRemoveAt, freeTb]; omega
            have hp_lt := (htp_eq b' hb' (bp₁.q b' * bp₁.K + k) hloc'_lt).2
            change bp₁.toPhys b' (bp₁.q b' * bp₁.K + k) < bp₁.nSide - 1 at hp_lt
            unfold toPhys at hp_lt
            rw [ite_eq_right (by omega), Nat.add_sub_cancel_left,
              ite_eq_right (not_lt.mpr hk_ge)] at hp_lt
            unfold physOfTail at hp_lt
            have heff_p : bp₁.effBlk P_prev (t' % bp₁.K) = P_prev := by
              by_cases ha1 : bp₁.topSwapAct = 1
              · obtain ⟨hs2, hd2⟩ := hbal₁.low_swap ha1
                exact effBlk_eq_self_of_ne (by dsimp only [P_prev]; omega)
                  (by dsimp only [P_prev]; omega)
              · unfold effBlk; simp [ha1]
            change bp₁.effBlk Pt (t' % bp₁.K) * bp₁.K + t' % bp₁.K < bp₁.nSide - 1 at hp_lt
            rw [hp_prev, heff_p, hns_sub] at hp_lt; omega
          · exact Or.inl (by omega)
        · have hlow := hbal₁.low_blk Pt (by rw [h2]; decide)
          have hne_l : Pt ≠ P_last := fun he => by
            rw [he, hPl_tag0] at h2; exact absurd h2 (by decide)
          have hm1_Pt : bp'.blkMeta1 Pt = bp₁.blkMeta1 Pt := by
            dsimp only [bp', commitPopCase2, unresRemoveAt, freeTb]
            split_ifs
            · exact set1_of_ne _ _ _ _ hne_l
            · rfl
          rw [hm1_Pt]
          exact Or.inr ⟨by dsimp only [P_prev]; omega, h2, hge_m⟩
      tail_bwd := fun P hP_le off hoff hlt hor =>
        commitPopCase2_tail_bwd hbal₁ hb hcnt hn_pos htp_end hrem P hP_le off hoff hlt hor }
  have hdebt_bound : bp'.topDebt ≤ 16 * bp'.rem + 16 := by
    rw [hrem']
    have h3k := hcv'.topDebt_le_three_K
    have hK_eq : bp'.K = bp₁.K := rfl
    rw [hK_eq] at h3k; omega
  have hsi' : bp'.StepInv b 16 :=
    { core := hcv'
      bktCount_le := fun b' hb' => by
        change b' < bp₁.M at hb'
        change bp'.bktCount b' ≤ bp₁.maxSlabs * bp₁.K
        by_cases hbe : b' = b
        · subst b'; rw [hbc_b]; exact (Nat.sub_le _ 1).trans (hbal₁.bktCount_le b hb')
        · rw [hbc_ne b' hbe]; exact hbal₁.bktCount_le b' hb'
      t_le := le_rfl
      hyst_tick := fun _ => hh_b16 bp' rfl rfl rfl (set1_self _ _ _)
      hyst_other := fun b' hb' hne => by
        change b' < bp₁.M at hb'
        have hh' := hbal₁.hyst b' hb'
        unfold BktHyst at hh' ⊢
        rw [hac', show bp'.actCode b' = bp₁.actCode b' from rfl,
          show bp'.K = bp₁.K from rfl, show bp'.q b' = bp₁.q b' from rfl,
          show bp'.r b' = bp₁.r b' from set1_of_ne _ _ _ _ hne]
        exact hh'
      low_blk := fun P htag => by
        change bp₁.blkTag P ≠ 0 at htag
        rw [hBf']
        have hlow := hbal₁.low_blk P htag
        by_cases hge2 : 2 ≤ bp₁.B_full
        · have hne_m2 : P ≠ bp₁.B_full - 2 := fun he => by
            rw [he, (hclean2 hge2).1] at htag; exact htag rfl
          dsimp only [P_prev]; omega
        · omega
      low_swap := fun ha => by
        change bp₁.topSwapAct = 1 at ha
        rw [hBf']
        change bp₁.topSwapSrc + 2 ≤ P_prev ∧ bp₁.topSwapDst + 2 ≤ P_prev
        obtain ⟨hs2, hd2⟩ := hbal₁.low_swap ha
        by_cases hge2 : 2 ≤ bp₁.B_full
        · obtain ⟨hs_ne, hd_ne⟩ := (hclean2 hge2).2 ha
          dsimp only [P_prev]; exact ⟨by omega, by omega⟩
        · omega }
  exact ⟨hsi', rfl, rfl, rfl, hbc_b, hbc_ne, hdebt_bound, htp_eq⟩

/-- After `prepPopBktBack` has placed `(b, bp₁.bktCount b - 1)` at `bp₁.nSide - 1`,
`commitPopBktBack` shrinks `nSide` to `bp₁.nSide - 1`, establishes `StepInv b 16`, bounds
`topDebt ≤ 16 * rem + 16`, and preserves `toPhys` on all remaining `< bktCount'` items! -/
theorem Balanced.commitPopBktBack_spec {bp₁ : BlockPoolState} (hbal₁ : bp₁.Balanced)
    {b : ℕ} (hb : b < bp₁.M) (hcnt : 0 < bp₁.bktCount b) (hn_pos : 0 < bp₁.nSide)
    (htp_end : bp₁.toPhys b (bp₁.bktCount b - 1) = bp₁.nSide - 1) :
    let bp' := bp₁.commitPopBktBack b
    bp'.StepInv b 16 ∧
    bp'.M = bp₁.M ∧
    bp'.K = bp₁.K ∧
    bp'.nSide = bp₁.nSide - 1 ∧
    bp'.bktCount b = bp₁.bktCount b - 1 ∧
    (∀ b' ≠ b, bp'.bktCount b' = bp₁.bktCount b') ∧
    bp'.topDebt ≤ 16 * bp'.rem + 16 ∧
    (∀ b' < bp₁.M, ∀ loc' < bp'.bktCount b',
      bp'.toPhys b' loc' = bp₁.toPhys b' loc' ∧ bp'.toPhys b' loc' < bp₁.nSide - 1) := by
  dsimp only
  unfold commitPopBktBack
  by_cases hrem : 0 < bp₁.rem
  · rw [ite_eq_left hrem]
    exact commitPopCase1_spec hbal₁ hb hcnt hn_pos htp_end hrem
  · rw [ite_eq_right hrem]
    exact commitPopCase2_spec hbal₁ hb hcnt hn_pos htp_end hrem

/-- End-to-end `Balanced` theorem for `commitPopBktBack` followed by `16` `bktTickOne` steps and
`16` `topCleanOne` steps. -/
theorem Balanced.popBktBack_rebalance_balanced {α : Type*} {bp₁ : BlockPoolState}
    (hbal₁ : bp₁.Balanced) {b : ℕ} (hb : b < bp₁.M) (hcnt : 0 < bp₁.bktCount b)
    (hn_pos : 0 < bp₁.nSide) (htp_end : bp₁.toPhys b (bp₁.bktCount b - 1) = bp₁.nSide - 1)
    (arr : ℕ → α) :
    let st_bkt := runBktTicks b 16 (bp₁.commitPopBktBack b, arr)
    let res := runTopCleanTicks 16 st_bkt
    res.1.Balanced ∧
    res.1.nSide = bp₁.nSide - 1 ∧
    res.1.bktCount b = bp₁.bktCount b - 1 ∧
    (∀ b' ≠ b, res.1.bktCount b' = bp₁.bktCount b') ∧
    (∀ b' < bp₁.M, ∀ loc' < res.1.bktCount b',
      res.2 (res.1.toPhys b' loc') = arr (bp₁.toPhys b' loc')) := by
  obtain ⟨hsi0, hM0, hK0, hn0, hbc_b0, hbc_ne0, hdebt0, htp0⟩ :=
    hbal₁.commitPopBktBack_spec hb hcnt hn_pos htp_end
  have hb_spec := hsi0.runBktTicks_spec 16 (hM0.symm ▸ hb) arr
  set st_bkt := runBktTicks b 16 (bp₁.commitPopBktBack b, arr)
  set bp₂ := st_bkt.1
  set arr₂ := st_bkt.2
  obtain ⟨hsi₂, hM₂, hK₂, hn₂, hbc₂, hdebt₂, harr₂⟩ := hb_spec
  have hc_spec := hsi₂.runTopCleanTicks_spec 16 arr₂
  set res := runTopCleanTicks 16 st_bkt
  set bp' := res.1
  set arr' := res.2
  obtain ⟨hsi', hM', hK', hn', hbc', hdebt', harr'⟩ := hc_spec
  have hrem_eq : bp'.rem = (bp₁.commitPopBktBack b).rem := by
    dsimp only [rem]; rw [hn', hn₂, hK', hK₂]
  have hbal' : bp'.Balanced :=
    { core := hsi'.core
      bktCount_le := hsi'.bktCount_le
      hyst := fun b' hb' => by
        by_cases hbe : b' = b
        · subst b'; exact hsi'.hyst_tick hb'
        · exact hsi'.hyst_other b' hb' hbe
      low_blk := hsi'.low_blk
      low_swap := hsi'.low_swap
      debt_le := by
        rw [hrem_eq, hdebt']
        have := hdebt₂.trans hdebt0
        omega }
  refine ⟨hbal', hn'.trans (hn₂.trans hn0), (hbc' b).trans ((hbc₂ b).trans hbc_b0),
    fun b' hne => (hbc' b').trans ((hbc₂ b').trans (hbc_ne0 b' hne)),
    fun b' hb' loc' hloc' => ?_⟩
  have hloc2 : loc' < bp₂.bktCount b' := by rw [← hbc' b']; exact hloc'
  have hloc0 : loc' < (bp₁.commitPopBktBack b).bktCount b' := by rw [← hbc₂ b']; exact hloc2
  exact (harr' b' (hM₂.symm ▸ hM0.symm ▸ hb') loc' hloc2).trans
    ((harr₂ b' (hM0.symm ▸ hb') loc' hloc0).trans (congrArg arr (htp0 b' hb' loc' hloc0).1))

end BlockPoolState

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

end
