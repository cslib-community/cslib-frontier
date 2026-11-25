/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpoch
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Window Bridge, `SlotIoLayout` Switching, and Batched Random Seed Sampling (`DualEpochWindow`)

This module supplies four reusable building blocks connecting the per-epoch `Memory.Prog` layer
(`LargeEpoch.lean`) to the 12-phase deamortized dual-epoch state machine (`DualEpochExec.lean`) for
the resizable succinct dynamic dictionary
([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024]):

1. **Deterministic event-log to `EpochWindowSpec` bridge (`EpochUpdate`, `windowOfEvents`):**
   Turns any fixed sequence `evs : List (EpochUpdate U V)` (`insert` / `delete`) of length `≤ 4 * N`
   staying at live size `≤ N` into an `EpochWindowSpec c U N` whose sub-epoch batches partition the
   new-key insertions by `qEpochWhp N`.
2. **Lossless `SlotIoLayout` transport (`transfer_io` lemmas):**
   Proves that changing a `SmallEpochLayout`, `FallbackLayout`, `FastEpochLayout`, or
   `FastSubEpochGood` layout's `io : SlotIoLayout` (e.g., direct ↔ `SplitPair` ↔ paged `PageUnperm`)
   while leaving epoch metadata intact and preserving `slotIoPairAt` on `[0, nSide)` preserves every
   semantic and good-seed invariant (`SmallEpochLayout.StateInv`, `FallbackLayout.StateInv`,
   `FastEpochInvGen`, `FastSubEpochGood`, `LargeEpochInv`, `CurBufKeysIn`).
3. **Band-stable `PagePairState` initialization (`pagePairInitBand`):**
   Generalizes `PagePairState.initFromSrc` across any `(q₀, r_cur)` satisfying `5 * B ≤ 4 * r_cur ≤
   11 * B` so incremental `pageInitTailBatchProg` finishes directly at a `WellBalanced` state even
   under concurrent inserts/deletes during tail initialization (paired with `unpermRank` Lyapunov
   decay in `DualEpochSchedule.lean`).
4. **Incremental `RInstr.rand` word-fill batch (`randFillBatchCode`):**
   Parameterized batch loop over `RCode .exact r` (`¬ReadsWidth`, `ExecRCodeSteps`) sampling
   consecutive ranges of uniform `w`-bit words and gluing them into exact
   `PMF.uniformOfFintype (EpochHashSeeds c U N)` via `BitPackedDoubleTabulation`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.EpochUpdate`, `windowOfEvents`
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.randFillBatchCode`

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

open scoped BigOperators ENNReal

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM.Resizable.Randomized
open Cslib.Probability
open Finset

/-! ## Section 1: Pure `EpochUpdate` Log to `EpochWindowSpec` -/

/-- `qEpochWhp N = (slabScale N) ^ 18` is at least `4` for every `N`. -/
theorem four_le_qEpochWhp (N : ℕ) : 4 ≤ qEpochWhp N := by
  have hL : 2 ≤ slabScale N :=
    (show 2 = 2 ^ 1 from rfl) ▸
      Nat.pow_le_pow_right (by decide) (Dynamic.one_le_logLogFactor N)
  calc 4 = 2 ^ 2 := by decide
    _ ≤ 2 ^ 18 := Nat.pow_le_pow_right (by decide) (by decide)
    _ ≤ slabScale N ^ 18 := Nat.pow_le_pow_left hL 18

/-- Above the WHP threshold, `2 * qEpochWhp N ≤ N`. -/
theorem two_mul_qEpochWhp_le {c N : ℕ} (hth : whpThreshold c ≤ N) :
    2 * qEpochWhp N ≤ N := by
  have hlog : 320 * Dynamic.logLogFactor N ≤ bCharWhp N :=
    (Nat.mul_le_mul_right _ (le_codeExpWhp c)).trans (codeExpWhp_mul_ell_le_bCharWhp hth)
  have hln : 1280 * Dynamic.logLogFactor N ≤ Nat.log 2 N := by
    unfold bCharWhp at hlog; omega
  have hell : 1 ≤ Dynamic.logLogFactor N := Dynamic.one_le_logLogFactor N
  have hN0 : N ≠ 0 := by have := whpThreshold_pos c; omega
  have hexp : 18 * Dynamic.logLogFactor N + 1 ≤ Nat.log 2 N := by omega
  calc 2 * qEpochWhp N
      = 2 * (2 ^ Dynamic.logLogFactor N) ^ 18 := rfl
    _ = 2 ^ (18 * Dynamic.logLogFactor N + 1) := by
        rw [← Nat.pow_mul, Nat.mul_comm (Dynamic.logLogFactor N) 18, Nat.pow_succ']
    _ ≤ 2 ^ Nat.log 2 N := Nat.pow_le_pow_right (by decide) hexp
    _ ≤ N := Nat.pow_log_le_self 2 hN0

/-- Basic epoch-level mutation event tracked for building `EpochWindowSpec`. -/
inductive EpochUpdate (U V : ℕ) where
  /-- Insert or overwrite `(u, v)`. -/
  | insert (u : Fin U) (v : Fin V)
  /-- Delete `u` (no-op if absent). -/
  | delete (u : Fin U)

namespace EpochUpdate

/-- Target key touched by an `EpochUpdate`. -/
@[expose] def key {U V : ℕ} : EpochUpdate U V → Fin U
  | insert u _ => u
  | delete u => u

/-- Single-step update of an abstract dictionary map `s : Fin U → Option (Fin V)`. -/
@[expose] def apply {U V : ℕ} (s : Fin U → Option (Fin V)) :
    EpochUpdate U V → Fin U → Option (Fin V)
  | insert u v => Function.update s u (some v)
  | delete u => Function.update s u none

/-- Replay a list of updates starting from the empty dictionary `fun _ => none`. -/
@[expose] def eval {U V : ℕ} (evs : List (EpochUpdate U V)) : Fin U → Option (Fin V) :=
  evs.foldl apply (fun _ => none)

/-- Live domain `Finset` of `s : Fin U → Option (Fin V)`. -/
@[expose] noncomputable def liveDom {U V : ℕ} (s : Fin U → Option (Fin V)) : Finset (Fin U) := by
  classical exact Finset.univ.filter fun u => s u ≠ none

@[simp] theorem eval_nil (U V : ℕ) : eval (U := U) (V := V) [] = fun _ => none := rfl

theorem eval_append_singleton {U V : ℕ} (evs : List (EpochUpdate U V)) (e : EpochUpdate U V) :
    eval (evs ++ [e]) = apply (eval evs) e := by
  unfold eval; simp [List.foldl_append]

theorem eval_take_succ {U V : ℕ} {evs : List (EpochUpdate U V)} {k : ℕ} (hk : k < evs.length) :
    eval (evs.take (k + 1)) = apply (eval (evs.take k)) evs[k] := by
  rw [List.take_succ_eq_append_getElem hk, eval_append_singleton]

theorem mem_liveDom_iff {U V : ℕ} (s : Fin U → Option (Fin V)) (u : Fin U) :
    u ∈ liveDom s ↔ s u ≠ none := by
  classical simp [liveDom]

/-- Indicator `true` iff step `k` of `evs` is a fresh-key insertion (`eval (evs.take k) u = none`).
-/
@[expose] noncomputable def isFreshAt {U V : ℕ} (evs : List (EpochUpdate U V)) (k : ℕ) : Bool := by
  classical
  exact if hk : k < evs.length then
    match evs[k] with
    | insert u _ => decide (eval (evs.take k) u = none)
    | delete _ => false
  else false

/-- Number of fresh-key insertions strictly before step `k` in `evs`. -/
@[expose] noncomputable def freshCount {U V : ℕ} (evs : List (EpochUpdate U V)) (k : ℕ) : ℕ :=
  ((Finset.range k).filter fun i => isFreshAt evs i = true).card

theorem freshCount_zero {U V : ℕ} (evs : List (EpochUpdate U V)) : freshCount evs 0 = 0 := by
  simp [freshCount]

theorem freshCount_succ {U V : ℕ} (evs : List (EpochUpdate U V)) (k : ℕ) :
    freshCount evs (k + 1) = freshCount evs k + if isFreshAt evs k = true then 1 else 0 := by
  unfold freshCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem freshCount_mono {U V : ℕ} (evs : List (EpochUpdate U V)) {a b : ℕ} (hab : a ≤ b) :
    freshCount evs a ≤ freshCount evs b := by
  unfold freshCount
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hab))

theorem freshCount_le {U V : ℕ} (evs : List (EpochUpdate U V)) (k : ℕ) :
    freshCount evs k ≤ k := by
  calc freshCount evs k ≤ (Finset.range k).card := Finset.card_filter_le _ _
    _ = k := Finset.card_range k

private lemma card_freshBucket_le {U V : ℕ} (evs : List (EpochUpdate U V)) {Q : ℕ}
    (hQ : 0 < Q) (e : ℕ) :
    ((Finset.range evs.length).filter
      fun i => isFreshAt evs i = true ∧ freshCount evs i / Q = e).card ≤ Q := by
  let S := (Finset.range evs.length).filter
    fun i => isFreshAt evs i = true ∧ freshCount evs i / Q = e
  have hinj : Set.InjOn (fun i => freshCount evs i % Q) (S : Set ℕ) := by
    intro i hi j hj heq
    simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_range] at hi hj
    have hmod : freshCount evs i % Q = freshCount evs j % Q := heq
    have hsame : freshCount evs i = freshCount evs j := by
      have hi_d := Nat.div_add_mod (freshCount evs i) Q
      have hj_d := Nat.div_add_mod (freshCount evs j) Q
      rw [← hi_d, ← hj_d, hi.2.2, hj.2.2, hmod]
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · have hst := freshCount_succ evs i
      have hmo := freshCount_mono evs (show i + 1 ≤ j by omega)
      rw [ite_eq_left hi.2.1] at hst; omega
    · rfl
    · have hst := freshCount_succ evs j
      have hmo := freshCount_mono evs (show j + 1 ≤ i by omega)
      rw [ite_eq_left hj.2.1] at hst; omega
  calc S.card
      ≤ (Finset.range Q).card :=
        Finset.card_le_card_of_injOn (fun i => freshCount evs i % Q)
          (fun _ _ => by simp only [Finset.mem_coe, Finset.mem_range]; exact Nat.mod_lt _ hQ)
          hinj
    _ = Q := Finset.card_range Q

/-- `Finset` of keys freshly inserted during sub-epoch index `e` (`freshCount evs i / Q = e`). -/
@[expose] noncomputable def freshBatch {U V : ℕ} (evs : List (EpochUpdate U V))
    (Q e : ℕ) : Finset (Fin U) := by
  classical
  exact (Finset.univ.filter fun i : Fin evs.length =>
    isFreshAt evs i.val = true ∧ freshCount evs i.val / Q = e).image fun i => evs[i.val].key

private theorem card_freshBatch_le {U V : ℕ} (evs : List (EpochUpdate U V))
    {Q : ℕ} (hQ : 0 < Q) (e : ℕ) :
    (freshBatch evs Q e).card ≤ Q := by
  classical
  refine Finset.card_image_le.trans ?_
  let S_fin : Finset (Fin evs.length) := Finset.univ.filter fun i =>
    isFreshAt evs i.val = true ∧ freshCount evs i.val / Q = e
  let S_nat : Finset ℕ := (Finset.range evs.length).filter fun i =>
    isFreshAt evs i = true ∧ freshCount evs i / Q = e
  have hle : S_fin.card ≤ S_nat.card :=
    Finset.card_le_card_of_injOn Fin.val
      (fun i hi => by
        simp only [S_fin, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp only [S_nat, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
        exact ⟨i.isLt, hi⟩)
      (fun _ _ _ _ h => Fin.ext h)
  exact hle.trans (card_freshBucket_le evs hQ e)

/-- Earliest prefix index `k ≤ evs.length` with `e * Q ≤ freshCount evs k` (or `evs.length`). -/
@[expose] noncomputable def subStart {U V : ℕ} (evs : List (EpochUpdate U V))
    (Q e : ℕ) : ℕ := by
  classical
  exact if h : ∃ k ≤ evs.length, e * Q ≤ freshCount evs k then
    Nat.find h
  else
    evs.length

private theorem subStart_le_len {U V : ℕ} (evs : List (EpochUpdate U V)) (Q e : ℕ) :
    subStart evs Q e ≤ evs.length := by
  classical
  unfold subStart
  split_ifs with h
  · exact (Nat.find_spec h).1
  · exact le_rfl

private theorem subStart_le_of_eq {U V : ℕ} {evs : List (EpochUpdate U V)} {Q k : ℕ}
    (hk : k ≤ evs.length) :
    subStart evs Q (freshCount evs k / Q) ≤ k := by
  classical
  have hm : (freshCount evs k / Q) * Q ≤ freshCount evs k := by
    rw [Nat.mul_comm]; exact Nat.mul_div_le _ _
  have hex : ∃ j ≤ evs.length, freshCount evs k / Q * Q ≤ freshCount evs j := ⟨k, hk, hm⟩
  unfold subStart
  rw [dite_eq_left hex]
  exact Nat.find_min' hex ⟨hk, hm⟩

private theorem subStart_fresh_div {U V : ℕ} {evs : List (EpochUpdate U V)} {Q i e : ℕ}
    (hQ : 0 < Q) (hi_lo : subStart evs Q e ≤ i) (hi_hi : i < evs.length)
    (hle : freshCount evs i / Q ≤ e) :
    freshCount evs i / Q = e := by
  classical
  by_cases hex : ∃ k ≤ evs.length, e * Q ≤ freshCount evs k
  · have hge : e * Q ≤ freshCount evs (subStart evs Q e) := by
      unfold subStart; rw [dite_eq_left hex]; exact (Nat.find_spec hex).2
    have hmo := freshCount_mono evs hi_lo
    have hdiv : e ≤ freshCount evs i / Q := by
      rw [Nat.le_div_iff_mul_le hQ]; omega
    omega
  · unfold subStart at hi_lo; rw [dite_eq_right hex] at hi_lo; omega

theorem liveDom_take_subset_subStart_union {U V : ℕ} (evs : List (EpochUpdate U V))
    {Q k : ℕ} (hQ : 0 < Q) (hk : k ≤ evs.length) :
    liveDom (eval (evs.take k)) ⊆
      liveDom (eval (evs.take (subStart evs Q (freshCount evs k / Q)))) ∪
        freshBatch evs Q (freshCount evs k / Q) := by
  classical
  set e := freshCount evs k / Q
  set s₀ := subStart evs Q e
  have hs₀ : s₀ ≤ k := subStart_le_of_eq hk
  intro u hu
  rw [mem_liveDom_iff] at hu
  have haux : ∀ j, s₀ ≤ j → j ≤ k → eval (evs.take j) u ≠ none →
      u ∈ liveDom (eval (evs.take s₀)) ∪ freshBatch evs Q e := by
    intro j hj_lo hj_hi hne
    induction j with
    | zero =>
      have hs0 : s₀ = 0 := by omega
      rw [hs0]; exact Finset.mem_union_left _ ((mem_liveDom_iff _ _).mpr hne)
    | succ m ih =>
      by_cases hsm : s₀ = m + 1
      · rw [hsm]; exact Finset.mem_union_left _ ((mem_liveDom_iff _ _).mpr hne)
      · have hm_lt : m < evs.length := by omega
        rw [eval_take_succ hm_lt] at hne
        cases hm_ev : evs[m] with
        | delete u' =>
          rw [hm_ev] at hne; dsimp only [apply] at hne
          by_cases heq : u = u'
          · subst heq; simp at hne
          · rw [Function.update_of_ne heq] at hne
            exact ih (by omega) (by omega) hne
        | insert u' v' =>
          rw [hm_ev] at hne; dsimp only [apply] at hne
          by_cases heq : u = u'
          · subst heq
            by_cases hprev : eval (evs.take m) u = none
            · refine Finset.mem_union_right _ ?_
              unfold freshBatch; rw [Finset.mem_image]
              have hdiv_le : freshCount evs m / Q ≤ e :=
                Nat.div_le_div_right (freshCount_mono evs (by omega))
              have hfr_eq : isFreshAt evs m = true := by
                unfold isFreshAt; rw [dite_eq_left hm_lt, hm_ev]; simp [hprev]
              refine ⟨⟨m, hm_lt⟩, ?_, by simp [hm_ev, key]⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hfr_eq, subStart_fresh_div hQ (by omega) hm_lt hdiv_le⟩
            · exact ih (by omega) (by omega) hprev
          · rw [Function.update_of_ne heq] at hne
            exact ih (by omega) (by omega) hne
  exact haux k hs₀ le_rfl hu

theorem eval_take_mem_allKeys {U V : ℕ} (evs : List (EpochUpdate U V))
    {k : ℕ} (hk : k ≤ evs.length) {u : Fin U} (hu : eval (evs.take k) u ≠ none) :
    ∃ i : Fin evs.length, evs[i.val].key = u := by
  induction k with
  | zero => simp at hu
  | succ m ih =>
    have hm : m < evs.length := by omega
    rw [eval_take_succ hm] at hu
    cases he : evs[m] with
    | delete u' =>
      rw [he] at hu; dsimp only [apply] at hu
      by_cases heq : u = u'
      · subst heq; simp at hu
      · rw [Function.update_of_ne heq] at hu; exact ih (by omega) hu
    | insert u' v' =>
      rw [he] at hu; dsimp only [apply] at hu
      by_cases heq : u = u'
      · subst heq; exact ⟨⟨m, hm⟩, by simp [he, key]⟩
      · rw [Function.update_of_ne heq] at hu; exact ih (by omega) hu

/-- Build an oblivious `EpochWindowSpec c U N` from any deterministic update log `evs` of length
`≤ 4 * N` whose live dictionary size stays `≤ N` at every prefix. -/
@[expose] noncomputable def windowOfEvents {c U V N : ℕ}
    (hth : whpThreshold c ≤ N) (evs : List (EpochUpdate U V))
    (hlen : evs.length ≤ 4 * N)
    (hcard : ∀ k ≤ evs.length, (liveDom (eval (evs.take k))).card ≤ N) :
    EpochWindowSpec c U N := by
  classical
  let Q := qEpochWhp N
  have hQ4 : 4 ≤ Q := four_le_qEpochWhp N
  have hQpos : 0 < Q := by omega
  have h2Q : 2 * Q ≤ N := two_mul_qEpochWhp_le hth
  let allK : Finset (Fin U) := Finset.univ.image fun i : Fin evs.length => (evs.get i).key
  let numS : ℕ := evs.length / Q + 2
  have hsub_all_live : ∀ k ≤ evs.length, liveDom (eval (evs.take k)) ⊆ allK := by
    intro k hk u hu
    rw [mem_liveDom_iff] at hu
    obtain ⟨i, hi⟩ := eval_take_mem_allKeys evs hk hu
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  have hsub_all_batch : ∀ e, freshBatch evs Q e ⊆ allK := by
    intro e u hu
    unfold freshBatch at hu
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  exact
    { allKeys := allK
      numSnaps := evs.length + 1
      snaps := fun t => liveDom (eval (evs.take t.val))
      numSubs := numS
      subUnions := fun e =>
        liveDom (eval (evs.take (subStart evs Q e.val))) ∪
          freshBatch evs Q e.val ∪
          (if e.val = 0 then ∅ else freshBatch evs Q (e.val - 1))
      subBatches := fun e => if e.val = 0 then ∅ else freshBatch evs Q (e.val - 1)
      card_allKeys_le := by
        calc allK.card ≤ (Finset.univ : Finset (Fin evs.length)).card := Finset.card_image_le
          _ = evs.length := Fintype.card_fin _
          _ ≤ 8 * N := by omega
      numSnaps_le := by omega
      snap_sub := fun t => hsub_all_live t.val (Nat.lt_succ_iff.mp t.isLt)
      card_snap_le := fun t => hcard t.val (Nat.lt_succ_iff.mp t.isLt)
      numSubs_le := by
        have hdiv : evs.length / Q ≤ N := by
          rw [Nat.div_le_iff_le_mul_add_pred hQpos]
          nlinarith
        have hN_pos : 1 ≤ N := by have := whpThreshold_pos c; omega
        dsimp only [numS]; omega
      subUnion_sub := fun e => by
        refine Finset.union_subset (Finset.union_subset ?_ (hsub_all_batch e.val)) ?_
        · exact hsub_all_live _ (subStart_le_len evs Q e.val)
        · split_ifs
          · exact Finset.empty_subset _
          · exact hsub_all_batch (e.val - 1)
      card_subUnion_le := fun e => by
        have h1 : (liveDom (eval (evs.take (subStart evs Q e.val)))).card ≤ N :=
          hcard _ (subStart_le_len evs Q e.val)
        have h2 : (freshBatch evs Q e.val).card ≤ Q := card_freshBatch_le evs hQpos e.val
        have h3 : (if e.val = 0 then (∅ : Finset (Fin U)) else
            freshBatch evs Q (e.val - 1)).card ≤ Q := by
          split_ifs
          · simp
          · exact card_freshBatch_le evs hQpos (e.val - 1)
        calc (liveDom _ ∪ freshBatch evs Q e.val ∪ _).card
            ≤ (liveDom _ ∪ freshBatch evs Q e.val).card +
                (if e.val = 0 then (∅ : Finset (Fin U)) else freshBatch evs Q (e.val - 1)).card :=
              Finset.card_union_le _ _
          _ ≤ (liveDom _).card + (freshBatch evs Q e.val).card +
                (if e.val = 0 then (∅ : Finset (Fin U)) else freshBatch evs Q (e.val - 1)).card :=
              Nat.add_le_add_right (Finset.card_union_le _ _) _
          _ ≤ N + Q + Q := by omega
          _ ≤ 2 * N := by omega
      subBatch_sub := fun _ => Finset.subset_union_right
      card_subBatch_le := fun e => by
        split_ifs
        · simp
        · exact card_freshBatch_le evs hQpos (e.val - 1) }

@[simp] theorem windowOfEvents_numSubs {c U V N : ℕ}
    (hth : whpThreshold c ≤ N) (evs : List (EpochUpdate U V))
    (hlen : evs.length ≤ 4 * N)
    (hcard : ∀ k ≤ evs.length, (liveDom (eval (evs.take k))).card ≤ N) :
    (windowOfEvents hth evs hlen hcard).numSubs = evs.length / qEpochWhp N + 2 := rfl

theorem mem_subUnion_windowOfEvents {c U V N : ℕ}
    (hth : whpThreshold c ≤ N) {evs : List (EpochUpdate U V)}
    (hlen : evs.length ≤ 4 * N)
    (hcard : ∀ k ≤ evs.length, (liveDom (eval (evs.take k))).card ≤ N)
    {k : ℕ} (hk : k < evs.length) {u : Fin U} {v : Fin V}
    (hev : evs[k] = insert u v) :
    let eVal := freshCount evs k / qEpochWhp N
    have heLt : eVal < (windowOfEvents hth evs hlen hcard).numSubs := by
      rw [windowOfEvents_numSubs]
      have hfr := freshCount_le evs k
      have : eVal ≤ evs.length / qEpochWhp N := Nat.div_le_div_right (by omega)
      omega
    u ∈ (windowOfEvents hth evs hlen hcard).subUnions ⟨eVal, heLt⟩ := by
  classical
  dsimp only
  have hQpos : 0 < qEpochWhp N := by have := four_le_qEpochWhp N; omega
  change u ∈
    liveDom (eval (evs.take (subStart evs (qEpochWhp N) (freshCount evs k / qEpochWhp N)))) ∪
      freshBatch evs (qEpochWhp N) (freshCount evs k / qEpochWhp N) ∪
      (if freshCount evs k / qEpochWhp N = 0 then ∅
       else freshBatch evs (qEpochWhp N) (freshCount evs k / qEpochWhp N - 1))
  by_cases hprev : eval (evs.take k) u = none
  · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
    unfold freshBatch
    rw [Finset.mem_image]
    have hfr : isFreshAt evs k = true := by
      unfold isFreshAt; rw [dite_eq_left hk, hev]; simp [hprev]
    exact ⟨⟨k, hk⟩, by simp [hfr], by simp [hev, key]⟩
  · have hmem : u ∈ liveDom (eval (evs.take k)) := (mem_liveDom_iff _ _).mpr hprev
    exact Finset.mem_union_left _ (liveDom_take_subset_subStart_union evs hQpos hk.le hmem)

theorem curBatch_subset_freshBatch {U V : ℕ} (evs : List (EpochUpdate U V))
    {Q k e : ℕ} (hk : k ≤ evs.length)
    {i : ℕ} (hi_lt : i < k) (hfr : isFreshAt evs i = true)
    (hi_div : freshCount evs i / Q = e) :
    (evs[i]'(hi_lt.trans_le hk)).key ∈ freshBatch evs Q e := by
  classical
  unfold freshBatch; rw [Finset.mem_image]
  exact ⟨⟨i, hi_lt.trans_le hk⟩, by simp [hfr, hi_div], rfl⟩

end EpochUpdate

/-! ## Section 2: `SlotIoLayout` Invariant Transport (`transfer_io`) -/

/-- Replace the `io : SlotIoLayout` field of a `SmallEpochLayout` while preserving its header
metadata and virtual pair values `[0, nSide)`. -/
theorem SmallEpochLayout.StateInv.transfer_io {L₁ : SmallEpochLayout} {io₂ : SlotIoLayout}
    {slack₁ slack₂ : ℕ} {m₁ m₂ : ℕ → ℕ} {s_abs : Fin L₁.U → Option (Fin L₁.V)}
    (hinv : L₁.StateInv slack₁ m₁ s_abs)
    (hm0 : m₂ L₁.metaBase = m₁ L₁.metaBase)
    (hm1 : m₂ (L₁.metaBase + 1) = m₁ (L₁.metaBase + 1))
    (hio₂ : io₂.StateInv (m₁ (L₁.metaBase + 1)) slack₂ m₂)
    (hcap : m₁ (L₁.metaBase + 1) ≤ io₂.pgL.nCap)
    (hpair : ∀ p < m₁ (L₁.metaBase + 1), slotIoPairAt io₂ m₂ p = slotIoPairAt L₁.io m₁ p) :
    ({ L₁ with io := io₂ } : SmallEpochLayout).StateInv slack₂ m₂ s_abs := by
  obtain ⟨h0, _, _, href⟩ := hinv
  refine ⟨hm0.trans h0, hm1 ▸ hcap, hm1 ▸ hio₂, ?_⟩
  rw [hm1]; exact href.congr (fun _ _ => rfl) hpair

/-- Non-page metadata word-interval predicate `[metaBase, metaBase + 18) ∪
[metaBase + 32, metaBase + offPageDir c w N)` (excluding `PageUnpermState` scalars `[18, 32)`). -/
@[expose] def OwnsEpochNonPageMeta (c w N metaBase addr : ℕ) : Prop :=
  (metaBase ≤ addr ∧ addr < metaBase + 18) ∨
  (metaBase + 32 ≤ addr ∧ addr < metaBase + offPageDir c w N)

/-- Transport `FallbackLayout.StateInv` to a different `SlotIoLayout` sharing the same metadata and
virtual `(quot, val)` pairs `[0, nSide)`. -/
theorem FallbackLayout.StateInv.transfer_io {fl : FallbackLayout} {io₂ : SlotIoLayout}
    {w slack₁ slack₂ : ℕ} {θ_bkt : BktSeed fl.c fl.U fl.N} {m₁ m₂ : ℕ → ℕ}
    {s_abs : Fin fl.U → Option (Fin fl.V)}
    (hmv : fl.bpL.mp.Valid w (fl.bpL.mp.metaBase + epochMetaWordsWhp fl.c fl.bpL.mp.w fl.N))
    (hinv : fl.StateInv slack₁ θ_bkt m₁ s_abs)
    (hm_meta : ∀ a, OwnsEpochNonPageMeta fl.c fl.bpL.mp.w fl.N fl.bpL.mp.metaBase a → m₂ a = m₁ a)
    (hmp_eq : fl.bpL.mp = epochBpMetaLayout fl.c fl.bpL.mp.w fl.N fl.bpL.mp.metaBase)
    (hio₂ : io₂.StateInv (extractFallback fl.bpL.mp m₁).nSide slack₂ m₂)
    (hpair : ∀ p < (extractFallback fl.bpL.mp m₁).nSide,
      slotIoPairAt io₂ m₂ p = slotIoPairAt fl.bpL.io m₁ p) :
    ({ fl with bpL := { fl.bpL with io := io₂ } } : FallbackLayout).StateInv slack₂ θ_bkt m₂
      s_abs := by
  have hfb_eq : extractFallback fl.bpL.mp m₂ = extractFallback fl.bpL.mp m₁ := by
    have hobm := hmv.offBktMeta_ge
    refine extractFallback_congr hmv.w_pos fun a ha => hm_meta a ?_
    rcases BpMetaLayout.OwnsMetaAddr.bounds hmv ha with (rfl | ⟨h1, h2⟩) | ⟨h1, h2⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · refine Or.inr ⟨by omega, ?_⟩
      have hle : fl.bpL.mp.offTailOwner + packedWords (16 * fl.bpL.mp.maxTail)
          fl.bpL.mp.ptrB fl.bpL.mp.w ≤ offPageDir fl.c fl.bpL.mp.w fl.N := by
        rw [hmp_eq]
        dsimp only [epochBpMetaLayout]
        unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
          offBTreeMeta offTailOwner
        omega
      omega
  have hseed : BitPackedDoubleTabulation.SeedRep (fl.bpL.mp.metaBase + offBktHash) fl.bpL.mp.w
      (redWidthWhp fl.U) (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) θ_bkt m₂ :=
    hinv.seed_bkt.congr_on hmv.w_pos fun a h1 h2' => hm_meta a (Or.inr ⟨by
      unfold offBktHash at h1; omega, by
      unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
        offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir offBktMeta offFpHash at *
      omega⟩)
  refine
    { hdr_N := (hm_meta fl.bpL.mp.metaBase (Or.inl ⟨le_rfl, by omega⟩)).trans hinv.hdr_N
      mode_eq := (hm_meta (fl.bpL.mp.metaBase + 2) (Or.inl ⟨by omega, by omega⟩)).trans hinv.mode_eq
      seed_bkt := hseed
      fb_valid := hfb_eq ▸ hinv.fb_valid
      nSide_le := by rw [hfb_eq]; exact hinv.nSide_le
      io_inv := by rw [hfb_eq]; exact hio₂
      refines := by
        rw [hfb_eq]
        exact hinv.refines.congr (fun _ _ => rfl) hpair }

private lemma offPageDir_bounds (c w N : ℕ) :
    32 ≤ offBktHash ∧
    offBktHash + BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp N)
      (bWhp N) = offFpHash c w N ∧
    offFpHash c w N + BitPackedDoubleTabulation.space w (cTabWhp c) (dTabWhp c) (bCharWhp N)
      (fpBitsWhp N) = offBktMeta c w N ∧
    offBktMeta c w N + packedWords (16 * numBucketsWhp N) (globalPtrBits N) w =
      offSlabDir c w N ∧
    offSlabDir c w N ≤ offTailOwner c w N ∧
    offTailOwner c w N + packedWords (16 * maxTailWhp N) (globalPtrBits N) w =
      offBTreeMeta c w N ∧
    offBTreeMeta c w N + packedWords (totalBTreeNodesWhp N) (nodeMetaBitsWhp N) w =
      offBTreeKeys c w N ∧
    offBTreeKeys c w N + packedWords (totalBTreeNodesWhp N) (keysWordBitsWhp N) w =
      offBTreeVals c w N ∧
    offBTreeVals c w N + packedWords (totalBTreeNodesWhp N) (valsWordBitsWhp N) w =
      offTrieChild c w N 0 ∧
    offTrieChild c w N 0 ≤ offTrieChild c w N 1 ∧
    offTrieChild c w N 1 + packedWords (maxTrieNodesWhp c N * 2 ^ bCharWhp N)
      (globalPtrBits N) w ≤ offTrieNode c w N 0 ∧
    offTrieNode c w N 0 ≤ offTrieNode c w N 1 ∧
    offTrieNode c w N 1 + packedWords (6 * maxTrieNodesWhp c N) (globalPtrBits N) w ≤
      offTrieItem c w N 0 ∧
    offTrieItem c w N 0 ≤ offTrieItem c w N 1 ∧
    offTrieItem c w N 1 + packedWords (6 * qEpochWhp N + 6) (globalPtrBits N) w ≤
      offPageDir c w N := by
  refine ⟨le_rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold offTailOwner offSlabOwner offTailDir; omega
  · unfold offTrieChild; simp
  · unfold offTrieChild; simp
  · unfold offTrieNode offTrieChild trieChildWords; omega
  · unfold offTrieNode; simp
  · unfold offTrieItem offTrieNode trieNodeWords; omega
  · unfold offTrieItem; simp
  · unfold offPageDir offTrieItem trieItemWords; omega

private theorem fastEpoch_meta_eq_of_region {fl : FastEpochLayout} {w fr : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hv : fl.Valid w fr)
    (hm : ∀ a, OwnsEpochNonPageMeta fl.c fl.w fl.N fl.metaBase a → m₂ a = m₁ a) :
    extractBlockPool fl.mp m₂ = extractBlockPool fl.mp m₁ ∧
    extractFastMeta fl m₂ = extractFastMeta fl m₁ ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) m₂ = extractBufTrie (fl.trieL r) m₁) ∧
    (∀ b < numBucketsWhp fl.N, ∀ role < 3,
      extractBTreeSlice fl.btL b role m₂ = extractBTreeSlice fl.btL b role m₁) := by
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  have hmv : fl.mp.Valid w fr := hv.mp_valid
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14⟩ :=
    offPageDir_bounds fl.c fl.w fl.N
  have hbm_eq : ∀ idx < 16 * numBucketsWhp fl.N,
      readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w m₂ idx =
        readPacked (fl.metaBase + offBktMeta fl.c fl.w fl.N) (globalPtrBits fl.N) fl.w m₁ idx :=
    fun idx hidx =>
      readPacked_congr hw_pos (fun a ⟨h1, h2⟩ => hm a (Or.inr ⟨by omega, by omega⟩)) hidx
  have hmt : fl.mp.M * fl.mp.K ≤ fl.mp.maxTail := by
    dsimp only [FastEpochLayout.mp, epochBpMetaLayout, maxTailWhp]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine extractBlockPool_congr hw_pos hmv.K_ge hmt fun a ha => ?_
    rcases BpMetaLayout.OwnsMetaAddr.bounds hmv ha with (rfl | ⟨h1, h2⟩) | ⟨h1, h2⟩ <;>
      dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at *
    · exact hm _ (Or.inl ⟨by omega, by omega⟩)
    · exact hm _ (Or.inl ⟨by omega, by omega⟩)
    · exact hm _ (Or.inr ⟨by omega, by omega⟩)
  · have hm_lt : ∀ k < 18, m₂ (fl.metaBase + k) = m₁ (fl.metaBase + k) := fun k hk =>
      hm _ (Or.inl ⟨Nat.le_add_right _ _, by omega⟩)
    unfold extractFastMeta
    congr 1
    · exact hm_lt 3 (by decide)
    · exact hm_lt 4 (by decide)
    · exact hm_lt 5 (by decide)
    · exact hm_lt 6 (by decide)
    · exact hm_lt 7 (by decide)
    · exact hm_lt 8 (by decide)
    · exact hm_lt 9 (by decide)
    · exact hm_lt 17 (by decide)
    · funext b; by_cases hb : b < numBucketsWhp fl.N
      · simp only [hb, ↓reduceIte]; exact hbm_eq (16 * b + 5) (by omega)
      · simp only [hb, ↓reduceIte]
    · funext b; by_cases hb : b < numBucketsWhp fl.N
      · simp only [hb, ↓reduceIte]; exact hbm_eq (16 * b + 12) (by omega)
      · simp only [hb, ↓reduceIte]
    · funext b; by_cases hb : b < numBucketsWhp fl.N
      · simp only [hb, ↓reduceIte]; exact hbm_eq (16 * b + 13) (by omega)
      · simp only [hb, ↓reduceIte]
    · funext b; by_cases hb : b < numBucketsWhp fl.N
      · simp only [hb, ↓reduceIte]; exact hbm_eq (16 * b + 14) (by omega)
      · simp only [hb, ↓reduceIte]
    · funext b; by_cases hb : b < numBucketsWhp fl.N
      · simp only [hb, ↓reduceIte]; exact hbm_eq (16 * b + 15) (by omega)
      · simp only [hb, ↓reduceIte]
  · intro r hr
    refine extractBufTrie_congr hw_pos fun a ha => ?_
    unfold TrieLayout.OwnsAddr at ha
    dsimp only [FastEpochLayout.trieL, epochTrieLayout] at ha
    rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;>
      rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      exact hm a (Or.inr ⟨by omega, lt_of_lt_of_le h2 (by omega)⟩)
  · intro b hb role hrole
    refine extractBTreeSlice_congr_entries
      (hbm_eq (16 * b + 6 + 2 * role) (by omega))
      (hbm_eq (16 * b + 7 + 2 * role) (by omega)) fun u hu => ?_
    have hidx : (3 * b + role) * nSliceWhp fl.N + u < totalBTreeNodesWhp fl.N := by
      have hu' : u < nSliceWhp fl.N := hu
      have h1 : 3 * b + role + 1 ≤ 3 * numBucketsWhp fl.N := by omega
      have hmul : (3 * b + role + 1) * nSliceWhp fl.N ≤
          3 * numBucketsWhp fl.N * nSliceWhp fl.N := Nat.mul_le_mul_right _ h1
      rw [Nat.add_one_mul] at hmul
      unfold totalBTreeNodesWhp; omega
    dsimp only [FastEpochLayout.btL, epochBTreeLayout]
    refine ⟨readPacked_congr hw_pos (fun a ⟨h1, h2⟩ => hm a (Or.inr ⟨by omega, by omega⟩)) hidx,
      readPacked_congr hw_pos (fun a ⟨h1, h2⟩ => hm a (Or.inr ⟨by omega, by omega⟩)) hidx,
      readPacked_congr hw_pos (fun a ⟨h1, h2⟩ => hm a (Or.inr ⟨by omega, by omega⟩)) hidx⟩

/-- Transport `FastEpochInvGen` to a new `SlotIoLayout` `io₂` agreeing on `[0, nSide)` pairs and
preserving non-page metadata `OwnsEpochNonPageMeta`. -/
theorem FastEpochInvGen.transfer_io {slackCur : ℕ} {fl : FastEpochLayout} {io₂ : SlotIoLayout}
    {w fr slack₁ slack₂ : ℕ} {seeds : EpochHashSeeds fl.c fl.U fl.N} {m₁ m₂ : ℕ → ℕ}
    {s_abs : Fin fl.U → Option (Fin fl.V)}
    (hv : fl.Valid w fr) (hinv : FastEpochInvGen slackCur fl slack₁ seeds m₁ s_abs)
    (hpt₂ : ({ fl with io := io₂ } : FastEpochLayout).ParamTable m₂)
    (hm : ∀ a, OwnsEpochNonPageMeta fl.c fl.w fl.N fl.metaBase a → m₂ a = m₁ a)
    (hio₂ : io₂.StateInv (extractBlockPool fl.mp m₁).nSide slack₂ m₂)
    (hpair : ∀ p < (extractBlockPool fl.mp m₁).nSide,
      slotIoPairAt io₂ m₂ p = slotIoPairAt fl.io m₁ p) :
    FastEpochInvGen slackCur { fl with io := io₂ } slack₂ seeds m₂ s_abs := by
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  obtain ⟨hbp, hfm, htr, hbt⟩ := fastEpoch_meta_eq_of_region hv hm
  let fl₂ : FastEpochLayout := { fl with io := io₂ }
  have hkey_eq : ∀ b < numBucketsWhp fl.N, ∀ loc < (extractBlockPool fl.mp m₁).bktCount b,
      fastKeyAt fl₂ seeds.bkt m₂ b loc = fastKeyAt fl seeds.bkt m₁ b loc := by
    intro b hb loc hl
    have hlt : (extractBlockPool fl.mp m₁).toPhys b loc <
        (extractBlockPool fl.mp m₁).nSide :=
      hinv.bp_inv.1.core.toPhys_lt (by
        change b < fl.mp.M; dsimp only [FastEpochLayout.mp, epochBpMetaLayout]; exact hb) hl
    unfold fastKeyAt bpPairAt BlockPoolLayout.mp
    change feistelReconstruct (bWhp fl.N) (bktHash fl.c fl.U fl.N seeds.bkt) b
        (slotIoPairAt io₂ m₂ ((extractBlockPool fl.mp m₂).toPhys b loc)).1 =
      feistelReconstruct (bWhp fl.N) (bktHash fl.c fl.U fl.N seeds.bkt) b
        (slotIoPairAt fl.io m₁ ((extractBlockPool fl.mp m₁).toPhys b loc)).1
    rw [hbp, hpair _ hlt]
  have hseed_b : BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) seeds.bkt m₂ :=
    hinv.seed_bkt.congr_on hw_pos fun a h1 h2 => hm a
      (Or.inr ⟨by dsimp only [FastEpochLayout.bktHashBase] at h1; unfold offBktHash at h1; omega,
        by dsimp only [FastEpochLayout.bktHashBase] at h2
           unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
             offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir offBktMeta offFpHash at *
           omega⟩)
  have hseed_f : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp m₂ :=
    hinv.seed_fp.congr_on hw_pos fun a h1 h2 => hm a
      (Or.inr ⟨by dsimp only [FastEpochLayout.fpHashBase] at h1
                  unfold offFpHash offBktHash at h1; omega,
        by dsimp only [FastEpochLayout.fpHashBase] at h2
           unfold offPageDir offTrieItem offTrieNode offTrieChild offBTreeVals offBTreeKeys
             offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir offBktMeta at *
           omega⟩)
  have hmp_eq : fl₂.mp = fl.mp := rfl
  have hfm_eq : extractFastMeta fl₂ m₂ = extractFastMeta fl m₁ := hfm
  have hbp_eq : extractBlockPool fl₂.mp m₂ = extractBlockPool fl.mp m₁ := hbp
  have htr_eq : ∀ r < 2, extractBufTrie (fl₂.trieL r) m₂ = extractBufTrie (fl.trieL r) m₁ := htr
  have hbt_eq : ∀ b < numBucketsWhp fl.N, ∀ role < 3,
      extractBTreeSlice fl₂.btL b role m₂ = extractBTreeSlice fl.btL b role m₁ := hbt
  refine
    { param_table := hpt₂
      hdr_N := (hm fl.metaBase (Or.inl ⟨le_rfl, by omega⟩)).trans hinv.hdr_N
      mode_zero := (hm (fl.metaBase + 2) (Or.inl ⟨by omega, by omega⟩)).trans hinv.mode_zero
      seed_bkt := hseed_b
      seed_fp := hseed_f
      bp_inv := by
        change (fl₂.bpL).StateInv slack₂ m₂
        unfold BlockPoolLayout.StateInv
        change (extractBlockPool fl.mp m₂).Balanced ∧
          (extractBlockPool fl.mp m₂).nSide ≤ fl.mp.nCap ∧
          io₂.StateInv (extractBlockPool fl.mp m₂).nSide slack₂ m₂
        rw [hbp]
        exact ⟨hinv.bp_inv.1, hinv.bp_inv.2.1, hio₂⟩
      bkt_le_capMax := fun b hb => by
        change (extractBlockPool fl.mp m₂).bktCount b ≤ capMaxWhp fl.N
        rw [hbp]; exact hinv.bkt_le_capMax b hb
      refines := by
        change PoolItemsRefines fl.U fl.V (bWhp fl.N) (bktHash fl.c fl.U fl.N seeds.bkt)
          (extractBlockPool fl.mp m₂).nSide (fun p => ((extractBlockPool fl.mp m₂).ownerOf p).1)
          (slotIoPairAt io₂ m₂) s_abs
        rw [hbp]
        exact hinv.refines.congr (fun _ _ => rfl) hpair
      role_lt := by change (extractFastMeta fl m₂).curBufRole < 2; rw [hfm]; exact hinv.role_lt
      subStep_lt := by
        change (extractFastMeta fl m₂).subStep < qEpochWhp fl.N; rw [hfm]; exact hinv.subStep_lt
      bkt_meta_bounds := fun b hb => by
        have hb0 := hinv.bkt_meta_bounds b hb
        have hfe : extractFastMeta ({ fl with io := io₂ } : FastEpochLayout) m₂ =
            extractFastMeta fl m₁ := hfm
        dsimp only at hb0 ⊢
        rw [hfe]
        exact hb0
      tiers := ?_ }
  have hrole_lt : (extractFastMeta fl m₁).curBufRole < 2 := hinv.role_lt
  have hold_lt : 1 - (extractFastMeta fl m₁).curBufRole < 2 := by omega
  obtain ⟨mC, mO, mB, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12⟩ := hinv.tiers
  refine ⟨mC, mO, mB, ?_⟩
  have htc_eq : extractBufTrie (fl₂.trieL (extractFastMeta fl₂ m₂).curBufRole) m₂ =
      extractBufTrie (fl.trieL (extractFastMeta fl m₁).curBufRole) m₁ := by
    rw [hfm_eq]; exact htr_eq _ hrole_lt
  have hto_eq : extractBufTrie (fl₂.trieL (1 - (extractFastMeta fl₂ m₂).curBufRole)) m₂ =
      extractBufTrie (fl.trieL (1 - (extractFastMeta fl m₁).curBufRole)) m₁ := by
    rw [hfm_eq]; exact htr_eq _ hold_lt
  dsimp only
  change ValidBufTrie (cTabWhp fl.c) (bCharWhp fl.N)
      (extractBufTrie (fl₂.trieL (extractFastMeta fl₂ m₂).curBufRole) m₂) mC ∧ _
  rw [htc_eq, hto_eq]
  have hsu_eq : (extractFastMeta fl₂ m₂).subStep = (extractFastMeta fl m₁).subStep :=
    congrArg FastEpochMeta.subStep hfm_eq
  have hta_eq : (extractFastMeta fl₂ m₂).tryAct = (extractFastMeta fl m₁).tryAct :=
    congrArg FastEpochMeta.tryAct hfm_eq
  have htb_eq : (extractFastMeta fl₂ m₂).tryBkt = (extractFastMeta fl m₁).tryBkt :=
    congrArg FastEpochMeta.tryBkt hfm_eq
  have hts_eq : (extractFastMeta fl₂ m₂).trySalt = (extractFastMeta fl m₁).trySalt :=
    congrArg FastEpochMeta.trySalt hfm_eq
  have htp_eq : (extractFastMeta fl₂ m₂).tryPos = (extractFastMeta fl m₁).tryPos :=
    congrArg FastEpochMeta.tryPos hfm_eq
  have hti_eq : (extractFastMeta fl₂ m₂).tryIns = (extractFastMeta fl m₁).tryIns :=
    congrArg FastEpochMeta.tryIns hfm_eq
  have hrole_eq : (extractFastMeta fl₂ m₂).curRole = (extractFastMeta fl m₁).curRole :=
    congrArg FastEpochMeta.curRole hfm_eq
  have hbs_eq : (extractFastMeta fl₂ m₂).bktSalt = (extractFastMeta fl m₁).bktSalt :=
    congrArg FastEpochMeta.bktSalt hfm_eq
  have hsc_eq : (extractFastMeta fl₂ m₂).shadowCode = (extractFastMeta fl m₁).shadowCode :=
    congrArg FastEpochMeta.shadowCode hfm_eq
  have hsi_eq : (extractFastMeta fl₂ m₂).shadowIns = (extractFastMeta fl m₁).shadowIns :=
    congrArg FastEpochMeta.shadowIns hfm_eq
  have hci_eq : (extractFastMeta fl₂ m₂).curIns = (extractFastMeta fl m₁).curIns :=
    congrArg FastEpochMeta.curIns hfm_eq
  have hdp_eq : (extractFastMeta fl₂ m₂).drainPos = (extractFastMeta fl m₁).drainPos :=
    congrArg FastEpochMeta.drainPos hfm_eq
  have hbc_eq : (extractBlockPool fl₂.mp m₂).bktCount = (extractBlockPool fl.mp m₁).bktCount :=
    congrArg BlockPoolState.bktCount hbp_eq
  refine ⟨t1, t2, t3, by rw [hsu_eq]; exact t4, t5, ?_, ?_, ?_, ?_, ?_, hta_eq ▸ t11, ?_⟩
  · intro rk b loc hmc
    obtain ⟨hb, hl, u, hrk, hk⟩ := t6 rk b loc hmc
    exact ⟨hb, by rw [hbc_eq]; exact hl, u, hrk, (hkey_eq b hb loc hl).trans hk⟩
  · rw [hsu_eq, hdp_eq, hta_eq]
    by_cases hs : (extractFastMeta fl m₁).subStep < qEpochWhp fl.N / 2
    · rw [ite_eq_left hs] at t7 ⊢
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := t7
      refine ⟨a1, a2, a3, a4, a5, a6, a7, fun rk b loc hmo => ?_⟩
      obtain ⟨hnc, hb, hl, u, hrk, hk⟩ := a8 rk b loc hmo
      exact ⟨hnc, hb, by rw [hbc_eq]; exact hl, u, hrk, (hkey_eq b hb loc hl).trans hk⟩
    · rw [ite_eq_right hs] at t7 ⊢; exact t7
  · intro b hb
    obtain ⟨hbv, hbs⟩ := t8 b hb
    have hrb : (extractFastMeta fl m₁).curRole b < 3 := (hinv.bkt_meta_bounds b hb).2.1
    refine ⟨?_, fun fp loc hmb => ?_⟩
    · change ValidWhpSlice fl.N ((extractFastMeta fl₂ m₂).curIns b)
        (extractBTreeSlice fl₂.btL b ((extractFastMeta fl₂ m₂).curRole b) m₂) (mB b)
      rw [congrFun hci_eq b, congrFun hrole_eq b, hbt_eq b hb _ hrb]; exact hbv
    · obtain ⟨hl, u, hfp, hk, d1, d2⟩ := hbs fp loc hmb
      refine ⟨by rw [hbc_eq]; exact hl, u, ?_, (hkey_eq b hb loc hl).trans hk,
        fun b₁ l₁ hmc => ?_, fun b₂ l₂ hmo => ?_⟩
      · refine Eq.trans (congrArg (fun s => (fpHash fl.c fl.U fl.N seeds.fp s u).val) ?_) hfp
        exact Fin.ext (congrFun hbs_eq b)
      · obtain ⟨hb₁, hl₁, _⟩ := t6 _ b₁ l₁ hmc
        rw [hkey_eq b₁ hb₁ l₁ hl₁]; exact d1 b₁ l₁ hmc
      · by_cases hs : (extractFastMeta fl m₁).subStep < qEpochWhp fl.N / 2
        · rw [ite_eq_left hs] at t7
          obtain ⟨_, hb₂, hl₂, _⟩ := t7.2.2.2.2.2.2.2 _ b₂ l₂ hmo
          rw [hkey_eq b₂ hb₂ l₂ hl₂]; exact d2 b₂ l₂ hmo
        · rw [ite_eq_right hs] at t7; rw [t7.1] at hmo; cases hmo
  · intro b hb loc hl
    have hl' : loc < (extractBlockPool fl.mp m₁).bktCount b := by rwa [← hbc_eq]
    obtain ⟨u, hk, hmem⟩ := t9 b hb loc hl'
    refine ⟨u, (hkey_eq b hb loc hl').trans hk, ?_⟩
    rcases hmem with h1 | h2 | h3
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · refine Or.inr (Or.inr ?_)
      have hss : (⟨(extractFastMeta fl₂ m₂).bktSalt b,
          (by rw [congrFun hbs_eq b]; exact (hinv.bkt_meta_bounds b hb).1)⟩ :
          Fin (sMaxWhp fl.c fl.N)) =
          ⟨(extractFastMeta fl m₁).bktSalt b, (hinv.bkt_meta_bounds b hb).1⟩ :=
        Fin.ext (congrFun hbs_eq b)
      change mB b (fpHash fl.c fl.U fl.N seeds.fp _ u).val = some loc
      rw [hss]; exact h3
  · intro b hb hsc
    have hsc' : (extractFastMeta fl m₁).shadowCode b ≠ 0 := by rwa [← congrFun hsc_eq b]
    obtain ⟨p1, p2, p3, p4, sm, hvs, hsm⟩ := t10 b hb hsc'
    have hsr : shadowRoleOf ((extractFastMeta fl m₁).curRole b) < 3 :=
      (shadowRoleOf_lt_and_ne (hinv.bkt_meta_bounds b hb).2.1).1
    refine ⟨?_, ?_, ?_, ?_, sm, ?_, ?_⟩
    · rw [congrFun hsc_eq b, congrFun hbc_eq b]; exact p1
    · rw [hta_eq, htb_eq]; exact p2
    · rw [congrFun hsi_eq b, congrFun hbc_eq b, congrFun hsc_eq b]; exact p3
    · rw [congrFun hci_eq b, congrFun hbc_eq b, congrFun hsc_eq b]; exact p4
    · change ValidWhpSlice fl.N ((extractFastMeta fl₂ m₂).shadowIns b)
        (extractBTreeSlice fl₂.btL b (shadowRoleOf ((extractFastMeta fl₂ m₂).curRole b)) m₂) sm
      rw [congrFun hsi_eq b, congrFun hrole_eq b, hbt_eq b hb _ hsr]; exact hvs
    · intro fp; rw [congrFun hsc_eq b]; exact hsm fp
  · intro hta
    have hta' : (extractFastMeta fl m₁).tryAct = 1 := by rwa [← hta_eq]
    obtain ⟨hs, hb, hst, htp, hsc, hbd, tm, hvt, hm1, hm2⟩ := t12 hta'
    have htr_lt : tryRoleOf ((extractFastMeta fl m₁).curRole
        (extractFastMeta fl m₁).tryBkt) < 3 :=
      (tryRoleOf_lt_and_ne (hinv.bkt_meta_bounds _ hb).2.1).1
    refine ⟨by rw [hsu_eq]; exact hs, by rw [htb_eq]; exact hb, by rw [hts_eq]; exact hst,
      by rw [htp_eq, htb_eq, hbc_eq]; exact htp, by rw [htb_eq, hsc_eq]; exact hsc,
      by rw [hti_eq, htb_eq, hbc_eq, htp_eq]; exact hbd, tm, ?_, ?_, ?_⟩
    · change ValidWhpSlice fl.N (extractFastMeta fl₂ m₂).tryIns
        (extractBTreeSlice fl₂.btL (extractFastMeta fl₂ m₂).tryBkt
          (tryRoleOf ((extractFastMeta fl₂ m₂).curRole (extractFastMeta fl₂ m₂).tryBkt)) m₂) tm
      rw [hti_eq, htb_eq, hrole_eq, hbt_eq _ hb _ htr_lt]; exact hvt
    · intro fp loc hmt
      obtain ⟨hl, u, hk, hmb, hfp⟩ := hm1 fp loc hmt
      refine ⟨by rw [htp_eq]; exact hl, u, ?_, ?_, ?_⟩
      · rw [htb_eq]; exact (hkey_eq _ hb loc (lt_of_lt_of_le hl htp)).trans hk
      · have hss : (⟨(extractFastMeta fl₂ m₂).bktSalt (extractFastMeta fl₂ m₂).tryBkt,
            by rw [htb_eq, congrFun hbs_eq _]; exact (hinv.bkt_meta_bounds _ hb).1⟩ :
            Fin (sMaxWhp fl.c fl.N)) =
            ⟨(extractFastMeta fl m₁).bktSalt (extractFastMeta fl m₁).tryBkt,
              (hinv.bkt_meta_bounds _ hb).1⟩ :=
          Fin.ext (by change (extractFastMeta fl₂ m₂).bktSalt _ = _; rw [htb_eq, congrFun hbs_eq _])
        change mB (extractFastMeta fl₂ m₂).tryBkt
          (fpHash fl.c fl.U fl.N seeds.fp _ u).val = some loc
        rw [hss, htb_eq]; exact hmb
      · have hss : (⟨(extractFastMeta fl₂ m₂).trySalt, by rw [hts_eq]; exact hst⟩ :
            Fin (sMaxWhp fl.c fl.N)) = ⟨(extractFastMeta fl m₁).trySalt, hst⟩ :=
          Fin.ext hts_eq
        change (fpHash fl.c fl.U fl.N seeds.fp _ u).val = fp
        rw [hss]; exact hfp
    · intro loc hl u hk hmb
      have hl' : loc < (extractFastMeta fl m₁).tryPos := by rwa [← htp_eq]
      have hk' : fastKeyAt fl seeds.bkt m₁ (extractFastMeta fl m₁).tryBkt loc = u := by
        rw [htb_eq] at hk
        exact (hkey_eq _ hb loc (lt_of_lt_of_le hl' htp)).symm.trans hk
      have hss_b : (⟨(extractFastMeta fl₂ m₂).bktSalt (extractFastMeta fl₂ m₂).tryBkt,
            by rw [htb_eq, congrFun hbs_eq _]; exact (hinv.bkt_meta_bounds _ hb).1⟩ :
            Fin (sMaxWhp fl.c fl.N)) =
            ⟨(extractFastMeta fl m₁).bktSalt (extractFastMeta fl m₁).tryBkt,
              (hinv.bkt_meta_bounds _ hb).1⟩ :=
        Fin.ext (by change (extractFastMeta fl₂ m₂).bktSalt _ = _; rw [htb_eq, congrFun hbs_eq _])
      have hmb' : mB (extractFastMeta fl m₁).tryBkt
          (fpHash fl.c fl.U fl.N seeds.fp
            ⟨(extractFastMeta fl m₁).bktSalt (extractFastMeta fl m₁).tryBkt,
              (hinv.bkt_meta_bounds _ hb).1⟩ u).val = some loc := by
        change mB (extractFastMeta fl₂ m₂).tryBkt
          (fpHash fl.c fl.U fl.N seeds.fp _ u).val = some loc at hmb
        exact (congrArg (fun a => mB a _ = some loc) htb_eq ▸
          (congrArg (fun s => mB _ (fpHash fl.c fl.U fl.N seeds.fp s u).val = some loc) hss_b ▸
            hmb))
      have hss_t : (⟨(extractFastMeta fl₂ m₂).trySalt, by rw [hts_eq]; exact hst⟩ :
            Fin (sMaxWhp fl.c fl.N)) = ⟨(extractFastMeta fl m₁).trySalt, hst⟩ :=
        Fin.ext hts_eq
      change tm (fpHash fl.c fl.U fl.N seeds.fp _ u).val = some loc
      rw [hss_t]; exact hm2 loc hl' u hk' hmb'

/-- Transport `LargeEpochInv` to a new `SlotIoLayout` `io₂` (fast or fallback mode). -/
theorem LargeEpochInv.transfer_io {fl : FastEpochLayout} {io₂ : SlotIoLayout}
    {w fr slack₁ slack₂ : ℕ} {seeds : EpochHashSeeds fl.c fl.U fl.N} {m₁ m₂ : ℕ → ℕ}
    {s_abs : Fin fl.U → Option (Fin fl.V)}
    (hv : fl.Valid w fr) (hinv : LargeEpochInv fl slack₁ seeds m₁ s_abs)
    (hpt₂ : ({ fl with io := io₂ } : FastEpochLayout).ParamTable m₂)
    (hm : ∀ a, OwnsEpochNonPageMeta fl.c fl.w fl.N fl.metaBase a → m₂ a = m₁ a)
    (hio₂_f : m₁ (fl.metaBase + 2) = 0 →
      io₂.StateInv (extractBlockPool fl.mp m₁).nSide slack₂ m₂)
    (hio₂_b : m₁ (fl.metaBase + 2) = 1 →
      io₂.StateInv (extractFallback fl.mp m₁).nSide slack₂ m₂)
    (hpair : ∀ p < (if m₁ (fl.metaBase + 2) = 0 then (extractBlockPool fl.mp m₁).nSide
        else (extractFallback fl.mp m₁).nSide),
      slotIoPairAt io₂ m₂ p = slotIoPairAt fl.io m₁ p) :
    LargeEpochInv { fl with io := io₂ } slack₂ seeds m₂ s_abs := by
  rcases hinv.2 with ⟨hm0, hf⟩ | ⟨hm1, hfb⟩
  · have hpair' : ∀ p < (extractBlockPool fl.mp m₁).nSide,
        slotIoPairAt io₂ m₂ p = slotIoPairAt fl.io m₁ p := fun p hp =>
      hpair p (by rw [ite_eq_left hm0]; exact hp)
    exact LargeEpochInv.fast
      ((hf.toGen 0).transfer_io hv hpt₂ hm (hio₂_f hm0) hpair').toInv
  · have hpair' : ∀ p < (extractFallback fl.mp m₁).nSide,
        slotIoPairAt io₂ m₂ p = slotIoPairAt fl.io m₁ p := fun p hp =>
      hpair p (by rw [ite_eq_right (by omega : m₁ (fl.metaBase + 2) ≠ 0)]; exact hp)
    have hmp_val : fl.fbL.bpL.mp.Valid w
        (fl.fbL.bpL.mp.metaBase + epochMetaWordsWhp fl.c fl.fbL.bpL.mp.w fl.N) := by
      have h := valid_epochBpMetaLayout hv.thresh_le hv.N_le_U (hv.w_eq ▸ hv.fits_U)
        (le_refl (fl.metaBase + epochMetaWordsWhp fl.c fl.w fl.N))
      cases hv.w_eq; exact h
    exact LargeEpochInv.fallback hpt₂
      (hfb.transfer_io hmp_val hm rfl (hio₂_b hm1) hpair')

/-- Transport `CurBufKeysIn` across a `SlotIoLayout` change. -/
theorem CurBufKeysIn.transfer_io {fl : FastEpochLayout} {io₂ : SlotIoLayout}
    {w fr : ℕ} {seeds : EpochHashSeeds fl.c fl.U fl.N} {m₁ m₂ : ℕ → ℕ}
    {S : Finset (Fin fl.U)}
    (hv : fl.Valid w fr)
    (hcore : (extractBlockPool fl.mp m₁).CoreValid)
    (hrole_lt : (extractFastMeta fl m₁).curBufRole < 2)
    (hm : ∀ a, OwnsEpochNonPageMeta fl.c fl.w fl.N fl.metaBase a → m₂ a = m₁ a)
    (hpair : ∀ p < (extractBlockPool fl.mp m₁).nSide,
      slotIoPairAt io₂ m₂ p = slotIoPairAt fl.io m₁ p)
    (hcur : CurBufKeysIn (fl := fl) seeds m₁ S) :
    CurBufKeysIn (fl := { fl with io := io₂ }) seeds m₂ S := by
  obtain ⟨hbp, hfm, htr, _⟩ := fastEpoch_meta_eq_of_region hv hm
  intro id b loc u hchk hb hl hk
  let fl₂ : FastEpochLayout := { fl with io := io₂ }
  change bufCheckSlot (extractBufTrie (fl₂.trieL (extractFastMeta fl₂ m₂).curBufRole) m₂) id =
      some (b, loc) at hchk
  have hfm_eq : extractFastMeta fl₂ m₂ = extractFastMeta fl m₁ := hfm
  have hbp_eq : extractBlockPool fl₂.mp m₂ = extractBlockPool fl.mp m₁ := hbp
  have htr_c : extractBufTrie (fl₂.trieL (extractFastMeta fl m₁).curBufRole) m₂ =
      extractBufTrie (fl.trieL (extractFastMeta fl m₁).curBufRole) m₁ := htr _ hrole_lt
  rw [hfm_eq, htr_c] at hchk
  rw [hbp_eq] at hl
  have hlt := hcore.toPhys_lt (by
    change b < fl.mp.M; dsimp only [FastEpochLayout.mp, epochBpMetaLayout]; exact hb) hl
  have hke : fastKeyAt fl₂ seeds.bkt m₂ b loc = fastKeyAt fl seeds.bkt m₁ b loc := by
    unfold fastKeyAt bpPairAt BlockPoolLayout.mp
    change feistelReconstruct (bWhp fl.N) (bktHash fl.c fl.U fl.N seeds.bkt) b
        (slotIoPairAt io₂ m₂ ((extractBlockPool fl.mp m₂).toPhys b loc)).1 =
      feistelReconstruct (bWhp fl.N) (bktHash fl.c fl.U fl.N seeds.bkt) b
        (slotIoPairAt fl.io m₁ ((extractBlockPool fl.mp m₁).toPhys b loc)).1
    rw [hbp, hpair _ hlt]
  exact hcur id b loc u hchk hb hl (hke.symm.trans hk)

/-- Transport `FastSubEpochGood` across a `SlotIoLayout` change. -/
theorem FastSubEpochGood.transfer_io {slackCur slackPot : ℕ} {fl : FastEpochLayout}
    {io₂ : SlotIoLayout} {w fr slack₁ slack₂ : ℕ}
    {win : EpochWindowSpec fl.c fl.U fl.N} {e : Fin win.numSubs}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {hgood : GoodEpochSeeds win seeds}
    {m₁ m₂ : ℕ → ℕ} {s_abs : Fin fl.U → Option (Fin fl.V)}
    (hv : fl.Valid w fr) (hg : FastSubEpochGood slackCur slackPot slack₁ win e seeds hgood m₁ s_abs)
    (hpt₂ : ({ fl with io := io₂ } : FastEpochLayout).ParamTable m₂)
    (hm : ∀ a, OwnsEpochNonPageMeta fl.c fl.w fl.N fl.metaBase a → m₂ a = m₁ a)
    (hio₂ : io₂.StateInv (extractBlockPool fl.mp m₁).nSide slack₂ m₂)
    (hpair : ∀ p < (extractBlockPool fl.mp m₁).nSide,
      slotIoPairAt io₂ m₂ p = slotIoPairAt fl.io m₁ p) :
    FastSubEpochGood slackCur slackPot (fl := { fl with io := io₂ }) slack₂ win e seeds hgood m₂
      s_abs := by
  let fl₂ : FastEpochLayout := { fl with io := io₂ }
  obtain ⟨hbp, hfm, htr, _⟩ := fastEpoch_meta_eq_of_region hv hm
  have hrole_lt : (extractFastMeta fl m₁).curBufRole < 2 := hg.inv.role_lt
  have hold_lt : 1 - (extractFastMeta fl m₁).curBufRole < 2 := by omega
  have hkey_eq : ∀ b < numBucketsWhp fl.N, ∀ loc < (extractBlockPool fl.mp m₁).bktCount b,
      fastKeyAt fl₂ seeds.bkt m₂ b loc = fastKeyAt fl seeds.bkt m₁ b loc := by
    intro b hb loc hl
    have hlt : (extractBlockPool fl.mp m₁).toPhys b loc <
        (extractBlockPool fl.mp m₁).nSide :=
      hg.inv.bp_inv.1.core.toPhys_lt (by
        change b < fl.mp.M; dsimp only [FastEpochLayout.mp, epochBpMetaLayout]; exact hb) hl
    unfold fastKeyAt bpPairAt BlockPoolLayout.mp
    change feistelReconstruct (bWhp fl.N) (bktHash fl.c fl.U fl.N seeds.bkt) b
        (slotIoPairAt io₂ m₂ ((extractBlockPool fl.mp m₂).toPhys b loc)).1 =
      feistelReconstruct (bWhp fl.N) (bktHash fl.c fl.U fl.N seeds.bkt) b
        (slotIoPairAt fl.io m₁ ((extractBlockPool fl.mp m₁).toPhys b loc)).1
    rw [hbp, hpair _ hlt]
  have hfm_eq : extractFastMeta fl₂ m₂ = extractFastMeta fl m₁ := hfm
  have hbp_eq : extractBlockPool fl₂.mp m₂ = extractBlockPool fl.mp m₁ := hbp
  have htr_eq : extractBufTrie (fl₂.trieL (1 - (extractFastMeta fl m₁).curBufRole)) m₂ =
      extractBufTrie (fl.trieL (1 - (extractFastMeta fl m₁).curBufRole)) m₁ := htr _ hold_lt
  have hbad_eq : ∀ id,
      isBadOldSlot (fl := fl₂) win e seeds m₂ id ↔
      isBadOldSlot (fl := fl) win e seeds m₁ id := by
    intro id
    constructor <;> rintro ⟨b, loc, u, hchk, hb, hl, hk, hcol⟩
    · refine ⟨b, loc, u, ?_, hb, ?_, ?_, hcol⟩
      · rwa [hfm_eq, htr_eq] at hchk
      · rwa [hbp_eq] at hl
      · exact (hkey_eq b hb loc (by rwa [hbp_eq] at hl)).symm.trans hk
    · refine ⟨b, loc, u, ?_, hb, ?_, ?_, hcol⟩
      · rw [hfm_eq, htr_eq]; exact hchk
      · rw [hbp_eq]; exact hl
      · exact (hkey_eq b hb loc hl).trans hk
  have hnb_eq : ∀ k,
      nBadFrom (fl := fl₂) win e seeds m₂ k = nBadFrom (fl := fl) win e seeds m₁ k := by
    intro k
    unfold nBadFrom
    simp only [hfm_eq, htr_eq]
    congr 1; ext id; simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun ⟨hr, hk, hb⟩ => ⟨hr, hk, (hbad_eq id).mp hb⟩,
      fun ⟨hr, hk, hb⟩ => ⟨hr, hk, (hbad_eq id).mpr hb⟩⟩
  have hsh_eq : ∀ b, shCost fl₂ m₂ b = shCost fl m₁ b := by
    intro b; unfold shCost shSlack
    simp only [hfm_eq, hbp_eq]; rfl
  have hst_eq : shTerm fl₂ win e seeds m₂ = shTerm fl win e seeds m₁ := by
    classical
    unfold shTerm
    dsimp only
    rw [hfm_eq]
    by_cases hb : isBadOldSlot (fl := fl) win e seeds m₁ (extractFastMeta fl m₁).drainPos
    · have hb₂ : isBadOldSlot (fl := fl₂) win e seeds m₂ (extractFastMeta fl m₁).drainPos :=
        (hbad_eq _).mpr hb
      rw [ite_eq_left hb₂, ite_eq_left hb, htr_eq]
      cases hc : bufCheckSlot _ _ <;> simp [hsh_eq]
    · have hb₂ : ¬isBadOldSlot (fl := fl₂) win e seeds m₂ (extractFastMeta fl m₁).drainPos :=
        fun h => hb ((hbad_eq _).mp h)
      rw [ite_eq_right hb₂, ite_eq_right hb]
  have hdp_eq : drainPotential (fl := fl₂) win e seeds hgood m₂ =
      drainPotential (fl := fl) win e seeds hgood m₁ := by
    classical
    unfold drainPotential
    dsimp only
    simp only [hfm_eq, htr_eq, hnb_eq, hst_eq, hbp_eq]
    split_ifs <;> rfl
  exact
    { inv := hg.inv.transfer_io hv hpt₂ hm hio₂ hpair
      live_sub := hg.live_sub
      old_sub := fun hs id b loc u hchk hb hl hk => by
        rw [hfm_eq] at hs hchk
        rw [htr_eq] at hchk
        rw [hbp_eq] at hl
        exact hg.old_sub hs id b loc u hchk hb hl ((hkey_eq b hb loc hl).symm.trans hk)
      try_match := fun hta hlt b' loc' hchk => by
        rw [hfm_eq] at hta hlt hchk ⊢
        rw [htr_eq] at hlt hchk
        exact hg.try_match hta hlt b' loc' hchk
      trySalt_le := fun hta => by
        rw [hfm_eq] at hta ⊢
        exact hg.trySalt_le hta
      pot_le := fun hs => by
        rw [hfm_eq] at hs ⊢
        rw [hdp_eq]
        exact hg.pot_le hs }

/-! ## Section 3: Incremental `SlotIoLayout` Mode-Switch `slotIoPairAt` Equivalences -/

/-- Switching a direct stream `(usePaged = 0, sideBit = 0, itemBase = A_lo, qBits = q_lo)` into
`SplitPair` mode with split cursor `mem spAddr = s_split` (`nSide ≤ s_split`) preserves every
virtual slot `p < nSide`. -/
theorem slotIoPairAt_direct_eq_split_start {pgLo pgSp : PageArenaLayout} {mem : ℕ → ℕ}
    {nSide : ℕ}
    (hlo : pgSp.offDir = pgLo.itemBase) (hq : pgSp.qBits = pgLo.qBits)
    (hv : pgSp.vBits = pgLo.vBits) (hw : pgSp.w = pgLo.w)
    (hsp : nSide ≤ mem pgSp.metaBase) {p : ℕ} (hp : p < nSide) :
    slotIoPairAt ⟨0, 1, pgSp⟩ mem p = slotIoPairAt ⟨0, 0, pgLo⟩ mem p := by
  unfold slotIoPairAt splitPairRead SlotIoLayout.splitCfg arenaPairAt
  simp only [↓reduceIte, Nat.one_ne_zero]
  have hlt : p < mem pgSp.metaBase := lt_of_lt_of_le hp hsp
  rw [ite_eq_left hlt, hlo, hq, hv, hw]
  exact Prod.ext (Nat.mod_eq_of_lt (pairQuotAt_lt ..)) rfl

/-- Leaving `SplitPair` mode at `mem spAddr = 0` to a direct stream at `itemBase = A_hi` with wider
quotient width `qBits = q_hi` (`q_lo ≤ q_hi`) preserves every virtual slot with `quot < 2 ^ q_lo`.
-/
theorem slotIoPairAt_split_zero_eq_direct {pgSp pgHi : PageArenaLayout} {mem : ℕ → ℕ}
    (hib : pgHi.itemBase = pgSp.itemBase) (hq_hi : pgHi.qBits = pgSp.offTail)
    (hv : pgHi.vBits = pgSp.vBits) (hw : pgHi.w = pgSp.w)
    (hsp0 : mem pgSp.metaBase = 0) {p : ℕ}
    (hq_fit : pairQuotAt pgSp.itemBase pgSp.offTail pgSp.vBits pgSp.w mem p < 2 ^ pgSp.qBits) :
    slotIoPairAt ⟨0, 0, pgHi⟩ mem p = slotIoPairAt ⟨0, 1, pgSp⟩ mem p := by
  unfold slotIoPairAt splitPairRead SlotIoLayout.splitCfg arenaPairAt
  simp only [↓reduceIte, Nat.one_ne_zero, hsp0, Nat.not_lt_zero]
  rw [hib, hq_hi, hv, hw]
  exact Prod.ext (Nat.mod_eq_of_lt hq_fit).symm rfl

/-- Entering paged `PageUnpermState` (`usePaged = 1, sideBit = 0`) right after identity init
(`∀ idx < nSide, toPhys false idx = idx`) preserves every virtual slot `p < nSide`. -/
theorem slotIoPairAt_paged_src_eq_direct {pgP pgD : PageArenaLayout} {mem : ℕ → ℕ}
    (hib : pgP.itemBase = pgD.itemBase) (hq : pgP.qBits = pgD.qBits)
    (hv : pgP.vBits = pgD.vBits) (hw : pgP.w = pgD.w) {p : ℕ}
    (hid : (extractPageUnperm pgP mem).toPhys false p = p) :
    slotIoPairAt ⟨1, 0, pgP⟩ mem p = slotIoPairAt ⟨0, 0, pgD⟩ mem p := by
  unfold slotIoPairAt PageUnpermState.virtAt SlotIoLayout.side arenaPairAt
  dsimp only
  simp only [Nat.one_ne_zero, ↓reduceIte]
  change (pairQuotAt pgP.itemBase pgP.qBits pgP.vBits pgP.w mem
      ((extractPageUnperm pgP mem).toPhys false p),
    pairValAt pgP.itemBase pgP.qBits pgP.vBits pgP.w mem
      ((extractPageUnperm pgP mem).toPhys false p)) = _
  rw [hid, hib, hq, hv, hw]

/-- Leaving paged `PageUnpermState` (`usePaged = 1, sideBit = 1`) once unpermutation completes
(`cleanPhase = 4`, `∀ idx < nSide, toPhys true idx = idx`) preserves every virtual slot `p < nSide`.
-/
theorem slotIoPairAt_direct_eq_paged_dst {pgP pgD : PageArenaLayout} {mem : ℕ → ℕ}
    (hib : pgD.itemBase = pgP.itemBase) (hq : pgD.qBits = pgP.qBits)
    (hv : pgD.vBits = pgP.vBits) (hw : pgD.w = pgP.w) {p : ℕ}
    (hid : (extractPageUnperm pgP mem).toPhys true p = p) :
    slotIoPairAt ⟨0, 0, pgD⟩ mem p = slotIoPairAt ⟨1, 1, pgP⟩ mem p := by
  unfold slotIoPairAt PageUnpermState.virtAt SlotIoLayout.side arenaPairAt
  dsimp only
  change (pairQuotAt pgD.itemBase pgD.qBits pgD.vBits pgD.w mem p,
      pairValAt pgD.itemBase pgD.qBits pgD.vBits pgD.w mem p) =
    (pairQuotAt pgP.itemBase pgP.qBits pgP.vBits pgP.w mem
      ((extractPageUnperm pgP mem).toPhys true p),
    pairValAt pgP.itemBase pgP.qBits pgP.vBits pgP.w mem
      ((extractPageUnperm pgP mem).toPhys true p))
  rw [hid, hib, hq, hv, hw]

/-! ## Section 4: Band-Stable `PagePairState` Initialization Helper -/

/-- Parametric initial `PagePairState` holding `q₀ * B + r_cur` items in identity physical order
on side `false`, valid whenever `q₀ = 0 ∧ r_cur < 4 * B` or `5 * B ≤ 4 * r_cur ≤ 11 * B`.
Its `tailRes` / `tailOwner` tables depend **only** on `q₀` (`qb_mod = (q₀ * B) % (8 * B)`), so
concurrent user operations shifting `r_cur` during incremental tail initialization never invalidate
the already-written tail directory entries. -/
@[expose] def pagePairInitBand (pgB q₀ r_cur : ℕ) : PagePairState where
  pageSize := max 32 pgB
  fullPages s := if s then 0 else q₀
  tailCount s := if s then 0 else r_cur
  tailHead _ := 0
  pageOf s vp := if s then 0 else vp
  ownerSide _ := false
  ownerVp P := P
  tailRes _ k := (q₀ * max 32 pgB + k) % (8 * max 32 pgB)
  tailOwnerSide _ := false
  tailOwnerRing res := (res + 8 * max 32 pgB - (q₀ * max 32 pgB) % (8 * max 32 pgB)) %
    (8 * max 32 pgB)
  job := .idle

/-- `pagePairInitBand pgB q₀ r_cur` is `WellBalanced`, `Valid`, and maps `[0, q₀ * pgB + r_cur)`
identically whenever `32 ≤ pgB` and `r_cur` stays inside `[5/4 * pgB, 11/4 * pgB]` (`0 < q₀`). -/
theorem pagePairInitBand_valid {pgB q₀ r_cur : ℕ} (hB32 : 32 ≤ pgB)
    (hr_hi : 4 * r_cur ≤ 11 * pgB) (hr_lo : 0 < q₀ → 5 * pgB ≤ 4 * r_cur) :
    let st := pagePairInitBand pgB q₀ r_cur
    st.WellBalanced ∧ st.Valid ∧
    st.pageSize = pgB ∧ st.virtLen false = q₀ * pgB + r_cur ∧ st.virtLen true = 0 ∧
    ∀ idx < q₀ * pgB + r_cur, st.toPhys false idx = idx := by
  have hmax : max 32 pgB = pgB := max_eq_right hB32
  have hBpos : 0 < pgB := by omega
  have hM : 0 < 8 * pgB := by omega
  set st := pagePairInitBand pgB q₀ r_cur
  have hps : st.pageSize = pgB := hmax
  have hvl_f : st.virtLen false = q₀ * pgB + r_cur := by
    simp [st, PagePairState.virtLen, pagePairInitBand, hmax]
  have hvl_t : st.virtLen true = 0 := by
    simp [st, PagePairState.virtLen, pagePairInitBand]
  have htot : st.totalItems = q₀ * pgB + r_cur := by
    unfold PagePairState.totalItems; rw [hvl_f, hvl_t, add_zero]
  have htp : st.totalPages = q₀ := by
    simp [st, PagePairState.totalPages, pagePairInitBand]
  have hvalid : st.Valid := by
    refine
      { pageSize_pos := by rw [hps]; exact hBpos
        tailCount_lt := fun s => by cases s <;> simp [st, pagePairInitBand, hmax] <;> omega
        tailSum_lt := by simp [st, pagePairInitBand, hmax]; omega
        tailHead_lt := fun _ => by simp [st, pagePairInitBand, hmax]; omega
        page_lt := fun s vp hvp => by
          cases s
          · rw [htp]; exact hvp
          · simp [st, pagePairInitBand] at hvp
        owner_pageOf := fun s vp hvp => by
          cases s
          · simp [st, pagePairInitBand]
          · simp [st, pagePairInitBand] at hvp
        pageOf_owner := fun P hP => by
          rw [htp] at hP
          simp [st, pagePairInitBand, hP]
        tailRes_lt := fun s t _ => by
          change (q₀ * max 32 pgB + st.ringSlot s t) % (8 * max 32 pgB) < 8 * max 32 pgB
          exact Nat.mod_lt _ (by rw [hmax]; exact hM)
        tail_lt := fun s t ht => by
          cases s
          · rw [htot]
            have ht' : t < r_cur := by simpa [st, pagePairInitBand] using ht
            have hbase : st.tailPhys false t = q₀ * pgB + t := by
              unfold PagePairState.tailPhys PagePairState.ringSlot
              rw [htp, hps]
              simp only [st, pagePairInitBand, hmax, zero_add,
                Nat.mod_eq_of_lt (show t < 4 * pgB by omega)]
              have hmd := offsetOfMod hM (base := q₀ * pgB) (p := q₀ * pgB + t)
                (Nat.le_add_right _ _) (by omega)
              rw [Nat.add_sub_cancel_left] at hmd
              change q₀ * pgB + ((q₀ * pgB + t) % (8 * pgB) + 8 * pgB -
                (q₀ * pgB) % (8 * pgB)) % (8 * pgB) = q₀ * pgB + t
              rw [hmd]
            omega
          · simp [st, pagePairInitBand] at ht
        owner_tail := fun s t ht => by
          cases s
          · have ht' : t < r_cur := by simpa [st, pagePairInitBand] using ht
            have hlt_t : t < 4 * pgB := by omega
            have hrs : st.ringSlot false t = t := by
              unfold PagePairState.ringSlot
              simp only [st, pagePairInitBand, hmax, zero_add]
              exact Nat.mod_eq_of_lt hlt_t
            simp only [hrs]
            change false = false ∧
              ((q₀ * max 32 pgB + t) % (8 * max 32 pgB) + 8 * max 32 pgB -
                (q₀ * max 32 pgB) % (8 * max 32 pgB)) % (8 * max 32 pgB) = t
            refine ⟨rfl, ?_⟩
            rw [hmax]
            have hmd := offsetOfMod hM (base := q₀ * pgB) (p := q₀ * pgB + t)
              (Nat.le_add_right _ _) (by omega)
            rwa [Nat.add_sub_cancel_left] at hmd
          · simp [st, pagePairInitBand] at ht
        tail_owner := fun p hp_lo hp_hi => by
          rw [htp, hps] at hp_lo
          rw [htot] at hp_hi
          have hmd := offsetOfMod hM (base := q₀ * pgB) (p := p) hp_lo (by omega)
          have hk_lt : p - q₀ * pgB < 4 * pgB := by omega
          have hring : st.tailOwnerRing (p % (8 * pgB)) = p - q₀ * pgB := by
            change (p % (8 * pgB) + 8 * max 32 pgB - (q₀ * max 32 pgB) % (8 * max 32 pgB)) %
              (8 * max 32 pgB) = p - q₀ * pgB
            rw [hmax]; exact hmd
          have hside : st.tailOwnerSide (p % (8 * pgB)) = false := rfl
          dsimp only; rw [hps, hring, hside]
          have hidx_eq : ringIdxOfSlot (st.tailHead false) pgB (p - q₀ * pgB) = p - q₀ * pgB := by
            unfold ringIdxOfSlot
            change (p - q₀ * pgB + 4 * pgB - 0) % (4 * pgB) = p - q₀ * pgB
            rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hk_lt]
          refine ⟨hk_lt, ?_, ?_⟩
          · rw [hidx_eq]; change p - q₀ * pgB < r_cur; omega
          · rw [hidx_eq]
            unfold PagePairState.tailPhys PagePairState.ringSlot
            rw [htp, hps]
            change q₀ * pgB + ((q₀ * max 32 pgB + (0 + (p - q₀ * pgB)) % (4 * pgB)) %
              (8 * max 32 pgB) + 8 * pgB - (q₀ * pgB) % (8 * pgB)) % (8 * pgB) = p
            rw [hmax, zero_add, Nat.mod_eq_of_lt hk_lt,
              show q₀ * pgB + (p - q₀ * pgB) = p by omega, hmd]
            omega }
  have hwb : st.WellBalanced :=
    { valid := hvalid
      pageSize_ge := by rw [hps]; exact hB32
      jobValid := trivial
      pot_bound := by
        change if (PageJob.idle : PageJob) = .idle then
            16 * st.phi ≤ 24 * st.pageSize - 8
          else 16 * st.phi + st.remTicks ≤ 28 * st.pageSize
        rw [ite_eq_left rfl]
        unfold PagePairState.phi PagePairState.dev
        have hq_f : st.fullPages false = q₀ := rfl
        have hq_t : st.fullPages true = 0 := rfl
        have hr_f : st.tailCount false = r_cur := rfl
        have hr_t : st.tailCount true = 0 := rfl
        rw [hps, hq_f, hq_t, hr_f, hr_t]
        by_cases hq : 0 < q₀
        · have hlo := hr_lo hq
          rw [ite_eq_left hq, ite_eq_right (Nat.not_lt_zero 0)]
          omega
        · rw [ite_eq_right hq, ite_eq_right (Nat.not_lt_zero 0)]
          omega
      side_bound := trivial }
  refine ⟨hwb, hvalid, hps, hvl_f, hvl_t, fun idx hidx => ?_⟩
  unfold PagePairState.toPhys
  rw [hps]
  by_cases hfull : idx < st.fullPages false * pgB
  · rw [ite_eq_left hfull]
    change (idx / pgB) * pgB + idx % pgB = idx
    exact Nat.div_add_mod' idx pgB
  · rw [ite_eq_right hfull]
    have hq_eq : st.fullPages false = q₀ := rfl
    rw [hq_eq] at hfull ⊢
    unfold PagePairState.tailPhys PagePairState.ringSlot
    rw [htp, hps]
    have hk_lt : idx - q₀ * pgB < 4 * pgB := by omega
    change q₀ * pgB + ((q₀ * max 32 pgB + (0 + (idx - q₀ * pgB)) % (4 * pgB)) %
      (8 * max 32 pgB) + 8 * pgB - (q₀ * pgB) % (8 * pgB)) % (8 * pgB) = idx
    rw [hmax, zero_add, Nat.mod_eq_of_lt hk_lt, show q₀ * pgB + (idx - q₀ * pgB) = idx by omega,
      offsetOfMod hM (base := q₀ * pgB) (p := idx) (by omega) (by omega)]
    omega

/-! ## Section 5: Incremental `RInstr.rand` Uniform Word-Fill Batch (`RCode .exact`) -/

/-- Parameter-free `RCode .exact r` loop sampling uniform `w`-bit words into
`mem[rCur .. rEnd)` using mask `rMask = 2 ^ w - 1` (`¬ReadsWidth`). -/
@[expose] def randFillBatchCode {r : ℕ} (rCur rEnd rMask rTmp rOne : Fin r) : RCode .exact r :=
  .loop (.lt rCur rEnd)
    (.seq (.rand rTmp rMask)
      (.seq (.op (.store rCur rTmp))
        (.op (.exactBin .add rCur rCur rOne))))

theorem randFillBatchCode_not_readsWidth {r : ℕ} (rCur rEnd rMask rTmp rOne : Fin r) :
    ¬(randFillBatchCode rCur rEnd rMask rTmp rOne).ReadsWidth := by
  simp [randFillBatchCode, RCode.ReadsWidth, Op.ReadsWidth, Op.exactBin]

/-- Deterministic memory overlay writing `words : Fin k → Fin (2 ^ w)` onto `[start, start + k)`.
-/
@[expose] def writeWords {w k : ℕ} (mem : ℕ → ℕ) (start : ℕ)
    (words : Fin k → Fin (2 ^ w)) : ℕ → ℕ :=
  fun a => if h : start ≤ a ∧ a < start + k then (words ⟨a - start, by omega⟩).val else mem a

theorem writeWords_apply_in {w k : ℕ} (mem : ℕ → ℕ) (start : ℕ)
    (words : Fin k → Fin (2 ^ w)) {i : ℕ} (hi : i < k) :
    writeWords mem start words (start + i) = (words ⟨i, hi⟩).val := by
  unfold writeWords
  have hc : start ≤ start + i ∧ start + i < start + k := ⟨Nat.le_add_right _ _, by omega⟩
  rw [dite_eq_left hc]
  congr 1; ext; simp

theorem writeWords_apply_out {w k : ℕ} (mem : ℕ → ℕ) (start : ℕ)
    (words : Fin k → Fin (2 ^ w)) {a : ℕ} (ha : ¬(start ≤ a ∧ a < start + k)) :
    writeWords mem start words a = mem a := by
  unfold writeWords; rw [dite_eq_right ha]

theorem writeWords_append {w a b : ℕ} (mem : ℕ → ℕ) (start : ℕ)
    (u : Fin a → Fin (2 ^ w)) (v : Fin b → Fin (2 ^ w)) :
    writeWords (writeWords mem start u) (start + a) v =
      writeWords mem start (Fin.append u v) := by
  funext addr
  by_cases hb : start + a ≤ addr ∧ addr < start + a + b
  · have hab : start ≤ addr ∧ addr < start + (a + b) := by omega
    unfold writeWords
    rw [dite_eq_left hb, dite_eq_left hab]
    have heq : (⟨addr - start, by omega⟩ : Fin (a + b)) =
        Fin.natAdd a ⟨addr - (start + a), by omega⟩ := by
      ext; dsimp; omega
    rw [heq, Fin.append_right]
  · unfold writeWords
    rw [dite_eq_right hb]
    by_cases ha : start ≤ addr ∧ addr < start + a
    · have hab : start ≤ addr ∧ addr < start + (a + b) := by omega
      rw [dite_eq_left ha, dite_eq_left hab]
      have heq : (⟨addr - start, by omega⟩ : Fin (a + b)) =
          Fin.castAdd b ⟨addr - start, by omega⟩ := by ext; rfl
      rw [heq, Fin.append_left]
    · have hab : ¬(start ≤ addr ∧ addr < start + (a + b)) := by omega
      rw [dite_eq_right ha, dite_eq_right hab]

private theorem randFill_step_exec {w L_peak : ℕ} {r : ℕ}
    {rCur rEnd rMask rTmp rOne : Fin r} {x : RData r}
    (_hw : 0 < w)
    (hd : [rCur, rEnd, rMask, rTmp, rOne].Nodup)
    (hmask : x.regs rMask = 2 ^ w - 1)
    (hone : x.regs rOne = 1)
    (hfr_le : x.frontier ≤ L_peak)
    (hcur_lt : x.regs rCur < x.frontier)
    (hfit_succ : Fits w (x.regs rCur + 1)) :
    ExecRCodeSteps w
      (.seq (.rand rTmp rMask)
        (.seq (.op (.store rCur rTmp))
          (.op (.exactBin .add rCur rCur rOne))))
      x
      ((PMF.uniformOfFintype (Fin (2 ^ w))).map fun v =>
        ⟨⟨Function.update (Function.update x.regs rTmp v.val) rCur (x.regs rCur + 1),
          Function.update x.mem (x.regs rCur) v.val, x.frontier⟩, 3, true⟩)
      L_peak := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, ← ne_eq,
    List.nodup_nil, and_true] at hd
  obtain ⟨⟨hce, hcm, hct, hco⟩, ⟨_, _, _⟩, ⟨_, _⟩, hto, -⟩ := hd
  have hfit_mask : Fits w (2 ^ w - 1) := Nat.sub_lt (Nat.two_pow_pos w) one_pos
  have h1 := ExecRCodeSteps.rand (B := .exact) (w := w) (dst := rTmp) (src := rMask)
    hfr_le (hmask ▸ hfit_mask)
  have hrest : ∀ z ∈ ((ProbComp.unifFin (x.regs rMask)).eval.map fun k =>
        ({ data := x.set rTmp k.val, steps := 1, timed := true } : RCodeStepOutcome r)).support,
      ExecRCodeSteps w (.seq (.op (.store rCur rTmp)) (.op (.exactBin .add rCur rCur rOne)))
        z.data
        (PMF.pure ⟨⟨Function.update z.data.regs rCur (x.regs rCur + 1),
          Function.update x.mem (x.regs rCur) (z.data.regs rTmp), x.frontier⟩, 2, true⟩)
        L_peak := by
    intro z hz
    rw [PMF.mem_support_map_iff] at hz
    obtain ⟨k, _, rfl⟩ := hz
    have hs_store : RDemonicExec (B := .exact) w L_peak (.op (.store rCur rTmp))
        (x.set rTmp k.val) 1
        (· = (x.set rTmp k.val).write (x.regs rCur) k.val) := by
      have hcur_eq : (x.set rTmp k.val).regs rCur = x.regs rCur := by
        simp [RData.set, Function.update_of_ne hct]
      have htmp_eq : (x.set rTmp k.val).regs rTmp = k.val := by simp [RData.set]
      refine (RDemonicExec.store (w := w) (L_peak := L_peak)
        (a := rCur) (s := rTmp) (x := x.set rTmp k.val)
        hfr_le (by simpa [hcur_eq] using hcur_lt)).mono le_rfl ?_
      rintro _ rfl; simp [RData.write, hcur_eq, htmp_eq]
    have hs_add : RDemonicExec (B := .exact) w L_peak (.op (.exactBin .add rCur rCur rOne))
        ((x.set rTmp k.val).write (x.regs rCur) k.val) 1
        (· = ⟨Function.update (x.set rTmp k.val).regs rCur (x.regs rCur + 1),
          Function.update x.mem (x.regs rCur) k.val, x.frontier⟩) := by
      have hcur_eq : ((x.set rTmp k.val).write (x.regs rCur) k.val).regs rCur = x.regs rCur := by
        simp [RData.set, RData.write, Function.update_of_ne hct]
      have hone_eq : ((x.set rTmp k.val).write (x.regs rCur) k.val).regs rOne = 1 := by
        simp [RData.set, RData.write, Function.update_of_ne hto.symm, hone]
      refine (RDemonicExec.exactBin (w := w) (L_peak := L_peak)
        (x := (x.set rTmp k.val).write (x.regs rCur) k.val)
        (v := x.regs rCur + 1)
        hfr_le ?_ hfit_succ).mono le_rfl ?_
      · show BinOp.evalExact .add
          (((x.set rTmp k.val).write (x.regs rCur) k.val).regs rCur)
          (((x.set rTmp k.val).write (x.regs rCur) k.val).regs rOne) = some (x.regs rCur + 1)
        rw [hcur_eq, hone_eq]; rfl
      · rintro _ rfl; rfl
    refine ExecRCodeSteps.of_demonicExec (RDemonicExec.seq_eq hs_store hs_add) |>.congr_dist ?_
    simp [RData.set]
  have heq_sub : (2 ^ w - 1) + 1 = 2 ^ w := Nat.sub_add_cancel Nat.one_le_two_pow
  have h1' : ExecRCodeSteps (B := .exact) w (.rand rTmp rMask) x
      ((PMF.uniformOfFintype (Fin (2 ^ w))).map fun k =>
        ⟨x.set rTmp k.val, 1, true⟩) L_peak := by
    refine h1.congr_dist ?_
    rw [hmask]
    have hmap_u : (ProbComp.unifFin (2 ^ w - 1)).eval =
        (PMF.uniformOfFintype (Fin (2 ^ w))).map (finCongr heq_sub.symm) := by
      rw [ProbComp.eval_unifFin, PMF.uniformOfFintype_map_equiv]
    rw [hmap_u, PMF.map_comp]; rfl
  have hrest' : ∀ z ∈ ((PMF.uniformOfFintype (Fin (2 ^ w))).map fun k =>
        ({ data := x.set rTmp k.val, steps := 1, timed := true } : RCodeStepOutcome r)).support,
      ExecRCodeSteps (B := .exact) w
        (.seq (.op (.store rCur rTmp)) (.op (.exactBin .add rCur rCur rOne)))
        z.data
        (PMF.pure ⟨⟨Function.update z.data.regs rCur (x.regs rCur + 1),
          Function.update x.mem (x.regs rCur) (z.data.regs rTmp), x.frontier⟩, 2, true⟩)
        L_peak := by
    intro z hz
    refine hrest z ?_
    rw [PMF.mem_support_map_iff] at hz ⊢
    obtain ⟨k, _, rfl⟩ := hz
    exact ⟨⟨k.val, by omega⟩, by rw [ProbComp.eval_unifFin]; simp, rfl⟩
  have hseq := ExecRCodeSteps.seq h1' hrest'
  refine hseq.congr_dist ?_
  rw [PMF.bind_map]
  unfold PMF.map
  refine congrArg (PMF.bind _) (funext fun v => ?_)
  dsimp only [Function.comp_def]
  rw [PMF.pure_bind]
  simp only [RCodeStepOutcome.seqCombine, RData.set, Function.update_self, Bool.and_self]

/-- Exact step-counted `ExecRCodeSteps` specification of `randFillBatchCode` for writing
`k = endAddr - start` uniform `w`-bit words into `[start, start + k)` in `5 * k + 2` deterministic
instructions (`x.regs rEnd = start + k ≤ x.frontier`). -/
theorem randFillBatchCode_exec {w L_peak : ℕ} {r : ℕ}
    {rCur rEnd rMask rTmp rOne : Fin r}
    (hw : 0 < w) (hd : [rCur, rEnd, rMask, rTmp, rOne].Nodup)
    (k start : ℕ) (x : RData r)
    (hcur : x.regs rCur = start) (hend : x.regs rEnd = start + k)
    (hmask : x.regs rMask = 2 ^ w - 1) (hone : x.regs rOne = 1)
    (hfr_le : x.frontier ≤ L_peak) (hbound : start + k ≤ x.frontier)
    (hfit_end : Fits w (start + k)) :
    ExecRCodeSteps w (randFillBatchCode rCur rEnd rMask rTmp rOne) x
      ((PMF.uniformOfFintype (Fin k → Fin (2 ^ w))).map fun ws =>
        ⟨⟨if h : k = 0 then x.regs
          else Function.update (Function.update x.regs rTmp (ws ⟨k - 1, by omega⟩).val)
            rCur (start + k),
          writeWords x.mem start ws, x.frontier⟩, 5 * k + 2, true⟩)
      L_peak := by
  have hd_orig := hd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, ← ne_eq,
    List.nodup_nil, and_true] at hd
  obtain ⟨⟨hce, hcm, hct, hco⟩, ⟨hem, het, heo⟩, ⟨hmt, hmo⟩, hto, -⟩ := hd
  induction k generalizing start x with
  | zero =>
    have hstop : ¬(Cond.lt rCur rEnd).Holds x.toData := by
      simp [Cond.Holds, hcur, hend]
    have hloop : RDemonicExec (B := .exact) w L_peak
        (randFillBatchCode rCur rEnd rMask rTmp rOne) x 2 (· = x) :=
      RDemonicExec.loop_exit hfr_le hstop rfl
    refine (ExecRCodeSteps.of_demonicExec hloop).congr_dist ?_
    have h1 : (PMF.uniformOfFintype (Fin 0 → Fin (2 ^ w))).map
        (fun ws : Fin 0 → Fin (2 ^ w) =>
          ({ data := ⟨x.regs, writeWords x.mem start ws, x.frontier⟩,
             steps := 2, timed := true } : RCodeStepOutcome r)) =
        PMF.pure ⟨x, 2, true⟩ := by
      have hws : ∀ ws : Fin 0 → Fin (2 ^ w), writeWords x.mem start ws = x.mem := by
        intro ws; funext a; exact writeWords_apply_out _ _ _ (by omega)
      simp only [hws]
      exact PMF.map_const _ _
    simpa only [↓reduceDIte, Nat.mul_zero, zero_add] using h1.symm
  | succ m ih =>
    have hhold : (Cond.lt rCur rEnd).Holds x.toData := by
      simp [Cond.Holds, hcur, hend]
    have hcur_lt_fr : x.regs rCur < x.frontier := by rw [hcur]; omega
    have hfit_s : Fits w (x.regs rCur + 1) := by rw [hcur]; exact hfit_end.of_le (by omega)
    have hbody := randFill_step_exec (L_peak := L_peak) hw hd_orig hmask hone hfr_le hcur_lt_fr
      hfit_s
    have htail : ∀ z₁ ∈ ((PMF.uniformOfFintype (Fin (2 ^ w))).map fun v : Fin (2 ^ w) =>
        ({ data := ⟨Function.update (Function.update x.regs rTmp v.val) rCur (x.regs rCur + 1),
             Function.update x.mem (x.regs rCur) v.val, x.frontier⟩,
           steps := 3, timed := true } : RCodeStepOutcome r)).support,
        ExecRCodeSteps w (randFillBatchCode rCur rEnd rMask rTmp rOne) z₁.data
          ((PMF.uniformOfFintype (Fin m → Fin (2 ^ w))).map fun ws =>
            ⟨⟨if hm : m = 0 then z₁.data.regs
              else Function.update (Function.update z₁.data.regs rTmp (ws ⟨m - 1, by omega⟩).val)
                rCur (start + 1 + m),
              writeWords z₁.data.mem (start + 1) ws, x.frontier⟩, 5 * m + 2, true⟩)
          L_peak := by
      intro z₁ hz₁
      rw [PMF.mem_support_map_iff] at hz₁
      obtain ⟨v, _, rfl⟩ := hz₁
      refine ih (start + 1) _ ?_ ?_ ?_ ?_ hfr_le ?_ ?_
      · simp [hcur]
      · dsimp only
        rw [Function.update_of_ne hce.symm, Function.update_of_ne het, hend]; omega
      · dsimp only
        rw [Function.update_of_ne hcm.symm, Function.update_of_ne hmt, hmask]
      · dsimp only
        rw [Function.update_of_ne hco.symm, Function.update_of_ne hto.symm, hone]
      · dsimp only; omega
      · rw [show start + 1 + m = start + (m + 1) by omega]; exact hfit_end
    have hlp := ExecRCodeSteps.loop_iter hhold hbody htail
    refine hlp.congr_dist ?_
    have hprod : (PMF.uniformOfFintype (Fin (2 ^ w))).bind (fun v =>
        (PMF.uniformOfFintype (Fin m → Fin (2 ^ w))).map fun ws => Fin.cons v ws) =
        PMF.uniformOfFintype (Fin (m + 1) → Fin (2 ^ w)) := by
      have heq := PMF.uniformOfFintype_map_equiv
        (Fin.consEquiv (fun _ : Fin (m + 1) => Fin (2 ^ w)))
      rw [← heq, ← PMF.uniformOfFintype_prod, PMF.map_bind]
      simp only [PMF.map_comp, Function.comp_def]; rfl
    rw [← hprod, PMF.map_bind, PMF.bind_map]
    simp only [PMF.map_comp, Function.comp_def, RCodeStepOutcome.loopCombine, Bool.and_self]
    congr 1; funext v; congr 1; funext ws
    have hst : 3 + (5 * m + 2) + 2 = 5 * (m + 1) + 2 := by omega
    rw [hst]
    refine congrArg (fun d => ({ data := d, steps := 5 * (m + 1) + 2, timed := true } :
      RCodeStepOutcome r)) ?_
    ext i
    · by_cases hm : m = 0
      · subst hm
        simp only [↓reduceDIte, Nat.add_eq_zero_iff, one_ne_zero, and_false, hcur]
        by_cases hic : i = rCur
        · subst hic; simp
        · rw [Function.update_of_ne hic, Function.update_of_ne hic]
          by_cases hit : i = rTmp
          · subst hit; simp
          · rw [Function.update_of_ne hit, Function.update_of_ne hit]
      · simp only [hm, ↓reduceDIte, show m + 1 ≠ 0 by omega, hcur]
        by_cases hic : i = rCur
        · subst hic; simp [show start + 1 + m = start + (m + 1) by omega]
        · rw [Function.update_of_ne hic, Function.update_of_ne hic]
          by_cases hit : i = rTmp
          · subst hit
            simp only [Function.update_self]
            have hidx : (⟨m + 1 - 1, by omega⟩ : Fin (m + 1)) =
                (⟨m - 1, by omega⟩ : Fin m).succ := by ext; simp; omega
            rw [hidx, Fin.cons_succ]
          · rw [Function.update_of_ne hit, Function.update_of_ne hic, Function.update_of_ne hit,
              Function.update_of_ne hit]
    · dsimp only
      by_cases ha : i = start
      · subst ha
        rw [writeWords_apply_out _ _ _ (by omega), hcur, Function.update_self]
        rw [show i = i + 0 by omega, writeWords_apply_in _ _ _ (Nat.succ_pos _)]
        simp
      · by_cases hin : start + 1 ≤ i ∧ i < start + 1 + m
        · unfold writeWords
          rw [dite_eq_left hin, dite_eq_left (by omega : start ≤ i ∧ i < start + (m + 1))]
          have : (⟨i - start, by omega⟩ : Fin (m + 1)) =
              (⟨i - (start + 1), by omega⟩ : Fin m).succ := by ext; simp; omega
          rw [this, Fin.cons_succ]
        · rw [writeWords_apply_out _ _ _ hin, hcur, Function.update_of_ne ha,
            writeWords_apply_out _ _ _ (by omega)]
    · rfl

/-- Single-epoch hash-seed construction extracting a uniform `EpochHashSeeds c U N` from the exact
uniform `w`-bit words sampled into `[metaBase + offBktHash, metaBase + offBktMeta c w N)`. -/
theorem uniform_epochHashSeeds_of_words {c U w N : ℕ} (hw : 0 < w) :
    let wB := BitPackedDoubleTabulation.topWords w (cTabWhp c) (dTabWhp c) (bCharWhp N) +
      BitPackedDoubleTabulation.botWords w (dTabWhp c) (bCharWhp N) (bWhp N)
    let wF := BitPackedDoubleTabulation.topWords w (cTabWhp c) (dTabWhp c) (bCharWhp N) +
      BitPackedDoubleTabulation.botWords w (dTabWhp c) (bCharWhp N) (fpBitsWhp N)
    let combine :
        Fin (2 ^ (redWidthWhp U - 1)) → (Fin wB → Fin (2 ^ w)) →
        Fin (2 ^ (redWidthWhp U - 1)) → (Fin wF → Fin (2 ^ w)) → EpochHashSeeds c U N :=
      fun aB wsB aF wsF =>
        let pB := BitPackedDoubleTabulation.tablesOfWords w (cTabWhp c) (dTabWhp c) (bCharWhp N)
          (bWhp N) hw wsB
        let pF := BitPackedDoubleTabulation.tablesOfWords w (cTabWhp c) (dTabWhp c) (bCharWhp N)
          (fpBitsWhp N) hw wsF
        ⟨⟨aB, pB.1, pB.2⟩, ⟨aF, pF.1, pF.2⟩⟩
    ((PMF.uniformOfFintype (Fin (2 ^ (redWidthWhp U - 1)))).bind fun aB =>
      (PMF.uniformOfFintype (Fin wB → Fin (2 ^ w))).bind fun wsB =>
        (PMF.uniformOfFintype (Fin (2 ^ (redWidthWhp U - 1)))).bind fun aF =>
          (PMF.uniformOfFintype (Fin wF → Fin (2 ^ w))).map fun wsF =>
            combine aB wsB aF wsF) =
      PMF.uniformOfFintype (EpochHashSeeds c U N) := by
  intro wB wF combine
  have huB := BitPackedDoubleTabulation.uniformOfFintype_map_tablesOfWords w
    (cTabWhp c) (dTabWhp c) (bCharWhp N) (bWhp N) hw
  have huF := BitPackedDoubleTabulation.uniformOfFintype_map_tablesOfWords w
    (cTabWhp c) (dTabWhp c) (bCharWhp N) (fpBitsWhp N) hw
  have hpushF : ∀ aB wsB aF,
      (PMF.uniformOfFintype (Fin wF → Fin (2 ^ w))).map (fun wsF => combine aB wsB aF wsF) =
      (PMF.uniformOfFintype
        (DoubleTabTopSeed (cTabWhp c + 1) (dTabWhp c) (bCharWhp N) ×
          DoubleTabBotSeed (dTabWhp c) (bCharWhp N) (fpBitsWhp N))).map
        (fun pF =>
          let pB := BitPackedDoubleTabulation.tablesOfWords w (cTabWhp c) (dTabWhp c)
            (bCharWhp N) (bWhp N) hw wsB
          EpochHashSeeds.mk (aB, pB.1, pB.2) (aF, pF.1, pF.2)) := by
    intro aB wsB aF
    rw [← huF, PMF.map_comp]; rfl
  simp_rw [hpushF]
  have hfp_eq : ∀ b : BktSeed c U N,
      (PMF.uniformOfFintype (Fin (2 ^ (redWidthWhp U - 1)))).bind (fun aF =>
        (PMF.uniformOfFintype
          (DoubleTabTopSeed (cTabWhp c + 1) (dTabWhp c) (bCharWhp N) ×
            DoubleTabBotSeed (dTabWhp c) (bCharWhp N) (fpBitsWhp N))).map
          fun pF => EpochHashSeeds.mk b (aF, pF.1, pF.2)) =
      (PMF.uniformOfFintype (FpSeed c U N)).map fun f => EpochHashSeeds.mk b f := by
    intro b
    have hprod := (PMF.uniformOfFintype_prod
      (Fin (2 ^ (redWidthWhp U - 1)))
      (DoubleTabTopSeed (cTabWhp c + 1) (dTabWhp c) (bCharWhp N) ×
        DoubleTabBotSeed (dTabWhp c) (bCharWhp N) (fpBitsWhp N))).symm
    change _ = (PMF.uniformOfFintype _).map fun f => EpochHashSeeds.mk b f
    rw [hprod, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]
  have hb_step : ∀ aB : Fin (2 ^ (redWidthWhp U - 1)),
      (PMF.uniformOfFintype (Fin wB → Fin (2 ^ w))).bind (fun wsB =>
        (PMF.uniformOfFintype (Fin (2 ^ (redWidthWhp U - 1)))).bind fun aF =>
          (PMF.uniformOfFintype
            (DoubleTabTopSeed (cTabWhp c + 1) (dTabWhp c) (bCharWhp N) ×
              DoubleTabBotSeed (dTabWhp c) (bCharWhp N) (fpBitsWhp N))).map
            fun pF =>
              let pB := BitPackedDoubleTabulation.tablesOfWords w (cTabWhp c) (dTabWhp c)
                (bCharWhp N) (bWhp N) hw wsB
              EpochHashSeeds.mk (aB, pB.1, pB.2) (aF, pF.1, pF.2)) =
      (PMF.uniformOfFintype
        (DoubleTabTopSeed (cTabWhp c + 1) (dTabWhp c) (bCharWhp N) ×
          DoubleTabBotSeed (dTabWhp c) (bCharWhp N) (bWhp N))).bind (fun pB =>
        (PMF.uniformOfFintype (FpSeed c U N)).map fun f =>
          EpochHashSeeds.mk (aB, pB.1, pB.2) f) := by
    intro aB
    have hinner : ∀ wsB : Fin wB → Fin (2 ^ w),
        (PMF.uniformOfFintype (Fin (2 ^ (redWidthWhp U - 1)))).bind (fun aF =>
          (PMF.uniformOfFintype
            (DoubleTabTopSeed (cTabWhp c + 1) (dTabWhp c) (bCharWhp N) ×
              DoubleTabBotSeed (dTabWhp c) (bCharWhp N) (fpBitsWhp N))).map
            fun pF =>
              let pB := BitPackedDoubleTabulation.tablesOfWords w (cTabWhp c) (dTabWhp c)
                (bCharWhp N) (bWhp N) hw wsB
              EpochHashSeeds.mk (aB, pB.1, pB.2) (aF, pF.1, pF.2)) =
        (PMF.uniformOfFintype (FpSeed c U N)).map fun f =>
          let pB := BitPackedDoubleTabulation.tablesOfWords w (cTabWhp c) (dTabWhp c)
            (bCharWhp N) (bWhp N) hw wsB
          EpochHashSeeds.mk (aB, pB.1, pB.2) f := fun wsB => hfp_eq _
    simp_rw [hinner]
    rw [← huB, PMF.bind_map]
    rfl
  simp_rw [hb_step]
  have hb_prod :
      (PMF.uniformOfFintype (Fin (2 ^ (redWidthWhp U - 1)))).bind (fun aB =>
        (PMF.uniformOfFintype
          (DoubleTabTopSeed (cTabWhp c + 1) (dTabWhp c) (bCharWhp N) ×
            DoubleTabBotSeed (dTabWhp c) (bCharWhp N) (bWhp N))).bind fun pB =>
          (PMF.uniformOfFintype (FpSeed c U N)).map fun f =>
            EpochHashSeeds.mk (aB, pB.1, pB.2) f) =
      (PMF.uniformOfFintype (BktSeed c U N)).bind fun b =>
        (PMF.uniformOfFintype (FpSeed c U N)).map fun f => EpochHashSeeds.mk b f := by
    have hp := (PMF.uniformOfFintype_prod
      (Fin (2 ^ (redWidthWhp U - 1)))
      (DoubleTabTopSeed (cTabWhp c + 1) (dTabWhp c) (bCharWhp N) ×
        DoubleTabBotSeed (dTabWhp c) (bCharWhp N) (bWhp N))).symm
    symm
    rw [hp, PMF.bind_bind]
    refine congrArg (PMF.bind _) (funext fun aB => ?_)
    rw [PMF.bind_map]; rfl
  let eqv : EpochHashSeeds c U N ≃ BktSeed c U N × FpSeed c U N :=
    { toFun := fun s => (s.bkt, s.fp)
      invFun := fun p => ⟨p.1, p.2⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  rw [hb_prod, ← PMF.uniformOfFintype_map_equiv eqv.symm]
  have hpe := (PMF.uniformOfFintype_prod (BktSeed c U N) (FpSeed c U N)).symm
  rw [hpe, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  rfl

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp
