/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.LargeEpochRemove
import CslibFrontier.Computability.WordRAM.Realization.BoundedTactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Top-Level Large-Epoch Fast/Fallback Operations (`O_c(1)` WHP)

This module composes the low-level large-epoch operations into a complete, `pBase`-parameterized
large-epoch dictionary supporting **`query`**, **`insert`**, **`delete`**, and **`popAny`** with
exact unconditional correctness on **100%** of hash seeds (`LargeEpochInv`) and `O_c(1)` worst-case
per-operation step complexity (`largeFastStepCost c`) throughout any epoch satisfying
`GoodEpochSeeds win seeds`.

## Main definitions

* `fastFallbackQueryProg`, `fastFallbackInsertProg`, `fastFallbackDeleteProg`,
  `fastFallbackPopAnyProg`: `pBase`-guarded wrappers over the exact `FallbackPool` operations
  (`RealizesBounded .exact`, `¬ReadsWidth`).
* `fastDeleteProg`, `fastInsertProg`: fast-mode (`fallbackMode = 0`) `delete` and `insert`
  programs, backed by `fastProbeProg`, `fastRemoveAtProg`, `drainTrySteps5Prog`,
  `fastShadowSteps8Prog`, `fastBpAppendProg`, `fastBufInsertProg`, `advanceSubEpochProg`, and the
  in-place `1 · OPT` transition `fastEnterFallbackProg`.
* `largeEpochQueryProg`, `largeEpochInsertProg`, `largeEpochDeleteProg`, `largeEpochPopAnyProg`:
  mode-dispatching large-epoch operations reading `fallbackMode := mem (metaBase + 2)`.
* `LargeEpochInv`: unified large-epoch state invariant (`FastEpochInv` when `mode = 0`,
  `FallbackLayout.StateInv` when `mode = 1`).
* `CurBufKeysIn`: active `BufCur` key containment invariant used alongside `FastSubEpochGood` for
  seamless rollover `e → eNext`.
* `largeFastStepCost`: `c`-only worst-case cost bound for every large-epoch operation in fast mode.

## Main results

* `fastDeleteProg_spec`, `fastDeleteProg_good`: unconditional fast-mode `delete` and good-seed
  invariant preservation.
* `fastInsertProg_spec`, `fastInsertProg_good`: unconditional `insert` (either stays in
  `FastEpochInv` with `≤ fastInsertCost fl.c` or transitions cleanly to `FallbackLayout.StateInv`),
  and under `GoodEpochSeeds win seeds` **never** enters fallback.
* `fastInitZeroedProg_good`: establishes `FastSubEpochGood 0 0` and `CurBufKeysIn ... ∅` right
  after `fastInitZeroedProg`.
* `largeEpochQueryProg_spec`, `largeEpochInsertProg_spec`, `largeEpochDeleteProg_spec`,
  `largeEpochPopAnyProg_spec`: unified mode-dispatching exact specifications on **100%** of seeds.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

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

attribute [local simp] Realization.memoryCost_bind'

/-! ## Section 1: Active `BufCur` Containment and Bucket-Count Helper -/

/-- All active keys currently indexed in `BufCur` lie in the finite set `S`. -/
@[expose] def CurBufKeysIn {fl : FastEpochLayout} (seeds : EpochHashSeeds fl.c fl.U fl.N)
    (mem : ℕ → ℕ) (S : Finset (Fin fl.U)) : Prop :=
  ∀ id b loc (u : Fin fl.U),
    bufCheckSlot (extractBufTrie (fl.trieL (extractFastMeta fl mem).curBufRole) mem) id =
      some (b, loc) →
    b < numBucketsWhp fl.N →
    loc < (extractBlockPool fl.mp mem).bktCount b →
    fastKeyAt fl seeds.bkt mem b loc = u.val →
    u ∈ S

theorem CurBufKeysIn.mono {fl : FastEpochLayout} {seeds : EpochHashSeeds fl.c fl.U fl.N}
    {mem : ℕ → ℕ} {S T : Finset (Fin fl.U)} (hsub : S ⊆ T) (h : CurBufKeysIn seeds mem S) :
    CurBufKeysIn seeds mem T :=
  fun id b loc u hchk hb hl hk => hsub (h id b loc u hchk hb hl hk)

/-- Unified large-epoch invariant: `ParamTable`, plus either fast mode (`mode = 0`, `FastEpochInv`)
or fallback mode (`mode = 1`, `FallbackLayout.StateInv`). -/
@[expose] def LargeEpochInv (fl : FastEpochLayout) (slack : ℕ)
    (seeds : EpochHashSeeds fl.c fl.U fl.N) (mem : ℕ → ℕ)
    (s_abs : Fin fl.U → Option (Fin fl.V)) : Prop :=
  fl.ParamTable mem ∧
  (mem (fl.metaBase + 2) = 0 ∧ FastEpochInv fl slack seeds mem s_abs ∨
    mem (fl.metaBase + 2) = 1 ∧ fl.fbL.StateInv slack seeds.bkt mem s_abs)

theorem LargeEpochInv.fast {fl : FastEpochLayout} {slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {mem : ℕ → ℕ} {s_abs : Fin fl.U → Option (Fin fl.V)}
    (h : FastEpochInv fl slack seeds mem s_abs) :
    LargeEpochInv fl slack seeds mem s_abs :=
  ⟨h.param_table, Or.inl ⟨h.mode_zero, h⟩⟩

theorem LargeEpochInv.fallback {fl : FastEpochLayout} {slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {mem : ℕ → ℕ} {s_abs : Fin fl.U → Option (Fin fl.V)}
    (hpt : fl.ParamTable mem) (h : fl.fbL.StateInv slack seeds.bkt mem s_abs) :
    LargeEpochInv fl slack seeds mem s_abs :=
  ⟨hpt, Or.inr ⟨h.mode_eq, h⟩⟩

theorem LargeEpochInv.nSide_eq_fallback_or_fast {fl : FastEpochLayout} {slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {mem : ℕ → ℕ} {s_abs : Fin fl.U → Option (Fin fl.V)}
    (h : LargeEpochInv fl slack seeds mem s_abs) :
    (mem (fl.metaBase + 2) = 0 →
      (extractBlockPool fl.mp mem).nSide ≤ fl.N ∧ FastEpochInv fl slack seeds mem s_abs) ∧
    (mem (fl.metaBase + 2) ≠ 0 →
      mem (fl.metaBase + 2) = 1 ∧ fl.fbL.StateInv slack seeds.bkt mem s_abs) := by
  rcases h.2 with ⟨hm0, hf⟩ | ⟨hm1, hfb⟩
  · exact ⟨fun _ => ⟨hf.bp_inv.2.1, hf⟩, fun hne => absurd hm0 hne⟩
  · exact ⟨fun h0 => absurd (h0.symm.trans hm1) Nat.zero_ne_one, fun _ => ⟨hm1, hfb⟩⟩

/-- In fast mode (`FastEpochInvGen`), the physical item count `bp.bktCount b` in bucket `b` is at
most the cardinality of live keys in bucket `b` inside any `Finset` `S` covering `s_abs`. When a
fresh key `u ∉ s_abs` with `epochBucket u = b` belongs to `S`, the inequality is strict. -/
theorem bktCount_lt_of_snap_insert {slackCur : ℕ} {fl : FastEpochLayout} {slack b : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {mem : ℕ → ℕ}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {S : Finset (Fin fl.U)}
    (hinv : FastEpochInvGen slackCur fl slack seeds mem s_abs)
    (hb : b < numBucketsWhp fl.N) {u : Fin fl.U} (habs : s_abs u = none)
    (hb_u : epochBucket fl.c fl.U fl.N seeds.bkt u = b) {hv_pos : 0 < fl.V}
    (hcover : ∀ k : Fin fl.U, Function.update s_abs u (some ⟨0, hv_pos⟩) k ≠ none → k ∈ S) :
    (extractBlockPool fl.mp mem).bktCount b <
      (S.filter fun k => epochBucket fl.c fl.U fl.N seeds.bkt k = b).card := by
  classical
  set bp := extractBlockPool fl.mp mem
  let keyOf : ℕ → Fin fl.U := fun loc =>
    if hloc : loc < bp.bktCount b then
      (hinv.bktSlot_refines hb hloc).choose
    else u
  have hkey_spec : ∀ loc (hloc : loc < bp.bktCount b),
      fastKeyAt fl seeds.bkt mem b loc = (keyOf loc).val ∧
      epochBucket fl.c fl.U fl.N seeds.bkt (keyOf loc) = b ∧
      s_abs (keyOf loc) ≠ none := fun loc hloc => by
    dsimp only [keyOf]; rw [dite_eq_left hloc]
    have hs := (hinv.bktSlot_refines hb hloc).choose_spec
    obtain ⟨v, hu, _, hb_k, _, hs_k⟩ := hs
    exact ⟨hu.symm, hb_k, by rw [hs_k]; exact Option.some_ne_none _⟩
  let liveBkt : Finset (Fin fl.U) :=
    (Finset.range (bp.bktCount b)).image keyOf
  have hinj : Set.InjOn keyOf (Finset.range (bp.bktCount b) : Set ℕ) := by
    intro l₁ hl₁ l₂ hl₂ heq
    rw [Finset.mem_coe, Finset.mem_range] at hl₁ hl₂
    have h1 := hkey_spec l₁ hl₁
    have h2 := hkey_spec l₂ hl₂
    have hkeq : fastKeyAt fl seeds.bkt mem b l₁ = fastKeyAt fl seeds.bkt mem b l₂ := by
      rw [h1.1, h2.1, heq]
    have hcv := hinv.bp_inv.1.core
    have hq1 := (hinv.bktSlot_refines hb hl₁).choose_spec
    have hq2 := (hinv.bktSlot_refines hb hl₂).choose_spec
    have hkey1 : (hinv.bktSlot_refines hb hl₁).choose = keyOf l₁ := by
      dsimp only [keyOf]; rw [dite_eq_left hl₁]
    have hkey2 : (hinv.bktSlot_refines hb hl₂).choose = keyOf l₂ := by
      dsimp only [keyOf]; rw [dite_eq_left hl₂]
    have hp1 := hcv.toPhys_lt hb hl₁
    have hp2 := hcv.toPhys_lt hb hl₂
    have ho1 : ((extractBlockPool fl.bpL.mp mem).ownerOf
        ((extractBlockPool fl.bpL.mp mem).toPhys b l₁)).1 = b := by
      rw [hcv.ownerOf_toPhys hb hl₁]
    have ho2 : ((extractBlockPool fl.bpL.mp mem).ownerOf
        ((extractBlockPool fl.bpL.mp mem).toPhys b l₂)).1 = b := by
      rw [hcv.ownerOf_toPhys hb hl₂]
    obtain ⟨_, _, _, _, hqp1, _⟩ := hq1
    obtain ⟨_, _, _, _, hqp2, _⟩ := hq2
    have hq_eq : (slotIoPairAt fl.io mem (bp.toPhys b l₁)).1 =
        (slotIoPairAt fl.io mem (bp.toPhys b l₂)).1 := by
      change (bpPairAt fl.bpL mem b l₁).1 = (bpPairAt fl.bpL mem b l₂).1
      rw [← hqp1, ← hqp2, hkey1, hkey2, heq]
    have hpe := hinv.refines.slot_inj _ hp1 _ hp2 (ho1.trans ho2.symm) hq_eq
    have hle := congrArg (fun x => ((extractBlockPool fl.bpL.mp mem).ownerOf x).2) hpe
    rw [hcv.ownerOf_toPhys hb hl₁, hcv.ownerOf_toPhys hb hl₂] at hle
    exact hle
  have hcard : liveBkt.card = bp.bktCount b := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hsub : liveBkt ⊆ S.filter fun k => epochBucket fl.c fl.U fl.N seeds.bkt k = b := by
    intro k hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨l, hl, rfl⟩
    rw [Finset.mem_range] at hl
    obtain ⟨_, hbk, hne⟩ := hkey_spec l hl
    rw [Finset.mem_filter]
    refine ⟨hcover (keyOf l) ?_, hbk⟩
    by_cases hku : keyOf l = u
    · rw [hku, Function.update_self]; exact Option.some_ne_none _
    · rwa [Function.update_of_ne hku]
  have hu_mem : u ∈ S.filter fun k => epochBucket fl.c fl.U fl.N seeds.bkt k = b := by
    rw [Finset.mem_filter]
    refine ⟨hcover u (by rw [Function.update_self]; exact Option.some_ne_none _), hb_u⟩
  have hu_nmem : u ∉ liveBkt := by
    intro hu_in
    rw [Finset.mem_image] at hu_in
    rcases hu_in with ⟨l, hl, hlu⟩
    rw [Finset.mem_range] at hl
    exact (hkey_spec l hl).2.2 (by rw [hlu, habs])
  have hss : liveBkt ⊂ S.filter fun k => epochBucket fl.c fl.U fl.N seeds.bkt k = b :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun he => hu_nmem (he ▸ hu_mem)⟩
  rw [← hcard]
  exact Finset.card_lt_card hss

/-- Bridge `fastBktReady` bucket count directly from `GoodBktSeed`. -/
theorem bktCount_lt_capMax_of_good {slackCur : ℕ} {fl : FastEpochLayout} {slack b : ℕ}
    {win : EpochWindowSpec fl.c fl.U fl.N}
    {seeds : EpochHashSeeds fl.c fl.U fl.N}
    (hgood : GoodEpochSeeds win seeds)
    {mem : ℕ → ℕ} {s_abs : Fin fl.U → Option (Fin fl.V)}
    (hinv : FastEpochInvGen slackCur fl slack seeds mem s_abs)
    (hb : b < numBucketsWhp fl.N) {u : Fin fl.U} (v : Fin fl.V) (habs : s_abs u = none)
    (hb_u : epochBucket fl.c fl.U fl.N seeds.bkt u = b)
    (t : Fin win.numSnaps)
    (hsnap : ∀ k : Fin fl.U, Function.update s_abs u (some v) k ≠ none → k ∈ win.snaps t) :
    (extractBlockPool fl.mp mem).bktCount b < capMaxWhp fl.N := by
  have hv_pos : 0 < fl.V := Nat.zero_lt_of_lt v.isLt
  have hcov : ∀ k : Fin fl.U, Function.update s_abs u (some ⟨0, hv_pos⟩) k ≠ none →
      k ∈ win.snaps t := fun k hk => by
    apply hsnap k
    by_cases hku : k = u
    · rw [hku, Function.update_self]; exact Option.some_ne_none _
    · rw [Function.update_of_ne hku] at hk ⊢; exact hk
  exact (bktCount_lt_of_snap_insert hinv hb habs hb_u (hv_pos := hv_pos) hcov).trans_le
    (hgood.1.1 t b hb)

/-- Exact proof-irrelevant bridge giving `FastLayoutReady` from a fallback state (`ParamTable`). -/
theorem fastLayoutReady_of_fallback {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {mem : ℕ → ℕ} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (hmem : s.mem = mem)
    (hv : fl.Valid w s.frontier) (hpt : fl.ParamTable mem)
    (hinv : fl.fbL.StateInv slack seeds.bkt mem s_abs)
    (hfp_lt : mem fl.fpHashBase < 2 ^ (redWidthWhp fl.U - 1)) :
    FastLayoutReady w fl s := by
  rw [← hmem] at hpt hinv hfp_lt
  exact ⟨hv, hpt, hinv.seed_bkt.1 ▸ seeds.bkt.1.isLt, hfp_lt⟩

/-! ## Section 2: `pBase`-Guarded Fallback Wrappers (`¬ReadsWidth`) -/

private theorem evalSalted_ready_bounds' {w : ℕ} {fl : FastEpochLayout} {s : Memory.State}
    (hr : FastLayoutReady w fl s) :
    0 < redWidthWhp fl.U ∧
    redWidthWhp fl.U ≤ w ∧
    bCharWhp fl.N < w ∧
    bWhp fl.N < w ∧
    fpBitsWhp fl.N < w ∧
    dTabWhp fl.c < 2 ^ w ∧
    cTabWhp fl.c + 1 < 2 ^ w ∧
    BitPackedDoubleTabulation.topEntries (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) < 2 ^ w ∧
    BitPackedDoubleTabulation.botEntries (dTabWhp fl.c) (bCharWhp fl.N) < 2 ^ w ∧
    fl.bktHashBase + BitPackedDoubleTabulation.space w (cTabWhp fl.c) (dTabWhp fl.c)
      (bCharWhp fl.N) (bWhp fl.N) ≤ s.frontier := by
  obtain ⟨hv, _, _, _⟩ := hr
  have hw_eq := hv.w_eq
  obtain ⟨_, _, _, hbc_w, hbw_w, hfp_w, _, _, _, htop_le, hbot_le, _, _, _, _, _, _, _, _, _⟩ :=
    largeEpoch_param_bounds hv.thresh_le hv.N_le_U hv.fits_U
  have hN_w : fl.N < 2 ^ w := lt_of_le_of_lt hv.N_le_U hv.fits_U
  have hbc1 : 1 ≤ 2 ^ bCharWhp fl.N := Nat.one_le_two_pow
  have hc1_le : cTabWhp fl.c + 1 ≤
      BitPackedDoubleTabulation.topEntries (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) := by
    unfold BitPackedDoubleTabulation.topEntries dTabWhp
    have hq := le_qTabWhp fl.c
    have hd_pos : 1 ≤ 2 * qTabWhp fl.c * (cTabWhp fl.c + 1) := by nlinarith
    calc cTabWhp fl.c + 1 ≤ (cTabWhp fl.c + 1) * (2 * qTabWhp fl.c * (cTabWhp fl.c + 1)) :=
          Nat.le_mul_of_pos_right _ hd_pos
      _ ≤ _ := Nat.le_mul_of_pos_right _ hbc1
  have hd_le : dTabWhp fl.c ≤ BitPackedDoubleTabulation.botEntries (dTabWhp fl.c) (bCharWhp fl.N) :=
    Nat.le_mul_of_pos_right _ hbc1
  have hend := offEpochEnd_eq_epochMetaWordsWhp (c := fl.c) (w := fl.w) hv.thresh_le
  have hmf := hv.meta_frontier
  subst hw_eq
  refine ⟨redWidthWhp_pos fl.U, hv.redWidth_le, hbc_w, hbw_w, hfp_w,
    lt_of_le_of_lt (hd_le.trans hbot_le) hN_w,
    lt_of_le_of_lt (hc1_le.trans htop_le) hN_w,
    lt_of_le_of_lt htop_le hN_w,
    lt_of_le_of_lt hbot_le hN_w, ?_⟩
  dsimp only [FastEpochLayout.bktHashBase]
  unfold offEpochEnd offPageTail offPageDir offTrieItem offTrieNode offTrieChild
    offBTreeVals offBTreeKeys offBTreeMeta offTailOwner offSlabOwner offTailDir offSlabDir
    offBktMeta offFpHash at hend
  omega

private theorem feistelSplitPre_of_fastReady {fl : FastEpochLayout} {w u_val : ℕ}
    {s : Memory.State} (hr : FastLayoutReady w fl s) (hu_le : u_val ≤ fl.U - 1) :
    FeistelSplitPre w (fl.feistelCtx, u_val) s := by
  have ⟨hv, _, hbkt, _⟩ := hr
  obtain ⟨hw0, hw0_le, hbc_w, hbw_w, _, hd_lt, hc1_lt, htop_lt, hbot_lt, hfr_bkt⟩ :=
    evalSalted_ready_bounds' hr
  have hU_pos : 0 < fl.U := lt_of_lt_of_le (whpThreshold_pos fl.c)
    (hv.thresh_le.trans hv.N_le_U)
  have hu_lt_U : u_val < fl.U := by omega
  have hu_lt_w0 : u_val < 2 ^ redWidthWhp fl.U :=
    hu_lt_U.trans_le (le_two_pow_redWidthWhp fl.U)
  have hq_lt_w0 : u_val >>> bWhp fl.N < 2 ^ redWidthWhp fl.U :=
    (Nat.shiftRight_le _ _).trans_lt hu_lt_w0
  exact ⟨hbw_w, hu_lt_w0, hv.w_pos, hv.w_eq, hw0, hw0_le, hbc_w, hbw_w.le,
    by rw [hv.w_eq]; rfl, hbkt, Nat.two_pow_pos _, hq_lt_w0, hd_lt, hc1_lt,
    htop_lt, hbot_lt, hfr_bkt⟩

private theorem feistelReconPre_of_fastReady {fl : FastEpochLayout} {w bkt q_val : ℕ}
    {s : Memory.State} (hr : FastLayoutReady w fl s)
    (hq : q_val < 2 ^ (redWidthWhp fl.U - bWhp fl.N)) :
    FeistelReconPre w (fl.feistelCtx, (bkt, q_val)) s := by
  have ⟨hv, _, hbkt, _⟩ := hr
  obtain ⟨hw0, hw0_le, hbc_w, hbw_w, _, hd_lt, hc1_lt, htop_lt, hbot_lt, hfr_bkt⟩ :=
    evalSalted_ready_bounds' hr
  have hbw_pos : 1 ≤ bWhp fl.N := by
    have hM := hv.mp_valid.M_ge
    dsimp only [FastEpochLayout.mp, epochBpMetaLayout] at hM
    unfold numBucketsWhp at hM
    by_contra hz; have h0 : bWhp fl.N = 0 := by omega
    rw [h0] at hM; omega
  have hbw_kb : bWhp fl.N ≤ keyBits fl.U := by
    unfold bWhp keyBits
    exact (Nat.sub_le _ _).trans ((Nat.log_mono_right hv.N_le_U).trans (Nat.log_le_clog 2 fl.U))
  have hrw_eq : redWidthWhp fl.U = keyBits fl.U := max_eq_right (by omega)
  have hq_lt : q_val < 2 ^ quotBitsWhp fl.U fl.N := by rwa [hrw_eq] at hq
  have hsum_w : quotBitsWhp fl.U fl.N + bWhp fl.N ≤ w := by
    unfold quotBitsWhp; rw [Nat.sub_add_cancel hbw_kb]
    exact Nat.clog_le_of_le_pow hv.fits_U.le
  have hq_w0 : q_val < 2 ^ redWidthWhp fl.U :=
    lt_of_lt_of_le hq_lt (two_pow_quotBitsWhp_le_redWidthWhp fl.U fl.N)
  exact ⟨quotBitsWhp fl.U fl.N, hbw_w, hsum_w, hq_lt,
    hv.w_pos, hv.w_eq, hw0, hw0_le, hbc_w, hbw_w.le, by rw [hv.w_eq]; rfl, hbkt,
    Nat.two_pow_pos _, hq_w0, hd_lt, hc1_lt, htop_lt, hbot_lt, hfr_bkt⟩

/-- Fallback `query(u)` loaded via `pBase` (`¬ReadsWidth`). -/
def fastFallbackQueryProg : ℕ × ℕ → Memory.Prog (ℕ × ℕ)
  | (pBase, u_val) => do
    let uMax ← Memory.read (pBase + 46)
    if u_val ≤ uMax then do
      let fctx ← loadHashStaticCtxProg (pBase, 0)
      let bpCtx ← loadBlockPoolCtxProg pBase
      fallbackQueryProg ((fctx, bpCtx), u_val)
    else
      pure (0, 0)

theorem realizesBounded_fastFallbackQuery :
    RealizesBounded .exact fastFallbackQueryProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hlf := realizesBounded_loadHashStaticCtx
  have hlb := realizesBounded_loadBlockPoolCtx
  have hfq := realizesBounded_fallbackQuery
  realize
  all_goals (
    rcases d with ⟨pBase, u_val⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_loadHashStaticCtxProg,
      runClient_state_loadBlockPoolCtxProg] at *
    first | exact hw6 | exact hp | omega | (
      have hum : s.mem (fl.pBase + 46) = fl.U - 1 := hr.2.1 46 (by decide)
      have hf_res := clientResult_loadFeistelCtx (s := s) hr.2.1
      have hb_res := clientResult_loadBlockPoolCtxProg (s := s) hr.2.1
      simp only [StateTransitionSpec.clientResult] at hf_res hb_res ⊢
      try rw [hf_res]
      try rw [hb_res]
      first
      | exact feistelSplitPre_of_fastReady hr (by omega)
      | (dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
         rw [BpMetaLayout.ofCtx_toCtx]; exact hr.1.mp_valid)
      | (dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
         rw [SlotIoLayout.ofCtx_toCtx]; exact hr.1.io_valid)))

theorem fastFallbackQueryProg_spec {fl : FastEpochLayout} {w slack : ℕ}
    {θ_bkt : BktSeed fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier) (hpt : fl.ParamTable s.mem)
    (hinv : fl.fbL.StateInv slack θ_bkt s.mem s_abs) (u : Fin fl.U) :
    (Memory.spec 0).clientState s (fastFallbackQueryProg (fl.pBase, u.val)) = s ∧
    (Memory.spec 0).clientResult s (fastFallbackQueryProg (fl.pBase, u.val)) =
      match s_abs u with
      | none => (0, 0)
      | some v => (1, v.val) := by
  have hum : s.mem (fl.pBase + 46) = fl.U - 1 := hpt 46 (by decide)
  have hle : u.val ≤ fl.U - 1 := Nat.le_sub_one_of_lt u.isLt
  obtain ⟨hst, hres⟩ := fallbackQueryProg_spec hv.fb_valid hinv u
  have hst_eq : (Memory.spec 0).clientState s (fastFallbackQueryProg (fl.pBase, u.val)) =
      (Memory.spec 0).clientState s (fallbackQueryProg (fl.fbL.toCtx, u.val)) := by
    unfold fastFallbackQueryProg; dsimp only
    rw [StateTransitionSpec.clientState_bind,
      show (Memory.spec 0).clientState s (Memory.read (fl.pBase + 46)) = s from rfl,
      prog_clientResult_read, hum, ite_eq_left hle,
      StateTransitionSpec.clientState_bind, clientState_loadHashStaticCtxProg,
      clientResult_loadFeistelCtx hpt,
      StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
      clientResult_loadBlockPoolCtxProg hpt]
    rfl
  have hres_eq : (Memory.spec 0).clientResult s (fastFallbackQueryProg (fl.pBase, u.val)) =
      (Memory.spec 0).clientResult s (fallbackQueryProg (fl.fbL.toCtx, u.val)) := by
    unfold fastFallbackQueryProg; dsimp only
    rw [prog_clientResult_bind,
      show (Memory.spec 0).clientState s (Memory.read (fl.pBase + 46)) = s from rfl,
      prog_clientResult_read, hum, ite_eq_left hle,
      prog_clientResult_bind, clientState_loadHashStaticCtxProg,
      clientResult_loadFeistelCtx hpt,
      prog_clientResult_bind, clientState_loadBlockPoolCtxProg,
      clientResult_loadBlockPoolCtxProg hpt]
    rfl
  exact ⟨by rw [hst_eq]; exact hst, by rw [hres_eq, hres]; cases s_abs u <;> rfl⟩

/-- Fallback `insert(u, v)` loaded via `pBase` (`¬ReadsWidth`). -/
def fastFallbackInsertProg : (ℕ × ℕ) × ℕ → Memory.Prog Unit
  | ((pBase, u_val), v_val) => do
    let uMax ← Memory.read (pBase + 46)
    if u_val ≤ uMax then do
      let fctx ← loadHashStaticCtxProg (pBase, 0)
      let bpCtx ← loadBlockPoolCtxProg pBase
      fallbackInsertProg (((fctx, bpCtx), u_val), v_val)
    else
      pure ()

theorem realizesBounded_fastFallbackInsert :
    RealizesBounded .exact fastFallbackInsertProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hlf := realizesBounded_loadHashStaticCtx
  have hlb := realizesBounded_loadBlockPoolCtx
  have hfi := realizesBounded_fallbackInsert
  realize
  all_goals (
    rcases d with ⟨⟨pBase, u_val⟩, v_val⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_loadHashStaticCtxProg,
      runClient_state_loadBlockPoolCtxProg] at *
    first | exact hw6 | exact hp | omega | (
      have hum : s.mem (fl.pBase + 46) = fl.U - 1 := hr.2.1 46 (by decide)
      have hf_res := clientResult_loadFeistelCtx (s := s) hr.2.1
      have hb_res := clientResult_loadBlockPoolCtxProg (s := s) hr.2.1
      simp only [StateTransitionSpec.clientResult] at hf_res hb_res ⊢
      try rw [hf_res]
      try rw [hb_res]
      first
      | exact feistelSplitPre_of_fastReady hr (by omega)
      | (dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
         rw [BpMetaLayout.ofCtx_toCtx]; exact hr.1.mp_valid)
      | (dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
         rw [SlotIoLayout.ofCtx_toCtx]; exact hr.1.io_valid)))

theorem fastFallbackInsertProg_spec {fl : FastEpochLayout} {w : ℕ}
    {θ_bkt : BktSeed fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier) (hpt : fl.ParamTable s.mem)
    (hinv : fl.fbL.StateInv 0 θ_bkt s.mem s_abs) (u : Fin fl.U) (v : Fin fl.V)
    (hcap_new : s_abs u = none →
      (extractFallback fl.mp s.mem).nSide < fl.N ∧
      fl.io.AppendCap (extractFallback fl.mp s.mem).nSide s.mem) :
    let fb := extractFallback fl.mp s.mem
    let s' := (Memory.spec 0).clientState s (fastFallbackInsertProg ((fl.pBase, u.val), v.val))
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    s'.frontier = s.frontier ∧
    fl.ParamTable s'.mem ∧
    (extractFallback fl.mp s'.mem).nSide = (if s_abs u = none then fb.nSide + 1 else fb.nSide) ∧
    fl.fbL.StateInv slack' θ_bkt s'.mem (Function.update s_abs u (some v)) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (fl.io.usePaged ≠ 0 →
      (extractPagePair fl.io.pgL s'.mem).virtLen fl.io.partner.side =
        (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side ∧
      (extractPagePair fl.io.pgL s'.mem).totalItems =
        (if s_abs u = none then (extractPagePair fl.io.pgL s.mem).totalItems + 1
         else (extractPagePair fl.io.pgL s.mem).totalItems) ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) := by
  dsimp only
  have hum : s.mem (fl.pBase + 46) = fl.U - 1 := hpt 46 (by decide)
  have hle : u.val ≤ fl.U - 1 := Nat.le_sub_one_of_lt u.isLt
  have hst : (Memory.spec 0).clientState s (fastFallbackInsertProg ((fl.pBase, u.val), v.val)) =
      (Memory.spec 0).clientState s (fallbackInsertProg ((fl.fbL.toCtx, u.val), v.val)) := by
    unfold fastFallbackInsertProg; dsimp only
    rw [StateTransitionSpec.clientState_bind,
      show (Memory.spec 0).clientState s (Memory.read (fl.pBase + 46)) = s from rfl,
      prog_clientResult_read, hum, ite_eq_left hle,
      StateTransitionSpec.clientState_bind, clientState_loadHashStaticCtxProg,
      clientResult_loadFeistelCtx hpt,
      StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
      clientResult_loadBlockPoolCtxProg hpt]
    rfl
  obtain ⟨hfr, hns, hinv', hout, hpart⟩ :=
    fallbackInsertProg_spec hv.fb_valid hinv u v hcap_new
  rw [hst]
  have hout_fast : ∀ addr, ¬fl.OwnsFastAddr addr →
      ((Memory.spec 0).clientState s
        (fallbackInsertProg ((fl.fbL.toCtx, u.val), v.val))).mem addr = s.mem addr :=
    fun a ha => hout a (fun hfb => ha (fl.owns_of_fb hv hfb))
  have hpt' : fl.ParamTable ((Memory.spec 0).clientState s
      (fallbackInsertProg ((fl.fbL.toCtx, u.val), v.val))).mem :=
    hpt.congr fun a ha1 ha2 => hout_fast a (hv.not_ownsFast_pBase ha1 (by omega))
  exact ⟨hfr, hpt', hns, hinv', hout_fast, hpart⟩

/-- Fallback `delete(u)` loaded via `pBase` (`¬ReadsWidth`). -/
def fastFallbackDeleteProg : ℕ × ℕ → Memory.Prog Unit
  | (pBase, u_val) => do
    let uMax ← Memory.read (pBase + 46)
    if u_val ≤ uMax then do
      let fctx ← loadHashStaticCtxProg (pBase, 0)
      let bpCtx ← loadBlockPoolCtxProg pBase
      fallbackDeleteProg ((fctx, bpCtx), u_val)
    else
      pure ()

theorem realizesBounded_fastFallbackDelete :
    RealizesBounded .exact fastFallbackDeleteProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hlf := realizesBounded_loadHashStaticCtx
  have hlb := realizesBounded_loadBlockPoolCtx
  have hfd := realizesBounded_fallbackDelete
  realize
  all_goals (
    rcases d with ⟨pBase, u_val⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_loadHashStaticCtxProg,
      runClient_state_loadBlockPoolCtxProg] at *
    first | exact hw6 | exact hp | omega | (
      have hum : s.mem (fl.pBase + 46) = fl.U - 1 := hr.2.1 46 (by decide)
      have hf_res := clientResult_loadFeistelCtx (s := s) hr.2.1
      have hb_res := clientResult_loadBlockPoolCtxProg (s := s) hr.2.1
      simp only [StateTransitionSpec.clientResult] at hf_res hb_res ⊢
      try rw [hf_res]
      try rw [hb_res]
      first
      | exact feistelSplitPre_of_fastReady hr (by omega)
      | (dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
         rw [BpMetaLayout.ofCtx_toCtx]; exact hr.1.mp_valid)
      | (dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
         rw [SlotIoLayout.ofCtx_toCtx]; exact hr.1.io_valid)))

theorem fastFallbackDeleteProg_spec {fl : FastEpochLayout} {w : ℕ}
    {θ_bkt : BktSeed fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier) (hpt : fl.ParamTable s.mem)
    (hinv : fl.fbL.StateInv 0 θ_bkt s.mem s_abs) (u : Fin fl.U) :
    let fb := extractFallback fl.mp s.mem
    let s' := (Memory.spec 0).clientState s (fastFallbackDeleteProg (fl.pBase, u.val))
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    s'.frontier = s.frontier ∧
    fl.ParamTable s'.mem ∧
    (extractFallback fl.mp s'.mem).nSide = (if s_abs u = none then fb.nSide else fb.nSide - 1) ∧
    fl.fbL.StateInv slack' θ_bkt s'.mem (Function.update s_abs u none) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (fl.io.usePaged ≠ 0 →
      (extractPagePair fl.io.pgL s'.mem).virtLen fl.io.partner.side =
        (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side ∧
      (extractPagePair fl.io.pgL s'.mem).totalItems =
        (if s_abs u = none then (extractPagePair fl.io.pgL s.mem).totalItems
         else (extractPagePair fl.io.pgL s.mem).totalItems - 1) ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) := by
  dsimp only
  have hum : s.mem (fl.pBase + 46) = fl.U - 1 := hpt 46 (by decide)
  have hle : u.val ≤ fl.U - 1 := Nat.le_sub_one_of_lt u.isLt
  have hst : (Memory.spec 0).clientState s (fastFallbackDeleteProg (fl.pBase, u.val)) =
      (Memory.spec 0).clientState s (fallbackDeleteProg (fl.fbL.toCtx, u.val)) := by
    unfold fastFallbackDeleteProg; dsimp only
    rw [StateTransitionSpec.clientState_bind,
      show (Memory.spec 0).clientState s (Memory.read (fl.pBase + 46)) = s from rfl,
      prog_clientResult_read, hum, ite_eq_left hle,
      StateTransitionSpec.clientState_bind, clientState_loadHashStaticCtxProg,
      clientResult_loadFeistelCtx hpt,
      StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
      clientResult_loadBlockPoolCtxProg hpt]
    rfl
  obtain ⟨hfr, hns, hinv', hout, hpart⟩ := fallbackDeleteProg_spec hv.fb_valid hinv u
  rw [hst]
  have hout_fast : ∀ addr, ¬fl.OwnsFastAddr addr →
      ((Memory.spec 0).clientState s
        (fallbackDeleteProg (fl.fbL.toCtx, u.val))).mem addr = s.mem addr :=
    fun a ha => hout a (fun hfb => ha (fl.owns_of_fb hv hfb))
  have hpt' : fl.ParamTable ((Memory.spec 0).clientState s
      (fallbackDeleteProg (fl.fbL.toCtx, u.val))).mem :=
    hpt.congr fun a ha1 ha2 => hout_fast a (hv.not_ownsFast_pBase ha1 (by omega))
  exact ⟨hfr, hpt', hns, hinv', hout_fast, hpart⟩

/-- Fallback `popAny` loaded via `pBase` (`¬ReadsWidth`). -/
def fastFallbackPopAnyProg (pBase : ℕ) : Memory.Prog (ℕ × ℕ) := do
  let fctx ← loadHashStaticCtxProg (pBase, 0)
  let bpCtx ← loadBlockPoolCtxProg pBase
  fallbackPopAnyProg (fctx, bpCtx)

theorem realizesBounded_fastFallbackPopAny :
    RealizesBounded .exact fastFallbackPopAnyProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w pBase s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hlf := realizesBounded_loadHashStaticCtx
  have hlb := realizesBounded_loadBlockPoolCtx
  have hfp := realizesBounded_fallbackPopAny
  realize
  all_goals (
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    try simp only [StateTransitionSpec.clientState, runClient_state_loadHashStaticCtxProg,
      runClient_state_loadBlockPoolCtxProg] at *
    first | exact hw6 | exact hp | (
      have hf_res := clientResult_loadFeistelCtx (s := s) hr.2.1
      have hb_res := clientResult_loadBlockPoolCtxProg (s := s) hr.2.1
      simp only [StateTransitionSpec.clientResult] at hf_res hb_res ⊢
      try rw [hf_res]
      try rw [hb_res]
      first
      | (dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
         rw [BpMetaLayout.ofCtx_toCtx]; exact hr.1.mp_valid)
      | (dsimp only [BlockPoolLayout.toCtx, FastEpochLayout.bpL]
         rw [SlotIoLayout.ofCtx_toCtx]; exact hr.1.io_valid)
      | (dsimp only [FastEpochLayout.feistelCtx]; exact hr.1.w_eq.symm)
      | (intro bkt q_val hq
         exact feistelReconPre_of_fastReady hr hq)))

theorem fastFallbackPopAnyProg_spec {fl : FastEpochLayout} {w : ℕ}
    {θ_bkt : BktSeed fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier) (hpt : fl.ParamTable s.mem)
    (hinv : fl.fbL.StateInv 0 θ_bkt s.mem s_abs)
    (hpos : 0 < (extractFallback fl.mp s.mem).nSide) :
    let fb := extractFallback fl.mp s.mem
    let s' := (Memory.spec 0).clientState s (fastFallbackPopAnyProg fl.pBase)
    let uv := (Memory.spec 0).clientResult s (fastFallbackPopAnyProg fl.pBase)
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    s'.frontier = s.frontier ∧
    fl.ParamTable s'.mem ∧
    (extractFallback fl.mp s'.mem).nSide = fb.nSide - 1 ∧
    (∃ (u : Fin fl.U) (v : Fin fl.V),
      uv = (u.val, v.val) ∧ s_abs u = some v ∧
      fl.fbL.StateInv slack' θ_bkt s'.mem (Function.update s_abs u none)) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (fl.io.usePaged ≠ 0 →
      (extractPagePair fl.io.pgL s'.mem).virtLen fl.io.partner.side =
        (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side ∧
      (extractPagePair fl.io.pgL s'.mem).totalItems =
        (extractPagePair fl.io.pgL s.mem).totalItems - 1 ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) := by
  dsimp only
  have hst : (Memory.spec 0).clientState s (fastFallbackPopAnyProg fl.pBase) =
      (Memory.spec 0).clientState s (fallbackPopAnyProg fl.fbL.toCtx) := by
    unfold fastFallbackPopAnyProg
    rw [StateTransitionSpec.clientState_bind, clientState_loadHashStaticCtxProg,
      clientResult_loadFeistelCtx hpt,
      StateTransitionSpec.clientState_bind, clientState_loadBlockPoolCtxProg,
      clientResult_loadBlockPoolCtxProg hpt]
    rfl
  have hres : (Memory.spec 0).clientResult s (fastFallbackPopAnyProg fl.pBase) =
      (Memory.spec 0).clientResult s (fallbackPopAnyProg fl.fbL.toCtx) := by
    unfold fastFallbackPopAnyProg
    rw [prog_clientResult_bind, clientState_loadHashStaticCtxProg,
      clientResult_loadFeistelCtx hpt,
      prog_clientResult_bind, clientState_loadBlockPoolCtxProg,
      clientResult_loadBlockPoolCtxProg hpt]
    rfl
  obtain ⟨hfr, hns, hinv', hout, hpart⟩ := fallbackPopAnyProg_spec hv.fb_valid hinv hpos
  rw [hst, hres]
  have hout_fast : ∀ addr, ¬fl.OwnsFastAddr addr →
      ((Memory.spec 0).clientState s
        (fallbackPopAnyProg fl.fbL.toCtx)).mem addr = s.mem addr :=
    fun a ha => hout a (fun hfb => ha (fl.owns_of_fb hv hfb))
  have hpt' : fl.ParamTable ((Memory.spec 0).clientState s
      (fallbackPopAnyProg fl.fbL.toCtx)).mem :=
    hpt.congr fun a ha1 ha2 => hout_fast a (hv.not_ownsFast_pBase ha1 (by omega))
  exact ⟨hfr, hpt', hns, hinv', hout_fast, hpart⟩

/-- Precondition for `fastInsertProg` / `largeEpochInsertProg`: extends `FastProgPre` with the
frame preservation of `fastEnterFallbackProg` when starting in fast mode (`mode = 0`). -/
@[expose] def FastInsertProgPre (w pBase : ℕ) (s : Memory.State) : Prop :=
  ∃ fl : FastEpochLayout, fl.pBase = pBase ∧ FastLayoutReady w fl s ∧
    (s.mem (fl.metaBase + 2) = 0 →
      FastLayoutReady w fl ((Memory.spec 0).clientState s (fastEnterFallbackProg pBase)))

/-- Every valid `LargeEpochInv` (plus `fpHashBase` bound when in fallback mode) discharges
`FastInsertProgPre`. -/
theorem LargeEpochInv.fastInsertProgPre {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (hv : fl.Valid w s.frontier)
    (hinv : LargeEpochInv fl slack seeds s.mem s_abs)
    (hfp : s.mem fl.fpHashBase < 2 ^ (redWidthWhp fl.U - 1)) :
    FastInsertProgPre w fl.pBase s := by
  rcases hinv.2 with ⟨hm0, hf⟩ | ⟨hm1, hfb⟩
  · have hr := hf.ready hv rfl
    refine ⟨fl, rfl, hr, fun _ => ?_⟩
    obtain ⟨hfr, _, _, _, hout, _⟩ := fastEnterFallbackProg_spec hr hf.hdr_N hf.seed_bkt
      hf.bp_inv.1.core hf.bp_inv.2.1 hf.bp_inv.2.2 hf.refines
    exact hr.of_frame hfr hout
  · exact ⟨fl, rfl, fastLayoutReady_of_fallback rfl hv hinv.1 hfb hfp,
      fun h0 => absurd (h0.symm.trans hm1) Nat.zero_ne_one⟩

/-! ## Section 3: Fast-Mode `delete` (`fastDeleteProg`) -/

/-- Worst-case `memoryCost` bound for `fastProbeProg` / `fastQueryProg` (pure function of `c`). -/
@[expose] def fastProbeCost (c : ℕ) : ℕ :=
  360 + 4 * dTabWhp c * (cTabWhp c + 2) + 4 * cTabWhp c + 6 * hMaxBTree

/-- Worst-case `memoryCost` bound for `fastDeleteProg` (pure function of `c`). -/
@[expose] def fastDeleteCost (c : ℕ) : ℕ :=
  fastProbeCost c + fastRemoveAtCost c

/-- Fast-mode (`fallbackMode = 0`) `delete(u)` via `pBase` (`¬ReadsWidth`). Does not advance
`subStep` so every `BufCur` slot corresponds strictly to a fresh insertion. -/
def fastDeleteProg : ℕ × ℕ → Memory.Prog Unit
  | (pBase, u_val) => do
    let pr ← fastProbeProg (pBase, u_val)
    if fastProbeTier pr = 0 then
      pure ()
    else
      fastRemoveAtProg ((pBase, fastProbeBkt pr), (fastProbeIdx pr, u_val))

theorem realizesBounded_fastDelete :
    RealizesBounded .exact fastDeleteProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hp := realizesBounded_fastProbe
  have hr := realizesBounded_fastRemoveAt
  realize
  all_goals (
    rcases d with ⟨pBase, u_val⟩
    obtain ⟨fl, rfl, hfl⟩ := h
    try simp only [StateTransitionSpec.clientState, runClient_state_fastProbeProg] at *
    exact ⟨fl, rfl, hfl⟩)

/-- Unconditional exact specification of `fastDeleteProg`: stays in `FastEpochInv`
(`fallbackMode = 0`) on **100%** of hash seeds in `≤ fastDeleteCost fl.c` memory operations. -/
theorem fastDeleteProg_spec {fl : FastEpochLayout} {w : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInv fl 0 seeds s.mem s_abs) (u : Fin fl.U) :
    let fm := extractFastMeta fl s.mem
    let bp := extractBlockPool fl.mp s.mem
    let s' := (Memory.spec 0).clientState s (fastDeleteProg (fl.pBase, u.val))
    let fm' := extractFastMeta fl s'.mem
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    s'.frontier = s.frontier ∧
    memoryCost (fastDeleteProg (fl.pBase, u.val)) s ≤ fastDeleteCost fl.c ∧
    FastEpochInv fl slack' seeds s'.mem (Function.update s_abs u none) ∧
    (extractBlockPool fl.mp s'.mem).nSide = (if s_abs u = none then bp.nSide else bp.nSide - 1) ∧
    fm'.curBufRole = fm.curBufRole ∧
    fm'.subStep = fm.subStep ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (fl.io.usePaged ≠ 0 →
      (extractPagePair fl.io.pgL s'.mem).virtLen fl.io.partner.side =
        (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side ∧
      (extractPagePair fl.io.pgL s'.mem).totalItems =
        (if s_abs u = none then (extractPagePair fl.io.pgL s.mem).totalItems
         else (extractPagePair fl.io.pgL s.mem).totalItems - 1) ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) ∧
    (∀ S : Finset (Fin fl.U), CurBufKeysIn seeds s.mem S → CurBufKeysIn seeds s'.mem S) := by
  dsimp only
  set b := epochBucket fl.c fl.U fl.N seeds.bkt u
  have hb : b < numBucketsWhp fl.N := epochBucket_lt fl.c fl.U fl.N seeds.bkt u
  obtain ⟨hpr_st, hpr_c, hpr_b, hpr_res⟩ :=
    fastProbeProg_spec (slack := 0) (seeds := seeds) (s_abs := s_abs) hv hinv u
  have hup_mono : ∀ sl, sl ≤ 24 → FastEpochInv fl 0 seeds s.mem s_abs →
      FastEpochInv fl sl seeds s.mem s_abs := fun sl hsl h =>
    { h with bp_inv := h.bp_inv.mono_slack (Nat.zero_le _) hsl }
  set slack' :=
    if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
  have hsl_le : slack' ≤ 24 := by dsimp only [slack']; split_ifs <;> decide
  unfold fastDeleteProg
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hpr_st]
  dsimp only
  cases hsu : s_abs u with
  | none =>
    rw [hsu] at hpr_res
    rw [ite_eq_left hpr_res.1, StateTransitionSpec.clientState_pure, memoryCost_pure]
    have hupd : Function.update s_abs u none = s_abs := Function.update_eq_self_iff.mpr hsu.symm
    rw [hupd]
    refine ⟨rfl, by unfold fastDeleteCost fastProbeCost; omega,
      hup_mono slack' hsl_le hinv, rfl, rfl, rfl, fun _ _ => rfl,
      fun _ => ⟨rfl, rfl, fun _ _ => rfl⟩, fun _ hS => hS⟩
  | some v =>
    rw [hsu] at hpr_res
    have hnz : ((Memory.spec 0).clientResult s (fastProbeProg (fl.pBase, u.val))).1.1 ≠ 0 := by
      rcases hpr_res.1 with h | h | h <;> omega
    set loc := ((Memory.spec 0).clientResult s (fastProbeProg (fl.pBase, u.val))).2.2.1
    rw [ite_eq_right hnz, hpr_b]
    have hloc : loc < (extractBlockPool fl.mp s.mem).bktCount b := hpr_res.2.1
    have hku : fastKeyAt fl seeds.bkt s.mem b loc = u.val := hpr_res.2.2.2.1
    obtain ⟨hfr', hrc', hinv', hns', _, _, _, hof', hpart', _, _, hcr', hss', _⟩ :=
      fastRemoveAtProg_spec u (by decide) hv (hinv.toGen 0) hb hloc hku
    have hcur_k := fastRemoveAtProg_curSlot_keys u (by decide) hv (hinv.toGen 0) hb hloc hku
    refine ⟨hfr', by unfold fastDeleteCost fastProbeCost; linarith only [hpr_c, hrc'],
      hinv'.toInv, hns', hcr', hss', hof', hpart', fun S hS id b' loc' u' hchk hb' hl' hk' => ?_⟩
    obtain ⟨loc₀, hl₀, hchk₀, hk₀⟩ := hcur_k id b' loc' u' hchk hb' hl' hk'
    exact hS id b' loc₀ u' hchk₀ hb' hl₀ hk₀

/-- Good-seed preservation for `fastDeleteProg`. -/
theorem fastDeleteProg_good {fl : FastEpochLayout} {w : ℕ}
    {win : EpochWindowSpec fl.c fl.U fl.N} {e : Fin win.numSubs}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {hgood : GoodEpochSeeds win seeds}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hg : FastSubEpochGood 0 0 0 win e seeds hgood s.mem s_abs) (u : Fin fl.U) :
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    FastSubEpochGood 0 0 slack' win e seeds hgood
      ((Memory.spec 0).clientState s (fastDeleteProg (fl.pBase, u.val))).mem
      (Function.update s_abs u none) := by
  dsimp only
  set slack' :=
    if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
  have hsl_le : slack' ≤ 24 := by dsimp only [slack']; split_ifs <;> decide
  set b := epochBucket fl.c fl.U fl.N seeds.bkt u
  have hb : b < numBucketsWhp fl.N := epochBucket_lt fl.c fl.U fl.N seeds.bkt u
  obtain ⟨hpr_st, _, hpr_b, hpr_res⟩ :=
    fastProbeProg_spec (slack := 0) (seeds := seeds) (s_abs := s_abs) hv hg.inv.toInv u
  unfold fastDeleteProg
  rw [StateTransitionSpec.clientState_bind, hpr_st]
  dsimp only
  cases hsu : s_abs u with
  | none =>
    rw [hsu] at hpr_res
    rw [ite_eq_left hpr_res.1, StateTransitionSpec.clientState_pure]
    have hupd : Function.update s_abs u none = s_abs := Function.update_eq_self_iff.mpr hsu.symm
    rw [hupd]
    exact
      { hg with
        inv := { hg.inv with
          bp_inv := hg.inv.bp_inv.mono_slack (Nat.zero_le _) hsl_le } }
  | some v =>
    rw [hsu] at hpr_res
    have hnz : ((Memory.spec 0).clientResult s (fastProbeProg (fl.pBase, u.val))).1.1 ≠ 0 := by
      rcases hpr_res.1 with h | h | h <;> omega
    rw [ite_eq_right hnz, hpr_b]
    exact fastRemoveAtProg_good u (by decide) hv hg hb hpr_res.2.1 hpr_res.2.2.2.1

/-! ## Section 4: Fast-Mode Overwrite and New-Key Insert Helpers -/

private theorem fastInsertOverwrite_spec {fl : FastEpochLayout} {w b loc : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInv fl 0 seeds s.mem s_abs)
    (u : Fin fl.U) (v : Fin fl.V)
    (hb : b < numBucketsWhp fl.N)
    (hb_u : b = epochBucket fl.c fl.U fl.N seeds.bkt u)
    (hloc : loc < (extractBlockPool fl.mp s.mem).bktCount b)
    (hq_u : (bpPairAt fl.bpL s.mem b loc).1 = keyQuotient (bWhp fl.N) u.val) :
    let q_u := keyQuotient (bWhp fl.N) u.val
    let s' := (Memory.spec 0).clientState s (fastBpWriteAtProg ((fl.pBase, (b, loc)), (q_u, v.val)))
    s'.frontier = s.frontier ∧
    memoryCost (fastBpWriteAtProg ((fl.pBase, (b, loc)), (q_u, v.val))) s ≤ 75 ∧
    FastEpochInv fl 0 seeds s'.mem (Function.update s_abs u (some v)) ∧
    extractBlockPool fl.mp s'.mem = extractBlockPool fl.mp s.mem ∧
    extractFastMeta fl s'.mem = extractFastMeta fl s.mem ∧
    (∀ r < 2, extractBufTrie (fl.trieL r) s'.mem = extractBufTrie (fl.trieL r) s.mem) ∧
    (∀ b' < numBucketsWhp fl.N, ∀ loc' < (extractBlockPool fl.mp s.mem).bktCount b',
      fastKeyAt fl seeds.bkt s'.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc') ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (fl.io.usePaged ≠ 0 →
      extractPageUnperm fl.io.pgL s'.mem = extractPageUnperm fl.io.pgL s.mem ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) := by
  dsimp only
  set q_u := keyQuotient (bWhp fl.N) u.val
  have hq_lt : q_u < 2 ^ fl.io.pgL.qBits :=
    (keyQuotient_bWhp_lt hv.N_le_U u).trans_le (Nat.pow_le_pow_right Nat.one_lt_two.le hv.qBits_le)
  have hv_lt : v.val < 2 ^ fl.io.pgL.vBits := by
    rw [hv.vBits_eq]; exact v.isLt.trans_le (Nat.le_pow_clog Nat.one_lt_two fl.V)
  have hr := hinv.ready hv rfl
  obtain ⟨hfr', hr', hc', hbp', hbp_inv', hfm', hm0', hm2', hbt', htr', hof', hpair', hpart'⟩ :=
    fastBpWriteAtProg_spec hr hinv.bp_inv hb hloc hq_lt hv_lt
  set s' := (Memory.spec 0).clientState s (fastBpWriteAtProg ((fl.pBase, (b, loc)), (q_u, v.val)))
  have hke : ∀ b' < numBucketsWhp fl.N, ∀ loc' < (extractBlockPool fl.mp s.mem).bktCount b',
      fastKeyAt fl seeds.bkt s'.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc' := by
    intro b' hb' loc' hl'
    unfold fastKeyAt
    have hq_eq : (bpPairAt fl.bpL s'.mem b' loc').1 = (bpPairAt fl.bpL s.mem b' loc').1 := by
      rw [hpair' b' hb' loc' hl']
      split_ifs with he
      · rcases he with ⟨rfl, rfl⟩; exact hq_u.symm
      · rfl
    rw [hq_eq]
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  have hsb' : BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) seeds.bkt s'.mem :=
    hinv.seed_bkt.congr_on hw_pos fun a h1 h2 =>
      hof' a (hv.not_ownsFast_seeds (by dsimp only [FastEpochLayout.bktHashBase] at h1; exact h1)
        (by dsimp only [FastEpochLayout.bktHashBase] at h2
            unfold offBktMeta offFpHash offBktHash at *; omega))
  have hsf' : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp s'.mem :=
    hinv.seed_fp.congr_on hw_pos fun a h1 h2 =>
      hof' a (hv.not_ownsFast_seeds
        (by dsimp only [FastEpochLayout.fpHashBase] at h1; unfold offFpHash at h1
            have : offBktHash ≤ offFpHash fl.c fl.w fl.U := by
              unfold offFpHash; exact Nat.le_add_right _ _
            omega)
        (by dsimp only [FastEpochLayout.fpHashBase] at h2; unfold offBktMeta; omega))
  have href' : PoolItemsRefines fl.U fl.V (bWhp fl.N) (bktHash fl.c fl.U fl.N seeds.bkt)
      (extractBlockPool fl.mp s'.mem).nSide
      (fun p => ((extractBlockPool fl.mp s'.mem).ownerOf p).1)
      (slotIoPairAt fl.io s'.mem) (Function.update s_abs u (some v)) :=
    poolRefines_bpWriteAt v hbp' hinv.bp_inv.1.core hinv.refines hb hloc hb_u hq_u hpair'
  have hb_inv : FastEpochInv fl 0 seeds s'.mem (Function.update s_abs u (some v)) := by
    refine
      { param_table := hr'.2.1
        hdr_N := hm0'.trans hinv.hdr_N
        mode_zero := hm2'.trans hinv.mode_zero
        seed_bkt := hsb'
        seed_fp := hsf'
        bp_inv := hbp_inv'
        bkt_le_capMax := by rw [hbp']; exact hinv.bkt_le_capMax
        refines := href'
        role_lt := by rw [hfm']; exact hinv.role_lt
        subStep_lt := by rw [hfm']; exact hinv.subStep_lt
        bkt_meta_bounds := by rw [hfm']; exact hinv.bkt_meta_bounds
        tiers := ?_ }
    have hrole_lt : (extractFastMeta fl s.mem).curBufRole < 2 := hinv.role_lt
    have hold_lt : 1 - (extractFastMeta fl s.mem).curBufRole < 2 := by omega
    obtain ⟨mC, mO, mB, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hinv.tiers
    refine ⟨mC, mO, mB, ?_⟩
    simp only [hfm', hbp', htr' _ hrole_lt, htr' _ hold_lt]
    refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_, ?_, ?_, h11, ?_⟩
    · intro rk b' loc' hm
      obtain ⟨hb', hl', u', hrk', hk'⟩ := h6 rk b' loc' hm
      exact ⟨hb', hl', u', hrk', (hke b' hb' loc' hl').trans hk'⟩
    · by_cases hsub : (extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2
      · rw [ite_eq_left hsub] at h7 ⊢
        obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h7
        refine ⟨a1, a2, a3, a4, a5, a6, a7, fun rk b' loc' hm => ?_⟩
        obtain ⟨hc, hb', hl', u', hrk', hk'⟩ := a8 rk b' loc' hm
        exact ⟨hc, hb', hl', u', hrk', (hke b' hb' loc' hl').trans hk'⟩
      · rw [ite_eq_right hsub] at h7 ⊢; exact h7
    · intro b' hb'
      obtain ⟨hvb, hbs⟩ := h8 b' hb'
      have hrb : (extractFastMeta fl s.mem).curRole b' < 3 := (hinv.bkt_meta_bounds b' hb').2.1
      rw [hbt' b' hb' _ hrb]
      refine ⟨hvb, fun fp loc' hm => ?_⟩
      obtain ⟨hl', u', hfp, hk', d1, d2⟩ := hbs fp loc' hm
      refine ⟨hl', u', hfp, (hke b' hb' loc' hl').trans hk', fun b₁ l₁ hm₁ => ?_,
        fun b₂ l₂ hm₂ => ?_⟩
      · obtain ⟨hb₁, hl₁, _⟩ := h6 _ b₁ l₁ hm₁
        rw [hke b₁ hb₁ l₁ hl₁]; exact d1 b₁ l₁ hm₁
      · by_cases hsub : (extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2
        · rw [ite_eq_left hsub] at h7
          obtain ⟨_, hb₂, hl₂, _⟩ := h7.2.2.2.2.2.2.2 _ b₂ l₂ hm₂
          rw [hke b₂ hb₂ l₂ hl₂]; exact d2 b₂ l₂ hm₂
        · rw [ite_eq_right hsub] at h7; rw [h7.1] at hm₂; cases hm₂
    · intro b' hb' loc' hl'
      obtain ⟨u', hk', hmem⟩ := h9 b' hb' loc' hl'
      exact ⟨u', (hke b' hb' loc' hl').trans hk', hmem⟩
    · intro b' hb' hsc
      obtain ⟨p1, p2, p3, p4, sm, hvs, hsm⟩ := h10 b' hb' hsc
      have hsr : shadowRoleOf ((extractFastMeta fl s.mem).curRole b') < 3 :=
        (shadowRoleOf_lt_and_ne (hinv.bkt_meta_bounds b' hb').2.1).1
      rw [hbt' b' hb' _ hsr]
      exact ⟨p1, p2, p3, p4, sm, hvs, hsm⟩
    · intro hta
      obtain ⟨hsub, hb_t, hs_t, htp, hsc_t, hbd, tm, hvt, htm1, htm2⟩ := h12 hta
      have htr_lt : tryRoleOf ((extractFastMeta fl s.mem).curRole
          (extractFastMeta fl s.mem).tryBkt) < 3 :=
        (tryRoleOf_lt_and_ne (hinv.bkt_meta_bounds _ hb_t).2.1).1
      rw [hbt' _ hb_t _ htr_lt]
      refine ⟨hsub, hb_t, hs_t, htp, hsc_t, hbd, tm, hvt, fun fp loc' hm => ?_,
        fun loc' hl' u' hk' hmb => ?_⟩
      · obtain ⟨hl', u', hk', hmb, hfp⟩ := htm1 fp loc' hm
        exact ⟨hl', u', (hke _ hb_t loc' (lt_of_lt_of_le hl' htp)).trans hk', hmb, hfp⟩
      · exact htm2 loc' hl' u' ((hke _ hb_t loc' (lt_of_lt_of_le hl' htp)).symm.trans hk') hmb
  exact ⟨hfr', hc', hb_inv, hbp', hfm', htr', hke, hof', hpart'⟩

/-- Worst-case `memoryCost` bound for inserting one new key before `advanceSubEpochProg`. -/
@[expose] def fastInsertNewStepCost (c : ℕ) : ℕ :=
  5 * drainTickCost c +
  8 * (360 + 4 * dTabWhp c * (cTabWhp c + 2) + 78 * hMaxBTree) +
  2 * dTabWhp c * (cTabWhp c + 2) + 24 * cTabWhp c + 5400

/-- Inner fast-path insertion body (executed when `s_abs u = none`, `rKey` is unused in active
buffer tries, and `bktCount b < capMaxWhp N`). Appends `(u, v)` to bucket `b` and indexes it in
`BufCur`, producing `FastEpochInvGen 1`. -/
private def fastInsertNewStepProg : (ℕ × ℕ) × ((ℕ × ℕ) × ℕ) → Memory.Prog Unit
  | ((pBase, u_val), ((b, cnt), v_val)) => do
    drainTrySteps5Prog pBase
    fastShadowSteps8Prog (pBase, b)
    let bq ← fastFeistelSplitProg (pBase, u_val)
    fastBpAppendProg ((pBase, b), (bq.2, v_val))
    let rk ← fastRKeyProg (pBase, u_val)
    let curR ← fastReadMetaProg (pBase, 3)
    fastBufInsertProg ((pBase, curR), (rk, (b, cnt)))

private theorem realizesBounded_fastInsertNewStep :
    RealizesBounded .exact fastInsertNewStepProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ((ℕ × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hd := realizesBounded_drainTrySteps5
  have hs := realizesBounded_fastShadowSteps8
  have hf := realizesBounded_fastFeistelSplit
  have ha := realizesBounded_fastBpAppend
  have hrk := realizesBounded_fastRKey
  have hrm := realizesBounded_fastReadMeta
  have hbi := realizesBounded_fastBufInsert
  realize
  all_goals (
    rcases d with ⟨⟨pBase, u_val⟩, ⟨⟨b, cnt⟩, v_val⟩⟩
    obtain ⟨fl, rfl, hfl⟩ := h
    have h1 := drainTrySteps5Prog_pre (⟨fl, rfl, hfl⟩ : FastProgPre w fl.pBase s)
    have h2 := fastShadowSteps8Prog_pre (x := (fl.pBase, b)) h1
    dsimp only [Fits] at *
    try simp only [StateTransitionSpec.clientState, runClient_state_fastFeistelSplitProg,
      runClient_state_fastRKeyProg, runClient_state_fastReadMetaProg] at *
    first
    | exact ⟨fl, rfl, hfl⟩
    | exact h1
    | exact h2
    | exact fastBpAppendProg_pre (x := ((fl.pBase, b), _)) h2
    | (obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound h2
       have hpow6 : 64 ≤ 2 ^ w :=
         (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
       omega))

private theorem fastInsertNewStepProg_spec {fl : FastEpochLayout} {w b : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInv fl 0 seeds s.mem s_abs) (u : Fin fl.U) (v : Fin fl.V)
    (hb_eq : b = epochBucket fl.c fl.U fl.N seeds.bkt u)
    (habs : s_abs u = none)
    (hn_lt : (extractBlockPool fl.mp s.mem).nSide < fl.N)
    (hcnt_lt : (extractBlockPool fl.mp s.mem).bktCount b < capMaxWhp fl.N)
    (hcap_io : fl.io.AppendCap (extractBlockPool fl.mp s.mem).nSide s.mem)
    (hcur_none : bufLookup (cTabWhp fl.c) (bCharWhp fl.N)
      (extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s.mem)
      (rKeyOf fl.c fl.U fl.N seeds.fp u) = none)
    (hold_none : (extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2 →
      bufLookup (cTabWhp fl.c) (bCharWhp fl.N)
        (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem)
        (rKeyOf fl.c fl.U fl.N seeds.fp u) = none) :
    let cnt := (extractBlockPool fl.mp s.mem).bktCount b
    let s' := (Memory.spec 0).clientState s
      (fastInsertNewStepProg ((fl.pBase, u.val), ((b, cnt), v.val)))
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    s'.frontier = s.frontier ∧
    memoryCost (fastInsertNewStepProg ((fl.pBase, u.val), ((b, cnt), v.val))) s ≤
      fastInsertNewStepCost fl.c ∧
    FastEpochInvGen 1 fl slack' seeds s'.mem (Function.update s_abs u (some v)) ∧
    (extractFastMeta fl s'.mem).curBufRole = (extractFastMeta fl s.mem).curBufRole ∧
    (extractFastMeta fl s'.mem).subStep = (extractFastMeta fl s.mem).subStep ∧
    (extractBlockPool fl.mp s'.mem).nSide = (extractBlockPool fl.mp s.mem).nSide + 1 ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (fl.io.usePaged ≠ 0 →
      (extractPagePair fl.io.pgL s'.mem).virtLen fl.io.partner.side =
        (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side ∧
      (extractPagePair fl.io.pgL s'.mem).totalItems =
        (extractPagePair fl.io.pgL s.mem).totalItems + 1 ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) ∧
    (∀ S : Finset (Fin fl.U), CurBufKeysIn seeds s.mem S →
      CurBufKeysIn seeds s'.mem (insert u S)) := by
  dsimp only
  have hb : b < numBucketsWhp fl.N := hb_eq ▸ epochBucket_lt fl.c fl.U fl.N seeds.bkt u
  set cnt := (extractBlockPool fl.mp s.mem).bktCount b
  set rk := rKeyOf fl.c fl.U fl.N seeds.fp u
  have hrk_lt : rk < 2 ^ (cTabWhp fl.c * bCharWhp fl.N) := rKeyOf_lt fl.c fl.U fl.N seeds.fp u
  -- Step 1: `drainTrySteps5Prog pBase`
  obtain ⟨hfr1, hc1, hinv1, hbp1, hcur1, hoi1, hof1, hcr1, hss1, htry_sl1⟩ :=
    drainTrySteps5Prog_spec hv (hinv.toGen 0) hb hcnt_lt
  generalize hs1_def : (Memory.spec 0).clientState s (drainTrySteps5Prog fl.pBase) = s1
    at hfr1 hinv1 hbp1 hcur1 hoi1 hof1 hcr1 hss1 htry_sl1
  have hv1 : fl.Valid w s1.frontier := hfr1.symm ▸ hv
  have hcnt1 : (extractBlockPool fl.mp s1.mem).bktCount b = cnt := by rw [hbp1]
  -- Step 2: `fastShadowSteps8Prog (pBase, b)`
  obtain ⟨hfr2, hc2, hinv2, hbp2, hcr2, hss2, hdp2, hta2, htb2, hts2, htp2, hti2, hbs2,
    htr2, hoi2, hof2, _, hsh_sl2⟩ := fastShadowSteps8Prog_spec (b := b) hv1 hinv1
  generalize hs2_def : (Memory.spec 0).clientState s1 (fastShadowSteps8Prog (fl.pBase, b)) = s2
    at hfr2 hinv2 hbp2 hcr2 hss2 hdp2 hta2 htb2 hts2 htp2 hti2 hbs2 htr2 hoi2 hof2 hsh_sl2
  have hv2 : fl.Valid w s2.frontier := hfr2.symm ▸ hv1
  have hbp12 : extractBlockPool fl.mp s2.mem = extractBlockPool fl.mp s.mem := hbp2.trans hbp1
  have hoi12 : ∀ a, fl.io.OwnsAddr a → s2.mem a = s.mem a :=
    fun a ha => (hoi2 a ha).trans (hoi1 a ha)
  have hof12 : ∀ a, ¬fl.OwnsFastAddr a → s2.mem a = s.mem a :=
    fun a ha => (hof2 a ha).trans (hof1 a ha)
  have hpg12 : fl.io.usePaged ≠ 0 →
      extractPageUnperm fl.io.pgL s2.mem = extractPageUnperm fl.io.pgL s.mem ∧
      extractPagePair fl.io.pgL s2.mem = extractPagePair fl.io.pgL s.mem ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s2.mem idx = slotIoPairAt fl.io.partner s.mem idx := fun hup =>
    pagePair_partner_eq_of_io hv hup hinv.bp_inv hoi12
  have hslack_eq : (if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s2.mem).cleanPhase = 0
      then 0 else 24) =
      (if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0
        then 0 else 24) := by
    by_cases hup : fl.io.usePaged = 0
    · simp [hup]
    · simp [hup, (hpg12 hup).1]
  have hr2 := hinv2.ready hv2 rfl
  obtain ⟨hfs_r, hfs_c⟩ := fastFeistelSplitProg_spec hr2 hinv2.seed_bkt u
  have hq_lt : keyQuotient (bWhp fl.N) u.val < 2 ^ fl.io.pgL.qBits :=
    (keyQuotient_bWhp_lt hv.N_le_U u).trans_le (Nat.pow_le_pow_right Nat.one_lt_two.le hv.qBits_le)
  have hv_lt : v.val < 2 ^ fl.io.pgL.vBits := by
    rw [hv.vBits_eq]; exact v.isLt.trans_le (Nat.le_pow_clog Nat.one_lt_two fl.V)
  have hcap_io2 : fl.io.AppendCap (extractBlockPool fl.mp s2.mem).nSide s2.mem := by
    unfold SlotIoLayout.AppendCap at hcap_io ⊢
    by_cases hup : fl.io.usePaged = 0
    · rw [ite_eq_left hup] at hcap_io ⊢; rwa [hbp12]
    · rw [ite_eq_right hup] at hcap_io ⊢; rwa [(hpg12 hup).2.1]
  -- Step 3: `fastBpAppendProg ((pBase, b), (q_u, v.val))`
  obtain ⟨hfr3, hr3, hc3, hbp_inv3, hns3, hbc_b3, hbc_ne3, hnew3, hold3, hfm3, hm0_3, hm2_3,
    hbt3, htr3, hof3, hpart3⟩ := fastBpAppendProg_spec hr2 hinv2.bp_inv hb
    (by rw [hbp12]; exact hn_lt) (by rw [hbp12]; exact hcnt_lt) hcap_io2 hq_lt hv_lt
  rw [hslack_eq] at hbp_inv3
  generalize hs3_def : (Memory.spec 0).clientState s2
    (fastBpAppendProg ((fl.pBase, b), (keyQuotient (bWhp fl.N) u.val, v.val))) = s3
    at hfr3 hr3 hbp_inv3 hns3 hbc_b3 hbc_ne3 hnew3 hold3 hfm3 hm0_3 hm2_3 hbt3 htr3 hof3 hpart3
  have hv3 : fl.Valid w s3.frontier := hfr3.symm ▸ hv2
  have hof13 : ∀ a, ¬fl.OwnsFastAddr a → s3.mem a = s.mem a :=
    fun a ha => (hof3 a ha).trans (hof12 a ha)
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  have hsb3 : BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) seeds.bkt s3.mem :=
    hinv.seed_bkt.congr_on hw_pos fun a h1 h2 =>
      hof13 a (hv.not_ownsFast_seeds (by dsimp only [FastEpochLayout.bktHashBase] at h1; exact h1)
        (by dsimp only [FastEpochLayout.bktHashBase] at h2
            unfold offBktMeta offFpHash offBktHash at *; omega))
  have hsf3 : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp s3.mem :=
    hinv.seed_fp.congr_on hw_pos fun a h1 h2 =>
      hof13 a (hv.not_ownsFast_seeds
        (by dsimp only [FastEpochLayout.fpHashBase] at h1; unfold offFpHash at h1
            have : offBktHash ≤ offFpHash fl.c fl.w fl.U := by
              unfold offFpHash; exact Nat.le_add_right _ _
            omega)
        (by dsimp only [FastEpochLayout.fpHashBase] at h2; unfold offBktMeta; omega))
  obtain ⟨hrk_r, hrk_c⟩ := fastRKeyProg_spec hr3 hsf3 u
  have hcr_eq : (extractFastMeta fl s2.mem).curBufRole = (extractFastMeta fl s.mem).curBufRole :=
    hcr2.trans hcr1
  have hss_eq : (extractFastMeta fl s2.mem).subStep = (extractFastMeta fl s.mem).subStep :=
    hss2.trans hss1
  have hrole_lt : (extractFastMeta fl s.mem).curBufRole < 2 := hinv.role_lt
  have hold_lt : 1 - (extractFastMeta fl s.mem).curBufRole < 2 := by omega
  have hcurR_s3 : (Memory.spec 0).clientResult s3 (fastReadMetaProg (fl.pBase, 3)) =
      (extractFastMeta fl s.mem).curBufRole :=
    (clientResult_fastReadMetaProg hr3.2.1 (by decide)).trans (by
      change (extractFastMeta fl s3.mem).curBufRole = (extractFastMeta fl s.mem).curBufRole
      rw [hfm3, hcr_eq])
  have hc_m3 := memoryCost_fastReadMetaProg (fl.pBase, 3) s3
  -- Extract `s2` tier witnesses for `fastBufInsertProg`
  obtain ⟨mapCur2, mapOld2, mapBTree2, hv_cur2, hrb_cur2, hrc_cur2, hia_cur2, hna_cur2,
    hcur_snd2, hold_half2, hbt_all2, hcomp2, hsh_all2, hta_le2, htry_all2⟩ := hinv2.tiers
  have htr_cur_eq_s0 : extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s2.mem =
      extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s.mem :=
    (htr2 _ hrole_lt).trans hcur1
  have htr_cur_eq3 : extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s3.mem =
      extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s2.mem :=
    htr3 _ hrole_lt
  have hv_cur3 : ValidBufTrie (cTabWhp fl.c) (bCharWhp fl.N)
      (extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s3.mem) mapCur2 := by
    rw [htr_cur_eq3, ← hcr_eq]; exact hv_cur2
  have hrb_cur3 : RawBufTrieBounds
      (extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s3.mem) := by
    rw [htr_cur_eq3, ← hcr_eq]; exact hrb_cur2
  have hrc_cur3 : RawClearableBounds
      (extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s3.mem) := by
    rw [htr_cur_eq3, ← hcr_eq]; exact hrc_cur2
  have hia_cur3_lt : (extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole)
      s3.mem).itemAlloc < qEpochWhp fl.N := by
    rw [htr_cur_eq3, ← hcr_eq]
    have hss_lt := hinv2.subStep_lt
    omega
  have hna_cur3_le : (extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole)
      s3.mem).nodeAlloc + cTabWhp fl.c ≤ maxTrieNodesWhp fl.c fl.N := by
    rw [htr_cur_eq3, ← hcr_eq]
    have hia_le : (extractBufTrie (fl.trieL (extractFastMeta fl s2.mem).curBufRole)
        s2.mem).itemAlloc ≤ qEpochWhp fl.N := hia_cur2.trans (by have := hinv2.subStep_lt; omega)
    exact (Nat.add_le_add_right (hna_cur2.trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ hia_le) 1)) _).trans
        (cTab_add_one_mul_le_maxTrieNodes hv.thresh_le)
  have hb_ptr : b < 2 ^ globalPtrBits fl.N := by
    have hM_le : numBucketsWhp fl.N ≤ fl.N := by
      have hb_le : bWhp fl.N ≤ Nat.log 2 fl.N := by unfold bWhp; omega
      have hN_pos : 0 < fl.N := lt_of_lt_of_le (whpThreshold_pos fl.c) hv.thresh_le
      exact (Nat.pow_le_pow_right (by decide) hb_le).trans (Nat.pow_log_le_self 2 hN_pos.ne')
    exact lt_of_lt_of_le (lt_of_lt_of_le hb hM_le) (Nat.le_of_lt hv.mp_valid.nCap_lt_ptrB)
  have hcnt_ptr : cnt < 2 ^ globalPtrBits fl.N :=
    lt_of_lt_of_le (hcnt_lt.trans_le hv.bounds_le_N.2.1) (Nat.le_of_lt hv.mp_valid.nCap_lt_ptrB)
  -- Step 4: `fastBufInsertProg`
  obtain ⟨hfr4, hr4, hc4, hext4, hv_cur4, hbp4, hfm4, hm2_4, hm0_4, hbt4, htr_o4, hoi4, hof4⟩ :=
    fastBufInsertProg_spec hr3 hrole_lt hv_cur3 hrb_cur3 hna_cur3_le hia_cur3_lt hrk_lt
      hb_ptr hcnt_ptr
  generalize hs4_def : (Memory.spec 0).clientState s3
    (fastBufInsertProg ((fl.pBase, (extractFastMeta fl s.mem).curBufRole), (rk, (b, cnt)))) = s4
    at hfr4 hr4 hext4 hv_cur4 hbp4 hfm4 hm2_4 hm0_4 hbt4 htr_o4 hoi4 hof4
  have hprog_st : (Memory.spec 0).clientState s
      (fastInsertNewStepProg ((fl.pBase, u.val), ((b, cnt), v.val))) = s4 := by
    unfold fastInsertNewStepProg; dsimp only
    rw [StateTransitionSpec.clientState_bind, hs1_def,
      StateTransitionSpec.clientState_bind, hs2_def,
      StateTransitionSpec.clientState_bind, clientState_fastFeistelSplitProg, hfs_r,
      StateTransitionSpec.clientState_bind, hs3_def,
      StateTransitionSpec.clientState_bind, clientState_fastRKeyProg, hrk_r,
      StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hcurR_s3, hs4_def]
  have hprog_cost : memoryCost
      (fastInsertNewStepProg ((fl.pBase, u.val), ((b, cnt), v.val))) s ≤
      fastInsertNewStepCost fl.c := by
    unfold fastInsertNewStepProg fastInsertNewStepCost; dsimp only
    rw [Realization.memoryCost_bind', hs1_def,
      Realization.memoryCost_bind', hs2_def,
      Realization.memoryCost_bind', clientState_fastFeistelSplitProg, hfs_r,
      Realization.memoryCost_bind', hs3_def,
      Realization.memoryCost_bind', clientState_fastRKeyProg, hrk_r,
      Realization.memoryCost_bind', clientState_fastReadMetaProg, hcurR_s3]
    dsimp only [cnt, rk] at hc1 hc2 hc3 hc4 hfs_c hrk_c hc_m3 ⊢
    linarith only [hc1, hc2, hfs_c, hc3, hrk_c, hc_m3, hc4]
  have hfm_tot : extractFastMeta fl s4.mem = extractFastMeta fl s2.mem := hfm4.trans hfm3
  have hbp_tot : extractBlockPool fl.mp s4.mem = extractBlockPool fl.mp s3.mem := hbp4
  have hof_tot : ∀ a, ¬fl.OwnsFastAddr a → s4.mem a = s.mem a :=
    fun a ha => (hof4 a ha).trans (hof13 a ha)
  have hbp_inv4 : fl.bpL.StateInv
      (if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24)
      s4.mem := by
    exact ⟨hbp4.symm ▸ hbp_inv3.1, hbp4.symm ▸ hbp_inv3.2.1,
      hbp4.symm ▸ (fl.io.congr_of_outside hv3.io_valid.w_pos hbp_inv3.2.2 hoi4).1⟩
  have hbc_b4 : (extractBlockPool fl.mp s4.mem).bktCount b = cnt + 1 := by
    rw [hbp4, hbc_b3, hbp12]
  have hbc_ne4 : ∀ b' ≠ b, (extractBlockPool fl.mp s4.mem).bktCount b' =
      (extractBlockPool fl.mp s.mem).bktCount b' := fun b' hne => by
    rw [hbp4, hbc_ne3 b' hne, hbp12]
  have hns4 : (extractBlockPool fl.mp s4.mem).nSide = (extractBlockPool fl.mp s.mem).nSide + 1 := by
    rw [hbp4, hns3, hbp12]
  have hpair_eq34 : ∀ b' < numBucketsWhp fl.N, ∀ loc' < (extractBlockPool fl.mp s3.mem).bktCount b',
      bpPairAt fl.bpL s4.mem b' loc' = bpPairAt fl.bpL s3.mem b' loc' := fun b' hb' loc' hl' =>
    bpPairAt_eq_of_fixed_pool hv3 hbp_inv3 hbp4 hoi4 hb' hl'
  have hpair_old : ∀ b' < numBucketsWhp fl.N, ∀ loc' < (extractBlockPool fl.mp s2.mem).bktCount b',
      bpPairAt fl.bpL s4.mem b' loc' = bpPairAt fl.bpL s2.mem b' loc' := fun b' hb' loc' hl' => by
    have hl3 : loc' < (extractBlockPool fl.mp s3.mem).bktCount b' := by
      by_cases hbb : b' = b
      · subst hbb; rw [hbc_b3]; exact lt_trans hl' (Nat.lt_succ_self _)
      · rw [hbc_ne3 b' hbb]; exact hl'
    exact (hpair_eq34 b' hb' loc' hl3).trans (hold3 b' hb' loc' hl')
  have hpair_new : bpPairAt fl.bpL s4.mem b cnt = (keyQuotient (bWhp fl.N) u.val, v.val) := by
    have hlt3 : cnt < (extractBlockPool fl.mp s3.mem).bktCount b := by rw [hbc_b3, hbp12]; omega
    exact (hpair_eq34 b hb cnt hlt3).trans (by simpa only [hbp12] using hnew3)
  have hkey_old : ∀ b' < numBucketsWhp fl.N, ∀ loc' < (extractBlockPool fl.mp s2.mem).bktCount b',
      fastKeyAt fl seeds.bkt s4.mem b' loc' = fastKeyAt fl seeds.bkt s2.mem b' loc' :=
    fun b' hb' loc' hl' => by unfold fastKeyAt; rw [hpair_old b' hb' loc' hl']
  have hkey_old_s0 : ∀ b' < numBucketsWhp fl.N, ∀ loc' < (extractBlockPool fl.mp s.mem).bktCount b',
      fastKeyAt fl seeds.bkt s4.mem b' loc' = fastKeyAt fl seeds.bkt s.mem b' loc' := by
    intro b' hb' loc' hl'
    have h1 := hkey_old b' hb' loc' (by rw [hbp12]; exact hl')
    have h2 := fastKeyAt_eq_of_fixed_pool (θ_bkt := seeds.bkt) hv hinv.bp_inv hbp12 hoi12 hb' hl'
    exact h1.trans h2
  have hkey_new : fastKeyAt fl seeds.bkt s4.mem b cnt = u.val := by
    unfold fastKeyAt; rw [hpair_new]; dsimp only
    rw [hb_eq]; exact feistelReconstruct_epochBucket fl.c fl.U fl.N seeds.bkt u
  have href4 : PoolItemsRefines fl.U fl.V (bWhp fl.N) (bktHash fl.c fl.U fl.N seeds.bkt)
      (extractBlockPool fl.mp s4.mem).nSide
      (fun p => ((extractBlockPool fl.mp s4.mem).ownerOf p).1)
      (slotIoPairAt fl.io s4.mem) (Function.update s_abs u (some v)) :=
    poolRefines_bpAppend v hinv2.bp_inv.1.core hbp_inv4.1.core hinv2.refines habs hb hb_eq
      (by rw [hbp4, hbc_b3]) (fun b' hne => by rw [hbp4, hbc_ne3 b' hne])
      (by rw [hbp12]; exact hpair_new) hpair_old
  have hsb4 : BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) seeds.bkt s4.mem :=
    hinv.seed_bkt.congr_on hw_pos fun a h1 h2 =>
      hof_tot a (hv.not_ownsFast_seeds (by dsimp only [FastEpochLayout.bktHashBase] at h1; exact h1)
        (by dsimp only [FastEpochLayout.bktHashBase] at h2
            unfold offBktMeta offFpHash offBktHash at *; omega))
  have hsf4 : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp s4.mem :=
    hinv.seed_fp.congr_on hw_pos fun a h1 h2 =>
      hof_tot a (hv.not_ownsFast_seeds
        (by dsimp only [FastEpochLayout.fpHashBase] at h1; unfold offFpHash at h1
            have : offBktHash ≤ offFpHash fl.c fl.w fl.U := by
              unfold offFpHash; exact Nat.le_add_right _ _
            omega)
        (by dsimp only [FastEpochLayout.fpHashBase] at h2; unfold offBktMeta; omega))
  have hbc_le4 : ∀ b' < numBucketsWhp fl.N,
      (extractBlockPool fl.mp s4.mem).bktCount b' ≤ capMaxWhp fl.N := fun b' hb' => by
    by_cases hbb : b' = b
    · rw [hbb, hbc_b4]; exact Nat.succ_le_of_lt hcnt_lt
    · rw [hbc_ne4 b' hbb]; exact hinv.bkt_le_capMax b' hb'
  have hmapC_none : mapCur2 rk = none := by
    have h1 := hv_cur2.lookup_eq hrk_lt
    rw [hcr_eq, htr_cur_eq_s0, hcur_none] at h1
    exact h1.symm
  have ⟨hrb_cur4, hrc_cur4⟩ := RawBufTrieBounds.insert_and_clearable (cTabWhp fl.c)
    (bCharWhp fl.N) rk b cnt hrb_cur3 hrc_cur3
  have hins_sp := hv_cur3.insert_spec (b := b) (loc := cnt) hrk_lt
  have hia4_le : (extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole)
      s4.mem).itemAlloc ≤ (extractFastMeta fl s2.mem).subStep + 1 := by
    rw [hext4, hins_sp.2.2.2.1]
    split_ifs
    · rw [htr_cur_eq3, ← hcr_eq]; exact hia_cur2.trans (Nat.le_succ _)
    · rw [htr_cur_eq3, ← hcr_eq]; exact Nat.add_le_add_right hia_cur2 1
  have hna4_le : (extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole)
      s4.mem).nodeAlloc ≤ 1 + cTabWhp fl.c *
      (extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s4.mem).itemAlloc := by
    rw [hext4]
    by_cases hev : bufEverPresent (cTabWhp fl.c) (bCharWhp fl.N)
        (extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s3.mem) rk = true
    · obtain ⟨hn_eq, hi_eq⟩ := hins_sp.2.2.2.2.2.1 hev
      rw [hn_eq, hi_eq, htr_cur_eq3, ← hcr_eq]; exact hna_cur2
    · have hia_s : (bufInsert (cTabWhp fl.c) (bCharWhp fl.N)
          (extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s3.mem)
            rk b cnt).itemAlloc =
          (extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole)
            s3.mem).itemAlloc + 1 := by
        rw [hins_sp.2.2.2.1, ite_eq_right (by simpa using hev)]
      have hna_s : (bufInsert (cTabWhp fl.c) (bCharWhp fl.N)
          (extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s3.mem)
            rk b cnt).nodeAlloc ≤
          (extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s3.mem).nodeAlloc +
            cTabWhp fl.c := hins_sp.2.2.1
      rw [hia_s, Nat.mul_add, Nat.mul_one, ← Nat.add_assoc]
      have hna3 : (extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole)
          s3.mem).nodeAlloc ≤ 1 + cTabWhp fl.c *
          (extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole)
            s3.mem).itemAlloc := by
        rw [htr_cur_eq3, ← hcr_eq]; exact hna_cur2
      exact hna_s.trans (Nat.add_le_add_right hna3 _)
  have htr_o_eq : extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s4.mem =
      extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s2.mem :=
    htr_o4.trans (htr3 _ hold_lt)
  have hinv4 : FastEpochInvGen 1 fl
      (if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24)
      seeds s4.mem (Function.update s_abs u (some v)) := by
    refine
      { param_table := hr4.2.1
        hdr_N := hm0_4.trans (hm0_3.trans hinv2.hdr_N)
        mode_zero := hm2_4.trans (hm2_3.trans hinv2.mode_zero)
        seed_bkt := hsb4
        seed_fp := hsf4
        bp_inv := hbp_inv4
        bkt_le_capMax := hbc_le4
        refines := href4
        role_lt := by rw [hfm_tot]; exact hinv2.role_lt
        subStep_lt := by rw [hfm_tot]; exact hinv2.subStep_lt
        bkt_meta_bounds := by rw [hfm_tot]; exact hinv2.bkt_meta_bounds
        tiers := ?_ }
    refine ⟨Function.update mapCur2 rk (some (b, cnt)), mapOld2, mapBTree2, ?_⟩
    simp only [hfm_tot, hcr_eq, htr_o_eq]
    refine ⟨hv_cur4, by rw [hext4]; exact hrb_cur4, by rw [hext4]; exact hrc_cur4,
      hia4_le, hna4_le, ?_, ?_, ?_, ?_, ?_, hta_le2, ?_⟩
    · intro rk' b' loc' hm
      by_cases hre : rk' = rk
      · rw [hre, Function.update_self] at hm
        have hp := Option.some.inj hm
        have hbe : b' = b := (congrArg Prod.fst hp).symm
        have hle : loc' = cnt := (congrArg Prod.snd hp).symm
        rw [hbe, hle, hbc_b4]
        exact ⟨hb, Nat.lt_succ_self _, u, hre.symm, hkey_new⟩
      · rw [Function.update_of_ne hre] at hm
        obtain ⟨hb', hl', u', hrk', hk'⟩ := hcur_snd2 rk' b' loc' hm
        have hl4 : loc' < (extractBlockPool fl.mp s4.mem).bktCount b' := by
          by_cases hbb : b' = b
          · rw [hbb, hbc_b4]; rw [hbb, hbp12] at hl'; exact lt_trans hl' (Nat.lt_succ_self _)
          · rw [hbc_ne4 b' hbb]; rwa [hbp12] at hl'
        exact ⟨hb', hl4, u', hrk', (hkey_old b' hb' loc' hl').trans hk'⟩
    · by_cases hsub : (extractFastMeta fl s2.mem).subStep < qEpochWhp fl.N / 2
      · rw [ite_eq_left hsub] at hold_half2 ⊢
        obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := hold_half2
        rw [hcr_eq] at o1 o2 o3 o4 o5 o7
        refine ⟨o1, o2, o3, o4, o5, o6, o7, fun rk' b' loc' hm => ?_⟩
        obtain ⟨hcn, hb', hl', u', hrk', hk'⟩ := o8 rk' b' loc' hm
        have hne_rk : rk' ≠ rk := fun h => by
          subst h
          have hlo : bufLookup (cTabWhp fl.c) (bCharWhp fl.N)
              (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s2.mem) rk =
              some (b', loc') := (o1.lookup_eq hrk_lt).trans hm
          have hs_e : (extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2 := hss_eq ▸ hsub
          have hnone1 := drainTrySteps5Prog_oldLookup_none hv (hinv.toGen 0) hs_e (hold_none hs_e)
          dsimp only at hnone1
          rw [hs1_def, hcr1] at hnone1
          rw [htr2 (1 - (extractFastMeta fl s.mem).curBufRole) hold_lt, hnone1] at hlo
          cases hlo
        have hl4 : loc' < (extractBlockPool fl.mp s4.mem).bktCount b' := by
          by_cases hbb : b' = b
          · rw [hbb, hbc_b4]; rw [hbb, hbp12] at hl'; exact lt_trans hl' (Nat.lt_succ_self _)
          · rw [hbc_ne4 b' hbb]; rwa [hbp12] at hl'
        exact ⟨by rw [Function.update_of_ne hne_rk]; exact hcn, hb', hl4, u', hrk',
          (hkey_old b' hb' loc' hl').trans hk'⟩
      · rw [ite_eq_right hsub] at hold_half2 ⊢
        rwa [hcr_eq] at hold_half2
    · intro b' hb'
      obtain ⟨hvb, hbs⟩ := hbt_all2 b' hb'
      have hrb : (extractFastMeta fl s2.mem).curRole b' < 3 := (hinv2.bkt_meta_bounds b' hb').2.1
      rw [hbt4 b' hb' _ hrb, hbt3 b' hb' _ hrb]
      refine ⟨hvb, fun fp loc' hm => ?_⟩
      obtain ⟨hl', u', hfp, hk', d1, d2⟩ := hbs fp loc' hm
      have hl4 : loc' < (extractBlockPool fl.mp s4.mem).bktCount b' := by
        by_cases hbb : b' = b
        · rw [hbb, hbc_b4]; rw [hbb, hbp12] at hl'; exact lt_trans hl' (Nat.lt_succ_self _)
        · rw [hbc_ne4 b' hbb]; rwa [hbp12] at hl'
      refine ⟨hl4, u', hfp, (hkey_old b' hb' loc' hl').trans hk', fun b₁ l₁ hm₁ => ?_,
        fun b₂ l₂ hm₂ => ?_⟩
      · by_cases hre : rKeyOf fl.c fl.U fl.N seeds.fp u' = rk
        · rw [hre, Function.update_self] at hm₁
          have hp := Option.some.inj hm₁
          have hbe : b₁ = b := (congrArg Prod.fst hp).symm
          have hle : l₁ = cnt := (congrArg Prod.snd hp).symm
          rw [hbe, hle, hkey_new]
          intro heq
          have hu'e : u = u' := Fin.ext heq
          obtain ⟨u₀, _, hu₀, _, _, _, hs₀⟩ := hinv2.bktSlot_refines hb' hl'
          have hsub_eq : u₀ = u := (Fin.ext (hu₀.trans hk')).trans hu'e.symm
          rw [hsub_eq, habs] at hs₀; cases hs₀
        · rw [Function.update_of_ne hre] at hm₁
          obtain ⟨hb₁, hl₁, _⟩ := hcur_snd2 _ b₁ l₁ hm₁
          rw [hkey_old b₁ hb₁ l₁ hl₁]; exact d1 b₁ l₁ hm₁
      · by_cases hsub : (extractFastMeta fl s2.mem).subStep < qEpochWhp fl.N / 2
        · rw [ite_eq_left hsub] at hold_half2
          obtain ⟨_, hb₂, hl₂, _⟩ := hold_half2.2.2.2.2.2.2.2 _ b₂ l₂ hm₂
          rw [hkey_old b₂ hb₂ l₂ hl₂]; exact d2 b₂ l₂ hm₂
        · rw [ite_eq_right hsub] at hold_half2
          rw [hold_half2.1] at hm₂; cases hm₂
    · intro b' hb' loc' hl'
      by_cases hnew : b' = b ∧ loc' = cnt
      · rcases hnew with ⟨rfl, rfl⟩
        refine ⟨u, hkey_new, Or.inl (by rw [Function.update_self])⟩
      · have hl2 : loc' < (extractBlockPool fl.mp s2.mem).bktCount b' := by
          by_cases hbb : b' = b
          · subst hbb; rw [hbc_b4] at hl'; rw [hbp12]
            exact lt_of_le_of_ne (Nat.le_of_lt_succ hl') (fun h => hnew ⟨rfl, h⟩)
          · rwa [hbc_ne4 b' hbb, ← hbp12] at hl'
        obtain ⟨u', hk', hmem⟩ := hcomp2 b' hb' loc' hl2
        refine ⟨u', (hkey_old b' hb' loc' hl2).trans hk', ?_⟩
        rcases hmem with hmc | hmo | hmb
        · left
          have hne_rk : rKeyOf fl.c fl.U fl.N seeds.fp u' ≠ rk := fun h => by
            rw [h, hmapC_none] at hmc; cases hmc
          rw [Function.update_of_ne hne_rk]; exact hmc
        · exact Or.inr (Or.inl hmo)
        · exact Or.inr (Or.inr hmb)
    · intro b' hb' hsc
      obtain ⟨p1, p2, p3, p4, sm, hvs, hsm⟩ := hsh_all2 b' hb' hsc
      have hsr : shadowRoleOf ((extractFastMeta fl s2.mem).curRole b') < 3 :=
        (shadowRoleOf_lt_and_ne (hinv2.bkt_meta_bounds b' hb').2.1).1
      rw [hbt4 b' hb' _ hsr, hbt3 b' hb' _ hsr]
      by_cases hbb : b' = b
      · subst hbb
        obtain ⟨hs_a, hs_b⟩ := hsh_sl2 hb hsc
        rw [hbp12] at p1 p3 p4
        rw [hbc_b4]
        refine ⟨lt_trans p1 (Nat.lt_succ_self _), p2, ?_, ?_, sm, hvs, hsm⟩
        · have : cnt + 1 - ((extractFastMeta fl s2.mem).shadowCode b' - 1) =
              cnt - ((extractFastMeta fl s2.mem).shadowCode b' - 1) + 1 := by omega
          rw [this]; rw [hbp1] at hs_a; omega
        · have : cnt + 1 - ((extractFastMeta fl s2.mem).shadowCode b' - 1) =
              cnt - ((extractFastMeta fl s2.mem).shadowCode b' - 1) + 1 := by omega
          rw [this]; rw [hbp1] at hs_b; omega
      · rw [hbc_ne4 b' hbb]; rw [hbp12] at p1 p3 p4
        exact ⟨p1, p2, p3, p4, sm, hvs, hsm⟩
    · intro hta
      obtain ⟨hsub, hb_t, hs_t, htp, hsc_t, hbd, tm, hvt, htm1, htm2⟩ := htry_all2 hta
      have htr_lt : tryRoleOf ((extractFastMeta fl s2.mem).curRole
          (extractFastMeta fl s2.mem).tryBkt) < 3 :=
        (tryRoleOf_lt_and_ne (hinv2.bkt_meta_bounds _ hb_t).2.1).1
      rw [hbt4 _ hb_t _ htr_lt, hbt3 _ hb_t _ htr_lt]
      refine ⟨hsub, hb_t, hs_t, ?_, hsc_t, ?_, tm, hvt, fun fp loc' hm => ?_,
        fun loc' hl' u' hk' hmb => ?_⟩
      · by_cases hbb : (extractFastMeta fl s2.mem).tryBkt = b
        · rw [hbb, hbc_b4]; rw [hbb, hbp12] at htp; exact htp.trans (Nat.le_succ _)
        · rw [hbc_ne4 _ hbb]; rwa [hbp12] at htp
      · by_cases hbb : (extractFastMeta fl s2.mem).tryBkt = b
        · rw [hbb, hbc_b4]
          have hta1 : (extractFastMeta fl s1.mem).tryAct = 1 := hta2 ▸ hta
          have htb1 : (extractFastMeta fl s1.mem).tryBkt = b := htb2 ▸ hbb
          have hsl := htry_sl1 hta1 htb1
          rw [← hti2, ← htp2] at hsl
          rw [hbb, hbp12] at htp
          have hdiff : cnt + 1 - (extractFastMeta fl s2.mem).tryPos ≤
              (cnt - (extractFastMeta fl s2.mem).tryPos) + 1 := by omega
          omega
        · rw [hbc_ne4 _ hbb]; rwa [hbp12] at hbd
      · obtain ⟨hl', u', hk', hmb, hfp⟩ := htm1 fp loc' hm
        exact ⟨hl', u', (hkey_old _ hb_t loc' (lt_of_lt_of_le hl' htp)).trans hk', hmb, hfp⟩
      · exact htm2 loc' hl' u' ((hkey_old _ hb_t loc' (lt_of_lt_of_le hl' htp)).symm.trans hk') hmb
  rw [hprog_st]
  refine ⟨hfr4.trans (hfr3.trans (hfr2.trans hfr1)), hprog_cost, hinv4,
    by rw [hfm_tot, hcr_eq], by rw [hfm_tot, hss_eq], hns4, hof_tot, ?_, ?_⟩
  · intro hup
    obtain ⟨hp1, hp2, hp3⟩ := hpart3 hup
    obtain ⟨hu1, hu2, hu3⟩ := hpg12 hup
    have h4eq : extractPagePair fl.io.pgL s4.mem = extractPagePair fl.io.pgL s3.mem ∧
        ∀ idx < (extractPagePair fl.io.pgL s3.mem).virtLen fl.io.partner.side,
          slotIoPairAt fl.io.partner s4.mem idx = slotIoPairAt fl.io.partner s3.mem idx := by
      have hpg := pagePair_partner_eq_of_io hv3 hup hbp_inv3 hoi4
      exact ⟨hpg.2.1, hpg.2.2⟩
    refine ⟨?_, ?_, fun idx hidx => ?_⟩
    · rw [h4eq.1, hp1, hu2]
    · rw [h4eq.1, hp2, hu2]
    · have hidx3 : idx < (extractPagePair fl.io.pgL s3.mem).virtLen fl.io.partner.side := by
        rw [hp1, hu2]; exact hidx
      have hidx2 : idx < (extractPagePair fl.io.pgL s2.mem).virtLen fl.io.partner.side := by
        rw [hu2]; exact hidx
      exact (h4eq.2 idx hidx3).trans ((hp3 idx hidx2).trans (hu3 idx hidx))
  · intro S hS id b' loc' u' hchk hb' hl' hk'
    have hrole4 : (extractFastMeta fl s4.mem).curBufRole =
        (extractFastMeta fl s.mem).curBufRole := by rw [hfm_tot, hcr_eq]
    rw [hrole4] at hchk
    obtain ⟨_, rk', hrk'lt, _, hmk'⟩ := hv_cur4.checkSlot_some hchk
    by_cases hre : rk' = rk
    · rw [hre, Function.update_self] at hmk'
      have hp := Option.some.inj hmk'
      have hbe : b' = b := (congrArg Prod.fst hp).symm
      have hle : loc' = cnt := (congrArg Prod.snd hp).symm
      rw [hbe, hle, hkey_new] at hk'
      have : u' = u := Fin.ext hk'.symm
      rw [this]; exact Finset.mem_insert_self u S
    · rw [Function.update_of_ne hre] at hmk'
      obtain ⟨id0, _, hchk0⟩ := hv_cur2.exists_checkSlot_of_map_some hmk'
      rw [hcr_eq, htr_cur_eq_s0] at hchk0
      obtain ⟨_, hl2, _⟩ := hcur_snd2 rk' b' loc' hmk'
      rw [hbp12] at hl2
      have hk0 : fastKeyAt fl seeds.bkt s.mem b' loc' = u'.val :=
        (hkey_old_s0 b' hb' loc' hl2).symm.trans hk'
      exact Finset.mem_insert_of_mem (hS id0 b' loc' u' hchk0 hb' hl2 hk0)

/-- Good-seed preservation for `fastInsertNewStepProg`: upgrades `FastSubEpochGood 0 0 0` to
`FastSubEpochGood 1 5 slack'` (`drainPotential` grows by at most `+1 ≤ 5` from `bktCount b + 1`). -/
private theorem fastInsertNewStepProg_good {fl : FastEpochLayout} {w b : ℕ}
    {win : EpochWindowSpec fl.c fl.U fl.N} {e : Fin win.numSubs}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {hgood : GoodEpochSeeds win seeds}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hg : FastSubEpochGood 0 0 0 win e seeds hgood s.mem s_abs)
    (u : Fin fl.U) (v : Fin fl.V)
    (hu_in : u ∈ win.subUnions e)
    (hb_eq : b = epochBucket fl.c fl.U fl.N seeds.bkt u)
    (habs : s_abs u = none)
    (hn_lt : (extractBlockPool fl.mp s.mem).nSide < fl.N)
    (hcnt_lt : (extractBlockPool fl.mp s.mem).bktCount b < capMaxWhp fl.N)
    (hcap_io : fl.io.AppendCap (extractBlockPool fl.mp s.mem).nSide s.mem)
    (hcur_none : bufLookup (cTabWhp fl.c) (bCharWhp fl.N)
      (extractBufTrie (fl.trieL (extractFastMeta fl s.mem).curBufRole) s.mem)
      (rKeyOf fl.c fl.U fl.N seeds.fp u) = none)
    (hold_none : (extractFastMeta fl s.mem).subStep < qEpochWhp fl.N / 2 →
      bufLookup (cTabWhp fl.c) (bCharWhp fl.N)
        (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s.mem).curBufRole)) s.mem)
        (rKeyOf fl.c fl.U fl.N seeds.fp u) = none) :
    let cnt := (extractBlockPool fl.mp s.mem).bktCount b
    let s' := (Memory.spec 0).clientState s
      (fastInsertNewStepProg ((fl.pBase, u.val), ((b, cnt), v.val)))
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    FastSubEpochGood 1 5 slack' win e seeds hgood s'.mem (Function.update s_abs u (some v)) := by
  dsimp only
  have hb : b < numBucketsWhp fl.N := hb_eq ▸ epochBucket_lt fl.c fl.U fl.N seeds.bkt u
  set cnt := (extractBlockPool fl.mp s.mem).bktCount b
  set rk := rKeyOf fl.c fl.U fl.N seeds.fp u
  have hrk_lt : rk < 2 ^ (cTabWhp fl.c * bCharWhp fl.N) := rKeyOf_lt fl.c fl.U fl.N seeds.fp u
  have hinv_s' := (fastInsertNewStepProg_spec hv hg.inv.toInv u v hb_eq habs hn_lt hcnt_lt
    hcap_io hcur_none hold_none).2.2.1
  -- Intermediate states `s1` (`drainTrySteps5Prog`), `s2` (`fastShadowSteps8Prog`),
  -- `s3` (`fastBpAppendProg`), `s4` (`fastBufInsertProg`)
  have hg1 : FastSubEpochGood 0 0 0 win e seeds hgood
      ((Memory.spec 0).clientState s (drainTrySteps5Prog fl.pBase)).mem s_abs :=
    drainTrySteps5Prog_good hv hg hb hcnt_lt
  obtain ⟨hfr1, _, hinv1, hbp1, _, hoi1, hof1, hcr1, hss1, _⟩ :=
    drainTrySteps5Prog_spec hv hg.inv hb hcnt_lt
  generalize hs1_def : (Memory.spec 0).clientState s (drainTrySteps5Prog fl.pBase) = s1
    at hg1 hfr1 hinv1 hbp1 hoi1 hof1 hcr1 hss1
  have hv1 : fl.Valid w s1.frontier := hfr1.symm ▸ hv
  have hsh_in : b < numBucketsWhp fl.N → (extractFastMeta fl s1.mem).shadowCode b ≠ 0 →
      4 * (extractFastMeta fl s1.mem).shadowIns b +
        5 * ((extractBlockPool fl.mp s1.mem).bktCount b -
          ((extractFastMeta fl s1.mem).shadowCode b - 1)) +
        shSlack fl s1.mem b ≤ 20 * slabScale fl.N ^ 12 ∧
      8 * ((extractFastMeta fl s1.mem).curIns b - 6 * slabScale fl.N ^ 12) +
        ((extractBlockPool fl.mp s1.mem).bktCount b -
          ((extractFastMeta fl s1.mem).shadowCode b - 1)) +
        shSlack fl s1.mem b ≤ 4 * slabScale fl.N ^ 12 := fun hb' hsc => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hsh, _, _⟩ := hinv1.tiers
    obtain ⟨_, _, h1, h2, _⟩ := hsh b hb' hsc
    dsimp only [shSlack]
    have hm1 := min_le_left
      (20 * slabScale fl.N ^ 12 - (4 * (extractFastMeta fl s1.mem).shadowIns b +
        5 * ((extractBlockPool fl.mp s1.mem).bktCount b -
          ((extractFastMeta fl s1.mem).shadowCode b - 1))))
      (4 * slabScale fl.N ^ 12 - (8 * ((extractFastMeta fl s1.mem).curIns b -
        6 * slabScale fl.N ^ 12) + ((extractBlockPool fl.mp s1.mem).bktCount b -
          ((extractFastMeta fl s1.mem).shadowCode b - 1))))
    have hm2 := min_le_right
      (20 * slabScale fl.N ^ 12 - (4 * (extractFastMeta fl s1.mem).shadowIns b +
        5 * ((extractBlockPool fl.mp s1.mem).bktCount b -
          ((extractFastMeta fl s1.mem).shadowCode b - 1))))
      (4 * slabScale fl.N ^ 12 - (8 * ((extractFastMeta fl s1.mem).curIns b -
        6 * slabScale fl.N ^ 12) + ((extractBlockPool fl.mp s1.mem).bktCount b -
          ((extractFastMeta fl s1.mem).shadowCode b - 1))))
    omega
  have hsh_sl_out := fastShadowSteps8Prog_spec_slack (b := b) (k := shSlack fl s1.mem b)
    hv1 hinv1 hsh_in
  obtain ⟨hfr2, _, hinv2, hbp2, hcr2, hss2, hdp2, hta2, htb2, hts2, htp2, _, _, htr2, hoi2,
    hof2, hoth2, _⟩ := fastShadowSteps8Prog_spec (b := b) hv1 hinv1
  generalize hs2_def : (Memory.spec 0).clientState s1 (fastShadowSteps8Prog (fl.pBase, b)) = s2
    at hfr2 hinv2 hbp2 hcr2 hss2 hdp2 hta2 htb2 hts2 htp2 htr2 hoi2 hof2 hoth2 hsh_sl_out
  have hv2 : fl.Valid w s2.frontier := hfr2.symm ▸ hv1
  have hbp12 : extractBlockPool fl.mp s2.mem = extractBlockPool fl.mp s.mem := hbp2.trans hbp1
  have hoi12 : ∀ a, fl.io.OwnsAddr a → s2.mem a = s.mem a :=
    fun a ha => (hoi2 a ha).trans (hoi1 a ha)
  have hpg12 : fl.io.usePaged ≠ 0 →
      extractPagePair fl.io.pgL s2.mem = extractPagePair fl.io.pgL s.mem := fun hup =>
    (pagePair_partner_eq_of_io hv hup hg.inv.bp_inv hoi12).2.1
  have hr2 := hinv2.ready hv2 rfl
  obtain ⟨hfs_r, _⟩ := fastFeistelSplitProg_spec hr2 hinv2.seed_bkt u
  have hq_lt : keyQuotient (bWhp fl.N) u.val < 2 ^ fl.io.pgL.qBits :=
    (keyQuotient_bWhp_lt hv.N_le_U u).trans_le (Nat.pow_le_pow_right Nat.one_lt_two.le hv.qBits_le)
  have hv_lt : v.val < 2 ^ fl.io.pgL.vBits := by
    rw [hv.vBits_eq]; exact v.isLt.trans_le (Nat.le_pow_clog Nat.one_lt_two fl.V)
  have hcap_io2 : fl.io.AppendCap (extractBlockPool fl.mp s2.mem).nSide s2.mem := by
    unfold SlotIoLayout.AppendCap at hcap_io ⊢
    by_cases hup : fl.io.usePaged = 0
    · rw [ite_eq_left hup] at hcap_io ⊢; rwa [hbp12]
    · rw [ite_eq_right hup] at hcap_io ⊢; rwa [hpg12 hup]
  obtain ⟨hfr3, hr3, _, hbp_inv3, _, hbc_b3, hbc_ne3, _, hold3, hfm3, _, _, _, htr3, hof3, _⟩ :=
    fastBpAppendProg_spec hr2 hinv2.bp_inv hb (by rw [hbp12]; exact hn_lt)
      (by rw [hbp12]; exact hcnt_lt) hcap_io2 hq_lt hv_lt
  generalize hs3_def : (Memory.spec 0).clientState s2
    (fastBpAppendProg ((fl.pBase, b), (keyQuotient (bWhp fl.N) u.val, v.val))) = s3
    at hfr3 hr3 hbp_inv3 hbc_b3 hbc_ne3 hold3 hfm3 htr3 hof3
  have hv3 : fl.Valid w s3.frontier := hfr3.symm ▸ hv2
  have hof13 : ∀ a, ¬fl.OwnsFastAddr a → s3.mem a = s.mem a :=
    fun a ha => (hof3 a ha).trans ((hof2 a ha).trans (hof1 a ha))
  have hw_pos : 0 < fl.w := hv.w_eq ▸ hv.w_pos
  have hsf3 : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w (redWidthWhp fl.U)
      (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N) seeds.fp s3.mem :=
    hg.inv.seed_fp.congr_on hw_pos fun a h1 h2 =>
      hof13 a (hv.not_ownsFast_seeds
        (by dsimp only [FastEpochLayout.fpHashBase] at h1; unfold offFpHash at h1
            have : offBktHash ≤ offFpHash fl.c fl.w fl.U := by
              unfold offFpHash; exact Nat.le_add_right _ _
            omega)
        (by dsimp only [FastEpochLayout.fpHashBase] at h2; unfold offBktMeta; omega))
  obtain ⟨hrk_r, _⟩ := fastRKeyProg_spec hr3 hsf3 u
  have hrole_lt : (extractFastMeta fl s1.mem).curBufRole < 2 := hinv1.role_lt
  have hold_lt : 1 - (extractFastMeta fl s1.mem).curBufRole < 2 := by omega
  have hcr2_r : (Memory.spec 0).clientResult s3 (fastReadMetaProg (fl.pBase, 3)) =
      (extractFastMeta fl s1.mem).curBufRole :=
    (clientResult_fastReadMetaProg hr3.2.1 (by decide)).trans (by
      change (extractFastMeta fl s3.mem).curBufRole = (extractFastMeta fl s1.mem).curBufRole
      rw [hfm3, hcr2])
  have hbi_r := fastBufInsertProg_ready (role := (extractFastMeta fl s1.mem).curBufRole)
    (rk := rk) (b := b) (loc := cnt) hr3
  generalize hs4_def : (Memory.spec 0).clientState s3
    (fastBufInsertProg ((fl.pBase, (extractFastMeta fl s1.mem).curBufRole), (rk, (b, cnt)))) = s4
    at hbi_r
  have hbi_out : ∀ a, ¬(fl.trieL (extractFastMeta fl s1.mem).curBufRole).OwnsAddr a →
      s4.mem a = s3.mem a := hbi_r.2.2.2 hrole_lt
  obtain ⟨hbp4, hfm4, _, _, _, htr_o4, hoi4, _⟩ :=
    fastTrieMod_frame hv3 hrole_lt hbi_out
  have hs'_eq : (Memory.spec 0).clientState s
      (fastInsertNewStepProg ((fl.pBase, u.val), ((b, cnt), v.val))) = s4 := by
    unfold fastInsertNewStepProg; dsimp only
    rw [StateTransitionSpec.clientState_bind, hs1_def,
      StateTransitionSpec.clientState_bind, hs2_def,
      StateTransitionSpec.clientState_bind, clientState_fastFeistelSplitProg, hfs_r,
      StateTransitionSpec.clientState_bind, hs3_def,
      StateTransitionSpec.clientState_bind, clientState_fastRKeyProg, hrk_r,
      StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hcr2_r, hs4_def]
  rw [hs'_eq] at hinv_s' ⊢
  have hfm_24 : extractFastMeta fl s4.mem = extractFastMeta fl s2.mem := hfm4.trans hfm3
  have hold_eq : extractBufTrie (fl.trieL (1 - (extractFastMeta fl s4.mem).curBufRole)) s4.mem =
      extractBufTrie (fl.trieL (1 - (extractFastMeta fl s1.mem).curBufRole)) s1.mem := by
    rw [hfm_24, hcr2]
    exact (htr_o4.trans ((htr3 _ hold_lt).trans (htr2 _ hold_lt)))
  have hbc_b4 : (extractBlockPool fl.mp s4.mem).bktCount b =
      (extractBlockPool fl.mp s1.mem).bktCount b + 1 := by
    rw [hbp4, hbc_b3, hbp2]
  have hbc_ne4 : ∀ b' ≠ b, (extractBlockPool fl.mp s4.mem).bktCount b' =
      (extractBlockPool fl.mp s1.mem).bktCount b' := fun b' hne => by
    rw [hbp4, hbc_ne3 b' hne, hbp2]
  have hkey_14 : ∀ b' < numBucketsWhp fl.N,
      ∀ loc' < (extractBlockPool fl.mp s1.mem).bktCount b',
      fastKeyAt fl seeds.bkt s4.mem b' loc' = fastKeyAt fl seeds.bkt s1.mem b' loc' := by
    intro b' hb' loc' hl'
    have h43 : bpPairAt fl.bpL s4.mem b' loc' = bpPairAt fl.bpL s3.mem b' loc' := by
      have hl3 : loc' < (extractBlockPool fl.mp s3.mem).bktCount b' := by
        by_cases hbb : b' = b
        · subst hbb; rw [hbc_b3, hbp2]; exact lt_trans hl' (Nat.lt_succ_self _)
        · rw [hbc_ne3 b' hbb, hbp2]; exact hl'
      exact bpPairAt_eq_of_fixed_pool hv3 hbp_inv3 hbp4 hoi4 hb' hl3
    have h32 : bpPairAt fl.bpL s3.mem b' loc' = bpPairAt fl.bpL s2.mem b' loc' :=
      hold3 b' hb' loc' (by rw [hbp2]; exact hl')
    have h21 : fastKeyAt fl seeds.bkt s2.mem b' loc' = fastKeyAt fl seeds.bkt s1.mem b' loc' :=
      fastKeyAt_eq_of_fixed_pool hv1 hinv1.bp_inv hbp2 hoi2 hb' hl'
    unfold fastKeyAt at h21 ⊢; rw [h43, h32]; exact h21
  have hold_bounds : (extractFastMeta fl s1.mem).subStep < qEpochWhp fl.N / 2 →
      ∀ id b' loc', bufCheckSlot
        (extractBufTrie (fl.trieL (1 - (extractFastMeta fl s1.mem).curBufRole)) s1.mem) id =
          some (b', loc') →
        b' < numBucketsWhp fl.N ∧ loc' < (extractBlockPool fl.mp s1.mem).bktCount b' := by
    intro hsub1 id b' loc' hchk
    obtain ⟨_, mapO1, _, _, _, _, _, _, _, ho1, _⟩ := hinv1.tiers
    rw [ite_eq_left hsub1] at ho1
    obtain ⟨hv_o, _, _, _, _, _, _, hso⟩ := ho1
    obtain ⟨_, rk', _, _, hm'⟩ := hv_o.checkSlot_some hchk
    obtain ⟨_, hb', hl', _⟩ := hso rk' b' loc' hm'
    exact ⟨hb', hl'⟩
  have hcr_14 : (extractFastMeta fl s4.mem).curBufRole = (extractFastMeta fl s1.mem).curBufRole :=
    by rw [hfm_24, hcr2]
  have hss_14 : (extractFastMeta fl s4.mem).subStep = (extractFastMeta fl s1.mem).subStep := by
    rw [hfm_24, hss2]
  have hdp_14 : (extractFastMeta fl s4.mem).drainPos = (extractFastMeta fl s1.mem).drainPos := by
    rw [hfm_24, hdp2]
  have hta_14 : (extractFastMeta fl s4.mem).tryAct = (extractFastMeta fl s1.mem).tryAct := by
    rw [hfm_24, hta2]
  have htb_14 : (extractFastMeta fl s4.mem).tryBkt = (extractFastMeta fl s1.mem).tryBkt := by
    rw [hfm_24, htb2]
  have hts_14 : (extractFastMeta fl s4.mem).trySalt = (extractFastMeta fl s1.mem).trySalt := by
    rw [hfm_24, hts2]
  have htp_14 : (extractFastMeta fl s4.mem).tryPos = (extractFastMeta fl s1.mem).tryPos := by
    rw [hfm_24, htp2]
  refine
    { inv := hinv_s'
      live_sub := fun u' hu' => by
        by_cases he : u' = u
        · exact he ▸ hu_in
        · rw [Function.update_of_ne he] at hu'; exact hg.live_sub u' hu'
      old_sub := fun hsub id b' loc' u' hchk hb' _ hk' => by
        have hsub1 : (extractFastMeta fl s1.mem).subStep < qEpochWhp fl.N / 2 := hss_14 ▸ hsub
        rw [hold_eq] at hchk
        have hl1 := (hold_bounds hsub1 id b' loc' hchk).2
        exact hg1.old_sub hsub1 id b' loc' u' hchk hb' hl1
          ((hkey_14 b' hb' loc' hl1).symm.trans hk')
      try_match := fun hta hdp b' loc' hchk => by
        rw [hold_eq, hdp_14] at hchk hdp
        rw [htb_14]
        exact hg1.try_match (hta_14 ▸ hta) hdp b' loc' hchk
      trySalt_le := fun hta => by
        rw [hts_14, htb_14]
        exact hg1.trySalt_le (hta_14 ▸ hta)
      pot_le := fun hsub => by
        have hsub1 : (extractFastMeta fl s1.mem).subStep < qEpochWhp fl.N / 2 := hss_14 ▸ hsub
        have hbad_imp : ∀ id, isBadOldSlot win e seeds s4.mem id →
            isBadOldSlot win e seeds s1.mem id := fun id h => by
          rcases h with ⟨b', loc', u', hchk, hb', _, hk', hcol⟩
          rw [hold_eq] at hchk
          have hl1 := (hold_bounds hsub1 id b' loc' hchk).2
          exact ⟨b', loc', u', hchk, hb', hl1, (hkey_14 b' hb' loc' hl1).symm.trans hk', hcol⟩
        have hia_eq : (extractBufTrie (fl.trieL
              (1 - (extractFastMeta fl s4.mem).curBufRole)) s4.mem).itemAlloc =
            (extractBufTrie (fl.trieL
              (1 - (extractFastMeta fl s1.mem).curBufRole)) s1.mem).itemAlloc := by
          rw [hold_eq]
        have hnb_mono : ∀ k, nBadFrom win e seeds s4.mem k ≤
            nBadFrom win e seeds s1.mem k := fun k =>
          nBadFrom_mono_of_imp hia_eq fun id _ hb_i => hbad_imp id hb_i
        have hpot_s4 : drainPotential win e seeds hgood s4.mem ≤
            drainPotential win e seeds hgood s1.mem + 1 := by
          unfold drainPotential; dsimp only
          rw [hia_eq, hdp_14, hta_14, htb_14]
          by_cases hta1 : (extractFastMeta fl s1.mem).tryAct = 1
          · rw [ite_eq_left hta1, ite_eq_left hta1, hts_14, htp_14]
            have hnb := hnb_mono ((extractFastMeta fl s1.mem).drainPos + 1)
            have hbc_tb : (extractBlockPool fl.mp s4.mem).bktCount
                (extractFastMeta fl s1.mem).tryBkt ≤
                (extractBlockPool fl.mp s1.mem).bktCount
                  (extractFastMeta fl s1.mem).tryBkt + 1 := by
              by_cases hbb : (extractFastMeta fl s1.mem).tryBkt = b
              · rw [hbb, hbc_b4]
              · rw [hbc_ne4 _ hbb]; exact Nat.le_succ _
            have hsub_t : (extractBlockPool fl.mp s4.mem).bktCount
                (extractFastMeta fl s1.mem).tryBkt - (extractFastMeta fl s1.mem).tryPos ≤
                ((extractBlockPool fl.mp s1.mem).bktCount
                  (extractFastMeta fl s1.mem).tryBkt - (extractFastMeta fl s1.mem).tryPos) + 1 := by
              omega
            have hm1 := Nat.mul_le_mul_left (sMaxWhp fl.c fl.N * (capMaxWhp fl.N + 2) + 1) hnb
            have hm2 := Nat.mul_le_mul_left (4 * slabScale fl.N ^ 12) hnb
            omega
          · rw [ite_eq_right hta1, ite_eq_right hta1]
            have hnb0 := hnb_mono (extractFastMeta fl s1.mem).drainPos
            have hnb1 := hnb_mono ((extractFastMeta fl s1.mem).drainPos + 1)
            have hsh_le : shTerm fl win e seeds s4.mem ≤ shTerm fl win e seeds s1.mem := by
              classical
              unfold shTerm; dsimp only
              by_cases hbad4 : isBadOldSlot win e seeds s4.mem (extractFastMeta fl s4.mem).drainPos
              · have hbad1 : isBadOldSlot win e seeds s1.mem
                    (extractFastMeta fl s1.mem).drainPos := hbad_imp _ (by rwa [hdp_14] at hbad4)
                rw [ite_eq_left hbad4, ite_eq_left hbad1, hdp_14, hold_eq]
                cases hchk : bufCheckSlot
                    (extractBufTrie (fl.trieL
                      (1 - (extractFastMeta fl s1.mem).curBufRole)) s1.mem)
                    (extractFastMeta fl s1.mem).drainPos with
                | none => exact le_rfl
                | some p =>
                  dsimp only
                  by_cases hpb : p.1 = b
                  · rw [hpb]
                    unfold shCost
                    by_cases hsc4 : (extractFastMeta fl s4.mem).shadowCode b = 0
                    · rw [ite_eq_left hsc4]; exact Nat.zero_le _
                    · have hsc2 : (extractFastMeta fl s2.mem).shadowCode b ≠ 0 := by
                        rwa [hfm_24] at hsc4
                      have hsc1 : (extractFastMeta fl s1.mem).shadowCode b ≠ 0 := fun h0 =>
                        hsc2 (by
                          have heq := fastShadowSteps8Prog_eq_of_shadowZero
                            (b := b) hinv1.param_table hb h0
                          have : s2 = s1 := hs2_def.symm.trans heq
                          rw [this]; exact h0)
                      rw [ite_eq_right hsc4, ite_eq_right hsc1]
                      obtain ⟨hsl1, hsl2⟩ := hsh_sl_out hb hsc2
                      have hcnt1_eq : (extractBlockPool fl.mp s4.mem).bktCount b =
                          (extractBlockPool fl.mp s1.mem).bktCount b + 1 := hbc_b4
                      have hslack_ge : shSlack fl s1.mem b ≤ shSlack fl s4.mem b := by
                        have h4_le : 4 * (extractFastMeta fl s2.mem).shadowIns b +
                            5 * ((extractBlockPool fl.mp s1.mem).bktCount b + 1 -
                              ((extractFastMeta fl s2.mem).shadowCode b - 1)) ≤
                            4 * (extractFastMeta fl s2.mem).shadowIns b +
                              5 * ((extractBlockPool fl.mp s1.mem).bktCount b -
                                ((extractFastMeta fl s2.mem).shadowCode b - 1)) + 5 := by omega
                        have h8_le : 8 * ((extractFastMeta fl s2.mem).curIns b -
                            6 * slabScale fl.N ^ 12) +
                            ((extractBlockPool fl.mp s1.mem).bktCount b + 1 -
                              ((extractFastMeta fl s2.mem).shadowCode b - 1)) ≤
                            8 * ((extractFastMeta fl s2.mem).curIns b -
                              6 * slabScale fl.N ^ 12) +
                              ((extractBlockPool fl.mp s1.mem).bktCount b -
                                ((extractFastMeta fl s2.mem).shadowCode b - 1)) + 1 := by omega
                        conv_rhs => unfold shSlack; dsimp only
                        rw [hfm_24, hcnt1_eq]
                        exact le_min (by omega) (by omega)
                      exact Nat.sub_le_sub_left hslack_ge _
                  · obtain ⟨_, hci, hsi, hsc⟩ := hoth2 p.1 hpb
                    have heq_cost : shCost fl s4.mem p.1 = shCost fl s1.mem p.1 := by
                      unfold shCost shSlack; dsimp only
                      rw [hfm_24, hci, hsi, hsc, hbc_ne4 p.1 hpb]
                    rw [heq_cost]
              · rw [ite_eq_right hbad4]; exact Nat.zero_le _
            have hm1 := Nat.mul_le_mul_left (sMaxWhp fl.c fl.N * (capMaxWhp fl.N + 2) + 1) hnb0
            have hm2 := Nat.mul_le_mul_left (4 * slabScale fl.N ^ 12) hnb1
            omega
        have hg_pot := hg1.pot_le hsub1
        rw [hss_14]
        omega }

/-! ## Section 5: Top-Level Fast-Mode `insert` (`fastInsertProg`) -/

/-- Worst-case `memoryCost` bound for checking `rKey` freedom across `BufCur` (and `BufOld` in the
first half of a sub-epoch). -/
@[expose] def fastCheckRKeyFreeCost (c : ℕ) : ℕ :=
  4 * cTabWhp c + 60

/-- Read-only check returning `0` iff `rKeyOf u` is absent from active `BufCur` (and from `BufOld`
when `subStep < Q / 2`), and `1` iff it collides with an active slot (`¬ReadsWidth`). -/
private def fastCheckRKeyFreeProg : ℕ × ℕ → Memory.Prog ℕ
  | (pBase, u_val) => do
    let rk ← fastRKeyProg (pBase, u_val)
    let curR ← fastReadMetaProg (pBase, 3)
    if curR < 2 then do
      let hc ← fastBufLookupProg ((pBase, curR), rk)
      if hc.1 ≠ 0 then
        pure 1
      else do
        let ss ← fastReadMetaProg (pBase, 4)
        let qMax ← Memory.read (pBase + 23)
        if ss < qMax / 2 then do
          let ho ← fastBufLookupProg ((pBase, 1 - curR), rk)
          if ho.1 ≠ 0 then pure 1 else pure 0
        else pure 0
    else pure 1

@[simp] private theorem runClient_state_fastCheckRKeyFreeProg (x : ℕ × ℕ) (s : Memory.State) :
    ((Memory.spec 0).runClient s (fastCheckRKeyFreeProg x)).2.1 = s := by
  rcases x with ⟨pBase, u_val⟩
  change (Memory.spec 0).clientState s (fastCheckRKeyFreeProg (pBase, u_val)) = s
  unfold fastCheckRKeyFreeProg; dsimp only
  rw [StateTransitionSpec.clientState_bind, clientState_fastRKeyProg,
    StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg]
  split_ifs
  · rw [StateTransitionSpec.clientState_bind, clientState_fastBufLookupProg]
    split_ifs
    · rfl
    · rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg,
        StateTransitionSpec.clientState_bind,
        show (Memory.spec 0).clientState s (Memory.read (pBase + 23)) = s from rfl]
      split_ifs
      · rw [StateTransitionSpec.clientState_bind, clientState_fastBufLookupProg]
        split_ifs <;> rfl
      · rfl
  · rfl

private theorem clientState_fastCheckRKeyFreeProg (x : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (fastCheckRKeyFreeProg x) = s :=
  runClient_state_fastCheckRKeyFreeProg x s

private theorem realizesBounded_fastCheckRKeyFree :
    RealizesBounded .exact fastCheckRKeyFreeProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrk := realizesBounded_fastRKey
  have hrm := realizesBounded_fastReadMeta
  have hbl := realizesBounded_fastBufLookup
  realize
  all_goals (
    rcases d with ⟨pBase, u_val⟩
    obtain ⟨fl, rfl, hfl⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hfl⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_fastRKeyProg,
      runClient_state_fastReadMetaProg, runClient_state_fastBufLookupProg] at *
    first | exact ⟨fl, rfl, hfl⟩ | omega)

private theorem fastCheckRKeyFreeProg_spec {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInv fl slack seeds s.mem s_abs) (u : Fin fl.U) (habs : s_abs u = none) :
    let rk := rKeyOf fl.c fl.U fl.N seeds.fp u
    let fm := extractFastMeta fl s.mem
    let r := (Memory.spec 0).clientResult s (fastCheckRKeyFreeProg (fl.pBase, u.val))
    memoryCost (fastCheckRKeyFreeProg (fl.pBase, u.val)) s ≤ fastCheckRKeyFreeCost fl.c ∧
    (r = 0 ∨ r = 1) ∧
    (r = 0 →
      bufLookup (cTabWhp fl.c) (bCharWhp fl.N)
        (extractBufTrie (fl.trieL fm.curBufRole) s.mem) rk = none ∧
      (fm.subStep < qEpochWhp fl.N / 2 →
        bufLookup (cTabWhp fl.c) (bCharWhp fl.N)
          (extractBufTrie (fl.trieL (1 - fm.curBufRole)) s.mem) rk = none)) ∧
    (r = 1 →
      ∃ u' : Fin fl.U, u' ≠ u ∧ s_abs u' ≠ none ∧ rKeyOf fl.c fl.U fl.N seeds.fp u' = rk) := by
  dsimp only
  have hr := hinv.ready hv rfl
  have hpt := hinv.param_table
  set fm := extractFastMeta fl s.mem
  set rk := rKeyOf fl.c fl.U fl.N seeds.fp u
  have hrk_lt : rk < 2 ^ (cTabWhp fl.c * bCharWhp fl.N) := rKeyOf_lt fl.c fl.U fl.N seeds.fp u
  have hrole_lt : fm.curBufRole < 2 := hinv.role_lt
  have hold_lt : 1 - fm.curBufRole < 2 := by omega
  obtain ⟨hrk_r, hrk_c⟩ := fastRKeyProg_spec hr hinv.seed_fp u
  have hm3_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 3)) = fm.curBufRole :=
    clientResult_fastReadMetaProg hpt (by decide)
  have hm4_r : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 4)) = fm.subStep :=
    clientResult_fastReadMetaProg hpt (by decide)
  have hm23_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 23)) = qEpochWhp fl.N :=
    hpt 23 (by decide)
  have cm3 := memoryCost_fastReadMetaProg (fl.pBase, 3) s
  have cm4 := memoryCost_fastReadMetaProg (fl.pBase, 4) s
  obtain ⟨mapCur, mapOld, _, hv_cur, _, _, _, _, hcur_snd, hold_half, _⟩ := hinv.tiers
  obtain ⟨hlk_cr, hlk_cc⟩ := fastBufLookupProg_spec hr hrole_lt hv_cur hrk_lt
  unfold fastCheckRKeyFreeProg fastCheckRKeyFreeCost
  rw [prog_clientResult_bind, Realization.memoryCost_bind', clientState_fastRKeyProg, hrk_r,
    prog_clientResult_bind, Realization.memoryCost_bind', clientState_fastReadMetaProg, hm3_r,
    ite_eq_left hrole_lt,
    prog_clientResult_bind, Realization.memoryCost_bind', clientState_fastBufLookupProg, hlk_cr]
  have hlive_of : ∀ b' loc' (u' : Fin fl.U), b' < numBucketsWhp fl.N →
      loc' < (extractBlockPool fl.mp s.mem).bktCount b' →
      fastKeyAt fl seeds.bkt s.mem b' loc' = u'.val → s_abs u' ≠ none := by
    intro b' l' u' hb' hl' hk'
    obtain ⟨u₀, _, hu₀, _, _, _, hs₀⟩ := hinv.bktSlot_refines hb' hl'
    have : u₀ = u' := Fin.ext (hu₀.trans hk')
    rw [← this, hs₀]; exact Option.some_ne_none _
  cases hmc : mapCur rk with
  | some p =>
    dsimp only; rw [ite_eq_left Nat.one_ne_zero, prog_clientResult_pure, memoryCost_pure]
    obtain ⟨hb', hl', u', hrk', hk'⟩ := hcur_snd rk p.1 p.2 hmc
    have hlv := hlive_of p.1 p.2 u' hb' hl' hk'
    refine ⟨by linarith only [hrk_c, cm3, hlk_cc], Or.inr rfl, fun h => absurd h Nat.one_ne_zero,
      fun _ => ⟨u', fun he => hlv (by rw [he, habs]), hlv, hrk'⟩⟩
  | none =>
    dsimp only
    rw [ite_eq_right (fun h => h rfl),
      prog_clientResult_bind, Realization.memoryCost_bind', clientState_fastReadMetaProg, hm4_r,
      prog_clientResult_bind, Realization.memoryCost_bind',
      show (Memory.spec 0).clientState s (Memory.read (fl.pBase + 23)) = s from rfl,
      hm23_r, prog_memoryCost_read]
    have hcur_eq : bufLookup (cTabWhp fl.c) (bCharWhp fl.N)
        (extractBufTrie (fl.trieL fm.curBufRole) s.mem) rk = none :=
      (hv_cur.lookup_eq hrk_lt).trans hmc
    by_cases hsub : fm.subStep < qEpochWhp fl.N / 2
    · rw [ite_eq_left hsub] at hold_half ⊢
      obtain ⟨hv_old, _, _, _, _, _, _, hold_snd⟩ := hold_half
      obtain ⟨hlk_or, hlk_oc⟩ := fastBufLookupProg_spec hr hold_lt hv_old hrk_lt
      rw [prog_clientResult_bind, Realization.memoryCost_bind', clientState_fastBufLookupProg,
        hlk_or]
      cases hmo : mapOld rk with
      | some p =>
        dsimp only; rw [ite_eq_left Nat.one_ne_zero, prog_clientResult_pure, memoryCost_pure]
        obtain ⟨_, hb', hl', u', hrk', hk'⟩ := hold_snd rk p.1 p.2 hmo
        have hlv := hlive_of p.1 p.2 u' hb' hl' hk'
        refine ⟨by linarith only [hrk_c, cm3, hlk_cc, cm4, hlk_oc], Or.inr rfl,
          fun h => absurd h Nat.one_ne_zero,
          fun _ => ⟨u', fun he => hlv (by rw [he, habs]), hlv, hrk'⟩⟩
      | none =>
        dsimp only; rw [ite_eq_right (fun h => h rfl), prog_clientResult_pure, memoryCost_pure]
        refine ⟨by linarith only [hrk_c, cm3, hlk_cc, cm4, hlk_oc], Or.inl rfl,
          fun _ => ⟨hcur_eq, fun _ => (hv_old.lookup_eq hrk_lt).trans hmo⟩,
          fun h => absurd h Nat.zero_ne_one⟩
    · rw [ite_eq_right hsub, prog_clientResult_pure, memoryCost_pure]
      exact ⟨by linarith only [hrk_c, cm3, hlk_cc, cm4], Or.inl rfl,
        fun _ => ⟨hcur_eq, fun hl => absurd hl hsub⟩, fun h => absurd h Nat.zero_ne_one⟩

/-- Worst-case `memoryCost` bound for the fast path of `fastInsertProg` (pure function of `c`). -/
@[expose] def fastInsertCost (c : ℕ) : ℕ :=
  fastProbeCost c + fastCheckRKeyFreeCost c + 40 + 2 * dTabWhp c * (cTabWhp c + 2) +
    fastInsertNewStepCost c + advanceSubEpochCost c + 80

/-- Uniform `c`-only worst-case fast-path step cost bound covering **every** large-epoch
operation (`query`, `insert`, `delete`, `popAny`). -/
@[expose] def largeFastStepCost (c : ℕ) : ℕ :=
  max (max (fastProbeCost c) (fastDeleteCost c)) (max (fastInsertCost c) (fastPopAnyCost c)) + 10

/-- Fast-mode (`fallbackMode = 0`) `insert(u, v)` via `pBase` (`¬ReadsWidth`). Exact on **100%**
of hash seeds: transitions in-place to `FallbackPool` on `rKey` collision, bucket overflow
(`bktCount b ≥ capMaxWhp N`), or un-drained `BufOld` rollover, and otherwise updates in
`≤ fastInsertCost c` worst-case memory steps. -/
def fastInsertProg : (ℕ × ℕ) × ℕ → Memory.Prog Unit
  | ((pBase, u_val), v_val) => do
    let pr ← fastProbeProg (pBase, u_val)
    if fastProbeTier pr ≠ 0 then do
      let bq ← fastFeistelSplitProg (pBase, u_val)
      fastBpWriteAtProg ((pBase, (fastProbeBkt pr, fastProbeIdx pr)), (bq.2, v_val))
    else do
      let coll ← fastCheckRKeyFreeProg (pBase, u_val)
      if coll ≠ 0 then do
        fastEnterFallbackProg pBase
        fastFallbackInsertProg ((pBase, u_val), v_val)
      else do
        let b := fastProbeBkt pr
        let cnt ← fastReadBktCntProg (pBase, b)
        let capMax ← Memory.read (pBase + 25)
        if capMax ≤ cnt then do
          fastEnterFallbackProg pBase
          fastFallbackInsertProg ((pBase, u_val), v_val)
        else do
          fastInsertNewStepProg ((pBase, u_val), ((b, cnt), v_val))
          advanceSubEpochProg pBase

private theorem fastInsertNewStepProg_pre {w : ℕ} {x : (ℕ × ℕ) × (ℕ × ℕ) × ℕ} {s : Memory.State}
    (h : FastProgPre w x.1.1 s) :
    FastProgPre w x.1.1 ((Memory.spec 0).clientState s (fastInsertNewStepProg x)) := by
  rcases x with ⟨⟨pBase, u_val⟩, ⟨b, cnt⟩, v_val⟩
  unfold fastInsertNewStepProg; dsimp only
  rw [StateTransitionSpec.clientState_bind]
  have h1 := drainTrySteps5Prog_pre h
  rw [StateTransitionSpec.clientState_bind]
  have h2 := fastShadowSteps8Prog_pre (x := (pBase, b)) h1
  rw [StateTransitionSpec.clientState_bind, clientState_fastFeistelSplitProg,
    StateTransitionSpec.clientState_bind]
  have h3 := fastBpAppendProg_pre
    (x := ((pBase, b), (((Memory.spec 0).clientResult
      ((Memory.spec 0).clientState ((Memory.spec 0).clientState s (drainTrySteps5Prog pBase))
        (fastShadowSteps8Prog (pBase, b)))
      (fastFeistelSplitProg (pBase, u_val))).2, v_val))) h2
  rw [StateTransitionSpec.clientState_bind, clientState_fastRKeyProg,
    StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg]
  exact fastBufInsertProg_pre
    (x := ((pBase, _), (_, (b, cnt)))) h3

theorem realizesBounded_fastInsert :
    RealizesBounded .exact fastInsertProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s =>
        ∃ fl : FastEpochLayout, fl.pBase = pBase ∧ FastLayoutReady w fl s ∧
          FastLayoutReady w fl ((Memory.spec 0).clientState s (fastEnterFallbackProg pBase)))
      (fun _ _ => 0) := by
  have hpr := realizesBounded_fastProbe
  have hfs := realizesBounded_fastFeistelSplit
  have hbw := realizesBounded_fastBpWriteAt
  have hck := realizesBounded_fastCheckRKeyFree
  have hef := realizesBounded_fastEnterFallback
  have hfi := realizesBounded_fastFallbackInsert
  have hbc := realizesBounded_fastReadBktCnt
  have hns := realizesBounded_fastInsertNewStep
  have had := realizesBounded_advanceSubEpoch
  realize
  all_goals (
    rcases d with ⟨⟨pBase, u_val⟩, v_val⟩
    obtain ⟨fl, rfl, hfl, hfl_fb⟩ := h
    obtain ⟨hw6, hp⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hfl⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    have hfr_w := hmem.1
    dsimp only [Fits] at hfr_w ⊢
    try simp only [StateTransitionSpec.clientState, runClient_state_fastProbeProg,
      runClient_state_fastFeistelSplitProg, runClient_state_fastCheckRKeyFreeProg,
      runClient_state_fastReadBktCntProg] at *
    first
    | exact ⟨fl, rfl, hfl⟩
    | exact ⟨fl, rfl, hfl_fb⟩
    | exact fastInsertNewStepProg_pre (x := ((fl.pBase, u_val), (_, v_val))) ⟨fl, rfl, hfl⟩
    | omega)

/-- Unconditional exact specification of `fastInsertProg` on **100%** of hash seeds: updates
`s_abs ↦ Function.update s_abs u (some v)` preserving `LargeEpochInv fl slack' seeds`, and charges
`memoryCost ≤ fastInsertCost fl.c` whenever the post-state remains in fast mode (`mode = 0`). -/
theorem fastInsertProg_spec {fl : FastEpochLayout} {w : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (hv : fl.Valid w s.frontier)
    (hinv : FastEpochInv fl 0 seeds s.mem s_abs) (u : Fin fl.U) (v : Fin fl.V)
    (hcap_new : s_abs u = none →
      (extractBlockPool fl.mp s.mem).nSide < fl.N ∧
      fl.io.AppendCap (extractBlockPool fl.mp s.mem).nSide s.mem) :
    let s' := (Memory.spec 0).clientState s (fastInsertProg ((fl.pBase, u.val), v.val))
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    s'.frontier = s.frontier ∧
    LargeEpochInv fl slack' seeds s'.mem (Function.update s_abs u (some v)) ∧
    (s'.mem (fl.metaBase + 2) = 0 →
      memoryCost (fastInsertProg ((fl.pBase, u.val), v.val)) s ≤ fastInsertCost fl.c ∧
      (extractBlockPool fl.mp s'.mem).nSide =
        (if s_abs u = none then (extractBlockPool fl.mp s.mem).nSide + 1
         else (extractBlockPool fl.mp s.mem).nSide)) ∧
    (s'.mem (fl.metaBase + 2) = 1 →
      (extractFallback fl.mp s'.mem).nSide =
        (if s_abs u = none then (extractBlockPool fl.mp s.mem).nSide + 1
         else (extractBlockPool fl.mp s.mem).nSide)) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (fl.io.usePaged ≠ 0 →
      (extractPagePair fl.io.pgL s'.mem).virtLen fl.io.partner.side =
        (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side ∧
      (extractPagePair fl.io.pgL s'.mem).totalItems =
        (if s_abs u = none then (extractPagePair fl.io.pgL s.mem).totalItems + 1
         else (extractPagePair fl.io.pgL s.mem).totalItems) ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) := by
  dsimp only
  have hr := hinv.ready hv rfl
  set b := epochBucket fl.c fl.U fl.N seeds.bkt u
  have hb : b < numBucketsWhp fl.N := epochBucket_lt fl.c fl.U fl.N seeds.bkt u
  obtain ⟨hpr_st, hpr_c, hpr_b, hpr_res⟩ :=
    fastProbeProg_spec (slack := 0) (seeds := seeds) (s_abs := s_abs) hv hinv u
  set slack' :=
    if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
  have hsl_le : slack' ≤ 24 := by dsimp only [slack']; split_ifs <;> decide
  have hfb_path : s_abs u = none →
      let s1 := (Memory.spec 0).clientState s (fastEnterFallbackProg fl.pBase)
      let s2 := (Memory.spec 0).clientState s1 (fastFallbackInsertProg ((fl.pBase, u.val), v.val))
      s2.frontier = s.frontier ∧
      LargeEpochInv fl slack' seeds s2.mem (Function.update s_abs u (some v)) ∧
      s2.mem (fl.metaBase + 2) = 1 ∧
      (extractFallback fl.mp s2.mem).nSide = (extractBlockPool fl.mp s.mem).nSide + 1 ∧
      (∀ addr, ¬fl.OwnsFastAddr addr → s2.mem addr = s.mem addr) ∧
      (fl.io.usePaged ≠ 0 →
        (extractPagePair fl.io.pgL s2.mem).virtLen fl.io.partner.side =
          (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side ∧
        (extractPagePair fl.io.pgL s2.mem).totalItems =
          (extractPagePair fl.io.pgL s.mem).totalItems + 1 ∧
        ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
          slotIoPairAt fl.io.partner s2.mem idx = slotIoPairAt fl.io.partner s.mem idx) := by
    intro habs
    obtain ⟨hfr_e, hpt_e, hns_e, hfb_e, hof_e, hpg_e⟩ :=
      fastEnterFallbackProg_spec hr hinv.hdr_N hinv.seed_bkt hinv.bp_inv.1.core
        hinv.bp_inv.2.1 hinv.bp_inv.2.2 hinv.refines
    set s1 := (Memory.spec 0).clientState s (fastEnterFallbackProg fl.pBase)
    have hv1 : fl.Valid w s1.frontier := hfr_e.symm ▸ hv
    have hcap1 : s_abs u = none → (extractFallback fl.mp s1.mem).nSide < fl.N ∧
        fl.io.AppendCap (extractFallback fl.mp s1.mem).nSide s1.mem := fun _ => by
      refine ⟨hns_e ▸ (hcap_new habs).1, ?_⟩
      have hcap0 := (hcap_new habs).2
      unfold SlotIoLayout.AppendCap at hcap0 ⊢
      by_cases hup : fl.io.usePaged = 0
      · rw [ite_eq_left hup] at hcap0 ⊢; rwa [hns_e]
      · rw [ite_eq_right hup] at hcap0 ⊢
        have hpe : extractPagePair fl.io.pgL s1.mem = extractPagePair fl.io.pgL s.mem :=
          congrArg PageUnpermState.st (hpg_e hup).1
        rwa [hpe]
    obtain ⟨hfr_f, hpt_f, hns_f, hfb_f, hof_f, hpg_f⟩ :=
      fastFallbackInsertProg_spec hv1 hpt_e hfb_e u v hcap1
    have hsl_e : (if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s1.mem).cleanPhase = 0
        then 0 else 24) = slack' := by
      by_cases hup : fl.io.usePaged = 0
      · simp [slack', hup]
      · simp [slack', hup, (hpg_e hup).1]
    rw [hsl_e] at hfb_f
    rw [ite_eq_left habs] at hns_f
    refine ⟨hfr_f.trans hfr_e, LargeEpochInv.fallback hpt_f hfb_f, hfb_f.mode_eq,
      hns_f.trans (by rw [hns_e]), fun a ha => (hof_f a ha).trans (hof_e a ha), fun hup => ?_⟩
    obtain ⟨hp1, hp2, hp3⟩ := hpg_f hup
    have hpe : extractPagePair fl.io.pgL s1.mem = extractPagePair fl.io.pgL s.mem :=
      congrArg PageUnpermState.st (hpg_e hup).1
    rw [hpe] at hp1 hp2 hp3
    rw [ite_eq_left habs] at hp2
    refine ⟨hp1, hp2, fun idx hidx => (hp3 idx hidx).trans ((hpg_e hup).2 idx hidx)⟩
  unfold fastInsertProg
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hpr_st]
  dsimp only
  cases hsu : s_abs u with
  | some v₀ =>
    rw [hsu] at hpr_res
    have hnz : ((Memory.spec 0).clientResult s (fastProbeProg (fl.pBase, u.val))).1.1 ≠ 0 := by
      rcases hpr_res.1 with h | h | h <;> omega
    set loc := ((Memory.spec 0).clientResult s (fastProbeProg (fl.pBase, u.val))).2.2.1
    obtain ⟨hfs_r, hfs_c⟩ := fastFeistelSplitProg_spec hr hinv.seed_bkt u
    obtain ⟨hfr', hcw, hinv', hbp', _, _, _, hof', hpg'⟩ :=
      fastInsertOverwrite_spec hv hinv u v hb rfl hpr_res.2.1
        (congrArg Prod.fst hpr_res.2.2.2.2)
    rw [ite_eq_left hnz, StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastFeistelSplitProg, hfs_r, hpr_b]
    have hmono : FastEpochInv fl slack' seeds _ (Function.update s_abs u (some v)) :=
      { hinv' with bp_inv := hinv'.bp_inv.mono_slack (Nat.zero_le _) hsl_le }
    refine ⟨hfr', LargeEpochInv.fast hmono, fun _ => ⟨?_, by rw [hbp']; rfl⟩,
      fun h1 => absurd (hinv'.mode_zero.symm.trans h1) Nat.zero_ne_one, hof', fun hup => ?_⟩
    · unfold fastInsertCost fastProbeCost; linarith only [hpr_c, hfs_c, hcw]
    · have hpe : extractPagePair fl.io.pgL _ = extractPagePair fl.io.pgL s.mem :=
        congrArg PageUnpermState.st (hpg' hup).1
      exact ⟨congrArg (fun p => p.virtLen fl.io.partner.side) hpe,
        congrArg PagePairState.totalItems hpe, (hpg' hup).2⟩
  | none =>
    rw [hsu] at hpr_res
    have hnz0 : ¬((Memory.spec 0).clientResult s
        (fastProbeProg (fl.pBase, u.val))).1.1 ≠ 0 := by
      rw [hpr_res.1]; exact fun h => h rfl
    rw [ite_eq_right hnz0, StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastCheckRKeyFreeProg]
    obtain ⟨hck_c, hck_bin, hck_free, _⟩ := fastCheckRKeyFreeProg_spec hv hinv u hsu
    by_cases hcoll : (Memory.spec 0).clientResult s (fastCheckRKeyFreeProg (fl.pBase, u.val)) ≠ 0
    · rw [ite_eq_left hcoll, StateTransitionSpec.clientState_bind]
      obtain ⟨hf, hl, hm, hns, hof, hpg⟩ := hfb_path hsu
      exact ⟨hf, hl, fun h0 => absurd (h0.symm.trans hm) Nat.zero_ne_one,
        fun _ => hns, hof, hpg⟩
    · have hcoll0 : (Memory.spec 0).clientResult s
          (fastCheckRKeyFreeProg (fl.pBase, u.val)) = 0 := by omega
      rw [ite_eq_right hcoll, hpr_b]
      obtain ⟨hcnt_r, hcnt_c⟩ := fastReadBktCntProg_spec hr hinv.bp_inv.1.core hb
      have hm25_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 25)) =
          capMaxWhp fl.N := hinv.param_table 25 (by decide)
      rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
        clientState_fastReadBktCntProg, hcnt_r,
        StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
        show (Memory.spec 0).clientState s (Memory.read (fl.pBase + 25)) = s from rfl,
        hm25_r, prog_memoryCost_read]
      by_cases hovf : capMaxWhp fl.N ≤ (extractBlockPool fl.mp s.mem).bktCount b
      · rw [ite_eq_left hovf, StateTransitionSpec.clientState_bind]
        obtain ⟨hf, hl, hm, hns, hof, hpg⟩ := hfb_path hsu
        exact ⟨hf, hl, fun h0 => absurd (h0.symm.trans hm) Nat.zero_ne_one,
          fun _ => hns, hof, hpg⟩
      · have hcnt_lt : (extractBlockPool fl.mp s.mem).bktCount b < capMaxWhp fl.N := by omega
        obtain ⟨hcur_none, hold_none⟩ := hck_free hcoll0
        obtain ⟨hn_lt, hpg_cap⟩ := hcap_new hsu
        rw [ite_eq_right hovf, StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
        obtain ⟨hfr1, hc1, hinv1, _, _, hns1, hof1, hpg1, _⟩ :=
          fastInsertNewStepProg_spec hv hinv u v rfl hsu hn_lt hcnt_lt hpg_cap hcur_none hold_none
        generalize hs1_def : (Memory.spec 0).clientState s
          (fastInsertNewStepProg ((fl.pBase, u.val),
            ((b, (extractBlockPool fl.mp s.mem).bktCount b), v.val))) = s1
          at hfr1 hinv1 hns1 hof1 hpg1
        have hv1 : fl.Valid w s1.frontier := hfr1.symm ▸ hv
        obtain ⟨hfr2, hof2, hpt2, hpg2, hbr⟩ := advanceSubEpochProg_spec hv1 hinv1
        set s2 := (Memory.spec 0).clientState s1 (advanceSubEpochProg fl.pBase)
        have hpg_tot : fl.io.usePaged ≠ 0 →
            (extractPagePair fl.io.pgL s2.mem).virtLen fl.io.partner.side =
              (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side ∧
            (extractPagePair fl.io.pgL s2.mem).totalItems =
              (extractPagePair fl.io.pgL s.mem).totalItems + 1 ∧
            ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
              slotIoPairAt fl.io.partner s2.mem idx = slotIoPairAt fl.io.partner s.mem idx := by
          intro hup
          obtain ⟨hp1, hp2, hp3⟩ := hpg1 hup
          obtain ⟨hu, hu_p⟩ := hpg2 hup
          have hpe : extractPagePair fl.io.pgL s2.mem = extractPagePair fl.io.pgL s1.mem :=
            congrArg PageUnpermState.st hu
          exact ⟨by rw [hpe, hp1], by rw [hpe, hp2], fun idx hidx =>
            (hu_p idx (hp1.symm ▸ hidx)).trans (hp3 idx hidx)⟩
        by_cases hsub : (extractFastMeta fl s1.mem).subStep < qEpochWhp fl.N / 2
        · rw [ite_eq_left hsub] at hbr
          by_cases hcond : (extractFastMeta fl s1.mem).subStep + 1 < qEpochWhp fl.N / 2 ∨
              ((extractBufTrie (fl.trieL (1 - (extractFastMeta fl s1.mem).curBufRole))
                  ((Memory.spec 0).clientState s1 (drainTicks16Prog fl.pBase)).mem).itemAlloc ≤
                (extractFastMeta fl
                  ((Memory.spec 0).clientState s1 (drainTicks16Prog fl.pBase)).mem).drainPos ∧
                (extractFastMeta fl
                  ((Memory.spec 0).clientState s1 (drainTicks16Prog fl.pBase)).mem).tryAct = 0)
          · rw [ite_eq_left hcond] at hbr
            obtain ⟨hc2, hinv2, hbp2, _, _, _⟩ := hbr
            refine ⟨hfr2.trans hfr1, LargeEpochInv.fast hinv2,
              fun _ => ⟨?_, by rw [hbp2, hns1, ite_eq_left rfl]⟩,
              fun h1 => absurd (hinv2.mode_zero.symm.trans h1) Nat.zero_ne_one,
              fun a ha => (hof2 a ha).trans (hof1 a ha), hpg_tot⟩
            unfold fastInsertCost fastProbeCost
            dsimp only [b] at hc1 hcnt_c ⊢
            exact (Nat.add_le_add hpr_c (Nat.add_le_add hck_c (Nat.add_le_add hcnt_c
              (Nat.add_le_add le_rfl (Nat.add_le_add hc1 hc2))))).trans (by omega)
          · rw [ite_eq_right hcond] at hbr
            obtain ⟨hns2, hfb2⟩ := hbr
            exact ⟨hfr2.trans hfr1, LargeEpochInv.fallback hpt2 hfb2,
              fun h0 => absurd (h0.symm.trans hfb2.mode_eq) Nat.zero_ne_one,
              fun _ => by rw [hns2, hns1, ite_eq_left rfl],
              fun a ha => (hof2 a ha).trans (hof1 a ha), hpg_tot⟩
        · rw [ite_eq_right hsub] at hbr
          obtain ⟨hc2, hinv2, hbp2, _, _, _⟩ := hbr
          refine ⟨hfr2.trans hfr1, LargeEpochInv.fast hinv2,
            fun _ => ⟨?_, by rw [hbp2, hns1, ite_eq_left rfl]⟩,
            fun h1 => absurd (hinv2.mode_zero.symm.trans h1) Nat.zero_ne_one,
            fun a ha => (hof2 a ha).trans (hof1 a ha), hpg_tot⟩
          unfold fastInsertCost fastProbeCost
          dsimp only [b] at hc1 hcnt_c ⊢
          exact (Nat.add_le_add hpr_c (Nat.add_le_add hck_c (Nat.add_le_add hcnt_c
            (Nat.add_le_add le_rfl (Nat.add_le_add hc1 hc2))))).trans (by omega)

/-- Under `GoodEpochSeeds win seeds`, `fastInsertProg` **NEVER** enters fallback
(`mode = 0`, `memoryCost ≤ fastInsertCost fl.c`), preserves `FastSubEpochGood 0 0 slack'`, and
cleanly tracks `CurBufKeysIn` through sub-epoch rollover `e → eNext`. -/
theorem fastInsertProg_good {fl : FastEpochLayout} {w : ℕ}
    {win : EpochWindowSpec fl.c fl.U fl.N} {e : Fin win.numSubs}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {hgood : GoodEpochSeeds win seeds}
    {s_abs : Fin fl.U → Option (Fin fl.V)} {s : Memory.State}
    (hv : fl.Valid w s.frontier)
    (hg : FastSubEpochGood 0 0 0 win e seeds hgood s.mem s_abs)
    (u : Fin fl.U) (v : Fin fl.V)
    (hu_sub : u ∈ win.subUnions e)
    (t : Fin win.numSnaps)
    (hsnap : ∀ k : Fin fl.U, Function.update s_abs u (some v) k ≠ none → k ∈ win.snaps t)
    (hcap_new : s_abs u = none →
      (extractBlockPool fl.mp s.mem).nSide < fl.N ∧
      fl.io.AppendCap (extractBlockPool fl.mp s.mem).nSide s.mem)
    {S : Finset (Fin fl.U)} (hcur_in : CurBufKeysIn seeds s.mem S) :
    let fm := extractFastMeta fl s.mem
    let s' := (Memory.spec 0).clientState s (fastInsertProg ((fl.pBase, u.val), v.val))
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    let s_abs' := Function.update s_abs u (some v)
    s'.mem (fl.metaBase + 2) = 0 ∧
    memoryCost (fastInsertProg ((fl.pBase, u.val), v.val)) s ≤ fastInsertCost fl.c ∧
    (s_abs u ≠ none →
      FastSubEpochGood 0 0 slack' win e seeds hgood s'.mem s_abs' ∧
      (extractFastMeta fl s'.mem).subStep = fm.subStep ∧
      CurBufKeysIn seeds s'.mem S) ∧
    (s_abs u = none → fm.subStep + 1 < qEpochWhp fl.N →
      FastSubEpochGood 0 0 slack' win e seeds hgood s'.mem s_abs' ∧
      (extractFastMeta fl s'.mem).subStep = fm.subStep + 1 ∧
      CurBufKeysIn seeds s'.mem (insert u S)) ∧
    (s_abs u = none → fm.subStep + 1 = qEpochWhp fl.N →
      (extractFastMeta fl s'.mem).subStep = 0 ∧
      CurBufKeysIn seeds s'.mem ∅ ∧
      ∀ eNext : Fin win.numSubs,
        (∀ k : Fin fl.U, s_abs' k ≠ none → k ∈ win.subUnions eNext) →
        insert u S ⊆ win.subBatches eNext →
        FastSubEpochGood 0 0 slack' win eNext seeds hgood s'.mem s_abs') := by
  dsimp only
  have hinv := hg.inv.toInv
  have hr := hinv.ready hv rfl
  set b := epochBucket fl.c fl.U fl.N seeds.bkt u
  have hb : b < numBucketsWhp fl.N := epochBucket_lt fl.c fl.U fl.N seeds.bkt u
  set slack' :=
    if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
  have hsl_le : slack' ≤ 24 := by dsimp only [slack']; split_ifs <;> decide
  obtain ⟨hpr_st, hpr_c, hpr_b, hpr_res⟩ :=
    fastProbeProg_spec (slack := 0) (seeds := seeds) (s_abs := s_abs) hv hinv u
  unfold fastInsertProg
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind', hpr_st]
  dsimp only
  cases hsu : s_abs u with
  | some v₀ =>
    rw [hsu] at hpr_res
    have hnz : ((Memory.spec 0).clientResult s (fastProbeProg (fl.pBase, u.val))).1.1 ≠ 0 := by
      rcases hpr_res.1 with h | h | h <;> omega
    obtain ⟨hfs_r, hfs_c⟩ := fastFeistelSplitProg_spec hr hinv.seed_bkt u
    obtain ⟨_, hcw, hinv', hbp', hfm', htr', hke', _, _⟩ :=
      fastInsertOverwrite_spec hv hinv u v hb rfl hpr_res.2.1
        (congrArg Prod.fst hpr_res.2.2.2.2)
    rw [ite_eq_left hnz, StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastFeistelSplitProg, hfs_r, hpr_b]
    set s' := (Memory.spec 0).clientState s
      (fastBpWriteAtProg ((fl.pBase, (b, _)), (keyQuotient (bWhp fl.N) u.val, v.val)))
    have hrole_lt : (extractFastMeta fl s.mem).curBufRole < 2 := hinv.role_lt
    have hold_lt : 1 - (extractFastMeta fl s.mem).curBufRole < 2 := by omega
    have hmono : FastEpochInvGen 0 fl slack' seeds s'.mem (Function.update s_abs u (some v)) :=
      { hinv'.toGen 0 with
        bp_inv := hinv'.bp_inv.mono_slack (Nat.zero_le _) hsl_le }
    have hgood_ow : FastSubEpochGood 0 0 slack' win e seeds hgood s'.mem
        (Function.update s_abs u (some v)) :=
      { inv := hmono
        live_sub := fun k hk => by
          by_cases hku : k = u
          · exact hku ▸ hu_sub
          · rw [Function.update_of_ne hku] at hk; exact hg.live_sub k hk
        old_sub := fun hsub id b' l' u' hchk hb' hl' hk' => by
          rw [hfm', htr' _ hold_lt] at hchk
          rw [hbp'] at hl'
          exact hg.old_sub (by rwa [hfm'] at hsub) id b' l' u' hchk hb' hl'
            ((hke' b' hb' l' hl').symm.trans hk')
        try_match := fun hta hdp b' l' hchk => by
          rw [hfm', htr' _ hold_lt] at hchk hdp
          rw [hfm'] at hta ⊢
          exact hg.try_match hta hdp b' l' hchk
        trySalt_le := fun hta => by rw [hfm'] at hta ⊢; exact hg.trySalt_le hta
        pot_le := fun hsub => by
          have hbad_iff : ∀ id, isBadOldSlot win e seeds s'.mem id ↔
              isBadOldSlot win e seeds s.mem id := fun id => by
            constructor
            · rintro ⟨b', l', u', hchk, hb', hl', hk', hcol⟩
              rw [hfm', htr' _ hold_lt] at hchk; rw [hbp'] at hl'
              exact ⟨b', l', u', hchk, hb', hl', (hke' b' hb' l' hl').symm.trans hk', hcol⟩
            · rintro ⟨b', l', u', hchk, hb', hl', hk', hcol⟩
              exact ⟨b', l', u', by rwa [hfm', htr' _ hold_lt], hb', by rwa [hbp'],
                (hke' b' hb' l' hl').trans hk', hcol⟩
          have hpeq : drainPotential win e seeds hgood s'.mem =
              drainPotential win e seeds hgood s.mem := by
            classical
            unfold drainPotential shTerm shCost shSlack nBadFrom; dsimp only
            simp only [hfm', hbp', htr' _ hold_lt, hbad_iff]
          rw [hpeq, hfm']; exact hg.pot_le (by rwa [hfm'] at hsub) }
    have hcur_ow : CurBufKeysIn seeds s'.mem S := fun id b' l' u' hchk hb' hl' hk' => by
      rw [hfm', htr' _ hrole_lt] at hchk; rw [hbp'] at hl'
      exact hcur_in id b' l' u' hchk hb' hl' ((hke' b' hb' l' hl').symm.trans hk')
    refine ⟨hinv'.mode_zero, ?_,
      fun _ => ⟨hgood_ow, congrArg FastEpochMeta.subStep hfm', hcur_ow⟩,
      fun h0 => absurd h0 (by simp), fun h0 => absurd h0 (by simp)⟩
    unfold fastInsertCost fastProbeCost; linarith only [hpr_c, hfs_c, hcw]
  | none =>
    rw [hsu] at hpr_res
    have hnz0 : ¬((Memory.spec 0).clientResult s
        (fastProbeProg (fl.pBase, u.val))).1.1 ≠ 0 := by rw [hpr_res.1]; exact fun h => h rfl
    obtain ⟨hck_c, hck_bin, hck_free, hck_coll⟩ := fastCheckRKeyFreeProg_spec hv hinv u hsu
    have hcoll0 : (Memory.spec 0).clientResult s (fastCheckRKeyFreeProg (fl.pBase, u.val)) = 0 := by
      rcases hck_bin with h0 | h1
      · exact h0
      · obtain ⟨u', hne_u, hlive_u', hrk_eq⟩ := hck_coll h1
        exact absurd (hgood.2.1 (win.subUnion_sub e (hg.live_sub u' hlive_u'))
          (win.subUnion_sub e hu_sub) hrk_eq) hne_u
    have hcnt_lt : (extractBlockPool fl.mp s.mem).bktCount b < capMaxWhp fl.N :=
      bktCount_lt_capMax_of_good hgood hg.inv hb v hsu rfl t hsnap
    rw [ite_eq_right hnz0, StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastCheckRKeyFreeProg, ite_eq_right (by rw [hcoll0]; exact fun h => h rfl),
      hpr_b]
    obtain ⟨hcnt_r, hcnt_c⟩ := fastReadBktCntProg_spec hr hinv.bp_inv.1.core hb
    have hm25_r : (Memory.spec 0).clientResult s (Memory.read (fl.pBase + 25)) =
        capMaxWhp fl.N := hinv.param_table 25 (by decide)
    rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      clientState_fastReadBktCntProg, hcnt_r,
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
      show (Memory.spec 0).clientState s (Memory.read (fl.pBase + 25)) = s from rfl,
      hm25_r, prog_memoryCost_read, ite_eq_right (Nat.not_le.mpr hcnt_lt),
      StateTransitionSpec.clientState_bind, Realization.memoryCost_bind']
    obtain ⟨hcur_none, hold_none⟩ := hck_free hcoll0
    obtain ⟨hn_lt, hpg_cap⟩ := hcap_new hsu
    obtain ⟨hfr1, hc1, hinv1, hcr1, hss1, _, _, _, hcur_ins⟩ :=
      fastInsertNewStepProg_spec hv hinv u v rfl hsu hn_lt hcnt_lt hpg_cap hcur_none hold_none
    have hg1 := fastInsertNewStepProg_good hv hg u v hu_sub rfl hsu hn_lt hcnt_lt hpg_cap
      hcur_none hold_none
    dsimp only at hg1
    change FastSubEpochGood 1 5 _ win e seeds hgood
      ((Memory.spec 0).clientState s
        (fastInsertNewStepProg ((fl.pBase, u.val),
          ((b, (extractBlockPool fl.mp s.mem).bktCount b), v.val)))).mem _ at hg1
    generalize hs1_def : (Memory.spec 0).clientState s
      (fastInsertNewStepProg ((fl.pBase, u.val),
        ((b, (extractBlockPool fl.mp s.mem).bktCount b), v.val))) = s1
      at hfr1 hinv1 hcr1 hss1 hcur_ins hg1
    have hv1 : fl.Valid w s1.frontier := hfr1.symm ▸ hv
    obtain ⟨_, hca, hinv_a, hbp_a, hoi_a, _, hsame, hroll⟩ := advanceSubEpochProg_good hv1 hg1
    obtain ⟨_, _, _, _, hbr⟩ := advanceSubEpochProg_spec hv1 hg1.inv
    have hcost_le : memoryCost (fastProbeProg (fl.pBase, u.val)) s +
        (memoryCost (fastCheckRKeyFreeProg (fl.pBase, u.val)) s +
          (memoryCost (fastReadBktCntProg (fl.pBase, b)) s + (1 +
            (memoryCost (fastInsertNewStepProg ((fl.pBase, u.val),
              ((b, (extractBlockPool fl.mp s.mem).bktCount b), v.val))) s +
             memoryCost (advanceSubEpochProg fl.pBase) s1)))) ≤ fastInsertCost fl.c := by
      unfold fastInsertCost fastProbeCost
      dsimp only [b] at hc1 hcnt_c ⊢
      exact (Nat.add_le_add hpr_c (Nat.add_le_add hck_c (Nat.add_le_add hcnt_c
        (Nat.add_le_add le_rfl (Nat.add_le_add hc1 hca))))).trans (by omega)
    refine ⟨hinv_a.mode_zero, hcost_le, fun h => absurd rfl h, ?_, ?_⟩
    · intro _ hlt
      obtain ⟨hga, hssa, hcra⟩ := hsame (by rwa [hss1])
      refine ⟨hga, hssa.trans (by rw [hss1]), ?_⟩
      have hcur_s1 : CurBufKeysIn seeds s1.mem (insert u S) := hcur_ins S hcur_in
      intro id b' l' u' hchk hb' hl' hk'
      have hl1 : l' < (extractBlockPool fl.mp s1.mem).bktCount b' := by rwa [← hbp_a]
      have hke : fastKeyAt fl seeds.bkt
          ((Memory.spec 0).clientState s1 (advanceSubEpochProg fl.pBase)).mem b' l' =
          fastKeyAt fl seeds.bkt s1.mem b' l' :=
        fastKeyAt_eq_of_fixed_pool hv1 hinv1.bp_inv hbp_a hoi_a hb' hl1
      have htr_cur_eq : extractBufTrie (fl.trieL (extractFastMeta fl s1.mem).curBufRole)
          ((Memory.spec 0).clientState s1 (advanceSubEpochProg fl.pBase)).mem =
          extractBufTrie (fl.trieL (extractFastMeta fl s1.mem).curBufRole) s1.mem := by
        by_cases hs1 : (extractFastMeta fl s1.mem).subStep < qEpochWhp fl.N / 2
        · rw [ite_eq_left hs1] at hbr
          have hcond : (extractFastMeta fl s1.mem).subStep + 1 < qEpochWhp fl.N / 2 ∨
              ((extractBufTrie (fl.trieL (1 - (extractFastMeta fl s1.mem).curBufRole))
                  ((Memory.spec 0).clientState s1 (drainTicks16Prog fl.pBase)).mem).itemAlloc ≤
                (extractFastMeta fl
                  ((Memory.spec 0).clientState s1 (drainTicks16Prog fl.pBase)).mem).drainPos ∧
                (extractFastMeta fl ((Memory.spec 0).clientState s1
                  (drainTicks16Prog fl.pBase)).mem).tryAct = 0) := by
            by_contra hn; rw [ite_eq_right hn] at hbr
            have hm1 := hbr.2.mode_eq
            exact absurd (hinv_a.mode_zero.symm.trans hm1) Nat.zero_ne_one
          rw [ite_eq_left hcond] at hbr
          have ht1 := hbr.2.2.2.2.1 (extractFastMeta fl s1.mem).curBufRole hinv1.role_lt
          have ht0 := (drainTicks16Prog_spec hv1 hinv1 hs1).2.2.2.2.1
          exact ht1.trans ht0
        · exact advanceSubEpochProg_curTrie_half2 hv1 hinv1 hs1 (by rwa [hss1])
      rw [hcra, htr_cur_eq] at hchk
      exact hcur_s1 id b' l' u' hchk hb' hl1 (hke.symm.trans hk')
    · intro _ heq
      obtain ⟨hcra, hssa, _, _, hgen⟩ := hroll (by rwa [hss1])
      have hsub_ge : ¬(extractFastMeta fl s1.mem).subStep < qEpochWhp fl.N / 2 := by
        have hL : 2 ≤ slabScale fl.N :=
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ Dynamic.logLogFactor fl.N :=
                Nat.pow_le_pow_right (by decide) (Dynamic.one_le_logLogFactor fl.N)
        have hQ4 : 4 ≤ qEpochWhp fl.N :=
          calc 4 = 2 ^ 2 := by decide
            _ ≤ 2 ^ 18 := Nat.pow_le_pow_right (by decide) (by decide)
            _ ≤ slabScale fl.N ^ 18 := Nat.pow_le_pow_left hL 18
        rw [hss1]; omega
      rw [ite_eq_right hsub_ge] at hbr
      have hia0 : (extractBufTrie (fl.trieL (extractFastMeta fl
          ((Memory.spec 0).clientState s1 (advanceSubEpochProg fl.pBase)).mem).curBufRole)
          ((Memory.spec 0).clientState s1 (advanceSubEpochProg fl.pBase)).mem).itemAlloc = 0 :=
        (hbr.2.2.2.2.2 (by rwa [hss1])).2.2.2.2.2.1
      refine ⟨hssa, fun id b' l' u' hchk => ?_, fun eNext hlive_n hsub_n =>
        hgen eNext hlive_n fun id b' l' u' hchk hb' hl' hk' =>
          hsub_n (hcur_ins S hcur_in id b' l' u' hchk hb' hl' hk')⟩
      exfalso
      unfold bufCheckSlot at hchk; rw [hia0] at hchk; simp at hchk

/-! ## Section 6: Empty Initialization under `GoodEpochSeeds` and Mode Dispatch -/

/-- `fastInitZeroedProg` establishes `FastSubEpochGood 0 0 slack` and `CurBufKeysIn seeds ... ∅`
for every `GoodEpochSeeds win seeds` and sub-epoch `e : Fin win.numSubs`. -/
theorem fastInitZeroedProg_good {fl : FastEpochLayout} {w slack : ℕ}
    {win : EpochWindowSpec fl.c fl.U fl.N} (e : Fin win.numSubs)
    {seeds : EpochHashSeeds fl.c fl.U fl.N} (hgood : GoodEpochSeeds win seeds)
    {s : Memory.State}
    (hv : fl.Valid w s.frontier) (hpt : fl.ParamTable s.mem)
    (hN : s.mem fl.metaBase = fl.N)
    (hbkt_rep : BitPackedDoubleTabulation.SeedRep fl.bktHashBase fl.w
      (redWidthWhp fl.U) (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (bWhp fl.N) seeds.bkt s.mem)
    (hfp_rep : BitPackedDoubleTabulation.SeedRep fl.fpHashBase fl.w
      (redWidthWhp fl.U) (cTabWhp fl.c) (dTabWhp fl.c) (bCharWhp fl.N) (fpBitsWhp fl.N)
      seeds.fp s.mem)
    (hzero_hdr : ∀ k, 1 ≤ k → k < 32 → s.mem (fl.metaBase + k) = 0)
    (hzero_tab : ∀ addr, fl.metaBase + offBktMeta fl.c fl.w fl.N ≤ addr →
      addr < fl.metaBase + offPageDir fl.c fl.w fl.N → s.mem addr = 0)
    (hio : fl.io.StateInv 0 slack s.mem) :
    let s' := (Memory.spec 0).clientState s (fastInitZeroedProg fl.pBase)
    FastSubEpochGood 0 0 slack win e seeds hgood s'.mem (fun _ => none) ∧
    CurBufKeysIn seeds s'.mem ∅ := by
  dsimp only
  have hr₀ : FastLayoutReady w fl s :=
    ⟨hv, hpt, hbkt_rep.1 ▸ seeds.bkt.1.isLt, hfp_rep.1 ▸ seeds.fp.1.isLt⟩
  obtain ⟨_, _, hinv', _, _⟩ :=
    fastInitZeroedProg_spec hv hpt hN hbkt_rep hfp_rep hzero_hdr hzero_tab hio
  have hhdr := fastInitZeroedProg_hdr_zero hr₀ hzero_hdr
  set s' := (Memory.spec 0).clientState s (fastInitZeroedProg fl.pBase)
  have hss0 : (extractFastMeta fl s'.mem).subStep = 0 := hhdr 4 (by decide) (by decide)
  have hdp0 : (extractFastMeta fl s'.mem).drainPos = 0 := hhdr 5 (by decide) (by decide)
  have hta0 : (extractFastMeta fl s'.mem).tryAct = 0 := hhdr 6 (by decide) (by decide)
  have hcur_empty : ∀ r id, r < 2 →
      ¬isBadOldSlot win e seeds s'.mem id := by
    intro _ id _ ⟨b, loc, _, _, hb, hl, _⟩
    obtain ⟨_, _, _, _, _, _, hs⟩ := hinv'.bktSlot_refines hb hl; cases hs
  have hpot_zero : drainPotential win e seeds hgood s'.mem ≤ 2 * qEpochWhp fl.N := by
    have hq_pos : 0 < qEpochWhp fl.N / 2 := by
      have hL : 2 ≤ slabScale fl.N :=
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ Dynamic.logLogFactor fl.N :=
              Nat.pow_le_pow_right (by decide) (Dynamic.one_le_logLogFactor fl.N)
      have hQ4 : 4 ≤ qEpochWhp fl.N :=
        calc 4 = 2 ^ 2 := by decide
          _ ≤ 2 ^ 18 := Nat.pow_le_pow_right (by decide) (by decide)
          _ ≤ slabScale fl.N ^ 18 := Nat.pow_le_pow_left hL 18
      omega
    obtain ⟨_, _, _, _, _, _, _, _, _, hoh, _⟩ := hinv'.tiers
    rw [ite_eq_left (by rw [hss0]; exact hq_pos)] at hoh
    have hia_le : (extractBufTrie (fl.trieL
        (1 - (extractFastMeta fl s'.mem).curBufRole)) s'.mem).itemAlloc ≤ qEpochWhp fl.N :=
      hoh.2.2.2.1
    have hnb_zero : ∀ k, nBadFrom win e seeds s'.mem k = 0 := fun k => by
      classical
      unfold nBadFrom
      exact Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun id _ h =>
        hcur_empty 0 id (by decide) h.2)
    have hsh_zero : shTerm fl win e seeds s'.mem = 0 := by
      classical
      unfold shTerm; dsimp only
      exact ite_eq_right (hcur_empty 0 _ (by decide))
    unfold drainPotential; dsimp only
    rw [ite_eq_right (by rw [hta0]; exact Nat.zero_ne_one), hnb_zero, hnb_zero, hsh_zero]
    omega
  refine ⟨
    { inv := hinv'.toGen 0
      live_sub := fun _ h => absurd rfl h
      old_sub := fun _ _ _ _ _ _ hb hl _ => by
        obtain ⟨_, _, _, _, _, _, hs⟩ := hinv'.bktSlot_refines hb hl; cases hs
      try_match := fun hta => absurd (hta0.symm.trans hta) Nat.zero_ne_one
      trySalt_le := fun hta => absurd (hta0.symm.trans hta) Nat.zero_ne_one
      pot_le := fun _ => by rw [hss0]; exact hpot_zero },
    fun _ _ _ _ _ hb hl _ => by
      obtain ⟨_, _, _, _, _, _, hs⟩ := hinv'.bktSlot_refines hb hl; cases hs⟩

/-- Mode-dispatching large-epoch `query(u)` via `pBase` (`¬ReadsWidth`). -/
def largeEpochQueryProg : ℕ × ℕ → Memory.Prog (ℕ × ℕ)
  | (pBase, u_val) => do
    let mode ← fastReadMetaProg (pBase, 2)
    if mode = 0 then
      fastQueryProg (pBase, u_val)
    else
      fastFallbackQueryProg (pBase, u_val)

theorem realizesBounded_largeEpochQuery :
    RealizesBounded .exact largeEpochQueryProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrm := realizesBounded_fastReadMeta
  have hfq := realizesBounded_fastQuery
  have hbq := realizesBounded_fastFallbackQuery
  realize
  all_goals (
    rcases d with ⟨pBase, u_val⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    first
    | exact ⟨fl, rfl, hr⟩
    | (simp only [StateTransitionSpec.clientState, runClient_state_fastReadMetaProg]
       exact ⟨fl, rfl, hr⟩)
    | (dsimp only [Fits]; omega))

/-- Exact specification of `largeEpochQueryProg` on **100%** of hash seeds. -/
theorem largeEpochQueryProg_spec {fl : FastEpochLayout} {w slack : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (hv : fl.Valid w s.frontier)
    (hinv : LargeEpochInv fl slack seeds s.mem s_abs) (u : Fin fl.U) :
    (Memory.spec 0).clientState s (largeEpochQueryProg (fl.pBase, u.val)) = s ∧
    (Memory.spec 0).clientResult s (largeEpochQueryProg (fl.pBase, u.val)) =
      (match s_abs u with | none => (0, 0) | some v => (1, v.val)) ∧
    (s.mem (fl.metaBase + 2) = 0 →
      memoryCost (largeEpochQueryProg (fl.pBase, u.val)) s ≤ largeFastStepCost fl.c) := by
  have hm2 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 2)) =
      s.mem (fl.metaBase + 2) := clientResult_fastReadMetaProg hinv.1 (by decide)
  have hcm2 := memoryCost_fastReadMetaProg (fl.pBase, 2) s
  unfold largeEpochQueryProg
  rcases hinv.2 with ⟨hm0, hf⟩ | ⟨hm1, hfb⟩
  · obtain ⟨hst, hc, hres⟩ := fastQueryProg_spec hv hf u
    refine ⟨?_, ?_, fun _ => ?_⟩
    · rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm2, hm0,
        ite_eq_left rfl]; exact hst
    · rw [prog_clientResult_bind, clientState_fastReadMetaProg, hm2, hm0, ite_eq_left rfl]
      exact hres
    · rw [Realization.memoryCost_bind', clientState_fastReadMetaProg, hm2, hm0, ite_eq_left rfl]
      unfold largeFastStepCost fastProbeCost
      have hle : fastProbeCost fl.c ≤
          max (max (fastProbeCost fl.c) (fastDeleteCost fl.c))
            (max (fastInsertCost fl.c) (fastPopAnyCost fl.c)) :=
        le_trans (le_max_left _ _) (le_max_left _ _)
      unfold fastProbeCost at hle
      omega
  · obtain ⟨hst, hres⟩ := fastFallbackQueryProg_spec hv hinv.1 hfb u
    have hnz : s.mem (fl.metaBase + 2) ≠ 0 := by rw [hm1]; exact Nat.one_ne_zero
    refine ⟨?_, ?_, fun h0 => absurd h0 hnz⟩
    · rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm2,
        ite_eq_right hnz]; exact hst
    · rw [prog_clientResult_bind, clientState_fastReadMetaProg, hm2, ite_eq_right hnz]
      exact hres

/-- Mode-dispatching large-epoch `insert(u, v)` via `pBase` (`¬ReadsWidth`). -/
def largeEpochInsertProg : (ℕ × ℕ) × ℕ → Memory.Prog Unit
  | ((pBase, u_val), v_val) => do
    let mode ← fastReadMetaProg (pBase, 2)
    if mode = 0 then
      fastInsertProg ((pBase, u_val), v_val)
    else
      fastFallbackInsertProg ((pBase, u_val), v_val)

theorem realizesBounded_largeEpochInsert :
    RealizesBounded .exact largeEpochInsertProg
      (WordEncoding.encode (α := (ℕ × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((pBase, _), _) s => FastInsertProgPre w pBase s) (fun _ _ => 0) := by
  have hrm := realizesBounded_fastReadMeta
  have hfi := realizesBounded_fastInsert
  have hbi := realizesBounded_fastFallbackInsert
  realize
  all_goals (
    rcases d with ⟨⟨pBase, u_val⟩, v_val⟩
    obtain ⟨fl, rfl, hr, hfb⟩ := h
    obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    first
    | exact ⟨fl, rfl, hr⟩
    | (simp only [StateTransitionSpec.clientState, runClient_state_fastReadMetaProg]
       exact ⟨fl, rfl, hr⟩)
    | (simp only [StateTransitionSpec.clientState, runClient_state_fastReadMetaProg]
       have hm2 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 2)) =
          s.mem (fl.metaBase + 2) := clientResult_fastReadMetaProg hr.2.1 (by decide)
       exact ⟨fl, rfl, hr, hfb (by rwa [← hm2])⟩)
    | (dsimp only [Fits]; omega))

/-- Exact specification of `largeEpochInsertProg` on **100%** of hash seeds. -/
theorem largeEpochInsertProg_spec {fl : FastEpochLayout} {w : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (hv : fl.Valid w s.frontier)
    (hinv : LargeEpochInv fl 0 seeds s.mem s_abs) (u : Fin fl.U) (v : Fin fl.V)
    (hcap_new : s_abs u = none →
      (s.mem (fl.metaBase + 2) = 0 →
        (extractBlockPool fl.mp s.mem).nSide < fl.N ∧
        fl.io.AppendCap (extractBlockPool fl.mp s.mem).nSide s.mem) ∧
      (s.mem (fl.metaBase + 2) = 1 →
        (extractFallback fl.mp s.mem).nSide < fl.N ∧
        fl.io.AppendCap (extractFallback fl.mp s.mem).nSide s.mem)) :
    let s' := (Memory.spec 0).clientState s (largeEpochInsertProg ((fl.pBase, u.val), v.val))
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    s'.frontier = s.frontier ∧
    LargeEpochInv fl slack' seeds s'.mem (Function.update s_abs u (some v)) ∧
    (s'.mem (fl.metaBase + 2) = 0 →
      memoryCost (largeEpochInsertProg ((fl.pBase, u.val), v.val)) s ≤ largeFastStepCost fl.c) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (fl.io.usePaged ≠ 0 →
      (extractPagePair fl.io.pgL s'.mem).virtLen fl.io.partner.side =
        (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side ∧
      (extractPagePair fl.io.pgL s'.mem).totalItems =
        (if s_abs u = none then (extractPagePair fl.io.pgL s.mem).totalItems + 1
         else (extractPagePair fl.io.pgL s.mem).totalItems) ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) := by
  have hm2 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 2)) =
      s.mem (fl.metaBase + 2) := clientResult_fastReadMetaProg hinv.1 (by decide)
  have hcm2 := memoryCost_fastReadMetaProg (fl.pBase, 2) s
  unfold largeEpochInsertProg
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadMetaProg, hm2]
  rcases hinv.2 with ⟨hm0, hf⟩ | ⟨hm1, hfb⟩
  · rw [hm0, ite_eq_left rfl]
    obtain ⟨hfr, hl, hfast, _, hof, hpg⟩ :=
      fastInsertProg_spec hv hf u v fun h => (hcap_new h).1 hm0
    refine ⟨hfr, hl, fun hm0' => ?_, hof, hpg⟩
    have hc := (hfast hm0').1
    have hle : fastInsertCost fl.c ≤
        max (max (fastProbeCost fl.c) (fastDeleteCost fl.c))
          (max (fastInsertCost fl.c) (fastPopAnyCost fl.c)) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    unfold largeFastStepCost; omega
  · have hnz : s.mem (fl.metaBase + 2) ≠ 0 := by rw [hm1]; exact Nat.one_ne_zero
    rw [ite_eq_right hnz]
    obtain ⟨hfr, hpt', _, hfb', hof, hpg⟩ :=
      fastFallbackInsertProg_spec hv hinv.1 hfb u v fun h => (hcap_new h).2 hm1
    exact ⟨hfr, LargeEpochInv.fallback hpt' hfb',
      fun h0 => absurd (h0.symm.trans hfb'.mode_eq) Nat.zero_ne_one, hof, hpg⟩

/-- Mode-dispatching large-epoch `delete(u)` via `pBase` (`¬ReadsWidth`). -/
def largeEpochDeleteProg : ℕ × ℕ → Memory.Prog Unit
  | (pBase, u_val) => do
    let mode ← fastReadMetaProg (pBase, 2)
    if mode = 0 then
      fastDeleteProg (pBase, u_val)
    else
      fastFallbackDeleteProg (pBase, u_val)

theorem realizesBounded_largeEpochDelete :
    RealizesBounded .exact largeEpochDeleteProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (pBase, _) s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrm := realizesBounded_fastReadMeta
  have hfd := realizesBounded_fastDelete
  have hbd := realizesBounded_fastFallbackDelete
  realize
  all_goals (
    rcases d with ⟨pBase, u_val⟩
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    first
    | exact ⟨fl, rfl, hr⟩
    | (simp only [StateTransitionSpec.clientState, runClient_state_fastReadMetaProg]
       exact ⟨fl, rfl, hr⟩)
    | (dsimp only [Fits]; omega))

/-- Exact specification of `largeEpochDeleteProg` on **100%** of hash seeds. -/
theorem largeEpochDeleteProg_spec {fl : FastEpochLayout} {w : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (hv : fl.Valid w s.frontier)
    (hinv : LargeEpochInv fl 0 seeds s.mem s_abs) (u : Fin fl.U) :
    let s' := (Memory.spec 0).clientState s (largeEpochDeleteProg (fl.pBase, u.val))
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    s'.frontier = s.frontier ∧
    LargeEpochInv fl slack' seeds s'.mem (Function.update s_abs u none) ∧
    (s.mem (fl.metaBase + 2) = 0 →
      s'.mem (fl.metaBase + 2) = 0 ∧
      memoryCost (largeEpochDeleteProg (fl.pBase, u.val)) s ≤ largeFastStepCost fl.c) ∧
    (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
    (fl.io.usePaged ≠ 0 →
      (extractPagePair fl.io.pgL s'.mem).virtLen fl.io.partner.side =
        (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side ∧
      (extractPagePair fl.io.pgL s'.mem).totalItems =
        (if s_abs u = none then (extractPagePair fl.io.pgL s.mem).totalItems
         else (extractPagePair fl.io.pgL s.mem).totalItems - 1) ∧
      ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
        slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) := by
  have hm2 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 2)) =
      s.mem (fl.metaBase + 2) := clientResult_fastReadMetaProg hinv.1 (by decide)
  have hcm2 := memoryCost_fastReadMetaProg (fl.pBase, 2) s
  unfold largeEpochDeleteProg
  rw [StateTransitionSpec.clientState_bind, Realization.memoryCost_bind',
    clientState_fastReadMetaProg, hm2]
  rcases hinv.2 with ⟨hm0, hf⟩ | ⟨hm1, hfb⟩
  · rw [hm0, ite_eq_left rfl]
    obtain ⟨hfr, hc, hinv', _, _, _, hof, hpg, _⟩ := fastDeleteProg_spec hv hf u
    refine ⟨hfr, LargeEpochInv.fast hinv', fun _ => ⟨hinv'.mode_zero, ?_⟩, hof, hpg⟩
    have hle : fastDeleteCost fl.c ≤
        max (max (fastProbeCost fl.c) (fastDeleteCost fl.c))
          (max (fastInsertCost fl.c) (fastPopAnyCost fl.c)) :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    unfold largeFastStepCost; omega
  · have hnz : s.mem (fl.metaBase + 2) ≠ 0 := by rw [hm1]; exact Nat.one_ne_zero
    rw [ite_eq_right hnz]
    obtain ⟨hfr, hpt', _, hfb', hof, hpg⟩ := fastFallbackDeleteProg_spec hv hinv.1 hfb u
    exact ⟨hfr, LargeEpochInv.fallback hpt' hfb', fun h0 => absurd h0 hnz, hof, hpg⟩

/-- Mode-dispatching large-epoch `popAny` via `pBase` (`¬ReadsWidth`). -/
def largeEpochPopAnyProg (pBase : ℕ) : Memory.Prog (ℕ × ℕ) := do
  let mode ← fastReadMetaProg (pBase, 2)
  if mode = 0 then
    fastPopAnyProg pBase
  else
    fastFallbackPopAnyProg pBase

theorem realizesBounded_largeEpochPopAny :
    RealizesBounded .exact largeEpochPopAnyProg
      (WordEncoding.encode (α := ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w pBase s => FastProgPre w pBase s) (fun _ _ => 0) := by
  have hrm := realizesBounded_fastReadMeta
  have hfp := realizesBounded_fastPopAny
  have hbp := realizesBounded_fastFallbackPopAny
  realize
  all_goals (
    obtain ⟨fl, rfl, hr⟩ := h
    obtain ⟨hw6, _⟩ := FastProgPre.pBase_bound ⟨fl, rfl, hr⟩
    have hpow6 : 64 ≤ 2 ^ w := (by decide : 64 = 2 ^ 6) ▸ Nat.pow_le_pow_right (by decide) hw6
    first
    | exact ⟨fl, rfl, hr⟩
    | (simp only [StateTransitionSpec.clientState, runClient_state_fastReadMetaProg]
       exact ⟨fl, rfl, hr⟩)
    | (dsimp only [Fits]; omega))

/-- Exact specification of `largeEpochPopAnyProg` on **100%** of hash seeds (`0 < nSide`). -/
theorem largeEpochPopAnyProg_spec {fl : FastEpochLayout} {w : ℕ}
    {seeds : EpochHashSeeds fl.c fl.U fl.N} {s_abs : Fin fl.U → Option (Fin fl.V)}
    {s : Memory.State} (hv : fl.Valid w s.frontier)
    (hinv : LargeEpochInv fl 0 seeds s.mem s_abs)
    (hpos : (s.mem (fl.metaBase + 2) = 0 → 0 < (extractBlockPool fl.mp s.mem).nSide) ∧
      (s.mem (fl.metaBase + 2) = 1 → 0 < (extractFallback fl.mp s.mem).nSide)) :
    let res := (Memory.spec 0).clientResult s (largeEpochPopAnyProg fl.pBase)
    let s' := (Memory.spec 0).clientState s (largeEpochPopAnyProg fl.pBase)
    let slack' :=
      if fl.io.usePaged = 0 ∨ (extractPageUnperm fl.io.pgL s.mem).cleanPhase = 0 then 0 else 24
    ∃ (u : Fin fl.U) (v : Fin fl.V),
      res = (u.val, v.val) ∧ s_abs u = some v ∧
      s'.frontier = s.frontier ∧
      LargeEpochInv fl slack' seeds s'.mem (Function.update s_abs u none) ∧
      (s.mem (fl.metaBase + 2) = 0 →
        s'.mem (fl.metaBase + 2) = 0 ∧
        memoryCost (largeEpochPopAnyProg fl.pBase) s ≤ largeFastStepCost fl.c) ∧
      (∀ addr, ¬fl.OwnsFastAddr addr → s'.mem addr = s.mem addr) ∧
      (fl.io.usePaged ≠ 0 →
        (extractPagePair fl.io.pgL s'.mem).virtLen fl.io.partner.side =
          (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side ∧
        (extractPagePair fl.io.pgL s'.mem).totalItems =
          (extractPagePair fl.io.pgL s.mem).totalItems - 1 ∧
        ∀ idx < (extractPagePair fl.io.pgL s.mem).virtLen fl.io.partner.side,
          slotIoPairAt fl.io.partner s'.mem idx = slotIoPairAt fl.io.partner s.mem idx) := by
  have hm2 : (Memory.spec 0).clientResult s (fastReadMetaProg (fl.pBase, 2)) =
      s.mem (fl.metaBase + 2) := clientResult_fastReadMetaProg hinv.1 (by decide)
  have hcm2 := memoryCost_fastReadMetaProg (fl.pBase, 2) s
  unfold largeEpochPopAnyProg
  rcases hinv.2 with ⟨hm0, hf⟩ | ⟨hm1, hfb⟩
  · obtain ⟨u, v, hres, hsu, hfr, hc, hinv', _, hof, hpg⟩ :=
      fastPopAnyProg_spec (by decide) hv (hf.toGen 0) (hpos.1 hm0)
    refine ⟨u, v, ?_, hsu, ?_, ?_, fun _ => ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [prog_clientResult_bind, clientState_fastReadMetaProg, hm2, hm0, ite_eq_left rfl]
      exact hres
    · rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm2, hm0,
        ite_eq_left rfl]; exact hfr
    · rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm2, hm0,
        ite_eq_left rfl]; exact LargeEpochInv.fast hinv'.toInv
    · rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm2, hm0,
        ite_eq_left rfl]; exact hinv'.toInv.mode_zero
    · rw [Realization.memoryCost_bind', clientState_fastReadMetaProg, hm2, hm0, ite_eq_left rfl]
      have hle : fastPopAnyCost fl.c ≤
          max (max (fastProbeCost fl.c) (fastDeleteCost fl.c))
            (max (fastInsertCost fl.c) (fastPopAnyCost fl.c)) :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      unfold largeFastStepCost; omega
    · intro a ha
      rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm2, hm0,
        ite_eq_left rfl]; exact hof a ha
    · intro hup
      rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm2, hm0,
        ite_eq_left rfl]; exact hpg hup
  · have hnz : s.mem (fl.metaBase + 2) ≠ 0 := by rw [hm1]; exact Nat.one_ne_zero
    obtain ⟨hfr, hpt', _, ⟨u, v, hres, hsu, hfb'⟩, hof, hpg⟩ :=
      fastFallbackPopAnyProg_spec hv hinv.1 hfb (hpos.2 hm1)
    refine ⟨u, v, ?_, hsu, ?_, ?_, fun h0 => absurd h0 hnz, ?_, ?_⟩
    · rw [prog_clientResult_bind, clientState_fastReadMetaProg, hm2, ite_eq_right hnz]
      exact hres
    · rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm2, ite_eq_right hnz]
      exact hfr
    · rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm2, ite_eq_right hnz]
      exact LargeEpochInv.fallback hpt' hfb'
    · intro a ha
      rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm2, ite_eq_right hnz]
      exact hof a ha
    · intro hup
      rw [StateTransitionSpec.clientState_bind, clientState_fastReadMetaProg, hm2, ite_eq_right hnz]
      exact hpg hup

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp
