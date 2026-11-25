/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.DualEpochWindow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Deterministic Dual-Epoch Rebuild Schedule, `1 · OPT` Space Bounds, and `WindowCovers`

This module defines the purely deterministic, seed-independent phase/window control schedule and
quantitative support lemmas for the deamortized worst-case WHP resizable succinct dictionary
([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024]):

1. **Metadata-width and padded `1 · OPT` word-space bounds:**
   * `epochMetaWordsWhp_le_self`: whenever `whpThreshold c ≤ N < 2 ^ w`,
     `epochMetaWordsWhp c w N ≤ N + 120` (because `60000 * Dynamic.logLogFactor N ≤ Nat.log 2 N`).
   * `dualEpochPaddedWords_le_succinctWords`: the Stage-A/Stage-B padded footprint
     `rootHdrWhp + max M_src M_dst + M_dst + 16 + packedWords n_t (max w_src w_dst) w` fits inside
     `Dynamic.succinctWords (whpResizableSpaceFactor c) whpResizableSpaceConst U V w n_t`
     (`1 · OPT`, never `2 · OPT`).
2. **Band-stable `PageUnpermState` transfer (`valid_extractPageUnperm_of_band`):**
   Couples `extractPageUnperm L mem` to `pagePairInitBand L.pgB q₀ r_cur` once directory and tail
   tables are initialized with snapshot `q₀` (`0 < q₀ → 5 * B ≤ 4 * r_cur ≤ 11 * B`).
3. **`unpermRank` Lyapunov decay under concurrent user updates:**
   Bounds the increase of `PageUnpermState.unpermRank` under `appendSlot true` / `popBackSlot true`
   during `cleanPhase ∈ {1, 2, 3}` (at most `+ 64`), guaranteeing termination at `cleanPhase = 4`
   within a fixed batch budget of `calcUnpermTicks` rounds of `itemBatchWhp = 1024` `unpermStep`s
   (`960` net rank drop per tick).
4. **Prefix-monotone `WindowCovers` invariant and `GoodEpochAt` bridge:**
   Connects `windowOfEvents` along growing prefixes `evs ↦ evs ++ [upd]` cleanly without ever
   shifting `GoodEpochSeeds` backward.
5. **Deterministic 2-stage rebuild capacity triggers and window bounds (`dualTriggerCap`,
   `dualPaddedWords`):**
   Pure capacity targets and budget bounds driven solely by the dictionary's live cardinality
   `n_t`, proving `EpochCapSafe` on both epochs across the rebuild window, resting hysteresis,
   `1 · OPT` frontier bounds, and per-epoch `≤ 4 * N` event-log length bounds.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–6][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM.Resizable.Randomized
open EpochUpdate

/-! ## Section 1: Metadata-Ratio and Padded `1 · OPT` Dual-Epoch Space Bounds -/

/-- Auxiliary exponential domination: `180000 * k ≤ 2 ^ k` for every `k ≥ 22`. -/
private theorem mul_le_two_pow_of_22 {k : ℕ} (hk : 22 ≤ k) : 180000 * k ≤ 2 ^ k := by
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 22 := ⟨k - 22, by omega⟩
  induction d with
  | zero => decide
  | succ d ih =>
    have hpow : 180000 ≤ 2 ^ (d + 22) :=
      calc 180000 ≤ 180000 * (d + 22) := Nat.le_mul_of_pos_right _ (by omega)
        _ ≤ 2 ^ (d + 22) := ih (by omega)
    rw [show d + 1 + 22 = (d + 22) + 1 by omega, Nat.pow_succ]
    have := ih (by omega)
    omega

/-- At every large capacity `whpThreshold c ≤ N`, `60000 * Dynamic.logLogFactor N ≤ Nat.log 2 N`. -/
theorem sixtyThousand_mul_ell_le_log {c N : ℕ} (hth : whpThreshold c ≤ N) :
    60000 * Dynamic.logLogFactor N ≤ Nat.log 2 N := by
  have hbm := bMinWhp_le_log hth
  have hbmin := le_bMinWhp c
  set m := Nat.log 2 N
  have hm_ge : 6553600 ≤ m := hbmin.trans hbm
  have hN_ge : 4 ≤ N := four_le_of_whpThreshold_le hth
  have hlt_clog : Nat.clog 2 N ≤ m + 1 := by
    refine (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr ?_
    exact (Nat.lt_pow_succ_log_self Nat.one_lt_two N).le
  have hL_le : Dynamic.logLogFactor N ≤ Nat.clog 2 (m + 1) := by
    unfold Dynamic.logLogFactor
    rw [max_eq_left hN_ge]
    exact Nat.clog_mono_right 2 hlt_clog
  set k := Dynamic.logLogFactor N
  by_cases hk : k ≤ 24
  · have : 60000 * k ≤ 60000 * 24 := Nat.mul_le_mul_left 60000 hk
    omega
  · have hlt_m : 2 ^ (k - 1) < m + 1 := by
      have hk_pos : 0 < k := Dynamic.one_le_logLogFactor N
      have hclog_gt : k - 1 < Nat.clog 2 (m + 1) := by omega
      exact (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mp hclog_gt
    have hdom := mul_le_two_pow_of_22 (k := k - 1) (by omega)
    have h60 : 60000 * k ≤ 180000 * (k - 1) := by omega
    omega

/-- At every large capacity `whpThreshold c ≤ N < 2 ^ w`, `epochMetaWordsWhp c w N ≤ N + 120`. -/
theorem epochMetaWordsWhp_le_self {c w N : ℕ} (hth : whpThreshold c ≤ N) (hNw : N < 2 ^ w) :
    epochMetaWordsWhp c w N ≤ N + 120 := by
  have hbits := epochMetaWordsWhp_le_bits c w N
  have hN_pos : 0 < N := lt_of_lt_of_le (whpThreshold_pos c) hth
  have hw_gt : Nat.log 2 N < w := by
    by_contra h
    have hle : w ≤ Nat.log 2 N := Nat.le_of_not_lt h
    have hpow := Nat.pow_log_le_self 2 hN_pos.ne'
    have h2 : 2 ^ w ≤ 2 ^ Nat.log 2 N := Nat.pow_le_pow_right (by decide) hle
    omega
  have hratio := sixtyThousand_mul_ell_le_log hth
  have hmul : 60000 * N * Dynamic.logLogFactor N ≤ N * w := by
    calc 60000 * N * Dynamic.logLogFactor N
        = N * (60000 * Dynamic.logLogFactor N) := by ring
      _ ≤ N * Nat.log 2 N := Nat.mul_le_mul_left N hratio
      _ ≤ N * w := Nat.mul_le_mul_left N hw_gt.le
  have hdiv : (60000 * N * Dynamic.logLogFactor N + w - 1) / w ≤ N := by
    have hw_pos : 0 < w := by omega
    rw [Nat.div_le_iff_le_mul_add_pred hw_pos, Nat.mul_comm w N]
    omega
  omega

/-- Lower bound `32 ≤ epochMetaWordsWhp c w N` whenever `whpThreshold c ≤ N`. -/
theorem thirtyTwo_le_epochMetaWordsWhp {c w N : ℕ} (hth : whpThreshold c ≤ N) :
    32 ≤ epochMetaWordsWhp c w N := by
  unfold epochMetaWordsWhp
  rw [ite_eq_right (Nat.not_lt.mpr hth)]
  dsimp only; omega

/-- **Padded Dual-Epoch `1 · OPT` Space Theorem (`dualEpochPaddedWords_le_succinctWords`).**
Uses `pad = max M_src M_dst` plus additive slack `16` (covering both Stage A `slot 0 → slot 1` and
Stage B `slot 1 → slot 0` with `+ 2` slide gap) inside the exact same
`Dynamic.succinctWords (whpResizableSpaceFactor c) whpResizableSpaceConst U V w n_t` budget. -/
theorem dualEpochPaddedWords_le_succinctWords {c U V w N_src N_dst n_t : ℕ}
    (hsrc : EpochCapSafe (whpThreshold c) U N_src n_t)
    (hdst : EpochCapSafe (whpThreshold c) U N_dst n_t) :
    rootHdrWhp + max (epochMetaWordsWhp c w N_src) (epochMetaWordsWhp c w N_dst) +
      epochMetaWordsWhp c w N_dst + 16 +
      packedWords n_t (max (epochItemBitsWhp c U V N_src) (epochItemBitsWhp c U V N_dst)) w ≤
      Dynamic.succinctWords (whpResizableSpaceFactor c) whpResizableSpaceConst U V w n_t := by
  have hm_src := epochSafe_metaWords_le (w := w) hsrc
  have hm_dst := epochSafe_metaWords_le (w := w) hdst
  have hm_pad : max (epochMetaWordsWhp c w N_src) (epochMetaWordsWhp c w N_dst) ≤
      (720000 * n_t * Dynamic.logLogFactor n_t + w - 1) / w + 120 :=
    max_le hm_src hm_dst
  have hi_src := epochSafe_itemBits_le_optBits (V := V) hsrc
  have hi_dst := epochSafe_itemBits_le_optBits (V := V) hdst
  have hmax_item :
      n_t * max (epochItemBitsWhp c U V N_src) (epochItemBitsWhp c U V N_dst) ≤
        Dynamic.optBits U V n_t + (bMinWhp c + 48) * n_t * Dynamic.logLogFactor n_t := by
    rcases max_choice (epochItemBitsWhp c U V N_src) (epochItemBitsWhp c U V N_dst) with h | h <;>
      rw [h]
    · exact hi_src
    · exact hi_dst
  have hfac : 1440000 + (bMinWhp c + 48) ≤ whpResizableSpaceFactor c := by
    unfold whpResizableSpaceFactor whpSpaceFactor; omega
  have hbits :
      720000 * n_t * Dynamic.logLogFactor n_t +
        720000 * n_t * Dynamic.logLogFactor n_t +
        n_t * max (epochItemBitsWhp c U V N_src) (epochItemBitsWhp c U V N_dst) ≤
        Dynamic.optBits U V n_t +
          whpResizableSpaceFactor c * n_t * Dynamic.logLogFactor n_t := by
    calc 720000 * n_t * Dynamic.logLogFactor n_t +
          720000 * n_t * Dynamic.logLogFactor n_t +
          n_t * max (epochItemBitsWhp c U V N_src) (epochItemBitsWhp c U V N_dst)
        ≤ 720000 * n_t * Dynamic.logLogFactor n_t +
            720000 * n_t * Dynamic.logLogFactor n_t +
            (Dynamic.optBits U V n_t + (bMinWhp c + 48) * n_t * Dynamic.logLogFactor n_t) :=
          Nat.add_le_add_left hmax_item _
      _ = Dynamic.optBits U V n_t +
            (1440000 + (bMinWhp c + 48)) * n_t * Dynamic.logLogFactor n_t := by ring
      _ ≤ Dynamic.optBits U V n_t +
            whpResizableSpaceFactor c * n_t * Dynamic.logLogFactor n_t := by gcongr
  have hd := dualEpochWords_le_succinctWords
    (hdrWords := rootHdrWhp)
    (M_src := max (epochMetaWordsWhp c w N_src) (epochMetaWordsWhp c w N_dst))
    (M_dst := epochMetaWordsWhp c w N_dst)
    (c_src := 120) (c_dst := 120) hm_pad hm_dst hbits
  unfold whpResizableSpaceConst Dynamic.succinctWords rootHdrWhp at hd ⊢
  omega

/-! ## Section 2: Band-Stable `extractPageUnperm` Transfer Theorem -/

/-- Like `valid_extractPageUnperm_of_init`, but parameterized by an independent snapshot `q₀` and
live tail count `r_cur` inside the band `5 * pgB ≤ 4 * r_cur ≤ 11 * pgB` (`0 < q₀`). Used right
when incremental `pageInitTailBatchProg` finishes under concurrent user operations. -/
theorem valid_extractPageUnperm_of_band {L : PageArenaLayout} {mem : ℕ → ℕ} {q₀ r_cur : ℕ}
    (hpg32 : 32 ≤ L.pgB) (_hmp4 : 4 ≤ L.maxPages)
    (hr_hi : 4 * r_cur ≤ 11 * L.pgB) (hr_lo : 0 < q₀ → 5 * L.pgB ≤ 4 * r_cur)
    (hq_lt : q₀ < L.maxPages)
    (hc_ph : (extractPageUnperm L mem).cleanPhase = 0)
    (hc_vp : (extractPageUnperm L mem).cleanVp = 0)
    (hc_off : (extractPageUnperm L mem).cleanOff = 0)
    (hps : (extractPagePair L mem).pageSize = L.pgB)
    (hfp : (extractPagePair L mem).fullPages = fun s => if s then 0 else q₀)
    (htc : (extractPagePair L mem).tailCount = fun s => if s then 0 else r_cur)
    (hth : (extractPagePair L mem).tailHead = fun _ => 0)
    (hjob : (extractPagePair L mem).job = .idle)
    (hpo : ∀ side vp, vp < L.maxPages →
      (extractPagePair L mem).pageOf side vp = if side then 0 else vp)
    (hos : ∀ P < L.maxPages, (extractPagePair L mem).ownerSide P = false)
    (hov : ∀ P < L.maxPages, (extractPagePair L mem).ownerVp P = P)
    (htr : ∀ side k, k < 4 * L.pgB →
      (extractPagePair L mem).tailRes side k = (q₀ * L.pgB + k) % (8 * L.pgB))
    (htos : ∀ res < 8 * L.pgB, (extractPagePair L mem).tailOwnerSide res = false)
    (htor : ∀ res < 8 * L.pgB,
      (extractPagePair L mem).tailOwnerRing res =
        (res + 8 * L.pgB - (q₀ * L.pgB) % (8 * L.pgB)) % (8 * L.pgB)) :
    let u := extractPageUnperm L mem
    u.Valid ∧ u.cleanPhase = 0 ∧ u.st.pageSize = L.pgB ∧
    u.st.totalPages = q₀ ∧ u.st.virtLen false = q₀ * L.pgB + r_cur ∧
    u.st.virtLen true = 0 ∧
    ∀ idx < q₀ * L.pgB + r_cur, u.toPhys false idx = idx := by
  have hmax : max 32 L.pgB = L.pgB := max_eq_right hpg32
  set st := extractPagePair L mem
  set st₀ := pagePairInitBand L.pgB q₀ r_cur
  obtain ⟨hwb₀, hv₀, hps₀, hvl₀_f, hvl₀_t, hid₀⟩ :=
    pagePairInitBand_valid hpg32 hr_hi hr_lo
  have hfp_eq : st.fullPages = st₀.fullPages := by rw [hfp]; rfl
  have htc_eq : st.tailCount = st₀.tailCount := by rw [htc]; rfl
  have hth_eq : st.tailHead = st₀.tailHead := by rw [hth]; rfl
  have hps_eq : st.pageSize = st₀.pageSize := by rw [hps, hps₀]
  have hvl_eq : st.virtLen = st₀.virtLen := by
    ext s; unfold PagePairState.virtLen; rw [hps_eq, hfp_eq, htc_eq]
  have htp_eq : st.totalPages = q₀ := by
    unfold PagePairState.totalPages; rw [hfp]; simp
  have htp₀ : st₀.totalPages = q₀ := by
    unfold PagePairState.totalPages; simp [st₀, pagePairInitBand]
  have hti_eq : st.totalItems = st₀.totalItems := by
    unfold PagePairState.totalItems; rw [hvl_eq]
  have hrs_eq : ∀ s t, st.ringSlot s t = st₀.ringSlot s t := fun s t => by
    unfold PagePairState.ringSlot; rw [hth_eq, hps_eq]
  have hM_pos : 0 < 8 * L.pgB := by omega
  have htr_eq : ∀ s t, t < st₀.tailCount s → st.tailPhys s t = st₀.tailPhys s t := fun s t _ => by
    unfold PagePairState.tailPhys
    rw [htp_eq, ← htp₀, hps_eq, hrs_eq s t]
    have hlt4 : st₀.ringSlot s t < 4 * L.pgB := by
      unfold PagePairState.ringSlot; rw [hps₀]
      exact Nat.mod_lt _ (by omega)
    rw [htr s _ hlt4]
    change st₀.totalPages * st₀.pageSize +
      ((q₀ * L.pgB + st₀.ringSlot s t) % (8 * L.pgB) + 8 * st₀.pageSize -
        (st₀.totalPages * st₀.pageSize) % (8 * st₀.pageSize)) % (8 * st₀.pageSize) =
      st₀.totalPages * st₀.pageSize +
        ((q₀ * max 32 L.pgB + st₀.ringSlot s t) % (8 * max 32 L.pgB) + 8 * st₀.pageSize -
          (st₀.totalPages * st₀.pageSize) % (8 * st₀.pageSize)) % (8 * st₀.pageSize)
    rw [hmax]
  have hv_st : st.Valid :=
    { pageSize_pos := by rw [hps]; omega
      tailCount_lt := fun s => by rw [htc_eq, hps_eq]; exact hv₀.tailCount_lt s
      tailSum_lt := by rw [htc_eq, hps_eq]; exact hv₀.tailSum_lt
      tailHead_lt := fun s => by rw [hth_eq, hps_eq]; exact hv₀.tailHead_lt s
      page_lt := fun s vp hvp => by
        rw [htp_eq]; cases s
        · have hv_lt : vp < q₀ := by rw [hfp] at hvp; exact hvp
          rw [hpo false vp (lt_trans hv_lt hq_lt)]; exact hv_lt
        · rw [hfp] at hvp; simp at hvp
      owner_pageOf := fun s vp hvp => by
        cases s
        · have hv_lt : vp < q₀ := by rw [hfp] at hvp; exact hvp
          have hP := lt_trans hv_lt hq_lt
          change st.ownerSide (st.pageOf false vp) = false ∧ st.ownerVp (st.pageOf false vp) = vp
          rw [hpo false vp hP]; simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨hos vp hP, hov vp hP⟩
        · rw [hfp] at hvp; simp at hvp
      pageOf_owner := fun P hP => by
        rw [htp_eq] at hP
        have hP' := lt_trans hP hq_lt
        rw [hos P hP', hov P hP']
        refine ⟨by rw [hfp]; exact hP, ?_⟩
        rw [hpo false P hP']; rfl
      tailRes_lt := fun s t _ => by
        have hlt4 : st.ringSlot s t < 4 * L.pgB := by
          unfold PagePairState.ringSlot; rw [hps]; exact Nat.mod_lt _ (by omega)
        rw [htr s _ hlt4, hps]; exact Nat.mod_lt _ hM_pos
      tail_lt := fun s t ht => by
        have ht₀ : t < st₀.tailCount s := by rwa [htc_eq] at ht
        rw [hti_eq, htr_eq s t ht₀]; exact hv₀.tail_lt s t ht₀
      owner_tail := fun s t ht => by
        have ht₀ : t < st₀.tailCount s := by rwa [htc_eq] at ht
        have hlt4 : st.ringSlot s t < 4 * L.pgB := by
          unfold PagePairState.ringSlot; rw [hps]; exact Nat.mod_lt _ (by omega)
        have hres_lt : (q₀ * L.pgB + st.ringSlot s t) % (8 * L.pgB) < 8 * L.pgB :=
          Nat.mod_lt _ hM_pos
        dsimp only
        rw [htr s _ hlt4, htos _ hres_lt, htor _ hres_lt]
        have ho := hv₀.owner_tail s t ht₀
        dsimp only at ho
        rw [hrs_eq s t]
        cases s
        · refine ⟨rfl, ?_⟩
          have : st₀.tailOwnerRing (st₀.tailRes false (st₀.ringSlot false t)) =
              st₀.ringSlot false t := ho.2
          simpa only [st₀, pagePairInitBand, hmax] using this
        · simp [st₀, pagePairInitBand] at ht₀
      tail_owner := fun p hp_lo hp_hi => by
        have hp_lo₀ : st₀.totalPages * st₀.pageSize ≤ p := by rwa [htp_eq, ← htp₀, hps_eq] at hp_lo
        have hp_hi₀ : p < st₀.totalItems := by rwa [hti_eq] at hp_hi
        have hm_lt : p % (8 * L.pgB) < 8 * L.pgB := Nat.mod_lt _ hM_pos
        have ho := hv₀.tail_owner p hp_lo₀ hp_hi₀
        dsimp only at ho ⊢
        rw [hps, htos _ hm_lt, htor _ hm_lt, hth_eq]
        have hring_eq : (p % (8 * L.pgB) + 8 * L.pgB - (q₀ * L.pgB) % (8 * L.pgB)) %
            (8 * L.pgB) = st₀.tailOwnerRing (p % (8 * st₀.pageSize)) := by
          simp [st₀, pagePairInitBand, hmax]
        have hside_eq : false = st₀.tailOwnerSide (p % (8 * st₀.pageSize)) := rfl
        rw [hring_eq, hside_eq]
        obtain ⟨h1, h2, h3⟩ := ho
        have hidx_eq : ringIdxOfSlot (st₀.tailHead (st₀.tailOwnerSide (p % (8 * st₀.pageSize))))
            L.pgB (st₀.tailOwnerRing (p % (8 * st₀.pageSize))) =
            ringIdxOfSlot (st₀.tailHead (st₀.tailOwnerSide (p % (8 * st₀.pageSize))))
              st₀.pageSize (st₀.tailOwnerRing (p % (8 * st₀.pageSize))) := by rw [hps₀]
        refine ⟨by rwa [← hps₀], ?_, ?_⟩
        · rw [hidx_eq, htc_eq]; exact h2
        · rw [hidx_eq, htr_eq _ _ h2]; exact h3 }
  have hphi_eq : st.phi = st₀.phi := by
    unfold PagePairState.phi; rw [hps_eq, hfp_eq, htc_eq]
  have hwb_st : st.WellBalanced :=
    { valid := hv_st
      pageSize_ge := by rw [hps]; exact hpg32
      jobValid := by unfold PagePairState.JobValid; rw [hjob]; trivial
      pot_bound := by
        rw [hjob, ite_eq_left rfl, hphi_eq, hps_eq]
        have hp := hwb₀.pot_bound
        change if (PageJob.idle : PageJob) = .idle then _ else _ at hp
        rwa [ite_eq_left rfl] at hp
      side_bound := by unfold PagePairState.ActiveSideBound; rw [hjob]; trivial }
  have hvalid_u : (extractPageUnperm L mem).Valid := by
    have hinv := PageUnpermState.valid_ofPagePair hwb_st
    have hrec : extractPageUnperm L mem = PageUnpermState.ofPagePair st := by
      unfold extractPageUnperm PageUnpermState.ofPagePair
      simp only [extractPageUnperm] at hc_ph hc_vp hc_off
      rw [hc_ph, hc_vp, hc_off]
    change (extractPageUnperm L mem).InvWithSlack 0
    rw [hrec]; exact hinv
  refine ⟨hvalid_u, hc_ph, hps, htp_eq, by change st.virtLen false = _; rw [hvl_eq, hvl₀_f],
    by change st.virtLen true = _; rw [hvl_eq, hvl₀_t], fun idx hidx => ?_⟩
  have hto : (extractPageUnperm L mem).toPhys false idx = st.toPhys false idx := by
    unfold PageUnpermState.toPhys PageUnpermState.effCleanPage PagePairState.toPhys
    have : (extractPageUnperm L mem).st = st := rfl
    have heff : ∀ P off,
        (extractPageUnperm L mem).effCleanPage P off = st.effPage P off := fun P off => by
      unfold PageUnpermState.effCleanPage; rw [hc_ph]; simp [this]
    simp only [hc_ph, Nat.reduceEqDiff, false_and, ↓reduceIte]
    rfl
  rw [hto]
  unfold PagePairState.toPhys
  change (if idx < st.fullPages false * st.pageSize then _ else _) = idx
  rw [hps, hfp]
  by_cases hfull : idx < q₀ * L.pgB
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [ite_eq_left hfull]
    have hdiv_lt : idx / L.pgB < q₀ := (Nat.div_lt_iff_lt_mul (by omega)).mpr hfull
    rw [hpo false (idx / L.pgB) (lt_trans hdiv_lt hq_lt)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold PagePairState.effPage
    rw [hjob]
    dsimp only
    rw [Nat.mul_comm (idx / L.pgB) L.pgB]
    exact Nat.div_add_mod idx L.pgB
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [ite_eq_right hfull]
    have ht_lt : idx - q₀ * L.pgB < st₀.tailCount false := by
      change idx - q₀ * L.pgB < r_cur; omega
    rw [htr_eq false (idx - q₀ * L.pgB) ht_lt]
    have hi0 := hid₀ idx hidx
    unfold PagePairState.toPhys at hi0
    rw [hps₀] at hi0
    have hqf0 : st₀.fullPages false = q₀ := rfl
    rw [hqf0, ite_eq_right hfull] at hi0
    exact hi0

/-- Choosing `q₀` at snapshot `n_0` and shifting `n_cur` by `|n_cur - n_0| ≤ pgB / 8` keeps `r_cur`
strictly inside the `pagePairInitBand` window `5 * pgB ≤ 4 * r_cur ≤ 11 * pgB` (`0 < q₀`). -/
theorem snap_band_of_drift {pgB n₀ n_cur : ℕ} (hB32 : 32 ≤ pgB)
    (hlo : n₀ ≤ n_cur + pgB / 8) (hhi : n_cur ≤ n₀ + pgB / 8) :
    let base_r := pgB + pgB / 2
    let q₀ := if n₀ < pgB + base_r then 0 else (n₀ - base_r) / pgB
    q₀ * pgB ≤ n_cur ∧
    4 * (n_cur - q₀ * pgB) ≤ 11 * pgB ∧
    (0 < q₀ → 5 * pgB ≤ 4 * (n_cur - q₀ * pgB)) := by
  dsimp only
  split_ifs with hsm
  · refine ⟨by simp, by omega, fun h => absurd h (by decide)⟩
  · have hq_mul : (n₀ - (pgB + pgB / 2)) / pgB * pgB ≤ n₀ - (pgB + pgB / 2) :=
      Nat.div_mul_le_self _ _
    have hlt := Nat.mod_lt (n₀ - (pgB + pgB / 2)) (by omega : 0 < pgB)
    have hmod_le : n₀ - (pgB + pgB / 2) < ((n₀ - (pgB + pgB / 2)) / pgB + 1) * pgB := by
      have hdiv := Nat.div_add_mod (n₀ - (pgB + pgB / 2)) pgB
      nlinarith
    have hmul_comm : (n₀ - (pgB + pgB / 2)) / pgB * pgB =
        pgB * ((n₀ - (pgB + pgB / 2)) / pgB) := Nat.mul_comm _ _
    have hbase : n₀ - (pgB + pgB / 2) =
        ((n₀ - (pgB + pgB / 2)) / pgB) * pgB + (n₀ - (pgB + pgB / 2)) % pgB := by
      rw [hmul_comm]; exact (Nat.div_add_mod _ _).symm
    refine ⟨by omega, by omega, fun _ => by omega⟩

/-! ## Section 3: `unpermRank` Bounds Under `appendSlot` / `popBackSlot` and Batched Decay -/

private theorem dev_diff_tail_le (B q r₁ r₂ : ℕ) (h1 : r₁ ≤ r₂ + 1) (h2 : r₂ ≤ r₁ + 1) :
    PagePairState.dev B q r₁ ≤ PagePairState.dev B q r₂ + 1 := by
  unfold PagePairState.dev
  split_ifs <;> omega

private theorem swapTailSlots_meta (st : PagePairState) (p₁ p₂ : ℕ) :
    let st' := (st.swapTailSlots p₁ p₂).1
    st'.pageSize = st.pageSize ∧ st'.fullPages = st.fullPages ∧
      st'.tailCount = st.tailCount ∧ st'.job = st.job := by
  unfold PagePairState.swapTailSlots; split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

private theorem jobPot_tick_step_le {st : PagePairState} {slack : ℕ}
    (hB32 : 32 ≤ st.pageSize) (hf0 : st.fullPages false = 0) (ht0 : st.tailCount false = 0)
    (hjv : st.JobValid) (hsb : st.ActiveSideBound (6 * st.pageSize + 2 + slack))
    (hsl : slack ≤ 16) (hj : st.job ≠ .idle) :
    let st' := st.tick.1
    st'.pageSize = st.pageSize ∧
    (st'.fullPages true = st.fullPages true ∧
        PageUnpermState.jobPot st' ≤ PageUnpermState.jobPot st ∨
     st'.fullPages true = st.fullPages true + 1 ∧
       PageUnpermState.jobPot st' + (2 * st.pageSize - 35) ≤ PageUnpermState.jobPot st ∨
     st'.fullPages true + 1 = st.fullPages true ∧
       PageUnpermState.jobPot st' ≤ PageUnpermState.jobPot st) := by
  have hms_le : ∀ s : PagePairState,
      PageUnpermState.jobPot s.maybeStartJob ≤ PageUnpermState.jobPot s := by
    intro s
    unfold PagePairState.maybeStartJob
    cases hsj : s.job <;> try exact le_rfl
    dsimp only
    have hrem : ∀ j : PageJob,
        (j = .promote false 0 ∨ j = .promote true 0 ∨
         j = .demoteSwap false 0 ∨ j = .demoteSwap true 0 ∨
         j = .demoteBuild false 0 ∨ j = .demoteBuild true 0) →
        PageUnpermState.jobPot { s with job := j } ≤ PageUnpermState.jobPot s := by
      intro j hj'
      unfold PageUnpermState.jobPot PagePairState.remTicks PagePairState.phi
      rw [hsj]
      rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
    split_ifs <;> first | exact le_rfl | exact hrem _ (by simp)
  have hms_fp : ∀ s : PagePairState, s.maybeStartJob.fullPages = s.fullPages := by
    intro s; unfold PagePairState.maybeStartJob; cases s.job <;> try rfl
    dsimp only; split_ifs <;> rfl
  have hms_ps : ∀ s : PagePairState, s.maybeStartJob.pageSize = s.pageSize := by
    intro s; unfold PagePairState.maybeStartJob; cases s.job <;> try rfl
    dsimp only; split_ifs <;> rfl
  dsimp only; unfold PagePairState.tick; dsimp only
  rw [hms_ps, hms_fp]
  have hle_ms := hms_le st.tickOne.1
  unfold PagePairState.tickOne at hle_ms ⊢
  cases hjob : st.job with
  | idle => exact absurd hjob hj
  | promote s cur =>
    rw [hjob] at hle_ms
    have hjv' := hjv; unfold PagePairState.JobValid at hjv'; rw [hjob] at hjv'
    have hsb' := hsb; unfold PagePairState.ActiveSideBound PagePairState.remTicks at hsb'
    rw [hjob] at hsb'
    have hs_t : s = true := by
      cases s
      · dsimp only at hjv'; rw [ht0] at hjv'; omega
      · rfl
    subst hs_t
    dsimp only at hle_ms hjv' hsb' ⊢
    by_cases hcur : cur < st.pageSize
    · rw [ite_eq_left hcur] at hle_ms ⊢
      obtain ⟨hps1, hfp1, htc1, _⟩ :=
        swapTailSlots_meta st (st.tailPhys true cur) (st.totalPages * st.pageSize + cur)
      refine ⟨hps1, Or.inl ⟨by dsimp only; rw [hfp1], le_trans hle_ms ?_⟩⟩
      unfold PageUnpermState.jobPot PagePairState.remTicks PagePairState.phi
      rw [hjob]; dsimp only; rw [hps1, hfp1, htc1]
      simp only [reduceCtorEq, ↓reduceIte]; omega
    · rw [ite_eq_right hcur] at hle_ms ⊢
      have hcur_eq : cur = st.pageSize := by omega
      subst hcur_eq
      refine ⟨rfl, Or.inr (Or.inl ⟨by dsimp only; rw [Function.update_self], ?_⟩)⟩
      have hjp1 : PageUnpermState.jobPot
          { st with
            fullPages := Function.update st.fullPages true (st.fullPages true + 1)
            tailCount := Function.update st.tailCount true (st.tailCount true - st.pageSize)
            tailHead := Function.update st.tailHead true
              ((st.tailHead true + st.pageSize) % (4 * st.pageSize))
            pageOf := PagePairState.set2 st.pageOf true (st.fullPages true) st.totalPages
            ownerSide := Function.update st.ownerSide st.totalPages true
            ownerVp := Function.update st.ownerVp st.totalPages (st.fullPages true)
            job := .idle } + (2 * st.pageSize - 35) ≤ PageUnpermState.jobPot st := by
        unfold PageUnpermState.jobPot PagePairState.remTicks PagePairState.phi PagePairState.dev
        rw [hjob]; dsimp only
        simp only [Function.update_self, Function.update_of_ne (by decide : false ≠ true),
          Nat.succ_pos, ↓reduceIte, hf0, ht0, reduceCtorEq]
        split_ifs <;> omega
      exact Nat.le_trans (Nat.add_le_add_right hle_ms _) hjp1
  | demoteSwap s cur =>
    rw [hjob] at hle_ms; dsimp only at hle_ms ⊢
    have hjv' := hjv; unfold PagePairState.JobValid at hjv'; rw [hjob] at hjv'
    by_cases hcur : cur < st.pageSize
    · rw [ite_eq_left hcur] at hle_ms ⊢
      refine ⟨rfl, Or.inl ⟨rfl, le_trans hle_ms ?_⟩⟩
      unfold PageUnpermState.jobPot PagePairState.remTicks PagePairState.phi
      rw [hjob]; dsimp only; simp only [reduceCtorEq, ↓reduceIte]; omega
    · rw [ite_eq_right hcur] at hle_ms ⊢
      refine ⟨rfl, Or.inl ⟨rfl, le_trans hle_ms ?_⟩⟩
      unfold PageUnpermState.jobPot PagePairState.remTicks PagePairState.phi
      rw [hjob]; dsimp only; simp only [reduceCtorEq, ↓reduceIte]; omega
  | demoteBuild s cur =>
    rw [hjob] at hle_ms; dsimp only at hle_ms ⊢
    have hjv' := hjv; unfold PagePairState.JobValid at hjv'; rw [hjob] at hjv'
    have hsb' := hsb; unfold PagePairState.ActiveSideBound PagePairState.remTicks at hsb'
    rw [hjob] at hsb'
    have hs_t : s = true := by
      cases s
      · dsimp only at hjv'; rw [hf0] at hjv'; omega
      · rfl
    subst hs_t
    dsimp only at hjv' hsb'
    by_cases hcur : cur < st.pageSize
    · rw [ite_eq_left hcur] at hle_ms ⊢
      refine ⟨rfl, Or.inl ⟨rfl, le_trans hle_ms ?_⟩⟩
      unfold PageUnpermState.jobPot PagePairState.remTicks PagePairState.phi
      rw [hjob]; dsimp only; simp only [reduceCtorEq, ↓reduceIte]; omega
    · rw [ite_eq_right hcur] at hle_ms ⊢
      refine ⟨rfl, Or.inr (Or.inr ⟨by
          dsimp only; rw [Function.update_self]; omega, le_trans hle_ms ?_⟩)⟩
      unfold PageUnpermState.jobPot PagePairState.remTicks PagePairState.phi PagePairState.dev
      rw [hjob]; dsimp only
      simp only [Function.update_self, Function.update_of_ne (by decide : false ≠ true),
        hf0, ht0, reduceCtorEq, ↓reduceIte]
      split_ifs <;> omega

/-- Initial `unpermRank` upper bound for any valid `u : PageUnpermState` in `cleanPhase ∈ {1..4}`.
-/
theorem unpermRank_le_of_inv {u : PageUnpermState} {slack : ℕ} (hi : u.InvWithSlack slack) :
    u.unpermRank ≤ 2 * u.st.virtLen true + 66 * u.st.pageSize + 200 := by
  have hB32 := hi.pageSize_ge
  have hsl := hi.slack_le
  have hle := hi.phase_le
  unfold PageUnpermState.unpermRank
  dsimp only
  by_cases h0 : u.cleanPhase = 0 ∨ 4 ≤ u.cleanPhase
  · rw [ite_eq_left h0]; omega
  · rw [ite_eq_right h0]
    by_cases h3 : u.cleanPhase = 3
    · rw [ite_eq_left h3]
      have htc := hi.valid.tailCount_lt true
      omega
    · rw [ite_eq_right h3]
      have hjp : PageUnpermState.jobPot u.st ≤ 30 * u.st.pageSize + 30 := by
        unfold PageUnpermState.jobPot
        by_cases hp1 : u.cleanPhase = 1
        · have hwb := (hi.phase1_wb hp1).1
          have hp := hwb.pot_bound
          split_ifs at hp ⊢ <;> omega
        · have hp2 : u.cleanPhase = 2 := by omega
          by_cases ho0 : u.cleanOff = 0
          · have ⟨hwb, hj, _⟩ := hi.phase2_zero hp2 ho0
            have hp := hwb.pot_bound; rw [hj, ite_eq_left rfl] at hp ⊢; omega
          · have ⟨hj, _, _, _, hphi⟩ := hi.phase2_pos hp2 (Nat.pos_of_ne_zero ho0)
            rw [hj, ite_eq_left rfl]; omega
      have hq_le : u.st.fullPages true * u.st.pageSize ≤ u.st.virtLen true := by
        unfold PagePairState.virtLen; omega
      have hq2 : u.st.fullPages true * 2 ≤ u.st.fullPages true * u.st.pageSize :=
        Nat.mul_le_mul_left _ (by omega)
      have hmul : (u.st.fullPages true - min u.cleanVp (u.st.fullPages true)) *
          (u.st.pageSize + 2) ≤ u.st.fullPages true * u.st.pageSize + u.st.fullPages true * 2 := by
        calc (u.st.fullPages true - min u.cleanVp (u.st.fullPages true)) * (u.st.pageSize + 2)
            ≤ u.st.fullPages true * (u.st.pageSize + 2) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
          _ = u.st.fullPages true * u.st.pageSize + u.st.fullPages true * 2 := by ring
      have hb1 : (if u.cleanPhase = 1 then 1 else 0) ≤ 1 := by split_ifs <;> decide
      omega

/-- Monotone drop of `unpermRank` across `k` `unpermStep`s (`PageUnpermState.runUnpermSteps`). -/
theorem unpermRank_runUnpermSteps_le (k : ℕ) {u : PageUnpermState} {slack : ℕ}
    (hi : u.InvWithSlack slack) :
    (u.runUnpermSteps k).1.unpermRank ≤ u.unpermRank - k := by
  induction k generalizing u slack with
  | zero => simp [PageUnpermState.runUnpermSteps]
  | succ m ih =>
    unfold PageUnpermState.runUnpermSteps
    dsimp only
    have hi' : u.unpermStep.1.InvWithSlack slack := (PageUnpermState.unpermStep_spec.{0} hi).1
    by_cases hact : 0 < u.cleanPhase ∧ u.cleanPhase < 4
    · have hlt := PageUnpermState.unpermRank_lt_of_unpermStep hi hact.1 hact.2
      have hnext := ih hi'
      omega
    · have hnr : u.unpermRank = 0 := by
        unfold PageUnpermState.unpermRank
        have : u.cleanPhase = 0 ∨ 4 ≤ u.cleanPhase := by omega
        simp [this]
      have hnr' : (u.unpermStep).1.unpermRank = 0 := by
        by_cases h0 : u.cleanPhase = 0
        · have : u.unpermStep.1 = u := by unfold PageUnpermState.unpermStep; simp [h0]
          rw [this, hnr]
        · have h4 : u.cleanPhase = 4 := by have := hi.phase_le; omega
          have : u.unpermStep.1 = u := by unfold PageUnpermState.unpermStep; simp [h4]
          rw [this, hnr]
      have hnext := ih hi'
      omega

/-- Exact equivalence: for an active `InvWithSlack` state with `0 < u.cleanPhase`,
`u.unpermRank = 0 ↔ u.cleanPhase = 4`. -/
theorem cleanPhase_eq_four_of_unpermRank_zero {u : PageUnpermState} {slack : ℕ}
    (hi : u.InvWithSlack slack) (hpos : 0 < u.cleanPhase) (hz : u.unpermRank = 0) :
    u.cleanPhase = 4 := by
  have hle := hi.phase_le
  by_contra hne
  have hlt4 : u.cleanPhase < 4 := by omega
  unfold PageUnpermState.unpermRank at hz
  rw [ite_eq_right (by omega : ¬(u.cleanPhase = 0 ∨ 4 ≤ u.cleanPhase))] at hz
  by_cases h3 : u.cleanPhase = 3
  · rw [ite_eq_left h3] at hz; omega
  · rw [ite_eq_right h3] at hz
    have hoff : u.cleanOff ≤ u.st.pageSize := by
      by_cases hp1 : u.cleanPhase = 1
      · exact (hi.phase1_wb hp1).2.2 ▸ Nat.zero_le _
      · have hp2 : u.cleanPhase = 2 := by omega
        by_cases ho0 : u.cleanOff = 0
        · omega
        · exact (hi.phase2_pos hp2 (Nat.pos_of_ne_zero ho0)).2.2.1
    have hB : 32 ≤ u.st.pageSize := hi.pageSize_ge
    omega

/-- `PageUnpermState.jobPot` is nonincreasing under `PagePairState.maybeStartJob`. -/
private theorem jobPot_maybeStartJob_le (s : PagePairState) :
    PageUnpermState.jobPot s.maybeStartJob ≤ PageUnpermState.jobPot s := by
  unfold PagePairState.maybeStartJob
  cases hsj : s.job <;> try exact le_rfl
  dsimp only
  have hrem : ∀ j : PageJob,
      (j = .promote false 0 ∨ j = .promote true 0 ∨
       j = .demoteSwap false 0 ∨ j = .demoteSwap true 0 ∨
       j = .demoteBuild false 0 ∨ j = .demoteBuild true 0) →
      PageUnpermState.jobPot { s with job := j } ≤ PageUnpermState.jobPot s := by
    intro j hj'
    unfold PageUnpermState.jobPot PagePairState.remTicks PagePairState.phi
    rw [hsj]
    rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
  split_ifs <;> first | exact le_rfl | exact hrem _ (by simp)

private theorem fullPages_maybeStartJob (s : PagePairState) :
    s.maybeStartJob.fullPages = s.fullPages := by
  unfold PagePairState.maybeStartJob; cases s.job <;> try rfl
  dsimp only; split_ifs <;> rfl

private theorem pageSize_maybeStartJob (s : PagePairState) :
    s.maybeStartJob.pageSize = s.pageSize := by
  unfold PagePairState.maybeStartJob; cases s.job <;> try rfl
  dsimp only; split_ifs <;> rfl

/-- After `PagePairState.runTicks k` from any `DriftInv st slack` with empty side `false`, the
quantity `2 * jobPot st + (fullPages true - min vp (fullPages true)) * (pageSize + 2)` is
nonincreasing (even across a `promote true` commit!). -/
private theorem unpermTailPot_runTicks_le (vp k : ℕ) {st : PagePairState} {slack : ℕ}
    (hd : PagePairState.DriftInv st slack)
    (hf0 : st.fullPages false = 0) (ht0 : st.tailCount false = 0) :
    let st' := (st.runTicks k).1
    st'.pageSize = st.pageSize ∧
    2 * PageUnpermState.jobPot st' +
        (st'.fullPages true - min vp (st'.fullPages true)) * (st'.pageSize + 2) ≤
      2 * PageUnpermState.jobPot st +
        (st.fullPages true - min vp (st.fullPages true)) * (st.pageSize + 2) := by
  induction k generalizing st slack with
  | zero => exact ⟨rfl, le_rfl⟩
  | succ m ih =>
    unfold PagePairState.runTicks
    dsimp only
    have ht_spec := PagePairState.tick_driftInv.{0} hd
    have hd1 : PagePairState.DriftInv st.tick.1 (slack - 1) := ht_spec.1
    have hps1 : st.tick.1.pageSize = st.pageSize := ht_spec.2.1
    have hvl1 : st.tick.1.virtLen = st.virtLen := ht_spec.2.2.1
    have hvl_f0 : st.tick.1.virtLen false = 0 := by
      rw [hvl1]; unfold PagePairState.virtLen; rw [hf0, ht0]; simp
    have hB_pos : 0 < st.tick.1.pageSize := hd1.valid.pageSize_pos
    have hf1 : st.tick.1.fullPages false = 0 := by
      unfold PagePairState.virtLen at hvl_f0
      by_contra hne; have : 1 ≤ st.tick.1.fullPages false := Nat.pos_of_ne_zero hne
      have : st.tick.1.pageSize ≤ st.tick.1.fullPages false * st.tick.1.pageSize :=
        Nat.le_mul_of_pos_left _ this
      omega
    have ht1 : st.tick.1.tailCount false = 0 := by
      unfold PagePairState.virtLen at hvl_f0; rw [hf1] at hvl_f0; omega
    obtain ⟨hps_ih, hpot_ih⟩ := ih hd1 hf1 ht1
    refine ⟨hps_ih.trans hps1, le_trans hpot_ih ?_⟩
    by_cases hidle : st.job = .idle
    · have hst1_eq : st.tick.1 = st.maybeStartJob := by
        unfold PagePairState.tick PagePairState.tickOne; rw [hidle]
      rw [hst1_eq, pageSize_maybeStartJob, fullPages_maybeStartJob]
      have hjp := jobPot_maybeStartJob_le st
      omega
    · have hsb : st.ActiveSideBound (6 * st.pageSize + 2 + slack) := hd.side_bound
      have hB32 := hd.pageSize_ge
      obtain ⟨hps_t, hcase⟩ := jobPot_tick_step_le hB32 hf0 ht0 hd.jobValid hsb hd.slack_le hidle
      rw [hps_t]
      rcases hcase with ⟨hfp, hjp⟩ | ⟨hfp, hjp⟩ | ⟨hfp, hjp⟩
      · rw [hfp]; omega
      · rw [hfp]
        have hsub : st.fullPages true + 1 - min vp (st.fullPages true + 1) ≤
            st.fullPages true - min vp (st.fullPages true) + 1 := by omega
        have hmul : (st.fullPages true + 1 - min vp (st.fullPages true + 1)) * (st.pageSize + 2) ≤
            (st.fullPages true - min vp (st.fullPages true)) * (st.pageSize + 2) +
              (st.pageSize + 2) := by
          calc _ ≤ (st.fullPages true - min vp (st.fullPages true) + 1) * (st.pageSize + 2) :=
                Nat.mul_le_mul_right _ hsub
            _ = _ := by ring
        omega
      · have hsub : st.tick.1.fullPages true - min vp (st.tick.1.fullPages true) ≤
            st.fullPages true - min vp (st.fullPages true) := by omega
        have hmul := Nat.mul_le_mul_right (st.pageSize + 2) hsub
        omega

/-- `appendSlot true` raises `unpermRank` by at most `64` during `cleanPhase ∈ {1, 2, 3}`. -/
theorem unpermRank_appendSlot_le {u : PageUnpermState}
    (hv : u.Valid) (hph0 : 0 < u.cleanPhase) (hph4 : u.cleanPhase < 4) :
    (u.appendSlot true).1.unpermRank ≤ u.unpermRank + 64 := by
  have hB32 := hv.pageSize_ge
  have hvl_f : u.st.virtLen false = 0 := by
    obtain ⟨hf, ht⟩ := hv.src_empty hph0
    unfold PagePairState.virtLen; rw [hf, ht]; simp
  have hf0 : u.st.fullPages false = 0 := (hv.src_empty hph0).1
  have ht0 : u.st.tailCount false = 0 := (hv.src_empty hph0).2
  unfold PageUnpermState.appendSlot
  rw [ite_eq_right (Nat.pos_iff_ne_zero.mp hph0)]
  by_cases hstep : u.cleanPhase = 1 ∨ (u.cleanPhase = 2 ∧ u.cleanOff = 0)
  · rw [ite_eq_left hstep]
    have hwb : u.st.WellBalanced := by
      rcases hstep with hp1 | ⟨hp2, ho0⟩
      · exact (hv.phase1_wb hp1).1
      · exact (hv.phase2_zero hp2 ho0).1
    have hd_r : PagePairState.DriftInv (u.st.rawAppend true).maybeStartJob 16 :=
      (PagePairState.rawAppend_driftInv hwb true).1
    have hfr_raw : (u.st.rawAppend true).maybeStartJob.fullPages false = 0 := by
      rw [fullPages_maybeStartJob]; exact hf0
    have htc_raw : (u.st.rawAppend true).maybeStartJob.tailCount false = 0 := by
      have hm_tc : ∀ s : PagePairState, s.maybeStartJob.tailCount = s.tailCount := fun s => by
        unfold PagePairState.maybeStartJob; cases s.job <;> try rfl
        dsimp only; split_ifs <;> rfl
      rw [hm_tc]; change Function.update u.st.tailCount true (u.st.tailCount true + 1) false = 0
      rw [Function.update_of_ne (by decide : false ≠ true)]; exact ht0
    obtain ⟨hps_r, hpot_r⟩ := unpermTailPot_runTicks_le u.cleanVp 16 hd_r hfr_raw htc_raw
    set st' := (u.st.stepAppend true).1
    set ph' := if st'.job = .idle then 2 else 1
    have hps_ms : (u.st.rawAppend true).maybeStartJob.pageSize = u.st.pageSize :=
      pageSize_maybeStartJob _
    have hfp_ms : (u.st.rawAppend true).maybeStartJob.fullPages true = u.st.fullPages true := by
      rw [fullPages_maybeStartJob]; rfl
    have hjp_raw : PageUnpermState.jobPot (u.st.rawAppend true) ≤
        PageUnpermState.jobPot u.st + 16 := by
      unfold PageUnpermState.jobPot PagePairState.phi PagePairState.remTicks
        PagePairState.rawAppend
      dsimp only
      have h1 := dev_diff_tail_le u.st.pageSize (u.st.fullPages true)
        (u.st.tailCount true + 1) (u.st.tailCount true) le_rfl (by omega)
      simp only [Function.update_self, Function.update_of_ne (by decide : false ≠ true)]
      omega
    have hjp_ms := (jobPot_maybeStartJob_le (u.st.rawAppend true)).trans hjp_raw
    change (⟨st', ph', min u.cleanVp (st'.fullPages true), 0⟩ : PageUnpermState).unpermRank ≤
      u.unpermRank + 64
    unfold PageUnpermState.unpermRank
    dsimp only
    have hph'_ok : ¬(ph' = 0 ∨ 4 ≤ ph') := by dsimp only [ph']; split_ifs <;> decide
    have hph'_n3 : ph' ≠ 3 := by dsimp only [ph']; split_ifs <;> decide
    have hph_ok : ¬(u.cleanPhase = 0 ∨ 4 ≤ u.cleanPhase) := by omega
    have hph_n3 : u.cleanPhase ≠ 3 := by rcases hstep with h1 | ⟨h2, _⟩ <;> omega
    rw [ite_eq_right hph'_ok, ite_eq_right hph'_n3, ite_eq_right hph_ok, ite_eq_right hph_n3]
    have hmin_eq : min (min u.cleanVp (st'.fullPages true)) (st'.fullPages true) =
        min u.cleanVp (st'.fullPages true) := by omega
    have hps_eq : st'.pageSize = u.st.pageSize := hps_r.trans hps_ms
    rw [hmin_eq, hps_eq]
    have hoff_eq : u.cleanOff = 0 := by
      rcases hstep with hp1 | ⟨_, ho0⟩
      · exact (hv.phase1_wb hp1).2.2
      · exact ho0
    have h1_le : (if ph' = 1 then 1 else 0) ≤ 1 := by split_ifs <;> decide
    have hpot_r' : 2 * PageUnpermState.jobPot st' +
        (st'.fullPages true - min u.cleanVp (st'.fullPages true)) * (u.st.pageSize + 2) ≤
        2 * PageUnpermState.jobPot (u.st.rawAppend true).maybeStartJob +
        (u.st.fullPages true - min u.cleanVp (u.st.fullPages true)) * (u.st.pageSize + 2) := by
      have hp' := hpot_r
      change 2 * PageUnpermState.jobPot st' +
          (st'.fullPages true - min u.cleanVp (st'.fullPages true)) * (st'.pageSize + 2) ≤
        2 * PageUnpermState.jobPot (u.st.rawAppend true).maybeStartJob +
          ((u.st.rawAppend true).maybeStartJob.fullPages true -
            min u.cleanVp ((u.st.rawAppend true).maybeStartJob.fullPages true)) *
            ((u.st.rawAppend true).maybeStartJob.pageSize + 2) at hp'
      rw [hps_eq, hps_ms, hfp_ms] at hp'; exact hp'
    have ho : u.cleanOff = 0 := hoff_eq
    simp only [ho, Nat.sub_zero]
    omega
  · rw [ite_eq_right hstep]
    by_cases h3 : u.cleanPhase = 3
    · unfold PageUnpermState.unpermRank
      simp only [h3, Nat.reduceEqDiff, Nat.reduceLeDiff, or_self, ↓reduceIte]
      have htc : (u.st.rawAppend true).tailCount true = u.st.tailCount true + 1 := by
        change Function.update u.st.tailCount true (u.st.tailCount true + 1) true = _
        rw [Function.update_self]
      have htc_lhs : (⟨u.st.rawAppend true, 3, u.cleanVp, u.cleanOff⟩ :
          PageUnpermState).st.tailCount true = u.st.tailCount true + 1 := htc
      omega
    · have hp2 : u.cleanPhase = 2 := by omega
      unfold PageUnpermState.unpermRank
      simp only [hp2, Nat.reduceEqDiff, Nat.reduceLeDiff, or_self, ↓reduceIte]
      have hps : (u.st.rawAppend true).pageSize = u.st.pageSize := rfl
      have hfp : (u.st.rawAppend true).fullPages true = u.st.fullPages true := rfl
      have hjp : PageUnpermState.jobPot (u.st.rawAppend true) ≤
          PageUnpermState.jobPot u.st + 16 := by
        unfold PageUnpermState.jobPot PagePairState.phi PagePairState.remTicks
          PagePairState.rawAppend
        dsimp only
        have h1 : PagePairState.dev u.st.pageSize (u.st.fullPages true)
            (u.st.tailCount true + 1) ≤
            PagePairState.dev u.st.pageSize (u.st.fullPages true) (u.st.tailCount true) + 1 :=
          dev_diff_tail_le _ _ _ _ le_rfl (by omega)
        simp only [Function.update_self, Function.update_of_ne (by decide : false ≠ true)]
        omega
      rw [hps, hfp]; omega

/-- `popBackSlot true` raises `unpermRank` by at most `64` during `cleanPhase ∈ {1, 2, 3}`. -/
theorem unpermRank_popBackSlot_le {u : PageUnpermState}
    (hv : u.Valid) (hpos : 0 < u.st.virtLen true)
    (hph0 : 0 < u.cleanPhase) (hph4 : u.cleanPhase < 4) :
    (u.popBackSlot true).1.unpermRank ≤ u.unpermRank + 64 := by
  have hf0 : u.st.fullPages false = 0 := (hv.src_empty hph0).1
  have ht0 : u.st.tailCount false = 0 := (hv.src_empty hph0).2
  have hraw_meta : (u.st.rawPopBack true).1.pageSize = u.st.pageSize ∧
      (u.st.rawPopBack true).1.fullPages = u.st.fullPages ∧
      (u.st.rawPopBack true).1.tailCount false = 0 ∧
      (u.st.rawPopBack true).1.tailCount true = u.st.tailCount true - 1 ∧
      (u.st.rawPopBack true).1.job = u.st.job := by
    unfold PagePairState.rawPopBack
    have hsw := swapTailSlots_meta u.st
      (u.st.tailPhys true (u.st.tailCount true - 1)) (u.st.totalItems - 1)
    exact ⟨hsw.1, hsw.2.1, by
      change Function.update (u.st.swapTailSlots (u.st.tailPhys true (u.st.tailCount true - 1))
        (u.st.totalItems - 1)).1.tailCount true (u.st.tailCount true - 1) false = 0
      rw [Function.update_of_ne (by decide : false ≠ true), hsw.2.2.1]; exact ht0,
      by change Function.update (u.st.swapTailSlots (u.st.tailPhys true (u.st.tailCount true - 1))
          (u.st.totalItems - 1)).1.tailCount true (u.st.tailCount true - 1) true =
          u.st.tailCount true - 1
         rw [Function.update_self], hsw.2.2.2⟩
  have hjp_raw : PageUnpermState.jobPot (u.st.rawPopBack true).1 ≤
      PageUnpermState.jobPot u.st + 16 := by
    unfold PageUnpermState.jobPot PagePairState.phi PagePairState.remTicks
    rw [hraw_meta.1, hraw_meta.2.1, hraw_meta.2.2.1, hraw_meta.2.2.2.1, hraw_meta.2.2.2.2]
    have h1 := dev_diff_tail_le u.st.pageSize (u.st.fullPages true)
      (u.st.tailCount true - 1) (u.st.tailCount true) (by omega) (by omega)
    rw [ht0]
    cases u.st.job <;> dsimp only <;> omega
  unfold PageUnpermState.popBackSlot
  rw [ite_eq_right (Nat.pos_iff_ne_zero.mp hph0)]
  by_cases hstep : u.cleanPhase = 1 ∨ (u.cleanPhase = 2 ∧ u.cleanOff = 0)
  · rw [ite_eq_left hstep]
    have hwb : u.st.WellBalanced := by
      rcases hstep with hp1 | ⟨hp2, ho0⟩
      · exact (hv.phase1_wb hp1).1
      · exact (hv.phase2_zero hp2 ho0).1
    have hd_r : PagePairState.DriftInv (u.st.rawPopBack true).1.maybeStartJob 16 :=
      (PagePairState.rawPopBack_driftInv.{0} hwb hpos).1
    have hfr_raw : (u.st.rawPopBack true).1.maybeStartJob.fullPages false = 0 := by
      rw [fullPages_maybeStartJob, hraw_meta.2.1]; exact hf0
    have htc_raw : (u.st.rawPopBack true).1.maybeStartJob.tailCount false = 0 := by
      have hm_tc : ∀ s : PagePairState, s.maybeStartJob.tailCount = s.tailCount := fun s => by
        unfold PagePairState.maybeStartJob; cases s.job <;> try rfl
        dsimp only; split_ifs <;> rfl
      rw [hm_tc]; exact hraw_meta.2.2.1
    obtain ⟨hps_r, hpot_r⟩ := unpermTailPot_runTicks_le u.cleanVp 16 hd_r hfr_raw htc_raw
    set st' := (u.st.stepPopBack true).1
    set ph' := if st'.job = .idle then 2 else 1
    have hps_ms : (u.st.rawPopBack true).1.maybeStartJob.pageSize = u.st.pageSize :=
      (pageSize_maybeStartJob _).trans hraw_meta.1
    have hfp_ms : (u.st.rawPopBack true).1.maybeStartJob.fullPages true = u.st.fullPages true := by
      rw [fullPages_maybeStartJob, hraw_meta.2.1]
    have hjp_ms := (jobPot_maybeStartJob_le (u.st.rawPopBack true).1).trans hjp_raw
    change (⟨st', ph', min u.cleanVp (st'.fullPages true), 0⟩ : PageUnpermState).unpermRank ≤
      u.unpermRank + 64
    unfold PageUnpermState.unpermRank
    dsimp only
    have hph'_ok : ¬(ph' = 0 ∨ 4 ≤ ph') := by dsimp only [ph']; split_ifs <;> decide
    have hph'_n3 : ph' ≠ 3 := by dsimp only [ph']; split_ifs <;> decide
    have hph_ok : ¬(u.cleanPhase = 0 ∨ 4 ≤ u.cleanPhase) := by omega
    have hph_n3 : u.cleanPhase ≠ 3 := by rcases hstep with h1 | ⟨h2, _⟩ <;> omega
    rw [ite_eq_right hph'_ok, ite_eq_right hph'_n3, ite_eq_right hph_ok, ite_eq_right hph_n3]
    have hmin_eq : min (min u.cleanVp (st'.fullPages true)) (st'.fullPages true) =
        min u.cleanVp (st'.fullPages true) := by omega
    have hps_eq : st'.pageSize = u.st.pageSize := hps_r.trans hps_ms
    rw [hmin_eq, hps_eq]
    have hoff_eq : u.cleanOff = 0 := by
      rcases hstep with hp1 | ⟨_, ho0⟩
      · exact (hv.phase1_wb hp1).2.2
      · exact ho0
    have h1_le : (if ph' = 1 then 1 else 0) ≤ 1 := by split_ifs <;> decide
    have hpot_r' : 2 * PageUnpermState.jobPot st' +
        (st'.fullPages true - min u.cleanVp (st'.fullPages true)) * (u.st.pageSize + 2) ≤
        2 * PageUnpermState.jobPot (u.st.rawPopBack true).1.maybeStartJob +
        (u.st.fullPages true - min u.cleanVp (u.st.fullPages true)) * (u.st.pageSize + 2) := by
      have hp' := hpot_r
      change 2 * PageUnpermState.jobPot st' +
          (st'.fullPages true - min u.cleanVp (st'.fullPages true)) * (st'.pageSize + 2) ≤
        2 * PageUnpermState.jobPot (u.st.rawPopBack true).1.maybeStartJob +
          ((u.st.rawPopBack true).1.maybeStartJob.fullPages true -
            min u.cleanVp ((u.st.rawPopBack true).1.maybeStartJob.fullPages true)) *
            ((u.st.rawPopBack true).1.maybeStartJob.pageSize + 2) at hp'
      rw [hps_eq, hps_ms, hfp_ms] at hp'; exact hp'
    have ho : u.cleanOff = 0 := hoff_eq
    simp only [ho, Nat.sub_zero]
    omega
  · rw [ite_eq_right hstep]
    by_cases hp2 : u.cleanPhase = 2
    · rw [ite_eq_left hp2]
      unfold PageUnpermState.unpermRank
      simp only [hp2, Nat.reduceEqDiff, Nat.reduceLeDiff, or_self, ↓reduceIte,
        hraw_meta.1, hraw_meta.2.1]
      omega
    · rw [ite_eq_right hp2]
      have h3 : u.cleanPhase = 3 := by omega
      unfold PageUnpermState.unpermRank
      simp only [h3, Nat.reduceEqDiff, Nat.reduceLeDiff, or_self, ↓reduceIte,
        hraw_meta.2.2.2.1]
      omega

/-! ## Section 4: Prefix-Monotone `WindowCovers` Invariant and `GoodEpochAt` -/

/-- `WindowCovers evs win` certifies that an oblivious `EpochWindowSpec c U N` covers the entire
prefix `evs : List (EpochUpdate U V)` (every snapshot, current sub-epoch union, and draining old
batch). Crucial monotonicity: `WindowCovers (evs ++ extra) win → WindowCovers evs win`! -/
structure WindowCovers {c U V N : ℕ}
    (evs : List (EpochUpdate U V)) (win : EpochWindowSpec c U N) : Prop where
  len_lt : evs.length < win.numSnaps
  sub_lt : freshCount evs evs.length / qEpochWhp N < win.numSubs
  snaps_cov : ∀ (t : Fin win.numSnaps), t.val ≤ evs.length →
    liveDom (EpochUpdate.eval (evs.take t.val)) ⊆ win.snaps t
  unions_cov : ∀ (e : Fin win.numSubs), e.val ≤ freshCount evs evs.length / qEpochWhp N →
    liveDom (EpochUpdate.eval (evs.take (subStart evs (qEpochWhp N) e.val))) ∪
      freshBatch evs (qEpochWhp N) e.val ⊆ win.subUnions e
  batches_cov : ∀ (e : Fin win.numSubs), 0 < e.val →
    e.val ≤ freshCount evs evs.length / qEpochWhp N →
    freshBatch evs (qEpochWhp N) (e.val - 1) ⊆ win.subBatches e

theorem isFreshAt_append_left {U V : ℕ} (evs extra : List (EpochUpdate U V)) {k : ℕ}
    (hk : k < evs.length) :
    isFreshAt (evs ++ extra) k = isFreshAt evs k := by
  classical
  unfold isFreshAt
  have hka : k < (evs ++ extra).length := by simp; omega
  rw [dite_eq_left hka, dite_eq_left hk]
  have hget : (evs ++ extra)[k] = evs[k] := List.getElem_append_left hk
  have htake : (evs ++ extra).take k = evs.take k := List.take_append_of_le_length hk.le
  rw [hget, htake]

theorem freshCount_append_left {U V : ℕ} (evs extra : List (EpochUpdate U V)) {k : ℕ}
    (hk : k ≤ evs.length) :
    freshCount (evs ++ extra) k = freshCount evs k := by
  unfold freshCount
  congr 1; ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor <;> rintro ⟨hi, hf⟩
  · exact ⟨hi, by rwa [← isFreshAt_append_left evs extra (lt_of_lt_of_le hi hk)]⟩
  · exact ⟨hi, by rwa [isFreshAt_append_left evs extra (lt_of_lt_of_le hi hk)]⟩

theorem subStart_append_left {U V : ℕ} (evs extra : List (EpochUpdate U V)) {Q e : ℕ}
    (hge : e * Q ≤ freshCount evs evs.length) :
    subStart (evs ++ extra) Q e = subStart evs Q e := by
  classical
  have hlen_le : evs.length ≤ (evs ++ extra).length := by simp
  have hex1 : ∃ k ≤ evs.length, e * Q ≤ freshCount evs k := ⟨evs.length, le_rfl, hge⟩
  have hex2 : ∃ k ≤ (evs ++ extra).length, e * Q ≤ freshCount (evs ++ extra) k :=
    ⟨evs.length, hlen_le, by rwa [freshCount_append_left evs extra le_rfl]⟩
  unfold subStart
  rw [dite_eq_left hex2, dite_eq_left hex1]
  have h1_le : Nat.find hex1 ≤ evs.length := (Nat.find_spec hex1).1
  have h2_le : Nat.find hex2 ≤ Nat.find hex1 :=
    Nat.find_min' hex2 ⟨h1_le.trans hlen_le, by
      rw [freshCount_append_left evs extra h1_le]; exact (Nat.find_spec hex1).2⟩
  have h2_len : Nat.find hex2 ≤ evs.length := h2_le.trans h1_le
  have h1_le2 : Nat.find hex1 ≤ Nat.find hex2 :=
    Nat.find_min' hex1 ⟨h2_len, by
      rw [← freshCount_append_left evs extra h2_len]; exact (Nat.find_spec hex2).2⟩
  omega

theorem freshBatch_subset_append {U V : ℕ} (evs extra : List (EpochUpdate U V)) (Q e : ℕ) :
    freshBatch evs Q e ⊆ freshBatch (evs ++ extra) Q e := by
  classical
  intro u hu
  unfold freshBatch at hu ⊢
  obtain ⟨⟨i, hi⟩, hmem, rfl⟩ := Finset.mem_image.mp hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  refine Finset.mem_image.mpr ⟨⟨i, by simp; omega⟩, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [isFreshAt_append_left evs extra hi, freshCount_append_left evs extra hi.le]
    exact hmem
  · simp [List.getElem_append_left hi]

/-- Key prefix monotonicity: any `EpochWindowSpec` covering `evs ++ extra` covers `evs`! -/
theorem WindowCovers.of_append {c U V N : ℕ} {evs extra : List (EpochUpdate U V)}
    {win : EpochWindowSpec c U N} (hc : WindowCovers (evs ++ extra) win) :
    WindowCovers evs win := by
  set Q := qEpochWhp N
  have hQpos : 0 < Q := lt_of_lt_of_le (by decide) (four_le_qEpochWhp N)
  have hlen_le : evs.length ≤ (evs ++ extra).length := by simp
  have hfr_le : freshCount evs evs.length ≤ freshCount (evs ++ extra) (evs ++ extra).length := by
    rw [← freshCount_append_left evs extra le_rfl]
    exact freshCount_mono (evs ++ extra) hlen_le
  have hdiv_le : freshCount evs evs.length / Q ≤
      freshCount (evs ++ extra) (evs ++ extra).length / Q :=
    Nat.div_le_div_right hfr_le
  exact
    { len_lt := lt_of_le_of_lt hlen_le hc.len_lt
      sub_lt := lt_of_le_of_lt hdiv_le hc.sub_lt
      snaps_cov := fun t ht => by
        have htk : (evs ++ extra).take t.val = evs.take t.val :=
          List.take_append_of_le_length ht
        simpa only [htk] using hc.snaps_cov t (ht.trans hlen_le)
      unions_cov := fun e he => by
        have hge : e.val * Q ≤ freshCount evs evs.length := by
          calc e.val * Q ≤ (freshCount evs evs.length / Q) * Q := Nat.mul_le_mul_right Q he
            _ ≤ freshCount evs evs.length := by
              rw [Nat.mul_comm]; exact Nat.mul_div_le _ _
        have hss := subStart_append_left evs extra hge
        have hss_le : subStart evs Q e.val ≤ evs.length := by
          classical
          unfold subStart
          have hex : ∃ k ≤ evs.length, e.val * Q ≤ freshCount evs k :=
            ⟨evs.length, le_rfl, hge⟩
          rw [dite_eq_left hex]; exact (Nat.find_spec hex).1
        have htake : (evs ++ extra).take (subStart (evs ++ extra) Q e.val) =
            evs.take (subStart evs Q e.val) := by
          rw [hss]; exact List.take_append_of_le_length hss_le
        have hsub := hc.unions_cov e (he.trans hdiv_le)
        refine Finset.union_subset ?_ ?_
        · rw [← htake]; exact Finset.Subset.trans Finset.subset_union_left hsub
        · exact (freshBatch_subset_append evs extra Q e.val).trans
            (Finset.Subset.trans Finset.subset_union_right hsub)
      batches_cov := fun e he0 he =>
        (freshBatch_subset_append evs extra Q (e.val - 1)).trans
          (hc.batches_cov e he0 (he.trans hdiv_le)) }

/-- The canonical window `windowOfEvents hth evs hlen hcard` covers `evs`. -/
theorem windowCovers_windowOfEvents {c U V N : ℕ}
    (hth : whpThreshold c ≤ N) (evs : List (EpochUpdate U V))
    (hlen : evs.length ≤ 4 * N)
    (hcard : ∀ k ≤ evs.length, (liveDom (EpochUpdate.eval (evs.take k))).card ≤ N) :
    WindowCovers evs (windowOfEvents hth evs hlen hcard) := by
  have hfr_le : freshCount evs evs.length ≤ evs.length := freshCount_le evs evs.length
  have hdiv : freshCount evs evs.length / qEpochWhp N ≤ evs.length / qEpochWhp N :=
    Nat.div_le_div_right hfr_le
  exact
    { len_lt := by simp [windowOfEvents]
      sub_lt := by simp [windowOfEvents]; omega
      snaps_cov := fun t _ => by simp [windowOfEvents]
      unions_cov := fun e _ => by
        change liveDom (EpochUpdate.eval (evs.take (subStart evs (qEpochWhp N) e.val))) ∪
          freshBatch evs (qEpochWhp N) e.val ⊆
          liveDom (EpochUpdate.eval (evs.take (subStart evs (qEpochWhp N) e.val))) ∪
            freshBatch evs (qEpochWhp N) e.val ∪ _
        exact Finset.subset_union_left
      batches_cov := fun e he0 _ => by
        change freshBatch evs (qEpochWhp N) (e.val - 1) ⊆
          if e.val = 0 then ∅ else freshBatch evs (qEpochWhp N) (e.val - 1)
        rw [ite_eq_right (Nat.pos_iff_ne_zero.mp he0)] }

/-- Prefix-indexed current-buffer key batch `curBatch evs` for `CurBufKeysIn`. -/
@[expose] noncomputable def curBatchAt {U V : ℕ} (Q : ℕ) (evs : List (EpochUpdate U V)) :
    Finset (Fin U) :=
  freshBatch evs Q (freshCount evs evs.length / Q)

/-- Conditional fast-mode invariant quantified over every `EpochWindowSpec` covering `evs`.
Stays closed under every `insert` (`fastInsertProg_good`), `delete` (`fastDeleteProg_good`),
and `SlotIoLayout` mode switch (`transfer_io`). -/
@[expose] def GoodEpochAt (fl : FastEpochLayout) (slack : ℕ)
    (seeds : EpochHashSeeds fl.c fl.U fl.N) (evs : List (EpochUpdate fl.U fl.V))
    (mem : ℕ → ℕ) : Prop :=
  ∀ (win : EpochWindowSpec fl.c fl.U fl.N) (hgood : GoodEpochSeeds win seeds)
    (hcov : WindowCovers evs win),
    let Q := qEpochWhp fl.N
    let e : Fin win.numSubs := ⟨freshCount evs evs.length / Q, hcov.sub_lt⟩
    mem (fl.metaBase + 2) = 0 ∧
    (extractFastMeta fl mem).subStep = freshCount evs evs.length % Q ∧
    FastSubEpochGood 0 0 slack win e seeds hgood mem (EpochUpdate.eval evs) ∧
    CurBufKeysIn (fl := fl) seeds mem (curBatchAt Q evs)

/-! ## Section 5: Deterministic Dual-Epoch Batch Sizes and Rebuild Budgets -/

/-- Uniform bulk word-batch size (`1024` words/op for `growZero`/`zeroMeta`/`randFill`/`initDir`).
-/
@[expose] def bulkBatchWhp : ℕ := 1024

/-- Slide (`slideUp`/`slideDown`), migrate (`popAny → insert`), and `unperm` batch size (`1024`).
-/
@[expose] def itemBatchWhp : ℕ := 1024

/-- Tail-directory init batch size (`128` entries/op → `≤ pgB / 16 + 1` ticks!). -/
@[expose] def tailBatchWhp : ℕ := 128

/-- Auxiliary `Nat.log 2 N + 2 ≤ N / 1024` for every `N ≥ 2 ^ 20` (so `whpThreshold c ≤ N`). -/
theorem log_add_two_le_div_1024 {N : ℕ} (hN : 2 ^ 20 ≤ N) :
    Nat.log 2 N + 2 ≤ N / 1024 := by
  have h1 : ∀ k : ℕ, 20 ≤ k → 1024 * (k + 2) ≤ 2 ^ k := by
    intro k hk
    obtain ⟨d, rfl⟩ : ∃ d, k = d + 20 := ⟨k - 20, by omega⟩
    induction d with
    | zero => decide
    | succ d ih =>
      rw [show d + 1 + 20 = (d + 20) + 1 by omega, Nat.pow_succ]
      have : 1024 ≤ 2 ^ (d + 20) := by
        calc 1024 ≤ 1024 * (d + 20 + 2) := Nat.le_mul_of_pos_right _ (by omega)
          _ ≤ 2 ^ (d + 20) := ih (by omega)
      have := ih (by omega)
      omega
  have hk_ge : 20 ≤ Nat.log 2 N := (Nat.le_log_iff_pow_le Nat.one_lt_two (by omega)).mpr hN
  have hpow : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hm := (h1 _ hk_ge).trans hpow
  omega

/-! ## Section 6: Deterministic Dual-Epoch Hysteresis and Trigger Rules -/

/-- Deterministic resting-to-rebuild target capacity rule (depends ONLY on `c, U, nSrc, nLive,
epochOps` — completely independent of every hash seed). Returns `some nDst` when starting a new
rebuild (`nDst = 0` = small target; `whpThreshold c ≤ nDst ≤ U` = large target). -/
@[expose] def dualTriggerCap (c U nSrc nLive epochOps : ℕ) : Option ℕ :=
  if nSrc = 0 then
    if whpThreshold c ≤ U ∧ whpThreshold c ≤ nLive then
      some (min (2 * nLive) U)
    else
      none
  else if nSrc < U ∧ 3 * nSrc ≤ 4 * nLive then
    some (min (2 * nLive) U)
  else if 5 * nLive ≤ 2 * nSrc then
    if 2 * nLive < whpThreshold c then some 0 else some (min (2 * nLive) U)
  else if nSrc ≤ 4 * epochOps then
    some nSrc
  else
    none

/-- Resting numerical invariant on `(nSrc, nLive)` right upon entering or resting in `idle`
(strictly strong enough to tolerate back-to-back rebuild drift of `±max T nSrc / 16`). -/
@[expose] def DualIdleSafe (c U nSrc nLive : ℕ) : Prop :=
  if nSrc = 0 then
    nLive ≤ U ∧ nLive < whpThreshold c + 1
  else
    whpThreshold c ≤ nSrc ∧ nSrc ≤ U ∧ nLive ≤ U ∧
    27 * nSrc ≤ 80 * nLive ∧
    (nSrc < U → 16 * nLive ≤ 13 * nSrc)

/-- Slightly wider precondition just before checking `dualTriggerCap` after a single `±1` step
from `DualIdleSafe`. -/
@[expose] def DualPostUpdateSafe (c U nSrc nLive : ℕ) : Prop :=
  if nSrc = 0 then
    nLive ≤ U ∧ nLive ≤ whpThreshold c
  else
    whpThreshold c ≤ nSrc ∧ nSrc ≤ U ∧ nLive ≤ U ∧
    27 * nSrc ≤ 80 * nLive + 80 ∧
    (nSrc < U → 16 * nLive ≤ 13 * nSrc + 16)

theorem whpThreshold_ge_pow20 (c : ℕ) : 2 ^ 20 ≤ whpThreshold c := by
  have hb := le_bMinWhp c
  rw [whpThreshold_eq]
  exact Nat.pow_le_pow_right (by decide) (by omega)

theorem dualIdleSafe_empty (c U : ℕ) : DualIdleSafe c U 0 0 := by
  unfold DualIdleSafe
  rw [ite_eq_left rfl]
  exact ⟨Nat.zero_le U, by have := whpThreshold_pos c; omega⟩

theorem dualIdleSafe_to_epochCapSafe {c U nSrc nLive : ℕ} (h : DualIdleSafe c U nSrc nLive) :
    EpochCapSafe (whpThreshold c) U nSrc nLive := by
  by_cases h0 : nSrc = 0
  · subst h0
    simp only [DualIdleSafe, EpochCapSafe, ↓reduceIte] at h ⊢
    have := whpThreshold_ge_pow20 c
    exact ⟨by omega, h.1⟩
  · simp only [DualIdleSafe, h0, EpochCapSafe, ↓reduceIte] at h ⊢
    obtain ⟨hth, hNU, hnU, hlo, hhi⟩ := h
    have hth_big := whpThreshold_ge_pow20 c
    refine ⟨hth, hNU, by omega, ?_⟩
    by_cases hlt : nSrc < U
    · have := hhi hlt; omega
    · omega

theorem dualIdleSafe_post_no_trigger {c U nSrc nLive epochOps nNext : ℕ}
    (h : DualIdleSafe c U nSrc nLive) (hstep : nNext ≤ nLive + 1 ∧ nLive ≤ nNext + 1)
    (hnextU : nNext ≤ U)
    (hno : dualTriggerCap c U nSrc nNext epochOps = none) :
    DualIdleSafe c U nSrc nNext := by
  by_cases h0 : nSrc = 0
  · subst h0
    simp only [DualIdleSafe, ↓reduceIte] at h ⊢
    refine ⟨hnextU, ?_⟩
    unfold dualTriggerCap at hno
    simp only [↓reduceIte] at hno
    by_cases hU : whpThreshold c ≤ U
    · by_cases hn : whpThreshold c ≤ nNext
      · simp [hU, hn] at hno
      · omega
    · omega
  · simp only [DualIdleSafe, h0, ↓reduceIte] at h ⊢
    obtain ⟨hth, hNU, _, _, _⟩ := h
    unfold dualTriggerCap at hno
    simp only [h0, ↓reduceIte] at hno
    by_cases hg : nSrc < U ∧ 3 * nSrc ≤ 4 * nNext
    · simp [hg] at hno
    · simp only [hg, ↓reduceIte] at hno
      by_cases hs : 5 * nNext ≤ 2 * nSrc
      · rw [ite_eq_left hs] at hno
        split_ifs at hno
      · refine ⟨hth, hNU, hnextU, by omega, fun hlt => by
          have : ¬(3 * nSrc ≤ 4 * nNext) := fun hh => hg ⟨hlt, hh⟩
          omega⟩

theorem dualPostUpdateSafe_of_idle {c U nSrc nLive nNext : ℕ}
    (h : DualIdleSafe c U nSrc nLive) (hno : dualTriggerCap c U nSrc nLive 0 = none ∨ nSrc ≠ 0)
    (hstep : nNext ≤ nLive + 1 ∧ nLive ≤ nNext + 1) (hnextU : nNext ≤ U) :
    DualPostUpdateSafe c U nSrc nNext := by
  by_cases h0 : nSrc = 0
  · subst h0
    simp only [DualIdleSafe, DualPostUpdateSafe, ↓reduceIte] at h ⊢
    refine ⟨hnextU, ?_⟩
    rcases hno with ht | hne
    · unfold dualTriggerCap at ht
      simp only [↓reduceIte] at ht
      by_cases hU : whpThreshold c ≤ U
      · by_cases hn : whpThreshold c ≤ nLive
        · simp [hU, hn] at ht
        · omega
      · omega
    · exact absurd rfl hne
  · simp only [DualIdleSafe, DualPostUpdateSafe, h0, ↓reduceIte] at h ⊢
    obtain ⟨hth, hNU, _, hlo, hhi⟩ := h
    refine ⟨hth, hNU, hnextU, by omega, fun hlt => by have := hhi hlt; omega⟩

/-- Active rebuild drift theorem: whenever `dualTriggerCap c U nSrc nTrig epochOps = some nDst`
fires from `DualPostUpdateSafe c U nSrc nTrig`, **throughout** every `nCur` within drift
`d ≤ max (whpThreshold c) nSrc / 16` (`nCur ≤ nTrig + d`, `nTrig ≤ nCur + d`, `nCur ≤ U`):
1. `nDst ≤ 2 * max (whpThreshold c) nSrc` (matches `total_rebuild_ticks_le_div16`).
2. `EpochCapSafe (whpThreshold c) U nSrc nCur` (`src` is `1 · OPT` & capacity-safe!).
3. `EpochCapSafe (whpThreshold c) U nDst nCur` (`dst` is `1 · OPT` & capacity-safe!).
4. `DualIdleSafe c U nDst nCur` (landing back in `idle` satisfies the exact inductive invariant!).
-/
theorem active_rebuild_safe {c U nSrc nTrig epochOps nDst nCur d : ℕ}
    (hpost : DualPostUpdateSafe c U nSrc nTrig)
    (htrig : dualTriggerCap c U nSrc nTrig epochOps = some nDst)
    (hdrift_hi : nCur ≤ nTrig + d) (hdrift_lo : nTrig ≤ nCur + d)
    (hd_le : 16 * d ≤ max (whpThreshold c) nSrc) (hcurU : nCur ≤ U) :
    nDst ≤ 2 * max (whpThreshold c) nSrc ∧
    EpochCapSafe (whpThreshold c) U nSrc nCur ∧
    EpochCapSafe (whpThreshold c) U nDst nCur ∧
    DualIdleSafe c U nDst nCur := by
  have hth_100 : 1000 ≤ whpThreshold c := by
    have h3 : 10 ≤ bMinWhp c := (by decide : 10 ≤ 6553600).trans (le_bMinWhp c)
    have h4 : 2 ^ 10 ≤ 2 ^ bMinWhp c := Nat.pow_le_pow_right (by decide) h3
    rw [whpThreshold_eq]
    omega
  by_cases h0 : nSrc = 0
  · subst h0
    simp only [DualPostUpdateSafe, ↓reduceIte] at hpost
    unfold dualTriggerCap at htrig
    simp only [↓reduceIte] at htrig
    by_cases hok : whpThreshold c ≤ U ∧ whpThreshold c ≤ nTrig
    · rw [ite_eq_left hok, Option.some.injEq] at htrig
      subst htrig
      have hnt_eq : nTrig = whpThreshold c := by omega
      have hmax : max (whpThreshold c) 0 = whpThreshold c := max_eq_left (Nat.zero_le _)
      rw [hmax] at hd_le ⊢
      have hdst_pos : min (2 * nTrig) U ≠ 0 := by omega
      refine ⟨by omega, ?_, ?_, ?_⟩
      · simp only [EpochCapSafe, ↓reduceIte]; exact ⟨by omega, hcurU⟩
      · simp only [EpochCapSafe, hdst_pos, ↓reduceIte]
        refine ⟨by omega, min_le_right _ _, by omega, ?_⟩
        exact le_min (by omega) hcurU
      · simp only [DualIdleSafe, hdst_pos, ↓reduceIte]
        refine ⟨by omega, min_le_right _ _, hcurU, by omega, fun hlt => ?_⟩
        have hmin_eq : min (2 * nTrig) U = 2 * nTrig := by omega
        omega
    · rw [ite_eq_right hok] at htrig; cases htrig
  · simp only [DualPostUpdateSafe, h0, ↓reduceIte] at hpost
    obtain ⟨hth, hNU, htrigU, hlo, hhi⟩ := hpost
    have hmax : max (whpThreshold c) nSrc = nSrc := max_eq_right hth
    rw [hmax] at hd_le ⊢
    unfold dualTriggerCap at htrig
    simp only [h0, ↓reduceIte] at htrig
    have hsrc_safe : EpochCapSafe (whpThreshold c) U nSrc nCur := by
      simp only [EpochCapSafe, h0, ↓reduceIte]
      refine ⟨hth, hNU, by omega, ?_⟩
      by_cases hlt : nSrc < U
      · have := hhi hlt; omega
      · omega
    by_cases hg : nSrc < U ∧ 3 * nSrc ≤ 4 * nTrig
    · rw [ite_eq_left hg] at htrig
      injection htrig with hd_eq; subst hd_eq
      have hhi_t := hhi hg.1
      have hdst_ne : min (2 * nTrig) U ≠ 0 := by omega
      refine ⟨by omega, hsrc_safe, ?_, ?_⟩
      · simp only [EpochCapSafe, hdst_ne, ↓reduceIte]
        exact ⟨by omega, min_le_right _ _, by omega, le_min (by omega) hcurU⟩
      · simp only [DualIdleSafe, hdst_ne, ↓reduceIte]
        exact ⟨by omega, min_le_right _ _, hcurU, by omega, fun hlt => by
          have : min (2 * nTrig) U = 2 * nTrig := by omega
          omega⟩
    · rw [ite_eq_right hg] at htrig
      by_cases hs : 5 * nTrig ≤ 2 * nSrc
      · rw [ite_eq_left hs] at htrig
        by_cases hsm : 2 * nTrig < whpThreshold c
        · rw [ite_eq_left hsm] at htrig
          injection htrig with hd_eq; subst hd_eq
          refine ⟨by omega, hsrc_safe, ?_, ?_⟩
          · simp only [EpochCapSafe, ↓reduceIte]; exact ⟨by omega, hcurU⟩
          · simp only [DualIdleSafe, ↓reduceIte]; exact ⟨hcurU, by omega⟩
        · rw [ite_eq_right hsm] at htrig
          injection htrig with hd_eq; subst hd_eq
          have hdst_eq : min (2 * nTrig) U = 2 * nTrig := min_eq_left (by omega)
          have hdst_ne : min (2 * nTrig) U ≠ 0 := by omega
          refine ⟨by omega, hsrc_safe, ?_, ?_⟩
          · simp only [EpochCapSafe, hdst_ne, ↓reduceIte]
            exact ⟨by omega, by omega, by omega, by omega⟩
          · simp only [DualIdleSafe, hdst_ne, ↓reduceIte]
            exact ⟨by omega, by omega, hcurU, by omega, fun _ => by omega⟩
      · rw [ite_eq_right hs] at htrig
        by_cases href : nSrc ≤ 4 * epochOps
        · rw [ite_eq_left href] at htrig
          injection htrig with hd_eq; subst hd_eq
          refine ⟨by omega, hsrc_safe, hsrc_safe, ?_⟩
          simp only [DualIdleSafe, h0, ↓reduceIte]
          refine ⟨hth, hNU, hcurU, by omega, fun hlt => ?_⟩
          have : ¬(3 * nSrc ≤ 4 * nTrig) := fun hh => hg ⟨hlt, hh⟩
          omega
        · rw [ite_eq_right href] at htrig; cases htrig

/-- Guaranteed migration batch bound: `nLive ≤ max (whpThreshold c) nSrc`, so `tMig` fixed
deterministic ticks drain EVERY item from `src` (`itemBatchWhp = 1024` pops/tick), regardless of
the pop order or hash seeds. -/
theorem migrate_ticks_drain_all {nStart tMig : ℕ} (h : nStart ≤ tMig * itemBatchWhp) :
    nStart - tMig * itemBatchWhp = 0 := by omega

/-- Event-length bound for ANY large epoch (`N > 0`): starting empty (`evs = []`), a full
`migrate` inserts at most `n_init + tMig` keys, plus `tUnp + tSlide` updates while settling, plus
`epochOps ≤ N / 4` updates while idle, plus `W_next` deletes. Total length stays `≤ 4 * N`. -/
theorem large_epoch_evs_len_le {N nInit wMig wIdle wNext : ℕ}
    (hn : nInit ≤ N) (hm : 8 * wMig ≤ N) (hi : 4 * wIdle ≤ N) (hw : 8 * wNext ≤ N) :
    nInit + wMig + wIdle + wNext ≤ 4 * N := by omega

/-- Two-epoch failure-probability union bound (`(1/2) * N_old^(-c) + (1/2) * N_new^(-c) ≤
(max n_t (whpThreshold c))^(-c)`). -/
theorem two_epoch_fail_sum_le {c U nOld nNew n_t : ℕ}
    (hOld : 0 < nOld → EpochCapSafe (whpThreshold c) U nOld n_t)
    (hNew : 0 < nNew → EpochCapSafe (whpThreshold c) U nNew n_t) :
    (if 0 < nOld then ((1 : ENNReal) / 2) * ((nOld : ENNReal)⁻¹ ^ c) else 0) +
      (if 0 < nNew then ((1 : ENNReal) / 2) * ((nNew : ENNReal)⁻¹ ^ c) else 0) ≤
      (((max n_t (whpThreshold c) : ℕ) : ENNReal)⁻¹ ^ c) := by
  set p := (((max n_t (whpThreshold c) : ℕ) : ENNReal)⁻¹ ^ c)
  have h1 : (if 0 < nOld then ((1 : ENNReal) / 2) * ((nOld : ENNReal)⁻¹ ^ c) else 0) ≤
      ((1 : ENNReal) / 2) * p := by
    by_cases h : 0 < nOld
    · rw [ite_eq_left h]; exact epochFail_le_half_max_inv_pow h (hOld h)
    · rw [ite_eq_right h]; exact zero_le
  have h2 : (if 0 < nNew then ((1 : ENNReal) / 2) * ((nNew : ENNReal)⁻¹ ^ c) else 0) ≤
      ((1 : ENNReal) / 2) * p := by
    by_cases h : 0 < nNew
    · rw [ite_eq_left h]; exact epochFail_le_half_max_inv_pow h (hNew h)
    · rw [ite_eq_right h]; exact zero_le
  have hhalf : ((1 : ENNReal) / 2) * p + ((1 : ENNReal) / 2) * p = p := by
    rw [← add_mul, ENNReal.add_halves, one_mul]
  exact (add_le_add h1 h2).trans hhalf.le

/-- Exact worst-case `1 · OPT` padded target frontier above `base` across every phase of a
rebuild `(nSrc, nDst)` at current live count `n_t`. -/
@[expose] def dualPaddedWords (c U V w nSrc nDst n_t : ℕ) : ℕ :=
  rootHdrWhp + max (epochMetaWordsWhp c w nSrc) (epochMetaWordsWhp c w nDst) +
    epochMetaWordsWhp c w nDst + 16 +
    packedWords n_t (max (epochItemBitsWhp c U V nSrc) (epochItemBitsWhp c U V nDst)) w

theorem dualPaddedWords_le_succinctWords {c U V w nSrc nDst n_t : ℕ}
    (hsrc : EpochCapSafe (whpThreshold c) U nSrc n_t)
    (hdst : EpochCapSafe (whpThreshold c) U nDst n_t) :
    dualPaddedWords c U V w nSrc nDst n_t ≤
      Dynamic.succinctWords (whpResizableSpaceFactor c) whpResizableSpaceConst U V w n_t :=
  dualEpochPaddedWords_le_succinctWords hsrc hdst

/-- Overflow-free upper bound on deterministic unperm ticks to reach `cleanPhase = 4` after
`migrate` ends (`unpermRank ≤ 4 * nRef + 66 * pgB + 512`, dropping by `itemBatchWhp - 64 = 960`
per tick). -/
@[expose] def calcUnpermTicks (nRef pgB : ℕ) : ℕ :=
  nRef / 240 + pgB / 8 + 4

theorem unperm_rank_reaches_zero {nRef pgB r₀ : ℕ}
    (hr : r₀ ≤ 4 * nRef + 66 * pgB + 512) :
    r₀ - calcUnpermTicks nRef pgB * (itemBatchWhp - 64) = 0 := by
  unfold calcUnpermTicks itemBatchWhp
  have hd1 := Nat.div_add_mod nRef 240
  have hd2 := Nat.div_add_mod pgB 8
  omega

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp
