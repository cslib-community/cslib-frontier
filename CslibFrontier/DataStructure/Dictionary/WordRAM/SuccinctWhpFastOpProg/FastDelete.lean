/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg.DelRemove
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg.DelMoveLast
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg.DelShrink
import CslibFrontier.Tactic.Realize

/-!
# Fast-Mode Deletion (`fastDeleteGenProg`)

Worst-case `O_c(1)` parameter-free fast-mode deletion program and `FastStateStep` realization
proof combining `fastDeleteRemove`, `fastDeleteMoveLast`, `fastDeleteShrink`, and `overmarsStep`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fastDeleteGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_fastDeleteGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fastDeleteGenProg_fastStep`
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.Dynamic (logLogFactor one_le_logLogFactor)
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

attribute [local simp] clientResult_pure_whp clientState_pure_whp

private theorem poolFreeTop_lt_of_backyard_active {c U V n_max b loc_last : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U}
    (hv : ValidFastState c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max)
    (hcnt : fs.bktCount b = loc_last + 1)
    (hcf : capFrontWhp n_max ≤ loc_last) :
    fs.backPtr b (loc_last - capFrontWhp n_max) < poolSizeWhp n_max ∧
    fs.poolFreeTop < poolSizeWhp n_max := by
  have hbp := (hv.backPtr_valid b hb (loc_last - capFrontWhp n_max) (by omega)).1
  have hpc := hv.pool_conservation
  have hle_sum : fs.bktCount b - capFrontWhp n_max ≤
      ∑ b' ∈ Finset.range (numBucketsWhp n_max), (fs.bktCount b' - capFrontWhp n_max) :=
    Finset.single_le_sum (f := fun b' => fs.bktCount b' - capFrontWhp n_max)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hb)
  exact ⟨hbp, by omega⟩

/-- Optional `fastDeleteMoveLast` wrapper (`if loc_del < loc_last`). -/
@[irreducible] private def fastDeleteOptMoveGenProg :
    (((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((((wp, base), b), (loc_del, loc_last)), rebAct) =>
    if loc_del < loc_last then
      fastDeleteMoveLastGenProg ((((wp, base), b), (loc_del, loc_last)), rebAct)
    else
      pure ()

private theorem realizes_fastDeleteOptMoveGen :
    Realizes .exact fastDeleteOptMoveGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((wp, base), b), (loc_del, loc_last)), rebAct) s =>
        loc_del < loc_last →
          FastDelMoveLastPre w ((((wp, base), b), (loc_del, loc_last)), rebAct) s)
      (fun _ _ => 0) := by
  unfold fastDeleteOptMoveGenProg
  have hdm := realizes_fastDeleteMoveLastGen
  realize
  rcases d with ⟨⟨⟨⟨wp, base⟩, b⟩, ⟨loc_del, loc_last⟩⟩, rebAct⟩
  exact h (by assumption)

/-- Read `(bktCount b - 1, rebActiveB)` for `fastDeleteHitGenProg` (`d = ((cp, base), b)`). -/
@[irreducible] private def delHitPrepGenProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((cp, base), b) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let cnt ← readBktFieldGenProg (((cp, base), b), z0)
    let loc_last ← pure (cnt - z1)
    let rebAct ← readRebActiveBGenProg ((cp, base), b)
    pure (loc_last, rebAct)

private theorem realizes_delHitPrepGen :
    Realizes .exact delHitPrepGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((cp, base), b) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          1 ≤ fs.bktCount b)
      (fun _ _ => 0) := by
  unfold delHitPrepGenProg
  have hrb := realizes_readBktFieldGen
  have hra := realizes_readRebActiveBGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hcnt1⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hdc_mem : s.mem (base + hdrDirtyCount) ≤ qEpochWhp n_max :=
      hrep.2.2.2.2.2.2.2.1.trans_le hrep.1
    obtain ⟨hc0_st, hc0_res, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 0 < 10) hrep (s := s)
    simp only [getBktField] at hc0_res
    obtain ⟨hra_st, _, _, _⟩ := readRebActiveBGenProg_spec henv hrep (b := b) (s := s)
    simp only [hc0_st, hc0_res, hra_st, wp_large_M hth, wp_large_qEpoch hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | omega
  )

/-- Hit branch of `fastDeleteBodyGenProg` once `fastFindLoc = some loc_del`
(`d = ((((wp, base), b), loc_del), u_val)`). -/
@[irreducible] private def fastDeleteHitGenProg :
    (((WhpParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((wp, base), b), loc_del), u_val) => do
    let prep ← delHitPrepGenProg ((wp.1, base), b)
    fastDeleteRemoveGenProg ((((wp, base), b), loc_del), u_val)
    fastDeleteOptMoveGenProg ((((wp, base), b), (loc_del, prep.1)), prep.2)
    fastDeleteShrinkGenProg (((wp.1, base), b), prep.1)

private theorem realizes_fastDeleteHitGen :
    Realizes .exact fastDeleteHitGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((wp, base), b), loc_del), u_val) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          b < numBucketsWhp n_max ∧
          loc_del < fs.bktCount b ∧
          u_val < U)
      (fun _ _ => 0) := by
  unfold fastDeleteHitGenProg
  have hdp := realizes_delHitPrepGen
  have hdr := realizes_fastDeleteRemoveGen
  have hdm := realizes_fastDeleteOptMoveGen
  have hds := realizes_fastDeleteShrinkGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨wp, base⟩, b⟩, loc_del⟩, u_val⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv, hb, hld, hu⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    set u : Fin U := ⟨u_val, hu⟩
    set loc_last := fs.bktCount b - 1
    have hcnt : fs.bktCount b = loc_last + 1 := by omega
    have hll_tl : loc_last < totalLocalCoordsWhp n_max :=
      (by omega : loc_last < fs.bktCount b).trans_le (hv.bktCount_le b hb)
    obtain ⟨hc0_st, hc0_res, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 0 < 10) hrep (s := s)
    simp only [getBktField] at hc0_res
    obtain ⟨hra_st, hra_res, _, _⟩ := readRebActiveBGenProg_spec henv hrep (b := b) (s := s)
    have hprep_st : (Memory.spec 0).clientState s
        (delHitPrepGenProg ((mkWhpCoreParams c U V w n_max, base), b)) = s := by
      unfold delHitPrepGenProg; simp only [pure_bind]
      rw [clientState_bind, hc0_st, hc0_res, clientState_bind, hra_st, hra_res]; rfl
    have hprep_res : (Memory.spec 0).clientResult s
        (delHitPrepGenProg ((mkWhpCoreParams c U V w n_max, base), b)) =
        (loc_last,
         if decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
           fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
           fs.rebCollision = 0) then 1 else 0) := by
      unfold delHitPrepGenProg; simp only [pure_bind]
      rw [clientResult_bind, hc0_st, hc0_res, clientResult_bind, hra_st, hra_res]; rfl
    obtain ⟨_, _, hdr_step⟩ :=
      fastDeleteRemoveGenProg_fastStep u henv hseed hrep hv hb hld (s := s)
    set s1 := (Memory.spec 0).clientState s
      (fastDeleteRemoveGenProg ((((mkWhpParams c U V w n_max, base), b), loc_del), u_val))
    rw [hcp_eq] at *
    try rw [hprep_st]
    try rw [hprep_res]
    first
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, by omega⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv, hb, hld, hu⟩
    | (dsimp only
       intro hlt_ll
       exact ⟨c, U, V, w, n_max, θ, fs, dict, u, henv, rfl, hv, hb, hcnt, hlt_ll, rfl,
         hdr_step.2.1, hdr_step.2.2.1⟩)
    | (dsimp only
       unfold fastDeleteOptMoveGenProg; dsimp only
       by_cases hlt_ll : loc_del < loc_last
       · rw [ite_eq_left hlt_ll]
         obtain ⟨_, _, hdm_step⟩ :=
           fastDeleteMoveLastGenProg_fastStep u henv hv hb hcnt hlt_ll
             hdr_step.2.1 hdr_step.2.2.1 (s := s1)
         exact ⟨c, U, V, w, n_max, θ, _, henv, rfl, hdm_step.2.1, hdm_step.2.2.1, hb, hll_tl,
           fun hcf => poolFreeTop_lt_of_backyard_active (fs := fs) hv hb hcnt hcf⟩
       · rw [ite_eq_right hlt_ll, clientState_pure_whp]
         exact ⟨c, U, V, w, n_max, θ, _, henv, rfl, hdr_step.2.1, hdr_step.2.2.1, hb, hll_tl,
           fun hcf => poolFreeTop_lt_of_backyard_active (fs := fs) hv hb hcnt hcf⟩)
  )

/-- A prefix `p` that leaves the state unchanged and returns `r` peels off `p >>= k`: the state,
result and validity of `p >>= k` are those of `k r`, and its cost is that of `p` plus `k r`. -/
private theorem bind_of_readOnly {α : Type} {w F : ℕ} {s : Memory.State} {p : Memory.Prog α}
    {r : α} (hst : (Memory.spec 0).clientState s p = s)
    (hres : (Memory.spec 0).clientResult s p = r) (hvp : ValidProg w F s p) :
    ∀ (β : Type) (k : α → Memory.Prog β),
    (Memory.spec 0).clientState s (p >>= k) = (Memory.spec 0).clientState s (k r) ∧
    (Memory.spec 0).clientResult s (p >>= k) = (Memory.spec 0).clientResult s (k r) ∧
    memoryCost (p >>= k) s = memoryCost p s + memoryCost (k r) s ∧
    (ValidProg w F s (p >>= k) ↔ ValidProg w F s (k r)) := fun _ k => by
  refine ⟨by rw [clientState_bind, hst, hres], by rw [clientResult_bind, hst, hres],
    by rw [memoryCost_bind', hst, hres], fun h hm => ?_, fun h => validProg_bind hvp ?_⟩
  · have := ((validHistory_bind' w p k s).1 (h hm)).2
    rwa [hst, hres] at this
  · rwa [hst, hres]

private theorem fastDeleteHitGenProg_fastStep {c U V w n_max base loc_del : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (u : Fin U)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict)
    (hld : loc_del < fs.bktCount (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val))
    (hq_del : fs.quotArr (fs.physSlot n_max
      (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val) loc_del) =
      keyQuotient (bWhp n_max) u.val) :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let loc_last := fs.bktCount b - 1
    let rebActiveB : Bool :=
      decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
        fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
        fs.rebCollision = 0)
    let fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
    let fs2 :=
      if loc_del < loc_last then
        fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1
      else fs1
    let fsAfterDel := fastDeleteShrink n_max b loc_last fs2
    let prog := fastDeleteHitGenProg ((((mkWhpParams c U V w n_max, base), b), loc_del), u.val)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 22 * cTabWhp c + 7 * hashEvalCostWhp c + 6371 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fsAfterDel s s' ∧
    OvermarsBucketStepBounds U n_max b fsAfterDel := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
  have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
  set loc_last := fs.bktCount b - 1
  have hcnt : fs.bktCount b = loc_last + 1 := by omega
  have hll_tl : loc_last < totalLocalCoordsWhp n_max :=
    (by omega : loc_last < fs.bktCount b).trans_le (hv.bktCount_le b hb)
  obtain ⟨hc0_st, hc0_res, hc0_mc, hc0_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 0 < 10) hrep (s := s)
  simp only [getBktField] at hc0_res
  obtain ⟨hra_st, hra_res, hra_mc, hra_vp⟩ :=
    readRebActiveBGenProg_spec henv hrep (b := b) (s := s)
  set rebActiveB : Bool := decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
      fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
      fs.rebCollision = 0)
  set rebAct := if rebActiveB then 1 else 0
  obtain ⟨hdr_mc, hdr_vp, hdr_step⟩ :=
    fastDeleteRemoveGenProg_fastStep u henv hseed hrep hv hb hld (s := s)
  set fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
  set s1 := (Memory.spec 0).clientState s
    (fastDeleteRemoveGenProg ((((mkWhpParams c U V w n_max, base), b), loc_del), u.val))
  dsimp only
  unfold fastDeleteHitGenProg delHitPrepGenProg fastDeleteOptMoveGenProg
  simp only [pure_bind, bind_assoc]
  have hC := bind_of_readOnly hc0_st hc0_res hc0_vp
  have hR := bind_of_readOnly hra_st hra_res hra_vp
  rw [hwp1, (hC _ _).1, (hC _ _).2.2.1, (hC _ _).2.2.2, hc0_mc, (hR _ _).1, (hR _ _).2.2.1,
    (hR _ _).2.2.2, clientState_bind, memoryCost_bind']
  by_cases hlt_ll : loc_del < fs.bktCount b - 1
  · have hlt_ll' : loc_del < loc_last := hlt_ll
    simp only [hlt_ll, ↓reduceIte]
    obtain ⟨hdm_mc, hdm_vp, hdm_step⟩ :=
      fastDeleteMoveLastGenProg_fastStep u henv hv hb hcnt hlt_ll' hdr_step.2.1 hdr_step.2.2.1
        (s := s1)
    set s2 := (Memory.spec 0).clientState s1
      (fastDeleteMoveLastGenProg
        ((((mkWhpParams c U V w n_max, base), b), (loc_del, loc_last)), rebAct))
    set fs2_rel := fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1
    obtain ⟨hds_mc, hds_vp, hds_step⟩ :=
      fastDeleteShrinkGenProg_fastStep (fs2 := fs2_rel) henv hb hll_tl
        (fun hcf => poolFreeTop_lt_of_backyard_active (fs := fs) hv hb hcnt hcf)
        hdm_step.2.1 hdm_step.2.2.1 (s := s2)
    obtain ⟨hc_rel, _, hom_rel, _⟩ := fastDelete_afterDel_reloc_spec hv u hld hq_del hlt_ll
    rw [clientState_bind, memoryCost_bind']
    refine ⟨?_, validProg_bind hdr_vp (validProg_bind hdm_vp hds_vp),
      (hdr_step.trans hdm_step).trans hds_step,
      OvermarsBucketStepBounds.of_core_and_pre hc_rel hb hom_rel⟩
    dsimp only [s1, s2, loc_last, rebAct, rebActiveB, b] at hra_mc hdr_mc hdm_mc hds_mc ⊢
    omega
  · simp only [hlt_ll, ↓reduceIte, pure_bind]
    obtain ⟨hds_mc, hds_vp, hds_step⟩ :=
      fastDeleteShrinkGenProg_fastStep (fs2 := fs1) henv hb hll_tl
        (fun hcf => poolFreeTop_lt_of_backyard_active (fs := fs) hv hb hcnt hcf)
        hdr_step.2.1 hdr_step.2.2.1 (s := s1)
    obtain ⟨hc_last, _, hom_last, _⟩ := fastDelete_afterDel_last_spec hv u hld hq_del hlt_ll
    refine ⟨?_, validProg_bind hdr_vp hds_vp, hdr_step.trans hds_step,
      OvermarsBucketStepBounds.of_core_and_pre hc_last hb hom_last⟩
    dsimp only [s1, loc_last, b] at hra_mc hdr_mc hds_mc ⊢
    omega

/-- Foreground body of `fastDelete` prior to `overmarsStep`
(`d = (((wp, base), bq), u_val)`). -/
@[irreducible] private def fastDeleteBodyGenProg :
    ((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | (((wp, base), bq), u_val) => do
    let z1 ← pure 1
    let fl ← fastFindLocBqGenProg (((wp, base), bq), u_val)
    if fl.1 = z1 then
      fastDeleteHitGenProg ((((wp, base), bq.1), fl.2), u_val)
    else
      pure ()

private theorem realizes_fastDeleteBodyGen :
    Realizes .exact fastDeleteBodyGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((wp, base), bq), u_val) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          u_val < U ∧
          bq = (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u_val,
                keyQuotient (bWhp n_max) u_val))
      (fun _ _ => 0) := by
  unfold fastDeleteBodyGenProg
  have hfl := realizes_fastFindLocBqGen
  have hhit := realizes_fastDeleteHitGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, ⟨b, q_val⟩⟩, u_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv, hu, hbq⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    rcases Prod.mk.inj hbq with ⟨rfl, rfl⟩
    set u : Fin U := ⟨u_val, hu⟩
    have hb : feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u_val < numBucketsWhp n_max :=
      feistelBucket_lt _ _ _
    obtain ⟨hfl_st, hfl_res, _, _⟩ := fastFindLocBqGenProg_spec henv hseed hrep hv u (s := s)
    dsimp only [u] at hfl_st hfl_res
    rw [hfl_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv⟩
    | (rw [hcp_eq, wp_large_M hth]; exact hb)
    | (have hspec := hv.fastFindLoc_spec u
       cases hfind : fastFindLoc c U n_max θ fs u with
       | none =>
         have hhit : ((Memory.spec 0).clientResult s
           (fastFindLocBqGenProg (((mkWhpParams c U V w n_max, base),
             (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u_val,
              keyQuotient (bWhp n_max) u_val)), u_val))).1 = 1 := by assumption
         rw [hfind] at hfl_res; rw [hfl_res] at hhit; cases hhit
       | some loc_del =>
         rw [hfind] at hfl_res hspec
         rw [hfl_res]; dsimp only
         exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv, hb, hspec.1, hu⟩)
  )

private theorem fastDeleteBodyGenProg_fastStep {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (u : Fin U)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict) :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let q_val := keyQuotient (bWhp n_max) u.val
    let fsAfterDel : FastState :=
      match fastFindLoc c U n_max θ fs u with
      | none => fs
      | some loc_del =>
        let loc_last := fs.bktCount b - 1
        let rebActiveB : Bool :=
          decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
            fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
            fs.rebCollision = 0)
        let fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
        let fs2 :=
          if loc_del < loc_last then
            fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1
          else fs1
        fastDeleteShrink n_max b loc_last fs2
    let prog := fastDeleteBodyGenProg (((mkWhpParams c U V w n_max, base), (b, q_val)), u.val)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 26 * cTabWhp c + 8 * hashEvalCostWhp c + 6675 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ fsAfterDel s s' ∧
    OvermarsBucketStepBounds U n_max b fsAfterDel := by
  set b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
  set q_val := keyQuotient (bWhp n_max) u.val
  have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
  obtain ⟨hfl_st, hfl_res, hfl_mc, hfl_vp⟩ :=
    fastFindLocBqGenProg_spec henv hseed hrep hv u (s := s)
  have hspec := hv.fastFindLoc_spec u
  dsimp only
  unfold fastDeleteBodyGenProg
  simp only [pure_bind]
  cases hfind : fastFindLoc c U n_max θ fs u with
  | none =>
    rw [hfind] at hfl_res
    dsimp only at hfl_res ⊢
    have hF := bind_of_readOnly hfl_st hfl_res hfl_vp
    rw [(hF _ _).1, (hF _ _).2.2.1, (hF _ _).2.2.2]
    simp only [zero_ne_one, ↓reduceIte, memoryCost_pure]
    refine ⟨?_, validProg_pure _, FastStateStep.refl hseed hrep,
      OvermarsBucketStepBounds.of_core_and_pre hv.toCore hb
        (OvermarsBucketInv.toPre (hv.overmars_valid b hb))⟩
    omega
  | some loc_del =>
    rw [hfind] at hfl_res hspec
    dsimp only at hfl_res ⊢
    obtain ⟨hld, hq_del⟩ := hspec
    obtain ⟨hhit_mc, hhit_vp, hhit_step, hhit_bnds⟩ :=
      fastDeleteHitGenProg_fastStep u henv hseed hrep hv hld hq_del (s := s)
    have hF := bind_of_readOnly hfl_st hfl_res hfl_vp
    rw [(hF _ _).1, (hF _ _).2.2.1, (hF _ _).2.2.2]
    simp only [↓reduceIte]
    refine ⟨?_, hhit_vp, hhit_step, hhit_bnds⟩
    dsimp only [b, q_val] at hfl_mc hhit_mc ⊢; omega

/-- Fast-mode deletion `fastDeleteGenProg` (`d = ((wp, base), u_val)`), refining `fastDelete` in
`O_c(1)` worst-case memory operations. -/
@[irreducible] def fastDeleteGenProg : (WhpParams × ℕ) × ℕ → Memory.Prog Unit
  | ((wp, base), u_val) => do
    let hrt ← mkHashRtGenProg (wp, base)
    let bq ← feistelSplitRtProg (hrt, u_val)
    fastDeleteBodyGenProg (((wp, base), bq), u_val)
    overmarsStepGenProg ((wp, base), bq.1)

theorem realizes_fastDeleteGen :
    Realizes .exact fastDeleteGenProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((wp, base), u_val) s => ValidFastMemPre w wp base s ∧ u_val < wpU wp.1)
      (fun _ _ => 0) := by
  unfold fastDeleteGenProg
  have hmh := realizes_mkHashRtGen
  have hfs := realizes_feistelSplitRt
  have hdb := realizes_fastDeleteBodyGen
  have hom := realizes_overmarsStepGen
  realize
  all_goals (
    rcases d with ⟨⟨wp, base⟩, u_val⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv⟩, hu_wp⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    have hu : u_val < U := by rw [hcp_eq, wp_large_U hth] at hu_wp; exact hu_wp
    set u : Fin U := ⟨u_val, hu⟩
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    obtain ⟨hfs_st, hfs_res, _, _⟩ :=
      feistelSplitRtProg_spec (u_val := u_val) henv hseed (s := s)
    obtain ⟨_, _, hdb_step, hdb_bnds⟩ :=
      fastDeleteBodyGenProg_fastStep u henv hseed hrep hv (s := s)
    dsimp only [u] at hdb_step hdb_bnds
    simp only [hmh_st, hmh_res, hfs_st, hfs_res] at *
    first
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv, hu, rfl⟩
    | exact ⟨c, U, V, w, n_max, θ, _, henv, rfl, hdb_step.2.1, hdb_step.2.2.1, hdb_bnds⟩
  )

theorem fastDeleteGenProg_fastStep {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict)
    (u : Fin U) :
    let prog := fastDeleteGenProg ((mkWhpParams c U V w n_max, base), u.val)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 26 * cTabWhp c + 41 * hashEvalCostWhp c + 46001 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (fastDelete c U n_max θ fs u) s s' := by
  have hth := henv.2.2.2.1
  obtain ⟨hmh_st, hmh_res, hmh_mc, hmh_vp⟩ :=
    mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hfs_st, hfs_res, hfs_mc, hfs_vp⟩ :=
    feistelSplitRtProg_spec (u_val := u.val) henv hseed (s := s)
  obtain ⟨hdb_mc, hdb_vp, hdb_step, hdb_bnds⟩ :=
    fastDeleteBodyGenProg_fastStep u henv hseed hrep hv (s := s)
  set bq := (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val,
             keyQuotient (bWhp n_max) u.val)
  set s1 := (Memory.spec 0).clientState s
    (fastDeleteBodyGenProg (((mkWhpParams c U V w n_max, base), bq), u.val))
  obtain ⟨hom_mc, hom_vp, hom_step⟩ :=
    overmarsStepGenProg_fastStep henv hdb_bnds hdb_step.2.1 hdb_step.2.2.1 (s := s1)
  have hM := bind_of_readOnly hmh_st hmh_res hmh_vp
  have hS := bind_of_readOnly hfs_st hfs_res hfs_vp
  dsimp only
  unfold fastDeleteGenProg fastDelete
  rw [(hM _ _).1, (hM _ _).2.2.1, (hM _ _).2.2.2, hmh_mc, (hS _ _).1, (hS _ _).2.2.1,
    (hS _ _).2.2.2, clientState_bind, memoryCost_bind']
  refine ⟨?_, validProg_bind hdb_vp hom_vp, hdb_step.trans hom_step⟩
  have hfs_mc' : memoryCost (feistelSplitRtProg (mkHashRt c U w n_max base, u.val)) s ≤
      hashEvalCostWhp c := hfs_mc
  dsimp only [s1, bq] at hdb_mc hom_mc ⊢
  omega

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
