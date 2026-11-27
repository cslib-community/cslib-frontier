/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpEpochTickProg.Internal.Common
import CslibFrontier.Tactic.Realize

/-!
# Rollover Pre-Check `checkEpochTickOkGenProg`

Implements and verifies the `O(1)` read-only rollover pre-check `checkEpochTickOkGenProg`
matching `epochTickWillSucceed n_max fs`, together with invariance of `epochTickWillSucceed`
across `fastInsert` and `fastDelete`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.EpochTickInternal

open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

attribute [local simp] clientResult_pure_whp clientState_pure_whp

private theorem overmarsScanSteps_tickFields {c U n_max : ℕ} (θ : SeedWhp c U n_max) (b : ℕ) :
    ∀ k (fs : FastState),
      let fs' := overmarsScanSteps c U n_max θ b k fs
      fs'.epochClock = fs.epochClock ∧
      fs'.rebStage = fs.rebStage ∧
      fs'.curEp = fs.curEp ∧
      fs'.buf = fs.buf
  | 0, _ => ⟨rfl, rfl, rfl, rfl⟩
  | k + 1, fs => by
    dsimp only [overmarsScanSteps]
    split_ifs <;> exact overmarsScanSteps_tickFields θ b k _

private theorem epochTickWillSucceed_eq_of_fields {n_max : ℕ} {fs₁ fs₂ : FastState}
    (h1 : fs₁.epochClock = fs₂.epochClock) (h2 : fs₁.rebStage = fs₂.rebStage)
    (_h3 : fs₁.curEp = fs₂.curEp) (h4 : fs₁.buf fs₁.oldEp = fs₂.buf fs₂.oldEp) :
    epochTickWillSucceed n_max fs₁ = epochTickWillSucceed n_max fs₂ := by
  unfold epochTickWillSucceed
  rw [h1, h2, h4]

private theorem overmarsStep_epochTickWillSucceed {c U n_max b : ℕ} (θ : SeedWhp c U n_max)
    (fs : FastState) :
    epochTickWillSucceed n_max (overmarsStep c U n_max θ b fs) = epochTickWillSucceed n_max fs := by
  have h :
      (overmarsStep c U n_max θ b fs).epochClock = fs.epochClock ∧
      (overmarsStep c U n_max θ b fs).rebStage = fs.rebStage ∧
      (overmarsStep c U n_max θ b fs).curEp = fs.curEp ∧
      (overmarsStep c U n_max θ b fs).buf = fs.buf := by
    unfold overmarsStep overmarsAfterActivate
    generalize (16 : ℕ) = k
    dsimp only
    split_ifs <;> first | exact overmarsScanSteps_tickFields θ b k _ | exact ⟨rfl, rfl, rfl, rfl⟩
  exact epochTickWillSucceed_eq_of_fields h.1 h.2.1 h.2.2.1
    (by unfold FastState.oldEp; rw [h.2.2.1, h.2.2.2])

/-- Successful `fastInsert` preserves `epochTickWillSucceed`. -/
theorem epochTickWillSucceed_fastInsert {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs fs1 : FastState} {dict : State U} (hv : ValidFastState c U V n_max θ fs dict)
    {u : Fin U} {v : ℕ} (hins : fastInsert c U n_max θ fs u v = some fs1) :
    epochTickWillSucceed n_max fs1 = epochTickWillSucceed n_max fs := by
  unfold fastInsert fastInsertAlloc fastInsertFresh at hins
  dsimp only at hins
  cases hfl : fastFindLoc c U n_max θ fs u <;> rw [hfl] at hins
  · have hne : 1 - fs.curEp ≠ fs.curEp := by
      rcases hv.curEp_or with h01 | h01 <;> simp [h01]
    split_ifs at hins <;> obtain ⟨rfl⟩ := hins <;>
      exact (overmarsStep_epochTickWillSucceed θ _).trans
        (epochTickWillSucceed_eq_of_fields rfl rfl rfl
          (by first | exact Function.update_of_ne hne _ _ | rfl))
  · exact Option.some.inj hins ▸ overmarsStep_epochTickWillSucceed θ _

private theorem buf_oldEp_ite_locState {α : Type*} {fs : FastState}
    (hce_or : fs.curEp = 0 ∨ fs.curEp = 1) {s : ℕ}
    (h1 : fs.oldEp = 1 → s ≠ 3) (h0 : fs.oldEp = 0 → s ≠ 2)
    (b2 b3 : α) (buf : ℕ → α) :
    (if s = 2 then Function.update buf 0 b2
     else if s = 3 then Function.update buf 1 b3
     else buf) fs.oldEp = buf fs.oldEp := by
  rcases hce_or with hce | hce <;> simp only [FastState.oldEp, hce] at h1 h0 ⊢
  all_goals
    split_ifs <;> first | rfl | exact absurd ‹_› (h1 trivial) | exact absurd ‹_› (h0 trivial)

/-- `fastDelete` preserves `epochTickWillSucceed`. -/
theorem epochTickWillSucceed_fastDelete {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hv : ValidFastState c U V n_max θ fs dict) (u : Fin U) :
    epochTickWillSucceed n_max (fastDelete c U n_max θ fs u) = epochTickWillSucceed n_max fs := by
  dsimp only [fastDelete]
  rw [overmarsStep_epochTickWillSucceed]
  cases hfl : fastFindLoc c U n_max θ fs u with
  | none => rfl
  | some loc_del =>
    dsimp only
    have hspec := hv.fastFindLoc_spec u
    rw [hfl] at hspec
    set b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
    set fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
    set fs2 := if loc_del < fs.bktCount b - 1 then
      fastDeleteMoveLast c U n_max θ b loc_del (fs.bktCount b - 1)
        (decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
          fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
          fs.rebCollision = 0)) fs1
      else fs1
    obtain ⟨hclk2, hstg2, hce2⟩ :
        (fastDeleteShrink n_max b (fs.bktCount b - 1) fs2).epochClock = fs.epochClock ∧
        (fastDeleteShrink n_max b (fs.bktCount b - 1) fs2).rebStage = fs.rebStage ∧
        (fastDeleteShrink n_max b (fs.bktCount b - 1) fs2).curEp = fs.curEp := by
      dsimp only [fastDeleteShrink, fs2, fs1]
      split_ifs <;> exact ⟨rfl, rfl, rfl⟩
    by_cases hs4 : fs.rebStage = 4
    · have hbo := hv.bufOld_valid
      rw [ite_eq_right (by omega : ¬(fs.rebStage ≤ 3)), ite_eq_left hs4] at hbo
      obtain ⟨hno_old, _, _⟩ := hbo
      have hrem_buf : fs1.buf fs.oldEp = fs.buf fs.oldEp :=
        buf_oldEp_ite_locState hv.curEp_or
          (fun ho => by simpa [ho] using hno_old b hb loc_del hspec.1)
          (fun ho => by simpa [ho] using hno_old b hb loc_del hspec.1) _ _ _
      have hmv_buf : fs2.buf fs.oldEp = fs.buf fs.oldEp := by
        dsimp only [fs2]
        split_ifs with hlt_l
        · have hne_l := hno_old b hb (fs.bktCount b - 1) (by omega)
          dsimp only [fastDeleteMoveLast]
          exact (buf_oldEp_ite_locState hv.curEp_or
            (fun ho => by rwa [ho] at hne_l)
            (fun ho => by rwa [ho] at hne_l) _ _ _).trans hrem_buf
        · exact hrem_buf
      refine epochTickWillSucceed_eq_of_fields hclk2 hstg2 hce2 ?_
      rwa [FastState.oldEp, hce2]
    · simp [epochTickWillSucceed, hclk2, hstg2, hs4]

/-- Read-only `O(1)` check returning `1` iff `epochTickWillSucceed n_max fs = true`
(`d = (cp, base)`). -/
@[irreducible] def checkEpochTickOkGenProg : WhpCoreParams × ℕ → Memory.Prog ℕ
  | (cp, base) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let z4 ← pure 4
    let z5 ← pure 5
    let c8 ← pure 8
    let clk ← readHdrProg (base, hdrEpochClock)
    let nextClk ← pure (clk + z1)
    let qEp ← pure (wpQEpoch cp)
    if nextClk < qEp then
      pure z1
    else
      let stg ← readHdrProg (base, hdrRebStage)
      if stg = z5 then
        pure z1
      else if stg = z4 then
        let oldEp ← readOldEpProg base
        let allocs ← readBufAllocsProg (base, oldEp)
        if allocs.1 ≤ c8 then
          pure z1
        else
          pure z0
      else
        pure z0

/-- `Realizes .exact` certificate for `checkEpochTickOkGenProg`. -/
theorem realizes_checkEpochTickOkGen :
    Realizes .exact checkEpochTickOkGenProg
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (cp, base) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          fs.epochClock < qEpochWhp n_max)
      (fun _ _ => 0) := by
  unfold checkEpochTickOkGenProg
  have hrh := realizes_readHdr
  have hro := realizes_readOldEp
  have hra := realizes_readBufAllocs
  realize
  all_goals (
    rcases d with ⟨cp, base⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hce_or, hclk_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hh := fastMemHdrs hrep
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hq_lt := (large_bounds_lt_n_max hth).2.2.2.2.2.2.1
    have hhdr (off) (hoff : base + off < base + largeSpaceWhp c U V w n_max) :=
      readHdrProg_spec (w := w) (F := base + largeSpaceWhp c U V w n_max) (base := base)
        (hdrOff := off) hoff (s := s)
    obtain ⟨hck_st, hck_res, _, _⟩ := hhdr hdrEpochClock (by dsimp [hdrEpochClock]; omega)
    obtain ⟨hst_st, hst_res, _, _⟩ := hhdr hdrRebStage (by dsimp [hdrRebStage]; omega)
    obtain ⟨hro_st, hro_res, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce_or
      hh.curEp (s := s)
    simp only [hck_st, hck_res, hst_st, hst_res, hro_st, hro_res, hh.epochClock, hh.rebStage] at *
    first
    | exact henv.two_le_w
    | exact henv.2.1
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by dsimp [hdrEpochClock, hdrRebStage, hdrCurEp]; omega)
    | exact henv.fits_largeSpace.of_le (by omega)
    | exact henv.fits_of_le_n_max (by omega)
  )

/-- Cost and result specification for `checkEpochTickOkGenProg`. -/
theorem checkEpochTickOkGenProg_spec {c U V w n_max base : ℕ}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce_or : fs.curEp = 0 ∨ fs.curEp = 1)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := checkEpochTickOkGenProg (mkWhpCoreParams c U V w n_max, base)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = (if epochTickWillSucceed n_max fs then 1 else 0) ∧
    memoryCost prog s ≤ 5 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hh := fastMemHdrs hrep
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
    rcases hce_or with h01 | h01 <;> simp [FastState.oldEp, h01]
  obtain ⟨hck_st, hck_res, hck_mc, hck_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrEpochClock)
    (by dsimp [hdrEpochClock]; omega) (s := s)
  rw [hh.epochClock] at hck_res
  let Spec (n : ℕ) (q : Memory.Prog ℕ) (r : ℕ) : Prop :=
    (Memory.spec 0).clientState s q = s ∧
    (Memory.spec 0).clientResult s q = r ∧
    memoryCost q s ≤ n ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s q
  have hpure (n r : ℕ) : Spec n (pure r) r :=
    ⟨rfl, rfl, by simp [memoryCost_pure], validProg_pure r⟩
  have step {α : Type} {p : Memory.Prog α} {v : α} {c₁ c₂ n r : ℕ}
      (hst : (Memory.spec 0).clientState s p = s)
      (hres : (Memory.spec 0).clientResult s p = v)
      (hmc : memoryCost p s ≤ c₁)
      (hvp : ValidProg w (base + largeSpaceWhp c U V w n_max) s p)
      (hn : c₁ + c₂ ≤ n) {k : α → Memory.Prog ℕ} (hk : Spec c₂ (k v) r) :
      Spec n (p >>= k) r := by
    refine ⟨by rw [clientState_bind, hst, hres, hk.1],
      by rw [clientResult_bind, hst, hres, hk.2.1], ?_,
      validProg_bind hvp (by simpa only [hst, hres] using hk.2.2.2)⟩
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hst, hres]
    exact (Nat.add_le_add hmc hk.2.2.1).trans hn
  dsimp only
  change Spec 5 _ _
  unfold checkEpochTickOkGenProg
  simp only [pure_bind, wp_large_qEpoch hth]
  unfold epochTickWillSucceed
  refine step hck_st hck_res (by omega) hck_vp (c₁ := 1) (c₂ := 4) (by omega) ?_
  by_cases hlt : fs.epochClock + 1 < qEpochWhp n_max
  · rw [decide_eq_true (Or.inl hlt), ite_eq_left hlt]
    exact hpure 4 1
  · obtain ⟨hst_st, hst_res, hst_mc, hst_vp⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage)
      (by dsimp [hdrRebStage]; omega) (s := s)
    rw [hh.rebStage] at hst_res
    rw [ite_eq_right hlt]
    refine step hst_st hst_res (by omega) hst_vp (c₁ := 1) (c₂ := 3) (by omega) ?_
    by_cases hs5 : fs.rebStage = 5
    · rw [decide_eq_true (Or.inr (Or.inl hs5)), ite_eq_left hs5]
      exact hpure 3 1
    · rw [ite_eq_right hs5]
      by_cases hs4 : fs.rebStage = 4
      · rw [ite_eq_left hs4]
        obtain ⟨hro_st, hro_res, hro_mc, hro_vp⟩ := readOldEpProg_spec (w := w)
          (F := base + largeSpaceWhp c U V w n_max) (by dsimp [hdrCurEp]; omega) hce_or
          hh.curEp (s := s)
        obtain ⟨hra_st, hra_res, hra_mc, hra_vp⟩ :=
          readBufAllocsProg_spec henv hold_or hrep (s := s)
        refine step hro_st hro_res (by omega) hro_vp (c₁ := 1) (c₂ := 2) (by omega) ?_
        refine step hra_st hra_res hra_mc hra_vp (c₁ := 2) (c₂ := 0) (by omega) ?_
        dsimp only
        by_cases h8 : (fs.buf fs.oldEp).nodeAlloc ≤ 8
        · rw [decide_eq_true (Or.inr (Or.inr ⟨hs4, h8⟩)), ite_eq_left h8]
          exact hpure 0 1
        · rw [decide_eq_false (by omega), ite_eq_right h8]
          exact hpure 0 0
      · rw [decide_eq_false (by omega), ite_eq_right hs4]
        exact hpure 3 0

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.EpochTickInternal

end
