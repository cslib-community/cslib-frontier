/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg
import CslibFrontier.Tactic.Realize

/-!
# Fast Deletion Substep 3 (`fastDeleteShrinkGenProg`)

Clears `locState b loc_last`, decrements `bktCount b`, and returns any released backyard pool
slot to `poolFreeStack`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fastDeleteShrinkGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_fastDeleteShrinkGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fastDeleteShrinkGenProg_fastStep`
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

/-- Backyard slot release helper for `fastDeleteShrinkGenProg` when `capFrontWhp ≤ loc_last`
(`d = (((cp, base), b), loc_last)`). -/
@[irreducible] private def delShrinkBackyardProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), b), loc_last) => do
    let z1 ← pure 1
    let k ← pure (loc_last - wpCapFront cp)
    let pSlot ← readBackPtrGenProg (((cp, base), b), k)
    let top ← readHdrProg (base, hdrPoolFreeTop)
    writePoolFreeStackGenProg (((cp, base), top), pSlot)
    let top1 ← pure (top + z1)
    writeHdrProg ((base, hdrPoolFreeTop), top1)

private theorem realizes_delShrinkBackyard :
    Realizes .exact delShrinkBackyardProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), b), loc_last) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs2 : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs2 s.mem ∧
          b < numBucketsWhp n_max ∧
          capFrontWhp n_max ≤ loc_last ∧
          loc_last < totalLocalCoordsWhp n_max ∧
          fs2.poolFreeTop < poolSizeWhp n_max)
      (fun _ _ => 0) := by
  unfold delShrinkBackyardProg
  have hrb := realizes_readBackPtrGen
  have hrh := realizes_readHdr
  have hws := realizes_writePoolFreeStackGen
  have hwh := realizes_writeHdr
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, loc_last⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs2, henv, rfl, hrep2, hb, hcf, hll, htop_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h32_sp := headerWords_le_largeSpaceWhp c U V w n_max
    have h2tl := (large_index_bounds hth).2.2.1
    have hps_le := (large_index_bounds hth).2.1
    have hk : loc_last - capFrontWhp n_max < capBackWhp n_max := by
      unfold totalLocalCoordsWhp at hll; omega
    obtain ⟨hrb_st, hrb_res, _, _⟩ := readBackPtrGenProg_spec henv hb hk hrep2 (s := s)
    obtain ⟨hrh_st, hrh_res, _, _⟩ := readHdrProg_large_spec c U V w n_max
      (base := base) (hdrOff := hdrPoolFreeTop) (s := s) (by decide)
    have hmem_top : s.mem (base + hdrPoolFreeTop) = fs2.poolFreeTop := hrep2.2.2.1
    simp only [wp_large_M hth, wp_large_capFront hth, wp_large_capBack hth,
      wp_large_poolSize hth] at *
    simp only [hrb_st, hrb_res, hrh_st, hrh_res, hmem_top] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact hk
    | exact htop_lt
    | omega
  )

/-- Substep 3 (`fastDeleteShrink`): clear `locState b loc_last := 0`, set `bktCount b := loc_last`,
and return any backyard slot to `poolFreeStack` (`d = (((cp, base), b), loc_last)`). -/
@[irreducible] def fastDeleteShrinkGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), b), loc_last) => do
    let z0 ← pure 0
    writeFastLocGenProg ((((cp, base), b), loc_last), z0)
    writeBktFieldGenProg ((((cp, base), b), z0), loc_last)
    let cf ← pure (wpCapFront cp)
    if cf ≤ loc_last then
      delShrinkBackyardProg (((cp, base), b), loc_last)
    else
      pure ()

theorem realizes_fastDeleteShrinkGen :
    Realizes .exact fastDeleteShrinkGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), b), loc_last) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs2 : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs2 s.mem ∧
          b < numBucketsWhp n_max ∧
          loc_last < totalLocalCoordsWhp n_max ∧
          (capFrontWhp n_max ≤ loc_last →
            fs2.backPtr b (loc_last - capFrontWhp n_max) < poolSizeWhp n_max ∧
            fs2.poolFreeTop < poolSizeWhp n_max))
      (fun _ _ => 0) := by
  unfold fastDeleteShrinkGenProg
  have hwl := realizes_writeFastLocGen
  have hwb := realizes_writeBktFieldGen
  have hsb := realizes_delShrinkBackyard
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, loc_last⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs2, henv, rfl, hseed, hrep2, hb, hll, hcf_fn⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h2tl := (large_index_bounds hth).2.2.1
    obtain ⟨_, _, hwl_step⟩ := writeFastLocGenProg_fastStep henv hb hll (by decide : 0 < 4)
      hseed hrep2 (s := s)
    set s1 := (Memory.spec 0).clientState s
      (writeFastLocGenProg ((((mkWhpCoreParams c U V w n_max, base), b), loc_last), 0))
    obtain ⟨_, _, hwb_step⟩ := writeBktFieldGenProg_fastStep henv hb (by decide : 0 < 10)
      (by omega : loc_last ≤ n_max) hwl_step.2.1 hwl_step.2.2.1 (s := s1)
    simp only [setBktField] at hwb_step
    try simp only [wp_large_M hth, wp_large_totalLoc hth, wp_large_capFront hth] at *
    first
    | decide
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact hll
    | (have hcf : capFrontWhp n_max ≤ loc_last := by omega
       exact ⟨c, U, V, w, n_max, _, henv, rfl, hwb_step.2.2.1, hb, hcf, hll, (hcf_fn hcf).2⟩)
  )

theorem fastDeleteShrinkGenProg_fastStep {c U V w n_max base b loc_last : ℕ}
    {θ : SeedWhp c U n_max} {fs2 : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hll : loc_last < totalLocalCoordsWhp n_max)
    (hcf_fn : capFrontWhp n_max ≤ loc_last →
      fs2.backPtr b (loc_last - capFrontWhp n_max) < poolSizeWhp n_max ∧
      fs2.poolFreeTop < poolSizeWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep2 : FastMemRep base c U V w n_max fs2 s.mem) :
    let prog := fastDeleteShrinkGenProg (((mkWhpCoreParams c U V w n_max, base), b), loc_last)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 16 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (fastDeleteShrink n_max b loc_last fs2) s s' := by
  have hth := henv.2.2.2.1
  have h32_sp := headerWords_le_largeSpaceWhp c U V w n_max
  have h2tl := (large_index_bounds hth).2.2.1
  have hps_le := (large_index_bounds hth).2.1
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hwl_mc, hwl_vp, hwl_step⟩ := writeFastLocGenProg_fastStep henv hb hll (by decide : 0 < 4)
    hseed hrep2 (s := s)
  set s1 := (Memory.spec 0).clientState s (writeFastLocGenProg ((((cp, base), b), loc_last), 0))
  obtain ⟨hwb_mc, hwb_vp, hwb_step⟩ := writeBktFieldGenProg_fastStep henv hb (by decide : 0 < 10)
    (by omega : loc_last ≤ n_max) hwl_step.2.1 hwl_step.2.2.1 (s := s1)
  set s2 := (Memory.spec 0).clientState s1 (writeBktFieldGenProg ((((cp, base), b), 0), loc_last))
  simp only [setBktField] at hwb_step
  unfold fastDeleteShrinkGenProg fastDeleteShrink
  simp only [cp, wp_large_capFront hth, pure_bind]
  by_cases hcf : capFrontWhp n_max ≤ loc_last
  · simp only [hcf, ↓reduceIte, delShrinkBackyardProg.eq_1, wp_large_capFront hth, pure_bind]
    have hk : loc_last - capFrontWhp n_max < capBackWhp n_max := by
      unfold totalLocalCoordsWhp at hll; omega
    obtain ⟨hbp_lt, htop_lt⟩ := hcf_fn hcf
    obtain ⟨hrb_st, hrb_res, hrb_mc, hrb_vp⟩ :=
      readBackPtrGenProg_spec henv hb hk hwb_step.2.2.1 (s := s2)
    obtain ⟨hrh_st, hrh_res, hrh_mc, hrh_vp⟩ := readHdrProg_large_spec c U V w n_max
      (base := base) (hdrOff := hdrPoolFreeTop) (s := s2) (by decide)
    rw [hwb_step.2.2.1.2.2.1] at hrh_res
    obtain ⟨hws_mc, hws_vp, hws_step⟩ := writePoolFreeStackGenProg_fastStep henv htop_lt
      (by omega : fs2.backPtr b (loc_last - capFrontWhp n_max) ≤ n_max)
      hwb_step.2.1 hwb_step.2.2.1 (s := s2)
    set s3 := (Memory.spec 0).clientState s2
      (writePoolFreeStackGenProg
        (((cp, base), fs2.poolFreeTop), fs2.backPtr b (loc_last - capFrontWhp n_max)))
    obtain ⟨hwh_mc, hwh_vp, hwh_step⟩ := writeHdrProg_fastStep (hdrOff := hdrPoolFreeTop) henv
      (by decide) (henv.fits_of_le_n_max (by omega))
      (by intro h; cases h) hws_step.2.1 hws_step.2.2.1
      (val := fs2.poolFreeTop + 1) (s := s3)
    dsimp only [updateFastHdr] at hwh_step
    refine ⟨?_, ?_, ?_⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      dsimp only [s1, s2, s3, cp]
        at hwl_mc hwb_mc hrb_st hrb_res hrb_mc hrh_st hrh_res hrh_mc hws_mc hwh_mc ⊢
      rw [hrb_st, hrb_res, hrb_mc, hrh_st, hrh_res, hrh_mc]; omega
    · refine validProg_bind hwl_vp (validProg_bind hwb_vp (validProg_bind hrb_vp ?_))
      rw [hrb_st, hrb_res]
      refine validProg_bind hrh_vp ?_
      rw [hrh_st, hrh_res]
      exact validProg_bind hws_vp hwh_vp
    · rw [clientState_bind, clientState_bind, clientState_bind, hrb_st, hrb_res,
        clientState_bind, hrh_st, hrh_res, clientState_bind]
      exact ((hwl_step.trans hwb_step).trans hws_step).trans hwh_step
  · simp only [hcf, ↓reduceIte]
    refine ⟨?_, validProg_bind hwl_vp (validProg_bind hwb_vp (validProg_pure _)), ?_⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_pure]
      dsimp only [s1, cp] at hwl_mc hwb_mc ⊢
      omega
    · rw [clientState_bind, clientState_bind]
      exact hwl_step.trans hwb_step

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
