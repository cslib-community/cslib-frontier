/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg.Bounds
import CslibFrontier.Tactic.Realize

/-!
# Fast Insertion Slot Allocation & Write Primitives

Low-level mutating primitives for fresh fast insertions: backyard slot pop/binding, `(q, v)` slot
writes, and collision vs. direct insertion commit steps.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fastInsertAllocGenProg`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.insWriteQVAtGenProg`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.insFinishCollisionGenProg`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.insFinishDirectGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fastInsertAllocGenProg_fastStep`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.insWriteQVAtGenProg_fastStep`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.insFinishCollisionGenProg_fastStep`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.insFinishDirectGenProg_fastStep`
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

/-- Pop one free slot from `poolFreeStack[poolFreeTop - 1]` and decrement `poolFreeTop`. -/
@[irreducible] private def insPopFreeSlotGenProg :
    WhpCoreParams × ℕ → Memory.Prog ℕ
  | (cp, base) => do
    let z1 ← pure 1
    let top ← readHdrProg (base, hdrPoolFreeTop)
    let top' ← pure (top - z1)
    let pSlot ← readPoolFreeStackGenProg ((cp, base), top')
    writeHdrProg ((base, hdrPoolFreeTop), top')
    pure pSlot

private theorem realizes_insPopFreeSlotGen :
    Realizes .exact insPopFreeSlotGenProg
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (cp, base) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          0 < fs.poolFreeTop ∧
          fs.poolFreeTop ≤ poolSizeWhp n_max)
      (fun _ _ => 0) := by
  unfold insPopFreeSlotGenProg
  have hrh := realizes_readHdr
  have hrs := realizes_readPoolFreeStackGen
  have hwh := realizes_writeHdr
  realize
  all_goals (
    rcases d with ⟨cp, base⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hpos, hle_ps⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hps_le := (large_index_bounds hth).2.2.2.1
    obtain ⟨ht_st, ht_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrPoolFreeTop)
      (by dsimp [hdrPoolFreeTop]; omega) (s := s)
    rw [hrep.2.2.1] at ht_res
    obtain ⟨hp_st, _, _, _⟩ :=
      readPoolFreeStackGenProg_spec henv (by omega : fs.poolFreeTop - 1 < poolSizeWhp n_max)
        hrep (s := s)
    simp only [ht_st, ht_res, hp_st, wp_large_poolSize hth] at *
    first
    | omega
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
  )

/-- Bind backyard slot `pSlot` to `(b, k)` in `backPtr` and `poolOwner`. -/
@[irreducible] private def insBindBackSlotGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, base), b), k), pSlot) => do
    writeBackPtrGenProg ((((cp, base), b), k), pSlot)
    let enc ← pure (b * wpCapBack cp + k)
    writePoolOwnerGenProg (((cp, base), pSlot), enc)

private theorem realizes_insBindBackSlotGen :
    Realizes .exact insBindBackSlotGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), k), pSlot) _ =>
        WhpLargeEnvGen w cp base ∧ b < wpM cp ∧ k < wpCapBack cp ∧ pSlot < wpPoolSize cp)
      (fun _ _ => 0) := by
  unfold insBindBackSlotGenProg
  have hwb := realizes_writeBackPtrGen
  have hwo := realizes_writePoolOwnerGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, k⟩, pSlot⟩
    dsimp only at *
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb, hk, hpSlot⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hmcb := (large_index_bounds hth).1
    simp only [wp_large_M hth, wp_large_capBack hth, wp_large_poolSize hth] at hb hk hpSlot ⊢
    have hidx := mul_add_lt_mul_bound hb hk
    first
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact hk
    | exact hpSlot
  )

/-- Backyard allocation sequence for `fastInsertAllocGenProg` when `capFrontWhp ≤ X`. -/
@[irreducible] private def insAllocBackyardProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), b), X) => do
    let k ← pure (X - wpCapFront cp)
    let pSlot ← insPopFreeSlotGenProg (cp, base)
    insBindBackSlotGenProg ((((cp, base), b), k), pSlot)

private theorem realizes_insAllocBackyard :
    Realizes .exact insAllocBackyardProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), b), X) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          capFrontWhp n_max ≤ X ∧
          X < totalLocalCoordsWhp n_max ∧
          0 < fs.poolFreeTop ∧
          fs.poolFreeTop ≤ poolSizeWhp n_max ∧
          fs.poolFreeStack (fs.poolFreeTop - 1) < poolSizeWhp n_max)
      (fun _ _ => 0) := by
  unfold insAllocBackyardProg
  have hpop := realizes_insPopFreeSlotGen
  have hbnd := realizes_insBindBackSlotGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, b⟩, X⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hcf, hX_tl, hpos, hle_ps, hp_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have h2tl := (large_index_bounds hth).2.2.1
    have hk : X - capFrontWhp n_max < capBackWhp n_max := by
      unfold totalLocalCoordsWhp at hX_tl; omega
    obtain ⟨ht_st, ht_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrPoolFreeTop)
      (by dsimp [hdrPoolFreeTop]; omega) (s := s)
    rw [hrep.2.2.1] at ht_res
    obtain ⟨hp_st, hp_res, _, _⟩ :=
      readPoolFreeStackGenProg_spec henv (by omega : fs.poolFreeTop - 1 < poolSizeWhp n_max)
        hrep (s := s)
    have hpop_res : (Memory.spec 0).clientResult s
        (insPopFreeSlotGenProg (mkWhpCoreParams c U V w n_max, base)) =
        fs.poolFreeStack (fs.poolFreeTop - 1) := by
      unfold insPopFreeSlotGenProg; dsimp only; simp only [pure_bind]
      rw [clientResult_bind, ht_st, ht_res, clientResult_bind, hp_st, hp_res,
        clientResult_bind, clientResult_pure_whp]
    simp only [hpop_res, wp_large_M hth, wp_large_capFront hth, wp_large_capBack hth,
      wp_large_poolSize hth] at *
    first
    | omega
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hpos, hle_ps⟩
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
  )

/-- Allocate backyard slot at `(b, X)` when `capFrontWhp ≤ X` (`d = (((cp, base), b), X)`). -/
@[irreducible] def fastInsertAllocGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | (((cp, base), b), X) => do
    let cf ← pure (wpCapFront cp)
    if cf ≤ X then
      insAllocBackyardProg (((cp, base), b), X)
    else
      pure ()

theorem realizes_fastInsertAllocGen :
    Realizes .exact fastInsertAllocGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w (((cp, base), b), X) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          X < totalLocalCoordsWhp n_max ∧
          (capFrontWhp n_max ≤ X →
            0 < fs.poolFreeTop ∧
            fs.poolFreeTop ≤ poolSizeWhp n_max ∧
            fs.poolFreeStack (fs.poolFreeTop - 1) < poolSizeWhp n_max))
      (fun _ _ => 0) := by
  unfold fastInsertAllocGenProg
  have hab := realizes_insAllocBackyard
  realize
  rcases d with ⟨⟨⟨cp, base⟩, b⟩, X⟩
  obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hX_tl, hcf_fn⟩ := h
  have hw_eq := henv.2.2.1; subst hw_eq
  have hth := henv.2.2.2.1
  simp only [wp_large_capFront hth] at *
  have hcf : capFrontWhp n_max ≤ X := by omega
  obtain ⟨hpos, hle_ps, hp_lt⟩ := hcf_fn hcf
  exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hcf, hX_tl, hpos, hle_ps, hp_lt⟩

theorem fastInsertAllocGenProg_fastStep {c U V w n_max base b X : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hX_tl : X < totalLocalCoordsWhp n_max)
    (hcf_fn : capFrontWhp n_max ≤ X →
      0 < fs.poolFreeTop ∧
      fs.poolFreeTop ≤ poolSizeWhp n_max ∧
      fs.poolFreeStack (fs.poolFreeTop - 1) < poolSizeWhp n_max)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := fastInsertAllocGenProg (((mkWhpCoreParams c U V w n_max, base), b), X)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 12 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (fastInsertAlloc n_max b X fs) s s' := by
  have hth := henv.2.2.2.1
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have hmcb := (large_index_bounds hth).1
  have hps_le := (large_index_bounds hth).2.2.2.1
  set cp := mkWhpCoreParams c U V w n_max
  dsimp only
  unfold fastInsertAllocGenProg fastInsertAlloc; dsimp only
  simp only [cp, wp_large_capFront hth, pure_bind]
  by_cases hcf : capFrontWhp n_max ≤ X
  · simp only [hcf, ↓reduceIte]
    obtain ⟨hpos, hle_ps, hp_lt⟩ := hcf_fn hcf
    have hk : X - capFrontWhp n_max < capBackWhp n_max := by
      unfold totalLocalCoordsWhp at hX_tl; omega
    set k := X - capFrontWhp n_max
    set top' := fs.poolFreeTop - 1
    set pSlot := fs.poolFreeStack top'
    obtain ⟨ht_st, ht_res, ht_mc, ht_vp⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrPoolFreeTop)
      (by dsimp [hdrPoolFreeTop]; omega) (s := s)
    rw [hrep.2.2.1] at ht_res
    obtain ⟨hp_st, hp_res, hp_mc, hp_vp⟩ :=
      readPoolFreeStackGenProg_spec henv (by omega : top' < poolSizeWhp n_max) hrep (s := s)
    obtain ⟨hwh_mc, hwh_vp, hwh_step⟩ := writeHdrProg_fastStep (hdrOff := hdrPoolFreeTop) henv
      (by decide) (henv.fits_of_le_n_max (by omega)) (by intro h; cases h) hseed hrep
      (val := top') (s := s)
    dsimp only [updateFastHdr] at hwh_step
    set s1 := (Memory.spec 0).clientState s (writeHdrProg ((base, hdrPoolFreeTop), top'))
    obtain ⟨hwb_mc, hwb_vp, hwb_step⟩ := writeBackPtrGenProg_fastStep henv hb hk
      (by omega : pSlot ≤ n_max) hwh_step.2.1 hwh_step.2.2.1 (s := s1)
    set s2 := (Memory.spec 0).clientState s1 (writeBackPtrGenProg ((((cp, base), b), k), pSlot))
    have hidx_enc : b * capBackWhp n_max + k < numBucketsWhp n_max * capBackWhp n_max :=
      mul_add_lt_mul_bound hb hk
    obtain ⟨hwo_mc, hwo_vp, hwo_step⟩ := writePoolOwnerGenProg_fastStep henv hp_lt
      (by omega : b * capBackWhp n_max + k ≤ n_max) hwb_step.2.1 hwb_step.2.2.1 (s := s2)
    have hpop_st : (Memory.spec 0).clientState s (insPopFreeSlotGenProg (cp, base)) = s1 := by
      unfold insPopFreeSlotGenProg; dsimp only; simp only [pure_bind]
      rw [clientState_bind, ht_st, ht_res, clientState_bind, hp_st, hp_res,
        clientState_bind, clientState_pure_whp]
    have hpop_res : (Memory.spec 0).clientResult s (insPopFreeSlotGenProg (cp, base)) = pSlot := by
      unfold insPopFreeSlotGenProg; dsimp only; simp only [pure_bind]
      rw [clientResult_bind, ht_st, ht_res, clientResult_bind, hp_st, hp_res,
        clientResult_bind, clientResult_pure_whp]
    have hpop_mc : memoryCost (insPopFreeSlotGenProg (cp, base)) s ≤ 4 := by
      unfold insPopFreeSlotGenProg; dsimp only
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      dsimp only [cp, top'] at hp_st hp_res hp_mc hwh_mc ⊢
      rw [ht_st, ht_res, ht_mc, hp_st, hp_res, hp_mc, memoryCost_pure]; omega
    have hpop_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
        (insPopFreeSlotGenProg (cp, base)) := by
      unfold insPopFreeSlotGenProg; dsimp only; simp only [pure_bind]
      refine validProg_bind ht_vp ?_; rw [ht_st, ht_res]
      refine validProg_bind hp_vp ?_; rw [hp_st, hp_res]
      exact validProg_bind hwh_vp (validProg_pure _)
    unfold insAllocBackyardProg; dsimp only
    simp only [wp_large_capFront hth, pure_bind]
    have hs'_eq : (Memory.spec 0).clientState s
        (insPopFreeSlotGenProg (cp, base) >>= fun p =>
          insBindBackSlotGenProg ((((cp, base), b), k), p)) =
        (Memory.spec 0).clientState s2
          (writePoolOwnerGenProg (((cp, base), pSlot), b * capBackWhp n_max + k)) := by
      rw [clientState_bind, hpop_st, hpop_res]
      unfold insBindBackSlotGenProg; dsimp only
      simp only [cp, wp_large_capBack hth, pure_bind]
      rw [clientState_bind]
    rw [hs'_eq]
    refine ⟨?_, ?_, (hwh_step.trans hwb_step).trans hwo_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hpop_st, hpop_res]
      unfold insBindBackSlotGenProg; dsimp only
      simp only [wp_large_capBack hth, pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      dsimp only [s1, s2, cp, k, pSlot] at hpop_mc hwb_mc hwo_mc ⊢; omega
    · refine validProg_bind hpop_vp ?_; rw [hpop_st, hpop_res]
      unfold insBindBackSlotGenProg; dsimp only
      simp only [wp_large_capBack hth, pure_bind]
      exact validProg_bind hwb_vp hwo_vp
  · simp only [hcf, ↓reduceIte, memoryCost_pure]
    exact ⟨Nat.zero_le _, validProg_pure _, FastStateStep.refl hseed hrep⟩

/-- Write `(q_val, v_val)` at `physSlot b X` (`d = ((((cp, base), b), X), (q_val, v_val))`). -/
@[irreducible] def insWriteQVAtGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((cp, base), b), X), (q_val, v_val)) => do
    let p_new ← physSlotGenProg (((cp, base), b), X)
    writeQuotGenProg (((cp, base), p_new), q_val)
    writeValGenProg (((cp, base), p_new), v_val)

theorem realizes_insWriteQVAtGen :
    Realizes .exact insWriteQVAtGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), X), (q_val, _)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          X < totalLocalCoordsWhp n_max ∧
          (capFrontWhp n_max ≤ X → fs.backPtr b (X - capFrontWhp n_max) < poolSizeWhp n_max) ∧
          q_val < 2 ^ quotBitsWhp U n_max)
      (fun _ _ => 0) := by
  unfold insWriteQVAtGenProg
  have hps := realizes_physSlotGen
  have hwq := realizes_writeQuotGen
  have hwv := realizes_writeValGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, X⟩, ⟨q_val, v_val⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hb, hX_tl, hbp, hq_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    obtain ⟨hps_st, hps_res, hps_lt, _, _⟩ := physSlotGenProg_spec henv hb hX_tl hbp hrep (s := s)
    obtain ⟨_, _, hwq_step⟩ := writeQuotGenProg_fastStep henv hps_lt hq_lt hseed hrep (s := s)
    simp only [hps_st, hps_res, wp_large_nMax hth] at *
    first
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hX_tl, hbp⟩
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hps_lt
  )

theorem insWriteQVAtGenProg_fastStep {c U V w n_max base b X q_val v_val : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hX_tl : X < totalLocalCoordsWhp n_max)
    (hbp : capFrontWhp n_max ≤ X → fs.backPtr b (X - capFrontWhp n_max) < poolSizeWhp n_max)
    (hq_lt : q_val < 2 ^ quotBitsWhp U n_max)
    (hv_lt : v_val < 2 ^ valBits V)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := insWriteQVAtGenProg
      ((((mkWhpCoreParams c U V w n_max, base), b), X), (q_val, v_val))
    let s' := (Memory.spec 0).clientState s prog
    let p_new := fs.physSlot n_max b X
    memoryCost prog s ≤ 10 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        quotArr := Function.update fs.quotArr p_new q_val
        valArr := Function.update fs.valArr p_new v_val } s s' := by
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hps_st, hps_res, hps_lt, hps_mc, hps_vp⟩ :=
    physSlotGenProg_spec henv hb hX_tl hbp hrep (s := s)
  obtain ⟨hwq_mc, hwq_vp, hwq_step⟩ :=
    writeQuotGenProg_fastStep henv hps_lt hq_lt hseed hrep (s := s)
  set s1 := (Memory.spec 0).clientState s
    (writeQuotGenProg (((cp, base), fs.physSlot n_max b X), q_val))
  obtain ⟨hwv_mc, hwv_vp, hwv_step⟩ :=
    writeValGenProg_fastStep henv hps_lt hv_lt hwq_step.2.1 hwq_step.2.2.1 (s := s1)
  dsimp only
  unfold insWriteQVAtGenProg; dsimp only
  have hs'_eq : (Memory.spec 0).clientState s
      (physSlotGenProg (((cp, base), b), X) >>= fun p =>
        writeQuotGenProg (((cp, base), p), q_val) >>= fun _ =>
        writeValGenProg (((cp, base), p), v_val)) =
      (Memory.spec 0).clientState s1
        (writeValGenProg (((cp, base), fs.physSlot n_max b X), v_val)) := by
    rw [clientState_bind, hps_st, hps_res, clientState_bind]
  rw [hs'_eq]
  refine ⟨?_, ?_, hwq_step.trans hwv_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hps_st, hps_res]; dsimp only [s1, cp] at hps_mc hwq_mc hwv_mc ⊢; omega
  · refine validProg_bind hps_vp ?_; rw [hps_st, hps_res]
    exact validProg_bind hwq_vp hwv_vp

/-- Set `bktCount b := X + 1` and `locState b X := tag` (`d = ((((cp, base), b), X), tag)`). -/
@[irreducible] private def insWriteCntLocGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, base), b), X), tag) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let X1 ← pure (X + z1)
    writeBktFieldGenProg ((((cp, base), b), z0), X1)
    writeFastLocGenProg ((((cp, base), b), X), tag)

private theorem realizes_insWriteCntLocGen :
    Realizes .exact insWriteCntLocGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), X), _) _ =>
        WhpLargeEnvGen w cp base ∧ b < wpM cp ∧ X < wpTotalLoc cp)
      (fun _ _ => 0) := by
  unfold insWriteCntLocGenProg
  have hwb := realizes_writeBktFieldGen
  have hwl := realizes_writeFastLocGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, X⟩, tag⟩
    dsimp only at *
    obtain ⟨⟨c, U, V, w₀, n_max, henv, rfl⟩, hb, hX_tl⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h2tl := (large_index_bounds hth).2.2.1
    simp only [wp_large_M hth, wp_large_totalLoc hth] at hb hX_tl ⊢
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact hX_tl
  )

private theorem insWriteCntLocGenProg_fastStep {c U V w n_max base b X tag : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hX_tl : X < totalLocalCoordsWhp n_max)
    (htag : tag < 4)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := insWriteCntLocGenProg ((((mkWhpCoreParams c U V w n_max, base), b), X), tag)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 8 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        bktCount := Function.update fs.bktCount b (X + 1)
        locState := Function.update fs.locState b
          (Function.update (fs.locState b) X tag) } s s' := by
  have h2tl := (large_index_bounds henv.2.2.2.1).2.2.1
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hwb_mc, hwb_vp, hwb_step⟩ := writeBktFieldGenProg_fastStep henv hb (by decide : 0 < 10)
    (by omega : X + 1 ≤ n_max) hseed hrep (s := s)
  simp only [setBktField] at hwb_step
  set s1 := (Memory.spec 0).clientState s (writeBktFieldGenProg ((((cp, base), b), 0), X + 1))
  obtain ⟨hwl_mc, hwl_vp, hwl_step⟩ := writeFastLocGenProg_fastStep henv hb hX_tl htag
    hwb_step.2.1 hwb_step.2.2.1 (s := s1)
  dsimp only
  unfold insWriteCntLocGenProg; dsimp only; simp only [pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (writeBktFieldGenProg ((((cp, base), b), 0), X + 1) >>= fun _ =>
        writeFastLocGenProg ((((cp, base), b), X), tag)) =
      (Memory.spec 0).clientState s1
        (writeFastLocGenProg ((((cp, base), b), X), tag)) := by
    rw [clientState_bind]
  rw [hs'_eq]
  refine ⟨?_, ?_, hwb_step.trans hwl_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    dsimp only [s1, cp] at hwb_mc hwl_mc ⊢; omega
  · exact validProg_bind hwb_vp hwl_vp

/-- Increment `liveInsCount b` by `1` (`d = ((cp, base), b)`). -/
@[irreducible] private def insIncLiveInsGenProg :
    (WhpCoreParams × ℕ) × ℕ → Memory.Prog Unit
  | ((cp, base), b) => do
    let z1 ← pure 1
    let f3 ← pure 3
    let lic ← readBktFieldGenProg (((cp, base), b), f3)
    let lic1 ← pure (lic + z1)
    writeBktFieldGenProg ((((cp, base), b), f3), lic1)

private theorem realizes_insIncLiveInsGen :
    Realizes .exact insIncLiveInsGenProg
      (WordEncoding.encode (α := (WhpCoreParams × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((cp, base), b) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12)
      (fun _ _ => 0) := by
  unfold insIncLiveInsGenProg
  have hrb := realizes_readBktFieldGen
  have hwb := realizes_writeBktFieldGen
  realize
  all_goals (
    rcases d with ⟨⟨cp, base⟩, b⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hlic⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hML12 := numBucketsWhp_mul_scale_pow12_le hth
    have hM_ge := (large_bounds_lt_n_max hth).1
    have h9L12_n : 9 * (slabScale n_max) ^ 12 ≤ n_max :=
      (Nat.mul_le_mul_right _ (by omega : 9 ≤ numBucketsWhp n_max)).trans hML12
    have hL12_pos : 1 ≤ (slabScale n_max) ^ 12 := Nat.one_le_pow 12 _ (slabScale_pos n_max)
    obtain ⟨h3_st, h3_res, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 3 < 10) hrep (s := s)
    simp only [getBktField] at h3_res
    simp only [h3_st, h3_res, wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (by omega)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
  )

private theorem insIncLiveInsGenProg_fastStep {c U V w n_max base b : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hlic : fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := insIncLiveInsGenProg ((mkWhpCoreParams c U V w n_max, base), b)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 6 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        liveInsCount := Function.update fs.liveInsCount b (fs.liveInsCount b + 1) } s s' := by
  have hth := henv.2.2.2.1
  have hML12 := numBucketsWhp_mul_scale_pow12_le hth
  have hM_ge := (large_bounds_lt_n_max hth).1
  have h9L12_n : 9 * (slabScale n_max) ^ 12 ≤ n_max :=
    (Nat.mul_le_mul_right _ (by omega : 9 ≤ numBucketsWhp n_max)).trans hML12
  have hL12_pos : 1 ≤ (slabScale n_max) ^ 12 := Nat.one_le_pow 12 _ (slabScale_pos n_max)
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨h3_st, h3_res, h3_mc, h3_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 3 < 10) hrep (s := s)
  simp only [getBktField] at h3_res
  obtain ⟨hwb_mc, hwb_vp, hwb_step⟩ := writeBktFieldGenProg_fastStep henv hb (by decide : 3 < 10)
    (by omega : fs.liveInsCount b + 1 ≤ n_max) hseed hrep (s := s)
  simp only [setBktField] at hwb_step
  dsimp only
  unfold insIncLiveInsGenProg; dsimp only; simp only [pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (readBktFieldGenProg (((cp, base), b), 3) >>= fun lic =>
        writeBktFieldGenProg ((((cp, base), b), 3), lic + 1)) =
      (Memory.spec 0).clientState s
        (writeBktFieldGenProg ((((cp, base), b), 3), fs.liveInsCount b + 1)) := by
    rw [clientState_bind, h3_st, h3_res]
  rw [hs'_eq]
  refine ⟨?_, ?_, hwb_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [h3_st, h3_res, h3_mc]; dsimp only [cp] at hwb_mc ⊢; omega
  · refine validProg_bind h3_vp ?_; rw [h3_st, h3_res]; exact hwb_vp

/-- Finish collision insertion (`hasFpCollision = true`): write `bktCount`, `locState := 2 + curEp`,
and insert `(b, X)` into `buf curEp` (`d = ((((cp, base), b), X), rKey)`). -/
@[irreducible] def insFinishCollisionGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((cp, base), b), X), rKey) => do
    let z2 ← pure 2
    let ep ← readHdrProg (base, hdrCurEp)
    let tag ← pure (z2 + ep)
    insWriteCntLocGenProg ((((cp, base), b), X), tag)
    bufInsertGenProg ((((cp, base), ep), rKey), (b, X))

theorem realizes_insFinishCollisionGen :
    Realizes .exact insFinishCollisionGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), X), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState)
            (curMap : ℕ → Option (ℕ × ℕ)),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          b < numBucketsWhp n_max ∧
          X < totalLocalCoordsWhp n_max ∧
          (fs.buf fs.curEp).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
          (fs.buf fs.curEp).itemAlloc < qEpochWhp n_max ∧
          ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) curMap)
      (fun _ _ => 0) := by
  unfold insFinishCollisionGenProg
  have hrh := realizes_readHdr
  have hwc := realizes_insWriteCntLocGen
  have hbi := realizes_bufInsertGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, X⟩, rKey⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, curMap, henv, rfl, hseed, hrep, hce, hb, hX_tl,
      hna_cap, hia_cap, hv_cur⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h2w := henv.two_le_w
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have htag_lt : 2 + fs.curEp < 4 := by rcases hce with hc | hc <;> omega
    have hfit_tag : Fits w (2 + fs.curEp) := by
      have h4 : 4 ≤ 2 ^ w := (by decide : 4 ≤ 2 ^ 2).trans (Nat.pow_le_pow_right two_pos h2w)
      change 2 + fs.curEp < 2 ^ w; omega
    obtain ⟨hep_st, hep_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrCurEp)
      (by dsimp [hdrCurEp]; omega) (s := s)
    rw [hrep.2.2.2.1] at hep_res
    obtain ⟨_, _, hwc_step⟩ :=
      insWriteCntLocGenProg_fastStep henv hb hX_tl htag_lt hseed hrep (s := s)
    simp only [hep_st, hep_res, wp_large_M hth, wp_large_totalLoc hth] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact hfit_tag
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact hX_tl
    | exact ⟨c, U, V, w, n_max, _, curMap, henv, rfl, hce,
        FastMemRep.buf_rep hce hwc_step.2.2.1, hv_cur, hna_cap, hia_cap, hb, hX_tl⟩
  )

/-- Finish direct insertion (`hasFpCollision = false`): write `bktCount`, `locState := 1`, insert
`(fp, X)` into `slices lIdx`, and increment `liveInsCount b`. -/
@[irreducible] def insFinishDirectGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((cp, base), b), X), (fp, lIdx)) => do
    let z1 ← pure 1
    insWriteCntLocGenProg ((((cp, base), b), X), z1)
    btreeInsertGenProg ((((cp, base), lIdx), fp), X)
    insIncLiveInsGenProg ((cp, base), b)

theorem realizes_insFinishDirectGen :
    Realizes .exact insFinishDirectGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), X), (fp, lIdx)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (lm : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          X < totalLocalCoordsWhp n_max ∧
          lIdx = fs.liveSliceIdx b ∧
          lIdx < 3 * numBucketsWhp n_max ∧
          fp < 2 ^ fpBitsWhp n_max ∧
          fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices lIdx) lm)
      (fun _ _ => 0) := by
  unfold insFinishDirectGenProg
  have hwc := realizes_insWriteCntLocGen
  have hbi := realizes_btreeInsertGen
  have hic := realizes_insIncLiveInsGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, X⟩, ⟨fp, lIdx⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, lm, henv, rfl, hseed, hrep, hb, hX_tl, rfl,
      hlIdx, hfp_lt, hlic, hv_l⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hval_X := loc_lt_two_pow_valLaneBits hX_tl
    obtain ⟨_, _, hwc_step⟩ :=
      insWriteCntLocGenProg_fastStep henv hb hX_tl (by decide : 1 < 4) hseed hrep (s := s)
    set fs1 : FastState :=
      { fs with
        bktCount := Function.update fs.bktCount b (X + 1)
        locState := Function.update fs.locState b (Function.update (fs.locState b) X 1) }
    set s1 := (Memory.spec 0).clientState s
      (insWriteCntLocGenProg ((((mkWhpCoreParams c U V w n_max, base), b), X), 1))
    obtain ⟨_, _, hbi_step⟩ :=
      btreeInsertGenProg_fastStep (fs := fs1) henv hlIdx hlic
        hwc_step.2.1 hwc_step.2.2.1 hv_l hfp_lt hval_X (s := s1)
    try simp only [wp_large_M hth, wp_large_totalLoc hth] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact hX_tl
    | exact ⟨c, U, V, w, n_max, fs.liveInsCount b, _, lm,
        henv, rfl, hlIdx, hlic, FastMemRep.slice_rep hlIdx hwc_step.2.2.1, hv_l, hfp_lt, hval_X⟩
    | exact ⟨c, U, V, w, n_max, _, henv, rfl, hbi_step.2.2.1, hb, hlic⟩
  )

theorem insFinishCollisionGenProg_fastStep {c U V w n_max base b X rKey : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {curMap : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hb : b < numBucketsWhp n_max) (hX_tl : X < totalLocalCoordsWhp n_max)
    (hna_cap : (fs.buf fs.curEp).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max)
    (hia_cap : (fs.buf fs.curEp).itemAlloc < qEpochWhp n_max)
    (hv_cur : ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) curMap)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := insFinishCollisionGenProg
      ((((mkWhpCoreParams c U V w n_max, base), b), X), rKey)
    let s' := (Memory.spec 0).clientState s prog
    let ep := fs.curEp
    let tr' := bufInsert (cTabWhp c) (bCharWhp n_max) (fs.buf ep) rKey b X
    memoryCost prog s ≤ 20 * cTabWhp c + 33 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        bktCount := Function.update fs.bktCount b (X + 1)
        locState := Function.update fs.locState b
          (Function.update (fs.locState b) X (2 + ep))
        buf := Function.update fs.buf ep tr' } s s' := by
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  have htag_lt : 2 + fs.curEp < 4 := by rcases hce with hc | hc <;> omega
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hep_st, hep_res, hep_mc, hep_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrCurEp)
    (by dsimp [hdrCurEp]; omega) (s := s)
  rw [hrep.2.2.2.1] at hep_res
  obtain ⟨hwc_mc, hwc_vp, hwc_step⟩ :=
    insWriteCntLocGenProg_fastStep henv hb hX_tl htag_lt hseed hrep (s := s)
  set fs1 : FastState :=
    { fs with
      bktCount := Function.update fs.bktCount b (X + 1)
      locState := Function.update fs.locState b
        (Function.update (fs.locState b) X (2 + fs.curEp)) }
  set s1 := (Memory.spec 0).clientState s
    (insWriteCntLocGenProg ((((cp, base), b), X), 2 + fs.curEp))
  obtain ⟨hbi_mc, hbi_vp, hbi_step⟩ :=
    bufInsertGenProg_fastStep (fs := fs1) henv hce hwc_step.2.1 hwc_step.2.2.1 hv_cur
      hna_cap hia_cap hb hX_tl (rKey := rKey) (s := s1)
  dsimp only
  unfold insFinishCollisionGenProg; dsimp only; simp only [pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (readHdrProg (base, hdrCurEp) >>= fun ep =>
        insWriteCntLocGenProg ((((cp, base), b), X), 2 + ep) >>= fun _ =>
        bufInsertGenProg ((((cp, base), ep), rKey), (b, X))) =
      (Memory.spec 0).clientState s1
        (bufInsertGenProg ((((cp, base), fs.curEp), rKey), (b, X))) := by
    rw [clientState_bind, hep_st, hep_res, clientState_bind]
  rw [hs'_eq]
  refine ⟨?_, ?_, hwc_step.trans hbi_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hep_st, hep_res, hep_mc]
    dsimp only [s1, cp] at hwc_mc hbi_mc ⊢; omega
  · refine validProg_bind hep_vp ?_; rw [hep_st, hep_res]
    exact validProg_bind hwc_vp hbi_vp

theorem insFinishDirectGenProg_fastStep {c U V w n_max base b X fp lIdx : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {lm : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hX_tl : X < totalLocalCoordsWhp n_max)
    (hlIdx_eq : lIdx = fs.liveSliceIdx b)
    (hlIdx : lIdx < 3 * numBucketsWhp n_max)
    (hfp_lt : fp < 2 ^ fpBitsWhp n_max)
    (hlic : fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12)
    (hv_l : ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices lIdx) lm)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := insFinishDirectGenProg
      ((((mkWhpCoreParams c U V w n_max, base), b), X), (fp, lIdx))
    let s' := (Memory.spec 0).clientState s prog
    let sl' := btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      (fs.slices lIdx) fp X
    memoryCost prog s ≤ 2440 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        bktCount := Function.update fs.bktCount b (X + 1)
        locState := Function.update fs.locState b (Function.update (fs.locState b) X 1)
        slices := Function.update fs.slices lIdx sl'
        liveInsCount := Function.update fs.liveInsCount b (fs.liveInsCount b + 1) } s s' := by
  subst hlIdx_eq
  have hval_X := loc_lt_two_pow_valLaneBits hX_tl
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hwc_mc, hwc_vp, hwc_step⟩ :=
    insWriteCntLocGenProg_fastStep henv hb hX_tl (by decide : 1 < 4) hseed hrep (s := s)
  set fs1 : FastState :=
    { fs with
      bktCount := Function.update fs.bktCount b (X + 1)
      locState := Function.update fs.locState b (Function.update (fs.locState b) X 1) }
  set s1 := (Memory.spec 0).clientState s
    (insWriteCntLocGenProg ((((cp, base), b), X), 1))
  obtain ⟨hbi_mc, hbi_vp, hbi_step⟩ :=
    btreeInsertGenProg_fastStep (fs := fs1) henv hlIdx hlic
      hwc_step.2.1 hwc_step.2.2.1 hv_l hfp_lt hval_X (s := s1)
  set fs2 : FastState :=
    { fs1 with
      slices := Function.update fs1.slices (fs.liveSliceIdx b)
        (btreeInsert (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) fp X) }
  set s2 := (Memory.spec 0).clientState s1
    (btreeInsertGenProg ((((cp, base), fs.liveSliceIdx b), fp), X))
  obtain ⟨hic_mc, hic_vp, hic_step⟩ :=
    insIncLiveInsGenProg_fastStep (fs := fs2) henv hb hlic hbi_step.2.1 hbi_step.2.2.1 (s := s2)
  dsimp only
  unfold insFinishDirectGenProg; dsimp only; simp only [pure_bind]
  have hs'_eq : (Memory.spec 0).clientState s
      (insWriteCntLocGenProg ((((cp, base), b), X), 1) >>= fun _ =>
        btreeInsertGenProg ((((cp, base), fs.liveSliceIdx b), fp), X) >>= fun _ =>
        insIncLiveInsGenProg ((cp, base), b)) =
      (Memory.spec 0).clientState s2
        (insIncLiveInsGenProg ((cp, base), b)) := by
    rw [clientState_bind, clientState_bind]
  rw [hs'_eq]
  refine ⟨?_, ?_, (hwc_step.trans hbi_step).trans hic_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    dsimp only [s1, s2, cp] at hwc_mc hbi_mc hic_mc ⊢; omega
  · exact validProg_bind hwc_vp (validProg_bind hbi_vp hic_vp)

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
