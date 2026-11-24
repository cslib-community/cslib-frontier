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
# Fast Deletion Move-Last Info Reader, Buffer Relocation & Slot Copy

Sub-helpers for Substep 2 (`fastDeleteMoveLast`): reading `loc_last` metadata, updating
epoch-buffer back-pointers, and copying `(quotArr, valArr, locState)` into `loc_del`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.delMoveBufGenProg`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.delCopySlotGenProg`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.delMoveReadInfoGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_delMoveBufGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.delMoveBufGenProg_fastStep`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_delCopySlotGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.delCopySlotGenProg_fastStep`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.delMoveReadInfoGenProg_spec`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_delMoveReadInfoGen`
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

/-- Sub-helper 6.2a: relocate `(b, loc_last) → (b, loc_del)` in `buf 0` or `buf 1`. -/
@[irreducible] def delMoveBufGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ) → Memory.Prog Unit
  | ((((cp, base), b), loc_del), (st_last, rKey_last)) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let z2 ← pure 2
    let z3 ← pure 3
    if st_last = z2 then
      bufInsertGenProg ((((cp, base), z0), rKey_last), (b, loc_del))
    else if st_last = z3 then
      bufInsertGenProg ((((cp, base), z1), rKey_last), (b, loc_del))
    else
      pure ()

theorem realizes_delMoveBufGen :
    Realizes .exact delMoveBufGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), loc_del), (st_last, _)) s =>
        ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          loc_del < totalLocalCoordsWhp n_max ∧
          (st_last = 2 →
            (fs.buf 0).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
            (fs.buf 0).itemAlloc < qEpochWhp n_max ∧
            ∃ m0, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf 0) m0) ∧
          (st_last = 3 →
            (fs.buf 1).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
            (fs.buf 1).itemAlloc < qEpochWhp n_max ∧
            ∃ m1, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf 1) m1))
      (fun _ _ => 0) := by
  unfold delMoveBufGenProg
  have hbi := realizes_bufInsertGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, loc_del⟩, ⟨st_last, rKey_last⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hld, h2, h3⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    first
    | exact henv.fits_const (by decide)
    | (obtain ⟨hna0, hia0, m0, hv0⟩ := h2 (by assumption)
       exact ⟨c, U, V, w, n_max, fs.buf 0, m0, henv, rfl, Or.inl rfl,
         hrep.buf_rep (Or.inl rfl), hv0, hna0, hia0, hb, hld⟩)
    | (obtain ⟨hna1, hia1, m1, hv1⟩ := h3 (by assumption)
       exact ⟨c, U, V, w, n_max, fs.buf 1, m1, henv, rfl, Or.inr rfl,
         hrep.buf_rep (Or.inr rfl), hv1, hna1, hia1, hb, hld⟩)
  )

theorem delMoveBufGenProg_fastStep {c U V w n_max base b loc_del st_last rKey_last : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max) (hld : loc_del < totalLocalCoordsWhp n_max)
    (h2 : st_last = 2 →
      (fs.buf 0).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
      (fs.buf 0).itemAlloc < qEpochWhp n_max ∧
      ∃ m0, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf 0) m0)
    (h3 : st_last = 3 →
      (fs.buf 1).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
      (fs.buf 1).itemAlloc < qEpochWhp n_max ∧
      ∃ m1, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf 1) m1)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := delMoveBufGenProg
      ((((mkWhpCoreParams c U V w n_max, base), b), loc_del), (st_last, rKey_last))
    let s' := (Memory.spec 0).clientState s prog
    let buf2 :=
      if st_last = 2 then
        Function.update fs.buf 0
          (bufInsert (cTabWhp c) (bCharWhp n_max) (fs.buf 0) rKey_last b loc_del)
      else if st_last = 3 then
        Function.update fs.buf 1
          (bufInsert (cTabWhp c) (bCharWhp n_max) (fs.buf 1) rKey_last b loc_del)
      else fs.buf
    memoryCost prog s ≤ 20 * cTabWhp c + 24 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ { fs with buf := buf2 } s s' := by
  dsimp only
  unfold delMoveBufGenProg
  simp only [pure_bind]
  by_cases hs2 : st_last = 2
  · simp only [hs2, ↓reduceIte]
    obtain ⟨hna0, hia0, m0, hv0⟩ := h2 hs2
    obtain ⟨hmc, hvp, hstep⟩ :=
      bufInsertGenProg_fastStep henv (Or.inl rfl) hseed hrep hv0 hna0 hia0 hb hld
        (rKey := rKey_last) (s := s)
    exact ⟨hmc, hvp, hstep⟩
  · simp only [hs2, ↓reduceIte]
    by_cases hs3 : st_last = 3
    · simp only [hs3, ↓reduceIte]
      obtain ⟨hna1, hia1, m1, hv1⟩ := h3 hs3
      obtain ⟨hmc, hvp, hstep⟩ :=
        bufInsertGenProg_fastStep henv (Or.inr rfl) hseed hrep hv1 hna1 hia1 hb hld
          (rKey := rKey_last) (s := s)
      exact ⟨hmc, hvp, hstep⟩
    · simp only [hs3, ↓reduceIte]
      exact ⟨Nat.zero_le _, validProg_pure _, FastStateStep.refl hseed hrep⟩


/-- Sub-helper 6.2d: copy `(quotArr[p_last], valArr[p_last], st_last)` into `(p_del, loc_del)`
(`d = ((((cp, base), b), (loc_del, loc_last)), st_last)`). -/
@[irreducible] def delCopySlotGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((((cp, base), b), (loc_del, loc_last)), st_last) => do
    let p_last ← physSlotGenProg (((cp, base), b), loc_last)
    let p_del ← physSlotGenProg (((cp, base), b), loc_del)
    let q_last ← readQuotGenProg ((cp, base), p_last)
    let v_last ← readValGenProg ((cp, base), p_last)
    writeQuotGenProg (((cp, base), p_del), q_last)
    writeValGenProg (((cp, base), p_del), v_last)
    writeFastLocGenProg ((((cp, base), b), loc_del), st_last)

theorem realizes_delCopySlotGen :
    Realizes .exact delCopySlotGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), (loc_del, loc_last)), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          loc_del < loc_last ∧
          loc_last < totalLocalCoordsWhp n_max ∧
          (∀ k < loc_last + 1 - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max) ∧
          fs.quotArr (fs.physSlot n_max b loc_last) < 2 ^ quotBitsWhp U n_max ∧
          fs.valArr (fs.physSlot n_max b loc_last) < 2 ^ valBits V)
      (fun _ _ => 0) := by
  unfold delCopySlotGenProg
  have hps := realizes_physSlotGen
  have hrq := realizes_readQuotGen
  have hrv := realizes_readValGen
  have hwq := realizes_writeQuotGen
  have hwv := realizes_writeValGen
  have hwl := realizes_writeFastLocGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, ⟨loc_del, loc_last⟩⟩, st_last⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hb, hlt, hll, hbp, hq_lt,
      hv_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have hld : loc_del < totalLocalCoordsWhp n_max := hlt.trans hll
    have hbp_l : capFrontWhp n_max ≤ loc_last →
        fs.backPtr b (loc_last - capFrontWhp n_max) < poolSizeWhp n_max :=
      fun hcf => hbp _ (by omega)
    have hbp_d : capFrontWhp n_max ≤ loc_del →
        fs.backPtr b (loc_del - capFrontWhp n_max) < poolSizeWhp n_max :=
      fun hcf => hbp _ (by omega)
    obtain ⟨hps1_st, hps1_res, hps1_lt, _, _⟩ :=
      physSlotGenProg_spec henv hb hll hbp_l hrep (s := s)
    obtain ⟨hps2_st, hps2_res, hps2_lt, _, _⟩ :=
      physSlotGenProg_spec henv hb hld hbp_d hrep (s := s)
    obtain ⟨hrq_st, hrq_res, _, _⟩ := readQuotGenProg_spec henv hps1_lt hrep (s := s)
    obtain ⟨hrv_st, hrv_res, _, _⟩ := readValGenProg_spec henv hps1_lt hrep (s := s)
    simp only [hps1_st, hps1_res, hps2_st, hps2_res, hrq_st, hrq_res, hrv_st, hrv_res,
      wp_large_M hth, wp_large_nMax hth, wp_large_totalLoc hth] at *
    first
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hll, hbp_l⟩
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hld, hbp_d⟩
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hps1_lt
    | exact hps2_lt
    | exact hb
    | exact hld
  )

theorem delCopySlotGenProg_fastStep
    {c U V w n_max base b loc_del loc_last st_last : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hb : b < numBucketsWhp n_max)
    (hlt : loc_del < loc_last) (hll : loc_last < totalLocalCoordsWhp n_max)
    (hbp : ∀ k < loc_last + 1 - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max)
    (hq_lt : fs.quotArr (fs.physSlot n_max b loc_last) < 2 ^ quotBitsWhp U n_max)
    (hv_lt : fs.valArr (fs.physSlot n_max b loc_last) < 2 ^ valBits V)
    (hst_lt : st_last < 4)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let prog := delCopySlotGenProg
      ((((mkWhpCoreParams c U V w n_max, base), b), (loc_del, loc_last)), st_last)
    let s' := (Memory.spec 0).clientState s prog
    let p_last := fs.physSlot n_max b loc_last
    let p_del := fs.physSlot n_max b loc_del
    memoryCost prog s ≤ 20 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      { fs with
        quotArr := Function.update fs.quotArr p_del (fs.quotArr p_last)
        valArr := Function.update fs.valArr p_del (fs.valArr p_last)
        locState := Function.update fs.locState b
          (Function.update (fs.locState b) loc_del st_last) } s s' := by
  set cp := mkWhpCoreParams c U V w n_max
  have hld : loc_del < totalLocalCoordsWhp n_max := hlt.trans hll
  obtain ⟨hps1_st, hps1_res, hps1_lt, hps1_mc, hps1_vp⟩ :=
    physSlotGenProg_spec henv hb hll (fun hcf => hbp _ (by omega)) hrep (s := s)
  obtain ⟨hps2_st, hps2_res, hps2_lt, hps2_mc, hps2_vp⟩ :=
    physSlotGenProg_spec henv hb hld (fun hcf => hbp _ (by omega)) hrep (s := s)
  obtain ⟨hrq_st, hrq_res, hrq_mc, hrq_vp⟩ := readQuotGenProg_spec henv hps1_lt hrep (s := s)
  obtain ⟨hrv_st, hrv_res, hrv_mc, hrv_vp⟩ := readValGenProg_spec henv hps1_lt hrep (s := s)
  obtain ⟨hwq_mc, hwq_vp, hwq_step⟩ :=
    writeQuotGenProg_fastStep henv hps2_lt hq_lt hseed hrep (s := s)
  set s1 := (Memory.spec 0).clientState s
    (writeQuotGenProg (((cp, base), fs.physSlot n_max b loc_del),
      fs.quotArr (fs.physSlot n_max b loc_last)))
  obtain ⟨hwv_mc, hwv_vp, hwv_step⟩ :=
    writeValGenProg_fastStep henv hps2_lt hv_lt hwq_step.2.1 hwq_step.2.2.1 (s := s1)
  set s2 := (Memory.spec 0).clientState s1
    (writeValGenProg (((cp, base), fs.physSlot n_max b loc_del),
      fs.valArr (fs.physSlot n_max b loc_last)))
  obtain ⟨hwl_mc, hwl_vp, hwl_step⟩ :=
    writeFastLocGenProg_fastStep henv hb hld hst_lt hwv_step.2.1 hwv_step.2.2.1 (s := s2)
  dsimp only
  unfold delCopySlotGenProg
  have hs'_eq : (Memory.spec 0).clientState s
      (physSlotGenProg (((cp, base), b), loc_last) >>= fun p_last =>
        physSlotGenProg (((cp, base), b), loc_del) >>= fun p_del =>
        readQuotGenProg ((cp, base), p_last) >>= fun q_last =>
        readValGenProg ((cp, base), p_last) >>= fun v_last =>
        writeQuotGenProg (((cp, base), p_del), q_last) >>= fun _ =>
        writeValGenProg (((cp, base), p_del), v_last) >>= fun _ =>
        writeFastLocGenProg ((((cp, base), b), loc_del), st_last)) =
      (Memory.spec 0).clientState s2
        (writeFastLocGenProg ((((cp, base), b), loc_del), st_last)) := by
    rw [clientState_bind, hps1_st, hps1_res, clientState_bind, hps2_st, hps2_res,
      clientState_bind, hrq_st, hrq_res, clientState_bind, hrv_st, hrv_res,
      clientState_bind, clientState_bind]
  rw [hs'_eq]
  refine ⟨?_, ?_, (hwq_step.trans hwv_step).trans hwl_step⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hps1_st, hps1_res, hps2_st, hps2_res, hrq_st, hrq_res, hrq_mc, hrv_st, hrv_res, hrv_mc]
    dsimp only [s1, s2, cp] at hps1_mc hps2_mc hwq_mc hwv_mc hwl_mc ⊢
    omega
  · refine validProg_bind hps1_vp ?_; rw [hps1_st, hps1_res]
    refine validProg_bind hps2_vp ?_; rw [hps2_st, hps2_res]
    refine validProg_bind hrq_vp ?_; rw [hrq_st, hrq_res]
    refine validProg_bind hrv_vp ?_; rw [hrv_st, hrv_res]
    exact validProg_bind hwq_vp (validProg_bind hwv_vp hwl_vp)

/-- Read `(st_last, rKey_last)` at `(b, loc_last)` without mutating memory. -/
@[irreducible] private def delMoveReadStRkGenProg :
    ((WhpParams × ℕ) × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | (((wp, base), b), loc_last) => do
    let st_last ← readFastLocGenProg (((wp.1, base), b), loc_last)
    let rKey_last ← rKeyAtGenProg (((wp, base), b), loc_last)
    pure (st_last, rKey_last)

private theorem realizes_delMoveReadStRkGen :
    Realizes .exact delMoveReadStRkGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      CoordHashPre
      (fun _ _ => 0) := by
  unfold delMoveReadStRkGenProg
  have hrl := realizes_readFastLocGen
  have hrk := realizes_rKeyAtGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, loc_last⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, heq_wp, hseed, hrep, hq_all, hb, hll, hbp_ll⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hst_l, _, _, _⟩ := readFastLocGenProg_spec henv hb hll hrep (s := s)
    obtain ⟨hrk_st, _, _, _⟩ := rKeyAtGenProg_spec henv hseed hrep hb hll hbp_ll (s := s)
    simp only [hcp_eq] at *
    simp only [hst_l, hrk_st, wp_large_M hth, wp_large_totalLoc hth] at *
    first
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact hll
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hq_all, hb, hll, hbp_ll⟩
  )

/-- Read `fpAt (bktSalt b) b loc_last` without mutating memory. -/
@[irreducible] private def readLiveFpAtGenProg :
    ((WhpParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((wp, base), b), loc_last) => do
    let salt_b ← readBktFieldGenProg (((wp.1, base), b), 1)
    fpAtGenProg ((((wp, base), salt_b), b), loc_last)

private theorem realizes_readLiveFpAtGen :
    Realizes .exact readLiveFpAtGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      CoordHashPre
      (fun _ _ => 0) := by
  unfold readLiveFpAtGenProg
  have hrb := realizes_readBktFieldGen
  have hfp := realizes_fpAtGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, loc_last⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, heq_wp, hseed, hrep, hq_all, hb, hll, hbp_ll⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hs1_st, _, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 1 < 10)
      hrep (s := s)
    simp only [hcp_eq] at *
    simp only [hs1_st, wp_large_M hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hq_all, hb, hll, hbp_ll⟩
  )

/-- Read `fpAt rebCandSalt b loc_last` without mutating memory. -/
@[irreducible] private def readCandFpAtGenProg :
    ((WhpParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((wp, base), b), loc_last) => do
    let cand ← readHdrProg (base, hdrRebCandSalt)
    fpAtGenProg ((((wp, base), cand), b), loc_last)

private theorem realizes_readCandFpAtGen :
    Realizes .exact readCandFpAtGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      CoordHashPre
      (fun _ _ => 0) := by
  unfold readCandFpAtGenProg
  have hrh := realizes_readHdr
  have hfp := realizes_fpAtGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, loc_last⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, heq_wp, hseed, hrep, hq_all, hb, hll, hbp_ll⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    obtain ⟨hcs_st, _, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebCandSalt)
      (by dsimp [hdrRebCandSalt]; omega) (s := s)
    simp only [hcs_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hq_all, hb, hll, hbp_ll⟩
  )

/-- Read `(st_last, (rKey_last, (fp_live_last, fp_cand_last)))` for `fastDeleteMoveLastGenProg`
without mutating memory. -/
@[irreducible] def delMoveReadInfoGenProg :
    ((WhpParams × ℕ) × ℕ) × ℕ → Memory.Prog (ℕ × (ℕ × (ℕ × ℕ)))
  | d => do
    let sr ← delMoveReadStRkGenProg d
    let fp_l ← readLiveFpAtGenProg d
    let fp_c ← readCandFpAtGenProg d
    pure (sr.1, (sr.2, (fp_l, fp_c)))

theorem delMoveReadInfoGenProg_spec {c U V w n_max base b loc_last : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hb : b < numBucketsWhp n_max)
    (hll : loc_last < totalLocalCoordsWhp n_max)
    (hbp_ll : capFrontWhp n_max ≤ loc_last →
      fs.backPtr b (loc_last - capFrontWhp n_max) < poolSizeWhp n_max) :
    let prog := delMoveReadInfoGenProg (((mkWhpParams c U V w n_max, base), b), loc_last)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (fs.locState b loc_last,
       (fs.rKeyAt c U n_max θ b loc_last,
        (fs.fpAt c U n_max θ (fs.bktSalt b) b loc_last,
         fs.fpAt c U n_max θ fs.rebCandSalt b loc_last))) ∧
    memoryCost prog s ≤ 5 * hashEvalCostWhp c + 18 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
  set cp := mkWhpCoreParams c U V w n_max
  set wp := mkWhpParams c U V w n_max
  obtain ⟨hst_l, hres_l, hmc_l, hvp_l⟩ := readFastLocGenProg_spec henv hb hll hrep (s := s)
  obtain ⟨hrk_st, hrk_res, hrk_mc, hrk_vp⟩ :=
    rKeyAtGenProg_spec henv hseed hrep hb hll hbp_ll (s := s)
  obtain ⟨hs1_st, hs1_res, hs1_mc, hs1_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 1 < 10) hrep (s := s)
  simp only [getBktField] at hs1_res
  obtain ⟨hfp1_st, hfp1_res, hfp1_mc, hfp1_vp⟩ :=
    fpAtGenProg_spec henv hseed hrep hb hll hbp_ll (salt := fs.bktSalt b) (s := s)
  obtain ⟨hcs_st, hcs_res, hcs_mc, hcs_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebCandSalt)
    (by dsimp [hdrRebCandSalt]; omega) (s := s)
  rw [hrep.2.2.2.2.2.2.2.2.2.1] at hcs_res
  obtain ⟨hfp2_st, hfp2_res, hfp2_mc, hfp2_vp⟩ :=
    fpAtGenProg_spec henv hseed hrep hb hll hbp_ll (salt := fs.rebCandSalt) (s := s)
  have hsr_st : (Memory.spec 0).clientState s
      (delMoveReadStRkGenProg (((wp, base), b), loc_last)) = s := by
    unfold delMoveReadStRkGenProg; dsimp only; rw [show wp.1 = cp from hwp1]
    rw [clientState_bind, hst_l, hres_l, clientState_bind, hrk_st, hrk_res]; rfl
  have hsr_res : (Memory.spec 0).clientResult s
      (delMoveReadStRkGenProg (((wp, base), b), loc_last)) =
      (fs.locState b loc_last, fs.rKeyAt c U n_max θ b loc_last) := by
    unfold delMoveReadStRkGenProg; dsimp only; rw [show wp.1 = cp from hwp1]
    rw [clientResult_bind, hst_l, hres_l, clientResult_bind, hrk_st, hrk_res]; rfl
  have hsr_mc : memoryCost (delMoveReadStRkGenProg (((wp, base), b), loc_last)) s ≤
      hashEvalCostWhp c + 7 := by
    unfold delMoveReadStRkGenProg; dsimp only; rw [show wp.1 = cp from hwp1]
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hst_l, hres_l, hmc_l, hrk_st, hrk_res, memoryCost_pure]
    have hrk_mc' : memoryCost (rKeyAtGenProg (((wp, base), b), loc_last)) s ≤
        hashEvalCostWhp c + 5 := hrk_mc
    omega
  have hsr_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (delMoveReadStRkGenProg (((wp, base), b), loc_last)) := by
    unfold delMoveReadStRkGenProg; dsimp only; rw [show wp.1 = cp from hwp1]
    refine validProg_bind hvp_l ?_; rw [hst_l, hres_l]
    refine validProg_bind hrk_vp ?_; rw [hrk_st, hrk_res]
    exact validProg_pure _
  have hfl_st : (Memory.spec 0).clientState s
      (readLiveFpAtGenProg (((wp, base), b), loc_last)) = s := by
    unfold readLiveFpAtGenProg; dsimp only; rw [show wp.1 = cp from hwp1]
    rw [clientState_bind, hs1_st, hs1_res, hfp1_st]
  have hfl_res : (Memory.spec 0).clientResult s
      (readLiveFpAtGenProg (((wp, base), b), loc_last)) =
      fs.fpAt c U n_max θ (fs.bktSalt b) b loc_last := by
    unfold readLiveFpAtGenProg; dsimp only; rw [show wp.1 = cp from hwp1]
    rw [clientResult_bind, hs1_st, hs1_res, hfp1_res]
  have hfl_mc : memoryCost (readLiveFpAtGenProg (((wp, base), b), loc_last)) s ≤
      2 * hashEvalCostWhp c + 6 := by
    unfold readLiveFpAtGenProg; dsimp only; rw [show wp.1 = cp from hwp1]
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hs1_st, hs1_res, hs1_mc]
    have hfp1_mc' : memoryCost (fpAtGenProg ((((wp, base), fs.bktSalt b), b), loc_last)) s ≤
        2 * hashEvalCostWhp c + 4 := hfp1_mc
    omega
  have hfl_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (readLiveFpAtGenProg (((wp, base), b), loc_last)) := by
    unfold readLiveFpAtGenProg; dsimp only; rw [show wp.1 = cp from hwp1]
    refine validProg_bind hs1_vp ?_; rw [hs1_st, hs1_res]; exact hfp1_vp
  have hfc_st : (Memory.spec 0).clientState s
      (readCandFpAtGenProg (((wp, base), b), loc_last)) = s := by
    unfold readCandFpAtGenProg
    rw [clientState_bind, hcs_st, hcs_res, hfp2_st]
  have hfc_res : (Memory.spec 0).clientResult s
      (readCandFpAtGenProg (((wp, base), b), loc_last)) =
      fs.fpAt c U n_max θ fs.rebCandSalt b loc_last := by
    unfold readCandFpAtGenProg
    rw [clientResult_bind, hcs_st, hcs_res, hfp2_res]
  have hfc_mc : memoryCost (readCandFpAtGenProg (((wp, base), b), loc_last)) s ≤
      2 * hashEvalCostWhp c + 5 := by
    unfold readCandFpAtGenProg
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hcs_st, hcs_res, hcs_mc]
    have hfp2_mc' : memoryCost (fpAtGenProg ((((wp, base), fs.rebCandSalt), b), loc_last)) s ≤
        2 * hashEvalCostWhp c + 4 := hfp2_mc
    omega
  have hfc_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
      (readCandFpAtGenProg (((wp, base), b), loc_last)) := by
    unfold readCandFpAtGenProg
    refine validProg_bind hcs_vp ?_; rw [hcs_st, hcs_res]; exact hfp2_vp
  dsimp only
  unfold delMoveReadInfoGenProg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hsr_st, hsr_res, clientState_bind, hfl_st, hfl_res,
      clientState_bind, hfc_st, hfc_res]; rfl
  · rw [clientResult_bind, hsr_st, hsr_res, clientResult_bind, hfl_st, hfl_res,
      clientResult_bind, hfc_st, hfc_res]; rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hsr_st, hsr_res, hfl_st, hfl_res, hfc_st, hfc_res, memoryCost_pure]
    dsimp only [wp] at hsr_mc hfl_mc hfc_mc ⊢
    omega
  · refine validProg_bind hsr_vp ?_; rw [hsr_st, hsr_res]
    refine validProg_bind hfl_vp ?_; rw [hfl_st, hfl_res]
    refine validProg_bind hfc_vp ?_; rw [hfc_st, hfc_res]
    exact validProg_pure _

theorem realizes_delMoveReadInfoGen :
    Realizes .exact delMoveReadInfoGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × (ℕ × ℕ))))
      CoordHashPre
      (fun _ _ => 0) := by
  unfold delMoveReadInfoGenProg
  have hsr := realizes_delMoveReadStRkGen
  have hfl := realizes_readLiveFpAtGen
  have hfc := realizes_readCandFpAtGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, loc_last⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, heq_wp, hseed, hrep, hq_all, hb, hll, hbp_ll⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hst_l, hres_l, _, _⟩ := readFastLocGenProg_spec henv hb hll hrep (s := s)
    obtain ⟨hrk_st, hrk_res, _, _⟩ := rKeyAtGenProg_spec henv hseed hrep hb hll hbp_ll (s := s)
    obtain ⟨hs1_st, hs1_res, _, _⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 1 < 10) hrep (s := s)
    simp only [getBktField] at hs1_res
    obtain ⟨hfp1_st, _, _, _⟩ :=
      fpAtGenProg_spec henv hseed hrep hb hll hbp_ll (salt := fs.bktSalt b) (s := s)
    have hsr_st : (Memory.spec 0).clientState s
        (delMoveReadStRkGenProg (((mkWhpParams c U V w n_max, base), b), loc_last)) = s := by
      unfold delMoveReadStRkGenProg; dsimp only; rw [hcp_eq]
      rw [clientState_bind, hst_l, hres_l, clientState_bind, hrk_st, hrk_res]; rfl
    have hfl_st : (Memory.spec 0).clientState s
        (readLiveFpAtGenProg (((mkWhpParams c U V w n_max, base), b), loc_last)) = s := by
      unfold readLiveFpAtGenProg; dsimp only; rw [hcp_eq]
      rw [clientState_bind, hs1_st, hs1_res, hfp1_st]
    rw [hsr_st] at *
    rw [hfl_st] at *
    exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hq_all, hb, hll, hbp_ll⟩
  )

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
