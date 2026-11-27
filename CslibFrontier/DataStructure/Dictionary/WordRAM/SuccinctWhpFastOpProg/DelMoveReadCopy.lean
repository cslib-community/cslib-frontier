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
  realize [realizes_bufInsertGen]
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
  unfold delMoveBufGenProg
  simp only [pure_bind]
  split_ifs with hs2 hs3
  · obtain ⟨hna0, hia0, m0, hv0⟩ := h2 hs2
    exact bufInsertGenProg_fastStep henv (Or.inl rfl) hseed hrep hv0 hna0 hia0 hb hld
  · obtain ⟨hna1, hia1, m1, hv1⟩ := h3 hs3
    exact bufInsertGenProg_fastStep henv (Or.inr rfl) hseed hrep hv1 hna1 hia1 hb hld
  · exact ⟨Nat.zero_le _, validProg_pure _, FastStateStep.refl hseed hrep⟩


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
  realize [realizes_physSlotGen, realizes_readQuotGen, realizes_readValGen,
    realizes_writeQuotGen, realizes_writeValGen, realizes_writeFastLocGen]
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
  unfold delCopySlotGenProg
  exact CostBoundedStep.elim
    (.bind ⟨hps1_st, hps1_res, hps1_mc, hps1_vp⟩ <|
      .bind ⟨hps2_st, hps2_res, hps2_mc, hps2_vp⟩ <|
      .bind ⟨hrq_st, hrq_res, hrq_mc.le, hrq_vp⟩ <|
      .bind ⟨hrv_st, hrv_res, hrv_mc.le, hrv_vp⟩ <|
      .bind ⟨rfl, rfl, hwq_mc.le, hwq_vp⟩ <|
      .bind ⟨rfl, rfl, hwv_mc.le, hwv_vp⟩ ⟨rfl, rfl, hwl_mc.le, hwl_vp⟩)
    (by omega) ((hwq_step.trans hwv_step).trans hwl_step)

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
  realize [realizes_readFastLocGen, realizes_rKeyAtGen]
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, loc_last⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hq_all, hb, hll, hbp_ll⟩ := h
    obtain rfl := henv.2.2.1
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hst_l, _, _, _⟩ := readFastLocGenProg_spec henv hb hll hrep (s := s)
    obtain ⟨hrk_st, _, _, _⟩ := rKeyAtGenProg_spec henv hseed hrep hb hll hbp_ll (s := s)
    simp only [hcp_eq, hst_l, hrk_st, wp_large_M hth, wp_large_totalLoc hth] at *
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
  realize [realizes_readBktFieldGen, realizes_fpAtGen]
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, loc_last⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hq_all, hb, hll, hbp_ll⟩ := h
    obtain rfl := henv.2.2.1
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hs1_st, _, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 1 < 10)
      hrep (s := s)
    simp only [hcp_eq, hs1_st, wp_large_M hth] at *
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
  realize [realizes_readHdr, realizes_fpAtGen]
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, loc_last⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hq_all, hb, hll, hbp_ll⟩ := h
    obtain rfl := henv.2.2.1
    obtain ⟨hcs_st, _, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebCandSalt)
      (by dsimp [hdrRebCandSalt, largeSpaceWhp]; omega) (s := s)
    simp only [hcs_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hq_all, hb, hll, hbp_ll⟩
  )

private theorem delMoveReadStRkGenProg_step {c U V w n_max base b loc_last : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hb : b < numBucketsWhp n_max)
    (hll : loc_last < totalLocalCoordsWhp n_max)
    (hbp_ll : capFrontWhp n_max ≤ loc_last →
      fs.backPtr b (loc_last - capFrontWhp n_max) < poolSizeWhp n_max) :
    CostBoundedStep w (base + largeSpaceWhp c U V w n_max) s
      (delMoveReadStRkGenProg (((mkWhpParams c U V w n_max, base), b), loc_last)) s
      (fs.locState b loc_last, fs.rKeyAt c U n_max θ b loc_last)
      (hashEvalCostWhp c + 7) := by
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr henv.2.2.2.1]
  obtain ⟨hst_l, hres_l, hmc_l, hvp_l⟩ := readFastLocGenProg_spec henv hb hll hrep (s := s)
  obtain ⟨hrk_st, hrk_res, hrk_mc, hrk_vp⟩ :=
    rKeyAtGenProg_spec henv hseed hrep hb hll hbp_ll (s := s)
  rw [delMoveReadStRkGenProg, hwp1]
  exact .mono (.bind ⟨hst_l, hres_l, hmc_l.le, hvp_l⟩ <|
    .bind ⟨hrk_st, hrk_res, hrk_mc, hrk_vp⟩ <| .pure _ _) (by omega)

private theorem readLiveFpAtGenProg_step {c U V w n_max base b loc_last : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hb : b < numBucketsWhp n_max)
    (hll : loc_last < totalLocalCoordsWhp n_max)
    (hbp_ll : capFrontWhp n_max ≤ loc_last →
      fs.backPtr b (loc_last - capFrontWhp n_max) < poolSizeWhp n_max) :
    CostBoundedStep w (base + largeSpaceWhp c U V w n_max) s
      (readLiveFpAtGenProg (((mkWhpParams c U V w n_max, base), b), loc_last)) s
      (fs.fpAt c U n_max θ (fs.bktSalt b) b loc_last)
      (2 * hashEvalCostWhp c + 6) := by
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr henv.2.2.2.1]
  obtain ⟨hs1_st, hs1_res, hs1_mc, hs1_vp⟩ :=
    readBktFieldGenProg_spec henv hb (by decide : 1 < 10) hrep (s := s)
  simp only [getBktField] at hs1_res
  obtain ⟨hfp1_st, hfp1_res, hfp1_mc, hfp1_vp⟩ :=
    fpAtGenProg_spec henv hseed hrep hb hll hbp_ll (salt := fs.bktSalt b) (s := s)
  rw [readLiveFpAtGenProg, hwp1]
  exact .mono (.bind ⟨hs1_st, hs1_res, hs1_mc.le, hs1_vp⟩ ⟨hfp1_st, hfp1_res, hfp1_mc, hfp1_vp⟩)
    (by omega)

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
  have hsr := delMoveReadStRkGenProg_step henv hseed hrep hb hll hbp_ll (s := s)
  have hfl := readLiveFpAtGenProg_step henv hseed hrep hb hll hbp_ll (s := s)
  obtain ⟨hcs_st, hcs_res, hcs_mc, hcs_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebCandSalt)
    (by dsimp [hdrRebCandSalt, largeSpaceWhp]; omega) (s := s)
  rw [hrep.2.2.2.2.2.2.2.2.2.1] at hcs_res
  obtain ⟨hfp2_st, hfp2_res, hfp2_mc, hfp2_vp⟩ :=
    fpAtGenProg_spec henv hseed hrep hb hll hbp_ll (salt := fs.rebCandSalt) (s := s)
  have htot : CostBoundedStep w (base + largeSpaceWhp c U V w n_max) s
      (delMoveReadInfoGenProg (((mkWhpParams c U V w n_max, base), b), loc_last)) s
      (fs.locState b loc_last,
       (fs.rKeyAt c U n_max θ b loc_last,
        (fs.fpAt c U n_max θ (fs.bktSalt b) b loc_last,
         fs.fpAt c U n_max θ fs.rebCandSalt b loc_last)))
      (5 * hashEvalCostWhp c + 18) := by
    unfold delMoveReadInfoGenProg readCandFpAtGenProg
    exact .mono (.bind hsr <| .bind hfl <|
      .bind (.bind ⟨hcs_st, hcs_res, hcs_mc.le, hcs_vp⟩ ⟨hfp2_st, hfp2_res, hfp2_mc, hfp2_vp⟩) <|
      .pure _ _) (by omega)
  exact ⟨htot.clientState_eq, htot.clientResult_eq, htot.memoryCost_le, htot.validProg⟩

theorem realizes_delMoveReadInfoGen :
    Realizes .exact delMoveReadInfoGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × (ℕ × ℕ))))
      CoordHashPre
      (fun _ _ => 0) := by
  unfold delMoveReadInfoGenProg
  realize [realizes_delMoveReadStRkGen, realizes_readLiveFpAtGen, realizes_readCandFpAtGen]
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, b⟩, loc_last⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hq_all, hb, hll, hbp_ll⟩ := h
    obtain rfl := henv.2.2.1
    try rw [(delMoveReadStRkGenProg_step henv hseed hrep hb hll hbp_ll (s := s)).clientState_eq]
    try rw [(readLiveFpAtGenProg_step henv hseed hrep hb hll hbp_ll (s := s)).clientState_eq]
    exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hq_all, hb, hll, hbp_ll⟩
  )

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
