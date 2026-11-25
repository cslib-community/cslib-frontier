/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpHashProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.Frame
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.HeaderBkt
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg.SlotArrays
import CslibFrontier.Tactic.Realize

/-!
# Fast-Mode Coordinate Lookup (`fastFindLocBqGenProg`) and Value Query (`fastQueryGenProg`)

This module implements worst-case `O_c(1)` fast-mode coordinate lookup and value query
`Memory.Prog` subroutines and their `Realizes .exact` certificates on `FastMemRep`, probing
`buf curEp`, `buf oldEp` (when `rebStage ≤ 3`), and `liveSlice[b]` with key verification via
`matchesKeyGenProg`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.ValidFastMemPre`: shared memory-state
  precondition for foreground fast-mode operations under `ValidFastState`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fastFindLocBqGenProg`,
  `fastQueryGenProg`: parameter-free `O_c(1)` lookup and query subroutines.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_fastFindLocBqGen`,
  `fastFindLocBqGenProg_spec`, `realizes_fastQueryGen`, `fastQueryGenProg_spec`.
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
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

attribute [local simp] clientResult_pure_whp clientState_pure_whp

/-! ## Section 1: Key Verification and Candidate Probe Helpers -/

/-- Check `fs.matchesKey n_max b q_val b_cand loc`
(`d = (((cp, base), (b, q_val)), (b_cand, loc))`). -/
@[irreducible] private def matchesKeyGenProg :
    ((WhpCoreParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog ℕ
  | (((cp, base), (b, q_val)), (b_cand, loc)) => do
    let z0 ← pure 0
    let z1 ← pure 1
    if b_cand = b then do
      let cnt ← readBktFieldGenProg (((cp, base), b), z0)
      if loc < cnt then do
        let p ← physSlotGenProg (((cp, base), b), loc)
        let q_got ← readQuotGenProg ((cp, base), p)
        if q_got = q_val then pure z1 else pure z0
      else
        pure z0
    else
      pure z0

/-- Precondition for `matchesKeyGenProg`. -/
private def MatchesKeyPre (w : ℕ) :
    ((WhpCoreParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.State → Prop
  | (((cp, base), (b, _)), (_, _)), s =>
    ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
      WhpLargeEnv c U V w₀ n_max w base ∧
      cp = mkWhpCoreParams c U V w₀ n_max ∧
      FastMemRep base c U V w₀ n_max fs s.mem ∧
      b < numBucketsWhp n_max ∧
      fs.bktCount b ≤ totalLocalCoordsWhp n_max ∧
      (∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max)

private theorem realizes_matchesKeyGen :
    Realizes .exact matchesKeyGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      MatchesKeyPre
      (fun _ _ => 0) := by
  unfold matchesKeyGenProg
  have hrb := realizes_readBktFieldGen
  have hps := realizes_physSlotGen
  have hrq := realizes_readQuotGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, ⟨b, q_val⟩⟩, ⟨b_cand, loc⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hb, hcnt_le, hbp_v⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    obtain ⟨hrb_st, hrb_res, _, _⟩ := readBktFieldGenProg_spec henv hb (by decide : 0 < 10)
      hrep (s := s)
    dsimp only [getBktField] at hrb_res
    simp only [hrb_st, hrb_res, wp_large_M hth, wp_large_nMax hth] at *
    first
    | decide
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | exact hb
    | refine ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, by omega, fun hcf => hbp_v _ (by omega)⟩
    | (obtain ⟨hps_st, hps_res, hps_lt, _, _⟩ := physSlotGenProg_spec henv hb (by omega : loc < _)
         (fun hcf => hbp_v _ (by omega)) hrep (s := s)
       simp only [hps_st, hps_res] at *
       exact hps_lt)
  )

private theorem matchesKeyGenProg_spec {c U V w n_max base b q_val b_cand loc : ℕ}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hb : b < numBucketsWhp n_max)
    (hcnt_le : fs.bktCount b ≤ totalLocalCoordsWhp n_max)
    (hbp_v : ∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max) :
    let prog := matchesKeyGenProg
      (((mkWhpCoreParams c U V w n_max, base), (b, q_val)), (b_cand, loc))
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (if fs.matchesKey n_max b q_val b_cand loc then 1 else 0) ∧
    memoryCost prog s ≤ 6 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  unfold matchesKeyGenProg FastState.matchesKey
  simp only [pure_bind]
  by_cases hbb : b_cand = b
  · simp only [hbb, ↓reduceIte, beq_self_eq_true, Bool.true_and]
    obtain ⟨hc_st, hc_res, hc_mc, hc_vp⟩ :=
      readBktFieldGenProg_spec henv hb (by decide : 0 < 10) hrep (s := s)
    simp only [getBktField] at hc_res
    by_cases hlt : loc < fs.bktCount b
    · obtain ⟨hp_st, hp_res, hp_lt, hp_mc, hp_vp⟩ :=
        physSlotGenProg_spec henv hb (hlt.trans_le hcnt_le) (fun hcf => hbp_v _ (by omega))
          hrep (s := s)
      obtain ⟨hq_st, hq_res, hq_mc, hq_vp⟩ := readQuotGenProg_spec henv hp_lt hrep (s := s)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [clientState_bind, hc_st, hc_res]; simp only [hlt, ↓reduceIte]
        rw [clientState_bind, hp_st, hp_res, clientState_bind, hq_st, hq_res]
        split_ifs <;> rfl
      · rw [clientResult_bind, hc_st, hc_res]; simp only [hlt, ↓reduceIte, decide_true,
          Bool.true_and]
        rw [clientResult_bind, hp_st, hp_res, clientResult_bind, hq_st, hq_res]
        by_cases hqq : fs.quotArr (fs.physSlot n_max b loc) = q_val <;> simp [hqq]
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hc_st, hc_res, hc_mc]; simp only [hlt, ↓reduceIte, memoryCost_bind]
        rw [hp_st, hp_res, hq_st, hq_res, hq_mc]
        split_ifs <;> (change 2 + (_ + (2 + 0)) ≤ 6; omega)
      · refine validProg_bind hc_vp ?_
        rw [hc_st, hc_res]; simp only [hlt, ↓reduceIte]
        refine validProg_bind hp_vp ?_
        rw [hp_st, hp_res]
        refine validProg_bind hq_vp ?_
        rw [hq_st]
        split_ifs <;> exact validProg_pure _
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [clientState_bind, hc_st, hc_res, ite_eq_right hlt]; rfl
      · rw [clientResult_bind, hc_st, hc_res, ite_eq_right hlt]; simp [hlt]
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hc_st, hc_res, hc_mc, ite_eq_right hlt]; simp
      · refine validProg_bind hc_vp ?_
        rw [hc_st, hc_res, ite_eq_right hlt]; exact validProg_pure _
  · rw [ite_eq_right hbb]
    exact ⟨rfl, by simp [hbb], Nat.zero_le 6, validProg_pure _⟩

/-- Shared specification combinator for verifying a lookup candidate with `matchesKeyGenProg`. -/
private theorem verifyCand_spec {c U V w n_max base b q_val C : ℕ}
    {fs : FastState} {s : Memory.State} {β : Type}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hb : b < numBucketsWhp n_max)
    (hcnt_le : fs.bktCount b ≤ totalLocalCoordsWhp n_max)
    (hbp_v : ∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max)
    (lookupProg : Memory.Prog (ℕ × β)) (bOf locOf : β → ℕ) (zeroβ : β)
    (opt : Option β)
    (hlk_st : (Memory.spec 0).clientState s lookupProg = s)
    (hlk_res : (Memory.spec 0).clientResult s lookupProg =
      opt.elim (0, zeroβ) (fun x => (1, x)))
    (hlk_mc : memoryCost lookupProg s ≤ C)
    (hlk_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s lookupProg) :
    let cp := mkWhpCoreParams c U V w n_max
    let prog : Memory.Prog (ℕ × ℕ) :=
      lookupProg >>= fun lk =>
        if lk.1 = 1 then do
          let ok ← matchesKeyGenProg (((cp, base), (b, q_val)), (bOf lk.2, locOf lk.2))
          if ok = 1 then pure (1, locOf lk.2) else pure (0, 0)
        else pure (0, 0)
    let cand : Option ℕ :=
      opt.elim none fun x =>
        if fs.matchesKey n_max b q_val (bOf x) (locOf x) then some (locOf x) else none
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (match cand with | some loc => (1, loc) | none => (0, 0)) ∧
    memoryCost prog s ≤ C + 6 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  dsimp only
  cases opt with
  | none =>
    dsimp only [Option.elim] at hlk_res ⊢
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hlk_st, hlk_res]; rfl
    · rw [clientResult_bind, hlk_st, hlk_res]; rfl
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hlk_st, hlk_res]; simp only [zero_ne_one, ↓reduceIte, memoryCost_pure]; omega
    · refine validProg_bind hlk_vp ?_; rw [hlk_st, hlk_res]; exact validProg_pure _
  | some x =>
    dsimp only [Option.elim] at hlk_res ⊢
    obtain ⟨hm_st, hm_res, hm_mc, hm_vp⟩ :=
      matchesKeyGenProg_spec henv hrep hb hcnt_le hbp_v (q_val := q_val)
        (b_cand := bOf x) (loc := locOf x) (s := s)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hlk_st, hlk_res]; dsimp only; simp only [↓reduceIte]
      rw [clientState_bind, hm_st]; split_ifs <;> rfl
    · rw [clientResult_bind, hlk_st, hlk_res]; dsimp only; simp only [↓reduceIte]
      rw [clientResult_bind, hm_st, hm_res]
      cases hmk : fs.matchesKey n_max b q_val (bOf x) (locOf x) <;> simp
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hlk_st, hlk_res]; dsimp only; simp only [↓reduceIte, memoryCost_bind]
      rw [hm_st]
      have hm_mc' : memoryCost (matchesKeyGenProg
          (((mkWhpCoreParams c U V w n_max, base), (b, q_val)), (bOf x, locOf x))) s ≤ 6 := hm_mc
      split_ifs <;> (simp only [memoryCost_pure]; omega)
    · refine validProg_bind hlk_vp ?_; rw [hlk_st, hlk_res]; dsimp only; simp only [↓reduceIte]
      refine validProg_bind hm_vp ?_; rw [hm_st]; split_ifs <;> exact validProg_pure _

/-- Probe epoch buffer `ep` at `rKey` and verify `matchesKey`
(`d = ((((cp, base), ep), (b, q_val)), rKey)`). -/
@[irreducible] private def probeBufCandGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((((cp, base), ep), (b, q_val)), rKey) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let lk ← bufLookupGenProg (((cp, base), ep), rKey)
    let (hit, b_loc) := lk
    if hit = z1 then do
      let ok ← matchesKeyGenProg (((cp, base), (b, q_val)), b_loc)
      if ok = z1 then pure (z1, b_loc.2) else pure (z0, z0)
    else
      pure (z0, z0)

/-- Precondition for `probeBufCandGenProg`. -/
private def ProbeBufCandPre (w : ℕ) :
    (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | ((((cp, base), ep), (b, _)), _), s =>
    ∃ (c U V w₀ n_max : ℕ) (fs : FastState) (mapFn : ℕ → Option (ℕ × ℕ)),
      WhpLargeEnv c U V w₀ n_max w base ∧
      cp = mkWhpCoreParams c U V w₀ n_max ∧
      FastMemRep base c U V w₀ n_max fs s.mem ∧
      (ep = 0 ∨ ep = 1) ∧
      ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf ep) mapFn ∧
      b < numBucketsWhp n_max ∧
      fs.bktCount b ≤ totalLocalCoordsWhp n_max ∧
      (∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max)

private theorem realizes_probeBufCandGen :
    Realizes .exact probeBufCandGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      ProbeBufCandPre
      (fun _ _ => 0) := by
  unfold probeBufCandGenProg
  have hbl := realizes_bufLookupGen
  have hmk := realizes_matchesKeyGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, ep⟩, ⟨b, q_val⟩⟩, rKey⟩
    try dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, mapFn, henv, rfl, hrep, hep, hv, hb, hcnt_le, hbp_v⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    obtain ⟨hbl_st, _, _, _⟩ :=
      bufLookupGenProg_spec henv hep (hrep.buf_rep hep) hv (rKey := rKey) (s := s)
    simp only [hbl_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, fs.buf ep, mapFn, henv, rfl, hep, hrep.buf_rep hep, hv⟩
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hcnt_le, hbp_v⟩
  )

private theorem probeBufCandGenProg_spec {c U V w n_max base ep b q_val rKey : ℕ}
    {fs : FastState} {mapFn : ℕ → Option (ℕ × ℕ)} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf ep) mapFn)
    (hb : b < numBucketsWhp n_max)
    (hcnt_le : fs.bktCount b ≤ totalLocalCoordsWhp n_max)
    (hbp_v : ∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max) :
    let prog := probeBufCandGenProg
      ((((mkWhpCoreParams c U V w n_max, base), ep), (b, q_val)), rKey)
    let cand : Option ℕ :=
      match bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf ep) rKey with
      | some (b', loc) => if fs.matchesKey n_max b q_val b' loc then some loc else none
      | none => none
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (match cand with | some loc => (1, loc) | none => (0, 0)) ∧
    memoryCost prog s ≤ 2 * cTabWhp c + 14 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  obtain ⟨hl_st, hl_res, hl_mc, hl_vp⟩ :=
    bufLookupGenProg_spec henv hep (hrep.buf_rep hep) hv (rKey := rKey) (s := s)
  have hl_res' : (Memory.spec 0).clientResult s
      (bufLookupGenProg (((mkWhpCoreParams c U V w n_max, base), ep), rKey)) =
      (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf ep) rKey).elim
        (0, (0, 0)) (fun x => (1, x)) := by
    rw [hl_res]
    cases bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf ep) rKey <;> rfl
  have hvc := verifyCand_spec henv hrep hb hcnt_le hbp_v
    (bufLookupGenProg (((mkWhpCoreParams c U V w n_max, base), ep), rKey))
    Prod.fst Prod.snd (0, 0)
    (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf ep) rKey)
    hl_st hl_res' hl_mc hl_vp (q_val := q_val)
  dsimp only at hvc ⊢
  unfold probeBufCandGenProg
  simp only [pure_bind]
  have hcand_eq :
      (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf ep) rKey).elim none (fun x =>
        if fs.matchesKey n_max b q_val x.1 x.2 then some x.2 else none) =
      (match bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf ep) rKey with
       | some (b', loc) => if fs.matchesKey n_max b q_val b' loc then some loc else none
       | none => none) := by
    cases bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf ep) rKey <;> rfl
  rw [hcand_eq] at hvc
  exact ⟨hvc.1, hvc.2.1, hvc.2.2.1.trans (by omega), hvc.2.2.2⟩

/-- Lookup `fpOfSalt` in `liveSlice[b]` (`d = ((wp, base), (b, u_val))`). -/
@[irreducible] private def probeLiveLookupGenProg :
    (WhpParams × ℕ) × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ)
  | ((wp, base), (b, u_val)) => do
    let si ← readLiveSaltIdxGenProg ((wp.1, base), b)
    let hrt ← mkHashRtGenProg (wp, base)
    let fp ← fpOfSaltOptRtProg ((hrt, si.1), u_val)
    btreeLookupGenProg (((wp.1, base), si.2), fp)

private theorem realizes_probeLiveLookupGen :
    Realizes .exact probeLiveLookupGenProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((wp, base), (b, _)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (mapFn : ℕ → Option ℕ),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          b < numBucketsWhp n_max ∧
          fs.liveRole b < 3 ∧
          fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
          ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) mapFn)
      (fun _ _ => 0) := by
  unfold probeLiveLookupGenProg
  have hrs := realizes_readLiveSaltIdxGen
  have hmh := realizes_mkHashRtGen
  have hfp := realizes_fpOfSaltOptRt
  have hbt := realizes_btreeLookupGen
  realize
  all_goals (
    rcases d with ⟨⟨wp, base⟩, ⟨b, u_val⟩⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, mapFn, henv, heq_wp, hseed, hrep,
      hb, hlr, hins, hv_sl⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have h3M := (large_index_bounds hth).2.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hrs_st, hrs_res, _, _⟩ := readLiveSaltIdxGenProg_spec henv hb hrep (s := s)
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    obtain ⟨hfp_st, hfp_res, _, _⟩ :=
      fpOfSaltOptRtProg_spec (salt := fs.bktSalt b) (kv := u_val) henv hseed (s := s)
    have hlIdx : fs.liveSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.liveSliceIdx; omega
    have hfp_lt : (if hs : fs.bktSalt b < sMaxWhp c n_max then
        if hu : u_val < U then fpHash c U n_max θ.2 ⟨fs.bktSalt b, hs⟩ ⟨u_val, hu⟩ else 0
       else 0) < 2 ^ fpBitsWhp n_max := fpOfSaltOpt_lt c U n_max _ _ θ.2
    simp only [hcp_eq] at *
    simp only [hrs_st, hrs_res, hmh_st, hmh_res, hfp_st, hfp_res] at *
    first
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hlr⟩
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
    | exact ⟨c, U, V, w, n_max, fs.liveInsCount b, fs.slices (fs.liveSliceIdx b), mapFn,
        henv, rfl, hlIdx, hins, hrep.slice_rep hlIdx, hv_sl, hfp_lt⟩
  )

private theorem probeLiveLookupGenProg_spec {c U V w n_max base b u_val : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hb : b < numBucketsWhp n_max) (hlr : fs.liveRole b < 3)
    (hins : fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12)
    (hv_sl : ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) mapFn) :
    let prog := probeLiveLookupGenProg ((mkWhpParams c U V w n_max, base), (b, u_val))
    let fp := if hs : fs.bktSalt b < sMaxWhp c n_max then
      if hu : u_val < U then fpHash c U n_max θ.2 ⟨fs.bktSalt b, hs⟩ ⟨u_val, hu⟩ else 0
     else 0
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (match btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) fp with
       | some loc => (1, loc)
       | none => (0, 0)) ∧
    memoryCost prog s ≤ hashEvalCostWhp c + 266 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  obtain ⟨hrs_st, hrs_res, hrs_mc, hrs_vp⟩ := readLiveSaltIdxGenProg_spec henv hb hrep (s := s)
  obtain ⟨hmh_st, hmh_res, hmh_mc, hmh_vp⟩ :=
    mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hfp_st, hfp_res, hfp_mc, hfp_vp⟩ :=
    fpOfSaltOptRtProg_spec (salt := fs.bktSalt b) (kv := u_val) henv hseed (s := s)
  set fp := if hs : fs.bktSalt b < sMaxWhp c n_max then
    if hu : u_val < U then fpHash c U n_max θ.2 ⟨fs.bktSalt b, hs⟩ ⟨u_val, hu⟩ else 0
   else 0
  have hfp_lt : fp < 2 ^ fpBitsWhp n_max := fpOfSaltOpt_lt c U n_max _ _ θ.2
  have hlIdx : fs.liveSliceIdx b < 3 * numBucketsWhp n_max := by
    unfold FastState.liveSliceIdx; omega
  obtain ⟨hbt_st, hbt_res, hbt_mc, hbt_vp⟩ :=
    btreeLookupGenProg_spec henv hlIdx hins (hrep.slice_rep hlIdx) hv_sl hfp_lt (s := s)
  rw [← hv_sl.lookup_eq hth hins hfp_lt] at hbt_res
  dsimp only
  unfold probeLiveLookupGenProg
  dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max from hwp1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hrs_st, hrs_res, clientState_bind, hmh_st, hmh_res,
      clientState_bind, hfp_st, hfp_res, hbt_st]
  · rw [clientResult_bind, hrs_st, hrs_res, clientResult_bind, hmh_st, hmh_res,
      clientResult_bind, hfp_st, hfp_res, hbt_res]
    cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      (fs.slices (fs.liveSliceIdx b)) fp <;> rfl
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hrs_st, hrs_res, hrs_mc, hmh_st, hmh_res, hmh_mc, hfp_st, hfp_res]
    have hfp_mc' : memoryCost (fpOfSaltOptRtProg ((mkHashRt c U w n_max base, fs.bktSalt b),
        u_val)) s ≤ hashEvalCostWhp c := hfp_mc
    have hbt_mc' : memoryCost (btreeLookupGenProg (((mkWhpCoreParams c U V w n_max, base),
        fs.liveSliceIdx b), fp)) s ≤ 262 := hbt_mc
    dsimp only
    omega
  · refine validProg_bind hrs_vp ?_; rw [hrs_st, hrs_res]
    refine validProg_bind hmh_vp ?_; rw [hmh_st, hmh_res]
    refine validProg_bind hfp_vp ?_; rw [hfp_st, hfp_res]
    exact hbt_vp

/-- Probe `liveSlice[b]` for key `u_val` and verify `matchesKey`
(`d = (((wp, base), (b, q_val)), u_val)`). -/
@[irreducible] private def probeLiveCandGenProg :
    ((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | (((wp, base), (b, q_val)), u_val) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let lk ← probeLiveLookupGenProg ((wp, base), (b, u_val))
    if lk.1 = z1 then do
      let ok ← matchesKeyGenProg (((wp.1, base), (b, q_val)), (b, lk.2))
      if ok = z1 then pure (z1, lk.2) else pure (z0, z0)
    else
      pure (z0, z0)

/-- Precondition for `probeLiveCandGenProg`. -/
private def ProbeLiveCandPre (w : ℕ) :
    ((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | (((wp, base), (b, _)), _), s =>
    ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (mapFn : ℕ → Option ℕ),
      WhpLargeEnv c U V w₀ n_max w base ∧
      wp = mkWhpParams c U V w₀ n_max ∧
      SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
      FastMemRep base c U V w₀ n_max fs s.mem ∧
      b < numBucketsWhp n_max ∧
      fs.liveRole b < 3 ∧
      fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
      ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) mapFn ∧
      fs.bktCount b ≤ totalLocalCoordsWhp n_max ∧
      (∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max)

private theorem realizes_probeLiveCandGen :
    Realizes .exact probeLiveCandGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      ProbeLiveCandPre
      (fun _ _ => 0) := by
  unfold probeLiveCandGenProg
  have hpl := realizes_probeLiveLookupGen
  have hmk := realizes_matchesKeyGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, ⟨b, q_val⟩⟩, u_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, mapFn, henv, heq_wp, hseed, hrep,
      hb, hlr, hins, hv_sl, hcnt_le, hbp_v⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hlk_st, _, _, _⟩ :=
      probeLiveLookupGenProg_spec (u_val := u_val) henv hseed hrep hb hlr hins hv_sl (s := s)
    simp only [hcp_eq, hlk_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, θ, fs, mapFn, henv, rfl, hseed, hrep, hb, hlr, hins, hv_sl⟩
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hcnt_le, hbp_v⟩
  )

private theorem probeLiveCandGenProg_spec {c U V w n_max base b q_val : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hb : b < numBucketsWhp n_max) (hlr : fs.liveRole b < 3)
    (hins : fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12)
    (hv_sl : ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) mapFn)
    (hcnt_le : fs.bktCount b ≤ totalLocalCoordsWhp n_max)
    (hbp_v : ∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max)
    (u : Fin U) :
    let prog := probeLiveCandGenProg (((mkWhpParams c U V w n_max, base), (b, q_val)), u.val)
    let fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
    let cand : Option ℕ :=
      match btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) fp with
      | some loc => if fs.matchesKey n_max b q_val b loc then some loc else none
      | none => none
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (match cand with | some loc => (1, loc) | none => (0, 0)) ∧
    memoryCost prog s ≤ hashEvalCostWhp c + 272 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  obtain ⟨hlk_st, hlk_res, hlk_mc, hlk_vp⟩ :=
    probeLiveLookupGenProg_spec (u_val := u.val) henv hseed hrep hb hlr hins hv_sl (s := s)
  set fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
  have hfp_eq : (if hs : fs.bktSalt b < sMaxWhp c n_max then
      if hu : u.val < U then fpHash c U n_max θ.2 ⟨fs.bktSalt b, hs⟩ ⟨u.val, hu⟩ else 0
     else 0) = fp := by
    dsimp only [fp, fpOfSalt]
    split_ifs with hs hu
    · rfl
    · exact absurd u.isLt hu
    · rfl
  rw [hfp_eq] at hlk_res
  have hlk_res' : (Memory.spec 0).clientResult s
      (probeLiveLookupGenProg ((mkWhpParams c U V w n_max, base), (b, u.val))) =
      (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (fs.slices (fs.liveSliceIdx b)) fp).elim (0, 0) (fun x => (1, x)) := by
    rw [hlk_res]
    cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      (fs.slices (fs.liveSliceIdx b)) fp <;> rfl
  have hvc := verifyCand_spec henv hrep hb hcnt_le hbp_v
    (probeLiveLookupGenProg ((mkWhpParams c U V w n_max, base), (b, u.val)))
    (fun _ => b) (fun x => x) 0
    (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      (fs.slices (fs.liveSliceIdx b)) fp)
    hlk_st hlk_res' hlk_mc hlk_vp (q_val := q_val)
  dsimp only at hvc ⊢
  unfold probeLiveCandGenProg
  dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max from hwp1]
  simp only [pure_bind]
  have hcand_eq :
      (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (fs.slices (fs.liveSliceIdx b)) fp).elim none (fun x =>
          if fs.matchesKey n_max b q_val b x then some x else none) =
      (match btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) fp with
       | some loc => if fs.matchesKey n_max b q_val b loc then some loc else none
       | none => none) := by
    cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      (fs.slices (fs.liveSliceIdx b)) fp <;> rfl
  rw [hcand_eq] at hvc
  exact ⟨hvc.1, hvc.2.1, hvc.2.2.1.trans (by omega), hvc.2.2.2⟩

/-! ## Section 2: `ValidFastMemPre`, `fastFindLocBqGenProg`, and `fastQueryGenProg` -/

/-- Shared memory-state precondition for foreground fast-mode operations under `ValidFastState`. -/
@[expose] def ValidFastMemPre (w : ℕ) (wp : WhpParams) (base : ℕ) (s : Memory.State) : Prop :=
  ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
    WhpLargeEnv c U V w₀ n_max w base ∧
    wp = mkWhpParams c U V w₀ n_max ∧
    SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
    FastMemRep base c U V w₀ n_max fs s.mem ∧
    ValidFastState c U V n_max θ fs dict

/-- Probe `buf oldEp` when `rebStage ≤ 3` (`d = (((cp, base), (b, q_val)), rKey)`). -/
@[irreducible] private def probeOldBufCandGenProg :
    ((WhpCoreParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | (((cp, base), (b, q_val)), rKey) => do
    let z0 ← pure 0
    let z3 ← pure 3
    let stg ← readHdrProg (base, hdrRebStage)
    if stg ≤ z3 then do
      let oldEp ← readOldEpProg base
      probeBufCandGenProg ((((cp, base), oldEp), (b, q_val)), rKey)
    else
      pure (z0, z0)

private def ProbeOldBufCandPre (w : ℕ) :
    ((WhpCoreParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | (((cp, base), (b, _)), _), s =>
    ∃ (c U V w₀ n_max : ℕ) (fs : FastState),
      WhpLargeEnv c U V w₀ n_max w base ∧
      cp = mkWhpCoreParams c U V w₀ n_max ∧
      FastMemRep base c U V w₀ n_max fs s.mem ∧
      (fs.curEp = 0 ∨ fs.curEp = 1) ∧
      (fs.rebStage ≤ 3 → ∃ oldMap,
        ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap) ∧
      b < numBucketsWhp n_max ∧
      fs.bktCount b ≤ totalLocalCoordsWhp n_max ∧
      (∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max)

private theorem realizes_probeOldBufCandGen :
    Realizes .exact probeOldBufCandGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      ProbeOldBufCandPre
      (fun _ _ => 0) := by
  unfold probeOldBufCandGenProg
  have hrh := realizes_readHdr
  have hro := realizes_readOldEp
  have hpb := realizes_probeBufCandGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨cp, base⟩, ⟨b, q_val⟩⟩, rKey⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, fs, henv, rfl, hrep, hce_or, hbo_fn, hb, hcnt_le, hbp_v⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hth := henv.2.2.2.1
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    have hlog_w := henv.log_lt_w
    have hbm_ge := bMinWhp_le_log hth
    have hbmin := le_bMinWhp c
    have hw2 : 2 ≤ w := by omega
    obtain ⟨hst_st, hst_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage) (s := s)
      (by dsimp only [hdrRebStage]; omega)
    rw [hrep.2.2.2.2.2.1] at hst_res
    obtain ⟨hro_st, hro_res, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max)
      (by dsimp [hdrCurEp]; omega) hce_or hrep.2.2.2.1 (s := s)
    have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
      rcases hce_or with h0 | h1
      · simp [FastState.oldEp, h0]
      · simp [FastState.oldEp, h1]
    simp only [hst_st, hst_res] at *
    simp only [hro_st, hro_res] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact hw2
    | (obtain ⟨oldMap, hv_old⟩ := hbo_fn (by omega)
       exact ⟨c, U, V, w, n_max, fs, oldMap, henv, rfl, hrep, hold_or, hv_old,
         hb, hcnt_le, hbp_v⟩)
  )

private theorem probeOldBufCandGenProg_spec {c U V w n_max base b q_val rKey : ℕ}
    {fs : FastState} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hce_or : fs.curEp = 0 ∨ fs.curEp = 1)
    (hbo_fn : fs.rebStage ≤ 3 → ∃ oldMap,
      ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap)
    (hb : b < numBucketsWhp n_max)
    (hcnt_le : fs.bktCount b ≤ totalLocalCoordsWhp n_max)
    (hbp_v : ∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max) :
    let prog := probeOldBufCandGenProg
      (((mkWhpCoreParams c U V w n_max, base), (b, q_val)), rKey)
    let cand : Option ℕ :=
      if fs.rebStage ≤ 3 then
        match bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey with
        | some (b', loc) => if fs.matchesKey n_max b q_val b' loc then some loc else none
        | none => none
      else none
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (match cand with | some loc => (1, loc) | none => (0, 0)) ∧
    memoryCost prog s ≤ 2 * cTabWhp c + 16 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  obtain ⟨hst_st, hst_res, hst_mc, hst_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrRebStage) (s := s)
    (by dsimp only [largeSpaceWhp, hdrRebStage]; omega)
  rw [hrep.2.2.2.2.2.1] at hst_res
  dsimp only
  unfold probeOldBufCandGenProg
  simp only [pure_bind]
  by_cases hle3 : fs.rebStage ≤ 3
  · obtain ⟨hro_st, hro_res, hro_mc, hro_vp⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max)
      (by dsimp only [largeSpaceWhp, hdrCurEp]; omega) hce_or hrep.2.2.2.1 (s := s)
    have hold_or : fs.oldEp = 0 ∨ fs.oldEp = 1 := by
      rcases hce_or with h0 | h1
      · simp [FastState.oldEp, h0]
      · simp [FastState.oldEp, h1]
    obtain ⟨oldMap, hv_old⟩ := hbo_fn hle3
    obtain ⟨hp_st, hp_res, hp_mc, hp_vp⟩ :=
      probeBufCandGenProg_spec henv hold_or hrep hv_old hb hcnt_le hbp_v
        (q_val := q_val) (rKey := rKey) (s := s)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hst_st, hst_res, ite_eq_left hle3,
        clientState_bind, hro_st, hro_res, hp_st]
    · rw [clientResult_bind, hst_st, hst_res, ite_eq_left hle3,
        clientResult_bind, hro_st, hro_res, hp_res, ite_eq_left hle3]
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_st, hst_res, hst_mc, ite_eq_left hle3, memoryCost_bind, hro_st, hro_res, hro_mc]
      omega
    · refine validProg_bind hst_vp ?_; rw [hst_st, hst_res, ite_eq_left hle3]
      refine validProg_bind hro_vp ?_; rw [hro_st, hro_res]
      exact hp_vp
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hst_st, hst_res, ite_eq_right hle3]; rfl
    · rw [clientResult_bind, hst_st, hst_res, ite_eq_right hle3, ite_eq_right hle3]; rfl
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hst_st, hst_res, hst_mc, ite_eq_right hle3]; simp only [memoryCost_pure]; omega
    · refine validProg_bind hst_vp ?_; rw [hst_st, hst_res, ite_eq_right hle3]
      exact validProg_pure _

/-- Inner lookup helper given precomputed `(b, q_val)` (`d = (((wp, base), (b, q_val)), u_val)`). -/
@[irreducible] def fastFindLocBqGenProg :
    ((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog (ℕ × ℕ)
  | (((wp, base), (b, q_val)), u_val) => do
    let z1 ← pure 1
    let hrt ← mkHashRtGenProg (wp, base)
    let rKey ← fpReducedKeyOptRtProg (hrt, u_val)
    let curEp ← readHdrProg (base, hdrCurEp)
    let c1 ← probeBufCandGenProg ((((wp.1, base), curEp), (b, q_val)), rKey)
    if c1.1 = z1 then
      pure c1
    else do
      let c2 ← probeOldBufCandGenProg (((wp.1, base), (b, q_val)), rKey)
      if c2.1 = z1 then
        pure c2
      else
        probeLiveCandGenProg (((wp, base), (b, q_val)), u_val)

theorem realizes_fastFindLocBqGen :
    Realizes .exact fastFindLocBqGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w (((wp, base), (b, _)), _) s =>
        ValidFastMemPre w wp base s ∧ b < wpM wp.1)
      (fun _ _ => 0) := by
  unfold fastFindLocBqGenProg
  have hmh := realizes_mkHashRtGen
  have hrk := realizes_fpReducedKeyOptRt
  have hrh := realizes_readHdr
  have hpb := realizes_probeBufCandGen
  have hpo := realizes_probeOldBufCandGen
  have hpl := realizes_probeLiveCandGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, ⟨b, q_val⟩⟩, u_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv⟩, hb_wp⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    have hb : b < numBucketsWhp n_max := by
      rw [hcp_eq, wp_large_M hth] at hb_wp; exact hb_wp
    have hm2 : s.mem (base + hdrCurEp) = fs.curEp := hrep.2.2.2.1
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    obtain ⟨hrk_st, _, _, _⟩ :=
      fpReducedKeyOptRtProg_spec (kv := u_val) henv hseed (s := s)
    have h32_sp : 32 ≤ largeSpaceWhp c U V w n_max := by dsimp only [largeSpaceWhp]; omega
    obtain ⟨hce_st, hce_res, _, _⟩ := readHdrProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrCurEp) (s := s)
      (by dsimp only [hdrCurEp]; omega)
    obtain ⟨_, _, curMap, hv_cur, _⟩ := hv.bufCur_valid
    have hcnt_le := hv.bktCount_le b hb
    have hbp_v : ∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max :=
      fun k hk => (hv.backPtr_valid b hb k hk).1
    have hbo_fn : fs.rebStage ≤ 3 → ∃ oldMap,
        ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap := by
      intro hle3
      have hbo := hv.bufOld_valid
      rw [ite_eq_left hle3] at hbo
      obtain ⟨_, _, oldMap, hv_old, _⟩ := hbo
      exact ⟨oldMap, hv_old⟩
    set rk_res := (Memory.spec 0).clientResult s
      (fpReducedKeyOptRtProg (mkHashRt c U w n_max base, u_val))
    obtain ⟨hc1_st, _, _, _⟩ := probeBufCandGenProg_spec henv hv.curEp_or hrep hv_cur hb hcnt_le
      hbp_v (q_val := q_val) (rKey := rk_res) (s := s)
    obtain ⟨hc2_st, _, _, _⟩ := probeOldBufCandGenProg_spec henv hrep hv.curEp_or hbo_fn
      hb hcnt_le hbp_v (q_val := q_val) (rKey := rk_res) (s := s)
    dsimp only [rk_res] at hc1_st hc2_st
    simp only [hcp_eq] at *
    simp only [hmh_st, hmh_res] at *
    simp only [hrk_st] at *
    simp only [hce_st, hce_res, hm2] at *
    simp only [hc1_st] at *
    simp only [hc2_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
    | exact ⟨c, U, V, w, n_max, fs, curMap, henv, rfl, hrep, hv.curEp_or, hv_cur,
        hb, hcnt_le, hbp_v⟩
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hv.curEp_or, hbo_fn, hb, hcnt_le, hbp_v⟩
    | (obtain ⟨liveMap, hv_live, _⟩ := hv.live_valid b hb
       have hins := liveInsCount_le_eight hv.toCore hb (hv.overmars_valid b hb)
       have hl_role := (hv.roles_valid b hb).1
       exact ⟨c, U, V, w, n_max, θ, fs, liveMap, henv, rfl, hseed, hrep,
         hb, hl_role, hins, hv_live, hcnt_le, hbp_v⟩)
  )

private def evalBufCand (n_max b q_val : ℕ) (fs : FastState) :
    Option (ℕ × ℕ) → Option ℕ
  | some (b', loc) => if fs.matchesKey n_max b q_val b' loc then some loc else none
  | none => none

private theorem fastFindLoc_cases (c U n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState)
    (u : Fin U) :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let q_val := keyQuotient (bWhp n_max) u.val
    let rKey := fpReducedKey c U n_max θ.2 u
    let fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
    let c1 := evalBufCand n_max b q_val fs
      (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey)
    let c2 :=
      if fs.rebStage ≤ 3 then
        evalBufCand n_max b q_val fs
          (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey)
      else none
    let c3 : Option ℕ :=
      match btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) fp with
      | some loc => if fs.matchesKey n_max b q_val b loc then some loc else none
      | none => none
    (∀ loc, c1 = some loc → fastFindLoc c U n_max θ fs u = some loc) ∧
    (∀ loc, c1 = none → c2 = some loc → fastFindLoc c U n_max θ fs u = some loc) ∧
    (c1 = none → c2 = none →
      (match fastFindLoc c U n_max θ fs u with | some loc => (1, loc) | none => (0, 0)) =
      (match c3 with | some loc => (1, loc) | none => (0, 0))) := by
  dsimp only [fastFindLoc, evalBufCand]
  set b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
  set q_val := keyQuotient (bWhp n_max) u.val
  set rKey := fpReducedKey c U n_max θ.2 u
  set fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
  cases bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey with
  | none =>
    cases bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey with
    | none =>
      cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) fp with
      | none => split_ifs <;> simp
      | some l3 =>
        dsimp only
        rcases Bool.eq_false_or_eq_true (fs.matchesKey n_max b q_val b l3) with h3 | h3 <;>
          (rw [h3]; split_ifs <;> simp)
    | some p2 =>
      rcases p2 with ⟨b2, l2⟩; dsimp only
      rcases Bool.eq_false_or_eq_true (fs.matchesKey n_max b q_val b2 l2) with h2 | h2 <;>
        (rw [h2];
         cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
           (fs.slices (fs.liveSliceIdx b)) fp with
         | none => split_ifs <;> simp
         | some l3 =>
           dsimp only
           rcases Bool.eq_false_or_eq_true (fs.matchesKey n_max b q_val b l3) with h3 | h3 <;>
             (rw [h3]; split_ifs <;> simp))
  | some p1 =>
    rcases p1 with ⟨b1, l1⟩; dsimp only
    rcases Bool.eq_false_or_eq_true (fs.matchesKey n_max b q_val b1 l1) with h1 | h1 <;>
      (rw [h1];
       cases bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey with
       | none =>
         cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
             (fs.slices (fs.liveSliceIdx b)) fp with
         | none => split_ifs <;> simp
         | some l3 =>
           dsimp only
           rcases Bool.eq_false_or_eq_true (fs.matchesKey n_max b q_val b l3) with h3 | h3 <;>
             (rw [h3]; split_ifs <;> simp)
       | some p2 =>
         rcases p2 with ⟨b2, l2⟩; dsimp only
         rcases Bool.eq_false_or_eq_true (fs.matchesKey n_max b q_val b2 l2) with h2 | h2 <;>
           (rw [h2];
            cases btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
              (fs.slices (fs.liveSliceIdx b)) fp with
            | none => split_ifs <;> simp
            | some l3 =>
              dsimp only
              rcases Bool.eq_false_or_eq_true (fs.matchesKey n_max b q_val b l3) with h3 | h3 <;>
                (rw [h3]; split_ifs <;> simp)))

theorem fastFindLocBqGenProg_spec {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict)
    (u : Fin U) :
    let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
    let q_val := keyQuotient (bWhp n_max) u.val
    let prog := fastFindLocBqGenProg (((mkWhpParams c U V w n_max, base), (b, q_val)), u.val)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (match fastFindLoc c U n_max θ fs u with
       | some loc => (1, loc)
       | none => (0, 0)) ∧
    memoryCost prog s ≤ 4 * cTabWhp c + hashEvalCostWhp c + 304 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  intro b q_val
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
  have hcnt_le := hv.bktCount_le b hb
  have hbp_v : ∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max :=
    fun k hk => (hv.backPtr_valid b hb k hk).1
  obtain ⟨hmh_st, hmh_res, hmh_mc, hmh_vp⟩ :=
    mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hrk_st, hrk_res, hrk_mc, hrk_vp⟩ :=
    fpReducedKeyOptRtProg_spec (kv := u.val) henv hseed (s := s)
  set rKey := fpReducedKey c U n_max θ.2 u
  have hrk_eq : (if h : u.val < U then fpReducedKey c U n_max θ.2 ⟨u.val, h⟩ else 0) = rKey := by
    simp [rKey, u.isLt]
  rw [hrk_eq] at hrk_res
  obtain ⟨hce_st, hce_res, hce_mc, hce_vp⟩ := readHdrProg_spec (w := w)
    (F := base + largeSpaceWhp c U V w n_max) (base := base) (hdrOff := hdrCurEp) (s := s)
    (by dsimp only [largeSpaceWhp, hdrCurEp]; omega)
  rw [hrep.2.2.2.1] at hce_res
  obtain ⟨_, _, curMap, hv_cur, _⟩ := hv.bufCur_valid
  obtain ⟨hc1_st, hc1_res, hc1_mc, hc1_vp⟩ :=
    probeBufCandGenProg_spec henv hv.curEp_or hrep hv_cur hb hcnt_le hbp_v
      (q_val := q_val) (rKey := rKey) (s := s)
  have hbo_fn : fs.rebStage ≤ 3 → ∃ oldMap,
      ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap := by
    intro hle3
    have hbo := hv.bufOld_valid
    rw [ite_eq_left hle3] at hbo
    obtain ⟨_, _, oldMap, hv_old, _⟩ := hbo
    exact ⟨oldMap, hv_old⟩
  obtain ⟨hc2_st, hc2_res, hc2_mc, hc2_vp⟩ :=
    probeOldBufCandGenProg_spec henv hrep hv.curEp_or hbo_fn hb hcnt_le hbp_v
      (q_val := q_val) (rKey := rKey) (s := s)
  obtain ⟨hfl_c1, hfl_c2, hfl_c3⟩ := fastFindLoc_cases c U n_max θ fs u
  have hc1_res_ev : (Memory.spec 0).clientResult s
      (probeBufCandGenProg
        ((((mkWhpCoreParams c U V w n_max, base), fs.curEp), (b, q_val)), rKey)) =
      (match evalBufCand n_max b q_val fs
          (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey) with
       | some loc => (1, loc) | none => (0, 0)) := by
    rw [hc1_res]
    cases bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey <;> rfl
  have hc2_res_ev : (Memory.spec 0).clientResult s
      (probeOldBufCandGenProg
        (((mkWhpCoreParams c U V w n_max, base), (b, q_val)), rKey)) =
      (match (if fs.rebStage ≤ 3 then
          evalBufCand n_max b q_val fs
            (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey)
        else none) with
       | some loc => (1, loc) | none => (0, 0)) := by
    rw [hc2_res]
    by_cases hs3 : fs.rebStage ≤ 3
    · rw [ite_eq_left hs3, ite_eq_left hs3]
      cases bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey <;> rfl
    · rw [ite_eq_right hs3, ite_eq_right hs3]
  have hmh_mc' : memoryCost (mkHashRtGenProg (mkWhpParams c U V w n_max, base)) s = 0 := hmh_mc
  have hrk_mc' : memoryCost (fpReducedKeyOptRtProg (mkHashRt c U w n_max base, u.val)) s ≤ 1 :=
    hrk_mc
  have hc1_mc' : memoryCost (probeBufCandGenProg
      ((((mkWhpCoreParams c U V w n_max, base), fs.curEp), (b, q_val)), rKey)) s ≤
      2 * cTabWhp c + 14 := hc1_mc
  have hc2_mc' : memoryCost (probeOldBufCandGenProg
      (((mkWhpCoreParams c U V w n_max, base), (b, q_val)), rKey)) s ≤
      2 * cTabWhp c + 16 := hc2_mc
  dsimp only
  unfold fastFindLocBqGenProg
  dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max from hwp1]
  simp only [pure_bind]
  cases hc1 : evalBufCand n_max b q_val fs
      (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey) with
  | some loc1 =>
    rw [hfl_c1 loc1 hc1]
    rw [hc1] at hc1_res_ev
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hmh_st, hmh_res, clientState_bind, hrk_st, hrk_res,
        clientState_bind, hce_st, hce_res, clientState_bind, hc1_st, hc1_res_ev]
      rfl
    · rw [clientResult_bind, hmh_st, hmh_res, clientResult_bind, hrk_st, hrk_res,
        clientResult_bind, hce_st, hce_res, clientResult_bind, hc1_st, hc1_res_ev]
      rfl
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hmh_st, hmh_res, hmh_mc, hrk_st, hrk_res, hce_st, hce_res, hce_mc, hc1_st, hc1_res_ev]
      simp only [↓reduceIte, memoryCost_pure]; omega
    · refine validProg_bind hmh_vp ?_; rw [hmh_st, hmh_res]
      refine validProg_bind hrk_vp ?_; rw [hrk_st, hrk_res]
      refine validProg_bind hce_vp ?_; rw [hce_st, hce_res]
      refine validProg_bind hc1_vp ?_; rw [hc1_st, hc1_res_ev]
      exact validProg_pure _
  | none =>
    rw [hc1] at hc1_res_ev
    cases hc2 : (if fs.rebStage ≤ 3 then
        evalBufCand n_max b q_val fs
          (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey)
      else none) with
    | some loc2 =>
      rw [hfl_c2 loc2 hc1 hc2]
      rw [hc2] at hc2_res_ev
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [clientState_bind, hmh_st, hmh_res, clientState_bind, hrk_st, hrk_res,
          clientState_bind, hce_st, hce_res, clientState_bind, hc1_st, hc1_res_ev]
        dsimp only; simp only [zero_ne_one, ↓reduceIte]
        rw [clientState_bind, hc2_st, hc2_res_ev]; rfl
      · rw [clientResult_bind, hmh_st, hmh_res, clientResult_bind, hrk_st, hrk_res,
          clientResult_bind, hce_st, hce_res, clientResult_bind, hc1_st, hc1_res_ev]
        dsimp only; simp only [zero_ne_one, ↓reduceIte]
        rw [clientResult_bind, hc2_st, hc2_res_ev]; rfl
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hmh_st, hmh_res, hmh_mc, hrk_st, hrk_res, hce_st, hce_res, hce_mc, hc1_st, hc1_res_ev]
        dsimp only; simp only [zero_ne_one, ↓reduceIte, memoryCost_bind]
        rw [hc2_st, hc2_res_ev]; simp only [↓reduceIte, memoryCost_pure]; omega
      · refine validProg_bind hmh_vp ?_; rw [hmh_st, hmh_res]
        refine validProg_bind hrk_vp ?_; rw [hrk_st, hrk_res]
        refine validProg_bind hce_vp ?_; rw [hce_st, hce_res]
        refine validProg_bind hc1_vp ?_; rw [hc1_st, hc1_res_ev]
        dsimp only; simp only [zero_ne_one, ↓reduceIte]
        refine validProg_bind hc2_vp ?_; rw [hc2_st, hc2_res_ev]
        exact validProg_pure _
    | none =>
      rw [hc2] at hc2_res_ev
      obtain ⟨liveMap, hv_live, _⟩ := hv.live_valid b hb
      have hins := liveInsCount_le_eight hv.toCore hb (hv.overmars_valid b hb)
      obtain ⟨hpl_st, hpl_res, hpl_mc, hpl_vp⟩ :=
        probeLiveCandGenProg_spec henv hseed hrep hb (hv.roles_valid b hb).1 hins hv_live
          hcnt_le hbp_v u (q_val := q_val) (s := s)
      have hpl_mc' : memoryCost (probeLiveCandGenProg
          (((mkWhpParams c U V w n_max, base), (b, q_val)), u.val)) s ≤
          hashEvalCostWhp c + 272 := hpl_mc
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [clientState_bind, hmh_st, hmh_res, clientState_bind, hrk_st, hrk_res,
          clientState_bind, hce_st, hce_res, clientState_bind, hc1_st, hc1_res_ev]
        dsimp only; simp only [zero_ne_one, ↓reduceIte]
        rw [clientState_bind, hc2_st, hc2_res_ev]
        dsimp only; simp only [zero_ne_one, ↓reduceIte]
        exact hpl_st
      · rw [clientResult_bind, hmh_st, hmh_res, clientResult_bind, hrk_st, hrk_res,
          clientResult_bind, hce_st, hce_res, clientResult_bind, hc1_st, hc1_res_ev]
        dsimp only; simp only [zero_ne_one, ↓reduceIte]
        rw [clientResult_bind, hc2_st, hc2_res_ev]
        dsimp only; simp only [zero_ne_one, ↓reduceIte]
        exact hpl_res.trans (hfl_c3 hc1 hc2).symm
      · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
        rw [hmh_st, hmh_res, hmh_mc, hrk_st, hrk_res, hce_st, hce_res, hce_mc, hc1_st, hc1_res_ev]
        dsimp only; simp only [zero_ne_one, ↓reduceIte, memoryCost_bind]
        rw [hc2_st, hc2_res_ev]; simp only [zero_ne_one, ↓reduceIte]; omega
      · refine validProg_bind hmh_vp ?_; rw [hmh_st, hmh_res]
        refine validProg_bind hrk_vp ?_; rw [hrk_st, hrk_res]
        refine validProg_bind hce_vp ?_; rw [hce_st, hce_res]
        refine validProg_bind hc1_vp ?_; rw [hc1_st, hc1_res_ev]
        dsimp only; simp only [zero_ne_one, ↓reduceIte]
        refine validProg_bind hc2_vp ?_; rw [hc2_st, hc2_res_ev]
        dsimp only; simp only [zero_ne_one, ↓reduceIte]
        exact hpl_vp

/-- Fast-mode value query `fastQueryGenProg` (`d = ((wp, base), u_val)`), returning `(1, val)` or
`(0, 0)` in `O_c(1)` worst-case memory operations without mutating memory. -/
@[irreducible] def fastQueryGenProg : (WhpParams × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | ((wp, base), u_val) => do
    let z0 ← pure 0
    let z1 ← pure 1
    let hrt ← mkHashRtGenProg (wp, base)
    let bq ← feistelSplitRtProg (hrt, u_val)
    let fl ← fastFindLocBqGenProg (((wp, base), bq), u_val)
    if fl.1 = z1 then do
      let p ← physSlotGenProg (((wp.1, base), bq.1), fl.2)
      let val ← readValGenProg ((wp.1, base), p)
      pure (z1, val)
    else
      pure (z0, z0)

theorem realizes_fastQueryGen :
    Realizes .exact fastQueryGenProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      (fun w ((wp, base), u_val) s => ValidFastMemPre w wp base s ∧ u_val < wpU wp.1)
      (fun _ _ => 0) := by
  unfold fastQueryGenProg
  have hmh := realizes_mkHashRtGen
  have hfs := realizes_feistelSplitRt
  have hfl := realizes_fastFindLocBqGen
  have hps := realizes_physSlotGen
  have hrv := realizes_readValGen
  realize
  all_goals (
    rcases d with ⟨⟨wp, base⟩, u_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv⟩, hu_wp⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    have hu : u_val < U := by rw [hcp_eq, wp_large_U hth] at hu_wp; exact hu_wp
    set u : Fin U := ⟨u_val, hu⟩
    have hb : feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u_val < numBucketsWhp n_max :=
      feistelBucket_lt _ _ _
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    obtain ⟨hfs_st, hfs_res, _, _⟩ :=
      feistelSplitRtProg_spec (u_val := u_val) henv hseed (s := s)
    obtain ⟨hfl_st, hfl_res, _, _⟩ :=
      fastFindLocBqGenProg_spec henv hseed hrep hv u (s := s)
    dsimp only [u] at hfl_st hfl_res
    simp only [hcp_eq] at *
    simp only [hmh_st, hmh_res, hfs_st, hfs_res, hfl_st, wp_large_M hth, wp_large_nMax hth] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | (have hspec := hv.fastFindLoc_spec u
       cases hfind : fastFindLoc c U n_max θ fs u with
       | none =>
         have hhit : ((Memory.spec 0).clientResult s
           (fastFindLocBqGenProg (((mkWhpParams c U V w n_max, base),
             (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u_val,
              keyQuotient (bWhp n_max) u_val)), u_val))).1 = 1 := by assumption
         rw [hfind] at hfl_res; rw [hfl_res] at hhit; cases hhit
       | some loc =>
         rw [hfind] at hfl_res hspec
         rw [hfl_res]
         have hloc_b : loc < fs.bktCount
             (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u_val) := hspec.1
         have hloc : loc < totalLocalCoordsWhp n_max := hloc_b.trans_le (hv.bktCount_le _ hb)
         have hbp : capFrontWhp n_max ≤ loc →
             fs.backPtr (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u_val)
               (loc - capFrontWhp n_max) < poolSizeWhp n_max :=
           fun hcf => (hv.backPtr_valid _ hb _ (by omega)).1
         first
         | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hloc, hbp⟩
         | (obtain ⟨hps_st, hps_res, hps_lt, _, _⟩ :=
              physSlotGenProg_spec henv hb hloc hbp hrep (s := s)
            simp only [hps_st, hps_res] at *
            exact hps_lt))
  )

theorem fastQueryGenProg_spec {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict)
    (u : Fin U) :
    let prog := fastQueryGenProg ((mkWhpParams c U V w n_max, base), u.val)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (match fastQuery c U n_max θ fs u with
       | some v => (1, v)
       | none => (0, 0)) ∧
    memoryCost prog s ≤ 4 * cTabWhp c + 2 * hashEvalCostWhp c + 308 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  let b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
  have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
  obtain ⟨hmh_st, hmh_res, hmh_mc, hmh_vp⟩ :=
    mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hfs_st, hfs_res, hfs_mc, hfs_vp⟩ :=
    feistelSplitRtProg_spec (u_val := u.val) henv hseed (s := s)
  obtain ⟨hfl_st, hfl_res, hfl_mc, hfl_vp⟩ :=
    fastFindLocBqGenProg_spec henv hseed hrep hv u (s := s)
  have hspec := hv.fastFindLoc_spec u
  dsimp only
  unfold fastQueryGenProg fastQuery
  dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max from hwp1]
  simp only [pure_bind]
  cases hfind : fastFindLoc c U n_max θ fs u with
  | none =>
    rw [hfind] at hfl_res
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hmh_st, hmh_res, clientState_bind, hfs_st, hfs_res,
        clientState_bind, hfl_st, hfl_res]; rfl
    · rw [clientResult_bind, hmh_st, hmh_res, clientResult_bind, hfs_st, hfs_res,
        clientResult_bind, hfl_st, hfl_res]; rfl
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hmh_st, hmh_res, hmh_mc, hfs_st, hfs_res, hfl_st, hfl_res]
      simp only [zero_ne_one, ↓reduceIte, memoryCost_pure]; omega
    · refine validProg_bind hmh_vp ?_; rw [hmh_st, hmh_res]
      refine validProg_bind hfs_vp ?_; rw [hfs_st, hfs_res]
      refine validProg_bind hfl_vp ?_; rw [hfl_st, hfl_res]
      exact validProg_pure _
  | some loc =>
    rw [hfind] at hfl_res hspec
    have hloc_b : loc < fs.bktCount b := hspec.1
    have hloc : loc < totalLocalCoordsWhp n_max := hloc_b.trans_le (hv.bktCount_le b hb)
    have hbp : capFrontWhp n_max ≤ loc →
        fs.backPtr b (loc - capFrontWhp n_max) < poolSizeWhp n_max :=
      fun hcf => (hv.backPtr_valid b hb _ (by omega)).1
    obtain ⟨hps_st, hps_res, hps_lt, hps_mc, hps_vp⟩ :=
      physSlotGenProg_spec henv hb hloc hbp hrep (s := s)
    obtain ⟨hrv_st, hrv_res, hrv_mc, hrv_vp⟩ := readValGenProg_spec henv hps_lt hrep (s := s)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hmh_st, hmh_res, clientState_bind, hfs_st, hfs_res,
        clientState_bind, hfl_st, hfl_res]; dsimp only; simp only [↓reduceIte]
      rw [clientState_bind, hps_st, hps_res, clientState_bind, hrv_st]; rfl
    · rw [clientResult_bind, hmh_st, hmh_res, clientResult_bind, hfs_st, hfs_res,
        clientResult_bind, hfl_st, hfl_res]; dsimp only; simp only [↓reduceIte]
      rw [clientResult_bind, hps_st, hps_res, clientResult_bind, hrv_st, hrv_res]; rfl
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hmh_st, hmh_res, hmh_mc, hfs_st, hfs_res, hfl_st, hfl_res]
      dsimp only; simp only [↓reduceIte, memoryCost_bind]
      rw [hps_st, hps_res, hrv_st, hrv_mc]
      have hmh_mc' : memoryCost (mkHashRtGenProg (mkWhpParams c U V w n_max, base)) s = 0 := hmh_mc
      have hfs_mc' : memoryCost (feistelSplitRtProg (mkHashRt c U w n_max base, u.val)) s ≤
          hashEvalCostWhp c := hfs_mc
      have hfl_mc' : memoryCost (fastFindLocBqGenProg
          (((mkWhpParams c U V w n_max, base),
            (b, keyQuotient (bWhp n_max) u.val)), u.val)) s ≤
          4 * cTabWhp c + hashEvalCostWhp c + 304 := hfl_mc
      have hps_mc' : memoryCost (physSlotGenProg
          (((mkWhpCoreParams c U V w n_max, base), b), loc)) s ≤ 2 := hps_mc
      have hrv_mc' : memoryCost (readValGenProg
          ((mkWhpCoreParams c U V w n_max, base), fs.physSlot n_max b loc)) s = 2 := hrv_mc
      dsimp only [b] at hfl_mc' hps_mc' hrv_mc' ⊢
      simp only [memoryCost_pure]; omega
    · refine validProg_bind hmh_vp ?_; rw [hmh_st, hmh_res]
      refine validProg_bind hfs_vp ?_; rw [hfs_st, hfs_res]
      refine validProg_bind hfl_vp ?_; rw [hfl_st, hfl_res]
      dsimp only; simp only [↓reduceIte]
      refine validProg_bind hps_vp ?_; rw [hps_st, hps_res]
      refine validProg_bind hrv_vp ?_; rw [hrv_st]
      exact validProg_pure _

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
