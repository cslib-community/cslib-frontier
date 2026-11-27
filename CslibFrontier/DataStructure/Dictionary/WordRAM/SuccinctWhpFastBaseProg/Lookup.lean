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

/-! ## Read-only program specifications -/

/-- From state `s`, the program `p` leaves memory unchanged, returns `r`, issues at most `C`
memory operations, and is valid below frontier `F`. -/
private structure ReadSpec {α : Type} (w F : ℕ) (s : Memory.State) (p : Memory.Prog α) (r : α)
    (C : ℕ) : Prop where
  state : (Memory.spec 0).clientState s p = s
  result : (Memory.spec 0).clientResult s p = r
  cost : memoryCost p s ≤ C
  valid : ValidProg w F s p

private theorem ReadSpec.of_le {α : Type} {w F C : ℕ} {s : Memory.State} {p : Memory.Prog α}
    {r : α} (h : (Memory.spec 0).clientState s p = s ∧ (Memory.spec 0).clientResult s p = r ∧
      memoryCost p s ≤ C ∧ ValidProg w F s p) : ReadSpec w F s p r C :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

private theorem ReadSpec.of_eq {α : Type} {w F C : ℕ} {s : Memory.State} {p : Memory.Prog α}
    {r : α} (h : (Memory.spec 0).clientState s p = s ∧ (Memory.spec 0).clientResult s p = r ∧
      memoryCost p s = C ∧ ValidProg w F s p) : ReadSpec w F s p r C :=
  ⟨h.1, h.2.1, h.2.2.1.le, h.2.2.2⟩

private theorem ReadSpec.toAnd {α : Type} {w F C : ℕ} {s : Memory.State} {p : Memory.Prog α}
    {r : α} (h : ReadSpec w F s p r C) :
    (Memory.spec 0).clientState s p = s ∧ (Memory.spec 0).clientResult s p = r ∧
      memoryCost p s ≤ C ∧ ValidProg w F s p :=
  ⟨h.state, h.result, h.cost, h.valid⟩

private theorem ReadSpec.weaken {α : Type} {w F C C' : ℕ} {s : Memory.State}
    {p : Memory.Prog α} {r r' : α} (h : ReadSpec w F s p r C) (hr : r = r') (hC : C ≤ C') :
    ReadSpec w F s p r' C' :=
  ⟨h.state, hr ▸ h.result, h.cost.trans hC, h.valid⟩

private theorem ReadSpec.pure {α : Type} {w F : ℕ} {s : Memory.State} (a : α) :
    ReadSpec w F s (pure a) a 0 :=
  ⟨rfl, rfl, le_rfl, validProg_pure a⟩

private theorem ReadSpec.bind {α β : Type} {w F C₁ C₂ : ℕ} {s : Memory.State}
    {m : Memory.Prog α} {k : α → Memory.Prog β} {a : α} {b : β}
    (hm : ReadSpec w F s m a C₁) (hk : ReadSpec w F s (k a) b C₂) :
    ReadSpec w F s (m >>= k) b (C₁ + C₂) where
  state := by rw [clientState_bind, hm.state, hm.result, hk.state]
  result := by rw [clientResult_bind, hm.state, hm.result, hk.result]
  cost := by rw [memoryCost_bind', hm.state, hm.result]; exact Nat.add_le_add hm.cost hk.cost
  valid := validProg_bind hm.valid (by rw [hm.state, hm.result]; exact hk.valid)

private theorem ReadSpec.ite {α : Type} {w F C₁ C₂ : ℕ} {s : Memory.State} {c : Prop}
    [Decidable c] {p₁ p₂ : Memory.Prog α} {r₁ r₂ : α}
    (h₁ : ReadSpec w F s p₁ r₁ C₁) (h₂ : ReadSpec w F s p₂ r₂ C₂) :
    ReadSpec w F s (if c then p₁ else p₂) (if c then r₁ else r₂) (C₁ + C₂) := by
  split_ifs
  · exact h₁.weaken rfl (by omega)
  · exact h₂.weaken rfl (by omega)

private theorem ReadSpec.if_pos {α : Type} {w F C : ℕ} {s : Memory.State} {c : Prop}
    [Decidable c] {p₁ p₂ : Memory.Prog α} {r : α} (hc : c) (h : ReadSpec w F s p₁ r C) :
    ReadSpec w F s (if c then p₁ else p₂) r C := by
  rwa [ite_eq_left hc]

private theorem ReadSpec.if_neg {α : Type} {w F C : ℕ} {s : Memory.State} {c : Prop}
    [Decidable c] {p₁ p₂ : Memory.Prog α} {r : α} (hc : ¬c) (h : ReadSpec w F s p₂ r C) :
    ReadSpec w F s (if c then p₁ else p₂) r C := by
  rwa [ite_eq_right hc]

private theorem mkWhpParams_fst (c U V w n_max : ℕ) :
    (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
  unfold mkWhpParams; split <;> rfl

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
    obtain rfl := henv.2.2.1
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
    ReadSpec w (base + largeSpaceWhp c U V w n_max) s
      (matchesKeyGenProg (((mkWhpCoreParams c U V w n_max, base), (b, q_val)), (b_cand, loc)))
      (if fs.matchesKey n_max b q_val b_cand loc then 1 else 0) 6 := by
  unfold matchesKeyGenProg
  simp only [pure_bind]
  have hc := ReadSpec.of_eq (readBktFieldGenProg_spec henv hb (by decide : 0 < 10) hrep (s := s))
  by_cases hbb : b_cand = b
  · by_cases hlt : loc < fs.bktCount b
    · obtain ⟨hp_st, hp_res, hp_lt, hp_mc, hp_vp⟩ := physSlotGenProg_spec henv hb
        (hlt.trans_le hcnt_le) (fun hcf => hbp_v _ (by omega)) hrep (s := s)
      exact .weaken (.if_pos hbb (hc.bind (.if_pos hlt (ReadSpec.bind ⟨hp_st, hp_res, hp_mc, hp_vp⟩
        ((ReadSpec.of_eq (readQuotGenProg_spec henv hp_lt hrep)).bind
          (.ite (.pure 1) (.pure 0)))))))
        (by simp [FastState.matchesKey, hbb, hlt]) (by omega)
    · exact .weaken (.if_pos hbb (hc.bind (.if_neg hlt (.pure 0))))
        (by simp [FastState.matchesKey, hlt]) (by omega)
  · exact .weaken (.if_neg hbb (.pure 0)) (by simp [FastState.matchesKey, hbb]) (by omega)

/-- The candidate `loc` that a buffer hit `(b', loc)` yields after verifying `(b, q_val)`. -/
private def evalBufCand (n_max b q_val : ℕ) (fs : FastState) :
    Option (ℕ × ℕ) → Option ℕ
  | some (b', loc) => if fs.matchesKey n_max b q_val b' loc then some loc else none
  | none => none

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
    obtain rfl := henv.2.2.1
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
    ReadSpec w (base + largeSpaceWhp c U V w n_max) s
      (probeBufCandGenProg ((((mkWhpCoreParams c U V w n_max, base), ep), (b, q_val)), rKey))
      (match evalBufCand n_max b q_val fs (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf ep) rKey)
       with | some loc => (1, loc) | none => (0, 0))
      (2 * cTabWhp c + 14) := by
  have hl := ReadSpec.of_le
    (bufLookupGenProg_spec henv hep (hrep.buf_rep hep) hv (rKey := rKey) (s := s))
  unfold probeBufCandGenProg
  simp only [pure_bind]
  generalize bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf ep) rKey = bl at hl ⊢
  rcases bl with _ | ⟨b', loc⟩ <;> dsimp only at hl
  · exact .weaken (hl.bind (.if_neg (by decide) (.pure _))) rfl (by omega)
  · exact .weaken (hl.bind (.if_pos rfl ((matchesKeyGenProg_spec henv hrep hb hcnt_le hbp_v).bind
      (.ite (.pure _) (.pure _)))))
      (by simp only [evalBufCand]; cases fs.matchesKey n_max b q_val b' loc <;> rfl)
      (by omega)

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
    obtain ⟨c, U, V, w₀, n_max, θ, fs, mapFn, henv, rfl, hseed, hrep,
      hb, hlr, hins, hv_sl⟩ := h
    obtain rfl := henv.2.2.1
    have hth := henv.2.2.2.1
    obtain ⟨hrs_st, hrs_res, _, _⟩ := readLiveSaltIdxGenProg_spec henv hb hrep (s := s)
    obtain ⟨hmh_st, hmh_res, _, _⟩ :=
      mkHashRtGenProg_spec (U := U) (V := V) (w := w) (base := base) hth s
    obtain ⟨hfp_st, hfp_res, _, _⟩ :=
      fpOfSaltOptRtProg_spec (salt := fs.bktSalt b) (kv := u_val) henv hseed (s := s)
    have hlIdx : fs.liveSliceIdx b < 3 * numBucketsWhp n_max := by
      dsimp [FastState.liveSliceIdx]; omega
    have hfp_lt := fpOfSaltOpt_lt c U n_max (fs.bktSalt b) u_val θ.2
    simp only [mkWhpParams_fst, hrs_st, hrs_res, hmh_st, hmh_res, hfp_st, hfp_res] at *
    first
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hlr⟩
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
    | exact ⟨c, U, V, w, n_max, fs.liveInsCount b, fs.slices (fs.liveSliceIdx b), mapFn,
        henv, rfl, hlIdx, hins, hrep.slice_rep hlIdx, hv_sl, hfp_lt⟩
  )

private theorem probeLiveLookupGenProg_spec {c U V w n_max base b u_val fp : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hb : b < numBucketsWhp n_max) (hlr : fs.liveRole b < 3)
    (hins : fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12)
    (hv_sl : ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) mapFn)
    (hfp : (if hs : fs.bktSalt b < sMaxWhp c n_max then
      if hu : u_val < U then fpHash c U n_max θ.2 ⟨fs.bktSalt b, hs⟩ ⟨u_val, hu⟩ else 0
     else 0) = fp) :
    ReadSpec w (base + largeSpaceWhp c U V w n_max) s
      (probeLiveLookupGenProg ((mkWhpParams c U V w n_max, base), (b, u_val)))
      (match btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) fp with
       | some loc => (1, loc)
       | none => (0, 0))
      (hashEvalCostWhp c + 266) := by
  subst hfp
  have hth := henv.2.2.2.1
  have hfp_lt := fpOfSaltOpt_lt c U n_max (fs.bktSalt b) u_val θ.2
  have hlIdx : fs.liveSliceIdx b < 3 * numBucketsWhp n_max := by
    dsimp [FastState.liveSliceIdx]; omega
  have hbt := ReadSpec.of_le
    (btreeLookupGenProg_spec henv hlIdx hins (hrep.slice_rep hlIdx) hv_sl hfp_lt (s := s))
  rw [← hv_sl.lookup_eq hth hins hfp_lt] at hbt
  unfold probeLiveLookupGenProg
  simp only [mkWhpParams_fst]
  exact .weaken ((ReadSpec.of_eq (readLiveSaltIdxGenProg_spec henv hb hrep)).bind
    ((ReadSpec.of_eq (mkHashRtGenProg_spec hth s)).bind
      ((ReadSpec.of_le (fpOfSaltOptRtProg_spec henv hseed)).bind hbt))) rfl (by omega)

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
    obtain ⟨c, U, V, w₀, n_max, θ, fs, mapFn, henv, rfl, hseed, hrep,
      hb, hlr, hins, hv_sl, hcnt_le, hbp_v⟩ := h
    obtain rfl := henv.2.2.1
    have hlk_st := (probeLiveLookupGenProg_spec (u_val := u_val) henv hseed hrep hb hlr hins hv_sl
      rfl (s := s)).state
    simp only [mkWhpParams_fst, hlk_st] at *
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
    ReadSpec w (base + largeSpaceWhp c U V w n_max) s
      (probeLiveCandGenProg (((mkWhpParams c U V w n_max, base), (b, q_val)), u.val))
      (match (match btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u) with
        | some loc => if fs.matchesKey n_max b q_val b loc then some loc else none
        | none => none) with
       | some loc => (1, loc) | none => (0, 0))
      (hashEvalCostWhp c + 272) := by
  have hlk := probeLiveLookupGenProg_spec henv hseed hrep hb hlr hins hv_sl
    (u_val := u.val) (fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u)
    (by simp only [fpOfSalt, u.isLt, ↓reduceDIte, Fin.eta]) (s := s)
  unfold probeLiveCandGenProg
  simp only [pure_bind, mkWhpParams_fst]
  generalize btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
    (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u) = bl at hlk ⊢
  rcases bl with _ | loc <;> dsimp only at hlk
  · exact .weaken (hlk.bind (.if_neg (by decide) (.pure _))) rfl (by omega)
  · exact .weaken (hlk.bind (.if_pos rfl ((matchesKeyGenProg_spec henv hrep hb hcnt_le hbp_v).bind
      (.ite (.pure _) (.pure _)))))
      (by dsimp only; cases fs.matchesKey n_max b q_val b loc <;> rfl)
      (by omega)

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
    obtain rfl := henv.2.2.1
    have hth := henv.2.2.2.1
    obtain ⟨hst_st, hst_res, _, _⟩ := readHdrProg_large_spec c U V w n_max
      (base := base) (hdrOff := hdrRebStage) (s := s) (by decide)
    obtain ⟨hro_st, hro_res, _, _⟩ := readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max)
      (Nat.add_lt_add_left
        ((by decide : hdrCurEp < 32).trans_le (headerWords_le_largeSpaceWhp c U V w n_max)) base) hce_or hrep.2.2.2.1 (s := s)
    simp only [hst_st, hst_res, hrep.2.2.2.2.2.1, hro_st, hro_res] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact (by decide : 2 ≤ _).trans
        ((le_bMinWhp c).trans ((bMinWhp_le_log hth).trans henv.log_lt_w.le))
    | (obtain ⟨oldMap, hv_old⟩ := hbo_fn (by omega)
       exact ⟨c, U, V, w, n_max, fs, oldMap, henv, rfl, hrep, fs.oldEp_or hce_or, hv_old,
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
    ReadSpec w (base + largeSpaceWhp c U V w n_max) s
      (probeOldBufCandGenProg (((mkWhpCoreParams c U V w n_max, base), (b, q_val)), rKey))
      (match (if fs.rebStage ≤ 3 then evalBufCand n_max b q_val fs
          (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey) else none) with
       | some loc => (1, loc) | none => (0, 0))
      (2 * cTabWhp c + 16) := by
  have hst := ReadSpec.of_eq (readHdrProg_large_spec c U V w n_max
    (base := base) (hdrOff := hdrRebStage) (s := s) (by decide))
  rw [hrep.2.2.2.2.2.1] at hst
  unfold probeOldBufCandGenProg
  simp only [pure_bind]
  by_cases hle3 : fs.rebStage ≤ 3
  · obtain ⟨oldMap, hv_old⟩ := hbo_fn hle3
    have hro := ReadSpec.of_eq (readOldEpProg_spec (w := w)
      (F := base + largeSpaceWhp c U V w n_max)
      (Nat.add_lt_add_left
        ((by decide : hdrCurEp < 32).trans_le (headerWords_le_largeSpaceWhp c U V w n_max)) base) hce_or hrep.2.2.2.1 (s := s))
    exact .weaken (hst.bind (.if_pos hle3 (hro.bind (probeBufCandGenProg_spec henv
      (fs.oldEp_or hce_or) hrep hv_old hb hcnt_le hbp_v)))) (by rw [ite_eq_left hle3]) (by omega)
  · exact .weaken (hst.bind (.if_neg hle3 (.pure _))) (by rw [ite_eq_right hle3]) (by omega)

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
    obtain ⟨⟨c, U, V, w₀, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv⟩, hb_wp⟩ := h
    obtain rfl := henv.2.2.1
    have hth := henv.2.2.2.1
    have hb : b < numBucketsWhp n_max := by rwa [mkWhpParams_fst, wp_large_M hth] at hb_wp
    obtain ⟨hmh_st, hmh_res, _, _⟩ :=
      mkHashRtGenProg_spec (U := U) (V := V) (w := w) (base := base) hth s
    obtain ⟨hrk_st, _, _, _⟩ := fpReducedKeyOptRtProg_spec (kv := u_val) henv hseed (s := s)
    obtain ⟨hce_st, hce_res, _, _⟩ := readHdrProg_large_spec c U V w n_max
      (base := base) (hdrOff := hdrCurEp) (s := s) (by decide)
    obtain ⟨_, _, curMap, hv_cur, _⟩ := hv.bufCur_valid
    have hcnt_le := hv.bktCount_le b hb
    have hbp_v : ∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max :=
      fun k hk => (hv.backPtr_valid b hb k hk).1
    have hbo_fn : fs.rebStage ≤ 3 → ∃ oldMap,
        ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap := fun hle3 => by
      obtain ⟨_, _, oldMap, hv_old, _⟩ := ite_eq_left hle3 ▸ hv.bufOld_valid
      exact ⟨oldMap, hv_old⟩
    have hc1_st (rKey : ℕ) := (probeBufCandGenProg_spec henv hv.curEp_or hrep hv_cur hb hcnt_le
      hbp_v (q_val := q_val) (rKey := rKey) (s := s)).state
    have hc2_st (rKey : ℕ) := (probeOldBufCandGenProg_spec henv hrep hv.curEp_or hbo_fn
      hb hcnt_le hbp_v (q_val := q_val) (rKey := rKey) (s := s)).state
    simp only [mkWhpParams_fst, hmh_st, hmh_res, hrk_st, hce_st, hce_res, hrep.2.2.2.1,
      hc1_st, hc2_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_hdr_addr (by decide)
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
    | exact ⟨c, U, V, w, n_max, fs, curMap, henv, rfl, hrep, hv.curEp_or, hv_cur,
        hb, hcnt_le, hbp_v⟩
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hv.curEp_or, hbo_fn, hb, hcnt_le, hbp_v⟩
    | (obtain ⟨liveMap, hv_live, _⟩ := hv.live_valid b hb
       have hins := liveInsCount_le_eight hv.toCore hb (hv.overmars_valid b hb)
       exact ⟨c, U, V, w, n_max, θ, fs, liveMap, henv, rfl, hseed, hrep,
         hb, (hv.roles_valid b hb).1, hins, hv_live, hcnt_le, hbp_v⟩)
  )

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
  have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
  have hcnt_le := hv.bktCount_le b hb
  have hbp_v : ∀ k < fs.bktCount b - capFrontWhp n_max, fs.backPtr b k < poolSizeWhp n_max :=
    fun k hk => (hv.backPtr_valid b hb k hk).1
  have hrk := ReadSpec.of_le (fpReducedKeyOptRtProg_spec (V := V) (kv := u.val) henv hseed (s := s))
  simp only [u.isLt, ↓reduceDIte, Fin.eta] at hrk
  have hce := ReadSpec.of_eq (readHdrProg_large_spec c U V w n_max
    (base := base) (hdrOff := hdrCurEp) (s := s) (by decide))
  rw [hrep.2.2.2.1] at hce
  obtain ⟨_, _, curMap, hv_cur, _⟩ := hv.bufCur_valid
  have hbo_fn : fs.rebStage ≤ 3 → ∃ oldMap,
      ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap := fun hle3 => by
    obtain ⟨_, _, oldMap, hv_old, _⟩ := ite_eq_left hle3 ▸ hv.bufOld_valid
    exact ⟨oldMap, hv_old⟩
  obtain ⟨liveMap, hv_live, _⟩ := hv.live_valid b hb
  have hins := liveInsCount_le_eight hv.toCore hb (hv.overmars_valid b hb)
  refine ReadSpec.toAnd ?_
  unfold fastFindLocBqGenProg
  simp only [pure_bind, mkWhpParams_fst]
  refine .weaken ((ReadSpec.of_eq (mkHashRtGenProg_spec hth s)).bind <| hrk.bind <| hce.bind <|
    (probeBufCandGenProg_spec henv hv.curEp_or hrep hv_cur hb hcnt_le hbp_v).bind <|
    .ite (.pure _) <|
    (probeOldBufCandGenProg_spec henv hrep hv.curEp_or hbo_fn hb hcnt_le hbp_v).bind <|
    .ite (.pure _) <|
    probeLiveCandGenProg_spec henv hseed hrep hb (hv.roles_valid b hb).1 hins hv_live hcnt_le
      hbp_v u) ?_ (by omega)
  dsimp only [fastFindLoc, evalBufCand]
  generalize bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp)
    (fpReducedKey c U n_max θ.2 u) = o1
  generalize bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp)
    (fpReducedKey c U n_max θ.2 u) = o2
  generalize btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
    (fs.slices (fs.liveSliceIdx b)) (fpOfSalt c U n_max θ.2 (fs.bktSalt b) u) = o3
  rcases o1 with _ | ⟨b1, l1⟩ <;> rcases o2 with _ | ⟨b2, l2⟩ <;> rcases o3 with _ | l3 <;>
    dsimp only <;> split_ifs <;> simp_all

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
    obtain ⟨⟨c, U, V, w₀, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv⟩, hu_wp⟩ := h
    obtain rfl := henv.2.2.1
    have hth := henv.2.2.2.1
    have hu : u_val < U := by rwa [mkWhpParams_fst, wp_large_U hth] at hu_wp
    set u : Fin U := ⟨u_val, hu⟩
    have hb := feistelBucket_lt (bWhp n_max) (bktHash c U n_max θ.1) u_val
    obtain ⟨hmh_st, hmh_res, _, _⟩ :=
      mkHashRtGenProg_spec (U := U) (V := V) (w := w) (base := base) hth s
    obtain ⟨hfs_st, hfs_res, _, _⟩ := feistelSplitRtProg_spec (u_val := u_val) henv hseed (s := s)
    obtain ⟨hfl_st, hfl_res, _, _⟩ := fastFindLocBqGenProg_spec henv hseed hrep hv u (s := s)
    dsimp only [u] at hfl_st hfl_res
    simp only [mkWhpParams_fst, hmh_st, hmh_res, hfs_st, hfs_res, hfl_st, hfl_res,
      wp_large_M hth, wp_large_nMax hth] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv⟩
    | exact hb
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | (have hspec := hv.fastFindLoc_spec u
       cases hfind : fastFindLoc c U n_max θ fs u with
       | none => simp [u, hfind] at *
       | some loc =>
         simp only [u, hfind] at *
         have hloc : loc < totalLocalCoordsWhp n_max := hspec.1.trans_le (hv.bktCount_le _ hb)
         have hbp (hcf : capFrontWhp n_max ≤ loc) :=
           (hv.backPtr_valid _ hb (loc - capFrontWhp n_max) (by omega)).1
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
  have hb := feistelBucket_lt (bWhp n_max) (bktHash c U n_max θ.1) u.val
  have hmh := ReadSpec.of_eq
    (mkHashRtGenProg_spec (U := U) (V := V) (w := w) (base := base) henv.2.2.2.1 s)
  have hfs := ReadSpec.of_le (feistelSplitRtProg_spec (u_val := u.val) henv hseed (s := s))
  have hfl := ReadSpec.of_le (fastFindLocBqGenProg_spec henv hseed hrep hv u (s := s))
  have hspec := hv.fastFindLoc_spec u
  refine ReadSpec.toAnd ?_
  unfold fastQueryGenProg fastQuery
  simp only [pure_bind, mkWhpParams_fst]
  cases hfind : fastFindLoc c U n_max θ fs u with
  | none =>
    rw [hfind] at hfl
    exact .weaken (hmh.bind <| hfs.bind <| hfl.bind <| .if_neg (by decide) (.pure _)) rfl
      (by omega)
  | some loc =>
    rw [hfind] at hfl hspec
    have hloc := hspec.1.trans_le (hv.bktCount_le _ hb)
    obtain ⟨hps_st, hps_res, hps_lt, hps_mc, hps_vp⟩ := physSlotGenProg_spec henv hb hloc
      (fun hcf => (hv.backPtr_valid _ hb _ (by omega)).1) hrep (s := s)
    exact .weaken (hmh.bind <| hfs.bind <| hfl.bind <| .if_pos rfl <|
      ReadSpec.bind ⟨hps_st, hps_res, hps_mc, hps_vp⟩ <|
      (ReadSpec.of_eq (readValGenProg_spec henv hps_lt hrep)).bind (.pure _)) rfl (by omega)

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
