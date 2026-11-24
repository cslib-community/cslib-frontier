/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg.InsAllocWrite
import CslibFrontier.Tactic.Realize

/-!
# Fast Insertion Fresh Commit & Overmars Step (`insCommitFreshGenProg`)

Combines slot allocation, `(q, v)` write, direct/collision insertion, and `overmarsStepGenProg`
once all fast-mode guards succeed.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.insCommitFreshGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_insCommitFreshGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.insCommitFreshGenProg_spec`
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

/-- Allocate slot, write `(q_val, v_val)`, and insert into `buf curEp` or `slices lIdx`
(`d = ((((cp, base), (b, X)), (q_val, v_val)), (hasCol, (rKey, (fp, lIdx))))`). -/
@[irreducible] private def fastInsertFreshGenProg :
    (((WhpCoreParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ))) → Memory.Prog Unit
  | ((((cp, base), (b, X)), (q_val, v_val)), (hasCol, (rKey, (fp, lIdx)))) => do
    let z1 ← pure 1
    fastInsertAllocGenProg (((cp, base), b), X)
    insWriteQVAtGenProg ((((cp, base), b), X), (q_val, v_val))
    if hasCol = z1 then
      insFinishCollisionGenProg ((((cp, base), b), X), rKey)
    else
      insFinishDirectGenProg ((((cp, base), b), X), (fp, lIdx))

private theorem realizes_fastInsertFreshGen :
    Realizes .exact fastInsertFreshGenProg
      (WordEncoding.encode
        (α := (((WhpCoreParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ)))))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), (b, X)), (q_val, v_val)), (hasCol, (_, (fp, lIdx)))) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          (fs.curEp = 0 ∨ fs.curEp = 1) ∧
          b < numBucketsWhp n_max ∧
          X < totalLocalCoordsWhp n_max ∧
          (capFrontWhp n_max ≤ X →
            0 < fs.poolFreeTop ∧
            fs.poolFreeTop ≤ poolSizeWhp n_max ∧
            fs.poolFreeStack (fs.poolFreeTop - 1) < poolSizeWhp n_max) ∧
          q_val < 2 ^ quotBitsWhp U n_max ∧
          v_val < 2 ^ valBits V ∧
          (hasCol = 1 →
            (fs.buf fs.curEp).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
            (fs.buf fs.curEp).itemAlloc < qEpochWhp n_max ∧
            ∃ curMap, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) curMap) ∧
          (hasCol ≠ 1 →
            lIdx = fs.liveSliceIdx b ∧
            lIdx < 3 * numBucketsWhp n_max ∧
            fp < 2 ^ fpBitsWhp n_max ∧
            fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
            ∃ lm, ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices lIdx) lm))
      (fun _ _ => 0) := by
  unfold fastInsertFreshGenProg
  have hal := realizes_fastInsertAllocGen
  have hwq := realizes_insWriteQVAtGen
  have hfc := realizes_insFinishCollisionGen
  have hfd := realizes_insFinishDirectGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, ⟨b, X⟩⟩, ⟨q_val, v_val⟩⟩, ⟨hasCol, ⟨rKey, ⟨fp, lIdx⟩⟩⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, henv, rfl, hseed, hrep, hce, hb, hX_tl, hcf_fn,
      hq_lt, hv_lt, hcol1, hcol0⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    have hbp_alloc : capFrontWhp n_max ≤ X →
        (fastInsertAlloc n_max b X fs).backPtr b (X - capFrontWhp n_max) < poolSizeWhp n_max := by
      intro hcf
      unfold fastInsertAlloc; dsimp only
      rw [ite_eq_left hcf]; dsimp only
      simp only [Function.update_self]
      exact (hcf_fn hcf).2.2
    obtain ⟨_, _, hal_step⟩ :=
      fastInsertAllocGenProg_fastStep henv hb hX_tl hcf_fn hseed hrep (s := s)
    set fsAlloc := fastInsertAlloc n_max b X fs
    set s1 := (Memory.spec 0).clientState s
      (fastInsertAllocGenProg (((mkWhpCoreParams c U V w n_max, base), b), X))
    obtain ⟨_, _, hwq_step⟩ :=
      insWriteQVAtGenProg_fastStep (fs := fsAlloc) henv hb hX_tl hbp_alloc hq_lt hv_lt
        hal_step.2.1 hal_step.2.2.1 (s := s1)
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep, hb, hX_tl, hcf_fn⟩
    | exact ⟨c, U, V, w, n_max, θ, fsAlloc, henv, rfl,
        hal_step.2.1, hal_step.2.2.1, hb, hX_tl, hbp_alloc, hq_lt⟩
    | (obtain ⟨hna_cap, hia_cap, curMap, hv_cur⟩ := hcol1 (by assumption)
       exact ⟨c, U, V, w, n_max, θ, _, curMap, henv, rfl, hwq_step.2.1, hwq_step.2.2.1,
         hce, hb, hX_tl, hna_cap, hia_cap, hv_cur⟩)
    | (obtain ⟨hlIdx_eq, hlIdx, hfp_lt, hlic, lm, hv_l⟩ := hcol0 (by assumption)
       exact ⟨c, U, V, w, n_max, θ, _, lm, henv, rfl, hwq_step.2.1, hwq_step.2.2.1,
         hb, hX_tl, hlIdx_eq, hlIdx, hfp_lt, hlic, hv_l⟩)
  )

private theorem fastInsertFreshGenProg_fastStep
    {c U V w n_max base b X q_val v_val rKey fp lIdx : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {s : Memory.State} (hasFpCollision : Bool)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hce : fs.curEp = 0 ∨ fs.curEp = 1)
    (hb : b < numBucketsWhp n_max) (hX_tl : X < totalLocalCoordsWhp n_max)
    (hcf_fn : capFrontWhp n_max ≤ X →
      0 < fs.poolFreeTop ∧
      fs.poolFreeTop ≤ poolSizeWhp n_max ∧
      fs.poolFreeStack (fs.poolFreeTop - 1) < poolSizeWhp n_max)
    (hq_lt : q_val < 2 ^ quotBitsWhp U n_max)
    (hv_lt : v_val < 2 ^ valBits V)
    (hcol_t : hasFpCollision = true →
      (fs.buf fs.curEp).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
      (fs.buf fs.curEp).itemAlloc < qEpochWhp n_max ∧
      ∃ curMap, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) curMap)
    (hcol_f : hasFpCollision = false →
      lIdx = fs.liveSliceIdx b ∧
      lIdx < 3 * numBucketsWhp n_max ∧
      fp < 2 ^ fpBitsWhp n_max ∧
      fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
      ∃ lm, ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices lIdx) lm)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem) :
    let hasCol := if hasFpCollision then 1 else 0
    let prog := fastInsertFreshGenProg
      ((((mkWhpCoreParams c U V w n_max, base), (b, X)), (q_val, v_val)),
       (hasCol, (rKey, (fp, lIdx))))
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 20 * cTabWhp c + 2462 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      (fastInsertFresh c n_max b X q_val v_val rKey fp lIdx hasFpCollision
        (fastInsertAlloc n_max b X fs)) s s' := by
  set cp := mkWhpCoreParams c U V w n_max
  have hbp_alloc : capFrontWhp n_max ≤ X →
      (fastInsertAlloc n_max b X fs).backPtr b (X - capFrontWhp n_max) < poolSizeWhp n_max := by
    intro hcf
    unfold fastInsertAlloc; dsimp only
    rw [ite_eq_left hcf]; dsimp only
    simp only [Function.update_self]
    exact (hcf_fn hcf).2.2
  obtain ⟨hal_mc, hal_vp, hal_step⟩ :=
    fastInsertAllocGenProg_fastStep henv hb hX_tl hcf_fn hseed hrep (s := s)
  set fsAlloc := fastInsertAlloc n_max b X fs
  set s1 := (Memory.spec 0).clientState s (fastInsertAllocGenProg (((cp, base), b), X))
  obtain ⟨hwq_mc, hwq_vp, hwq_step⟩ :=
    insWriteQVAtGenProg_fastStep (fs := fsAlloc) henv hb hX_tl hbp_alloc hq_lt hv_lt
      hal_step.2.1 hal_step.2.2.1 (s := s1)
  set fsQV : FastState :=
    { fsAlloc with
      quotArr := Function.update fsAlloc.quotArr (fsAlloc.physSlot n_max b X) q_val
      valArr := Function.update fsAlloc.valArr (fsAlloc.physSlot n_max b X) v_val }
  set s2 := (Memory.spec 0).clientState s1
    (insWriteQVAtGenProg ((((cp, base), b), X), (q_val, v_val)))
  dsimp only
  unfold fastInsertFreshGenProg fastInsertFresh; dsimp only; simp only [pure_bind]
  cases hasFpCollision with
  | true =>
    simp only [↓reduceIte]
    obtain ⟨hna_cap, hia_cap, curMap, hv_cur⟩ := hcol_t rfl
    obtain ⟨hfc_mc, hfc_vp, hfc_step⟩ :=
      insFinishCollisionGenProg_fastStep (fs := fsQV) henv hce hb hX_tl hna_cap hia_cap hv_cur
        hwq_step.2.1 hwq_step.2.2.1 (rKey := rKey) (s := s2)
    have hs'_eq : (Memory.spec 0).clientState s
        (fastInsertAllocGenProg (((cp, base), b), X) >>= fun _ =>
          insWriteQVAtGenProg ((((cp, base), b), X), (q_val, v_val)) >>= fun _ =>
          insFinishCollisionGenProg ((((cp, base), b), X), rKey)) =
        (Memory.spec 0).clientState s2
          (insFinishCollisionGenProg ((((cp, base), b), X), rKey)) := by
      rw [clientState_bind, clientState_bind]
    rw [hs'_eq]
    refine ⟨?_, ?_, (hal_step.trans hwq_step).trans hfc_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      dsimp only [s1, s2, cp] at hal_mc hwq_mc hfc_mc ⊢; omega
    · exact validProg_bind hal_vp (validProg_bind hwq_vp hfc_vp)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, zero_ne_one]
    obtain ⟨hlIdx_eq, hlIdx, hfp_lt, hlic, lm, hv_l⟩ := hcol_f rfl
    obtain ⟨hfd_mc, hfd_vp, hfd_step⟩ :=
      insFinishDirectGenProg_fastStep (fs := fsQV) henv hb hX_tl hlIdx_eq hlIdx hfp_lt hlic hv_l
        hwq_step.2.1 hwq_step.2.2.1 (s := s2)
    have hs'_eq : (Memory.spec 0).clientState s
        (fastInsertAllocGenProg (((cp, base), b), X) >>= fun _ =>
          insWriteQVAtGenProg ((((cp, base), b), X), (q_val, v_val)) >>= fun _ =>
          insFinishDirectGenProg ((((cp, base), b), X), (fp, lIdx))) =
        (Memory.spec 0).clientState s2
          (insFinishDirectGenProg ((((cp, base), b), X), (fp, lIdx))) := by
      rw [clientState_bind, clientState_bind]
    rw [hs'_eq]
    refine ⟨?_, ?_, (hal_step.trans hwq_step).trans hfd_step⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      dsimp only [s1, s2, cp] at hal_mc hwq_mc hfd_mc ⊢; omega
    · exact validProg_bind hal_vp (validProg_bind hwq_vp hfd_vp)

private theorem overmarsBucketStepBounds_insFresh {c U V n_max b q_val v_val rKey fp : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} (hasFpCollision : Bool)
    (hv : ValidFastState c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max)
    (hX_tl : fs.bktCount b < totalLocalCoordsWhp n_max)
    (hcf_fn : capFrontWhp n_max ≤ fs.bktCount b →
      0 < fs.poolFreeTop ∧
      fs.poolFreeTop ≤ poolSizeWhp n_max ∧
      fs.poolFreeStack (fs.poolFreeTop - 1) < poolSizeWhp n_max)
    (hq_lt : q_val < 2 ^ quotBitsWhp U n_max) :
    OvermarsBucketStepBounds U n_max b
      (fastInsertFresh c n_max b (fs.bktCount b) q_val v_val rKey fp (fs.liveSliceIdx b)
        hasFpCollision (fastInsertAlloc n_max b (fs.bktCount b) fs)) := by
  set X := fs.bktCount b
  set fsIns := fastInsertFresh c n_max b X q_val v_val rKey fp (fs.liveSliceIdx b) hasFpCollision
    (fastInsertAlloc n_max b X fs)
  have h2tl := (large_index_bounds hv.hth).2.2.1
  have hL2 := two_le_slabScale n_max
  have hL12 : 4096 ≤ (slabScale n_max) ^ 12 := by
    calc 4096 = 2 ^ 12 := by decide
      _ ≤ (slabScale n_max) ^ 12 := Nat.pow_le_pow_left hL2 12
  have hX_3L : X < 3 * (slabScale n_max) ^ 12 :=
    hX_tl.trans_le totalLocalCoordsWhp_le_three_mul
  have hce_ins : fsIns.curEp = fs.curEp := by cases hasFpCollision <;> rfl
  have hlr_ins : fsIns.liveRole = fs.liveRole := by cases hasFpCollision <;> rfl
  have hor_ins : fsIns.overmarsRole = fs.overmarsRole := by cases hasFpCollision <;> rfl
  have hoa_ins : fsIns.overmarsActive = fs.overmarsActive := by cases hasFpCollision <;> rfl
  have hoc_ins : fsIns.overmarsCursor = fs.overmarsCursor := by cases hasFpCollision <;> rfl
  have hoi_ins : fsIns.overmarsInsCount = fs.overmarsInsCount := by cases hasFpCollision <;> rfl
  have hcnt_ins : fsIns.bktCount b = X + 1 := by
    cases hasFpCollision <;> simp [fsIns, fastInsertFresh, fastInsertAlloc]
  have hq_ins : ∀ i < n_max, fsIns.quotArr i < 2 ^ quotBitsWhp U n_max := by
    intro i _
    have hqa : fsIns.quotArr =
        Function.update fs.quotArr ((fastInsertAlloc n_max b X fs).physSlot n_max b X) q_val := by
      cases hasFpCollision <;> rfl
    rw [hqa]
    by_cases hi : i = (fastInsertAlloc n_max b X fs).physSlot n_max b X
    · subst hi; simp only [Function.update_self]; exact hq_lt
    · rw [Function.update_of_ne hi]; exact (hv.qv_global i).1
  have hbp_ins : ∀ k < fsIns.bktCount b - capFrontWhp n_max,
      fsIns.backPtr b k < poolSizeWhp n_max := by
    rw [hcnt_ins]
    intro k hk
    have hbp_eq : fsIns.backPtr = (fastInsertAlloc n_max b X fs).backPtr := by
      cases hasFpCollision <;> rfl
    rw [hbp_eq]
    by_cases hcf : capFrontWhp n_max ≤ X
    · unfold fastInsertAlloc; dsimp only; rw [ite_eq_left hcf]; dsimp only
      rw [Function.update_self]
      by_cases hk_eq : k = X - capFrontWhp n_max
      · subst hk_eq; rw [Function.update_self]; exact (hcf_fn hcf).2.2
      · rw [Function.update_of_ne hk_eq]; exact (hv.backPtr_valid b hb k (by omega)).1
    · omega
  have hom_idx : fsIns.overmarsSliceIdx b = fs.overmarsSliceIdx b := by
    unfold FastState.overmarsSliceIdx; rw [hor_ins]
  have hom_sl : fsIns.slices (fs.overmarsSliceIdx b) = fs.slices (fs.overmarsSliceIdx b) := by
    cases hasFpCollision with
    | true => rfl
    | false =>
      have hne_role := (hv.roles_valid b hb).2.2
      have hne_idx : fs.overmarsSliceIdx b ≠ fs.liveSliceIdx b := by
        unfold FastState.overmarsSliceIdx FastState.liveSliceIdx; omega
      dsimp only [fsIns, fastInsertFresh, fastInsertAlloc]
      exact Function.update_of_ne hne_idx _ _
  refine ⟨hb, hce_ins ▸ hv.curEp_or, hlr_ins ▸ (hv.roles_valid b hb).1,
    hor_ins ▸ (hv.roles_valid b hb).2.1, by omega, hq_ins, hbp_ins, ?_⟩
  unfold overmarsAfterActivate
  rw [hoa_ins]
  intro ha1
  rcases hv.overmars_valid b hb with ⟨ha0, _⟩ | ⟨ha_act, _, hcur_lt, _, hins_le, omMap0, hv0, _⟩
  · by_cases htrig : 5 * (slabScale n_max) ^ 12 ≤ fsIns.liveInsCount b
    · have hc0 : fs.overmarsActive b = 0 ∧ 5 * (slabScale n_max) ^ 12 ≤ fsIns.liveInsCount b :=
        ⟨ha0, htrig⟩
      rw [ite_eq_left hc0]
      dsimp only [FastState.overmarsSliceIdx]
      simp only [Function.update_self]
      exact ⟨by omega, by omega, ⟨fun _ => none, validWhpSlice_zero _ 0 _⟩⟩
    · have hnc0 : ¬(fs.overmarsActive b = 0 ∧ 5 * (slabScale n_max) ^ 12 ≤ fsIns.liveInsCount b) :=
        fun ⟨_, h⟩ => htrig h
      rw [ite_eq_right hnc0] at ha1; rw [hoa_ins] at ha1; omega
  · have hnc0 : ¬(fs.overmarsActive b = 0 ∧ 5 * (slabScale n_max) ^ 12 ≤ fsIns.liveInsCount b) :=
      by omega
    rw [ite_eq_right hnc0, hoc_ins, hoi_ins, hom_idx, hom_sl]
    exact ⟨by omega, by omega, ⟨omMap0, hv0⟩⟩

/-- Commit fresh insertion and run `overmarsStepGenProg`, returning `1`. -/
@[irreducible] def insCommitFreshGenProg :
    (((WhpParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ))) → Memory.Prog ℕ
  | ((((wp, base), (b, X)), (q_val, v_val)), (hasCol, (rKey, (fp, lIdx)))) => do
    fastInsertFreshGenProg
      ((((wp.1, base), (b, X)), (q_val, v_val)), (hasCol, (rKey, (fp, lIdx))))
    overmarsStepGenProg ((wp, base), b)
    pure 1

theorem realizes_insCommitFreshGen :
    Realizes .exact insCommitFreshGenProg
      (WordEncoding.encode
        (α := (((WhpParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × ℕ)))))
      (WordEncoding.encode (α := ℕ))
      (fun w ((((wp, base), (b, X)), (q_val, v_val)), (hasCol, (_, (fp, lIdx)))) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U)
            (hasFpCollision : Bool),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          b < numBucketsWhp n_max ∧
          X = fs.bktCount b ∧
          X < totalLocalCoordsWhp n_max ∧
          (capFrontWhp n_max ≤ X → 0 < fs.poolFreeTop) ∧
          q_val < 2 ^ quotBitsWhp U n_max ∧
          v_val < V ∧
          hasCol = (if hasFpCollision then 1 else 0) ∧
          lIdx = fs.liveSliceIdx b ∧
          fp < 2 ^ fpBitsWhp n_max)
      (fun _ _ => 0) := by
  unfold insCommitFreshGenProg
  have hfr := realizes_fastInsertFreshGen
  have hom := realizes_overmarsStepGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨wp, base⟩, ⟨b, X⟩⟩, ⟨q_val, v_val⟩⟩, ⟨hasCol, ⟨rKey, ⟨fp, lIdx⟩⟩⟩⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, hasFpCollision, henv, heq_wp, hseed, hrep, hv,
      hb, rfl, hX_tl, hpos_fn, hq_lt, hv_v, rfl, rfl, hfp_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    have hv_pow := val_lt_two_pow_valBits hv_v
    have hcf_fn : capFrontWhp n_max ≤ fs.bktCount b →
        0 < fs.poolFreeTop ∧
        fs.poolFreeTop ≤ poolSizeWhp n_max ∧
        fs.poolFreeStack (fs.poolFreeTop - 1) < poolSizeWhp n_max := fun hcf =>
      ⟨hpos_fn hcf, hv.poolFreeTop_le, hv.freeStack_lt _ (by have := hpos_fn hcf; omega)⟩
    obtain ⟨hia_le, hna_le, curMap, hv_cur, _⟩ := hv.bufCur_valid
    obtain ⟨hna_cap, hia_cap⟩ := bufTrie_caps_of_bounds hth hia_le hna_le
    obtain ⟨liveMap, hv_live, _⟩ := hv.live_valid b hb
    have hlic := liveInsCount_le_eight hv.toCore hb (hv.overmars_valid b hb)
    have hlr_lt := (hv.roles_valid b hb).1
    have hlIdx : fs.liveSliceIdx b < 3 * numBucketsWhp n_max := by
      unfold FastState.liveSliceIdx; omega
    have hcol_t : hasFpCollision = true →
        (fs.buf fs.curEp).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
        (fs.buf fs.curEp).itemAlloc < qEpochWhp n_max ∧
        ∃ cm, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) cm :=
      fun _ => ⟨hna_cap, hia_cap, curMap, hv_cur⟩
    have hcol_f : hasFpCollision = false →
        fs.liveSliceIdx b = fs.liveSliceIdx b ∧
        fs.liveSliceIdx b < 3 * numBucketsWhp n_max ∧
        fp < 2 ^ fpBitsWhp n_max ∧
        fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
        ∃ lm, ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices (fs.liveSliceIdx b)) lm :=
      fun _ => ⟨rfl, hlIdx, hfp_lt, hlic, liveMap, hv_live⟩
    obtain ⟨_, _, hfr_step⟩ :=
      fastInsertFreshGenProg_fastStep hasFpCollision henv hv.curEp_or hb hX_tl hcf_fn
        hq_lt hv_pow hcol_t hcol_f hseed hrep (rKey := rKey) (s := s)
    have hbnds_ins :=
      overmarsBucketStepBounds_insFresh hasFpCollision hv hb hX_tl hcf_fn hq_lt
        (v_val := v_val) (rKey := rKey) (fp := fp)
    rw [hcp_eq] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hv.curEp_or, hb, hX_tl, hcf_fn,
        hq_lt, hv_pow,
        fun _ => ⟨hna_cap, hia_cap, curMap, hv_cur⟩,
        fun _ => ⟨rfl, hlIdx, hfp_lt, hlic, liveMap, hv_live⟩⟩
    | exact ⟨c, U, V, w, n_max, θ, _, henv, rfl, hfr_step.2.1, hfr_step.2.2.1, hbnds_ins⟩
  )

theorem insCommitFreshGenProg_spec {c U V w n_max base b q_val v_val rKey fp : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (hasFpCollision : Bool)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max)
    (hX_tl : fs.bktCount b < totalLocalCoordsWhp n_max)
    (hpos_fn : capFrontWhp n_max ≤ fs.bktCount b → 0 < fs.poolFreeTop)
    (hq_lt : q_val < 2 ^ quotBitsWhp U n_max)
    (hv_v : v_val < V)
    (hfp_lt : fp < 2 ^ fpBitsWhp n_max) :
    let X := fs.bktCount b
    let lIdx := fs.liveSliceIdx b
    let hasCol := if hasFpCollision then 1 else 0
    let prog := insCommitFreshGenProg
      ((((mkWhpParams c U V w n_max, base), (b, X)), (q_val, v_val)),
       (hasCol, (rKey, (fp, lIdx))))
    let s' := (Memory.spec 0).clientState s prog
    let fsIns := fastInsertFresh c n_max b X q_val v_val rKey fp lIdx hasFpCollision
      (fastInsertAlloc n_max b X fs)
    (Memory.spec 0).clientResult s prog = 1 ∧
    memoryCost prog s ≤ 20 * cTabWhp c + 32 * hashEvalCostWhp c + 41788 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (overmarsStep c U n_max θ b fsIns) s s' := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  set X := fs.bktCount b
  set lIdx := fs.liveSliceIdx b
  set hasCol := if hasFpCollision then 1 else 0
  have hv_pow := val_lt_two_pow_valBits hv_v
  have hcf_fn : capFrontWhp n_max ≤ X →
      0 < fs.poolFreeTop ∧
      fs.poolFreeTop ≤ poolSizeWhp n_max ∧
      fs.poolFreeStack (fs.poolFreeTop - 1) < poolSizeWhp n_max := fun hcf =>
    ⟨hpos_fn hcf, hv.poolFreeTop_le, hv.freeStack_lt _ (by have := hpos_fn hcf; omega)⟩
  obtain ⟨hia_le, hna_le, curMap, hv_cur, _⟩ := hv.bufCur_valid
  obtain ⟨hna_cap, hia_cap⟩ := bufTrie_caps_of_bounds hth hia_le hna_le
  obtain ⟨liveMap, hv_live, _⟩ := hv.live_valid b hb
  have hlic := liveInsCount_le_eight hv.toCore hb (hv.overmars_valid b hb)
  have hlr_lt := (hv.roles_valid b hb).1
  have hlIdx : lIdx < 3 * numBucketsWhp n_max := by
    dsimp only [lIdx]; unfold FastState.liveSliceIdx; omega
  have hcol_t : hasFpCollision = true →
      (fs.buf fs.curEp).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
      (fs.buf fs.curEp).itemAlloc < qEpochWhp n_max ∧
      ∃ cm, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) cm :=
    fun _ => ⟨hna_cap, hia_cap, curMap, hv_cur⟩
  have hcol_f : hasFpCollision = false →
      lIdx = fs.liveSliceIdx b ∧
      lIdx < 3 * numBucketsWhp n_max ∧
      fp < 2 ^ fpBitsWhp n_max ∧
      fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
      ∃ lm, ValidWhpSlice n_max (fs.liveInsCount b) (fs.slices lIdx) lm :=
    fun _ => ⟨rfl, hlIdx, hfp_lt, hlic, liveMap, hv_live⟩
  obtain ⟨hfr_mc, hfr_vp, hfr_step⟩ :=
    fastInsertFreshGenProg_fastStep hasFpCollision henv hv.curEp_or hb hX_tl hcf_fn
      hq_lt hv_pow hcol_t hcol_f hseed hrep (rKey := rKey) (s := s)
  set s1 := (Memory.spec 0).clientState s
    (fastInsertFreshGenProg
      ((((cp, base), (b, X)), (q_val, v_val)), (hasCol, (rKey, (fp, lIdx)))))
  have hbnds_ins :=
    overmarsBucketStepBounds_insFresh hasFpCollision hv hb hX_tl hcf_fn hq_lt
      (v_val := v_val) (rKey := rKey) (fp := fp)
  obtain ⟨hom_mc, hom_vp, hom_step⟩ :=
    overmarsStepGenProg_fastStep henv hbnds_ins hfr_step.2.1 hfr_step.2.2.1 (s := s1)
  dsimp only
  unfold insCommitFreshGenProg; dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  have hs'_eq : (Memory.spec 0).clientState s
      (fastInsertFreshGenProg
          ((((cp, base), (b, X)), (q_val, v_val)), (hasCol, (rKey, (fp, lIdx)))) >>= fun _ =>
        overmarsStepGenProg ((mkWhpParams c U V w n_max, base), b) >>= fun _ => pure 1) =
      (Memory.spec 0).clientState s1
        (overmarsStepGenProg ((mkWhpParams c U V w n_max, base), b)) := by
    rw [clientState_bind, clientState_bind, clientState_pure_whp]
  rw [hs'_eq]
  refine ⟨?_, ?_, ?_, hfr_step.trans hom_step⟩
  · rw [clientResult_bind, clientResult_bind, clientResult_pure_whp]
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, memoryCost_pure]
    dsimp only [s1, cp, X, lIdx, hasCol] at hfr_mc hom_mc ⊢; omega
  · exact validProg_bind hfr_vp (validProg_bind hom_vp (validProg_pure _))

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
