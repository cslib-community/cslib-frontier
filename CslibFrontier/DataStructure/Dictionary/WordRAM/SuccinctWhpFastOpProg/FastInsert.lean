/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastBaseProg
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg.InsOverwrite
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg.InsGuards
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg.InsFresh
import CslibFrontier.Tactic.Realize

/-!
# Fast-Mode Guarded Insertion / Overwrite (`fastInsertGenProg`)

Worst-case `O_c(1)` guarded insertion and overwrite program refining `fastInsert` and leaving
memory untouched whenever any fast-mode guard rejects.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fastInsertGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_fastInsertGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fastInsertGenProg_spec`
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

private theorem bind_read_zero {α : Type} {c U V w n_max base C₀ C B : ℕ}
    {s : Memory.State} {p : Memory.Prog α} {k : α → Memory.Prog ℕ} {a : α}
    (hp_st : (Memory.spec 0).clientState s p = s)
    (hp_res : (Memory.spec 0).clientResult s p = a)
    (hp_mc : memoryCost p s ≤ C)
    (hp_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s p)
    (hk : C₀ + C + memoryCost (k a) s ≤ B ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s (k a) ∧
      ((Memory.spec 0).clientResult s (k a) = 0 ∧
        (Memory.spec 0).clientState s (k a) = s)) :
    C₀ + memoryCost (p >>= k) s ≤ B ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s (p >>= k) ∧
      ((Memory.spec 0).clientResult s (p >>= k) = 0 ∧
        (Memory.spec 0).clientState s (p >>= k) = s) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hp_st, hp_res]
    have := hk.1
    omega
  · refine validProg_bind hp_vp ?_
    rw [hp_st, hp_res]
    exact hk.2.1
  · rw [clientResult_bind, clientState_bind, hp_st, hp_res]
    exact hk.2.2

private theorem bind_read_some {α : Type} {c U V w n_max base C₀ C B : ℕ}
    {θ : SeedWhp c U n_max} {fs' : FastState} {s : Memory.State}
    {p : Memory.Prog α} {k : α → Memory.Prog ℕ} {a : α}
    (hp_st : (Memory.spec 0).clientState s p = s)
    (hp_res : (Memory.spec 0).clientResult s p = a)
    (hp_mc : memoryCost p s ≤ C)
    (hp_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s p)
    (hk : C₀ + C + memoryCost (k a) s ≤ B ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s (k a) ∧
      ((Memory.spec 0).clientResult s (k a) = 1 ∧
        FastStateStep base c U V w n_max θ fs' s ((Memory.spec 0).clientState s (k a)))) :
    C₀ + memoryCost (p >>= k) s ≤ B ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s (p >>= k) ∧
      ((Memory.spec 0).clientResult s (p >>= k) = 1 ∧
        FastStateStep base c U V w n_max θ fs' s ((Memory.spec 0).clientState s (p >>= k))) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hp_st, hp_res]
    have := hk.1
    omega
  · refine validProg_bind hp_vp ?_
    rw [hp_st, hp_res]
    exact hk.2.1
  · rw [clientResult_bind, clientState_bind, hp_st, hp_res]
    exact hk.2.2

private theorem pure_zero_opt {c U V w n_max base C₀ B : ℕ}
    {s : Memory.State} (hB : C₀ ≤ B) :
    C₀ + memoryCost (pure 0 : Memory.Prog ℕ) s ≤ B ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s (pure 0) ∧
      ((Memory.spec 0).clientResult s (pure 0) = 0 ∧
        (Memory.spec 0).clientState s (pure 0) = s) := by
  simp only [memoryCost_pure, Nat.add_zero]
  exact ⟨hB, validProg_pure 0, rfl, rfl⟩

/-- Post-`rKey`-guard step: compute `(hasFpCollision, (fp, lIdx))`, check Guard 3, and commit. -/
@[irreducible] private def insAfterRKeyGenProg :
    (((WhpParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ) → Memory.Prog ℕ
  | ((((wp, base), (b, X)), (q_val, v_val)), (u_val, rKey)) => do
    let z1 ← pure 1
    let cfp ← insReadFpLiveGenProg ((wp, base), (b, u_val))
    let ok3 ← insCheckFpCapOptGenProg (((wp.1, base), cfp.1), rKey)
    if ok3 = z1 then
      insCommitFreshGenProg ((((wp, base), (b, X)), (q_val, v_val)), (cfp.1, (rKey, cfp.2)))
    else
      pure 0

private theorem realizes_insAfterRKeyGen :
    Realizes .exact insAfterRKeyGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w ((((wp, base), (b, X)), (q_val, v_val)), (u_val, _)) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          u_val < U ∧
          b < numBucketsWhp n_max ∧
          X = fs.bktCount b ∧
          X < totalLocalCoordsWhp n_max ∧
          (capFrontWhp n_max ≤ X → 0 < fs.poolFreeTop) ∧
          q_val < 2 ^ quotBitsWhp U n_max ∧
          v_val < V)
      (fun _ _ => 0) := by
  unfold insAfterRKeyGenProg
  have hrf := realizes_insReadFpLiveGen
  have hck := realizes_insCheckFpCapOptGen
  have hcm := realizes_insCommitFreshGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨wp, base⟩, ⟨b, X⟩⟩, ⟨q_val, v_val⟩⟩, ⟨u_val, rKey⟩⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv, hu,
      hb, rfl, hX_tl, hpos_fn, hq_lt, hv_v⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    set u : Fin U := ⟨u_val, hu⟩
    obtain ⟨_, _, curMap, hv_cur, _⟩ := hv.bufCur_valid
    obtain ⟨liveMap, hv_live, _⟩ := hv.live_valid b hb
    have hlic := liveInsCount_le_eight hv.toCore hb (hv.overmars_valid b hb)
    have hlr_lt := (hv.roles_valid b hb).1
    obtain ⟨hrf_st, hrf_res, _, _⟩ :=
      insReadFpLiveGenProg_spec u henv hseed hrep hb hlr_lt hlic hv_live (s := s)
    dsimp only [u] at hrf_st hrf_res
    set fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) ⟨u_val, hu⟩
    set hasFpCollision :=
      (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (fs.slices (fs.liveSliceIdx b)) fp).isSome
    have hfp_lt : fp < 2 ^ fpBitsWhp n_max := by
      dsimp only [fp, fpOfSalt]
      split_ifs with hs
      · exact fpHash_lt c U n_max θ.2 ⟨fs.bktSalt b, hs⟩ ⟨u_val, hu⟩
      · exact Nat.two_pow_pos _
    obtain ⟨hck_st, _, _, _⟩ :=
      insCheckFpCapOptGenProg_spec hasFpCollision henv hv.curEp_or hv_cur hrep (rKey := rKey)
        (s := s)
    simp only [hcp_eq] at *
    simp only [hrf_st, hrf_res, hck_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, θ, fs, liveMap, henv, rfl, hseed, hrep, hb, hlr_lt, hlic, hv_live⟩
    | exact ⟨c, U, V, w, n_max, fs, curMap, henv, rfl, hrep, hv.curEp_or, hv_cur⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, hasFpCollision, henv, rfl, hseed, hrep, hv,
        hb, rfl, hX_tl, hpos_fn, hq_lt, hv_v, rfl, rfl, hfp_lt⟩
  )

/-- Evaluate `fpReducedKeyOpt` from `(wp, base, u_val)`. -/
@[irreducible] private def insEvalRKeyGenProg :
    (WhpParams × ℕ) × ℕ → Memory.Prog ℕ
  | ((wp, base), u_val) => do
    let hrt ← mkHashRtGenProg (wp, base)
    fpReducedKeyOptRtProg (hrt, u_val)

private theorem realizes_insEvalRKeyGen :
    Realizes .exact insEvalRKeyGenProg
      (WordEncoding.encode (α := (WhpParams × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((wp, base), _) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem)
      (fun _ _ => 0) := by
  unfold insEvalRKeyGenProg
  have hmh := realizes_mkHashRtGen
  have hrk := realizes_fpReducedKeyOptRt
  realize
  rcases d with ⟨⟨wp, base⟩, u_val⟩
  obtain ⟨c, U, V, w₀, n_max, θ, henv, heq_wp, hseed⟩ := h
  have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
  have hth := henv.2.2.2.1
  obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) hth s
  simp only [Prod.mk.eta, hmh_st, hmh_res] at *
  exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩

private theorem insEvalRKeyGenProg_spec {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {s : Memory.State} (u : Fin U)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem) :
    let prog := insEvalRKeyGenProg ((mkWhpParams c U V w n_max, base), u.val)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = fpReducedKey c U n_max θ.2 u ∧
    memoryCost prog s ≤ 1 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  have hth := henv.2.2.2.1
  obtain ⟨hmh_st, hmh_res, hmh_mc, hmh_vp⟩ :=
    mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hrk_st, hrk_res, hrk_mc, hrk_vp⟩ :=
    fpReducedKeyOptRtProg_spec (kv := u.val) henv hseed (s := s)
  have hrk_eq : (if h : u.val < U then fpReducedKey c U n_max θ.2 ⟨u.val, h⟩ else 0) =
      fpReducedKey c U n_max θ.2 u := by simp [u.isLt]
  rw [hrk_eq] at hrk_res
  dsimp only
  unfold insEvalRKeyGenProg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [clientState_bind, hmh_st, hmh_res, hrk_st]
  · rw [clientResult_bind, hmh_st, hmh_res, hrk_res]
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hmh_st, hmh_res, hmh_mc, Nat.zero_add]; exact hrk_mc
  · refine validProg_bind hmh_vp ?_; rw [hmh_st, hmh_res]; exact hrk_vp

/-- Post-cap-guard step: compute `rKey`, check Guard 2, and delegate to `insAfterRKeyGenProg`. -/
@[irreducible] private def insAfterCapGenProg :
    (((WhpParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ → Memory.Prog ℕ
  | ((((wp, base), (b, X)), (q_val, v_val)), u_val) => do
    let z1 ← pure 1
    let rKey ← insEvalRKeyGenProg ((wp, base), u_val)
    let ok2 ← insCheckRKeyGuardsGenProg ((wp.1, base), rKey)
    if ok2 = z1 then
      insAfterRKeyGenProg ((((wp, base), (b, X)), (q_val, v_val)), (u_val, rKey))
    else
      pure 0

private theorem realizes_insAfterCapGen :
    Realizes .exact insAfterCapGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × (ℕ × ℕ)) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((((wp, base), (b, X)), (q_val, v_val)), u_val) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          u_val < U ∧
          b < numBucketsWhp n_max ∧
          X = fs.bktCount b ∧
          X < totalLocalCoordsWhp n_max ∧
          (capFrontWhp n_max ≤ X → 0 < fs.poolFreeTop) ∧
          q_val < 2 ^ quotBitsWhp U n_max ∧
          v_val < V)
      (fun _ _ => 0) := by
  unfold insAfterCapGenProg
  have her := realizes_insEvalRKeyGen
  have hcg := realizes_insCheckRKeyGuardsGen
  have har := realizes_insAfterRKeyGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨wp, base⟩, ⟨b, X⟩⟩, ⟨q_val, v_val⟩⟩, u_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv, hu,
      hb, rfl, hX_tl, hpos_fn, hq_lt, hv_v⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    set u : Fin U := ⟨u_val, hu⟩
    obtain ⟨_, _, curMap, hv_cur, _⟩ := hv.bufCur_valid
    have hbo_fn : fs.rebStage ≤ 3 →
        ∃ oldMap, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap := by
      intro hle3
      have hbo := hv.bufOld_valid; rw [ite_eq_left hle3] at hbo
      obtain ⟨_, _, oldMap, hv_old, _⟩ := hbo; exact ⟨oldMap, hv_old⟩
    obtain ⟨her_st, her_res, _, _⟩ := insEvalRKeyGenProg_spec u henv hseed (s := s)
    dsimp only [u] at her_st her_res
    obtain ⟨hcg_st, _, _, _⟩ :=
      insCheckRKeyGuardsGenProg_spec henv hv.curEp_or hv_cur hbo_fn hrep
        (rKey := fpReducedKey c U n_max θ.2 ⟨u_val, hu⟩) (s := s)
    simp only [hcp_eq] at *
    simp only [her_st, her_res, hcg_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
    | exact ⟨c, U, V, w, n_max, fs, curMap, henv, rfl, hrep, hv.curEp_or, hv_cur, hbo_fn⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv, hu,
        hb, rfl, hX_tl, hpos_fn, hq_lt, hv_v⟩
  )

/-- Miss branch of `fastInsert`: check Guard 1 and delegate to `insAfterCapGenProg`. -/
@[irreducible] private def fastInsertMissGenProg :
    (((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog ℕ
  | ((((wp, base), (b, q_val)), u_val), v_val) => do
    let z1 ← pure 1
    let cpRes ← insCheckCapPoolGenProg ((wp.1, base), b)
    if cpRes.1 = z1 then
      insAfterCapGenProg ((((wp, base), (b, cpRes.2)), (q_val, v_val)), u_val)
    else
      pure 0

private theorem realizes_fastInsertMissGen :
    Realizes .exact fastInsertMissGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((((wp, base), (b, q_val)), u_val), v_val) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          u_val < U ∧
          b < numBucketsWhp n_max ∧
          q_val < 2 ^ quotBitsWhp U n_max ∧
          v_val < V)
      (fun _ _ => 0) := by
  unfold fastInsertMissGenProg
  have hcp := realizes_insCheckCapPoolGen
  have hac := realizes_insAfterCapGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨wp, base⟩, ⟨b, q_val⟩⟩, u_val⟩, v_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv, hu,
      hb, hq_lt, hv_v⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    obtain ⟨hcp_st, hcp_res, _, _⟩ := insCheckCapPoolGenProg_spec henv hb hrep (s := s)
    simp only [hcp_eq] at *
    rw [hcp_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, henv, rfl⟩
    | (rw [wp_large_M hth]; exact hb)
    | (have hhit : ((Memory.spec 0).clientResult s
          (insCheckCapPoolGenProg ((mkWhpCoreParams c U V w n_max, base), b))).1 = 1 := by
          assumption
       rw [hcp_res] at hhit ⊢
       by_cases hbad1 : totalLocalCoordsWhp n_max ≤ fs.bktCount b ∨
           (capFrontWhp n_max ≤ fs.bktCount b ∧ fs.poolFreeTop = 0)
       · rw [ite_eq_left hbad1] at hhit; cases hhit
       · rw [ite_eq_right hbad1]; dsimp only
         exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv, hu, hb,
           rfl, by omega, fun hcf => by omega, hq_lt, hv_v⟩)
  )

private theorem fastInsertMissGenProg_spec {c U V w n_max base b q_val v_val : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State} (u : Fin U)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max)
    (hq_lt : q_val < 2 ^ quotBitsWhp U n_max)
    (hv_v : v_val < V) :
    let prog := fastInsertMissGenProg
      ((((mkWhpParams c U V w n_max, base), (b, q_val)), u.val), v_val)
    let s' := (Memory.spec 0).clientState s prog
    let X := fs.bktCount b
    let cf := capFrontWhp n_max
    let rKey := fpReducedKey c U n_max θ.2 u
    let fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
    let lIdx := fs.liveSliceIdx b
    let hasFpCollision :=
      (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
        (fs.slices lIdx) fp).isSome
    let missOpt : Option FastState :=
      if totalLocalCoordsWhp n_max ≤ X ∨ (cf ≤ X ∧ fs.poolFreeTop = 0) then
        none
      else if (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey).isSome ∨
          (fs.rebStage ≤ 3 ∧
            (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey).isSome) then
        none
      else if hasFpCollision ∧
          !bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey ∧
          2 * sMaxWhp c n_max ≤ (fs.buf fs.curEp).itemAlloc then
        none
      else
        some (overmarsStep c U n_max θ b
          (fastInsertFresh c n_max b X q_val v_val rKey fp lIdx hasFpCollision
        (fastInsertAlloc n_max b X fs)))
    memoryCost prog s ≤ 26 * cTabWhp c + 33 * hashEvalCostWhp c + 42082 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    match missOpt with
    | some fs' =>
      (Memory.spec 0).clientResult s prog = 1 ∧
      FastStateStep base c U V w n_max θ fs' s s'
    | none =>
      (Memory.spec 0).clientResult s prog = 0 ∧ s' = s := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  set X := fs.bktCount b
  set cf := capFrontWhp n_max
  set rKey := fpReducedKey c U n_max θ.2 u
  set fp := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
  set lIdx := fs.liveSliceIdx b
  set hasFpCollision :=
    (btreeLookup (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
      (fs.slices lIdx) fp).isSome
  obtain ⟨hcp_st, hcp_res, hcp_mc, hcp_vp⟩ :=
    insCheckCapPoolGenProg_spec henv hb hrep (s := s)
  dsimp only
  rw [← Nat.zero_add (memoryCost _ s)]
  unfold fastInsertMissGenProg
  dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  simp only [pure_bind]
  by_cases hbad1 : totalLocalCoordsWhp n_max ≤ X ∨ (cf ≤ X ∧ fs.poolFreeTop = 0)
  · rw [ite_eq_left hbad1] at hcp_res ⊢
    refine bind_read_zero hcp_st hcp_res hcp_mc hcp_vp ?_
    simpa only [zero_ne_one, ↓reduceIte] using pure_zero_opt (by omega)
  · rw [ite_eq_right hbad1] at hcp_res ⊢
    have hX_tl : X < totalLocalCoordsWhp n_max := by omega
    have hpos_fn : cf ≤ X → 0 < fs.poolFreeTop := fun _ => by omega
    obtain ⟨_, _, curMap, hv_cur, _⟩ := hv.bufCur_valid
    have hbo_fn : fs.rebStage ≤ 3 →
        ∃ oldMap, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) oldMap := by
      intro hle3
      obtain ⟨_, _, oldMap, hv_old, _⟩ := ite_eq_left hle3 ▸ hv.bufOld_valid
      exact ⟨oldMap, hv_old⟩
    obtain ⟨her_st, her_res, her_mc, her_vp⟩ := insEvalRKeyGenProg_spec u henv hseed (s := s)
    obtain ⟨hcg_st, hcg_res, hcg_mc, hcg_vp⟩ :=
      insCheckRKeyGuardsGenProg_spec henv hv.curEp_or hv_cur hbo_fn hrep (rKey := rKey) (s := s)
    by_cases hbad2 : (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey).isSome ∨
        (fs.rebStage ≤ 3 ∧
          (bufLookup (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey).isSome)
    · rw [ite_eq_left hbad2] at hcg_res ⊢
      refine bind_read_zero hcp_st hcp_res hcp_mc hcp_vp ?_
      simp only [↓reduceIte]
      unfold insAfterCapGenProg
      dsimp only
      rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
      simp only [pure_bind]
      refine bind_read_zero her_st her_res her_mc her_vp ?_
      refine bind_read_zero hcg_st hcg_res hcg_mc hcg_vp ?_
      simpa only [zero_ne_one, ↓reduceIte] using pure_zero_opt (by omega)
    · rw [ite_eq_right hbad2] at hcg_res ⊢
      obtain ⟨liveMap, hv_live, _⟩ := hv.live_valid b hb
      have hlic := liveInsCount_le_eight hv.toCore hb (hv.overmars_valid b hb)
      have hlr_lt := (hv.roles_valid b hb).1
      obtain ⟨hrf_st, hrf_res, hrf_mc, hrf_vp⟩ :=
        insReadFpLiveGenProg_spec u henv hseed hrep hb hlr_lt hlic hv_live (s := s)
      obtain ⟨hck_st, hck_res, hck_mc, hck_vp⟩ :=
        insCheckFpCapOptGenProg_spec hasFpCollision henv hv.curEp_or hv_cur hrep
          (rKey := rKey) (s := s)
      by_cases hbad3 : hasFpCollision ∧
          !bufEverPresent (cTabWhp c) (bCharWhp n_max) (fs.buf fs.curEp) rKey ∧
          2 * sMaxWhp c n_max ≤ (fs.buf fs.curEp).itemAlloc
      · rw [ite_eq_left hbad3] at hck_res ⊢
        refine bind_read_zero hcp_st hcp_res hcp_mc hcp_vp ?_
        simp only [↓reduceIte]
        unfold insAfterCapGenProg
        dsimp only
        rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
        simp only [pure_bind]
        refine bind_read_zero her_st her_res her_mc her_vp ?_
        refine bind_read_zero hcg_st hcg_res hcg_mc hcg_vp ?_
        simp only [↓reduceIte]
        unfold insAfterRKeyGenProg
        dsimp only
        rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
        simp only [pure_bind]
        refine bind_read_zero hrf_st hrf_res hrf_mc hrf_vp ?_
        dsimp only
        refine bind_read_zero hck_st hck_res hck_mc hck_vp ?_
        simpa only [zero_ne_one, ↓reduceIte] using pure_zero_opt (by omega)
      · rw [ite_eq_right hbad3] at hck_res ⊢
        refine bind_read_some hcp_st hcp_res hcp_mc hcp_vp ?_
        simp only [↓reduceIte]
        unfold insAfterCapGenProg
        dsimp only
        rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
        simp only [pure_bind]
        refine bind_read_some her_st her_res her_mc her_vp ?_
        refine bind_read_some hcg_st hcg_res hcg_mc hcg_vp ?_
        simp only [↓reduceIte]
        unfold insAfterRKeyGenProg
        dsimp only
        rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
        simp only [pure_bind]
        refine bind_read_some hrf_st hrf_res hrf_mc hrf_vp ?_
        dsimp only
        refine bind_read_some hck_st hck_res hck_mc hck_vp ?_
        simp only [↓reduceIte]
        have hfp_lt : fp < 2 ^ fpBitsWhp n_max := by
          dsimp only [fp, fpOfSalt]
          split_ifs with hs
          · exact fpHash_lt c U n_max θ.2 ⟨fs.bktSalt b, hs⟩ u
          · exact Nat.two_pow_pos _
        obtain ⟨hcm_res, hcm_mc, hcm_vp, hcm_step⟩ :=
          insCommitFreshGenProg_spec hasFpCollision henv hseed hrep hv hb hX_tl hpos_fn
            hq_lt hv_v hfp_lt (rKey := rKey) (s := s)
        exact ⟨by dsimp only [cp, X, rKey, fp, lIdx, hasFpCollision] at hcm_mc ⊢; omega,
          hcm_vp, hcm_res, hcm_step⟩

/-- Body of `fastInsertGenProg` after Feistel split (`d = ((((wp, base), bq), u_val), v_val)`). -/
@[irreducible] private def fastInsertBodyGenProg :
    (((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ → Memory.Prog ℕ
  | ((((wp, base), bq), u_val), v_val) => do
    let z1 ← pure 1
    let fl ← fastFindLocBqGenProg (((wp, base), bq), u_val)
    if fl.1 = z1 then
      fastInsertOverwriteGenProg (((wp, base), (bq.1, fl.2)), v_val)
    else
      fastInsertMissGenProg ((((wp, base), bq), u_val), v_val)

private theorem realizes_fastInsertBodyGen :
    Realizes .exact fastInsertBodyGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × (ℕ × ℕ)) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w ((((wp, base), bq), u_val), v_val) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          u_val < U ∧
          v_val < V ∧
          bq = (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u_val,
                keyQuotient (bWhp n_max) u_val))
      (fun _ _ => 0) := by
  unfold fastInsertBodyGenProg
  have hfl := realizes_fastFindLocBqGen
  have hov := realizes_fastInsertOverwriteGen
  have hms := realizes_fastInsertMissGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨wp, base⟩, ⟨b, q_val⟩⟩, u_val⟩, v_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv, hu, hv_v, hbq⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    rcases Prod.mk.inj hbq with ⟨rfl, rfl⟩
    set u : Fin U := ⟨u_val, hu⟩
    have hb : feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u_val < numBucketsWhp n_max :=
      feistelBucket_lt _ _ _
    have hq_lt : keyQuotient (bWhp n_max) u_val < 2 ^ quotBitsWhp U n_max :=
      keyQuotient_lt_pow_quotBits u
    obtain ⟨hfl_st, hfl_res, _, _⟩ := fastFindLocBqGenProg_spec henv hseed hrep hv u (s := s)
    dsimp only [u] at hfl_st hfl_res
    rw [hfl_st] at *
    first
    | exact henv.fits_const (by decide)
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv⟩
    | (rw [hcp_eq, wp_large_M hth]; exact hb)
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv, hu, hb, hq_lt, hv_v⟩
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
         rw [hfl_res]; dsimp only
         exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv, hb, hspec.1, hv_v⟩)
  )

/-- Fast-mode guarded insertion / overwrite `fastInsertGenProg`
(`d = (((wp, base), u_val), v_val)`), returning `1` when `fastInsert` succeeds (`FastStateStep`)
and `0` without mutating memory when any fast-mode guard fires. -/
@[irreducible] def fastInsertGenProg : ((WhpParams × ℕ) × ℕ) × ℕ → Memory.Prog ℕ
  | (((wp, base), u_val), v_val) => do
    let hrt ← mkHashRtGenProg (wp, base)
    let bq ← feistelSplitRtProg (hrt, u_val)
    fastInsertBodyGenProg ((((wp, base), bq), u_val), v_val)

theorem realizes_fastInsertGen :
    Realizes .exact fastInsertGenProg
      (WordEncoding.encode (α := ((WhpParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w (((wp, base), u_val), v_val) s =>
        ValidFastMemPre w wp base s ∧ u_val < wpU wp.1 ∧ v_val < wpV wp.1)
      (fun _ _ => 0) := by
  unfold fastInsertGenProg
  have hmh := realizes_mkHashRtGen
  have hfs := realizes_feistelSplitRt
  have hib := realizes_fastInsertBodyGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨wp, base⟩, u_val⟩, v_val⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv⟩, hu_wp, hv_wp⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    have hu : u_val < U := by rw [hcp_eq, wp_large_U hth] at hu_wp; exact hu_wp
    have hv_v : v_val < V := by rw [hcp_eq, wp_large_V hth] at hv_wp; exact hv_wp
    obtain ⟨hmh_st, hmh_res, _, _⟩ := mkHashRtGenProg_spec (c := c) (U := U) (V := V)
      (w := w) (n_max := n_max) (base := base) hth s
    obtain ⟨hfs_st, hfs_res, _, _⟩ :=
      feistelSplitRtProg_spec (u_val := u_val) henv hseed (s := s)
    simp only [hmh_st, hmh_res, hfs_st, hfs_res] at *
    first
    | exact ⟨c, U, V, w, n_max, θ, henv, rfl, hseed⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv, hu, hv_v, rfl⟩
  )

theorem fastInsertGenProg_spec {c U V w n_max base : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict)
    (u : Fin U) {v_val : ℕ} (hv_v : v_val < V) :
    let prog := fastInsertGenProg (((mkWhpParams c U V w n_max, base), u.val), v_val)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 30 * cTabWhp c + 35 * hashEvalCostWhp c + 42386 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    match fastInsert c U n_max θ fs u v_val with
    | some fs' =>
      (Memory.spec 0).clientResult s prog = 1 ∧
      FastStateStep base c U V w n_max θ fs' s s'
    | none =>
      (Memory.spec 0).clientResult s prog = 0 ∧ s' = s := by
  have hth := henv.2.2.2.1
  set b := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val
  set q_val := keyQuotient (bWhp n_max) u.val
  have hb : b < numBucketsWhp n_max := feistelBucket_lt _ _ _
  have hq_lt : q_val < 2 ^ quotBitsWhp U n_max := keyQuotient_lt_pow_quotBits u
  obtain ⟨hmh_st, hmh_res, hmh_mc, hmh_vp⟩ :=
    mkHashRtGenProg_spec (c := c) (U := U) (V := V) (w := w) (n_max := n_max) (base := base) hth s
  obtain ⟨hfs_st, hfs_res, hfs_mc, hfs_vp⟩ :=
    feistelSplitRtProg_spec (u_val := u.val) henv hseed (s := s)
  obtain ⟨hfl_st, hfl_res, hfl_mc, hfl_vp⟩ :=
    fastFindLocBqGenProg_spec henv hseed hrep hv u (s := s)
  have hspec := hv.fastFindLoc_spec u
  dsimp only
  rw [← Nat.zero_add (memoryCost _ s)]
  unfold fastInsertGenProg fastInsert
  dsimp only
  cases hfind : fastFindLoc c U n_max θ fs u with
  | some loc =>
    rw [hfind] at hfl_res hspec
    refine bind_read_some hmh_st hmh_res hmh_mc.le hmh_vp ?_
    refine bind_read_some hfs_st hfs_res hfs_mc hfs_vp ?_
    unfold fastInsertBodyGenProg
    dsimp only
    simp only [pure_bind]
    refine bind_read_some hfl_st hfl_res hfl_mc hfl_vp ?_
    simp only [↓reduceIte]
    obtain ⟨hov_res, hov_mc, hov_vp, hov_step⟩ :=
      fastInsertOverwriteGenProg_spec henv hseed hrep hv hb hspec.1 hv_v (v_val := v_val) (s := s)
    exact ⟨by dsimp only [b, q_val] at hov_mc ⊢; omega, hov_vp, hov_res, hov_step⟩
  | none =>
    rw [hfind] at hfl_res
    obtain ⟨hms_mc, hms_vp, hms_match⟩ :=
      fastInsertMissGenProg_spec u henv hseed hrep hv hb hq_lt hv_v (v_val := v_val) (s := s)
    dsimp only [b, q_val] at hms_mc hms_vp hms_match
    refine ⟨?_, ?_, ?_⟩
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hmh_st, hmh_res, hfs_st, hfs_res]
      unfold fastInsertBodyGenProg
      dsimp only
      simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      rw [hfl_st, hfl_res]
      simp only [zero_ne_one, ↓reduceIte]
      omega
    · refine validProg_bind hmh_vp ?_
      rw [hmh_st, hmh_res]
      refine validProg_bind hfs_vp ?_
      rw [hfs_st, hfs_res]
      unfold fastInsertBodyGenProg
      dsimp only
      simp only [pure_bind]
      refine validProg_bind hfl_vp ?_
      rw [hfl_st, hfl_res]
      simpa only [zero_ne_one, ↓reduceIte] using hms_vp
    · have hres_eq :
          (Memory.spec 0).clientResult s
            (mkHashRtGenProg (mkWhpParams c U V w n_max, base) >>= fun hrt =>
              feistelSplitRtProg (hrt, u.val) >>= fun bq =>
                fastInsertBodyGenProg ((((mkWhpParams c U V w n_max, base), bq), u.val), v_val)) =
          (Memory.spec 0).clientResult s
            (fastInsertMissGenProg
              ((((mkWhpParams c U V w n_max, base), (b, q_val)), u.val), v_val)) := by
        rw [clientResult_bind, hmh_st, hmh_res, clientResult_bind, hfs_st, hfs_res]
        unfold fastInsertBodyGenProg
        dsimp only
        simp only [pure_bind]
        rw [clientResult_bind, hfl_st, hfl_res]
        rfl
      have hst_eq :
          (Memory.spec 0).clientState s
            (mkHashRtGenProg (mkWhpParams c U V w n_max, base) >>= fun hrt =>
              feistelSplitRtProg (hrt, u.val) >>= fun bq =>
                fastInsertBodyGenProg ((((mkWhpParams c U V w n_max, base), bq), u.val), v_val)) =
          (Memory.spec 0).clientState s
            (fastInsertMissGenProg
              ((((mkWhpParams c U V w n_max, base), (b, q_val)), u.val), v_val)) := by
        rw [clientState_bind, hmh_st, hmh_res, clientState_bind, hfs_st, hfs_res]
        unfold fastInsertBodyGenProg
        dsimp only
        simp only [pure_bind]
        rw [clientState_bind, hfl_st, hfl_res]
        rfl
      rw [hres_eq, hst_eq]
      exact hms_match

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
