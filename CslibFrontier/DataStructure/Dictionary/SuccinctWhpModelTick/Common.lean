/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep

/-!
# Shared Invariant-Transfer and Live-Count Bounds for WHP Fast State

Shared helper lemmas for `SuccinctWhpModelTick`, providing the public `liveInsCount` upper bound
from `CoreFastInv` + `OvermarsBucketInv` along with private metadata-transition invariant transfer
lemmas (`core_and_om_of_inLiveTree_eq`, `step_of_inLiveTree_eq`) across epoch stages
[BenderFarachColtonKuszmaulKuszmaul2024].

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.liveInsCount_le_eight`: bounds `fs.liveInsCount b` by
  `8 * (slabScale n_max) ^ 12` from `CoreFastInv` and `OvermarsBucketInv`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Finset
open scoped BigOperators

private theorem fpOfSalt_lt {c U n_max : ℕ} (θ₂ : FpSeed c U n_max) (salt : ℕ) (u : Fin U) :
    fpOfSalt c U n_max θ₂ salt u < 2 ^ fpBitsWhp n_max := by
  dsimp only [fpOfSalt]
  split_ifs with hs
  · exact fpHash_lt c U n_max θ₂ ⟨salt, hs⟩ u
  · exact Nat.two_pow_pos _

private theorem curEp_ne_oldEp {fs : FastState} (h : fs.curEp = 0 ∨ fs.curEp = 1) :
    fs.curEp ≠ fs.oldEp := by
  rcases h with hc | hc <;> simp [FastState.oldEp, hc]

private theorem BufMapRel.insert_skip {M tag b₀ : ℕ} {bktCnt : ℕ → ℕ}
    {locSt locSt' rKeyOf rKeyOf' : ℕ → ℕ → ℕ} {m : ℕ → Option (ℕ × ℕ)}
    (hrel : BufMapRel M tag bktCnt locSt rKeyOf m)
    (hst_new : locSt' b₀ (bktCnt b₀) ≠ tag)
    (hst_pres : ∀ b < M, ∀ loc < bktCnt b, locSt' b loc = locSt b loc)
    (hrk_pres : ∀ b < M, ∀ loc < bktCnt b, rKeyOf' b loc = rKeyOf b loc) :
    BufMapRel M tag (Function.update bktCnt b₀ (bktCnt b₀ + 1)) locSt' rKeyOf' m := by
  refine BufMapRel.of_some_iff fun rk b loc => ?_
  rw [hrel.2 rk b loc]
  refine ⟨fun ⟨hb, hloc, hst0, hrk0⟩ => ?_, fun ⟨hb, hloc_upd, hst', hrk'⟩ => ?_⟩
  · refine ⟨hb, ?_, (hst_pres b hb loc hloc).trans hst0, (hrk_pres b hb loc hloc).trans hrk0⟩
    by_cases hbb : b = b₀
    · subst hbb; rw [Function.update_self]; exact Nat.lt_succ_of_lt hloc
    · rwa [Function.update_of_ne hbb]
  · have hlt : loc < bktCnt b := by
      rw [Function.update_apply] at hloc_upd
      split_ifs at hloc_upd with hbb
      · subst hbb; exact lt_of_le_of_ne (Nat.lt_succ_iff.mp hloc_upd) fun h => hst_new (h ▸ hst')
      · exact hloc_upd
    exact ⟨hb, hlt, (hst_pres b hb loc hlt).symm.trans hst',
      (hrk_pres b hb loc hlt).symm.trans hrk'⟩

private theorem inLiveTree_curEp_eq_false {fs : FastState} (hc : fs.curEp = 0 ∨ fs.curEp = 1)
    (doneB : ℕ) :
    inLiveTree fs.rebStage fs.oldEp doneB (2 + fs.curEp) = false := by
  rcases hc with h | h <;> simp [inLiveTree, FastState.oldEp, h]

/-- Bound `fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12` from `CoreFastInv` and
`OvermarsBucketInv`. -/
theorem liveInsCount_le_eight {c U V n_max b : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U} (hc : CoreFastInv c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max) (hom : OvermarsBucketInv c U n_max θ fs b) :
    fs.liveInsCount b ≤ 8 * (slabScale n_max) ^ 12 := by
  have hcnt3 : fs.bktCount b ≤ 3 * (slabScale n_max) ^ 12 :=
    (hc.bktCount_le b hb).trans totalLocalCoordsWhp_le_three_mul
  rcases hom with ⟨_, hlt⟩ | ⟨_, _, hcur, hlin, _, _⟩ <;> omega

/-- Transfer `CoreFastInv` and `OvermarsBucketInv` across any metadata/stage transition that leaves
buckets, backyard pool, roles, salts, `curEp`, `bufCur`, `liveSlice`, and `overmarsSlice` untouched
and preserves `inLiveTree` on all active coordinates. -/
private theorem core_and_om_of_inLiveTree_eq {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} (fs' : FastState) {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs b)
    (hep : fs'.curEp = fs.curEp)
    (hclk : fs'.epochClock < qEpochWhp n_max)
    (hstg_le : fs'.rebStage ≤ 5)
    (hcoll0 : fs'.rebCollision = 0)
    (hq : fs'.quotArr = fs.quotArr) (hv_arr : fs'.valArr = fs.valArr)
    (hbkt : fs'.bktCount = fs.bktCount) (hls : fs'.locState = fs.locState)
    (hbp : fs'.backPtr = fs.backPtr) (htop : fs'.poolFreeTop = fs.poolFreeTop)
    (hstk : fs'.poolFreeStack = fs.poolFreeStack) (hown : fs'.poolOwner = fs.poolOwner)
    (hlr : fs'.liveRole = fs.liveRole) (hor : fs'.overmarsRole = fs.overmarsRole)
    (hbs : fs'.bktSalt = fs.bktSalt) (hlic : fs'.liveInsCount = fs.liveInsCount)
    (hoa : fs'.overmarsActive = fs.overmarsActive) (hoc : fs'.overmarsCursor = fs.overmarsCursor)
    (hoi : fs'.overmarsInsCount = fs.overmarsInsCount)
    (hbuf_cur : fs'.buf fs'.curEp = fs.buf fs.curEp)
    (hsl_live : ∀ b < numBucketsWhp n_max,
      fs'.slices (fs'.liveSliceIdx b) = fs.slices (fs.liveSliceIdx b))
    (hsl_om : ∀ b < numBucketsWhp n_max,
      fs'.slices (fs'.overmarsSliceIdx b) = fs.slices (fs.overmarsSliceIdx b))
    (hinL : ∀ b < numBucketsWhp n_max, ∀ loc < fs.bktCount b,
      inLiveTree fs'.rebStage fs'.oldEp (fs'.rebDoneFlag b) (fs.locState b loc) =
        inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc))
    (hbo' :
      if fs'.rebStage ≤ 3 then
        (fs'.buf fs'.oldEp).itemAlloc ≤ 2 * sMaxWhp c n_max ∧
        (fs'.buf fs'.oldEp).nodeAlloc ≤ 1 + cTabWhp c * (fs'.buf fs'.oldEp).itemAlloc ∧
        ∃ oldMap,
          ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs'.buf fs'.oldEp) oldMap ∧
          BufMapRel (numBucketsWhp n_max) (2 + fs'.oldEp) fs'.bktCount fs'.locState
            (fs'.rKeyAt c U n_max θ) oldMap
      else if fs'.rebStage = 4 then
        (∀ b < numBucketsWhp n_max, ∀ loc < fs'.bktCount b, fs'.locState b loc ≠ 2 + fs'.oldEp) ∧
        ClearableBufTrie (fs'.buf fs'.oldEp) ∧
        (fs'.buf fs'.oldEp).nodeAlloc ≤ 1 + cTabWhp c * (2 * sMaxWhp c n_max)
      else
        (∀ b < numBucketsWhp n_max, ∀ loc < fs'.bktCount b, fs'.locState b loc ≠ 2 + fs'.oldEp) ∧
        ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs'.buf fs'.oldEp) (fun _ => none) ∧
        (fs'.buf fs'.oldEp).nodeAlloc = 1 ∧
        (fs'.buf fs'.oldEp).itemAlloc = 0) :
    CoreFastInv c U V n_max θ fs' dict ∧
    (∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs' b) := by
  have hphys : fs'.physSlot n_max = fs.physSlot n_max := by
    funext b loc; dsimp only [FastState.physSlot]; rw [hbp]
  have hkv : fs'.keyValAt c U n_max θ.1 = fs.keyValAt c U n_max θ.1 :=
    keyValAt_eq_of_fields hq hbp
  have hrk : fs'.rKeyAt c U n_max θ = fs.rKeyAt c U n_max θ :=
    rKeyAt_eq_of_fields hq hbp
  have hfp : ∀ salt b, fs'.fpAt c U n_max θ salt b = fs.fpAt c U n_max θ salt b :=
    fun salt b => fpAt_eq_of_fields hq hbp salt b
  refine ⟨?_, fun b hb => ?_⟩
  · exact
      { hth := hc.hth
        curEp_or := hep ▸ hc.curEp_or
        epochClock_lt := hclk
        rebStage_le := hstg_le
        rebCollision_zero := hcoll0
        qv_global := fun p => by rw [hq, hv_arr]; exact hc.qv_global p
        bktCount_le := by rw [hbkt]; exact hc.bktCount_le
        bktCount_ge_zero := by rw [hbkt]; exact hc.bktCount_ge_zero
        locState_active := by rw [hbkt, hls]; exact hc.locState_active
        locState_inactive := by rw [hbkt, hls]; exact hc.locState_inactive
        active_item := fun b hb loc hloc => by
          rw [hbkt] at hloc
          dsimp only; rw [hkv, hq, hv_arr, hphys]
          exact hc.active_item b hb loc hloc
        quot_inj := fun b hb l₁ hl₁ l₂ hl₂ heq => by
          rw [hbkt] at hl₁ hl₂; rw [hq, hphys] at heq
          exact hc.quot_inj b hb l₁ hl₁ l₂ hl₂ heq
        dict_map := fun u => by
          dsimp only; rw [hbkt, hq, hv_arr, hphys]; exact hc.dict_map u
        poolFreeTop_le := htop ▸ hc.poolFreeTop_le
        backPtr_valid := by rw [hbkt, hbp, hown]; exact hc.backPtr_valid
        freeStack_lt := by rw [htop, hstk]; exact hc.freeStack_lt
        backPtr_inj := by rw [hbkt, hbp]; exact hc.backPtr_inj
        freeStack_inj := by rw [htop, hstk]; exact hc.freeStack_inj
        back_free_disj := by rw [hbkt, htop, hbp, hstk]; exact hc.back_free_disj
        pool_conservation := by rw [htop, hbkt]; exact hc.pool_conservation
        roles_valid := by rw [hlr, hor]; exact hc.roles_valid
        bktSalt_lt := by rw [hbs]; exact hc.bktSalt_lt
        live_fp_inj := fun b hb l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq => by
          rw [hbkt] at hl₁ hl₂
          rw [hls, hinL b hb l₁ hl₁] at hin₁
          rw [hls, hinL b hb l₂ hl₂] at hin₂
          rw [hbs, hfp] at hfeq
          exact hc.live_fp_inj b hb l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq
        live_valid := fun b hb => by
          obtain ⟨lm, hvl, hrl⟩ := hc.live_valid b hb
          refine ⟨lm, ?_, ?_⟩
          · rwa [hlic, hsl_live b hb]
          · rw [hbs, hfp, hbkt, hls]
            exact hrl.congr (fun _ _ => rfl) (fun loc hlt => by rw [hinL b hb loc hlt])
        rKey_buf_inj := by rw [hbkt, hls, hrk]; exact hc.rKey_buf_inj
        bufCur_valid := by
          rw [hbuf_cur, hep, hbkt, hls, hrk]; exact hc.bufCur_valid
        bufOld_valid := hbo' }
  · dsimp only [OvermarsBucketInv]
    rcases hom b hb with ⟨ha0, hlt5⟩ | ⟨ha1, h16, hcur, hlin, hins_om, omM, hvO, hrO⟩
    · rw [hoa, hlic]; exact Or.inl ⟨ha0, hlt5⟩
    · rw [hoa, hoc, hbkt, hlic, hoi, hsl_om b hb, hbs, hfp, hls]
      exact Or.inr ⟨ha1, h16, hcur, hlin, hins_om, omM, hvO,
        hrO.congr (fun _ _ => rfl) (fun loc hlt => by rw [hinL b hb loc (hlt.trans hcur)])⟩

private theorem step_of_inLiveTree_eq {c U V n_max clk₀ : ℕ} {θ : SeedWhp c U n_max}
    {fs fs' : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs b)
    (hep : fs'.curEp = fs.curEp)
    (hclk : fs'.epochClock < qEpochWhp n_max)
    (hstg_le : fs'.rebStage ≤ 5)
    (hcoll0 : fs'.rebCollision = 0)
    (hq : fs'.quotArr = fs.quotArr) (hv_arr : fs'.valArr = fs.valArr)
    (hbkt : fs'.bktCount = fs.bktCount) (hls : fs'.locState = fs.locState)
    (hbp : fs'.backPtr = fs.backPtr) (htop : fs'.poolFreeTop = fs.poolFreeTop)
    (hstk : fs'.poolFreeStack = fs.poolFreeStack) (hown : fs'.poolOwner = fs.poolOwner)
    (hlr : fs'.liveRole = fs.liveRole) (hor : fs'.overmarsRole = fs.overmarsRole)
    (hbs : fs'.bktSalt = fs.bktSalt) (hlic : fs'.liveInsCount = fs.liveInsCount)
    (hoa : fs'.overmarsActive = fs.overmarsActive) (hoc : fs'.overmarsCursor = fs.overmarsCursor)
    (hoi : fs'.overmarsInsCount = fs.overmarsInsCount)
    (hbuf_cur : fs'.buf fs'.curEp = fs.buf fs.curEp)
    (hsl_live : ∀ b < numBucketsWhp n_max,
      fs'.slices (fs'.liveSliceIdx b) = fs.slices (fs.liveSliceIdx b))
    (hsl_om : ∀ b < numBucketsWhp n_max,
      fs'.slices (fs'.overmarsSliceIdx b) = fs.slices (fs.overmarsSliceIdx b))
    (hinL : ∀ b < numBucketsWhp n_max, ∀ loc < fs.bktCount b,
      inLiveTree fs'.rebStage fs'.oldEp (fs'.rebDoneFlag b) (fs.locState b loc) =
        inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) (fs.locState b loc))
    (hbo' :
      if fs'.rebStage ≤ 3 then
        (fs'.buf fs'.oldEp).itemAlloc ≤ 2 * sMaxWhp c n_max ∧
        (fs'.buf fs'.oldEp).nodeAlloc ≤ 1 + cTabWhp c * (fs'.buf fs'.oldEp).itemAlloc ∧
        ∃ oldMap,
          ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs'.buf fs'.oldEp) oldMap ∧
          BufMapRel (numBucketsWhp n_max) (2 + fs'.oldEp) fs'.bktCount fs'.locState
            (fs'.rKeyAt c U n_max θ) oldMap
      else if fs'.rebStage = 4 then
        (∀ b < numBucketsWhp n_max, ∀ loc < fs'.bktCount b, fs'.locState b loc ≠ 2 + fs'.oldEp) ∧
        ClearableBufTrie (fs'.buf fs'.oldEp) ∧
        (fs'.buf fs'.oldEp).nodeAlloc ≤ 1 + cTabWhp c * (2 * sMaxWhp c n_max)
      else
        (∀ b < numBucketsWhp n_max, ∀ loc < fs'.bktCount b, fs'.locState b loc ≠ 2 + fs'.oldEp) ∧
        ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs'.buf fs'.oldEp) (fun _ => none) ∧
        (fs'.buf fs'.oldEp).nodeAlloc = 1 ∧
        (fs'.buf fs'.oldEp).itemAlloc = 0)
    (hstg_valid : ValidEpochStage c U n_max θ fs')
    (hclk_eq : fs'.epochClock = clk₀) :
    CoreFastInv c U V n_max θ fs' dict ∧
    (∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs' b) ∧
    ValidEpochStage c U n_max θ fs' ∧
    fs'.epochClock = clk₀ := by
  obtain ⟨hc', hom'⟩ := core_and_om_of_inLiveTree_eq fs' hc hom hep hclk hstg_le hcoll0 hq hv_arr
    hbkt hls hbp htop hstk hown hlr hor hbs hlic hoa hoc hoi hbuf_cur hsl_live hsl_om hinL hbo'
  exact ⟨hc', hom', hstg_valid, hclk_eq⟩

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
