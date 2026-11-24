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
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg.DelRemCore
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg.DelRemReb
import CslibFrontier.Tactic.Realize

/-!
# Fast Deletion Substep 1 (`fastDeleteRemoveGenProg`)

Assembles Substep 1 (`fastDeleteRemove`) combining epoch-buffer, live-slice, Overmars-slice, and
rebuild-slice deletions.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fastDeleteRemoveGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_fastDeleteRemoveGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fastDeleteRemoveGenProg_fastStep`
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

/-- Core `WhpCoreParams` removal sequence (`buf`, `liveSlice`, `overmarsSlice`) for
`fastDeleteRemoveGenProg`. -/
@[irreducible] private def delRemCoreGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × (ℕ × ℕ)) → Memory.Prog Unit
  | ((((cp, base), b), loc_del), (st_del, (rKey_u, fp_live_u))) => do
    delRemBufGenProg (((cp, base), st_del), rKey_u)
    delRemLiveGenProg (((cp, base), b), (st_del, fp_live_u))
    delRemOmGenProg ((((cp, base), b), loc_del), (st_del, fp_live_u))

private theorem realizes_delRemCoreGen :
    Realizes .exact delRemCoreGenProg
      (WordEncoding.encode (α := (((WhpCoreParams × ℕ) × ℕ) × ℕ) × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := Unit))
      (fun w ((((cp, base), b), loc_del), (st_del, (_, fp_live_u))) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          cp = mkWhpCoreParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          b < numBucketsWhp n_max ∧
          loc_del < fs.bktCount b ∧
          st_del = fs.locState b loc_del ∧
          fp_live_u < 2 ^ fpBitsWhp n_max)
      (fun _ _ => 0) := by
  unfold delRemCoreGenProg
  have db1 := realizes_delRemBufGen
  have db2 := realizes_delRemLiveGen
  have db3 := realizes_delRemOmGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, loc_del⟩, ⟨st_del, ⟨rKey_u, fp_live_u⟩⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv, hb, hld,
      rfl, hfp_lt⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    obtain ⟨hb0, hb1, _, _, _, hne_lo, _, _, ⟨hlic_le, lm, hv_l⟩, hom_fn, _⟩ :=
      validFastState_delete_bounds hv hb
    set st_del := fs.locState b loc_del
    obtain ⟨_, _, hst1⟩ := delRemBufGenProg_fastStep henv
      (fun h2 => (hb0 loc_del hld h2).2.2) (fun h3 => (hb1 loc_del hld h3).2.2)
      hseed hrep (st_del := st_del) (rKey_u := rKey_u) (s := s)
    set s1 := (Memory.spec 0).clientState s
      (delRemBufGenProg (((mkWhpCoreParams c U V w n_max, base), st_del), rKey_u))
    set buf1 :=
      if st_del = 2 then
        Function.update fs.buf 0 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 0) rKey_u)
      else if st_del = 3 then
        Function.update fs.buf 1 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 1) rKey_u)
      else fs.buf
    set fs_b : FastState := { fs with buf := buf1 }
    obtain ⟨_, _, hst2⟩ := delRemLiveGenProg_fastStep (fs := fs_b) henv hv.curEp_or hb
      (hv.roles_valid b hb).1 hlic_le hv_l hfp_lt hst1.2.1 hst1.2.2.1 (st_del := st_del) (s := s1)
    set slices1 :=
      if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
        Function.update fs.slices (fs.liveSliceIdx b)
          (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices (fs.liveSliceIdx b)) fp_live_u)
      else fs.slices
    set fs_l : FastState := { fs_b with slices := slices1 }
    have hom_fn2 : fs_l.overmarsActive b = 1 →
        fs_l.overmarsInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
        ∃ om, ValidWhpSlice n_max (fs_l.overmarsInsCount b)
          (fs_l.slices (fs_l.overmarsSliceIdx b)) om := by
      intro ha1
      obtain ⟨hins_o, om, hv_o⟩ := hom_fn ha1
      refine ⟨hins_o.le, om, ?_⟩
      change ValidWhpSlice n_max (fs.overmarsInsCount b) (slices1 (fs.overmarsSliceIdx b)) om
      dsimp only [slices1]
      by_cases hin : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del = true
      · rw [ite_eq_left hin, Function.update_of_ne hne_lo.symm]; exact hv_o
      · rw [ite_eq_right hin]; exact hv_o
    first
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep,
        fun h2 => (hb0 loc_del hld h2).2.2, fun h3 => (hb1 loc_del hld h3).2.2⟩
    | exact ⟨c, U, V, w, n_max, fs_b, lm, henv, rfl, hst1.2.2.1, hv.curEp_or, hb,
        (hv.roles_valid b hb).1, hlic_le, hv_l, hfp_lt⟩
    | exact ⟨c, U, V, w, n_max, fs_l, henv, rfl, hst2.2.2.1, hv.curEp_or, hb,
        (hv.roles_valid b hb).2.1, hom_fn2, hfp_lt⟩
  )

/-- Complete Substep 1 (`fastDeleteRemove`): remove `(u, loc_del)` from epoch buffers and slices
(`d = ((((wp, base), b), loc_del), u_val)`). -/
@[irreducible] def fastDeleteRemoveGenProg :
    (((WhpParams × ℕ) × ℕ) × ℕ) × ℕ → Memory.Prog Unit
  | ((((wp, base), b), loc_del), u_val) => do
    let info ← delRemReadInfoGenProg ((((wp, base), b), loc_del), u_val)
    delRemCoreGenProg ((((wp.1, base), b), loc_del), info)
    delRemRebGenProg ((((wp, base), b), loc_del), (info.1, u_val))

theorem realizes_fastDeleteRemoveGen :
    Realizes .exact fastDeleteRemoveGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := Unit))
      (fun w ((((wp, base), b), loc_del), u_val) s =>
        ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U),
          WhpLargeEnv c U V w₀ n_max w base ∧
          wp = mkWhpParams c U V w₀ n_max ∧
          SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
          FastMemRep base c U V w₀ n_max fs s.mem ∧
          ValidFastState c U V n_max θ fs dict ∧
          b < numBucketsWhp n_max ∧
          loc_del < fs.bktCount b ∧
          u_val < U)
      (fun _ _ => 0) := by
  unfold fastDeleteRemoveGenProg
  have hri := realizes_delRemReadInfoGen
  have hdc := realizes_delRemCoreGen
  have db4 := realizes_delRemRebGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨wp, base⟩, b⟩, loc_del⟩, u_val⟩
    dsimp only at *
    try simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, henv, heq_wp, hseed, hrep, hv, hb, hld, hu⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    set u : Fin U := ⟨u_val, hu⟩
    have hld_tl : loc_del < totalLocalCoordsWhp n_max := hld.trans_le (hv.bktCount_le b hb)
    obtain ⟨hb0, hb1, _, _, hr_lt, hne_lo, hne_lr, hne_or,
      ⟨hlic_le, lm, hv_l⟩, hom_fn, hreb_fn⟩ := validFastState_delete_bounds hv hb
    obtain ⟨hri_st, hri_res, _, _⟩ :=
      delRemReadInfoGenProg_spec u henv hseed hrep hb hld_tl (s := s)
    dsimp only [u] at hri_st hri_res
    have hfp_lt : fpOfSalt c U n_max θ.2 (fs.bktSalt b) u < 2 ^ fpBitsWhp n_max := by
      unfold fpOfSalt
      by_cases hs : fs.bktSalt b < sMaxWhp c n_max
      · simp only [hs, ↓reduceDIte]; exact fpHash_lt c U n_max θ.2 ⟨_, hs⟩ u
      · simp only [hs, ↓reduceDIte]; exact Nat.two_pow_pos _
    set st_del := fs.locState b loc_del
    set rKey_u := fpReducedKey c U n_max θ.2 u
    set fp_live_u := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
    obtain ⟨_, _, hst1⟩ := delRemBufGenProg_fastStep henv
      (fun h2 => (hb0 loc_del hld h2).2.2) (fun h3 => (hb1 loc_del hld h3).2.2)
      hseed hrep (st_del := st_del) (rKey_u := rKey_u) (s := s)
    set s1 := (Memory.spec 0).clientState s
      (delRemBufGenProg (((mkWhpCoreParams c U V w n_max, base), st_del), rKey_u))
    set buf1 :=
      if st_del = 2 then
        Function.update fs.buf 0 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 0) rKey_u)
      else if st_del = 3 then
        Function.update fs.buf 1 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 1) rKey_u)
      else fs.buf
    set fs_b : FastState := { fs with buf := buf1 }
    obtain ⟨_, _, hst2⟩ := delRemLiveGenProg_fastStep (fs := fs_b) henv hv.curEp_or hb
      (hv.roles_valid b hb).1 hlic_le hv_l hfp_lt hst1.2.1 hst1.2.2.1 (st_del := st_del) (s := s1)
    set s2 := (Memory.spec 0).clientState s1
      (delRemLiveGenProg (((mkWhpCoreParams c U V w n_max, base), b), (st_del, fp_live_u)))
    set slices1 :=
      if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
        Function.update fs.slices (fs.liveSliceIdx b)
          (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices (fs.liveSliceIdx b)) fp_live_u)
      else fs.slices
    set fs_l : FastState := { fs_b with slices := slices1 }
    have hom_fn2 : fs_l.overmarsActive b = 1 →
        fs_l.overmarsInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
        ∃ om, ValidWhpSlice n_max (fs_l.overmarsInsCount b)
          (fs_l.slices (fs_l.overmarsSliceIdx b)) om := by
      intro ha1
      obtain ⟨hins_o, om, hv_o⟩ := hom_fn ha1
      refine ⟨hins_o.le, om, ?_⟩
      change ValidWhpSlice n_max (fs.overmarsInsCount b) (slices1 (fs.overmarsSliceIdx b)) om
      dsimp only [slices1]
      by_cases hin : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del = true
      · rw [ite_eq_left hin, Function.update_of_ne hne_lo.symm]; exact hv_o
      · rw [ite_eq_right hin]; exact hv_o
    obtain ⟨_, _, hst3⟩ := delRemOmGenProg_fastStep (fs := fs_l) henv hv.curEp_or hb
      (hv.roles_valid b hb).2.1 hom_fn2 hfp_lt hst2.2.1 hst2.2.2.1
      (loc_del := loc_del) (st_del := st_del) (s := s2)
    set slices2 :=
      if fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
          inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
        Function.update slices1 (fs.overmarsSliceIdx b)
          (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (slices1 (fs.overmarsSliceIdx b)) fp_live_u)
      else slices1
    set fs_o : FastState := { fs_l with slices := slices2 }
    have hcore_st : (Memory.spec 0).clientState s
        (delRemCoreGenProg ((((mkWhpCoreParams c U V w n_max, base), b), loc_del),
          (st_del, (rKey_u, fp_live_u)))) =
        (Memory.spec 0).clientState s2
          (delRemOmGenProg ((((mkWhpCoreParams c U V w n_max, base), b), loc_del),
            (st_del, fp_live_u))) := by
      unfold delRemCoreGenProg; dsimp only
      rw [clientState_bind, clientState_bind]
    rw [hcp_eq] at *
    rw [hri_st] at *
    rw [hri_res] at *
    rw [hcore_st] at *
    dsimp only at *
    first
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hb, hld_tl⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv, hb, hld, rfl, hfp_lt⟩
    | (refine ⟨c, U, V, w, n_max, θ, fs_o, henv, rfl, hst3.2.1, hst3.2.2.1, hv.curEp_or, hb, hr_lt,
         fun hrbt => ?_⟩
       obtain ⟨hins_r, rm, hv_r⟩ := hreb_fn hrbt
       refine ⟨hins_r.le, rm, ?_⟩
       have hsl2 : slices2 (fs.rebSliceIdx b) = slices1 (fs.rebSliceIdx b) := by
         dsimp only [slices2]
         by_cases ho : fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
             inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del = true
         · rw [ite_eq_left ho]; exact Function.update_of_ne hne_or.symm _ _
         · rw [ite_eq_right ho]
       have hsl1 : slices1 (fs.rebSliceIdx b) = fs.slices (fs.rebSliceIdx b) := by
         dsimp only [slices1]
         by_cases hl : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del = true
         · rw [ite_eq_left hl]; exact Function.update_of_ne hne_lr.symm _ _
         · rw [ite_eq_right hl]
       change ValidWhpSlice n_max fs.rebInsCount (slices2 (fs.rebSliceIdx b)) rm
       rwa [hsl2, hsl1])
  )

theorem fastDeleteRemoveGenProg_fastStep {c U V w n_max base b loc_del : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (u : Fin U)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max)
    (hld : loc_del < fs.bktCount b) :
    let prog := fastDeleteRemoveGenProg
      ((((mkWhpParams c U V w n_max, base), b), loc_del), u.val)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 2 * cTabWhp c + 2 * hashEvalCostWhp c + 870 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ (fastDeleteRemove c U n_max θ fs u b loc_del) s s' := by
  have hth := henv.2.2.2.1
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr hth]
  set cp := mkWhpCoreParams c U V w n_max
  have hld_tl : loc_del < totalLocalCoordsWhp n_max := hld.trans_le (hv.bktCount_le b hb)
  obtain ⟨hb0, hb1, _, _, hr_lt, hne_lo, hne_lr, hne_or,
    ⟨hlic_le, lm, hv_l⟩, hom_fn, hreb_fn⟩ := validFastState_delete_bounds hv hb
  obtain ⟨hri_st, hri_res, hri_mc, hri_vp⟩ :=
    delRemReadInfoGenProg_spec u henv hseed hrep hb hld_tl (s := s)
  have hfp_lt : fpOfSalt c U n_max θ.2 (fs.bktSalt b) u < 2 ^ fpBitsWhp n_max := by
    unfold fpOfSalt
    by_cases hs : fs.bktSalt b < sMaxWhp c n_max
    · simp only [hs, ↓reduceDIte]; exact fpHash_lt c U n_max θ.2 ⟨_, hs⟩ u
    · simp only [hs, ↓reduceDIte]; exact Nat.two_pow_pos _
  set st_del := fs.locState b loc_del
  set rKey_u := fpReducedKey c U n_max θ.2 u
  set fp_live_u := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
  obtain ⟨hmc1, hvp1, hst1⟩ := delRemBufGenProg_fastStep henv
    (fun h2 => (hb0 loc_del hld h2).2.2) (fun h3 => (hb1 loc_del hld h3).2.2)
    hseed hrep (st_del := st_del) (rKey_u := rKey_u) (s := s)
  set s1 := (Memory.spec 0).clientState s (delRemBufGenProg (((cp, base), st_del), rKey_u))
  set buf1 :=
    if st_del = 2 then
      Function.update fs.buf 0 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 0) rKey_u)
    else if st_del = 3 then
      Function.update fs.buf 1 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 1) rKey_u)
    else fs.buf
  set fs_b : FastState := { fs with buf := buf1 }
  obtain ⟨hmc2, hvp2, hst2⟩ := delRemLiveGenProg_fastStep (fs := fs_b) henv hv.curEp_or hb
    (hv.roles_valid b hb).1 hlic_le hv_l hfp_lt hst1.2.1 hst1.2.2.1
    (st_del := st_del) (s := s1)
  set s2 := (Memory.spec 0).clientState s1
    (delRemLiveGenProg (((cp, base), b), (st_del, fp_live_u)))
  set slices1 :=
    if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
      Function.update fs.slices (fs.liveSliceIdx b)
        (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (fs.slices (fs.liveSliceIdx b)) fp_live_u)
    else fs.slices
  set fs_l : FastState := { fs_b with slices := slices1 }
  have hom_fn2 : fs_l.overmarsActive b = 1 →
      fs_l.overmarsInsCount b ≤ 8 * (slabScale n_max) ^ 12 ∧
      ∃ om, ValidWhpSlice n_max (fs_l.overmarsInsCount b)
        (fs_l.slices (fs_l.overmarsSliceIdx b)) om := by
    intro ha1
    obtain ⟨hins_o, om, hv_o⟩ := hom_fn ha1
    refine ⟨hins_o.le, om, ?_⟩
    change ValidWhpSlice n_max (fs.overmarsInsCount b) (slices1 (fs.overmarsSliceIdx b)) om
    dsimp only [slices1]
    by_cases hin : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del = true
    · rw [ite_eq_left hin, Function.update_of_ne hne_lo.symm]; exact hv_o
    · rw [ite_eq_right hin]; exact hv_o
  obtain ⟨hmc3, hvp3, hst3⟩ := delRemOmGenProg_fastStep (fs := fs_l) henv hv.curEp_or hb
    (hv.roles_valid b hb).2.1 hom_fn2 hfp_lt hst2.2.1 hst2.2.2.1
    (loc_del := loc_del) (st_del := st_del) (s := s2)
  set s3 := (Memory.spec 0).clientState s2
    (delRemOmGenProg ((((cp, base), b), loc_del), (st_del, fp_live_u)))
  set slices2 :=
    if fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
        inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
      Function.update slices1 (fs.overmarsSliceIdx b)
        (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
          (slices1 (fs.overmarsSliceIdx b)) fp_live_u)
    else slices1
  set fs_o : FastState := { fs_l with slices := slices2 }
  have hreb_fn3 : decide (fs_o.rebStage = 2 ∧ fs_o.dirtyIdx < fs_o.dirtyCount ∧
      fs_o.dirtyBuckets fs_o.dirtyIdx = b ∧ fs_o.rebCandSalt < sMaxWhp c n_max ∧
      fs_o.rebCollision = 0) = true →
      fs_o.rebInsCount ≤ 8 * (slabScale n_max) ^ 12 ∧
      ∃ rm, ValidWhpSlice n_max fs_o.rebInsCount (fs_o.slices (fs_o.rebSliceIdx b)) rm := by
    intro hrbt
    obtain ⟨hins_r, rm, hv_r⟩ := hreb_fn hrbt
    refine ⟨hins_r.le, rm, ?_⟩
    have hsl2 : slices2 (fs.rebSliceIdx b) = slices1 (fs.rebSliceIdx b) := by
      dsimp only [slices2]
      by_cases ho : fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
          inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del = true
      · rw [ite_eq_left ho]; exact Function.update_of_ne hne_or.symm _ _
      · rw [ite_eq_right ho]
    have hsl1 : slices1 (fs.rebSliceIdx b) = fs.slices (fs.rebSliceIdx b) := by
      dsimp only [slices1]
      by_cases hl : inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del = true
      · rw [ite_eq_left hl]; exact Function.update_of_ne hne_lr.symm _ _
      · rw [ite_eq_right hl]
    change ValidWhpSlice n_max fs.rebInsCount (slices2 (fs.rebSliceIdx b)) rm
    rwa [hsl2, hsl1]
  obtain ⟨hmc4, hvp4, hst4⟩ := delRemRebGenProg_fastStep (fs := fs_o) u henv hv.curEp_or hb
    hr_lt hreb_fn3 hst3.2.1 hst3.2.2.1 (loc_del := loc_del) (st_del := st_del) (s := s3)
  have hcore_st : (Memory.spec 0).clientState s
      (delRemCoreGenProg ((((cp, base), b), loc_del), (st_del, (rKey_u, fp_live_u)))) = s3 := by
    unfold delRemCoreGenProg; dsimp only
    rw [clientState_bind, clientState_bind]
  dsimp only
  unfold fastDeleteRemoveGenProg
  dsimp only
  rw [show (mkWhpParams c U V w n_max).1 = cp from hwp1]
  have hs'_eq : (Memory.spec 0).clientState s
      (delRemReadInfoGenProg ((((mkWhpParams c U V w n_max, base), b), loc_del), u.val) >>=
        fun info =>
        delRemCoreGenProg ((((cp, base), b), loc_del), info) >>= fun _ =>
        delRemRebGenProg ((((mkWhpParams c U V w n_max, base), b), loc_del), (info.1, u.val))) =
      (Memory.spec 0).clientState s3
        (delRemRebGenProg
          ((((mkWhpParams c U V w n_max, base), b), loc_del), (st_del, u.val))) := by
    rw [clientState_bind, hri_st, hri_res]; dsimp only
    rw [clientState_bind, hcore_st]
  rw [hs'_eq]
  refine ⟨?_, ?_, ((hst1.trans hst2).trans hst3).trans hst4⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hri_st, hri_res]; dsimp only
    rw [hcore_st]
    unfold delRemCoreGenProg; dsimp only
    simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    have hri_mc' : memoryCost (delRemReadInfoGenProg
        ((((mkWhpParams c U V w n_max, base), b), loc_del), u.val)) s ≤
        hashEvalCostWhp c + 5 := hri_mc
    dsimp only [s1, s2, s3, cp, st_del, rKey_u, fp_live_u] at hmc1 hmc2 hmc3 hmc4 ⊢
    omega
  · refine validProg_bind hri_vp ?_; rw [hri_st, hri_res]; dsimp only
    have hcore_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s
        (delRemCoreGenProg ((((cp, base), b), loc_del), (st_del, (rKey_u, fp_live_u)))) := by
      unfold delRemCoreGenProg; dsimp only
      exact validProg_bind hvp1 (validProg_bind hvp2 hvp3)
    refine validProg_bind hcore_vp ?_; rw [hcore_st]
    exact hvp4

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
