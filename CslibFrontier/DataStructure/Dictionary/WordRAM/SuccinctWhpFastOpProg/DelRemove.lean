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

/-- A conditional single-slot update leaves every other slot unchanged. -/
private theorem ite_update_apply_of_ne {α : Type} {p : Prop} [Decidable p] {f : ℕ → α}
    {i k : ℕ} {x : α} (h : k ≠ i) : (if p then Function.update f i x else f) k = f k := by
  split_ifs
  · exact Function.update_of_ne h _ _
  · rfl

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
    obtain rfl := henv.2.2.1
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
      rwa [ite_update_apply_of_ne hne_lo.symm]
    first
    | exact ⟨c, U, V, w, n_max, fs, henv, rfl, hrep,
        fun h2 => (hb0 loc_del hld h2).2.2, fun h3 => (hb1 loc_del hld h3).2.2⟩
    | exact ⟨c, U, V, w, n_max, fs_b, lm, henv, rfl, hst1.2.2.1, hv.curEp_or, hb,
        (hv.roles_valid b hb).1, hlic_le, hv_l, hfp_lt⟩
    | exact ⟨c, U, V, w, n_max, fs_l, henv, rfl, hst2.2.2.1, hv.curEp_or, hb,
        (hv.roles_valid b hb).2.1, hom_fn2, hfp_lt⟩
  )

private theorem delRemCoreGenProg_fastStep {c U V w n_max base b loc_del : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (u : Fin U)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep : FastMemRep base c U V w n_max fs s.mem)
    (hv : ValidFastState c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max)
    (hld : loc_del < fs.bktCount b) :
    let st_del := fs.locState b loc_del
    let rKey_u := fpReducedKey c U n_max θ.2 u
    let fp_live_u := fpOfSalt c U n_max θ.2 (fs.bktSalt b) u
    let buf1 :=
      if st_del = 2 then
        Function.update fs.buf 0 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 0) rKey_u)
      else if st_del = 3 then
        Function.update fs.buf 1 (bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf 1) rKey_u)
      else fs.buf
    let slices1 :=
      if inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
        Function.update fs.slices (fs.liveSliceIdx b)
          (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (fs.slices (fs.liveSliceIdx b)) fp_live_u)
      else fs.slices
    let slices2 :=
      if fs.overmarsActive b = 1 ∧ loc_del < fs.overmarsCursor b ∧
          inLiveTree fs.rebStage fs.oldEp (fs.rebDoneFlag b) st_del then
        Function.update slices1 (fs.overmarsSliceIdx b)
          (btreeDelete (fpBitsWhp n_max) (valLaneBitsWhp n_max) (tMinWhp n_max)
            (slices1 (fs.overmarsSliceIdx b)) fp_live_u)
      else slices1
    let fs_o : FastState := { fs with buf := buf1, slices := slices2 }
    let prog := delRemCoreGenProg
      ((((mkWhpCoreParams c U V w n_max, base), b), loc_del), (st_del, (rKey_u, fp_live_u)))
    let s' := (Memory.spec 0).clientState s prog
    fp_live_u < 2 ^ fpBitsWhp n_max ∧
    CostBoundedStep w (base + largeSpaceWhp c U V w n_max) s prog s' () (2 * cTabWhp c + 573) ∧
    FastStateStep base c U V w n_max θ fs_o s s' ∧
    (fs_o.curEp = 0 ∨ fs_o.curEp = 1) ∧
    fs_o.rebSliceIdx b < 3 * numBucketsWhp n_max ∧
    (decide (fs_o.rebStage = 2 ∧ fs_o.dirtyIdx < fs_o.dirtyCount ∧
        fs_o.dirtyBuckets fs_o.dirtyIdx = b ∧ fs_o.rebCandSalt < sMaxWhp c n_max ∧
        fs_o.rebCollision = 0) = true →
      fs_o.rebInsCount ≤ 8 * (slabScale n_max) ^ 12 ∧
      ∃ rm, ValidWhpSlice n_max fs_o.rebInsCount (fs_o.slices (fs_o.rebSliceIdx b)) rm) := by
  set cp := mkWhpCoreParams c U V w n_max
  obtain ⟨hb0, hb1, _, _, hr_lt, hne_lo, hne_lr, hne_or, ⟨hlic_le, lm, hv_l⟩, hom_fn, hreb_fn⟩ :=
    validFastState_delete_bounds hv hb
  have hfp_lt : fpOfSalt c U n_max θ.2 (fs.bktSalt b) u < 2 ^ fpBitsWhp n_max := by
    unfold fpOfSalt
    by_cases hs : fs.bktSalt b < sMaxWhp c n_max
    · simp only [hs, ↓reduceDIte]
      exact fpHash_lt c U n_max θ.2 ⟨_, hs⟩ u
    · simp only [hs, ↓reduceDIte]
      exact Nat.two_pow_pos _
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
    (hv.roles_valid b hb).1 hlic_le hv_l hfp_lt hst1.2.1 hst1.2.2.1 (st_del := st_del) (s := s1)
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
    rwa [ite_update_apply_of_ne hne_lo.symm]
  obtain ⟨hmc3, hvp3, hst3⟩ := delRemOmGenProg_fastStep (fs := fs_l) henv hv.curEp_or hb
    (hv.roles_valid b hb).2.1 hom_fn2 hfp_lt hst2.2.1 hst2.2.2.1
    (loc_del := loc_del) (st_del := st_del) (s := s2)
  set s3 := (Memory.spec 0).clientState s2
    (delRemOmGenProg ((((cp, base), b), loc_del), (st_del, fp_live_u)))
  have hcore : CostBoundedStep w (base + largeSpaceWhp c U V w n_max) s
      (delRemCoreGenProg ((((cp, base), b), loc_del), (st_del, (rKey_u, fp_live_u)))) s3 ()
      (2 * cTabWhp c + 573) := by
    unfold delRemCoreGenProg
    dsimp only
    exact .mono (.bind ⟨rfl, rfl, hmc1, hvp1⟩ <|
      .bind ⟨rfl, rfl, hmc2, hvp2⟩ ⟨rfl, rfl, hmc3, hvp3⟩) (by omega)
  dsimp only
  rw [hcore.clientState_eq]
  refine ⟨hfp_lt, hcore, (hst1.trans hst2).trans hst3, hv.curEp_or, hr_lt, fun hrbt => ?_⟩
  obtain ⟨hins_r, rm, hv_r⟩ := hreb_fn hrbt
  refine ⟨hins_r.le, rm, ?_⟩
  change ValidWhpSlice n_max fs.rebInsCount ((ite _ _ _ : _ → _) (fs.rebSliceIdx b)) rm
  rwa [ite_update_apply_of_ne hne_or.symm, ite_update_apply_of_ne hne_lr.symm]

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
    obtain rfl := henv.2.2.1
    subst heq_wp
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr henv.2.2.2.1]
    set u : Fin U := ⟨u_val, hu⟩
    have hld_tl : loc_del < totalLocalCoordsWhp n_max := hld.trans_le (hv.bktCount_le b hb)
    obtain ⟨hri_st, hri_res, _, _⟩ :=
      delRemReadInfoGenProg_spec u henv hseed hrep hb hld_tl (s := s)
    dsimp only [u] at hri_st hri_res
    obtain ⟨hfp_lt, _, hst_core, hce_o, hr_lt_o, hreb_fn_o⟩ :=
      delRemCoreGenProg_fastStep u henv hseed hrep hv hb hld (s := s)
    rw [hcp_eq] at *
    rw [hri_st] at *
    rw [hri_res] at *
    first
    | exact ⟨c, U, V, w, n_max, θ, fs, henv, rfl, hseed, hrep, hb, hld_tl⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, henv, rfl, hseed, hrep, hv, hb, hld, rfl, hfp_lt⟩
    | exact ⟨c, U, V, w, n_max, θ, _, henv, rfl, hst_core.2.1, hst_core.2.2.1,
        hce_o, hb, hr_lt_o, hreb_fn_o⟩
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
  have hwp1 : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
    simp [mkWhpParams, Nat.not_lt.mpr henv.2.2.2.1]
  have hld_tl : loc_del < totalLocalCoordsWhp n_max := hld.trans_le (hv.bktCount_le b hb)
  obtain ⟨hri_st, hri_res, hri_mc, hri_vp⟩ :=
    delRemReadInfoGenProg_spec u henv hseed hrep hb hld_tl (s := s)
  obtain ⟨_, hcore, hst_core, hce_o, hr_lt_o, hreb_fn_o⟩ :=
    delRemCoreGenProg_fastStep u henv hseed hrep hv hb hld (s := s)
  obtain ⟨hmc4, hvp4, hst4⟩ := delRemRebGenProg_fastStep u henv hce_o hb hr_lt_o hreb_fn_o
    hst_core.2.1 hst_core.2.2.1 (loc_del := loc_del) (st_del := fs.locState b loc_del)
  dsimp only
  unfold fastDeleteRemoveGenProg
  dsimp only
  rw [hwp1]
  exact CostBoundedStep.elim
    (.bind ⟨hri_st, hri_res, hri_mc, hri_vp⟩ <| .bind hcore ⟨rfl, rfl, hmc4, hvp4⟩)
    (by omega) (hst_core.trans hst4)

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
