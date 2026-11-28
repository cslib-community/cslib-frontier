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
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg.DelMoveReadCopy
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg.DelMoveLiveOm
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpFastOpProg.DelMoveReb
import CslibFrontier.Tactic.Realize

/-!
# Fast Deletion Substep 2 (`fastDeleteMoveLastGenProg`)

Assembles Substep 2 (`fastDeleteMoveLast`) swapping the last coordinate `loc_last` into the freed
slot `loc_del` across epoch buffers, slices, and slot arrays.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fastDeleteMoveLastGenProg`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.FastDelMoveLastPre`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_fastDeleteMoveLastGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.fastDeleteMoveLastGenProg_fastStep`
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

/-- `WhpCoreParams`-only write phase of `fastDeleteMoveLastGenProg` once `info` has been read. -/
@[irreducible] private def delMoveApplyCoreGenProg :
    (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × (ℕ × ℕ)))) → Memory.Prog Unit
  | ((((cp, base), b), (loc_del, loc_last)),
     (rebAct, (st_last, (rKey_last, (fp_live_last, fp_cand_last))))) => do
    delMoveBufGenProg ((((cp, base), b), loc_del), (st_last, rKey_last))
    delMoveLiveOmGenProg ((((cp, base), b), (loc_del, loc_last)), (st_last, fp_live_last))
    delMoveRebGenProg ((((cp, base), b), (loc_del, loc_last)), ((rebAct, st_last), fp_cand_last))
    delCopySlotGenProg ((((cp, base), b), (loc_del, loc_last)), st_last)

/-- Complete Substep 2 (`fastDeleteMoveLast`, when `loc_del < loc_last`): relocate `loc_last` into
`loc_del` (`d = ((((wp, base), b), (loc_del, loc_last)), rebAct)`). -/
@[irreducible] def fastDeleteMoveLastGenProg :
    (((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ → Memory.Prog Unit
  | ((((wp, base), b), (loc_del, loc_last)), rebAct) => do
    let info ← delMoveReadInfoGenProg (((wp, base), b), loc_last)
    delMoveApplyCoreGenProg ((((wp.1, base), b), (loc_del, loc_last)), (rebAct, info))

/-- Precondition for `fastDeleteMoveLastGenProg` on `fs1 = fastDeleteRemove c U n_max θ fs u b
loc_del` under `ValidFastState ... fs dict`. -/
@[expose] def FastDelMoveLastPre (w : ℕ) :
    (((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ → Memory.State → Prop
  | ((((wp, base), b), (loc_del, loc_last)), rebAct), s =>
    ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U) (u : Fin U),
      WhpLargeEnv c U V w₀ n_max w base ∧
      wp = mkWhpParams c U V w₀ n_max ∧
      ValidFastState c U V n_max θ fs dict ∧
      b < numBucketsWhp n_max ∧
      fs.bktCount b = loc_last + 1 ∧
      loc_del < loc_last ∧
      rebAct = (if decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
          fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
          fs.rebCollision = 0) then 1 else 0) ∧
      SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
      FastMemRep base c U V w₀ n_max (fastDeleteRemove c U n_max θ fs u b loc_del) s.mem

/-- Reading index `j ≠ i` of a conditionally updated array ignores the update at `i`. -/
private theorem ite_update_apply_of_ne {α β : Type*} {P : Prop} {dP : Decidable P}
    {dα : DecidableEq α} {f : α → β} {i j : α} {v : β} (h : j ≠ i) :
    (if P then Function.update f i v else f) j = f j := by
  split_ifs
  exacts [Function.update_of_ne h v f, rfl]

/-- Reading the updated index of a conditionally updated array. -/
private theorem ite_update_apply_self {α β : Type*} {P : Prop} {dP : Decidable P}
    {dα : DecidableEq α} {f : α → β} {i : α} {v : β} :
    (if P then Function.update f i v else f) i = if P then v else f i := by
  split_ifs
  exacts [Function.update_self i v f, rfl]

private theorem fs1_moveLast_invs {c U V n_max b loc_del loc_last : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} (u : Fin U)
    (hv : ValidFastState c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max)
    (hcnt : fs.bktCount b = loc_last + 1)
    (_hlt : loc_del < loc_last) :
    let fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
    let st_last := fs1.locState b loc_last
    let rebActiveB := decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
      fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
      fs.rebCollision = 0)
    loc_last < totalLocalCoordsWhp n_max ∧
    (∀ k < loc_last + 1 - capFrontWhp n_max, fs1.backPtr b k < poolSizeWhp n_max) ∧
    (∀ i < n_max, fs1.quotArr i < 2 ^ quotBitsWhp U n_max) ∧
    fs1.valArr (fs1.physSlot n_max b loc_last) < 2 ^ valBits V ∧
    st_last < 4 ∧
    (st_last = 2 →
      (fs1.buf 0).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
      (fs1.buf 0).itemAlloc < qEpochWhp n_max ∧
      ∃ m0, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs1.buf 0) m0) ∧
    (st_last = 3 →
      (fs1.buf 1).nodeAlloc + cTabWhp c ≤ maxTrieNodesWhp c n_max ∧
      (fs1.buf 1).itemAlloc < qEpochWhp n_max ∧
      ∃ m1, ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs1.buf 1) m1) ∧
    (∃ lm1, ValidWhpSlice n_max (fs1.liveInsCount b) (fs1.slices (fs1.liveSliceIdx b)) lm1) ∧
    (fs1.overmarsActive b = 1 →
      fs1.overmarsInsCount b < 8 * (slabScale n_max) ^ 12 ∧
      ∃ om1, ValidWhpSlice n_max (fs1.overmarsInsCount b)
        (fs1.slices (fs1.overmarsSliceIdx b)) om1) ∧
    (rebActiveB = true →
      fs1.rebCandSalt < sMaxWhp c n_max ∧
      fs1.rebInsCount < 8 * (slabScale n_max) ^ 12 ∧
      ∃ rm1, ValidWhpSlice n_max fs1.rebInsCount (fs1.slices (fs1.rebSliceIdx b)) rm1) := by
  intro fs1 st_last rebActiveB
  have hll_b : loc_last < fs.bktCount b := by omega
  have hll_tl : loc_last < totalLocalCoordsWhp n_max := hll_b.trans_le (hv.bktCount_le b hb)
  obtain ⟨hb0, hb1, _, _, _, hne_lo, hne_lr, hne_or,
    ⟨hlic_le, lm, hv_l⟩, hom_fn, hreb_fn⟩ := validFastState_delete_bounds hv hb
  have hv_last : fs.valArr (fs.physSlot n_max b loc_last) < 2 ^ valBits V :=
    val_lt_two_pow_valBits (hv.active_item b hb loc_last hll_b).2.2.2
  have hst_lt : st_last < 4 := by
    have := (hv.locState_active b hb loc_last hll_b).2
    dsimp [st_last, fs1, fastDeleteRemove]; omega
  have hrk_u_lt : fpReducedKey c U n_max θ.2 u < 2 ^ (cTabWhp c * bCharWhp n_max) :=
    fpReducedKey_lt c U n_max θ.2 u
  have hfp_lt (salt : ℕ) : fpOfSalt c U n_max θ.2 salt u < 2 ^ fpBitsWhp n_max := by
    unfold fpOfSalt
    split_ifs with hs
    exacts [fpHash_lt c U n_max θ.2 ⟨_, hs⟩ u, Nat.two_pow_pos _]
  refine ⟨hll_tl,
    fun k hk => (hv.backPtr_valid b hb k (by omega)).1,
    fun i _ => (hv.qv_global i).1,
    hv_last, hst_lt,
    fun h2 => ?_, fun h3 => ?_, ?_, fun ha1 => ?_, fun hrbt => ?_⟩
  · obtain ⟨hna0, hia0, m0, hv0⟩ := hb0 loc_last hll_b h2
    dsimp only [fs1, fastDeleteRemove]
    split_ifs
    · rw [Function.update_self]
      obtain ⟨hv0', hna_e, hia_e, _, _⟩ := hv0.delete_spec hrk_u_lt
      exact ⟨hna_e ▸ hna0, hia_e ▸ hia0, _, hv0'⟩
    · exact Function.update_of_ne Nat.zero_ne_one _ _ ▸ ⟨hna0, hia0, m0, hv0⟩
    · exact ⟨hna0, hia0, m0, hv0⟩
  · obtain ⟨hna1, hia1, m1, hv1⟩ := hb1 loc_last hll_b h3
    dsimp only [fs1, fastDeleteRemove]
    split_ifs
    · exact Function.update_of_ne Nat.one_ne_zero _ _ ▸ ⟨hna1, hia1, m1, hv1⟩
    · rw [Function.update_self]
      obtain ⟨hv1', hna_e, hia_e, _, _⟩ := hv1.delete_spec hrk_u_lt
      exact ⟨hna_e ▸ hna1, hia_e ▸ hia1, _, hv1'⟩
    · exact ⟨hna1, hia1, m1, hv1⟩
  · -- `liveSlice` in `fs1`
    change ∃ lm1, ValidWhpSlice n_max (fs.liveInsCount b) (fs1.slices (fs.liveSliceIdx b)) lm1
    dsimp only [fs1, fastDeleteRemove]
    rw [ite_update_apply_of_ne hne_lr, ite_update_apply_of_ne hne_lo, ite_update_apply_self]
    split_ifs
    exacts [⟨_, hv_l.delete_spec hv.hth hlic_le (hfp_lt _)⟩, ⟨lm, hv_l⟩]
  · -- `overmarsSlice` in `fs1`
    obtain ⟨hins_om, om, hv_om⟩ := hom_fn ha1
    refine ⟨hins_om, ?_⟩
    change ∃ om1, ValidWhpSlice n_max (fs.overmarsInsCount b)
      (fs1.slices (fs.overmarsSliceIdx b)) om1
    dsimp only [fs1, fastDeleteRemove]
    rw [ite_update_apply_of_ne hne_or, ite_update_apply_self, ite_update_apply_of_ne hne_lo.symm]
    split_ifs
    exacts [⟨_, hv_om.delete_spec hv.hth hins_om.le (hfp_lt _)⟩, ⟨om, hv_om⟩]
  · -- `rebSlice` in `fs1`
    obtain ⟨hins_r, rm, hv_r⟩ := hreb_fn hrbt
    refine ⟨(of_decide_eq_true hrbt).2.2.2.1, hins_r, ?_⟩
    change ∃ rm1, ValidWhpSlice n_max fs.rebInsCount (fs1.slices (fs.rebSliceIdx b)) rm1
    dsimp only [fs1, fastDeleteRemove]
    rw [ite_update_apply_self, ite_update_apply_of_ne hne_or.symm,
      ite_update_apply_of_ne hne_lr.symm]
    split_ifs
    exacts [⟨_, hv_r.delete_spec hv.hth hins_r.le (hfp_lt _)⟩, ⟨rm, hv_r⟩]

private theorem reb_valid_after_moveSlices {c n_max b loc_del loc_last fp : ℕ}
    {fs1 : FastState} (buf' : ℕ → BufTrie) {P : Prop}
    (hne_lr : fs1.liveSliceIdx b ≠ fs1.rebSliceIdx b)
    (hne_or : fs1.overmarsSliceIdx b ≠ fs1.rebSliceIdx b)
    (hreb1_fn : P →
      fs1.rebCandSalt < sMaxWhp c n_max ∧
      fs1.rebInsCount < 8 * (slabScale n_max) ^ 12 ∧
      ∃ rm1, ValidWhpSlice n_max fs1.rebInsCount (fs1.slices (fs1.rebSliceIdx b)) rm1) :
    let fs1b : FastState := { fs1 with buf := buf' }
    let omPair := fastDeleteMoveSlices n_max b loc_del loc_last fp fs1b
    let fs1lo : FastState := { fs1b with slices := omPair.1, overmarsInsCount := omPair.2 }
    P →
      fs1lo.rebCandSalt < sMaxWhp c n_max ∧
      fs1lo.rebInsCount < 8 * (slabScale n_max) ^ 12 ∧
      ∃ rm1, ValidWhpSlice n_max fs1lo.rebInsCount
        (fs1lo.slices (fs1lo.rebSliceIdx b)) rm1 := by
  intro fs1b omPair fs1lo hrbt
  obtain ⟨hcs, hins_r, rm1, hv_r1⟩ := hreb1_fn hrbt
  refine ⟨hcs, hins_r, rm1, ?_⟩
  have hne_lr1 : fs1b.liveSliceIdx b ≠ fs1.rebSliceIdx b := hne_lr
  have hne_or1 : fs1b.overmarsSliceIdx b ≠ fs1.rebSliceIdx b := hne_or
  have hsl_r_eq : omPair.1 (fs1.rebSliceIdx b) = fs1.slices (fs1.rebSliceIdx b) := by
    dsimp only [omPair, fastDeleteMoveSlices]
    split_ifs <;>
      simp only [Function.update_of_ne hne_or1.symm, Function.update_of_ne hne_lr1.symm] <;>
      rfl
  dsimp only [fs1lo, fs1b, FastState.rebSliceIdx, FastState.rebRole] at hv_r1 hsl_r_eq ⊢
  rwa [hsl_r_eq]

/-- Precondition for `delMoveApplyCoreGenProg`. -/
private def DelMoveApplyCorePre (w : ℕ) :
    (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × (ℕ × ℕ)))) → Memory.State → Prop
  | ((((cp, base), b), (loc_del, loc_last)), (rebAct, info)), s =>
    ∃ (c U V w₀ n_max : ℕ) (θ : SeedWhp c U n_max) (fs : FastState) (dict : State U) (u : Fin U),
      let fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
      WhpLargeEnv c U V w₀ n_max w base ∧
      cp = mkWhpCoreParams c U V w₀ n_max ∧
      ValidFastState c U V n_max θ fs dict ∧
      b < numBucketsWhp n_max ∧
      fs.bktCount b = loc_last + 1 ∧
      loc_del < loc_last ∧
      rebAct = (if decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
          fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
          fs.rebCollision = 0) then 1 else 0) ∧
      info = (fs1.locState b loc_last,
        (fs1.rKeyAt c U n_max θ b loc_last,
         (fs1.fpAt c U n_max θ (fs1.bktSalt b) b loc_last,
          fs1.fpAt c U n_max θ fs1.rebCandSalt b loc_last))) ∧
      SeedWhpMemRep base c U w₀ n_max θ s.mem ∧
      FastMemRep base c U V w₀ n_max fs1 s.mem

private theorem realizes_delMoveApplyCoreGen :
    Realizes .exact delMoveApplyCoreGenProg
      (WordEncoding.encode
        (α := (((WhpCoreParams × ℕ) × ℕ) × (ℕ × ℕ)) × (ℕ × (ℕ × (ℕ × (ℕ × ℕ))))))
      (WordEncoding.encode (α := Unit))
      DelMoveApplyCorePre
      (fun _ _ => 0) := by
  unfold delMoveApplyCoreGenProg
  have mb1 := realizes_delMoveBufGen
  have mb2 := realizes_delMoveLiveOmGen
  have mb3 := realizes_delMoveRebGen
  have mb4 := realizes_delCopySlotGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨cp, base⟩, b⟩, ⟨loc_del, loc_last⟩⟩,
      ⟨rebAct, ⟨st_l, ⟨rk_l, ⟨fpl_l, fpc_l⟩⟩⟩⟩⟩
    dsimp only at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, u, henv, rfl, hv, hb, hcnt, hlt, rfl,
      hinfo, hseed, hrep1⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq
    cases hinfo
    set fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
    obtain ⟨hll_tl, hbp1, hq1, hv1_lt, _, hbuf0_1, hbuf1_1, ⟨lm1, hv_l1⟩, hom1_fn,
      hreb1_fn⟩ := fs1_moveLast_invs u hv hb hcnt hlt
    obtain ⟨_, _, _, _, hr_lt, hne_lo, hne_lr, hne_or, ⟨hlic_le, _⟩, _, _⟩ :=
      validFastState_delete_bounds hv hb
    have hld_tl : loc_del < totalLocalCoordsWhp n_max := hlt.trans hll_tl
    have hbp_ll : capFrontWhp n_max ≤ loc_last →
        fs1.backPtr b (loc_last - capFrontWhp n_max) < poolSizeWhp n_max :=
      fun hcf => hbp1 _ (by omega)
    have hfp_live_lt := fpAt_lt θ fs1 (fs1.bktSalt b) b loc_last
    have hfp_cand_lt := fpAt_lt θ fs1 fs1.rebCandSalt b loc_last
    set st_last := fs1.locState b loc_last
    set rKey_last := fs1.rKeyAt c U n_max θ b loc_last
    set fp_live_last := fs1.fpAt c U n_max θ (fs1.bktSalt b) b loc_last
    set fp_cand_last := fs1.fpAt c U n_max θ fs1.rebCandSalt b loc_last
    obtain ⟨_, _, hstep_b⟩ := delMoveBufGenProg_fastStep (fs := fs1) henv hb hld_tl
      hbuf0_1 hbuf1_1 hseed hrep1 (st_last := st_last) (rKey_last := rKey_last) (s := s)
    set sb := (Memory.spec 0).clientState s
      (delMoveBufGenProg ((((mkWhpCoreParams c U V w n_max, base), b), loc_del),
        (st_last, rKey_last)))
    set fs1b : FastState :=
      { fs1 with
        buf :=
          if st_last = 2 then
            Function.update fs1.buf 0
              (bufInsert (cTabWhp c) (bCharWhp n_max) (fs1.buf 0) rKey_last b loc_del)
          else if st_last = 3 then
            Function.update fs1.buf 1
              (bufInsert (cTabWhp c) (bCharWhp n_max) (fs1.buf 1) rKey_last b loc_del)
          else fs1.buf }
    obtain ⟨_, _, hstep_lo⟩ := delMoveLiveOmGenProg_fastStep (fs := fs1b) henv hv.curEp_or hb
      (hv.roles_valid b hb).1 (hv.roles_valid b hb).2.1 hne_lo hld_tl hfp_live_lt
      hlic_le hv_l1 hom1_fn rfl hstep_b.2.1 hstep_b.2.2.1 (loc_last := loc_last) (s := sb)
    set slo := (Memory.spec 0).clientState sb
      (delMoveLiveOmGenProg ((((mkWhpCoreParams c U V w n_max, base), b), (loc_del, loc_last)),
        (st_last, fp_live_last)))
    set omPair := fastDeleteMoveSlices n_max b loc_del loc_last fp_live_last fs1b
    set fs1lo : FastState :=
      { fs1b with slices := omPair.1, overmarsInsCount := omPair.2 }
    have hreb_slo := reb_valid_after_moveSlices (fs1 := fs1) (loc_del := loc_del)
      (loc_last := loc_last) (fp := fp_live_last) fs1b.buf hne_lr hne_or hreb1_fn
    obtain ⟨_, _, hstep_r⟩ := delMoveRebGenProg_fastStep (fs := fs1lo) henv hv.curEp_or hb
      hr_lt hld_tl hfp_cand_lt hreb_slo hstep_lo.2.1 hstep_lo.2.2.1 (loc_last := loc_last)
      (st_last := st_last) (s := slo)
    first
    | exact ⟨c, U, V, w, n_max, fs1, henv, rfl, hrep1, hb, hld_tl, hbuf0_1, hbuf1_1⟩
    | exact ⟨c, U, V, w, n_max, θ, fs1b, lm1, henv, rfl, hstep_b.2.1, hstep_b.2.2.1,
        hv.curEp_or, hb, (hv.roles_valid b hb).1, (hv.roles_valid b hb).2.1, hne_lo,
        hld_tl, hfp_live_lt, hlic_le, hv_l1, hom1_fn⟩
    | (refine ⟨c, U, V, w, n_max, θ, fs1lo, henv, rfl, hstep_lo.2.1, hstep_lo.2.2.1,
         hv.curEp_or, hb, hr_lt, hld_tl, hfp_cand_lt, fun hra1 => ?_⟩
       exact hreb_slo (Bool.of_not_eq_false fun hd => by rw [hd] at hra1; cases hra1))
    | exact ⟨c, U, V, w, n_max, θ, _, henv, rfl, hstep_r.2.1, hstep_r.2.2.1,
        hb, hlt, hll_tl, hbp1, hq1 _ (physSlotGenProg_spec henv hb hll_tl hbp_ll hrep1).2.2.1,
        hv1_lt⟩
  )

theorem realizes_fastDeleteMoveLastGen :
    Realizes .exact fastDeleteMoveLastGenProg
      (WordEncoding.encode (α := (((WhpParams × ℕ) × ℕ) × (ℕ × ℕ)) × ℕ))
      (WordEncoding.encode (α := Unit))
      FastDelMoveLastPre
      (fun _ _ => 0) := by
  unfold fastDeleteMoveLastGenProg
  have hri := realizes_delMoveReadInfoGen
  have hac := realizes_delMoveApplyCoreGen
  realize
  all_goals (
    rcases d with ⟨⟨⟨⟨wp, base⟩, b⟩, ⟨loc_del, loc_last⟩⟩, rebAct⟩
    dsimp only at *
    simp only [Prod.mk.eta] at *
    obtain ⟨c, U, V, w₀, n_max, θ, fs, dict, u, henv, heq_wp, hv, hb, hcnt, hlt, rfl,
      hseed, hrep1⟩ := h
    have hw_eq := henv.2.2.1; subst hw_eq; subst heq_wp
    have hth := henv.2.2.2.1
    have hcp_eq : (mkWhpParams c U V w n_max).1 = mkWhpCoreParams c U V w n_max := by
      simp [mkWhpParams, Nat.not_lt.mpr hth]
    set fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
    obtain ⟨hll_tl, hbp1, hq1, _, _, _, _, _, _, _⟩ := fs1_moveLast_invs u hv hb hcnt hlt
    have hbp_ll : capFrontWhp n_max ≤ loc_last →
        fs1.backPtr b (loc_last - capFrontWhp n_max) < poolSizeWhp n_max :=
      fun hcf => hbp1 _ (by omega)
    obtain ⟨hri_st, hri_res, _, _⟩ :=
      delMoveReadInfoGenProg_spec henv hseed hrep1 hb hll_tl hbp_ll (s := s)
    rw [hcp_eq, hri_st, hri_res] at *
    first
    | exact ⟨c, U, V, w, n_max, θ, fs1, henv, rfl, hseed, hrep1, hq1, hb, hll_tl, hbp_ll⟩
    | exact ⟨c, U, V, w, n_max, θ, fs, dict, u, henv, rfl, hv, hb, hcnt, hlt, rfl, rfl,
        hseed, hrep1⟩
  )

theorem fastDeleteMoveLastGenProg_fastStep {c U V w n_max base b loc_del loc_last : ℕ}
    {θ : SeedWhp c U n_max} {fs : FastState} {dict : State U} {s : Memory.State}
    (u : Fin U)
    (henv : WhpLargeEnv c U V w n_max w base)
    (hv : ValidFastState c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max)
    (hcnt : fs.bktCount b = loc_last + 1)
    (hlt : loc_del < loc_last)
    (hseed : SeedWhpMemRep base c U w n_max θ s.mem)
    (hrep1 : FastMemRep base c U V w n_max (fastDeleteRemove c U n_max θ fs u b loc_del) s.mem) :
    let rebActiveB : Bool :=
      decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
        fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
        fs.rebCollision = 0)
    let rebAct := if rebActiveB then 1 else 0
    let fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
    let prog := fastDeleteMoveLastGenProg
      ((((mkWhpParams c U V w n_max, base), b), (loc_del, loc_last)), rebAct)
    let s' := (Memory.spec 0).clientState s prog
    memoryCost prog s ≤ 20 * cTabWhp c + 5 * hashEvalCostWhp c + 5476 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
    FastStateStep base c U V w n_max θ
      (fastDeleteMoveLast c U n_max θ b loc_del loc_last rebActiveB fs1) s s' := by
  set cp := mkWhpCoreParams c U V w n_max
  have hwp1 : (mkWhpParams c U V w n_max).1 = cp := by
    simp [mkWhpParams, Nat.not_lt.mpr henv.2.2.2.1, cp]
  set fs1 := fastDeleteRemove c U n_max θ fs u b loc_del
  set rebActiveB : Bool :=
    decide (fs.rebStage = 2 ∧ fs.dirtyIdx < fs.dirtyCount ∧
      fs.dirtyBuckets fs.dirtyIdx = b ∧ fs.rebCandSalt < sMaxWhp c n_max ∧
      fs.rebCollision = 0)
  set rebAct := if rebActiveB then 1 else 0
  obtain ⟨hll_tl, hbp1, hq1, hv1_lt, hst_lt, hbuf0_1, hbuf1_1, ⟨lm1, hv_l1⟩, hom1_fn,
    hreb1_fn⟩ := fs1_moveLast_invs u hv hb hcnt hlt
  obtain ⟨_, _, _, _, hr_lt, hne_lo, hne_lr, hne_or, ⟨hlic_le, _⟩, _, _⟩ :=
    validFastState_delete_bounds hv hb
  have hld_tl : loc_del < totalLocalCoordsWhp n_max := hlt.trans hll_tl
  have hbp_ll : capFrontWhp n_max ≤ loc_last →
      fs1.backPtr b (loc_last - capFrontWhp n_max) < poolSizeWhp n_max :=
    fun hcf => hbp1 _ (by omega)
  obtain ⟨hri_st, hri_res, hri_mc, hri_vp⟩ :=
    delMoveReadInfoGenProg_spec henv hseed hrep1 hb hll_tl hbp_ll (s := s)
  set st_last := fs1.locState b loc_last
  set rKey_last := fs1.rKeyAt c U n_max θ b loc_last
  set fp_live_last := fs1.fpAt c U n_max θ (fs1.bktSalt b) b loc_last
  set fp_cand_last := fs1.fpAt c U n_max θ fs1.rebCandSalt b loc_last
  have hfp_live_lt := fpAt_lt θ fs1 (fs1.bktSalt b) b loc_last
  have hfp_cand_lt := fpAt_lt θ fs1 fs1.rebCandSalt b loc_last
  obtain ⟨hmc_b, hvp_b, hstep_b⟩ :=
    delMoveBufGenProg_fastStep (fs := fs1) henv hb hld_tl hbuf0_1 hbuf1_1 hseed hrep1
      (st_last := st_last) (rKey_last := rKey_last) (s := s)
  set sb := (Memory.spec 0).clientState s
    (delMoveBufGenProg ((((cp, base), b), loc_del), (st_last, rKey_last)))
  set fs1b : FastState :=
    { fs1 with
      buf :=
        if st_last = 2 then
          Function.update fs1.buf 0
            (bufInsert (cTabWhp c) (bCharWhp n_max) (fs1.buf 0) rKey_last b loc_del)
        else if st_last = 3 then
          Function.update fs1.buf 1
            (bufInsert (cTabWhp c) (bCharWhp n_max) (fs1.buf 1) rKey_last b loc_del)
        else fs1.buf }
  obtain ⟨hmc_lo, hvp_lo, hstep_lo⟩ :=
    delMoveLiveOmGenProg_fastStep (fs := fs1b) henv hv.curEp_or hb (hv.roles_valid b hb).1
      (hv.roles_valid b hb).2.1 hne_lo hld_tl hfp_live_lt hlic_le hv_l1 hom1_fn rfl
      hstep_b.2.1 hstep_b.2.2.1 (loc_last := loc_last) (s := sb)
  set slo := (Memory.spec 0).clientState sb
    (delMoveLiveOmGenProg ((((cp, base), b), (loc_del, loc_last)), (st_last, fp_live_last)))
  set omPair := fastDeleteMoveSlices n_max b loc_del loc_last fp_live_last fs1b
  set fs1lo : FastState :=
    { fs1b with slices := omPair.1, overmarsInsCount := omPair.2 }
  have hreb_slo := reb_valid_after_moveSlices (fs1 := fs1) (loc_del := loc_del)
    (loc_last := loc_last) (fp := fp_live_last) fs1b.buf hne_lr hne_or hreb1_fn
  obtain ⟨hmc_r, hvp_r, hstep_r⟩ :=
    delMoveRebGenProg_fastStep (fs := fs1lo) henv hv.curEp_or hb hr_lt hld_tl
      hfp_cand_lt hreb_slo hstep_lo.2.1 hstep_lo.2.2.1 (loc_last := loc_last)
      (st_last := st_last) (s := slo)
  set sr := (Memory.spec 0).clientState slo
    (delMoveRebGenProg ((((cp, base), b), (loc_del, loc_last)), ((rebAct, st_last), fp_cand_last)))
  have hps_lt1 := (physSlotGenProg_spec henv hb hll_tl hbp_ll hrep1 (s := s)).2.2.1
  obtain ⟨hmc_c, hvp_c, hstep_c⟩ :=
    delCopySlotGenProg_fastStep henv hb hlt hll_tl (by exact hbp1) (by exact hq1 _ hps_lt1)
      (by exact hv1_lt) hst_lt hstep_r.2.1 hstep_r.2.2.1 (s := sr)
  unfold fastDeleteMoveLastGenProg
  dsimp only
  rw [hwp1]
  refine ⟨?_, ?_, ?_⟩
  · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hri_st, hri_res,
      delMoveApplyCoreGenProg]
    dsimp only [sb, slo, sr, cp, fs1, fs1b, st_last, rKey_last, fp_live_last, fp_cand_last,
      rebAct, rebActiveB] at hri_mc hmc_b hmc_lo hmc_r hmc_c ⊢
    omega
  · refine validProg_bind hri_vp ?_
    rw [hri_st, hri_res]
    unfold delMoveApplyCoreGenProg
    exact validProg_bind hvp_b (validProg_bind hvp_lo (validProg_bind hvp_r hvp_c))
  · rw [clientState_bind, hri_st, hri_res]
    unfold delMoveApplyCoreGenProg fastDeleteMoveLast
    dsimp only
    rw [clientState_bind, clientState_bind, clientState_bind]
    exact ((hstep_b.trans hstep_lo).trans hstep_r).trans hstep_c

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
