/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep
import CslibFrontier.Foundations.Logic.Function.UpdateKernel
-- `import all`: reads private epoch/invariant-transfer helpers (`curEp_ne_oldEp`,
-- `core_and_om_of_inLiveTree_eq`, `step_of_inLiveTree_eq`) from `Common`.
import all CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelTick.Common

/-!
# Epoch Rebuild Stages 3 and 4 (Old-Buffer Drain and Trie Node Clearing)

Internal correctness proofs for `epochTickStage3` and `epochTickStage4`
[BenderFarachColtonKuszmaulKuszmaul2024].

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.epochTickStage3_spec`: Stage 3 preserves
  `CoreFastInv` and `OvermarsBucketInv` and restores `ValidEpochStage`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.epochTickStage4_spec`: Stage 4 preserves
  `CoreFastInv` and `OvermarsBucketInv` and restores `ValidEpochStage`.

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

private theorem bufDelete_self_checkSlot_none {cTab bChar id rKey : ℕ} {tr : BufTrie}
    (hw : bufWalk bChar tr.trieChild rKey cTab 0 0 = some (tr.itemLeaf id)) :
    bufCheckSlot (bufDelete cTab bChar tr rKey) id = none := by
  dsimp only [bufDelete]
  rw [hw]
  dsimp only
  split_ifs with hcond
  · dsimp only [bufCheckSlot]
    split_ifs <;> first | rfl | omega
  · simp only [bufCheckSlot, Function.update_self, ne_eq, not_true_eq_false, and_false,
      ↓reduceIte, ite_self]

private theorem BufMapRel.untag_one {M tag b₀ loc₀ : ℕ} {bktCnt : ℕ → ℕ}
    {locSt rKeyOf : ℕ → ℕ → ℕ} {m : ℕ → Option (ℕ × ℕ)}
    (hrel : BufMapRel M tag bktCnt locSt rKeyOf m)
    (hb₀ : b₀ < M) (hl₀ : loc₀ < bktCnt b₀) (hst₀ : locSt b₀ loc₀ = tag)
    (hinj : ∀ b < M, ∀ loc < bktCnt b, locSt b loc = tag →
      rKeyOf b loc = rKeyOf b₀ loc₀ → b = b₀ ∧ loc = loc₀)
    (hne : 1 ≠ tag) :
    BufMapRel M tag bktCnt
      (Function.update locSt b₀ (Function.update (locSt b₀) loc₀ 1)) rKeyOf
      (Function.update m (rKeyOf b₀ loc₀) none) := by
  refine BufMapRel.of_some_iff fun rk b loc => ?_
  by_cases hbl : b = b₀ ∧ loc = loc₀
  · rcases hbl with ⟨rfl, rfl⟩
    rw [Function.update_self, Function.update_self]
    refine ⟨fun hm => ?_, fun h => absurd h.2.2.1 hne⟩
    rcases eq_or_ne rk (rKeyOf b loc) with rfl | hrk
    · rw [Function.update_self] at hm
      cases hm
    · rw [Function.update_of_ne hrk] at hm
      exact absurd ((hrel.2 rk b loc).mp hm).2.2.2.symm hrk
  · rw [Function.update_update_apply_of_ne hbl]
    by_cases hrk : rk = rKeyOf b₀ loc₀
    · subst hrk
      simp only [Function.update_self, reduceCtorEq, false_iff]
      exact fun ⟨hb, hloc, hst, heq⟩ => hbl (hinj b hb loc hloc hst heq)
    · rw [Function.update_of_ne hrk, hrel.2 rk b loc]

private def epochTickStage3Finish (s : FastState) : FastState :=
  if (s.buf s.oldEp).itemAlloc ≤ s.stageCursor then
    { s with rebStage := 4 }
  else s

private theorem epochTickStage3Finish_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {s : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ s dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ s b)
    (hs3 : s.rebStage = 3)
    (hsc_le : s.stageCursor ≤ (s.buf s.oldEp).itemAlloc)
    (hnone_lt : ∀ id < s.stageCursor, bufCheckSlot (s.buf s.oldEp) id = none) :
    let fs1 := epochTickStage3Finish s
    CoreFastInv c U V n_max θ fs1 dict ∧
    (∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs1 b) ∧
    ValidEpochStage c U n_max θ fs1 ∧
    fs1.epochClock = s.epochClock := by
  dsimp only [epochTickStage3Finish]
  by_cases hdone : (s.buf s.oldEp).itemAlloc ≤ s.stageCursor
  · rw [ite_eq_left hdone]
    have hbo := hc.bufOld_valid
    rw [ite_eq_left (by omega : s.rebStage ≤ 3)] at hbo
    obtain ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩ := hbo
    have hno_old : ∀ b < numBucketsWhp n_max, ∀ loc < s.bktCount b,
        s.locState b loc ≠ 2 + s.oldEp := by
      intro b hb loc hloc hst
      have hms : oldMap (s.rKeyAt c U n_max θ b loc) = some (b, loc) :=
        (hrel_o.2 _ b loc).mpr ⟨hb, hloc, hst, rfl⟩
      obtain ⟨id, hid, hchk⟩ := hv_o.exists_checkSlot_of_map_some hms
      exact nomatch (hnone_lt id (hid.trans_le hdone)).symm.trans hchk
    refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
      (show 4 ≤ 5 by decide) hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun b hb loc hloc => by
        change inLiveTree 4 s.oldEp (s.rebDoneFlag b) (s.locState b loc) =
          inLiveTree s.rebStage s.oldEp (s.rebDoneFlag b) (s.locState b loc)
        simp [inLiveTree, hs3, hno_old b hb loc hloc])
      (by
        dsimp only [FastState.oldEp]
        simp only [Nat.reduceLeDiff, ↓reduceIte]
        exact ⟨hno_old, hv_o.toClearable,
          hna_o.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hia_o) 1)⟩)
      (by simp [ValidEpochStage]) rfl
  · rw [ite_eq_right hdone]
    exact ⟨hc, hom, by simpa [ValidEpochStage, hs3, hsc_le] using hnone_lt, rfl⟩

/-- Stage-3 tick promotes `2 + oldEp` items to `locState = 1` and deletes them from `buf oldEp`. -/
theorem epochTickStage3_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs b)
    (hs3 : fs.rebStage = 3)
    (hpre : ValidEpochStagePreTick c U n_max θ fs) :
    let fs1 := epochTickStage3 c U n_max θ fs
    CoreFastInv c U V n_max θ fs1 dict ∧
    (∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs1 b) ∧
    ValidEpochStage c U n_max θ fs1 ∧
    fs1.epochClock = fs.epochClock := by
  simp only [ValidEpochStagePreTick, hs3, Nat.reduceEqDiff, ↓reduceIte] at hpre
  obtain ⟨hsc_le, hnone0⟩ := hpre
  have hbo := hc.bufOld_valid
  rw [ite_eq_left (by omega : fs.rebStage ≤ 3)] at hbo
  obtain ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩ := hbo
  set oldEp := fs.oldEp
  set oldTr := fs.buf oldEp
  dsimp only [epochTickStage3]
  by_cases hlt : fs.stageCursor < oldTr.itemAlloc
  · rw [ite_eq_left hlt]
    set nextCur := fs.stageCursor + 1
    cases hchk : bufCheckSlot oldTr fs.stageCursor with
    | some bloc =>
      rcases bloc with ⟨b₀, loc₀⟩
      dsimp only
      obtain ⟨_, k, hk_lt, hwk, hmk⟩ := hv_o.checkSlot_some hchk
      obtain ⟨hb₀, hl₀, hst₀, hrk_k⟩ := (hrel_o.2 k b₀ loc₀).mp hmk
      subst hrk_k
      set rKey := fs.rKeyAt c U n_max θ b₀ loc₀
      set tr' := bufDelete (cTabWhp c) (bCharWhp n_max) oldTr rKey
      obtain ⟨hv_tr', hna_eq, hia_eq, _, hnone_pres⟩ := hv_o.delete_spec hk_lt
      have hself_none : bufCheckSlot tr' fs.stageCursor = none :=
        bufDelete_self_checkSlot_none hwk
      set fs' : FastState :=
        { fs with
          buf := Function.update fs.buf oldEp tr'
          locState := Function.update fs.locState b₀ (Function.update (fs.locState b₀) loc₀ 1)
          stageCursor := nextCur }
      have hinL_pres : ∀ b < numBucketsWhp n_max, ∀ loc < fs.bktCount b,
          inLiveTree fs'.rebStage fs'.oldEp (fs'.rebDoneFlag b) (fs'.locState b loc) =
            inLiveTree fs.rebStage oldEp (fs.rebDoneFlag b) (fs.locState b loc) := by
        intro b _ loc _
        change inLiveTree fs.rebStage oldEp _ _ = _
        rw [hs3]
        dsimp only [fs']
        by_cases hbl : b = b₀ ∧ loc = loc₀
        · rcases hbl with ⟨rfl, rfl⟩
          rw [Function.update_self, Function.update_self, hst₀]
          simp [inLiveTree]
        · rw [Function.update_update_apply_of_ne hbl]
      have hc' : CoreFastInv c U V n_max θ fs' dict :=
        { hth := hc.hth
          curEp_or := hc.curEp_or
          epochClock_lt := hc.epochClock_lt
          rebStage_le := hc.rebStage_le
          rebCollision_zero := hc.rebCollision_zero
          qv_global := hc.qv_global
          bktCount_le := hc.bktCount_le
          bktCount_ge_zero := hc.bktCount_ge_zero
          locState_active := fun b hb loc hloc => by
            dsimp only [fs']
            by_cases hbl : b = b₀ ∧ loc = loc₀
            · rcases hbl with ⟨rfl, rfl⟩
              simp
            · rw [Function.update_update_apply_of_ne hbl]
              exact hc.locState_active b hb loc hloc
          locState_inactive := fun b loc hnot => by
            dsimp only [fs']
            rw [Function.update_update_apply_of_ne (fun ⟨rfl, rfl⟩ => hnot ⟨hb₀, hl₀⟩)]
            exact hc.locState_inactive b loc hnot
          active_item := hc.active_item
          quot_inj := hc.quot_inj
          dict_map := hc.dict_map
          poolFreeTop_le := hc.poolFreeTop_le
          backPtr_valid := hc.backPtr_valid
          freeStack_lt := hc.freeStack_lt
          backPtr_inj := hc.backPtr_inj
          freeStack_inj := hc.freeStack_inj
          back_free_disj := hc.back_free_disj
          pool_conservation := hc.pool_conservation
          roles_valid := hc.roles_valid
          bktSalt_lt := hc.bktSalt_lt
          live_fp_inj := fun b hb l₁ hl₁ l₂ hl₂ hin₁ hin₂ hfeq =>
            hc.live_fp_inj b hb l₁ hl₁ l₂ hl₂ ((hinL_pres b hb l₁ hl₁).symm.trans hin₁)
              ((hinL_pres b hb l₂ hl₂).symm.trans hin₂) hfeq
          live_valid := fun b hb => by
            obtain ⟨lm, hvl, hrl⟩ := hc.live_valid b hb
            exact ⟨lm, hvl, hrl.congr (fun _ _ => rfl) fun loc hloc => by
              rw [hinL_pres b hb loc hloc]⟩
          rKey_buf_inj := fun b₁ hb₁ l₁ hl₁ b₂ hb₂ l₂ hl₂ h2₁ h2₂ hrkeq => by
            have h2_orig : ∀ b < numBucketsWhp n_max, ∀ l < fs.bktCount b,
                2 ≤ fs'.locState b l → 2 ≤ fs.locState b l := by
              intro b _ l _ h2
              dsimp only [fs'] at h2
              by_cases hbl : b = b₀ ∧ l = loc₀
              · rcases hbl with ⟨rfl, rfl⟩
                rw [Function.update_self, Function.update_self] at h2
                omega
              · rwa [Function.update_update_apply_of_ne hbl] at h2
            exact hc.rKey_buf_inj b₁ hb₁ l₁ hl₁ b₂ hb₂ l₂ hl₂
              (h2_orig b₁ hb₁ l₁ hl₁ h2₁) (h2_orig b₂ hb₂ l₂ hl₂ h2₂) hrkeq
          bufCur_valid := by
            obtain ⟨hi_c, hn_c, cm, hvc, hrc⟩ := hc.bufCur_valid
            dsimp only [fs']
            rw [Function.update_of_ne (curEp_ne_oldEp hc.curEp_or)]
            refine ⟨hi_c, hn_c, cm, hvc, hrc.congr (fun _ _ => rfl) (fun b _ loc _ => ?_)
              (fun _ _ _ _ => rfl)⟩
            by_cases hbl : b = b₀ ∧ loc = loc₀
            · rcases hbl with ⟨rfl, rfl⟩
              rw [Function.update_self, Function.update_self, hst₀]
              have := curEp_ne_oldEp hc.curEp_or
              omega
            · rw [Function.update_update_apply_of_ne hbl]
          bufOld_valid := by
            dsimp only [fs', FastState.oldEp, oldEp]
            simp only [hs3, Nat.reduceLeDiff, ↓reduceIte, Function.update_self]
            refine ⟨hia_eq ▸ hia_o, hna_eq.symm ▸ hia_eq.symm ▸ hna_o,
              Function.update oldMap rKey none, hv_tr', ?_⟩
            exact hrel_o.untag_one hb₀ hl₀ hst₀
              (fun b hb loc hloc h1 =>
                hc.rKey_buf_inj b hb loc hloc b₀ hb₀ loc₀ hl₀ (by omega) (by omega))
              (by omega) }
      have hom' : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs' b := by
        intro b hb
        rcases hom b hb with ⟨ha0, hlt5⟩ | ⟨ha1, h16, hcur, hlin, hins_om, omM, hvO, hrO⟩
        · exact Or.inl ⟨ha0, hlt5⟩
        · exact Or.inr ⟨ha1, h16, hcur, hlin, hins_om, omM, hvO,
            hrO.congr (fun _ _ => rfl) fun loc hlt_c => by
              rw [hinL_pres b hb loc (hlt_c.trans hcur)]⟩
      have hbuf_o' : fs'.buf fs'.oldEp = tr' := Function.update_self _ _ _
      exact epochTickStage3Finish_spec hc' hom' hs3
        (hbuf_o'.symm ▸ hia_eq.symm ▸ Nat.succ_le_of_lt hlt)
        fun id hid => by
          rw [hbuf_o']
          rcases Nat.lt_succ_iff_lt_or_eq.mp hid with hid' | rfl
          · exact hnone_pres id (hnone0 id hid')
          · exact hself_none
    | none =>
      dsimp only
      set fs' : FastState := { fs with stageCursor := nextCur }
      obtain ⟨hc', hom'⟩ := core_and_om_of_inLiveTree_eq fs' hc hom rfl hc.epochClock_lt
        hc.rebStage_le hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
        (by dsimp only [fs', FastState.oldEp]; rw [ite_eq_left (by omega : fs.rebStage ≤ 3)]
            exact ⟨hia_o, hna_o, oldMap, hv_o, hrel_o⟩)
      exact epochTickStage3Finish_spec hc' hom' hs3 (Nat.succ_le_of_lt hlt)
        (fun id hid => by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hid with hid' | rfl
          · exact hnone0 id hid'
          · exact hchk)
  · rw [ite_eq_right hlt]
    simpa only [epochTickStage3Finish, oldTr, oldEp, ite_eq_left (Nat.not_lt.mp hlt)] using
      epochTickStage3Finish_spec hc hom hs3 hsc_le hnone0

private theorem ClearableBufTrie.clearSteps_pres :
    ∀ (k : ℕ) {tr : BufTrie}, ClearableBufTrie tr →
      ClearableBufTrie (bufClearSteps k tr) ∧ (bufClearSteps k tr).nodeAlloc ≤ max 1 tr.nodeAlloc
  | 0, tr, hc => ⟨hc, le_max_right 1 tr.nodeAlloc⟩
  | k + 1, tr, hc => by
    obtain ⟨hc1, hna1⟩ := hc.clearOne_step
    obtain ⟨hck, hnak⟩ := hc1.clearSteps_pres k
    refine ⟨hck, hnak.trans ?_⟩
    rw [hna1]
    have := hc.bounds.1
    omega

/-- Stage-4 tick clears 8 trie nodes of `buf oldEp` per step until empty (`rebStage = 5`). -/
theorem epochTickStage4_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {fs : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hom : ∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs b)
    (hs4 : fs.rebStage = 4) :
    let fs1 := epochTickStage4 fs
    CoreFastInv c U V n_max θ fs1 dict ∧
    (∀ b < numBucketsWhp n_max, OvermarsBucketInv c U n_max θ fs1 b) ∧
    ValidEpochStage c U n_max θ fs1 ∧
    fs1.epochClock = fs.epochClock := by
  have hbo := hc.bufOld_valid
  rw [ite_eq_right (by omega : ¬(fs.rebStage ≤ 3)), ite_eq_left hs4] at hbo
  obtain ⟨hno_old, hclr, hna_ub⟩ := hbo
  set oldEp := fs.oldEp
  set oldTr := fs.buf oldEp
  dsimp only [epochTickStage4]
  by_cases hle8 : oldTr.nodeAlloc ≤ 8
  · obtain ⟨hv_empty, hna1, hia0⟩ := hclr.clearSteps_spec (cTabWhp c) (bCharWhp n_max) 8 hle8
    rw [decide_eq_true hle8, ite_eq_left rfl]
    refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
      le_rfl hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (Function.update_of_ne (curEp_ne_oldEp hc.curEp_or) _ _)
      (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => by simp [inLiveTree, hs4])
      (by
        simp only [Nat.reduceLeDiff, Nat.reduceEqDiff, ↓reduceIte]
        dsimp only [FastState.oldEp, oldEp]
        rw [Function.update_self]
        exact ⟨hno_old, hv_empty, hna1, hia0⟩)
      (by simp [ValidEpochStage]) rfl
  · obtain ⟨hclr', hna'⟩ := hclr.clearSteps_pres 8
    have h1_le : 1 ≤ oldTr.nodeAlloc := hclr.bounds.1
    rw [decide_eq_false hle8, ite_eq_right Bool.false_ne_true]
    refine step_of_inLiveTree_eq hc hom rfl hc.epochClock_lt
      (show 4 ≤ 5 by decide) hc.rebCollision_zero rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl
      (Function.update_of_ne (curEp_ne_oldEp hc.curEp_or) _ _)
      (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => by simp [inLiveTree, hs4])
      (by
        simp only [Nat.reduceLeDiff, ↓reduceIte]
        dsimp only [FastState.oldEp, oldEp]
        rw [Function.update_self]
        exact ⟨hno_old, hclr', hna'.trans ((max_eq_right h1_le).trans_le hna_ub)⟩)
      (by simp [ValidEpochStage]) rfl


end Cslib.DataStructure.Dictionary.SuccinctWhp

end
