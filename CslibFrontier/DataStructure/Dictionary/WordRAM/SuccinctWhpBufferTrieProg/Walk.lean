/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpSwarProg
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.Rt
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.Helpers
import CslibFrontier.Tactic.Realize

/-!
# Internal Bounded-Depth `BufTrie` Character Walk (`bufWalkLoopGenProg`)

Internal traversal loop shared privately by `EverPresent`, `Lookup`, and `Delete`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufWalkLoopGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_bufWalkLoopGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufWalkLoop_spec`
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Finset
open scoped BigOperators
open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.Dynamic (logLogFactor one_le_logLogFactor)
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

attribute [local simp] clientResult_pure_whp clientState_pure_whp

/-- Precondition for one step of `bufWalk`. -/
def BufWalkStepPre (w : ℕ) : BufRt × (ℕ × (ℕ × ℕ)) → Memory.State → Prop
  | (rt, (_, (cur, _))), _ => BufRtEnvGen w rt ∧ cur < brMaxNodes rt

/-- One character-walk step on `offChild`. -/
def bufWalkStepProg : BufRt × (ℕ × (ℕ × ℕ)) → Memory.Prog (ℕ × (ℕ × ℕ))
  | (rt, (alive, (cur, r_cur))) => do
    let ch ← pure (r_cur &&& brMaskBChar rt)
    let idx ← pure (cur * brPowBChar rt + ch)
    let nxt ← readPackedGenProg (((brBase rt, brOffChild rt), (brGBits rt, brW rt)), idx)
    let r_nxt ← pure (r_cur >>> brBChar rt)
    if alive = 0 then
      pure (0, (0, r_nxt))
    else if nxt = 0 then
      pure (0, (0, r_nxt))
    else
      pure (1, (nxt, r_nxt))

@[simp]
private theorem memoryCost_bufWalkStepProg (p : BufRt × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    memoryCost (bufWalkStepProg p) s = 2 := by
  unfold bufWalkStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
  rw [memoryCost_bind, memoryCost_readPackedGen]
  split_ifs <;> rfl

private theorem memoryCost_bufWalkStepProg_pos (p : BufRt × (ℕ × (ℕ × ℕ))) (s : Memory.State) :
    1 ≤ memoryCost (bufWalkStepProg p) s := by simp

private theorem realizes_bufWalkStep :
    Realizes .exact bufWalkStepProg
      (WordEncoding.encode (α := BufRt × (ℕ × (ℕ × ℕ))))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      BufWalkStepPre
      (fun _ _ => 0) := by
  unfold bufWalkStepProg
  have hrp := realizes_readPackedGen
  realize
  all_goals
    rcases d with ⟨rt, ⟨alive, ⟨cur, r_cur⟩⟩⟩
    obtain ⟨⟨c, U, V, w₀, n_max, base, ep, henv, hep, rfl⟩, hcur⟩ := h
    have hth := henv.2.2.2.1
    have hw_eq := henv.2.2.1
    subst hw_eq
    dsimp only [mkBufRt, brMaxNodes, brMaskBChar, brPowBChar, brBChar, brBase, brOffChild,
      brGBits, brW] at hcur ⊢
    obtain ⟨_, _, _, htc_le, _, _⟩ := sublinear_table_bits_le hth
    have hg_pos := globalPtrBits_pos_of_large hth
    have htc_n : trieChildEntriesWhp c n_max ≤ n_max :=
      (Nat.le_mul_of_pos_right _ hg_pos).trans htc_le
    have hch_lt : r_cur &&& (2 ^ bCharWhp n_max - 1) < 2 ^ bCharWhp n_max := by
      rw [Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hprod_le : cur * 2 ^ bCharWhp n_max ≤ trieChildEntriesWhp c n_max := by
      unfold trieChildEntriesWhp
      exact Nat.mul_le_mul_right _ hcur.le
    have hidx_lt : cur * 2 ^ bCharWhp n_max + (r_cur &&& (2 ^ bCharWhp n_max - 1)) <
        trieChildEntriesWhp c n_max := by
      unfold trieChildEntriesWhp
      calc cur * 2 ^ bCharWhp n_max + (r_cur &&& (2 ^ bCharWhp n_max - 1))
          < cur * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hch_lt _
        _ = (cur + 1) * 2 ^ bCharWhp n_max := by ring
        _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hcur
    first
    | exact henv.fits_const (by decide)
    | exact henv.fits_of_le_n_max (hidx_lt.le.trans htc_n)
    | exact rt_child_safe henv hep hidx_lt

/-- Parameter-free wrapper for `iterate bufWalkStepProg`. -/
def bufWalkLoopGenProg :
    (BufRt × (ℕ × (ℕ × ℕ))) × ℕ → Memory.Prog (ℕ × (ℕ × ℕ))
  | ((rt, x), rem) => iterate bufWalkStepProg rt rem x

theorem realizes_bufWalkLoopGen :
    Realizes .exact bufWalkLoopGenProg
      (WordEncoding.encode (α := (BufRt × (ℕ × (ℕ × ℕ))) × ℕ))
      (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
      (fun w ((rt, x), rem) s => iterationSafe bufWalkStepProg BufWalkStepPre w rt rem x s)
      (fun _ _ => 0) :=
  Realizes.iterate₀
    (WordEncoding.encode (α := BufRt))
    (WordEncoding.encode (α := ℕ × (ℕ × ℕ)))
    realizes_bufWalkStep
    memoryCost_bufWalkStepProg_pos

theorem bufWalkLoop_spec {c U V w n_max base ep : ℕ} {tr : BufTrie} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : BufTrieMemRep base c U V w n_max ep tr s.mem)
    (halloc : 1 ≤ tr.nodeAlloc)
    (hchild : ∀ v ch, tr.trieChild v ch ≠ 0 → tr.trieChild v ch < tr.nodeAlloc) :
    let rt := mkBufRt c U V w n_max base ep
    ∀ rem alive cur r_cur,
      cur < tr.nodeAlloc →
      let prog := bufWalkLoopGenProg ((rt, (alive, (cur, r_cur))), rem)
      iterationSafe bufWalkStepProg BufWalkStepPre w rt rem (alive, (cur, r_cur)) s ∧
      (Memory.spec 0).clientState s prog = s ∧
      memoryCost prog s = 2 * rem ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog ∧
      (alive = 0 → ((Memory.spec 0).clientResult s prog).1 = 0) ∧
      (alive = 1 →
        match bufWalk (bCharWhp n_max) tr.trieChild r_cur rem 0 cur with
        | none => ((Memory.spec 0).clientResult s prog).1 = 0
        | some leaf =>
          ∃ r_leaf,
            (Memory.spec 0).clientResult s prog = (1, (leaf, r_leaf)) ∧
            leaf < tr.nodeAlloc) := by
  intro rt rem
  have hw := henv.2.1
  have hna_max : tr.nodeAlloc ≤ maxTrieNodesWhp c n_max := hrep.1
  have hc_seg := (rt_seg_le c U V w n_max base ep hep).2.2.1
  have hrep_ch : ∀ u < maxTrieNodesWhp c n_max, ∀ ch < 2 ^ bCharWhp n_max,
      readPacked (base + brOffChild rt) (globalPtrBits n_max) w s.mem
        (u * 2 ^ bCharWhp n_max + ch) = tr.trieChild u ch := by
    have h := hrep.2.2.2.2.1
    rcases hep with rfl | rfl <;> exact h
  induction rem with
  | zero =>
    intro alive cur r_cur _
    refine ⟨trivial, rfl, Nat.mul_zero 2 ▸ rfl, validProg_pure _,
      fun ha => ha, fun ha => ?_⟩
    dsimp only [bufWalk, bufWalkLoopGenProg, iterate]
    rw [StateTransitionSpec.clientResult_pure]
    exact ⟨r_cur, ha ▸ rfl, ‹cur < tr.nodeAlloc›⟩
  | succ rem ih =>
    intro alive cur r_cur hcur
    have hcur_max : cur < maxTrieNodesWhp c n_max := hcur.trans_le hna_max
    have hpre : BufWalkStepPre w (rt, (alive, (cur, r_cur))) s :=
      ⟨⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩, hcur_max⟩
    set ch := r_cur % 2 ^ bCharWhp n_max with hch_def
    have hch_eq : r_cur &&& brMaskBChar rt = ch := by
      dsimp only [rt, mkBufRt, brMaskBChar, ch]
      exact Nat.and_two_pow_sub_one_eq_mod r_cur (bCharWhp n_max)
    have hch_lt : ch < 2 ^ bCharWhp n_max := Nat.mod_lt _ (Nat.two_pow_pos _)
    set idx := cur * 2 ^ bCharWhp n_max + ch
    have hidx_lt : idx < trieChildEntriesWhp c n_max := by
      unfold trieChildEntriesWhp
      calc cur * 2 ^ bCharWhp n_max + ch
          < cur * 2 ^ bCharWhp n_max + 2 ^ bCharWhp n_max := Nat.add_lt_add_left hch_lt _
        _ = (cur + 1) * 2 ^ bCharWhp n_max := by ring
        _ ≤ maxTrieNodesWhp c n_max * 2 ^ bCharWhp n_max := Nat.mul_le_mul_right _ hcur_max
    set r_nxt := r_cur / 2 ^ bCharWhp n_max with hr_def
    have hr_eq : r_cur >>> brBChar rt = r_nxt := by
      dsimp only [rt, mkBufRt, brBChar, r_nxt]
      exact Nat.shiftRight_eq_div_pow r_cur (bCharWhp n_max)
    set stepP := bufWalkStepProg (rt, (alive, (cur, r_cur)))
    have hidx_rt : cur * brPowBChar rt + (r_cur &&& brMaskBChar rt) = idx := by
      rw [hch_eq]; rfl
    have hstep_st : (Memory.spec 0).clientState s stepP = s := by
      dsimp only [stepP, bufWalkStepProg]
      simp only [pure_bind]
      rw [clientState_bind, clientState_readPackedGen]
      split_ifs <;> rfl
    have hstep_vp : ValidProg w (base + largeSpaceWhp c U V w n_max) s stepP := by
      dsimp only [stepP, bufWalkStepProg]
      simp only [pure_bind]
      refine validProg_bind (validProg_readPacked hw (hidx_rt.symm ▸ hidx_lt) hc_seg) ?_
      rw [clientState_readPackedGen]
      split_ifs <;> exact validProg_pure _
    have hnxt_eq : readPacked (brBase rt + brOffChild rt) (brGBits rt) (brW rt) s.mem
        (cur * brPowBChar rt + (r_cur &&& brMaskBChar rt)) = tr.trieChild cur ch := by
      rw [hch_eq]
      exact hrep_ch cur hcur_max ch hch_lt
    set stepRes :=
      if alive = 0 then (0, (0, r_nxt))
      else if tr.trieChild cur ch = 0 then (0, (0, r_nxt))
      else (1, (tr.trieChild cur ch, r_nxt))
    have hstep_res : (Memory.spec 0).clientResult s stepP = stepRes := by
      dsimp only [stepP, bufWalkStepProg, stepRes]
      simp only [pure_bind]
      rw [clientResult_bind, clientState_readPackedGen,
        clientResult_readPackedGen, hnxt_eq, hr_eq]
      by_cases ha0 : alive = 0
      · simp [ha0]
      · by_cases hn0 : tr.trieChild cur ch = 0 <;> simp [ha0, hn0]
    have hcur_nxt : stepRes.2.1 < tr.nodeAlloc := by
      dsimp only [stepRes]
      split_ifs with ha0 hn0
      · exact halloc
      · exact halloc
      · exact hchild cur ch hn0
    obtain ⟨hsafe_r, hst_r, hmc_r, hvp_r, ha0_r, ha1_r⟩ :=
      ih stepRes.1 stepRes.2.1 stepRes.2.2 hcur_nxt
    have hst_all : (Memory.spec 0).clientState s
        (bufWalkLoopGenProg ((rt, (alive, (cur, r_cur))), rem + 1)) = s := by
      change (Memory.spec 0).clientState s
        (stepP >>= fun s' => iterate bufWalkStepProg rt rem s') = s
      rw [clientState_bind, hstep_st, hstep_res]
      exact hst_r
    have hres_all : (Memory.spec 0).clientResult s
        (bufWalkLoopGenProg ((rt, (alive, (cur, r_cur))), rem + 1)) =
        (Memory.spec 0).clientResult s (bufWalkLoopGenProg ((rt, stepRes), rem)) := by
      change (Memory.spec 0).clientResult s
        (stepP >>= fun s' => iterate bufWalkStepProg rt rem s') = _
      rw [clientResult_bind, hstep_st, hstep_res]
      rfl
    refine ⟨⟨hpre, ?_⟩, hst_all, ?_, ?_, ?_, ?_⟩
    · rw [clientState_width, hstep_st, clientResult_width, hstep_res]
      exact hsafe_r
    · change memoryCost (stepP >>= fun s' => iterate bufWalkStepProg rt rem s') s = 2 * (rem + 1)
      simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
      change memoryCost stepP s +
        memoryCost (bufWalkLoopGenProg
          ((rt, (Memory.spec 0).clientResult s stepP), rem))
          ((Memory.spec 0).clientState s stepP) = 2 * (rem + 1)
      rw [hstep_st, hstep_res, memoryCost_bufWalkStepProg, hmc_r]
      ring
    · change ValidProg w (base + largeSpaceWhp c U V w n_max) s
        (stepP >>= fun s' => iterate bufWalkStepProg rt rem s')
      refine validProg_bind hstep_vp ?_
      change ValidProg w (base + largeSpaceWhp c U V w n_max)
        ((Memory.spec 0).clientState s stepP)
        (bufWalkLoopGenProg ((rt, (Memory.spec 0).clientResult s stepP), rem))
      rw [hstep_st, hstep_res]
      exact hvp_r
    · intro ha0
      rw [hres_all]
      exact ha0_r (by dsimp [stepRes]; simp [ha0])
    · intro ha1
      rw [hres_all]
      dsimp only [bufWalk]
      rw [laneGet_zero_eq_mod, ← hch_def]
      by_cases hn0 : tr.trieChild cur ch = 0
      · rw [ite_eq_left hn0]
        exact ha0_r (by dsimp [stepRes]; simp [ha1, hn0])
      · rw [ite_eq_right hn0, bufWalk_add_off, ← hr_def]
        have hsr : stepRes = (1, (tr.trieChild cur ch, r_nxt)) := by
          dsimp [stepRes]; simp [ha1, hn0]
        rw [hsr] at ha1_r ⊢
        exact ha1_r rfl

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
