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
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBufferTrieProg.Helpers
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.Tactic.Realize

/-!
# Internal Bounded-Depth `BufTrie` Character Walk (`bufWalkLoopGenProg`)

Internal traversal loop shared privately by `EverPresent`, `Lookup`, and `Delete`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufWalkLoopGenProg`

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_bufWalkLoopGen`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufWalkLoop_spec`
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.bufWalkLoop_root_bind_spec`
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
    have hidx_lt : cur * 2 ^ bCharWhp n_max + (r_cur &&& (2 ^ bCharWhp n_max - 1)) <
        trieChildEntriesWhp c n_max := mul_add_lt_mul_bound hcur hch_lt
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
  intro rt rem alive cur r_cur hcur
  have hw := henv.2.1
  have hna_max : tr.nodeAlloc ≤ maxTrieNodesWhp c n_max := hrep.1
  have hc_seg := (rt_seg_le c U V w n_max base ep hep).child_le
  have hrep_ch : ∀ u < maxTrieNodesWhp c n_max, ∀ ch < 2 ^ bCharWhp n_max,
      readPacked (base + brOffChild rt) (globalPtrBits n_max) w s.mem
        (u * 2 ^ bCharWhp n_max + ch) = tr.trieChild u ch := by
    have h := hrep.2.2.2.2.1
    rcases hep with rfl | rfl <;> exact h
  -- After `k` steps the state is `s`, and a live walk has `rem - k` characters left of the
  -- outcome it started with.
  let inv : ℕ → ℕ × (ℕ × ℕ) → Memory.State → Prop := fun k a t =>
    t = s ∧ a.2.1 < tr.nodeAlloc ∧ (alive = 0 → a.1 = 0) ∧
      (alive = 1 → a.1 = 0 ∧ bufWalk (bCharWhp n_max) tr.trieChild r_cur rem 0 cur = none ∨
        a.1 = 1 ∧ bufWalk (bCharWhp n_max) tr.trieChild r_cur rem 0 cur =
          bufWalk (bCharWhp n_max) tr.trieChild a.2.2 (rem - k) 0 a.2.1)
  have hstep : ∀ k < rem, ∀ a t, inv k a t →
      BufWalkStepPre w (rt, a) t ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) t (bufWalkStepProg (rt, a)) ∧
      inv (k + 1) ((Memory.spec 0).clientResult t (bufWalkStepProg (rt, a)))
        ((Memory.spec 0).clientState t (bufWalkStepProg (rt, a))) := by
    rintro k hk ⟨al, cu, rc⟩ t ⟨rfl, hcu, h0, h1⟩
    dsimp only at hcu h0 h1
    have hcu_max : cu < maxTrieNodesWhp c n_max := hcu.trans_le hna_max
    set ch := rc % 2 ^ bCharWhp n_max with hch_def
    have hch_lt : ch < 2 ^ bCharWhp n_max := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hidx : cu * brPowBChar rt + (rc &&& brMaskBChar rt) = cu * 2 ^ bCharWhp n_max + ch := by
      rw [show rc &&& brMaskBChar rt = ch from Nat.and_two_pow_sub_one_eq_mod rc _]; rfl
    have hr : rc >>> brBChar rt = rc / 2 ^ bCharWhp n_max := Nat.shiftRight_eq_div_pow _ _
    have hnxt : readPacked (brBase rt + brOffChild rt) (brGBits rt) (brW rt) t.mem
        (cu * brPowBChar rt + (rc &&& brMaskBChar rt)) = tr.trieChild cu ch := by
      rw [hidx]; exact hrep_ch cu hcu_max ch hch_lt
    have hst : (Memory.spec 0).clientState t (bufWalkStepProg (rt, (al, (cu, rc)))) = t := by
      dsimp only [bufWalkStepProg]
      simp only [pure_bind]
      rw [clientState_bind, clientState_readPackedGen]
      split_ifs <;> rfl
    have hres : (Memory.spec 0).clientResult t (bufWalkStepProg (rt, (al, (cu, rc)))) =
        if al = 0 ∨ tr.trieChild cu ch = 0 then (0, (0, rc / 2 ^ bCharWhp n_max))
        else (1, (tr.trieChild cu ch, rc / 2 ^ bCharWhp n_max)) := by
      dsimp only [bufWalkStepProg]
      simp only [pure_bind]
      rw [clientResult_bind, clientState_readPackedGen, clientResult_readPackedGen, hnxt, hr]
      by_cases ha0 : al = 0 <;> by_cases hn0 : tr.trieChild cu ch = 0 <;> simp [ha0, hn0]
    refine ⟨⟨⟨c, U, V, w, n_max, base, ep, henv, hep, rfl⟩, hcu_max⟩, ?_, ?_⟩
    · dsimp only [bufWalkStepProg]
      simp only [pure_bind]
      refine validProg_bind (validProg_readPacked hw
        (hidx.symm ▸ mul_add_lt_mul_bound hcu_max hch_lt) hc_seg) ?_
      rw [clientState_readPackedGen]
      split_ifs <;> exact validProg_pure _
    rw [hst, hres]
    refine ⟨rfl, ?_, fun ha => by simp [h0 ha], fun ha => ?_⟩
    · split_ifs with hn0
      · exact halloc
      · exact hchild cu ch (not_or.1 hn0).2
    rcases h1 ha with ⟨ha0, hw0⟩ | ⟨ha1, hwk⟩
    · exact .inl ⟨by simp [ha0], hw0⟩
    rw [hwk, show rem - k = rem - (k + 1) + 1 by omega]
    dsimp only [bufWalk]
    rw [laneGet_zero_eq_mod, ← hch_def, bufWalk_add_off]
    by_cases hn0 : tr.trieChild cu ch = 0 <;> simp [ha1, hn0]
  obtain ⟨hsafe, hvp, hst, hlt, h0, h1⟩ := validProg_iterate_of_inv inv hstep
    (a := (alive, (cur, r_cur))) ⟨rfl, hcur, id, fun ha => .inr ⟨ha, rfl⟩⟩
  refine ⟨hsafe, hst, memoryCost_iterate_eq_of _ 2 rt (fun a => memoryCost_bufWalkStepProg (rt, a))
    rem _ s, hvp, h0, fun ha => ?_⟩
  rcases h1 ha with ⟨hr0, hw0⟩ | ⟨hr1, hwk⟩
  · rw [hw0]; exact hr0
  · rw [hwk, Nat.sub_self]
    exact ⟨_, Prod.ext hr1 rfl, hlt⟩

/-- The shape shared by `bufEverPresentGenProg`, `bufLookupGenProg` and `bufDeleteGenProg`: walk
`rKey` from the root of a valid trie, then return `dflt` if the walk falls off the trie and run
`leafProg` on the leaf reached otherwise. The composite costs the `2 * cTabWhp c` of the walk
plus the cost of the branch taken, and only the leaf branch touches memory. -/
theorem bufWalkLoop_root_bind_spec {α : Type} (dflt : α) (leafProg : BufRt × ℕ → Memory.Prog α)
    {c U V w n_max base ep rKey : ℕ} {tr : BufTrie} {mapFn : ℕ → Option (ℕ × ℕ)}
    {s : Memory.State} (henv : WhpLargeEnv c U V w n_max w base) (hep : ep = 0 ∨ ep = 1)
    (hrep : BufTrieMemRep base c U V w n_max ep tr s.mem)
    (hv : ValidBufTrie (cTabWhp c) (bCharWhp n_max) tr mapFn) :
    let rt := mkBufRt c U V w n_max base ep
    let prog := mkBufRtGenProg ((mkWhpCoreParams c U V w n_max, base), ep) >>= fun rt =>
      bufWalkLoopGenProg ((rt, (1, (0, rKey))), brCTab rt) >>= fun (alive, leafRest) =>
        if alive = 0 then pure dflt else leafProg (rt, leafRest.1)
    (bufWalk (bCharWhp n_max) tr.trieChild rKey (cTabWhp c) 0 0 = none →
      (Memory.spec 0).clientState s prog = s ∧ (Memory.spec 0).clientResult s prog = dflt ∧
      memoryCost prog s = 2 * cTabWhp c ∧
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog) ∧
    ∀ leaf, bufWalk (bCharWhp n_max) tr.trieChild rKey (cTabWhp c) 0 0 = some leaf →
      leaf < tr.nodeAlloc ∧
      (Memory.spec 0).clientState s prog = (Memory.spec 0).clientState s (leafProg (rt, leaf)) ∧
      (Memory.spec 0).clientResult s prog =
        (Memory.spec 0).clientResult s (leafProg (rt, leaf)) ∧
      memoryCost prog s = 2 * cTabWhp c + memoryCost (leafProg (rt, leaf)) s ∧
      (ValidProg w (base + largeSpaceWhp c U V w n_max) s (leafProg (rt, leaf)) →
        ValidProg w (base + largeSpaceWhp c U V w n_max) s prog) := by
  intro rt prog
  obtain ⟨hrt_st, hrt_res, hrt_mc, hrt_vp⟩ := mkBufRtGenProg_spec (c := c) (U := U) (V := V)
    (w := w) (n_max := n_max) (base := base) (ep := ep) henv.2.2.2.1 s
  obtain ⟨-, hw_st, hw_mc, hw_vp, -, hw1⟩ :=
    bufWalkLoop_spec henv hep hrep hv.bounds.1 hv.bounds.2.2.1 (cTabWhp c) 1 0 rKey hv.bounds.1
  set wres := (Memory.spec 0).clientResult s (bufWalkLoopGenProg ((rt, (1, (0, rKey))), cTabWhp c))
  have hbr : brCTab rt = cTabWhp c := rfl
  -- `prog` reduces to the branch on the walk's result, at the unchanged state.
  set q := if wres.1 = 0 then pure dflt else leafProg (rt, wres.2.1)
  have hst : (Memory.spec 0).clientState s prog = (Memory.spec 0).clientState s q := by
    dsimp only [prog]; rw [clientState_bind, hrt_st, hrt_res, hbr, clientState_bind, hw_st]
  have hres : (Memory.spec 0).clientResult s prog = (Memory.spec 0).clientResult s q := by
    dsimp only [prog]; rw [clientResult_bind, hrt_st, hrt_res, hbr, clientResult_bind, hw_st]
  have hmc : memoryCost prog s = 2 * cTabWhp c + memoryCost q s := by
    dsimp only [prog]; simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
    rw [hrt_st, hrt_res, hrt_mc, hbr, hw_st, hw_mc, Nat.zero_add]
  have hvp (h : ValidProg w (base + largeSpaceWhp c U V w n_max) s q) :
      ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
    dsimp only [prog]
    refine validProg_bind hrt_vp ?_
    rw [hrt_st, hrt_res, hbr]
    exact validProg_bind hw_vp (by rw [hw_st]; exact h)
  refine ⟨fun hwk => ?_, fun leaf hwk => ?_⟩ <;> rw [hwk] at hw1
  · have hq : q = pure dflt := ite_eq_left (hw1 rfl)
    rw [hq] at hst hres hmc hvp
    exact ⟨hst, hres, hmc.trans (Nat.add_zero _), hvp (validProg_pure _)⟩
  · obtain ⟨_, hw_eq, hlf_lt⟩ := hw1 rfl
    have hq : q = leafProg (rt, leaf) :=
      (ite_eq_right (by rw [hw_eq]; exact one_ne_zero)).trans (by rw [hw_eq])
    rw [hq] at hst hres hmc hvp
    exact ⟨hlf_lt, hst, hres, hmc, hvp⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
