/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.BasicOps
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Consolidation
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Degree-indexed root consolidation and `extractMin` for a Fibonacci heap

This file proves the correctness, memory-safety, and `O(log |dom s| + 1)` amortized instruction
bound of `scatterRootCode` and `extractMinCode` in the current number of stored elements
`sz = (IndexedMinPQ.dom s).card` [Fredman and Tarjan][FredmanTarjan1987]
[Cormen et al., Section 19.2][CLRS2009].

The proofs step the machine code; the forest reasoning is that of the record heap
(`Cslib.DataStructure.PriorityQueue.FibonacciHeap`, `Consolidation.lean`), applied to the machine
state read as `RawState.ofData n base x`:

* **Root scattering (`scatterRootCode_exec`):** each collision step is `Placing.collide` followed
  by a link, which the machine performs as `LinksAs`; the final store into an empty slot is
  `Placing.place`. The result is `Consolidated`, and the step count satisfies
  `t + 50 * slotTrees'.length ≤ 63 + 50 * slotTrees.length`.
* **Minimum extraction (`extractMinCode_exec`):** `FibRawInv.detach` splits the heap at
  `z = minRoot - 1` (which agrees with `IndexedMinPQ.findMin`). The two scatter loops are driven by
  `Detached.scatterChildren`, `Scattering.unmark`/`step` and `Detached.scatterRoots`, the slot scan
  by `Detached.gathering` and `Gathering.take`, and `Detached.finish` rebuilds `FibRawInv`. The scan
  covers only `0 .. maxDeg`, at most `2 * Nat.log 2 (IndexedMinPQ.dom s).card + 2` slots, so
  `t + potential y ≤ 410 * (Nat.log 2 (IndexedMinPQ.dom s).card + 1) + potential x`.

## Main results

* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.scatterRootCode_exec`: amortized root
  scattering, as `Consolidated`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.extractMinCode_exec`:
  `O(log |dom s| + 1)` amortized `extractMin` specification in the current number of stored
  elements.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci Heaps and Their Uses in Improved Network Optimization
  Algorithms*][FredmanTarjan1987]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 19.2][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.FibonacciHeap hiding potential
open scoped Cslib.WordRAM

/-! ## Root scattering (`scatterBody_wp` and `scatterRootCode_exec`) -/

private abbrev scatterSwapBranch : Code .exact rFib :=
  ram_exact[
    if zeroP < s6 then [
      s6 ← s4;
      s4 ← s5;
      s5 ← s6
    ] else [
      s0 ← zeroP
    ]
  ]

private abbrev scatterLinkBranch : Code .exact rFib :=
  ram_exact[
    if s1 = zeroP then [
      s0 ← leftBase + s5;
      *s0 ← s5;
      s0 ← rightBase + s5;
      *s0 ← s5;
      s2 ← s5 + oneP;
      s0 ← childBase + s4;
      *s0 ← s2;
      s0 ← degBase + s4;
      *s0 ← oneP
    ] else [
      s0 ← childBase + s4;
      s6 ← *s0;
      s6 ← s6 - oneP;
      ⟪insertIntoNonEmptyList s6 s5⟫;
      s1 ← s1 + oneP;
      s0 ← degBase + s4;
      *s0 ← s1
    ]
  ]

private abbrev scatterBody : Code .exact rFib :=
  ram_exact[
    s5 ← s3 - oneP;
    s0 ← consBase + curDReg;
    *s0 ← zeroP;
    s0 ← baseReg + s4;
    s1 ← *s0;
    s0 ← baseReg + s5;
    s2 ← *s0;
    ⟪prioLTFlag s5 s2 s4 s1 s6⟫;
    ⟪scatterSwapBranch⟫;
    s1 ← s4 + oneP;
    s0 ← parBase + s5;
    *s0 ← s1;
    s0 ← degBase + s4;
    s1 ← *s0;
    ⟪scatterLinkBranch⟫;
    curDReg ← curDReg + oneP;
    s0 ← consBase + curDReg;
    s3 ← *s0
  ]

private theorem scatterRootCode_preserves :
    ∀ r : Fin rFib, r.val < 33 → scatterRootCode.Preserves r := by
  decide +kernel

private theorem scatterSwapBranch_wp {n base w curD : ℕ} {a : Data rFib}
    {st st₁ : RawState n} {T_cur T_slot : FHTree n}
    (hb : a.Bounded w) (hbr : BaseRegs n base a)
    (hst : RawState.ofData n base a = st₁)
    (hT_cur : ValidRoot st₁ none T_cur) (hT_slot : ValidRoot st₁ none T_slot)
    (hdeg_c : T_cur.deg = curD) (hdeg_s : T_slot.deg = curD)
    (hnd : (T_cur.nodes ++ T_slot.nodes).Nodup)
    (ha_s4 : a.regs s4 = T_cur.root.val) (ha_s5 : a.regs s5 = T_slot.root.val)
    (ha_cd : a.regs curDReg = curD)
    (ha_s6 : a.regs s6 = if IndexedMinPQ.PrioLT (T_slot.root, st.key T_slot.root)
        (T_cur.root, st.key T_cur.root) then 1 else 0)
    (hk_eq : st₁.key = st.key) :
    WP w scatterSwapBranch a fun a' t =>
      t ≤ 4 ∧ a'.Bounded w ∧ BaseRegs n base a' ∧ a'.mem = a.mem ∧
      a'.regs curDReg = curD ∧ RawState.ofData n base a' = st₁ ∧
      ∃ T₁ T₂ : FHTree n,
        ValidRoot st₁ none T₁ ∧ T₁.deg = curD ∧
        a'.regs s4 = T₁.root.val ∧ a'.regs s5 = T₂.root.val ∧
        ∀ {st₂ : RawState n}, LinksAs st₁ T₁.root T₂.root st₂ →
          Linked st₁ st₂ T_cur T_slot (.node T₁.root (T₁.children ++ [T₂])) := by
  have hfit := hbr.fits_of_le hb
  have hne : T_cur.root ≠ T_slot.root :=
    (List.nodup_append.mp hnd).2.2 _ T_cur.root_mem_nodes _ T_slot.root_mem_nodes
  have hlt_eq : IndexedMinPQ.PrioLT (T_slot.root, st₁.key T_slot.root)
      (T_cur.root, st₁.key T_cur.root) ↔
      IndexedMinPQ.PrioLT (T_slot.root, st.key T_slot.root) (T_cur.root, st.key T_cur.root) := by
    rw [hk_eq]
  refine WP.bounded hb ?_
  unfold scatterSwapBranch
  by_cases hlt54 : IndexedMinPQ.PrioLT (T_slot.root, st.key T_slot.root)
      (T_cur.root, st.key T_cur.root) <;>
    (wram_exec [hfit, hbr.regs_zeroP, ha_s4, ha_s5, ha_s6, hlt54]
     intro hb'
     refine ⟨by omega, hb', by wram_simp [BaseRegs.set_iff, hbr], rfl, by wram_simp [ha_cd],
       by wram_simp [ofData_set_scratch, hst], ?_⟩)
  · exact ⟨T_slot, T_cur, hT_slot, hdeg_s, by wram_simp, by wram_simp, fun hl =>
      (LinksAs.linked hT_slot hT_cur (List.perm_append_comm.nodup_iff.mp hnd)
        (hdeg_s.trans hdeg_c.symm) (hlt_eq.mpr hlt54) hl).symm (hdeg_c.trans hdeg_s.symm)⟩
  · have hlt45 := (IndexedMinPQ.prioLT_or_prioLT_of_ne hne (st₁.key T_cur.root)
      (st₁.key T_slot.root)).resolve_right (hlt_eq.not.mpr hlt54)
    exact ⟨T_cur, T_slot, hT_cur, hdeg_c, by wram_simp [ha_s4], by wram_simp [ha_s5], fun hl =>
      LinksAs.linked hT_cur hT_slot hnd (hdeg_c.trans hdeg_s.symm) hlt45 hl⟩

private theorem scatterLinkBranch_wp {n base w curD : ℕ} {a : Data rFib}
    {st₁ : RawState n} {T₁ T₂ : FHTree n}
    (hb : a.Bounded w) (hbr : BaseRegs n base a)
    (hT₁ : ValidRoot st₁ none T₁) (hd₁ : T₁.deg = curD) (hd_lt : curD + 1 ≤ n)
    (ha_s4 : a.regs s4 = T₁.root.val) (ha_s5 : a.regs s5 = T₂.root.val)
    (ha_cd : a.regs curDReg = curD) (ha_s1 : a.regs s1 = curD)
    (hst : RawState.ofData n base a =
      { st₁ with par := Function.update st₁.par T₂.root (T₁.root.val + 1) }) :
    WP w scatterLinkBranch a fun a' t =>
      t ≤ 18 ∧ a'.Bounded w ∧ BaseRegs n base a' ∧
      Modifies (Block.mk base (space n)).footprint a.mem a'.mem ∧
      a'.regs s4 = T₁.root.val ∧ a'.regs curDReg = curD ∧
      LinksAs st₁ T₁.root T₂.root (RawState.ofData n base a') := by
  have hfit := hbr.fits_of_le hb
  have hw1_lt := T₁.root.isLt
  have hw2_lt := T₂.root.isLt
  have hdeg_w1 : st₁.deg T₁.root = curD := (ValidSubtree.deg_root hT₁.1).trans hd₁
  refine WP.bounded hb ?_
  unfold scatterLinkBranch
  by_cases hd0 : curD = 0
  · wram_exec [hfit, hbr.regs_leftBase, hbr.regs_rightBase, hbr.regs_childBase,
      hbr.regs_degBase, hbr.regs_zeroP, hbr.regs_oneP, ha_s4, ha_s5, ha_s1, hd0]
    intro hb5
    refine ⟨by omega, hb5, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr],
      Modifies.block_iff.2 fun addr haddr => by have := out_of_footprint n base haddr; wram_simp,
      by wram_simp [ha_s4], by wram_simp [ha_cd], Or.inl ⟨hdeg_w1.trans hd0, ?_⟩⟩
    wram_simp [ofData_write_deg, ofData_write_child, ofData_write_right, ofData_write_left,
      ofData_set_scratch, hst]
  · obtain ⟨h_c, r_c, hcw1_eq, hr_c⟩ := ValidSubtree.exists_child hT₁.1
      (by rw [ValidSubtree.deg_root hT₁.1]; exact fun h => hd0 (hd₁.symm.trans h))
    have hhc_lt := h_c.isLt
    have hcw1_mem : a.mem (base + 2 * n + T₁.root.val) = h_c.val + 1 :=
      (congrFun (congrArg RawState.child hst) T₁.root).trans hcw1_eq
    wram_exec [hfit, hbr.regs_childBase, hbr.regs_zeroP, hbr.regs_oneP, ha_s4, ha_s1,
      hcw1_mem, hd0]
    have hst_q1 : RawState.ofData n base
        (((a.set s0 (base + 2 * n + T₁.root.val)).set s6 (h_c.val + 1)).set s6 h_c.val) =
        { st₁ with par := Function.update st₁.par T₂.root (T₁.root.val + 1) } := by
      wram_simp [ofData_set_scratch, hst]
    wram_call (insertIntoNonEmptyList_exec (w := w) (base := base) (hReg := s6) (uReg := s5)
        (h := h_c) (u := T₂.root) (r := r_c) (by wram_bounded <;> exact hfit _ (by omega))
        (by wram_simp [BaseRegs.set_iff, hbr])
        (by decide) (by decide) (by decide) (by decide)
        (by wram_simp) (by wram_simp [ha_s5]) (by rw [hst_q1]; exact hr_c))
      with q2 ⟨hbr_q2, hmod_q2, hst_q2⟩
    have hq2_s1 : q2.regs s1 = curD := by regs_frame
    have hq2_s4 : q2.regs s4 = T₁.root.val := by regs_frame
    have hq2_cd : q2.regs curDReg = curD := by regs_frame
    refine WP.bounded (‹ExecWithin _ _ _ q2 _›.bounded
      (by wram_bounded <;> exact hfit _ (by omega))) ?_
    wram_exec [hfit, hbr_q2.regs_degBase, hbr_q2.regs_oneP, hq2_s1, hq2_s4]
    intro hb5 _
    refine ⟨by omega, hb5, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr_q2],
      modifies_block_trans hmod_q2
        (Modifies.write_of_owns (owns_arr_addr (k := 5) (by decide) hw1_lt) _),
      by wram_simp [hq2_s4], by wram_simp [hq2_cd],
      Or.inr ⟨h_c, r_c, fun h => hd0 (hdeg_w1.symm.trans h), hcw1_eq, hr_c, ?_⟩⟩
    rw [hst_q1] at hst_q2
    wram_simp [ofData_write_deg, ofData_set_scratch, hst_q2, hdeg_w1]

/-- Single collision step of `scatterRootCode`: clears `cons[curD]`, links the tree `T_cur` in
`s4` with the table's tree of the same degree (the one that precedes becomes the parent), and
advances `curD`, in `≤ 43` steps. -/
private theorem scatterBody_wp {n sz base w maxDeg curD : ℕ} {a : Data rFib}
    {T_cur : FHTree n} {slotTrees : List (FHTree n)} {z : Fin n}
    (hb : a.Bounded w) (hbr : BaseRegs n base a)
    (hP : Placing sz z (RawState.ofData n base a) T_cur slotTrees maxDeg)
    (hcur_deg : T_cur.deg = curD) (ha_s4 : a.regs s4 = T_cur.root.val)
    (ha_curD : a.regs curDReg = curD) (ha_s3 : a.regs s3 = (RawState.ofData n base a).cons curD)
    (hcond : (Cond.lt zeroP s3).Holds a) :
    WP w scatterBody a fun a' t =>
      t ≤ 43 ∧ ∃ T_next slotTrees',
        a'.Bounded w ∧ BaseRegs n base a' ∧
        Modifies (Block.mk base (space n)).footprint a.mem a'.mem ∧
        slotTrees'.length + 1 = slotTrees.length ∧
        T_next.deg = curD + 1 ∧ a'.regs s4 = T_next.root.val ∧
        a'.regs curDReg = curD + 1 ∧
        a'.regs s3 = (RawState.ofData n base a').cons (curD + 1) ∧
        Placing sz z (RawState.ofData n base a') T_next slotTrees' maxDeg ∧
        ∀ {st' : RawState n} {slots' : List (FHTree n)} {md' : ℕ},
          Consolidated sz (RawState.ofData n base a') st'
            (forestNodes (T_next :: slotTrees')) slots' md' →
          Consolidated sz (RawState.ofData n base a) st'
            (forestNodes (T_cur :: slotTrees)) slots' md' := by
  set st := RawState.ofData n base a with hst_def
  have hfit := hbr.fits_of_le hb
  have hd_le_n : curD ≤ n := by have := hcur_deg ▸ hP.deg_bounds; omega
  have hd1_le_n : curD + 1 ≤ n := by have := hcur_deg ▸ hP.deg_bounds; omega
  have hcons_pos : 0 < st.cons curD := by rwa [Cond.Holds, hbr.regs_zeroP, ha_s3] at hcond
  rcases hP.table.lookup hd_le_n with ⟨hc0, _⟩ |
      ⟨idx, hidx, hslot_deg, hcons_eq, hlen_er, hno_other⟩
  · omega
  have hu4_lt := T_cur.root.isLt
  have hu5_lt := slotTrees[idx].root.isLt
  let st₁ : RawState n := { st with cons := Function.update st.cons curD 0 }
  obtain ⟨hT_cur1, hT_slot1, hnd_pair, hnext⟩ := hP.collide (st₁ := st₁)
    hidx (hslot_deg.trans hcur_deg.symm) (fun R hR => hcur_deg ▸ hno_other R hR)
    (by rw [hcur_deg])
  have hs3_eq : a.regs s3 = slotTrees[idx].root.val + 1 := ha_s3.trans hcons_eq
  have hku4 : a.mem (base + T_cur.root.val) = st.key T_cur.root := rfl
  have hku5 : a.mem (base + slotTrees[idx].root.val) = st.key slotTrees[idx].root := rfl
  refine WP.bounded hb ?_
  wram_exec [scatterBody, hfit, hbr.regs_consBase, hbr.regs_baseReg, hbr.regs_zeroP, hbr.regs_oneP,
    hs3_eq, ha_curD, ha_s4, hku4, hku5]
  wram_call (@prioLTFlag_exec n base) [BaseRegs.set_iff, BaseRegs.write_iff, hbr]
  wram_call (scatterSwapBranch_wp (w := w) (base := base) (st := st) (st₁ := st₁)
      (by wram_bounded <;> exact hfit _ (by (try split_ifs) <;> omega))
      (by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr])
      (by wram_simp [st₁, ofData_write_cons hd_le_n, ofData_set_scratch, ← hst_def])
      hT_cur1 hT_slot1 hcur_deg hslot_deg hnd_pair
      (by wram_simp [ha_s4]) (by wram_simp) (by wram_simp [ha_curD])
      (by wram_simp [ha_s4]; rfl) rfl)
    with a3 t3 ⟨ht3, hb3, hbr3, hmem3, ha3_cd, hst3, T₁, T₂, hT₁, hd₁, ha3_s4, ha3_s5, hlinked⟩
  have hmod3 : Modifies (Block.mk base (space n)).footprint a.mem a3.mem := by
    rw [hmem3]; exact Modifies.write_of_owns (owns_cons_addr hd_le_n) 0
  have hw1_lt := T₁.root.isLt
  have hw2_lt := T₂.root.isLt
  have hdw1_mem : a3.mem (base + 5 * n + T₁.root.val) = curD :=
    (congrFun (congrArg RawState.deg hst3) T₁.root).trans ((ValidSubtree.deg_root hT₁.1).trans hd₁)
  wram_exec -split [hfit, hbr3.regs_parBase, hbr3.regs_degBase, hbr3.regs_oneP, ha3_s4, ha3_s5,
    hdw1_mem]
  wram_call (scatterLinkBranch_wp (w := w) (base := base) (T₂ := T₂)
      (by wram_bounded <;> exact hfit _ (by omega))
      (by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr3]) hT₁ hd₁ hd1_le_n
      (by wram_simp [ha3_s4]) (by wram_simp [ha3_s5])
      (by wram_simp [ha3_cd]) (by wram_simp)
      (by wram_simp [ofData_write_par, ofData_set_scratch, hst3]))
    with a5 t5 ⟨ht5, hb5, hbr5, hmod5, ha5_s4, ha5_cd, hlink5⟩
  have hown_w2 : (Block.mk base (space n)).Owns (base + n + T₂.root.val) := by
    dsimp only [Block.Owns, space]; omega
  have hL := hlinked hlink5
  obtain ⟨hP_next, hback⟩ := hnext hL
  have hm_c1 : a5.mem (base + 8 * n + (curD + 1)) =
      (RawState.ofData n base a5).cons (curD + 1) := by
    simp only [RawState.ofData, hd1_le_n, ↓reduceIte]
  refine WP.bounded hb5 ?_
  wram_exec [hfit, hbr5.regs_consBase, hbr5.regs_oneP, ha5_cd, hm_c1]
  intro hb6 _
  refine ⟨by omega, .node T₁.root (T₁.children ++ [T₂]), slotTrees.eraseIdx idx, hb6,
    by wram_simp [BaseRegs.set_iff, hbr5],
    modifies_block_trans hmod3 (modifies_block_trans (Modifies.write_of_owns hown_w2 _) hmod5),
    hlen_er,
    hL.deg.trans (by rw [hcur_deg]), by wram_simp [ha5_s4, FHTree.root_node], by wram_simp,
    by wram_simp [ofData_set_scratch],
    by wram_simp [ofData_set_scratch]; exact hP_next,
    fun hc => hback (by wram_simp [ofData_set_scratch] at hc; exact hc)⟩

/-- Full `while zeroP < s3 do scatterBody` loop by induction on `slotTrees.length`: it stops at an
empty slot `curD_f`, holding `Placing` for the final tree `T_f`, in
`t + 50 * slotTrees_f.length ≤ 2 + 50 * slotTrees.length` instructions. -/
private theorem scatterLoop_exec {n sz base w maxDeg : ℕ} {z : Fin n}
    (k : ℕ) {a : Data rFib} {T_cur : FHTree n} {slotTrees : List (FHTree n)} {curD : ℕ}
    (hk : slotTrees.length = k) (hb : a.Bounded w) (hbr : BaseRegs n base a)
    (hP : Placing sz z (RawState.ofData n base a) T_cur slotTrees maxDeg)
    (hcd : T_cur.deg = curD) (hs4 : a.regs s4 = T_cur.root.val)
    (hcd_r : a.regs curDReg = curD) (hs3 : a.regs s3 = (RawState.ofData n base a).cons curD) :
    WP w (.loop (.lt zeroP s3) scatterBody) a fun z_lp t =>
      ∃ T_f slotTrees_f curD_f,
        t + slotCredit * slotTrees_f.length ≤ 2 + slotCredit * slotTrees.length ∧
        ¬(Cond.lt zeroP s3).Holds z_lp ∧ z_lp.Bounded w ∧ BaseRegs n base z_lp ∧
        Modifies (Block.mk base (space n)).footprint a.mem z_lp.mem ∧
        T_f.deg = curD_f ∧ z_lp.regs s4 = T_f.root.val ∧ z_lp.regs curDReg = curD_f ∧
        z_lp.regs s3 = (RawState.ofData n base z_lp).cons curD_f ∧
        Placing sz z (RawState.ofData n base z_lp) T_f slotTrees_f maxDeg ∧
        ∀ {st' : RawState n} {slots' : List (FHTree n)} {md' : ℕ},
          Consolidated sz (RawState.ofData n base z_lp) st' (forestNodes (T_f :: slotTrees_f))
            slots' md' →
          Consolidated sz (RawState.ofData n base a) st' (forestNodes (T_cur :: slotTrees))
            slots' md' := by
  by_cases hc : (Cond.lt zeroP s3).Holds a
  · obtain ⟨a', t1, he1, ht1, T_next, slotTrees', hb', hbr', hmod1, hlen_er, hdeg1, hs4_1, hcd1,
      hs3_1, hP1, hback1⟩ := scatterBody_wp hb hbr hP hcd hs4 hcd_r hs3 hc
    cases k with
    | zero => omega
    | succ k =>
      obtain ⟨z_lp, t₂, he2, T_f, slotTrees_f, curD_f, ht2, hnc, hbz, hbrz, hmod2, hdeg2,
        hs4_2, hcd2, hs3_2, hP2, hback2⟩ :=
        scatterLoop_exec k (by omega) hb' hbr' hP1 hdeg1 hs4_1 hcd1 hs3_1
      exact ⟨z_lp, t1 + t₂ + 2, ExecWithin.loop_iter hc he1 he2, T_f, slotTrees_f, curD_f,
        by dsimp only [slotCredit] at ht2 ⊢; omega, hnc, hbz, hbrz,
        modifies_block_trans hmod1 hmod2, hdeg2, hs4_2, hcd2, hs3_2, hP2,
        fun hc' => hback1 (hback2 hc')⟩
  · exact ⟨a, 2, ExecWithin.loop_exit hc, T_cur, slotTrees, curD, by omega, hc, hb, hbr,
      Modifies.refl _ _, hcd, hs4, hcd_r, hs3, hP, fun h => h⟩

/-- `scatterRootCode` places the valid root tree `T₀` (`iterCur = T₀.root.val`) into the
consolidation table, linking equal-degree roots and updating `maxDegReg`: the result is
`Consolidated`, in `t + 50 * slotTrees'.length ≤ 63 + 50 * slotTrees₀.length` instructions, and
all registers `< 33` are preserved. -/
theorem scatterRootCode_exec {n sz base w maxDeg₀ : ℕ} {x : Data rFib}
    {T₀ : FHTree n} {slotTrees₀ : List (FHTree n)} {z : Fin n}
    (hb : x.Bounded w) (hbr : BaseRegs n base x)
    (hP : Placing sz z (RawState.ofData n base x) T₀ slotTrees₀ maxDeg₀)
    (hx_ic : x.regs iterCur = T₀.root.val)
    (hx_md : x.regs maxDegReg = maxDeg₀) :
    ∃ y slotTrees' maxDeg' t,
      ExecWithin w scatterRootCode x y t ∧
      t + slotCredit * slotTrees'.length ≤ 63 + slotCredit * slotTrees₀.length ∧
      y.Bounded w ∧ BaseRegs n base y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      (∀ r : Fin rFib, r.val < 33 → y.regs r = x.regs r) ∧
      y.regs maxDegReg = maxDeg' ∧
      Consolidated sz (RawState.ofData n base x) (RawState.ofData n base y)
        (forestNodes (T₀ :: slotTrees₀)) slotTrees' maxDeg' := by
  set st := RawState.ofData n base x with hst_def
  have hfit := hbr.fits_of_le hb
  have hu0_lt := T₀.root.isLt
  have hd0_le_n : T₀.deg ≤ n := by have := hP.deg_bounds; omega
  have hm_du0 : x.mem (base + 5 * n + T₀.root.val) = T₀.deg := ValidSubtree.deg_root hP.valid.1
  have hm_cd0 : x.mem (base + 8 * n + T₀.deg) = st.cons T₀.deg := by
    simp only [st, RawState.ofData, hd0_le_n, ↓reduceIte]
  suffices hwp : WP w scatterRootCode x fun y t => ∃ slotTrees' maxDeg',
      t + slotCredit * slotTrees'.length ≤ 63 + slotCredit * slotTrees₀.length ∧
      y.Bounded w ∧ BaseRegs n base y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      y.regs maxDegReg = maxDeg' ∧
      Consolidated sz st (RawState.ofData n base y)
        (forestNodes (T₀ :: slotTrees₀)) slotTrees' maxDeg' by
    obtain ⟨y, t, he, slotTrees', maxDeg', ht, hby, hbry, hmod, hymd, hc⟩ := hwp
    exact ⟨y, slotTrees', maxDeg', t, he, ht, hby, hbry, hmod,
      fun r hr => he.regs_eq (scatterRootCode_preserves r hr), hymd, hc⟩
  wram_exec [scatterRootCode, hfit, hbr.regs_degBase, hbr.regs_consBase, hx_ic, hm_du0, hm_cd0]
  have hst1 : RawState.ofData n base
      (((((x.set s4 T₀.root.val).set s0 (base + 5 * n + T₀.root.val)).set curDReg T₀.deg).set s0
        (base + 8 * n + T₀.deg)).set s3 (st.cons T₀.deg)) = st := by
    wram_simp [ofData_set_scratch, ← hst_def]
  wram_call (scatterLoop_exec (w := w) slotTrees₀.length rfl
      (by have : Fits w (st.cons T₀.deg) := hm_cd0 ▸ hb.2 _
          wram_bounded <;> exact hfit _ (by omega))
      (by wram_simp [BaseRegs.set_iff, hbr])
      (hst1 ▸ hP) rfl (by wram_simp) (by wram_simp) (by wram_simp [hst1]))
    with z_lp t_lp ⟨T_f, slotTrees_f, curD_f, ht_lp, hnc_lp, hbz, hbrz, hmod_lp,
      hdeg_f, hs4_lp, hcd_lp, hs3_lp, hP_f, hback⟩
  have hmd_lp : z_lp.regs maxDegReg = maxDeg₀ := by regs_frame
  have hdf_le_n : curD_f ≤ n := by have := hdeg_f ▸ hP_f.deg_bounds; omega
  have hcons_f_zero : (RawState.ofData n base z_lp).cons curD_f = 0 := by
    rw [Cond.Holds, hbrz.regs_zeroP, hs3_lp] at hnc_lp; omega
  have hnone_f : ∀ R ∈ slotTrees_f, R.deg ≠ curD_f := by
    rcases hP_f.table.lookup hdf_le_n with ⟨_, hnone⟩ | ⟨_, _, _, hce, _, _⟩
    · exact hnone
    · omega
  have huf_lt := T_f.root.isLt
  refine WP.bounded hbz ?_
  wram_exec [hfit, hbrz.regs_consBase, hbrz.regs_zeroP, hbrz.regs_oneP, hs4_lp, hcd_lp, hmd_lp]
  all_goals
    intro hby
    refine ⟨T_f :: slotTrees_f, max maxDeg₀ curD_f,
      by simp only [List.length_cons, slotCredit] at ht_lp ⊢; omega,
      hby, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbrz],
      modifies_block_trans hmod_lp (Modifies.write_of_owns (owns_cons_addr hdf_le_n) _),
      by wram_simp [hmd_lp, hcd_lp]; omega, ?_⟩
    wram_simp [ofData_write_cons hdf_le_n, ofData_set_scratch]
    exact hst1 ▸ hback (hdeg_f ▸ hP_f.place (hdeg_f ▸ hnone_f))

/-! ## Consolidation scatter loops (`childScatterLoop` and `rootScatterLoop`) -/

private abbrev scatterTail : Code .exact rFib :=
  ram_exact[
    ⟪scatterRootCode⟫;
    iterCur ← iterNxt;
    remReg ← remReg - oneP
  ]

private abbrev childScatterBody : Code .exact rFib :=
  ram_exact[
    s0 ← rightBase + iterCur;
    iterNxt ← *s0;
    s0 ← parBase + iterCur;
    *s0 ← zeroP;
    s0 ← markBase + iterCur;
    s1 ← *s0;
    if zeroP < s1 then [
      *s0 ← zeroP;
      numMarkedReg ← numMarkedReg - oneP
    ] else [
      s0 ← zeroP
    ];
    ⟪scatterTail⟫
  ]

private abbrev childScatterLoop : Code .exact rFib :=
  .loop (.lt zeroP remReg) childScatterBody

private abbrev rootScatterBody : Code .exact rFib :=
  ram_exact[
    s0 ← rightBase + iterCur;
    iterNxt ← *s0;
    ⟪scatterTail⟫
  ]

private abbrev rootScatterLoop : Code .exact rFib :=
  .loop (.lt zeroP remReg) rootScatterBody

private theorem rootScatterLoop_preserves :
    ∀ r : Fin rFib, r.val < 30 → rootScatterLoop.Preserves r := by
  decide +kernel

/-- Common step postcondition for the scatter-list loop bodies (`prep = true` for children,
`prep = false` for remaining roots). -/
private abbrev ScatterStepPost {n : ℕ} (sz base w : ℕ) (z : Fin n) (prep : Bool)
    (a : Data rFib) (T_u : FHTree n) (slotTrees tl : List (FHTree n)) (cost : ℕ)
    (a_next : Data rFib) (t : ℕ) : Prop :=
  ∃ slotTrees_1 maxDeg_1,
    t + slotCredit * slotTrees_1.length ≤ cost + slotCredit * slotTrees.length ∧
    a_next.Bounded w ∧ BaseRegs n base a_next ∧
    Modifies (Block.mk base (space n)).footprint a.mem a_next.mem ∧
    a_next.regs remReg = tl.length ∧ a_next.regs maxDegReg = maxDeg_1 ∧
    (∀ y ∈ (tl.map FHTree.root).head?, a_next.regs iterCur = y.val) ∧
    Scattering sz z prep (RawState.ofData n base a_next) slotTrees_1 tl maxDeg_1 ∧
    ∀ {st' : RawState n} {slots' : List (FHTree n)} {md' : ℕ},
      Consolidated sz (RawState.ofData n base a_next) st'
        (forestNodes (slotTrees_1 ++ tl)) slots' md' →
      Consolidated sz (RawState.ofData n base a) st'
        (forestNodes (slotTrees ++ (T_u :: tl))) slots' md'

/-- Shared tail of `childScatterBody` and `rootScatterBody`: runs `scatterRootCode`, then advances
`iterCur ← iterNxt` and decrements `remReg`. -/
private theorem scatterTail_wp {n sz base w : ℕ} {z : Fin n} {prep : Bool}
    {a : Data rFib} {T_u : FHTree n} {tl slotTrees : List (FHTree n)} {maxDeg : ℕ}
    (hb : a.Bounded w) (hbr : BaseRegs n base a)
    (h : Scattering sz z prep (RawState.ofData n base a) slotTrees (T_u :: tl) maxDeg)
    (hTu : ValidRoot (RawState.ofData n base a) none T_u)
    (ha_ic : a.regs iterCur = T_u.root.val) (ha_md : a.regs maxDegReg = maxDeg)
    (ha_rem : a.regs remReg = tl.length + 1)
    (ha_nxt : a.regs iterNxt = (RawState.ofData n base a).right T_u.root) :
    WP w scatterTail a (ScatterStepPost sz base w z prep a T_u slotTrees tl 65) := by
  obtain ⟨a_sc, slotTrees_1, maxDeg_1, t_sc, he_sc, ht_sc, hb_sc, hbr_sc, hmod_sc, _,
    hmd_sc, hc₁⟩ := scatterRootCode_exec hb hbr (h.placing hTu) ha_ic ha_md
  obtain ⟨h₂, hback₂⟩ := h.step hc₁
  have hsc_nxt : a_sc.regs iterNxt = (RawState.ofData n base a).right T_u.root := by regs_frame
  have hsc_rem : a_sc.regs remReg = tl.length + 1 := by regs_frame
  have hfit_rem : Fits w tl.length := (hsc_rem ▸ hb_sc.1 remReg).of_le (by omega)
  unfold scatterTail
  refine WP.seq (WP.of_execWithin he_sc (WP.bounded hb_sc ?_))
  wram_exec [hfit_rem, hbr_sc.regs_oneP, hsc_nxt, hsc_rem]
  intro hb_next
  exact ⟨slotTrees_1, maxDeg_1, by omega, hb_next,
    by wram_simp [BaseRegs.set_iff, hbr_sc], hmod_sc,
    by wram_simp, by wram_simp [hmd_sc],
    fun y hy => by wram_simp; exact RightChain.right_head h.chain y hy,
    by wram_simp [ofData_set_scratch]; exact h₂,
    fun hc' => hback₂ (by wram_simp [ofData_set_scratch] at hc'; exact hc')⟩

/-- Generic induction driving both `childScatterLoop` (`prep = true`) and `rootScatterLoop`
(`prep = false`). -/
private theorem scatterListLoop_exec {n sz base w : ℕ} {z : Fin n}
    (prep : Bool) (body : Code .exact rFib) (stepCost : ℕ)
    (hstep : ∀ {T_u : FHTree n} {tl slotTrees : List (FHTree n)} {maxDeg : ℕ} {a : Data rFib},
      a.Bounded w → BaseRegs n base a →
      Scattering sz z prep (RawState.ofData n base a) slotTrees (T_u :: tl) maxDeg →
      a.regs remReg = tl.length + 1 → a.regs maxDegReg = maxDeg →
      a.regs iterCur = T_u.root.val →
      WP w body a (ScatterStepPost sz base w z prep a T_u slotTrees tl stepCost)) :
    ∀ (rest : List (FHTree n)) (a : Data rFib) (slotTrees : List (FHTree n)) (maxDeg : ℕ),
      a.Bounded w → BaseRegs n base a →
      Scattering sz z prep (RawState.ofData n base a) slotTrees rest maxDeg →
      a.regs remReg = rest.length → a.regs maxDegReg = maxDeg →
      (∀ y ∈ (rest.map FHTree.root).head?, a.regs iterCur = y.val) →
      WP w (.loop (.lt zeroP remReg) body) a fun b t =>
        ∃ slotTrees' maxDeg',
          t + slotCredit * slotTrees'.length ≤
            2 + (stepCost + 2) * rest.length + slotCredit * slotTrees.length ∧
          b.Bounded w ∧ BaseRegs n base b ∧
          Modifies (Block.mk base (space n)).footprint a.mem b.mem ∧
          b.regs maxDegReg = maxDeg' ∧
          Consolidated sz (RawState.ofData n base a) (RawState.ofData n base b)
            (forestNodes (slotTrees ++ rest)) slotTrees' maxDeg'
  | [], a, slotTrees, maxDeg, hb, hbr, h, hrem, hmd, _ => by
    have hc : ¬(Cond.lt zeroP remReg).Holds a := by
      simp only [Cond.Holds, hbr.regs_zeroP, hrem, List.length_nil, Nat.lt_irrefl,
        not_false_eq_true]
    exact ⟨a, 2, ExecWithin.loop_exit hc, slotTrees, maxDeg, by omega, hb, hbr,
      Modifies.refl _ _, hmd, h.done⟩
  | T_u :: tl, a, slotTrees, maxDeg, hb, hbr, h, hrem, hmd, hic => by
    have hc : (Cond.lt zeroP remReg).Holds a := by
      simp only [Cond.Holds, hbr.regs_zeroP, hrem, List.length_cons]; omega
    obtain ⟨a_next, t_b, he_b, slotTrees_1, maxDeg_1, ht_b, hb_next, hbr_next, hmod_b,
      hrem_next, hmd_next, hic_next, h₂, hback_b⟩ :=
      hstep hb hbr h (by simpa only [List.length_cons] using hrem) hmd (hic T_u.root rfl)
    obtain ⟨b, t_tl, he_tl, slotTrees', maxDeg', ht_tl, hb_b, hbr_b, hmod_tl, hmd_b, hc'⟩ :=
      scatterListLoop_exec prep body stepCost hstep tl a_next slotTrees_1 maxDeg_1
        hb_next hbr_next h₂ hrem_next hmd_next hic_next
    exact ⟨b, t_b + t_tl + 2, ExecWithin.loop_iter hc he_b he_tl, slotTrees', maxDeg',
      by simp only [List.length_cons, Nat.mul_succ] at ht_tl ⊢; omega,
      hb_b, hbr_b, modifies_block_trans hmod_b hmod_tl, hmd_b, hback_b hc'⟩

private theorem childScatterBody_wp {n sz base w : ℕ} {z : Fin n}
    {T_u : FHTree n} {tl slotTrees : List (FHTree n)} {maxDeg : ℕ} {a : Data rFib}
    (hb : a.Bounded w) (hbr : BaseRegs n base a)
    (h : Scattering sz z true (RawState.ofData n base a) slotTrees (T_u :: tl) maxDeg)
    (hrem : a.regs remReg = tl.length + 1) (hmd : a.regs maxDegReg = maxDeg)
    (hu_ic : a.regs iterCur = T_u.root.val) :
    WP w childScatterBody a (ScatterStepPost sz base w z true a T_u slotTrees tl 74) := by
  set st := RawState.ofData n base a with hst_def
  have hfit := hbr.fits_of_le hb
  have hu_lt := T_u.root.isLt
  have hu_in := h.inHeap _ (List.mem_append_left _ T_u.root_mem_nodes)
  have hu_mk_le := ValidSubtree.mark_root_le (h.valid T_u List.mem_cons_self)
  have hnm_le : st.numMarked ≤ n := h.numMarked ▸ markedCount_le_n st
  obtain ⟨h₁, hT₁, hsc₁⟩ := h.unmark
  have hm_r : a.mem (base + 4 * n + T_u.root.val) = st.right T_u.root := rfl
  have hm_mk : a.mem (base + 6 * n + T_u.root.val) = st.mark T_u.root := rfl
  have hnm_reg : a.regs numMarkedReg = st.numMarked := rfl
  wram_exec -split [childScatterBody, hfit, hbr.regs_rightBase, hbr.regs_parBase, hbr.regs_markBase,
    hbr.regs_zeroP, hu_ic, hm_r, hm_mk]
  refine WP.cut (fun a_mid t_m => t_m ≤ 3 ∧ a_mid.Bounded w ∧ BaseRegs n base a_mid ∧
      Modifies (Block.mk base (space n)).footprint a.mem a_mid.mem ∧
      a_mid.regs iterCur = T_u.root.val ∧ a_mid.regs iterNxt = st.right T_u.root ∧
      a_mid.regs remReg = tl.length + 1 ∧ a_mid.regs maxDegReg = maxDeg ∧
      RawState.ofData n base a_mid = unmarkState st T_u.root)
    (WP.bounded (by
      have : Fits w (st.right T_u.root) := hm_r ▸ hb.2 _
      have : Fits w (st.mark T_u.root) := hm_mk ▸ hb.2 _
      wram_bounded <;> exact hfit _ (by omega)) ?_) ?_
  · by_cases hmk_pos : 0 < st.mark T_u.root
    · have hnm_pos : 1 ≤ st.numMarked := h.numMarked ▸ Finset.card_pos.mpr
        ⟨T_u.root, by simp [markedSet, hu_in, hmk_pos.ne']⟩
      have hmk1 : st.mark T_u.root = 1 := by omega
      wram_exec [hfit, hbr.regs_zeroP, hbr.regs_oneP, hnm_reg, hmk_pos]
      intro hb_mid
      refine ⟨by omega, hb_mid, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr],
        Modifies.block_iff.2 fun addr haddr => by have := out_of_footprint n base haddr; wram_simp,
        by wram_simp [hu_ic], by wram_simp, by wram_simp [hrem], by wram_simp [hmd], ?_⟩
      wram_simp [unmarkState, hmk1, ofData_set_numMarked, ofData_write_mark, ofData_write_par,
        ofData_set_scratch, ← hst_def]
    · have hmk0 : st.mark T_u.root = 0 := by omega
      have hupd : Function.update st.mark T_u.root 0 = st.mark := hmk0 ▸ Function.update_eq_self _ _
      wram_exec [hfit, hbr.regs_zeroP, hmk0]
      intro hb_mid
      refine ⟨by omega, hb_mid, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr],
        Modifies.block_iff.2 fun addr haddr => by have := out_of_footprint n base haddr; wram_simp,
        by wram_simp [hu_ic], by wram_simp, by wram_simp [hrem], by wram_simp [hmd], ?_⟩
      wram_simp [unmarkState, hmk0, Nat.sub_zero, hupd, ofData_write_par, ofData_set_scratch,
        ← hst_def]
  rintro a_mid t_m ⟨ht_m, hb_mid, hbr_mid, hmod_mid, hmid_ic, hmid_nxt, hmid_rem, hmid_md, hst_mid⟩
  obtain ⟨a_next, t_s, he_s, s1, md1, ht_s, hb_n, hbr_n, hmod_s, hrem_n, hmd_n, hic_n, h₂,
    hback⟩ := scatterTail_wp hb_mid hbr_mid (hst_mid ▸ h₁) (hst_mid ▸ hT₁) hmid_ic hmid_md
      hmid_rem (hst_mid ▸ hmid_nxt)
  exact WP.of_execWithin he_s ⟨s1, md1, by omega, hb_n, hbr_n,
    modifies_block_trans hmod_mid hmod_s, hrem_n, hmd_n, hic_n, h₂,
    fun hc' => (hst_mid ▸ hback hc').pre hsc₁ (.refl _)⟩

private theorem rootScatterBody_wp {n sz base w : ℕ} {z : Fin n}
    {T_u : FHTree n} {tl slotTrees : List (FHTree n)} {maxDeg : ℕ} {a : Data rFib}
    (hb : a.Bounded w) (hbr : BaseRegs n base a)
    (h : Scattering sz z false (RawState.ofData n base a) slotTrees (T_u :: tl) maxDeg)
    (hrem : a.regs remReg = tl.length + 1) (hmd : a.regs maxDegReg = maxDeg)
    (hu_ic : a.regs iterCur = T_u.root.val) :
    WP w rootScatterBody a (ScatterStepPost sz base w z false a T_u slotTrees tl 67) := by
  have hfit := hbr.fits_of_le hb
  have hu_lt := T_u.root.isLt
  have hm_r : a.mem (base + 4 * n + T_u.root.val) = (RawState.ofData n base a).right T_u.root := rfl
  unfold rootScatterBody
  refine WP.seq (WP.exactBin hbr.regs_rightBase hu_ic rfl (hfit _ (by omega))
    (WP.seq (WP.load (by wram_simp) hm_r ?_)))
  have hst1 : RawState.ofData n base
      ((a.set s0 (base + 4 * n + T_u.root.val)).set iterNxt
        ((RawState.ofData n base a).right T_u.root)) = RawState.ofData n base a := by
    wram_simp [ofData_set_scratch]
  wram_call (scatterTail_wp (w := w) (base := base)
      (by have : Fits w ((RawState.ofData n base a).right T_u.root) := hm_r ▸ hb.2 _
          wram_bounded; exact hfit _ (by omega))
      (by wram_simp [BaseRegs.set_iff, hbr])
      (hst1 ▸ h) (hst1 ▸ h.validRoot)
      (by wram_simp [hu_ic]) (by wram_simp [hmd])
      (by wram_simp [hrem]) (by wram_simp [hst1]))
    with a_next t_s ⟨s1, md1, ht_s, hb_n, hbr_n, hmod_s, hrem_n, hmd_n, hic_n, h₂, hback⟩
  exact ⟨s1, md1, by omega, hb_n, hbr_n, hmod_s, hrem_n, hmd_n, hic_n, h₂,
    fun hc' => hst1 ▸ hback hc'⟩

/-! ## Phase B slot gathering (`gatherSlotsLoop_exec`) -/

private abbrev gatherSlotBody : Code .exact rFib :=
  ram_exact[
    s0 ← consBase + curDReg;
    s3 ← *s0;
    if zeroP < s3 then [
      *s0 ← zeroP;
      iterCur ← s3 - oneP;
      ⟪addRootAndUpdateMin iterCur⟫
    ] else [
      s0 ← zeroP
    ];
    curDReg ← curDReg + oneP
  ]

private abbrev gatherSlotsLoop : Code .exact rFib :=
  .loop (.lt curDReg maxDegReg) gatherSlotBody

private theorem gatherSlotsLoop_preserves :
    ∀ r : Fin rFib, r.val < 30 → r ≠ minRootReg → r ≠ numRootsReg →
      gatherSlotsLoop.Preserves r := by
  decide +kernel

private theorem gatherSlotBody_occ_wp {n sz base w maxDeg curD idx : ℕ} {a : Data rFib}
    {slotTrees accRoots : List (FHTree n)}
    (hb : a.Bounded w) (hbr : BaseRegs n base a)
    (hcurD : a.regs curDReg = curD) (hmaxD : a.regs maxDegReg = maxDeg + 1)
    (h : Gathering sz (RawState.ofData n base a) accRoots slotTrees maxDeg)
    (hd_le_n : curD ≤ n) (hidx : idx < slotTrees.length)
    (hslot_deg : slotTrees[idx].deg = curD)
    (hcons_eq : (RawState.ofData n base a).cons curD = slotTrees[idx].root.val + 1)
    (hno_other : ∀ R ∈ slotTrees.eraseIdx idx, R.deg ≠ curD) :
    WP w gatherSlotBody a fun a5 t_b =>
      t_b ≤ 34 ∧ a5.Bounded w ∧ BaseRegs n base a5 ∧
      Modifies (Block.mk base (space n)).footprint a.mem a5.mem ∧
      a5.regs curDReg = curD + 1 ∧ a5.regs maxDegReg = maxDeg + 1 ∧
      Gathering sz (RawState.ofData n base a5) (slotTrees[idx] :: accRoots)
        (slotTrees.eraseIdx idx) maxDeg ∧
      ∀ {st' : RawState n} {final : List (FHTree n)},
        Gathered (RawState.ofData n base a5) st'
          (forestNodes ((slotTrees[idx] :: accRoots) ++ slotTrees.eraseIdx idx)) final →
        Gathered (RawState.ofData n base a) st' (forestNodes (accRoots ++ slotTrees)) final := by
  set st := RawState.ofData n base a with hst_def
  have hfit := hbr.fits_of_le hb
  have hu_lt := slotTrees[idx].root.isLt
  have hm_c : a.mem (base + 8 * n + curD) = st.cons curD := by
    simp only [st, RawState.ofData, hd_le_n, ↓reduceIte]
  wram_exec [gatherSlotBody,
    hfit, hbr.regs_consBase, hbr.regs_zeroP, hbr.regs_oneP, hcurD, hm_c, hcons_eq]
  have hb3 : ((((a.set s0 (base + 8 * n + curD)).set s3 (slotTrees[idx].root.val + 1)).write
      (base + 8 * n + curD) 0).set iterCur slotTrees[idx].root.val).Bounded w := by
    wram_bounded <;> exact hfit _ (by omega)
  have hst3 : RawState.ofData n base
      ((((a.set s0 (base + 8 * n + curD)).set s3 (slotTrees[idx].root.val + 1)).write
        (base + 8 * n + curD) 0).set iterCur slotTrees[idx].root.val) =
      { st with cons := Function.update st.cons curD 0 } := by
    wram_simp [ofData_write_cons hd_le_n, ofData_set_scratch, ← hst_def]
  obtain ⟨hroot, hnr, hnext⟩ := h.take hidx hslot_deg hd_le_n hno_other hst3
  wram_call (addRootAndUpdateMin_exec (w := w) (uReg := iterCur) (u := slotTrees[idx].root) hb3
      (by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr])
      (by decide) (by wram_simp) hroot hnr)
    with a4 ⟨hbr4, hmod_add, hadd⟩
  obtain ⟨h₂, hback⟩ := hnext hadd
  have ha4_cd : a4.regs curDReg = curD := by regs_frame
  have ha4_md : a4.regs maxDegReg = maxDeg + 1 := by regs_frame
  refine WP.bounded (‹ExecWithin _ _ _ a4 _›.bounded hb3) ?_
  wram_exec [hfit, hbr4.regs_oneP, ha4_cd]
  intro hb5
  exact ⟨by omega, hb5, by wram_simp [BaseRegs.set_iff, hbr4],
    modifies_block_trans (Modifies.write_of_owns (owns_cons_addr hd_le_n) 0) hmod_add,
    by wram_simp, by wram_simp [ha4_md],
    by wram_simp [ofData_set_scratch]; exact h₂,
    fun hG => hback (by wram_simp [ofData_set_scratch] at hG; exact hG)⟩

/-- Phase B loop: scans `curD` up to `maxDeg + 1` (`curD + rem = maxDeg + 1`), clearing every
occupied `cons[curD]` and adding its tree to the root list with `addRootAndUpdateMin iterCur`. -/
private theorem gatherSlotsLoop_exec {n sz base w maxDeg : ℕ} (rem : ℕ) :
    ∀ (a : Data rFib) (curD : ℕ) (slotTrees accRoots : List (FHTree n)),
      curD + rem = maxDeg + 1 →
      a.Bounded w → BaseRegs n base a →
      a.regs curDReg = curD → a.regs maxDegReg = maxDeg + 1 →
      Gathering sz (RawState.ofData n base a) accRoots slotTrees maxDeg →
      (∀ T ∈ slotTrees, curD ≤ T.deg) →
      ∃ b finalRoots t,
        ExecWithin w gatherSlotsLoop a b t ∧
        t + unitCredit * finalRoots.length ≤
          2 + 116 * rem + unitCredit * accRoots.length ∧
        b.Bounded w ∧ BaseRegs n base b ∧
        Modifies (Block.mk base (space n)).footprint a.mem b.mem ∧
        Gathered (RawState.ofData n base a) (RawState.ofData n base b)
          (forestNodes (accRoots ++ slotTrees)) finalRoots := by
  induction rem with
  | zero =>
    intro a curD slotTrees accRoots hsum hb hbr hcurD hmaxD h hge
    have hcur_eq : curD = maxDeg + 1 := by omega
    subst hcur_eq
    have hc : ¬(Cond.lt curDReg maxDegReg).Holds a := by
      simp only [Cond.Holds, hcurD, hmaxD, Nat.lt_irrefl, not_false_eq_true]
    obtain ⟨rfl, hG⟩ := h.done hge
    exact ⟨a, accRoots, 2, ExecWithin.loop_exit hc, by omega, hb, hbr, Modifies.refl _ _,
      by simpa only [List.append_nil] using hG⟩
  | succ rem' ih =>
    intro a curD slotTrees accRoots hsum hb hbr hcurD hmaxD h hge
    have hd_le_n : curD ≤ n := SlotInv.le_n h.table (by omega)
    have hc_loop : (Cond.lt curDReg maxDegReg).Holds a := by
      simp only [Cond.Holds, hcurD, hmaxD]; omega
    rcases h.table.lookup hd_le_n with ⟨hc0, hnone⟩ |
        ⟨idx, hidx, hslot_deg, hcons_eq, _, hno_other⟩
    · have hm_c : a.mem (base + 8 * n + curD) = (RawState.ofData n base a).cons curD := by
        simp only [RawState.ofData, hd_le_n, ↓reduceIte]
      have hfit := hbr.fits_of_le hb
      have hfit_cd1 : Fits w (curD + 1) := (hmaxD ▸ hb.1 maxDegReg).of_le (by omega)
      have hbody : WP w gatherSlotBody a fun a3 t_b =>
          t_b ≤ 6 ∧ a3.Bounded w ∧ BaseRegs n base a3 ∧ a3.mem = a.mem ∧
          a3.regs curDReg = curD + 1 ∧ a3.regs maxDegReg = maxDeg + 1 ∧
          RawState.ofData n base a3 = RawState.ofData n base a := by
        refine WP.bounded hb ?_
        wram_exec [gatherSlotBody, hfit, hfit_cd1, hbr.regs_consBase, hbr.regs_zeroP,
          hbr.regs_oneP, hcurD, hm_c, hc0]
        intro hb3
        exact ⟨by omega, hb3, by wram_simp [BaseRegs.set_iff, hbr], rfl,
          by wram_simp, by wram_simp [hmaxD], by wram_simp [ofData_set_scratch]⟩
      obtain ⟨a3, t_b, he_body, ht_b, hb3, hbr3, hmem3, ha3_cd, ha3_md, hst3⟩ := hbody
      obtain ⟨b, finalRoots, t_tl, he_tl, ht_tl, hb_b, hbr_b, hmod_tl, hG⟩ :=
        ih a3 (curD + 1) slotTrees accRoots (by omega) hb3 hbr3 ha3_cd ha3_md (hst3 ▸ h)
          fun T hT => by have := hge T hT; have := hnone T hT; omega
      exact ⟨b, finalRoots, t_b + t_tl + 2, ExecWithin.loop_iter hc_loop he_body he_tl,
        by omega, hb_b, hbr_b, hmem3 ▸ hmod_tl, hst3 ▸ hG⟩
    · obtain ⟨a5, t_b, he_body, ht_b, hb5, hbr5, hmod5, ha5_cd, ha5_md, h₂, hback⟩ :=
        gatherSlotBody_occ_wp hb hbr hcurD hmaxD h hd_le_n hidx hslot_deg hcons_eq hno_other
      obtain ⟨b, finalRoots, t_tl, he_tl, ht_tl, hb_b, hbr_b, hmod_tl, hG⟩ :=
        ih a5 (curD + 1) (slotTrees.eraseIdx idx) (slotTrees[idx] :: accRoots) (by omega) hb5 hbr5
          ha5_cd ha5_md h₂ fun R hR => by
            have := hge R (List.mem_of_mem_eraseIdx hR); have := hno_other R hR; omega
      exact ⟨b, finalRoots, t_b + t_tl + 2, ExecWithin.loop_iter hc_loop he_body he_tl,
        by simp only [List.length_cons, unitCredit] at ht_tl ⊢; omega,
        hb_b, hbr_b, modifies_block_trans hmod5 hmod_tl, hback hG⟩

/-! ## `extractMinCode` correctness and `O(log n)` amortized bound -/

private abbrev extractChildrenCode : Code .exact rFib :=
  ram_exact[
    if zeroP < remReg then [
      s0 ← childBase + zReg;
      s1 ← *s0;
      iterCur ← s1 - oneP;
      ⟪childScatterLoop⟫
    ] else [
      s0 ← zeroP
    ]
  ]

private theorem extractChildrenCode_wp {n K_max w base : ℕ} {s : IndexedMinPQ.State n}
    {z : Fin n} {cs E : List (FHTree n)} {st : RawState n} {x : Data rFib}
    (hb : x.Bounded w) (hbr : BaseRegs n base x) (hD : Detached n K_max s st z cs E)
    (hx_st : RawState.ofData n base x = detachState st z)
    (hx_z : x.regs zReg = z.val) (hx_rem : x.regs remReg = st.deg z)
    (hx_md : x.regs maxDegReg = 0)
    (hx_out : x.regs outFlag = 1 ∧ x.regs outV = z.val ∧ x.regs outK = st.key z ∧
      x.regs pReg = st.right z) :
    WP w extractChildrenCode x fun x_A1 t_A1 => ∃ slotTrees_1 maxDeg_1,
      t_A1 + slotCredit * slotTrees_1.length ≤ 7 + 76 * cs.length ∧
      x_A1.Bounded w ∧ BaseRegs n base x_A1 ∧
      Modifies (Block.mk base (space n)).footprint x.mem x_A1.mem ∧
      x_A1.regs outFlag = 1 ∧ x_A1.regs outV = z.val ∧ x_A1.regs outK = st.key z ∧
      x_A1.regs pReg = st.right z ∧ x_A1.regs maxDegReg = maxDeg_1 ∧
      Consolidated (forestNodes (cs ++ E)).length (detachState st z)
        (RawState.ofData n base x_A1) (forestNodes ([] ++ cs)) slotTrees_1 maxDeg_1 := by
  have hfit := hbr.fits_of_le hb
  have hz_lt := z.isLt
  refine WP.bounded hb ?_
  unfold extractChildrenCode
  cases cs with
  | nil =>
    have hdz0 : st.deg z = 0 := by simpa only [List.length_nil] using hD.deg
    wram_exec [hbr.regs_zeroP, hx_rem, hdz0]
    intro hb_A1
    refine ⟨[], 0, by simp only [List.length_nil, Nat.mul_zero]; omega, hb_A1,
      by wram_simp [BaseRegs.set_iff, hbr], Modifies.refl _ _,
      by wram_simp [hx_out.1], by wram_simp [hx_out.2.1], by wram_simp [hx_out.2.2.1],
      by wram_simp [hx_out.2.2.2], by wram_simp [hx_md], ?_⟩
    wram_simp [ofData_set_scratch, hx_st]; exact hD.scatterChildren.done
  | cons C₀ cs₀ =>
    have hhc_lt := C₀.root.isLt
    have hcz_mem : x.mem (base + 2 * n + z.val) = C₀.root.val + 1 :=
      (congrFun (congrArg RawState.child hx_st) z).trans (hD.child C₀.root rfl)
    have hdz_pos : 0 < st.deg z := by rw [hD.deg, List.length_cons]; omega
    wram_exec [hfit, hbr.regs_childBase, hbr.regs_zeroP, hbr.regs_oneP, hx_z, hx_rem,
      hdz_pos, hcz_mem]
    have hst_c0 : RawState.ofData n base
        (((x.set s0 (base + 2 * n + z.val)).set s1 (C₀.root.val + 1)).set iterCur C₀.root.val) =
        detachState st z := by wram_simp [ofData_set_scratch, hx_st]
    wram_call (scatterListLoop_exec (w := w) true childScatterBody 74 childScatterBody_wp
        (C₀ :: cs₀) _ [] 0 (by wram_bounded <;> exact hfit _ (by omega))
        (by wram_simp [BaseRegs.set_iff, hbr]) (hst_c0 ▸ hD.scatterChildren)
        (by wram_simp [hx_rem, hD.deg]) (by wram_simp [hx_md])
        (fun y hy => by cases hy; wram_simp))
      with x_A1 t_sc1 ⟨slotTrees_1, maxDeg_1, ht_sc1, hb_A1, hbr_A1, hmod_sc1, hmd_sc1, hc_sc1⟩
    obtain ⟨_, _, _, _⟩ := hx_out
    exact fun _ =>
      ⟨slotTrees_1, maxDeg_1, by simp only [slotCredit, List.length_nil] at ht_sc1 ⊢; omega,
        hb_A1, hbr_A1, hmod_sc1,
        by regs_frame, by regs_frame, by regs_frame, by regs_frame,
        hmd_sc1, hst_c0 ▸ hc_sc1⟩

private abbrev extractFinishCode : Code .exact rFib :=
  ram_exact[
    remReg ← numRootsReg - oneP;
    iterCur ← pReg;
    ⟪rootScatterLoop⟫;
    minRootReg ← zeroP;
    numRootsReg ← zeroP;
    maxDegReg ← maxDegReg + oneP;
    curDReg ← zeroP;
    ⟪gatherSlotsLoop⟫
  ]

private theorem extractFinishCode_wp {n K_max w base maxDeg_1 : ℕ} {s : IndexedMinPQ.State n}
    {z : Fin n} {cs E slotTrees_1 : List (FHTree n)} {st : RawState n} {x_A1 : Data rFib}
    (hb_A1 : x_A1.Bounded w) (hbr_A1 : BaseRegs n base x_A1)
    (hD : Detached n K_max s st z cs E) (hr_le : E.length + 1 ≤ n)
    (hmd_A1 : x_A1.regs maxDegReg = maxDeg_1) (hpr : x_A1.regs pReg = st.right z)
    (hright_fit : Fits w (st.right z))
    (hc₁ : Consolidated (forestNodes (cs ++ E)).length (detachState st z)
      (RawState.ofData n base x_A1) (forestNodes cs) slotTrees_1 maxDeg_1) :
    WP w extractFinishCode x_A1 fun y t =>
      ∃ (finalRoots : List (FHTree n)) (maxDeg_2 : ℕ),
        t + unitCredit * finalRoots.length ≤
          10 + 69 * E.length + slotCredit * slotTrees_1.length + 116 * (maxDeg_2 + 1) ∧
        y.Bounded w ∧ BaseRegs n base y ∧
        Modifies (Block.mk base (space n)).footprint x_A1.mem y.mem ∧
        (∀ r : Fin rFib, r.val < 30 → r ≠ minRootReg → r ≠ numRootsReg →
          y.regs r = x_A1.regs r) ∧
        FibRawInv n K_max ((indexedMinPQSpec n K_max).stepFn s .extractMin).1
          (RawState.ofData n base y) ∧
        y.regs numRootsReg = finalRoots.length ∧
        y.regs numMarkedReg ≤ st.numMarked ∧
        maxDeg_2 ≤ 2 * Nat.log 2 (IndexedMinPQ.dom s).card + 1 := by
  have hfit := hbr_A1.fits_of_le hb_A1
  have hnr_xA1 : x_A1.regs numRootsReg = E.length + 1 := hc₁.scattered.numRoots.trans hD.numRoots
  wram_exec [extractFinishCode, hfit, hbr_A1.regs_oneP, hnr_xA1, hpr]
  refine WP.name fun x_tr hx_tr => ?_
  have hb_tr : x_tr.Bounded w := by subst hx_tr; wram_bounded; exact hfit _ (by omega)
  have hst_tr : RawState.ofData n base x_tr = RawState.ofData n base x_A1 := by
    subst hx_tr; wram_simp [ofData_set_scratch]
  obtain ⟨x_A2, t_A2, he_A2, slotTrees_2, maxDeg_2, ht_A2, hb_A2, hbr_A2, hmod_A2,
    hmd_A2, hc₂⟩ :=
    scatterListLoop_exec false rootScatterBody 67 rootScatterBody_wp
      E x_tr slotTrees_1 maxDeg_1 hb_tr
      (by subst hx_tr; wram_simp [BaseRegs.set_iff, hbr_A1])
      (hst_tr ▸ hD.scatterRoots hc₁) (by subst hx_tr; wram_simp)
      (by subst hx_tr; wram_simp [hmd_A1])
      (fun y hy => by subst hx_tr; wram_simp; exact hD.right y hy)
  rw [hst_tr] at hc₂
  refine WP.of_execWithin he_A2 ?_
  have hmd2_le_n : maxDeg_2 + 1 ≤ n := by
    obtain ⟨_, _, _, _, _, hcases⟩ := hc₂.table; rcases hcases with h0 | h2 <;> omega
  wram_exec [hfit, hbr_A2.regs_zeroP, hbr_A2.regs_oneP, hmd_A2]
  refine WP.name fun x_B0 hx_B0 => ?_
  have hb_B0 : x_B0.Bounded w := by subst hx_B0; wram_bounded <;> exact hfit _ (by omega)
  have hst_B0 : RawState.ofData n base x_B0 =
      { RawState.ofData n base x_A2 with minRoot := 0, numRoots := 0 } := by
    subst hx_B0; wram_simp [ofData_set_scratch, ofData_set_numRoots, ofData_set_minRoot]
  obtain ⟨y, finalRoots, t_B, he_B, ht_B, hb_y, hbr_y, hmod_B, hG⟩ :=
    gatherSlotsLoop_exec (maxDeg := maxDeg_2) (maxDeg_2 + 1) x_B0 0 slotTrees_2 [] (by omega)
      hb_B0 (by subst hx_B0; wram_simp [BaseRegs.set_iff, hbr_A2])
      (by subst hx_B0; wram_simp) (by subst hx_B0; wram_simp)
      (hst_B0 ▸ hD.gathering hc₁ hc₂) fun _ _ => Nat.zero_le _
  obtain ⟨hfin, hnm_le, hmd2_log⟩ := hD.finish hc₁ hc₂ (hst_B0 ▸ hG)
  refine WP.of_execWithin he_B ⟨finalRoots, maxDeg_2, by simp only [List.length_nil] at ht_B; omega,
    hb_y, hbr_y,
    modifies_block_trans (by subst hx_tr; exact hmod_A2) (by subst hx_B0; exact hmod_B),
    fun r hr hm hnr => by
      rw [he_B.regs_eq (gatherSlotsLoop_preserves r hr hm hnr)]
      subst hx_B0; wram_simp [he_A2.regs_eq (rootScatterLoop_preserves r hr)]
      subst hx_tr; wram_simp,
    by simp only [indexedMinPQSpec, IndexedMinPQ.step, StateTransitionSpec.stepFn, hD.findMin]
       exact hfin,
    (hst_B0 ▸ hG).numRoots, hnm_le, hmd2_log⟩

/-- `extractMinCode` implements `.extractMin` on `FibInv` within
`410 * (Nat.log 2 (IndexedMinPQ.dom s).card + 1)` amortized instructions
(`t + potential y ≤ 410 * (Nat.log 2 (IndexedMinPQ.dom s).card + 1) + potential x`). The forest
reasoning is that of the record heap: `FibRawInv.detach` splits the heap at its minimum root, the
three loops produce `Consolidated`, `Consolidated` and `Gathered`, and `Detached.finish`
reassembles `FibRawInv`. -/
theorem extractMinCode_exec {n K_max w base : ℕ} {s : IndexedMinPQ.State n} {x : Data rFib}
    (hinv : FibInv n K_max w base s x) :
    ∃ y t, ExecWithin w extractMinCode x y t ∧
      code.decode (n := n) (K_max := K_max) .extractMin y.regs =
        some ((indexedMinPQSpec n K_max).stepFn s .extractMin).2 ∧
      FibInv n K_max w base ((indexedMinPQSpec n K_max).stepFn s .extractMin).1 y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      t + potential y ≤
        410 * (Nat.log 2 (IndexedMinPQ.dom s).card + 1) + potential x := by
  obtain ⟨hb, hbr, hraw⟩ := hinv
  set st := RawState.ofData n base x with hst_def
  have hfit := hbr.fits_of_le hb
  change WP w extractMinCode x fun y t => _
  unfold extractMinCode
  by_cases hm0 : st.minRoot = 0
  · obtain ⟨_, hfind⟩ := hraw.findMin_eq_none hm0
    refine WP.bounded hb ?_
    wram_exec [hbr.regs_zeroP, show x.regs minRootReg = 0 from hm0]
    intro hby
    simp only [PQCode.decode, code, indexedMinPQSpec, IndexedMinPQ.step,
      StateTransitionSpec.stepFn, hfind]
    refine ⟨by wram_simp,
      ⟨hby, hbr.set_non_base (by decide) 0,
        (ofData_set_scratch x (by decide : 17 ≤ outFlag.val) 0).symm ▸ hraw⟩,
      Modifies.refl _ _, ?_⟩
    rw [potential_set_scratch x (by decide : 17 ≤ outFlag.val) 0]; omega
  · obtain ⟨z, -, hmin_z, -⟩ := (FibonacciHeap.minRoot_cases hraw).resolve_left hm0
    obtain ⟨cs, E, hD⟩ := FibonacciHeap.FibRawInv.detach hraw hmin_z
    have hz_lt := z.isLt
    have hsz_pos : 1 ≤ st.sz := by
      have := Finset.card_pos.mpr ⟨z, IndexedMinPQ.findMin_mem_dom hD.findMin⟩; rw [hD.sz]; omega
    have hsz_le_n : st.sz ≤ n := hraw.bounds.1
    have hr_le : E.length + 1 ≤ n := by have := hraw.bounds.2.1; have := hD.numRoots; omega
    have hmin_reg : x.regs minRootReg = z.val + 1 := hmin_z
    have hsz_reg : x.regs szReg = st.sz := rfl
    have hkz_mem : x.mem (base + z.val) = st.key z := rfl
    have hrz_mem : x.mem (base + 4 * n + z.val) = st.right z := rfl
    have hdz_mem : x.mem (base + 5 * n + z.val) = st.deg z := rfl
    wram_exec -split [hfit, hbr.regs_baseReg, hbr.regs_inBase, hbr.regs_rightBase,
      hbr.regs_degBase, hbr.regs_zeroP, hbr.regs_oneP, hmin_reg, hsz_reg,
      hkz_mem, hrz_mem, hdz_mem]
    wram_call (extractChildrenCode_wp (w := w) (base := base)
        (by have : Fits w (st.key z) := hkz_mem ▸ hb.2 _
            have : Fits w (st.right z) := hrz_mem ▸ hb.2 _
            have : Fits w (st.deg z) := hdz_mem ▸ hb.2 _
            wram_bounded <;> exact hfit _ (by omega))
        (by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr]) hD
        (by wram_simp [detachState, ofData_set_sz, ofData_write_inHeap, ofData_set_scratch,
          ← hst_def])
        (by wram_simp) (by wram_simp) (by wram_simp)
        ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩)
      with x_A1 t_A1 ⟨slotTrees_1, maxDeg_1, ht_A1, hb_A1, hbr_A1, hmod_A1,
        hA1_of, hA1_ov, hA1_ok, hA1_pr, hmd_A1, hc₁⟩
    wram_call (extractFinishCode_wp (w := w) hb_A1 hbr_A1 hD hr_le hmd_A1 hA1_pr
        (hrz_mem ▸ hb.2 _) hc₁)
      with y t_f ⟨finalRoots, maxDeg_2, ht_f, hb_y, hbr_y, hmod_f, hregs_y, hfin,
        hnr_y, hnm_y, hmd2_log⟩
    refine ⟨?_, ⟨hb_y, hbr_y, hfin⟩,
      modifies_block_trans (Modifies.write_of_owns (owns_arr_addr (k := 7) (by decide) hz_lt) 0)
        (modifies_block_trans hmod_A1 hmod_f), ?_⟩
    · simp only [PQCode.decode, code, indexedMinPQSpec, IndexedMinPQ.step,
        StateTransitionSpec.stepFn, hD.findMin,
        hregs_y outFlag (by decide) (by decide) (by decide), hA1_of,
        hregs_y outV (by decide) (by decide) (by decide), hA1_ov,
        hregs_y outK (by decide) (by decide) (by decide), hA1_ok,
        one_ne_zero, ↓reduceIte, hz_lt, ↓reduceDIte, Fin.eta]
    · have hnr_x : x.regs numRootsReg = E.length + 1 := hD.numRoots
      have hnm_x : x.regs numMarkedReg = st.numMarked := rfl
      have hdz := hD.degBound
      simp only [potential, unitCredit, slotCredit, hnr_x, hnm_x, hnr_y] at ht_A1 ht_f ⊢
      omega

end Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap
