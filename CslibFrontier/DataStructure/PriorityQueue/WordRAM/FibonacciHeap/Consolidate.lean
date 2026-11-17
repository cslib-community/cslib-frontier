/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.BasicOps
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Consolidation

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

/-! ## Root scattering (`scatterBody_exec` and `scatterRootCode_exec`) -/

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
    if zeroP < s6 then [
      s6 ← s4;
      s4 ← s5;
      s5 ← s6
    ] else [
      s0 ← zeroP
    ];
    s1 ← s4 + oneP;
    s0 ← parBase + s5;
    *s0 ← s1;
    s0 ← degBase + s4;
    s1 ← *s0;
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
    ];
    curDReg ← curDReg + oneP;
    s0 ← consBase + curDReg;
    s3 ← *s0
  ]

/-- The collision body writes only its degree counter and inner scratch registers. -/
private theorem scatterBody_preserves :
    ∀ r : Fin rFib, r.val < 34 → scatterBody.Preserves r := by
  decide +kernel

private theorem scatterRootCode_preserves :
    ∀ r : Fin rFib, r.val < 33 → scatterRootCode.Preserves r := by
  decide +kernel

/-- Single collision step of `scatterRootCode`: clears `cons[curD]`, links the tree `T_cur` in
`s4` with the table's tree of the same degree (the one that precedes becomes the parent), and
advances `curD`, in `≤ 43` steps. The forest reasoning is `Placing.collide` and `LinksAs.linked`:
the machine state after the link is `LinksAs` of the state before it. -/
private theorem scatterBody_exec {n sz base w maxDeg curD : ℕ} {a : Data rFib}
    {T_cur : FHTree n} {slotTrees : List (FHTree n)} {z : Fin n}
    (hb : a.Bounded w) (hbr : BaseRegs n base a)
    (hP : Placing sz z (RawState.ofData n base a) T_cur slotTrees maxDeg)
    (hcur_deg : T_cur.deg = curD)
    (ha_s4 : a.regs s4 = T_cur.root.val)
    (ha_curD : a.regs curDReg = curD)
    (ha_s3 : a.regs s3 = (RawState.ofData n base a).cons curD)
    (hcond : (Cond.lt zeroP s3).Holds a) :
    ∃ a' T_next slotTrees',
      ExecWithin w scatterBody a a' 43 ∧
      a'.Bounded w ∧ BaseRegs n base a' ∧
      Modifies (Block.mk base (space n)).footprint a.mem a'.mem ∧
      (∀ r : Fin rFib, r.val < 34 → a'.regs r = a.regs r) ∧
      slotTrees'.length + 1 = slotTrees.length ∧
      T_next.deg = curD + 1 ∧
      a'.regs s4 = T_next.root.val ∧
      a'.regs curDReg = curD + 1 ∧
      a'.regs s3 = (RawState.ofData n base a').cons (curD + 1) ∧
      Placing sz z (RawState.ofData n base a') T_next slotTrees' maxDeg ∧
      ∀ {st' : RawState n} {slots' : List (FHTree n)} {md' : ℕ},
        Consolidated sz (RawState.ofData n base a') st' (forestNodes (T_next :: slotTrees'))
          slots' md' →
        Consolidated sz (RawState.ofData n base a) st' (forestNodes (T_cur :: slotTrees))
          slots' md' := by
  set st := RawState.ofData n base a with hst_def
  have hfit := hbr.fits_of_le hb
  have hdeg_bds := hP.deg_bounds
  rw [hcur_deg] at hdeg_bds
  have hd_le_n : curD ≤ n := by omega
  have hd1_le_n : curD + 1 ≤ n := by omega
  have hcons_pos : 0 < st.cons curD := by
    rw [Cond.Holds, hbr.regs_zeroP, ha_s3] at hcond
    exact hcond
  rcases hP.table.lookup hd_le_n with ⟨hc0, _⟩ |
      ⟨idx, hidx, hslot_deg, hcons_eq, hlen_er, hno_other⟩
  · omega
  have hu4_lt := T_cur.root.isLt
  have hu5_lt := slotTrees[idx].root.isLt
  let st₁ : RawState n := { st with cons := Function.update st.cons curD 0 }
  obtain ⟨hT_cur1, hT_slot1, hnd_pair, hnext⟩ := hP.collide (st₁ := st₁)
    hidx (hslot_deg.trans hcur_deg.symm) (fun R hR => by rw [hcur_deg]; exact hno_other R hR)
    (by rw [hcur_deg])
  have hu4_ne_u5 : T_cur.root ≠ slotTrees[idx].root :=
    (List.nodup_append.mp hnd_pair).2.2 _ T_cur.root_mem_nodes _ slotTrees[idx].root_mem_nodes
  suffices WP w scatterBody a fun a' t => t ≤ 43 ∧ ∃ T_next : FHTree n,
      a'.Bounded w ∧ BaseRegs n base a' ∧
      Modifies (Block.mk base (space n)).footprint a.mem a'.mem ∧
      T_next.deg = curD + 1 ∧
      a'.regs s4 = T_next.root.val ∧
      a'.regs curDReg = curD + 1 ∧
      a'.regs s3 = (RawState.ofData n base a').cons (curD + 1) ∧
      Placing sz z (RawState.ofData n base a') T_next (slotTrees.eraseIdx idx) maxDeg ∧
      ∀ {st' : RawState n} {slots' : List (FHTree n)} {md' : ℕ},
        Consolidated sz (RawState.ofData n base a') st'
          (forestNodes (T_next :: slotTrees.eraseIdx idx)) slots' md' →
        Consolidated sz st st' (forestNodes (T_cur :: slotTrees)) slots' md' by
    obtain ⟨a', t, he, ht, T_next, hba', hbra', hmod, hdeg', hs4', hcd', hs3', hP', hback⟩ := this
    have he_all := he.mono ht
    exact ⟨a', T_next, slotTrees.eraseIdx idx, he_all, hba', hbra', hmod,
      fun r hr => he_all.regs_eq (scatterBody_preserves r hr),
      hlen_er, hdeg', hs4', hcd', hs3', hP', hback⟩
  refine WP.bounded hb ?_
  have hs3_eq : a.regs s3 = slotTrees[idx].root.val + 1 := ha_s3.trans hcons_eq
  have hku4 : a.mem (base + T_cur.root.val) = st.key T_cur.root := rfl
  have hku5 : a.mem (base + slotTrees[idx].root.val) = st.key slotTrees[idx].root := rfl
  unfold scatterBody
  -- Step 1–2: clear `cons[curD]` and load `key[T_cur.root]`, `key[slotTrees[idx].root]`.
  wram_exec [hfit, hbr.regs_consBase, hbr.regs_baseReg, hbr.regs_zeroP, hbr.regs_oneP,
    hs3_eq, ha_curD, ha_s4, hku4, hku5]
  refine WP.name fun a2_pre ha2_pre => ?_
  have hbr2_pre : BaseRegs n base a2_pre := by
    subst ha2_pre
    wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr]
  have he_plt := prioLTFlag_exec (w := w) hbr2_pre s5 s2 s4 s1 s6
  dsimp only at he_plt
  have ha2_s2 : a2_pre.regs s2 = st.key slotTrees[idx].root := by subst ha2_pre; wram_simp
  have ha2_s1 : a2_pre.regs s1 = st.key T_cur.root := by subst ha2_pre; wram_simp
  have ha2_s5 : a2_pre.regs s5 = slotTrees[idx].root.val := by subst ha2_pre; wram_simp
  have ha2_s4 : a2_pre.regs s4 = T_cur.root.val := by subst ha2_pre; wram_simp [ha_s4]
  rw [ha2_s2, ha2_s1, ha2_s5, ha2_s4] at he_plt
  have he_plt' : ExecWithin w (prioLTFlag s5 s2 s4 s1 s6) a2_pre
      (a2_pre.set s6 (if IndexedMinPQ.PrioLT (slotTrees[idx].root, st.key slotTrees[idx].root)
        (T_cur.root, st.key T_cur.root) then 1 else 0)) 6 :=
    he_plt
  refine WP.of_execWithin he_plt' ?_
  -- Step 3: swap `(s4, s5)` if `slotTrees[idx]` precedes `T_cur`.
  apply WP.seq
  refine WP.cut (fun a3 t3 => t3 ≤ 4 ∧ a3.Bounded w ∧ BaseRegs n base a3 ∧
      Modifies (Block.mk base (space n)).footprint a.mem a3.mem ∧
      a3.regs curDReg = curD ∧
      RawState.ofData n base a3 = st₁ ∧
      ∃ T₁ T₂ : FHTree n,
        ValidRoot st₁ none T₁ ∧ T₁.deg = curD ∧ (T₁.nodes ++ T₂.nodes).Nodup ∧
        a3.regs s4 = T₁.root.val ∧ a3.regs s5 = T₂.root.val ∧
        ∀ {st₂ : RawState n}, LinksAs st₁ T₁.root T₂.root st₂ →
          Linked st₁ st₂ T_cur slotTrees[idx] (.node T₁.root (T₁.children ++ [T₂])))
    (WP.bounded
      (by subst ha2_pre; wram_bounded <;> exact hfit _ (by (try split_ifs) <;> omega)) ?_) ?_
  · subst ha2_pre
    by_cases hlt54 : IndexedMinPQ.PrioLT (slotTrees[idx].root, st.key slotTrees[idx].root)
        (T_cur.root, st.key T_cur.root)
    · wram_exec [hfit, hbr.regs_zeroP, ha_s4, hlt54]
      intro hb3
      refine ⟨by omega, hb3, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr],
        Modifies.block_iff.2 fun addr haddr => by
          have := out_of_footprint n base haddr; wram_simp,
        by wram_simp [ha_curD],
        by wram_simp [st₁, ofData_write_cons hd_le_n, ofData_set_scratch, ← hst_def],
        slotTrees[idx], T_cur, hT_slot1, hslot_deg, List.perm_append_comm.nodup_iff.mp hnd_pair,
        by wram_simp, by wram_simp,
        fun hl => (LinksAs.linked hT_slot1 hT_cur1 (List.perm_append_comm.nodup_iff.mp hnd_pair)
          (hslot_deg.trans hcur_deg.symm) hlt54 hl).symm (hcur_deg.trans hslot_deg.symm)⟩
    · have hlt45 : IndexedMinPQ.PrioLT (T_cur.root, st.key T_cur.root)
          (slotTrees[idx].root, st.key slotTrees[idx].root) :=
        (IndexedMinPQ.prioLT_or_prioLT_of_ne hu4_ne_u5 _ _).resolve_right hlt54
      wram_exec [hfit, hbr.regs_zeroP, ha_s4, hlt54]
      intro hb3
      refine ⟨by omega, hb3, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr],
        Modifies.block_iff.2 fun addr haddr => by
          have := out_of_footprint n base haddr; wram_simp,
        by wram_simp [ha_curD],
        by wram_simp [st₁, ofData_write_cons hd_le_n, ofData_set_scratch, ← hst_def],
        T_cur, slotTrees[idx], hT_cur1, hcur_deg, hnd_pair,
        by wram_simp [ha_s4], by wram_simp,
        fun hl => LinksAs.linked hT_cur1 hT_slot1 hnd_pair (hcur_deg.trans hslot_deg.symm) hlt45 hl⟩
  rintro a3 t3 ⟨ht3, hb3, hbr3, hmod3, ha3_cd, hst3, T₁, T₂, hT₁, hd₁, hnd12, ha3_s4, ha3_s5,
    hlinked⟩
  have hw1_lt := T₁.root.isLt
  have hw2_lt := T₂.root.isLt
  have hdeg_w1 : st₁.deg T₁.root = curD := (ValidSubtree.deg_root hT₁.1).trans hd₁
  have hdw1_mem : a3.mem (base + 5 * n + T₁.root.val) = curD :=
    (congrFun (congrArg RawState.deg hst3) T₁.root).trans hdeg_w1
  -- Step 4: set `par[T₂.root] ← T₁.root + 1` and load `s1 ← deg[T₁.root]`,
  -- stopping at `if s1 = zeroP`.
  wram_exec -split [hfit, hbr3.regs_parBase, hbr3.regs_degBase, hbr3.regs_oneP, ha3_s4, ha3_s5,
    hdw1_mem]
  -- Step 5: splice `T₂.root` into `T₁.root`'s child list and increment `deg[T₁.root]`.
  refine WP.cut (fun a5 t5 => t5 ≤ 18 ∧ a5.Bounded w ∧ BaseRegs n base a5 ∧
      Modifies (Block.mk base (space n)).footprint a3.mem a5.mem ∧
      a5.regs s4 = T₁.root.val ∧ a5.regs curDReg = curD ∧
      LinksAs st₁ T₁.root T₂.root (RawState.ofData n base a5))
    (WP.bounded (by wram_bounded <;> exact hfit _ (by omega)) ?_) ?_
  · by_cases hd0 : curD = 0
    · wram_exec [hfit, hbr3.regs_leftBase, hbr3.regs_rightBase, hbr3.regs_childBase,
        hbr3.regs_degBase, hbr3.regs_zeroP, hbr3.regs_oneP, ha3_s4, ha3_s5, hd0]
      intro hb5
      refine ⟨by omega, hb5, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr3],
        Modifies.block_iff.2 fun addr haddr => by
          have := out_of_footprint n base haddr; wram_simp,
        by wram_simp [ha3_s4], by wram_simp [ha3_cd], Or.inl ⟨hdeg_w1.trans hd0, ?_⟩⟩
      wram_simp [ofData_write_deg, ofData_write_child, ofData_write_right, ofData_write_left,
        ofData_write_par, ofData_set_scratch, hst3, st₁]
    · obtain ⟨h_c, r_c, hcw1_eq, hr_c⟩ := ValidSubtree.exists_child hT₁.1
        (by rw [ValidSubtree.deg_root hT₁.1]; exact fun h => hd0 (hd₁.symm.trans h))
      have hhc_lt := h_c.isLt
      have hcw1_mem : a3.mem (base + 2 * n + T₁.root.val) = h_c.val + 1 :=
        (congrFun (congrArg RawState.child hst3) T₁.root).trans hcw1_eq
      wram_exec [hfit, hbr3.regs_childBase, hbr3.regs_zeroP, hbr3.regs_oneP, ha3_s4, hcw1_mem, hd0]
      refine WP.name fun q1 hq1 => ?_
      have hb_q1 : q1.Bounded w := by subst hq1; wram_bounded <;> exact hfit _ (by omega)
      have hbr_q1 : BaseRegs n base q1 := by
        subst hq1; wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr3]
      have hst_q1 : RawState.ofData n base q1 =
          { st₁ with par := Function.update st₁.par T₂.root (T₁.root.val + 1) } := by
        subst hq1
        wram_simp [ofData_write_par, ofData_set_scratch, hst3]
      obtain ⟨q2, t4, hbr_q2, hmod_q2, hst_q2⟩ :=
        insertIntoNonEmptyList_exec (x := q1) (hReg := s6) (uReg := s5) (h := h_c) (u := T₂.root)
          (r := r_c) hb_q1 hbr_q1 (by decide) (by decide) (by decide) (by decide)
          (by subst hq1; wram_simp) (by subst hq1; wram_simp [ha3_s5])
          (by rw [hst_q1]; exact hr_c)
      rw [hst_q1] at hst_q2
      refine WP.of_execWithin t4 ?_
      have hb_q2 : q2.Bounded w := t4.bounded hb_q1
      have hq2_s1 : q2.regs s1 = curD := by
        rw [t4.regs_eq (insertIntoNonEmptyList_preserves (by decide) (by decide))]
        subst hq1; wram_simp
      have hq2_s4 : q2.regs s4 = T₁.root.val := by
        rw [t4.regs_eq (insertIntoNonEmptyList_preserves (by decide) (by decide))]
        subst hq1; wram_simp [ha3_s4]
      have hq2_cd : q2.regs curDReg = curD := by
        rw [t4.regs_eq (insertIntoNonEmptyList_preserves (by decide) (by decide))]
        subst hq1; wram_simp [ha3_cd]
      have hmod_a3_q1 : Modifies (Block.mk base (space n)).footprint a3.mem q1.mem := by
        subst hq1
        exact Modifies.block_iff.2 fun addr haddr => by
          have := out_of_footprint n base haddr; wram_simp
      refine WP.bounded hb_q2 ?_
      wram_exec [hfit, hbr_q2.regs_degBase, hbr_q2.regs_oneP, hq2_s1, hq2_s4]
      intro hb5 _
      have hmod_q2_a5 : Modifies (Block.mk base (space n)).footprint q2.mem
          (((q2.set s1 (curD + 1)).set s0 (base + 5 * n + T₁.root.val)).write
            (base + 5 * n + T₁.root.val) (curD + 1)).mem :=
        Modifies.block_iff.2 fun addr haddr => by
          have := out_of_footprint n base haddr; wram_simp
      refine ⟨by omega, hb5, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr_q2],
        modifies_block_trans (modifies_block_trans hmod_a3_q1 hmod_q2) hmod_q2_a5,
        by wram_simp [hq2_s4], by wram_simp [hq2_cd],
        Or.inr ⟨h_c, r_c, fun h => hd0 (hdeg_w1.symm.trans h), hcw1_eq, hr_c, ?_⟩⟩
      wram_simp [ofData_write_deg, ofData_set_scratch, hst_q2, hdeg_w1]
  rintro a5 t5 ⟨ht5, hb5, hbr5, hmod5, ha5_s4, ha5_cd, hlink5⟩
  let T_next : FHTree n := FHTree.node T₁.root (T₁.children ++ [T₂])
  have hL := hlinked hlink5
  obtain ⟨hP_next, hback⟩ := hnext hL
  -- Step 6: increment `curDReg` and load `s3 ← cons[curD + 1]`.
  have hm_c1 : a5.mem (base + 8 * n + (curD + 1)) =
      (RawState.ofData n base a5).cons (curD + 1) := by
    simp only [RawState.ofData, hd1_le_n, ↓reduceIte]
  refine WP.bounded hb5 ?_
  wram_exec [hfit, hbr5.regs_consBase, hbr5.regs_oneP, ha5_cd, hm_c1]
  intro hb6 _
  refine ⟨by omega, T_next, hb6, by wram_simp [BaseRegs.set_iff, hbr5],
    modifies_block_trans hmod3 hmod5, hL.deg.trans (by rw [hcur_deg]),
    by wram_simp [ha5_s4, T_next, FHTree.root_node], by wram_simp,
    by wram_simp [ofData_set_scratch],
    by wram_simp [ofData_set_scratch]; exact hP_next,
    fun hc => hback (by wram_simp [ofData_set_scratch] at hc; exact hc)⟩

/-- Full `while zeroP < s3 do scatterBody` loop by induction on `slotTrees.length`: it stops at an
empty slot `curD_f`, holding `Placing` for the final tree `T_f`, in
`t + 50 * slotTrees_f.length ≤ 2 + 50 * slotTrees.length` instructions. Placing `T_f` places
`T_cur`. -/
private theorem scatterLoop_exec {n sz base w maxDeg : ℕ} {z : Fin n} :
    ∀ (k : ℕ) {a : Data rFib} {T_cur : FHTree n} {slotTrees : List (FHTree n)} {curD : ℕ},
      slotTrees.length = k →
      a.Bounded w → BaseRegs n base a →
      Placing sz z (RawState.ofData n base a) T_cur slotTrees maxDeg →
      T_cur.deg = curD →
      a.regs s4 = T_cur.root.val →
      a.regs curDReg = curD →
      a.regs s3 = (RawState.ofData n base a).cons curD →
      ∃ z_lp T_f slotTrees_f curD_f t,
        ExecWithin w (.loop (.lt zeroP s3) scatterBody) a z_lp t ∧
        t + slotCredit * slotTrees_f.length ≤ 2 + slotCredit * slotTrees.length ∧
        ¬(Cond.lt zeroP s3).Holds z_lp ∧
        z_lp.Bounded w ∧ BaseRegs n base z_lp ∧
        Modifies (Block.mk base (space n)).footprint a.mem z_lp.mem ∧
        (∀ r : Fin rFib, r.val < 34 → z_lp.regs r = a.regs r) ∧
        T_f.deg = curD_f ∧
        z_lp.regs s4 = T_f.root.val ∧
        z_lp.regs curDReg = curD_f ∧
        z_lp.regs s3 = (RawState.ofData n base z_lp).cons curD_f ∧
        Placing sz z (RawState.ofData n base z_lp) T_f slotTrees_f maxDeg ∧
        ∀ {st' : RawState n} {slots' : List (FHTree n)} {md' : ℕ},
          Consolidated sz (RawState.ofData n base z_lp) st' (forestNodes (T_f :: slotTrees_f))
            slots' md' →
          Consolidated sz (RawState.ofData n base a) st' (forestNodes (T_cur :: slotTrees))
            slots' md'
  | 0, a, T_cur, slotTrees, curD, _, hb, hbr, hP, hcd, hs4, hcd_r, hs3 => by
    by_cases hc : (Cond.lt zeroP s3).Holds a
    · obtain ⟨_, _, _, _, _, _, _, _, hlen_er, _⟩ := scatterBody_exec hb hbr hP hcd hs4 hcd_r hs3 hc
      omega
    · exact ⟨a, T_cur, slotTrees, curD, 2, ExecWithin.loop_exit hc, by omega, hc, hb, hbr,
        Modifies.refl _ _, fun _ _ => rfl, hcd, hs4, hcd_r, hs3, hP, fun h => h⟩
  | k + 1, a, T_cur, slotTrees, curD, hk, hb, hbr, hP, hcd, hs4, hcd_r, hs3 => by
    by_cases hc : (Cond.lt zeroP s3).Holds a
    · obtain ⟨a', T_next, slotTrees', he1, hb', hbr', hmod1, hlow1, hlen_er, hdeg1, hs4_1, hcd1,
        hs3_1, hP1, hback1⟩ := scatterBody_exec hb hbr hP hcd hs4 hcd_r hs3 hc
      obtain ⟨z_lp, T_f, slotTrees_f, curD_f, t₂, he2, ht2, hnc, hbz, hbrz, hmod2, hlow2, hdeg2,
        hs4_2, hcd2, hs3_2, hP2, hback2⟩ :=
        scatterLoop_exec k (by omega) hb' hbr' hP1 hdeg1 hs4_1 hcd1 hs3_1
      exact ⟨z_lp, T_f, slotTrees_f, curD_f, 43 + t₂ + 2, ExecWithin.loop_iter hc he1 he2,
        by dsimp only [slotCredit] at ht2 ⊢; omega, hnc, hbz, hbrz,
        modifies_block_trans hmod1 hmod2, fun r hr => (hlow2 r hr).trans (hlow1 r hr), hdeg2,
        hs4_2, hcd2, hs3_2, hP2, fun hc' => hback1 (hback2 hc')⟩
    · exact ⟨a, T_cur, slotTrees, curD, 2, ExecWithin.loop_exit hc, by omega, hc, hb, hbr,
        Modifies.refl _ _, fun _ _ => rfl, hcd, hs4, hcd_r, hs3, hP, fun h => h⟩

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
  have hd0_bds := hP.deg_bounds
  have hd0_le_n : T₀.deg ≤ n := by omega
  have hm_du0 : x.mem (base + 5 * n + T₀.root.val) = T₀.deg := ValidSubtree.deg_root hP.valid.1
  have hm_cd0 : x.mem (base + 8 * n + T₀.deg) = st.cons T₀.deg := by
    simp only [st, RawState.ofData, hd0_le_n, ↓reduceIte]
  suffices WP w scatterRootCode x fun y t => ∃ slotTrees' maxDeg',
      t + slotCredit * slotTrees'.length ≤ 63 + slotCredit * slotTrees₀.length ∧
      y.Bounded w ∧ BaseRegs n base y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      y.regs maxDegReg = maxDeg' ∧
      Consolidated sz st (RawState.ofData n base y)
        (forestNodes (T₀ :: slotTrees₀)) slotTrees' maxDeg' by
    obtain ⟨y, t, he, slotTrees', maxDeg', ht, hby, hbry, hmod, hymd, hc⟩ := this
    exact ⟨y, slotTrees', maxDeg', t, he, ht, hby, hbry, hmod,
      fun r hr => he.regs_eq (scatterRootCode_preserves r hr), hymd, hc⟩
  unfold scatterRootCode
  wram_exec [hfit, hbr.regs_degBase, hbr.regs_consBase, hx_ic, hm_du0, hm_cd0]
  refine WP.name fun x1 hx1 => ?_
  have hb1 : x1.Bounded w := by
    subst hx1
    have : Fits w (st.cons T₀.deg) := hm_cd0 ▸ hb.2 _
    wram_bounded <;> exact hfit _ (by omega)
  have hbr1 : BaseRegs n base x1 := by subst hx1; wram_simp [BaseRegs.set_iff, hbr]
  have hst1 : RawState.ofData n base x1 = st := by
    subst hx1; wram_simp [ofData_set_scratch, ← hst_def]
  obtain ⟨z_lp, T_f, slotTrees_f, curD_f, t_lp, he_lp, ht_lp, hnc_lp, hbz, hbrz, hmod_lp,
    hlow_lp, hdeg_f, hs4_lp, hcd_lp, hs3_lp, hP_f, hback⟩ :=
    scatterLoop_exec slotTrees₀.length rfl hb1 hbr1 (by rw [hst1]; exact hP) rfl
      (by subst hx1; wram_simp) (by subst hx1; wram_simp)
      (by subst hx1; wram_simp [hst1])
  rw [hst1] at hback
  have hmd_lp : z_lp.regs maxDegReg = maxDeg₀ :=
    (hlow_lp maxDegReg (by decide)).trans (by subst hx1; wram_simp [hx_md])
  have hdf_bds := hP_f.deg_bounds
  rw [hdeg_f] at hdf_bds
  have hdf_le_n : curD_f ≤ n := by omega
  have hcons_f_zero : (RawState.ofData n base z_lp).cons curD_f = 0 := by
    rw [Cond.Holds, hbrz.regs_zeroP, hs3_lp] at hnc_lp
    omega
  have hnone_f : ∀ R ∈ slotTrees_f, R.deg ≠ curD_f := by
    rcases hP_f.table.lookup hdf_le_n with ⟨_, hnone⟩ | ⟨_, _, _, hce, _, _⟩
    · exact hnone
    · omega
  have huf_lt := T_f.root.isLt
  have hmod_x_zlp : Modifies (Block.mk base (space n)).footprint x.mem z_lp.mem := by
    subst hx1; exact hmod_lp
  refine WP.of_execWithin he_lp ?_
  refine WP.bounded hbz ?_
  wram_exec [hfit, hbrz.regs_consBase, hbrz.regs_zeroP, hbrz.regs_oneP, hs4_lp, hcd_lp, hmd_lp]
  all_goals
    intro hby
    refine ⟨T_f :: slotTrees_f, max maxDeg₀ curD_f,
      by simp only [List.length_cons, slotCredit] at ht_lp ⊢; omega,
      hby, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbrz],
      modifies_block_trans hmod_x_zlp
        (Modifies.block_iff.2 fun addr haddr => by
          have := out_of_footprint n base haddr; wram_simp),
      by wram_simp [hmd_lp, hcd_lp]; omega, ?_⟩
    wram_simp [ofData_write_cons hdf_le_n, ofData_set_scratch]
    refine hback ?_
    rw [← hdeg_f]
    exact hP_f.place (hdeg_f ▸ hnone_f)

/-! ## Consolidation scatter loops (`childScatterLoop` and `rootScatterLoop`) -/

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
    ⟪scatterRootCode⟫;
    iterCur ← iterNxt;
    remReg ← remReg - oneP
  ]

private abbrev childScatterLoop : Code .exact rFib :=
  .loop (.lt zeroP remReg) childScatterBody

private theorem childScatterLoop_preserves :
    ∀ r : Fin rFib, r.val < 30 → r ≠ numMarkedReg → childScatterLoop.Preserves r := by
  decide +kernel

/-- Phase A1 loop: walks the children `rest` along their `right` pointers, clears each one's `par`
and `mark` (decrementing `numMarkedReg` when it was marked), and scatters it into `cons`. The
result is `Consolidated`; the forest reasoning is `Scattering.unmark`, `Scattering.placing` and
`Scattering.step`. -/
private theorem scatterChildrenLoop_exec {n sz base w : ℕ} {z : Fin n} :
    ∀ (rest : List (FHTree n)) (a : Data rFib) (slotTrees : List (FHTree n)) (maxDeg : ℕ),
      a.Bounded w → BaseRegs n base a →
      Scattering sz z true (RawState.ofData n base a) slotTrees rest maxDeg →
      a.regs remReg = rest.length →
      a.regs maxDegReg = maxDeg →
      (∀ y ∈ (rest.map FHTree.root).head?, a.regs iterCur = y.val) →
      ∃ b slotTrees' maxDeg' t,
        ExecWithin w childScatterLoop a b t ∧
        t + slotCredit * slotTrees'.length ≤
          2 + 76 * rest.length + slotCredit * slotTrees.length ∧
        b.Bounded w ∧ BaseRegs n base b ∧
        Modifies (Block.mk base (space n)).footprint a.mem b.mem ∧
        (∀ r : Fin rFib, r.val < 30 → r ≠ numMarkedReg → b.regs r = a.regs r) ∧
        b.regs maxDegReg = maxDeg' ∧
        Consolidated sz (RawState.ofData n base a) (RawState.ofData n base b)
          (forestNodes (slotTrees ++ rest)) slotTrees' maxDeg'
  | [], a, slotTrees, maxDeg, hb, hbr, h, hrem, hmd, _ => by
    have hc : ¬(Cond.lt zeroP remReg).Holds a := by
      simp only [Cond.Holds, hbr.regs_zeroP, hrem, List.length_nil, Nat.lt_irrefl,
        not_false_eq_true]
    exact ⟨a, slotTrees, maxDeg, 2, ExecWithin.loop_exit hc, by omega, hb, hbr,
      Modifies.refl _ _, fun _ _ _ => rfl, hmd, h.done⟩
  | T_u :: c_tl, a, slotTrees, maxDeg, hb, hbr, h, hrem, hmd, hic => by
    set st := RawState.ofData n base a with hst_def
    have hfit := hbr.fits_of_le hb
    have hc : (Cond.lt zeroP remReg).Holds a := by
      simp only [Cond.Holds, hbr.regs_zeroP, hrem, List.length_cons]; omega
    have hu_ic : a.regs iterCur = T_u.root.val := hic T_u.root rfl
    have hu_lt := T_u.root.isLt
    have hTu_sub : ValidSubtree st none T_u := h.valid T_u List.mem_cons_self
    have hu_bds : st.inHeap T_u.root ≠ 0 ∧ st.mark T_u.root ≤ 1 :=
      ⟨h.inHeap _ (List.mem_append_left _ T_u.root_mem_nodes), ValidSubtree.mark_root_le hTu_sub⟩
    have hnm : st.numMarked = markedCount st := h.numMarked
    have hnm_le : st.numMarked ≤ n := hnm ▸ markedCount_le_n st
    obtain ⟨h₁, hT₁, hsc₁⟩ := h.unmark
    have hm_r : a.mem (base + 4 * n + T_u.root.val) = st.right T_u.root := rfl
    have hm_mk : a.mem (base + 6 * n + T_u.root.val) = st.mark T_u.root := rfl
    have hnm_reg : a.regs numMarkedReg = st.numMarked := rfl
    have hbody : WP w childScatterBody a fun a_next t_b =>
        ∃ slotTrees_1 maxDeg_1,
          t_b + slotCredit * slotTrees_1.length ≤ 74 + slotCredit * slotTrees.length ∧
          a_next.Bounded w ∧ BaseRegs n base a_next ∧
          Modifies (Block.mk base (space n)).footprint a.mem a_next.mem ∧
          a_next.regs remReg = c_tl.length ∧
          a_next.regs maxDegReg = maxDeg_1 ∧
          (∀ y ∈ (c_tl.map FHTree.root).head?, a_next.regs iterCur = y.val) ∧
          Scattering sz z true (RawState.ofData n base a_next) slotTrees_1 c_tl maxDeg_1 ∧
          (∀ {st' : RawState n} {slots' : List (FHTree n)} {md' : ℕ},
            Consolidated sz (RawState.ofData n base a_next) st'
              (forestNodes (slotTrees_1 ++ c_tl)) slots' md' →
            Consolidated sz st st' (forestNodes (slotTrees ++ (T_u :: c_tl))) slots' md') := by
      unfold childScatterBody
      wram_exec -split [hfit, hbr.regs_rightBase, hbr.regs_parBase, hbr.regs_markBase,
        hbr.regs_zeroP, hu_ic, hm_r, hm_mk]
      refine WP.cut (fun a_mid t_m => t_m ≤ 3 ∧ a_mid.Bounded w ∧ BaseRegs n base a_mid ∧
          Modifies (Block.mk base (space n)).footprint a.mem a_mid.mem ∧
          a_mid.regs iterCur = T_u.root.val ∧
          a_mid.regs iterNxt = st.right T_u.root ∧
          a_mid.regs remReg = c_tl.length + 1 ∧
          a_mid.regs maxDegReg = maxDeg ∧
          RawState.ofData n base a_mid = unmarkState st T_u.root)
        (WP.bounded (by
          have : Fits w (st.right T_u.root) := hm_r ▸ hb.2 _
          have : Fits w (st.mark T_u.root) := hm_mk ▸ hb.2 _
          wram_bounded <;> exact hfit _ (by omega)) ?_) ?_
      · by_cases hmk_pos : 0 < st.mark T_u.root
        · have hu_in_mk : T_u.root ∈ markedSet st := by
            simp only [markedSet, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hu_bds.1, by omega⟩
          have hnm_pos : 1 ≤ st.numMarked := hnm ▸ Finset.card_pos.mpr ⟨_, hu_in_mk⟩
          have hmk1 : st.mark T_u.root = 1 := by omega
          wram_exec [hfit, hbr.regs_zeroP, hbr.regs_oneP, hnm_reg, hmk_pos]
          intro hb_mid
          refine ⟨by omega, hb_mid, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr],
            Modifies.block_iff.2 fun addr haddr => by
              have := out_of_footprint n base haddr; wram_simp,
            by wram_simp [hu_ic], by wram_simp,
            by wram_simp [hrem, List.length_cons], by wram_simp [hmd], ?_⟩
          wram_simp [unmarkState, hmk1, ofData_set_numMarked, ofData_write_mark, ofData_write_par,
            ofData_set_scratch, ← hst_def]
        · have hmk0 : st.mark T_u.root = 0 := by omega
          have hupd : Function.update st.mark T_u.root 0 = st.mark := by
            rw [← hmk0, Function.update_eq_self]
          wram_exec [hfit, hbr.regs_zeroP, hmk0]
          intro hb_mid
          refine ⟨by omega, hb_mid, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr],
            Modifies.block_iff.2 fun addr haddr => by
              have := out_of_footprint n base haddr; wram_simp,
            by wram_simp [hu_ic], by wram_simp,
            by wram_simp [hrem, List.length_cons], by wram_simp [hmd], ?_⟩
          wram_simp [unmarkState, hmk0, Nat.sub_zero, hupd, ofData_write_par, ofData_set_scratch,
            ← hst_def]
      rintro a_mid t_m ⟨ht_m, hb_mid, hbr_mid, hmod_mid, hmid_ic, hmid_nxt, hmid_rem, hmid_md,
        hst_mid⟩
      obtain ⟨a_sc, slotTrees_1, maxDeg_1, t_sc, he3, ht_sc, hb_sc, hbr_sc, hmod3, hlow_sc,
        hmd_sc, hc₁⟩ :=
        scatterRootCode_exec hb_mid hbr_mid (by rw [hst_mid]; exact h₁.placing hT₁) hmid_ic hmid_md
      rw [hst_mid] at hc₁
      obtain ⟨h₂, hback₂⟩ := h₁.step hc₁
      have hsc_nxt : a_sc.regs iterNxt = st.right T_u.root :=
        (hlow_sc iterNxt (by decide)).trans hmid_nxt
      have hsc_rem : a_sc.regs remReg = c_tl.length + 1 :=
        (hlow_sc remReg (by decide)).trans hmid_rem
      apply WP.seq
      refine WP.of_execWithin he3 ?_
      refine WP.bounded hb_sc ?_
      have hfit_rem : Fits w c_tl.length := (hsc_rem ▸ hb_sc.1 remReg).of_le (by omega)
      wram_exec [hfit_rem, hbr_sc.regs_oneP, hsc_nxt, hsc_rem]
      intro hb_next
      refine ⟨slotTrees_1, maxDeg_1, by omega, hb_next,
        by wram_simp [BaseRegs.set_iff, hbr_sc],
        modifies_block_trans hmod_mid hmod3,
        by wram_simp, by wram_simp [hmd_sc],
        fun y hy => by wram_simp; exact RightChain.right_head h.chain y hy,
        by wram_simp [ofData_set_scratch]; exact h₂,
        fun hc' => ?_⟩
      wram_simp [ofData_set_scratch] at hc'
      exact (hback₂ hc').pre hsc₁ (.refl _)
    obtain ⟨a_next, t_b, he_b, slotTrees_1, maxDeg_1, ht_b, hb_next, hbr_next, hmod_b,
      hrem_next, hmd_next, hic_next, h₂, hback_b⟩ := hbody
    obtain ⟨b, slotTrees', maxDeg', t_tl, he_tl, ht_tl, hb_b, hbr_b, hmod_tl, _, hmd_b, hc'⟩ :=
      scatterChildrenLoop_exec c_tl a_next slotTrees_1 maxDeg_1 hb_next hbr_next h₂
        hrem_next hmd_next hic_next
    have he_all : ExecWithin w childScatterLoop a b (t_b + t_tl + 2) :=
      ExecWithin.loop_iter hc he_b he_tl
    exact ⟨b, slotTrees', maxDeg', t_b + t_tl + 2, he_all,
      by simp only [List.length_cons] at ht_tl ⊢; omega,
      hb_b, hbr_b, modifies_block_trans hmod_b hmod_tl,
      fun r hr hne_nm => he_all.regs_eq (childScatterLoop_preserves r hr hne_nm),
      hmd_b, hback_b hc'⟩

private abbrev rootScatterBody : Code .exact rFib :=
  ram_exact[
    s0 ← rightBase + iterCur;
    iterNxt ← *s0;
    ⟪scatterRootCode⟫;
    iterCur ← iterNxt;
    remReg ← remReg - oneP
  ]

private abbrev rootScatterLoop : Code .exact rFib :=
  .loop (.lt zeroP remReg) rootScatterBody

private theorem rootScatterLoop_preserves :
    ∀ r : Fin rFib, r.val < 30 → rootScatterLoop.Preserves r := by
  decide +kernel

/-- Phase A2 loop: walks the root trees `rest` along their `right` pointers and scatters each
into `cons`. The result is `Consolidated`; the forest reasoning is `Scattering.validRoot`,
`Scattering.placing` and `Scattering.step`. -/
private theorem scatterRootsLoop_exec {n sz base w : ℕ} {z : Fin n} :
    ∀ (rest : List (FHTree n)) (a : Data rFib) (slotTrees : List (FHTree n)) (maxDeg : ℕ),
      a.Bounded w → BaseRegs n base a →
      Scattering sz z false (RawState.ofData n base a) slotTrees rest maxDeg →
      a.regs remReg = rest.length →
      a.regs maxDegReg = maxDeg →
      (∀ y ∈ (rest.map FHTree.root).head?, a.regs iterCur = y.val) →
      ∃ b slotTrees' maxDeg' t,
        ExecWithin w rootScatterLoop a b t ∧
        t + slotCredit * slotTrees'.length ≤
          2 + 69 * rest.length + slotCredit * slotTrees.length ∧
        b.Bounded w ∧ BaseRegs n base b ∧
        Modifies (Block.mk base (space n)).footprint a.mem b.mem ∧
        (∀ r : Fin rFib, r.val < 30 → b.regs r = a.regs r) ∧
        b.regs maxDegReg = maxDeg' ∧
        Consolidated sz (RawState.ofData n base a) (RawState.ofData n base b)
          (forestNodes (slotTrees ++ rest)) slotTrees' maxDeg'
  | [], a, slotTrees, maxDeg, hb, hbr, h, hrem, hmd, _ => by
    have hc : ¬(Cond.lt zeroP remReg).Holds a := by
      simp only [Cond.Holds, hbr.regs_zeroP, hrem, List.length_nil, Nat.lt_irrefl,
        not_false_eq_true]
    exact ⟨a, slotTrees, maxDeg, 2, ExecWithin.loop_exit hc, by omega, hb, hbr,
      Modifies.refl _ _, fun _ _ => rfl, hmd, h.done⟩
  | T_u :: r_tl, a, slotTrees, maxDeg, hb, hbr, h, hrem, hmd, hic => by
    set st := RawState.ofData n base a with hst_def
    have hfit := hbr.fits_of_le hb
    have hc : (Cond.lt zeroP remReg).Holds a := by
      simp only [Cond.Holds, hbr.regs_zeroP, hrem, List.length_cons]; omega
    have hu_ic : a.regs iterCur = T_u.root.val := hic T_u.root rfl
    have hu_lt := T_u.root.isLt
    have hm_r : a.mem (base + 4 * n + T_u.root.val) = st.right T_u.root := rfl
    have hbody : WP w rootScatterBody a fun a_next t_b =>
        ∃ slotTrees_1 maxDeg_1,
          t_b + slotCredit * slotTrees_1.length ≤ 67 + slotCredit * slotTrees.length ∧
          a_next.Bounded w ∧ BaseRegs n base a_next ∧
          Modifies (Block.mk base (space n)).footprint a.mem a_next.mem ∧
          a_next.regs remReg = r_tl.length ∧
          a_next.regs maxDegReg = maxDeg_1 ∧
          (∀ y ∈ (r_tl.map FHTree.root).head?, a_next.regs iterCur = y.val) ∧
          Scattering sz z false (RawState.ofData n base a_next) slotTrees_1 r_tl maxDeg_1 ∧
          (∀ {st' : RawState n} {slots' : List (FHTree n)} {md' : ℕ},
            Consolidated sz (RawState.ofData n base a_next) st'
              (forestNodes (slotTrees_1 ++ r_tl)) slots' md' →
            Consolidated sz st st' (forestNodes (slotTrees ++ (T_u :: r_tl))) slots' md') := by
      unfold rootScatterBody
      wram_exec [hfit, hbr.regs_rightBase, hu_ic, hm_r]
      refine WP.name fun a1 ha1 => ?_
      have hb1 : a1.Bounded w := by
        subst ha1
        have : Fits w (st.right T_u.root) := hm_r ▸ hb.2 _
        wram_bounded; exact hfit _ (by omega)
      have hbr1 : BaseRegs n base a1 := by subst ha1; wram_simp [BaseRegs.set_iff, hbr]
      have hst1 : RawState.ofData n base a1 = st := by
        subst ha1; wram_simp [ofData_set_scratch, ← hst_def]
      obtain ⟨a_sc, slotTrees_1, maxDeg_1, t_sc, he2, ht_sc, hb_sc, hbr_sc, hmod2, hlow_sc,
        hmd_sc, hc₁⟩ :=
        scatterRootCode_exec hb1 hbr1 (by rw [hst1]; exact h.placing h.validRoot)
          (by subst ha1; wram_simp [hu_ic]) (by subst ha1; wram_simp [hmd])
      rw [hst1] at hc₁
      obtain ⟨h₂, hback₂⟩ := h.step hc₁
      have hsc_nxt : a_sc.regs iterNxt = st.right T_u.root :=
        (hlow_sc iterNxt (by decide)).trans (by subst ha1; wram_simp)
      have hsc_rem : a_sc.regs remReg = r_tl.length + 1 :=
        (hlow_sc remReg (by decide)).trans (by subst ha1; wram_simp [hrem, List.length_cons])
      have hmod_a_asc : Modifies (Block.mk base (space n)).footprint a.mem a_sc.mem := by
        subst ha1; exact hmod2
      refine WP.of_execWithin he2 ?_
      refine WP.bounded hb_sc ?_
      have hfit_rem : Fits w r_tl.length := (hsc_rem ▸ hb_sc.1 remReg).of_le (by omega)
      wram_exec [hfit_rem, hbr_sc.regs_oneP, hsc_nxt, hsc_rem]
      intro hb_next
      refine ⟨slotTrees_1, maxDeg_1, by omega, hb_next,
        by wram_simp [BaseRegs.set_iff, hbr_sc], hmod_a_asc,
        by wram_simp, by wram_simp [hmd_sc],
        fun y hy => by wram_simp; exact RightChain.right_head h.chain y hy,
        by wram_simp [ofData_set_scratch]; exact h₂,
        fun hc' => by wram_simp [ofData_set_scratch] at hc'; exact hback₂ hc'⟩
    obtain ⟨a_next, t_b, he_b, slotTrees_1, maxDeg_1, ht_b, hb_next, hbr_next, hmod_b,
      hrem_next, hmd_next, hic_next, h₂, hback_b⟩ := hbody
    obtain ⟨b, slotTrees', maxDeg', t_tl, he_tl, ht_tl, hb_b, hbr_b, hmod_tl, _, hmd_b, hc'⟩ :=
      scatterRootsLoop_exec r_tl a_next slotTrees_1 maxDeg_1 hb_next hbr_next h₂
        hrem_next hmd_next hic_next
    have he_all : ExecWithin w rootScatterLoop a b (t_b + t_tl + 2) :=
      ExecWithin.loop_iter hc he_b he_tl
    exact ⟨b, slotTrees', maxDeg', t_b + t_tl + 2, he_all,
      by simp only [List.length_cons] at ht_tl ⊢; omega,
      hb_b, hbr_b, modifies_block_trans hmod_b hmod_tl,
      fun r hr => he_all.regs_eq (rootScatterLoop_preserves r hr),
      hmd_b, hback_b hc'⟩

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

/-- Phase B loop: scans `curD` up to `maxDeg + 1` (`curD + rem = maxDeg + 1`), clearing every
occupied `cons[curD]` and adding its tree to the root list with `addRootAndUpdateMin iterCur`. The
result is `Gathered`; the forest reasoning is `Gathering.take` and `Gathering.done`. -/
private theorem gatherSlotsLoop_exec {n sz base w maxDeg : ℕ} (rem : ℕ) :
    ∀ (a : Data rFib) (curD : ℕ) (slotTrees accRoots : List (FHTree n)),
      curD + rem = maxDeg + 1 →
      a.Bounded w → BaseRegs n base a →
      a.regs curDReg = curD →
      a.regs maxDegReg = maxDeg + 1 →
      Gathering sz (RawState.ofData n base a) accRoots slotTrees maxDeg →
      (∀ T ∈ slotTrees, curD ≤ T.deg) →
      ∃ b finalRoots t,
        ExecWithin w gatherSlotsLoop a b t ∧
        t + unitCredit * finalRoots.length ≤
          2 + 116 * rem + unitCredit * accRoots.length ∧
        b.Bounded w ∧ BaseRegs n base b ∧
        Modifies (Block.mk base (space n)).footprint a.mem b.mem ∧
        (∀ r : Fin rFib, r.val < 30 → r ≠ minRootReg → r ≠ numRootsReg → b.regs r = a.regs r) ∧
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
    exact ⟨a, accRoots, 2, ExecWithin.loop_exit hc, by omega, hb, hbr,
      Modifies.refl _ _, fun _ _ _ _ => rfl, by simpa only [List.append_nil] using hG⟩
  | succ rem' ih =>
    intro a curD slotTrees accRoots hsum hb hbr hcurD hmaxD h hge
    set st := RawState.ofData n base a with hst_def
    have hfit := hbr.fits_of_le hb
    have hd_le_n : curD ≤ n := SlotInv.le_n h.table (by omega)
    have hc_loop : (Cond.lt curDReg maxDegReg).Holds a := by
      simp only [Cond.Holds, hcurD, hmaxD]; omega
    have hm_c : a.mem (base + 8 * n + curD) = st.cons curD := by
      simp only [st, RawState.ofData, hd_le_n, ↓reduceIte]
    rcases h.table.lookup hd_le_n with ⟨hc0, hnone⟩ |
        ⟨idx, hidx, hslot_deg, hcons_eq, _, hno_other⟩
    · -- Unoccupied slot (`st.cons curD = 0`)
      have hfit_cd1 : Fits w (curD + 1) := (hmaxD ▸ hb.1 maxDegReg).of_le (by omega)
      have hbody : WP w gatherSlotBody a fun a3 t_b =>
          t_b ≤ 6 ∧ a3.Bounded w ∧ BaseRegs n base a3 ∧ a3.mem = a.mem ∧
          a3.regs curDReg = curD + 1 ∧ a3.regs maxDegReg = maxDeg + 1 ∧
          RawState.ofData n base a3 = st := by
        unfold gatherSlotBody
        refine WP.bounded hb ?_
        wram_exec [hfit, hfit_cd1, hbr.regs_consBase, hbr.regs_zeroP, hbr.regs_oneP, hcurD, hm_c,
          hc0]
        intro hb3
        exact ⟨by omega, hb3, by wram_simp [BaseRegs.set_iff, hbr], rfl,
          by wram_simp, by wram_simp [hmaxD], by wram_simp [ofData_set_scratch, ← hst_def]⟩
      obtain ⟨a3, t_b, he_body, ht_b, hb3, hbr3, hmem3, ha3_cd, ha3_md, hst3⟩ := hbody
      obtain ⟨b, finalRoots, t_tl, he_tl, ht_tl, hb_b, hbr_b, hmod_tl, _, hG⟩ :=
        ih a3 (curD + 1) slotTrees accRoots (by omega) hb3 hbr3 ha3_cd ha3_md
          (by rw [hst3]; exact h) fun T hT => by have := hge T hT; have := hnone T hT; omega
      rw [hst3] at hG
      rw [hmem3] at hmod_tl
      have he_all : ExecWithin w gatherSlotsLoop a b (t_b + t_tl + 2) :=
        ExecWithin.loop_iter hc_loop he_body he_tl
      exact ⟨b, finalRoots, t_b + t_tl + 2, he_all, by omega, hb_b, hbr_b, hmod_tl,
        fun r hr hrm hrnr => he_all.regs_eq (gatherSlotsLoop_preserves r hr hrm hrnr), hG⟩
    · -- Occupied slot (`slotTrees[idx]`)
      have hu_lt := slotTrees[idx].root.isLt
      have hbody : WP w gatherSlotBody a fun a5 t_b =>
          t_b ≤ 34 ∧ a5.Bounded w ∧ BaseRegs n base a5 ∧
          Modifies (Block.mk base (space n)).footprint a.mem a5.mem ∧
          a5.regs curDReg = curD + 1 ∧ a5.regs maxDegReg = maxDeg + 1 ∧
          Gathering sz (RawState.ofData n base a5) (slotTrees[idx] :: accRoots)
            (slotTrees.eraseIdx idx) maxDeg ∧
          (∀ {st' : RawState n} {final : List (FHTree n)},
            Gathered (RawState.ofData n base a5) st'
              (forestNodes ((slotTrees[idx] :: accRoots) ++ slotTrees.eraseIdx idx)) final →
            Gathered st st' (forestNodes (accRoots ++ slotTrees)) final) := by
        unfold gatherSlotBody
        wram_exec [hfit, hbr.regs_consBase, hbr.regs_zeroP, hbr.regs_oneP, hcurD, hm_c, hcons_eq]
        refine WP.name fun a3 ha3 => ?_
        have hb3 : a3.Bounded w := by subst ha3; wram_bounded <;> exact hfit _ (by omega)
        have hbr3 : BaseRegs n base a3 := by
          subst ha3; wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr]
        have hst3 : RawState.ofData n base a3 =
            { st with cons := Function.update st.cons curD 0 } := by
          subst ha3
          wram_simp [ofData_write_cons hd_le_n, ofData_set_scratch, ← hst_def]
        have hmod_a_a3 : Modifies (Block.mk base (space n)).footprint a.mem a3.mem := by
          subst ha3
          exact Modifies.block_iff.2 fun addr haddr => by
            have := out_of_footprint n base haddr; wram_simp
        obtain ⟨hroot, hnr, hnext⟩ := h.take hidx hslot_deg hd_le_n hno_other hst3
        obtain ⟨a4, he_add, hbr4, hmod_add, hadd⟩ :=
          addRootAndUpdateMin_exec (uReg := iterCur) (u := slotTrees[idx].root) hb3 hbr3
            ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
            (by subst ha3; wram_simp) hroot hnr
        obtain ⟨h₂, hback⟩ := hnext hadd
        have hb4 : a4.Bounded w := he_add.bounded hb3
        have ha4_cd : a4.regs curDReg = curD := by
          rw [he_add.regs_eq (addRootAndUpdateMin_preserves (uReg := iterCur)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide))]
          subst ha3; wram_simp [hcurD]
        have ha4_md : a4.regs maxDegReg = maxDeg + 1 := by
          rw [he_add.regs_eq (addRootAndUpdateMin_preserves (uReg := iterCur)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide))]
          subst ha3; wram_simp [hmaxD]
        refine WP.of_execWithin he_add ?_
        refine WP.bounded hb4 ?_
        wram_exec [hfit, hbr4.regs_oneP, ha4_cd]
        intro hb5
        exact ⟨by omega, hb5, by wram_simp [BaseRegs.set_iff, hbr4],
          modifies_block_trans hmod_a_a3 hmod_add,
          by wram_simp, by wram_simp [ha4_md],
          by wram_simp [ofData_set_scratch]; exact h₂,
          fun hG => by wram_simp [ofData_set_scratch] at hG; exact hback hG⟩
      obtain ⟨a5, t_b, he_body, ht_b, hb5, hbr5, hmod5, ha5_cd, ha5_md, h₂, hback⟩ := hbody
      obtain ⟨b, finalRoots, t_tl, he_tl, ht_tl, hb_b, hbr_b, hmod_tl, _, hG⟩ :=
        ih a5 (curD + 1) (slotTrees.eraseIdx idx) (slotTrees[idx] :: accRoots) (by omega) hb5 hbr5
          ha5_cd ha5_md h₂ fun R hR => by
            have := hge R (List.mem_of_mem_eraseIdx hR)
            have := hno_other R hR
            omega
      have he_all : ExecWithin w gatherSlotsLoop a b (t_b + t_tl + 2) :=
        ExecWithin.loop_iter hc_loop he_body he_tl
      exact ⟨b, finalRoots, t_b + t_tl + 2, he_all,
        by simp only [List.length_cons, unitCredit] at ht_tl ⊢; omega,
        hb_b, hbr_b, modifies_block_trans hmod5 hmod_tl,
        fun r hr hrm hrnr => he_all.regs_eq (gatherSlotsLoop_preserves r hr hrm hrnr),
        hback hG⟩

/-! ## `extractMinCode` correctness and `O(log n)` amortized bound -/

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
  change WP w extractMinCode x fun y t =>
    code.decode (n := n) (K_max := K_max) .extractMin y.regs =
      some ((indexedMinPQSpec n K_max).stepFn s .extractMin).2 ∧
    FibInv n K_max w base ((indexedMinPQSpec n K_max).stepFn s .extractMin).1 y ∧
    Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
    t + potential y ≤ 410 * (Nat.log 2 (IndexedMinPQ.dom s).card + 1) + potential x
  unfold extractMinCode
  by_cases hm0 : st.minRoot = 0
  · -- Empty heap (`minRoot = 0`)
    have hm0_reg : x.regs minRootReg = 0 := hm0
    obtain ⟨_, hfind⟩ := hraw.findMin_eq_none hm0
    refine WP.bounded hb ?_
    wram_exec [hbr.regs_zeroP, hm0_reg]
    intro hby
    refine ⟨by wram_simp [PQCode.decode, code, indexedMinPQSpec, IndexedMinPQ.step,
        StateTransitionSpec.stepFn, hfind],
      by simp only [indexedMinPQSpec, IndexedMinPQ.step, StateTransitionSpec.stepFn, hfind]
         exact ⟨hby, hbr.set_non_base (by decide) 0,
           (ofData_set_scratch x (by decide : 17 ≤ outFlag.val) 0).symm ▸ hraw⟩,
      Modifies.refl _ _, ?_⟩
    rw [potential_set_scratch x (by decide : 17 ≤ outFlag.val) 0]
    omega
  · -- Non-empty heap (`st.minRoot = z.val + 1`)
    rcases FibonacciHeap.minRoot_cases hraw with h0 | ⟨z, -, hmin_z, -⟩
    · exact absurd h0 hm0
    obtain ⟨cs, E, hD⟩ := FibonacciHeap.FibRawInv.detach hraw hmin_z
    have hz_lt := z.isLt
    have hfind := hD.findMin
    have hz_dom : z ∈ IndexedMinPQ.dom s := IndexedMinPQ.findMin_mem_dom hfind
    have hsz_pos : 1 ≤ st.sz := by
      have : 0 < (IndexedMinPQ.dom s).card := Finset.card_pos.mpr ⟨z, hz_dom⟩
      rw [hD.sz]; omega
    have hsz_le_n : st.sz ≤ n := hraw.bounds.1
    have hmin_reg : x.regs minRootReg = z.val + 1 := hmin_z
    have hsz_reg : x.regs szReg = st.sz := rfl
    have hkz_mem : x.mem (base + z.val) = st.key z := rfl
    have hrz_mem : x.mem (base + 4 * n + z.val) = st.right z := rfl
    have hdz_mem : x.mem (base + 5 * n + z.val) = st.deg z := rfl
    -- Preamble (13 instructions), stopping at `if zeroP < remReg`.
    wram_exec -split [hfit, hbr.regs_baseReg, hbr.regs_inBase, hbr.regs_rightBase,
      hbr.regs_degBase, hbr.regs_zeroP, hbr.regs_oneP, hmin_reg, hsz_reg,
      hkz_mem, hrz_mem, hdz_mem]
    -- Phase A1: scatter children `cs` of `z`.
    refine WP.cut (fun x_A1 t_A1 => ∃ slotTrees_1 maxDeg_1,
        t_A1 + slotCredit * slotTrees_1.length ≤ 7 + 76 * cs.length ∧
        x_A1.Bounded w ∧ BaseRegs n base x_A1 ∧
        Modifies (Block.mk base (space n)).footprint x.mem x_A1.mem ∧
        x_A1.regs outFlag = 1 ∧ x_A1.regs outV = z.val ∧ x_A1.regs outK = st.key z ∧
        x_A1.regs pReg = st.right z ∧ x_A1.regs maxDegReg = maxDeg_1 ∧
        Consolidated (forestNodes (cs ++ E)).length (detachState st z)
          (RawState.ofData n base x_A1) (forestNodes ([] ++ cs)) slotTrees_1 maxDeg_1)
      (WP.bounded (by
        have : Fits w (st.key z) := hkz_mem ▸ hb.2 _
        have : Fits w (st.right z) := hrz_mem ▸ hb.2 _
        have : Fits w (st.deg z) := hdz_mem ▸ hb.2 _
        wram_bounded <;> exact hfit _ (by omega)) ?_) ?_
    · cases cs with
      | nil =>
        have hdz0 : st.deg z = 0 := by simpa only [List.length_nil] using hD.deg
        wram_exec [hbr.regs_zeroP, hdz0]
        intro hb_A1
        refine ⟨[], 0, by simp only [List.length_nil, Nat.mul_zero]; omega,
          hb_A1, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr],
          Modifies.block_iff.2 fun addr haddr => by
            have := out_of_footprint n base haddr; wram_simp,
          by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp, ?_⟩
        wram_simp [detachState, ofData_set_sz, ofData_write_inHeap, ofData_set_scratch, ← hst_def]
        exact hD.scatterChildren.done
      | cons C₀ cs₀ =>
        have hcz : st.child z = C₀.root.val + 1 := hD.child C₀.root rfl
        have hhc_lt := C₀.root.isLt
        have hcz_mem : x.mem (base + 2 * n + z.val) = C₀.root.val + 1 := hcz
        have hdz_pos : 0 < st.deg z := by rw [hD.deg, List.length_cons]; omega
        wram_exec [hfit, hbr.regs_childBase, hbr.regs_zeroP, hbr.regs_oneP, hdz_pos, hcz_mem]
        refine WP.name fun x_c0 hx_c0 => ?_
        have hb_c0 : x_c0.Bounded w := by
          subst hx_c0
          have : Fits w (st.key z) := hkz_mem ▸ hb.2 _
          have : Fits w (st.right z) := hrz_mem ▸ hb.2 _
          have : Fits w (st.deg z) := hdz_mem ▸ hb.2 _
          wram_bounded <;> exact hfit _ (by omega)
        have hbr_c0 : BaseRegs n base x_c0 := by
          subst hx_c0; wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr]
        have hst_c0 : RawState.ofData n base x_c0 = detachState st z := by
          subst hx_c0
          wram_simp [detachState, ofData_set_sz, ofData_write_inHeap, ofData_set_scratch, ← hst_def]
        have hmod_pre : Modifies (Block.mk base (space n)).footprint x.mem x_c0.mem := by
          subst hx_c0
          exact Modifies.block_iff.2 fun addr haddr => by
            have := out_of_footprint n base haddr; wram_simp
        obtain ⟨x_A1, slotTrees_1, maxDeg_1, t_sc1, he_sc1, ht_sc1, hb_A1, hbr_A1, hmod_sc1,
          hregs_sc1, hmd_sc1, hc_sc1⟩ :=
          scatterChildrenLoop_exec (C₀ :: cs₀) x_c0 [] 0 hb_c0 hbr_c0
            (by rw [hst_c0]; exact hD.scatterChildren)
            (by subst hx_c0; wram_simp [hD.deg])
            (by subst hx_c0; wram_simp)
            (fun y hy => by cases hy; subst hx_c0; wram_simp)
        rw [hst_c0] at hc_sc1
        refine WP.of_execWithin he_sc1 fun _ => ?_
        refine ⟨slotTrees_1, maxDeg_1,
          by simp only [slotCredit, List.length_nil] at ht_sc1 ⊢; omega,
          hb_A1, hbr_A1, modifies_block_trans hmod_pre hmod_sc1,
          (hregs_sc1 outFlag (by decide) (by decide)).trans (by subst hx_c0; wram_simp),
          (hregs_sc1 outV (by decide) (by decide)).trans (by subst hx_c0; wram_simp),
          (hregs_sc1 outK (by decide) (by decide)).trans (by subst hx_c0; wram_simp),
          (hregs_sc1 pReg (by decide) (by decide)).trans (by subst hx_c0; wram_simp),
          hmd_sc1, hc_sc1⟩
    rintro x_A1 t_A1 ⟨slotTrees_1, maxDeg_1, ht_A1, hb_A1, hbr_A1, hmod_A1,
      hA1_of, hA1_ov, hA1_ok, hA1_pr, hmd_A1, hc₁⟩
    -- Transition + Phase A2 (`rootScatterLoop`).
    have hnr_xA1 : x_A1.regs numRootsReg = E.length + 1 :=
      hc₁.scattered.numRoots.trans hD.numRoots
    have hnr_le_n : st.numRoots ≤ n := hraw.bounds.2.1
    have hr_le : E.length + 1 ≤ n := by have := hD.numRoots; omega
    wram_exec [hfit, hbr_A1.regs_oneP, hnr_xA1, hA1_pr]
    refine WP.name fun x_tr hx_tr => ?_
    have hb_tr : x_tr.Bounded w := by
      subst hx_tr
      have : Fits w (st.right z) := hrz_mem ▸ hb.2 _
      wram_bounded; exact hfit _ (by omega)
    have hbr_tr : BaseRegs n base x_tr := by subst hx_tr; wram_simp [BaseRegs.set_iff, hbr_A1]
    have hst_tr : RawState.ofData n base x_tr = RawState.ofData n base x_A1 := by
      subst hx_tr; wram_simp [ofData_set_scratch]
    obtain ⟨x_A2, slotTrees_2, maxDeg_2, t_A2, he_A2, ht_A2, hb_A2, hbr_A2, hmod_A2,
      hregs_A2, hmd_A2, hc₂⟩ :=
      scatterRootsLoop_exec E x_tr slotTrees_1 maxDeg_1 hb_tr hbr_tr
        (by rw [hst_tr]; exact hD.scatterRoots hc₁)
        (by subst hx_tr; wram_simp)
        (by subst hx_tr; wram_simp [hmd_A1])
        (fun y hy => by subst hx_tr; wram_simp; exact hD.right y hy)
    rw [hst_tr] at hc₂
    have hmod_xA1_xA2 : Modifies (Block.mk base (space n)).footprint x_A1.mem x_A2.mem := by
      subst hx_tr; exact hmod_A2
    have hA2_of : x_A2.regs outFlag = 1 :=
      (hregs_A2 outFlag (by decide)).trans (by subst hx_tr; wram_simp [hA1_of])
    have hA2_ov : x_A2.regs outV = z.val :=
      (hregs_A2 outV (by decide)).trans (by subst hx_tr; wram_simp [hA1_ov])
    have hA2_ok : x_A2.regs outK = st.key z :=
      (hregs_A2 outK (by decide)).trans (by subst hx_tr; wram_simp [hA1_ok])
    refine WP.of_execWithin he_A2 ?_
    -- Phase B preamble + `gatherSlotsLoop`.
    have hmd2_le_n : maxDeg_2 + 1 ≤ n := by
      rcases hc₂.table.2.2.2.2.2 with h0 | h2 <;> omega
    wram_exec [hfit, hbr_A2.regs_zeroP, hbr_A2.regs_oneP, hmd_A2]
    refine WP.name fun x_B0 hx_B0 => ?_
    have hb_B0 : x_B0.Bounded w := by subst hx_B0; wram_bounded <;> exact hfit _ (by omega)
    have hbr_B0 : BaseRegs n base x_B0 := by subst hx_B0; wram_simp [BaseRegs.set_iff, hbr_A2]
    have hst_B0 : RawState.ofData n base x_B0 =
        { RawState.ofData n base x_A2 with minRoot := 0, numRoots := 0 } := by
      subst hx_B0
      wram_simp [ofData_set_scratch, ofData_set_numRoots, ofData_set_minRoot]
    obtain ⟨y, finalRoots, t_B, he_B, ht_B, hb_y, hbr_y, hmod_B, hregs_B, hG⟩ :=
      gatherSlotsLoop_exec (maxDeg := maxDeg_2) (maxDeg_2 + 1) x_B0 0 slotTrees_2 [] (by omega)
        hb_B0 hbr_B0 (by subst hx_B0; wram_simp) (by subst hx_B0; wram_simp)
        (by rw [hst_B0]; exact hD.gathering hc₁ hc₂) fun _ _ => Nat.zero_le _
    rw [hst_B0] at hG
    obtain ⟨hfin, hnm_le, hmd2_log⟩ := hD.finish hc₁ hc₂ hG
    have hmod_xA2_y : Modifies (Block.mk base (space n)).footprint x_A2.mem y.mem := by
      subst hx_B0; exact hmod_B
    have hy_of : y.regs outFlag = 1 :=
      (hregs_B outFlag (by decide) (by decide) (by decide)).trans
        (by subst hx_B0; wram_simp [hA2_of])
    have hy_ov : y.regs outV = z.val :=
      (hregs_B outV (by decide) (by decide) (by decide)).trans
        (by subst hx_B0; wram_simp [hA2_ov])
    have hy_ok : y.regs outK = st.key z :=
      (hregs_B outK (by decide) (by decide) (by decide)).trans
        (by subst hx_B0; wram_simp [hA2_ok])
    refine WP.of_execWithin he_B ?_
    refine ⟨?_, ?_, modifies_block_trans hmod_A1 (modifies_block_trans hmod_xA1_xA2 hmod_xA2_y),
      ?_⟩
    · simp only [PQCode.decode, code, indexedMinPQSpec, IndexedMinPQ.step,
        StateTransitionSpec.stepFn, hfind, hy_of, hy_ov, hy_ok, one_ne_zero, ↓reduceIte,
        hz_lt, ↓reduceDIte, Fin.eta]
    · simp only [indexedMinPQSpec, IndexedMinPQ.step, StateTransitionSpec.stepFn, hfind]
      exact ⟨hb_y, hbr_y, hfin⟩
    · have hnr_x : x.regs numRootsReg = E.length + 1 := hD.numRoots
      have hnm_x : x.regs numMarkedReg = st.numMarked := rfl
      have hnr_y : y.regs numRootsReg = finalRoots.length := hG.numRoots
      have hnm_y_le : y.regs numMarkedReg ≤ st.numMarked := hnm_le
      have hdz := hD.degBound
      simp only [potential, unitCredit, slotCredit, List.length_nil, hnr_x, hnm_x, hnr_y]
        at ht_A1 ht_A2 ht_B ⊢
      omega

end Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap
