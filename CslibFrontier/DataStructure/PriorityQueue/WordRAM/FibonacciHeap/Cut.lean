/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.BasicOps
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.DecreaseKey
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Fibonacci Heap: `decreaseKey` and Cascading Cuts

This file proves the exact-Word-RAM specification `decreaseKeyCode_exec` (`O(1)` amortized time
under `potential = 80 * (numRoots + 2 * numMarked)`). The proofs step the machine code; the forest
reasoning is that of the record heap (`Cslib.DataStructure.PriorityQueue.FibonacciHeap`,
`DecreaseKey.lean`), applied to the machine state read as `RawState.ofData n base x`:

* **Single-edge cut (`cutNodeCode_raw`):** `cutNodeCode` runs in at most `36` instructions, and the
  state it leaves is `cutState`, so its effect is `CutsNode` (`cutsNode_cutState`). The potential
  drops by `80` when `cur` was marked and grows by `80` otherwise.
* **Cascading cuts (`decreaseKeyCode_exec`):** the machine writes the new key first, so the forest
  is read with the old keys as `Cascading`. Each cut is `CutsNode.cascading`, and the cascade ends
  with `Cascading.clear_root` or `Cascading.mark`. `Cascading.lowerRootKey` (after a cut) or
  `FibRawInv.lowerKey_noCut` (without one) then stores the key. `ExecWithin.loop_potential_retain`
  pays every cascading-cut iteration (`≤ 50` instructions including the loop step) out of the
  `-80` drop in `potential`; marking the stopping non-root ancestor costs `+160`, and `FibInv` is
  restored within amortized charge `330` (`335 ≤ tDec n` including dispatch).

## Main definitions

* `cutNodeCode` and `decreaseKeyCode` are defined in
  `CslibFrontier/DataStructure/PriorityQueue/WordRAM/FibonacciHeap/Program.lean`.

## Main results

* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.cutNodeCode_raw`: a single-edge cut, as
  `CutsNode`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap.decreaseKeyCode_exec`: `O(1)` amortized
  `decreaseKey` specification with cascading cuts.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci Heaps and Their Uses in Improved Network Optimization
  Algorithms*][FredmanTarjan1987]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 19][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.PriorityQueue
open Cslib.DataStructure.PriorityQueue.FibonacciHeap hiding potential

/-! ## Local framing and proof-only helpers -/

private theorem modifies_of_eq {n base : ℕ} {m₁ m₂ : ℕ → ℕ}
    (h : ∀ a, a < base ∨ base + 9 * n + 1 ≤ a → m₂ a = m₁ a) :
    Modifies (Block.mk base (space n)).footprint m₁ m₂ :=
  Modifies.block_iff.2 fun a ha => h a (out_of_footprint n base ha)

private theorem numMarked_pos_of_mark {n : ℕ} {st : RawState n} {u : Fin n}
    (hnm : st.numMarked = markedCount st) (hin : st.inHeap u ≠ 0) (hm : st.mark u ≠ 0) :
    1 ≤ st.numMarked :=
  hnm ▸ Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hin, hm⟩⟩

private theorem potential_eq_of_evalCascGuard {x y : Data rFib}
    (hreg : ∀ r : Fin rFib, r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ iterCur → y.regs r = x.regs r) :
    potential y = potential x := by
  simp only [potential, hreg numRootsReg (by decide) (by decide) (by decide) (by decide),
    hreg numMarkedReg (by decide) (by decide) (by decide) (by decide)]

/-! ## `evalCascGuard` specification -/

/-- `evalCascGuard` sets `iterCur ← 1` iff `par[cur] ≠ 0 ∧ mark[cur] ≠ 0`, and `0` otherwise, in
at most `8` instructions while preserving `BaseRegs`, `RawState.ofData`, and all registers other
than `s0, s1, s2, iterCur`. -/
theorem evalCascGuard_exec {n base w : ℕ} {x : Data rFib}
    (hb : x.Bounded w) (hbr : BaseRegs n base x) {cur : Fin n} (hz_reg : x.regs zReg = cur.val) :
    let st := RawState.ofData n base x
    let gval := if st.par cur ≠ 0 ∧ st.mark cur ≠ 0 then 1 else 0
    ∃ y, ExecWithin w evalCascGuard x y 8 ∧
      BaseRegs n base y ∧
      RawState.ofData n base y = st ∧
      y.mem = x.mem ∧
      y.regs iterCur = gval ∧
      (∀ r : Fin rFib, r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ iterCur → y.regs r = x.regs r) := by
  intro st gval
  have hfit := hbr.fits_of_le hb
  have := cur.isLt
  wram_exec [evalCascGuard,
    hfit, hbr.regs_parBase, hbr.regs_markBase, hbr.regs_zeroP, hbr.regs_oneP, hz_reg]
  all_goals refine ⟨by wram_simp [BaseRegs.set_iff, hbr], by wram_simp [ofData_set_scratch]; rfl,
    rfl, ?_, fun r h0 h1 h2 h3 => by wram_simp⟩
  all_goals wram_simp [gval, st, RawState.ofData]; split_ifs <;> omega

/-! ## `cutNodeCode` machine execution -/

private theorem cutUnlink_wp {n base w : ℕ} {x : Data rFib}
    (hb : x.Bounded w) (hbr : BaseRegs n base x) {cur p : Fin n}
    (hz_reg : x.regs zReg = cur.val) (hp_reg : x.regs pReg = p.val)
    (hdp_pos : 1 ≤ (RawState.ofData n base x).deg p)
    (hdp_le : (RawState.ofData n base x).deg p ≤ n)
    (hdp2 : 2 ≤ (RawState.ofData n base x).deg p →
      ∃ (h : Fin n) (tail : List (Fin n)),
        (RawState.ofData n base x).child p = h.val + 1 ∧
        IsCircList (RawState.ofData n base x).left (RawState.ofData n base x).right (h :: tail) ∧
        cur ∈ h :: tail ∧ 2 ≤ (h :: tail).length ∧
        ∀ u ∈ h :: tail, (RawState.ofData n base x).par u = p.val + 1) :
    let st := RawState.ofData n base x
    let post (y : Data rFib) (t : ℕ) : Prop :=
      t ≤ 13 ∧ y.Bounded w ∧ BaseRegs n base y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      (∀ r : Fin rFib, r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ s3 → r ≠ s4 → y.regs r = x.regs r) ∧
      ∃ (left₁ right₁ : Fin n → ℕ) (child₁ : ℕ),
        ((st.deg p = 1 ∧ child₁ = 0 ∧ left₁ = st.left ∧ right₁ = st.right) ∨
          (2 ≤ st.deg p ∧ ∃ r l : Fin n, st.right cur = r.val ∧ st.left cur = l.val ∧
            child₁ = r.val + 1 ∧ left₁ = Function.update st.left r l.val ∧
            right₁ = Function.update st.right l r.val)) ∧
        RawState.ofData n base y = { st with
          deg := Function.update st.deg p (st.deg p - 1)
          child := Function.update st.child p child₁
          left := left₁
          right := right₁ }
    WP w (ram_exact[
      if s1 = zeroP then [s0 ← childBase + pReg; *s0 ← zeroP]
      else [
        s0 ← rightBase + zReg; s2 ← *s0; s0 ← leftBase + zReg; s3 ← *s0;
        s0 ← leftBase + s2; *s0 ← s3; s0 ← rightBase + s3; *s0 ← s2;
        s4 ← s2 + oneP; s0 ← childBase + pReg; *s0 ← s4
      ]])
      ((((x.set s0 (base + 5 * n + p.val)).set s1 (st.deg p)).set s1 (st.deg p - 1)).write
        (base + 5 * n + p.val) (st.deg p - 1))
      post := by
  intro st post
  have hfit := hbr.fits_of_le hb
  have hp_lt := p.isLt
  have hcur_lt := cur.isLt
  have hdp_pos' : 1 ≤ st.deg p := hdp_pos
  have hdp_le' : st.deg p ≤ n := hdp_le
  refine WP.bounded (by wram_bounded <;> exact hfit _ (by omega)) ?_
  by_cases hdp1 : st.deg p - 1 = 0
  · wram_exec [hfit, hbr.regs_childBase, hbr.regs_zeroP, hp_reg, hdp1]
    intro hb2
    refine ⟨by omega, hb2, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr],
      modifies_of_eq fun a ha => by wram_simp, fun r h0 h1 h2 h3 h4 => by wram_simp,
      st.left, st.right, 0, Or.inl ⟨by omega, rfl, rfl, rfl⟩, ?_⟩
    wram_simp [ofData_write_child, ofData_write_deg, ofData_set_scratch, st]
  · have hge2 : 2 ≤ st.deg p := by omega
    obtain ⟨h_w, tail_w, _, hcirc_w, hcur_w, hlen_w, _⟩ := hdp2 hge2
    obtain ⟨r_nb, l_nb, -, hr_cur, hl_cur, -⟩ := hcirc_w.remove hcur_w hlen_w
    have hr_lt := r_nb.isLt
    have hl_lt := l_nb.isLt
    have hr_cur' : x.mem (base + 4 * n + cur.val) = r_nb.val := hr_cur
    have hl_cur' : x.mem (base + 3 * n + cur.val) = l_nb.val := hl_cur
    wram_exec [hfit, hbr.regs_childBase, hbr.regs_leftBase, hbr.regs_rightBase, hbr.regs_zeroP,
      hbr.regs_oneP, hp_reg, hz_reg, hr_cur', hl_cur', hdp1]
    intro hb2
    refine ⟨by omega, hb2, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr],
      modifies_of_eq fun a ha => by wram_simp, fun r h0 h1 h2 h3 h4 => by wram_simp,
      _, _, _, Or.inr ⟨hge2, r_nb, l_nb, hr_cur, hl_cur, rfl, rfl, rfl⟩, ?_⟩
    wram_simp [ofData_write_child, ofData_write_left, ofData_write_right,
      ofData_write_deg, ofData_set_scratch, st]

/-- Raw machine specification of `cutNodeCode`: cuts `cur` (`zReg`) from `p` (`pReg`) and splices
`cur` after `m` (`minRootReg = m.val + 1`) in at most `36` instructions. Its effect is `CutsNode`,
as for the record program `cut`: the machine state after the cut is `cutState`, and
`cutsNode_cutState` does the list reasoning. -/
theorem cutNodeCode_raw {n base w : ℕ} {x : Data rFib}
    (hb : x.Bounded w) (hbr : BaseRegs n base x)
    {cur p m : Fin n} {rtail : List (Fin n)}
    (hz_reg : x.regs zReg = cur.val) (hp_reg : x.regs pReg = p.val)
    (hdp_pos : 1 ≤ (RawState.ofData n base x).deg p)
    (hdp_le : (RawState.ofData n base x).deg p ≤ n)
    (hdp2 : 2 ≤ (RawState.ofData n base x).deg p →
      ∃ (h : Fin n) (tail : List (Fin n)),
        (RawState.ofData n base x).child p = h.val + 1 ∧
        IsCircList (RawState.ofData n base x).left (RawState.ofData n base x).right (h :: tail) ∧
        cur ∈ h :: tail ∧ 2 ≤ (h :: tail).length ∧
        ∀ u ∈ h :: tail, (RawState.ofData n base x).par u = p.val + 1)
    (hmin : (RawState.ofData n base x).minRoot = m.val + 1)
    (hcirc_r : IsCircList (RawState.ofData n base x).left (RawState.ofData n base x).right
      (m :: rtail))
    (hroots_par0 : ∀ u ∈ m :: rtail, (RawState.ofData n base x).par u = 0)
    (hpar_cur : (RawState.ofData n base x).par cur = p.val + 1)
    (hin_cur : (RawState.ofData n base x).inHeap cur ≠ 0)
    (hmk_cur : (RawState.ofData n base x).mark cur ≤ 1)
    (hnm : (RawState.ofData n base x).numMarked = markedCount (RawState.ofData n base x))
    (hnr_le : (RawState.ofData n base x).numRoots + 1 ≤ n) :
    ∃ y, ExecWithin w cutNodeCode x y 36 ∧
      BaseRegs n base y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      (∀ r : Fin rFib, r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ s3 → r ≠ s4 →
        r ≠ numMarkedReg → r ≠ numRootsReg → y.regs r = x.regs r) ∧
      (((RawState.ofData n base x).mark cur ≠ 0 → potential y + unitCredit = potential x) ∧
        ((RawState.ofData n base x).mark cur = 0 → potential y = potential x + unitCredit)) ∧
      CutsNode (RawState.ofData n base x) cur p m rtail (RawState.ofData n base y) := by
  have hfit := hbr.fits_of_le hb
  set st := RawState.ofData n base x with hst_def
  have hp_lt := p.isLt
  have hcur_lt := cur.isLt
  have hm_lt := m.isLt
  have hdeg_p : x.mem (base + 5 * n + p.val) = st.deg p := rfl
  wram_exec -split [cutNodeCode, hfit, hbr.regs_degBase, hbr.regs_oneP, hp_reg, hdeg_p]
  refine WP.cut _ (cutUnlink_wp hb hbr hz_reg hp_reg hdp_pos hdp_le hdp2) ?_
  rintro x2 t2 ⟨ht2, hb2, hbr2, hmod2, hx2_reg, left₁, right₁, child₁, hunlink, hst2⟩
  have hx2_z : x2.regs zReg = cur.val := by regs_frame
  have hmin_x2 : x2.regs minRootReg = m.val + 1 := by
    change (RawState.ofData n base x2).minRoot = _; rw [hst2]; exact hmin
  wram_exec [hfit, hbr2.regs_oneP, hmin_x2]
  obtain ⟨r', hr'⟩ := exists_right_min_of_unlink hdp2 hcirc_r hroots_par0 hunlink
  obtain ⟨x4, he4, hbr4, hmod4, hst4⟩ :=
    insertIntoNonEmptyList_exec (x := x2.set s1 m.val) (hReg := s1) (uReg := zReg) (h := m)
      (u := cur) (r := r') (hb2.set (hfit _ (by omega))) (hbr2.set_non_base (by decide) _)
      (by decide) (by decide) (by decide) (by decide) (by wram_simp) (by wram_simp [hx2_z])
      (by rw [ofData_set_scratch _ (by decide : 17 ≤ s1.val), hst2]; exact hr')
  rw [ofData_set_scratch _ (by decide : 17 ≤ s1.val)] at hst4
  refine WP.of_execWithin he4 ?_
  have hx4_reg (r : Fin rFib) (h0 : r ≠ s0) (h1 : r ≠ s1) (h2 : r ≠ s2) (h3 : r ≠ s3)
      (h4 : r ≠ s4) : x4.regs r = x.regs r := by
    rw [he4.regs_eq (insertIntoNonEmptyList_preserves h0 h2)]
    wram_simp [hx2_reg r h0 h1 h2 h3 h4]
  have hx4_z : x4.regs zReg = cur.val := by regs_frame
  have hp4 : (RawState.ofData n base x4).par = st.par := by rw [hst4, hst2]
  have hmk4 : (RawState.ofData n base x4).mark = st.mark := by rw [hst4, hst2]
  have hnm4 : (RawState.ofData n base x4).numMarked = st.numMarked := by rw [hst4, hst2]
  have hmk4_cur : x4.mem (base + 6 * n + cur.val) = st.mark cur := congrFun hmk4 cur
  wram_exec -split [hfit, hbr4.regs_parBase, hbr4.regs_markBase, hbr4.regs_zeroP, hx4_z, hmk4_cur]
  have hnm_le : st.numMarked ≤ n := hnm ▸ markedCount_le_n st
  let nm' := if st.mark cur = 0 then st.numMarked else st.numMarked - 1
  refine WP.cut (fun y t => t ≤ 3 ∧ BaseRegs n base y ∧
      Modifies (Block.mk base (space n)).footprint x4.mem y.mem ∧
      (∀ r : Fin rFib, r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ s3 → r ≠ s4 → r ≠ numMarkedReg →
        y.regs r = x.regs r) ∧
      RawState.ofData n base y =
        { RawState.ofData n base x4 with
          par := Function.update st.par cur 0
          mark := Function.update st.mark cur 0
          numMarked := nm' }) ?_ ?_
  · by_cases hmk0 : st.mark cur = 0
    · wram_exec [hfit, hbr4.regs_zeroP, hmk0]
      refine ⟨by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr4],
        modifies_of_eq fun a ha => by wram_simp,
        fun r h0 h1 h2 h3 h4 _ => by wram_simp [hx4_reg r h0 h1 h2 h3 h4], ?_⟩
      wram_simp [ofData_write_mark, ofData_write_par, ofData_set_scratch, hp4, hmk4, hnm4,
        nm', hmk0]
    · have hnm_pos := numMarked_pos_of_mark hnm hin_cur hmk0
      have hx4_nm : x4.regs numMarkedReg = st.numMarked := by regs_frame
      wram_exec [hfit, hbr4.regs_zeroP, hbr4.regs_oneP, hx4_nm, hmk0]
      refine ⟨by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr4],
        modifies_of_eq fun a ha => by wram_simp,
        fun r h0 h1 h2 h3 h4 _ => by wram_simp [hx4_reg r h0 h1 h2 h3 h4], ?_⟩
      wram_simp [ofData_set_numMarked, ofData_write_mark, ofData_write_par, ofData_set_scratch,
        hp4, hmk4, nm', hmk0]
  rintro x7 t7 ⟨ht7, hbr7, hmod7, hx7_reg, hst7⟩
  have hx7_nr : x7.regs numRootsReg = st.numRoots := by regs_frame
  wram_exec [hfit, hbr7.regs_oneP, hx7_nr]
  have hnm' : nm' = st.numMarked - st.mark cur := by
    dsimp only [nm']
    split_ifs <;> omega
  have hcs : RawState.ofData n base (x7.set numRootsReg (st.numRoots + 1)) =
      cutState st cur p m r' left₁ right₁ child₁ := by
    rw [ofData_set_numRoots, hst7, hst4, hst2, hnm']; rfl
  have hx7_nm : x7.regs numMarkedReg = nm' := congrArg RawState.numMarked hst7
  refine ⟨by wram_simp [BaseRegs.set_iff, hbr7],
    modifies_block_trans (modifies_block_trans hmod2 hmod4) hmod7,
    fun r h0 h1 h2 h3 h4 hnm_ne _ => by wram_simp [hx7_reg r h0 h1 h2 h3 h4 hnm_ne],
    ⟨fun hmk_ne => ?_, fun hmk0 => ?_⟩,
    hcs ▸ cutsNode_cutState hdp_pos hdp2 hcirc_r hroots_par0 hpar_cur hunlink hr'⟩
  · have hnm_pos := numMarked_pos_of_mark hnm hin_cur hmk_ne
    change unitCredit * (_ + 2 * _) + unitCredit = unitCredit * (st.numRoots + 2 * st.numMarked)
    wram_simp [hx7_nm, nm', hmk_ne, unitCredit]; omega
  · change unitCredit * (_ + 2 * _) = unitCredit * (st.numRoots + 2 * st.numMarked) + unitCredit
    wram_simp [hx7_nm, nm', hmk0, unitCredit]; omega

/-! ## Final `minRootReg` update tail and `decreaseKeyCode_exec` -/

private def decreaseKeyTail : Code .exact rFib :=
  ram_exact[
    s1 ← minRootReg - oneP;
    s0 ← baseReg + s1;
    s2 ← *s0;
    ⟪prioLTFlag argV argK s1 s2 s3⟫;
    if zeroP < s3 then [minRootReg ← argV + oneP] else [s0 ← zeroP]
  ]

private theorem decreaseKeyTail_exec {n base w : ℕ} {x : Data rFib}
    (hb : x.Bounded w) (hbr : BaseRegs n base x)
    {v m : Fin n} {k : ℕ}
    (hv_reg : x.regs argV = v.val) (hk_reg : x.regs argK = k)
    (hmin : (RawState.ofData n base x).minRoot = m.val + 1)
    (hkv : (RawState.ofData n base x).key v = k) :
    ∃ y, ExecWithin w decreaseKeyTail x y 12 ∧
      y.Bounded w ∧ BaseRegs n base y ∧ y.mem = x.mem ∧
      potential y = potential x ∧
      (let st := RawState.ofData n base x
       RawState.ofData n base y =
         { st with
           minRoot :=
             if IndexedMinPQ.PrioLT (v, st.key v) (m, st.key m)
               then v.val + 1 else m.val + 1 }) := by
  have hfit := hbr.fits_of_le hb
  set st := RawState.ofData n base x with hst_def
  have := v.isLt; have := m.isLt
  have hmin' : x.regs minRootReg = m.val + 1 := hmin
  have hkm : x.mem (base + m.val) = st.key m := rfl
  refine WP.exists_execWithin (WP.bounded hb ?_)
  wram_exec [decreaseKeyTail, hfit, hbr.regs_oneP, hbr.regs_baseReg, hmin', hkm]
  refine WP.of_execWithin (prioLTFlag_exec (n := n) (base := base)
    (by wram_simp [BaseRegs.set_iff, hbr]) argV argK s1 s2 s3) ?_
  have hlt_iff : IndexedMinPQ.PrioLT (v, st.key v) (m, st.key m) ↔
      k < st.key m ∨ k = st.key m ∧ v.val < m.val := by rw [← hkv]; rfl
  by_cases hlt : IndexedMinPQ.PrioLT (v, st.key v) (m, st.key m)
  · wram_exec [hfit, hv_reg, hk_reg, hbr.regs_zeroP, hbr.regs_oneP, hlt_iff.mp hlt]
    exact fun hby => ⟨by omega, hby, by wram_simp [BaseRegs.set_iff, hbr], rfl,
      by simp only [potential]; wram_simp,
      by wram_simp [ofData_set_minRoot, ofData_set_scratch, ← hst_def, hlt]⟩
  · wram_exec [hfit, hv_reg, hk_reg, hbr.regs_zeroP, hbr.regs_oneP, hlt_iff.not.mp hlt]
    exact fun hby => ⟨by omega, hby, by wram_simp [BaseRegs.set_iff, hbr], rfl,
      by simp only [potential]; wram_simp,
      by wram_simp [ofData_set_scratch, ← hst_def, hlt, ← hmin]⟩

/-- Upgrade `CutInv ... none` through the `minRootReg` update performed by `decreaseKeyTail`. -/
private theorem fibRawInv_of_tail {n K_max : ℕ} {s' : IndexedMinPQ.State n}
    {st st' : RawState n} {v m : Fin n}
    (hcut : CutInv n K_max s' st v m none)
    (hupd : st' = { st with
      minRoot := if IndexedMinPQ.PrioLT (v, st.key v) (m, st.key m)
        then v.val + 1 else m.val + 1 }) :
    FibRawInv n K_max s' st' := by
  subst hupd
  refine hcut.to_fibRawInv ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_
  by_cases hlt : IndexedMinPQ.PrioLT (v, st.key v) (m, st.key m) <;> simp [hlt]

/-- Loop invariant during the cascading-cut `while` loop in `decreaseKeyCode`. -/
private def CascLoopInv (n K_max w base : ℕ) (s : IndexedMinPQ.State n)
    (st₀ : RawState n) (mem₀ : ℕ → ℕ) (v m : Fin n) (k : ℕ) (a : Data rFib) : Prop :=
  a.Bounded w ∧ BaseRegs n base a ∧
  Modifies (Block.mk base (space n)).footprint mem₀ a.mem ∧
  a.regs argV = v.val ∧ a.regs argK = k ∧
  (RawState.ofData n base a).key = Function.update st₀.key v k ∧
  ∃ (cur : Fin n) (ts_c : List (FHTree n)),
    a.regs zReg = cur.val ∧
    Cascading n K_max s { RawState.ofData n base a with key := st₀.key } v m (some cur) ts_c ∧
    (∃ T ∈ ts_c, T.root = v) ∧ (∀ T ∈ ts_c, cur ∈ T.nodes → T.root ≠ v) ∧
    cur ∈ forestNodes ts_c ∧
    a.regs iterCur =
      if (RawState.ofData n base a).par cur ≠ 0 ∧ (RawState.ofData n base a).mark cur ≠ 0
      then 1 else 0

/-- Shared `cutNodeCode; zReg ← pReg; evalCascGuard` step used both for the initial cut of `v`
and inside every cascading-cut loop iteration. -/
private theorem cutAndGuard_exec {n K_max w base : ℕ} {s : IndexedMinPQ.State n}
    {st₀ : RawState n} {mem₀ : ℕ → ℕ} {v m cur p : Fin n} {k : ℕ}
    {pending : Option (Fin n)} {ts : List (FHTree n)} {a : Data rFib}
    (hb : a.Bounded w) (hbr : BaseRegs n base a)
    (hmod : Modifies (Block.mk base (space n)).footprint mem₀ a.mem)
    (ha_v : a.regs argV = v.val) (ha_k : a.regs argK = k)
    (ha_z : a.regs zReg = cur.val) (ha_p : a.regs pReg = p.val)
    (ha_key : (RawState.ofData n base a).key = Function.update st₀.key v k)
    (hc : Cascading n K_max s { RawState.ofData n base a with key := st₀.key } v m pending ts)
    (hpend : pending = none ∨ pending = some cur)
    (hrootv : cur = v ∨ ∃ T ∈ ts, T.root = v)
    (hne : ∀ T ∈ ts, cur ∈ T.nodes → T.root ≠ v)
    (hcur_fn : cur ∈ forestNodes ts)
    (hpar : (RawState.ofData n base a).par cur = p.val + 1) :
    ∃ a₁ a₂, ExecWithin w cutNodeCode a a₁ 36 ∧ a₁.regs pReg = p.val ∧
      ExecWithin w evalCascGuard (a₁.set zReg p.val) a₂ 8 ∧
      CascLoopInv n K_max w base s st₀ mem₀ v m k a₂ ∧
      ((RawState.ofData n base a).mark cur ≠ 0 → potential a₂ + unitCredit = potential a) ∧
      ((RawState.ofData n base a).mark cur = 0 → potential a₂ = potential a + unitCredit) := by
  have hfit := hbr.fits_of_le hb
  set st := RawState.ofData n base a
  obtain ⟨rtail, hcirc, hperm⟩ := hc.roots
  obtain ⟨hdp, hdp2, hdp_le, hroots0, hnr, -⟩ := hc.cut_pre hperm hcur_fn hpar
  obtain ⟨T, hT, hdesc⟩ := hc.desc_of_par hcur_fn (by dsimp only; omega)
  obtain ⟨-, -, -, hin_c, hmk_c, -⟩ := exists_parent_info (hc.valid T hT).1 hdesc hpar
  obtain ⟨a₁, he_cut, hbr₁, hmod₁, ha₁_reg, hpot_cut, hcut⟩ :=
    cutNodeCode_raw hb hbr ha_z ha_p hdp hdp_le hdp2 hc.minRoot hcirc hroots0 hpar
      hin_c hmk_c hc.numMarked hnr
  have hb₁ : a₁.Bounded w := he_cut.bounded hb
  obtain ⟨ts', hc', hv', hpv', hp'⟩ :=
    (hcut.withKey st₀.key).cascading hc hperm hpend hrootv hne hcur_fn hpar
  have ha₁_p : a₁.regs pReg = p.val := by regs_frame
  have ha₁_v : a₁.regs argV = v.val := by regs_frame
  have ha₁_k : a₁.regs argK = k := by regs_frame
  have hb_s : (a₁.set zReg p.val).Bounded w := hb₁.set (hfit _ (by have := p.isLt; omega))
  have hbr_s : BaseRegs n base (a₁.set zReg p.val) := by wram_simp [BaseRegs.set_iff, hbr₁]
  have hst_s : RawState.ofData n base (a₁.set zReg p.val) = RawState.ofData n base a₁ := by
    wram_simp [ofData_set_scratch]
  obtain ⟨a₂, he_cg, hbr₂, hst₂, hmem₂, ha₂_ic, ha₂_reg⟩ :=
    evalCascGuard_exec hb_s hbr_s (cur := p) (by wram_simp)
  have hpot₂ : potential a₂ = potential a₁ :=
    (potential_eq_of_evalCascGuard ha₂_reg).trans (by simp only [potential]; wram_simp)
  have hst₂₁ : RawState.ofData n base a₂ = RawState.ofData n base a₁ := hst₂.trans hst_s
  refine ⟨a₁, a₂, he_cut, ha₁_p, he_cg,
    ⟨he_cg.bounded hb_s, hbr₂, hmem₂ ▸ modifies_block_trans hmod hmod₁,
      by wram_simp [ha₂_reg argV _ _ _ _, ha₁_v], by wram_simp [ha₂_reg argK _ _ _ _, ha₁_k],
      by rw [hst₂₁, hcut.key, ha_key], p, ts',
      by wram_simp [ha₂_reg zReg _ _ _ _],
      by rw [hst₂₁]; exact hc', hv', hpv', hp',
      by rw [hst₂₁]; rw [hst_s] at ha₂_ic; exact ha₂_ic⟩,
    fun hm => hpot₂ ▸ hpot_cut.1 hm, fun hm => hpot₂ ▸ hpot_cut.2 hm⟩

private def cascLoopBody : Code .exact rFib :=
  ram_exact[
    s0 ← parBase + zReg;
    s1 ← *s0;
    pReg ← s1 - oneP;
    ⟪cutNodeCode⟫;
    zReg ← pReg;
    ⟪evalCascGuard⟫
  ]

private theorem cascLoopBody_step {n K_max w base : ℕ} {s : IndexedMinPQ.State n}
    {st₀ : RawState n} {mem₀ : ℕ → ℕ} {v m : Fin n} {k : ℕ} {a : Data rFib}
    (ha : CascLoopInv n K_max w base s st₀ mem₀ v m k a)
    (hguard : (Cond.lt zeroP iterCur).Holds a) :
    ∃ y T, ExecWithin w cascLoopBody a y T ∧
      CascLoopInv n K_max w base s st₀ mem₀ v m k y ∧
      T + 2 + potential y ≤ potential a := by
  rcases ha with ⟨hba, hbra, hmoda, ha_v, ha_k, ha_key, cur, ts_c, ha_z, hc, hTv_c,
    hcur_ne_v, hcur_fn, ha_ic⟩
  have hfit := hbra.fits_of_le hba
  set st_a := RawState.ofData n base a with hst_a_def
  have hcond : st_a.par cur ≠ 0 ∧ st_a.mark cur ≠ 0 := by
    rw [Cond.Holds, hbra.regs_zeroP, ha_ic] at hguard
    by_contra hnot; simp only [hnot, ↓reduceIte, lt_self_iff_false] at hguard
  obtain ⟨T_ci, hTci, hdesc⟩ := hc.desc_of_par hcur_fn hcond.1
  obtain ⟨p_c, -, hpar_c⟩ := (hc.valid T_ci hTci).1.par_of_mem_children cur hdesc
  have hcur_lt := cur.isLt; have hpc_lt := p_c.isLt
  have hpar_mem : a.mem (base + n + cur.val) = p_c.val + 1 := hpar_c
  wram_exec [cascLoopBody, hfit, hbra.regs_parBase, hbra.regs_oneP, ha_z, hpar_mem]
  refine WP.name fun a₃ ha₃ => ?_
  have hst₃ : RawState.ofData n base a₃ = st_a := by
    rw [ha₃]; wram_simp [ofData_set_scratch, ← hst_a_def]
  have hpot₃ : potential a₃ = potential a := by rw [ha₃]; simp only [potential]; wram_simp
  obtain ⟨a₁, a₂, he_cut, ha₁_p, he_cg, hinv₂, hdrop, -⟩ :=
    cutAndGuard_exec (w := w) (base := base) (a := a₃) (mem₀ := mem₀) (st₀ := st₀)
      (pending := some cur) (cur := cur) (p := p_c) (v := v) (m := m) (k := k)
      (by rw [ha₃]; wram_bounded <;> exact hfit _ (by omega))
      (by rw [ha₃]; wram_simp [BaseRegs.set_iff, hbra])
      (by rw [ha₃]; exact hmoda)
      (by rw [ha₃]; wram_simp [ha_v]) (by rw [ha₃]; wram_simp [ha_k])
      (by rw [ha₃]; wram_simp [ha_z]) (by rw [ha₃]; wram_simp)
      (by rw [hst₃]; exact ha_key) (by rw [hst₃]; exact hc)
      (Or.inr rfl) (Or.inr hTv_c) hcur_ne_v hcur_fn (by rw [hst₃]; exact hpar_c)
  have hpot_drop : potential a₂ + unitCredit = potential a :=
    (hdrop (hst₃ ▸ hcond.2)).trans hpot₃
  refine WP.of_execWithin he_cut ?_
  wram_exec [ha₁_p]
  exact WP.of_execWithin he_cg ⟨hinv₂, by dsimp only [unitCredit] at hpot_drop ⊢; omega⟩

private def cascPostMarkCode : Code .exact rFib :=
  ram_exact[
    s0 ← parBase + zReg;
    s1 ← *s0;
    if zeroP < s1 then [
      s0 ← markBase + zReg;
      *s0 ← oneP;
      numMarkedReg ← numMarkedReg + oneP
    ] else [s0 ← zeroP]
  ]

private theorem cascPostMark_exec {n K_max w base : ℕ} {s : IndexedMinPQ.State n}
    {st₀ : RawState n} {mem₀ : ℕ → ℕ} {v m : Fin n} {k k₀ : ℕ}
    (hsv₀ : s v = some k₀) (hkle₀ : k ≤ k₀) (hk_max : k ≤ K_max)
    {z_lp : Data rFib} (hz_inv : CascLoopInv n K_max w base s st₀ mem₀ v m k z_lp)
    (hz_exit : ¬(Cond.lt zeroP iterCur).Holds z_lp) :
    ∃ y t, ExecWithin w cascPostMarkCode z_lp y t ∧
      y.Bounded w ∧ BaseRegs n base y ∧
      y.regs argV = v.val ∧ y.regs argK = k ∧
      Modifies (Block.mk base (space n)).footprint mem₀ y.mem ∧
      (RawState.ofData n base y).minRoot = m.val + 1 ∧
      (RawState.ofData n base y).key = Function.update st₀.key v k ∧
      CutInv n K_max (Function.update s v (some k)) (RawState.ofData n base y) v m none ∧
      t + potential y ≤ 166 + potential z_lp := by
  rcases hz_inv with ⟨hb_lp, hbr_lp, hmod_lp, hlp_v, hlp_k, hlp_key, cur_f, ts_f, hlp_z,
    hc_f, hTv_f, -, hcurf_fn, hlp_ic⟩
  have hfit := hbr_lp.fits_of_le hb_lp
  set st_lp := RawState.ofData n base z_lp with hst_lp_def
  have hcurf_lt := cur_f.isLt
  have hnot_both : ¬(st_lp.par cur_f ≠ 0 ∧ st_lp.mark cur_f ≠ 0) := fun hb =>
    hz_exit (by simp [Cond.Holds, hbr_lp.regs_zeroP, hlp_ic, hb.1, hb.2])
  have hlp_par : z_lp.mem (base + n + cur_f.val) = st_lp.par cur_f := rfl
  refine WP.bounded hb_lp ?_
  unfold cascPostMarkCode
  by_cases hpf0 : st_lp.par cur_f = 0
  · wram_exec [hfit, hbr_lp.regs_parBase, hbr_lp.regs_zeroP, hlp_z, hlp_par, hpf0]
    intro hb_post
    refine ⟨hb_post, by wram_simp [BaseRegs.set_iff, hbr_lp], by wram_simp [hlp_v],
      by wram_simp [hlp_k], hmod_lp,
      by wram_simp [ofData_set_scratch, ← hst_lp_def]; exact hc_f.minRoot,
      by wram_simp [ofData_set_scratch, ← hst_lp_def]; exact hlp_key, ?_, ?_⟩
    · wram_simp [ofData_set_scratch, ← hst_lp_def]
      simpa only [← hlp_key] using
        (hc_f.clear_root hcurf_fn hpf0).lowerRootKey hTv_f hsv₀ hkle₀ hk_max
    · wram_simp [potential_set_scratch]; omega
  · have hmf0 : st_lp.mark cur_f = 0 := by_contra fun h => hnot_both ⟨hpf0, h⟩
    have hmk_inv := hc_f.mark hcurf_fn hpf0 hmf0
    have hnm_add_le : st_lp.numMarked + 1 ≤ n := by
      have h1 := hmk_inv.numMarked
      have h2 := markedCount_le_n { st_lp with
        mark := Function.update st_lp.mark cur_f 1, numMarked := st_lp.numMarked + 1,
        key := st₀.key }
      dsimp only at h1; omega
    have hlp_nm : z_lp.regs numMarkedReg = st_lp.numMarked := rfl
    wram_exec [hfit, hbr_lp.regs_parBase, hbr_lp.regs_markBase, hbr_lp.regs_zeroP,
      hbr_lp.regs_oneP, hlp_z, hlp_par, hlp_nm, hpf0]
    intro hb_post
    refine ⟨hb_post, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr_lp],
      by wram_simp [hlp_v], by wram_simp [hlp_k],
      modifies_block_trans hmod_lp (modifies_of_eq fun a ha => by wram_simp),
      by wram_simp [ofData_set_numMarked, ofData_write_mark, ofData_set_scratch, ← hst_lp_def]
         exact hc_f.minRoot,
      by wram_simp [ofData_set_numMarked, ofData_write_mark, ofData_set_scratch, ← hst_lp_def]
         exact hlp_key, ?_, ?_⟩
    · wram_simp [ofData_set_numMarked, ofData_write_mark, ofData_set_scratch, ← hst_lp_def]
      simpa only [← hlp_key] using hmk_inv.lowerRootKey hTv_f hsv₀ hkle₀ hk_max
    · wram_simp [potential_set_numMarked, potential_set_scratch]
      change _ + unitCredit * (z_lp.regs numRootsReg + 2 * (st_lp.numMarked + 1)) ≤
        166 + unitCredit * (z_lp.regs numRootsReg + 2 * st_lp.numMarked)
      dsimp only [unitCredit]; omega

private theorem cascadeFromInit_wp {n K_max w base : ℕ} {s : IndexedMinPQ.State n}
    {st₀ : RawState n} {mem₀ : ℕ → ℕ} {v m p₀ : Fin n} {k k₀ : ℕ}
    {ts₀ : List (FHTree n)} {x6 : Data rFib}
    (hb6 : x6.Bounded w) (hbr6 : BaseRegs n base x6)
    (hmod6 : Modifies (Block.mk base (space n)).footprint mem₀ x6.mem)
    (hreg_v : x6.regs argV = v.val) (hreg_k : x6.regs argK = k)
    (hreg_z : x6.regs zReg = v.val) (hreg_p : x6.regs pReg = p₀.val)
    (hst6 : RawState.ofData n base x6 = { st₀ with key := Function.update st₀.key v k })
    (hc₀ : Cascading n K_max s st₀ v m none ts₀)
    (hsv₀ : s v = some k₀) (hkle₀ : k ≤ k₀) (hk_max : k ≤ K_max)
    (hv_fn : v ∈ forestNodes ts₀) (hpv_eq : st₀.par v = p₀.val + 1) :
    WP w cutNodeCode x6 fun a₁ t₁ =>
      WP (B := .exact) w (.op (.copy zReg pReg)) a₁ fun a₂ t₂ =>
        WP w evalCascGuard a₂ fun a₃ t₃ =>
          WP w (.seq (.loop (.lt zeroP iterCur) cascLoopBody) cascPostMarkCode)
            a₃ fun y t₄ =>
            y.Bounded w ∧ BaseRegs n base y ∧
            y.regs argV = v.val ∧ y.regs argK = k ∧
            Modifies (Block.mk base (space n)).footprint mem₀ y.mem ∧
            (RawState.ofData n base y).minRoot = m.val + 1 ∧
            (RawState.ofData n base y).key = Function.update st₀.key v k ∧
            CutInv n K_max (Function.update s v (some k)) (RawState.ofData n base y) v m none ∧
            (t₄ + t₃ + t₂ + t₁) + potential y ≤ 293 + potential x6 := by
  have hv_ne : ∀ T ∈ ts₀, v ∈ T.nodes → T.root ≠ v := fun T hT _ e => by
    have h0 := (hc₀.valid T hT).2.1; rw [e] at h0; omega
  obtain ⟨a₁, x9, he_cut, ha₁_p, he_cg, hx9_inv, hdrop, hgrow⟩ :=
    cutAndGuard_exec (w := w) (base := base) (a := x6) (mem₀ := mem₀) (st₀ := st₀)
      (pending := none) (cur := v) (p := p₀) (v := v) (m := m) (k := k)
      hb6 hbr6 hmod6 hreg_v hreg_k hreg_z hreg_p
      (by rw [hst6]) (by rw [hst6]; exact hc₀) (Or.inl rfl) (Or.inl rfl) hv_ne hv_fn
      (by rw [hst6]; exact hpv_eq)
  have hpot9_le : potential x9 ≤ potential x6 + unitCredit := by
    by_cases hm : (RawState.ofData n base x6).mark v = 0
    · rw [hgrow hm]
    · have := hdrop hm; dsimp only [unitCredit] at this ⊢; omega
  obtain ⟨z_lp, t_lp, he_lp, hz_inv, hz_exit, hpot_lp⟩ :=
    ExecWithin.loop_potential_retain (B := .exact) (w := w)
      (cond := .lt zeroP iterCur) (body := cascLoopBody)
      (CascLoopInv n K_max w base s st₀ mem₀ v m k) potential
      (fun _ ha hc => cascLoopBody_step ha hc) hx9_inv
  obtain ⟨y, t_p, he_p, hb_p, hbr_p, hv_p, hk_p, hmod_p, hmin_p, hkey_p, hcut_p, hpot_p⟩ :=
    cascPostMark_exec hsv₀ hkle₀ hk_max hz_inv hz_exit
  refine WP.of_execWithin he_cut ?_
  wram_exec [ha₁_p]
  exact WP.of_execWithin he_cg <| WP.seq <| WP.of_execWithin he_lp <| WP.of_execWithin he_p
    ⟨hb_p, hbr_p, hv_p, hk_p, hmod_p, hmin_p, hkey_p, hcut_p,
      by dsimp only [unitCredit] at hpot9_le; omega⟩

/-- `decreaseKeyCode` lowers `key[v]` to `k ≤ k₀` (`s v = some k₀`), performs cascading cuts when
parent heap order is violated, updates `minRootReg`, and restores `FibInv` in amortized time
`t + potential y ≤ 330 + potential x`. The forest reasoning is the record heap's: the machine writes
the new key first, so the forest is read with the old keys (`{ st with key := st₀.key }`) as
`Cascading`, each cut is `CutsNode.cascading`, the cascade ends with `Cascading.clear_root` or
`Cascading.mark`, and `Cascading.lowerRootKey` or `FibRawInv.lowerKey_noCut` stores the key. -/
theorem decreaseKeyCode_exec {n K_max w base : ℕ} {s : IndexedMinPQ.State n} {x : Data rFib}
    (v : Fin n) (k : ℕ) (hinv : FibInv n K_max w base s x)
    (hval : (∃ k₀, s v = some k₀ ∧ k ≤ k₀) ∧ k ≤ K_max)
    (hv_reg : x.regs argV = v.val) (hk_reg : x.regs argK = k) :
    ∃ y t, ExecWithin w decreaseKeyCode x y t ∧
      FibInv n K_max w base (Function.update s v (some k)) y ∧
      Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
      t + potential y ≤ 330 + potential x := by
  obtain ⟨hb, hbr, hraw⟩ := hinv
  obtain ⟨⟨k₀, hsv₀, hkle₀⟩, hk_max⟩ := hval
  have hfit := hbr.fits_of_le hb
  set st₀ := RawState.ofData n base x with hst₀_def
  obtain ⟨m, ts₀, hc₀⟩ := cascading_of_fibRawInv (v := v) hraw (by simp [hsv₀])
  have hv_in_fn₀ : v ∈ forestNodes ts₀ := (hc₀.dom v).mpr (by simp [hsv₀])
  obtain ⟨T_rv, hTrv_mem, hv_in_Trv⟩ := mem_forestNodes_iff.mp hv_in_fn₀
  have hv_lt := v.isLt
  have hfit_k : Fits w k := hk_reg ▸ hb.1 argK
  have hfit_par : Fits w (st₀.par v) := hb.2 _
  have hpar_v : x.mem (base + n + v.val) = st₀.par v := rfl
  let s' := Function.update s v (some k)
  let preTail (y : Data rFib) (t : ℕ) : Prop :=
    y.Bounded w ∧ BaseRegs n base y ∧ y.regs argV = v.val ∧ y.regs argK = k ∧
    Modifies (Block.mk base (space n)).footprint x.mem y.mem ∧
    (RawState.ofData n base y).minRoot = m.val + 1 ∧
    (RawState.ofData n base y).key = Function.update st₀.key v k ∧
    t + potential y ≤ 314 + potential x ∧
    (CutInv n K_max s' (RawState.ofData n base y) v m none ∨
      (RawState.ofData n base y = { st₀ with key := Function.update st₀.key v k } ∧
        ∃ p₀ : Fin n, st₀.par v = p₀.val + 1 ∧ ¬IndexedMinPQ.PrioLT (v, k) (p₀, st₀.key p₀)))
  wram_exec -split [decreaseKeyCode,
    hfit, hbr.regs_baseReg, hbr.regs_parBase, hv_reg, hk_reg, hpar_v]
  refine WP.cut preTail ?_ ?_
  · by_cases hpv0 : st₀.par v = 0
    · refine WP.bounded (by wram_bounded <;> exact hfit _ (by omega)) ?_
      wram_exec [hbr.regs_zeroP, hpv0]
      intro hb3
      have hrv := ((hc₀.valid T_rv hTrv_mem).par_eq_zero_iff_root hv_in_Trv).mp hpv0
      refine ⟨hb3, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr],
        by wram_simp [hv_reg], by wram_simp [hk_reg],
        modifies_of_eq fun a ha => by wram_simp, ?_, ?_,
        by simp only [potential]; wram_simp; omega, Or.inl ?_⟩
      all_goals wram_simp [ofData_write_key, ofData_set_scratch, ← hst₀_def]
      · exact hc₀.minRoot
      · exact hc₀.lowerRootKey ⟨T_rv, hTrv_mem, hrv.symm⟩ hsv₀ hkle₀ hk_max
    · obtain ⟨T, hT, hv_desc⟩ := hc₀.desc_of_par hv_in_fn₀ hpv0
      obtain ⟨p₀, -, hpv_eq⟩ := (hc₀.valid T hT).1.par_of_mem_children v hv_desc
      have hp₀_lt := p₀.isLt
      have hp₀_ne_v' : p₀.val ≠ v.val := fun e =>
        (hc₀.valid T hT).1.par_ne_self (forestNodes_nodup_tree hc₀.nodup hT) hv_desc
          (Fin.ext e ▸ hpv_eq)
      have hkey_p₀ : x.mem (base + p₀.val) = st₀.key p₀ := rfl
      have hviol_iff : IndexedMinPQ.PrioLT (v, k) (p₀, st₀.key p₀) ↔
          k < st₀.key p₀ ∨ k = st₀.key p₀ ∧ v.val < p₀.val := Iff.rfl
      refine WP.bounded (by wram_bounded <;> exact hfit _ (by omega)) ?_
      wram_exec [hfit, hbr.regs_baseReg, hbr.regs_zeroP, hbr.regs_oneP, hpv_eq, hkey_p₀]
      refine WP.of_execWithin (prioLTFlag_exec (n := n) (base := base)
        (by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr]) argV argK pReg s2 s3) ?_
      by_cases hviol : IndexedMinPQ.PrioLT (v, k) (p₀, st₀.key p₀)
      · wram_exec [hv_reg, hk_reg, hbr.regs_zeroP, hviol_iff.mp hviol]
        refine WP.name fun x6 hx6 => ?_
        have hpot6 : potential x6 = potential x := by rw [hx6]; simp only [potential]; wram_simp
        exact (cascadeFromInit_wp (w := w) (base := base) (x6 := x6) (mem₀ := x.mem)
          (st₀ := st₀) (v := v) (m := m) (p₀ := p₀) (k := k)
          (by rw [hx6]; wram_bounded <;> first
            | exact hfit _ (by omega) | (split <;> exact hfit _ (by omega)))
          (by rw [hx6]; wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr])
          (modifies_of_eq fun a ha => by rw [hx6]; wram_simp)
          (by rw [hx6]; wram_simp [hv_reg]) (by rw [hx6]; wram_simp [hk_reg])
          (by rw [hx6]; wram_simp [hv_reg]) (by rw [hx6]; wram_simp)
          (by rw [hx6]; wram_simp [ofData_write_key, ofData_set_scratch, ← hst₀_def])
          hc₀ hsv₀ hkle₀ hk_max hv_in_fn₀ hpv_eq).mono fun _ _ h =>
          WP.seq <| h.mono fun _ _ h => WP.seq <| h.mono fun _ _ h => h.mono fun _ _
            ⟨hb_p, hbr_p, hv_p, hk_p, hmod_p, hmin_p, hkey_p, hcut_p, hpot_p⟩ _ =>
            ⟨hb_p, hbr_p, hv_p, hk_p, hmod_p, hmin_p, hkey_p, by omega, Or.inl hcut_p⟩
      · wram_exec [hv_reg, hk_reg, hbr.regs_zeroP, hviol_iff.not.mp hviol]
        intro hb6
        refine ⟨hb6, by wram_simp [BaseRegs.set_iff, BaseRegs.write_iff, hbr],
          by wram_simp [hv_reg], by wram_simp [hk_reg],
          modifies_of_eq fun a ha => by wram_simp, ?_, ?_,
          by simp only [potential]; wram_simp; omega, Or.inr ⟨?_, p₀, hpv_eq, hviol⟩⟩
        all_goals wram_simp [ofData_write_key, ofData_set_scratch, ← hst₀_def]
        exact hc₀.minRoot
  · rintro x_p t_p ⟨hb_p, hbr_p, hp_v, hp_k, hmod_p, hmin_p, hkey_p, hpot_p, hinv_p⟩
    obtain ⟨y, he_tail, hby, hbry, hmemy, hpoty, hsty⟩ :=
      decreaseKeyTail_exec hb_p hbr_p hp_v hp_k hmin_p (by rw [hkey_p, Function.update_self])
    dsimp only at hsty
    refine WP.of_execWithin he_tail ⟨⟨hby, hbry, ?_⟩, hmemy ▸ hmod_p, by omega⟩
    rcases hinv_p with hcut_p | ⟨hst_p, p₀, hpv_eq, hviol⟩
    · exact fibRawInv_of_tail hcut_p hsty
    · obtain ⟨hinv, hnot⟩ := FibRawInv.lowerKey_noCut hraw hsv₀ hkle₀ hk_max hpv_eq hviol
      have hnlt : ¬IndexedMinPQ.PrioLT (v, (RawState.ofData n base x_p).key v)
          (m, (RawState.ofData n base x_p).key m) := by
        rw [hst_p]; dsimp only; rw [Function.update_self]; exact hnot m hc₀.minRoot
      rwa [hsty, ite_eq_right hnlt, hst_p, ← hc₀.minRoot]

end Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap
