/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Approximation.UniqueGames.PropagationTime.Layout
import CslibFrontier.Computability.PCP.Approximation.UniqueGames.PropagationTime.Extend
import CslibFrontier.Computability.PCP.Approximation.UniqueGames.PropagationTime.StartPrune
import CslibFrontier.Computability.PCP.Approximation.UniqueGames.PropagationTime.Settle
import all CslibFrontier.Computability.PCP.Approximation.UniqueGames.Propagation

/-!
# Phase 3 symbolic execution: adjacency traversal, component exploration, and outer `stepsLoop`

This internal module composes `startCode`, `extendCode`, `pruneCode`, and `settleCode` into the
linked-list adjacency pass (`visitListLoop`), potential-charged stack exploration (`exploreCode`),
initial search-state reset (`resetStateCode`), and outer edge loop (`stepsLoop`) computing
`run (List.finRange L) g` in `O(L · (slots g + |g.edges|))` instructions.

## Main definitions

* `Cslib.Complexity.UniqueGames.Propagation.resetStateCode`: resets stack/component lengths and
  outer index before Phase 3.
* `Cslib.Complexity.UniqueGames.Propagation.stepsLoop`: outer edge-iteration loop executing
  component propagation across all connected components.

## Main results

* `Cslib.Complexity.UniqueGames.Propagation.resetStateCode_spec`: establishes
  `TableStateAt g (init g)` from `BucketsAt` and zeroed workspace at `≥ visBase g`.
* `Cslib.Complexity.UniqueGames.Propagation.stepsLoop_spec`: `ExecWithin` specification establishing
  `TableStateAt g (run (List.finRange L) g)` in
  `(5 * L + 38) * slots g + (106 * L + 152) * |g.edges| + 2` instructions via `creditRAM` potential
  accounting.
-/

public section

namespace Cslib.Complexity.UniqueGames.Propagation

open Cslib.PCP Cslib.PCP.Encoded Cslib.WordRAM Cslib.WordRAM.Block Reg

private abbrev visitPass (L : ℕ) : ℕ := 44 * L + 56

private def visitListHead : Code .standard 34 := ram[
  rEdgeIdx ← *rCurNode;
  rTmp1 ← rCurNode + rOne;
  rCurNode ← *rTmp1;
  rTmp1 ← rEdgeIdx * rStride;
  rEdgeIdx ← rEdgeBase + rTmp1;
  rSrc ← *rEdgeIdx;
  rTmp1 ← rEdgeIdx + rOne;
  rDst ← *rTmp1 ]

private def visitListBody : Code .standard 34 := ram[
  ⟪visitListHead⟫;
  ⟪extendCode⟫;
  ⟪pruneCode⟫ ]

private def visitListLoop : Code .standard 34 :=
  .loop (.lt rZero rCurNode) visitListBody

private def scanPop : Code .standard 34 := ram[
  rStackLen ← rStackLen - rOne;
  rTmp1 ← rStackBase + rStackLen;
  rChosen ← *rTmp1;
  rTmp1 ← rCompBase + rCompLen;
  *rTmp1 ← rChosen;
  rCompLen ← rCompLen + rOne;
  rTmp1 ← rHeadBase + rChosen;
  rCurNode ← *rTmp1 ]

private def scanCode : Code .standard 34 := ram[
  ⟪scanPop⟫;
  ⟪visitListLoop⟫ ]

private def exploreBody : Code .standard 34 := ram[
  if rStackLen = rZero then [ rRem ← rZero ] else [
    rRem ← rRem - rOne;
    ⟪scanCode⟫ ] ]

private def exploreCode : Code .standard 34 := ram[
  rRem ← rN;
  ⟪.loop (.lt rZero rRem) exploreBody⟫ ]

private def stepHead : Code .standard 34 := ram[
  rTmp1 ← rOuterIdx * rStride;
  rTmp1 ← rEdgeBase + rTmp1;
  rSrc ← *rTmp1;
  rTmp1 ← rVisBase + rSrc;
  rTmp1 ← *rTmp1 ]

private def stepBody : Code .standard 34 := ram[
  ⟪stepHead⟫;
  if rTmp1 = rZero then [
    ⟪startCode⟫;
    ⟪exploreCode⟫;
    ⟪settleCode⟫
  ] else [ rOuterIdx ← rOuterIdx ];
  rOuterIdx ← rOuterIdx + rOne ]

/-- Reset `rStackLen`, `rCompLen`, and `rOuterIdx` to `0` prior to `stepsLoop`. -/
def resetStateCode : Code .standard 34 := ram[
  rStackLen ← rZero;
  rCompLen ← rZero;
  rOuterIdx ← rZero ]

/-- Phase 3 outer loop iterating `stepBody` across all `|g.edges|` input edges. -/
def stepsLoop : Code .standard 34 :=
  .loop (.lt rOuterIdx rE) stepBody

/-- Specification for `resetStateCode`. -/
theorem resetStateCode_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (x2 : Data 34)
    (hc2 : ConstRegs g x2) (hinp2 : InputAt g x2.mem) (hbkt2 : BucketsAt g x2.mem)
    (hzero2 : ∀ a, visBase g ≤ a → x2.mem a = 0) :
    ∃ x3, ExecWithin w resetStateCode x2 x3 3 ∧
      TableStateAt g (init g) x3 ∧ x3.regs rOuterIdx = 0 := by
  unfold resetStateCode
  wram_exec [hc2.zero]
  refine ⟨⟨by wram_simp [hc2],
    by simpa only [Data.set_mem] using hinp2,
    by simpa only [Data.set_mem] using hbkt2, List.length_replicate,
    fun v _ _ => by
      simp only [Data.set_mem]
      exact hzero2 _ (Nat.le_add_right _ _),
    fun v hv fn hvf => by
      simp only [State.get, init, List.getD_replicate _ hv] at hvf
      nomatch hvf⟩,
    by wram_simp⟩

private theorem visitListLoop_spec {L w : ℕ} (g : Graph (Fin L → Fin L))
    (es : List (Edge (Fin L → Fin L))) (S : State (Fin L)) (x : Data 34)
    (hS : StateAt g S x) (hch : AdjChain g x.mem (visBase g) (x.regs rCurNode) es)
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w visitListLoop x y (visitPass L * es.length + 2) ∧
      StateAt g (es.foldl (visit (List.finRange L)) S) y ∧
      y.regs rRem = x.regs rRem ∧ y.regs rOuterIdx = x.regs rOuterIdx := by
  induction es generalizing S x with
  | nil =>
    generalize hp : x.regs rCurNode = p at hch
    cases hch
    exact ⟨x, ⟨2, by omega, .loop_exit
        (by simp only [Cond.holds_lt, hS.consts.zero, hp]; omega)⟩, hS, rfl, rfl⟩
  | cons e es' ih =>
    generalize hp : x.regs rCurNode = p at hch
    cases hch with
    | @cons _ j _ hj hlo hhi hp0 htl =>
    rw [← hp] at hlo hhi hp0 htl
    have hc_loop : (Cond.lt rZero rCurNode).Holds x := by
      simp only [Cond.holds_lt, hS.consts.zero]
      simp only [nodeBase, headBase] at hlo; omega
    have hhead : ∃ x1, ExecWithin w visitListHead x x1 8 ∧
        StateAt g S x1 ∧ x1.regs rCurNode = x.mem (x.regs rCurNode + 1) ∧
        x1.regs rEdgeIdx = 4 + j * (L + 2) ∧
        x1.regs rSrc = g.edges[j].src ∧ x1.regs rDst = g.edges[j].dst ∧
        x1.regs rRem = x.regs rRem ∧ x1.regs rOuterIdx = x.regs rOuterIdx ∧
        x1.mem = x.mem := by
      have hed := edge_end_le_wordBound hj
      have : Fits w (x.regs rCurNode + 1) := fits_top hw (by wram_omega)
      have : Fits w (j * (L + 2)) := hw.of_le (by omega)
      have : Fits w (4 + j * (L + 2)) := hw.of_le (by omega)
      have : Fits w (4 + j * (L + 2) + 1) := hw.of_le (by omega)
      unfold visitListHead
      wram_exec [hS.consts.one, hS.consts.stride, hS.consts.edgeB, hp0,
        hS.inp.edge_src j hj, hS.inp.edge_dst j hj]
      exact ⟨hS.of_eq (by wram_simp [hS.consts]) (by wram_simp [hS.stack_len])
          (by wram_simp [hS.comp_len]) (by wram_simp),
        by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
        by wram_simp⟩
    obtain ⟨x1, hx1, hS1, hcn1, he1, hs1, hd1, hrem1, hidx1, hm1⟩ := hhead
    obtain ⟨x2, hx2, hS2, he2, hs2, hd2, hcn2, hrem2, hidx2, hfr2⟩ :=
      extendCode_spec (w := w) g S x1 j hj hS1 he1 hs1 hd1 hw
    obtain ⟨x3, hx3, hS3, hcn3, hrem3, hidx3, hfr3⟩ :=
      pruneCode_spec (w := w) g (extend (List.finRange L) S g.edges[j]) x2 j hj hS2 he2 hs2 hd2 hw
    have htl_x3 : AdjChain g x3.mem (visBase g) (x3.regs rCurNode) es' := by
      rw [hcn3, hcn2, hcn1]
      exact htl.frame le_rfl fun a _ ha => by rw [hfr3 a ha, hfr2 a ha, hm1]
    obtain ⟨tb, htb, hexb⟩ : ExecWithin w visitListBody x x3 (44 * L + 54) :=
      (hx1.seq (hx2.seq hx3)).mono (by omega)
    obtain ⟨y, ⟨tl, htl_t, hexl⟩, hSy, hremy, hidxy⟩ :=
      ih (visit (List.finRange L) S g.edges[j]) x3 hS3 htl_x3
    refine ⟨y, ⟨tb + tl + 2, ?_, .loop_iter hc_loop hexb hexl⟩, hSy,
      hremy.trans (hrem3.trans (hrem2.trans hrem1)),
      hidxy.trans (hidx3.trans (hidx2.trans hidx1))⟩
    simp only [visitPass, List.length_cons, Nat.mul_succ] at htl_t ⊢; omega

private def weightRAM {L : ℕ} (g : Graph (Fin L → Fin L)) (v : ℕ) : ℕ :=
  16 + freezePass L + visitPass L * (adj g v).length

private def creditRAM {L : ℕ} (g : Graph (Fin L → Fin L)) (S : State (Fin L)) : ℕ :=
  S.wpot (weightRAM g) + freezePass L * S.comp.length

private theorem scanCode_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (S : State (Fin L))
    (x : Data 34) {u : ℕ} {rest : List ℕ} (hS : StateAt g S x)
    (hst : S.stack = u :: rest) (hcomp_lt : S.comp.length < slots g)
    (hw : Fits w (wordBound g)) :
    ∃ y t, Exec w scanCode x y t ∧
      t + 5 + creditRAM g (scan (List.finRange L) g S) ≤ creditRAM g S ∧
      StateAt g (scan (List.finRange L) g S) y ∧
      y.regs rRem = x.regs rRem ∧ y.regs rOuterIdx = x.regs rOuterIdx := by
  have hu_lt : u < slots g := hS.stack_lt u (by simp only [hst, List.mem_cons, true_or])
  have hm := hS.stack_mem
  rw [hst, List.reverse_cons] at hm
  obtain ⟨hstk1, hstk2⟩ := holdsList_append_iff.mp hm
  rw [List.length_reverse] at hstk2
  have hrest_le : rest.length < slots g := by
    have hp := hS.pot_le
    simp only [statePotential, hst, List.length_cons] at hp
    omega
  set S1 : State (Fin L) := { S with stack := rest, comp := u :: S.comp }
  have hpop_raw : ∃ x1, ExecWithin w scanPop x x1 8 ∧
      ConstRegs g x1 ∧ x1.regs rStackLen = rest.length ∧
      x1.regs rCompLen = S.comp.length + 1 ∧
      x1.regs rCurNode = x.mem (headBase g + u) ∧
      x1.regs rRem = x.regs rRem ∧ x1.regs rOuterIdx = x.regs rOuterIdx ∧
      x1.mem = Function.update x.mem (compBase g + S.comp.length) u := by
    have hlen_u : x.regs rStackLen = rest.length + 1 := by
      simp only [hS.stack_len, hst, List.length_cons]
    have : Fits w (stackBase g + rest.length) := fits_top hw (by wram_omega)
    have : Fits w (compBase g + S.comp.length) := fits_top hw (by wram_omega)
    have : Fits w (S.comp.length + 1) := fits_top hw (by wram_omega)
    have : Fits w (headBase g + u) := fits_top hw (by wram_omega)
    have hfr_hb : Function.update x.mem (compBase g + S.comp.length) u (headBase g + u) =
        x.mem (headBase g + u) := Function.update_of_ne (by wram_omega) _ _
    unfold scanPop
    wram_exec [hS.consts.one, hS.consts.headB, hS.consts.stackB, hS.consts.compB,
      hlen_u, Nat.add_sub_cancel rest.length 1, (holdsList_cons_iff.mp hstk2).1, hS.comp_len,
      hfr_hb]
    exact ⟨by wram_simp [hS.consts], by wram_simp, by wram_simp, by wram_simp [hfr_hb],
      by wram_simp, by wram_simp, by wram_simp⟩
  obtain ⟨x1, ⟨t1, ht1, hex1⟩, hc1, hsl1, hcl1, hcn1, hrem1, hidx1, hx1m⟩ := hpop_raw
  have hfr_comp : ∀ a < compBase g, x1.mem a = x.mem a := fun a ha => by
    rw [hx1m]; exact Function.update_of_ne (by omega) _ _
  have hS1 : StateAt g S1 x1 :=
    ⟨hS.toTableStateAt.frame hc1 rfl (compBase g) (by wram_omega) hfr_comp,
      by have hp : S.potential ≤ slots g := hS.pot_le
         have hun : S1.unvisited = S.unvisited := rfl
         change S1.potential ≤ slots g
         unfold State.potential at hp ⊢
         simp only [S1, hun, hst, List.length_cons] at hp ⊢
         omega,
      fun a ha => by
        rw [hfr_comp _ (by wram_omega)]
        exact hS.cand_mem a ha,
      hsl1, fun v hv => hS.stack_lt v (hst ▸ List.mem_cons_of_mem u hv),
      hstk1.frame fun a _ ha2 => hfr_comp a (by
        rw [List.length_reverse] at ha2
        wram_omega),
      by simpa only [S1, List.length_cons] using hcl1,
      by simp only [S1, List.length_cons]; omega,
      fun v hv => (List.mem_cons.mp hv).elim (· ▸ hu_lt) (hS.comp_lt v),
      by simpa only [S1, List.reverse_cons, List.length_reverse, hx1m] using
        hS.comp_mem.append_one u⟩
  have hch1 : AdjChain g x1.mem (visBase g) (x1.regs rCurNode) (adj g u) := by
    rw [hcn1]
    exact (hS.bkt u hu_lt).frame le_rfl fun a _ ha => hfr_comp a (by wram_omega)
  obtain ⟨y, ⟨t2, ht2, hex2⟩, hSy, hrem2, hidx2⟩ :=
    visitListLoop_spec (w := w) g (adj g u) S1 x1 hS1 hch1 hw
  rw [scan_cons (List.finRange L) g hst]
  refine ⟨y, t1 + t2, hex1.seq hex2, ?_, hSy, hrem2.trans hrem1, hidx2.trans hidx1⟩
  have hstep := foldl_visit_step (List.finRange L) (adj g u) (S := S1) (adj_bounds hS.len_table u)
  have hw_pot := hstep.wpot (weightRAM g)
  have hS1w : S1.wpot (weightRAM g) + weightRAM g u = S.wpot (weightRAM g) := by
    have hun : S1.unvisited = S.unvisited := rfl
    simp only [State.wpot, hun, S1, hst, List.map_cons, List.sum_cons]; omega
  have hwu : weightRAM g u = 16 + freezePass L + visitPass L * (adj g u).length := rfl
  unfold creditRAM
  dsimp only [S1] at hstep hw_pot hS1w ⊢
  rw [hstep.comp]
  simp only [List.length_cons, Nat.mul_succ]; omega

private theorem exploreCode_spec {L w : ℕ} (g : Graph (Fin L → Fin L)) (S : State (Fin L))
    (x : Data 34) (hS : StateAt g S x) (hcomp0 : S.comp = [])
    (hw : Fits w (wordBound g)) :
    ∃ y t, Exec w exploreCode x y t ∧
      t + creditRAM g ((scan (List.finRange L) g)^[slots g] S) ≤ creditRAM g S + 8 ∧
      StateAt g ((scan (List.finRange L) g)^[slots g] S) y ∧
      y.regs rOuterIdx = x.regs rOuterIdx := by
  have hset : ∃ x0, ExecWithin w (ram[ rRem ← rN ] : Code .standard 34) x x0 1 ∧
      StateAt g S x0 ∧ x0.regs rRem = slots g ∧ x0.regs rOuterIdx = x.regs rOuterIdx := by
    wram_exec [hS.consts.regN]
    exact ⟨hS.of_eq (by wram_simp [hS.consts]) (by wram_simp [hS.stack_len])
        (by wram_simp [hS.comp_len]) (by wram_simp),
      by wram_simp, by wram_simp⟩
  obtain ⟨x0, ⟨t0, ht0, hex0⟩, hS0, hrem0, hidx0⟩ := hset
  suffices hloop : ∀ (k : ℕ) (S' : State (Fin L)) (z : Data 34),
      StateAt g S' z → z.regs rRem = k → S'.comp.length + k ≤ slots g →
      ∃ y t, Exec w (.loop (.lt rZero rRem) exploreBody) z y t ∧
        t + creditRAM g ((scan (List.finRange L) g)^[k] S') ≤ creditRAM g S' + 7 ∧
        StateAt g ((scan (List.finRange L) g)^[k] S') y ∧
        y.regs rOuterIdx = z.regs rOuterIdx by
    obtain ⟨y, t, hexl, hcred, hSy, hidxy⟩ :=
      hloop (slots g) S x0 hS0 hrem0 (by simp only [hcomp0, List.length_nil, Nat.zero_add, le_refl])
    exact ⟨y, t0 + t, hex0.seq hexl, by omega, hSy, hidxy.trans hidx0⟩
  intro k
  induction k with
  | zero =>
    intro S' z hS' hrem' _
    refine ⟨z, 2, .loop_exit (by simp only [Cond.holds_lt, hS'.consts.zero, hrem']; omega),
      by simp only [Function.iterate_zero, id_eq]; omega, hS', rfl⟩
  | succ k ih =>
    intro S' z hS' hrem' hck
    have hc_loop : (Cond.lt rZero rRem).Holds z := by
      simp only [Cond.holds_lt, hS'.consts.zero, hrem']; omega
    cases hst : S'.stack with
    | nil =>
      have hc_br : (Cond.eq rStackLen rZero).Holds z := by
        simp only [Cond.holds_eq, hS'.stack_len, hst, List.length_nil, hS'.consts.zero]
      have hbody_nil : ∃ z1, ExecWithin w (ram[ rRem ← rZero ] : Code .standard 34) z z1 1 ∧
          StateAt g S' z1 ∧ z1.regs rRem = 0 ∧ z1.regs rOuterIdx = z.regs rOuterIdx := by
        wram_exec [hS'.consts.zero]
        exact ⟨hS'.of_eq (by wram_simp [hS'.consts]) (by wram_simp [hS'.stack_len])
            (by wram_simp [hS'.comp_len]) (by wram_simp),
          by wram_simp, by wram_simp⟩
      obtain ⟨z1, ⟨tb, htb, hexb⟩, hS1, hrem1, hidx1⟩ := hbody_nil
      have hexl_exit : Exec w (.loop (.lt rZero rRem) exploreBody) z1 z1 2 :=
        .loop_exit (by simp only [Cond.holds_lt, hS1.consts.zero, hrem1]; omega)
      have hfix : (scan (List.finRange L) g)^[k + 1] S' = S' :=
        Function.iterate_fixed (scan_nil (List.finRange L) g hst) (k + 1)
      rw [hfix]
      exact ⟨z1, (tb + 1) + 2 + 2,
        .loop_iter hc_loop (.branch_pos hc_br hexb) hexl_exit, by omega, hS1, hidx1⟩
    | cons u rest =>
      have hc_br : ¬ (Cond.eq rStackLen rZero).Holds z := by
        simp only [Cond.holds_eq, hS'.stack_len, hst, List.length_cons, hS'.consts.zero,
          Nat.add_one_ne_zero, not_false_eq_true]
      have hdec : ∃ z1, ExecWithin w (ram[ rRem ← rRem - rOne ] : Code .standard 34) z z1 1 ∧
          StateAt g S' z1 ∧ z1.regs rRem = k ∧ z1.regs rOuterIdx = z.regs rOuterIdx := by
        have : Fits w k := hw.of_le (by have := edges_lt_wordBound g; omega)
        wram_exec [hS'.consts.one, hrem']
        exact ⟨hS'.of_eq (by wram_simp [hS'.consts]) (by wram_simp [hS'.stack_len])
            (by wram_simp [hS'.comp_len]) (by wram_simp),
          by wram_simp, by wram_simp⟩
      obtain ⟨z1, ⟨td, htd, hexd⟩, hS1, hrem1, hidx1⟩ := hdec
      obtain ⟨z2, ts, hexs, hcred_s, hS2, hrem2, hidx2⟩ :=
        scanCode_spec (w := w) g S' z1 hS1 hst (by omega) hw
      have hcomp_next : (scan (List.finRange L) g S').comp.length = S'.comp.length + 1 := by
        rw [scan_cons (List.finRange L) g hst]
        have hstep := foldl_visit_step (List.finRange L) (adj g u)
          (S := { S' with stack := rest, comp := u :: S'.comp }) (adj_bounds hS'.len_table u)
        rw [hstep.comp]; rfl
      obtain ⟨y, tl, hexl, hcred_l, hSy, hidxy⟩ :=
        ih (scan (List.finRange L) g S') z2 hS2 (hrem2.trans hrem1) (by omega)
      rw [Function.iterate_succ_apply]
      exact ⟨y, (td + ts + 2) + tl + 2,
        .loop_iter hc_loop (.branch_neg hc_br (hexd.seq hexs)) hexl,
        by omega, hSy, hidxy.trans (hidx2.trans hidx1)⟩

private theorem sum_length_adj_le_fin {L : ℕ} (g : Graph (Fin L → Fin L)) :
    ∑ v ∈ Finset.range (slots g), (adj g v).length ≤ 2 * g.edges.length := by
  suffices ∀ (l : List (Edge (Fin L → Fin L))),
      ∑ v ∈ Finset.range (slots g), (l.filter (incident v)).length ≤ 2 * l.length from this _
  intro l
  induction l with
  | nil => simp
  | cons e l ih =>
    have hcount (v : ℕ) : ((e :: l).filter (incident v)).length =
        (l.filter (incident v)).length + if incident v e then 1 else 0 := by
      rw [List.filter_cons]
      split_ifs <;> simp
    simp only [hcount, Finset.sum_add_distrib, List.length_cons]
    have h2 : ∑ v ∈ Finset.range (slots g), (if incident v e = true then 1 else 0) ≤ 2 := by
      rw [Finset.sum_boole]
      refine (Finset.card_le_card (t := {e.src, e.dst}) fun v hv => ?_).trans Finset.card_le_two
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, incident,
        Bool.or_eq_true, beq_iff_eq] at hv ⊢
      omega
    omega

/-- Specification for `stepsLoop`. -/
theorem stepsLoop_spec {L w : ℕ} [NeZero L] (g : Graph (Fin L → Fin L)) (x : Data 34)
    (hT : TableStateAt g (init g) x) (hidx0 : x.regs rOuterIdx = 0)
    (hw : Fits w (wordBound g)) :
    ∃ y, ExecWithin w stepsLoop x y
        ((5 * L + 38) * slots g + (106 * L + 152) * g.edges.length + 2) ∧
      TableStateAt g (run (List.finRange L) g) y := by
  have hewb := edges_lt_wordBound g
  have hstep_one : ∀ (j : ℕ) (hj : j < g.edges.length) (S : State (Fin L)) (z : Data 34),
      TableStateAt g S z → z.regs rOuterIdx = j → S.comp = [] → S.stack = [] →
      ∃ y t, Exec w stepBody z y t ∧
        t + creditRAM g (step (List.finRange L) g S g.edges[j]) ≤
          creditRAM g S + (18 * L + 38) ∧
        TableStateAt g (step (List.finRange L) g S g.edges[j]) y ∧
        (step (List.finRange L) g S g.edges[j]).comp = [] ∧
        (step (List.finRange L) g S g.edges[j]).stack = [] ∧
        y.regs rOuterIdx = j + 1 := by
    intro j hj S z hzT hzIdx hzComp hzStk
    set e := g.edges[j]
    have hs_lt : e.src < slots g := src_lt_slots (List.getElem_mem hj)
    have hed := edge_end_le_wordBound hj
    have : Fits w (j * (L + 2)) := hw.of_le (by omega)
    have : Fits w (4 + j * (L + 2)) := hw.of_le (by omega)
    have : Fits w (visBase g + e.src) := fits_top hw (by wram_omega)
    have : Fits w (j + 1) := hw.of_le (by omega)
    have hinc (S' : State (Fin L)) (z4 : Data 34) (hz4T : TableStateAt g S' z4)
        (hz4Idx : z4.regs rOuterIdx = j) :
        ∃ y, ExecWithin w (ram[ rOuterIdx ← rOuterIdx + rOne ] : Code .standard 34) z4 y 1 ∧
          TableStateAt g S' y ∧ y.regs rOuterIdx = j + 1 := by
      wram_exec [hz4T.consts.one, hz4Idx]
      exact ⟨hz4T.of_eq
          (by wram_simp [hz4T.consts])
          (by wram_simp),
        by wram_simp⟩
    have hhead : ∃ z1, ExecWithin w stepHead z z1 5 ∧
        TableStateAt g S z1 ∧ z1.regs rSrc = e.src ∧ z1.regs rTmp1 = z.mem (visBase g + e.src) ∧
        z1.regs rOuterIdx = j := by
      unfold stepHead
      wram_exec [hzT.consts.stride, hzT.consts.edgeB, hzT.consts.visB, hzIdx,
        hzT.inp.edge_src j hj]
      exact ⟨hzT.of_eq (by wram_simp [hzT.consts]) (by wram_simp),
        by wram_simp; rfl, by wram_simp; rfl, by wram_simp [hzIdx]⟩
    obtain ⟨z1, ⟨th, hth, hexh⟩, hz1T, hz1S, hz1T1, hz1Idx⟩ := hhead
    cases hgs : S.get e.src with
    | some fn =>
      obtain ⟨hvis1, _⟩ := hzT.vis_some e.src hs_lt fn hgs
      have hc_br : ¬ (Cond.eq rTmp1 rZero).Holds z1 := by
        simp only [Cond.holds_eq, hz1T1, hvis1, hz1T.consts.zero, Nat.one_ne_zero,
          not_false_eq_true]
      obtain ⟨y, ⟨ti, hti, hexi⟩, hyT, hyIdx⟩ := hinc S z1 hz1T hz1Idx
      simp only [step, hgs]
      exact ⟨y, th + (1 + 2 + ti), hexh.seq ((Exec.branch_neg hc_br (exec_nop _ _)).seq hexi),
        by omega, hyT, hzComp, hzStk, hyIdx⟩
    | none =>
      have hc_br : (Cond.eq rTmp1 rZero).Holds z1 := by
        simp only [Cond.holds_eq, hz1T1, hzT.vis_none e.src hs_lt hgs, hz1T.consts.zero]
      obtain ⟨z2, ⟨ts, hts, hexs⟩, hz2S, hz2Idx⟩ :=
        startCode_spec (w := w) g S z1 e.src hz1T hz1S hs_lt hgs hw
      obtain ⟨z3, te, hexe, hcred_e, hz3S, hz3Idx⟩ :=
        exploreCode_spec (w := w) g (start S e.src) z2 hz2S rfl hw
      obtain ⟨z4, ⟨tf, htf, hexf⟩, hz4T, hz4Idx⟩ :=
        settleCode_spec (w := w) g ((scan (List.finRange L) g)^[slots g] (start S e.src))
          z3 hz3S hw
      obtain ⟨y, ⟨ti, hti, hexi⟩, hyT, hyIdx⟩ :=
        hinc _ z4 hz4T (hz4Idx.trans (hz3Idx.trans (hz2Idx.trans hz1Idx)))
      simp only [step, hgs]
      set Tscan := (scan (List.finRange L) g)^[slots g] (start S e.src)
      have hstk_end : Tscan.stack = [] :=
        iterate_scan_eq_nil (List.finRange L) g
          (by simp only [start, List.length_set, hzT.len_table])
          (potential_start hzT.len_table (hzT.len_table ▸ hs_lt))
      have hcred_start : creditRAM g (start S e.src) ≤ creditRAM g S := by
        have hun : (start S e.src).unvisited = S.unvisited.erase e.src :=
          unvisited_push (hzT.len_table ▸ hs_lt) id
        have hsum := Finset.sum_erase_add _ (weightRAM g)
          (mem_unvisited (hzT.len_table ▸ hs_lt) hgs)
        unfold creditRAM State.wpot
        rw [hun]
        simp only [start, hzComp, hzStk, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, List.length_nil, mul_zero, add_zero]
        omega
      have hcred_settle : creditRAM g (settle (List.finRange L) Tscan) =
          Tscan.wpot (weightRAM g) := by
        unfold creditRAM State.wpot
        rw [unvisited_settle (List.finRange L) Tscan]
        simp only [settle, hstk_end, List.map_nil, List.sum_nil, List.length_nil, mul_zero,
          add_zero]
      have hcred_Tscan : creditRAM g Tscan =
          Tscan.wpot (weightRAM g) + freezePass L * Tscan.comp.length := rfl
      exact ⟨y, th + ((ts + (te + tf) + 1) + ti),
        hexh.seq ((Exec.branch_pos hc_br (hexs.seq (hexe.seq hexf))).seq hexi),
        by omega, hyT, rfl, hstk_end, hyIdx⟩
  suffices hrem_edges : ∀ (m : ℕ) (hm : m ≤ g.edges.length)
      (S : State (Fin L)) (z : Data 34),
      TableStateAt g S z → z.regs rOuterIdx = g.edges.length - m → S.comp = [] → S.stack = [] →
      ∃ y t, Exec w stepsLoop z y t ∧
        t + creditRAM g ((g.edges.drop (g.edges.length - m)).foldl (step (List.finRange L) g) S) ≤
          creditRAM g S + (18 * L + 40) * m + 2 ∧
        TableStateAt g ((g.edges.drop (g.edges.length - m)).foldl (step (List.finRange L) g) S) y by
    obtain ⟨y, t, hexl, hcred, hyT⟩ :=
      hrem_edges g.edges.length le_rfl (init g) x hT (by rw [hidx0, Nat.sub_self]) rfl rfl
    simp only [Nat.sub_self, List.drop_zero] at hcred hyT
    have hinit_cred : creditRAM g (init g) ≤
        (5 * L + 38) * slots g + (88 * L + 112) * g.edges.length := by
      have hun : (init g).unvisited = Finset.range (slots g) := by
        ext v
        simp [State.unvisited, init, State.get]
      unfold creditRAM State.wpot
      rw [hun]
      simp only [init, List.map_nil, List.sum_nil, List.length_nil,
        mul_zero, add_zero, weightRAM, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        smul_eq_mul, ← Finset.mul_sum]
      have hadj := Nat.mul_le_mul_left (visitPass L) (sum_length_adj_le_fin g)
      simp only [visitPass] at hadj ⊢; nlinarith
    exact ⟨y, ⟨t, by nlinarith, hexl⟩, hyT⟩
  intro m
  induction m with
  | zero =>
    intro _ S z hzT hzIdx _ _
    simp only [Nat.sub_zero, List.drop_length, List.foldl_nil] at hzIdx ⊢
    exact ⟨z, 2, .loop_exit (by simp only [Cond.holds_lt, hzIdx, hzT.consts.regE]; omega),
      by omega, hzT⟩
  | succ m ih =>
    intro hm S z hzT hzIdx hzComp hzStk
    set j := g.edges.length - (m + 1)
    have hj : j < g.edges.length := by omega
    have hc_loop : (Cond.lt rOuterIdx rE).Holds z := by
      simp only [Cond.holds_lt, hzIdx, hzT.consts.regE]; omega
    obtain ⟨z1, t1, hex1, hcred1, hz1T, hz1Comp, hz1Stk, hz1Idx⟩ :=
      hstep_one j hj S z hzT hzIdx hzComp hzStk
    obtain ⟨y, t2, hex2, hcred2, hyT⟩ :=
      ih (by omega) (step (List.finRange L) g S g.edges[j]) z1 hz1T (by omega) hz1Comp hz1Stk
    have hdrop : g.edges.drop j = g.edges[j] :: g.edges.drop (g.edges.length - m) := by
      rw [show g.edges.length - m = j + 1 by omega]
      exact List.drop_eq_getElem_cons hj
    rw [hdrop, List.foldl_cons]
    exact ⟨y, t1 + t2 + 2, .loop_iter hc_loop hex1 hex2,
      by simp only [Nat.mul_succ]; omega, hyT⟩

end Cslib.Complexity.UniqueGames.Propagation
