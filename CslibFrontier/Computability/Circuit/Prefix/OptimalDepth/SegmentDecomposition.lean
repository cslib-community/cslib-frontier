/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Prefix.Basic
public import CslibFrontier.Computability.Circuit.Prefix.OptimalDepth.Trees
-- `import all`: reads private zero-deficiency DAG helpers (`programWord`, `ancMul`, `stripId`,
-- `leftSpine`, `universal_mul_sets`) from `Prefix.Basic` and private `programWord`-indexed
-- segment-tree helpers (`gateWord_range_split`, `exists_wireIntervalTree`, `spine_decomposition`,
-- `wireState`, `buildSegTree`, `buildSegTree_counts`) from `OptimalDepth.SegmentTree`.
import all CslibFrontier.Computability.Circuit.Prefix.Basic
import all CslibFrontier.Computability.Circuit.Prefix.OptimalDepth.SegmentTree
import CslibFrontier.Computability.Circuit.Basic
import CslibFrontier.Computability.Circuit.FanIn
import CslibFrontier.Computability.Circuit.Program

/-!
# Principal-chain segment decomposition of optimal prefix circuits

Combines zero-deficiency multiplication-gate uniqueness (`universal_mul_sets`) with `buildSegTree`
to extract consistent `(IntervalTree, GenPrefixTree)` pairs across all `c.depth` principal-chain
segments of an optimal fanout-`k` universal prefix circuit [Sergeev2025PrefixDepth].

## Main results

* `Cslib.Circuits.Prefix.optimal_segment_decomposition`: partitions any optimal fanout-`k` prefix
  circuit on `N ≥ 1` inputs into `c.depth` valid segment pairs `(I_d, t_d)` with root budget
  `≤ k - 1`, fanout `≤ k`, depth `d + t_d.depth ≤ c.depth`, unit output/mul multiplicities, and
  segment width `T (d + 1) - T d ≤ t_d.outCount`.

## References

* [I. S. Sergeev, *A Note on the Depth of Optimal Fanout-Bounded Prefix
  Circuits*][Sergeev2025PrefixDepth]
-/

public section

namespace Cslib.Circuits.Prefix

private theorem buildSegTree_props {N k : ℕ} (c : PrefixCircuit N) (a b D : ℕ)
    (root : Wire N c.size) (I : IntervalTree a b)
    (hfan : FanoutAtMost c k)
    (houtWord : ∀ j : Fin N, programWord c.program (c.outputs j) = List.range' 0 (j.val + 1))
    (hout_depth : ∀ j : Fin N, c.program.wireDepths (c.outputs j) ≤ D)
    (hroot_unique : ∀ g : Fin c.size,
      (c.program.lines g).op = .mul →
      programWord c.program (.gate g) = List.range' 0 a → Wire.gate g = root)
    (hmul_seg : ∀ g : Fin c.size, ∀ s, a < s → s < b →
      (c.program.lines g).op = .mul →
      programWord c.program (.gate g) = List.range' 0 s →
        ∃ p, a ≤ p ∧ p < s ∧
          programWord c.program (firstInput (c.program.lines g)) = List.range' 0 p ∧
          (p, s) ∈ I.intervals.erase (a, b))
    (w : Wire N c.size) (hact : segActive c a b root w = true) :
    (∃ s, a ≤ s ∧ s < b ∧ programWord c.program w = List.range' 0 s ∧
        (buildSegTree c a b root w).state = s) ∧
      (buildSegTree c a b root w).MaxStateLt b ∧
      (buildSegTree c a b root w).FanoutAtMost k ∧
      (buildSegTree c a b root w).Valid (I.intervals.erase (a, b)) ∧
      c.program.wireDepths w + (buildSegTree c a b root w).depth ≤ D := by
  have ih := fun g (hg : g ∈ segChildren c a b root w) =>
    buildSegTree_props c a b D root I hfan houtWord hout_depth hroot_unique hmul_seg (.gate g)
      ((mem_segChildren_iff c a b root w g).mp hg).2.2
  -- A child at state `s` fixes the state of `w`, through a valid transition.
  have hchild : ∀ g ∈ segChildren c a b root w, ∀ s, a ≤ s → s < b →
      programWord c.program (.gate g) = List.range' 0 s →
      if ((c.program.lines g).op == .mul) = true then
        ∃ p, a ≤ p ∧ p < s ∧ programWord c.program w = List.range' 0 p ∧
          (p, s) ∈ I.intervals.erase (a, b)
      else programWord c.program w = List.range' 0 s := by
    intro g hg s hs1 hs2 hgw
    obtain ⟨hne, hfi, -⟩ := (mem_segChildren_iff c a b root w g).mp hg
    cases hline : c.program.lines g with
    | mk op wires =>
      cases op with
      | mul =>
        simp only [BEq.rfl, ↓reduceIte, ← hfi]
        have hs : s ≠ a := fun h => hne (hroot_unique g (by rw [hline]) (h ▸ hgw))
        simpa only [hline] using hmul_seg g s (by omega) hs2 (by rw [hline]) hgw
      | id =>
        simp only [show ((PrefixOp.id == PrefixOp.mul) = true) = False by decide, ↓reduceIte]
        rw [← hfi, hline]
        exact (programWord_gate_id c.program g wires hline).symm.trans hgw
  -- The state of `w`, and the depth bound at `w`.
  have hbase : (∃ s, a ≤ s ∧ s < b ∧ programWord c.program w = List.range' 0 s) ∧
      c.program.wireDepths w ≤ D := by
    rcases (segActive_iff c a b root w).mp hact with hout | ⟨g, hg⟩
    · simp only [segHasOut, decide_eq_true_eq] at hout
      obtain ⟨j, hj1, hj2, rfl⟩ := hout
      exact ⟨⟨j.val + 1, hj1, hj2, houtWord j⟩, hout_depth j⟩
    · obtain ⟨⟨s, hs1, hs2, hgw, -⟩, -, -, -, hdep⟩ := ih g hg
      have hlt := wireDepths_firstInput_lt c.program g
      rw [((mem_segChildren_iff c a b root w g).mp hg).2.1] at hlt
      refine ⟨?_, by omega⟩
      have h := hchild g hg s hs1 hs2 hgw
      split_ifs at h
      · obtain ⟨p, hp1, hp2, hpw, -⟩ := h
        exact ⟨p, hp1, by omega, hpw⟩
      · exact ⟨s, hs1, hs2, h⟩
  obtain ⟨⟨s, hs1, hs2, hpw⟩, hwD⟩ := hbase
  have hws : wireState c.program w = s := by simp only [wireState, hpw, List.length_range']
  have hmem (i : Fin (segChildren c a b root w).length) :
      (segChildren c a b root w)[i] ∈ segChildren c a b root w := List.getElem_mem _
  rw [buildSegTree_eq]
  refine ⟨⟨s, hs1, hs2, hpw, hws⟩, ⟨hws ▸ hs2, fun i => (ih _ (hmem i)).2.1⟩,
    ⟨(seg_fanout_bound c a b root w).trans (hfan w), fun i => (ih _ (hmem i)).2.2.1⟩,
    ⟨fun i => ?_, fun i => (ih _ (hmem i)).2.2.2.1⟩, ?_⟩
  · obtain ⟨⟨s_i, hsi1, hsi2, hgwi, hsti⟩, -⟩ := ih _ (hmem i)
    have h := hchild _ (hmem i) s_i hsi1 hsi2 hgwi
    dsimp only
    rw [hws, hsti]
    split_ifs at h ⊢
    · obtain ⟨p, -, hp2, hpw', hpI⟩ := h
      obtain rfl : p = s := (List.range'_inj.mp (hpw'.symm.trans hpw)).1
      exact ⟨hp2, hpI⟩
    · exact (List.range'_inj.mp (h.symm.trans hpw)).1
  · refine Nat.add_le_of_le_sub' hwD (Finset.sup_le fun i _ => ?_)
    have hlt := wireDepths_firstInput_lt c.program (segChildren c a b root w)[i]
    rw [((mem_segChildren_iff c a b root w _).mp (hmem i)).2.1] at hlt
    have := (ih _ (hmem i)).2.2.2.2
    dsimp only
    omega
termination_by c.size - w.rank
decreasing_by
  have hlt := rank_firstInput_lt c.program g
  rw [((mem_segChildren_iff c a b root w g).mp hg).2.1] at hlt
  have := Wire.rank_le (Wire.gate g : Wire N c.size)
  omega

private theorem reaches_root_of_seg_wire {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (hN : 1 ≤ N) (ha1 : 1 ≤ a) (root : Wire N c.size) (iv : Finset (ℕ × ℕ))
    (hroot_zero : a = 1 → root = .input ⟨0, hN⟩)
    (hroot_unique : ∀ g : Fin c.size,
      (c.program.lines g).op = .mul →
      programWord c.program (.gate g) = List.range' 0 a → Wire.gate g = root)
    (hmul_seg : ∀ g : Fin c.size, ∀ s, a < s → s < b →
      (c.program.lines g).op = .mul →
      programWord c.program (.gate g) = List.range' 0 s →
        ∃ p, a ≤ p ∧ p < s ∧
          programWord c.program (firstInput (c.program.lines g)) = List.range' 0 p ∧
          (p, s) ∈ iv) :
    ∀ u : Wire N c.size, ∀ s, a ≤ s → s < b →
      programWord c.program u = List.range' 0 s →
      segActive c a b root u = true →
      ReachesInSeg c a b root root u := by
  intro u
  refine prefix_wire_induction c.program
    (fun i s hs1 _ hpw _ => ?_)
    (fun g wires hline ih0 s hs1 hs2 hpw hact => ?_)
    (fun g wires hline ih0 _ s hs1 hs2 hpw hact => ?_) u
  · rw [programWord_input] at hpw
    obtain rfl : s = 1 := by simpa using (congrArg List.length hpw).symm
    obtain rfl : i = ⟨0, hN⟩ := Fin.ext (by simpa using hpw)
    rw [← hroot_zero (by omega)]
    exact ReachesInSeg.refl root
  all_goals
    by_cases hgr : (Wire.gate g : Wire N c.size) = root
    · rw [hgr]; exact ReachesInSeg.refl root
    have hg_ch : g ∈ segChildren c a b root (wires 0) :=
      (mem_segChildren_iff c a b root (wires 0) g).mpr ⟨hgr, by simp only [hline, firstInput], hact⟩
    have hact0 : segActive c a b root (wires 0) = true :=
      (segActive_iff c a b root (wires 0)).mpr (Or.inr ⟨g, hg_ch⟩)
    refine ReachesInSeg.step hg_ch ?_
  · exact ih0 s hs1 hs2 ((programWord_gate_id c.program g wires hline).symm.trans hpw) hact0
  · have hs_ne : s ≠ a := fun heq => hgr (hroot_unique g (by rw [hline]) (heq ▸ hpw))
    obtain ⟨p, hp1, hp2, hpw0, -⟩ := hmul_seg g s (by omega) hs2 (by rw [hline]) hpw
    rw [hline] at hpw0
    exact ih0 p hp1 (by omega) hpw0 hact0

/-- A sum of terms at most one, at most one of which is nonzero, is at most one. -/
private theorem sum_le_one_of_ne_zero_imp_eq {α : Type*} [Fintype α] {f : α → ℕ}
    (hf : ∀ x, f x ≤ 1) (huniq : ∀ x y, f x ≠ 0 → f y ≠ 0 → x = y) : ∑ x, f x ≤ 1 := by
  by_cases h : ∃ x, f x ≠ 0
  · obtain ⟨x, hx⟩ := h
    rw [Fintype.sum_eq_single x fun y hy => by_contra fun hy0 => hy (huniq y x hy0 hx)]
    exact hf x
  · simp only [ne_eq, not_exists, not_not] at h
    simp only [h, Finset.sum_const_zero, zero_le]

/-- Decomposes any optimal (zero-deficiency) fanout-`k` universal prefix circuit of depth `D`
along its principal chain `1 = T 0 < T 1 < ⋯ < T D = N` into valid `(IntervalTree, GenPrefixTree)`
pairs at each step `d < D` ([Sergeev2025PrefixDepth], pp. 2–3). -/
theorem optimal_segment_decomposition {N k : ℕ} (hN : 1 ≤ N)
    {c : PrefixCircuit N} (hopt : IsOptimalPrefixCircuit c) (hfan : FanoutAtMost c k) :
    ∃ T : ℕ → ℕ,
      T 0 = 1 ∧
      T c.depth = N ∧
      ∀ d < c.depth,
        T d < T (d + 1) ∧
        ∃ (I : IntervalTree (T d) (T (d + 1))) (t : GenPrefixTree),
          I.depth ≤ d ∧
          t.state = T d ∧
          t.MaxStateLt (T (d + 1)) ∧
          t.rootBudget + 1 ≤ k ∧
          t.FanoutAtMost k ∧
          d + t.depth ≤ c.depth ∧
          t.Valid (I.intervals.erase (T d, T (d + 1))) ∧
          (∀ s, t.outAt s ≤ 1) ∧
          (∀ m, t.mulCount m ≤ 1) ∧
          T (d + 1) - T d ≤ t.outCount := by
  obtain ⟨hc, hzero_def⟩ := hopt
  set D := c.depth
  obtain ⟨houtWord, hwLast, hB, hF_sub, hF_card, lastMul, hlastSpec,
      hOut_sub, hOut_card, hinter_sub⟩ := universal_mul_sets hN hc
  have hlastWord : ∀ r : Fin (N - 1),
      programWord c.program (.gate (lastMul r)) = List.range' 0 (r.val + 2) :=
    fun r => (hlastSpec r).2.2
  let B : Finset (Fin c.size) := Finset.univ.filter fun g => (c.program.lines g).op = .mul
  let wLast : Wire N c.size := c.outputs ⟨N - 1, by omega⟩
  let F : Finset (Fin c.size) := ancMul c.program wLast
  let OutMul : Finset (Fin c.size) := Finset.univ.image lastMul
  have hc1 := Finset.card_le_card hinter_sub
  have hc2 := List.toFinset_card_le (leftSpine c.program wLast)
  have hc3 := leftSpine_length_le_wireDepths c.program wLast
  have hc4 : c.program.wireDepths wLast ≤ D := c.outputDepths_le_depth ⟨N - 1, by omega⟩
  have hunion_le := Finset.card_le_card (Finset.union_subset hF_sub hOut_sub)
  have hie := Finset.card_union_add_card_inter F OutMul
  dsimp only [B, wLast, F, OutMul] at hc1 hc2 hc3 hc4 hunion_le hie hB hF_card hOut_card
  have hB_eq : F ∪ OutMul = B :=
    Finset.eq_of_subset_of_card_le (Finset.union_subset hF_sub hOut_sub)
      (by dsimp only [B, wLast, F, OutMul]; omega)
  have hinter_eq : F ∩ OutMul = (leftSpine c.program wLast).toFinset :=
    Finset.eq_of_subset_of_card_le hinter_sub (by dsimp only [wLast, F, OutMul]; omega)
  have hspine_len : (leftSpine c.program wLast).length = D := by dsimp only [wLast]; omega
  have hwLast_d : c.program.wireDepths wLast = D := by dsimp only [wLast]; omega
  obtain ⟨v, u, T, hv0, hT0, hvD, hTD, hseg, hanc_part⟩ :=
    spine_decomposition c.program hN wLast N hN hwLast (hspine_len.trans hwLast_d.symm)
  rw [hwLast_d] at hvD hTD hseg hanc_part
  have hchain : StrictMono (fun i : Fin (D + 1) => T i) :=
    Fin.strictMono_iff_lt_succ.mpr fun i => (hseg i i.isLt).1
  have hT_strict : StrictMonoOn T (Set.Iic D) := fun i hi j hj hij =>
    hchain (a := ⟨i, Nat.lt_succ_of_le hi⟩) (b := ⟨j, Nat.lt_succ_of_le hj⟩) hij
  have hT_mono := hT_strict.monotoneOn
  -- Multiplication gates computing a prefix are the gates `lastMul`.
  have hmul_unique (g : Fin c.size) (s : ℕ) (hs2 : 2 ≤ s) (hsN : s ≤ N)
      (hop : (c.program.lines g).op = .mul)
      (hgw : programWord c.program (.gate g) = List.range' 0 s) :
      g = lastMul ⟨s - 2, by lia⟩ := by
    have hgB : g ∈ F ∪ OutMul := hB_eq ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ g, hop⟩
    have hgOut : g ∈ OutMul := by
      rcases Finset.mem_union.mp hgB with hgF | hgO
      · have hsp : g ∈ (leftSpine c.program wLast).toFinset := List.mem_toFinset.mpr
          ((zero_mem_ancMul_iff_mem_leftSpine c.program wLast N hN hwLast g hgF).mp
            (by rw [hgw, List.mem_range'_1]; omega))
        exact (Finset.mem_inter.mp (hinter_eq.symm ▸ hsp : g ∈ F ∩ OutMul)).2
      · exact hgO
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hgOut
    have := (List.range'_inj.mp (hgw.symm.trans (hlastWord r))).1
    exact congrArg lastMul (Fin.ext (by simp only; omega))
  refine ⟨T, hT0, hTD, fun d hd => ?_⟩
  obtain ⟨hTd_lt, ⟨sg, _, hvd_succ, wires_d, hsg_line, hsg_w0, hsg_w1⟩,
      hvd_d, hud_d, hvd_w, hud_w⟩ := hseg d hd
  refine ⟨hTd_lt, ?_⟩
  set a := T d
  set b := T (d + 1)
  set root := v d
  have ha1 : 1 ≤ a := hT0 ▸ hT_mono (Nat.zero_le D) hd.le (Nat.zero_le d)
  have hbN : b ≤ N := hTD ▸ hT_mono hd (Set.mem_Iic.mpr le_rfl) hd
  obtain ⟨I, hI_d, hI_anc⟩ := exists_wireIntervalTree c.program (u d) a b hTd_lt hud_w
  have hroot_zero : a = 1 → root = .input ⟨0, hN⟩ := by
    intro ha_eq
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · dsimp only [root]; rw [hd0, hv0]
    · have ha2 : 1 < a := hT0 ▸ hT_strict (Nat.zero_le D) hd.le hd0
      exact (ha2.ne ha_eq.symm).elim
  -- The segment root is the only multiplication gate at state `a`.
  have hroot_unique : ∀ g : Fin c.size,
      (c.program.lines g).op = .mul →
      programWord c.program (.gate g) = List.range' 0 a → Wire.gate g = root := by
    intro g hop hgw
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · have ha_eq : a = 1 := by dsimp only [a]; rw [hd0, hT0]
      cases hline : c.program.lines g with
      | mk op wires =>
        cases op with
        | id => rw [hline] at hop; cases hop
        | mul =>
          obtain ⟨p, hp, hp1, _⟩ := gateWord_range_split c.program g wires hline
            (a := 0) (b := 1) (by simpa only [ha_eq, Nat.sub_zero] using hgw)
          exact (Nat.not_lt_of_ge hp hp1).elim
    · have ha2 : 1 < a := hT0 ▸ hT_strict (Nat.zero_le D) hd.le hd0
      obtain ⟨_, ⟨sg_prev, _, hv_prev_succ, _, hprev_line, _, _⟩, _, _, _, _⟩ :=
        hseg (d - 1) (by omega)
      have hv_eq : root = .gate sg_prev := by
        dsimp only [root]
        simpa only [show d - 1 + 1 = d by omega] using hv_prev_succ
      rw [hv_eq, hmul_unique g a ha2 (by omega) hop hgw,
        hmul_unique sg_prev a ha2 (by omega) (by rw [hprev_line]) (hv_eq ▸ hvd_w)]
  -- A multiplication gate inside the segment multiplies by an interval of `I`.
  have hmul_seg : ∀ g : Fin c.size, ∀ s, a < s → s < b →
      (c.program.lines g).op = .mul →
      programWord c.program (.gate g) = List.range' 0 s →
        ∃ p, a ≤ p ∧ p < s ∧
          programWord c.program (firstInput (c.program.lines g)) = List.range' 0 p ∧
          (p, s) ∈ I.intervals.erase (a, b) := by
    intro g s has hsb hop hgw
    cases hline : c.program.lines g with
    | mk op wires =>
      cases op with
      | id => rw [hline] at hop; cases hop
      | mul =>
        obtain ⟨p, hp_pos, hps, hw0, hw1⟩ := gateWord_range_split c.program g wires hline
          (a := 0) (b := s) (by simpa only [Nat.sub_zero] using hgw)
        suffices h : a ≤ p ∧ (p, s) ∈ I.intervals from
          ⟨p, h.1, hps, by simpa only [firstInput, Nat.sub_zero] using hw0,
            Finset.mem_erase_of_ne_of_mem (fun he => hsb.ne (congrArg Prod.snd he)) h.2⟩
        obtain ⟨hsw, _, hs_op⟩ := stripId_spec c.program (wires 1)
        rw [hw1] at hsw
        cases hs_id : stripId c.program (wires 1) with
        | input i =>
          rw [hs_id, programWord_input] at hsw
          have : s - p = 1 := by simpa using (congrArg List.length hsw).symm
          rw [show s = p + 1 by omega]
          exact ⟨by omega, I.unit_mem_intervals p (by omega) (by omega)⟩
        | gate g₁ =>
          have hg₁_w : programWord c.program (.gate g₁) = List.range' p (s - p) := hs_id ▸ hsw
          have hg₁_not0 : 0 ∉ programWord c.program (.gate g₁) := by
            rw [hg₁_w, List.mem_range'_1]; omega
          have hg₁_B : g₁ ∈ F ∪ OutMul :=
            hB_eq ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ g₁, hs_op g₁ hs_id⟩
          have hg₁_F : g₁ ∈ F := by
            refine (Finset.mem_union.mp hg₁_B).resolve_right fun hO1 => ?_
            obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hO1
            exact hg₁_not0 (by rw [hlastWord r, List.mem_range'_1]; omega)
          rcases hanc_part g₁ hg₁_F with hsp | ⟨r, hrD, hg₁_ur⟩
          · exact absurd
              ((zero_mem_ancMul_iff_mem_leftSpine c.program wLast N hN hwLast g₁ hg₁_F).mpr hsp)
              hg₁_not0
          · have hr_lt := (hseg r hrD).1
            obtain ⟨p₀, q₀, hp₀, hpq₀, hq₀, hg₁_pq⟩ := (ancMul_range_and_card c.program (u r) (T r)
              (T (r + 1) - T r) (by omega) (hseg r hrD).2.2.2.2.2).1 g₁ hg₁_ur
            obtain ⟨rfl, hlen⟩ := range'_eq_range'_iff (by omega) (hg₁_w.symm.trans hg₁_pq)
            obtain rfl : r = d := by
              rcases lt_trichotomy r d with h | h | h
              · have hsep : T (r + 1) ≤ a := hT_mono (h.trans_le hd.le) hd.le h
                omega
              · exact h
              · have hsep : b ≤ T r := hT_mono (h.trans_le hrD.le) hrD.le h
                omega
            exact ⟨hp₀, hI_anc g₁ hg₁_ur p s (by omega) hg₁_w⟩
  have hreach_out : ∀ (s : ℕ) (_ : a ≤ s) (_ : s < b),
      segHasOut c a b (c.outputs ⟨s - 1, by omega⟩) = true ∧
        ReachesInSeg c a b root root (c.outputs ⟨s - 1, by omega⟩) := by
    intro s hs1 hs2
    have hj_has : segHasOut c a b (c.outputs ⟨s - 1, by omega⟩) = true := by
      simp only [segHasOut, decide_eq_true_eq]
      exact ⟨⟨s - 1, by omega⟩, by dsimp only; omega, by dsimp only; omega, rfl⟩
    refine ⟨hj_has, reaches_root_of_seg_wire c a b hN ha1 root _ hroot_zero hroot_unique hmul_seg
      _ s hs1 hs2 ?_ ((segActive_iff c a b root _).mpr (Or.inl hj_has))⟩
    simpa only [show s - 1 + 1 = s by omega] using houtWord ⟨s - 1, by omega⟩
  have hroot_act : segActive c a b root root = true := by
    obtain ⟨hhas_a, hr_a⟩ := hreach_out a le_rfl hTd_lt
    rcases hr_a.top_inversion with heq | ⟨g, hg, _⟩
    · exact (segActive_iff c a b root root).mpr (Or.inl (heq ▸ hhas_a))
    · exact (segActive_iff c a b root root).mpr (Or.inr ⟨g, hg⟩)
  have hprops := buildSegTree_props c a b D root I hfan houtWord
    (fun j => c.outputDepths_le_depth j) hroot_unique hmul_seg
  let t := buildSegTree c a b root root
  obtain ⟨⟨s_r, _, _, hpw_r, hst_r⟩, hmax_t, hfan_t, hval_t, hd_t⟩ := hprops root hroot_act
  have hsr_eq : s_r = a := (List.range'_inj.mp (hpw_r.symm.trans hvd_w)).1
  have hsg_not : sg ∉ segChildren c a b root root := by
    intro hsg_mem
    obtain ⟨⟨s_sg, _, hs_sg_lt, hpw_sg, _⟩, _⟩ :=
      hprops (.gate sg) ((mem_segChildren_iff c a b root root sg).mp hsg_mem).2.2
    have hpw_b : programWord c.program (.gate sg) = List.range' 0 b := by
      dsimp only [b]
      rw [← hvd_succ]
      by_cases hd1 : d + 1 < D
      · exact (hseg (d + 1) hd1).2.2.2.2.1
      · rw [show d + 1 = D by omega, hvD, hTD]
        exact hwLast
    have := (List.range'_inj.mp (hpw_sg.symm.trans hpw_b)).1
    omega
  have hroot_bud : t.rootBudget + 1 ≤ k := by
    dsimp only [t]
    rw [buildSegTree_eq]
    exact (seg_root_fanout_bound c a b root sg
      (by simp only [hsg_line, firstInput, hsg_w0]) hsg_not).trans (hfan root)
  obtain ⟨hout_cnt, hout_at, hmul_cnt⟩ := buildSegTree_counts c a b root root
  refine ⟨I, t, hI_d.trans hud_d, hst_r.trans hsr_eq, hmax_t, hroot_bud, hfan_t,
    by rw [hvd_d] at hd_t; exact hd_t, hval_t, fun s => ?_, fun m => ?_, ?_⟩
  · -- Each state is the output of at most one wire.
    change (buildSegTree c a b root root).outAt s ≤ 1
    rw [hout_at s]
    have key : ∀ u, segHasOut c a b u = true ∧ wireState c.program u = s →
        ∃ j : Fin N, j.val + 1 = s ∧ c.outputs j = u := by
      rintro u ⟨hhas, hws⟩
      simp only [segHasOut, decide_eq_true_eq] at hhas
      obtain ⟨j, -, -, rfl⟩ := hhas
      exact ⟨j, by simpa only [wireState, houtWord j, List.length_range'] using hws, rfl⟩
    refine sum_le_one_of_ne_zero_imp_eq (fun u => ?_) fun u v hu hv => ?_
    · split_ifs
      exacts [countWireInSeg_le_one c a b root u root, zero_le_one]
    · obtain ⟨j, hj, rfl⟩ := key u (ite_ne_right_iff.mp hu).1
      obtain ⟨j', hj', rfl⟩ := key v (ite_ne_right_iff.mp hv).1
      rw [Fin.ext (show j.val = j'.val by omega)]
  · -- Each state is reached by at most one multiplication gate.
    change (buildSegTree c a b root root).mulCount m ≤ 1
    rw [hmul_cnt m]
    have key : ∀ g : Fin c.size, (if (c.program.lines g).op = .mul ∧
        wireState c.program (.gate g) = m ∧ root ≠ .gate g then
          countWireInSeg c a b root (.gate g) root else 0) ≠ 0 →
        ∃ _ : 2 ≤ m ∧ m ≤ N, g = lastMul ⟨m - 2, by omega⟩ := by
      intro g hg
      obtain ⟨⟨hop, hws, hne⟩, hcnt⟩ := ite_ne_right_iff.mp hg
      obtain ⟨⟨s_g, hs1, hs2, hpw_g, -⟩, -⟩ :=
        hprops (.gate g) ((reaches_of_countWireInSeg_ne_zero hcnt).segActive_of hroot_act)
      obtain rfl : s_g = m := by simpa only [wireState, hpw_g, List.length_range'] using hws
      have hm2 : 2 ≤ s_g := by
        by_contra
        exact hne (hroot_unique g hop ((show s_g = a by omega) ▸ hpw_g)).symm
      exact ⟨⟨hm2, by omega⟩, hmul_unique g s_g hm2 (by omega) hop hpw_g⟩
    refine sum_le_one_of_ne_zero_imp_eq (fun g => ?_) fun g g' hg hg' => ?_
    · split_ifs
      exacts [countWireInSeg_le_one c a b root _ root, zero_le_one]
    · obtain ⟨-, rfl⟩ := key g hg
      obtain ⟨-, rfl⟩ := key g' hg'
      rfl
  · -- The outputs at states `a, …, b - 1` are distinct segment outputs reached from the root.
    change b - a ≤ (buildSegTree c a b root root).outCount
    rw [hout_cnt]
    let outMap : ℕ → Wire N c.size := fun s =>
      if hs : a ≤ s ∧ s < b then c.outputs ⟨s - 1, by omega⟩ else root
    let fCnt : Wire N c.size → ℕ := fun u =>
      if segHasOut c a b u = true then countWireInSeg c a b root u root else 0
    have hinj : Set.InjOn outMap (Finset.Ico a b) := by
      intro s₁ hs₁ s₂ hs₂ heq
      rw [Finset.mem_coe, Finset.mem_Ico] at hs₁ hs₂
      simp only [outMap, hs₁, hs₂, and_self, ↓reduceDIte] at heq
      have hw := congrArg (fun w => (programWord c.program w).length) heq
      simp only [houtWord, List.length_range'] at hw
      omega
    have hone : ∀ s ∈ Finset.Ico a b, 1 ≤ fCnt (outMap s) := by
      intro s hs
      rw [Finset.mem_Ico] at hs
      obtain ⟨hhas_s, hr_s⟩ := hreach_out s hs.1 hs.2
      simp only [fCnt, outMap, hs, and_self, ↓reduceDIte, hhas_s, ↓reduceIte,
        countWireInSeg_eq_one_of_reaches hr_s, le_rfl]
    calc
      b - a ≤ ∑ s ∈ Finset.Ico a b, fCnt (outMap s) := by
        simpa using Finset.card_nsmul_le_sum _ _ 1 hone
      _ = ∑ u ∈ (Finset.Ico a b).image outMap, fCnt u := (Finset.sum_image hinj).symm
      _ ≤ ∑ u : Wire N c.size, fCnt u := Finset.sum_le_sum_of_subset (Finset.subset_univ _)


end Cslib.Circuits.Prefix
