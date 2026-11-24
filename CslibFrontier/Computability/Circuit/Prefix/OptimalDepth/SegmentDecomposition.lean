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
-- segment-tree helpers (`exists_wireIntervalTree`, `spine_decomposition`, `wireState`,
-- `buildSegTree`, `buildSegTree_counts`) from `OptimalDepth.SegmentTree`.
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
          (p, s) ∈ I.intervals.erase (a, b)) :
    ∀ w : Wire N c.size, segActive c a b root w = true →
      (∃ s, a ≤ s ∧ s < b ∧ programWord c.program w = List.range' 0 s ∧
        (buildSegTree c a b root w).state = s) ∧
      (buildSegTree c a b root w).MaxStateLt b ∧
      (buildSegTree c a b root w).FanoutAtMost k ∧
      (buildSegTree c a b root w).Valid (I.intervals.erase (a, b)) ∧
      c.program.wireDepths w + (buildSegTree c a b root w).depth ≤ D := by
  intro w
  have haux : ∀ rem, ∀ w : Wire N c.size, c.size - w.rank = rem →
      segActive c a b root w = true →
      (∃ s, a ≤ s ∧ s < b ∧ programWord c.program w = List.range' 0 s ∧
        (buildSegTree c a b root w).state = s) ∧
      (buildSegTree c a b root w).MaxStateLt b ∧
      (buildSegTree c a b root w).FanoutAtMost k ∧
      (buildSegTree c a b root w).Valid (I.intervals.erase (a, b)) ∧
      c.program.wireDepths w + (buildSegTree c a b root w).depth ≤ D := by
    intro rem
    induction rem using Nat.strong_induction_on with
    | _ rem ih =>
      intro w hrem hact
      have hch_ih : ∀ i : Fin (segChildren c a b root w).length,
          (∃ s, a ≤ s ∧ s < b ∧
            programWord c.program (.gate (segChildren c a b root w)[i]) = List.range' 0 s ∧
            (buildSegTree c a b root (.gate (segChildren c a b root w)[i])).state = s) ∧
          (buildSegTree c a b root (.gate (segChildren c a b root w)[i])).MaxStateLt b ∧
          (buildSegTree c a b root (.gate (segChildren c a b root w)[i])).FanoutAtMost k ∧
          (buildSegTree c a b root (.gate (segChildren c a b root w)[i])).Valid
            (I.intervals.erase (a, b)) ∧
          c.program.wireDepths (.gate (segChildren c a b root w)[i]) +
            (buildSegTree c a b root (.gate (segChildren c a b root w)[i])).depth ≤ D := by
        intro i
        have hmem : (segChildren c a b root w)[i] ∈ segChildren c a b root w := List.getElem_mem _
        obtain ⟨_, _, hact_i⟩ := (mem_segChildren_iff c a b root w _).mp hmem
        have hlt := segChildren_rank_lt c a b root w i
        have hle := Wire.rank_le (Wire.gate (segChildren c a b root w)[i] : Wire N c.size)
        exact ih (c.size - (Wire.gate (segChildren c a b root w)[i] : Wire N c.size).rank)
          (by omega) (.gate (segChildren c a b root w)[i]) rfl hact_i
      have hw_state : ∃ s, a ≤ s ∧ s < b ∧ programWord c.program w = List.range' 0 s := by
        rcases (segActive_iff c a b root w).mp hact with hout | ⟨g, hg⟩
        · simp only [segHasOut, decide_eq_true_eq] at hout
          obtain ⟨j, hj1, hj2, hjeq⟩ := hout
          exact ⟨j.val + 1, hj1, hj2, hjeq ▸ houtWord j⟩
        · obtain ⟨idx, hidx_lt, hidx_eq⟩ := List.getElem_of_mem hg
          let i₀ : Fin (segChildren c a b root w).length := ⟨idx, hidx_lt⟩
          obtain ⟨⟨s', hs1, hs2, hgw, _⟩, _⟩ := hch_ih i₀
          dsimp only [i₀] at hgw
          rw [Fin.getElem_fin, hidx_eq] at hgw
          obtain ⟨hne_r, hfi, _⟩ := (mem_segChildren_iff c a b root w g).mp hg
          cases hline : c.program.lines g with
          | mk op wires =>
            cases op with
            | mul =>
              have hs_ne : s' ≠ a := by
                intro heq
                rw [heq] at hgw
                exact hne_r (hroot_unique g (by rw [hline]) hgw)
              obtain ⟨p, hp1, hp2, hpw, _⟩ :=
                hmul_seg g s' (by omega) hs2 (by rw [hline]) hgw
              exact ⟨p, hp1, by omega, hfi ▸ hpw⟩
            | id =>
              have hpw : programWord c.program (wires 0) = List.range' 0 s' := by
                rw [← programWord_gate_id c.program g wires hline]
                exact hgw
              have hfi0 : wires 0 = w := by simpa only [hline, firstInput] using hfi
              exact ⟨s', hs1, hs2, hfi0 ▸ hpw⟩
      obtain ⟨s, hs1, hs2, hpw⟩ := hw_state
      have hws : wireState c.program w = s := by
        simp only [wireState, hpw, List.length_range']
      have hst_tree : (buildSegTree c a b root w).state = s := by
        rw [buildSegTree_eq]
        exact hws
      refine ⟨⟨s, hs1, hs2, hpw, hst_tree⟩, ?_, ?_, ?_, ?_⟩
      · rw [buildSegTree_eq]
        exact ⟨by rw [hws]; exact hs2, fun i => (hch_ih i).2.1⟩
      · rw [buildSegTree_eq]
        exact ⟨(seg_fanout_bound c a b root w).trans (hfan w), fun i => (hch_ih i).2.2.1⟩
      · rw [buildSegTree_eq]
        refine ⟨fun i => ?_, fun i => (hch_ih i).2.2.2.1⟩
        dsimp only
        let gi := (segChildren c a b root w)[i]
        obtain ⟨⟨s_i, hsi1, hsi2, hgwi, hsti⟩, _⟩ := hch_ih i
        obtain ⟨hne_r, hfi, _⟩ := (mem_segChildren_iff c a b root w gi).mp (List.getElem_mem _)
        change if ((c.program.lines gi).op == .mul) = true then
            wireState c.program w < (buildSegTree c a b root (.gate gi)).state ∧
              (wireState c.program w, (buildSegTree c a b root (.gate gi)).state) ∈
                I.intervals.erase (a, b)
          else (buildSegTree c a b root (.gate gi)).state = wireState c.program w
        change programWord c.program (.gate gi) = List.range' 0 s_i at hgwi
        change (buildSegTree c a b root (.gate gi)).state = s_i at hsti
        rw [hws, hsti]
        cases hline : c.program.lines gi with
        | mk op wires =>
          cases op with
          | mul =>
            simp only [BEq.rfl, ↓reduceIte]
            have hsi_ne : s_i ≠ a := by
              intro heq
              rw [heq] at hgwi
              exact hne_r (hroot_unique gi (by rw [hline]) hgwi)
            obtain ⟨p, hp1, hp2, hpw_p, hpiv⟩ :=
              hmul_seg gi s_i (by omega) hsi2 (by rw [hline]) hgwi
            have hps : p = s := by
              have h1 : List.range' 0 p = List.range' 0 s := by
                rw [← hpw_p, hfi, hpw]
              have := congrArg List.length h1
              simpa only [List.length_range'] using this
            rw [← hps]
            exact ⟨hp2, hpiv⟩
          | id =>
            have hop : ((PrefixOp.id == PrefixOp.mul) = true) = False := by decide
            simp only [hop, ↓reduceIte]
            have h1 : List.range' 0 s_i = List.range' 0 s := by
              rw [← hgwi, programWord_gate_id c.program gi wires hline]
              have hfi0 : wires 0 = w := by simpa only [hline, firstInput] using hfi
              rw [hfi0, hpw]
            have := congrArg List.length h1
            simpa only [List.length_range'] using this
      · rw [buildSegTree_eq]
        simp only [GenPrefixTree.depth]
        by_cases hch0 : (segChildren c a b root w).length = 0
        · have hempty : (Finset.univ : Finset (Fin (segChildren c a b root w).length)) = ∅ := by
            ext i; exact absurd i.isLt (by omega)
          rw [hempty, Finset.sup_empty, Nat.bot_eq_zero, Nat.add_zero]
          rcases (segActive_iff c a b root w).mp hact with hout | ⟨g, hg⟩
          · simp only [segHasOut, decide_eq_true_eq] at hout
            obtain ⟨j, _, _, rfl⟩ := hout
            exact hout_depth j
          · exact absurd (List.length_pos_of_mem hg) (by omega)
        · let i₀ : Fin (segChildren c a b root w).length := ⟨0, by omega⟩
          have hsup_le : (Finset.univ.sup fun i : Fin (segChildren c a b root w).length =>
              (buildSegTree c a b root (.gate (segChildren c a b root w)[i])).depth + 1) ≤
              D - c.program.wireDepths w := by
            refine Finset.sup_le fun i _ => ?_
            have hdi := (hch_ih i).2.2.2.2
            have hmem : (segChildren c a b root w)[i] ∈ segChildren c a b root w :=
              List.getElem_mem _
            obtain ⟨_, hfi, _⟩ := (mem_segChildren_iff c a b root w _).mp hmem
            have hstep := wireDepths_firstInput_lt c.program (segChildren c a b root w)[i]
            rw [hfi] at hstep
            omega
          have hwd_le : c.program.wireDepths w ≤ D := by
            have hdi := (hch_ih i₀).2.2.2.2
            have hmem : (segChildren c a b root w)[i₀] ∈ segChildren c a b root w :=
              List.getElem_mem _
            obtain ⟨_, hfi, _⟩ := (mem_segChildren_iff c a b root w _).mp hmem
            have hstep := wireDepths_firstInput_lt c.program (segChildren c a b root w)[i₀]
            rw [hfi] at hstep
            omega
          omega
  exact haux (c.size - w.rank) w rfl

private theorem reaches_root_of_seg_wire {N : ℕ} (c : PrefixCircuit N) (a b : ℕ)
    (hN : 1 ≤ N) (ha1 : 1 ≤ a) (root : Wire N c.size)
    (hroot_zero : a = 1 → root = .input ⟨0, hN⟩)
    (hroot_unique : ∀ g : Fin c.size,
      (c.program.lines g).op = .mul →
      programWord c.program (.gate g) = List.range' 0 a → Wire.gate g = root)
    (hmul_seg : ∀ g : Fin c.size, ∀ s, a < s → s < b →
      (c.program.lines g).op = .mul →
      programWord c.program (.gate g) = List.range' 0 s →
        ∃ p, a ≤ p ∧ p < s ∧
          programWord c.program (firstInput (c.program.lines g)) = List.range' 0 p) :
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
    have hs_eq : s = 1 := by
      have := congrArg List.length hpw
      simpa only [List.length_singleton, List.length_range'] using this.symm
    subst hs_eq
    have ha_eq : a = 1 := by omega
    simp only [List.range'_one, List.cons.injEq, and_true] at hpw
    have hi : i = ⟨0, hN⟩ := Fin.ext hpw
    rw [hi, ← hroot_zero ha_eq]
    exact ReachesInSeg.refl root
  · by_cases hgr : (Wire.gate g : Wire N c.size) = root
    · rw [hgr]; exact ReachesInSeg.refl root
    · have hpw0 : programWord c.program (wires 0) = List.range' 0 s := by
        rw [← programWord_gate_id c.program g wires hline]; exact hpw
      have hfi : firstInput (c.program.lines g) = wires 0 := by simp only [hline, firstInput]
      have hg_ch : g ∈ segChildren c a b root (wires 0) :=
        (mem_segChildren_iff c a b root (wires 0) g).mpr ⟨hgr, hfi, hact⟩
      have hact0 : segActive c a b root (wires 0) = true :=
        (segActive_iff c a b root (wires 0)).mpr (Or.inr ⟨g, hg_ch⟩)
      exact ReachesInSeg.step hg_ch (ih0 s hs1 hs2 hpw0 hact0)
  · by_cases hgr : (Wire.gate g : Wire N c.size) = root
    · rw [hgr]; exact ReachesInSeg.refl root
    · have hs_ne : s ≠ a := fun heq => hgr (hroot_unique g (by rw [hline]) (heq ▸ hpw))
      obtain ⟨p, hp1, hp2, hpw0⟩ := hmul_seg g s (by omega) hs2 (by rw [hline]) hpw
      have hfi : firstInput (c.program.lines g) = wires 0 := by simp only [hline, firstInput]
      rw [hfi] at hpw0
      have hg_ch : g ∈ segChildren c a b root (wires 0) :=
        (mem_segChildren_iff c a b root (wires 0) g).mpr ⟨hgr, hfi, hact⟩
      have hact0 : segActive c a b root (wires 0) = true :=
        (segActive_iff c a b root (wires 0)).mpr (Or.inr ⟨g, hg_ch⟩)
      exact ReachesInSeg.step hg_ch (ih0 p hp1 (by omega) hpw0 hact0)

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
  have hT_mono : ∀ d₁ d₂, d₁ ≤ d₂ → d₂ ≤ D → T d₁ ≤ T d₂ := by
    intro d₁ d₂ h12 h2D
    induction d₂ with
    | zero =>
      have hd0 : d₁ = 0 := by omega
      rw [hd0]
    | succ d₂ ih =>
      by_cases h_eq : d₁ = d₂ + 1
      · rw [h_eq]
      · exact (ih (by omega) (by omega)).trans (hseg d₂ (by omega)).1.le
  have hT_strict : ∀ d₁ d₂, d₁ < d₂ → d₂ ≤ D → T d₁ < T d₂ := by
    intro d₁ d₂ hlt h2D
    exact lt_of_lt_of_le (hseg d₁ (by omega)).1 (hT_mono (d₁ + 1) d₂ (by omega) h2D)
  have hmul_unique : ∀ (g : Fin c.size) (s : ℕ) (_ : 2 ≤ s) (_ : s ≤ N),
      (c.program.lines g).op = .mul →
      programWord c.program (.gate g) = List.range' 0 s →
      g = lastMul ⟨s - 2, by omega⟩ := by
    intro g s hs2 hsN hop hgw
    have hgB : g ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ g, hop⟩
    rw [← hB_eq, Finset.mem_union] at hgB
    have hgOut : g ∈ OutMul := by
      rcases hgB with hgF | hgO
      · have hsp : g ∈ (leftSpine c.program wLast).toFinset := by
          rw [List.mem_toFinset]
          refine (zero_mem_ancMul_iff_mem_leftSpine c.program wLast N hN hwLast g hgF).mp ?_
          rw [hgw, List.mem_range'_1]; omega
        rw [← hinter_eq, Finset.mem_inter] at hsp
        exact hsp.2
      · exact hgO
    rcases Finset.mem_image.mp hgOut with ⟨r, _, rfl⟩
    have h1 := hgw.symm.trans (hlastWord r)
    have hlen := congrArg List.length h1
    simp only [List.length_range'] at hlen
    congr 1
    exact Fin.ext (by simp only; omega)
  refine ⟨T, hT0, hTD, fun d hd => ?_⟩
  obtain ⟨hTd_lt, ⟨sg, _, hvd_succ, wires_d, hsg_line, hsg_w0, hsg_w1⟩,
      hvd_d, hud_d, hvd_w, hud_w⟩ := hseg d hd
  refine ⟨hTd_lt, ?_⟩
  set a := T d
  set b := T (d + 1)
  set root := v d
  have ha1 : 1 ≤ a := by
    have := hT_mono 0 d (Nat.zero_le d) (by omega)
    omega
  have hbN : b ≤ N := by
    have := hT_mono (d + 1) D (by omega) le_rfl
    omega
  obtain ⟨I, hI_d, hI_anc⟩ := exists_wireIntervalTree c.program (u d) a b hTd_lt hud_w
  have hroot_zero : a = 1 → root = .input ⟨0, hN⟩ := by
    intro ha_eq
    by_cases hd0 : d = 0
    · dsimp only [root]; rw [hd0, hv0]
    · have := hT_strict 0 d (by omega) (by omega)
      omega
  have hroot_unique : ∀ g : Fin c.size,
      (c.program.lines g).op = .mul →
      programWord c.program (.gate g) = List.range' 0 a → Wire.gate g = root := by
    intro g hop hgw
    by_cases hd0 : d = 0
    · have ha_eq : a = 1 := by dsimp only [a]; rw [hd0, hT0]
      rw [ha_eq] at hgw
      cases hline : c.program.lines g with
      | mk op wires =>
        cases op with
        | id => rw [hline] at hop; cases hop
        | mul =>
          rw [programWord_gate_mul c.program g wires hline] at hgw
          have h0_pos : 1 ≤ (programWord c.program (wires 0)).length :=
            List.length_pos_iff.mpr (programWord_ne_nil c.program (wires 0))
          have h1_pos : 1 ≤ (programWord c.program (wires 1)).length :=
            List.length_pos_iff.mpr (programWord_ne_nil c.program (wires 1))
          have hlen := congrArg List.length hgw
          simp only [List.length_append, List.length_range'] at hlen
          omega
    · have ha2 : 2 ≤ a := by
        have := hT_strict 0 d (by omega) (by omega)
        omega
      obtain ⟨_, ⟨sg_prev, _, hv_prev_succ, _, hprev_line, _, _⟩, _, _, _, _⟩ :=
        hseg (d - 1) (by omega)
      have hv_eq : root = .gate sg_prev := by
        dsimp only [root]
        simpa only [show d - 1 + 1 = d by omega] using hv_prev_succ
      have hg_eq := hmul_unique g a ha2 (by omega) hop hgw
      have hprev_eq := hmul_unique sg_prev a ha2 (by omega) (by rw [hprev_line])
        (hv_eq ▸ hvd_w)
      rw [hv_eq, hg_eq, hprev_eq]
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
        rw [programWord_gate_mul c.program g wires hline] at hgw
        obtain ⟨hp_pos, hps_pos, hw0, hw1⟩ := range_split_of_append
          (programWord_ne_nil c.program (wires 0)) (programWord_ne_nil c.program (wires 1)) hgw
        set p := (programWord c.program (wires 0)).length
        rw [Nat.zero_add] at hw1
        obtain ⟨hsw, _, hs_op⟩ := stripId_spec c.program (wires 1)
        rw [hw1] at hsw
        cases hs_id : stripId c.program (wires 1) with
        | input i =>
          rw [hs_id, programWord_input] at hsw
          have hlen := congrArg List.length hsw
          simp only [List.length_singleton, List.length_range'] at hlen
          have hp_eq : p = s - 1 := by omega
          refine ⟨p, by omega, by omega, by simpa only [firstInput] using hw0, ?_⟩
          refine Finset.mem_erase.mpr ⟨?_, ?_⟩
          · intro heq; rw [Prod.mk.injEq] at heq; omega
          · rw [show s = p + 1 by omega]
            exact I.unit_mem_intervals p (by omega) (by omega)
        | gate g₁ =>
          have hg₁_op : (c.program.lines g₁).op = .mul := hs_op g₁ hs_id
          have hg₁_w : programWord c.program (.gate g₁) = List.range' p (s - p) := hs_id ▸ hsw
          have hg₁_not0 : 0 ∉ programWord c.program (.gate g₁) := by
            rw [hg₁_w, List.mem_range'_1]; omega
          have hg₁_B : g₁ ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ g₁, hg₁_op⟩
          rw [← hB_eq, Finset.mem_union] at hg₁_B
          have hg₁_F : g₁ ∈ F := by
            rcases hg₁_B with hF1 | hO1
            · exact hF1
            · rcases Finset.mem_image.mp hO1 with ⟨r, _, rfl⟩
              exfalso
              apply hg₁_not0
              rw [hlastWord r, List.mem_range'_1]; omega
          have hg₁_not_sp : g₁ ∉ leftSpine c.program wLast := fun hsp =>
            hg₁_not0 ((zero_mem_ancMul_iff_mem_leftSpine c.program wLast N hN hwLast g₁ hg₁_F).mpr
              hsp)
          rcases hanc_part g₁ hg₁_F with hsp | ⟨r, hrD, hg₁_ur⟩
          · exact absurd hsp hg₁_not_sp
          · obtain ⟨_, _, _, _, _, hur_w⟩ := hseg r hrD
            have hr_lt := (hseg r hrD).1
            obtain ⟨hsub_r, _⟩ := ancMul_range_and_card c.program (u r) (T r) (T (r + 1) - T r)
              (by omega) hur_w
            obtain ⟨p₀, q₀, hp₀, hpq₀, hq₀, hg₁_pq⟩ := hsub_r g₁ hg₁_ur
            obtain ⟨hp_eq_p₀, hlen_eq⟩ := range'_eq_range'_iff (by omega) (hg₁_w.symm.trans hg₁_pq)
            have hq₀_eq : q₀ = s := by omega
            have hrd : r = d := by
              by_contra hne
              rcases lt_or_gt_of_ne hne with hr_lt_d | hd_lt_r
              · have := hT_mono (r + 1) d (by omega) (by omega)
                omega
              · have := hT_mono (d + 1) r (by omega) (by omega)
                omega
            subst hrd
            have hmem_I := hI_anc g₁ hg₁_ur p s (by omega) hg₁_w
            refine ⟨p, by omega, by omega, by simpa only [firstInput] using hw0,
              Finset.mem_erase.mpr ⟨?_, hmem_I⟩⟩
            intro heq; rw [Prod.mk.injEq] at heq; omega
  have hmul_seg_weak : ∀ g : Fin c.size, ∀ s, a < s → s < b →
      (c.program.lines g).op = .mul →
      programWord c.program (.gate g) = List.range' 0 s →
        ∃ p, a ≤ p ∧ p < s ∧
          programWord c.program (firstInput (c.program.lines g)) = List.range' 0 p :=
    fun g s has hsb hop hgw =>
      let ⟨p, hp1, hp2, hpw, _⟩ := hmul_seg g s has hsb hop hgw
      ⟨p, hp1, hp2, hpw⟩
  have hreach_out : ∀ (s : ℕ) (_ : a ≤ s) (_ : s < b),
      segHasOut c a b (c.outputs ⟨s - 1, by omega⟩) = true ∧
        ReachesInSeg c a b root root (c.outputs ⟨s - 1, by omega⟩) := by
    intro s hs1 hs2
    let j : Fin N := ⟨s - 1, by omega⟩
    have hj_has : segHasOut c a b (c.outputs j) = true := by
      simp only [segHasOut, decide_eq_true_eq]
      exact ⟨j, by dsimp only [j]; omega, by dsimp only [j]; omega, rfl⟩
    have hj_act : segActive c a b root (c.outputs j) = true :=
      (segActive_iff c a b root (c.outputs j)).mpr (Or.inl hj_has)
    have hj_w : programWord c.program (c.outputs j) = List.range' 0 s := by
      simpa only [j, show s - 1 + 1 = s by omega] using houtWord j
    exact ⟨hj_has, reaches_root_of_seg_wire c a b hN ha1 root hroot_zero hroot_unique
      hmul_seg_weak (c.outputs j) s hs1 hs2 hj_w hj_act⟩
  have hroot_act : segActive c a b root root = true := by
    obtain ⟨hhas_a, hr_a⟩ := hreach_out a le_rfl hTd_lt
    rcases hr_a.top_inversion with heq | ⟨g, hg, _⟩
    · rw [heq] at hhas_a
      exact (segActive_iff c a b root root).mpr (Or.inl hhas_a)
    · exact (segActive_iff c a b root root).mpr (Or.inr ⟨g, hg⟩)
  let t := buildSegTree c a b root root
  obtain ⟨⟨s_r, _, _, hpw_r, hst_r⟩, hmax_t, hfan_t, hval_t, hd_t⟩ :=
    buildSegTree_props c a b D root I hfan houtWord
      (fun j => c.outputDepths_le_depth j) hroot_unique hmul_seg root hroot_act
  have hsr_eq : s_r = a := by
    have := congrArg List.length (hpw_r.symm.trans hvd_w)
    simpa only [List.length_range'] using this
  have hsg_fi : firstInput (c.program.lines sg) = root := by
    simp only [hsg_line, firstInput, hsg_w0]
  have hsg_not : sg ∉ segChildren c a b root root := by
    intro hsg_mem
    obtain ⟨_, _, hsg_act⟩ := (mem_segChildren_iff c a b root root sg).mp hsg_mem
    obtain ⟨⟨s_sg, _, hs_sg_lt, hpw_sg, _⟩, _⟩ :=
      buildSegTree_props c a b D root I hfan houtWord
        (fun j => c.outputDepths_le_depth j) hroot_unique hmul_seg (.gate sg) hsg_act
    have hpw_b : programWord c.program (.gate sg) = List.range' 0 b := by
      dsimp only [b]
      rw [← hvd_succ]
      by_cases hd1 : d + 1 < D
      · exact (hseg (d + 1) hd1).2.2.2.2.1
      · have hdD : d + 1 = D := by omega
        rw [hdD, hvD, hTD]
        exact hwLast
    have := congrArg List.length (hpw_sg.symm.trans hpw_b)
    simp only [List.length_range'] at this
    omega
  have hroot_bud : t.rootBudget + 1 ≤ k := by
    have hbud_eq : t.rootBudget =
        (segChildren c a b root root).length + (if segHasOut c a b root then 1 else 0) := by
      dsimp only [t]
      rw [buildSegTree_eq]
      rfl
    rw [hbud_eq]
    exact (seg_root_fanout_bound c a b root sg hsg_fi hsg_not).trans (hfan root)
  obtain ⟨hout_cnt, hout_at, hmul_cnt⟩ := buildSegTree_counts c a b root root
  refine ⟨I, t, hI_d.trans hud_d, hst_r.trans hsr_eq, hmax_t, hroot_bud, hfan_t,
    by rw [hvd_d] at hd_t; exact hd_t, hval_t, ?_, ?_, ?_⟩
  · intro s
    change (buildSegTree c a b root root).outAt s ≤ 1
    rw [hout_at s]
    by_cases hs_in : a ≤ s ∧ s < b
    · let u_s := c.outputs ⟨s - 1, by omega⟩
      have hother : ∀ u : Wire N c.size, u ≠ u_s →
          (if segHasOut c a b u = true ∧ wireState c.program u = s then
            countWireInSeg c a b root u root else 0) = 0 := by
        intro u hne
        split_ifs with hc
        · exfalso
          obtain ⟨hhas_u, hws_u⟩ := hc
          simp only [segHasOut, decide_eq_true_eq] at hhas_u
          obtain ⟨j, _, _, rfl⟩ := hhas_u
          have hj_s : j.val + 1 = s := by
            simpa only [wireState, houtWord j, List.length_range'] using hws_u
          apply hne
          dsimp only [u_s]
          congr 1
          exact Fin.ext (by simp only; omega)
        · rfl
      rw [Fintype.sum_eq_single u_s hother]
      split_ifs
      · exact countWireInSeg_le_one c a b root u_s root
      · exact Nat.zero_le _
    · have hzero : ∀ u : Wire N c.size,
          (if segHasOut c a b u = true ∧ wireState c.program u = s then
            countWireInSeg c a b root u root else 0) = 0 := by
        intro u
        split_ifs with hc
        · exfalso
          obtain ⟨hhas_u, hws_u⟩ := hc
          simp only [segHasOut, decide_eq_true_eq] at hhas_u
          obtain ⟨j, hj1, hj2, rfl⟩ := hhas_u
          have hj_s : j.val + 1 = s := by
            simpa only [wireState, houtWord j, List.length_range'] using hws_u
          omega
        · rfl
      simp only [hzero, Finset.sum_const_zero, Nat.zero_le]
  · intro m
    change (buildSegTree c a b root root).mulCount m ≤ 1
    rw [hmul_cnt m]
    by_cases hm_in : 2 ≤ m ∧ m ≤ N
    · let g_m := lastMul ⟨m - 2, by omega⟩
      have hother : ∀ g : Fin c.size, g ≠ g_m →
          (if (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m ∧
              root ≠ .gate g then
            countWireInSeg c a b root (.gate g) root else 0) = 0 := by
        intro g hne
        split_ifs with hc
        · by_cases hcnt : countWireInSeg c a b root (.gate g) root = 0
          · exact hcnt
          · exfalso
            have hr := reaches_of_countWireInSeg_ne_zero hcnt
            have hact_g := hr.segActive_of hroot_act
            obtain ⟨⟨s_g, _, _, hpw_g, _⟩, _⟩ :=
              buildSegTree_props c a b D root I hfan houtWord
                (fun j => c.outputDepths_le_depth j) hroot_unique hmul_seg (.gate g) hact_g
            have hsm : s_g = m := by
              simpa only [wireState, hpw_g, List.length_range'] using hc.2.1
            rw [hsm] at hpw_g
            exact hne (hmul_unique g m hm_in.1 hm_in.2 hc.1 hpw_g)
        · rfl
      rw [Fintype.sum_eq_single g_m hother]
      split_ifs
      · exact countWireInSeg_le_one c a b root (.gate g_m) root
      · exact Nat.zero_le _
    · have hzero : ∀ g : Fin c.size,
          (if (c.program.lines g).op = .mul ∧ wireState c.program (.gate g) = m ∧
              root ≠ .gate g then
            countWireInSeg c a b root (.gate g) root else 0) = 0 := by
        intro g
        split_ifs with hc
        · by_cases hcnt : countWireInSeg c a b root (.gate g) root = 0
          · exact hcnt
          · exfalso
            have hr := reaches_of_countWireInSeg_ne_zero hcnt
            have hact_g := hr.segActive_of hroot_act
            obtain ⟨⟨s_g, hs1_g, hs2_g, hpw_g, _⟩, _⟩ :=
              buildSegTree_props c a b D root I hfan houtWord
                (fun j => c.outputDepths_le_depth j) hroot_unique hmul_seg (.gate g) hact_g
            have hsm : s_g = m := by
              simpa only [wireState, hpw_g, List.length_range'] using hc.2.1
            have hm2 : 2 ≤ m := by
              by_contra hm_lt2
              have hm_eq_a : m = a := by omega
              rw [hsm, hm_eq_a] at hpw_g
              exact hc.2.2 (hroot_unique g hc.1 hpw_g).symm
            omega
        · rfl
      simp only [hzero, Finset.sum_const_zero, Nat.zero_le]
  · change b - a ≤ (buildSegTree c a b root root).outCount
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
    calc
      b - a = ∑ _s ∈ Finset.Ico a b, 1 := by
        rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul, Nat.mul_one]
      _ ≤ ∑ s ∈ Finset.Ico a b, fCnt (outMap s) := by
        refine Finset.sum_le_sum fun s hs => ?_
        rw [Finset.mem_Ico] at hs
        have h_eq : outMap s = c.outputs ⟨s - 1, by omega⟩ := by
          simp only [outMap, hs, and_self, ↓reduceDIte]
        dsimp only [fCnt]
        rw [h_eq]
        obtain ⟨hhas_s, hr_s⟩ := hreach_out s hs.1 hs.2
        rw [countWireInSeg_eq_one_of_reaches hr_s]
        simp only [hhas_s, ↓reduceIte, le_rfl]
      _ = ∑ u ∈ (Finset.Ico a b).image outMap, fCnt u :=
        (Finset.sum_image (f := fCnt) hinj).symm
      _ ≤ ∑ u : Wire N c.size, fCnt u :=
        Finset.sum_le_sum_of_subset fun u _ => Finset.mem_univ u


end Cslib.Circuits.Prefix
