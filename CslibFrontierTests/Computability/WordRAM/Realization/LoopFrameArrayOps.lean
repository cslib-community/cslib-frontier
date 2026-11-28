/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

-- upstream: local-only (tests)

import CslibFrontier.Computability.WordRAM.Realization.ArrayOps
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize

/-!
# Client tests for `Realization.LoopFrame` and `Realization.ArrayOps`

Exercises `boundedWhile_potential_spec`, `boundedWhile_spec`, `iterate_potential_spec`, concrete
evaluations, `count = 0` boundary cases, and specifications of `fillConstProg`, `Memory.copy`,
`prefixSumProg`, `Memory.allocBlock`, `Memory.allocBlockDirty`, composite `Realizes .exact`
compilation using `realize`, and `Classical.choice`-free `#print axioms` verification.
-/

namespace CslibFrontierTests.Computability.WordRAM.Realization.LoopFrameArrayOps

open Cslib.DataStructure
open Cslib.DataStructure.Memory
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ## 1. Amortized `boundedWhile_potential_spec` on a stateful array-clearing loop -/

private def clearNonzeroGuard (d : ℕ × ℕ) (i : ℕ) : Prop := i < d.2

private instance (d : ℕ × ℕ) (i : ℕ) : Decidable (clearNonzeroGuard d i) :=
  inferInstanceAs (Decidable (i < d.2))

private def clearNonzeroBody (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let v ← Memory.read (d.1.1 + d.2)
  if v = 0 then
    pure (d.2 + 1)
  else
    Memory.write (d.1.1 + d.2) 0
    pure (d.2 + 1)

private def nonzeroPot (base n idx : ℕ) (s : Memory.State) : ℕ :=
  ∑ j ∈ Finset.Ico idx n, if s.mem (base + j) = 0 then 0 else 1

example {w base n : ℕ} {s : Memory.State} (hbound : base + n ≤ s.frontier) :
    let prog := boundedWhile clearNonzeroGuard clearNonzeroBody (base, n) n 0
    let a' := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    a' = n ∧
    Memory.Modifies (Set.Ico base (base + n)) s s' ∧
    s'.frontier = s.frontier ∧
    (∀ j < n, s'.mem (base + j) = 0) ∧
    memoryCost prog s ≤ nonzeroPot base n 0 s + n := by
  let S : Set ℕ := Set.Ico base (base + n)
  let I (idx : ℕ) (t : Memory.State) : Prop :=
    idx ≤ n ∧ t.frontier = s.frontier ∧ ∀ j < idx, t.mem (base + j) = 0
  let rank (idx : ℕ) (_ : Memory.State) : ℕ := n - idx
  have hzero : ∀ idx t, I idx t → rank idx t = 0 → ¬clearNonzeroGuard (base, n) idx := by
    intro idx t ⟨hle, _⟩ hrank hg
    change idx < n at hg
    dsimp only [rank] at hrank
    omega
  have hstep : ∀ idx t, I idx t → clearNonzeroGuard (base, n) idx →
      True ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (clearNonzeroBody ((base, n), idx))) ∧
      let a' := (Memory.spec 0).clientResult t (clearNonzeroBody ((base, n), idx))
      let t' := (Memory.spec 0).clientState t (clearNonzeroBody ((base, n), idx))
      memoryCost (clearNonzeroBody ((base, n), idx)) t + nonzeroPot base n a' t' ≤
        nonzeroPot base n idx t + 1 ∧
      Memory.Modifies S t t' ∧
      I a' t' ∧
      rank a' t' < rank idx t := by
    intro idx t ⟨hle, htfr, hclr⟩ hg
    change idx < n at hg
    have hsum_split :
        nonzeroPot base n idx t =
          (if t.mem (base + idx) = 0 then 0 else 1) +
            ∑ j ∈ Finset.Ico (idx + 1) n, if t.mem (base + j) = 0 then 0 else 1 := by
      rw [nonzeroPot, Finset.sum_eq_sum_Ico_succ_bot hg]
    by_cases hv : t.mem (base + idx) = 0
    · have hvh : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (clearNonzeroBody ((base, n), idx))) := by
        dsimp only [clearNonzeroBody]
        refine validHistory_read_bind (by rw [htfr]; omega) ?_
        simp only [hv, ↓reduceIte]
        exact validHistory_pure w t (idx + 1)
      have hcost : memoryCost (clearNonzeroBody ((base, n), idx)) t = 1 := by
        dsimp only [clearNonzeroBody]
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read]
        simp only [hv, ↓reduceIte, memoryCost_pure]
      have hres : (Memory.spec 0).clientResult t (clearNonzeroBody ((base, n), idx)) =
          idx + 1 := by
        dsimp only [clearNonzeroBody]
        rw [clientResult_bind_read]
        simp only [hv, ↓reduceIte]
        rfl
      have hst : (Memory.spec 0).clientState t (clearNonzeroBody ((base, n), idx)) = t := by
        dsimp only [clearNonzeroBody]
        rw [clientState_bind_read]
        simp only [hv, ↓reduceIte]
        rfl
      refine ⟨trivial, hvh, ?_, ?_, ?_, ?_⟩
      · rw [hres, hst, hcost, hsum_split]
        simp only [hv, ↓reduceIte, Nat.zero_add, nonzeroPot]
        omega
      · rw [hst]; exact Memory.Modifies.refl S t
      · rw [hres, hst]
        refine ⟨by omega, htfr, fun j hj => ?_⟩
        by_cases hji : j = idx
        · rw [hji, hv]
        · exact hclr j (by omega)
      · rw [hres]; dsimp only [rank]; omega
    · have hvh : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (clearNonzeroBody ((base, n), idx))) := by
        dsimp only [clearNonzeroBody]
        refine validHistory_read_bind (by rw [htfr]; omega) ?_
        simp only [hv, ↓reduceIte]
        exact validHistory_write_bind (by rw [htfr]; omega) (fits_zero w)
          (validHistory_pure w _ (idx + 1))
      have hcost : memoryCost (clearNonzeroBody ((base, n), idx)) t = 2 := by
        dsimp only [clearNonzeroBody]
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read]
        simp only [hv, ↓reduceIte, memoryCost_bind', memoryCost_write, memoryCost_pure]
      have hres : (Memory.spec 0).clientResult t (clearNonzeroBody ((base, n), idx)) =
          idx + 1 := by
        dsimp only [clearNonzeroBody]
        rw [clientResult_bind_read]
        simp only [hv, ↓reduceIte, clientResult_bind_write]
        rfl
      have hst : (Memory.spec 0).clientState t (clearNonzeroBody ((base, n), idx)) =
          ⟨Function.update t.mem (base + idx) 0, t.frontier⟩ := by
        dsimp only [clearNonzeroBody]
        rw [clientState_bind_read]
        simp only [hv, ↓reduceIte]
        rfl
      have hcongr :
          nonzeroPot base n (idx + 1) ⟨Function.update t.mem (base + idx) 0, t.frontier⟩ =
            ∑ j ∈ Finset.Ico (idx + 1) n, if t.mem (base + j) = 0 then 0 else 1 := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hlt : idx < j := (Finset.mem_Ico.mp hj).1
        simp only [Function.update_of_ne (by omega : base + j ≠ base + idx)]
      refine ⟨trivial, hvh, ?_, ?_, ?_, ?_⟩
      · rw [hres, hst, hcost, hsum_split, hcongr]
        simp only [hv, ↓reduceIte]
        omega
      · rw [hst]
        exact (Memory.Modifies.write t (base + idx) 0).mono fun x hx => by
          have heq : x = base + idx := hx
          subst heq
          exact ⟨Nat.le_add_right _ _, by omega⟩
      · rw [hres, hst]
        refine ⟨by omega, htfr, fun j hj => ?_⟩
        dsimp only
        by_cases hji : j = idx
        · rw [hji, Function.update_self]
        · rw [Function.update_of_ne (by omega)]
          exact hclr j (by omega)
      · rw [hres]; dsimp only [rank]; omega
  obtain ⟨_, hv, hstop, ⟨hle_end, hfr_end, hclr_end⟩, hmod, hcost⟩ :=
    boundedWhile_potential_spec clearNonzeroGuard clearNonzeroBody
      (fun _ _ _ => True) w (base, n) 1 I rank (nonzeroPot base n) S hzero hstep n 0 s
      ⟨Nat.zero_le n, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩ (by dsimp only [rank]; omega)
  have hna :
      (Memory.spec 0).clientResult s (boundedWhile clearNonzeroGuard clearNonzeroBody (base, n) n 0)
        = n := by
    change ¬clearNonzeroGuard (base, n) _ at hstop
    dsimp only [clearNonzeroGuard] at hstop
    omega
  refine ⟨hv, hna, hmod, hfr_end, fun j hj => hclr_end j (hna.symm ▸ hj), ?_⟩
  simpa [rank] using Nat.le_trans (Nat.le_add_right _ _) hcost

/-! ## 2. Growing-frontier `iterate_potential_spec` with `Modifies` framing -/

private def allocStep (_ : Unit × Block) : Memory.Prog Block := do
  let b ← Memory.alloc 2
  Memory.write b 11
  pure ⟨b, 2⟩

example {w base : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (h11 : Fits w 11) (hfit : Fits w (s.frontier + 6))
    (hb₀ : (Block.mk base 2).Allocated s) (hvals : Block.HoldsList base [3, 4] s.mem) :
    let prog := iterate allocStep () 3 ⟨0, 0⟩
    let s' := (Memory.spec 0).clientState s prog
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    memoryCost prog s ≤ 12 ∧
    Memory.Modifies ∅ s s' ∧
    Block.HoldsList base [3, 4] s'.mem := by
  let inv (k : ℕ) (_ : Block) (t : Memory.State) : Prop :=
    t.frontier = s.frontier + 2 * k ∧ Memory.WellFormed w t
  have hstep : ∀ k < 3, ∀ a t, inv k a t →
      True ∧
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (allocStep ((), a))) ∧
      let a' := (Memory.spec 0).clientResult t (allocStep ((), a))
      let t' := (Memory.spec 0).clientState t (allocStep ((), a))
      memoryCost (allocStep ((), a)) t + 0 ≤ 0 + 4 ∧
      Memory.Modifies ∅ t t' ∧
      inv (k + 1) a' t' := by
    intro k hk a t ⟨htfr, hwt⟩
    have hfk : Fits w (t.frontier + 2) := hfit.of_le (by rw [htfr]; omega)
    have hvh : (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (allocStep ((), a))) := by
      dsimp only [allocStep]
      exact validHistory_alloc_bind hfk
        (validHistory_write_bind (by dsimp only; omega) h11 (validHistory_pure w _ _))
    have hcost : memoryCost (allocStep ((), a)) t ≤ 4 := by
      dsimp only [allocStep]
      rw [memoryCost_bind', memoryCost_alloc, clientResult_alloc, clientState_alloc,
        memoryCost_bind', memoryCost_write, memoryCost_pure]
    have hst : (Memory.spec 0).clientState t (allocStep ((), a)) =
        ⟨Function.update (clear t.mem t.frontier 2) t.frontier 11, t.frontier + 2⟩ := rfl
    have hmod : Memory.Modifies ∅ t
        ⟨Function.update (clear t.mem t.frontier 2) t.frontier 11, t.frontier + 2⟩ :=
      ⟨by simp only; omega, fun x hx _ => by
        change Function.update (clear t.mem t.frontier 2) t.frontier 11 x = t.mem x
        rw [Function.update_of_ne (by omega), clear_of_not_owns (by wram_omega)]⟩
    refine ⟨trivial, hvh, by omega, by rw [hst]; exact hmod, ?_, wellFormed_clientState hwt hvh⟩
    rw [hst]
    dsimp only
    omega
  obtain ⟨_, hv, hcost, hmod, _⟩ :=
    iterate_potential_spec allocStep (fun _ _ _ => True) w () 4 3 inv (fun _ _ _ => 0) ∅
      hstep ⟨0, 0⟩ s ⟨by simp, hwf⟩
  refine ⟨hv, by simpa using hcost, hmod, ?_⟩
  exact Block.holdsList_of_modifies_disjoint hb₀ hvals hmod (Set.empty_disjoint _)

/-! ## 3. Concrete invocations and composite `Realizes .exact` for `ArrayOps` -/

private def sampleState : Memory.State :=
  ⟨fun a => if a = 2 then 3 else if a = 3 then 5 else if a = 4 then 7 else 0, 10⟩

private theorem sample_wf : Memory.WellFormed 8 sampleState := by
  refine ⟨by simp [Fits, sampleState], fun a => ?_⟩
  dsimp only [sampleState]
  split_ifs <;> simp [Fits]

private theorem sample_zeroAbove : Memory.ZeroAbove sampleState := by
  intro a ha
  dsimp only [sampleState] at ha ⊢
  split_ifs <;> omega

-- Concrete execution checks on `sampleState`.
example :
    let s' := (Memory.spec 8).clientState sampleState (fillConstProg 1 9 4)
    s'.frontier = 10 ∧ s'.mem 0 = 0 ∧ s'.mem 1 = 9 ∧ s'.mem 4 = 9 ∧ s'.mem 5 = 0 ∧
    memoryCost (fillConstProg 1 9 4) sampleState ≤ 4 := by
  have h := fillConstProg_spec (w := 8) (base := 1) (val := 9) (count := 4)
    sample_wf (by simp [Fits]) (by simp [Fits]) (by simp [sampleState])
  obtain ⟨_, hcost, hmod, hfr, _, hvals⟩ := framedTriple_iff_realization.mp h
  rw [← clientState_width 8] at hmod hfr hvals
  refine ⟨hfr, hmod.mem_eq_of_not_mem (by simp [sampleState]) (by simp), hvals 0 (by omega),
    hvals 3 (by omega), hmod.mem_eq_of_not_mem (by simp [sampleState]) (by simp), hcost⟩

example :
    let s' := (Memory.spec 8).clientState sampleState (Memory.copy 2 6 3)
    s'.mem 6 = 3 ∧ s'.mem 7 = 5 ∧ s'.mem 8 = 7 ∧ s'.mem 2 = 3 ∧
    memoryCost (Memory.copy 2 6 3) sampleState ≤ 6 := by
  have h : Memory.FramedTriple 8 sampleState (Memory.copy 2 6 3) 6 (Set.Ico 6 9) fun _ s' =>
      s' = ⟨ArrayCopy.copyPrefix sampleState.mem 2 6 3, sampleState.frontier⟩ :=
    Memory.FramedTriple.copy (Or.inl (by omega)) (by simp [sampleState]) (by simp [sampleState])
      (fun _ _ => by dsimp only [sampleState]; split_ifs <;> simp [Fits]) rfl
  obtain ⟨_, hcost, hmod, hst⟩ := framedTriple_iff_realization.mp h
  rw [← clientState_width 8] at hmod hst
  refine ⟨?_, ?_, ?_, hmod.mem_eq_of_not_mem (by simp [sampleState]) (by simp), hcost⟩ <;>
    · rw [hst]
      simp [ArrayCopy.copyPrefix, sampleState]

example :
    let prog := prefixSumProg 2 3
    (Memory.spec 8).clientResult sampleState prog = 15 ∧
    ((Memory.spec 8).clientState sampleState prog).mem 2 = 0 ∧
    ((Memory.spec 8).clientState sampleState prog).mem 3 = 3 ∧
    ((Memory.spec 8).clientState sampleState prog).mem 4 = 8 ∧
    memoryCost prog sampleState ≤ 6 := by
  have hsum_eq : (∑ i ∈ Finset.range 3, sampleState.mem (2 + i)) = 15 := by
    simp [Finset.sum_range_succ, sampleState]
  have h := prefixSumProg_spec (w := 8) (base := 2) (count := 3)
    sample_wf (by simp [Fits]) (by simp [sampleState]) (by rw [hsum_eq]; simp [Fits])
  obtain ⟨_, hcost, _, hres, _, _, hvals⟩ := framedTriple_iff_realization.mp h
  rw [← clientResult_width 8] at hres
  rw [← clientState_width 8] at hvals
  refine ⟨hres.trans hsum_eq, ?_, ?_, ?_, hcost⟩
  · simpa [Finset.sum_range_zero] using hvals 0 (by omega)
  · have h1 := hvals 1 (by omega)
    simpa [Finset.sum_range_succ, sampleState] using h1
  · have h2 := hvals 2 (by omega)
    simpa [Finset.sum_range_succ, sampleState] using h2

example :
    let prog := Memory.allocBlock 4
    let b := (Memory.spec 8).clientResult sampleState prog
    let s' := (Memory.spec 8).clientState sampleState prog
    b = ⟨10, 4⟩ ∧ s'.frontier = 14 ∧ s'.mem 10 = 0 ∧ s'.mem 13 = 0 ∧
    (Block.mk 2 5).Disjoint b ∧ memoryCost prog sampleState ≤ 5 := by
  have h := allocBlock_spec (w := 8) (size := 4) sample_wf (by simp [Fits, sampleState])
  obtain ⟨_, hcost, _, hb, _, _, hzeros, hdisj⟩ := framedTriple_iff_realization.mp h
  rw [← clientResult_width 8] at hb hzeros hdisj
  rw [← clientState_width 8] at hzeros
  exact ⟨hb, rfl,
    hzeros 0 (by omega), hzeros 3 (by omega), hdisj ⟨2, 5⟩ (by simp [Block.Allocated, sampleState]),
    hcost⟩

example :
    let prog := Memory.allocBlockDirty 4
    let b := (Memory.spec 8).clientResult sampleState prog
    let s' := (Memory.spec 8).clientState sampleState prog
    b = ⟨10, 4⟩ ∧ s'.frontier = 14 ∧ s'.mem 12 = 0 ∧ memoryCost prog sampleState ≤ 1 := by
  have h := allocBlockDirty_spec (w := 8) (size := 4)
    sample_wf sample_zeroAbove (by simp [Fits, sampleState])
  obtain ⟨_, hcost, _, hb, _, _, _, hzeros, _⟩ := framedTriple_iff_realization.mp h
  rw [← clientResult_width 8] at hb hzeros
  rw [← clientState_width 8] at hzeros
  exact ⟨hb, rfl,
    hzeros 2 (by omega), hcost⟩

-- Boundary checks at `count = 0`.
example {w base val : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hval : Fits w val) (hbound : base ≤ s.frontier) :
    let prog := fillConstProg base val 0
    memoryCost prog s ≤ 0 ∧
    (∀ a, ((Memory.spec w).clientState s prog).mem a = s.mem a) := by
  have h := fillConstProg_spec hwf hval (fits_zero w) hbound
  refine ⟨by rw [memoryCost_eq_totalCost w]; exact h.cost_le, fun a => ?_⟩
  exact h.mem_eq_of_frontier_eq h.post.1 a (by simp)

example {w src dst : ℕ} {s : Memory.State} (hsrc : src ≤ s.frontier) (hdst : dst ≤ s.frontier) :
    let prog := Memory.copy src dst 0
    memoryCost prog s ≤ 0 ∧
    (∀ a, ((Memory.spec w).clientState s prog).mem a = s.mem a) := by
  have hdisj : src + 0 ≤ dst ∨ dst + 0 ≤ src := by
    rcases le_total src dst with hle | hle
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have h : Memory.FramedTriple w s (Memory.copy src dst 0) 0 (Set.Ico dst (dst + 0)) fun _ s' =>
      s'.frontier = s.frontier :=
    Memory.FramedTriple.copy hdisj hsrc hdst (fun _ hi => absurd hi (Nat.not_lt_zero _)) rfl
  refine ⟨by rw [memoryCost_eq_totalCost w]; exact h.cost_le, fun a => ?_⟩
  exact h.mem_eq_of_frontier_eq h.post a (by simp)

example {w base : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s) (hbound : base ≤ s.frontier) :
    let prog := prefixSumProg base 0
    (Memory.spec w).clientResult s prog = 0 ∧
    memoryCost prog s ≤ 0 ∧
    (∀ a, ((Memory.spec w).clientState s prog).mem a = s.mem a) := by
  have h := prefixSumProg_spec hwf (fits_zero w) hbound (by simp [fits_zero w])
  refine ⟨by simpa using h.post.1, by rw [memoryCost_eq_totalCost w]; simpa using h.cost_le,
    fun a => ?_⟩
  exact h.mem_eq_of_frontier_eq h.post.2.1 a (by simp)

/-- Composite client program combining `Memory.allocBlock`, `Memory.copy`, and `prefixSumProg`,
certified uniformly with `Realizes .exact` (`work = 0`). -/
private def allocCopyPrefixProg (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let b ← Memory.allocBlock d.2
  Memory.copy d.1 b.base d.2
  prefixSumProg b.base d.2

theorem realizes_allocCopyPrefixProg :
    Realizes .exact allocCopyPrefixProg WordEncoding.encode WordEncoding.encode
      (fun w d s =>
        d.1 + d.2 ≤ s.frontier ∧
        Fits w (s.frontier + d.2) ∧
        Fits w (∑ i ∈ Finset.range d.2, s.mem (d.1 + i)))
      (fun _ _ => 0) := by
  unfold allocCopyPrefixProg
  realize [realizes_allocBlock, realizes_copy, realizes_prefixSumProg]
  · have hs1 : (Memory.spec 0).clientState s (Memory.allocBlock d.2) =
        ⟨clear s.mem s.frontier d.2, s.frontier + d.2⟩ := rfl
    change d.1 + d.2 ≤ ((Memory.spec 0).clientState s (Memory.allocBlock d.2)).frontier
    rw [hs1]; dsimp only; omega
  · have hs1 : (Memory.spec 0).clientState s (Memory.allocBlock d.2) =
        ⟨clear s.mem s.frontier d.2, s.frontier + d.2⟩ := rfl
    have hb1 : (Memory.spec 0).clientResult s (Memory.allocBlock d.2) = ⟨s.frontier, d.2⟩ := rfl
    change ((Memory.spec 0).clientResult s (Memory.allocBlock d.2)).base + d.2 ≤
        ((Memory.spec 0).clientState s (Memory.allocBlock d.2)).frontier
    rw [hb1, hs1]
  · have hs1 : (Memory.spec 0).clientState s (Memory.allocBlock d.2) =
        ⟨clear s.mem s.frontier d.2, s.frontier + d.2⟩ := rfl
    have hb1 : (Memory.spec 0).clientResult s (Memory.allocBlock d.2) = ⟨s.frontier, d.2⟩ := rfl
    change ((Memory.spec 0).clientResult s (Memory.allocBlock d.2)).base + d.2 ≤
        ((Memory.spec 0).clientState ((Memory.spec 0).clientState s (Memory.allocBlock d.2))
          (Memory.copy d.1 ((Memory.spec 0).clientResult s (Memory.allocBlock d.2)).base
            d.2)).frontier
    rw [hb1, hs1, Memory.clientState_copy (h := Or.inl h.1)]
  · have hs1 : (Memory.spec 0).clientState s (Memory.allocBlock d.2) =
        ⟨clear s.mem s.frontier d.2, s.frontier + d.2⟩ := rfl
    have hb1 : (Memory.spec 0).clientResult s (Memory.allocBlock d.2) = ⟨s.frontier, d.2⟩ := rfl
    have ha := allocBlock_spec (w := w) (size := d.2) hmem h.2.1
    obtain ⟨_, _, hmod1, _, _, _, _, _⟩ := framedTriple_iff_realization.mp ha
    have hsum_eq :
        (∑ i ∈ Finset.range d.2,
          ((Memory.spec 0).clientState
            ((Memory.spec 0).clientState s (Memory.allocBlock d.2))
            (Memory.copy d.1 ((Memory.spec 0).clientResult s (Memory.allocBlock d.2)).base
              d.2)).mem
            (((Memory.spec 0).clientResult s (Memory.allocBlock d.2)).base + i)) =
        ∑ i ∈ Finset.range d.2, s.mem (d.1 + i) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi_lt : i < d.2 := Finset.mem_range.mp hi
      rw [hb1, hs1, Memory.clientState_copy (h := Or.inl h.1)]
      dsimp only
      rw [ArrayCopy.copyPrefix_read hi_lt]
      exact hmod1.mem_eq_of_not_mem (by omega) (by simp)
    rw [hsum_eq]
    exact h.2.2

private def scanStep (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read (d.1.1 + d.2)
  pure (d.2 + 1)

-- Rank-bounded `boundedWhile_spec` exercise with worst-case cost 1 per step.
example {w base n : ℕ} {s : Memory.State} (hbound : base + n ≤ s.frontier) :
    let prog := boundedWhile clearNonzeroGuard scanStep (base, n) n 0
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (Memory.spec 0).clientResult s prog = n ∧
    memoryCost prog s ≤ n := by
  have hbw := boundedWhile_spec clearNonzeroGuard scanStep (fun _ _ _ => True) w (base, n) 1
    (fun idx t => idx ≤ n ∧ t.frontier = s.frontier) (fun idx _ => n - idx) ∅
    (fun idx _ ⟨hle, _⟩ hr hg => by change idx < n at hg; omega)
    (fun idx t ⟨hle, htfr⟩ hg => by
      change idx < n at hg
      have hvh : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (scanStep ((base, n), idx))) := by
        dsimp only [scanStep]
        exact validHistory_read_bind (by rw [htfr]; omega) (validHistory_pure w t (idx + 1))
      have hcost : memoryCost (scanStep ((base, n), idx)) t ≤ 1 := by
        dsimp only [scanStep]
        rw [memoryCost_bind', memoryCost_read, memoryCost_pure]
      have hres : (Memory.spec 0).clientResult t (scanStep ((base, n), idx)) = idx + 1 := rfl
      have hst : (Memory.spec 0).clientState t (scanStep ((base, n), idx)) = t := rfl
      refine ⟨trivial, hvh, hcost, Memory.Modifies.refl ∅ t,
        ⟨by rw [hres]; omega, by rw [hst]; exact htfr⟩, by rw [hres]; omega⟩)
    n 0 s (⟨Nat.zero_le n, rfl⟩) (by omega)
  obtain ⟨_, hv, hstop, ⟨hle, _⟩, _, hcost⟩ := hbw
  change ¬clearNonzeroGuard (base, n) _ at hstop
  dsimp only [clearNonzeroGuard] at hstop
  refine ⟨hv, by omega, by simpa using hcost⟩

/-! ## 4. Axiom checks (`#print axioms`) -/

/-- info: 'Cslib.WordRAM.Realization.iterate_potential_spec' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.Realization.iterate_potential_spec

/-- info: 'Cslib.WordRAM.Realization.boundedWhile_potential_spec' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.Realization.boundedWhile_potential_spec

/-- info: 'Cslib.WordRAM.Realization.boundedWhile_spec' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.Realization.boundedWhile_spec

end CslibFrontierTests.Computability.WordRAM.Realization.LoopFrameArrayOps
