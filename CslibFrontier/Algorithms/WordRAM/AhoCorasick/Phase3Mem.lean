/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.AhoCorasick.BFSCorrect
public import CslibFrontier.Algorithms.WordRAM.AhoCorasick.Phase1Setup
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Foundations.Data.Nat.Div

/-!
# Phase 3a: `BFSMem` Invariant and Depth-1 Root Loop (`exec_bfsRootLoop`)

Shared Word-RAM automaton invariant `BFSMem` together with its frame/update lemmas and the
depth-1 root-loop execution proof (`exec_bfsRootLoop`). Both `Phase3Loop` (`bfsBuildCode`) and
`Phase4Step` / `Phase4Scan` (`scanCode`) build directly on top of `BFSMem` in parallel.

## Main definitions

* `Cslib.Algorithms.WordRAM.AhoCorasick.Input.bfs`: opaque pure BFS automaton `PBFS.build`.
* `Cslib.Algorithms.WordRAM.AhoCorasick.BFSMem`: memory invariant pairing the nine Word-RAM tables
  with `PTrie` and `PBFS`.

## Main results

* `Cslib.Algorithms.WordRAM.AhoCorasick.Input.bfs_spec`: `AutomatonInv` for `inp.bfs`.
* `Cslib.Algorithms.WordRAM.AhoCorasick.bfsMem_init`,
  `Cslib.Algorithms.WordRAM.AhoCorasick.bfsMem_of_eq_below_outBase`,
  `Cslib.Algorithms.WordRAM.AhoCorasick.bfsMem_of_set_delta`,
  `Cslib.Algorithms.WordRAM.AhoCorasick.bfsMem_of_enqueue`: initialization and table updates.
* `Cslib.Algorithms.WordRAM.AhoCorasick.exec_bfsRootLoop`: depth-1 BFS root loop proof.
-/

public section

namespace Cslib.Algorithms.WordRAM.AhoCorasick

open Cslib.WordRAM
open Cslib.Algorithms.Lean.AhoCorasick
open Reg

/-- Pure BFS automaton built from `inp.trie` over alphabet `[0, inp.alphabetSize)`. -/
def Input.bfs (inp : Input) : PBFS := PBFS.build inp.trie inp.alphabetSize

/-- Unfolding equation for opaque `Input.bfs`. -/
theorem Input.bfs_eq (inp : Input) : inp.bfs = PBFS.build inp.trie inp.alphabetSize := by rfl

/-- Completed `AutomatonInv` certificate for `inp.bfs` under `inp.Valid`. -/
theorem Input.bfs_spec {inp : Input} (hv : inp.Valid) :
    AutomatonInv inp.patterns inp.alphabetSize inp.trie inp.bfs := by
  rw [Input.bfs_eq, Input.trie_eq]
  exact build_bfs_spec inp.patterns inp.alphabetSize hv.1

/-- Word-RAM memory invariant matching the partial breadth-first automaton `B : PBFS` over
trie `T : PTrie`. -/
structure BFSMem (inp : Input) (T : PTrie) (B : PBFS) (mem : ℕ → ℕ) : Prop where
  txt : Block.HoldsList inp.textBase inp.text mem
  trie_cell : ∀ u < inp.maxS, ∀ c < inp.alphabetSize,
    mem (inp.trieBase + u * inp.alphabetSize + c) = T.trie u c
  delta_cell : ∀ u < inp.maxS, ∀ c < inp.alphabetSize,
    mem (inp.deltaBase + u * inp.alphabetSize + c) = B.delta u c
  fail_cell : ∀ u < inp.maxS, mem (inp.failBase + u) = B.fail u
  depth_cell : ∀ u < inp.maxS, mem (inp.depthBase + u) = T.depth u
  term_cell : ∀ u < inp.maxS, mem (inp.termBase + u) = T.isTerm u
  outHead_cell : ∀ u < inp.maxS, mem (inp.outHeadBase + u) = B.outHead u
  outNext_cell : ∀ u < inp.maxS, mem (inp.outNextBase + u) = B.outNext u
  queue_cell : ∀ i < inp.maxS, mem (inp.queueBase + i) = B.queue i

/-- Transport a `BFSMem` invariant across writes that agree with `mem` on every address strictly
below `inp.outBase`. Shared by Phase 4 output writes. -/
theorem bfsMem_of_eq_below_outBase {inp : Input} {T : PTrie} {B : PBFS}
    {mem mem' : ℕ → ℕ} (hM : BFSMem inp T B mem)
    (heq : ∀ a < inp.outBase, mem' a = mem a) : BFSMem inp T B mem' := by
  have hlo := layout_order inp
  have hmul : ∀ u < inp.maxS, ∀ c < inp.alphabetSize,
      u * inp.alphabetSize + c < inp.maxS * inp.alphabetSize := fun _ hu _ hc =>
    Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu hc
  refine
    { txt := hM.txt.frame fun a _ ha2 => heq a (by omega)
      trie_cell := fun u hu c hc => (heq _ (by have := hmul u hu c hc; omega)).trans
        (hM.trie_cell u hu c hc)
      delta_cell := fun u hu c hc => (heq _ (by have := hmul u hu c hc; omega)).trans
        (hM.delta_cell u hu c hc)
      fail_cell := fun u hu => (heq _ (by omega)).trans (hM.fail_cell u hu)
      depth_cell := fun u hu => (heq _ (by omega)).trans (hM.depth_cell u hu)
      term_cell := fun u hu => (heq _ (by omega)).trans (hM.term_cell u hu)
      outHead_cell := fun u hu => (heq _ (by omega)).trans (hM.outHead_cell u hu)
      outNext_cell := fun u hu => (heq _ (by omega)).trans (hM.outNext_cell u hu)
      queue_cell := fun i hi => (heq _ (by omega)).trans (hM.queue_cell i hi) }

/-- Initialize `BFSMem inp T PBFS.init` from a freshly built `TrieMem`. -/
theorem bfsMem_init {inp : Input} {T : PTrie} {mem : ℕ → ℕ}
    (hM : TrieMem inp T mem) : BFSMem inp T PBFS.init mem where
  txt := hM.txt
  trie_cell := hM.trie_cell
  delta_cell := fun u hu c hc => by
    have hlo := layout_order inp
    have hlt := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu hc
    exact hM.zero_df _ (by omega) (by omega)
  fail_cell := fun u hu => by
    have hlo := layout_order inp
    exact hM.zero_df _ (by omega) (by omega)
  depth_cell := hM.depth_cell
  term_cell := hM.term_cell
  outHead_cell := fun u hu => by
    have hlo := layout_order inp
    exact hM.zero_rest _ (by omega) (by omega)
  outNext_cell := fun u hu => by
    have hlo := layout_order inp
    exact hM.zero_rest _ (by omega) (by omega)
  queue_cell := fun i hi => by
    have hlo := layout_order inp
    exact hM.zero_rest _ (by omega) (by omega)

private theorem bfsMem_preserves_table {mem : ℕ → ℕ} {base s val : ℕ}
    {f : ℕ → ℕ} {lim : ℕ}
    (h : ∀ u < lim, mem (base + u) = f u) (u : ℕ) (hu : u < lim) :
    Function.update mem (base + s) val (base + u) = Function.update f s val u := by
  by_cases hus : u = s
  · subst hus; simp
  · rw [Function.update_of_ne (by omega), Function.update_of_ne hus]
    exact h u hu

/-- Single-cell update preserving `BFSMem` when writing `delta[u₀, a] := dval`. -/
theorem bfsMem_of_set_delta {inp : Input} {T : PTrie} {B : PBFS} {mem : ℕ → ℕ}
    {u₀ a dval : ℕ} (hu₀ : u₀ < inp.maxS) (ha : a < inp.alphabetSize)
    (hM : BFSMem inp T B mem) :
    BFSMem inp T
      { B with delta := fun u c => if u = u₀ ∧ c = a then dval else B.delta u c }
      (Function.update mem (inp.deltaBase + (u₀ * inp.alphabetSize + a)) dval) := by
  have hlo := layout_order inp
  have hrm₀ := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu₀ ha
  refine
    { txt := hM.txt.frame fun _ _ _ => Function.update_of_ne (by omega) _ _
      trie_cell := fun u hu c hc => by
        have := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu hc
        rw [Function.update_of_ne (by omega)]; exact hM.trie_cell u hu c hc
      delta_cell := fun u hu c hc => by
        dsimp only
        by_cases hrc : u = u₀ ∧ c = a
        · obtain ⟨rfl, rfl⟩ := hrc
          simp only [and_self, ↓reduceIte, ← Nat.add_assoc, Function.update_self]
        · simp only [hrc, ↓reduceIte]
          have hne : inp.deltaBase + u * inp.alphabetSize + c ≠
              inp.deltaBase + (u₀ * inp.alphabetSize + a) := fun heq => by
            obtain ⟨hc_eq, hu_eq⟩ := Nat.eq_of_add_mul_eq (b := u) (b' := u₀) hc ha (by omega)
            exact hrc ⟨hu_eq, hc_eq⟩
          rw [Function.update_of_ne hne]; exact hM.delta_cell u hu c hc
      fail_cell := fun u hu => by rw [Function.update_of_ne (by omega)]; exact hM.fail_cell u hu
      depth_cell := fun u hu => by rw [Function.update_of_ne (by omega)]; exact hM.depth_cell u hu
      term_cell := fun u hu => by rw [Function.update_of_ne (by omega)]; exact hM.term_cell u hu
      outHead_cell := fun u hu => by
        rw [Function.update_of_ne (by omega)]; exact hM.outHead_cell u hu
      outNext_cell := fun u hu => by
        rw [Function.update_of_ne (by omega)]; exact hM.outNext_cell u hu
      queue_cell := fun i hi => by rw [Function.update_of_ne (by omega)]; exact hM.queue_cell i hi }

private theorem bfsMem_of_set_fail_queue {inp : Input} {T : PTrie} {B : PBFS} {mem : ℕ → ℕ}
    {s fval : ℕ} (hs : s < inp.maxS) (hM : BFSMem inp T B mem) :
    BFSMem inp T
      { B with
        fail := Function.update B.fail s fval
        queue := Function.update B.queue B.qTail s
        qTail := B.qTail + 1 }
      (Function.update (Function.update mem (inp.failBase + s) fval)
        (inp.queueBase + B.qTail) s) := by
  have hlo := layout_order inp
  have hmul : ∀ u < inp.maxS, ∀ c < inp.alphabetSize,
      u * inp.alphabetSize + c < inp.maxS * inp.alphabetSize := fun _ hu _ hc =>
    Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu hc
  exact
    { txt := hM.txt.frame fun _ _ _ => by simp (disch := omega) only [Function.update_of_ne]
      trie_cell := fun u hu c hc => by
        have := hmul u hu c hc; simp (disch := omega) only [Function.update_of_ne]
        exact hM.trie_cell u hu c hc
      delta_cell := fun u hu c hc => by
        have := hmul u hu c hc; simp (disch := omega) only [Function.update_of_ne]
        exact hM.delta_cell u hu c hc
      fail_cell := fun u hu => by
        dsimp only; rw [Function.update_of_ne (by omega)]
        exact bfsMem_preserves_table hM.fail_cell u hu
      depth_cell := fun u hu => by
        simp (disch := omega) only [Function.update_of_ne]; exact hM.depth_cell u hu
      term_cell := fun u hu => by
        simp (disch := omega) only [Function.update_of_ne]; exact hM.term_cell u hu
      outHead_cell := fun u hu => by
        simp (disch := omega) only [Function.update_of_ne]; exact hM.outHead_cell u hu
      outNext_cell := fun u hu => by
        simp (disch := omega) only [Function.update_of_ne]; exact hM.outNext_cell u hu
      queue_cell := fun i hi => by
        dsimp only
        exact bfsMem_preserves_table (fun j hj => by
          rw [Function.update_of_ne (by omega)]; exact hM.queue_cell j hj) i hi }

private theorem bfsMem_of_set_out {inp : Input} {T : PTrie} {B : PBFS} {mem : ℕ → ℕ}
    {s onval ohval : ℕ} (hs : s < inp.maxS) (hM : BFSMem inp T B mem) :
    BFSMem inp T
      { B with
        outHead := Function.update B.outHead s ohval
        outNext := Function.update B.outNext s onval }
      (Function.update (Function.update mem (inp.outNextBase + s) onval)
        (inp.outHeadBase + s) ohval) := by
  have hlo := layout_order inp
  have hmul : ∀ u < inp.maxS, ∀ c < inp.alphabetSize,
      u * inp.alphabetSize + c < inp.maxS * inp.alphabetSize := fun _ hu _ hc =>
    Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu hc
  exact
    { txt := hM.txt.frame fun _ _ _ => by simp (disch := omega) only [Function.update_of_ne]
      trie_cell := fun u hu c hc => by
        have := hmul u hu c hc; simp (disch := omega) only [Function.update_of_ne]
        exact hM.trie_cell u hu c hc
      delta_cell := fun u hu c hc => by
        have := hmul u hu c hc; simp (disch := omega) only [Function.update_of_ne]
        exact hM.delta_cell u hu c hc
      fail_cell := fun u hu => by
        simp (disch := omega) only [Function.update_of_ne]; exact hM.fail_cell u hu
      depth_cell := fun u hu => by
        simp (disch := omega) only [Function.update_of_ne]; exact hM.depth_cell u hu
      term_cell := fun u hu => by
        simp (disch := omega) only [Function.update_of_ne]; exact hM.term_cell u hu
      outHead_cell := fun u hu => by
        dsimp only
        exact bfsMem_preserves_table (fun v hv => by
          rw [Function.update_of_ne (by omega)]; exact hM.outHead_cell v hv) u hu
      outNext_cell := fun u hu => by
        dsimp only; rw [Function.update_of_ne (by omega)]
        exact bfsMem_preserves_table hM.outNext_cell u hu
      queue_cell := fun i hi => by
        simp (disch := omega) only [Function.update_of_ne]; exact hM.queue_cell i hi }

/-- Combined five-write update preserving `BFSMem` when enqueuing child state `s`. -/
theorem bfsMem_of_enqueue {inp : Input} {T : PTrie} {B : PBFS} {mem : ℕ → ℕ}
    {u₀ a s fval onval ohval : ℕ} (hu₀ : u₀ < inp.maxS) (ha : a < inp.alphabetSize)
    (hs : s < inp.maxS) (hM : BFSMem inp T B mem) :
    BFSMem inp T
      { B with
        delta := fun u c => if u = u₀ ∧ c = a then s else B.delta u c
        fail := Function.update B.fail s fval
        outHead := Function.update B.outHead s ohval
        outNext := Function.update B.outNext s onval
        queue := Function.update B.queue B.qTail s
        qTail := B.qTail + 1 }
      (Function.update
        (Function.update
          (Function.update
            (Function.update
              (Function.update mem (inp.deltaBase + (u₀ * inp.alphabetSize + a)) s)
              (inp.failBase + s) fval)
            (inp.queueBase + B.qTail) s)
          (inp.outNextBase + s) onval)
        (inp.outHeadBase + s) ohval) :=
  bfsMem_of_set_out hs (bfsMem_of_set_fail_queue hs (bfsMem_of_set_delta hu₀ ha hM))

theorem exec_bfsRootLoop (inp : Input) (w : ℕ) (hvalid : inp.Valid)
    (hw : Fits w inp.wordBound) :
    ∀ (k a : ℕ) (B : PBFS) (x : Data 26),
      a + k = inp.alphabetSize →
      LayoutInv inp x →
      BFSMem inp inp.trie B x.mem →
      RootLoopInv inp.patterns inp.alphabetSize inp.trie a B →
      x.regs r1 = 0 →
      x.regs r2 = B.qTail →
      x.regs r5 = a →
      ∃ y, ExecWithin w (.loop (.lt r5 sigma) bfsRootStepCode) x y (21 * k + 2) ∧
        LayoutInv inp y ∧
        BFSMem inp inp.trie (PBFS.rootLoop inp.trie k a B) y.mem ∧
        y.regs r1 = 0 ∧
        y.regs r2 = (PBFS.rootLoop inp.trie k a B).qTail := by
  intro k
  obtain ⟨hT, hT_maxS, _, _, hterm⟩ := inp.trie_spec hvalid
  have hchar := inp.char_iff hvalid
  have hlo := layout_order inp
  induction k with
  | zero =>
    intro a B x hak hL hM _ hr1 hr2 hr5
    have hstop : ¬(Cond.lt r5 sigma).Holds x := by
      simp only [Cond.holds_lt, hr5, hL.h_sigma]; omega
    exact ⟨x, ExecWithin.loop_exit hstop, hL, hM, hr1, hr2⟩
  | succ k ih =>
    intro a B x hak hL hM hinv hr1 hr2 hr5
    have ha : a < inp.alphabetSize := by omega
    have hc : (Cond.lt r5 sigma).Holds x := by
      simp only [Cond.holds_lt, hr5, hL.h_sigma]; exact ha
    have h0_maxS : 0 < inp.maxS := by omega
    have ha_rm : a < inp.maxS * inp.alphabetSize := by
      simpa only [Nat.mul_zero, Nat.zero_add] using Nat.mul_add_lt_mul_of_lt_of_lt h0_maxS ha
    have ht_read : x.mem (inp.trieBase + a) = inp.trie.trie 0 a := by
      simpa only [Nat.zero_mul, Nat.add_zero] using hM.trie_cell 0 h0_maxS a ha
    have hf_ta : Fits w (inp.trieBase + a) := fits_of_le_outBase hw (by omega)
    have hf_da : Fits w (inp.deltaBase + a) := fits_of_le_outBase hw (by omega)
    have hf_a1 : Fits w (a + 1) := fits_of_le_outBase hw (by omega)
    have hinv_next := rootStep_spec hT hchar hterm ha hinv
    set B' := PBFS.rootStep inp.trie B a
    have hstep : ∃ x₁, ExecWithin w bfsRootStepCode x x₁ 19 ∧
        LayoutInv inp x₁ ∧ BFSMem inp inp.trie B' x₁.mem ∧
        x₁.regs r1 = 0 ∧ x₁.regs r2 = B'.qTail ∧ x₁.regs r5 = a + 1 := by
      have hld : ∃ x₀, ExecWithin w (ram[ r6 ← trieBase + r5; r6 ← *r6 ]) x x₀ 2 ∧
          x₀.regs r6 = inp.trie.trie 0 a ∧ x₀.regs r1 = 0 ∧ x₀.regs r2 = B.qTail ∧
          x₀.regs r5 = a ∧ x₀.mem = x.mem := by
        refine WP.exists_execWithin ?_
        wram_exec [hL.h_trieBase, hr5, ht_read, hf_ta]
        exact ⟨by wram_simp, by wram_simp [hr1], by wram_simp [hr2], by wram_simp [hr5],
          by wram_simp⟩
      obtain ⟨x₀, he₀, hx₀_r6, hx₀_r1, hx₀_r2, hx₀_r5, hx₀_mem⟩ := hld
      have hL₀ : LayoutInv inp x₀ :=
        hL.of_preserves he₀
      by_cases hs_pos : 0 < inp.trie.trie 0 a
      · set s := inp.trie.trie 0 a
        have hs_pos' : 0 < inp.trie.trie 0 a := hs_pos
        have hcond_s : (Cond.lt zero r6).Holds x₀ := by
          simp only [Cond.holds_lt, hL₀.h_zero, hx₀_r6]; exact hs_pos
        have hs_lt : s < inp.trie.numStates := hT.trie_lt 0 hT.one_le a ha
        have hs_maxS : s < inp.maxS := lt_of_lt_of_le hs_lt hT_maxS
        have hqt_lt : B.qTail < inp.trie.numStates :=
          qTail_lt_numStates hT.one_le
            (fun i hi => ⟨(hinv.q_bounds i hi).1, (hinv.q_bounds i hi).2.1⟩) hinv.q_inj
        have hqt_maxS : B.qTail < inp.maxS := lt_of_lt_of_le hqt_lt hT_maxS
        have hf_fs : Fits w (inp.failBase + s) := fits_of_le_outBase hw (by omega)
        have hf_qt : Fits w (inp.queueBase + B.qTail) := fits_of_le_outBase hw (by omega)
        have hf_qt1 : Fits w (B.qTail + 1) := fits_of_le_outBase hw (by omega)
        have hf_ons : Fits w (inp.outNextBase + s) := fits_of_le_outBase hw (by omega)
        have hf_tms : Fits w (inp.termBase + s) := fits_of_le_outBase hw (by omega)
        have hf_ohs : Fits w (inp.outHeadBase + s) := fits_of_le_outBase hw (by omega)
        have htm_read : x₀.mem (inp.termBase + s) = inp.trie.isTerm s := by
          rw [hx₀_mem]; exact hM.term_cell s hs_maxS
        have hmid : ∃ x_m, ExecWithin w (ram[
            r7 ← deltaBase + r5; *r7 ← r6;
            r7 ← failBase + r6; *r7 ← zero;
            r7 ← queueBase + r2; *r7 ← r6;
            r2 ← r2 + one;
            r7 ← outNextBase + r6; *r7 ← zero;
            rState ← termBase + r6; rState ← *rState ]) x₀ x_m 11 ∧
          x_m.regs rState = inp.trie.isTerm s ∧ x_m.regs r6 = s ∧
          x_m.regs r1 = 0 ∧ x_m.regs r2 = B.qTail + 1 ∧ x_m.regs r5 = a ∧
          x_m.mem = Function.update
            (Function.update
              (Function.update
                (Function.update x.mem (inp.deltaBase + a) s)
                (inp.failBase + s) 0)
              (inp.queueBase + B.qTail) s)
            (inp.outNextBase + s) 0 := by
          refine WP.exists_execWithin ?_
          have hne1 : inp.termBase + s ≠ inp.outNextBase + s := by omega
          have hne2 : inp.termBase + s ≠ inp.queueBase + B.qTail := by omega
          have hne3 : inp.termBase + s ≠ inp.failBase + s := by omega
          have hne4 : inp.termBase + s ≠ inp.deltaBase + a := by omega
          wram_exec [hL₀.h_deltaBase, hL₀.h_failBase, hL₀.h_queueBase, hL₀.h_outNextBase,
            hL₀.h_termBase, hL₀.h_zero, hL₀.h_one, hx₀_r5, hx₀_r6, hx₀_r2, hf_da, hf_fs,
            hf_qt, hf_qt1, hf_ons, hf_tms, htm_read, hne1, hne2, hne3, hne4]
          exact ⟨by wram_simp, by wram_simp [hx₀_r6], by wram_simp [hx₀_r1], by wram_simp,
            by wram_simp [hx₀_r5], by wram_simp [hx₀_mem]⟩
        obtain ⟨x_m, he_m, hxm_rS, hxm_r6, hxm_r1, hxm_r2, hxm_r5, hxm_mem⟩ := hmid
        have hL_m : LayoutInv inp x_m :=
          hL₀.of_preserves he_m
        have hoh_br : ∃ x₁, ExecWithin w
            (.branch (.lt zero rState)
              (ram[ r7 ← outHeadBase + r6; *r7 ← r6; r5 ← r5 + one ])
              (ram[ r7 ← outHeadBase + r6; *r7 ← zero; r5 ← r5 + one ])) x_m x₁ 5 ∧
            x₁.regs r1 = 0 ∧ x₁.regs r2 = B.qTail + 1 ∧ x₁.regs r5 = a + 1 ∧
            x₁.mem = Function.update x_m.mem (inp.outHeadBase + s)
              (if 0 < inp.trie.isTerm s then s else 0) := by
          by_cases ht_pos : 0 < inp.trie.isTerm s
          · have hct : (Cond.lt zero rState).Holds x_m := by
              simp only [Cond.holds_lt, hL_m.h_zero, hxm_rS]; exact ht_pos
            have hp : ∃ x₁, ExecWithin w
                (ram[ r7 ← outHeadBase + r6; *r7 ← r6; r5 ← r5 + one ]) x_m x₁ 3 ∧
                x₁.regs r1 = 0 ∧ x₁.regs r2 = B.qTail + 1 ∧ x₁.regs r5 = a + 1 ∧
                x₁.mem = Function.update x_m.mem (inp.outHeadBase + s) s := by
              refine WP.exists_execWithin ?_
              wram_exec [hL_m.h_outHeadBase, hL_m.h_one, hxm_r6, hxm_r5, hf_ohs, hf_a1]
              exact ⟨by wram_simp [hxm_r1], by wram_simp [hxm_r2], by wram_simp, by wram_simp⟩
            obtain ⟨x₁, hep, h1, h2, h5, hm1⟩ := hp
            simp only [ht_pos, ↓reduceIte]
            exact ⟨x₁, (ExecWithin.branch_pos hct hep).mono (by omega), h1, h2, h5, hm1⟩
          · have hct : ¬(Cond.lt zero rState).Holds x_m := by
              simp only [Cond.holds_lt, hL_m.h_zero, hxm_rS]; exact ht_pos
            have hn : ∃ x₁, ExecWithin w
                (ram[ r7 ← outHeadBase + r6; *r7 ← zero; r5 ← r5 + one ]) x_m x₁ 3 ∧
                x₁.regs r1 = 0 ∧ x₁.regs r2 = B.qTail + 1 ∧ x₁.regs r5 = a + 1 ∧
                x₁.mem = Function.update x_m.mem (inp.outHeadBase + s) 0 := by
              refine WP.exists_execWithin ?_
              wram_exec [hL_m.h_outHeadBase, hL_m.h_zero, hL_m.h_one, hxm_r6, hxm_r5,
                hf_ohs, hf_a1]
              exact ⟨by wram_simp [hxm_r1], by wram_simp [hxm_r2], by wram_simp, by wram_simp⟩
            obtain ⟨x₁, hen, h1, h2, h5, hm1⟩ := hn
            simp only [ht_pos, ↓reduceIte]
            exact ⟨x₁, ExecWithin.branch_neg hct hen, h1, h2, h5, hm1⟩
        obtain ⟨x₁, he_oh, hx₁_r1, hx₁_r2, hx₁_r5, hx₁_mem⟩ := hoh_br
        have he_tot : ExecWithin w bfsRootStepCode x x₁ 19 :=
          (he₀.seq (ExecWithin.branch_pos hcond_s (he_m.seq he_oh))).mono (by omega)
        have hL₁ : LayoutInv inp x₁ :=
          hL.of_preserves he_tot
        have hB'_qt : B'.qTail = B.qTail + 1 := by
          dsimp only [B', PBFS.rootStep]; simp only [hs_pos', ↓reduceIte]
        refine ⟨x₁, he_tot, hL₁, ?_, hx₁_r1, hx₁_r2.trans hB'_qt.symm, hx₁_r5⟩
        rw [hx₁_mem, hxm_mem]
        dsimp only [B', PBFS.rootStep]
        simp only [hs_pos', ↓reduceIte]
        simpa only [Nat.zero_mul, Nat.zero_add] using
          bfsMem_of_enqueue h0_maxS ha hs_maxS hM
      · have hs_pos' : ¬0 < inp.trie.trie 0 a := hs_pos
        have hcond_s : ¬(Cond.lt zero r6).Holds x₀ := by
          simp only [Cond.holds_lt, hL₀.h_zero, hx₀_r6]; exact hs_pos
        have hneg : ∃ x₁, ExecWithin w
            (ram[ r7 ← deltaBase + r5; *r7 ← zero; r5 ← r5 + one ]) x₀ x₁ 3 ∧
            x₁.regs r1 = 0 ∧ x₁.regs r2 = B.qTail ∧ x₁.regs r5 = a + 1 ∧
            x₁.mem = Function.update x.mem (inp.deltaBase + a) 0 := by
          refine WP.exists_execWithin ?_
          wram_exec [hL₀.h_deltaBase, hL₀.h_zero, hL₀.h_one, hx₀_r5, hf_da, hf_a1]
          exact ⟨by wram_simp [hx₀_r1], by wram_simp [hx₀_r2], by wram_simp,
            by wram_simp [hx₀_mem]⟩
        obtain ⟨x₁, he_n, hx₁_r1, hx₁_r2, hx₁_r5, hx₁_mem⟩ := hneg
        have he_tot : ExecWithin w bfsRootStepCode x x₁ 19 :=
          (he₀.seq (ExecWithin.branch_neg hcond_s he_n)).mono (by omega)
        have hL₁ : LayoutInv inp x₁ :=
          hL.of_preserves he_tot
        have hB'_qt : B'.qTail = B.qTail := by
          dsimp only [B', PBFS.rootStep]; simp only [hs_pos', ↓reduceIte]
        refine ⟨x₁, he_tot, hL₁, ?_, hx₁_r1, hx₁_r2.trans hB'_qt.symm, hx₁_r5⟩
        rw [hx₁_mem]
        dsimp only [B', PBFS.rootStep]
        simp only [hs_pos', ↓reduceIte]
        simpa only [Nat.zero_mul, Nat.zero_add] using bfsMem_of_set_delta h0_maxS ha hM
    obtain ⟨x₁, he_st, hL₁, hM₁, hx₁_r1, hx₁_r2, hx₁_r5⟩ := hstep
    obtain ⟨y, he_tl, hLy, hMy, hy_r1, hy_r2⟩ :=
      ih (a + 1) B' x₁ (by omega) hL₁ hM₁ hinv_next hx₁_r1 hx₁_r2 hx₁_r5
    exact ⟨y, (ExecWithin.loop_iter hc he_st he_tl).mono (by omega), hLy, hMy, hy_r1, hy_r2⟩

end Cslib.Algorithms.WordRAM.AhoCorasick
