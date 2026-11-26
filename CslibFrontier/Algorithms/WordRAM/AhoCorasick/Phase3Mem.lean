/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.AhoCorasick.BFSCorrect
public import CslibFrontier.Algorithms.WordRAM.AhoCorasick.Phase1Setup
import all CslibFrontier.Algorithms.WordRAM.AhoCorasick.Layout
import CslibFrontier.Computability.WordRAM.SymbolicExec

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
    AutomatonInv inp.patterns inp.alphabetSize inp.trie inp.bfs :=
  Input.bfs_eq inp ▸ Input.trie_eq inp ▸ build_bfs_spec inp.patterns inp.alphabetSize hv.1

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

private theorem frame_matrix_cells {mem mem' : ℕ → ℕ} {f : ℕ → ℕ → ℕ}
    {base rows cols : ℕ}
    (hread : ∀ u < rows, ∀ c < cols, mem (base + u * cols + c) = f u c)
    (hframe : ∀ a < base + rows * cols, mem' a = mem a) :
    ∀ u < rows, ∀ c < cols, mem' (base + u * cols + c) = f u c := by
  intro u hu c hc
  have hoff : u * cols + c < rows * cols :=
    Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu hc
  exact (hframe _ (by simpa only [Nat.add_assoc] using Nat.add_lt_add_left hoff base)).trans
    (hread u hu c hc)

-- The BFS updates leave the input text and the fixed trie tables in two separate regions.
private theorem BFSMem.frame_trie {inp : Input} {T : PTrie} {B : PBFS} {mem mem' : ℕ → ℕ}
    (hM : BFSMem inp T B mem) (htextTrie : ∀ a < inp.deltaBase, mem' a = mem a)
    (hdepthTerm : ∀ a, inp.depthBase ≤ a → a < inp.outHeadBase → mem' a = mem a) :
    Block.HoldsList inp.textBase inp.text mem' ∧
      (∀ u < inp.maxS, ∀ c < inp.alphabetSize,
        mem' (inp.trieBase + u * inp.alphabetSize + c) = T.trie u c) ∧
      (∀ u < inp.maxS, mem' (inp.depthBase + u) = T.depth u) ∧
      ∀ u < inp.maxS, mem' (inp.termBase + u) = T.isTerm u := by
  have hlo := layout_order inp
  exact ⟨hM.txt.frame (fun a _ ha => htextTrie a (by lia)),
    frame_matrix_cells hM.trie_cell (fun a ha => htextTrie a (by lia)),
    fun u hu => (hdepthTerm _ (Nat.le_add_right _ _) (by lia)).trans (hM.depth_cell u hu),
    fun u hu => (hdepthTerm _ (by lia) (by lia)).trans (hM.term_cell u hu)⟩

/-- Transport a `BFSMem` invariant across writes that agree with `mem` on every address strictly
below `inp.outBase`. Shared by Phase 4 output writes. -/
theorem bfsMem_of_eq_below_outBase {inp : Input} {T : PTrie} {B : PBFS}
    {mem mem' : ℕ → ℕ} (hM : BFSMem inp T B mem)
    (heq : ∀ a < inp.outBase, mem' a = mem a) : BFSMem inp T B mem' := by
  have hlo := layout_order inp
  obtain ⟨htxt, htrie, hdepth, hterm⟩ :=
    hM.frame_trie (fun a ha => heq a (by lia)) (fun a _ ha => heq a (by lia))
  exact
    { txt := htxt
      trie_cell := htrie
      delta_cell := frame_matrix_cells hM.delta_cell (fun a ha => heq a (by lia))
      fail_cell := fun u hu => (heq _ (by lia)).trans (hM.fail_cell u hu)
      depth_cell := hdepth
      term_cell := hterm
      outHead_cell := fun u hu => (heq _ (by omega)).trans (hM.outHead_cell u hu)
      outNext_cell := fun u hu => (heq _ (by omega)).trans (hM.outNext_cell u hu)
      queue_cell := fun i hi => (heq _ (by omega)).trans (hM.queue_cell i hi) }

/-- Initialize `BFSMem inp T PBFS.init` from a freshly built `TrieMem`. -/
theorem bfsMem_init {inp : Input} {T : PTrie} {mem : ℕ → ℕ}
    (hM : TrieMem inp T mem) : BFSMem inp T PBFS.init mem := by
  have hlo := layout_order inp
  exact
    { txt := hM.txt
      trie_cell := hM.trie_cell
      delta_cell := fun u hu c hc =>
        hM.zero_df _ (by omega)
          (by have := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu hc; omega)
      fail_cell := fun u hu => hM.zero_df _ (by omega) (by omega)
      depth_cell := hM.depth_cell
      term_cell := hM.term_cell
      outHead_cell := fun u hu => hM.zero_rest _ (by omega) (by omega)
      outNext_cell := fun u hu => hM.zero_rest _ (by omega) (by omega)
      queue_cell := fun i hi => hM.zero_rest _ (by omega) (by omega) }

/-- Single-cell update preserving `BFSMem` when writing `delta[u₀, a] := dval`. -/
theorem bfsMem_of_set_delta {inp : Input} {T : PTrie} {B : PBFS} {mem : ℕ → ℕ}
    {u₀ a dval : ℕ} (hu₀ : u₀ < inp.maxS) (ha : a < inp.alphabetSize)
    (hM : BFSMem inp T B mem) :
    BFSMem inp T
      { B with delta := fun u c => if u = u₀ ∧ c = a then dval else B.delta u c }
      (Function.update mem (inp.deltaBase + (u₀ * inp.alphabetSize + a)) dval) := by
  have hlo := layout_order inp
  have hrm₀ := Nat.mul_comm _ _ ▸ Nat.mul_add_lt_mul_of_lt_of_lt hu₀ ha
  have hfr (a' : ℕ) (ha' : a' < inp.deltaBase ∨ inp.failBase ≤ a') :
      Function.update mem (inp.deltaBase + (u₀ * inp.alphabetSize + a)) dval a' = mem a' :=
    Function.update_of_ne (by lia) _ _
  obtain ⟨htxt, htrie, hdepth, hterm⟩ := hM.frame_trie (fun a' ha' => hfr a' (.inl ha'))
    (fun a' ha' _ => hfr a' (.inr (by lia)))
  exact
    { txt := htxt
      trie_cell := htrie
      delta_cell := fun u hu c hc => read_update_matrix_cell hc ha (hM.delta_cell u hu c hc)
      fail_cell := fun u hu => (hfr _ (.inr (Nat.le_add_right _ _))).trans (hM.fail_cell u hu)
      depth_cell := hdepth
      term_cell := hterm
      outHead_cell := fun u hu => (hfr _ (.inr (by lia))).trans (hM.outHead_cell u hu)
      outNext_cell := fun u hu => (hfr _ (.inr (by lia))).trans (hM.outNext_cell u hu)
      queue_cell := fun i hi => (hfr _ (.inr (by lia))).trans (hM.queue_cell i hi) }

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
  have hfr (a : ℕ) (h : a < inp.failBase ∨ inp.depthBase ≤ a ∧ a < inp.queueBase) :
      Function.update (Function.update mem (inp.failBase + s) fval)
        (inp.queueBase + B.qTail) s a = mem a := by
    simp (disch := omega) only [Function.update_of_ne]
  obtain ⟨htxt, htrie, hdepth, hterm⟩ :=
    hM.frame_trie (fun a ha => hfr a (.inl (by lia))) (fun a ha₁ ha₂ => hfr a (.inr ⟨ha₁, by lia⟩))
  exact
    { txt := htxt
      trie_cell := htrie
      delta_cell := frame_matrix_cells hM.delta_cell (fun a ha => hfr a (.inl (by lia)))
      fail_cell := fun u hu =>
        (Function.update_of_ne (by lia) _ _).trans (read_update_array_cell (hM.fail_cell u hu))
      depth_cell := hdepth
      term_cell := hterm
      outHead_cell := fun _ hu => (hfr _ (by lia)).trans (hM.outHead_cell _ hu)
      outNext_cell := fun _ hu => (hfr _ (by lia)).trans (hM.outNext_cell _ hu)
      queue_cell := fun i hi => read_update_array_cell
        ((Function.update_of_ne (by lia) _ _).trans (hM.queue_cell i hi)) }

private theorem bfsMem_of_set_out {inp : Input} {T : PTrie} {B : PBFS} {mem : ℕ → ℕ}
    {s onval ohval : ℕ} (hs : s < inp.maxS) (hM : BFSMem inp T B mem) :
    BFSMem inp T
      { B with
        outHead := Function.update B.outHead s ohval
        outNext := Function.update B.outNext s onval }
      (Function.update (Function.update mem (inp.outNextBase + s) onval)
        (inp.outHeadBase + s) ohval) := by
  have hlo := layout_order inp
  have hfr (a : ℕ) (h : a < inp.outHeadBase ∨ inp.queueBase ≤ a) :
      Function.update (Function.update mem (inp.outNextBase + s) onval)
        (inp.outHeadBase + s) ohval a = mem a := by
    simp (disch := omega) only [Function.update_of_ne]
  obtain ⟨htxt, htrie, hdepth, hterm⟩ :=
    hM.frame_trie (fun a ha => hfr a (.inl (by lia))) (fun a _ ha => hfr a (.inl ha))
  exact
    { txt := htxt
      trie_cell := htrie
      delta_cell := frame_matrix_cells hM.delta_cell (fun a ha => hfr a (.inl (by lia)))
      fail_cell := fun _ hu => (hfr _ (.inl (by lia))).trans (hM.fail_cell _ hu)
      depth_cell := hdepth
      term_cell := hterm
      outHead_cell := fun u hu => read_update_array_cell
        ((Function.update_of_ne (by lia) _ _).trans (hM.outHead_cell u hu))
      outNext_cell := fun u hu =>
        (Function.update_of_ne (by lia) _ _).trans (read_update_array_cell (hM.outNext_cell u hu))
      queue_cell := fun _ hi => (hfr _ (.inr (Nat.le_add_right _ _))).trans (hM.queue_cell _ hi) }

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
  intro k a B x hak hL hM hinv hr1 hr2 hr5
  obtain ⟨hT, hT_maxS, _, _, hterm⟩ := inp.trie_spec hvalid
  have hchar := inp.char_iff hvalid
  have hlo := layout_order inp
  induction k generalizing a B x with
  | zero =>
    exact ⟨x, ExecWithin.loop_exit (by simp only [Cond.holds_lt, hr5, hL.h_sigma]; omega),
      hL, hM, hr1, hr2⟩
  | succ k ih =>
    have ha : a < inp.alphabetSize := by omega
    have hc : (Cond.lt r5 sigma).Holds x := by
      simp only [Cond.holds_lt, hr5, hL.h_sigma]; omega
    have h0_maxS : 0 < inp.maxS := by omega
    have ha_rm : a < inp.maxS * inp.alphabetSize :=
      Nat.lt_of_lt_of_le ha (Nat.le_mul_of_pos_left _ h0_maxS)
    have hfit (n : ℕ) (hn : n ≤ inp.outBase := by omega) : Fits w n := fits_of_le_outBase hw hn
    have ht_read : x.mem (inp.trieBase + a) = inp.trie.trie 0 a := by
      simpa only [Nat.zero_mul, Nat.add_zero] using hM.trie_cell 0 h0_maxS a ha
    obtain ⟨x₁, he_st, hM₁, hx₁_r1, hx₁_r2, hx₁_r5⟩ : ∃ x₁, ExecWithin w bfsRootStepCode x x₁ 19 ∧
        BFSMem inp inp.trie (PBFS.rootStep inp.trie B a) x₁.mem ∧ x₁.regs r1 = 0 ∧
        x₁.regs r2 = (PBFS.rootStep inp.trie B a).qTail ∧ x₁.regs r5 = a + 1 := by
      refine WP.exists_execWithin ?_
      unfold bfsRootStepCode
      set s := inp.trie.trie 0 a with hs
      by_cases hs_pos : 0 < s
      · have hs_maxS : s < inp.maxS := lt_of_lt_of_le (hT.trie_lt 0 hT.one_le a ha) hT_maxS
        have hqt_maxS : B.qTail < inp.maxS := lt_of_lt_of_le (qTail_lt_numStates hT.one_le
          (fun i hi => ⟨(hinv.q_bounds i hi).1, (hinv.q_bounds i hi).2.1⟩) hinv.q_inj) hT_maxS
        have hM' := bfsMem_of_enqueue (fval := 0) (onval := 0)
          (ohval := if 0 < inp.trie.isTerm s then s else 0) h0_maxS ha hs_maxS hM
        simp only [Nat.zero_mul, Nat.zero_add] at hM'
        wram_exec [hL.h_trieBase, hL.h_deltaBase, hL.h_failBase, hL.h_queueBase,
          hL.h_outNextBase, hL.h_termBase, hL.h_outHeadBase, hL.h_zero, hL.h_one, hr1, hr2, hr5,
          ht_read, hs_pos, hM.term_cell s hs_maxS, hfit (inp.trieBase + a),
          hfit (inp.deltaBase + a), hfit (inp.failBase + s), hfit (inp.queueBase + B.qTail),
          hfit (B.qTail + 1), hfit (inp.outNextBase + s), hfit (inp.termBase + s),
          hfit (inp.outHeadBase + s), hfit (a + 1)]
        all_goals
          simp only [PBFS.rootStep, ← hs, hs_pos, hc, ↓reduceIte] at hM' ⊢
          exact ⟨by wram_simp [hM'], by wram_simp [hr1], by wram_simp [hr2], by wram_simp⟩
      · wram_exec [hL.h_trieBase, hL.h_deltaBase, hL.h_zero, hL.h_one, hr1, hr2, hr5, ht_read,
          hs_pos, hfit (inp.trieBase + a), hfit (inp.deltaBase + a), hfit (a + 1)]
        simp only [PBFS.rootStep, ← hs, hs_pos, ↓reduceIte]
        have hM' := bfsMem_of_set_delta (dval := 0) h0_maxS ha hM
        simp only [Nat.zero_mul, Nat.zero_add] at hM'
        exact ⟨by wram_simp [hM'], by wram_simp [hr1], by wram_simp [hr2], by wram_simp⟩
    obtain ⟨y, he_tl, hLy, hMy, hy_r1, hy_r2⟩ := ih (a + 1) _ x₁ (by omega) (hL.of_preserves he_st)
      hM₁ (rootStep_spec hT hchar hterm ha hinv) hx₁_r1 hx₁_r2 hx₁_r5
    exact ⟨y, (ExecWithin.loop_iter hc he_st he_tl).mono (by omega), hLy, hMy, hy_r1, hy_r2⟩

end Cslib.Algorithms.WordRAM.AhoCorasick
