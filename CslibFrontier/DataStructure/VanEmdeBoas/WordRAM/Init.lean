/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.VanEmdeBoas.WordRAM.Init.Table
public import CslibFrontier.Computability.WordRAM.Defs
import CslibFrontier.Computability.WordRAM.SymbolicExec
import Mathlib.Tactic.Ring

/-!
# Charged uniform Word-RAM initialization of van Emde Boas trees

This module certifies a single fixed 32-register Word-RAM program (`initProgram`) that initializes
an empty recursive van Emde Boas tree of arbitrary depth `d` at base address `base`, together with
the scratch stack pointer at `base + span d`, without depth-dependent code generation, square-root
oracle instructions, or uncharged zero-memory assumptions.

The initializer executes in three phases:
1. Compute `(universeSize d, span d)` by `d` iterations of the layout recurrences.
2. Set `tableBase = stackBase = base + span d` and populate a `(splitSize k, childSpan k)` lookup
   table of `2 * (d + 1)` words at `[tableBase, tableBase + 2 * (d + 1))`.
3. Traverse the recursive layout in depth-first order using `d` words of per-depth cluster counters
   at `[tableBase + 2 * (d + 1) + 1, tableBase + 3 * d + 2]`, writing `0`, `splitSize k`, and
   `childSpan k` into every depth-`k` header while leaving empty minimum/maximum cells untouched.

The program `initProgram` and its first two phases are developed in
`CslibFrontier.DataStructure.VanEmdeBoas.WordRAM.Init.Table` and re-exported here.

## Main definitions

* `DfsConst`, `DfsState`: the constant-register and loop invariants of the Phase 3 traversal.

## Main results

* `init_dispatch_spec`: structured execution in at most `8 * span d + 20 * d + 24` instructions,
  establishing `Rep (Tree.empty d) base z.mem`, `z.regs root = base`, and
  `z.regs stackBase = base + span d`, while preserving all memory outside
  `[base, base + span d + 4 * (d + 1))`.
* `init_call`, `init_executes`, `init_executes_generic`: bounded-state, flat, and generic RAM
  initialization certificates.
* `init_space_le`: the total tree-plus-scratch footprint is at most
  `10 * universeSize d + 4 * (d + 1)` words.

## References

* [E. Demaine, *Divide and conquer: van Emde Boas trees*, Lecture 4][Demaine2015VanEmdeBoas]
-/

@[expose] public section

namespace Cslib.DataStructure.VanEmdeBoas.WordRAM

open Cslib.WordRAM
open Cslib.DataStructure.VanEmdeBoas

/-! ## Phase 3: depth-first empty-header initialization -/

/-- Constant registers and lookup-table invariant preserved throughout the Phase 3 DFS loop. -/
def DfsConst (base d : ℕ) (s : Data 32) : Prop :=
  s.regs zero = 0 ∧ s.regs one = 1 ∧ s.regs two = 2 ∧
    s.regs three = 3 ∧ s.regs four = 4 ∧ s.regs five = 5 ∧
    s.regs root = base ∧ s.regs depth = d ∧
    s.regs payload = base + span d ∧
    s.regs tableBase = base + span d ∧
    s.regs stackBase = base + span d ∧
    s.regs low = base + span d + 2 * (d + 1) ∧
    TableInv (base + span d) d s.mem

/-- Extract the lookup-table invariant from `DfsConst`. -/
private theorem DfsConst.tableInv {base d : ℕ} {s : Data 32} (hc : DfsConst base d s) :
    TableInv (base + span d) d s.mem :=
  hc.2.2.2.2.2.2.2.2.2.2.2.2

/-- Transfer `DfsConst` across a state update that preserves the twelve constant registers and
establishes the lookup-table invariant on the new memory. -/
private theorem DfsConst.of_regs {base d : ℕ} {s s' : Data 32} (hc : DfsConst base d s)
    (r0 : s'.regs zero = s.regs zero) (r1 : s'.regs one = s.regs one)
    (r2 : s'.regs two = s.regs two) (r3 : s'.regs three = s.regs three)
    (r4 : s'.regs four = s.regs four) (r5 : s'.regs five = s.regs five)
    (rr : s'.regs root = s.regs root) (rd : s'.regs depth = s.regs depth)
    (rp : s'.regs payload = s.regs payload) (rt : s'.regs tableBase = s.regs tableBase)
    (rs : s'.regs stackBase = s.regs stackBase) (rl : s'.regs low = s.regs low)
    (hinv : TableInv (base + span d) d s'.mem) :
    DfsConst base d s' :=
  ⟨r0.trans hc.1, r1.trans hc.2.1, r2.trans hc.2.2.1, r3.trans hc.2.2.2.1,
    r4.trans hc.2.2.2.2.1, r5.trans hc.2.2.2.2.2.1, rr.trans hc.2.2.2.2.2.2.1,
    rd.trans hc.2.2.2.2.2.2.2.1, rp.trans hc.2.2.2.2.2.2.2.2.1,
    rt.trans hc.2.2.2.2.2.2.2.2.2.1, rs.trans hc.2.2.2.2.2.2.2.2.2.2.1,
    rl.trans hc.2.2.2.2.2.2.2.2.2.2.2.1, hinv⟩

/-- Active DFS state at pointer `ptr`, subtree depth `k`, and phase `kindVal` (`0` = enter,
`1` = exit). -/
def DfsState (base d ptr k kindVal : ℕ) (s : Data 32) : Prop :=
  DfsConst base d s ∧
    s.regs p = ptr ∧ s.regs x = k ∧ s.regs kind = kindVal ∧ s.regs runFlag = 1

/-- Every active `DfsState` satisfies the `dfsLoop` continuation condition `0 < runFlag`. -/
private theorem dfsState_cond_holds {base d ptr k kindVal : ℕ} {s : Data 32}
    (hs : DfsState base d ptr k kindVal s) : (Cond.lt zero runFlag).Holds s := by
  obtain ⟨⟨h0, _⟩, _, _, _, hrun⟩ := hs
  simp [Cond.holds_lt, h0, hrun]

/-- `TableInv` depends only on the `2 * (d + 1)` table words starting at `tbl`. -/
private theorem tableInv_congr {tbl d : ℕ} {m m' : ℕ → ℕ}
    (hinv : TableInv tbl d m)
    (h : ∀ a, tbl ≤ a → a < tbl + 2 * (d + 1) → m' a = m a) :
    TableInv tbl d m' := by
  intro j hj
  rw [h (tbl + 2 * j) (by omega) (by omega), h (tbl + 2 * j + 1) (by omega) (by omega)]
  exact hinv j hj

/-- One `dfsBody` step entering a leaf (`kind = 0`, `x = 0`): writes the five-word empty leaf
header at `ptr` and switches to exit mode at `ptr + span 0`. -/
private theorem dfsBody_leaf_spec {w base d ptr : ℕ} {s : Data 32}
    (hs : DfsState base d ptr 0 0 s) (ha : Fits w (base + span d + 4 * (d + 1)))
    (hptr_end : ptr + 5 ≤ base + span d) :
    ∃ s', ExecWithin w dfsBody s s' 14 ∧
      DfsState base d (ptr + span 0) 0 1 s' ∧
      Rep (Tree.empty 0) ptr s'.mem ∧
      (∀ a, a < ptr ∨ ptr + 5 ≤ a → s'.mem a = s.mem a) := by
  have ⟨hc, hp, hx, hkind, hrun⟩ := hs
  have ⟨h0, h1, h2, h3, _, h5, _, _, _, htbl, _, _, hinv⟩ := hc
  have htbl0 : s.mem (base + span d) = 0 := by
    simpa only [Nat.mul_zero, Nat.add_zero, splitSize] using (hinv 0 (by omega)).1
  have htbl1 : s.mem (base + span d + 1) = 0 := by
    simpa only [Nat.mul_zero, Nat.add_zero, childSpan] using (hinv 0 (by omega)).2
  have hf_p5 : Fits w (ptr + 5) := ha.of_le (by omega)
  apply WP.exists_execWithin
  unfold dfsBody dfsEnterBody
  wram_exec [h0, h1, h2, h3, h5, htbl, hp, hx, hkind, htbl0, htbl1]
  have haway : ∀ a, a < ptr ∨ ptr + 5 ≤ a →
      Function.update (Function.update (Function.update s.mem ptr 0) (ptr + 3) 0)
        (ptr + 3 + 1) 0 a = s.mem a := by
    intro a ha_out
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  refine ⟨⟨hc.of_regs (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)
      (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)
      (by wram_simp) (by wram_simp) (by wram_simp) ?_,
    by wram_simp [span], by wram_simp [hx], by wram_simp, by wram_simp [hrun]⟩, ?_, ?_⟩
  · apply tableInv_congr hinv
    intro a ha_lo _
    simpa only [Data.set_mem, Data.write_mem] using haway a (Or.inr (by omega))
  · change Header 0 none ptr _
    simp only [Header, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, splitSize, childSpan]
    exact ⟨by wram_simp, trivial, by wram_simp, by wram_simp [Nat.add_assoc]⟩
  · intro a ha_out
    simpa only [Data.set_mem, Data.write_mem] using haway a ha_out

/-- One `dfsBody` step entering an internal node (`kind = 0`, `x = k + 1`): writes the empty depth
`k + 1` header at `ptr`, initializes the cluster counter at `low + (k + 1)` to `universeSize k`,
and moves to the summary at `ptr + 5` with depth `k`. -/
private theorem dfsBody_enter_succ_spec {w base d ptr k : ℕ} {s : Data 32}
    (hs : DfsState base d ptr (k + 1) 0 s) (hk : k + 1 ≤ d)
    (ha : Fits w (base + span d + 4 * (d + 1))) (hptr_end : ptr + span (k + 1) ≤ base + span d) :
    ∃ s₀, ExecWithin w dfsBody s s₀ 17 ∧
      DfsState base d (ptr + 5) k 0 s₀ ∧
      Header (k + 1) none ptr s₀.mem ∧
      s₀.mem (base + span d + 2 * (d + 1) + (k + 1)) = universeSize k ∧
      (∀ a, (a < ptr ∨ ptr + 5 ≤ a) →
        a ≠ base + span d + 2 * (d + 1) + (k + 1) → s₀.mem a = s.mem a) := by
  have ⟨hc, hp, hx, hkind, hrun⟩ := hs
  have ⟨h0, h1, h2, h3, _, h5, _, _, _, htbl, _, hlow, hinv⟩ := hc
  have h5_le := five_le_span (k + 1)
  have htbl0 : s.mem (base + span d + (k + 1) * 2) = universeSize k := by
    rw [Nat.mul_comm]; exact (hinv (k + 1) hk).1
  have htbl1 : s.mem (base + span d + (k + 1) * 2 + 1) = span k := by
    rw [Nat.mul_comm]; exact (hinv (k + 1) hk).2
  have hf_a1 : Fits w (base + span d + (k + 1) * 2 + 1) := ha.of_le (by omega)
  have hf_p5 : Fits w (ptr + 5) := ha.of_le (by omega)
  have hf_lw : Fits w (base + span d + 2 * (d + 1) + (k + 1)) := ha.of_le (by omega)
  have hne : k + 1 ≠ 0 := by omega
  apply WP.exists_execWithin
  unfold dfsBody dfsEnterBody
  wram_exec [h0, h1, h2, h3, h5, htbl, hlow, hp, hx, hkind, htbl0, htbl1, hne]
  let lw := base + span d + 2 * (d + 1)
  have haway : ∀ a, (a < ptr ∨ ptr + 5 ≤ a) → a ≠ lw + (k + 1) →
      Function.update
        (Function.update
          (Function.update (Function.update s.mem ptr 0) (ptr + 3) (universeSize k))
          (ptr + 3 + 1) (span k))
        (lw + (k + 1)) (universeSize k) a = s.mem a := by
    intro a ha_ptr ha_lw
    rw [Function.update_of_ne ha_lw, Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  refine ⟨⟨hc.of_regs (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)
      (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)
      (by wram_simp) (by wram_simp) (by wram_simp) ?_,
    by wram_simp, by wram_simp, by wram_simp [hkind], by wram_simp [hrun]⟩,
    ?_, by wram_simp, ?_⟩
  · apply tableInv_congr hinv
    intro a ha_lo ha_hi
    simpa only [Data.set_mem, Data.write_mem] using haway a (Or.inr (by omega)) (by omega)
  · simp only [Header, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, splitSize, childSpan]
    exact ⟨by wram_simp, trivial, by wram_simp, by wram_simp [Nat.add_assoc]⟩
  · intro a ha_ptr ha_lw
    simpa only [Data.set_mem, Data.write_mem] using haway a ha_ptr ha_lw

/-- One `dfsBody` step advancing from a completed child to the next cluster (`kind = 1`, `x = k`,
`mem (low + k + 1) = cnt + 1`): decrements the counter and re-enters at depth `k`. -/
private theorem dfsBody_next_cluster_spec {w base d ptr k cnt : ℕ} {s : Data 32}
    (hs : DfsState base d ptr k 1 s) (hk : k + 1 ≤ d)
    (hcnt : s.mem (base + span d + 2 * (d + 1) + (k + 1)) = cnt + 1)
    (ha : Fits w (base + span d + 4 * (d + 1))) (hcnt_fit : Fits w cnt) :
    ∃ s₁, ExecWithin w dfsBody s s₁ 13 ∧
      DfsState base d ptr k 0 s₁ ∧
      s₁.mem (base + span d + 2 * (d + 1) + (k + 1)) = cnt ∧
      (∀ a, a ≠ base + span d + 2 * (d + 1) + (k + 1) → s₁.mem a = s.mem a) := by
  have ⟨hc, hp, hx, hkind, hrun⟩ := hs
  have ⟨h0, h1, _, _, _, _, _, hdepth, _, _, _, hlow, hinv⟩ := hc
  have hf_lw : Fits w (base + span d + 2 * (d + 1) + (k + 1)) := ha.of_le (by omega)
  have hnot_lt : ¬d < k + 1 := by omega
  have hne : cnt + 1 ≠ 0 := by omega
  apply WP.exists_execWithin
  unfold dfsBody dfsExitBody
  wram_exec [h0, h1, hdepth, hlow, hx, hkind, hcnt, hnot_lt, hne]
  refine ⟨⟨hc.of_regs (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)
      (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)
      (by wram_simp) (by wram_simp) (by wram_simp) ?_,
    by wram_simp [hp], by wram_simp, by wram_simp, by wram_simp [hrun]⟩,
    by wram_simp, fun a ha_ne => by wram_simp⟩
  apply tableInv_congr hinv
  intro a _ ha_hi
  have ha_ne : a ≠ base + span d + 2 * (d + 1) + (k + 1) := by omega
  wram_simp

/-- One `dfsBody` step finishing all clusters of a depth `k + 1` node (`kind = 1`, `x = k`,
`mem (low + k + 1) = 0`). -/
private theorem dfsBody_exit_node_spec {w base d ptr k : ℕ} {s : Data 32}
    (hs : DfsState base d ptr k 1 s) (hk : k + 1 ≤ d)
    (hrem : s.mem (base + span d + 2 * (d + 1) + (k + 1)) = 0)
    (ha : Fits w (base + span d + 4 * (d + 1))) :
    ∃ s', ExecWithin w dfsBody s s' 9 ∧
      DfsState base d ptr (k + 1) 1 s' ∧ s'.mem = s.mem := by
  have ⟨hc, hp, hx, hkind, hrun⟩ := hs
  have ⟨h0, h1, _, _, _, _, _, hdepth, _, _, _, hlow, hinv⟩ := hc
  have hf_lw : Fits w (base + span d + 2 * (d + 1) + (k + 1)) := ha.of_le (by omega)
  have hnot_lt : ¬d < k + 1 := by omega
  apply WP.exists_execWithin
  unfold dfsBody dfsExitBody
  wram_exec [h0, h1, hdepth, hlow, hx, hkind, hrem, hnot_lt]
  exact ⟨⟨hc.of_regs (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)
      (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)
      (by wram_simp) (by wram_simp) (by wram_simp) (by simpa only [Data.set_mem] using hinv),
    by wram_simp [hp], by wram_simp, by wram_simp, by wram_simp [hrun]⟩, by wram_simp⟩

/-- Final `dfsBody` step exiting the root (`kind = 1`, `x = d`): clears `runFlag` and preserves
`zero`, `root`, `payload`, `stackBase`, and memory. -/
private theorem dfsBody_finish_spec {w base d ptr : ℕ} {s : Data 32}
    (hs : DfsState base d ptr d 1 s) (ha : Fits w (base + span d + 4 * (d + 1))) :
    ∃ z, ExecWithin w dfsBody s z 5 ∧
      z.regs zero = 0 ∧ z.regs runFlag = 0 ∧
      z.regs root = base ∧ z.regs payload = base + span d ∧ z.regs stackBase = base + span d ∧
      z.mem = s.mem := by
  obtain ⟨hc, _, hx, hkind, _⟩ := hs
  obtain ⟨h0, h1, _, _, _, _, hroot, hdepth, hpay, _, hstk, _, _⟩ := hc
  have hlt : d < d + 1 := by omega
  apply WP.exists_execWithin
  unfold dfsBody dfsExitBody
  wram_exec [h0, h1, hdepth, hx, hkind, hlt]
  exact ⟨by wram_simp [h0], by wram_simp, by wram_simp [hroot],
    by wram_simp [hpay], by wram_simp [hstk], by wram_simp⟩

/-- Cluster-iteration helper for `dfs_subtree_spec` at depth `k + 1`: given the induction
hypothesis `ih` at depth `k`, initializes the remaining `cnt` clusters starting at index `m`
(where `m + cnt = universeSize k`) in `cnt * (8 * span k)` loop instructions. -/
private theorem dfs_clusters_spec {w base d ptr k : ℕ}
    (hk : k + 1 ≤ d) (ha : Fits w (base + span d + 4 * (d + 1)))
    (hptr_end : ptr + span (k + 1) ≤ base + span d)
    (ih : ∀ {p₀ : ℕ} {s₀ : Data 32},
      DfsState base d p₀ k 0 s₀ → p₀ + span k ≤ base + span d →
      ∃ s₁, DfsState base d (p₀ + span k) k 1 s₁ ∧
        Rep (Tree.empty k) p₀ s₁.mem ∧
        (∀ a, (a < p₀ ∨ p₀ + span k ≤ a) →
          (a < base + span d + 2 * (d + 1) + 1 ∨
            base + span d + 2 * (d + 1) + k < a) →
          s₁.mem a = s₀.mem a) ∧
        (∀ z T_cont, ExecWithin w dfsLoop s₁ z T_cont →
          ExecWithin w dfsLoop s₀ z (8 * span k - 15 + T_cont)))
    (cnt : ℕ) {m : ℕ} {s : Data 32} (hm : m + cnt = universeSize k)
    (hs : DfsState base d (ptr + 5 + (m + 1) * span k) k 1 s)
    (hcnt : s.mem (base + span d + 2 * (d + 1) + (k + 1)) = cnt)
    (hprev : ∀ i : Fin (universeSize k), i.val < m →
      Rep (Tree.empty k) (ptr + clusterOffset k i.val) s.mem) :
    ∃ s', DfsState base d (ptr + span (k + 1)) k 1 s' ∧
      s'.mem (base + span d + 2 * (d + 1) + (k + 1)) = 0 ∧
      (∀ i : Fin (universeSize k),
        Rep (Tree.empty k) (ptr + clusterOffset k i.val) s'.mem) ∧
      (∀ a, (a < ptr + 5 + (m + 1) * span k ∨ ptr + span (k + 1) ≤ a) →
        (a < base + span d + 2 * (d + 1) + 1 ∨
          base + span d + 2 * (d + 1) + (k + 1) < a) →
        s'.mem a = s.mem a) ∧
      (∀ z T_cont, ExecWithin w dfsLoop s' z T_cont →
        ExecWithin w dfsLoop s z (cnt * (8 * span k) + T_cont)) := by
  induction cnt generalizing m s with
  | zero =>
    have hm_eq : m = universeSize k := by omega
    have hptr_eq : ptr + 5 + (m + 1) * span k = ptr + span (k + 1) := by
      rw [hm_eq, span_succ]; omega
    refine ⟨s, hptr_eq ▸ hs, hcnt, fun i => hprev i (hm_eq ▸ i.isLt),
      fun _ _ _ => rfl, fun z T_cont hcont => by
        simpa only [Nat.zero_mul, Nat.zero_add] using hcont⟩
  | succ cnt ih_cnt =>
    have hm_lt : m < universeSize k := by omega
    have hu_le : universeSize k ≤ span d :=
      (universeSize_le_span k).trans (span_mono (by omega))
    have hcnt_fit : Fits w cnt := ha.of_le (by omega)
    let p_m := ptr + 5 + (m + 1) * span k
    let lw := base + span d + 2 * (d + 1)
    obtain ⟨s₁, hstep, hs₁_state, hs₁_cnt, hs₁_away⟩ :=
      dfsBody_next_cluster_spec hs hk hcnt ha hcnt_fit
    have hp_m_end : p_m + span k ≤ ptr + span (k + 1) := by
      have : p_m = ptr + clusterOffset k m := by dsimp only [p_m, clusterOffset]; omega
      have hce := cluster_end_le_span k hm_lt
      omega
    obtain ⟨s₂, hs₂_state, hs₂_rep, hs₂_frame, hs₂_cps⟩ :=
      ih hs₁_state (hp_m_end.trans hptr_end)
    have hs₂_p_eq : p_m + span k = ptr + 5 + (m + 1 + 1) * span k := by
      dsimp only [p_m]; ring
    have hs₂_cnt : s₂.mem (lw + (k + 1)) = cnt := by
      rw [hs₂_frame (lw + (k + 1))
        (Or.inr (by have := hp_m_end.trans hptr_end; dsimp only [lw]; omega))
        (Or.inr (by dsimp only [lw]; omega))]
      exact hs₁_cnt
    have hs₂_prev : ∀ i : Fin (universeSize k), i.val < m + 1 →
        Rep (Tree.empty k) (ptr + clusterOffset k i.val) s₂.mem := by
      intro i hi
      by_cases him : i.val < m
      · apply rep_frame (hprev i him)
        intro a ha_lo ha_hi
        have hce := cluster_end_le_clusterOffset k him
        have hce_span := cluster_end_le_span k i.isLt
        have hp_m_eq : p_m = ptr + clusterOffset k m := by dsimp only [p_m, clusterOffset]; omega
        rw [hs₂_frame a (Or.inl (by omega)) (Or.inl (by omega))]
        exact hs₁_away a (by omega)
      · have hi_eq : i.val = m := by omega
        have hp_eq : ptr + clusterOffset k i.val = p_m := by
          dsimp only [p_m, clusterOffset]; rw [hi_eq]; omega
        simpa only [hp_eq] using hs₂_rep
    obtain ⟨s', hs'_state, hs'_cnt, hs'_all, hs'_frame, hs'_cps⟩ :=
      ih_cnt (m := m + 1) (s := s₂) (by omega)
        (hs₂_p_eq ▸ hs₂_state) hs₂_cnt hs₂_prev
    refine ⟨s', hs'_state, hs'_cnt, hs'_all, ?_, ?_⟩
    · intro a ha_tree ha_cnt
      have ha_tree₂ : a < ptr + 5 + (m + 1 + 1) * span k ∨ ptr + span (k + 1) ≤ a := by
        rcases ha_tree with hlt | hge
        · exact Or.inl (by omega)
        · exact Or.inr hge
      rw [hs'_frame a ha_tree₂ ha_cnt]
      have ha_tree₁ : a < p_m ∨ p_m + span k ≤ a := by
        rcases ha_tree with hlt | hge
        · exact Or.inl hlt
        · exact Or.inr (hp_m_end.trans hge)
      have ha_cnt₁ : a < lw + 1 ∨ lw + k < a := by omega
      rw [hs₂_frame a ha_tree₁ ha_cnt₁]
      exact hs₁_away a (by omega)
    · intro z T_cont hcont
      have h1 := hs'_cps z T_cont hcont
      have h2 := hs₂_cps z (cnt * (8 * span k) + T_cont) h1
      have h3 := ExecWithin.loop_iter (dfsState_cond_holds hs) hstep h2
      have h5_le := five_le_span k
      have hmul : (cnt + 1) * (8 * span k) = cnt * (8 * span k) + 8 * span k :=
        Nat.succ_mul cnt (8 * span k)
      exact h3.mono (by omega)

/-- Subtree initialization theorem: from `DfsState base d ptr k 0 s` with `k ≤ d` and
`ptr + span k ≤ base + span d`, the DFS loop initializes `Rep (Tree.empty k) ptr s'.mem`
and reaches `DfsState base d (ptr + span k) k 1 s'` in at most `8 * span k - 15` instructions,
modifying only `[ptr, ptr + span k)` and counters `[low + 1, low + k]`. -/
private theorem dfs_subtree_spec {w base d : ℕ} (k : ℕ) (hk : k ≤ d)
    (ha : Fits w (base + span d + 4 * (d + 1))) :
    ∀ {ptr : ℕ} {s : Data 32},
      DfsState base d ptr k 0 s → ptr + span k ≤ base + span d →
      ∃ s', DfsState base d (ptr + span k) k 1 s' ∧
        Rep (Tree.empty k) ptr s'.mem ∧
        (∀ a, (a < ptr ∨ ptr + span k ≤ a) →
          (a < base + span d + 2 * (d + 1) + 1 ∨
            base + span d + 2 * (d + 1) + k < a) →
          s'.mem a = s.mem a) ∧
        (∀ z T_cont, ExecWithin w dfsLoop s' z T_cont →
          ExecWithin w dfsLoop s z (8 * span k - 15 + T_cont)) := by
  induction k with
  | zero =>
    intro ptr s hs hptr_end
    obtain ⟨s', hstep, hs'_state, hs'_rep, hs'_away⟩ := dfsBody_leaf_spec hs ha hptr_end
    refine ⟨s', hs'_state, hs'_rep, fun a ha_tree _ => hs'_away a ha_tree, ?_⟩
    intro z T_cont hcont
    exact (ExecWithin.loop_iter (dfsState_cond_holds hs) hstep hcont).mono
      (by dsimp only [span]; omega)
  | succ k ih =>
    intro ptr s hs hptr_end
    have ih' {p₀ : ℕ} {s₀ : Data 32} := ih (by omega) (ptr := p₀) (s := s₀)
    let lw := base + span d + 2 * (d + 1)
    obtain ⟨s₀, hstep_enter, hs₀_state, hs₀_hdr, hs₀_cnt, hs₀_away⟩ :=
      dfsBody_enter_succ_spec hs hk ha hptr_end
    have hsum_end : (ptr + 5) + span k ≤ base + span d := by
      have := summary_end_le_span k
      dsimp only [summaryOffset] at this
      omega
    obtain ⟨s₁, hs₁_state, hs₁_sum_rep, hs₁_frame, hs₁_cps⟩ := ih' hs₀_state hsum_end
    have hs₁_p_eq : ptr + 5 + span k = ptr + 5 + (0 + 1) * span k := by ring
    have hs₁_cnt : s₁.mem (lw + (k + 1)) = universeSize k := by
      rw [hs₁_frame (lw + (k + 1)) (Or.inr (by dsimp only [lw]; omega))
        (Or.inr (by dsimp only [lw]; omega))]
      exact hs₀_cnt
    obtain ⟨s₂, hs₂_state, hs₂_cnt, hs₂_clusters, hs₂_frame, hs₂_cps⟩ :=
      dfs_clusters_spec hk ha hptr_end ih' (universeSize k) (m := 0) (s := s₁)
        (by omega) (hs₁_p_eq ▸ hs₁_state) hs₁_cnt (fun i hi => by omega)
    obtain ⟨s', hstep_exit, hs'_state, hs'_mem⟩ :=
      dfsBody_exit_node_spec hs₂_state hk hs₂_cnt ha
    have hs'_hdr : Header (k + 1) none ptr s'.mem := by
      have h5_le := five_le_span (k + 1)
      apply (header_congr ?_).mp hs₀_hdr
      intro a ha_lt5
      rw [hs'_mem,
        hs₂_frame (ptr + a) (Or.inl (by omega)) (Or.inl (by omega)),
        hs₁_frame (ptr + a) (Or.inl (by omega)) (Or.inl (by omega))]
    have hs'_sum : Rep (Tree.empty k) (ptr + summaryOffset) s'.mem := by
      have hsum_le := summary_end_le_span k
      have hso : summaryOffset = 5 := rfl
      apply rep_frame hs₁_sum_rep
      intro a ha_lo ha_hi
      rw [hs'_mem]
      exact hs₂_frame a (Or.inl (by omega)) (Or.inl (by omega))
    refine ⟨s', hs'_state, ⟨hs'_hdr, hs'_sum, hs'_mem.symm ▸ hs₂_clusters⟩, ?_, ?_⟩
    · intro a ha_tree ha_cnt
      have h5_le := five_le_span k
      have hsum_le := summary_end_le_span k
      dsimp only [summaryOffset] at hsum_le
      rw [hs'_mem,
        hs₂_frame a (by omega) ha_cnt,
        hs₁_frame a (by omega) (by omega),
        hs₀_away a (by omega) (by omega)]
    · intro z T_cont hcont
      have h_exit := ExecWithin.loop_iter (dfsState_cond_holds hs₂_state) hstep_exit hcont
      have h_clus := hs₂_cps z (9 + T_cont + 2) h_exit
      have h_sum := hs₁_cps z (universeSize k * (8 * span k) + (9 + T_cont + 2)) h_clus
      have h_enter := ExecWithin.loop_iter (dfsState_cond_holds hs) hstep_enter h_sum
      have h5_le := five_le_span k
      apply h_enter.mono
      rw [span_succ]
      have h_alg : universeSize k * (8 * span k) + 8 * span k =
        8 * ((universeSize k + 1) * span k) := by ring
      omega

/-- Complete Phase 3 DFS loop specification: from `DfsState base d base d 0 s`, `dfsLoop`
terminates in at most `8 * span d - 6` instructions, establishing `Rep (Tree.empty d) base z.mem`,
preserving `root`, `payload`, and `stackBase`, and modifying only `[base, base + span d)` and
`[base + span d + 2 * (d + 1) + 1, base + span d + 3 * d + 2]`. -/
private theorem dfsLoop_spec {w base d : ℕ} {s : Data 32}
    (hs : DfsState base d base d 0 s) (ha : Fits w (base + span d + 4 * (d + 1))) :
    ∃ z, ExecWithin w dfsLoop s z (8 * span d - 6) ∧
      Rep (Tree.empty d) base z.mem ∧
      z.regs root = base ∧
      z.regs payload = base + span d ∧
      z.regs stackBase = base + span d ∧
      (∀ a, (a < base ∨ base + span d ≤ a) →
        (a < base + span d + 2 * (d + 1) + 1 ∨
          base + span d + 2 * (d + 1) + d < a) →
        z.mem a = s.mem a) := by
  obtain ⟨s', hs'_state, hs'_rep, hs'_frame, hs'_cps⟩ :=
    dfs_subtree_spec d le_rfl ha hs le_rfl
  obtain ⟨z, hfinish, hz0, hz_run, hzr, hzp, hzstk, hzm⟩ := dfsBody_finish_spec hs'_state ha
  have hc_exit : ¬(Cond.lt zero runFlag).Holds z := by
    simp [Cond.holds_lt, hz0, hz_run]
  have hcont := ExecWithin.loop_iter (dfsState_cond_holds hs'_state) hfinish
    (ExecWithin.loop_exit hc_exit)
  have h5_le := five_le_span d
  have hrun : ExecWithin w dfsLoop s z (8 * span d - 6) :=
    (hs'_cps z (5 + 2 + 2) hcont).mono (by omega)
  exact ⟨z, hrun, hzm ▸ hs'_rep, hzr, hzp, hzstk,
    fun a ha_tree ha_cnt => (congrFun hzm a).trans (hs'_frame a ha_tree ha_cnt)⟩

/-! ## Complete initializer specifications -/

/-- Complete structured execution of `initProgram` (excluding only the final flat `halt`):
from any state with `s.regs root = base` and `s.regs depth = d`, `initProgram` executes in at
most `8 * span d + 20 * d + 24` instructions, establishes `Rep (Tree.empty d) base z.mem`,
preserves `z.regs root = base`, sets `z.regs stackBase = base + span d` and
`z.regs out = base + span d`, and modifies no memory outside `[base, base + span d + 4 * (d + 1))`.
-/
theorem init_dispatch_spec {w base d : ℕ} {s : Data 32}
    (ha : Fits w (base + span d + 4 * (d + 1)))
    (hroot : s.regs root = base) (hdepth : s.regs depth = d) :
    ∃ z, ExecWithin w initProgram s z (8 * span d + 20 * d + 24) ∧
      Rep (Tree.empty d) base z.mem ∧
      z.regs root = base ∧
      z.regs stackBase = base + span d ∧
      z.regs out = base + span d ∧
      (∀ a, a < base ∨ base + span d + 4 * (d + 1) ≤ a → z.mem a = s.mem a) := by
  have h5_le := five_le_span d
  have hw5 : Fits w 5 := ha.of_le (by omega)
  have hspan : Fits w (span d) := ha.of_le (by omega)
  have hd : Fits w d := ha.of_le (by omega)
  apply WP.exists_execWithin
  unfold initProgram initSetup
  wram_exec
  apply WP.name; intro s₁ hs₁
  have hs₁_root : s₁.regs root = base := by subst hs₁; wram_simp [hroot]
  have hs₁_mem : s₁.mem = s.mem := by subst hs₁; rfl
  obtain ⟨s₂, h2, hs₂0, hs₂1, hs₂2, hs₂3, hs₂4, hs₂5, hs₂r, hs₂d, _, hs₂t, hs₂m⟩ :=
    sizeLoop_spec d (k := 0) (s := s₁) (by omega) hspan hd
      (by subst hs₁; wram_simp) (by subst hs₁; wram_simp) (by subst hs₁; wram_simp)
      (by subst hs₁; wram_simp) (by subst hs₁; wram_simp) (by subst hs₁; wram_simp)
      (by subst hs₁; wram_simp [hdepth]) (by subst hs₁; wram_simp [universeSize])
      (by subst hs₁; wram_simp [span]) (by subst hs₁; wram_simp)
  clear hs₁
  have hs₂_root : s₂.regs root = base := hs₂r.trans hs₁_root
  have hs₂_mem : s₂.mem = s.mem := hs₂m.trans hs₁_mem
  refine WP.of_execWithin h2 ?_
  unfold tableSetup
  wram_exec [hs₂0, hs₂1, hs₂2, hs₂5, hs₂_root, hs₂t]
  apply WP.name; intro s₃ hs₃
  have hs₃_inv : TableInv (base + span d) 0 s₃.mem := by
    intro j hj
    obtain rfl : j = 0 := by omega
    subst hs₃
    exact ⟨by wram_simp [splitSize], by wram_simp [childSpan]⟩
  have hs₃_away : ∀ a, a < base + span d ∨ base + span d + 2 ≤ a → s₃.mem a = s.mem a := by
    intro a ha_out
    have hne0 : a ≠ base + span d := by omega
    have hne1 : a ≠ base + span d + 1 := by omega
    subst hs₃
    wram_simp [hs₂_mem]
  obtain ⟨s₄, h4, hs₄0, hs₄1, hs₄2, hs₄3, hs₄4, hs₄5, hs₄r, hs₄d, hs₄p, hs₄tbl, hs₄stk,
      hs₄sp, hs₄inv, hs₄frame⟩ :=
    tableLoop_spec d (k := 0) (s := s₃) (by omega) ha
      (by subst hs₃; wram_simp [hs₂0]) (by subst hs₃; wram_simp [hs₂1])
      (by subst hs₃; wram_simp [hs₂2]) (by subst hs₃; wram_simp [hs₂3])
      (by subst hs₃; wram_simp [hs₂4]) (by subst hs₃; wram_simp [hs₂5])
      (by subst hs₃; wram_simp [hs₂_root]) (by subst hs₃; wram_simp [hs₂d])
      (by subst hs₃; wram_simp) (by subst hs₃; wram_simp) (by subst hs₃; wram_simp)
      (by subst hs₃; wram_simp)
      (by subst hs₃; wram_simp [universeSize]) (by subst hs₃; wram_simp [span])
      (by subst hs₃; wram_simp) hs₃_inv
  clear hs₃ hs₂0 hs₂1 hs₂2 hs₂3 hs₂4 hs₂5 hs₂r hs₂d hs₂t hs₂m hs₂_root hs₁_root
  refine WP.of_execWithin h4 ?_
  unfold dfsSetup
  wram_exec [hs₄0, hs₄1, hs₄r, hs₄d, hs₄sp]
  apply WP.name; intro s₅ hs₅
  have hs₅_mem : s₅.mem = s₄.mem := by subst hs₅; rfl
  have hs₅_state : DfsState base d base d 0 s₅ := by
    subst hs₅
    exact ⟨⟨by wram_simp [hs₄0], by wram_simp [hs₄1], by wram_simp [hs₄2],
      by wram_simp [hs₄3], by wram_simp [hs₄4], by wram_simp [hs₄5],
      by wram_simp [hs₄r], by wram_simp [hs₄d], by wram_simp [hs₄p],
      by wram_simp [hs₄tbl], by wram_simp [hs₄stk], by wram_simp, hs₄inv⟩,
      by wram_simp, by wram_simp, by wram_simp, by wram_simp⟩
  clear hs₅ hs₄0 hs₄1 hs₄2 hs₄3 hs₄4 hs₄5 hs₄r hs₄d hs₄p hs₄tbl hs₄stk hs₄sp hs₄inv
  obtain ⟨s₆, h6, hs₆_rep, hs₆r, hs₆p, hs₆stk, hs₆frame⟩ := dfsLoop_spec hs₅_state ha
  refine WP.of_execWithin h6 ?_
  wram_exec [hs₆p]
  refine ⟨by simpa only [Data.set_mem] using hs₆_rep, by wram_simp [hs₆r],
    by wram_simp [hs₆stk], by wram_simp, ?_⟩
  intro a ha_out
  dsimp only [Data.set_mem]
  rw [hs₆frame a (by omega) (by omega), hs₅_mem, hs₄frame a (by omega)]
  exact hs₃_away a (by omega)

/-- Bounded-caller initialization certificate: from any bounded state with `s.regs root = base`
and `s.regs depth = d`, `initProgram` executes in at most `8 * span d + 20 * d + 25` instructions
(including the final halt), preserves boundedness, establishes `Rep (Tree.empty d) base z.mem`,
and sets `z.regs root = base` and `z.regs stackBase = base + span d`. -/
theorem init_call {w base d : ℕ} {s : Data 32}
    (hs : s.Bounded w) (ha : Fits w (base + span d + 4 * (d + 1)))
    (hroot : s.regs root = base) (hdepth : s.regs depth = d) :
    ∃ z n, n + 1 ≤ 8 * span d + 20 * d + 25 ∧ Exec w initProgram s z n ∧
      z.Bounded w ∧ Rep (Tree.empty d) base z.mem ∧
      z.regs root = base ∧ z.regs stackBase = base + span d ∧
      z.regs out = base + span d ∧
      (∀ a, a < base ∨ base + span d + 4 * (d + 1) ≤ a → z.mem a = s.mem a) := by
  obtain ⟨z, ⟨n, hn, he⟩, hrep, hr, hstk, hout, hframe⟩ :=
    init_dispatch_spec ha hroot hdepth
  exact ⟨z, n, by omega, he, he.bounded hs, hrep, hr, hstk, hout, hframe⟩

/-- Flat bounded-word execution of `initProgram.program out`, including the final halt, in at
most `8 * span d + 20 * d + 25` instructions. -/
theorem init_executes {w base d : ℕ} {s : Data 32}
    (hs : s.Bounded w) (ha : Fits w (base + span d + 4 * (d + 1)))
    (hroot : s.regs root = base) (hdepth : s.regs depth = d) :
    ∃ n ≤ 8 * span d + 20 * d + 25,
      Executes w (initProgram.program out) ⟨0, s⟩ (base + span d) n := by
  obtain ⟨z, n, hn, he, _, _, _, _, hout, _⟩ := init_call hs ha hroot hdepth
  exact ⟨n + 1, hn, hout ▸ he.executes out⟩

/-- Exact transfer of the flat initializer execution into the shared generic RAM model. -/
theorem init_executes_generic {w base d : ℕ} {s : Data 32}
    (hs : s.Bounded w) (ha : Fits w (base + span d + 4 * (d + 1)))
    (hroot : s.regs root = base) (hdepth : s.regs depth = d) :
    ∃ n ≤ 8 * span d + 20 * d + 25,
      GenericRAM.Executes w (initProgram.program out).toGeneric
        ((⟨0, s⟩ : State 32).toGeneric .standard) (base + span d) n := by
  obtain ⟨n, hn, he⟩ := init_executes hs ha hroot hdepth
  exact ⟨n, hn, executes_toGeneric_iff.mpr he⟩

/-- The flat initializer instruction bound written directly in terms of `universeSize d`. -/
theorem init_executes_universe {w base d : ℕ} {s : Data 32}
    (hs : s.Bounded w) (ha : Fits w (base + span d + 4 * (d + 1)))
    (hroot : s.regs root = base) (hdepth : s.regs depth = d) :
    ∃ n ≤ 80 * universeSize d + 20 * d,
      Executes w (initProgram.program out) ⟨0, s⟩ (base + span d) n := by
  obtain ⟨n, hn, he⟩ := init_executes hs ha hroot hdepth
  have hsp := span_add_fifteen_le d
  exact ⟨n, by omega, he⟩

/-- The combined tree and scratch region of `span d + 4 * (d + 1)` words is bounded by
`10 * universeSize d + 4 * (d + 1)`. -/
theorem init_space_le (d : ℕ) :
    span d + 4 * (d + 1) ≤ 10 * universeSize d + 4 * (d + 1) :=
  Nat.add_le_add_right (span_le d) (4 * (d + 1))

end Cslib.DataStructure.VanEmdeBoas.WordRAM
