/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.CausalBroadcast.Causal
import CslibFrontier.Computability.Distributed.CausalBroadcast.TotalOrder

/-! Asynchronous causal broadcast versus total-order (atomic) broadcast (checked as a `module`
client with ordinary imports):
1. `decide`-checked `Fin 3` out-of-order causal-triangle trace (`0 → 1 → 2` overtaking `0 → 2`,
   held back in `2`'s delay buffer until `0 → 2` arrives and is delivered, unlocking `1 → 2` and
   establishing `(proc 2).delivered = [m₀, m₁]`), plus instantiations of `bssLTS_mTr_iff`,
   `sup_ts_eq_update_of_deliverable`, `bss_integrity`, `bss_no_duplicates`,
   `bss_causalPrec_iff_ts_lt`, and `bss_causal_delivery`;
2. `decide`-checked `Fin 3` concurrent broadcast trace (`0` broadcasts `c₀` and `1` broadcasts `c₁`
   concurrently) delivering `[c₀, c₁]` at `0` and `[c₁, c₀]` at `1`, witnessing
   `CausalBroadcast ⊊ TotalOrderBroadcast`;
3. `decide`-checked multi-slot `canonicalBatch` / `runConsensusSlots` execution over overlapping,
   duplicate-containing batches in opposite orders, plus a concrete non-vacuous
   `ConsensusSlotExec (Fin 3) ℕ {2}` with a crashing proposer verified via
   `totalOrderBroadcast_of_consensusSlotExec`;
4. `decide`-checked out-of-order `zeroFaultTotalOrderAlg` sequencer reorder-buffer trace, `t = 0`
   solvability, `Cslib.FLP` `t ≥ 1` impossibility on `Fin 2` and `Fin 3`, and the
   `causal_vs_oneShotTotalOrder_dichotomy` step. -/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.CausalBroadcast

open Cslib Cslib.Distributed.CausalBroadcast

/-! ### 1. `Fin 3` Out-of-Order Causal Triangle Trace (`0 → 1 → 2` Racing Ahead of `0 → 2`) -/

/-- Packet `m₀` broadcast initially by `0` on `Fin 3` with vector clock `(1, 0, 0)`. -/
def triPkt0 : Packet (Fin 3) ℕ :=
  bssBroadcastPacket (bssInit (Fin 3) ℕ) 0 10

/-- Intermediate state after `0` broadcasts `10` and `1` receives and delivers `m₀`. -/
def triAfter1Deliv0 : BSSState (Fin 3) ℕ :=
  bssRun (bssInit (Fin 3) ℕ)
    [.broadcast 0 10, .recv ⟨1, triPkt0⟩, .deliver 1 triPkt0]

/-- Packet `m₁` broadcast by `1` after delivering `m₀`, carrying vector clock `(1, 1, 0)`. -/
def triPkt1 : Packet (Fin 3) ℕ :=
  bssBroadcastPacket triAfter1Deliv0 1 20

/-- Prefix where `0 → 1 → 2` (`triPkt1`) races ahead of `0 → 2` (`triPkt0`) and arrives at `2`
first. -/
def triEarlyPrefix : List (BSSAction (Fin 3) ℕ) :=
  [.broadcast 0 10,
   .recv ⟨1, triPkt0⟩,
   .deliver 1 triPkt0,
   .broadcast 1 20,
   .recv ⟨2, triPkt1⟩]

/-- Full `Fin 3` triangle trace under fault set `{2}`: `0 → 2` subsequently arrives and is
delivered at `2`, unlocking buffered `triPkt1`, followed by `2` crashing. -/
def triFullTrace : List (BSSAction (Fin 3) ℕ) :=
  triEarlyPrefix ++
    [.recv ⟨2, triPkt0⟩,
     .deliver 2 triPkt0,
     .deliver 2 triPkt1,
     .crash 2]

/-- Vector timestamps of `triPkt0` and `triPkt1` reflect causal dependence `triPkt0.ts < triPkt1.ts`
with weights `1` and `2`. -/
example :
    triPkt0.ts 0 = 1 ∧ triPkt0.ts 1 = 0 ∧ triPkt0.ts 2 = 0 ∧
    triPkt1.ts 0 = 1 ∧ triPkt1.ts 1 = 1 ∧ triPkt1.ts 2 = 0 ∧
    vtWeight triPkt0.ts = 1 ∧ vtWeight triPkt1.ts = 2 := by
  decide

/-- When `triPkt1` arrives early at `2` before `triPkt0`, `triPkt1` sits in `(proc 2).pending` with
`¬ Deliverable` (blocked on `triPkt1.ts 0 = 1 > (proc 2).vt 0 = 0`) and `delivered = []`. -/
theorem tri_early_arrival_buffered_not_deliverable :
    let sMid := bssRun (bssInit (Fin 3) ℕ) triEarlyPrefix
    bssValidTrace ({2} : Set (Fin 3)) (bssInit (Fin 3) ℕ) triEarlyPrefix ∧
    triPkt1 ∈ (sMid.proc 2).pending ∧
    ¬ Deliverable (sMid.proc 2).vt triPkt1 ∧
    (sMid.proc 2).delivered = [] := by
  decide

/-- Once `triPkt0` arrives at `2` and is delivered, `triPkt1` becomes `Deliverable` and `2`
delivers `[triPkt0, triPkt1]` in causal order despite out-of-order network arrival. -/
theorem tri_full_trace_valid_and_ordered :
    let sEnd := bssRun (bssInit (Fin 3) ℕ) triFullTrace
    bssValidTrace ({2} : Set (Fin 3)) (bssInit (Fin 3) ℕ) triFullTrace ∧
    (sEnd.proc 0).delivered = [triPkt0] ∧
    (sEnd.proc 1).delivered = [triPkt0, triPkt1] ∧
    (sEnd.proc 2).delivered = [triPkt0, triPkt1] ∧
    (sEnd.proc 2).pending = 0 ∧
    (sEnd.proc 2).halted = true := by
  decide

/-- Check `sup_ts_eq_update_of_deliverable` on `triPkt0` at process `1`. -/
example :
    let sRecv := bssRun (bssInit (Fin 3) ℕ) [.broadcast 0 10, .recv ⟨1, triPkt0⟩]
    (sRecv.proc 1).vt ⊔ triPkt0.ts =
      Function.update (sRecv.proc 1).vt triPkt0.sender ((sRecv.proc 1).vt triPkt0.sender + 1) :=
  sup_ts_eq_update_of_deliverable (by decide)

/-- Instantiate `bssLTS_mTr_iff`, `bss_integrity`, `bss_no_duplicates`, `bss_causalPrec_iff_ts_lt`,
and `bss_causal_delivery` on the `Fin 3` triangle execution (including crashed receiver `2 ∈ F`). -/
theorem tri_theorems_instantiated :
    let F : Set (Fin 3) := {2}
    let sEnd := bssRun (bssInit (Fin 3) ℕ) triFullTrace
    (bssLTS F).MTr (bssInit (Fin 3) ℕ) triFullTrace sEnd ∧
    (∀ q, (sEnd.proc q).delivered.Nodup) ∧
    triPkt0 ∈ BroadcastIn triFullTrace ∧
    triPkt1 ∈ BroadcastIn triFullTrace ∧
    CausalPrec triFullTrace triPkt0 triPkt1 ∧
    (triPkt0 ∈ (sEnd.proc 2).delivered ∧
      (sEnd.proc 2).delivered.idxOf triPkt0 < (sEnd.proc 2).delivered.idxOf triPkt1) := by
  intro F sEnd
  have hmtr : (bssLTS F).MTr (bssInit (Fin 3) ℕ) triFullTrace sEnd :=
    (bssLTS_mTr_iff F (bssInit (Fin 3) ℕ) triFullTrace sEnd).mpr
      ⟨tri_full_trace_valid_and_ordered.1, rfl⟩
  have hb0 : triPkt0 ∈ BroadcastIn triFullTrace := ⟨0, by decide, by decide⟩
  have hb1 : triPkt1 ∈ BroadcastIn triFullTrace := ⟨3, by decide, by decide⟩
  have hts_lt : triPkt0.ts < triPkt1.ts := by
    rw [Pi.lt_def]
    exact ⟨by decide, ⟨1, by decide⟩⟩
  have hprec : CausalPrec triFullTrace triPkt0 triPkt1 :=
    (bss_causalPrec_iff_ts_lt hmtr hb0 hb1).mpr hts_lt
  have hdel1_at_2 : triPkt1 ∈ (sEnd.proc 2).delivered := by decide
  have _ : triPkt1 ∈ BroadcastIn triFullTrace := bss_integrity hmtr 2 hdel1_at_2
  exact ⟨hmtr, bss_no_duplicates hmtr, hb0, hb1, hprec,
    bss_causal_delivery hmtr hb0 hb1 hprec 2 hdel1_at_2⟩

/-! ### 2. Concurrent Broadcasts Separating Causal Broadcast from Total-Order Broadcast -/

/-- Concurrent broadcasts on `Fin 3`: `0` broadcasts `100` (`concPkt0`) and `1` concurrently
broadcasts `200` (`concPkt1`), after which each receives and delivers the other's packet. -/
def concPkt0 : Packet (Fin 3) ℕ :=
  bssBroadcastPacket (bssInit (Fin 3) ℕ) 0 100

/-- Concurrent broadcast packet from `1` with vector clock `(0, 1, 0)`. -/
def concPkt1 : Packet (Fin 3) ℕ :=
  bssBroadcastPacket (bssStep (bssInit (Fin 3) ℕ) (.broadcast 0 100)) 1 200

/-- Valid `bssLTS` trace in which `0` delivers `[concPkt0, concPkt1]` while `1` delivers
`[concPkt1, concPkt0]`. -/
def concTrace : List (BSSAction (Fin 3) ℕ) :=
  [.broadcast 0 100,
   .broadcast 1 200,
   .recv ⟨0, concPkt1⟩,
   .deliver 0 concPkt1,
   .recv ⟨1, concPkt0⟩,
   .deliver 1 concPkt0]

/-- `CausalBroadcast ⊊ TotalOrderBroadcast`: `concTrace` is a valid fault-free execution of
`bssLTS ∅` in which `concPkt0` and `concPkt1` are causally incomparable (`¬ CausalPrec` in either
direction) and processes `0` and `1` deliver them in strictly opposite orders! -/
theorem causal_strictly_weaker_than_totalOrder :
    let sConc := bssRun (bssInit (Fin 3) ℕ) concTrace
    (bssLTS (∅ : Set (Fin 3))).MTr (bssInit (Fin 3) ℕ) concTrace sConc ∧
    ¬ CausalPrec concTrace concPkt0 concPkt1 ∧
    ¬ CausalPrec concTrace concPkt1 concPkt0 ∧
    (sConc.proc 0).delivered = [concPkt0, concPkt1] ∧
    (sConc.proc 1).delivered = [concPkt1, concPkt0] ∧
    ((sConc.proc 0).delivered.idxOf concPkt0 < (sConc.proc 0).delivered.idxOf concPkt1 ∧
      (sConc.proc 1).delivered.idxOf concPkt1 < (sConc.proc 1).delivered.idxOf concPkt0) := by
  intro sConc
  have hmtr : (bssLTS (∅ : Set (Fin 3))).MTr (bssInit (Fin 3) ℕ) concTrace sConc :=
    (bssLTS_mTr_iff (∅ : Set (Fin 3)) (bssInit (Fin 3) ℕ) concTrace sConc).mpr ⟨by decide, rfl⟩
  have hb0 : concPkt0 ∈ BroadcastIn concTrace := ⟨0, by decide, by decide⟩
  have hb1 : concPkt1 ∈ BroadcastIn concTrace := ⟨1, by decide, by decide⟩
  have hnc01 : ¬ CausalPrec concTrace concPkt0 concPkt1 := by
    rw [bss_causalPrec_iff_ts_lt hmtr hb0 hb1, Pi.lt_def]
    intro ⟨hle, _⟩
    exact absurd (hle 0) (by decide)
  have hnc10 : ¬ CausalPrec concTrace concPkt1 concPkt0 := by
    rw [bss_causalPrec_iff_ts_lt hmtr hb1 hb0, Pi.lt_def]
    intro ⟨hle, _⟩
    exact absurd (hle 1) (by decide)
  exact ⟨hmtr, hnc01, hnc10, by decide, by decide, by decide⟩

/-! ### 3. Reduction 2: `canonicalBatch`, `runConsensusSlots`, and Concrete `ConsensusSlotExec` -/

/-- Processes deciding extensionally equal Consensus batches with duplicates and reversed list
orders produce the identical canonical Total-Order delivery sequence `[10, 30, 20, 40]`. -/
example :
    insertSorted 20 [10, 30] = [10, 20, 30] ∧
    canonicalBatch [10, 30] [40, 30, 20, 10, 20] = [20, 40] ∧
    runConsensusSlots [[30, 10, 30], [20, 10, 40]] = [10, 30, 20, 40] ∧
    runConsensusSlots [[10, 30], [40, 30, 20]] = [10, 30, 20, 40] := by
  decide

example :
    canonicalBatch [(1 : Fin 5)] [3, 1, 2, 3] = canonicalBatch [1] [2, 3] ∧
    (runConsensusSlots [[30, 10, 30], [20, 10, 40]]).Nodup :=
  ⟨canonicalBatch_ext (by decide), runConsensusSlots_nodup _⟩

/-- R-delivered message sets in the 2-slot `Fin 3` test execution. -/
def concreteRDeliv (p : Fin 3) (t : ℕ) : Finset ℕ :=
  if p = 2 then {10, 30}
  else if t = 0 then {10}
  else {10, 20, 30}

/-- Decided Consensus batches in the 2-slot `Fin 3` test execution. -/
def concreteDecided (p : Fin 3) (t : ℕ) : List (List ℕ) :=
  if t = 0 then []
  else if p = 2 then [[30, 10]]
  else if t = 1 then (if p = 0 then [[30, 10]] else [[10, 30]])
  else (if p = 0 then [[30, 10], [20]] else [[10, 30], [20]])

/-- Characterization of slot membership across all processes and times in `concreteDecided`. -/
theorem concreteDecided_slot_mem (r : Fin 3) (t k : ℕ)
    (hk : k < (concreteDecided r t).length) (m : ℕ) :
    (k = 0 ∧ (m ∈ (concreteDecided r t)[k] ↔ m = 10 ∨ m = 30)) ∨
    (k = 1 ∧ (m ∈ (concreteDecided r t)[k] ↔ m = 20)) := by
  rcases k with _ | _ | k
  · left
    refine ⟨rfl, ?_⟩
    revert hk
    dsimp only [concreteDecided]
    split_ifs <;> intro hk <;> first | (exfalso; simp at hk; done) | (simp; done) | (simp; tauto)
  · right
    refine ⟨rfl, ?_⟩
    revert hk
    dsimp only [concreteDecided]
    split_ifs <;> intro hk <;> first | (exfalso; simp at hk; done) | simp
  · exfalso
    revert hk
    dsimp only [concreteDecided]
    split_ifs <;> intro hk <;> simp at hk

/-- Concrete 2-slot `ConsensusSlotExec` on `Fin 3` with faulty process `2 ∈ ({2} : Set (Fin 3))`:
* Broadcast set `bcast = {10, 20, 30}`, `correctBcast = {10, 20}` (`30` broadcast by faulty `2`).
* Slot `0`: faulty `2` proposes `[30, 10]` at `t = 0` before crashing (`K_2 = 1`); correct `0` and
  `1` propose `[10]` at `t = 0`; Consensus decides `{10, 30}` (represented as `[30, 10]` at `0, 2`
  and `[10, 30]` at `1`), delivering `[10, 30]` at all three processes!
* Slot `1`: faulty `2` has halted; correct `0` and `1` R-deliver `20` at `t = 1`, propose `[20]`,
  and decide `[20]` at `t = 2`, extending `aDelivered` at `0` and `1` to `[10, 30, 20]`. -/
def concreteSlotExec : ConsensusSlotExec (Fin 3) ℕ ({2} : Set (Fin 3)) where
  bcast := {10, 20, 30}
  correctBcast := {10, 20}
  correctBcast_sub := by
    intro m hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm ⊢
    tauto
  rDelivered := concreteRDeliv
  decidedBatches := concreteDecided
  Proposed p k t batch :=
    (p = 2 ∧ k = 0 ∧ t = 0 ∧ batch = [30, 10]) ∨
    (p ≠ 2 ∧ k = 0 ∧ t = 0 ∧ batch = [10]) ∨
    (p ≠ 2 ∧ k = 1 ∧ t = 1 ∧ batch = [20])
  rDelivered_mono p {t₁ t₂} hle := by
    dsimp only [concreteRDeliv]
    split_ifs <;> first | omega | decide
  rb_integrity p t m hm := by
    dsimp only [concreteRDeliv] at hm
    split_ifs at hm <;>
      (simp only [Finset.mem_insert, Finset.mem_singleton] at hm;
       simp only [Set.mem_insert_iff, Set.mem_singleton_iff];
       tauto)
  rb_validity m hm q hq := by
    have hq2 : q ≠ 2 := by simpa using hq
    refine ⟨1, ?_⟩
    simp only [concreteRDeliv, hq2, ↓reduceIte, one_ne_zero]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rb_agreement p hp q hq m t hm := by
    have hp2 : p ≠ 2 := by simpa using hp
    have hq2 : q ≠ 2 := by simpa using hq
    refine ⟨1, ?_⟩
    dsimp only [concreteRDeliv] at hm ⊢
    split_ifs at hm ⊢ <;>
      (simp only [Finset.mem_insert, Finset.mem_singleton] at hm ⊢;
       first | contradiction | tauto)
  decidedBatches_prefix p {t₁ t₂} hle := by
    dsimp only [concreteDecided]
    split_ifs <;> first | omega | decide
  propose_spec p k t batch hprop := by
    rcases hprop with ⟨rfl, rfl, rfl, rfl⟩ | ⟨hp, rfl, rfl, rfl⟩ | ⟨hp, rfl, rfl, rfl⟩
    · refine ⟨rfl, by decide, fun m => ?_⟩
      dsimp only [concreteRDeliv, concreteDecided]
      simp only [↓reduceIte, runConsensusSlots, List.foldl_nil, Finset.mem_insert,
        Finset.mem_singleton, List.not_mem_nil, not_false_eq_true, and_true, List.mem_cons,
        or_false]
      omega
    · refine ⟨rfl, by decide, fun m => ?_⟩
      simp only [concreteRDeliv, concreteDecided, hp, ↓reduceIte, runConsensusSlots,
        List.foldl_nil, Finset.mem_singleton, List.not_mem_nil, not_false_eq_true, and_true,
        List.mem_singleton]
    · simp only [concreteRDeliv, concreteDecided, one_ne_zero, ↓reduceIte, hp]
      by_cases hp0 : p = 0 <;> simp only [hp0, ↓reduceIte]
      · have hrun : runConsensusSlots [[30, 10]] = [10, 30] := by decide
        rw [hrun]
        refine ⟨rfl, by decide, fun m => ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, List.mem_cons, List.not_mem_nil,
          or_false]
        omega
      · have hrun : runConsensusSlots [[10, 30]] = [10, 30] := by decide
        rw [hrun]
        refine ⟨rfl, by decide, fun m => ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton, List.mem_cons, List.not_mem_nil,
          or_false]
        omega
  decide_requires_propose p t k hk := by
    dsimp only [concreteDecided] at hk
    split_ifs at hk with ht0 hp2 ht1 hp0 hp0'
    · simp at hk
    · simp only [List.length_singleton] at hk
      have hk0 : k = 0 := by omega
      subst hk0
      exact ⟨0, Nat.zero_le _, [30, 10], Or.inl ⟨hp2, rfl, rfl, rfl⟩⟩
    · simp only [List.length_singleton] at hk
      have hk0 : k = 0 := by omega
      subst hk0
      exact ⟨0, Nat.zero_le _, [10], Or.inr (Or.inl ⟨hp2, rfl, rfl, rfl⟩)⟩
    · simp only [List.length_singleton] at hk
      have hk0 : k = 0 := by omega
      subst hk0
      exact ⟨0, Nat.zero_le _, [10], Or.inr (Or.inl ⟨hp2, rfl, rfl, rfl⟩)⟩
    · simp only [List.length_cons, List.length_nil] at hk
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · exact ⟨0, Nat.zero_le _, [10], Or.inr (Or.inl ⟨hp2, rfl, rfl, rfl⟩)⟩
      · exact ⟨1, by omega, [20], Or.inr (Or.inr ⟨hp2, rfl, rfl, rfl⟩)⟩
    · simp only [List.length_cons, List.length_nil] at hk
      rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
      · exact ⟨0, Nat.zero_le _, [10], Or.inr (Or.inl ⟨hp2, rfl, rfl, rfl⟩)⟩
      · exact ⟨1, by omega, [20], Or.inr (Or.inr ⟨hp2, rfl, rfl, rfl⟩)⟩
  task3_fair p hp t k hlen hne := by
    obtain ⟨m, hm_r, hm_na⟩ := hne
    have hp2 : p ≠ 2 := by simpa using hp
    simp only [concreteRDeliv, concreteDecided, hp2, ↓reduceIte] at hlen hm_r hm_na
    split_ifs at hlen hm_r hm_na
    · simp only [List.length_nil] at hlen
      subst hlen
      exact ⟨0, [10], Or.inr (Or.inl ⟨hp2, rfl, rfl, rfl⟩)⟩
    · simp only [List.length_singleton] at hlen
      subst hlen
      exact ⟨1, [20], Or.inr (Or.inr ⟨hp2, rfl, rfl, rfl⟩)⟩
    · simp only [List.length_singleton] at hlen
      subst hlen
      exact ⟨1, [20], Or.inr (Or.inr ⟨hp2, rfl, rfl, rfl⟩)⟩
    · exfalso
      have hrun : runConsensusSlots [[30, 10], [20]] = [10, 30, 20] := by decide
      rw [hrun] at hm_na
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm_r
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm_na
      omega
    · exfalso
      have hrun : runConsensusSlots [[10, 30], [20]] = [10, 30, 20] := by decide
      rw [hrun] at hm_na
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm_r
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm_na
      omega
  faulty_eventually_halted r hr := by
    simp only [Set.mem_singleton_iff] at hr
    subst hr
    refine ⟨1, fun k hk t batch hprop => ?_⟩
    rcases hprop with ⟨_, rfl, _, _⟩ | ⟨hne, _, _, _⟩ | ⟨hne, _, _, _⟩
    · omega
    · exact hne rfl
    · exact hne rfl
  cons_agreement p q t₁ t₂ k hk₁ hk₂ m := by
    rcases concreteDecided_slot_mem p t₁ k hk₁ m with ⟨hk0, hp_iff⟩ | ⟨hk1, hp_iff⟩ <;>
      rcases concreteDecided_slot_mem q t₂ k hk₂ m with ⟨hk0', hq_iff⟩ | ⟨hk1', hq_iff⟩
    · exact hp_iff.trans hq_iff.symm
    · omega
    · omega
    · exact hp_iff.trans hq_iff.symm
  cons_validity p t k hk := by
    rcases concreteDecided_slot_mem p t (k := k) hk 0 with ⟨hk0, _⟩ | ⟨hk1, _⟩
    · subst hk0
      refine ⟨2, 0, [30, 10], Or.inl ⟨rfl, rfl, rfl, rfl⟩, fun m => ?_⟩
      rcases concreteDecided_slot_mem p t 0 hk m with ⟨_, hiff⟩ | ⟨hk1, _⟩
      · rw [hiff]; simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
      · omega
    · subst hk1
      refine ⟨0, 1, [20], Or.inr (Or.inr ⟨by decide, rfl, rfl, rfl⟩), fun m => ?_⟩
      rcases concreteDecided_slot_mem p t 1 hk m with ⟨hk0, _⟩ | ⟨_, hiff⟩
      · omega
      · rw [hiff]; simp
  cons_termination k hall q hq := by
    have hq2 : q ≠ 2 := by simpa using hq
    rcases k with _ | _ | k
    · refine ⟨1, ?_⟩
      dsimp only [concreteDecided]
      split_ifs <;> first | contradiction | decide
    · refine ⟨2, ?_⟩
      dsimp only [concreteDecided]
      split_ifs <;> first | contradiction | omega | decide
    · obtain ⟨t₀, b₀, hp₀⟩ := hall 0 (by decide)
      rcases hp₀ with ⟨_, hk0, _⟩ | ⟨_, hk0, _⟩ | ⟨_, hk1, _⟩ <;> omega

/-- Verify both executable `aDelivered` logs and `totalOrderBroadcast_of_consensusSlotExec` on
`concreteSlotExec`. -/
example :
    concreteSlotExec.aDelivered 0 2 = [10, 30, 20] ∧
    concreteSlotExec.aDelivered 1 2 = [10, 30, 20] ∧
    concreteSlotExec.aDelivered 2 2 = [10, 30] ∧
    (∀ p t, (concreteSlotExec.aDelivered p t).Nodup) ∧
    (∀ m ∈ concreteSlotExec.correctBcast, ∀ p ∉ ({2} : Set (Fin 3)),
      ∃ t, m ∈ concreteSlotExec.aDelivered p t) := by
  have htot := totalOrderBroadcast_of_consensusSlotExec concreteSlotExec
  exact ⟨by decide, by decide, by decide, htot.1, htot.2.2.2.2⟩

/-! ### 4. Sequencer Reorder Trace (`t = 0`), `Cslib.FLP` Impossibility (`t ≥ 1`), & Dichotomy -/

/-- Out-of-order sequencer arrival at process `2` in `zeroFaultTotalOrderAlg 0`: slot `1` arrives
before slot `0` and is buffered (`delivered = []`); when slot `0` arrives, `drainConsecutive`
delivers `[⟨0, true⟩, ⟨1, false⟩]` in one step! -/
example :
    let π := zeroFaultTotalOrderAlg (P := Fin 3) (V := Bool) 0
    let m0 : BcastMsg (Fin 3) Bool := ⟨0, true⟩
    let m1 : BcastMsg (Fin 3) Bool := ⟨1, false⟩
    let eSlot1 : BcastEvent (Fin 3) (SeqMsg (Fin 3) Bool) Bool := ⟨2, Sum.inr (.ordered 1 m1)⟩
    let eSlot0 : BcastEvent (Fin 3) (SeqMsg (Fin 3) Bool) Bool := ⟨2, Sum.inr (.ordered 0 m0)⟩
    let st0 := π.init 2
    let st1 := π.next eSlot1 st0
    π.deliver eSlot1 st0 = [] ∧
    st1.nextDeliver = 0 ∧
    π.deliver eSlot0 st1 = [m0, m1] ∧
    (π.next eSlot0 st1).nextDeliver = 2 := by
  decide

/-- Positive `0`-fault Total-Order Broadcast solvability on `Fin 2` and `Fin 3`. -/
example : (zeroFaultTotalOrderAlg (P := Fin 2) (V := Bool) 0).SolvesTotalOrderBroadcast 0 :=
  zeroFaultTotalOrderAlg_solves 0

example : (zeroFaultTotalOrderAlg (P := Fin 3) (V := ℕ) 0).SolvesTotalOrderBroadcast 0 :=
  zeroFaultTotalOrderAlg_solves 0

/-- Direct `Cslib.FLP` bridge (`consensusOfTotalOrderBroadcast_consensus`) and
`uniformTotalOrder_of_solvesTotalOrderBroadcast` instantiated on `zeroFaultTotalOrderAlg`. -/
example :
    (consensusOfTotalOrderBroadcast
      (zeroFaultTotalOrderAlg (P := Fin 3) (V := Bool) 0)).Consensus 0 ∧
    (zeroFaultTotalOrderAlg (P := Fin 3) (V := ℕ) 0).UniformTotalOrder :=
  ⟨consensusOfTotalOrderBroadcast_consensus (zeroFaultTotalOrderAlg_solves 0),
   uniformTotalOrder_of_solvesTotalOrderBroadcast (zeroFaultTotalOrderAlg_solves 0)⟩

/-- 1-crash and 2-crash FLP impossibility of one-shot `TotalOrderBroadcastAlg` on `Fin 2` and
`Fin 3`. -/
example {M S : Type} [DecidableEq M] :
    ¬ ∃ π : TotalOrderBroadcastAlg (Fin 2) M S Bool, π.SolvesTotalOrderBroadcast 1 :=
  not_exists_oneShotTotalOrderBroadcast_ge_one (by decide) (le_refl 1)

example {M S : Type} [DecidableEq M] :
    ¬ ∃ π : TotalOrderBroadcastAlg (Fin 3) M S Bool, π.SolvesTotalOrderBroadcast 1 :=
  not_exists_oneShotTotalOrderBroadcast_ge_one (by decide) (le_refl 1)

example {M S : Type} [DecidableEq M] :
    ¬ ∃ π : TotalOrderBroadcastAlg (Fin 3) M S ℕ, π.SolvesTotalOrderBroadcast 2 :=
  not_exists_oneShotTotalOrderBroadcast_ge_one (by decide) (by decide)

/-- Exact `t = 0` solvability equivalence and fault-tolerance dichotomy step on `Fin 2` and
`Fin 3`. -/
example (t : ℕ) :
    (∃ (M S : Type) (_ : DecidableEq M) (π : TotalOrderBroadcastAlg (Fin 2) M S Bool),
      π.SolvesTotalOrderBroadcast t) ↔ t = 0 :=
  exists_oneShotTotalOrderBroadcast_iff_eq_zero (by decide) t

example :
    (∀ F : Set (Fin 3), F.ncard ≤ 2 →
      (∃ q : Fin 3, q ∉ F) ∧ BSSSolvesAtomicMulticastCausalBroadcast (Fin 3) Bool F) ∧
    ((∃ (M S : Type) (_ : DecidableEq M) (π : TotalOrderBroadcastAlg (Fin 3) M S Bool),
        π.SolvesTotalOrderBroadcast 2) ↔ 2 = 0) :=
  causal_vs_oneShotTotalOrder_dichotomy (P := Fin 3) (V := Bool) (by decide) (t := 2) (by decide)

end CslibFrontierTests.Distributed.CausalBroadcast
