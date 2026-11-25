/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.CRDT.Basic
import CslibFrontier.Computability.Distributed.CRDT.DataTypes
import CslibFrontier.Computability.Distributed.CRDT.Monotonicity
import Mathlib.Tactic.FinCases

/-! Conflict-free replicated data types (`CvRDT`, `CmRDT`, `OR-Set`) and semilattice
coordination-free monotonicity steps (checked as a `module` client with ordinary imports):
1. `decide`-checked `Fin 3` directed-ring `CvRDT.gossipLTS` trace with packet duplication, loss, and
   out-of-order merge on `GCounter`, instantiating `CvRDT.gossipLTS_mTr_iff`,
   `CvRDT.replica_eq_evalHistory`, `CvRDT.strong_convergence`, and
   `CvRDT.converge_of_allPairsReachable`;
2. `decide`-checked `Fin 3` `CausalBroadcast.bssLTS` trace running `PNCounter.cmrdt (Fin 3)` with
   opposite concurrent delivery orders and out-of-order causal holdback, instantiating
   `CmRDT.bss_strong_convergence`, together with `CvRDT.toCmRDT` and `CmRDT.toCvRDT` emulation and
   `deliverableEvents` out-of-order causal holdback tests;
3. Concrete `TwoPhaseSet` vs `ORSetCv` vs op-based `ORSetCausalHistory` (Shapiro et al. Figure 14
   concurrent add/remove diamond under both causal linearizations `[0, 1, 2]` and `[0, 2, 1]`),
   plus `not_exists_untagged_finset_merge` and non-vacuity checks on `(· ∪ ·)` and `(· ∩ ·)`;
4. Positive and negative `Monotonicity.lean` instantiations (`gcounterThresholdEmit`,
   `gcounterThresholdBool`, `gsetMemEmit`, `gsetFilterImage`, `emitted_eq_global_of_monotone`,
   1-node `Fin 1` `Subsingleton` necessity, and split-brain retraction runs for `gsetIsEmptyEmit`,
   `TwoPhaseSet.elements`, and `gcounterExactCountEmit`). -/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.CRDT

open Cslib Cslib.Distributed.CausalBroadcast Cslib.Distributed.CRDT

/-! ### 1. `Fin 3` Directed-Ring State-Based `CvRDT` Gossip Trace with Duplication, Drop, & Order -/

/-- Oriented 3-node ring `0 → 1 → 2 → 0` on `Fin 3`. -/
def ringGraph3 : Digraph (Fin 3) where
  Adj u v := v = u + 1

instance : DecidableRel ringGraph3.Adj := fun u v => inferInstanceAs (Decidable (v = u + 1))

theorem ringGraph3_allPairsReachable :
    ∀ p q : Fin 3, Relation.ReflTransGen ringGraph3.Adj p q := by
  intro p q
  fin_cases p <;> fin_cases q
  · exact .refl
  · exact .single rfl
  · exact .tail (.single rfl) rfl
  · exact .tail (.single rfl) rfl
  · exact .refl
  · exact .single rfl
  · exact .single rfl
  · exact .tail (.single rfl) rfl
  · exact .refl

/-- Concrete `GCounter (Fin 3)` gossip trace where:
* replica `0` increments (`uid = 10`), sends twice (`0 → 1`): one packet is dropped, the other is
  merged **twice** via `mergeDuplicate` + `mergeConsume`;
* replica `1` increments (`uid = 20`) and forwards `1 → 2`;
* replica `2` merges `{10, 20}` and forwards `2 → 0`, where `0` merges `{10, 20}` so `0`, `1`, and
  `2` share history `{10, 20}` despite opposite arrival orders, drops, and duplicates. -/
def gc3 : CvRDT (GCounter (Fin 3)) (Fin 3) ℕ := GCounter.cvrdt (Fin 3)

def pkt0To1 : GossipPacket (Fin 3) ℕ (GCounter (Fin 3)) :=
  ⟨1, (GCounter.zero (Fin 3)).inc 0, {10}⟩

def pkt1To2 : GossipPacket (Fin 3) ℕ (GCounter (Fin 3)) :=
  ⟨2, ((GCounter.zero (Fin 3)).inc 0).inc 1, {10, 20}⟩

def pkt2To0 : GossipPacket (Fin 3) ℕ (GCounter (Fin 3)) :=
  ⟨0, ((GCounter.zero (Fin 3)).inc 0).inc 1, {10, 20}⟩

def gossipRingTrace : List (GossipAction (Fin 3) ℕ (Fin 3) (GCounter (Fin 3))) :=
  [.update 0 10 0,
   .send 0 1,
   .send 0 1,
   .drop pkt0To1,
   .mergeDuplicate pkt0To1,
   .mergeConsume pkt0To1,
   .update 1 20 1,
   .send 1 2,
   .mergeConsume pkt1To2,
   .send 2 0,
   .mergeConsume pkt2To0]

theorem gossipRingTrace_valid_and_converged :
    let sEnd := gc3.gossipRun gc3.gossipInit gossipRingTrace
    gc3.gossipValidTrace ringGraph3 gc3.gossipInit gossipRingTrace ∧
    sEnd.history 0 = {10, 20} ∧
    sEnd.history 1 = {10, 20} ∧
    sEnd.history 2 = {10, 20} ∧
    (sEnd.replica 0).value = 2 ∧
    (sEnd.replica 1).value = 2 ∧
    (sEnd.replica 2).value = 2 ∧
    sEnd.inFlight = 0 := by
  simp only [gc3, gossipRingTrace, pkt0To1, pkt1To2, pkt2To0, ringGraph3,
    CvRDT.gossipRun, CvRDT.gossipValidTrace, CvRDT.gossipStep, CvRDT.gossipInit,
    CvRDT.GossipEnabled, GCounter.cvrdt, GCounter.inc, GCounter.zero, GCounter.value,
    List.foldl_cons, List.foldl_nil, Function.update_self, Function.update_of_ne, ne_eq,
    Fin.isValue, Fin.reduceEq, not_false_eq_true, Finset.empty_union, Finset.pair_comm 20 10,
    bot_sup_eq, sup_idem, Multiset.mem_cons, Multiset.erase_cons_head, true_or, and_true, true_and]
  decide

/-- Instantiate `CvRDT.gossipLTS_mTr_iff`, `CvRDT.replica_eq_evalHistory`,
`CvRDT.strong_convergence`, and `CvRDT.converge_of_allPairsReachable` on `ringGraph3`. -/
theorem gossipRing_theorems_instantiated :
    let sEnd := gc3.gossipRun gc3.gossipInit gossipRingTrace
    (gc3.gossipLTS ringGraph3).MTr gc3.gossipInit gossipRingTrace sEnd ∧
    sEnd.replica 0 = evalHistory gc3.init sEnd.postState (sEnd.history 0) ∧
    (sEnd.replica 0 = sEnd.replica 2 ∧ gc3.query (sEnd.replica 0) = gc3.query (sEnd.replica 2)) ∧
    (∃ xl' s', (gc3.gossipLTS ringGraph3).MTr sEnd xl' s' ∧
      s'.generated = sEnd.generated ∧
      (∀ p : Fin 3, s'.replica p = Finset.univ.sup' Finset.univ_nonempty sEnd.replica) ∧
      ∀ p : Fin 3, s'.history p = Finset.univ.biUnion sEnd.history) := by
  intro sEnd
  have hv : gc3.gossipValidTrace ringGraph3 gc3.gossipInit gossipRingTrace :=
    gossipRingTrace_valid_and_converged.1
  have hmtr : (gc3.gossipLTS ringGraph3).MTr gc3.gossipInit gossipRingTrace sEnd :=
    (gc3.gossipLTS_mTr_iff ringGraph3 gc3.gossipInit gossipRingTrace sEnd).mpr ⟨hv, rfl⟩
  have hhist : sEnd.history 0 = sEnd.history 2 := by
    rw [gossipRingTrace_valid_and_converged.2.1, gossipRingTrace_valid_and_converged.2.2.2.1]
  exact ⟨hmtr,
    gc3.replica_eq_evalHistory hmtr 0,
    gc3.strong_convergence hmtr hhist,
    gc3.converge_of_allPairsReachable ringGraph3_allPairsReachable sEnd⟩

/-! ### 2. `CmRDT` Over `CausalBroadcast.bssLTS` & `CvRDT ↔ CmRDT` Mutual Emulation -/

def pnCm3 : CmRDT (PNCounter (Fin 3)) (PNCounterOp (Fin 3)) (PNCounterOp (Fin 3)) ℤ :=
  PNCounter.cmrdt (Fin 3)

def bssInc0Pkt : Packet (Fin 3) (PNCounterOp (Fin 3)) :=
  bssBroadcastPacket (bssInit (Fin 3) (PNCounterOp (Fin 3))) 0 (.inc 0)

def bssDec1Pkt : Packet (Fin 3) (PNCounterOp (Fin 3)) :=
  bssBroadcastPacket
    (bssRun (bssInit (Fin 3) (PNCounterOp (Fin 3))) [.broadcast 0 (.inc 0)]) 1 (.dec 1)

/-- Concurrent `PNCounter` broadcast trace on `Fin 3` under fault set `{2}`:
* `0` broadcasts `.inc 0` and `1` concurrently broadcasts `.dec 1`;
* `0` delivers `[.inc 0, .dec 1]` whereas `1` delivers `[.dec 1, .inc 0]` in opposite order;
* `1` then broadcasts `.inc 1` (causally after `.inc 0` and `.dec 1`), whose copy arrives at `2`
  early before `.inc 0` or `.dec 1` and is held back in `(proc 2).pending` (`¬ Deliverable`). -/
def bssConcurrentPNTrace : List (BSSAction (Fin 3) (PNCounterOp (Fin 3))) :=
  let sAfterConcurrent :=
    bssRun (bssInit (Fin 3) (PNCounterOp (Fin 3)))
      [.broadcast 0 (.inc 0),
       .broadcast 1 (.dec 1),
       .recv ⟨0, bssDec1Pkt⟩,
       .deliver 0 bssDec1Pkt,
       .recv ⟨1, bssInc0Pkt⟩,
       .deliver 1 bssInc0Pkt]
  let pktAfter := bssBroadcastPacket sAfterConcurrent 1 (.inc 1)
  [.broadcast 0 (.inc 0),
   .broadcast 1 (.dec 1),
   .recv ⟨0, bssDec1Pkt⟩,
   .deliver 0 bssDec1Pkt,
   .recv ⟨1, bssInc0Pkt⟩,
   .deliver 1 bssInc0Pkt,
   .broadcast 1 (.inc 1),
   .recv ⟨2, pktAfter⟩]

theorem bss_pncounter_opposite_orders_and_holdback :
    let sEnd := bssRun (bssInit (Fin 3) (PNCounterOp (Fin 3))) bssConcurrentPNTrace
    bssValidTrace ({2} : Set (Fin 3)) (bssInit (Fin 3) (PNCounterOp (Fin 3)))
      bssConcurrentPNTrace ∧
    (sEnd.proc 0).delivered = [bssInc0Pkt, bssDec1Pkt] ∧
    (sEnd.proc 1).delivered.take 2 = [bssDec1Pkt, bssInc0Pkt] ∧
    (sEnd.proc 2).delivered = [] ∧
    (sEnd.proc 2).pending ≠ 0 ∧
    (pnCm3.bssReplicaState sEnd 0).value = 0 ∧
    (pnCm3.bssReplicaState sEnd 1).value = 1 := by
  decide

/-- Instantiate the `CmRDT.bss_strong_convergence` bridge theorem directly on `bssLTS {2}` when `0`
and `1` have delivered the same two concurrent packets in opposite orders (`[inc 0, dec 1]` vs
`[dec 1, inc 0]`). -/
theorem bss_pncounter_bridge_instantiated :
    let xl : List (BSSAction (Fin 3) (PNCounterOp (Fin 3))) :=
      [.broadcast 0 (.inc 0),
       .broadcast 1 (.dec 1),
       .recv ⟨0, bssDec1Pkt⟩,
       .deliver 0 bssDec1Pkt,
       .recv ⟨1, bssInc0Pkt⟩,
       .deliver 1 bssInc0Pkt]
    let s := bssRun (bssInit (Fin 3) (PNCounterOp (Fin 3))) xl
    pnCm3.bssReplicaState s 0 = pnCm3.bssReplicaState s 1 ∧
      pnCm3.query (pnCm3.bssReplicaState s 0) = pnCm3.query (pnCm3.bssReplicaState s 1) := by
  intro xl s
  have hv : bssValidTrace ({2} : Set (Fin 3)) (bssInit (Fin 3) (PNCounterOp (Fin 3))) xl := by
    decide
  have hmtr : (bssLTS ({2} : Set (Fin 3))).MTr (bssInit (Fin 3) (PNCounterOp (Fin 3))) xl s :=
    (bssLTS_mTr_iff ({2} : Set (Fin 3)) _ xl s).mpr ⟨hv, rfl⟩
  have hcomm : ConcurrentCommute pnCm3.effect (CausalPrec xl) Packet.payload (BroadcastIn xl) :=
    PNCounter.cmrdt_effectsCommute.concurrentCommute _ _ _
  have hsame : ∀ pkt, pkt ∈ (s.proc 0).delivered ↔ pkt ∈ (s.proc 1).delivered := by
    have hd0 : (s.proc 0).delivered = [bssInc0Pkt, bssDec1Pkt] := by decide
    have hd1 : (s.proc 1).delivered = [bssDec1Pkt, bssInc0Pkt] := by decide
    intro pkt
    rw [hd0, hd1]
    simp [or_comm]
  exact pnCm3.bss_strong_convergence hmtr hcomm hsame

/-- Out-of-order causal holdback in `deliverableEvents` (used by `CmRDT.toCvRDT`): when event `2`
depends on `1` and `1` depends on `0`, receiving `{1, 2}` without `0` yields `∅`, receiving
`{0, 2}` yields `{0}`, and receiving `{0, 1, 2}` unlocks `{0, 1, 2}`. -/
def chainDeps : Fin 3 → Finset (Fin 3)
  | 0 => ∅
  | 1 => {0}
  | 2 => {1}

example :
    deliverableEvents chainDeps ({1, 2} : Finset (Fin 3)) = ∅ ∧
    deliverableEvents chainDeps ({0, 2} : Finset (Fin 3)) = {0} ∧
    deliverableEvents chainDeps ({0, 1, 2} : Finset (Fin 3)) = {0, 1, 2} := by
  decide

/-- Check `CvRDT.toCmRDT` and `CmRDT.toCvRDT_query_eq` emulation theorems on `gc3` and `pnCm3`. -/
theorem cvrdt_cmrdt_emulations_checked :
    EffectsCommute gc3.toCmRDT.effect ∧
    gc3.toCmRDT.effect (gc3.toCmRDT.prepare 0 gc3.init) gc3.init = gc3.update 0 gc3.init ∧
    (pnCm3.toCvRDT (· < ·) chainDeps
        (fun i : Fin 3 => if i = 1 then .dec 1 else .inc i)).query {0, 1, 2} = 1 := by
  refine ⟨gc3.toCmRDT_effectsCommute, gc3.toCmRDT_source_step 0 gc3.init, ?_⟩
  have hdeps_prec : ∀ e x : Fin 3, x ∈ chainDeps e → x < e := by decide
  have hclosed : ∀ e ∈ ({0, 1, 2} : Finset (Fin 3)), chainDeps e ⊆ {0, 1, 2} := by decide
  have hcomm := PNCounter.cmrdt_effectsCommute.concurrentCommute (· < ·)
    (fun i : Fin 3 => if i = 1 then PNCounterOp.dec 1 else PNCounterOp.inc i)
    (({0, 1, 2} : Finset (Fin 3)) : Set (Fin 3))
  have hl : IsCausalLinearization (· < ·) ({0, 1, 2} : Finset (Fin 3)) [0, 1, 2] := by
    refine ⟨by decide, by decide, ?_⟩
    intro e₁ _ e₂ _ hlt
    fin_cases e₁ <;> fin_cases e₂ <;> revert hlt <;> decide
  rw [pnCm3.toCvRDT_query_eq (· < ·) chainDeps hdeps_prec _ hclosed hcomm hl]
  decide

/-! ### 3. `GCounter`, `PNCounter`, `TwoPhaseSet`, `ORSet` (Add-Wins), & Untagged Impossibility -/

/-- Check `GCounter.value_sup_of_local_counts` on a 2-replica `Fin 2` configuration. -/
example :
    let rep : Fin 2 → GCounter (Fin 2) := fun i =>
      if i = 0 then ((GCounter.zero (Fin 2)).inc 0).inc 0
      else (GCounter.zero (Fin 2)).inc 1
    (Finset.univ.sup' Finset.univ_nonempty rep).value = 3 := by
  let rep : Fin 2 → GCounter (Fin 2) := fun i =>
    if i = 0 then ((GCounter.zero (Fin 2)).inc 0).inc 0 else (GCounter.zero (Fin 2)).inc 1
  let k : Fin 2 → ℕ := fun i => if i = 0 then 2 else 1
  have hval := GCounter.value_sup_of_local_counts rep k
    (by decide) (by decide)
  exact hval.trans (by decide)

/-- Contrast `TwoPhaseSet` (concurrent remove-wins + permanent tombstone blocking re-add) against
state-based `ORSetCv` (concurrent add-wins + sequential re-add succeeds with a fresh tag). -/
theorem twoPhaseSet_vs_orSetCv_contrast :
    let tp₁ := (TwoPhaseSet.empty : TwoPhaseSet ℕ).add 7
    let tp₂ := tp₁.remove 7
    (7 ∉ (tp₂.add 7).elements ∧ 7 ∉ (tp₁.add 7 ⊔ tp₁.remove 7).elements) ∧
    (let or₀ := (ORSetCv.empty : ORSetCv (Fin 2) ℕ).add 0 0 7
     7 ∈ ((or₀.removeObserved 7) ⊔ (or₀.add 1 0 7)).elements ∧
     7 ∈ ((or₀.removeObserved 7).add 0 1 7).elements) := by
  refine ⟨⟨TwoPhaseSet.not_mem_readd_after_remove _ 7,
    TwoPhaseSet.remove_wins_concurrent _ _ 7⟩, ?_⟩
  exact ⟨ORSetCv.mem_sup_removeObserved_add (by decide) (by decide) (by decide),
    ORSetCv.mem_add_after_removeObserved (by decide) (by decide)⟩

/-- Shapiro et al. Figure 14 op-based `OR-Set` causal history over `Fin 3` events:
* `0`: replica `0` adds `7` with tag `(0, 0)`;
* `1` (`0 ≺ 1`): replica `0` removes `7` (observing only `{⟨7, 0, 0⟩}`);
* `2` (concurrent with `0` and `1`): replica `1` concurrently adds `7` with tag `(1, 0)`. -/
def fig14Prec (a b : Fin 3) : Prop := a = 0 ∧ b = 1

instance : DecidableRel fig14Prec := fun a b => inferInstanceAs (Decidable (a = 0 ∧ b = 1))

instance : IsStrictOrder (Fin 3) fig14Prec where
  irrefl _ h := by rcases h with ⟨rfl, h⟩; cases h
  trans _ _ _ hab hbc := by rcases hab with ⟨_, rfl⟩; rcases hbc with ⟨h, _⟩; cases h

def fig14Op : Fin 3 → ORSetOp (Fin 2) ℕ
  | 0 => .add 0 0 7
  | 1 => .remove 7
  | 2 => .add 1 0 7

def fig14Eff : Fin 3 → ORSetEff (Fin 2) ℕ
  | 0 => .addTag ⟨7, 0, 0⟩
  | 1 => .removeTags {⟨7, 0, 0⟩}
  | 2 => .addTag ⟨7, 1, 0⟩

def fig14History : ORSetCausalHistory (Fin 2) ℕ (Fin 3) fig14Prec {0, 1, 2} where
  closed := by
    intro a b _ hprec
    rcases hprec with ⟨rfl, rfl⟩
    decide
  opOf := fig14Op
  effOf := fig14Eff
  unique_add_tag := by
    intro e₁ _ e₂ _ p₁ n₁ x₁ p₂ n₂ x₂ h₁ h₂ hp _
    fin_cases e₁ <;> fin_cases e₂
    · rfl
    · nomatch h₂
    · cases h₁; cases h₂; cases hp
    · nomatch h₁
    · nomatch h₁
    · nomatch h₁
    · cases h₁; cases h₂; cases hp
    · nomatch h₂
    · rfl
  eff_add := by
    intro e _ p n x hop
    fin_cases e
    · cases hop; rfl
    · nomatch hop
    · cases hop; rfl
  eff_remove := by
    intro e _ x hop
    fin_cases e
    · simp [fig14Op] at hop
    · simp only [fig14Op, ORSetOp.remove.injEq] at hop
      subst hop
      refine ⟨[0], ⟨List.nodup_singleton 0, by decide, ?_⟩, by decide⟩
      intro u₁ hu₁ u₂ hu₂ hprec
      rcases hprec with ⟨rfl, rfl⟩
      simp at hu₂
    · simp [fig14Op] at hop

/-- Instantiate `ORSetCausalHistory.concurrentCommute`, `ORSetCausalHistory.foldl_eq_survivingTags`,
and `ORSetCausalHistory.mem_elements_iff_causal_add_wins` across both causal linearizations
`[0, 1, 2]` and `[0, 2, 1]` of Figure 14: concurrent `add 7` (`2`) survives `remove 7` (`1`)! -/
theorem fig14_causal_add_wins_verified :
    let l₁ : List (Fin 3) := [0, 1, 2]
    let l₂ : List (Fin 3) := [0, 2, 1]
    ConcurrentCommute orsetEffect fig14Prec fig14History.effOf
      (({0, 1, 2} : Finset (Fin 3)) : Set (Fin 3)) ∧
    l₁.foldl (fun s e => orsetEffect (fig14History.effOf e) s) ∅ = {⟨7, 1, 0⟩} ∧
    l₂.foldl (fun s e => orsetEffect (fig14History.effOf e) s) ∅ = {⟨7, 1, 0⟩} ∧
    7 ∈ orsetElements (l₁.foldl (fun s e => orsetEffect (fig14History.effOf e) s) ∅) ∧
    7 ∈ orsetElements (l₂.foldl (fun s e => orsetEffect (fig14History.effOf e) s) ∅) ∧
    8 ∉ orsetElements (l₂.foldl (fun s e => orsetEffect (fig14History.effOf e) s) ∅) := by
  intro l₁ l₂
  have hl₁ : IsCausalLinearization fig14Prec {0, 1, 2} l₁ := by
    refine ⟨by decide, by decide, ?_⟩
    intro e₁ _ e₂ _ hprec
    rcases hprec with ⟨rfl, rfl⟩
    decide
  have hl₂ : IsCausalLinearization fig14Prec {0, 1, 2} l₂ := by
    refine ⟨by decide, by decide, ?_⟩
    intro e₁ _ e₂ _ hprec
    rcases hprec with ⟨rfl, rfl⟩
    decide
  have hmem7 :
      7 ∈ orsetElements (l₂.foldl (fun s e => orsetEffect (fig14History.effOf e) s) ∅) :=
    (fig14History.mem_elements_iff_causal_add_wins hl₂ 7).mpr
      ⟨2, by decide, ⟨1, 0, rfl⟩, by decide⟩
  have hnot8 :
      8 ∉ orsetElements (l₂.foldl (fun s e => orsetEffect (fig14History.effOf e) s) ∅) := by
    rw [fig14History.mem_elements_iff_causal_add_wins hl₂ 8]
    rintro ⟨e, _, ⟨p, n, hop⟩, _⟩
    fin_cases e <;> simp [fig14History, fig14Op] at hop
  exact ⟨fig14History.concurrentCommute,
    (fig14History.foldl_eq_survivingTags hl₁).trans (by decide),
    (fig14History.foldl_eq_survivingTags hl₂).trans (by decide),
    by decide, hmem7, hnot8⟩

/-- Untagged `Finset` merge impossibility (`not_exists_untagged_finset_merge` &
`untagged_insert_erase_ne_erase_insert`), paired with non-vacuity checks showing `(· ∪ ·)` and
`(· ∩ ·)` are commutative merges that each satisfy one requirement while violating the other. -/
theorem untagged_set_impossibility_and_nonvacuity :
    (¬ ∃ (merge : Finset ℕ → Finset ℕ → Finset ℕ),
        Std.Commutative merge ∧
        (∀ x : ℕ, x ∈ merge ∅ (insert x ∅)) ∧
        (∀ x : ℕ, x ∉ merge {x} (({x} : Finset ℕ).erase x))) ∧
    ((insert 0 (∅ : Finset ℕ)).erase 0 ≠ insert 0 ((∅ : Finset ℕ).erase 0)) ∧
    (∀ x : ℕ, x ∈ (∅ : Finset ℕ) ∪ insert x ∅) ∧
    (∀ x : ℕ, x ∉ ({x} : Finset ℕ) ∩ (({x} : Finset ℕ).erase x)) := by
  refine ⟨not_exists_untagged_finset_merge, untagged_insert_erase_ne_erase_insert 0, ?_, ?_⟩
  · intro x
    exact Finset.mem_union_right _ (Finset.mem_insert_self x _)
  · intro x h
    exact (Finset.mem_erase.mp (Finset.mem_inter.mp h).2).1 rfl

/-! ### 4. Semilattice Irrevocable-Emission Coordination-Free Consistency ↔ Monotonicity -/

/-- Positive monotone CRDT query instantiations (`GCounter` threshold, Boolean threshold on both
`Fin 3` and `Fin 1`, `GSet` membership, and `GSet` selection-projection). -/
theorem positive_monotone_queries_instantiated :
    SemilatticeCoordinationFreeConsistent (Fin 3) (gcounterThresholdEmit (Q := Fin 3) 2) ∧
    SemilatticeObservableConsistent (Fin 3) (gcounterThresholdBool (Q := Fin 3) 2) ∧
    SemilatticeObservableConsistent (Fin 1) (gcounterThresholdBool (Q := Fin 3) 2) ∧
    SemilatticeCoordinationFreeConsistent (Fin 3) (gsetMemEmit (α := ℕ) 5) ∧
    SemilatticeCoordinationFreeConsistent (Fin 3)
      (gsetFilterImage (α := ℕ) (β := ℕ) (fun n => decide (n % 2 = 0)) (· / 2)) :=
  ⟨semilatticeCoordinationFreeConsistent_gcounterThreshold (Fin 3) 2,
   semilatticeObservableConsistent_gcounterThresholdBool (Fin 3) 2,
   semilatticeObservableConsistent_gcounterThresholdBool (Fin 1) 2,
   semilatticeCoordinationFreeConsistent_gsetMem (Fin 3) 5,
   semilatticeCoordinationFreeConsistent_gsetFilterImage (Fin 3) _ _⟩

/-- Concrete `Fin 2` full-gossip execution verifying `emitted_eq_global_of_monotone` for
`gcounterThresholdEmit 2`: neither partitioned replica initially reaches threshold `2` (`1 < 2`),
and after full gossip `[(0, 1), (1, 0), (0, 0), (1, 1)]` both replicas emit `{()}`. -/
example :
    let cfg : Fin 2 → GCounter (Fin 2) := fun i =>
      if i = 0 then (GCounter.zero (Fin 2)).inc 0 else (GCounter.zero (Fin 2)).inc 1
    let hops : List (Fin 2 × Fin 2) := [(0, 1), (1, 0), (0, 0), (1, 1)]
    (initIrrevocableState (gcounterThresholdEmit 2) cfg).emitted 0 = ∅ ∧
    (initIrrevocableState (gcounterThresholdEmit 2) cfg).emitted 1 = ∅ ∧
    (runGossipEmit (gcounterThresholdEmit 2) cfg hops).emitted 0 = {()} ∧
    (runGossipEmit (gcounterThresholdEmit 2) cfg hops).emitted 1 = {()} := by
  intro cfg hops
  have hcovers : ∀ src dst : Fin 2, (src, dst) ∈ hops := by decide
  have h0 := emitted_eq_global_of_monotone (monotone_gcounterThresholdEmit 2) cfg hcovers 0
  have h1 := emitted_eq_global_of_monotone (monotone_gcounterThresholdEmit 2) cfg hcovers 1
  refine ⟨by decide, by decide, h0.2.trans (by decide), h1.2.trans (by decide)⟩

/-- On a 1-node network (`Fin 1`), even non-monotone `gsetIsEmptyEmit` is coordination-free
consistent (`semilatticeCoordinationFreeConsistent_of_subsingleton`), confirming that
`[Nontrivial P]` in `semilatticeCoordinationFreeConsistent_iff_monotone` is non-vacuous and
necessary. -/
example : SemilatticeCoordinationFreeConsistent (Fin 1) (gsetIsEmptyEmit (α := ℕ)) :=
  semilatticeCoordinationFreeConsistent_of_subsingleton _

/-- Negative non-monotone CRDT query refutations over `Fin 2`, together with a `decide`-checked
2-replica split-brain execution where replica `0` (`∅`) irrevocably emits `() ∈ gsetIsEmptyEmit ∅`
while replica `1` holds `{9}`, retracting `() ∉ gsetIsEmptyEmit (globalMergedState cfg)`. -/
theorem negative_nonmonotone_queries_and_split_brain :
    ¬ SemilatticeCoordinationFreeConsistent (Fin 2) (gsetIsEmptyEmit (α := ℕ)) ∧
    ¬ SemilatticeCoordinationFreeConsistent (Fin 2) (TwoPhaseSet.elements (α := ℕ)) ∧
    ¬ SemilatticeCoordinationFreeConsistent (Fin 2) (gcounterExactCountEmit (Q := Fin 2) 0) ∧
    (let cfg : Fin 2 → Finset ℕ := fun i => if i = 0 then ∅ else {9}
     () ∈ (runGossipEmit gsetIsEmptyEmit cfg []).emitted 0 ∧
     () ∉ gsetIsEmptyEmit (globalMergedState cfg)) := by
  exact ⟨not_semilatticeCoordinationFreeConsistent_gsetIsEmpty (Fin 2),
    not_semilatticeCoordinationFreeConsistent_twoPhaseSetElements (Fin 2),
    not_semilatticeCoordinationFreeConsistent_gcounterExactCount (Fin 2) 0,
    by decide⟩

end CslibFrontierTests.Distributed.CRDT
