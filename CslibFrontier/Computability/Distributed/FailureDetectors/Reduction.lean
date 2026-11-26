/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.FailureDetectors.Hierarchy
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.Dedup

/-!
# Suspect-Forwarding Gossip Reduction from Weak to Strong Completeness

Formalizes the suspect-forwarding gossip transducer step after
[Chandra and Toueg, §3, Figure 3, Lemmas 3.1–3.3 and Theorem 3.4, pp. 235–238][ChandraToueg1996]
(part of #7503).

## Transducer model

In [Chandra and Toueg, §3, Figure 3, p. 236][ChandraToueg1996], each process `p` maintains an
emulated suspect set `output_p` (initially `∅`), periodically broadcasts `(p, suspects_p)` queried
from its underlying local failure detector, and upon receiving `(q, suspects_q)` updates
`output_p ← (output_p ∪ suspects_q) \ {q}`.

Here we model asynchronous suspect-forwarding runs directly via:

* `GossipPacket P`: a tagged suspect-list broadcast `(sender, sendTick)` carrying
  `H sender sendTick`.
* `applyGossipPacket H out pkt`: Figure 3's Task-2 state transition
  `(out ∪ H pkt.sender pkt.sendTick) \ {pkt.sender}`.
* `gossipHistory H sched`: executable discrete-tick transducer folding `applyGossipPacket H` over
  the packet list `sched p t` delivered to `p` during tick `t`, allowing arbitrary unbounded finite
  message delays and out-of-order delivery across ticks.
* `AdmissibleGossipSchedule F sched`: causal, crash-respecting, duplicate-free asynchronous
  delivery in which every correct sender has infinitely many post-`t₀` packets delivered to every
  correct recipient, witnessed constructively (with zero-delay `sendTick = t` delivery) for every
  `F` by `syncGossipSchedule`.

We prove the three key properties P1–P3 as discrete-tick gossip-transducer steps for #7503 (after
[Lemmas 3.1–3.3, p. 237][ChandraToueg1996]) for every `AdmissibleGossipSchedule F sched`:

1. **P1 (`gossipHistory_strongCompleteness`):** boosts `WeakCompleteness F H` to
   `StrongCompleteness F (gossipHistory H sched)` on finite `P`.
2. **P2 (`gossipHistory_preserves_perpetual_notMem`):** if no alive process suspects `p` before
   tick `t` in `H`, then no process suspects `p` at tick `t` in `gossipHistory H sched`, preserving
   both `StrongAccuracy` and `WeakAccuracy`.
3. **P3 (`gossipHistory_preserves_eventual_notMem`):** if no correct process suspects a correct `p`
   from `t₁` onward in `H`, then eventually no correct process suspects `p` in
   `gossipHistory H sched`, preserving both `EventualStrongAccuracy` and `EventualWeakAccuracy`.

Combining P1–P3 yields all four gossip-transducer reduction steps `Q → P`, `W → S`, `◇Q → ◇P`, and
`◇W → ◇S` (`gossipHistory_isPerfect_of_isQuasiPerfect`, `gossipHistory_isStrong_of_isWeak`,
`gossipHistory_isEventuallyPerfect_of_isEventuallyQuasiPerfect`,
`gossipHistory_isEventuallyStrong_of_isEventuallyWeak`, and
`DetectorClass.gossipHistory_sat_boost`).

## Main definitions

* `Cslib.Distributed.FailureDetectors.GossipPacket`: `(sender, sendTick)` identifier of a broadcast
  suspect set.
* `Cslib.Distributed.FailureDetectors.applyGossipPacket`,
  `Cslib.Distributed.FailureDetectors.gossipHistory`: executable Task-2 update and discrete-tick
  suspect-forwarding transducer.
* `Cslib.Distributed.FailureDetectors.AdmissibleGossipSchedule`: asynchronous causality, crash
  validity, non-duplication, and correct-to-correct liveness conditions on a gossip schedule.
* `Cslib.Distributed.FailureDetectors.syncGossipSchedule`: zero-delay (`sendTick = t`) all-to-all
  gossip schedule witnessing non-vacuity of `AdmissibleGossipSchedule F`.
* `Cslib.Distributed.FailureDetectors.DetectorClass.boost`: projection of the 8 detector classes
  onto the 4 strong-completeness classes `{.P, .S, .EP, .ES}`.

## Main results

* `Cslib.Distributed.FailureDetectors.gossipHistory_strongCompleteness`: discrete-tick
  gossip-transducer step for #7503 boosting `WeakCompleteness` to `StrongCompleteness` (after
  Lemma 3.1, p. 237).
* `Cslib.Distributed.FailureDetectors.gossipHistory_strongAccuracy`,
  `Cslib.Distributed.FailureDetectors.gossipHistory_weakAccuracy`: discrete-tick gossip-transducer
  steps for #7503 preserving perpetual accuracy (after Lemma 3.2, p. 237).
* `Cslib.Distributed.FailureDetectors.gossipHistory_eventualStrongAccuracy`,
  `Cslib.Distributed.FailureDetectors.gossipHistory_eventualWeakAccuracy`: discrete-tick
  gossip-transducer steps for #7503 preserving eventual accuracy on finite `P` (after Lemma 3.3,
  p. 237).
* `Cslib.Distributed.FailureDetectors.gossipHistory_isPerfect_of_isQuasiPerfect`,
  `Cslib.Distributed.FailureDetectors.gossipHistory_isStrong_of_isWeak`,
  `Cslib.Distributed.FailureDetectors.gossipHistory_isEventuallyPerfect_of_isEventuallyQuasiPerfect`
  and `Cslib.Distributed.FailureDetectors.gossipHistory_isEventuallyStrong_of_isEventuallyWeak`,
  `Cslib.Distributed.FailureDetectors.DetectorClass.gossipHistory_sat_boost`: discrete-tick
  gossip-transducer steps for #7503 for `Q → P`, `W → S`, `◇Q → ◇P`, and `◇W → ◇S` (after
  Theorem 3.4, p. 237, and Corollary 3.5, p. 238).
* `Cslib.Distributed.FailureDetectors.admissible_syncGossipSchedule`: non-vacuity of
  `AdmissibleGossipSchedule F` via `syncGossipSchedule`.

## References

* [T. D. Chandra and S. Toueg, *Unreliable Failure Detectors for Reliable Distributed
  Systems*][ChandraToueg1996]
-/

public section

namespace Cslib.Distributed.FailureDetectors

open Finset

/-! ### Suspect-forwarding packets and executable transducer -/

/-- Identifier for a suspect-list broadcast `(sender, H sender sendTick)` emitted at global clock
tick `sendTick` ([Chandra and Toueg, §3, Figure 3, Task 1, p. 236][ChandraToueg1996]). -/
structure GossipPacket (P : Type*) where
  /-- Process `q` that queried its local failure detector and sent `(q, suspects_q)`. -/
  sender : P
  /-- Global clock tick at which `sender` queried its local failure detector. -/
  sendTick : ℕ
  deriving @[expose] DecidableEq

/-- Task-2 update of [Chandra and Toueg, §3, Figure 3, p. 236][ChandraToueg1996]: upon receiving
`(q, suspects_q)` (`pkt`), process `p` adds `H pkt.sender pkt.sendTick` to its emulated suspect set
and removes `pkt.sender`. -/
@[expose] def applyGossipPacket {P : Type*} [DecidableEq P] (H : DetectorHistory P)
    (out : Finset P) (pkt : GossipPacket P) : Finset P :=
  (out ∪ H pkt.sender pkt.sendTick) \ {pkt.sender}

/-- Executable discrete-tick suspect-forwarding transducer: starts with `∅` at tick `0` and folds
`applyGossipPacket H` across the packets `sched p t` delivered to `p` during tick `t`. -/
@[expose] def gossipHistory {P : Type*} [DecidableEq P] (H : DetectorHistory P)
    (sched : P → ℕ → List (GossipPacket P)) (p : P) : ℕ → Finset P
  | 0 => ∅
  | t + 1 => (sched p t).foldl (applyGossipPacket H) (gossipHistory H sched p t)

@[simp]
theorem gossipHistory_zero {P : Type*} [DecidableEq P] (H : DetectorHistory P)
    (sched : P → ℕ → List (GossipPacket P)) (p : P) :
    gossipHistory H sched p 0 = ∅ := rfl

@[simp]
theorem gossipHistory_succ {P : Type*} [DecidableEq P] (H : DetectorHistory P)
    (sched : P → ℕ → List (GossipPacket P)) (p : P) (t : ℕ) :
    gossipHistory H sched p (t + 1) =
      (sched p t).foldl (applyGossipPacket H) (gossipHistory H sched p t) := rfl

/-! ### List-fold transfer lemmas for `applyGossipPacket` -/

private theorem notMem_foldl_applyGossipPacket {P : Type*} [DecidableEq P]
    (H : DetectorHistory P) {p : P} {l : List (GossipPacket P)} {out : Finset P}
    (hout : p ∉ out) (hl : ∀ pkt ∈ l, p ∉ H pkt.sender pkt.sendTick) :
    p ∉ l.foldl (applyGossipPacket H) out := by
  induction l generalizing out with
  | nil => exact hout
  | cons pkt rest ih =>
    refine ih ?_ fun pkt' hpkt' => hl pkt' (List.mem_cons_of_mem pkt hpkt')
    simp only [applyGossipPacket, mem_sdiff, mem_union, hout, hl pkt List.mem_cons_self,
      or_self, false_and, not_false_eq_true]

private theorem mem_foldl_applyGossipPacket_of_mem {P : Type*} [DecidableEq P]
    (H : DetectorHistory P) {p : P} {l : List (GossipPacket P)} {out : Finset P}
    (hout : p ∈ out) (hnsend : ∀ pkt ∈ l, pkt.sender ≠ p) :
    p ∈ l.foldl (applyGossipPacket H) out := by
  induction l generalizing out with
  | nil => exact hout
  | cons pkt rest ih =>
    refine ih ?_ fun pkt' hpkt' => hnsend pkt' (List.mem_cons_of_mem pkt hpkt')
    simp only [applyGossipPacket, mem_sdiff, mem_union, hout, true_or, mem_singleton,
      (hnsend pkt List.mem_cons_self).symm, not_false_eq_true, and_self]

private theorem mem_foldl_applyGossipPacket_of_pkt {P : Type*} [DecidableEq P]
    (H : DetectorHistory P) {p : P} {l : List (GossipPacket P)} {out : Finset P}
    {pkt₀ : GossipPacket P} (hpkt₀ : pkt₀ ∈ l) (hsusp : p ∈ H pkt₀.sender pkt₀.sendTick)
    (hnsend : ∀ pkt ∈ l, pkt.sender ≠ p) :
    p ∈ l.foldl (applyGossipPacket H) out := by
  induction l generalizing out with
  | nil => nomatch hpkt₀
  | cons pkt rest ih =>
    rcases List.mem_cons.mp hpkt₀ with rfl | hrest
    · apply mem_foldl_applyGossipPacket_of_mem H _
        (fun pkt' hpkt' => hnsend pkt' (List.mem_cons_of_mem pkt₀ hpkt'))
      simp only [applyGossipPacket, mem_sdiff, mem_union, hsusp, or_true, mem_singleton,
        (hnsend pkt₀ List.mem_cons_self).symm, not_false_eq_true, and_self]
    · exact ih hrest (fun pkt' hpkt' => hnsend pkt' (List.mem_cons_of_mem pkt hpkt'))

private theorem notMem_foldl_applyGossipPacket_of_sender {P : Type*} [DecidableEq P]
    (H : DetectorHistory P) {p : P} {l : List (GossipPacket P)} {out : Finset P}
    {pkt₀ : GossipPacket P} (hpkt₀ : pkt₀ ∈ l) (hsend : pkt₀.sender = p)
    (hl : ∀ pkt ∈ l, p ∉ H pkt.sender pkt.sendTick) :
    p ∉ l.foldl (applyGossipPacket H) out := by
  induction l generalizing out with
  | nil => nomatch hpkt₀
  | cons pkt rest ih =>
    rcases List.mem_cons.mp hpkt₀ with rfl | hrest
    · apply notMem_foldl_applyGossipPacket H _
        (fun pkt' hpkt' => hl pkt' (List.mem_cons_of_mem pkt₀ hpkt'))
      simp only [applyGossipPacket, hsend, mem_sdiff, mem_singleton, not_true, and_false,
        not_false_eq_true]
    · exact ih hrest (fun pkt' hpkt' => hl pkt' (List.mem_cons_of_mem pkt hpkt'))

/-! ### Asynchronous gossip schedule admissibility -/

/-- Asynchronous admissibility of a packet-delivery schedule `sched` for failure pattern `F`
(modeling the asynchronous run assumptions of
[Chandra and Toueg, §2.5, p. 234; §3, pp. 236–237][ChandraToueg1996]):
* `valid_delivery`: packets delivered to `p` at tick `t` require `p ∉ F t`, `pkt.sendTick ≤ t`, and
  `pkt.sender ∉ F pkt.sendTick`.
* `unique_delivery_tick`: a given packet `pkt` is delivered to recipient `p` in at most one tick.
* `fair_delivery`: for any correct sender `q ∈ F.Correct`, correct recipient `p ∈ F.Correct`, and
  threshold `t₀`, some packet sent by `q` at `t_send ≥ t₀` is delivered to `p` at
  `t_recv ≥ t_send`. -/
structure AdmissibleGossipSchedule {P : Type*} (F : FailurePattern P)
    (sched : P → ℕ → List (GossipPacket P)) : Prop where
  /-- Only non-crashed processes receive packets, and every delivered packet was sent no later than
  the delivery tick by a process not yet crashed at `sendTick`. -/
  valid_delivery : ∀ p t pkt, pkt ∈ sched p t →
    p ∉ F t ∧ pkt.sendTick ≤ t ∧ pkt.sender ∉ F pkt.sendTick
  /-- At-most-once delivery tick per `(recipient, packet)` pair (preventing unbounded replay of
  pre-crash messages). -/
  unique_delivery_tick : ∀ p t₁ t₂ pkt, pkt ∈ sched p t₁ → pkt ∈ sched p t₂ → t₁ = t₂
  /-- Every correct process infinitely often broadcasts packets that reach every correct process. -/
  fair_delivery : ∀ q ∈ F.Correct, ∀ p ∈ F.Correct, ∀ t₀,
    ∃ t_send t_recv, t₀ ≤ t_send ∧ t_send ≤ t_recv ∧
      GossipPacket.mk q t_send ∈ sched p t_recv

/-! ### Finite horizon for stale packet deliveries -/

/-- Because each packet in a finite set `bad : Finset (GossipPacket P)` can be delivered to `q` in
at most one tick (`unique_delivery_tick`), there is a finite tick `B` from which onward `q` never
receives any packet in `bad`. -/
private theorem exists_tick_disjoint_packets {P : Type*} {F : FailurePattern P}
    {sched : P → ℕ → List (GossipPacket P)} (hadm : AdmissibleGossipSchedule F sched)
    (q : P) (bad : Finset (GossipPacket P)) :
    ∃ B, ∀ t, B ≤ t → ∀ pkt ∈ sched q t, pkt ∉ bad := by
  classical
  let lastPlusOne : GossipPacket P → ℕ := fun pkt =>
    if h : ∃ t, pkt ∈ sched q t then h.choose + 1 else 0
  let B := bad.sup lastPlusOne
  refine ⟨B, fun t ht pkt hpkt hmem => ?_⟩
  have hex : ∃ t', pkt ∈ sched q t' := ⟨t, hpkt⟩
  have heq : t = hex.choose := hadm.unique_delivery_tick q t hex.choose pkt hpkt hex.choose_spec
  have hle : hex.choose + 1 ≤ B := by
    simpa only [lastPlusOne, hex, ↓reduceDIte] using Finset.le_sup (f := lastPlusOne) hmem
  omega

/-- On a finite process type, per-process thresholds after which `R p` holds combine into one
uniform threshold. -/
private theorem exists_uniform_threshold {P : Type*} [Finite P] {S : P → Prop} {R : P → ℕ → Prop}
    (h : ∀ p, S p → ∃ T, ∀ t, T ≤ t → R p t) : ∃ T, ∀ t, T ≤ t → ∀ p, S p → R p t := by
  classical
  let _ := Fintype.ofFinite P
  let bound : P → ℕ := fun p => if hp : S p then (h p hp).choose else 0
  refine ⟨univ.sup bound, fun t ht p hp => (h p hp).choose_spec t (le_trans ?_ ht)⟩
  simpa only [bound, hp, ↓reduceDIte] using le_sup (f := bound) (mem_univ p)

/-! ### Lemmas 3.1, 3.2, and 3.3 of Chandra–Toueg (1996, p. 237) -/

/-- Discrete-tick gossip-transducer step for #7503 (Property P2, after
[Chandra and Toueg, Lemma 3.2, p. 237][ChandraToueg1996]): in `gossipHistory`, if no non-crashed
process suspects `p` strictly before tick `t` in `H`, then no process suspects `p` at tick `t` in
`gossipHistory H sched`. -/
theorem gossipHistory_preserves_perpetual_notMem {P : Type*} [DecidableEq P]
    {F : FailurePattern P} {sched : P → ℕ → List (GossipPacket P)}
    (hadm : AdmissibleGossipSchedule F sched) (H : DetectorHistory P) {p : P} {t : ℕ}
    (hH : ∀ t', t' < t → ∀ r ∉ F t', p ∉ H r t') :
    ∀ q, p ∉ gossipHistory H sched q t := by
  induction t with
  | zero => exact fun q => notMem_empty p
  | succ t ih =>
    intro q
    rw [gossipHistory_succ]
    refine notMem_foldl_applyGossipPacket H (ih (fun t' ht' r hr => hH t' (by omega) r hr) q)
      fun pkt hpkt => ?_
    obtain ⟨_, hle, hsend⟩ := hadm.valid_delivery q t pkt hpkt
    exact hH pkt.sendTick (by omega) pkt.sender hsend

/-- Discrete-tick gossip-transducer step for #7503 (after
[Chandra and Toueg, Lemma 3.2, p. 237][ChandraToueg1996]): `gossipHistory` preserves
`StrongAccuracy`. -/
theorem gossipHistory_strongAccuracy {P : Type*} [DecidableEq P]
    {F : FailurePattern P} {sched : P → ℕ → List (GossipPacket P)}
    (hadm : AdmissibleGossipSchedule F sched) {H : DetectorHistory P}
    (hSA : StrongAccuracy F H) :
    StrongAccuracy F (gossipHistory H sched) := fun _ _ hp q _ =>
  gossipHistory_preserves_perpetual_notMem hadm H (fun t' ht' r hr =>
    hSA t' _ (fun hmem => hp (F.mem_of_le ht'.le hmem)) r hr) q

/-- Discrete-tick gossip-transducer step for #7503 (after
[Chandra and Toueg, Lemma 3.2, p. 237][ChandraToueg1996]): `gossipHistory` preserves
`WeakAccuracy`. -/
theorem gossipHistory_weakAccuracy {P : Type*} [DecidableEq P]
    {F : FailurePattern P} {sched : P → ℕ → List (GossipPacket P)}
    (hadm : AdmissibleGossipSchedule F sched) {H : DetectorHistory P}
    (hWA : WeakAccuracy F H) :
    WeakAccuracy F (gossipHistory H sched) :=
  hWA.imp fun _ ⟨hp, hns⟩ =>
    ⟨hp, fun _ q _ => gossipHistory_preserves_perpetual_notMem hadm H (fun t' _ => hns t') q⟩

/-- Discrete-tick gossip-transducer step for #7503 (Property P1, after
[Chandra and Toueg, Lemma 3.1, p. 237][ChandraToueg1996]): on finite `P`, if `H` satisfies
`WeakCompleteness F H`, then `gossipHistory H sched` satisfies `StrongCompleteness F` for every
`AdmissibleGossipSchedule F sched`. -/
theorem gossipHistory_strongCompleteness {P : Type*} [Finite P] [DecidableEq P]
    {F : FailurePattern P} {sched : P → ℕ → List (GossipPacket P)}
    (hadm : AdmissibleGossipSchedule F sched) {H : DetectorHistory P}
    (hWC : WeakCompleteness F H) :
    StrongCompleteness F (gossipHistory H sched) := by
  classical
  let _ := Fintype.ofFinite P
  obtain ⟨t₁, ht₁⟩ := hWC
  -- For a fixed crashed `p` and correct `q`, show `q` eventually permanently suspects `p`.
  have hpair : ∀ p ∈ F.Crashed, ∀ q ∈ F.Correct,
      ∃ T, ∀ t', T ≤ t' → p ∈ gossipHistory H sched q t' := by
    intro p hp q hq
    obtain ⟨t_crash, hcrash⟩ := hp
    obtain ⟨w, hw, hw_susp⟩ := ht₁ p ⟨t_crash, hcrash⟩
    let pPkts : Finset (GossipPacket P) :=
      (Finset.range t_crash).image (fun s => GossipPacket.mk p s)
    obtain ⟨B, hB⟩ := exists_tick_disjoint_packets hadm q pPkts
    have hno_p : ∀ t, B ≤ t → ∀ pkt ∈ sched q t, pkt.sender ≠ p := by
      rintro t ht ⟨_, s⟩ hpkt rfl
      exact hB t ht _ hpkt (mem_image.mpr ⟨s, mem_range.mpr
        (not_le.mp fun hge => (hadm.valid_delivery q t _ hpkt).2.2 (F.mem_of_le hge hcrash)), rfl⟩)
    obtain ⟨t_send, t_recv, hts_ge, htr_ge, hdeliv⟩ :=
      hadm.fair_delivery w hw q hq (max t₁ B)
    have hBt : B ≤ t_recv := ((le_max_right t₁ B).trans hts_ge).trans htr_ge
    refine ⟨t_recv + 1, fun t' ht' => ?_⟩
    induction t', ht' using Nat.le_induction with
    | base =>
      exact mem_foldl_applyGossipPacket_of_pkt H hdeliv
        (hw_susp t_send ((le_max_left t₁ B).trans hts_ge)) (hno_p t_recv hBt)
    | succ n hn ih => exact mem_foldl_applyGossipPacket_of_mem H ih (hno_p n (by omega))
  -- Take a uniform threshold across correct `q`, then across crashed `p`.
  obtain ⟨T, hT⟩ := exists_uniform_threshold fun p hp => exists_uniform_threshold (hpair p hp)
  exact ⟨T, fun p hp q hq t' ht' => hT t' ht' p hp q hq⟩

/-- Discrete-tick gossip-transducer step for #7503 (Property P3, after
[Chandra and Toueg, Lemma 3.3, p. 237][ChandraToueg1996]): on finite `P`, if `p ∈ F.Correct` and
no correct process suspects `p` from tick `t₁` onward in `H`, then there is a tick `T` from which
onward no correct process suspects `p` in `gossipHistory H sched`. -/
theorem gossipHistory_preserves_eventual_notMem {P : Type*} [Finite P] [DecidableEq P]
    {F : FailurePattern P} {sched : P → ℕ → List (GossipPacket P)}
    (hadm : AdmissibleGossipSchedule F sched) (H : DetectorHistory P)
    {p : P} (hp : p ∈ F.Correct) {t₁ : ℕ}
    (hH : ∀ t', t₁ ≤ t' → ∀ r ∈ F.Correct, p ∉ H r t') :
    ∃ T, ∀ t', T ≤ t' → ∀ q ∈ F.Correct, p ∉ gossipHistory H sched q t' := by
  classical
  let _ := Fintype.ofFinite P
  obtain ⟨t_stab, hstab⟩ := F.exists_stabilize
  let cutoff := max t₁ t_stab
  let badPkts : Finset (GossipPacket P) :=
    (Finset.univ : Finset P).biUnion fun r =>
      (Finset.range cutoff).image fun s => GossipPacket.mk r s
  have hper_q : ∀ q ∈ F.Correct, ∃ Tq, ∀ t', Tq ≤ t' → p ∉ gossipHistory H sched q t' := by
    intro q hq
    obtain ⟨B, hB⟩ := exists_tick_disjoint_packets hadm q badPkts
    have hno_susp : ∀ t, B ≤ t → ∀ pkt ∈ sched q t, p ∉ H pkt.sender pkt.sendTick := by
      rintro t ht ⟨r, s⟩ hpkt hsusp
      obtain ⟨_, _, hsend_alive⟩ := hadm.valid_delivery q t _ hpkt
      rcases lt_or_ge s cutoff with hslt | hsge
      · exact hB t ht _ hpkt
          (mem_biUnion.mpr ⟨r, mem_univ r, mem_image_of_mem _ (mem_range.mpr hslt)⟩)
      · exact hH s ((le_max_left t₁ t_stab).trans hsge) r
          (((hstab s ((le_max_right t₁ t_stab).trans hsge)).2 r).mp hsend_alive) hsusp
    obtain ⟨t_send, t_recv, hts_ge, htr_ge, hdeliv⟩ := hadm.fair_delivery p hp q hq B
    have htr_B : B ≤ t_recv := hts_ge.trans htr_ge
    refine ⟨t_recv + 1, fun t' ht' => ?_⟩
    induction t', ht' using Nat.le_induction with
    | base => exact notMem_foldl_applyGossipPacket_of_sender H hdeliv rfl (hno_susp t_recv htr_B)
    | succ n hn ih => exact notMem_foldl_applyGossipPacket H ih (hno_susp n (by omega))
  exact exists_uniform_threshold hper_q

/-- Discrete-tick gossip-transducer step for #7503 (after
[Chandra and Toueg, Lemma 3.3, p. 237][ChandraToueg1996]): `gossipHistory` preserves
`EventualStrongAccuracy` on finite `P`. -/
theorem gossipHistory_eventualStrongAccuracy {P : Type*} [Finite P] [DecidableEq P]
    {F : FailurePattern P} {sched : P → ℕ → List (GossipPacket P)}
    (hadm : AdmissibleGossipSchedule F sched) {H : DetectorHistory P}
    (hESA : EventualStrongAccuracy F H) :
    EventualStrongAccuracy F (gossipHistory H sched) :=
  let ⟨_, ht₁⟩ := hESA
  exists_uniform_threshold fun _ hp =>
    gossipHistory_preserves_eventual_notMem hadm H hp fun t' ht' r hr => ht₁ t' ht' _ hp r hr

/-- Discrete-tick gossip-transducer step for #7503 (after
[Chandra and Toueg, Lemma 3.3, p. 237][ChandraToueg1996]): `gossipHistory` preserves
`EventualWeakAccuracy` on finite `P`. -/
theorem gossipHistory_eventualWeakAccuracy {P : Type*} [Finite P] [DecidableEq P]
    {F : FailurePattern P} {sched : P → ℕ → List (GossipPacket P)}
    (hadm : AdmissibleGossipSchedule F sched) {H : DetectorHistory P}
    (hEWA : EventualWeakAccuracy F H) :
    EventualWeakAccuracy F (gossipHistory H sched) :=
  let ⟨_, p, hp, ht₁⟩ := hEWA
  (gossipHistory_preserves_eventual_notMem hadm H hp ht₁).imp fun _ hT => ⟨p, hp, hT⟩

/-! ### The four completeness-boosting reductions (`Q → P`, `W → S`, `◇Q → ◇P`, `◇W → ◇S`) -/

/-- Discrete-tick gossip-transducer step for #7503 (after
[Chandra and Toueg, Theorem 3.4, p. 237][ChandraToueg1996]): `gossipHistory` upgrades
`IsQuasiPerfect` (`Q`) to `IsPerfect` (`P`). -/
theorem gossipHistory_isPerfect_of_isQuasiPerfect {P : Type*} [Finite P] [DecidableEq P]
    {F : FailurePattern P} {sched : P → ℕ → List (GossipPacket P)}
    (hadm : AdmissibleGossipSchedule F sched) {H : DetectorHistory P}
    (h : IsQuasiPerfect F H) :
    IsPerfect F (gossipHistory H sched) :=
  ⟨gossipHistory_strongCompleteness hadm h.1, gossipHistory_strongAccuracy hadm h.2⟩

/-- Discrete-tick gossip-transducer step for #7503 (after
[Chandra and Toueg, Theorem 3.4, p. 237][ChandraToueg1996]): `gossipHistory` upgrades `IsWeak`
(`W`) to `IsStrong` (`S`). -/
theorem gossipHistory_isStrong_of_isWeak {P : Type*} [Finite P] [DecidableEq P]
    {F : FailurePattern P} {sched : P → ℕ → List (GossipPacket P)}
    (hadm : AdmissibleGossipSchedule F sched) {H : DetectorHistory P}
    (h : IsWeak F H) :
    IsStrong F (gossipHistory H sched) :=
  ⟨gossipHistory_strongCompleteness hadm h.1, gossipHistory_weakAccuracy hadm h.2⟩

/-- Discrete-tick gossip-transducer step for #7503 (after
[Chandra and Toueg, Theorem 3.4, p. 237][ChandraToueg1996]): `gossipHistory` upgrades
`IsEventuallyQuasiPerfect` (`◇Q`) to `IsEventuallyPerfect` (`◇P`). -/
theorem gossipHistory_isEventuallyPerfect_of_isEventuallyQuasiPerfect
    {P : Type*} [Finite P] [DecidableEq P]
    {F : FailurePattern P} {sched : P → ℕ → List (GossipPacket P)}
    (hadm : AdmissibleGossipSchedule F sched) {H : DetectorHistory P}
    (h : IsEventuallyQuasiPerfect F H) :
    IsEventuallyPerfect F (gossipHistory H sched) :=
  ⟨gossipHistory_strongCompleteness hadm h.1, gossipHistory_eventualStrongAccuracy hadm h.2⟩

/-- Discrete-tick gossip-transducer step for #7503 (after
[Chandra and Toueg, Theorem 3.4, p. 237][ChandraToueg1996]): `gossipHistory` upgrades
`IsEventuallyWeak` (`◇W`) to `IsEventuallyStrong` (`◇S`). -/
theorem gossipHistory_isEventuallyStrong_of_isEventuallyWeak
    {P : Type*} [Finite P] [DecidableEq P]
    {F : FailurePattern P} {sched : P → ℕ → List (GossipPacket P)}
    (hadm : AdmissibleGossipSchedule F sched) {H : DetectorHistory P}
    (h : IsEventuallyWeak F H) :
    IsEventuallyStrong F (gossipHistory H sched) :=
  ⟨gossipHistory_strongCompleteness hadm h.1, gossipHistory_eventualWeakAccuracy hadm h.2⟩

/-- Projects each of the eight detector classes onto its strong-completeness counterpart (step map
for #7503, after [Chandra and Toueg, Corollary 3.5, p. 238][ChandraToueg1996]). -/
@[expose] def DetectorClass.boost : DetectorClass → DetectorClass
  | .P | .Q => .P
  | .S | .W => .S
  | .EP | .EQ => .EP
  | .ES | .EW => .ES

@[simp]
theorem DetectorClass.boost_le (c : DetectorClass) : c.boost ≤ c := by
  cases c <;> decide

@[simp]
theorem DetectorClass.boost_idem (c : DetectorClass) : c.boost.boost = c.boost := by
  cases c <;> rfl

/-- Discrete-tick gossip-transducer step for #7503 (after
[Chandra and Toueg, Theorem 3.4, p. 237, and Corollary 3.5, p. 238][ChandraToueg1996]): for every
`c : DetectorClass` and every `AdmissibleGossipSchedule F sched` on finite `P`,
`gossipHistory H sched` upgrades `c` to `c.boost`. -/
theorem DetectorClass.gossipHistory_sat_boost {P : Type*} [Finite P] [DecidableEq P]
    (c : DetectorClass) {F : FailurePattern P} {sched : P → ℕ → List (GossipPacket P)}
    (hadm : AdmissibleGossipSchedule F sched) {H : DetectorHistory P} (hsat : c.Sat F H) :
    c.boost.Sat F (gossipHistory H sched) := by
  cases c with
  | P =>
    by_cases hcorr : F.Correct.Nonempty
    · exact gossipHistory_isPerfect_of_isQuasiPerfect hadm (hsat.toQuasiPerfect hcorr)
    · refine ⟨⟨0, fun _ _ q hq => absurd ⟨q, hq⟩ hcorr⟩,
        gossipHistory_strongAccuracy hadm hsat.2⟩
  | S => exact gossipHistory_isStrong_of_isWeak hadm hsat.toWeak
  | EP =>
    by_cases hcorr : F.Correct.Nonempty
    · exact gossipHistory_isEventuallyPerfect_of_isEventuallyQuasiPerfect hadm
        (hsat.toEventuallyQuasiPerfect hcorr)
    · exact ⟨⟨0, fun _ _ q hq => absurd ⟨q, hq⟩ hcorr⟩,
        ⟨0, fun _ _ p hp => absurd ⟨p, hp⟩ hcorr⟩⟩
  | ES => exact gossipHistory_isEventuallyStrong_of_isEventuallyWeak hadm hsat.toEventuallyWeak
  | Q => exact gossipHistory_isPerfect_of_isQuasiPerfect hadm hsat
  | W => exact gossipHistory_isStrong_of_isWeak hadm hsat
  | EQ => exact gossipHistory_isEventuallyPerfect_of_isEventuallyQuasiPerfect hadm hsat
  | EW => exact gossipHistory_isEventuallyStrong_of_isEventuallyWeak hadm hsat

/-! ### Non-vacuity witness for `AdmissibleGossipSchedule` -/

/-- Zero-delay (`sendTick = t`) all-to-all gossip schedule witnessing non-vacuity of
`AdmissibleGossipSchedule F`: at each tick `t`, every non-crashed process `p ∉ F t` receives one
suspect-list packet `⟨q, t⟩` from each non-crashed process `q ∉ F t` in `procs.dedup`. -/
@[expose] def syncGossipSchedule {P : Type*} [DecidableEq P]
    (F : FailurePattern P) (procs : List P) (p : P) (t : ℕ) : List (GossipPacket P) :=
  if p ∈ F t then []
  else (procs.dedup.filter fun q => decide (q ∉ F t)).map fun q => ⟨q, t⟩

/-- Non-vacuity of `AdmissibleGossipSchedule F`: the zero-delay (`sendTick = t`) schedule
`syncGossipSchedule F procs` satisfies `AdmissibleGossipSchedule F` whenever `procs` lists every
process in `P`. -/
theorem admissible_syncGossipSchedule {P : Type*} [DecidableEq P]
    (F : FailurePattern P) {procs : List P} (hprocs : ∀ q : P, q ∈ procs) :
    AdmissibleGossipSchedule F (syncGossipSchedule F procs) where
  valid_delivery p t pkt hpkt := by
    by_cases hp : p ∈ F t
    · simp [syncGossipSchedule, hp] at hpkt
    · simp only [syncGossipSchedule, hp, ↓reduceIte, List.mem_map, List.mem_filter,
        decide_eq_true_eq] at hpkt
      obtain ⟨q, ⟨_, hq⟩, rfl⟩ := hpkt
      exact ⟨hp, le_rfl, hq⟩
  unique_delivery_tick p t₁ t₂ pkt h₁ h₂ := by
    have hs {t} (h : pkt ∈ syncGossipSchedule F procs p t) : pkt.sendTick = t := by
      by_cases hp : p ∈ F t
      · simp [syncGossipSchedule, hp] at h
      · simp only [syncGossipSchedule, hp, ↓reduceIte, List.mem_map] at h
        obtain ⟨_, _, rfl⟩ := h
        rfl
    exact (hs h₁).symm.trans (hs h₂)
  fair_delivery q hq p hp t₀ := by
    refine ⟨t₀, t₀, le_rfl, le_rfl, ?_⟩
    simp only [syncGossipSchedule, hp t₀, ↓reduceIte, List.mem_map, List.mem_filter,
      List.mem_dedup, decide_eq_true_eq]
    exact ⟨q, ⟨hprocs q, hq t₀⟩, rfl⟩

end Cslib.Distributed.FailureDetectors
