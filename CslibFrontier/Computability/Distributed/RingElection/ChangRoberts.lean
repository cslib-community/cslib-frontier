/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Count
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# All-Initiator Unidirectional FIFO Ring Election Steps

Intermediate steps for unidirectional asynchronous FIFO ring election on `Fin n` (`n ≥ 1`) with
injective identifiers `uid : Fin n → U` when all `n` nodes initiate simultaneously and the election
pass ends upon the maximum-identifier node receiving its own identifier back (steps towards
[Chang and Roberts][ChangRoberts1979], not the arbitrary-initiator or announcement-pass endpoints of
`[ChangRoberts1979]`).

Initially every node `i : Fin n` injects its own identifier `uid i` into its outgoing clockwise
FIFO channel `i → i + 1` (`crAllInit`). Whenever the channel `target - 1 → target` is nonempty, its
oldest message `m` may be delivered to `target` (`crStep`, `crLTS`):

* if `uid target < m`, `target` forwards `m` onto `target → target + 1`;
* if `m < uid target`, `target` discards `m`;
* if `m = uid target`, `target` sets `isLeader target := true` without forwarding `m`.

Because each node's forwarding decision compares `m` only against its static identifier
`uid target`, every token `uid s` traverses a schedule-independent clockwise arc of length
`crHops uid s ∈ {1, …, n}` until hitting the first node `j` with `uid s ≤ uid j`. Tracking per-node
delivery progress yields:

1. **Safety and termination steps (`crAllInit_isLeader_le`, `crAllInit_isLeader_iff_max`,
   `crAllInit_terminates`):** in every state reachable from `crAllInit uid`, only a `uid`-maximizer
   can set `isLeader = true`; every execution terminates in at most `∑ s, crHops uid s` deliveries;
   and every quiescent reachable state elects the unique `uid`-maximizing node `i*` while all
   `j ≠ i*` have `isLeader j = false`.
2. **Worst-case and best-case message steps (`crAllInit_messages_le`, `crAllInit_totalMsgs_rev_eq`,
   `crAllInit_totalMsgs_id_eq`):** total messages transmitted from `crAllInit uid` satisfy
   `crAllInitMsgs uid sched ≤ n * (n + 1) / 2`, attaining `n * (n + 1) / 2` on `Fin.rev` and
   `2 * n - 1` on `id`.
3. **Average-case step (`crAllInit_avg_totalMsgs_eq`):** over uniform random identifier
   permutations `σ : Equiv.Perm (Fin n)`, the average of `crAllInitTotalMsgs` equals
   `∑ k ∈ Finset.Icc 1 n, (n : ℚ) / k`, proved via clockwise arc partitioning (`sum_arcLen_eq`) and
   left-composition with `Equiv.swap v u` within upper-level sets.

## Main definitions

* `Cslib.Distributed.RingElection.CRConfig`, `crAllInit`, `crStep`, `crLTS`, `crExec`: asynchronous
  FIFO configurations, simultaneous all-initiator start state, transitions, and LTS.
* `Cslib.Distributed.RingElection.crAllInitMsgs`, `crAllInitTotalMsgs`, `crHops`: operational and
  combinatorial message/hop counts for simultaneous all-node initiation.

## Main results

* `Cslib.Distributed.RingElection.crAllInit_isLeader_le`: safety step from `crAllInit uid`.
* `Cslib.Distributed.RingElection.crAllInit_isLeader_iff_max`: quiescent leader characterization
  step from `crAllInit uid`.
* `Cslib.Distributed.RingElection.crAllInit_terminates`: bounded-termination and unique-leader step
  from `crAllInit uid`.
* `Cslib.Distributed.RingElection.crAllInit_execMsgs_eq_totalMsgs`,
  `Cslib.Distributed.RingElection.crAllInit_messages_le`: complete-run message-count step and
  `≤ n * (n + 1) / 2` bound step from `crAllInit uid`.
* `Cslib.Distributed.RingElection.crAllInit_totalMsgs_rev_eq`,
  `Cslib.Distributed.RingElection.crAllInit_totalMsgs_id_eq`: `n * (n + 1) / 2` and `2 * n - 1`
  evaluation steps for `crAllInitTotalMsgs`.
* `Cslib.Distributed.RingElection.crAllInit_avg_totalMsgs_eq`: `n H_n` permutation-average step for
  `crAllInitTotalMsgs`.

## References

* [E. Chang, R. Roberts, *An Improved Algorithm for Decentralized Extrema-Finding in Circular
  Configurations of Processes*][ChangRoberts1979]
-/

public section

namespace Cslib.Distributed.RingElection

open Cslib

/-! ### Operational asynchronous FIFO ring model -/

/-- Global configuration of unidirectional FIFO ring election on `Fin n`. -/
@[ext]
structure CRConfig (n : ℕ) (U : Type*) where
  /-- Whether node `i` has received its own identifier back and declared leadership. -/
  isLeader : Fin n → Bool
  /-- Clockwise FIFO channel on directed edge `i → i + 1` (head is oldest, tail is newest). -/
  chan : Fin n → List U

/-- Number of messages currently in flight across all `n` ring channels. -/
@[expose] def CRConfig.inFlight {n : ℕ} {U : Type*} (cfg : CRConfig n U) : ℕ :=
  ∑ i : Fin n, (cfg.chan i).length

/-- Simultaneous all-initiator start configuration: every node `i` injects `[uid i]` onto
`i → i + 1`. -/
@[expose] def crAllInit {n : ℕ} {U : Type*} (uid : Fin n → U) : CRConfig n U where
  isLeader _ := false
  chan i := [uid i]

/-- Deliver the oldest message on channel `target - 1 → target` to node `target` (no-op if empty):
forward if `uid target < m`, drop if `m < uid target`, and set `isLeader target := true` if
`m = uid target`. -/
@[expose] def crStep {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U] (uid : Fin n → U)
    (target : Fin n) (cfg : CRConfig n U) : CRConfig n U :=
  match cfg.chan (target - 1) with
  | [] => cfg
  | m :: rest =>
    let chan₁ := Function.update cfg.chan (target - 1) rest
    if uid target < m then
      CRConfig.mk cfg.isLeader (Function.update chan₁ target (chan₁ target ++ [m]))
    else if m < uid target then
      CRConfig.mk cfg.isLeader chan₁
    else
      CRConfig.mk (Function.update cfg.isLeader target true) chan₁

/-- Number of messages forwarded (transmitted onto `target → target + 1`) by a single `crStep`. -/
@[expose] def crStepMsgs {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U] (uid : Fin n → U)
    (target : Fin n) (cfg : CRConfig n U) : ℕ :=
  match cfg.chan (target - 1) with
  | [] => 0
  | m :: _ => if uid target < m then 1 else 0

/-- Execute a finite delivery schedule `sched : List (Fin n)` starting from `cfg`. -/
@[expose] def crExec {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U] (uid : Fin n → U)
    (cfg : CRConfig n U) (sched : List (Fin n)) : CRConfig n U :=
  sched.foldl (fun c i => crStep uid i c) cfg

/-- Cumulative messages forwarded during `sched` starting from `cfg`. -/
@[expose] def crForwardedMsgs {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U] (uid : Fin n → U)
    (cfg : CRConfig n U) : List (Fin n) → ℕ
  | [] => 0
  | target :: rest =>
    crStepMsgs uid target cfg + crForwardedMsgs uid (crStep uid target cfg) rest

/-- Total messages transmitted across edges in schedule `sched` from `crAllInit uid`: the `n`
initial identifier injections plus all subsequent message forwardings. -/
@[expose] def crAllInitMsgs {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U] (uid : Fin n → U)
    (sched : List (Fin n)) : ℕ :=
  n + crForwardedMsgs uid (crAllInit uid) sched

/-- Labelled transition system of enabled FIFO deliveries for `crStep uid` on `Fin n`. -/
@[expose] def crLTS {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U] (uid : Fin n → U) :
    LTS (CRConfig n U) (Fin n) where
  Tr cfg target cfg' := cfg.chan (target - 1) ≠ [] ∧ cfg' = crStep uid target cfg

/-! ### Clockwise arc lengths and per-token hop counts -/

/-- Clockwise hop distance `d ∈ {1, …, n}` from `a : Fin n` to the next element of `A` along the
ring (`a + 1, a + 2, …, a + n = a`). -/
@[expose] def arcLen {n : ℕ} [NeZero n] (A : Finset (Fin n)) (a : Fin n) : ℕ :=
  match (List.range n).find? (fun k => decide (a + Fin.ofNat n (k + 1) ∈ A)) with
  | some k => k + 1
  | none => n

/-- Clockwise hop count made by node `s`'s initial message `uid s` before reaching the first node
`j` with `uid s ≤ uid j` (`1 ≤ crHops uid s ≤ n`). -/
@[expose] def crHops {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (uid : Fin n → U) (s : Fin n) : ℕ :=
  arcLen (Finset.univ.filter fun j => uid s ≤ uid j) s

/-- Total number of edge transmissions in a complete election pass from `crAllInit uid`. -/
@[expose] def crAllInitTotalMsgs {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (uid : Fin n → U) : ℕ :=
  ∑ s : Fin n, crHops uid s

private theorem ofNat_self_fin (n : ℕ) [NeZero n] : Fin.ofNat n n = 0 :=
  Fin.ext (Nat.mod_self n)

private theorem ofNat_zero_fin (n : ℕ) [NeZero n] : Fin.ofNat n 0 = 0 :=
  Fin.ext (Nat.zero_mod n)

private theorem ofNat_one_fin (n : ℕ) [NeZero n] : Fin.ofNat n 1 = 1 :=
  rfl

private theorem ofNat_add_fin {n : ℕ} [NeZero n] (a b : ℕ) :
    Fin.ofNat n (a + b) = Fin.ofNat n a + Fin.ofNat n b := by
  ext
  change (a + b) % n = (a % n + b % n) % n
  exact Nat.add_mod a b n

private theorem ofNat_val_eq_self {n : ℕ} [NeZero n] (x : Fin n) :
    Fin.ofNat n x.val = x :=
  Fin.ext (Nat.mod_eq_of_lt x.isLt)

private theorem val_add_ofNat_fin {n : ℕ} [NeZero n] (a : Fin n) {k : ℕ} (h : a.val + k < n) :
    (a + Fin.ofNat n k).val = a.val + k := by
  change (a.val + k % n) % n = a.val + k
  rw [Nat.mod_eq_of_lt (show k < n by omega), Nat.mod_eq_of_lt h]

private theorem add_ofNat_fin_inj {n : ℕ} [NeZero n] (a : Fin n) {k₁ k₂ : ℕ} (h₁ : k₁ < n)
    (h₂ : k₂ < n) (h : a + Fin.ofNat n k₁ = a + Fin.ofNat n k₂) : k₁ = k₂ := by
  have hv := congrArg Fin.val (add_left_cancel h)
  change k₁ % n = k₂ % n at hv
  rwa [Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at hv

private theorem fin_add_ofNat_eq_self_iff {n : ℕ} [NeZero n] (a : Fin n) {d : ℕ}
    (hd1 : 1 ≤ d) (hdn : d ≤ n) :
    a + Fin.ofNat n d = a ↔ d = n := by
  constructor
  · intro h
    have hd0 : Fin.ofNat n d = 0 := add_left_cancel (h.trans (add_zero a).symm)
    have hmod : d % n = 0 := congrArg Fin.val hd0
    rcases lt_or_eq_of_le hdn with hlt | heq
    · have := Nat.mod_eq_of_lt hlt
      omega
    · exact heq
  · rintro rfl
    rw [ofNat_self_fin, add_zero]

theorem arcLen_bounds_and_mem {n : ℕ} [NeZero n] {A : Finset (Fin n)} {a : Fin n} (ha : a ∈ A) :
    1 ≤ arcLen A a ∧ arcLen A a ≤ n ∧ a + Fin.ofNat n (arcLen A a) ∈ A ∧
      ∀ k, 1 ≤ k → k < arcLen A a → a + Fin.ofNat n k ∉ A := by
  dsimp only [arcLen]
  cases hfind : (List.range n).find? (fun k => decide (a + Fin.ofNat n (k + 1) ∈ A)) with
  | none =>
    dsimp only
    have hn : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
    have hnone := List.find?_eq_none.mp hfind
    refine ⟨hn, le_rfl, ?_, fun d hd1 hdn => ?_⟩
    · rwa [ofNat_self_fin, add_zero]
    · have hmem : d - 1 ∈ List.range n := List.mem_range.mpr (by omega)
      have hfalse := hnone (d - 1) hmem
      rw [show d - 1 + 1 = d by omega, decide_eq_true_eq] at hfalse
      exact hfalse
  | some k =>
    dsimp only
    obtain ⟨hhit, as, bs, hsplit, hbefore⟩ := List.find?_eq_some_iff_append.mp hfind
    have hk_range : k ∈ List.range n := by
      rw [hsplit]
      exact List.mem_append_right as List.mem_cons_self
    have hk_lt : k < n := List.mem_range.mp hk_range
    refine ⟨by omega, by omega, decide_eq_true_eq.mp hhit, fun d hd1 hdk => ?_⟩
    let j := d - 1
    have hj_lt_k : j < k := by omega
    have hj_range : j ∈ List.range n := List.mem_range.mpr (by omega)
    rw [hsplit, List.mem_append, List.mem_cons] at hj_range
    have hj_as : j ∈ as := by
      rcases hj_range with hjas | hjk | hjbs
      · exact hjas
      · omega
      · exfalso
        have hpw : (as ++ k :: bs).Pairwise (· < ·) := hsplit ▸ List.pairwise_lt_range
        have hgt := (List.pairwise_cons.mp (List.pairwise_append.mp hpw).2.1).1 j hjbs
        omega
    have hnot := hbefore j hj_as
    rw [Bool.not_eq_true', decide_eq_false_iff_not, show j + 1 = d by omega] at hnot
    exact hnot

theorem arcLen_eq_of_isFirst {n : ℕ} [NeZero n] {A : Finset (Fin n)} {a : Fin n} (ha : a ∈ A)
    {d : ℕ} (hd1 : 1 ≤ d) (hmem : a + Fin.ofNat n d ∈ A)
    (hmin : ∀ k, 1 ≤ k → k < d → a + Fin.ofNat n k ∉ A) :
    arcLen A a = d := by
  obtain ⟨ha1, _, hamem, hamin⟩ := arcLen_bounds_and_mem ha
  rcases lt_trichotomy (arcLen A a) d with hlt | heq | hgt
  · exact absurd hamem (hmin (arcLen A a) ha1 hlt)
  · exact heq
  · exact absurd hmem (hamin d hd1 hgt)

private theorem crHops_spec {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (uid : Fin n → U) (s : Fin n) :
    1 ≤ crHops uid s ∧ crHops uid s ≤ n ∧ uid s ≤ uid (s + Fin.ofNat n (crHops uid s)) ∧
      ∀ k, 1 ≤ k → k < crHops uid s → uid (s + Fin.ofNat n k) < uid s := by
  have hs : s ∈ Finset.univ.filter (fun j => uid s ≤ uid j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ s, le_rfl⟩
  obtain ⟨h1, hn, hmem, hmin⟩ := arcLen_bounds_and_mem hs
  refine ⟨h1, hn, (Finset.mem_filter.mp hmem).2, fun k hk1 hk2 => ?_⟩
  have hnot := hmin k hk1 hk2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hnot
  exact hnot

private theorem crHops_eq_n_iff_max {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid) (s : Fin n) :
    crHops uid s = n ↔ ∀ j : Fin n, uid j ≤ uid s := by
  obtain ⟨h1, hn, hle, hlt⟩ := crHops_spec uid s
  constructor
  · intro heq j
    let k := (j - s).val
    have hkj : s + Fin.ofNat n k = j := by
      rw [ofNat_val_eq_self (j - s), add_sub_cancel]
    rcases eq_or_ne k 0 with hk0 | hkne
    · have hjs : j = s := by
        rw [← hkj, hk0, ofNat_zero_fin, add_zero]
      subst hjs
      exact le_rfl
    · have hk_lt : k < crHops uid s := by
        rw [heq]
        exact (j - s).isLt
      exact le_of_lt (hkj ▸ hlt k (by omega) hk_lt)
  · intro hmax
    by_contra hne
    have heq_uid : uid (s + Fin.ofNat n (crHops uid s)) = uid s :=
      le_antisymm (hmax _) hle
    have heq_fin : s + Fin.ofNat n (crHops uid s) = s := huid heq_uid
    exact hne ((fin_add_ofNat_eq_self_iff s h1 hn).mp heq_fin)

/-! ### Message conservation and reachable-state invariant -/

private theorem sum_update_fin {n : ℕ} {α : Type*} [AddCommMonoid α] (f : Fin n → α)
    (i : Fin n) (v : α) :
    (∑ j : Fin n, Function.update f i v j) + f i = (∑ j : Fin n, f j) + v := by
  have h1 := Finset.add_sum_erase Finset.univ (Function.update f i v) (Finset.mem_univ i)
  have h2 := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)
  have herase : ∑ j ∈ Finset.univ.erase i, Function.update f i v j =
      ∑ j ∈ Finset.univ.erase i, f j :=
    Finset.sum_congr rfl fun j hj =>
      Function.update_of_ne (Finset.ne_of_mem_erase hj) v f
  simp only [Function.update_self] at h1
  rw [← h1, herase, ← h2]
  ac_rfl

private theorem sum_length_update {n : ℕ} {α : Type*} (ch : Fin n → List α) (i : Fin n)
    (xs : List α) :
    (∑ j : Fin n, (Function.update ch i xs j).length) + (ch i).length =
      (∑ j : Fin n, (ch j).length) + xs.length := by
  simpa only [Function.apply_update (fun _ => List.length)] using
    sum_update_fin (fun k => (ch k).length) i xs.length

private theorem sum_length_update_cons {n : ℕ} {α : Type*} (ch : Fin n → List α) (i : Fin n)
    {m : α} {tl : List α} (hq : ch i = m :: tl) :
    (∑ j : Fin n, (Function.update ch i tl j).length) + 1 = ∑ j : Fin n, (ch j).length := by
  have hu := sum_length_update ch i tl
  have hq_len : (ch i).length = tl.length + 1 := by rw [hq, List.length_cons]
  omega

private theorem card_filter_eq_sum_ite {α : Type*} (s : Finset α) (P : α → Prop)
    [DecidablePred P] :
    (s.filter P).card = ∑ x ∈ s, if P x then 1 else 0 := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Message conservation along every valid execution `(crLTS uid).MTr (crAllInit uid) sched cfg`:
total messages transmitted equal messages delivered (`sched.length`) plus messages still in flight
(`cfg.inFlight`). -/
private theorem crExecMsgs_eq_length_add_inFlight {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (uid : Fin n → U) {sched : List (Fin n)} {cfg : CRConfig n U}
    (hmtr : (crLTS uid).MTr (crAllInit uid) sched cfg) :
    crAllInitMsgs uid sched = sched.length + cfg.inFlight := by
  suffices ∀ (c₀ : CRConfig n U) (tr : List (Fin n)) (c₁ : CRConfig n U),
      (crLTS uid).MTr c₀ tr c₁ →
      c₀.inFlight + crForwardedMsgs uid c₀ tr = tr.length + c₁.inFlight by
    have hinit : (crAllInit uid).inFlight = n := by
      simp only [CRConfig.inFlight, crAllInit, List.length_singleton, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    have h := this (crAllInit uid) sched cfg hmtr
    rw [hinit] at h
    simpa only [crAllInitMsgs] using h
  intro c₀ tr c₁ h
  induction h with
  | refl => simp only [crForwardedMsgs, List.length_nil, zero_add, add_zero]
  | @stepL s1 target s2 rest s3 htr _ ih =>
    obtain ⟨hne, rfl⟩ := htr
    cases hq : s1.chan (target - 1) with
    | nil => exact absurd hq hne
    | cons m tl =>
      simp only [crForwardedMsgs, crStepMsgs, List.length_cons]
      let chan₁ := Function.update s1.chan (target - 1) tl
      have hlen1 : (∑ j : Fin n, (chan₁ j).length) + 1 = s1.inFlight :=
        sum_length_update_cons s1.chan (target - 1) hq
      by_cases hlt : uid target < m
      · have hstep_eq : crStep uid target s1 =
            CRConfig.mk s1.isLeader (Function.update chan₁ target (chan₁ target ++ [m])) := by
          simp only [crStep, hq, hlt, ↓reduceIte, chan₁]
        simp only [hq, hlt, ↓reduceIte, hstep_eq] at ih ⊢
        have hu2 := sum_length_update chan₁ target (chan₁ target ++ [m])
        rw [List.length_append, List.length_singleton] at hu2
        dsimp only [CRConfig.inFlight] at hlen1 ih ⊢
        linarith
      · have hinf : (crStep uid target s1).inFlight = ∑ j : Fin n, (chan₁ j).length := by
          simp only [crStep, hq, hlt, ↓reduceIte, chan₁]
          split_ifs <;> rfl
        simp only [hq, hlt, ↓reduceIte] at ih ⊢
        rw [hinf] at ih
        dsimp only [CRConfig.inFlight] at hlen1 ih ⊢
        linarith

/-- Global state invariant relating any configuration `cfg` reachable from `crAllInit uid` to a
per-origin hop progress vector `prog : Fin n → ℕ`. -/
private def CRStateInv {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (uid : Fin n → U) (schedLen : ℕ) (cfg : CRConfig n U) (prog : Fin n → ℕ) : Prop :=
  (∀ s, prog s ≤ crHops uid s) ∧
  (∀ e m, m ∈ cfg.chan e → ∃ s, m = uid s) ∧
  (∀ e s, (cfg.chan e).count (uid s) =
    if prog s < crHops uid s ∧ e = s + Fin.ofNat n (prog s) then 1 else 0) ∧
  (∀ i, cfg.isLeader i = decide ((∀ j, uid j ≤ uid i) ∧ prog i = crHops uid i)) ∧
  schedLen = ∑ s : Fin n, prog s ∧
  cfg.inFlight = (Finset.univ.filter fun s => prog s < crHops uid s).card

private theorem crStateInv_init {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid) :
    CRStateInv uid 0 (crAllInit uid) (fun _ => 0) := by
  refine ⟨fun _ => Nat.zero_le _, ?_, ?_, ?_, ?_, ?_⟩
  · intro e m hm
    simp only [crAllInit, List.mem_singleton] at hm
    exact ⟨e, hm⟩
  · intro e s
    have h1 : 0 < crHops uid s := (crHops_spec uid s).1
    simp only [crAllInit, ofNat_zero_fin, add_zero, h1, true_and]
    by_cases hes : e = s
    · rcases hes with rfl
      simp only [List.count_singleton_self, ↓reduceIte]
    · have hne : uid e ≠ uid s := fun h => hes (huid h)
      simp only [hes, ↓reduceIte, List.count_cons_of_ne hne, List.count_nil]
  · intro i
    have hne : 0 ≠ crHops uid i := ne_of_lt (crHops_spec uid i).1
    simp only [crAllInit, hne, and_false, decide_false]
  · simp only [Finset.sum_const_zero]
  · have hfilt : (Finset.univ.filter fun s : Fin n => 0 < crHops uid s) = Finset.univ := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact iff_of_true (crHops_spec uid s).1 trivial
    simp only [CRConfig.inFlight, crAllInit, List.length_singleton, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, hfilt]

private theorem crStateInv_step {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid) {len : ℕ} {cfg cfg' : CRConfig n U}
    {target : Fin n} {prog : Fin n → ℕ}
    (hinv : CRStateInv uid len cfg prog) (htr : (crLTS uid).Tr cfg target cfg') :
    CRStateInv uid (len + 1) cfg' (Function.update prog
      (Classical.choose (hinv.2.1 (target - 1) ((cfg.chan (target - 1)).head htr.1)
        (List.head_mem htr.1)))
      (prog (Classical.choose (hinv.2.1 (target - 1) ((cfg.chan (target - 1)).head htr.1)
        (List.head_mem htr.1))) + 1)) := by
  obtain ⟨hprog_le, hmem_uid, hcnt, hlead, hsum, hflight⟩ := hinv
  obtain ⟨hne, rfl⟩ := htr
  let m := (cfg.chan (target - 1)).head hne
  let rest := (cfg.chan (target - 1)).tail
  have hq : cfg.chan (target - 1) = m :: rest := (List.cons_head_tail hne).symm
  let s := Classical.choose (hmem_uid (target - 1) m (List.head_mem hne))
  have hm_eq : m = uid s := Classical.choose_spec (hmem_uid (target - 1) m (List.head_mem hne))
  let prog' := Function.update prog s (prog s + 1)
  change CRStateInv uid (len + 1) (crStep uid target cfg) prog'
  have hcnt_s := hcnt (target - 1) s
  rw [hq, hm_eq, List.count_cons_self] at hcnt_s
  have hcond : prog s < crHops uid s ∧ target - 1 = s + Fin.ofNat n (prog s) := by
    by_contra hnot
    simp only [hnot, ↓reduceIte] at hcnt_s
    omega
  obtain ⟨hs_lt, htarget_pred⟩ := hcond
  have hrest_cnt_s : rest.count (uid s) = 0 := by
    simp only [hs_lt, htarget_pred, and_self, ↓reduceIte] at hcnt_s
    omega
  have htarget_eq : target = s + Fin.ofNat n (prog s + 1) := by
    calc target = (target - 1) + 1 := (sub_add_cancel target 1).symm
      _ = s + Fin.ofNat n (prog s) + Fin.ofNat n 1 := by rw [htarget_pred, ofNat_one_fin]
      _ = s + Fin.ofNat n (prog s + 1) := by rw [add_assoc, ← ofNat_add_fin]
  have hprog'_le : ∀ x, prog' x ≤ crHops uid x := fun x => by
    rcases eq_or_ne x s with rfl | hx
    · simp only [prog', Function.update_self]; omega
    · simpa only [prog', Function.update_of_ne hx] using hprog_le x
  have hsum' : len + 1 = ∑ x : Fin n, prog' x := by
    have hu := sum_update_fin prog s (prog s + 1)
    change (∑ j : Fin n, prog' j) + prog s = (∑ j : Fin n, prog j) + (prog s + 1) at hu
    omega
  let chan₁ := Function.update cfg.chan (target - 1) rest
  have hlen1 : (∑ j : Fin n, (chan₁ j).length) + 1 = cfg.inFlight :=
    sum_length_update_cons cfg.chan (target - 1) hq
  have hchan1_mem : ∀ e x, x ∈ chan₁ e → ∃ s', x = uid s' := fun e x hx => by
    rcases eq_or_ne e (target - 1) with rfl | he
    · simp only [chan₁, Function.update_self] at hx
      exact hmem_uid (target - 1) x (hq ▸ List.mem_cons_of_mem m hx)
    · simp only [chan₁, Function.update_of_ne he] at hx
      exact hmem_uid e x hx
  have hchan1_cnt : ∀ e s', (chan₁ e).count (uid s') =
      if s' = s then 0
      else if prog s' < crHops uid s' ∧ e = s' + Fin.ofNat n (prog s') then 1 else 0 := by
    intro e s'
    rcases eq_or_ne e (target - 1) with rfl | he
    · simp only [chan₁, Function.update_self]
      rcases eq_or_ne s' s with rfl | hs'
      · simp only [↓reduceIte, hrest_cnt_s]
      · have hne_uid : uid s ≠ uid s' := fun h => hs' (huid h).symm
        have hc := hcnt (target - 1) s'
        rw [hq, hm_eq, List.count_cons_of_ne hne_uid] at hc
        simp only [hs', ↓reduceIte, hc]
    · simp only [chan₁, Function.update_of_ne he, hcnt e s']
      rcases eq_or_ne s' s with rfl | hs'
      · have hne_e : e ≠ s + Fin.ofNat n (prog s) := fun h => he (h.trans htarget_pred.symm)
        simp only [↓reduceIte, hne_e, and_false]
      · simp only [hs', ↓reduceIte]
  obtain ⟨_, hcr_le, hcr_stop, hcr_pass⟩ := crHops_spec uid s
  rcases lt_or_eq_of_le (show prog s + 1 ≤ crHops uid s by omega) with hmore | hdone
  · -- Subcase A: `prog s + 1 < crHops uid s`, so `uid target < uid s = m`.
    have hlt_uid : uid target < m := by
      rw [hm_eq, htarget_eq]
      exact hcr_pass (prog s + 1) (by omega) hmore
    have hstep_eq : crStep uid target cfg =
        CRConfig.mk cfg.isLeader (Function.update chan₁ target (chan₁ target ++ [m])) := by
      simp only [crStep, hq, hlt_uid, ↓reduceIte, chan₁]
    rw [hstep_eq]
    refine ⟨hprog'_le, ?_, ?_, ?_, hsum', ?_⟩
    · intro e x hx
      by_cases he : e = target
      · rw [he] at hx
        simp only [Function.update_self, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx1 | rfl
        · exact hchan1_mem target x hx1
        · exact ⟨s, hm_eq⟩
      · simp only [Function.update_of_ne he] at hx
        exact hchan1_mem e x hx
    · intro e s'
      by_cases he : e = target
      · rw [he]
        simp only [Function.update_self, List.count_append, hchan1_cnt target s']
        rcases eq_or_ne s' s with rfl | hs'
        · simp only [↓reduceIte, zero_add, hm_eq, List.count_singleton_self, prog',
            Function.update_self, hmore, htarget_eq, and_self]
        · have hne_uid : uid s ≠ uid s' := fun h => hs' (huid h).symm
          simp only [hs', ↓reduceIte, hm_eq, List.count_cons_of_ne hne_uid, List.count_nil,
            add_zero, prog', Function.update_of_ne hs']
      · simp only [Function.update_of_ne he, hchan1_cnt e s']
        rcases eq_or_ne s' s with rfl | hs'
        · have hne_t : e ≠ s + Fin.ofNat n (prog s + 1) := fun h => he (h.trans htarget_eq.symm)
          simp only [↓reduceIte, prog', Function.update_self, hne_t, and_false]
        · simp only [hs', ↓reduceIte, prog', Function.update_of_ne hs']
    · intro i
      rw [hlead i]
      rcases eq_or_ne i s with rfl | hi
      · have hne1 : prog s ≠ crHops uid s := by omega
        have hne2 : prog s + 1 ≠ crHops uid s := by omega
        simp only [prog', Function.update_self, hne1, hne2, and_false]
      · simp only [prog', Function.update_of_ne hi]
    · have hfilt_eq : (Finset.univ.filter fun x => prog' x < crHops uid x) =
          Finset.univ.filter fun x => prog x < crHops uid x := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases eq_or_ne x s with rfl | hx
        · simp only [prog', Function.update_self]
          exact ⟨fun _ => hs_lt, fun _ => hmore⟩
        · simp only [prog', Function.update_of_ne hx]
      have hu2 := sum_length_update chan₁ target (chan₁ target ++ [m])
      rw [List.length_append, List.length_singleton] at hu2
      rw [hfilt_eq, ← hflight]
      dsimp only [CRConfig.inFlight] at hlen1 ⊢
      linarith
  · -- Subcase B: `prog s + 1 = crHops uid s`, so `m = uid s ≤ uid target`.
    have hm_le : m ≤ uid target := by
      rw [hm_eq, htarget_eq, hdone]
      exact hcr_stop
    have hnot_lt : ¬ uid target < m := not_lt.mpr hm_le
    have hfilt_erase : (Finset.univ.filter fun x => prog' x < crHops uid x) =
        (Finset.univ.filter fun x => prog x < crHops uid x).erase s := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq]
      rcases eq_or_ne x s with rfl | hx
      · simp only [prog', Function.update_self, hdone, lt_self_iff_false, not_true_eq_false,
          false_and]
      · simp only [prog', Function.update_of_ne hx, hx, not_false_eq_true, true_and]
    have hmem_s_filt : s ∈ Finset.univ.filter fun x => prog x < crHops uid x :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs_lt⟩
    have hcard_erase := Finset.card_erase_add_one hmem_s_filt
    have hchan1_cnt' : ∀ e s', (chan₁ e).count (uid s') =
        if prog' s' < crHops uid s' ∧ e = s' + Fin.ofNat n (prog' s') then 1 else 0 := by
      intro e s'
      rw [hchan1_cnt e s']
      rcases eq_or_ne s' s with rfl | hs'
      · simp only [↓reduceIte, prog', Function.update_self, hdone, lt_self_iff_false, false_and]
      · simp only [hs', ↓reduceIte, prog', Function.update_of_ne hs']
    rcases lt_or_eq_of_le hm_le with hm_strict | hm_self
    · -- Subcase B1: `m < uid target` (dropped, non-maximum `s`).
      have hstep_eq : crStep uid target cfg = CRConfig.mk cfg.isLeader chan₁ := by
        simp only [crStep, hq, hnot_lt, hm_strict, ↓reduceIte, chan₁]
      rw [hstep_eq]
      refine ⟨hprog'_le, hchan1_mem, hchan1_cnt', ?_, hsum', ?_⟩
      · intro i
        rw [hlead i]
        rcases eq_or_ne i s with rfl | hi
        · have hnot_max : ¬ ∀ j, uid j ≤ uid s := fun hall =>
            not_lt_of_ge (hall target) (hm_eq ▸ hm_strict)
          simp only [hnot_max, false_and]
        · simp only [prog', Function.update_of_ne hi]
      · rw [hfilt_erase]
        dsimp only [CRConfig.inFlight] at hflight hlen1 ⊢
        linarith
    · -- Subcase B2: `m = uid target` (`target = s`, unique global maximum elected!).
      have hnot_strict : ¬ m < uid target := hm_self ▸ lt_irrefl m
      have hstep_eq : crStep uid target cfg =
          CRConfig.mk (Function.update cfg.isLeader target true) chan₁ := by
        simp only [crStep, hq, hnot_lt, hnot_strict, ↓reduceIte, chan₁]
      have hts : target = s := (huid (hm_eq.symm.trans hm_self)).symm
      have hd_eq_n : crHops uid s = n := by
        have hself : s + Fin.ofNat n (crHops uid s) = s := by
          rw [← hdone, ← htarget_eq, hts]
        exact (fin_add_ofNat_eq_self_iff s (by omega) hcr_le).mp hself
      have hs_max : ∀ j, uid j ≤ uid s := (crHops_eq_n_iff_max huid s).mp hd_eq_n
      rw [hstep_eq]
      refine ⟨hprog'_le, hchan1_mem, hchan1_cnt', ?_, hsum', ?_⟩
      · intro i
        dsimp only
        rcases eq_or_ne i s with rfl | hi
        · simp only [hts, Function.update_self, prog', hs_max, hdone, implies_true, and_self,
            decide_true]
        · have hit : i ≠ target := fun h => hi (h.trans hts)
          simp only [Function.update_of_ne hit, hlead i, prog', Function.update_of_ne hi]
      · rw [hfilt_erase]
        dsimp only [CRConfig.inFlight] at hflight hlen1 ⊢
        linarith

private theorem crStateInv_of_mtr {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid) {sched : List (Fin n)} {cfg : CRConfig n U}
    (hmtr : (crLTS uid).MTr (crAllInit uid) sched cfg) :
    ∃ prog, CRStateInv uid sched.length cfg prog := by
  suffices ∀ c₀ tr c₁, (crLTS uid).MTr c₀ tr c₁ →
      ∀ l₀ prog₀, CRStateInv uid l₀ c₀ prog₀ →
      ∃ prog₁, CRStateInv uid (l₀ + tr.length) c₁ prog₁ by
    obtain ⟨prog, h⟩ := this (crAllInit uid) sched cfg hmtr 0 (fun _ => 0) (crStateInv_init huid)
    exact ⟨prog, by simpa only [zero_add] using h⟩
  intro c₀ tr c₁ h
  induction h with
  | refl =>
    intro l₀ prog₀ hinv
    exact ⟨prog₀, by simpa only [List.length_nil, add_zero] using hinv⟩
  | @stepL s1 target s2 rest s3 htr _ ih =>
    intro l₀ prog₀ hinv
    have h1 := crStateInv_step huid hinv htr
    obtain ⟨prog₁, h2⟩ := ih (l₀ + 1) _ h1
    exact ⟨prog₁, by simpa only [List.length_cons, add_assoc, add_comm 1 rest.length] using h2⟩

/-! ### Correctness and termination theorems -/

/-- A safety step for simultaneous all-initiator unidirectional FIFO ring election (a step towards
[Chang and Roberts][ChangRoberts1979], not the arbitrary-initiator endpoint): in any configuration
reachable from `crAllInit uid`, if `cfg.isLeader i = true` then `uid i` maximizes `uid`. -/
theorem crAllInit_isLeader_le {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid) {sched : List (Fin n)} {cfg : CRConfig n U}
    (hmtr : (crLTS uid).MTr (crAllInit uid) sched cfg) {i : Fin n} (hi : cfg.isLeader i = true) :
    ∀ j : Fin n, uid j ≤ uid i := by
  obtain ⟨prog, _, _, _, hlead, _, _⟩ := crStateInv_of_mtr huid hmtr
  rw [hlead i, decide_eq_true_eq] at hi
  exact hi.1

private theorem isTerminal_iff_inFlight_eq_zero {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    (uid : Fin n → U) (cfg : CRConfig n U) :
    (crLTS uid).IsTerminal cfg ↔ cfg.inFlight = 0 := by
  constructor
  · intro hterm
    simp only [CRConfig.inFlight, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_true_left,
      List.length_eq_zero_iff]
    intro e
    by_contra hne
    have hpred : (e + 1) - 1 = e := add_sub_cancel_right e 1
    exact hterm (e + 1) (crStep uid (e + 1) cfg) ⟨by rwa [hpred], rfl⟩
  · intro hzero target cfg' ⟨hne, _⟩
    simp only [CRConfig.inFlight, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_true_left,
      List.length_eq_zero_iff] at hzero
    exact hne (hzero (target - 1))

/-- A quiescent-characterization step for simultaneous all-initiator unidirectional FIFO ring
election (a step towards [Chang and Roberts][ChangRoberts1979], not the arbitrary-initiator
endpoint): at any quiescent (`LTS.IsTerminal`) state reachable from `crAllInit uid`,
`cfg.isLeader i = true` iff `uid i` is the global maximum identifier. -/
theorem crAllInit_isLeader_iff_max {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid) {sched : List (Fin n)} {cfg : CRConfig n U}
    (hmtr : (crLTS uid).MTr (crAllInit uid) sched cfg) (hterm : (crLTS uid).IsTerminal cfg)
    (i : Fin n) :
    cfg.isLeader i = true ↔ ∀ j : Fin n, uid j ≤ uid i := by
  obtain ⟨prog, hle, _, _, hlead, _, hflight⟩ := crStateInv_of_mtr huid hmtr
  have hzero : cfg.inFlight = 0 := (isTerminal_iff_inFlight_eq_zero uid cfg).mp hterm
  rw [hzero, eq_comm, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hflight
  have hprog_eq : prog i = crHops uid i := by
    have hnot_lt : ¬ prog i < crHops uid i := hflight (Finset.mem_univ i)
    have := hle i
    omega
  rw [hlead i, hprog_eq, decide_eq_true_eq]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

/-- A complete-run message-count step for simultaneous all-initiator unidirectional FIFO ring
election (a step towards [Chang and Roberts][ChangRoberts1979], not the cited endpoint): every
quiescent configuration reachable from `crAllInit uid` was reached in `crAllInitTotalMsgs uid`
deliveries and transmitted `crAllInitTotalMsgs uid` messages in total. -/
theorem crAllInit_execMsgs_eq_totalMsgs {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid) {sched : List (Fin n)} {cfg : CRConfig n U}
    (hmtr : (crLTS uid).MTr (crAllInit uid) sched cfg) (hterm : (crLTS uid).IsTerminal cfg) :
    crAllInitMsgs uid sched = crAllInitTotalMsgs uid ∧
      sched.length = crAllInitTotalMsgs uid := by
  obtain ⟨prog, hle, _, _, _, hsum, hflight⟩ := crStateInv_of_mtr huid hmtr
  have hzero : cfg.inFlight = 0 := (isTerminal_iff_inFlight_eq_zero uid cfg).mp hterm
  rw [hzero, eq_comm, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hflight
  have hprog_eq : ∀ s : Fin n, prog s = crHops uid s := fun s => by
    have := hflight (Finset.mem_univ s)
    have := hle s
    omega
  have hlen : sched.length = crAllInitTotalMsgs uid := by
    rw [hsum, crAllInitTotalMsgs]
    exact Finset.sum_congr rfl fun s _ => hprog_eq s
  have hmsgs := crExecMsgs_eq_length_add_inFlight uid hmtr
  rw [hzero, add_zero, hlen] at hmsgs
  exact ⟨hmsgs, hlen⟩

private theorem crExecMsgs_le_totalMsgs {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid) {sched : List (Fin n)} {cfg : CRConfig n U}
    (hmtr : (crLTS uid).MTr (crAllInit uid) sched cfg) :
    sched.length ≤ crAllInitTotalMsgs uid ∧
      crAllInitMsgs uid sched ≤ crAllInitTotalMsgs uid := by
  obtain ⟨prog, hle, _, _, _, hsum, hflight⟩ := crStateInv_of_mtr huid hmtr
  have hlen : sched.length ≤ crAllInitTotalMsgs uid := by
    rw [hsum, crAllInitTotalMsgs]
    exact Finset.sum_le_sum fun s _ => hle s
  refine ⟨hlen, ?_⟩
  rw [crExecMsgs_eq_length_add_inFlight uid hmtr, hsum, hflight, card_filter_eq_sum_ite,
    ← Finset.sum_add_distrib, crAllInitTotalMsgs]
  refine Finset.sum_le_sum fun s _ => ?_
  have := hle s
  split_ifs <;> omega

/-- A bounded-termination and unique-leader step for simultaneous all-initiator unidirectional FIFO
ring election (a step towards [Chang and Roberts][ChangRoberts1979], not the arbitrary-initiator
endpoint): every configuration reachable from `crAllInit uid` extends to quiescence, and every
reachable quiescent state elects the unique `uid`-maximizing node `i*`. -/
theorem crAllInit_terminates {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid) :
    (∀ sched cfg, (crLTS uid).MTr (crAllInit uid) sched cfg →
      ∃ tail cfg', (crLTS uid).MTr cfg tail cfg' ∧ (crLTS uid).IsTerminal cfg') ∧
    (∃! iStar : Fin n, ∀ j : Fin n, uid j ≤ uid iStar) ∧
    ∀ sched cfg, (crLTS uid).MTr (crAllInit uid) sched cfg → (crLTS uid).IsTerminal cfg →
      ∃! iStar : Fin n, cfg.isLeader iStar = true := by
  have huniq_max : ∃! iStar : Fin n, ∀ j : Fin n, uid j ≤ uid iStar := by
    obtain ⟨iStar, -, hmax⟩ := Finset.univ.exists_max_image uid Finset.univ_nonempty
    exact ⟨iStar, fun j => hmax j (Finset.mem_univ j),
      fun k hk => huid (le_antisymm (hmax k (Finset.mem_univ k)) (hk iStar))⟩
  refine ⟨?_, huniq_max, ?_⟩
  · intro sched cfg hmtr
    obtain ⟨rem, hrem⟩ : ∃ rem, crAllInitTotalMsgs uid - sched.length = rem := ⟨_, rfl⟩
    induction rem using Nat.strong_induction_on generalizing sched cfg with
    | _ rem ih =>
      by_cases hterm : (crLTS uid).IsTerminal cfg
      · exact ⟨[], cfg, LTS.MTr.refl, hterm⟩
      simp only [LTS.IsTerminal, not_forall, Classical.not_not] at hterm
      obtain ⟨target, c', htr⟩ := hterm
      have hmtr' := hmtr.stepR (crLTS uid) htr
      have hlen' := (crExecMsgs_le_totalMsgs huid hmtr').1
      rw [List.length_append, List.length_singleton] at hlen'
      obtain ⟨tail, c_end, htail, hterm_end⟩ := ih (crAllInitTotalMsgs uid - (sched.length + 1))
        (by omega) (sched ++ [target]) c' hmtr' (by rw [List.length_append, List.length_singleton])
      exact ⟨target :: tail, c_end, LTS.MTr.stepL htr htail, hterm_end⟩
  · intro sched cfg hmtr hterm
    obtain ⟨iStar, hiStar, huniq⟩ := huniq_max
    refine ⟨iStar, (crAllInit_isLeader_iff_max huid hmtr hterm iStar).mpr hiStar, fun j hj => ?_⟩
    exact huniq j ((crAllInit_isLeader_iff_max huid hmtr hterm j).mp hj)

/-! ### Tight worst-case and best-case message bounds -/

private theorem crAllInitTotalMsgs_le {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid) :
    crAllInitTotalMsgs uid ≤ n * (n + 1) / 2 := by
  have hhop_le : ∀ s : Fin n,
      crHops uid s ≤ 1 + (Finset.univ.filter fun j : Fin n => uid j < uid s).card := by
    intro s
    obtain ⟨h1, hn, _, hlt⟩ := crHops_spec uid s
    let passed := (Finset.Ico 1 (crHops uid s)).image fun k : ℕ => s + Fin.ofNat n k
    have hsub : passed ⊆ Finset.univ.filter fun j : Fin n => uid j < uid s := by
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨k, hk, rfl⟩
      rw [Finset.mem_Ico] at hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt k hk.1 hk.2⟩
    have hinj : Set.InjOn (fun k : ℕ => s + Fin.ofNat n k) (Finset.Ico 1 (crHops uid s)) :=
      fun k₁ hk₁ k₂ hk₂ => by
        simp only [Finset.coe_Ico, Set.mem_Ico] at hk₁ hk₂
        exact add_ofNat_fin_inj s (by omega) (by omega)
    have hcard : passed.card = crHops uid s - 1 := by
      rw [Finset.card_image_of_injOn hinj, Nat.card_Ico]
    have hle := Finset.card_le_card hsub
    omega
  have hsum_le : crAllInitTotalMsgs uid ≤
      n + ∑ s : Fin n, (Finset.univ.filter fun j : Fin n => uid j < uid s).card := by
    calc crAllInitTotalMsgs uid
        ≤ ∑ s : Fin n, (1 + (Finset.univ.filter fun j : Fin n => uid j < uid s).card) :=
          Finset.sum_le_sum fun s _ => hhop_le s
      _ = n + ∑ s : Fin n, (Finset.univ.filter fun j : Fin n => uid j < uid s).card := by
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  let Slt := ∑ s : Fin n, (Finset.univ.filter fun j : Fin n => uid j < uid s).card
  let Sgt := ∑ s : Fin n, (Finset.univ.filter fun j : Fin n => uid s < uid j).card
  have hswap : Slt = Sgt := by
    simp only [Slt, Sgt, card_filter_eq_sum_ite]
    exact Finset.sum_comm
  have hpart : ∀ s : Fin n,
      (Finset.univ.filter fun j : Fin n => uid j < uid s).card +
        (Finset.univ.filter fun j : Fin n => uid s < uid j).card + 1 = n := by
    intro s
    have hdisj1 : Disjoint (Finset.univ.filter fun j : Fin n => uid j < uid s)
        (Finset.univ.filter fun j : Fin n => uid s < uid j) :=
      Finset.disjoint_left.mpr fun j h1 h2 =>
        lt_asymm (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    have hnot_mem : s ∉ (Finset.univ.filter fun j : Fin n => uid j < uid s) ∪
        (Finset.univ.filter fun j : Fin n => uid s < uid j) := by
      simp only [Finset.mem_union, Finset.mem_filter, lt_self_iff_false, and_false, or_self,
        not_false_eq_true]
    have huniv : insert s ((Finset.univ.filter fun j : Fin n => uid j < uid s) ∪
        (Finset.univ.filter fun j : Fin n => uid s < uid j)) = Finset.univ := by
      ext j
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and, iff_true]
      rcases lt_trichotomy (uid j) (uid s) with hlt | heq | hgt
      · exact Or.inr (Or.inl hlt)
      · exact Or.inl (huid heq)
      · exact Or.inr (Or.inr hgt)
    have hcard := congrArg Finset.card huniv
    rw [Finset.card_insert_of_notMem hnot_mem, Finset.card_union_of_disjoint hdisj1,
      Finset.card_univ, Fintype.card_fin] at hcard
    omega
  have hdouble : 2 * Slt + n = n * n := by
    have hsum_part : ∑ s : Fin n,
        ((Finset.univ.filter fun j : Fin n => uid j < uid s).card +
          (Finset.univ.filter fun j : Fin n => uid s < uid j).card + 1) = ∑ _s : Fin n, n :=
      Finset.sum_congr rfl fun s _ => hpart s
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at hsum_part
    change Slt + Sgt + n = n * n at hsum_part
    omega
  have hmul : 2 * crAllInitTotalMsgs uid ≤ n * (n + 1) := by
    change crAllInitTotalMsgs uid ≤ n + Slt at hsum_le
    nlinarith
  omega

/-- A worst-case operational message-bound step for simultaneous all-initiator unidirectional FIFO
ring election (a step towards [Chang and Roberts][ChangRoberts1979], not the cited endpoint): in
every execution `(crLTS uid).MTr (crAllInit uid) sched cfg`, total messages transmitted satisfy
`crAllInitMsgs uid sched ≤ n * (n + 1) / 2`. -/
theorem crAllInit_messages_le {n : ℕ} [NeZero n] {U : Type*} [LinearOrder U]
    {uid : Fin n → U} (huid : Function.Injective uid) {sched : List (Fin n)} {cfg : CRConfig n U}
    (hmtr : (crLTS uid).MTr (crAllInit uid) sched cfg) :
    crAllInitMsgs uid sched ≤ n * (n + 1) / 2 :=
  (crExecMsgs_le_totalMsgs huid hmtr).2.trans (crAllInitTotalMsgs_le huid)

/-- A reverse-ordered evaluation step for `crAllInitTotalMsgs` (a step towards
[Chang and Roberts][ChangRoberts1979], not the cited endpoint): when identifiers decrease along the
clockwise traversal direction (`Fin.rev : Fin n → Fin n`), every node `s` sends its token
`n - s.val` hops to node `0`, giving `n * (n + 1) / 2` total messages. -/
theorem crAllInit_totalMsgs_rev_eq (n : ℕ) [NeZero n] :
    crAllInitTotalMsgs (Fin.rev : Fin n → Fin n) = n * (n + 1) / 2 := by
  have hhop : ∀ s : Fin n, crHops (Fin.rev : Fin n → Fin n) s = n - s.val := by
    intro s
    have hs_lt : s.val < n := s.isLt
    have hs_mem : s ∈ Finset.univ.filter (fun j : Fin n => Fin.rev s ≤ Fin.rev j) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ s, le_rfl⟩
    refine arcLen_eq_of_isFirst hs_mem (by omega) ?_ ?_
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def, Fin.val_rev]
      have hzero : (s + Fin.ofNat n (n - s.val)).val = 0 := by
        change (s.val + (n - s.val) % n) % n = 0
        rcases eq_or_ne s.val 0 with hs0 | hs_pos
        · rw [hs0, Nat.sub_zero, Nat.mod_self, Nat.zero_add, Nat.zero_mod]
        · have hmod : (n - s.val) % n = n - s.val := Nat.mod_eq_of_lt (by omega)
          rw [hmod, show s.val + (n - s.val) = n by omega, Nat.mod_self]
      rw [hzero]
      omega
    · intro k hk1 hk2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def, Fin.val_rev, not_le]
      rw [val_add_ofNat_fin s (by omega)]
      omega
  have hsum : crAllInitTotalMsgs (Fin.rev : Fin n → Fin n) = ∑ i ∈ Finset.range n, (n - i) := by
    rw [crAllInitTotalMsgs, ← Fin.sum_univ_eq_sum_range (fun i => n - i) n]
    exact Finset.sum_congr rfl fun s _ => hhop s
  rw [hsum]
  have hgauss : ∀ m : ℕ, 2 * (∑ i ∈ Finset.range m, (m - i)) = m * (m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ']
      have hsub : (∑ x ∈ Finset.range m, (m + 1 - (x + 1))) = ∑ x ∈ Finset.range m, (m - x) :=
        Finset.sum_congr rfl fun _ _ => Nat.succ_sub_succ_eq_sub _ _
      rw [hsub, Nat.sub_zero, mul_add]
      linarith
  have hm := hgauss n
  omega

/-- An increasing-order evaluation step for `crAllInitTotalMsgs` (a step towards
[Chang and Roberts][ChangRoberts1979], not the cited endpoint): when identifiers increase clockwise
(`id : Fin n → Fin n`), nodes `0, …, n - 2` travel `1` hop while node `n - 1` travels `n` hops,
giving `2 * n - 1` total messages. -/
theorem crAllInit_totalMsgs_id_eq (n : ℕ) [NeZero n] :
    crAllInitTotalMsgs (id : Fin n → Fin n) = 2 * n - 1 := by
  have hn_pos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hn_pos) with rfl | hn2
  · have h0 : crHops (id : Fin 1 → Fin 1) 0 = 1 := by
      obtain ⟨h1, hle, _, _⟩ := crHops_spec (id : Fin 1 → Fin 1) 0
      omega
    rw [crAllInitTotalMsgs, Fin.sum_univ_one, h0]
  · have hhop : ∀ s : Fin n,
        crHops (id : Fin n → Fin n) s = if s.val = n - 1 then n else 1 := by
      intro s
      split_ifs with hs
      · refine (crHops_eq_n_iff_max Function.injective_id s).mpr fun j => ?_
        simp only [id, Fin.le_def, hs]
        omega
      · have hs_lt : s.val < n := s.isLt
        have hs_mem : s ∈ Finset.univ.filter (fun j : Fin n => s ≤ j) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ s, le_rfl⟩
        refine arcLen_eq_of_isFirst hs_mem le_rfl ?_ fun k hk1 hk2 => by omega
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
        rw [val_add_ofNat_fin s (by omega)]
        omega
    let sLast : Fin n := ⟨n - 1, by omega⟩
    have hhop' : ∀ s : Fin n,
        crHops (id : Fin n → Fin n) s = 1 + if s = sLast then n - 1 else 0 := fun s => by
      simp only [hhop s, Fin.ext_iff, sLast]
      split_ifs <;> omega
    simp only [crAllInitTotalMsgs, hhop', Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    omega

/-! ### Exact `n H_n` average-case message complexity -/

/-- Structural search over `k = 0, 1, …, n - 1` for the smallest `k` with
`x - Fin.ofNat n k ∈ A`. -/
private def prevDistAux {n : ℕ} [NeZero n] (A : Finset (Fin n)) (x : Fin n) (k : ℕ) : ℕ → ℕ
  | 0 => k
  | fuel + 1 => if x - Fin.ofNat n k ∈ A then k else prevDistAux A x (k + 1) fuel

private def prevDist {n : ℕ} [NeZero n] (A : Finset (Fin n)) (x : Fin n) : ℕ :=
  prevDistAux A x 0 n

private def prevNode {n : ℕ} [NeZero n] (A : Finset (Fin n)) (x : Fin n) : Fin n :=
  x - Fin.ofNat n (prevDist A x)

private theorem prevDistAux_spec {n : ℕ} [NeZero n] {A : Finset (Fin n)} {x : Fin n} :
    ∀ fuel k, (∃ m, k ≤ m ∧ m < k + fuel ∧ x - Fin.ofNat n m ∈ A) →
      k ≤ prevDistAux A x k fuel ∧
      prevDistAux A x k fuel < k + fuel ∧
      x - Fin.ofNat n (prevDistAux A x k fuel) ∈ A ∧
      ∀ j, k ≤ j → j < prevDistAux A x k fuel → x - Fin.ofNat n j ∉ A := by
  intro fuel
  induction fuel with
  | zero =>
    intro k ⟨m, hkm, hlt, _⟩
    omega
  | succ f ih =>
    intro k ⟨m, hkm, hlt, hmA⟩
    simp only [prevDistAux]
    by_cases hhit : x - Fin.ofNat n k ∈ A
    · simp only [hhit, ↓reduceIte]
      exact ⟨le_rfl, by omega, trivial, fun j hj1 hj2 => by omega⟩
    · simp only [hhit, ↓reduceIte]
      have hgt : k + 1 ≤ m := by
        rcases eq_or_lt_of_le hkm with rfl | hgt
        · exact absurd hmA hhit
        · exact hgt
      obtain ⟨hlo, hhi, hmem, hmin⟩ := ih (k + 1) ⟨m, hgt, by omega, hmA⟩
      refine ⟨by omega, by omega, hmem, fun j hj1 hj2 => ?_⟩
      rcases eq_or_lt_of_le hj1 with rfl | hj_gt
      · exact hhit
      · exact hmin j hj_gt hj2

private theorem prevDist_spec {n : ℕ} [NeZero n] {A : Finset (Fin n)} (hA : A.Nonempty)
    (x : Fin n) :
    prevDist A x < n ∧ prevNode A x ∈ A ∧
      ∀ j, j < prevDist A x → x - Fin.ofNat n j ∉ A := by
  obtain ⟨a₀, ha₀⟩ := hA
  let m := (x - a₀).val
  have hm_mem : x - Fin.ofNat n m ∈ A := by
    rw [ofNat_val_eq_self (x - a₀), sub_sub_cancel]
    exact ha₀
  obtain ⟨_, hlt, hmem, hmin⟩ :=
    prevDistAux_spec n 0 ⟨m, Nat.zero_le m, by simp only [zero_add]; exact (x - a₀).isLt, hm_mem⟩
  exact ⟨by simpa only [prevDist, zero_add] using hlt, hmem, fun j hj => hmin j (Nat.zero_le j) hj⟩

/-- For any nonempty subset `A ⊆ Fin n`, the clockwise distances `arcLen A a` between consecutive
elements of `A` around the `n`-ring sum to `n`. -/
theorem sum_arcLen_eq {n : ℕ} [NeZero n] {A : Finset (Fin n)} (hA : A.Nonempty) :
    ∑ a ∈ A, arcLen A a = n := by
  have hmaps : ∀ x ∈ (Finset.univ : Finset (Fin n)), prevNode A x ∈ A :=
    fun x _ => (prevDist_spec hA x).2.1
  have hpart := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Finset.card_univ, Fintype.card_fin] at hpart
  conv_rhs => rw [hpart]
  refine Finset.sum_congr rfl fun a ha => ?_
  obtain ⟨ha1, han, hamem, hamin⟩ := arcLen_bounds_and_mem ha
  have hfib : Finset.univ.filter (fun x : Fin n => prevNode A x = a) =
      (Finset.range (arcLen A a)).image (fun k : ℕ => a + Fin.ofNat n k) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hprev
      obtain ⟨_, _, hk_min⟩ := prevDist_spec hA x
      refine ⟨prevDist A x, ?_, ?_⟩
      · by_contra hge
        have hd_le : arcLen A a ≤ prevDist A x := not_lt.mp hge
        let j := prevDist A x - arcLen A a
        have hj_lt : j < prevDist A x := by omega
        have hj_in : x - Fin.ofNat n j ∈ A := by
          have hx_eq : x = a + Fin.ofNat n (prevDist A x) := by
            rw [← hprev, prevNode, sub_add_cancel]
          have hcast : Fin.ofNat n (prevDist A x) = Fin.ofNat n (arcLen A a) + Fin.ofNat n j := by
            rw [← ofNat_add_fin, show arcLen A a + j = prevDist A x by omega]
          have hxj : x - Fin.ofNat n j = a + Fin.ofNat n (arcLen A a) := by
            rw [hx_eq, hcast, ← add_assoc, add_sub_cancel_right]
          rw [hxj]
          exact hamem
        exact hk_min j hj_lt hj_in
      · rw [← hprev, prevNode, add_comm, add_sub_cancel]
    · rintro ⟨k, hk_lt, rfl⟩
      let p := prevDist A (a + Fin.ofNat n k)
      obtain ⟨_, hp_mem, hp_min⟩ := prevDist_spec hA (a + Fin.ofNat n k)
      change a + Fin.ofNat n k - Fin.ofNat n p ∈ A at hp_mem
      have hpk : p = k := by
        rcases lt_trichotomy p k with hlt | heq | hgt
        · exfalso
          let d := k - p
          have hd_eq : a + Fin.ofNat n k - Fin.ofNat n p = a + Fin.ofNat n d := by
            have hcast : Fin.ofNat n k = Fin.ofNat n d + Fin.ofNat n p := by
              rw [← ofNat_add_fin, show d + p = k by omega]
            rw [hcast, ← add_assoc, add_sub_cancel_right]
          rw [hd_eq] at hp_mem
          exact hamin d (by omega) (by omega) hp_mem
        · exact heq
        · exfalso
          have hak : a + Fin.ofNat n k - Fin.ofNat n k ∈ A := by
            rwa [add_sub_cancel_right]
          exact hp_min k hgt hak
      simp only [prevNode, show prevDist A (a + Fin.ofNat n k) = k from hpk,
        add_sub_cancel_right]
  rw [hfib, Finset.card_image_of_injOn, Finset.card_range]
  intro k₁ hk₁ k₂ hk₂
  simp only [Finset.coe_range, Set.mem_Iio] at hk₁ hk₂
  exact add_ofNat_fin_inj a (by omega) (by omega)

/-- For `v ≤ u`, swapping `v` and `u` stabilizes `{w | v ≤ w}`: `v ≤ swap v u w ↔ v ≤ w`. -/
private theorem le_swap_iff_le {n : ℕ} {v u : Fin n} (hvu : v ≤ u) (w : Fin n) :
    v ≤ Equiv.swap v u w ↔ v ≤ w := by
  by_cases hwv : w = v
  · subst hwv
    rw [Equiv.swap_apply_left]
    exact ⟨fun _ => le_rfl, fun _ => hvu⟩
  · by_cases hwu : w = u
    · subst hwu
      rw [Equiv.swap_apply_right]
      exact ⟨fun _ => hvu, fun _ => le_rfl⟩
    · rw [Equiv.swap_apply_of_ne_of_ne hwv hwu]

/-- Exact cleared-denominator per-rank expectation: for the `r`-th largest UID `v`
(`r = n - v.val`), `r * ∑ σ, crHops (⇑σ) (σ.symm v) = n * n!`. -/
private theorem mul_sum_crHops_perm_eq {n : ℕ} [NeZero n] (v : Fin n) :
    (n - v.val) * (∑ σ : Equiv.Perm (Fin n), crHops (⇑σ) (σ.symm v)) =
      n * Nat.factorial n := by
  let S : Finset (Fin n) := Finset.univ.filter fun u : Fin n => v ≤ u
  have hS_card : S.card = n - v.val := by
    simp only [S, Finset.filter_le_eq_Ici, Fin.card_Ici]
  have hswap_sum : ∀ u ∈ S,
      (∑ σ : Equiv.Perm (Fin n), crHops (⇑σ) (σ.symm v)) =
      ∑ σ : Equiv.Perm (Fin n),
        arcLen (Finset.univ.filter fun i : Fin n => v ≤ σ i) (σ.symm u) := by
    intro u hu
    have hvu : v ≤ u := (Finset.mem_filter.mp hu).2
    let postSwap : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) :=
      { toFun := fun σ => σ.trans (Equiv.swap v u)
        invFun := fun σ => σ.trans (Equiv.swap v u)
        left_inv := fun σ => by ext x; simp only [Equiv.trans_apply, Equiv.swap_apply_self]
        right_inv := fun σ => by ext x; simp only [Equiv.trans_apply, Equiv.swap_apply_self] }
    rw [← Equiv.sum_comp postSwap]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hsymm : (postSwap σ).symm v = σ.symm u := by
      change (σ.trans (Equiv.swap v u)).symm v = σ.symm u
      rw [Equiv.symm_trans_apply, Equiv.symm_swap, Equiv.swap_apply_left]
    have happ : (postSwap σ) (σ.symm u) = v := by
      change (σ.trans (Equiv.swap v u)) (σ.symm u) = v
      rw [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.swap_apply_right]
    have hfilt :
        (Finset.univ.filter fun j : Fin n => (postSwap σ) ((postSwap σ).symm v) ≤ (postSwap σ) j) =
        Finset.univ.filter fun j : Fin n => v ≤ σ j := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hsymm, happ]
      exact le_swap_iff_le hvu (σ j)
    rw [crHops, hfilt, hsymm]
  calc (n - v.val) * (∑ σ : Equiv.Perm (Fin n), crHops (⇑σ) (σ.symm v))
      = S.card * (∑ σ : Equiv.Perm (Fin n), crHops (⇑σ) (σ.symm v)) := by rw [hS_card]
    _ = ∑ u ∈ S, ∑ σ : Equiv.Perm (Fin n), crHops (⇑σ) (σ.symm v) := by
          rw [Finset.sum_const, smul_eq_mul]
    _ = ∑ u ∈ S, ∑ σ : Equiv.Perm (Fin n),
          arcLen (Finset.univ.filter fun i : Fin n => v ≤ σ i) (σ.symm u) :=
          Finset.sum_congr rfl fun u hu => hswap_sum u hu
    _ = ∑ σ : Equiv.Perm (Fin n), ∑ u ∈ S,
          arcLen (Finset.univ.filter fun i : Fin n => v ≤ σ i) (σ.symm u) := Finset.sum_comm
    _ = ∑ σ : Equiv.Perm (Fin n),
          ∑ a ∈ (Finset.univ.filter fun i : Fin n => v ≤ σ i),
            arcLen (Finset.univ.filter fun i : Fin n => v ≤ σ i) a := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          refine Finset.sum_nbij (fun u => σ.symm u) ?_ ?_ ?_ fun _ _ => rfl
          · intro u hu
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
            simpa only [Equiv.apply_symm_apply] using hu
          · intro u₁ _ u₂ _ heq
            exact σ.symm.injective heq
          · intro a ha
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha
            exact ⟨σ a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, σ.symm_apply_apply a⟩
    _ = ∑ _σ : Equiv.Perm (Fin n), n := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          have hne : (Finset.univ.filter fun i : Fin n => v ≤ σ i).Nonempty :=
            ⟨σ.symm v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩⟩
          exact sum_arcLen_eq hne
    _ = n * Nat.factorial n := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            smul_eq_mul, mul_comm]

/-- An average-case step for simultaneous all-initiator unidirectional FIFO ring election (a step
towards [Chang and Roberts][ChangRoberts1979], not the cited endpoint): averaged uniformly over all
`n!` identifier permutations `σ : Equiv.Perm (Fin n)`, `crAllInitTotalMsgs` equals
`∑ k ∈ Finset.Icc 1 n, (n : ℚ) / k`. -/
theorem crAllInit_avg_totalMsgs_eq (n : ℕ) [NeZero n] :
    (∑ σ : Equiv.Perm (Fin n), (crAllInitTotalMsgs (⇑σ) : ℚ)) / (Nat.factorial n : ℚ) =
      ∑ k ∈ Finset.Icc 1 n, (n : ℚ) / k := by
  have hfact_ne : (Nat.factorial n : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hsum_swap : (∑ σ : Equiv.Perm (Fin n), (crAllInitTotalMsgs (⇑σ) : ℚ)) =
      ∑ v : Fin n, ∑ σ : Equiv.Perm (Fin n), (crHops (⇑σ) (σ.symm v) : ℚ) := by
    have h1 : ∀ σ : Equiv.Perm (Fin n),
        (crAllInitTotalMsgs (⇑σ) : ℚ) = ∑ v : Fin n, (crHops (⇑σ) (σ.symm v) : ℚ) := by
      intro σ
      rw [crAllInitTotalMsgs]
      push_cast
      exact (Equiv.sum_comp σ.symm fun i => (crHops (⇑σ) i : ℚ)).symm
    simp_rw [h1]
    exact Finset.sum_comm
  rw [hsum_swap, div_eq_mul_inv, Finset.sum_mul]
  simp_rw [← div_eq_mul_inv]
  have hterm : ∀ v : Fin n,
      (∑ σ : Equiv.Perm (Fin n), (crHops (⇑σ) (σ.symm v) : ℚ)) / (Nat.factorial n : ℚ) =
        (n : ℚ) / ((n - v.val : ℕ) : ℚ) := by
    intro v
    have hpos : (n - v.val : ℕ) ≠ 0 := by omega
    have hr_ne : ((n - v.val : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hpos
    have hnat := congrArg (Nat.cast (R := ℚ)) (mul_sum_crHops_perm_eq v)
    push_cast at hnat
    rw [div_eq_div_iff hfact_ne hr_ne]
    linarith
  simp_rw [hterm]
  refine Finset.sum_nbij (fun v : Fin n => n - v.val) ?_ ?_ ?_ fun _ _ => rfl
  · intro v _
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro v₁ _ v₂ _ heq
    dsimp only at heq
    have := v₁.isLt
    have := v₂.isLt
    ext
    omega
  · intro k hk
    simp only [Finset.coe_Icc, Set.mem_Icc] at hk
    exact ⟨⟨n - k, by omega⟩, Finset.mem_univ _, by dsimp only; omega⟩

end Cslib.Distributed.RingElection
