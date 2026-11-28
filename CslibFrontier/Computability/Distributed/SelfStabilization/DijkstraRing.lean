/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Distributed.SelfStabilization.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Dijkstra's `K`-state self-stabilizing token ring and enabled-move composite-ring symmetry step

This module formalizes Dijkstra's first self-stabilizing mutual-exclusion / token-circulation
protocol on a directed ring of `n` finite-state machines with `K` states per machine under a
central daemon ([Dijkstra][Dijkstra1974], pp. 643–644; manuscript [Dijkstra][Dijkstra1973]),
together with an original simultaneous atomic-subset transition model (`dijkstraDistRing`),
original sharp periodic converse counterexamples for both transition models, and scheduler-scoped
enabled-move symmetry steps towards the composite-ring impossibility argument of
[Dijkstra][Dijkstra1973] (`EWD391`).

In [Dijkstra][Dijkstra1974] (p. 644, left column), the ring consists of `N + 1` machines numbered
`0` through `N`; here `n` denotes the total ring size `N + 1`, indexed by `Fin n`:

* Bottom machine `0`: privileged iff `s 0 = s (0 - 1)` (`s 0 = s ⟨n - 1, _⟩`), moving to `s 0 + 1`
  (`(s 0 + 1) mod K` in `Fin K`).
* Normal machine `i > 0`: privileged iff `s i ≠ s (i - 1)`, moving to `s (i - 1)`.
* Legitimate configurations (`DijkstraLegitimate n K`): configurations in which *exactly one*
  machine `i : Fin n` is privileged.

[Dijkstra][Dijkstra1974] (p. 643) explicitly assumes a central daemon (`dijkstraRing n K`) and
excludes a distributed daemon, while the later section of [Dijkstra][Dijkstra1973] (`EWD391`)
discusses separate local reads and adjustments rather than atomic simultaneous updates from a
single pre-step state. Accordingly, `dijkstraDistRing n K` (which fires any nonempty subset `S` of
privileged machines atomically from the same old state) and its closure, convergence (`2 ≤ n ≤ K`),
and sharpness (`iff`) theorems are original results for the simultaneous atomic-subset model.

We establish:

1. *Deadlock-freedom* (`exists_dijkstraPrivileged`, `dijkstraRing_not_isTerminal`,
   `dijkstraDistRing_not_isTerminal`): every configuration has at least one privileged machine.
2. *Plateau characterization, closure, and round-robin circulation*
   (`dijkstraPrivilegedSet_eq_singleton_iff`, `dijkstraPrivilegedSet_step_of_eq_singleton`,
   `dijkstraRing_legitimate_closed`, `dijkstraDistRing_legitimate_closed`,
   `dijkstraRing_token_circulates`): legitimate configurations are constant or two-plateau step
   functions, central and simultaneous atomic-subset transitions coincide on legitimate states, and
   the unique privilege advances from `p` to `p + 1` on every step, visiting every machine once per
   `n` steps.
3. *Worst-case finite stabilization* (`dijkstraRing_selfStabilizing_of_pred_le`,
   `dijkstraRing_mTr_legitimate_of_le`, `dijkstraDistRing_mTr_legitimate_of_le`,
   `dijkstraDistRing_selfStabilizing_of_le`): under a central daemon, `n - 1 ≤ K` (`K ≥ N` with
   `2 ≤ n` and `2 ≤ K`, Note 1 on p. 644 of [Dijkstra][Dijkstra1974]) suffices for
   self-stabilization; in the original simultaneous atomic-subset model `dijkstraDistRing n K`,
   `2 ≤ n ≤ K` yields stabilization within `K * (n * (n - 1) / 2) + K` steps without fairness
   assumptions.
4. *Sharpness and necessary-and-sufficient bounds* (`dijkstraRing_not_selfStabilizing_of_lt_pred`,
   `dijkstraDistRing_not_selfStabilizing_of_lt`, `dijkstraRing_selfStabilizing_iff`,
   `dijkstraDistRing_selfStabilizing_iff`): original explicit periodic non-stabilizing executions
   show that for `2 ≤ n` and `2 ≤ K`, `dijkstraRing n K` is self-stabilizing iff `n - 1 ≤ K` and
   `dijkstraDistRing n K` is self-stabilizing iff `n ≤ K`.
5. *Enabled-move composite-ring symmetry steps*
   (`not_uniform_enabledMove_selfStabilizing_composite_ring`,
   `not_uniform_distEnabledMove_selfStabilizing_composite_ring`): scheduler-scoped steps towards
   [Dijkstra][Dijkstra1973] (`EWD391`) showing that on a composite ring of size `n = a * b`
   (`2 ≤ a`, `2 ≤ b`), no uniform deterministic ring protocol self-stabilizes to unique-privilege
   states under arbitrary enabled-move central (`π.centralLTS`) or simultaneous-subset (`π.distLTS`)
   schedules; EWD391's fair-command composite-ring endpoint (where every machine receives infinitely
   many adjustment commands, permitting no-effect commands) remains open (#7291).

## Main definitions

* `Cslib.Distributed.SelfStabilization.dijkstraPrivileged`,
  `Cslib.Distributed.SelfStabilization.dijkstraNextVal`,
  `Cslib.Distributed.SelfStabilization.dijkstraStep`,
  `Cslib.Distributed.SelfStabilization.dijkstraDistStep`: local privilege predicate, central
  single-machine update, and original simultaneous atomic-subset update for Dijkstra's `K`-state
  ring.
* `Cslib.Distributed.SelfStabilization.dijkstraRing`,
  `Cslib.Distributed.SelfStabilization.dijkstraDistRing`: central-daemon ([Dijkstra][Dijkstra1974],
  pp. 643–644) and original simultaneous atomic-subset labelled transition systems for Dijkstra's
  `K`-state ring.
* `Cslib.Distributed.SelfStabilization.dijkstraPrivilegedSet`,
  `Cslib.Distributed.SelfStabilization.DijkstraLegitimate`,
  `Cslib.Distributed.SelfStabilization.dijkstraTokenConfig`: privileged set, unique-privilege
  legitimate configurations, and canonical two-plateau configurations.
* `Cslib.Distributed.SelfStabilization.UniformRingProtocol`,
  `Cslib.Distributed.SelfStabilization.IsRingPeriodic`: anonymous deterministic local ring
  protocols and `a`-periodic configurations.

## Main results

* `Cslib.Distributed.SelfStabilization.exists_dijkstraPrivileged`,
  `Cslib.Distributed.SelfStabilization.dijkstraRing_not_isTerminal`,
  `Cslib.Distributed.SelfStabilization.dijkstraDistRing_not_isTerminal`: deadlock-freedom on every
  configuration.
* `Cslib.Distributed.SelfStabilization.dijkstraPrivilegedSet_eq_singleton_iff`,
  `Cslib.Distributed.SelfStabilization.dijkstraPrivilegedSet_tokenConfig`,
  `Cslib.Distributed.SelfStabilization.dijkstraPrivilegedSet_step_of_eq_singleton`: explicit
  two-plateau characterization of unique-privilege configurations and one-step clockwise rotation
  of the privilege from `p` to `p + 1`.
* `Cslib.Distributed.SelfStabilization.dijkstraRing_legitimate_closed`,
  `Cslib.Distributed.SelfStabilization.dijkstraDistRing_tr_iff_dijkstraRing_of_legitimate`,
  `Cslib.Distributed.SelfStabilization.dijkstraDistRing_legitimate_closed`,
  `Cslib.Distributed.SelfStabilization.dijkstraRing_token_circulates`: closure of
  `DijkstraLegitimate` under central and simultaneous atomic-subset transitions, their coincidence
  on legitimate configurations, and exact `n`-step round-robin token circulation.
* `Cslib.Distributed.SelfStabilization.dijkstraRing_selfStabilizing_of_pred_le`: central-daemon
  self-stabilization for `n - 1 ≤ K` ([Dijkstra][Dijkstra1974], p. 644, Note 1).
* `Cslib.Distributed.SelfStabilization.dijkstraDistRing_mTr_legitimate_of_le`,
  `Cslib.Distributed.SelfStabilization.dijkstraDistRing_selfStabilizing_of_le`,
  `Cslib.Distributed.SelfStabilization.dijkstraRing_mTr_legitimate_of_le`: original explicit
  `K * (n * (n - 1) / 2) + K` stabilization bounds for `2 ≤ n ≤ K` in the simultaneous
  atomic-subset and central-daemon models.
* `Cslib.Distributed.SelfStabilization.dijkstraRing_not_selfStabilizing_of_lt_pred`,
  `Cslib.Distributed.SelfStabilization.dijkstraDistRing_not_selfStabilizing_of_lt`: original
  explicit periodic non-stabilizing executions when `K + 1 < n` (central daemon) and `K < n`
  (simultaneous atomic-subset model).
* `Cslib.Distributed.SelfStabilization.dijkstraDistRing_selfStabilizing_iff`,
  `Cslib.Distributed.SelfStabilization.dijkstraRing_selfStabilizing_iff`: exact `n ≤ K` and
  `n - 1 ≤ K` characterizations for the simultaneous atomic-subset and central-daemon models
  (`2 ≤ n`, `2 ≤ K`).
* `UniformRingProtocol.card_privilegedSet_dvd_of_isRingPeriodic`,
  `UniformRingProtocol.isRingPeriodic_distStep`,
  `Cslib.Distributed.SelfStabilization.not_uniform_enabledMove_selfStabilizing_composite_ring`,
  `Cslib.Distributed.SelfStabilization.not_uniform_distEnabledMove_selfStabilizing_composite_ring`:
  `b`-divisor privilege count on `a`-periodic configurations and scheduler-scoped enabled-move
  steps towards anonymous composite-ring impossibility on sizes `n = a * b` (`2 ≤ a`, `2 ≤ b`).

## References

* [E. W. Dijkstra, *Self-stabilization in Spite of Distributed Control* (EWD391)][Dijkstra1973]
* [E. W. Dijkstra, *Self-stabilizing Systems in Spite of Distributed Control*][Dijkstra1974]
-/

public section

namespace Cslib.Distributed.SelfStabilization

open Cslib

/-! ### Modular `Fin` arithmetic helpers and Dijkstra's `K`-state token ring -/

private theorem fin_sub_one_eq {n : ℕ} [NeZero n] (i : Fin n) :
    i - 1 = if h : i.val = 0 then
      ⟨n - 1, Nat.sub_lt (NeZero.pos n) Nat.one_pos⟩
    else
      ⟨i.val - 1, Nat.lt_trans (Nat.sub_lt (Nat.pos_of_ne_zero h) Nat.one_pos) i.isLt⟩ := by
  rcases n with _ | _ | m
  · exact absurd rfl (NeZero.ne 0)
  · ext; simp
  · ext
    rcases i with ⟨_ | k, hk⟩
    · simp [Fin.sub_def]
    · simp only [Nat.succ_ne_zero, ↓reduceDIte, Fin.sub_def, Fin.val_one, Nat.add_sub_cancel]
      have : m + 1 + (k + 1) = (m + 1 + 1) + k := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

private theorem fin_add_one_eq {n : ℕ} [NeZero n] (i : Fin n) :
    i + 1 = if h : i.val + 1 = n then
      ⟨0, NeZero.pos n⟩
    else
      ⟨i.val + 1, Nat.lt_of_le_of_ne (Nat.succ_le_of_lt i.isLt) h⟩ := by
  ext
  rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  split_ifs with h
  · simp [h]
  · exact Nat.mod_eq_of_lt (by omega)

private theorem fin_add_one_mod {K : ℕ} [NeZero K] (x : Fin K) :
    x + 1 = ⟨(x.val + 1) % K, Nat.mod_lt _ (NeZero.pos K)⟩ :=
  Fin.ext (by simp [Fin.val_add])

private theorem fin_add_sub_one {n : ℕ} [NeZero n] (i : Fin n) :
    i + 1 - 1 = i := by
  rw [fin_add_one_eq]
  split_ifs with hlast
  · rw [fin_sub_one_eq]; simp [← hlast]
  · rw [fin_sub_one_eq]; simp

private theorem fin_add_one_ne_self {K : ℕ} [NeZero K] (hK : 2 ≤ K) (x : Fin K) :
    x + 1 ≠ x := by
  intro h
  have hval := congrArg Fin.val h
  rw [fin_add_one_mod] at hval
  dsimp only at hval
  rcases Nat.lt_or_ge (x.val + 1) K with hx | hx
  · rw [Nat.mod_eq_of_lt hx] at hval; omega
  · rw [show x.val + 1 = K by omega, Nat.mod_self] at hval; omega

/-- Machine `i` is privileged in configuration `s` iff `s 0 = s (0 - 1)` when `i = 0`, and
`s i ≠ s (i - 1)` when `i > 0` ([Dijkstra][Dijkstra1974], p. 644, "Solution with K-state
Machines"). -/
@[expose] def dijkstraPrivileged {n K : ℕ} [NeZero n] (s : Fin n → Fin K) (i : Fin n) : Prop :=
  if i.val = 0 then s i = s (i - 1) else s i ≠ s (i - 1)

instance {n K : ℕ} [NeZero n] (s : Fin n → Fin K) (i : Fin n) :
    Decidable (dijkstraPrivileged s i) :=
  inferInstanceAs (Decidable (if i.val = 0 then s i = s (i - 1) else s i ≠ s (i - 1)))

/-- Next local value of machine `i` when firing: `s 0 + 1` (`(s 0 + 1) mod K`) for bottom machine
`0`, and `s (i - 1)` for `i > 0` ([Dijkstra][Dijkstra1974], p. 644). -/
@[expose] def dijkstraNextVal {n K : ℕ} [NeZero n] [NeZero K]
    (s : Fin n → Fin K) (i : Fin n) : Fin K :=
  if i.val = 0 then s i + 1 else s (i - 1)

/-- Single-machine configuration update when machine `i` moves. -/
@[expose] def dijkstraStep {n K : ℕ} [NeZero n] [NeZero K]
    (s : Fin n → Fin K) (i : Fin n) : Fin n → Fin K :=
  Function.update s i (dijkstraNextVal s i)

/-- Original simultaneous atomic-subset configuration update: every machine in `S` evaluates
`dijkstraNextVal` on the same pre-step configuration `s` and updates simultaneously. -/
@[expose] def dijkstraDistStep {n K : ℕ} [NeZero n] [NeZero K]
    (s : Fin n → Fin K) (S : Finset (Fin n)) : Fin n → Fin K :=
  fun j => if j ∈ S then dijkstraNextVal s j else s j

/-- Central-daemon labelled transition system for Dijkstra's `K`-state ring on `Fin n`
([Dijkstra][Dijkstra1974], pp. 643–644): each transition selects one privileged machine `i`. -/
@[expose] def dijkstraRing (n K : ℕ) [NeZero n] [NeZero K] :
    LTS (Fin n → Fin K) (Fin n) where
  Tr s i s' := dijkstraPrivileged s i ∧ s' = dijkstraStep s i

/-- Original simultaneous atomic-subset labelled transition system for Dijkstra's `K`-state ring on
`Fin n`: each transition selects a nonempty set `S` of privileged machines and updates them
atomically from the pre-step configuration `s` (distinct from [Dijkstra][Dijkstra1974], p. 643,
which excludes a distributed daemon, and from the separate read/adjust discussion in
[Dijkstra][Dijkstra1973]). -/
@[expose] def dijkstraDistRing (n K : ℕ) [NeZero n] [NeZero K] :
    LTS (Fin n → Fin K) (Finset (Fin n)) where
  Tr s S s' := S.Nonempty ∧ (∀ i ∈ S, dijkstraPrivileged s i) ∧ s' = dijkstraDistStep s S

/-- Set of privileged machines in configuration `s`. -/
@[expose] def dijkstraPrivilegedSet {n K : ℕ} [NeZero n]
    (s : Fin n → Fin K) : Finset (Fin n) :=
  Finset.univ.filter (dijkstraPrivileged s)

/-- Legitimate configurations of Dijkstra's token ring: configurations in which *exactly one*
machine is privileged ([Dijkstra][Dijkstra1974], p. 644). -/
@[expose] def DijkstraLegitimate (n K : ℕ) [NeZero n] : Set (Fin n → Fin K) :=
  { s | (dijkstraPrivilegedSet s).card = 1 }

/-- Canonical two-plateau configuration placing the unique privilege at `p` with base value `c`. -/
@[expose] def dijkstraTokenConfig (n K : ℕ) [NeZero K]
    (p : Fin n) (c : Fin K) : Fin n → Fin K :=
  fun j => if p.val = 0 then c else if j.val < p.val then c + 1 else c

@[simp]
theorem dijkstraDistStep_singleton {n K : ℕ} [NeZero n] [NeZero K]
    (s : Fin n → Fin K) (i : Fin n) :
    dijkstraDistStep s {i} = dijkstraStep s i := by
  funext j
  by_cases hji : j = i
  · subst hji; simp [dijkstraDistStep, dijkstraStep]
  · simp [dijkstraDistStep, dijkstraStep, hji]

/-- A central-daemon step of machine `i` coincides with the singleton distributed-daemon step
`{i}`. -/
theorem dijkstraRing_tr_iff_distRing_singleton {n K : ℕ} [NeZero n] [NeZero K]
    (s : Fin n → Fin K) (i : Fin n) (s' : Fin n → Fin K) :
    (dijkstraRing n K).Tr s i s' ↔ (dijkstraDistRing n K).Tr s {i} s' := by
  simp [dijkstraRing, dijkstraDistRing]

private theorem dijkstraRing_mTr_to_distRing {n K : ℕ} [NeZero n] [NeZero K]
    {s s' : Fin n → Fin K} {μs : List (Fin n)}
    (hmtr : (dijkstraRing n K).MTr s μs s') :
    (dijkstraDistRing n K).MTr s (μs.map fun i => {i}) s' := by
  induction hmtr with
  | refl => exact .refl
  | stepL htr _ ih =>
    exact .stepL ((dijkstraRing_tr_iff_distRing_singleton _ _ _).mp htr) ih

/-! ### Deadlock-freedom -/

private theorem eq_zero_of_unprivileged_prefix {n K : ℕ} [NeZero n]
    {s : Fin n → Fin K} {m : ℕ} (hm : m ≤ n)
    (hunpriv : ∀ i : Fin n, 0 < i.val → i.val < m → ¬ dijkstraPrivileged s i) :
    ∀ k (hk : k < m), s ⟨k, Nat.lt_of_lt_of_le hk hm⟩ = s 0 := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hkn : k + 1 < n := Nat.lt_of_lt_of_le hk hm
    have hnot := hunpriv ⟨k + 1, hkn⟩ (Nat.succ_pos k) hk
    simp only [dijkstraPrivileged, Nat.succ_ne_zero, ↓reduceIte, fin_sub_one_eq,
      ↓reduceDIte, Nat.add_sub_cancel, not_not] at hnot
    exact hnot.trans (ih (Nat.lt_of_succ_lt hk))

/-- Every ring configuration has at least one privileged machine: if no machine `i > 0` differs
from its left neighbour, then all machines equal `s 0`, so bottom machine `0` is privileged. -/
theorem exists_dijkstraPrivileged {n K : ℕ} [NeZero n] (s : Fin n → Fin K) :
    ∃ i : Fin n, dijkstraPrivileged s i := by
  by_cases hall : ∀ i : Fin n, 0 < i.val → ¬ dijkstraPrivileged s i
  · refine ⟨0, ?_⟩
    have hconst := eq_zero_of_unprivileged_prefix le_rfl fun i hi _ => hall i hi
    have hz : (0 : Fin n).val = 0 := rfl
    simp only [dijkstraPrivileged, hz, ↓reduceIte, fin_sub_one_eq, ↓reduceDIte]
    exact (hconst (n - 1) (Nat.sub_lt (NeZero.pos n) Nat.one_pos)).symm
  · push Not at hall
    obtain ⟨i, _, hi⟩ := hall
    exact ⟨i, hi⟩

/-- Dijkstra's `K`-state ring has no terminal configurations under a central daemon. -/
theorem dijkstraRing_not_isTerminal {n K : ℕ} [NeZero n] [NeZero K]
    (s : Fin n → Fin K) : ¬ (dijkstraRing n K).IsTerminal s := by
  intro hterm
  obtain ⟨i, hi⟩ := exists_dijkstraPrivileged s
  exact hterm i (dijkstraStep s i) ⟨hi, rfl⟩

/-- Dijkstra's `K`-state ring has no terminal configurations in the simultaneous atomic-subset
transition system `dijkstraDistRing n K`. -/
theorem dijkstraDistRing_not_isTerminal {n K : ℕ} [NeZero n] [NeZero K]
    (s : Fin n → Fin K) : ¬ (dijkstraDistRing n K).IsTerminal s := by
  intro hterm
  obtain ⟨i, hi⟩ := exists_dijkstraPrivileged s
  exact hterm {i} (dijkstraDistStep s {i}) ⟨Finset.singleton_nonempty i, by simp [hi], rfl⟩

/-! ### Plateau characterization, closure, and round-robin circulation -/

/-- Explicit characterization of configurations whose unique privileged machine is `p`:
constant configurations when `p = 0`, and two-plateau configurations jumping at `p` when `p > 0`. -/
theorem dijkstraPrivilegedSet_eq_singleton_iff {n K : ℕ} [NeZero n]
    (s : Fin n → Fin K) (p : Fin n) :
    dijkstraPrivilegedSet s = {p} ↔
      (if p.val = 0 then
        ∀ j : Fin n, s j = s 0
      else
        s p ≠ s 0 ∧ (∀ j : Fin n, j.val < p.val → s j = s 0) ∧
          (∀ j : Fin n, p.val ≤ j.val → s j = s p)) := by
  have hzero_eq : (⟨0, NeZero.pos n⟩ : Fin n) = 0 := rfl
  constructor
  · intro heq
    have hmem : ∀ i : Fin n, dijkstraPrivileged s i ↔ i = p := by
      intro i
      simpa [dijkstraPrivilegedSet] using Finset.ext_iff.mp heq i
    split_ifs with hp0
    · have hconst := eq_zero_of_unprivileged_prefix le_rfl fun i hi _ hpriv => by
        have hip := (hmem i).mp hpriv
        omega
      intro j
      exact hconst j.val j.isLt
    · have hlt := eq_zero_of_unprivileged_prefix (Nat.le_of_lt p.isLt) fun i _ hil hpriv => by
        have hip := (hmem i).mp hpriv
        exact Nat.ne_of_lt hil (congrArg Fin.val hip)
      have hp_priv : dijkstraPrivileged s p := (hmem p).mpr rfl
      simp only [dijkstraPrivileged, hp0, ↓reduceIte, fin_sub_one_eq, ↓reduceDIte] at hp_priv
      have hp_sub_lt : p.val - 1 < p.val :=
        Nat.sub_lt (Nat.pos_of_ne_zero hp0) Nat.one_pos
      have hp_pred : s ⟨p.val - 1, Nat.lt_trans hp_sub_lt p.isLt⟩ = s 0 :=
        hlt (p.val - 1) hp_sub_lt
      have hge : ∀ d (hd : p.val + d < n), s ⟨p.val + d, hd⟩ = s p := by
        intro d
        induction d with
        | zero => intro _; rfl
        | succ d ih =>
          intro hd
          have hne_p : (⟨p.val + (d + 1), hd⟩ : Fin n) ≠ p := by
            intro h
            have hv : p.val + (d + 1) = p.val := congrArg Fin.val h
            omega
          have hnz : p.val + (d + 1) ≠ 0 := by omega
          have hnot : ¬ dijkstraPrivileged s ⟨p.val + (d + 1), hd⟩ := mt (hmem _).mp hne_p
          simp only [dijkstraPrivileged, hnz, ↓reduceIte, fin_sub_one_eq, ↓reduceDIte,
            not_not] at hnot
          have hsub : (⟨p.val + (d + 1) - 1,
              Nat.lt_trans (Nat.sub_lt (Nat.pos_of_ne_zero hnz) Nat.one_pos) hd⟩ : Fin n) =
              ⟨p.val + d, Nat.lt_of_succ_lt hd⟩ := by ext; dsimp only; omega
          rw [hsub] at hnot
          exact hnot.trans (ih (Nat.lt_of_succ_lt hd))
      refine ⟨fun h => hp_priv (h.trans hp_pred.symm), fun j hj => hlt j.val hj, fun j hj => ?_⟩
      have hj_lt := j.isLt
      have hj' : (⟨p.val + (j.val - p.val), by omega⟩ : Fin n) = j := by ext; dsimp only; omega
      rw [← hj']
      exact hge (j.val - p.val) (by omega)
  · intro hplat
    ext i
    simp only [dijkstraPrivilegedSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    split_ifs at hplat with hp0
    · have hp_eq : p = 0 := by ext; exact hp0
      rw [hp_eq]
      by_cases hi0 : i.val = 0
      · have hi_eq : i = 0 := by ext; exact hi0
        simp [dijkstraPrivileged, hi_eq, hplat]
      · have hi_ne : i ≠ 0 := fun h => hi0 (by rw [h]; rfl)
        simp [dijkstraPrivileged, hi0, hi_ne, hplat]
    · obtain ⟨hne, hlt, hge⟩ := hplat
      by_cases hi0 : i.val = 0
      · have hi_ne_p : i ≠ p := fun h => hp0 (h ▸ hi0)
        have hi_eq0 : s i = s 0 := hlt i (by omega)
        have hlast : s (i - 1) = s p := by
          apply hge
          simp only [fin_sub_one_eq, hi0, ↓reduceDIte]
          omega
        simp only [dijkstraPrivileged, hi0, ↓reduceIte, hi_eq0, hlast, hi_ne_p, iff_false]
        exact hne.symm
      · by_cases hip : i = p
        · subst hip
          simp only [dijkstraPrivileged, hi0, ↓reduceIte, iff_true]
          have hleft : (i - 1).val < i.val := by
            simp only [fin_sub_one_eq, hi0, ↓reduceDIte]
            omega
          rw [hlt (i - 1) hleft]
          exact hne
        · simp only [dijkstraPrivileged, hi0, ↓reduceIte, hip, iff_false, not_not]
          by_cases hilt : i.val < p.val
          · have hleft : (i - 1).val < p.val := by
              simp only [fin_sub_one_eq, hi0, ↓reduceDIte]
              omega
            rw [hlt i hilt, hlt (i - 1) hleft]
          · have higt : p.val < i.val := by
              have : i.val ≠ p.val := fun h => hip (Fin.ext h)
              omega
            have hleft : p.val ≤ (i - 1).val := by
              simp only [fin_sub_one_eq, hi0, ↓reduceDIte]
              omega
            rw [hge i (Nat.le_of_lt higt), hge (i - 1) hleft]

/-- Every canonical plateau configuration `dijkstraTokenConfig n K p c` has `p` as its unique
privileged machine when `2 ≤ K`. -/
theorem dijkstraPrivilegedSet_tokenConfig {n K : ℕ} [NeZero n] [NeZero K]
    (hK : 2 ≤ K) (p : Fin n) (c : Fin K) :
    dijkstraPrivilegedSet (dijkstraTokenConfig n K p c) = {p} := by
  rw [dijkstraPrivilegedSet_eq_singleton_iff]
  have hzero_val : (0 : Fin n).val = 0 := rfl
  split_ifs with hp0
  · intro j
    simp [dijkstraTokenConfig, hp0]
  · have hpos : 0 < p.val := Nat.pos_of_ne_zero hp0
    refine ⟨?_, ?_, ?_⟩
    · simp only [dijkstraTokenConfig, hp0, ↓reduceIte, lt_irrefl, hzero_val, hpos, ne_eq]
      exact (fin_add_one_ne_self hK c).symm
    · intro j hj
      simp [dijkstraTokenConfig, hp0, hj, hpos]
    · intro j hj
      have hnot_lt : ¬ j.val < p.val := Nat.not_lt.mpr hj
      simp [dijkstraTokenConfig, hp0, hnot_lt]

/-- Firing the unique privileged machine `p` in a legitimate configuration transfers the unique
privilege to `p + 1` ([Dijkstra][Dijkstra1974], p. 644). -/
theorem dijkstraPrivilegedSet_step_of_eq_singleton {n K : ℕ} [NeZero n] [NeZero K]
    (hK : 2 ≤ K) {s : Fin n → Fin K} {p : Fin n}
    (hs : dijkstraPrivilegedSet s = {p}) :
    dijkstraPrivilegedSet (dijkstraStep s p) = {p + 1} := by
  have hplat := (dijkstraPrivilegedSet_eq_singleton_iff s p).mp hs
  rw [dijkstraPrivilegedSet_eq_singleton_iff]
  have hz : (0 : Fin n).val = 0 := rfl
  by_cases hp0 : p.val = 0
  · simp only [hp0, ↓reduceIte] at hplat
    have hp_eq0 : p = 0 := Fin.ext hp0
    subst hp_eq0
    by_cases hn1 : n = 1
    · have hr0 : ((0 : Fin n) + 1).val = 0 := by
        simp [fin_add_one_eq, hn1]
      simp only [hr0, ↓reduceIte]
      intro j
      have hj0 : j = 0 := Fin.ext (by have := j.isLt; omega)
      rw [hj0]
    · have h1ne : 0 + 1 ≠ n := by omega
      have hr_val : ((0 : Fin n) + 1).val = 1 := by
        simp [fin_add_one_eq, h1ne]
      simp only [hr_val, Nat.one_ne_zero, ↓reduceIte]
      have hs'0 : dijkstraStep s 0 0 = s 0 + 1 := by
        simp [dijkstraStep, dijkstraNextVal]
      have hs'_pos : ∀ j : Fin n, 0 < j.val → dijkstraStep s 0 j = s 0 := by
        intro j hj
        have hjne : j ≠ 0 := fun h => by rw [h] at hj; exact Nat.lt_irrefl 0 hj
        rw [dijkstraStep, Function.update_of_ne hjne, hplat j]
      refine ⟨?_, ?_, ?_⟩
      · rw [hs'0, hs'_pos (0 + 1) (by omega)]
        exact (fin_add_one_ne_self hK (s 0)).symm
      · intro j hj
        have hj0 : j = 0 := Fin.ext (by omega)
        rw [hj0]
      · intro j hj
        rw [hs'_pos j (by omega), hs'_pos (0 + 1) (by omega)]
  · simp only [hp0, ↓reduceIte] at hplat
    obtain ⟨hne, hlt, hge⟩ := hplat
    have hp_pos : 0 < p.val := Nat.pos_of_ne_zero hp0
    have hnext_p : dijkstraNextVal s p = s 0 := by
      simp only [dijkstraNextVal, hp0, ↓reduceIte]
      apply hlt
      simp only [fin_sub_one_eq, hp0, ↓reduceDIte]
      omega
    have hs'_lt : ∀ j : Fin n, j.val ≤ p.val → dijkstraStep s p j = s 0 := by
      intro j hj
      by_cases hjp : j = p
      · rw [hjp, dijkstraStep, Function.update_self, hnext_p]
      · have hjlt : j.val < p.val :=
          Nat.lt_of_le_of_ne hj fun h => hjp (Fin.ext h)
        rw [dijkstraStep, Function.update_of_ne hjp, hlt j hjlt]
    have hs'_gt : ∀ j : Fin n, p.val < j.val → dijkstraStep s p j = s p := by
      intro j hj
      have hjp : j ≠ p := fun h => Nat.ne_of_gt hj (congrArg Fin.val h)
      rw [dijkstraStep, Function.update_of_ne hjp, hge j (Nat.le_of_lt hj)]
    by_cases hlast : p.val + 1 = n
    · have hr0 : (p + 1).val = 0 := by simp [fin_add_one_eq, hlast]
      simp only [hr0, ↓reduceIte]
      intro j
      have hj_lt := j.isLt
      rw [hs'_lt j (by omega), hs'_lt 0 (by rw [hz]; omega)]
    · have hr_val : (p + 1).val = p.val + 1 := by simp [fin_add_one_eq, hlast]
      simp only [hr_val, Nat.succ_ne_zero, ↓reduceIte]
      refine ⟨?_, ?_, ?_⟩
      · rw [hs'_gt (p + 1) (by omega), hs'_lt 0 (by rw [hz]; omega)]
        exact hne
      · intro j hj
        rw [hs'_lt j (by omega), hs'_lt 0 (by rw [hz]; omega)]
      · intro j hj
        rw [hs'_gt j (by omega), hs'_gt (p + 1) (by omega)]

private theorem eq_of_privileged_of_eq_singleton {n K : ℕ} [NeZero n] {s : Fin n → Fin K}
    {p i : Fin n} (hs : dijkstraPrivilegedSet s = {p}) (hi : dijkstraPrivileged s i) : i = p := by
  rw [← Finset.mem_singleton, ← hs]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩

/-- Closure of `DijkstraLegitimate n K` under central-daemon transitions (`2 ≤ K`). -/
theorem dijkstraRing_legitimate_closed {n K : ℕ} [NeZero n] [NeZero K] (hK : 2 ≤ K)
    {s s' : Fin n → Fin K} {i : Fin n}
    (hs : s ∈ DijkstraLegitimate n K) (htr : (dijkstraRing n K).Tr s i s') :
    s' ∈ DijkstraLegitimate n K := by
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hs
  obtain ⟨hpriv, rfl⟩ := htr
  obtain rfl := eq_of_privileged_of_eq_singleton hp hpriv
  simp [DijkstraLegitimate, dijkstraPrivilegedSet_step_of_eq_singleton hK hp]

/-- On `DijkstraLegitimate n K`, simultaneous atomic-subset transitions (`dijkstraDistRing`)
coincide with central-daemon transitions (`dijkstraRing`) since only one machine is privileged. -/
theorem dijkstraDistRing_tr_iff_dijkstraRing_of_legitimate {n K : ℕ} [NeZero n] [NeZero K]
    {s s' : Fin n → Fin K} (hs : s ∈ DijkstraLegitimate n K) (S : Finset (Fin n)) :
    (dijkstraDistRing n K).Tr s S s' ↔ ∃ i, S = {i} ∧ (dijkstraRing n K).Tr s i s' := by
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hs
  constructor
  · rintro ⟨hne, hpriv, rfl⟩
    obtain rfl : S = {p} := hne.subset_singleton_iff.mp fun i hi =>
      Finset.mem_singleton.mpr (eq_of_privileged_of_eq_singleton hp (hpriv i hi))
    exact ⟨p, rfl, hpriv p (Finset.mem_singleton_self p), dijkstraDistStep_singleton s p⟩
  · rintro ⟨i, rfl, htr⟩
    exact (dijkstraRing_tr_iff_distRing_singleton s i s').mp htr

/-- Original closure theorem for the simultaneous atomic-subset model: `DijkstraLegitimate n K` is
closed under `dijkstraDistRing n K` transitions when `2 ≤ K`. -/
theorem dijkstraDistRing_legitimate_closed {n K : ℕ} [NeZero n] [NeZero K] (hK : 2 ≤ K)
    {s s' : Fin n → Fin K} {S : Finset (Fin n)}
    (hs : s ∈ DijkstraLegitimate n K) (htr : (dijkstraDistRing n K).Tr s S s') :
    s' ∈ DijkstraLegitimate n K := by
  obtain ⟨i, _, htr'⟩ := (dijkstraDistRing_tr_iff_dijkstraRing_of_legitimate hs S).mp htr
  exact dijkstraRing_legitimate_closed hK hs htr'

/-- Round-robin token circulation: along any multistep execution from a legitimate configuration
with unique privilege at `p`, the `k`-th step fires `(p + k) mod n` and the final configuration has
unique privilege at `(p + μs.length) mod n`. In particular, over any `n` consecutive steps every
machine fires once. -/
theorem dijkstraRing_token_circulates {n K : ℕ} [NeZero n] [NeZero K] (hK : 2 ≤ K)
    {s s' : Fin n → Fin K} {p : Fin n} {μs : List (Fin n)}
    (hs : dijkstraPrivilegedSet s = {p}) (hmtr : (dijkstraRing n K).MTr s μs s') :
    dijkstraPrivilegedSet s' =
        {⟨(p.val + μs.length) % n, Nat.mod_lt _ (NeZero.pos n)⟩} ∧
      ∀ k (hk : k < μs.length),
        μs[k] = ⟨(p.val + k) % n, Nat.mod_lt _ (NeZero.pos n)⟩ := by
  induction hmtr generalizing p with
  | refl =>
    refine ⟨?_, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
    simpa [Nat.mod_eq_of_lt p.isLt] using hs
  | @stepL s₁ i s₂ μs s₃ htr _ ih =>
    obtain ⟨hpriv, rfl⟩ := htr
    obtain rfl := eq_of_privileged_of_eq_singleton hs hpriv
    obtain ⟨hfinal, hsteps⟩ := ih (dijkstraPrivilegedSet_step_of_eq_singleton hK hs)
    have hr_mod : ∀ m, ((i + 1).val + m) % n = (i.val + (m + 1)) % n := fun m => by
      simp only [fin_add_one_mod, Nat.mod_add_mod]; ring_nf
    refine ⟨?_, fun k hk => ?_⟩
    · rw [hfinal]; congr 1; ext; exact hr_mod μs.length
    · rcases k with _ | k
      · simp [Nat.mod_eq_of_lt i.isLt]
      · rw [List.getElem_cons_succ, hsteps k (Nat.succ_lt_succ_iff.mp hk)]; ext; exact hr_mod k

/-! ### Discrepancy potential and worst-case finite stabilization -/

private def dijkstraPotential {n K : ℕ} [NeZero n] (s : Fin n → Fin K) : ℕ :=
  ∑ i : Fin n, if 0 < i.val ∧ s i ≠ s (i - 1) then n - i.val else 0

private theorem dijkstraPotential_le {n K : ℕ} [NeZero n] (s : Fin n → Fin K) :
    dijkstraPotential s ≤ n * (n - 1) / 2 := by
  let rev : Fin n → Fin n := fun i =>
    ⟨if i.val = 0 then 0 else n - i.val, by split_ifs <;> omega⟩
  have hbij : Function.Bijective rev := by
    refine (Fintype.bijective_iff_injective_and_card rev).mpr ⟨fun i j hij => ?_, rfl⟩
    have hval := congrArg Fin.val hij
    simp only [rev] at hval
    ext
    split_ifs at hval <;> omega
  have hle : dijkstraPotential s ≤ ∑ i : Fin n, (rev i).val := by
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [rev]
    split_ifs <;> omega
  have hsum : ∑ i : Fin n, (rev i).val = ∑ j : Fin n, j.val :=
    Fintype.sum_bijective rev hbij _ _ fun _ => rfl
  have hrange : 2 * ∑ j : Fin n, j.val = n * (n - 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => k) n, Nat.mul_comm 2, Finset.sum_range_id_mul_two]
  omega

private theorem dijkstraPotential_distStep_le {n K : ℕ} [NeZero n] [NeZero K]
    {s s' : Fin n → Fin K} {S : Finset (Fin n)}
    (htr : (dijkstraDistRing n K).Tr s S s') (h0 : (0 : Fin n) ∉ S) :
    dijkstraPotential s' + S.card ≤ dijkstraPotential s := by
  obtain ⟨_, hpriv, rfl⟩ := htr
  let d : (Fin n → Fin K) → ℕ → ℕ := fun u k =>
    if hk : 0 < k ∧ k < n then
      if u ⟨k, hk.2⟩ ≠ u (⟨k, hk.2⟩ - 1) then 1 else 0
    else 0
  let inS : ℕ → ℕ := fun k =>
    if hk : k < n then (if (⟨k, hk⟩ : Fin n) ∈ S then 1 else 0) else 0
  have hinS0 : inS 0 = 0 := by
    have h0eq : (⟨0, NeZero.pos n⟩ : Fin n) = 0 := rfl
    simp [inS, NeZero.pos n, h0eq, h0]
  have hpt : ∀ k < n, d (dijkstraDistStep s S) k + inS k ≤ d s k + inS (k - 1) := by
    intro k hkn
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · simp [d]
    have hk_sub : k - 1 < n := by omega
    let ik : Fin n := ⟨k, hkn⟩
    let ik_prev : Fin n := ⟨k - 1, hk_sub⟩
    have hleft_eq : ik - 1 = ik_prev := by
      rw [fin_sub_one_eq]
      have hik_nz : k ≠ 0 := by omega
      simp [ik, ik_prev, hik_nz]
    have hd_s : d s k = if s ik ≠ s ik_prev then 1 else 0 := by
      simp [d, hk_pos, hkn, ik, hleft_eq]
    have hd_s' : d (dijkstraDistStep s S) k =
        if dijkstraDistStep s S ik ≠ dijkstraDistStep s S ik_prev then 1 else 0 := by
      simp [d, hk_pos, hkn, ik, hleft_eq]
    have hinS_k : inS k = if ik ∈ S then 1 else 0 := by simp [inS, hkn, ik]
    have hinS_prev : inS (k - 1) = if ik_prev ∈ S then 1 else 0 := by
      simp [inS, hk_sub, ik_prev]
    rw [hd_s, hd_s', hinS_k, hinS_prev]
    by_cases hik : ik ∈ S
    · have hp_ik := hpriv ik hik
      have hik_nz : ik.val ≠ 0 := by simp [ik]; omega
      simp only [dijkstraPrivileged, hik_nz, ↓reduceIte, hleft_eq] at hp_ik
      have hstep_ik : dijkstraDistStep s S ik = s ik_prev := by
        simp [dijkstraDistStep, hik, dijkstraNextVal, hik_nz, hleft_eq]
      by_cases hprev : ik_prev ∈ S
      · simp only [hik, hprev, ↓reduceIte, hp_ik, ne_eq, not_false_eq_true]
        split_ifs <;> omega
      · have hstep_prev : dijkstraDistStep s S ik_prev = s ik_prev := by
          simp [dijkstraDistStep, hprev]
        simp [hik, hprev, hp_ik, hstep_ik, hstep_prev]
    · have hstep_ik : dijkstraDistStep s S ik = s ik := by simp [dijkstraDistStep, hik]
      by_cases hprev : ik_prev ∈ S
      · simp only [hik, hprev, ↓reduceIte]
        split_ifs <;> omega
      · have hstep_prev : dijkstraDistStep s S ik_prev = s ik_prev := by
          simp [dijkstraDistStep, hprev]
        simp [hik, hprev, hstep_ik, hstep_prev]
  have hphi_eq : ∀ u : Fin n → Fin K,
      dijkstraPotential u = ∑ k ∈ Finset.range n, (n - k) * d u k := by
    intro u
    rw [dijkstraPotential, ← Fin.sum_univ_eq_sum_range (fun k => (n - k) * d u k) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi0 : 0 < i.val
    · by_cases hne : u i = u (i - 1) <;> simp [d, hi0, i.isLt, hne]
    · simp [d, hi0]
  have hcard_eq : S.card = ∑ k ∈ Finset.range n, inS k := by
    rw [← Fin.sum_univ_eq_sum_range inS n]
    simp [inS]
  have htele : ∀ (N : ℕ) (f : ℕ → ℕ), f 0 = 0 →
      ∑ k ∈ Finset.range N, (N - k) * f (k - 1) + ∑ k ∈ Finset.range N, f k =
        ∑ k ∈ Finset.range N, (N - k) * f k := by
    rintro (_ | m) f hf
    · simp
    rw [Finset.sum_range_succ', Finset.sum_range_succ _ m, Finset.sum_range_succ _ m]
    simp only [Nat.add_sub_add_right, Nat.add_sub_cancel, Nat.zero_sub, hf, mul_zero, add_zero,
      show m + 1 - m = 1 by omega, one_mul, ← add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [show m + 1 - k = m - k + 1 by have := Finset.mem_range.mp hk; omega]
    ring
  have hwsum := Finset.sum_le_sum fun k (hk : k ∈ Finset.range n) =>
    Nat.mul_le_mul_left (n - k) (hpt k (Finset.mem_range.mp hk))
  simp only [mul_add, Finset.sum_add_distrib, ← hphi_eq] at hwsum
  have := htele n inS hinS0
  omega

private def bottomSteps {n : ℕ} [NeZero n] (μs : List (Finset (Fin n))) : ℕ :=
  (μs.filter fun S => decide ((0 : Fin n) ∈ S)).length

private theorem bottomSteps_append {n : ℕ} [NeZero n] (l₁ l₂ : List (Finset (Fin n))) :
    bottomSteps (l₁ ++ l₂) = bottomSteps l₁ + bottomSteps l₂ := by
  simp [bottomSteps, List.filter_append]

private theorem mTr_length_le_of_bottomSteps {n K : ℕ} [NeZero n] [NeZero K]
    {s s' : Fin n → Fin K} {μs : List (Finset (Fin n))}
    (hmtr : (dijkstraDistRing n K).MTr s μs s') :
    μs.length + dijkstraPotential s' ≤
      dijkstraPotential s + bottomSteps μs * (n * (n - 1) / 2 + 1) := by
  induction hmtr with
  | refl => simp [bottomSteps]
  | @stepL s₁ S s₂ μs s₃ htr _ ih =>
    by_cases h0 : (0 : Fin n) ∈ S
    · have hb : bottomSteps (S :: μs) = bottomSteps μs + 1 := by simp [bottomSteps, h0]
      have hphi := dijkstraPotential_le s₂
      rw [List.length_cons, hb, Nat.add_mul, one_mul]
      omega
    · have hb : bottomSteps (S :: μs) = bottomSteps μs := by simp [bottomSteps, h0]
      have hcard : 1 ≤ S.card := Finset.card_pos.mpr htr.1
      have hdec := dijkstraPotential_distStep_le htr h0
      rw [List.length_cons, hb]
      omega

private def modDist {K : ℕ} (x v : Fin K) : ℕ :=
  (v.val + K - x.val) % K

private def OnlyZeroPrefix {n K : ℕ} (v : Fin K) (s : Fin n → Fin K) : Prop :=
  ∃ m : ℕ, 1 ≤ m ∧ m < n ∧
    (∀ i : Fin n, i.val < m → s i = v) ∧
    (∀ i : Fin n, m ≤ i.val → s i ≠ v)

private theorem not_legit_bottomSteps_eq_zero_of_onlyZeroPrefix {n K : ℕ} [NeZero n] [NeZero K]
    (hK : 2 ≤ K) (v : Fin K) {s s' : Fin n → Fin K} {μs : List (Finset (Fin n))}
    (hmtr : (dijkstraDistRing n K).MTr s μs s')
    (hpref : OnlyZeroPrefix v s)
    (hs' : s' ∉ DijkstraLegitimate n K) :
    bottomSteps μs = 0 := by
  induction hmtr with
  | refl => rfl
  | @stepL s₁ S s₂ μs s₃ htr hmtr' ih =>
    obtain ⟨m, hm1, hmn, hlt, hge⟩ := hpref
    have hs₁0 : s₁ 0 = v := hlt 0 (by change 0 < m; omega)
    have hs₁_last : s₁ (0 - 1) ≠ v := by
      apply hge
      have hzero : (0 : Fin n).val = 0 := rfl
      simp only [fin_sub_one_eq, hzero, ↓reduceDIte]
      omega
    have hnot_priv0 : ¬ dijkstraPrivileged s₁ 0 := by
      have hzero : (0 : Fin n).val = 0 := rfl
      simp only [dijkstraPrivileged, hzero, ↓reduceIte]
      intro heq
      exact hs₁_last (heq.symm.trans hs₁0)
    have h0 : (0 : Fin n) ∉ S := fun h => hnot_priv0 (htr.2.1 0 h)
    have hb_cons : bottomSteps (S :: μs) = bottomSteps μs := by simp [bottomSteps, h0]
    rw [hb_cons]
    obtain ⟨_, hpriv, rfl⟩ := htr
    have hlt_keep : ∀ i : Fin n, i.val < m → dijkstraDistStep s₁ S i = v := by
      intro i hi
      by_cases hi0 : i.val = 0
      · have hi_eq0 : i = 0 := Fin.ext hi0
        rw [hi_eq0]
        simp [dijkstraDistStep, h0, hs₁0]
      · have hnot_priv : ¬ dijkstraPrivileged s₁ i := by
          simp only [dijkstraPrivileged, hi0, ↓reduceIte, not_not]
          have hleft : (i - 1).val < m := by
            simp only [fin_sub_one_eq, hi0, ↓reduceDIte]
            omega
          rw [hlt i hi, hlt (i - 1) hleft]
        have hiS : i ∉ S := fun h => hnot_priv (hpriv i h)
        simp [dijkstraDistStep, hiS, hlt i hi]
    let im : Fin n := ⟨m, hmn⟩
    by_cases him : im ∈ S
    · have hm_val : dijkstraDistStep s₁ S im = v := by
        have hm_nz : im.val ≠ 0 := by simp [im]; omega
        simp only [dijkstraDistStep, him, ↓reduceIte, dijkstraNextVal, hm_nz]
        apply hlt
        simp only [fin_sub_one_eq, hm_nz, ↓reduceDIte, im]
        omega
      have hgt_ne : ∀ i : Fin n, m + 1 ≤ i.val → dijkstraDistStep s₁ S i ≠ v := by
        intro i hi
        by_cases hiS : i ∈ S
        · have hi_nz : i.val ≠ 0 := by omega
          simp only [dijkstraDistStep, hiS, ↓reduceIte, dijkstraNextVal, hi_nz]
          apply hge
          simp only [fin_sub_one_eq, hi_nz, ↓reduceDIte]
          omega
        · simp only [dijkstraDistStep, hiS, ↓reduceIte]
          exact hge i (by omega)
      by_cases hmn' : m + 1 = n
      · exfalso
        have hconst : ∀ i : Fin n, dijkstraDistStep s₁ S i = v := by
          intro i
          by_cases hil : i.val < m
          · exact hlt_keep i hil
          · have hieq : i = im := by ext; simp [im]; omega
            rw [hieq, hm_val]
        have hleg : dijkstraDistStep s₁ S ∈ DijkstraLegitimate n K := by
          have hps : dijkstraPrivilegedSet (dijkstraDistStep s₁ S) = {0} := by
            rw [dijkstraPrivilegedSet_eq_singleton_iff]
            simp [hconst]
          simp [DijkstraLegitimate, hps]
        have hclosed : ∀ u₁ μs' u₂, (dijkstraDistRing n K).MTr u₁ μs' u₂ →
            u₁ ∈ DijkstraLegitimate n K → u₂ ∈ DijkstraLegitimate n K :=
          (dijkstraDistRing n K).mtrInv_of_trInv fun _ _ _ h hp =>
            dijkstraDistRing_legitimate_closed hK hp h
        exact hs' (hclosed _ _ _ hmtr' hleg)
      · exact ih ⟨m + 1, by omega, by omega, fun i hi => by
          by_cases hil : i.val < m
          · exact hlt_keep i hil
          · have hieq : i = im := by ext; simp [im]; omega
            rw [hieq, hm_val], hgt_ne⟩ hs'
    · have hge_ne : ∀ i : Fin n, m ≤ i.val → dijkstraDistStep s₁ S i ≠ v := by
        intro i hi
        by_cases hi_eq : i.val = m
        · have hieq : i = im := Fin.ext hi_eq
          rw [hieq]
          simp [dijkstraDistStep, him, hge im (by simp [im])]
        · by_cases hiS : i ∈ S
          · have hi_nz : i.val ≠ 0 := by omega
            simp only [dijkstraDistStep, hiS, ↓reduceIte, dijkstraNextVal, hi_nz]
            apply hge
            simp only [fin_sub_one_eq, hi_nz, ↓reduceDIte]
            omega
          · simp [dijkstraDistStep, hiS, hge i hi]
      exact ih ⟨m, hm1, hmn, hlt_keep, hge_ne⟩ hs'

private theorem not_legit_bottomSteps_le_of_avoids {n K : ℕ} [NeZero n] [NeZero K]
    (hn : 2 ≤ n) (hK : 2 ≤ K) (v : Fin K) {s s' : Fin n → Fin K}
    {μs : List (Finset (Fin n))}
    (hmtr : (dijkstraDistRing n K).MTr s μs s')
    (hav : ∀ i : Fin n, s i ≠ v)
    (hs' : s' ∉ DijkstraLegitimate n K) :
    bottomSteps μs ≤ modDist (s 0) v := by
  induction hmtr with
  | refl => simp [bottomSteps]
  | @stepL s₁ S s₂ μs s₃ htr hmtr' ih =>
    obtain ⟨_, _, rfl⟩ := htr
    have hpos_ne : ∀ i : Fin n, 0 < i.val → dijkstraDistStep s₁ S i ≠ v := by
      intro i hi
      by_cases hiS : i ∈ S
      · have hi_nz : i.val ≠ 0 := by omega
        simp only [dijkstraDistStep, hiS, ↓reduceIte, dijkstraNextVal, hi_nz]
        exact hav (i - 1)
      · simp [dijkstraDistStep, hiS, hav i]
    by_cases h0 : (0 : Fin n) ∈ S
    · have hs₂0 : dijkstraDistStep s₁ S 0 = s₁ 0 + 1 := by
        simp [dijkstraDistStep, h0, dijkstraNextVal]
      have hb_cons : bottomSteps (S :: μs) = bottomSteps μs + 1 := by simp [bottomSteps, h0]
      have hdist_pos : 0 < modDist (s₁ 0) v := by
        simp only [modDist]
        have hne_val : (s₁ 0).val ≠ v.val := fun h => hav 0 (Fin.ext h)
        have hlt1 := (s₁ 0).isLt
        have hlt2 := v.isLt
        by_cases hcmp : (s₁ 0).val ≤ v.val
        · have : v.val + K - (s₁ 0).val = K + (v.val - (s₁ 0).val) := by omega
          rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
          omega
        · rw [Nat.mod_eq_of_lt (by omega)]
          omega
      by_cases hhit : s₁ 0 + 1 = v
      · have hpref : OnlyZeroPrefix v (dijkstraDistStep s₁ S) := by
          refine ⟨1, le_rfl, hn, fun i hi => ?_, fun i hi => hpos_ne i (by omega)⟩
          have hi0 : i = 0 := Fin.ext (show i.val = 0 by omega)
          rw [hi0, hs₂0, hhit]
        have hb0 := not_legit_bottomSteps_eq_zero_of_onlyZeroPrefix hK v hmtr' hpref hs'
        omega
      · have hav' : ∀ i : Fin n, dijkstraDistStep s₁ S i ≠ v := by
          intro i
          by_cases hi0 : i.val = 0
          · have hi_eq0 : i = 0 := Fin.ext hi0
            rw [hi_eq0, hs₂0]
            exact hhit
          · exact hpos_ne i (Nat.pos_of_ne_zero hi0)
        have hdist_dec : modDist (s₁ 0 + 1) v + 1 = modDist (s₁ 0) v := by
          simp only [modDist, fin_add_one_mod]
          have hlt1 := (s₁ 0).isLt
          have hlt2 := v.isLt
          have hne0 : (s₁ 0).val ≠ v.val := fun h => hav 0 (Fin.ext h)
          have hne_succ : ((s₁ 0).val + 1) % K ≠ v.val :=
            fun h => hhit (by rw [fin_add_one_mod]; exact Fin.ext h)
          by_cases hwrap : (s₁ 0).val + 1 = K
          · rw [hwrap, Nat.mod_self, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
            have : v.val + K - (s₁ 0).val = v.val + 1 := by omega
            rw [this, Nat.mod_eq_of_lt (by omega)]
          · have hlt_succ : (s₁ 0).val + 1 < K := by omega
            rw [Nat.mod_eq_of_lt hlt_succ]
            by_cases hcmp : (s₁ 0).val < v.val
            · have h1 : v.val + K - ((s₁ 0).val + 1) = K + (v.val - (s₁ 0).val - 1) := by omega
              have h2 : v.val + K - (s₁ 0).val = K + (v.val - (s₁ 0).val) := by omega
              have hne_succ' : (s₁ 0).val + 1 ≠ v.val := by
                rwa [Nat.mod_eq_of_lt hlt_succ] at hne_succ
              rw [h1, h2, Nat.add_mod_left, Nat.add_mod_left,
                Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
              omega
            · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
              omega
        have ih' := ih hav' hs'
        rw [hs₂0] at ih'
        omega
    · have hav' : ∀ i : Fin n, dijkstraDistStep s₁ S i ≠ v := by
        intro i
        by_cases hi0 : i.val = 0
        · have hi_eq0 : i = 0 := Fin.ext hi0
          rw [hi_eq0]
          simp [dijkstraDistStep, h0, hav 0]
        · exact hpos_ne i (Nat.pos_of_ne_zero hi0)
      have hs₂0 : dijkstraDistStep s₁ S 0 = s₁ 0 := by simp [dijkstraDistStep, h0]
      have ih' := ih hav' hs'
      rw [hs₂0] at ih'
      have hb_cons : bottomSteps (S :: μs) = bottomSteps μs := by simp [bottomSteps, h0]
      omega

private theorem refute_not_legit_of_missing_pos {n K : ℕ} [NeZero n] [NeZero K]
    (hn : 2 ≤ n) (hK : 2 ≤ K) (w : Fin K) {u s' : Fin n → Fin K}
    {μs : List (Finset (Fin n))}
    (hw : ∀ j : Fin n, 0 < j.val → u j ≠ w)
    (hmtr : (dijkstraDistRing n K).MTr u μs s')
    (hs' : s' ∉ DijkstraLegitimate n K)
    (hb : K ≤ bottomSteps μs) : False := by
  by_cases hu0 : u 0 = w
  · have hpref : OnlyZeroPrefix w u := by
      refine ⟨1, le_rfl, hn, fun i hi => ?_, fun i hi => hw i (by omega)⟩
      have hi0 : i = 0 := Fin.ext (show i.val = 0 by omega)
      rw [hi0, hu0]
    have hb0 := not_legit_bottomSteps_eq_zero_of_onlyZeroPrefix hK w hmtr hpref hs'
    omega
  · have hav : ∀ j : Fin n, u j ≠ w := fun j => by
      by_cases hj0 : j.val = 0
      · have hjeq : j = 0 := Fin.ext hj0
        rwa [hjeq]
      · exact hw j (Nat.pos_of_ne_zero hj0)
    have hbub := not_legit_bottomSteps_le_of_avoids hn hK w hmtr hav hs'
    have hlt : modDist (u 0) w < K := Nat.mod_lt _ (NeZero.pos K)
    omega

private theorem exists_missing_of_priv_zero {n K : ℕ} [NeZero n]
    (hn : 2 ≤ n) (hnK : n ≤ K) {s : Fin n → Fin K}
    (hpriv0 : dijkstraPrivileged s 0) :
    ∃ v : Fin K, ∀ i : Fin n, s i ≠ v := by
  have hz : (0 : Fin n).val = 0 := rfl
  simp only [dijkstraPrivileged, hz, ↓reduceIte] at hpriv0
  let last : Fin n := (0 : Fin n) - 1
  have hlast_ne0 : last ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [last, fin_sub_one_eq, hz, ↓reduceDIte] at hv
    omega
  have himg_sub : Finset.univ.image s ⊆ (Finset.univ.erase last).image s := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    by_cases hil : i = last
    · rw [hil, ← hpriv0]
      exact Finset.mem_image.mpr ⟨0, Finset.mem_erase.mpr ⟨hlast_ne0.symm, Finset.mem_univ _⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_erase.mpr ⟨hil, Finset.mem_univ _⟩, rfl⟩
  have hcard_lt : (Finset.univ.image s).card < (Finset.univ : Finset (Fin K)).card := by
    have h1 := Finset.card_le_card himg_sub
    have h2 : ((Finset.univ.erase last).image s).card ≤ (Finset.univ.erase last).card :=
      Finset.card_image_le
    simp only [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      at h2 ⊢
    omega
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt
  exact ⟨v, fun i hi => hv (hi ▸ Finset.mem_image_of_mem s (Finset.mem_univ i))⟩

private theorem mTr_split_first_bottom {n K : ℕ} [NeZero n] [NeZero K]
    {s s' : Fin n → Fin K} {μs : List (Finset (Fin n))}
    (hmtr : (dijkstraDistRing n K).MTr s μs s') (hb : 1 ≤ bottomSteps μs) :
    ∃ s₁ S₁ s₂ μs₁ μs₂,
      μs = μs₁ ++ S₁ :: μs₂ ∧
      bottomSteps μs₁ = 0 ∧
      (0 : Fin n) ∈ S₁ ∧
      (dijkstraDistRing n K).MTr s μs₁ s₁ ∧
      (dijkstraDistRing n K).Tr s₁ S₁ s₂ ∧
      (dijkstraDistRing n K).MTr s₂ μs₂ s' := by
  induction hmtr with
  | refl => simp [bottomSteps] at hb
  | @stepL s₀ S s₁ μs' s' htr hmtr' ih =>
    by_cases h0 : (0 : Fin n) ∈ S
    · exact ⟨s₀, S, s₁, [], μs', rfl, rfl, h0, .refl, htr, hmtr'⟩
    · have hb' : 1 ≤ bottomSteps μs' := by simpa [bottomSteps, h0] using hb
      obtain ⟨u₁, S₁, u₂, μs₁, μs₂, rfl, hb₁, h0₁, hm₁, htr₁, hm₂⟩ := ih hb'
      refine ⟨u₁, S₁, u₂, S :: μs₁, μs₂, rfl, ?_, h0₁, .stepL htr hm₁, htr₁, hm₂⟩
      rw [show bottomSteps (S :: μs₁) = bottomSteps μs₁ by simp [bottomSteps, h0]]
      exact hb₁

/-- Original explicit worst-case convergence bound in the simultaneous atomic-subset model
`dijkstraDistRing n K`: when `2 ≤ n ≤ K`, every execution of length at least
`K * (n * (n - 1) / 2) + K` ends in `DijkstraLegitimate n K`, with zero fairness assumptions. -/
theorem dijkstraDistRing_mTr_legitimate_of_le {n K : ℕ} [NeZero n] [NeZero K]
    (hn : 2 ≤ n) (hnK : n ≤ K) {s₀ s' : Fin n → Fin K} {μs : List (Finset (Fin n))}
    (hmtr : (dijkstraDistRing n K).MTr s₀ μs s')
    (hlen : K * (n * (n - 1) / 2) + K ≤ μs.length) :
    s' ∈ DijkstraLegitimate n K := by
  have hK : 2 ≤ K := le_trans hn hnK
  by_contra hs'
  have hlen_ub := mTr_length_le_of_bottomSteps hmtr
  have hphi_ub := dijkstraPotential_le s₀
  have hb_ge_K : K ≤ bottomSteps μs := by
    by_contra hlt
    have := Nat.mul_le_mul_right (n * (n - 1) / 2 + 1) (Nat.succ_le_of_lt (not_le.mp hlt))
    nlinarith
  obtain ⟨s₁, S₁, s₂, μs₁, μs₂, rfl, hb₁, h0₁, _, htr₁, hmtr₂⟩ :=
    mTr_split_first_bottom hmtr (by omega)
  have hb_tail : bottomSteps (S₁ :: μs₂) = bottomSteps (μs₁ ++ S₁ :: μs₂) := by
    rw [bottomSteps_append, hb₁, zero_add]
  obtain ⟨v, hav⟩ := exists_missing_of_priv_zero hn hnK (htr₁.2.1 0 h0₁)
  have hb_ub :=
    not_legit_bottomSteps_le_of_avoids hn hK v (.stepL htr₁ hmtr₂) hav hs'
  have hdist_lt : modDist (s₁ 0) v < K := Nat.mod_lt _ (NeZero.pos K)
  omega

/-- Original convergence theorem for the simultaneous atomic-subset model: whenever `2 ≤ n` and
`n ≤ K`, `dijkstraDistRing n K` is self-stabilizing to `DijkstraLegitimate n K`. -/
theorem dijkstraDistRing_selfStabilizing_of_le {n K : ℕ} [NeZero n] [NeZero K]
    (hn : 2 ≤ n) (hnK : n ≤ K) :
    SelfStabilizing (dijkstraDistRing n K) (DijkstraLegitimate n K) :=
  SelfStabilizing.of_mTr_bound (K * (n * (n - 1) / 2) + K)
    (fun _ hs _ _ htr => dijkstraDistRing_legitimate_closed (le_trans hn hnK) hs htr)
    dijkstraDistRing_not_isTerminal
    (fun _ _ _ hmtr hlen => dijkstraDistRing_mTr_legitimate_of_le hn hnK hmtr hlen)

/-- Original explicit worst-case convergence bound under a central daemon when `2 ≤ n ≤ K`
(quantitative refinement of [Dijkstra][Dijkstra1974], p. 644). -/
theorem dijkstraRing_mTr_legitimate_of_le {n K : ℕ} [NeZero n] [NeZero K]
    (hn : 2 ≤ n) (hnK : n ≤ K) {s₀ s' : Fin n → Fin K} {μs : List (Fin n)}
    (hmtr : (dijkstraRing n K).MTr s₀ μs s')
    (hlen : K * (n * (n - 1) / 2) + K ≤ μs.length) :
    s' ∈ DijkstraLegitimate n K :=
  dijkstraDistRing_mTr_legitimate_of_le hn hnK (dijkstraRing_mTr_to_distRing hmtr)
    (by simpa using hlen)

private theorem dijkstraRing_selfStabilizing_of_le {n K : ℕ} [NeZero n] [NeZero K]
    (hn : 2 ≤ n) (hnK : n ≤ K) :
    SelfStabilizing (dijkstraRing n K) (DijkstraLegitimate n K) :=
  SelfStabilizing.of_subLTS (dijkstraDistRing_selfStabilizing_of_le hn hnK)
    (fun _ i _ htr => ⟨{i}, (dijkstraRing_tr_iff_distRing_singleton _ i _).mp htr⟩)
    dijkstraRing_not_isTerminal

/-- Note 1 of [Dijkstra][Dijkstra1974] (p. 644): under a central daemon, `n - 1 ≤ K` (`K ≥ N` for
`n = N + 1` machines, with `2 ≤ n` and `2 ≤ K`) suffices for self-stabilization, within at most
`(K + 1) * (n * (n - 1) / 2) + (K + 1)` steps. -/
theorem dijkstraRing_selfStabilizing_of_pred_le {n K : ℕ} [NeZero n] [NeZero K]
    (hn : 2 ≤ n) (hK : 2 ≤ K) (hnK : n - 1 ≤ K) :
    SelfStabilizing (dijkstraRing n K) (DijkstraLegitimate n K) := by
  by_cases hle : n ≤ K
  · exact dijkstraRing_selfStabilizing_of_le hn hle
  · have hnk_eq : n = K + 1 := by omega
    refine SelfStabilizing.of_mTr_bound ((K + 1) * (n * (n - 1) / 2) + (K + 1))
      (fun _ hs _ _ htr => dijkstraRing_legitimate_closed hK hs htr)
      dijkstraRing_not_isTerminal ?_
    intro s₀ μs s' hmtr hlen
    by_contra hs'
    have hdist := dijkstraRing_mTr_to_distRing hmtr
    have hlen_ub := mTr_length_le_of_bottomSteps hdist
    have hphi_ub := dijkstraPotential_le s₀
    have hb_ge : K + 1 ≤ bottomSteps (μs.map fun i => {i}) := by
      by_contra hlt
      have := Nat.mul_le_mul_right (n * (n - 1) / 2 + 1) (Nat.succ_le_of_lt (not_le.mp hlt))
      simp only [List.length_map] at hlen_ub
      nlinarith
    obtain ⟨s₁, S₁, s₂, μs₁, μs₂, hmap_eq, hb₁, h0₁, _, htr₁, hmtr₂⟩ :=
      mTr_split_first_bottom hdist (by omega)
    have hS₁ : S₁ = {0} := by
      have hmem : S₁ ∈ μs.map fun i => {i} := by
        rw [hmap_eq]
        exact List.mem_append_right _ List.mem_cons_self
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hmem
      have hi0 : 0 = i := Finset.mem_singleton.mp h0₁
      rw [← hi0]
    subst hS₁
    have hb_m₂ : K ≤ bottomSteps μs₂ := by
      have hsplit_b : bottomSteps (μs₁ ++ ({0} : Finset (Fin n)) :: μs₂) =
          bottomSteps μs₂ + 1 := by
        rw [bottomSteps_append, hb₁, zero_add]
        simp [bottomSteps]
      rw [hmap_eq] at hb_ge
      omega
    have htr₀ : (dijkstraRing n K).Tr s₁ 0 s₂ :=
      (dijkstraRing_tr_iff_distRing_singleton s₁ 0 s₂).mpr htr₁
    obtain ⟨hpriv₀, rfl⟩ := htr₀
    let s₂' := dijkstraStep s₁ 0
    let posSet : Finset (Fin n) := Finset.univ.erase 0
    have hcard_pos : posSet.card = K := by
      simp [posSet, Finset.card_erase_of_mem (Finset.mem_univ _), hnk_eq]
    by_cases hsurj : posSet.image s₂' = Finset.univ
    · cases hmtr₂ with
      | refl =>
        simp only [bottomSteps, List.filter_nil, List.length_nil] at hb_m₂
        omega
      | @stepL _ S₂ s₃ μs₃ _ htr₂ hmtr₃ =>
        have hS₂_sing : ∃ i : Fin n, S₂ = {i} := by
          have hmem : S₂ ∈ μs.map fun i => {i} := by
            rw [hmap_eq]
            exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp hmem
          exact ⟨i, rfl⟩
        obtain ⟨i, rfl⟩ := hS₂_sing
        have htr_i : (dijkstraRing n K).Tr s₂' i s₃ :=
          (dijkstraRing_tr_iff_distRing_singleton s₂' i s₃).mpr htr₂
        obtain ⟨hpriv_i, rfl⟩ := htr_i
        have hz : (0 : Fin n).val = 0 := rfl
        simp only [dijkstraPrivileged, hz, ↓reduceIte] at hpriv₀
        have hi_ne0 : i ≠ 0 := by
          intro hi0
          subst hi0
          have hs₂'0 : s₂' 0 = s₁ 0 + 1 := by simp [s₂', dijkstraStep, dijkstraNextVal]
          have hs₂'_last : s₂' (0 - 1) = s₁ 0 := by
            have hne : (0 : Fin n) - 1 ≠ 0 := by
              intro h
              have hv := congrArg Fin.val h
              simp only [fin_sub_one_eq, hz, ↓reduceDIte] at hv
              omega
            change dijkstraStep s₁ 0 (0 - 1) = s₁ 0
            rw [dijkstraStep, Function.update_of_ne hne, hpriv₀.symm]
          simp only [dijkstraPrivileged, hz, ↓reduceIte, hs₂'0, hs₂'_last] at hpriv_i
          exact fin_add_one_ne_self hK (s₁ 0) hpriv_i
        have h0not_i : (0 : Fin n) ∉ ({i} : Finset (Fin n)) := by simp [Ne.symm hi_ne0]
        have hb_m₃ : K ≤ bottomSteps μs₃ := by
          simpa [bottomSteps, h0not_i] using hb_m₂
        have hinj : Set.InjOn s₂' (posSet : Set (Fin n)) := by
          have hcard_img : (posSet.image s₂').card = posSet.card := by
            rw [hsurj, Finset.card_univ, Fintype.card_fin, hcard_pos]
          exact Finset.injOn_of_card_image_eq hcard_img
        have hw : ∀ j : Fin n, 0 < j.val → dijkstraStep s₂' i j ≠ s₂' i := by
          intro j hj
          by_cases hji : j = i
          · subst hji
            have hi_nz : j.val ≠ 0 := fun h => hi_ne0 (Fin.ext h)
            simp only [dijkstraPrivileged, hi_nz, ↓reduceIte] at hpriv_i
            simp only [dijkstraStep, Function.update_self, dijkstraNextVal, hi_nz, ↓reduceIte]
            exact hpriv_i.symm
          · rw [dijkstraStep, Function.update_of_ne hji]
            intro heq
            have hj_mem : j ∈ (posSet : Set (Fin n)) :=
              Finset.mem_coe.mpr (Finset.mem_erase.mpr
                ⟨fun h => by rw [h] at hj; exact Nat.lt_irrefl 0 hj, Finset.mem_univ _⟩)
            have hi_mem : i ∈ (posSet : Set (Fin n)) := by simp [posSet, hi_ne0]
            exact hji (hinj hj_mem hi_mem heq)
        exact refute_not_legit_of_missing_pos hn hK (s₂' i) hw hmtr₃ hs' hb_m₃
    · have hcard_lt : (posSet.image s₂').card < (Finset.univ : Finset (Fin K)).card :=
        Finset.card_lt_card (lt_of_le_of_ne (Finset.subset_univ _) hsurj)
      obtain ⟨w, _, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt
      have hw_pos : ∀ j : Fin n, 0 < j.val → s₂' j ≠ w := by
        intro j hj heq
        have hj_mem : j ∈ posSet := Finset.mem_erase.mpr
          ⟨fun h => by rw [h] at hj; exact Nat.lt_irrefl 0 hj, Finset.mem_univ _⟩
        exact hw (heq ▸ Finset.mem_image_of_mem s₂' hj_mem)
      exact refute_not_legit_of_missing_pos hn hK w hw_pos hmtr₂ hs' hb_m₂

/-! ### Impossibility cycles and sharp necessary-and-sufficient characterizations -/

private def shiftVal {n K : ℕ} [NeZero K] (c : ℕ) (s : Fin n → Fin K) : Fin n → Fin K :=
  fun i => ⟨((s i).val + c) % K, Nat.mod_lt _ (NeZero.pos K)⟩

private theorem shiftVal_add {n K : ℕ} [NeZero K] (a b : ℕ) (s : Fin n → Fin K) :
    shiftVal a (shiftVal b s) = shiftVal (b + a) s := by
  funext i
  ext
  simp only [shiftVal, Nat.mod_add_mod, Nat.add_assoc]

private theorem add_one_mod_inj {K : ℕ} {a b : ℕ} (ha : a < K) (hb : b < K)
    (h : (a + 1) % K = (b + 1) % K) : a = b := by
  by_cases ha1 : a + 1 = K
  · rw [ha1, Nat.mod_self] at h
    by_cases hb1 : b + 1 = K
    · omega
    · rw [Nat.mod_eq_of_lt (by omega : b + 1 < K)] at h
      omega
  · rw [Nat.mod_eq_of_lt (by omega : a + 1 < K)] at h
    by_cases hb1 : b + 1 = K
    · rw [hb1, Nat.mod_self] at h
      omega
    · rw [Nat.mod_eq_of_lt (by omega : b + 1 < K)] at h
      omega

private theorem shiftVal_eq_iff {K : ℕ} [NeZero K] (c : ℕ) (x y : Fin K) :
    shiftVal c (fun _ : Fin 1 => x) 0 = shiftVal c (fun _ : Fin 1 => y) 0 ↔ x = y := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have hv : (x.val + c) % K = (y.val + c) % K := congrArg Fin.val h
  clear h
  induction c with
  | zero =>
    rw [add_zero, add_zero, Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] at hv
    exact Fin.ext hv
  | succ c ih =>
    have hstep : ((x.val + c) % K + 1) % K = ((y.val + c) % K + 1) % K := by
      simpa [Nat.add_assoc, Nat.mod_add_mod] using hv
    exact ih (add_one_mod_inj (Nat.mod_lt _ (NeZero.pos K)) (Nat.mod_lt _ (NeZero.pos K)) hstep)

private theorem dijkstraPrivileged_shiftVal {n K : ℕ} [NeZero n] [NeZero K]
    (c : ℕ) (s : Fin n → Fin K) (i : Fin n) :
    dijkstraPrivileged (shiftVal c s) i ↔ dijkstraPrivileged s i := by
  have heq : (shiftVal c s i = shiftVal c s (i - 1)) ↔ s i = s (i - 1) :=
    shiftVal_eq_iff c (s i) (s (i - 1))
  simp only [dijkstraPrivileged]
  split_ifs
  · exact heq
  · exact not_congr heq

private theorem mem_dijkstraLegitimate_shiftVal {n K : ℕ} [NeZero n] [NeZero K]
    (c : ℕ) (s : Fin n → Fin K) :
    shiftVal c s ∈ DijkstraLegitimate n K ↔ s ∈ DijkstraLegitimate n K := by
  have hps : dijkstraPrivilegedSet (shiftVal c s) = dijkstraPrivilegedSet s := by
    ext i
    simp [dijkstraPrivilegedSet, dijkstraPrivileged_shiftVal]
  simp [DijkstraLegitimate, hps]

private theorem dijkstraStep_shiftVal {n K : ℕ} [NeZero n] [NeZero K]
    (c : ℕ) (s : Fin n → Fin K) (i : Fin n) :
    dijkstraStep (shiftVal c s) i = shiftVal c (dijkstraStep s i) := by
  funext j
  by_cases hji : j = i
  · subst hji
    ext
    simp only [dijkstraStep, shiftVal, Function.update_self, dijkstraNextVal, fin_add_one_mod]
    split_ifs
    · simp only [Nat.mod_add_mod]
      congr 1
      omega
    · rfl
  · simp [dijkstraStep, shiftVal, hji]

private theorem dijkstraDistStep_shiftVal {n K : ℕ} [NeZero n] [NeZero K]
    (c : ℕ) (s : Fin n → Fin K) (S : Finset (Fin n)) :
    dijkstraDistStep (shiftVal c s) S = shiftVal c (dijkstraDistStep s S) := by
  funext j
  by_cases hjS : j ∈ S
  · ext
    simp only [dijkstraDistStep, hjS, ↓reduceIte, shiftVal, dijkstraNextVal, fin_add_one_mod]
    split_ifs
    · simp only [Nat.mod_add_mod]
      congr 1
      omega
    · rfl
  · simp [dijkstraDistStep, shiftVal, hjS]

private theorem div_mod_succ {m : ℕ} (hm : 0 < m) (t : ℕ) :
    if t % m + 1 < m then
      (t + 1) / m = t / m ∧ (t + 1) % m = t % m + 1
    else
      (t + 1) / m = t / m + 1 ∧ (t + 1) % m = 0 := by
  have hdm := Nat.div_add_mod t m
  have hlt := Nat.mod_lt t hm
  split_ifs with hstep
  · have hq : t + 1 = (t % m + 1) + m * (t / m) := by omega
    refine ⟨?_, ?_⟩
    · rw [hq, Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hstep, zero_add]
    · rw [hq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hstep]
  · have heq : t % m + 1 = m := by omega
    have hq : t + 1 = 0 + m * (t / m + 1) := by
      calc
        t + 1 = m * (t / m) + (t % m + 1) := by omega
        _ = m * (t / m) + m := by rw [heq]
        _ = 0 + m * (t / m + 1) := by ring
    refine ⟨?_, ?_⟩
    · rw [hq, Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hm, zero_add]
    · rw [hq, Nat.add_mul_mod_self_left, Nat.zero_mod]

private def centralCycleState (n K : ℕ) [NeZero K] (r : ℕ) : Fin n → Fin K :=
  let d := n - (K + 2)
  if r = 0 then
    fun i =>
      if i.val ≤ d + 1 then ⟨0, NeZero.pos K⟩
      else ⟨(n - 1 - i.val) % K, Nat.mod_lt _ (NeZero.pos K)⟩
  else if r ≤ K then
    fun i =>
      if i.val = 0 then ⟨1 % K, Nat.mod_lt _ (NeZero.pos K)⟩
      else if i.val ≤ d + 1 then ⟨0, NeZero.pos K⟩
      else if i.val ≤ n - r then ⟨(n - 1 - i.val) % K, Nat.mod_lt _ (NeZero.pos K)⟩
      else ⟨(n - i.val) % K, Nat.mod_lt _ (NeZero.pos K)⟩
  else
    fun i =>
      if i.val ≤ r - (K + 1) then ⟨1 % K, Nat.mod_lt _ (NeZero.pos K)⟩
      else if i.val ≤ d + 1 then ⟨0, NeZero.pos K⟩
      else ⟨(n - i.val) % K, Nat.mod_lt _ (NeZero.pos K)⟩

private def centralCycleSched (n K : ℕ) [NeZero n] (hn : K + 2 ≤ n) (r : ℕ) : Fin n :=
  if h0 : r = 0 then ⟨0, NeZero.pos n⟩
  else if hK : r ≤ K then ⟨n - r, by omega⟩
  else if hr : r < n then ⟨r - K, by omega⟩
  else ⟨0, NeZero.pos n⟩

private theorem centralCycleState_step {n K : ℕ} [NeZero n] [NeZero K]
    (hK : 2 ≤ K) (hn : K + 2 ≤ n) {r : ℕ} (hr : r < n) :
    (dijkstraRing n K).Tr (centralCycleState n K r)
      (centralCycleSched n K hn r) (centralCycleState n K (r + 1)) ∧
      centralCycleState n K r ∉ DijkstraLegitimate n K := by
  have h1mod : 1 % K = 1 := Nat.mod_eq_of_lt hK
  have not_legit_of_two {u : Fin n → Fin K} {p₁ p₂ : Fin n}
      (hp₁ : dijkstraPrivileged u p₁) (hp₂ : dijkstraPrivileged u p₂) (hne : p₁ ≠ p₂) :
      u ∉ DijkstraLegitimate n K := by
    intro hleg
    have hmem₁ : p₁ ∈ dijkstraPrivilegedSet u := by simp [dijkstraPrivilegedSet, hp₁]
    have hmem₂ : p₂ ∈ dijkstraPrivilegedSet u := by simp [dijkstraPrivilegedSet, hp₂]
    have hgt : 1 < (dijkstraPrivilegedSet u).card :=
      Finset.one_lt_card.mpr ⟨p₁, hmem₁, p₂, hmem₂, hne⟩
    change (dijkstraPrivilegedSet u).card = 1 at hleg
    omega
  by_cases hr0 : r = 0
  · subst hr0
    have hsched : centralCycleSched n K hn 0 = 0 := rfl
    rw [hsched]
    have hp0 : dijkstraPrivileged (centralCycleState n K 0) 0 := by
      have hz : (0 : Fin n).val = 0 := rfl
      simp only [dijkstraPrivileged, hz, ↓reduceIte, fin_sub_one_eq, ↓reduceDIte,
        centralCycleState]
      ext
      have hnot : ¬ n - 1 ≤ n - (K + 2) + 1 := by omega
      simp only [Nat.zero_le, hnot, ↓reduceIte, Nat.sub_self, Nat.zero_mod]
    have hplast : dijkstraPrivileged (centralCycleState n K 0) ⟨n - 1, by omega⟩ := by
      have hnz : n - 1 ≠ 0 := by omega
      simp only [dijkstraPrivileged, hnz, ↓reduceIte, fin_sub_one_eq, ↓reduceDIte,
        centralCycleState]
      have hnot1 : ¬ n - 1 ≤ n - (K + 2) + 1 := by omega
      have hnot2 : ¬ n - 1 - 1 ≤ n - (K + 2) + 1 := by omega
      intro heq
      have hv := congrArg Fin.val heq
      simp only [hnot1, hnot2, ↓reduceIte] at hv
      have hsub : n - 1 - (n - 1 - 1) = 1 := by omega
      rw [Nat.sub_self, Nat.zero_mod, hsub, h1mod] at hv
      omega
    have hstep_eq : centralCycleState n K 1 = dijkstraStep (centralCycleState n K 0) 0 := by
      funext i
      have h1le : 1 ≤ K := by omega
      by_cases hi0 : i.val = 0
      · obtain rfl : i = 0 := Fin.ext hi0
        ext
        simp only [centralCycleState, Nat.one_ne_zero, h1le, ↓reduceIte, Fin.val_zero,
          dijkstraStep, Function.update_self, dijkstraNextVal, fin_add_one_mod, Nat.zero_le,
          zero_add]
      · have hine : i ≠ 0 := fun h => hi0 (by rw [h]; rfl)
        have hil : i.val ≤ n - 1 := by have := i.isLt; omega
        rw [dijkstraStep, Function.update_of_ne hine]
        simp only [centralCycleState, Nat.one_ne_zero, h1le, ↓reduceIte, hi0, hil]
    refine ⟨⟨hp0, hstep_eq⟩, not_legit_of_two hp0 hplast (fun h => ?_)⟩
    have hv : 0 = n - 1 := congrArg Fin.val h
    omega
  · by_cases hrK : r ≤ K
    · have hsched_val : (centralCycleSched n K hn r).val = n - r := by
        simp only [centralCycleSched, hr0, hrK, ↓reduceDIte]
      let p := centralCycleSched n K hn r
      have hp_nz : p.val ≠ 0 := by rw [hsched_val]; omega
      have hleft_val : (p - 1).val = n - r - 1 := by
        simp only [fin_sub_one_eq, hp_nz, ↓reduceDIte]
        rw [hsched_val]
      have hp_priv : dijkstraPrivileged (centralCycleState n K r) p := by
        simp only [dijkstraPrivileged, hp_nz, ↓reduceIte]
        intro heq
        have hv := congrArg Fin.val heq
        simp only [centralCycleState, hr0, hrK, ↓reduceIte, hp_nz] at hv
        have hp_gt_d : ¬ p.val ≤ n - (K + 2) + 1 := by rw [hsched_val]; omega
        have hp_le_nr : p.val ≤ n - r := by rw [hsched_val]
        simp only [hp_gt_d, hp_le_nr, ↓reduceIte] at hv
        have hl_nz : (p - 1).val ≠ 0 := by rw [hleft_val]; omega
        simp only [hl_nz, ↓reduceIte] at hv
        by_cases hrrK : r = K
        · have hl_le_d : (p - 1).val ≤ n - (K + 2) + 1 := by rw [hleft_val]; omega
          simp only [hl_le_d, ↓reduceIte] at hv
          have hsub : n - 1 - p.val = K - 1 := by rw [hsched_val]; omega
          rw [hsub, Nat.mod_eq_of_lt (by omega)] at hv
          omega
        · have hl_gt_d : ¬ (p - 1).val ≤ n - (K + 2) + 1 := by rw [hleft_val]; omega
          have hl_le_nr : (p - 1).val ≤ n - r := by rw [hleft_val]; omega
          simp only [hl_gt_d, hl_le_nr, ↓reduceIte] at hv
          have hs1 : n - 1 - p.val = r - 1 := by rw [hsched_val]; omega
          have hs2 : n - 1 - (p - 1).val = r := by rw [hleft_val]; omega
          rw [hs1, hs2, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
          omega
      have hstep_eq : centralCycleState n K (r + 1) =
          dijkstraStep (centralCycleState n K r) p := by
        funext i
        ext
        have hr1_nz : r + 1 ≠ 0 := by omega
        by_cases hip : i = p
        · subst hip
          simp only [dijkstraStep, Function.update_self, dijkstraNextVal, hp_nz, ↓reduceIte]
          have hnext_val : (centralCycleState n K r (p - 1)).val = (n - p.val) % K := by
            have hl_nz : (p - 1).val ≠ 0 := by rw [hleft_val]; omega
            simp only [centralCycleState, hr0, hrK, ↓reduceIte, hl_nz]
            by_cases hrrK : r = K
            · have hl_le_d : (p - 1).val ≤ n - (K + 2) + 1 := by rw [hleft_val]; omega
              have hnp : n - p.val = K := by rw [hsched_val]; omega
              simp only [hl_le_d, ↓reduceIte, hnp, Nat.mod_self]
            · have hl_gt_d : ¬ (p - 1).val ≤ n - (K + 2) + 1 := by rw [hleft_val]; omega
              have hl_le_nr : (p - 1).val ≤ n - r := by rw [hleft_val]; omega
              have hs2 : n - 1 - (p - 1).val = n - p.val := by
                rw [hleft_val, hsched_val]; omega
              simp only [hl_gt_d, hl_le_nr, ↓reduceIte, hs2]
          rw [hnext_val]
          have hp_gt_d : ¬ p.val ≤ n - (K + 2) + 1 := by rw [hsched_val]; omega
          by_cases hrrK : r = K
          · have hnotK : ¬ r + 1 ≤ K := by omega
            have hsub0 : r + 1 - (K + 1) = 0 := by omega
            have hnot0 : ¬ p.val ≤ 0 := by omega
            simp only [centralCycleState, hr1_nz, hnotK, ↓reduceIte, hsub0, hnot0, hp_gt_d]
          · have hr1K : r + 1 ≤ K := by omega
            have hnot_nr1 : ¬ p.val ≤ n - (r + 1) := by rw [hsched_val]; omega
            simp only [centralCycleState, hr1_nz, hr1K, ↓reduceIte, hp_nz, hp_gt_d, hnot_nr1]
        · rw [dijkstraStep, Function.update_of_ne hip]
          have hi_lt := i.isLt
          have hi_ne_val : i.val ≠ n - r := fun h => hip (Fin.ext (h.trans hsched_val.symm))
          by_cases hrrK : r = K
          · have hnotK : ¬ r + 1 ≤ K := by omega
            have hsub0 : r + 1 - (K + 1) = 0 := by omega
            simp only [centralCycleState, hr1_nz, hnotK, ↓reduceIte, hsub0, hr0, hrK]
            by_cases hi0 : i.val = 0
            · simp only [hi0, Nat.zero_le, ↓reduceIte]
            · have hnot0 : ¬ i.val ≤ 0 := by omega
              simp only [hi0, hnot0, ↓reduceIte]
              split_ifs with hd hnr
              · rfl
              · exfalso; omega
              · rfl
          · have hr1K : r + 1 ≤ K := by omega
            simp only [centralCycleState, hr1_nz, hr1K, ↓reduceIte, hr0, hrK]
            by_cases hi0 : i.val = 0
            · simp only [hi0, ↓reduceIte]
            · simp only [hi0, ↓reduceIte]
              by_cases hd : i.val ≤ n - (K + 2) + 1
              · simp only [hd, ↓reduceIte]
              · simp only [hd, ↓reduceIte]
                have hiff : (i.val ≤ n - (r + 1)) ↔ (i.val ≤ n - r) := by omega
                simp only [hiff]
      have hnot_leg : centralCycleState n K r ∉ DijkstraLegitimate n K := by
        by_cases hr1 : r = 1
        · subst hr1
          have hp1 : dijkstraPrivileged (centralCycleState n K 1) ⟨1, by omega⟩ := by
            have h1le : 1 ≤ K := by omega
            have h1d : 1 ≤ n - (K + 2) + 1 := by omega
            simp only [dijkstraPrivileged, Nat.one_ne_zero, ↓reduceIte, fin_sub_one_eq, ↓reduceDIte,
              Nat.sub_self, centralCycleState, h1le, h1d]
            exact fun heq => Nat.zero_ne_one ((congrArg Fin.val heq).trans h1mod)
          refine not_legit_of_two hp1 hp_priv (fun h => ?_)
          have hv : 1 = p.val := congrArg Fin.val h
          rw [hsched_val] at hv; omega
        · have hp0 : dijkstraPrivileged (centralCycleState n K r) 0 := by
            have hnot_d : ¬ n - 1 ≤ n - (K + 2) + 1 := by omega
            have hnot_nr : ¬ n - 1 ≤ n - r := by omega
            have hsub1 : n - (n - 1) = 1 := by omega
            simp only [dijkstraPrivileged, Fin.val_zero, ↓reduceIte, fin_sub_one_eq, ↓reduceDIte,
              centralCycleState, hr0, hrK, Nat.sub_ne_zero_of_lt (by omega : 1 < n), hnot_d,
              hnot_nr, hsub1]
          exact not_legit_of_two hp0 hp_priv (Ne.symm (fun h => hp_nz (by rw [h]; rfl)))
      exact ⟨⟨hp_priv, hstep_eq⟩, hnot_leg⟩
    · have hgtK : K + 1 ≤ r := by omega
      have hnot_leK : ¬ r ≤ K := hrK
      have hsched_val : (centralCycleSched n K hn r).val = r - K := by
        simp only [centralCycleSched, hr0, hrK, hr, ↓reduceDIte]
      let p := centralCycleSched n K hn r
      have hp_nz : p.val ≠ 0 := by rw [hsched_val]; omega
      have hleft_val : (p - 1).val = r - (K + 1) := by
        simp only [fin_sub_one_eq, hp_nz, ↓reduceDIte]
        rw [hsched_val]
        omega
      have hp_priv : dijkstraPrivileged (centralCycleState n K r) p := by
        simp only [dijkstraPrivileged, hp_nz, ↓reduceIte]
        intro heq
        have hv := congrArg Fin.val heq
        have hp_not_1 : ¬ p.val ≤ r - (K + 1) := by rw [hsched_val]; omega
        have hp_le_d : p.val ≤ n - (K + 2) + 1 := by rw [hsched_val]; omega
        have hl_le_1 : (p - 1).val ≤ r - (K + 1) := by rw [hleft_val]
        simp only [centralCycleState, hr0, hnot_leK, ↓reduceIte, hp_not_1, hp_le_d,
          hl_le_1, h1mod] at hv
        omega
      have hp0 : dijkstraPrivileged (centralCycleState n K r) 0 := by
        have hnot1 : ¬ n - 1 ≤ r - (K + 1) := by omega
        have hnotd : ¬ n - 1 ≤ n - (K + 2) + 1 := by omega
        have hsub1 : n - (n - 1) = 1 := by omega
        simp only [dijkstraPrivileged, Fin.val_zero, ↓reduceIte, fin_sub_one_eq, ↓reduceDIte,
          centralCycleState, hr0, hnot_leK, Nat.zero_le, hnot1, hnotd, hsub1]
      have hstep_eq : centralCycleState n K (r + 1) =
          dijkstraStep (centralCycleState n K r) p := by
        funext i
        have hr1_nz : r + 1 ≠ 0 := by omega
        have hnot_leK1 : ¬ r + 1 ≤ K := by omega
        by_cases hip : i = p
        · subst hip
          ext
          have hl_le_1 : (p - 1).val ≤ r - (K + 1) := by rw [hleft_val]
          have hp_le_next : p.val ≤ r + 1 - (K + 1) := by rw [hsched_val]; omega
          simp only [dijkstraStep, Function.update_self, dijkstraNextVal, hp_nz, ↓reduceIte,
            centralCycleState, hr1_nz, hnot_leK1, hp_le_next, hr0, hnot_leK, hl_le_1]
        · rw [dijkstraStep, Function.update_of_ne hip]
          have hi_ne_val : i.val ≠ r - K := fun h => hip (Fin.ext (h.trans hsched_val.symm))
          have hiff : (i.val ≤ r + 1 - (K + 1)) ↔ (i.val ≤ r - (K + 1)) := by omega
          simp only [centralCycleState, hr1_nz, hnot_leK1, ↓reduceIte, hr0, hnot_leK, hiff]
      exact ⟨⟨hp_priv, hstep_eq⟩,
        not_legit_of_two hp0 hp_priv (Ne.symm (fun h => hp_nz (by rw [h]; rfl)))⟩

private theorem centralCycleState_end {n K : ℕ} [NeZero K] (hn : K + 2 ≤ n) :
    centralCycleState n K n = shiftVal 1 (centralCycleState n K 0) := by
  funext i
  apply Fin.ext
  have hi_lt := i.isLt
  have hn0 : n ≠ 0 := by omega
  have hnot_leK : ¬ n ≤ K := by omega
  have hsub_eq : n - (K + 1) = n - (K + 2) + 1 := by omega
  simp only [centralCycleState, hn0, hnot_leK, ↓reduceIte, hsub_eq, shiftVal]
  split_ifs with hd
  · rfl
  · dsimp only
    have hni : n - i.val = n - 1 - i.val + 1 := by omega
    rw [hni, Nat.mod_add_mod]

/-- Original converse counterexample showing sharpness of Note 1 of [Dijkstra][Dijkstra1974]
(p. 644): when `2 ≤ K` and `K + 1 < n` (`K < N`), Dijkstra's `K`-state ring admits an explicit
periodic central-daemon execution that never enters `DijkstraLegitimate n K`, so
`dijkstraRing n K` is not self-stabilizing. -/
theorem dijkstraRing_not_selfStabilizing_of_lt_pred {n K : ℕ} [NeZero n] [NeZero K]
    (hK : 2 ≤ K) (hKn : K + 1 < n) :
    ¬ SelfStabilizing (dijkstraRing n K) (DijkstraLegitimate n K) := by
  have hn : K + 2 ≤ n := by omega
  have hn_pos : 0 < n := NeZero.pos n
  let ss : ωSequence (Fin n → Fin K) :=
    ⟨fun t => shiftVal (t / n) (centralCycleState n K (t % n))⟩
  let μs : ωSequence (Fin n) :=
    ⟨fun t => centralCycleSched n K hn (t % n)⟩
  have hexec : (dijkstraRing n K).OmegaExecution ss μs := by
    intro t
    have hstep := (centralCycleState_step hK hn (Nat.mod_lt t hn_pos)).1
    obtain ⟨hpriv, hnext⟩ := hstep
    have hdm := div_mod_succ hn_pos t
    refine ⟨(dijkstraPrivileged_shiftVal (t / n) _ _).mpr hpriv, ?_⟩
    change shiftVal ((t + 1) / n) (centralCycleState n K ((t + 1) % n)) =
      dijkstraStep (shiftVal (t / n) (centralCycleState n K (t % n)))
        (centralCycleSched n K hn (t % n))
    rw [dijkstraStep_shiftVal, ← hnext]
    split_ifs at hdm with hlt
    · rw [hdm.1, hdm.2]
    · have heq : t % n + 1 = n := by
        have := Nat.mod_lt t hn_pos
        omega
      rw [hdm.1, hdm.2, heq, centralCycleState_end hn, shiftVal_add, Nat.one_add]
  have hbad : ∀ t, ss t ∉ DijkstraLegitimate n K := by
    intro t
    change shiftVal (t / n) (centralCycleState n K (t % n)) ∉ DijkstraLegitimate n K
    rw [mem_dijkstraLegitimate_shiftVal]
    exact (centralCycleState_step hK hn (Nat.mod_lt t hn_pos)).2
  exact not_selfStabilizing_of_omegaExecution hexec hbad

/-- Original converse counterexample in the simultaneous atomic-subset model `dijkstraDistRing`:
when `2 ≤ K` and `K < n`, `dijkstraDistRing n K` is not self-stabilizing (at `n = K + 1`,
synchronous execution from `(0, K - 1, K - 2, …, 1, 0)` cycles through `K` states in each of which
all `n ≥ 3` machines are privileged). -/
theorem dijkstraDistRing_not_selfStabilizing_of_lt {n K : ℕ} [NeZero n] [NeZero K]
    (hK : 2 ≤ K) (hKn : K < n) :
    ¬ SelfStabilizing (dijkstraDistRing n K) (DijkstraLegitimate n K) := by
  by_cases hpred : K + 1 < n
  · intro hss
    exact dijkstraRing_not_selfStabilizing_of_lt_pred hK hpred
      (SelfStabilizing.of_subLTS hss
        (fun _ i _ htr => ⟨{i}, (dijkstraRing_tr_iff_distRing_singleton _ i _).mp htr⟩)
        dijkstraRing_not_isTerminal)
  · have hnk : n = K + 1 := by omega
    let s₀ : Fin n → Fin K := fun i =>
      ⟨(K - i.val % K) % K, Nat.mod_lt _ (NeZero.pos K)⟩
    have hpriv_all : ∀ i : Fin n, dijkstraPrivileged s₀ i := by
      intro i
      by_cases hi0 : i.val = 0
      · simp only [dijkstraPrivileged, hi0, ↓reduceIte, fin_sub_one_eq, ↓reduceDIte]
        apply Fin.ext
        dsimp only [s₀]
        have hlast : n - 1 = K := by omega
        rw [hi0, Nat.zero_mod, Nat.sub_zero, hlast, Nat.mod_self, Nat.sub_zero]
        exact (Nat.mod_self K).symm
      · simp only [dijkstraPrivileged, hi0, ↓reduceIte, fin_sub_one_eq, ↓reduceDIte]
        intro heq
        have hv : (K - i.val % K) % K = (K - (i.val - 1) % K) % K := congrArg Fin.val heq
        by_cases hi1 : i.val = 1
        · rw [hi1, Nat.mod_eq_of_lt hK, Nat.sub_self, Nat.zero_mod, Nat.sub_zero,
            Nat.mod_self, Nat.mod_eq_of_lt (by omega : K - 1 < K)] at hv
          omega
        · by_cases hiK : i.val = K
          · have hsub : K - 1 < K := by omega
            rw [hiK, Nat.mod_self, Nat.sub_zero, Nat.mod_self,
              Nat.mod_eq_of_lt hsub, show K - (K - 1) = 1 by omega,
              Nat.mod_eq_of_lt hK] at hv
            omega
          · have hilt : i.val < K := by have := i.isLt; omega
            have hprev_lt : i.val - 1 < K := by omega
            rw [Nat.mod_eq_of_lt hilt, Nat.mod_eq_of_lt hprev_lt,
              Nat.mod_eq_of_lt (by omega : K - i.val < K),
              Nat.mod_eq_of_lt (by omega : K - (i.val - 1) < K)] at hv
            omega
    have hstep_univ : dijkstraDistStep s₀ Finset.univ = shiftVal 1 s₀ := by
      funext i
      apply Fin.ext
      by_cases hi0 : i.val = 0
      · simp [dijkstraDistStep, dijkstraNextVal, hi0, fin_add_one_mod, shiftVal, s₀]
      · simp only [dijkstraDistStep, Finset.mem_univ, ↓reduceIte, dijkstraNextVal,
          hi0, fin_sub_one_eq, ↓reduceDIte, shiftVal]
        dsimp only [s₀]
        rw [Nat.mod_add_mod]
        by_cases hi1 : i.val = 1
        · rw [hi1, Nat.sub_self, Nat.zero_mod, Nat.sub_zero, Nat.mod_self,
            Nat.mod_eq_of_lt hK, show K - 1 + 1 = K by omega, Nat.mod_self]
        · by_cases hiK : i.val = K
          · have hsub : K - 1 < K := by omega
            rw [hiK, Nat.mod_self, Nat.sub_zero, Nat.mod_eq_of_lt hsub,
              show K - (K - 1) = 1 by omega, show K + 1 = 1 + K by omega, Nat.add_mod_right]
          · have hilt : i.val < K := by have := i.isLt; omega
            have hprev_lt : i.val - 1 < K := by omega
            rw [Nat.mod_eq_of_lt hilt, Nat.mod_eq_of_lt hprev_lt]
            congr 1
            omega
    let ss : ωSequence (Fin n → Fin K) := ⟨fun t => shiftVal t s₀⟩
    let μs : ωSequence (Finset (Fin n)) := ⟨fun _ => Finset.univ⟩
    have hexec : (dijkstraDistRing n K).OmegaExecution ss μs := by
      intro t
      refine ⟨Finset.univ_nonempty, fun i _ =>
        (dijkstraPrivileged_shiftVal t s₀ i).mpr (hpriv_all i), ?_⟩
      change shiftVal (t + 1) s₀ = dijkstraDistStep (shiftVal t s₀) Finset.univ
      rw [dijkstraDistStep_shiftVal, hstep_univ, shiftVal_add, Nat.one_add]
    have hbad : ∀ t, ss t ∉ DijkstraLegitimate n K := by
      intro t
      change shiftVal t s₀ ∉ DijkstraLegitimate n K
      rw [mem_dijkstraLegitimate_shiftVal]
      have hps : dijkstraPrivilegedSet s₀ = Finset.univ := by
        ext i; simp [dijkstraPrivilegedSet, hpriv_all i]
      change (dijkstraPrivilegedSet s₀).card ≠ 1
      rw [hps, Finset.card_univ, Fintype.card_fin]
      omega
    exact not_selfStabilizing_of_omegaExecution hexec hbad

/-- Original exact characterization in the simultaneous atomic-subset model (`2 ≤ n`, `2 ≤ K`):
`dijkstraDistRing n K` is self-stabilizing iff `n ≤ K`. -/
theorem dijkstraDistRing_selfStabilizing_iff {n K : ℕ} [NeZero n] [NeZero K]
    (hn : 2 ≤ n) (hK : 2 ≤ K) :
    SelfStabilizing (dijkstraDistRing n K) (DijkstraLegitimate n K) ↔ n ≤ K :=
  ⟨fun hss => not_lt.mp fun hlt => dijkstraDistRing_not_selfStabilizing_of_lt hK hlt hss,
    dijkstraDistRing_selfStabilizing_of_le hn⟩

/-- Exact characterization under a central daemon (`2 ≤ n`, `2 ≤ K`), combining Note 1 of
[Dijkstra][Dijkstra1974] (p. 644, `K ≥ N`) with the original converse
`dijkstraRing_not_selfStabilizing_of_lt_pred`: Dijkstra's `K`-state token ring is self-stabilizing
iff `n - 1 ≤ K`. -/
theorem dijkstraRing_selfStabilizing_iff {n K : ℕ} [NeZero n] [NeZero K]
    (hn : 2 ≤ n) (hK : 2 ≤ K) :
    SelfStabilizing (dijkstraRing n K) (DijkstraLegitimate n K) ↔ n - 1 ≤ K :=
  ⟨fun hss => not_lt.mp fun hlt =>
      dijkstraRing_not_selfStabilizing_of_lt_pred hK (by omega) hss,
    dijkstraRing_selfStabilizing_of_pred_le hn hK⟩

/-! ### Enabled-move composite anonymous ring symmetry steps -/

/-- A deterministic *uniform* (anonymous) local ring protocol over state space `State`, in which
every node executes the identical local privilege predicate and state-transition function on its
`(left, self, right)` neighbourhood (after [Dijkstra][Dijkstra1973]; [Dijkstra][Dijkstra1974],
pp. 643–644). -/
structure UniformRingProtocol (State : Type*) where
  /-- Boolean privilege predicate reading `(left, self, right)` neighbour states. -/
  privileged : State → State → State → Bool
  /-- Next local state upon moving, reading `(left, self, right)` neighbour states. -/
  step : State → State → State → State

/-- A ring configuration `s : Fin n → State` is `a`-periodic in residue classes when positions
congruent modulo `a` carry equal states. -/
@[expose] def IsRingPeriodic (a : ℕ) {n : ℕ} {State : Type*} (s : Fin n → State) : Prop :=
  ∀ i j : Fin n, i.val % a = j.val % a → s i = s j

private theorem mul_add_lt_mul {a b k r : ℕ} (hr : r < a) (hk : k < b) : a * k + r < a * b :=
  (Nat.add_lt_add_left hr _).trans_le
    ((Nat.mul_succ a k).symm.trans_le (Nat.mul_le_mul_left a hk))

private theorem fin_sub_one_val_mod {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) [NeZero (a * b)]
    (x : Fin (a * b)) : (x - 1).val % a = (x.val + (a - 1)) % a := by
  rw [fin_sub_one_eq]
  split_ifs with hx0 <;> dsimp only
  · have := Nat.le_mul_of_pos_right a hb
    rw [hx0, zero_add, show a * b - 1 = a - 1 + a * (b - 1) by rw [Nat.mul_sub_one]; omega,
      Nat.add_mul_mod_self_left]
  · rw [← Nat.add_mod_right, show x.val - 1 + a = x.val + (a - 1) by omega]

namespace UniformRingProtocol

section Ring

variable {State : Type*} (π : UniformRingProtocol State)

/-- Whether node `i` is privileged in configuration `s`. -/
@[expose] def isPrivileged {n : ℕ} [NeZero n] (s : Fin n → State) (i : Fin n) : Bool :=
  π.privileged (s (i - 1)) (s i) (s (i + 1))

/-- Next state of node `i` in configuration `s`. -/
@[expose] def nextVal {n : ℕ} [NeZero n] (s : Fin n → State) (i : Fin n) : State :=
  π.step (s (i - 1)) (s i) (s (i + 1))

/-- Set of privileged nodes of `π` in configuration `s`. -/
@[expose] def privilegedSet {n : ℕ} [NeZero n] (s : Fin n → State) : Finset (Fin n) :=
  Finset.univ.filter fun i => π.isPrivileged s i = true

/-- Configurations in which *exactly one* node is privileged under `π`. -/
@[expose] def UniquePrivilege (n : ℕ) [NeZero n] : Set (Fin n → State) :=
  { s | (π.privilegedSet s).card = 1 }

/-- Enabled-move central-daemon labelled transition system of `π` on `Fin n`: transitions permit
only privileged moves, with no per-machine fairness obligation across residue classes. -/
@[expose] def centralLTS (n : ℕ) [NeZero n] : LTS (Fin n → State) (Fin n) where
  Tr s i s' := π.isPrivileged s i = true ∧ s' = Function.update s i (π.nextVal s i)

/-- Simultaneous atomic-subset enabled-move labelled transition system of `π` on `Fin n`: each
transition updates a nonempty set of privileged nodes atomically from the pre-step state. -/
@[expose] def distLTS (n : ℕ) [NeZero n] : LTS (Fin n → State) (Finset (Fin n)) where
  Tr s S s' :=
    S.Nonempty ∧ (∀ i ∈ S, π.isPrivileged s i = true) ∧
      s' = fun j => if j ∈ S then π.nextVal s j else s j

private theorem sub_one_mod_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) [NeZero (a * b)]
    {i j : Fin (a * b)} (hij : i.val % a = j.val % a) :
    (i - 1).val % a = (j - 1).val % a := by
  rw [fin_sub_one_val_mod ha hb, fin_sub_one_val_mod ha hb, ← Nat.mod_add_mod, hij, Nat.mod_add_mod]

private theorem add_one_mod_eq {a b : ℕ} [NeZero (a * b)]
    {i j : Fin (a * b)} (hij : i.val % a = j.val % a) :
    (i + 1).val % a = (j + 1).val % a := by
  have hmod : ∀ x : Fin (a * b), (x + 1).val % a = (x.val + 1) % a := by
    intro x
    simp only [fin_add_one_eq]
    split_ifs with hlast
    · simp only [Nat.zero_mod]
      have : (x.val + 1) % a = (a * b) % a := by rw [hlast]
      rw [this, Nat.mul_mod_right]
    · rfl
  rw [hmod i, hmod j, ← Nat.mod_add_mod, hij, Nat.mod_add_mod]

private theorem isPrivileged_eq_of_isRingPeriodic {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    [NeZero (a * b)] {s : Fin (a * b) → State} (hper : IsRingPeriodic a s)
    {i j : Fin (a * b)} (hij : i.val % a = j.val % a) :
    π.isPrivileged s i = π.isPrivileged s j := by
  simp only [isPrivileged]
  rw [hper _ _ (sub_one_mod_eq ha hb hij), hper i j hij, hper _ _ (add_one_mod_eq hij)]

private theorem nextVal_eq_of_isRingPeriodic {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    [NeZero (a * b)] {s : Fin (a * b) → State} (hper : IsRingPeriodic a s)
    {i j : Fin (a * b)} (hij : i.val % a = j.val % a) :
    π.nextVal s i = π.nextVal s j := by
  simp only [nextVal]
  rw [hper _ _ (sub_one_mod_eq ha hb hij), hper i j hij, hper _ _ (add_one_mod_eq hij)]

/-- On a ring of size `a * b` (`1 ≤ a`, `1 ≤ b`), the number of privileged nodes in any
`a`-periodic configuration is divisible by `b`. -/
theorem card_privilegedSet_dvd_of_isRingPeriodic {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    [NeZero (a * b)] {s : Fin (a * b) → State} (hper : IsRingPeriodic a s) :
    b ∣ (π.privilegedSet s).card := by
  let eqv : Fin a × Fin b ≃ Fin (a * b) :=
    { toFun := fun rq => ⟨a * rq.2.val + rq.1.val, mul_add_lt_mul rq.1.isLt rq.2.isLt⟩
      invFun := fun i => (⟨i.val % a, Nat.mod_lt _ ha⟩, ⟨i.val / a, Nat.div_lt_of_lt_mul i.isLt⟩)
      left_inv := fun ⟨r, q⟩ => by
        ext
        · dsimp only
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt r.isLt]
        · dsimp only
          rw [Nat.mul_add_div ha, Nat.div_eq_of_lt r.isLt, add_zero]
      right_inv := fun i => by
        ext
        dsimp only
        exact Nat.div_add_mod i.val a }
  have hcard : (π.privilegedSet s).card =
      ∑ i : Fin (a * b), if π.isPrivileged s i = true then 1 else 0 := by
    simp [privilegedSet]
  rw [hcard, ← Equiv.sum_comp eqv]
  have hconst : ∀ (r : Fin a) (q : Fin b),
      π.isPrivileged s (eqv (r, q)) = π.isPrivileged s (eqv (r, ⟨0, hb⟩)) := by
    intro r q
    apply π.isPrivileged_eq_of_isRingPeriodic ha hb hper
    simp only [eqv, Equiv.coe_fn_mk]
    rw [Nat.mul_add_mod, Nat.mul_zero, zero_add]
  rw [Fintype.sum_prod_type]
  have hrow : ∑ r : Fin a, ∑ q : Fin b, (if π.isPrivileged s (eqv (r, q)) = true then 1 else 0) =
      b * ∑ r : Fin a, (if π.isPrivileged s (eqv (r, ⟨0, hb⟩)) = true then 1 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have : (∑ q : Fin b, if π.isPrivileged s (eqv (r, q)) = true then 1 else 0) =
        ∑ _q : Fin b, (if π.isPrivileged s (eqv (r, ⟨0, hb⟩)) = true then 1 else 0) :=
      Finset.sum_congr rfl fun q _ => by rw [hconst r q]
    rw [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hrow]
  exact dvd_mul_right b _

/-- Any distributed step whose firing set `S` is a union of `a`-residue classes preserves
`IsRingPeriodic a`. -/
theorem isRingPeriodic_distStep {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) [NeZero (a * b)]
    {s : Fin (a * b) → State} {S : Finset (Fin (a * b))}
    (hper : IsRingPeriodic a s)
    (hS : ∀ i j : Fin (a * b), i.val % a = j.val % a → (i ∈ S ↔ j ∈ S)) :
    IsRingPeriodic a (fun j => if j ∈ S then π.nextVal s j else s j) := by
  intro i j hij
  by_cases hi : i ∈ S
  · have hj : j ∈ S := (hS i j hij).mp hi
    simp [hi, hj, π.nextVal_eq_of_isRingPeriodic ha hb hper hij]
  · have hj : j ∉ S := mt (hS i j hij).mpr hi
    simp [hi, hj, hper i j hij]

end Ring

end UniformRingProtocol

/-- Scheduler-scoped enabled-move step towards the composite-ring symmetry argument of
[Dijkstra][Dijkstra1973] (`EWD391`), and not `EWD391`'s fair-command impossibility endpoint: on a
ring of composite size `a * b` (`2 ≤ a`, `2 ≤ b`) over a nonempty state type, no uniform
deterministic ring protocol satisfies `SelfStabilizing (π.centralLTS (a * b)) Legitimate` for any
`Legitimate ⊆ π.UniquePrivilege (a * b)`.

Because `2 ≤ a` and `2 ≤ b`, the `b` positions in any single modulo-`a` residue class have pairwise
ring distance at least `2`. Stepping an enabled residue class sequentially in `b`-move blocks
reaches a new `a`-periodic configuration every `b` moves while closure of `Legitimate` rules out
intermediate visits to `Legitimate`. Note that `π.centralLTS` permits only privileged moves with no
fairness obligation across residue classes, whereas `EWD391`'s daemon issues infinitely many
adjustment commands to every machine (permitting no-effect commands); `EWD391`'s fair-command
composite-ring endpoint remains open (#7291). -/
theorem not_uniform_enabledMove_selfStabilizing_composite_ring {State : Type*} [Nonempty State]
    {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) [NeZero (a * b)]
    (π : UniformRingProtocol State) {Legitimate : Set (Fin (a * b) → State)}
    (hleg : Legitimate ⊆ π.UniquePrivilege (a * b)) :
    ¬ SelfStabilizing (π.centralLTS (a * b)) Legitimate := by
  intro hss
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have hnot_leg_per : ∀ {u : Fin (a * b) → State}, IsRingPeriodic a u → u ∉ Legitimate := by
    intro u hper hu
    have hdvd := π.card_privilegedSet_dvd_of_isRingPeriodic ha1 hb1 hper
    have hcard1 : (π.privilegedSet u).card = 1 := hleg hu
    rw [hcard1] at hdvd
    have hle1 := Nat.le_of_dvd Nat.one_pos hdvd
    omega
  -- Independent-set property: distinct elements of a mod-`a` coset are non-adjacent in `C_{a*b}`.
  have coset_ne_sub_one : ∀ {r : ℕ} (hr : r < a) {k₁ k₂ : ℕ} (hk₁ : k₁ < b) (hk₂ : k₂ < b),
      (⟨a * k₁ + r, mul_add_lt_mul hr hk₁⟩ : Fin (a * b)) ≠
        (⟨a * k₂ + r, mul_add_lt_mul hr hk₂⟩ : Fin (a * b)) - 1 := by
    intro r hr k₁ k₂ hk₁ hk₂ h
    have hv := congrArg (fun x : Fin (a * b) => x.val % a) h
    simp only [fin_sub_one_val_mod ha1 hb1, add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt hr] at hv
    rw [Nat.add_mod_eq_ite, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt (by omega : a - 1 < a)] at hv
    split_ifs at hv <;> omega
  -- For any `a`-periodic configuration `u`, construct its `b`-step coset sweep.
  have hcoset_sweep : ∀ u : Fin (a * b) → State, IsRingPeriodic a u →
      ∃ (st : ℕ → Fin (a * b) → State) (lbl : ℕ → Fin (a * b)),
        st 0 = u ∧
        IsRingPeriodic a (st b) ∧
        (∀ k < b, (π.centralLTS (a * b)).Tr (st k) (lbl k) (st (k + 1))) ∧
        (∀ k < b, st k ∉ Legitimate) := by
    intro u hper
    obtain ⟨i₀, _, hi₀_tr⟩ := hss.exists_tr u
    have hi₀_priv : π.isPrivileged u i₀ = true := hi₀_tr.1
    let r := i₀.val % a
    have hr_lt : r < a := Nat.mod_lt _ ha1
    let v_new := π.nextVal u i₀
    let cosetNode : ℕ → Fin (a * b) := fun k =>
      if hk : k < b then ⟨a * k + r, mul_add_lt_mul hr_lt hk⟩ else ⟨0, NeZero.pos (a * b)⟩
    let st : ℕ → Fin (a * b) → State := fun k j =>
      if j.val % a = r ∧ j.val / a < min k b then v_new else u j
    have hst0 : st 0 = u := by funext j; simp [st]
    have hstb_per : IsRingPeriodic a (st b) := by
      intro i j hij
      simp only [st, min_self, Nat.div_lt_of_lt_mul i.isLt, Nat.div_lt_of_lt_mul j.isLt, and_true,
        hij]
      split_ifs
      · rfl
      · exact hper i j hij
    have hstep_k : ∀ k, k < b →
        (π.centralLTS (a * b)).Tr (st k) (cosetNode k) (st (k + 1)) := by
      intro k hk
      let pk : Fin (a * b) := ⟨a * k + r, mul_add_lt_mul hr_lt hk⟩
      have hcn : cosetNode k = pk := by simp [cosetNode, hk, pk]
      rw [hcn]
      have hpk_mod : pk.val % a = r := by
        dsimp only [pk]; rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr_lt]
      have hpk_div : pk.val / a = k := by
        dsimp only [pk]; rw [Nat.mul_add_div ha1, Nat.div_eq_of_lt hr_lt, add_zero]
      have hmin_k : min k b = k := Nat.min_eq_left (Nat.le_of_lt hk)
      have hmin_k1 : min (k + 1) b = k + 1 := Nat.min_eq_left hk
      have hpk_same : st k pk = u pk := by
        simp only [st, hpk_div, hmin_k, lt_irrefl, and_false, ↓reduceIte]
      have hnbor_same : ∀ x : Fin (a * b),
          (x = pk - 1 ∨ x = pk + 1) → st k x = u x := by
        intro x hx
        simp only [st, hmin_k]
        split_ifs with hcond
        · exfalso
          obtain ⟨hx_mod, hx_div⟩ := hcond
          let k' := x.val / a
          have hk'_lt : k' < b := lt_trans hx_div hk
          have hx_eq : x = ⟨a * k' + r, mul_add_lt_mul hr_lt hk'_lt⟩ := by
            ext
            dsimp only [k']
            rw [← hx_mod]
            exact (Nat.div_add_mod x.val a).symm
          rcases hx with rfl | rfl
          · exact coset_ne_sub_one hr_lt hk'_lt hk hx_eq.symm
          · exact coset_ne_sub_one hr_lt hk hk'_lt (by rw [← hx_eq, fin_add_sub_one])
        · rfl
      have hleft_same : st k (pk - 1) = u (pk - 1) :=
        hnbor_same _ (Or.inl rfl)
      have hright_same : st k (pk + 1) = u (pk + 1) :=
        hnbor_same _ (Or.inr rfl)
      have hpriv_pk : π.isPrivileged (st k) pk = true := by
        have heq_p : π.isPrivileged (st k) pk = π.isPrivileged u pk := by
          simp only [UniformRingProtocol.isPrivileged, hleft_same, hpk_same, hright_same]
        rw [heq_p, π.isPrivileged_eq_of_isRingPeriodic ha1 hb1 hper hpk_mod]
        exact hi₀_priv
      have hnext_pk : π.nextVal (st k) pk = v_new := by
        simp only [UniformRingProtocol.nextVal, hleft_same, hpk_same, hright_same, v_new]
        exact π.nextVal_eq_of_isRingPeriodic ha1 hb1 hper hpk_mod
      refine ⟨hpriv_pk, ?_⟩
      funext j
      by_cases hjp : j = pk
      · subst hjp
        rw [Function.update_self, hnext_pk]
        simp only [st, hpk_mod, hpk_div, hmin_k1, lt_add_iff_pos_right, zero_lt_one,
          and_self, ↓reduceIte]
      · rw [Function.update_of_ne hjp]
        simp only [st, hmin_k, hmin_k1]
        by_cases hj_mod : j.val % a = r
        · have hj_div_ne : j.val / a ≠ k := by
            intro hd
            apply hjp
            ext
            have h1 := Nat.div_add_mod j.val a
            rw [hd, hj_mod] at h1
            exact h1.symm
          have hiff : (j.val / a < k + 1) ↔ (j.val / a < k) := by omega
          simp [hj_mod, hiff]
        · simp [hj_mod]
    have hmTr_to_end : ∀ k, k ≤ b →
        ∃ μs, (π.centralLTS (a * b)).MTr (st k) μs (st b) := by
      intro k hk
      obtain ⟨d, rfl⟩ : ∃ d, k = b - d := ⟨b - k, by omega⟩
      clear hk
      induction d with
      | zero =>
        rw [Nat.sub_zero]
        exact ⟨[], .refl⟩
      | succ d ih =>
        by_cases hdb : b ≤ d
        · have heq : b - (d + 1) = b - d := by omega
          rwa [heq]
        · have hlt_b : b - (d + 1) < b := by omega
          have hsucc : b - (d + 1) + 1 = b - d := by omega
          obtain ⟨μs, hmtr⟩ := ih
          have htr := hstep_k (b - (d + 1)) hlt_b
          rw [hsucc] at htr
          exact ⟨cosetNode (b - (d + 1)) :: μs, .stepL htr hmtr⟩
    refine ⟨st, cosetNode, hst0, hstb_per, hstep_k, fun k hk hleg_k => ?_⟩
    obtain ⟨μs, hmtr⟩ := hmTr_to_end k (Nat.le_of_lt hk)
    exact hnot_leg_per hstb_per (hss.mTr_mem hleg_k hmtr)
  -- Iterate `hcoset_sweep` from the constant `a`-periodic initial state to get an infinite trace.
  let u₀ : Fin (a * b) → State := fun _ => Classical.arbitrary State
  have hu₀_per : IsRingPeriodic a u₀ := fun _ _ _ => rfl
  let PerState := { u : Fin (a * b) → State // IsRingPeriodic a u }
  let nextPer : PerState → PerState := fun ⟨u, hu⟩ =>
    ⟨(hcoset_sweep u hu).choose b, (hcoset_sweep u hu).choose_spec.choose_spec.2.1⟩
  let seqPer : ℕ → PerState := fun m => nextPer^[m] ⟨u₀, hu₀_per⟩
  let stOf : ℕ → ℕ → Fin (a * b) → State := fun m =>
    (hcoset_sweep (seqPer m).val (seqPer m).property).choose
  let lblOf : ℕ → ℕ → Fin (a * b) := fun m =>
    (hcoset_sweep (seqPer m).val (seqPer m).property).choose_spec.choose
  have hb_pos : 0 < b := by omega
  let ss : ωSequence (Fin (a * b) → State) := ⟨fun t => stOf (t / b) (t % b)⟩
  let μs : ωSequence (Fin (a * b)) := ⟨fun t => lblOf (t / b) (t % b)⟩
  have hexec : (π.centralLTS (a * b)).OmegaExecution ss μs := by
    intro t
    have hspec :=
      (hcoset_sweep (seqPer (t / b)).val (seqPer (t / b)).property).choose_spec.choose_spec
    have hstep : (π.centralLTS (a * b)).Tr (stOf (t / b) (t % b)) (lblOf (t / b) (t % b))
        (stOf (t / b) (t % b + 1)) := hspec.2.2.1 (t % b) (Nat.mod_lt t hb_pos)
    have hdm := div_mod_succ hb_pos t
    change (π.centralLTS (a * b)).Tr (stOf (t / b) (t % b)) (lblOf (t / b) (t % b))
      (stOf ((t + 1) / b) ((t + 1) % b))
    split_ifs at hdm with hlt
    · rw [hdm.1, hdm.2]
      exact hstep
    · have heq : t % b + 1 = b := by have := Nat.mod_lt t hb_pos; omega
      rw [heq] at hstep
      have hstart_next : stOf (t / b + 1) 0 = stOf (t / b) b := by
        have h0 : stOf (t / b + 1) 0 = (seqPer (t / b + 1)).val :=
          (hcoset_sweep (seqPer (t / b + 1)).val
            (seqPer (t / b + 1)).property).choose_spec.choose_spec.1
        have hiter : (seqPer (t / b + 1)).val = stOf (t / b) b := by
          change (nextPer^[t / b + 1] ⟨u₀, hu₀_per⟩).val = stOf (t / b) b
          rw [Function.iterate_succ_apply']
        exact h0.trans hiter
      rw [hdm.1, hdm.2, hstart_next]
      exact hstep
  have hbad : ∀ t, ss t ∉ Legitimate := fun t =>
    (hcoset_sweep (seqPer (t / b)).val (seqPer (t / b)).property).choose_spec.choose_spec.2.2.2
      (t % b) (Nat.mod_lt t hb_pos)
  exact not_selfStabilizing_of_omegaExecution hexec hbad hss

/-- Scheduler-scoped enabled-move step towards [Dijkstra][Dijkstra1973] (`EWD391`) in the
simultaneous atomic-subset model `π.distLTS`, and not `EWD391`'s fair-command impossibility
endpoint: on a composite ring of size `a * b` (`2 ≤ a`, `2 ≤ b`) over a nonempty state type, no
uniform deterministic ring protocol satisfies `SelfStabilizing (π.distLTS (a * b)) Legitimate` for
any `Legitimate ⊆ π.UniquePrivilege (a * b)`. -/
theorem not_uniform_distEnabledMove_selfStabilizing_composite_ring {State : Type*} [Nonempty State]
    {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) [NeZero (a * b)]
    (π : UniformRingProtocol State) {Legitimate : Set (Fin (a * b) → State)}
    (hleg : Legitimate ⊆ π.UniquePrivilege (a * b)) :
    ¬ SelfStabilizing (π.distLTS (a * b)) Legitimate := by
  intro hss
  have hno_term_central : ∀ s, ¬ (π.centralLTS (a * b)).IsTerminal s := by
    intro s hterm
    obtain ⟨S, s', hne, hpriv, _⟩ := hss.exists_tr s
    obtain ⟨i, hi⟩ := hne
    exact hterm i (Function.update s i (π.nextVal s i)) ⟨hpriv i hi, rfl⟩
  have hsub : ∀ ⦃s i s'⦄, (π.centralLTS (a * b)).Tr s i s' →
      ∃ S, (π.distLTS (a * b)).Tr s S s' := by
    rintro s i _ ⟨hpriv, rfl⟩
    refine ⟨{i}, Finset.singleton_nonempty i, by simp [hpriv], ?_⟩
    funext j
    by_cases hji : j = i
    · subst hji; simp
    · simp [hji]
  exact not_uniform_enabledMove_selfStabilizing_composite_ring ha hb π hleg
    (SelfStabilizing.of_subLTS hss hsub hno_term_central)

end Cslib.Distributed.SelfStabilization
