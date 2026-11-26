/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Unreliable Failure Detector Classes and Inclusion Hierarchy

Formalizes crash failure patterns, suspect-set failure detector histories, completeness and accuracy
properties, the eight failure detector classes of [Chandra and Toueg, §§2.1–2.4][ChandraToueg1996],
and the `Ω` eventual-leader history predicate and pure history-map step
`LeaderHistory.toDetectorHistory` toward #7503 (after
[Chandra, Hadzilacos and Toueg, §5][ChandraHadzilacosToueg1996]; their asynchronous automaton
transformation `T_{Ω → ◇W}` is not formalized here).

## Mathematical overview

Over a process type `P` and discrete global clock ticks `t : ℕ`:

* A `FailurePattern P` is a monotone map `F : ℕ → Finset P` recording the processes that have
  crashed through time `t` (`t ≤ t' → F t ⊆ F t'`), inducing `F.Crashed` and `F.Correct`
  ([Chandra and Toueg, §2.1, p. 231][ChandraToueg1996]). When `P` is finite, `F t` stabilizes to
  `F.Crashed` after finitely many ticks (`FailurePattern.exists_stabilize`).
* A `DetectorHistory P` (`P → ℕ → Finset P`) assigns to each process `p` and tick `t` the finite set
  `H p t` of processes that `p` currently suspects to have crashed
  ([§2.2, pp. 231–232][ChandraToueg1996]).
* Pairing the two completeness properties (`StrongCompleteness`, `WeakCompleteness`) with the four
  accuracy properties (`StrongAccuracy`, `WeakAccuracy`, `EventualStrongAccuracy`,
  `EventualWeakAccuracy`) yields the eight classes `P, S, ◇P, ◇S, Q, W, ◇Q, ◇W`
  ([§2.4, Figure 1, p. 234][ChandraToueg1996]). On finite `P`, the correct-process and alive-process
  formulations of eventual accuracy coincide (`eventualStrongAccuracy_iff_alive`,
  `eventualWeakAccuracy_iff_alive`, characterizing the §2.3 definitions on p. 233).
* Before distributed gossip reduction (see
  `CslibFrontier.Computability.Distributed.FailureDetectors.Reduction`), raw history inclusion over
  admissible failure patterns (`F.Correct.Nonempty`) forms a 3-dimensional Boolean lattice
  `DetectorClass` (`⊥ = P`, `⊤ = ◇W`). On `3 ≤ Fintype.card P`, raw history implication holds if
  and only if `c₁ ≤ c₂` in that cube (`DetectorClass.forall_sat_imp_iff_le`), whereas on
  `Fintype.card P ≤ 2` weak and strong completeness coincide
  (`weakCompleteness_iff_strongCompleteness_of_card_le_two`).

## Main definitions

* `Cslib.Distributed.FailureDetectors.FailurePattern`, `FailurePattern.Crashed`,
  `FailurePattern.Correct`: monotone crash patterns and crashed/correct process sets.
* `Cslib.Distributed.FailureDetectors.DetectorHistory`: suspect-set failure detector histories.
* `Cslib.Distributed.FailureDetectors.StrongCompleteness`, `WeakCompleteness`, `StrongAccuracy`,
  `WeakAccuracy`, `EventualStrongAccuracy`, `EventualWeakAccuracy`: completeness and accuracy
  predicates ([Chandra and Toueg, §2.3, pp. 232–233][ChandraToueg1996]).
* `Cslib.Distributed.FailureDetectors.IsPerfect`, `IsStrong`, `IsEventuallyPerfect`,
  `IsEventuallyStrong`, `IsQuasiPerfect`, `IsWeak`, `IsEventuallyQuasiPerfect`, `IsEventuallyWeak`:
  the eight Chandra–Toueg classes ([§2.4, Figure 1, p. 234][ChandraToueg1996]).
* `Cslib.Distributed.FailureDetectors.DetectorClass`: enum of the eight classes equipped with its
  product Boolean lattice structure (`⊥ = .P`, `⊤ = .EW`) and satisfaction relation `Sat`.
* `Cslib.Distributed.FailureDetectors.LeaderHistory`, `IsEventuallyLeader`,
  `LeaderHistory.toDetectorHistory`: the `Ω` eventual-leader history predicate and pure history-map
  step `H p t = univ \ {L p t}` toward #7503 (after
  [Chandra, Hadzilacos and Toueg, §5, p. 694][ChandraHadzilacosToueg1996]).

## Main results

* `Cslib.Distributed.FailureDetectors.FailurePattern.exists_stabilize`: interface characterization
  on finite `P` showing every `FailurePattern P` stabilizes to `F.Crashed` at a finite tick `t₀`.
* `Cslib.Distributed.FailureDetectors.eventualStrongAccuracy_iff_alive`,
  `Cslib.Distributed.FailureDetectors.eventualWeakAccuracy_iff_alive`: interface characterizations
  equating the `F.Correct` and alive-at-`t'` formulations of eventual accuracy on finite `P`.
* `Cslib.Distributed.FailureDetectors.DetectorClass.sat_mono`,
  `Cslib.Distributed.FailureDetectors.DetectorClass.forall_sat_imp_iff_le`: original soundness and
  exact completeness (`3 ≤ Fintype.card P`) of the 8-class raw-history inclusion lattice, supported
  by explicit separating histories (`exists_isEventuallyPerfect_not_isWeakAccuracy`,
  `exists_isStrong_not_isEventualStrongAccuracy`,
  `exists_isQuasiPerfect_not_isStrongCompleteness`).
* `Cslib.Distributed.FailureDetectors.weakCompleteness_iff_strongCompleteness_of_card_le_two`:
  original collapse of weak and strong completeness when `Fintype.card P ≤ 2` and
  `F.Correct.Nonempty`.
* `Cslib.Distributed.FailureDetectors.IsEventuallyLeader.toDetectorHistory_isEventuallyStrong`:
  pure history-map step `Ω → ◇S` for #7503 (after
  [Chandra, Hadzilacos and Toueg, Theorem 5.1, p. 694][ChandraHadzilacosToueg1996]).

## References

* [T. D. Chandra and S. Toueg, *Unreliable Failure Detectors for Reliable Distributed
  Systems*][ChandraToueg1996]
* [T. D. Chandra, V. Hadzilacos and S. Toueg, *The Weakest Failure Detector for Solving
  Consensus*][ChandraHadzilacosToueg1996]
-/

public section

namespace Cslib.Distributed.FailureDetectors

open Finset

/-! ### Failure patterns and finite-time crash stabilization -/

/-- A crash failure pattern over process set `P`
([Chandra and Toueg, §2.1, p. 231][ChandraToueg1996]): `atTime t` is the finite set of processes
that have crashed through global clock tick `t`, and crashed processes never recover (`mono`). -/
structure FailurePattern (P : Type*) where
  /-- Processes crashed through tick `t`. -/
  atTime : ℕ → Finset P
  /-- Crash monotonicity: `t ≤ t' → atTime t ⊆ atTime t'`. -/
  mono : Monotone atTime

namespace FailurePattern

variable {P : Type*}

instance : CoeFun (FailurePattern P) (fun _ => ℕ → Finset P) :=
  ⟨FailurePattern.atTime⟩

/-- Step-wise constructor from one-tick monotonicity `∀ t, f t ⊆ f (t + 1)`
([Chandra and Toueg, §2.1, p. 231][ChandraToueg1996]). -/
@[expose] def ofSucc (f : ℕ → Finset P) (h : ∀ t, f t ⊆ f (t + 1)) : FailurePattern P where
  atTime := f
  mono := monotone_nat_of_le_succ h

@[simp]
theorem ofSucc_apply (f : ℕ → Finset P) (h : ∀ t, f t ⊆ f (t + 1)) (t : ℕ) :
    ofSucc f h t = f t := rfl

/-- Static failure pattern in which `S` crashes at tick `0` and no other process ever crashes. -/
@[expose] def const (S : Finset P) : FailurePattern P where
  atTime _ := S
  mono := monotone_const

@[simp]
theorem const_apply (S : Finset P) (t : ℕ) : const S t = S := rfl

/-- If `p` has crashed by tick `t` and `t ≤ t'`, then `p` remains crashed at tick `t'`. -/
theorem mem_of_le (F : FailurePattern P) {t t' : ℕ} {p : P} (hle : t ≤ t') (hp : p ∈ F t) :
    p ∈ F t' :=
  F.mono hle hp

/-- Set of processes that crash at some finite tick in `F` (`crashed(F)` in
[Chandra and Toueg, §2.1, p. 231][ChandraToueg1996]). -/
@[expose] def Crashed (F : FailurePattern P) : Set P :=
  {p | ∃ t, p ∈ F t}

/-- Set of processes that never crash in `F` (`correct(F)` in
[Chandra and Toueg, §2.1, p. 231][ChandraToueg1996]). -/
@[expose] def Correct (F : FailurePattern P) : Set P :=
  {p | ∀ t, p ∉ F t}

@[simp]
theorem mem_crashed_iff (F : FailurePattern P) (p : P) :
    p ∈ F.Crashed ↔ ∃ t, p ∈ F t := Iff.rfl

@[simp]
theorem mem_correct_iff (F : FailurePattern P) (p : P) :
    p ∈ F.Correct ↔ ∀ t, p ∉ F t := Iff.rfl

theorem mem_correct_iff_notMem_crashed (F : FailurePattern P) (p : P) :
    p ∈ F.Correct ↔ p ∉ F.Crashed := by
  simp only [mem_correct_iff, mem_crashed_iff, not_exists]

theorem mem_crashed_iff_notMem_correct (F : FailurePattern P) (p : P) :
    p ∈ F.Crashed ↔ p ∉ F.Correct := by
  rw [mem_correct_iff_notMem_crashed, Classical.not_not]

@[simp]
theorem crashed_const (S : Finset P) : (const S).Crashed = (S : Set P) := by
  ext p
  simp only [mem_crashed_iff, const_apply, exists_const, mem_coe]

@[simp]
theorem correct_const (S : Finset P) : (const S).Correct = (S : Set P)ᶜ := by
  ext p
  simp only [mem_correct_iff, const_apply, forall_const, Set.mem_compl_iff, mem_coe]

/-- Interface characterization of `FailurePattern` on a finite process set `P` (capturing the
stabilization remark in [Chandra and Toueg, §2.3, p. 233][ChandraToueg1996]): there is a tick `t₀`
from which onward `F t` contains every process in `F.Crashed` (equivalently
`p ∉ F t ↔ p ∈ F.Correct`). -/
theorem exists_stabilize [Finite P] (F : FailurePattern P) :
    ∃ t₀, ∀ t, t₀ ≤ t → (∀ p, p ∈ F t ↔ p ∈ F.Crashed) ∧ (∀ p, p ∉ F t ↔ p ∈ F.Correct) := by
  classical
  let _ := Fintype.ofFinite P
  let cTime : P → ℕ := fun p => if h : p ∈ F.Crashed then h.choose else 0
  refine ⟨Finset.univ.sup cTime, fun t ht => ?_⟩
  have hcrashed : ∀ p, p ∈ F t ↔ p ∈ F.Crashed := fun p => by
    refine ⟨fun hp => ⟨t, hp⟩, fun hp => F.mem_of_le (le_trans ?_ ht) hp.choose_spec⟩
    simpa only [cTime, hp, ↓reduceDIte] using Finset.le_sup (f := cTime) (Finset.mem_univ p)
  exact ⟨hcrashed, fun p => by rw [hcrashed p, ← mem_correct_iff_notMem_crashed]⟩

/-- If `∀ t, (F t).card ≤ bound` on finite `P`, then at least `Fintype.card P - bound` processes
are correct in `F` (in particular, `F.Correct.Nonempty` whenever `bound < Fintype.card P`). -/
theorem card_correct_ge_of_card_le [Fintype P] (F : FailurePattern P) {bound : ℕ}
    (hF : ∀ t, (F t).card ≤ bound) :
    ∃ C : Finset P, (C : Set P) = F.Correct ∧ Fintype.card P - bound ≤ C.card := by
  classical
  obtain ⟨t₀, ht₀⟩ := F.exists_stabilize
  refine ⟨Finset.univ \ F t₀, ?_, ?_⟩
  · ext p
    simp only [mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and, (ht₀ t₀ le_rfl).2]
  · rw [Finset.card_univ_sdiff]
    exact Nat.sub_le_sub_left (hF t₀) _

theorem correct_nonempty_of_card_lt [Fintype P] (F : FailurePattern P) {bound : ℕ}
    (hF : ∀ t, (F t).card ≤ bound) (hlt : bound < Fintype.card P) :
    F.Correct.Nonempty := by
  obtain ⟨C, hC, hcard⟩ := F.card_correct_ge_of_card_le hF
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < C.card)
  exact ⟨p, hC ▸ hp⟩

end FailurePattern

/-! ### Failure detector histories, completeness, and accuracy -/

/-- A suspect-set failure detector history ([Chandra and Toueg, §2.2, p. 231][ChandraToueg1996]):
`q ∈ H p t` means process `p`'s local detector module suspects process `q` at clock tick `t`. -/
abbrev DetectorHistory (P : Type*) := P → ℕ → Finset P

section Properties

variable {P : Type*}

/-- **Strong completeness** ([Chandra and Toueg, §2.3, p. 232][ChandraToueg1996]): eventually every
process that crashes is permanently suspected by every correct process. -/
@[expose] def StrongCompleteness (F : FailurePattern P) (H : DetectorHistory P) : Prop :=
  ∃ t, ∀ p ∈ F.Crashed, ∀ q ∈ F.Correct, ∀ t', t ≤ t' → p ∈ H q t'

/-- **Weak completeness** ([Chandra and Toueg, §2.3, p. 232][ChandraToueg1996]): eventually every
process that crashes is permanently suspected by some correct process. -/
@[expose] def WeakCompleteness (F : FailurePattern P) (H : DetectorHistory P) : Prop :=
  ∃ t, ∀ p ∈ F.Crashed, ∃ q ∈ F.Correct, ∀ t', t ≤ t' → p ∈ H q t'

/-- **Strong accuracy** ([Chandra and Toueg, §2.3, p. 232][ChandraToueg1996]): no process is
suspected before it crashes (`∀ t, ∀ p ∉ F t, ∀ q ∉ F t, p ∉ H q t`). -/
@[expose] def StrongAccuracy (F : FailurePattern P) (H : DetectorHistory P) : Prop :=
  ∀ t, ∀ p ∉ F t, ∀ q ∉ F t, p ∉ H q t

/-- **Weak accuracy** ([Chandra and Toueg, §2.3, p. 233][ChandraToueg1996]): some correct process
is never suspected by any non-crashed process. -/
@[expose] def WeakAccuracy (F : FailurePattern P) (H : DetectorHistory P) : Prop :=
  ∃ p ∈ F.Correct, ∀ t, ∀ q ∉ F t, p ∉ H q t

/-- **Eventual strong accuracy** ([Chandra and Toueg, §2.3, p. 233][ChandraToueg1996]): there is a
time after which correct processes are never suspected by any correct process. -/
@[expose] def EventualStrongAccuracy (F : FailurePattern P) (H : DetectorHistory P) : Prop :=
  ∃ t, ∀ t', t ≤ t' → ∀ p ∈ F.Correct, ∀ q ∈ F.Correct, p ∉ H q t'

/-- **Eventual weak accuracy** ([Chandra and Toueg, §2.3, p. 233][ChandraToueg1996]): there is a
time after which some correct process is never suspected by any correct process. -/
@[expose] def EventualWeakAccuracy (F : FailurePattern P) (H : DetectorHistory P) : Prop :=
  ∃ t, ∃ p ∈ F.Correct, ∀ t', t ≤ t' → ∀ q ∈ F.Correct, p ∉ H q t'

/-! #### Equivalence of alive-process and correct-process eventual accuracy on finite `P` -/

/-- Interface characterization of `EventualStrongAccuracy` on finite `P` (capturing the definition
equivalence noted in [Chandra and Toueg, §2.3, p. 233][ChandraToueg1996]): quantifying over
`F.Correct` is equivalent to quantifying over processes alive at `t'` (`p ∉ F t'`, `q ∉ F t'`). -/
theorem eventualStrongAccuracy_iff_alive [Finite P] (F : FailurePattern P)
    (H : DetectorHistory P) :
    EventualStrongAccuracy F H ↔ ∃ t, ∀ t', t ≤ t' → ∀ p ∉ F t', ∀ q ∉ F t', p ∉ H q t' := by
  refine ⟨fun ⟨t₁, ht₁⟩ => ?_,
    fun ⟨t, ht⟩ => ⟨t, fun t' ht' p hp q hq => ht t' ht' p (hp t') q (hq t')⟩⟩
  obtain ⟨t₀, ht₀⟩ := F.exists_stabilize
  refine ⟨max t₁ t₀, fun t' ht' p hp q hq => ?_⟩
  have hstab := (ht₀ t' ((le_max_right t₁ t₀).trans ht')).2
  exact ht₁ t' ((le_max_left t₁ t₀).trans ht') p (hstab p |>.mp hp) q (hstab q |>.mp hq)

/-- Interface characterization of `EventualWeakAccuracy` on finite `P` (analogous to
`eventualStrongAccuracy_iff_alive`, [Chandra and Toueg, §2.3, p. 233][ChandraToueg1996]):
quantifying over correct observers `q ∈ F.Correct` is equivalent to quantifying over alive observers
`q ∉ F t'`. -/
theorem eventualWeakAccuracy_iff_alive [Finite P] (F : FailurePattern P)
    (H : DetectorHistory P) :
    EventualWeakAccuracy F H ↔
      ∃ t, ∃ p ∈ F.Correct, ∀ t', t ≤ t' → ∀ q ∉ F t', p ∉ H q t' := by
  refine ⟨fun ⟨t₁, p, hp, ht₁⟩ => ?_,
    fun ⟨t, p, hp, ht⟩ => ⟨t, p, hp, fun t' ht' q hq => ht t' ht' q (hq t')⟩⟩
  obtain ⟨t₀, ht₀⟩ := F.exists_stabilize
  refine ⟨max t₁ t₀, p, hp, fun t' ht' q hq => ?_⟩
  have hstab := (ht₀ t' ((le_max_right t₁ t₀).trans ht')).2
  exact ht₁ t' ((le_max_left t₁ t₀).trans ht') q (hstab q |>.mp hq)

/-! #### Implications among completeness and accuracy properties -/

theorem StrongCompleteness.toWeak {F : FailurePattern P} {H : DetectorHistory P}
    (h : StrongCompleteness F H) (hcorr : F.Correct.Nonempty) : WeakCompleteness F H :=
  let ⟨q₀, hq₀⟩ := hcorr
  h.imp fun _ ht p hp => ⟨q₀, hq₀, ht p hp q₀ hq₀⟩

theorem StrongAccuracy.toWeak {F : FailurePattern P} {H : DetectorHistory P}
    (h : StrongAccuracy F H) (hcorr : F.Correct.Nonempty) : WeakAccuracy F H :=
  let ⟨p₀, hp₀⟩ := hcorr
  ⟨p₀, hp₀, fun t q hq => h t p₀ (hp₀ t) q hq⟩

theorem StrongAccuracy.toEventualStrong {F : FailurePattern P} {H : DetectorHistory P}
    (h : StrongAccuracy F H) : EventualStrongAccuracy F H :=
  ⟨0, fun t' _ p hp q hq => h t' p (hp t') q (hq t')⟩

theorem WeakAccuracy.toEventualWeak {F : FailurePattern P} {H : DetectorHistory P}
    (h : WeakAccuracy F H) : EventualWeakAccuracy F H :=
  let ⟨p, hp, hns⟩ := h
  ⟨0, p, hp, fun t' _ q hq => hns t' q (hq t')⟩

theorem WeakAccuracy.correct_nonempty {F : FailurePattern P} {H : DetectorHistory P}
    (h : WeakAccuracy F H) : F.Correct.Nonempty :=
  h.imp fun _ => And.left

theorem EventualWeakAccuracy.correct_nonempty {F : FailurePattern P} {H : DetectorHistory P}
    (h : EventualWeakAccuracy F H) : F.Correct.Nonempty :=
  let ⟨_, p, hp, _⟩ := h
  ⟨p, hp⟩

theorem EventualStrongAccuracy.toEventualWeak {F : FailurePattern P} {H : DetectorHistory P}
    (h : EventualStrongAccuracy F H) (hcorr : F.Correct.Nonempty) : EventualWeakAccuracy F H :=
  let ⟨t, ht⟩ := h
  let ⟨p₀, hp₀⟩ := hcorr
  ⟨t, p₀, hp₀, fun t' ht' q hq => ht t' ht' p₀ hp₀ q hq⟩

/-! ### The eight Chandra–Toueg failure detector classes -/

/-- **Perfect (`P`)** failure detector history: strong completeness and strong accuracy
([Chandra and Toueg, §2.4, Figure 1, p. 234][ChandraToueg1996]). -/
@[expose] def IsPerfect (F : FailurePattern P) (H : DetectorHistory P) : Prop :=
  StrongCompleteness F H ∧ StrongAccuracy F H

/-- **Strong (`S`)** failure detector history: strong completeness and weak accuracy
([Chandra and Toueg, §2.4, Figure 1, p. 234][ChandraToueg1996]). -/
@[expose] def IsStrong (F : FailurePattern P) (H : DetectorHistory P) : Prop :=
  StrongCompleteness F H ∧ WeakAccuracy F H

/-- **Eventually Perfect (`◇P`)** failure detector history: strong completeness and eventual strong
accuracy ([Chandra and Toueg, §2.4, Figure 1, p. 234][ChandraToueg1996]). -/
@[expose] def IsEventuallyPerfect (F : FailurePattern P) (H : DetectorHistory P) : Prop :=
  StrongCompleteness F H ∧ EventualStrongAccuracy F H

/-- **Eventually Strong (`◇S`)** failure detector history: strong completeness and eventual weak
accuracy ([Chandra and Toueg, §2.4, Figure 1, p. 234][ChandraToueg1996]). -/
@[expose] def IsEventuallyStrong (F : FailurePattern P) (H : DetectorHistory P) : Prop :=
  StrongCompleteness F H ∧ EventualWeakAccuracy F H

/-- **Quasi-Perfect (`Q`)** failure detector history: weak completeness and strong accuracy
(denoted `𝒬` without an English adjective in
[Chandra and Toueg, §2.4, Figure 1, p. 234][ChandraToueg1996]). -/
@[expose] def IsQuasiPerfect (F : FailurePattern P) (H : DetectorHistory P) : Prop :=
  WeakCompleteness F H ∧ StrongAccuracy F H

/-- **Weak (`W`)** failure detector history: weak completeness and weak accuracy
([Chandra and Toueg, §2.4, Figure 1, p. 234][ChandraToueg1996]). -/
@[expose] def IsWeak (F : FailurePattern P) (H : DetectorHistory P) : Prop :=
  WeakCompleteness F H ∧ WeakAccuracy F H

/-- **Eventually Quasi-Perfect (`◇Q`)** failure detector history: weak completeness and eventual
strong accuracy (denoted `◇𝒬` without an English adjective in
[Chandra and Toueg, §2.4, Figure 1, p. 234][ChandraToueg1996]). -/
@[expose] def IsEventuallyQuasiPerfect (F : FailurePattern P) (H : DetectorHistory P) : Prop :=
  WeakCompleteness F H ∧ EventualStrongAccuracy F H

/-- **Eventually Weak (`◇W`)** failure detector history: weak completeness and eventual weak
accuracy ([Chandra and Toueg, §2.4, Figure 1, p. 234][ChandraToueg1996];
[Chandra, Hadzilacos and Toueg, §2.2, pp. 689–690][ChandraHadzilacosToueg1996]). -/
@[expose] def IsEventuallyWeak (F : FailurePattern P) (H : DetectorHistory P) : Prop :=
  WeakCompleteness F H ∧ EventualWeakAccuracy F H

/-! #### Covering inclusions among the eight classes -/

theorem IsPerfect.toStrong {F : FailurePattern P} {H : DetectorHistory P}
    (h : IsPerfect F H) (hcorr : F.Correct.Nonempty) : IsStrong F H :=
  ⟨h.1, h.2.toWeak hcorr⟩

theorem IsPerfect.toEventuallyPerfect {F : FailurePattern P} {H : DetectorHistory P}
    (h : IsPerfect F H) : IsEventuallyPerfect F H :=
  ⟨h.1, h.2.toEventualStrong⟩

theorem IsPerfect.toQuasiPerfect {F : FailurePattern P} {H : DetectorHistory P}
    (h : IsPerfect F H) (hcorr : F.Correct.Nonempty) : IsQuasiPerfect F H :=
  ⟨h.1.toWeak hcorr, h.2⟩

theorem IsStrong.toWeak {F : FailurePattern P} {H : DetectorHistory P}
    (h : IsStrong F H) : IsWeak F H :=
  ⟨h.1.toWeak h.2.correct_nonempty, h.2⟩

theorem IsStrong.toEventuallyStrong {F : FailurePattern P} {H : DetectorHistory P}
    (h : IsStrong F H) : IsEventuallyStrong F H :=
  ⟨h.1, h.2.toEventualWeak⟩

theorem IsEventuallyPerfect.toEventuallyStrong {F : FailurePattern P} {H : DetectorHistory P}
    (h : IsEventuallyPerfect F H) (hcorr : F.Correct.Nonempty) : IsEventuallyStrong F H :=
  ⟨h.1, h.2.toEventualWeak hcorr⟩

theorem IsEventuallyPerfect.toEventuallyQuasiPerfect {F : FailurePattern P} {H : DetectorHistory P}
    (h : IsEventuallyPerfect F H) (hcorr : F.Correct.Nonempty) : IsEventuallyQuasiPerfect F H :=
  ⟨h.1.toWeak hcorr, h.2⟩

theorem IsEventuallyStrong.toEventuallyWeak {F : FailurePattern P} {H : DetectorHistory P}
    (h : IsEventuallyStrong F H) : IsEventuallyWeak F H :=
  ⟨h.1.toWeak h.2.correct_nonempty, h.2⟩

theorem IsQuasiPerfect.toWeak {F : FailurePattern P} {H : DetectorHistory P}
    (h : IsQuasiPerfect F H) (hcorr : F.Correct.Nonempty) : IsWeak F H :=
  ⟨h.1, h.2.toWeak hcorr⟩

theorem IsQuasiPerfect.toEventuallyQuasiPerfect {F : FailurePattern P} {H : DetectorHistory P}
    (h : IsQuasiPerfect F H) : IsEventuallyQuasiPerfect F H :=
  ⟨h.1, h.2.toEventualStrong⟩

theorem IsWeak.toEventuallyWeak {F : FailurePattern P} {H : DetectorHistory P}
    (h : IsWeak F H) : IsEventuallyWeak F H :=
  ⟨h.1, h.2.toEventualWeak⟩

theorem IsEventuallyQuasiPerfect.toEventuallyWeak {F : FailurePattern P} {H : DetectorHistory P}
    (h : IsEventuallyQuasiPerfect F H) (hcorr : F.Correct.Nonempty) : IsEventuallyWeak F H :=
  ⟨h.1, h.2.toEventualWeak hcorr⟩

end Properties

/-! ### Complete Boolean lattice of the eight detector classes -/

/-- Enumeration of the eight Chandra–Toueg failure detector classes
([Chandra and Toueg, §2.4, Figure 1, p. 234][ChandraToueg1996]), ordered by raw-history set
inclusion (`⊥ = .P`, `⊤ = .EW`). -/
inductive DetectorClass where
  /-- `P`: Perfect (`StrongCompleteness ∧ StrongAccuracy`). -/
  | P
  /-- `S`: Strong (`StrongCompleteness ∧ WeakAccuracy`). -/
  | S
  /-- `◇P`: Eventually Perfect (`StrongCompleteness ∧ EventualStrongAccuracy`). -/
  | EP
  /-- `◇S`: Eventually Strong (`StrongCompleteness ∧ EventualWeakAccuracy`). -/
  | ES
  /-- `Q`: Quasi-Perfect (`WeakCompleteness ∧ StrongAccuracy`). -/
  | Q
  /-- `W`: Weak (`WeakCompleteness ∧ WeakAccuracy`). -/
  | W
  /-- `◇Q`: Eventually Quasi-Perfect (`WeakCompleteness ∧ EventualStrongAccuracy`). -/
  | EQ
  /-- `◇W`: Eventually Weak (`WeakCompleteness ∧ EventualWeakAccuracy`). -/
  | EW
  deriving @[expose] DecidableEq

namespace DetectorClass

/-- Coordinates `(weakCompleteness, eventualAccuracy, weakScope)` in the 3-cube `Bool × Bool × Bool`
with `false ≤ true`, sending `.P ↦ (false, false, false)` and `.EW ↦ (true, true, true)`. -/
@[expose] def toCube : DetectorClass → Bool × Bool × Bool
  | .P => (false, false, false)
  | .S => (false, false, true)
  | .EP => (false, true, false)
  | .ES => (false, true, true)
  | .Q => (true, false, false)
  | .W => (true, false, true)
  | .EQ => (true, true, false)
  | .EW => (true, true, true)

/-- Inverse of `DetectorClass.toCube`. -/
@[expose] def ofCube : Bool × Bool × Bool → DetectorClass
  | (false, false, false) => .P
  | (false, false, true) => .S
  | (false, true, false) => .EP
  | (false, true, true) => .ES
  | (true, false, false) => .Q
  | (true, false, true) => .W
  | (true, true, false) => .EQ
  | (true, true, true) => .EW

@[simp]
theorem ofCube_toCube (c : DetectorClass) : ofCube (toCube c) = c := by
  cases c <;> rfl

@[simp]
theorem toCube_ofCube (b : Bool × Bool × Bool) : toCube (ofCube b) = b := by
  rcases b with ⟨⟨⟩ | ⟨⟩, ⟨⟩ | ⟨⟩, ⟨⟩ | ⟨⟩⟩ <;> rfl

/-- Bijection between `DetectorClass` and the 3-cube `Bool × Bool × Bool`. -/
@[expose] def equivCube : DetectorClass ≃ Bool × Bool × Bool where
  toFun := toCube
  invFun := ofCube
  left_inv := ofCube_toCube
  right_inv := toCube_ofCube

instance : PartialOrder DetectorClass :=
  PartialOrder.lift toCube equivCube.injective

instance (a b : DetectorClass) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (toCube a ≤ toCube b))

instance : DistribLattice DetectorClass where
  sup a b := ofCube (toCube a ⊔ toCube b)
  le_sup_left a b := by change toCube a ≤ _; rw [toCube_ofCube]; exact le_sup_left
  le_sup_right a b := by change toCube b ≤ _; rw [toCube_ofCube]; exact le_sup_right
  sup_le a b c hac hbc := by change _ ≤ toCube c; rw [toCube_ofCube]; exact sup_le hac hbc
  inf a b := ofCube (toCube a ⊓ toCube b)
  inf_le_left a b := by change _ ≤ toCube a; rw [toCube_ofCube]; exact inf_le_left
  inf_le_right a b := by change _ ≤ toCube b; rw [toCube_ofCube]; exact inf_le_right
  le_inf a b c hab hac := by change toCube a ≤ _; rw [toCube_ofCube]; exact le_inf hab hac
  le_sup_inf a b c := by
    cases a <;> cases b <;> cases c <;> decide

instance : BoundedOrder DetectorClass where
  top := .EW
  le_top a := by cases a <;> decide
  bot := .P
  bot_le a := by cases a <;> decide

@[simp]
theorem bot_eq : (⊥ : DetectorClass) = .P := rfl

@[simp]
theorem top_eq : (⊤ : DetectorClass) = .EW := rfl

theorem le_iff_toCube_le (c₁ c₂ : DetectorClass) : c₁ ≤ c₂ ↔ toCube c₁ ≤ toCube c₂ := Iff.rfl

/-- Satisfaction predicate mapping each `DetectorClass` to its corresponding Chandra–Toueg property
pair on `(F, H)`. -/
@[expose] def Sat {P : Type*} : DetectorClass → FailurePattern P → DetectorHistory P → Prop
  | .P, F, H => IsPerfect F H
  | .S, F, H => IsStrong F H
  | .EP, F, H => IsEventuallyPerfect F H
  | .ES, F, H => IsEventuallyStrong F H
  | .Q, F, H => IsQuasiPerfect F H
  | .W, F, H => IsWeak F H
  | .EQ, F, H => IsEventuallyQuasiPerfect F H
  | .EW, F, H => IsEventuallyWeak F H

/-- Original soundness of the 8-class raw-history inclusion lattice: over any admissible failure
pattern (`F.Correct.Nonempty`), `c₁ ≤ c₂` implies `c₁.Sat F H → c₂.Sat F H`. -/
theorem sat_mono {P : Type*} {c₁ c₂ : DetectorClass} (hle : c₁ ≤ c₂)
    {F : FailurePattern P} (hcorr : F.Correct.Nonempty) {H : DetectorHistory P}
    (hsat : c₁.Sat F H) : c₂.Sat F H := by
  -- Weaken the completeness and accuracy components separately.
  cases c₁ <;> cases c₂ <;> (try exact absurd hle (by decide)) <;>
    obtain ⟨hc, ha⟩ := hsat <;> refine ⟨by first | exact hc | exact hc.toWeak hcorr, ?_⟩ <;>
    first
      | exact ha | exact ha.toWeak hcorr | exact ha.toEventualStrong | exact ha.toEventualWeak
      | exact ha.toEventualWeak hcorr | exact (ha.toWeak hcorr).toEventualWeak

end DetectorClass

/-! ### Explicit separating detector histories and collapse for `|P| ≤ 2` -/

/-- Original two-process boundary characterization: when at most two processes exist
(`Fintype.card P ≤ 2`) and at least one is correct, weak and strong completeness coincide as raw
history properties (either no process crashes or the unique correct process is the sole witness in
`F.Correct`). -/
theorem weakCompleteness_iff_strongCompleteness_of_card_le_two {P : Type*} [Fintype P]
    (hcard : Fintype.card P ≤ 2) {F : FailurePattern P} (hcorr : F.Correct.Nonempty)
    (H : DetectorHistory P) :
    WeakCompleteness F H ↔ StrongCompleteness F H := by
  refine ⟨fun ⟨t, ht⟩ => ⟨t, fun p hp q hq t' ht' => ?_⟩, fun h => h.toWeak hcorr⟩
  obtain ⟨q', hq', hsusp⟩ := ht p hp
  suffices q = q' from this ▸ hsusp t' ht'
  by_contra hne
  classical
  have hqp : q ≠ p := fun heq => F.mem_correct_iff_notMem_crashed q |>.mp hq (heq ▸ hp)
  have hq'p : q' ≠ p := fun heq => F.mem_correct_iff_notMem_crashed q' |>.mp hq' (heq ▸ hp)
  have hle := Finset.card_le_univ ({q, q', p} : Finset P)
  rw [Finset.card_eq_three.mpr ⟨q, q', p, hne, hqp, hq'p, rfl⟩] at hle
  omega

/-- **Original raw-history coatom witness 1 (`◇P \ W`):** on any finite nonempty `P`, suspecting
everyone at tick `0` and nobody at ticks `t ≥ 1` under the crash-free pattern `const ∅` satisfies
`IsEventuallyPerfect` (hence `◇P, ◇S, ◇Q, ◇W`) while violating `WeakAccuracy` (hence `P, S, Q,
W`). -/
theorem exists_isEventuallyPerfect_not_isWeakAccuracy {P : Type*} [Finite P] [Nonempty P] :
    ∃ (F : FailurePattern P) (H : DetectorHistory P),
      F.Correct.Nonempty ∧ IsEventuallyPerfect F H ∧ ¬ WeakAccuracy F H := by
  let _ := Fintype.ofFinite P
  let F : FailurePattern P := FailurePattern.const ∅
  let H : DetectorHistory P := fun _ t => if t = 0 then Finset.univ else ∅
  obtain ⟨p₀⟩ := ‹Nonempty P›
  have hcorr : F.Correct.Nonempty := ⟨p₀, by simp [F]⟩
  exact ⟨F, H, hcorr,
    ⟨⟨0, fun p hp => by simp [F] at hp⟩,
     ⟨1, fun t' ht' _ _ _ _ => by simp [H, Nat.ne_of_gt ht']⟩⟩,
    fun ⟨p, _, hns⟩ => by simpa [H] using hns 0 p (by simp [F])⟩

/-- **Original raw-history coatom witness 2 (`S \ ◇Q`):** on any `[Nontrivial P]`, permanently
suspecting one fixed correct process `p₁` while never suspecting a distinct correct process
`p₀ ≠ p₁` under `const ∅` satisfies `IsStrong` (hence `S, W, ◇S, ◇W`) while violating
`EventualStrongAccuracy` (hence `P, ◇P, Q, ◇Q`). -/
theorem exists_isStrong_not_isEventualStrongAccuracy {P : Type*} [Nontrivial P] :
    ∃ (F : FailurePattern P) (H : DetectorHistory P),
      F.Correct.Nonempty ∧ IsStrong F H ∧ ¬ EventualStrongAccuracy F H := by
  classical
  obtain ⟨p₀, p₁, hne⟩ := exists_pair_ne P
  let F : FailurePattern P := FailurePattern.const ∅
  let H : DetectorHistory P := fun _ _ => {p₁}
  have hp₀ : p₀ ∈ F.Correct := by simp [F]
  have hp₁ : p₁ ∈ F.Correct := by simp [F]
  exact ⟨F, H, ⟨p₀, hp₀⟩,
    ⟨⟨0, fun p hp => by simp [F] at hp⟩, ⟨p₀, hp₀, fun _ _ _ => mem_singleton.not.mpr hne⟩⟩,
    fun ⟨t, ht⟩ => by simpa [H] using ht t le_rfl p₁ hp₁ p₀ hp₀⟩

/-- **Original raw-history coatom witness 3 (`Q \ ◇S`):** when `3 ≤ Fintype.card P`, crashing one
process `f` while one correct process `c₁` permanently suspects `f` and a second correct process
`c₂` never suspects anyone satisfies `IsQuasiPerfect` (hence `Q, W, ◇Q, ◇W`) while violating
`StrongCompleteness` (hence `P, S, ◇P, ◇S`) prior to gossip reduction. -/
theorem exists_isQuasiPerfect_not_isStrongCompleteness {P : Type*} [Fintype P]
    (hcard : 3 ≤ Fintype.card P) :
    ∃ (F : FailurePattern P) (H : DetectorHistory P),
      F.Correct.Nonempty ∧ IsQuasiPerfect F H ∧ ¬ StrongCompleteness F H := by
  classical
  let e := Fintype.equivFin P
  let c₁ : P := e.symm ⟨0, by omega⟩
  let c₂ : P := e.symm ⟨1, by omega⟩
  let f : P := e.symm ⟨2, by omega⟩
  have hc₁f : c₁ ≠ f := e.symm.injective.ne (by simp)
  have hc₂f : c₂ ≠ f := e.symm.injective.ne (by simp)
  have hc₂c₁ : c₂ ≠ c₁ := e.symm.injective.ne (by simp)
  let F : FailurePattern P := FailurePattern.const {f}
  let H : DetectorHistory P := fun q _ => if q = c₁ then {f} else ∅
  have hc₁ : c₁ ∈ F.Correct := by simp [F, hc₁f]
  refine ⟨F, H, ⟨c₁, hc₁⟩, ⟨?_, ?_⟩, ?_⟩
  · exact ⟨0, fun p hp => ⟨c₁, hc₁, fun _ _ => by simp_all [F, H]⟩⟩
  · intro t p hp q _
    by_cases hqc₁ : q = c₁ <;> simp_all [F, H]
  · rintro ⟨t, ht⟩
    simpa [H, hc₂c₁] using
      ht f ⟨0, mem_singleton_self f⟩ c₂ (fun _ => mt mem_singleton.mp hc₂f) t le_rfl

/-- **Original exact completeness of the 8-class raw-history lattice (`3 ≤ Fintype.card P`):** over
a type `P` with at least three processes, raw history inclusion `c₁.Sat F H → c₂.Sat F H` holds
across all admissible failure patterns `F` (`F.Correct.Nonempty`) if and only if `c₁ ≤ c₂` in
`DetectorClass`, establishing all 28 strict inclusions and all 28 non-inclusions among
`P, S, ◇P, ◇S, Q, W, ◇Q, ◇W` prior to distributed gossip reduction. -/
theorem DetectorClass.forall_sat_imp_iff_le {P : Type*} [Fintype P]
    (hcard : 3 ≤ Fintype.card P) (c₁ c₂ : DetectorClass) :
    (∀ (F : FailurePattern P), F.Correct.Nonempty → ∀ H, c₁.Sat F H → c₂.Sat F H) ↔ c₁ ≤ c₂ := by
  refine ⟨fun himp => ?_, fun hle _ hcorr _ hsat => DetectorClass.sat_mono hle hcorr hsat⟩
  have hNontriv : Nontrivial P := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hNonempty : Nonempty P := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨F_ep, H_ep, hcorr_ep, hEP, hnWA⟩ :=
    exists_isEventuallyPerfect_not_isWeakAccuracy (P := P)
  obtain ⟨F_s, H_s, hcorr_s, hS, hnESA⟩ :=
    exists_isStrong_not_isEventualStrongAccuracy (P := P)
  obtain ⟨F_q, H_q, hcorr_q, hQ, hnSC⟩ :=
    exists_isQuasiPerfect_not_isStrongCompleteness (P := P) hcard
  have hnSA_ep : ¬ StrongAccuracy F_ep H_ep := fun h => hnWA (h.toWeak hcorr_ep)
  have hnSA_s : ¬ StrongAccuracy F_s H_s := fun h => hnESA h.toEventualStrong
  rw [DetectorClass.le_iff_toCube_le]
  refine ⟨?_, ?_, ?_⟩
  · -- Coordinate 1 (`weakCompleteness`): test on `(F_q, H_q) ∈ Q \ ◇S`
    cases hc₁ : (c₁.toCube).1
    · exact Bool.false_le _
    · have hsat₂ := himp F_q hcorr_q H_q (DetectorClass.sat_mono (c₁ := .Q)
        (by cases c₁ <;> simp_all [le_iff_toCube_le, toCube]) hcorr_q hQ)
      cases c₂ <;> first | exact le_rfl | exact absurd hsat₂.1 hnSC
  · -- Coordinate 2 (`eventualAccuracy`): test on `(F_ep, H_ep) ∈ ◇P \ W`
    cases hc₁ : (c₁.toCube).2.1
    · exact Bool.false_le _
    · have hsat₂ := himp F_ep hcorr_ep H_ep (DetectorClass.sat_mono (c₁ := .EP)
        (by cases c₁ <;> simp_all [le_iff_toCube_le, toCube]) hcorr_ep hEP)
      cases c₂ <;>
        first | exact le_rfl | exact absurd hsat₂.2 hnSA_ep | exact absurd hsat₂.2 hnWA
  · -- Coordinate 3 (`weakScope`): test on `(F_s, H_s) ∈ S \ ◇Q`
    cases hc₁ : (c₁.toCube).2.2
    · exact Bool.false_le _
    · have hsat₂ := himp F_s hcorr_s H_s (DetectorClass.sat_mono (c₁ := .S)
        (by cases c₁ <;> simp_all [le_iff_toCube_le, toCube]) hcorr_s hS)
      cases c₂ <;>
        first | exact le_rfl | exact absurd hsat₂.2 hnSA_s | exact absurd hsat₂.2 hnESA

/-! ### The `Ω` Eventual-Leader Oracle and Complement Transformation ([CHT 1996, §5]) -/

/-- History of a single-leader oracle `Ω`
([Chandra, Hadzilacos and Toueg, §5, p. 694][ChandraHadzilacosToueg1996]): `L p t` is the single
process currently trusted by `p` at tick `t`. -/
abbrev LeaderHistory (P : Type*) := P → ℕ → P

/-- **`Ω` eventual-leader property**
([Chandra, Hadzilacos and Toueg, §5, p. 694][ChandraHadzilacosToueg1996]): there is a time after
which all correct processes permanently trust the same correct process `q*`. -/
@[expose] def IsEventuallyLeader {P : Type*} (F : FailurePattern P) (L : LeaderHistory P) : Prop :=
  ∃ t, ∃ q ∈ F.Correct, ∀ p ∈ F.Correct, ∀ t', t ≤ t' → L p t' = q

/-- Pure history-level complement map `H p t = univ \ {L p t}` (step for #7503, after `T_{Ω → ◇W}`
in [Chandra, Hadzilacos and Toueg, Theorem 5.1, p. 694][ChandraHadzilacosToueg1996]): at tick `t`,
process `p` suspects every process except its currently trusted leader `L p t`. -/
@[expose] def LeaderHistory.toDetectorHistory {P : Type*} [Fintype P] [DecidableEq P]
    (L : LeaderHistory P) : DetectorHistory P :=
  fun p t => Finset.univ.erase (L p t)

/-- Pure history-map step for #7503 (after the history map behind `T_{Ω → ◇W}` in
[Chandra, Hadzilacos and Toueg, Theorem 5.1, p. 694][ChandraHadzilacosToueg1996]; their full theorem
is stated over event-driven asynchronous automata `(F, H_Ω, I, S, T)`): suspecting
`univ \ {L p t}` via `LeaderHistory.toDetectorHistory` converts any `Ω` history `L` into an
`IsEventuallyStrong` (`◇S`) detector history. -/
theorem IsEventuallyLeader.toDetectorHistory_isEventuallyStrong {P : Type*}
    [Fintype P] [DecidableEq P] {F : FailurePattern P} {L : LeaderHistory P}
    (hL : IsEventuallyLeader F L) :
    IsEventuallyStrong F L.toDetectorHistory := by
  obtain ⟨t, qStar, hqStar, htrust⟩ := hL
  refine ⟨⟨t, fun p hp q hq t' ht' => ?_⟩, ⟨t, qStar, hqStar, fun t' ht' q hq => ?_⟩⟩
  · have hpne : p ≠ qStar := fun heq =>
      F.mem_correct_iff_notMem_crashed qStar |>.mp hqStar (heq ▸ hp)
    simp only [LeaderHistory.toDetectorHistory, htrust q hq t' ht', mem_erase, ne_eq, hpne,
      not_false_eq_true, mem_univ, and_self]
  · simp only [LeaderHistory.toDetectorHistory, htrust q hq t' ht', mem_erase, ne_eq, not_true,
      false_and, not_false_eq_true]

end Cslib.Distributed.FailureDetectors
