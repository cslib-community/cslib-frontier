/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.ApproxAgreement.Protocol
import Mathlib.Algebra.Order.Ring.Rat

/-! Unit-interval fixed-horizon approximate Byzantine agreement tests (checked as a `module` client
with ordinary imports): kernel-evaluated (`decide +kernel`) `ℚ` checks on `trimmed`, `midTrim`, and
`multisetMidTrim` (outlier rejection, permutation invariance, exact `(hi - lo) / 2` contraction
tightness, and the `Fin 5, t = 1` single-hop non-contraction witness showing `5t < n` is tight for
`asyncApproxProtocol`), concrete multi-round synchronous runs on `Fin 4, t = 1` against
equivocating and rushing adversaries, concrete multi-round asynchronous LTS traces on
`Fin 6, t = 1` (`R = 2`) with Byzantine equivocation, replay flooding, and out-of-order round
buffering, plus instantiations of all unit-interval solvability and `2 ≤ n ≤ 3t` impossibility
theorems. -/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.ApproxAgreement

open Cslib Cslib.Distributed.AsyncByzantine Cslib.Distributed.ApproxAgreement

/-! ### Part 1: Kernel-evaluated `trimmed`, `midTrim`, and `multisetMidTrim` over `ℚ` -/

-- Outlier rejection and permutation invariance on `ℚ`: extreme faulty values `-1000` and `1000`
-- are discarded when `t = 1`.
example :
    trimmed 1 ([-1000, 1, 0, 1000] : List ℚ) = [0, 1] ∧
    midTrim 1 ([-1000, 1, 0, 1000] : List ℚ) = 1 / 2 ∧
    midTrim 1 ([1000, 0, -1000, 1] : List ℚ) = 1 / 2 ∧
    multisetMidTrim 1 (Multiset.ofList ([1000, 0, -1000, 1] : List ℚ)) = 1 / 2 := by
  decide +kernel

-- Degenerate `xs.length ≤ 2 * t` fallback returns `0`.
example :
    trimmed 2 ([1, 2, 3, 4] : List ℚ) = [] ∧
    midTrim 2 ([1, 2, 3, 4] : List ℚ) = 0 := by
  decide +kernel

-- Tightness of `(hi - lo) / 2` in synchronous (`n = 4, t = 1`) and asynchronous (`n = 6, m = 5,
-- t = 1`) views: two honest recipients can differ by exactly `1 / 2` after one round.
example :
    let sync₁ : List ℚ := [0, 0, 1, -50]
    let sync₂ : List ℚ := [0, 0, 1, 50]
    let async₁ : List ℚ := [0, 0, 1, 1, -50]
    let async₂ : List ℚ := [0, 1, 1, 1, 50]
    midTrim 1 sync₁ = 0 ∧
    midTrim 1 sync₂ = 1 / 2 ∧
    |midTrim 1 sync₁ - midTrim 1 sync₂| = (1 - 0) / 2 ∧
    midTrim 1 async₁ = 1 / 2 ∧
    midTrim 1 async₂ = 1 ∧
    |midTrim 1 async₁ - midTrim 1 async₂| = (1 - 0) / 2 := by
  decide +kernel

-- Sharpness of `5 * t < |P|` for single-hop `midTrim 1` when `|P| = 5, t = 1` (`m = n - t = 4`):
-- with honest inputs `[0, 0, 1, 1]` and one equivocating sender, two recipients of `4` values can
-- see `[0, 0, 0, 1]` and `[0, 1, 1, 1]`, producing `0` and `1` (zero contraction).
example :
    midTrim 1 ([0, 0, 0, 1] : List ℚ) = 0 ∧
    midTrim 1 ([0, 1, 1, 1] : List ℚ) = 1 := by
  decide +kernel

/-! ### Part 2: Concrete synchronous executions on `Fin 4, t = 1` (`3 * 1 < 4`) -/

private def syncInp : Fin 4 → ℚ
  | 0 => 0
  | 1 => 1 / 2
  | 2 => 1
  | 3 => 999

-- Faulty process `3` equivocates every round, sending `-100` to `0, 1` and `+100` to `2`.
private def syncAdv (_r : ℕ) (_src : Fin 4) (dest : Fin 4) : ℚ :=
  if dest = 2 then 100 else -100

-- Kernel check across rounds `0, 1, 2, 3`: honest outputs stay in `[0, 1]` and contract by `1 / 2`
-- every round (`1 → 1/4 → 1/8 → 1/16`).
example :
    let π := syncApproxProtocol (Fin 4) ℚ 1
    let d := π.decision {3} syncAdv syncInp
    -- Round 0: `[0, 1/2, 1]`, spread `1`
    d 0 0 = 0 ∧ d 0 1 = 1 / 2 ∧ d 0 2 = 1 ∧
    -- Round 1: `0, 1` see `[-100, 0, 1/2, 1]` → `1/4`; `2` sees `[0, 1/2, 1, 100]` → `3/4`
    d 1 0 = 1 / 4 ∧ d 1 1 = 1 / 4 ∧ d 1 2 = 3 / 4 ∧
    |d 1 0 - d 1 2| ≤ 1 / 2 ∧
    -- Round 2: `0, 1` see `[-100, 1/4, 1/4, 3/4]` → `1/4`; `2` sees `[1/4, 1/4, 3/4, 100]` → `1/2`
    d 2 0 = 1 / 4 ∧ d 2 1 = 1 / 4 ∧ d 2 2 = 1 / 2 ∧
    |d 2 0 - d 2 2| ≤ 1 / 4 ∧
    -- Round 3: `0, 1` see `[-100, 1/4, 1/4, 1/2]` → `1/4`; `2` sees `[1/4, 1/4, 1/2, 100]` → `3/8`
    d 3 0 = 1 / 4 ∧ d 3 1 = 1 / 4 ∧ d 3 2 = 3 / 8 ∧
    |d 3 0 - d 3 2| ≤ 1 / 8 := by
  decide +kernel

-- Rushing adversary inspecting the live round state `σ` before choosing equivocating values.
example :
    let π := syncApproxProtocol (Fin 4) ℚ 1
    let strat : ℕ → (Fin 4 → ℚ) → Fin 4 → Fin 4 → ℚ :=
      fun _ σ _ dest => if dest = 0 then σ 0 - 50 else σ 2 + 50
    let s₂ := π.adaptiveState {3} strat syncInp 2
    0 ≤ s₂ 0 ∧ s₂ 2 ≤ 1 ∧ |s₂ 0 - s₂ 2| ≤ 1 / 4 := by
  decide +kernel

/-! ### Part 3: Concrete asynchronous LTS traces (`decide +kernel`) -/

private def execAsyncStep {P S M V : Type*} [DecidableEq P] [DecidableEq M]
    (π : AsyncProtocol P V S M) (s : State P S M V) : Action P M → State P S M V
  | .deliver e => π.recvHonest e s
  | .byzRecv src dest body => π.recvByz src dest body s
  | .stutter => s

private def execAsync {P S M V : Type*} [DecidableEq P] [DecidableEq M]
    (π : AsyncProtocol P V S M) (s : State P S M V) :
    List (Action P M) → State P S M V
  | [] => s
  | a :: xl => execAsync π (execAsyncStep π s a) xl

private def validAsyncStepBool {P S M V : Type*} [DecidableEq P] [DecidableEq M]
    (F : Finset P) (s : State P S M V) : Action P M → Bool
  | .deliver e => decide (e ∈ s.msgs ∧ e.dest ∉ F)
  | .byzRecv src dest _ => decide (src ∈ F ∧ dest ∉ F)
  | .stutter => true

private def validAsyncTraceBool {P S M V : Type*} [DecidableEq P] [DecidableEq M]
    (π : AsyncProtocol P V S M) (F : Finset P) (s : State P S M V) :
    List (Action P M) → Bool
  | [] => true
  | a :: xl =>
    validAsyncStepBool F s a &&
      validAsyncTraceBool π F (execAsyncStep π s a) xl

private lemma mTr_of_validAsyncTraceBool {P S M V : Type*} [DecidableEq P] [DecidableEq M]
    (π : AsyncProtocol P V S M) (F : Finset P)
    (s : State P S M V) (xl : List (Action P M))
    (hv : validAsyncTraceBool π F s xl = true) :
    (π.lts F).MTr s xl (execAsync π s xl) := by
  induction xl generalizing s with
  | nil => exact LTS.MTr.refl
  | cons a xl ih =>
    simp only [validAsyncTraceBool, Bool.and_eq_true] at hv
    have hstep : (π.lts F).Tr s a (execAsyncStep π s a) := by
      cases a with
      | deliver e =>
        simp only [validAsyncStepBool, decide_eq_true_eq] at hv
        exact ⟨hv.1.1, hv.1.2, rfl⟩
      | byzRecv src dest body =>
        simp only [validAsyncStepBool, decide_eq_true_eq] at hv
        exact ⟨hv.1.1, hv.1.2, rfl⟩
      | stutter => rfl
    exact LTS.MTr.stepL hstep (ih (execAsyncStep π s a) hv.2)

-- Local deduplication & future-round cascade check on `Fin 6, t = 1, R = 2`:
-- process `4` buffers round-`1` messages *before* finishing round `0`, ignores duplicate or
-- equivocated round-`0` messages from faulty sender `5`, and cascades straight from round `0` to
-- round `2` (delivering its output) in a single `asyncApproxStep` once its 5th round-`0` sender
-- arrives!
example :
    let st₀ := asyncApproxInit (Fin 6) (1 : ℚ)
    -- Pre-deliver five round-1 messages `(1, 1/2)` from senders `0, 1, 2, 3, 4` while still at
    -- `round = 0`, plus equivocating round-0 messages `(0, 100)` then `(0, -100)` from `5`.
    let preEvents : List (Fin 6 × RoundMsg ℚ) :=
      [(0, ⟨1, 1 / 2⟩), (1, ⟨1, 1 / 2⟩), (2, ⟨1, 1 / 2⟩), (3, ⟨1, 1 / 2⟩), (4, ⟨1, 1 / 2⟩),
       (5, ⟨0, 100⟩), (5, ⟨0, -100⟩),
       (1, ⟨0, 0⟩), (2, ⟨0, 1 / 2⟩), (3, ⟨0, 1⟩)]
    let stPre := preEvents.foldl
      (fun s ev => (asyncApproxStep 1 2 s ev.1 ev.2).nextState) st₀
    -- `stPre` has 4 round-0 senders `{1, 2, 3, 5}` (`< 6 - 1 = 5`), so it is still at round 0,
    -- and sender `5`'s second equivocated value `-100` was rejected in favor of `100`.
    let finalRes := asyncApproxStep 1 2 stPre 4 ⟨0, 1⟩
    stPre.round = 0 ∧
    stPre.heard 0 5 = some 100 ∧
    -- Delivering the 5th round-0 sender `4` advances round `0 → 1` (`est = (1/2 + 1)/2 = 3/4`)
    -- AND immediately cascades `1 → 2` using the 5 pre-buffered round-1 values (`est = 1/2`)!
    -- Any stale round-0 message arriving afterwards (`msg.round < st.round`) is ignored.
    let staleRes := asyncApproxStep 1 3 finalRes.nextState 0 ⟨0, 42⟩
    finalRes.nextState.round = 2 ∧
    finalRes.delivered = some (1 / 2) ∧
    finalRes.outgoing = broadcastAll (Fin 6) ⟨1, 3 / 4⟩ ∧
    staleRes.nextState.heard 0 0 = none ∧
    staleRes.outgoing = 0 ∧
    staleRes.delivered = none := by
  decide +kernel

-- Full reachable 2-round asynchronous trace on `Fin 6, t = 1` (`5 * 1 < 6`):
-- Correct processes `0..4` have inputs `0, 0, 1/2, 1, 1`; faulty process `5` equivocates (`-50` to
-- `0, 1` and `+50` to `2, 3, 4` in both rounds, plus duplicate replay flooding). Processes `0, 1`
-- hear from `{0, 1, 2, 3, 5}` (omitting slow `4`) while `2, 3, 4` hear from `{1, 2, 3, 4, 5}`
-- (omitting slow `0`), and `4` buffers round-1 messages before finishing round 0.
private def asyncInp6 : Fin 6 → ℚ
  | 0 => 0
  | 1 => 0
  | 2 => 1 / 2
  | 3 => 1
  | 4 => 1
  | 5 => 777

private def asyncTrace6 : List (Action (Fin 6) (RoundMsg ℚ)) :=
  -- Round 0 for `0, 1` (senders `{0, 1, 2, 3, 5}` with faulty `-50`, plus duplicate `5` replay):
  -- multiset `[-50, 0, 0, 1/2, 1]` → `trimmed 1 = [0, 0, 1/2]` → round-1 proposal `1/4`.
  [.byzRecv 5 0 ⟨0, -50⟩, .byzRecv 5 0 ⟨0, 999⟩,
   .deliver ⟨0, 0, ⟨0, 0⟩⟩, .deliver ⟨1, 0, ⟨0, 0⟩⟩,
   .deliver ⟨2, 0, ⟨0, 1 / 2⟩⟩, .deliver ⟨3, 0, ⟨0, 1⟩⟩,
   .byzRecv 5 1 ⟨0, -50⟩,
   .deliver ⟨0, 1, ⟨0, 0⟩⟩, .deliver ⟨1, 1, ⟨0, 0⟩⟩,
   .deliver ⟨2, 1, ⟨0, 1 / 2⟩⟩, .deliver ⟨3, 1, ⟨0, 1⟩⟩,
   -- Round 0 for `2, 3` (senders `{1, 2, 3, 4, 5}` with faulty `+50`):
   -- multiset `[0, 1/2, 1, 1, 50]` → `trimmed 1 = [1/2, 1, 1]` → round-1 proposal `3/4`.
   .byzRecv 5 2 ⟨0, 50⟩,
   .deliver ⟨1, 2, ⟨0, 0⟩⟩, .deliver ⟨2, 2, ⟨0, 1 / 2⟩⟩,
   .deliver ⟨3, 2, ⟨0, 1⟩⟩, .deliver ⟨4, 2, ⟨0, 1⟩⟩,
   .byzRecv 5 3 ⟨0, 50⟩,
   .deliver ⟨1, 3, ⟨0, 0⟩⟩, .deliver ⟨2, 3, ⟨0, 1 / 2⟩⟩,
   .deliver ⟨3, 3, ⟨0, 1⟩⟩, .deliver ⟨4, 3, ⟨0, 1⟩⟩,
   -- Out-of-order: `4` receives round-1 messages from `1, 2, 3` and `5` BEFORE finishing round 0!
   .deliver ⟨1, 4, ⟨1, 1 / 4⟩⟩, .deliver ⟨2, 4, ⟨1, 3 / 4⟩⟩,
   .deliver ⟨3, 4, ⟨1, 3 / 4⟩⟩, .byzRecv 5 4 ⟨1, 50⟩,
   -- Now `4` receives round-0 from `{1, 2, 3, 4, 5}` → advances to round 1 (`3/4`) and broadcasts!
   .byzRecv 5 4 ⟨0, 50⟩,
   .deliver ⟨1, 4, ⟨0, 0⟩⟩, .deliver ⟨2, 4, ⟨0, 1 / 2⟩⟩,
   .deliver ⟨3, 4, ⟨0, 1⟩⟩, .deliver ⟨4, 4, ⟨0, 1⟩⟩,
   -- Deliver `4`'s own `<1, 3/4>` self-message so `4` finishes round 1 (`[1/4, 3/4, 3/4, 3/4, 50]`
   -- → `3/4`):
   .deliver ⟨4, 4, ⟨1, 3 / 4⟩⟩,
   -- Round 1 for `0, 1` (senders `{0, 1, 2, 3, 5}` with faulty `-50`):
   -- `[-50, 1/4, 1/4, 3/4, 3/4]` → `trimmed 1 = [1/4, 1/4, 3/4]` → `(1/4 + 3/4)/2 = 1/2`.
   .byzRecv 5 0 ⟨1, -50⟩,
   .deliver ⟨0, 0, ⟨1, 1 / 4⟩⟩, .deliver ⟨1, 0, ⟨1, 1 / 4⟩⟩,
   .deliver ⟨2, 0, ⟨1, 3 / 4⟩⟩, .deliver ⟨3, 0, ⟨1, 3 / 4⟩⟩,
   .byzRecv 5 1 ⟨1, -50⟩,
   .deliver ⟨0, 1, ⟨1, 1 / 4⟩⟩, .deliver ⟨1, 1, ⟨1, 1 / 4⟩⟩,
   .deliver ⟨2, 1, ⟨1, 3 / 4⟩⟩, .deliver ⟨3, 1, ⟨1, 3 / 4⟩⟩,
   -- Round 1 for `2, 3` (senders `{1, 2, 3, 4, 5}` with faulty `+50`):
   -- `[1/4, 3/4, 3/4, 3/4, 50]` → `trimmed 1 = [3/4, 3/4, 3/4]` → `3/4`.
   .byzRecv 5 2 ⟨1, 50⟩,
   .deliver ⟨1, 2, ⟨1, 1 / 4⟩⟩, .deliver ⟨2, 2, ⟨1, 3 / 4⟩⟩,
   .deliver ⟨3, 2, ⟨1, 3 / 4⟩⟩, .deliver ⟨4, 2, ⟨1, 3 / 4⟩⟩,
   .byzRecv 5 3 ⟨1, 50⟩,
   .deliver ⟨1, 3, ⟨1, 1 / 4⟩⟩, .deliver ⟨2, 3, ⟨1, 3 / 4⟩⟩,
   .deliver ⟨3, 3, ⟨1, 3 / 4⟩⟩, .deliver ⟨4, 3, ⟨1, 3 / 4⟩⟩]

theorem asyncApprox_fin6_round2_reachable :
    let π := asyncApproxProtocol (Fin 6) ℚ 1 2
    let sFinal := execAsync π (π.start {5} asyncInp6) asyncTrace6
    π.Reachable {5} asyncInp6 sFinal ∧
    sFinal.ProcDecided 0 (1 / 2) ∧
    sFinal.ProcDecided 1 (1 / 2) ∧
    sFinal.ProcDecided 2 (3 / 4) ∧
    sFinal.ProcDecided 3 (3 / 4) ∧
    sFinal.ProcDecided 4 (3 / 4) ∧
    |(1 / 2 : ℚ) - 3 / 4| ≤ 1 / 4 := by
  intro π sFinal
  have hv : validAsyncTraceBool π {5} (π.start {5} asyncInp6) asyncTrace6 = true := by
    decide +kernel
  refine ⟨⟨asyncTrace6, mTr_of_validAsyncTraceBool π {5} _ asyncTrace6 hv⟩, ?_⟩
  decide +kernel

-- Reachable non-contraction counterexample on `Fin 5, t = 1` (`|P| = 5 = 5 * t`):
-- `asyncApproxProtocol (Fin 5) ℚ 1 1` fails `1 / 2`-agreement because correct processes `0` and
-- `2` can reach `ProcDecided 0 0` and `ProcDecided 2 1`!
private def asyncInp5 : Fin 5 → ℚ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 0

private def asyncTrace5 : List (Action (Fin 5) (RoundMsg ℚ)) :=
  [.byzRecv 4 0 ⟨0, 0⟩,
   .deliver ⟨0, 0, ⟨0, 0⟩⟩, .deliver ⟨1, 0, ⟨0, 0⟩⟩, .deliver ⟨2, 0, ⟨0, 1⟩⟩,
   .byzRecv 4 2 ⟨0, 1⟩,
   .deliver ⟨0, 2, ⟨0, 0⟩⟩, .deliver ⟨2, 2, ⟨0, 1⟩⟩, .deliver ⟨3, 2, ⟨0, 1⟩⟩]

example : ¬ (asyncApproxProtocol (Fin 5) ℚ 1 1).SolvesUnitAsyncApproxAgreement 1 (1 / 2) := by
  intro hsol
  let π := asyncApproxProtocol (Fin 5) ℚ 1 1
  let sFinal := execAsync π (π.start {4} asyncInp5) asyncTrace5
  have hv : validAsyncTraceBool π {4} (π.start {4} asyncInp5) asyncTrace5 = true := by
    decide +kernel
  have hreach : π.Reachable {4} asyncInp5 sFinal :=
    ⟨asyncTrace5, mTr_of_validAsyncTraceBool π {4} _ asyncTrace5 hv⟩
  have hd0 : sFinal.ProcDecided 0 0 := by decide +kernel
  have hd2 : sFinal.ProcDecided 2 1 := by decide +kernel
  have hx : ∀ k : Fin 5, k ∉ ({4} : Finset (Fin 5)) → asyncInp5 k ∈ Set.Icc (0 : ℚ) 1 := by
    intro k _
    change 0 ≤ asyncInp5 k ∧ asyncInp5 k ≤ 1
    revert k
    decide +kernel
  have habs := hsol.agreement {4} (by decide) asyncInp5 hx sFinal hreach
    0 (by decide) 2 (by decide) 0 1 hd0 hd2
  norm_num at habs

/-! ### Part 4: Unit-interval solvability, arbitrary-interval contraction, and impossibility -/

-- Arbitrary-interval contraction (`[-10, 30]` over `ℚ`, width `40`): after `4` synchronous rounds
-- on `Fin 4, t = 1`, honest decisions lie in `[-10, 30]` and differ by at most `40 / 16 = 5 / 2`.
example (adv : ℕ → Fin 4 → Fin 4 → ℚ) (x : Fin 4 → ℚ)
    (hx : ∀ k ∉ ({3} : Finset (Fin 4)), x k ∈ Set.Icc (-10 : ℚ) 30) :
    (syncApproxProtocol (Fin 4) ℚ 1).decision {3} adv x 4 0 ∈ Set.Icc (-10 : ℚ) 30 ∧
    |(syncApproxProtocol (Fin 4) ℚ 1).decision {3} adv x 4 0 -
      (syncApproxProtocol (Fin 4) ℚ 1).decision {3} adv x 4 2| ≤ 5 / 2 := by
  refine ⟨syncApproxProtocol_decision_mem_Icc (by decide) (by decide) adv x hx 4 (by decide), ?_⟩
  have h := syncApproxProtocol_abs_decision_sub_le (P := Fin 4) (K := ℚ) (t := 1)
    (by decide) (F := {3}) (by decide) adv x hx 4 (i := 0) (j := 2) (by decide) (by decide)
  refine h.trans ?_
  norm_num

-- Unit-interval synchronous solvability and monotonicity (`Fin 4, t = 1`, `ε = 1 / 16` in `R = 4`).
example : (syncApproxProtocol (Fin 4) ℚ 1).SolvesUnitSyncApproxAgreement 1 4 (1 / 16) :=
  solvesUnitSyncApproxAgreement_syncApprox (by decide) (by norm_num)

example : (syncApproxProtocol (Fin 4) ℚ 1).SolvesUnitSyncApproxAgreement 0 4 (1 / 8) :=
  (solvesUnitSyncApproxAgreement_syncApprox (P := Fin 4) (K := ℚ) (t := 1) (R := 4) (ε := 1 / 16)
    (by decide) (by norm_num)).mono (Nat.zero_le 1) (by norm_num)

-- Sharp unit-interval synchronous threshold instantiations (`Fin 1`, `Fin 3`, `Fin 4`).
example : ∃ (S M : Type) (π : SyncProtocol (Fin 1) ℚ S M) (R : ℕ),
    π.SolvesUnitSyncApproxAgreement 5 R (1 / 1000) :=
  (exists_solvesUnitSyncApproxAgreement_iff (Fin 1) ℚ 5 (by norm_num) (by norm_num)).mpr
    (Or.inl (by decide))

example : ¬ ∃ (S M : Type) (π : SyncProtocol (Fin 3) ℚ S M) (R : ℕ),
    π.SolvesUnitSyncApproxAgreement 1 R (1 / 3) := by
  rw [exists_solvesUnitSyncApproxAgreement_iff (Fin 3) ℚ 1 (by norm_num) (by norm_num)]
  decide

example : ∃ (S M : Type) (π : SyncProtocol (Fin 4) ℚ S M) (R : ℕ),
    π.SolvesUnitSyncApproxAgreement 1 R (1 / 100) :=
  (exists_solvesUnitSyncApproxAgreement_iff (Fin 4) ℚ 1 (by norm_num) (by norm_num)).mpr
    (Or.inr (by decide))

-- Unit-interval synchronous `2 ≤ |P| ≤ 3 * t` impossibility (`ε = 1 / 3` and `ε = 99 / 100 < 1`).
example {S M : Type} (π : SyncProtocol (Fin 3) ℚ S M) (R : ℕ) :
    ¬ π.SolvesUnitSyncApproxAgreement 1 R (99 / 100) :=
  π.not_solvesUnitSyncApproxAgreement (by decide) (by decide) (by norm_num)

example {S M : Type} (π : SyncProtocol (Fin 2) ℚ S M) (R : ℕ) :
    ¬ π.SolvesUnitSyncApproxAgreement 1 R (1 / 3) :=
  π.not_solvesUnitSyncApproxAgreement (by decide) (by decide) (by norm_num)

-- Unit-interval asynchronous solvability (`Fin 6, t = 1`, `ε = 1 / 8` in `R = 3` rounds).
example : (asyncApproxProtocol (Fin 6) ℚ 1 3).SolvesUnitAsyncApproxAgreement 1 (1 / 8) :=
  solvesUnitAsyncApproxAgreement_asyncApprox (by decide) (by norm_num)

example : ∃ (S M : Type) (_ : DecidableEq M) (π : AsyncProtocol (Fin 6) ℚ S M),
    π.SolvesUnitAsyncApproxAgreement 1 (1 / 1000) :=
  exists_solvesUnitAsyncApproxAgreement (Fin 6) ℚ 1 (by norm_num) (Or.inr (by decide))

example : ∃ (S M : Type) (_ : DecidableEq M) (π : AsyncProtocol (Fin 1) ℚ S M),
    π.SolvesUnitAsyncApproxAgreement 3 (1 / 1000) :=
  exists_solvesUnitAsyncApproxAgreement (Fin 1) ℚ 3 (by norm_num) (Or.inl (by decide))

-- Independent universe polymorphism `.{u, v}` across `P : Type u` and `K : Type v`.
private theorem async_universes.{u, v} (P : Type u) (K : Type v) [Fintype P] [DecidableEq P]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K]
    (t : ℕ) {ε : K} (hε : 0 < ε) (hn : Fintype.card P ≤ 1 ∨ 5 * t < Fintype.card P) :
    ∃ (S : Type (max u v)) (M : Type v) (_ : DecidableEq M) (π : AsyncProtocol P K S M),
      π.SolvesUnitAsyncApproxAgreement t ε :=
  exists_solvesUnitAsyncApproxAgreement.{u, v} P K t hε hn

-- Admissible-run cross-step agreement (`agreement_admissible`) and fair termination instantiation.
example {x : Fin 6 → ℚ} (hx : ∀ k ∉ ({5} : Finset (Fin 6)), x k ∈ Set.Icc (0 : ℚ) 1)
    {ss : Cslib.ωSequence (State (Fin 6) (AsyncApproxState (Fin 6) ℚ) (RoundMsg ℚ) ℚ)}
    {xs : Cslib.ωSequence (Action (Fin 6) (RoundMsg ℚ))}
    (ha : (asyncApproxProtocol (Fin 6) ℚ 1 3).AdmissibleRun {5} x ss xs) :
    (∃ n₀ v₀, (ss n₀).ProcDecided 0 v₀) ∧
    (∀ n₀ n₁ v₀ v₁, (ss n₀).ProcDecided 0 v₀ → (ss n₁).ProcDecided 1 v₁ →
      |v₀ - v₁| ≤ 1 / 8) := by
  have hsol : (asyncApproxProtocol (Fin 6) ℚ 1 3).SolvesUnitAsyncApproxAgreement 1 (1 / 8) :=
    solvesUnitAsyncApproxAgreement_asyncApprox (by decide) (by norm_num)
  refine ⟨asyncApproxProtocol_terminates (by decide) (by decide) x ha (by decide), ?_⟩
  intro n₀ n₁ v₀ v₁ h₀ h₁
  exact hsol.agreement_admissible (by decide) hx ha (by decide) (by decide) h₀ h₁

-- Unit-interval asynchronous `2 ≤ |P| ≤ 3 * t` impossibility (`Fin 3, t = 1` and `Fin 2, t = 1`).
example {S M : Type} [DecidableEq M] (π : AsyncProtocol (Fin 3) ℚ S M) :
    ¬ π.SolvesUnitAsyncApproxAgreement 1 (99 / 100) :=
  π.not_solvesUnitAsyncApproxAgreement (by decide) (by decide) (by norm_num)

example {S M : Type} [DecidableEq M] (π : AsyncProtocol (Fin 2) ℚ S M) :
    ¬ π.SolvesUnitAsyncApproxAgreement 1 (1 / 3) :=
  π.not_solvesUnitAsyncApproxAgreement (by decide) (by decide) (by norm_num)

end CslibFrontierTests.Distributed.ApproxAgreement
