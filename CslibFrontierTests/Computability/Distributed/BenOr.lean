/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.BenOr.Liveness

/-! Quorum-phase safety and pre-coin phase-scheduler termination step for Ben-Or's binary consensus
(checked as a `module` client with ordinary imports): threshold values (`majorityThreshold`),
`decide`-checked runs on `Fin 3, t = 1` and `Fin 5, t = 2` covering the 1-phase unanimous fast path
without coin use, split-input phase schedules rescued by a lucky coin flip, single-process Stage-2
decision locking all estimates for the next phase, phased mid-stage crashes (`CrashSchedule` and
`crashRun` with post-decision crash preserving uniform agreement), failure at `n = 2, t = 1`
(`2 * t = n`), deterministic static-coin non-termination (`exists_nonterminating_of_fixed_coin`),
dot-notation checks, and pre-coin phase-scheduler tail bounds under both `localCoinLaw`
(`(1 - (1 / 2) ^ n) ^ k`) and the separate `commonCoinLaw` variant (`(1 / 2) ^ k`). -/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.BenOr

open Cslib.Distributed.BenOr Filter
open scoped ENNReal

/-! ### Majority threshold arithmetic -/

example : majorityThreshold 1 = 1 := rfl
example : majorityThreshold 3 = 2 := rfl
example : majorityThreshold 4 = 3 := rfl
example : majorityThreshold 5 = 3 := rfl

/-! ### `Fin 3, t = 1` (`2 * 1 < 3`): `decide`-checked concrete executions -/

-- 1. Unanimous `true` input on `Fin 3, t = 1` with process `2` omitted (`honestQuorum {2}`):
-- even when every coin is adversarially `false`, all 3 processes decide `true` after 1 phase.
example :
    let sched : ℕ → PhaseSchedule (Fin 3) := fun _ => PhaseSchedule.honestQuorum {2}
    let coins : ℕ → Fin 3 → Bool := fun _ _ => false
    let s₁ := run 1 sched coins (fun _ => true) 1
    ∀ p : Fin 3, s₁ p = ⟨true, some true⟩ := by
  decide

-- 2. Split input `[false, true, true]` on `Fin 3, t = 1` under an asymmetric asynchronous schedule:
-- `0` hears `{0, 1}` (`none`), `1` hears `{1, 2}` (`some true`), `2` hears `{0, 2}` (`none`);
-- in Stage 2, `0` hears `{0, 2}` (`none, none` -> flips coin), while `1` and `2` hear `{1, 2}`
-- (one `some true` -> adopt `true` without reaching the decision threshold `t + 1 = 2`).
-- An unlucky Phase-0 coin (`false`) leaves the system in its initial split state, whereas a lucky
-- Phase-0 coin (`true`) aligns all estimates at `r = 1` and forces unanimous decision `true` at
-- `r = 2` even when Phase-1 coins are all `false`.
private def fin3AdvSched : PhaseSchedule (Fin 3) where
  q1
    | 0 => {0, 1}
    | 1 => {1, 2}
    | 2 => {0, 2}
  q2
    | 0 => {0, 2}
    | 1 => {1, 2}
    | 2 => {1, 2}

private def fin3SplitInp : Fin 3 → Bool
  | 0 => false
  | 1 => true
  | 2 => true

example :
    let sched : ℕ → PhaseSchedule (Fin 3) := fun _ => fin3AdvSched
    let unluckyCoins : ℕ → Fin 3 → Bool := fun _ _ => false
    let luckyCoins : ℕ → Fin 3 → Bool
      | 0, _ => true
      | _ + 1, _ => false
    let sUnlucky₁ := run 1 sched unluckyCoins fin3SplitInp 1
    let sLucky₁ := run 1 sched luckyCoins fin3SplitInp 1
    let sLucky₂ := run 1 sched luckyCoins fin3SplitInp 2
    (∀ p : Fin 3, (sUnlucky₁ p).decided = none) ∧
    (sUnlucky₁ 0).est = false ∧ (sUnlucky₁ 1).est = true ∧ (sUnlucky₁ 2).est = true ∧
    (∀ p : Fin 3, sLucky₁ p = ⟨true, none⟩) ∧
    (∀ p : Fin 3, sLucky₂ p = ⟨true, some true⟩) := by
  decide

-- 3. Asymmetric Stage-2 decision + single-phase lock-in on `Fin 3, t = 1`:
-- `0` and `1` hear `{1, 2}` in Stage 1 (both propose `some true`), while `2` hears `{0, 1}`
-- (`none`). In Stage 2, `0` hears `{0, 1}` (two `some true`s >= `t + 1 = 2` -> `0` decides `true`
-- at `r = 1`), whereas `1` and `2` hear `{1, 2}` (only one `some true` -> `decided = none` at
-- `r = 1`, yet both lock `est = true` despite `false` coins and decide `true` at `r = 2`).
private def fin3PartialDecideSched : PhaseSchedule (Fin 3) where
  q1
    | 0 => {1, 2}
    | 1 => {1, 2}
    | 2 => {0, 1}
  q2
    | 0 => {0, 1}
    | 1 => {1, 2}
    | 2 => {1, 2}

example :
    let sched : ℕ → PhaseSchedule (Fin 3) := fun _ => fin3PartialDecideSched
    let coins : ℕ → Fin 3 → Bool := fun _ _ => false
    let s₁ := run 1 sched coins fin3SplitInp 1
    let s₂ := run 1 sched coins fin3SplitInp 2
    s₁ 0 = ⟨true, some true⟩ ∧
    s₁ 1 = ⟨true, none⟩ ∧
    s₁ 2 = ⟨true, none⟩ ∧
    (∀ p : Fin 3, s₂ p = ⟨true, some true⟩) := by
  decide

-- 4. Dynamic mid-stage crash trace (`CrashSchedule` on `Fin 3, t = 1`):
-- Process `0` decides `true` at `r = 1` under `fin3PartialDecideSched` and immediately crashes
-- before Phase 1 (`crashed1 1 = {0}, crashed2 1 = {0}`). Process `0`'s state freezes at
-- `⟨true, some true⟩`, while surviving processes `1` and `2` hear only `{1, 2}` in Phase 1 and
-- both decide `true` at `r = 2`.
private def fin3PostDecisionCrash : CrashSchedule (Fin 3) where
  crashed1
    | 0 => ∅
    | _ + 1 => {0}
  crashed2
    | 0 => ∅
    | _ + 1 => {0}
  q1
    | 0 => fin3PartialDecideSched.q1
    | _ + 1 => fun _ => {1, 2}
  q2
    | 0 => fin3PartialDecideSched.q2
    | _ + 1 => fun _ => {1, 2}

private theorem valid_fin3PostDecisionCrash : fin3PostDecisionCrash.Valid 1 where
  crashed1_subset r := by cases r <;> (dsimp only [fin3PostDecisionCrash]; decide)
  crashed2_subset r := by cases r <;> (dsimp only [fin3PostDecisionCrash]; decide)
  card_crashed2 r := by cases r <;> (dsimp only [fin3PostDecisionCrash]; decide)
  card_q1 r := by cases r <;> (dsimp only [fin3PostDecisionCrash]; decide)
  card_q2 r := by cases r <;> (dsimp only [fin3PostDecisionCrash]; decide)
  disjoint_q1 r := by cases r <;> (dsimp only [fin3PostDecisionCrash]; decide)
  disjoint_q2 r := by cases r <;> (dsimp only [fin3PostDecisionCrash]; decide)

example :
    let coins : ℕ → Fin 3 → Bool := fun _ _ => false
    let c₁ := crashRun 1 fin3PostDecisionCrash coins fin3SplitInp 1
    let c₂ := crashRun 1 fin3PostDecisionCrash coins fin3SplitInp 2
    c₁ 0 = ⟨true, some true⟩ ∧
    c₁ 1 = ⟨true, none⟩ ∧
    c₁ 2 = ⟨true, none⟩ ∧
    (∀ p : Fin 3, c₂ p = ⟨true, some true⟩) := by
  decide

example {coins : ℕ → Fin 3 → Bool} {inp : Fin 3 → Bool} {r₁ r₂ : ℕ} {p₁ p₂ : Fin 3}
    {b₁ b₂ : Bool}
    (hd₁ : (crashRun 1 fin3PostDecisionCrash coins inp r₁ p₁).decided = some b₁)
    (hd₂ : (crashRun 1 fin3PostDecisionCrash coins inp r₂ p₂).decided = some b₂) :
    b₁ = b₂ :=
  crashRun_agreement (by decide) valid_fin3PostDecisionCrash hd₁ hd₂

-- 5. Sharpness of `2 * t < |P|` at `n = 2, t = 1` (`2 * 1 = 2`):
-- With singleton `n - t = 1` quorums (`{p}`), `1 < majorityThreshold 2 = 2`, so even on unanimous
-- `true` input and unanimous `true` coins, no process ever proposes `some true` or decides.
private def fin2SingletonSched : PhaseSchedule (Fin 2) where
  q1 p := {p}
  q2 p := {p}

example :
    fin2SingletonSched.Valid 1 ∧
    (∀ p : Fin 2,
      (run 1 (fun _ => fin2SingletonSched) (fun _ _ => true) (fun _ => true) 3 p).decided = none) :=
  ⟨⟨by decide, by decide⟩, by decide⟩

/-! ### `Fin 5, t = 2` (`2 * 2 < 5`): `decide`-checked concrete executions -/

-- 1. Unanimous `false` input on `Fin 5, t = 2` with two crashed processes `{3, 4}`:
-- all 5 processes decide `false` in Phase 0 even with all-`true` coins.
example :
    let sched : ℕ → PhaseSchedule (Fin 5) := fun _ => PhaseSchedule.honestQuorum {3, 4}
    let coins : ℕ → Fin 5 → Bool := fun _ _ => true
    let s₁ := run 2 sched coins (fun _ => false) 1
    ∀ p : Fin 5, s₁ p = ⟨false, some false⟩ := by
  decide

-- 2. Split 3-vs-2 input `[true, true, true, false, false]` on `Fin 5, t = 2` (`majority = 3`,
-- `t + 1 = 3`): `0` hears `{0, 1, 2}` (`some true`), `1..4` hear `{2, 3, 4}` (`none`);
-- in Stage 2, `0` and `1` hear `{0, 1, 2}` (one `some true` -> adopt `true`, `< 3` so undecided),
-- while `2, 3, 4` hear `{2, 3, 4}` (all `none` -> flip coins). A lucky `true` coin flip aligns all
-- 5 processes at `r = 1` and decides `true` across all 5 processes at `r = 2`.
private def fin5AdvSched : PhaseSchedule (Fin 5) where
  q1
    | 0 => {0, 1, 2}
    | _ => {2, 3, 4}
  q2
    | 0 => {0, 1, 2}
    | 1 => {0, 1, 2}
    | _ => {2, 3, 4}

private def fin5SplitInp : Fin 5 → Bool
  | 0 => true
  | 1 => true
  | 2 => true
  | _ => false

example :
    let sched : ℕ → PhaseSchedule (Fin 5) := fun _ => fin5AdvSched
    let luckyCoins : ℕ → Fin 5 → Bool
      | 0, _ => true
      | _ + 1, _ => false
    let s₁ := run 2 sched luckyCoins fin5SplitInp 1
    let s₂ := run 2 sched luckyCoins fin5SplitInp 2
    fin5AdvSched.Valid 2 ∧
    (∀ p : Fin 5, s₁ p = ⟨true, none⟩) ∧
    (∀ p : Fin 5, s₂ p = ⟨true, some true⟩) :=
  ⟨⟨by decide, by decide⟩, by decide, by decide⟩

/-! ### Dot-notation, static-coin non-termination, and probabilistic tail-bound instantiations -/

-- Dot-notation checks (`PhaseSchedule.Valid.mono`, `IsUnanimous.phaseStep`,
-- `EstimateLocked.phaseStep`, `CrashSchedule.Valid.valid_toSchedule`).
example {P : Type*} [Fintype P] [DecidableEq P] {t : ℕ} (ht : 2 * t < Fintype.card P)
    {cs : CrashSchedule P} (hv : cs.Valid t) {st : P → ProcState}
    (hu : IsUnanimous st) (hl : EstimateLocked st) (coins : P → Bool) :
    (cs.toSchedule 0).Valid (t + 1) ∧
    IsUnanimous (phaseStep t (cs.toSchedule 0) coins st) ∧
    EstimateLocked (phaseStep t (cs.toSchedule 0) coins st) :=
  ⟨(hv.valid_toSchedule 0).mono (Nat.le_succ t),
   hu.phaseStep ht (hv.valid_toSchedule 0) coins,
   hl.phaseStep ht (hv.valid_toSchedule 0) coins⟩

-- Static deterministic fallback `fun p => p == 0` fails to terminate on `Fin 3, t = 1`.
example : ∃ (inp : Fin 3 → Bool) (sched : PhaseSchedule (Fin 3)),
    sched.Valid 1 ∧
      ∀ (r : ℕ) (p : Fin 3),
        (run 1 (fun _ => sched) (fun _ p => p == 0) inp r p).decided = none :=
  exists_nonterminating_of_fixed_coin (fun p => p == 0)

-- Common fair coin (`(1 / 2) ^ k`) and independent local fair coins (`(7 / 8) ^ k`) on `Fin 3,
-- t = 1` against any adaptive scheduler.
example {strat : ℕ → (Fin 3 → ProcState) → PhaseSchedule (Fin 3)}
    (hv : ∀ r st, (strat r st).Valid 1) (inp : Fin 3 → Bool) (k : ℕ) :
    (probRun 1 (commonCoinLaw (Fin 3)) strat inp (k + 1)).toOuterMeasure
        {st | ¬ AllDecided st} ≤ (1 / 2 : ℝ≥0∞) ^ k ∧
    Tendsto
      (fun m => (probRun 1 (commonCoinLaw (Fin 3)) strat inp m).toOuterMeasure
        {st | ¬ AllDecided st})
      atTop (nhds 0) :=
  ⟨probRun_commonCoin_not_allDecided_le (by decide) inp k (fun r _ st => hv r st),
   tendsto_probRun_commonCoin_not_allDecided (by decide) hv inp⟩

example {strat : ℕ → (Fin 3 → ProcState) → PhaseSchedule (Fin 3)}
    (hv : ∀ r st, (strat r st).Valid 1) (inp : Fin 3 → Bool) (k : ℕ) :
    (probRun 1 (localCoinLaw (Fin 3)) strat inp (k + 1)).toOuterMeasure
        {st | ¬ AllDecided st} ≤ (1 - (1 / 2 : ℝ≥0∞) ^ 3) ^ k ∧
    Tendsto
      (fun m => (probRun 1 (localCoinLaw (Fin 3)) strat inp m).toOuterMeasure
        {st | ¬ AllDecided st})
      atTop (nhds 0) := by
  refine ⟨?_, tendsto_probRun_localCoin_not_allDecided (by decide) hv inp⟩
  simpa [Fintype.card_fin] using
    probRun_localCoin_not_allDecided_le (by decide) inp k (fun r _ st => hv r st)

-- Common fair coin and independent local fair coins on `Fin 5, t = 2`.
example {strat : ℕ → (Fin 5 → ProcState) → PhaseSchedule (Fin 5)}
    (hv : ∀ r st, (strat r st).Valid 2) (inp : Fin 5 → Bool) (k : ℕ) :
    (probRun 2 (commonCoinLaw (Fin 5)) strat inp (k + 1)).toOuterMeasure
        {st | ¬ AllDecided st} ≤ (1 / 2 : ℝ≥0∞) ^ k ∧
    (probRun 2 (localCoinLaw (Fin 5)) strat inp (k + 1)).toOuterMeasure
        {st | ¬ AllDecided st} ≤ (1 - (1 / 2 : ℝ≥0∞) ^ 5) ^ k :=
  ⟨probRun_commonCoin_not_allDecided_le (by decide) inp k (fun r _ st => hv r st),
   by simpa [Fintype.card_fin] using
     probRun_localCoin_not_allDecided_le (by decide) inp k (fun r _ st => hv r st)⟩

-- Abstract `[Fintype P]` usability without `[DecidableEq P]` for `localCoinLaw`.
example {P : Type*} [Fintype P] {t : ℕ} (ht : 2 * t < Fintype.card P)
    {strat : ℕ → (P → ProcState) → PhaseSchedule P}
    (hv : ∀ r st, (strat r st).Valid t) (inp : P → Bool) (k : ℕ) :
    (probRun t (localCoinLaw P) strat inp (k + 1)).toOuterMeasure {st | ¬ AllDecided st} ≤
      (1 - (1 / 2 : ℝ≥0∞) ^ Fintype.card P) ^ k :=
  probRun_localCoin_not_allDecided_le ht inp k (fun r _ st => hv r st)

end CslibFrontierTests.Distributed.BenOr
