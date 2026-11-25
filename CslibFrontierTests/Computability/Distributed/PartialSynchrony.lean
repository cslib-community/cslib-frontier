/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.PartialSynchrony.Liveness

/-! Partial-synchrony consensus (checked as a `module` client with ordinary imports):
`decide`-checked 3-view `Fin 4, t = 1` execution of `byzQuorumProtocol` with pre-GST Byzantine
leader equivocation in view `0`, pre-GST split lock and timeout in view `1`, and unanimous decision
at `GST = 12` in view `2`; `decide`-checked 2-view `Fin 3, t = 1` execution of
`omissionQuorumProtocol`; instantiations of `solvesByzantinePartialSync_byzQuorumProtocol`
(including infinite `V = ℕ`), `solvesOmissionPartialSync_omissionQuorumProtocol`, synchronous
`GST = 0` impossibility `not_partialSync_of_le_three_t`, unbounded impossibilities
`not_solvesByzantinePartialSync` and `not_solvesOmissionPartialSync`, and the sharp
characterizations `exists_solvesByzantinePartialSync_iff` and
`exists_solvesOmissionPartialSync_iff`. -/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.PartialSynchrony

open Cslib.Distributed Cslib.Distributed.PartialSynchrony

/-! ### `Fin 4, t = 1` multi-view Byzantine trace: equivocation, split lock, post-GST decision -/

/-- Round-robin `byzQuorumProtocol` instance on `Fin 4` against `t = 1` Byzantine fault. -/
def fin4ByzProto : PartialSyncProtocol (Fin 4) Bool (ByzViewState Bool) (ByzViewMsg Bool) :=
  byzQuorumProtocol (Fin 4) Bool (List.finRange 4) (rotatingCoordinator (List.finRange 4) 0) 1

/-- Initial inputs on `Fin 4`: `0, 1 ↦ false`, `2, 3 ↦ true`. -/
def fin4Inputs : Fin 4 → Bool
  | 0 => false
  | 1 => false
  | 2 => true
  | 3 => true

/-- Adversarial pre-GST delivery schedule with `GST = 12` (start of view `2`):
* View `0` (`r = 0..5`): delivers in subrounds `0..3` and drops all messages in subrounds `4..5`.
* View `1` (`r = 6..11`): delivers in subrounds `0..3`, delivers only to process `1` in subround `4`
  (`r = 10`, creating a split lock at `1` while `2, 3` time out unlocked), and drops subround `5`.
* View `2` onward (`r ≥ 12`): `GST` holds and all messages are delivered. -/
def fin4Deliver (r : ℕ) (_j i : Fin 4) : Bool :=
  if r < 4 then true
  else if r < 6 then false
  else if r < 10 then true
  else if r = 10 then decide (i = 1)
  else if r = 11 then false
  else true

/-- Equivocating Byzantine adversary controlled by faulty process `0`:
* Round `0`: sends `.rawStatus false []` to all processes so both `false` and `true` appear twice.
* Round `2` (view `0` proposal, `leader 0 = 0`): equivocates—proposes `true` to `{1, 2}` and
  `false` to `{3}`.
* Round `3` (view `0` echo): equivocates—sends `.echo 0 true` to `1` and `.echo 0 false` to `3`.
* Rounds `12..17` (view `2`, post-GST): attempts to disrupt consensus by sending conflicting
  `false` messages. -/
def fin4ByzAdv (r : ℕ) (_j i : Fin 4) : Option (ByzViewMsg Bool) :=
  if r = 0 then some (.rawStatus false [])
  else if r = 2 then
    if i = 3 then some (.propose 0 ⟨false, none⟩) else some (.propose 0 ⟨true, none⟩)
  else if r = 3 then
    if i = 1 then some (.echo 0 true)
    else if i = 3 then some (.echo 0 false)
    else none
  else if 12 ≤ r then some (.echo 2 false)
  else none

-- `fin4Deliver` satisfies `IsGST` starting at round `12` (view `2`).
theorem fin4Deliver_isGST : IsGST fin4Deliver ({0} : Finset (Fin 4)) 12 := by
  intro r hr _ _ _ _
  have h1 : ¬ r < 4 := by omega
  have h2 : ¬ r < 6 := by omega
  have h3 : ¬ r < 10 := by omega
  have h4 : r ≠ 10 := by omega
  have h5 : r ≠ 11 := by omega
  simp only [fin4Deliver, h1, h2, h3, h4, h5, ↓reduceIte]

-- View `0` (pre-GST): Byzantine coordinator `0` equivocates (`true` accepted by `1, 2` and `false`
-- accepted by `3`), `1` records a Stage-2 vote `⟨0, true⟩` while `prevoteQuorum_unique` blocks `3`
-- from voting `false`, and pre-GST drops leave everyone unlocked and undecided at round `6`.
example :
    let st := fin4ByzProto.byzantineState {0} fin4Deliver fin4ByzAdv fin4Inputs
    (st 3 1).myEcho = some true ∧
    (st 3 2).myEcho = some true ∧
    (st 3 3).myEcho = some false ∧
    (st 4 1).votedViews = [⟨0, true⟩] ∧
    (st 4 3).myVote = none ∧
    (∀ i : Fin 4, i ≠ 0 → (st 6 i).locked = none ∧ (st 6 i).decided = none) := by
  decide

-- View `1` (pre-GST): honest coordinator `1` runs under partial omissions, causing `1` to acquire a
-- lock `⟨1, true⟩` while `2` and `3` time out unlocked (`locked = none`), and nobody decides yet.
example :
    let st := fin4ByzProto.byzantineState {0} fin4Deliver fin4ByzAdv fin4Inputs
    (st 12 1).locked = some ⟨1, true⟩ ∧
    (st 12 2).locked = none ∧
    (st 12 3).locked = none ∧
    (∀ i : Fin 4, i ≠ 0 → (st 12 i).decided = none) := by
  decide

-- View `2` (`GST = 12`): unlocked honest coordinator `2` relays view `1`'s certified lock via the
-- 2-round unauthenticated status amplification, and all correct processes `{1, 2, 3}` unanimously
-- decide `some true` at round `18`.
example :
    ∀ i : Fin 4, i ≠ 0 →
      fin4ByzProto.byzantineDecision {0} fin4Deliver fin4ByzAdv fin4Inputs 18 i = some true := by
  decide

/-! ### `Fin 3, t = 1` crash/omission trace (`2 * t < 3`) -/

/-- Round-robin `omissionQuorumProtocol` instance on `Fin 3` against `t = 1` omission fault. -/
def fin3OmissionProto :
    PartialSyncProtocol (Fin 3) Bool (OmissionViewState Bool) (OmissionViewMsg Bool) :=
  omissionQuorumProtocol (Fin 3) Bool (List.finRange 3) (rotatingCoordinator (List.finRange 3) 0) 1

/-- Schedule on `Fin 3` where crashed process `0` omits all messages in view `0` (`leader 0 = 0`),
and `GST = 3` (view `1`, `leader 1 = 1`) delivers among correct `{1, 2}`. -/
def fin3OmissionDeliver (r : ℕ) (j i : Fin 3) : Bool :=
  decide (3 ≤ r ∧ j ≠ 0 ∧ i ≠ 0)

example :
    let dec := fin3OmissionProto.omissionDecision fin3OmissionDeliver (fun i => decide (i = 1))
    dec 3 1 = none ∧ dec 3 2 = none ∧ dec 6 1 = some true ∧ dec 6 2 = some true := by
  decide

/-! ### Correctness, infinite value domains, and tight resiliency instantiations -/

-- `fin4ByzProto` solves unauthenticated Byzantine partial-synchrony consensus on `Fin 4` (`t = 1`).
example : fin4ByzProto.SolvesByzantinePartialSync 1 :=
  solvesByzantinePartialSync_byzQuorumProtocol (List.mem_finRange) 0 (by decide)

-- Works over infinite `[DecidableEq V]` value domains such as `ℕ` on `Fin 4` (`t = 1`) and
-- `Fin 7` (`t = 2`).
example : (byzQuorumProtocol (Fin 4) ℕ (List.finRange 4)
    (rotatingCoordinator (List.finRange 4) 0) 1).SolvesByzantinePartialSync 1 :=
  solvesByzantinePartialSync_byzQuorumProtocol (List.mem_finRange) 0 (by decide)

example : (byzQuorumProtocol (Fin 7) ℕ (List.finRange 7)
    (rotatingCoordinator (List.finRange 7) 0) 2).SolvesByzantinePartialSync 2 :=
  solvesByzantinePartialSync_byzQuorumProtocol (List.mem_finRange) 0 (by decide)

-- `fin3OmissionProto` solves crash/omission partial-synchrony consensus on `Fin 3` (`t = 1`),
-- where unauthenticated Byzantine consensus is impossible!
example : fin3OmissionProto.SolvesOmissionPartialSync 1 :=
  solvesOmissionPartialSync_omissionQuorumProtocol (List.mem_finRange) 0 (by decide)

example {S M : Type} (π : PartialSyncProtocol (Fin 3) Bool S M) :
    ¬ π.SolvesByzantinePartialSync 1 :=
  not_solvesByzantinePartialSync π (by decide) (by decide)

example {S M : Type} (π : PartialSyncProtocol (Fin 2) Bool S M) :
    ¬ π.SolvesOmissionPartialSync 1 :=
  not_solvesOmissionPartialSync π (by decide) (by decide)

-- Weak-unanimity omission lower bound (`not_omissionPartialSync_weakUnanimity`, Theorem 4.3).
example {S M : Type} (π : PartialSyncProtocol (Fin 2) Bool S M)
    (hag : ∀ deliver x r₁ r₂ i j v₁ v₂, (∃ gst, IsGST deliver ∅ gst) →
      π.omissionDecision deliver x r₁ i = some v₁ →
      π.omissionDecision deliver x r₂ j = some v₂ → v₁ = v₂)
    (hwu : ∀ deliver x v, (∃ gst, IsGST deliver ∅ gst) → (∀ i, x i = v) →
      ∀ r i w, π.omissionDecision deliver x r i = some w → w = v)
    (hterm : ∀ F : Finset (Fin 2), F.card ≤ 1 → ∀ deliver gst x,
      IsGST deliver F gst → ∀ i ∉ F, ∃ r, (π.omissionDecision deliver x r i).isSome = true) :
    False :=
  not_omissionPartialSync_weakUnanimity π (by decide) (by decide) hag hwu hterm

-- Direct synchronous `GST = 0` special-case impossibility for fixed-round `R` agreement, validity,
-- and termination at `deliver = fun _ _ _ => true`.
example {S M : Type} (π : PartialSyncProtocol (Fin 3) Bool S M) (R : ℕ)
    (hag : ∀ F : Finset (Fin 3), F.card ≤ 1 → ∀ adv x,
      ∀ i ∉ F, ∀ j ∉ F, ∀ v₁ v₂,
        π.byzantineDecision F (fun _ _ _ => true) adv x R i = some v₁ →
        π.byzantineDecision F (fun _ _ _ => true) adv x R j = some v₂ → v₁ = v₂)
    (hval : ∀ F : Finset (Fin 3), F.card ≤ 1 → ∀ adv x v,
      (∀ i ∉ F, x i = v) → ∀ i ∉ F, ∀ w,
        π.byzantineDecision F (fun _ _ _ => true) adv x R i = some w → w = v)
    (hbdd : ∀ F : Finset (Fin 3), F.card ≤ 1 → ∀ adv x,
      ∀ i ∉ F, (π.byzantineDecision F (fun _ _ _ => true) adv x R i).isSome = true) : False :=
  not_partialSync_of_le_three_t π (by decide) (by decide) hag hval hbdd

-- Sharp `iff` characterizations on concrete finite process sets.
example : (∃ (S M : Type) (π : PartialSyncProtocol (Fin 3) Bool S M),
    π.SolvesByzantinePartialSync 1) ↔ False := by
  rw [exists_solvesByzantinePartialSync_iff]
  decide

example : (∃ (S M : Type) (π : PartialSyncProtocol (Fin 4) Bool S M),
    π.SolvesByzantinePartialSync 1) ↔ True := by
  rw [exists_solvesByzantinePartialSync_iff]
  decide

example : (∃ (S M : Type) (π : PartialSyncProtocol (Fin 3) Bool S M),
    π.SolvesOmissionPartialSync 1) ↔ True := by
  rw [exists_solvesOmissionPartialSync_iff]
  decide

end CslibFrontierTests.Distributed.PartialSynchrony
