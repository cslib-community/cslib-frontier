/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Distributed.ByzantineQuorum.QuorumSystems
import CslibFrontier.Computability.Distributed.ByzantineQuorum.PBFT

/-! Uniform `b`-threshold Malkhi–Reiter Byzantine quorum systems and ideal-authentication
checkpoint-free multi-slot `PBFT` state-machine replication steps (checked as a `module` client
with ordinary imports): threshold `decide` witnesses and impossibility boundaries across
`Fin 3`..`Fin 7` for dissemination (`3 * b < |P|`), masking (`4 * b < |P|`), and strong-opaque
(`5 * b < |P|`) quorum systems; unauthenticated `maskingRead` resilience against forged higher
timestamps on `Fin 5` (`b = 1`) contrasted with `Fin 4` ambiguity without signatures; concrete
normal-case and adversarial multi-slot `PBFT` executions on `Fin 4` (`f = 1`, `F = {3}`) where
`computeOset` preserves committed slot `0`, fills unprepared slot `1` with `none` (`null` no-op),
and carries prepared slot `2` despite Byzantine history-erasure attempts; non-minimal `Fin 5`
(`f = 1`, `pbftQuorumSize = 4`) liveness and agreement; and the `|P| = 3 * f` (`Fin 3, f = 1`)
split-brain view-change counterexample. -/
set_option linter.privateModule false

namespace CslibFrontierTests.Distributed.ByzantineQuorum

open Cslib Cslib.Distributed.ByzantineQuorum

/-! ### 1. Malkhi–Reiter threshold quorum systems: concrete thresholds, hierarchy, and boundaries -/

example : ({0, 1, 2} : Finset (Fin 4)) ∈ (disseminationThresholdQuorums (Fin 4) 1).quorums := by
  decide

example : ({0, 1} : Finset (Fin 4)) ∉ (disseminationThresholdQuorums (Fin 4) 1).quorums := by
  decide

example : ({0, 1, 2, 3} : Finset (Fin 5)) ∈ (maskingThresholdQuorums (Fin 5) 1).quorums := by
  decide

example : ({0, 1, 2} : Finset (Fin 5)) ∉ (maskingThresholdQuorums (Fin 5) 1).quorums := by
  decide

example :
    ({0, 1, 2, 3, 4} : Finset (Fin 6)) ∈ (strongOpaqueThresholdQuorums (Fin 6) 1).quorums := by
  decide

example : ({0, 1, 2, 3} : Finset (Fin 6)) ∉ (strongOpaqueThresholdQuorums (Fin 6) 1).quorums := by
  decide

theorem exists_dissemination_fin4 :
    ∃ qs : QuorumSystem (Fin 4), qs.IsThresholdDisseminationQuorumSystem 1 :=
  (exists_thresholdDisseminationQuorumSystem_iff (P := Fin 4) (b := 1)).mpr (by decide)

theorem not_exists_dissemination_fin3 :
    ¬∃ qs : QuorumSystem (Fin 3), qs.IsThresholdDisseminationQuorumSystem 1 := by
  rw [exists_thresholdDisseminationQuorumSystem_iff]
  decide

theorem exists_masking_fin5 :
    ∃ qs : QuorumSystem (Fin 5), qs.IsThresholdMaskingQuorumSystem 1 :=
  (exists_thresholdMaskingQuorumSystem_iff (P := Fin 5) (b := 1)).mpr (by decide)

theorem not_exists_masking_fin4 :
    ¬∃ qs : QuorumSystem (Fin 4), qs.IsThresholdMaskingQuorumSystem 1 := by
  rw [exists_thresholdMaskingQuorumSystem_iff]
  decide

theorem exists_strongOpaque_fin6 :
    ∃ qs : QuorumSystem (Fin 6), qs.IsThresholdStrongOpaqueQuorumSystem 1 :=
  (exists_thresholdStrongOpaqueQuorumSystem_iff (P := Fin 6) (b := 1)).mpr (by decide)

theorem not_exists_strongOpaque_fin5 :
    ¬∃ qs : QuorumSystem (Fin 5), qs.IsThresholdStrongOpaqueQuorumSystem 1 := by
  rw [exists_thresholdStrongOpaqueQuorumSystem_iff]
  decide

/-- At `|P| = 7` and `b = 2`, `2`-threshold dissemination quorums exist (`3 * 2 < 7`) whereas
`2`-threshold masking quorums do not (`¬(4 * 2 < 7)`). -/
theorem fin7_twoFault_dissemination_without_masking :
    (∃ qs : QuorumSystem (Fin 7), qs.IsThresholdDisseminationQuorumSystem 2) ∧
      ¬∃ qs : QuorumSystem (Fin 7), qs.IsThresholdMaskingQuorumSystem 2 := by
  rw [exists_thresholdDisseminationQuorumSystem_iff, exists_thresholdMaskingQuorumSystem_iff]
  decide

/-- Exercising `StrongOpaque → Masking → Dissemination` and quorum non-emptiness on `Fin 6`
(`b = 1`). -/
theorem strongOpaque_fin6_hierarchy_inter_nonempty
    {Q₁ Q₂ : Finset (Fin 6)}
    (hQ₁ : Q₁ ∈ (strongOpaqueThresholdQuorums (Fin 6) 1).quorums)
    (hQ₂ : Q₂ ∈ (strongOpaqueThresholdQuorums (Fin 6) 1).quorums) :
    (strongOpaqueThresholdQuorums (Fin 6) 1).quorums.Nonempty ∧ (Q₁ ∩ Q₂).Nonempty := by
  have hopq :=
    isThresholdStrongOpaqueQuorumSystem_strongOpaqueThresholdQuorums (P := Fin 6) (b := 1)
      (by decide)
  have hdis := hopq.toMasking.toDissemination
  exact ⟨hdis.quorums_nonempty, hdis.inter_nonempty hQ₁ hQ₂⟩

/-! ### 2. Unauthenticated masking register: forged-timestamp filtering vs `Fin 4` ambiguity -/

/-- Honest write history on `Q_w = {0, 1, 2, 3} ⊆ Fin 5`: older write `⟨5, 7⟩` followed by
completed write `⟨10, 42⟩`, while server `4 ∈ F` is Byzantine and forges a future timestamp
`⟨999, 666⟩`. -/
def maskingDeliveredFin5 : Fin 5 → List (TimestampedVal ℕ ℕ)
  | 0 => [⟨10, 42⟩, ⟨5, 7⟩]
  | 1 => [⟨5, 7⟩, ⟨10, 42⟩]
  | 2 => [⟨10, 42⟩]
  | 3 => [⟨5, 7⟩, ⟨10, 42⟩]
  | 4 => []

def forgedByzRespFin5 : Fin 5 → TimestampedVal ℕ ℕ
  | 4 => ⟨999, 666⟩
  | u => applyWrites ⟨0, 0⟩ (maskingDeliveredFin5 u)

/-- Reading from `Q_r = {1, 2, 3, 4}` filters out server `4`'s forged `⟨999, 666⟩` (count `1 < 2`)
and uniquely recovers `some 42`. -/
theorem forgedByzRespFin5_candidates_and_read :
    maskingCandidates 1 ({1, 2, 3, 4} : Finset (Fin 5)) forgedByzRespFin5 = {⟨10, 42⟩} ∧
      maskingRead 1 ({1, 2, 3, 4} : Finset (Fin 5)) forgedByzRespFin5 = some 42 := by
  decide

/-- Quantified read-after-write safety on `Fin 5` (`b = 1`, `F = {4}`) against *arbitrary*
Byzantine response payloads from server `4`. -/
theorem maskingRead_fin5_arbitrary_byzantine
    (byzEntry : TimestampedVal ℕ ℕ)
    {Q_r : Finset (Fin 5)} (hQr : Q_r ∈ (maskingThresholdQuorums (Fin 5) 1).quorums) :
    maskingRead 1 Q_r
      (fun u => if u = 4 then byzEntry else applyWrites ⟨0, 0⟩ (maskingDeliveredFin5 u)) =
      some 42 := by
  have hqs :=
    isThresholdMaskingQuorumSystem_maskingThresholdQuorums (P := Fin 5) (b := 1) (by decide)
  have hQw : ({0, 1, 2, 3} : Finset (Fin 5)) ∈ (maskingThresholdQuorums (Fin 5) 1).quorums := by
    decide
  have hF : ({4} : Finset (Fin 5)).card ≤ 1 := by decide
  refine threshold_maskingRead_eq_some_latest_write hqs hF hQw hQr
    (init := ⟨0, 0⟩) (latest := ⟨10, 42⟩) (delivered := maskingDeliveredFin5) (by decide) ?_ ?_ ?_
  · decide
  · decide
  · intro u huF
    have hne : u ≠ 4 := Finset.notMem_singleton.mp huF
    simp only [hne, ↓reduceIte]

/-- Contrast on `Fin 4` (`b = 1`, quorum size `3`): if write `⟨10, 42⟩` reached `Q_w = {1, 2, 3}`
where `1` is Byzantine (`F = {1}`), a read from `Q_r = {0, 1, 2}` sees stale `⟨0, 0⟩` from `0`,
honest `⟨10, 42⟩` from `2`, and forged `⟨10, 99⟩` from Byzantine `1`, leaving zero `≥ 2`-vote
support for `⟨10, 42⟩` without self-verifying signatures. -/
theorem fin4_unauthenticated_read_fails_threshold :
    let resp : Fin 4 → TimestampedVal ℕ ℕ
      | 0 => ⟨0, 0⟩
      | 1 => ⟨10, 99⟩
      | 2 => ⟨10, 42⟩
      | 3 => ⟨10, 42⟩
    maskingCandidates 1 ({0, 1, 2} : Finset (Fin 4)) resp = ∅ ∧
      maskingRead 1 ({0, 1, 2} : Finset (Fin 4)) resp = none := by
  decide

/-! ### 3. Multi-slot `PBFT` normal-case, view-change `null` gap filling, and SMR execution -/

/-- Round-robin primary schedule on `Fin 4`. -/
def fin4Primary (v : ℕ) : Fin 4 :=
  ⟨v % 4, Nat.mod_lt v (by decide)⟩

/-- Concrete 9-step normal-case 3-phase trace on `Fin 4` (`f = 1`, `F = {3}`): all honest replicas
`{0, 1, 2}` locally commit `(0, 0, some 1)`. -/
def normalCaseTraceFin4 : List (PBFTAction (Fin 4) ℕ) :=
  let cert : PreparedCert (Fin 4) ℕ := ⟨0, 0, some 1, {1, 2}⟩
  [ .propose 0 0 (some 1)
  , .acceptPrePrepare 1 0 0 (some 1)
  , .acceptPrePrepare 2 0 0 (some 1)
  , .completePrepare 0 cert
  , .completePrepare 1 cert
  , .completePrepare 2 cert
  , .completeCommit 0 cert {0, 1, 2}
  , .completeCommit 1 cert {0, 1, 2}
  , .completeCommit 2 cert {0, 1, 2} ]

def normalCaseStateFin4 : PBFTState (Fin 4) ℕ :=
  normalCaseTraceFin4.foldl (pbftStep fin4Primary 1 ({3} : Finset (Fin 4)))
    (initPBFTState (Fin 4) ℕ)

theorem normalCaseStateFin4_all_honest_commit :
    CommittedLocal normalCaseStateFin4 0 0 0 (some 1) ∧
      CommittedLocal normalCaseStateFin4 1 0 0 (some 1) ∧
      CommittedLocal normalCaseStateFin4 2 0 0 (some 1) := by
  decide

/-- Certificate prepared in view `0` at slot `0` (`some 1`) over backups `{1, 3}`. -/
def certSlot0View0 : PreparedCert (Fin 4) ℕ :=
  ⟨0, 0, some 1, {1, 3}⟩

/-- Certificate prepared in view `0` at slot `2` (`some 2`) over backups `{2, 3}` (while slot `1`
was never proposed in view `0`). -/
def certSlot2View0 : PreparedCert (Fin 4) ℕ :=
  ⟨0, 2, some 2, {2, 3}⟩

/-- Adversarial multi-slot view-change execution on `Fin 4` (`f = 1`, Byzantine `F = {3}`), running
the `Fin 3` history-erasure attack against `n = 4 > 3 * f`:
1. View `0`: replica `0` (`primary 0`) commits slot `0` (`some 1`) via `{0, 1, 3}`, while replica
   `2` prepares slot `2` (`some 2`) via `{0, 2, 3}` (leaving slot `1` unprepared).
2. View change to view `1` (`fin4Primary 1 = 1`): committed replica `0` is slow, and Byzantine `3`
   equivocates at slot `0` and sends an empty `VIEW-CHANGE ⟨1, 3, ∅⟩` attempting to erase slot `0`;
   quorum `{1, 2, 3}` intersects `{0, 1, 3}` at honest `1`, so `computeOset` preserves committed
   slot `0` (`some 1`), fills the gap at slot `1` with `none` (`null` no-op), and carries prepared
   slot `2` (`some 2`). -/
def vc1View1 : ViewChangeMsg (Fin 4) ℕ := ⟨1, 1, {certSlot0View0}⟩
def vc2View1 : ViewChangeMsg (Fin 4) ℕ := ⟨1, 2, {certSlot2View0}⟩
def vc3ByzView1 : ViewChangeMsg (Fin 4) ℕ := ⟨1, 3, ∅⟩

def vsetView1 : Finset (ViewChangeMsg (Fin 4) ℕ) :=
  {vc1View1, vc2View1, vc3ByzView1}

def expectedOsetView1 : Finset (SlotProposal ℕ) :=
  {⟨0, some 1⟩, ⟨1, none⟩, ⟨2, some 2⟩}

theorem computeOset_vsetView1_eq :
    computeOset vsetView1 = some expectedOsetView1 := by
  decide

def multiSlotTraceFin4 : List (PBFTAction (Fin 4) ℕ) :=
  [ .propose 0 0 (some 1)
  , .acceptPrePrepare 1 0 0 (some 1)
  , .byzSend (.prepare 0 0 (some 1) 3)
  , .completePrepare 0 certSlot0View0
  , .completePrepare 1 certSlot0View0
  , .byzSend (.commit 0 0 (some 1) 3)
  , .completeCommit 0 certSlot0View0 {0, 1, 3}
  , .propose 0 2 (some 2)
  , .acceptPrePrepare 2 0 2 (some 2)
  , .byzSend (.prepare 0 2 (some 2) 3)
  , .completePrepare 2 certSlot2View0
  , .byzSend (.prepare 0 0 (some 9) 3)
  , .startViewChange 1 1
  , .startViewChange 2 1
  , .byzSend (.viewChange vc3ByzView1)
  , .formNewView 1 vsetView1
  , .enterNewView 2 1 vsetView1 expectedOsetView1 ]

def multiSlotEndStateFin4 : PBFTState (Fin 4) ℕ :=
  multiSlotTraceFin4.foldl (pbftStep fin4Primary 1 ({3} : Finset (Fin 4)))
    (initPBFTState (Fin 4) ℕ)

theorem multiSlotEndStateFin4_reachable :
    PBFTReachable fin4Primary 1 ({3} : Finset (Fin 4)) multiSlotEndStateFin4 :=
  PBFTReachable.init.foldl_steps multiSlotTraceFin4

/-- Committed command schedule across slots `0..2`: `some 1`, `none` (`null` no-op), `some 2`. -/
def expectedCmdsFin4 : ℕ → Option ℕ
  | 0 => some 1
  | 1 => none
  | 2 => some 2
  | _ => none

theorem multiSlotEndStateFin4_preserves_and_fills_gap :
    CommittedLocal multiSlotEndStateFin4 0 0 0 (some 1) ∧
      PBFTMsg.newView 1 vsetView1 expectedOsetView1 ∈ multiSlotEndStateFin4.network ∧
      (⟨1, 0, some 1⟩ : SlotEntry ℕ) ∈ (multiSlotEndStateFin4.replicas 2).accepted ∧
      (⟨1, 1, none⟩ : SlotEntry ℕ) ∈ (multiSlotEndStateFin4.replicas 2).accepted ∧
      (⟨1, 2, some 2⟩ : SlotEntry ℕ) ∈ (multiSlotEndStateFin4.replicas 2).accepted ∧
      executeSlotLog 0 (· + ·) expectedCmdsFin4 3 = 3 := by
  decide

/-- Instantiating `pbft_smr_state_agreement_idealAuth` on `multiSlotEndStateFin4`: any two honest
replicas executing any committed prefix `k` on any deterministic state machine `(S, smInit, smStep)`
produce the exact same post-state. -/
theorem multiSlotEndStateFin4_smr_agreement {S : Type*} (smInit : S) (smStep : S → ℕ → S)
    {i₁ i₂ : Fin 4} (hi₁ : i₁ ∉ ({3} : Finset (Fin 4))) (hi₂ : i₂ ∉ ({3} : Finset (Fin 4)))
    {views₁ views₂ : ℕ → ℕ} {cmds₁ cmds₂ : ℕ → Option ℕ} {k : ℕ}
    (h₁ : ∀ s < k, CommittedLocal multiSlotEndStateFin4 i₁ (views₁ s) s (cmds₁ s))
    (h₂ : ∀ s < k, CommittedLocal multiSlotEndStateFin4 i₂ (views₂ s) s (cmds₂ s)) :
    executeSlotLog smInit smStep cmds₁ k = executeSlotLog smInit smStep cmds₂ k :=
  pbft_smr_state_agreement_idealAuth (P := Fin 4) (f := 1) (F := {3})
    (by decide) (by decide) multiSlotEndStateFin4_reachable hi₁ hi₂ smInit smStep h₁ h₂

/-! ### 4. Non-minimal `3 * f < |P|` (`Fin 5, f = 1`, quorum size `4`) and `Fin 3` split-brain -/

def fin5Primary (v : ℕ) : Fin 5 :=
  ⟨v % 5, Nat.mod_lt v (by decide)⟩

/-- Verifying that `pbftQuorumSize (Fin 5) 1 = 4` (`|P| = 5 > 3 * 1`, strictly larger than
`3 * f + 1 = 4`) satisfies both 3-phase liveness and cross-view commit agreement. -/
theorem fin5_nonMinimal_quorum_liveness_and_safety :
    pbftQuorumSize (Fin 5) 1 = 4 ∧
      ∃ st' : PBFTState (Fin 5) Bool,
        PBFTReachable fin5Primary 1 ({4} : Finset (Fin 5)) st' ∧
        (∀ i : Fin 5, i ∉ ({4} : Finset (Fin 5)) → CommittedLocal st' i 0 0 (some true)) ∧
        ∀ v₂ val₂, CommittedLocal st' 0 v₂ 0 val₂ → val₂ = some true := by
  refine ⟨by decide, ?_⟩
  obtain ⟨acts, hreach, hcom⟩ :=
    pbft_honest_primary_three_phase_liveness_idealAuth (P := Fin 5) (V := Bool)
      (primary := fin5Primary) (f := 1) (F := {4}) (by decide) PBFTReachable.init
      (v := 0) (s := 0) (some true) (by decide)
      (fun _ _ => ⟨rfl, rfl⟩)
      (fun _ _ _ he => absurd he (Finset.notMem_empty _))
  refine ⟨acts.foldl (pbftStep fin5Primary 1 {4}) (initPBFTState (Fin 5) Bool),
    hreach, hcom, fun v₂ val₂ hcom₂ => ?_⟩
  exact (pbft_commit_agreement_idealAuth (P := Fin 5) (f := 1) (F := {4})
    (by decide) (by decide) hreach
    (i₁ := 1) (i₂ := 0) (by decide) (by decide) (hcom 1 (by decide)) hcom₂).symm

/-- Exercising `exists_pbft_splitBrain_fin3` at `|P| = 3 * f` (`Fin 3, f = 1`): honest replicas
`0 ∉ {2}` and `1 ∉ {2}` reach conflicting SMR service states (`!false = true ≠ false = !true`)
after executing slot `0`. -/
theorem fin3_splitBrain_divergent_smr_states :
    ∃ (F : Finset (Fin 3)) (primary : ℕ → Fin 3) (st : PBFTState (Fin 3) Bool),
      F.card ≤ 1 ∧ (0 : Fin 3) ∉ F ∧ (1 : Fin 3) ∉ F ∧
      PBFTReachable primary 1 F st ∧
      CommittedLocal st 0 0 0 (some false) ∧
      CommittedLocal st 1 1 0 (some true) ∧
      executeSlotLog false (fun _ b => !b) (fun _ => some false) 1 ≠
        executeSlotLog false (fun _ b => !b) (fun _ => some true) 1 := by
  obtain ⟨hcard, h0, h1, primary, st, hreach, hc0, hc1⟩ := exists_pbft_splitBrain_fin3
  exact ⟨{2}, primary, st, hcard, h0, h1, hreach, hc0, hc1, by decide⟩

end CslibFrontierTests.Distributed.ByzantineQuorum
