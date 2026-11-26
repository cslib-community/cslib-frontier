/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.Byzantine.NodeBound
public import CslibFrontier.Computability.Distributed.PartialSynchrony.Basic
public import CslibFrontier.Computability.Distributed.RoundRobin
import Mathlib.Data.Fintype.EquivFin

/-!
# Post-GST deterministic liveness and tight resiliency bounds under partial synchrony

Post-stabilization termination of `byzQuorumProtocol` (`3 * t < Fintype.card P`) and
`omissionQuorumProtocol` (`2 * t < Fintype.card P`) under the shared round-robin
`Cslib.Distributed.rotatingCoordinator`, together
with the matching impossibility results (`2 ≤ Fintype.card P ≤ 3 * t` for unauthenticated Byzantine
faults and `2 ≤ Fintype.card P ≤ 2 * t` for crash/omission faults) and exact characterizations of
when deterministic partial-synchrony consensus is solvable
([Dwork, Lynch and Stockmeyer, §§3.2, 4.3][DworkLynchStockmeyer1988]).

## Main definitions

* `Cslib.Distributed.PartialSynchrony.PartialSyncProtocol.toSyncProtocol`: specializes a
  `PartialSyncProtocol` at `GST = 0` without message omissions (`deliver = fun _ _ _ => true`) to a
  synchronous `Cslib.Distributed.Byzantine.Protocol`.

## Main results

* `Cslib.Distributed.PartialSynchrony.byzQuorum_terminates_in_honest_view`,
  `Cslib.Distributed.PartialSynchrony.byzQuorum_terminates_after_gst`: once `GST` holds, an
  honest-leader view decides for all correct processes at `6 * (v* + 1)`, yielding uniform bounded
  termination by round `gst + 6 * (t + 2)` (`O(t)` rounds after `GST`, cf.
  [Dwork, Lynch and Stockmeyer, §3.2.3, Remark 1, p. 302][DworkLynchStockmeyer1988]).
* `Cslib.Distributed.PartialSynchrony.solvesByzantinePartialSync_byzQuorumProtocol`:
  `byzQuorumProtocol` solves unauthenticated Byzantine partial-synchrony consensus whenever
  `3 * t < Fintype.card P` (witnessing the existence half of
  [Theorem 3.3, p. 302][DworkLynchStockmeyer1988] via a six-subround rotating-coordinator
  view-locking protocol).
* `Cslib.Distributed.PartialSynchrony.omission_terminates_in_honest_view`,
  `Cslib.Distributed.PartialSynchrony.omission_terminates_after_gst`,
  `Cslib.Distributed.PartialSynchrony.solvesOmissionPartialSync_omissionQuorumProtocol`:
  `omissionQuorumProtocol` terminates by round `gst + 3 * (t + 2)` and solves crash/omission
  partial-synchrony consensus whenever `2 * t < Fintype.card P` (witnessing the existence half of
  [Theorem 3.1, p. 297][DworkLynchStockmeyer1988] via a three-subround rotating-coordinator
  view-locking protocol).
* `Cslib.Distributed.PartialSynchrony.not_partialSync_of_le_three_t`: synchronous `GST = 0`
  reduction from `Cslib.Distributed.Byzantine.Protocol.not_solvesByzantineAgreement` refuting
  fixed-round `R` agreement, validity, and termination at `deliver = fun _ _ _ => true` for
  `2 ≤ Fintype.card P ≤ 3 * t`.
* `Cslib.Distributed.PartialSynchrony.not_omissionPartialSync_weakUnanimity`,
  `Cslib.Distributed.PartialSynchrony.not_solvesOmissionPartialSync`: crash/omission impossibility
  for `2 ≤ Fintype.card P ≤ 2 * t` over any `[Nontrivial V]`, proved under weak unanimity (`F = ∅`,
  `∃ gst, IsGST deliver ∅ gst`) by healing the pre-`GST` two-group partition after `R₀`, `R₁`, and
  `max R₀ R₁` ([Theorem 4.3, pp. 305–306][DworkLynchStockmeyer1988] in the §3.1 basic round model).
* `Cslib.Distributed.PartialSynchrony.not_solvesByzantinePartialSync`: unauthenticated Byzantine
  impossibility for `2 ≤ Fintype.card P ≤ 3 * t` over any `[Nontrivial V]`, reducing correct-input
  validity at `GST = 0` to synchronous covering
  ([Pease, Shostak and Lamport][PeaseShostakLamport1980];
  [Fischer, Lynch and Merritt][FischerLynchMerritt1985]), matching the unauthenticated "only if"
  reduction noted in [Dwork, Lynch and Stockmeyer, §1.2, p. 291][DworkLynchStockmeyer1988].
* `Cslib.Distributed.PartialSynchrony.exists_solvesByzantinePartialSync_iff`,
  `Cslib.Distributed.PartialSynchrony.exists_solvesOmissionPartialSync_iff`: sharp characterizations
  `Fintype.card P ≤ 1 ∨ 3 * t < Fintype.card P` and `Fintype.card P ≤ 1 ∨ 2 * t < Fintype.card P`
  ([Table I, p. 291][DworkLynchStockmeyer1988], circumventing asynchronous FLP impossibility via
  eventual `GST` without randomness).

## References

* [C. Dwork, N. Lynch, L. Stockmeyer, *Consensus in the presence of partial
  synchrony*][DworkLynchStockmeyer1988]
* [M. Pease, R. Shostak, L. Lamport, *Reaching agreement in the presence of
  faults*][PeaseShostakLamport1980]
* [M. J. Fischer, N. A. Lynch, M. Merritt, *Easy impossibility proofs for distributed consensus
  problems*][FischerLynchMerritt1985]
-/

public section

namespace Cslib.Distributed.PartialSynchrony

open Finset

/-! ### Post-GST bounded termination of `byzQuorumProtocol` (`3 * t < Fintype.card P`) -/

private theorem card_compl_ge_sub {P : Type*} [Fintype P] [DecidableEq P]
    {F : Finset P} {t : ℕ} (hF : F.card ≤ t) :
    Fintype.card P - t ≤ (Finset.univ \ F).card := by
  have hs := Finset.le_card_sdiff F (Finset.univ : Finset P)
  simp only [Finset.card_univ] at hs
  omega

private theorem card_sub_le_filter_of_compl {P : Type*} [Fintype P]
    {F : Finset P} {t : ℕ} (hF : F.card ≤ t) {p : P → Prop} [DecidablePred p]
    (h : ∀ j ∉ F, p j) : Fintype.card P - t ≤ (Finset.univ.filter p).card := by
  classical
  exact (card_compl_ge_sub hF).trans (Finset.card_le_card fun j hj =>
    Finset.mem_filter.2 ⟨Finset.mem_univ j, h j (Finset.mem_sdiff.1 hj).2⟩)

private theorem succ_le_card_filter_sdiff {P : Type*} [Fintype P] [DecidableEq P]
    {F : Finset P} {t : ℕ} (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t) {p : P → Prop}
    [DecidablePred p] (h : Fintype.card P - t ≤ (Finset.univ.filter p).card) :
    t + 1 ≤ ((Finset.univ.filter p) \ F).card := by
  have := Finset.le_card_sdiff F (Finset.univ.filter p)
  omega

private theorem findQuorumVal_of_compl {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    {procs : List P} (hprocs : ∀ p : P, p ∈ procs) {F : Finset P} {t : ℕ} (hF : F.card ≤ t)
    (hn : 2 * t < Fintype.card P) {f : P → Option V} {v : V} (h : ∀ j ∉ F, f j = some v) :
    findQuorumVal procs (Fintype.card P - t) f = some v :=
  (findQuorumVal_eq_some_iff hprocs (by omega) f v).2 (card_sub_le_filter_of_compl hF h)

section ByzLiveness

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
variable {procs : List P} (leader : ℕ → P) {t : ℕ}

/-- Subround 0 lock-witness completeness: if view `v*` has reliable correct-to-correct delivery in
round `6 * v*` and some correct process `p ∉ F` holds `locked = some lk` at round `6 * v*`, then
every correct process `i ∉ F` records `lk ∈ certPairs` at round `6 * v* + 1` and `lk.view < v*`. -/
private theorem subround0_lock_in_certPairs {F : Finset P}
    (hprocs : ∀ p : P, p ∈ procs) (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t)
    {deliver : ℕ → P → P → Bool} {adv : ℕ → P → P → Option (ByzViewMsg V)} {x : P → V}
    {vStar : ℕ} (hdel0 : ∀ j ∉ F, ∀ i ∉ F, deliver (6 * vStar) j i = true)
    {p : P} (_hp : p ∉ F) {lk : ViewLock V}
    (hlk : ((byzQuorumProtocol P V procs leader t).byzantineState
      F deliver adv x (6 * vStar) p).locked = some lk) :
    lk.view < vStar ∧ ∀ i ∉ F,
      lk ∈ ((byzQuorumProtocol P V procs leader t).byzantineState
        F deliver adv x (6 * vStar + 1) i).certPairs := by
  obtain ⟨hlt_r, hwit⟩ := byzState_locked_witness leader hprocs hn hF (6 * vStar) p hlk
  have hlt : lk.view < vStar := by omega
  refine ⟨hlt, fun i hi => ?_⟩
  rw [byzQuorum_state_succ]
  simp only [byzUpdate, show (6 * vStar) % 6 = 0 by omega,
    show (6 * vStar) / 6 = vStar by omega, computeCertPairs, List.mem_filter, List.mem_dedup,
    List.mem_flatMap, decide_eq_true_eq, rawVoteCount, hlt, ↓reduceIte]
  have hW_mem : ∀ h ∈ (Finset.univ \ F).filter (fun h =>
      lk ∈ ((byzQuorumProtocol P V procs leader t).byzantineState
        F deliver adv x (6 * vStar) h).votedViews),
      lk ∈ extractRawVotes
        (byzIncoming procs leader t F deliver adv x (6 * vStar) i h) := fun h hh => by
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hh
    simpa only [byzIncoming, hh.1, ↓reduceIte, hdel0 h hh.1 i hi, byzSend, Nat.mul_mod_right,
      extractRawVotes] using hh.2
  obtain ⟨h₀, hh₀⟩ := Finset.card_pos.1 (lt_of_lt_of_le (by omega) hwit)
  refine ⟨⟨h₀, hprocs h₀, hW_mem h₀ hh₀⟩, ?_⟩
  rw [length_filter_dedup_eq_card hprocs]
  refine le_trans (by omega) (hwit.trans (Finset.card_le_card fun h hh => ?_))
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] using hW_mem h hh

/-- Subround 0 input-properness completeness: when round `6 * v*` delivers between all correct
processes, either some value `w₀` appears in `properReport.freqVals` at every correct process, or
`properReport.allProper = true` at every correct process. -/
private theorem subround0_proper_complete {F : Finset P}
    (hprocs : ∀ p : P, p ∈ procs) (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t)
    {deliver : ℕ → P → P → Bool} {adv : ℕ → P → P → Option (ByzViewMsg V)} {x : P → V}
    {vStar : ℕ} (hdel0 : ∀ j ∉ F, ∀ i ∉ F, deliver (6 * vStar) j i = true) :
    (∃ w₀, ∀ i ∉ F, w₀ ∈ ((byzQuorumProtocol P V procs leader t).byzantineState
      F deliver adv x (6 * vStar + 1) i).properReport.freqVals) ∨
    (∀ i ∉ F, ((byzQuorumProtocol P V procs leader t).byzantineState
      F deliver adv x (6 * vStar + 1) i).properReport.allProper = true) := by
  have hH_card : Fintype.card P - t ≤ (Finset.univ \ F).card := card_compl_ge_sub hF
  have hH_init : ∀ i ∉ F, ∀ h ∉ F,
      extractRawInit (byzIncoming procs leader t F deliver adv x (6 * vStar) i h) = some (x h) := by
    intro i hi h hhF
    simp only [byzIncoming, hhF, ↓reduceIte, hdel0 h hhF i hi, byzSend,
      show (6 * vStar) % 6 = 0 by omega, extractRawInit, byzState_input_eq]
  by_cases hex : ∃ w₀ : V, t + 1 ≤ ((Finset.univ \ F).filter fun h => x h = w₀).card
  · obtain ⟨w₀, hw₀⟩ := hex
    refine Or.inl ⟨w₀, fun i hi => ?_⟩
    rw [byzQuorum_state_succ]
    simp only [byzUpdate, show (6 * vStar) % 6 = 0 by omega, computeProperReport,
      List.mem_filter, List.mem_dedup, List.mem_filterMap, decide_eq_true_eq]
    obtain ⟨h₀, hh₀⟩ := Finset.card_pos.1 (lt_of_lt_of_le (by omega) hw₀)
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hh₀
    refine ⟨⟨h₀, hprocs h₀, ?_⟩, ?_⟩
    · rw [hH_init i hi h₀ hh₀.1, hh₀.2]
    · rw [countVal_eq_card hprocs]
      refine le_trans hw₀ (Finset.card_le_card fun h hh => ?_)
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hh ⊢
      rw [hH_init i hi h hh.1, hh.2]
  · refine Or.inr fun i hi => ?_
    rw [byzQuorum_state_succ]
    simp only [byzUpdate, show (6 * vStar) % 6 = 0 by omega, computeProperReport,
      decide_eq_true_eq]
    constructor
    · rw [length_filter_dedup_eq_card hprocs]
      refine le_trans (by omega) (card_sub_le_filter_of_compl hF fun h hhF => ?_)
      rw [hH_init i hi h hhF, Option.isSome_some]
    · intro j hj
      simp only [List.mem_filter, List.mem_dedup] at hj
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hj.2
      rw [List.filter_filter, length_filter_dedup_eq_card hprocs]
      have hsd := Finset.le_card_sdiff ((Finset.univ \ F).filter fun h => x h = w) (Finset.univ \ F)
      have hlt := Nat.lt_of_not_ge fun hge => hex ⟨w, hge⟩
      refine le_trans (by omega) (Finset.card_le_card (s := (Finset.univ \ F) \
        (Finset.univ \ F).filter fun h => x h = w) fun h hh => ?_)
      obtain ⟨hhH, hhnot⟩ := Finset.mem_sdiff.1 hh
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hhH
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
        decide_eq_true_eq, hH_init i hi h hhH, Option.isSome_some, hw, ne_eq, Option.some.injEq,
        and_true]
      exact fun hx => hhnot (Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨Finset.mem_univ h, hhH⟩, hx⟩)

/-- **Single-honest-view termination (`byzQuorum_terminates_in_honest_view`):** when
`3 * t < Fintype.card P`, `F.card ≤ t`, the view coordinator `leader v*` is correct (`∉ F`), and
all 6 subrounds `6 * v* .. 6 * v* + 5` of view `v*` deliver every message between correct
processes, every correct process `i ∉ F` has decided (`isSome = true`) at `6 * (v* + 1)`. -/
theorem byzQuorum_terminates_in_honest_view {F : Finset P}
    (hprocs : ∀ p : P, p ∈ procs) (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t)
    {deliver : ℕ → P → P → Bool} {adv : ℕ → P → P → Option (ByzViewMsg V)} (x : P → V)
    {vStar : ℕ} (hl : leader vStar ∉ F)
    (hsync : ∀ r, 6 * vStar ≤ r → r < 6 * (vStar + 1) → ∀ j ∉ F, ∀ i ∉ F, deliver r j i = true) :
    ∀ i ∉ F, ((byzQuorumProtocol P V procs leader t).byzantineDecision
      F deliver adv x (6 * (vStar + 1)) i).isSome = true := by
  have hlen : procs.dedup.length = Fintype.card P := dedup_length_eq_card hprocs
  have hmod : ∀ k < 6, (6 * vStar + k) % 6 = k := fun k hk => by omega
  have hdiv : ∀ k < 6, (6 * vStar + k) / 6 = vStar := fun k hk => by omega
  have hdel : ∀ k < 6, ∀ j ∉ F, ∀ i ∉ F, deliver (6 * vStar + k) j i = true :=
    fun k hk => hsync _ (by omega) (by omega)
  have hdel0 : ∀ j ∉ F, ∀ i ∉ F, deliver (6 * vStar) j i = true := hdel 0 (by omega)
  let st := (byzQuorumProtocol P V procs leader t).byzantineState F deliver adv x
  -- Locked state of every process is unchanged from `6 * vStar` to `6 * vStar + 2`.
  have hlk_2_eq_0 (i : P) : (st (6 * vStar + 2) i).locked = (st (6 * vStar) i).locked :=
    (byzState_locked_unchanged_of_ne_four leader F deliver adv x (6 * vStar + 1) (by omega) i).trans
      (byzState_locked_unchanged_of_ne_four leader F deliver adv x (6 * vStar) (by omega) i)
  -- Step 1 (end of Subround 1): honest leader `leader vStar` prepares `some prop` accepted by
  -- every correct voter `i ∉ F`.
  have hprop_ok : ∃ prop : Proposal V,
      (st (6 * vStar + 2) (leader vStar)).leaderProposal = some prop ∧
      ∀ i ∉ F, acceptsProposal t (st (6 * vStar + 2) i) prop = true := by
    let m1 := byzIncoming procs leader t F deliver adv x (6 * vStar + 1)
    have hm1_mod := hmod 1 (by omega)
    have hm1_div := hdiv 1 (by omega)
    have hm1_honest : ∀ i ∉ F, ∀ j ∉ F,
        extractCertStatus (m1 i j) =
          some ((st (6 * vStar + 1) j).properReport, (st (6 * vStar + 1) j).certPairs) :=
      fun i hi j hj => by
        simp only [m1, byzIncoming, hj, ↓reduceIte, hdel 1 (by omega) j hj i hi, byzSend, hm1_mod,
          extractCertStatus, st]
    let allCandsL := (procs.dedup.flatMap fun j =>
      ((extractCertStatus (m1 (leader vStar) j)).map Prod.snd).getD []).dedup
    let lCerts := allCandsL.filter fun lk =>
      decide (procs.dedup.length - t ≤ certSupportCount procs vStar (m1 (leader vStar)) lk)
    -- Every correct lock at `6 * vStar` lands in `lCerts` at `leader vStar`.
    have hlock_in_lCerts : ∀ p ∉ F, ∀ lk, (st (6 * vStar) p).locked = some lk → lk ∈ lCerts :=
      fun p hp lk hplk => by
        obtain ⟨hlt, hcp⟩ := subround0_lock_in_certPairs leader hprocs hn hF hdel0 hp hplk
        simp only [lCerts, allCandsL, List.mem_filter, List.mem_dedup, List.mem_flatMap,
          decide_eq_true_eq]
        refine ⟨⟨leader vStar, hprocs (leader vStar), ?_⟩, ?_⟩
        · simpa only [hm1_honest (leader vStar) hl (leader vStar) hl, Option.map_some,
            Option.getD_some] using hcp (leader vStar) hl
        · simp only [certSupportCount, hlt, ↓reduceIte, hlen, length_filter_dedup_eq_card hprocs]
          refine card_sub_le_filter_of_compl hF fun j hjF => ?_
          simpa only [hm1_honest (leader vStar) hl j hjF, decide_eq_true_eq] using hcp j hjF
    cases hpm : pickMaxLock lCerts with
    | some best =>
      refine ⟨⟨best.val, some best.view⟩, ?_, fun i hi => ?_⟩
      · dsimp only [st, lCerts, allCandsL, m1] at hpm ⊢
        rw [byzQuorum_state_succ]
        simp only [byzUpdate, hm1_mod, hm1_div, hpm]
      · -- `best ∈ lCerts` gives `≥ n - 2t ≥ t + 1` correct relays to every `i ∉ F`.
        have hbest_mem : best ∈ lCerts := pickMaxLock_mem hpm
        simp only [lCerts, List.mem_filter, decide_eq_true_eq] at hbest_mem
        have hcntL := hbest_mem.2
        simp only [certSupportCount] at hcntL
        split_ifs at hcntL with hbv_lt
        · rw [hlen, length_filter_dedup_eq_card hprocs] at hcntL
          let predL : P → Prop := fun j =>
            (match extractCertStatus (m1 (leader vStar) j) with
              | some (_, cp) => decide (best ∈ cp)
              | none => false) = true
          have hSL_card : t + 1 ≤ ((Finset.univ.filter predL) \ F).card :=
            succ_le_card_filter_sdiff hn hF hcntL
          have hSL_cp : ∀ j ∈ (Finset.univ.filter predL) \ F,
              best ∈ (st (6 * vStar + 1) j).certPairs := fun j hj => by
            simp only [predL, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hj
            simpa only [hm1_honest (leader vStar) hl j hj.2, decide_eq_true_eq] using hj.1
          have hbest_vc : best ∈ (st (6 * vStar + 2) i).voterCerts := by
            dsimp only [st]
            rw [byzQuorum_state_succ]
            simp only [byzUpdate, hm1_mod, hm1_div, List.mem_filter, List.mem_dedup,
              List.mem_flatMap, decide_eq_true_eq, certSupportCount, hbv_lt, ↓reduceIte]
            obtain ⟨j₀, hj₀⟩ := Finset.card_pos.1 (lt_of_lt_of_le (by omega) hSL_card)
            have hj₀F : j₀ ∉ F := (Finset.mem_sdiff.1 hj₀).2
            refine ⟨⟨j₀, hprocs j₀, ?_⟩, ?_⟩
            · change best ∈ ((extractCertStatus (m1 i j₀)).map Prod.snd).getD []
              simpa only [hm1_honest i hi j₀ hj₀F, Option.map_some, Option.getD_some] using
                hSL_cp j₀ hj₀
            · rw [length_filter_dedup_eq_card hprocs]
              refine le_trans hSL_card (Finset.card_le_card fun j hj => ?_)
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              change (match extractCertStatus (m1 i j) with
                | some (_, cp) => decide (best ∈ cp) | none => false) = true
              simpa only [hm1_honest i hi j (Finset.mem_sdiff.1 hj).2, decide_eq_true_eq] using
                hSL_cp j hj
          cases hilk : (st (6 * vStar) i).locked with
          | none => simp [acceptsProposal, hlk_2_eq_0 i, hilk, hbest_vc]
          | some lk =>
            simp [acceptsProposal, hlk_2_eq_0 i, hilk, hbest_vc,
              pickMaxLock_le hpm lk (hlock_in_lCerts i hi lk hilk)]
        · omega
    | none =>
      have hlCerts_empty : lCerts = [] := pickMaxLock_eq_none_iff.1 hpm
      have hunlocked : ∀ i ∉ F, (st (6 * vStar) i).locked = none := fun i hi =>
        Option.eq_none_iff_forall_ne_some.2 fun lk hilk => by
          simpa only [hlCerts_empty, List.not_mem_nil] using hlock_in_lCerts i hi lk hilk
      let snapsL := procs.dedup.filterMap fun j =>
        (extractCertStatus (m1 (leader vStar) j)).map Prod.fst
      let valCands := ((st (6 * vStar + 1) (leader vStar)).input ::
        snapsL.flatMap ProperReport.freqVals).dedup
      -- `valCands.find?` succeeds at `leader vStar`.
      have hfind_ne : (valCands.find? fun w =>
          decide (procs.dedup.length - t ≤ properSupportCount snapsL w)) ≠ none := by
        intro hfn
        rw [List.find?_eq_none] at hfn
        have hcnt : ∀ w, (∀ j ∉ F, (st (6 * vStar + 1) j).properReport.allProper = true ∨
            w ∈ (st (6 * vStar + 1) j).properReport.freqVals) →
            decide (procs.dedup.length - t ≤ properSupportCount snapsL w) = true := by
          intro w hw
          simp only [snapsL, properSupportCount, filterMap_fst_filter_length, hlen,
            length_filter_dedup_eq_card hprocs, decide_eq_true_eq]
          refine card_sub_le_filter_of_compl hF fun j hjF => ?_
          simp only [hm1_honest (leader vStar) hl j hjF, Bool.or_eq_true, decide_eq_true_eq]
          exact hw j hjF
        rcases subround0_proper_complete leader hprocs hn hF
          (adv := adv) (x := x) hdel0 with ⟨w₀, hw₀⟩ | hall
        · refine hfn w₀ ?_ (hcnt w₀ fun j hj => Or.inr (hw₀ j hj))
          simp only [valCands, List.mem_dedup, List.mem_cons, List.mem_flatMap]
          refine Or.inr ⟨(st (6 * vStar + 1) (leader vStar)).properReport, ?_,
            hw₀ (leader vStar) hl⟩
          simp only [snapsL, List.mem_filterMap]
          exact ⟨leader vStar, List.mem_dedup.2 (hprocs (leader vStar)),
            by rw [hm1_honest (leader vStar) hl (leader vStar) hl]; rfl⟩
        · exact hfn _ (List.mem_dedup.2 List.mem_cons_self) (hcnt _ fun j hj => Or.inl (hall j hj))
      obtain ⟨wStar, hwStar⟩ := Option.ne_none_iff_exists'.1 hfind_ne
      have hwStar_cnt : procs.dedup.length - t ≤ properSupportCount snapsL wStar := by
        simpa using List.find?_some hwStar
      refine ⟨⟨wStar, none⟩, ?_, fun i hi => ?_⟩
      · dsimp only [st, lCerts, allCandsL, valCands, snapsL, m1] at hpm hwStar ⊢
        rw [byzQuorum_state_succ]
        simp only [byzUpdate, hm1_mod, hm1_div, hpm, hwStar, Option.map_some]
      · simp only [acceptsProposal, hlk_2_eq_0 i, hunlocked i hi, Option.isNone_none,
          Bool.true_and, decide_eq_true_eq]
        simp only [snapsL, properSupportCount, filterMap_fst_filter_length, hlen,
          length_filter_dedup_eq_card hprocs] at hwStar_cnt
        let predP : P → Prop := fun j =>
          (match extractCertStatus (m1 (leader vStar) j) with
            | some (rep, _) => rep.allProper || decide (wStar ∈ rep.freqVals)
            | none => false) = true
        have hSP_card : t + 1 ≤ ((Finset.univ.filter predP) \ F).card :=
          succ_le_card_filter_sdiff hn hF hwStar_cnt
        dsimp only [st]
        rw [byzQuorum_state_succ]
        simp only [byzUpdate, hm1_mod, hm1_div, properSupportCount, filterMap_fst_filter_length,
          length_filter_dedup_eq_card hprocs]
        refine le_trans hSP_card (Finset.card_le_card fun j hj => ?_)
        simp only [predP, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        obtain ⟨hjL, hjF⟩ := hj
        dsimp only [m1] at hm1_honest hjL
        rwa [hm1_honest i hi j hjF, ← hm1_honest (leader vStar) hl j hjF]
  obtain ⟨prop, hpropL, hpropV⟩ := hprop_ok
  -- Step 2 (Subround 2 → 3): every correct `i ∉ F` sets `myEcho = some prop.val`.
  have hecho3 : ∀ i ∉ F, (st (6 * vStar + 3) i).myEcho = some prop.val := by
    intro i hi
    have hacc := hpropV i hi
    dsimp only [st] at hpropL hacc ⊢
    rw [byzQuorum_state_succ]
    simp only [byzUpdate, hmod 2 (by omega), hdiv 2 (by omega), byzIncoming, hl, ↓reduceIte,
      hdel 2 (by omega) (leader vStar) hl i hi, byzSend, hpropL, true_and, hacc]
  -- Steps 3–5 (Subrounds 3 → 4 → 5 → `6 * (vStar + 1)`): every correct `i ∉ F` observes `≥ n - t`
  -- echoes, votes and commits, setting `myVote`, `myCommit` and finally `decided`.
  have hvote4 : ∀ i ∉ F, (st (6 * vStar + 4) i).myVote = some prop.val := fun i hi => by
    dsimp only [st] at hecho3 ⊢
    rw [byzQuorum_state_succ]
    simp only [byzUpdate, hmod 3 (by omega), hdiv 3 (by omega), hlen]
    rw [findQuorumVal_of_compl hprocs hF (by omega) (v := prop.val) fun j hjF => by
      simp only [byzIncoming, hjF, ↓reduceIte, hdel 3 (by omega) j hjF i hi, byzSend,
        hmod 3 (by omega), hdiv 3 (by omega), hecho3 j hjF, extractEcho]]
  have hcommit5 : ∀ i ∉ F, (st (6 * vStar + 5) i).myCommit = some prop.val := fun i hi => by
    dsimp only [st] at hvote4 ⊢
    rw [byzQuorum_state_succ]
    simp only [byzUpdate, hmod 4 (by omega), hdiv 4 (by omega), hlen]
    rw [findQuorumVal_of_compl hprocs hF (by omega) (v := prop.val) fun j hjF => by
      simp only [byzIncoming, hjF, ↓reduceIte, hdel 4 (by omega) j hjF i hi, byzSend,
        hmod 4 (by omega), hdiv 4 (by omega), hvote4 j hjF, extractVote]]
  intro i hi
  dsimp only [st] at hcommit5
  change ((byzQuorumProtocol P V procs leader t).byzantineState
    F deliver adv x ((6 * vStar + 5) + 1) i).decided.isSome = true
  rw [byzQuorum_state_succ]
  simp only [byzUpdate, hmod 5 (by omega), hdiv 5 (by omega), hlen]
  rw [findQuorumVal_of_compl hprocs hF (by omega) (v := prop.val) fun j hjF => by
    simp only [byzIncoming, hjF, ↓reduceIte, hdel 5 (by omega) j hjF i hi, byzSend,
      hmod 5 (by omega), hdiv 5 (by omega), hcommit5 j hjF, extractCommit]]
  cases ((byzQuorumProtocol P V procs leader t).byzantineState
    F deliver adv x (6 * vStar + 5) i).decided <;> rfl

/-- **Post-GST bounded termination (`byzQuorum_terminates_after_gst`):** under
`rotatingCoordinator`, once `IsGST deliver F gst` holds with `3 * t < Fintype.card P` and
`F.card ≤ t`, every correct process `i ∉ F` has decided by round `gst + 6 * (t + 2)` (`O(t)` rounds
after `GST`, cf.
[Dwork, Lynch and Stockmeyer, §3.2.3, Remark 1, p. 302][DworkLynchStockmeyer1988]). -/
theorem byzQuorum_terminates_after_gst {F : Finset P}
    (hprocs : ∀ p : P, p ∈ procs) (fallback : P)
    (hn : 3 * t < Fintype.card P) (hF : F.card ≤ t)
    {deliver : ℕ → P → P → Bool} {gst : ℕ} (hgst : IsGST deliver F gst)
    (adv : ℕ → P → P → Option (ByzViewMsg V)) (x : P → V) :
    ∀ i ∉ F,
      ((byzQuorumProtocol P V procs (rotatingCoordinator procs fallback) t).byzantineDecision
        F deliver adv x (gst + 6 * (t + 2)) i).isSome = true := by
  let v₀ := (gst + 5) / 6
  obtain ⟨vStar, hv₀_le, hvStar_le, hl⟩ :=
    exists_rotatingCoordinator_notMem hprocs fallback hF (by omega) v₀
  have hdec := byzQuorum_terminates_in_honest_view (rotatingCoordinator procs fallback) hprocs hn hF
    (adv := adv) x hl (fun r hr_ge _ j hj i hi => hgst r (by omega) j hj i hi)
  intro i hi
  obtain ⟨val, hval⟩ := Option.isSome_iff_exists.1 (hdec i hi)
  exact Option.isSome_iff_exists.2 ⟨val, byzQuorum_irrevocable
    (rotatingCoordinator procs fallback) F deliver adv x (by omega) i val hval⟩

/-- `byzQuorumProtocol` with `rotatingCoordinator` solves unauthenticated Byzantine
partial-synchrony consensus whenever `3 * t < Fintype.card P` (witnessing the existence half of
[Dwork, Lynch and Stockmeyer, Theorem 3.3, p. 302][DworkLynchStockmeyer1988] in the §3.1 basic round
model via a six-subround rotating-coordinator view-locking protocol). -/
theorem solvesByzantinePartialSync_byzQuorumProtocol
    (hprocs : ∀ p : P, p ∈ procs) (fallback : P) (hn : 3 * t < Fintype.card P) :
    (byzQuorumProtocol P V procs (rotatingCoordinator procs fallback) t).SolvesByzantinePartialSync
      t where
  irrevocable F _ deliver adv x _ _ hr i _ val hdec :=
    byzQuorum_irrevocable (rotatingCoordinator procs fallback) F deliver adv x hr i val hdec
  agreement _ hF deliver adv x _ _ _ _ _ _ _ _ h₁ h₂ :=
    byzQuorum_agreement (rotatingCoordinator procs fallback) hprocs hn hF deliver adv x h₁ h₂
  validity _ hF deliver adv _ _ hv r i _ _ hw :=
    byzQuorum_validity (rotatingCoordinator procs fallback) hprocs hn hF deliver adv hv r i hw
  termination _ hF _ gst adv x hgst i hi :=
    ⟨gst + 6 * (t + 2), byzQuorum_terminates_after_gst hprocs fallback hn hF hgst adv x i hi⟩

end ByzLiveness

/-! ### Post-GST bounded termination of `omissionQuorumProtocol` (`2 * t < Fintype.card P`) -/

section OmissionLiveness

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
variable {procs : List P} (leader : ℕ → P) {t : ℕ}

/-- **Single-honest-view omission termination (`omission_terminates_in_honest_view`):** if
`2 * t < Fintype.card P`, `F.card ≤ t`, `leader v* ∉ F`, and all 3 subrounds `3 * v* .. 3 * v* + 2`
deliver every message between correct processes, then every correct process `i ∉ F` has decided at
round `3 * (v* + 1)`. -/
theorem omission_terminates_in_honest_view {F : Finset P}
    (hprocs : ∀ p : P, p ∈ procs) (hn : 2 * t < Fintype.card P) (hF : F.card ≤ t)
    {deliver : ℕ → P → P → Bool} (x : P → V) {vStar : ℕ} (hl : leader vStar ∉ F)
    (hsync : ∀ r, 3 * vStar ≤ r → r < 3 * (vStar + 1) → ∀ j ∉ F, ∀ i ∉ F, deliver r j i = true) :
    ∀ i ∉ F, ((omissionQuorumProtocol P V procs leader t).omissionDecision
      deliver x (3 * (vStar + 1)) i).isSome = true := by
  have hlen : procs.dedup.length = Fintype.card P := dedup_length_eq_card hprocs
  let st := (omissionQuorumProtocol P V procs leader t).omissionState deliver x
  -- Subround 0 → 1: `leader vStar` receives ≥ `n - t` `.status` messages and prepares `some prop`
  -- compatible with every correct voter's lock.
  have hprop : ∃ prop : Proposal V,
      (st (3 * vStar + 1) (leader vStar)).leaderProposal = some prop ∧
      ∀ i ∉ F, acceptsOmissionProposal vStar vStar (st (3 * vStar + 1) i) prop = true := by
    let m0 := omissionIncoming procs leader t deliver x (3 * vStar) (leader vStar)
    have hcnt : procs.dedup.length - t ≤
        (procs.dedup.filter fun j => isOmissionStatus (m0 j)).length := by
      rw [hlen, length_filter_dedup_eq_card hprocs]
      refine card_sub_le_filter_of_compl hF fun j hjF => ?_
      simp only [m0, omissionIncoming,
        hsync (3 * vStar) (by omega) (by omega) j hjF (leader vStar) hl, ↓reduceIte, omissionSend,
        show (3 * vStar) % 3 = 0 by omega, isOmissionStatus]
    have hlk1_eq_0 (i : P) : (st (3 * vStar + 1) i).locked = (st (3 * vStar) i).locked :=
      omission_locked_unchanged_of_ne_one leader deliver x (3 * vStar) (by omega) i
    let locks := procs.dedup.filterMap fun j => extractStatusLock (m0 j)
    have hlock_in : ∀ i ∉ F, ∀ lk, (st (3 * vStar) i).locked = some lk → lk ∈ locks := by
      intro i hi lk hilk
      simp only [locks, List.mem_filterMap]
      refine ⟨i, List.mem_dedup.2 (hprocs i), ?_⟩
      simp only [m0, omissionIncoming,
        hsync (3 * vStar) (by omega) (by omega) i hi (leader vStar) hl, ↓reduceIte, omissionSend,
        show (3 * vStar) % 3 = 0 by omega]
      change extractStatusLock (some (.status (st (3 * vStar) i).input
        (st (3 * vStar) i).locked)) = some lk
      rw [hilk, extractStatusLock]
    have hlProp_eq : (st (3 * vStar + 1) (leader vStar)).leaderProposal =
        some (match pickMaxLock locks with
          | some best => ⟨best.val, some best.view⟩
          | none => ⟨(st (3 * vStar) (leader vStar)).input, none⟩) := by
      dsimp only [m0] at hcnt
      dsimp only [st, locks, m0]
      rw [omissionQuorum_state_succ]
      simp only [omissionUpdate, show (3 * vStar) % 3 = 0 by omega, hcnt, ↓reduceIte]
      cases pickMaxLock _ <;> rfl
    refine ⟨_, hlProp_eq, fun i hi => ?_⟩
    simp only [acceptsOmissionProposal, decide_true, Bool.true_and, hlk1_eq_0 i]
    cases hilk : (st (3 * vStar) i).locked with
    | none => rfl
    | some lk =>
      have hmem := hlock_in i hi lk hilk
      cases hpm : pickMaxLock locks with
      | some best => simp [pickMaxLock_le hpm lk hmem]
      | none => simp only [pickMaxLock_eq_none_iff.1 hpm, List.not_mem_nil] at hmem
  obtain ⟨prop, hpropL, hpropV⟩ := hprop
  -- Subround 1 → 2: every correct `i ∉ F` sets `myAck = some prop.val`.
  have hack2 : ∀ i ∉ F, (st (3 * vStar + 2) i).myAck = some prop.val := fun i hi => by
    have hacc := hpropV i hi
    dsimp only [st] at hpropL hacc ⊢
    rw [omissionQuorum_state_succ]
    simp only [omissionUpdate, show (3 * vStar + 1) % 3 = 1 by omega,
      show (3 * vStar + 1) / 3 = vStar by omega, omissionIncoming,
      hsync (3 * vStar + 1) (by omega) (by omega) (leader vStar) hl i hi,
      ↓reduceIte, omissionSend, hpropL, hacc]
  -- Subround 2 → `3 * (vStar + 1)`: every correct `i ∉ F` observes `≥ n - t` acks and decides.
  intro i hi
  dsimp only [st] at hack2
  change ((omissionQuorumProtocol P V procs leader t).omissionState
    deliver x ((3 * vStar + 2) + 1) i).decided.isSome = true
  rw [omissionQuorum_state_succ]
  simp only [omissionUpdate, show (3 * vStar + 2) % 3 = 2 by omega,
    show (3 * vStar + 2) / 3 = vStar by omega, hlen]
  rw [findQuorumVal_of_compl hprocs hF hn (v := prop.val) fun j hjF => by
    simp only [omissionIncoming, hsync (3 * vStar + 2) (by omega) (by omega) j hjF i hi,
      ↓reduceIte, omissionSend, show (3 * vStar + 2) % 3 = 2 by omega,
      show (3 * vStar + 2) / 3 = vStar by omega, hack2 j hjF, extractAck]]
  cases ((omissionQuorumProtocol P V procs leader t).omissionState
    deliver x (3 * vStar + 2) i).decided <;> rfl

/-- **Post-GST bounded omission termination (`omission_terminates_after_gst`):** under
`rotatingCoordinator`, once `IsGST deliver F gst` holds with `2 * t < Fintype.card P` and
`F.card ≤ t`, every correct process `i ∉ F` has decided by round `gst + 3 * (t + 2)`. -/
theorem omission_terminates_after_gst {F : Finset P}
    (hprocs : ∀ p : P, p ∈ procs) (fallback : P)
    (hn : 2 * t < Fintype.card P) (hF : F.card ≤ t)
    {deliver : ℕ → P → P → Bool} {gst : ℕ} (hgst : IsGST deliver F gst) (x : P → V) :
    ∀ i ∉ F,
      ((omissionQuorumProtocol P V procs (rotatingCoordinator procs fallback) t).omissionDecision
        deliver x (gst + 3 * (t + 2)) i).isSome = true := by
  let v₀ := (gst + 2) / 3
  obtain ⟨vStar, hv₀_le, hvStar_le, hl⟩ :=
    exists_rotatingCoordinator_notMem hprocs fallback hF (by omega) v₀
  have hdec := omission_terminates_in_honest_view (rotatingCoordinator procs fallback) hprocs hn hF
    x hl (fun r hr_ge _ j hj i hi => hgst r (by omega) j hj i hi)
  intro i hi
  obtain ⟨val, hval⟩ := Option.isSome_iff_exists.1 (hdec i hi)
  exact Option.isSome_iff_exists.2 ⟨val,
    omission_irrevocable (rotatingCoordinator procs fallback) deliver x (by omega) i val hval⟩

/-- `omissionQuorumProtocol` with `rotatingCoordinator` solves crash/omission partial-synchrony
consensus whenever `2 * t < Fintype.card P` (witnessing the existence half of
[Dwork, Lynch and Stockmeyer, Theorem 3.1, p. 297][DworkLynchStockmeyer1988] in the §3.1 basic round
model via a three-subround rotating-coordinator view-locking protocol). -/
theorem solvesOmissionPartialSync_omissionQuorumProtocol
    (hprocs : ∀ p : P, p ∈ procs) (fallback : P) (hn : 2 * t < Fintype.card P) :
    (omissionQuorumProtocol P V procs
      (rotatingCoordinator procs fallback) t).SolvesOmissionPartialSync t where
  irrevocable deliver x _ _ hr i val hdec :=
    omission_irrevocable (rotatingCoordinator procs fallback) deliver x hr i val hdec
  agreement _ _ deliver x _ _ _ _ _ _ _ _ h₁ h₂ :=
    omission_agreement (rotatingCoordinator procs fallback) hprocs hn deliver x h₁ h₂
  validity deliver _ _ hv r i _ hw :=
    omission_validity (rotatingCoordinator procs fallback) hprocs hn deliver hv r i hw
  termination _ hF _ gst x hgst i hi :=
    ⟨gst + 3 * (t + 2), omission_terminates_after_gst hprocs fallback hn hF hgst x i hi⟩

end OmissionLiveness

/-! ### Synchronous `GST = 0` reduction and tight lower bounds (`2t < n` and `3t < n`) -/

/-- Specializes a `PartialSyncProtocol P V S M` to a synchronous Boolean
`Cslib.Distributed.Byzantine.Protocol P S (Option M)` at `GST = 0` (`deliver = fun _ _ _ => true`),
mapping input bits `false ↦ v₀`, `true ↦ v₁` and testing `output i s = some v₁`. -/
@[expose] def PartialSyncProtocol.toSyncProtocol {P V S M : Type*} [DecidableEq V]
    (π : PartialSyncProtocol P V S M) (v₀ v₁ : V) :
    Cslib.Distributed.Byzantine.Protocol P S (Option M) where
  init i b := π.init i (if b then v₁ else v₀)
  send r i s j := some (π.send r i s j)
  update r i s m := π.update r i s m
  output i s := decide (π.output i s = some v₁)

/-- With zero network omissions (`deliver = fun _ _ _ => true`), `byzantineState` coincides round
for round with `(π.toSyncProtocol v₀ v₁).state`. -/
theorem PartialSyncProtocol.byzantineState_always_eq_state {P V S M : Type*}
    [DecidableEq P] [DecidableEq V] (π : PartialSyncProtocol P V S M) (v₀ v₁ : V)
    (F : Finset P) (adv : ℕ → P → P → Option M) (b : P → Bool) :
    ∀ r i, π.byzantineState F (fun _ _ _ => true) adv (fun j => if b j then v₁ else v₀) r i =
      (π.toSyncProtocol v₀ v₁).state F adv b r i
  | 0, _ => rfl
  | r + 1, i => by
    rw [PartialSyncProtocol.byzantineState, Cslib.Distributed.Byzantine.Protocol.state]
    congr 1
    · exact π.byzantineState_always_eq_state v₀ v₁ F adv b r i
    · funext j
      by_cases hj : j ∈ F <;>
        simp [hj, PartialSyncProtocol.toSyncProtocol,
          π.byzantineState_always_eq_state v₀ v₁ F adv b r j]

/-- **Synchronous-special-case impossibility (`not_partialSync_of_le_three_t`):** since `GST = 0`
with `deliver = fun _ _ _ => true` embeds synchronous `Byzantine.Protocol` directly,
`Cslib.Distributed.Byzantine.Protocol.not_solvesByzantineAgreement` rules out any protocol that
achieves fixed-round `R` agreement, correct-input validity, and termination at
`deliver = fun _ _ _ => true` when `2 ≤ Fintype.card P ≤ 3 * t`. -/
theorem not_partialSync_of_le_three_t {P V S M : Type*}
    [Fintype P] [DecidableEq P] [Nontrivial V]
    (π : PartialSyncProtocol P V S M) {t R : ℕ}
    (h2 : 2 ≤ Fintype.card P) (h3 : Fintype.card P ≤ 3 * t)
    (hag : ∀ F : Finset P, F.card ≤ t → ∀ adv x,
      ∀ i ∉ F, ∀ j ∉ F, ∀ v₁ v₂,
        π.byzantineDecision F (fun _ _ _ => true) adv x R i = some v₁ →
        π.byzantineDecision F (fun _ _ _ => true) adv x R j = some v₂ → v₁ = v₂)
    (hval : ∀ F : Finset P, F.card ≤ t → ∀ adv x v,
      (∀ i ∉ F, x i = v) → ∀ i ∉ F, ∀ w,
        π.byzantineDecision F (fun _ _ _ => true) adv x R i = some w → w = v)
    (hbdd : ∀ F : Finset P, F.card ≤ t → ∀ adv x,
      ∀ i ∉ F, (π.byzantineDecision F (fun _ _ _ => true) adv x R i).isSome = true) :
    False := by
  classical
  obtain ⟨v₀, v₁, hne⟩ := exists_pair_ne V
  refine (π.toSyncProtocol v₀ v₁).not_solvesByzantineAgreement (t := t) (R := R) h2 h3 ?_
  have hdec (F : Finset P) (adv) (b : P → Bool) (i : P) :
      (π.toSyncProtocol v₀ v₁).decision F adv b R i =
        decide (π.byzantineDecision F (fun _ _ _ => true) adv
          (fun k => if b k then v₁ else v₀) R i = some v₁) :=
    congrArg ((π.toSyncProtocol v₀ v₁).output i)
      (π.byzantineState_always_eq_state v₀ v₁ F adv b R i).symm
  refine ⟨fun F hF adv b i hi j hj => ?_, fun F hF adv b bit hbit i hi => ?_⟩
  · obtain ⟨wi, hwi⟩ := Option.isSome_iff_exists.1 (hbdd F hF adv _ i hi)
    obtain ⟨wj, hwj⟩ := Option.isSome_iff_exists.1 (hbdd F hF adv _ j hj)
    rw [hdec, hdec, hwi, hwj, hag F hF adv _ i hi j hj wi wj hwi hwj]
  · obtain ⟨wi, hwi⟩ := Option.isSome_iff_exists.1 (hbdd F hF adv _ i hi)
    rw [hdec, hwi, hval F hF adv _ (if bit then v₁ else v₀)
      (fun k hk => by simp only [hbit k hk]) i hi wi hwi]
    cases bit <;> simp [hne]

/-- **Unbounded unauthenticated Byzantine impossibility (`not_solvesByzantinePartialSync`,
[Dwork, Lynch and Stockmeyer, §1.2 and Table I, p. 291][DworkLynchStockmeyer1988]):** when
`2 ≤ Fintype.card P ≤ 3 * t` and `V` has at least two values, no deterministic protocol solves
`SolvesByzantinePartialSync t` (even with run-dependent unbounded termination rounds and infinite
message spaces).

As noted in [Dwork, Lynch and Stockmeyer, §1.2, p. 291][DworkLynchStockmeyer1988], for
unauthenticated Byzantine faults with correct-input validity (`∀ i ∉ F, x i = v`) the `2 ≤ |P| ≤ 3t`
lower bound reduces at `GST = 0` (`deliver = fun _ _ _ => true`) to the completely synchronous
bound of [Pease, Shostak and Lamport][PeaseShostakLamport1980], proved here via the synchronous
covering simulation `Cslib.Distributed.Byzantine.Protocol.state_eq_coverState` of
[Fischer, Lynch and Merritt][FischerLynchMerritt1985] (distinct from DLS Theorem 4.4, p. 306, which
establishes `2 ≤ N ≤ 3t` for *authenticated* Byzantine faults and *weak unanimity* via pre-`GST`
partition delay and is not formalized here). -/
theorem not_solvesByzantinePartialSync {P V S M : Type*}
    [Fintype P] [DecidableEq P] [Nontrivial V]
    (π : PartialSyncProtocol P V S M) {t : ℕ}
    (h2 : 2 ≤ Fintype.card P) (h3 : Fintype.card P ≤ 3 * t) :
    ¬ π.SolvesByzantinePartialSync t := by
  classical
  intro h
  obtain ⟨v₀, v₁, hne⟩ := exists_pair_ne V
  let e := Fintype.equivFin P
  let g : P → Fin 3 := fun i => ⟨2 * (e i : ℕ) % 3, Nat.mod_lt _ (by omega)⟩
  have hcard : ∀ k : Fin 3, (Finset.univ.filter fun i => g i = k).card ≤ t := by
    intro k
    calc (Finset.univ.filter fun i => g i = k).card
        ≤ (Finset.range t).card := Finset.card_le_card_of_injOn (fun i => (e i : ℕ) / 3)
          (fun i _ => by
            have := (e i).isLt
            simp only [Finset.coe_range, Set.mem_Iio]
            omega)
          (fun i hi j hj hij => by
            simp only [Finset.coe_filter, Finset.mem_univ, true_and,
              Set.mem_ofPred_eq] at hi hj
            apply e.injective
            have hi' := congrArg Fin.val hi
            have hj' := congrArg Fin.val hj
            simp only [g] at hi' hj' hij
            ext
            omega)
      _ = t := Finset.card_range t
  let a : P := e.symm ⟨0, by omega⟩
  let c : P := e.symm ⟨1, by omega⟩
  have ha : g a = 0 := by simp only [a, g, Equiv.apply_symm_apply]; rfl
  have hc : g c = 2 := by simp only [c, g, Equiv.apply_symm_apply]; rfl
  let πs := π.toSyncProtocol v₀ v₁
  let cross : P → P → Bool := fun i j => decide ((g i = 0 ∧ g j = 2) ∨ (g i = 2 ∧ g j = 0))
  let nbr : P × Bool → P → P × Bool := fun p j => (j, p.2 ^^ cross p.1 j)
  let cover := πs.coverState Prod.fst Prod.snd nbr
  let adv : (P → Bool) → ℕ → P → P → Option M := fun σ r j i =>
    πs.send r j (cover r (nbr (i, σ i) j)) i
  let Fk : Fin 3 → Finset P := fun k => Finset.univ.filter fun i => g i = k
  have hnotMem : ∀ (k : Fin 3) (i : P), i ∉ Fk k ↔ g i ≠ k := fun k i => by
    simp only [Fk, Finset.mem_filter, Finset.mem_univ, true_and]
  have hgst0 : ∀ k : Fin 3, IsGST (fun _ _ _ => true) (Fk k) 0 := fun _ _ _ _ _ _ _ => rfl
  have key : ∀ (k : Fin 3) (σ : P → Bool),
      (∀ i j, g i ≠ k → g j ≠ k → (σ i ^^ cross i j) = σ j) →
      ∀ r i, g i ≠ k →
        π.byzantineDecision (Fk k) (fun _ _ _ => true) (adv σ)
          (fun j => if σ j then v₁ else v₀) r i = π.output i (cover r (i, σ i)) := by
    intro k σ hσ r i hi
    simp only [PartialSyncProtocol.byzantineDecision,
      π.byzantineState_always_eq_state v₀ v₁ (Fk k) (adv σ) σ r i]
    rw [Cslib.Distributed.Byzantine.Protocol.state_eq_coverState πs Prod.fst Prod.snd nbr
      (Fk k) (adv σ) σ (fun i => (i, σ i)) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun i hi' j hj' => by
        simp only [nbr, Prod.mk.injEq, true_and]
        exact hσ i j ((hnotMem k i).1 hi') ((hnotMem k j).1 hj'))
      (fun _ _ _ _ _ => rfl) r i ((hnotMem k i).2 hi)]
  have hc₀ : g c ≠ 0 := by rw [hc]; decide
  have ha₂ : g a ≠ 2 := by rw [ha]; decide
  have ha₁ : g a ≠ 1 := by rw [ha]; decide
  have hc₁ : g c ≠ 1 := by rw [hc]; decide
  -- Unanimous run helper when `k ∈ {0, 2}` is faulty and all inputs equal `bit`.
  have hrun : ∀ (k : Fin 3) (bit : Bool) (p : P), (k = 0 ∨ k = 2) → g p ≠ k →
      ∃ R, π.output p (cover R (p, bit)) = some (if bit then v₁ else v₀) := by
    intro k bit p hk hp
    obtain ⟨R, hR⟩ := h.termination (Fk k) (hcard k) (fun _ _ _ => true) 0 (adv fun _ => bit)
      (fun _ => if bit then v₁ else v₀) (hgst0 k) p ((hnotMem k p).2 hp)
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hR
    have hw_eq := h.validity (Fk k) (hcard k) (fun _ _ _ => true) (adv fun _ => bit)
      (fun _ => if bit then v₁ else v₀) (if bit then v₁ else v₀) (fun _ _ => rfl)
      R p ((hnotMem k p).2 hp) w hw
    rw [hw_eq] at hw
    refine ⟨R, ?_⟩
    rw [← key k (fun _ => bit) (fun i j hi hj => by
      rcases hk with rfl | rfl <;>
        simp only [cross, hi, hj, false_and, and_false, or_self, decide_false, Bool.xor_false])
      R p hp]
    exact hw
  obtain ⟨R₀, hcov₀⟩ := hrun 0 false c (Or.inl rfl) hc₀
  obtain ⟨R₂, hcov₂⟩ := hrun 2 true a (Or.inr rfl) ha₂
  -- Run 1 (`G₁` faulty, `G₀` placed in copy `true` and `G₂` in copy `false`): `a` decides `v₁` at
  -- `R₂` and `c` decides `v₀` at `R₀`, violating unconditional agreement.
  have hfin : ∀ u v : Fin 3, u ≠ 1 → v ≠ 1 →
      (decide (u = 0) ^^ decide ((u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 0))) = decide (v = 0) := by
    decide
  let σ₁ : P → Bool := fun i => decide (g i = 0)
  have hdec_a : π.byzantineDecision (Fk 1) (fun _ _ _ => true) (adv σ₁)
      (fun j => if σ₁ j then v₁ else v₀) R₂ a = some v₁ := by
    simpa only [key 1 σ₁ (fun _ _ => hfin _ _) R₂ a ha₁, σ₁, ha, decide_true, ↓reduceIte] using
      hcov₂
  have hdec_c : π.byzantineDecision (Fk 1) (fun _ _ _ => true) (adv σ₁)
      (fun j => if σ₁ j then v₁ else v₀) R₀ c = some v₀ := by
    simpa only [key 1 σ₁ (fun _ _ => hfin _ _) R₀ c hc₁, σ₁, hc,
      (by decide : (2 : Fin 3) ≠ 0), decide_false, Bool.false_eq_true, ↓reduceIte] using hcov₀
  have hag := h.agreement (Fk 1) (hcard 1) (fun _ _ _ => true) (adv σ₁)
    (fun j => if σ₁ j then v₁ else v₀) R₂ R₀ a ((hnotMem 1 a).2 ha₁) c ((hnotMem 1 c).2 hc₁)
    v₁ v₀ hdec_a hdec_c
  exact hne hag.symm

/-- Prefix indistinguishability on a closed group `S : P → Prop` for `omissionState`: if `x₁` and
`x₂` agree on `S`, and before round `N` the delivery schedules `d₁` and `d₂` agree on every
recipient `i` in `S` and deliver to `i` only from senders in `S`, then `omissionState` agrees on `S`
for all `r ≤ N`. -/
private theorem omissionState_eq_of_prefix {P V State Msg : Type*}
    (π : PartialSyncProtocol P V State Msg)
    {d₁ d₂ : ℕ → P → P → Bool} {x₁ x₂ : P → V} {S : P → Prop} {N : ℕ}
    (hx : ∀ i, S i → x₁ i = x₂ i)
    (hd : ∀ r < N, ∀ j i, S i → d₁ r j i = d₂ r j i ∧ (d₂ r j i = true → S j)) :
    ∀ r ≤ N, ∀ i, S i → π.omissionState d₁ x₁ r i = π.omissionState d₂ x₂ r i
  | 0, _, i, hi => by simp only [PartialSyncProtocol.omissionState, hx i hi]
  | r + 1, hr, i, hi => by
    have hr_lt : r < N := by omega
    simp only [PartialSyncProtocol.omissionState]
    congr 1
    · exact omissionState_eq_of_prefix π hx hd r (by omega) i hi
    · funext j
      obtain ⟨hdeq, hclosed⟩ := hd r hr_lt j i hi
      rw [hdeq]
      cases hd₂ : d₂ r j i
      · simp only [Bool.false_eq_true, ↓reduceIte]
      · simp only [↓reduceIte,
          omissionState_eq_of_prefix π hx hd r (by omega) j (hclosed hd₂)]

/-- **Weak-unanimity crash/omission lower bound (`not_omissionPartialSync_weakUnanimity`,
[Dwork, Lynch and Stockmeyer, Theorem 4.3, pp. 305–306][DworkLynchStockmeyer1988]):** in the §3.1
basic round model, when `2 ≤ Fintype.card P ≤ 2 * t` and `V` has at least two values, no
deterministic protocol achieves post-`GST` termination against `≤ t` omission faults together with
failure-free (`F = ∅`, `∃ gst, IsGST deliver ∅ gst`) agreement and weak unanimity.

Matches the partition-and-healing proof of Theorem 4.3: partitioning `P` into `A` and `Aᶜ` of size
`≤ t` forces `a ∈ A` to decide at some round `R₀` on all-`v₀` inputs (which must equal `v₀` by
healing the partition after `R₀` so `IsGST _ ∅ R₀` holds and invoking weak unanimity) and `b ∉ A` to
decide `v₁` at some round `R₁` on all-`v₁` inputs (healing after `R₁`), contradicting failure-free
agreement on the mixed-input schedule that heals at `max R₀ R₁`. -/
theorem not_omissionPartialSync_weakUnanimity {P V S M : Type*}
    [Fintype P] [Nontrivial V]
    (π : PartialSyncProtocol P V S M) {t : ℕ}
    (h2 : 2 ≤ Fintype.card P) (h2t : Fintype.card P ≤ 2 * t)
    (hag : ∀ deliver x r₁ r₂ i j v₁ v₂, (∃ gst, IsGST deliver ∅ gst) →
      π.omissionDecision deliver x r₁ i = some v₁ →
      π.omissionDecision deliver x r₂ j = some v₂ → v₁ = v₂)
    (hwu : ∀ deliver x v, (∃ gst, IsGST deliver ∅ gst) → (∀ i, x i = v) →
      ∀ r i w, π.omissionDecision deliver x r i = some w → w = v)
    (hterm : ∀ F : Finset P, F.card ≤ t → ∀ deliver gst x,
      IsGST deliver F gst → ∀ i ∉ F, ∃ r, (π.omissionDecision deliver x r i).isSome = true) :
    False := by
  classical
  obtain ⟨v₀, v₁, hne⟩ := exists_pair_ne V
  let n := Fintype.card P
  let k := n / 2
  let e := Fintype.equivFin P
  let A : Finset P := Finset.univ.filter fun i => (e i : ℕ) < k
  let B : Finset P := Finset.univ \ A
  have hA_card : A.card = k := by
    rw [← Finset.card_range k]
    refine Finset.card_bij (fun i _ => (e i : ℕ)) (fun i hi => ?_)
      (fun _ _ _ _ h => e.injective (Fin.ext h)) (fun m hm => ?_)
    · simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] using hi
    · rw [Finset.mem_range] at hm
      exact ⟨e.symm ⟨m, by omega⟩, by
        simp only [A, Finset.mem_filter, Finset.mem_univ, Equiv.apply_symm_apply, hm, and_self],
        congrArg Fin.val (e.apply_symm_apply _)⟩
  have hB_card : B.card = n - k := by
    simpa [B, hA_card, n] using Finset.card_sdiff_of_subset (Finset.subset_univ A)
  let a : P := e.symm ⟨0, by omega⟩
  let b : P := e.symm ⟨n - 1, by omega⟩
  have haA : a ∈ A := by simp [a, A]; omega
  have hbA : b ∉ A := by simp [b, A]; omega
  have haB : a ∉ B := fun h => (Finset.mem_sdiff.1 h).2 haA
  -- Partitioned schedule: deliver within `A` and within `Aᶜ`, drop across `A ↔ Aᶜ`.
  let partDeliver : ℕ → P → P → Bool := fun _ j i => decide (j ∈ A ↔ i ∈ A)
  let healAt (T : ℕ) : ℕ → P → P → Bool := fun r j i => if r < T then partDeliver r j i else true
  have hgst_heal : ∀ T, IsGST (healAt T) ∅ T := fun T r hr _ _ _ _ => by
    simp only [healAt, Nat.not_lt.mpr hr, ↓reduceIte]
  have hgstB : IsGST partDeliver B 0 := fun _ _ j hj i hi => by
    simp only [B, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hj hi
    simp only [partDeliver, hj, hi, decide_true]
  have hgstA : IsGST partDeliver A 0 := fun _ _ j hj i hi => by
    simp only [partDeliver, hj, hi, decide_true]
  -- Healing a partitioned unanimous run at its decision round does not change the decision.
  have hheal : ∀ (v : V) R p, π.omissionDecision (healAt R) (fun _ => v) R p =
      π.omissionDecision partDeliver (fun _ => v) R p := fun v R p =>
    congrArg (π.output p) (omissionState_eq_of_prefix π (d₁ := healAt R) (d₂ := partDeliver)
      (x₁ := fun _ => v) (x₂ := fun _ => v) (S := fun _ => True) (fun _ _ => rfl)
      (fun r hr _ _ _ => ⟨by simp only [healAt, hr, ↓reduceIte], fun _ => trivial⟩) R le_rfl p
      trivial)
  -- Scenario A (`B` faulty, all inputs `v₀`): `a ∈ A` decides at `R₀`; healing at `R₀` yields `v₀`.
  obtain ⟨R₀, hR₀⟩ := hterm B (by omega) partDeliver 0 (fun _ => v₀) hgstB a haB
  obtain ⟨w₀, hw₀⟩ := Option.isSome_iff_exists.1 hR₀
  rw [hwu (healAt R₀) (fun _ => v₀) v₀ ⟨R₀, hgst_heal R₀⟩ (fun _ => rfl) R₀ a w₀
    ((hheal v₀ R₀ a).trans hw₀)] at hw₀
  -- Scenario B (`A` faulty, all inputs `v₁`): `b ∉ A` decides at `R₁`; healing at `R₁` yields `v₁`.
  obtain ⟨R₁, hR₁⟩ := hterm A (by omega) partDeliver 0 (fun _ => v₁) hgstA b hbA
  obtain ⟨w₁, hw₁⟩ := Option.isSome_iff_exists.1 hR₁
  rw [hwu (healAt R₁) (fun _ => v₁) v₁ ⟨R₁, hgst_heal R₁⟩ (fun _ => rfl) R₁ b w₁
    ((hheal v₁ R₁ b).trans hw₁)] at hw₁
  -- Scenario C (`F = ∅`, mixed inputs `xMix`, healing at `G = max R₀ R₁`).
  let G := max R₀ R₁
  let xMix : P → V := fun i => if i ∈ A then v₀ else v₁
  have hdec_a : π.omissionDecision (healAt G) xMix R₀ a = some v₀ :=
    (congrArg (π.output a) (omissionState_eq_of_prefix π (d₁ := healAt G) (d₂ := partDeliver)
      (x₁ := xMix) (x₂ := fun _ => v₀) (S := fun i => i ∈ A)
      (fun i hi => by simp only [xMix, hi, ↓reduceIte])
      (fun r hr j i hi => ⟨by simp only [healAt, G, hr, ↓reduceIte], fun hp => by
        simpa only [partDeliver, hi, iff_true, decide_eq_true_eq] using hp⟩)
      R₀ (le_max_left R₀ R₁) a haA)).trans hw₀
  have hdec_b : π.omissionDecision (healAt G) xMix R₁ b = some v₁ :=
    (congrArg (π.output b) (omissionState_eq_of_prefix π (d₁ := healAt G) (d₂ := partDeliver)
      (x₁ := xMix) (x₂ := fun _ => v₁) (S := fun i => i ∉ A)
      (fun i hi => by simp only [xMix, hi, ↓reduceIte])
      (fun r hr j i hi => ⟨by simp only [healAt, G, hr, ↓reduceIte], fun hp => by
        simpa only [partDeliver, hi, iff_false, decide_eq_true_eq] using hp⟩)
      R₁ (le_max_right R₀ R₁) b hbA)).trans hw₁
  exact hne (hag (healAt G) xMix R₀ R₁ a b v₀ v₁ ⟨G, hgst_heal G⟩ hdec_a hdec_b)

/-- **Crash/omission lower bound (`not_solvesOmissionPartialSync`,
[Dwork, Lynch and Stockmeyer, Theorem 4.3, pp. 305–306][DworkLynchStockmeyer1988]):** when
`2 ≤ Fintype.card P ≤ 2 * t` and `V` has at least two values, no deterministic protocol solves
`SolvesOmissionPartialSync t` (immediate from `not_omissionPartialSync_weakUnanimity`). -/
theorem not_solvesOmissionPartialSync {P V S M : Type*}
    [Fintype P] [Nontrivial V]
    (π : PartialSyncProtocol P V S M) {t : ℕ}
    (h2 : 2 ≤ Fintype.card P) (h2t : Fintype.card P ≤ 2 * t) :
    ¬ π.SolvesOmissionPartialSync t := fun h =>
  not_omissionPartialSync_weakUnanimity π h2 h2t
    (fun deliver x r₁ r₂ i j v₁ v₂ _ => h.agreement ∅ (Nat.zero_le t) deliver x r₁ r₂
      i (Finset.notMem_empty i) j (Finset.notMem_empty j) v₁ v₂)
    (fun deliver x v _ => h.validity deliver x v)
    h.termination

/-! ### Sharp resiliency characterizations -/

/-- **Sharp characterization of unauthenticated Byzantine consensus under partial synchrony
(`exists_solvesByzantinePartialSync_iff`,
[Dwork, Lynch and Stockmeyer, Table I, p. 291][DworkLynchStockmeyer1988]):** over any nontrivial
value domain `[Nontrivial V]`, deterministic consensus tolerating `t` unauthenticated Byzantine
faults under partial synchrony is solvable if and only if
`Fintype.card P ≤ 1 ∨ 3 * t < Fintype.card P`. -/
theorem exists_solvesByzantinePartialSync_iff.{u, v} (P : Type u) (V : Type v)
    [Fintype P] [DecidableEq P] [Nontrivial V] (t : ℕ) :
    (∃ (S M : Type v) (π : PartialSyncProtocol P V S M), π.SolvesByzantinePartialSync t) ↔
      Fintype.card P ≤ 1 ∨ 3 * t < Fintype.card P := by
  classical
  refine ⟨fun ⟨_, _, π, hsol⟩ => or_iff_not_imp_left.2 fun h1 =>
    not_le.1 fun h3 => not_solvesByzantinePartialSync π (by omega) h3 hsol, ?_⟩
  rintro (h1 | h3t)
  · have : Subsingleton P := Fintype.card_le_one_iff_subsingleton.1 h1
    exact ⟨V, PUnit.{v + 1}, ownInputProtocol P V, solvesByzantinePartialSync_ownInput t⟩
  · let e := Fintype.equivFin P
    exact ⟨ByzViewState V, ByzViewMsg V,
      byzQuorumProtocol P V (List.ofFn e.symm)
        (rotatingCoordinator (List.ofFn e.symm) (e.symm ⟨0, by omega⟩)) t,
      solvesByzantinePartialSync_byzQuorumProtocol
        (fun p => List.mem_ofFn.2 ⟨e p, e.symm_apply_apply p⟩) _ h3t⟩

/-- **Sharp characterization of crash/omission consensus under partial synchrony
(`exists_solvesOmissionPartialSync_iff`,
[Dwork, Lynch and Stockmeyer, Table I, p. 291][DworkLynchStockmeyer1988]):** over any nontrivial
value domain `[Nontrivial V]`, deterministic consensus tolerating `t` crash/omission faults under
partial synchrony is solvable if and only if `Fintype.card P ≤ 1 ∨ 2 * t < Fintype.card P`. -/
theorem exists_solvesOmissionPartialSync_iff.{u, v} (P : Type u) (V : Type v)
    [Fintype P] [Nontrivial V] (t : ℕ) :
    (∃ (S M : Type v) (π : PartialSyncProtocol P V S M), π.SolvesOmissionPartialSync t) ↔
      Fintype.card P ≤ 1 ∨ 2 * t < Fintype.card P := by
  classical
  refine ⟨fun ⟨_, _, π, hsol⟩ => or_iff_not_imp_left.2 fun h1 =>
    not_le.1 fun h2 => not_solvesOmissionPartialSync π (by omega) h2 hsol, ?_⟩
  rintro (h1 | h2t)
  · have : Subsingleton P := Fintype.card_le_one_iff_subsingleton.1 h1
    exact ⟨V, PUnit.{v + 1}, ownInputProtocol P V,
      (solvesByzantinePartialSync_ownInput t).toOmission⟩
  · let e := Fintype.equivFin P
    exact ⟨OmissionViewState V, OmissionViewMsg V,
      omissionQuorumProtocol P V (List.ofFn e.symm)
        (rotatingCoordinator (List.ofFn e.symm) (e.symm ⟨0, by omega⟩)) t,
      solvesOmissionPartialSync_omissionQuorumProtocol
        (fun p => List.mem_ofFn.2 ⟨e p, e.symm_apply_apply p⟩) _ h2t⟩

end Cslib.Distributed.PartialSynchrony
