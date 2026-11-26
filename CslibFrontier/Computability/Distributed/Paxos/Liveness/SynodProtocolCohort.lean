/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.Paxos.Liveness.SynodProtocol
import CslibFrontier.Computability.Distributed.Paxos.Liveness.SynodProtocolSim
import CslibFrontier.Computability.Distributed.Paxos.Liveness.SynodProtocolDelivery
import Mathlib.Data.Finset.Sort

/-!
# Safety and supported-cohort progress for `synodQuorumProtocol`

Proves `synodQuorumProtocol_safeCohort_crashStop`, showing that `synodQuorumProtocol qs` satisfies
both `SafeConsensus` and cohort progress `CanDecideIn Q` whenever `qs.Supports Q`.

## Main results

* `Cslib.Distributed.Paxos.synodQuorumProtocol_safeCohort_crashStop`: crash-stop step showing
  `synodQuorumProtocol qs` achieves `SafeConsensus` and `CanDecideIn Q` whenever `qs.Supports Q`.
-/

public section

namespace Cslib.Distributed.Paxos

open Cslib

/-- Crash-stop step for co-located `synodQuorumProtocol` (a crash-stop step towards [Lamport1998]
§2 and [Lamport2001] §2, not the crash-recovery cited protocol): for every quorum system
`qs : QuorumSystem P` over a finite, linearly ordered process set `P` (in particular
`majorityQuorums hmaj` whenever `2 * t < Fintype.card P`), `synodQuorumProtocol qs` satisfies both
`SafeConsensus` and cohort progress `CanDecideIn Q` whenever `Q` contains a prepare quorum
and an accept quorum (`qs.Supports Q`). These may differ and neither phase needs pairwise
intersection. An accept quorum alone is not assumed to be sufficient for a new prepare. -/
theorem synodQuorumProtocol_safeCohort_crashStop {P V : Type*} [Fintype P] [LinearOrder P]
    [DecidableEq V] (qs : QuorumSystem P) :
    (synodQuorumProtocol (V := V) qs).SafeConsensus ∧
      ∀ Q, qs.Supports Q → (synodQuorumProtocol (V := V) qs).CanDecideIn Q := by
  let π := synodQuorumProtocol (V := V) qs
  refine ⟨?_, ?_⟩
  · intro inp s hreach
    obtain ⟨hr, hout⟩ := netToSynod_reach qs hreach
    refine ⟨fun p₁ p₂ v₁ v₂ h₁ h₂ => ?_,
      fun p v hpv => paxos_validity_crashStop qs hr (hout p ▸ hpv)⟩
    obtain ⟨b₁, hl₁⟩ := hr.learned_eq_some_iff.mp (hout p₁ ▸ h₁)
    obtain ⟨b₂, hl₂⟩ := hr.learned_eq_some_iff.mp (hout p₂ ▸ h₂)
    exact paxos_agreement_crashStop qs hr hl₁ hl₂
  · intro Q₀ hQ₀ v
    obtain ⟨p₀, hp₀Q⟩ := hQ₀.nonempty
    obtain ⟨⟨Q₁, hQ₁, hQ₁_sub⟩, ⟨Q₂, hQ₂, hQ₂_sub⟩⟩ := hQ₀
    let b : Ballot P := ⟨0, p₀⟩
    let qList := Q₀.toList
    let s₀ := π.start fun _ => v
    let act₀ : NetAction P ℕ (Msg P P V) := .localStep p₀ 0
    let s₁ := AsyncQuorumProtocol.applyResult p₀ (π.onLocal p₀ 0 (s₀.proc p₀)) s₀
    have htr₀ : π.lts.Tr s₀ act₀ s₁ := ⟨⟨rfl, trivial⟩, rfl⟩
    let propOf (S : Finset P) : ProposerState P P V :=
      { input := v
        round := some 0
        proposed := decide (∃ Q ∈ qs.prepareQuorums, Q ⊆ S)
        promised := S
        maxVote := none
        crashed := false }
    have hempty_no_q : decide (∃ Q ∈ qs.prepareQuorums, Q ⊆ (∅ : Finset P)) = false :=
      decide_eq_false fun ⟨Q, hQ, hsub⟩ =>
        let ⟨x, hx⟩ := qs.prepareQuorum_nonempty hQ
        Finset.notMem_empty x (hsub hx)
    have hs₁_prop : (s₁.proc p₀).state.prop = propOf ∅ := by
      dsimp only [s₁, AsyncQuorumProtocol.applyResult, π, synodQuorumProtocol, s₀,
        AsyncQuorumProtocol.start, propOf]
      rw [hempty_no_q, ite_eq_left rfl]
    have hs₁_learn : (s₁.proc p₀).state.learn.crashed = false := by
      dsimp only [s₁, AsyncQuorumProtocol.applyResult, π, synodQuorumProtocol, s₀,
        AsyncQuorumProtocol.start]
      simp only [↓reduceIte]
    have hs₁_as : ∀ x ∈ qList, (⟨p₀, x, Msg.phase1a b⟩ : Packet P (Msg P P V)) ∈ s₁.msgs ∧
        (s₁.proc x).state.acc = { maxBal := none, maxVoted := none, crashed := false } := by
      intro x _
      refine ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(x, Msg.phase1a b),
        Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩, rfl⟩), ?_⟩
      dsimp only [s₁, AsyncQuorumProtocol.applyResult, π, synodQuorumProtocol, s₀,
        AsyncQuorumProtocol.start]
      by_cases hxp : x = p₀ <;> simp only [hxp, ↓reduceIte]
    -- Phase 1a fanout across `qList`:
    obtain ⟨hmtr_1a, hs₂_pl, _, hs₂_in⟩ :=
      deliver_fanout_acc qs p₀ (.phase1a b)
        { maxBal := none, maxVoted := none, crashed := false }
        { maxBal := some b, maxVoted := none, crashed := false }
        (fun a => .phase1b a b none)
        (fun a st hacc => by
          refine ⟨{(b.proposer, .phase1b a b none)}, ?_, Finset.mem_singleton_self _⟩
          dsimp only [synodQuorumProtocol]
          rw [hacc]
          rfl)
        Q₀.nodup_toList hs₁_as
    set s₂ := qList.foldl (fun w a => π.deliverStep w ⟨p₀, a, .phase1a b⟩) s₁
    -- Phase 1b fan-in to `p₀` across `qList`:
    obtain ⟨hmtr_1b, S₃, _, hs₃_mem, hs₃_al, _, hs₃_2a_imp⟩ :=
      deliver_fanin_leader qs p₀ (fun a => .phase1b a b none)
        (fun S u =>
          (∀ x : P, (u.proc x).state.acc = (s₂.proc x).state.acc ∧
            (u.proc x).state.learn = (s₂.proc x).state.learn) ∧
          (u.proc p₀).state.prop = propOf S ∧
          (decide (∃ Q ∈ qs.prepareQuorums, Q ⊆ S) = true →
            ∀ x : P, (⟨p₀, x, Msg.phase2a b v⟩ : Packet P (Msg P P V)) ∈ u.msgs))
        (fun u S a ⟨hal, hpS, h2a⟩ => by
          dsimp only [AsyncQuorumProtocol.deliverStep, AsyncQuorumProtocol.applyResult, π,
            synodQuorumProtocol]
          have hg : (u.proc p₀).state.prop.crashed = false ∧ a = a := ⟨by rw [hpS], rfl⟩
          rw [ite_eq_left hg, hpS]
          dsimp only [propOf, mergeVote]
          have hal' (np : NodeProcState (SynodNodeState P V) V)
              (ha : np.state.acc = (u.proc p₀).state.acc)
              (hl : np.state.learn = (u.proc p₀).state.learn) (x : P) :
              (if x = p₀ then np else u.proc x).state.acc = (s₂.proc x).state.acc ∧
              (if x = p₀ then np else u.proc x).state.learn = (s₂.proc x).state.learn := by
            split_ifs <;> simp only [*, and_self]
          by_cases haS : a ∈ S
          · rw [ite_eq_right (fun h : b = ⟨0, p₀⟩ ∧ a ∉ S => h.2 haS), Finset.insert_eq_of_mem haS]
            exact ⟨hal' _ rfl rfl,
              by rw [ite_eq_left rfl]; exact hpS,
              fun hq x => Finset.mem_union_left _ (h2a hq x)⟩
          · rw [ite_eq_left (⟨rfl, haS⟩ : b = ⟨0, p₀⟩ ∧ a ∉ S)]
            by_cases hqS : ∃ Q ∈ qs.prepareQuorums, Q ⊆ S
            · have hq_ins : ∃ Q ∈ qs.prepareQuorums, Q ⊆ insert a S :=
                hqS.imp fun Q ⟨hQ, hsub⟩ => ⟨hQ, hsub.trans (Finset.subset_insert a S)⟩
              simp only [decide_eq_true hqS, decide_eq_true hq_ins, Bool.not_true,
                Bool.false_and, Bool.false_eq_true, ↓reduceIte]
              exact ⟨hal' _ rfl rfl, trivial,
                fun _ x => Finset.mem_union_left _ (h2a (decide_eq_true hqS) x)⟩
            · by_cases hq_ins : ∃ Q ∈ qs.prepareQuorums, Q ⊆ insert a S
              · simp only [decide_eq_false hqS, decide_eq_true hq_ins, Bool.not_false,
                  Bool.true_and, ↓reduceIte]
                exact ⟨hal' _ rfl rfl, trivial,
                  fun _ x => Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(x, .phase2a b v),
                    Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩, rfl⟩)⟩
              · simp only [decide_eq_false hqS, decide_eq_false hq_ins, Bool.not_false,
                  Bool.true_and, Bool.false_eq_true, ↓reduceIte]
                exact ⟨hal' _ rfl rfl, trivial, nofun⟩)
        (as := qList) (u := s₂) (S₀ := ∅)
        (fun x hx => (hs₂_in x hx).2)
        ⟨fun _ => ⟨rfl, rfl⟩, (hs₂_pl p₀).1.trans hs₁_prop, by rw [hempty_no_q]; exact nofun⟩
    set s₃ := qList.foldl (fun w a => π.deliverStep w ⟨a, p₀, .phase1b a b none⟩) s₂
    have hs₃_2a_msgs : ∀ x : P, (⟨p₀, x, Msg.phase2a b v⟩ : Packet P (Msg P P V)) ∈ s₃.msgs :=
      hs₃_2a_imp (decide_eq_true
        ⟨Q₁, hQ₁, fun a haQ => hs₃_mem a (Finset.mem_toList.mpr (hQ₁_sub haQ))⟩)
    -- Phase 2a fanout across `qList`:
    have hal_b : allowsVote (some b) b = true := by
      simp only [allowsVote, decide_eq_true_eq, le_refl]
    obtain ⟨hmtr_2a, hs₄_pl, _, hs₄_in⟩ :=
      deliver_fanout_acc qs p₀ (.phase2a b v)
        { maxBal := some b, maxVoted := none, crashed := false }
        { maxBal := some b, maxVoted := some ⟨b, v⟩, crashed := false }
        (fun a => .phase2b a b v)
        (fun a st hacc => by
          refine ⟨Finset.univ.image fun q => (q, .phase2b a b v), ?_,
            Finset.mem_image.mpr ⟨p₀, Finset.mem_univ p₀, rfl⟩⟩
          dsimp only [synodQuorumProtocol]
          rw [hacc, ite_eq_left ⟨rfl, hal_b⟩])
        Q₀.nodup_toList
        (fun x hx => ⟨hs₃_2a_msgs x, (hs₃_al x).1.trans (hs₂_in x hx).1⟩)
    set s₄ := qList.foldl (fun w a => π.deliverStep w ⟨p₀, a, .phase2a b v⟩) s₃
    have hs₄_learn : (s₄.proc p₀).state.learn.crashed = false := by
      rwa [(hs₄_pl p₀).2, (hs₃_al p₀).2, (hs₂_pl p₀).2]
    -- Phase 2b fan-in to `p₀` across `qList`:
    obtain ⟨hmtr_2b, S₅, _, hs₅_mem, _, hs₅_recv_S⟩ :=
      deliver_fanin_leader qs p₀ (fun a => .phase2b a b v)
        (fun S u => (u.proc p₀).state.learn.crashed = false ∧
          ∀ a ∈ S, ⟨a, b, v⟩ ∈ (u.proc p₀).state.learn.received)
        (fun u S a ⟨hl, hrec⟩ => by
          dsimp only [AsyncQuorumProtocol.deliverStep, AsyncQuorumProtocol.applyResult, π,
            synodQuorumProtocol]
          rw [ite_eq_left (⟨hl, rfl⟩ : (u.proc p₀).state.learn.crashed = false ∧ a = a)]
          simp only [↓reduceIte, hl, true_and, Finset.mem_insert, forall_eq_or_imp, true_or]
          exact fun x hxS => .inr (hrec x hxS))
        (as := qList) (u := s₄) (S₀ := ∅)
        (fun x hx => (hs₄_in x hx).2)
        ⟨hs₄_learn, fun _ hm => False.elim (Finset.notMem_empty _ hm)⟩
    set s₅ := qList.foldl (fun w a => π.deliverStep w ⟨a, p₀, .phase2b a b v⟩) s₄
    have hs₅_recv : ∀ a ∈ qList, ⟨a, b, v⟩ ∈ (s₅.proc p₀).state.learn.received :=
      fun a ha => hs₅_recv_S a (hs₅_mem a ha)
    let xl : List (NetAction P ℕ (Msg P P V)) :=
      [act₀] ++
        (qList.map fun a => NetAction.deliver (L := ℕ) ⟨p₀, a, Msg.phase1a b⟩) ++
        (qList.map fun a => NetAction.deliver (L := ℕ) ⟨a, p₀, Msg.phase1b a b none⟩) ++
        (qList.map fun a => NetAction.deliver (L := ℕ) ⟨p₀, a, Msg.phase2a b v⟩) ++
        (qList.map fun a => NetAction.deliver (L := ℕ) ⟨a, p₀, Msg.phase2b a b v⟩)
    have hmtr_all : π.lts.MTr s₀ xl s₅ :=
      ((((LTS.MTr.single _ htr₀).comp _ hmtr_1a).comp _ hmtr_1b).comp _ hmtr_2a).comp _ hmtr_2b
    have hgroup : ∀ act ∈ xl, act.InGroup Q₀ := by
      intro act hact
      simp only [xl, qList, List.mem_append, List.mem_singleton, List.mem_map,
        Finset.mem_toList] at hact
      rcases hact with (((rfl | ⟨a, haQ, rfl⟩) | ⟨a, haQ, rfl⟩) | ⟨a, haQ, rfl⟩) | ⟨a, haQ, rfl⟩
      exacts [hp₀Q, ⟨hp₀Q, haQ⟩, ⟨haQ, hp₀Q⟩, ⟨hp₀Q, haQ⟩, ⟨haQ, hp₀Q⟩]
    obtain ⟨hr₅, hout₅⟩ := netToSynod_reach qs ⟨xl, hmtr_all⟩
    have hlearnedAt₅ : (netToSynod s₅).LearnedAt qs p₀ b v :=
      ⟨Q₂, hQ₂, fun a haQ => hs₅_recv a (Finset.mem_toList.mpr (hQ₂_sub haQ))⟩
    exact ⟨xl, s₅, hgroup, hmtr_all, p₀, hp₀Q, v,
      (hout₅ p₀).trans (hr₅.learned_eq_some_iff.mpr ⟨b, hlearnedAt₅⟩)⟩

end Cslib.Distributed.Paxos
