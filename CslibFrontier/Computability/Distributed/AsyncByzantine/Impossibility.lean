/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.AsyncByzantine.Basic
import CslibFrontier.Tactic.FinsetCard
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# The `3t + 1` impossibility bound for asynchronous Byzantine reliable broadcast

No deterministic asynchronous protocol on `n` processes with `3 ≤ n ≤ 3t` solves reliable broadcast
over a **nonempty** value domain `V` (even a singleton such as `Unit`) against `t` static Byzantine
faults. For the weaker notion of *consistent* broadcast (`validity` + `consistency`, without
`totality` or `noSpurious`), the same bound holds over any **nontrivial** value domain `V`
([BrachaToueg1985]; [Bracha1987]). Unlike the synchronous bound of
`CslibFrontier.Computability.Distributed.Byzantine.NodeBound`, these bounds need **no** fixed
round count and no finiteness assumptions on the state or message types.

Notice the threshold at `n = 2` differs from Byzantine *agreement*: with `n = 2` processes, if the
broadcaster `dealer` is faulty then only a single correct process remains, so consistency and
totality hold vacuously (`solvesReliableBroadcast_direct_of_card_le_two`).

## Two replay proofs

Partition the process set `P` into three pairwise disjoint subsets `A, B, C` of cardinality at most
`t` each, with `dealer ∈ A`, `b₀ ∈ B`, and `c₀ ∈ C`.

* **Consistent broadcast (`[Nontrivial V]`, `not_consistentBroadcast_of_partition`):** fix
  `v₀ ≠ v₁`. Run 1 (`C` silent faulty, `input = some v₀`) drives `b₀ ∈ B` to decide `v₀`; Run 2
  (`B` silent faulty, `input = some v₁`) drives `c₀ ∈ C` to decide `v₁`. Under `F = A`, replay
  `B`'s steps of Run 1 followed by `C`'s steps of Run 2 (`replay_subset_mTr`), yielding a reachable
  state where `b₀` decides `v₀` and `c₀` decides `v₁`, contradicting `consistency`.
* **Full reliable broadcast (`[Nonempty V]`, `not_reliableBroadcast_of_partition`):** fix any
  `v₀ : V`. As above, replay `B`'s prefix of Run 1 (`C` silent faulty, `input = some v₀`) under
  `F = A`, reaching `u₁` where `b₀` decides `v₀` while `C` stays at its initial state. Extend `u₁`
  with a fair Byzantine-free suffix (`Reachable.exists_admissibleRun`); by `totality`, `c₀ ∈ C`
  eventually decides `v₀`. Replay `C`'s steps of that honest suffix under `F = B` (`input = none`,
  with `dealer ∈ A` honest and silent), driving `c₀` to decide `v₀` and contradicting `noSpurious`.

## Main results

* `Cslib.Distributed.AsyncByzantine.Protocol.replay_subset_mTr`: projecting a Byzantine-free
  execution onto a correct group `H`, replacing incoming `A → H` envelopes by Byzantine injections.
* `Cslib.Distributed.AsyncByzantine.Protocol.not_consistentBroadcast_of_partition`: split-brain
  impossibility (`validity` + `consistency`) for `v₀ ≠ v₁` given a `3`-partition of sizes `≤ t`.
* `Cslib.Distributed.AsyncByzantine.Protocol.not_reliableBroadcast_of_partition`: spurious-delivery
  impossibility (`validity` + `totality` + `noSpurious`) for any single `v₀ : V`.
* `Cslib.Distributed.AsyncByzantine.Protocol.not_solvesReliableBroadcast`: impossibility for every
  `3 ≤ Fintype.card P ≤ 3 * t` and nonempty `V` (including `Unit`).
* `Cslib.Distributed.AsyncByzantine.Protocol.not_solvesReliableBroadcast_three`: the `Fin 3`,
  `t = 1` special case.

## References

* [G. Bracha, *Asynchronous Byzantine agreement protocols*][Bracha1987]
* [G. Bracha, S. Toueg, *Asynchronous consensus and broadcast protocols*][BrachaToueg1985]
-/

public section

namespace Cslib.Distributed.AsyncByzantine

namespace Protocol

open Cslib

variable {P S M V : Type*} {dealer : P} [Fintype P] [DecidableEq P] [DecidableEq M]
  (π : Protocol P S M V dealer)

omit [Fintype P] in
private lemma count_map_tagSender_eq_zero {p : P} {ms : Multiset (P × M)} {e : Envelope P M}
    (hne : e.src ≠ p) : (ms.map (tagSender p)).count e = 0 :=
  Multiset.count_eq_zero_of_notMem fun h => by
    obtain ⟨qm, _, htag⟩ := Multiset.mem_map.mp h
    exact hne (congrArg Envelope.src htag).symm

private lemma start_msgs_count_of_notMem (F : Finset P) (input : Option V)
    {e : Envelope P M} (hnot : e.src ∉ F) :
    (π.start F input).msgs.count e =
      ((π.initSend input e.src).map (tagSender e.src)).count e := by
  simp only [start, Multiset.count_bind, ← Finset.sum_eq_multiset_sum]
  rw [Finset.sum_eq_single e.src (fun p _ hne => ?_) (fun h => absurd (Finset.mem_univ _) h)]
  · simp [hnot]
  · split_ifs <;> simp [count_map_tagSender_eq_zero (Ne.symm hne)]

omit [Fintype P] in
/-- **Group replay lemma.** Given pairwise-relevant subsets `A, H : Finset P` with `Disjoint A H`,
and a Byzantine-free finite execution `(π.lts F_src).MTr s₀ xl s₁` whose active envelopes all
originate in `A ∪ H`, the `H`-destined steps of `xl` can be replayed under `π.lts A` from any
state `u₀` that matches `s₀` on `H`'s local states and has at least `s₀`'s `H → H` message counts.
All non-`H` local states and all non-`H`-sourced message counts remain untouched. -/
theorem replay_subset_mTr {A H F_src : Finset P} (hAH : Disjoint A H)
    {s₀ s₁ : State P S M V} {xl : List (Action P M)}
    (hmtr : (π.lts F_src).MTr s₀ xl s₁)
    (hhon : ∀ a ∈ xl, a.IsHonest)
    (hsrc_init : ∀ e ∈ s₀.msgs, e.src ∈ A ∨ e.src ∈ H)
    (hFsrc : ∀ p, p ∉ F_src → p ∈ A ∨ p ∈ H)
    {u₀ : State P S M V}
    (hproc₀ : ∀ p ∈ H, u₀.proc p = s₀.proc p)
    (hmsg₀ : ∀ e : Envelope P M, e.src ∈ H → e.dest ∈ H → s₀.msgs.count e ≤ u₀.msgs.count e) :
    ∃ yl u₁, (π.lts A).MTr u₀ yl u₁ ∧
      (∀ p ∈ H, u₁.proc p = s₁.proc p) ∧
      (∀ p ∉ H, u₁.proc p = u₀.proc p) ∧
      (∀ e : Envelope P M, e.src ∉ H → u₁.msgs.count e = u₀.msgs.count e) := by
  induction hmtr generalizing u₀ with
  | refl =>
    exact ⟨[], u₀, LTS.MTr.refl, hproc₀, fun _ _ => rfl, fun _ _ => rfl⟩
  | @stepL s a s' xl' s₁ htr hrest ih =>
    have ha_hon : a.IsHonest := hhon a List.mem_cons_self
    have hrest_hon : ∀ b ∈ xl', b.IsHonest := fun b hb => hhon b (List.mem_cons_of_mem a hb)
    cases a with
    | stutter => obtain rfl := htr; exact ih hrest_hon hsrc_init hproc₀ hmsg₀
    | byzRecv => exact False.elim ha_hon
    | deliver e =>
      obtain ⟨he_mem, he_dest_F, rfl⟩ := htr
      have hsrc' : ∀ m ∈ (π.recvHonest e s).msgs, m.src ∈ A ∨ m.src ∈ H := by
        intro m hm
        simp only [recvHonest, recvCore, Multiset.mem_add, Multiset.mem_map] at hm
        rcases hm with hm | ⟨qm, _, rfl⟩
        · exact hsrc_init m (Multiset.mem_of_mem_erase hm)
        · exact hFsrc e.dest he_dest_F
      by_cases hdestH : e.dest ∈ H
      · -- Replay an `H → H` message as `.deliver e` and an `A → H` one as a Byzantine injection.
        have hdestA : e.dest ∉ A := Finset.disjoint_right.mp hAH hdestH
        have hproc_e : u₀.proc e.dest = s.proc e.dest := hproc₀ e.dest hdestH
        obtain ⟨act, base, hstep, hbase_le, hbase_eq⟩ : ∃ act base,
            (π.lts A).Tr u₀ act (π.recvCore e.src e.dest e.body base u₀) ∧
            (∀ m : Envelope P M, m.src ∈ H → m.dest ∈ H →
              (s.msgs.erase e).count m ≤ base.count m) ∧
            ∀ m : Envelope P M, m.src ∉ H → base.count m = u₀.msgs.count m := by
          by_cases hsrcH : e.src ∈ H
          · refine ⟨.deliver e, u₀.msgs.erase e, ⟨Multiset.count_pos.mp ?_, hdestA, rfl⟩,
              fun m hs hd => ?_, fun m hm => ?_⟩
            · exact (Multiset.count_pos.mpr he_mem).trans_le (hmsg₀ e hsrcH hdestH)
            · rcases eq_or_ne m e with rfl | hme
              · simpa only [Multiset.count_erase_self] using
                  Nat.sub_le_sub_right (hmsg₀ m hs hd) 1
              · simpa only [Multiset.count_erase_of_ne hme] using hmsg₀ m hs hd
            · exact Multiset.count_erase_of_ne (show m ≠ e from fun h => hm (h ▸ hsrcH)) _
          · refine ⟨.byzRecv e.src e.dest e.body, u₀.msgs,
              ⟨(hsrc_init e he_mem).resolve_right hsrcH, hdestA, rfl⟩, fun m hs hd => ?_,
              fun _ _ => rfl⟩
            rw [Multiset.count_erase_of_ne (show m ≠ e from fun h => hsrcH (h ▸ hs))]
            exact hmsg₀ m hs hd
        have hproc' : ∀ p ∈ H,
            (π.recvCore e.src e.dest e.body base u₀).proc p = (π.recvHonest e s).proc p :=
          fun p hp => by simp only [recvHonest, recvCore, hproc_e, hproc₀ p hp]
        have hmsg' : ∀ m : Envelope P M, m.src ∈ H → m.dest ∈ H →
            (π.recvHonest e s).msgs.count m ≤
              (π.recvCore e.src e.dest e.body base u₀).msgs.count m :=
          fun m hs hd => by
            simp only [recvHonest, recvCore, Multiset.count_add, hproc_e]
            exact Nat.add_le_add_right (hbase_le m hs hd) _
        obtain ⟨yl, u₁, hyl, hpH, hpOut, hmOut⟩ := ih hrest_hon hsrc' hproc' hmsg'
        refine ⟨act :: yl, u₁, LTS.MTr.stepL hstep hyl, hpH, fun p hp => ?_, fun m hm => ?_⟩
        · rw [hpOut p hp]
          exact ite_eq_right fun h : p = e.dest => hp (h.symm ▸ hdestH)
        · rw [hmOut m hm]
          simp only [recvCore, Multiset.count_add, hbase_eq m hm,
            count_map_tagSender_eq_zero (p := e.dest) (e := m)
              fun h : m.src = e.dest => hm (h.symm ▸ hdestH), add_zero]
      · -- Delivery to `e.dest ∉ H`: skip in the `A`-faulty replay; `H` is untouched.
        exact ih hrest_hon hsrc'
          (fun p hp => by
            simpa only [recvHonest, recvCore, show p ≠ e.dest from fun h => hdestH (h ▸ hp),
              ↓reduceIte] using hproc₀ p hp)
          fun m hs hd => by
            simp only [recvHonest, recvCore, Multiset.count_add,
              count_map_tagSender_eq_zero (p := e.dest) (e := m) fun h => hdestH (h ▸ hs), add_zero]
            exact (Multiset.count_le_of_le m (Multiset.erase_le e s.msgs)).trans (hmsg₀ m hs hd)

omit [Fintype P] [DecidableEq P] [DecidableEq M] in
private lemma extract_isHonest (xs : ωSequence (Action P M)) {k₀ k₁ : ℕ}
    (hhon : ∀ j, k₀ ≤ j → (xs j).IsHonest) :
    ∀ a ∈ xs.extract k₀ k₁, a.IsHonest := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  rw [xs.get_extract (by simpa [ωSequence.length_extract] using hi)]
  exact hhon (k₀ + i) (Nat.le_add_right k₀ i)

private lemma honest_decision_prefix (F : Finset P) (v : V) (p : P)
    (hdec : ∀ ss xs, π.AdmissibleRun F (some v) ss xs → ∃ k, (ss k).ProcDecided p v) :
    ∃ xl s, (π.lts F).MTr (π.start F (some v)) xl s ∧
      (∀ a ∈ xl, a.IsHonest) ∧ s.ProcDecided p v := by
  obtain ⟨ss, xs, ha, hhon⟩ := π.exists_honest_admissibleRun F (some v)
  obtain ⟨k, hk⟩ := hdec ss xs ha
  exact ⟨xs.extract 0 k, ss k, ha.1 ▸ ha.2.1.extract_mTr (Nat.zero_le k),
    extract_isHonest xs fun j _ => hhon j, hk⟩

private lemma replay_from_start {A H F_src : Finset P}
    (hAH : Disjoint A H) (hHF : Disjoint H F_src) (hdH : dealer ∉ H)
    (hcover : ∀ p, p ∉ F_src → p ∈ A ∨ p ∈ H)
    {inp_s inp_u : Option V} {u : State P S M V}
    (hu_proc : ∀ p ∈ H, u.proc p = (π.start A inp_u).proc p)
    (hu_msg : ∀ e : Envelope P M, e.src ∈ H → u.msgs.count e = (π.start A inp_u).msgs.count e)
    {xl : List (Action P M)} {s₁ : State P S M V}
    (hmtr : (π.lts F_src).MTr (π.start F_src inp_s) xl s₁)
    (hhon : ∀ a ∈ xl, a.IsHonest) :
    ∃ yl u', (π.lts A).MTr u yl u' ∧
      (∀ p ∈ H, u'.proc p = s₁.proc p) ∧
      (∀ p ∉ H, u'.proc p = u.proc p) ∧
      (∀ e : Envelope P M, e.src ∉ H → u'.msgs.count e = u.msgs.count e) := by
  refine π.replay_subset_mTr hAH hmtr hhon
    (fun e he => hcover e.src (π.start_msgs_src_notMem F_src inp_s he))
    hcover (fun p hp => by
      rw [hu_proc p hp]
      simp [start, initState, show p ≠ dealer from fun h => hdH (h ▸ hp)])
    fun e heH _ => ?_
  rw [hu_msg e heH, π.start_msgs_count_of_notMem F_src inp_s (Finset.disjoint_left.mp hHF heH),
    π.start_msgs_count_of_notMem A inp_u (Finset.disjoint_right.mp hAH heH)]
  simp [initSend, show e.src ≠ dealer from fun h => hdH (h ▸ heH)]

/-- **Split-brain impossibility for consistent broadcast**
([BrachaToueg1985]; [Bracha1987]). If the processes can be partitioned into three pairwise
disjoint groups `A, B, C` each of size at most `t`, with `dealer ∈ A`, `b₀ ∈ B`, `c₀ ∈ C`, then
no protocol satisfies both `validity` and `consistency` over a value domain containing two
distinct values `v₀ ≠ v₁`. Totality and `noSpurious` are not needed. -/
theorem not_consistentBroadcast_of_partition {t : ℕ}
    (A B C : Finset P)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hcover : ∀ p : P, p ∈ A ∨ p ∈ B ∨ p ∈ C)
    (hA : A.card ≤ t) (hB : B.card ≤ t) (hC : C.card ≤ t)
    (hdA : dealer ∈ A) {b₀ c₀ : P} (hb₀ : b₀ ∈ B) (hc₀ : c₀ ∈ C)
    {v₀ v₁ : V} (hne : v₀ ≠ v₁)
    (hval : ∀ (F : Finset P), F.card ≤ t → dealer ∉ F →
      ∀ (v : V) (ss : ωSequence (State P S M V)) (xs : ωSequence (Action P M)),
      π.AdmissibleRun F (some v) ss xs → ∀ i ∉ F, ∃ k, (ss k).ProcDecided i v)
    (hcon : ∀ (F : Finset P), F.card ≤ t → ∀ (input : Option V) (s : State P S M V),
      π.Reachable F input s → ∀ i ∉ F, ∀ j ∉ F, ∀ w₁ w₂,
      s.ProcDecided i w₁ → s.ProcDecided j w₂ → w₁ = w₂) :
    False := by
  have hd_not_C : dealer ∉ C := Finset.disjoint_left.mp hAC hdA
  have hd_not_B : dealer ∉ B := Finset.disjoint_left.mp hAB hdA
  have hb₀_not_C : b₀ ∉ C := Finset.disjoint_left.mp hBC hb₀
  have hcoverC : ∀ p, p ∉ C → p ∈ A ∨ p ∈ B := fun p hp =>
    (hcover p).imp_right (·.resolve_right hp)
  have hcoverB : ∀ p, p ∉ B → p ∈ A ∨ p ∈ C := fun p hp =>
    (hcover p).imp_right (·.resolve_left hp)
  -- Run 1 (`C` silent faulty, `some v₀`) drives `b₀` to decide `v₀`.
  obtain ⟨xl₀, s₀, hmtr₀, hhon₀, hk₀⟩ :=
    π.honest_decision_prefix C v₀ b₀ fun ss xs ha => hval C hC hd_not_C v₀ ss xs ha b₀ hb₀_not_C
  -- Run 2 (`B` silent faulty, `some v₁`) drives `c₀` to decide `v₁`.
  obtain ⟨xl₁, s₁, hmtr₁, hhon₁, hk₁⟩ :=
    π.honest_decision_prefix B v₁ c₀ fun ss xs ha =>
      hval B hB hd_not_B v₁ ss xs ha c₀ (Finset.disjoint_right.mp hBC hc₀)
  -- Run 3 (`A` faulty): replay `B` from Run 1, then `C` from Run 2.
  obtain ⟨yl₀, u₁, hyl₀, hu₁_B, hu₁_out, hu₁_msg⟩ := π.replay_from_start hAB hBC hd_not_B hcoverC
    (inp_u := none) (fun _ _ => rfl) (fun _ _ => rfl) hmtr₀ hhon₀
  obtain ⟨yl₁, u₂, hyl₁, hu₂_C, hu₂_out, _⟩ := π.replay_from_start hAC hBC.symm hd_not_C hcoverB
    (inp_u := none)
    (fun p hp => hu₁_out p (Finset.disjoint_right.mp hBC hp))
    (fun e he => hu₁_msg e (Finset.disjoint_right.mp hBC he)) hmtr₁ hhon₁
  have hreach : π.Reachable A none u₂ := ⟨yl₀ ++ yl₁, LTS.MTr.comp (π.lts A) hyl₀ hyl₁⟩
  have hb_dec : u₂.ProcDecided b₀ v₀ :=
    (congrArg ProcState.out ((hu₂_out b₀ hb₀_not_C).trans (hu₁_B b₀ hb₀))).trans hk₀
  have hc_dec : u₂.ProcDecided c₀ v₁ := (congrArg ProcState.out (hu₂_C c₀ hc₀)).trans hk₁
  exact hne (hcon A hA none u₂ hreach b₀ (Finset.disjoint_right.mp hAB hb₀)
    c₀ (Finset.disjoint_right.mp hAC hc₀) v₀ v₁ hb_dec hc_dec)

/-- **Single-value impossibility for full reliable broadcast** (even for a singleton domain such
as `V = Unit`). Under any `3`-partition `A, B, C` of sizes at most `t` with `dealer ∈ A`,
`b₀ ∈ B`, and `c₀ ∈ C`, no protocol satisfies `validity`, `totality`, and `noSpurious`
simultaneously (`consistency` is not needed, nor are two distinct values). -/
theorem not_reliableBroadcast_of_partition {t : ℕ}
    (A B C : Finset P)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hcover : ∀ p : P, p ∈ A ∨ p ∈ B ∨ p ∈ C)
    (hA : A.card ≤ t) (hB : B.card ≤ t) (hC : C.card ≤ t)
    (hdA : dealer ∈ A) {b₀ c₀ : P} (hb₀ : b₀ ∈ B) (hc₀ : c₀ ∈ C) (v₀ : V)
    (hval : ∀ (F : Finset P), F.card ≤ t → dealer ∉ F →
      ∀ (v : V) (ss : ωSequence (State P S M V)) (xs : ωSequence (Action P M)),
      π.AdmissibleRun F (some v) ss xs → ∀ i ∉ F, ∃ k, (ss k).ProcDecided i v)
    (htot : ∀ (F : Finset P), F.card ≤ t → ∀ (input : Option V)
      (ss : ωSequence (State P S M V)) (xs : ωSequence (Action P M)),
      π.AdmissibleRun F input ss xs →
      ∀ i ∉ F, ∀ k v, (ss k).ProcDecided i v → ∀ j ∉ F, ∃ k', (ss k').ProcDecided j v)
    (hnoSp : ∀ (F : Finset P), F.card ≤ t → dealer ∉ F →
      ∀ (input : Option V) (s : State P S M V),
      π.Reachable F input s → ∀ i ∉ F, ∀ v, s.ProcDecided i v → input = some v) :
    False := by
  have hd_not_C : dealer ∉ C := Finset.disjoint_left.mp hAC hdA
  have hd_not_B : dealer ∉ B := Finset.disjoint_left.mp hAB hdA
  have hcoverC : ∀ p, p ∉ C → p ∈ A ∨ p ∈ B := fun p hp =>
    (hcover p).imp_right (·.resolve_right hp)
  have hcoverA : ∀ p, p ∉ A → p ∈ B ∨ p ∈ C := fun p hp => (hcover p).resolve_left hp
  -- Step 1 (`C` silent faulty, `some v₀`): drive `b₀ ∈ B` to decide `v₀`.
  obtain ⟨xl₀, s₀, hmtr₀, hhon₀, hk₀⟩ :=
    π.honest_decision_prefix C v₀ b₀ fun ss xs ha =>
      hval C hC hd_not_C v₀ ss xs ha b₀ (Finset.disjoint_left.mp hBC hb₀)
  -- Step 2 (`A` faulty, `none`): replay `B`'s prefix so `b₀` decides `v₀` while `C` stays initial.
  obtain ⟨yl₀, u₁, hyl₀, hu₁_B, hu₁_out, hu₁_msg⟩ := π.replay_from_start hAB hBC hd_not_B hcoverC
    (inp_u := none) (fun _ _ => rfl) (fun _ _ => rfl) hmtr₀ hhon₀
  have hreach_u₁ : π.Reachable A none u₁ := ⟨yl₀, hyl₀⟩
  have hb_dec : u₁.ProcDecided b₀ v₀ := (congrArg ProcState.out (hu₁_B b₀ hb₀)).trans hk₀
  -- Step 3: extend `u₁` with a fair Byzantine-free suffix; by `totality`, `c₀ ∈ C` decides `v₀`.
  obtain ⟨ss, xs, k₀, ha, hsk₀, hhon_suf⟩ := hreach_u₁.exists_admissibleRun
  obtain ⟨k₁, hk₁⟩ := htot A hA none ss xs ha b₀ (Finset.disjoint_right.mp hAB hb₀) k₀ v₀
    (hsk₀.symm ▸ hb_dec) c₀ (Finset.disjoint_right.mp hAC hc₀)
  let k₂ := max k₀ k₁
  have hm_suf : (π.lts A).MTr u₁ (xs.extract k₀ k₂) (ss k₂) :=
    hsk₀ ▸ ha.2.1.extract_mTr (le_max_left k₀ k₁)
  have hc_dec₂ : (ss k₂).ProcDecided c₀ v₀ :=
    π.omega_procDecided_stable ha.2.1 (le_max_right k₀ k₁) hk₁
  -- Step 4 (`B` faulty, `none`): replay `C`'s steps of the honest suffix onto `π.start B none`.
  have hsrc_u₁ : ∀ e ∈ u₁.msgs, e.src ∈ B ∨ e.src ∈ C :=
    fun e he => hcoverA e.src (hreach_u₁.msgs_src_notMem he)
  have hproc_C : ∀ p ∈ C, (π.start B none).proc p = u₁.proc p := fun p hp => by
    rw [hu₁_out p (Finset.disjoint_right.mp hBC hp)]
    simp [start, initState, show p ≠ dealer from fun h => hd_not_C (h ▸ hp)]
  have hmsg_C : ∀ e : Envelope P M, e.src ∈ C → e.dest ∈ C →
      u₁.msgs.count e ≤ (π.start B none).msgs.count e := fun e heC _ => by
    have hnotB : e.src ∉ B := Finset.disjoint_right.mp hBC heC
    rw [hu₁_msg e hnotB, π.start_msgs_count_of_notMem A none (Finset.disjoint_right.mp hAC heC),
      π.start_msgs_count_of_notMem B none hnotB]
  obtain ⟨yl₁, w₁, hyl₁, hw₁_C, _, _⟩ := π.replay_subset_mTr hBC hm_suf
    (extract_isHonest xs hhon_suf) hsrc_u₁ hcoverA hproc_C hmsg_C
  have hw₁_dec : w₁.ProcDecided c₀ v₀ := (congrArg ProcState.out (hw₁_C c₀ hc₀)).trans hc_dec₂
  exact absurd
    (hnoSp B hB hd_not_B none w₁ ⟨yl₁, hyl₁⟩ c₀ (Finset.disjoint_right.mp hBC hc₀) v₀ hw₁_dec)
    (by simp)

private lemma exists_three_partition {P : Type*} [Fintype P]
    (dealer : P) {t : ℕ} (h3 : 3 ≤ Fintype.card P) (hle : Fintype.card P ≤ 3 * t) :
    ∃ A B C : Finset P,
      Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧
      (∀ p : P, p ∈ A ∨ p ∈ B ∨ p ∈ C) ∧
      A.card ≤ t ∧ B.card ≤ t ∧ C.card ≤ t ∧
      dealer ∈ A ∧ B.Nonempty ∧ C.Nonempty := by
  classical
  let n := Fintype.card P
  have hn3 : 3 ≤ n := h3
  let zero : Fin n := ⟨0, by omega⟩
  let e : P ≃ Fin n := (Fintype.equivFin P).trans (Equiv.swap (Fintype.equivFin P dealer) zero)
  have he_dealer : e dealer = zero := by simp [e, Equiv.swap_apply_left]
  let grp : Fin 3 → Finset P := fun k => Finset.univ.filter fun p => (e p : ℕ) % 3 = k.val
  have hgrp_disj : ∀ k₁ k₂ : Fin 3, k₁ ≠ k₂ → Disjoint (grp k₁) (grp k₂) :=
    fun _ _ _ => by finset_card
  have hgrp_card : ∀ k : Fin 3, (grp k).card ≤ t := fun k => by
    refine (Finset.card_le_card_of_injOn (fun p => (e p : ℕ) / 3) (fun p _ => ?_)
      fun p hp q hq hdiv => ?_).trans_eq (Finset.card_range t)
    · simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.div_lt_of_lt_mul ((e p).isLt.trans_le (by omega))
    · simp only [grp, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
      exact e.injective (Fin.ext (by dsimp only at hdiv; omega))
  refine ⟨grp 0, grp 1, grp 2,
    hgrp_disj 0 1 (by decide), hgrp_disj 0 2 (by decide), hgrp_disj 1 2 (by decide),
    fun p => ?_, hgrp_card 0, hgrp_card 1, hgrp_card 2, by simp [grp, he_dealer, zero],
    ⟨e.symm ⟨1, by omega⟩, by simp [grp]⟩, ⟨e.symm ⟨2, by omega⟩, by simp [grp]⟩⟩
  simp only [grp, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_zero, Fin.val_one,
    Fin.val_two]
  omega

/-- **No asynchronous Byzantine reliable broadcast for `3 ≤ n ≤ 3t`**
([BrachaToueg1985]; [Bracha1987]). For any **nonempty** value domain `V` (even a singleton such
as `Unit`), no deterministic asynchronous protocol on `n` processes with `3 ≤ n ≤ 3t` solves
reliable broadcast against `t` Byzantine faults. -/
theorem not_solvesReliableBroadcast [Nonempty V] {t : ℕ}
    (h3 : 3 ≤ Fintype.card P) (hle : Fintype.card P ≤ 3 * t) :
    ¬ π.SolvesReliableBroadcast t := by
  intro hsol
  obtain ⟨v₀⟩ := ‹Nonempty V›
  obtain ⟨A, B, C, hAB, hAC, hBC, hcover, hA, hB, hC, hdA, ⟨b₀, hb₀⟩, ⟨c₀, hc₀⟩⟩ :=
    exists_three_partition dealer h3 hle
  exact π.not_reliableBroadcast_of_partition A B C hAB hAC hBC hcover hA hB hC hdA hb₀ hc₀ v₀
    hsol.validity hsol.totality hsol.noSpurious

/-- **Three-process impossibility**: on `Fin 3`, no asynchronous deterministic protocol over a
nonempty value domain `V` solves reliable broadcast against a single Byzantine fault. -/
theorem not_solvesReliableBroadcast_three {S M V : Type*} [DecidableEq M] [Nonempty V]
    (dealer : Fin 3) (π : Protocol (Fin 3) S M V dealer) :
    ¬ π.SolvesReliableBroadcast 1 :=
  π.not_solvesReliableBroadcast (by decide) (by decide)

end Protocol

end Cslib.Distributed.AsyncByzantine
