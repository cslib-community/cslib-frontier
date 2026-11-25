/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.ABD.Basic
import CslibFrontier.Computability.Distributed.ABD.Protocol
import CslibFrontier.Tactic.FinsetCard
import Mathlib.Data.Fintype.EquivFin

/-!
# The `2t + 1` resilience threshold for asynchronous linearizable atomic registers

This module formalizes the partition-indistinguishability lower bound and sharp process-count
characterization for wait-free linearizable atomic registers over deterministic asynchronous
message passing. Attiya, Bar-Noy, and Dolev ([AttiyaBarNoyDolev1995], §1, p. 127) motivate
majority resilience (`⌊(n - 1)/2⌋` faults) by observing that suspending messages between two
groups of fewer than a majority lets the groups operate separately and perform contradicting
operations. Here we prove the quantified converse for `2 ≤ Fintype.card P ≤ 2 * t` over any
nontrivial value domain `[Nontrivial V]` (`not_implementsAtomicRegister_of_partition` and
`not_implementsAtomicRegister`), and combine it with the single-process zero-message disjunct
`implementsAtomicRegister_local_of_card_le_one` (`Fintype.card P ≤ 1`) and the cardinality-quorum
envelope specialization `implementsAtomicRegister_abd` (`2 * t < Fintype.card P`, after
[LynchShvartsman1997], §4.1–4.2 and [AttiyaBarNoyDolev1995], §4) into Lean's resilience
characterization `exists_linearizableRegister_iff`.

## Partition replay argument

Partition `P` into two disjoint nonempty subsets `A, B : Finset P` with `A.card ≤ t`, `B.card ≤ t`,
`a₀ ∈ A`, and `b₀ ∈ B`, and choose `v₁ ≠ v₀`:

1. **Run 1 (`F = B` crashed/delayed):** starting from `π.start`, invoke `write v₁` at `a₀ ∈ A` and
   extend via `Protocol.exists_fair_omegaExecution B`, delivering messages only to `A`. By
   `terminates B`, `a₀`'s write completes at some reachable state `s₁` in which every `p ∈ B`
   retains its initial local state `π.start.proc p` and every initial boot message addressed to `B`
   is still in transit (`π.start.msgs.count e ≤ s₁.msgs.count e`).
2. **Run 2 (`F = A` crashed/delayed):** starting from `π.start`, invoke `read` at `b₀ ∈ B` and
   extend via `Protocol.exists_fair_omegaExecution A`, delivering messages only to `B`. By
   `terminates A`, `b₀`'s read completes at some reachable state `s₂` returning `r`, and by
   `linearizable s₂` (with zero writes in `s₂.history`), `r = v₀`.
3. **Run 3 (combined execution):** starting from `s₁` (after `write v₁` has already completed at
   step `< s₁.step`), replay `Action.invoke b₀ .read` followed by Run 2's `B`-only delivery prefix,
   holding all cross-partition `A → B` messages in flight. Because `B`'s local states match
   `π.start` and all `B`-destined envelopes from Run 2 are available in `s₁.msgs`, Run 3 reaches a
   state `u₂` where `u₂.history` consists of the completed `write v₁` (`op 0`) strictly preceding in
   real time (`prec u₂.history 0 1`) a completed `read` returning `v₀` (`op 1`), violating
   `linearizable u₂`.

## Main results

* `Cslib.Distributed.ABD.Protocol.not_implementsAtomicRegister_of_partition`: partition
  impossibility given disjoint nonempty `A, B` covering `P` with `A.card ≤ t` and `B.card ≤ t`.
* `Cslib.Distributed.ABD.Protocol.not_implementsAtomicRegister`: no protocol implements a `t`-fault
  wait-free linearizable atomic register when `2 ≤ Fintype.card P ≤ 2 * t` and `[Nontrivial V]`.
* `Cslib.Distributed.ABD.exists_linearizableRegister_iff`: a `t`-fault wait-free linearizable
  atomic register protocol over `(P, V)` exists if and only if
  `Fintype.card P ≤ 1 ∨ 2 * t < Fintype.card P`.

## References

* [H. Attiya, A. Bar-Noy, D. Dolev, *Sharing memory robustly in message-passing
  systems*][AttiyaBarNoyDolev1995]
* [N. A. Lynch, A. A. Shvartsman, *Robust emulation of shared memory using dynamic
  quorum-acknowledged broadcasts*][LynchShvartsman1997]
-/

public section

namespace Cslib.Distributed.ABD

open Cslib Cslib.ωSequence

namespace Protocol

variable {P S M V : Type*} [Fintype P] [DecidableEq P] [DecidableEq M]
  (π : Protocol P S M V)

omit [Fintype P] [DecidableEq P] [DecidableEq M] in
private lemma extract_isDrainAction (F : Finset P) (xs : ωSequence (Action P M V)) {k₀ k₁ : ℕ}
    (hdrain : ∀ j, k₀ ≤ j → IsDrainAction F (xs j)) :
    ∀ a ∈ xs.extract k₀ k₁, IsDrainAction F a := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hi' : i < k₁ - k₀ := by simpa [ωSequence.length_extract] using hi
  rw [xs.get_extract hi']
  exact hdrain (k₀ + i) (Nat.le_add_right k₀ i)

omit [Fintype P] in
/-- Along any finite sequence of `IsDrainAction F` transitions:
1. `history.length` does not change;
2. any response timestamp in `history` stays strictly below `step`;
3. every process `p ∈ F` keeps its initial `proc p`;
4. message counts addressed to `F` never decrease. -/
private lemma mTr_drain_preserves {F : Finset P} {s₀ s₁ : State P S M V}
    {xl : List (Action P M V)} (hmtr : π.lts.MTr s₀ xl s₁)
    (hdrain : ∀ a ∈ xl, IsDrainAction F a)
    (hresp₀ : ∀ (i : ℕ) (hi : i < s₀.history.length) r,
      s₀.history[i].status.respStep? = some r → r < s₀.step) :
    s₁.history.length = s₀.history.length ∧
    (∀ (i : ℕ) (hi₁ : i < s₁.history.length) r,
      s₁.history[i].status.respStep? = some r → r < s₁.step) ∧
    (∀ p ∈ F, s₁.proc p = s₀.proc p) ∧
    (∀ e : Envelope P M, e.dest ∈ F → s₀.msgs.count e ≤ s₁.msgs.count e) := by
  induction hmtr with
  | refl =>
    exact ⟨rfl, hresp₀, fun _ _ => rfl, fun _ _ => le_rfl⟩
  | @stepL s a s' xl' s_end htr _ ih =>
    have ha : IsDrainAction F a := hdrain a List.mem_cons_self
    have hrest : ∀ b ∈ xl', IsDrainAction F b := fun b hb => hdrain b (List.mem_cons_of_mem a hb)
    cases a with
    | invoke _ _ => exact False.elim ha
    | stutter => obtain rfl := htr; exact ih hrest hresp₀
    | deliver m =>
      obtain ⟨_, rfl⟩ := htr
      have hmdest : m.dest ∉ F := ha
      let s' := π.doDeliver m s
      have hlen_s' : s'.history.length = s.history.length := by simp [s', doDeliver]
      have hresp_s' : ∀ (i : ℕ) (hi' : i < s'.history.length) r,
          s'.history[i].status.respStep? = some r → r < s'.step := by
        intro i hi' r hr
        have hi : i < s.history.length := hlen_s' ▸ hi'
        obtain ⟨_, _, _, hstep⟩ := deliverHistory_entry_preserves s.history
          (π.onRecv m.dest (s.proc m.dest).state m.src m.body).resp s.step
          (s.proc m.dest).pending hi hi'
        rcases hstep r hr with hold | rfl
        exacts [Nat.lt_succ_of_lt (hresp₀ i hi r hold), Nat.lt_succ_self s.step]
      obtain ⟨hlen1, hresp1, hproc1, hmsg1⟩ := ih hrest hresp_s'
      refine ⟨hlen1.trans hlen_s', hresp1, ?_, ?_⟩
      · intro p hp
        rw [hproc1 p hp]
        simp [doDeliver, Function.update_of_ne (ne_of_mem_of_not_mem hp hmdest)]
      · intro e heF
        have hem : e ≠ m := fun heq => hmdest (heq ▸ heF)
        refine le_trans ?_ (hmsg1 e heF)
        simp only [doDeliver, Multiset.count_add, Multiset.count_erase_of_ne hem]
        exact Nat.le_add_right _ _

/-- Simulation relation coupling Run 2 (`s`, after invoking `read` at `b₀` from `π.start`) with
Run 3 (`u`, after invoking `read` at `b₀` from `s₁`). -/
private def SimAfterRead (B : Finset P) (s₁ : State P S M V) (b₀ : P)
    (s u : State P S M V) : Prop :=
  (∀ p ∈ B, (u.proc p).state = (s.proc p).state) ∧
  (∀ e : Envelope P M, e.dest ∈ B → s.msgs.count e ≤ u.msgs.count e) ∧
  (∀ p ∈ B, p ≠ b₀ → (s.proc p).pending = none ∧ (u.proc p).pending = none) ∧
  (((s.proc b₀).pending = some ⟨0, .read⟩ ∧
    (u.proc b₀).pending = some ⟨s₁.history.length, .read⟩ ∧
    s.history = [⟨b₀, .read, 0, .pending⟩] ∧
    u.history = s₁.history ++ [⟨b₀, .read, s₁.step, .pending⟩]) ∨
   (∃ r stp_s stp_u,
    (s.proc b₀).pending = none ∧
    (u.proc b₀).pending = none ∧
    s.history = [⟨b₀, .read, 0, .doneRead stp_s r⟩] ∧
    u.history = s₁.history ++ [⟨b₀, .read, s₁.step, .doneRead stp_u r⟩]))

omit [Fintype P] [DecidableEq P] [DecidableEq M] in
private lemma matchCompletion_read_cases (resp : Option (OpResp V)) :
    (∀ step, matchCompletion .read resp step = none) ∨ ∃ r, resp = some (.readRet r) := by
  rcases resp with _ | (_ | _) <;> first | exact Or.inl fun _ => rfl | exact Or.inr ⟨_, rfl⟩

private lemma simAfterRead_init {B : Finset P} {s₁ : State P S M V} {b₀ : P} (hb₀ : b₀ ∈ B)
    (hproc₁ : ∀ p ∈ B, s₁.proc p = π.start.proc p)
    (hmsg₁ : ∀ e : Envelope P M, e.dest ∈ B → π.start.msgs.count e ≤ s₁.msgs.count e) :
    SimAfterRead B s₁ b₀ (π.doInvoke b₀ .read π.start) (π.doInvoke b₀ .read s₁) := by
  have hb₀_st : (s₁.proc b₀).state = π.init b₀ := congrArg ProcState.state (hproc₁ b₀ hb₀)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    by_cases hpb : p = b₀
    · subst hpb; simp [doInvoke, start, hb₀_st]
    · simpa only [doInvoke, Function.update_of_ne hpb] using congrArg ProcState.state (hproc₁ p hp)
  · intro e heB
    simp only [doInvoke, start, hb₀_st, Multiset.count_add]
    exact Nat.add_le_add_right (hmsg₁ e heB) _
  · intro p hp hpb
    simp only [doInvoke, Function.update_of_ne hpb, hproc₁ p hp]; exact ⟨rfl, rfl⟩
  · rcases matchCompletion_read_cases (π.onInvoke b₀ (π.init b₀) .read).resp with hnone | ⟨r, hsp⟩
    · exact Or.inl (by simp [doInvoke, start, hb₀_st, invokePending, hnone])
    · right
      refine ⟨r, 0, s₁.step, ?_, ?_, ?_, ?_⟩ <;>
        simp [doInvoke, start, hb₀_st, hsp, invokePending, matchCompletion]

omit [Fintype P] in
private lemma simAfterRead_mTr {A B : Finset P} (hcover : ∀ p : P, p ∈ A ∨ p ∈ B)
    {s₁ : State P S M V} {b₀ : P} {s u s' : State P S M V} {xl : List (Action P M V)}
    (hmtr : π.lts.MTr s xl s') (hdrain : ∀ a ∈ xl, IsDrainAction A a)
    (hsim : SimAfterRead B s₁ b₀ s u) :
    ∃ yl u', π.lts.MTr u yl u' ∧ SimAfterRead B s₁ b₀ s' u' := by
  induction hmtr generalizing u with
  | refl => exact ⟨[], u, LTS.MTr.refl, hsim⟩
  | @stepL s a s_mid xl' s_end htr _ ih =>
    have ha : IsDrainAction A a := hdrain a List.mem_cons_self
    have hrest : ∀ x ∈ xl', IsDrainAction A x := fun x hx => hdrain x (List.mem_cons_of_mem a hx)
    cases a with
    | invoke _ _ => exact False.elim ha
    | stutter => obtain rfl := htr; exact ih hrest hsim
    | deliver e =>
      obtain ⟨he_mem, rfl⟩ := htr
      have hedB : e.dest ∈ B := (hcover e.dest).resolve_left ha
      obtain ⟨hst_eq, hmsg_le, hother_pend, hb₀_cases⟩ := hsim
      have he_u : e ∈ u.msgs :=
        Multiset.count_pos.mp (lt_of_lt_of_le (Multiset.count_pos.mpr he_mem) (hmsg_le e hedB))
      have htr_u : π.lts.Tr u (.deliver e) (π.doDeliver e u) := ⟨he_u, rfl⟩
      have hd_st : (u.proc e.dest).state = (s.proc e.dest).state := hst_eq e.dest hedB
      have hsim' : SimAfterRead B s₁ b₀ (π.doDeliver e s) (π.doDeliver e u) := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro p hp
          by_cases hpe : p = e.dest
          · subst hpe; simp [doDeliver, hd_st]
          · simp [doDeliver, hpe, hst_eq p hp]
        · intro m hmB
          simp only [doDeliver, hd_st, Multiset.count_add]
          apply Nat.add_le_add_right
          by_cases hme : m = e
          · subst hme; rw [Multiset.count_erase_self, Multiset.count_erase_self]
            exact Nat.sub_le_sub_right (hmsg_le m hmB) 1
          · simpa only [Multiset.count_erase_of_ne hme] using hmsg_le m hmB
        · intro p hp hpb
          obtain ⟨hsp, hup⟩ := hother_pend p hp hpb
          by_cases hpe : p = e.dest
          · subst hpe; simp [doDeliver, deliverPending, hsp, hup]
          · simp only [doDeliver, Function.update_of_ne hpe]; exact ⟨hsp, hup⟩
        · by_cases hbe : e.dest = b₀
          · subst hbe
            rcases hb₀_cases with ⟨hsp, hup, hsh, huh⟩ | ⟨r, stp_s, stp_u, hsp, hup, hsh, huh⟩
            · rcases matchCompletion_read_cases
                  (π.onRecv e.dest (s.proc e.dest).state e.src e.body).resp with hnone | ⟨r, hrsp⟩
              · exact Or.inl (by simp [doDeliver, hd_st, hsp, hup, hsh, huh, deliverPending,
                  deliverHistory, hnone])
              · right
                refine ⟨r, s.step, u.step, ?_, ?_, ?_, ?_⟩ <;>
                  simp [doDeliver, hd_st, hsp, hup, hsh, huh, hrsp, deliverPending,
                    deliverHistory, matchCompletion, List.set_append_right]
            · right
              refine ⟨r, stp_s, stp_u, ?_, ?_, ?_, ?_⟩ <;>
                simp [doDeliver, deliverPending, deliverHistory, hsp, hup, hsh, huh]
          · obtain ⟨hsp_d, hup_d⟩ := hother_pend e.dest hedB hbe
            simpa only [doDeliver, Function.update_of_ne (Ne.symm hbe), deliverHistory,
              hsp_d, hup_d] using hb₀_cases
      obtain ⟨yl, u', hyl, hsim_end⟩ := ih hrest hsim'
      exact ⟨.deliver e :: yl, u', LTS.MTr.stepL htr_u hyl, hsim_end⟩

omit [Fintype P] [DecidableEq P] [DecidableEq M] in
/-- A linearizable history consisting of a single completed `read` (and zero writes) must return
the initial value `v₀`. -/
private lemma read_eq_init_of_singleton_linearizable {v₀ r : V} {b₀ : P} {stp : ℕ}
    (hlin : Linearizable v₀ ([⟨b₀, .read, 0, .doneRead stp r⟩] : List (OpRecord P V))) :
    r = v₀ := by
  obtain ⟨seq, hnd, hcomp, _, hvalid⟩ := hlin
  obtain ⟨hin_bounds, _⟩ := (seqValid_iff_registerValAfter v₀ _ seq).mp hvalid
  have hperm : seq.Perm [0] :=
    (List.perm_ext_iff_of_nodup hnd (by decide)).mpr fun x =>
      ⟨fun hx => by have := (hin_bounds x hx).1; simp at this ⊢; omega,
       fun hx => (List.mem_singleton.mp hx) ▸ hcomp 0 (by simp) rfl⟩
  rw [List.perm_singleton.mp hperm] at hvalid
  simpa [seqValid] using hvalid

omit [Fintype P] [DecidableEq P] [DecidableEq M] in
/-- A 2-operation history consisting of a completed `write v₁` at index `0` strictly preceding in
real time (`stp₁ < inv₂`) a completed `read` returning `v₀` at index `1` cannot be linearizable
when `v₁ ≠ v₀`. -/
private lemma not_linearizable_write_then_stale_read {v₀ v₁ : V} (hne : v₁ ≠ v₀)
    {a₀ b₀ : P} {stp₁ inv₂ stp₂ : ℕ} (hlt : stp₁ < inv₂) :
    ¬ Linearizable v₀
      ([⟨a₀, .write v₁, 0, .doneWrite stp₁⟩, ⟨b₀, .read, inv₂, .doneRead stp₂ v₀⟩] :
        List (OpRecord P V)) := by
  rintro ⟨seq, hnd, hcomp, hprec_ord, hvalid⟩
  let hist : List (OpRecord P V) :=
    [⟨a₀, .write v₁, 0, .doneWrite stp₁⟩, ⟨b₀, .read, inv₂, .doneRead stp₂ v₀⟩]
  obtain ⟨hin_bounds, _⟩ := (seqValid_iff_registerValAfter v₀ hist seq).mp hvalid
  have h0 : 0 ∈ seq := hcomp 0 (by simp) rfl
  have h1 : 1 ∈ seq := hcomp 1 (by simp) rfl
  have hidx01 : seq.idxOf 0 < seq.idxOf 1 :=
    hprec_ord 0 h0 1 h1 ⟨by simp, by simp, stp₁, rfl, hlt⟩
  have hperm : seq.Perm [0, 1] :=
    (List.perm_ext_iff_of_nodup hnd (by decide)).mpr fun x =>
      ⟨fun hx => by have := (hin_bounds x hx).1; simp [hist] at this ⊢; omega,
       by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro (rfl | rfl) <;> assumption⟩
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hperm.length_eq
  have hab : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by simp at h0 h1; omega
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hv : v₀ = v₁ := by simpa [seqValid] using hvalid
    exact hne hv.symm
  · simp at hidx01

private lemma exists_completed_drain_of_invoke {t : ℕ} {v₀ : V}
    (hImpl : π.ImplementsAtomicRegister v₀ t) (F : Finset P) (hF : F.card ≤ t)
    {c : P} (hc : c ∉ F) (kind : OpKind V) :
    ∃ (s : State P S M V) (xl : List (Action P M V)) (hi : 0 < s.history.length),
      π.Reachable s ∧
      π.lts.MTr (π.doInvoke c kind π.start) xl s ∧
      (∀ a ∈ xl, IsDrainAction F a) ∧
      s.history[0].status.isCompleted = true := by
  let s_init := π.doInvoke c kind π.start
  have hr₀ : π.Reachable s_init := ⟨[.invoke c kind], LTS.MTr.single π.lts ⟨rfl, rfl⟩⟩
  obtain ⟨ss, xs, k₀, ha, hss0, hdrain⟩ := hr₀.exists_admissibleRun F
  have hi0 : 0 < (ss k₀).history.length := by simp [hss0, s_init, doInvoke, start]
  have hc0 : (ss k₀).history[0].caller ∉ F := by simpa [hss0, s_init, doInvoke, start] using hc
  obtain ⟨k, hk_lt, hk_ge, hk_comp⟩ := hImpl.terminates F hF ss xs ha k₀ 0 hi0 hc0
  exact ⟨ss k, xs.extract k₀ k, hk_lt, π.admissibleRun_reachable ha k,
    by simpa [hss0, s_init] using ha.2.1.extract_mTr hk_ge,
    extract_isDrainAction F xs hdrain, hk_comp⟩

/-- **Partition impossibility for asynchronous linearizable registers** (formalizing the
two-group message-suspension obstruction noted in [AttiyaBarNoyDolev1995], §1, p. 127): if `P`
can be partitioned into two disjoint subsets `A, B` each of size at most `t`, with `a₀ ∈ A` and
`b₀ ∈ B`, and there exists `v₁ ≠ v₀`, then `π` cannot implement a `t`-resilient wait-free
linearizable atomic register initialized to `v₀`. -/
theorem not_implementsAtomicRegister_of_partition {t : ℕ}
    (A B : Finset P) (hAB : Disjoint A B) (hcover : ∀ p : P, p ∈ A ∨ p ∈ B)
    (hA : A.card ≤ t) (hB : B.card ≤ t)
    {a₀ b₀ : P} (ha₀ : a₀ ∈ A) (hb₀ : b₀ ∈ B)
    {v₀ v₁ : V} (hne : v₁ ≠ v₀) :
    ¬ π.ImplementsAtomicRegister v₀ t := by
  intro hImpl
  have ha₀_notB : a₀ ∉ B := Finset.disjoint_left.mp hAB ha₀
  have hb₀_notA : b₀ ∉ A := Finset.disjoint_right.mp hAB hb₀
  -- Run 1 (`F = B`): invoke `write v₁` at `a₀ ∈ A` and drain only `A`-destined messages.
  let s₁_init := π.doInvoke a₀ (.write v₁) π.start
  obtain ⟨s₁, xl₁, hk₁_lt, hreach_s₁, hm₁, hdrain₁, hk₁_comp⟩ :=
    π.exists_completed_drain_of_invoke hImpl B hB ha₀_notB (.write v₁)
  have hresp_s₁_init : ∀ (i : ℕ) (hi : i < s₁_init.history.length) r,
      s₁_init.history[i].status.respStep? = some r → r < s₁_init.step := by
    intro i hi r hr
    obtain rfl : i = 0 := Nat.lt_one_iff.mp (by simpa [s₁_init, doInvoke, start] using hi)
    rcases hsp : (π.onInvoke a₀ (π.init a₀) (.write v₁)).resp with _ | (_ | _) <;>
      simp [s₁_init, doInvoke, start, hsp, matchCompletion, OpStatus.respStep?] at hr ⊢
    omega
  obtain ⟨hlen₁, hresp₁, hproc₁_B, hmsg₁_B⟩ :=
    π.mTr_drain_preserves hm₁ hdrain₁ hresp_s₁_init
  obtain ⟨rec0, hs₁_eq⟩ : ∃ rec0, s₁.history = [rec0] :=
    List.length_eq_one_iff.mp (by simpa [s₁_init, doInvoke, start] using hlen₁)
  have hs₁_rec : ∃ stp₁ < s₁.step, s₁.history = [⟨a₀, .write v₁, 0, .doneWrite stp₁⟩] := by
    obtain ⟨hc0, hk0, hinv0⟩ :=
      π.mTr_history_entry_preserves hm₁ (by simp [doInvoke, start]) hk₁_lt
    simp only [doInvoke, start, List.nil_append, List.getElem_singleton] at hc0 hk0 hinv0
    obtain ⟨seq₁, _, hcomp₁, _, hvalid₁⟩ := hImpl.linearizable s₁ hreach_s₁
    obtain ⟨hin₁, _⟩ := (seqValid_iff_registerValAfter v₀ s₁.history seq₁).mp hvalid₁
    have helig0 : s₁.history[0].isEligible := (hin₁ 0 (hcomp₁ 0 hk₁_lt hk₁_comp)).2
    cases hst0 : s₁.history[0].status with
    | pending => simp [hst0, OpStatus.isCompleted, OpStatus.respStep?] at hk₁_comp
    | doneRead _ _ => simp [OpRecord.isEligible, hk0, hst0] at helig0
    | doneWrite stp₁ =>
      refine ⟨stp₁, hresp₁ 0 hk₁_lt stp₁ (by simp [hst0, OpStatus.respStep?]), ?_⟩
      rw [hs₁_eq]; congr 1
      simp only [hs₁_eq, List.getElem_cons_zero] at hc0 hk0 hinv0 hst0
      ext <;> assumption
  obtain ⟨stp₁, hstp₁_lt, hs₁_hist⟩ := hs₁_rec
  have hs₁_procB : ∀ p ∈ B, s₁.proc p = π.start.proc p := by
    intro p hp
    rw [hproc₁_B p hp]
    simp [doInvoke, Function.update_of_ne (ne_of_mem_of_not_mem hp ha₀_notB)]
  have hs₁_msgB : ∀ e : Envelope P M, e.dest ∈ B → π.start.msgs.count e ≤ s₁.msgs.count e := by
    intro e heB
    refine le_trans ?_ (hmsg₁_B e heB)
    simp only [doInvoke, Multiset.count_add]
    exact Nat.le_add_right _ _
  -- Run 2 (`F = A`): invoke `read` at `b₀ ∈ B` and drain only `B`-destined messages.
  obtain ⟨s₂, xl₂, _, hreach_s₂, hm₂, hdrain₂, hk₂_comp⟩ :=
    π.exists_completed_drain_of_invoke hImpl A hA hb₀_notA .read
  -- Run 3: from `s₁`, invoke `read` at `b₀` and replay Run 2's `B`-only prefix.
  have htr₃_0 : π.lts.Tr s₁ (.invoke b₀ .read) (π.doInvoke b₀ .read s₁) :=
    ⟨by rw [hs₁_procB b₀ hb₀]; rfl, rfl⟩
  have hsim₀ := π.simAfterRead_init hb₀ hs₁_procB hs₁_msgB
  obtain ⟨yl, u₂, hyl, hsim₂⟩ := π.simAfterRead_mTr hcover hm₂ hdrain₂ hsim₀
  rcases hsim₂.2.2.2 with ⟨_, _, hs₂_pend, _⟩ | ⟨r, stp_s, stp_u, _, _, hs₂_done, hu₂_done⟩
  · simp [hs₂_pend, OpStatus.isCompleted, OpStatus.respStep?] at hk₂_comp
  · obtain rfl : v₀ = r :=
      (read_eq_init_of_singleton_linearizable (hs₂_done ▸ hImpl.linearizable s₂ hreach_s₂)).symm
    have hreach_u₂ : π.Reachable u₂ :=
      hreach_s₁.trans ⟨.invoke b₀ .read :: yl, LTS.MTr.stepL htr₃_0 hyl⟩
    have hu₂_hist : u₂.history =
        [⟨a₀, .write v₁, 0, .doneWrite stp₁⟩, ⟨b₀, .read, s₁.step, .doneRead stp_u v₀⟩] := by
      rw [hu₂_done, hs₁_hist]; rfl
    exact not_linearizable_write_then_stale_read hne hstp₁_lt
      (hu₂_hist ▸ hImpl.linearizable u₂ hreach_u₂)

private lemma exists_two_partition {P : Type*} [Fintype P] {t : ℕ}
    (h2 : 2 ≤ Fintype.card P) (hle : Fintype.card P ≤ 2 * t) :
    ∃ A B : Finset P,
      Disjoint A B ∧ (∀ p : P, p ∈ A ∨ p ∈ B) ∧
      A.card ≤ t ∧ B.card ≤ t ∧ A.Nonempty ∧ B.Nonempty := by
  classical
  let n := Fintype.card P
  let e : P ≃ Fin n := Fintype.equivFin P
  let grp : Fin 2 → Finset P := fun k => Finset.univ.filter fun p => (e p : ℕ) % 2 = k.val
  have hdisj : Disjoint (grp 0) (grp 1) := by finset_card
  have hcard : ∀ k : Fin 2, (grp k).card ≤ t := by
    intro k
    calc (grp k).card
        ≤ (Finset.range t).card := by
          apply Finset.card_le_card_of_injOn (fun p => (e p : ℕ) / 2)
          · intro p _
            have hlt : (e p : ℕ) < n := (e p).isLt
            simp only [Finset.coe_range, Set.mem_Iio]; omega
          · intro p hp q hq hdiv
            simp only [grp, Finset.coe_filter, Finset.mem_univ, true_and,
              Set.mem_ofPred_eq] at hp hq
            refine e.injective (Fin.ext ?_)
            have hmod : (e p : ℕ) % 2 = (e q : ℕ) % 2 := hp.trans hq.symm
            dsimp only at hdiv
            omega
      _ = t := Finset.card_range t
  refine ⟨grp 0, grp 1, hdisj, ?_, hcard 0, hcard 1, ?_, ?_⟩
  · intro p
    simp only [grp, Finset.mem_filter, Finset.mem_univ, true_and]
    change (e p : ℕ) % 2 = 0 ∨ (e p : ℕ) % 2 = 1; omega
  · exact ⟨e.symm ⟨0, by omega⟩, by simp [grp]⟩
  · exact ⟨e.symm ⟨1, by omega⟩, by simp [grp]⟩

/-- **No asynchronous wait-free linearizable register for `2 ≤ n ≤ 2t`**: over any nontrivial
value domain `[Nontrivial V]`, no deterministic asynchronous protocol on `P` with
`2 ≤ Fintype.card P ≤ 2 * t` implements a `t`-resilient wait-free linearizable atomic register
(quantified converse to majority resilience, motivated by [AttiyaBarNoyDolev1995], §1, p. 127). -/
theorem not_implementsAtomicRegister [Nontrivial V] {t : ℕ}
    (h2 : 2 ≤ Fintype.card P) (hle : Fintype.card P ≤ 2 * t) (v₀ : V) :
    ¬ π.ImplementsAtomicRegister v₀ t := by
  obtain ⟨v₁, hne⟩ := exists_ne v₀
  obtain ⟨A, B, hAB, hcover, hA, hB, ⟨a₀, ha₀⟩, ⟨b₀, hb₀⟩⟩ := exists_two_partition h2 hle
  exact π.not_implementsAtomicRegister_of_partition A B hAB hcover hA hB ha₀ hb₀ hne

end Protocol

/-! ### Sharp fault-tolerance threshold (`exists_linearizableRegister_iff`) -/

private def uliftStateProtocol.{w} {P S M V : Type*} (π : Protocol P S M V) :
    Protocol P (ULift.{w} S) M V where
  init p := .up (π.init p)
  initMsgs := π.initMsgs
  onInvoke p st kind :=
    let res := π.onInvoke p st.down kind
    ⟨.up res.nextState, res.outgoing, res.resp⟩
  onRecv p st src msg :=
    let res := π.onRecv p st.down src msg
    ⟨.up res.nextState, res.outgoing, res.resp⟩

private def unmapULiftState.{w} {P S M V : Type*} (u : State P (ULift.{w} S) M V) :
    State P S M V where
  msgs := u.msgs
  proc p := ⟨(u.proc p).state.down, (u.proc p).pending⟩
  history := u.history
  step := u.step

private lemma unmap_proc_update.{w} {P S V : Type*} [DecidableEq P]
    (proc : P → ProcState (ULift.{w} S) V) (q : P) (st : S) (pend : Option (PendingOp V)) (p : P) :
    ProcState.mk ((Function.update proc q (ProcState.mk (.up st) pend) p).state).down
        (Function.update proc q (ProcState.mk (.up st) pend) p).pending =
      Function.update (fun r => ProcState.mk (proc r).state.down (proc r).pending)
        q (ProcState.mk st pend) p := by
  by_cases hp : p = q <;> [subst hp; skip] <;> simp [*]

private lemma unmap_tr.{w} {P S M V : Type*} [DecidableEq P] [DecidableEq M]
    {π : Protocol P S M V} {u u' : State P (ULift.{w} S) M V} {a : Action P M V}
    (htr : (uliftStateProtocol.{w} π).lts.Tr u a u') :
    π.lts.Tr (unmapULiftState u) a (unmapULiftState u') := by
  cases a with
  | stutter =>
    obtain rfl := htr; rfl
  | invoke caller kind =>
    obtain ⟨hpend, rfl⟩ := htr
    refine ⟨hpend, ?_⟩
    ext1 <;> [rfl; (funext p; exact unmap_proc_update u.proc caller _ _ p); rfl; rfl]
  | deliver e =>
    obtain ⟨hmem, rfl⟩ := htr
    refine ⟨hmem, ?_⟩
    ext1 <;> [rfl; (funext p; exact unmap_proc_update u.proc e.dest _ _ p); rfl; rfl]

private lemma unmap_mTr.{w} {P S M V : Type*} [DecidableEq P] [DecidableEq M]
    {π : Protocol P S M V} {u u' : State P (ULift.{w} S) M V} {xl : List (Action P M V)}
    (hm : (uliftStateProtocol.{w} π).lts.MTr u xl u') :
    π.lts.MTr (unmapULiftState u) xl (unmapULiftState u') := by
  induction hm with
  | refl => exact LTS.MTr.refl
  | stepL htr _ ih => exact LTS.MTr.stepL (unmap_tr htr) ih

private lemma implementsAtomicRegister_uliftState.{w} {P S M V : Type*}
    [Fintype P] [DecidableEq P] [DecidableEq M]
    {π : Protocol P S M V} {v₀ : V} {t : ℕ}
    (h : π.ImplementsAtomicRegister v₀ t) :
    (uliftStateProtocol.{w} π).ImplementsAtomicRegister v₀ t where
  linearizable u hr := by
    obtain ⟨xl, hxl⟩ := hr
    exact h.linearizable (unmapULiftState u) ⟨xl, unmap_mTr hxl⟩
  terminates F hF ss xs ha k i hi hc := by
    obtain ⟨h0, hexec, hfair⟩ := ha
    let ss' : ωSequence (State P S M V) := ss.map unmapULiftState
    have ha' : π.AdmissibleRun F ss' xs :=
      ⟨by simp [ss', h0, unmapULiftState, Protocol.start, uliftStateProtocol],
       fun n => unmap_tr (hexec n),
       fun e hd n hm => hfair e hd n hm⟩
    exact h.terminates F hF ss' xs ha' k i hi hc

/-- **Resilience characterization for asynchronous linearizable atomic registers**: over a finite
process set `P` and nontrivial value domain `V`, a deterministic asynchronous message-passing
protocol implementing a `t`-fault wait-free linearizable atomic register initialized to `v₀`
exists if and only if `Fintype.card P ≤ 1 ∨ 2 * t < Fintype.card P`:

* for `Fintype.card P ≤ 1`, `localRegisterProtocol` executes locally in zero messages;
* for `2 * t < Fintype.card P`, `abdProtocol` provides sufficiency via `(n - t)`-cardinality
  envelope quorums and idle-only invocations (an independent specialization **after**
  [LynchShvartsman1997], §4.1–4.2 and [AttiyaBarNoyDolev1995], §4, pairing `abd_linearizable` with
  `abd_terminates`);
* for `2 ≤ Fintype.card P ≤ 2 * t`, `Protocol.not_implementsAtomicRegister` proves impossibility
  by two-group partition replay (motivated by [AttiyaBarNoyDolev1995], §1, p. 127). -/
theorem exists_linearizableRegister_iff.{u, v} (P : Type u) (V : Type v) [Fintype P] [DecidableEq P]
    [Nontrivial V] (v₀ : V) (t : ℕ) :
    (∃ (S M : Type (max u v)) (_ : DecidableEq M) (π : Protocol P S M V),
      π.ImplementsAtomicRegister v₀ t) ↔
      Fintype.card P ≤ 1 ∨ 2 * t < Fintype.card P := by
  constructor
  · rintro ⟨S, M, _, π, hImpl⟩
    by_contra hnot
    exact π.not_implementsAtomicRegister (by omega) (by omega) v₀ hImpl
  · rintro (hle1 | h2t)
    · exact ⟨ULift.{u} V, PUnit.{max u v + 1}, inferInstance,
        uliftStateProtocol.{u} (localRegisterProtocol.{u, v, max u v} P V v₀),
        implementsAtomicRegister_uliftState.{u}
          (implementsAtomicRegister_local_of_card_le_one hle1 v₀ t)⟩
    · classical
      let e : P ≃ Fin (Fintype.card P) := Fintype.equivFin P
      let : LinearOrder P := LinearOrder.lift' e e.injective
      let : DecidableEq V := Classical.decEq V
      exact ⟨ABDState P V, ABDMsg P V, inferInstance, abdProtocol P V v₀ t,
        implementsAtomicRegister_abd h2t v₀⟩

end Cslib.Distributed.ABD
