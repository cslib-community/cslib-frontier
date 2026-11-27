/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.VectorClock.Basic
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Monotone.Basic

/-!
# Lamport scalar clocks and Mattern vector clocks

This module formalizes operational logical clocks over causally well-formed asynchronous
message-passing executions (`Cslib.Distributed.VectorClock.Execution`):

1. **Lamport scalar clocks** ([Lamport1978]): each process maintains a scalar `ℕ` counter,
   stepping to `L p + 1` on local/send events and `max (L p) L_msg + 1` upon message receipt. We
   prove strict causal monotonicity (`lamportClock_strictMono`), show that breaking timestamp ties
   by `[LinearOrder P]` yields a strict total order extending `HappensBefore`
   (`instIsStrictTotalOrderLamportTotalOrder`, `happensBefore_imp_lamportTotalOrder`), and prove
   **scalar incompleteness** (`not_exists_1d_characterization`): whenever `2 ≤ Fintype.card P`,
   there exists a valid execution on `P` whose causal order embeds into *no* `LinearOrder α`.

2. **Mattern vector clocks** ([Mattern1989], §§7–8; see also [Fidge1988] for the asynchronous
   sender-increment variant): each process maintains `Cslib.Distributed.VectorClock P := P → ℕ`,
   taking coordinatewise `⊔` upon message receipt and incrementing its own coordinate at every step
   (`Execution.vc`; in contrast, [Fidge1988]'s asynchronous Rule RA4 additionally increments the
   sender's coordinate on receive so its single-coordinate test uses `<` instead of `≤`). We prove:
   * **Exact order-isomorphism** (`happensBeforeLe_iff_vc_le`, `happensBefore_iff_vc_lt`):
     `e₁ ≼ e₂ ↔ E.vc e₁ ≤ E.vc e₂` and `e₁ ≺ e₂ ↔ E.vc e₁ < E.vc e₂`,
   * **Single-coordinate comparison of given timestamps** (`happensBeforeLe_iff_coord_le`,
     `happensBefore_iff_coord_le`): `e₁ ≼ e₂ ↔ E.vc e₁ e₁.actor ≤ E.vc e₂ e₁.actor`, and for
     `e₁ ≠ e₂`, `e₁ ≺ e₂ ↔ E.vc e₁ e₁.actor ≤ E.vc e₂ e₁.actor`,
   * **Exact concurrency detection** (`concurrent_iff_vc_incomparable`), and
   * **Mattern's frontier cut characterization** (`isConsistentCut_cutOfFrontier_iff`): the cut
     induced by per-process frontier events `frontier : P → E.Event` is consistent iff every
     process's own coordinate is maximized at its own frontier event
     (`∀ p q, E.vc (frontier q) p ≤ E.vc (frontier p) p`).

## Main definitions

* `Cslib.Distributed.VectorClock`: `P`-indexed `ℕ` timestamp vector `P → ℕ`.
* `Cslib.Distributed.VectorClock.Execution.lamportClock`: Lamport scalar timestamp `E.Event → ℕ`.
* `Cslib.Distributed.VectorClock.Execution.lamportTotalOrder`: tie-broken strict total order on
  `E.Event` extending `HappensBefore`.
* `Cslib.Distributed.VectorClock.Execution.vc`: Mattern vector timestamp `E.Event → VectorClock P`.
* `Cslib.Distributed.VectorClock.Execution.cutOfFrontier`: global event prefix induced by a
  per-process frontier `P → E.Event`.

## Main results

* `Cslib.Distributed.VectorClock.Execution.lamportClock_strictMono`: `e₁ ≺ e₂ →
  E.lamportClock e₁ < E.lamportClock e₂`.
* `Cslib.Distributed.VectorClock.Execution.instIsStrictTotalOrderLamportTotalOrder`,
  `Cslib.Distributed.VectorClock.Execution.happensBefore_imp_lamportTotalOrder`:
  `lamportTotalOrder` is a strict total order extending `HappensBefore`.
* `Cslib.Distributed.VectorClock.not_exists_1d_characterization`: for `2 ≤ Fintype.card P`, no
  single `LinearOrder`-valued clock characterizes `HappensBeforeLe` across executions on `P`.
* `Cslib.Distributed.VectorClock.Execution.happensBeforeLe_iff_coord_le`,
  `Cslib.Distributed.VectorClock.Execution.happensBefore_iff_coord_le`: causality
  characterization by single-coordinate comparison of given timestamps at `e₁.actor`.
* `Cslib.Distributed.VectorClock.Execution.happensBeforeLe_iff_vc_le`,
  `Cslib.Distributed.VectorClock.Execution.happensBefore_iff_vc_lt`: exact order-isomorphism between
  happens-before and the product order on `VectorClock P`.
* `Cslib.Distributed.VectorClock.Execution.concurrent_iff_vc_incomparable`: exact concurrency
  detection from vector-clock incomparability.
* `Cslib.Distributed.VectorClock.Execution.isConsistentCut_cutOfFrontier_iff`: Mattern's
  owner-maximum frontier criterion for consistent cuts.

## References

* [C. J. Fidge, *Timestamps in Message-Passing Systems That Preserve the Partial
  Ordering*][Fidge1988]
* [L. Lamport, *Time, Clocks, and the Ordering of Events in a Distributed System*][Lamport1978]
* [F. Mattern, *Virtual Time and Global States of Distributed Systems*][Mattern1989]
-/

public section

namespace Cslib.Distributed

universe u v

/-- A vector timestamp over process type `P`, equipped with Mathlib's coordinatewise product
`PartialOrder` and `SemilatticeSup` (`⊔`). -/
abbrev VectorClock (P : Type u) : Type u := P → ℕ

namespace VectorClock

/-- Decidability of strict vector-clock comparison over a finite process set. -/
scoped instance instDecidableLTVectorClock {P : Type u} [Fintype P] :
    DecidableLT (VectorClock P) :=
  decidableLTOfDecidableLE

namespace Execution

variable {P : Type u}

/-! ### Shared execution clock scanner -/

/-- Single step of `scanSteps`, advancing `(hist, loc)` across `E.steps[k]`. -/
@[expose] def scanStepAux [DecidableEq P] {α : Type*} (E : Execution P)
    (next : P → α → Option α → α) (k : ℕ) (hk : k < E.steps.length)
    (hist : List α) (loc : P → α) : List α × (P → α) :=
  let st := E.steps[k]
  let msg? := match st with
    | .recv _ sIdx => hist[sIdx]?
    | _ => none
  let val := next st.actor (loc st.actor) msg?
  (hist ++ [val], Function.update loc st.actor val)

/-- Prefix scan over the first `k` steps of `E`, maintaining recorded step timestamps `List α` and
the per-process local clock `P → α`. Pattern-matching on the recursive pair and list forces kernel
WHNF evaluation once per step during `decide`. -/
@[expose] def scanSteps [DecidableEq P] {α : Type*} (E : Execution P) (init : P → α)
    (next : P → α → Option α → α) : ℕ → List α × (P → α)
  | 0 => ([], init)
  | k + 1 =>
    if hk : k < E.steps.length then
      match E.scanSteps init next k with
      | ([], loc) => E.scanStepAux next k hk [] loc
      | (hd :: tl, loc) => E.scanStepAux next k hk (hd :: tl) loc
    else
      E.scanSteps init next k

private theorem scanSteps_succ_of_lt [DecidableEq P] {α : Type*} (E : Execution P) (init : P → α)
    (next : P → α → Option α → α) {k : ℕ} (hk : k < E.steps.length) :
    E.scanSteps init next (k + 1) =
      E.scanStepAux next k hk (E.scanSteps init next k).1 (E.scanSteps init next k).2 := by
  simp only [scanSteps, hk, ↓reduceDIte]
  rcases E.scanSteps init next k with ⟨_ | _, _⟩ <;> rfl

private theorem length_scanSteps [DecidableEq P] {α : Type*} (E : Execution P) (init : P → α)
    (next : P → α → Option α → α) {k : ℕ} (hk : k ≤ E.steps.length) :
    (E.scanSteps init next k).1.length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [E.scanSteps_succ_of_lt init next (Nat.lt_of_succ_le hk)]
    simp [scanStepAux, ih (Nat.le_of_succ_le hk)]

private theorem scanSteps_fst_lt [DecidableEq P] {α : Type*} (E : Execution P) (init : P → α)
    (next : P → α → Option α → α) {i k : ℕ} (hik : i < k) (hk : k ≤ E.steps.length) :
    (E.scanSteps init next k).1[i]? = (E.scanSteps init next (i + 1)).1[i]? := by
  induction k with
  | zero => omega
  | succ k ih =>
    have hlt : k < E.steps.length := Nat.lt_of_succ_le hk
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hik) with hik' | rfl
    · rw [E.scanSteps_succ_of_lt init next hlt, scanStepAux,
        List.getElem?_append_left (by simp [E.length_scanSteps init next hlt.le, hik']),
        ih hik' hlt.le]
    · rfl

/-- Evaluate a `scanSteps` clock at event `e` (running the prefix up to `e.idx + 1`). -/
@[expose] def evalScan [DecidableEq P] {α : Type*} (E : Execution P) (defaultVal : α)
    (init : P → α) (next : P → α → Option α → α) (e : E.Event) : α :=
  ((E.scanSteps init next (e.idx.val + 1)).1[e.idx.val]?).getD defaultVal

private theorem scanSteps_fst_succ_self [DecidableEq P] {α : Type*} (E : Execution P)
    (init : P → α) (next : P → α → Option α → α) (e : E.Event) :
    (E.scanSteps init next (e.idx.val + 1)).1[e.idx.val]? =
      some (next e.actor ((E.scanSteps init next e.idx.val).2 e.actor)
        (match e.step with
          | .recv _ sIdx => (E.scanSteps init next e.idx.val).1[sIdx]?
          | _ => none)) := by
  have hlen : (E.scanSteps init next e.idx.val).1.length = e.idx.val :=
    E.length_scanSteps init next e.idx.isLt.le
  rw [E.scanSteps_succ_of_lt init next e.idx.isLt, scanStepAux,
    List.getElem?_append_right hlen.le, hlen, Nat.sub_self, List.getElem?_cons_zero]
  rfl

private theorem evalScan_step_eq [DecidableEq P] {α : Type*} (E : Execution P)
    (defaultVal : α) (init : P → α) (next : P → α → Option α → α) (e : E.Event) :
    E.evalScan defaultVal init next e =
      next e.actor ((E.scanSteps init next e.idx.val).2 e.actor)
        (match e.step with
          | .recv _ sIdx => (E.scanSteps init next e.idx.val).1[sIdx]?
          | _ => none) := by
  rw [evalScan, E.scanSteps_fst_succ_self init next e, Option.getD_some]

private theorem scanSteps_fst_eq_some_evalScan [DecidableEq P] {α : Type*} (E : Execution P)
    (defaultVal : α) (init : P → α) (next : P → α → Option α → α) {k : ℕ}
    (hk : k ≤ E.steps.length) (e : E.Event) (he : e.idx.val < k) :
    (E.scanSteps init next k).1[e.idx.val]? = some (E.evalScan defaultVal init next e) := by
  rw [E.scanSteps_fst_lt init next he hk, E.scanSteps_fst_succ_self init next e,
    E.evalScan_step_eq defaultVal init next e]

private theorem evalScan_of_recv [DecidableEq P] {α : Type*} (E : Execution P)
    (defaultVal : α) (init : P → α) (next : P → α → Option α → α)
    {eSend eRecv : E.Event} {p : P} (hrecv : eRecv.step = .recv p eSend.idx.val) :
    E.evalScan defaultVal init next eRecv =
      next eRecv.actor ((E.scanSteps init next eRecv.idx.val).2 eRecv.actor)
        (some (E.evalScan defaultVal init next eSend)) := by
  have hlt : eSend.idx.val < eRecv.idx.val :=
    E.causalStep_idx_lt (.inr (E.messageOrder_of_recv hrecv))
  simp only [E.evalScan_step_eq defaultVal init next eRecv, hrecv,
    E.scanSteps_fst_eq_some_evalScan defaultVal init next eRecv.idx.isLt.le eSend hlt]

private theorem scanSteps_snd_succ_self [DecidableEq P] {α : Type*} (E : Execution P)
    (defaultVal : α) (init : P → α) (next : P → α → Option α → α) (e : E.Event) :
    (E.scanSteps init next (e.idx.val + 1)).2 e.actor =
      E.evalScan defaultVal init next e := by
  rw [E.evalScan_step_eq defaultVal init next e, E.scanSteps_succ_of_lt init next e.idx.isLt]
  simp only [scanStepAux, Event.actor, Event.step, Fin.getElem_fin, Function.update_self]; rfl

private theorem scanSteps_snd_mono [DecidableEq P] {α : Type*} [Preorder α] (E : Execution P)
    (init : P → α) (next : P → α → Option α → α)
    (hstep : ∀ p c m, c ≤ next p c m) {k₁ k₂ : ℕ} (hk₁₂ : k₁ ≤ k₂)
    (hk₂ : k₂ ≤ E.steps.length) (q : P) :
    (E.scanSteps init next k₁).2 q ≤ (E.scanSteps init next k₂).2 q := by
  induction k₂ with
  | zero => obtain rfl := Nat.eq_zero_of_le_zero hk₁₂; exact le_rfl
  | succ k ih =>
    rcases Nat.lt_or_eq_of_le hk₁₂ with hlt | rfl
    · refine (ih (Nat.le_of_lt_succ hlt) (Nat.le_of_succ_le hk₂)).trans ?_
      rw [E.scanSteps_succ_of_lt init next (Nat.lt_of_succ_le hk₂)]
      by_cases hq : q = (E.steps[k]).actor <;> simp [scanStepAux, hstep, hq]
    · exact le_rfl

private theorem evalScan_le_snd_of_lt [DecidableEq P] {α : Type*} [Preorder α] (E : Execution P)
    (defaultVal : α) (init : P → α) (next : P → α → Option α → α)
    (hstep : ∀ p c m, c ≤ next p c m) {x : E.Event} {k : ℕ}
    (hxk : x.idx.val < k) (hk : k ≤ E.steps.length) :
    E.evalScan defaultVal init next x ≤ (E.scanSteps init next k).2 x.actor := by
  rw [← E.scanSteps_snd_succ_self defaultVal init next x]
  exact E.scanSteps_snd_mono init next hstep hxk hk x.actor

private theorem scanSteps_snd_provenance [DecidableEq P] {α : Type*} (E : Execution P)
    (defaultVal : α) (init : P → α) (next : P → α → Option α → α) {k : ℕ}
    (hk : k ≤ E.steps.length) (q : P) :
    (E.scanSteps init next k).2 q = init q ∨
      ∃ x : E.Event, x.idx.val < k ∧ x.actor = q ∧
        (E.scanSteps init next k).2 q = E.evalScan defaultVal init next x := by
  induction k with
  | zero => exact .inl rfl
  | succ k ih =>
    have hk_lt : k < E.steps.length := Nat.lt_of_succ_le hk
    let ek : E.Event := ⟨⟨k, hk_lt⟩⟩
    by_cases hq : q = ek.actor
    · exact .inr ⟨ek, Nat.lt_succ_self k, hq.symm,
        hq ▸ E.scanSteps_snd_succ_self defaultVal init next ek⟩
    · have hq' : q ≠ (E.steps[k]).actor := hq
      simp only [E.scanSteps_succ_of_lt init next hk_lt, scanStepAux, Function.update_of_ne hq']
      exact (ih hk_lt.le).imp_right fun ⟨x, hxk, hact, heq⟩ =>
        ⟨x, Nat.lt_succ_of_lt hxk, hact, heq⟩

/-! ### Lamport scalar clocks ([Lamport1978]) -/

/-- Local transition rule for Lamport's scalar logical clock. -/
@[expose] def lamportNext (_ : P) (cur : ℕ) (msg? : Option ℕ) : ℕ :=
  max cur (msg?.getD 0) + 1

/-- Lamport's scalar logical clock `E.Event → ℕ` ([Lamport1978]): each local/send event receives
`L p + 1` and each receive event receives `max (L p) L_msg + 1`. -/
@[expose] def lamportClock [DecidableEq P] (E : Execution P) (e : E.Event) : ℕ :=
  E.evalScan 0 (fun _ => 0) lamportNext e

/-- Every Lamport timestamp is strictly positive (`1 ≤ E.lamportClock e`). -/
theorem lamportClock_pos [DecidableEq P] (E : Execution P) (e : E.Event) :
    0 < E.lamportClock e := by
  rw [lamportClock, E.evalScan_step_eq]
  simp [lamportNext]

private theorem causalStep_imp_lamportClock_lt [DecidableEq P] {E : Execution P}
    {e₁ e₂ : E.Event} (h : E.CausalStep e₁ e₂) :
    E.lamportClock e₁ < E.lamportClock e₂ := by
  have hstep : ∀ (p : P) (c : ℕ) (m : Option ℕ), c ≤ lamportNext p c m := fun _ _ _ => by
    simp only [lamportNext]; omega
  rcases h with ⟨hact, hlt⟩ | hmsg
  · have hle : E.lamportClock e₁ ≤
        (E.scanSteps (fun _ => 0) lamportNext e₂.idx.val).2 e₁.actor :=
      E.evalScan_le_snd_of_lt 0 (fun _ => 0) lamportNext hstep hlt e₂.idx.isLt.le
    rw [hact] at hle
    conv_rhs => rw [lamportClock, E.evalScan_step_eq 0 (fun _ => 0) lamportNext e₂]
    simp only [lamportNext]
    omega
  · conv_rhs => rw [lamportClock, E.evalScan_of_recv 0 (fun _ => 0) lamportNext hmsg]
    simp only [lamportNext, Option.getD_some]
    exact lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _)

/-- **Strict causal monotonicity of Lamport clocks** ([Lamport1978]):
`e₁ ≺ e₂ → E.lamportClock e₁ < E.lamportClock e₂`. -/
theorem lamportClock_strictMono [DecidableEq P] (E : Execution P) :
    StrictMono E.lamportClock := by
  intro e₁ e₂ hhb
  change E.HappensBefore e₁ e₂ at hhb
  induction hhb with
  | single hs => exact causalStep_imp_lamportClock_lt hs
  | tail _ hs ih => exact ih.trans (causalStep_imp_lamportClock_lt hs)

/-- Reflexive causal monotonicity of Lamport clocks (`e₁ ≼ e₂ → E.lamportClock e₁ ≤
E.lamportClock e₂`). -/
theorem lamportClock_mono [DecidableEq P] (E : Execution P) :
    Monotone E.lamportClock :=
  E.lamportClock_strictMono.monotone

/-- Distinct events on the same process never share a Lamport timestamp, so `(lamportClock, actor)`
uniquely identifies every event. -/
theorem lamportClock_actor_injective [DecidableEq P] (E : Execution P)
    {e₁ e₂ : E.Event} (hc : E.lamportClock e₁ = E.lamportClock e₂)
    (ha : e₁.actor = e₂.actor) : e₁ = e₂ := by
  rcases lt_trichotomy e₁.idx e₂.idx with hlt | heq | hgt
  · exact absurd (E.lamportClock_strictMono (E.programOrder_happensBefore ha hlt)) (by omega)
  · exact Event.ext heq
  · exact absurd (E.lamportClock_strictMono (E.programOrder_happensBefore ha.symm hgt)) (by omega)

/-- Lamport's total ordering of events ([Lamport1978]): order by scalar timestamp and break ties
using a linear order on process identifiers. -/
@[expose] def lamportTotalOrder [LinearOrder P] (E : Execution P) (e₁ e₂ : E.Event) : Prop :=
  E.lamportClock e₁ < E.lamportClock e₂ ∨
    (E.lamportClock e₁ = E.lamportClock e₂ ∧ e₁.actor < e₂.actor)

instance instDecidableRelLamportTotalOrder [LinearOrder P] (E : Execution P) :
    DecidableRel E.lamportTotalOrder :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Lamport's tie-broken event relation is a strict total order on `E.Event`. -/
instance instIsStrictTotalOrderLamportTotalOrder [LinearOrder P] (E : Execution P) :
    IsStrictTotalOrder E.Event E.lamportTotalOrder where
  irrefl e := by
    rintro (hlt | ⟨_, hlt⟩)
    · exact Nat.lt_irrefl _ hlt
    · exact lt_irrefl _ hlt
  trans e₁ e₂ e₃ h₁₂ h₂₃ := by
    rcases h₁₂ with hlt₁ | ⟨heq₁, ha₁⟩ <;> rcases h₂₃ with hlt₂ | ⟨heq₂, ha₂⟩
    · exact .inl (hlt₁.trans hlt₂)
    · exact .inl (heq₂ ▸ hlt₁)
    · exact .inl (heq₁.symm ▸ hlt₂)
    · exact .inr ⟨heq₁.trans heq₂, ha₁.trans ha₂⟩
  trichotomous e₁ e₂ h₁₂ h₂₁ := by
    have hc : E.lamportClock e₁ = E.lamportClock e₂ := by
      rcases lt_trichotomy (E.lamportClock e₁) (E.lamportClock e₂) with hlt | heq | hgt
      · exact absurd (.inl hlt) h₁₂
      · exact heq
      · exact absurd (.inl hgt) h₂₁
    have ha : e₁.actor = e₂.actor := by
      rcases lt_trichotomy e₁.actor e₂.actor with ha | haeq | ha'
      · exact absurd (.inr ⟨hc, ha⟩) h₁₂
      · exact haeq
      · exact absurd (.inr ⟨hc.symm, ha'⟩) h₂₁
    exact E.lamportClock_actor_injective hc ha

/-- `lamportTotalOrder` is a linear extension of `HappensBefore`. -/
theorem happensBefore_imp_lamportTotalOrder [LinearOrder P] {E : Execution P}
    {e₁ e₂ : E.Event} (h : E.HappensBefore e₁ e₂) : E.lamportTotalOrder e₁ e₂ :=
  .inl (E.lamportClock_strictMono h)

end Execution

/-- **Scalar incompleteness of one-dimensional clocks** (original two-process communication-free
counterexample witnessing [Lamport1978], p. 560): whenever `2 ≤ Fintype.card P`, there is a
causally well-formed execution on `P` admitting *no* order-embedding into any `LinearOrder α`. -/
theorem not_exists_1d_characterization {P : Type u} [Fintype P] (hP : 2 ≤ Fintype.card P) :
    ∃ E : Execution P, ∀ {α : Type v} [LinearOrder α] (f : E.Event → α),
      ¬ ∀ e₁ e₂ : E.Event, E.HappensBeforeLe e₁ e₂ ↔ f e₁ ≤ f e₂ := by
  obtain ⟨p₀, p₁, hpne⟩ := Fintype.one_lt_card_iff_nontrivial.mp (by omega : 1 < Fintype.card P)
  let E : Execution P := Execution.ofInternal [p₀, p₁]
  refine ⟨E, fun {α} _ f hf => ?_⟩
  let e₀ : E.Event := ⟨⟨0, Nat.zero_lt_succ 1⟩⟩
  let e₁ : E.Event := ⟨⟨1, Nat.lt_succ_self 1⟩⟩
  rcases le_total (f e₀) (f e₁) with hle | hge
  · rcases Execution.ofInternal_happensBeforeLe_iff.mp ((hf e₀ e₁).mpr hle) with heq | ⟨hact, _⟩
    · exact Nat.zero_ne_one (congrArg (fun e => e.idx.val) heq)
    · exact hpne hact
  · rcases Execution.ofInternal_happensBeforeLe_iff.mp ((hf e₁ e₀).mpr hge) with heq | ⟨hact, _⟩
    · exact Nat.one_ne_zero (congrArg (fun e => e.idx.val) heq)
    · exact hpne hact.symm

namespace Execution

variable {P : Type u}

/-! ### Mattern vector clocks ([Mattern1989]; see also [Fidge1988]) -/

/-- Local transition rule for Mattern vector clocks ([Mattern1989], §7): coordinatewise `⊔` with
the incoming message vector (if any), followed by incrementing the executing process's own entry. -/
@[expose] def vcNext [DecidableEq P] (p : P) (cur : VectorClock P)
    (msg? : Option (VectorClock P)) : VectorClock P :=
  let merged := cur ⊔ msg?.getD 0
  Function.update merged p (merged p + 1)

/-- Mattern vector clock `E.Event → VectorClock P` ([Mattern1989], §7; cf. [Fidge1988], Rules
RA1–RA4, which additionally increment the sender's entry upon receive). -/
@[expose] def vc [DecidableEq P] (E : Execution P) (e : E.Event) : VectorClock P :=
  E.evalScan 0 (fun _ => 0) vcNext e

private theorem le_vcNext [DecidableEq P] (p : P) (cur : VectorClock P)
    (msg? : Option (VectorClock P)) : cur ≤ vcNext p cur msg? := fun q => by
  rcases eq_or_ne q p with rfl | hq
  · simp only [vcNext, Function.update_self, Pi.sup_apply]; omega
  · simp [vcNext, Function.update_of_ne hq]

/-- At every event `e`, its executing process's own vector-clock entry is strictly positive. -/
theorem vc_actor_pos [DecidableEq P] (E : Execution P) (e : E.Event) :
    0 < E.vc e e.actor := by
  rw [vc, E.evalScan_step_eq]
  simp only [vcNext, Function.update_self]; omega

/-- Along events of the same process, that process's vector-clock coordinate is strictly
increasing. -/
theorem vc_actor_strictMono_of_sameActor [DecidableEq P] {E : Execution P} {e₁ e₂ : E.Event}
    (hact : e₁.actor = e₂.actor) (hlt : e₁.idx < e₂.idx) :
    E.vc e₁ e₁.actor < E.vc e₂ e₂.actor := by
  have hcoord : E.vc e₁ e₁.actor ≤
      (E.scanSteps (fun _ => 0) vcNext e₂.idx.val).2 e₂.actor e₂.actor :=
    hact ▸ E.evalScan_le_snd_of_lt 0 (fun _ => 0) vcNext le_vcNext hlt e₂.idx.isLt.le e₁.actor
  have heq := congrFun (E.evalScan_step_eq 0 (fun _ => 0) vcNext e₂) e₂.actor
  change E.vc e₂ e₂.actor = _ at heq
  simp only [vcNext, Function.update_self, Pi.sup_apply] at heq
  omega

private theorem causalStep_imp_vc_le [DecidableEq P] {E : Execution P} {e₁ e₂ : E.Event}
    (h : E.CausalStep e₁ e₂) : E.vc e₁ ≤ E.vc e₂ := by
  rcases h with ⟨hact, hlt⟩ | hmsg
  · have hle : E.vc e₁ ≤ (E.scanSteps (fun _ => 0) vcNext e₂.idx.val).2 e₁.actor :=
      E.evalScan_le_snd_of_lt 0 (fun _ => 0) vcNext le_vcNext hlt e₂.idx.isLt.le
    rw [hact] at hle
    conv_rhs => rw [vc, E.evalScan_step_eq 0 (fun _ => 0) vcNext e₂]
    exact hle.trans (le_vcNext _ _ _)
  · conv_rhs => rw [vc, E.evalScan_of_recv 0 (fun _ => 0) vcNext hmsg]
    intro q
    by_cases hq : q = e₂.actor
    · simp only [hq, vc, vcNext, Option.getD_some, Function.update_self, Pi.sup_apply]; omega
    · simp only [vc, vcNext, Option.getD_some, Function.update_of_ne hq, Pi.sup_apply]; omega

/-- Vector clocks are monotone with respect to `HappensBeforeLe`. -/
theorem vc_mono [DecidableEq P] (E : Execution P) : Monotone E.vc := by
  intro e₁ e₂ hle
  change E.HappensBeforeLe e₁ e₂ at hle
  induction hle with
  | refl => exact le_rfl
  | tail _ hs ih => exact ih.trans (causalStep_imp_vc_le hs)

/-- **Provenance invariant of vector clocks**: every nonzero coordinate `E.vc e p` equals `E.vc x p`
for some causal predecessor `x ≼ e` executing on process `p`. -/
private theorem vc_eq_zero_or_exists_le [DecidableEq P] (E : Execution P) :
    ∀ (e : E.Event) (p : P),
      E.vc e p = 0 ∨ ∃ x : E.Event, x.actor = p ∧ E.HappensBeforeLe x e ∧ E.vc x p = E.vc e p := by
  intro ⟨⟨j, hj⟩⟩
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    let ej : E.Event := ⟨⟨j, hj⟩⟩
    intro p
    by_cases hp : p = ej.actor
    · exact .inr ⟨ej, hp.symm, E.happensBeforeLe_refl ej, rfl⟩
    · have hloc_prov :
          (E.scanSteps (fun _ => 0) vcNext j).2 ej.actor p = 0 ∨
            ∃ x : E.Event, x.actor = p ∧ E.HappensBeforeLe x ej ∧
              E.vc x p = (E.scanSteps (fun _ => 0) vcNext j).2 ej.actor p := by
        rcases E.scanSteps_snd_provenance 0 (fun _ => 0) vcNext hj.le ej.actor with h0 |
          ⟨y, hyj, hyact, hyeq⟩
        · exact .inl (congrFun h0 p)
        · change _ = E.vc y at hyeq
          have hyej : E.HappensBefore y ej := E.programOrder_happensBefore hyact hyj
          rcases ih y.idx.val hyj y.idx.isLt p with hz0 | ⟨x, hxact, hxy, hxeq⟩
          · exact .inl ((congrFun hyeq p).trans hz0)
          · exact .inr ⟨x, hxact, hxy.trans hyej.happensBeforeLe, by rw [hyeq, hxeq]⟩
      cases hstep : ej.step with
      | internal _ | send _ _ =>
        have heq : E.vc ej p = (E.scanSteps (fun _ => 0) vcNext j).2 ej.actor p := by
          rw [vc, E.evalScan_step_eq]
          simp only [ej, hstep, vcNext, Function.update_of_ne hp, Option.getD_none, Pi.sup_apply,
            Pi.zero_apply, max_eq_left (Nat.zero_le _)]
        rwa [heq]
      | recv q sIdx =>
        obtain ⟨eSend, hval, hlt, _, _⟩ := E.recv_sendEvent hstep
        have hrecv : ej.step = .recv q eSend.idx.val := hval.symm ▸ hstep
        have hm : E.vc ej p = (E.scanSteps (fun _ => 0) vcNext j).2 ej.actor p ⊔ E.vc eSend p := by
          rw [vc, E.evalScan_of_recv 0 (fun _ => 0) vcNext hrecv]
          simp only [ej, vc, vcNext, Function.update_of_ne hp, Option.getD_some, Pi.sup_apply]
        rcases max_choice
            ((E.scanSteps (fun _ => 0) vcNext j).2 ej.actor p) (E.vc eSend p) with hmax | hmax <;>
          rw [hm, hmax]
        · exact hloc_prov
        · have hmsg : E.HappensBefore eSend ej :=
            E.messageOrder_happensBefore (E.messageOrder_of_recv hrecv)
          rcases ih eSend.idx.val hlt eSend.idx.isLt p with hz0 | ⟨x, hxact, hxs, hxeq⟩
          · exact .inl hz0
          · exact .inr ⟨x, hxact, hxs.trans hmsg.happensBeforeLe, hxeq⟩

/-- **Single-coordinate comparison of given timestamps (`≼`)** ([Mattern1989], §8, Theorem 11):
`e₁ ≼ e₂` iff `e₁`'s own process coordinate in `vc e₁` is at most that in `vc e₂`. -/
theorem happensBeforeLe_iff_coord_le [DecidableEq P] {E : Execution P} {e₁ e₂ : E.Event} :
    E.HappensBeforeLe e₁ e₂ ↔ E.vc e₁ e₁.actor ≤ E.vc e₂ e₁.actor := by
  refine ⟨fun hle => E.vc_mono hle e₁.actor, fun hcoord => ?_⟩
  rcases E.vc_eq_zero_or_exists_le e₂ e₁.actor with h0 | ⟨x, hxact, hxe₂, hxeq⟩
  · exact absurd (hcoord.trans_eq h0) (not_le_of_gt (E.vc_actor_pos e₁))
  · refine (E.programOrder_happensBeforeLe hxact.symm (le_of_not_gt fun hlt => ?_)).trans hxe₂
    have hvc_lt := hxact ▸ E.vc_actor_strictMono_of_sameActor hxact hlt
    omega

/-- **Single-coordinate comparison of given timestamps (`≺`)** ([Mattern1989], §8, Theorem 11):
for distinct events `e₁ ≠ e₂`, `e₁ ≺ e₂` iff `E.vc e₁ e₁.actor ≤ E.vc e₂ e₁.actor`. -/
theorem happensBefore_iff_coord_le [DecidableEq P] {E : Execution P} {e₁ e₂ : E.Event}
    (hne : e₁ ≠ e₂) :
    E.HappensBefore e₁ e₂ ↔ E.vc e₁ e₁.actor ≤ E.vc e₂ e₁.actor := by
  rw [← happensBeforeLe_iff_coord_le, happensBeforeLe_iff]
  exact ⟨fun h => .inr h, fun h => h.resolve_left hne⟩

/-- **Vector-clock order-isomorphism (`≼`)** ([Mattern1989], §8, Theorem 10):
`e₁ ≼ e₂ ↔ E.vc e₁ ≤ E.vc e₂`. -/
theorem happensBeforeLe_iff_vc_le [DecidableEq P] {E : Execution P} {e₁ e₂ : E.Event} :
    E.HappensBeforeLe e₁ e₂ ↔ E.vc e₁ ≤ E.vc e₂ :=
  ⟨fun h => E.vc_mono h, fun h => happensBeforeLe_iff_coord_le.mpr (h e₁.actor)⟩

/-- Vector timestamps uniquely identify events (`Function.Injective E.vc`). -/
theorem vc_injective [DecidableEq P] (E : Execution P) : Function.Injective E.vc :=
  fun _ _ heq => le_antisymm (happensBeforeLe_iff_vc_le.mpr heq.le)
    (happensBeforeLe_iff_vc_le.mpr heq.ge)

/-- **Vector-clock strict order-isomorphism (`≺`)** ([Mattern1989], §8, Theorem 10):
`e₁ ≺ e₂ ↔ E.vc e₁ < E.vc e₂`. -/
theorem happensBefore_iff_vc_lt [DecidableEq P] {E : Execution P} {e₁ e₂ : E.Event} :
    E.HappensBefore e₁ e₂ ↔ E.vc e₁ < E.vc e₂ := by
  change (e₁ < e₂) ↔ E.vc e₁ < E.vc e₂
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, event_le_iff, event_le_iff,
    happensBeforeLe_iff_vc_le, happensBeforeLe_iff_vc_le]

/-- **Exact concurrency detection**: two events are causally concurrent iff their vector timestamps
are coordinatewise incomparable. -/
theorem concurrent_iff_vc_incomparable [DecidableEq P] {E : Execution P} {e₁ e₂ : E.Event} :
    E.Concurrent e₁ e₂ ↔ ¬ E.vc e₁ ≤ E.vc e₂ ∧ ¬ E.vc e₂ ≤ E.vc e₁ := by
  rw [Concurrent, happensBeforeLe_iff_vc_le, happensBeforeLe_iff_vc_le]

/-! ### Mattern's frontier vector-clock criterion for consistent cuts -/

/-- The cut induced by a per-process frontier `frontier : P → E.Event`, containing every event `e`
occurring on its process at or before `frontier e.actor`. -/
@[expose] def cutOfFrontier (E : Execution P) (frontier : P → E.Event) : Finset E.Event :=
  Finset.univ.filter fun e => e.idx ≤ (frontier e.actor).idx

@[simp] theorem mem_cutOfFrontier {E : Execution P} {frontier : P → E.Event} {e : E.Event} :
    e ∈ E.cutOfFrontier frontier ↔ e.idx ≤ (frontier e.actor).idx := by
  simp [cutOfFrontier]

/-- **Mattern's frontier cut characterization** ([Mattern1989]): when `frontier p` is an event on
process `p` for every `p : P`, `E.cutOfFrontier frontier` is a consistent cut iff every process's
own vector-clock coordinate across the frontier is maximized at its own frontier event
(`∀ p q, E.vc (frontier q) p ≤ E.vc (frontier p) p`). -/
theorem isConsistentCut_cutOfFrontier_iff [DecidableEq P] {E : Execution P}
    {frontier : P → E.Event} (hact : ∀ p : P, (frontier p).actor = p) :
    E.IsConsistentCut (E.cutOfFrontier frontier) ↔
      ∀ p q : P, E.vc (frontier q) p ≤ E.vc (frontier p) p := by
  constructor
  · intro hcut p q
    rcases E.vc_eq_zero_or_exists_le (frontier q) p with h0 | ⟨x, hxact, hxfq, hxeq⟩
    · omega
    · have hx_mem := hcut.mem_of_happensBeforeLe hxfq (by rw [mem_cutOfFrontier, hact q])
      rw [mem_cutOfFrontier, hxact] at hx_mem
      exact hxeq ▸ E.vc_mono (E.programOrder_happensBeforeLe (hxact.trans (hact p).symm) hx_mem) p
  · intro hmax e₁ e₂ hhb he₂
    rw [mem_cutOfFrontier] at he₂ ⊢
    have he₁_fq : E.HappensBeforeLe e₁ (frontier e₂.actor) :=
      hhb.happensBeforeLe.trans (E.programOrder_happensBeforeLe (hact e₂.actor).symm he₂)
    exact E.happensBeforeLe_idx_le (happensBeforeLe_iff_coord_le.mpr
      ((E.vc_mono he₁_fq e₁.actor).trans (hmax e₁.actor e₂.actor)))

end Execution

end VectorClock

end Cslib.Distributed
