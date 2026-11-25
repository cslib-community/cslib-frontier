/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.StableMatching.Incomplete.DeferredAcceptance
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Basic

/-!
# Blocking lemma, incentives, and comparative statics with incomplete lists

This module extends the blocking lemma and incentive theory of
`CslibFrontier.Algorithms.Lean.StableMatching.Blocking` and `Incentives` to one-to-one markets
with **strict, possibly incomplete preference lists and unequal sides** (`IncompleteInstance m n`),
without assuming preference lists are duplicate-free (`Nodup`).

1. **Blocking lemma (Hwang; [GaleSotomayor1985])**: `IncompleteInstance.exists_isBlockingPair_of_lt`
   generalizes the blocking lemma to arbitrary receiver-individually-rational partial matchings `μ`.
2. **Weak Pareto optimality & coalitional strategy-proofness ([DubinsFreedman1981]; [Roth1982])**:
   under proposer-proposing deferred acceptance, no coalition of proposers can misreport (including
   truncating lists or declaring new partners acceptable) so that every member gets a strictly
   preferred outcome under *any* stable matching of the reported market.
3. **Sharp Roth impossibility for incomplete lists ([Roth1982])**: with incomplete lists
   (allowing truncation), **no** stable partial matching mechanism is strategy-proof for both
   proposers and receivers whenever **`2 ≤ m ∧ 2 ≤ n`** — contrasting with the complete-list
   threshold `n ≥ 3` (`RothImpossibility.lean`). Conversely, when **`m ≤ 1 ∨ n ≤ 1`**,
   proposer-proposing (and receiver-proposing) deferred acceptance is strategy-proof for **both**
   sides.
4. **Entry comparative statics ([GaleSotomayor1985])**: adding a new receiver to a market leaves
   every original proposer weakly better off and every original receiver weakly worse off under
   **both** proposer-optimal (`deferredAcceptance`) and receiver-optimal
   (`receiverDeferredAcceptance`) deferred acceptance, with dual results for adding a proposer.

## Main definitions

* `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance.updatePropPref`,
  `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance.updateRecvPref`: single-agent
  misreports (allowing truncation and reordering).
* `Cslib.Algorithms.Lean.StableMatching.PartialMatchingMechanism`: direct mechanism returning a
  partial matching (`IncompleteInstance m n → PartialMatching m n`), with `IsStable`,
  `IsProposerStrategyProof`, and `IsReceiverStrategyProof`.
* `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance.ExtendsByReceiver`: witness that
  `I' : IncompleteInstance m (n + 1)` extends `I : IncompleteInstance m n` by one added receiver
  preserving existing receivers' lists and existing proposers' relative preferences over `Fin n`.

## Main results

* `IncompleteInstance.propRank_deferredAcceptance_eq_finalState`: exact rank equality
  (holds even if `propPref` contains repeated entries).
* `IncompleteInstance.exists_isBlockingPair_of_lt`: blocking lemma for incomplete lists and
  unequal sides.
* `IncompleteInstance.not_forall_propRank_lt_deferredAcceptance`: weak Pareto optimality for
  proposers (among receiver-individually-rational matchings).
* `IncompleteInstance.not_forall_mem_propRank_lt_of_isStable`: coalitional strategy-proofness of
  deferred acceptance ([DubinsFreedman1981]).
* `PartialMatchingMechanism.isProposerStrategyProof_deferredAcceptance`,
  `PartialMatchingMechanism.isReceiverStrategyProof_receiverDeferredAcceptance`: individual
  strategy-proofness with incomplete lists (including truncation).
* `PartialMatchingMechanism.not_isStable_and_strategyProof`: impossibility of a mutually
  strategy-proof stable mechanism for every `m ≥ 2, n ≥ 2`.
* `PartialMatchingMechanism.isReceiverStrategyProof_deferredAcceptance_of_le_one`: sharp converse
  when `m ≤ 1 ∨ n ≤ 1`.
* `IncompleteInstance.ExtendsByReceiver.deferredAcceptance_propRank_le`,
  `IncompleteInstance.ExtendsByReceiver.deferredAcceptance_recvRank_le`,
  `IncompleteInstance.ExtendsByReceiver.receiverDeferredAcceptance_recvRank_le`,
  `IncompleteInstance.ExtendsByReceiver.receiverDeferredAcceptance_propRank_le`: comparative
  statics under adding a receiver ([GaleSotomayor1985]).

## References

* [DubinsFreedman1981]
* [GaleSotomayor1985]
* [Roth1982]
* [RothSotomayor1990]
* [SchummerVohra2007]
-/

public section

namespace Cslib.Algorithms.Lean.StableMatching

namespace IncompleteInstance

variable {m n : ℕ} (I : IncompleteInstance m n)

/-! ### Misreports -/

/-- The instance in which proposer `p` reports list `l` (possibly truncated or reordered) and
everyone else reports truthfully. -/
@[expose] def updatePropPref (p : Fin m) (l : List (Fin n)) : IncompleteInstance m n :=
  ⟨Function.update I.propPref p l, I.recvPref⟩

/-- The instance in which receiver `r` reports list `l` and everyone else reports truthfully. -/
@[expose] def updateRecvPref (r : Fin n) (l : List (Fin m)) : IncompleteInstance m n :=
  ⟨I.propPref, Function.update I.recvPref r l⟩

theorem swap_updateRecvPref (r : Fin n) (l : List (Fin m)) :
    (I.updateRecvPref r l).swap = I.swap.updatePropPref r l := rfl

/-! ### Run monotonicity & exact final rank -/

private theorem run_mono_step (k : ℕ) (p : Fin m) : I.run k p ≤ I.run (k + 1) p := by
  rw [run_succ]
  rcases I.step_cases (I.run k) with ⟨h, -⟩ | ⟨q, -, h⟩
  · rw [h]
  · rw [h]
    by_cases hpq : p = q
    · subst hpq; rw [Function.update_self]; omega
    · rw [Function.update_of_ne hpq]

private theorem run_mono {j k : ℕ} (hjk : j ≤ k) (p : Fin m) : I.run j p ≤ I.run k p := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact ih.trans (I.run_mono_step k p)

private theorem run_le_finalState (k : ℕ) (p : Fin m) : I.run k p ≤ I.finalState p := by
  rcases le_total k I.totalLength with h | h
  · exact I.run_mono h p
  · rw [I.run_fixed_of_le h I.step_run_fixed]; rfl

private theorem turnsDown_run_mono {j k : ℕ} (hjk : j ≤ k) {p : Fin m} {r : Fin n}
    (h : I.TurnsDown (I.run j) r p) : I.TurnsDown (I.run k) r p := by
  induction k, hjk using Nat.le_induction with
  | base => exact h
  | succ k _ ih =>
    rw [run_succ]
    rcases I.step_cases (I.run k) with ⟨hfix, -⟩ | ⟨q, hq, hupd⟩
    · rwa [hfix]
    · rw [hupd]
      rcases ih with hnot | ⟨x, hx, hxp⟩
      · exact Or.inl hnot
      · by_cases hxq : x = q
        · subst hxq
          obtain ⟨r', hr', hd⟩ := hq
          have hrr : r' = r := Option.some_injective _ (hr'.symm.trans hx)
          subst hrr
          rcases hd with hnot | ⟨y, hy, hyx⟩
          · exfalso
            have heq : I.recvRank r' (some x) = I.recvRank r' none :=
              List.idxOf_eq_length_iff.2 hnot
            have := I.recvRank_le_recvRank_none r' (some p)
            omega
          · have hyx' : y ≠ x := by rintro rfl; exact lt_irrefl _ hyx
            exact Or.inr ⟨y, by simp only [target, Function.update_of_ne hyx']; exact hy,
              lt_trans hyx hxp⟩
        · exact Or.inr ⟨x, by simp only [target, Function.update_of_ne hxq]; exact hx, hxp⟩

private theorem getElem?_idxOf_of_mem {α : Type*} [DecidableEq α] {l : List α} {a : α}
    (ha : a ∈ l) : l[l.idxOf a]? = some a := by
  have hlt : l.idxOf a < l.length := List.idxOf_lt_length_iff.2 ha
  exact List.getElem?_eq_getElem hlt |>.trans (congrArg some (List.getElem_idxOf hlt))

/-- For every proposer `p`, the final state index of deferred acceptance equals the rank of
`p`'s final outcome (`idxOf` when matched, `length` when unmatched), even with duplicate entries. -/
theorem propRank_deferredAcceptance_eq_finalState (p : Fin m) :
    I.propRank p (I.deferredAcceptance p) = I.finalState p := by
  refine le_antisymm (I.propRank_deferredAcceptance_le p) ?_
  by_contra hlt
  push Not at hlt
  cases hd : I.deferredAcceptance p with
  | none =>
    rw [hd, propRank_none] at hlt
    have hle := I.inv_finalState.le_length p
    rw [deferredAcceptance_apply] at hd
    have : (I.propPref p).length ≤ I.finalState p := List.getElem?_eq_none_iff.1 hd
    omega
  | some r =>
    have hmem : r ∈ I.propPref p := (I.isIndividuallyRational_deferredAcceptance p r hd).1
    have hget : (I.propPref p)[(I.propPref p).idxOf r]? = some r := getElem?_idxOf_of_mem hmem
    rw [hd, propRank_some] at hlt
    have htd : I.TurnsDown I.finalState r p := I.inv_finalState.turnsDown p _ r hlt hget
    exact I.not_rejected_finalState p ⟨r, hd, htd⟩

/-! ### The blocking lemma for incomplete lists -/

private theorem recvRank_deferredAcceptance_lt {q : Fin m} {r : Fin n}
    (hq_lt : I.propRank q (some r) < I.propRank q (I.deferredAcceptance q))
    (hqr : q ∈ I.recvPref r) :
    ∃ x : Fin m, I.deferredAcceptance x = some r ∧
      I.recvRank r (some x) < I.recvRank r (some q) := by
  have hr_mem : r ∈ I.propPref q :=
    (I.propRank_some_lt_none_iff q r).1 (lt_of_lt_of_le hq_lt (I.propRank_le_propRank_none q _))
  have hk : (I.propPref q).idxOf r < I.finalState q := by
    rw [← propRank_deferredAcceptance_eq_finalState]
    exact hq_lt
  have htd := I.inv_finalState.turnsDown q _ r hk (getElem?_idxOf_of_mem hr_mem)
  rcases htd with hnot | ⟨x, hx, hxq⟩
  · exact absurd hqr hnot
  · exact ⟨x, hx, hxq⟩

private theorem exists_last_change (B : Finset (Fin m)) {p₀ : Fin m} (hp₀ : p₀ ∈ B)
    (hpos : 0 < I.finalState p₀) :
    ∃ t < I.totalLength, ∃ p ∈ B, I.run t p ≠ I.run (t + 1) p ∧
      ∀ q ∈ B, I.run (t + 1) q = I.finalState q := by
  classical
  let N := I.totalLength
  let T := (Finset.range N).filter fun k => ∃ p ∈ B, I.run k p ≠ I.run (k + 1) p
  have hT : T.Nonempty := by
    by_contra hTe
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hTe
    have key : ∀ k ≤ N, I.run k p₀ = 0 := by
      intro k hk
      induction k with
      | zero => rfl
      | succ k ih =>
        have h1 := hTe (Finset.mem_range.2 (show k < N by omega))
        push Not at h1
        rw [← h1 p₀ hp₀, ih (by omega)]
    have := key N le_rfl
    change I.finalState p₀ = 0 at this
    omega
  set t := T.max' hT
  have ht : t ∈ T := T.max'_mem hT
  rw [Finset.mem_filter, Finset.mem_range] at ht
  obtain ⟨htN, p, hpB, hp⟩ := ht
  refine ⟨t, htN, p, hpB, hp, fun q hq => ?_⟩
  have stable : ∀ k, t + 1 ≤ k → k ≤ N → I.run (t + 1) q = I.run k q := by
    intro k hk hkN
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      rw [ih (by omega)]
      by_contra hne
      have hmem : k ∈ T := by
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, q, hq, hne⟩
      have := T.le_max' k hmem
      omega
  exact stable N (by omega) le_rfl

private theorem run_succ_eq_update_of_ne {t : ℕ} {p₀ : Fin m}
    (h : I.run t p₀ ≠ I.run (t + 1) p₀) :
    I.Rejected (I.run t) p₀ ∧
      I.run (t + 1) = Function.update (I.run t) p₀ (I.run t p₀ + 1) := by
  rw [run_succ] at h ⊢
  rcases I.step_cases (I.run t) with ⟨hs, -⟩ | ⟨p, hp, hs⟩
  · rw [hs] at h; exact absurd rfl h
  · have hpp : p₀ = p := by
      by_contra hne
      rw [hs, Function.update_of_ne hne] at h
      exact h rfl
    subst hpp
    exact ⟨hp, hs⟩

/-- **The blocking lemma for incomplete lists** (Hwang; [GaleSotomayor1985]): let `μ` be any
partial matching that is individually rational for the receivers (`μ p = some r → p ∈ recvPref r`).
If some proposer `q₀` strictly prefers `μ q₀` to `I.deferredAcceptance q₀`, then `μ` is blocked by
a pair `(x, r)` where `μ q = some r` for some proposer `q` who strictly prefers `μ`, and `x`
weakly prefers `I.deferredAcceptance x` to `μ x`. -/
theorem exists_isBlockingPair_of_lt {μ : PartialMatching m n}
    (hrecIR : ∀ p r, μ p = some r → p ∈ I.recvPref r) {q₀ : Fin m}
    (hq₀ : I.propRank q₀ (μ q₀) < I.propRank q₀ (I.deferredAcceptance q₀)) :
    ∃ (x q : Fin m) (r : Fin n), μ q = some r ∧
      I.propRank q (some r) < I.propRank q (I.deferredAcceptance q) ∧
      I.propRank x (I.deferredAcceptance x) ≤ I.propRank x (μ x) ∧
      I.IsBlockingPair μ x r := by
  classical
  set D := I.deferredAcceptance
  let B : Finset (Fin m) := Finset.univ.filter fun q => I.propRank q (μ q) < I.propRank q (D q)
  have hB : ∀ q, q ∈ B ↔ I.propRank q (μ q) < I.propRank q (D q) := fun q => by
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
  have hB_some : ∀ q ∈ B, ∃ r : Fin n, μ q = some r := by
    intro q hq
    cases h : μ q with
    | none =>
      have hlt := (hB q).1 hq
      rw [h] at hlt
      exact absurd hlt (not_lt.2 (I.propRank_le_propRank_none q _))
    | some r => exact ⟨r, rfl⟩
  have hmatch : ∀ q ∈ B, ∃ (r : Fin n) (x : Fin m),
      μ q = some r ∧ D x = some r ∧ I.recvRank r (some x) < I.recvRank r (some q) := by
    intro q hq
    obtain ⟨r, hqr⟩ := hB_some q hq
    have hlt : I.propRank q (some r) < I.propRank q (D q) := hqr ▸ (hB q).1 hq
    obtain ⟨x, hxD, hxlt⟩ := I.recvRank_deferredAcceptance_lt hlt (hrecIR q r hqr)
    exact ⟨r, x, hqr, hxD, hxlt⟩
  by_cases hnot : ∃ q ∈ B, ∃ (r : Fin n) (x : Fin m),
      μ q = some r ∧ D x = some r ∧ I.recvRank r (some x) < I.recvRank r (some q) ∧ x ∉ B
  · obtain ⟨q, hqB, r, x, hqr, hxD, hxlt, hxnot⟩ := hnot
    have hxle : I.propRank x (D x) ≤ I.propRank x (μ x) := le_of_not_gt (mt (hB x).2 hxnot)
    have hxq : x ≠ q := fun h => hxnot (h ▸ hqB)
    have hr_acc : r ∈ I.propPref x := (I.isIndividuallyRational_deferredAcceptance x r hxD).1
    have hne_μ : μ x ≠ some r := fun h => hxq (μ.inj h hqr)
    have hprop_lt : I.propRank x (some r) < I.propRank x (μ x) := by
      refine lt_of_le_of_ne (hxD ▸ hxle) fun heq => hne_μ ?_
      exact I.eq_of_propRank_eq hr_acc heq
    have hμsymm : μ.symm r = some q := μ.eq_some_iff.2 hqr
    exact ⟨x, q, r, hqr, hqr ▸ (hB q).1 hqB, hxle, hprop_lt, hμsymm ▸ hxlt⟩
  · -- Closed case: the map `q ↦ D.symm (μ q)` maps `B` injectively into `B`, hence onto `B`.
    push Not at hnot
    have hclosed : ∀ q ∈ B, ∃ x ∈ B, ∃ r : Fin n, μ q = some r ∧ D x = some r := by
      intro q hq
      obtain ⟨r, x, hqr, hxD, hxlt⟩ := hmatch q hq
      exact ⟨x, hnot q hq r x hqr hxD hxlt, r, hqr, hxD⟩
    have honto : ∀ p ∈ B, ∃ q ∈ B, ∃ r : Fin n, μ q = some r ∧ D p = some r := by
      let f : {q // q ∈ B} → {p // p ∈ B} := fun q =>
        ⟨(hclosed q.1 q.2).choose, (hclosed q.1 q.2).choose_spec.1⟩
      have hfinj : Function.Injective f := by
        rintro ⟨q₁, hq₁⟩ ⟨q₂, hq₂⟩ heq
        have hx : (hclosed q₁ hq₁).choose = (hclosed q₂ hq₂).choose := congrArg Subtype.val heq
        obtain ⟨r₁, hμ₁, hD₁⟩ := (hclosed q₁ hq₁).choose_spec.2
        obtain ⟨r₂, hμ₂, hD₂⟩ := (hclosed q₂ hq₂).choose_spec.2
        rw [hx] at hD₁
        have hrr : r₁ = r₂ := Option.some_injective _ (hD₁.symm.trans hD₂)
        exact Subtype.ext (μ.inj hμ₁ (hrr ▸ hμ₂))
      have hsurj := (Finite.injective_iff_bijective.1 hfinj).2
      intro p hp
      obtain ⟨⟨q, hq⟩, hfq⟩ := hsurj ⟨p, hp⟩
      have heq : (hclosed q hq).choose = p := congrArg Subtype.val hfq
      obtain ⟨r, hμq, hDp⟩ := (hclosed q hq).choose_spec.2
      exact ⟨q, hq, r, hμq, heq ▸ hDp⟩
    have hq₀B : q₀ ∈ B := (hB q₀).2 hq₀
    have hpos : 0 < I.finalState q₀ := by
      have hlt := (hB q₀).1 hq₀B
      rw [I.propRank_deferredAcceptance_eq_finalState q₀] at hlt
      omega
    obtain ⟨t, _, p₀, hp₀B, hch, hfin⟩ := I.exists_last_change B hq₀B hpos
    obtain ⟨hrej, hupd⟩ := I.run_succ_eq_update_of_ne hch
    obtain ⟨q, hqB, r₀, hμq, hDp₀⟩ := honto p₀ hp₀B
    have hqp : q ≠ p₀ := by
      rintro rfl
      have h := (hB q).1 hqB
      rw [hμq, hDp₀] at h
      exact lt_irrefl _ h
    have hrun_ne : ∀ y, y ≠ p₀ → I.run (t + 1) y = I.run t y := fun y hy => by
      rw [hupd, Function.update_of_ne hy]
    have hq_mem : r₀ ∈ I.propPref q :=
      (I.propRank_some_lt_none_iff q r₀).1
        (lt_of_lt_of_le (hμq ▸ (hB q).1 hqB) (I.propRank_le_propRank_none q _))
    have hk_q : (I.propPref q).idxOf r₀ < I.run t q := by
      have h := (hB q).1 hqB
      rw [hμq, propRank_some, I.propRank_deferredAcceptance_eq_finalState q,
        ← hfin q hqB, hrun_ne q hqp] at h
      exact h
    have htd_q := (I.inv_run t).turnsDown q _ r₀ hk_q (getElem?_idxOf_of_mem hq_mem)
    rcases htd_q with hnot_rec | ⟨x, hx, hxq⟩
    · exact absurd (hrecIR q r₀ hμq) hnot_rec
    have hxp : x ≠ p₀ := by
      rintro rfl
      have htd_p : I.TurnsDown (I.run (t + 1)) r₀ x := by
        have hklt : I.run t x < I.run (t + 1) x := by rw [hupd, Function.update_self]; omega
        exact (I.inv_run (t + 1)).turnsDown x (I.run t x) r₀ hklt hx
      have htd_fin : I.TurnsDown I.finalState r₀ x := by
        rw [show I.finalState = I.run I.totalLength from rfl]
        rcases le_total (t + 1) I.totalLength with hle | hge
        · exact I.turnsDown_run_mono hle htd_p
        · have heq : I.run (t + 1) = I.run I.totalLength :=
            I.run_fixed_of_le hge I.step_run_fixed
          exact heq ▸ htd_p
      exact I.not_rejected_finalState x ⟨r₀, hDp₀, htd_fin⟩
    have hx' : I.target (I.run (t + 1)) x = some r₀ := by
      simpa only [target, hrun_ne x hxp] using hx
    have hxB : x ∉ B := by
      intro hxB
      have hDx : D x = some r₀ := by
        change I.target I.finalState x = some r₀
        simpa only [target, hfin x hxB] using hx'
      exact hxp (I.target_finalState_inj x p₀ r₀ hDx hDp₀)
    have hxle : I.propRank x (D x) ≤ I.propRank x (μ x) := le_of_not_gt (mt (hB x).2 hxB)
    have hxlt_state : I.run (t + 1) x < I.finalState x := by
      refine lt_of_le_of_ne (I.run_le_finalState (t + 1) x) fun heq => hxp ?_
      have hDx : I.target I.finalState x = some r₀ := by simpa only [target, heq] using hx'
      exact I.target_finalState_inj x p₀ r₀ hDx hDp₀
    have hxlt_rank : I.propRank x (some r₀) < I.propRank x (D x) := by
      rw [propRank_some, I.propRank_deferredAcceptance_eq_finalState x]
      have hidx_le : (I.propPref x).idxOf r₀ ≤ I.run (t + 1) x := by
        obtain ⟨_, hka⟩ := List.getElem?_eq_some_iff.1 hx'
        by_contra hlt
        push Not at hlt
        have hnot := List.not_of_lt_findIdx (p := fun y => y == r₀) (xs := I.propPref x) hlt
        simp only [hka, beq_self_eq_true] at hnot
        exact Bool.false_ne_true hnot.symm
      exact lt_of_le_of_lt hidx_le hxlt_state
    refine ⟨x, q, r₀, hμq, hμq ▸ (hB q).1 hqB, hxle, lt_of_lt_of_le hxlt_rank hxle, ?_⟩
    rw [μ.eq_some_iff.2 hμq]
    exact hxq

/-! ### Weak Pareto optimality and coalitional strategy-proofness -/

/-- **Weak Pareto optimality for proposers** ([Roth1982], incomplete-list setting): if `m ≥ 1`, no
receiver-individually-rational partial matching makes every proposer strictly better off than
`deferredAcceptance`. -/
theorem not_forall_propRank_lt_deferredAcceptance [NeZero m] {μ : PartialMatching m n}
    (hrecIR : ∀ p r, μ p = some r → p ∈ I.recvPref r) :
    ¬ ∀ p, I.propRank p (μ p) < I.propRank p (I.deferredAcceptance p) := by
  intro h
  obtain ⟨x, -, -, -, -, hx, -⟩ := I.exists_isBlockingPair_of_lt hrecIR (h 0)
  exact absurd (h x) (not_lt_of_ge hx)

/-- **Coalitional strategy-proofness of deferred acceptance** ([DubinsFreedman1981], incomplete
lists with unequal sides): if proposers in a nonempty coalition `C` jointly submit arbitrary lists
(including truncations or reorderings), then in **no** matching `μ` stable for the reported
instance `J` can every member of `C` strictly improve over its true `deferredAcceptance`
outcome. -/
theorem not_forall_mem_propRank_lt_of_isStable {J : IncompleteInstance m n} {C : Set (Fin m)}
    (hrecv : J.recvPref = I.recvPref) (hprop : ∀ p ∉ C, J.propPref p = I.propPref p)
    (hC : C.Nonempty) {μ : PartialMatching m n} (hμ : J.IsStable μ) :
    ¬ ∀ p ∈ C, I.propRank p (μ p) < I.propRank p (I.deferredAcceptance p) := by
  intro h
  have hrecIR : ∀ p r, μ p = some r → p ∈ I.recvPref r := fun p r hpr => by
    rw [← hrecv]; exact (hμ.1 p r hpr).2
  obtain ⟨p₀, hp₀⟩ := hC
  obtain ⟨x, -, r, -, -, hx, hbx⟩ := I.exists_isBlockingPair_of_lt hrecIR (h p₀ hp₀)
  have hxC : x ∉ C := fun hxC => absurd (h x hxC) (not_lt_of_ge hx)
  refine hμ.2 x r ⟨?_, ?_⟩
  · simpa only [propRank, hprop x hxC] using hbx.1
  · simpa only [recvRank, hrecv] using hbx.2

theorem propRank_deferredAcceptance_le_of_isStable_updatePropPref (p : Fin m)
    (l : List (Fin n)) {μ : PartialMatching m n} (hμ : (I.updatePropPref p l).IsStable μ) :
    I.propRank p (I.deferredAcceptance p) ≤ I.propRank p (μ p) := by
  refine le_of_not_gt fun h =>
    I.not_forall_mem_propRank_lt_of_isStable (J := I.updatePropPref p l) (C := {p}) rfl
      (fun q hq => Function.update_of_ne hq _ _) ⟨p, rfl⟩ hμ ?_
  rintro q rfl
  exact h

theorem propRank_deferredAcceptance_le_updatePropPref (p : Fin m) (l : List (Fin n)) :
    I.propRank p (I.deferredAcceptance p) ≤
      I.propRank p ((I.updatePropPref p l).deferredAcceptance p) :=
  I.propRank_deferredAcceptance_le_of_isStable_updatePropPref p l
    (isStable_deferredAcceptance _)

/-! ### Comparative statics: adding a receiver (`GaleSotomayor1985`) -/

/-- `I' : IncompleteInstance m (n + 1)` **extends `I : IncompleteInstance m n` by adding a new
receiver** (`Fin.last n`): original receivers keep their exact preference lists, and every
proposer preserves both membership and relative order over the original `n` receivers. -/
structure ExtendsByReceiver (I : IncompleteInstance m n)
    (I' : IncompleteInstance m (n + 1)) : Prop where
  /-- Original receivers keep their exact preference lists. -/
  recvPref_castSucc : ∀ r : Fin n, I'.recvPref r.castSucc = I.recvPref r
  /-- Original receiver acceptability is preserved for every proposer. -/
  mem_propPref_castSucc_iff :
    ∀ (p : Fin m) (r : Fin n), r.castSucc ∈ I'.propPref p ↔ r ∈ I.propPref p
  /-- Relative ranking between original receivers is preserved for every proposer. -/
  propRank_castSucc_lt_iff :
    ∀ (p : Fin m) (r₁ r₂ : Fin n),
      I'.propRank p (some r₁.castSucc) < I'.propRank p (some r₂.castSucc) ↔
        I.propRank p (some r₁) < I.propRank p (some r₂)

namespace ExtendsByReceiver

private def liftMatching (μ : PartialMatching m n) : PartialMatching m (n + 1) :=
  PartialMatching.ofInjOn (fun p => (μ p).map Fin.castSucc) fun p q r hp hq => by
    cases hμp : μ p with
    | none => simp [hμp] at hp
    | some rp =>
      cases hμq : μ q with
      | none => simp [hμq] at hq
      | some rq =>
        simp only [hμp, hμq, Option.map_some, Option.some.injEq] at hp hq
        have heq : rp = rq := Fin.castSucc_injective _ (hp.trans hq.symm)
        exact μ.inj hμp (heq ▸ hμq)

private theorem liftMatching_symm_castSucc (μ : PartialMatching m n) (r : Fin n) :
    (liftMatching μ).symm r.castSucc = μ.symm r := by
  cases h : μ.symm r with
  | none =>
    cases hc : (liftMatching μ).symm r.castSucc with
    | none => rfl
    | some p =>
      have hp := (liftMatching μ).eq_some_iff.1 hc
      change (μ p).map Fin.castSucc = some r.castSucc at hp
      cases hμp : μ p with
      | none => simp [hμp] at hp
      | some r' =>
        simp only [hμp, Option.map_some, Option.some.injEq] at hp
        have hr : r' = r := Fin.castSucc_injective _ hp
        have := μ.eq_some_iff.2 (hr ▸ hμp)
        rw [h] at this; exact absurd this (by simp)
  | some p =>
    refine (liftMatching μ).eq_some_iff.2 ?_
    change (μ p).map Fin.castSucc = some r.castSucc
    rw [μ.eq_some_iff.1 h, Option.map_some]

private def restrictMatching (μ' : PartialMatching m (n + 1)) : PartialMatching m n :=
  PartialMatching.ofInjOn
    (fun p => match μ' p with
      | some r => if h : r.val < n then some ⟨r.val, h⟩ else none
      | none => none)
    fun p q r hp hq => by
      cases hμp : μ' p with
      | none => simp [hμp] at hp
      | some rp =>
        cases hμq : μ' q with
        | none => simp [hμq] at hq
        | some rq =>
          simp only [hμp, hμq] at hp hq
          split_ifs at hp with h1
          split_ifs at hq with h2
          have hrp : rp = r.castSucc :=
            Fin.ext (congrArg Fin.val (Option.some_injective (Fin n) hp) : rp.val = r.val)
          have hrq : rq = r.castSucc :=
            Fin.ext (congrArg Fin.val (Option.some_injective (Fin n) hq) : rq.val = r.val)
          exact μ'.inj (hrp ▸ hμp) (hrq ▸ hμq)

private theorem restrictMatching_symm (μ' : PartialMatching m (n + 1)) (r : Fin n) :
    (restrictMatching μ').symm r = μ'.symm r.castSucc := by
  cases h : μ'.symm r.castSucc with
  | none =>
    cases hc : (restrictMatching μ').symm r with
    | none => rfl
    | some p =>
      have hp := (restrictMatching μ').eq_some_iff.1 hc
      dsimp only [restrictMatching, PartialMatching.ofInjOn_apply] at hp
      cases hμp : μ' p with
      | none => simp [hμp] at hp
      | some r' =>
        simp only [hμp] at hp
        split_ifs at hp with hr'
        have heq : r' = r.castSucc :=
          Fin.ext (congrArg Fin.val (Option.some_injective (Fin n) hp) : r'.val = r.val)
        have := μ'.eq_some_iff.2 (heq ▸ hμp)
        rw [h] at this; exact absurd this (by simp)
  | some p =>
    refine (restrictMatching μ').eq_some_iff.2 ?_
    dsimp only [restrictMatching, PartialMatching.ofInjOn_apply]
    rw [μ'.eq_some_iff.1 h]
    simp [r.isLt]

private theorem propRank_lt_of_castSucc {I : IncompleteInstance m n}
    {I' : IncompleteInstance m (n + 1)} (hE : ExtendsByReceiver I I')
    {p : Fin m} {r : Fin n} {o : Option (Fin n)}
    (h : I'.propRank p (some r.castSucc) < I'.propRank p (o.map Fin.castSucc)) :
    I.propRank p (some r) < I.propRank p o := by
  cases o with
  | none =>
    rw [Option.map_none] at h
    exact (I.propRank_some_lt_none_iff p r).2
      ((hE.mem_propPref_castSucc_iff p r).1 ((I'.propRank_some_lt_none_iff p r.castSucc).1 h))
  | some s =>
    rw [Option.map_some] at h
    exact (hE.propRank_castSucc_lt_iff p r s).1 h

private theorem recvRank_castSucc {I : IncompleteInstance m n}
    {I' : IncompleteInstance m (n + 1)} (hE : ExtendsByReceiver I I') (r : Fin n)
    (o : Option (Fin m)) : I'.recvRank r.castSucc o = I.recvRank r o := by
  cases o <;> simp [recvRank, hE.recvPref_castSucc r]

/-- **Gale–Sotomayor comparative statics (proposer side, proposer-DA)** ([GaleSotomayor1985]):
adding a receiver makes every proposer weakly better off under `deferredAcceptance`. -/
theorem deferredAcceptance_propRank_le {I : IncompleteInstance m n}
    {I' : IncompleteInstance m (n + 1)} (hE : ExtendsByReceiver I I') (p : Fin m) :
    I'.propRank p (I'.deferredAcceptance p) ≤
      I'.propRank p ((I.deferredAcceptance p).map Fin.castSucc) := by
  by_contra hlt
  push Not at hlt
  let μl := liftMatching I.deferredAcceptance
  have hrecIR : ∀ q r', μl q = some r' → q ∈ I'.recvPref r' := by
    intro q r' hq
    change (I.deferredAcceptance q).map Fin.castSucc = some r' at hq
    cases h : I.deferredAcceptance q with
    | none => simp [h] at hq
    | some r =>
      simp only [h, Option.map_some, Option.some.injEq] at hq
      subst hq
      rw [hE.recvPref_castSucc r]
      exact (I.isIndividuallyRational_deferredAcceptance q r h).2
  have hlt' : I'.propRank p (μl p) < I'.propRank p (I'.deferredAcceptance p) := hlt
  obtain ⟨x, q, r', hμq, -, -, hbp⟩ := I'.exists_isBlockingPair_of_lt hrecIR hlt'
  change (I.deferredAcceptance q).map Fin.castSucc = some r' at hμq
  cases h : I.deferredAcceptance q with
  | none => simp [h] at hμq
  | some r =>
    simp only [h, Option.map_some, Option.some.injEq] at hμq
    subst hμq
    refine I.isStable_deferredAcceptance.2 x r ⟨?_, ?_⟩
    · exact hE.propRank_lt_of_castSucc hbp.1
    · have := hbp.2
      rwa [liftMatching_symm_castSucc, hE.recvRank_castSucc, hE.recvRank_castSucc] at this

/-- **Gale–Sotomayor comparative statics (receiver side, proposer-DA)** ([GaleSotomayor1985]):
adding a receiver makes every original receiver weakly worse off under `deferredAcceptance`. -/
theorem deferredAcceptance_recvRank_le {I : IncompleteInstance m n}
    {I' : IncompleteInstance m (n + 1)} (hE : ExtendsByReceiver I I') (r : Fin n) :
    I.recvRank r (I.deferredAcceptance.symm r) ≤
      I.recvRank r (I'.deferredAcceptance.symm r.castSucc) := by
  cases h : I'.deferredAcceptance.symm r.castSucc with
  | none => exact I.recvRank_le_recvRank_none r _
  | some p =>
    refine not_lt.1 fun hlt => ?_
    have hD'p : I'.deferredAcceptance p = some r.castSucc :=
      I'.deferredAcceptance.eq_some_iff.1 h
    have hacc' : r.castSucc ∈ I'.propPref p :=
      (I'.isIndividuallyRational_deferredAcceptance p r.castSucc hD'p).1
    have hple : I'.propRank p (some r.castSucc) ≤
        I'.propRank p ((I.deferredAcceptance p).map Fin.castSucc) :=
      hD'p ▸ hE.deferredAcceptance_propRank_le p
    have hplt : I'.propRank p (some r.castSucc) <
        I'.propRank p ((I.deferredAcceptance p).map Fin.castSucc) := by
      refine lt_of_le_of_ne hple fun heq => ?_
      have heq_opt := I'.eq_of_propRank_eq hacc' heq
      cases hDp : I.deferredAcceptance p with
      | none => simp [hDp] at heq_opt
      | some r₀ =>
        simp only [hDp, Option.map_some, Option.some.injEq] at heq_opt
        have hrr : r₀ = r := Fin.castSucc_injective _ heq_opt
        have hsym := I.deferredAcceptance.eq_some_iff.2 (hrr ▸ hDp)
        rw [hsym] at hlt
        exact lt_irrefl _ hlt
    exact I.isStable_deferredAcceptance.2 p r ⟨hE.propRank_lt_of_castSucc hplt, hlt⟩

/-- **Gale–Sotomayor comparative statics (receiver side, receiver-DA)** ([GaleSotomayor1985]):
adding a receiver makes every original receiver weakly worse off under
`receiverDeferredAcceptance`. -/
theorem receiverDeferredAcceptance_recvRank_le {I : IncompleteInstance m n}
    {I' : IncompleteInstance m (n + 1)} (hE : ExtendsByReceiver I I') (r : Fin n) :
    I.recvRank r (I.receiverDeferredAcceptance.symm r) ≤
      I.recvRank r (I'.receiverDeferredAcceptance.symm r.castSucc) := by
  by_contra hlt
  push Not at hlt
  let νr := restrictMatching I'.receiverDeferredAcceptance
  have hpropIR : ∀ q p, νr.symm q = some p → q ∈ I.swap.recvPref p := by
    intro q p hqp
    rw [restrictMatching_symm] at hqp
    have hIR' := I'.isStable_receiverDeferredAcceptance.1 p q.castSucc
      (I'.receiverDeferredAcceptance.eq_some_iff.1 hqp)
    exact (hE.mem_propPref_castSucc_iff p q).1 hIR'.1
  have hlt_swap : I.swap.propRank r (νr.symm r) <
      I.swap.propRank r (I.swap.deferredAcceptance r) := by
    change I.recvRank r (νr.symm r) < I.recvRank r (I.swap.deferredAcceptance r)
    rw [restrictMatching_symm]
    exact hlt
  obtain ⟨r_b, q, p, hνq, -, -, hbp⟩ :=
    I.swap.exists_isBlockingPair_of_lt (μ := νr.symm) hpropIR hlt_swap
  have hν'p : I'.receiverDeferredAcceptance p = some q.castSucc := by
    rw [restrictMatching_symm] at hνq
    exact I'.receiverDeferredAcceptance.eq_some_iff.1 hνq
  have hp_mem : r_b.castSucc ∈ I'.propPref p :=
    (hE.mem_propPref_castSucc_iff p r_b).2
      ((I.propRank_some_lt_none_iff p r_b).1
        (lt_of_lt_of_le hbp.2 (I.propRank_le_propRank_none p _)))
  refine I'.isStable_receiverDeferredAcceptance.2 p r_b.castSucc ⟨?_, ?_⟩
  · rw [hν'p]
    have hq_symm : νr p = some q := (restrictMatching _).eq_some_iff.1 hνq
    have h2 : I.propRank p (some r_b) < I.propRank p (some q) := by
      simpa only [swap_recvRank, PEquiv.symm_symm, hq_symm] using hbp.2
    exact (hE.propRank_castSucc_lt_iff p r_b q).2 h2
  · have h1 : I.recvRank r_b (some p) < I.recvRank r_b (νr.symm r_b) := hbp.1
    rw [restrictMatching_symm] at h1
    simpa only [hE.recvRank_castSucc] using h1

/-- **Gale–Sotomayor comparative statics (proposer side, receiver-DA)** ([GaleSotomayor1985]):
adding a receiver makes every proposer weakly better off under `receiverDeferredAcceptance`. -/
theorem receiverDeferredAcceptance_propRank_le {I : IncompleteInstance m n}
    {I' : IncompleteInstance m (n + 1)} (hE : ExtendsByReceiver I I') (p : Fin m) :
    I'.propRank p (I'.receiverDeferredAcceptance p) ≤
      I'.propRank p ((I.receiverDeferredAcceptance p).map Fin.castSucc) := by
  by_contra hlt
  push Not at hlt
  cases h : I.receiverDeferredAcceptance p with
  | none =>
    rw [h, Option.map_none] at hlt
    exact absurd hlt (not_lt.2 (I'.propRank_le_propRank_none p _))
  | some r =>
    rw [h, Option.map_some] at hlt
    have hp_acc : p ∈ I.recvPref r := (I.isStable_receiverDeferredAcceptance.1 p r h).2
    have hsym := I.receiverDeferredAcceptance.eq_some_iff.2 h
    have hrle : I.recvRank r (some p) ≤
        I.recvRank r (I'.receiverDeferredAcceptance.symm r.castSucc) :=
      hsym ▸ hE.receiverDeferredAcceptance_recvRank_le r
    have hrlt : I.recvRank r (some p) <
        I.recvRank r (I'.receiverDeferredAcceptance.symm r.castSucc) := by
      refine lt_of_le_of_ne hrle fun heq => ?_
      have heq_opt := I.eq_of_recvRank_eq hp_acc heq
      have hfp := I'.receiverDeferredAcceptance.eq_some_iff.1 heq_opt
      rw [hfp] at hlt
      exact lt_irrefl _ hlt
    exact I'.isStable_receiverDeferredAcceptance.2 p r.castSucc
      ⟨hlt, by simpa only [hE.recvRank_castSucc] using hrlt⟩

end ExtendsByReceiver

end IncompleteInstance

/-! ### Direct matching mechanisms with incomplete lists -/

/-- A direct matching mechanism on markets with `m` proposers, `n` receivers, and possibly
incomplete preference lists. -/
abbrev PartialMatchingMechanism (m n : ℕ) := IncompleteInstance m n → PartialMatching m n

namespace PartialMatchingMechanism

variable {m n : ℕ}

/-- A partial matching mechanism is stable when it returns a stable partial matching on every
reported market. -/
@[expose] def IsStable (M : PartialMatchingMechanism m n) : Prop :=
  ∀ I : IncompleteInstance m n, I.IsStable (M I)

/-- A mechanism is strategy-proof for the proposers when no proposer can strictly reduce its rank
by reporting any preference list `l` (including truncating acceptable receivers or adding
unacceptable ones). -/
@[expose] def IsProposerStrategyProof (M : PartialMatchingMechanism m n) : Prop :=
  ∀ (I : IncompleteInstance m n) (p : Fin m) (l : List (Fin n)),
    I.propRank p (M I p) ≤ I.propRank p (M (I.updatePropPref p l) p)

/-- A mechanism is strategy-proof for the receivers when no receiver can strictly reduce its rank
by misreporting its preference list. -/
@[expose] def IsReceiverStrategyProof (M : PartialMatchingMechanism m n) : Prop :=
  ∀ (I : IncompleteInstance m n) (r : Fin n) (l : List (Fin m)),
    I.recvRank r ((M I).symm r) ≤ I.recvRank r ((M (I.updateRecvPref r l)).symm r)

theorem isStable_deferredAcceptance :
    IsStable (IncompleteInstance.deferredAcceptance (m := m) (n := n)) :=
  fun I => I.isStable_deferredAcceptance

theorem isStable_receiverDeferredAcceptance :
    IsStable (IncompleteInstance.receiverDeferredAcceptance (m := m) (n := n)) :=
  fun I => I.isStable_receiverDeferredAcceptance

/-- Proposer-proposing deferred acceptance is strategy-proof for proposers on incomplete-list
markets with unequal sides ([DubinsFreedman1981]; [Roth1982]). -/
theorem isProposerStrategyProof_deferredAcceptance :
    IsProposerStrategyProof (IncompleteInstance.deferredAcceptance (m := m) (n := n)) :=
  fun I p l => I.propRank_deferredAcceptance_le_updatePropPref p l

/-- Receiver-proposing deferred acceptance is strategy-proof for receivers on incomplete-list
markets with unequal sides. -/
theorem isReceiverStrategyProof_receiverDeferredAcceptance :
    IsReceiverStrategyProof (IncompleteInstance.receiverDeferredAcceptance (m := m) (n := n)) := by
  intro I r l
  exact I.swap.propRank_deferredAcceptance_le_updatePropPref r l

/-! ### Sharp Roth impossibility for incomplete lists: `2 ≤ m ∧ 2 ≤ n` -/

/-- Embedded `2 × 2` symmetric-cycle market with `m - 2` empty-list dummy proposers and `n - 2`
empty-list dummy receivers (`2 ≤ m, 2 ≤ n`). Truncating a list to a single agent turns either of
its two stable matchings into the unique stable matching of the truncated market. -/
@[expose] def truncationWitness (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    IncompleteInstance m n where
  propPref p :=
    if p.val = 0 then [⟨0, by omega⟩, ⟨1, by omega⟩]
    else if p.val = 1 then [⟨1, by omega⟩, ⟨0, by omega⟩]
    else []
  recvPref r :=
    if r.val = 0 then [⟨1, by omega⟩, ⟨0, by omega⟩]
    else if r.val = 1 then [⟨0, by omega⟩, ⟨1, by omega⟩]
    else []

private theorem ne_none_of_two_by_two_cycle {m n : ℕ} {K : IncompleteInstance m n}
    {μ : PartialMatching m n} (hK : K.IsStable μ) {p0 p1 : Fin m} {r0 r1 : Fin n}
    (hrne : r0 ≠ r1) (hp0 : r0 ∈ K.propPref p0) (hp1 : K.propPref p1 = [r1, r0])
    (hr0 : K.recvPref r0 = [p1, p0]) (hr1 : K.recvPref r1 = [p0, p1]) :
    μ p0 ≠ none := by
  intro h0
  cases hsym0 : μ.symm r0 with
  | none =>
    refine hK.2 p0 r0 ⟨?_, ?_⟩
    · rw [h0, K.propRank_some_lt_none_iff]
      exact hp0
    · rw [hsym0, K.recvRank_some_lt_none_iff, hr0]
      simp
  | some q =>
    have hq_mem : q = p1 ∨ q = p0 := by
      have hacc := (hK.1 q r0 (μ.eq_some_iff.1 hsym0)).2
      simpa [hr0] using hacc
    rcases hq_mem with hqp1 | hqp0
    · subst q
      have hp1_eq : μ p1 = some r0 := μ.eq_some_iff.1 hsym0
      have hsym1 : μ.symm r1 = none := by
        cases hr1_eq : μ.symm r1 with
        | none => rfl
        | some x =>
          have hx_mem : x = p0 ∨ x = p1 := by
            have hacc := (hK.1 x r1 (μ.eq_some_iff.1 hr1_eq)).2
            simpa [hr1] using hacc
          rcases hx_mem with hxp0 | hxp1
          · subst x
            have hx0 := μ.eq_some_iff.1 hr1_eq
            rw [h0] at hx0
            exact absurd hx0 (by simp)
          · subst x
            have hx1 := μ.eq_some_iff.1 hr1_eq
            rw [hp1_eq] at hx1
            exact absurd (Option.some_injective _ hx1) hrne
      refine hK.2 p1 r1 ⟨?_, ?_⟩
      · rw [hp1_eq]
        simp [IncompleteInstance.propRank, hp1, hrne.symm]
      · rw [hsym1, K.recvRank_some_lt_none_iff, hr1]
        simp
    · subst q
      have hp0_eq := μ.eq_some_iff.1 hsym0
      rw [h0] at hp0_eq
      exact absurd hp0_eq (by simp)

/-- With incomplete preference lists (where truncation is permitted), **Roth's impossibility**
holds already at **`m ≥ 2, n ≥ 2`** (compare with `n ≥ 3` for complete lists in
`RothImpossibility.lean`). -/
theorem not_isStable_and_strategyProof {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (M : PartialMatchingMechanism m n) :
    ¬ (M.IsStable ∧ M.IsProposerStrategyProof ∧ M.IsReceiverStrategyProof) := by
  rintro ⟨hs, hp, hr⟩
  let p0 : Fin m := ⟨0, by omega⟩
  let p1 : Fin m := ⟨1, by omega⟩
  let r0 : Fin n := ⟨0, by omega⟩
  let r1 : Fin n := ⟨1, by omega⟩
  have hpne : p0 ≠ p1 := fun h => by have := congrArg Fin.val h; simp [p0, p1] at this
  have hrne : r0 ≠ r1 := fun h => by have := congrArg Fin.val h; simp [r0, r1] at this
  let I := truncationWitness m n hm hn
  have hM := hs I
  have hM0_ne : M I p0 ≠ none :=
    ne_none_of_two_by_two_cycle hM hrne (p1 := p1)
      (by simp [I, truncationWitness, p0, r0])
      (by simp [I, truncationWitness, p1, r0, r1])
      (by simp [I, truncationWitness, p0, p1, r0])
      (by simp [I, truncationWitness, p0, p1, r1])
  obtain ⟨r_init, h0_init⟩ := Option.ne_none_iff_exists'.1 hM0_ne
  have hM_r0_eq : M I p0 = some r0 ∨ M I p0 = some r1 := by
    have hmem := (hM.1 p0 r_init h0_init).1
    rcases (by simpa [I, truncationWitness, p0, r0, r1] using hmem : r_init = r0 ∨ r_init = r1)
      with rfl | rfl
    · exact Or.inl h0_init
    · exact Or.inr h0_init
  rcases hM_r0_eq with h0 | h0
  · -- Receiver `r0` truncates from `[p1, p0]` to `[p1]`, forcing `p1` as its partner.
    let J := I.updateRecvPref r0 [p1]
    have hJ := hs J
    have hM_symm0 : (M I).symm r0 = some p0 := (M I).eq_some_iff.2 h0
    have hJ_ne : (M J).symm r0 ≠ none :=
      ne_none_of_two_by_two_cycle ((J.isStable_swap_iff (M J)).2 hJ) hpne.symm (p1 := r1)
        (by simp [J, IncompleteInstance.updateRecvPref, IncompleteInstance.swap])
        (by simp [J, IncompleteInstance.updateRecvPref, IncompleteInstance.swap,
          Function.update_of_ne hrne.symm, I, truncationWitness, p0, p1, r1])
        (by simp [J, IncompleteInstance.updateRecvPref, IncompleteInstance.swap, I,
          truncationWitness, p1, r0, r1])
        (by simp [J, IncompleteInstance.updateRecvPref, IncompleteInstance.swap, I,
          truncationWitness, p0, r0, r1])
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 hJ_ne
    have hJ_symm0 : (M J).symm r0 = some p1 := by
      have hx_acc := (hJ.1 x r0 ((M J).eq_some_iff.1 hx)).2
      have hxp1 : x = p1 := by simpa [J, IncompleteInstance.updateRecvPref] using hx_acc
      exact hxp1 ▸ hx
    have hsp := hr I r0 [p1]
    rw [hM_symm0, hJ_symm0] at hsp
    have hrank_lt : I.recvRank r0 (some p1) < I.recvRank r0 (some p0) := by
      simp [I, truncationWitness, p0, p1, r0, hpne.symm]
    exact absurd hsp (not_le_of_gt hrank_lt)
  · -- Proposer `p0` truncates from `[r0, r1]` to `[r0]`, forcing `r0` as its partner.
    let J := I.updatePropPref p0 [r0]
    have hJ := hs J
    have hJ_ne : M J p0 ≠ none :=
      ne_none_of_two_by_two_cycle hJ hrne (p1 := p1)
        (by simp [J, IncompleteInstance.updatePropPref])
        (by simp [J, IncompleteInstance.updatePropPref, Function.update_of_ne hpne.symm, I,
          truncationWitness, p1, r0, r1])
        (by simp [J, IncompleteInstance.updatePropPref, I, truncationWitness, p0, p1, r0])
        (by simp [J, IncompleteInstance.updatePropPref, I, truncationWitness, p0, p1, r1])
    obtain ⟨s, hs_eq⟩ := Option.ne_none_iff_exists'.1 hJ_ne
    have hJ_0 : M J p0 = some r0 := by
      have hs_acc := (hJ.1 p0 s hs_eq).1
      have hsr0 : s = r0 := by simpa [J, IncompleteInstance.updatePropPref] using hs_acc
      exact hsr0 ▸ hs_eq
    have hsp := hp I p0 [r0]
    rw [h0, hJ_0] at hsp
    have hrank_lt : I.propRank p0 (some r0) < I.propRank p0 (some r1) := by
      simp [I, truncationWitness, p0, r0, r1, hrne]
    exact absurd hsp (not_le_of_gt hrank_lt)

/-- Sharp positive converse for incomplete lists: when `m ≤ 1` or `n ≤ 1`, proposer-proposing
deferred acceptance is **also** strategy-proof for the receivers. -/
theorem isReceiverStrategyProof_deferredAcceptance_of_le_one {m n : ℕ} (h : m ≤ 1 ∨ n ≤ 1) :
    IsReceiverStrategyProof (IncompleteInstance.deferredAcceptance (m := m) (n := n)) := by
  intro I r l
  rcases h with hm | hn
  · rcases (show m = 0 ∨ m = 1 by omega) with rfl | rfl
    · cases h1 : (I.deferredAcceptance.symm r) with
      | none =>
        cases h2 : ((I.updateRecvPref r l).deferredAcceptance.symm r) with
        | none => exact le_rfl
        | some p => exact p.elim0
      | some p => exact p.elim0
    · cases h1 : I.deferredAcceptance.symm r with
      | some p =>
        have hp : p = 0 := Subsingleton.elim p 0
        subst hp
        have hmem : (0 : Fin 1) ∈ I.recvPref r :=
          (I.isIndividuallyRational_deferredAcceptance 0 r
            (I.deferredAcceptance.eq_some_iff.1 h1)).2
        cases h2 : (I.updateRecvPref r l).deferredAcceptance.symm r with
        | none => exact (I.recvRank_some_lt_none_iff r 0).2 hmem |>.le
        | some q =>
          have : q = 0 := Subsingleton.elim q 0
          subst this; exact le_rfl
      | none =>
        cases h2 : (I.updateRecvPref r l).deferredAcceptance.symm r with
        | none => exact le_rfl
        | some q =>
          have hq : q = 0 := Subsingleton.elim q 0
          subst hq
          by_cases hmem : (0 : Fin 1) ∈ I.recvPref r
          · exfalso
            have h0r : (I.updateRecvPref r l).deferredAcceptance 0 = some r :=
              (I.updateRecvPref r l).deferredAcceptance.eq_some_iff.1 h2
            have hr_mem : r ∈ I.propPref 0 :=
              (I.updateRecvPref r l).isIndividuallyRational_deferredAcceptance 0 r h0r |>.1
            have hne_none : I.propRank 0 (some r) < I.propRank 0 none :=
              (I.propRank_some_lt_none_iff 0 r).2 hr_mem
            cases h0 : I.deferredAcceptance 0 with
            | none =>
              exact I.isStable_deferredAcceptance.2 0 r
                ⟨h0 ▸ hne_none, h1 ▸ (I.recvRank_some_lt_none_iff r 0).2 hmem⟩
            | some r' =>
              have hne : r' ≠ r := by
                intro e; subst e
                have := I.deferredAcceptance.eq_some_iff.2 h0
                rw [h1] at this; exact absurd this (by simp)
              have hlt_r' : I.propRank 0 (some r') < I.propRank 0 (some r) := by
                by_contra hge
                push Not at hge
                have hgt : I.propRank 0 (some r) < I.propRank 0 (some r') :=
                  lt_of_le_of_ne hge fun e =>
                    hne (Option.some_injective _ (I.eq_of_propRank_eq hr_mem e))
                exact I.isStable_deferredAcceptance.2 0 r
                  ⟨h0 ▸ hgt, h1 ▸ (I.recvRank_some_lt_none_iff r 0).2 hmem⟩
              have hmem_r' : (0 : Fin 1) ∈ (I.updateRecvPref r l).recvPref r' := by
                change (0 : Fin 1) ∈ Function.update I.recvPref r l r'
                rw [Function.update_of_ne hne]
                exact (I.isIndividuallyRational_deferredAcceptance 0 r' h0).2
              have hr'_none : (I.updateRecvPref r l).deferredAcceptance.symm r' = none := by
                cases hx : (I.updateRecvPref r l).deferredAcceptance.symm r' with
                | none => rfl
                | some x =>
                  have hx0 : x = 0 := Subsingleton.elim x 0
                  subst hx0
                  have := (I.updateRecvPref r l).deferredAcceptance.eq_some_iff.1 hx
                  rw [h0r] at this
                  exact absurd (Option.some_injective _ this) hne.symm
              exact (I.updateRecvPref r l).isStable_deferredAcceptance.2 0 r'
                ⟨h0r ▸ hlt_r',
                  hr'_none ▸ ((I.updateRecvPref r l).recvRank_some_lt_none_iff r' 0).2 hmem_r'⟩
          · rw [IncompleteInstance.recvRank_none, IncompleteInstance.recvRank_some,
              List.idxOf_eq_length_iff.2 hmem]
  · rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
    · exact r.elim0
    · have hsr : ∀ (K : IncompleteInstance m 1),
          K.deferredAcceptance = K.receiverDeferredAcceptance := fun K => by
        refine K.isProposerOptimal_deferredAcceptance.unique
          ⟨K.isStable_receiverDeferredAcceptance, fun ν hν p => ?_⟩
        cases hνp : ν p with
        | none => exact K.propRank_le_propRank_none p _
        | some s =>
          refine not_lt.1 fun hlt => ?_
          have hs : s = 0 := Subsingleton.elim s 0
          subst hs
          have hmem : p ∈ K.recvPref 0 := (hν.1 p 0 hνp).2
          have hsym := ν.eq_some_iff.2 hνp
          have hopt := K.isReceiverOptimal_receiverDeferredAcceptance.2 ν hν 0
          rw [hsym] at hopt
          cases hR : K.receiverDeferredAcceptance.symm 0 with
          | none =>
            rw [hR] at hopt
            have := (K.recvRank_some_lt_none_iff 0 p).2 hmem
            omega
          | some q =>
            by_cases hqp : q = p
            · subst hqp
              have := K.receiverDeferredAcceptance.eq_some_iff.1 hR
              rw [this] at hlt; exact lt_irrefl _ hlt
            · have hnone : K.receiverDeferredAcceptance p = none := by
                cases hRp : K.receiverDeferredAcceptance p with
                | none => rfl
                | some t =>
                  have ht : t = 0 := Subsingleton.elim t 0
                  subst ht
                  have hqp' := K.receiverDeferredAcceptance.inj hRp
                    (K.receiverDeferredAcceptance.eq_some_iff.1 hR)
                  exact absurd hqp'.symm hqp
              have hqlt : K.recvRank 0 (some q) < K.recvRank 0 (some p) :=
                lt_of_le_of_ne (hR ▸ hopt) fun e =>
                  hqp (Option.some_injective _ (K.eq_of_recvRank_eq
                    (K.isStable_receiverDeferredAcceptance.1 q 0
                      (K.receiverDeferredAcceptance.eq_some_iff.1 hR)).2 e)).symm
              have hqm : (0 : Fin 1) ∈ K.propPref q :=
                (K.isStable_receiverDeferredAcceptance.1 q 0
                  (K.receiverDeferredAcceptance.eq_some_iff.1 hR)).1
              have hνq : ν q = none := by
                cases hνq' : ν q with
                | none => rfl
                | some t =>
                  have ht : t = 0 := Subsingleton.elim t 0
                  subst ht
                  exact absurd (ν.inj hνq' hνp) hqp
              exact hν.2 q 0 ⟨hνq ▸ (K.propRank_some_lt_none_iff q 0).2 hqm, hsym ▸ hqlt⟩
      change I.recvRank r (I.deferredAcceptance.symm r) ≤
        I.recvRank r ((I.updateRecvPref r l).deferredAcceptance.symm r)
      rw [hsr I, hsr (I.updateRecvPref r l)]
      exact isReceiverStrategyProof_receiverDeferredAcceptance I r l

end PartialMatchingMechanism

end Cslib.Algorithms.Lean.StableMatching
