/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.BinPacking.BrownLiang
public import CslibFrontier.Algorithms.Lean.BinPacking.OnlineLowerBound
public import CslibFrontier.DataStructure.Online.Basic

/-!
# Online bin packing in the competitive-analysis framework

This file makes online bin packing with capacity `C` an instance of the competitive-analysis
framework `Cslib.DataStructure.Online.Problem` (`problem`). The state is the list of bins,
starting empty, and a request is an item of size at most `C`. A step puts the item at the end of
an existing bin with room for it, or into a new last bin, and costs `1` exactly when it opens a
bin. These are the steps of `onlineInsert` (`problem_validStep_iff`).

A schedule's cost is then its number of bins, and its final state packs the requests
(`scheduleCost_eq_length_finalState`, `isPacking_finalState`). Conversely every packing yields a
schedule costing at most its number of bins (`exists_validSchedule_of_isPacking`): the schedule
fills the packing's bins in the order in which their first items arrive. So the optimal offline
cost is the least number of bins of a packing.

Every online packer is a deterministic strategy (`OnlinePacker.toDetStrategy`) whose cost on a
request list is the number of bins of `OnlinePacker.run` (`OnlinePacker.cost_toDetStrategy`).
Conversely every deterministic strategy has the same cost as some online packer on every request
list (`exists_onlinePacker_cost_eq`), because its next state is always the result of
`onlineInsert` for some choice of bin, and its memory is a function of the requests seen.

So lower bounds against online packers transfer to the framework
(`exists_validSchedule_ratio_violation`). From Yao's bound
`OnlinePacker.exists_ratio_violation_of_lt` and the Brown–Liang bound
`OnlinePacker.brown_liang_exists_ratio_violation_of_lt`: for every deterministic strategy, every
ratio `p / q` below `3/2` (in capacity `41`), resp. below `56029 / 36379` (in capacity
`3263441`), and every additive constant `b`, some request list and valid offline schedule satisfy
`p * OPT + b < q * ALG` (`yao_exists_validSchedule_ratio_violation`,
`brown_liang_exists_validSchedule_ratio_violation`). Since `b` is arbitrary, these bound the
asymptotic ratio. `DetStrategy.IsCompetitive c b` takes an integer ratio `c`, so in its terms the
bounds say only that no deterministic strategy is `(c, b)`-competitive for `c ≤ 1`
(`not_isCompetitive_of_two_mul_lt`); the rational form above is the full statement.

## Main definitions

* `Cslib.Algorithms.Lean.BinPacking.problem`: online bin packing as an `Online.Problem`.
* `Cslib.Algorithms.Lean.BinPacking.OnlinePacker.toDetStrategy`: an online packer as a
  deterministic strategy.

## Main results

* `Cslib.Algorithms.Lean.BinPacking.problem_validStep_iff`: the steps are those of
  `onlineInsert`.
* `Cslib.Algorithms.Lean.BinPacking.isPacking_finalState` and
  `Cslib.Algorithms.Lean.BinPacking.scheduleCost_eq_length_finalState`: a schedule ends in a
  packing whose number of bins is its cost.
* `Cslib.Algorithms.Lean.BinPacking.exists_validSchedule_of_isPacking`: every packing gives a
  schedule costing at most its number of bins.
* `Cslib.Algorithms.Lean.BinPacking.OnlinePacker.cost_toDetStrategy`: the strategy of an online
  packer costs the number of bins of its packing.
* `Cslib.Algorithms.Lean.BinPacking.exists_onlinePacker_cost_eq`: every deterministic strategy has
  the cost of an online packer.
* `Cslib.Algorithms.Lean.BinPacking.exists_validSchedule_ratio_violation`: lower bounds against
  online packers hold against deterministic strategies.
* `Cslib.Algorithms.Lean.BinPacking.yao_exists_validSchedule_ratio_violation` and
  `Cslib.Algorithms.Lean.BinPacking.brown_liang_exists_validSchedule_ratio_violation`: no
  deterministic strategy has ratio below `3/2`, resp. `56029 / 36379`, with any additive constant.
* `Cslib.Algorithms.Lean.BinPacking.not_isCompetitive_of_two_mul_lt`: the same for the
  integer ratios of `DetStrategy.IsCompetitive`.
-/

public section

namespace Cslib.Algorithms.Lean.BinPacking

open Cslib.DataStructure.Online List

/-- Online bin packing with capacity `C` as an `Online.Problem`. The state is the list of bins,
starting with no bins; a request is an item of size at most `C`. A step puts the item at the end
of an existing bin with room for it, or into a new last bin. It costs the number of bins it opens:
`1` for a new bin and `0` otherwise. -/
abbrev problem (C : ℕ) : Problem where
  State := List (List ℕ)
  Req := {a : ℕ // a ≤ C}
  ValidInit bins := bins = []
  ValidStep bins a bins' :=
    (∃ (i : ℕ) (hi : i < bins.length), bins[i].sum + a.1 ≤ C ∧
      bins' = bins.set i (bins[i] ++ [a.1])) ∨ bins' = bins ++ [[a.1]]
  stepCost bins _ bins' := bins'.length - bins.length

/-! ### Steps -/

private theorem onlineInsert_none (C a : ℕ) :
    ∀ bins : List (List ℕ), onlineInsert C a none bins = bins ++ [[a]]
  | [] => rfl
  | b :: bs => by simp [onlineInsert, onlineInsert_none C a bs]

private theorem onlineInsert_some_of_lt {C a : ℕ} :
    ∀ {i : ℕ} {bins : List (List ℕ)} (hi : i < bins.length), bins[i].sum + a ≤ C →
      onlineInsert C a (some i) bins = bins.set i (bins[i] ++ [a])
  | 0, b :: bs, _, h => by
    simp only [getElem_cons_zero] at h
    simp [onlineInsert, h]
  | i + 1, b :: bs, hi, h => by
    simp only [onlineInsert, set_cons_succ, getElem_cons_succ]
    rw [onlineInsert_some_of_lt (Nat.lt_of_succ_lt_succ hi) h]

private theorem onlineInsert_some_of_not {C a : ℕ} :
    ∀ {i : ℕ} {bins : List (List ℕ)}, ¬ (∃ hi : i < bins.length, bins[i].sum + a ≤ C) →
      onlineInsert C a (some i) bins = bins ++ [[a]]
  | _, [], _ => rfl
  | 0, b :: bs, h => by
    simp only [length_cons, Nat.zero_lt_succ, getElem_cons_zero, exists_true_left] at h
    simp [onlineInsert, h, onlineInsert_none]
  | i + 1, b :: bs, h => by
    simp only [length_cons, Nat.add_lt_add_iff_right, getElem_cons_succ] at h
    simp [onlineInsert, onlineInsert_some_of_not h]

/-- The steps of `problem C` are those of `onlineInsert`, for some choice of bin. -/
theorem problem_validStep_iff {C : ℕ} {bins bins' : List (List ℕ)} {a : (problem C).Req} :
    (problem C).ValidStep bins a bins' ↔ ∃ o, bins' = onlineInsert C a.1 o bins := by
  constructor
  · rintro (⟨i, hi, hfit, rfl⟩ | rfl)
    · exact ⟨some i, (onlineInsert_some_of_lt hi hfit).symm⟩
    · exact ⟨none, (onlineInsert_none C a.1 bins).symm⟩
  · rintro ⟨_ | i, rfl⟩
    · exact Or.inr (onlineInsert_none C a.1 bins)
    · by_cases h : ∃ hi : i < bins.length, bins[i].sum + a.1 ≤ C
      · obtain ⟨hi, hfit⟩ := h
        exact Or.inl ⟨i, hi, hfit, onlineInsert_some_of_lt hi hfit⟩
      · exact Or.inr (onlineInsert_some_of_not h)

/-! ### Schedules and packings -/

private theorem validSchedule_facts {C : ℕ} {s : (problem C).State}
    {reqs : List (problem C).Req} {ss : List (problem C).State}
    (hv : (problem C).ValidSchedule s reqs ss) :
    ((problem C).finalState s ss).flatten ~ s.flatten ++ reqs.map Subtype.val ∧
      ((∀ b ∈ s, b.sum ≤ C) → ∀ b ∈ (problem C).finalState s ss, b.sum ≤ C) ∧
      (problem C).scheduleCost s reqs ss + s.length =
        ((problem C).finalState s ss).length := by
  induction hv using Problem.ValidSchedule.induction (P := problem C) with
  | nil => simp [Problem.finalState, Problem.scheduleCost]
  | cons s r rs s' ss hstep _ ih =>
    obtain ⟨o, ho⟩ := problem_validStep_iff.1 hstep
    have hlen : s.length ≤ s'.length := by
      rcases hstep with ⟨i, hi, -, rfl⟩ | rfl <;> simp
    refine ⟨?_, fun h => ih.2.1 (ho ▸ sum_le_of_mem_onlineInsert r.2 h), ?_⟩
    · refine ih.1.trans ?_
      rw [ho]
      simpa using ((flatten_onlineInsert_perm C r.1 o s).trans
        (perm_append_singleton _ _).symm).append_right (rs.map Subtype.val)
    · have e : (problem C).scheduleCost s (r :: rs) (s' :: ss) =
          s'.length - s.length + (problem C).scheduleCost s' rs ss := rfl
      have e2 : (problem C).finalState s (s' :: ss) = (problem C).finalState s' ss := rfl
      rw [e, e2, ← ih.2.2]
      omega

/-- A schedule of `problem C` from no bins ends in a packing of the requests. -/
theorem isPacking_finalState {C : ℕ} {reqs : List (problem C).Req}
    {ss : List (problem C).State} (hv : (problem C).ValidSchedule [] reqs ss) :
    IsPacking C (reqs.map Subtype.val) ((problem C).finalState [] ss) :=
  ⟨by simpa using (validSchedule_facts hv).1, (validSchedule_facts hv).2.1 (by simp)⟩

/-- A schedule of `problem C` from no bins costs the number of bins it ends with. -/
theorem scheduleCost_eq_length_finalState {C : ℕ} {reqs : List (problem C).Req}
    {ss : List (problem C).State} (hv : (problem C).ValidSchedule [] reqs ss) :
    (problem C).scheduleCost [] reqs ss = ((problem C).finalState [] ss).length := by
  simpa using (validSchedule_facts hv).2.2

private theorem perm_cons_flatten_set {L : List (List ℕ)} {i : ℕ} (hi : i < L.length) {a : ℕ}
    (ha : a ∈ L[i]) : a :: (L.set i (L[i].erase a)).flatten ~ L.flatten := by
  have hL : L = L.take i ++ L[i] :: L.drop (i + 1) := by
    rw [getElem_cons_drop, take_append_drop]
  rw [set_eq_take_append_cons_drop, ite_eq_left_iff.2 fun h => absurd hi h]
  conv_rhs => rw [hL]
  simp only [flatten_append, flatten_cons]
  refine perm_middle.symm.trans (Perm.append_left _ ?_)
  exact ((perm_cons_erase ha).symm.append_right _)

/-- Building a schedule from a packing. The current bins are `SR.map Prod.fst`; the second
component of each pair holds the items still to come for that bin, and `N` the bins still to
open. -/
private theorem exists_validSchedule_aux {C : ℕ} :
    ∀ (reqs : List (problem C).Req) (SR : List (List ℕ × List ℕ)) (N : List (List ℕ)),
      (∀ p ∈ SR, p.1.sum + p.2.sum ≤ C) → (∀ n ∈ N, n.sum ≤ C) →
      (SR.map Prod.snd ++ N).flatten ~ reqs.map Subtype.val →
      ∃ ss, (problem C).ValidSchedule (SR.map Prod.fst) reqs ss ∧
        ((problem C).finalState (SR.map Prod.fst) ss).length ≤ SR.length + N.length
  | [], SR, N, _, _, _ => ⟨[], trivial, by simp [Problem.finalState]⟩
  | r :: reqs, SR, N, hSR, hN, hperm => by
    have hr : r.1 ∈ (SR.map Prod.snd ++ N).flatten := hperm.mem_iff.2 (by simp)
    obtain ⟨t, ht, hrt⟩ := mem_flatten.1 hr
    rcases mem_append.1 ht with ht | ht
    · obtain ⟨i, hi, hti⟩ := mem_iff_getElem.1 ht
      rw [length_map] at hi
      have hti' : SR[i].2 = t := by simpa using hti
      subst hti'
      set SR' := SR.set i (SR[i].1 ++ [r.1], SR[i].2.erase r.1) with hSR'
      have hfit : SR[i].1.sum + r.1 ≤ C :=
        (Nat.add_le_add_left (le_sum_of_mem hrt) _).trans (hSR _ (getElem_mem hi))
      obtain ⟨ss, hv, hlen⟩ := exists_validSchedule_aux reqs SR' N
        (fun p hp => by
          rcases mem_or_eq_of_mem_set hp with hp | rfl
          · exact hSR p hp
          · have := sum_erase hrt
            have := hSR _ (getElem_mem hi)
            simp only [sum_append, sum_cons, sum_nil]
            omega)
        hN
        (by
          refine Perm.cons_inv (a := r.1) ?_
          have h1 := perm_cons_flatten_set (L := SR.map Prod.snd) (i := i) (by simpa using hi)
            (by simpa using hrt)
          refine Perm.trans ?_ (hperm.trans (by simp))
          simpa [hSR', map_set, flatten_append] using h1.append_right N.flatten)
      refine ⟨SR'.map Prod.fst :: ss, ⟨Or.inl ⟨i, by simpa using hi, by simpa using hfit, ?_⟩, hv⟩,
        hlen.trans_eq (by simp [hSR'])⟩
      simp [hSR', map_set]
    · set SR' := SR ++ [([r.1], t.erase r.1)] with hSR'
      obtain ⟨ss, hv, hlen⟩ := exists_validSchedule_aux reqs SR' (N.erase t)
        (fun p hp => by
          rcases mem_append.1 hp with hp | hp
          · exact hSR p hp
          · obtain rfl := mem_singleton.1 hp
            have := sum_erase hrt
            have := hN t ht
            simp only [sum_cons, sum_nil]
            omega)
        (fun n hn => hN n (mem_of_mem_erase hn))
        (by
          refine Perm.cons_inv (a := r.1) ?_
          refine Perm.trans ?_ (hperm.trans (by simp))
          have hNt := ((perm_cons_erase ht).flatten).symm
          simp only [hSR', map_append, map_cons, map_nil, flatten_append, flatten_cons,
            flatten_nil, append_nil, append_assoc]
          refine perm_middle.symm.trans (Perm.append_left _ ?_)
          refine Perm.trans ?_ hNt
          simpa using (perm_cons_erase hrt).symm.append_right (N.erase t).flatten)
      refine ⟨SR'.map Prod.fst :: ss, ⟨Or.inr (by simp [hSR']), hv⟩, hlen.trans_eq ?_⟩
      have := length_erase_of_mem ht
      have : 0 < N.length := length_pos_of_mem ht
      simp only [hSR', length_append, length_cons, length_nil]
      omega

/-- **Packings give schedules.** For every packing `Q` of the requests, some schedule of
`problem C` costs at most `Q.length`. -/
theorem exists_validSchedule_of_isPacking {C : ℕ} {reqs : List (problem C).Req}
    {Q : List (List ℕ)} (hQ : IsPacking C (reqs.map Subtype.val) Q) :
    ∃ ss, (problem C).ValidSchedule [] reqs ss ∧
      (problem C).scheduleCost [] reqs ss ≤ Q.length := by
  obtain ⟨ss, hv, hlen⟩ :=
    exists_validSchedule_aux reqs [] Q (by simp) hQ.sum_le (by simpa using hQ.perm)
  exact ⟨ss, hv, by simpa [scheduleCost_eq_length_finalState hv] using hlen⟩

/-! ### Online packers and deterministic strategies -/

/-- An online packer as a deterministic strategy of `problem C`: from the requests seen so far
and the current bins, it applies `onlineInsert` with the bin `A.place` chooses. -/
@[expose] def OnlinePacker.toDetStrategy {C : ℕ} (A : OnlinePacker C) :
    DetStrategy (problem C) :=
  DetStrategy.ofHistory
    (fun _ hist bins a => onlineInsert C a.1 (A.place (hist.map Subtype.val) bins a.1) bins)
    fun _ _ _ => problem_validStep_iff.2 ⟨_, rfl⟩

private theorem curState_runMem_toDetStrategy {C : ℕ} (A : OnlinePacker C) (s₀ : List (List ℕ)) :
    ∀ (reqs hist : List (problem C).Req) (bins : List (List ℕ)),
      (A.toDetStrategy.runMem ⟨s₀, hist, bins⟩ reqs).curState =
        A.runFrom (hist.map Subtype.val) bins (reqs.map Subtype.val)
  | [], _, _ => rfl
  | r :: reqs, hist, bins => (curState_runMem_toDetStrategy A s₀ reqs (hist ++ [r]) _).trans
    (by simp [OnlinePacker.runFrom])

private theorem cost_eq_length {C : ℕ} (S : DetStrategy (problem C))
    (reqs : List (problem C).Req) :
    S.cost [] reqs = (S.project (S.runMem (S.init []) reqs)).length := by
  rw [DetStrategy.cost, scheduleCost_eq_length_finalState (S.validSchedule_states rfl reqs),
    DetStrategy.states, ← S.finalState_statesFrom, (S.valid_init (s₀ := []) rfl).2]

/-- The strategy of an online packer costs the number of bins of the packing it builds. -/
theorem OnlinePacker.cost_toDetStrategy {C : ℕ} (A : OnlinePacker C)
    (reqs : List (problem C).Req) :
    A.toDetStrategy.cost [] reqs = (A.run (reqs.map Subtype.val)).length := by
  rw [cost_eq_length]
  exact congrArg length (curState_runMem_toDetStrategy A [] reqs [] [])

private theorem runMem_append {P : Problem} (S : DetStrategy P) (m : S.Mem) :
    ∀ l₁ l₂ : List P.Req, S.runMem m (l₁ ++ l₂) = S.runMem (S.runMem m l₁) l₂
  | [], _ => rfl
  | r :: l₁, l₂ => runMem_append S (S.step m r) l₁ l₂

/-- **Deterministic strategies are online packers.** Every deterministic strategy of
`problem C` has the cost of some online packer on every request list. -/
theorem exists_onlinePacker_cost_eq {C : ℕ} (S : DetStrategy (problem C)) :
    ∃ A : OnlinePacker C, ∀ reqs, S.cost [] reqs = (A.run (reqs.map Subtype.val)).length := by
  classical
  let lift : List ℕ → List (problem C).Req :=
    filterMap fun a => if h : a ≤ C then some (⟨a, h⟩ : (problem C).Req) else none
  have hlift : ∀ hs : List (problem C).Req, lift (hs.map Subtype.val) = hs := by
    intro hs
    induction hs with
    | nil => rfl
    | cons r hs ih =>
      simp only [lift, map_cons, filterMap_cons, r.2, ↓reduceDIte, Subtype.coe_eta] at ih ⊢
      exact congrArg (r :: ·) ih
  let A : OnlinePacker C := ⟨fun hist bins a =>
    if h : a ≤ C then
      if hx : ∃ o, S.project (S.step (S.runMem (S.init []) (lift hist)) ⟨a, h⟩) =
          onlineInsert C a o bins then hx.choose else none
    else none⟩
  have key : ∀ (reqs hs : List (problem C).Req), S.ValidMem (S.runMem (S.init []) hs) →
      A.runFrom (hs.map Subtype.val) (S.project (S.runMem (S.init []) hs))
        (reqs.map Subtype.val) = S.project (S.runMem (S.init []) (hs ++ reqs)) := by
    intro reqs
    induction reqs with
    | nil => simp [OnlinePacker.runFrom]
    | cons r reqs ih =>
      intro hs hm
      obtain ⟨hm', hstep⟩ := S.valid_step r hm
      have hx := problem_validStep_iff.1 hstep
      have hplace : onlineInsert C r.1 (A.place (hs.map Subtype.val)
          (S.project (S.runMem (S.init []) hs)) r.1) (S.project (S.runMem (S.init []) hs)) =
          S.project (S.runMem (S.init []) (hs ++ [r])) := by
        simp only [A, r.2, hx, ↓reduceDIte, hlift, Subtype.coe_eta]
        exact hx.choose_spec.symm.trans (by rw [runMem_append]; rfl)
      have := ih (hs ++ [r]) (by rw [runMem_append]; exact hm')
      simp only [map_append, map_cons, map_nil, append_assoc, cons_append, nil_append] at this
      simp only [map_cons, OnlinePacker.runFrom, hplace, this]
  refine ⟨A, fun reqs => ?_⟩
  rw [cost_eq_length]
  have h := key reqs [] (S.valid_init (s₀ := []) rfl).1
  have h0 : S.project (S.runMem (S.init []) []) = [] := (S.valid_init (s₀ := []) rfl).2
  simp only [map_nil, nil_append] at h
  rw [h0] at h
  exact congrArg length h.symm

/-! ### Non-competitiveness -/

/-- **Lower bounds transfer.** If every online packer uses more than `p / q` times the bins of
some packing, plus `b / q`, then so does every deterministic strategy of `problem C` against
some valid offline schedule. -/
theorem exists_validSchedule_ratio_violation {C p q b : ℕ} (S : DetStrategy (problem C))
    (h : ∀ A : OnlinePacker C, ∃ (l : List ℕ) (Q : List (List ℕ)), IsPacking C l Q ∧
      p * Q.length + b < q * (A.run l).length) :
    ∃ reqs offStates, (problem C).ValidSchedule [] reqs offStates ∧
      p * (problem C).scheduleCost [] reqs offStates + b < q * S.cost [] reqs := by
  obtain ⟨A, hA⟩ := exists_onlinePacker_cost_eq S
  obtain ⟨l, Q, hQ, hlt⟩ := h A
  let reqs : List (problem C).Req := l.attach.map fun a => ⟨a.1, hQ.le_of_mem a.2⟩
  have hreqs : reqs.map Subtype.val = l := by simp [reqs]
  obtain ⟨ss, hv, hc⟩ := exists_validSchedule_of_isPacking (hreqs ▸ hQ)
  refine ⟨reqs, ss, hv, ?_⟩
  rw [hA, hreqs]
  have := Nat.mul_le_mul_left p hc
  omega

/-- **Yao's lower bound in the framework.** For every deterministic strategy of `problem 41`,
every ratio `p / q < 3/2` and every additive constant `b`, some request list and valid offline
schedule satisfy `p * OPT + b < q * ALG`. -/
theorem yao_exists_validSchedule_ratio_violation (S : DetStrategy (problem 41)) {p q : ℕ}
    (hpq : 2 * p < 3 * q) (b : ℕ) :
    ∃ reqs offStates, (problem 41).ValidSchedule [] reqs offStates ∧
      p * (problem 41).scheduleCost [] reqs offStates + b < q * S.cost [] reqs :=
  exists_validSchedule_ratio_violation S fun A =>
    let ⟨l, Q, hQ, _, h⟩ := A.exists_ratio_violation_of_lt hpq b
    ⟨l, Q, hQ, h⟩

/-- **The Brown–Liang lower bound in the framework**, with the constant `56029 / 36379`. For every
deterministic strategy of `problem 3263441`, every ratio `p / q < 56029 / 36379` and every
additive constant `b`, some request list and valid offline schedule satisfy
`p * OPT + b < q * ALG`. -/
theorem brown_liang_exists_validSchedule_ratio_violation (S : DetStrategy (problem 3263441))
    {p q : ℕ} (hpq : 36379 * p < 56029 * q) (b : ℕ) :
    ∃ reqs offStates, (problem 3263441).ValidSchedule [] reqs offStates ∧
      p * (problem 3263441).scheduleCost [] reqs offStates + b < q * S.cost [] reqs :=
  exists_validSchedule_ratio_violation S fun A =>
    let ⟨l, Q, hQ, _, h⟩ := A.brown_liang_exists_ratio_violation_of_lt hpq b
    ⟨l, Q, hQ, h⟩

/-- No deterministic strategy of `problem 41` is `(c, b)`-competitive for an integer ratio
`c < 3/2` and any additive constant `b`. The ratio of `DetStrategy.IsCompetitive` is an integer, so
this is the case `c ≤ 1` of `yao_exists_validSchedule_ratio_violation`. -/
theorem not_isCompetitive_of_two_mul_lt (S : DetStrategy (problem 41)) {c : ℕ}
    (hc : 2 * c < 3) (b : ℕ) : ¬ S.IsCompetitive c b := fun h => by
  obtain ⟨reqs, offStates, hv, hlt⟩ :=
    yao_exists_validSchedule_ratio_violation S (q := 1) (by omega) b
  have := h [] rfl reqs offStates hv
  omega

end Cslib.Algorithms.Lean.BinPacking
