/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting.Round
import Mathlib.Algebra.BigOperators.Fin

/-!
# Bounded outer double-counting controller

This is the outer step of Figures 2 and 3 in the March 31, 1999 version of
[ReinhardtAllender2000], Section 2, pp. 6–7. Given adjacency and current-round membership
callbacks, count qualifying predecessors of each vertex outside the round. Add a single tally
contribution for a positive count and flag any count greater than one. Figure 2 counts once
per qualifying predecessor, yielding the same tally whenever the tie flag is clear.

The controller returns the first bad round, or tests the target after stabilization.
In the list monad, each entry represents a successful replay, so the singleton equations in
`runController_correct` account for multiplicity even when branches return equal values.
Rejected replays contribute no list entries. The native `LogSpace.DoubleCounting` module
certifies the binary update. Callback and branch-preserving native composition are tracked in #6747.

See the checked caller in `CslibFrontierTests.LayeredDigraph`.
-/

public section

namespace Cslib.DoubleCounting

open Finset Relation

/-- The registers accumulated by the outer vertex scan. -/
structure RoundUpdate where
  /-- Count and distance sum after adding new vertices. -/
  tally : Tally
  /-- Whether some new vertex has multiple qualifying predecessors. -/
  bad : Bool

/-- Accumulate a single vertex's contribution using its predecessor count. -/
@[expose] def RoundUpdate.addVertex (a : RoundUpdate) (k predecessors : ℕ) : RoundUpdate :=
  { tally :=
      if predecessors = 0 then a.tally else ⟨a.tally.count + 1, a.tally.lengthSum + (k + 1)⟩
    bad := a.bad || decide (1 < predecessors) }

/-- The Figure 1 callback takes the radius, current tally, and queried vertex. -/
abbrev MembershipScan (m : Type → Type) (n : ℕ) := ℕ → Tally → Fin n → m Bool

private def countPredecessors {m : Type → Type} [Monad m] {n : ℕ}
    (edge : Fin n → Fin n → m Bool) (member : Fin n → m Bool) (v : Fin n) : m ℕ :=
  Fin.foldlM n (fun c u => do
    if ← edge u v then
      if ← member u then return c + 1 else return c
    else return c) 0

private def scanVertex {m : Type → Type} [Monad m] {n : ℕ}
    (edge : Fin n → Fin n → m Bool) (member : Fin n → m Bool)
    (k : ℕ) (a : RoundUpdate) (v : Fin n) : m RoundUpdate := do
  if ← member v then return a
  let predecessors ← countPredecessors edge member v
  return a.addVertex k predecessors

/-- Update the tally and check for ties by scanning vertices and their predecessors.
Only scalar registers persist across calls. -/
def scanNextRound {m : Type → Type} [Monad m] {n : ℕ}
    (edge : Fin n → Fin n → m Bool) (member : MembershipScan m n) (k : ℕ) (t : Tally) :
    m RoundUpdate :=
  Fin.foldlM n (scanVertex edge (member k t) k) ⟨t, false⟩

private theorem foldl_count {n : ℕ} (p : Fin n → Prop) [DecidablePred p] (c : ℕ) :
    Fin.foldl n (fun a i => if p i then a + 1 else a) c =
      c + ∑ i, if p i then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc, ih]
    split <;> simp [*, Nat.add_assoc]

private theorem foldl_update {n : ℕ} (p : Fin n → ℕ) (k : ℕ) (a : RoundUpdate) :
    let out := Fin.foldl n (fun a v => a.addVertex k (p v)) a
    let fresh := ∑ v, if p v = 0 then 0 else 1
    out.tally.count = a.tally.count + fresh ∧
    out.tally.lengthSum = a.tally.lengthSum + fresh * (k + 1) ∧
    (out.bad = true ↔ a.bad = true ∨ ∃ v, 1 < p v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
    obtain ⟨hc, hs, hb⟩ := ih (fun i => p i.castSucc)
    simp only [RoundUpdate.addVertex] at hc hs hb ⊢
    simp only [Bool.or_eq_true, decide_eq_true_eq, hb, Fin.exists_iff_castSucc]
    by_cases h : p (Fin.last n) = 0
    · simp [h, hc, hs]
    · simp [h, hc, hs, Nat.add_assoc, Nat.add_mul]
      tauto

private noncomputable def predecessorCount {n : ℕ} (r : Fin n → Fin n → Prop)
    (s : Fin n) (k : ℕ) (v : Fin n) : ℕ := by
  classical
  exact if v ∈ round r s k then 0 else
    (univ.filter fun u => u ∈ round r s k ∧ r u v).card

/-- With correct callback replies, the bounded scans compute the exact next tally and flag
exactly the failure of next-round uniqueness, provided the current round is unique. -/
theorem scanNextRound_correct {m : Type → Type} [Monad m] [LawfulMonad m] {n : ℕ}
    {r : Fin n → Fin n → Prop} {s : Fin n} {k : ℕ}
    {edge : Fin n → Fin n → m Bool} {member : MembershipScan m n}
    (he : ∀ u v, edge u v = pure (by classical exact decide (r u v)))
    (hm : ∀ v, member k (expected r s k) v = pure (by classical exact decide (v ∈ round r s k)))
    (hw : ∃! w, Passes r s k w) :
    ∃ a, scanNextRound edge member k (expected r s k) = pure a ∧
      a.tally = expected r s (k + 1) ∧
      (a.bad = false ↔ ∃! w, Passes r s (k + 1) w) := by
  classical
  obtain ⟨w, hpass⟩ := hw.exists
  let p := predecessorCount r s k
  let init : RoundUpdate := ⟨expected r s k, false⟩
  let a := Fin.foldl n (fun a v => a.addVertex k (p v)) init
  have hpred (v : Fin n) :
      countPredecessors edge (member k (expected r s k)) v =
        pure (univ.filter fun u => u ∈ round r s k ∧ r u v).card := by
    simp only [countPredecessors, he, hm, pure_bind]
    have hstep (c : ℕ) (u : Fin n) :
        (if decide (r u v) = true then
          if decide (u ∈ round r s k) = true then (pure (c + 1) : m ℕ) else pure c
        else pure c) = pure (if u ∈ round r s k ∧ r u v then c + 1 else c) := by
      by_cases h₁ : r u v <;> by_cases h₂ : u ∈ round r s k <;> simp [h₁, h₂]
    simp only [hstep, Fin.foldlM_pure, foldl_count, Nat.zero_add, card_eq_sum_ones, sum_filter]
  have hstep (a : RoundUpdate) (v : Fin n) :
      scanVertex edge (member k (expected r s k)) k a v = pure (a.addVertex k (p v)) := by
    rw [scanVertex, hm, pure_bind]
    simp only [decide_eq_true_eq]
    by_cases hv : v ∈ round r s k
    · simp [hv, p, predecessorCount, RoundUpdate.addVertex]
    · rw [ite_eq_right hv, hpred, pure_bind]
      simp only [p, predecessorCount, ite_eq_right hv]
  have hfront (v : Fin n) : p v ≠ 0 ↔ v ∈ frontier r w := by
    rw [mem_frontier_iff hpass]
    by_cases hv : v ∈ round r s k
    · simp [p, predecessorCount, hv]
    · change predecessorCount r s k v ≠ 0 ↔ _
      rw [predecessorCount, ite_eq_right hv, card_ne_zero]
      simp only [Finset.Nonempty, mem_filter, mem_univ, true_and, hv, not_false_eq_true, and_true,
        mem_round, reachableWithin_succ, Set.mem_union, Set.mem_ofPred_eq]
      simp only [← mem_round, hv, false_or]
  have hsum : (∑ v, if p v = 0 then 0 else 1) = (frontier r w).card := by
    have hfilter : (univ.filter fun v => p v ≠ 0) = frontier r w := by
      ext v
      simpa using hfront v
    rw [← hfilter, card_eq_sum_ones, sum_filter]
    apply sum_congr rfl
    intro v _
    by_cases h : p v = 0 <;> simp [h]
  obtain ⟨hc, hs, hb⟩ := foldl_update p k init
  refine ⟨a, ?_, ?_, ?_⟩
  · rw [scanNextRound, funext fun x => funext (hstep x), Fin.foldlM_pure]
  · rw [← nextTally_eq_expected hpass]
    cases ha : a.tally with
    | mk count lengthSum =>
      change a.tally.count = _ at hc
      change a.tally.lengthSum = _ at hs
      simp only [ha, hsum] at hc hs
      rw [hc, hs]
      rfl
  · rw [← Bool.not_eq_true, hb, existsUnique_passes_succ_iff hpass hw]
    simp only [init, Bool.false_eq_true, false_or, not_exists, Nat.not_lt]
    refine ⟨fun h v hv => ?_, fun h v => ?_⟩
    · have hpos : 0 < p v := Nat.pos_of_ne_zero ((hfront v).mpr hv)
      have hold := ((mem_frontier_iff hpass).mp hv).2
      have heq : p v = 1 := Nat.le_antisymm (h v) hpos
      simpa [p, predecessorCount, hold, card_eq_one_iff_existsUnique] using heq
    · by_cases hv : v ∈ frontier r w
      · have hold := ((mem_frontier_iff hpass).mp hv).2
        have heq : p v = 1 := by
          simpa [p, predecessorCount, hold, card_eq_one_iff_existsUnique] using h v hv
        omega
      · have hz : p v = 0 := by simpa using mt (hfront v).mp hv
        omega

/-- A terminal verdict distinguishes a tied graph from a reachability answer. -/
inductive ControllerVerdict where
  /-- The first round containing a shortest-walk tie. -/
  | bad (radius : ℕ)
  /-- Whether the target is reachable. -/
  | decided (reachable : Bool)
  deriving DecidableEq, Repr

private def runRounds {m : Type → Type} [Monad m] {n : ℕ}
    (edge : Fin n → Fin n → m Bool) (member : MembershipScan m n) (target : Fin n) :
    ℕ → ℕ → Tally → m (Option ControllerVerdict)
  | 0, _, _ => pure none
  | fuel + 1, k, t => do
    let a ← scanNextRound edge member k t
    if a.bad then return some (.bad (k + 1))
    if a.tally.count == t.count then
      return some (.decided (← member k t target))
    runRounds edge member target fuel (k + 1) a.tally

/-- Run at most one update per vertex, starting with the source alone. The correctness
theorem excludes fuel exhaustion when the callback contract holds. -/
def runController {m : Type → Type} [Monad m] {n : ℕ}
    (edge : Fin n → Fin n → m Bool) (member : MembershipScan m n) (target : Fin n) :
    m (Option ControllerVerdict) :=
  runRounds edge member target n 0 ⟨1, 0⟩

private theorem stable_of_count_eq {n : ℕ} {r : Fin n → Fin n → Prop}
    {s : Fin n} {k : ℕ}
    (h : (expected r s (k + 1)).count = (expected r s k).count) :
    reachableWithin r s k = {v | ReflTransGen r s v} := by
  have heq : round r s k = round r s (k + 1) :=
    eq_of_subset_of_card_le (fun _ hv => mem_round.mpr
      (reachableWithin_mono (Nat.le_succ k) (mem_round.mp hv))) h.le
  apply reachableWithin_eq_of_succ_eq
  ext v
  simp only [← mem_round, heq]

private theorem round_stable_of_size_le {n : ℕ} {r : Fin n → Fin n → Prop}
    {s : Fin n} {k : ℕ} (h : n ≤ k + 1) :
    round r s (k + 1) = round r s k := by
  ext v
  rw [mem_round, mem_round, reachableWithin_eq_of_card_le, reachableWithin_eq_of_card_le]
  · simpa using h
  · simpa using h.trans (Nat.le_succ (k + 1))

private theorem runRounds_correct {m : Type → Type} [Monad m] [LawfulMonad m] {n : ℕ}
    {r : Fin n → Fin n → Prop} {s target : Fin n}
    {edge : Fin n → Fin n → m Bool} {member : MembershipScan m n}
    (he : ∀ u v, edge u v = pure (by classical exact decide (r u v)))
    (hm : ∀ k, (∃! w, Passes r s k w) → ∀ v,
      member k (expected r s k) v = pure (by classical exact decide (v ∈ round r s k)))
    (fuel k : ℕ) (hbound : n ≤ k + fuel) (hpos : 0 < fuel)
    (hgood : ∀ j ≤ k, ∃! w, Passes r s j w) :
    ∃ verdict, runRounds edge member target fuel k (expected r s k) = pure (some verdict) ∧
      match verdict with
      | .bad j => (∀ i < j, ∃! w, Passes r s i w) ∧ ¬ (∃! w, Passes r s j w)
      | .decided b => (∀ j, ∃! w, Passes r s j w) ∧ (b = true ↔ ReflTransGen r s target) := by
  classical
  induction fuel generalizing k with
  | zero => omega
  | succ fuel ih =>
    have hk := hgood k le_rfl
    obtain ⟨a, ha, ht, hb⟩ := scanNextRound_correct he (hm k hk) hk
    cases hbad : a.bad with
    | true =>
      refine ⟨.bad (k + 1), by simp [runRounds, ha, hbad], fun i hi => hgood i (by omega), ?_⟩
      exact fun h => by simpa [hbad] using hb.mpr h
    | false =>
      by_cases hs : (expected r s (k + 1)).count = (expected r s k).count
      · have hstable := stable_of_count_eq hs
        refine ⟨.decided (decide (target ∈ round r s k)), ?_, ?_, ?_⟩
        · simp [runRounds, ha, hbad, ht, hs, hm k hk]
        · intro j
          rw [existsUnique_passes_iff]
          intro v hv
          have hr := reachableWithin_subset_setOf_reflTransGen (mem_round.mp hv)
          exact (existsUnique_passes_iff.mp hk) v (mem_round.mpr (hstable ▸ hr))
        · simp only [decide_eq_true_eq, mem_round, hstable, Set.mem_ofPred_eq]
      · have hsize : k + 1 < n := by
          by_contra! h
          exact hs (by simp [expected, round_stable_of_size_le h])
        have hgood' (j : ℕ) (hj : j ≤ k + 1) : ∃! w, Passes r s j w := by
          rcases Nat.eq_or_lt_of_le hj with rfl | hj
          · exact hb.mp hbad
          · exact hgood j (by omega)
        obtain ⟨verdict, hv, hspec⟩ := ih (k + 1) (by omega) (by omega) hgood'
        exact ⟨verdict, by simp [runRounds, ha, hbad, ht, hs, hv], hspec⟩

/-- Under the adjacency and unique membership-replay contracts, the controller returns the
first nonunique round, or the reachability answer when all rounds are unique. Fuel suffices
for either outcome. -/
theorem runController_correct {m : Type → Type} [Monad m] [LawfulMonad m] {n : ℕ}
    {r : Fin n → Fin n → Prop} {s target : Fin n}
    {edge : Fin n → Fin n → m Bool} {member : MembershipScan m n}
    (he : ∀ u v, edge u v = pure (by classical exact decide (r u v)))
    (hm : ∀ k, (∃! w, Passes r s k w) → ∀ v,
      member k (expected r s k) v = pure (by classical exact decide (v ∈ round r s k))) :
    ∃ verdict, runController edge member target = pure (some verdict) ∧
      match verdict with
      | .bad j => (∀ i < j, ∃! w, Passes r s i w) ∧ ¬ (∃! w, Passes r s j w)
      | .decided b => (∀ j, ∃! w, Passes r s j w) ∧ (b = true ↔ ReflTransGen r s target) := by
  have hgood (j : ℕ) (hj : j ≤ 0) : ∃! w, Passes r s j w :=
    (Nat.eq_zero_of_le_zero hj).symm ▸ existsUnique_passes_zero r s
  rw [runController, ← expected_zero r s]
  exact runRounds_correct (target := target) he hm n 0 (by simp) (Nat.zero_lt_of_lt s.isLt) hgood

end Cslib.DoubleCounting
