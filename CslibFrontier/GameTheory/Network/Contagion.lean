/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.GameTheory.Strategic.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Networked Coordination Games and Morris's 1/2 Contagion Threshold

This module formalizes the game-theoretic contagion model on locally finite graphs from
[Kleinberg2007], Section 24.2 (pp. 614–618, and Exercises 24.1–24.2, p. 632), originally due to
[Morris2000].

Each vertex of a locally finite undirected graph `G : SimpleGraph V` chooses between an old
behavior `A` (`false`) and a new behavior `B` (`true`) and plays a symmetric `2 × 2` coordination
game (`CoordinationPayoffs`) across each incident edge, summing the resulting payoffs. In the
normalized game `CoordinationPayoffs.normalized q` with parameter `q`, matching on `A` yields `q`,
matching on `B` yields `1 - q`, and mismatching yields `0` ([Kleinberg2007], pp. 614–615).
Holding other vertices fixed at adopter set `S`, choosing `B` weakly beats `A` at vertex `v` iff
`q * G.degree v ≤ (G.neighborSet v ∩ S).ncard` (breaking ties in favor of `B`, avoiding
division by zero at isolated vertices, and matching the fraction `d_v^B / d_v ≥ q` whenever
`0 < G.degree v`). Every general symmetric coordination payoff matrix with `uBA < uAA` and
`uAB < uBB` induces the exact same best-response step as the normalized game at
`threshold p = (uAA - uBA) / ((uAA - uBA) + (uBB - uAB))` ([Kleinberg2007], Exercise 24.2, p. 632).

Starting from an initial adopter set `S`, synchronous best-response dynamics iterate
`bestResponseStep G q` (`h_q`), while progressive dynamics iterate `progressiveStep G q`
(`h̄_q(X) = X ∪ h_q(X)`). A set `S` is contagious for an update rule `step` (`IsContagious`) iff
every vertex `w` eventually stays in `step^[j] S` for all sufficiently large `j` ([Kleinberg2007],
p. 615). The contagion threshold `contagionThreshold G` is the supremum of `q ∈ [0, 1]` admitting a
finite contagious set (formalizing Morris's supremum and [Kleinberg2007], p. 615, where it is
called the maximum).

## Scope notes

* For Theorem 24.2 (`contagionThreshold_le_half`), we assume `[Infinite V]` and
  `∀ v, 0 < G.degree v` (no isolated vertices, matching [Morris2000]'s nonempty neighbor-set
  assumption and [Kleinberg2007]'s neighbor-fraction wording on p. 615 and strict-majority step
  on p. 618). Under the tie-breaking rule `d_v^B ≥ q * d_v`, an isolated vertex satisfies
  `0 ≥ q * 0` for every `q`, so on `⊥ : SimpleGraph ℕ` the empty set is contagious for all `q`.
  Every connected infinite graph satisfies `∀ v, 0 < G.degree v` via
  `SimpleGraph.Preconnected.degree_pos_of_nontrivial`.
* On the two-way infinite path `intPathGraph` (`ℤ`) at `q = 1 / 2`, starting from `{0}` yields
  the parity-oscillating sets `{x | -k ≤ x ≤ k ∧ x % 2 = k % 2}` (rather than dying out at step 2
  as remarked informally in [Kleinberg2007], p. 616). Nevertheless `{0}` still fails to convert any
  vertex under `bestResponseStep`, while converting all of `ℤ` under `progressiveStep`, and
  `{0, 1}` is contagious under `bestResponseStep`, witnessing
  `contagionThreshold intPathGraph = 1 / 2`.

## Main definitions

* `Cslib.GameTheory.Network.CoordinationPayoffs`: symmetric `2 × 2` edge coordination payoffs,
  normalization (`normalized`), equivalent threshold (`threshold`), per-vertex payoffs
  (`payoff`, `payoffA`, `payoffB`), and `CostGame` embedding (`toCostGame`).
* `Cslib.GameTheory.Network.bestResponseStep`: synchronous nonprogressive update `h_q`.
* `Cslib.GameTheory.Network.progressiveStep`: synchronous progressive update `h̄_q`.
* `Cslib.GameTheory.Network.IsContagious`: eventual permanent conversion of all vertices.
* `Cslib.GameTheory.Network.contagionThreshold`: supremum threshold in `[0, 1]` admitting a finite
  contagious set.
* `Cslib.GameTheory.Network.intPathGraph`: two-way infinite path graph on `ℤ`.

## Main results

* `Cslib.GameTheory.Network.CoordinationPayoffs.bestResponseStep_eq`: reduction of arbitrary
  symmetric `2 × 2` coordination games to normalized parameter `threshold p` ([Kleinberg2007],
  Exercise 24.2, p. 632).
* `Cslib.GameTheory.Network.progressiveStep_iterate_succ`:
  `(progressiveStep G q)^[j + 1] S = S ∪ bestResponseStep G q ((progressiveStep G q)^[j] S)`
  ([Kleinberg2007], Equation (24.1), p. 617; Exercise 24.1, p. 632).
* `Cslib.GameTheory.Network.exists_finset_isContagious_bestResponseStep_iff_progressiveStep`:
  existence of a finite contagious set for `h_q` iff one exists for `h̄_q` ([Kleinberg2007],
  Theorem 24.1, p. 617; [Morris2000]).
* `Cslib.GameTheory.Network.not_isContagious_progressiveStep_of_half_lt`,
  `Cslib.GameTheory.Network.not_isContagious_bestResponseStep_of_half_lt`,
  `Cslib.GameTheory.Network.contagionThreshold_le_half`: no finite set is contagious for `q > 1/2`
  and `contagionThreshold G ≤ 1 / 2` ([Kleinberg2007], Theorem 24.2, p. 618; [Morris2000]).
* `Cslib.GameTheory.Network.contagionThreshold_intPathGraph`: tightness
  `contagionThreshold intPathGraph = 1 / 2` ([Kleinberg2007], Section 24.2, p. 616).

## References

* [Kleinberg2007] Jon Kleinberg, *Cascading Behavior in Networks: Algorithmic and Economic Issues*,
  in *Algorithmic Game Theory*, Chapter 24, pp. 613–632, 2007.
* [Morris2000] Stephen Morris, *Contagion*, Review of Economic Studies 67:57–78, 2000.
-/

public section

namespace Cslib.GameTheory.Network

/-! ## Coordination game payoffs -/

/-- Payoffs of a symmetric two-action coordination game played across each edge of a network,
where `A` (`false`) is the old behavior and `B` (`true`) is the new behavior ([Kleinberg2007],
Section 24.2, pp. 614–615; Exercise 24.2, p. 632). On an edge `(v, w)`, node `v` receives `uXY`
when `v` chooses `X` and `w` chooses `Y`. -/
structure CoordinationPayoffs where
  /-- Payoff when both endpoints choose `A`. -/
  uAA : ℝ
  /-- Payoff when the player chooses `B` and the neighbor chooses `A`. -/
  uBA : ℝ
  /-- Payoff when the player chooses `A` and the neighbor chooses `B`. -/
  uAB : ℝ
  /-- Payoff when both endpoints choose `B`. -/
  uBB : ℝ

namespace CoordinationPayoffs

/-- Strictly better payoffs for matching behaviors on each edge (`uAA > uBA` and `uBB > uAB`,
[Kleinberg2007], Exercise 24.2, p. 632). -/
@[expose] def IsCoordination (p : CoordinationPayoffs) : Prop :=
  p.uBA < p.uAA ∧ p.uAB < p.uBB

/-- The normalized coordination game with parameter `q`: matching on `A` pays `q`, matching on `B`
pays `1 - q`, and opposite behaviors pay `0` ([Kleinberg2007], Section 24.2, pp. 614–615). -/
@[expose] def normalized (q : ℝ) : CoordinationPayoffs :=
  ⟨q, 0, 0, 1 - q⟩

/-- The normalized coordination game with `0 < q < 1` satisfies `IsCoordination`. -/
theorem isCoordination_normalized {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    (normalized q).IsCoordination :=
  ⟨hq0, sub_pos.mpr hq1⟩

/-- The equivalent adoption threshold `q = (uAA - uBA) / ((uAA - uBA) + (uBB - uAB))` of a general
symmetric coordination game ([Kleinberg2007], Exercise 24.2, p. 632). -/
noncomputable def threshold (p : CoordinationPayoffs) : ℝ :=
  (p.uAA - p.uBA) / ((p.uAA - p.uBA) + (p.uBB - p.uAB))

theorem threshold_def (p : CoordinationPayoffs) :
    p.threshold = (p.uAA - p.uBA) / ((p.uAA - p.uBA) + (p.uBB - p.uAB)) := by
  rfl

@[simp] theorem threshold_normalized (q : ℝ) : (normalized q).threshold = q := by
  simp only [threshold, normalized]
  ring

theorem threshold_pos {p : CoordinationPayoffs} (hp : p.IsCoordination) : 0 < p.threshold :=
  div_pos (sub_pos.mpr hp.1) (add_pos (sub_pos.mpr hp.1) (sub_pos.mpr hp.2))

theorem threshold_lt_one {p : CoordinationPayoffs} (hp : p.IsCoordination) : p.threshold < 1 := by
  rw [threshold, div_lt_one (by linarith [hp.1, hp.2])]
  linarith [hp.2]

/-- Single-edge payoff to a player choosing `mine` against a neighbor choosing `other`
(`false` = old behavior `A`, `true` = new behavior `B`). -/
def edgePayoff (p : CoordinationPayoffs) (mine other : Bool) : ℝ :=
  match mine, other with
  | false, false => p.uAA
  | false, true => p.uAB
  | true, false => p.uBA
  | true, true => p.uBB

@[simp] theorem edgePayoff_false_false (p : CoordinationPayoffs) :
    p.edgePayoff false false = p.uAA := by rfl
@[simp] theorem edgePayoff_false_true (p : CoordinationPayoffs) :
    p.edgePayoff false true = p.uAB := by rfl
@[simp] theorem edgePayoff_true_false (p : CoordinationPayoffs) :
    p.edgePayoff true false = p.uBA := by rfl
@[simp] theorem edgePayoff_true_true (p : CoordinationPayoffs) :
    p.edgePayoff true true = p.uBB := by rfl

section SetPayoffs

variable {V : Type*} (p : CoordinationPayoffs) (G : SimpleGraph V)

/-- Payoff to vertex `v` from choosing old behavior `A` when the set of `B`-adopters is `S`. -/
noncomputable def payoffA (S : Set V) (v : V) : ℝ :=
  p.uAA * ((G.neighborSet v \ S).ncard : ℝ) + p.uAB * ((G.neighborSet v ∩ S).ncard : ℝ)

/-- Payoff to vertex `v` from choosing new behavior `B` when the set of `B`-adopters is `S`. -/
noncomputable def payoffB (S : Set V) (v : V) : ℝ :=
  p.uBA * ((G.neighborSet v \ S).ncard : ℝ) + p.uBB * ((G.neighborSet v ∩ S).ncard : ℝ)

theorem payoffA_def (S : Set V) (v : V) :
    p.payoffA G S v =
      p.uAA * ((G.neighborSet v \ S).ncard : ℝ) + p.uAB * ((G.neighborSet v ∩ S).ncard : ℝ) := by
  rfl

theorem payoffB_def (S : Set V) (v : V) :
    p.payoffB G S v =
      p.uBA * ((G.neighborSet v \ S).ncard : ℝ) + p.uBB * ((G.neighborSet v ∩ S).ncard : ℝ) := by
  rfl

@[simp] theorem normalized_payoffA (q : ℝ) (S : Set V) (v : V) :
    (normalized q).payoffA G S v = q * ((G.neighborSet v \ S).ncard : ℝ) := by
  simp only [payoffA, normalized, zero_mul, add_zero]

@[simp] theorem normalized_payoffB (q : ℝ) (S : Set V) (v : V) :
    (normalized q).payoffB G S v = (1 - q) * ((G.neighborSet v ∩ S).ncard : ℝ) := by
  simp only [payoffB, normalized, zero_mul, zero_add]

/-- Synchronous best-response update for general edge payoffs `p`: a vertex adopts `B` iff its
payoff from `B` is at least its payoff from `A` (ties broken in favor of `B`, [Kleinberg2007],
Section 24.2, p. 615 and Exercise 24.2, p. 632). -/
def bestResponseStep (S : Set V) : Set V :=
  {v | p.payoffA G S v ≤ p.payoffB G S v}

theorem mem_bestResponseStep_iff (S : Set V) (v : V) :
    v ∈ p.bestResponseStep G S ↔ p.payoffA G S v ≤ p.payoffB G S v := by
  rfl

end SetPayoffs

section GraphPayoffs

variable {V : Type*} (p : CoordinationPayoffs) (G : SimpleGraph V) [G.LocallyFinite]

/-- Total payoff of vertex `v` in the networked coordination game on `G` at strategy profile
`s : V → Bool` ([Kleinberg2007], Section 24.2, p. 615). -/
def payoff (v : V) (s : V → Bool) : ℝ :=
  ∑ w ∈ G.neighborFinset v, p.edgePayoff (s v) (s w)

theorem payoff_def (v : V) (s : V → Bool) :
    p.payoff G v s = ∑ w ∈ G.neighborFinset v, p.edgePayoff (s v) (s w) := by
  rfl

/-- The networked coordination game viewed as a strategic `CostGame` (with costs equal to negated
payoffs). -/
def toCostGame : CostGame V (fun _ => Bool) where
  cost v s := -(p.payoff G v s)

@[simp] theorem toCostGame_cost (v : V) (s : V → Bool) :
    (p.toCostGame G).cost v s = -(p.payoff G v s) := by
  rfl

private theorem card_filter_neighborFinset_eq_ncard_inter (s : V → Bool) (v : V) :
    ((G.neighborFinset v).filter (fun w => s w = true)).card =
      (G.neighborSet v ∩ {w | s w = true}).ncard := by
  rw [← Set.ncard_coe_finset]
  exact congrArg Set.ncard (Set.ext fun w => by simp [SimpleGraph.mem_neighborSet])

private theorem card_filter_neighborFinset_false_eq_ncard_sdiff (s : V → Bool) (v : V) :
    ((G.neighborFinset v).filter (fun w => s w = false)).card =
      (G.neighborSet v \ {w | s w = true}).ncard := by
  rw [← Set.ncard_coe_finset]
  exact congrArg Set.ncard (Set.ext fun w => by simp [SimpleGraph.mem_neighborSet])

private theorem payoff_update_bool [DecidableEq V] (b : Bool) (v : V) (s : V → Bool) :
    p.payoff G v (Function.update s v b) =
      p.edgePayoff b false * ((G.neighborSet v \ {w | s w = true}).ncard : ℝ) +
        p.edgePayoff b true * ((G.neighborSet v ∩ {w | s w = true}).ncard : ℝ) := by
  rw [payoff]
  refine (Finset.sum_congr
    (g := fun w => if s w = true then p.edgePayoff b true else p.edgePayoff b false) rfl
    fun w hw => ?_).trans ?_
  · rw [Function.update_self,
      Function.update_of_ne (G.ne_of_adj ((G.mem_neighborFinset v w).mp hw)).symm]
    cases s w <;> rfl
  · simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, Bool.not_eq_true,
      card_filter_neighborFinset_eq_ncard_inter, card_filter_neighborFinset_false_eq_ncard_sdiff]
    ring

/-- Evaluating `payoff` when `v` chooses `A` (`false`) against the rest of profile `s` yields
`payoffA` at `{w | s w = true}`. -/
theorem payoff_update_false [DecidableEq V] (v : V) (s : V → Bool) :
    p.payoff G v (Function.update s v false) = p.payoffA G {w | s w = true} v := by
  simpa only [payoffA, edgePayoff_false_false, edgePayoff_false_true] using
    payoff_update_bool p G false v s

/-- Evaluating `payoff` when `v` chooses `B` (`true`) against the rest of profile `s` yields
`payoffB` at `{w | s w = true}`. -/
theorem payoff_update_true [DecidableEq V] (v : V) (s : V → Bool) :
    p.payoff G v (Function.update s v true) = p.payoffB G {w | s w = true} v := by
  simpa only [payoffB, edgePayoff_true_false, edgePayoff_true_true] using
    payoff_update_bool p G true v s

/-- Every fixed point of `p.bestResponseStep G` defines a pure Nash equilibrium of the networked
coordination game `p.toCostGame G`. -/
theorem isPureNash_of_bestResponseStep_eq [DecidableEq V] {s : V → Bool}
    (h : p.bestResponseStep G {w | s w = true} = {w | s w = true}) :
    (p.toCostGame G).IsPureNash s := by
  intro v a
  simp only [toCostGame_cost, neg_le_neg_iff]
  have hiff : p.payoff G v (Function.update s v false) ≤
      p.payoff G v (Function.update s v true) ↔ s v = true := by
    simpa only [mem_bestResponseStep_iff, ← p.payoff_update_false G v s,
      ← p.payoff_update_true G v s, Set.mem_ofPred_eq] using Set.ext_iff.mp h v
  conv_rhs => rw [← Function.update_eq_self v s]
  cases a <;> cases hsv : s v <;> try exact le_rfl
  · exact hiff.mpr hsv
  · exact le_of_not_ge (mt hiff.mp (by simp [hsv]))

end GraphPayoffs

end CoordinationPayoffs

/-! ## Threshold best-response and progressive contagion dynamics -/

section Dynamics

variable {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]

private theorem ncard_neighborSet_eq_degree (v : V) :
    (G.neighborSet v).ncard = G.degree v := by
  rw [← G.coe_neighborFinset, Set.ncard_coe_finset, SimpleGraph.card_neighborFinset_eq_degree]

private theorem ncard_neighborSet_inter_add_sdiff (S : Set V) (v : V) :
    (G.neighborSet v ∩ S).ncard + (G.neighborSet v \ S).ncard = G.degree v := by
  rw [Set.ncard_inter_add_ncard_sdiff_eq_ncard (G.neighborSet v) S (G.neighborSet v).toFinite,
    ncard_neighborSet_eq_degree]

/-- Synchronous nonprogressive best-response update `h_q` on `G` with threshold `q`: vertex `v`
adopts `B` iff `q * d_v ≤ d_v^B` ([Kleinberg2007], Section 24.2, p. 615). Using the
cross-multiplied inequality matches the payoff comparison `(1 - q) * d_v^B ≥ q * d_v^A` with
ties broken in favor of `B`, without dividing by zero at isolated vertices. -/
def bestResponseStep (q : ℝ) (S : Set V) : Set V :=
  {v | q * (G.degree v : ℝ) ≤ ((G.neighborSet v ∩ S).ncard : ℝ)}

theorem mem_bestResponseStep_iff (q : ℝ) (S : Set V) (v : V) :
    v ∈ bestResponseStep G q S ↔ q * (G.degree v : ℝ) ≤ ((G.neighborSet v ∩ S).ncard : ℝ) := by
  rfl

/-- At any vertex of positive degree, `v ∈ bestResponseStep G q S` iff at least a `q` fraction of
`v`'s neighbors belong to `S` ([Kleinberg2007], Section 24.2, p. 615). -/
theorem mem_bestResponseStep_iff_div (q : ℝ) (S : Set V) {v : V} (hv : 0 < G.degree v) :
    v ∈ bestResponseStep G q S ↔ q ≤ ((G.neighborSet v ∩ S).ncard : ℝ) / (G.degree v : ℝ) := by
  rw [mem_bestResponseStep_iff, le_div_iff₀ (Nat.cast_pos.mpr hv)]

/-- Payoff derivation of `h_q`: in the normalized coordination game with parameter `q`, the
best-response update equals `bestResponseStep G q` ([Kleinberg2007], Section 24.2, p. 615). -/
theorem CoordinationPayoffs.normalized_bestResponseStep (q : ℝ) :
    (CoordinationPayoffs.normalized q).bestResponseStep G = Network.bestResponseStep G q := by
  ext S v
  simp only [CoordinationPayoffs.mem_bestResponseStep_iff, CoordinationPayoffs.normalized_payoffA,
    CoordinationPayoffs.normalized_payoffB, Network.mem_bestResponseStep_iff]
  have hdeg : ((G.neighborSet v ∩ S).ncard : ℝ) + ((G.neighborSet v \ S).ncard : ℝ) =
      (G.degree v : ℝ) := mod_cast ncard_neighborSet_inter_add_sdiff G S v
  rw [← hdeg]
  constructor <;> intro h <;> linarith

/-- **Exercise 24.2** ([Kleinberg2007], p. 632): any symmetric `2 × 2` coordination game with
`uBA < uAA` and `uAB < uBB` has the exact same best-response update map as the normalized
coordination game with parameter `q = p.threshold = (uAA - uBA) / ((uAA - uBA) + (uBB - uAB))`. -/
theorem CoordinationPayoffs.bestResponseStep_eq {p : CoordinationPayoffs} (hp : p.IsCoordination) :
    p.bestResponseStep G = Network.bestResponseStep G p.threshold := by
  ext S v
  simp only [CoordinationPayoffs.mem_bestResponseStep_iff, CoordinationPayoffs.payoffA_def,
    CoordinationPayoffs.payoffB_def, Network.mem_bestResponseStep_iff,
    CoordinationPayoffs.threshold_def]
  have hdeg : ((G.neighborSet v ∩ S).ncard : ℝ) + ((G.neighborSet v \ S).ncard : ℝ) =
      (G.degree v : ℝ) := mod_cast ncard_neighborSet_inter_add_sdiff G S v
  have hden : 0 < (p.uAA - p.uBA) + (p.uBB - p.uAB) := by linarith [hp.1, hp.2]
  rw [div_mul_eq_mul_div, div_le_iff₀ hden, ← hdeg]
  constructor <;> intro h <;> linarith

theorem bestResponseStep_mono (q : ℝ) : Monotone (bestResponseStep G q) := by
  intro S T hST v hv
  rw [mem_bestResponseStep_iff] at hv ⊢
  have hcard : (G.neighborSet v ∩ S).ncard ≤ (G.neighborSet v ∩ T).ncard :=
    Set.ncard_le_ncard (Set.inter_subset_inter_right _ hST)
      ((G.neighborSet v).toFinite.subset Set.inter_subset_left)
  exact hv.trans (Nat.cast_le.mpr hcard)

theorem bestResponseStep_antitone_threshold {q₁ q₂ : ℝ} (hq : q₁ ≤ q₂) (S : Set V) :
    bestResponseStep G q₂ S ⊆ bestResponseStep G q₁ S := by
  intro v hv
  rw [mem_bestResponseStep_iff] at hv ⊢
  exact (mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg _)).trans hv

theorem bestResponseStep_of_nonpos {q : ℝ} (hq : q ≤ 0) (S : Set V) :
    bestResponseStep G q S = Set.univ := by
  ext v
  simp only [mem_bestResponseStep_iff, Set.mem_univ, iff_true]
  exact (mul_nonpos_of_nonpos_of_nonneg hq (Nat.cast_nonneg _)).trans (Nat.cast_nonneg _)

/-- Synchronous progressive update `h̄_q(S) = S ∪ h_q(S)`: nodes already following `B` remain
with `B`, and any node with at least a `q` fraction of neighbors in `S` switches to `B`
([Kleinberg2007], Section 24.2, p. 616). -/
def progressiveStep (q : ℝ) (S : Set V) : Set V :=
  S ∪ bestResponseStep G q S

theorem progressiveStep_def (q : ℝ) (S : Set V) :
    progressiveStep G q S = S ∪ bestResponseStep G q S := by
  rfl

theorem subset_progressiveStep (q : ℝ) (S : Set V) : S ⊆ progressiveStep G q S :=
  Set.subset_union_left

theorem bestResponseStep_subset_progressiveStep (q : ℝ) (S : Set V) :
    bestResponseStep G q S ⊆ progressiveStep G q S :=
  Set.subset_union_right

theorem progressiveStep_mono (q : ℝ) : Monotone (progressiveStep G q) :=
  fun _ _ hST => Set.union_subset_union hST (bestResponseStep_mono G q hST)

theorem progressiveStep_iterate_mono (q : ℝ) (S : Set V) :
    Monotone fun j => (progressiveStep G q)^[j] S :=
  monotone_nat_of_le_succ fun _ =>
    (Function.iterate_succ_apply' ..).symm ▸ subset_progressiveStep G q _

private theorem bestResponseStep_iterate_subset_progressiveStep_iterate (q : ℝ) (S : Set V) :
    ∀ j, (bestResponseStep G q)^[j] S ⊆ (progressiveStep G q)^[j] S
  | 0 => Set.Subset.rfl
  | j + 1 => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (bestResponseStep_mono G q
        (bestResponseStep_iterate_subset_progressiveStep_iterate q S j)).trans
        (bestResponseStep_subset_progressiveStep G q _)

/-- **Equation (24.1) / Exercise 24.1** ([Kleinberg2007], Section 24.2, p. 617; Exercise 24.1,
p. 632): for every `S` and every `j ≥ 0`, iterating `progressiveStep` `j + 1` times equals
applying `bestResponseStep` once to the `j`-th progressive iterate and adjoining the initial
set `S`. -/
theorem progressiveStep_iterate_succ (q : ℝ) (S : Set V) :
    ∀ j, (progressiveStep G q)^[j + 1] S = S ∪ bestResponseStep G q ((progressiveStep G q)^[j] S)
  | 0 => rfl
  | j + 1 => by
      have hsub : bestResponseStep G q ((progressiveStep G q)^[j] S) ⊆
          bestResponseStep G q ((progressiveStep G q)^[j + 1] S) :=
        bestResponseStep_mono G q (progressiveStep_iterate_mono G q S (Nat.le_succ j))
      rw [Function.iterate_succ_apply', progressiveStep_def,
        progressiveStep_iterate_succ q S j, Set.union_assoc]
      rw [progressiveStep_iterate_succ q S j] at hsub
      rw [Set.union_eq_right.mpr hsub]

/-- A set `S` is **contagious** with respect to an update operator `step` if every vertex `w` is
eventually permanently converted: there exists `k` such that `w ∈ step^[j] S` for all `j ≥ k`
([Kleinberg2007], Section 24.2, pp. 615–616). -/
@[expose] def IsContagious (step : Set V → Set V) (S : Set V) : Prop :=
  ∀ w, ∃ k, ∀ j, k ≤ j → w ∈ step^[j] S

/-- Because iterates of `progressiveStep` are nondecreasing, `S` is progressive-contagious iff
the union of all iterates `⋃ j, (progressiveStep G q)^[j] S` is `Set.univ`. -/
theorem isContagious_progressiveStep_iff_iUnion_eq_univ (q : ℝ) (S : Set V) :
    IsContagious (progressiveStep G q) S ↔ (⋃ j, (progressiveStep G q)^[j] S) = Set.univ := by
  simp only [IsContagious, Set.eq_univ_iff_forall, Set.mem_iUnion]
  exact forall_congr' fun w => ⟨fun ⟨k, hk⟩ => ⟨k, hk k le_rfl⟩,
    fun ⟨k, hk⟩ => ⟨k, fun j hj => progressiveStep_iterate_mono G q S hj hk⟩⟩

theorem isContagious_bestResponseStep_of_le {q₁ q₂ : ℝ} (hq : q₁ ≤ q₂) {S : Set V}
    (hS : IsContagious (bestResponseStep G q₂) S) :
    IsContagious (bestResponseStep G q₁) S := by
  have hsub (j : ℕ) : (bestResponseStep G q₂)^[j] S ⊆ (bestResponseStep G q₁)^[j] S := by
    induction j with
    | zero => exact Set.Subset.rfl
    | succ j ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact (bestResponseStep_mono G q₂ ih).trans (bestResponseStep_antitone_threshold G hq _)
  exact fun w => (hS w).imp fun _ hk j hj => hsub j (hk j hj)

theorem isContagious_bestResponseStep_of_nonpos {q : ℝ} (hq : q ≤ 0) (S : Set V) :
    IsContagious (bestResponseStep G q) S := by
  intro w
  refine ⟨1, fun j hj => ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hj
  rw [Function.iterate_succ_apply', bestResponseStep_of_nonpos G hq]
  trivial

/-- Contagion equivalence for Exercise 24.2 ([Kleinberg2007], p. 632): for any symmetric
coordination payoffs `p` with `p.IsCoordination`, a set `S` is contagious under `p` iff it is
contagious under the normalized threshold `p.threshold`. -/
theorem CoordinationPayoffs.isContagious_iff {p : CoordinationPayoffs} (hp : p.IsCoordination)
    (S : Set V) :
    IsContagious (p.bestResponseStep G) S ↔
      IsContagious (Network.bestResponseStep G p.threshold) S := by
  rw [CoordinationPayoffs.bestResponseStep_eq G hp]

/-- The **contagion threshold** of a locally finite graph `G`: the supremum of thresholds
`q ∈ [0, 1]` for which there exists a finite contagious set with respect to `bestResponseStep G q`
([Kleinberg2007], Section 24.2, p. 615; [Morris2000]). -/
noncomputable def contagionThreshold : ℝ :=
  sSup {q ∈ Set.Icc (0 : ℝ) 1 | ∃ S : Finset V, IsContagious (bestResponseStep G q) (S : Set V)}

private theorem contagionSet_nonempty :
    {q ∈ Set.Icc (0 : ℝ) 1 |
      ∃ S : Finset V, IsContagious (bestResponseStep G q) (S : Set V)}.Nonempty :=
  ⟨0, ⟨⟨le_rfl, zero_le_one⟩, ∅, isContagious_bestResponseStep_of_nonpos G le_rfl _⟩⟩

private theorem contagionSet_bddAbove :
    BddAbove {q ∈ Set.Icc (0 : ℝ) 1 |
      ∃ S : Finset V, IsContagious (bestResponseStep G q) (S : Set V)} :=
  ⟨1, fun _ hq => hq.1.2⟩

theorem contagionThreshold_nonneg : 0 ≤ contagionThreshold G :=
  le_csSup (contagionSet_bddAbove G)
    ⟨⟨le_rfl, zero_le_one⟩, ∅, isContagious_bestResponseStep_of_nonpos G le_rfl _⟩

theorem contagionThreshold_le_one : contagionThreshold G ≤ 1 :=
  csSup_le (contagionSet_nonempty G) fun _ hq => hq.1.2

theorem le_contagionThreshold {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (S : Finset V)
    (hS : IsContagious (bestResponseStep G q) (S : Set V)) :
    q ≤ contagionThreshold G :=
  le_csSup (contagionSet_bddAbove G) ⟨⟨hq0, hq1⟩, S, hS⟩

/-! ## Theorem 24.1: Progressive vs. nonprogressive contagion -/

private theorem bestResponseStep_sdiff_isolated (q : ℝ) (X : Set V) :
    bestResponseStep G q (X \ {v | G.IsIsolated v}) = bestResponseStep G q X := by
  ext v
  simp only [mem_bestResponseStep_iff]
  have hinter : G.neighborSet v ∩ (X \ {u | G.IsIsolated u}) = G.neighborSet v ∩ X := by
    ext u
    simp only [Set.mem_inter_iff, SimpleGraph.mem_neighborSet, Set.mem_sdiff, Set.mem_ofPred_eq,
      and_congr_right_iff]
    intro huv
    exact ⟨fun h => h.1, fun hu => ⟨hu, huv.not_isIsolated_right⟩⟩
  rw [hinter]

private theorem bestResponseStep_sdiff_isolated_finite {q : ℝ} (hq0 : 0 < q) {X : Set V}
    (hX : (X \ {v | G.IsIsolated v}).Finite) :
    (bestResponseStep G q X \ {v | G.IsIsolated v}).Finite := by
  have hsub : bestResponseStep G q X \ {v | G.IsIsolated v} ⊆
      ⋃ u ∈ X \ {v | G.IsIsolated v}, G.neighborSet u := by
    intro v ⟨hv, hni⟩
    rw [mem_bestResponseStep_iff] at hv
    have hpos : 0 < (G.neighborSet v ∩ X).ncard :=
      Nat.cast_pos.mp ((mul_pos hq0 (Nat.cast_pos.mpr ((G.degree_pos v).mpr hni))).trans_le hv)
    obtain ⟨u, huv, huX⟩ :=
      (Set.ncard_pos ((G.neighborSet v).toFinite.subset Set.inter_subset_left)).mp hpos
    exact Set.mem_biUnion ⟨huX, huv.not_isIsolated_right⟩ huv.symm
  exact (Set.Finite.biUnion hX fun u _ => (G.neighborSet u).toFinite).subset hsub

private theorem progressiveStep_iterate_sdiff_isolated_finite {q : ℝ} (hq0 : 0 < q) (S : Finset V) :
    ∀ n, ((progressiveStep G q)^[n] (S : Set V) \ {v | G.IsIsolated v}).Finite
  | 0 => S.finite_toSet.subset Set.sdiff_subset
  | n + 1 => by
      rw [Function.iterate_succ_apply', progressiveStep, Set.union_sdiff_distrib]
      have ih := progressiveStep_iterate_sdiff_isolated_finite hq0 S n
      exact ih.union (bestResponseStep_sdiff_isolated_finite G hq0 ih)

/-- **Theorem 24.1** ([Kleinberg2007], Section 24.2, p. 617; [Morris2000]):
for any locally finite graph `G` and any threshold `q ≤ 1`, there exists a finite contagious set
with respect to the nonprogressive update `bestResponseStep G q` iff there exists one with respect
to the progressive update `progressiveStep G q`. -/
theorem exists_finset_isContagious_bestResponseStep_iff_progressiveStep {q : ℝ} (hq : q ≤ 1) :
    (∃ S : Finset V, IsContagious (bestResponseStep G q) (S : Set V)) ↔
      (∃ S : Finset V, IsContagious (progressiveStep G q) (S : Set V)) := by
  constructor
  · exact fun ⟨S, hS⟩ => ⟨S, fun w => (hS w).imp fun _ hk j hj =>
      bestResponseStep_iterate_subset_progressiveStep_iterate G q S j (hk j hj)⟩
  · rintro ⟨S, hS⟩
    by_cases hq0 : q ≤ 0
    · exact ⟨∅, isContagious_bestResponseStep_of_nonpos G hq0 _⟩
    push Not at hq0
    classical
    let closedNbhd : Finset V := S ∪ S.biUnion fun v => G.neighborFinset v
    have hreach : ∀ w ∈ closedNbhd, ∃ k, w ∈ (progressiveStep G q)^[k] (S : Set V) :=
      fun w _ => (hS w).imp fun k hk => hk k le_rfl
    choose f hf using hreach
    let ℓ : ℕ := closedNbhd.attach.sup fun x => f x.1 x.2
    have hclosed : (closedNbhd : Set V) ⊆ (progressiveStep G q)^[ℓ] (S : Set V) := by
      intro w hw
      have hle : f w hw ≤ ℓ := Finset.le_sup (f := fun x : {x // x ∈ closedNbhd} => f x.1 x.2)
        (Finset.mem_attach closedNbhd ⟨w, hw⟩)
      exact progressiveStep_iterate_mono G q (S : Set V) hle (hf w hw)
    have hstep_eq : ∀ j, ℓ ≤ j →
        (progressiveStep G q)^[j + 1] (S : Set V) =
          bestResponseStep G q ((progressiveStep G q)^[j] (S : Set V)) := by
      intro j hj
      rw [progressiveStep_iterate_succ]
      refine Set.union_eq_right.mpr fun v hv => ?_
      have hnb : G.neighborSet v ⊆ (progressiveStep G q)^[j] (S : Set V) := fun u hu =>
        progressiveStep_iterate_mono G q (S : Set V) hj (hclosed (Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨v, hv, (G.mem_neighborFinset v u).mpr hu⟩)))
      rw [mem_bestResponseStep_iff, Set.inter_eq_left.mpr hnb, ncard_neighborSet_eq_degree]
      exact mul_le_of_le_one_left (Nat.cast_nonneg _) hq
    have hTfin : ((progressiveStep G q)^[ℓ] (S : Set V) \ {v | G.IsIsolated v}).Finite :=
      progressiveStep_iterate_sdiff_isolated_finite G hq0 S ℓ
    let T : Finset V := hTfin.toFinset
    have hTcoe : (T : Set V) = (progressiveStep G q)^[ℓ] (S : Set V) \ {v | G.IsIsolated v} :=
      hTfin.coe_toFinset
    have hiter : ∀ m, (bestResponseStep G q)^[m + 1] (T : Set V) =
        (progressiveStep G q)^[ℓ + m + 1] (S : Set V) := by
      intro m
      induction m with
      | zero =>
          rw [Function.iterate_succ_apply', Function.iterate_zero_apply, add_zero, hTcoe,
            bestResponseStep_sdiff_isolated]
          exact (hstep_eq ℓ le_rfl).symm
      | succ m ih =>
          have hle_m : ℓ ≤ ℓ + m + 1 := by omega
          rw [Function.iterate_succ_apply', ih, ← hstep_eq (ℓ + m + 1) hle_m]; rfl
    refine ⟨T, fun w => ?_⟩
    obtain ⟨k, hk⟩ := hS w
    refine ⟨k + 1, fun j hj => ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hj
    rw [← Nat.add_assoc, hiter (m + k)]
    exact hk (ℓ + (m + k) + 1) (by omega)

/-- Progressive and nonprogressive contagion have the exact same contagion threshold on every
locally finite graph ([Kleinberg2007], Section 24.2, p. 617; [Morris2000]). -/
theorem contagionThreshold_eq_sSup_progressive :
    contagionThreshold G =
      sSup {q ∈ Set.Icc (0 : ℝ) 1 |
        ∃ S : Finset V, IsContagious (progressiveStep G q) (S : Set V)} := by
  exact congrArg sSup (Set.ext fun _ => and_congr_right fun hq =>
    exists_finset_isContagious_bestResponseStep_iff_progressiveStep G hq.2)

/-! ## Theorem 24.2: Morris's 1/2 contagion threshold bound -/

/-- Number of edges with one endpoint in `X` and one endpoint outside `X` (the cut size `d(X)`
of [Kleinberg2007], Section 24.2, p. 618). -/
private def edgeBoundaryCard [DecidableEq V] (X : Finset V) : ℕ :=
  ∑ v ∈ X, (G.neighborFinset v \ X).card

private theorem sum_card_inter_neighborFinset_comm [DecidableEq V] (X D : Finset V) :
    ∑ v ∈ X, (G.neighborFinset v ∩ D).card = ∑ u ∈ D, (G.neighborFinset u ∩ X).card := by
  classical
  have hcard (A B : Finset V) :
      ∑ v ∈ A, (G.neighborFinset v ∩ B).card = ∑ v ∈ A, ∑ u ∈ B, if G.Adj v u then 1 else 0 :=
    Finset.sum_congr rfl fun v _ => by
      rw [← Finset.card_filter]
      congr 1
      ext u
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_filter, and_comm]
  rw [hcard X D, hcard D X, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  simp only [SimpleGraph.adj_comm]

private theorem edgeBoundaryCard_union_add [DecidableEq V] {X D : Finset V} (hdisj : Disjoint X D) :
    edgeBoundaryCard G (X ∪ D) + ∑ u ∈ D, (G.neighborFinset u ∩ X).card =
      edgeBoundaryCard G X + ∑ u ∈ D, (G.neighborFinset u \ (X ∪ D)).card := by
  unfold edgeBoundaryCard
  rw [Finset.sum_union hdisj, ← sum_card_inter_neighborFinset_comm G X D]
  have hsplit : ∀ v ∈ X,
      (G.neighborFinset v \ (X ∪ D)).card + (G.neighborFinset v ∩ D).card =
        (G.neighborFinset v \ X).card := by
    intro v _
    have hdisj' : Disjoint (G.neighborFinset v \ (X ∪ D)) (G.neighborFinset v ∩ D) :=
      Finset.disjoint_left.2 fun w hw1 hw2 =>
        (Finset.mem_sdiff.1 hw1).2 (Finset.mem_union_right _ (Finset.mem_inter.1 hw2).2)
    rw [← Finset.card_union_of_disjoint hdisj']
    congr 1
    ext w
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    have hd : w ∈ X → w ∉ D := fun hwX => Finset.disjoint_left.mp hdisj hwX
    tauto
  have := Finset.sum_congr rfl hsplit
  rw [Finset.sum_add_distrib] at this
  omega

private theorem progressiveStep_iterate_finite {q : ℝ} (hq0 : 0 < q)
    (hdeg : ∀ v, 0 < G.degree v) (S : Finset V) (n : ℕ) :
    ((progressiveStep G q)^[n] (S : Set V)).Finite := by
  have hiso : {v : V | G.IsIsolated v} = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun v => (G.degree_pos v).mp (hdeg v)
  have h := progressiveStep_iterate_sdiff_isolated_finite G hq0 S n
  rwa [hiso, Set.sdiff_empty] at h

/-- **Theorem 24.2 (progressive form)** ([Kleinberg2007], Section 24.2, p. 618; [Morris2000]):
on any infinite locally finite graph with no isolated vertices, no finite set is contagious for
`progressiveStep G q` whenever `q > 1 / 2`. -/
theorem not_isContagious_progressiveStep_of_half_lt [Infinite V]
    (hdeg : ∀ v, 0 < G.degree v) {q : ℝ} (hq : 1 / 2 < q) (S : Finset V) :
    ¬ IsContagious (progressiveStep G q) (S : Set V) := by
  classical
  have hq0 : 0 < q := by linarith
  let Sfin : ℕ → Finset V := fun j => (progressiveStep_iterate_finite G hq0 hdeg S j).toFinset
  have hSfin_coe : ∀ j, (Sfin j : Set V) = (progressiveStep G q)^[j] (S : Set V) :=
    fun j => (progressiveStep_iterate_finite G hq0 hdeg S j).coe_toFinset
  have hSfin_sub : ∀ j, Sfin j ⊆ Sfin (j + 1) := by
    intro j
    rw [← Finset.coe_subset, hSfin_coe, hSfin_coe]
    exact progressiveStep_iterate_mono G q (S : Set V) (Nat.le_succ j)
  have hdec : ∀ j, Sfin j ≠ Sfin (j + 1) →
      edgeBoundaryCard G (Sfin (j + 1)) < edgeBoundaryCard G (Sfin j) := by
    intro j hne
    let X := Sfin j
    let D := Sfin (j + 1) \ Sfin j
    have hdisj : Disjoint X D := Finset.disjoint_sdiff
    have hunion : X ∪ D = Sfin (j + 1) := Finset.union_sdiff_of_subset (hSfin_sub j)
    have hDne : D.Nonempty :=
      Finset.nonempty_iff_ne_empty.2 fun hemp => hne (by rw [← hunion, hemp, Finset.union_empty])
    have hlt_each : ∀ u ∈ D,
        (G.neighborFinset u \ (X ∪ D)).card < (G.neighborFinset u ∩ X).card := by
      intro u hu
      have huD : u ∈ Sfin (j + 1) ∧ u ∉ Sfin j := Finset.mem_sdiff.mp hu
      have hbr : u ∈ bestResponseStep G q ((progressiveStep G q)^[j] (S : Set V)) := by
        have h1 : u ∈ (progressiveStep G q)^[j + 1] (S : Set V) := hSfin_coe (j + 1) ▸ huD.1
        rw [Function.iterate_succ_apply', progressiveStep] at h1
        exact h1.resolve_left (hSfin_coe j ▸ huD.2)
      rw [mem_bestResponseStep_iff, ← hSfin_coe] at hbr
      have hncard : (G.neighborSet u ∩ (X : Set V)).ncard = (G.neighborFinset u ∩ X).card := by
        rw [← G.coe_neighborFinset, ← Finset.coe_inter, Set.ncard_coe_finset]
      rw [hncard] at hbr
      have hdu : 0 < (G.degree u : ℝ) := Nat.cast_pos.mpr (hdeg u)
      have hmaj : G.degree u < 2 * (G.neighborFinset u ∩ X).card := by
        have := mul_lt_mul_of_pos_right hq hdu
        exact_mod_cast (by linarith : (G.degree u : ℝ) < 2 * ((G.neighborFinset u ∩ X).card : ℝ))
      have hdisj_nb : Disjoint (G.neighborFinset u ∩ X) (G.neighborFinset u \ (X ∪ D)) :=
        Finset.disjoint_left.2 fun w hw1 hw2 =>
          (Finset.mem_sdiff.1 hw2).2 (Finset.mem_union_left _ (Finset.mem_inter.1 hw1).2)
      have hcard_le :
          (G.neighborFinset u ∩ X).card + (G.neighborFinset u \ (X ∪ D)).card ≤ G.degree u := by
        rw [← Finset.card_union_of_disjoint hdisj_nb, ← G.card_neighborFinset_eq_degree]
        exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_left Finset.sdiff_subset)
      omega
    have hsum_lt :
        ∑ u ∈ D, (G.neighborFinset u \ (X ∪ D)).card < ∑ u ∈ D, (G.neighborFinset u ∩ X).card :=
      Finset.sum_lt_sum_of_nonempty hDne hlt_each
    have heq := edgeBoundaryCard_union_add G hdisj
    rw [hunion] at heq hsum_lt
    change edgeBoundaryCard G (Sfin (j + 1)) + ∑ u ∈ D, (G.neighborFinset u ∩ X).card =
      edgeBoundaryCard G (Sfin j) + ∑ u ∈ D, (G.neighborFinset u \ Sfin (j + 1)).card at heq
    omega
  have hstop : ∃ k, Sfin k = Sfin (k + 1) := by
    by_contra! hno
    have hbound : ∀ n, edgeBoundaryCard G (Sfin n) + n ≤ edgeBoundaryCard G (Sfin 0) := by
      intro n
      induction n with
      | zero => omega
      | succ n ih => linarith [hdec n (hno n)]
    linarith [hbound (edgeBoundaryCard G (Sfin 0) + 1)]
  obtain ⟨k, hk⟩ := hstop
  have hconst : ∀ m, (progressiveStep G q)^[k + m] (S : Set V) = (Sfin k : Set V) := by
    intro m
    induction m with
    | zero => exact (hSfin_coe k).symm
    | succ m ih =>
        rw [← Nat.add_assoc, Function.iterate_succ_apply', ih, hSfin_coe k,
          ← Function.iterate_succ_apply' (progressiveStep G q) k (S : Set V),
          ← hSfin_coe (k + 1), ← hSfin_coe k, hk]
  intro hcont
  obtain ⟨w, hw⟩ := Set.Infinite.exists_notMem_finset Set.infinite_univ (Sfin k)
  obtain ⟨k', hk'⟩ := hcont w
  exact hw.2 (hconst k' ▸ hk' (k + k') (Nat.le_add_left k' k) : w ∈ (Sfin k : Set V))

/-- **Theorem 24.2 (nonprogressive form)** ([Kleinberg2007], Section 24.2, p. 618; [Morris2000]):
on any infinite locally finite graph with no isolated vertices, no finite set is contagious for
`bestResponseStep G q` whenever `q > 1 / 2`. -/
theorem not_isContagious_bestResponseStep_of_half_lt [Infinite V]
    (hdeg : ∀ v, 0 < G.degree v) {q : ℝ} (hq : 1 / 2 < q) (S : Finset V) :
    ¬ IsContagious (bestResponseStep G q) (S : Set V) :=
  fun hcont => not_isContagious_progressiveStep_of_half_lt G hdeg hq S fun w =>
    (hcont w).imp fun _ hk j hj =>
      bestResponseStep_iterate_subset_progressiveStep_iterate G q S j (hk j hj)

/-- **Theorem 24.2** ([Kleinberg2007], Section 24.2, p. 618; [Morris2000]):
the contagion threshold of any infinite locally finite graph with no isolated vertices is at most
`1 / 2`. -/
theorem contagionThreshold_le_half [Infinite V] (hdeg : ∀ v, 0 < G.degree v) :
    contagionThreshold G ≤ 1 / 2 := by
  refine csSup_le (contagionSet_nonempty G) fun q ⟨_, S, hS⟩ => ?_
  by_contra! hlt
  exact not_isContagious_bestResponseStep_of_half_lt G hdeg hlt S hS

end Dynamics

/-! ## Tightness: the two-way infinite path on `ℤ` -/

/-- The two-way infinite path graph on `ℤ`: vertices `x` and `y` are adjacent iff
`y = x + 1` or `x = y + 1` ([Kleinberg2007], Section 24.2, p. 616). -/
def intPathGraph : SimpleGraph ℤ where
  Adj x y := y = x + 1 ∨ x = y + 1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by omega⟩

theorem intPathGraph_adj_iff (x y : ℤ) :
    intPathGraph.Adj x y ↔ y = x + 1 ∨ x = y + 1 := by
  rfl

instance : intPathGraph.LocallyFinite := fun x =>
  Fintype.ofFinset {x - 1, x + 1} fun y => by
    simp only [Finset.mem_insert, Finset.mem_singleton, SimpleGraph.mem_neighborSet,
      intPathGraph_adj_iff]
    omega

theorem intPathGraph_neighborFinset (x : ℤ) :
    intPathGraph.neighborFinset x = {x - 1, x + 1} := by
  ext y
  simp only [SimpleGraph.mem_neighborFinset, intPathGraph_adj_iff, Finset.mem_insert,
    Finset.mem_singleton]
  omega

@[simp] theorem intPathGraph_degree (x : ℤ) : intPathGraph.degree x = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, intPathGraph_neighborFinset,
    Finset.card_pair (by omega : x - 1 ≠ x + 1)]

theorem intPathGraph_connected : intPathGraph.Connected := by
  refine SimpleGraph.Connected.mk fun x y => ?_
  have hstep : ∀ (a : ℤ) (n : ℕ), intPathGraph.Reachable a (a + n) := by
    intro a n
    induction n with
    | zero => simp only [Nat.cast_zero, add_zero, SimpleGraph.Reachable.refl]
    | succ n ih => exact ih.trans (SimpleGraph.Adj.reachable (Or.inl (by omega)))
  by_cases hxy : x ≤ y
  · exact (by omega : x + (y - x).toNat = y) ▸ hstep x (y - x).toNat
  · exact ((by omega : y + (x - y).toNat = x) ▸ hstep y (x - y).toNat).symm

private theorem mem_bestResponseStep_intPathGraph_half_iff (S : Set ℤ) (x : ℤ) :
    x ∈ bestResponseStep intPathGraph (1 / 2) S ↔ x - 1 ∈ S ∨ x + 1 ∈ S := by
  rw [mem_bestResponseStep_iff, intPathGraph_degree]
  have hcard : (1 / 2 : ℝ) * (2 : ℕ) ≤ ((intPathGraph.neighborSet x ∩ S).ncard : ℝ) ↔
      1 ≤ (intPathGraph.neighborSet x ∩ S).ncard := by
    norm_num
  rw [hcard, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero,
    Set.ncard_pos ((intPathGraph.neighborSet x).toFinite.subset Set.inter_subset_left),
    ← intPathGraph.coe_neighborFinset, intPathGraph_neighborFinset]
  simp [Set.Nonempty, or_and_right, exists_or]

/-- On `intPathGraph` at threshold `q = 1 / 2`, one nonprogressive step expands any integer
interval `[a, b]` with at least two vertices (`a < b`) to `[a - 1, b + 1]`
([Kleinberg2007], Section 24.2, p. 616). -/
theorem bestResponseStep_intPathGraph_half_Icc {a b : ℤ} (hab : a < b) :
    bestResponseStep intPathGraph (1 / 2) (Set.Icc a b) = Set.Icc (a - 1) (b + 1) := by
  ext x
  simp only [mem_bestResponseStep_intPathGraph_half_iff, Set.mem_Icc]
  omega

/-- On `intPathGraph` at `q = 1 / 2`, `{0, 1}` is contagious under `bestResponseStep`
([Kleinberg2007], Section 24.2, p. 616). -/
theorem isContagious_intPathGraph_half_pair :
    IsContagious (bestResponseStep intPathGraph (1 / 2)) (({0, 1} : Finset ℤ) : Set ℤ) := by
  have hpair : (({0, 1} : Finset ℤ) : Set ℤ) = Set.Icc (0 : ℤ) 1 := by
    ext x
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_Icc]
    omega
  have hiter : ∀ k : ℕ,
      (bestResponseStep intPathGraph (1 / 2))^[k] (Set.Icc (0 : ℤ) 1) =
        Set.Icc (-(k : ℤ)) (1 + (k : ℤ)) := by
    intro k
    induction k with
    | zero => simp only [Function.iterate_zero_apply, Nat.cast_zero, neg_zero, add_zero]
    | succ k ih =>
        rw [Function.iterate_succ_apply', ih,
          bestResponseStep_intPathGraph_half_Icc (by omega : -(k : ℤ) < 1 + (k : ℤ))]
        push_cast
        exact congrArg₂ Set.Icc (by ring) (by ring)
  rw [hpair]
  refine fun w => ⟨w.natAbs, fun j hj => ?_⟩
  rw [hiter j, Set.mem_Icc]; omega

/-- On `intPathGraph` at `q = 1 / 2`, starting from a single node `{0}` produces the
parity-alternating sets `{x | -k ≤ x ≤ k ∧ x % 2 = k % 2}` at step `k`. -/
theorem bestResponseStep_iterate_intPathGraph_half_singleton (k : ℕ) :
    (bestResponseStep intPathGraph (1 / 2))^[k] ({0} : Set ℤ) =
      {x : ℤ | -(k : ℤ) ≤ x ∧ x ≤ (k : ℤ) ∧ x % 2 = (k : ℤ) % 2} := by
  induction k with
  | zero =>
      ext x
      simp only [Function.iterate_zero_apply, Set.mem_singleton_iff, Nat.cast_zero, neg_zero,
        Set.mem_ofPred_eq]
      omega
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      ext x
      simp only [mem_bestResponseStep_intPathGraph_half_iff, Set.mem_ofPred_eq]
      omega

/-- Starting from `{0}` on `intPathGraph` at `q = 1 / 2` is not contagious for the nonprogressive
update (no node is permanently converted because memberships alternate in parity), even though
every node is visited infinitely often. -/
theorem not_isContagious_intPathGraph_half_singleton :
    ¬ IsContagious (bestResponseStep intPathGraph (1 / 2)) ({0} : Set ℤ) := by
  intro h
  obtain ⟨k, hk⟩ := h 0
  have hmem := hk (2 * k + 1) (by omega)
  rw [bestResponseStep_iterate_intPathGraph_half_singleton] at hmem
  simp only [Set.mem_ofPred_eq] at hmem
  omega

/-- Starting from `{0}` on `intPathGraph` at `q = 1 / 2` *is* contagious for the progressive
update `progressiveStep`, showing why Theorem 24.1 must replace the seed set rather than keeping
the same set. -/
theorem isContagious_progressiveStep_intPathGraph_half_singleton :
    IsContagious (progressiveStep intPathGraph (1 / 2)) ({0} : Set ℤ) := by
  have hstep : ∀ a b : ℤ, a ≤ b →
      progressiveStep intPathGraph (1 / 2) (Set.Icc a b) = Set.Icc (a - 1) (b + 1) := by
    intro a b hab
    ext x
    simp only [progressiveStep, Set.mem_union, mem_bestResponseStep_intPathGraph_half_iff,
      Set.mem_Icc]
    omega
  have hiter : ∀ k : ℕ,
      (progressiveStep intPathGraph (1 / 2))^[k] (Set.Icc (0 : ℤ) 0) =
        Set.Icc (-(k : ℤ)) (k : ℤ) := by
    intro k
    induction k with
    | zero => simp only [Function.iterate_zero_apply, Nat.cast_zero, neg_zero]
    | succ k ih =>
        rw [Function.iterate_succ_apply', ih, hstep _ _ (by omega)]
        push_cast
        exact congrArg₂ Set.Icc (by ring) (by ring)
  rw [← Set.Icc_self (0 : ℤ)]
  refine fun w => ⟨w.natAbs, fun j hj => ?_⟩
  rw [hiter j, Set.mem_Icc]; omega

/-- **Tightness of Theorem 24.2** ([Kleinberg2007], Section 24.2, p. 616):
the contagion threshold of the two-way infinite path on `ℤ` is exactly `1 / 2`. -/
theorem contagionThreshold_intPathGraph : contagionThreshold intPathGraph = 1 / 2 := by
  refine le_antisymm ?_ ?_
  · exact contagionThreshold_le_half intPathGraph (fun x => by rw [intPathGraph_degree]; omega)
  · exact le_contagionThreshold intPathGraph (by norm_num) (by norm_num) {0, 1}
      isContagious_intPathGraph_half_pair

end Cslib.GameTheory.Network
