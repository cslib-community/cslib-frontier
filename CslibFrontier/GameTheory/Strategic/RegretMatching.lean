/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Strategic.SwapRegretDynamics
public import CslibFrontier.MachineLearning.OnlineLearning.RegretMatching
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Empirical play, internal/swap regret bridges, and Hart–Mas-Colell regret-matching dynamics

This module connects **external, internal, and swap regret** to **approximate coarse correlated and
correlated equilibria** of repeated normal-form games ([HartMasColell2000] §§2–4, pp. 1129–1139;
[BlumMansour2007AGT] §4.4, Theorems 4.12 and 4.13), extending
`CslibFrontier.GameTheory.Strategic.Correlated`, `NoRegret`, and `SwapRegretDynamics` without
duplication:

1. **Approximate coarse correlated and pairwise correlated equilibria**: complements
   `CostGame.IsApproxCorrelatedEquilibrium` (`Correlated.lean`, [BlumMansour2007AGT] Definition
   4.11) with `CostGame.IsApproxCoarseCorrelatedEquilibrium` (`ε`-CCE) and
   `CostGame.IsApproxInternalCorrelatedEquilibrium` (Hart and Mas-Colell's pairwise correlated
   `ε`-equilibrium, [HartMasColell2000] §2, p. 1129). At `ε = 0`, both reduce to their exact
   counterparts (`IsCoarseCorrelatedEquilibrium` and `IsCorrelatedEquilibrium`), while for general
   slack `ε`, swap-`ε`-CE implies internal-`ε`-CE and internal-`ε`-CE implies
   `(|S i| * ε i)`-CE (`IsApproxInternalCorrelatedEquilibrium.isApproxCorrelatedEquilibrium`).
2. **Empirical joint distribution of pure play and exact deterministic bridges**: for a pure action
   trajectory `s : ℕ → ∀ i, S i` and `0 < T`, `empiricalDist s T hT` ([HartMasColell2000] eq.
   `(2.3)`, p. 1131) is the uniform time average of the point masses at `s 0, …, s (T - 1)`. We
   prove:
   - `CostGame.timeAverage_isApproxCorrelatedEquilibrium` ([BlumMansour2007AGT] Theorem 4.12): for
     *any* sequence of joint distributions `σ t`, cumulative swap regret at most `R i` makes
     `timeAverage σ T hT` an `(R i / T)`-correlated equilibrium.
   - **Exact bidirectional characterizations (`↔`)** on `empiricalDist s T hT`:
     `empiricalDist_isApproxCorrelatedEquilibrium_iff` (average swap regret `≤ ε i` ↔ `ε`-CE),
     `empiricalDist_isApproxInternalCorrelatedEquilibrium_iff` (average pairwise internal regret
     `≤ ε i` ↔ Hart–Mas-Colell correlated `ε`-equilibrium, finite-horizon Proposition of
     [HartMasColell2000] §3, pp. 1133–1134), and
     `empiricalDist_isApproxCoarseCorrelatedEquilibrium_iff` (average external regret `≤ ε i` ↔
     `ε`-CCE).
3. **Elimination of `ε`-strictly dominated strategies** ([BlumMansour2007AGT] Theorem 4.13): if
   player `i` incurs cumulative swap regret at most `R` over `T > 0` rounds, the time-averaged
   probability mass placed on the set of `ε`-dominated actions (`0 < ε`) is at most `R / (ε * T)`
   (`CostGame.average_epsDominated_le_div`).
4. **Coupled anytime multi-player regret-matching dynamics**: unlike `hedgeProb` (`Hedge.lean`) and
   `blumMansourDynamics` (`SwapRegretDynamics.lean`), which depend on a pre-selected horizon `T`
   and require `T ≥ m_i ln m_i`, both `extRegretMatchingDynamics` ([HartMasColell2000] `(4.2)`,
   Theorem B) and `intRegretMatchingDynamics` ([HartMasColell2000] `(3.1)`, Theorem A & Corollary)
   define a **single horizon-free, parameter-free trajectory** whose product-distribution time
   average at *every* `T > 0` is respectively a `2 M √(|S i| / T)`-CCE and a
   `2 M √(|S i| (|S i| - 1) / T)`-CE (and `2 M √((|S i| - 1) / T)` pairwise correlated
   `ε`-equilibrium) whenever `|G.cost i s| ≤ M`.

## Main definitions

* `Cslib.GameTheory.empiricalDist`: the empirical joint distribution `(1 / T) ∑_{t < T} δ_{s t}` of
  a pure-play sequence ([HartMasColell2000] eq. `(2.3)`).
* `Cslib.GameTheory.CostGame.IsApproxCoarseCorrelatedEquilibrium`: `ε`-approximate coarse correlated
  equilibria.
* `Cslib.GameTheory.CostGame.IsApproxInternalCorrelatedEquilibrium`: Hart and Mas-Colell's pairwise
  correlated `ε`-equilibrium ([HartMasColell2000] §2, p. 1129).
* `Cslib.GameTheory.CostGame.IsEpsDominated`: `ε`-strict dominance of a pure strategy
  ([BlumMansour2007AGT] §4.4).
* `Cslib.GameTheory.CostGame.extRegretMatchingDynamics`,
  `Cslib.GameTheory.CostGame.intRegretMatchingDynamics`: horizon-free coupled multi-player external
  and stationary internal regret-matching dynamics.

## Main results

* `Cslib.GameTheory.CostGame.timeAverage_isApproxCorrelatedEquilibrium`: Theorem 4.12 of
  [BlumMansour2007AGT] for arbitrary joint outcome distributions.
* `Cslib.GameTheory.CostGame.empiricalDist_isApproxCorrelatedEquilibrium_iff`,
  `Cslib.GameTheory.CostGame.empiricalDist_isApproxInternalCorrelatedEquilibrium_iff`,
  `Cslib.GameTheory.CostGame.empiricalDist_isApproxCoarseCorrelatedEquilibrium_iff`: exact
  bidirectional deterministic bridges from swap, internal, and external regret to `ε`-CE, pairwise
  `ε`-CE ([HartMasColell2000] §3 Proposition), and `ε`-CCE.
* `Cslib.GameTheory.CostGame.average_epsDominated_le_div`: Theorem 4.13 of [BlumMansour2007AGT]
  bounding the average play frequency of `ε`-dominated actions by `R / (ε * T)`.
* `Cslib.GameTheory.CostGame.extRegretMatching_isApproxCoarseCorrelatedEquilibrium`: anytime
  `O(1 / √T)` convergence of coupled external regret-matching to `ε`-CCE ([HartMasColell2000]
  Theorem B).
* `Cslib.GameTheory.CostGame.intRegretMatching_isApproxInternalCorrelatedEquilibrium`,
  `Cslib.GameTheory.CostGame.intRegretMatching_isApproxCorrelatedEquilibrium`: anytime `O(1 / √T)`
  convergence of coupled stationary internal regret-matching to pairwise and swap `ε`-CE
  ([HartMasColell2000] Theorem A and Corollary).

## References

* [A. Blum and Y. Mansour, *Learning, Regret Minimization, and Equilibria*][BlumMansour2007AGT]
* [S. Hart and A. Mas-Colell, *A Simple Adaptive Procedure Leading to Correlated
  Equilibrium*][HartMasColell2000]
-/

public section

namespace Cslib.GameTheory

open Finset Function Real Cslib.MachineLearning.OnlineLearning.Experts

/-! ### Empirical joint distribution of pure play -/

section EmpiricalDist

variable {X : Type*}

/-- The **empirical joint distribution** `(1 / T) ∑_{t < T} δ_{s t}` of a pure-outcome sequence
`s : ℕ → X` over `T > 0` rounds ([HartMasColell2000] §2, eq. `(2.3)`, p. 1131). -/
noncomputable def empiricalDist (s : ℕ → X) (T : ℕ) (hT : 0 < T) : Convexity.StdSimplex ℝ X :=
  timeAverage (fun t => Convexity.StdSimplex.single (s t)) T hT

/-- Expectation under `empiricalDist s T hT` equals the sample mean `(∑ t ∈ range T, f (s t)) / T`.
-/
theorem empiricalDist_sum (s : ℕ → X) {T : ℕ} (hT : 0 < T) (f : X → ℝ) :
    (empiricalDist s T hT).weights.sum (fun x w => w * f x) = (∑ t ∈ range T, f (s t)) / T := by
  rw [empiricalDist, timeAverage_sum]
  congr 1
  refine sum_congr rfl fun t _ => ?_
  simp only [Convexity.StdSimplex.weights_single, Finsupp.sum_single_index, zero_mul, one_mul]

end EmpiricalDist

namespace CostGame

/-! ### Approximate coarse correlated and pairwise correlated equilibria -/

section ApproxEquilibria

variable {ι : Type*} {S : ι → Type*} [DecidableEq ι] (G : CostGame ι S)

/-- A finitely supported distribution `σ` on profiles is an **`ε`-approximate coarse correlated
equilibrium (`ε`-CCE)** if committing to any fixed strategy `a : S i` reduces player `i`'s expected
cost by at most `ε i`. -/
@[expose] def IsApproxCoarseCorrelatedEquilibrium (ε : ι → ℝ)
    (σ : Convexity.StdSimplex ℝ (∀ i, S i)) : Prop :=
  ∀ i (a : S i), σ.weights.sum (fun s w => w * G.cost i s)
    ≤ σ.weights.sum (fun s w => w * G.cost i (update s i a)) + ε i

/-- A finitely supported distribution `σ` on profiles is a **pairwise approximate correlated
equilibrium** (a **correlated `ε`-equilibrium** in [HartMasColell2000] §2, p. 1129; cf.
[BlumMansour2007AGT] Definition 4.10) if replacing recommendation `a` by `b` reduces player `i`'s
expected cost on the event `s i = a` by at most `ε i`. -/
@[expose] def IsApproxInternalCorrelatedEquilibrium [∀ i, DecidableEq (S i)] (ε : ι → ℝ)
    (σ : Convexity.StdSimplex ℝ (∀ i, S i)) : Prop :=
  ∀ i (a b : S i),
    σ.weights.sum (fun s w => w * if s i = a then G.cost i s else 0)
      ≤ σ.weights.sum (fun s w => w * if s i = a then G.cost i (update s i b) else 0) + ε i

variable {G}

theorem isApproxCoarseCorrelatedEquilibrium_zero_iff
    {σ : Convexity.StdSimplex ℝ (∀ i, S i)} :
    G.IsApproxCoarseCorrelatedEquilibrium 0 σ ↔ G.IsCoarseCorrelatedEquilibrium σ := by
  dsimp [IsApproxCoarseCorrelatedEquilibrium, IsCoarseCorrelatedEquilibrium]
  simp only [add_zero]

/-- Every `ε`-approximate correlated equilibrium is an `ε`-approximate coarse correlated
equilibrium, via constant switching functions `fun _ => a`. -/
theorem IsApproxCorrelatedEquilibrium.isApproxCoarseCorrelatedEquilibrium
    {ε : ι → ℝ} {σ : Convexity.StdSimplex ℝ (∀ i, S i)}
    (h : G.IsApproxCorrelatedEquilibrium ε σ) :
    G.IsApproxCoarseCorrelatedEquilibrium ε σ :=
  fun i a => h i fun _ => a

/-- Pairwise correlated `ε`-equilibrium is equivalent to bounding unilateral deviations of the form
`switchAction a b` by `ε i`. -/
theorem isApproxInternalCorrelatedEquilibrium_iff_switchAction [∀ i, DecidableEq (S i)]
    {ε : ι → ℝ} {σ : Convexity.StdSimplex ℝ (∀ i, S i)} :
    G.IsApproxInternalCorrelatedEquilibrium ε σ ↔
      ∀ i (a b : S i),
        σ.weights.sum (fun s w => w * G.cost i s) ≤
          σ.weights.sum (fun s w => w * G.cost i (update s i (switchAction a b (s i)))) + ε i := by
  have hsplit (i : ι) (a b : S i) :
      σ.weights.sum (fun s w => w * G.cost i s) =
        σ.weights.sum (fun s w => w * if s i = a then G.cost i s else 0) +
          σ.weights.sum (fun s w => w * if s i = a then 0 else G.cost i s) ∧
      σ.weights.sum (fun s w => w * G.cost i (update s i (switchAction a b (s i)))) =
        σ.weights.sum (fun s w => w * if s i = a then G.cost i (update s i b) else 0) +
          σ.weights.sum (fun s w => w * if s i = a then 0 else G.cost i s) := by
    constructor
    · rw [← Finsupp.sum_add]
      refine Finsupp.sum_congr fun s _ => ?_
      split_ifs <;> ring
    · rw [← Finsupp.sum_add]
      refine Finsupp.sum_congr fun s _ => ?_
      split_ifs with hs
      · rw [hs, switchAction_self]
        ring
      · rw [switchAction_of_ne hs, update_eq_self]
        ring
  constructor
  · intro h i a b
    obtain ⟨h1, h2⟩ := hsplit i a b
    linarith [h i a b]
  · intro h i a b
    obtain ⟨h1, h2⟩ := hsplit i a b
    linarith [h i a b]

/-- At zero slack, Hart and Mas-Colell's pairwise correlated `0`-equilibrium coincides with
`IsCorrelatedEquilibrium`. -/
theorem isApproxInternalCorrelatedEquilibrium_zero_iff [∀ i, DecidableEq (S i)]
    {σ : Convexity.StdSimplex ℝ (∀ i, S i)} :
    G.IsApproxInternalCorrelatedEquilibrium 0 σ ↔ G.IsCorrelatedEquilibrium σ := by
  rw [isCorrelatedEquilibrium_iff]
  dsimp [IsApproxInternalCorrelatedEquilibrium]
  simp only [add_zero]

/-- Every `ε`-approximate correlated equilibrium is a pairwise correlated `ε`-equilibrium. -/
theorem IsApproxCorrelatedEquilibrium.isApproxInternalCorrelatedEquilibrium
    [∀ i, DecidableEq (S i)] {ε : ι → ℝ} {σ : Convexity.StdSimplex ℝ (∀ i, S i)}
    (h : G.IsApproxCorrelatedEquilibrium ε σ) :
    G.IsApproxInternalCorrelatedEquilibrium ε σ :=
  isApproxInternalCorrelatedEquilibrium_iff_switchAction.mpr fun i a b => h i (switchAction a b)

/-- Every pairwise correlated `ε`-equilibrium is a `(|S i| * ε i)`-approximate correlated
equilibrium against all `|S i| ^ |S i|` switching functions ([BlumMansour2007AGT] Exercise 4.1). -/
theorem IsApproxInternalCorrelatedEquilibrium.isApproxCorrelatedEquilibrium
    [∀ i, DecidableEq (S i)] [∀ i, Fintype (S i)]
    {ε : ι → ℝ} {σ : Convexity.StdSimplex ℝ (∀ i, S i)}
    (h : G.IsApproxInternalCorrelatedEquilibrium ε σ) :
    G.IsApproxCorrelatedEquilibrium (fun i => Fintype.card (S i) * ε i) σ := by
  rw [isApproxCorrelatedEquilibrium_iff]
  intro i δ
  calc ∑ a, σ.weights.sum (fun s w => w * if s i = a then G.cost i s else 0)
      ≤ ∑ a, (σ.weights.sum
          (fun s w => w * if s i = a then G.cost i (update s i (δ a)) else 0) + ε i) :=
        sum_le_sum fun a _ => h i a (δ a)
    _ = (∑ a, σ.weights.sum
          (fun s w => w * if s i = a then G.cost i (update s i (δ a)) else 0)) +
          Fintype.card (S i) * ε i := by
        rw [sum_add_distrib]
        simp [sum_const, nsmul_eq_mul]

end ApproxEquilibria

/-! ### Deterministic bridges from swap, internal, and external regret to `ε`-CE and `ε`-CCE -/

section DeterministicBridges

variable {ι : Type*} {S : ι → Type*} [DecidableEq ι] {G : CostGame ι S}

/-- **Theorem 4.12** of [BlumMansour2007AGT] (§4.4) for arbitrary sequences of joint distributions:
if over `T > 0` rounds each player `i` has cumulative swap regret at most `R i`, then
`timeAverage σ T hT` is an `(R i / T)`-approximate correlated equilibrium. -/
theorem timeAverage_isApproxCorrelatedEquilibrium
    {σ : ℕ → Convexity.StdSimplex ℝ (∀ i, S i)} {T : ℕ} (hT : 0 < T) {R : ι → ℝ}
    (hR : ∀ i (δ : S i → S i),
      ∑ t ∈ range T, (σ t).weights.sum (fun s w => w * G.cost i s)
        ≤ ∑ t ∈ range T, (σ t).weights.sum (fun s w => w * G.cost i (update s i (δ (s i)))) + R i) :
    G.IsApproxCorrelatedEquilibrium (fun i => R i / T) (timeAverage σ T hT) := by
  intro i δ
  rw [timeAverage_sum, timeAverage_sum, ← add_div]
  exact div_le_div_of_nonneg_right (hR i δ) (Nat.cast_nonneg T)

/-- External-regret counterpart of `timeAverage_isApproxCorrelatedEquilibrium` (packaging
`NoRegret.timeAverage_le_add` into `IsApproxCoarseCorrelatedEquilibrium`): cumulative external
regret at most `R i` makes `timeAverage σ T hT` an `(R i / T)`-CCE. -/
theorem timeAverage_isApproxCoarseCorrelatedEquilibrium
    {σ : ℕ → Convexity.StdSimplex ℝ (∀ i, S i)} {T : ℕ} (hT : 0 < T) {R : ι → ℝ}
    (hR : ∀ i (a : S i),
      ∑ t ∈ range T, (σ t).weights.sum (fun s w => w * G.cost i s)
        ≤ ∑ t ∈ range T, (σ t).weights.sum (fun s w => w * G.cost i (update s i a)) + R i) :
    G.IsApproxCoarseCorrelatedEquilibrium (fun i => R i / T) (timeAverage σ T hT) :=
  timeAverage_le_add hT hR

/-- **Exact deterministic swap-regret bridge**: for any pure-play trajectory `s : ℕ → ∀ i, S i` and
`0 < T`, the empirical joint distribution `empiricalDist s T hT` is an `ε`-correlated equilibrium
if and only if every player `i`'s time-averaged swap regret along `s` is at most `ε i`. -/
theorem empiricalDist_isApproxCorrelatedEquilibrium_iff
    {s : ℕ → ∀ i, S i} {T : ℕ} (hT : 0 < T) {ε : ι → ℝ} :
    G.IsApproxCorrelatedEquilibrium ε (empiricalDist s T hT) ↔
      ∀ i (δ : S i → S i),
        (∑ t ∈ range T, (G.cost i (s t) - G.cost i (update (s t) i (δ (s t i))))) / T ≤ ε i := by
  have hT_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  constructor
  · intro h i δ
    have hi := h i δ
    rw [empiricalDist_sum, empiricalDist_sum] at hi
    rw [sum_sub_distrib, sub_div]
    linarith
  · intro h i δ
    have hi := h i δ
    rw [sum_sub_distrib, sub_div] at hi
    rw [empiricalDist_sum, empiricalDist_sum]
    linarith

/-- Zero-slack specialization: `empiricalDist s T hT` is an exact correlated equilibrium iff every
player has nonpositive swap regret along `s 0, …, s (T - 1)`. -/
theorem empiricalDist_isCorrelatedEquilibrium_iff {s : ℕ → ∀ i, S i} {T : ℕ} (hT : 0 < T) :
    G.IsCorrelatedEquilibrium (empiricalDist s T hT) ↔
      ∀ i (δ : S i → S i),
        ∑ t ∈ range T, G.cost i (s t) ≤ ∑ t ∈ range T, G.cost i (update (s t) i (δ (s t i))) := by
  have hT_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  rw [← isApproxCorrelatedEquilibrium_zero_iff, empiricalDist_isApproxCorrelatedEquilibrium_iff hT]
  refine forall_congr' fun i => forall_congr' fun δ => ?_
  rw [Pi.zero_apply, div_le_iff₀ hT_pos, zero_mul, sum_sub_distrib, sub_nonpos]

/-- **Finite-horizon Proposition of [HartMasColell2000]** (§3, pp. 1133–1134):
`empiricalDist s T hT` is a pairwise correlated `ε`-equilibrium if and only if every player `i`'s
time-averaged internal regret `D_T^i(a, b)` along `s` is at most `ε i` for all actions `a, b : S i`.
-/
theorem empiricalDist_isApproxInternalCorrelatedEquilibrium_iff [∀ i, DecidableEq (S i)]
    {s : ℕ → ∀ i, S i} {T : ℕ} (hT : 0 < T) {ε : ι → ℝ} :
    G.IsApproxInternalCorrelatedEquilibrium ε (empiricalDist s T hT) ↔
      ∀ i (a b : S i),
        (∑ t ∈ range T,
          if s t i = a then G.cost i (s t) - G.cost i (update (s t) i b) else 0) / T ≤ ε i := by
  have hdiff (i : ι) (a b : S i) :
      (∑ t ∈ range T, if s t i = a then G.cost i (s t) else 0) -
        (∑ t ∈ range T, if s t i = a then G.cost i (update (s t) i b) else 0) =
      ∑ t ∈ range T, if s t i = a then G.cost i (s t) - G.cost i (update (s t) i b) else 0 := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun t _ => ?_
    split_ifs <;> ring
  constructor
  · intro h i a b
    have hi := h i a b
    rw [empiricalDist_sum, empiricalDist_sum] at hi
    rw [← hdiff, sub_div]
    linarith
  · intro h i a b
    have hi := h i a b
    rw [← hdiff, sub_div] at hi
    rw [empiricalDist_sum, empiricalDist_sum]
    linarith

/-- **Exact deterministic external-regret bridge**: `empiricalDist s T hT` is an `ε`-coarse
correlated equilibrium if and only if every player `i`'s time-averaged external regret along `s` is
at most `ε i`. -/
theorem empiricalDist_isApproxCoarseCorrelatedEquilibrium_iff
    {s : ℕ → ∀ i, S i} {T : ℕ} (hT : 0 < T) {ε : ι → ℝ} :
    G.IsApproxCoarseCorrelatedEquilibrium ε (empiricalDist s T hT) ↔
      ∀ i (a : S i),
        (∑ t ∈ range T, (G.cost i (s t) - G.cost i (update (s t) i a))) / T ≤ ε i := by
  constructor
  · intro h i a
    have hi := h i a
    rw [empiricalDist_sum, empiricalDist_sum] at hi
    rw [sum_sub_distrib, sub_div]
    linarith
  · intro h i a
    have hi := h i a
    rw [sum_sub_distrib, sub_div] at hi
    rw [empiricalDist_sum, empiricalDist_sum]
    linarith

/-- Zero-slack specialization: `empiricalDist s T hT` is an exact coarse correlated equilibrium iff
every player has nonpositive external regret along `s 0, …, s (T - 1)`. -/
theorem empiricalDist_isCoarseCorrelatedEquilibrium_iff
    {s : ℕ → ∀ i, S i} {T : ℕ} (hT : 0 < T) :
    G.IsCoarseCorrelatedEquilibrium (empiricalDist s T hT) ↔
      ∀ i (a : S i),
        ∑ t ∈ range T, G.cost i (s t) ≤ ∑ t ∈ range T, G.cost i (update (s t) i a) := by
  have hT_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  rw [← isApproxCoarseCorrelatedEquilibrium_zero_iff,
    empiricalDist_isApproxCoarseCorrelatedEquilibrium_iff hT]
  refine forall_congr' fun i => forall_congr' fun a => ?_
  rw [Pi.zero_apply, div_le_iff₀ hT_pos, zero_mul, sum_sub_distrib, sub_nonpos]

/-! ### Elimination of `ε`-strictly dominated strategies (NRTV Theorem 4.13) -/

variable (G) in
/-- Strategy `a : S i` of player `i` is **`ε`-dominated** ([BlumMansour2007AGT] §4.4) if some pure
strategy `b : S i` beats `a` by at least `ε` in cost against every opponent profile. -/
@[expose] def IsEpsDominated (i : ι) (ε : ℝ) (a : S i) : Prop :=
  ∃ b : S i, ∀ s : ∀ j, S j, G.cost i (update s i b) + ε ≤ G.cost i (update s i a)

/-- **Theorem 4.13** of [BlumMansour2007AGT] (§4.4): if player `i` incurs cumulative swap regret at
most `R` over `T > 0` rounds of a joint outcome sequence `σ`, then the time-averaged probability
mass that player `i` places on any finite set `D` of `ε`-dominated strategies (`0 < ε`) is at most
`R / (ε * T)`. -/
theorem average_epsDominated_le_div [∀ j, DecidableEq (S j)]
    {σ : ℕ → Convexity.StdSimplex ℝ (∀ j, S j)} {T : ℕ} (hT : 0 < T) {i : ι} {ε R : ℝ}
    (hε : 0 < ε) {D : Finset (S i)} (hD : ∀ a ∈ D, G.IsEpsDominated i ε a)
    (hR : ∀ δ : S i → S i,
      ∑ t ∈ range T, (σ t).weights.sum (fun s w => w * G.cost i s) ≤
        ∑ t ∈ range T, (σ t).weights.sum (fun s w => w * G.cost i (update s i (δ (s i)))) + R) :
    (∑ t ∈ range T, (σ t).weights.sum (fun s w => w * if s i ∈ D then 1 else 0)) / T ≤
      R / (ε * T) := by
  let δ : S i → S i := fun a => if ha : a ∈ D then (hD a ha).choose else a
  have hpoint : ∀ s : ∀ j, S j,
      ε * (if s i ∈ D then 1 else 0) ≤ G.cost i s - G.cost i (update s i (δ (s i))) := fun s => by
    by_cases hs : s i ∈ D
    · rw [ite_eq_left hs, mul_one]
      have hdom := (hD (s i) hs).choose_spec s
      rw [update_eq_self] at hdom
      have hδ : δ (s i) = (hD (s i) hs).choose := dite_eq_left hs
      rw [hδ]
      linarith
    · rw [ite_eq_right hs, mul_zero]
      have hδ : δ (s i) = s i := dite_eq_right hs
      rw [hδ, update_eq_self, sub_self]
  have hround : ∀ t,
      ε * (σ t).weights.sum (fun s w => w * if s i ∈ D then 1 else 0) ≤
        (σ t).weights.sum (fun s w => w * G.cost i s) -
          (σ t).weights.sum (fun s w => w * G.cost i (update s i (δ (s i)))) := fun t => by
    rw [Finsupp.mul_sum, ← Finsupp.sum_sub]
    refine Finsupp.sum_le_sum fun s _ => ?_
    have hw : 0 ≤ (σ t).weights s := (σ t).nonneg s
    have hp := mul_le_mul_of_nonneg_left (hpoint s) hw
    linarith
  have hsum : ε * ∑ t ∈ range T, (σ t).weights.sum (fun s w => w * if s i ∈ D then 1 else 0) ≤
      R := by
    rw [mul_sum]
    have h1 := sum_le_sum fun t (_ : t ∈ range T) => hround t
    rw [sum_sub_distrib] at h1
    linarith [hR δ]
  have hT_pos : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  rw [div_le_div_iff₀ hT_pos (mul_pos hε hT_pos)]
  have heq : (∑ t ∈ range T, (σ t).weights.sum (fun s w => w * if s i ∈ D then 1 else 0)) *
      (ε * T) =
      (ε * ∑ t ∈ range T, (σ t).weights.sum (fun s w => w * if s i ∈ D then 1 else 0)) * T := by
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right hsum hT_pos.le

end DeterministicBridges

/-! ### Coupled anytime multi-player regret-matching dynamics -/

section RegretMatchingDynamics

set_option linter.unusedDecidableInType false

variable {ι : Type*} {S : ι → Type*} [DecidableEq ι] [Fintype ι] [∀ i, Fintype (S i)]
  (G : CostGame ι S)

/-- Coupled horizon-free **Blackwell external regret-matching dynamics** ([HartMasColell2000]
§4(c), eqs. `(4.2a)`–`(4.2b)`, Theorem B, p. 1139): in round `t`, each player `i` runs
`regretMatchingProb` against its realized expected cost vectors from rounds `< t`. -/
noncomputable def extRegretMatchingDynamics : ℕ → ∀ i, S i → ℝ :=
  WellFounded.fix Nat.lt_wfRel.wf fun t p i =>
    regretMatchingProb (fun s c => if h : s < t then G.deviationCost (p s h) i c else 0) t

private theorem extRegretMatchingDynamics_eq (t : ℕ) (i : ι) :
    G.extRegretMatchingDynamics t i =
      regretMatchingProb
        (fun s c => if _h : s < t then G.deviationCost (G.extRegretMatchingDynamics s) i c else 0)
        t := by
  rw [extRegretMatchingDynamics, WellFounded.fix_eq]

/-- Each player in `extRegretMatchingDynamics` runs the single-learner `regretMatchingProb` against
its realized expected cost sequence. -/
theorem extRegretMatchingDynamics_eq_regretMatchingProb (t : ℕ) (i : ι) :
    G.extRegretMatchingDynamics t i =
      regretMatchingProb (fun s c => G.deviationCost (G.extRegretMatchingDynamics s) i c) t := by
  rw [extRegretMatchingDynamics_eq]
  refine regretMatchingProb_congr fun s hs => ?_
  ext c
  simp only [hs, dite_eq_left]

theorem extRegretMatchingDynamics_nonneg (t : ℕ) (i : ι) (a : S i) :
    0 ≤ G.extRegretMatchingDynamics t i a := by
  rw [extRegretMatchingDynamics_eq_regretMatchingProb]
  exact regretMatchingProb_nonneg _ _ _

theorem sum_extRegretMatchingDynamics [∀ i, Nonempty (S i)] (t : ℕ) (i : ι) :
    ∑ a, G.extRegretMatchingDynamics t i a = 1 := by
  rw [extRegretMatchingDynamics_eq_regretMatchingProb]
  exact sum_regretMatchingProb _ _

/-- Outcome distribution in round `t` of `extRegretMatchingDynamics`. -/
noncomputable def extRegretMatchingDist [∀ i, Nonempty (S i)] (t : ℕ) :
    Convexity.StdSimplex ℝ (∀ i, S i) :=
  productDist (G.extRegretMatchingDynamics_nonneg t) (G.sum_extRegretMatchingDynamics t)

variable [∀ i, DecidableEq (S i)]

/-- Coupled horizon-free **Hart–Mas-Colell stationary internal regret-matching dynamics**
([HartMasColell2000] §3, eq. `(3.1)`, Theorem A and Corollary, pp. 1133–1134): in round `t`, each
player `i` runs `internalRegretMatchingProb` against its realized expected cost vectors from rounds
`< t`. -/
noncomputable def intRegretMatchingDynamics : ℕ → ∀ i, S i → ℝ :=
  WellFounded.fix Nat.lt_wfRel.wf fun t p i =>
    internalRegretMatchingProb (fun s c => if h : s < t then G.deviationCost (p s h) i c else 0) t

private theorem intRegretMatchingDynamics_eq (t : ℕ) (i : ι) :
    G.intRegretMatchingDynamics t i =
      internalRegretMatchingProb
        (fun s c => if _h : s < t then G.deviationCost (G.intRegretMatchingDynamics s) i c else 0)
        t := by
  rw [intRegretMatchingDynamics, WellFounded.fix_eq]

/-- Each player in `intRegretMatchingDynamics` runs the single-learner `internalRegretMatchingProb`
against its realized expected cost sequence. -/
theorem intRegretMatchingDynamics_eq_internalRegretMatchingProb (t : ℕ) (i : ι) :
    G.intRegretMatchingDynamics t i =
      internalRegretMatchingProb
        (fun s c => G.deviationCost (G.intRegretMatchingDynamics s) i c) t := by
  rw [intRegretMatchingDynamics_eq]
  refine internalRegretMatchingProb_congr fun s hs => ?_
  ext c
  simp only [hs, dite_eq_left]

variable [∀ i, Nonempty (S i)]

theorem intRegretMatchingDynamics_nonneg (t : ℕ) (i : ι) (a : S i) :
    0 ≤ G.intRegretMatchingDynamics t i a := by
  rw [intRegretMatchingDynamics_eq_internalRegretMatchingProb]
  exact internalRegretMatchingProb_nonneg _ _ _

theorem sum_intRegretMatchingDynamics (t : ℕ) (i : ι) :
    ∑ a, G.intRegretMatchingDynamics t i a = 1 := by
  rw [intRegretMatchingDynamics_eq_internalRegretMatchingProb]
  exact sum_internalRegretMatchingProb _ _

/-- Outcome distribution in round `t` of `intRegretMatchingDynamics`. -/
noncomputable def intRegretMatchingDist (t : ℕ) : Convexity.StdSimplex ℝ (∀ i, S i) :=
  productDist (G.intRegretMatchingDynamics_nonneg t) (G.sum_intRegretMatchingDynamics t)

variable {G}

omit [∀ i, DecidableEq (S i)] in
/-- **Anytime `O(1 / √T)` convergence of external regret-matching to `ε`-CCE** ([HartMasColell2000]
§4(c), Theorem B, p. 1139): if game costs satisfy `|G.cost i s| ≤ M` (`0 ≤ M`), then at *every*
horizon `T > 0` (without any lower bound on `T`), the time average of `extRegretMatchingDist` is a
`(fun i => 2 * M * √(|S i| / T))`-approximate coarse correlated equilibrium. -/
theorem extRegretMatching_isApproxCoarseCorrelatedEquilibrium {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ i s, |G.cost i s| ≤ M) {T : ℕ} (hT : 0 < T) :
    G.IsApproxCoarseCorrelatedEquilibrium
      (fun i => 2 * M * √(Fintype.card (S i) / T))
      (timeAverage G.extRegretMatchingDist T hT) := by
  have hT' : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hslack : (fun i => 2 * M * √(Fintype.card (S i) / T)) =
      fun i => (2 * M * √((T : ℝ) * Fintype.card (S i))) / T := by
    ext i
    rw [mul_div_assoc (2 * M), Real.sqrt_mul_div_self hT']
  rw [hslack]
  refine timeAverage_isApproxCoarseCorrelatedEquilibrium hT fun i a => ?_
  have hbd := regretMatching_externalRegret_le_of_abs_le
    (ℓ := fun s c => G.deviationCost (G.extRegretMatchingDynamics s) i c)
    (T := T) hM
    (fun s _ b => G.abs_deviationCost_le (G.extRegretMatchingDynamics_nonneg s)
      (G.sum_extRegretMatchingDynamics s) (hc i) b) a
  simp only [← G.extRegretMatchingDynamics_eq_regretMatchingProb, externalRegretOf,
    sum_sub_distrib] at hbd
  have hL : ∑ t ∈ range T, (G.extRegretMatchingDist t).weights.sum (fun s w => w * G.cost i s) =
      ∑ t ∈ range T, ∑ b, G.extRegretMatchingDynamics t i b *
        G.deviationCost (G.extRegretMatchingDynamics t) i b := by
    refine sum_congr rfl fun t _ => ?_
    rw [extRegretMatchingDist, productDist_sum,
      ← sum_mul_deviationCost G _ (G.sum_extRegretMatchingDynamics t i)]
  have hR : ∑ t ∈ range T, (G.extRegretMatchingDist t).weights.sum
        (fun s w => w * G.cost i (update s i a)) =
      ∑ t ∈ range T, G.deviationCost (G.extRegretMatchingDynamics t) i a := by
    refine sum_congr rfl fun t _ => ?_
    rw [extRegretMatchingDist, productDist_sum, deviationCost_def]
  rw [hL, hR, mul_comm (T : ℝ) (Fintype.card (S i))]
  linarith

private theorem abs_deviationCost_sub_le {M : ℝ} (hc : ∀ i s, |G.cost i s| ≤ M)
    (s : ℕ) (i : ι) (c d : S i) :
    |G.deviationCost (G.intRegretMatchingDynamics s) i c -
      G.deviationCost (G.intRegretMatchingDynamics s) i d| ≤ 2 * M := by
  have hc1 := G.abs_deviationCost_le (G.intRegretMatchingDynamics_nonneg s)
    (G.sum_intRegretMatchingDynamics s) (hc i) c
  have hd1 := G.abs_deviationCost_le (G.intRegretMatchingDynamics_nonneg s)
    (G.sum_intRegretMatchingDynamics s) (hc i) d
  calc |G.deviationCost (G.intRegretMatchingDynamics s) i c -
          G.deviationCost (G.intRegretMatchingDynamics s) i d|
      ≤ |G.deviationCost (G.intRegretMatchingDynamics s) i c| +
          |-G.deviationCost (G.intRegretMatchingDynamics s) i d| := abs_add_le _ _
    _ ≤ M + M := by rw [abs_neg]; exact add_le_add hc1 hd1
    _ = 2 * M := by ring

/-- **Quantitative Theorem A and Corollary** of [HartMasColell2000] (§3, pp. 1133–1134, 1138): if
`|G.cost i s| ≤ M` (`0 ≤ M`), then at *every* horizon `T > 0`, the time average of
`intRegretMatchingDist` is a `(fun i => 2 * M * √((|S i| - 1) / T))` pairwise correlated
`ε`-equilibrium. -/
theorem intRegretMatching_isApproxInternalCorrelatedEquilibrium {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ i s, |G.cost i s| ≤ M) {T : ℕ} (hT : 0 < T) :
    G.IsApproxInternalCorrelatedEquilibrium
      (fun i => 2 * M * √((Fintype.card (S i) - 1 : ℕ) / T))
      (timeAverage G.intRegretMatchingDist T hT) := by
  have hT' : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  intro i a b
  rw [timeAverage_sum, timeAverage_sum]
  have hbd := internalRegretMatching_pairInternalRegret_le
    (ℓ := fun s c => G.deviationCost (G.intRegretMatchingDynamics s) i c)
    (T := T) (by positivity) (fun s _ c d => abs_deviationCost_sub_le hc s i c d) a b
  simp only [← G.intRegretMatchingDynamics_eq_internalRegretMatchingProb, pairInternalRegret,
    mul_sub, sum_sub_distrib] at hbd
  have hL : ∑ t ∈ range T, (G.intRegretMatchingDist t).weights.sum
        (fun s w => w * if s i = a then G.cost i s else 0) =
      ∑ t ∈ range T, G.intRegretMatchingDynamics t i a *
        G.deviationCost (G.intRegretMatchingDynamics t) i a := by
    refine sum_congr rfl fun t _ => ?_
    rw [intRegretMatchingDist, productDist_sum]
    have heq : (∑ s, productWeight (G.intRegretMatchingDynamics t) s *
          if s i = a then G.cost i s else 0) =
        ∑ s, productWeight (G.intRegretMatchingDynamics t) s *
          if s i = a then G.cost i (update s i a) else 0 := by
      refine sum_congr rfl fun s _ => ?_
      split_ifs with hs
      · rw [← hs, update_eq_self]
      · rfl
    rw [heq, sum_ite_productWeight G (G.intRegretMatchingDynamics t)
      (G.sum_intRegretMatchingDynamics t i) a a]
  have hR : ∑ t ∈ range T, (G.intRegretMatchingDist t).weights.sum
        (fun s w => w * if s i = a then G.cost i (update s i b) else 0) =
      ∑ t ∈ range T, G.intRegretMatchingDynamics t i a *
        G.deviationCost (G.intRegretMatchingDynamics t) i b := by
    refine sum_congr rfl fun t _ => ?_
    rw [intRegretMatchingDist, productDist_sum,
      sum_ite_productWeight G (G.intRegretMatchingDynamics t)
        (G.sum_intRegretMatchingDynamics t i) a b]
  rw [hL, hR]
  dsimp only
  have hscale : 2 * M * √((Fintype.card (S i) - 1 : ℕ) / T) =
      (2 * M * √((Fintype.card (S i) - 1 : ℕ) * T)) / T := by
    rw [mul_div_assoc (2 * M), mul_comm ((Fintype.card (S i) - 1 : ℕ) : ℝ) T,
      Real.sqrt_mul_div_self hT']
  rw [hscale, ← add_div]
  exact div_le_div_of_nonneg_right (by linarith) hT'.le

/-- **Anytime `O(1 / √T)` convergence of Hart–Mas-Colell stationary regret-matching to `ε`-CE**
(full swap-regret correlated equilibrium, [BlumMansour2007AGT] Definition 4.11 & Theorem 4.12): if
`|G.cost i s| ≤ M` (`0 ≤ M`), then at *every* horizon `T > 0`, the time average of
`intRegretMatchingDist` is a `(fun i => 2 * M * √(|S i| * (|S i| - 1) / T))`-approximate correlated
equilibrium. -/
theorem intRegretMatching_isApproxCorrelatedEquilibrium {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ i s, |G.cost i s| ≤ M) {T : ℕ} (hT : 0 < T) :
    G.IsApproxCorrelatedEquilibrium
      (fun i => 2 * M * √(Fintype.card (S i) * (Fintype.card (S i) - 1 : ℕ) / T))
      (timeAverage G.intRegretMatchingDist T hT) := by
  have hT' : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hslack :
      (fun i => 2 * M * √(Fintype.card (S i) * (Fintype.card (S i) - 1 : ℕ) / T)) =
        fun i =>
          (2 * M * √((T : ℝ) * (Fintype.card (S i) * (Fintype.card (S i) - 1 : ℕ)))) / T := by
    ext i
    rw [mul_div_assoc (2 * M), Real.sqrt_mul_div_self hT']
  rw [hslack]
  refine timeAverage_productDist_isApproxCorrelatedEquilibrium G hT
    G.intRegretMatchingDynamics_nonneg G.sum_intRegretMatchingDynamics fun i δ => ?_
  have hbd := internalRegretMatching_swapRegret_le
    (ℓ := fun s c => G.deviationCost (G.intRegretMatchingDynamics s) i c)
    (T := T) (by positivity) (fun s _ c d => abs_deviationCost_sub_le hc s i c d) δ
  simp only [← G.intRegretMatchingDynamics_eq_internalRegretMatchingProb, swapRegretOf,
    mul_sub, sum_sub_distrib] at hbd
  have hcomm : (T : ℝ) * (Fintype.card (S i) * (Fintype.card (S i) - 1 : ℕ)) =
      Fintype.card (S i) * (Fintype.card (S i) - 1 : ℕ) * T := by ring
  rw [hcomm]
  linarith

end RegretMatchingDynamics

end CostGame

end Cslib.GameTheory
