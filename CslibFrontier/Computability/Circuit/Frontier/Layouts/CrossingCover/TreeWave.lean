/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.CrossingCover.Submodular
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.CrossingCover.CoverLifting
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.CrossingCover.GaussianComparison
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.CrossingCover.AR2Density
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.CrossingCover.AlternatingSum
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Radial Gaussian wave processes on finite cubic graphs

For a finite cubic simple graph `H` on vertex type `V`, radius `R : ℕ`, and regularization
parameter `ε ∈ [0, 1]`, this module defines the pushed radial non-backtracking walk distribution
`pushedProb H R v x` and the unit-norm row vectors `waveRow H R ε v : V ⊕ V → ℝ`. The resulting
centered Gaussian wave process `waveScore H R ε g v = ∑ z, waveRow H R ε v z * g z` drives the
asymptotic upper bound on the expected minimum crossing vertex cover of `H`.

## Main definitions

* `Cslib.Circuits.Frontier.CrossingCover.nbCount`: number of non-backtracking walks of length `k`
  between two vertices.
* `Cslib.Circuits.Frontier.CrossingCover.shellNorm`: normalizing factor `1 + 3 * R / 2` for radial
  shells up to radius `R`.
* `Cslib.Circuits.Frontier.CrossingCover.pushedProb`: normalized non-backtracking walk kernel on
  `H` up to radius `R`.
* `Cslib.Circuits.Frontier.CrossingCover.waveRow`,
  `Cslib.Circuits.Frontier.CrossingCover.waveScore`: unit-norm row vectors and centered Gaussian
  wave field.
* `Cslib.Circuits.Frontier.CrossingCover.treeCovLimit`,
  `Cslib.Circuits.Frontier.CrossingCover.treeOverlap`: exact covariance formula on high-girth
  cubic graphs and its `R → ∞` limit `(1 + d / 3) * 2 ^ (-d / 2)`.
* `Cslib.Circuits.Frontier.CrossingCover.ar2StepMap`,
  `Cslib.Circuits.Frontier.CrossingCover.ar2AltProb`: stationary AR(2) Gaussian realization and
  its alternating-sign orthant probability.

## Main results

* `Cslib.Circuits.Frontier.CrossingCover.nbCount_symm`,
  `Cslib.Circuits.Frontier.CrossingCover.sum_nbCount_eq`,
  `Cslib.Circuits.Frontier.CrossingCover.nbCount_lift_fiber_sum`: basic symmetries, counts, and
  covering-lift fiber identities for non-backtracking walks.
* `Cslib.Circuits.Frontier.CrossingCover.waveRow_cov_cover_le_base`: fiberwise Cauchy–Schwarz
  comparison showing covering lifts have pointwise smaller or equal covariance than base graphs.
* `Cslib.Circuits.Frontier.CrossingCover.tendsto_treeOverlap`,
  `Cslib.Circuits.Frontier.CrossingCover.waveRow_inner_eq_treeOverlap`: exact covariance calculation
  on high-girth cubic graphs and its `R → ∞` limit.
* `Cslib.Circuits.Frontier.CrossingCover.ar2AltProb_eq_altPathProb`: the alternating-sign orthant
  probability of the Gaussian AR(2) process is the density integral `altPathProb` of
  `CrossingCover.AR2Density`.
* `Cslib.Circuits.Frontier.CrossingCover.exists_degThree_star_bound`,
  `Cslib.Circuits.Frontier.CrossingCover.exists_nbWalk_prob_close`: uniform convergence lemmas for
  high-girth cubic graphs.
* `Cslib.Circuits.Frontier.CrossingCover.exists_wave_params_expected_crossingCover_le`: combined
  expectation upper bound valid simultaneously for every finite cubic simple graph and every
  threshold.
-/

public section

namespace Cslib.Circuits.Frontier.CrossingCover

open Finset Function MeasureTheory ProbabilityTheory Real Filter
open scoped NNReal ENNReal Topology

/-! ### Non-backtracking walk reversal, concatenation, and counting -/

section NBWalkHelpers

variable {V : Type*} {H : SimpleGraph V}

/-- Reverse a walk of length `k`. -/
private def revWalk (k : ℕ) (w : Fin (k + 1) → V) : Fin (k + 1) → V :=
  fun i => w (Fin.rev i)

private theorem revWalk_revWalk (k : ℕ) (w : Fin (k + 1) → V) :
    revWalk k (revWalk k w) = w := by
  ext i
  simp [revWalk]

private theorem revWalk_zero (k : ℕ) (w : Fin (k + 1) → V) :
    revWalk k w 0 = w (Fin.last k) := by
  simp [revWalk]

private theorem revWalk_last (k : ℕ) (w : Fin (k + 1) → V) :
    revWalk k w (Fin.last k) = w 0 := by
  simp [revWalk]

private theorem isNBWalk_revWalk {k : ℕ} {w : Fin (k + 1) → V} (hw : IsNBWalk H k w) :
    IsNBWalk H k (revWalk k w) := by
  refine ⟨fun i => ?_, fun i hi => ?_⟩
  · have hi_lt : i.val < k := i.isLt
    have hadj := (hw.adj_step (i := k - 1 - i.val) (by omega)).symm
    have h1 : (Fin.rev i.castSucc).val = k - 1 - i.val + 1 := by
      simp [Fin.val_rev]; omega
    have h2 : (Fin.rev i.succ).val = k - 1 - i.val := by
      simp [Fin.val_rev]; omega
    change H.Adj (w (Fin.rev i.castSucc)) (w (Fin.rev i.succ))
    rwa [show Fin.rev i.castSucc = ⟨k - 1 - i.val + 1, by omega⟩ from Fin.ext h1,
      show Fin.rev i.succ = ⟨k - 1 - i.val, by omega⟩ from Fin.ext h2]
  · have hne := (hw.ne_two_step (i := k - (i + 2)) (by omega)).symm
    have h1 : (Fin.rev (⟨i, by omega⟩ : Fin (k + 1))).val = k - (i + 2) + 2 := by
      simp [Fin.val_rev]; omega
    have h2 : (Fin.rev (⟨i + 2, by omega⟩ : Fin (k + 1))).val = k - (i + 2) := by
      simp [Fin.val_rev]
    change w (Fin.rev ⟨i, by omega⟩) ≠ w (Fin.rev ⟨i + 2, by omega⟩)
    rwa [show Fin.rev (⟨i, by omega⟩ : Fin (k + 1)) =
        ⟨k - (i + 2) + 2, by omega⟩ from Fin.ext h1,
      show Fin.rev (⟨i + 2, by omega⟩ : Fin (k + 1)) =
        ⟨k - (i + 2), by omega⟩ from Fin.ext h2]

/-- Concatenate two walks `w₁` (length `j₁`) and `w₂` (length `j₂`) along `w₁ (last j₁) = w₂ 0`. -/
private def concatWalk (j₁ j₂ : ℕ) (w₁ : Fin (j₁ + 1) → V) (w₂ : Fin (j₂ + 1) → V) :
    Fin (j₁ + j₂ + 1) → V :=
  fun i => if h : i.val ≤ j₁ then w₁ ⟨i.val, by omega⟩ else w₂ ⟨i.val - j₁, by omega⟩

private theorem concatWalk_le {j₁ j₂ : ℕ} {w₁ : Fin (j₁ + 1) → V} {w₂ : Fin (j₂ + 1) → V}
    (k : ℕ) (hk : k ≤ j₁) :
    concatWalk j₁ j₂ w₁ w₂ ⟨k, by omega⟩ = w₁ ⟨k, by omega⟩ := by
  simp [concatWalk, hk]

private theorem concatWalk_ge {j₁ j₂ : ℕ} {w₁ : Fin (j₁ + 1) → V} {w₂ : Fin (j₂ + 1) → V}
    (hjoin : w₁ (Fin.last j₁) = w₂ 0) (k : ℕ) (hk1 : j₁ ≤ k) (hk2 : k ≤ j₁ + j₂) :
    concatWalk j₁ j₂ w₁ w₂ ⟨k, by omega⟩ = w₂ ⟨k - j₁, by omega⟩ := by
  by_cases heq : k = j₁
  · subst heq
    simp only [concatWalk, le_refl, ↓reduceDIte]
    simpa [Fin.last, Nat.sub_self] using hjoin
  · have hnot : ¬(k ≤ j₁) := by omega
    simp [concatWalk, hnot]

private theorem isNBWalk_concatWalk {j₁ j₂ : ℕ} {w₁ : Fin (j₁ + 1) → V} {w₂ : Fin (j₂ + 1) → V}
    (h1 : IsNBWalk H j₁ w₁) (h2 : IsNBWalk H j₂ w₂)
    (hjoin : w₁ (Fin.last j₁) = w₂ 0)
    (hnb : ∀ (_ : 0 < j₁) (_ : 0 < j₂), w₁ ⟨j₁ - 1, by omega⟩ ≠ w₂ ⟨1, by omega⟩) :
    IsNBWalk H (j₁ + j₂) (concatWalk j₁ j₂ w₁ w₂) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨i, hi⟩
    by_cases hlt : i + 1 ≤ j₁
    · rw [show (⟨i, hi⟩ : Fin (j₁ + j₂)).castSucc = ⟨i, by omega⟩ from rfl,
          show (⟨i, hi⟩ : Fin (j₁ + j₂)).succ = ⟨i + 1, by omega⟩ from rfl,
          concatWalk_le i (by omega), concatWalk_le (i + 1) hlt]
      exact h1.adj_step (by omega)
    · rw [show (⟨i, hi⟩ : Fin (j₁ + j₂)).castSucc = ⟨i, by omega⟩ from rfl,
          show (⟨i, hi⟩ : Fin (j₁ + j₂)).succ = ⟨i + 1, by omega⟩ from rfl,
          concatWalk_ge hjoin i (by omega) (by omega),
          concatWalk_ge hjoin (i + 1) (by omega) (by omega)]
      have hadj := h2.adj_step (i := i - j₁) (by omega)
      have hidx : i + 1 - j₁ = i - j₁ + 1 := by omega
      rwa [show (⟨i + 1 - j₁, by omega⟩ : Fin (j₂ + 1)) =
        ⟨i - j₁ + 1, by omega⟩ from Fin.ext hidx]
  · intro i hi
    rcases lt_or_ge (i + 2) (j₁ + 1) with hle | hgt
    · rw [concatWalk_le i (by omega), concatWalk_le (i + 2) (by omega)]
      exact h1.ne_two_step (by omega)
    · rcases lt_or_ge i j₁ with hlt | hge
      · have hi_eq : i = j₁ - 1 := by omega
        have hj1 : 0 < j₁ := by omega
        have hj2 : 0 < j₂ := by omega
        rw [concatWalk_le i (by omega), concatWalk_ge hjoin (i + 2) (by omega) (by omega)]
        rw [show (⟨i, by omega⟩ : Fin (j₁ + 1)) = ⟨j₁ - 1, by omega⟩ from Fin.ext hi_eq,
          show (⟨i + 2 - j₁, by omega⟩ : Fin (j₂ + 1)) = ⟨1, by omega⟩ from
            Fin.ext (by dsimp; omega)]
        exact hnb hj1 hj2
      · rw [concatWalk_ge hjoin i hge (by omega),
            concatWalk_ge hjoin (i + 2) (by omega) (by omega)]
        have hstep := h2.ne_two_step (i := i - j₁) (by omega)
        rwa [show (⟨i + 2 - j₁, by omega⟩ : Fin (j₂ + 1)) =
          ⟨i - j₁ + 2, by omega⟩ from Fin.ext (by dsimp; omega)]

/-- Sharp sum-bounded uniqueness of non-backtracking walks in a graph with no closed
non-backtracking walk of length `1 ≤ j ≤ g`. -/
private theorem isNBWalk_eq_of_no_closed_sum {g : ℕ}
    (hgirth : ∀ (j : ℕ), 1 ≤ j → j ≤ g →
      ∀ w : Fin (j + 1) → V, IsNBWalk H j w → w 0 ≠ w (Fin.last j))
    {j₁ j₂ : ℕ} (hsum : j₁ + j₂ ≤ g)
    {w₁ : Fin (j₁ + 1) → V} {w₂ : Fin (j₂ + 1) → V}
    (h1 : IsNBWalk H j₁ w₁) (h2 : IsNBWalk H j₂ w₂)
    (hstart : w₁ 0 = w₂ 0) (hend : w₁ (Fin.last j₁) = w₂ (Fin.last j₂)) :
    ∃ _ : j₁ = j₂, ∀ i : ℕ, (hi : i ≤ j₁) → w₁ ⟨i, by omega⟩ = w₂ ⟨i, by omega⟩ := by
  have hmain : ∀ s : ℕ, s ≤ g → ∀ (j₁ j₂ : ℕ), j₁ + j₂ = s →
      ∀ (w₁ : Fin (j₁ + 1) → V) (w₂ : Fin (j₂ + 1) → V),
        IsNBWalk H j₁ w₁ → IsNBWalk H j₂ w₂ →
        w₁ 0 = w₂ 0 → w₁ (Fin.last j₁) = w₂ (Fin.last j₂) →
        ∃ _ : j₁ = j₂, ∀ i : ℕ, (hi : i ≤ j₁) → w₁ ⟨i, by omega⟩ = w₂ ⟨i, by omega⟩ := by
    intro s
    induction s using Nat.strong_induction_on with
    | ind s ih =>
      intro hsle j₁ j₂ hseq w₁ w₂ h1' h2' hs he
      rcases j₁ with _ | j₁'
      · rcases j₂ with _ | j₂'
        · refine ⟨rfl, fun i hi => ?_⟩
          have : i = 0 := by omega
          subst this; exact hs
        · exfalso
          exact hgirth (j₂' + 1) (by omega) (by omega) w₂ h2' (hs.symm.trans he)
      · rcases j₂ with _ | j₂'
        · exfalso
          exact hgirth (j₁' + 1) (by omega) (by omega) w₁ h1' (hs.trans he.symm)
        · by_cases hpen : w₁ ⟨j₁', by omega⟩ = w₂ ⟨j₂', by omega⟩
          · obtain ⟨hlen, hfn⟩ := ih (j₁' + j₂') (by omega) (by omega) j₁' j₂' rfl
              (fun i => w₁ i.castSucc) (fun i => w₂ i.castSucc) h1'.init h2'.init hs hpen
            refine ⟨by omega, fun i hi => ?_⟩
            by_cases hlast : i = j₁' + 1
            · subst hlast
              simpa [Fin.last, hlen] using he
            · exact hfn i (by omega)
          · exfalso
            have hjoin : w₁ (Fin.last (j₁' + 1)) = revWalk (j₂' + 1) w₂ 0 := by
              rw [revWalk_zero]; exact he
            have hnb := isNBWalk_concatWalk h1' (isNBWalk_revWalk h2') hjoin fun _ _ => by
              have hr : revWalk (j₂' + 1) w₂ ⟨1, by omega⟩ = w₂ ⟨j₂', by omega⟩ :=
                congrArg w₂ (Fin.ext (by simp [Fin.val_rev]))
              rw [hr]
              simpa only [show j₁' + 1 - 1 = j₁' by omega] using hpen
            have h0 : concatWalk (j₁' + 1) (j₂' + 1) w₁ (revWalk (j₂' + 1) w₂) 0 = w₁ 0 :=
              concatWalk_le 0 (by omega)
            have hl : concatWalk (j₁' + 1) (j₂' + 1) w₁ (revWalk (j₂' + 1) w₂)
                (Fin.last ((j₁' + 1) + (j₂' + 1))) = w₂ 0 := by
              have hge := concatWalk_ge hjoin ((j₁' + 1) + (j₂' + 1)) (by omega) le_rfl
              have hsub : (j₁' + 1) + (j₂' + 1) - (j₁' + 1) = j₂' + 1 := by omega
              calc concatWalk (j₁' + 1) (j₂' + 1) w₁ (revWalk (j₂' + 1) w₂)
                    (Fin.last ((j₁' + 1) + (j₂' + 1)))
                  = revWalk (j₂' + 1) w₂ ⟨(j₁' + 1) + (j₂' + 1) - (j₁' + 1), by omega⟩ := hge
                _ = revWalk (j₂' + 1) w₂ (Fin.last (j₂' + 1)) := by
                    congr 1; exact Fin.ext hsub
                _ = w₂ 0 := revWalk_last _ _
            exact hgirth ((j₁' + 1) + (j₂' + 1)) (by omega) (by omega) _ hnb
              (h0.trans (hs.trans hl.symm))
  exact hmain (j₁ + j₂) hsum j₁ j₂ rfl w₁ w₂ h1 h2 hstart hend

/-- Convert a length-`k` non-backtracking walk `w : Fin (k + 1) → V` into a `SimpleGraph.Walk`. -/
private def nbWalkToWalk :
    ∀ (k : ℕ) (w : Fin (k + 1) → V),
      (∀ i : Fin k, H.Adj (w i.castSucc) (w i.succ)) →
        H.Walk (w 0) (w (Fin.last k))
  | 0, _, _ => SimpleGraph.Walk.nil
  | k + 1, w, hadj =>
    SimpleGraph.Walk.cons (hadj 0)
      (nbWalkToWalk k (fun i => w i.succ) fun i => hadj i.succ)

private theorem nbWalkToWalk_length :
    ∀ (k : ℕ) (w : Fin (k + 1) → V) (hadj : ∀ i : Fin k, H.Adj (w i.castSucc) (w i.succ)),
      (nbWalkToWalk k w hadj).length = k
  | 0, _, _ => rfl
  | k + 1, w, hadj =>
    show (SimpleGraph.Walk.cons (hadj 0)
        (nbWalkToWalk k (fun i => w i.succ) fun i => hadj i.succ)).length = k + 1 by
      rw [SimpleGraph.Walk.length_cons,
        nbWalkToWalk_length k (fun i => w i.succ) fun i => hadj i.succ]

/-- Sub-walk of `w : Fin (k + 1) → V` from index `a` of length `l` (`a + l ≤ k`). -/
private def subWalk {k : ℕ} (w : Fin (k + 1) → V) (a l : ℕ) (hal : a + l ≤ k) :
    Fin (l + 1) → V :=
  fun i => w ⟨a + i.val, by omega⟩

private theorem isNBWalk_subWalk {k : ℕ} {w : Fin (k + 1) → V} (hw : IsNBWalk H k w)
    (a l : ℕ) (hal : a + l ≤ k) : IsNBWalk H l (subWalk w a l hal) := by
  refine ⟨fun i => ?_, fun i hi => ?_⟩
  · have hadj := hw.adj_step (i := a + i.val) (by omega)
    simpa only [subWalk, Fin.val_castSucc, Fin.val_succ, Nat.add_assoc] using hadj
  · have hne := hw.ne_two_step (i := a + i) (by omega)
    simpa only [subWalk, Nat.add_assoc] using hne

/-- Prefix walk `w|_{[0..t]}` of length `t ≤ k`. -/
private theorem isNBWalk_prefix {k : ℕ} {w : Fin (k + 1) → V} (hw : IsNBWalk H k w)
    (t : ℕ) (ht : t ≤ k) :
    IsNBWalk H t (fun i => w ⟨i.val, by omega⟩) :=
  ⟨fun i => hw.adj_step (i := i.val) (by have := i.isLt; omega),
    fun i hi => hw.ne_two_step (i := i) (by omega)⟩

/-- Exact count of non-backtracking walks of length `s` starting at `v` whose first step (when
`s > 0`) avoids a forbidden subset `F ⊆ H.neighborFinset v`, in a finite cubic graph `H`. -/
private theorem card_nbWalk_avoid [Fintype V] (H : SimpleGraph V)
    (hreg : ∀ u : V, open Classical in H.degree u = 3)
    (v : V) (F : Finset V) (hF : ∀ x ∈ F, H.Adj v x) (s : ℕ) :
    open Classical in
    (Finset.univ.filter fun w : Fin (s + 1) → V =>
      IsNBWalk H s w ∧ w 0 = v ∧ ∀ (_ : 0 < s), w ⟨1, by omega⟩ ∉ F).card =
      if s = 0 then 1 else (3 - F.card) * 2 ^ (s - 1) := by
  classical
  induction s with
  | zero =>
    have heq : Finset.univ.filter (fun w : Fin 1 → V =>
        IsNBWalk H 0 w ∧ w 0 = v ∧ ∀ (_ : 0 < 0), w ⟨1, by omega⟩ ∉ F) =
        {fun _ : Fin 1 => v} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h0, _⟩
        ext i; fin_cases i; exact h0
      · rintro rfl
        exact ⟨⟨fun i => i.elim0, fun _ hi => by omega⟩, rfl, fun h => by omega⟩
    rw [heq, Finset.card_singleton]
    simp
  | succ s ih =>
    rcases s with _ | s
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.sub_self, pow_zero,
        mul_one]
      have hsub : F ⊆ H.neighborFinset v := fun x hx =>
        (H.mem_neighborFinset v x).mpr (hF x hx)
      have hcard : (H.neighborFinset v \ F).card = 3 - F.card := by
        rw [Finset.card_sdiff_of_subset hsub]
        have hdeg : (H.neighborFinset v).card = 3 := hreg v
        omega
      rw [← hcard]
      refine Finset.card_bij (fun w _ => w 1) ?_ ?_ ?_
      · intro w hw
        have ⟨hnb, h0, hnot⟩ := (Finset.mem_filter.mp hw).2
        refine Finset.mem_sdiff.mpr ⟨(H.mem_neighborFinset v _).mpr ?_, hnot (by omega)⟩
        rw [← h0]; exact hnb.adj_step (i := 0) (by omega)
      · intro w₁ hw₁ w₂ hw₂ heq
        have h0₁ := (Finset.mem_filter.mp hw₁).2.2.1
        have h0₂ := (Finset.mem_filter.mp hw₂).2.2.1
        ext i; fin_cases i
        · exact h0₁.trans h0₂.symm
        · exact heq
      · intro x hx
        have hadj : H.Adj v x := (H.mem_neighborFinset v x).mp (Finset.mem_sdiff.mp hx).1
        have hnot : x ∉ F := (Finset.mem_sdiff.mp hx).2
        refine ⟨fun i : Fin 2 => if i = 0 then v else x,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨fun i => ?_, fun _ hi => by omega⟩,
            rfl, fun _ => hnot⟩, rfl⟩
        fin_cases i; exact hadj
    · set m := s + 1
      have hm_pos : 0 < m := by omega
      have hfib_card : ∀ (u : Fin (m + 1) → V),
          IsNBWalk H m u ∧ u 0 = v ∧ (∀ (_ : 0 < m), u ⟨1, by omega⟩ ∉ F) →
          ((Finset.univ.filter fun w : Fin (m + 2) → V =>
            (IsNBWalk H (m + 1) w ∧ w 0 = v ∧ ∀ (_ : 0 < m + 1), w ⟨1, by omega⟩ ∉ F) ∧
            (fun i : Fin (m + 1) => w i.castSucc) = u)).card = 2 := by
        intro u ⟨hunb, hu0, huf⟩
        have hprev_adj : H.Adj (u ⟨m, by omega⟩) (u ⟨m - 1, by omega⟩) := by
          have := (hunb.adj_step (i := m - 1) (by omega)).symm
          simpa [show m - 1 + 1 = m by omega] using this
        have herase_card : ((H.neighborFinset (u ⟨m, by omega⟩)).erase
            (u ⟨m - 1, by omega⟩)).card = 2 := by
          rw [Finset.card_erase_of_mem ((H.mem_neighborFinset _ _).mpr hprev_adj)]
          have hdeg : (H.neighborFinset (u ⟨m, by omega⟩)).card = 3 := hreg _
          omega
        conv_rhs => rw [← herase_card]
        refine Finset.card_bij (fun w _ => w (Fin.last (m + 1))) ?_ ?_ ?_
        · intro w hw
          obtain ⟨⟨hnb, _, _⟩, hpre⟩ := (Finset.mem_filter.mp hw).2
          have hlm : w ⟨m, by omega⟩ = u ⟨m, by omega⟩ := congrFun hpre ⟨m, by omega⟩
          have hpm : w ⟨m - 1, by omega⟩ = u ⟨m - 1, by omega⟩ := congrFun hpre ⟨m - 1, by omega⟩
          refine Finset.mem_erase.mpr ⟨?_, (H.mem_neighborFinset _ _).mpr ?_⟩
          · rw [← hpm]
            have hne := hnb.ne_two_step (i := m - 1) (by omega)
            have hidx : (⟨m - 1 + 2, by omega⟩ : Fin (m + 2)) = Fin.last (m + 1) :=
              Fin.ext (by simp [Fin.last]; omega)
            rw [hidx] at hne
            exact hne.symm
          · rw [← hlm]
            exact hnb.adj_step (i := m) (by omega)
        · intro w₁ hw₁ w₂ hw₂ heq
          have hp1 := (Finset.mem_filter.mp hw₁).2.2
          have hp2 := (Finset.mem_filter.mp hw₂).2.2
          ext i
          by_cases hi : i.val < m + 1
          · exact (congrFun hp1 ⟨i.val, hi⟩).trans (congrFun hp2 ⟨i.val, hi⟩).symm
          · have hlast : i = Fin.last (m + 1) := Fin.ext (by simp [Fin.last]; omega)
            subst hlast; exact heq
        · intro x hx
          have hxne : x ≠ u ⟨m - 1, by omega⟩ := (Finset.mem_erase.mp hx).1
          have hxadj : H.Adj (u ⟨m, by omega⟩) x :=
            (H.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hx).2
          let w : Fin (m + 2) → V := Fin.snoc u x
          refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩,
            by simp [w, Fin.snoc_last]⟩
          · intro i
            by_cases hi : i.val < m
            · have hc : i.castSucc = (⟨i.val, hi⟩ : Fin m).castSucc.castSucc := Fin.ext rfl
              have hs' : i.succ = (⟨i.val, hi⟩ : Fin m).succ.castSucc := Fin.ext rfl
              simp only [w, hc, hs', Fin.snoc_castSucc]
              exact hunb.1 ⟨i.val, hi⟩
            · have hi_eq : i.val = m := by omega
              have hc : i.castSucc = (Fin.last m).castSucc := Fin.ext (by simp [hi_eq])
              have hs' : i.succ = Fin.last (m + 1) := Fin.ext (by simp [hi_eq])
              rw [hc, hs']
              dsimp only [w]
              rw [Fin.snoc_castSucc, Fin.snoc_last]
              exact hxadj
          · intro i hi
            by_cases hlt : i + 2 ≤ m
            · have h1 : (⟨i, by omega⟩ : Fin (m + 2)) = (⟨i, by omega⟩ : Fin (m + 1)).castSucc :=
                Fin.ext rfl
              have h2 : (⟨i + 2, by omega⟩ : Fin (m + 2)) =
                  (⟨i + 2, by omega⟩ : Fin (m + 1)).castSucc := Fin.ext rfl
              dsimp only [w]
              rw [h1, h2, Fin.snoc_castSucc, Fin.snoc_castSucc]
              exact hunb.ne_two_step (i := i) hlt
            · have hi_eq : i = m - 1 := by omega
              have h1 : (⟨i, by omega⟩ : Fin (m + 2)) =
                  (⟨m - 1, by omega⟩ : Fin (m + 1)).castSucc := Fin.ext (by dsimp; omega)
              have h2 : (⟨i + 2, by omega⟩ : Fin (m + 2)) = Fin.last (m + 1) :=
                Fin.ext (by simp [Fin.last]; omega)
              dsimp only [w]
              rw [h1, h2, Fin.snoc_castSucc, Fin.snoc_last]
              exact hxne.symm
          · have h0 : (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc := Fin.ext rfl
            dsimp only [w]
            rw [h0, Fin.snoc_castSucc]
            exact hu0
          · intro _
            have h1 : (⟨1, by omega⟩ : Fin (m + 2)) =
                (⟨1, by omega⟩ : Fin (m + 1)).castSucc := Fin.ext rfl
            dsimp only [w]
            rw [h1, Fin.snoc_castSucc]
            exact huf hm_pos
          · ext i; simp [w, Fin.snoc_castSucc]
      let S₀ : Finset (Fin (m + 1) → V) := Finset.univ.filter fun u =>
        IsNBWalk H m u ∧ u 0 = v ∧ ∀ (_ : 0 < m), u ⟨1, by omega⟩ ∉ F
      let S₁ : Finset (Fin (m + 2) → V) := Finset.univ.filter fun w =>
        IsNBWalk H (m + 1) w ∧ w 0 = v ∧ ∀ (_ : 0 < m + 1), w ⟨1, by omega⟩ ∉ F
      have hmaps : ∀ w ∈ S₁, (fun i : Fin (m + 1) => w i.castSucc) ∈ S₀ := by
        intro w hw
        obtain ⟨hnb, h0, hnot⟩ := (Finset.mem_filter.mp hw).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnb.init, h0, fun _ => ?_⟩
        exact hnot (by omega)
      have hsum := Finset.card_eq_sum_card_fiberwise (s := S₁) (t := S₀)
        (f := fun w (i : Fin (m + 1)) => w i.castSucc) (fun w hw => hmaps w hw)
      have hfilt_eq : ∀ u ∈ S₀,
          (S₁.filter fun w => (fun i : Fin (m + 1) => w i.castSucc) = u).card = 2 := by
        intro u hu
        have heq : S₁.filter (fun w => (fun i : Fin (m + 1) => w i.castSucc) = u) =
            Finset.univ.filter fun w =>
              (IsNBWalk H (m + 1) w ∧ w 0 = v ∧ ∀ (_ : 0 < m + 1), w ⟨1, by omega⟩ ∉ F) ∧
                (fun i : Fin (m + 1) => w i.castSucc) = u := by
          ext w; simp [S₁]
        rw [heq]
        exact hfib_card u (Finset.mem_filter.mp hu).2
      have hih : S₀.card = (3 - F.card) * 2 ^ (m - 1) := by
        simpa [S₀, m, show m ≠ 0 by omega] using ih
      change S₁.card = if m + 1 = 0 then 1 else (3 - F.card) * 2 ^ (m + 1 - 1)
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        show m + 1 - 1 = m by omega]
      rw [hsum, Finset.sum_congr rfl hfilt_eq, Finset.sum_const, smul_eq_mul, hih]
      have : 2 ^ m = 2 ^ (m - 1) * 2 := by
        conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
      rw [this, mul_assoc]

end NBWalkHelpers

/-! ### Finite non-backtracking walk counts and pushed radial profile -/

section PushedProfile

variable {V : Type*}

/-- Number of non-backtracking walks of length `k` from `v` to `w` in `H`. -/
@[expose] noncomputable def nbCount [Fintype V] (H : SimpleGraph V) (k : ℕ) (v w : V) : ℕ :=
  open Classical in
  (Finset.univ.filter fun walk : Fin (k + 1) → V =>
    IsNBWalk H k walk ∧ walk 0 = v ∧ walk (Fin.last k) = w).card

/-- Reversing a walk shows `nbCount H k v w = nbCount H k w v`. -/
theorem nbCount_symm [Fintype V] (H : SimpleGraph V) (k : ℕ) (v w : V) :
    nbCount H k v w = nbCount H k w v := by
  classical
  change (Finset.univ.filter _).card = (Finset.univ.filter _).card
  refine Finset.card_bij (fun walk _ => revWalk k walk) ?_ ?_ ?_
  · intro walk hw
    obtain ⟨hnb, h0, hl⟩ := (Finset.mem_filter.mp hw).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, isNBWalk_revWalk hnb, (revWalk_zero k walk).trans hl,
        (revWalk_last k walk).trans h0⟩
  · intro w₁ _ w₂ _ heq
    have := congrArg (revWalk k) heq
    simpa only [revWalk_revWalk] using this
  · intro walk hw
    obtain ⟨hnb, h0, hl⟩ := (Finset.mem_filter.mp hw).2
    refine ⟨revWalk k walk, Finset.mem_filter.mpr ⟨Finset.mem_univ _, isNBWalk_revWalk hnb,
      (revWalk_zero k walk).trans hl, (revWalk_last k walk).trans h0⟩, revWalk_revWalk k walk⟩

/-- Sum of `nbCount H k v w` over all endpoints `w` in a finite cubic simple graph `H`. -/
theorem sum_nbCount_eq [Fintype V] (H : SimpleGraph V)
    (hreg : ∀ v : V, open Classical in H.degree v = 3) (k : ℕ) (v : V) :
    ∑ w : V, nbCount H k v w = if k = 0 then 1 else 3 * 2 ^ (k - 1) := by
  classical
  let S : Finset (Fin (k + 1) → V) :=
    Finset.univ.filter fun walk => IsNBWalk H k walk ∧ walk 0 = v
  have hsum : S.card = ∑ w : V, nbCount H k v w := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun walk : Fin (k + 1) → V => walk (Fin.last k))
      (t := (Finset.univ : Finset V)) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun w _ => ?_
    change (S.filter _).card = (Finset.univ.filter _).card
    congr 1; ext walk; simp [S, and_assoc]
  rw [← hsum]
  have hS : S = Finset.univ.filter fun walk : Fin (k + 1) → V =>
      IsNBWalk H k walk ∧ walk 0 = v ∧ ∀ (_ : 0 < k), walk ⟨1, by omega⟩ ∉ (∅ : Finset V) := by
    ext walk; simp [S]
  rw [hS]
  simpa using card_nbWalk_avoid H hreg v ∅ (fun _ hx => (Finset.notMem_empty _ hx).elim) k

/-- On a finite cubic simple graph `H`, the number of directed non-backtracking walks of length
`k ≥ 1` is `3 * 2 ^ (k - 1) * Fintype.card V`. -/
theorem dirNBCount_cubic_eq [Fintype V] (H : SimpleGraph V)
    (hreg : ∀ v : V, open Classical in H.degree v = 3) {k : ℕ} (hk : 1 ≤ k) :
    dirNBCount H k = 3 * 2 ^ (k - 1) * Fintype.card V := by
  classical
  let W : Finset (Fin (k + 1) → V) := Finset.univ.filter fun w => IsNBWalk H k w
  have hpart : W.card = ∑ v : V, (W.filter fun w => w 0 = v).card :=
    Finset.card_eq_sum_card_fiberwise (f := fun w : Fin (k + 1) → V => w 0)
      (fun _ _ => Finset.mem_univ _)
  have hterm : ∀ v : V, (W.filter fun w => w 0 = v).card = 3 * 2 ^ (k - 1) := by
    intro v
    have h1 : ∑ x : V, nbCount H k v x = (W.filter fun w => w 0 = v).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := fun w : Fin (k + 1) → V => w (Fin.last k))
        (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl fun x _ => ?_
      change (Finset.univ.filter _).card = _
      congr 1; ext walk; simp [W, and_assoc]
    rw [← h1, sum_nbCount_eq H hreg k v, ite_eq_right_iff.mpr (fun h => by omega)]
  change W.card = _
  rw [hpart, Finset.sum_congr rfl fun v _ => hterm v, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_comm]

/-- Non-backtracking walk count in a base graph equals the fiber sum of walk counts in a finite
covering graph. -/
theorem nbCount_lift_fiber_sum {V' : Type*} [Fintype V'] [Fintype V] [DecidableEq V]
    {H' : SimpleGraph V'} {H : SimpleGraph V} {m : ℕ}
    (cov : SimpleGraphCover H' H m) (k : ℕ) (u' : V') (x : V) :
    nbCount H k (cov.proj u') x = ∑ x' ∈ cov.fiber x, nbCount H' k u' x' := by
  classical
  let T' : Finset (Fin (k + 1) → V') := Finset.univ.filter fun w' =>
    IsNBWalk H' k w' ∧ w' 0 = u' ∧ cov.proj (w' (Fin.last k)) = x
  have hsum : T'.card = ∑ x' ∈ cov.fiber x, nbCount H' k u' x' := by
    rw [Finset.card_eq_sum_card_fiberwise (t := cov.fiber x)
      (f := fun w' : Fin (k + 1) → V' => w' (Fin.last k))
      (fun w' hw' => cov.mem_fiber.mpr (Finset.mem_filter.mp hw').2.2.2)]
    refine Finset.sum_congr rfl fun x' hx' => ?_
    change _ = (Finset.univ.filter _).card
    congr 1; ext w'
    have hpx' : cov.proj x' = x := cov.mem_fiber.mp hx'
    simp only [T', Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hnb, h0, _⟩, rfl⟩; exact ⟨hnb, h0, rfl⟩
    · rintro ⟨hnb, h0, rfl⟩; exact ⟨⟨hnb, h0, hpx'⟩, rfl⟩
  let W : Finset (Fin (k + 1) → V) := Finset.univ.filter fun w =>
    IsNBWalk H k w ∧ w 0 = cov.proj u' ∧ w (Fin.last k) = x
  have hnb_eq : nbCount H k (cov.proj u') x = W.card := by
    unfold nbCount
    congr 1; ext w; simp [W]
  rw [← hsum, hnb_eq]
  symm
  refine Finset.card_bij (fun w' _ => cov.proj ∘ w') ?_ ?_ ?_
  · intro w' hw'
    obtain ⟨hnb, h0, hlast⟩ := (Finset.mem_filter.mp hw').2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnb.map_cover cov, ?_, hlast⟩
    simp [h0]
  · intro w₁' hw₁' w₂' hw₂' heq
    have h1 := (Finset.mem_filter.mp hw₁').2
    have h2 := (Finset.mem_filter.mp hw₂').2
    exact cov.liftWalk_unique h1.1.1 h2.1.1 h1.2.1 h2.2.1 fun i => congrFun heq i
  · intro w hw
    obtain ⟨hnb, h0, hlast⟩ := (Finset.mem_filter.mp hw).2
    obtain ⟨w', ⟨hnb', hw'0, hproj⟩, _⟩ := cov.existsUnique_lift_nbWalk u' hnb h0
    refine ⟨w', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnb', hw'0, ?_⟩, hproj⟩
    exact (congrFun hproj (Fin.last k)).trans hlast

/-- Radial normalization constant `1 + 3 * R / 2` for shells up to radius `R`. -/
noncomputable def shellNorm (R : ℕ) : ℝ := 1 + 3 * (R : ℝ) / 2

/-- `shellNorm R` is strictly positive for every `R : ℕ`. -/
theorem shellNorm_pos (R : ℕ) : 0 < shellNorm R := by
  unfold shellNorm
  positivity

/-- `shellNorm R` is at least `1` for every `R : ℕ`. -/
theorem one_le_shellNorm (R : ℕ) : 1 ≤ shellNorm R := by
  unfold shellNorm
  linarith [show (0 : ℝ) ≤ 3 * (R : ℝ) / 2 by positivity]

/-- Normalized pushed non-backtracking radial distribution up to radius `R`. -/
noncomputable def pushedProb [Fintype V] (H : SimpleGraph V) (R : ℕ) (v x : V) : ℝ :=
  (shellNorm R)⁻¹ * ∑ k ∈ Finset.range (R + 1), (nbCount H k v x : ℝ) * (2 : ℝ)⁻¹ ^ k

/-- Every entry of `pushedProb H R v x` is nonnegative. -/
theorem pushedProb_nonneg [Fintype V] (H : SimpleGraph V) (R : ℕ) (v x : V) :
    0 ≤ pushedProb H R v x := by
  unfold pushedProb
  have hnorm : 0 ≤ (shellNorm R)⁻¹ := (inv_pos.mpr (shellNorm_pos R)).le
  exact mul_nonneg hnorm (Finset.sum_nonneg fun k _ => by positivity)

/-- `pushedProb H R v x` is symmetric in `v` and `x` by walk reversal. -/
theorem pushedProb_symm [Fintype V] (H : SimpleGraph V) (R : ℕ) (v x : V) :
    pushedProb H R v x = pushedProb H R x v := by
  unfold pushedProb
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [nbCount_symm]

/-- On a finite cubic simple graph `H`, `pushedProb H R v` is a probability distribution. -/
theorem sum_pushedProb_eq_one [Fintype V] (H : SimpleGraph V)
    (hreg : ∀ v : V, open Classical in H.degree v = 3) (R : ℕ) (v : V) :
    ∑ x : V, pushedProb H R v x = 1 := by
  unfold pushedProb
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hinner : ∑ k ∈ Finset.range (R + 1),
      ∑ x : V, (nbCount H k v x : ℝ) * (2 : ℝ)⁻¹ ^ k = shellNorm R := by
    have hterm : ∀ k ∈ Finset.range (R + 1),
        ∑ x : V, (nbCount H k v x : ℝ) * (2 : ℝ)⁻¹ ^ k =
          if k = 0 then (1 : ℝ) else (3 / 2 : ℝ) := by
      intro k _
      rw [← Finset.sum_mul, ← Nat.cast_sum, sum_nbCount_eq H hreg k v]
      rcases k with _ | k
      · simp
      · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
          show k + 1 - 1 = k by omega]
        push_cast
        have hpow : (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ (k + 1) = (2 : ℝ)⁻¹ := by
          rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
            one_pow, one_mul]
        rw [mul_assoc, hpow]
        ring
    rw [Finset.sum_congr rfl hterm]
    rw [Finset.sum_range_succ']
    simp only [↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, shellNorm]
    ring
  rw [hinner, inv_mul_cancel₀ (shellNorm_pos R).ne']

/-- If `pushedProb H R v x ≠ 0`, then there is a non-backtracking walk of length at most `R` from
`v` to `x`. -/
theorem exists_nbWalk_of_pushedProb_ne_zero [Fintype V] {H : SimpleGraph V} {R : ℕ} {v x : V}
    (h : pushedProb H R v x ≠ 0) :
    ∃ k ≤ R, ∃ w : Fin (k + 1) → V, IsNBWalk H k w ∧ w 0 = v ∧ w (Fin.last k) = x := by
  classical
  unfold pushedProb at h
  have hsum_ne : ∑ k ∈ Finset.range (R + 1), (nbCount H k v x : ℝ) * (2 : ℝ)⁻¹ ^ k ≠ 0 :=
    right_ne_zero_of_mul h
  obtain ⟨k, hk_mem, hkne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  have hcnt : nbCount H k v x ≠ 0 := by
    intro hc; apply hkne; simp [hc]
  have hpos : 0 < (Finset.univ.filter fun walk : Fin (k + 1) → V =>
      IsNBWalk H k walk ∧ walk 0 = v ∧ walk (Fin.last k) = x).card := Nat.pos_of_ne_zero hcnt
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk_mem), w, (Finset.mem_filter.mp hw).2⟩

/-- Locality of `pushedProb`: nonzero mass implies extended graph distance at most `R`. -/
theorem pushedProb_eq_zero_of_edist_gt [Fintype V] {H : SimpleGraph V} {R : ℕ} {v x : V}
    (h : pushedProb H R v x ≠ 0) : H.edist v x ≤ R := by
  obtain ⟨k, hk, w, hnb, h0, hlast⟩ := exists_nbWalk_of_pushedProb_ne_zero h
  let p : H.Walk v x := (nbWalkToWalk k w hnb.1).copy h0 hlast
  have hlen : p.length = k := by
    simp [p, nbWalkToWalk_length]
  calc H.edist v x ≤ p.length := p.edist_le
    _ = (k : ℕ∞) := by rw [hlen]
    _ ≤ (R : ℕ∞) := Nat.cast_le.mpr hk

/-- Summing `pushedProb` over the fiber of a covering map recovers `pushedProb` on the base. -/
theorem sum_fiber_pushedProb_eq {V' : Type*} [Fintype V'] [Fintype V] [DecidableEq V]
    {H' : SimpleGraph V'} {H : SimpleGraph V} {m : ℕ}
    (cov : SimpleGraphCover H' H m) (R : ℕ) (u' : V') (x : V) :
    ∑ x' ∈ cov.fiber x, pushedProb H' R u' x' = pushedProb H R (cov.proj u') x := by
  unfold pushedProb
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_mul, ← Nat.cast_sum, nbCount_lift_fiber_sum cov k u' x]

end PushedProfile

/-! ### Gaussian wave rows and fiberwise Cauchy–Schwarz covariance comparison -/

section WaveRow

variable {V : Type*}

/-- Unit-norm row vector `V ⊕ V → ℝ` defining the regularized Gaussian wave at vertex `v`. -/
@[expose] noncomputable def waveRow [Fintype V] (H : SimpleGraph V) (R : ℕ) (ε : ℝ) (v : V) :
    V ⊕ V → ℝ
  | Sum.inl x => Real.sqrt (1 - ε ^ 2) * Real.sqrt (pushedProb H R v x)
  | Sum.inr x => open Classical in if x = v then ε else 0

/-- Evaluation of the Gaussian wave field at vertex `v`. -/
@[expose] noncomputable def waveScore [Fintype V] (H : SimpleGraph V) (R : ℕ) (ε : ℝ)
    (g : V ⊕ V → ℝ) (v : V) : ℝ :=
  ∑ z : V ⊕ V, waveRow H R ε v z * g z

/-- Every wave row `waveRow H R ε v` has squared Euclidean norm `1` on a finite cubic graph
when `0 ≤ ε ≤ 1`. -/
theorem sum_sq_waveRow_eq_one [Fintype V] (H : SimpleGraph V)
    (hreg : ∀ v : V, open Classical in H.degree v = 3)
    (R : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (v : V) :
    ∑ z : V ⊕ V, waveRow H R ε v z ^ 2 = 1 := by
  classical
  have h1e : 0 ≤ 1 - ε ^ 2 := by nlinarith
  rw [Fintype.sum_sum_type]
  have hleft : ∑ x : V, waveRow H R ε v (Sum.inl x) ^ 2 = 1 - ε ^ 2 := by
    simp only [waveRow, mul_pow, Real.sq_sqrt h1e]
    have hsq : ∀ x : V, Real.sqrt (pushedProb H R v x) ^ 2 = pushedProb H R v x := fun x =>
      Real.sq_sqrt (pushedProb_nonneg H R v x)
    simp_rw [hsq, ← Finset.mul_sum, sum_pushedProb_eq_one H hreg R v, mul_one]
  have hright : ∑ x : V, waveRow H R ε v (Sum.inr x) ^ 2 = ε ^ 2 := by
    simp only [waveRow]
    rw [Finset.sum_eq_single v]
    · simp
    · intro x _ hxv; simp [hxv]
    · intro hv; exact absurd (Finset.mem_univ v) hv
  rw [hleft, hright]
  ring

/-- The radial entry `waveRow H R ε v (Sum.inl x)` vanishes outside the `R`-ball of
non-backtracking walks starting at `v`. -/
theorem waveRow_locality [Fintype V] (H : SimpleGraph V) (R : ℕ) (ε : ℝ) (v x : V)
    (hno : ¬ ∃ k ≤ R, ∃ w : Fin (k + 1) → V,
      IsNBWalk H k w ∧ w 0 = v ∧ w (Fin.last k) = x) :
    waveRow H R ε v (Sum.inl x) = 0 := by
  have hp : pushedProb H R v x = 0 := by
    by_contra hne
    exact hno (exists_nbWalk_of_pushedProb_ne_zero hne)
  simp [waveRow, hp]

/-- Inner product expansion for two wave rows. -/
theorem waveRow_inner_eq [Fintype V] (H : SimpleGraph V) (R : ℕ) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (u v : V) :
    ∑ z : V ⊕ V, waveRow H R ε u z * waveRow H R ε v z =
      (1 - ε ^ 2) * ∑ x : V, Real.sqrt (pushedProb H R u x * pushedProb H R v x) +
        (open Classical in if u = v then ε ^ 2 else 0) := by
  classical
  have h1e : 0 ≤ 1 - ε ^ 2 := by nlinarith
  rw [Fintype.sum_sum_type]
  congr 1
  · calc ∑ x : V, waveRow H R ε u (Sum.inl x) * waveRow H R ε v (Sum.inl x)
        = ∑ x : V, (1 - ε ^ 2) *
            (Real.sqrt (pushedProb H R u x) * Real.sqrt (pushedProb H R v x)) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            simp only [waveRow]
            calc (√(1 - ε ^ 2) * √(pushedProb H R u x)) *
                  (√(1 - ε ^ 2) * √(pushedProb H R v x))
                = (√(1 - ε ^ 2) ^ 2) *
                    (√(pushedProb H R u x) * √(pushedProb H R v x)) := by ring
              _ = _ := by rw [Real.sq_sqrt h1e]
      _ = (1 - ε ^ 2) * ∑ x : V, Real.sqrt (pushedProb H R u x * pushedProb H R v x) := by
            rw [← Finset.mul_sum]
            refine congrArg _ (Finset.sum_congr rfl fun x _ => ?_)
            exact (Real.sqrt_mul (pushedProb_nonneg H R u x) _).symm
  · by_cases huv : u = v
    · subst huv
      simp only [↓reduceIte]
      rw [Finset.sum_eq_single u]
      · simp [waveRow, sq]
      · intro x _ hxu; simp [waveRow, hxu]
      · intro hu; exact absurd (Finset.mem_univ u) hu
    · simp only [huv, ↓reduceIte]
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hxu : x = u
      · subst hxu; simp [waveRow, huv]
      · simp [waveRow, hxu]

/-- **Fiberwise Cauchy–Schwarz covariance comparison:** lifting `H` along a finite covering map
`cov : SimpleGraphCover H' H m` never increases the off-diagonal wave row inner product. -/
theorem waveRow_cov_cover_le_base {V' : Type*} [Fintype V'] [Fintype V]
    {H' : SimpleGraph V'} {H : SimpleGraph V} {m : ℕ}
    (cov : SimpleGraphCover H' H m) (R : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {u' v' : V'} (hne : u' ≠ v') :
    ∑ z' : V' ⊕ V', waveRow H' R ε u' z' * waveRow H' R ε v' z' ≤
      ∑ z : V ⊕ V, waveRow H R ε (cov.proj u') z * waveRow H R ε (cov.proj v') z := by
  classical
  have h1e : 0 ≤ 1 - ε ^ 2 := by nlinarith
  rw [waveRow_inner_eq H' R hε0 hε1 u' v', waveRow_inner_eq H R hε0 hε1 (cov.proj u') (cov.proj v')]
  simp only [hne, ↓reduceIte, add_zero]
  have hinr : (0 : ℝ) ≤ if cov.proj u' = cov.proj v' then ε ^ 2 else 0 := by
    split_ifs <;> positivity
  have hcs : ∑ x' : V', Real.sqrt (pushedProb H' R u' x' * pushedProb H' R v' x') ≤
      ∑ x : V, Real.sqrt (pushedProb H R (cov.proj u') x * pushedProb H R (cov.proj v') x) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
      (g := cov.proj) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_le_sum fun x _ => ?_
    have hfib_eq : Finset.univ.filter (fun x' : V' => cov.proj x' = x) = cov.fiber x := rfl
    rw [hfib_eq]
    have hnn_sum : 0 ≤ ∑ x' ∈ cov.fiber x,
        Real.sqrt (pushedProb H' R u' x' * pushedProb H' R v' x') :=
      Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
    have hsq : (∑ x' ∈ cov.fiber x,
        Real.sqrt (pushedProb H' R u' x' * pushedProb H' R v' x')) ^ 2 ≤
        pushedProb H R (cov.proj u') x * pushedProb H R (cov.proj v') x := by
      calc (∑ x' ∈ cov.fiber x,
            Real.sqrt (pushedProb H' R u' x' * pushedProb H' R v' x')) ^ 2
          = (∑ x' ∈ cov.fiber x,
              Real.sqrt (pushedProb H' R u' x') * Real.sqrt (pushedProb H' R v' x')) ^ 2 := by
              congr 1; refine Finset.sum_congr rfl fun x' _ => ?_
              exact Real.sqrt_mul (pushedProb_nonneg H' R u' x') _
        _ ≤ (∑ x' ∈ cov.fiber x, Real.sqrt (pushedProb H' R u' x') ^ 2) *
              (∑ x' ∈ cov.fiber x, Real.sqrt (pushedProb H' R v' x') ^ 2) :=
              Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        _ = (∑ x' ∈ cov.fiber x, pushedProb H' R u' x') *
              (∑ x' ∈ cov.fiber x, pushedProb H' R v' x') := by
              congr 1 <;> refine Finset.sum_congr rfl fun x' _ =>
                Real.sq_sqrt (pushedProb_nonneg H' R _ x')
        _ = pushedProb H R (cov.proj u') x * pushedProb H R (cov.proj v') x := by
              rw [sum_fiber_pushedProb_eq cov R u' x, sum_fiber_pushedProb_eq cov R v' x]
    exact Real.le_sqrt_of_sq_le hsq
  calc (1 - ε ^ 2) * ∑ x' : V', Real.sqrt (pushedProb H' R u' x' * pushedProb H' R v' x')
      ≤ (1 - ε ^ 2) * ∑ x : V,
          Real.sqrt (pushedProb H R (cov.proj u') x * pushedProb H R (cov.proj v') x) :=
        mul_le_mul_of_nonneg_left hcs h1e
    _ ≤ _ := le_add_of_nonneg_right hinr

end WaveRow

/-! ### Exact radial overlap on the infinite 3-regular tree and high-girth graphs -/

section TreeOverlap

/-- Limiting covariance of the radial Gaussian wave process at graph distance `d` on the infinite
3-regular tree: `(1 + d / 3) * 2 ^ (-d / 2)`. -/
noncomputable def treeCovLimit (d : ℕ) : ℝ :=
  (1 + (d : ℝ) / 3) * (2 : ℝ) ^ (-(d : ℝ) / 2)

/-- At distance `0`, `treeCovLimit 0 = 1`. -/
theorem treeCovLimit_zero : treeCovLimit 0 = 1 := by
  simp [treeCovLimit]

/-- At distance `1`, `treeCovLimit 1 = 2 * √2 / 3`. -/
theorem treeCovLimit_one : treeCovLimit 1 = 2 * Real.sqrt 2 / 3 := by
  unfold treeCovLimit
  have hpow : (2 : ℝ) ^ (-(1 : ℝ) / 2) = (Real.sqrt 2)⁻¹ := by
    rw [neg_div, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_eq_rpow]
  rw [Nat.cast_one, hpow]
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  field_simp [hne]
  nlinarith [hsq]

/-- At distance `2`, `treeCovLimit 2 = 5 / 6`. -/
theorem treeCovLimit_two : treeCovLimit 2 = 5 / 6 := by
  unfold treeCovLimit
  have hpow : (2 : ℝ) ^ (-(2 : ℝ) / 2) = 2⁻¹ := by
    rw [show -(2 : ℝ) / 2 = -1 by ring, Real.rpow_neg_one]
  rw [Nat.cast_ofNat, hpow]
  norm_num

/-- Second-order linear recurrence satisfied by `treeCovLimit`:
`treeCovLimit (d + 2) = √2 * treeCovLimit (d + 1) - (1 / 2) * treeCovLimit d`. -/
theorem treeCovLimit_rec (d : ℕ) :
    treeCovLimit (d + 2) =
      Real.sqrt 2 * treeCovLimit (d + 1) - (1 / 2) * treeCovLimit d := by
  unfold treeCovLimit
  set r : ℝ := (2 : ℝ) ^ (-(d : ℝ) / 2)
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h1 : (2 : ℝ) ^ (-((d + 1 : ℕ) : ℝ) / 2) = r * (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add h2pos]
    congr 1; push_cast; ring
  have h2 : (2 : ℝ) ^ (-((d + 2 : ℕ) : ℝ) / 2) = r * (1 / 2 : ℝ) := by
    have heq : (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one]; norm_num
    rw [heq, ← Real.rpow_add h2pos]
    congr 1; push_cast; ring
  have hmul : Real.sqrt 2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [Real.rpow_neg h2pos.le, ← Real.sqrt_eq_rpow]
    exact mul_inv_cancel₀ (Real.sqrt_pos.mpr h2pos).ne'
  rw [h1, h2]
  have hd1 : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; rfl
  have hd2 : ((d + 2 : ℕ) : ℝ) = (d : ℝ) + 2 := by push_cast; rfl
  rw [hd1, hd2]
  calc (1 + ((d : ℝ) + 2) / 3) * (r * (1 / 2))
      = (1 + ((d : ℝ) + 1) / 3) * (1 * r) - (1 / 2) * ((1 + (d : ℝ) / 3) * r) := by ring
    _ = (1 + ((d : ℝ) + 1) / 3) * (Real.sqrt 2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) * r) -
          (1 / 2) * ((1 + (d : ℝ) / 3) * r) := by rw [hmul]
    _ = Real.sqrt 2 * ((1 + ((d : ℝ) + 1) / 3) * (r * (2 : ℝ) ^ (-(1 / 2 : ℝ)))) -
          (1 / 2) * ((1 + (d : ℝ) / 3) * r) := by ring

/-- Exact radial wave overlap at distance `d` and radius `R` on a cubic tree (valid for `d ≤ R`). -/
noncomputable def treeOverlap (R d : ℕ) : ℝ :=
  if d = 0 then 1
  else if d ≤ R then
    (shellNorm R)⁻¹ * (2 : ℝ) ^ (-(d : ℝ) / 2) *
      (2 * (1 + ((R - d : ℕ) : ℝ)) +
        ∑ t ∈ Finset.Ioo 0 d, (1 + ((R - max t (d - t) : ℕ) : ℝ) / 2))
  else 0

/-- At distance `0`, `treeOverlap R 0 = 1`. -/
theorem treeOverlap_zero (R : ℕ) : treeOverlap R 0 = 1 := by
  simp [treeOverlap]

/-- As `R → ∞`, `treeOverlap R d` converges to `treeCovLimit d` for every `d : ℕ`. -/
theorem tendsto_treeOverlap (d : ℕ) :
    Tendsto (fun R : ℕ => treeOverlap R d) atTop (nhds (treeCovLimit d)) := by
  rcases d with _ | d'
  · simp [treeOverlap, treeCovLimit_zero]
  · set d := d' + 1
    have hhd : d ≠ 0 := Nat.succ_ne_zero d'
    have hratio : ∀ c : ℕ,
        Tendsto (fun R : ℕ => (shellNorm R)⁻¹ * ((R - c : ℕ) : ℝ)) atTop
          (nhds (2 / 3 : ℝ)) := by
      intro c
      have hev : ∀ᶠ R : ℕ in atTop,
          (shellNorm R)⁻¹ * ((R - c : ℕ) : ℝ) =
            (1 - (c : ℝ) / (R : ℝ)) / ((1 : ℝ) / (R : ℝ) + 3 / 2) := by
        filter_upwards [Filter.eventually_ge_atTop (max c 1)] with R hR
        have hRc : c ≤ R := (le_max_left c 1).trans hR
        have hRpos : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr ((le_max_right c 1).trans hR)
        have hsn_pos : (0 : ℝ) < shellNorm R := shellNorm_pos R
        rw [Nat.cast_sub hRc]
        unfold shellNorm
        field_simp [hRpos.ne', hsn_pos.ne']
      have hinv : Tendsto (fun R : ℕ => (1 : ℝ) / (R : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      have hnum : Tendsto (fun R : ℕ => 1 - (c : ℝ) / (R : ℝ)) atTop (nhds 1) := by
        have h0 : Tendsto (fun R : ℕ => (c : ℝ) / (R : ℝ)) atTop (nhds 0) :=
          tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
        simpa using tendsto_const_nhds.sub h0
      have hden : Tendsto (fun R : ℕ => (1 : ℝ) / (R : ℝ) + 3 / 2) atTop (nhds (3 / 2)) := by
        simpa using hinv.add tendsto_const_nhds
      have hlim : Tendsto (fun R : ℕ =>
          (1 - (c : ℝ) / (R : ℝ)) / ((1 : ℝ) / (R : ℝ) + 3 / 2))
          atTop (nhds ((1 : ℝ) / (3 / 2))) :=
        hnum.div hden (by norm_num)
      rw [show (1 : ℝ) / (3 / 2) = 2 / 3 by norm_num] at hlim
      exact hlim.congr' (hev.mono fun _ h => h.symm)
    have hsn_inv : Tendsto (fun R : ℕ => (shellNorm R)⁻¹) atTop (nhds 0) := by
      have htop : Tendsto (fun R : ℕ => shellNorm R) atTop atTop := by
        refine tendsto_atTop_mono (fun R => ?_) tendsto_natCast_atTop_atTop
        unfold shellNorm
        linarith [Nat.cast_nonneg (α := ℝ) R]
      exact tendsto_inv_atTop_zero.comp htop
    have hhead : Tendsto (fun R : ℕ =>
        (shellNorm R)⁻¹ * (2 * (1 + ((R - d : ℕ) : ℝ)))) atTop (nhds (4 / 3 : ℝ)) := by
      have hlim := (hsn_inv.add (hratio d)).const_mul 2
      have hval : 2 * ((0 : ℝ) + 2 / 3) = 4 / 3 := by norm_num
      rw [hval] at hlim
      exact hlim.congr fun R => by ring
    have hterm : ∀ t : ℕ,
        Tendsto (fun R : ℕ =>
          (shellNorm R)⁻¹ * (1 + ((R - max t (d - t) : ℕ) : ℝ) / 2)) atTop
          (nhds (1 / 3 : ℝ)) := by
      intro t
      have hlim := hsn_inv.add ((hratio (max t (d - t))).div_const 2)
      have hval : (0 : ℝ) + (2 / 3) / 2 = 1 / 3 := by norm_num
      rw [hval] at hlim
      exact hlim.congr fun R => by ring
    have hsum : Tendsto (fun R : ℕ => ∑ t ∈ Finset.Ioo 0 d,
        (shellNorm R)⁻¹ * (1 + ((R - max t (d - t) : ℕ) : ℝ) / 2)) atTop
        (nhds (∑ _t ∈ Finset.Ioo 0 d, (1 / 3 : ℝ))) := by
      induction (Finset.Ioo 0 d) using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        simp_rw [Finset.sum_insert ha]
        exact (hterm a).add ih
    have hcard : (Finset.Ioo 0 d).card = d - 1 := by simp [Nat.card_Ioo]
    have hsum_val : ∑ _t ∈ Finset.Ioo 0 d, (1 / 3 : ℝ) = ((d : ℝ) - 1) / 3 := by
      rw [Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
      ring
    rw [hsum_val] at hsum
    have hcomb := (hhead.add hsum).const_mul ((2 : ℝ) ^ (-(d : ℝ) / 2))
    have hlim_eq : (2 : ℝ) ^ (-(d : ℝ) / 2) * (4 / 3 + ((d : ℝ) - 1) / 3) = treeCovLimit d := by
      unfold treeCovLimit; ring
    rw [hlim_eq] at hcomb
    refine hcomb.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop d] with R hR
    simp only [treeOverlap, hhd, ↓reduceIte, hR]
    rw [mul_add, ← Finset.mul_sum]
    ring

private theorem pushedProb_eq_of_nbWalk_of_no_closed {V' : Type*} [Fintype V']
    {H' : SimpleGraph V'} {R : ℕ}
    (hgirth : ∀ (j : ℕ), 1 ≤ j → j ≤ 2 * R →
      ∀ w' : Fin (j + 1) → V', IsNBWalk H' j w' → w' 0 ≠ w' (Fin.last j))
    {u' x' : V'} {k : ℕ} (hk : k ≤ R) {w : Fin (k + 1) → V'}
    (hnb : IsNBWalk H' k w) (h0 : w 0 = u') (hlast : w (Fin.last k) = x') :
    pushedProb H' R u' x' = (shellNorm R)⁻¹ * (2 : ℝ)⁻¹ ^ k := by
  classical
  unfold pushedProb
  congr 1
  rw [Finset.sum_eq_single k]
  · have hcnt : nbCount H' k u' x' = 1 := by
      change (Finset.univ.filter fun walk : Fin (k + 1) → V' =>
        IsNBWalk H' k walk ∧ walk 0 = u' ∧ walk (Fin.last k) = x').card = 1
      refine Finset.card_eq_one.mpr ⟨w, ?_⟩
      ext walk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hnb', h0', hl'⟩
        obtain ⟨_, heq⟩ := isNBWalk_eq_of_no_closed_sum hgirth (by omega : k + k ≤ 2 * R)
          hnb' hnb (h0'.trans h0.symm) (hl'.trans hlast.symm)
        ext i; exact heq i.val (by omega)
      · rintro rfl; exact ⟨hnb, h0, hlast⟩
    rw [hcnt, Nat.cast_one, one_mul]
  · intro j hj hjne
    have hjr : j ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hcnt : nbCount H' j u' x' = 0 := by
      change (Finset.univ.filter fun walk : Fin (j + 1) → V' =>
        IsNBWalk H' j walk ∧ walk 0 = u' ∧ walk (Fin.last j) = x').card = 0
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro walk hw
      obtain ⟨hnb', h0', hl'⟩ := (Finset.mem_filter.mp hw).2
      obtain ⟨hlen, _⟩ := isNBWalk_eq_of_no_closed_sum hgirth (by omega : j + k ≤ 2 * R)
        hnb' hnb (h0'.trans h0.symm) (hl'.trans hlast.symm)
      exact hjne hlen
    simp [hcnt]
  · intro hkmem; exact absurd (Finset.mem_range.mpr (by omega)) hkmem

/-- Auxiliary exact overlap identity for the endpoints of a non-backtracking walk `p` of length
`1 ≤ d ≤ R`. -/
private theorem sum_sqrt_pushedProb_eq_treeOverlap_pos {V' : Type*} [Fintype V']
    (H' : SimpleGraph V') (hreg : ∀ v : V', open Classical in H'.degree v = 3)
    {R d : ℕ} (hd1 : 1 ≤ d) (hdR : d ≤ R)
    (hgirth : ∀ (k : ℕ), 1 ≤ k → k ≤ 2 * R + d →
      ∀ w' : Fin (k + 1) → V', IsNBWalk H' k w' → w' 0 ≠ w' (Fin.last k))
    {p : Fin (d + 1) → V'} (hp : IsNBWalk H' d p) :
    ∑ x' : V', Real.sqrt (pushedProb H' R (p 0) x' * pushedProb H' R (p (Fin.last d)) x') =
      treeOverlap R d := by
  classical
  have hg2R : ∀ (k : ℕ), 1 ≤ k → k ≤ 2 * R →
      ∀ w' : Fin (k + 1) → V', IsNBWalk H' k w' → w' 0 ≠ w' (Fin.last k) :=
    fun k h1 h2 => hgirth k h1 (by omega)
  let forb (t : Fin (d + 1)) : Finset V' :=
    (if h : 0 < t.val then {p ⟨t.val - 1, by omega⟩} else ∅) ∪
    (if h : t.val < d then {p ⟨t.val + 1, by omega⟩} else ∅)
  have hforb_adj : ∀ t : Fin (d + 1), ∀ z ∈ forb t, H'.Adj (p t) z := by
    intro t z hz
    simp only [forb, Finset.mem_union] at hz
    rcases hz with h1 | h2
    · split_ifs at h1 with ht
      · rw [Finset.mem_singleton.mp h1]
        have := (hp.adj_step (i := t.val - 1) (by omega)).symm
        simpa [show t.val - 1 + 1 = t.val by omega] using this
      · exact (Finset.notMem_empty _ h1).elim
    · split_ifs at h2 with ht
      · rw [Finset.mem_singleton.mp h2]
        exact hp.adj_step (i := t.val) ht
      · exact (Finset.notMem_empty _ h2).elim
  have hforb_card_zero : (forb ⟨0, by omega⟩).card = 1 := by
    have hlt : 0 < d := hd1
    have h0 : ¬(0 < (0 : ℕ)) := Nat.not_lt_zero 0
    simp only [forb, h0, hlt, ↓reduceDIte, Finset.empty_union, Finset.card_singleton]
  have hforb_card_last : (forb ⟨d, by omega⟩).card = 1 := by
    have hpos : 0 < d := hd1
    have hnd : ¬(d < d) := lt_irrefl d
    simp only [forb, hpos, hnd, ↓reduceDIte, Finset.union_empty, Finset.card_singleton]
  have hforb_card_mid : ∀ t : Fin (d + 1), 0 < t.val → t.val < d → (forb t).card = 2 := by
    intro t ht0 htd
    have hne : p ⟨t.val - 1, by omega⟩ ≠ p ⟨t.val + 1, by omega⟩ := by
      have := hp.ne_two_step (i := t.val - 1) (by omega)
      simpa [show t.val - 1 + 2 = t.val + 1 by omega] using this
    simp only [forb, ht0, htd, ↓reduceDIte]
    rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton.mpr hne)]
    simp
  let branchWalks (t : Fin (d + 1)) (s : ℕ) : Finset (Fin (s + 1) → V') :=
    Finset.univ.filter fun q =>
      IsNBWalk H' s q ∧ q 0 = p t ∧ ∀ (_ : 0 < s), q ⟨1, by omega⟩ ∉ forb t
  let prefixOf (t : Fin (d + 1)) : Fin (t.val + 1) → V' := fun i => p ⟨i.val, by omega⟩
  let suffixRevOf (t : Fin (d + 1)) : Fin (d - t.val + 1) → V' :=
    revWalk (d - t.val) (subWalk p t.val (d - t.val) (by omega))
  have htoU : ∀ (t : Fin (d + 1)) (s : ℕ) (q : Fin (s + 1) → V'),
      q ∈ branchWalks t s →
      IsNBWalk H' (t.val + s) (concatWalk t.val s (prefixOf t) q) ∧
        concatWalk t.val s (prefixOf t) q 0 = p 0 ∧
        concatWalk t.val s (prefixOf t) q (Fin.last (t.val + s)) = q (Fin.last s) := by
    intro t s q hq
    obtain ⟨hqnb, hq0, hqf⟩ := (Finset.mem_filter.mp hq).2
    have hjoin : prefixOf t (Fin.last t.val) = q 0 := by
      rw [hq0]; rfl
    have hnb : IsNBWalk H' (t.val + s) (concatWalk t.val s (prefixOf t) q) := by
      refine isNBWalk_concatWalk (isNBWalk_prefix hp t.val (by omega)) hqnb hjoin ?_
      intro ht hs heq
      apply hqf hs
      rw [← heq]
      simp only [forb, prefixOf, Finset.mem_union]
      left; simp [ht]
    refine ⟨hnb, concatWalk_le 0 (by omega), ?_⟩
    have := concatWalk_ge hjoin (t.val + s) (by omega) le_rfl
    simpa [Fin.last, Nat.add_sub_cancel_left] using this
  have htoV : ∀ (t : Fin (d + 1)) (s : ℕ) (q : Fin (s + 1) → V'),
      q ∈ branchWalks t s →
      IsNBWalk H' (d - t.val + s) (concatWalk (d - t.val) s (suffixRevOf t) q) ∧
        concatWalk (d - t.val) s (suffixRevOf t) q 0 = p (Fin.last d) ∧
        concatWalk (d - t.val) s (suffixRevOf t) q (Fin.last (d - t.val + s)) =
          q (Fin.last s) := by
    intro t s q hq
    obtain ⟨hqnb, hq0, hqf⟩ := (Finset.mem_filter.mp hq).2
    have hsub_nb : IsNBWalk H' (d - t.val) (subWalk p t.val (d - t.val) (by omega)) :=
      isNBWalk_subWalk hp t.val (d - t.val) (by omega)
    have hrev_nb : IsNBWalk H' (d - t.val) (suffixRevOf t) := isNBWalk_revWalk hsub_nb
    have hjoin : suffixRevOf t (Fin.last (d - t.val)) = q 0 := by
      simp only [suffixRevOf, revWalk_last, subWalk, Fin.val_zero, add_zero]
      exact hq0.symm
    have hnb : IsNBWalk H' (d - t.val + s) (concatWalk (d - t.val) s (suffixRevOf t) q) := by
      refine isNBWalk_concatWalk hrev_nb hqnb hjoin ?_
      intro hdt hs heq
      apply hqf hs
      have hprev : suffixRevOf t ⟨d - t.val - 1, by omega⟩ = p ⟨t.val + 1, by omega⟩ := by
        simp only [suffixRevOf, revWalk, subWalk]
        congr 1; ext; simp [Fin.val_rev]; omega
      rw [← heq, hprev]
      simp only [forb, Finset.mem_union]
      right
      have htd : t.val < d := by omega
      simp [htd]
    have h0 : concatWalk (d - t.val) s (suffixRevOf t) q 0 = p (Fin.last d) := by
      have hle : concatWalk (d - t.val) s (suffixRevOf t) q ⟨0, by omega⟩ =
          suffixRevOf t ⟨0, by omega⟩ := concatWalk_le 0 (by omega)
      calc concatWalk (d - t.val) s (suffixRevOf t) q 0
          = suffixRevOf t 0 := hle
        _ = subWalk p t.val (d - t.val) (by omega) (Fin.last (d - t.val)) :=
            revWalk_zero _ _
        _ = p (Fin.last d) := by
            simp only [subWalk, Fin.last]
            congr 1; apply Fin.ext; dsimp; omega
    have hlast : concatWalk (d - t.val) s (suffixRevOf t) q (Fin.last (d - t.val + s)) =
        q (Fin.last s) := by
      have := concatWalk_ge hjoin (d - t.val + s) (by omega) le_rfl
      simpa [Fin.last, Nat.add_sub_cancel_left] using this
    exact ⟨hnb, h0, hlast⟩
  let idxSet : Finset (Fin (d + 1) × ℕ) :=
    ((Finset.univ : Finset (Fin (d + 1))).sigma fun t =>
      Finset.range (R - max t.val (d - t.val) + 1)).map
      ⟨fun q => (q.1, q.2), fun a b h => by
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        cases a; cases b; dsimp at h1 h2; subst h1; subst h2; rfl⟩
  let bVerts (ts : Fin (d + 1) × ℕ) : Finset V' :=
    (branchWalks ts.1 ts.2).image fun q => q (Fin.last ts.2)
  have hmem_idx : ∀ ts ∈ idxSet, ts.2 ≤ R - max ts.1.val (d - ts.1.val) := by
    intro ⟨t, s⟩ hts
    obtain ⟨⟨t', s'⟩, hs', heq⟩ := Finset.mem_map.mp hts
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_sigma.mp hs').2)
  have hsum_bounds : ∀ ts ∈ idxSet, ts.1.val + ts.2 ≤ R ∧ d - ts.1.val + ts.2 ≤ R := by
    intro ⟨t, s⟩ hts
    have hs := hmem_idx (t, s) hts
    have ht_le : t.val ≤ d := by omega
    have hmax_le : max t.val (d - t.val) ≤ R := (max_le (ht_le.trans hdR) (by omega))
    exact ⟨by have := le_max_left t.val (d - t.val); omega,
      by have := le_max_right t.val (d - t.val); omega⟩
  have huniq_tsq : ∀ {t₁ t₂ : Fin (d + 1)} {s₁ s₂ : ℕ}
      (h1 : (t₁, s₁) ∈ idxSet) (h2 : (t₂, s₂) ∈ idxSet)
      {q₁ : Fin (s₁ + 1) → V'} {q₂ : Fin (s₂ + 1) → V'}
      (hq₁ : q₁ ∈ branchWalks t₁ s₁) (hq₂ : q₂ ∈ branchWalks t₂ s₂),
      q₁ (Fin.last s₁) = q₂ (Fin.last s₂) →
      t₁ = t₂ ∧ s₁ = s₂ := by
    intro t₁ t₂ s₁ s₂ h1 h2 q₁ q₂ hq₁ hq₂ hend
    have hb1 : t₁.val + s₁ ≤ R := (hsum_bounds (t₁, s₁) h1).1
    have hb2 : t₂.val + s₂ ≤ R := (hsum_bounds (t₂, s₂) h2).1
    obtain ⟨hnb1, h01, hl1⟩ := htoU t₁ s₁ q₁ hq₁
    obtain ⟨hnb2, h02, hl2⟩ := htoU t₂ s₂ q₂ hq₂
    obtain ⟨hlen, hwalk⟩ := isNBWalk_eq_of_no_closed_sum hg2R (by omega : (t₁.val + s₁) +
      (t₂.val + s₂) ≤ 2 * R) hnb1 hnb2 (h01.trans h02.symm)
      (hl1.trans (hend.trans hl2.symm))
    have ht_not_lt : ∀ {a b : Fin (d + 1)} {sa sb : ℕ}
        {qa : Fin (sa + 1) → V'} {qb : Fin (sb + 1) → V'},
        qa ∈ branchWalks a sa → qb ∈ branchWalks b sb →
        (hsum : a.val + sa = b.val + sb) →
        (∀ i : ℕ, (hi : i ≤ a.val + sa) →
          concatWalk a.val sa (prefixOf a) qa ⟨i, by omega⟩ =
          concatWalk b.val sb (prefixOf b) qb ⟨i, by omega⟩) →
        ¬ (a.val < b.val) := by
      intro a b sa sb qa qb hqa _ hsum' hweq hlt
      have hsa_pos : 0 < sa := by omega
      have hjoin_a : prefixOf a (Fin.last a.val) = qa 0 := by
        rw [(Finset.mem_filter.mp hqa).2.2.1]; rfl
      have hstep := hweq (a.val + 1) (by omega)
      rw [concatWalk_ge hjoin_a (a.val + 1) (by omega) (by omega),
        concatWalk_le (a.val + 1) (by omega)] at hstep
      have hsub : a.val + 1 - a.val = 1 := by omega
      have hq1 : qa ⟨1, by omega⟩ = p ⟨a.val + 1, by omega⟩ := by
        simpa [hsub, prefixOf] using hstep
      have hmem_forb : qa ⟨1, by omega⟩ ∈ forb a := by
        rw [hq1]; simp only [forb, Finset.mem_union]; right
        have had : a.val < d := by omega
        simp [had]
      exact (Finset.mem_filter.mp hqa).2.2.2 hsa_pos hmem_forb
    have h12 : ¬ t₁.val < t₂.val := ht_not_lt hq₁ hq₂ hlen hwalk
    have h21 : ¬ t₂.val < t₁.val := ht_not_lt hq₂ hq₁ hlen.symm fun i hi =>
      (hwalk i (by omega)).symm
    have ht_eq : t₁ = t₂ := Fin.ext (by omega)
    exact ⟨ht_eq, by cases ht_eq; omega⟩
  have hcard_bVerts : ∀ ts ∈ idxSet, (bVerts ts).card = (branchWalks ts.1 ts.2).card := by
    intro ⟨t, s⟩ hts
    refine Finset.card_image_of_injOn fun q₁ hq₁ q₂ hq₂ hend => ?_
    obtain ⟨hnb1, h01, hl1⟩ := htoU t s q₁ hq₁
    obtain ⟨hnb2, h02, hl2⟩ := htoU t s q₂ hq₂
    have hle : t.val + s ≤ R := (hsum_bounds (t, s) hts).1
    obtain ⟨_, hwalk⟩ := isNBWalk_eq_of_no_closed_sum hg2R (by omega : (t.val + s) +
      (t.val + s) ≤ 2 * R) hnb1 hnb2 (h01.trans h02.symm)
      (hl1.trans (hend.trans hl2.symm))
    have hj1 : prefixOf t (Fin.last t.val) = q₁ 0 := by
      rw [(Finset.mem_filter.mp hq₁).2.2.1]; rfl
    have hj2 : prefixOf t (Fin.last t.val) = q₂ 0 := by
      rw [(Finset.mem_filter.mp hq₂).2.2.1]; rfl
    ext i
    have hi := hwalk (t.val + i.val) (by omega)
    rw [concatWalk_ge hj1 (t.val + i.val) (by omega) (by omega),
      concatWalk_ge hj2 (t.val + i.val) (by omega) (by omega)] at hi
    simpa [Nat.add_sub_cancel_left] using hi
  have hdisj : Set.PairwiseDisjoint (idxSet : Set (Fin (d + 1) × ℕ)) bVerts := by
    intro ts₁ h1 ts₂ h2 hne
    change Disjoint (bVerts ts₁) (bVerts ts₂)
    rw [Finset.disjoint_left]
    intro x' hx₁ hx₂
    obtain ⟨q₁, hq₁, hxq₁⟩ := Finset.mem_image.mp hx₁
    obtain ⟨q₂, hq₂, hxq₂⟩ := Finset.mem_image.mp hx₂
    obtain ⟨ht, hs⟩ := huniq_tsq h1 h2 hq₁ hq₂ (hxq₁.trans hxq₂.symm)
    exact hne (Prod.ext ht hs)
  let U : Finset V' := idxSet.biUnion bVerts
  have houtside : ∀ x' ∈ (Finset.univ : Finset V'), x' ∉ U →
      Real.sqrt (pushedProb H' R (p 0) x' * pushedProb H' R (p (Fin.last d)) x') = 0 := by
    intro x' _ hxU
    by_contra hnz
    have hmul_nz : pushedProb H' R (p 0) x' * pushedProb H' R (p (Fin.last d)) x' ≠ 0 := by
      intro h0; apply hnz; simp [h0]
    obtain ⟨k₁, hk₁, w₁, hnb₁, h0₁, hl₁⟩ :=
      exists_nbWalk_of_pushedProb_ne_zero (left_ne_zero_of_mul hmul_nz)
    obtain ⟨k₂, hk₂, w₂, hnb₂, h0₂, hl₂⟩ :=
      exists_nbWalk_of_pushedProb_ne_zero (right_ne_zero_of_mul hmul_nz)
    let hit : Finset ℕ := (Finset.range (min k₁ d + 1)).filter fun i =>
      if h : i ≤ min k₁ d then w₁ ⟨i, by have := min_le_left k₁ d; omega⟩ =
        p ⟨i, by have := min_le_right k₁ d; omega⟩ else False
    have hhit_ne : hit.Nonempty := ⟨0, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), by
        simp only [Nat.zero_le, ↓reduceDIte]; exact h0₁⟩⟩
    let t₀ : ℕ := hit.max' hhit_ne
    have ht₀_mem := Finset.max'_mem hit hhit_ne
    have ht₀_le_min : t₀ ≤ min k₁ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp
      (Finset.mem_filter.mp ht₀_mem).1)
    have ht₀_k1 : t₀ ≤ k₁ := ht₀_le_min.trans (min_le_left _ _)
    have ht₀_d : t₀ ≤ d := ht₀_le_min.trans (min_le_right _ _)
    have ht₀_eq : w₁ ⟨t₀, by omega⟩ = p ⟨t₀, by omega⟩ := by
      have hspec := (Finset.mem_filter.mp ht₀_mem).2
      dsimp only [hit] at hspec
      split_ifs at hspec
      · exact hspec
      · exact hspec
    let t : Fin (d + 1) := ⟨t₀, by omega⟩
    have hprefix_eq : ∀ i : ℕ, (hi : i ≤ t₀) →
        w₁ ⟨i, by omega⟩ = p ⟨i, by omega⟩ := by
      obtain ⟨_, heq⟩ := isNBWalk_eq_of_no_closed_sum hg2R (by omega : t₀ + t₀ ≤ 2 * R)
        (isNBWalk_prefix hnb₁ t₀ ht₀_k1) (isNBWalk_prefix hp t₀ ht₀_d) h0₁ ht₀_eq
      exact heq
    let s : ℕ := k₁ - t₀
    let q : Fin (s + 1) → V' := subWalk w₁ t₀ s (by omega)
    have hq_mem : q ∈ branchWalks t s := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, isNBWalk_subWalk hnb₁ t₀ s (by omega),
        ?_, ?_⟩
      · simpa [q, subWalk, t] using ht₀_eq
      · intro hs_pos hmem
        have hs_k1 : t₀ < k₁ := by dsimp [s] at hs_pos; omega
        simp only [forb, Finset.mem_union] at hmem
        rcases hmem with h1 | h2
        · split_ifs at h1 with htpos
          · have ht0_pos : 0 < t₀ := htpos
            have hq1 := Finset.mem_singleton.mp h1
            have hprev := hprefix_eq (t₀ - 1) (by omega)
            have hne := hnb₁.ne_two_step (i := t₀ - 1) (by omega)
            apply hne
            rw [hprev]
            simpa [q, subWalk, t, show t₀ - 1 + 2 = t₀ + 1 by omega] using hq1.symm
          · exact (Finset.notMem_empty _ h1).elim
        · split_ifs at h2 with htd
          · have ht0_lt_d : t₀ < d := htd
            have hq1 := Finset.mem_singleton.mp h2
            have hmin : t₀ + 1 ≤ min k₁ d := le_min (by omega) (by omega)
            have hmem' : t₀ + 1 ∈ hit := Finset.mem_filter.mpr
              ⟨Finset.mem_range.mpr (by omega), by
                simp only [hmin, ↓reduceDIte]
                simpa [q, subWalk, t] using hq1⟩
            have hle := Finset.le_max' hit (t₀ + 1) hmem'
            omega
          · exact (Finset.notMem_empty _ h2).elim
    obtain ⟨hnbV, h0V, hlV⟩ := htoV t s q hq_mem
    have hqlast : q (Fin.last s) = x' := by
      simpa [q, subWalk, Fin.last, s, show t₀ + (k₁ - t₀) = k₁ by omega] using hl₁
    have hsum_bound : (d - t₀ + s) + k₂ ≤ 2 * R + d := by
      have hs_def : s = k₁ - t₀ := rfl; omega
    obtain ⟨hlen, _⟩ := isNBWalk_eq_of_no_closed_sum hgirth hsum_bound hnbV hnb₂
      (h0V.trans h0₂.symm) (hlV.trans (hqlast.trans hl₂.symm))
    have hdt_s : d - t₀ + s = k₂ := hlen
    have hts_mem : (t, s) ∈ idxSet := by
      refine Finset.mem_map.mpr ⟨⟨t, s⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ t,
        Finset.mem_range.mpr ?_⟩, rfl⟩
      rcases le_total t.val (d - t.val) with h | h
      · rw [max_eq_right h]; dsimp [t, s]; omega
      · rw [max_eq_left h]; dsimp [t, s]; omega
    exact hxU (Finset.mem_biUnion.mpr ⟨(t, s), hts_mem,
      Finset.mem_image.mpr ⟨q, hq_mem, hqlast⟩⟩)
  have hval : ∀ ts ∈ idxSet, ∀ x' ∈ bVerts ts,
      Real.sqrt (pushedProb H' R (p 0) x' * pushedProb H' R (p (Fin.last d)) x') =
        (shellNorm R)⁻¹ * (2 : ℝ) ^ (-(d : ℝ) / 2) * (2 : ℝ)⁻¹ ^ ts.2 := by
    rintro ⟨t, s⟩ hts x' hx'
    obtain ⟨q, hq, hql⟩ := Finset.mem_image.mp hx'
    obtain ⟨hbU, hbV⟩ := hsum_bounds (t, s) hts
    obtain ⟨hnbU, h0U, hlU⟩ := htoU t s q hq
    obtain ⟨hnbV, h0V, hlV⟩ := htoV t s q hq
    have hpU : pushedProb H' R (p 0) x' = (shellNorm R)⁻¹ * (2 : ℝ)⁻¹ ^ (t.val + s) :=
      pushedProb_eq_of_nbWalk_of_no_closed hg2R hbU hnbU h0U (hlU.trans hql)
    have hpV : pushedProb H' R (p (Fin.last d)) x' =
        (shellNorm R)⁻¹ * (2 : ℝ)⁻¹ ^ (d - t.val + s) :=
      pushedProb_eq_of_nbWalk_of_no_closed hg2R hbV hnbV h0V (hlV.trans hql)
    rw [hpU, hpV]
    have hsn_nn : 0 ≤ (shellNorm R)⁻¹ := (shellNorm_pos R).le |> inv_nonneg.mpr
    have h2nn : (0 : ℝ) ≤ (2 : ℝ) ^ (-(d : ℝ) / 2) := by positivity
    have heq_sq : (shellNorm R)⁻¹ * (2 : ℝ)⁻¹ ^ (t.val + s) *
        ((shellNorm R)⁻¹ * (2 : ℝ)⁻¹ ^ (d - t.val + s)) =
        ((shellNorm R)⁻¹ * (2 : ℝ) ^ (-(d : ℝ) / 2) * (2 : ℝ)⁻¹ ^ s) ^ 2 := by
      have hpow_d : ((2 : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 = (2 : ℝ)⁻¹ ^ d := by
        rw [← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
          show (-(d : ℝ) / 2) * ((2 : ℕ) : ℝ) = -(d : ℝ) by push_cast; ring,
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast, inv_pow]
      have hsum_exp : (t.val + s) + (d - t.val + s) = d + (s + s) := by omega
      calc (shellNorm R)⁻¹ * (2 : ℝ)⁻¹ ^ (t.val + s) *
            ((shellNorm R)⁻¹ * (2 : ℝ)⁻¹ ^ (d - t.val + s))
          = (shellNorm R)⁻¹ ^ 2 * ((2 : ℝ)⁻¹ ^ (t.val + s) * (2 : ℝ)⁻¹ ^ (d - t.val + s)) := by
              ring
        _ = (shellNorm R)⁻¹ ^ 2 * (2 : ℝ)⁻¹ ^ ((t.val + s) + (d - t.val + s)) := by
              rw [← pow_add]
        _ = (shellNorm R)⁻¹ ^ 2 * (2 : ℝ)⁻¹ ^ (d + (s + s)) := by rw [hsum_exp]
        _ = (shellNorm R)⁻¹ ^ 2 * ((2 : ℝ)⁻¹ ^ d * ((2 : ℝ)⁻¹ ^ s) ^ 2) := by
              rw [pow_add, pow_add, ← sq]
        _ = ((shellNorm R)⁻¹ * (2 : ℝ) ^ (-(d : ℝ) / 2) * (2 : ℝ)⁻¹ ^ s) ^ 2 := by
              rw [← hpow_d]; ring
    rw [heq_sq, Real.sqrt_sq (by positivity)]
  have hsum_main :
      ∑ x' : V', Real.sqrt (pushedProb H' R (p 0) x' * pushedProb H' R (p (Fin.last d)) x') =
        ∑ ts ∈ idxSet, ((branchWalks ts.1 ts.2).card : ℝ) *
          ((shellNorm R)⁻¹ * (2 : ℝ) ^ (-(d : ℝ) / 2) * (2 : ℝ)⁻¹ ^ ts.2) := by
    rw [← Finset.sum_subset (Finset.subset_univ U) houtside, Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun ts hts => ?_
    rw [Finset.sum_congr rfl (fun x' hx' => hval ts hts x' hx'), Finset.sum_const, nsmul_eq_mul,
      hcard_bVerts ts hts]
  rw [hsum_main]
  have hsum_sigma :
      ∑ ts ∈ idxSet, ((branchWalks ts.1 ts.2).card : ℝ) *
        ((shellNorm R)⁻¹ * (2 : ℝ) ^ (-(d : ℝ) / 2) * (2 : ℝ)⁻¹ ^ ts.2) =
      (shellNorm R)⁻¹ * (2 : ℝ) ^ (-(d : ℝ) / 2) *
        ∑ t : Fin (d + 1), ∑ s ∈ Finset.range (R - max t.val (d - t.val) + 1),
          ((branchWalks t s).card : ℝ) * (2 : ℝ)⁻¹ ^ s := by
    dsimp only [idxSet]
    rw [Finset.sum_map, Finset.sum_sigma, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    change ((branchWalks t s).card : ℝ) *
      ((shellNorm R)⁻¹ * (2 : ℝ) ^ (-(d : ℝ) / 2) * (2 : ℝ)⁻¹ ^ s) = _
    ring
  rw [hsum_sigma]
  simp only [treeOverlap, show d ≠ 0 by omega, ↓reduceIte, hdR]
  congr 1
  have hline : ∀ (t : Fin (d + 1)) (c : ℕ), (forb t).card = c → c ≤ 3 →
      ∑ s ∈ Finset.range (R - max t.val (d - t.val) + 1),
        ((branchWalks t s).card : ℝ) * (2 : ℝ)⁻¹ ^ s =
        1 + ((3 - c : ℕ) : ℝ) / 2 * ((R - max t.val (d - t.val) : ℕ) : ℝ) := by
    intro t c hfc _
    have hterm : ∀ s : ℕ, ((branchWalks t s).card : ℝ) * (2 : ℝ)⁻¹ ^ s =
        if s = 0 then (1 : ℝ) else ((3 - c : ℕ) : ℝ) / 2 := by
      intro s
      have hc := card_nbWalk_avoid H' hreg (p t) (forb t) (hforb_adj t) s
      change (branchWalks t s).card = _ at hc
      rw [hc, hfc]
      rcases s with _ | s
      · simp
      · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
          show s + 1 - 1 = s by omega]
        push_cast
        have hpow : (2 : ℝ) ^ s * (2 : ℝ)⁻¹ ^ (s + 1) = (2 : ℝ)⁻¹ := by
          rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
            one_pow, one_mul]
        rw [mul_assoc, hpow]
        ring
    simp_rw [hterm, Finset.sum_range_succ']
    simp only [↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    ring
  let g : ℕ → ℝ := fun t =>
    if h : t < d + 1 then
      ∑ s ∈ Finset.range (R - max t (d - t) + 1),
        ((branchWalks ⟨t, h⟩ s).card : ℝ) * (2 : ℝ)⁻¹ ^ s
    else 0
  have hfin_eq : ∑ t : Fin (d + 1), ∑ s ∈ Finset.range (R - max t.val (d - t.val) + 1),
      ((branchWalks t s).card : ℝ) * (2 : ℝ)⁻¹ ^ s = ∑ t ∈ Finset.range (d + 1), g t := by
    rw [← Fin.sum_univ_eq_sum_range g (d + 1)]
    exact Finset.sum_congr rfl fun t _ => by simp only [g, t.isLt, ↓reduceDIte]
  rw [hfin_eq]
  have hsplit : Finset.range (d + 1) =
      insert 0 (insert d (Finset.Ioo 0 d)) := by
    ext t; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]; omega
  have h0_nm : (0 : ℕ) ∉ insert d (Finset.Ioo 0 d) := by
    simp only [Finset.mem_insert, Finset.mem_Ioo]; omega
  have hd_nm : d ∉ Finset.Ioo 0 d := by simp only [Finset.mem_Ioo]; omega
  rw [hsplit, Finset.sum_insert h0_nm, Finset.sum_insert hd_nm]
  have h0_val : g 0 = 1 + ((R - d : ℕ) : ℝ) := by
    have hlt0 : 0 < d + 1 := by omega
    simp only [g, hlt0, ↓reduceDIte]
    have hl := hline ⟨0, hlt0⟩ 1 hforb_card_zero (by omega)
    simp only [Nat.sub_zero, max_eq_right (Nat.zero_le d)] at hl ⊢
    rw [hl]; norm_num
  have hd_val : g d = 1 + ((R - d : ℕ) : ℝ) := by
    have hltd : d < d + 1 := by omega
    simp only [g, hltd, ↓reduceDIte]
    have hl := hline ⟨d, hltd⟩ 1 hforb_card_last (by omega)
    simp only [Nat.sub_self, max_eq_left (Nat.zero_le d)] at hl ⊢
    rw [hl]; norm_num
  have hmid_val : ∑ t ∈ Finset.Ioo 0 d, g t =
      ∑ t ∈ Finset.Ioo 0 d, (1 + ((R - max t (d - t) : ℕ) : ℝ) / 2) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have ⟨ht0, htd⟩ := Finset.mem_Ioo.mp ht
    have hltt : t < d + 1 := by omega
    simp only [g, hltt, ↓reduceDIte]
    have hl := hline ⟨t, hltt⟩ 2 (hforb_card_mid ⟨t, hltt⟩ ht0 htd) (by omega)
    simpa only [show 3 - 2 = 1 by omega, Nat.cast_one] using
      (hl.trans (by ring))
  rw [h0_val, hd_val, hmid_val]
  ring

/-- **Exact radial overlap on high-girth cubic graphs:** if `H'` is finite cubic with no closed
non-backtracking walk of length `1 ≤ k ≤ 2 * R + d`, `d ≤ R`, and `w` is a non-backtracking walk
of length `d`, then the overlap between `w a` and `w b` equals `treeOverlap R |a - b|`. -/
theorem sum_sqrt_pushedProb_eq_treeOverlap {V' : Type*} [Fintype V']
    (H' : SimpleGraph V') (hreg : ∀ v : V', open Classical in H'.degree v = 3)
    {R d : ℕ} (hdR : d ≤ R)
    (hgirth : ∀ (k : ℕ), 1 ≤ k → k ≤ 2 * R + d →
      ∀ w' : Fin (k + 1) → V', IsNBWalk H' k w' → w' 0 ≠ w' (Fin.last k))
    {w : Fin (d + 1) → V'} (hw : IsNBWalk H' d w) (a b : Fin (d + 1)) :
    ∑ x' : V', Real.sqrt (pushedProb H' R (w a) x' * pushedProb H' R (w b) x') =
      treeOverlap R (Int.natAbs ((a : ℤ) - (b : ℤ))) := by
  rcases lt_trichotomy a.val b.val with hlt | heq | hgt
  · have hdist : Int.natAbs ((a : ℤ) - (b : ℤ)) = b.val - a.val := by omega
    rw [hdist]
    have hsub := isNBWalk_subWalk hw a.val (b.val - a.val) (by omega)
    have hg : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * R + (b.val - a.val) →
        ∀ w' : Fin (k + 1) → V', IsNBWalk H' k w' → w' 0 ≠ w' (Fin.last k) :=
      fun k h1 h2 => hgirth k h1 (by omega)
    have hres := sum_sqrt_pushedProb_eq_treeOverlap_pos H' hreg (by omega : 1 ≤ b.val - a.val)
      (by omega : b.val - a.val ≤ R) hg hsub
    have h0 : subWalk w a.val (b.val - a.val) (by omega) 0 = w a := by
      simp [subWalk]
    have hl : subWalk w a.val (b.val - a.val) (by omega) (Fin.last (b.val - a.val)) = w b := by
      simp only [subWalk, Fin.last]
      congr 1; ext; dsimp; omega
    rwa [h0, hl] at hres
  · have hab : a = b := Fin.ext heq
    subst hab
    simp only [sub_self, Int.natAbs_zero, treeOverlap_zero]
    calc ∑ x' : V', Real.sqrt (pushedProb H' R (w a) x' * pushedProb H' R (w a) x')
        = ∑ x' : V', pushedProb H' R (w a) x' :=
          Finset.sum_congr rfl fun x' _ => by
            rw [← sq, Real.sqrt_sq (pushedProb_nonneg H' R (w a) x')]
      _ = 1 := sum_pushedProb_eq_one H' hreg R (w a)
  · have hdist : Int.natAbs ((a : ℤ) - (b : ℤ)) = a.val - b.val := by omega
    rw [hdist]
    have hsub := isNBWalk_subWalk hw b.val (a.val - b.val) (by omega)
    have hg : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * R + (a.val - b.val) →
        ∀ w' : Fin (k + 1) → V', IsNBWalk H' k w' → w' 0 ≠ w' (Fin.last k) :=
      fun k h1 h2 => hgirth k h1 (by omega)
    have hres := sum_sqrt_pushedProb_eq_treeOverlap_pos H' hreg (by omega : 1 ≤ a.val - b.val)
      (by omega : a.val - b.val ≤ R) hg hsub
    have h0 : subWalk w b.val (a.val - b.val) (by omega) 0 = w b := by
      simp [subWalk]
    have hl : subWalk w b.val (a.val - b.val) (by omega) (Fin.last (a.val - b.val)) = w a := by
      simp only [subWalk, Fin.last]
      congr 1; ext; dsimp; omega
    rw [h0, hl] at hres
    simpa only [mul_comm] using hres

/-- Exact inner product of two wave row vectors along a non-backtracking walk in a high-girth
cubic graph `H'`. -/
theorem waveRow_inner_eq_treeOverlap {V' : Type*} [Fintype V']
    (H' : SimpleGraph V') (hreg : ∀ v : V', open Classical in H'.degree v = 3)
    {R d : ℕ} (hdR : d ≤ R) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hgirth : ∀ (k : ℕ), 1 ≤ k → k ≤ 2 * R + d →
      ∀ w' : Fin (k + 1) → V', IsNBWalk H' k w' → w' 0 ≠ w' (Fin.last k))
    {w : Fin (d + 1) → V'} (hw : IsNBWalk H' d w) (a b : Fin (d + 1)) :
    ∑ z' : V' ⊕ V', waveRow H' R ε (w a) z' * waveRow H' R ε (w b) z' =
      (1 - ε ^ 2) * treeOverlap R (Int.natAbs ((a : ℤ) - (b : ℤ))) +
        if a = b then ε ^ 2 else 0 := by
  classical
  rw [waveRow_inner_eq H' R hε0 hε1 (w a) (w b),
    sum_sqrt_pushedProb_eq_treeOverlap H' hreg hdR hgirth hw a b]
  congr 1
  have hiff : w a = w b ↔ a = b := by
    constructor
    · intro hwa
      by_contra hne
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
      · have hsub := isNBWalk_subWalk hw a.val (b.val - a.val) (by omega)
        refine hgirth (b.val - a.val) (by omega) (by omega) _ hsub ?_
        simp only [subWalk, Fin.last, Fin.val_zero, add_zero]
        have heq : (⟨a.val + (b.val - a.val), by omega⟩ : Fin (d + 1)) = b :=
          Fin.ext (by dsimp; omega)
        rw [heq]; exact hwa
      · have hsub := isNBWalk_subWalk hw b.val (a.val - b.val) (by omega)
        refine hgirth (a.val - b.val) (by omega) (by omega) _ hsub ?_
        simp only [subWalk, Fin.last, Fin.val_zero, add_zero]
        have heq : (⟨b.val + (a.val - b.val), by omega⟩ : Fin (d + 1)) = a :=
          Fin.ext (by dsimp; omega)
        rw [heq]; exact hwa.symm
    · intro h; subst h; rfl
  simp [hiff]

end TreeOverlap

/-! ### Stationary AR(2) Gaussian realization and alternating orthant probability -/

section AR2Process

/-- Lower-triangular coefficient sequence realizing the stationary Gaussian process with
covariance `treeCovLimit |a - b|`. -/
noncomputable def ar2Coeff : ℕ → ℕ → ℝ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k = 0 then 2 * Real.sqrt 2 / 3 else if k = 1 then 1 / 3 else 0
  | i + 2, k =>
      Real.sqrt 2 * ar2Coeff (i + 1) k - (1 / 2) * ar2Coeff i k +
        if k = i + 2 then 1 / Real.sqrt 12 else 0

/-- Lower-triangular support of `ar2Coeff`: `ar2Coeff i k = 0` whenever `i < k`. -/
theorem ar2Coeff_eq_zero_of_lt {i k : ℕ} (h : i < k) : ar2Coeff i k = 0 := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    match i with
    | 0 => simp [ar2Coeff, show k ≠ 0 by omega]
    | 1 => simp [ar2Coeff, show k ≠ 0 by omega, show k ≠ 1 by omega]
    | i' + 2 =>
      simp only [ar2Coeff]
      rw [ih (i' + 1) (by omega) (by omega), ih i' (by omega) (by omega)]
      simp [show k ≠ i' + 2 by omega]

/-- Diagonal entries of `ar2Coeff` are strictly positive (`1`, `1 / 3`, and `1 / √12`). -/
theorem ar2Coeff_diag (i : ℕ) :
    ar2Coeff i i = if i = 0 then 1 else if i = 1 then 1 / 3 else 1 / Real.sqrt 12 := by
  match i with
  | 0 => simp [ar2Coeff]
  | 1 => simp [ar2Coeff]
  | i' + 2 =>
    simp only [ar2Coeff, ↓reduceIte, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false]
    rw [ar2Coeff_eq_zero_of_lt (by omega : i' + 1 < i' + 2),
      ar2Coeff_eq_zero_of_lt (by omega : i' < i' + 2)]
    simp [show i' + 2 ≠ 1 by omega]

/-- Positivity of diagonal entries `ar2Coeff i i`. -/
theorem ar2Coeff_diag_pos (i : ℕ) : 0 < ar2Coeff i i := by
  rw [ar2Coeff_diag]
  split_ifs <;> positivity

private theorem ar2Coeff_inner_range_le {a b n : ℕ} (ha : a ≤ n) (hb : b ≤ n) :
    ∑ k ∈ Finset.range (n + 1), ar2Coeff a k * ar2Coeff b k =
      treeCovLimit (Int.natAbs ((a : ℤ) - (b : ℤ))) := by
  have hmain : ∀ s : ℕ, ∀ x y : ℕ, x + y = s → x ≤ y →
      ∑ k ∈ Finset.range (y + 1), ar2Coeff x k * ar2Coeff y k = treeCovLimit (y - x) := by
    intro s
    induction s using Nat.strong_induction_on with
    | ind s ih =>
      intro x y hxy hle
      have hcov_le : ∀ (u v : ℕ), u + v < s → u ≤ v → ∀ N : ℕ, v ≤ N →
          ∑ k ∈ Finset.range (N + 1), ar2Coeff u k * ar2Coeff v k = treeCovLimit (v - u) := by
        intro u v huv hule N hvN
        have hsub := Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hvN))
          (f := fun k => ar2Coeff u k * ar2Coeff v k) fun k _ hk => by
            have hkge : v + 1 ≤ k := by simpa [Finset.mem_range] using hk
            simp [ar2Coeff_eq_zero_of_lt (by omega : u < k)]
        rw [← hsub]
        exact ih (u + v) huv u v rfl hule
      match y with
      | 0 =>
        have hx0 : x = 0 := by omega
        subst hx0
        simp [ar2Coeff, treeCovLimit_zero]
      | 1 =>
        rcases eq_or_lt_of_le hle with rfl | hxlt
        · simp only [Nat.sub_self, treeCovLimit_zero]
          rw [Finset.sum_range_succ, Finset.sum_range_one]
          simp only [ar2Coeff, ↓reduceIte, Nat.one_ne_zero]
          have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
          nlinarith [hsq]
        · have hx0 : x = 0 := by omega
          subst hx0
          simp only [Nat.sub_zero, treeCovLimit_one]
          rw [Finset.sum_range_succ, Finset.sum_range_one]
          simp [ar2Coeff]
      | i + 2 =>
        rcases eq_or_lt_of_le hle with rfl | hxlt
        · simp only [Nat.sub_self, treeCovLimit_zero]
          rw [Finset.sum_range_succ]
          have hlast : ar2Coeff (i + 2) (i + 2) * ar2Coeff (i + 2) (i + 2) = 1 / 12 := by
            rw [ar2Coeff_diag (i + 2)]
            simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte,
              show i + 2 ≠ 1 by omega]
            have hsq : Real.sqrt 12 ^ 2 = 12 := Real.sq_sqrt (by norm_num)
            have hne : Real.sqrt 12 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
            field_simp [hne]; rw [hsq]
          have hpre : ∑ k ∈ Finset.range (i + 2),
              ar2Coeff (i + 2) k * ar2Coeff (i + 2) k =
              2 * (∑ k ∈ Finset.range (i + 2), ar2Coeff (i + 1) k * ar2Coeff (i + 1) k) -
                Real.sqrt 2 * (∑ k ∈ Finset.range (i + 2), ar2Coeff i k * ar2Coeff (i + 1) k) +
                (1 / 4) * (∑ k ∈ Finset.range (i + 2), ar2Coeff i k * ar2Coeff i k) := by
            have hterm : ∀ k ∈ Finset.range (i + 2),
                ar2Coeff (i + 2) k * ar2Coeff (i + 2) k =
                  2 * (ar2Coeff (i + 1) k * ar2Coeff (i + 1) k) -
                    Real.sqrt 2 * (ar2Coeff i k * ar2Coeff (i + 1) k) +
                    (1 / 4) * (ar2Coeff i k * ar2Coeff i k) := by
              intro k hk
              have hkne : k ≠ i + 2 := by
                have := Finset.mem_range.mp hk; omega
              simp only [ar2Coeff, hkne, ↓reduceIte, add_zero]
              have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
              linear_combination (ar2Coeff (i + 1) k) ^ 2 * hsq
            rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
          have haa := hcov_le (i + 1) (i + 1) (by omega) le_rfl (i + 1) le_rfl
          have hab := hcov_le i (i + 1) (by omega) (by omega) (i + 1) le_rfl
          have hbb := hcov_le i i (by omega) le_rfl (i + 1) (by omega)
          simp only [Nat.sub_self, show i + 1 - i = 1 by omega] at haa hab hbb
          rw [hpre, haa, hab, hbb, hlast, treeCovLimit_zero, treeCovLimit_one]
          have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
          nlinarith [hsq]
        · have hxle : x ≤ i + 1 := by omega
          have hzero : ar2Coeff x (i + 2) = 0 := ar2Coeff_eq_zero_of_lt (by omega)
          rw [Finset.sum_range_succ, hzero, zero_mul, add_zero]
          have hterm : ∀ k ∈ Finset.range (i + 2),
              ar2Coeff x k * ar2Coeff (i + 2) k =
                Real.sqrt 2 * (ar2Coeff x k * ar2Coeff (i + 1) k) -
                  (1 / 2) * (ar2Coeff x k * ar2Coeff i k) := by
            intro k hk
            have hkne : k ≠ i + 2 := by have := Finset.mem_range.mp hk; omega
            simp only [ar2Coeff, hkne, ↓reduceIte, add_zero]
            ring
          rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
          rcases eq_or_lt_of_le hxle with rfl | hxi
          · have h1 := hcov_le (i + 1) (i + 1) (by omega) le_rfl (i + 1) le_rfl
            have h2 := hcov_le i (i + 1) (by omega) (by omega) (i + 1) le_rfl
            have hcomm : ∑ k ∈ Finset.range (i + 2), ar2Coeff (i + 1) k * ar2Coeff i k =
                ∑ k ∈ Finset.range (i + 2), ar2Coeff i k * ar2Coeff (i + 1) k :=
              Finset.sum_congr rfl fun k _ => mul_comm _ _
            rw [h1, hcomm, h2]
            simp only [Nat.sub_self, show i + 1 - i = 1 by omega, show i + 2 - (i + 1) = 1 by omega,
              treeCovLimit_zero, treeCovLimit_one]
            ring
          · have h1 := hcov_le x (i + 1) (by omega) (by omega) (i + 1) le_rfl
            have h2 := hcov_le x i (by omega) (by omega) (i + 1) (by omega)
            rw [h1, h2]
            have hrec := treeCovLimit_rec (i - x)
            rw [show i - x + 2 = i + 2 - x by omega,
              show i - x + 1 = i + 1 - x by omega] at hrec
            exact hrec.symm
  rcases le_total a b with hab | hba
  · have hnat : Int.natAbs ((a : ℤ) - (b : ℤ)) = b - a := by omega
    rw [hnat]
    have hsub : ∑ k ∈ Finset.range (n + 1), ar2Coeff a k * ar2Coeff b k =
        ∑ k ∈ Finset.range (b + 1), ar2Coeff a k * ar2Coeff b k := by
      symm
      exact Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hb)) fun k _ hk => by
        have hkb : b + 1 ≤ k := by simpa [Finset.mem_range] using hk
        simp [ar2Coeff_eq_zero_of_lt (by omega : b < k)]
    rw [hsub]
    exact hmain (a + b) a b rfl hab
  · have hnat : Int.natAbs ((a : ℤ) - (b : ℤ)) = a - b := by omega
    rw [hnat]
    have hcomm : ∑ k ∈ Finset.range (n + 1), ar2Coeff a k * ar2Coeff b k =
        ∑ k ∈ Finset.range (n + 1), ar2Coeff b k * ar2Coeff a k :=
      Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hcomm]
    have hsub : ∑ k ∈ Finset.range (n + 1), ar2Coeff b k * ar2Coeff a k =
        ∑ k ∈ Finset.range (a + 1), ar2Coeff b k * ar2Coeff a k := by
      symm
      exact Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ ha)) fun k _ hk => by
        have hka : a + 1 ≤ k := by simpa [Finset.mem_range] using hk
        simp [ar2Coeff_eq_zero_of_lt (by omega : a < k)]
    rw [hsub]
    exact hmain (b + a) b a rfl hba

/-- Stationary AR(2) linear map taking i.i.d. standard Gaussians `ξ : Fin (j + 1) → ℝ` to a
centered Gaussian vector with covariance `treeCovLimit |a - b|`. -/
noncomputable def ar2StepMap (j : ℕ) (ξ : Fin (j + 1) → ℝ) : Fin (j + 1) → ℝ :=
  fun i => ∑ k : Fin (j + 1), ar2Coeff i.val k.val * ξ k

/-- Coordinate `0` of `ar2StepMap j ξ` is `ξ 0`. -/
theorem ar2StepMap_zero (j : ℕ) (ξ : Fin (j + 1) → ℝ) :
    ar2StepMap j ξ 0 = ξ 0 := by
  unfold ar2StepMap
  rw [Finset.sum_eq_single 0]
  · simp [ar2Coeff]
  · intro k _ hk
    have hkv : k.val ≠ 0 := fun h => hk (Fin.ext h)
    simp [ar2Coeff, hkv]
  · intro h0; exact absurd (Finset.mem_univ 0) h0

/-- Coordinate `1` of `ar2StepMap j ξ` is `(2 * √2 / 3) * ξ 0 + (1 / 3) * ξ 1`. -/
theorem ar2StepMap_one {j : ℕ} (hj : 1 ≤ j) (ξ : Fin (j + 1) → ℝ) :
    ar2StepMap j ξ ⟨1, by omega⟩ =
      (2 * Real.sqrt 2 / 3) * ξ 0 + (1 / 3) * ξ ⟨1, by omega⟩ := by
  unfold ar2StepMap
  have hsum : ∑ k : Fin (j + 1), ar2Coeff 1 k.val * ξ k =
      ∑ k ∈ ({(0 : Fin (j + 1)), ⟨1, by omega⟩} : Finset (Fin (j + 1))),
        ar2Coeff 1 k.val * ξ k := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    have h0 : k.val ≠ 0 := fun h => hk.1 (Fin.ext h)
    have h1 : k.val ≠ 1 := fun h => hk.2 (Fin.ext h)
    simp [ar2Coeff, h0, h1]
  rw [hsum]
  have hne : (0 : Fin (j + 1)) ≠ ⟨1, by omega⟩ := fun h => by
    have hv := congrArg Fin.val h
    exact Nat.zero_ne_one hv
  rw [Finset.sum_pair hne]
  simp [ar2Coeff]

/-- AR(2) recurrence for `ar2StepMap j ξ` at index `i + 2 ≤ j`. -/
theorem ar2StepMap_add_two {j i : ℕ} (hi : i + 2 ≤ j) (ξ : Fin (j + 1) → ℝ) :
    ar2StepMap j ξ ⟨i + 2, by omega⟩ =
      Real.sqrt 2 * ar2StepMap j ξ ⟨i + 1, by omega⟩ -
        (1 / 2) * ar2StepMap j ξ ⟨i, by omega⟩ +
        (1 / Real.sqrt 12) * ξ ⟨i + 2, by omega⟩ := by
  unfold ar2StepMap
  dsimp only
  simp_rw [ar2Coeff, add_mul, sub_mul, mul_assoc]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_eq_single ⟨i + 2, by omega⟩]
  · simp
  · intro k _ hk
    have hkne : k.val ≠ i + 2 := fun h => hk (Fin.ext h)
    simp [hkne]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

/-- `ar2StepMap` is causal (lower-triangular): appending a last coordinate does not alter
earlier outputs. -/
theorem ar2StepMap_snoc_castSucc (j : ℕ) (ξ : Fin (j + 1) → ℝ) (u : ℝ) (i : Fin (j + 1)) :
    ar2StepMap (j + 1) (Fin.snoc (α := fun _ => ℝ) ξ u) i.castSucc = ar2StepMap j ξ i := by
  unfold ar2StepMap
  rw [Fin.sum_univ_castSucc]
  have hlast : ar2Coeff i.castSucc.val (Fin.last (j + 1)).val *
      Fin.snoc (α := fun _ => ℝ) ξ u (Fin.last (j + 1)) = 0 := by
    rw [ar2Coeff_eq_zero_of_lt (by simp [Fin.last]; omega), zero_mul]
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl fun k _ => by simp [Fin.snoc_castSucc]

/-- Exact Gram matrix of `ar2StepMap j`: inner product of rows `a, b` is `treeCovLimit |a - b|`. -/
theorem ar2Coeff_inner_eq (j : ℕ) (a b : Fin (j + 1)) :
    ∑ k : Fin (j + 1), ar2Coeff a.val k.val * ar2Coeff b.val k.val =
      treeCovLimit (Int.natAbs ((a : ℤ) - (b : ℤ))) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => ar2Coeff a.val k * ar2Coeff b.val k) (j + 1)]
  exact ar2Coeff_inner_range_le (by omega) (by omega)

/-- Each row of `ar2Coeff` has unit Euclidean norm. -/
theorem ar2Coeff_sq_sum_eq_one (j : ℕ) (a : Fin (j + 1)) :
    ∑ k : Fin (j + 1), ar2Coeff a.val k.val ^ 2 = 1 := by
  simpa [sq, treeCovLimit_zero] using ar2Coeff_inner_eq j a a

/-- Alternating-sign orthant probability `2 * P(∀ i, (-1)^i * X_i > 0)` of the stationary AR(2)
Gaussian process of length `j`. -/
noncomputable def ar2AltProb (j : ℕ) : ℝ :=
  2 * (piGauss (Fin (j + 1))).real
    {ξ | ∀ i : Fin (j + 1), 0 < (-1 : ℝ) ^ i.val * ar2StepMap j ξ i}

private theorem measurePreserving_snoc_pi {n : ℕ} (ν : Measure ℝ) [SigmaFinite ν] :
    MeasurePreserving (fun p : (Fin n → ℝ) × ℝ => Fin.snoc (α := fun _ => ℝ) p.1 p.2)
      ((Measure.pi fun _ : Fin n => ν).prod ν)
      (Measure.pi fun _ : Fin (n + 1) => ν) := by
  have hmeas : Measurable (fun p : (Fin n → ℝ) × ℝ => Fin.snoc (α := fun _ => ℝ) p.1 p.2) := by
    rw [measurable_pi_iff]
    intro i
    induction i using Fin.lastCases with
    | last => simpa [Fin.snoc_last] using measurable_snd
    | cast j =>
      have heq : (fun p : (Fin n → ℝ) × ℝ =>
          Fin.snoc (α := fun _ => ℝ) p.1 p.2 j.castSucc) = fun p => p.1 j :=
        funext fun p => by simp [Fin.snoc_castSucc]
      rw [heq]
      exact (measurable_pi_apply j).comp measurable_fst
  refine ⟨hmeas, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (Fin n → ℝ) × ℝ => Fin.snoc (α := fun _ => ℝ) p.1 p.2) ⁻¹'
        Set.pi Set.univ s =
      (Set.pi Set.univ (fun i : Fin n => s i.castSucc)) ×ˢ s (Fin.last n) := by
    ext ⟨x, u⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, ?_⟩
      · simpa [Fin.snoc_castSucc] using h i.castSucc
      · simpa [Fin.snoc_last] using h (Fin.last n)
    · rintro ⟨hx, hu⟩ i
      induction i using Fin.lastCases with
      | last => simpa [Fin.snoc_last] using hu
      | cast j => simpa [Fin.snoc_castSucc] using hx j
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Fin.prod_univ_castSucc]

private theorem lintegral_gaussianReal_affine {a : ℝ} (ha : a ≠ 0) (m : ℝ)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ u, g (a * u + m) ∂(gaussianReal 0 1) =
      ∫⁻ z, gaussianPDF m ⟨a ^ 2, sq_nonneg a⟩ z * g z ∂volume := by
  have hva : (⟨a ^ 2, sq_nonneg a⟩ : ℝ≥0) ≠ 0 := by
    intro h
    have : a ^ 2 = 0 := congrArg NNReal.toReal h
    exact ha (sq_eq_zero_iff.mp this)
  have hmap : (gaussianReal 0 1).map (fun u => a * u + m) =
      gaussianReal m ⟨a ^ 2, sq_nonneg a⟩ := by
    have hcomp : (fun u : ℝ => a * u + m) = (· + m) ∘ (a * ·) := rfl
    rw [hcomp, ← Measure.map_map (measurable_add_const m) (measurable_const_mul a),
      gaussianReal_map_const_mul, gaussianReal_map_add_const]
    simp only [mul_zero, zero_add, mul_one]
    rfl
  calc ∫⁻ u, g (a * u + m) ∂(gaussianReal 0 1)
      = ∫⁻ z, g z ∂((gaussianReal 0 1).map (fun u => a * u + m)) :=
          (lintegral_map hg (by fun_prop)).symm
    _ = ∫⁻ z, g z ∂(gaussianReal m ⟨a ^ 2, sq_nonneg a⟩) := by rw [hmap]
    _ = ∫⁻ z, gaussianPDF m ⟨a ^ 2, sq_nonneg a⟩ z * g z ∂volume := by
          rw [gaussianReal_of_var_ne_zero m hva]
          exact lintegral_withDensity_eq_lintegral_mul volume (measurable_gaussianPDF m _) hg

private theorem gaussianPDF_init_mul (x y : ℝ) :
    gaussianPDFReal 0 1 x *
      gaussianPDFReal (-(2 * Real.sqrt 2 / 3) * x) ⟨(-1 / 3) ^ 2, sq_nonneg _⟩ y =
      (3 / (2 * Real.pi)) *
        Real.exp (-(9 / 2) * (x ^ 2 + y ^ 2) - 6 * Real.sqrt 2 * x * y) := by
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcoeff : (Real.sqrt (2 * Real.pi))⁻¹ *
      (Real.sqrt (2 * Real.pi * (-1 / 3 : ℝ) ^ 2))⁻¹ = 3 / (2 * Real.pi) := by
    have h1 : Real.sqrt (2 * Real.pi * (-1 / 3 : ℝ) ^ 2) =
        Real.sqrt (2 * Real.pi) * (1 / 3) := by
      rw [Real.sqrt_mul (by positivity), show (-1 / 3 : ℝ) ^ 2 = (1 / 3 : ℝ) ^ 2 by ring,
        Real.sqrt_sq (by norm_num)]
    rw [h1]
    have hsp : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have hsqpi : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
    field_simp [hsp, hpi.ne']
    nlinarith [hsqpi]
  have hexp : -(x ^ 2) / 2 + -(y - -(2 * Real.sqrt 2 / 3) * x) ^ 2 / (2 * (-1 / 3 : ℝ) ^ 2) =
      -(9 / 2) * (x ^ 2 + y ^ 2) - 6 * Real.sqrt 2 * x * y := by
    have hnum : (-(2 * Real.sqrt 2 / 3) * x) ^ 2 = 8 / 9 * x ^ 2 := by
      have : (2 * Real.sqrt 2 / 3) ^ 2 = 4 / 9 * Real.sqrt 2 ^ 2 := by ring
      rw [neg_mul, neg_sq, mul_pow, this, hsq2]; ring
    linear_combination -2 * x ^ 2 * hsq2
  calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) *
        ((Real.sqrt (2 * Real.pi * (-1 / 3 : ℝ) ^ 2))⁻¹ *
          Real.exp (-(y - -(2 * Real.sqrt 2 / 3) * x) ^ 2 / (2 * (-1 / 3 : ℝ) ^ 2)))
      = ((Real.sqrt (2 * Real.pi))⁻¹ *
          (Real.sqrt (2 * Real.pi * (-1 / 3 : ℝ) ^ 2))⁻¹) *
          (Real.exp (-(x ^ 2) / 2) *
            Real.exp (-(y - -(2 * Real.sqrt 2 / 3) * x) ^ 2 / (2 * (-1 / 3 : ℝ) ^ 2))) := by
          ring
    _ = (3 / (2 * Real.pi)) * Real.exp (-(x ^ 2) / 2 +
          -(y - -(2 * Real.sqrt 2 / 3) * x) ^ 2 / (2 * (-1 / 3 : ℝ) ^ 2)) := by
          rw [hcoeff, ← Real.exp_add]
    _ = _ := by rw [hexp]

private theorem gaussianPDF_kernel_eq (k : ℕ) (x y z : ℝ) :
    gaussianPDFReal (-Real.sqrt 2 * y - x / 2)
      ⟨((-1 : ℝ) ^ (k + 2) / Real.sqrt 12) ^ 2, sq_nonneg _⟩ z =
      Real.sqrt (6 / Real.pi) * Real.exp (-6 * (z + Real.sqrt 2 * y + x / 2) ^ 2) := by
  have h12 : ((-1 : ℝ) ^ (k + 2) / Real.sqrt 12) ^ 2 = 1 / 12 := by
    have hs : ((-1 : ℝ) ^ (k + 2)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [div_pow, hs, Real.sq_sqrt (by norm_num)]
  unfold gaussianPDFReal
  change (Real.sqrt (2 * Real.pi * ((-1 : ℝ) ^ (k + 2) / Real.sqrt 12) ^ 2))⁻¹ *
      Real.exp (-(z - (-Real.sqrt 2 * y - x / 2)) ^ 2 /
        (2 * ((-1 : ℝ) ^ (k + 2) / Real.sqrt 12) ^ 2)) = _
  rw [h12]
  have hcoeff : (Real.sqrt (2 * Real.pi * (1 / 12 : ℝ)))⁻¹ = Real.sqrt (6 / Real.pi) := by
    rw [show 2 * Real.pi * (1 / 12 : ℝ) = Real.pi / 6 by ring,
      ← Real.sqrt_inv, inv_div]
  have hexp : -(z - (-Real.sqrt 2 * y - x / 2)) ^ 2 / (2 * (1 / 12 : ℝ)) =
      -6 * (z + Real.sqrt 2 * y + x / 2) ^ 2 := by ring
  rw [hcoeff, hexp]

private noncomputable def ar2AltMap (j : ℕ) (ξ : Fin (j + 1) → ℝ) : Fin (j + 1) → ℝ :=
  fun i => (-1 : ℝ) ^ i.val * ar2StepMap j ξ i

private theorem measurable_ar2AltMap (j : ℕ) : Measurable (ar2AltMap j) := by
  rw [measurable_pi_iff]
  intro i
  unfold ar2AltMap ar2StepMap
  fun_prop

private theorem lintegral_ar2AltMap (j : ℕ) {f : (Fin (j + 1) → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ξ, f (ar2AltMap j ξ) ∂(piGauss (Fin (j + 1))) =
      ∫⁻ y, ENNReal.ofReal (ar2JointDensity j y) * f y
        ∂(Measure.pi fun _ : Fin (j + 1) => volume) := by
  induction j with
  | zero =>
    have hmp_g :=
      (MeasureTheory.measurePreserving_piUnique (fun _ : Fin 1 => gaussianReal 0 1)).symm
    have hmp_v :=
      (MeasureTheory.measurePreserving_piUnique (fun _ : Fin 1 => (volume : Measure ℝ))).symm
    have huni : ∀ u : ℝ, (MeasurableEquiv.piUnique fun _ : Fin 1 => ℝ).symm u = fun _ => u :=
      fun u => funext fun i => by fin_cases i; rfl
    have hl : ∫⁻ ξ, f (ar2AltMap 0 ξ) ∂(piGauss (Fin 1)) =
        ∫⁻ u, f (fun _ => u) ∂(gaussianReal 0 1) := by
      have hm := hmp_g.lintegral_comp (f := fun ξ => f (ar2AltMap 0 ξ))
        (hf.comp (measurable_ar2AltMap 0))
      rw [← hm]
      refine lintegral_congr fun u => congrArg f (funext fun i => ?_)
      rw [huni u]
      fin_cases i; simp [ar2AltMap, ar2StepMap_zero]
    have hr : ∫⁻ y, ENNReal.ofReal (ar2JointDensity 0 y) * f y
        ∂(Measure.pi fun _ : Fin 1 => volume) =
        ∫⁻ u, ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(u ^ 2) / 2)) *
          f (fun _ => u) ∂volume := by
      have hm := hmp_v.lintegral_comp
        (f := fun y => ENNReal.ofReal (ar2JointDensity 0 y) * f y)
        (((ar2JointDensity_continuous 0).measurable.ennreal_ofReal).mul hf)
      rw [← hm]
      refine lintegral_congr fun u => by rw [huni u]; simp [ar2JointDensity]
    have hf_const : Measurable (fun u : ℝ => f (fun _ : Fin 1 => u)) := by
      have heq : (fun u : ℝ => f (fun _ : Fin 1 => u)) =
          f ∘ (MeasurableEquiv.piUnique fun _ : Fin 1 => ℝ).symm :=
        funext fun u => congrArg f (huni u).symm
      rw [heq]; exact hf.comp hmp_v.measurable
    rw [hl, hr, gaussianReal_of_var_ne_zero 0 one_ne_zero,
      lintegral_withDensity_eq_lintegral_mul volume (measurable_gaussianPDF 0 1) hf_const]
    refine lintegral_congr fun u => ?_
    simp [gaussianPDF, gaussianPDFReal]
  | succ j ih =>
    let snoc : (Fin (j + 1) → ℝ) → ℝ → (Fin (j + 2) → ℝ) :=
      fun x u => Fin.snoc (α := fun _ => ℝ) x u
    have hmp_g := measurePreserving_snoc_pi (n := j + 1) (gaussianReal 0 1)
    have hmp_v := measurePreserving_snoc_pi (n := j + 1) (volume : Measure ℝ)
    have hprod_l : ∫⁻ ξ, f (ar2AltMap (j + 1) ξ) ∂(piGauss (Fin (j + 2))) =
        ∫⁻ ξ' : Fin (j + 1) → ℝ, ∫⁻ u : ℝ, f (ar2AltMap (j + 1) (snoc ξ' u))
          ∂(gaussianReal 0 1) ∂(piGauss (Fin (j + 1))) := by
      have hm := hmp_g.lintegral_comp (f := fun ξ => f (ar2AltMap (j + 1) ξ))
        (hf.comp (measurable_ar2AltMap (j + 1)))
      rw [← hm]
      exact lintegral_prod _
        (hf.comp ((measurable_ar2AltMap (j + 1)).comp hmp_g.measurable)).aemeasurable
    have hprod_r : ∫⁻ y, ENNReal.ofReal (ar2JointDensity (j + 1) y) * f y
        ∂(Measure.pi fun _ : Fin (j + 2) => volume) =
        ∫⁻ y' : Fin (j + 1) → ℝ, ∫⁻ z : ℝ,
          ENNReal.ofReal (ar2JointDensity (j + 1) (snoc y' z)) * f (snoc y' z)
          ∂volume ∂(Measure.pi fun _ : Fin (j + 1) => volume) := by
      have hm := hmp_v.lintegral_comp
        (f := fun y => ENNReal.ofReal (ar2JointDensity (j + 1) y) * f y)
        (((ar2JointDensity_continuous (j + 1)).measurable.ennreal_ofReal).mul hf)
      rw [← hm]
      exact lintegral_prod _ ((((ar2JointDensity_continuous (j + 1)).measurable.ennreal_ofReal).mul
        hf).comp hmp_v.measurable).aemeasurable
    rw [hprod_l, hprod_r]
    cases j with
    | zero =>
      have hsnoc_eq : ∀ (ξ' : Fin 1 → ℝ) (u : ℝ),
          ar2AltMap 1 (snoc ξ' u) =
            snoc (ar2AltMap 0 ξ')
              ((-1 / 3) * u + -(2 * Real.sqrt 2 / 3) * (ar2AltMap 0 ξ' 0)) := by
        intro ξ' u
        ext i; fin_cases i
        · change (-1 : ℝ) ^ 0 * ar2StepMap 1 (snoc ξ' u) (0 : Fin 1).castSucc =
              snoc (ar2AltMap 0 ξ') _ (0 : Fin 1).castSucc
          rw [ar2StepMap_snoc_castSucc 0 ξ' u 0]
          simp [snoc, ar2AltMap]
        · have h1 := ar2StepMap_one (j := 1) le_rfl (snoc ξ' u)
          have h0 : snoc ξ' u 0 = ξ' 0 := by
            change Fin.snoc (α := fun _ => ℝ) ξ' u (0 : Fin 1).castSucc = ξ' 0
            exact Fin.snoc_castSucc _ _ _
          have hlast : snoc ξ' u ⟨1, by omega⟩ = u := by
            change Fin.snoc (α := fun _ => ℝ) ξ' u (Fin.last 1) = u
            exact Fin.snoc_last _ _
          have hm : (snoc (ar2AltMap 0 ξ')
              ((-1 / 3) * u + -(2 * Real.sqrt 2 / 3) * (ar2AltMap 0 ξ' 0))) ⟨1, by omega⟩ =
              (-1 / 3) * u + -(2 * Real.sqrt 2 / 3) * (ar2AltMap 0 ξ' 0) :=
            Fin.snoc_last (α := fun _ => ℝ) _ _
          change (-1 : ℝ) ^ 1 * ar2StepMap 1 (snoc ξ' u) ⟨1, by omega⟩ = _
          rw [h1, h0, hlast, hm]
          simp only [ar2AltMap, Fin.val_zero, pow_zero, one_mul, ar2StepMap_zero, pow_one]
          ring
      have hstep : ∀ ξ' : Fin 1 → ℝ,
          ∫⁻ u : ℝ, f (ar2AltMap 1 (snoc ξ' u)) ∂(gaussianReal 0 1) =
            ∫⁻ z : ℝ, gaussianPDF (-(2 * Real.sqrt 2 / 3) * ar2AltMap 0 ξ' 0)
              ⟨(-1 / 3) ^ 2, sq_nonneg _⟩ z * f (snoc (ar2AltMap 0 ξ') z) ∂volume := by
        intro ξ'
        simp_rw [hsnoc_eq ξ']
        have hsnoc_m : Measurable (fun z : ℝ => snoc (ar2AltMap 0 ξ') z) := by
          have heq : (fun z : ℝ => snoc (ar2AltMap 0 ξ') z) =
              (fun p : (Fin 1 → ℝ) × ℝ => Fin.snoc p.1 p.2) ∘
                fun z => (ar2AltMap 0 ξ', z) := rfl
          rw [heq]
          exact hmp_v.measurable.comp (measurable_const.prodMk measurable_id)
        exact lintegral_gaussianReal_affine (by norm_num : (-1 / 3 : ℝ) ≠ 0) _ (hf.comp hsnoc_m)
      simp_rw [hstep]
      let G : (Fin 1 → ℝ) → ℝ≥0∞ := fun y' =>
        ∫⁻ z : ℝ, gaussianPDF (-(2 * Real.sqrt 2 / 3) * y' 0)
          ⟨(-1 / 3) ^ 2, sq_nonneg _⟩ z * f (snoc y' z) ∂volume
      have hG_meas : Measurable G := by
        refine Measurable.lintegral_prod_right' (f := fun p : (Fin 1 → ℝ) × ℝ =>
          gaussianPDF (-(2 * Real.sqrt 2 / 3) * p.1 0)
            ⟨(-1 / 3) ^ 2, sq_nonneg _⟩ p.2 * f (snoc p.1 p.2)) ?_
        have hpdf : Measurable (fun p : (Fin 1 → ℝ) × ℝ =>
            gaussianPDF (-(2 * Real.sqrt 2 / 3) * p.1 0) ⟨(-1 / 3) ^ 2, sq_nonneg _⟩ p.2) := by
          change Measurable (fun p : (Fin 1 → ℝ) × ℝ =>
            ENNReal.ofReal (gaussianPDFReal (-(2 * Real.sqrt 2 / 3) * p.1 0)
              ⟨(-1 / 3) ^ 2, sq_nonneg _⟩ p.2))
          refine (Continuous.measurable ?_).ennreal_ofReal
          unfold gaussianPDFReal
          fun_prop
        exact hpdf.mul (hf.comp hmp_v.measurable)
      change ∫⁻ ξ', G (ar2AltMap 0 ξ') ∂(piGauss (Fin 1)) = _
      rw [ih hG_meas]
      refine lintegral_congr fun y' => ?_
      dsimp only [G]
      rw [← lintegral_const_mul _ (by
        have hpdf : Measurable (fun z : ℝ =>
            gaussianPDF (-(2 * Real.sqrt 2 / 3) * y' 0) ⟨(-1 / 3) ^ 2, sq_nonneg _⟩ z) :=
          measurable_gaussianPDF _ _
        exact hpdf.mul (hf.comp (hmp_v.measurable.comp (measurable_const.prodMk measurable_id))))]
      refine lintegral_congr fun z => ?_
      rw [← mul_assoc]
      congr 1
      have h0 : ar2JointDensity 0 y' = gaussianPDFReal 0 1 (y' 0) := by
        simp [ar2JointDensity, gaussianPDFReal_def]
      change ENNReal.ofReal (ar2JointDensity 0 y') *
          ENNReal.ofReal (gaussianPDFReal (-(2 * Real.sqrt 2 / 3) * y' 0)
            ⟨(-1 / 3) ^ 2, sq_nonneg _⟩ z) = _
      rw [h0, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 _), gaussianPDF_init_mul]
      congr 1
      have hs0 : snoc y' z ⟨0, by omega⟩ = y' 0 := by
        change Fin.snoc (α := fun _ => ℝ) y' z (0 : Fin 1).castSucc = y' 0
        exact Fin.snoc_castSucc _ _ _
      have hs1 : snoc y' z ⟨1, by omega⟩ = z := by
        change Fin.snoc (α := fun _ => ℝ) y' z (Fin.last 1) = z
        exact Fin.snoc_last _ _
      change _ = (3 / (2 * Real.pi) * Real.exp (-(9 / 2) * (snoc y' z ⟨0, by omega⟩ ^ 2 +
        snoc y' z ⟨1, by omega⟩ ^ 2) - 6 * Real.sqrt 2 * snoc y' z ⟨0, by omega⟩ *
        snoc y' z ⟨1, by omega⟩)) * ∏ _i : Fin 0, _
      rw [hs0, hs1, Fin.prod_univ_zero, mul_one]
    | succ k =>
      have hsnoc_eq : ∀ (ξ' : Fin (k + 2) → ℝ) (u : ℝ),
          ar2AltMap (k + 2) (snoc ξ' u) =
            snoc (ar2AltMap (k + 1) ξ')
              (((-1 : ℝ) ^ (k + 2) / Real.sqrt 12) * u +
                (-Real.sqrt 2 * ar2AltMap (k + 1) ξ' ⟨k + 1, by omega⟩ -
                  ar2AltMap (k + 1) ξ' ⟨k, by omega⟩ / 2)) := by
        intro ξ' u
        ext i
        induction i using Fin.lastCases with
        | cast j' =>
          simp only [snoc, Fin.snoc_castSucc, ar2AltMap, Fin.val_castSucc,
            ar2StepMap_snoc_castSucc (k + 1) ξ' u j']
        | last =>
          simp only [snoc, Fin.snoc_last, ar2AltMap, Fin.val_last]
          have hrec := ar2StepMap_add_two (j := k + 2) (i := k) le_rfl (snoc ξ' u)
          have hk0 : (⟨k, by omega⟩ : Fin (k + 3)) =
              (⟨k, by omega⟩ : Fin (k + 2)).castSucc := rfl
          have hk1 : (⟨k + 1, by omega⟩ : Fin (k + 3)) =
              (⟨k + 1, by omega⟩ : Fin (k + 2)).castSucc := rfl
          have hkl : (⟨k + 2, by omega⟩ : Fin (k + 3)) = Fin.last (k + 2) := rfl
          change (-1 : ℝ) ^ (k + 2) * ar2StepMap (k + 2) (snoc ξ' u) (Fin.last (k + 2)) = _
          rw [← hkl, hrec, hk0, hk1]
          have hs0 : ar2StepMap (k + 2) (snoc ξ' u) (⟨k, by omega⟩ : Fin (k + 2)).castSucc =
              ar2StepMap (k + 1) ξ' ⟨k, by omega⟩ :=
            ar2StepMap_snoc_castSucc (k + 1) ξ' u ⟨k, by omega⟩
          have hs1 : ar2StepMap (k + 2) (snoc ξ' u) (⟨k + 1, by omega⟩ : Fin (k + 2)).castSucc =
              ar2StepMap (k + 1) ξ' ⟨k + 1, by omega⟩ :=
            ar2StepMap_snoc_castSucc (k + 1) ξ' u ⟨k + 1, by omega⟩
          have hsl : snoc ξ' u ⟨k + 2, by omega⟩ = u := by
            change Fin.snoc (α := fun _ => ℝ) ξ' u (Fin.last (k + 2)) = u
            exact Fin.snoc_last _ _
          rw [hs0, hs1, hsl]
          have hp1 : (-1 : ℝ) ^ (k + 2) = -(-1 : ℝ) ^ (k + 1) := by
            rw [pow_succ]; ring
          have hp2 : (-1 : ℝ) ^ (k + 2) = (-1 : ℝ) ^ k := by
            rw [pow_add]; norm_num
          calc (-1 : ℝ) ^ (k + 2) *
                (Real.sqrt 2 * ar2StepMap (k + 1) ξ' ⟨k + 1, by omega⟩ -
                  1 / 2 * ar2StepMap (k + 1) ξ' ⟨k, by omega⟩ +
                  1 / Real.sqrt 12 * u)
              = (-1 : ℝ) ^ (k + 2) / Real.sqrt 12 * u +
                  Real.sqrt 2 * ((-1 : ℝ) ^ (k + 2) *
                    ar2StepMap (k + 1) ξ' ⟨k + 1, by omega⟩) -
                  (1 / 2) * ((-1 : ℝ) ^ (k + 2) *
                    ar2StepMap (k + 1) ξ' ⟨k, by omega⟩) := by ring
            _ = (-1 : ℝ) ^ (k + 2) / Real.sqrt 12 * u +
                  (-Real.sqrt 2 * ((-1 : ℝ) ^ (k + 1) *
                    ar2StepMap (k + 1) ξ' ⟨k + 1, by omega⟩) -
                  ((-1 : ℝ) ^ k * ar2StepMap (k + 1) ξ' ⟨k, by omega⟩) / 2) := by
                  have ha : (-1 : ℝ) ^ (k + 2) * ar2StepMap (k + 1) ξ' ⟨k + 1, by omega⟩ =
                      -((-1 : ℝ) ^ (k + 1) * ar2StepMap (k + 1) ξ' ⟨k + 1, by omega⟩) := by
                    rw [hp1]; ring
                  have hb : (-1 : ℝ) ^ (k + 2) * ar2StepMap (k + 1) ξ' ⟨k, by omega⟩ =
                      (-1 : ℝ) ^ k * ar2StepMap (k + 1) ξ' ⟨k, by omega⟩ := by rw [hp2]
                  rw [ha, hb]; ring
      have ha_ne : (-1 : ℝ) ^ (k + 2) / Real.sqrt 12 ≠ 0 :=
        div_ne_zero (pow_ne_zero _ (by norm_num)) (Real.sqrt_pos.mpr (by norm_num)).ne'
      have hstep : ∀ ξ' : Fin (k + 2) → ℝ,
          ∫⁻ u : ℝ, f (ar2AltMap (k + 2) (snoc ξ' u)) ∂(gaussianReal 0 1) =
            ∫⁻ z : ℝ, gaussianPDF
              (-Real.sqrt 2 * ar2AltMap (k + 1) ξ' ⟨k + 1, by omega⟩ -
                ar2AltMap (k + 1) ξ' ⟨k, by omega⟩ / 2)
              ⟨((-1 : ℝ) ^ (k + 2) / Real.sqrt 12) ^ 2, sq_nonneg _⟩ z *
              f (snoc (ar2AltMap (k + 1) ξ') z) ∂volume := by
        intro ξ'
        simp_rw [hsnoc_eq ξ']
        have hsnoc_m : Measurable (fun z : ℝ => snoc (ar2AltMap (k + 1) ξ') z) := by
          have heq : (fun z : ℝ => snoc (ar2AltMap (k + 1) ξ') z) =
              (fun p : (Fin (k + 2) → ℝ) × ℝ => Fin.snoc p.1 p.2) ∘
                fun z => (ar2AltMap (k + 1) ξ', z) := rfl
          rw [heq]
          exact hmp_v.measurable.comp (measurable_const.prodMk measurable_id)
        exact lintegral_gaussianReal_affine ha_ne _ (hf.comp hsnoc_m)
      simp_rw [hstep]
      let G : (Fin (k + 2) → ℝ) → ℝ≥0∞ := fun y' =>
        ∫⁻ z : ℝ, gaussianPDF
          (-Real.sqrt 2 * y' ⟨k + 1, by omega⟩ - y' ⟨k, by omega⟩ / 2)
          ⟨((-1 : ℝ) ^ (k + 2) / Real.sqrt 12) ^ 2, sq_nonneg _⟩ z *
          f (snoc y' z) ∂volume
      have hG_meas : Measurable G := by
        refine Measurable.lintegral_prod_right' (f := fun p : (Fin (k + 2) → ℝ) × ℝ =>
          gaussianPDF (-Real.sqrt 2 * p.1 ⟨k + 1, by omega⟩ - p.1 ⟨k, by omega⟩ / 2)
            ⟨((-1 : ℝ) ^ (k + 2) / Real.sqrt 12) ^ 2, sq_nonneg _⟩ p.2 *
            f (snoc p.1 p.2)) ?_
        have hpdf : Measurable (fun p : (Fin (k + 2) → ℝ) × ℝ =>
            gaussianPDF (-Real.sqrt 2 * p.1 ⟨k + 1, by omega⟩ - p.1 ⟨k, by omega⟩ / 2)
              ⟨((-1 : ℝ) ^ (k + 2) / Real.sqrt 12) ^ 2, sq_nonneg _⟩ p.2) := by
          change Measurable (fun p : (Fin (k + 2) → ℝ) × ℝ =>
            ENNReal.ofReal (gaussianPDFReal
              (-Real.sqrt 2 * p.1 ⟨k + 1, by omega⟩ - p.1 ⟨k, by omega⟩ / 2)
              ⟨((-1 : ℝ) ^ (k + 2) / Real.sqrt 12) ^ 2, sq_nonneg _⟩ p.2))
          refine (Continuous.measurable ?_).ennreal_ofReal
          unfold gaussianPDFReal
          fun_prop
        exact hpdf.mul (hf.comp hmp_v.measurable)
      change ∫⁻ ξ', G (ar2AltMap (k + 1) ξ') ∂(piGauss (Fin (k + 2))) = _
      rw [ih hG_meas]
      refine lintegral_congr fun y' => ?_
      dsimp only [G]
      rw [← lintegral_const_mul _ (by
        have hpdf : Measurable (fun z : ℝ =>
            gaussianPDF (-Real.sqrt 2 * y' ⟨k + 1, by omega⟩ - y' ⟨k, by omega⟩ / 2)
              ⟨((-1 : ℝ) ^ (k + 2) / Real.sqrt 12) ^ 2, sq_nonneg _⟩ z) :=
          measurable_gaussianPDF _ _
        exact hpdf.mul (hf.comp (hmp_v.measurable.comp (measurable_const.prodMk measurable_id))))]
      refine lintegral_congr fun z => ?_
      rw [← mul_assoc]
      congr 1
      change ENNReal.ofReal (ar2JointDensity (k + 1) y') *
          ENNReal.ofReal (gaussianPDFReal
            (-Real.sqrt 2 * y' ⟨k + 1, by omega⟩ - y' ⟨k, by omega⟩ / 2)
            ⟨((-1 : ℝ) ^ (k + 2) / Real.sqrt 12) ^ 2, sq_nonneg _⟩ z) = _
      rw [← ENNReal.ofReal_mul (ar2JointDensity_nonneg (k + 1) y'),
        gaussianPDF_kernel_eq k]
      congr 1
      simp only [ar2JointDensity, ar2InitDensity, ar2Kernel]
      rw [Fin.prod_univ_castSucc, ← mul_assoc]
      have h0 : snoc y' z ⟨0, by omega⟩ = y' ⟨0, by omega⟩ := by
        change Fin.snoc (α := fun _ => ℝ) y' z (⟨0, by omega⟩ : Fin (k + 2)).castSucc = _
        exact Fin.snoc_castSucc _ _ _
      have h1 : snoc y' z ⟨1, by omega⟩ = y' ⟨1, by omega⟩ := by
        change Fin.snoc (α := fun _ => ℝ) y' z (⟨1, by omega⟩ : Fin (k + 2)).castSucc = _
        exact Fin.snoc_castSucc _ _ _
      have hprod : ∏ i : Fin k, (Real.sqrt (6 / Real.pi) *
            Real.exp (-6 * (snoc y' z ⟨i.castSucc.val + 2, by omega⟩ +
              Real.sqrt 2 * snoc y' z ⟨i.castSucc.val + 1, by omega⟩ +
              snoc y' z ⟨i.castSucc.val, by omega⟩ / 2) ^ 2)) =
          ∏ i : Fin k, (Real.sqrt (6 / Real.pi) *
            Real.exp (-6 * (y' ⟨i.val + 2, by omega⟩ +
              Real.sqrt 2 * y' ⟨i.val + 1, by omega⟩ +
              y' ⟨i.val, by omega⟩ / 2) ^ 2)) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        have ha' : snoc y' z ⟨i.val + 2, by omega⟩ = y' ⟨i.val + 2, by omega⟩ := by
          change Fin.snoc (α := fun _ => ℝ) y' z (⟨i.val + 2, by omega⟩ : Fin (k + 2)).castSucc = _
          exact Fin.snoc_castSucc _ _ _
        have hb' : snoc y' z ⟨i.val + 1, by omega⟩ = y' ⟨i.val + 1, by omega⟩ := by
          change Fin.snoc (α := fun _ => ℝ) y' z (⟨i.val + 1, by omega⟩ : Fin (k + 2)).castSucc = _
          exact Fin.snoc_castSucc _ _ _
        have hc' : snoc y' z ⟨i.val, by omega⟩ = y' ⟨i.val, by omega⟩ := by
          change Fin.snoc (α := fun _ => ℝ) y' z (⟨i.val, by omega⟩ : Fin (k + 2)).castSucc = _
          exact Fin.snoc_castSucc _ _ _
        simp only [Fin.val_castSucc, ha', hb', hc']
      have hlast0 : snoc y' z ⟨(Fin.last k).val, by omega⟩ = y' ⟨k, by omega⟩ := by
        change Fin.snoc (α := fun _ => ℝ) y' z (⟨k, by omega⟩ : Fin (k + 2)).castSucc = _
        exact Fin.snoc_castSucc _ _ _
      have hlast1 : snoc y' z ⟨(Fin.last k).val + 1, by omega⟩ = y' ⟨k + 1, by omega⟩ := by
        change Fin.snoc (α := fun _ => ℝ) y' z (⟨k + 1, by omega⟩ : Fin (k + 2)).castSucc = _
        exact Fin.snoc_castSucc _ _ _
      have hlast2 : snoc y' z ⟨(Fin.last k).val + 2, by omega⟩ = z := by
        change Fin.snoc (α := fun _ => ℝ) y' z (Fin.last (k + 2)) = z
        exact Fin.snoc_last _ _
      rw [h0, h1, hprod, hlast0, hlast1, hlast2]
      ring

/-- The alternating-sign orthant probability `ar2AltProb j` of the Gaussian AR(2) process is
`altPathProb j`, twice the positive-orthant Lebesgue integral of `ar2JointDensity j`. -/
theorem ar2AltProb_eq_altPathProb (j : ℕ) : ar2AltProb j = altPathProb j := by
  let S : Set (Fin (j + 1) → ℝ) := Set.pi Set.univ (fun _ : Fin (j + 1) => Set.Ioi (0 : ℝ))
  have hS_meas : MeasurableSet S := MeasurableSet.univ_pi fun _ => measurableSet_Ioi
  let ind : (Fin (j + 1) → ℝ) → ℝ≥0∞ := S.indicator fun _ => 1
  have hind_meas : Measurable ind := measurable_const.indicator hS_meas
  have hpre : (piGauss (Fin (j + 1))) {ξ | ∀ i : Fin (j + 1),
      0 < (-1 : ℝ) ^ i.val * ar2StepMap j ξ i} =
      ∫⁻ ξ, ind (ar2AltMap j ξ) ∂(piGauss (Fin (j + 1))) := by
    have hset : {ξ | ∀ i : Fin (j + 1), 0 < (-1 : ℝ) ^ i.val * ar2StepMap j ξ i} =
        ar2AltMap j ⁻¹' S := by
      ext ξ; simp [S, ar2AltMap, Set.mem_pi, Set.mem_Ioi]
    rw [hset, ← lintegral_indicator_one (hS_meas.preimage (measurable_ar2AltMap j))]
    refine lintegral_congr fun ξ => ?_
    change (ar2AltMap j ⁻¹' S).indicator (fun _ => (1 : ℝ≥0∞)) ξ =
      S.indicator (fun _ => (1 : ℝ≥0∞)) (ar2AltMap j ξ)
    by_cases h : ar2AltMap j ξ ∈ S <;> simp [h]
  have hlin : ∫⁻ y, ENNReal.ofReal (ar2JointDensity j y) * ind y
      ∂(Measure.pi fun _ : Fin (j + 1) => volume) =
      ∫⁻ y in S, ENNReal.ofReal (ar2JointDensity j y)
        ∂(Measure.pi fun _ : Fin (j + 1) => volume) := by
    rw [← lintegral_indicator hS_meas]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ S <;> simp [ind, hy]
  have heq_enn : (piGauss (Fin (j + 1)))
      {ξ | ∀ i : Fin (j + 1), 0 < (-1 : ℝ) ^ i.val * ar2StepMap j ξ i} =
      ∫⁻ y in S, ENNReal.ofReal (ar2JointDensity j y)
        ∂(Measure.pi fun _ : Fin (j + 1) => volume) := by
    rw [hpre, lintegral_ar2AltMap j hind_meas, hlin]
  unfold ar2AltProb altPathProb ar2OrthantIntegral
  congr 1
  rw [measureReal_def, heq_enn,
    ← integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun y => ar2JointDensity_nonneg j y)
      (ar2JointDensity_continuous j).measurable.aestronglyMeasurable]

end AR2Process

/-! ### High-girth convergence theorems (degree-3 star and non-backtracking walks) -/

section HighGirthConvergence

/-- Two linear projections of independent standard Gaussian vectors with identical Gram matrix
have the exact same joint law. -/
private theorem map_piGauss_eq_of_gram_eq {ι κ₁ κ₂ : Type*}
    [Finite ι] [Fintype κ₁] [Fintype κ₂]
    (a : ι → κ₁ → ℝ) (b : ι → κ₂ → ℝ)
    (hgram : ∀ i l : ι, ∑ k : κ₁, a i k * a l k = ∑ k : κ₂, b i k * b l k) :
    (piGauss κ₁).map (fun x i => ∑ k : κ₁, a i k * x k) =
      (piGauss κ₂).map (fun y i => ∑ k : κ₂, b i k * y k) := by
  have := Fintype.ofFinite ι
  let A : (κ₁ → ℝ) → EuclideanSpace ℝ ι := fun x =>
    WithLp.toLp 2 (fun i => ∑ k : κ₁, a i k * x k)
  let B : (κ₂ → ℝ) → EuclideanSpace ℝ ι := fun y =>
    WithLp.toLp 2 (fun i => ∑ k : κ₂, b i k * y k)
  have hA_meas : Measurable A := by fun_prop
  have hB_meas : Measurable B := by fun_prop
  have hvar : ∀ t : EuclideanSpace ℝ ι,
      ‖WithLp.toLp 2 (fun k : κ₁ => ∑ i : ι, a i k * t i)‖₊ ^ 2 =
        ‖WithLp.toLp 2 (fun k : κ₂ => ∑ i : ι, b i k * t i)‖₊ ^ 2 := by
    intro t
    ext
    simp only [NNReal.coe_pow, coe_nnNorm, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    calc ∑ k : κ₁, (∑ i : ι, a i k * t i) ^ 2
        = ∑ k : κ₁, ∑ i : ι, ∑ l : ι, (t i * t l) * (a i k * a l k) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [sq, Finset.sum_mul_sum]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ i : ι, ∑ l : ι, (t i * t l) * ∑ k : κ₁, a i k * a l k := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun l _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ i : ι, ∑ l : ι, (t i * t l) * ∑ k : κ₂, b i k * b l k := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by
              rw [hgram i l]
      _ = ∑ k : κ₂, ∑ i : ι, ∑ l : ι, (t i * t l) * (b i k * b l k) := by
            symm
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun l _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ k : κ₂, (∑ i : ι, b i k * t i) ^ 2 := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [sq, Finset.sum_mul_sum]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  have hchar : (piGauss κ₁).map A = (piGauss κ₂).map B := by
    refine Measure.ext_of_charFun (funext fun t => ?_)
    rw [charFun_map_eq_charFun_map_inner_one hA_meas.aemeasurable,
      charFun_map_eq_charFun_map_inner_one hB_meas.aemeasurable]
    have hinnerA : (fun x : κ₁ → ℝ => inner ℝ (A x) t) =
        fun x => (fun k => ∑ i : ι, a i k * t i) ⬝ᵥ x := by
      ext x
      rw [EuclideanSpace.inner_toLp_toLp]
      simp only [star_trivial, dotProduct, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    have hinnerB : (fun y : κ₂ → ℝ => inner ℝ (B y) t) =
        fun y => (fun k => ∑ i : ι, b i k * t i) ⬝ᵥ y := by
      ext y
      rw [EuclideanSpace.inner_toLp_toLp]
      simp only [star_trivial, dotProduct, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    rw [hinnerA, hinnerB, pi_gaussianReal_map_dotProduct, pi_gaussianReal_map_dotProduct, hvar t]
  have hA_comp : (fun x : κ₁ → ℝ => fun i : ι => ∑ k : κ₁, a i k * x k) =
      WithLp.ofLp ∘ A := rfl
  have hB_comp : (fun y : κ₂ → ℝ => fun i : ι => ∑ k : κ₂, b i k * y k) =
      WithLp.ofLp ∘ B := rfl
  rw [hA_comp, hB_comp, ← Measure.map_map (by fun_prop) hA_meas,
    ← Measure.map_map (by fun_prop) hB_meas, hchar]

/-- **Degree-3 crossing-star bound:** for every `η > 0`, there exist `R₀ : ℕ` and `ε₀ > 0` such
that for all `R ≥ R₀` and `0 < ε ≤ ε₀`, on *every* finite cubic simple graph `H'` with no closed
non-backtracking walk of length `1 ≤ k ≤ 2 * R + 6`, every vertex has degree `3` in the crossing
graph with probability at most `η`. -/
theorem exists_degThree_star_bound (η : ℝ) (hη : 0 < η) :
    ∃ (R₀ : ℕ) (ε₀ : ℝ), 0 < ε₀ ∧
      ∀ {V' : Type*} [Fintype V'] (H' : SimpleGraph V'),
        (∀ v : V', open Classical in H'.degree v = 3) →
        ∀ (R : ℕ), R₀ ≤ R → ∀ (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        (∀ (k : ℕ), 1 ≤ k → k ≤ 2 * R + 6 →
          ∀ w' : Fin (k + 1) → V', IsNBWalk H' k w' → w' 0 ≠ w' (Fin.last k)) →
        ∀ v' : V',
          (piGauss (V' ⊕ V')).real
            {g | open Classical in
              (crossingGraph H' (thresholdVec (waveScore H' R ε g) 0)).degree v' = 3} ≤ η := by
  let δ : ℝ := η * Real.sqrt (2 * Real.pi) / 4
  have hδ_pos : 0 < δ := by positivity
  let target : ℝ := 4 * η * δ ^ 2
  have htarget_pos : 0 < target := by positivity
  let err1 : ℝ := target / 3
  have herr1_pos : 0 < err1 := by positivity
  have ht1 := tendsto_treeOverlap 1
  have ht2 := tendsto_treeOverlap 2
  rw [Metric.tendsto_atTop] at ht1 ht2
  obtain ⟨R₁, hR₁⟩ := ht1 (err1 / (12 * Real.sqrt 2)) (by positivity)
  obtain ⟨R₂, hR₂⟩ := ht2 (err1 / 6) (by positivity)
  let R₀ : ℕ := max 2 (max R₁ R₂)
  let cε : ℝ := 6 * treeCovLimit 2 + 12 * Real.sqrt 2 * treeCovLimit 1
  have hcε_pos : 0 < cε := by
    dsimp only [cε]; rw [treeCovLimit_one, treeCovLimit_two]; positivity
  let ε₀ : ℝ := min (1 / 2) (Real.sqrt (err1 / cε))
  have hε₀_pos : 0 < ε₀ := lt_min (by norm_num) (Real.sqrt_pos.mpr (div_pos herr1_pos hcε_pos))
  refine ⟨R₀, ε₀, hε₀_pos, fun {V'} _ H' hreg R hR ε hε0 hε1 hgirth v' => ?_⟩
  classical
  have hε_le_half : ε ≤ 1 / 2 := hε1.trans (min_le_left _ _)
  have hε_le1 : ε ≤ 1 := by linarith
  have h1e_nn : 0 ≤ 1 - ε ^ 2 := by nlinarith
  have h1e_le : 1 - ε ^ 2 ≤ 1 := by nlinarith
  have hR_ge2 : 2 ≤ R := (le_max_left 2 _).trans hR
  have hR_ge1 : R₁ ≤ R := (le_max_left R₁ R₂).trans ((le_max_right 2 _).trans hR)
  have hR_ge2' : R₂ ≤ R := (le_max_right R₁ R₂).trans ((le_max_right 2 _).trans hR)
  have hcard3 : (H'.neighborFinset v').card = 3 := hreg v'
  obtain ⟨u₁, u₂, u₃, h12, h13, h23, hnb_eq⟩ := Finset.card_eq_three.mp hcard3
  have hadj1 : H'.Adj v' u₁ := (H'.mem_neighborFinset v' u₁).mp (by rw [hnb_eq]; simp)
  have hadj2 : H'.Adj v' u₂ := (H'.mem_neighborFinset v' u₂).mp (by rw [hnb_eq]; simp)
  have hadj3 : H'.Adj v' u₃ := (H'.mem_neighborFinset v' u₃).mp (by rw [hnb_eq]; simp)
  have hinner_edge : ∀ u : V', H'.Adj v' u →
      ∑ z' : V' ⊕ V', waveRow H' R ε v' z' * waveRow H' R ε u z' =
        (1 - ε ^ 2) * treeOverlap R 1 := by
    intro u hadj
    let w : Fin 2 → V' := fun i => if i = 0 then v' else u
    have hw : IsNBWalk H' 1 w := ⟨fun i => by fin_cases i; exact hadj, fun _ hi => by omega⟩
    have h := waveRow_inner_eq_treeOverlap H' hreg (by omega : 1 ≤ R) hε0.le hε_le1
      (fun k h1 h2 => hgirth k h1 (by omega)) hw 0 1
    simpa [w] using h
  have hinner_two : ∀ x y : V', H'.Adj v' x → H'.Adj v' y → x ≠ y →
      ∑ z' : V' ⊕ V', waveRow H' R ε x z' * waveRow H' R ε y z' =
        (1 - ε ^ 2) * treeOverlap R 2 := by
    intro x y hx hy hxy
    let w : Fin 3 → V' := fun i => if i.val = 0 then x else if i.val = 1 then v' else y
    have hw : IsNBWalk H' 2 w := by
      refine ⟨fun i => ?_, fun i hi => ?_⟩
      · fin_cases i
        · exact hx.symm
        · exact hy
      · have : i = 0 := by omega
        subst this; exact hxy
    have h := waveRow_inner_eq_treeOverlap H' hreg hR_ge2 hε0.le hε_le1
      (fun k h1 h2 => hgirth k h1 (by omega)) hw 0 ⟨2, by omega⟩
    simpa [w] using h
  let a : V' ⊕ V' → ℝ := fun z' =>
    waveRow H' R ε u₁ z' + waveRow H' R ε u₂ z' + waveRow H' R ε u₃ z' -
      2 * Real.sqrt 2 * waveRow H' R ε v' z'
  have hnorm_sq : ∑ z' : V' ⊕ V', a z' ^ 2 =
      11 + 6 * (1 - ε ^ 2) * treeOverlap R 2 -
        12 * Real.sqrt 2 * (1 - ε ^ 2) * treeOverlap R 1 := by
    have hsq_exp : ∀ z' : V' ⊕ V', a z' ^ 2 =
        waveRow H' R ε u₁ z' ^ 2 + waveRow H' R ε u₂ z' ^ 2 + waveRow H' R ε u₃ z' ^ 2 +
        2 * (waveRow H' R ε u₁ z' * waveRow H' R ε u₂ z') +
        2 * (waveRow H' R ε u₁ z' * waveRow H' R ε u₃ z') +
        2 * (waveRow H' R ε u₂ z' * waveRow H' R ε u₃ z') +
        8 * waveRow H' R ε v' z' ^ 2 -
        4 * Real.sqrt 2 * (waveRow H' R ε v' z' * waveRow H' R ε u₁ z') -
        4 * Real.sqrt 2 * (waveRow H' R ε v' z' * waveRow H' R ε u₂ z') -
        4 * Real.sqrt 2 * (waveRow H' R ε v' z' * waveRow H' R ε u₃ z') := by
      intro z'
      dsimp only [a]
      have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      linear_combination 4 * waveRow H' R ε v' z' ^ 2 * hsq2
    simp_rw [hsq_exp]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [sum_sq_waveRow_eq_one H' hreg R hε0.le hε_le1 u₁,
      sum_sq_waveRow_eq_one H' hreg R hε0.le hε_le1 u₂,
      sum_sq_waveRow_eq_one H' hreg R hε0.le hε_le1 u₃,
      sum_sq_waveRow_eq_one H' hreg R hε0.le hε_le1 v',
      hinner_two u₁ u₂ hadj1 hadj2 h12, hinner_two u₁ u₃ hadj1 hadj3 h13,
      hinner_two u₂ u₃ hadj2 hadj3 h23,
      hinner_edge u₁ hadj1, hinner_edge u₂ hadj2, hinner_edge u₃ hadj3]
    ring
  have hε_sq_le : ε ^ 2 * cε ≤ err1 := by
    have hε_bound : ε ≤ Real.sqrt (err1 / cε) := hε1.trans (min_le_right _ _)
    have hsq : ε ^ 2 ≤ err1 / cε := by
      calc ε ^ 2 ≤ Real.sqrt (err1 / cε) ^ 2 :=
            sq_le_sq' (by linarith [Real.sqrt_nonneg (err1 / cε)]) hε_bound
        _ = err1 / cε := Real.sq_sqrt (by positivity)
    exact (le_div_iff₀ hcε_pos).mp hsq
  have hvar_le : ∑ z' : V' ⊕ V', a z' ^ 2 ≤ target := by
    have hd1 : |treeOverlap R 1 - treeCovLimit 1| < err1 / (12 * Real.sqrt 2) := by
      simpa [Real.dist_eq] using hR₁ R hR_ge1
    have hd2 : |treeOverlap R 2 - treeCovLimit 2| < err1 / 6 := by
      simpa [Real.dist_eq] using hR₂ R hR_ge2'
    have hbase : (11 : ℝ) + 6 * treeCovLimit 2 - 12 * Real.sqrt 2 * treeCovLimit 1 = 0 := by
      rw [treeCovLimit_one, treeCovLimit_two]
      have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      linear_combination -8 * hsq2
    have hdiff1 : 12 * Real.sqrt 2 * (1 - ε ^ 2) * (treeCovLimit 1 - treeOverlap R 1) ≤ err1 := by
      have hab : treeCovLimit 1 - treeOverlap R 1 ≤ err1 / (12 * Real.sqrt 2) := by
        linarith [neg_abs_le (treeOverlap R 1 - treeCovLimit 1),
          abs_le.mp hd1.le]
      calc 12 * Real.sqrt 2 * (1 - ε ^ 2) * (treeCovLimit 1 - treeOverlap R 1)
          ≤ 12 * Real.sqrt 2 * (1 - ε ^ 2) * (err1 / (12 * Real.sqrt 2)) :=
            mul_le_mul_of_nonneg_left hab (by positivity)
        _ = (1 - ε ^ 2) * err1 := by
            have hne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
            field_simp [hne]
        _ ≤ 1 * err1 := mul_le_mul_of_nonneg_right h1e_le herr1_pos.le
        _ = err1 := one_mul _
    have hdiff2 : 6 * (1 - ε ^ 2) * (treeOverlap R 2 - treeCovLimit 2) ≤ err1 := by
      have hab : treeOverlap R 2 - treeCovLimit 2 ≤ err1 / 6 := (le_abs_self _).trans hd2.le
      calc 6 * (1 - ε ^ 2) * (treeOverlap R 2 - treeCovLimit 2)
          ≤ 6 * (1 - ε ^ 2) * (err1 / 6) :=
            mul_le_mul_of_nonneg_left hab (by positivity)
        _ = (1 - ε ^ 2) * err1 := by ring
        _ ≤ 1 * err1 := mul_le_mul_of_nonneg_right h1e_le herr1_pos.le
        _ = err1 := one_mul _
    have hdiff3 : ε ^ 2 * (12 * Real.sqrt 2 * treeCovLimit 1 - 6 * treeCovLimit 2) ≤ err1 := by
      have hle : 12 * Real.sqrt 2 * treeCovLimit 1 - 6 * treeCovLimit 2 ≤ cε := by
        dsimp only [cε]; rw [treeCovLimit_two]; linarith
      exact (mul_le_mul_of_nonneg_left hle (sq_nonneg ε)).trans hε_sq_le
    rw [hnorm_sq]
    have hsplit : 11 + 6 * (1 - ε ^ 2) * treeOverlap R 2 -
          12 * Real.sqrt 2 * (1 - ε ^ 2) * treeOverlap R 1 =
        (11 + 6 * treeCovLimit 2 - 12 * Real.sqrt 2 * treeCovLimit 1) +
        6 * (1 - ε ^ 2) * (treeOverlap R 2 - treeCovLimit 2) +
        12 * Real.sqrt 2 * (1 - ε ^ 2) * (treeCovLimit 1 - treeOverlap R 1) +
        ε ^ 2 * (12 * Real.sqrt 2 * treeCovLimit 1 - 6 * treeCovLimit 2) := by ring
    rw [hsplit, hbase, zero_add]
    dsimp only [err1] at hdiff1 hdiff2 hdiff3 ⊢
    linarith
  let E := {g : V' ⊕ V' → ℝ |
    (crossingGraph H' (thresholdVec (waveScore H' R ε g) 0)).degree v' = 3}
  let A := {g : V' ⊕ V' → ℝ | waveScore H' R ε g v' ∈ Set.Icc (-δ) δ}
  let B := {g : V' ⊕ V' → ℝ | 2 * Real.sqrt 2 * δ ≤ |a ⬝ᵥ g|}
  have hsub : E ⊆ A ∪ B := by
    intro g hg
    by_cases hwin : |waveScore H' R ε g v'| ≤ δ
    · exact Or.inl (abs_le.mp hwin)
    · right
      have hgt : δ < |waveScore H' R ε g v'| := lt_of_not_ge hwin
      have hcg_sub : (crossingGraph H' (thresholdVec (waveScore H' R ε g) 0)).neighborFinset v' ⊆
          H'.neighborFinset v' := fun u hu => by
        rw [SimpleGraph.mem_neighborFinset] at hu ⊢; exact hu.1
      have hcg_eq : (crossingGraph H' (thresholdVec (waveScore H' R ε g) 0)).neighborFinset v' =
          H'.neighborFinset v' :=
        Finset.eq_of_subset_of_card_le hcg_sub (by
          have hcard := (SimpleGraph.degree (crossingGraph H'
            (thresholdVec (waveScore H' R ε g) 0)) v' : ℕ)
          have hdeg : (crossingGraph H' (thresholdVec (waveScore H' R ε g) 0)).degree v' = 3 := hg
          rw [SimpleGraph.degree] at hdeg; omega)
      have hflip : ∀ u ∈ ({u₁, u₂, u₃} : Finset V'),
          thresholdVec (waveScore H' R ε g) 0 v' ≠ thresholdVec (waveScore H' R ε g) 0 u := by
        intro u hu
        have hu' : u ∈ (crossingGraph H'
            (thresholdVec (waveScore H' R ε g) 0)).neighborFinset v' := by
          rw [hcg_eq, hnb_eq]; exact hu
        exact ((SimpleGraph.mem_neighborFinset _ _ _).mp hu').2
      have hdot : a ⬝ᵥ g = waveScore H' R ε g u₁ + waveScore H' R ε g u₂ +
          waveScore H' R ε g u₃ - 2 * Real.sqrt 2 * waveScore H' R ε g v' := by
        simp only [dotProduct, a, waveScore, sub_mul, add_mul, mul_assoc,
          Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      change 2 * Real.sqrt 2 * δ ≤ |a ⬝ᵥ g|
      rw [hdot]
      by_cases hv : waveScore H' R ε g v' < 0
      · have h0 : thresholdVec (waveScore H' R ε g) 0 v' = true :=
          (thresholdVec_apply_eq_true _ 0 v').mpr hv
        have hnn : ∀ u ∈ ({u₁, u₂, u₃} : Finset V'), 0 ≤ waveScore H' R ε g u := by
          intro u hu
          have hne := hflip u hu
          rw [h0] at hne
          cases ht : thresholdVec (waveScore H' R ε g) 0 u
          · exact (thresholdVec_apply_eq_false _ 0 u).mp ht
          · exact (hne ht.symm).elim
        have h1 := hnn u₁ (by simp)
        have h2 := hnn u₂ (by simp)
        have h3 := hnn u₃ (by simp)
        have hval : -waveScore H' R ε g v' > δ := by
          rwa [abs_of_neg hv] at hgt
        have hlo : 2 * Real.sqrt 2 * δ ≤ waveScore H' R ε g u₁ + waveScore H' R ε g u₂ +
            waveScore H' R ε g u₃ - 2 * Real.sqrt 2 * waveScore H' R ε g v' := by
          have : 2 * Real.sqrt 2 * δ ≤ -(2 * Real.sqrt 2 * waveScore H' R ε g v') := by
            have hpos2 : 0 ≤ 2 * Real.sqrt 2 := by positivity
            nlinarith
          linarith
        exact hlo.trans (le_abs_self _)
      · have hvge : 0 ≤ waveScore H' R ε g v' := not_lt.mp hv
        have h0 : thresholdVec (waveScore H' R ε g) 0 v' = false :=
          (thresholdVec_apply_eq_false _ 0 v').mpr hvge
        have hlt_u : ∀ u ∈ ({u₁, u₂, u₃} : Finset V'), waveScore H' R ε g u < 0 := by
          intro u hu
          have hne := hflip u hu
          rw [h0] at hne
          cases ht : thresholdVec (waveScore H' R ε g) 0 u
          · exact (hne ht.symm).elim
          · exact (thresholdVec_apply_eq_true _ 0 u).mp ht
        have h1 := hlt_u u₁ (by simp)
        have h2 := hlt_u u₂ (by simp)
        have h3 := hlt_u u₃ (by simp)
        have hval : waveScore H' R ε g v' > δ := by rwa [abs_of_nonneg hvge] at hgt
        have hhi : waveScore H' R ε g u₁ + waveScore H' R ε g u₂ +
            waveScore H' R ε g u₃ - 2 * Real.sqrt 2 * waveScore H' R ε g v' ≤
            -(2 * Real.sqrt 2 * δ) := by
          have hpos2 : 0 ≤ 2 * Real.sqrt 2 := by positivity
          nlinarith
        exact (by linarith : 2 * Real.sqrt 2 * δ ≤ -(waveScore H' R ε g u₁ +
          waveScore H' R ε g u₂ + waveScore H' R ε g u₃ -
          2 * Real.sqrt 2 * waveScore H' R ε g v')).trans (neg_le_abs _)
  have hA_le : (piGauss (V' ⊕ V')).real A ≤ η / 2 := by
    have hnorm : ‖WithLp.toLp 2 (waveRow H' R ε v')‖₊ ^ 2 = 1 := by
      ext
      simp only [NNReal.coe_pow, coe_nnNorm, NNReal.coe_one, EuclideanSpace.norm_sq_eq,
        Real.norm_eq_abs, sq_abs]
      exact sum_sq_waveRow_eq_one H' hreg R hε0.le hε_le1 v'
    have hmap : (piGauss (V' ⊕ V')).map (waveRow H' R ε v' ⬝ᵥ ·) = gaussianReal 0 1 := by
      rw [pi_gaussianReal_map_dotProduct, hnorm]
    have hA_eq : A = (waveRow H' R ε v' ⬝ᵥ ·) ⁻¹' Set.Icc (-δ) δ := by
      ext g; simp [A, waveScore, dotProduct]
    rw [measureReal_def, hA_eq, ← Measure.map_apply (by fun_prop) measurableSet_Icc, hmap]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    calc gaussianReal 0 1 (Set.Icc (-δ) δ)
        ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi * (1 : ℝ≥0)))⁻¹ * volume (Set.Icc (-δ) δ) :=
          gaussianReal_le_ofReal_mul_volume 0 one_ne_zero _
      _ = ENNReal.ofReal (Real.sqrt (2 * Real.pi))⁻¹ * ENNReal.ofReal (2 * δ) := by
          rw [Real.volume_Icc, show δ - -δ = 2 * δ by ring, NNReal.coe_one, mul_one]
      _ = ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * (2 * δ)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (η / 2) := by
          congr 1
          have hne : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
          dsimp only [δ]; field_simp [hne]; ring
  have hB_le : (piGauss (V' ⊕ V')).real B ≤ η / 2 := by
    have hB_eq : B = (a ⬝ᵥ ·) ⁻¹' {x : ℝ | 2 * Real.sqrt 2 * δ ≤ |x - 0|} := by
      ext g; simp [B]
    have hc_pos : 0 < 2 * Real.sqrt 2 * δ := by positivity
    rw [measureReal_def, hB_eq,
      ← Measure.map_apply (by fun_prop) (measurableSet_le measurable_const (by fun_prop)),
      pi_gaussianReal_map_dotProduct]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    refine (gaussianReal_meas_ge_le 0 (‖WithLp.toLp 2 a‖₊ ^ 2) hc_pos).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hcoe : ((‖WithLp.toLp 2 a‖₊ ^ 2 : ℝ≥0) : ℝ) = ∑ z' : V' ⊕ V', a z' ^ 2 := by
      simp only [NNReal.coe_pow, coe_nnNorm, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    rw [hcoe]
    have hden : (2 * Real.sqrt 2 * δ) ^ 2 = 8 * δ ^ 2 := by
      have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      linear_combination 4 * δ ^ 2 * hsq2
    rw [hden, div_le_iff₀ (by positivity)]
    have : η / 2 * (8 * δ ^ 2) = target := by dsimp only [target]; ring
    linarith [hvar_le]
  calc (piGauss (V' ⊕ V')).real E
      ≤ (piGauss (V' ⊕ V')).real (A ∪ B) := measureReal_mono hsub
    _ ≤ (piGauss (V' ⊕ V')).real A + (piGauss (V' ⊕ V')).real B := measureReal_union_le A B
    _ ≤ η / 2 + η / 2 := add_le_add hA_le hB_le
    _ = η := by ring

/-- Recursive lower-triangular Cholesky factor `L` of an infinite array `M : ℕ → ℕ → ℝ`. -/
private noncomputable def chol (M : ℕ → ℕ → ℝ) (i k : ℕ) : ℝ :=
  if hlt : k < i then
    (M i k - ∑ l : Fin k, chol M i l.val * chol M k l.val) / chol M k k
  else if k = i then
    Real.sqrt (M i i - ∑ l : Fin i, chol M i l.val ^ 2)
  else 0
termination_by (i, k)
decreasing_by
  all_goals first
    | exact Prod.Lex.right _ (by omega)
    | exact Prod.Lex.left _ _ (by omega)

private theorem chol_of_lt (M : ℕ → ℕ → ℝ) {i k : ℕ} (hlt : k < i) :
    chol M i k = (M i k - ∑ l : Fin k, chol M i l.val * chol M k l.val) / chol M k k := by
  rw [chol]; simp only [hlt, ↓reduceDIte]

private theorem chol_diag (M : ℕ → ℕ → ℝ) (i : ℕ) :
    chol M i i = Real.sqrt (M i i - ∑ l : Fin i, chol M i l.val ^ 2) := by
  rw [chol]; simp only [lt_irrefl, ↓reduceDIte, ↓reduceIte]

private theorem chol_of_gt (M : ℕ → ℕ → ℝ) {i k : ℕ} (hgt : i < k) :
    chol M i k = 0 := by
  rw [chol]
  have h1 : ¬(k < i) := by omega
  have h2 : k ≠ i := by omega
  simp only [h1, h2, ↓reduceDIte, ↓reduceIte]

private noncomputable def extMat {j : ℕ} (M : Fin (j + 1) → Fin (j + 1) → ℝ) (a b : ℕ) : ℝ :=
  if ha : a < j + 1 then if hb : b < j + 1 then M ⟨a, ha⟩ ⟨b, hb⟩ else 0 else 0

private noncomputable def limCovMat (j : ℕ) : Fin (j + 1) → Fin (j + 1) → ℝ :=
  fun a b => treeCovLimit (Int.natAbs ((a : ℤ) - (b : ℤ)))

private theorem continuousAt_finsetSum_real {X α : Type*} [TopologicalSpace X] {s : Finset α}
    {f : α → X → ℝ} {x : X} (hf : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun y => ∑ i ∈ s, f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuousAt_const
  | @insert a s ha ih =>
    have heq : (fun y => ∑ i ∈ insert a s, f i y) = fun y => f a y + ∑ i ∈ s, f i y :=
      funext fun y => Finset.sum_insert ha
    rw [heq]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem tendsto_finsetSum_real {ι α : Type*} {l : Filter ι} {s : Finset α}
    {f : α → ι → ℝ} {a : α → ℝ} (hf : ∀ i ∈ s, Tendsto (f i) l (nhds (a i))) :
    Tendsto (fun x => ∑ i ∈ s, f i x) l (nhds (∑ i ∈ s, a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tendsto_const_nhds
  | @insert k s hk ih =>
    simp_rw [Finset.sum_insert hk]
    exact (hf k (Finset.mem_insert_self k s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem chol_extMat_limCovMat (j : ℕ) {i k : ℕ} (hi : i ≤ j) (hk : k ≤ j) :
    chol (extMat (limCovMat j)) i k = ar2Coeff i k := by
  induction i using Nat.strong_induction_on generalizing k with
  | ind i ihi =>
    induction k using Nat.strong_induction_on with
    | ind k ihk =>
      rcases lt_trichotomy k i with hlt | hkeq | hgt
      · rw [chol_of_lt _ hlt]
        have hM : extMat (limCovMat j) i k = treeCovLimit (Int.natAbs ((i : ℤ) - (k : ℤ))) := by
          simp [extMat, limCovMat, show i < j + 1 by omega, show k < j + 1 by omega]
        have hih_kk : chol (extMat (limCovMat j)) k k = ar2Coeff k k :=
          ihi k hlt hk hk
        have hsum_eq : ∑ l : Fin k, chol (extMat (limCovMat j)) i l.val *
              chol (extMat (limCovMat j)) k l.val =
            ∑ l ∈ Finset.range k, ar2Coeff i l * ar2Coeff k l := by
          rw [← Fin.sum_univ_eq_sum_range (fun l => ar2Coeff i l * ar2Coeff k l) k]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [ihk l.val l.isLt (by omega), ihi k hlt hk (by omega)]
        have hfull : ∑ l ∈ Finset.range (k + 1), ar2Coeff i l * ar2Coeff k l =
            treeCovLimit (Int.natAbs ((i : ℤ) - (k : ℤ))) := by
          have h := ar2Coeff_inner_range_le (a := i) (b := k) (n := j) hi hk
          have hsub : ∑ l ∈ Finset.range (k + 1), ar2Coeff i l * ar2Coeff k l =
              ∑ l ∈ Finset.range (j + 1), ar2Coeff i l * ar2Coeff k l :=
            Finset.sum_subset (Finset.range_mono (by omega)) fun l _ hl => by
              have hlk : k + 1 ≤ l := by simpa [Finset.mem_range] using hl
              simp [ar2Coeff_eq_zero_of_lt (by omega : k < l)]
          rw [hsub, h]
        rw [Finset.sum_range_succ] at hfull
        rw [hM, hih_kk, hsum_eq, ← hfull, add_sub_cancel_left,
          mul_div_cancel_right₀ _ (ar2Coeff_diag_pos k).ne']
      · subst hkeq
        rw [chol_diag]
        have hM : extMat (limCovMat j) k k = 1 := by
          simp [extMat, limCovMat, show k < j + 1 by omega, treeCovLimit_zero]
        have hsum_eq : ∑ l : Fin k, chol (extMat (limCovMat j)) k l.val ^ 2 =
            ∑ l ∈ Finset.range k, ar2Coeff k l ^ 2 := by
          rw [← Fin.sum_univ_eq_sum_range (fun l => ar2Coeff k l ^ 2) k]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [ihk l.val l.isLt (by omega)]
        have hfull : ∑ l ∈ Finset.range (k + 1), ar2Coeff k l ^ 2 = 1 := by
          simpa [sq, treeCovLimit_zero] using ar2Coeff_inner_range_le (a := k) (b := k) (n := k)
            le_rfl le_rfl
        rw [Finset.sum_range_succ] at hfull
        rw [hM, hsum_eq, ← hfull, add_sub_cancel_left,
          Real.sqrt_sq (ar2Coeff_diag_pos k).le]
      · rw [chol_of_gt _ hgt, ar2Coeff_eq_zero_of_lt hgt]

private theorem continuousAt_chol_extMat (j : ℕ) {i k : ℕ} (hi : i ≤ j) (hk : k ≤ j) :
    ContinuousAt (fun M : Fin (j + 1) → Fin (j + 1) → ℝ => chol (extMat M) i k)
      (limCovMat j) := by
  have hcoord : ∀ (a b : ℕ) (ha : a ≤ j) (hb : b ≤ j),
      ContinuousAt (fun M : Fin (j + 1) → Fin (j + 1) → ℝ => extMat M a b)
        (limCovMat j) := by
    intro a b ha hb
    have heq : (fun M : Fin (j + 1) → Fin (j + 1) → ℝ => extMat M a b) =
        fun M => M ⟨a, by omega⟩ ⟨b, by omega⟩ :=
      funext fun M => by simp [extMat, show a < j + 1 by omega, show b < j + 1 by omega]
    rw [heq]
    exact ((continuous_apply (⟨b, by omega⟩ : Fin (j + 1))).comp
      (continuous_apply (⟨a, by omega⟩ : Fin (j + 1)))).continuousAt
  induction i using Nat.strong_induction_on generalizing k with
  | ind i ihi =>
    induction k using Nat.strong_induction_on with
    | ind k ihk =>
      rcases lt_trichotomy k i with hlt | hkeq | hgt
      · have hfn : (fun M : Fin (j + 1) → Fin (j + 1) → ℝ => chol (extMat M) i k) =
            fun M => (extMat M i k -
              ∑ l : Fin k, chol (extMat M) i l.val * chol (extMat M) k l.val) /
              chol (extMat M) k k :=
          funext fun M => chol_of_lt _ hlt
        rw [hfn]
        refine ContinuousAt.div ?_ ?_ ?_
        · refine (hcoord i k hi hk).sub (continuousAt_finsetSum_real fun l _ => ?_)
          exact (ihk l.val l.isLt (by omega)).mul (ihi k hlt hk (by omega))
        · exact ihi k hlt hk hk
        · rw [chol_extMat_limCovMat j hk hk]
          exact (ar2Coeff_diag_pos k).ne'
      · subst hkeq
        have hfn : (fun M : Fin (j + 1) → Fin (j + 1) → ℝ => chol (extMat M) k k) =
            fun M => Real.sqrt (extMat M k k - ∑ l : Fin k, chol (extMat M) k l.val ^ 2) :=
          funext fun M => chol_diag _ k
        rw [hfn]
        refine ContinuousAt.sqrt ((hcoord k k hk hk).sub
          (continuousAt_finsetSum_real fun l _ => ?_))
        exact (ihk l.val l.isLt (by omega)).pow 2
      · have hfn : (fun M : Fin (j + 1) → Fin (j + 1) → ℝ => chol (extMat M) i k) = fun _ => 0 :=
          funext fun M => chol_of_gt _ hgt
        rw [hfn]; exact continuousAt_const

private theorem chol_mul_transpose_eq {j : ℕ} (M : Fin (j + 1) → Fin (j + 1) → ℝ)
    (hsym : ∀ a b, M a b = M b a)
    (hrad : ∀ i : Fin (j + 1),
      0 < extMat M i.val i.val - ∑ l : Fin i.val, chol (extMat M) i.val l.val ^ 2)
    (a b : Fin (j + 1)) :
    ∑ k : Fin (j + 1), chol (extMat M) a.val k.val * chol (extMat M) b.val k.val = M a b := by
  have hle_case : ∀ x y : Fin (j + 1), y.val ≤ x.val →
      ∑ k : Fin (j + 1), chol (extMat M) x.val k.val * chol (extMat M) y.val k.val = M x y := by
    intro x y hyx
    have hsub : ∑ k : Fin (j + 1), chol (extMat M) x.val k.val * chol (extMat M) y.val k.val =
        ∑ k ∈ Finset.range (y.val + 1),
          chol (extMat M) x.val k * chol (extMat M) y.val k := by
      rw [Fin.sum_univ_eq_sum_range (fun k => chol (extMat M) x.val k * chol (extMat M) y.val k)
        (j + 1)]
      symm
      exact Finset.sum_subset (Finset.range_mono (by omega)) fun k _ hk => by
        have hgt : y.val < k := by
          have : ¬(k < y.val + 1) := by simpa [Finset.mem_range] using hk
          omega
        rw [chol_of_gt _ hgt, mul_zero]
    rw [hsub, Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range
      (fun k => chol (extMat M) x.val k * chol (extMat M) y.val k) y.val]
    have hdiag_pos : 0 < chol (extMat M) y.val y.val := by
      rw [chol_diag]; exact Real.sqrt_pos.mpr (hrad y)
    rcases eq_or_lt_of_le hyx with heq | hlt
    · have hxy : x = y := Fin.ext heq.symm
      subst hxy
      have hsq : chol (extMat M) x.val x.val * chol (extMat M) x.val x.val =
          extMat M x.val x.val - ∑ l : Fin x.val, chol (extMat M) x.val l.val ^ 2 := by
        rw [← sq, chol_diag, Real.sq_sqrt (hrad x).le]
      have hsq_sum : ∑ k : Fin x.val, chol (extMat M) x.val k.val * chol (extMat M) x.val k.val =
          ∑ l : Fin x.val, chol (extMat M) x.val l.val ^ 2 :=
        Finset.sum_congr rfl fun k _ => (sq _).symm
      rw [hsq, hsq_sum, add_sub_cancel]
      simp [extMat, x.isLt]
    · rw [chol_of_lt _ hlt, div_mul_cancel₀ _ hdiag_pos.ne', add_sub_cancel]
      simp [extMat, x.isLt, y.isLt]
  rcases le_total b.val a.val with h | h
  · exact hle_case a b h
  · rw [hsym a b, ← hle_case b a h]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **Non-backtracking walk probability convergence:** for every `j ≥ 1` and `η > 0`, there exist
`R₀ : ℕ` and `ε₀ > 0` such that for all `R ≥ R₀` and `0 < ε ≤ ε₀`, on *every* finite cubic simple
graph `H'` with no closed non-backtracking walk of length `1 ≤ k ≤ 2 * R + j + 4`, the event that
a given non-backtracking walk `w` of length `j` crosses every step of `crossingGraph H' b` has
probability within `η` of `ar2AltProb j`. -/
theorem exists_nbWalk_prob_close (j : ℕ) (hj : 1 ≤ j) (η : ℝ) (hη : 0 < η) :
    ∃ (R₀ : ℕ) (ε₀ : ℝ), 0 < ε₀ ∧
      ∀ {V' : Type*} [Fintype V'] (H' : SimpleGraph V'),
        (∀ v : V', open Classical in H'.degree v = 3) →
        ∀ (R : ℕ), R₀ ≤ R → ∀ (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        (∀ (k : ℕ), 1 ≤ k → k ≤ 2 * R + j + 4 →
          ∀ w' : Fin (k + 1) → V', IsNBWalk H' k w' → w' 0 ≠ w' (Fin.last k)) →
        ∀ w : Fin (j + 1) → V', IsNBWalk H' j w →
          |(piGauss (V' ⊕ V')).real
            {g | IsNBWalk (crossingGraph H' (thresholdVec (waveScore H' R ε g) 0)) j w} -
            ar2AltProb j| ≤ η := by
  let _ := hj
  let rad : (Fin (j + 1) → Fin (j + 1) → ℝ) → Fin (j + 1) → ℝ := fun M i =>
    extMat M i.val i.val - ∑ l : Fin i.val, chol (extMat M) i.val l.val ^ 2
  have hrad_cont : ∀ i : Fin (j + 1), ContinuousAt (fun M => rad M i) (limCovMat j) := by
    intro i
    have hdiag : ContinuousAt (fun M : Fin (j + 1) → Fin (j + 1) → ℝ => extMat M i.val i.val)
        (limCovMat j) := by
      have heq : (fun M : Fin (j + 1) → Fin (j + 1) → ℝ => extMat M i.val i.val) =
          fun M => M i i := funext fun M => by simp [extMat, i.isLt]
      rw [heq]; exact ((continuous_apply i).comp (continuous_apply i)).continuousAt
    refine hdiag.sub (continuousAt_finsetSum_real fun l _ => ?_)
    exact (continuousAt_chol_extMat j (by omega) (by omega)).pow 2
  have hrad_val : ∀ i : Fin (j + 1), 0 < rad (limCovMat j) i := by
    intro i
    have h1 : extMat (limCovMat j) i.val i.val = 1 := by
      simp [extMat, limCovMat, i.isLt, treeCovLimit_zero]
    have h2 : ∑ l : Fin i.val, chol (extMat (limCovMat j)) i.val l.val ^ 2 =
        ∑ l ∈ Finset.range i.val, ar2Coeff i.val l ^ 2 := by
      rw [← Fin.sum_univ_eq_sum_range (fun l => ar2Coeff i.val l ^ 2) i.val]
      refine Finset.sum_congr rfl fun l _ => by
        rw [chol_extMat_limCovMat j (by omega) (by omega)]
    have hfull : ∑ l ∈ Finset.range (i.val + 1), ar2Coeff i.val l ^ 2 = 1 := by
      simpa [sq, treeCovLimit_zero] using ar2Coeff_inner_range_le (a := i.val) (b := i.val)
        (n := i.val) le_rfl le_rfl
    rw [Finset.sum_range_succ] at hfull
    dsimp only [rad]
    rw [h1, h2, ← hfull, add_sub_cancel_left]
    exact sq_pos_of_pos (ar2Coeff_diag_pos i.val)
  let orthProb : (Fin (j + 1) → Fin (j + 1) → ℝ) → ℝ := fun M =>
    (piGauss (Fin (j + 1))).real
      {ξ | ∀ i : Fin (j + 1),
        0 < (-1 : ℝ) ^ i.val * ∑ k : Fin (j + 1), chol (extMat M) i.val k.val * ξ k}
  have horth_cont : ContinuousAt orthProb (limCovMat j) := by
    rw [ContinuousAt, tendsto_iff_seq_tendsto]
    intro M hM
    let S : (Fin (j + 1) → Fin (j + 1) → ℝ) → Set (Fin (j + 1) → ℝ) := fun N =>
      {ξ | ∀ i : Fin (j + 1),
        0 < (-1 : ℝ) ^ i.val * ∑ k : Fin (j + 1), chol (extMat N) i.val k.val * ξ k}
    have hS_meas : ∀ N, MeasurableSet (S N) := fun N => by
      have heq : S N = ⋂ i : Fin (j + 1),
          {ξ | (0 : ℝ) < (-1 : ℝ) ^ i.val *
            ∑ k : Fin (j + 1), chol (extMat N) i.val k.val * ξ k} := by
        ext ξ; simp [S]
      rw [heq]
      refine MeasurableSet.iInter fun i => measurableSet_lt measurable_const ?_
      fun_prop
    have hind_eq : ∀ N, orthProb N =
        ∫ ξ, (S N).indicator (fun _ => (1 : ℝ)) ξ ∂(piGauss (Fin (j + 1))) := fun N =>
      (integral_indicator_one (hS_meas N)).symm
    change Tendsto (fun n => orthProb (M n)) atTop (nhds (orthProb (limCovMat j)))
    simp_rw [hind_eq]
    have hae_nz : ∀ᵐ ξ ∂(piGauss (Fin (j + 1))),
        ∀ i : Fin (j + 1), ar2StepMap j ξ i ≠ 0 := by
      rw [ae_all_iff]
      intro i
      rw [ae_iff]
      have hset : {ξ : Fin (j + 1) → ℝ | ¬ ar2StepMap j ξ i ≠ 0} =
          ((fun k : Fin (j + 1) => ar2Coeff i.val k.val) ⬝ᵥ ·) ⁻¹' {0} := by
        ext ξ; simp [ar2StepMap, dotProduct]
      have hnn : ‖WithLp.toLp 2 (fun k : Fin (j + 1) => ar2Coeff i.val k.val)‖₊ ^ 2 = 1 := by
        ext
        simp only [NNReal.coe_pow, coe_nnNorm, NNReal.coe_one, EuclideanSpace.norm_sq_eq,
          Real.norm_eq_abs, sq_abs]
        exact ar2Coeff_sq_sum_eq_one j i
      have hmap : (piGauss (Fin (j + 1))).map
          ((fun k : Fin (j + 1) => ar2Coeff i.val k.val) ⬝ᵥ ·) = gaussianReal 0 1 := by
        rw [pi_gaussianReal_map_dotProduct, hnn]
      rw [hset, ← Measure.map_apply (by fun_prop) (MeasurableSet.singleton 0), hmap]
      have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
      exact measure_singleton 0
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => ((measurable_const : Measurable fun _ : Fin (j + 1) → ℝ => (1 : ℝ)).indicator
        (hS_meas (M n))).aestronglyMeasurable)
      (integrable_const (μ := piGauss (Fin (j + 1))) (1 : ℝ))
      (fun n => ae_of_all _ fun ξ => by
        rw [Real.norm_eq_abs]
        by_cases h : ξ ∈ S (M n) <;> simp [h])
      ?_
    filter_upwards [hae_nz] with ξ hξ
    have hval_lim : ∀ i : Fin (j + 1),
        Tendsto (fun n => (-1 : ℝ) ^ i.val *
          ∑ k : Fin (j + 1), chol (extMat (M n)) i.val k.val * ξ k)
          atTop (nhds ((-1 : ℝ) ^ i.val * ar2StepMap j ξ i)) := by
      intro i
      have hterm : ∀ k : Fin (j + 1),
          Tendsto (fun n => chol (extMat (M n)) i.val k.val * ξ k) atTop
            (nhds (ar2Coeff i.val k.val * ξ k)) := fun k => by
        have hck := (continuousAt_chol_extMat j (i := i.val) (k := k.val)
          (by omega) (by omega)).tendsto.comp hM
        rw [chol_extMat_limCovMat j (by omega) (by omega)] at hck
        exact hck.mul_const (ξ k)
      have hsum : Tendsto (fun n =>
          ∑ k : Fin (j + 1), chol (extMat (M n)) i.val k.val * ξ k) atTop
          (nhds (∑ k : Fin (j + 1), ar2Coeff i.val k.val * ξ k)) :=
        tendsto_finsetSum_real fun k _ => hterm k
      exact hsum.const_mul ((-1 : ℝ) ^ i.val)
    have hlim_eq : (S (limCovMat j)).indicator (fun _ => (1 : ℝ)) ξ =
        if ∀ i : Fin (j + 1), 0 < (-1 : ℝ) ^ i.val * ar2StepMap j ξ i then 1 else 0 := by
      have hsum_eq : ∀ i : Fin (j + 1),
          ∑ k : Fin (j + 1), chol (extMat (limCovMat j)) i.val k.val * ξ k =
            ar2StepMap j ξ i := fun i =>
        Finset.sum_congr rfl fun k _ => by
          rw [chol_extMat_limCovMat j (by omega) (by omega)]
      have hiff : ξ ∈ S (limCovMat j) ↔
          ∀ i : Fin (j + 1), 0 < (-1 : ℝ) ^ i.val * ar2StepMap j ξ i := by
        simp only [S, Set.mem_ofPred_eq, hsum_eq]
      by_cases h : ∀ i : Fin (j + 1), 0 < (-1 : ℝ) ^ i.val * ar2StepMap j ξ i
      · simp [Set.indicator_of_mem (hiff.mpr h), h]
      · simp [Set.indicator_of_notMem (mt hiff.mp h), h]
    by_cases hpos : ∀ i : Fin (j + 1), 0 < (-1 : ℝ) ^ i.val * ar2StepMap j ξ i
    · have hev : ∀ᶠ n in atTop, ξ ∈ S (M n) :=
        eventually_all.mpr fun i => (hval_lim i).eventually (Ioi_mem_nhds (hpos i))
      refine tendsto_const_nhds.congr' (hev.mono fun n hn => ?_)
      dsimp only
      rw [hlim_eq, ite_eq_left_iff.mpr (fun h => (h hpos).elim), Set.indicator_of_mem hn]
    · push Not at hpos
      obtain ⟨i₀, hi₀⟩ := hpos
      have hne0 : (-1 : ℝ) ^ i₀.val * ar2StepMap j ξ i₀ ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (by norm_num)) (hξ i₀)
      have hlt : (-1 : ℝ) ^ i₀.val * ar2StepMap j ξ i₀ < 0 := lt_of_le_of_ne hi₀ hne0
      have hev : ∀ᶠ n in atTop, ξ ∉ S (M n) := by
        filter_upwards [(hval_lim i₀).eventually (Iio_mem_nhds hlt)] with n hn hmem
        exact (not_lt.mpr hn.le) (hmem i₀)
      refine tendsto_const_nhds.congr' (hev.mono fun n hn => ?_)
      have hnot : ¬ ∀ i : Fin (j + 1), 0 < (-1 : ℝ) ^ i.val * ar2StepMap j ξ i :=
        fun h => not_lt.mpr hi₀ (h i₀)
      dsimp only
      rw [hlim_eq, ite_eq_right_iff.mpr (fun h => (hnot h).elim), Set.indicator_of_notMem hn]
  have hnb_ev : ∀ᶠ M in nhds (limCovMat j),
      (∀ i : Fin (j + 1), 0 < rad M i) ∧ |orthProb M - orthProb (limCovMat j)| ≤ η / 2 := by
    have h1 : ∀ᶠ M in nhds (limCovMat j), ∀ i : Fin (j + 1), 0 < rad M i :=
      eventually_all.mpr fun i => (hrad_cont i).eventually (Ioi_mem_nhds (hrad_val i))
    have h2 : ∀ᶠ M in nhds (limCovMat j), |orthProb M - orthProb (limCovMat j)| < η / 2 :=
      (horth_cont.tendsto.eventually
        (Metric.ball_mem_nhds _ (half_pos hη))).mono fun M hM => by
          simpa [Metric.mem_ball, Real.dist_eq] using hM
    filter_upwards [h1, h2] with M hM1 hM2
    exact ⟨hM1, hM2.le⟩
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := Metric.eventually_nhds_iff.mp hnb_ev
  have hR_all : ∀ d : Fin (j + 1),
      ∃ Rd : ℕ, ∀ R : ℕ, Rd ≤ R → |treeOverlap R d.val - treeCovLimit d.val| < δ / 4 := by
    intro d
    have ht := tendsto_treeOverlap d.val
    rw [Metric.tendsto_atTop] at ht
    obtain ⟨Rd, hRd⟩ := ht (δ / 4) (by positivity)
    exact ⟨Rd, fun R hR => by simpa [Real.dist_eq] using hRd R hR⟩
  choose Rd hRd using hR_all
  let R₀ : ℕ := max j (Finset.univ.sup Rd)
  let Mbound : ℝ := 1 + Finset.univ.sup' Finset.univ_nonempty
    (fun d : Fin (j + 1) => |treeCovLimit d.val|)
  have hMb_pos : 0 < Mbound := by
    have h0 : |treeCovLimit 0| ≤
        Finset.univ.sup' Finset.univ_nonempty (fun d : Fin (j + 1) => |treeCovLimit d.val|) :=
      Finset.le_sup' (fun d : Fin (j + 1) => |treeCovLimit d.val|)
        (Finset.mem_univ (0 : Fin (j + 1)))
    have hnn : (0 : ℝ) ≤ |treeCovLimit 0| := abs_nonneg _
    change 0 < 1 + _
    linarith
  let ε₀ : ℝ := min (1 / 2) (Real.sqrt (δ / (4 * (Mbound + 1))))
  have hε₀_pos : 0 < ε₀ :=
    lt_min (by norm_num) (Real.sqrt_pos.mpr (by positivity))
  refine ⟨R₀, ε₀, hε₀_pos, fun {V'} _ H' hreg R hR ε hε0 hε1 hgirth w hw => ?_⟩
  classical
  have hε_le_half : ε ≤ 1 / 2 := hε1.trans (min_le_left _ _)
  have hε_le1 : ε ≤ 1 := by linarith
  have hjR : j ≤ R := (le_max_left j _).trans hR
  let sigM : Fin (j + 1) → Fin (j + 1) → ℝ := fun a b =>
    (1 - ε ^ 2) * treeOverlap R (Int.natAbs ((a : ℤ) - (b : ℤ))) +
      if a = b then ε ^ 2 else 0
  have hsig_dist : dist sigM (limCovMat j) < δ := by
    rw [dist_pi_lt_iff hδ_pos]
    intro a
    rw [dist_pi_lt_iff hδ_pos]
    intro b
    rw [Real.dist_eq]
    dsimp only [sigM, limCovMat]
    set d : ℕ := Int.natAbs ((a : ℤ) - (b : ℤ))
    have hd_lt : d < j + 1 := by omega
    let df : Fin (j + 1) := ⟨d, hd_lt⟩
    have hRd_le : Rd df ≤ R := (Finset.le_sup (Finset.mem_univ df)).trans
      ((le_max_right j _).trans hR)
    have htd : |treeOverlap R d - treeCovLimit d| < δ / 4 := hRd df R hRd_le
    have hcd_le : |treeCovLimit d| ≤ Mbound := by
      have h1 := Finset.le_sup' (fun k : Fin (j + 1) => |treeCovLimit k.val|) (Finset.mem_univ df)
      linarith
    have hε_sq : ε ^ 2 ≤ δ / (4 * (Mbound + 1)) := by
      have hle : ε ≤ Real.sqrt (δ / (4 * (Mbound + 1))) := hε1.trans (min_le_right _ _)
      calc ε ^ 2 ≤ Real.sqrt (δ / (4 * (Mbound + 1))) ^ 2 :=
            sq_le_sq' (by linarith [Real.sqrt_nonneg (δ / (4 * (Mbound + 1)))]) hle
        _ = δ / (4 * (Mbound + 1)) := Real.sq_sqrt (by positivity)
    have h1e_nn : 0 ≤ 1 - ε ^ 2 := by nlinarith
    have h1e_le : 1 - ε ^ 2 ≤ 1 := by nlinarith
    have hdiag_le : |if a = b then ε ^ 2 else (0 : ℝ)| ≤ ε ^ 2 := by
      split_ifs
      · rw [abs_of_nonneg (sq_nonneg ε)]
      · simp [sq_nonneg ε]
    have heq : (1 - ε ^ 2) * treeOverlap R d + (if a = b then ε ^ 2 else 0) - treeCovLimit d =
        (1 - ε ^ 2) * (treeOverlap R d - treeCovLimit d) -
          ε ^ 2 * treeCovLimit d + (if a = b then ε ^ 2 else 0) := by ring
    rw [heq]
    calc |(1 - ε ^ 2) * (treeOverlap R d - treeCovLimit d) - ε ^ 2 * treeCovLimit d +
            (if a = b then ε ^ 2 else 0)|
        ≤ |(1 - ε ^ 2) * (treeOverlap R d - treeCovLimit d) - ε ^ 2 * treeCovLimit d| +
            |if a = b then ε ^ 2 else (0 : ℝ)| := abs_add_le _ _
      _ ≤ (|(1 - ε ^ 2) * (treeOverlap R d - treeCovLimit d)| + |ε ^ 2 * treeCovLimit d|) +
            ε ^ 2 := add_le_add (abs_sub _ _) hdiag_le
      _ = (1 - ε ^ 2) * |treeOverlap R d - treeCovLimit d| +
            ε ^ 2 * |treeCovLimit d| + ε ^ 2 := by
            rw [abs_mul, abs_of_nonneg h1e_nn, abs_mul, abs_of_nonneg (sq_nonneg ε)]
      _ ≤ 1 * (δ / 4) + ε ^ 2 * (Mbound + 1) := by
            have ha1 : (1 - ε ^ 2) * |treeOverlap R d - treeCovLimit d| ≤ 1 * (δ / 4) :=
              mul_le_mul h1e_le htd.le (abs_nonneg _) zero_le_one
            have ha2 : ε ^ 2 * |treeCovLimit d| ≤ ε ^ 2 * Mbound :=
              mul_le_mul_of_nonneg_left hcd_le (sq_nonneg ε)
            linarith
      _ ≤ δ / 4 + δ / 4 := by
            have : ε ^ 2 * (Mbound + 1) ≤ δ / 4 := by
              calc ε ^ 2 * (Mbound + 1) ≤ (δ / (4 * (Mbound + 1))) * (Mbound + 1) :=
                    mul_le_mul_of_nonneg_right hε_sq (by linarith)
                _ = δ / 4 := by field_simp [(by linarith : Mbound + 1 ≠ 0)]
            linarith
      _ < δ := by linarith
  obtain ⟨hradsig, horth_close⟩ := hδ_ball hsig_dist
  have hsig_sym : ∀ a b : Fin (j + 1), sigM a b = sigM b a := by
    intro a b
    simp only [sigM]
    have hnat : Int.natAbs ((a : ℤ) - (b : ℤ)) = Int.natAbs ((b : ℤ) - (a : ℤ)) := by omega
    rw [hnat]
    by_cases h : a = b
    · subst h; simp
    · have h' : b ≠ a := Ne.symm h; simp [h, h']
  have hgram : ∀ a b : Fin (j + 1),
      ∑ z' : V' ⊕ V', waveRow H' R ε (w a) z' * waveRow H' R ε (w b) z' =
        ∑ k : Fin (j + 1), chol (extMat sigM) a.val k.val * chol (extMat sigM) b.val k.val := by
    intro a b
    rw [waveRow_inner_eq_treeOverlap H' hreg hjR hε0.le hε_le1
        (fun k h1 h2 => hgirth k h1 (by omega)) hw a b,
      chol_mul_transpose_eq sigM hsig_sym hradsig a b]
  have hlaw : (piGauss (V' ⊕ V')).map
        (fun g i => waveScore H' R ε g (w i)) =
      (piGauss (Fin (j + 1))).map
        (fun ξ i => ∑ k : Fin (j + 1), chol (extMat sigM) i.val k.val * ξ k) :=
    map_piGauss_eq_of_gram_eq (fun (i : Fin (j + 1)) => waveRow H' R ε (w i))
      (fun (i : Fin (j + 1)) (k : Fin (j + 1)) => chol (extMat sigM) i.val k.val) hgram
  let Pplus : Set (V' ⊕ V' → ℝ) :=
    {g | ∀ i : Fin (j + 1), 0 < (-1 : ℝ) ^ i.val * waveScore H' R ε g (w i)}
  let Pminus : Set (V' ⊕ V' → ℝ) :=
    {g | ∀ i : Fin (j + 1), (-1 : ℝ) ^ i.val * waveScore H' R ε g (w i) < 0}
  let Ewalk : Set (V' ⊕ V' → ℝ) :=
    {g | IsNBWalk (crossingGraph H' (thresholdVec (waveScore H' R ε g) 0)) j w}
  have hPplus_meas : MeasurableSet Pplus := by
    have heq : Pplus = ⋂ i : Fin (j + 1),
        {g | (0 : ℝ) < (-1 : ℝ) ^ i.val * waveScore H' R ε g (w i)} := by
      ext g; simp [Pplus]
    rw [heq]
    refine MeasurableSet.iInter fun i => measurableSet_lt measurable_const ?_
    unfold waveScore; fun_prop
  have hPminus_meas : MeasurableSet Pminus := by
    have heq : Pminus = ⋂ i : Fin (j + 1),
        {g | (-1 : ℝ) ^ i.val * waveScore H' R ε g (w i) < (0 : ℝ)} := by
      ext g; simp [Pminus]
    rw [heq]
    refine MeasurableSet.iInter fun i => measurableSet_lt ?_ measurable_const
    unfold waveScore; fun_prop
  have hdisj : Disjoint Pplus Pminus := Set.disjoint_left.mpr fun g h1 h2 =>
    not_lt.mpr (h1 0).le (h2 0)
  have hsym_eq : (piGauss (V' ⊕ V')).real Pminus = (piGauss (V' ⊕ V')).real Pplus := by
    have hmp := measurePreserving_neg_piGauss (κ := V' ⊕ V')
    have hpre : (fun g : V' ⊕ V' → ℝ => -g) ⁻¹' Pplus = Pminus := by
      ext g
      simp only [Set.mem_preimage, Pplus, Pminus, Set.mem_ofPred_eq]
      refine forall_congr' fun i => ?_
      have hneg : waveScore H' R ε (-g) (w i) = -waveScore H' R ε g (w i) := by
        simp [waveScore, mul_neg, Finset.sum_neg_distrib]
      rw [hneg, mul_neg]
      exact ⟨fun h => neg_pos.mp h, fun h => neg_pos.mpr h⟩
    rw [← hpre]
    exact hmp.measureReal_preimage hPplus_meas.nullMeasurableSet
  have hae_nz_w : ∀ᵐ g ∂(piGauss (V' ⊕ V')), ∀ i : Fin (j + 1),
      waveScore H' R ε g (w i) ≠ 0 := by
    rw [ae_all_iff]
    intro i
    rw [ae_iff]
    have hset : {g : V' ⊕ V' → ℝ | ¬ waveScore H' R ε g (w i) ≠ 0} =
        (waveRow H' R ε (w i) ⬝ᵥ ·) ⁻¹' {0} := by
      ext g; simp [waveScore, dotProduct]
    have hnn : ‖WithLp.toLp 2 (waveRow H' R ε (w i))‖₊ ^ 2 = 1 := by
      ext
      simp only [NNReal.coe_pow, coe_nnNorm, NNReal.coe_one, EuclideanSpace.norm_sq_eq,
        Real.norm_eq_abs, sq_abs]
      exact sum_sq_waveRow_eq_one H' hreg R hε0.le hε_le1 (w i)
    have hmap : (piGauss (V' ⊕ V')).map (waveRow H' R ε (w i) ⬝ᵥ ·) = gaussianReal 0 1 := by
      rw [pi_gaussianReal_map_dotProduct, hnn]
    rw [hset, ← Measure.map_apply (by fun_prop) (MeasurableSet.singleton 0), hmap]
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    exact measure_singleton 0
  have hae_eq : Ewalk =ᵐ[piGauss (V' ⊕ V')] (Pplus ∪ Pminus : Set (V' ⊕ V' → ℝ)) := by
    filter_upwards [hae_nz_w] with g hg
    simp only [Ewalk, Pplus, Pminus, Set.mem_union, Set.mem_ofPred_eq,
      isNBWalk_crossingGraph_iff, hw, true_and]
    have hstep_pos : ∀ (c : Fin (j + 1) → ℝ), (∀ i, c i ≠ 0) →
        ((∀ i : Fin j, thresholdVec c 0 i.castSucc ≠ thresholdVec c 0 i.succ) ↔
          (∀ i : Fin (j + 1), 0 < (-1 : ℝ) ^ i.val * c i) ∨
            (∀ i : Fin (j + 1), (-1 : ℝ) ^ i.val * c i < 0)) := by
      intro c hc
      have hsign : ∀ x : ℝ, x ≠ 0 →
          (thresholdVec (fun _ : Unit => x) 0 () = true ↔ x < 0) := fun x _ =>
        thresholdVec_apply_eq_true _ 0 ()
      constructor
      · intro halt
        have hstep_neg : ∀ i : Fin j,
            ((-1 : ℝ) ^ i.castSucc.val * c i.castSucc < 0 ↔
              (-1 : ℝ) ^ i.succ.val * c i.succ < 0) := by
          intro i
          have hne := halt i
          have hp : (-1 : ℝ) ^ i.succ.val = -(-1 : ℝ) ^ i.castSucc.val := by
            simp [Fin.val_succ, pow_succ]
          rw [hp, neg_mul]
          cases h1 : thresholdVec c 0 i.castSucc <;> cases h2 : thresholdVec c 0 i.succ
          · exact (hne (h1.trans h2.symm)).elim
          · have hc1 : 0 < c i.castSucc :=
              lt_of_le_of_ne ((thresholdVec_apply_eq_false c 0 _).mp h1) (hc _).symm
            have hc2 : c i.succ < 0 := (thresholdVec_apply_eq_true c 0 _).mp h2
            rcases Nat.even_or_odd i.castSucc.val with hev | hodd
            · rw [hev.neg_one_pow]
              simp [not_lt.mpr hc1.le, not_lt.mpr (by linarith : 0 ≤ -c i.succ)]
            · rw [hodd.neg_one_pow]; simp [hc1, hc2]
          · have hc1 : c i.castSucc < 0 := (thresholdVec_apply_eq_true c 0 _).mp h1
            have hc2 : 0 < c i.succ :=
              lt_of_le_of_ne ((thresholdVec_apply_eq_false c 0 _).mp h2) (hc _).symm
            rcases Nat.even_or_odd i.castSucc.val with hev | hodd
            · rw [hev.neg_one_pow]; simp [hc1, hc2]
            · rw [hodd.neg_one_pow]; simp [not_lt.mpr (by linarith : 0 ≤ -c i.castSucc),
                not_lt.mpr hc2.le]
          · exact (hne (h1.trans h2.symm)).elim
        have hall : ∀ i : Fin (j + 1),
            ((-1 : ℝ) ^ i.val * c i < 0 ↔ c 0 < 0) := by
          intro i
          induction i using Fin.induction with
          | zero => simp
          | succ k ih => exact (hstep_neg k).symm.trans ih
        rcases lt_or_gt_of_ne (hc 0) with h0 | h0
        · right; intro i; exact (hall i).mpr h0
        · left; intro i
          have hnot : ¬((-1 : ℝ) ^ i.val * c i < 0) := fun h => not_lt.mpr h0.le ((hall i).mp h)
          exact lt_of_le_of_ne (not_lt.mp hnot)
            (mul_ne_zero (pow_ne_zero _ (by norm_num)) (hc i)).symm
      · intro h i
        -- in either phase consecutive entries have opposite signs
        have hprod : c i.castSucc * c i.succ < 0 := by
          have hpw : (-1 : ℝ) ^ i.succ.val = -(-1 : ℝ) ^ i.castSucc.val := by
            simp [Fin.val_succ, pow_succ]
          have hsq : ((-1 : ℝ) ^ i.castSucc.val) ^ 2 = 1 := by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num
          have hpos : 0 < ((-1 : ℝ) ^ i.castSucc.val * c i.castSucc) *
              ((-1 : ℝ) ^ i.succ.val * c i.succ) := by
            rcases h with hp | hm
            · exact mul_pos (hp _) (hp _)
            · exact mul_pos_of_neg_of_neg (hm _) (hm _)
          have hrw : ((-1 : ℝ) ^ i.castSucc.val * c i.castSucc) *
              (-(-1 : ℝ) ^ i.castSucc.val * c i.succ) =
              -(((-1 : ℝ) ^ i.castSucc.val) ^ 2 * (c i.castSucc * c i.succ)) := by ring
          rw [hpw, hrw, hsq, one_mul] at hpos
          linarith
        rcases mul_neg_iff.mp hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [(thresholdVec_apply_eq_false c 0 _).mpr h1.le,
            (thresholdVec_apply_eq_true c 0 _).mpr h2]
          decide
        · rw [(thresholdVec_apply_eq_true c 0 _).mpr h1,
            (thresholdVec_apply_eq_false c 0 _).mpr h2.le]
          decide
    exact hstep_pos (fun i => waveScore H' R ε g (w i)) hg
  have hE_eq : (piGauss (V' ⊕ V')).real Ewalk = 2 * (piGauss (V' ⊕ V')).real Pplus := by
    rw [measureReal_congr hae_eq, measureReal_union hdisj hPminus_meas, hsym_eq]; ring
  let orthSet : Set (Fin (j + 1) → ℝ) :=
    {x | ∀ i : Fin (j + 1), 0 < (-1 : ℝ) ^ i.val * x i}
  have horthSet_meas : MeasurableSet orthSet := by
    have heq : orthSet = ⋂ i : Fin (j + 1), {x | (0 : ℝ) < (-1 : ℝ) ^ i.val * x i} := by
      ext x; simp [orthSet]
    rw [heq]
    exact MeasurableSet.iInter fun i =>
      measurableSet_lt measurable_const (measurable_const.mul (measurable_pi_apply i))
  have hPplus_eq : (piGauss (V' ⊕ V')).real Pplus = orthProb sigM := by
    have h1 : Pplus = (fun g i => waveScore H' R ε g (w i)) ⁻¹' orthSet := by
      ext g; simp [Pplus, orthSet]
    have h2 : {ξ : Fin (j + 1) → ℝ | ∀ i : Fin (j + 1), 0 < (-1 : ℝ) ^ i.val *
          ∑ k : Fin (j + 1), chol (extMat sigM) i.val k.val * ξ k} =
        (fun (ξ : Fin (j + 1) → ℝ) (i : Fin (j + 1)) =>
          ∑ k : Fin (j + 1), chol (extMat sigM) i.val k.val * ξ k) ⁻¹' orthSet := by
      ext ξ; simp [orthSet]
    have hm1 : Measurable (fun g : V' ⊕ V' → ℝ => fun i => waveScore H' R ε g (w i)) := by
      rw [measurable_pi_iff]; intro i; unfold waveScore; fun_prop
    have hm2 : Measurable (fun (ξ : Fin (j + 1) → ℝ) (i : Fin (j + 1)) =>
        ∑ k : Fin (j + 1), chol (extMat sigM) i.val k.val * ξ k) := by
      rw [measurable_pi_iff]; intro i; fun_prop
    change (piGauss (V' ⊕ V')).real Pplus = (piGauss (Fin (j + 1))).real _
    rw [h1, h2, measureReal_def, measureReal_def,
      ← Measure.map_apply hm1 horthSet_meas, hlaw, Measure.map_apply hm2 horthSet_meas]
  have har2_eq : ar2AltProb j = 2 * orthProb (limCovMat j) := by
    unfold ar2AltProb orthProb
    congr 2
    ext ξ
    have heq_sum : ∀ i : Fin (j + 1), ar2StepMap j ξ i =
        ∑ k : Fin (j + 1), chol (extMat (limCovMat j)) i.val k.val * ξ k := fun i =>
      Finset.sum_congr rfl fun k _ => by
        rw [chol_extMat_limCovMat j (by omega) (by omega)]
    simp only [Set.mem_ofPred_eq, heq_sum]
  rw [show (piGauss (V' ⊕ V')).real
      {g | IsNBWalk (crossingGraph H' (thresholdVec (waveScore H' R ε g) 0)) j w} =
      (piGauss (V' ⊕ V')).real Ewalk from rfl, hE_eq, hPplus_eq, har2_eq]
  rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  linarith [horth_close]

end HighGirthConvergence

/-! ### Main expectation theorem for finite cubic graphs -/

section MainExpectation

/-- `simpleCrossingCover H` is submodular on `V → Bool`. -/
theorem isSubmodularBool_simpleCrossingCover {V : Type*} [Finite V] (H : SimpleGraph V) :
    IsSubmodularBool (fun b : V → Bool => (simpleCrossingCover H b : ℝ)) := by
  have heq : (fun b : V → Bool => (simpleCrossingCover H b : ℝ)) =
      fun b => (crossingCover (ofSimpleGraph H) b : ℝ) :=
    funext fun b => by rw [crossingCover_ofSimpleGraph]
  rw [heq]
  exact isSubmodularBool_crossingCover (ofSimpleGraph H)

/-- `simpleCrossingCover H` is complement-symmetric on `V → Bool`. -/
theorem isSymmetricBool_simpleCrossingCover {V : Type*} [Finite V] (H : SimpleGraph V) :
    IsSymmetricBool (fun b : V → Bool => (simpleCrossingCover H b : ℝ)) := by
  have heq : (fun b : V → Bool => (simpleCrossingCover H b : ℝ)) =
      fun b => (crossingCover (ofSimpleGraph H) b : ℝ) :=
    funext fun b => by rw [crossingCover_ofSimpleGraph]
  rw [heq]
  exact isSymmetricBool_crossingCover (ofSimpleGraph H)

/-- **Uniform radial wave expectation upper bound:** for every odd truncation order `J ≥ 1` and
every `η > 0`, there exist `R : ℕ` and `ε ∈ (0, 1)` such that for *every* finite cubic simple
graph `H` and *every* real threshold `t`,
`E[simpleCrossingCover H (thresholdVec (waveScore H R ε g) t)] ≤
(alternatingWaveSum J + η) * |V|`. -/
theorem exists_wave_params_expected_crossingCover_le.{u} (J : ℕ) (hJ : Odd J)
    (η : ℝ) (hη : 0 < η) :
    ∃ (R : ℕ) (ε : ℝ), 0 < ε ∧ ε < 1 ∧
      ∀ {V : Type u} [Fintype V] (H : SimpleGraph V),
        (∀ v : V, open Classical in H.degree v = 3) →
        ∀ t : ℝ,
          ∫ g, (simpleCrossingCover H (thresholdVec (waveScore H R ε g) t) : ℝ)
              ∂(piGauss (V ⊕ V)) ≤
            (alternatingWaveSum J + η) * (Fintype.card V : ℝ) := by
  have hJ1 : 1 ≤ J := by obtain ⟨k, rfl⟩ := hJ; omega
  let Cwalk : ℝ := ∑ j ∈ Finset.Icc 1 J, (3 / 2 : ℝ) * (2 : ℝ) ^ (j - 1)
  have hCwalk_pos : 0 < Cwalk := by
    have h1 : (1 : ℕ) ∈ Finset.Icc 1 J := Finset.mem_Icc.mpr ⟨le_rfl, hJ1⟩
    have hterm_le : (3 / 2 : ℝ) * (2 : ℝ) ^ (1 - 1) ≤ Cwalk :=
      Finset.single_le_sum (f := fun j : ℕ => (3 / 2 : ℝ) * (2 : ℝ) ^ (j - 1))
        (fun j _ => by positivity) h1
    have hpos : (0 : ℝ) < (3 / 2 : ℝ) * (2 : ℝ) ^ (1 - 1) := by norm_num
    exact hpos.trans_le hterm_le
  let ηwalk : ℝ := η / (2 * Cwalk)
  have hηwalk_pos : 0 < ηwalk := by positivity
  have herr_ge2 : 2 ≤ altErrConst J := by
    unfold altErrConst; omega
  let ηdeg : ℝ := η / (altErrConst J : ℝ)
  have hηdeg_pos : 0 < ηdeg := by
    exact div_pos hη (Nat.cast_pos.mpr (by omega))
  obtain ⟨Rdeg, εdeg, hεdeg_pos, hdeg_bd⟩ := exists_degThree_star_bound ηdeg hηdeg_pos
  have hwalk_ex : ∀ j : {j : ℕ // j ∈ Finset.Icc 1 J},
      ∃ (Rj : ℕ) (εj : ℝ), 0 < εj ∧
        ∀ {V' : Type u} [Fintype V'] (H' : SimpleGraph V'),
          (∀ v : V', open Classical in H'.degree v = 3) →
          ∀ (R : ℕ), Rj ≤ R → ∀ (ε : ℝ), 0 < ε → ε ≤ εj →
          (∀ (k : ℕ), 1 ≤ k → k ≤ 2 * R + j.1 + 4 →
            ∀ w' : Fin (k + 1) → V', IsNBWalk H' k w' → w' 0 ≠ w' (Fin.last k)) →
          ∀ w : Fin (j.1 + 1) → V', IsNBWalk H' j.1 w →
            |(piGauss (V' ⊕ V')).real
              {g | IsNBWalk (crossingGraph H' (thresholdVec (waveScore H' R ε g) 0)) j.1 w} -
              ar2AltProb j.1| ≤ ηwalk := fun j =>
    exists_nbWalk_prob_close j.1 (Finset.mem_Icc.mp j.2).1 ηwalk hηwalk_pos
  choose Rj hRj using hwalk_ex
  choose εj hεj using hRj
  let S : Finset {j : ℕ // j ∈ Finset.Icc 1 J} := Finset.univ
  let R : ℕ := max Rdeg (S.sup Rj)
  have hS_ne : S.Nonempty := ⟨⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hJ1⟩⟩, Finset.mem_univ _⟩
  let ε : ℝ := min (1 / 2) (min εdeg (S.inf' hS_ne εj))
  have hε_pos : 0 < ε := by
    refine lt_min (by norm_num) (lt_min hεdeg_pos ?_)
    rw [Finset.lt_inf'_iff]
    intro j _; exact (hεj j).1
  have hε_lt1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hε_le_deg : ε ≤ εdeg := (min_le_right _ _).trans (min_le_left _ _)
  have hR_ge_deg : Rdeg ≤ R := le_max_left _ _
  refine ⟨R, ε, hε_pos, hε_lt1, fun {V} _ H hreg t => ?_⟩
  classical
  obtain ⟨Q, _, _, H', cov, _, hgirth⟩ := exists_cover_girth_gt H (2 * R + J + 10)
  set m : ℕ := Fintype.card Q
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr cov.hm
  have hreg' : ∀ u' : V × Q, H'.degree u' = 3 := fun u' => by
    rw [cov.degree_eq u']; exact hreg (cov.proj u')
  have hsubmod : IsSubmodularBool (fun b : V × Q → Bool => (simpleCrossingCover H' b : ℝ)) :=
    isSubmodularBool_simpleCrossingCover H'
  have hsymm : IsSymmetricBool (fun b : V × Q → Bool => (simpleCrossingCover H' b : ℝ)) :=
    isSymmetricBool_simpleCrossingCover H'
  have hlift : (m : ℝ) *
      ∫ g, (simpleCrossingCover H (thresholdVec (waveScore H R ε g) t) : ℝ)
        ∂(piGauss (V ⊕ V)) =
      ∫ g, (simpleCrossingCover H'
        (thresholdVec (fun u' => ∑ z : V ⊕ V, waveRow H R ε (cov.proj u') z * g z) t) : ℝ)
        ∂(piGauss (V ⊕ V)) := by
    rw [← integral_const_mul]
    congr 1; ext g
    have hcomp : thresholdVec (fun u' => ∑ z : V ⊕ V, waveRow H R ε (cov.proj u') z * g z) t =
        (thresholdVec (waveScore H R ε g) t) ∘ cov.proj := by
      ext u'; rfl
    rw [hcomp, simpleCrossingCover_lift_eq cov, Nat.cast_mul]
  have hcmp :
      ∫ g, (simpleCrossingCover H'
        (thresholdVec (fun u' => ∑ z : V ⊕ V, waveRow H R ε (cov.proj u') z * g z) t) : ℝ)
        ∂(piGauss (V ⊕ V)) ≤
      ∫ g', (simpleCrossingCover H' (thresholdVec (waveScore H' R ε g') t) : ℝ)
        ∂(piGauss ((V × Q) ⊕ (V × Q))) :=
    integral_threshold_le_of_cov_le hsubmod
      (waveRow H' R ε) (fun u' => waveRow H R ε (cov.proj u'))
      (fun u' => sum_sq_waveRow_eq_one H' hreg' R hε_pos.le hε_lt1.le u')
      (fun u' => sum_sq_waveRow_eq_one H hreg R hε_pos.le hε_lt1.le (cov.proj u'))
      (fun u' v' hne => waveRow_cov_cover_le_base cov R hε_pos.le hε_lt1.le hne) t
  have hzero :
      ∫ g', (simpleCrossingCover H' (thresholdVec (waveScore H' R ε g') t) : ℝ)
        ∂(piGauss ((V × Q) ⊕ (V × Q))) ≤
      ∫ g', (simpleCrossingCover H' (thresholdVec (waveScore H' R ε g') 0) : ℝ)
        ∂(piGauss ((V × Q) ⊕ (V × Q))) :=
    integral_threshold_le_zero hsubmod hsymm (waveRow H' R ε)
      (fun u' => sum_sq_waveRow_eq_one H' hreg' R hε_pos.le hε_lt1.le u') t
  let μ' := piGauss ((V × Q) ⊕ (V × Q))
  let bt : ((V × Q) ⊕ (V × Q) → ℝ) → (V × Q → Bool) :=
    fun g' => thresholdVec (waveScore H' R ε g') 0
  have hbt_meas : Measurable bt :=
    measurable_thresholdVec (measurable_pi_iff.mpr fun u' => by unfold waveScore; fun_prop)
      (fun _ => 0) measurable_const
  have hint_cov : Integrable (fun g' => (simpleCrossingCover H' (bt g') : ℝ)) μ' :=
    Integrable.of_bound
      (((Measurable.of_discrete (f := fun b : V × Q → Bool =>
        (simpleCrossingCover H' b : ℝ))).comp hbt_meas).aestronglyMeasurable)
      (Fintype.card (V × Q) : ℝ)
      (ae_of_all _ fun g' => by
        rw [Real.norm_eq_abs, Nat.abs_cast]
        exact_mod_cast simpleCrossingCover_le_card (isSimpleCrossingCover_univ H' (bt g')))
  have hint_dir : ∀ j : ℕ,
      Integrable (fun g' => (dirNBCount (crossingGraph H' (bt g')) j : ℝ)) μ' := fun j =>
    Integrable.of_bound
      (((Measurable.of_discrete (f := fun b : V × Q → Bool =>
        (dirNBCount (crossingGraph H' b) j : ℝ))).comp hbt_meas).aestronglyMeasurable)
      (Fintype.card (Fin (j + 1) → V × Q) : ℝ)
      (ae_of_all _ fun g' => by
        rw [Real.norm_eq_abs, Nat.abs_cast]
        exact_mod_cast Finset.card_filter_le _ _)
  have hint_deg : Integrable (fun g' => ((degThreeSet (crossingGraph H' (bt g'))).card : ℝ)) μ' :=
    Integrable.of_bound
      (((Measurable.of_discrete (f := fun b : V × Q → Bool =>
        ((degThreeSet (crossingGraph H' b)).card : ℝ))).comp hbt_meas).aestronglyMeasurable)
      (Fintype.card (V × Q) : ℝ)
      (ae_of_all _ fun g' => by
        rw [Real.norm_eq_abs, Nat.abs_cast]
        exact_mod_cast Finset.card_filter_le _ _)
  have hpt : ∀ g' : (V × Q) ⊕ (V × Q) → ℝ,
      2 * (simpleCrossingCover H' (bt g') : ℝ) ≤
        (∑ j ∈ Finset.Icc 1 J,
          (-1 : ℝ) ^ (j + 1) * (dirNBCount (crossingGraph H' (bt g')) j : ℝ)) +
          (altErrConst J : ℝ) * ((degThreeSet (crossingGraph H' (bt g'))).card : ℝ) := by
    intro g'
    have hdet := two_mul_simpleCrossingCover_le_alternating H'
      (fun v' => (hreg' v').le) (bt g') J hJ
    have hcast : ((2 * simpleCrossingCover H' (bt g') : ℤ) : ℝ) ≤
        (((∑ j ∈ Finset.Icc 1 J,
            (-1 : ℤ) ^ (j + 1) * (dirNBCount (crossingGraph H' (bt g')) j : ℤ)) +
          (altErrConst J * (degThreeSet (crossingGraph H' (bt g'))).card : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast hdet
    push_cast at hcast
    exact hcast
  have hrhs_int : Integrable (fun g' =>
      (∑ j ∈ Finset.Icc 1 J,
          (-1 : ℝ) ^ (j + 1) * (dirNBCount (crossingGraph H' (bt g')) j : ℝ)) +
        (altErrConst J : ℝ) * ((degThreeSet (crossingGraph H' (bt g'))).card : ℝ)) μ' :=
    (integrable_finsetSum _ fun j _ => (hint_dir j).const_mul _).add
      (hint_deg.const_mul _)
  have hE_alt : 2 * ∫ g', (simpleCrossingCover H' (bt g') : ℝ) ∂μ' ≤
      (∑ j ∈ Finset.Icc 1 J,
          (-1 : ℝ) ^ (j + 1) * ∫ g', (dirNBCount (crossingGraph H' (bt g')) j : ℝ) ∂μ') +
        (altErrConst J : ℝ) *
          ∫ g', ((degThreeSet (crossingGraph H' (bt g'))).card : ℝ) ∂μ' := by
    have hm := integral_mono (hint_cov.const_mul 2) hrhs_int hpt
    rw [integral_const_mul, integral_add
        (integrable_finsetSum _ fun j _ => (hint_dir j).const_mul _)
        (hint_deg.const_mul _),
      integral_finsetSum _ fun j _ => (hint_dir j).const_mul _,
      integral_const_mul] at hm
    simp_rw [integral_const_mul] at hm
    exact hm
  have hE_dir : ∀ j ∈ Finset.Icc 1 J,
      (-1 : ℝ) ^ (j + 1) * ∫ g', (dirNBCount (crossingGraph H' (bt g')) j : ℝ) ∂μ' ≤
        ((-1 : ℝ) ^ (j + 1) * ar2AltProb j + ηwalk) *
          (3 * (2 : ℝ) ^ (j - 1) * (Fintype.card (V × Q) : ℝ)) := by
    intro j hj
    let Wj : Finset (Fin (j + 1) → V × Q) := Finset.univ.filter fun w => IsNBWalk H' j w
    have hcount_eq : ∀ g', (dirNBCount (crossingGraph H' (bt g')) j : ℝ) =
        ∑ w ∈ Wj, if IsNBWalk (crossingGraph H' (bt g')) j w then (1 : ℝ) else 0 := by
      intro g'
      have hsub : (Finset.univ.filter fun w : Fin (j + 1) → V × Q =>
            IsNBWalk (crossingGraph H' (bt g')) j w) =
          Wj.filter fun w => IsNBWalk (crossingGraph H' (bt g')) j w := by
        ext w
        simp only [Wj, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun hw => ⟨((isNBWalk_crossingGraph_iff H' (bt g') j w).mp hw).1, hw⟩,
          fun hw => hw.2⟩
      change ((Finset.univ.filter _).card : ℝ) = _
      rw [hsub, Finset.card_filter, Nat.cast_sum]
      exact Finset.sum_congr rfl fun w _ => by split_ifs <;> simp
    have hmeas_w : ∀ w : Fin (j + 1) → V × Q,
        MeasurableSet {g' | IsNBWalk (crossingGraph H' (bt g')) j w} := fun w =>
      (MeasurableSet.of_discrete (s := {b : V × Q → Bool |
        IsNBWalk (crossingGraph H' b) j w})).preimage hbt_meas
    have hint_w : ∀ w ∈ Wj, Integrable
        (fun g' => if IsNBWalk (crossingGraph H' (bt g')) j w then (1 : ℝ) else 0) μ' :=
      fun w _ => Integrable.of_bound
        (Measurable.ite (hmeas_w w) measurable_const measurable_const).aestronglyMeasurable
        1 (ae_of_all _ fun g' => by
          rw [Real.norm_eq_abs]; split_ifs <;> simp)
    have hE_eq : ∫ g', (dirNBCount (crossingGraph H' (bt g')) j : ℝ) ∂μ' =
        ∑ w ∈ Wj, μ'.real {g' | IsNBWalk (crossingGraph H' (bt g')) j w} := by
      simp_rw [hcount_eq]
      rw [integral_finsetSum Wj hint_w]
      refine Finset.sum_congr rfl fun w _ => ?_
      simpa [Set.indicator_apply] using integral_indicator_one (μ := μ') (hmeas_w w)
    rw [hE_eq, Finset.mul_sum]
    have hj_mem : (⟨j, hj⟩ : {k : ℕ // k ∈ Finset.Icc 1 J}) ∈ S := Finset.mem_univ _
    have hR_j : Rj ⟨j, hj⟩ ≤ R :=
      (Finset.le_sup hj_mem).trans (le_max_right _ _)
    have hε_j : ε ≤ εj ⟨j, hj⟩ :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (Finset.inf'_le εj hj_mem))
    have hle_sum : ∑ w ∈ Wj, (-1 : ℝ) ^ (j + 1) *
          μ'.real {g' | IsNBWalk (crossingGraph H' (bt g')) j w} ≤
        ∑ _w ∈ Wj, ((-1 : ℝ) ^ (j + 1) * ar2AltProb j + ηwalk) := by
      refine Finset.sum_le_sum fun w hw => ?_
      have hwb := (hεj ⟨j, hj⟩).2 H' hreg' R hR_j ε hε_pos hε_j
        (fun k h1 h2 => hgirth k h1 (by
          have hjJ : j ≤ J := (Finset.mem_Icc.mp hj).2
          have h2' : k ≤ 2 * R + j + 4 := h2
          omega))
        w (Finset.mem_filter.mp hw).2
      have hsign : |(-1 : ℝ) ^ (j + 1)| = 1 := by simp
      have habs : |(-1 : ℝ) ^ (j + 1) *
            μ'.real {g' | IsNBWalk (crossingGraph H' (bt g')) j w} -
          (-1 : ℝ) ^ (j + 1) * ar2AltProb j| ≤ ηwalk := by
        rw [← mul_sub, abs_mul, hsign, one_mul]; exact hwb
      linarith [le_abs_self ((-1 : ℝ) ^ (j + 1) *
        μ'.real {g' | IsNBWalk (crossingGraph H' (bt g')) j w} -
          (-1 : ℝ) ^ (j + 1) * ar2AltProb j), habs]
    have hcard_Wj : (Wj.card : ℝ) = 3 * (2 : ℝ) ^ (j - 1) * (Fintype.card (V × Q) : ℝ) := by
      have hc : Wj.card = dirNBCount H' j := rfl
      rw [hc, dirNBCount_cubic_eq H' hreg' (Finset.mem_Icc.mp hj).1]
      push_cast; ring
    calc ∑ w ∈ Wj, (-1 : ℝ) ^ (j + 1) *
            μ'.real {g' | IsNBWalk (crossingGraph H' (bt g')) j w}
        ≤ ∑ _w ∈ Wj, ((-1 : ℝ) ^ (j + 1) * ar2AltProb j + ηwalk) := hle_sum
      _ = (Wj.card : ℝ) * ((-1 : ℝ) ^ (j + 1) * ar2AltProb j + ηwalk) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((-1 : ℝ) ^ (j + 1) * ar2AltProb j + ηwalk) *
            (3 * (2 : ℝ) ^ (j - 1) * (Fintype.card (V × Q) : ℝ)) := by
          rw [hcard_Wj, mul_comm]
  have hE_deg : ∫ g', ((degThreeSet (crossingGraph H' (bt g'))).card : ℝ) ∂μ' ≤
      ηdeg * (Fintype.card (V × Q) : ℝ) := by
    have hcnt : ∀ g', ((degThreeSet (crossingGraph H' (bt g'))).card : ℝ) =
        ∑ v' : V × Q, if (crossingGraph H' (bt g')).degree v' = 3 then (1 : ℝ) else 0 := by
      intro g'
      simp only [degThreeSet, Finset.card_filter, Nat.cast_sum]
      exact Finset.sum_congr rfl fun v' _ => by split_ifs <;> simp
    have hmeas_v : ∀ v' : V × Q,
        MeasurableSet {g' | (crossingGraph H' (bt g')).degree v' = 3} := fun v' =>
      (MeasurableSet.of_discrete (s := {b : V × Q → Bool |
        (crossingGraph H' b).degree v' = 3})).preimage hbt_meas
    have hint_v : ∀ v' : V × Q, Integrable
        (fun g' => if (crossingGraph H' (bt g')).degree v' = 3 then (1 : ℝ) else 0) μ' :=
      fun v' => Integrable.of_bound
        (Measurable.ite (hmeas_v v') measurable_const measurable_const).aestronglyMeasurable
        1 (ae_of_all _ fun g' => by
          rw [Real.norm_eq_abs]; split_ifs <;> simp)
    simp_rw [hcnt]
    rw [integral_finsetSum Finset.univ fun v' _ => hint_v v']
    calc ∑ v' : V × Q, ∫ g',
            (if (crossingGraph H' (bt g')).degree v' = 3 then (1 : ℝ) else 0) ∂μ'
        = ∑ v' : V × Q, μ'.real {g' | (crossingGraph H' (bt g')).degree v' = 3} :=
            Finset.sum_congr rfl fun v' _ => by
              simpa [Set.indicator_apply] using integral_indicator_one (μ := μ') (hmeas_v v')
      _ ≤ ∑ _v' : V × Q, ηdeg := Finset.sum_le_sum fun v' _ =>
            hdeg_bd H' hreg' R hR_ge_deg ε hε_pos hε_le_deg
              (fun k h1 h2 => hgirth k h1 (by omega)) v'
      _ = ηdeg * (Fintype.card (V × Q) : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  have hsum_bd : 2 * ∫ g', (simpleCrossingCover H' (bt g') : ℝ) ∂μ' ≤
      (2 * alternatingWaveSum J + 2 * η) * (Fintype.card (V × Q) : ℝ) := by
    have hs1 : ∑ j ∈ Finset.Icc 1 J,
          (-1 : ℝ) ^ (j + 1) * ∫ g', (dirNBCount (crossingGraph H' (bt g')) j : ℝ) ∂μ' ≤
        ∑ j ∈ Finset.Icc 1 J, ((-1 : ℝ) ^ (j + 1) * ar2AltProb j + ηwalk) *
          (3 * (2 : ℝ) ^ (j - 1) * (Fintype.card (V × Q) : ℝ)) :=
      Finset.sum_le_sum hE_dir
    have hs1_eq : ∑ j ∈ Finset.Icc 1 J, ((-1 : ℝ) ^ (j + 1) * ar2AltProb j + ηwalk) *
          (3 * (2 : ℝ) ^ (j - 1) * (Fintype.card (V × Q) : ℝ)) =
        (2 * alternatingWaveSum J + η) * (Fintype.card (V × Q) : ℝ) := by
      have hsep : ∀ j : ℕ, ((-1 : ℝ) ^ (j + 1) * ar2AltProb j + ηwalk) *
            (3 * (2 : ℝ) ^ (j - 1) * (Fintype.card (V × Q) : ℝ)) =
          (2 * ((-1 : ℝ) ^ (j + 1) * (3 / 2) * (2 : ℝ) ^ (j - 1) * ar2AltProb j)) *
            (Fintype.card (V × Q) : ℝ) +
          (2 * ηwalk * ((3 / 2 : ℝ) * (2 : ℝ) ^ (j - 1))) *
            (Fintype.card (V × Q) : ℝ) := fun j => by ring
      simp_rw [hsep, Finset.sum_add_distrib, ← Finset.sum_mul]
      have ha1 : ∑ j ∈ Finset.Icc 1 J,
          2 * ((-1 : ℝ) ^ (j + 1) * (3 / 2) * (2 : ℝ) ^ (j - 1) * ar2AltProb j) =
          2 * alternatingWaveSum J := by
        rw [← Finset.mul_sum]; simp only [ar2AltProb_eq_altPathProb]; rfl
      have ha2 : ∑ j ∈ Finset.Icc 1 J,
          2 * ηwalk * ((3 / 2 : ℝ) * (2 : ℝ) ^ (j - 1)) =
          2 * ηwalk * Cwalk := by
        rw [← Finset.mul_sum]
      rw [ha1, ha2]
      have hcw : 2 * ηwalk * Cwalk = η := by
        dsimp only [ηwalk]; field_simp [hCwalk_pos.ne']
      rw [hcw]; ring
    have hs2 : (altErrConst J : ℝ) *
          ∫ g', ((degThreeSet (crossingGraph H' (bt g'))).card : ℝ) ∂μ' ≤
        η * (Fintype.card (V × Q) : ℝ) := by
      calc (altErrConst J : ℝ) *
              ∫ g', ((degThreeSet (crossingGraph H' (bt g'))).card : ℝ) ∂μ'
          ≤ (altErrConst J : ℝ) * (ηdeg * (Fintype.card (V × Q) : ℝ)) :=
            mul_le_mul_of_nonneg_left hE_deg (Nat.cast_nonneg _)
        _ = η * (Fintype.card (V × Q) : ℝ) := by
            have hne : (altErrConst J : ℝ) ≠ 0 := (Nat.cast_pos.mpr (by omega)).ne'
            dsimp only [ηdeg]; field_simp [hne]
    rw [hs1_eq] at hs1
    linarith [hE_alt, hs1, hs2]
  have hcover_le : ∫ g', (simpleCrossingCover H' (bt g') : ℝ) ∂μ' ≤
      (alternatingWaveSum J + η) * ((m : ℝ) * (Fintype.card V : ℝ)) := by
    have hcard : (Fintype.card (V × Q) : ℝ) = (m : ℝ) * (Fintype.card V : ℝ) := by
      have := cov.card_vert_eq
      exact_mod_cast this
    rw [← hcard]
    linarith [hsum_bd]
  have hmul : (m : ℝ) *
      ∫ g, (simpleCrossingCover H (thresholdVec (waveScore H R ε g) t) : ℝ)
        ∂(piGauss (V ⊕ V)) ≤
      (m : ℝ) * ((alternatingWaveSum J + η) * (Fintype.card V : ℝ)) := by
    calc (m : ℝ) * _ = _ := hlift
      _ ≤ _ := hcmp
      _ ≤ _ := hzero
      _ ≤ (alternatingWaveSum J + η) * ((m : ℝ) * (Fintype.card V : ℝ)) := hcover_le
      _ = (m : ℝ) * ((alternatingWaveSum J + η) * (Fintype.card V : ℝ)) := by ring
  exact le_of_mul_le_mul_left hmul hm_pos

end MainExpectation

end Cslib.Circuits.Frontier.CrossingCover
