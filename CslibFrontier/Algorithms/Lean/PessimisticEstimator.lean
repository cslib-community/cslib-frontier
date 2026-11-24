/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Product.ConditionalExpectation

/-!
# Method of conditional expectations on a finite product space

`Cslib.PessimisticEstimator.greedy` in
`CslibFrontier.Foundations.Combinatorics.PessimisticEstimator` models binary pessimistic-estimator
rounds, and `CslibFrontier.Computability.PolyTime.PessimisticEstimator` certifies multi-tape Turing
polynomial-time computability of greedy derandomizers.

This module packages the pure method of conditional expectations over a general finite product space
`∀ i : ι, α i` (`ProductDerandomizer`): for each coordinate `i` in `order`, it evaluates the
conditional-expectation oracle `condExp (insert i fixed) (Function.update x i a)` across every
candidate `a ∈ choices i` and selects a minimizing coordinate value. When `condExp` agrees with
`PMF.condExpect p f` through a monotone map `M → ℝ`, `derandomize_spec` proves
`f (D.derandomize order init) ≤ E_{y ∼ pi p}[f y]`.

## Main definitions

* `Cslib.Algorithms.Lean.PessimisticEstimator.ProductDerandomizer`: finite-product
  conditional-expectation derandomizer.
* `Cslib.Algorithms.Lean.PessimisticEstimator.ProductDerandomizer.scanCandidates`, `stepCoord`,
  `runFrom`, `derandomize`: pure coordinate fixing over an explicit round order.

## Main results

* `Cslib.Algorithms.Lean.PessimisticEstimator.ProductDerandomizer.derandomize_spec`: deterministic
  expectation guarantee `f (D.derandomize order init) ≤ E[f]` over finite product distributions
  `PMF.pi p`.
-/

public section

open scoped BigOperators

namespace Cslib.Algorithms.Lean.PessimisticEstimator

open Cslib.Probability

/-- Deterministic conditional-expectation derandomizer over `∀ i : ι, α i`: at each coordinate `i`,
evaluates `condExp (insert i fixed) (Function.update x i a)` across every candidate `a ∈ choices i`
and picks a value minimizing the returned conditional expectation. -/
structure ProductDerandomizer (ι : Type) (α : ι → Type) (M : Type) where
  /-- Candidate list of domain values tested at coordinate `i`. -/
  choices : (i : ι) → List (α i)
  /-- Conditional-expectation oracle given fixed coordinates and current assignment. -/
  condExp : Finset ι → (∀ i, α i) → M

namespace ProductDerandomizer

section Execution

variable {ι : Type} [DecidableEq ι] {α : ι → Type} {M : Type}
  [LE M] [DecidableRel (α := M) (· ≤ ·)]
  (D : ProductDerandomizer ι α M)

/-- Evaluate candidates in `cs` starting from best pair `(bestA, bestV)`. -/
@[expose] def scanCandidates (fixedNext : Finset ι) (x : ∀ i, α i) (i : ι) :
    List (α i) → α i × M → α i × M
  | [], best => best
  | a :: cs, best =>
      let val := D.condExp fixedNext (Function.update x i a)
      scanCandidates fixedNext x i cs (if val ≤ best.2 then (a, val) else best)

/-- Choose the best value for coordinate `i` among `D.choices i` (leaving `x` unchanged if
`D.choices i` is empty). -/
@[expose] def stepCoord (state : Finset ι × (∀ i, α i)) (i : ι) :
    Finset ι × (∀ i, α i) :=
  let fixedNext := insert i state.1
  match D.choices i with
  | [] => (fixedNext, state.2)
  | a₀ :: cs =>
      let v₀ := D.condExp fixedNext (Function.update state.2 i a₀)
      let best := D.scanCandidates fixedNext state.2 i cs (a₀, v₀)
      (fixedNext, Function.update state.2 i best.1)

/-- Run coordinate fixing along `order` starting from `(fixed, x)`. -/
@[expose] def runFrom (order : List ι) (fixed : Finset ι) (x : ∀ i, α i) :
    Finset ι × (∀ i, α i) :=
  order.foldl D.stepCoord (fixed, x)

/-- Deterministic assignment produced by fixing all coordinates in `order` from `∅`. -/
@[expose] def derandomize (order : List ι) (init : ∀ i, α i) : ∀ i, α i :=
  (D.runFrom order ∅ init).2

end Execution

section Correctness

variable {ι : Type} [DecidableEq ι] {α : ι → Type} {M : Type} [LinearOrder M]
  (D : ProductDerandomizer ι α M)

private theorem scanCandidates_spec (fixedNext : Finset ι) (x : ∀ i, α i) (i : ι) :
    ∀ (cs : List (α i)) (best : α i × M),
      best.2 = D.condExp fixedNext (Function.update x i best.1) →
      (D.scanCandidates fixedNext x i cs best).2 =
          D.condExp fixedNext
            (Function.update x i (D.scanCandidates fixedNext x i cs best).1) ∧
        (D.scanCandidates fixedNext x i cs best).2 ≤ best.2 ∧
        ∀ a ∈ cs, (D.scanCandidates fixedNext x i cs best).2 ≤
          D.condExp fixedNext (Function.update x i a)
  | [], _, hbest => ⟨hbest, le_rfl, by simp⟩
  | a :: cs, best, hbest => by
    let val := D.condExp fixedNext (Function.update x i a)
    let next : α i × M := if val ≤ best.2 then (a, val) else best
    have hnext_eq : next.2 = D.condExp fixedNext (Function.update x i next.1) := by
      dsimp only [next, val]
      split_ifs <;> simp [hbest]
    have hnext_le_best : next.2 ≤ best.2 := by
      dsimp only [next]
      split_ifs with hle
      · exact hle
      · exact le_rfl
    have hnext_le_a : next.2 ≤ val := by
      dsimp only [next]
      split_ifs with hle
      · exact le_rfl
      · exact le_of_not_ge hle
    obtain ⟨heq_out, hle_next, hforall_cs⟩ := scanCandidates_spec fixedNext x i cs next hnext_eq
    refine ⟨heq_out, hle_next.trans hnext_le_best, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact hle_next.trans hnext_le_a
    · exact hforall_cs b hb'

private theorem runFrom_spec [Fintype ι] [∀ i, Fintype (α i)]
    (p : ∀ i, PMF (α i)) (f : (∀ i, α i) → ℝ)
    {toReal : M → ℝ} (hmono : Monotone toReal)
    (heval : ∀ fixed x, toReal (D.condExp fixed x) = PMF.condExpect p f fixed x)
    (hchoices : ∀ i a, a ∈ (p i).support → a ∈ D.choices i) :
    ∀ (order : List ι) (fixed : Finset ι) (x : ∀ i, α i),
      order.Nodup → (∀ j ∈ order, j ∉ fixed) →
      (D.runFrom order fixed x).1 = fixed ∪ order.toFinset ∧
        PMF.condExpect p f (D.runFrom order fixed x).1
          (D.runFrom order fixed x).2 ≤ PMF.condExpect p f fixed x
  | [], fixed, x, _, _ => by
    simp [runFrom]
  | i :: rs, fixed, x, hnd, hdisj => by
    obtain ⟨hi_rs, hnd_rs⟩ := List.nodup_cons.mp hnd
    have hi_fix : i ∉ fixed := hdisj i List.mem_cons_self
    obtain ⟨a_star, ha_supp, ha_le⟩ := PMF.exists_condExpect_insert_le p f hi_fix x
    have ha_mem : a_star ∈ D.choices i := hchoices i a_star ha_supp
    cases hcs : D.choices i with
    | nil =>
      rw [hcs] at ha_mem
      cases ha_mem
    | cons a₀ cs =>
      let fixedNext := insert i fixed
      let v₀ := D.condExp fixedNext (Function.update x i a₀)
      obtain ⟨heq_best, hle_v₀, hle_cs⟩ := scanCandidates_spec D fixedNext x i cs (a₀, v₀) rfl
      set best := D.scanCandidates fixedNext x i cs (a₀, v₀)
      have hbest_le_star : best.2 ≤ D.condExp fixedNext (Function.update x i a_star) := by
        rw [hcs] at ha_mem
        rcases List.mem_cons.mp ha_mem with rfl | hmem_cs
        · exact hle_v₀
        · exact hle_cs a_star hmem_cs
      have hstep_exp : PMF.condExpect p f fixedNext (Function.update x i best.1) ≤
          PMF.condExpect p f fixed x := by
        have hm := hmono hbest_le_star
        rw [heq_best, heval, heval] at hm
        exact hm.trans ha_le
      have hdisj_next : ∀ j ∈ rs, j ∉ fixedNext := by
        intro j hj hmem
        rcases Finset.mem_insert.mp hmem with rfl | hj_fix
        · exact hi_rs hj
        · exact hdisj j (List.mem_cons_of_mem i hj) hj_fix
      have hstep_eq : D.stepCoord (fixed, x) i = (fixedNext, Function.update x i best.1) := by
        simp [stepCoord, hcs, fixedNext, best, v₀]
      obtain ⟨hset_end, hexp_end⟩ :=
        runFrom_spec p f hmono heval hchoices rs fixedNext
          (Function.update x i best.1) hnd_rs hdisj_next
      have hrun : D.runFrom (i :: rs) fixed x =
          D.runFrom rs fixedNext (Function.update x i best.1) := by
        simp [runFrom, hstep_eq]
      refine ⟨?_, ?_⟩
      · rw [hrun, hset_end]
        ext j
        simp [fixedNext]
      · rw [hrun]
        exact hexp_end.trans hstep_exp

/-- **Method of conditional expectations on a finite product space**: if `order` visits every
coordinate without repetition, `D.choices i` covers `(p i).support`, and `D.condExp` computes
`PMF.condExpect p f` (via monotone `toReal : M → ℝ`), then `D.derandomize order init` returns a
deterministic point `x*` with `f x* ≤ E_{y ∼ pi p}[f y]`. -/
theorem derandomize_spec [Fintype ι] [∀ i, Fintype (α i)]
    (p : ∀ i, PMF (α i)) (f : (∀ i, α i) → ℝ)
    {toReal : M → ℝ} (hmono : Monotone toReal)
    (heval : ∀ fixed x, toReal (D.condExp fixed x) = PMF.condExpect p f fixed x)
    (hchoices : ∀ i a, a ∈ (p i).support → a ∈ D.choices i)
    (order : List ι) (hnd : order.Nodup) (hcov : ∀ i, i ∈ order) (init : ∀ i, α i) :
    f (D.derandomize order init) ≤ ∑ y, (PMF.pi p y).toReal * f y := by
  obtain ⟨hset, hexp⟩ :=
    runFrom_spec D p f hmono heval hchoices order ∅ init hnd (by simp)
  have huniv : (D.runFrom order ∅ init).1 = Finset.univ := by
    rw [hset]
    ext i
    simp [hcov i]
  rw [huniv, PMF.condExpect_univ, PMF.condExpect_empty] at hexp
  exact hexp

end Correctness

end ProductDerandomizer

end Cslib.Algorithms.Lean.PessimisticEstimator
