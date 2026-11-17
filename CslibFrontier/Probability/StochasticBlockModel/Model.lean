/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Sign
public import CslibFrontier.Probability.Distributional.Search
public import CslibFrontier.Probability.PMF.Coin
public import CslibFrontier.Probability.Product
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import CslibFrontier.Probability.PMF.EventBind
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The two-community stochastic block model

Conditioned on hidden Boolean labels `g`, distinct vertices are adjacent independently with
probability `p` when their labels agree and `q` otherwise. The labels need not be balanced.
`coinLaw` samples independent bits indexed by ordered pairs and `sample` reads only their upper
triangle. The unused bits give a simple finite product space without changing the graph law.

The graph law is invariant under swapping all labels. Accordingly, `searchProblem` reveals only
the graph and accepts exactly recovery up to that swap. Its prior on hidden labels is arbitrary;
the parameters `p` and `q` are fixed public parameters of the problem.

The shifted centered adjacency matrix is
`A - ((p+q)/2) (J-I) + ((p-q)/2) I`. Its mean is the rank-one matrix
`((p-q)/2) g gᵀ`, where Boolean labels are read as signs. This identity does not assume equal
community sizes. The mean-zero noise is represented by independent upper-triangular entries and
their transpose, for use with random-matrix concentration.

## Main results

* `graphLaw_not`: swapping every hidden label leaves the graph law unchanged.
* `sum_sample_adjMatrix`: the expected adjacency matrix has the prescribed block probabilities.
* `shiftedCenteredAdjacency_sample`: the shifted matrix is a rank-one signal plus centered noise.
* `searchProblem_failure_le_of_fixedLabels`: conditional recovery bounds hold under any prior.
-/

public section

open scoped unitInterval
open Finset

namespace Cslib.Probability.StochasticBlockModel

/-- Independent edge coins; only the strict upper triangle is observed. -/
abbrev Coins (n : ℕ) := (Fin n × Fin n) → Bool

/-- The edge probability for two vertices with the specified hidden labels. -/
@[expose] def edgeProbability {n : ℕ} (p q : I) (g : Fin n → Bool) (i j : Fin n) : I :=
  if g i = g j then p else q

/-- The midpoint of the within-community and between-community edge probabilities. -/
noncomputable abbrev midpoint (p q : I) : ℝ := ((p : ℝ) + q) / 2

/-- Half the difference between within-community and between-community edge probabilities. -/
noncomputable abbrev gap (p q : I) : ℝ := ((p : ℝ) - q) / 2

/-- The graph read from the independent upper-triangular edge bits. -/
@[expose] def sample {n : ℕ} (ω : Coins n) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ ω (min i j, max i j) = true
  symm := by
    constructor
    intro i j h
    simpa only [ne_comm, min_comm j i, max_comm j i] using h
  loopless := by constructor; intro i; simp

instance {n : ℕ} (ω : Coins n) : DecidableRel (sample ω).Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ ω (min i j, max i j) = true))

/-- Independent Bernoulli edge bits, conditioned on the hidden labels. -/
@[expose] noncomputable def coinLaw {n : ℕ} (p q : I) (g : Fin n → Bool) : PMF (Coins n) :=
  PMF.pi fun e => PMF.coin (edgeProbability p q g e.1 e.2)

/-- The conditional graph law of the two-community stochastic block model. -/
@[expose] noncomputable def graphLaw {n : ℕ} (p q : I) (g : Fin n → Bool) :
    PMF (SimpleGraph (Fin n)) :=
  (coinLaw p q g).map sample

/-- Expected adjacency entries, with zero diagonal. -/
@[expose] def meanAdjacency {n : ℕ} (p q : I) (g : Fin n → Bool) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then 0 else (edgeProbability p q g i j : ℝ)

/-- Independent upper-triangular centered edge entries. -/
@[expose] def upperNoise {n : ℕ} (p q : I) (g : Fin n → Bool) (ω : Coins n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i < j then BitString.bitVal ℝ (ω (i, j)) - edgeProbability p q g i j else 0

/-- The mean-zero symmetric noise in the adjacency matrix. -/
@[expose] def noise {n : ℕ} (p q : I) (g : Fin n → Bool) (ω : Coins n) :
    Matrix (Fin n) (Fin n) ℝ :=
  upperNoise p q g ω + (upperNoise p q g ω).transpose

/-- Adjacency centered by the midpoint of the two edge probabilities off the diagonal. -/
@[expose] noncomputable def centeredAdjacency {n : ℕ} (p q : I) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : Matrix (Fin n) (Fin n) ℝ :=
  G.adjMatrix ℝ - midpoint p q • (Matrix.of (fun _ _ => 1) - 1)

/-- Add `gap p q` to the diagonal of the centered adjacency matrix, so its mean is rank one. -/
@[expose] noncomputable def shiftedCenteredAdjacency {n : ℕ} (p q : I) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : Matrix (Fin n) (Fin n) ℝ :=
  centeredAdjacency p q G + gap p q • 1

variable {n : ℕ} (p q : I) (g : Fin n → Bool)

/-- Edge probabilities are symmetric in their vertices. -/
theorem edgeProbability_comm (i j : Fin n) :
    edgeProbability p q g i j = edgeProbability p q g j i := by
  simp only [edgeProbability, eq_comm]

/-- Swapping all labels preserves each edge probability. -/
@[simp] theorem edgeProbability_not (i j : Fin n) :
    edgeProbability p q (fun v => !g v) i j = edgeProbability p q g i j := by
  simp [edgeProbability]

/-- Swapping all hidden labels leaves the conditional graph law unchanged. -/
theorem graphLaw_not : graphLaw p q (fun v => !g v) = graphLaw p q g := by
  simp only [graphLaw, coinLaw, edgeProbability_not]

private theorem edgeProbability_min_max (i j : Fin n) :
    edgeProbability p q g (min i j) (max i j) = edgeProbability p q g i j := by
  rcases le_total i j with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, edgeProbability_comm]

/-- Off the diagonal the sampled adjacency reads its single upper-triangular edge bit. -/
theorem sample_adjMatrix_of_ne (ω : Coins n) {i j : Fin n} (hij : i ≠ j) :
    (sample ω).adjMatrix ℝ i j = BitString.bitVal ℝ (ω (min i j, max i j)) := by
  change (if i ≠ j ∧ ω (min i j, max i j) = true then 1 else 0) = _
  simp [hij, BitString.bitVal]

/-- The expected adjacency entry is the prescribed within-community or between-community
probability, and the diagonal is zero. -/
theorem sum_sample_adjMatrix (i j : Fin n) :
    ∑ ω, (coinLaw p q g ω).toReal * (sample ω).adjMatrix ℝ i j =
      meanAdjacency p q g i j := by
  by_cases hij : i = j
  · subst j
    simp [meanAdjacency]
  · simp only [sample_adjMatrix_of_ne _ hij, meanAdjacency, ite_eq_right hij, coinLaw]
    rw [PMF.sum_pi_mul_eval]
    simp [PMF.coin_apply_toReal, edgeProbability_min_max]

/-- The centered noise matrix is symmetric. -/
theorem noise_transpose (ω : Coins n) : (noise p q g ω).transpose = noise p q g ω := by
  simp [noise, Matrix.transpose_add, add_comm]

/-- Centered noise has zero diagonal. -/
@[simp] theorem noise_diag (ω : Coins n) (i : Fin n) : noise p q g ω i i = 0 := by
  simp [noise, upperNoise]

/-- An off-diagonal noise entry is its edge indicator minus its edge probability. -/
theorem noise_of_ne (ω : Coins n) {i j : Fin n} (hij : i ≠ j) :
    noise p q g ω i j =
      BitString.bitVal ℝ (ω (min i j, max i j)) - edgeProbability p q g i j := by
  rcases lt_or_gt_of_ne hij with h | h
  · simp [noise, upperNoise, h, not_lt_of_ge h.le, min_eq_left h.le, max_eq_right h.le]
  · simp [noise, upperNoise, h, not_lt_of_ge h.le, min_eq_right h.le, max_eq_left h.le,
      edgeProbability_comm p q g j i]

/-- The independent-entry representation is exactly adjacency minus its expectation. -/
theorem noise_eq_sub_mean (ω : Coins n) :
    noise p q g ω = (sample ω).adjMatrix ℝ - meanAdjacency p q g := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [meanAdjacency]
  · rw [Matrix.sub_apply, noise_of_ne p q g ω hij, sample_adjMatrix_of_ne ω hij]
    simp [meanAdjacency, hij]

/-- The expected off-diagonal edge probability is midpoint plus the label-product signal. -/
theorem edgeProbability_eq_midpoint_add_gap (i j : Fin n) :
    (edgeProbability p q g i j : ℝ) =
      midpoint p q + gap p q * (BitString.signVal (g i) * BitString.signVal (g j)) := by
  rw [BitString.signVal_mul_signVal]
  by_cases h : g i = g j <;> simp [edgeProbability, h, midpoint, gap] <;> ring

/-- The shifted centered adjacency matrix consists of a rank-one label signal and centered
independent-edge noise. No balance assumption on the two label classes is needed. -/
theorem shiftedCenteredAdjacency_sample (ω : Coins n) :
    shiftedCenteredAdjacency p q (sample ω) =
      gap p q • Matrix.vecMulVec (fun i => BitString.signVal (g i))
        (fun i => BitString.signVal (g i)) + noise p q g ω := by
  rw [noise_eq_sub_mean]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [shiftedCenteredAdjacency, centeredAdjacency, meanAdjacency,
      Matrix.vecMulVec, BitString.signVal_mul_self]
  · simp only [shiftedCenteredAdjacency, centeredAdjacency, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.one_apply, hij, ite_false,
      Matrix.vecMulVec, smul_eq_mul, meanAdjacency, sub_zero, mul_zero, add_zero]
    rw [edgeProbability_eq_midpoint_add_gap]
    ring

/-- Centering and the scalar diagonal shift preserve symmetry. -/
theorem shiftedCenteredAdjacency_transpose (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (shiftedCenteredAdjacency p q G).transpose = shiftedCenteredAdjacency p q G := by
  simp [shiftedCenteredAdjacency, centeredAdjacency, Matrix.transpose_sub,
    Matrix.transpose_add, Matrix.transpose_smul]

/-- Every entry of the shifted centered matrix has absolute value at most one. -/
theorem abs_shiftedCenteredAdjacency_le_one (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (i j : Fin n) : |shiftedCenteredAdjacency p q G i j| ≤ 1 := by
  have hp₀ := p.2.1
  have hp₁ := p.2.2
  have hq₀ := q.2.1
  have hq₁ := q.2.2
  by_cases hij : i = j
  · subst j
    rw [abs_le]
    constructor <;>
      simp [shiftedCenteredAdjacency, centeredAdjacency, gap] <;> linarith
  · rw [abs_le]
    constructor <;> by_cases hadj : G.Adj i j <;>
      simp [shiftedCenteredAdjacency, centeredAdjacency, hij, hadj, midpoint] <;> linarith

/-- A hidden-label state and the graph it generates. -/
structure Instance (n : ℕ) where
  /-- The latent community label of every vertex. -/
  labels : Fin n → Bool
  /-- The observed graph. -/
  graph : SimpleGraph (Fin n)

/-- Draw labels from a supplied prior, then their conditional stochastic block graph. -/
@[expose] noncomputable def instanceDistribution (prior : PMF (Fin n → Bool)) :
    PMF (Instance n) := do
  let labels ← prior
  let graph ← graphLaw p q labels
  pure ⟨labels, graph⟩

/-- Recover all hidden community labels up to their global swap. Only the graph is observed. -/
@[expose] noncomputable def searchProblem (prior : PMF (Fin n → Bool)) :
    DistributionalSearchProblem (Instance n) (SimpleGraph (Fin n)) (Fin n → Bool) where
  distribution := instanceDistribution p q prior
  observe := Instance.graph
  accepts state answer := answer = state.labels ∨ answer = fun i => !state.labels i

/-- A uniform conditional failure bound for every hidden labeling transfers to any prior on
those labels. This is the hidden-state search experiment, with no labels given to the solver. -/
theorem searchProblem_failure_le_of_fixedLabels
    (prior : PMF (Fin n → Bool)) (solve : SimpleGraph (Fin n) → Fin n → Bool)
    {error : ℝ} (herror : 0 ≤ error)
    (hsolve : ∀ labels : Fin n → Bool,
      ((coinLaw p q labels).toOuterMeasure {ω |
        ¬ (solve (sample ω) = labels ∨ solve (sample ω) = fun i => !labels i)}).toReal ≤ error) :
    ((searchProblem p q prior).experiment (fun G => PMF.pure (solve G)) false).toReal ≤
      error := by
  rw [DistributionalSearchProblem.experiment_pure_false]
  have h := PMF.toOuterMeasure_bind_failure_toReal_le prior
    (fun labels => (graphLaw p q labels).map fun graph => (⟨labels, graph⟩ : Instance n))
    Set.univ {state : Instance n |
      ¬ (solve state.graph = state.labels ∨ solve state.graph = fun i => !state.labels i)}
    herror (fun labels _ _ => by
      rw [PMF.toOuterMeasure_map_apply, graphLaw, PMF.toOuterMeasure_map_apply]
      exact hsolve labels)
  simpa only [Set.compl_univ, MeasureTheory.measure_empty, ENNReal.toReal_zero, zero_add,
    searchProblem, instanceDistribution, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.map, Function.comp_def] using h

end Cslib.Probability.StochasticBlockModel
