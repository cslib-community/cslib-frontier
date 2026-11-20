/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.Replicable.Basic
public import CslibFrontier.Probability.CorrelatedSampling.Grid
public import CslibFrontier.Probability.MoserTardos.Coupling
import CslibFrontier.Foundations.Probability.InfinitePi
import CslibFrontier.Probability.MoserTardos.TotalVariation
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.Product

/-!
# Replicable constraint solving by Moser–Tardos

A learner sees a dataset `S` and must output an assignment avoiding every bad event `A i`, where
the variables are to be sampled from distributions `P̂ S v` estimated from the data. Running the
Moser–Tardos algorithm with samples drawn by correlated sampling from a shared seed makes the
output *replicable*: two runs on independent datasets, sharing the seed, give the same output
except with probability `4 ∑ v, E_{S, S'} d_TV(P̂ S v, P̂ S' v)`.

The replicability interface `Cslib.MachineLearning.Replicable.Algorithm` takes the shared seed
from a `PMF`, so the seed is finite here:

* The estimated distributions are grid distributions with a common denominator `L`
  (`Cslib.Probability.CorrelatedSampling.GridDist`), for example empirical frequencies. Each
  table entry is sampled by the grid form of Holenstein's protocol
  (`Cslib.Probability.CorrelatedSampling.gridSample`) from its own uniform enumeration.
* The run is **budgeted**: it reads only the first `B + 1` samples of each variable, and outputs
  the current assignment if the rule has stopped after `B` steps and `none` (a timeout)
  otherwise (`budgetedOutput`).

The algorithm is `budgetedMoserTardos`. Its disagreement bound
(`disagreeProb_budgetedMoserTardos_le`) needs the local-lemma hypothesis `e p (d + 1) ≤ 1` for
every estimate, and does not depend on the budget, the number of events or the dependency degree:
the timeout output is itself replicated. A rule that stops only when no event occurs never
outputs a bad assignment (`budgetedOutput_eq_some`), so the budget enters only through the
timeout probability.

The statement and its proof route are original (cslib-frontier issue #6718).

## Main definitions

* `Cslib.MachineLearning.Replicable.budgetedOutput`: the output of a run budgeted to `B` steps.
* `Cslib.MachineLearning.Replicable.BudgetSeed`, `Cslib.MachineLearning.Replicable.seedTable`:
  the shared seed and the table it gives for a family of grid distributions.
* `Cslib.MachineLearning.Replicable.budgetedMoserTardos`: the replicable algorithm.

## Main results

* `Cslib.MachineLearning.Replicable.budgetedOutput_eq_some`: outputs avoid every event.
* `Cslib.MachineLearning.Replicable.seedTable_disagree_le`: for fixed estimates `P` and `Q`, two
  runs sharing the seed disagree with probability at most `4 ∑ v, d_TV(P v, Q v)`.
* `Cslib.MachineLearning.Replicable.disagreeProb_budgetedMoserTardos_le`: the replicability bound.

## Implementation notes

`seedTable_disagree_le` transfers the first-disagreement bound
(`Cslib.Probability.MoserTardos.coupledTable_diverge_le_two_mul`) from the infinite coupled table
to the finite seed. The budgeted outputs depend only on the samples with index at most `B`, and
the laws of those samples under the seed and under the coupled table are the same product.

## References

* [R. A. Moser, G. Tardos, *A constructive proof of the general Lovász Local Lemma*]
  [MoserTardos2010]
* [T. Holenstein, *Parallel repetition: simplifications and the no-signaling case*]
  [Holenstein2009]
* [ImpagliazzoLeiPitassiSorrell2022]
-/

public section

namespace Cslib.MachineLearning.Replicable

open Finset MeasureTheory Cslib.Probability.MoserTardos Cslib.Probability.CorrelatedSampling
open scoped ENNReal Cslib.Probability.PMF

section Budgeted

variable {V ι : Type*} [DecidableEq V] {α : V → Type*} (vbl : ι → Finset V)
  (r : List ι → (∀ v, α v) → Option ι) (B : ℕ)

/-- The output of the run of `historyRule r` on the table `T` **budgeted** to `B` steps: the
current assignment if the rule has stopped after `B` steps, and `none` (a timeout) otherwise. -/
def budgetedOutput (T : ∀ p : V × ℕ, α p.1) : Option (∀ v, α v) :=
  match r (run (historyRule vbl r) T B) (current vbl T (run (historyRule vbl r) T B)) with
  | none => some (current vbl T (run (historyRule vbl r) T B))
  | some _ => none

variable {vbl r B}

/-- A rule that stops only when no event occurs outputs only assignments avoiding every event. -/
theorem budgetedOutput_eq_some {A : ι → Set (∀ v, α v)}
    (hstop : ∀ w a, r w a = none → ∀ i, a ∉ A i) {T : ∀ p : V × ℕ, α p.1} {a : ∀ v, α v}
    (h : budgetedOutput vbl r B T = some a) (i : ι) : a ∉ A i := by
  unfold budgetedOutput at h
  split at h
  · cases h
    exact hstop _ _ ‹_› i
  · cases h

/-- The budgeted output depends only on the entries `(v, k)` with `k ≤ B`. -/
theorem dependsOn_budgetedOutput [Fintype V] :
    DependsOn (budgetedOutput vbl r B (α := α))
      ((univ ×ˢ range (B + 1) : Finset (V × ℕ)) : Set (V × ℕ)) := by
  intro T T' h
  obtain ⟨h₁, h₂⟩ := Prod.ext_iff.1 (dependsOn_run_current (vbl := vbl) (r := r) B h)
  simp only at h₁ h₂
  unfold budgetedOutput
  rw [h₂, h₁]

/-- Two coupled runs that do not diverge have the same budgeted output. -/
theorem budgetedOutput_eq_of_not_diverge {T : ∀ p : V × ℕ, α p.1 × α p.1}
    (hT : ¬Diverge vbl r T) :
    budgetedOutput vbl r B (fstTable T) = budgetedOutput vbl r B (sndTable T) := by
  simp only [Diverge, not_exists, not_or, not_not] at hT
  unfold budgetedOutput
  rw [(hT B).2, (hT B).1]

end Budgeted

section Seed

variable {V : Type*} [Fintype V] [DecidableEq V] {α : V → Type*} [∀ v, Fintype (α v)]
  [∀ v, DecidableEq (α v)] {L : ℕ} [NeZero L] (B : ℕ)

/-- The **shared seed** of the budgeted run: an enumeration of the cells of `α v × Fin L` for each
variable `v` and each of its first `B + 1` samples. -/
abbrev BudgetSeed (α : V → Type*) [∀ v, Fintype (α v)] (L B : ℕ) :=
  ∀ p : V × Fin (B + 1), Enumeration (α p.1 × Fin L)

/-- The table given by the seed `σ` for the grid distributions `P`: entry `(v, k)` is sampled from
`P v` by correlated sampling from the enumeration at `(v, min k B)`. A run budgeted to `B` steps
reads only the entries with `k ≤ B`. -/
def seedTable (P : ∀ v, GridDist (α v) L) (σ : BudgetSeed α L B) : ∀ p : V × ℕ, α p.1 :=
  fun p => gridSample (P p.1) (σ (p.1, ⟨min p.2 B, Nat.lt_succ_of_le (min_le_right _ _)⟩))

variable [∀ v, MeasurableSpace (α v)] [∀ v, MeasurableSingletonClass (α v)]

/-- **Replicable runs for fixed estimates (original).** Let `r` be a non-anticipating rule that
only selects occurring events. Suppose every event has at most `d` neighbours in `Γ` and
probability at most `p` under the product of the `P v`, with `e p (d + 1) ≤ 1`. Then two runs
budgeted to `B` steps, one with `P` and one with `Q`, reading the tables of one uniformly random
seed, give different outputs with probability at most `4 ∑ v, d_TV(P v, Q v)`. -/
theorem seedTable_disagree_le {ι : Type*} [Finite ι] (vbl : ι → Finset V)
    (r : List ι → (∀ v, α v) → Option ι) (P Q : ∀ v, GridDist (α v) L)
    (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) (Γ : ι → Finset ι)
    (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i) {d : ℕ}
    (hΓd : ∀ i, (Γ i).card ≤ d) {p : ℝ}
    (hP : ∀ i, (Measure.pi fun v => (P v).toPMF.toMeasure).real (A i) ≤ p)
    (hp : Real.exp 1 * p * (d + 1) ≤ 1) (hr : ∀ w a i, r w a = some i → a ∈ A i) :
    (Probability.PMF.uniformOfFintype (BudgetSeed α L B)).toOuterMeasure
        {σ | budgetedOutput vbl r B (seedTable B P σ) ≠ budgetedOutput vbl r B (seedTable B Q σ)} ≤
      ENNReal.ofReal (4 * ∑ v, dist (P v).toPMF (Q v).toPMF) := by
  classical
  set G : ∀ v, Enumeration (α v × Fin L) → α v × α v :=
    fun v σ => (gridSample (P v) σ, gridSample (Q v) σ)
  set κ : ∀ v, Measure (α v × α v) :=
    fun v => ((Probability.PMF.uniformOfFintype (Enumeration (α v × Fin L))).map (G v)).toMeasure
  have hκP : ∀ v, (κ v).map Prod.fst = (P v).toPMF.toMeasure := fun v => by
    rw [PMF.toMeasure_map (hf := measurable_fst), PMF.map_comp]
    exact congrArg PMF.toMeasure (map_gridSample (P v))
  have hdis : ∀ v, κ v {x | x.1 ≠ x.2} ≤ ENNReal.ofReal (2 * dist (P v).toPMF (Q v).toPMF) :=
    fun v => by
      rw [PMF.toMeasure_apply_eq_toOuterMeasure, PMF.toOuterMeasure_map_apply,
        ← ENNReal.ofReal_toReal (Probability.PMF.toOuterMeasure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal (gridSample_disagree_le (P v) (Q v))
  have hP' : ∀ i, (Measure.pi fun v => (κ v).map Prod.fst).real (A i) ≤ p :=
    fun i => by simpa only [hκP] using hP i
  -- The seed gives the coupled pair table `pairT σ`.
  set pairT : BudgetSeed α L B → ∀ p : V × ℕ, α p.1 × α p.1 :=
    fun σ p => G p.1 (σ (p.1, ⟨min p.2 B, Nat.lt_succ_of_le (min_le_right _ _)⟩))
  set E : Set (∀ p : V × ℕ, α p.1 × α p.1) :=
    {T | budgetedOutput vbl r B (fstTable T) ≠ budgetedOutput vbl r B (sndTable T)}
  have hEdep : DependsOn (· ∈ E) ((univ ×ˢ range (B + 1) : Finset (V × ℕ)) : Set (V × ℕ)) :=
    fun T T' h => by
      have h₁ := dependsOn_budgetedOutput (vbl := vbl) (r := r) (B := B) (x := fstTable T)
        (y := fstTable T') fun p hp => by simp only [fstTable]; rw [h p hp]
      have h₂ := dependsOn_budgetedOutput (vbl := vbl) (r := r) (B := B) (x := sndTable T)
        (y := sndTable T') fun p hp => by simp only [sndTable]; rw [h p hp]
      simp only [E, Set.mem_ofPred_eq, h₁, h₂]
  have hEm : MeasurableSet E := measurableSet_of_dependsOn hEdep
  -- Reading the entries with index at most `B`.
  set read : (∀ p : V × ℕ, α p.1 × α p.1) → ∀ q : V × Fin (B + 1), α q.1 × α q.1 :=
    fun T q => T (q.1, q.2.val)
  have hread : Measurable read := measurable_pi_iff.2 fun q => measurable_pi_apply _
  have hE : E = read ⁻¹' (read '' E) := by
    ext T
    refine ⟨fun h => ⟨T, h, rfl⟩, fun ⟨T', hT', heq⟩ => ?_⟩
    have : T' ∈ E ↔ T ∈ E := by
      refine iff_of_eq (hEdep fun p hp => ?_)
      simp only [coe_product, coe_univ, coe_range, Set.mem_prod, Set.mem_univ, Set.mem_Iio,
        true_and] at hp
      exact congrFun heq (p.1, ⟨p.2, hp⟩)
    exact this.1 hT'
  have himage : MeasurableSet (read '' E) := (Set.to_countable _).measurableSet
  have hcoupled : (coupledTable κ).map read = Measure.pi fun q => κ q.1 := by
    have hinj : Function.Injective fun q : V × Fin (B + 1) => ((q.1, q.2.val) : V × ℕ) :=
      fun q q' h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (Fin.ext h.2)
    rw [coupledTable_def, Measure.map_infinitePi_infinitePi_of_inj
      (P := fun p : V × ℕ => κ p.1) hinj, Measure.infinitePi_eq_pi]
  have hseed : ((Probability.PMF.uniformOfFintype (BudgetSeed α L B)).map pairT).toMeasure.map
      read = Measure.pi fun q => κ q.1 := by
    rw [PMF.toMeasure_map (hf := hread), PMF.map_comp]
    have hcomp : read ∘ pairT =
        fun (σ : BudgetSeed α L B) (q : V × Fin (B + 1)) => G q.1 (σ q) := by
      funext σ q
      simp only [Function.comp_apply, read, pairT]
      congr 2
      exact Prod.ext rfl (Fin.ext (min_eq_left (Nat.lt_succ_iff.1 q.2.isLt)))
    rw [hcomp, ← Probability.PMF.pi_uniformOfFintype, ← Probability.PMF.pi_map,
      Probability.PMF.toMeasure_pi]
  calc (Probability.PMF.uniformOfFintype (BudgetSeed α L B)).toOuterMeasure
          {σ | budgetedOutput vbl r B (seedTable B P σ) ≠
            budgetedOutput vbl r B (seedTable B Q σ)}
      = (Probability.PMF.uniformOfFintype (BudgetSeed α L B)).toOuterMeasure (pairT ⁻¹' E) := rfl
    _ = ((Probability.PMF.uniformOfFintype (BudgetSeed α L B)).map pairT).toMeasure E := by
        rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hEm, PMF.toOuterMeasure_map_apply]
    _ = coupledTable κ E := by
        rw [hE, ← Measure.map_apply hread himage, hseed, ← hcoupled,
          Measure.map_apply hread himage]
    _ ≤ coupledTable κ {T | Diverge vbl r T} := measure_mono fun T hT => by
        by_contra hd
        exact hT (budgetedOutput_eq_of_not_diverge hd)
    _ ≤ 2 * ∑ v, κ v {x | x.1 ≠ x.2} :=
        coupledTable_diverge_le_two_mul κ vbl r A hAm hA Γ hΓ hΓd hP' hp hr
    _ ≤ 2 * ∑ v, ENNReal.ofReal (2 * dist (P v).toPMF (Q v).toPMF) := by
        gcongr with v
        exact hdis v
    _ = ENNReal.ofReal (4 * ∑ v, dist (P v).toPMF (Q v).toPMF) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun v _ => by positivity, ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num), ← mul_sum, ← mul_assoc]
        norm_num

/-- The **budgeted Moser–Tardos learner**. On the dataset `S`, it runs the rule `historyRule r`
for `B` steps on the table of the shared seed for the estimated grid distributions `P̂ S`, and
outputs the budgeted output: an assignment, or `none` on a timeout. -/
noncomputable def budgetedMoserTardos {ι X : Type*} {m : ℕ} (vbl : ι → Finset V)
    (r : List ι → (∀ v, α v) → Option ι) (est : (Fin m → X) → ∀ v, GridDist (α v) L) :
    Algorithm X (BudgetSeed α L B) (Option (∀ v, α v)) m :=
  Algorithm.deterministic (Probability.PMF.uniformOfFintype _) fun S σ =>
    budgetedOutput vbl r B (seedTable B (est S) σ)

/-- **Replicable constraint solving (original).** Let `r` be a non-anticipating rule that only
selects occurring events, and let the dataset `S` determine grid estimates `P̂ S v` of the
variables' distributions. Suppose that for every dataset every event has at most `d` neighbours in
`Γ` and probability at most `p` under the product of the `P̂ S v`, with `e p (d + 1) ≤ 1`. Then
two runs of `budgetedMoserTardos` on independent `m`-samples from `D`, sharing the seed, disagree
with probability `ρ ≤ 4 ∑ v, E_{S, S'} d_TV(P̂ S v, P̂ S' v)`, for every budget `B`. -/
theorem disagreeProb_budgetedMoserTardos_le {ι X : Type*} [Finite ι] {m : ℕ}
    (vbl : ι → Finset V) (r : List ι → (∀ v, α v) → Option ι)
    (est : (Fin m → X) → ∀ v, GridDist (α v) L) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i) {d : ℕ}
    (hΓd : ∀ i, (Γ i).card ≤ d) {p : ℝ}
    (hP : ∀ S i, (Measure.pi fun v => (est S v).toPMF.toMeasure).real (A i) ≤ p)
    (hp : Real.exp 1 * p * (d + 1) ≤ 1) (hr : ∀ w a i, r w a = some i → a ∈ A i) (D : PMF X) :
    ENNReal.ofReal ((budgetedMoserTardos B vbl r est).disagreeProb D) ≤
      4 * ∑ v, ∑' S₁, ∑' S₂, Probability.PMF.iid D m S₁ * Probability.PMF.iid D m S₂ *
        ENNReal.ofReal (dist (est S₁ v).toPMF (est S₂ v).toPMF) := by
  rw [Algorithm.disagreeProb, ENNReal.ofReal_toReal (Probability.PMF.toOuterMeasure_ne_top _ _),
    budgetedMoserTardos, Algorithm.pairedOutput_deterministic_eq_samples,
    PMF.toOuterMeasure_bind_apply]
  have hpair : ∀ S₁ S₂ : Fin m → X,
      ((Probability.PMF.uniformOfFintype (BudgetSeed α L B)).map fun σ =>
        (budgetedOutput vbl r B (seedTable B (est S₁) σ),
          budgetedOutput vbl r B (seedTable B (est S₂) σ))).toOuterMeasure
        {q | q.1 ≠ q.2} ≤ 4 * ∑ v, ENNReal.ofReal (dist (est S₁ v).toPMF (est S₂ v).toPMF) := by
    intro S₁ S₂
    rw [PMF.toOuterMeasure_map_apply]
    refine (seedTable_disagree_le B vbl r (est S₁) (est S₂) A hAm hA Γ hΓ hΓd (hP S₁) hp hr).trans
      (le_of_eq ?_)
    rw [← ENNReal.ofReal_sum_of_nonneg fun v _ => dist_nonneg, ← ENNReal.ofReal_ofNat 4,
      ← ENNReal.ofReal_mul (by norm_num), mul_sum]
  calc ∑' S₁, Probability.PMF.iid D m S₁ * ((Probability.PMF.iid D m).bind fun S₂ =>
          (Probability.PMF.uniformOfFintype (BudgetSeed α L B)).map fun σ =>
            (budgetedOutput vbl r B (seedTable B (est S₁) σ),
              budgetedOutput vbl r B (seedTable B (est S₂) σ))).toOuterMeasure {q | q.1 ≠ q.2}
      ≤ ∑' S₁, Probability.PMF.iid D m S₁ * ∑' S₂, Probability.PMF.iid D m S₂ *
          (4 * ∑ v, ENNReal.ofReal (dist (est S₁ v).toPMF (est S₂ v).toPMF)) := by
        refine tsum_le_tsum fun S₁ => ?_
        gcongr
        rw [PMF.toOuterMeasure_bind_apply]
        exact tsum_le_tsum fun S₂ => by gcongr; exact hpair S₁ S₂
    _ = 4 * ∑ v, ∑' S₁, ∑' S₂, Probability.PMF.iid D m S₁ * Probability.PMF.iid D m S₂ *
          ENNReal.ofReal (dist (est S₁ v).toPMF (est S₂ v).toPMF) := by
        simp only [mul_sum, ← ENNReal.tsum_mul_left]
        rw [← Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable]
        refine tsum_congr fun S₁ => ?_
        rw [← Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable]
        refine tsum_congr fun S₂ => sum_congr rfl fun v _ => ?_
        ring

end Seed

end Cslib.MachineLearning.Replicable
