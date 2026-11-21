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
except with probability `4 ∑ v, E_{S, S'} d_TV(P̂ S v, P̂ S' v)`, plus the probability that a
dataset is not one on which the estimates satisfy the local-lemma hypothesis.

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
the estimates of the datasets in a set `good`, and pays `Pr[S ∉ good]` for the others; it does not
depend on the budget, the number of events or the dependency degree. Two runs whose histories
agree through the budget give equal `Option` outputs, including a shared timeout `none`
(`budgetedOutput_eq_of_not_diverge`). A run whose history diverges from the other's can time out
on only one side, and that case is counted in the divergence probability. The budget enters
through the timeout probability: a single run times out with probability at most
`|ι| / ((d + 1) (B + 1))` (`seedTable_timeout_le`). A rule that stops only when no event occurs
never outputs a bad assignment (`budgetedOutput_eq_some`), so the learner is accurate up to that
timeout probability (`isAccurateOn_budgetedMoserTardos`,
`isAccurate_budgetedMoserTardos`).

The statement and its proof route are original (cslib-frontier issue #6718).

## Main definitions

* `Cslib.MachineLearning.Replicable.budgetedOutput`: the output of a run budgeted to `B` steps.
* `Cslib.MachineLearning.Replicable.BudgetSeed`, `Cslib.MachineLearning.Replicable.seedTable`:
  the shared seed and the table it gives for a family of grid distributions.
* `Cslib.MachineLearning.Replicable.budgetedMoserTardos`: the replicable algorithm.
* `Cslib.MachineLearning.Replicable.goodOutput`: the outputs that are assignments avoiding every
  event.

## Main results

* `Cslib.MachineLearning.Replicable.budgetedOutput_eq_some`: outputs avoid every event.
* `Cslib.MachineLearning.Replicable.seedTable_disagree_le`: for fixed estimates `P` and `Q`, two
  runs sharing the seed disagree with probability at most `4 ∑ v, d_TV(P v, Q v)`.
* `Cslib.MachineLearning.Replicable.seedTable_timeout_le`: a single budgeted run times out with
  probability at most `|ι| / ((d + 1) (B + 1))`.
* `Cslib.MachineLearning.Replicable.isAccurateOn_budgetedMoserTardos`,
  `Cslib.MachineLearning.Replicable.isAccurate_budgetedMoserTardos`: the learner outputs a good
  assignment except with the timeout probability (plus `Pr[S ∉ good]`).
* `Cslib.MachineLearning.Replicable.disagreeProb_budgetedMoserTardos_le`: the replicability bound.

## Implementation notes

`seedTable_disagree_le` transfers the first-disagreement bound
(`Cslib.Probability.MoserTardos.coupledTable_diverge_le_two_mul`) from the infinite coupled table
to the finite seed, and `seedTable_timeout_le` transfers the Moser–Tardos resampling bound
(`Cslib.Probability.MoserTardos.exists_measurable_ge_resamplings`, with the symmetric weights of
`Cslib.Probability.MoserTardos.lll_of_symm`) followed by Markov's inequality. The budgeted outputs
depend only on the samples with index at most `B`, and the laws of those samples under the seed
and under the independent table are the same product (a private lemma).

No statement mentions a measurable structure: the hypotheses are stated with the product
distribution `Cslib.Probability.PMF.pi`, and the proofs equip each `α v` with the discrete
structure locally.

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

/-- The table read from the seed `σ` through the maps `G v`: entry `(v, k)` is `G v` of the
enumeration at `(v, min k B)`. -/
private def readSeed {β : V → Type*} (G : ∀ v, Enumeration (α v × Fin L) → β v)
    (σ : BudgetSeed α L B) : ∀ p : V × ℕ, β p.1 :=
  fun p => G p.1 (σ (p.1, ⟨min p.2 B, Nat.lt_succ_of_le (min_le_right _ _)⟩))

/-- The table given by the seed `σ` for the grid distributions `P`: entry `(v, k)` is sampled from
`P v` by correlated sampling from the enumeration at `(v, min k B)`. A run budgeted to `B` steps
reads only the entries with `k ≤ B`. -/
def seedTable (P : ∀ v, GridDist (α v) L) (σ : BudgetSeed α L B) : ∀ p : V × ℕ, α p.1 :=
  readSeed B (fun v => gridSample (P v)) σ

omit [NeZero L] in
/-- **The seed is faithful on the first `B + 1` samples.** An event of the table that depends only
on the entries `(v, k)` with `k ≤ B` has the same probability under the seed as under the
independent table whose entries at `v` have the law of `G v` of a uniform enumeration. -/
private theorem toOuterMeasure_readSeed {β : V → Type*} [∀ v, Finite (β v)]
    [∀ v, MeasurableSpace (β v)] [∀ v, MeasurableSingletonClass (β v)]
    (G : ∀ v, Enumeration (α v × Fin L) → β v) {E : Set (∀ p : V × ℕ, β p.1)}
    (hE : DependsOn (· ∈ E) ((univ ×ˢ range (B + 1) : Finset (V × ℕ)) : Set (V × ℕ))) :
    (Probability.PMF.uniformOfFintype (BudgetSeed α L B)).toOuterMeasure (readSeed B G ⁻¹' E) =
      Measure.infinitePi (fun p : V × ℕ =>
        ((Probability.PMF.uniformOfFintype (Enumeration (α p.1 × Fin L))).map
          (G p.1)).toMeasure) E := by
  classical
  set κ : ∀ v, Measure (β v) := fun v =>
    ((Probability.PMF.uniformOfFintype (Enumeration (α v × Fin L))).map (G v)).toMeasure
  have hEm : MeasurableSet E := measurableSet_of_dependsOn hE
  -- Reading the entries with index at most `B`.
  set read : (∀ p : V × ℕ, β p.1) → ∀ q : V × Fin (B + 1), β q.1 :=
    fun T q => T (q.1, q.2.val)
  have hread : Measurable read := measurable_pi_iff.2 fun q => measurable_pi_apply _
  have hE' : E = read ⁻¹' (read '' E) := by
    ext T
    refine ⟨fun h => ⟨T, h, rfl⟩, fun ⟨T', hT', heq⟩ => ?_⟩
    have : T' ∈ E ↔ T ∈ E := by
      refine iff_of_eq (hE fun p hp => ?_)
      simp only [coe_product, coe_univ, coe_range, Set.mem_prod, Set.mem_univ, Set.mem_Iio,
        true_and] at hp
      exact congrFun heq (p.1, ⟨p.2, hp⟩)
    exact this.1 hT'
  have himage : MeasurableSet (read '' E) := (Set.to_countable _).measurableSet
  have htable : (Measure.infinitePi fun p : V × ℕ => κ p.1).map read =
      Measure.pi fun q => κ q.1 := by
    have hinj : Function.Injective fun q : V × Fin (B + 1) => ((q.1, q.2.val) : V × ℕ) :=
      fun q q' h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (Fin.ext h.2)
    rw [Measure.map_infinitePi_infinitePi_of_inj (P := fun p : V × ℕ => κ p.1) hinj,
      Measure.infinitePi_eq_pi]
  have hseed : ((Probability.PMF.uniformOfFintype (BudgetSeed α L B)).map
      (readSeed B G)).toMeasure.map read = Measure.pi fun q => κ q.1 := by
    rw [PMF.toMeasure_map (hf := hread), PMF.map_comp]
    have hcomp : read ∘ readSeed B G =
        fun (σ : BudgetSeed α L B) (q : V × Fin (B + 1)) => G q.1 (σ q) := by
      funext σ q
      simp only [Function.comp_apply, read, readSeed]
      congr 2
      exact Prod.ext rfl (Fin.ext (min_eq_left (Nat.lt_succ_iff.1 q.2.isLt)))
    rw [hcomp, ← Probability.PMF.pi_uniformOfFintype, ← Probability.PMF.pi_map,
      Probability.PMF.toMeasure_pi]
  rw [← PMF.toOuterMeasure_map_apply, ← PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hEm, hE',
    ← Measure.map_apply hread himage, hseed, ← htable, Measure.map_apply hread himage]

omit [DecidableEq V] [∀ v, DecidableEq (α v)] in
/-- The local-lemma hypothesis on the product of the grid distributions, transported to the
product measure for the discrete measurable structure. -/
private theorem measureReal_pi_toPMF_le (P : ∀ v, GridDist (α v) L) {A : Set (∀ v, α v)} {p : ℝ}
    (hP : ((Probability.PMF.pi fun v => (P v).toPMF).toOuterMeasure A).toReal ≤ p) :
    let (v : V) : MeasurableSpace (α v) := ⊤
    (Measure.pi fun v => (P v).toPMF.toMeasure).real A ≤ p := by
  intro
  rwa [← Probability.PMF.toMeasure_pi, measureReal_def,
    PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (Set.to_countable _).measurableSet]

/-- **Replicable runs for fixed estimates (original).** Let `r` be a non-anticipating rule that
only selects occurring events. Suppose every event has at most `d` neighbours in `Γ` and
probability at most `p` under the product of the `P v`, with `e p (d + 1) ≤ 1`. Then two runs
budgeted to `B` steps, one with `P` and one with `Q`, reading the tables of one uniformly random
seed, give different outputs with probability at most `4 ∑ v, d_TV(P v, Q v)`. -/
theorem seedTable_disagree_le {ι : Type*} [Finite ι] (vbl : ι → Finset V)
    (r : List ι → (∀ v, α v) → Option ι) (P Q : ∀ v, GridDist (α v) L)
    (A : ι → Set (∀ v, α v)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) (Γ : ι → Finset ι)
    (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i) {d : ℕ}
    (hΓd : ∀ i, (Γ i).card ≤ d) {p : ℝ}
    (hP : ∀ i, ((Probability.PMF.pi fun v => (P v).toPMF).toOuterMeasure (A i)).toReal ≤ p)
    (hp : Real.exp 1 * p * (d + 1) ≤ 1) (hr : ∀ w a i, r w a = some i → a ∈ A i) :
    ((Probability.PMF.uniformOfFintype (BudgetSeed α L B)).toOuterMeasure
        {σ | budgetedOutput vbl r B (seedTable B P σ) ≠
          budgetedOutput vbl r B (seedTable B Q σ)}).toReal ≤
      4 * ∑ v, dist (P v).toPMF (Q v).toPMF := by
  classical
  let (v : V) : MeasurableSpace (α v) := ⊤
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
    fun i => by simpa only [hκP] using measureReal_pi_toPMF_le P (hP i)
  set E : Set (∀ p : V × ℕ, α p.1 × α p.1) :=
    {T | budgetedOutput vbl r B (fstTable T) ≠ budgetedOutput vbl r B (sndTable T)}
  have hEdep : DependsOn (· ∈ E) ((univ ×ˢ range (B + 1) : Finset (V × ℕ)) : Set (V × ℕ)) :=
    fun T T' h => by
      have h₁ := dependsOn_budgetedOutput (vbl := vbl) (r := r) (B := B) (x := fstTable T)
        (y := fstTable T') fun p hp => by simp only [fstTable]; rw [h p hp]
      have h₂ := dependsOn_budgetedOutput (vbl := vbl) (r := r) (B := B) (x := sndTable T)
        (y := sndTable T') fun p hp => by simp only [sndTable]; rw [h p hp]
      simp only [E, Set.mem_ofPred_eq, h₁, h₂]
  refine ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (by norm_num) (sum_nonneg fun v _ => dist_nonneg)) ?_
  calc (Probability.PMF.uniformOfFintype (BudgetSeed α L B)).toOuterMeasure
          {σ | budgetedOutput vbl r B (seedTable B P σ) ≠
            budgetedOutput vbl r B (seedTable B Q σ)}
      = (Probability.PMF.uniformOfFintype (BudgetSeed α L B)).toOuterMeasure
          (readSeed B G ⁻¹' E) := rfl
    _ = coupledTable κ E := by rw [toOuterMeasure_readSeed B G hEdep, coupledTable_def]
    _ ≤ coupledTable κ {T | Diverge vbl r T} := measure_mono fun T hT => by
        by_contra hd
        exact hT (budgetedOutput_eq_of_not_diverge hd)
    _ ≤ 2 * ∑ v, κ v {x | x.1 ≠ x.2} :=
        coupledTable_diverge_le_two_mul κ vbl r A (fun i => measurableSet_of_dependsOn (hA i)) hA
          Γ hΓ hΓd hP' hp hr
    _ ≤ 2 * ∑ v, ENNReal.ofReal (2 * dist (P v).toPMF (Q v).toPMF) := by
        gcongr with v
        exact hdis v
    _ = ENNReal.ofReal (4 * ∑ v, dist (P v).toPMF (Q v).toPMF) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun v _ => by positivity, ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num), ← mul_sum, ← mul_assoc]
        norm_num

omit [Fintype V] [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)] in
/-- A budgeted run times out only after `B + 1` resamplings: its log after `B + 1` steps has
length `B + 1`. -/
private theorem length_run_of_budgetedOutput_eq_none {ι : Type*} {vbl : ι → Finset V}
    {r : List ι → (∀ v, α v) → Option ι} {T : ∀ p : V × ℕ, α p.1}
    (h : budgetedOutput vbl r B T = none) :
    (run (historyRule vbl r) T (B + 1)).length = B + 1 := by
  have hB : historyRule vbl r T (run (historyRule vbl r) T B) ≠ none := by
    unfold budgetedOutput at h
    split at h
    · cases h
    · simp only [historyRule]
      simp_all
  have hstep : ∀ m ≤ B, historyRule vbl r T (run (historyRule vbl r) T m) ≠ none :=
    fun m hm hm' => hB (by rw [run_eq_of_eq_none hm' hm]; exact hm')
  have hlen : ∀ m ≤ B + 1, (run (historyRule vbl r) T m).length = m := by
    intro m hm
    induction m with
    | zero => rw [run_zero, List.length_nil]
    | succ m ih =>
      obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.1 (hstep m (by omega))
      rw [run_succ_of_eq_some hi, List.length_cons, ih (by omega)]
  exact hlen _ le_rfl

/-- **Timeouts are rare (original).** Let `r` be a non-anticipating rule that only selects
occurring events. Suppose every event has at most `d` neighbours in `Γ` and probability at most
`p` under the product of the `P v`, with `e p (d + 1) ≤ 1`. Then a run budgeted to `B` steps on
the table of a uniformly random seed times out with probability at most
`|ι| / ((d + 1) (B + 1))`.

A timeout means `B + 1` resamplings. By Moser–Tardos the expected number of resamplings of each
event is at most `1 / (d + 1)` on the independent table, which the seed reproduces on the entries
the budgeted run reads; Markov's inequality gives the bound. -/
theorem seedTable_timeout_le {ι : Type*} [Fintype ι] (vbl : ι → Finset V)
    (r : List ι → (∀ v, α v) → Option ι) (P : ∀ v, GridDist (α v) L)
    (A : ι → Set (∀ v, α v)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) (Γ : ι → Finset ι)
    (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i) {d : ℕ}
    (hΓd : ∀ i, (Γ i).card ≤ d) {p : ℝ}
    (hP : ∀ i, ((Probability.PMF.pi fun v => (P v).toPMF).toOuterMeasure (A i)).toReal ≤ p)
    (hp : Real.exp 1 * p * (d + 1) ≤ 1) (hr : ∀ w a i, r w a = some i → a ∈ A i) :
    ((Probability.PMF.uniformOfFintype (BudgetSeed α L B)).toOuterMeasure
        {σ | budgetedOutput vbl r B (seedTable B P σ) = none}).toReal ≤
      Fintype.card ι / ((d + 1) * (B + 1)) := by
  classical
  let (v : V) : MeasurableSpace (α v) := ⊤
  set μ : ∀ v, Measure (α v) := fun v => (P v).toPMF.toMeasure
  obtain ⟨hx, hPx⟩ := lll_of_symm (Measure.pi μ) Γ hΓd (fun i => measureReal_pi_toPMF_le P (hP i))
    hp
  choose g hgm hg hge using fun i => exists_measurable_ge_resamplings μ vbl A
    (fun i => measurableSet_of_dependsOn (hA i)) hA Γ hΓ hx hPx i
  set E : Set (∀ p : V × ℕ, α p.1) := {T | budgetedOutput vbl r B T = none}
  have hEdep : DependsOn (· ∈ E) ((univ ×ˢ range (B + 1) : Finset (V × ℕ)) : Set (V × ℕ)) :=
    fun T T' h => by simp only [E, Set.mem_ofPred_eq, dependsOn_budgetedOutput h]
  have hseed : (Probability.PMF.uniformOfFintype (BudgetSeed α L B)).toOuterMeasure
      {σ | budgetedOutput vbl r B (seedTable B P σ) = none} = table μ E := by
    rw [show {σ | budgetedOutput vbl r B (seedTable B P σ) = none} =
        readSeed B (fun v => gridSample (P v)) ⁻¹' E from rfl, toOuterMeasure_readSeed B _ hEdep,
      table_def]
    simp only [map_gridSample, μ]
  -- A timeout forces `B + 1` resamplings.
  have hsub : E ⊆ {T | ((B + 1 : ℕ) : ℝ≥0∞) ≤ ∑ i, g i T} := fun T hT => by
    set w := run (historyRule vbl r) T (B + 1)
    calc ((B + 1 : ℕ) : ℝ≥0∞) = (w.length : ℝ≥0∞) := by
          rw [length_run_of_budgetedOutput_eq_none B hT]
      _ = ∑ i, (w.count i : ℝ≥0∞) := by
          rw [← Nat.cast_sum]
          congr 1
          have := Multiset.sum_count_eq_card (s := univ) (m := (w : Multiset ι))
            fun a _ => mem_univ a
          simpa using this.symm
      _ ≤ ∑ i, resamplings (historyRule vbl r) i T := sum_le_sum fun i _ => by
          rw [resamplings_def]
          exact le_iSup (fun n => ((run (historyRule vbl r) T n).count i : ℝ≥0∞)) (B + 1)
      _ ≤ ∑ i, g i T := sum_le_sum fun i _ => hge i _ (historyRule_valid hr) T
  have hxd : (1 / (d + 2 : ℝ)) / (1 - 1 / (d + 2)) = 1 / (d + 1) := by
    have h2 : (d + 2 : ℝ) ≠ 0 := by positivity
    rw [one_sub_div h2, show (d + 2 : ℝ) - 1 = d + 1 by ring, div_div_div_cancel_right₀ h2]
  have hint : ∫⁻ T, ∑ i, g i T ∂table μ ≤ Fintype.card ι * ENNReal.ofReal (1 / (d + 1)) := by
    rw [lintegral_finsetSum _ fun i _ => hgm i]
    calc ∑ i, ∫⁻ T, g i T ∂table μ ≤ ∑ _i : ι, ENNReal.ofReal (1 / (d + 1)) :=
          sum_le_sum fun i _ => (hg i).trans_eq (by rw [hxd])
      _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]
  have hB0 : ((B + 1 : ℕ) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero B)
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  calc (Probability.PMF.uniformOfFintype (BudgetSeed α L B)).toOuterMeasure
          {σ | budgetedOutput vbl r B (seedTable B P σ) = none}
      = table μ E := hseed
    _ ≤ table μ {T | ((B + 1 : ℕ) : ℝ≥0∞) ≤ ∑ i, g i T} := measure_mono hsub
    _ ≤ (∫⁻ T, ∑ i, g i T ∂table μ) / ((B + 1 : ℕ) : ℝ≥0∞) :=
        meas_ge_le_lintegral_div (Finset.measurable_sum _ fun i _ => hgm i).aemeasurable hB0
          (ENNReal.natCast_ne_top _)
    _ ≤ Fintype.card ι * ENNReal.ofReal (1 / (d + 1)) / ((B + 1 : ℕ) : ℝ≥0∞) := by
        gcongr
    _ = ENNReal.ofReal (Fintype.card ι / ((d + 1) * (B + 1))) := by
        rw [← ENNReal.ofReal_natCast (Fintype.card ι), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_natCast (B + 1), ← ENNReal.ofReal_div_of_pos (by positivity)]
        congr 1
        push_cast
        field_simp

/-- The **budgeted Moser–Tardos learner**. On the dataset `S`, it runs the rule `historyRule r`
for `B` steps on the table of the shared seed for the estimated grid distributions `P̂ S`, and
outputs the budgeted output: an assignment, or `none` on a timeout. -/
noncomputable def budgetedMoserTardos {ι X : Type*} {m : ℕ} (vbl : ι → Finset V)
    (r : List ι → (∀ v, α v) → Option ι) (est : (Fin m → X) → ∀ v, GridDist (α v) L) :
    Algorithm X (BudgetSeed α L B) (Option (∀ v, α v)) m :=
  Algorithm.deterministic (Probability.PMF.uniformOfFintype _) fun S σ =>
    budgetedOutput vbl r B (seedTable B (est S) σ)

/-- The outputs of `budgetedMoserTardos` that are assignments avoiding every event. -/
def goodOutput {ι : Type*} (A : ι → Set (∀ v, α v)) : Set (Option (∀ v, α v)) :=
  {o | ∃ a, o = some a ∧ ∀ i, a ∉ A i}

/-- **Accuracy of the budgeted learner (original).** Let `r` be a non-anticipating rule that
only selects occurring events and stops only when no event occurs. Suppose that for every dataset
in `good` every event has at most `d` neighbours in `Γ` and probability at most `p` under the
product of the estimates `P̂ S v`, with `e p (d + 1) ≤ 1`. Then on an `m`-sample from `D` the
learner fails to output an assignment avoiding every event with probability at most
`|ι| / ((d + 1) (B + 1))` plus the probability that the sample is not in `good`. -/
theorem isAccurateOn_budgetedMoserTardos {ι X : Type*} [Fintype ι] {m : ℕ}
    (vbl : ι → Finset V) (r : List ι → (∀ v, α v) → Option ι)
    (est : (Fin m → X) → ∀ v, GridDist (α v) L) (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i) {d : ℕ}
    (hΓd : ∀ i, (Γ i).card ≤ d) {p : ℝ} (good : Set (Fin m → X))
    (hP : ∀ S ∈ good, ∀ i,
      ((Probability.PMF.pi fun v => (est S v).toPMF).toOuterMeasure (A i)).toReal ≤ p)
    (hp : Real.exp 1 * p * (d + 1) ≤ 1) (hr : ∀ w a i, r w a = some i → a ∈ A i)
    (hstop : ∀ w a, r w a = none → ∀ i, a ∉ A i) (D : PMF X) :
    IsAccurateOn (budgetedMoserTardos B vbl r est) D (goodOutput A)
      (Fintype.card ι / ((d + 1) * (B + 1)) +
        ((Probability.PMF.iid D m).toOuterMeasure goodᶜ).toReal) := by
  set c : ℝ := Fintype.card ι / ((d + 1) * (B + 1))
  have hS : ∀ S, ((Probability.PMF.uniformOfFintype (BudgetSeed α L B)).map fun σ =>
      budgetedOutput vbl r B (seedTable B (est S) σ)).toOuterMeasure (goodOutput A)ᶜ ≤
        ENNReal.ofReal c + goodᶜ.indicator 1 S := fun S => by
    rw [PMF.toOuterMeasure_map_apply]
    by_cases hSg : S ∈ good
    · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.2 hSg), add_zero]
      refine (measure_mono fun σ hσ => ?_).trans
        (ENNReal.le_ofReal_iff_toReal_le (Probability.PMF.toOuterMeasure_ne_top _ _)
          (by positivity) |>.2 (seedTable_timeout_le B vbl r (est S) A hA Γ hΓ hΓd (hP S hSg)
            hp hr))
      simp only [Set.mem_preimage, Set.mem_compl_iff, goodOutput, Set.mem_ofPred_eq,
        not_exists, not_and] at hσ ⊢
      cases ho : budgetedOutput vbl r B (seedTable B (est S) σ) with
      | none => rfl
      | some a => exact absurd (fun i => budgetedOutput_eq_some hstop ho i) (hσ a ho)
    · rw [Set.indicator_of_mem hSg]
      exact le_add_left (Probability.PMF.toOuterMeasure_le_one _ _)
  have hbound : (((budgetedMoserTardos B vbl r est).marginal D).toOuterMeasure
      (goodOutput A)ᶜ) ≤ ENNReal.ofReal c + (Probability.PMF.iid D m).toOuterMeasure goodᶜ := by
    rw [Algorithm.marginal, PMF.toOuterMeasure_bind_apply]
    calc ∑' S, Probability.PMF.iid D m S *
          ((budgetedMoserTardos B vbl r est).output S).toOuterMeasure (goodOutput A)ᶜ
        ≤ ∑' S, Probability.PMF.iid D m S * (ENNReal.ofReal c + goodᶜ.indicator 1 S) := by
          refine tsum_le_tsum fun S => ?_
          gcongr
          have h := hS S
          rw [← PMF.bind_pure_comp] at h
          exact h
      _ = ENNReal.ofReal c + (Probability.PMF.iid D m).toOuterMeasure goodᶜ := by
          simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
            PMF.toOuterMeasure_apply]
          congr 1
          refine tsum_congr fun S => ?_
          by_cases hSg : S ∈ goodᶜ <;> simp [Set.indicator, hSg]
  refine (ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, Probability.PMF.toOuterMeasure_ne_top _ _⟩)
    hbound).trans ?_
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (Probability.PMF.toOuterMeasure_ne_top _ _),
    ENNReal.toReal_ofReal (by positivity)]

/-- **Strong accuracy of the budgeted learner (original).** If the local-lemma hypothesis holds
for the estimates of every dataset, the learner outputs an assignment avoiding every event except
with probability at most `|ι| / ((d + 1) (B + 1))`, for every distribution of the data. -/
theorem isAccurate_budgetedMoserTardos {ι X : Type*} [Fintype ι] {m : ℕ}
    (vbl : ι → Finset V) (r : List ι → (∀ v, α v) → Option ι)
    (est : (Fin m → X) → ∀ v, GridDist (α v) L) (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i) {d : ℕ}
    (hΓd : ∀ i, (Γ i).card ≤ d) {p : ℝ}
    (hP : ∀ S i, ((Probability.PMF.pi fun v => (est S v).toPMF).toOuterMeasure (A i)).toReal ≤ p)
    (hp : Real.exp 1 * p * (d + 1) ≤ 1) (hr : ∀ w a i, r w a = some i → a ∈ A i)
    (hstop : ∀ w a, r w a = none → ∀ i, a ∉ A i) :
    IsAccurate (budgetedMoserTardos B vbl r est) (fun _ => goodOutput A)
      (Fintype.card ι / ((d + 1) * (B + 1))) := fun D _ => by
  have h := isAccurateOn_budgetedMoserTardos B vbl r est A hA Γ hΓ hΓd Set.univ
    (fun S _ => hP S) hp hr hstop D
  simpa only [Set.compl_univ, measure_empty, ENNReal.toReal_zero, add_zero] using h

/-- Two-sample expectations of a function with values in `[0, 1]`, computed in `ℝ≥0∞` and in `ℝ`,
agree. -/
private theorem toReal_tsum_tsum_iid {X : Type*} {m : ℕ} (D : PMF X)
    (f : (Fin m → X) → (Fin m → X) → ℝ) (hf0 : ∀ S₁ S₂, 0 ≤ f S₁ S₂)
    (hf1 : ∀ S₁ S₂, f S₁ S₂ ≤ 1) :
    (∑' S₁, ∑' S₂, Probability.PMF.iid D m S₁ * Probability.PMF.iid D m S₂ *
        ENNReal.ofReal (f S₁ S₂)) ≠ ∞ ∧
      (∑' S₁, ∑' S₂, Probability.PMF.iid D m S₁ * Probability.PMF.iid D m S₂ *
        ENNReal.ofReal (f S₁ S₂)).toReal =
        ∑' S₁, ∑' S₂, (Probability.PMF.iid D m S₁).toReal * (Probability.PMF.iid D m S₂).toReal *
          f S₁ S₂ := by
  set μ := Probability.PMF.iid D m
  have hin : ∀ S₁, ∑' S₂, μ S₁ * μ S₂ * ENNReal.ofReal (f S₁ S₂) ≤ μ S₁ := fun S₁ => by
    calc ∑' S₂, μ S₁ * μ S₂ * ENNReal.ofReal (f S₁ S₂) ≤ ∑' S₂, μ S₁ * μ S₂ :=
          tsum_le_tsum fun S₂ => mul_le_of_le_one_right' (ENNReal.ofReal_le_one.2 (hf1 _ _))
      _ = μ S₁ := by rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
  have hout : ∑' S₁, ∑' S₂, μ S₁ * μ S₂ * ENNReal.ofReal (f S₁ S₂) ≤ 1 :=
    (tsum_le_tsum hin).trans_eq μ.tsum_coe
  refine ⟨ne_top_of_le_ne_top ENNReal.one_ne_top hout, ?_⟩
  rw [ENNReal.tsum_toReal_eq fun S₁ => ne_top_of_le_ne_top (μ.apply_ne_top S₁) (hin S₁)]
  refine tsum_congr fun S₁ => ?_
  rw [ENNReal.tsum_toReal_eq fun S₂ => ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (μ.apply_ne_top _) (μ.apply_ne_top _)) ENNReal.ofReal_ne_top]
  refine tsum_congr fun S₂ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf0 _ _)]

/-- **Replicable constraint solving (original).** Let `r` be a non-anticipating rule that only
selects occurring events, and let the dataset `S` determine grid estimates `P̂ S v` of the
variables' distributions. Suppose that for every dataset in `good` every event has at most `d`
neighbours in `Γ` and probability at most `p` under the product of the `P̂ S v`, with
`e p (d + 1) ≤ 1`. Then two runs of `budgetedMoserTardos` on independent `m`-samples from `D`,
sharing the seed, disagree with probability
`ρ ≤ 4 ∑ v, E_{S, S'} d_TV(P̂ S v, P̂ S' v) + Pr[S ∉ good]`, for every budget `B`. With
`good = Set.univ` the last term vanishes. -/
theorem disagreeProb_budgetedMoserTardos_le {ι X : Type*} [Finite ι] {m : ℕ}
    (vbl : ι → Finset V) (r : List ι → (∀ v, α v) → Option ι)
    (est : (Fin m → X) → ∀ v, GridDist (α v) L) (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i) {d : ℕ}
    (hΓd : ∀ i, (Γ i).card ≤ d) {p : ℝ} (good : Set (Fin m → X))
    (hP : ∀ S ∈ good, ∀ i,
      ((Probability.PMF.pi fun v => (est S v).toPMF).toOuterMeasure (A i)).toReal ≤ p)
    (hp : Real.exp 1 * p * (d + 1) ≤ 1) (hr : ∀ w a i, r w a = some i → a ∈ A i) (D : PMF X) :
    (budgetedMoserTardos B vbl r est).disagreeProb D ≤
      4 * ∑ v, ∑' S₁, ∑' S₂, (Probability.PMF.iid D m S₁).toReal *
        (Probability.PMF.iid D m S₂).toReal * dist (est S₁ v).toPMF (est S₂ v).toPMF +
      ((Probability.PMF.iid D m).toOuterMeasure goodᶜ).toReal := by
  set μ := Probability.PMF.iid D m
  set e : V → ℝ≥0∞ := fun v => ∑' S₁, ∑' S₂, μ S₁ * μ S₂ *
    ENNReal.ofReal (dist (est S₁ v).toPMF (est S₂ v).toPMF)
  have he := fun v => toReal_tsum_tsum_iid D (fun S₁ S₂ => dist (est S₁ v).toPMF (est S₂ v).toPMF)
    (fun _ _ => dist_nonneg) (fun _ _ => Cslib.Probability.PMF.dist_le_one _ _)
  have hpair : ∀ S₁ S₂ : Fin m → X,
      ((Probability.PMF.uniformOfFintype (BudgetSeed α L B)).map fun σ =>
        (budgetedOutput vbl r B (seedTable B (est S₁) σ),
          budgetedOutput vbl r B (seedTable B (est S₂) σ))).toOuterMeasure
        {q | q.1 ≠ q.2} ≤
        4 * ∑ v, ENNReal.ofReal (dist (est S₁ v).toPMF (est S₂ v).toPMF) +
          goodᶜ.indicator 1 S₁ := by
    intro S₁ S₂
    rw [PMF.toOuterMeasure_map_apply]
    by_cases hS : S₁ ∈ good
    · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.2 hS), add_zero]
      refine (ENNReal.le_ofReal_iff_toReal_le (Probability.PMF.toOuterMeasure_ne_top _ _)
        (mul_nonneg (by norm_num) (sum_nonneg fun v _ => dist_nonneg)) |>.2
          (seedTable_disagree_le B vbl r (est S₁) (est S₂) A hA Γ hΓ hΓd (hP S₁ hS) hp hr)).trans
        (le_of_eq ?_)
      rw [← ENNReal.ofReal_sum_of_nonneg fun v _ => dist_nonneg, ← ENNReal.ofReal_ofNat 4,
        ← ENNReal.ofReal_mul (by norm_num)]
    · rw [Set.indicator_of_mem hS]
      exact le_add_left (Probability.PMF.toOuterMeasure_le_one _ _)
  have hbound : ((budgetedMoserTardos B vbl r est).pairedOutput D).toOuterMeasure
      {q | q.1 ≠ q.2} ≤ 4 * ∑ v, e v + μ.toOuterMeasure goodᶜ := by
    rw [budgetedMoserTardos, Algorithm.pairedOutput_deterministic_eq_samples,
      PMF.toOuterMeasure_bind_apply]
    calc ∑' S₁, μ S₁ * (μ.bind fun S₂ =>
            (Probability.PMF.uniformOfFintype (BudgetSeed α L B)).map fun σ =>
              (budgetedOutput vbl r B (seedTable B (est S₁) σ),
                budgetedOutput vbl r B (seedTable B (est S₂) σ))).toOuterMeasure {q | q.1 ≠ q.2}
        ≤ ∑' S₁, μ S₁ * ∑' S₂, μ S₂ *
            (4 * ∑ v, ENNReal.ofReal (dist (est S₁ v).toPMF (est S₂ v).toPMF) +
              goodᶜ.indicator 1 S₁) := by
          refine tsum_le_tsum fun S₁ => ?_
          gcongr
          rw [PMF.toOuterMeasure_bind_apply]
          exact tsum_le_tsum fun S₂ => by gcongr; exact hpair S₁ S₂
      _ = 4 * ∑ v, e v + μ.toOuterMeasure goodᶜ := by
          simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
            PMF.toOuterMeasure_apply]
          congr 1
          · simp only [e, mul_sum, ← ENNReal.tsum_mul_left]
            rw [← Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable]
            refine tsum_congr fun S₁ => ?_
            rw [← Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable]
            refine tsum_congr fun S₂ => sum_congr rfl fun v _ => ?_
            ring
          · refine tsum_congr fun S => ?_
            by_cases hSg : S ∈ goodᶜ <;> simp [Set.indicator, hSg]
  have hfin₁ : 4 * ∑ v, e v ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.sum_ne_top.2 fun v _ => (he v).1)
  rw [Algorithm.disagreeProb]
  refine (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin₁, Probability.PMF.toOuterMeasure_ne_top
    _ _⟩) hbound).trans_eq ?_
  rw [ENNReal.toReal_add hfin₁ (Probability.PMF.toOuterMeasure_ne_top _ _),
    ENNReal.toReal_mul, ENNReal.toReal_sum fun v _ => (he v).1, ENNReal.toReal_ofNat]
  simp only [fun v => (he v).2]
  rfl

end Seed

end Cslib.MachineLearning.Replicable
