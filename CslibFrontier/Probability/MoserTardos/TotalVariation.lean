/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.MoserTardos.Coupling
import CslibFrontier.Foundations.Probability.InfinitePi
import CslibFrontier.Probability.StatisticalDistance.OptimalCoupling

/-!
# The output law of the Moser–Tardos algorithm is stable under perturbation

The output of a Moser–Tardos run with a non-anticipating rule (`historyRule`) is the assignment at
which the rule stops, or `none` if it never stops (`output`). Its law under the resampling table
of a family of distributions `P` is the output law `outputLaw vbl r P`, a distribution on
`Option (∀ v, α v)`. Under the local-lemma hypothesis it puts no mass on `none`
(`outputLaw_none`), and for a rule that stops only when no event occurs it puts mass only on
assignments avoiding every event (`outputLaw_some_eq_zero`).

Coupling two runs entry by entry, the output laws are at statistical distance at most the
divergence probability (`dist_outputLaw_le`). With an optimal coupling at each entry, whose
disagreement probability is exactly `d_TV(P v, Q v)`
(`Cslib.Probability.PMF.exists_coupling_toReal_eq_dist`), and the first-disagreement bound in the
symmetric case `e p (d + 1) ≤ 1` (`coupledTable_diverge_le_two_mul`), this gives
`d_TV(MT(P), MT(Q)) ≤ 2 ∑ v, d_TV(P v, Q v)` (`dist_outputLaw_le_two_mul`).

The statement and its proof route are original (cslib-frontier issue #6718).

## Main definitions

* `Cslib.Probability.MoserTardos.output`: the output of a run, `none` if the run never stops.
* `Cslib.Probability.MoserTardos.outputLaw`: the law of the output under the resampling table.

## Main results

* `Cslib.Probability.MoserTardos.output_eq_some_iff`: the run outputs `a` exactly when it stops at
  some step with current assignment `a`.
* `Cslib.Probability.MoserTardos.outputLaw_none`: under the local-lemma hypothesis the run
  terminates almost surely.
* `Cslib.Probability.MoserTardos.outputLaw_some_eq_zero`: a rule that stops only when no event
  occurs outputs only good assignments.
* `Cslib.Probability.MoserTardos.dist_outputLaw_le`: the coupling inequality for two coupled runs.
* `Cslib.Probability.MoserTardos.dist_outputLaw_le_two_mul`: the total-variation bound
  `d_TV(MT(P), MT(Q)) ≤ 2 ∑ v, d_TV(P v, Q v)`.

## Implementation notes

Only the first family `P` needs the local-lemma hypothesis in `dist_outputLaw_le_two_mul`: the
output `none` records non-termination, so two runs that never diverge have equal outputs whether
or not they stop. The bound is the companion of `correlated_diverge_le`. Optimal couplings halve
the constant `4`, but they depend on both distributions, so they do not give a protocol in which
each run knows only its own distribution.

## References

* [R. A. Moser, G. Tardos, *A constructive proof of the general Lovász Local Lemma*]
  [MoserTardos2010]
-/

public section

namespace Cslib.Probability.MoserTardos

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal Cslib.Probability.PMF

section Output

variable {V ι : Type*} [DecidableEq V] {α : V → Type*} (vbl : ι → Finset V)
  (r : List ι → (∀ v, α v) → Option ι)

omit [DecidableEq V] in
/-- Once the rule stops, the log stays fixed. -/
theorem run_eq_of_eq_none {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    {T : ∀ p : V × ℕ, α p.1} {m : ℕ} (h : sel T (run sel T m) = none) {n : ℕ} (hmn : m ≤ n) :
    run sel T n = run sel T m := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n _ ih => rw [run_succ_of_eq_none (ih ▸ h), ih]

open scoped Classical in
/-- The **output** of the run of `historyRule r` on the table `T`: the assignment at the first step
at which the rule stops, or `none` if it never stops. -/
noncomputable def output (T : ∀ p : V × ℕ, α p.1) : Option (∀ v, α v) :=
  if h : ∃ n, historyRule vbl r T (run (historyRule vbl r) T n) = none then
    some (current vbl T (run (historyRule vbl r) T (Nat.find h)))
  else none

variable {vbl r}

/-- The run outputs `a` exactly when the rule stops at some step with current assignment `a`. -/
theorem output_eq_some_iff {T : ∀ p : V × ℕ, α p.1} {a : ∀ v, α v} :
    output vbl r T = some a ↔ ∃ n, historyRule vbl r T (run (historyRule vbl r) T n) = none ∧
      current vbl T (run (historyRule vbl r) T n) = a := by
  classical
  unfold output
  split_ifs with h
  · rw [Option.some_inj]
    refine ⟨fun ha => ⟨Nat.find h, Nat.find_spec h, ha⟩, fun ⟨n, hstop, hn⟩ => ?_⟩
    rw [← hn, run_eq_of_eq_none (Nat.find_spec h) (Nat.find_min' h hstop)]
  · exact ⟨fun h' => absurd h' (by simp), fun ⟨n, hn, _⟩ => absurd ⟨n, hn⟩ h⟩

/-- The run outputs `none` exactly when the rule never stops. -/
theorem output_eq_none_iff {T : ∀ p : V × ℕ, α p.1} :
    output vbl r T = none ↔ ∀ n, historyRule vbl r T (run (historyRule vbl r) T n) ≠ none := by
  classical
  unfold output
  split_ifs with h
  · exact ⟨fun h' => absurd h' (by simp), fun h' => absurd h (not_exists.2 fun n hn => h' n hn)⟩
  · exact ⟨fun _ n hn => h ⟨n, hn⟩, fun _ => rfl⟩

/-- The log and the current assignment after `n` steps depend only on the entries `(v, k)` with
`k ≤ n`. -/
theorem dependsOn_run_current [Fintype V] (n : ℕ) :
    DependsOn (fun T : ∀ p : V × ℕ, α p.1 =>
        (run (historyRule vbl r) T n, current vbl T (run (historyRule vbl r) T n)))
      ((univ ×ˢ range (n + 1) : Finset (V × ℕ)) : Set (V × ℕ)) := by
  intro T T' h
  have hmem : ∀ (m : ℕ) (u : V), m ≤ n →
      ((u, uses vbl (run (historyRule vbl r) T m) u) : V × ℕ) ∈
        ((univ ×ˢ range (n + 1) : Finset (V × ℕ)) : Set (V × ℕ)) := fun m u hm => by
    have := (uses_le_length (vbl := vbl) (run (historyRule vbl r) T m) u).trans
      (length_run_le _ T m)
    simp only [coe_product, coe_univ, coe_range, Set.mem_prod, Set.mem_univ, Set.mem_Iio,
      true_and]
    omega
  have hrun : run (historyRule vbl r) T n = run (historyRule vbl r) T' n :=
    run_eq_of_agree r n fun m hm u => h _ (hmem m u hm.le)
  refine Prod.ext hrun (funext fun u => ?_)
  simp only [current_apply, ← hrun]
  exact h _ (hmem n u le_rfl)

variable [∀ v, MeasurableSpace (α v)] [∀ v, Countable (α v)] [∀ v, MeasurableSingletonClass (α v)]

/-- Every fibre of the output is measurable. -/
theorem measurableSet_output_preimage [Finite V] (o : Option (∀ v, α v)) :
    MeasurableSet (output vbl r ⁻¹' {o}) := by
  have := Fintype.ofFinite V
  have hstep : ∀ (n : ℕ) (s : Set (List ι × ∀ v, α v)), MeasurableSet
      {T : ∀ p : V × ℕ, α p.1 |
        (run (historyRule vbl r) T n, current vbl T (run (historyRule vbl r) T n)) ∈ s} :=
    fun n s => measurableSet_of_dependsOn (S := univ ×ˢ range (n + 1)) fun T T' h => by
      exact congrArg (· ∈ s) (dependsOn_run_current (vbl := vbl) (r := r) n h)
  cases o with
  | none =>
    have : output vbl r ⁻¹' {none} = ⋂ n, {T : ∀ p : V × ℕ, α p.1 |
        (run (historyRule vbl r) T n, current vbl T (run (historyRule vbl r) T n)) ∈
          {x | r x.1 x.2 ≠ none}} := by
      ext T
      simp only [Set.mem_preimage, Set.mem_singleton_iff, output_eq_none_iff, Set.mem_iInter,
        Set.mem_ofPred_eq, historyRule]
    rw [this]
    exact MeasurableSet.iInter fun n => hstep n _
  | some a =>
    have : output vbl r ⁻¹' {some a} = ⋃ n, {T : ∀ p : V × ℕ, α p.1 |
        (run (historyRule vbl r) T n, current vbl T (run (historyRule vbl r) T n)) ∈
          {x | r x.1 x.2 = none ∧ x.2 = a}} := by
      ext T
      simp only [Set.mem_preimage, Set.mem_singleton_iff, output_eq_some_iff, Set.mem_iUnion,
        Set.mem_ofPred_eq, historyRule]
    rw [this]
    exact MeasurableSet.iUnion fun n => hstep n _

omit [∀ v, MeasurableSpace (α v)] [∀ v, Countable (α v)] [∀ v, MeasurableSingletonClass (α v)] in
/-- Two coupled runs that do not diverge have the same output. -/
theorem output_eq_of_not_diverge {T : ∀ p : V × ℕ, α p.1 × α p.1} (hT : ¬Diverge vbl r T) :
    output vbl r (fstTable T) = output vbl r (sndTable T) := by
  simp only [Diverge, not_exists, not_or, not_not] at hT
  refine Option.ext fun a => ?_
  simp only [output_eq_some_iff, historyRule]
  refine exists_congr fun n => ?_
  rw [(hT n).2, (hT n).1]

end Output

section Law

variable {Ω β : Type*} [MeasurableSpace Ω] [Fintype β]

/-- **Coupling inequality for measures.** If `p` and `q` are the laws of two finite-valued
functions `f` and `g` on one probability space, their statistical distance is at most the
probability that `f` and `g` differ. -/
private theorem dist_le_measure_ne (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → β)
    (hf : ∀ b, MeasurableSet (f ⁻¹' {b})) (hg : ∀ b, MeasurableSet (g ⁻¹' {b})) (p q : PMF β)
    (hp : ∀ b, p b = μ (f ⁻¹' {b})) (hq : ∀ b, q b = μ (g ⁻¹' {b})) :
    dist p q ≤ (μ {x | f x ≠ g x}).toReal := by
  let _ : MeasurableSpace β := ⊤
  set F : Ω → β × β := fun x => (f x, g x)
  have hF : Measurable F := (measurable_to_countable' hf).prodMk (measurable_to_countable' hg)
  set ω := (μ.map F).toPMF
  have hω : ∀ s, ω.toOuterMeasure s = μ (F ⁻¹' s) := fun s => by
    rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (Set.to_countable s).measurableSet,
      Measure.toPMF_toMeasure, Measure.map_apply hF (Set.to_countable s).measurableSet]
  have h1 : ω.map Prod.fst = p := PMF.ext fun b => by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply, hω, hp]
    rfl
  have h2 : ω.map Prod.snd = q := PMF.ext fun b => by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply, hω, hq]
    rfl
  rw [← h1, ← h2]
  refine (PMF.dist_map_map_le ω Prod.fst Prod.snd).trans_eq ?_
  rw [hω]
  rfl

end Law

section TotalVariation

variable {V ι : Type*} [Fintype V] [DecidableEq V] {α : V → Type*} [∀ v, Fintype (α v)]
  [∀ v, MeasurableSpace (α v)] [∀ v, MeasurableSingletonClass (α v)]
  (vbl : ι → Finset V) (r : List ι → (∀ v, α v) → Option ι)

/-- The **output law** of the Moser–Tardos run of `historyRule r` with the distributions `P`: the
law of `output vbl r` under the resampling table of `P`. -/
noncomputable def outputLaw (P : ∀ v, PMF (α v)) : PMF (Option (∀ v, α v)) :=
  PMF.ofFintype (fun o => table (fun v => (P v).toMeasure) (output vbl r ⁻¹' {o})) <| by
    rw [sum_measure_preimage_singleton univ fun o _ => measurableSet_output_preimage o, coe_univ,
      Set.preimage_univ, measure_univ]

theorem outputLaw_apply (P : ∀ v, PMF (α v)) (o : Option (∀ v, α v)) :
    outputLaw vbl r P o = table (fun v => (P v).toMeasure) (output vbl r ⁻¹' {o}) := by
  rw [outputLaw, PMF.ofFintype_apply]

/-- **Termination.** Under the local-lemma hypothesis, for a rule that only selects occurring
events, the output law puts no mass on non-termination. -/
theorem outputLaw_none [Finite ι] (P : ∀ v, PMF (α v)) (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi fun v => (P v).toMeasure).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    (hr : ∀ w a i, r w a = some i → a ∈ A i) :
    outputLaw vbl r P none = 0 := by
  rw [outputLaw_apply]
  refine measure_mono_null (fun T hT => ?_)
    (ae_iff.1 (ae_exists_run_eq_none _ vbl A (fun i => measurableSet_of_dependsOn (hA i)) hA Γ hΓ hx
      hP (historyRule_valid hr)))
  simp only [Set.mem_preimage, Set.mem_singleton_iff, output_eq_none_iff] at hT
  simpa only [Set.mem_ofPred_eq, not_exists] using hT

/-- **Good outputs.** A rule that stops only when no event occurs outputs only assignments
avoiding every event. -/
theorem outputLaw_some_eq_zero {A : ι → Set (∀ v, α v)}
    (hstop : ∀ w a, r w a = none → ∀ i, a ∉ A i) (P : ∀ v, PMF (α v)) {a : ∀ v, α v} {i : ι}
    (ha : a ∈ A i) : outputLaw vbl r P (some a) = 0 := by
  rw [outputLaw_apply]
  convert measure_empty (μ := table fun v => (P v).toMeasure)
  refine Set.eq_empty_of_forall_notMem fun T hT => ?_
  obtain ⟨n, hn, rfl⟩ := output_eq_some_iff.1 hT
  exact hstop _ _ hn i ha

/-- **Coupling inequality for Moser–Tardos runs.** If the coupling `κ v` has marginals `P v` and
`Q v`, the output laws of the runs with `P` and with `Q` are at statistical distance at most the
probability that the coupled runs diverge. -/
theorem dist_outputLaw_le (P Q : ∀ v, PMF (α v)) (κ : ∀ v, Measure (α v × α v))
    [∀ v, IsProbabilityMeasure (κ v)] (hκP : ∀ v, (κ v).map Prod.fst = (P v).toMeasure)
    (hκQ : ∀ v, (κ v).map Prod.snd = (Q v).toMeasure) :
    dist (outputLaw vbl r P) (outputLaw vbl r Q) ≤
      (coupledTable κ {T | Diverge vbl r T}).toReal := by
  have hfib : ∀ (t : (∀ p : V × ℕ, α p.1 × α p.1) → ∀ p : V × ℕ, α p.1), Measurable t →
      ∀ o, MeasurableSet ((output vbl r ∘ t) ⁻¹' {o}) :=
    fun t ht o => ht (measurableSet_output_preimage o)
  have hP : table (fun v => (P v).toMeasure) = (coupledTable κ).map fstTable := by
    rw [coupledTable_map_fstTable]
    exact congrArg table (funext fun v => (hκP v).symm)
  have hQ : table (fun v => (Q v).toMeasure) = (coupledTable κ).map sndTable := by
    rw [coupledTable_map_sndTable]
    exact congrArg table (funext fun v => (hκQ v).symm)
  refine (dist_le_measure_ne (coupledTable κ) (output vbl r ∘ fstTable) (output vbl r ∘ sndTable)
    (hfib _ measurable_fstTable) (hfib _ measurable_sndTable) _ _ (fun o => ?_)
    (fun o => ?_)).trans ?_
  · rw [outputLaw_apply, hP, Measure.map_apply measurable_fstTable
      (measurableSet_output_preimage o)]
    rfl
  · rw [outputLaw_apply, hQ, Measure.map_apply measurable_sndTable
      (measurableSet_output_preimage o)]
    rfl
  · refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun T hT => ?_)
    by_contra hd
    exact hT (output_eq_of_not_diverge hd)

/-- **Total-variation stability of Moser–Tardos (original).** Let `r` be a non-anticipating rule
that only selects occurring events. Suppose every event has at most `d` neighbours in `Γ` and
probability at most `p` under the product of the `P v`, with `e p (d + 1) ≤ 1`. Then the output
laws of the runs with `P` and with `Q` satisfy `d_TV(MT(P), MT(Q)) ≤ 2 ∑ v, d_TV(P v, Q v)`,
independently of `d` and of the number of events. No hypothesis on `Q` is needed: the output
`none` records non-termination. -/
theorem dist_outputLaw_le_two_mul [Finite ι] (P Q : ∀ v, PMF (α v)) (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i) {d : ℕ}
    (hΓd : ∀ i, (Γ i).card ≤ d) {p : ℝ}
    (hP : ∀ i, (Measure.pi fun v => (P v).toMeasure).real (A i) ≤ p)
    (hp : Real.exp 1 * p * (d + 1) ≤ 1) (hr : ∀ w a i, r w a = some i → a ∈ A i) :
    dist (outputLaw vbl r P) (outputLaw vbl r Q) ≤ 2 * ∑ v, dist (P v) (Q v) := by
  choose ω hω₁ hω₂ hω₃ using fun v => PMF.exists_coupling_toReal_eq_dist (P v) (Q v)
  have hκP : ∀ v, (ω v).toMeasure.map Prod.fst = (P v).toMeasure := fun v => by
    rw [PMF.toMeasure_map (p := ω v) (hf := measurable_fst), hω₁]
  have hκQ : ∀ v, (ω v).toMeasure.map Prod.snd = (Q v).toMeasure := fun v => by
    rw [PMF.toMeasure_map (p := ω v) (hf := measurable_snd), hω₂]
  have hP' : ∀ i, (Measure.pi fun v => (ω v).toMeasure.map Prod.fst).real (A i) ≤ p :=
    fun i => by simpa only [hκP] using hP i
  have hdis : ∀ v, (ω v).toMeasure {x | x.1 ≠ x.2} = ENNReal.ofReal (dist (P v) (Q v)) :=
    fun v => by
      rw [← hω₃, ← PMF.toMeasure_apply_eq_toOuterMeasure, ENNReal.ofReal_toReal
        (measure_ne_top _ _)]
  refine (dist_outputLaw_le vbl r P Q _ hκP hκQ).trans ?_
  have h := coupledTable_diverge_le_two_mul _ vbl r A (fun i => measurableSet_of_dependsOn (hA i))
    hA Γ hΓ hΓd hP' hp hr
  simp only [hdis] at h
  rw [← ENNReal.ofReal_sum_of_nonneg fun v _ => dist_nonneg, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num)] at h
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg zero_le_two (sum_nonneg fun v _ => dist_nonneg)) h

end TotalVariation

end Cslib.Probability.MoserTardos
