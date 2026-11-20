/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Probability.MoserTardos.Coupling

/-! Coupled Moser–Tardos runs.

* A concrete run of a non-anticipating rule on one coin. The event "the coin shows `true`" is
  resampled until the table gives `false`. On the table `true, true, false, …` the run reads
  three samples and stops after two resamplings, which `decide` computes.
* Two tables that differ only at an entry the run never reads give the same log
  (`run_eq_of_agree`).
* With no perturbation (`P = Q`), correlated sampling makes the two runs never diverge
  (`correlated_diverge_le`), and they output the same good assignment
  (`correlated_not_agreeGood_le`).
* The symmetric weight bound for `d = 0`.
* On a table where the coin always shows `true`, the run never stops, so the termination of the
  second run needs the local-lemma hypothesis for its own distributions
  (`coupledTable_ae_terminate`).
* The divergence and output bounds need the local-lemma hypothesis for the first run. If both
  runs sample a coin that always shows `true`, the runs never diverge, so the bound of
  `correlated_not_agreeGood_le` is `0`. But neither run stops, so the runs fail to output a
  common good assignment with probability `1`. If the first coin always shows `true` and the
  coupling makes the second show `false` with probability `1 / 8`, the bound of
  `coupledTable_diverge_le_two_mul` is `1 / 4`, but the runs diverge almost surely. -/

set_option linter.privateModule false

namespace CslibFrontierTests.MoserTardosCoupling

open Cslib.Probability.MoserTardos MeasureTheory
open scoped ENNReal

/-- The single event reads the single variable. -/
def vbl : Unit → Finset Unit := fun _ => {()}

/-- Resample while the coin shows `true`. -/
def r : List Unit → (Unit → Bool) → Option Unit :=
  fun _ a => if a () then some () else none

/-- The table `true, true, false, false, …`. -/
def T₀ : ∀ _ : Unit × ℕ, Bool := fun p => decide (p.2 < 2)

/-- `T₀` with entry `k = 5` flipped. -/
def T₁ : ∀ _ : Unit × ℕ, Bool := fun p => if p.2 = 5 then true else decide (p.2 < 2)

/-- The run resamples twice and stops. -/
example : run (historyRule vbl r) T₀ 4 = [(), ()] := by decide

/-- It reads samples `0`, `1` and `2` only. -/
example : ∀ n < 4, uses vbl (run (historyRule vbl r) T₀ n) () ≤ 2 := by decide

/-- Without the local-lemma hypothesis, a run need not stop: on the all-`true` table (the table of
a coin that always shows `true`) the rule resamples forever. -/
example (n : ℕ) :
    historyRule vbl r (fun _ => true) (run (historyRule vbl r) (fun _ => true) n) = some () := by
  simp [historyRule, r, current_apply]

/-- Flipping an entry the run never reads does not change the run. -/
example : run (historyRule vbl r) T₀ 4 = run (historyRule vbl r) T₁ 4 :=
  run_eq_of_agree r 4 fun m hm u => by
    cases u
    have : uses vbl (run (historyRule vbl r) T₀ m) () ≠ 5 := by
      interval_cases m <;> decide
    simp [T₀, T₁, this]

open scoped Cslib.Probability.PMF in
/-- **No perturbation, no divergence.** If both runs sample from the same distributions, the
correlated-sampling coupling makes them identical almost surely. -/
example {V ι : Type*} [Fintype V] [DecidableEq V] [Finite ι] {α : V → Type*}
    [∀ v, Fintype (α v)] [∀ v, MeasurableSpace (α v)] [∀ v, MeasurableSingletonClass (α v)]
    (P : ∀ v, PMF (α v)) (vbl : ι → Finset V) (r : List ι → (∀ v, α v) → Option ι)
    (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) (Γ : ι → Finset ι)
    (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i) {d : ℕ}
    (hΓd : ∀ i, (Γ i).card ≤ d) {p : ℝ}
    (hP : ∀ i, (Measure.pi fun v => (P v).toMeasure).real (A i) ≤ p)
    (hp : Real.exp 1 * p * (d + 1) ≤ 1) (hr : ∀ w a i, r w a = some i → a ∈ A i) :
    coupledTable (correlatedCoupling P P) {T | Diverge vbl r T} = 0 := by
  refine le_antisymm ?_ bot_le
  simpa using correlated_diverge_le P P vbl r A hAm hA Γ hΓ hΓd hP hp hr

open scoped Cslib.Probability.PMF in
/-- **No perturbation, same good output.** With the same distributions and a rule that stops only
when no event occurs, the two runs almost surely output the same assignment avoiding every
event. -/
example {V ι : Type*} [Fintype V] [DecidableEq V] [Finite ι] {α : V → Type*}
    [∀ v, Fintype (α v)] [∀ v, MeasurableSpace (α v)] [∀ v, MeasurableSingletonClass (α v)]
    (P : ∀ v, PMF (α v)) (vbl : ι → Finset V) (r : List ι → (∀ v, α v) → Option ι)
    (A : ι → Set (∀ v, α v)) (hAm : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) (Γ : ι → Finset ι)
    (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i) {d : ℕ}
    (hΓd : ∀ i, (Γ i).card ≤ d) {p : ℝ}
    (hP : ∀ i, (Measure.pi fun v => (P v).toMeasure).real (A i) ≤ p)
    (hp : Real.exp 1 * p * (d + 1) ≤ 1) (hr : ∀ w a i, r w a = some i → a ∈ A i)
    (hstop : ∀ w a, r w a = none → ∀ i, a ∉ A i) :
    coupledTable (correlatedCoupling P P) {T | ¬AgreeGood vbl r A T} = 0 := by
  refine le_antisymm ?_ bot_le
  simpa using correlated_not_agreeGood_le P P vbl r A hAm hA Γ hΓ hΓd hP hp hr hstop

/-! ### The local-lemma hypothesis on `P` is needed

The divergence and output bounds assume the local-lemma hypothesis for the first run's
distributions. Without it they fail, already on one coin. -/

/-- The event "the coin shows `true`". -/
def A : Unit → Set (Unit → Bool) := fun _ => {a | a () = true}

theorem uses_replicate (n : ℕ) : uses vbl (List.replicate n ()) () = n := by
  simp [uses, vbl]

/-- On a table whose first `k` samples show `true`, the first `n ≤ k` steps resample every
time. -/
theorem run_eq_replicate (T : ∀ _ : Unit × ℕ, Bool) (k : ℕ) (hT : ∀ j < k, T ((), j) = true) :
    ∀ n ≤ k, run (historyRule vbl r) T n = List.replicate n ()
  | 0, _ => run_zero _ _
  | n + 1, hn => by
    have ih := run_eq_replicate T k hT n (by omega)
    rw [run_succ_of_eq_some (i := ()), ih, List.replicate_succ]
    simp [historyRule, r, ih, current_apply, uses_replicate, hT n (by omega)]

/-- If the runs output the same good assignment, the first table shows `false` somewhere. -/
theorem exists_fst_false_of_agreeGood {T : ∀ _ : Unit × ℕ, Bool × Bool}
    (h : AgreeGood vbl r A T) : ∃ k, (T ((), k)).1 = false := by
  obtain ⟨n, hn, -⟩ := h
  refine ⟨uses vbl (run (historyRule vbl r) (fstTable (α := fun _ => Bool) T) n) (), ?_⟩
  simpa [historyRule, r, current_apply, fstTable] using hn

/-- The probability that the coupled table has a given property at entry `k`. -/
theorem coupledTable_entry (κ : Unit → Measure (Bool × Bool)) [∀ v, IsProbabilityMeasure (κ v)]
    (k : ℕ) (s : Set (Bool × Bool)) :
    coupledTable κ {T | T ((), k) ∈ s} = κ () s := by
  rw [coupledTable_def, show {T : ∀ _ : Unit × ℕ, Bool × Bool | T ((), k) ∈ s} =
      (fun T => T ((), k)) ⁻¹' s from rfl,
    ← Measure.map_apply (measurable_pi_apply ((), k)) (Set.toFinite s).measurableSet,
    Measure.infinitePi_map_eval]

/-- If the first sample is almost surely `true`, the coupled table almost surely shows `true` in
every first entry. -/
theorem ae_fst_true (κ : Unit → Measure (Bool × Bool)) [∀ v, IsProbabilityMeasure (κ v)]
    (h : κ () {x | x.1 = false} = 0) :
    ∀ᵐ T ∂coupledTable κ, ∀ k, (T ((), k)).1 = true := by
  rw [ae_all_iff]
  intro k
  rw [ae_iff]
  simp only [Bool.not_eq_true]
  exact (coupledTable_entry κ k {x | x.1 = false}).trans h

open scoped Cslib.Probability.PMF in
/-- **Same distributions, no common good output.** Let both runs sample a coin that always shows
`true`. Correlated sampling gives identical samples, so the runs never diverge and the bound of
`correlated_not_agreeGood_le` would be `4 · 0 = 0`. But neither run ever stops, so they fail to
output a common good assignment with probability `1`. -/
example :
    let P : Unit → PMF Bool := fun _ => PMF.pure true
    coupledTable (correlatedCoupling P P) {T | ¬AgreeGood vbl r A T} = 1 ∧
      ENNReal.ofReal (4 * ∑ v, dist (P v) (P v)) = 0 := by
  intro P
  refine ⟨le_antisymm prob_le_one ?_, by simp⟩
  have hfst : correlatedCoupling P P () {x | x.1 = false} = 0 := by
    rw [show {x : Bool × Bool | x.1 = false} = Prod.fst ⁻¹' {false} from rfl,
      ← Measure.map_apply measurable_fst (Set.toFinite _).measurableSet,
      correlatedCoupling_map_fst (α := fun _ => Bool)]
    simp [P, PMF.toMeasure_pure]
  have hgood : coupledTable (correlatedCoupling P P) {T | AgreeGood vbl r A T} = 0 :=
    measure_mono_null_ae ((ae_fst_true _ hfst).mono fun T hT hg => by
      obtain ⟨k, hk⟩ := exists_fst_false_of_agreeGood hg
      simp [hT k] at hk) measure_empty
  calc (1 : ℝ≥0∞) = coupledTable (correlatedCoupling P P) Set.univ := measure_univ.symm
    _ ≤ coupledTable (correlatedCoupling P P) ({T | ¬AgreeGood vbl r A T} ∪
          {T | AgreeGood vbl r A T}) :=
        measure_mono fun T _ => (em' (AgreeGood vbl r A T)).elim Or.inl Or.inr
    _ ≤ _ := (measure_union_le _ _).trans (by rw [hgood, add_zero])

/-- A coupling of a coin that always shows `true` with one that shows `false` with
probability `1 / 8`: the samples disagree exactly when the second shows `false`. -/
noncomputable def κ : Unit → Measure (Bool × Bool) :=
  fun _ => (7 / 8 : ℝ≥0∞) • Measure.dirac (true, true) +
    (1 / 8 : ℝ≥0∞) • Measure.dirac (true, false)

instance (v : Unit) : IsProbabilityMeasure (κ v) := ⟨by
  simp only [κ, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.add_div, show (7 : ℝ≥0∞) + 1 = 8 by norm_num]
  exact ENNReal.div_self (by norm_num) (by norm_num)⟩

/-- **The divergence bound fails.** For the coupling `κ`, the samples disagree with probability
`1 / 8`, so `coupledTable_diverge_le_two_mul` would bound the divergence probability by `1 / 4`.
But the first run resamples forever, and the second stops at its first `false`, so the runs
diverge almost surely. -/
example : coupledTable κ {T | Diverge vbl r T} = 1 ∧ ∑ v, κ v {x | x.1 ≠ x.2} = 1 / 8 := by
  refine ⟨le_antisymm prob_le_one ?_, by simp [κ]⟩
  have hfst := ae_fst_true κ (by simp [κ])
  -- Almost surely, the second table shows `false` somewhere.
  have hsnd : ∀ᵐ T ∂coupledTable κ, ∃ k, (T ((), k)).2 = false := by
    rw [ae_iff]
    refine le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (r := 7 / 8) ?_) fun N => ?_) bot_le
    · rw [ENNReal.div_lt_iff (by norm_num) (by norm_num), one_mul]
      norm_num
    calc coupledTable κ {T | ¬∃ k, (T ((), k)).2 = false}
        ≤ coupledTable κ (Set.pi ((Finset.range N).image fun k => ((), k))
            fun _ => {x | x.2 = true}) :=
          measure_mono fun T hT p hp => by
            simp only [not_exists, Bool.not_eq_false, Set.mem_ofPred_eq] at hT
            simpa using hT p.2
      _ = (7 / 8) ^ N := by
          rw [coupledTable_def, Measure.infinitePi_pi (X := fun _ : Unit × ℕ => Bool × Bool)
              (μ := fun p => κ p.1) fun _ _ => (Set.toFinite _).measurableSet,
            Finset.prod_image (by simp)]
          simp [κ]
  refine le_of_eq_of_le measure_univ.symm (measure_mono_ae ((hfst.and hsnd).mono ?_))
  rintro T ⟨h1, h2⟩ -
  classical
  set k := Nat.find h2
  have hk : (T ((), k)).2 = false := Nat.find_spec h2
  have hlt : ∀ j < k, sndTable (α := fun _ => Bool) T ((), j) = true := fun j hj => by
    simpa [sndTable] using Nat.find_min h2 hj
  have hrun1 := run_eq_replicate (fstTable (α := fun _ => Bool) T) k (fun j _ => h1 j) k le_rfl
  have hrun2 := run_eq_replicate (sndTable (α := fun _ => Bool) T) k hlt k le_rfl
  refine ⟨k, Or.inr fun h => ?_⟩
  have := congrFun h ()
  simp [hrun1, hrun2, current_apply, uses_replicate, fstTable, sndTable, h1 k, hk] at this

/-- With no neighbours, `e p ≤ 1` gives `p ≤ 1 / 2`. -/
example {p : ℝ} (hp : Real.exp 1 * p * (0 + 1) ≤ 1) : p ≤ 1 / 2 := by
  simpa using le_weight_of_exp_mul_le 0 (by simpa using hp)

end CslibFrontierTests.MoserTardosCoupling
