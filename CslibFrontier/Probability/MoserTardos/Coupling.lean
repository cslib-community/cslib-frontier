/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.CorrelatedSampling
public import CslibFrontier.Probability.MoserTardos
import CslibFrontier.Foundations.Probability.InfinitePi
import CslibFrontier.Probability.PMF.Event
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Coupled runs of the Moser–Tardos algorithm

Two runs of the Moser–Tardos algorithm, one on a table of samples from `μ` and one on a table of
samples from `ν`, can share randomness: give each table entry `(v, k)` a pair of samples drawn
from a coupling of `μ v` and `ν v`, independently for each entry. If the selection rule is
*non-anticipating*, meaning it sees only the log and the current assignment
(`Cslib.Probability.MoserTardos.historyRule`), then the two runs stay identical for as long as the
entries the first run reads agree (`run_eq_of_agree`). So the runs can differ only if some entry
read by the first run is a disagreeing pair.

Whether the first run ever reads entry `(v, k)` does not depend on that entry
(`dependsOn_le_uses`), so it is independent of whether the pair at `(v, k)` disagrees. A
union bound over the entries read then bounds the probability that the runs differ by
`∑ v, η v · E[N v]` (`coupledTable_diverge_le`), where `η v` is the disagreement probability of the
coupling at `v` and `N v` is the number of samples of `v` that the first run reads. The bound
counts samples actually read: comparing the two infinite tables would not work, since some entry
eventually disagrees.

When the rule stops only once no event occurs, the first run almost surely stops at a good
assignment, and away from divergence the second run stops at the same step with the same
assignment. So the two runs output the same assignment avoiding every event except with the
divergence probability (`coupledTable_not_agreeGood_le`, `correlated_not_agreeGood_le`).

The statement and its proof route are original (cslib-frontier issue #6718).

## Main definitions

* `Cslib.Probability.MoserTardos.historyRule`: the selection rule given by a function of the log
  and the current assignment.
* `Cslib.Probability.MoserTardos.coupledTable`: a table of independent coupled pairs, with
  `fstTable` and `sndTable` the two runs' tables.
* `Cslib.Probability.MoserTardos.Diverge`: the two runs' logs or assignments differ at some step.
* `Cslib.Probability.MoserTardos.AgreeGood`: both runs stop at the same step with the same
  assignment, which avoids every event.
* `Cslib.Probability.MoserTardos.correlatedCoupling`: the coupling given by correlated sampling.

## Main results

* `Cslib.Probability.MoserTardos.run_eq_of_agree`: tables that agree on the entries read by the
  first `n` steps give the same log after `n` steps.
* `Cslib.Probability.MoserTardos.dependsOn_le_uses`: whether entry `(v, k)` has been read after
  `n` steps does not depend on that entry.
* `Cslib.Probability.MoserTardos.coupledTable_diverge_le`: the first-disagreement bound
  `Pr[diverge] ≤ ∑ v, η v · E[N v]`.
* `Cslib.Probability.MoserTardos.coupledTable_diverge_le_of_lll`: with the local-lemma
  hypothesis, `E[N v] ≤ 1 + ∑_{i ∋ v} x i / (1 - x i)`.
* `Cslib.Probability.MoserTardos.coupledTable_diverge_le_two_mul`: in the symmetric case
  `e p (d + 1) ≤ 1`, `Pr[diverge] ≤ 2 ∑ v, η v`.
* `Cslib.Probability.MoserTardos.correlated_diverge_le`: with correlated sampling,
  `Pr[diverge] ≤ 4 ∑ v, d_TV(P v, Q v)`.
* `Cslib.Probability.MoserTardos.coupledTable_not_agreeGood_le`: for a rule that stops only when
  no event occurs, the runs fail to output the same good assignment with probability at most
  `Pr[diverge]`.
* `Cslib.Probability.MoserTardos.correlated_not_agreeGood_le`: with correlated sampling, the runs
  output the same good assignment except with probability `4 ∑ v, d_TV(P v, Q v)`.
* `Cslib.Probability.MoserTardos.coupledTable_ae_terminate`,
  `Cslib.Probability.MoserTardos.correlated_ae_terminate`: if both runs' distributions satisfy the
  local-lemma hypothesis, both runs stop almost surely.

## Implementation notes

The coordinates take values in countable types with the discrete measurable structure, so every
event determined by finitely many table entries is measurable (by a private lemma) and the rule
needs no measurability assumption. The event `AgreeGood` need not be measurable; its complement
is bounded through `measure_mono_ae`, which holds for outer measure. The seed of
`correlatedCoupling` is the library's finite correlated sampling, whose law is built from both
`P v` and `Q v`. A protocol in which each party needs only its own distribution is milestone 2 of
#6718. The divergence and output bounds use no hypothesis on `Q`: they need only the first run's
expected sample counts, and the second run stops whenever the runs agree. Almost-sure termination
of both runs (`coupledTable_ae_terminate`) does need the local-lemma hypothesis for `Q` as well.

## References

* [R. A. Moser, G. Tardos, *A constructive proof of the general Lovász Local Lemma*]
  [MoserTardos2010]
* [T. Holenstein, *Parallel repetition: simplifications and the no-signaling case*]
  [Holenstein2009]
-/

public section

namespace Cslib.Probability.MoserTardos

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

section Rule

variable {V ι : Type*} [DecidableEq V] {α : V → Type*} (vbl : ι → Finset V)

/-- The **non-anticipating** selection rule given by `r`: after the log `w`, it selects
`r w a`, where `a` is the current assignment. Unlike a general rule, it cannot read table entries
the algorithm has not yet used. -/
@[expose] def historyRule (r : List ι → (∀ v, α v) → Option ι) :
    (∀ p : V × ℕ, α p.1) → List ι → Option ι :=
  fun T w => r w (current vbl T w)

variable {vbl}

/-- A valid `r`, one that only selects events occurring in the given assignment, gives a valid
selection rule. -/
theorem historyRule_valid {A : ι → Set (∀ v, α v)} {r : List ι → (∀ v, α v) → Option ι}
    (hr : ∀ w a i, r w a = some i → a ∈ A i) :
    ∀ T w i, historyRule vbl r T w = some i → current vbl T w ∈ A i :=
  fun _ _ _ h => hr _ _ _ h

/-- How often `v` has been resampled: the number of steps of `w` on events containing `v`. -/
theorem uses_eq_sum_count [Fintype ι] [DecidableEq ι] (w : List ι) (v : V) :
    uses vbl w v = ∑ i ∈ univ.filter (fun i => v ∈ vbl i), w.count i := by
  induction w with
  | nil => simp [uses_nil]
  | cons j w ih =>
    rw [uses_cons, ih]
    simp only [List.count_cons, beq_iff_eq, sum_add_distrib]
    rw [sum_ite_eq]
    simp

omit [DecidableEq V] in
/-- The log after `n` steps has at most `n` entries. -/
theorem length_run_le (sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι) (T : ∀ p : V × ℕ, α p.1) :
    ∀ n, (run sel T n).length ≤ n
  | 0 => by simp [run_zero]
  | n + 1 => by
    cases h : sel T (run sel T n) with
    | none => rw [run_succ_of_eq_none h]; exact (length_run_le sel T n).trans n.le_succ
    | some i =>
      rw [run_succ_of_eq_some h, List.length_cons]
      exact Nat.succ_le_succ (length_run_le sel T n)

/-- A variable is resampled at most as often as there are steps. -/
theorem uses_le_length (w : List ι) (v : V) : uses vbl w v ≤ w.length := by
  unfold uses
  exact List.length_filter_le _ _

/-- The number of resamplings of a variable grows along the run. -/
theorem uses_run_mono (sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι) (T : ∀ p : V × ℕ, α p.1)
    (v : V) : Monotone fun n => uses vbl (run sel T n) v := by
  refine monotone_nat_of_le_succ fun n => ?_
  cases h : sel T (run sel T n) with
  | none => rw [run_succ_of_eq_none h]
  | some i => rw [run_succ_of_eq_some h, uses_cons]; exact Nat.le_add_right _ _

/-- **Agreement.** Under a non-anticipating rule, two tables that agree on every entry read by the
first `n` steps on `T` give the same log after `n` steps. -/
theorem run_eq_of_agree (r : List ι → (∀ v, α v) → Option ι) {T T' : ∀ p : V × ℕ, α p.1} :
    ∀ n, (∀ m < n, ∀ u, T (u, uses vbl (run (historyRule vbl r) T m) u) =
      T' (u, uses vbl (run (historyRule vbl r) T m) u)) →
      run (historyRule vbl r) T n = run (historyRule vbl r) T' n
  | 0, _ => by simp [run_zero]
  | n + 1, h => by
    have ih := run_eq_of_agree r n fun m hm => h m (Nat.lt_succ_of_lt hm)
    have hcur : current vbl T (run (historyRule vbl r) T n) =
        current vbl T' (run (historyRule vbl r) T' n) := by
      rw [← ih]
      funext u
      simp only [current_apply]
      exact h n (Nat.lt_succ_self n) u
    have hsel : historyRule vbl r T (run (historyRule vbl r) T n) =
        historyRule vbl r T' (run (historyRule vbl r) T' n) := by
      simp only [historyRule]
      rw [hcur, ← ih]
    simp only [run]
    rw [hsel, ih]

/-- The table entries read by the first `n + 1` steps, other than `(v, k)`. -/
@[expose] def horizon [Fintype V] (n : ℕ) (v : V) (k : ℕ) : Finset (V × ℕ) :=
  (univ ×ˢ range (n + 1)).erase (v, k)

/-- If `v` has been resampled fewer than `k` times after `m ≤ n` steps, the run so far has not read
entry `(v, k)`: tables that agree on `horizon n v k` give the same log after `m` steps. -/
theorem run_eq_of_agree_horizon [Fintype V] (r : List ι → (∀ v, α v) → Option ι)
    {T T' : ∀ p : V × ℕ, α p.1} {n m : ℕ} {v : V} {k : ℕ}
    (h : ∀ p ∈ horizon n v k, T p = T' p) (hm : m ≤ n)
    (hk : uses vbl (run (historyRule vbl r) T m) v < k) :
    run (historyRule vbl r) T m = run (historyRule vbl r) T' m := by
  refine run_eq_of_agree r m fun m' hm' u => h _ ?_
  have hle : uses vbl (run (historyRule vbl r) T m') u ≤ m' :=
    (uses_le_length _ u).trans (length_run_le _ T m')
  refine mem_erase.2 ⟨fun he => ?_, mem_product.2 ⟨mem_univ u, mem_range.2 (by omega)⟩⟩
  obtain ⟨rfl, he⟩ := Prod.mk.inj he
  have hmono : uses vbl (run (historyRule vbl r) T m') u ≤
      uses vbl (run (historyRule vbl r) T m) u :=
    uses_run_mono (historyRule vbl r) T u hm'.le
  omega

/-- **Reading `(v, k)` does not depend on `(v, k)`.** Whether `v` has been resampled at least `k`
times after `n` steps depends only on the entries in `horizon n v k`, which exclude `(v, k)`. -/
theorem dependsOn_le_uses [Fintype V] (r : List ι → (∀ v, α v) → Option ι) (n : ℕ) (v : V)
    (k : ℕ) :
    DependsOn (fun T : ∀ p : V × ℕ, α p.1 => k ≤ uses vbl (run (historyRule vbl r) T n) v)
      (horizon n v k : Set (V × ℕ)) := by
  intro T T' h
  have h' : ∀ p ∈ horizon n v k, T p = T' p := fun p hp => h p (mem_coe.2 hp)
  have h'' : ∀ p ∈ horizon n v k, T' p = T p := fun p hp => (h' p hp).symm
  refine propext ⟨fun hT => ?_, fun hT' => ?_⟩
  · by_contra hlt
    rw [not_le] at hlt
    rw [run_eq_of_agree_horizon r h'' le_rfl hlt] at hlt
    omega
  · by_contra hlt
    rw [not_le] at hlt
    rw [run_eq_of_agree_horizon r h' le_rfl hlt] at hlt
    omega

end Rule

section Measurable

variable {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] [∀ i, Countable (Ω i)]
  [∀ i, MeasurableSingletonClass (Ω i)]

/-- With countable discrete coordinates, a set determined by finitely many coordinates is
measurable. -/
private theorem measurableSet_of_dependsOn {A : Set (∀ i, Ω i)} {S : Finset ι}
    (h : DependsOn (· ∈ A) (S : Set ι)) : MeasurableSet A := by
  have hA : A = S.restrict ⁻¹' (S.restrict '' A) := by
    ext x
    refine ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hxy⟩ => ?_⟩
    have := h (x := y) (y := x) fun i hi => congrFun hxy ⟨i, hi⟩
    simpa [this] using hy
  rw [hA]
  exact Finset.measurable_restrict S (Set.to_countable _).measurableSet

end Measurable

open scoped Classical in
/-- **Tail sum.** For a monotone count `U`, the number of `k` with `k ≤ U n` for some `n` is at most
`1 + sup U`. -/
theorem tsum_ite_exists_le_le {U : ℕ → ℕ} (hU : Monotone U) :
    ∑' k, (if ∃ n, k ≤ U n then (1 : ℝ≥0∞) else 0) ≤ 1 + ⨆ n, (U n : ℝ≥0∞) := by
  classical
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  set M := (range N).sup fun k => if h : ∃ n, k ≤ U n then Nat.find h else 0
  have hk : ∀ k ∈ range N, (if ∃ n, k ≤ U n then (1 : ℝ≥0∞) else 0) ≤
      if k ≤ U M then 1 else 0 := by
    intro k hkN
    by_cases h : ∃ n, k ≤ U n
    · have hfind : Nat.find h ≤ M := by
        have := Finset.le_sup (f := fun k => if h : ∃ n, k ≤ U n then Nat.find h else 0) hkN
        simpa [h] using this
      have : k ≤ U M := (Nat.find_spec h).trans (hU hfind)
      simp [h, this]
    · simp [h]
  calc ∑ k ∈ range N, (if ∃ n, k ≤ U n then (1 : ℝ≥0∞) else 0)
      ≤ ∑ k ∈ range N, (if k ≤ U M then (1 : ℝ≥0∞) else 0) := sum_le_sum hk
    _ = (((range N).filter fun k => k ≤ U M).card : ℝ≥0∞) := by
        rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_one]
    _ ≤ ((range (U M + 1)).card : ℝ≥0∞) := by
        gcongr
        intro k hk
        simp only [mem_filter, mem_range] at hk ⊢
        omega
    _ = 1 + (U M : ℝ≥0∞) := by rw [card_range, Nat.cast_add, Nat.cast_one, add_comm]
    _ ≤ 1 + ⨆ n, (U n : ℝ≥0∞) := by gcongr; exact le_iSup (fun n => (U n : ℝ≥0∞)) M

/-- **The symmetric weights.** If `e p (d + 1) ≤ 1`, then `p ≤ x (1 - x) ^ d` for `x = 1 / (d + 2)`,
since `(1 + 1 / (d + 1)) ^ (d + 1) ≤ e`. -/
theorem le_weight_of_exp_mul_le (d : ℕ) {p : ℝ} (hp : Real.exp 1 * p * (d + 1) ≤ 1) :
    p ≤ 1 / (d + 2) * (1 - 1 / (d + 2)) ^ d := by
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  have hkey : (1 + 1 / (d + 1 : ℝ)) ^ (d + 1) ≤ Real.exp 1 := by
    calc (1 + 1 / (d + 1 : ℝ)) ^ (d + 1) ≤ Real.exp (1 / (d + 1)) ^ (d + 1) := by
          gcongr
          rw [add_comm]
          exact Real.add_one_le_exp _
      _ = Real.exp 1 := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          field_simp
  have hform : 1 / (d + 2 : ℝ) * (1 - 1 / (d + 2)) ^ d =
      1 / (d + 1) * ((1 + 1 / (d + 1 : ℝ)) ^ (d + 1))⁻¹ := by
    rw [show (1 : ℝ) - 1 / (d + 2) = (d + 1) / (d + 2) by field_simp; ring,
      show (1 : ℝ) + 1 / (d + 1) = (d + 2) / (d + 1) by field_simp; ring, div_pow, div_pow,
      inv_div, pow_succ, pow_succ]
    field_simp
  rw [hform]
  have hpos : 0 < (1 + 1 / (d + 1 : ℝ)) ^ (d + 1) := by positivity
  calc p ≤ 1 / (d + 1) * (Real.exp 1)⁻¹ := by
        rw [le_mul_inv_iff₀ (Real.exp_pos 1), le_div_iff₀ hd1]
        linarith [hp]
    _ ≤ _ := by gcongr

/-- The events containing a variable pairwise share it, so if every event has at most `d`
neighbours in `Γ`, at most `d + 1` events contain any one variable. -/
theorem card_filter_mem_le {ι : Type*} [Fintype ι] {V : Type*} [DecidableEq V] (vbl : ι → Finset V)
    (Γ : ι → Finset ι)
    (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i) {d : ℕ}
    (hΓd : ∀ i, (Γ i).card ≤ d) (v : V) : (univ.filter fun i => v ∈ vbl i).card ≤ d + 1 := by
  classical
  rcases (univ.filter fun i => v ∈ vbl i).eq_empty_or_nonempty with h | ⟨i₀, hi₀⟩
  · rw [h, card_empty]
    omega
  · have hsub : (univ.filter fun i => v ∈ vbl i) ⊆ insert i₀ (Γ i₀) := by
      intro j hj
      rw [mem_filter] at hi₀ hj
      by_cases hji : j = i₀
      · exact hji ▸ mem_insert_self _ _
      · exact mem_insert_of_mem (hΓ i₀ j hji (not_disjoint_iff.2 ⟨v, hi₀.2, hj.2⟩))
    exact (card_le_card hsub).trans ((card_insert_le _ _).trans (Nat.succ_le_succ (hΓd i₀)))

section Coupled

variable {V ι : Type*} [Fintype V] [DecidableEq V] {α : V → Type*}
  [∀ v, MeasurableSpace (α v)] (κ : ∀ v, Measure (α v × α v)) [∀ v, IsProbabilityMeasure (κ v)]

/-- The **coupled table**: an independent pair of samples `T (v, k) ∼ κ v` for every table entry,
where `κ v` couples the two runs' distributions of `v`. -/
noncomputable def coupledTable : Measure (∀ p : V × ℕ, α p.1 × α p.1) :=
  Measure.infinitePi fun p : V × ℕ => κ p.1

instance : IsProbabilityMeasure (coupledTable κ) := by
  unfold coupledTable
  infer_instance

omit [Fintype V] [DecidableEq V] [∀ v, IsProbabilityMeasure (κ v)] in
theorem coupledTable_def : coupledTable κ = Measure.infinitePi fun p : V × ℕ => κ p.1 := by
  rw [coupledTable]

/-- The first run's table. -/
@[expose] def fstTable (T : ∀ p : V × ℕ, α p.1 × α p.1) : ∀ p : V × ℕ, α p.1 :=
  fun p => (T p).1

/-- The second run's table. -/
@[expose] def sndTable (T : ∀ p : V × ℕ, α p.1 × α p.1) : ∀ p : V × ℕ, α p.1 :=
  fun p => (T p).2

omit [Fintype V] [DecidableEq V] in
theorem measurable_fstTable : Measurable (fstTable (V := V) (α := α)) :=
  measurable_pi_iff.2 fun p => measurable_fst.comp (measurable_pi_apply p)

omit [Fintype V] [DecidableEq V] in
theorem measurable_sndTable : Measurable (sndTable (V := V) (α := α)) :=
  measurable_pi_iff.2 fun p => measurable_snd.comp (measurable_pi_apply p)

omit [Fintype V] [DecidableEq V] in
/-- The first run's table is a resampling table for the first marginals of the couplings. -/
theorem coupledTable_map_fstTable :
    (coupledTable κ).map fstTable = table fun v => (κ v).map Prod.fst := by
  rw [coupledTable, table_def]
  exact Measure.infinitePi_map_pi _ fun _ => measurable_fst

omit [Fintype V] [DecidableEq V] in
/-- The second run's table is a resampling table for the second marginals of the couplings. -/
theorem coupledTable_map_sndTable :
    (coupledTable κ).map sndTable = table fun v => (κ v).map Prod.snd := by
  rw [coupledTable, table_def]
  exact Measure.infinitePi_map_pi _ fun _ => measurable_snd

variable [∀ v, Countable (α v)] [∀ v, MeasurableSingletonClass (α v)] (vbl : ι → Finset V)
  (r : List ι → (∀ v, α v) → Option ι)

/-- The two runs on the coupled table `T` **diverge**: at some step their logs or their current
assignments differ. -/
@[expose] def Diverge (T : ∀ p : V × ℕ, α p.1 × α p.1) : Prop :=
  ∃ n, run (historyRule vbl r) (fstTable T) n ≠ run (historyRule vbl r) (sndTable T) n ∨
    current vbl (fstTable T) (run (historyRule vbl r) (fstTable T) n) ≠
      current vbl (sndTable T) (run (historyRule vbl r) (sndTable T) n)

omit [Fintype V] [∀ v, MeasurableSpace (α v)] [∀ v, Countable (α v)]
  [∀ v, MeasurableSingletonClass (α v)] in
/-- The runs diverge only if some entry `(v, k)` that the first run reads is a disagreeing
pair. -/
theorem setOf_diverge_subset :
    {T | Diverge vbl r T} ⊆ ⋃ v, ⋃ k : ℕ,
      (⋃ n, {T | k ≤ uses vbl (run (historyRule vbl r) (fstTable T) n) v}) ∩
        {T | (T (v, k)).1 ≠ (T (v, k)).2} := by
  intro T hT
  by_contra hno
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, not_exists, not_and,
    not_not] at hno
  have hagree : ∀ m u, fstTable T (u, uses vbl (run (historyRule vbl r) (fstTable T) m) u) =
      sndTable T (u, uses vbl (run (historyRule vbl r) (fstTable T) m) u) :=
    fun m u => hno u _ ⟨m, le_rfl⟩
  have hrun : ∀ n, run (historyRule vbl r) (fstTable T) n =
      run (historyRule vbl r) (sndTable T) n :=
    fun n => run_eq_of_agree r n fun m _ u => hagree m u
  obtain ⟨n, hn⟩ := hT
  refine hn.elim (fun h => h (hrun n)) fun h => h ?_
  rw [← hrun n]
  funext u
  simp only [current_apply]
  exact hagree n u

omit [Fintype V] in
/-- **Independence of reading and disagreeing.** The probability that the first run reads entry
`(v, k)` and the pair there disagrees factors. -/
theorem coupledTable_read_inter_disagree [Finite V] (v : V) (k : ℕ) :
    coupledTable κ ((⋃ n, {T | k ≤ uses vbl (run (historyRule vbl r) (fstTable T) n) v}) ∩
        {T | (T (v, k)).1 ≠ (T (v, k)).2}) =
      table (fun v => (κ v).map Prod.fst)
          {T | ∃ n, k ≤ uses vbl (run (historyRule vbl r) T n) v} *
        κ v {x | x.1 ≠ x.2} := by
  have := Fintype.ofFinite V
  set E : ℕ → Set (∀ p : V × ℕ, α p.1 × α p.1) :=
    fun n => {T | k ≤ uses vbl (run (historyRule vbl r) (fstTable T) n) v}
  set D : Set (∀ p : V × ℕ, α p.1 × α p.1) := {T | (T (v, k)).1 ≠ (T (v, k)).2}
  have hEdep : ∀ n, DependsOn (· ∈ E n) (horizon n v k : Set (V × ℕ)) := fun n T T' h =>
    dependsOn_le_uses r n v k (x := fstTable T) (y := fstTable T') fun p hp => by
      simp only [fstTable]; rw [h p hp]
  have hDdep : DependsOn (· ∈ D) (({(v, k)} : Finset (V × ℕ)) : Set (V × ℕ)) := fun T T' h => by
    simp only [D, Set.mem_ofPred_eq]
    rw [h (v, k) (by simp)]
  have hEm : ∀ n, MeasurableSet (E n) := fun n => measurableSet_of_dependsOn (hEdep n)
  have hDm : MeasurableSet D := measurableSet_of_dependsOn hDdep
  have hmono : Monotone E := fun n n' hnn' T hT =>
    le_trans hT (uses_run_mono (historyRule vbl r) (fstTable T) v hnn')
  have hind : ∀ n, coupledTable κ (E n ∩ D) = coupledTable κ (E n) * coupledTable κ D := by
    intro n
    rw [coupledTable]
    refine (indepSet_infinitePi_of_dependsOn (hEm n) hDm (hEdep n) hDdep ?_).measure_inter_eq_mul
    simp [horizon]
  have hD : coupledTable κ D = κ v {x | x.1 ≠ x.2} := by
    have hm : MeasurableSet {x : α v × α v | x.1 ≠ x.2} := (Set.to_countable _).measurableSet
    rw [coupledTable, show D = (fun T : ∀ p : V × ℕ, α p.1 × α p.1 => T (v, k)) ⁻¹'
      {x : α v × α v | x.1 ≠ x.2} from rfl, ← Measure.map_apply (measurable_pi_apply (v, k)) hm,
      Measure.infinitePi_map_eval]
  have hE : coupledTable κ (⋃ n, E n) =
      table (fun v => (κ v).map Prod.fst)
        {T | ∃ n, k ≤ uses vbl (run (historyRule vbl r) T n) v} := by
    have hm1 : MeasurableSet
        {T : ∀ p : V × ℕ, α p.1 | ∃ n, k ≤ uses vbl (run (historyRule vbl r) T n) v} := by
      simp only [Set.ofPred_exists]
      exact MeasurableSet.iUnion fun n => measurableSet_of_dependsOn (dependsOn_le_uses r n v k)
    rw [← coupledTable_map_fstTable, Measure.map_apply measurable_fstTable hm1]
    congr 1
    ext T
    simp [E]
  have hmono' : Monotone fun n => E n ∩ D := fun _ _ h => Set.inter_subset_inter_left D (hmono h)
  rw [Set.iUnion_inter, hmono'.measure_iUnion, ← hE, ← hD, hmono.measure_iUnion, ENNReal.iSup_mul]
  exact iSup_congr hind

omit [Fintype V] in
/-- **Expected samples read.** The expected number of samples of `v` read by a run, `1` for the
initial sample plus one per resampling of `v`, bounds the sum over `k` of the probability that the
run reads entry `(v, k)`. -/
theorem tsum_table_read_le [Finite V] (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)]
    (v : V) :
    ∑' k : ℕ, table μ {T | ∃ n, k ≤ uses vbl (run (historyRule vbl r) T n) v} ≤
      1 + ∫⁻ T, ⨆ n, (uses vbl (run (historyRule vbl r) T n) v : ℝ≥0∞) ∂table μ := by
  classical
  have := Fintype.ofFinite V
  have hm : ∀ k : ℕ, MeasurableSet
      {T : ∀ p : V × ℕ, α p.1 | ∃ n, k ≤ uses vbl (run (historyRule vbl r) T n) v} := fun k => by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun n => measurableSet_of_dependsOn (dependsOn_le_uses r n v k)
  calc ∑' k : ℕ, table μ {T | ∃ n, k ≤ uses vbl (run (historyRule vbl r) T n) v}
      = ∑' k : ℕ, ∫⁻ T, Set.indicator
          {T | ∃ n, k ≤ uses vbl (run (historyRule vbl r) T n) v} 1 T ∂table μ :=
        tsum_congr fun k => (lintegral_indicator_one (hm k)).symm
    _ = ∫⁻ T, ∑' k : ℕ, Set.indicator
          {T | ∃ n, k ≤ uses vbl (run (historyRule vbl r) T n) v} 1 T ∂table μ :=
        (lintegral_tsum fun k => (measurable_one.indicator (hm k)).aemeasurable).symm
    _ = ∫⁻ T, ∑' k : ℕ, (if ∃ n, k ≤ uses vbl (run (historyRule vbl r) T n) v then 1 else 0)
          ∂table μ := by
        simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    _ ≤ ∫⁻ T, (1 + ⨆ n, (uses vbl (run (historyRule vbl r) T n) v : ℝ≥0∞)) ∂table μ :=
        lintegral_mono fun T => tsum_ite_exists_le_le (uses_run_mono _ T v)
    _ = 1 + ∫⁻ T, ⨆ n, (uses vbl (run (historyRule vbl r) T n) v : ℝ≥0∞) ∂table μ := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, one_mul]

/-- **The first-disagreement bound.** Let both runs use the non-anticipating rule `historyRule r`
on the coupled table. The probability that they diverge is at most `∑ v, η v · E[N v]`. Here
`η v` is the probability that the coupling `κ v` gives two different samples, and `N v` is the
number of samples of `v` that the first run reads, `1` plus the number of resamplings of `v`. -/
theorem coupledTable_diverge_le :
    coupledTable κ {T | Diverge vbl r T} ≤
      ∑ v, κ v {x | x.1 ≠ x.2} * (1 + ∫⁻ T, ⨆ n,
        (uses vbl (run (historyRule vbl r) T n) v : ℝ≥0∞) ∂table fun v => (κ v).map Prod.fst) := by
  calc coupledTable κ {T | Diverge vbl r T}
      ≤ ∑' v, ∑' k : ℕ, coupledTable κ
          ((⋃ n, {T | k ≤ uses vbl (run (historyRule vbl r) (fstTable T) n) v}) ∩
            {T | (T (v, k)).1 ≠ (T (v, k)).2}) :=
        (measure_mono (setOf_diverge_subset vbl r)).trans
          ((measure_iUnion_le _).trans (tsum_le_tsum fun v => measure_iUnion_le _))
    _ = ∑ v, κ v {x | x.1 ≠ x.2} * ∑' k : ℕ, table (fun v => (κ v).map Prod.fst)
          {T | ∃ n, k ≤ uses vbl (run (historyRule vbl r) T n) v} := by
        rw [tsum_fintype]
        refine sum_congr rfl fun v _ => ?_
        simp only [coupledTable_read_inter_disagree, mul_comm]
        exact ENNReal.tsum_mul_left
    _ ≤ _ := by
        gcongr with v
        exact tsum_table_read_le vbl r _ v

/-- **Divergence under the local-lemma hypothesis.** Suppose the first run's distributions satisfy
the hypothesis of the asymmetric local lemma with weights `x`, and `r` only selects occurring
events. Then the two runs diverge with probability at most
`∑ v, η v · (1 + ∑_{i ∋ v} x i / (1 - x i))`, where `η v` is the disagreement probability of the
coupling at `v`. -/
theorem coupledTable_diverge_le_of_lll [Fintype ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi fun v => (κ v).map Prod.fst).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    (hr : ∀ w a i, r w a = some i → a ∈ A i) :
    coupledTable κ {T | Diverge vbl r T} ≤
      ∑ v, κ v {x | x.1 ≠ x.2} *
        (1 + ∑ i ∈ univ.filter (fun i => v ∈ vbl i), ENNReal.ofReal (x i / (1 - x i))) := by
  classical
  refine (coupledTable_diverge_le κ vbl r).trans ?_
  gcongr with v
  have hg := fun i => exists_measurable_ge_resamplings (fun v => (κ v).map Prod.fst) vbl A hAm hA
    Γ hΓ hx hP i
  choose g hgm hgint hge using hg
  calc ∫⁻ T, ⨆ n, (uses vbl (run (historyRule vbl r) T n) v : ℝ≥0∞)
        ∂(table fun v => (κ v).map Prod.fst)
      ≤ ∫⁻ T, ∑ i ∈ univ.filter (fun i => v ∈ vbl i), g i T
          ∂(table fun v => (κ v).map Prod.fst) := by
        refine lintegral_mono fun T => iSup_le fun n => ?_
        rw [uses_eq_sum_count, Nat.cast_sum]
        refine sum_le_sum fun i _ => le_trans ?_ (hge i _ (historyRule_valid hr) T)
        rw [resamplings_def]
        exact le_iSup (fun n => ((run (historyRule vbl r) T n).count i : ℝ≥0∞)) n
    _ = ∑ i ∈ univ.filter (fun i => v ∈ vbl i), ∫⁻ T, g i T
          ∂(table fun v => (κ v).map Prod.fst) :=
        lintegral_finsetSum _ fun i _ => hgm i
    _ ≤ _ := sum_le_sum fun i _ => hgint i

omit [Fintype V] [DecidableEq V] [∀ v, Countable (α v)] [∀ v, MeasurableSingletonClass (α v)] in
/-- The symmetric hypothesis `e p (d + 1) ≤ 1`, with at most `d` neighbours per event, gives the
asymmetric one with the weights `x = 1 / (d + 2)`. -/
private theorem lll_of_symm {A : ι → Set (∀ v, α v)} (m : Measure (∀ v, α v))
    (Γ : ι → Finset ι) {d : ℕ} (hΓd : ∀ i, (Γ i).card ≤ d) {p : ℝ} (hP : ∀ i, m.real (A i) ≤ p)
    (hp : Real.exp 1 * p * (d + 1) ≤ 1) :
    (∀ _ : ι, 1 / (d + 2 : ℝ) ∈ Set.Ico 0 1) ∧
      ∀ i, m.real (A i) ≤ 1 / (d + 2 : ℝ) * ∏ _j ∈ Γ i, (1 - 1 / (d + 2 : ℝ)) := by
  have hd : (0 : ℝ) < d + 2 := by positivity
  refine ⟨fun _ => ⟨by positivity, by rw [div_lt_one hd]; linarith⟩, fun i => ?_⟩
  have h0 : 0 ≤ 1 - 1 / (d + 2 : ℝ) := by rw [sub_nonneg, div_le_one hd]; linarith
  have h1 : 1 - 1 / (d + 2 : ℝ) ≤ 1 := by rw [sub_le_self_iff]; positivity
  rw [prod_const]
  exact (hP i).trans ((le_weight_of_exp_mul_le d hp).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one h0 h1 (hΓd i)) (by positivity)))

/-- **The symmetric case.** Suppose every event has at most `d` neighbours in `Γ` and probability
at most `p` under the first run's distributions, with `e p (d + 1) ≤ 1`, and `r` only selects
occurring events. Then each variable is read at most twice in expectation, and the two runs
diverge with probability at most `2 ∑ v, η v`. -/
theorem coupledTable_diverge_le_two_mul [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i) {d : ℕ}
    (hΓd : ∀ i, (Γ i).card ≤ d) {p : ℝ}
    (hP : ∀ i, (Measure.pi fun v => (κ v).map Prod.fst).real (A i) ≤ p)
    (hp : Real.exp 1 * p * (d + 1) ≤ 1) (hr : ∀ w a i, r w a = some i → a ∈ A i) :
    coupledTable κ {T | Diverge vbl r T} ≤ 2 * ∑ v, κ v {x | x.1 ≠ x.2} := by
  have := Fintype.ofFinite ι
  have hd : (0 : ℝ) < d + 2 := by positivity
  obtain ⟨hx, hP'⟩ := lll_of_symm _ Γ hΓd hP hp
  refine (coupledTable_diverge_le_of_lll κ vbl r A hAm hA Γ hΓ hx hP' hr).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun v _ => ?_
  rw [mul_comm (2 : ℝ≥0∞)]
  gcongr
  have hval : 1 / (d + 2 : ℝ) / (1 - 1 / (d + 2)) = 1 / (d + 1) := by
    rw [show (1 : ℝ) - 1 / (d + 2) = (d + 1) / (d + 2) by field_simp; ring,
      div_div_div_cancel_right₀ hd.ne']
  rw [sum_const, hval, nsmul_eq_mul]
  calc 1 + ((univ.filter fun i => v ∈ vbl i).card : ℝ≥0∞) * ENNReal.ofReal (1 / (d + 1))
      ≤ 1 + ((d + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / (d + 1)) := by
        gcongr
        exact card_filter_mem_le vbl Γ hΓ hΓd v
    _ = 2 := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          show ((d + 1 : ℕ) : ℝ) * (1 / (d + 1)) = 1 by push_cast; field_simp, ENNReal.ofReal_one]
        norm_num

/-- The two runs on the coupled table `T` **agree on a good output**: after the same `n` steps
both stop, with the same log and the same assignment, and no event `A i` occurs in it. -/
@[expose] def AgreeGood (A : ι → Set (∀ v, α v)) (T : ∀ p : V × ℕ, α p.1 × α p.1) : Prop :=
  ∃ n, historyRule vbl r (fstTable T) (run (historyRule vbl r) (fstTable T) n) = none ∧
    historyRule vbl r (sndTable T) (run (historyRule vbl r) (sndTable T) n) = none ∧
    run (historyRule vbl r) (fstTable T) n = run (historyRule vbl r) (sndTable T) n ∧
    current vbl (fstTable T) (run (historyRule vbl r) (fstTable T) n) =
      current vbl (sndTable T) (run (historyRule vbl r) (sndTable T) n) ∧
    ∀ i, current vbl (fstTable T) (run (historyRule vbl r) (fstTable T) n) ∉ A i

omit [Fintype V] [∀ v, MeasurableSpace (α v)] [∀ v, Countable (α v)]
  [∀ v, MeasurableSingletonClass (α v)] in
/-- If the runs do not diverge and the first run stops, both stop at the same step with the same
assignment, and a rule that stops only when no event occurs leaves a good assignment. -/
theorem agreeGood_of_not_diverge {A : ι → Set (∀ v, α v)} {T : ∀ p : V × ℕ, α p.1 × α p.1}
    (hstop : ∀ w a, r w a = none → ∀ i, a ∉ A i) (hT : ¬Diverge vbl r T)
    (hfst : ∃ n, historyRule vbl r (fstTable T) (run (historyRule vbl r) (fstTable T) n) = none) :
    AgreeGood vbl r A T := by
  obtain ⟨n, hn⟩ := hfst
  simp only [Diverge, not_exists, not_or, not_not] at hT
  obtain ⟨hrun, hcur⟩ := hT n
  refine ⟨n, hn, ?_, hrun, hcur, hstop _ _ hn⟩
  simp only [historyRule] at hn ⊢
  rwa [← hcur, ← hrun]

omit [∀ v, Countable (α v)] [∀ v, MeasurableSingletonClass (α v)] in
/-- **The runs output the same good assignment.** Under the asymmetric local-lemma hypothesis for
the first run's distributions, for a valid `r` that stops only when no event occurs, the two runs
fail to stop together at one assignment avoiding every event with probability at most the
divergence probability. The second run's termination is not assumed: it follows from agreement. -/
theorem coupledTable_not_agreeGood_le [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi fun v => (κ v).map Prod.fst).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    (hr : ∀ w a i, r w a = some i → a ∈ A i) (hstop : ∀ w a, r w a = none → ∀ i, a ∉ A i) :
    coupledTable κ {T | ¬AgreeGood vbl r A T} ≤ coupledTable κ {T | Diverge vbl r T} := by
  have hae : ∀ᵐ T ∂coupledTable κ,
      ∃ n, historyRule vbl r (fstTable T) (run (historyRule vbl r) (fstTable T) n) = none := by
    have h1 : ∀ᵐ T' ∂(coupledTable κ).map fstTable,
        ∃ n, historyRule vbl r T' (run (historyRule vbl r) T' n) = none := by
      rw [coupledTable_map_fstTable]
      exact ae_exists_run_eq_none _ vbl A hAm hA Γ hΓ hx hP (historyRule_valid hr)
    exact ae_of_ae_map (measurable_fstTable (V := V) (α := α)).aemeasurable h1
  refine measure_mono_ae (hae.mono fun T hT h => ?_)
  by_contra hd
  exact h (agreeGood_of_not_diverge vbl r hstop hd hT)

omit [∀ v, Countable (α v)] [∀ v, MeasurableSingletonClass (α v)] in
/-- **Both runs terminate.** If each run's distributions satisfy the asymmetric local-lemma
hypothesis, with weights `x` and `y`, then almost surely both runs stop. The local-lemma
hypothesis for the second run cannot be dropped. Take one coin, a second-run distribution that
always gives `true`, and the rule that resamples whenever the coin shows `true`. The second run's
table is then almost surely all `true`, and on that table the rule resamples forever. -/
theorem coupledTable_ae_terminate [Finite ι] (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x y : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1) (hy : ∀ i, y i ∈ Set.Ico 0 1)
    (hP : ∀ i, (Measure.pi fun v => (κ v).map Prod.fst).real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    (hQ : ∀ i, (Measure.pi fun v => (κ v).map Prod.snd).real (A i) ≤ y i * ∏ j ∈ Γ i, (1 - y j))
    (hr : ∀ w a i, r w a = some i → a ∈ A i) :
    ∀ᵐ T ∂coupledTable κ,
      (∃ n, historyRule vbl r (fstTable T) (run (historyRule vbl r) (fstTable T) n) = none) ∧
      ∃ n, historyRule vbl r (sndTable T) (run (historyRule vbl r) (sndTable T) n) = none := by
  have h1 : ∀ᵐ T' ∂(coupledTable κ).map fstTable,
      ∃ n, historyRule vbl r T' (run (historyRule vbl r) T' n) = none := by
    rw [coupledTable_map_fstTable]
    exact ae_exists_run_eq_none _ vbl A hAm hA Γ hΓ hx hP (historyRule_valid hr)
  have h2 : ∀ᵐ T' ∂(coupledTable κ).map sndTable,
      ∃ n, historyRule vbl r T' (run (historyRule vbl r) T' n) = none := by
    rw [coupledTable_map_sndTable]
    exact ae_exists_run_eq_none _ vbl A hAm hA Γ hΓ hy hQ (historyRule_valid hr)
  exact (ae_of_ae_map (measurable_fstTable (V := V) (α := α)).aemeasurable h1).and
    (ae_of_ae_map (measurable_sndTable (V := V) (α := α)).aemeasurable h2)

end Coupled


section Correlated

variable {V ι : Type*} [Fintype V] [DecidableEq V] {α : V → Type*} [∀ v, Fintype (α v)]
  [∀ v, MeasurableSpace (α v)] [∀ v, MeasurableSingletonClass (α v)]

/-- The **correlated-sampling coupling** of `P v` and `Q v`: both parties read one shared seed of
correlated sampling (`Cslib.Probability.CorrelatedSampling`) and output their own samples. -/
noncomputable def correlatedPair (P Q : ∀ v, PMF (α v)) (v : V) : PMF (α v × α v) :=
  (CorrelatedSampling.shared ![P v, Q v]).map fun l =>
    (CorrelatedSampling.sample ![P v, Q v] 0 l, CorrelatedSampling.sample ![P v, Q v] 1 l)

/-- The correlated-sampling coupling as a measure. -/
noncomputable def correlatedCoupling (P Q : ∀ v, PMF (α v)) (v : V) : Measure (α v × α v) :=
  (correlatedPair P Q v).toMeasure

instance (P Q : ∀ v, PMF (α v)) (v : V) : IsProbabilityMeasure (correlatedCoupling P Q v) := by
  unfold correlatedCoupling
  infer_instance

omit [Fintype V] [DecidableEq V] [∀ v, MeasurableSingletonClass (α v)] in
/-- The first party samples from `P v`. -/
theorem correlatedCoupling_map_fst (P Q : ∀ v, PMF (α v)) (v : V) :
    (correlatedCoupling P Q v).map Prod.fst = (P v).toMeasure := by
  rw [correlatedCoupling, PMF.toMeasure_map (hf := measurable_fst), correlatedPair, PMF.map_comp]
  have := CorrelatedSampling.map_sample (P := ![P v, Q v]) 0
  simp only [Matrix.cons_val_zero] at this
  exact congrArg PMF.toMeasure this

omit [Fintype V] [DecidableEq V] [∀ v, MeasurableSingletonClass (α v)] in
/-- The second party samples from `Q v`. -/
theorem correlatedCoupling_map_snd (P Q : ∀ v, PMF (α v)) (v : V) :
    (correlatedCoupling P Q v).map Prod.snd = (Q v).toMeasure := by
  rw [correlatedCoupling, PMF.toMeasure_map (hf := measurable_snd), correlatedPair, PMF.map_comp]
  have := CorrelatedSampling.map_sample (P := ![P v, Q v]) 1
  simp only [Matrix.cons_val_one] at this
  exact congrArg PMF.toMeasure this

open scoped Cslib.Probability.PMF in
omit [Fintype V] [DecidableEq V] in
/-- The two samples differ with probability at most twice the statistical distance. -/
theorem correlatedCoupling_disagree_le (P Q : ∀ v, PMF (α v)) (v : V) :
    correlatedCoupling P Q v {x | x.1 ≠ x.2} ≤ ENNReal.ofReal (2 * dist (P v) (Q v)) := by
  have hm : MeasurableSet {x : α v × α v | x.1 ≠ x.2} := (Set.toFinite _).measurableSet
  rw [correlatedCoupling, PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hm, correlatedPair,
    PMF.toOuterMeasure_map_apply]
  have h := CorrelatedSampling.disagree_le (P := ![P v, Q v]) 0 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [← ENNReal.ofReal_toReal (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal h

open scoped Cslib.Probability.PMF in
/-- **Replicable Moser–Tardos (original).** Two runs of the Moser–Tardos algorithm with a
non-anticipating rule `r`, one sampling from the product of the `P v` and one from the product of
the `Q v`, share the randomness of correlated sampling at every table entry. Each run on its own
is an ordinary Moser–Tardos run (`correlatedCoupling_map_fst`, `correlatedCoupling_map_snd`).
Suppose every event has at most `d` neighbours in `Γ` and probability at most `p` under `P`, with
`e p (d + 1) ≤ 1`, and `r` only selects occurring events. Then the two runs diverge with
probability at most `4 ∑ v, d_TV(P v, Q v)`, independently of `d` and of the number of events. -/
theorem correlated_diverge_le [Finite ι] (P Q : ∀ v, PMF (α v))
    (vbl : ι → Finset V) (r : List ι → (∀ v, α v) → Option ι) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i) {d : ℕ}
    (hΓd : ∀ i, (Γ i).card ≤ d) {p : ℝ}
    (hP : ∀ i, (Measure.pi fun v => (P v).toMeasure).real (A i) ≤ p)
    (hp : Real.exp 1 * p * (d + 1) ≤ 1) (hr : ∀ w a i, r w a = some i → a ∈ A i) :
    coupledTable (correlatedCoupling P Q) {T | Diverge vbl r T} ≤
      ENNReal.ofReal (4 * ∑ v, dist (P v) (Q v)) := by
  have hP' : ∀ i, (Measure.pi fun v => (correlatedCoupling P Q v).map Prod.fst).real (A i) ≤ p :=
    fun i => by simpa only [correlatedCoupling_map_fst] using hP i
  refine (coupledTable_diverge_le_two_mul _ vbl r A hAm hA Γ hΓ hΓd hP' hp hr).trans ?_
  calc 2 * ∑ v, correlatedCoupling P Q v {x | x.1 ≠ x.2}
      ≤ 2 * ∑ v, ENNReal.ofReal (2 * dist (P v) (Q v)) := by
        gcongr with v
        exact correlatedCoupling_disagree_le P Q v
    _ = ENNReal.ofReal (4 * ∑ v, dist (P v) (Q v)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun v _ => by positivity, ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num), ← mul_sum, ← mul_assoc]
        norm_num

open scoped Cslib.Probability.PMF in
/-- **Replicable output under correlated sampling.** In the symmetric case, for a valid `r` that
stops only when no event occurs, the two runs output the same assignment avoiding every event,
except with probability at most `4 ∑ v, d_TV(P v, Q v)`. -/
theorem correlated_not_agreeGood_le [Finite ι] (P Q : ∀ v, PMF (α v))
    (vbl : ι → Finset V) (r : List ι → (∀ v, α v) → Option ι) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i) {d : ℕ}
    (hΓd : ∀ i, (Γ i).card ≤ d) {p : ℝ}
    (hP : ∀ i, (Measure.pi fun v => (P v).toMeasure).real (A i) ≤ p)
    (hp : Real.exp 1 * p * (d + 1) ≤ 1) (hr : ∀ w a i, r w a = some i → a ∈ A i)
    (hstop : ∀ w a, r w a = none → ∀ i, a ∉ A i) :
    coupledTable (correlatedCoupling P Q) {T | ¬AgreeGood vbl r A T} ≤
      ENNReal.ofReal (4 * ∑ v, dist (P v) (Q v)) := by
  have hP' : ∀ i, (Measure.pi fun v => (correlatedCoupling P Q v).map Prod.fst).real (A i) ≤ p :=
    fun i => by simpa only [correlatedCoupling_map_fst] using hP i
  obtain ⟨hx, hP''⟩ := lll_of_symm _ Γ hΓd hP' hp
  exact (coupledTable_not_agreeGood_le _ vbl r A hAm hA Γ hΓ hx hP'' hr hstop).trans
    (correlated_diverge_le P Q vbl r A hAm hA Γ hΓ hΓd hP hp hr)

omit [∀ v, MeasurableSingletonClass (α v)] in
/-- **Both runs terminate under correlated sampling.** In the symmetric case for both `P` and `Q`,
almost surely both runs stop. -/
theorem correlated_ae_terminate [Finite ι] (P Q : ∀ v, PMF (α v))
    (vbl : ι → Finset V) (r : List ι → (∀ v, α v) → Option ι) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i) {d : ℕ}
    (hΓd : ∀ i, (Γ i).card ≤ d) {p : ℝ}
    (hP : ∀ i, (Measure.pi fun v => (P v).toMeasure).real (A i) ≤ p)
    (hQ : ∀ i, (Measure.pi fun v => (Q v).toMeasure).real (A i) ≤ p)
    (hp : Real.exp 1 * p * (d + 1) ≤ 1) (hr : ∀ w a i, r w a = some i → a ∈ A i) :
    ∀ᵐ T ∂coupledTable (correlatedCoupling P Q),
      (∃ n, historyRule vbl r (fstTable T) (run (historyRule vbl r) (fstTable T) n) = none) ∧
      ∃ n, historyRule vbl r (sndTable T) (run (historyRule vbl r) (sndTable T) n) = none := by
  have hP' : ∀ i, (Measure.pi fun v => (correlatedCoupling P Q v).map Prod.fst).real (A i) ≤ p :=
    fun i => by simpa only [correlatedCoupling_map_fst] using hP i
  have hQ' : ∀ i, (Measure.pi fun v => (correlatedCoupling P Q v).map Prod.snd).real (A i) ≤ p :=
    fun i => by simpa only [correlatedCoupling_map_snd] using hQ i
  obtain ⟨hx, hP''⟩ := lll_of_symm _ Γ hΓd hP' hp
  obtain ⟨hy, hQ''⟩ := lll_of_symm _ Γ hΓd hQ' hp
  exact coupledTable_ae_terminate _ vbl r A hAm hA Γ hΓ hx hy hP'' hQ'' hr

end Correlated

end Cslib.Probability.MoserTardos
