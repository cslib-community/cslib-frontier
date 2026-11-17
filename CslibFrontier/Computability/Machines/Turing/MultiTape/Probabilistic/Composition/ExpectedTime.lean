/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Composition
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ExpectedTime
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect

/-!
# Tail bounds for sequenced and composed fair-coin machines

The halting lemmas for `Turing.MultiTapePTM.seq` and `Turing.MultiTapePTM.comp` assume that each
phase halts within a fixed clock. Machines with an expected running time have no such clock, so
this file bounds the probability that a run has not yet reached a set `good` of halted
configurations (its *miss probability*) instead. That probability decreases with the clock and
bounds the expected running time (`Turing.MultiTapePTM.toOuterMeasure_compl_antitone` and
`Turing.MultiTapePTM.expectedTime_le_tsum_toOuterMeasure_compl`, next to the definition of the
expected running time).

A machine that mirrors another one step at a time, through a map of configurations, misses at
time `fuel + rest` at most as often as the mirrored machine's configuration at time `fuel` followed
by `rest` more steps of the mirroring machine
(`Turing.MultiTapePTM.toOuterMeasure_compl_add_le_bind`). If the mirrored machine halts early, the
mirroring machine has simply taken more steps, which only lowers its miss probability. For
sequencing and composition this gives:

* `Turing.MultiTapePTM.toOuterMeasure_compl_seq_le`: the first phase runs for `fuel` steps and the
  second phase, if the first has halted, for `rest` more;
* `Turing.MultiTapePTM.toOuterMeasure_compl_comp_le`: the same for `comp`, which also charges the
  handoff of an intermediate word of length at most `L`;
* `Turing.MultiTapePTM.toOuterMeasure_compl_comp_le_of_halted` and
  `Turing.MultiTapePTM.toOuterMeasure_compl_comp_le_of_good`: the two special cases where the
  first phase halts within a clock, or the second phase reaches `good` within a clock.

## Main results

* `Turing.MultiTapePTM.tsum_le_add_of_shift`: shifted tails.
* `Turing.MultiTapePTM.eval_runClosedConfigFrom_one_of_step`: a fixed-coin mirror is a one-step
  mirror of distributions.
* `Turing.MultiTapePTM.toOuterMeasure_compl_add_le_bind`.
* `Turing.MultiTapePTM.toOuterMeasure_compl_seq_le`,
  `Turing.MultiTapePTM.toOuterMeasure_compl_comp_le`,
  `Turing.MultiTapePTM.toOuterMeasure_compl_comp_le_of_halted`,
  `Turing.MultiTapePTM.toOuterMeasure_compl_comp_le_of_good`.
-/

public section

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability MultiTapeMachine
open scoped ENNReal

variable {k : ℕ} {Symbol State State' : Type} {input : List Symbol}

/-- A bind whose continuations miss less misses less. -/
private theorem toOuterMeasure_bind_mono {β γ : Type} (p : PMF β) {f g : β → PMF γ}
    {s : Set γ} (h : ∀ b ∈ p.support, (f b).toOuterMeasure s ≤ (g b).toOuterMeasure s) :
    (p.bind f).toOuterMeasure s ≤ (p.bind g).toOuterMeasure s := by
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  refine tsum_le_tsum fun b => ?_
  by_cases hb : b ∈ p.support
  · exact mul_le_mul_of_nonneg_left (h b hb) zero_le
  · rw [(PMF.apply_eq_zero_iff p b).mpr hb, zero_mul, zero_mul]

/-- **Shifted tails**: if a sequence of probabilities is bounded after a shift by `D` by another
sequence, its sum exceeds the other sum by at most `D`. -/
theorem tsum_le_add_of_shift {f g : ℕ → ℝ≥0∞} (D : ℕ) (hf : ∀ t, f t ≤ 1)
    (hshift : ∀ s, f (D + s) ≤ g s) : ∑' t, f t ≤ D + ∑' s, g s := by
  rw [← CompleteLattice.summable.sum_add_tsum_nat_add' (k := D) (f := f)]
  refine add_le_add ?_ (tsum_le_tsum fun s => (add_comm s D).symm ▸ hshift s)
  calc ∑ t ∈ Finset.range D, f t ≤ ∑ _t ∈ Finset.range D, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum fun t _ => hf t
    _ = D := by simp

/-- A deterministic one-step mirror of fixed-coin steps gives a one-step mirror of distributions. -/
theorem eval_runClosedConfigFrom_one_of_step {N : MultiTapePTM k Symbol State'}
    (machine : MultiTapePTM k Symbol State)
    (φ : Config k Symbol State' Empty input → Config k Symbol State Empty input)
    (c : Config k Symbol State' Empty input)
    (h : ∀ bit, (machine.withCoin bit).step (φ c) = φ ((N.withCoin bit).step c)) :
    ProbComp.eval (machine.runClosedConfigFrom 1 (φ c)) =
      (ProbComp.eval (N.runClosedConfigFrom 1 c)).map φ := by
  rw [eval_runClosedConfigFrom_one, eval_runClosedConfigFrom_one, PMF.map_comp]
  exact congrArg (PMF.map · _) (funext h)

/-- **Mirrored runs.** If `machine` mirrors `N` one step at a time through `φ` while `N` runs, then
after `fuel + rest` steps from `φ c` it misses `good` at most as often as `N` run for `fuel` steps
followed by `rest` steps of `machine` from the image. If `N` halts early, `machine` has taken more
steps from the image, which only lowers its miss probability. -/
theorem toOuterMeasure_compl_add_le_bind {N : MultiTapePTM k Symbol State'}
    (machine : MultiTapePTM k Symbol State)
    (φ : Config k Symbol State' Empty input → Config k Symbol State Empty input)
    (hφ : ∀ c, c.tapes.state ≠ none → ProbComp.eval (machine.runClosedConfigFrom 1 (φ c)) =
      (ProbComp.eval (N.runClosedConfigFrom 1 c)).map φ)
    {good : Set (Config k Symbol State Empty input)} (hgood : ∀ c ∈ good, c.tapes.state = none)
    (fuel rest : ℕ) (c : Config k Symbol State' Empty input) :
    (ProbComp.eval (machine.runClosedConfigFrom (fuel + rest) (φ c))).toOuterMeasure goodᶜ ≤
      ((ProbComp.eval (N.runClosedConfigFrom fuel c)).bind fun r =>
        ProbComp.eval (machine.runClosedConfigFrom rest (φ r))).toOuterMeasure goodᶜ := by
  induction fuel generalizing c with
  | zero =>
    have h0 : N.runClosedConfigFrom 0 c = pure c := by
      unfold runClosedConfigFrom runConfigFrom
      exact MultiTapeMachine.runConfigFrom_zero _ _ _ c
    rw [Nat.zero_add, h0, ProbComp.eval_pure, PMF.pure_bind]
  | succ fuel ih =>
    by_cases hc : c.tapes.state = none
    · rw [eval_runClosedConfigFrom_of_halted N _ c hc, PMF.pure_bind]
      exact machine.toOuterMeasure_compl_antitone (φ c) hgood (by omega)
    · rw [show fuel + 1 + rest = 1 + (fuel + rest) by omega, eval_runClosedConfigFrom_add,
        hφ c hc, PMF.bind_map, Nat.add_comm fuel 1, N.eval_runClosedConfigFrom_add, PMF.bind_bind]
      exact toOuterMeasure_bind_mono _ fun c' _ => ih c'

/-! ### Sequencing -/

/-- After a first phase has halted, the sequenced machine runs the second phase. -/
theorem eval_runClosedConfigFrom_seq_left_of_halted {S₀ S₁ : Type}
    (first : MultiTapePTM k Symbol S₀) (second : MultiTapePTM k Symbol S₁) (t : ℕ)
    (r : Config k Symbol S₀ Empty input) (hr : r.tapes.state = none) :
    ProbComp.eval ((first.seq second).runClosedConfigFrom t (Sequential.left second r)) =
      (ProbComp.eval (second.runClosedConfigFrom t (Sequential.start second r))).map
        Sequential.right := by
  rw [Sequential.left_halted second r hr, runClosedConfigFrom, runConfigFrom,
    Sequential.runConfigFrom_right first second (fun choices => choices <$> ProbComp.uniform Bool)
      (fun _ _ => by rw [Functor.map_map]; rfl),
    ProbComp.eval_map]
  rfl

/-- **Tail of a sequenced run.** After `fuel + rest` steps, the sequenced machine misses `good` at
most as often as the first phase run for `fuel` steps followed, if it has halted, by `rest` steps
of the second phase; a first phase still running counts as a miss. -/
theorem toOuterMeasure_compl_seq_le {S₀ S₁ : Type}
    (first : MultiTapePTM k Symbol S₀) (second : MultiTapePTM k Symbol S₁)
    {good : Set (Config k Symbol (S₀ ⊕ S₁) Empty input)} (hgood : ∀ c ∈ good, c.tapes.state = none)
    (fuel rest : ℕ) (c : Config k Symbol S₀ Empty input) :
    (ProbComp.eval ((first.seq second).runClosedConfigFrom (fuel + rest)
      (Sequential.left second c))).toOuterMeasure goodᶜ ≤
      ∑' r, ProbComp.eval (first.runClosedConfigFrom fuel c) r *
        if r.tapes.state = none then
          (ProbComp.eval (second.runClosedConfigFrom rest
            (Sequential.start second r))).toOuterMeasure
            (Sequential.right ⁻¹' goodᶜ)
        else 1 := by
  refine (toOuterMeasure_compl_add_le_bind (N := first) (first.seq second) (Sequential.left second)
    (fun c hc => ?_) hgood fuel rest c).trans ?_
  · rw [runClosedConfigFrom, runConfigFrom, runClosedConfigFrom, runConfigFrom,
      Sequential.runConfigFrom_one first second (fun choices => choices <$> ProbComp.uniform Bool)
        (fun _ _ => by rw [Functor.map_map]; rfl) _ c hc,
      ProbComp.eval_map]
  · rw [PMF.toOuterMeasure_bind_apply]
    refine tsum_le_tsum fun r => mul_le_mul_of_nonneg_left ?_ zero_le
    split_ifs with hr
    · rw [eval_runClosedConfigFrom_seq_left_of_halted first second rest r hr,
        PMF.toOuterMeasure_map_apply]
    · exact PMF.toOuterMeasure_le_one _ _

/-! ### Composition -/

section Comp

variable {k₀ k₁ : ℕ} {State₀ State₁ : Type}
  (first : MultiTapePTM k₀ Symbol State₀) (second : MultiTapePTM k₁ Symbol State₁) (mark : Symbol)

/-- After the source has halted with an output of length at most `L`, the continuation of a
composition prepares the intermediate word within `L + 4` steps and then runs the second machine
on it. -/
theorem toOuterMeasure_compl_continuation_le
    {good : Set (Config (k₁ + k₀ + 2) Symbol
      ((MultiTapeTM.MarkWorkState ⊕ MultiTapeTM.RewindWorkState) ⊕ State₁) Empty input)}
    (hgood : ∀ c ∈ good, c.tapes.state = none) (cfg : Config k₀ Symbol State₀ Empty input)
    {L : ℕ} (hL : cfg.tapes.output.length ≤ L) (rest : ℕ) :
    (ProbComp.eval ((Composition.continuation second k₀ mark).runClosedConfigFrom (L + 4 + rest)
      (Sequential.start (Composition.continuation second k₀ mark)
        (MultiTapeMachine.Composition.buffer k₁ cfg)))).toOuterMeasure goodᶜ ≤
      (ProbComp.eval (second.runClosedConfigFrom rest
        (second.initialConfig cfg.tapes.output))).toOuterMeasure
        ((fun final => Sequential.right
          (MultiTapeMachine.Composition.consumerConfig mark cfg final)) ⁻¹' goodᶜ) := by
  let prep := MultiTapeTM.prepareInput (k₁ + k₀) mark
  let initial :=
    Sequential.start (ofDeterministic prep) (MultiTapeMachine.Composition.buffer k₁ cfg)
  have hdet := MultiTapeMachine.Composition.runFrom_prepare mark k₁ cfg
  change prep.runFrom initial.tapes (cfg.tapes.output.length + 4) = _ at hdet
  have hprep : prep.runFrom initial.tapes (L + 4) =
      (MultiTapeMachine.Composition.ready mark k₁ cfg).tapes := by
    rw [prep.runFrom_eq_of_halt initial.tapes (τ := cfg.tapes.output.length + 4) (by omega)
      (by rw [hdet]; rfl), hdet]
  have hstate : ProbComp.eval ((ofDeterministic prep).runClosedConfigFrom (L + 4) initial) =
      PMF.pure (MultiTapeMachine.Composition.ready mark k₁ cfg) := by
    rw [eval_runClosedConfigFrom_ofDeterministic, hprep]
    rfl
  change (ProbComp.eval (((ofDeterministic prep).seq
    (Composition.consumer second k₀)).runClosedConfigFrom _
      (Sequential.left (Composition.consumer second k₀) initial))).toOuterMeasure goodᶜ ≤ _
  refine (toOuterMeasure_compl_seq_le _ _ hgood (L + 4) rest initial).trans ?_
  rw [hstate, tsum_eq_single (MultiTapeMachine.Composition.ready mark k₁ cfg)
      fun r hr => by rw [PMF.pure_apply, ite_eq_right hr, zero_mul],
    PMF.pure_apply, ite_eq_left rfl, one_mul,
    ite_eq_left (show (MultiTapeMachine.Composition.ready mark k₁ cfg).tapes.state = none from rfl),
    MultiTapeMachine.Composition.start_ready,
    Composition.runClosedConfigFrom_consumer, ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
  rfl

/-- **Tail of a composition.** After `fuel + (L + 4 + rest)` steps, the composed machine misses
`good` at most as often as the first machine run for `fuel` steps followed, if it has halted with
an output of length at most `L`, by `rest` steps of the second machine on that output; every other
first-phase configuration counts as a miss. -/
theorem toOuterMeasure_compl_comp_le
    {good : Set (Config (k₁ + k₀ + 2) Symbol
      (State₀ ⊕ ((MultiTapeTM.MarkWorkState ⊕ MultiTapeTM.RewindWorkState) ⊕ State₁)) Empty input)}
    (hgood : ∀ c ∈ good, c.tapes.state = none) (L fuel rest : ℕ) :
    (ProbComp.eval ((second.comp first mark).runClosedConfigFrom (fuel + (L + 4 + rest))
      ((second.comp first mark).initialConfig input))).toOuterMeasure goodᶜ ≤
      ∑' r, ProbComp.eval (first.runClosedConfigFrom fuel (first.initialConfig input)) r *
        if r.tapes.state = none ∧ r.tapes.output.length ≤ L then
          (ProbComp.eval (second.runClosedConfigFrom rest
            (second.initialConfig r.tapes.output))).toOuterMeasure
            (MultiTapeMachine.Composition.finalConfig mark r ⁻¹' goodᶜ)
        else 1 := by
  change (ProbComp.eval (((Composition.source first k₁).seq
    (Composition.continuation second k₀ mark)).runClosedConfigFrom _
      (Sequential.left (Composition.continuation second k₀ mark)
        ((Composition.source first k₁).initialConfig input)))).toOuterMeasure goodᶜ ≤ _
  refine (toOuterMeasure_compl_seq_le _ _ hgood fuel (L + 4 + rest) _).trans ?_
  rw [Composition.runClosedConfigFrom_source, ProbComp.eval_map, PMF.tsum_map_mul]
  refine tsum_le_tsum fun r => mul_le_mul_of_nonneg_left ?_ zero_le
  have hstate : (MultiTapeMachine.Composition.buffer k₁ r).tapes.state = r.tapes.state := by
    rw [MultiTapeMachine.Composition.buffer_tapes]
  by_cases h : r.tapes.state = none ∧ r.tapes.output.length ≤ L
  · rw [ite_eq_left (hstate.trans h.1), ite_eq_left h, Set.preimage_compl]
    exact toOuterMeasure_compl_continuation_le second mark
      (good := Sequential.right ⁻¹' good) (fun c hc => by
        have := hgood _ hc
        simpa [Sequential.right, Cfg.mapState] using this) r h.2 rest
  · rw [ite_eq_right h]
    split_ifs
    · exact PMF.toOuterMeasure_le_one _ _
    · exact le_rfl

/-- **Tail of a composition with a halting first phase.** If the first machine halts within
`fuel` steps, the composed machine after `fuel + (fuel + 4 + rest)` steps misses `good` at most as
often as the second machine run for `rest` steps on the first machine's output. -/
theorem toOuterMeasure_compl_comp_le_of_halted
    {good : Set (Config (k₁ + k₀ + 2) Symbol
      (State₀ ⊕ ((MultiTapeTM.MarkWorkState ⊕ MultiTapeTM.RewindWorkState) ⊕ State₁)) Empty input)}
    (hgood : ∀ c ∈ good, c.tapes.state = none) (fuel rest : ℕ)
    (hfirst : ∀ r ∈ (ProbComp.eval (first.runClosedConfigFrom fuel
      (first.initialConfig input))).support, r.tapes.state = none) :
    (ProbComp.eval ((second.comp first mark).runClosedConfigFrom (fuel + (fuel + 4 + rest))
      ((second.comp first mark).initialConfig input))).toOuterMeasure goodᶜ ≤
      ((ProbComp.eval (first.runClosedConfigFrom fuel (first.initialConfig input))).bind fun r =>
        (ProbComp.eval (second.runClosedConfigFrom rest (second.initialConfig r.tapes.output))).map
          (MultiTapeMachine.Composition.finalConfig mark r)).toOuterMeasure goodᶜ := by
  refine (toOuterMeasure_compl_comp_le first second mark hgood fuel fuel rest).trans_eq ?_
  rw [PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun r => ?_
  by_cases hr : r ∈ (ProbComp.eval (first.runClosedConfigFrom fuel
    (first.initialConfig input))).support
  · rw [ite_eq_left ⟨hfirst r hr, first.length_output_eval_runClosed_le fuel input _
      (Composition.output_mem first fuel input r hr)⟩, PMF.toOuterMeasure_map_apply]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr hr, zero_mul, zero_mul]

/-- **Tail of a composition with a bounded second phase.** If, from every configuration of `good₁`
(halted, with an output of length at most `L`), the second machine reaches `good` within `rest`
steps, the composed machine after `fuel + (L + 4 + rest)` steps misses `good` at most as often as
the first machine misses `good₁` after `fuel` steps. -/
theorem toOuterMeasure_compl_comp_le_of_good
    {good : Set (Config (k₁ + k₀ + 2) Symbol
      (State₀ ⊕ ((MultiTapeTM.MarkWorkState ⊕ MultiTapeTM.RewindWorkState) ⊕ State₁)) Empty input)}
    (hgood : ∀ c ∈ good, c.tapes.state = none) {good₁ : Set (Config k₀ Symbol State₀ Empty input)}
    {L : ℕ} (hgood₁ : ∀ r ∈ good₁, r.tapes.state = none ∧ r.tapes.output.length ≤ L) (rest : ℕ)
    (hsecond : ∀ r ∈ good₁, ∀ final ∈ (ProbComp.eval (second.runClosedConfigFrom rest
      (second.initialConfig r.tapes.output))).support,
      MultiTapeMachine.Composition.finalConfig mark r final ∈ good) (fuel : ℕ) :
    (ProbComp.eval ((second.comp first mark).runClosedConfigFrom (fuel + (L + 4 + rest))
      ((second.comp first mark).initialConfig input))).toOuterMeasure goodᶜ ≤
      (ProbComp.eval (first.runClosedConfigFrom fuel
        (first.initialConfig input))).toOuterMeasure good₁ᶜ := by
  refine (toOuterMeasure_compl_comp_le first second mark hgood L fuel rest).trans ?_
  rw [PMF.toOuterMeasure_apply]
  refine tsum_le_tsum fun r => ?_
  by_cases hr : r ∈ good₁
  · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hr), ite_eq_left (hgood₁ r hr),
      (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr (Set.disjoint_left.mpr fun final hfinal
        (hbad : MultiTapeMachine.Composition.finalConfig mark r final ∉ good) =>
          hbad (hsecond r hr final hfinal)), mul_zero]
  · rw [Set.indicator_of_mem (Set.mem_compl hr)]
    split_ifs
    · exact mul_le_of_le_one_right' (PMF.toOuterMeasure_le_one _ _)
    · rw [mul_one]

end Comp

end Turing.MultiTapePTM
