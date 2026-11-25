/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.HaltedReplay
import CslibFrontier.Probability.PMF.Event

/-!
# Expected running time of fair-coin machines

The running time `T_{M,x}` of a closed fair-coin machine `M` on an input `x` is the number of
steps after which it first halts, a random variable over its coins
[Arora and Barak, Section 7.3][AroraBarak07]. Its expectation is the tail sum
`E[T_{M,x}] = ∑ₜ Pr[T_{M,x} > t]`, and `T_{M,x} > t` exactly when the closed run with clock `t`
has not halted. `Turing.MultiTapePTM.expectedTime` is this tail sum, valued in `ℝ≥0∞`, so it is
total and equals `⊤` when the machine does not halt almost surely or its running time has infinite
expectation. This is the convention of `Cslib.WordRAM.expectedTime`.

Halting is absorbing, so the probability of still running after `t` steps decreases with `t`, and
the probability of having halted in any given set of halted configurations increases with `t`.
Hence Markov's inequality takes the form `(t + 1) * Pr[T_{M,x} > t] ≤ E[T_{M,x}]`. A finite
expectation also means that every finite coin prefix has an extension on which the machine halts:
otherwise the run would keep running on a set of coin sequences of positive probability.

## Main definitions

* `Turing.MultiTapePTM.expectedTime`: the expected running time.

## Main results

* `Turing.MultiTapePTM.toOuterMeasure_running_antitone`: the probability of still running
  decreases.
* `Turing.MultiTapePTM.toOuterMeasure_halted_monotone`: the probability of having halted in a set
  of halted configurations increases.
* `Turing.MultiTapePTM.toOuterMeasure_compl_antitone`,
  `Turing.MultiTapePTM.expectedTime_le_tsum_toOuterMeasure_compl`: the probability of not yet
  being in such a set decreases, and these probabilities bound the expected running time.
* `Turing.MultiTapePTM.mul_toOuterMeasure_running_le_expectedTime`: Markov's inequality.
* `Turing.MultiTapePTM.expectedTime_le_of_halted`: halting within `T` steps bounds the expectation
  by `T`.
* `Turing.MultiTapePTM.toOuterMeasure_running_eq_card`: the probability of still running, as a
  count of coin strings.
* `Turing.MultiTapePTM.exists_halted_append_of_expectedTime_ne_top`: with finite expected running
  time, every coin prefix extends to a halting one.
* `Turing.MultiTapePTM.output_isPrefix_append`: replaying more coins only extends the output.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak07]
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib Cslib.Probability MultiTapeMachine
open scoped ENNReal

variable {k : ℕ} {Symbol State : Type} {input : List Symbol}
  (machine : MultiTapePTM k Symbol State)

/-- The **expected running time** of `machine` on `input` under fair coins: the tail sum over `t`
of the probability that the closed run has not halted after `t` steps
[Arora and Barak, Section 7.3][AroraBarak07]. It is `⊤` when the expectation is infinite. -/
noncomputable def expectedTime (input : List Symbol) : ℝ≥0∞ :=
  ∑' t, (ProbComp.eval (machine.runClosedConfigFrom t (machine.initialConfig input))).toOuterMeasure
    {final | final.tapes.state.isSome}

/-- Running `t + m` steps runs `t` steps and then `m` more. -/
theorem eval_runClosedConfigFrom_add (t m : ℕ) (cfg : Config k Symbol State Empty input) :
    ProbComp.eval (machine.runClosedConfigFrom (t + m) cfg) =
      (ProbComp.eval (machine.runClosedConfigFrom t cfg)).bind
        fun mid => ProbComp.eval (machine.runClosedConfigFrom m mid) := by
  rw [← ProbComp.eval_bind]
  exact congrArg ProbComp.eval (MultiTapeMachine.runConfigFrom_add machine _ _ t m cfg)

/-- A halted configuration stays where it is. -/
theorem eval_runClosedConfigFrom_of_halted (m : ℕ)
    (cfg : Config k Symbol State Empty input) (h : cfg.tapes.state = none) :
    ProbComp.eval (machine.runClosedConfigFrom m cfg) = PMF.pure cfg := by
  rw [show machine.runClosedConfigFrom m cfg = pure cfg from
    MultiTapeMachine.runConfigFrom_halted machine _ _ m cfg h, ProbComp.eval_pure]

/-- **The probability of still running decreases** with the clock. -/
theorem toOuterMeasure_running_antitone (cfg : Config k Symbol State Empty input) :
    Antitone fun t => (ProbComp.eval (machine.runClosedConfigFrom t cfg)).toOuterMeasure
      {final | final.tapes.state.isSome} := by
  intro t t' htt'
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le htt'
  dsimp only
  rw [eval_runClosedConfigFrom_add, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  refine tsum_le_tsum fun mid => ?_
  by_cases hmid : mid.tapes.state.isSome
  · rw [Set.indicator_of_mem (hmid : mid ∈ {final | final.tapes.state.isSome})]
    exact mul_le_of_le_one_right' (Cslib.Probability.PMF.toOuterMeasure_le_one _ _)
  · have hhalt : mid.tapes.state = none := Option.not_isSome_iff_eq_none.mp hmid
    simp [eval_runClosedConfigFrom_of_halted machine m mid hhalt, hhalt]

/-- **The probability of having halted in a set of halted configurations increases** with the
clock: halted configurations stay. -/
theorem toOuterMeasure_halted_monotone (cfg : Config k Symbol State Empty input)
    {S : Set (Config k Symbol State Empty input)} (hS : ∀ final ∈ S, final.tapes.state = none) :
    Monotone fun t => (ProbComp.eval (machine.runClosedConfigFrom t cfg)).toOuterMeasure S := by
  intro t t' htt'
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le htt'
  dsimp only
  rw [eval_runClosedConfigFrom_add, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  refine tsum_le_tsum fun mid => ?_
  by_cases hmid : mid ∈ S
  · rw [Set.indicator_of_mem hmid, eval_runClosedConfigFrom_of_halted machine m mid (hS mid hmid),
      PMF.toOuterMeasure_pure_apply, ite_eq_left hmid, mul_one]
  · rw [Set.indicator_of_notMem hmid]
    exact zero_le

/-- **The miss probability decreases** with the clock: the probability of not yet being in a set of
halted configurations is the complement of an increasing probability. -/
theorem toOuterMeasure_compl_antitone (cfg : Config k Symbol State Empty input)
    {good : Set (Config k Symbol State Empty input)} (hgood : ∀ c ∈ good, c.tapes.state = none) :
    Antitone fun t => (ProbComp.eval (machine.runClosedConfigFrom t cfg)).toOuterMeasure goodᶜ := by
  intro t t' htt'
  have hcompl (s : ℕ) : (ProbComp.eval (machine.runClosedConfigFrom s cfg)).toOuterMeasure goodᶜ =
      1 - (ProbComp.eval (machine.runClosedConfigFrom s cfg)).toOuterMeasure good :=
    ENNReal.eq_sub_of_add_eq (PMF.toOuterMeasure_ne_top _ _)
      ((add_comm _ _).trans (PMF.toOuterMeasure_add_compl_ennreal _ good))
  simp only [hcompl]
  exact tsub_le_tsub_left (machine.toOuterMeasure_halted_monotone cfg hgood htt') 1

/-- **The expected running time is at most the sum of the miss probabilities** of any set of
halted configurations. -/
theorem expectedTime_le_tsum_toOuterMeasure_compl
    {good : Set (Config k Symbol State Empty input)} (hgood : ∀ c ∈ good, c.tapes.state = none) :
    machine.expectedTime input ≤ ∑' t, (ProbComp.eval (machine.runClosedConfigFrom t
      (machine.initialConfig input))).toOuterMeasure goodᶜ :=
  tsum_le_tsum fun _ => PMF.toOuterMeasure_mono _ fun c ⟨hc, _⟩ hgc => by
    simp [hgood c hgc] at hc

/-- **Markov's inequality** for the running time: the run is still going after `t` steps with
probability at most `E[T] / (t + 1)`. -/
theorem mul_toOuterMeasure_running_le_expectedTime (t : ℕ) :
    ((t : ℝ≥0∞) + 1) * (ProbComp.eval (machine.runClosedConfigFrom t
      (machine.initialConfig input))).toOuterMeasure {final | final.tapes.state.isSome} ≤
      machine.expectedTime input := by
  set P : ℕ → ℝ≥0∞ := fun s => (ProbComp.eval (machine.runClosedConfigFrom s
    (machine.initialConfig input))).toOuterMeasure {final | final.tapes.state.isSome}
  calc ((t : ℝ≥0∞) + 1) * P t = ∑ _s ∈ Finset.range (t + 1), P t := by
        simp [nsmul_eq_mul]
    _ ≤ ∑ s ∈ Finset.range (t + 1), P s := Finset.sum_le_sum fun s hs =>
        machine.toOuterMeasure_running_antitone _ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs))
    _ ≤ ∑' s, P s := sum_le_tsum _

/-- **Halting within a clock bounds the expected running time**: if every run has halted after
`T` steps, the expected running time is at most `T`. -/
theorem expectedTime_le_of_halted {T : ℕ}
    (h : ∀ final ∈ (ProbComp.eval (machine.runClosedConfigFrom T
      (machine.initialConfig input))).support, final.tapes.state = none) :
    machine.expectedTime input ≤ T := by
  have hzero (t : ℕ) (ht : T ≤ t) : (ProbComp.eval (machine.runClosedConfigFrom t
      (machine.initialConfig input))).toOuterMeasure {final | final.tapes.state.isSome} = 0 :=
    le_antisymm ((machine.toOuterMeasure_running_antitone _ ht).trans_eq <|
      (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr <| Set.disjoint_left.mpr fun final hf hr => by
        simp [h final hf] at hr) zero_le
  rw [expectedTime, tsum_eq_sum (s := Finset.range T) fun t ht => hzero t (by simpa using ht)]
  exact (Finset.sum_le_sum fun t _ =>
    Cslib.Probability.PMF.toOuterMeasure_le_one _ _).trans_eq (by simp)

/-- **The probability of still running as a count**: the fraction of the `2 ^ t` coin strings of
length `t` whose replay has not halted. -/
theorem toOuterMeasure_running_eq_card (t : ℕ) :
    (ProbComp.eval (machine.runClosedConfigFrom t (machine.initialConfig input))).toOuterMeasure
      {final | final.tapes.state.isSome} =
      ((Finset.univ.filter fun r : Fin t → Bool =>
        (machine.runClosedConfigFromCoins (List.ofFn r)
          (machine.initialConfig input)).tapes.state.isSome).card : ℝ≥0∞) / 2 ^ t := by
  rw [show {final : Config k Symbol State Empty input | final.tapes.state.isSome} =
      (fun final => final.tapes.state.isSome) ⁻¹' {true} from rfl,
    ← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton,
    eval_runClosedConfigFrom_eq_map_coins, PMF.map_comp, BitString.uniformList_map_apply]
  rfl

/-- Replaying coins from a halted configuration leaves its tapes unchanged. -/
theorem tapes_runClosedConfigFromCoins_of_halted (coins : List Bool)
    (cfg : Config k Symbol State Empty input) (h : cfg.tapes.state = none) :
    (machine.runClosedConfigFromCoins coins cfg).tapes = cfg.tapes := by
  rw [tapes_runClosedConfigFromCoins]
  exact machine.stepCoins_of_halted h coins

/-- **Outputs only grow**: replaying more coins extends the output of a replay. -/
theorem output_isPrefix_append (coins more : List Bool) (cfg : Config k Symbol State Empty input) :
    (machine.runClosedConfigFromCoins coins cfg).tapes.output <+:
      (machine.runClosedConfigFromCoins (coins ++ more) cfg).tapes.output := by
  rw [replay_append, tapes_runClosedConfigFromCoins (machine := machine) more]
  generalize (machine.runClosedConfigFromCoins coins cfg).tapes = c
  induction more generalizing c with
  | nil => exact List.prefix_refl _
  | cons bit more ih =>
    rw [stepCoins_cons]
    refine List.IsPrefix.trans ?_ (ih ((machine.withCoin bit).toTM.step c))
    cases h : c.state with
    | none => simp only [MultiTapeTM.step_of_halt h, List.prefix_refl]
    | some q =>
      rw [MultiTapeTM.step_of_state h, Action.apply_output]
      exact List.prefix_append _ _

/-- **With finite expected running time, every coin prefix extends to a halting run**: some
extension of the prefix is a coin string on which the replay has halted. Otherwise every run
extending the prefix would keep running, with probability at least that of the prefix at every
clock, and the tail sum would be infinite. -/
theorem exists_halted_append_of_expectedTime_ne_top (h : machine.expectedTime input ≠ ⊤)
    (coins : List Bool) : ∃ more : List Bool,
      (machine.runClosedConfigFromCoins (coins ++ more) (machine.initialConfig input)).tapes.state =
        none := by
  by_contra hrun
  simp only [not_exists] at hrun
  set n := coins.length
  have hpos : BitString.uniformList n coins ≠ 0 :=
    (PMF.mem_support_iff _ _).mp (BitString.mem_support_uniformList_iff.mpr rfl)
  have hlow (m : ℕ) : BitString.uniformList n coins ≤
      (ProbComp.eval (machine.runClosedConfigFrom (n + m)
        (machine.initialConfig input))).toOuterMeasure {final | final.tapes.state.isSome} := by
    rw [← PMF.toOuterMeasure_apply_singleton, ← BitString.uniformList_take (Nat.le_add_right n m),
      PMF.toOuterMeasure_map_apply, eval_runClosedConfigFrom_eq_map_coins,
      PMF.toOuterMeasure_map_apply]
    refine PMF.toOuterMeasure_mono _ fun word ⟨hword, _⟩ => ?_
    have hsplit : word = coins ++ word.drop n := by
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hword
      conv_lhs => rw [← List.take_append_drop n word, hword]
    rw [Set.mem_preimage, Set.mem_ofPred_eq, hsplit, Option.isSome_iff_ne_none]
    exact hrun _
  refine h (eq_top_iff.mpr <| (ENNReal.tsum_const_eq_top_of_ne_zero hpos).symm.trans_le <|
    (tsum_le_tsum hlow).trans ?_)
  rw [expectedTime]
  exact tsum_comp_le_tsum_of_injective (f := (n + ·)) (fun _ _ => Nat.add_left_cancel)
    fun t => (ProbComp.eval (machine.runClosedConfigFrom t
      (machine.initialConfig input))).toOuterMeasure {final | final.tapes.state.isSome}

end Turing.MultiTapePTM
