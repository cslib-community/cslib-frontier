/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Time
public import CslibFrontier.Computability.Complexity.Classes.ZPP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ExpectedTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.ReplayInput
import CslibFrontier.Probability.PMF.Event

/-!
# Zero-error expected time

The Arora–Barak draft defines `ZPP` through probabilistic machines that never err and run in
expected polynomial time [Arora and Barak, Definition 7.7][AroraBarak07]: `ZTIME(T(n))` contains
the languages `L` decided by a machine `M` whose expected running time is `O(T(n))`, with
`Pr[M accepts x] = 1` for `x ∈ L` and `Pr[M halts without accepting x] = 1` for `x ∉ L`, and
`ZPP = ⋃_c ZTIME(n ^ c)`.

* `Turing.MultiTapePTM.DecidesWithZeroErrorInExpectedTime machine enc A t`: on every encoded
  instance `enc a`, the expected running time of the fair-coin machine
  (`Turing.MultiTapePTM.expectedTime`) is at most `t a`, and the probability that the run has halted
  with the right answer tends to `1`. The answer is the output `[true]` for members and `[false]`
  for the others, the decider convention of `Cslib.Complexity.BPTIME`.
* `Cslib.Complexity.ZTIME enc t`: such machines with a binary alphabet and finitely many states,
  within expected time `c₁ * t n + c₂`.

A halted run with a wrong answer would keep a positive probability of having erred at every later
clock, so such machines never err: every halted run outputs the right answer
(`Turing.MultiTapePTM.DecidesWithZeroErrorInExpectedTime.output_eq_of_halted`).

## `ZTIME(n ^ d) ⊆ ZPP`

Replaying the machine on `2 * T` saved coins, for an expected-time bound `T`, gives a verifier
that reads the coins as its random string, and testing whether the output is `[true]` decides the
problem with one-sided error. By Markov's inequality the run has halted, with the right answer,
on at least half of the coin strings. On a non-member no coin string can already show `[true]`:
outputs only grow, so no extension of that string could halt with the answer `[false]`, while a
finite expected running time makes some extension halt
(`Turing.MultiTapePTM.exists_halted_append_of_expectedTime_ne_top`). Testing for `[false]`
decides the complement in the same way. So the problem is in `RP ∩ coRP`, which is `ZPP`
(`Cslib.Complexity.ZPP_eq_RP_inter_coRP`).

The converse, that the library's `ZPP` is contained in `⋃_d ZTIME(n ^ d)`, needs a machine that
repeats a zero-error verifier until it answers. It is proved in
`CslibFrontier.Computability.Complexity.Classes.Time.LasVegas`, which also states Arora and Barak,
Theorem 7.8, for the draft's `ZPP`.

## Main definitions

* `Turing.MultiTapePTM.DecidesWithZeroErrorInExpectedTime`, `Cslib.Complexity.ZTIME`.

## Main results

* `Turing.MultiTapePTM.DecidesWithZeroErrorInExpectedTime.of_halted`: halting within a clock with
  the right answer is a special case.
* `Turing.MultiTapePTM.DecidesWithZeroErrorInExpectedTime.output_eq_of_halted`: such machines never
  err.
* `Turing.MultiTapePTM.DecidesWithZeroErrorInExpectedTime.decidesWithOneSidedError`: the replay
  test for a fixed answer decides with one-sided error.
* `Cslib.Complexity.ZTIME_pow_subset_RP`, `Cslib.Complexity.ZTIME_pow_subset_coRP`,
  `Cslib.Complexity.ZTIME_pow_subset_ZPP`: `ZTIME(n ^ d) ⊆ RP ∩ coRP = ZPP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak07]
-/

@[expose] public section

namespace Turing.MultiTapePTM

open Cslib
open scoped ENNReal

variable {k : ℕ} {State : Type} {α : Type}

/-- `machine` decides `A` with zero error in expected time `t`, relative to the encoding `enc`
[Arora and Barak, Definition 7.7][AroraBarak07]: on every encoded instance `enc a`, its expected
running time is at most `t a`, and with probability `1` it halts with output `[true]` if `a ∈ A`,
and with output `[false]` otherwise. The probability of having halted with that output by clock
`s` increases with `s`, and its supremum is the probability of eventually doing so. -/
def DecidesWithZeroErrorInExpectedTime (machine : MultiTapePTM k Bool State) (enc : α ↪ List Bool)
    (A : Set α) (t : α → ℕ) : Prop :=
  ∀ a, machine.expectedTime (enc a) ≤ t a ∧
    ⨆ s, (ProbComp.eval (machine.runClosedConfigFrom s
      (machine.initialConfig (enc a)))).toOuterMeasure
        {final | final.tapes.state = none ∧ final.tapes.output = [MultiTapeTM.indicator A a]} = 1

namespace DecidesWithZeroErrorInExpectedTime

variable {machine : MultiTapePTM k Bool State} {enc : α ↪ List Bool} {A : Set α} {t : α → ℕ}

/-- A machine that halts within `T a` steps on every run, with the right answer, decides with zero
error in expected time `T`. -/
theorem of_halted {T : α → ℕ}
    (h : ∀ a, ∀ final ∈ (ProbComp.eval (machine.runClosedConfigFrom (T a)
      (machine.initialConfig (enc a)))).support,
      final.tapes.state = none ∧ final.tapes.output = [MultiTapeTM.indicator A a]) :
    machine.DecidesWithZeroErrorInExpectedTime enc A T := fun a =>
  ⟨machine.expectedTime_le_of_halted fun final hfinal => (h a final hfinal).1,
    le_antisymm
      (iSup_le fun _ => Cslib.Probability.PMF.toOuterMeasure_le_one _ _)
      (le_iSup_of_le (T a) ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr
        fun final hfinal => h a final hfinal).ge)⟩

/-- **Zero-error machines never err**: every halted run outputs the right answer. A halted run
with a wrong answer stays halted, so it would keep the probability of halting with the right
answer at most one minus its own probability at every clock. -/
theorem output_eq_of_halted (h : machine.DecidesWithZeroErrorInExpectedTime enc A t) (a : α)
    {s : ℕ} {final : MultiTapeMachine.Config k Bool State Empty (enc a)}
    (hfinal : final ∈ (ProbComp.eval (machine.runClosedConfigFrom s
      (machine.initialConfig (enc a)))).support)
    (hhalt : final.tapes.state = none) :
    final.tapes.output = [MultiTapeTM.indicator A a] := by
  by_contra hwrong
  set G : Set (MultiTapeMachine.Config k Bool State Empty (enc a)) :=
    {final | final.tapes.state = none ∧ final.tapes.output = [MultiTapeTM.indicator A a]}
  have hbound (s' : ℕ) : (ProbComp.eval (machine.runClosedConfigFrom s'
      (machine.initialConfig (enc a)))).toOuterMeasure G +
      ProbComp.eval (machine.runClosedConfigFrom s (machine.initialConfig (enc a))) final ≤ 1 := by
    have h₁ := machine.toOuterMeasure_halted_monotone (machine.initialConfig (enc a))
      (S := G) (fun _ hc => hc.1) (le_max_left s' s)
    have h₂ := machine.toOuterMeasure_halted_monotone (machine.initialConfig (enc a))
      (S := {final}) (by rintro _ rfl; exact hhalt) (le_max_right s' s)
    simp only [PMF.toOuterMeasure_apply_singleton] at h₂
    exact (add_le_add h₁ (h₂.trans ((PMF.toOuterMeasure_apply_singleton _ final).symm.trans_le
      ((PMF.toOuterMeasure _).mono
        (Set.singleton_subset_iff.mpr fun hG : final ∈ G => hwrong hG.2))))).trans_eq
      (Cslib.Probability.PMF.toOuterMeasure_add_compl_ennreal _ G)
  have hsup : (⨆ s', (ProbComp.eval (machine.runClosedConfigFrom s'
      (machine.initialConfig (enc a)))).toOuterMeasure G) +
      ProbComp.eval (machine.runClosedConfigFrom s (machine.initialConfig (enc a))) final ≤
        1 + 0 := by
    simpa only [ENNReal.iSup_add, add_zero] using iSup_le hbound
  rw [(h a).2] at hsup
  exact (PMF.mem_support_iff _ _).mp hfinal
    (nonpos_iff_eq_zero.mp ((ENNReal.add_le_add_iff_left ENNReal.one_ne_top).mp hsup))

/-- **The replay test decides with one-sided error.** If the expected running time is at most
`q(n)`, replaying the machine on random strings of length `2 * q(n)` and testing whether the output
is `[b]` accepts no instance whose answer is not `b`, and accepts at least half of the random
strings on an instance whose answer is `b`. -/
theorem decidesWithOneSidedError (h : machine.DecidesWithZeroErrorInExpectedTime enc A t)
    {q : Polynomial ℕ} (ht : ∀ a, t a ≤ q.eval (enc a).length) (b : Bool) :
    Complexity.DecidesWithOneSidedError enc (Polynomial.C 2 * q)
      (fun x => decide (machine.runClosedCoins x.2 (enc x.1) = [b]))
      {a | MultiTapeTM.indicator A a = b} := by
  intro a
  set Q := q.eval (enc a).length
  rw [show (Polynomial.C (2 : ℕ) * q).eval (enc a).length = 2 * Q by
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Q]]
  set T := 2 * Q
  have hE : machine.expectedTime (enc a) ≤ Q := (h a).1.trans (by exact_mod_cast ht a)
  refine ⟨fun hb => ?_, fun hb r => ?_⟩
  · -- by Markov's inequality, at most a `Q / (2 Q + 1)` fraction of the runs is still going
    set running := Finset.univ.filter fun r : Fin T → Bool =>
      (machine.runClosedConfigFromCoins (List.ofFn r)
        (machine.initialConfig (enc a))).tapes.state.isSome
    have hmarkov := machine.mul_toOuterMeasure_running_le_expectedTime (input := enc a) T
    rw [toOuterMeasure_running_eq_card, ← mul_div_assoc,
      ENNReal.div_le_iff (by simp) (by simp)] at hmarkov
    have hcount : (T + 1) * running.card ≤ Q * 2 ^ T := by
      exact_mod_cast hmarkov.trans (mul_le_mul_of_nonneg_right hE zero_le)
    -- every halted run gives the answer `b`
    have hcover : 2 ^ T ≤ running.card + Complexity.acceptCount
        (fun x => decide (machine.runClosedCoins x.2 (enc x.1) = [b])) a T := by
      have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        fun r : Fin T → Bool => (machine.runClosedConfigFromCoins (List.ofFn r)
          (machine.initialConfig (enc a))).tapes.state.isSome
      simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hsplit
      rw [← hsplit]
      refine Nat.add_le_add_left (Finset.card_le_card fun r hr => ?_) _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hr ⊢
      have hmem := machine.runClosedConfigFromCoins_mem_support (List.ofFn r)
        (machine.initialConfig (enc a))
      rw [List.length_ofFn] at hmem
      exact (output_eq_of_halted h a hmem (by simpa using hr)).trans (congrArg (· :: []) hb)
    have hhalf : 2 * running.card ≤ 2 ^ T := by
      by_contra! hlt
      have hpos : 0 < 2 ^ T := by positivity
      generalize 2 ^ T = X at hcount hlt hpos
      dsimp only [T] at hcount
      nlinarith
    omega
  · -- no coin string can already show the answer `[b]` on a non-member
    simp only [decide_eq_false_iff_not]
    intro hr
    obtain ⟨more, hmore⟩ := machine.exists_halted_append_of_expectedTime_ne_top
      (ne_top_of_le_ne_top (ENNReal.natCast_ne_top Q) hE) (List.ofFn r)
    have hmem := machine.runClosedConfigFromCoins_mem_support (List.ofFn r ++ more)
      (machine.initialConfig (enc a))
    have hpre := machine.output_isPrefix_append (List.ofFn r) more (machine.initialConfig (enc a))
    rw [output_eq_of_halted h a hmem hmore,
      show (machine.runClosedConfigFromCoins (List.ofFn r)
        (machine.initialConfig (enc a))).tapes.output = [b] from hr] at hpre
    exact hb (List.singleton_inj.mp (hpre.eq_of_length (by simp))).symm

end DecidesWithZeroErrorInExpectedTime

end Turing.MultiTapePTM

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- The problems decidable with zero error in expected time `O(t n)`, that is `c₁ * t n + c₂` for
constants `c₁` and `c₂`, on instances whose encoding under `enc` has length `n`, by a fair-coin
machine with a binary alphabet and finitely many states
[Arora and Barak, Definition 7.7][AroraBarak07]. -/
def ZTIME (enc : α ↪ List Bool) (t : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ c₁ c₂ : ℕ, ∃ (k : ℕ) (State : Type) (_ : Finite State)
    (machine : MultiTapePTM k Bool State),
      machine.DecidesWithZeroErrorInExpectedTime enc A fun a => c₁ * t (enc a).length + c₂}

/-- Testing the replayed output for a fixed answer is a polynomial-time verifier. -/
private theorem computableInPolyTime_decide_runClosedCoins_eq {k : ℕ} {State : Type}
    [Finite State] (machine : MultiTapePTM k Bool State) (w : List Bool) :
    ComputableInPolyTime
      (fun x : α × List Bool => decide (machine.runClosedCoins x.2 (enc x.1) = w))
      (encPair enc encBits) encBool :=
  ComputableInPolyTime.decide_eq'
    ((MultiTapePTM.computableInPolyTime_runClosedCoins machine).comp
      ((ComputableInPolyTime.snd enc encBits).prod
        ((ComputableInPolyTime.of_eq (encIn := enc) (encOut := encBits) (f := fun x : α => enc x)
          fun _ => rfl).comp (ComputableInPolyTime.fst enc encBits))))
    (ComputableInPolyTime.const w)

/-- A problem in `ZTIME(n ^ d)` with answer `b` on the instances of `S` puts `S` in `RP`. -/
private theorem mem_RP_of_mem_ZTIME_pow {d : ℕ} {A : Set α} (hA : A ∈ ZTIME enc (· ^ d))
    (b : Bool) : {a | MultiTapeTM.indicator A a = b} ∈ RP enc := by
  obtain ⟨c₁, c₂, k, State, _, machine, h⟩ := hA
  let q : Polynomial ℕ := Polynomial.C c₁ * Polynomial.X ^ d + Polynomial.C c₂
  exact ⟨Polynomial.C 2 * q, _, computableInPolyTime_decide_runClosedCoins_eq machine [b],
    h.decidesWithOneSidedError (q := q) (fun a => by simp [q]) b⟩

/-- **`ZTIME(n ^ d) ⊆ RP`**: replay the machine on twice as many coins as its expected-time bound
and accept on the output `[true]`. -/
theorem ZTIME_pow_subset_RP (d : ℕ) : ZTIME enc (· ^ d) ⊆ RP enc := fun A hA => by
  convert mem_RP_of_mem_ZTIME_pow hA true using 1
  ext a
  by_cases ha : a ∈ A <;> simp [MultiTapeTM.indicator, ha]

/-- **`ZTIME(n ^ d) ⊆ coRP`**: accept the complement on the output `[false]`. -/
theorem ZTIME_pow_subset_coRP (d : ℕ) : ZTIME enc (· ^ d) ⊆ coRP enc := fun A hA => by
  rw [mem_coRP]
  convert mem_RP_of_mem_ZTIME_pow hA false using 1
  ext a
  by_cases ha : a ∈ A <;> simp [MultiTapeTM.indicator, ha]

/-- **`ZTIME(n ^ d) ⊆ ZPP`**: the problems decided with zero error in expected polynomial time in
the sense of [Arora and Barak, Definition 7.7][AroraBarak07] are in the library's `ZPP`. This is
one inclusion of the draft's definition `ZPP = ⋃_c ZTIME(n ^ c)` against the library's `ZPP`; the
converse is `Cslib.Complexity.exists_mem_ZTIME_pow_of_mem_ZPP`. -/
theorem ZTIME_pow_subset_ZPP (d : ℕ) : ZTIME enc (· ^ d) ⊆ ZPP enc := fun _ hA => by
  rw [ZPP_eq_RP_inter_coRP]
  exact ⟨ZTIME_pow_subset_RP d hA, ZTIME_pow_subset_coRP d hA⟩

end Cslib.Complexity
