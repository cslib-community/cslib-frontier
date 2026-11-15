/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Crypto.Game.SecondPreimage
public import CslibFrontier.Crypto.Negligible.Basic
public import CslibFrontier.Languages.Probabilistic.BitString
public import CslibFrontier.Probability.PMF
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Support
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Asymptotic second-preimage resistance on bit strings

A function `f` is second-preimage resistant ([BonehShoup2023], Section 8.11.1, Definition 8.6,
p. 336) when, given a uniformly sampled input `x` and the unary security parameter `n`, every
efficient adversary has negligible probability of finding `x' ≠ x` with `f x' = f x`.

In Boneh–Shoup Definition 8.6 (`m' ∈ M`), the adversary's answer is restricted to the message space.
`secondPreimageGameOn f valid` and `SecondPreimageResistantOn f valid` model that restriction via
a parameter-indexed validity predicate `valid : ℕ → List Bool → Bool` (so
`valid := fun n w => decide (w.length = n)` gives Definition 8.6 on `M = {0,1}ⁿ`), while
`secondPreimageGame` and `SecondPreimageResistant` (`valid := fun _ _ => true`) accept an answer
`x'` of any length, matching the any-length preimage convention of `Cslib.Crypto.OneWay`.

This module defines the valid-domain game `secondPreimageGameOn` and its any-length specialization
`secondPreimageGame`, their strict PPT certificates, `SecondPreimageResistantOn`, and
`SecondPreimageResistant`, along with `.of_injective`, `not_secondPreimageResistantOn_const`, and
`not_secondPreimageResistant_const`. The monad-generic finite experiment and distributional
bounds of Exercise 8.23(a)–(b) live in `CslibFrontier.Crypto.Game.SecondPreimage`; the certified
bit-string reductions of (8.17), Exercise 8.23(b)–(d), and Theorem 8.12 live in follow-on modules.

## Main definitions

* `Cslib.Crypto.SecondPreimageFinder`: `ℕ → List Bool → ProbComp (List Bool)`.
* `Cslib.Crypto.secondPreimageGameOn`: second-preimage game on uniform `n`-bit inputs accepting
  only `valid n`-valid distinct collisions.
* `Cslib.Crypto.secondPreimageGame`: `secondPreimageExperiment` on uniform `n`-bit inputs
  (answers of any length accepted).
* `Cslib.Crypto.SecondPreimageResistantOn`: polynomial-time evaluation and negligible success in
  `secondPreimageGameOn` for every uniform strict PPT `SecondPreimageFinder`.
* `Cslib.Crypto.SecondPreimageResistant`: stronger any-length variant (`valid := fun _ _ => true`).

## Main results

* `Cslib.Crypto.isPPTOn_secondPreimageGameOn`, `Cslib.Crypto.isPPT_secondPreimageGameOn`,
  `Cslib.Crypto.isPPTOn_secondPreimageGame`, `Cslib.Crypto.isPPT_secondPreimageGame`: the
  second-preimage experiments are uniformly strict PPT.
* `Cslib.Crypto.SecondPreimageResistantOn.of_injective`,
  `Cslib.Crypto.SecondPreimageResistant.of_injective`: any injective polynomial-time function is
  unconditionally second-preimage resistant.
* `Cslib.Crypto.not_secondPreimageResistantOn_const`,
  `Cslib.Crypto.not_secondPreimageResistant_const`: constant functions are not
  second-preimage resistant.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 8.11.1, Definition 8.6, p. 336.
-/

public section

namespace Cslib.Crypto

open ProbComp Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- A second-preimage finder receives the unary parameter and the sampled input word. -/
abbrev SecondPreimageFinder := ℕ → List Bool → ProbComp (List Bool)

/-- The valid-domain second-preimage game at length `n` ([BonehShoup2023], Section 8.11.1,
Definition 8.6, p. 336): draw `x ← BitString.sampleList n`, run `x' ← adversary n x`, and accept
when `valid n x'`, `x' ≠ x`, and `f x' = f x`. When `valid n w = decide (w.length = n)`, this is
Definition 8.6 on `M = {0,1}ⁿ`. -/
@[expose]
noncomputable def secondPreimageGameOn (f : List Bool → List Bool)
    (valid : ℕ → List Bool → Bool) (adversary : SecondPreimageFinder) (n : ℕ) :
    ProbComp Bool := do
  let x ← BitString.sampleList n
  let x' ← adversary n x
  return valid n x' && (x' != x && f x' == f x)

/-- Run the valid-domain second-preimage experiment on its unary parameter. -/
@[program_certificate]
theorem isPPTOn_secondPreimageGameOn {f : List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} {adversary : SecondPreimageFinder}
    (hf : ComputableInPolyTime f encBits encBits)
    (hv : ComputableInPolyTime (fun p : ℕ × List Bool => valid p.1 p.2)
      (encPair encUnary encBits) encBool)
    (ha : IsPPT encBits adversary) :
    IsPPTOn encUnary encBool (secondPreimageGameOn f valid adversary) := by
  unfold secondPreimageGameOn
  ppt

/-- The valid-domain second-preimage experiment is uniformly PPT, independently of the unused
auxiliary input. -/
@[program_certificate]
theorem isPPT_secondPreimageGameOn {f : List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} {adversary : SecondPreimageFinder}
    (hf : ComputableInPolyTime f encBits encBits)
    (hv : ComputableInPolyTime (fun p : ℕ × List Bool => valid p.1 p.2)
      (encPair encUnary encBits) encBool)
    (ha : IsPPT encBits adversary) :
    IsPPT encBool (fun n _ => secondPreimageGameOn f valid adversary n) := by ppt

/-- The second-preimage game at length `n`: `secondPreimageExperiment` for `f` on a uniform `n`-bit
input, with the finder told `n`. This specializes `secondPreimageGameOn` to `valid := fun _ _ =>
true`, accepting any `x' ≠ x` with `f x' = f x` regardless of length. -/
@[expose]
noncomputable def secondPreimageGame (f : List Bool → List Bool)
    (adversary : SecondPreimageFinder) (n : ℕ) : ProbComp Bool :=
  secondPreimageExperiment (BitString.sampleList n) f (adversary n)

theorem secondPreimageGame_eq_secondPreimageGameOn (f : List Bool → List Bool)
    (adversary : SecondPreimageFinder) (n : ℕ) :
    secondPreimageGame f adversary n = secondPreimageGameOn f (fun _ _ => true) adversary n :=
  rfl

/-- Run the complete second-preimage experiment on its unary parameter. -/
@[program_certificate]
theorem isPPTOn_secondPreimageGame {f : List Bool → List Bool} {adversary : SecondPreimageFinder}
    (hf : ComputableInPolyTime f encBits encBits) (ha : IsPPT encBits adversary) :
    IsPPTOn encUnary encBool (secondPreimageGame f adversary) := by
  unfold secondPreimageGame secondPreimageExperiment
  ppt

/-- The second-preimage experiment is uniformly PPT, independently of the unused auxiliary input. -/
@[program_certificate]
theorem isPPT_secondPreimageGame {f : List Bool → List Bool} {adversary : SecondPreimageFinder}
    (hf : ComputableInPolyTime f encBits encBits) (ha : IsPPT encBits adversary) :
    IsPPT encBool (fun n _ => secondPreimageGame f adversary n) := by ppt

/-- One plain polynomial-time algorithm evaluates the function, and every uniform strict PPT
second-preimage finder has negligible success in `secondPreimageGameOn f valid` over the uniform
`n`-bit input and its own independent random coins ([BonehShoup2023], Section 8.11.1,
Definition 8.6, p. 336). When `valid n w = decide (w.length = n)`, this states Definition 8.6 on
`M = {0,1}ⁿ`. -/
structure SecondPreimageResistantOn (f : List Bool → List Bool)
    (valid : ℕ → List Bool → Bool) : Prop where
  /-- A deterministic polynomial-time algorithm evaluates the function. -/
  polyTime : ComputableInPolyTime f encBits encBits
  /-- Valid-domain second-preimage search is indistinguishable from certain failure in the common
  game calculus. -/
  secure : Game.Indistinguishable
    (fun adversary n => ProbComp.eval (secondPreimageGameOn f valid adversary n))
    (fun _ _ => PMF.pure false) (IsPPT encBits)

/-- Second-preimage resistance on `valid` yields negligible winning probability in
`secondPreimageGameOn` for every uniform strict PPT finder. -/
theorem SecondPreimageResistantOn.negligible {f : List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} (h : SecondPreimageResistantOn f valid)
    (adversary : SecondPreimageFinder) (ha : IsPPT encBits adversary) :
    Negligible fun n =>
      Game.succProbability (ProbComp.eval (secondPreimageGameOn f valid adversary n)) := by
  simpa only [Game.advantage_pure_false] using h.secure adversary ha

/-- Establish `SecondPreimageResistantOn` by proving negligible winning probability for every
uniform strict PPT finder. -/
theorem SecondPreimageResistantOn.of_negligible {f : List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} (hf : ComputableInPolyTime f encBits encBits)
    (hneg : ∀ adversary, IsPPT encBits adversary →
      Negligible fun n =>
        Game.succProbability (ProbComp.eval (secondPreimageGameOn f valid adversary n))) :
    SecondPreimageResistantOn f valid := by
  refine ⟨hf, fun adversary ha => ?_⟩
  simpa only [Game.advantage_pure_false] using hneg adversary ha

/-- Shrinking the valid answer predicate preserves second-preimage resistance. -/
theorem SecondPreimageResistantOn.mono {f : List Bool → List Bool}
    {valid₁ valid₂ : ℕ → List Bool → Bool}
    (h : SecondPreimageResistantOn f valid₁)
    (hle : ∀ n w, valid₂ n w = true → valid₁ n w = true) :
    SecondPreimageResistantOn f valid₂ := by
  refine SecondPreimageResistantOn.of_negligible h.polyTime fun adversary ha => ?_
  refine negligible_of_le (h.negligible adversary ha) fun n => ?_
  refine Game.succProbability_mono ?_
  unfold secondPreimageGameOn
  simp only [ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_apply_mono_on_support _ _ fun x _ =>
    PMF.bind_apply_mono_on_support _ _ fun x' _ => ?_
  by_cases hv₂ : valid₂ n x' = true
  · simp [hv₂, hle n x' hv₂]
  · simp [hv₂]

/-- An injective polynomial-time function is unconditionally second-preimage resistant on any
valid-answer predicate. -/
theorem SecondPreimageResistantOn.of_injective {f : List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} (hf : ComputableInPolyTime f encBits encBits)
    (hinj : Function.Injective f) :
    SecondPreimageResistantOn f valid := by
  refine SecondPreimageResistantOn.of_negligible hf fun adversary _ => ?_
  have hzero : ∀ n, Game.succProbability
      (ProbComp.eval (secondPreimageGameOn f valid adversary n)) = 0 := fun n => by
    have heval : ProbComp.eval (secondPreimageGameOn f valid adversary n) = PMF.pure false := by
      unfold secondPreimageGameOn
      simp only [ProbComp.eval_bind, ProbComp.eval_pure]
      have hconst : ∀ x x' : List Bool,
          (valid n x' && (x' != x && f x' == f x)) = false := fun x x' => by
        by_cases hx : x' = x
        · simp [hx]
        · have hfx : f x' ≠ f x := fun h => hx (hinj h)
          simp [hx, hfx]
      simp_rw [hconst, PMF.bind_const]
    simp [heval, Game.succProbability]
  simpa only [hzero] using negligible_zero

/-- Winning `secondPreimageGameOn` eventually with probability bounded away from zero refutes
`SecondPreimageResistantOn`. -/
theorem not_secondPreimageResistantOn_of_le_succProbability {f : List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} (adversary : SecondPreimageFinder)
    (ha : IsPPT encBits adversary) {c : ℝ≥0} (hc : c ≠ 0)
    (hle : ∀ᶠ n in Filter.atTop, c ≤ Game.succProbability
      (ProbComp.eval (secondPreimageGameOn f valid adversary n))) :
    ¬ SecondPreimageResistantOn f valid := by
  intro hf
  have ht : Filter.Tendsto
      (fun n => Game.succProbability (ProbComp.eval (secondPreimageGameOn f valid adversary n)))
      Filter.atTop (nhds 0) := by
    simpa using hf.negligible adversary ha 0
  exact hc (le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds ht hle) bot_le)

/-- Any constant function is not second-preimage resistant on any validity predicate that admits the
head-flipped word on `n`-bit inputs for sufficiently large `n` (in particular,
`valid n w := decide (w.length = n)` or `fun _ _ => true`). -/
theorem not_secondPreimageResistantOn_const {valid : ℕ → List Bool → Bool} (c : List Bool)
    (hvalid : ∀ᶠ n in Filter.atTop, ∀ x : List Bool, x.length = n →
      valid n ((!x.headD false) :: x.tail) = true) :
    ¬ SecondPreimageResistantOn (fun _ => c) valid := by
  let flip : List Bool → List Bool := fun x => (!x.headD false) :: x.tail
  have hflip_poly : ComputableInPolyTime flip encBits encBits := by polytime
  let adv : SecondPreimageFinder := fun _ x => pure (flip x)
  have hadv : IsPPT encBits adv := hflip_poly.isPPT
  refine not_secondPreimageResistantOn_of_le_succProbability adv hadv one_ne_zero ?_
  filter_upwards [hvalid, Filter.eventually_ge_atTop 1] with n hvn _
  have heval : ProbComp.eval (secondPreimageGameOn (fun _ => c) valid adv n) = PMF.pure true := by
    unfold secondPreimageGameOn adv
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList]
    refine PMF.bind_eq_pure_of_forall_mem_support fun x hx => ?_
    have hlen : x.length = n := BitString.mem_support_uniformList_iff.mp hx
    have hne : (!x.headD false) :: x.tail ≠ x := by cases x <;> simp
    have hcond : (valid n (flip x) && flip x != x) = true := by
      simp only [flip, Bool.and_eq_true, bne_iff_ne]
      exact ⟨hvn x hlen, hne⟩
    simp [hcond]
  rw [heval, Game.succProbability, PMF.pure_apply_self, ENNReal.toNNReal_one]

/-- Any-length second-preimage resistance on bit strings (novel to this library: strengthens
`SecondPreimageResistantOn f (fun n w => decide (w.length = n))`, which is
[BonehShoup2023], Section 8.11.1, Definition 8.6, p. 336, by accepting answers `x'` of any
length, matching `Cslib.Crypto.OneWay`). One plain polynomial-time algorithm evaluates the
function, and every uniform strict PPT finder has negligible success in `secondPreimageGame`. -/
structure SecondPreimageResistant (f : List Bool → List Bool) : Prop where
  /-- A deterministic polynomial-time algorithm evaluates the function. -/
  polyTime : ComputableInPolyTime f encBits encBits
  /-- Second-preimage search is indistinguishable from certain failure in the common game
  calculus. -/
  secure : Game.Indistinguishable
    (fun adversary n => ProbComp.eval (secondPreimageGame f adversary n))
    (fun _ _ => PMF.pure false) (IsPPT encBits)

/-- The shared game definition gives negligible second-preimage success probability. -/
theorem SecondPreimageResistant.negligible {f : List Bool → List Bool}
    (h : SecondPreimageResistant f) (adversary : SecondPreimageFinder)
    (hPPT : IsPPT encBits adversary) :
    Negligible
      (fun n => Game.succProbability (ProbComp.eval (secondPreimageGame f adversary n))) := by
  simpa only [Game.advantage_pure_false] using h.secure adversary hPPT

/-- Establish second-preimage resistance by bounding every efficient finder's success
probability. -/
theorem SecondPreimageResistant.of_negligible {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits)
    (h : ∀ adversary : SecondPreimageFinder, IsPPT encBits adversary →
      Negligible
        (fun n => Game.succProbability (ProbComp.eval (secondPreimageGame f adversary n)))) :
    SecondPreimageResistant f := by
  refine ⟨hf, fun adversary hPPT => ?_⟩
  simpa only [Game.advantage_pure_false] using h adversary hPPT

/-- Any injective polynomial-time function is unconditionally second-preimage resistant. -/
theorem SecondPreimageResistant.of_injective {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits) (hinj : Function.Injective f) :
    SecondPreimageResistant f := by
  refine ⟨hf, fun adversary _ => ?_⟩
  simp only [secondPreimageGame, eval_secondPreimageExperiment,
    secondPreimageExperiment_eq_pure_false_of_injective _ hinj, Game.advantage_self,
    negligible_zero]

/-- **Finding second preimages with probability bounded away from zero refutes
`SecondPreimageResistant`**: an efficient finder whose success probability is at least a fixed
`c > 0` at every length. -/
theorem not_secondPreimageResistant_of_le_succProbability {f : List Bool → List Bool} {c : ℝ≥0}
    (hc : c ≠ 0) (finder : SecondPreimageFinder) (hPPT : IsPPT encBits finder)
    (h : ∀ n, c ≤ Game.succProbability (ProbComp.eval (secondPreimageGame f finder n))) :
    ¬ SecondPreimageResistant f := fun hf =>
  not_negligible_const hc (negligible_of_le (hf.negligible finder hPPT) h)

/-- Constant functions are not second-preimage resistant: prepending `true` always gives a
distinct word with the same constant image. -/
theorem not_secondPreimageResistant_const (word : List Bool) :
    ¬ SecondPreimageResistant (fun _ => word) := by
  refine not_secondPreimageResistant_of_le_succProbability one_ne_zero
    (fun _ x => pure (true :: x)) ?_ fun n => ?_
  · have h : ComputableInPolyTime (List.cons true) encBits encBits := by polytime
    exact h.isPPT
  · have hcond (x : List Bool) : ((true :: x != x) && (word == word)) = true := by
      rw [Bool.and_eq_true, bne_iff_ne, beq_self_eq_true]
      exact ⟨ne_of_apply_ne List.length (by simp), rfl⟩
    have heval :
        ProbComp.eval (secondPreimageGame (fun _ => word) (fun _ x => pure (true :: x)) n) =
          PMF.pure true := by
      simp only [secondPreimageGame, secondPreimageExperiment, ProbComp.eval_bind,
        ProbComp.eval_pure, BitString.eval_sampleList, PMF.pure_bind, hcond, PMF.bind_const]
    rw [heval, Game.succProbability, PMF.pure_apply_self, ENNReal.toNNReal_one]

/-- Helper bridging the any-length and valid-domain notions: `SecondPreimageResistant` implies
`SecondPreimageResistantOn` for every answer-validity predicate `valid`. -/
theorem SecondPreimageResistant.secondPreimageResistantOn {f : List Bool → List Bool}
    (h : SecondPreimageResistant f) (valid : ℕ → List Bool → Bool) :
    SecondPreimageResistantOn f valid := by
  refine SecondPreimageResistantOn.of_negligible h.polyTime fun adversary ha => ?_
  refine negligible_of_le (h.negligible adversary ha) fun n => Game.succProbability_mono ?_
  rw [secondPreimageGame_eq_secondPreimageGameOn]
  unfold secondPreimageGameOn
  simp only [ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_apply_mono_on_support _ _ fun x _ =>
    PMF.bind_apply_mono_on_support _ _ fun x' _ => ?_
  by_cases hv : valid n x' = true <;> simp [hv]

/-- Any-length second-preimage resistance is equivalent to `SecondPreimageResistantOn` with every
word admitted as valid. -/
theorem secondPreimageResistant_iff_on (f : List Bool → List Bool) :
    SecondPreimageResistant f ↔ SecondPreimageResistantOn f (fun _ _ => true) :=
  ⟨fun h => h.secondPreimageResistantOn _, fun h => ⟨h.polyTime, fun a ha => by
    simpa only [Game.advantage_pure_false, secondPreimageGame_eq_secondPreimageGameOn]
      using h.negligible a ha⟩⟩

end Cslib.Crypto
