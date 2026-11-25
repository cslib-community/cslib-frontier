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
`secondPreimageGame`, `SecondPreimageResistantOn`, and the any-length `abbrev`
`SecondPreimageResistant` (`valid := fun _ _ => true`), along with `.of_injective` and
`not_secondPreimageResistantOn_const`. The monad-generic finite experiment and distributional bounds
of Exercise 8.23(a)–(b) live in `CslibFrontier.Crypto.Game.SecondPreimage`; the certified bit-string
reductions of (8.17), Exercise 8.23(b)–(d), and Theorem 8.12 live in follow-on modules.

## Main definitions

* `Cslib.Crypto.SecondPreimageFinder`: `ℕ → List Bool → ProbComp (List Bool)`.
* `Cslib.Crypto.secondPreimageGameOn`: second-preimage game on uniform `n`-bit inputs accepting
  only `valid n`-valid distinct collisions.
* `Cslib.Crypto.secondPreimageGame`: `secondPreimageExperiment` on uniform `n`-bit inputs
  (answers of any length accepted).
* `Cslib.Crypto.SecondPreimageResistantOn`: polynomial-time evaluation and negligible success in
  `secondPreimageGameOn` for every uniform strict PPT `SecondPreimageFinder`.
* `Cslib.Crypto.SecondPreimageResistant`: `SecondPreimageResistantOn f (fun _ _ => true)`
  (stronger any-length variant).

## Main results

* `Cslib.Crypto.isPPTOn_secondPreimageGame`, `Cslib.Crypto.isPPT_secondPreimageGame`: the
  second-preimage experiment is uniformly strict PPT.
* `Cslib.Crypto.SecondPreimageResistantOn.of_injective`: any polynomial-time function that is
  injective among valid answers colliding with `n`-bit inputs is unconditionally second-preimage
  resistant.
* `Cslib.Crypto.not_secondPreimageResistantOn_const`: constant functions are not
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
    SecondPreimageResistantOn f valid :=
  ⟨hf, fun adversary ha => by simpa only [Game.advantage_pure_false] using hneg adversary ha⟩

/-- Compare two `secondPreimageGameOn` runs when every winning `(x, x')` pair in the first
(`x.length = n`, `valid₁ n x'`, `x' ≠ x`, `f₁ x' = f₁ x`) satisfies `valid₂ n x'` and
`f₂ x' = f₂ x`. -/
theorem succProbability_secondPreimageGameOn_le_of_imp
    {f₁ f₂ : List Bool → List Bool} {valid₁ valid₂ : ℕ → List Bool → Bool} {n : ℕ}
    (h : ∀ x x' : List Bool, x.length = n → valid₁ n x' = true → x' ≠ x → f₁ x' = f₁ x →
      valid₂ n x' = true ∧ f₂ x' = f₂ x)
    (adversary : SecondPreimageFinder) :
    Game.succProbability (ProbComp.eval (secondPreimageGameOn f₁ valid₁ adversary n)) ≤
      Game.succProbability (ProbComp.eval (secondPreimageGameOn f₂ valid₂ adversary n)) := by
  refine Game.succProbability_mono ?_
  unfold secondPreimageGameOn
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList]
  refine PMF.bind_apply_mono_on_support _ _ fun x hx =>
    PMF.bind_apply_mono_on_support _ _ fun x' _ => ?_
  cases hwin : (valid₁ n x' && (x' != x && f₁ x' == f₁ x))
  · simp
  · simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hwin
    obtain ⟨hv, hf⟩ := h x x' (BitString.mem_support_uniformList_iff.mp hx)
      hwin.1 hwin.2.1 hwin.2.2
    simp [hv, hwin.2.1, hf]

/-- Shrinking the valid answer predicate preserves second-preimage resistance. -/
theorem SecondPreimageResistantOn.mono {f : List Bool → List Bool}
    {valid₁ valid₂ : ℕ → List Bool → Bool}
    (h : SecondPreimageResistantOn f valid₁)
    (hle : ∀ n w, valid₂ n w = true → valid₁ n w = true) :
    SecondPreimageResistantOn f valid₂ :=
  SecondPreimageResistantOn.of_negligible h.polyTime fun adversary ha =>
    negligible_of_le (h.negligible adversary ha) fun _ =>
      succProbability_secondPreimageGameOn_le_of_imp
        (fun _ _ _ hv _ hf => ⟨hle _ _ hv, hf⟩) adversary

/-- A polynomial-time function that has no valid second preimages colliding with `n`-bit inputs is
unconditionally second-preimage resistant on `valid`. -/
theorem SecondPreimageResistantOn.of_injective {f : List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} (hf : ComputableInPolyTime f encBits encBits)
    (hinj : ∀ n x x', x.length = n → valid n x' = true → f x' = f x → x' = x) :
    SecondPreimageResistantOn f valid := by
  refine SecondPreimageResistantOn.of_negligible hf fun adversary _ => ?_
  have hzero (n : ℕ) : Game.succProbability
      (ProbComp.eval (secondPreimageGameOn f valid adversary n)) = 0 := by
    suffices ProbComp.eval (secondPreimageGameOn f valid adversary n) = PMF.pure false by
      simp [this, Game.succProbability]
    unfold secondPreimageGameOn
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList]
    refine PMF.bind_eq_pure_of_forall_mem_support fun x hx => ?_
    have hconst (x' : List Bool) : (valid n x' && (x' != x && f x' == f x)) = false := by
      simp only [Bool.and_eq_false_imp, bne_iff_ne, beq_eq_false_iff_ne]
      exact fun hv hx' hf =>
        hx' (hinj n x x' (BitString.mem_support_uniformList_iff.mp hx) hv hf)
    simp_rw [hconst, PMF.bind_const]
  simpa only [hzero] using negligible_zero

/-- Winning `secondPreimageGameOn` eventually with probability bounded away from zero refutes
`SecondPreimageResistantOn`. -/
theorem not_secondPreimageResistantOn_of_le_succProbability {f : List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} {c : ℝ≥0} (hc : c ≠ 0) (adversary : SecondPreimageFinder)
    (ha : IsPPT encBits adversary)
    (hle : ∀ᶠ n in Filter.atTop, c ≤ Game.succProbability
      (ProbComp.eval (secondPreimageGameOn f valid adversary n))) :
    ¬ SecondPreimageResistantOn f valid := by
  intro hf
  have ht : Filter.Tendsto
      (fun n => Game.succProbability (ProbComp.eval (secondPreimageGameOn f valid adversary n)))
      Filter.atTop (nhds 0) := by
    simpa using hf.negligible adversary ha 0
  exact hc (le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds ht hle) bot_le)

/-- A deterministic function `g` producing valid distinct colliding answers on every `n`-bit input
wins `secondPreimageGameOn f valid` at length `n` with probability `1`. -/
theorem succProbability_secondPreimageGameOn_pure_eq_one {f g : List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} {n : ℕ}
    (h : ∀ x : List Bool, x.length = n → valid n (g x) = true ∧ g x ≠ x ∧ f (g x) = f x) :
    Game.succProbability
      (ProbComp.eval (secondPreimageGameOn f valid (fun _ x => pure (g x)) n)) = 1 := by
  suffices ProbComp.eval (secondPreimageGameOn f valid (fun _ x => pure (g x)) n) =
      PMF.pure true by
    rw [this, Game.succProbability, PMF.pure_apply_self, ENNReal.toNNReal_one]
  unfold secondPreimageGameOn
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList, PMF.pure_bind]
  refine PMF.bind_eq_pure_of_forall_mem_support fun x hx => ?_
  obtain ⟨hv, hne, hf⟩ := h x (BitString.mem_support_uniformList_iff.mp hx)
  simp [hv, bne_iff_ne.mpr hne, hf]

/-- Any constant function is not second-preimage resistant on any validity predicate that admits the
head-flipped word on `n`-bit inputs for sufficiently large `n` (in particular,
`valid n w := decide (w.length = n)` or `fun _ _ => true`). -/
theorem not_secondPreimageResistantOn_const {valid : ℕ → List Bool → Bool} (c : List Bool)
    (hvalid : ∀ᶠ n in Filter.atTop, ∀ x : List Bool, x.length = n →
      valid n ((!x.headD false) :: x.tail) = true) :
    ¬ SecondPreimageResistantOn (fun _ => c) valid := by
  let flip : List Bool → List Bool := fun x => (!x.headD false) :: x.tail
  have hflip_poly : ComputableInPolyTime flip encBits encBits := by polytime
  refine not_secondPreimageResistantOn_of_le_succProbability one_ne_zero
    (fun _ x => pure (flip x)) hflip_poly.isPPT (hvalid.mono fun n hvn => ?_)
  exact (succProbability_secondPreimageGameOn_pure_eq_one fun x hx =>
    ⟨hvn x hx, by cases x <;> simp, rfl⟩).symm.le

/-- Any-length second-preimage resistance on bit strings (novel to this library: strengthens
`SecondPreimageResistantOn f (fun n w => decide (w.length = n))`, which is
[BonehShoup2023], Section 8.11.1, Definition 8.6, p. 336, by accepting answers `x'` of any
length, matching `Cslib.Crypto.OneWay`; plausible because `CollisionResistantToOneWay.keyDigest H`
satisfies it for every collision-resistant `HashFamily H`). -/
abbrev SecondPreimageResistant (f : List Bool → List Bool) : Prop :=
  SecondPreimageResistantOn f (fun _ _ => true)

end Cslib.Crypto
