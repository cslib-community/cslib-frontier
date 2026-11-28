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
public import CslibFrontier.Crypto.Game.Inversion
public import CslibFrontier.Languages.Probabilistic.BitString
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.PPT

/-!
# One-way functions and permutations

A polynomial-time function on binary words is one-way when, given its value on a uniform
`n`-bit input and the unary parameter `n`, every uniform PPT inverter has negligible probability
of finding **any** preimage. Recovering the sampled input is not required, and the inverter's
answer is not restricted to the sampled input's length.

`OneWayPermutation` additionally requires a length-preserving bijection. Its inverse exists as a
mathematical function; no efficiency of that inverse is assumed. Such a permutation preserves
the uniform distribution at every input length. These are definitions, not assertions that
one-way functions or permutations exist.

`OneWayOn f valid` is one-wayness on a declared domain, as in [BonehShoup2023], Definition 8.6,
where the inverter must output a preimage in the message space: an answer `x'` wins only when
`valid n x'`. With `valid n w = decide (w.length = n)` it is Definition 8.6 on `M = {0,1}ⁿ`.
`OneWay` is the case `valid := fun _ _ => true` (`oneWayOn_true_iff`), so it implies `OneWayOn` on
every domain (`OneWay.oneWayOn`); for an injective function the two agree
(`OneWayOn.oneWay_of_injective`).

## Main definitions

* `Cslib.Crypto.inversionGame`: the inversion experiment on uniform `n`-bit inputs.
* `Cslib.Crypto.OneWay`, `Cslib.Crypto.OneWayPermutation`: uniform computational assumptions.
* `Cslib.Crypto.inversionGameOn`, `Cslib.Crypto.OneWayOn`: the inversion game and one-wayness
  with answers restricted to a declared domain.

## Main results

* `Cslib.Crypto.isPPT_inversionGame`: the inversion experiment is uniformly strict PPT.
* `Cslib.Crypto.OneWay.inversion_negligible`: negligible success for each efficient inverter.
* `Cslib.Crypto.OneWayPermutation.uniformList_append_bit`: the ideal one-bit extension is uniform.
* `Cslib.Crypto.not_oneWay_of_le_succProbability`: inverting with probability bounded away from
  zero at every length refutes one-wayness.
* `Cslib.Crypto.not_oneWay_of_inverse`, `not_oneWay_const`: efficient preimages refute one-wayness.
* `Cslib.Crypto.oneWayOn_true_iff`, `Cslib.Crypto.OneWay.oneWayOn`,
  `Cslib.Crypto.OneWayOn.oneWay_of_injective`: how `OneWayOn` relates to `OneWay`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 9.2.
* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 8.11.1, Definition 8.6, p. 336.

Adapted from Crypto/Computational/OneWay.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using finite fair-bit programs, tidy deterministic
certificates and the upstream nonnegative game API.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

/-- An inverter receives the unary parameter and the image of the sampled input. -/
abbrev Inverter := ℕ → List Bool → ProbComp (List Bool)

/-- The inversion game at length `n`: `Cslib.Crypto.inversionExperiment` for `f` on a uniform
`n`-bit input, with the inverter told `n`. Any preimage of the challenge is accepted. -/
noncomputable def inversionGame (f : List Bool → List Bool) (adversary : Inverter) (n : ℕ) :
    ProbComp Bool :=
  inversionExperiment (BitString.sampleList n) f (adversary n)

/-- Run the complete inversion experiment on its unary parameter. -/
@[program_certificate]
theorem isPPTOn_inversionGame {f : List Bool → List Bool} {adversary : Inverter}
    (hf : ComputableInPolyTime f encBits encBits) (ha : IsPPT encBits adversary) :
    IsPPTOn encUnary encBool (inversionGame f adversary) := by
  unfold inversionGame inversionExperiment
  ppt

/-- The inversion experiment is uniformly PPT, independently of the unused auxiliary input. -/
@[program_certificate]
theorem isPPT_inversionGame {f : List Bool → List Bool} {adversary : Inverter}
    (hf : ComputableInPolyTime f encBits encBits) (ha : IsPPT encBits adversary) :
    IsPPT encBool (fun n _ => inversionGame f adversary n) := by ppt

/-- One plain polynomial-time algorithm evaluates the function. Every uniform strict PPT inverter
has negligible success over the uniform input and its own independent random coins.

This is strong one-wayness, [Goldreich1998Fragments], Definition 2.2.1, p. 29: the inverter
receives `f x` for a uniform `n`-bit `x` together with `n` in unary, and succeeds when it outputs
any preimage of `f x`, of any length. -/
structure OneWay (f : List Bool → List Bool) : Prop where
  /-- A deterministic polynomial-time algorithm evaluates the function. -/
  polyTime : ComputableInPolyTime f encBits encBits
  /-- Inversion is indistinguishable from certain failure in the common game calculus. -/
  secure : Game.Indistinguishable (fun adversary n => ProbComp.eval (inversionGame f adversary n))
    (fun _ _ => PMF.pure false) (IsPPT encBits)

/-- The shared game definition gives the usual negligible inversion probability. -/
theorem OneWay.inversion_negligible {f : List Bool → List Bool} (h : OneWay f)
    (adversary : Inverter) (hPPT : IsPPT encBits adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (inversionGame f adversary n))) := by
  simpa only [Game.advantage_pure_false] using h.secure adversary hPPT

/-- Establish one-wayness by bounding every efficient inverter's success probability. -/
theorem OneWay.of_inversion_negligible {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits)
    (h : ∀ adversary : Inverter, IsPPT encBits adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (inversionGame f adversary n)))) :
    OneWay f := by
  refine ⟨hf, fun adversary hPPT => ?_⟩
  simpa only [Game.advantage_pure_false] using h adversary hPPT

/-- A length-preserving permutation that is one-way against every uniform PPT inverter: a
length-preserving one-to-one function that is `OneWay`, which is how [Goldreich1998Fragments],
Section 3.4.1, p. 91, describes one-way permutations. Being one-to-one and length-preserving, such
a function permutes the words of each length, so `bijective` adds nothing to injectivity. -/
structure OneWayPermutation (f : List Bool → List Bool) : Prop where
  /-- Evaluation is polynomial time, and inversion has negligible success. -/
  oneWay : OneWay f
  /-- The permutation acts separately on words of each length. -/
  length_eq : ∀ word, (f word).length = word.length
  /-- Every word has exactly one preimage; finding it need not be efficient. -/
  bijective : Function.Bijective f

/-- A one-way permutation preserves the uniform distribution at each input length. -/
theorem OneWayPermutation.uniformList_map {f : List Bool → List Bool}
    (hf : OneWayPermutation f) (n : ℕ) :
    (BitString.uniformList n).map f = BitString.uniformList n :=
  BitString.uniformList_map_of_bijective f hf.bijective hf.length_eq n

/-- A permuted uniform seed followed by an independent fair bit is exactly uniform at the
expanded length. Security is needed when replacing the independent bit by a hard-core predicate. -/
theorem OneWayPermutation.uniformList_append_bit {f : List Bool → List Bool}
    (hf : OneWayPermutation f) (n : ℕ) :
    (BitString.uniformList n).bind (fun word =>
      (PMF.uniformOfFintype Bool).map (fun bit => f word ++ [bit])) =
        BitString.uniformList (n + 1) := by
  change (BitString.uniformList n).bind
    ((fun word => (PMF.uniformOfFintype Bool).map (fun bit => word ++ [bit])) ∘ f) = _
  rw [← PMF.bind_map, hf.uniformList_map]
  exact (BitString.uniformList_snoc n).symm

/-- For an injective function, accepting any preimage is equivalent to recovering the sampled
input. The general inversion experiment does not make this assumption. -/
theorem inversionGame_eq_of_injective (f : List Bool → List Bool) (hf : Function.Injective f)
    (adversary : Inverter) (n : ℕ) :
    inversionGame f adversary n = (do
      let input ← BitString.sampleList n
      let candidate ← adversary n (f input)
      return candidate == input) :=
  inversionExperiment_eq_of_injective _ hf _

/-- An inverter that, told the input length, always returns a preimage makes the experiment
always succeed. -/
theorem eval_inversionGame_of_rightInverse (f : List Bool → List Bool)
    (inverse : ℕ → List Bool → List Bool) (h : ∀ x, f (inverse x.length (f x)) = f x) (n : ℕ) :
    ProbComp.eval (inversionGame f (fun n y => pure (inverse n y)) n) = PMF.pure true := by
  simp only [inversionGame, inversionExperiment, ProbComp.eval_bind, ProbComp.eval_pure,
    BitString.eval_sampleList]
  refine (PMF.bind_congr_on_support _ _ (fun _ => PMF.pure true) fun x hx => ?_).trans
    (PMF.bind_const _ _)
  simp [← BitString.length_of_mem_support_uniformList hx, h]

/-- **Inverting with probability bounded away from zero refutes one-wayness**: an efficient
inverter whose success probability is at least a fixed `c > 0` at every length. -/
theorem not_oneWay_of_le_succProbability {f : List Bool → List Bool} {c : ℝ≥0} (hc : c ≠ 0)
    (inverter : Inverter) (hPPT : IsPPT encBits inverter)
    (h : ∀ n, c ≤ Game.succProbability (ProbComp.eval (inversionGame f inverter n))) :
    ¬ OneWay f := fun hf =>
  not_negligible_const hc (negligible_of_le (hf.inversion_negligible inverter hPPT) h)

/-- Efficiently finding any preimage, told the input length, contradicts one-wayness. -/
theorem not_oneWay_of_inverse (f : List Bool → List Bool) (inverse : ℕ → List Bool → List Bool)
    (hPPT : IsPPT encBits (fun n y => pure (inverse n y)))
    (hinv : ∀ x, f (inverse x.length (f x)) = f x) : ¬ OneWay f :=
  not_oneWay_of_le_succProbability one_ne_zero _ hPPT fun n => by
    rw [Game.succProbability, eval_inversionGame_of_rightInverse f inverse hinv n,
      PMF.pure_apply_self, ENNReal.toNNReal_one]

/-- Constant functions are not one-way: the empty word is always a preimage. -/
theorem not_oneWay_const (word : List Bool) : ¬ OneWay (fun _ => word) :=
  not_oneWay_of_inverse _ (fun _ _ => [])
    (ComputableInPolyTime.const []).isPPT (fun _ => rfl)

/-! ### One-wayness on a declared domain -/

/-- The inversion game on a declared domain at length `n` ([BonehShoup2023], Section 8.11.1,
Definition 8.6, p. 336): draw `x ← BitString.sampleList n`, give the inverter `n` and `f x`, and
accept its answer `x'` when `valid n x'` and `f x' = f x`. With `valid n w = decide (w.length = n)`
this is the one-wayness game of Definition 8.6 on `M = {0,1}ⁿ`. -/
noncomputable def inversionGameOn (f : List Bool → List Bool) (valid : ℕ → List Bool → Bool)
    (adversary : Inverter) (n : ℕ) : ProbComp Bool := do
  let x ← BitString.sampleList n
  let x' ← adversary n (f x)
  return valid n x' && f x' == f x

/-- One plain polynomial-time algorithm evaluates the function, and every uniform strict PPT
inverter has negligible success in `inversionGameOn f valid` over the uniform `n`-bit input and its
own independent random coins.

This is one-wayness as [BonehShoup2023], Section 8.11.1, Definition 8.6, p. 336, defines it: the
challenger sends `t := H(m)` for a random `m ∈ M`, and the adversary wins by outputting `m' ∈ M`
with `H(m') = t`. The inverter also receives `n` in unary. With
`valid n w = decide (w.length = n)` this is Definition 8.6 on `M = {0,1}ⁿ`; a wider `valid`
accepts more answers and gives a stronger assumption. `OneWay`, after Goldreich, accepts a
preimage of any length: it is `OneWayOn f (fun _ _ => true)` (`oneWayOn_true_iff`). -/
structure OneWayOn (f : List Bool → List Bool) (valid : ℕ → List Bool → Bool) : Prop where
  /-- A deterministic polynomial-time algorithm evaluates the function. -/
  polyTime : ComputableInPolyTime f encBits encBits
  /-- Inversion within the domain is indistinguishable from certain failure in the common game
  calculus. -/
  secure : Game.Indistinguishable
    (fun adversary n => ProbComp.eval (inversionGameOn f valid adversary n))
    (fun _ _ => PMF.pure false) (IsPPT encBits)

/-- One-wayness on `valid` gives every uniform strict PPT inverter negligible success in
`inversionGameOn f valid`. -/
theorem OneWayOn.negligible {f : List Bool → List Bool} {valid : ℕ → List Bool → Bool}
    (h : OneWayOn f valid) (adversary : Inverter) (hPPT : IsPPT encBits adversary) :
    Negligible fun n =>
      Game.succProbability (ProbComp.eval (inversionGameOn f valid adversary n)) := by
  simpa only [Game.advantage_pure_false] using h.secure adversary hPPT

/-- Establish one-wayness on `valid` by bounding every efficient inverter's success
probability. -/
theorem OneWayOn.of_negligible {f : List Bool → List Bool} {valid : ℕ → List Bool → Bool}
    (hf : ComputableInPolyTime f encBits encBits)
    (h : ∀ adversary : Inverter, IsPPT encBits adversary →
      Negligible fun n =>
        Game.succProbability (ProbComp.eval (inversionGameOn f valid adversary n))) :
    OneWayOn f valid := by
  refine ⟨hf, fun adversary hPPT => ?_⟩
  simpa only [Game.advantage_pure_false] using h adversary hPPT

/-- `OneWay` is one-wayness on the domain that accepts every answer. -/
theorem oneWayOn_true_iff {f : List Bool → List Bool} :
    OneWayOn f (fun _ _ => true) ↔ OneWay f :=
  ⟨fun h => ⟨h.polyTime, h.secure⟩, fun h => ⟨h.polyTime, h.secure⟩⟩

/-- Compare two domain games for the same inverter when every answer that wins the first, a
preimage of an `n`-bit input, is also accepted by the second domain. -/
theorem succProbability_inversionGameOn_le_of_imp {f : List Bool → List Bool}
    {valid₁ valid₂ : ℕ → List Bool → Bool} {n : ℕ}
    (h : ∀ x x' : List Bool, x.length = n → valid₁ n x' = true → f x' = f x →
      valid₂ n x' = true)
    (adversary : Inverter) :
    Game.succProbability (ProbComp.eval (inversionGameOn f valid₁ adversary n)) ≤
      Game.succProbability (ProbComp.eval (inversionGameOn f valid₂ adversary n)) := by
  refine Game.succProbability_mono ?_
  simp only [inversionGameOn, ProbComp.eval_bind, ProbComp.eval_pure, BitString.eval_sampleList]
  refine PMF.bind_apply_mono_on_support _ _ fun x hx =>
    PMF.bind_apply_mono_on_support _ _ fun x' _ => ?_
  cases hwin : (valid₁ n x' && f x' == f x)
  · simp
  · simp only [Bool.and_eq_true, beq_iff_eq] at hwin
    simp [h x x' (BitString.mem_support_uniformList_iff.mp hx) hwin.1 hwin.2, hwin.2]

/-- Shrinking the domain preserves one-wayness. -/
theorem OneWayOn.mono {f : List Bool → List Bool} {valid₁ valid₂ : ℕ → List Bool → Bool}
    (h : OneWayOn f valid₁) (hle : ∀ n w, valid₂ n w = true → valid₁ n w = true) :
    OneWayOn f valid₂ :=
  OneWayOn.of_negligible h.polyTime fun adversary hPPT =>
    negligible_of_le (h.negligible adversary hPPT) fun _ =>
      succProbability_inversionGameOn_le_of_imp (fun _ _ _ hv _ => hle _ _ hv) adversary

/-- A `OneWay` function is one-way on every domain. -/
theorem OneWay.oneWayOn {f : List Bool → List Bool} (h : OneWay f)
    {valid : ℕ → List Bool → Bool} : OneWayOn f valid :=
  (oneWayOn_true_iff.mpr h).mono fun _ _ _ => rfl

/-- For an injective function the only preimage of `f x` is `x`, so one-wayness on a domain that
contains every `n`-bit word is `OneWay`. -/
theorem OneWayOn.oneWay_of_injective {f : List Bool → List Bool}
    {valid : ℕ → List Bool → Bool} (h : OneWayOn f valid) (hinj : Function.Injective f)
    (hvalid : ∀ n x, x.length = n → valid n x = true) : OneWay f :=
  oneWayOn_true_iff.mp <| OneWayOn.of_negligible h.polyTime fun adversary hPPT =>
    negligible_of_le (h.negligible adversary hPPT) fun _ =>
      succProbability_inversionGameOn_le_of_imp
        (fun x _ hx _ hfx => hinj hfx ▸ hvalid _ x hx) adversary

end Cslib.Crypto
