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
public import CslibFrontier.Crypto.Negligible.Basic
public import CslibFrontier.Languages.Probabilistic.BitString
public import CslibFrontier.Probability.PMF
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Second-preimage resistance

A function `f` is second-preimage resistant ([BonehShoup2023], Section 8.11.1, Definition 8.6,
p. 336) when, given a uniformly sampled input `x` and the unary security parameter `n`, every
efficient adversary has negligible probability of finding `x' ≠ x` with `f x' = f x`.

This module defines:
* the monad-generic experiment `secondPreimageExperiment sample f finder` and the finite-domain
  predicate `HasSecondPreimage H m`, together with the finite-domain counting and reduction bounds
  of [BonehShoup2023], Exercise 8.23(a)–(b), pp. 352–353; and
* the uniform bit-string game `secondPreimageGame f adversary n`, its strict PPT certificates, and
  the assumption `SecondPreimageResistant f` on `List Bool → List Bool`, matching `OneWay`.

## Main definitions

* `Cslib.Crypto.secondPreimageExperiment`: draw `x ← sample`, run `x' ← finder x`, and accept when
  `x' ≠ x` and `f x' = f x`.
* `Cslib.Crypto.HasSecondPreimage`: `∃ m' ≠ m, H m' = H m`.
* `Cslib.Crypto.SecondPreimageFinder`: `ℕ → List Bool → ProbComp (List Bool)`.
* `Cslib.Crypto.secondPreimageGame`: `secondPreimageExperiment` on uniform `n`-bit inputs.
* `Cslib.Crypto.SecondPreimageResistant`: polynomial-time evaluation and negligible success in
  `secondPreimageGame` for every uniform strict PPT `SecondPreimageFinder`.

## Main results

* `Cslib.Crypto.card_not_hasSecondPreimage_le`,
  `Cslib.Crypto.card_not_hasSecondPreimage_div_le`: at most `|T|` inputs of a finite domain `M`
  lack a second preimage under `H : M → T`, hence at most a `1 / s` fraction when `|M| ≥ s · |T|`
  (Exercise 8.23(a)).
* `Cslib.Crypto.succProbability_inversionExperiment_uniform_le_card_not_hasSecondPreimage`,
  `Cslib.Crypto.succProbability_inversionExperiment_uniform_le`,
  `Cslib.Crypto.succProbability_inversionExperiment_uniform_le_of_compression`: for a uniform input
  from a finite nonempty domain `M`, wrapping a one-way inverter `A` into the second-preimage
  finder `m ↦ A (H m)` satisfies
  `OWadv[A, H] ≤ 2 · SPRadv[B, H] + |{m | ¬ HasSecondPreimage H m}| / |M|`, hence
  `≤ 2 · SPRadv[B, H] + |T| / |M|` and `≤ 2 · SPRadv[B, H] + 1 / s` when `|M| ≥ s · |T|`
  (Exercise 8.23(b), equation (8.22)).
* `Cslib.Crypto.succProbability_secondPreimageExperiment_le_of_eq_imp`: monotonicity of
  `secondPreimageExperiment` under a digest map that preserves or refines equality on distinct
  inputs (used for Exercise 8.23(c)).
* `Cslib.Crypto.isPPTOn_secondPreimageGame`, `Cslib.Crypto.isPPT_secondPreimageGame`: the
  second-preimage experiment is uniformly strict PPT.
* `Cslib.Crypto.SecondPreimageResistant.of_injective`: any injective polynomial-time function is
  unconditionally second-preimage resistant.
* `Cslib.Crypto.not_secondPreimageResistant_of_le_succProbability`,
  `Cslib.Crypto.not_secondPreimageResistant_const`: finding second preimages with probability
  bounded away from zero refutes `SecondPreimageResistant`; constant functions are not
  second-preimage resistant.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 8.11.1 (Definition 8.6, pp. 336–337) and Exercise 8.23(a)–(c) (pp. 352–353).
-/

public section

namespace Cslib.Crypto

open ProbComp Probability Turing.MultiTapeTM
open Cslib.Probability.PMF (uniformOfFintype)
open scoped NNReal ENNReal

/-! ## Finite-domain second-preimage experiment and Exercise 8.23(a)–(b) -/

variable {m : Type → Type*} [Monad m] {α : Type} {β : Type*}

/-- The second-preimage experiment for `f` on inputs drawn from `sample`
([BonehShoup2023], Section 8.11.1, Definition 8.6, p. 336): the challenger draws `x ← sample`
and gives `x` to `finder`; it wins when it returns `x' ≠ x` with `f x' = f x`. -/
@[expose]
def secondPreimageExperiment [BEq α] [BEq β] (sample : m α) (f : α → β)
    (finder : α → m α) : m Bool := do
  let x ← sample
  let x' ← finder x
  return (x' != x) && (f x' == f x)

/-- On distributions, the second-preimage experiment maps the finder's output distribution through
the distinct-preimage test. -/
theorem secondPreimageExperiment_eq_bind_map [BEq α] [BEq β] (sample : PMF α) (f : α → β)
    (finder : α → PMF α) :
    secondPreimageExperiment sample f finder =
      sample.bind fun x => (finder x).map fun x' => (x' != x) && (f x' == f x) :=
  rfl

/-- Evaluating the second-preimage experiment of programs gives the second-preimage experiment of
their distributions. -/
@[simp]
theorem eval_secondPreimageExperiment [BEq α] [BEq β] (sample : ProbComp α) (f : α → β)
    (finder : α → ProbComp α) :
    ProbComp.eval (secondPreimageExperiment sample f finder) =
      secondPreimageExperiment (ProbComp.eval sample) f (fun x => ProbComp.eval (finder x)) := by
  simp only [secondPreimageExperiment, ProbComp.eval_bind, ProbComp.eval_pure]
  rfl

/-- For an injective function, no element has a second preimage, so the experiment always returns
`false`. -/
theorem secondPreimageExperiment_eq_pure_false_of_injective [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β] (sample : PMF α) {f : α → β} (hf : Function.Injective f)
    (finder : α → PMF α) :
    secondPreimageExperiment sample f finder = PMF.pure false := by
  have hfalse (x x' : α) : ((x' != x) && (f x' == f x)) = false := by
    rw [Bool.and_eq_false_iff, bne_eq_false_iff_eq, beq_eq_false_iff_ne]
    by_cases h : x' = x
    · exact Or.inl h
    · exact Or.inr (hf.ne h)
  simp only [secondPreimageExperiment, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, hfalse,
    PMF.bind_const]

/-- If every second preimage under `g` is also a second preimage under `f`, then every finder's
success probability in `secondPreimageExperiment` against `g` is at most its success probability
against `f`. -/
theorem succProbability_secondPreimageExperiment_le_of_eq_imp
    {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (sample : PMF α) {f : α → β} {g : α → γ}
    (himp : ∀ x x', x' ≠ x → g x' = g x → f x' = f x) (finder : α → PMF α) :
    Game.succProbability (secondPreimageExperiment sample g finder) ≤
      Game.succProbability (secondPreimageExperiment sample f finder) := by
  apply Game.succProbability_mono
  simp only [secondPreimageExperiment_eq_bind_map]
  refine PMF.bind_apply_mono_on_support _ _ fun x _ =>
    PMF.map_true_mono _ fun x' _ h => ?_
  rw [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at h ⊢
  exact ⟨h.1, himp x x' h.1 h.2⟩

/-- An input `m : M` has a second preimage under `H` if some `m' ≠ m` has `H m' = H m`
([BonehShoup2023], Exercise 8.23(a), p. 352). -/
@[expose]
def HasSecondPreimage {M T : Type*} (H : M → T) (m : M) : Prop :=
  ∃ m' ≠ m, H m' = H m

instance {M T : Type*} [Fintype M] [DecidableEq M] [DecidableEq T] (H : M → T) :
    DecidablePred (HasSecondPreimage H) :=
  fun _ => Fintype.decidableExistsFintype

/-- An input without a second preimage is the unique preimage of its digest. -/
theorem eq_of_not_hasSecondPreimage {M T : Type*} {H : M → T} {m m' : M}
    (hm : ¬ HasSecondPreimage H m) (h : H m' = H m) : m' = m := by
  by_contra hne
  exact hm ⟨m', hne, h⟩

/-- At most `|T|` inputs in a finite domain `M` have no second preimage under `H : M → T`: `H` is
injective on `{m | ¬ HasSecondPreimage H m}`. -/
theorem card_not_hasSecondPreimage_le {M T : Type*} [Fintype M] [DecidableEq M]
    [Fintype T] [DecidableEq T] (H : M → T) :
    (Finset.univ.filter (fun m => ¬ HasSecondPreimage H m)).card ≤ Fintype.card T := by
  calc
    (Finset.univ.filter (fun m => ¬ HasSecondPreimage H m)).card
      = ((Finset.univ.filter (fun m => ¬ HasSecondPreimage H m)).image H).card := by
        refine (Finset.card_image_of_injOn ?_).symm
        intro m₁ hm₁ m₂ _ hH
        exact (eq_of_not_hasSecondPreimage (Finset.mem_filter.mp hm₁).2 hH.symm).symm
    _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card T := rfl

/-- **Exercise 8.23(a)** ([BonehShoup2023], p. 352): when `|M| ≥ s · |T|` with `0 < s`, at most a
`1 / s` fraction of `M` has no second preimage under `H`. -/
theorem card_not_hasSecondPreimage_div_le {M T : Type*} [Fintype M] [DecidableEq M]
    [Fintype T] [DecidableEq T] (H : M → T) {s : ℝ} (hs : 0 < s)
    (hM : s * Fintype.card T ≤ Fintype.card M) :
    ((Finset.univ.filter (fun m => ¬ HasSecondPreimage H m)).card : ℝ) / Fintype.card M ≤
      1 / s := by
  rcases Nat.eq_zero_or_pos (Fintype.card M) with h0 | hpos
  · simp [h0, hs.le]
  · have hposR : (0 : ℝ) < Fintype.card M := Nat.cast_pos.mpr hpos
    rw [div_le_div_iff₀ hposR hs]
    calc
      ((Finset.univ.filter (fun m => ¬ HasSecondPreimage H m)).card : ℝ) * s
        ≤ (Fintype.card T : ℝ) * s := by
          gcongr
          exact_mod_cast card_not_hasSecondPreimage_le H
      _ = s * Fintype.card T := mul_comm _ _
      _ ≤ 1 * Fintype.card M := by linarith

private theorem map_true_eq_tsum_ite {α : Type*} (p : PMF α)
    (P : α → Bool) :
    (p.map P) true = ∑' x, if P x = true then p x else 0 := by
  rw [PMF.map_apply]
  congr 1 with x
  by_cases h : P x = true
  · simp [h]
  · have hf : P x = false := Bool.eq_false_iff.mpr h
    simp [hf]

/-- For every input `x : M` that has a second preimage `m₀ ≠ x` with `H m₀ = H x`, the probability
that `A (H x)` outputs `x` is bounded by the sum over `m : M` of the probability that `A (H m)`
outputs `x` as a valid second preimage of `m`. -/
private theorem apply_self_le_sum_secondPreimage {M T : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq T] (H : M → T) (A : T → PMF M) {x : M} (hx : HasSecondPreimage H x) :
    A (H x) x ≤ ∑ m : M, if (x != m && H x == H m) = true then A (H m) x else 0 := by
  rcases hx with ⟨m₀, hne, hH⟩
  have h1 : A (H x) x = (if (x != m₀ && H x == H m₀) = true then A (H m₀) x else 0) := by
    simp [hne.symm, hH]
  rw [h1]
  exact Finset.single_le_sum
    (f := fun m => if (x != m && H x == H m) = true then A (H m) x else 0)
    (fun _ _ => zero_le) (Finset.mem_univ m₀)

/-- **Exercise 8.23(b), via part (a)** ([BonehShoup2023], p. 353): on a uniform input from a finite
nonempty domain `M`, wrapping a one-way inverter `A` into the second-preimage finder
`m ↦ A (H m)` bounds the inversion success probability by twice the second-preimage success
probability plus the fraction of inputs without a second preimage. -/
theorem succProbability_inversionExperiment_uniform_le_card_not_hasSecondPreimage
    {M T : Type} [Fintype M] [Nonempty M] [DecidableEq M] [DecidableEq T]
    (H : M → T) (A : T → PMF M) :
    (Game.succProbability (inversionExperiment (uniformOfFintype M) H A) : ℝ) ≤
      2 * (Game.succProbability
        (secondPreimageExperiment (uniformOfFintype M) H (fun m => A (H m))) : ℝ) +
        ((Finset.univ.filter (fun m => ¬ HasSecondPreimage H m)).card : ℝ) / Fintype.card M := by
  let c : ℝ≥0∞ := (Fintype.card M : ℝ≥0∞)⁻¹
  have hspr_sum :
      (secondPreimageExperiment (uniformOfFintype M) H (fun m => A (H m))) true =
        c * ∑ m : M, ∑ x : M, if (x != m && H x == H m) = true then A (H m) x else 0 := by
    rw [secondPreimageExperiment_eq_bind_map, PMF.bind_apply, tsum_fintype]
    simp only [Cslib.Probability.PMF.uniformOfFintype_apply, map_true_eq_tsum_ite, tsum_fintype]
    rw [← Finset.mul_sum]
  have hsplit (m x : M) :
      (if (H x == H m) = true then A (H m) x else 0) =
        (if (x != m && H x == H m) = true then A (H m) x else 0) +
          (if x = m then A (H m) x else 0) := by
    by_cases hxm : x = m
    · subst hxm
      simp
    · have hbne : (x != m) = true := bne_iff_ne.mpr hxm
      simp [hxm, hbne]
  have how_sum :
      (inversionExperiment (uniformOfFintype M) H A) true =
        (secondPreimageExperiment (uniformOfFintype M) H (fun m => A (H m))) true +
          c * ∑ m : M, A (H m) m := by
    rw [hspr_sum, inversionExperiment_eq_bind_map, PMF.bind_apply, tsum_fintype]
    simp only [Cslib.Probability.PMF.uniformOfFintype_apply, map_true_eq_tsum_ite, tsum_fintype]
    rw [← Finset.mul_sum, ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    calc
      ∑ x : M, (if (H x == H m) = true then A (H m) x else 0)
        = (∑ x : M, if (x != m && H x == H m) = true then A (H m) x else 0) +
            ∑ x : M, if x = m then A (H m) x else 0 := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun x _ => hsplit m x
      _ = (∑ x : M, if (x != m && H x == H m) = true then A (H m) x else 0) + A (H m) m := by
          simp
  have hdiag :
      c * ∑ x : M, A (H x) x ≤
        (secondPreimageExperiment (uniformOfFintype M) H (fun m => A (H m))) true +
          (Finset.univ.filter (fun m => ¬ HasSecondPreimage H m)).card * c := by
    have hhas :
        ∑ x ∈ Finset.univ.filter (HasSecondPreimage H), A (H x) x ≤
          ∑ m : M, ∑ x : M, if (x != m && H x == H m) = true then A (H m) x else 0 := by
      rw [Finset.sum_comm]
      calc
        ∑ x ∈ Finset.univ.filter (HasSecondPreimage H), A (H x) x
          ≤ ∑ x ∈ Finset.univ.filter (HasSecondPreimage H),
              ∑ m : M, if (x != m && H x == H m) = true then A (H m) x else 0 :=
            Finset.sum_le_sum fun x hx =>
              apply_self_le_sum_secondPreimage H A (Finset.mem_filter.mp hx).2
        _ ≤ ∑ x : M, ∑ m : M, if (x != m && H x == H m) = true then A (H m) x else 0 :=
            Finset.sum_le_univ_sum_of_nonneg fun _ => zero_le
    have hnot :
        ∑ x ∈ Finset.univ.filter (fun m => ¬ HasSecondPreimage H m), A (H x) x ≤
          (Finset.univ.filter (fun m => ¬ HasSecondPreimage H m)).card := by
      calc
        ∑ x ∈ Finset.univ.filter (fun m => ¬ HasSecondPreimage H m), A (H x) x
          ≤ ∑ _x ∈ Finset.univ.filter (fun m => ¬ HasSecondPreimage H m), (1 : ℝ≥0∞) :=
            Finset.sum_le_sum fun x _ => PMF.coe_le_one (A (H x)) x
        _ = (Finset.univ.filter (fun m => ¬ HasSecondPreimage H m)).card := by simp
    rw [hspr_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (HasSecondPreimage H),
      mul_add, mul_comm _ c]
    exact add_le_add (by gcongr) (by gcongr)
  have henn :
      (inversionExperiment (uniformOfFintype M) H A) true ≤
        2 * (secondPreimageExperiment (uniformOfFintype M) H (fun m => A (H m))) true +
          (Finset.univ.filter (fun m => ¬ HasSecondPreimage H m)).card * c := by
    rw [how_sum, two_mul, add_assoc]
    exact add_le_add le_rfl hdiag
  have hcard_ne : (Fintype.card M : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hfin :
      2 * (secondPreimageExperiment (uniformOfFintype M) H (fun m => A (H m))) true +
          (Finset.univ.filter (fun m => ¬ HasSecondPreimage H m)).card * c ≠ ⊤ := by
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top (PMF.apply_ne_top _ _),
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.inv_ne_top.mpr hcard_ne)⟩
  have hreal := (ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _) hfin).mpr henn
  simpa only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_add
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (PMF.apply_ne_top _ _))
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.inv_ne_top.mpr hcard_ne)),
    ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast, ENNReal.toReal_inv,
    div_eq_mul_inv, c] using hreal

/-- **Exercise 8.23(b), in terms of `|T| / |M|`** ([BonehShoup2023], p. 353). -/
theorem succProbability_inversionExperiment_uniform_le
    {M T : Type} [Fintype M] [Nonempty M] [DecidableEq M] [Fintype T] [DecidableEq T]
    (H : M → T) (A : T → PMF M) :
    (Game.succProbability (inversionExperiment (uniformOfFintype M) H A) : ℝ) ≤
      2 * (Game.succProbability
        (secondPreimageExperiment (uniformOfFintype M) H (fun m => A (H m))) : ℝ) +
        (Fintype.card T : ℝ) / Fintype.card M := by
  refine (succProbability_inversionExperiment_uniform_le_card_not_hasSecondPreimage H A).trans ?_
  gcongr
  exact_mod_cast card_not_hasSecondPreimage_le H

/-- **Exercise 8.23(b), equation (8.22)** ([BonehShoup2023], p. 353): when `|M| ≥ s · |T|` with
`0 < s`, wrapping a one-way inverter `A` into the second-preimage finder `m ↦ A (H m)` satisfies
`OWadv[A, H] ≤ 2 · SPRadv[B, H] + 1 / s`. -/
theorem succProbability_inversionExperiment_uniform_le_of_compression
    {M T : Type} [Fintype M] [Nonempty M] [DecidableEq M] [Fintype T] [DecidableEq T]
    (H : M → T) (A : T → PMF M) {s : ℝ} (hs : 0 < s)
    (hM : s * Fintype.card T ≤ Fintype.card M) :
    (Game.succProbability (inversionExperiment (uniformOfFintype M) H A) : ℝ) ≤
      2 * (Game.succProbability
        (secondPreimageExperiment (uniformOfFintype M) H (fun m => A (H m))) : ℝ) +
        1 / s := by
  refine (succProbability_inversionExperiment_uniform_le_card_not_hasSecondPreimage H A).trans ?_
  exact add_le_add le_rfl (card_not_hasSecondPreimage_div_le H hs hM)

/-! ## Asymptotic second-preimage resistance on bit strings -/

/-- A second-preimage finder receives the unary parameter and the sampled input word. -/
abbrev SecondPreimageFinder := ℕ → List Bool → ProbComp (List Bool)

/-- The second-preimage game at length `n` ([BonehShoup2023], Section 8.11.1, Definition 8.6,
p. 336): `secondPreimageExperiment` for `f` on a uniform `n`-bit input, with the finder told `n`.
Any word `x' ≠ x` with `f x' = f x` wins. -/
@[expose]
noncomputable def secondPreimageGame (f : List Bool → List Bool)
    (adversary : SecondPreimageFinder) (n : ℕ) : ProbComp Bool :=
  secondPreimageExperiment (BitString.sampleList n) f (adversary n)

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
second-preimage finder has negligible success over the uniform `n`-bit input and its own
independent random coins ([BonehShoup2023], Section 8.11.1, Definition 8.6, p. 336). -/
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

end Cslib.Crypto
