/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.OneWay.Normalize
public import CslibFrontier.Crypto.Computational.OneWay.Weak
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Probability.PMF.Bind

/-!
# Length-preserving one-way functions

If one-way functions exist, then length-preserving one-way functions exist
[Goldreich, Exercise 7.1][Goldreich2007DraftR4]: some one-way function `f'` has `|f'(x)| = |x|` for
every `x` (`Cslib.Crypto.OneWay.exists_lengthPreserving`).

The construction follows the guideline of the exercise. Normalize the output length of a one-way
function `g` to `L(|x|)` (`Cslib.Crypto.OneWay.exists_fixedOutputLength`), and choose the
input-length schedule `m(n) = 4 n + 2 L(n) + 3`. On an input `z`, let `n` be the greatest parameter
with `m(n) ≤ |z|` and evaluate `g` on the `n`-bit prefix of `z`, pairing the image with `n`
(`Cslib.Crypto.OneWayReindex.reindex`). The result has `2 n + 1 + L(n)` bits, so its
self-delimiting padding fits into `|z|` bits (`Cslib.Crypto.OneWayLengthPreserving.fit`). The
guideline pads `f(x)` by `0 1 ^ (|z| - |f(x)| - 1)` and inverts the schedule `n ↦ p(n)`; here the
padding is the library's self-delimiting `padWord`, and the image also records `n`, so that images
of different parameters are disjoint and the reindexing reduction of
`Cslib.Crypto.OneWayReindex.oneWay` applies to any polynomial-time schedule.

## Main definitions

* `Cslib.Crypto.OneWayLengthPreserving.fit`: the first `k` bits of the self-delimiting padding.
* `Cslib.Crypto.OneWayLengthPreserving.lengthPreserving`: the length-preserving function built
  from a function with output length `L(|x|)`.

## Main results

* `Cslib.Crypto.OneWayLengthPreserving.inversion_le`: an inverter for the length-preserving
  function yields an inverter for the reindexed function at every length `M ≥ m(0)`.
* `Cslib.Crypto.OneWayLengthPreserving.oneWay`: the construction is one-way.
* `Cslib.Crypto.OneWay.exists_lengthPreserving`: Goldreich, Exercise 7.1.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft `r4.pdf` of
  March 2007][Goldreich2007DraftR4], Exercise 7.1 (printed page 305, PDF page 41).
-/

@[expose] public section

namespace Cslib.Crypto

open Filter Probability Turing.MultiTapeTM

namespace OneWayLengthPreserving

/-! ### Fitting a word into a fixed number of bits -/

/-- The first `k` bits of the self-delimiting padding of `word` (`Cslib.BitString.padWord`). A word
with `2 |word| + 1 ≤ k` can be read back from the result (`word_eq_of_fit_eq`). -/
def fit (k : ℕ) (word : List Bool) : List Bool :=
  (BitString.padWord k word).take k

/-- Fitting always produces exactly `k` bits. -/
@[simp]
theorem length_fit (k : ℕ) (word : List Bool) : (fit k word).length = k := by
  simp only [fit, BitString.padWord, List.length_take, List.length_append, length_frame,
    List.length_replicate]
  omega

/-- Words with `2 |word| + 1 ≤ k` are determined by their fitted form. -/
theorem word_eq_of_fit_eq {k : ℕ} {word word' : List Bool} (hword : 2 * word.length + 1 ≤ k)
    (hword' : 2 * word'.length + 1 ≤ k) (h : fit k word = fit k word') : word = word' := by
  simp only [fit, BitString.padWord, List.take_append, length_frame,
    List.take_of_length_le (show (frame word).length ≤ k by rwa [length_frame]),
    List.take_of_length_le (show (frame word').length ≤ k by rwa [length_frame])] at h
  exact (frame_append_inj h).1

/-! ### The construction -/

/-- The input-length schedule `m(n) = 4 n + 2 L(n) + 3`: parameter `n` reads this many input
bits, enough room for the padded image of `n` and `g` on `n` bits. -/
def schedule (L : ℕ → ℕ) (n : ℕ) : ℕ :=
  4 * n + 2 * L n + 3

/-- The parameter-indexed family: `g` on the `n`-bit prefix. -/
def core (g : List Bool → List Bool) (n : ℕ) (word : List Bool) : List Bool :=
  g (word.take n)

/-- The length-preserving function: reindex `g` along `schedule L` and fit the result into `|x|`
bits. -/
def lengthPreserving (g : List Bool → List Bool) (L : ℕ → ℕ) (x : List Bool) : List Bool :=
  fit x.length (OneWayReindex.reindex (schedule L) (core g) x)

@[simp]
theorem length_lengthPreserving (g : List Bool → List Bool) (L : ℕ → ℕ) (x : List Bool) :
    (lengthPreserving g L x).length = x.length :=
  length_fit _ _

/-- From length `m(0)` on, the reindexed image fits: twice its length plus one is at most the
input length. -/
theorem two_mul_length_reindex_add_one_le {g : List Bool → List Bool} {L : ℕ → ℕ}
    (hg : ∀ x, (g x).length = L x.length) {x : List Bool} (hx : schedule L 0 ≤ x.length) :
    2 * (OneWayReindex.reindex (schedule L) (core g) x).length + 1 ≤ x.length := by
  set n := GeneratorReindex.parameter (schedule L) x.length
  have hfits : schedule L n ≤ x.length := GeneratorReindex.parameter_fits hx
  have hn : n ≤ schedule L n := by unfold schedule; omega
  have hcore : (core g n (x.take (schedule L n))).length = L n := by
    simp only [core, hg, List.take_take, List.length_take]
    congr 1
    omega
  have hlen : (OneWayReindex.reindex (schedule L) (core g) x).length = 2 * n + 1 + L n := by
    change (OneWayReindex.wrappedImage n (core g n (x.take (schedule L n)))).length = _
    simp only [OneWayReindex.wrappedImage, length_encPair]
    rw [show (encBits (core g n (x.take (schedule L n)))).length = L n from hcore,
      show (encUnary n).length = n from List.length_replicate]
  rw [hlen]
  unfold schedule at hfits
  omega

/-- **Inversion reduction.** At every length `M ≥ m(0)`, an inverter for the length-preserving
function inverts the reindexed function at least as well once its challenge is fitted into `M`
bits: a successful candidate has length `M`, and fitting is injective on the images that occur. -/
theorem inversion_le {g : List Bool → List Bool} {L : ℕ → ℕ}
    (hg : ∀ x, (g x).length = L x.length) (adversary : Inverter) {M : ℕ}
    (hM : schedule L 0 ≤ M) :
    Game.succProbability (ProbComp.eval (inversionGame (lengthPreserving g L) adversary M)) ≤
      Game.succProbability (ProbComp.eval (inversionGame
        (OneWayReindex.reindex (schedule L) (core g)) (fun n image => adversary n (fit n image))
        M)) := by
  apply ENNReal.toNNReal_mono (PMF.apply_ne_top _ _)
  simp only [inversionGame, inversionExperiment, ProbComp.eval_bind, BitString.eval_sampleList]
  apply PMF.bind_apply_mono_on_support _ true
  intro input hinput
  have hlen : input.length = M := BitString.length_of_mem_support_uniformList hinput
  simp only [lengthPreserving, hlen]
  apply PMF.bind_apply_mono_on_support _ true
  intro candidate _
  simp only [ProbComp.eval_pure, PMF.pure_apply]
  by_cases h : fit candidate.length (OneWayReindex.reindex (schedule L) (core g) candidate) =
      fit M (OneWayReindex.reindex (schedule L) (core g) input)
  · have hc : candidate.length = M := by simpa using congrArg List.length h
    have hcand := two_mul_length_reindex_add_one_le hg (x := candidate) (by omega)
    have hinput := two_mul_length_reindex_add_one_le hg (x := input) (by omega)
    rw [hc] at h hcand
    rw [hlen] at hinput
    rw [word_eq_of_fit_eq hcand hinput h]
    simp [hc]
  · simp [h]

/-- The parameter-indexed game for `core g` is the inversion game for `g` against the inverter
that truncates its candidate to `n` bits. -/
theorem eval_familyInversionGame_core (g : List Bool → List Bool) (L : ℕ → ℕ)
    (adversary : Inverter) (n : ℕ) :
    ProbComp.eval (OneWayReindex.familyInversionGame (schedule L) (core g) adversary n) =
      ProbComp.eval (inversionGame g (fun n image => List.take n <$> adversary n image) n) := by
  have hn : n ≤ schedule L n := by unfold schedule; omega
  simp only [OneWayReindex.familyInversionGame, inversionGame, inversionExperiment, core,
    ProbComp.eval_bind, ProbComp.eval_map, BitString.eval_sampleList, List.take_take,
    Nat.min_eq_left hn, ProbComp.eval_pure]
  rw [← BitString.uniformList_take hn, PMF.bind_map]
  refine congrArg _ (funext fun a => ?_)
  simp only [Function.comp_apply, PMF.bind_map]
  rfl

end OneWayLengthPreserving

open OneWayLengthPreserving

/-- **The length-preserving construction is one-way.** If `g` is one-way with output length
`L(|x|)`, computable in unary polynomial time, then `lengthPreserving g L` is one-way. -/
theorem OneWayLengthPreserving.oneWay {g : List Bool → List Bool} {L : ℕ → ℕ} (hg : OneWay g)
    (hlen : ∀ x, (g x).length = L x.length) (hL : ComputableInPolyTime L encUnary encUnary) :
    OneWay (lengthPreserving g L) := by
  have hm : ComputableInPolyTime (schedule L) encUnary encUnary := by
    unfold schedule
    fun_prop
  have hcore : ComputableInPolyTime (fun p : ℕ × List Bool => core g p.1 p.2)
      (encPair encUnary encBits) encBits := by
    have := hg.polyTime
    unfold core
    fun_prop
  have hreindex : OneWay (OneWayReindex.reindex (schedule L) (core g)) :=
    OneWayReindex.oneWay hm (fun n => by unfold schedule; omega) hcore fun adversary hPPT => by
      have htrunc : IsPPT encBits (fun n image => List.take n <$> adversary n image) :=
        IsPPTOn.map_with (f := fun (p : ℕ × List Bool) (c : List Bool) => c.take p.1) hPPT.on
          (by fun_prop)
      simpa only [eval_familyInversionGame_core] using hg.inversion_negligible _ htrunc
  refine OneWay.of_inversion_negligible ?_ fun adversary hPPT => ?_
  · have := OneWayReindex.computableInPolyTime_reindex hm hcore
    unfold lengthPreserving fit
    fun_prop
  · have hfit : IsPPT encBits (fun n image => adversary n (fit n image)) := by
      refine IsPPTOn.isPPT (hPPT.preprocess (parameter := Prod.fst)
        (auxiliary := fun p : ℕ × List Bool => fit p.1 p.2) ?_ ?_)
      · fun_prop
      · unfold fit
        fun_prop
    exact negligible_of_eventually_le (hreindex.inversion_negligible _ hfit)
      (eventually_ge_atTop (schedule L 0) |>.mono fun M hM => inversion_le hlen adversary hM)

/-- **[Goldreich, Exercise 7.1][Goldreich2007DraftR4]**: if one-way functions exist, then
length-preserving one-way functions exist. From any one-way function `f` we obtain a one-way
function `f'` with `|f'(x)| = |x|` for every `x`. One-wayness is `Cslib.Crypto.OneWay`: polynomial
time evaluation, and negligible inversion probability against uniform strict PPT inverters. -/
theorem OneWay.exists_lengthPreserving {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ f' : List Bool → List Bool, OneWay f' ∧ ∀ x, (f' x).length = x.length := by
  obtain ⟨g, L, hg, hlen, hL⟩ := hf.exists_fixedOutputLength
  exact ⟨lengthPreserving g L, OneWayLengthPreserving.oneWay hg hlen hL,
    length_lengthPreserving g L⟩

end Cslib.Crypto
