/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.Compression.Basic
public import CslibFrontier.MachineLearning.PACLearning.DualVCDimension
public import CslibFrontier.MachineLearning.PACLearning.EpsilonApproximation
public import CslibFrontier.MachineLearning.PACLearning.EpsilonNet
public import CslibFrontier.MachineLearning.PACLearning.FundamentalTheorem
import CslibFrontier.MachineLearning.PACLearning.Compression.Shattering
import CslibFrontier.MachineLearning.PACLearning.Compression.VCDimension
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.TFAE

/-!
# Sample compression schemes for VC classes (Moran–Yehudayoff)

Moran and Yehudayoff [MoranYehudayoff2016] resolved the sample compression conjecture of
Littlestone and Warmuth [LittlestoneWarmuth1986] qualitatively by showing that every binary
concept class `C` of finite VC dimension `d` admits a labeled sample compression scheme of size
exponential in `d`, via its dual VC dimension `d*` (which satisfies `d* < 2 ^ (d + 1)` by
Assouad's bound, `DualVCDimension.lean`).

This module combines the three pieces already in the library to build the full compression scheme
on an **arbitrary** domain type `α` (no countability or measurability assumptions):

1. Weak learning & minimax
   (`CslibFrontier/MachineLearning/PACLearning/Compression/VCDimension.lean`,
   `IsConsistent.exists_pmf_subsample_toOuterMeasure_le`): given any nonempty sample `S` of `m`
   examples realized by `C` and any consistent learner `A` reading `s ≥ vcSampleSize d (1/3) (1/2)`
   examples, there exists a distribution `μ : PMF (Fin s → Fin m)` on index tuples such that at
   every position `i : Fin m`, `μ {b | A (S ∘ b) (S i).1 ≠ (S i).2} ≤ 1 / 3`.
2. Precomposed dual VC bound (`DualVCDimension.lean`, `SetShatters.card_le_of_comp`): mapping
   `b ↦ ⟨A (S ∘ b), _⟩ : ↥C` pulls `dualClass C` back to a class `G` on the finite set
   `Fin s → Fin m` whose shattered sets have size at most `d*`.
3. `ε`-approximations (`EpsilonApproximation.lean`,
   `exists_isEpsApprox_of_uniformConvergenceSampleSize_le`): because `Fin s → Fin m` is finite
   (hence countable with discrete σ-algebra), `μ.toMeasure` admits a `1/6`-approximation
   `B : Fin t → (Fin s → Fin m)` for `G` of size `t ≥ uniformConvergenceSampleSize d* (1/6) (1/2)`.
   At every `i : Fin m`, the fraction of `j : Fin t` predicting `true` is `> 2/3 - 1/6 = 1/2` when
   `(S i).2 = true` and `< 1/3 + 1/6 = 1/2` when `(S i).2 = false` (strict majority, no ties).

## Relation to the published model

In [MoranYehudayoff2016, Theorem 1.4] (locator unverified), a *labeled* compression scheme returns
an unordered subset `T : Finset (α × Bool)` of at most `k` examples plus side-information bits;
indexing a `t × s` table into a canonical enumeration of `T` uses `|T| ≤ t * s` distinct examples
and fixed side-information alphabet `Fin t → Fin s → Fin (t * s)` of cardinality `(t * s) ^ (t * s)`
(`O(d* d log (d* d))` bits of side information). In this library's `SampleCompressionScheme` type
(`CslibFrontier/MachineLearning/PACLearning/Compression/Basic.lean`), the compressor outputs an
**ordered** `List (Fin m)` with repetitions allowed, so flattening `B : Fin t → Fin s → Fin m`
requires exact length `t * s = O(d* d)` with no extra side bits. Both forms are provided:
`exists_finset_compression_of_dualVCDim` (sample-independent decoder `ρ` from an unordered
`Finset (α × Bool)` plus side info in `Fin t → Fin s → Fin (t * s)`) and `moranYehudayoffScheme`
(ordered `SampleCompressionScheme`).

Note that our `t` (`moranYehudayoffMajoritySize`) uses Vapnik–Chervonenkis uniform convergence at
the *constant* accuracy `ε = 1/6`, so even the `log (1/ε)` factor of `EpsilonApproximation.lean`
is an absolute constant `log 60`, keeping `t = O(d*)` and `s = O(d)` strictly linear with no
`log d` or `log d*` overhead.

## Main definitions

- `moranYehudayoffSubsampleSize d`: subsample size `s = ⌈vcSampleSize d (1/3) (1/2)⌉₊ ≤ 120 d + 60`.
- `moranYehudayoffMajoritySize dStar`: majority ensemble size
  `t = ⌈uniformConvergenceSampleSize dStar (1/6) (1/2)⌉₊ ≤ 5184 d* + 1440`.
- `moranYehudayoffCompressionSize d dStar`: product `t * s = O(d* d)`.
- `moranYehudayoffVCCompressionSize d`: specialization `d* = 2 ^ (d + 1) - 1`, giving `O(d · 2^d)`.
- `moranYehudayoffScheme`: explicit `SampleCompressionScheme C (moranYehudayoffCompressionSize d
  dStar)`.
- `moranYehudayoffSchemeOfVCDim`: explicit `SampleCompressionScheme C
  (moranYehudayoffVCCompressionSize d)`.

## Main results

- `exists_majority_subsamples_of_dualVCDim`: `t` subsamples of length `s` whose strict majority
  vote under a consistent learner `A` matches every label of `S`.
- `exists_finset_compression_of_dualVCDim`: sample-independent reconstruction map
  `ρ : Finset (α × Bool) → (Fin t → Fin s → Fin (t * s)) → α → Bool` such that every realizable
  sample `S` compresses to an unordered subset `T : Finset (α × Bool)` of size `≤ t * s` drawn from
  `S` plus side information `info : Fin t → Fin s → Fin (t * s)` (`(t * s) ^ (t * s)` tables).
- `exists_sampleCompressionScheme_iff_hasFiniteVCDim`: a binary concept class on **any** type `α`
  has a sample compression scheme of finite size iff it has finite VC dimension.
- `tfae_hasFiniteVCDim_compression`: adds finite-size sample compression to the six-way fundamental
  theorem of statistical learning (`FundamentalTheorem.lean`, `tfae_hasFiniteVCDim`).

## References

* [S. Moran, A. Yehudayoff, *Sample compression schemes for VC classes*][MoranYehudayoff2016]
  (Theorem 1.3, Theorem 1.4, Claim 3.1; locators unverified)
* [N. Littlestone, M. K. Warmuth, *Relating data compression and learnability*]
  [LittlestoneWarmuth1986] (locator unverified)
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014] (Theorem 6.7; locator unverified)
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Cslib.MachineLearning.PACLearning

/-! ### Explicit compression parameters and algebraic bounds -/

/-- Subsample size `s` for weak learning at accuracy `1/3` and confidence `1/2` in the
Moran–Yehudayoff construction (`O(d)`). -/
@[expose] noncomputable def moranYehudayoffSubsampleSize (d : ℕ) : ℕ :=
  ⌈vcSampleSize d (1 / 3) (1 / 2)⌉₊

/-- Majority-ensemble size `t` for a `1/6`-approximation of the dual class at confidence `1/2`
(`O(d*)`). -/
@[expose] noncomputable def moranYehudayoffMajoritySize (dStar : ℕ) : ℕ :=
  ⌈uniformConvergenceSampleSize dStar (1 / 6) (1 / 2)⌉₊

/-- Total ordered sample compression size `t * s` in terms of VC dimension `d` and dual VC
dimension `d*` (`O(d* · d)`). -/
@[expose] noncomputable def moranYehudayoffCompressionSize (d dStar : ℕ) : ℕ :=
  moranYehudayoffMajoritySize dStar * moranYehudayoffSubsampleSize d

/-- Total ordered sample compression size parameterized by the VC dimension `d` alone, plugging in
Assouad's dual VC bound `d* ≤ 2 ^ (d + 1) - 1` (`O(d · 2 ^ d)`). -/
@[expose] noncomputable def moranYehudayoffVCCompressionSize (d : ℕ) : ℕ :=
  moranYehudayoffCompressionSize d (2 ^ (d + 1) - 1)

private theorem exp_five_gt_144 : (144 : ℝ) < Real.exp 5 := by
  have he : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  calc (144 : ℝ) < (2.718 : ℝ) ^ 5 := by norm_num
    _ < (Real.exp 1) ^ 5 := by gcongr
    _ = Real.exp (5 : ℝ) := by rw [← Real.exp_nat_mul]; norm_num

private theorem log_144_lt_five : Real.log 144 < 5 := by
  rw [← Real.log_exp (5 : ℝ)]
  exact Real.log_lt_log (by norm_num) exp_five_gt_144

private theorem log_lt_half_of_sq_lt_exp {a : ℝ} (n : ℕ) (ha : 0 < a)
    (h : a ^ 2 < Real.exp (n : ℝ)) : Real.log a < (n : ℝ) / 2 := by
  have hlog : Real.log (a ^ 2) < n := by
    rw [← Real.log_exp (n : ℝ)]
    exact Real.log_lt_log (pow_pos ha 2) h
  rw [Real.log_pow] at hlog
  push_cast at hlog
  linarith

private theorem log_8_lt_five_div_two : Real.log 8 < 5 / 2 :=
  log_lt_half_of_sq_lt_exp 5 (by norm_num) (by push_cast; linarith [exp_five_gt_144])

private theorem log_60_lt_nine_div_two : Real.log 60 < 9 / 2 := by
  have he : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  refine log_lt_half_of_sq_lt_exp 9 (by norm_num) ?_
  calc (60 : ℝ) ^ 2 < (2.718 : ℝ) ^ 9 := by norm_num
    _ < (Real.exp 1) ^ 9 := by gcongr
    _ = Real.exp ((9 : ℕ) : ℝ) := by rw [← Real.exp_nat_mul]; norm_num

private theorem vcSampleSize_one_third_half_pos (d : ℕ) :
    0 < vcSampleSize d (1 / 3) (1 / 2) := by
  rw [vcSampleSize]
  have h1 : 0 ≤ Real.log (48 / (1 / 3)) := Real.log_nonneg (by norm_num)
  have h2 : 0 < Real.log (4 / (1 / 2)) := Real.log_pos (by norm_num)
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hmul : 0 ≤ (d : ℝ) * Real.log (48 / (1 / 3)) := mul_nonneg hd h1
  positivity

private theorem uniformConvergenceSampleSize_one_sixth_half_pos (dStar : ℕ) :
    0 < uniformConvergenceSampleSize dStar (1 / 6) (1 / 2) := by
  rw [uniformConvergenceSampleSize]
  have h1 : 0 ≤ Real.log (10 / (1 / 6)) := Real.log_nonneg (by norm_num)
  have h2 : 0 < Real.log (4 / (1 / 2)) := Real.log_pos (by norm_num)
  have hd : (0 : ℝ) ≤ dStar := Nat.cast_nonneg dStar
  have hmul : 0 ≤ 2 * (dStar : ℝ) * Real.log (10 / (1 / 6)) := by positivity
  positivity

/-- The subsample size `moranYehudayoffSubsampleSize d` is strictly positive. -/
theorem moranYehudayoffSubsampleSize_pos (d : ℕ) : 0 < moranYehudayoffSubsampleSize d :=
  Nat.ceil_pos.2 (vcSampleSize_one_third_half_pos d)

/-- The majority-ensemble size `moranYehudayoffMajoritySize dStar` is strictly positive. -/
theorem moranYehudayoffMajoritySize_pos (dStar : ℕ) : 0 < moranYehudayoffMajoritySize dStar :=
  Nat.ceil_pos.2 (uniformConvergenceSampleSize_one_sixth_half_pos dStar)

/-- Explicit linear bound `moranYehudayoffSubsampleSize d ≤ 120 * d + 60`. -/
theorem moranYehudayoffSubsampleSize_le (d : ℕ) :
    moranYehudayoffSubsampleSize d ≤ 120 * d + 60 := by
  refine Nat.ceil_le.2 ?_
  rw [vcSampleSize]
  have h144 : (48 : ℝ) / (1 / 3) = 144 := by norm_num
  have h8 : (4 : ℝ) / (1 / 2) = 8 := by norm_num
  have h24 : (8 : ℝ) / (1 / 3) = 24 := by norm_num
  rw [h144, h8, h24]
  push_cast
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hmul : (d : ℝ) * Real.log 144 ≤ (d : ℝ) * 5 :=
    mul_le_mul_of_nonneg_left log_144_lt_five.le hd
  linarith [log_8_lt_five_div_two]

/-- Explicit linear bound `moranYehudayoffMajoritySize dStar ≤ 5184 * dStar + 1440`. -/
theorem moranYehudayoffMajoritySize_le (dStar : ℕ) :
    moranYehudayoffMajoritySize dStar ≤ 5184 * dStar + 1440 := by
  refine Nat.ceil_le.2 ?_
  rw [uniformConvergenceSampleSize]
  have h60 : (10 : ℝ) / (1 / 6) = 60 := by norm_num
  have h8 : (4 : ℝ) / (1 / 2) = 8 := by norm_num
  have h576 : (16 : ℝ) / (1 / 6) ^ 2 = 576 := by norm_num
  rw [h60, h8, h576]
  push_cast
  have hd : (0 : ℝ) ≤ dStar := Nat.cast_nonneg dStar
  have hmul : 2 * (dStar : ℝ) * Real.log 60 ≤ 2 * (dStar : ℝ) * (9 / 2) :=
    mul_le_mul_of_nonneg_left log_60_lt_nine_div_two.le (by positivity)
  linarith [log_8_lt_five_div_two]

/-- Explicit bilinear bound `moranYehudayoffCompressionSize d dStar = O(d* · d)`. -/
theorem moranYehudayoffCompressionSize_le (d dStar : ℕ) :
    moranYehudayoffCompressionSize d dStar ≤ (5184 * dStar + 1440) * (120 * d + 60) :=
  Nat.mul_le_mul (moranYehudayoffMajoritySize_le dStar) (moranYehudayoffSubsampleSize_le d)

/-- Explicit exponential bound `moranYehudayoffVCCompressionSize d = O(d · 2 ^ d)`. -/
theorem moranYehudayoffVCCompressionSize_le (d : ℕ) :
    moranYehudayoffVCCompressionSize d ≤ (5184 * 2 ^ (d + 1) + 1440) * (120 * d + 60) :=
  (moranYehudayoffCompressionSize_le d (2 ^ (d + 1) - 1)).trans <|
    Nat.mul_le_mul_right _ (by gcongr; exact Nat.sub_le _ _)

/-! ### Majority voting over a family of subsamples -/

section MajorityVote

variable {α : Type*}

/-- Flatten a family `B : Fin t → Fin s → Fin m` of `t` subsamples of size `s` into a single list
of `t * s` indices using `finProdFinEquiv`. -/
private def flattenSubsamples {m t s : ℕ} (B : Fin t → Fin s → Fin m) : List (Fin m) :=
  List.ofFn fun p : Fin (t * s) =>
    let q := finProdFinEquiv.symm p
    B q.1 q.2

private theorem length_flattenSubsamples {m t s : ℕ} (B : Fin t → Fin s → Fin m) :
    (flattenSubsamples B).length = t * s := by
  simp only [flattenSubsamples, List.length_ofFn]

/-- **Majority-vote reconstruction**: given a base learner `A : Learner α Bool s` and a flat list
`xs` of `t * s` labeled examples, split `xs` into `t` consecutive subsamples of length `s`, apply
`A` to each, and return `true` iff strictly more than half of the `t` hypotheses return `true`.
When `xs.length ≠ t * s` it defaults to `false`. -/
private def majorityReconstruct {s : ℕ} (A : Learner α Bool s) (t : ℕ)
    (xs : List (α × Bool)) (x : α) : Bool :=
  if h : xs.length = t * s then
    let sub : Fin t → LabeledSample α Bool s := fun j u =>
      xs[(finProdFinEquiv (j, u)).1]'(by rw [h]; exact (finProdFinEquiv (j, u)).2)
    decide (t < 2 * (Finset.univ.filter fun j : Fin t => A (sub j) x = true).card)
  else
    false

private theorem majorityReconstruct_map_flattenSubsamples {m t s : ℕ}
    (A : Learner α Bool s) (S : LabeledSample α Bool m) (B : Fin t → Fin s → Fin m) (x : α) :
    majorityReconstruct A t ((flattenSubsamples B).map S) x =
      decide (t < 2 * (Finset.univ.filter fun j : Fin t => A (S ∘ B j) x = true).card) := by
  have hlen : ((flattenSubsamples B).map S).length = t * s := by
    rw [List.length_map, length_flattenSubsamples]
  unfold majorityReconstruct
  rw [dite_eq_left_of_eq_true (eq_true hlen)]
  have hsub : ∀ j : Fin t,
      (fun u : Fin s => ((flattenSubsamples B).map S)[(finProdFinEquiv (j, u)).1]'(by
        rw [hlen]; exact (finProdFinEquiv (j, u)).2)) = S ∘ B j := fun j => funext fun u => by
    simp only [flattenSubsamples, List.getElem_map, List.getElem_ofFn, Function.comp_apply,
      Fin.eta, Equiv.symm_apply_apply]
  refine congrArg (fun n => decide (t < 2 * n)) (congrArg Finset.card ?_)
  exact Finset.filter_congr fun j _ => by dsimp only; rw [hsub j]

/-- A canonical consistent learner for `C`: picks an arbitrary concept of `C` consistent with a
realizable sample, and `fun _ => false` otherwise. -/
private noncomputable def canonicalConsistentLearner (C : ConceptClass α Bool) (s : ℕ) :
    Learner α Bool s :=
  fun T =>
    letI := Classical.propDecidable
    if h : Realizable C T then Classical.choose h else fun _ => false

private theorem isConsistent_canonicalConsistentLearner (C : ConceptClass α Bool) (s : ℕ) :
    IsConsistent (canonicalConsistentLearner C s) C := by
  intro T hT
  have hdef : canonicalConsistentLearner C s T = Classical.choose hT := by
    unfold canonicalConsistentLearner
    split_ifs
    rfl
  rw [hdef]
  obtain ⟨hc, hcT⟩ := Classical.choose_spec hT
  exact ⟨hc, fun i => (hcT i).symm⟩

/-- **Existence of a majority-voting ensemble of subsamples** [MoranYehudayoff2016, Claim 3.1]
(locator unverified). Let `C` be a binary concept class whose finite shattered sets have size at
most `d` and whose dual class has finite shattered sets of size at most `dStar`. For every
consistent learner `A` reading `s ≥ vcSampleSize d (1/3) (1/2)` examples, every
`t ≥ uniformConvergenceSampleSize dStar (1/6) (1/2)`, and every nonempty sample `S` realized by
`C`, there exists a family `B : Fin t → Fin s → Fin m` of `t` subsamples of length `s` such that
at every example `i : Fin m`, strictly more than half of the hypotheses `A (S ∘ B j)` predict
`(S i).2`. -/
theorem exists_majority_subsamples_of_dualVCDim {C : ConceptClass α Bool} {d dStar : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d)
    (hdual : ∀ F : Finset ↥C, SetShatters (dualClass C) ↑F → F.card ≤ dStar)
    {s t : ℕ} {A : Learner α Bool s} (hA : IsConsistent A C)
    (hs : vcSampleSize d (1 / 3) (1 / 2) ≤ s)
    (ht : uniformConvergenceSampleSize dStar (1 / 6) (1 / 2) ≤ t)
    {m : ℕ} (hm : 0 < m) {S : LabeledSample α Bool m} (hS : Realizable C S) :
    ∃ B : Fin t → Fin s → Fin m,
      ∀ i : Fin m,
        t < 2 * (Finset.univ.filter fun j : Fin t => A (S ∘ B j) (S i).1 = (S i).2).card := by
  classical
  -- Step 1: minimax distribution `μ` on length-`s` index tuples (`error ≤ 1/3` at every `i`).
  obtain ⟨μ, hμ⟩ := hA.exists_pmf_subsample_toOuterMeasure_le hC
    (ε := 1 / 3) (δ := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hs hm hS
  -- Every subsample `S ∘ b` is realized by `C`, so `A (S ∘ b) ∈ C`.
  obtain ⟨c₀, hc₀, hc₀S⟩ := hS
  have hA_mem (b : Fin s → Fin m) : A (S ∘ b) ∈ C :=
    (hA (S ∘ b) ⟨c₀, hc₀, fun u => hc₀S (b u)⟩).1
  let φ : (Fin s → Fin m) → ↥C := fun b => ⟨A (S ∘ b), hA_mem b⟩
  let G : ConceptClass (Fin s → Fin m) Bool := (fun g => g ∘ φ) '' dualClass C
  -- Step 2: equip the finite space `Fin s → Fin m` with the discrete measurable space.
  let _ : MeasurableSpace (Fin s → Fin m) := ⊤
  have _ : MeasurableSingletonClass (Fin s → Fin m) := ⟨fun _ => trivial⟩
  have hG : ∀ W : Finset (Fin s → Fin m), SetShatters G ↑W → W.card ≤ dStar :=
    fun W hW => SetShatters.card_le_of_comp hdual hW
  -- Step 3: `1/6`-approximation `B` of size `t` for `G` under `μ.toMeasure`.
  obtain ⟨B, hB⟩ := exists_isEpsApprox_of_uniformConvergenceSampleSize_le
    μ.toMeasure hG (ε := 1 / 6) (δ := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ht
  refine ⟨B, fun i => ?_⟩
  have htpos : (0 : ℝ) < t :=
    lt_of_lt_of_le (uniformConvergenceSampleSize_one_sixth_half_pos dStar) ht
  let g : (Fin s → Fin m) → Bool := (fun c : ↥C => (c : α → Bool) (S i).1) ∘ φ
  have hgG : g ∈ G :=
    ⟨fun c : ↥C => (c : α → Bool) (S i).1, mem_dualClass.2 ⟨(S i).1, rfl⟩, rfl⟩
  have happrox := abs_lt.1 (hB g hgG)
  set c := (Finset.univ.filter fun j => g (B j) = true).card with hc
  have hμi : (μ.toMeasure {b | A (S ∘ b) (S i).1 ≠ (S i).2}).toReal ≤ 1 / 3 := by
    rw [PMF.toMeasure_apply_eq_toOuterMeasure]
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (hμ i)
  cases hy : (S i).2
  · -- When `(S i).2 = false`, `{g = true}` is the error set, so `μ {g = true} ≤ 1/3`.
    have hset : {b : Fin s → Fin m | g b = true} = {b | A (S ∘ b) (S i).1 ≠ (S i).2} := by
      ext b; simp [g, φ, hy]
    have hprob : (μ.toMeasure {b | g b = true}).toReal ≤ 1 / 3 := hset ▸ hμi
    have hlt := (div_lt_iff₀ htpos).1 (by linarith [happrox.2] : (c : ℝ) / t < 1 / 2)
    have hlt_nat : 2 * c < t := by exact_mod_cast (by linarith : (2 * c : ℝ) < t)
    have hcard_sum :
        (Finset.univ.filter fun j : Fin t => A (S ∘ B j) (S i).1 = false).card + c = t := by
      rw [hc, add_comm]
      simpa only [g, φ, Function.comp_apply, Bool.not_eq_true, Finset.card_univ,
        Fintype.card_fin] using Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin t))) (p := fun j => g (B j) = true)
    omega
  · -- When `(S i).2 = true`, `{g = true}` is the error set's complement, so `μ {g = true} ≥ 2/3`.
    have hcompl : {b : Fin s → Fin m | g b = true} =
        ({b | A (S ∘ b) (S i).1 ≠ (S i).2})ᶜ := by
      ext b; simp [g, φ, hy]
    have hmeas_err : μ.toMeasure {b | A (S ∘ b) (S i).1 ≠ (S i).2} ≠ ⊤ :=
      measure_ne_top _ _
    have hcompl_eq : (μ.toMeasure {b | g b = true}).toReal =
        1 - (μ.toMeasure {b | A (S ∘ b) (S i).1 ≠ (S i).2}).toReal := by
      rw [hcompl, measure_compl (Set.toFinite _).measurableSet hmeas_err, measure_univ,
        ENNReal.toReal_sub_of_le (prob_le_one) ENNReal.one_ne_top, ENNReal.toReal_one]
    have hgt := (lt_div_iff₀ htpos).1 (by linarith [happrox.1] : 1 / 2 < (c : ℝ) / t)
    have hlt_nat : t < 2 * c := by exact_mod_cast (by linarith : (t : ℝ) < 2 * c)
    simpa only [hc, g, φ, Function.comp_apply] using hlt_nat

/-- Strict majority correctness expressed via `decide (t < 2 * count_true) = (S i).2`. -/
private theorem decide_majority_eq_label {t : ℕ} (f : Fin t → Bool) (y : Bool)
    (h : t < 2 * (Finset.univ.filter fun j => f j = y).card) :
    decide (t < 2 * (Finset.univ.filter fun j => f j = true).card) = y := by
  cases y
  · have hsum : (Finset.univ.filter fun j => f j = true).card +
        (Finset.univ.filter fun j => f j = false).card = t := by
      simpa only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] using
        Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin t)))
          (p := fun j => f j = true)
    exact decide_eq_false (by omega)
  · exact decide_eq_true h

/-- Sample-independent decoder from an unordered `Finset (α × Bool)` and fixed side-information
table `info : Fin t → Fin s → Fin (t * s)`. Enumerates `T` solely via `Fintype.equivFinOfCardEq`,
decodes each pointer `info j u` modulo `T.card`, and takes the strict majority vote of `A`. -/
private noncomputable def finsetSideReconstruct {s : ℕ} (A : Learner α Bool s) (t : ℕ)
    (T : Finset (α × Bool)) (info : Fin t → Fin s → Fin (t * s)) (x : α) : Bool :=
  if h : 0 < T.card then
    let e : T ≃ Fin T.card := Fintype.equivFinOfCardEq (Fintype.card_coe T)
    let sub : Fin t → LabeledSample α Bool s := fun j u =>
      (e.symm ⟨(info j u).1 % T.card, Nat.mod_lt _ h⟩).1
    decide (t < 2 * (Finset.univ.filter fun j : Fin t => A (sub j) x = true).card)
  else
    false

/-- **Unordered-subset plus side-information form of Moran–Yehudayoff** [MoranYehudayoff2016,
Theorem 1.4] (locator unverified). Fixes a **single, sample-independent** reconstruction map
`ρ : Finset (α × Bool) → (Fin t → Fin s → Fin (t * s)) → α → Bool` using the fixed finite
side-information alphabet `Fin t → Fin s → Fin (t * s)` of cardinality `(t * s) ^ (t * s)`
(`O(d* d log (d* d))` bits). For every realizable sample `S : LabeledSample α Bool m` (any `m : ℕ`),
there exist an **unordered subset** `T : Finset (α × Bool)` of examples drawn from `S` with
`T.card ≤ t * s` and side information `info : Fin t → Fin s → Fin (t * s)` such that `ρ T info`
correctly labels every example of `S`. -/
theorem exists_finset_compression_of_dualVCDim {C : ConceptClass α Bool} {d dStar : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d)
    (hdual : ∀ F : Finset ↥C, SetShatters (dualClass C) ↑F → F.card ≤ dStar)
    {s t : ℕ} {A : Learner α Bool s} (hA : IsConsistent A C)
    (hs : vcSampleSize d (1 / 3) (1 / 2) ≤ s)
    (ht : uniformConvergenceSampleSize dStar (1 / 6) (1 / 2) ≤ t) :
    ∃ ρ : Finset (α × Bool) → (Fin t → Fin s → Fin (t * s)) → α → Bool,
      ∀ {m : ℕ} (S : LabeledSample α Bool m), Realizable C S →
        ∃ (T : Finset (α × Bool)) (info : Fin t → Fin s → Fin (t * s)),
          (∀ z ∈ T, ∃ i : Fin m, S i = z) ∧
          T.card ≤ t * s ∧
          ∀ i : Fin m, ρ T info (S i).1 = (S i).2 := by
  classical
  have hs_pos : 0 < s := Nat.cast_pos.1 ((vcSampleSize_one_third_half_pos d).trans_le hs)
  have ht_pos : 0 < t :=
    Nat.cast_pos.1 ((uniformConvergenceSampleSize_one_sixth_half_pos dStar).trans_le ht)
  refine ⟨finsetSideReconstruct A t, fun {m} S hS => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨∅, fun _ _ => ⟨0, Nat.mul_pos ht_pos hs_pos⟩,
      fun _ hz => (Finset.notMem_empty _ hz).elim, Nat.zero_le _, fun i => i.elim0⟩
  · obtain ⟨B, hB⟩ := exists_majority_subsamples_of_dualVCDim hC hdual hA hs ht hm hS
    let T : Finset (α × Bool) :=
      Finset.univ.biUnion fun j : Fin t => Finset.univ.image (S ∘ B j)
    have hmem (j : Fin t) (u : Fin s) : S (B j u) ∈ T :=
      Finset.mem_biUnion.2
        ⟨j, Finset.mem_univ _, Finset.mem_image_of_mem _ (Finset.mem_univ u)⟩
    have hT_sub : ∀ z ∈ T, ∃ i : Fin m, S i = z := by
      intro z hz
      obtain ⟨j, -, hu⟩ := Finset.mem_biUnion.1 hz
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hu
      exact ⟨B j u, rfl⟩
    have hT_card : T.card ≤ t * s := Finset.card_biUnion_le.trans <|
      (Finset.sum_le_sum fun _ _ => Finset.card_image_le).trans_eq (by simp)
    have hT_pos : 0 < T.card :=
      Finset.card_pos.2 ⟨S (B ⟨0, ht_pos⟩ ⟨0, hs_pos⟩), hmem _ _⟩
    let e : T ≃ Fin T.card := Fintype.equivFinOfCardEq (Fintype.card_coe T)
    let info : Fin t → Fin s → Fin (t * s) := fun j u =>
      ⟨(e ⟨S (B j u), hmem j u⟩).1, lt_of_lt_of_le (e ⟨S (B j u), hmem j u⟩).2 hT_card⟩
    refine ⟨T, info, hT_sub, hT_card, fun i => ?_⟩
    have hsub : ∀ j : Fin t,
        (fun u : Fin s => (e.symm ⟨(info j u).1 % T.card, Nat.mod_lt _ hT_pos⟩).1) =
          S ∘ B j := fun j => funext fun u => by
      have hfin : (⟨(info j u).1 % T.card, Nat.mod_lt _ hT_pos⟩ : Fin T.card) =
          e ⟨S (B j u), hmem j u⟩ := Fin.ext (Nat.mod_eq_of_lt (e ⟨S (B j u), hmem j u⟩).2)
      rw [hfin, Equiv.symm_apply_apply]
      rfl
    have heval : finsetSideReconstruct A t T info (S i).1 =
        decide (t < 2 * (Finset.univ.filter fun j : Fin t =>
          A (S ∘ B j) (S i).1 = true).card) := by
      unfold finsetSideReconstruct
      rw [dite_eq_left_of_eq_true (eq_true hT_pos)]
      refine congrArg (fun n => decide (t < 2 * n)) (congrArg Finset.card ?_)
      exact Finset.filter_congr fun j _ => by dsimp only; rw [hsub j]
    rw [heval]
    exact decide_majority_eq_label _ (S i).2 (hB i)

/-! ### The Moran–Yehudayoff sample compression scheme -/

/-- **Moran–Yehudayoff sample compression scheme parameterized by `(d, d*)`**
[MoranYehudayoff2016, Theorem 1.4] (locator unverified). Every binary concept class on an arbitrary
domain `α` with VC bound `d` and dual VC bound `dStar` admits an ordered `SampleCompressionScheme`
of size `moranYehudayoffCompressionSize d dStar ≤ (5184 * dStar + 1440) * (120 * d + 60)`. No
countability or measurability assumption on `α` is needed. -/
noncomputable def moranYehudayoffScheme {C : ConceptClass α Bool} {d dStar : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d)
    (hdual : ∀ F : Finset ↥C, SetShatters (dualClass C) ↑F → F.card ≤ dStar) :
    SampleCompressionScheme C (moranYehudayoffCompressionSize d dStar) :=
  let A := canonicalConsistentLearner C (moranYehudayoffSubsampleSize d)
  have hA : IsConsistent A C :=
    isConsistent_canonicalConsistentLearner C (moranYehudayoffSubsampleSize d)
  have hs : vcSampleSize d (1 / 3) (1 / 2) ≤ (moranYehudayoffSubsampleSize d : ℝ) :=
    Nat.le_ceil _
  have ht : uniformConvergenceSampleSize dStar (1 / 6) (1 / 2) ≤
      (moranYehudayoffMajoritySize dStar : ℝ) := Nat.le_ceil _
  { compress := fun {m} S =>
      letI := Classical.propDecidable
      if h : 0 < m ∧ Realizable C S then
        flattenSubsamples (Classical.choose
          (exists_majority_subsamples_of_dualVCDim hC hdual hA hs ht h.1 h.2))
      else
        []
    reconstruct := majorityReconstruct A (moranYehudayoffMajoritySize dStar)
    length_compress_le := fun {m} S hS => by
      by_cases h : 0 < m ∧ Realizable C S
      · rw [dite_eq_left_of_eq_true (eq_true h), length_flattenSubsamples]
        exact le_rfl
      · rw [dite_eq_right_of_eq_false (eq_false h), List.length_nil]
        exact Nat.zero_le _
    reconstruct_correct := fun {m} S hS i => by
      have hcond : 0 < m ∧ Realizable C S := ⟨Fin.pos i, hS⟩
      rw [dite_eq_left_of_eq_true (eq_true hcond),
        majorityReconstruct_map_flattenSubsamples]
      have hB := Classical.choose_spec
        (exists_majority_subsamples_of_dualVCDim hC hdual hA hs ht hcond.1 hcond.2) i
      exact decide_majority_eq_label _ (S i).2 hB }

/-- **Moran–Yehudayoff sample compression scheme parameterized by VC dimension `d`**
[MoranYehudayoff2016, Theorem 1.3] (locator unverified). Combines `moranYehudayoffScheme` with
Assouad's dual VC bound `card_le_of_setShatters_dualClass` (`d* ≤ 2 ^ (d + 1) - 1`), giving size
`moranYehudayoffVCCompressionSize d ≤ (5184 * 2 ^ (d + 1) + 1440) * (120 * d + 60)`. -/
noncomputable def moranYehudayoffSchemeOfVCDim {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) :
    SampleCompressionScheme C (moranYehudayoffVCCompressionSize d) :=
  moranYehudayoffScheme hC fun _ hF => card_le_of_setShatters_dualClass hC hF

/-- **Every binary class of finite VC dimension admits a finite sample compression scheme**
[MoranYehudayoff2016, Theorem 1.3] (locator unverified), of explicit size
`moranYehudayoffVCCompressionSize (vcDim C)`. -/
theorem exists_sampleCompressionScheme_of_hasFiniteVCDim {C : ConceptClass α Bool}
    (hC : HasFiniteVCDim C) :
    Nonempty (SampleCompressionScheme C (moranYehudayoffVCCompressionSize (vcDim C))) :=
  ⟨moranYehudayoffSchemeOfVCDim fun _ hW => hW.card_le_vcDim hC⟩

/-- **Complete characterization of compressibility by finite VC dimension**
[LittlestoneWarmuth1986; MoranYehudayoff2016, Theorem 1.3] (locators unverified). On **any**
domain type `α` (no countability or measurability assumption), a binary concept class admits a
sample compression scheme of finite size iff it has finite VC dimension. -/
theorem exists_sampleCompressionScheme_iff_hasFiniteVCDim (C : ConceptClass α Bool) :
    (∃ k : ℕ, Nonempty (SampleCompressionScheme C k)) ↔ HasFiniteVCDim C :=
  ⟨fun ⟨_, ⟨κ⟩⟩ => κ.hasFiniteVCDim,
    fun hC => ⟨_, exists_sampleCompressionScheme_of_hasFiniteVCDim hC⟩⟩

end MajorityVote

/-! ### Seven-way Fundamental Theorem of Statistical Learning -/

/-- **Seven-way fundamental theorem of statistical learning**: on a countable domain with
measurable singletons, finite-size sample compressibility joins the six equivalent conditions of
[ShalevShwartzBenDavid2014, Theorem 6.7] (`tfae_hasFiniteVCDim`). -/
theorem tfae_hasFiniteVCDim_compression {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] {C : ConceptClass α Bool} :
    List.TFAE
      [HasUniformConvergence C Set.univ,
       IsERMLearnable C Set.univ,
       IsPACLearnable C Set.univ,
       IsPACLearnable C (realizableDistributions C),
       IsERMLearnable C (realizableDistributions C),
       HasFiniteVCDim C,
       ∃ k : ℕ, Nonempty (SampleCompressionScheme C k)] := by
  tfae_have 1 ↔ 2 := (tfae_hasFiniteVCDim (C := C)).out 1 2
  tfae_have 2 ↔ 3 := (tfae_hasFiniteVCDim (C := C)).out 2 3
  tfae_have 3 ↔ 4 := (tfae_hasFiniteVCDim (C := C)).out 3 4
  tfae_have 4 ↔ 5 := (tfae_hasFiniteVCDim (C := C)).out 4 5
  tfae_have 5 ↔ 6 := (tfae_hasFiniteVCDim (C := C)).out 5 6
  tfae_have 6 ↔ 7 := (exists_sampleCompressionScheme_iff_hasFiniteVCDim C).symm
  tfae_finish

end Cslib.MachineLearning.PACLearning
