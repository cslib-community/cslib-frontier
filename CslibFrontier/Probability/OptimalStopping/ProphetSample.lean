/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.IID
public import CslibFrontier.Probability.OptimalStopping.Prophet
public import Mathlib.GroupTheory.Perm.Basic
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Prod.Lex.Basic

/-!
# The single-sample prophet inequality

When the laws `μ₀, …, μₙ₋₁` of `n` independent nonnegative values are unknown to the gambler,
a single offline sample `sᵢ ~ μᵢ` from each law suffices to recover the optimal `1/2` prophet
guarantee: set the threshold to the maximum of the `n` samples and accept the first online value
that beats it ([RubinsteinWangWeinberg2020], Definition 1 and Theorem 1, §1–§3, pp. 1–4; the
order-oblivious case dates to Azar, Kleinberg and Weinberg, 2014).

When the laws have atoms, ties between online values and the sample maximum must be broken
randomly: if `X₀ = 1` deterministically (`PMF.pure 1`), then `S₀ = 1` as well, so accepting only
values strictly above `maxⱼ Sⱼ` collects `0` (`expectedReward_strictSampleRule_pure_eq_zero`),
whereas accepting all values at least `maxⱼ Sⱼ` fails on `tightLaws k` in the same way as a naive
greedy rule. Following [RubinsteinWangWeinberg2020], §2 ("Continuous vs. Discrete Distributions",
p. 2), the gambler draws a uniform permutation `π : Equiv.Perm (Fin (2 * n))` of the `2n` sample
and online slots and compares pairs `(value, rank)` lexicographically:

* Sample `j` receives rank `π (2j)`, online step `i` receives rank `π (2i + 1)`.
* `singleSampleRule s π : List ℝ≥0 → Bool` is an online stopping rule in the sense of
  `Cslib.Probability.OptimalStopping.payoff`: at step `i` (`past.length = i`) it stops iff
  `(x, π (2i + 1))` exceeds `(s j, π (2j))` lexicographically for all `j`. Strictly larger values
  always beat the sample maximum and strictly smaller ones never do; `π` only breaks exact ties.

The proof uses the deferred-decisions coupling of [RubinsteinWangWeinberg2020], §3 (Observation 3,
Propositions 4 and 5, and Proof of Theorem 1, pp. 3–4), turned into an explicit 2-to-1 injection on
the `2ⁿ` fair-coin assignments `c : Fin n → Bool` so that all expectations remain in `ℝ≥0∞` with no
integrability hypothesis (`E[max]` may be `⊤`). Because `μ : Fin n → PMF ℝ≥0` is arbitrary, the
same `1/2` bound holds under any arrival permutation `σ : Equiv.Perm (Fin n)`
(`expectedMax_le_two_mul_singleSampleExpectedReward_perm`).

## Main definitions

* `Cslib.Probability.OptimalStopping.Prophet.singleSampleRule`: the online stopping rule induced by
  a sample vector `s` and tie-breaking permutation `π`.
* `Cslib.Probability.OptimalStopping.Prophet.singleSampleExpectedReward`: expected reward of the
  single-sample algorithm over `s ~ piFin μ`, `π ~ uniformOfFintype (Equiv.Perm (Fin (2 * n)))`,
  and online arrivals `x ~ jointLaw (List.ofFn μ)`.
* `Cslib.Probability.OptimalStopping.Prophet.strictSampleRule`,
  `Cslib.Probability.OptimalStopping.Prophet.strictSampleExpectedReward`: the deterministic rule
  accepting the first online value strictly above `maxⱼ sⱼ`.

## Main results

* `Cslib.Probability.OptimalStopping.Prophet.expectedMax_le_two_mul_singleSampleExpectedReward`:
  **the single-sample prophet inequality** (`E[max] ≤ 2 · E[ALG]`).
* `expectedMax_le_two_mul_singleSampleExpectedReward_perm`:
  invariance under arbitrary arrival permutations.
* `Cslib.Probability.OptimalStopping.Prophet.expectedReward_strictSampleRule_pure_eq_zero`:
  without randomized tie-breaking, strict comparison against the sample maximum collects `0` on
  point-mass distributions.

## References

* [A. Rubinstein, J. Z. Wang, S. M. Weinberg, *Optimal single-choice prophet inequalities from
  samples*][RubinsteinWangWeinberg2020], Definition 1, Observation 3, Propositions 4–5, Theorem 1
-/

public section

namespace Cslib.Probability.OptimalStopping.Prophet

open Cslib.Probability.PMF
open scoped ENNReal NNReal

/-- Slot `2 * i` in `Fin (2 * n)`, assigned to offline sample `i`. -/
def sampleSlot {n : ℕ} (i : Fin n) : Fin (2 * n) :=
  ⟨2 * i.val, by have := i.isLt; omega⟩

/-- Slot `2 * i + 1` in `Fin (2 * n)`, assigned to online observation `i`. -/
def onlineSlot {n : ℕ} (i : Fin n) : Fin (2 * n) :=
  ⟨2 * i.val + 1, by have := i.isLt; omega⟩

/-- A value in `ℝ≥0` paired lexicographically with its tie-breaking rank in `Fin (2 * n)`. -/
abbrev TaggedValue (n : ℕ) : Type := ℝ≥0 ×ₗ Fin (2 * n)

/-- Tag sample `j` with its rank under `π`. -/
@[expose] def sampleTag {n : ℕ} (s : Fin n → ℝ≥0) (π : Equiv.Perm (Fin (2 * n))) (j : Fin n) :
    TaggedValue n :=
  toLex (s j, π (sampleSlot j))

/-- Tag an online value `x` at step `i` with its rank under `π`. -/
@[expose] def onlineTag {n : ℕ} (x : ℝ≥0) (π : Equiv.Perm (Fin (2 * n))) (i : Fin n) :
    TaggedValue n :=
  toLex (x, π (onlineSlot i))

/-- **The single-sample stopping rule** ([RubinsteinWangWeinberg2020], §2, p. 2): given offline
samples `s : Fin n → ℝ≥0` and a tie-breaking permutation `π : Equiv.Perm (Fin (2 * n))`, stop at
step `i` (`past.length = i`) iff `(x, π (2i + 1))` exceeds every tagged sample `(s j, π (2j))` in
lexicographic order. -/
noncomputable def singleSampleRule {n : ℕ} (s : Fin n → ℝ≥0)
    (π : Equiv.Perm (Fin (2 * n))) : List ℝ≥0 → Bool
  | [] => false
  | x :: past =>
      if hk : past.length < n then
        decide (∀ j : Fin n, sampleTag s π j < onlineTag x π ⟨past.length, hk⟩)
      else
        false

/-- Expected reward of the single-sample stopping algorithm on `n` independent distributions `μ`:
draw one sample vector `s ~ piFin μ`, an independent uniform permutation `π`, and run
`singleSampleRule s π` online on `jointLaw (List.ofFn μ)`. -/
noncomputable def singleSampleExpectedReward {n : ℕ} (μ : Fin n → PMF ℝ≥0) : ℝ≥0∞ :=
  ∑' s, piFin μ s *
    ∑' π, uniformOfFintype (Equiv.Perm (Fin (2 * n))) π *
      expectedReward (singleSampleRule s π) (List.ofFn μ)

/-- Unfolding equation for `singleSampleExpectedReward`. -/
theorem singleSampleExpectedReward_eq {n : ℕ} (μ : Fin n → PMF ℝ≥0) :
    singleSampleExpectedReward μ =
      ∑' s, piFin μ s *
        ∑' π, uniformOfFintype (Equiv.Perm (Fin (2 * n))) π *
          expectedReward (singleSampleRule s π) (List.ofFn μ) := by
  unfold singleSampleExpectedReward
  rfl

/-- Deterministic strict-maximum rule: accept the first online value strictly exceeding every
offline sample `s j` (and positive when `n = 0`). -/
noncomputable def strictSampleRule {n : ℕ} (s : Fin n → ℝ≥0) : List ℝ≥0 → Bool :=
  acceptRule fun x => decide ((∀ j : Fin n, s j < x) ∧ (n = 0 → 0 < x))

/-- Expected reward of the deterministic strict-maximum rule over `s ~ piFin μ`. -/
noncomputable def strictSampleExpectedReward {n : ℕ} (μ : Fin n → PMF ℝ≥0) : ℝ≥0∞ :=
  ∑' s, piFin μ s * expectedReward (strictSampleRule s) (List.ofFn μ)

/-! ### Relationship between `piFin` and `jointLaw` -/

/-- Pushing `piFin μ` along `List.ofFn` gives `jointLaw (List.ofFn μ)`. -/
theorem piFin_map_ofFn {α : Type*} :
    ∀ {n : ℕ} (μ : Fin n → PMF α), (piFin μ).map List.ofFn = jointLaw (List.ofFn μ)
  | 0, _ => by simp [piFin]
  | n + 1, μ => by
      rw [piFin, List.ofFn_succ, jointLaw_cons, PMF.map_bind]
      congr 1 with a : 1
      rw [← piFin_map_ofFn (fun j => μ j.succ), _root_.PMF.map_comp, _root_.PMF.map_comp]
      congr 1; funext v; simp

/-- Expectations under `jointLaw (List.ofFn μ)` rewrite as expectations under `piFin μ`. -/
theorem tsum_jointLaw_ofFn_mul {α : Type*} {n : ℕ} (μ : Fin n → PMF α) (f : List α → ℝ≥0∞) :
    ∑' xs, jointLaw (List.ofFn μ) xs * f xs = ∑' x, piFin μ x * f (List.ofFn x) := by
  rw [← piFin_map_ofFn μ, tsum_map_mul]

private theorem listMax_ofFn_eq_sup' {n : ℕ} [NeZero n] (x : Fin n → ℝ≥0) :
    listMax (List.ofFn x) = Finset.univ.sup' Finset.univ_nonempty x :=
  le_antisymm
    ((listMax_le_iff _ _).mpr fun _ hv => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv; exact Finset.le_sup' x (Finset.mem_univ i))
    (Finset.sup'_le _ _ fun i _ =>
      (listMax_le_iff _ _).mp le_rfl (x i) (List.mem_ofFn.mpr ⟨i, rfl⟩))

/-! ### Online execution on a tuple -/

/-- The reward collected by scanning `i = 0, …, n - 1` and taking the first `x i` whose tag beats
every sample tag. -/
@[expose] noncomputable def firstBeatReward {n : ℕ} (x s : Fin n → ℝ≥0)
    (π : Equiv.Perm (Fin (2 * n))) : ℝ≥0∞ :=
  let W := Finset.univ.filter fun i : Fin n => ∀ j : Fin n, sampleTag s π j < onlineTag (x i) π i
  if hW : W.Nonempty then (x (W.min' hW) : ℝ≥0∞) else 0

private theorem payoff_singleSampleRule_aux {n : ℕ} (x s : Fin n → ℝ≥0)
    (π : Equiv.Perm (Fin (2 * n))) :
    ∀ (k : ℕ) (past : List ℝ≥0), past.length = k → k ≤ n →
      payoff (singleSampleRule s π) reward past ((List.ofFn x).drop k) =
        let W := Finset.univ.filter fun i : Fin n =>
          k ≤ i.val ∧ ∀ j : Fin n, sampleTag s π j < onlineTag (x i) π i
        if hW : W.Nonempty then (x (W.min' hW) : ℝ≥0∞) else 0 := by
  intro k
  induction hrem : n - k generalizing k with
  | zero =>
      intro past _ hkn
      obtain rfl : k = n := by omega
      have hdrop : (List.ofFn x).drop k = [] := by simp
      have hempty : (Finset.univ.filter fun i : Fin k =>
          k ≤ i.val ∧ ∀ j : Fin k, sampleTag s π j < onlineTag (x i) π i) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun i _ h => by have := i.isLt; omega
      simp [hdrop, payoff_nil, hempty]
  | succ m ih =>
      intro past hpast hkn
      have hlt : k < n := by omega
      have hdrop : (List.ofFn x).drop k = x ⟨k, hlt⟩ :: (List.ofFn x).drop (k + 1) := by
        rw [← List.cons_getElem_drop_succ (h := by simp [hlt])]; simp
      rw [hdrop, payoff_cons]
      have hrule : singleSampleRule s π (x ⟨k, hlt⟩ :: past) =
          decide (∀ j : Fin n, sampleTag s π j < onlineTag (x ⟨k, hlt⟩) π ⟨k, hlt⟩) := by
        simp [singleSampleRule, hpast, hlt]
      rw [hrule]
      set Wk := Finset.univ.filter fun i : Fin n =>
        k ≤ i.val ∧ ∀ j : Fin n, sampleTag s π j < onlineTag (x i) π i
      set Wk1 := Finset.univ.filter fun i : Fin n =>
        k + 1 ≤ i.val ∧ ∀ j : Fin n, sampleTag s π j < onlineTag (x i) π i
      by_cases hbeat : ∀ j : Fin n, sampleTag s π j < onlineTag (x ⟨k, hlt⟩) π ⟨k, hlt⟩
      · have hmem : (⟨k, hlt⟩ : Fin n) ∈ Wk := by simp [Wk, hbeat]
        have hne : Wk.Nonempty := ⟨⟨k, hlt⟩, hmem⟩
        have hmin : Wk.min' hne = ⟨k, hlt⟩ := le_antisymm (Finset.min'_le Wk _ hmem)
          (Fin.le_def.mpr (Finset.mem_filter.mp (Finset.min'_mem Wk hne)).2.1)
        simp [hbeat, reward, hne, hmin]
      · simp only [decide_eq_false hbeat, Bool.false_eq_true, ↓reduceIte]
        rw [ih (k + 1) (by omega) (x ⟨k, hlt⟩ :: past) (by simp [hpast]) (by omega)]
        have hW_eq : Wk = Wk1 := by
          ext i
          simp only [Wk, Wk1, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨fun ⟨hik, hi⟩ => ⟨?_, hi⟩, fun ⟨hik1, hi⟩ => ⟨by omega, hi⟩⟩
          rcases eq_or_lt_of_le hik with heq | hgt
          · have hi' : i = ⟨k, hlt⟩ := Fin.ext heq.symm
            exact absurd (hi' ▸ hi) hbeat
          · omega
        rw [hW_eq]

/-- On `List.ofFn x`, `singleSampleRule s π` collects `firstBeatReward x s π`. -/
theorem payoff_singleSampleRule_ofFn {n : ℕ} (x s : Fin n → ℝ≥0)
    (π : Equiv.Perm (Fin (2 * n))) :
    payoff (singleSampleRule s π) reward [] (List.ofFn x) = firstBeatReward x s π := by
  simpa [firstBeatReward] using payoff_singleSampleRule_aux x s π 0 [] rfl (Nat.zero_le n)

/-! ### Combinatorial 2-to-1 coin pairing (Observation 3, Propositions 4–5, Theorem 1) -/

section CoinPairing

variable {n : ℕ}

private def tagVal (t : TaggedValue n) : ℝ≥0∞ := ((ofLex t).1 : ℝ≥0∞)

private theorem tagVal_mono {t₁ t₂ : TaggedValue n} (h : t₁ ≤ t₂) : tagVal t₁ ≤ tagVal t₂ :=
  ENNReal.coe_le_coe.mpr (Prod.Lex.monotone_fst t₁ t₂ h)

/-- Given strictly ordered candidate pairs `Z i < Y i` at each coordinate and coin flips `c`,
the online tagged values `X_c` and sample tagged values `S_c`. -/
private def onlineChoice (Y Z : Fin n → TaggedValue n) (c : Fin n → Bool) (i : Fin n) :
    TaggedValue n :=
  if c i then Y i else Z i

private def sampleChoice (Y Z : Fin n → TaggedValue n) (c : Fin n → Bool) (i : Fin n) :
    TaggedValue n :=
  if c i then Z i else Y i

/-- Unique `Y`-maximizer on a nonempty `Finset` when `Y` is injective. -/
private noncomputable def argmaxY (Y : Fin n → TaggedValue n) (S : Finset (Fin n))
    (hS : S.Nonempty) : Fin n :=
  (S.exists_max_image Y hS).choose

private theorem argmaxY_mem {Y : Fin n → TaggedValue n} {S : Finset (Fin n)} (hS : S.Nonempty) :
    argmaxY Y S hS ∈ S :=
  (S.exists_max_image Y hS).choose_spec.1

private theorem le_argmaxY {Y : Fin n → TaggedValue n} {S : Finset (Fin n)} (hS : S.Nonempty)
    {j : Fin n} (hj : j ∈ S) : Y j ≤ Y (argmaxY Y S hS) :=
  (S.exists_max_image Y hS).choose_spec.2 j hj

private theorem argmaxY_eq_of_isMax {Y : Fin n → TaggedValue n} (hY : Function.Injective Y)
    {S : Finset (Fin n)} (hS : S.Nonempty) {m : Fin n} (hm : m ∈ S)
    (hmax : ∀ j ∈ S, Y j ≤ Y m) : argmaxY Y S hS = m :=
  hY (le_antisymm (hmax _ (argmaxY_mem hS)) (le_argmaxY hS hm))

/-- Unique `Y`-minimizer on a nonempty `Finset` when `Y` is injective. -/
private noncomputable def argminY (Y : Fin n → TaggedValue n) (S : Finset (Fin n))
    (hS : S.Nonempty) : Fin n :=
  (S.exists_min_image Y hS).choose

private theorem argminY_mem {Y : Fin n → TaggedValue n} {S : Finset (Fin n)} (hS : S.Nonempty) :
    argminY Y S hS ∈ S :=
  (S.exists_min_image Y hS).choose_spec.1

private theorem argminY_le {Y : Fin n → TaggedValue n} {S : Finset (Fin n)} (hS : S.Nonempty)
    {j : Fin n} (hj : j ∈ S) : Y (argminY Y S hS) ≤ Y j :=
  (S.exists_min_image Y hS).choose_spec.2 j hj

private theorem argminY_eq_of_isMin {Y : Fin n → TaggedValue n} (hY : Function.Injective Y)
    {S : Finset (Fin n)} (hS : S.Nonempty) {m : Fin n} (hm : m ∈ S)
    (hmin : ∀ j ∈ S, Y m ≤ Y j) : argminY Y S hS = m :=
  hY (le_antisymm (argminY_le hS hm) (hmin _ (argminY_mem hS)))

variable [NeZero n]

private noncomputable def prophetCoinVal (Y Z : Fin n → TaggedValue n) (c : Fin n → Bool) :
    ℝ≥0∞ :=
  tagVal (Finset.univ.sup' Finset.univ_nonempty (onlineChoice Y Z c))

private noncomputable def coinWinSet (Y Z : Fin n → TaggedValue n) (c : Fin n → Bool) :
    Finset (Fin n) :=
  Finset.univ.filter fun i : Fin n =>
    Finset.univ.sup' Finset.univ_nonempty (sampleChoice Y Z c) < onlineChoice Y Z c i

private noncomputable def gamblerCoinVal (Y Z : Fin n → TaggedValue n) (c : Fin n → Bool) :
    ℝ≥0∞ :=
  let W := coinWinSet Y Z c
  if hW : W.Nonempty then tagVal (onlineChoice Y Z c (W.min' hW)) else 0

private theorem gamblerCoinVal_eq_of_nonempty {Y Z : Fin n → TaggedValue n} {c : Fin n → Bool}
    (hW : (coinWinSet Y Z c).Nonempty) :
    gamblerCoinVal Y Z c = tagVal (onlineChoice Y Z c ((coinWinSet Y Z c).min' hW)) := by
  simp only [gamblerCoinVal, hW, ↓reduceDIte]

private noncomputable def candSet (Y Z : Fin n → TaggedValue n) : Finset (Fin n) :=
  Finset.univ.filter fun i : Fin n => Finset.univ.sup' Finset.univ_nonempty Z < Y i

private noncomputable def activeSet (Y Z : Fin n → TaggedValue n) (c : Fin n → Bool) :
    Finset (Fin n) :=
  (candSet Y Z).filter fun i => c i = true

private noncomputable def lowerSet (Y Z : Fin n → TaggedValue n) (m : Fin n) : Finset (Fin n) :=
  (candSet Y Z).filter fun j => Y j < Y m

private noncomputable def sub2Config (Y Z : Fin n → TaggedValue n) (m m' : Fin n)
    (c : Fin n → Bool) (i : Fin n) : Bool :=
  if i ∈ candSet Y Z ∧ Y m ≤ Y i then true else if i = m' then false else c i

private noncomputable def allTrueConfig (Y Z : Fin n → TaggedValue n) (c : Fin n → Bool)
    (i : Fin n) : Bool :=
  if i ∈ candSet Y Z then true else c i

/-- The 2-to-1 map from prophet coin configurations `c` to `(gamblerConfig, bit)` (with no `let`
bindings, so `simp only` splits its `dite` branches directly). -/
private noncomputable def coinPairMap (Y Z : Fin n → TaggedValue n) (c : Fin n → Bool) :
    (Fin n → Bool) × Bool :=
  if hA : (activeSet Y Z c).Nonempty then
    if hL : (lowerSet Y Z (argmaxY Y (activeSet Y Z c) hA)).Nonempty then
      (sub2Config Y Z (argmaxY Y (activeSet Y Z c) hA)
        (argmaxY Y (lowerSet Y Z (argmaxY Y (activeSet Y Z c) hA)) hL) c,
        c (argmaxY Y (lowerSet Y Z (argmaxY Y (activeSet Y Z c) hA)) hL))
    else
      (allTrueConfig Y Z c, true)
  else
    (allTrueConfig Y Z c, false)

private theorem filter_allTrueConfig_false (Y Z : Fin n → TaggedValue n) (c : Fin n → Bool) :
    (candSet Y Z).filter (fun j => allTrueConfig Y Z c j = false) = ∅ := by
  ext j
  simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
  intro hjK
  simp [allTrueConfig, hjK]

private theorem sub2Config_false_max {Y Z : Fin n → TaggedValue n} (c : Fin n → Bool)
    {m m' : Fin n} (hm'L : m' ∈ lowerSet Y Z m)
    (hm'max : ∀ j ∈ lowerSet Y Z m, Y j ≤ Y m') :
    m' ∈ (candSet Y Z).filter (fun j => sub2Config Y Z m m' c j = false) ∧
      ∀ j ∈ (candSet Y Z).filter (fun j => sub2Config Y Z m m' c j = false), Y j ≤ Y m' := by
  have hm'K : m' ∈ candSet Y Z := (Finset.mem_filter.mp hm'L).1
  have hm'lt : Y m' < Y m := (Finset.mem_filter.mp hm'L).2
  refine ⟨Finset.mem_filter.mpr ⟨hm'K, ?_⟩, fun j hj => ?_⟩
  · simp [sub2Config, hm'K, not_le.mpr hm'lt]
  · obtain ⟨hjK, hjf⟩ := Finset.mem_filter.mp hj
    have hjlt : Y j < Y m := by
      by_contra hge
      have hge' : Y m ≤ Y j := not_lt.mp hge
      simp [sub2Config, hjK, hge'] at hjf
    exact hm'max j (Finset.mem_filter.mpr ⟨hjK, hjlt⟩)

private theorem sub2Config_ne_allTrueConfig {Y Z : Fin n → TaggedValue n}
    (c₁ c₂ : Fin n → Bool) {m m' : Fin n} (hm'L : m' ∈ lowerSet Y Z m)
    (hm'max : ∀ j ∈ lowerSet Y Z m, Y j ≤ Y m') :
    sub2Config Y Z m m' c₁ ≠ allTrueConfig Y Z c₂ := by
  intro heq
  have hcon := (sub2Config_false_max c₁ hm'L hm'max).1
  rw [heq, filter_allTrueConfig_false] at hcon
  exact Finset.notMem_empty _ hcon

private theorem eq_of_argmaxY_activeSet {Y Z : Fin n → TaggedValue n} (hY : Function.Injective Y)
    {c₁ c₂ : Fin n → Bool} {hA₁ : (activeSet Y Z c₁).Nonempty}
    {hA₂ : (activeSet Y Z c₂).Nonempty}
    (hm : argmaxY Y (activeSet Y Z c₁) hA₁ = argmaxY Y (activeSet Y Z c₂) hA₂)
    {i : Fin n} (hiK : i ∈ candSet Y Z) (hle : Y (argmaxY Y (activeSet Y Z c₁) hA₁) ≤ Y i) :
    c₁ i = c₂ i := by
  set m₁ := argmaxY Y (activeSet Y Z c₁) hA₁
  set m₂ := argmaxY Y (activeSet Y Z c₂) hA₂
  rcases eq_or_lt_of_le hle with hy | hylt
  · obtain rfl : i = m₁ := hY hy.symm
    have h1 : c₁ m₁ = true := (Finset.mem_filter.mp (argmaxY_mem hA₁)).2
    have h2 : c₂ m₁ = true := hm ▸ (Finset.mem_filter.mp (argmaxY_mem hA₂)).2
    exact h1.trans h2.symm
  · have hfalse : ∀ {c : Fin n → Bool} (hA : (activeSet Y Z c).Nonempty),
        argmaxY Y (activeSet Y Z c) hA = m₁ → c i = false := fun hA heq => by
      by_contra htrue
      exact not_le.mpr hylt
        (heq ▸ le_argmaxY hA (Finset.mem_filter.mpr ⟨hiK, Bool.eq_true_of_not_eq_false htrue⟩))
    exact (hfalse hA₁ rfl).trans (hfalse hA₂ hm.symm).symm

private theorem coinPairMap_injective {Y Z : Fin n → TaggedValue n} (hY : Function.Injective Y) :
    Function.Injective (coinPairMap Y Z) := by
  intro c₁ c₂ heq
  have hfst : (coinPairMap Y Z c₁).1 = (coinPairMap Y Z c₂).1 := congrArg Prod.fst heq
  have hsnd : (coinPairMap Y Z c₁).2 = (coinPairMap Y Z c₂).2 := congrArg Prod.snd heq
  unfold coinPairMap at hfst hsnd
  by_cases hA₁ : (activeSet Y Z c₁).Nonempty <;> simp only [hA₁, ↓reduceDIte] at hfst hsnd
  · let m₁ := argmaxY Y (activeSet Y Z c₁) hA₁
    by_cases hL₁ : (lowerSet Y Z m₁).Nonempty <;> simp only [m₁, hL₁, ↓reduceDIte] at hfst hsnd
    · let m'₁ := argmaxY Y (lowerSet Y Z m₁) hL₁
      have hb₁ := sub2Config_false_max c₁ (argmaxY_mem hL₁) (fun j hj => le_argmaxY hL₁ hj)
      by_cases hA₂ : (activeSet Y Z c₂).Nonempty <;> simp only [hA₂, ↓reduceDIte] at hfst hsnd
      · let m₂ := argmaxY Y (activeSet Y Z c₂) hA₂
        by_cases hL₂ : (lowerSet Y Z m₂).Nonempty <;> simp only [m₂, hL₂, ↓reduceDIte] at hfst hsnd
        · let m'₂ := argmaxY Y (lowerSet Y Z m₂) hL₂
          have hfst' : sub2Config Y Z m₁ m'₁ c₁ = sub2Config Y Z m₂ m'₂ c₂ := hfst
          have hsnd' : c₁ m'₁ = c₂ m'₂ := hsnd
          have hb₂ := sub2Config_false_max c₂ (argmaxY_mem hL₂) (fun j hj => le_argmaxY hL₂ hj)
          set B := (candSet Y Z).filter fun j => sub2Config Y Z m₁ m'₁ c₁ j = false
          have hB_eq :
              ((candSet Y Z).filter fun j => sub2Config Y Z m₂ m'₂ c₂ j = false) = B := by
            rw [← hfst']
          have hBne : B.Nonempty := ⟨m'₁, hb₁.1⟩
          have hm'eq : m'₁ = m'₂ :=
            (argmaxY_eq_of_isMax hY hBne hb₁.1 hb₁.2).symm.trans
              (argmaxY_eq_of_isMax hY hBne (hB_eq ▸ hb₂.1) fun j hj => hb₂.2 j (hB_eq.symm ▸ hj))
          set U := (candSet Y Z).filter fun j => Y m'₁ < Y j
          have hm₁U : m₁ ∈ U := Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp (argmaxY_mem hA₁)).1, (Finset.mem_filter.mp (argmaxY_mem hL₁)).2⟩
          have hm₂U : m₂ ∈ U := Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp (argmaxY_mem hA₂)).1,
              hm'eq ▸ (Finset.mem_filter.mp (argmaxY_mem hL₂)).2⟩
          have hmin : ∀ {m : Fin n} (hL : (lowerSet Y Z m).Nonempty),
              argmaxY Y (lowerSet Y Z m) hL = m'₁ → ∀ j ∈ U, Y m ≤ Y j := by
            intro m hL hmeq j hj
            obtain ⟨hjK, hjgt⟩ := Finset.mem_filter.mp hj
            by_contra hlt
            exact not_le.mpr hjgt
              (hmeq ▸ le_argmaxY hL (Finset.mem_filter.mpr ⟨hjK, not_le.mp hlt⟩))
          have hmeq : m₁ = m₂ :=
            (argminY_eq_of_isMin hY ⟨m₁, hm₁U⟩ hm₁U (hmin hL₁ rfl)).symm.trans
              (argminY_eq_of_isMin hY ⟨m₁, hm₁U⟩ hm₂U (hmin hL₂ hm'eq.symm))
          funext i
          by_cases hi1 : i ∈ candSet Y Z ∧ Y m₁ ≤ Y i
          · exact eq_of_argmaxY_activeSet hY hmeq hi1.1 hi1.2
          · by_cases hi2 : i = m'₁
            · subst hi2; exact hm'eq ▸ hsnd'
            · have hi1' : ¬ (i ∈ candSet Y Z ∧ Y m₂ ≤ Y i) := by rwa [← hmeq]
              have hi2' : i ≠ m'₂ := by rwa [← hm'eq]
              simpa only [sub2Config, hi1, hi1', hi2, hi2', ↓reduceIte] using congrFun hfst' i
        · exact absurd hfst
            (sub2Config_ne_allTrueConfig c₁ c₂ (argmaxY_mem hL₁) fun j hj => le_argmaxY hL₁ hj)
      · exact absurd hfst
          (sub2Config_ne_allTrueConfig c₁ c₂ (argmaxY_mem hL₁) fun j hj => le_argmaxY hL₁ hj)
    · by_cases hA₂ : (activeSet Y Z c₂).Nonempty <;> simp only [hA₂, ↓reduceDIte] at hfst hsnd
      · let m₂ := argmaxY Y (activeSet Y Z c₂) hA₂
        by_cases hL₂ : (lowerSet Y Z m₂).Nonempty <;> simp only [m₂, hL₂, ↓reduceDIte] at hfst hsnd
        · exact absurd hfst.symm
            (sub2Config_ne_allTrueConfig c₂ c₁ (argmaxY_mem hL₂) fun j hj => le_argmaxY hL₂ hj)
        · have hm₁K : m₁ ∈ candSet Y Z := (Finset.mem_filter.mp (argmaxY_mem hA₁)).1
          have hm₂K : m₂ ∈ candSet Y Z := (Finset.mem_filter.mp (argmaxY_mem hA₂)).1
          have hmin : ∀ {m : Fin n}, ¬(lowerSet Y Z m).Nonempty → ∀ j ∈ candSet Y Z, Y m ≤ Y j :=
            fun hL j hjK => by_contra fun hlt => hL ⟨j, Finset.mem_filter.mpr ⟨hjK, not_le.mp hlt⟩⟩
          have hmeq : m₁ = m₂ :=
            (argminY_eq_of_isMin hY ⟨m₁, hm₁K⟩ hm₁K (hmin hL₁)).symm.trans
              (argminY_eq_of_isMin hY ⟨m₁, hm₁K⟩ hm₂K (hmin hL₂))
          funext i
          by_cases hiK : i ∈ candSet Y Z
          · exact eq_of_argmaxY_activeSet hY hmeq hiK (hmin hL₁ i hiK)
          · simpa only [allTrueConfig, hiK, ↓reduceIte] using congrFun hfst i
      · exact Bool.noConfusion hsnd
  · by_cases hA₂ : (activeSet Y Z c₂).Nonempty <;> simp only [hA₂, ↓reduceDIte] at hfst hsnd
    · let m₂ := argmaxY Y (activeSet Y Z c₂) hA₂
      by_cases hL₂ : (lowerSet Y Z m₂).Nonempty <;> simp only [m₂, hL₂, ↓reduceDIte] at hfst hsnd
      · exact absurd hfst.symm
          (sub2Config_ne_allTrueConfig c₂ c₁ (argmaxY_mem hL₂) fun j hj => le_argmaxY hL₂ hj)
      · exact Bool.noConfusion hsnd
    · funext i
      by_cases hiK : i ∈ candSet Y Z
      · have hfalse : ∀ {c : Fin n → Bool}, ¬(activeSet Y Z c).Nonempty → c i = false :=
          fun hA => by_contra fun ht =>
            hA ⟨i, Finset.mem_filter.mpr ⟨hiK, Bool.eq_true_of_not_eq_false ht⟩⟩
        exact (hfalse hA₁).trans (hfalse hA₂).symm
      · simpa only [allTrueConfig, hiK, ↓reduceIte] using congrFun hfst i

/-- Pointwise dominance along `coinPairMap`: every prophet configuration `c` is bounded by the
gambler's reward at `(coinPairMap Y Z c).1`. -/
private theorem prophetCoinVal_le_gamblerCoinVal {Y Z : Fin n → TaggedValue n}
    (hZY : ∀ i, Z i < Y i) (c : Fin n → Bool) :
    prophetCoinVal Y Z c ≤ gamblerCoinVal Y Z (coinPairMap Y Z c).1 := by
  let zmax := Finset.univ.sup' Finset.univ_nonempty Z
  obtain ⟨istar, -, histar⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty Z
  have histar' : zmax = Z istar := histar
  have histarK : istar ∈ candSet Y Z :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      change zmax < Y istar; rw [histar']; exact hZY istar⟩
  have hKne : (candSet Y Z).Nonempty := ⟨istar, histarK⟩
  have hZle : ∀ j, Z j ≤ zmax := fun j => Finset.le_sup' Z (Finset.mem_univ j)
  have hnotK : ∀ j, j ∉ candSet Y Z → Y j ≤ zmax := fun j hj =>
    not_lt.mp fun hgt => hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩)
  have hallK : ∀ t : TaggedValue n, t ≤ Y (argminY Y (candSet Y Z) hKne) →
      tagVal t ≤ gamblerCoinVal Y Z (allTrueConfig Y Z c) := by
    intro t ht
    let c' := allTrueConfig Y Z c
    have hsmax : Finset.univ.sup' Finset.univ_nonempty (sampleChoice Y Z c') = zmax := by
      refine le_antisymm (Finset.sup'_le _ _ fun j _ => ?_) ?_
      · by_cases hjK : j ∈ candSet Y Z
        · simp only [sampleChoice, c', allTrueConfig, hjK, ↓reduceIte]; exact hZle j
        · simp only [sampleChoice, c', allTrueConfig, hjK, ↓reduceIte]
          split_ifs
          · exact hZle j
          · exact hnotK j hjK
      · calc zmax = sampleChoice Y Z c' istar := by
              simp [histar', sampleChoice, c', allTrueConfig, histarK]
          _ ≤ _ := Finset.le_sup' (sampleChoice Y Z c') (Finset.mem_univ istar)
    have hWne : (coinWinSet Y Z c').Nonempty := ⟨istar, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [hsmax]; simp only [onlineChoice, c', allTrueConfig, histarK, ↓reduceIte]
      exact (Finset.mem_filter.mp histarK).2⟩⟩
    have hwK : (coinWinSet Y Z c').min' hWne ∈ candSet Y Z := by
      have hgt := (Finset.mem_filter.mp (Finset.min'_mem _ hWne)).2
      rw [hsmax] at hgt
      by_contra hwK
      refine not_le.mpr hgt ?_
      simp only [onlineChoice, c', allTrueConfig, hwK, ↓reduceIte]
      split_ifs
      · exact hnotK _ hwK
      · exact hZle _
    rw [gamblerCoinVal_eq_of_nonempty hWne,
      show onlineChoice Y Z c' ((coinWinSet Y Z c').min' hWne) =
        Y ((coinWinSet Y Z c').min' hWne) by simp [onlineChoice, c', allTrueConfig, hwK]]
    exact tagVal_mono (ht.trans (argminY_le hKne hwK))
  have hprophet_A : ∀ (hA : (activeSet Y Z c).Nonempty),
      Finset.univ.sup' Finset.univ_nonempty (onlineChoice Y Z c) ≤
        Y (argmaxY Y (activeSet Y Z c) hA) := fun hA => by
    have hzm : zmax < Y (argmaxY Y (activeSet Y Z c) hA) :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp (argmaxY_mem hA)).1).2
    refine Finset.sup'_le _ _ fun j _ => ?_
    simp only [onlineChoice]
    split_ifs with hjc
    · by_cases hjK : j ∈ candSet Y Z
      · exact le_argmaxY hA (Finset.mem_filter.mpr ⟨hjK, hjc⟩)
      · exact (hnotK j hjK).trans hzm.le
    · exact (hZle j).trans hzm.le
  unfold coinPairMap prophetCoinVal
  by_cases hA : (activeSet Y Z c).Nonempty <;> simp only [hA, ↓reduceDIte]
  · let m := argmaxY Y (activeSet Y Z c) hA
    by_cases hL : (lowerSet Y Z m).Nonempty <;> simp only [m, hL, ↓reduceDIte]
    · let m' := argmaxY Y (lowerSet Y Z m) hL
      let c' := sub2Config Y Z m m' c
      have hmK : m ∈ candSet Y Z := (Finset.mem_filter.mp (argmaxY_mem hA)).1
      have hm'L : m' ∈ lowerSet Y Z m := argmaxY_mem hL
      have hm'K : m' ∈ candSet Y Z := (Finset.mem_filter.mp hm'L).1
      have hm'lt : Y m' < Y m := (Finset.mem_filter.mp hm'L).2
      have hzm' : zmax < Y m' := (Finset.mem_filter.mp hm'K).2
      have hle_m' : ∀ j, ¬(j ∈ candSet Y Z ∧ Y m ≤ Y j) →
          Y j ≤ Y m' ∧ Z j ≤ Y m' := fun j hj1 =>
        ⟨if hjK : j ∈ candSet Y Z then
            le_argmaxY hL (Finset.mem_filter.mpr ⟨hjK, not_le.mp fun h => hj1 ⟨hjK, h⟩⟩)
          else (hnotK j hjK).trans hzm'.le,
         (hZle j).trans hzm'.le⟩
      have hsmax : Finset.univ.sup' Finset.univ_nonempty (sampleChoice Y Z c') = Y m' := by
        refine le_antisymm (Finset.sup'_le _ _ fun j _ => ?_) ?_
        · by_cases hj1 : j ∈ candSet Y Z ∧ Y m ≤ Y j
          · simp only [sampleChoice, c', sub2Config, hj1.1, hj1.2, and_self, ↓reduceIte]
            exact (hZle j).trans hzm'.le
          · simp only [sampleChoice]; split_ifs
            · exact (hle_m' j hj1).2
            · exact (hle_m' j hj1).1
        · calc Y m' = sampleChoice Y Z c' m' := by
                simp [sampleChoice, c', sub2Config, hm'K, not_le.mpr hm'lt]
            _ ≤ _ := Finset.le_sup' (sampleChoice Y Z c') (Finset.mem_univ m')
      have hWne : (coinWinSet Y Z c').Nonempty := ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rw [hsmax]; simp only [onlineChoice, c', sub2Config, hmK, le_rfl, and_self, ↓reduceIte]
        exact hm'lt⟩⟩
      have hw_mem : (coinWinSet Y Z c').min' hWne ∈ candSet Y Z ∧
          Y m ≤ Y ((coinWinSet Y Z c').min' hWne) := by
        have hgt := (Finset.mem_filter.mp (Finset.min'_mem _ hWne)).2
        rw [hsmax] at hgt
        by_contra hnot
        refine not_le.mpr hgt ?_
        simp only [onlineChoice]; split_ifs
        · exact (hle_m' _ hnot).1
        · exact (hle_m' _ hnot).2
      change tagVal _ ≤ gamblerCoinVal Y Z c'
      rw [gamblerCoinVal_eq_of_nonempty hWne,
        show onlineChoice Y Z c' ((coinWinSet Y Z c').min' hWne) =
          Y ((coinWinSet Y Z c').min' hWne) by
            simp [onlineChoice, c', sub2Config, hw_mem.1, hw_mem.2]]
      exact tagVal_mono ((hprophet_A hA).trans hw_mem.2)
    · exact hallK _ <| (hprophet_A hA).trans <| by_contra fun hlt =>
        hL ⟨argminY Y (candSet Y Z) hKne, Finset.mem_filter.mpr ⟨argminY_mem hKne, not_le.mp hlt⟩⟩
  · refine hallK _ <| (Finset.sup'_le _ _ fun j _ => ?_).trans
      (Finset.mem_filter.mp (argminY_mem hKne)).2.le
    simp only [onlineChoice]
    split_ifs with hjc
    · exact hnotK j fun hjK => hA ⟨j, Finset.mem_filter.mpr ⟨hjK, hjc⟩⟩
    · exact hZle j

/-- Summing over all `2ⁿ` coin configurations: `∑_c prophet ≤ 2 * ∑_c gambler`. -/
private theorem sum_prophetCoinVal_le_two_mul_sum_gamblerCoinVal {Y Z : Fin n → TaggedValue n}
    (hZY : ∀ i, Z i < Y i) (hY : Function.Injective Y) :
    ∑ c : Fin n → Bool, prophetCoinVal Y Z c ≤ 2 * ∑ c : Fin n → Bool, gamblerCoinVal Y Z c := by
  calc ∑ c : Fin n → Bool, prophetCoinVal Y Z c
      ≤ ∑ c : Fin n → Bool, gamblerCoinVal Y Z (coinPairMap Y Z c).1 :=
        Finset.sum_le_sum fun c _ => prophetCoinVal_le_gamblerCoinVal hZY c
    _ = ∑ p ∈ Finset.univ.image (coinPairMap Y Z), gamblerCoinVal Y Z p.1 := by
        rw [Finset.sum_image fun _ _ _ _ h => coinPairMap_injective hY h]
    _ ≤ ∑ p : (Fin n → Bool) × Bool, gamblerCoinVal Y Z p.1 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => zero_le
    _ = ∑ c : Fin n → Bool, ∑ _b : Bool, gamblerCoinVal Y Z c :=
        Fintype.sum_prod_type fun p => gamblerCoinVal Y Z p.1
    _ = 2 * ∑ c : Fin n → Bool, gamblerCoinVal Y Z c := by
        simp only [Fintype.sum_bool, ← two_mul, Finset.mul_sum]

end CoinPairing

/-! ### Symmetry of sample and online slots under `piFin` and `Equiv.Perm` -/

/-- Swap `(2i)` and `(2i + 1)` at each coordinate `i` where `c i = false`. -/
private def slotSwapPerm {n : ℕ} (c : Fin n → Bool) : Equiv.Perm (Fin (2 * n)) where
  toFun m :=
    if c ⟨m.val / 2, by have := m.isLt; omega⟩ then m
    else ⟨2 * (m.val / 2) + (1 - m.val % 2), by have := m.isLt; omega⟩
  invFun m :=
    if c ⟨m.val / 2, by have := m.isLt; omega⟩ then m
    else ⟨2 * (m.val / 2) + (1 - m.val % 2), by have := m.isLt; omega⟩
  left_inv m := by
    have hm := m.isLt
    dsimp only
    by_cases hc : c ⟨m.val / 2, by omega⟩ = true
    · simp [hc]
    · have hc' : c ⟨m.val / 2, by omega⟩ = false := Bool.eq_false_iff.mpr hc
      have hdiv : (2 * (m.val / 2) + (1 - m.val % 2)) / 2 = m.val / 2 := by omega
      simp only [hc', Bool.false_eq_true, ↓reduceIte]
      have hc'' : c ⟨(2 * (m.val / 2) + (1 - m.val % 2)) / 2, by omega⟩ = false := by
        convert hc' using 2
        exact Fin.ext (by dsimp only; omega)
      simp only [hc'', Bool.false_eq_true, ↓reduceIte]
      exact Fin.ext (by dsimp only; omega)
  right_inv m := by
    have hm := m.isLt
    dsimp only
    by_cases hc : c ⟨m.val / 2, by omega⟩ = true
    · simp [hc]
    · have hc' : c ⟨m.val / 2, by omega⟩ = false := Bool.eq_false_iff.mpr hc
      have hdiv : (2 * (m.val / 2) + (1 - m.val % 2)) / 2 = m.val / 2 := by omega
      simp only [hc', Bool.false_eq_true, ↓reduceIte]
      have hc'' : c ⟨(2 * (m.val / 2) + (1 - m.val % 2)) / 2, by omega⟩ = false := by
        convert hc' using 2
        exact Fin.ext (by dsimp only; omega)
      simp only [hc'', Bool.false_eq_true, ↓reduceIte]
      exact Fin.ext (by dsimp only; omega)

private theorem slotSwapPerm_onlineSlot {n : ℕ} (c : Fin n → Bool) (i : Fin n) :
    slotSwapPerm c (onlineSlot i) = if c i then onlineSlot i else sampleSlot i := by
  have hi := i.isLt
  have hdiv : (⟨(2 * i.val + 1) / 2, by omega⟩ : Fin n) = i :=
    Fin.ext (by dsimp only; omega)
  simp only [slotSwapPerm, onlineSlot, sampleSlot, Equiv.coe_fn_mk, hdiv]
  split_ifs
  · rfl
  · exact Fin.ext (by dsimp only; omega)

private theorem slotSwapPerm_sampleSlot {n : ℕ} (c : Fin n → Bool) (i : Fin n) :
    slotSwapPerm c (sampleSlot i) = if c i then sampleSlot i else onlineSlot i := by
  have hi := i.isLt
  have hdiv : (⟨(2 * i.val) / 2, by omega⟩ : Fin n) = i :=
    Fin.ext (by dsimp only; omega)
  simp only [slotSwapPerm, onlineSlot, sampleSlot, Equiv.coe_fn_mk, hdiv]
  split_ifs
  · rfl
  · exact Fin.ext (by dsimp only; omega)

/-- Coordinatewise exchange `(x, s) ↦ (if c i then x i else s i, if c i then s i else x i)`. -/
private def swapTuples {α : Type*} {n : ℕ} (c : Fin n → Bool) :
    (Fin n → α) × (Fin n → α) ≃ (Fin n → α) × (Fin n → α) where
  toFun p := (fun i => if c i then p.1 i else p.2 i, fun i => if c i then p.2 i else p.1 i)
  invFun p := (fun i => if c i then p.1 i else p.2 i, fun i => if c i then p.2 i else p.1 i)
  left_inv p := by
    rcases p with ⟨x, s⟩
    exact Prod.ext (funext fun i => by dsimp only; cases c i <;> simp)
      (funext fun i => by dsimp only; cases c i <;> simp)
  right_inv p := by
    rcases p with ⟨x, s⟩
    exact Prod.ext (funext fun i => by dsimp only; cases c i <;> simp)
      (funext fun i => by dsimp only; cases c i <;> simp)

private theorem piFin_mul_swapTuples {n : ℕ} (μ : Fin n → PMF ℝ≥0) (c : Fin n → Bool)
    (x s : Fin n → ℝ≥0) :
    piFin μ (swapTuples c (x, s)).1 * piFin μ (swapTuples c (x, s)).2 =
      piFin μ x * piFin μ s := by
  simp only [piFin_apply, ← Finset.prod_mul_distrib, swapTuples, Equiv.coe_fn_mk]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases c i <;> simp [mul_comm]

/-- Deferred-decisions invariance: exchanging `(x i, onlineSlot i)` and `(s i, sampleSlot i)` along
any `c : Fin n → Bool` leaves the expectation over `(x, s, π)` unchanged. -/
private theorem tsum_swap_eq {n : ℕ} (μ : Fin n → PMF ℝ≥0) (c : Fin n → Bool)
    (F : (Fin n → ℝ≥0) → (Fin n → ℝ≥0) → Equiv.Perm (Fin (2 * n)) → ℝ≥0∞) :
    (∑' x, piFin μ x * ∑' s, piFin μ s *
      ∑' π, uniformOfFintype (Equiv.Perm (Fin (2 * n))) π * F x s π) =
    ∑' x, piFin μ x * ∑' s, piFin μ s *
      ∑' π, uniformOfFintype (Equiv.Perm (Fin (2 * n))) π *
        F (swapTuples c (x, s)).1 (swapTuples c (x, s)).2 (π * slotSwapPerm c) := by
  have hπ : ∀ x s,
      (∑' π, uniformOfFintype (Equiv.Perm (Fin (2 * n))) π * F x s π) =
      ∑' π, uniformOfFintype (Equiv.Perm (Fin (2 * n))) π *
        F x s (π * slotSwapPerm c) := fun x s => by
    rw [← (Equiv.mulRight (slotSwapPerm c)).tsum_eq]
    exact tsum_congr fun π => by simp [uniformOfFintype_apply]
  simp_rw [hπ]
  let H : (Fin n → ℝ≥0) × (Fin n → ℝ≥0) → ℝ≥0∞ := fun p =>
    piFin μ p.1 * (piFin μ p.2 *
      ∑' π, uniformOfFintype (Equiv.Perm (Fin (2 * n))) π * F p.1 p.2 (π * slotSwapPerm c))
  have hprod1 : (∑' x, piFin μ x * ∑' s, piFin μ s *
      ∑' π, uniformOfFintype (Equiv.Perm (Fin (2 * n))) π * F x s (π * slotSwapPerm c)) =
      ∑' p : (Fin n → ℝ≥0) × (Fin n → ℝ≥0), H p :=
    (tsum_congr fun _ => ENNReal.tsum_mul_left.symm).trans tsum_prod.symm
  have hprod2 : (∑' x, piFin μ x * ∑' s, piFin μ s *
      ∑' π, uniformOfFintype (Equiv.Perm (Fin (2 * n))) π *
        F (swapTuples c (x, s)).1 (swapTuples c (x, s)).2 (π * slotSwapPerm c)) =
      ∑' p : (Fin n → ℝ≥0) × (Fin n → ℝ≥0), H (swapTuples c p) := by
    calc _ = ∑' x, ∑' s, H (swapTuples c (x, s)) := tsum_congr fun x => by
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun s => by simp only [H, ← mul_assoc, piFin_mul_swapTuples μ c x s]
      _ = _ := tsum_prod.symm
  rw [hprod1, hprod2, (swapTuples c).tsum_eq]

/-! ### Main theorem -/

private theorem finset_sum_tsum_ennreal {α β : Type*} (S : Finset α) (f : α → β → ℝ≥0∞) :
    ∑ a ∈ S, ∑' b, f a b = ∑' b, ∑ a ∈ S, f a b :=
  (Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable).symm

private theorem tsum_mul_tsum_mul_comm {α β : Type*} (f : α → ℝ≥0∞) (g : β → ℝ≥0∞)
    (h : α → β → ℝ≥0∞) :
    (∑' a, f a * ∑' b, g b * h a b) = ∑' b, g b * ∑' a, f a * h a b := by
  calc (∑' a, f a * ∑' b, g b * h a b)
      = ∑' a, ∑' b, f a * (g b * h a b) := tsum_congr fun _ => ENNReal.tsum_mul_left.symm
    _ = ∑' b, ∑' a, f a * (g b * h a b) := tsum_comm
    _ = _ := tsum_congr fun b => by
        rw [← ENNReal.tsum_mul_left]; exact tsum_congr fun a => mul_left_comm _ _ _

/-- **The single-sample prophet inequality** ([RubinsteinWangWeinberg2020], Theorem 1, p. 1, and
Proof of Theorem 1, §3, p. 4).

For any `n` independent nonnegative distributions `μ : Fin n → PMF ℝ≥0`, given one offline sample
`sᵢ ~ μᵢ` from each distribution and an independent uniform tie-breaking permutation `π`, the
online stopping rule `singleSampleRule s π` collects in expectation at least half of the prophet's
expected maximum `expectedMax (List.ofFn μ)`. No finiteness or atom-freeness hypothesis is
needed. -/
theorem expectedMax_le_two_mul_singleSampleExpectedReward {n : ℕ} (μ : Fin n → PMF ℝ≥0) :
    expectedMax (List.ofFn μ) ≤ 2 * singleSampleExpectedReward μ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [expectedMax, listMax]
  have : NeZero n := ⟨hn.ne'⟩
  let G : (Fin n → ℝ≥0) → (Fin n → ℝ≥0) → Equiv.Perm (Fin (2 * n)) → ℝ≥0∞ :=
    fun x s π => firstBeatReward x s π
  let P : (Fin n → ℝ≥0) → (Fin n → ℝ≥0) → Equiv.Perm (Fin (2 * n)) → ℝ≥0∞ :=
    fun x _ _ => (listMax (List.ofFn x) : ℝ≥0∞)
  have hLHS : expectedMax (List.ofFn μ) =
      ∑' x, piFin μ x * ∑' s, piFin μ s *
        ∑' π, uniformOfFintype (Equiv.Perm (Fin (2 * n))) π * P x s π := by
    rw [expectedMax, tsum_jointLaw_ofFn_mul]
    exact tsum_congr fun x => by simp only [P, tsum_pmf_mul_const]
  have hRHS : singleSampleExpectedReward μ =
      ∑' x, piFin μ x * ∑' s, piFin μ s *
        ∑' π, uniformOfFintype (Equiv.Perm (Fin (2 * n))) π * G x s π := by
    rw [singleSampleExpectedReward]
    have hexp : ∀ s π, expectedReward (singleSampleRule s π) (List.ofFn μ) =
        ∑' x, piFin μ x * G x s π := fun s π => by
      rw [expectedReward, tsum_jointLaw_ofFn_mul]
      exact tsum_congr fun x => by rw [payoff_singleSampleRule_ofFn]
    simp_rw [hexp, tsum_mul_tsum_mul_comm (uniformOfFintype (Equiv.Perm (Fin (2 * n)))) (piFin μ)]
    exact tsum_mul_tsum_mul_comm (piFin μ) (piFin μ) _
  rw [← ENNReal.mul_le_mul_iff_right (by simp : (Fintype.card (Fin n → Bool) : ℝ≥0∞) ≠ 0)
    (ENNReal.natCast_ne_top _)]
  have havg : ∀ (F : (Fin n → ℝ≥0) → (Fin n → ℝ≥0) → Equiv.Perm (Fin (2 * n)) → ℝ≥0∞),
      (Fintype.card (Fin n → Bool) : ℝ≥0∞) *
        (∑' x, piFin μ x * ∑' s, piFin μ s *
          ∑' π, uniformOfFintype (Equiv.Perm (Fin (2 * n))) π * F x s π) =
      ∑' x, piFin μ x * ∑' s, piFin μ s *
        ∑' π, uniformOfFintype (Equiv.Perm (Fin (2 * n))) π *
          ∑ c : Fin n → Bool, F (swapTuples c (x, s)).1 (swapTuples c (x, s)).2
            (π * slotSwapPerm c) := fun F => by
    calc _ = ∑ c : Fin n → Bool, ∑' x, piFin μ x * ∑' s, piFin μ s *
              ∑' π, uniformOfFintype (Equiv.Perm (Fin (2 * n))) π *
                F (swapTuples c (x, s)).1 (swapTuples c (x, s)).2 (π * slotSwapPerm c) := by
            rw [← Finset.card_univ, ← nsmul_eq_mul, ← Finset.sum_const]
            exact Finset.sum_congr rfl fun c _ => tsum_swap_eq μ c F
      _ = _ := by
            rw [finset_sum_tsum_ennreal]
            refine tsum_congr fun x => ?_
            rw [← Finset.mul_sum, finset_sum_tsum_ennreal]; congr 1
            refine tsum_congr fun s => ?_
            rw [← Finset.mul_sum, finset_sum_tsum_ennreal]; congr 1
            exact tsum_congr fun π => (Finset.mul_sum _ _ _).symm
  rw [hLHS, hRHS, havg P, ← mul_assoc, mul_comm (Fintype.card (Fin n → Bool) : ℝ≥0∞) 2, mul_assoc,
    havg G]
  have hpull2 : 2 * (∑' x, piFin μ x * ∑' s, piFin μ s *
      ∑' π, uniformOfFintype (Equiv.Perm (Fin (2 * n))) π *
        ∑ c : Fin n → Bool, G (swapTuples c (x, s)).1 (swapTuples c (x, s)).2
          (π * slotSwapPerm c)) =
      ∑' x, piFin μ x * ∑' s, piFin μ s *
        ∑' π, uniformOfFintype (Equiv.Perm (Fin (2 * n))) π *
          (2 * ∑ c : Fin n → Bool, G (swapTuples c (x, s)).1 (swapTuples c (x, s)).2
            (π * slotSwapPerm c)) := by
    rw [← ENNReal.tsum_mul_left]; refine tsum_congr fun x => ?_
    rw [mul_left_comm, ← ENNReal.tsum_mul_left]; congr 1; refine tsum_congr fun s => ?_
    rw [mul_left_comm, ← ENNReal.tsum_mul_left]; congr 1
    exact tsum_congr fun π => mul_left_comm _ _ _
  rw [hpull2]
  refine tsum_le_tsum fun x => mul_le_mul_right (tsum_le_tsum fun s =>
    mul_le_mul_right (tsum_le_tsum fun π => mul_le_mul_right ?_ _) _) _
  let p₀ : Fin n → TaggedValue n := fun i => onlineTag (x i) π i
  let p₁ : Fin n → TaggedValue n := fun i => sampleTag s π i
  let Y : Fin n → TaggedValue n := fun i => max (p₀ i) (p₁ i)
  let Z : Fin n → TaggedValue n := fun i => min (p₀ i) (p₁ i)
  have hZY : ∀ i, Z i < Y i := fun i => min_lt_max.mpr fun h => by
    have hinj := π.injective (congrArg (Prod.snd ∘ ofLex) h)
    simp only [onlineSlot, sampleSlot, Fin.mk.injEq] at hinj; omega
  have hY : Function.Injective Y := by
    have hrank : ∀ i, (ofLex (Y i)).2 = π (onlineSlot i) ∨ (ofLex (Y i)).2 = π (sampleSlot i) :=
      fun i => by
        rcases max_choice (p₀ i) (p₁ i) with h | h <;> rw [show Y i = _ from h] <;>
          simp [p₀, p₁, onlineTag, sampleTag]
    intro i j hij
    have heq2 : (ofLex (Y i)).2 = (ofLex (Y j)).2 := congrArg (Prod.snd ∘ ofLex) hij
    rcases hrank i with hi | hi <;> rcases hrank j with hj | hj <;>
      have := π.injective (hi.symm.trans (heq2.trans hj)) <;>
      simp only [onlineSlot, sampleSlot, Fin.mk.injEq] at this
    · exact Fin.ext (by omega)
    · omega
    · omega
    · exact Fin.ext (by omega)
  let d : Fin n → Bool := fun i => decide (p₁ i ≤ p₀ i)
  let xorEquiv : (Fin n → Bool) ≃ (Fin n → Bool) := {
    toFun := fun c i => if d i then c i else !c i
    invFun := fun c i => if d i then c i else !c i
    left_inv := fun c => by funext i; dsimp only; cases d i <;> cases c i <;> simp
    right_inv := fun c => by funext i; dsimp only; cases d i <;> cases c i <;> simp
  }
  have honline : ∀ (c : Fin n → Bool) (i : Fin n),
      onlineTag ((swapTuples (xorEquiv c) (x, s)).1 i) (π * slotSwapPerm (xorEquiv c)) i =
        onlineChoice Y Z c i := fun c i => by
    simp only [onlineTag, Equiv.Perm.mul_apply, slotSwapPerm_onlineSlot, swapTuples,
      Equiv.coe_fn_mk, onlineChoice, xorEquiv]
    by_cases hle : p₁ i ≤ p₀ i
    · simp only [d, decide_eq_true hle, ↓reduceIte, Y, Z, max_eq_left hle, min_eq_right hle]
      cases c i <;> rfl
    · have hle' : p₀ i ≤ p₁ i := (not_le.mp hle).le
      simp only [d, decide_eq_false hle, Bool.false_eq_true, ↓reduceIte, Y, Z,
        max_eq_right hle', min_eq_left hle']
      cases c i <;> rfl
  have hsample : ∀ (c : Fin n → Bool) (i : Fin n),
      sampleTag (swapTuples (xorEquiv c) (x, s)).2 (π * slotSwapPerm (xorEquiv c)) i =
        sampleChoice Y Z c i := fun c i => by
    simp only [sampleTag, Equiv.Perm.mul_apply, slotSwapPerm_sampleSlot, swapTuples,
      Equiv.coe_fn_mk, sampleChoice, xorEquiv]
    by_cases hle : p₁ i ≤ p₀ i
    · simp only [d, decide_eq_true hle, ↓reduceIte, Y, Z, max_eq_left hle, min_eq_right hle]
      cases c i <;> rfl
    · have hle' : p₀ i ≤ p₁ i := (not_le.mp hle).le
      simp only [d, decide_eq_false hle, Bool.false_eq_true, ↓reduceIte, Y, Z,
        max_eq_right hle', min_eq_left hle']
      cases c i <;> rfl
  rw [← xorEquiv.sum_comp
      (fun c => P (swapTuples c (x, s)).1 (swapTuples c (x, s)).2 (π * slotSwapPerm c)),
    ← xorEquiv.sum_comp
      (fun c => G (swapTuples c (x, s)).1 (swapTuples c (x, s)).2 (π * slotSwapPerm c))]
  have hP_eq : ∀ c : Fin n → Bool,
      P (swapTuples (xorEquiv c) (x, s)).1 (swapTuples (xorEquiv c) (x, s)).2
        (π * slotSwapPerm (xorEquiv c)) = prophetCoinVal Y Z c := fun c => by
    simp only [P, listMax_ofFn_eq_sup', prophetCoinVal, tagVal]
    congr 1
    refine le_antisymm (Finset.sup'_le _ _ fun i _ => ?_) ?_
    · rw [show (swapTuples (xorEquiv c) (x, s)).1 i = (ofLex (onlineChoice Y Z c i)).1 by
        rw [← honline c i]; rfl]
      exact Prod.Lex.monotone_fst _ _ (Finset.le_sup' (onlineChoice Y Z c) (Finset.mem_univ i))
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (onlineChoice Y Z c)
      rw [show (ofLex (Finset.univ.sup' Finset.univ_nonempty (onlineChoice Y Z c))).1 =
        (swapTuples (xorEquiv c) (x, s)).1 i by rw [hi, ← honline c i]; rfl]
      exact Finset.le_sup' (swapTuples (xorEquiv c) (x, s)).1 (Finset.mem_univ i)
  have hG_eq : ∀ c : Fin n → Bool,
      G (swapTuples (xorEquiv c) (x, s)).1 (swapTuples (xorEquiv c) (x, s)).2
        (π * slotSwapPerm (xorEquiv c)) = gamblerCoinVal Y Z c := fun c => by
    have hfilt : (Finset.univ.filter fun i : Fin n =>
        ∀ j : Fin n, sampleTag (swapTuples (xorEquiv c) (x, s)).2
          (π * slotSwapPerm (xorEquiv c)) j <
          onlineTag ((swapTuples (xorEquiv c) (x, s)).1 i)
            (π * slotSwapPerm (xorEquiv c)) i) = coinWinSet Y Z c := by
      ext i
      simp only [coinWinSet, Finset.mem_filter, Finset.mem_univ, true_and, honline c i,
        Finset.sup'_lt_iff]
      exact ⟨fun h j _ => hsample c j ▸ h j, fun h j => (hsample c j).symm ▸ h j trivial⟩
    unfold G firstBeatReward gamblerCoinVal
    dsimp only
    rw [hfilt]
    split_ifs with hW
    · rw [tagVal, ← honline c ((coinWinSet Y Z c).min' hW)]; rfl
    · rfl
  rw [Finset.sum_congr rfl fun c _ => hP_eq c, Finset.sum_congr rfl fun c _ => hG_eq c]
  exact sum_prophetCoinVal_le_two_mul_sum_gamblerCoinVal hZY hY

/-! ### Arrival-order invariance and atom-boundary witness -/

private theorem expectedMax_perm {n : ℕ} (μ : Fin n → PMF ℝ≥0) (σ : Equiv.Perm (Fin n)) :
    expectedMax (List.ofFn (μ ∘ σ)) = expectedMax (List.ofFn μ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [expectedMax]
  have : NeZero n := ⟨hn.ne'⟩
  rw [expectedMax, expectedMax, tsum_jointLaw_ofFn_mul, tsum_jointLaw_ofFn_mul]
  let e : (Fin n → ℝ≥0) ≃ (Fin n → ℝ≥0) := Equiv.arrowCongr σ.symm (Equiv.refl ℝ≥0)
  rw [← e.tsum_eq]
  refine tsum_congr fun x => ?_
  have he : ∀ i : Fin n, e x i = x (σ i) := fun i => by simp [e, Equiv.arrowCongr_apply]
  have hpi : piFin (μ ∘ σ) (e x) = piFin μ x := by
    simp only [piFin_apply, Function.comp_apply, he]; exact Equiv.prod_comp σ fun i => μ i (x i)
  have hmax : listMax (List.ofFn (e x)) = listMax (List.ofFn x) := by
    rw [listMax_ofFn_eq_sup', listMax_ofFn_eq_sup']
    exact le_antisymm
      (Finset.sup'_le _ _ fun i _ => he i ▸ Finset.le_sup' x (Finset.mem_univ (σ i)))
      (Finset.sup'_le _ _ fun i _ => by
        have hle := Finset.le_sup' (e x) (Finset.mem_univ (σ.symm i))
        rwa [he, Equiv.apply_symm_apply] at hle)
  rw [hpi, hmax]

/-- **Arrival-order invariance**: under any fixed arrival permutation `σ : Equiv.Perm (Fin n)`,
running the single-sample algorithm on `μ ∘ σ` achieves at least half of
`expectedMax (List.ofFn μ)`. -/
theorem expectedMax_le_two_mul_singleSampleExpectedReward_perm {n : ℕ} (μ : Fin n → PMF ℝ≥0)
    (σ : Equiv.Perm (Fin n)) :
    expectedMax (List.ofFn μ) ≤ 2 * singleSampleExpectedReward (μ ∘ σ) := by
  rw [← expectedMax_perm μ σ]
  exact expectedMax_le_two_mul_singleSampleExpectedReward (μ ∘ σ)

/-- Without randomized tie-breaking, the deterministic strict-maximum rule `strictSampleRule`
collects `0` on `n ≥ 1` identical point-mass distributions `PMF.pure a`, since every online value
equals the sample maximum `a`. -/
theorem expectedReward_strictSampleRule_pure_eq_zero {n : ℕ} [NeZero n] (a : ℝ≥0) :
    strictSampleExpectedReward (fun _ : Fin n => PMF.pure a) = 0 := by
  have hpi : piFin (fun _ : Fin n => PMF.pure a) = PMF.pure (fun _ => a) := by
    ext s
    rw [piFin_apply, PMF.pure_apply]
    by_cases hs : s = fun _ => a
    · subst hs; simp
    · obtain ⟨i, hi⟩ : ∃ i, s i ≠ a := by_contra fun h => hs (funext (by simpa using h))
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [PMF.pure_apply, hi])]
      simp [hs]
  rw [strictSampleExpectedReward, hpi, tsum_pure_mul, expectedReward, tsum_jointLaw_ofFn_mul, hpi,
    tsum_pure_mul]
  have hpay : ∀ (l past : List ℝ≥0), (∀ y ∈ l, y = a) →
      payoff (strictSampleRule (fun _ : Fin n => a)) reward past l = 0 := fun l => by
    induction l with
    | nil => intros; rfl
    | cons y ys ih =>
        intro past hall
        have hfalse : strictSampleRule (fun _ : Fin n => a) (a :: past) = false := by
          simp only [strictSampleRule, acceptRule, decide_eq_false_iff_not]
          rintro ⟨hlt, -⟩; exact lt_irrefl a (hlt 0)
        rw [hall y List.mem_cons_self, payoff_cons, hfalse]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih (a :: past) fun z hz => hall z (List.mem_cons_of_mem _ hz)
  exact hpay _ [] fun _ hy => by obtain ⟨_, rfl⟩ := List.mem_ofFn.mp hy; rfl

end Cslib.Probability.OptimalStopping.Prophet
