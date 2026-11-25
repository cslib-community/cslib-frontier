/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.Taxation
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Affine maximizers and Roberts' theorem

Characterization of dominant-strategy incentive compatible (DSIC) mechanisms on unrestricted
valuation domains `ℝ^Ω` ([Nisan2007], §9.5.3, p. 228; [Lavi2007], §12.4, pp. 317–320, and
Exercise 12.8, p. 329).

* **Affine maximizers & weighted Groves mechanisms** ([Nisan2007], Definition 9.30 &
  Proposition 9.31, p. 228; [Lavi2007], Definition 12.23, p. 317): an outcome rule `f` maximizes
  the affine score `c ω + ∑ i, w i * b i ω` over a subrange `A ⊆ Ω` for nonnegative, not-all-zero
  player weights `w : ι → ℝ` and additive outcome weights `c : Ω → ℝ`. Note two literal slips in
  the textbook definitions:
  - [Nisan2007], Definition 9.30 writes `wᵢ ∈ ℝ⁺` (strictly positive weights), which guarantees
    DSIC for arbitrary tie-breaking via `weightedGroves` (Proposition 9.31) but literally excludes
    dictatorships (`w = (1, 0, …, 0)`), which are surjective and DSIC and therefore must be
    admitted in Theorem 9.32.
  - [Lavi2007], Definition 12.23 omits the sign/nonzero conditions `wᵢ ≥ 0` and `∃ i, wᵢ > 0`;
    negative weights produce non-implementable rules (e.g., `argmin`), and all-zero weights with
    `c = 0` would accept every function. When some `wᵢ = 0`, arbitrary adverse tie-breaking can
    break DSIC; `weightedGroves_isDSIC_of_nonneg` proves DSIC when weight-zero agents are dummies.
* **PAD & Generalized-WMON** ([Lavi2007], Definitions 12.27 & 12.29, Claims 12.28 & 12.30,
  pp. 318–319): positive association of differences holds on arbitrary domains for weakly monotone
  (and hence implementable) rules with finitely many agents, and implies generalized weak
  monotonicity on the unrestricted domain `ℝ^Ω`.
* **Roberts' theorem** ([Nisan2007], Theorem 9.32, p. 228; [Lavi2007], Theorem 12.24, p. 318):
  for finitely many agents and finitely many outcomes `|Ω| ≥ 3`, every surjective weakly monotone
  (in particular, DSIC-implementable) social choice function `f : (ι → Ω → ℝ) → Ω` is an affine
  maximizer with nonnegative weights summing to `1` (`∃ i, 0 < w i`). The proof follows [Lavi2007],
  Claims 12.31–12.34 and Exercise 12.8 (pp. 319–320, 329): forming the difference sets `P(x, y)`
  and their uniform shifts `γ(x, y) = inf {p ∈ ℝ | p · 1 ∈ P(x, y)}`, proving `γ(x, y) = -γ(y, x)`
  and `γ(x, z) = γ(x, y) + γ(y, z)`, identifying the common open shifted cone `K` (convex and
  excluding `0`), separating `0` from `K` by geometric Hahn–Banach, and reading off the additive
  terms `c x = γ(x₀, x)`.
* **Neutral Roberts' theorem** ([Lavi2007], Definition 12.25 & Theorem 12.26, p. 318): when `f` is
  neutral (unanimity on strict peaks), every shift `γ(x, y) = 0`, so `f` maximizes pure weighted
  welfare `∑ i, w i * b i ω` with `c = 0`.
* **Finite-range extension**: when `Set.range f` is finite with `3 ≤ (Set.range f).ncard` (without
  assuming `f` surjective or `Ω` finite), weak monotonicity still forces `f` to be an affine
  maximizer over `Set.range f`.

No running-time or computability claim is made in this module.

## Main definitions

* `Mechanism.affineScore`: the weighted affine score `c ω + ∑ i, w i * b i ω`.
* `Mechanism.IsAffineMaximizerFor`, `Mechanism.IsAffineMaximizer`: affine-maximizing outcome rules.
* `Mechanism.weightedGroves`: the weighted Groves (weighted VCG) mechanism.
* `Mechanism.IsNeutral`: neutrality / unanimity on strictly preferred outcomes.
* `Mechanism.IsPADOn`, `Mechanism.IsGeneralizedWMONOn`: positive association of differences and
  generalized weak monotonicity.

## Main results

* `Mechanism.weightedGroves_isDSIC`, `Mechanism.weightedGroves_isDSIC_of_nonneg`: weighted Groves
  mechanisms are DSIC ([Nisan2007], Proposition 9.31, p. 228).
* `Mechanism.IsWeaklyMonotoneOn.isPADOn`: weak monotonicity implies PAD ([Lavi2007], Claim 12.28,
  p. 318).
* `Mechanism.isGeneralizedWMON_of_isPAD`: PAD on `ℝ^Ω` implies Generalized-WMON ([Lavi2007],
  Claim 12.30, p. 319).
* `Mechanism.exists_isAffineMaximizerFor_of_isWeaklyMonotone`,
  `Mechanism.IsImplementable.isAffineMaximizer`, `Mechanism.IsDSIC.isAffineMaximizer`:
  **Roberts' theorem** for surjective rules ([Nisan2007], Theorem 9.32, p. 228; [Lavi2007],
  Theorem 12.24, p. 318).
* `Mechanism.exists_isAffineMaximizerFor_range_of_isWeaklyMonotone`: finite-range Roberts' theorem
  over `Set.range f`.
* `Mechanism.exists_weightedWelfare_of_isNeutral_of_isWeaklyMonotone`,
  `Mechanism.exists_weightedWelfare_of_isNeutral_of_isImplementable`: **neutral Roberts' theorem**
  with `c = 0` ([Lavi2007], Theorem 12.26, p. 318).

## References

* [N. Nisan, *Introduction to Mechanism Design (for Computer Scientists)*][Nisan2007]
* [R. Lavi, *Computationally Efficient Approximation Mechanisms*][Lavi2007]
-/

public section

namespace Cslib.GameTheory.Mechanism

variable {ι Ω : Type*}

/-! ### Affine maximizers and weighted Groves (Nisan 2007, §9.5.3; Lavi 2007, Def. 12.23) -/

/-- The affine score `c ω + ∑ i, w i * b i ω` of outcome `ω` under profile `b`, with player
weights `w : ι → ℝ` and additive outcome weights `c : Ω → ℝ`. -/
@[expose] def affineScore [Fintype ι] (w : ι → ℝ) (c : Ω → ℝ) (b : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  c ω + ∑ i, w i * b i ω

/-- An outcome rule `f` maximizes the affine score `(w, c)` over the subrange `A ⊆ Ω`. -/
@[expose] def IsAffineMaximizerFor [Fintype ι] (f : (ι → Ω → ℝ) → Ω) (A : Set Ω)
    (w : ι → ℝ) (c : Ω → ℝ) : Prop :=
  ∀ b, f b ∈ A ∧ ∀ ω ∈ A, affineScore w c b ω ≤ affineScore w c b (f b)

/-- An **affine maximizer** ([Nisan2007], Definition 9.30, p. 228; [Lavi2007], Definition 12.23,
p. 317): there exist a subrange `A ⊆ Ω`, nonnegative, not-all-zero player weights `w : ι → ℝ`,
and outcome offsets `c : Ω → ℝ` such that `f b ∈ argmax_{ω ∈ A} (c ω + ∑ i, w i * b i ω)` for
every profile `b`. Allowing `w i = 0` (unlike `w i > 0` in [Nisan2007], Definition 9.30) is
necessary to include dictatorships in Roberts' theorem; requiring `0 ≤ w i` and `∃ i, 0 < w i`
repairs the omission in [Lavi2007], Definition 12.23. -/
@[expose] def IsAffineMaximizer [Fintype ι] (f : (ι → Ω → ℝ) → Ω) : Prop :=
  ∃ (A : Set Ω) (w : ι → ℝ) (c : Ω → ℝ),
    (∀ i, 0 ≤ w i) ∧ (∃ i, 0 < w i) ∧ IsAffineMaximizerFor f A w c

/-- The **weighted Groves** (weighted VCG) mechanism ([Nisan2007], Proposition 9.31, p. 228):
for agent `i`, with `w i ≠ 0` the payment is
`h i b - ∑ j ≠ i, (w j / w i) * b j (f b) - c (f b) / w i`; when `w i = 0`, it is `h i b`. -/
noncomputable def weightedGroves [Fintype ι] [DecidableEq ι]
    (f : (ι → Ω → ℝ) → Ω) (w : ι → ℝ) (c : Ω → ℝ) (h : ι → (ι → Ω → ℝ) → ℝ) :
    Mechanism ι Ω where
  outcome := f
  payment b i :=
    if w i = 0 then h i b
    else h i b - (∑ j ∈ Finset.univ.erase i, (w j / w i) * b j (f b) + c (f b) / w i)

/-- The outcome rule of `weightedGroves f w c h` is `f`. -/
@[simp] theorem weightedGroves_outcome [Fintype ι] [DecidableEq ι]
    (f : (ι → Ω → ℝ) → Ω) (w : ι → ℝ) (c : Ω → ℝ) (h : ι → (ι → Ω → ℝ) → ℝ) :
    (weightedGroves f w c h).outcome = f := by
  unfold weightedGroves
  rfl

/-- Payment charged to agent `i` on reports `b` under `weightedGroves f w c h`. -/
@[simp] theorem weightedGroves_payment [Fintype ι] [DecidableEq ι]
    (f : (ι → Ω → ℝ) → Ω) (w : ι → ℝ) (c : Ω → ℝ) (h : ι → (ι → Ω → ℝ) → ℝ)
    (b : ι → Ω → ℝ) (i : ι) :
    (weightedGroves f w c h).payment b i =
      if w i = 0 then h i b
      else h i b - (∑ j ∈ Finset.univ.erase i, (w j / w i) * b j (f b) + c (f b) / w i) := by
  unfold weightedGroves
  rfl

private theorem affineScore_eq_add [Fintype ι] [DecidableEq ι] (w : ι → ℝ) (c : Ω → ℝ)
    (b : ι → Ω → ℝ) (i : ι) (ω : Ω) :
    affineScore w c b ω = c ω + w i * b i ω + ∑ j ∈ Finset.univ.erase i, w j * b j ω := by
  simp only [affineScore]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  ring

private theorem sum_erase_weighted_update [Fintype ι] [DecidableEq ι] (g : ι → ℝ)
    (b : ι → Ω → ℝ) (i : ι) (v : Ω → ℝ) (ω : Ω) :
    ∑ j ∈ Finset.univ.erase i, g j * Function.update b i v j ω =
      ∑ j ∈ Finset.univ.erase i, g j * b j ω :=
  Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- **Weighted Groves mechanisms with dummy weight-zero agents are DSIC**: if `f` maximizes the
affine score `(w, c)` over `A` with nonnegative weights `w`, each pivot `h i` ignores `i`'s report,
and every agent with `w i = 0` cannot change the chosen outcome, then `weightedGroves f w c h` is
DSIC. Note that without the dummy condition, adverse tie-breaking for a weight-zero agent can break
DSIC. -/
theorem weightedGroves_isDSIC_of_nonneg [Fintype ι] [DecidableEq ι] {f : (ι → Ω → ℝ) → Ω}
    {A : Set Ω} {w : ι → ℝ} {c : Ω → ℝ} {h : ι → (ι → Ω → ℝ) → ℝ}
    (hf : IsAffineMaximizerFor f A w c) (hw : ∀ i, 0 ≤ w i)
    (hdummy : ∀ i, w i = 0 → ∀ b v, f (Function.update b i v) = f b)
    (hh : ∀ i b v, h i (Function.update b i v) = h i b) :
    (weightedGroves f w c h).IsDSIC := by
  intro i b v
  by_cases hwi : w i = 0
  · simp only [utility, weightedGroves, hwi, ↓reduceIte, hdummy i hwi b v, hh i b v, le_rfl]
  · have hpos : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hwi)
    have hkey := (hf (Function.update b i v)).2 (f b) (hf b).1
    rw [affineScore_eq_add w c _ i, affineScore_eq_add w c _ i, Function.update_self,
      sum_erase_weighted_update, sum_erase_weighted_update] at hkey
    have hmul_eq : ∀ ω : Ω,
        w i * (∑ j ∈ Finset.univ.erase i, (w j / w i) * b j ω + c ω / w i) =
          ∑ j ∈ Finset.univ.erase i, w j * b j ω + c ω := fun ω => by
      rw [mul_add, Finset.mul_sum, mul_div_cancel₀ _ hwi]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by
        rw [← mul_assoc, mul_div_cancel₀ _ hwi]
    refine le_of_mul_le_mul_left ?_ hpos
    simp only [utility, weightedGroves, hwi, ↓reduceIte, hh i b v, sum_erase_weighted_update]
    calc
      w i * (v (f b) - (h i b -
          (∑ j ∈ Finset.univ.erase i, (w j / w i) * b j (f b) + c (f b) / w i)))
          = w i * v (f b) - w i * h i b +
              w i * (∑ j ∈ Finset.univ.erase i, (w j / w i) * b j (f b) + c (f b) / w i) := by
            ring
      _ = w i * v (f b) - w i * h i b +
            (∑ j ∈ Finset.univ.erase i, w j * b j (f b) + c (f b)) := by rw [hmul_eq]
      _ ≤ w i * v (f (Function.update b i v)) - w i * h i b +
            (∑ j ∈ Finset.univ.erase i, w j * b j (f (Function.update b i v)) +
              c (f (Function.update b i v))) := by linarith
      _ = w i * v (f (Function.update b i v)) - w i * h i b +
            w i * (∑ j ∈ Finset.univ.erase i,
              (w j / w i) * b j (f (Function.update b i v)) +
                c (f (Function.update b i v)) / w i) := by rw [hmul_eq]
      _ = w i * (v (f (Function.update b i v)) - (h i b -
            (∑ j ∈ Finset.univ.erase i,
              (w j / w i) * b j (f (Function.update b i v)) +
                c (f (Function.update b i v)) / w i))) := by ring

/-- **Weighted Groves mechanisms are DSIC** ([Nisan2007], Proposition 9.31, §9.5.3, p. 228): if `f`
maximizes the affine score `c ω + ∑ i, w i * b i ω` over a subrange `A ⊆ Ω` with strictly positive
weights `w i > 0` and each pivot `h i` is independent of agent `i`'s report, then
`weightedGroves f w c h` is DSIC under arbitrary tie-breaking. -/
theorem weightedGroves_isDSIC [Fintype ι] [DecidableEq ι] {f : (ι → Ω → ℝ) → Ω} {A : Set Ω}
    {w : ι → ℝ} {c : Ω → ℝ} {h : ι → (ι → Ω → ℝ) → ℝ}
    (hf : IsAffineMaximizerFor f A w c) (hw : ∀ i, 0 < w i)
    (hh : ∀ i b v, h i (Function.update b i v) = h i b) :
    (weightedGroves f w c h).IsDSIC :=
  weightedGroves_isDSIC_of_nonneg hf (fun i => (hw i).le)
    (fun i hi => absurd hi (hw i).ne') hh

/-- Every positive-weight affine maximizer is DSIC-implementable ([Nisan2007], Proposition 9.31,
§9.5.3, p. 228). -/
theorem IsAffineMaximizerFor.isImplementable [Fintype ι] [DecidableEq ι] {f : (ι → Ω → ℝ) → Ω}
    {A : Set Ω} {w : ι → ℝ} {c : Ω → ℝ} (hf : IsAffineMaximizerFor f A w c)
    (hw : ∀ i, 0 < w i) : IsImplementable f :=
  ⟨(weightedGroves f w c fun _ _ => 0).payment, weightedGroves_isDSIC hf hw fun _ _ _ => rfl⟩

/-! ### Neutrality, PAD, and Generalized-WMON (Lavi 2007, §12.4) -/

/-- **Neutrality** ([Lavi2007], Definition 12.25, §12.4, p. 318): if every agent strictly prefers
alternative `x` to every other alternative `y ≠ x`, then `f` must select `x`. -/
@[expose] def IsNeutral (f : (ι → Ω → ℝ) → Ω) : Prop :=
  ∀ (v : ι → Ω → ℝ) (x : Ω), (∀ i, ∀ y, y ≠ x → v i y < v i x) → f v = x

/-- Every neutral social choice rule is surjective. -/
theorem IsNeutral.surjective {f : (ι → Ω → ℝ) → Ω} (hf : IsNeutral f) :
    Function.Surjective f := by
  classical
  intro x
  refine ⟨fun _ y => if y = x then 1 else 0, hf _ x fun _ y hy => ?_⟩
  simp only [hy, ↓reduceIte, zero_lt_one]

/-- **Positive association of differences (PAD)** on domains `V` ([Lavi2007], Definition 12.27,
§12.4, p. 318): if `f v = x` and `v'` strictly raises every agent's valuation of `x` relative to
every `y ≠ x`, then `f v' = x`. -/
@[expose] def IsPADOn (f : (ι → Ω → ℝ) → Ω) (V : ι → Set (Ω → ℝ)) : Prop :=
  ∀ (v v' : ι → Ω → ℝ), (∀ i, v i ∈ V i) → (∀ i, v' i ∈ V i) →
    (∀ i, ∀ y, y ≠ f v → v' i y - v i y < v' i (f v) - v i (f v)) → f v' = f v

private theorem pad_range_of_isWeaklyMonotoneOn [Finite ι] [DecidableEq ι]
    {f : (ι → Ω → ℝ) → Ω} {V : ι → Set (Ω → ℝ)} (hf : IsWeaklyMonotoneOn f V)
    {v v' : ι → Ω → ℝ} (hv : ∀ i, v i ∈ V i) (hv' : ∀ i, v' i ∈ V i)
    (hinc : ∀ i, ∀ y ∈ Set.range f, y ≠ f v → v' i y - v i y < v' i (f v) - v i (f v)) :
    f v' = f v := by
  have := Fintype.ofFinite ι
  let hybrid (S : Finset ι) (j : ι) : Ω → ℝ := if j ∈ S then v' j else v j
  have hhyb : ∀ S : Finset ι, f (hybrid S) = f v := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have : hybrid ∅ = v :=
        funext fun j => by simp only [hybrid, Finset.notMem_empty, ↓reduceIte]
      rw [this]
    | @insert i S hi ih =>
      have hdom : ∀ j, j ≠ i → hybrid S j ∈ V j := fun j _ => by
        by_cases hj : j ∈ S
        · simp only [hybrid, hj, ↓reduceIte]; exact hv' j
        · simp only [hybrid, hj, ↓reduceIte]; exact hv j
      have h1 : Function.update (hybrid S) i (v i) = hybrid S := by
        ext j ω
        by_cases hji : j = i
        · subst hji; simp only [Function.update_self, hybrid, hi, ↓reduceIte]
        · rw [Function.update_of_ne hji]
      have h2 : Function.update (hybrid S) i (v' i) = hybrid (insert i S) := by
        ext j ω
        by_cases hji : j = i
        · subst hji; simp only [Function.update_self, hybrid, Finset.mem_insert_self, ↓reduceIte]
        · rw [Function.update_of_ne hji]
          simp only [hybrid, Finset.mem_insert, hji, false_or]
      by_contra hne
      have hw := hf i (hybrid S) (v i) (v' i) hdom (hv i) (hv' i)
      rw [h1, h2, ih] at hw
      have hstr := hinc i (f (hybrid (insert i S))) (Set.mem_range_self _) hne
      linarith
  have huniv : hybrid Finset.univ = v' :=
    funext fun j => by simp only [hybrid, Finset.mem_univ, ↓reduceIte]
  rw [← huniv]
  exact hhyb Finset.univ

/-- **Weak monotonicity implies PAD** ([Lavi2007], Claim 12.28, §12.4, p. 318): with finitely many
agents, every weakly monotone (hence every DSIC-implementable) rule on any domain `V` satisfies
positive association of differences. -/
theorem IsWeaklyMonotoneOn.isPADOn [Finite ι] [DecidableEq ι] {f : (ι → Ω → ℝ) → Ω}
    {V : ι → Set (Ω → ℝ)} (hf : IsWeaklyMonotoneOn f V) : IsPADOn f V :=
  fun _ _ hv hv' hinc =>
    pad_range_of_isWeaklyMonotoneOn hf hv hv' fun i y _ hy => hinc i y hy

/-- **Generalized weak monotonicity (Generalized-WMON)** on domains `V` ([Lavi2007],
Definition 12.29, §12.4, pp. 318–319): whenever `f v ≠ f v'` for profiles `v, v'` in `V`, some
agent `i` satisfies `v' i (f v) - v i (f v) ≤ v' i (f v') - v i (f v')`. The guard `f v ≠ f v'`
is automatic when `ι` is nonempty (since `f v = f v'` holds by reflexivity for any `i`). -/
@[expose] def IsGeneralizedWMONOn (f : (ι → Ω → ℝ) → Ω) (V : ι → Set (Ω → ℝ)) : Prop :=
  ∀ (v v' : ι → Ω → ℝ), (∀ i, v i ∈ V i) → (∀ i, v' i ∈ V i) →
    f v ≠ f v' → ∃ i, v' i (f v) - v i (f v) ≤ v' i (f v') - v i (f v')

/-- **PAD implies Generalized-WMON on the unrestricted domain** ([Lavi2007], Claim 12.30, §12.4,
p. 319): on `V i = Set.univ`, positive association of differences yields generalized weak
monotonicity. -/
theorem isGeneralizedWMON_of_isPAD {f : (ι → Ω → ℝ) → Ω}
    (hf : IsPADOn f (fun _ => Set.univ)) :
    IsGeneralizedWMONOn f (fun _ => Set.univ) := by
  classical
  intro v v' _ _ hne
  by_contra hcon
  push Not at hcon
  set x := f v
  set y := f v'
  have hxy : x ≠ y := hne
  let Δ : ι → ℝ := fun i => (v' i x - v' i y) - (v i x - v i y)
  have hΔ : ∀ i, 0 < Δ i := fun i => by
    have := hcon i
    change v' i y - v i y < v' i x - v i x at this
    simp only [Δ]
    linarith
  let v'' : ι → Ω → ℝ := fun i z =>
    if z = x then v i x + Δ i / 2
    else if z = y then v i y
    else min (v i z + Δ i / 2) (v' i z + (v i y - v' i y)) - 1
  have hfx : f v'' = x :=
    hf v v'' (fun _ => Set.mem_univ _) (fun _ => Set.mem_univ _) fun i z hz => by
      change z ≠ x at hz
      have hvx : v'' i x = v i x + Δ i / 2 := by simp only [v'', ↓reduceIte]
      rw [hvx]
      by_cases hzy : z = y
      · have hvy : v'' i z = v i z := by
          rw [hzy]
          simp only [v'', hxy.symm, ↓reduceIte]
        rw [hvy]
        linarith [hΔ i]
      · have hvz : v'' i z = min (v i z + Δ i / 2) (v' i z + (v i y - v' i y)) - 1 := by
          simp only [v'', hz, hzy, ↓reduceIte]
        rw [hvz]
        linarith [min_le_left (v i z + Δ i / 2) (v' i z + (v i y - v' i y))]
  have hfy : f v'' = y :=
    hf v' v'' (fun _ => Set.mem_univ _) (fun _ => Set.mem_univ _) fun i z hz => by
      change z ≠ y at hz
      have hvy : v'' i y = v i y := by simp only [v'', hxy.symm, ↓reduceIte]
      rw [hvy]
      by_cases hzx : z = x
      · have hvx : v'' i z = v i z + Δ i / 2 := by
          rw [hzx]
          simp only [v'', ↓reduceIte]
        rw [hvx, hzx]
        have hdef : Δ i = (v' i x - v' i y) - (v i x - v i y) := rfl
        linarith [hΔ i, hdef]
      · have hvz : v'' i z = min (v i z + Δ i / 2) (v' i z + (v i y - v' i y)) - 1 := by
          simp only [v'', hzx, hz, ↓reduceIte]
        rw [hvz]
        linarith [min_le_right (v i z + Δ i / 2) (v' i z + (v i y - v' i y))]
  exact hxy (hfx.symm.trans hfy)

/-- On the unrestricted domain `ℝ^Ω` with finitely many agents, every weakly monotone rule satisfies
Generalized-WMON ([Lavi2007], Claim 12.30, §12.4, p. 319). -/
theorem IsWeaklyMonotone.isGeneralizedWMONOn [Finite ι] [DecidableEq ι] {f : (ι → Ω → ℝ) → Ω}
    (hf : IsWeaklyMonotone f) : IsGeneralizedWMONOn f (fun _ => Set.univ) :=
  isGeneralizedWMON_of_isPAD (isWeaklyMonotoneOn_univ_iff.2 hf).isPADOn

/-! ### Difference sets and shift proof (Lavi 2007, Claims 12.31–12.34 & Exercise 12.8) -/

private def diffSet (f : (ι → Ω → ℝ) → Ω) (x y : Ω) : Set (ι → ℝ) :=
  {α | ∃ v : ι → Ω → ℝ, (∀ i, v i x - v i y = α i) ∧ f v = x}

private noncomputable def gamma [DecidableEq Ω] (f : (ι → Ω → ℝ) → Ω) (x y : Ω) : ℝ :=
  if x = y then 0 else sInf {p : ℝ | (fun _ : ι => p) ∈ diffSet f x y}

private theorem nonempty_of_surjective_of_two_le_card [Fintype Ω] {f : (ι → Ω → ℝ) → Ω}
    (hf : Function.Surjective f) (hcard : 2 ≤ Fintype.card Ω) : Nonempty ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.1 (by omega : 1 < Fintype.card Ω)
  obtain ⟨va, hva⟩ := hf a
  obtain ⟨vb, hvb⟩ := hf b
  have heq : va = vb := funext fun i => (IsEmpty.false i).elim
  exact hab (by rw [← hva, ← hvb, heq])

private theorem exists_ne_pair [Fintype Ω] (hcard : 3 ≤ Fintype.card Ω)
    (x y : Ω) : ∃ z : Ω, z ≠ x ∧ z ≠ y := by
  classical
  have hlt : ({x, y} : Finset Ω).card < (Finset.univ : Finset Ω).card := by
    have h2 : ({x, y} : Finset Ω).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ]
    omega
  obtain ⟨z, _, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨z, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hz⟩

private theorem diffSet_nonempty {f : (ι → Ω → ℝ) → Ω}
    (hf_onto : Function.Surjective f) (x y : Ω) : (diffSet f x y).Nonempty := by
  obtain ⟨v, hv⟩ := hf_onto x
  exact ⟨fun i => v i x - v i y, v, fun _ => rfl, hv⟩

private theorem diffSet_upward {f : (ι → Ω → ℝ) → Ω}
    (hpad : IsPADOn f (fun _ => Set.univ)) {x y : Ω} (hxy : x ≠ y)
    {α β : ι → ℝ} (hα : α ∈ diffSet f x y) (hlt : ∀ i, α i < β i) :
    β ∈ diffSet f x y := by
  classical
  obtain ⟨v, hdiff, hfx⟩ := hα
  let v' : ι → Ω → ℝ := fun i z => if z = x then v i x + (β i - α i) else v i z
  have hfv' : f v' = x := by
    rw [← hfx]
    refine hpad v v' (fun _ => Set.mem_univ _) (fun _ => Set.mem_univ _) fun i z hz => ?_
    rw [hfx] at hz ⊢
    simp only [v', hz, ↓reduceIte]
    linarith [hlt i]
  refine ⟨v', fun i => ?_, hfv'⟩
  simp only [v', hxy.symm, ↓reduceIte]
  linarith [hdiff i]

/-- Contrapositive core behind Claim 12.31(i) ([Lavi2007], p. 319). -/
private theorem exists_add_nonneg_of_mem_diffSet {f : (ι → Ω → ℝ) → Ω}
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ)) {x y : Ω} (hxy : x ≠ y)
    {α β : ι → ℝ} (hα : α ∈ diffSet f x y) (hβ : β ∈ diffSet f y x) :
    ∃ i, 0 ≤ α i + β i := by
  obtain ⟨u, hud, hfu⟩ := hα
  obtain ⟨v, hvd, hfv⟩ := hβ
  have hne : f u ≠ f v := by rw [hfu, hfv]; exact hxy
  obtain ⟨i, hi⟩ := hgw u v (fun _ => Set.mem_univ _) (fun _ => Set.mem_univ _) hne
  rw [hfu, hfv] at hi
  refine ⟨i, ?_⟩
  linarith [hud i, hvd i]

/-- Claim 12.31(ii) ([Lavi2007], p. 319): `α ∉ P(x, y) → -α ∈ P(y, x)`. -/
private theorem neg_mem_diffSet_of_notMem {f : (ι → Ω → ℝ) → Ω}
    (hf_onto : Function.Surjective f) (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ))
    {x y : Ω} (hxy : x ≠ y) {α : ι → ℝ} (hα : α ∉ diffSet f x y) :
    -α ∈ diffSet f y x := by
  classical
  choose β hβ using fun z : Ω => diffSet_nonempty hf_onto x z
  let v : ι → Ω → ℝ := fun i z =>
    if z = x then α i
    else if z = y then 0
    else α i - (β z i + 1)
  have hnotz : ∀ z, z ≠ x → z ≠ y → f v ≠ z := by
    intro z hzx hzy hfz
    have hmem : (fun i => v i z - v i x) ∈ diffSet f z x := ⟨v, fun _ => rfl, hfz⟩
    obtain ⟨i, hi⟩ := exists_add_nonneg_of_mem_diffSet hgw hzx (hmem) (hβ z)
    simp only [v, hzx, hzy, ↓reduceIte] at hi
    linarith
  have hnotx : f v ≠ x := by
    intro hfx
    apply hα
    refine ⟨v, fun i => ?_, hfx⟩
    simp only [v, hxy.symm, ↓reduceIte, sub_zero]
  have hfy : f v = y := by
    by_contra hne
    exact hnotz (f v) hnotx hne rfl
  refine ⟨v, fun i => ?_, hfy⟩
  simp only [v, hxy.symm, ↓reduceIte, Pi.neg_apply, zero_sub]

/-- Claim 12.32 ([Lavi2007], p. 319): strict triangle/addition law for `P`. -/
private theorem add_shift_mem_diffSet {f : (ι → Ω → ℝ) → Ω}
    (hf_onto : Function.Surjective f) (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ))
    {x y z : Ω} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    {α β : ι → ℝ} (hα : α ∈ diffSet f x y) (hβ : β ∈ diffSet f y z)
    {δ : ℝ} (hδ : 0 < δ) :
    (fun i => α i + β i + δ) ∈ diffSet f x z := by
  classical
  choose η hη using fun w : Ω => diffSet_nonempty hf_onto x w
  let v : ι → Ω → ℝ := fun i w =>
    if w = x then α i + β i + δ
    else if w = y then β i + δ / 2
    else if w = z then 0
    else (α i + β i + δ) - (η w i + 1)
  have hnoty : f v ≠ y := by
    intro hfy
    obtain ⟨i, hi⟩ := exists_add_nonneg_of_mem_diffSet hgw hxy hα ⟨v, fun _ => rfl, hfy⟩
    simp only [v, hxy.symm, ↓reduceIte] at hi
    linarith
  have hnotz : f v ≠ z := by
    intro hfz
    obtain ⟨i, hi⟩ := exists_add_nonneg_of_mem_diffSet hgw hyz hβ ⟨v, fun _ => rfl, hfz⟩
    simp only [v, hxy.symm, hxz.symm, hyz.symm, ↓reduceIte] at hi
    linarith
  have hnotw : ∀ w, w ≠ x → w ≠ y → w ≠ z → f v ≠ w := by
    intro w hwx hwy hwz hfw
    obtain ⟨i, hi⟩ := exists_add_nonneg_of_mem_diffSet hgw hwx ⟨v, fun _ => rfl, hfw⟩ (hη w)
    simp only [v, hwx, hwy, hwz, ↓reduceIte] at hi
    linarith
  have hfx : f v = x := by
    by_contra hne
    exact hnotw (f v) hne hnoty hnotz rfl
  refine ⟨v, fun i => ?_, hfx⟩
  simp only [v, hxz.symm, hyz.symm, ↓reduceIte, sub_zero]

private theorem gammaSet_nonempty [Finite ι] [Nonempty ι]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hpad : IsPADOn f (fun _ => Set.univ)) {x y : Ω} (hxy : x ≠ y) :
    {p : ℝ | (fun _ : ι => p) ∈ diffSet f x y}.Nonempty := by
  have := Fintype.ofFinite ι
  obtain ⟨α, hα⟩ := diffSet_nonempty hf_onto x y
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty α + 1
  refine ⟨M, diffSet_upward hpad hxy hα fun i => ?_⟩
  have hle : α i ≤ Finset.univ.sup' Finset.univ_nonempty α :=
    Finset.le_sup' α (Finset.mem_univ i)
  linarith

private theorem gammaSet_bddBelow [Finite ι] [Nonempty ι]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ)) {x y : Ω} (hxy : x ≠ y) :
    BddBelow {p : ℝ | (fun _ : ι => p) ∈ diffSet f x y} := by
  have := Fintype.ofFinite ι
  obtain ⟨β, hβ⟩ := diffSet_nonempty hf_onto y x
  refine ⟨Finset.univ.inf' Finset.univ_nonempty (fun i => -β i), fun p hp => ?_⟩
  obtain ⟨i, hi⟩ := exists_add_nonneg_of_mem_diffSet hgw hxy hp hβ
  have hle : Finset.univ.inf' Finset.univ_nonempty (fun i => -β i) ≤ -β i :=
    Finset.inf'_le (fun i => -β i) (Finset.mem_univ i)
  linarith

private theorem const_mem_diffSet_of_gamma_lt [Finite ι] [Nonempty ι] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hpad : IsPADOn f (fun _ => Set.univ)) {x y : Ω} (hxy : x ≠ y)
    {p : ℝ} (hp : gamma f x y < p) :
    (fun _ : ι => p) ∈ diffSet f x y := by
  simp only [gamma, hxy, ↓reduceIte] at hp
  obtain ⟨q, hq, hqp⟩ := exists_lt_of_csInf_lt (gammaSet_nonempty hf_onto hpad hxy) hp
  exact diffSet_upward hpad hxy hq fun _ => hqp

private theorem const_notMem_diffSet_of_lt_gamma [Finite ι] [Nonempty ι] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ)) {x y : Ω} (hxy : x ≠ y)
    {p : ℝ} (hp : p < gamma f x y) :
    (fun _ : ι => p) ∉ diffSet f x y := fun hmem => by
  have hle : gamma f x y ≤ p := by
    simp only [gamma, hxy, ↓reduceIte]
    exact csInf_le (gammaSet_bddBelow hf_onto hgw hxy) hmem
  linarith

private theorem gamma_neg [Finite ι] [Nonempty ι] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hpad : IsPADOn f (fun _ => Set.univ))
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ)) (x y : Ω) :
    gamma f x y = -gamma f y x := by
  by_cases hxy : x = y
  · subst hxy; simp [gamma]
  · refine le_antisymm ?_ ?_
    · refine le_of_forall_pos_le_add fun ε hε => ?_
      have hnot : (fun _ : ι => gamma f y x - ε) ∉ diffSet f y x :=
        const_notMem_diffSet_of_lt_gamma hf_onto hgw (Ne.symm hxy) (by linarith)
      have hmem := neg_mem_diffSet_of_notMem hf_onto hgw (Ne.symm hxy) hnot
      have hmem' : (fun _ : ι => -gamma f y x + ε) ∈ diffSet f x y := by
        convert hmem using 1
        ext _; simp only [Pi.neg_apply]; ring
      have hle : gamma f x y ≤ -gamma f y x + ε := by
        simp only [gamma, hxy, ↓reduceIte]
        exact csInf_le (gammaSet_bddBelow hf_onto hgw hxy) hmem'
      exact hle
    · have hnonneg : 0 ≤ gamma f x y + gamma f y x := by
        by_contra hlt
        push Not at hlt
        have hε : 0 < -(gamma f x y + gamma f y x) / 4 := by linarith
        have h1 := const_mem_diffSet_of_gamma_lt hf_onto hpad hxy
          (p := gamma f x y + -(gamma f x y + gamma f y x) / 4) (by linarith)
        have h2 := const_mem_diffSet_of_gamma_lt hf_onto hpad (Ne.symm hxy)
          (p := gamma f y x + -(gamma f x y + gamma f y x) / 4) (by linarith)
        obtain ⟨_, hi⟩ := exists_add_nonneg_of_mem_diffSet hgw hxy h1 h2
        linarith
      linarith

private theorem gamma_add_le [Finite ι] [Nonempty ι] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hpad : IsPADOn f (fun _ => Set.univ))
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ)) (x y z : Ω) :
    gamma f x z ≤ gamma f x y + gamma f y z := by
  by_cases hxy : x = y
  · subst hxy; simp [gamma]
  by_cases hyz : y = z
  · subst hyz; simp [gamma]
  by_cases hxz : x = z
  · subst hxz; rw [gamma_neg hf_onto hpad hgw y x]; simp [gamma]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h1 := const_mem_diffSet_of_gamma_lt hf_onto hpad hxy (p := gamma f x y + ε / 3)
    (by linarith)
  have h2 := const_mem_diffSet_of_gamma_lt hf_onto hpad hyz (p := gamma f y z + ε / 3)
    (by linarith)
  have h3 := add_shift_mem_diffSet hf_onto hgw hxy hyz hxz h1 h2 (δ := ε / 3) (by linarith)
  have h3' : (fun _ : ι => gamma f x y + gamma f y z + ε) ∈ diffSet f x z := by
    convert h3 using 1; ext _; ring
  simp only [gamma, hxz, ↓reduceIte]
  exact csInf_le (gammaSet_bddBelow hf_onto hgw hxz) h3'

private theorem gamma_add [Finite ι] [Nonempty ι] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hpad : IsPADOn f (fun _ => Set.univ))
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ)) (x y z : Ω) :
    gamma f x z = gamma f x y + gamma f y z := by
  refine le_antisymm (gamma_add_le hf_onto hpad hgw x y z) ?_
  have h := gamma_add_le hf_onto hpad hgw z y x
  rw [gamma_neg hf_onto hpad hgw z x, gamma_neg hf_onto hpad hgw z y,
    gamma_neg hf_onto hpad hgw y x] at h
  linarith

private def openShifted [DecidableEq Ω] (f : (ι → Ω → ℝ) → Ω) (x y : Ω) : Set (ι → ℝ) :=
  {α | ∃ ε : ℝ, 0 < ε ∧ (fun i => α i + gamma f x y - ε) ∈ diffSet f x y}

private theorem openShifted_trans_add [Finite ι] [Nonempty ι] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hpad : IsPADOn f (fun _ => Set.univ))
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ))
    {x y z : Ω} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    {α β : ι → ℝ} (hα : α ∈ openShifted f x y) (hβ : β ∈ openShifted f y z) :
    α + β ∈ openShifted f x z := by
  obtain ⟨ε₁, hε₁, hmem₁⟩ := hα
  obtain ⟨ε₂, hε₂, hmem₂⟩ := hβ
  have htri := add_shift_mem_diffSet hf_onto hgw hxy hyz hxz hmem₁ hmem₂
    (δ := (ε₁ + ε₂) / 2) (by linarith)
  refine ⟨(ε₁ + ε₂) / 2, by linarith, ?_⟩
  convert htri using 1
  ext i
  rw [gamma_add hf_onto hpad hgw x y z]
  simp only [Pi.add_apply]
  ring

private theorem const_pos_mem_openShifted [Finite ι] [Nonempty ι] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hpad : IsPADOn f (fun _ => Set.univ)) {x y : Ω} (hxy : x ≠ y)
    {r : ℝ} (hr : 0 < r) : (fun _ : ι => r) ∈ openShifted f x y := by
  refine ⟨r / 2, by linarith, ?_⟩
  convert const_mem_diffSet_of_gamma_lt hf_onto hpad hxy (p := gamma f x y + r / 2) (by linarith)
    using 1
  ext _
  ring

private theorem openShifted_subset_right [Finite ι] [Nonempty ι] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hpad : IsPADOn f (fun _ => Set.univ))
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ))
    {x y z : Ω} (hxy : x ≠ y) (hxz : x ≠ z) :
    openShifted f x y ⊆ openShifted f x z := by
  by_cases hyz : y = z
  · subst hyz; exact Set.Subset.rfl
  rintro α ⟨ε, hε, hmem⟩
  have hα' : (fun i => α i - ε / 2) ∈ openShifted f x y :=
    ⟨ε / 2, by linarith, by convert hmem using 1; ext _; ring⟩
  have hc := const_pos_mem_openShifted hf_onto hpad hyz (r := ε / 2) (by linarith)
  simpa only [show (fun i => α i - ε / 2) + (fun _ => ε / 2) = α by ext _; simp] using
    openShifted_trans_add hf_onto hpad hgw hxy hyz hxz hα' hc

private theorem openShifted_subset_left [Finite ι] [Nonempty ι] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hpad : IsPADOn f (fun _ => Set.univ))
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ))
    {w x y : Ω} (hwy : w ≠ y) (hxy : x ≠ y) :
    openShifted f x y ⊆ openShifted f w y := by
  by_cases hwx : w = x
  · subst hwx; exact Set.Subset.rfl
  rintro α ⟨ε, hε, hmem⟩
  have hc := const_pos_mem_openShifted hf_onto hpad hwx (r := ε / 2) (by linarith)
  have hα' : (fun i => α i - ε / 2) ∈ openShifted f x y :=
    ⟨ε / 2, by linarith, by convert hmem using 1; ext _; ring⟩
  simpa only [show (fun _ => ε / 2) + (fun i => α i - ε / 2) = α by ext _; simp] using
    openShifted_trans_add hf_onto hpad hgw hwx hxy hwy hc hα'

private theorem openShifted_eq [Finite ι] [Nonempty ι] [Fintype Ω] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hpad : IsPADOn f (fun _ => Set.univ))
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ))
    (hcard : 3 ≤ Fintype.card Ω) {x y w z : Ω} (hxy : x ≠ y) (hwz : w ≠ z) :
    openShifted f x y = openShifted f w z := by
  have hright : ∀ a b c : Ω, a ≠ b → a ≠ c → openShifted f a b = openShifted f a c :=
    fun a b c hab hac => le_antisymm
      (openShifted_subset_right hf_onto hpad hgw hab hac)
      (openShifted_subset_right hf_onto hpad hgw hac hab)
  have hleft : ∀ a b c : Ω, a ≠ c → b ≠ c → openShifted f a c = openShifted f b c :=
    fun a b c hac hbc => le_antisymm
      (openShifted_subset_left hf_onto hpad hgw hbc hac)
      (openShifted_subset_left hf_onto hpad hgw hac hbc)
  by_cases hxz : x = z
  · subst hxz
    by_cases hwy : w = y
    · subst hwy
      obtain ⟨u, hux, huy⟩ := exists_ne_pair hcard x w
      exact (hright x w u hxy hux.symm).trans
        ((hleft x w u hux.symm huy.symm).trans (hright w u x huy.symm hwz))
    · exact (hleft x w y hxy hwy).trans (hright w y x hwy hwz)
  · exact (hright x y z hxy hxz).trans (hleft x w z hxz hwz)

private theorem openShifted_isOpen [Finite ι] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hpad : IsPADOn f (fun _ => Set.univ))
    {x y : Ω} (hxy : x ≠ y) : IsOpen (openShifted f x y) := by
  rw [isOpen_iff_forall_mem_open]
  rintro α ⟨ε, hε, hmem⟩
  refine ⟨Set.pi Set.univ fun i => Set.Ioi (α i - ε / 2), ?_, ?_, ?_⟩
  · intro β hβ
    refine ⟨ε / 2, by linarith, diffSet_upward hpad hxy hmem fun i => ?_⟩
    have hi : α i - ε / 2 < β i := hβ i (Set.mem_univ i)
    linarith
  · exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi
  · intro i _
    simp only [Set.mem_Ioi]
    linarith

private theorem openShifted_upward [DecidableEq Ω] {f : (ι → Ω → ℝ) → Ω}
    (hpad : IsPADOn f (fun _ => Set.univ)) {x y : Ω} (hxy : x ≠ y)
    {α β : ι → ℝ} (hα : α ∈ openShifted f x y) (hle : ∀ i, α i ≤ β i) :
    β ∈ openShifted f x y := by
  obtain ⟨ε, hε, hmem⟩ := hα
  refine ⟨ε / 2, by linarith, diffSet_upward hpad hxy hmem fun i => ?_⟩
  linarith [hle i]

private theorem openShifted_add [Finite ι] [Nonempty ι] [Fintype Ω] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hpad : IsPADOn f (fun _ => Set.univ))
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ))
    (hcard : 3 ≤ Fintype.card Ω) {x₀ y₀ : Ω} (hxy : x₀ ≠ y₀)
    {α β : ι → ℝ} (hα : α ∈ openShifted f x₀ y₀) (hβ : β ∈ openShifted f x₀ y₀) :
    α + β ∈ openShifted f x₀ y₀ := by
  obtain ⟨z₀, hzx, hzy⟩ := exists_ne_pair hcard x₀ y₀
  have hβ' : β ∈ openShifted f y₀ z₀ := by
    rwa [openShifted_eq hf_onto hpad hgw hcard hxy hzy.symm] at hβ
  have hmem_sum := openShifted_trans_add hf_onto hpad hgw hxy hzy.symm hzx.symm hα hβ'
  rwa [openShifted_eq hf_onto hpad hgw hcard hxy hzx.symm]

private theorem openShifted_half [Finite ι] [Nonempty ι] [Fintype Ω] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hpad : IsPADOn f (fun _ => Set.univ))
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ))
    (hcard : 3 ≤ Fintype.card Ω) {x₀ y₀ : Ω} (hxy : x₀ ≠ y₀)
    {α : ι → ℝ} (hα : α ∈ openShifted f x₀ y₀) :
    ((1 / 2 : ℝ) • α) ∈ openShifted f x₀ y₀ := by
  by_contra hnot
  obtain ⟨ε, hε, hmem⟩ := hα
  have hnot_diff : (fun i => α i / 2 + gamma f x₀ y₀ - ε / 8) ∉ diffSet f x₀ y₀ := by
    intro h
    exact hnot ⟨ε / 8, by linarith, by
      convert h using 1; ext i; simp only [Pi.smul_apply, smul_eq_mul]; ring⟩
  have hneg := neg_mem_diffSet_of_notMem hf_onto hgw hxy hnot_diff
  have h2 : (fun i => -α i / 2 + ε / 4) ∈ openShifted f y₀ x₀ := by
    refine ⟨ε / 8, by linarith, ?_⟩
    convert hneg using 1
    ext i
    simp only [Pi.neg_apply]
    rw [gamma_neg hf_onto hpad hgw y₀ x₀]
    ring
  rw [openShifted_eq hf_onto hpad hgw hcard hxy.symm hxy] at h2
  have h1 : (fun i => α i - ε / 2) ∈ openShifted f x₀ y₀ := by
    refine ⟨ε / 2, by linarith, ?_⟩
    convert hmem using 1; ext i; ring
  have hsum := openShifted_add hf_onto hpad hgw hcard hxy h1 h2
  have hlt : ∀ i, ((fun i => α i - ε / 2) + (fun i => -α i / 2 + ε / 4)) i ≤
      ((1 / 2 : ℝ) • α) i := fun i => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  exact hnot (openShifted_upward hpad hxy hsum hlt)

private theorem openShifted_smul_pos [Finite ι] [Nonempty ι] [Fintype Ω] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hpad : IsPADOn f (fun _ => Set.univ))
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ))
    (hcard : 3 ≤ Fintype.card Ω) {x₀ y₀ : Ω} (hxy : x₀ ≠ y₀)
    {α : ι → ℝ} (hα : α ∈ openShifted f x₀ y₀) {t : ℝ} (ht : 0 < t) :
    t • α ∈ openShifted f x₀ y₀ := by
  have := Fintype.ofFinite ι
  have hnsmul : ∀ (n : ℕ) (β : ι → ℝ), 0 < n → β ∈ openShifted f x₀ y₀ →
      (n : ℝ) • β ∈ openShifted f x₀ y₀ := by
    intro n β hn hβ
    induction n with
    | zero => omega
    | succ k ih =>
      rcases k with _ | k
      · simpa using hβ
      · have hsucc : ((k + 2 : ℕ) : ℝ) • β = ((k + 1 : ℕ) : ℝ) • β + β := by
          ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_add,
            Nat.cast_one]; ring
        rw [hsucc]
        exact openShifted_add hf_onto hpad hgw hcard hxy (ih (by omega)) hβ
  have hpow : ∀ (m : ℕ) (β : ι → ℝ), β ∈ openShifted f x₀ y₀ →
      ((1 / 2 : ℝ) ^ m) • β ∈ openShifted f x₀ y₀ := by
    intro m β hβ
    induction m with
    | zero => simpa using hβ
    | succ m ih =>
      have heq : ((1 / 2 : ℝ) ^ (m + 1)) • β = (1 / 2 : ℝ) • (((1 / 2 : ℝ) ^ m) • β) := by
        rw [smul_smul, pow_succ']
      rw [heq]
      exact openShifted_half hf_onto hpad hgw hcard hxy ih
  obtain ⟨ε, hε, hmem⟩ := hα
  let r : ℝ := ε / 2
  have hr : 0 < r := half_pos hε
  let α' : ι → ℝ := fun i => α i - r
  have hα' : α' ∈ openShifted f x₀ y₀ := by
    refine ⟨ε / 2, by linarith, ?_⟩
    convert hmem using 1; ext i; simp only [α', r]; ring
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i => |α i|) + 1
  have hM : 0 < M := by
    have ⟨i₀⟩ := ‹Nonempty ι›
    have h0 : |α i₀| ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => |α i|) :=
      Finset.le_sup' (fun i => |α i|) (Finset.mem_univ i₀)
    have : 0 ≤ |α i₀| := abs_nonneg _
    change 0 < Finset.univ.sup' Finset.univ_nonempty (fun i => |α i|) + 1
    linarith
  have hM_le : ∀ i, |α i| ≤ M := fun i => by
    have h := Finset.le_sup' (fun i => |α i|) (Finset.mem_univ i)
    change |α i| ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => |α i|) + 1
    linarith
  let η : ℝ := min (t / 2) (t * r / (2 * M))
  have hη : 0 < η := lt_min (half_pos ht) (div_pos (mul_pos ht hr) (mul_pos two_pos hM))
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hη (by norm_num : (1 / 2 : ℝ) < 1)
  have h2m_pos : (0 : ℝ) < (2 : ℝ) ^ m := pow_pos (by norm_num) m
  have hinv : (1 / 2 : ℝ) ^ m = 1 / (2 : ℝ) ^ m := by rw [one_div, inv_pow, one_div]
  have hδ : 1 / (2 : ℝ) ^ m < η := by rwa [← hinv]
  set n : ℕ := ⌊t * (2 : ℝ) ^ m⌋₊
  set d : ℝ := (n : ℝ) / (2 : ℝ) ^ m
  have hdt_le : d ≤ t := by
    rw [div_le_iff₀ h2m_pos]
    exact Nat.floor_le (mul_nonneg ht.le h2m_pos.le)
  have hdt_lt : t - 1 / (2 : ℝ) ^ m < d := by
    have hfl : t * (2 : ℝ) ^ m < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2ne : (2 : ℝ) ^ m ≠ 0 := h2m_pos.ne'
    have hprod : (t - 1 / (2 : ℝ) ^ m) * (2 : ℝ) ^ m = t * (2 : ℝ) ^ m - 1 := by
      field_simp
    have : (t - 1 / (2 : ℝ) ^ m) * (2 : ℝ) ^ m < (n : ℝ) := by linarith
    exact (lt_div_iff₀ h2m_pos).2 this
  have htd_half : t / 2 < d := by
    have : 1 / (2 : ℝ) ^ m < t / 2 := lt_of_lt_of_le hδ (min_le_left _ _)
    linarith
  have hd_pos : 0 < d := by linarith
  have hn_pos : 0 < n := by
    by_contra h0
    have : n = 0 := by omega
    simp only [d, this, Nat.cast_zero, zero_div] at hd_pos
    linarith
  have hd_mem : d • α' ∈ openShifted f x₀ y₀ := by
    have heq : d • α' = ((1 / 2 : ℝ) ^ m) • ((n : ℝ) • α') := by
      rw [smul_smul, hinv]
      congr 1; simp only [d]; ring
    rw [heq]
    exact hpow m _ (hnsmul n α' hn_pos hα')
  refine openShifted_upward hpad hxy hd_mem fun i => ?_
  simp only [Pi.smul_apply, smul_eq_mul, α']
  have htd_nonneg : 0 ≤ t - d := by linarith
  have htd_lt_bound : t - d < t * r / (2 * M) := by
    have hη2 : η ≤ t * r / (2 * M) := min_le_right _ _
    linarith
  have habs_mul : (t - d) * |α i| ≤ t * r / 2 := by
    have h1 : (t - d) * |α i| ≤ (t - d) * M := mul_le_mul_of_nonneg_left (hM_le i) htd_nonneg
    have h2 : (t - d) * M ≤ (t * r / (2 * M)) * M :=
      mul_le_mul_of_nonneg_right htd_lt_bound.le hM.le
    have h3 : (t * r / (2 * M)) * M = t * r / 2 := by
      have hMne : M ≠ 0 := hM.ne'
      field_simp
    linarith
  have hlow : -(t - d) * |α i| ≤ (t - d) * α i := by
    have hneg : -|α i| ≤ α i := neg_abs_le (α i)
    calc
      -(t - d) * |α i| = (t - d) * (-|α i|) := by ring
      _ ≤ (t - d) * α i := mul_le_mul_of_nonneg_left hneg htd_nonneg
  have hdr : t * r / 2 ≤ d * r := by nlinarith
  linarith

private theorem openShifted_convex [Finite ι] [Nonempty ι] [Fintype Ω] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hpad : IsPADOn f (fun _ => Set.univ))
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ))
    (hcard : 3 ≤ Fintype.card Ω) {x₀ y₀ : Ω} (hxy : x₀ ≠ y₀) :
    Convex ℝ (openShifted f x₀ y₀) := by
  intro α hα β hβ a b ha hb hab
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hb1 : b = 1 := by linarith
    simpa [hb1] using hβ
  · rcases eq_or_lt_of_le hb with rfl | hb'
    · have ha1 : a = 1 := by linarith
      simpa [ha1] using hα
    · exact openShifted_add hf_onto hpad hgw hcard hxy
        (openShifted_smul_pos hf_onto hpad hgw hcard hxy hα ha')
        (openShifted_smul_pos hf_onto hpad hgw hcard hxy hβ hb')

private theorem zero_notMem_openShifted [Finite ι] [Nonempty ι] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ))
    {x₀ y₀ : Ω} (hxy : x₀ ≠ y₀) : (0 : ι → ℝ) ∉ openShifted f x₀ y₀ := by
  rintro ⟨ε, hε, hmem⟩
  have hmem' : (fun _ : ι => gamma f x₀ y₀ - ε) ∈ diffSet f x₀ y₀ := by
    convert hmem using 1; ext i; simp
  exact const_notMem_diffSet_of_lt_gamma hf_onto hgw hxy (by linarith) hmem'

private theorem roberts_with_gamma [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hf_wmon : IsWeaklyMonotone f) (hcard : 3 ≤ Fintype.card Ω) (x₀ : Ω) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      IsAffineMaximizerFor f Set.univ w (fun x => gamma f x₀ x) := by
  have : Nonempty ι := nonempty_of_surjective_of_two_le_card hf_onto (by omega)
  have hpad : IsPADOn f (fun _ => Set.univ) :=
    (isWeaklyMonotoneOn_univ_iff.2 hf_wmon).isPADOn
  have hgw : IsGeneralizedWMONOn f (fun _ => Set.univ) :=
    isGeneralizedWMON_of_isPAD hpad
  obtain ⟨y₀, hy₀, _⟩ := exists_ne_pair hcard x₀ x₀
  have hxy : x₀ ≠ y₀ := hy₀.symm
  have hconv : Convex ℝ (openShifted f x₀ y₀) :=
    openShifted_convex hf_onto hpad hgw hcard hxy
  have hopen : IsOpen (openShifted f x₀ y₀) := openShifted_isOpen hpad hxy
  have hzero : (0 : ι → ℝ) ∉ openShifted f x₀ y₀ := zero_notMem_openShifted hf_onto hgw hxy
  obtain ⟨L, hL⟩ := geometric_hahn_banach_point_open hconv hopen hzero
  have hL_pos : ∀ α ∈ openShifted f x₀ y₀, 0 < L α := fun α hα => by
    have := hL α hα
    rwa [map_zero] at this
  let w₀ : ι → ℝ := fun i => L (Pi.single i 1)
  have hL_eq : ∀ α : ι → ℝ, L α = ∑ i, w₀ i * α i := fun α => by
    have hdecomp : α = ∑ i : ι, α i • Pi.single i (1 : ℝ) := by
      ext j
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq Finset.univ j α]
      simp only [Finset.mem_univ, ↓reduceIte]
    conv_lhs => rw [hdecomp]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have hone_mem : (fun _ : ι => (1 : ℝ)) ∈ openShifted f x₀ y₀ :=
    const_pos_mem_openShifted hf_onto hpad hxy zero_lt_one
  have hsum_pos : 0 < ∑ i, w₀ i := by
    have h := hL_pos (fun _ => 1) hone_mem
    rw [hL_eq] at h
    simpa only [mul_one] using h
  have hw₀_nonneg : ∀ i, 0 ≤ w₀ i := by
    intro i
    by_contra hneg
    push Not at hneg
    have hneg' : 0 < -w₀ i := by linarith
    let t : ℝ := (∑ j, w₀ j) / (-w₀ i) + 1
    have ht : 0 ≤ t := by
      have hdiv_nn : 0 ≤ (∑ j, w₀ j) / (-w₀ i) := div_nonneg hsum_pos.le hneg'.le
      change 0 ≤ (∑ j, w₀ j) / (-w₀ i) + 1
      linarith
    have hmem : (fun _ : ι => (1 : ℝ)) + t • Pi.single i (1 : ℝ) ∈ openShifted f x₀ y₀ := by
      refine openShifted_upward hpad hxy hone_mem fun j => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      split_ifs <;> linarith
    have hlt := hL_pos _ hmem
    rw [map_add, map_smul, smul_eq_mul, hL_eq] at hlt
    simp only [mul_one] at hlt
    have hwi_ne : w₀ i ≠ 0 := hneg.ne
    have hcalc : t * w₀ i = -(∑ j, w₀ j) + w₀ i := by
      change ((∑ j, w₀ j) / (-w₀ i) + 1) * w₀ i = -(∑ j, w₀ j) + w₀ i
      field_simp [hwi_ne]
    change 0 < ∑ j, w₀ j + t * w₀ i at hlt
    linarith
  let S : ℝ := ∑ i, w₀ i
  have hSne : S ≠ 0 := hsum_pos.ne'
  let w : ι → ℝ := fun i => w₀ i / S
  refine ⟨w, fun i => div_nonneg (hw₀_nonneg i) hsum_pos.le, ?_, fun b => ⟨Set.mem_univ _, ?_⟩⟩
  · have hmul : (∑ i, w i) * S = S := by
      simp only [w, Finset.sum_mul]
      calc
        ∑ i, w₀ i / S * S = ∑ i, w₀ i :=
          Finset.sum_congr rfl fun i _ => div_mul_cancel₀ _ hSne
        _ = S := rfl
    exact eq_of_sub_eq_zero (mul_right_cancel₀ hSne (by linarith))
  · intro y _
    set x := f b
    by_cases heq : y = x
    · subst heq; exact le_rfl
    have hdiff : (fun i => b i x - b i y) ∈ diffSet f x y := ⟨b, fun _ => rfl, rfl⟩
    have hnonneg : 0 ≤ ∑ i, w₀ i * ((b i x - b i y) - gamma f x y) := by
      by_contra hlt
      push Not at hlt
      let ε : ℝ := -(∑ i, w₀ i * ((b i x - b i y) - gamma f x y)) / (2 * S)
      have hε : 0 < ε := div_pos (by linarith) (mul_pos two_pos hsum_pos)
      let α : ι → ℝ := fun i => b i x - b i y - gamma f x y + ε
      have hα_xy : α ∈ openShifted f x y := by
        refine ⟨ε, hε, ?_⟩
        convert hdiff using 1; ext i; simp only [α]; ring
      have hα : α ∈ openShifted f x₀ y₀ := by
        rwa [openShifted_eq hf_onto hpad hgw hcard (Ne.symm heq) hxy] at hα_xy
      have hpos := hL_pos α hα
      rw [hL_eq] at hpos
      have hexp : ∑ i, w₀ i * α i =
          ∑ i, w₀ i * ((b i x - b i y) - gamma f x y) + ε * S := by
        simp only [α, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, S]
        ring
      have hεS : ε * S = -(∑ i, w₀ i * ((b i x - b i y) - gamma f x y)) / 2 := by
        change (-(∑ i, w₀ i * ((b i x - b i y) - gamma f x y)) / (2 * S)) * S = _
        field_simp [hSne]
      linarith
    have hdiv : 0 ≤ ∑ i, w i * (b i x - b i y) - gamma f x y := by
      refine nonneg_of_mul_nonneg_left ?_ hsum_pos
      have h1 : (∑ i, w i * (b i x - b i y) - gamma f x y) * S =
          ∑ i, w₀ i * ((b i x - b i y) - gamma f x y) := by
        rw [sub_mul, Finset.sum_mul]
        have hsum_eq : ∑ i, w i * (b i x - b i y) * S = ∑ i, w₀ i * (b i x - b i y) :=
          Finset.sum_congr rfl fun i _ => by
            simp only [w]
            rw [mul_right_comm, div_mul_cancel₀ _ hSne]
        rw [hsum_eq]
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, S]
        ring
      change 0 ≤ (∑ i, w i * (b i x - b i y) - gamma f x y) * S
      rw [h1]
      exact hnonneg
    have hcocycle : gamma f x y = gamma f x₀ y - gamma f x₀ x := by
      have h := gamma_add hf_onto hpad hgw x₀ x y
      linarith
    simp only [affineScore]
    have hsub : ∑ i, w i * (b i x - b i y) = ∑ i, w i * b i x - ∑ i, w i * b i y := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    linarith

/-! ### Headline theorems (Roberts' theorem and neutral Roberts' theorem) -/

/-- **Roberts' theorem (from weak monotonicity)** ([Nisan2007], Theorem 9.32, §9.5.3, p. 228;
[Lavi2007], Theorem 12.24, §12.4, p. 318; Exercise 12.8, p. 329): if there are finitely many agents
and finitely many outcomes with `3 ≤ |Ω|`, then every surjective weakly monotone outcome rule
`f : (ι → Ω → ℝ) → Ω` on the unrestricted domain `ℝ^Ω` is an affine maximizer over `Set.univ`
with nonnegative weights `w` summing to `1` (hence not all zero). -/
theorem exists_isAffineMaximizerFor_of_isWeaklyMonotone [Fintype ι] [DecidableEq ι]
    [Fintype Ω] {f : (ι → Ω → ℝ) → Ω} (hcard : 3 ≤ Fintype.card Ω)
    (hf_onto : Function.Surjective f) (hf_wmon : IsWeaklyMonotone f) :
    ∃ (w : ι → ℝ) (c : Ω → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ IsAffineMaximizerFor f Set.univ w c := by
  classical
  have : Nonempty Ω := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨x₀⟩ := ‹Nonempty Ω›
  obtain ⟨w, hw, hsum, hmax⟩ := roberts_with_gamma hf_onto hf_wmon hcard x₀
  exact ⟨w, fun x => gamma f x₀ x, hw, hsum, hmax⟩

/-- **Roberts' theorem** ([Nisan2007], Theorem 9.32, §9.5.3, p. 228; [Lavi2007], Theorem 12.24,
§12.4, p. 318): on the unrestricted domain `ℝ^Ω` with finitely many agents and `3 ≤ |Ω|`, every
surjective DSIC-implementable social choice function `f` is an affine maximizer over `Set.univ`
with nonnegative weights summing to `1` (`∃ i, 0 < w i`). -/
theorem exists_isAffineMaximizerFor_of_isImplementable [Fintype ι] [DecidableEq ι]
    [Fintype Ω] {f : (ι → Ω → ℝ) → Ω} (hcard : 3 ≤ Fintype.card Ω)
    (hf_onto : Function.Surjective f) (hf : IsImplementable f) :
    ∃ (w : ι → ℝ) (c : Ω → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ IsAffineMaximizerFor f Set.univ w c :=
  exists_isAffineMaximizerFor_of_isWeaklyMonotone hcard hf_onto hf.isWeaklyMonotone

/-- Bundled `IsAffineMaximizer` form of **Roberts' theorem** ([Nisan2007], Theorem 9.32, p. 228;
[Lavi2007], Theorem 12.24, p. 318) for a surjective DSIC-implementable rule. -/
theorem IsImplementable.isAffineMaximizer [Fintype ι] [DecidableEq ι]
    [Fintype Ω] {f : (ι → Ω → ℝ) → Ω} (hcard : 3 ≤ Fintype.card Ω)
    (hf_onto : Function.Surjective f) (hf : IsImplementable f) : IsAffineMaximizer f := by
  obtain ⟨w, c, hw, hsum, hmax⟩ := exists_isAffineMaximizerFor_of_isImplementable hcard hf_onto hf
  have hne : ∃ i, 0 < w i := by
    by_contra h
    push Not at h
    have h0 : ∑ i, w i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (h i) (hw i)
    linarith
  exact ⟨Set.univ, w, c, hw, hne, hmax⟩

/-- Mechanism form of **Roberts' theorem** ([Nisan2007], Theorem 9.32, p. 228): if `M` is DSIC on
the unrestricted domain `ℝ^Ω` with `3 ≤ |Ω|` and `M.outcome` is surjective, then `M.outcome` is an
affine maximizer. -/
theorem IsDSIC.isAffineMaximizer [Fintype ι] [DecidableEq ι] [Fintype Ω] {M : Mechanism ι Ω}
    (hcard : 3 ≤ Fintype.card Ω) (honto : Function.Surjective M.outcome) (hM : M.IsDSIC) :
    IsAffineMaximizer M.outcome :=
  IsImplementable.isAffineMaximizer hcard honto ⟨M.payment, hM⟩

/-- **Neutral Roberts' theorem (from weak monotonicity)** ([Lavi2007], Theorem 12.26, §12.4,
p. 318): if `3 ≤ |Ω|` and `f : (ι → Ω → ℝ) → Ω` is neutral (Definition 12.25) and weakly monotone,
then `f` maximizes a pure weighted sum `∑ i, w i * b i ω` (all additive outcome offsets are `0`)
with nonnegative weights `w` summing to `1`. -/
theorem exists_weightedWelfare_of_isNeutral_of_isWeaklyMonotone [Fintype ι] [DecidableEq ι]
    [Fintype Ω] {f : (ι → Ω → ℝ) → Ω} (hcard : 3 ≤ Fintype.card Ω)
    (hneut : IsNeutral f) (hf_wmon : IsWeaklyMonotone f) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      ∀ (b : ι → Ω → ℝ) (ω : Ω), ∑ i, w i * b i ω ≤ ∑ i, w i * b i (f b) := by
  classical
  have hf_onto : Function.Surjective f := hneut.surjective
  have : Nonempty ι := nonempty_of_surjective_of_two_le_card hf_onto (by omega)
  have : Nonempty Ω := Fintype.card_pos_iff.1 (by omega)
  have hpad : IsPADOn f (fun _ => Set.univ) :=
    (isWeaklyMonotoneOn_univ_iff.2 hf_wmon).isPADOn
  have hgw : IsGeneralizedWMONOn f (fun _ => Set.univ) :=
    isGeneralizedWMON_of_isPAD hpad
  have hgamma_le : ∀ x y : Ω, x ≠ y → gamma f x y ≤ 0 := fun x y hxy => by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    let v : ι → Ω → ℝ := fun _ z => if z = x then ε else if z = y then 0 else -1
    have hfv : f v = x := hneut v x fun _ z hz => by
      simp only [v, hz, ↓reduceIte]
      split_ifs <;> linarith
    have hmem : (fun _ : ι => ε) ∈ diffSet f x y := ⟨v, fun _ => by
      simp only [v, hxy.symm, ↓reduceIte, sub_zero], hfv⟩
    simp only [gamma, hxy, ↓reduceIte, zero_add]
    exact csInf_le (gammaSet_bddBelow hf_onto hgw hxy) hmem
  have hgamma_zero : ∀ x y : Ω, gamma f x y = 0 := fun x y => by
    by_cases hxy : x = y
    · subst hxy; simp [gamma]
    · have h1 := hgamma_le x y hxy
      have h2 := hgamma_le y x (Ne.symm hxy)
      rw [gamma_neg hf_onto hpad hgw y x] at h2
      linarith
  obtain ⟨x₀⟩ := ‹Nonempty Ω›
  obtain ⟨w, hw, hsum, hmax⟩ := roberts_with_gamma hf_onto hf_wmon hcard x₀
  refine ⟨w, hw, hsum, fun b ω => ?_⟩
  have h := (hmax b).2 ω (Set.mem_univ _)
  simpa only [affineScore, hgamma_zero, zero_add] using h

/-- **Neutral Roberts' theorem** ([Lavi2007], Theorem 12.26, §12.4, p. 318): every neutral,
DSIC-implementable rule on the unrestricted domain `ℝ^Ω` with `3 ≤ |Ω|` maximizes a pure
nonnegatively weighted welfare sum `∑ i, w i * b i ω` (`∑ i, w i = 1`, zero additive constants). -/
theorem exists_weightedWelfare_of_isNeutral_of_isImplementable [Fintype ι] [DecidableEq ι]
    [Fintype Ω] {f : (ι → Ω → ℝ) → Ω} (hcard : 3 ≤ Fintype.card Ω)
    (hneut : IsNeutral f) (hf : IsImplementable f) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      ∀ (b : ι → Ω → ℝ) (ω : Ω), ∑ i, w i * b i ω ≤ ∑ i, w i * b i (f b) :=
  exists_weightedWelfare_of_isNeutral_of_isWeaklyMonotone hcard hneut hf.isWeaklyMonotone

/-- **Roberts' theorem on a finite range (no surjectivity assumption)**: for an arbitrary outcome
type `Ω`, if `f : (ι → Ω → ℝ) → Ω` is weakly monotone (e.g., DSIC-implementable) and `Set.range f`
is finite with at least `3` elements, then `f` is an affine maximizer over `Set.range f` with
nonnegative weights summing to `1`. -/
theorem exists_isAffineMaximizerFor_range_of_isWeaklyMonotone [Fintype ι] [DecidableEq ι]
    {f : (ι → Ω → ℝ) → Ω} (hfin : (Set.range f).Finite) (hcard : 3 ≤ (Set.range f).ncard)
    (hf_wmon : IsWeaklyMonotone f) :
    ∃ (w : ι → ℝ) (c : Ω → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ IsAffineMaximizerFor f (Set.range f) w c := by
  classical
  let _ : Fintype (Set.range f) := hfin.fintype
  have hcardR : 3 ≤ Fintype.card (Set.range f) := by
    have heq : (Set.range f).ncard = Fintype.card (Set.range f) :=
      Set.ncard_eq_toFinset_card' (Set.range f) |>.trans (Set.toFinset_card _)
    omega
  let ext (u : ι → Set.range f → ℝ) : ι → Ω → ℝ :=
    fun i ω => if h : ω ∈ Set.range f then u i ⟨ω, h⟩ else 0
  let g : (ι → Set.range f → ℝ) → Set.range f := fun u => ⟨f (ext u), Set.mem_range_self _⟩
  have hpad : ∀ {v v' : ι → Ω → ℝ},
      (∀ i, ∀ y ∈ Set.range f, y ≠ f v → v' i y - v i y < v' i (f v) - v i (f v)) →
      f v' = f v := fun hinc =>
    pad_range_of_isWeaklyMonotoneOn (isWeaklyMonotoneOn_univ_iff.2 hf_wmon)
      (fun _ => Set.mem_univ _) (fun _ => Set.mem_univ _) hinc
  have hg_wmon : IsWeaklyMonotone g := by
    intro i u v v'
    let vv : Ω → ℝ := fun ω => if h : ω ∈ Set.range f then v ⟨ω, h⟩ else 0
    let vv' : Ω → ℝ := fun ω => if h : ω ∈ Set.range f then v' ⟨ω, h⟩ else 0
    have hu1 : ext (Function.update u i v) = Function.update (ext u) i vv := by
      ext j ω
      by_cases hji : j = i
      · subst hji; simp only [ext, Function.update_self, vv]
      · simp only [ext, Function.update_of_ne hji]
    have hu2 : ext (Function.update u i v') = Function.update (ext u) i vv' := by
      ext j ω
      by_cases hji : j = i
      · subst hji; simp only [ext, Function.update_self, vv']
      · simp only [ext, Function.update_of_ne hji]
    have hw := hf_wmon i (ext u) vv vv'
    rw [← hu1, ← hu2] at hw
    simpa only [g, vv, vv', Set.mem_range_self, ↓reduceDIte] using hw
  have hg_onto : Function.Surjective g := by
    rintro ⟨a, v, rfl⟩
    let u : ι → Set.range f → ℝ :=
      fun i r => if r.val = f v then v i r.val + 1 else v i r.val
    refine ⟨u, Subtype.ext ?_⟩
    exact hpad fun i y hy hyne => by
      simp only [ext, hy, Set.mem_range_self, ↓reduceDIte, u, hyne, ↓reduceIte]
      linarith
  obtain ⟨w, c', hw, hsum, hmax⟩ :=
    exists_isAffineMaximizerFor_of_isWeaklyMonotone hcardR hg_onto hg_wmon
  let c : Ω → ℝ := fun ω => if h : ω ∈ Set.range f then c' ⟨ω, h⟩ else 0
  refine ⟨w, c, hw, hsum, fun b => ⟨Set.mem_range_self b, fun y hy => ?_⟩⟩
  set x := f b
  by_cases hyx : y = x
  · subst hyx; exact le_rfl
  refine le_of_forall_pos_le_add fun ε hε => ?_
  let u : ι → Set.range f → ℝ :=
    fun i r => if r.val = x then b i x + ε else b i r.val
  have hfu : f (ext u) = x := hpad fun i z hz hzne => by
    change z ≠ x at hzne
    have hz_eq : ext u i z = b i z := by
      simp only [ext, hz, ↓reduceDIte, u, hzne, ↓reduceIte]
    have hx_eq : ext u i (f b) = b i x + ε := by
      simp only [ext, Set.mem_range_self b, ↓reduceDIte, u, x, ↓reduceIte]
    rw [hz_eq, hx_eq]
    change b i z - b i z < b i x + ε - b i x
    linarith
  have hgu : g u = ⟨x, Set.mem_range_self b⟩ := Subtype.ext hfu
  have hle := (hmax u).2 ⟨y, hy⟩ (Set.mem_univ _)
  rw [hgu] at hle
  have hcy : c y = c' ⟨y, hy⟩ := dite_eq_left hy
  have hcx : c x = c' ⟨x, Set.mem_range_self b⟩ := dite_eq_left (Set.mem_range_self b)
  have hs1 : ∑ i, w i * u i ⟨y, hy⟩ = ∑ i, w i * b i y :=
    Finset.sum_congr rfl fun i _ => by simp only [u, hyx, ↓reduceIte]
  have hs2 : ∑ i, w i * u i ⟨x, Set.mem_range_self b⟩ = ∑ i, w i * b i x + ε := by
    calc
      ∑ i, w i * u i ⟨x, Set.mem_range_self b⟩
          = ∑ i, (w i * b i x + w i * ε) :=
        Finset.sum_congr rfl fun i _ => by simp only [u, ↓reduceIte]; ring
      _ = ∑ i, w i * b i x + (∑ i, w i) * ε := by rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      _ = ∑ i, w i * b i x + ε := by rw [hsum, one_mul]
  change c y + ∑ i, w i * b i y ≤ c x + ∑ i, w i * b i x + ε
  simp only [affineScore] at hle
  rw [hcy, hcx]
  linarith

end Cslib.GameTheory.Mechanism
