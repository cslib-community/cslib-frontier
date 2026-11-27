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
  rfl

/-- Payment charged to agent `i` on reports `b` under `weightedGroves f w c h`. -/
@[simp] theorem weightedGroves_payment [Fintype ι] [DecidableEq ι]
    (f : (ι → Ω → ℝ) → Ω) (w : ι → ℝ) (c : Ω → ℝ) (h : ι → (ι → Ω → ℝ) → ℝ)
    (b : ι → Ω → ℝ) (i : ι) :
    (weightedGroves f w c h).payment b i =
      if w i = 0 then h i b
      else h i b - (∑ j ∈ Finset.univ.erase i, (w j / w i) * b j (f b) + c (f b) / w i) := by
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
      exact congrArg (· + c ω) (Finset.sum_congr rfl fun j _ => by
        rw [← mul_assoc, mul_div_cancel₀ _ hwi])
    refine le_of_mul_le_mul_left ?_ hpos
    simp only [utility, weightedGroves, hwi, ↓reduceIte, hh i b v, sum_erase_weighted_update]
    calc w i * (v (f b) - (h i b -
            (∑ j ∈ Finset.univ.erase i, (w j / w i) * b j (f b) + c (f b) / w i)))
      _ = w i * v (f b) - w i * h i b +
            (∑ j ∈ Finset.univ.erase i, w j * b j (f b) + c (f b)) := by
          rw [← hmul_eq]; ring
      _ ≤ w i * v (f (Function.update b i v)) - w i * h i b +
            (∑ j ∈ Finset.univ.erase i, w j * b j (f (Function.update b i v)) +
              c (f (Function.update b i v))) := by linarith
      _ = w i * (v (f (Function.update b i v)) - (h i b -
            (∑ j ∈ Finset.univ.erase i,
              (w j / w i) * b j (f (Function.update b i v)) +
                c (f (Function.update b i v)) / w i))) := by
          rw [← hmul_eq]; ring

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
  have hhyb : ∀ S : Finset ι, f (hybrid S) = f v := fun S => by
    induction S using Finset.induction_on with
    | empty => exact congrArg f (funext fun _ => by simp [hybrid])
    | @insert i S hi ih =>
      have hdom : ∀ j, j ≠ i → hybrid S j ∈ V j := fun j _ => by
        by_cases hj : j ∈ S <;> simp [hybrid, hj, hv' j, hv j]
      have h1 : Function.update (hybrid S) i (v i) = hybrid S :=
        Function.update_eq_self_iff.mpr (ite_eq_right hi).symm
      have h2 : Function.update (hybrid S) i (v' i) = hybrid (insert i S) :=
        funext fun j => by by_cases h : j = i <;> simp [h, hybrid]
      by_contra hne
      have hw := hf i (hybrid S) (v i) (v' i) hdom (hv i) (hv' i)
      rw [h1, h2, ih] at hw
      linarith [hinc i (f (hybrid (insert i S))) (Set.mem_range_self _) hne]
  exact (congrArg f (funext fun _ => by simp [hybrid])).symm.trans (hhyb Finset.univ)

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
  have hΔ : ∀ i, 0 < Δ i := fun i => by linarith [hcon i]
  let v'' : ι → Ω → ℝ := fun i z =>
    if z = x then v i x + Δ i / 2
    else if z = y then v i y
    else min (v i z + Δ i / 2) (v' i z + (v i y - v' i y)) - 1
  have hfx : f v'' = x :=
    hf v v'' (fun _ => trivial) (fun _ => trivial) fun i z hz => by
      dsimp only [v'', x, y] at hxy hz ⊢
      rcases eq_or_ne (f v') z with rfl | hzy
      · simp only [hxy.symm, ↓reduceIte]
        linarith [hΔ i]
      · simp only [hz, hzy.symm, ↓reduceIte]
        linarith [min_le_left (v i z + Δ i / 2) (v' i z + (v i (f v') - v' i (f v')))]
  have hfy : f v'' = y :=
    hf v' v'' (fun _ => trivial) (fun _ => trivial) fun i z hz => by
      dsimp only [v'', Δ, x, y] at hxy hz hΔ ⊢
      rcases eq_or_ne (f v) z with rfl | hzx
      · simp only [hxy.symm, ↓reduceIte]
        linarith [hΔ i]
      · simp only [hzx.symm, hz, hxy.symm, ↓reduceIte]
        linarith [min_le_right (v i z + Δ i / 2) (v' i z + (v i (f v') - v' i (f v')))]
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
  have := not_nonempty_iff.mp h
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.1 (by omega : 1 < Fintype.card Ω)
  obtain ⟨va, rfl⟩ := hf a
  obtain ⟨vb, rfl⟩ := hf b
  exact hab (congrArg f (funext fun i => (IsEmpty.false i).elim))

private theorem exists_ne_pair [Fintype Ω] (hcard : 3 ≤ Fintype.card Ω)
    (x y : Ω) : ∃ z : Ω, z ≠ x ∧ z ≠ y := by
  classical
  have hlt : ({x, y} : Finset Ω).card < (Finset.univ : Finset Ω).card :=
    lt_of_le_of_lt Finset.card_le_two (by rw [Finset.card_univ]; omega)
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
  refine ⟨v', fun i => by simp only [v', hxy.symm, ↓reduceIte]; linarith [hdiff i], ?_⟩
  rw [← hfx]
  refine hpad v v' (fun _ => trivial) (fun _ => trivial) fun i z hz => ?_
  rw [hfx] at hz ⊢
  simp only [v', hz, ↓reduceIte]
  linarith [hlt i]

/-- Contrapositive core behind Claim 12.31(i) ([Lavi2007], p. 319). -/
private theorem exists_add_nonneg_of_mem_diffSet {f : (ι → Ω → ℝ) → Ω}
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ)) {x y : Ω} (hxy : x ≠ y)
    {α β : ι → ℝ} (hα : α ∈ diffSet f x y) (hβ : β ∈ diffSet f y x) :
    ∃ i, 0 ≤ α i + β i := by
  obtain ⟨u, hud, rfl⟩ := hα
  obtain ⟨v, hvd, rfl⟩ := hβ
  obtain ⟨i, hi⟩ := hgw u v (fun _ => trivial) (fun _ => trivial) hxy
  exact ⟨i, by linarith [hud i, hvd i]⟩

/-- Claim 12.31(ii) ([Lavi2007], p. 319): `α ∉ P(x, y) → -α ∈ P(y, x)`. -/
private theorem neg_mem_diffSet_of_notMem {f : (ι → Ω → ℝ) → Ω}
    (hf_onto : Function.Surjective f) (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ))
    {x y : Ω} (hxy : x ≠ y) {α : ι → ℝ} (hα : α ∉ diffSet f x y) :
    -α ∈ diffSet f y x := by
  classical
  choose β hβ using fun z : Ω => diffSet_nonempty hf_onto x z
  let v : ι → Ω → ℝ := fun i z =>
    if z = x then α i else if z = y then 0 else α i - (β z i + 1)
  refine ⟨v, fun i => by simp [v, hxy.symm], by_contra fun hne => ?_⟩
  have hnotx : f v ≠ x := fun hfx =>
    hα ⟨v, fun i => by simp [v, hxy.symm], hfx⟩
  obtain ⟨i, hi⟩ := exists_add_nonneg_of_mem_diffSet hgw hnotx ⟨v, fun _ => rfl, rfl⟩ (hβ (f v))
  simp only [v, hnotx, hne, ↓reduceIte] at hi
  linarith

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
    if w = x then α i + β i + δ else if w = y then β i + δ / 2
    else if w = z then 0 else (α i + β i + δ) - (η w i + 1)
  have hnoty : f v ≠ y := fun hfy => by
    obtain ⟨i, hi⟩ := exists_add_nonneg_of_mem_diffSet hgw hxy hα ⟨v, fun _ => rfl, hfy⟩
    simp only [v, hxy.symm, ↓reduceIte] at hi; linarith
  have hnotz : f v ≠ z := fun hfz => by
    obtain ⟨i, hi⟩ := exists_add_nonneg_of_mem_diffSet hgw hyz hβ ⟨v, fun _ => rfl, hfz⟩
    simp only [v, hxy.symm, hxz.symm, hyz.symm, ↓reduceIte] at hi; linarith
  refine ⟨v, fun i => by simp [v, hxz.symm, hyz.symm], by_contra fun hne => ?_⟩
  obtain ⟨i, hi⟩ := exists_add_nonneg_of_mem_diffSet hgw hne ⟨v, fun _ => rfl, rfl⟩ (hη (f v))
  simp only [v, hne, hnoty, hnotz, ↓reduceIte] at hi; linarith

private theorem gammaSet_nonempty [Finite ι] [Nonempty ι]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hpad : IsPADOn f (fun _ => Set.univ)) {x y : Ω} (hxy : x ≠ y) :
    {p : ℝ | (fun _ : ι => p) ∈ diffSet f x y}.Nonempty := by
  have := Fintype.ofFinite ι
  obtain ⟨α, hα⟩ := diffSet_nonempty hf_onto x y
  exact ⟨Finset.univ.sup' Finset.univ_nonempty α + 1,
    diffSet_upward hpad hxy hα fun i => by linarith [Finset.le_sup' α (Finset.mem_univ i)]⟩

private theorem gammaSet_bddBelow [Finite ι] [Nonempty ι]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ)) {x y : Ω} (hxy : x ≠ y) :
    BddBelow {p : ℝ | (fun _ : ι => p) ∈ diffSet f x y} := by
  have := Fintype.ofFinite ι
  obtain ⟨β, hβ⟩ := diffSet_nonempty hf_onto y x
  refine ⟨Finset.univ.inf' Finset.univ_nonempty (fun i => -β i), fun p hp => ?_⟩
  obtain ⟨i, hi⟩ := exists_add_nonneg_of_mem_diffSet hgw hxy hp hβ
  linarith [Finset.inf'_le (fun i => -β i) (Finset.mem_univ i)]

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
  simp only [gamma, hxy, ↓reduceIte] at hp
  exact hp.not_ge (csInf_le (gammaSet_bddBelow hf_onto hgw hxy) hmem)

private theorem gamma_neg [Finite ι] [Nonempty ι] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hpad : IsPADOn f (fun _ => Set.univ))
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ)) (x y : Ω) :
    gamma f x y = -gamma f y x := by
  rcases eq_or_ne y x with rfl | hxy
  · simp [gamma]
  · refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) ?_
    · simp only [gamma, hxy.symm, ↓reduceIte]
      refine csInf_le (gammaSet_bddBelow hf_onto hgw hxy.symm) ?_
      change (fun _ : ι => -gamma f y x + ε) ∈ diffSet f x y
      convert neg_mem_diffSet_of_notMem hf_onto hgw hxy
        (const_notMem_diffSet_of_lt_gamma hf_onto hgw hxy
          (p := gamma f y x - ε) (by linarith)) using 1
      exact funext fun _ => by simp only [Pi.neg_apply]; ring
    · by_contra hlt
      push Not at hlt
      obtain ⟨_, hi⟩ := exists_add_nonneg_of_mem_diffSet hgw hxy.symm
        (const_mem_diffSet_of_gamma_lt hf_onto hpad hxy.symm
          (p := gamma f x y - (gamma f x y + gamma f y x) / 4) (by linarith))
        (const_mem_diffSet_of_gamma_lt hf_onto hpad hxy
          (p := gamma f y x - (gamma f x y + gamma f y x) / 4) (by linarith))
      linarith

private theorem gamma_add_le [Finite ι] [Nonempty ι] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hpad : IsPADOn f (fun _ => Set.univ))
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ)) (x y z : Ω) :
    gamma f x z ≤ gamma f x y + gamma f y z := by
  rcases eq_or_ne y x with rfl | hxy
  · simp [gamma]
  rcases eq_or_ne z y with rfl | hyz
  · simp [gamma]
  rcases eq_or_ne z x with rfl | hxz
  · rw [gamma_neg hf_onto hpad hgw y z]
    simp [gamma]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  simp only [gamma, hxz.symm, ↓reduceIte]
  refine csInf_le (gammaSet_bddBelow hf_onto hgw hxz.symm) ?_
  change (fun _ : ι => gamma f x y + gamma f y z + ε) ∈ diffSet f x z
  convert add_shift_mem_diffSet hf_onto hgw hxy.symm hyz.symm hxz.symm
    (const_mem_diffSet_of_gamma_lt hf_onto hpad hxy.symm (p := gamma f x y + ε / 3) (by linarith))
    (const_mem_diffSet_of_gamma_lt hf_onto hpad hyz.symm (p := gamma f y z + ε / 3) (by linarith))
    (δ := ε / 3) (by linarith) using 1
  exact funext fun _ => by ring

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
  exact funext fun _ => by ring

private theorem openShifted_subset_right [Finite ι] [Nonempty ι] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hpad : IsPADOn f (fun _ => Set.univ))
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ))
    {x y z : Ω} (hxy : x ≠ y) (hxz : x ≠ z) :
    openShifted f x y ⊆ openShifted f x z := by
  by_cases hyz : y = z
  · subst hyz; exact Set.Subset.rfl
  rintro α ⟨ε, hε, hmem⟩
  have hsum : (fun i => α i - ε / 2) + (fun _ => ε / 2) = α := funext fun _ => sub_add_cancel _ _
  refine hsum ▸ openShifted_trans_add hf_onto hpad hgw hxy hyz hxz ⟨ε / 2, half_pos hε, ?_⟩
    (const_pos_mem_openShifted hf_onto hpad hyz (half_pos hε))
  convert hmem using 1
  exact funext fun _ => by ring

private theorem openShifted_subset_left [Finite ι] [Nonempty ι] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hpad : IsPADOn f (fun _ => Set.univ))
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ))
    {w x y : Ω} (hwy : w ≠ y) (hxy : x ≠ y) :
    openShifted f x y ⊆ openShifted f w y := by
  by_cases hwx : w = x
  · subst hwx; exact Set.Subset.rfl
  rintro α ⟨ε, hε, hmem⟩
  have hsum : (fun _ => ε / 2) + (fun i => α i - ε / 2) = α := funext fun _ => add_sub_cancel _ _
  refine hsum ▸ openShifted_trans_add hf_onto hpad hgw hwx hxy hwy
    (const_pos_mem_openShifted hf_onto hpad hwx (half_pos hε)) ⟨ε / 2, half_pos hε, ?_⟩
  convert hmem using 1
  exact funext fun _ => by ring

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
  refine ⟨Set.pi Set.univ fun i => Set.Ioi (α i - ε / 2), ?_,
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioi, fun i _ => ?_⟩
  · exact fun β hβ => ⟨ε / 2, half_pos hε, diffSet_upward hpad hxy hmem fun i =>
      by linarith [Set.mem_Ioi.1 (hβ i (Set.mem_univ i))]⟩
  · simp only [Set.mem_Ioi]
    linarith

private theorem openShifted_upward [DecidableEq Ω] {f : (ι → Ω → ℝ) → Ω}
    (hpad : IsPADOn f (fun _ => Set.univ)) {x y : Ω} (hxy : x ≠ y)
    {α β : ι → ℝ} (hα : α ∈ openShifted f x y) (hle : ∀ i, α i ≤ β i) :
    β ∈ openShifted f x y := by
  obtain ⟨ε, hε, hmem⟩ := hα
  exact ⟨ε / 2, half_pos hε, diffSet_upward hpad hxy hmem fun i => by linarith [hle i]⟩

private theorem openShifted_add [Finite ι] [Nonempty ι] [Fintype Ω] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hpad : IsPADOn f (fun _ => Set.univ))
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ))
    (hcard : 3 ≤ Fintype.card Ω) {x₀ y₀ : Ω} (hxy : x₀ ≠ y₀)
    {α β : ι → ℝ} (hα : α ∈ openShifted f x₀ y₀) (hβ : β ∈ openShifted f x₀ y₀) :
    α + β ∈ openShifted f x₀ y₀ := by
  obtain ⟨z₀, hzx, hzy⟩ := exists_ne_pair hcard x₀ y₀
  rw [openShifted_eq hf_onto hpad hgw hcard hxy hzy.symm] at hβ
  rw [openShifted_eq hf_onto hpad hgw hcard hxy hzx.symm]
  exact openShifted_trans_add hf_onto hpad hgw hxy hzy.symm hzx.symm hα hβ

private theorem openShifted_half [Finite ι] [Nonempty ι] [Fintype Ω] [DecidableEq Ω]
    {f : (ι → Ω → ℝ) → Ω} (hf_onto : Function.Surjective f)
    (hpad : IsPADOn f (fun _ => Set.univ))
    (hgw : IsGeneralizedWMONOn f (fun _ => Set.univ))
    (hcard : 3 ≤ Fintype.card Ω) {x₀ y₀ : Ω} (hxy : x₀ ≠ y₀)
    {α : ι → ℝ} (hα : α ∈ openShifted f x₀ y₀) :
    ((1 / 2 : ℝ) • α) ∈ openShifted f x₀ y₀ := by
  by_contra hnot
  obtain ⟨ε, hε, hmem⟩ := hα
  have hnot_diff : (fun i => α i / 2 + gamma f x₀ y₀ - ε / 8) ∉ diffSet f x₀ y₀ := fun h =>
    hnot ⟨ε / 8, by linarith,
      by
        convert h using 1
        exact funext fun _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring⟩
  have h2 : (fun i => -α i / 2 + ε / 4) ∈ openShifted f x₀ y₀ := by
    rw [openShifted_eq hf_onto hpad hgw hcard hxy hxy.symm]
    refine ⟨ε / 8, by linarith, ?_⟩
    convert neg_mem_diffSet_of_notMem hf_onto hgw hxy hnot_diff using 1
    exact funext fun _ => by simp only [Pi.neg_apply, gamma_neg hf_onto hpad hgw y₀ x₀]; ring
  have h1 : (fun i => α i - ε / 2) ∈ openShifted f x₀ y₀ :=
    ⟨ε / 2, half_pos hε, by
      convert hmem using 1
      exact funext fun _ => by ring⟩
  exact hnot <| openShifted_upward hpad hxy (openShifted_add hf_onto hpad hgw hcard hxy h1 h2)
    fun i => by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; linarith

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
      · rw [Nat.cast_succ, add_smul, one_smul]
        exact openShifted_add hf_onto hpad hgw hcard hxy (ih (Nat.succ_pos k)) hβ
  have hpow : ∀ (m : ℕ) (β : ι → ℝ), β ∈ openShifted f x₀ y₀ →
      ((1 / 2 : ℝ) ^ m) • β ∈ openShifted f x₀ y₀ := by
    intro m β hβ
    induction m with
    | zero => simpa using hβ
    | succ m ih =>
      rw [pow_succ', ← smul_smul]
      exact openShifted_half hf_onto hpad hgw hcard hxy ih
  obtain ⟨ε, hε, hmem⟩ := hα
  let r : ℝ := ε / 2
  have hr : 0 < r := half_pos hε
  let α' : ι → ℝ := fun i => α i - r
  have hα' : α' ∈ openShifted f x₀ y₀ :=
    ⟨ε / 2, hr, by
      convert hmem using 1
      exact funext fun _ => by ring⟩
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i => |α i|) + 1
  have hM_le : ∀ i, |α i| ≤ M := fun i =>
    le_add_of_le_of_nonneg (Finset.le_sup' (fun i => |α i|) (Finset.mem_univ i)) zero_le_one
  have ⟨i₀⟩ := ‹Nonempty ι›
  have hM : 0 < M := lt_of_le_of_lt (abs_nonneg (α i₀))
    (lt_of_le_of_lt (Finset.le_sup' (fun i => |α i|) (Finset.mem_univ i₀)) (lt_add_one _))
  let η : ℝ := min (t / 2) (t * r / (2 * M))
  have hη : 0 < η := lt_min (half_pos ht) (div_pos (mul_pos ht hr) (mul_pos two_pos hM))
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hη (by norm_num : (1 / 2 : ℝ) < 1)
  have h2m_pos : (0 : ℝ) < (2 : ℝ) ^ m := pow_pos (by norm_num) m
  have hinv : (1 / 2 : ℝ) ^ m = 1 / (2 : ℝ) ^ m := one_div_pow 2 m
  have hδ : 1 / (2 : ℝ) ^ m < η := hinv ▸ hm
  set n : ℕ := ⌊t * (2 : ℝ) ^ m⌋₊
  set d : ℝ := (n : ℝ) / (2 : ℝ) ^ m
  have hdt_le : d ≤ t := (div_le_iff₀ h2m_pos).2 (Nat.floor_le (mul_nonneg ht.le h2m_pos.le))
  have hdt_lt : t - 1 / (2 : ℝ) ^ m < d := (lt_div_iff₀ h2m_pos).2 <| by
    rw [sub_mul, div_mul_cancel₀ _ h2m_pos.ne']
    linarith [Nat.lt_floor_add_one (t * (2 : ℝ) ^ m)]
  have htd_half : t / 2 < d := by linarith [min_le_left (t / 2) (t * r / (2 * M))]
  have hn_pos : 0 < n := Nat.pos_of_ne_zero fun h0 => by
    simp only [d, h0, Nat.cast_zero, zero_div] at htd_half; linarith
  have hd_mem : d • α' ∈ openShifted f x₀ y₀ := by
    convert hpow m _ (hnsmul n α' hn_pos hα') using 1
    rw [smul_smul, hinv, one_div_mul_eq_div]
  refine openShifted_upward hpad hxy hd_mem fun i => ?_
  simp only [Pi.smul_apply, smul_eq_mul, α']
  have htd_lt_bound : t - d < t * r / (2 * M) := by
    linarith [min_le_right (t / 2) (t * r / (2 * M))]
  have habs_mul : (t - d) * |α i| ≤ t * r / 2 :=
    calc (t - d) * |α i|
      _ ≤ (t - d) * M := mul_le_mul_of_nonneg_left (hM_le i) (by linarith)
      _ ≤ (t * r / (2 * M)) * M := mul_le_mul_of_nonneg_right htd_lt_bound.le hM.le
      _ = t * r / 2 := by field_simp [hM.ne']
  have hlow := mul_le_mul_of_nonneg_left (neg_abs_le (α i)) (by linarith : 0 ≤ t - d)
  nlinarith

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
  have hpad := (isWeaklyMonotoneOn_univ_iff.2 hf_wmon).isPADOn
  have hgw := isGeneralizedWMON_of_isPAD hpad
  obtain ⟨y₀, hy₀, _⟩ := exists_ne_pair hcard x₀ x₀
  have hxy : x₀ ≠ y₀ := hy₀.symm
  obtain ⟨L, hL⟩ := geometric_hahn_banach_point_open
    (openShifted_convex hf_onto hpad hgw hcard hxy) (openShifted_isOpen hpad hxy)
    (zero_notMem_openShifted hf_onto hgw hxy)
  have hL_pos : ∀ α ∈ openShifted f x₀ y₀, 0 < L α := fun α hα => by simpa using hL α hα
  let w₀ : ι → ℝ := fun i => L (Pi.single i 1)
  have hL_eq : ∀ α : ι → ℝ, L α = ∑ i, w₀ i * α i := fun α => by
    have hdecomp : α = ∑ i : ι, α i • Pi.single i (1 : ℝ) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hdecomp]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul, mul_comm]
  have hone_mem := const_pos_mem_openShifted hf_onto hpad hxy zero_lt_one
  have hsum_pos : 0 < ∑ i, w₀ i := by simpa only [hL_eq, mul_one] using hL_pos _ hone_mem
  have hw₀_nonneg : ∀ i, 0 ≤ w₀ i := fun i => by
    by_contra! hneg
    let t : ℝ := (∑ j, w₀ j) / (-w₀ i) + 1
    have ht : 0 ≤ t := add_nonneg (div_nonneg hsum_pos.le (by linarith)) zero_le_one
    have hlt := hL_pos ((fun _ : ι => (1 : ℝ)) + t • Pi.single i (1 : ℝ))
      (openShifted_upward hpad hxy hone_mem fun j => by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
        split_ifs <;> linarith)
    rw [map_add, map_smul, smul_eq_mul, hL_eq] at hlt
    simp only [mul_one] at hlt
    have hcalc : t * w₀ i = -(∑ j, w₀ j) + w₀ i := by dsimp [t]; field_simp [hneg.ne]
    change 0 < ∑ j, w₀ j + t * w₀ i at hlt
    linarith
  let S : ℝ := ∑ i, w₀ i
  have hSne : S ≠ 0 := hsum_pos.ne'
  let w : ι → ℝ := fun i => w₀ i / S
  refine ⟨w, fun i => div_nonneg (hw₀_nonneg i) hsum_pos.le, ?_, fun b => ⟨Set.mem_univ _, ?_⟩⟩
  · simp only [w, div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ hSne
  · intro y _
    set x := f b
    by_cases heq : y = x
    · subst heq; exact le_rfl
    have hnonneg : 0 ≤ ∑ i, w₀ i * ((b i x - b i y) - gamma f x y) := by
      by_contra! hlt
      let ε : ℝ := -(∑ i, w₀ i * ((b i x - b i y) - gamma f x y)) / (2 * S)
      have hε : 0 < ε := div_pos (by linarith) (mul_pos two_pos hsum_pos)
      let α : ι → ℝ := fun i => b i x - b i y - gamma f x y + ε
      have hα_diff : (fun i => α i + gamma f x y - ε) ∈ diffSet f x y :=
        ⟨b, fun _ => by simp only [α]; ring, rfl⟩
      have hα : α ∈ openShifted f x₀ y₀ := by
        rw [← openShifted_eq hf_onto hpad hgw hcard (Ne.symm heq) hxy]
        exact ⟨ε, hε, hα_diff⟩
      have hexp : L α = (∑ i, w₀ i * ((b i x - b i y) - gamma f x y)) / 2 :=
        calc L α
          _ = ∑ i, w₀ i * α i := hL_eq α
          _ = ∑ i, w₀ i * ((b i x - b i y) - gamma f x y) + ε * S := by
                simp only [α, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, S]
                ring
          _ = (∑ i, w₀ i * ((b i x - b i y) - gamma f x y)) / 2 := by
                have hεS : ε * S = -(∑ i, w₀ i * ((b i x - b i y) - gamma f x y)) / 2 := by
                  dsimp [ε]
                  field_simp [hSne]
                linarith
      linarith [hL_pos α hα]
    have hdiv : 0 ≤ ∑ i, w i * (b i x - b i y) - gamma f x y := by
      refine nonneg_of_mul_nonneg_left (b := S) ?_ hsum_pos
      rw [sub_mul, Finset.sum_mul]
      simp only [w, div_mul_eq_mul_div, div_mul_cancel₀ _ hSne]
      simpa only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, mul_comm (gamma f x y) S]
        using hnonneg
    simp only [mul_sub, Finset.sum_sub_distrib] at hdiv
    simp only [affineScore]
    linarith [gamma_add hf_onto hpad hgw x₀ x y]

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
  have ⟨x₀⟩ : Nonempty Ω := Fintype.card_pos_iff.1 (by omega)
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
  refine ⟨Set.univ, w, c, hw, ?_, hmax⟩
  by_contra! h
  linarith [Finset.sum_nonpos (s := Finset.univ) fun i _ => h i]

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
  have ⟨x₀⟩ : Nonempty Ω := Fintype.card_pos_iff.1 (by omega)
  have hpad := (isWeaklyMonotoneOn_univ_iff.2 hf_wmon).isPADOn
  have hgw := isGeneralizedWMON_of_isPAD hpad
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
    rcases eq_or_ne y x with rfl | hxy
    · simp [gamma]
    · linarith [hgamma_le x y hxy.symm, hgamma_le y x hxy, gamma_neg hf_onto hpad hgw y x]
  obtain ⟨w, hw, hsum, hmax⟩ := roberts_with_gamma hf_onto hf_wmon hcard x₀
  exact ⟨w, hw, hsum, fun b ω => by
    simpa only [affineScore, hgamma_zero, zero_add] using (hmax b).2 ω (Set.mem_univ _)⟩

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
    rwa [Set.ncard_eq_toFinset_card', Set.toFinset_card] at hcard
  let ext (u : ι → Set.range f → ℝ) : ι → Ω → ℝ :=
    fun i ω => if h : ω ∈ Set.range f then u i ⟨ω, h⟩ else 0
  let g : (ι → Set.range f → ℝ) → Set.range f := fun u => ⟨f (ext u), Set.mem_range_self _⟩
  have hpad : ∀ {v v' : ι → Ω → ℝ},
      (∀ i, ∀ y ∈ Set.range f, y ≠ f v → v' i y - v i y < v' i (f v) - v i (f v)) →
      f v' = f v := fun hinc =>
    pad_range_of_isWeaklyMonotoneOn (isWeaklyMonotoneOn_univ_iff.2 hf_wmon)
      (fun _ => trivial) (fun _ => trivial) hinc
  have hext_upd (u : ι → Set.range f → ℝ) (i : ι) (v : Set.range f → ℝ) :
      ext (Function.update u i v) =
        Function.update (ext u) i (fun ω => if h : ω ∈ Set.range f then v ⟨ω, h⟩ else 0) := by
    ext j ω
    by_cases h : j = i <;> simp [h, ext]
  have hg_wmon : IsWeaklyMonotone g := fun i u v v' => by
    simpa only [← hext_upd, g, Set.mem_range_self, ↓reduceDIte] using
      hf_wmon i (ext u) (fun ω => if h : ω ∈ Set.range f then v ⟨ω, h⟩ else 0)
        (fun ω => if h : ω ∈ Set.range f then v' ⟨ω, h⟩ else 0)
  have hg_onto : Function.Surjective g := by
    rintro ⟨a, v, rfl⟩
    refine ⟨fun i r => if r.val = f v then v i r.val + 1 else v i r.val,
      Subtype.ext <| hpad fun i y hy hyne => ?_⟩
    simp only [ext, hy, Set.mem_range_self, ↓reduceDIte, hyne, ↓reduceIte]; linarith
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
    simp only [ext, hz, Set.mem_range_self b, ↓reduceDIte, u, hzne, x, ↓reduceIte]; linarith
  calc affineScore w c b y
    _ = affineScore w c' u ⟨y, hy⟩ := by
          simp only [affineScore, c, hy, ↓reduceDIte]
          exact congrArg (c' ⟨y, hy⟩ + ·)
            (Finset.sum_congr rfl fun i _ => by simp only [u, hyx, ↓reduceIte])
    _ ≤ affineScore w c' u ⟨x, Set.mem_range_self b⟩ :=
          (Subtype.ext hfu : g u = ⟨x, Set.mem_range_self b⟩) ▸
            (hmax u).2 ⟨y, hy⟩ (Set.mem_univ _)
    _ = affineScore w c b x + ε := by
          simp only [affineScore, c, u, x, Set.mem_range_self b, ↓reduceDIte, ↓reduceIte, mul_add,
            Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul, add_assoc]

end Cslib.GameTheory.Mechanism
