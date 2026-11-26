/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Market.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Foundations.Analysis.ReverseHolder
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Gross substitutability, separating hyperplanes, and Cobb–Douglas / CES demands

For general exchange economies equilibrium price vectors need not be unique or even form a
connected set ([CodenottiVaradarajan2007], Section 6.1.4, p. 138; Section 6.5.1, p. 151). When the
aggregate excess-demand function `Z : (G → ℝ) → G → ℝ` on strictly positive price vectors satisfies
**gross substitutability** (`IsGrossSubstitutes`) or **weak gross substitutability**
(`IsWeakGrossSubstitutes`), raising the prices of some goods while holding the remaining prices
fixed never decreases the excess demand for any good whose price remained fixed.

Building on `CslibFrontier.GameTheory.Market.Basic`, this module formalizes the structural and
parametric results of [CodenottiVaradarajan2007], Sections 6.1.4–6.1.5, 6.3, 6.4.2, and
Exercises 6.1–6.3:

1. **Excess-demand systems, GS/WGS, and uniqueness (`§6.1.1, §6.1.4`, pp. 137–138):**
   degree-`0` homogeneity (`IsHomogeneousDegZero`), Walras's law (`SatisfiesWalrasLaw`), positive
   Walrasian equilibria (`IsWalrasianEquilibrium`), closure of WGS/GS under aggregation, and
   uniqueness of positive Walrasian equilibrium prices up to positive scaling under strict gross
   substitutability (`IsGrossSubstitutes.eq_smul_of_isWalrasianEquilibrium`). Note that
   [CodenottiVaradarajan2007], Section 6.1.4, p. 138 informally attributes uniqueness up to scaling
   to WGS; under non-strict WGS alone, independent submarkets can produce a multi-ray convex cone of
   positive equilibria, whereas strict GS gives uniqueness up to scaling and WGS gives convexity.
2. **Arrow–Block–Hurwicz / Arrow–Hurwicz separating hyperplane (`Lemma 6.4`, pp. 142–143;
   Equations `(6.5)`–`(6.6)`, pp. 145–146; `§6.7`, p. 156) and convexity (`Exercise 6.3`, p. 158):**
   via the sorted price-ratio hybrid chain `q^s = min(α_s p̂, p)`, in any homogeneous excess-demand
   system satisfying Walras's law and **weak** gross substitutability, every positive equilibrium
   `p̂` and positive non-equilibrium `p` satisfy `0 < expenditure p̂ (Z p)`
   (`IsWeakGrossSubstitutes.expenditure_pos_of_not_isWalrasianEquilibrium`). Consequently, moving
   from `p` in direction `Z p` makes a strictly acute angle with `p̂ - p` (`§6.3.1`, p. 143), and
   the set of positive Walrasian equilibrium price vectors is convex
   (`IsWeakGrossSubstitutes.convex_setOf_isWalrasianEquilibrium`, **Exercise 6.3**).
3. **Cobb–Douglas and CES Marshallian demands (`§6.1.5`, p. 139; `§6.4.2` Eq. `(6.7)`, p. 149;
   `Exercises 6.1–6.2`, p. 158):**
   explicit closed-form demands `cobbDouglasDemand` and `cesDemand`, exact `Market.demandSet`
   characterizations via weighted AM–GM and reverse Hölder (**Exercise 6.1**), WGS of Cobb–Douglas
   exchange markets and `0 < ρ < 1` CES excess demands, and the polynomial-size linear-program
   characterization of positive equilibrium prices in Cobb–Douglas exchange economies
   (`CobbDouglasExchangeMarket.isWalrasianEquilibrium_iff_linearInequalities`, **Exercise 6.2**).

## Main definitions

* `Cslib.GameTheory.Market.IsHomogeneousDegZero`, `Cslib.GameTheory.Market.SatisfiesWalrasLaw`,
  `Cslib.GameTheory.Market.IsWalrasianEquilibrium`: properties of a single-valued excess-demand
  map `Z : (G → ℝ) → G → ℝ` on strictly positive prices.
* `Cslib.GameTheory.Market.IsWeakGrossSubstitutes`, `Cslib.GameTheory.Market.IsGrossSubstitutes`:
  weak and strict gross substitutability ([CodenottiVaradarajan2007], Section 6.1.4, p. 138).
* `Cslib.GameTheory.Market.cobbDouglasUtility`, `Cslib.GameTheory.Market.cobbDouglasDemand`,
  `Cslib.GameTheory.Market.CobbDouglasExchangeMarket`: Cobb–Douglas utilities, Marshallian demands,
  and exchange economies ([CodenottiVaradarajan2007], Section 6.1.5, p. 139).
* `Cslib.GameTheory.Market.cesUtility`, `Cslib.GameTheory.Market.cesDemand`: constant-elasticity-of-
  substitution utilities and Marshallian demand formula `(6.7)` ([CodenottiVaradarajan2007],
  Section 6.1.5, p. 139 and Section 6.4.2, p. 149).

## Main results

* `Cslib.GameTheory.Market.IsGrossSubstitutes.eq_smul_of_isWalrasianEquilibrium`: positive
  Walrasian equilibrium prices are unique up to positive scaling under strict GS.
* `Cslib.GameTheory.Market.IsWeakGrossSubstitutes.expenditure_pos_of_not_isWalrasianEquilibrium`:
  **Lemma 6.4** (Arrow–Block–Hurwicz / Arrow–Hurwicz separating hyperplane under WGS).
* `Cslib.GameTheory.Market.IsWeakGrossSubstitutes.convex_setOf_isWalrasianEquilibrium`:
  **Exercise 6.3** (convexity of the set of positive equilibrium price vectors under WGS).
* `Cslib.GameTheory.Market.cobbDouglasDemand_mem_demandSet`,
  `Cslib.GameTheory.Market.demandSet_cobbDouglasUtility_eq`: **Exercise 6.1 (Cobb–Douglas)**
  optimality and uniqueness of Marshallian demand.
* `CobbDouglasExchangeMarket.isWalrasianEquilibrium_iff_linearInequalities`,
  `CobbDouglasExchangeMarket.isCompetitiveEquilibrium_of_isWalrasianEquilibrium`:
  **Exercise 6.2** (linear-program characterization of Cobb–Douglas equilibrium prices).
* `Cslib.GameTheory.Market.cesDemand_mem_demandSet`,
  `Cslib.GameTheory.Market.isWeakGrossSubstitutes_cesExcessDemand`: **Exercise 6.1 (CES)**
  optimality of formula `(6.7)` for all `ρ < 1, ρ ≠ 0`, and WGS in the substitutes regime
  `0 < ρ < 1`.

## References

* [ArrowBlockHurwicz1959] (primary PDF unverified; cited via [CodenottiVaradarajan2007])
* [ArrowHurwicz1960a] (primary PDF unverified; cited via [CodenottiVaradarajan2007])
* [CodenottiVaradarajan2007], Sections 6.1.4–6.1.5, 6.3, 6.4.2, 6.7, and Exercises 6.1–6.3,
  pp. 137–150, 156, 158
-/

public section

namespace Cslib.GameTheory.Market

open Finset
open scoped BigOperators

/-! ### Single-valued excess-demand systems and gross substitutability -/

section ExcessDemand

variable {G : Type*}

/-- An excess-demand map `Z : (G → ℝ) → G → ℝ` is **homogeneous of degree `0`** on strictly positive
price vectors ([CodenottiVaradarajan2007], Section 6.1.1, p. 137) if scaling all prices by `c > 0`
leaves `Z` unchanged. -/
@[expose] def IsHomogeneousDegZero (Z : (G → ℝ) → G → ℝ) : Prop :=
  ∀ ⦃c : ℝ⦄, 0 < c → ∀ ⦃p : G → ℝ⦄, (∀ g, 0 < p g) → Z (c • p) = Z p

/-- An excess-demand map `Z : (G → ℝ) → G → ℝ` satisfies **Walras's law** on strictly positive price
vectors ([CodenottiVaradarajan2007], Section 6.1.1, p. 137) if `expenditure p (Z p) = 0` for every
`p > 0`. -/
@[expose] def SatisfiesWalrasLaw [Fintype G] (Z : (G → ℝ) → G → ℝ) : Prop :=
  ∀ ⦃p : G → ℝ⦄, (∀ g, 0 < p g) → expenditure p (Z p) = 0

/-- A strictly positive price vector `p` is a **Walrasian equilibrium** of `Z`
([CodenottiVaradarajan2007], Section 6.1.1, p. 137) if `Z p g ≤ 0` for every good `g`. -/
@[expose] def IsWalrasianEquilibrium (Z : (G → ℝ) → G → ℝ) (p : G → ℝ) : Prop :=
  (∀ g, 0 < p g) ∧ ∀ g, Z p g ≤ 0

/-- Under Walras's law, every strictly positive Walrasian equilibrium clears every good with exact
equality (`Z p = 0`). -/
theorem SatisfiesWalrasLaw.eq_zero_of_isWalrasianEquilibrium [Fintype G] {Z : (G → ℝ) → G → ℝ}
    (hW : SatisfiesWalrasLaw Z) {p : G → ℝ} (heq : IsWalrasianEquilibrium Z p) :
    Z p = 0 := by
  funext g
  have h0 := (sum_eq_zero_iff_of_nonpos fun k _ =>
    mul_nonpos_of_nonneg_of_nonpos (heq.1 k).le (heq.2 k)).1
      ((expenditure_eq_sum _ _).symm.trans (hW heq.1)) g (mem_univ g)
  exact (mul_eq_zero.1 h0).resolve_left (heq.1 g).ne'

theorem SatisfiesWalrasLaw.isWalrasianEquilibrium_iff_eq_zero [Fintype G] {Z : (G → ℝ) → G → ℝ}
    (hW : SatisfiesWalrasLaw Z) {p : G → ℝ} :
    IsWalrasianEquilibrium Z p ↔ (∀ g, 0 < p g) ∧ Z p = 0 :=
  ⟨fun h => ⟨h.1, hW.eq_zero_of_isWalrasianEquilibrium h⟩,
    fun ⟨hp, hz⟩ => ⟨hp, fun g => by rw [hz]; exact le_rfl⟩⟩

theorem IsHomogeneousDegZero.isWalrasianEquilibrium_smul {Z : (G → ℝ) → G → ℝ}
    (hH : IsHomogeneousDegZero Z) {p : G → ℝ} (heq : IsWalrasianEquilibrium Z p)
    {c : ℝ} (hc : 0 < c) :
    IsWalrasianEquilibrium Z (c • p) :=
  ⟨fun g => mul_pos hc (heq.1 g), fun g => (hH hc heq.1).symm ▸ heq.2 g⟩

/-- **Weak gross substitutability (WGS)** ([CodenottiVaradarajan2007], Section 6.1.4, p. 138):
whenever prices move from `p > 0` to `p' ≥ p`, the excess demand of any good `g` whose price remains
unchanged (`p' g = p g`) does not decrease (`Z p g ≤ Z p' g`). (Note that
[CodenottiVaradarajan2007] additionally writes `∃ j, p j < p' j`; when `p = p'` the inequality
`Z p g ≤ Z p' g` holds trivially by reflexivity.) -/
@[expose] def IsWeakGrossSubstitutes (Z : (G → ℝ) → G → ℝ) : Prop :=
  ∀ ⦃p p' : G → ℝ⦄, (∀ g, 0 < p g) → (∀ g, p g ≤ p' g) → ∀ g, p' g = p g → Z p g ≤ Z p' g

/-- **Strict gross substitutability (GS)** ([ArrowBlockHurwicz1959]; [CodenottiVaradarajan2007],
Section 6.1.4, p. 138): whenever prices move from `p > 0` to `p' ≥ p` with `p j < p' j` for at least
one good `j`, the excess demand of every good `g` whose price remains unchanged (`p' g = p g`)
strictly increases (`Z p g < Z p' g`). -/
@[expose] def IsGrossSubstitutes (Z : (G → ℝ) → G → ℝ) : Prop :=
  ∀ ⦃p p' : G → ℝ⦄, (∀ g, 0 < p g) → (∀ g, p g ≤ p' g) → (∃ j, p j < p' j) →
    ∀ g, p' g = p g → Z p g < Z p' g

theorem IsGrossSubstitutes.isWeakGrossSubstitutes {Z : (G → ℝ) → G → ℝ}
    (hGS : IsGrossSubstitutes Z) : IsWeakGrossSubstitutes Z := by
  intro p p' hp hle g hfg
  by_cases hex : ∃ j, p j < p' j
  · exact (hGS hp hle hex g hfg).le
  · rw [funext fun j => le_antisymm (hle j) (not_lt.1 fun hj => hex ⟨j, hj⟩)]

/-- Weak gross substitutability is closed under finite aggregation ([CodenottiVaradarajan2007],
Section 6.1.4, p. 138). -/
theorem IsWeakGrossSubstitutes.sum {ι : Type*} (s : Finset ι) {z : ι → (G → ℝ) → G → ℝ}
    (hz : ∀ i ∈ s, IsWeakGrossSubstitutes (z i)) :
    IsWeakGrossSubstitutes (fun p g => ∑ i ∈ s, z i p g) :=
  fun _ _ hp hle g hfg => sum_le_sum fun i hi => hz i hi hp hle g hfg

/-- Aggregating a family of WGS excess-demand functions in which at least one agent satisfies strict
GS yields strict GS. -/
theorem IsGrossSubstitutes.of_sum_exists {ι : Type*} (s : Finset ι) {z : ι → (G → ℝ) → G → ℝ}
    (hwgs : ∀ i ∈ s, IsWeakGrossSubstitutes (z i))
    (hgs : ∃ i ∈ s, IsGrossSubstitutes (z i)) :
    IsGrossSubstitutes (fun p g => ∑ i ∈ s, z i p g) := by
  obtain ⟨i₀, hi₀, hgs₀⟩ := hgs
  intro p p' hp hle hex g hfg
  exact sum_lt_sum (fun i hi => hwgs i hi hp hle g hfg) ⟨i₀, hi₀, hgs₀ hp hle hex g hfg⟩

theorem IsWeakGrossSubstitutes.sub_const {X : (G → ℝ) → G → ℝ} (hX : IsWeakGrossSubstitutes X)
    (W : G → ℝ) : IsWeakGrossSubstitutes (fun p g => X p g - W g) :=
  fun _ _ hp hle g hfg => sub_le_sub_right (hX hp hle g hfg) (W g)

theorem IsGrossSubstitutes.sub_const {X : (G → ℝ) → G → ℝ} (hX : IsGrossSubstitutes X)
    (W : G → ℝ) : IsGrossSubstitutes (fun p g => X p g - W g) :=
  fun _ _ hp hle hex g hfg => sub_lt_sub_right (hX hp hle hex g hfg) (W g)

/-- **Uniqueness of Walrasian equilibrium prices up to positive scaling under strict GS**
([ArrowBlockHurwicz1959]; [CodenottiVaradarajan2007], Section 6.1.4, p. 138): if `Z` is homogeneous
of degree `0`, satisfies Walras's law, and satisfies strict gross substitutability, any two positive
Walrasian equilibrium price vectors differ by a positive scalar factor. -/
theorem IsGrossSubstitutes.eq_smul_of_isWalrasianEquilibrium [Fintype G] [Nonempty G]
    {Z : (G → ℝ) → G → ℝ} (hH : IsHomogeneousDegZero Z) (hW : SatisfiesWalrasLaw Z)
    (hGS : IsGrossSubstitutes Z) {p p' : G → ℝ}
    (hp : IsWalrasianEquilibrium Z p) (hp' : IsWalrasianEquilibrium Z p') :
    ∃ c : ℝ, 0 < c ∧ p' = c • p := by
  obtain ⟨g₀, -, hg₀_max⟩ := exists_max_image univ (fun g => p' g / p g) univ_nonempty
  set c : ℝ := p' g₀ / p g₀
  have hc : 0 < c := div_pos (hp'.1 g₀) (hp.1 g₀)
  refine ⟨c, hc, ?_⟩
  have hle : ∀ g, p' g ≤ (c • p) g := fun g =>
    (div_le_iff₀ (hp.1 g)).1 (hg₀_max g (mem_univ g))
  have hfix : (c • p) g₀ = p' g₀ := div_mul_cancel₀ (p' g₀) (hp.1 g₀).ne'
  by_contra hne
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  have hlt := hGS hp'.1 hle ⟨j, lt_of_le_of_ne (hle j) hj⟩ g₀ hfix
  rw [hW.eq_zero_of_isWalrasianEquilibrium hp', hH hc hp.1,
    hW.eq_zero_of_isWalrasianEquilibrium hp] at hlt
  exact lt_irrefl _ hlt

end ExcessDemand

/-! ### Sorted price-ratio hybrid chain and Arrow–Hurwicz separating hyperplanes -/

section SeparatingHyperplane

variable {G : Type*} [Fintype G]

/-- Bijection `Fin (Fintype.card G) ≃ G` ordering the goods so that the price ratio
`s ↦ p (σ s) / pHat (σ s)` is nondecreasing ([CodenottiVaradarajan2007], Lemma 6.7 proof,
p. 145). -/
noncomputable def sortedPriceRatioEquiv (pHat p : G → ℝ) : Fin (Fintype.card G) ≃ G :=
  let e := Fintype.equivFin G
  (Tuple.sort (fun s => p (e.symm s) / pHat (e.symm s))).trans e.symm

theorem monotone_sortedPriceRatio (pHat p : G → ℝ) :
    Monotone
      (fun s => p (sortedPriceRatioEquiv pHat p s) / pHat (sortedPriceRatioEquiv pHat p s)) := by
  intro s₁ s₂ h
  exact Tuple.monotone_sort
    (fun s => p ((Fintype.equivFin G).symm s) / pHat ((Fintype.equivFin G).symm s)) h

/-- Componentwise minimum `min (α * pHat g) (p g)` used as the intermediate hybrid price vector
`q^s` in [CodenottiVaradarajan2007], Lemma 6.7, p. 145. -/
def hybridPrice (pHat p : G → ℝ) (α : ℝ) (g : G) : ℝ :=
  min (α * pHat g) (p g)

omit [Fintype G] in
@[simp] theorem hybridPrice_apply (pHat p : G → ℝ) (α : ℝ) (g : G) :
    hybridPrice pHat p α g = min (α * pHat g) (p g) := by rfl

omit [Fintype G] in
theorem hybridPrice_pos {pHat p : G → ℝ} {α : ℝ} (hpHat : ∀ g, 0 < pHat g) (hp : ∀ g, 0 < p g)
    (hα : 0 < α) (g : G) : 0 < hybridPrice pHat p α g :=
  lt_min (mul_pos hα (hpHat g)) (hp g)

omit [Fintype G] in
theorem hybridPrice_le_smul (pHat p : G → ℝ) (α : ℝ) (g : G) :
    hybridPrice pHat p α g ≤ (α • pHat) g :=
  min_le_left _ _

omit [Fintype G] in
theorem hybridPrice_mono (pHat p : G → ℝ) {α₁ α₂ : ℝ} (hα : α₁ ≤ α₂) (hpHat : ∀ g, 0 ≤ pHat g)
    (g : G) : hybridPrice pHat p α₁ g ≤ hybridPrice pHat p α₂ g :=
  min_le_min_right (p g) (mul_le_mul_of_nonneg_right hα (hpHat g))

theorem hybridPrice_sorted_of_le {pHat p : G → ℝ} (hpHat : ∀ g, 0 < pHat g)
    {s t : Fin (Fintype.card G)} (ht : t ≤ s) :
    let σ := sortedPriceRatioEquiv pHat p
    hybridPrice pHat p (p (σ s) / pHat (σ s)) (σ t) = p (σ t) := by
  intro σ
  exact min_eq_right ((div_le_iff₀ (hpHat (σ t))).1 (monotone_sortedPriceRatio pHat p ht))

theorem hybridPrice_sorted_of_ge {pHat p : G → ℝ} (hpHat : ∀ g, 0 < pHat g)
    {s t : Fin (Fintype.card G)} (ht : s ≤ t) :
    let σ := sortedPriceRatioEquiv pHat p
    hybridPrice pHat p (p (σ s) / pHat (σ s)) (σ t) = (p (σ s) / pHat (σ s)) * pHat (σ t) := by
  intro σ
  exact min_eq_left ((le_div_iff₀ (hpHat (σ t))).1 (monotone_sortedPriceRatio pHat p ht))

theorem hybridPrice_zero_eq_smul {pHat p : G → ℝ} (hpHat : ∀ g, 0 < pHat g)
    (h0 : 0 < Fintype.card G) :
    let σ := sortedPriceRatioEquiv pHat p
    hybridPrice pHat p (p (σ ⟨0, h0⟩) / pHat (σ ⟨0, h0⟩)) =
      (p (σ ⟨0, h0⟩) / pHat (σ ⟨0, h0⟩)) • pHat := by
  intro σ
  funext g
  obtain ⟨t, rfl⟩ := σ.surjective g
  exact hybridPrice_sorted_of_ge hpHat (Nat.zero_le t.val)

theorem hybridPrice_last_eq {pHat p : G → ℝ} (hpHat : ∀ g, 0 < pHat g)
    (h0 : 0 < Fintype.card G) :
    let σ := sortedPriceRatioEquiv pHat p
    let sLast : Fin (Fintype.card G) := ⟨Fintype.card G - 1, Nat.sub_lt h0 Nat.zero_lt_one⟩
    hybridPrice pHat p (p (σ sLast) / pHat (σ sLast)) = p := by
  intro σ sLast
  funext g
  obtain ⟨t, rfl⟩ := σ.surjective g
  exact hybridPrice_sorted_of_le hpHat (Nat.le_sub_one_of_lt t.isLt)

/-- At step `s`, WGS against `α_s • pHat` implies `Z q^s (σ t) ≤ 0` for all `t ≥ s`
([CodenottiVaradarajan2007], Lemma 6.7 proof, p. 145). -/
theorem excessDemand_hybridPrice_nonpos_of_ge {Z : (G → ℝ) → G → ℝ}
    (hH : IsHomogeneousDegZero Z) (hW : SatisfiesWalrasLaw Z) (hWGS : IsWeakGrossSubstitutes Z)
    {pHat p : G → ℝ} (heq : IsWalrasianEquilibrium Z pHat) (hp : ∀ g, 0 < p g)
    {s t : Fin (Fintype.card G)} (ht : s ≤ t) :
    let σ := sortedPriceRatioEquiv pHat p
    Z (hybridPrice pHat p (p (σ s) / pHat (σ s))) (σ t) ≤ 0 := by
  intro σ
  set αs := p (σ s) / pHat (σ s)
  have hαs : 0 < αs := div_pos (hp (σ s)) (heq.1 (σ s))
  have hwgs := hWGS (hybridPrice_pos heq.1 hp hαs) (hybridPrice_le_smul pHat p αs) (σ t)
    (hybridPrice_sorted_of_ge heq.1 ht).symm
  rwa [hH hαs heq.1, hW.eq_zero_of_isWalrasianEquilibrium heq] at hwgs

/-- Between consecutive hybrid levels `s` and `s' = s + 1`, WGS implies that excess demand on the
head `{t | t ≤ s}` is nondecreasing (`Z q^s (σ t) ≤ Z q^{s'} (σ t)`). -/
theorem excessDemand_hybridPrice_le_succ_of_le {Z : (G → ℝ) → G → ℝ}
    (hWGS : IsWeakGrossSubstitutes Z) {pHat p : G → ℝ}
    (hpHat : ∀ g, 0 < pHat g) (hp : ∀ g, 0 < p g)
    {s s' t : Fin (Fintype.card G)} (hss' : s ≤ s') (ht : t ≤ s) :
    let σ := sortedPriceRatioEquiv pHat p
    Z (hybridPrice pHat p (p (σ s) / pHat (σ s))) (σ t) ≤
      Z (hybridPrice pHat p (p (σ s') / pHat (σ s'))) (σ t) := by
  intro σ
  have hq_pos := hybridPrice_pos hpHat hp (div_pos (hp (σ s)) (hpHat (σ s)))
  have hq_le :=
    hybridPrice_mono pHat p (monotone_sortedPriceRatio pHat p hss') fun g => (hpHat g).le
  refine hWGS hq_pos hq_le (σ t) ?_
  rw [hybridPrice_sorted_of_le hpHat (ht.trans hss'), hybridPrice_sorted_of_le hpHat ht]

/-- Exact algebraic identity underlying Equation `(6.5)` of [CodenottiVaradarajan2007], Lemma 6.7,
p. 145: for consecutive sorted indices `s` and `s'` (`s'.val = s.val + 1`), Walras's law on `q^{s'}`
and `q^s` expresses `α_{s'} * (p̂ · Z(q^{s'}) - p̂ · Z(q^s))` as a sum of nonnegative head and tail
terms. -/
private theorem hybridPrice_step_identity {Z : (G → ℝ) → G → ℝ} (hW : SatisfiesWalrasLaw Z)
    {pHat p : G → ℝ} (hpHat : ∀ g, 0 < pHat g) (hp : ∀ g, 0 < p g)
    {s s' : Fin (Fintype.card G)} (hsucc : s'.val = s.val + 1) :
    let σ := sortedPriceRatioEquiv pHat p
    let α := fun t => p (σ t) / pHat (σ t)
    let q := fun t => hybridPrice pHat p (α t)
    α s' * (expenditure pHat (Z (q s')) - expenditure pHat (Z (q s))) =
      (∑ t ∈ univ.filter (· ≤ s),
        (α s' * pHat (σ t) - p (σ t)) * (Z (q s') (σ t) - Z (q s) (σ t))) -
      (∑ t ∈ univ.filter (s < ·),
        (α s' - α s) * pHat (σ t) * Z (q s) (σ t)) := by
  intro σ α q
  have hq_pos : ∀ t, ∀ g, 0 < q t g := fun t =>
    hybridPrice_pos hpHat hp (div_pos (hp (σ t)) (hpHat (σ t)))
  have hw₁ : expenditure (q s') (Z (q s')) = 0 := hW (hq_pos s')
  have hw₂ : expenditure (q s) (Z (q s)) = 0 := hW (hq_pos s)
  have hdiff0 : ∑ t : Fin (Fintype.card G),
      (q s' (σ t) * Z (q s') (σ t) - q s (σ t) * Z (q s) (σ t)) = 0 := by
    rw [sum_sub_distrib, σ.sum_comp (fun g => q s' g * Z (q s') g),
      σ.sum_comp (fun g => q s g * Z (q s) g), ← expenditure_eq_sum, ← expenditure_eq_sum, hw₁, hw₂,
      sub_self]
  have hpHat_diff : expenditure pHat (Z (q s')) - expenditure pHat (Z (q s)) =
      ∑ t : Fin (Fintype.card G), pHat (σ t) * (Z (q s') (σ t) - Z (q s) (σ t)) := by
    rw [← expenditure_sub, expenditure_eq_sum]
    exact (σ.sum_comp (fun g => pHat g * (Z (q s') g - Z (q s) g))).symm
  rw [hpHat_diff, mul_sum]
  have hpart : ∀ f : Fin (Fintype.card G) → ℝ,
      ∑ t : Fin (Fintype.card G), f t =
        (∑ t ∈ univ.filter (· ≤ s), f t) + (∑ t ∈ univ.filter (s < ·), f t) := fun f => by
    simpa only [not_le] using (sum_filter_add_sum_filter_not univ (· ≤ s) f).symm
  rw [hpart] at hdiff0 ⊢
  have hhead : ∑ t ∈ univ.filter (· ≤ s),
      (q s' (σ t) * Z (q s') (σ t) - q s (σ t) * Z (q s) (σ t)) =
      ∑ t ∈ univ.filter (· ≤ s), p (σ t) * (Z (q s') (σ t) - Z (q s) (σ t)) :=
    sum_congr rfl fun t ht => by
      have hts : t ≤ s := (mem_filter.1 ht).2
      have hts' : t ≤ s' := hts.trans (Fin.le_def.2 (by omega))
      dsimp only [q, α, σ]
      rw [hybridPrice_sorted_of_le (p := p) hpHat hts',
        hybridPrice_sorted_of_le (p := p) hpHat hts, mul_sub]
  have htail : ∑ t ∈ univ.filter (s < ·),
      (q s' (σ t) * Z (q s') (σ t) - q s (σ t) * Z (q s) (σ t)) =
      ∑ t ∈ univ.filter (s < ·),
        (α s' * pHat (σ t) * Z (q s') (σ t) - α s * pHat (σ t) * Z (q s) (σ t)) :=
    sum_congr rfl fun t ht => by
      have hst : s < t := (mem_filter.1 ht).2
      have hs't : s' ≤ t := Fin.le_def.2 (hsucc ▸ Nat.succ_le_of_lt hst)
      dsimp only [q, α, σ]
      rw [hybridPrice_sorted_of_ge (p := p) hpHat hs't,
        hybridPrice_sorted_of_ge (p := p) hpHat hst.le]
  rw [hhead, htail] at hdiff0
  have hhead_sub :
      (∑ t ∈ univ.filter (· ≤ s), α s' * (pHat (σ t) * (Z (q s') (σ t) - Z (q s) (σ t)))) -
      (∑ t ∈ univ.filter (· ≤ s), p (σ t) * (Z (q s') (σ t) - Z (q s) (σ t))) =
      ∑ t ∈ univ.filter (· ≤ s),
        (α s' * pHat (σ t) - p (σ t)) * (Z (q s') (σ t) - Z (q s) (σ t)) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun _ _ => by ring
  have htail_sub :
      (∑ t ∈ univ.filter (s < ·), α s' * (pHat (σ t) * (Z (q s') (σ t) - Z (q s) (σ t)))) -
      (∑ t ∈ univ.filter (s < ·),
        (α s' * pHat (σ t) * Z (q s') (σ t) - α s * pHat (σ t) * Z (q s) (σ t))) =
      - (∑ t ∈ univ.filter (s < ·), (α s' - α s) * pHat (σ t) * Z (q s) (σ t)) := by
    rw [← sum_neg_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun _ _ => by ring
  linarith

/-- **Equation `(6.5)`** of [CodenottiVaradarajan2007], Lemma 6.7, p. 145: for consecutive sorted
indices `s` and `s'` (`s'.val = s.val + 1`),
`(1 - α s / α s') * ∑_{t ≤ s} pHat (σ t) * (Z (q s') (σ t) - Z (q s) (σ t)) ≤
  expenditure pHat (Z (q s')) - expenditure pHat (Z (q s))`,
and both sides are nonnegative. -/
theorem expenditure_hybridPrice_step_ge {Z : (G → ℝ) → G → ℝ}
    (hH : IsHomogeneousDegZero Z) (hW : SatisfiesWalrasLaw Z) (hWGS : IsWeakGrossSubstitutes Z)
    {pHat p : G → ℝ} (heq : IsWalrasianEquilibrium Z pHat) (hp : ∀ g, 0 < p g)
    {s s' : Fin (Fintype.card G)} (hsucc : s'.val = s.val + 1) :
    let σ := sortedPriceRatioEquiv pHat p
    let α := fun t => p (σ t) / pHat (σ t)
    let q := fun t => hybridPrice pHat p (α t)
    (1 - α s / α s') *
        (∑ t ∈ univ.filter (· ≤ s), pHat (σ t) * (Z (q s') (σ t) - Z (q s) (σ t))) ≤
      expenditure pHat (Z (q s')) - expenditure pHat (Z (q s)) := by
  intro σ α q
  have hss' : s ≤ s' := by change s.val ≤ s'.val; omega
  have hαs' : 0 < α s' := div_pos (hp (σ s')) (heq.1 (σ s'))
  have hα_le : α s ≤ α s' := monotone_sortedPriceRatio pHat p hss'
  have hid := hybridPrice_step_identity hW heq.1 hp hsucc
  have htail_nonpos :
      ∑ t ∈ univ.filter (s < ·), (α s' - α s) * pHat (σ t) * Z (q s) (σ t) ≤ 0 :=
    sum_nonpos fun t ht => mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (sub_nonneg.2 hα_le) (heq.1 (σ t)).le)
      (excessDemand_hybridPrice_nonpos_of_ge hH hW hWGS heq hp (mem_filter.1 ht).2.le)
  have hhead_ge :
      (α s' - α s) *
          (∑ t ∈ univ.filter (· ≤ s), pHat (σ t) * (Z (q s') (σ t) - Z (q s) (σ t))) ≤
        ∑ t ∈ univ.filter (· ≤ s),
          (α s' * pHat (σ t) - p (σ t)) * (Z (q s') (σ t) - Z (q s) (σ t)) := by
    rw [mul_sum]
    refine sum_le_sum fun t ht => ?_
    have hts : t ≤ s := (mem_filter.1 ht).2
    have hcoef : (α s' - α s) * pHat (σ t) ≤ α s' * pHat (σ t) - p (σ t) := by
      have hp_eq : p (σ t) = α t * pHat (σ t) :=
        (div_mul_cancel₀ (p (σ t)) (heq.1 (σ t)).ne').symm
      have hαt_le : α t ≤ α s := monotone_sortedPriceRatio pHat p hts
      linarith [mul_le_mul_of_nonneg_right hαt_le (heq.1 (σ t)).le]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef
      (sub_nonneg.2 (excessDemand_hybridPrice_le_succ_of_le hWGS heq.1 hp hss' hts))
  have hdiv : ((α s' - α s) / α s') *
      (∑ t ∈ univ.filter (· ≤ s), pHat (σ t) * (Z (q s') (σ t) - Z (q s) (σ t))) ≤
      expenditure pHat (Z (q s')) - expenditure pHat (Z (q s)) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hαs']
    linarith
  rwa [sub_div, div_self hαs'.ne'] at hdiv

theorem expenditure_hybridPrice_step_nonneg {Z : (G → ℝ) → G → ℝ}
    (hH : IsHomogeneousDegZero Z) (hW : SatisfiesWalrasLaw Z) (hWGS : IsWeakGrossSubstitutes Z)
    {pHat p : G → ℝ} (heq : IsWalrasianEquilibrium Z pHat) (hp : ∀ g, 0 < p g)
    {s s' : Fin (Fintype.card G)} (hsucc : s'.val = s.val + 1) :
    let σ := sortedPriceRatioEquiv pHat p
    let α := fun t => p (σ t) / pHat (σ t)
    let q := fun t => hybridPrice pHat p (α t)
    0 ≤ expenditure pHat (Z (q s')) - expenditure pHat (Z (q s)) := by
  intro σ α q
  have hss' : s ≤ s' := by change s.val ≤ s'.val; omega
  have hαs' : 0 < α s' := div_pos (hp (σ s')) (heq.1 (σ s'))
  have hα_le : α s ≤ α s' := monotone_sortedPriceRatio pHat p hss'
  have h1 : 0 ≤ 1 - α s / α s' := sub_nonneg.2 ((div_le_one hαs').2 hα_le)
  have h2 : 0 ≤ ∑ t ∈ univ.filter (· ≤ s), pHat (σ t) * (Z (q s') (σ t) - Z (q s) (σ t)) :=
    sum_nonneg fun t ht => mul_nonneg (heq.1 (σ t)).le
      (sub_nonneg.2 (excessDemand_hybridPrice_le_succ_of_le hWGS heq.1 hp hss' (mem_filter.1 ht).2))
  exact le_trans (mul_nonneg h1 h2) (expenditure_hybridPrice_step_ge hH hW hWGS heq hp hsucc)

private theorem telescope_nat_diff (f : ℕ → ℝ) :
    ∀ m : ℕ, (∑ k ∈ range m, (f (k + 1) - f k)) = f m - f 0
  | 0 => by simp
  | m + 1 => by
    rw [sum_range_succ, telescope_nat_diff f m]
    ring

/-- Telescoping decomposition of `expenditure pHat (Z p)` along the sorted hybrid chain `q^0, …,
q^{n-1}` ([CodenottiVaradarajan2007], Lemma 6.7 proof, p. 146). -/
theorem expenditure_eq_sum_hybridPrice_steps {Z : (G → ℝ) → G → ℝ}
    (hH : IsHomogeneousDegZero Z) (hW : SatisfiesWalrasLaw Z)
    {pHat p : G → ℝ} (heq : IsWalrasianEquilibrium Z pHat) (hp : ∀ g, 0 < p g)
    (h0 : 0 < Fintype.card G) :
    let σ := sortedPriceRatioEquiv pHat p
    let α := fun t => p (σ t) / pHat (σ t)
    let q := fun t => hybridPrice pHat p (α t)
    expenditure pHat (Z p) =
      ∑ k : Fin (Fintype.card G - 1),
        (expenditure pHat (Z (q ⟨k.val + 1, by omega⟩)) -
          expenditure pHat (Z (q ⟨k.val, by omega⟩))) := by
  intro σ α q
  let F : ℕ → ℝ := fun k =>
    if hk : k < Fintype.card G then expenditure pHat (Z (q ⟨k, hk⟩)) else 0
  have hsum : (∑ k : Fin (Fintype.card G - 1),
      (expenditure pHat (Z (q ⟨k.val + 1, by omega⟩)) -
        expenditure pHat (Z (q ⟨k.val, by omega⟩)))) =
      ∑ k ∈ range (Fintype.card G - 1), (F (k + 1) - F k) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun k _ => ?_
    have hk1 : k.val + 1 < Fintype.card G := by omega
    simp [F, hk1, Nat.lt_of_succ_lt hk1]
  rw [hsum, telescope_nat_diff F (Fintype.card G - 1)]
  have hF0 : F 0 = 0 := by
    simp only [F, q, α, σ, h0, ↓reduceDIte, hybridPrice_zero_eq_smul heq.1 h0]
    rw [hH (div_pos (hp _) (heq.1 _)) heq.1, hW.eq_zero_of_isWalrasianEquilibrium heq,
      expenditure_zero_right]
  have hFlast : F (Fintype.card G - 1) = expenditure pHat (Z p) := by
    simp only [F, q, α, σ, Nat.sub_lt h0 Nat.zero_lt_one, ↓reduceDIte,
      hybridPrice_last_eq heq.1 h0]
  linarith

/-- In any WGS excess-demand system satisfying homogeneity and Walras's law, every positive
equilibrium `pHat` and every positive price vector `p` satisfy `0 ≤ expenditure pHat (Z p)`
([CodenottiVaradarajan2007], Equation `(6.6)`, p. 146). -/
theorem IsWeakGrossSubstitutes.expenditure_nonneg_of_isWalrasianEquilibrium
    {Z : (G → ℝ) → G → ℝ} (hH : IsHomogeneousDegZero Z) (hW : SatisfiesWalrasLaw Z)
    (hWGS : IsWeakGrossSubstitutes Z) {pHat p : G → ℝ}
    (heq : IsWalrasianEquilibrium Z pHat) (hp : ∀ g, 0 < p g) :
    0 ≤ expenditure pHat (Z p) := by
  rcases Nat.eq_zero_or_pos (Fintype.card G) with hcard0 | h0
  · have : IsEmpty G := Fintype.card_eq_zero_iff.1 hcard0
    simp [expenditure_eq_sum]
  · rw [expenditure_eq_sum_hybridPrice_steps hH hW heq hp h0]
    exact sum_nonneg fun k _ =>
      expenditure_hybridPrice_step_nonneg hH hW hWGS heq hp (s := ⟨k.val, by omega⟩)
        (s' := ⟨k.val + 1, by omega⟩) rfl

/-- **Arrow–Block–Hurwicz / Arrow–Hurwicz Separating Hyperplane Theorem (Lemma 6.4)**
([ArrowBlockHurwicz1959]; [ArrowHurwicz1960a]; [CodenottiVaradarajan2007], Section 6.3, Lemma 6.4,
pp. 142–143 and Section 6.7, p. 156): if `Z` satisfies degree-`0` homogeneity, Walras's law, and
**weak** gross substitutability, then for every positive Walrasian equilibrium `pHat` and every
positive non-equilibrium price vector `p`, `0 < expenditure pHat (Z p)`. -/
theorem IsWeakGrossSubstitutes.expenditure_pos_of_not_isWalrasianEquilibrium
    {Z : (G → ℝ) → G → ℝ} (hH : IsHomogeneousDegZero Z) (hW : SatisfiesWalrasLaw Z)
    (hWGS : IsWeakGrossSubstitutes Z) {pHat p : G → ℝ}
    (heq : IsWalrasianEquilibrium Z pHat) (hp : ∀ g, 0 < p g)
    (hnot : ¬ IsWalrasianEquilibrium Z p) :
    0 < expenditure pHat (Z p) := by
  have hge0 := hWGS.expenditure_nonneg_of_isWalrasianEquilibrium hH hW heq hp
  refine lt_of_le_of_ne hge0 fun hzero => hnot ?_
  rcases Nat.eq_zero_or_pos (Fintype.card G) with hcard0 | h0
  · have : IsEmpty G := Fintype.card_eq_zero_iff.1 hcard0
    exact ⟨hp, fun g => isEmptyElim g⟩
  · set n := Fintype.card G
    set σ := sortedPriceRatioEquiv pHat p
    set α := fun t : Fin n => p (σ t) / pHat (σ t)
    set q := fun t : Fin n => hybridPrice pHat p (α t)
    have hsum0 : ∑ k : Fin (n - 1),
        (expenditure pHat (Z (q ⟨k.val + 1, by omega⟩)) -
          expenditure pHat (Z (q ⟨k.val, by omega⟩))) = 0 := by
      rw [← expenditure_eq_sum_hybridPrice_steps hH hW heq hp h0]
      exact hzero.symm
    have hstep_nn : ∀ k ∈ (univ : Finset (Fin (n - 1))),
        0 ≤ expenditure pHat (Z (q ⟨k.val + 1, by omega⟩)) -
          expenditure pHat (Z (q ⟨k.val, by omega⟩)) :=
      fun k _ => expenditure_hybridPrice_step_nonneg hH hW hWGS heq hp
        (s := ⟨k.val, by omega⟩) (s' := ⟨k.val + 1, by omega⟩) rfl
    have hstep0 : ∀ (k : ℕ) (hk : k + 1 < n),
        expenditure pHat (Z (q ⟨k + 1, hk⟩)) - expenditure pHat (Z (q ⟨k, by omega⟩)) = 0 := by
      exact fun k hk => (sum_eq_zero_iff_of_nonneg hstep_nn).1 hsum0 ⟨k, by omega⟩ (mem_univ _)
    -- Inductively prove `Z (q ⟨m, hm⟩) = 0` for all `m < n`.
    have hz_all : ∀ (m : ℕ) (hm : m < n), Z (q ⟨m, hm⟩) = 0 := by
      intro m
      induction m with
      | zero =>
        intro hm
        have hq0 : q ⟨0, hm⟩ = α ⟨0, hm⟩ • pHat := hybridPrice_zero_eq_smul heq.1 hm
        have hα0 : 0 < α ⟨0, hm⟩ := div_pos (hp (σ ⟨0, hm⟩)) (heq.1 (σ ⟨0, hm⟩))
        rw [hq0, hH hα0 heq.1]
        exact hW.eq_zero_of_isWalrasianEquilibrium heq
      | succ k ih =>
        intro hk
        set s : Fin n := ⟨k, by omega⟩
        set s' : Fin n := ⟨k + 1, hk⟩
        have hprev : Z (q s) = 0 := ih (by omega)
        rcases eq_or_lt_of_le (monotone_sortedPriceRatio pHat p (show s ≤ s' by
          change k ≤ k + 1; omega)) with hα_eq | hα_lt
        · have hq_eq : q s' = q s := by
            simp only [q, α, σ] at hα_eq ⊢
            rw [← hα_eq]
          rw [hq_eq, hprev]
        · have hαs' : 0 < α s' := div_pos (hp (σ s')) (heq.1 (σ s'))
          have h1_pos : 0 < 1 - α s / α s' := sub_pos.2 ((div_lt_one hαs').2 hα_lt)
          have hge := expenditure_hybridPrice_step_ge hH hW hWGS heq hp (s := s) (s' := s') rfl
          have hdiff_zero := hstep0 k hk
          have hhead_le0 :
              ∑ t ∈ univ.filter (· ≤ s), pHat (σ t) * (Z (q s') (σ t) - Z (q s) (σ t)) ≤ 0 := by
            by_contra! hpos
            linarith [mul_pos h1_pos hpos]
          have hhead_nn : ∀ t ∈ univ.filter (· ≤ s),
              0 ≤ pHat (σ t) * (Z (q s') (σ t) - Z (q s) (σ t)) := fun t ht =>
            mul_nonneg (heq.1 (σ t)).le
              (sub_nonneg.2 (excessDemand_hybridPrice_le_succ_of_le hWGS heq.1 hp
                (show s ≤ s' by change k ≤ k + 1; omega) (mem_filter.1 ht).2))
          have hhead0 : ∑ t ∈ univ.filter (· ≤ s),
              pHat (σ t) * (Z (q s') (σ t) - Z (q s) (σ t)) = 0 :=
            le_antisymm hhead_le0 (sum_nonneg hhead_nn)
          have hq_s'_le0 : ∀ g : G, Z (q s') g ≤ 0 := by
            intro g
            obtain ⟨t, rfl⟩ := σ.surjective g
            by_cases hts : t ≤ s
            · have hsub0 := (mul_eq_zero.1 ((sum_eq_zero_iff_of_nonneg hhead_nn).1 hhead0 t
                (mem_filter.2 ⟨mem_univ t, hts⟩))).resolve_left (heq.1 (σ t)).ne'
              linarith [show Z (q s) (σ t) = 0 from congrFun hprev (σ t)]
            · exact excessDemand_hybridPrice_nonpos_of_ge hH hW hWGS heq hp
                (Nat.succ_le_of_lt (lt_of_not_ge hts))
          have hq_s'_pos : ∀ g, 0 < q s' g := hybridPrice_pos heq.1 hp hαs'
          exact hW.eq_zero_of_isWalrasianEquilibrium ⟨hq_s'_pos, hq_s'_le0⟩
    have hn1 : n - 1 < n := Nat.sub_lt h0 Nat.zero_lt_one
    have hlast : q ⟨n - 1, hn1⟩ = p := hybridPrice_last_eq heq.1 h0
    have hZp : Z p = 0 := hlast ▸ hz_all (n - 1) hn1
    exact (hW.isWalrasianEquilibrium_iff_eq_zero).2 ⟨hp, hZp⟩

/-- Continuous-tâtonnement acute-angle corollary ([CodenottiVaradarajan2007], Section 6.3.1,
p. 143): at any positive non-equilibrium price `p`, the excess-demand direction `Z p` has strictly
positive inner product with `pHat - p`, so the Lyapunov derivative `d/dt (1/2 ‖p - pHat‖_2^2) =
(p - pHat) · Z(p) = - pHat · Z(p) < 0` is strictly negative. -/
theorem IsWeakGrossSubstitutes.expenditure_sub_pos_of_not_isWalrasianEquilibrium
    {Z : (G → ℝ) → G → ℝ} (hH : IsHomogeneousDegZero Z) (hW : SatisfiesWalrasLaw Z)
    (hWGS : IsWeakGrossSubstitutes Z) {pHat p : G → ℝ}
    (heq : IsWalrasianEquilibrium Z pHat) (hp : ∀ g, 0 < p g)
    (hnot : ¬ IsWalrasianEquilibrium Z p) :
    0 < expenditure (pHat - p) (Z p) := by
  have hsub : expenditure (pHat - p) (Z p) = expenditure pHat (Z p) - expenditure p (Z p) := by
    simp only [expenditure_eq_sum, Pi.sub_apply, sub_mul, sum_sub_distrib]
  rw [hsub, hW hp, sub_zero]
  exact hWGS.expenditure_pos_of_not_isWalrasianEquilibrium hH hW heq hp hnot

/-- **NRTV Exercise 6.3** ([CodenottiVaradarajan2007], Section 6.3, p. 143 and Exercise 6.3,
p. 158): under degree-`0` homogeneity, Walras's law, and weak gross substitutability, the set of
positive Walrasian equilibrium price vectors `{p | IsWalrasianEquilibrium Z p}` is convex. -/
theorem IsWeakGrossSubstitutes.convex_setOf_isWalrasianEquilibrium
    {Z : (G → ℝ) → G → ℝ} (hH : IsHomogeneousDegZero Z) (hW : SatisfiesWalrasLaw Z)
    (hWGS : IsWeakGrossSubstitutes Z) :
    Convex ℝ {p : G → ℝ | IsWalrasianEquilibrium Z p} := by
  intro p₁ hp₁ p₂ hp₂ a b ha hb hab
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · obtain rfl : b = 1 := by linarith
    simpa using hp₂
  · rcases eq_or_lt_of_le hb with rfl | hb_pos
    · obtain rfl : a = 1 := by linarith
      simpa using hp₁
    · set p := a • p₁ + b • p₂
      have hp_pos : ∀ g, 0 < p g := fun g =>
        add_pos (mul_pos ha_pos (hp₁.1 g)) (mul_pos hb_pos (hp₂.1 g))
      by_contra hnot
      have h1 := hWGS.expenditure_pos_of_not_isWalrasianEquilibrium hH hW hp₁ hp_pos hnot
      have h2 := hWGS.expenditure_pos_of_not_isWalrasianEquilibrium hH hW hp₂ hp_pos hnot
      have hcomb : expenditure p (Z p) =
          a * expenditure p₁ (Z p) + b * expenditure p₂ (Z p) := by
        simp only [p, expenditure_eq_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
          sum_add_distrib, mul_assoc, ← mul_sum]
      have hw : expenditure p (Z p) = 0 := hW hp_pos
      nlinarith

end SeparatingHyperplane

/-! ### Cobb–Douglas utilities, Marshallian demand, and LP equilibrium characterization -/

section CobbDouglas

variable {G : Type*} [Fintype G]

/-- **Cobb–Douglas utility function** `∏ g, (b g) ^ (α g)` ([CodenottiVaradarajan2007],
Section 6.1.5, p. 139). -/
noncomputable def cobbDouglasUtility (α b : G → ℝ) : ℝ :=
  ∏ g : G, (b g) ^ (α g)

theorem cobbDouglasUtility_eq_prod (α b : G → ℝ) :
    cobbDouglasUtility α b = ∏ g : G, (b g) ^ (α g) := by rfl

theorem cobbDouglasUtility_nonneg {α b : G → ℝ} (hb : ∀ g, 0 ≤ b g) :
    0 ≤ cobbDouglasUtility α b :=
  prod_nonneg fun g _ => Real.rpow_nonneg (hb g) (α g)

/-- Homogeneous-of-degree-`1` scaling of Cobb–Douglas utility when `∑ g, α g = 1`
([CodenottiVaradarajan2007], Section 6.1.5, p. 139). -/
theorem cobbDouglasUtility_smul {α b : G → ℝ} (hα_sum : ∑ g : G, α g = 1)
    (hb : ∀ g, 0 ≤ b g) {c : ℝ} (hc : 0 < c) :
    cobbDouglasUtility α (c • b) = c * cobbDouglasUtility α b := by
  simp only [cobbDouglasUtility, Pi.smul_apply, smul_eq_mul]
  simp_rw [fun g => Real.mul_rpow hc.le (hb g), prod_mul_distrib, ← Real.rpow_sum_of_pos hc,
    hα_sum, Real.rpow_one]

/-- Explicit **Cobb–Douglas Marshallian demand** `α g * m / p g` ([CodenottiVaradarajan2007],
Section 6.1.5, p. 139; Exercise 6.1, p. 158): a Cobb–Douglas consumer spends fraction `α g` of
budget `m` on good `g`. -/
noncomputable def cobbDouglasDemand (α p : G → ℝ) (m : ℝ) (g : G) : ℝ :=
  α g * m / p g

omit [Fintype G] in
@[simp] theorem cobbDouglasDemand_apply (α p : G → ℝ) (m : ℝ) (g : G) :
    cobbDouglasDemand α p m g = α g * m / p g := by rfl

theorem expenditure_cobbDouglasDemand {α p : G → ℝ} (hα_sum : ∑ g : G, α g = 1)
    (hp : ∀ g, 0 < p g) (m : ℝ) :
    expenditure p (cobbDouglasDemand α p m) = m := by
  rw [expenditure_eq_sum]
  simp_rw [cobbDouglasDemand_apply, fun g => mul_div_cancel₀ (α g * m) (hp g).ne',
    ← sum_mul, hα_sum, one_mul]

/-- At strictly positive prices, `0` is the unique bundle budget-feasible within income `0`. -/
theorem IsBudgetFeasible.eq_zero_of_zero {p b : G → ℝ}
    (hp : ∀ g, 0 < p g) (hb : IsBudgetFeasible p 0 b) : b = 0 := by
  funext g
  by_contra hne
  have hpos : 0 < b g := lt_of_le_of_ne (hb.1 g) (Ne.symm hne)
  have hle : p g * b g ≤ expenditure p b := by
    rw [expenditure_eq_sum]
    exact single_le_sum (fun k _ => mul_nonneg (hp k).le (hb.1 k)) (mem_univ g)
  linarith [mul_pos (hp g) hpos, hb.2]

/-- **NRTV Exercise 6.1 (Cobb–Douglas optimality)** ([CodenottiVaradarajan2007], p. 158): for
nonnegative exponents `α` summing to `1`, strictly positive prices `p > 0`, and budget `m ≥ 0`,
`cobbDouglasDemand α p m` belongs to `demandSet (cobbDouglasUtility α) p m`. -/
theorem cobbDouglasDemand_mem_demandSet {α p : G → ℝ} {m : ℝ}
    (hα_nn : ∀ g, 0 ≤ α g) (hα_sum : ∑ g : G, α g = 1) (hp : ∀ g, 0 < p g) (hm : 0 ≤ m) :
    cobbDouglasDemand α p m ∈ demandSet (cobbDouglasUtility α) p m := by
  classical
  set xStar := cobbDouglasDemand α p m
  have hx_nn : ∀ g, 0 ≤ xStar g := fun g =>
    div_nonneg (mul_nonneg (hα_nn g) hm) (hp g).le
  have hx_exp : expenditure p xStar = m := expenditure_cobbDouglasDemand hα_sum hp m
  rw [mem_demandSet]
  refine ⟨⟨hx_nn, hx_exp.le⟩, fun b hb => ?_⟩
  rcases eq_or_lt_of_le hm with rfl | hm_pos
  · have hx0 : xStar = 0 := funext fun g => by simp [xStar, cobbDouglasDemand_apply]
    rw [hb.eq_zero_of_zero hp, hx0]
  · by_cases hzero_supp : ∃ g : G, 0 < α g ∧ b g = 0
    · obtain ⟨g₀, hαg₀, hbg₀⟩ := hzero_supp
      rw [cobbDouglasUtility_eq_prod,
        prod_eq_zero (mem_univ g₀) ((congrArg (· ^ α g₀) hbg₀).trans (Real.zero_rpow hαg₀.ne'))]
      exact cobbDouglasUtility_nonneg hx_nn
    · push Not at hzero_supp
      set S : Finset G := univ.filter (fun g => 0 < α g)
      have hS_sum : ∑ g ∈ S, α g = 1 := by
        rw [← hα_sum, ← sum_filter_add_sum_filter_not univ (fun g => 0 < α g) α,
          sum_eq_zero fun g hg => le_antisymm (not_lt.1 (mem_filter.1 hg).2) (hα_nn g), add_zero]
      have hprod_eq : ∀ y : G → ℝ, cobbDouglasUtility α y = ∏ g ∈ S, (y g) ^ (α g) := by
        intro y
        rw [cobbDouglasUtility_eq_prod, ← prod_filter_mul_prod_filter_not univ (fun g => 0 < α g)]
        have hrest : ∏ g ∈ univ.filter (fun g => ¬ 0 < α g), (y g) ^ (α g) = 1 :=
          prod_eq_one fun g hg => by
            rw [le_antisymm (not_lt.1 (mem_filter.1 hg).2) (hα_nn g), Real.rpow_zero]
        rw [hrest, mul_one]
      have hx_pos : ∀ g ∈ S, 0 < xStar g := fun g hg =>
        div_pos (mul_pos (mem_filter.1 hg).2 hm_pos) (hp g)
      let z : G → ℝ := fun g => b g / xStar g
      have hz_nn : ∀ g ∈ S, 0 ≤ z g := fun g hg => div_nonneg (hb.1 g) (hx_pos g hg).le
      have hamgm := Real.geom_mean_le_arith_mean_weighted S α z
        (fun g _ => hα_nn g) hS_sum hz_nn
      have harith_le : ∑ g ∈ S, α g * z g ≤ 1 := by
        have hterm : ∀ g ∈ S, α g * z g = p g * b g / m := fun g hg => by
          dsimp only [z, xStar]
          rw [cobbDouglasDemand_apply]
          field_simp [(mem_filter.1 hg).2.ne', hm_pos.ne', (hp g).ne']
        rw [sum_congr rfl hterm, ← sum_div]
        have hsub : ∑ g ∈ S, p g * b g ≤ expenditure p b := by
          rw [expenditure_eq_sum]
          exact sum_le_sum_of_subset_of_nonneg (subset_univ S)
            fun g _ _ => mul_nonneg (hp g).le (hb.1 g)
        exact (div_le_one hm_pos).2 (hsub.trans hb.2)
      have hprod_z : ∏ g ∈ S, (z g) ^ (α g) =
          (∏ g ∈ S, (b g) ^ (α g)) / (∏ g ∈ S, (xStar g) ^ (α g)) := by
        rw [← prod_div_distrib]
        exact prod_congr rfl fun g hg => Real.div_rpow (hb.1 g) (hx_pos g hg).le (α g)
      have hden_pos : 0 < ∏ g ∈ S, (xStar g) ^ (α g) :=
        prod_pos fun g hg => Real.rpow_pos_of_pos (hx_pos g hg) (α g)
      rw [hprod_eq b, hprod_eq xStar]
      exact (div_le_one hden_pos).1 (by linarith)

/-- **Strict uniqueness of Cobb–Douglas Marshallian demand** ([CodenottiVaradarajan2007],
Section 6.1.5, p. 139; Exercise 6.1, p. 158): when every exponent `α g` is strictly positive,
`cobbDouglasDemand α p m` is the **unique** optimal bundle in
`demandSet (cobbDouglasUtility α) p m`. -/
theorem demandSet_cobbDouglasUtility_eq {α p : G → ℝ} {m : ℝ}
    (hα_pos : ∀ g, 0 < α g) (hα_sum : ∑ g : G, α g = 1) (hp : ∀ g, 0 < p g) (hm : 0 ≤ m) :
    demandSet (cobbDouglasUtility α) p m = {cobbDouglasDemand α p m} := by
  have hα_nn : ∀ g, 0 ≤ α g := fun g => (hα_pos g).le
  refine Set.Subset.antisymm (fun b hb => ?_) ?_
  · rw [mem_demandSet] at hb
    rw [Set.mem_singleton_iff]
    set xStar := cobbDouglasDemand α p m
    have hx_mem := (mem_demandSet).1 (cobbDouglasDemand_mem_demandSet hα_nn hα_sum hp hm)
    rcases eq_or_lt_of_le hm with rfl | hm_pos
    · rw [hb.1.eq_zero_of_zero hp]
      exact funext fun g => by simp [xStar, cobbDouglasDemand_apply]
    · have hx_pos : ∀ g, 0 < xStar g := fun g =>
        div_pos (mul_pos (hα_pos g) hm_pos) (hp g)
      have hux_pos : 0 < cobbDouglasUtility α xStar :=
        prod_pos fun g _ => Real.rpow_pos_of_pos (hx_pos g) (α g)
      have hge_x : cobbDouglasUtility α xStar ≤ cobbDouglasUtility α b := hb.2 xStar hx_mem.1
      let z : G → ℝ := fun g => b g / xStar g
      have hz_nn : ∀ g ∈ (univ : Finset G), 0 ≤ z g :=
        fun g _ => div_nonneg (hb.1.1 g) (hx_pos g).le
      have hprod_z : ∏ g : G, (z g) ^ (α g) =
          cobbDouglasUtility α b / cobbDouglasUtility α xStar := by
        simp only [cobbDouglasUtility_eq_prod, ← prod_div_distrib]
        exact prod_congr rfl fun g _ => Real.div_rpow (hb.1.1 g) (hx_pos g).le (α g)
      have h1_le_gm : 1 ≤ ∏ g : G, (z g) ^ (α g) := hprod_z ▸ (one_le_div hux_pos).2 hge_x
      have hgm_le_am := Real.geom_mean_le_arith_mean_weighted univ α z
        (fun g _ => hα_nn g) hα_sum hz_nn
      have ham_eq : ∑ g : G, α g * z g = expenditure p b / m := by
        rw [expenditure_eq_sum, sum_div]
        refine sum_congr rfl fun g _ => ?_
        dsimp only [z, xStar]
        rw [cobbDouglasDemand_apply]
        field_simp [(hα_pos g).ne', hm_pos.ne', (hp g).ne']
      have ham_le_1 : ∑ g : G, α g * z g ≤ 1 := ham_eq ▸ (div_le_one hm_pos).2 hb.1.2
      have ham_eq_1 : ∑ g : G, α g * z g = 1 :=
        le_antisymm ham_le_1 (h1_le_gm.trans hgm_le_am)
      have hz_const : ∀ j ∈ (univ : Finset G), z j = ∑ g : G, α g * z g := by
        by_contra! hnot
        have hlt := (Real.geom_mean_lt_arith_mean_weighted_iff_of_pos' univ α z
          (fun g _ => hα_pos g) hα_sum hz_nn).2 hnot
        linarith
      exact funext fun j =>
        (div_eq_one_iff_eq (hx_pos j).ne').1 ((hz_const j (mem_univ j)).trans ham_eq_1)
  · rw [Set.singleton_subset_iff]
    exact cobbDouglasDemand_mem_demandSet hα_nn hα_sum hp hm

/-- Individual excess demand of a Cobb–Douglas trader with endowment `w ≥ 0` and weights `α ≥ 0`
satisfies weak gross substitutability. -/
theorem isWeakGrossSubstitutes_cobbDouglasExcessDemand {α w : G → ℝ}
    (hα_nn : ∀ g, 0 ≤ α g) (hw_nn : ∀ g, 0 ≤ w g) :
    IsWeakGrossSubstitutes (fun p g => cobbDouglasDemand α p (expenditure p w) g - w g) := by
  refine IsWeakGrossSubstitutes.sub_const (fun p p' hp hle g hfg => ?_) w
  simp only [cobbDouglasDemand_apply, hfg]
  have hexp_le : expenditure p w ≤ expenditure p' w := by
    simp only [expenditure_eq_sum]
    exact sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hle k) (hw_nn k)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp_le (hα_nn g)) (hp g).le

/-- A **Cobb–Douglas Arrow–Debreu exchange economy** ([CodenottiVaradarajan2007], Section 6.1.5,
p. 139; Exercise 6.2, p. 158): each trader `i : I` has nonnegative endowment `endowment i` and
nonnegative Cobb–Douglas expenditure shares `weight i` summing to `1`. -/
structure CobbDouglasExchangeMarket (I G : Type*) [Fintype G] where
  /-- Initial endowment `endowment i g` of good `g` held by trader `i`. -/
  endowment : I → G → ℝ
  /-- Expenditure-share exponent `weight i g` placed by trader `i` on good `g`. -/
  weight : I → G → ℝ
  /-- Initial endowments are nonnegative. -/
  endowment_nonneg : ∀ (i : I) (g : G), 0 ≤ endowment i g
  /-- Expenditure shares are nonnegative. -/
  weight_nonneg : ∀ (i : I) (g : G), 0 ≤ weight i g
  /-- Each trader's expenditure shares sum to `1`. -/
  sum_weight : ∀ i : I, ∑ g : G, weight i g = 1

namespace CobbDouglasExchangeMarket

variable {I : Type*} [Fintype I] (E : CobbDouglasExchangeMarket I G)

/-- View `E` as an `ExchangeMarket I G` with `cobbDouglasUtility (E.weight i)`. -/
noncomputable def toExchangeMarket : ExchangeMarket I G where
  endowment := E.endowment
  utility i := cobbDouglasUtility (E.weight i)
  endowment_nonneg := E.endowment_nonneg

omit [Fintype I] in
@[simp] theorem toExchangeMarket_endowment : E.toExchangeMarket.endowment = E.endowment := by rfl

omit [Fintype I] in
@[simp] theorem toExchangeMarket_utility (i : I) :
    E.toExchangeMarket.utility i = cobbDouglasUtility (E.weight i) := by rfl

/-- Single-valued aggregate excess-demand function `Z(p)_g = ∑_i α_{ig} (p · w_i) / p_g - W_g` of
Cobb–Douglas exchange economy `E`. -/
noncomputable def excessDemandFn (p : G → ℝ) (g : G) : ℝ :=
  (∑ i : I, cobbDouglasDemand (E.weight i) p (expenditure p (E.endowment i)) g) -
    E.toExchangeMarket.totalSupply g

theorem excessDemandFn_eq (p : G → ℝ) (g : G) :
    E.excessDemandFn p g =
      (∑ i : I, E.weight i g * expenditure p (E.endowment i) / p g) -
        E.toExchangeMarket.totalSupply g := by rfl

theorem isHomogeneousDegZero_excessDemandFn : IsHomogeneousDegZero E.excessDemandFn := by
  intro c hc p hp
  funext g
  simp only [excessDemandFn_eq, expenditure_smul_left, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  have hpg := (hp g).ne'
  field_simp [hc.ne', hpg]

theorem satisfiesWalrasLaw_excessDemandFn : SatisfiesWalrasLaw E.excessDemandFn := by
  intro p hp
  rw [expenditure_eq_sum]
  have hterm : ∀ g : G, p g * E.excessDemandFn p g =
      (∑ i : I, E.weight i g * expenditure p (E.endowment i)) -
        p g * E.toExchangeMarket.totalSupply g := fun g => by
    rw [excessDemandFn_eq, mul_sub, mul_sum]
    exact congrArg (· - _) (sum_congr rfl fun i _ => mul_div_cancel₀ _ (hp g).ne')
  simp_rw [hterm, sum_sub_distrib]
  have hswap : (∑ g : G, ∑ i : I, E.weight i g * expenditure p (E.endowment i)) =
      ∑ i : I, expenditure p (E.endowment i) := by
    rw [sum_comm]
    exact sum_congr rfl fun i _ => by rw [← sum_mul, E.sum_weight i, one_mul]
  rw [hswap]
  have hinc := E.toExchangeMarket.sum_income p
  simp only [ExchangeMarket.income_eq, toExchangeMarket_endowment, expenditure_eq_sum] at hinc ⊢
  linarith

theorem isWeakGrossSubstitutes_excessDemandFn : IsWeakGrossSubstitutes E.excessDemandFn := by
  refine IsWeakGrossSubstitutes.sub_const ?_ E.toExchangeMarket.totalSupply
  intro p p' hp hle g hfg
  refine sum_le_sum fun i _ => ?_
  have hw := isWeakGrossSubstitutes_cobbDouglasExcessDemand (E.weight_nonneg i)
    (E.endowment_nonneg i) hp hle g hfg
  linarith

/-- If for every pair of distinct goods `j ≠ g` some trader holds a positive endowment of `j` and
puts positive Cobb–Douglas weight on `g`, then `E.excessDemandFn` satisfies **strict** gross
substitutability (and hence has a unique positive equilibrium price ray). -/
theorem isGrossSubstitutes_excessDemandFn
    (hconn : ∀ g j : G, j ≠ g → ∃ i : I, 0 < E.weight i g ∧ 0 < E.endowment i j) :
    IsGrossSubstitutes E.excessDemandFn := by
  refine IsGrossSubstitutes.sub_const ?_ E.toExchangeMarket.totalSupply
  intro p p' hp hle ⟨j, hj_lt⟩ g hfg
  have hj_ne_g : j ≠ g := fun heq => (ne_of_lt hj_lt) (heq ▸ hfg).symm
  obtain ⟨i₀, hwi₀, hei₀⟩ := hconn g j hj_ne_g
  refine sum_lt_sum (fun i _ => ?_) ⟨i₀, mem_univ i₀, ?_⟩
  · have hw := isWeakGrossSubstitutes_cobbDouglasExcessDemand (E.weight_nonneg i)
      (E.endowment_nonneg i) hp hle g hfg
    linarith
  · simp only [cobbDouglasDemand_apply, hfg]
    have hexp_lt : expenditure p (E.endowment i₀) < expenditure p' (E.endowment i₀) := by
      simp only [expenditure_eq_sum]
      exact sum_lt_sum
        (fun k _ => mul_le_mul_of_nonneg_right (hle k) (E.endowment_nonneg i₀ k))
        ⟨j, mem_univ j, mul_lt_mul_of_pos_right hj_lt hei₀⟩
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hexp_lt hwi₀) (hp g)

/-- **NRTV Exercise 6.2** ([CodenottiVaradarajan2007], p. 158): strictly positive prices `p > 0`
form a Walrasian equilibrium of Cobb–Douglas exchange economy `E` if and only if `p` satisfies the
`|G|` homogeneous linear inequalities
`∑ i, E.weight i g * expenditure p (E.endowment i) ≤ p g * E.toExchangeMarket.totalSupply g`
(equivalently, exact linear equalities, by Walras's law). -/
theorem isWalrasianEquilibrium_iff_linearInequalities {p : G → ℝ} (hp : ∀ g, 0 < p g) :
    IsWalrasianEquilibrium E.excessDemandFn p ↔
      ∀ g : G, ∑ i : I, E.weight i g * expenditure p (E.endowment i) ≤
        p g * E.toExchangeMarket.totalSupply g := by
  rw [IsWalrasianEquilibrium, and_iff_right hp]
  refine forall_congr' fun g => ?_
  rw [excessDemandFn_eq, sub_nonpos, ← sum_div, div_le_iff₀ (hp g), mul_comm]

theorem isWalrasianEquilibrium_iff_linearEquations {p : G → ℝ} (hp : ∀ g, 0 < p g) :
    IsWalrasianEquilibrium E.excessDemandFn p ↔
      ∀ g : G, ∑ i : I, E.weight i g * expenditure p (E.endowment i) =
        p g * E.toExchangeMarket.totalSupply g := by
  rw [E.satisfiesWalrasLaw_excessDemandFn.isWalrasianEquilibrium_iff_eq_zero,
    and_iff_right hp, funext_iff]
  refine forall_congr' fun g => ?_
  rw [Pi.zero_apply, excessDemandFn_eq, ← sum_div, sub_eq_zero, div_eq_iff (hp g).ne', mul_comm]

/-- Any positive Walrasian equilibrium `p` of `E.excessDemandFn` induces a full competitive
equilibrium `(x, p)` of `E.toExchangeMarket` at
`x i = cobbDouglasDemand (E.weight i) p (income p i)`. -/
theorem isCompetitiveEquilibrium_of_isWalrasianEquilibrium {p : G → ℝ}
    (heq : IsWalrasianEquilibrium E.excessDemandFn p) :
    E.toExchangeMarket.IsCompetitiveEquilibrium
      (fun i => cobbDouglasDemand (E.weight i) p (E.toExchangeMarket.income p i)) p := by
  have hz0 := E.satisfiesWalrasLaw_excessDemandFn.eq_zero_of_isWalrasianEquilibrium heq
  have hex_eq : ∀ g : G,
      E.toExchangeMarket.excessDemand
        (fun i => cobbDouglasDemand (E.weight i) p (E.toExchangeMarket.income p i)) g =
        E.excessDemandFn p g := fun g => by
    simp [ExchangeMarket.excessDemand_eq, excessDemandFn, ExchangeMarket.income_eq]
  refine ⟨fun g => (heq.1 g).le, fun i => ?_, fun g => ?_, fun g => ?_⟩
  · rw [ExchangeMarket.mem_demandSet, toExchangeMarket_utility]
    exact cobbDouglasDemand_mem_demandSet (E.weight_nonneg i) (E.sum_weight i) heq.1
      (E.toExchangeMarket.income_nonneg (fun g => (heq.1 g).le) i)
  · rw [hex_eq, hz0]
    exact le_rfl
  · rw [hex_eq, hz0, Pi.zero_apply, mul_zero]

end CobbDouglasExchangeMarket

end CobbDouglas

/-! ### Constant-elasticity-of-substitution (CES) utilities and demand formula `(6.7)` -/

section CES

variable {G : Type*} [Fintype G]

/-- **Constant-elasticity-of-substitution (CES) utility function** ([CodenottiVaradarajan2007],
Section 6.1.5, p. 139 and Section 6.4.2, p. 149): for `ρ < 0`, `cesUtility α ρ b = 0` whenever some
coordinate `b g ≤ 0` (ensuring continuity on `ℝ_+^G`); otherwise
`(∑ g, α g * (b g) ^ ρ) ^ (1 / ρ)`. -/
noncomputable def cesUtility (α : G → ℝ) (ρ : ℝ) (b : G → ℝ) : ℝ :=
  open Classical in
  if ρ < 0 ∧ ∃ g : G, b g ≤ 0 then 0 else (∑ g : G, α g * (b g) ^ ρ) ^ (1 / ρ)

theorem cesUtility_of_pos_exp {α : G → ℝ} {ρ : ℝ} (hρ : 0 < ρ) (b : G → ℝ) :
    cesUtility α ρ b = (∑ g : G, α g * (b g) ^ ρ) ^ (1 / ρ) := by
  unfold cesUtility
  exact ite_eq_right_iff.2 fun h => (not_lt_of_gt hρ h.1).elim

theorem cesUtility_of_bundle_pos (α : G → ℝ) (ρ : ℝ) {b : G → ℝ} (hb : ∀ g, 0 < b g) :
    cesUtility α ρ b = (∑ g : G, α g * (b g) ^ ρ) ^ (1 / ρ) := by
  unfold cesUtility
  exact ite_eq_right_iff.2 fun ⟨_, g, hg⟩ => (not_le_of_gt (hb g) hg).elim

theorem cesUtility_of_neg_of_exists_nonpos (α : G → ℝ) {ρ : ℝ} (hρ : ρ < 0) {b : G → ℝ}
    (hb : ∃ g : G, b g ≤ 0) : cesUtility α ρ b = 0 := by
  unfold cesUtility
  exact ite_eq_left_iff.2 fun h => (h ⟨hρ, hb⟩).elim

theorem cesUtility_nonneg {α b : G → ℝ} (hα : ∀ g, 0 ≤ α g) (ρ : ℝ) (hb : ∀ g, 0 ≤ b g) :
    0 ≤ cesUtility α ρ b := by
  unfold cesUtility
  split_ifs
  · exact le_rfl
  · exact Real.rpow_nonneg (sum_nonneg fun g _ => mul_nonneg (hα g) (Real.rpow_nonneg (hb g) ρ)) _

/-- Explicit **CES Marshallian demand** formula `(6.7)` ([CodenottiVaradarajan2007], Section 6.4.2,
p. 149; Exercise 6.1, p. 158):
`x_g(p, m) = (α_g / p_g)^{1 / (1 - ρ)} * m / ∑_k α_k^{1 / (1 - ρ)} p_k^{- ρ / (1 - ρ)}`. -/
noncomputable def cesDemand (α : G → ℝ) (ρ : ℝ) (p : G → ℝ) (m : ℝ) (g : G) : ℝ :=
  ((α g) ^ (1 / (1 - ρ)) / (p g) ^ (1 / (1 - ρ))) *
    (m / ∑ k : G, (α k) ^ (1 / (1 - ρ)) * (p k) ^ (- ρ / (1 - ρ)))

@[simp] theorem cesDemand_apply (α : G → ℝ) (ρ : ℝ) (p : G → ℝ) (m : ℝ) (g : G) :
    cesDemand α ρ p m g =
      ((α g) ^ (1 / (1 - ρ)) / (p g) ^ (1 / (1 - ρ))) *
        (m / ∑ k : G, (α k) ^ (1 / (1 - ρ)) * (p k) ^ (- ρ / (1 - ρ))) := by rfl

theorem expenditure_cesDemand [Nonempty G] {α p : G → ℝ} {ρ : ℝ}
    (hα : ∀ g, 0 < α g) (hρ_lt : ρ < 1) (hp : ∀ g, 0 < p g) (m : ℝ) :
    expenditure p (cesDemand α ρ p m) = m := by
  have h10 : 1 - ρ ≠ 0 := by linarith
  set D : ℝ := ∑ k : G, (α k) ^ (1 / (1 - ρ)) * (p k) ^ (- ρ / (1 - ρ))
  have hD_pos : 0 < D := sum_pos
    (fun k _ => mul_pos (Real.rpow_pos_of_pos (hα k) _) (Real.rpow_pos_of_pos (hp k) _))
    univ_nonempty
  rw [expenditure_eq_sum]
  have hterm : ∀ g : G, p g * cesDemand α ρ p m g =
      ((α g) ^ (1 / (1 - ρ)) * (p g) ^ (- ρ / (1 - ρ))) * (m / D) := by
    intro g
    simp only [cesDemand_apply]
    change p g * (((α g) ^ (1 / (1 - ρ)) / (p g) ^ (1 / (1 - ρ))) * (m / D)) = _
    have hp_pow : p g / (p g) ^ (1 / (1 - ρ)) = (p g) ^ (- ρ / (1 - ρ)) :=
      calc p g / (p g) ^ (1 / (1 - ρ))
          = (p g) ^ (1 - 1 / (1 - ρ)) := by rw [Real.rpow_sub (hp g), Real.rpow_one]
        _ = (p g) ^ (- ρ / (1 - ρ)) := by
            congr 1
            field_simp [h10]
            ring
    calc
      p g * (((α g) ^ (1 / (1 - ρ)) / (p g) ^ (1 / (1 - ρ))) * (m / D)) =
          (α g) ^ (1 / (1 - ρ)) * (p g / (p g) ^ (1 / (1 - ρ))) * (m / D) := by ring
      _ = ((α g) ^ (1 / (1 - ρ)) * (p g) ^ (- ρ / (1 - ρ))) * (m / D) := by rw [hp_pow]
  simp_rw [hterm, ← sum_mul]
  change D * (m / D) = m
  exact mul_div_cancel₀ m hD_pos.ne'

/-- **NRTV Exercise 6.1 (CES demand optimality, Equation `(6.7)`)** ([CodenottiVaradarajan2007],
Section 6.4.2, p. 149 and Exercise 6.1, p. 158): for strictly positive utility weights `α > 0`,
exponent `ρ < 1` with `ρ ≠ 0`, strictly positive prices `p > 0`, and budget `m ≥ 0`, the closed-form
vector `cesDemand α ρ p m` belongs to `demandSet (cesUtility α ρ) p m`. -/
theorem cesDemand_mem_demandSet [Nonempty G] {α p : G → ℝ} {ρ m : ℝ}
    (hα : ∀ g, 0 < α g) (hρ_lt : ρ < 1) (hρ_ne : ρ ≠ 0) (hp : ∀ g, 0 < p g) (hm : 0 ≤ m) :
    cesDemand α ρ p m ∈ demandSet (cesUtility α ρ) p m := by
  set D : ℝ := ∑ k : G, (α k) ^ (1 / (1 - ρ)) * (p k) ^ (- ρ / (1 - ρ))
  have hD_pos : 0 < D := sum_pos
    (fun k _ => mul_pos (Real.rpow_pos_of_pos (hα k) _) (Real.rpow_pos_of_pos (hp k) _))
    univ_nonempty
  set xStar := cesDemand α ρ p m
  have hx_nn : ∀ g, 0 ≤ xStar g := fun g =>
    mul_nonneg
      (div_nonneg (Real.rpow_nonneg (hα g).le _) (Real.rpow_nonneg (hp g).le _))
      (div_nonneg hm hD_pos.le)
  have hx_exp : expenditure p xStar = m := expenditure_cesDemand hα hρ_lt hp m
  rw [mem_demandSet]
  refine ⟨⟨hx_nn, hx_exp.le⟩, fun b hb => ?_⟩
  have h1ρ_pos : 0 < 1 - ρ := by linarith
  have hρ1_ne : ρ - 1 ≠ 0 := by linarith
  rcases eq_or_lt_of_le hm with rfl | hm_pos
  · have hx0 : xStar = 0 := funext fun g => by simp [xStar, cesDemand_apply]
    rw [hb.eq_zero_of_zero hp, hx0]
  · -- First evaluate `cesUtility α ρ xStar = m * D ^ ((1 - ρ) / ρ)`.
    have hx_pos : ∀ g, 0 < xStar g := fun g =>
      mul_pos
        (div_pos (Real.rpow_pos_of_pos (hα g) _) (Real.rpow_pos_of_pos (hp g) _))
        (div_pos hm_pos hD_pos)
    have hux : cesUtility α ρ xStar = m * D ^ ((1 - ρ) / ρ) := by
      rw [cesUtility_of_bundle_pos α ρ hx_pos]
      have hterm : ∀ g : G, α g * (xStar g) ^ ρ =
          ((α g) ^ (1 / (1 - ρ)) * (p g) ^ (- ρ / (1 - ρ))) * (m / D) ^ ρ := by
        intro g
        have hαg := hα g
        have hpg := hp g
        have hmD : 0 < m / D := div_pos hm_pos hD_pos
        dsimp only [xStar]
        rw [cesDemand_apply,
          Real.mul_rpow
            (div_nonneg (Real.rpow_nonneg hαg.le _) (Real.rpow_nonneg hpg.le _)) hmD.le,
          Real.div_rpow (Real.rpow_nonneg hαg.le _) (Real.rpow_nonneg hpg.le _),
          ← Real.rpow_mul hαg.le, ← Real.rpow_mul hpg.le]
        have hα_pow : α g * ((α g) ^ (1 / (1 - ρ) * ρ) / (p g) ^ (1 / (1 - ρ) * ρ)) =
            (α g) ^ (1 / (1 - ρ)) * (p g) ^ (- ρ / (1 - ρ)) := by
          have h1 : α g * (α g) ^ (1 / (1 - ρ) * ρ) = (α g) ^ (1 / (1 - ρ)) :=
            calc
              α g * (α g) ^ (1 / (1 - ρ) * ρ) = (α g) ^ (1 + 1 / (1 - ρ) * ρ) := by
                rw [Real.rpow_add hαg, Real.rpow_one]
              _ = (α g) ^ (1 / (1 - ρ)) := by
                congr 1
                field_simp [h1ρ_pos.ne']
                ring
          have h2 : ((p g) ^ (1 / (1 - ρ) * ρ))⁻¹ = (p g) ^ (- ρ / (1 - ρ)) := by
            rw [← Real.rpow_neg hpg.le]
            congr 1
            field_simp [h1ρ_pos.ne']
          rw [div_eq_mul_inv, ← mul_assoc, h1, h2]
        calc
          α g * (((α g) ^ (1 / (1 - ρ) * ρ) / (p g) ^ (1 / (1 - ρ) * ρ)) * (m / D) ^ ρ) =
              (α g * ((α g) ^ (1 / (1 - ρ) * ρ) / (p g) ^ (1 / (1 - ρ) * ρ))) * (m / D) ^ ρ := by
            ring
          _ = ((α g) ^ (1 / (1 - ρ)) * (p g) ^ (- ρ / (1 - ρ))) * (m / D) ^ ρ := by rw [hα_pow]
      simp_rw [hterm, ← sum_mul]
      change (D * (m / D) ^ ρ) ^ (1 / ρ) = m * D ^ ((1 - ρ) / ρ)
      rw [Real.mul_rpow hD_pos.le (Real.rpow_nonneg (div_pos hm_pos hD_pos).le _),
        ← Real.rpow_mul (div_pos hm_pos hD_pos).le, mul_one_div_cancel hρ_ne, Real.rpow_one]
      have hD_exp : D ^ (1 / ρ) * D⁻¹ = D ^ ((1 - ρ) / ρ) := by
        rw [← Real.rpow_neg_one D, ← Real.rpow_add hD_pos]
        congr 1
        field_simp [hρ_ne]
        ring
      calc D ^ (1 / ρ) * (m / D) = m * (D ^ (1 / ρ) * D⁻¹) := by ring
        _ = m * D ^ ((1 - ρ) / ρ) := by rw [hD_exp]
    -- Now bound `cesUtility α ρ b ≤ m * D ^ ((1 - ρ) / ρ)` via ReverseHolder!
    let f : G → ℝ := fun g => (α g) ^ (1 / ρ) * b g
    let k : G → ℝ := fun g => p g * (α g) ^ (- (1 / ρ))
    have hk_pos : ∀ g, 0 < k g := fun g =>
      mul_pos (hp g) (Real.rpow_pos_of_pos (hα g) _)
    have hfk : ∀ g, f g * k g = p g * b g := by
      intro g
      dsimp only [f, k]
      rw [Real.rpow_neg (hα g).le, mul_comm (p g), ← mul_assoc, mul_right_comm _ (b g),
        mul_inv_cancel₀ (Real.rpow_pos_of_pos (hα g) _).ne', one_mul, mul_comm]
    have hf_pow : ∀ g, (f g) ^ ρ = α g * (b g) ^ ρ := by
      intro g
      dsimp only [f]
      rw [Real.mul_rpow (Real.rpow_nonneg (hα g).le _) (hb.1 g),
        ← Real.rpow_mul (hα g).le, one_div_mul_cancel hρ_ne, Real.rpow_one]
    have hk_pow : ∀ g, (k g) ^ (ρ / (ρ - 1)) =
        (α g) ^ (1 / (1 - ρ)) * (p g) ^ (- ρ / (1 - ρ)) := by
      intro g
      dsimp only [k]
      rw [Real.mul_rpow (hp g).le (Real.rpow_nonneg (hα g).le _),
        ← Real.rpow_mul (hα g).le, mul_comm ((p g) ^ _)]
      congr 1
      · congr 1
        field_simp [hρ_ne, hρ1_ne, h1ρ_pos.ne']
        ring
      · congr 1
        field_simp [hρ1_ne, h1ρ_pos.ne']
        ring
    have hfinish :
        Cslib.lpNorm ρ f * Cslib.lpNorm (ρ / (ρ - 1)) k ≤ 𝔼 g, f g * k g →
        (∑ g : G, α g * (b g) ^ ρ) ^ (1 / ρ) ≤ m * D ^ ((1 - ρ) / ρ) := by
      intro hrh
      have hN : (0 : ℝ) < Fintype.card G := Nat.cast_pos.2 Fintype.card_pos
      have hf_nn : ∀ g, 0 ≤ f g := fun g =>
        mul_nonneg (Real.rpow_nonneg (hα g).le _) (hb.1 g)
      rw [Cslib.lpNorm_of_nonneg ρ hf_nn,
        Cslib.lpNorm_of_nonneg (ρ / (ρ - 1)) (fun g => (hk_pos g).le)] at hrh
      simp only [expect_eq_sum_div_card, card_univ, hf_pow, hk_pow, hfk] at hrh
      set A := ∑ g : G, α g * (b g) ^ ρ
      change (A / (Fintype.card G : ℝ)) ^ ρ⁻¹ *
        (D / (Fintype.card G : ℝ)) ^ (ρ / (ρ - 1))⁻¹ ≤
        (∑ i : G, p i * b i) / (Fintype.card G : ℝ) at hrh
      have hA_nn : 0 ≤ A := sum_nonneg fun g _ =>
        mul_nonneg (hα g).le (Real.rpow_nonneg (hb.1 g) _)
      rw [Real.div_rpow hA_nn hN.le, Real.div_rpow hD_pos.le hN.le,
        div_mul_div_comm, ← Real.rpow_add hN] at hrh
      have hexp1 : ρ⁻¹ + (ρ / (ρ - 1))⁻¹ = 1 := by field_simp [hρ_ne, hρ1_ne]; ring
      rw [hexp1, Real.rpow_one, div_le_div_iff_of_pos_right hN, ← expenditure_eq_sum] at hrh
      have hD_inv : (D ^ (ρ / (ρ - 1))⁻¹)⁻¹ = D ^ ((1 - ρ) / ρ) := by
        rw [← Real.rpow_neg hD_pos.le]
        congr 1
        field_simp [hρ_ne, hρ1_ne]
        ring
      rw [one_div, ← hD_inv, le_mul_inv_iff₀ (Real.rpow_pos_of_pos hD_pos _)]
      exact hrh.trans hb.2
    rcases lt_or_gt_of_ne hρ_ne with hρ_neg | hρ_pos
    · by_cases hex_le0 : ∃ g : G, b g ≤ 0
      · rw [cesUtility_of_neg_of_exists_nonpos α hρ_neg hex_le0]
        exact cesUtility_nonneg (fun g => (hα g).le) ρ hx_nn
      · push Not at hex_le0
        have hf_pos : ∀ g, 0 < f g := fun g =>
          mul_pos (Real.rpow_pos_of_pos (hα g) _) (hex_le0 g)
        rw [cesUtility_of_bundle_pos α ρ hex_le0, hux]
        exact hfinish (Cslib.lpNorm_mul_lpNorm_le_expect_mul_of_neg hρ_neg hf_pos
          fun g => (hk_pos g).le)
    · have hf_nn : ∀ g, 0 ≤ f g := fun g =>
        mul_nonneg (Real.rpow_nonneg (hα g).le _) (hb.1 g)
      rw [cesUtility_of_pos_exp hρ_pos b, hux]
      exact hfinish (Cslib.lpNorm_mul_lpNorm_le_expect_mul_of_pos hρ_pos hρ_lt hf_nn hk_pos)

/-- In the **substitutes CES regime `0 < ρ < 1`** ([CodenottiVaradarajan2007], Section 6.1.5,
p. 139), the individual excess demand `p ↦ cesDemand α ρ p (expenditure p w) - w` of a CES trader
with `α > 0` and endowment `w ≥ 0` satisfies weak gross substitutability. -/
theorem isWeakGrossSubstitutes_cesExcessDemand [Nonempty G] {α w : G → ℝ} {ρ : ℝ}
    (hα : ∀ g, 0 < α g) (hw : ∀ g, 0 ≤ w g) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    IsWeakGrossSubstitutes (fun p g => cesDemand α ρ p (expenditure p w) g - w g) := by
  refine IsWeakGrossSubstitutes.sub_const (fun p p' hp hle g hfg => ?_) w
  have hp' : ∀ k, 0 < p' k := fun k => lt_of_lt_of_le (hp k) (hle k)
  simp only [cesDemand_apply, hfg]
  have hfac_nn : 0 ≤ (α g) ^ (1 / (1 - ρ)) / (p g) ^ (1 / (1 - ρ)) :=
    div_nonneg (Real.rpow_nonneg (hα g).le _) (Real.rpow_nonneg (hp g).le _)
  refine mul_le_mul_of_nonneg_left ?_ hfac_nn
  have hexp_le : expenditure p w ≤ expenditure p' w := by
    simp only [expenditure_eq_sum]
    exact sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hle k) (hw k)
  have hexp_nn : 0 ≤ expenditure p w := expenditure_nonneg (fun k => (hp k).le) hw
  have hneg_exp : - ρ / (1 - ρ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  set D := ∑ k : G, (α k) ^ (1 / (1 - ρ)) * (p k) ^ (- ρ / (1 - ρ))
  set D' := ∑ k : G, (α k) ^ (1 / (1 - ρ)) * (p' k) ^ (- ρ / (1 - ρ))
  have hD'_pos : 0 < D' := sum_pos
    (fun k _ => mul_pos (Real.rpow_pos_of_pos (hα k) _) (Real.rpow_pos_of_pos (hp' k) _))
    univ_nonempty
  have hD'_le_D : D' ≤ D := by
    refine sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (hα k).le _)
    exact Real.rpow_le_rpow_of_nonpos (hp k) (hle k) hneg_exp
  calc
    expenditure p w / D ≤ expenditure p w / D' :=
      div_le_div_of_nonneg_left hexp_nn hD'_pos hD'_le_D
    _ ≤ expenditure p' w / D' :=
      div_le_div_of_nonneg_right hexp_le hD'_pos.le

end CES

end Cslib.GameTheory.Market
