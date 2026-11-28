/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Market.ConvexExchange
public import CslibFrontier.GameTheory.Market.EisenbergGale
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import CslibFrontier.Foundations.Analysis.Convex.FirstOrder
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Farkas
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fisher markets with homogeneous consumers and Eisenberg's convex program

Following Eisenberg (1961) as presented in [CodenottiVaradarajan2007], Section 6.2,
pp. 141–142, when every buyer `i : I` in a `FisherMarket I G` has a concave, positively
homogeneous-of-degree-`1` utility function `u_i : ℝ_+^G → ℝ` and positive money budget `e_i > 0`,
market equilibria are characterized by **Eisenberg's convex program**:

`max ∑ i, e_i * log (u_i (x_i))` subject to `x ≥ 0` and `∑ i, x_{ij} ≤ q_j` for each good `j`.

This module formalizes the complete Section 6.2 development without assuming KKT multipliers as a
hypothesis:

1. **Euler's identity (`IsHomogeneousDegOne.fderivWithin_self_eq`, `sum_partial_mul_eq`):**
   for any positively homogeneous-of-degree-`1` function `u` differentiable within `ℝ_+^G` at
   `x ∈ ℝ_+^G` with Fréchet derivative `L`, `L x = ∑_g L (Pi.single g 1) * x_g = u x` (valid on
   both interior and boundary points of `ℝ_+^G`).
2. **KKT optimality → Fisher market equilibrium (`FisherMarket.IsEisenbergKKT`, pp. 141–142,
   Equations `(6.2)`–`(6.4)`):** any primal-dual triple `(x, π, λ)` satisfying `(6.2)`–`(6.4)`
   exhausts every buyer's budget (`expenditure π (x i) = M.budget i`), places every buyer's bundle
   in `M.demandSet π i`, and yields a free-disposal equilibrium `M.IsEquilibrium x π`; under
   monotonicity of a designated buyer's utility, allocating any zero-price surplus
   `q_g - ∑_i x_{ig}` to that buyer yields an exact-clearing equilibrium (`∑_i x'_{ig} = q_g`,
   p. 142).
3. **Unconditional KKT existence via Farkas' lemma (`FisherMarket.exists_isEisenbergKKT_of_isMaxOn`)
   and full characterization (`FisherMarket.exists_isEquilibrium_iff_isMaxOn_eisenbergObjective`):**
   because the constraints `x ≥ 0`, `∑_i x_{ij} ≤ q_j` are polyhedral, any maximizer `x̄` of
   `M.eisenbergObjective` over positive-utility feasible allocations at which each `u_i` is
   differentiable within `ℝ_+^G` admits nonnegative KKT multipliers `(π, λ)` satisfying
   `(6.2)`–`(6.4)` via `Matrix.exists_nonneg_mulVec_eq_iff`. Conversely, every positive-utility
   Fisher equilibrium for homogeneous utilities maximizes `M.eisenbergObjective`.
4. **Concrete instances:** `LinearFisherMarket` (recovering the Eisenberg–Gale program) and CES
   Fisher markets (`cesUtility (α i) (ρ i)` with `α > 0`, `ρ < 1`, `ρ ≠ 0`), where every Eisenberg
   maximizer under positive budgets and supplies is automatically strictly positive
   (`cesFisherMarket_pos_of_isMaxOn`), hence smooth and exact-clearing without extra hypotheses
   (`cesFisherMarket_exists_isEquilibrium_of_isMaxOn`).

## Main definitions

* `Cslib.GameTheory.Market.IsHomogeneousDegOne`: positive homogeneity of degree `1` on `ℝ_+^G`
  ([CodenottiVaradarajan2007], Section 6.1.5, p. 139).
* `Cslib.GameTheory.Market.FisherMarket.eisenbergObjective`,
  `Cslib.GameTheory.Market.FisherMarket.IsPositiveUtilityAllocation`,
  `Cslib.GameTheory.Market.FisherMarket.IsEisenbergKKT`: Eisenberg's logarithmic objective, its
  positive-utility feasible domain, and KKT conditions `(6.2)`–`(6.4)`
  ([CodenottiVaradarajan2007], Section 6.2, p. 141).

## Main results

* `Cslib.GameTheory.Market.IsHomogeneousDegOne.fderivWithin_self_eq`,
  `Cslib.GameTheory.Market.IsHomogeneousDegOne.sum_partial_mul_eq`: Euler's homogeneous function
  identity on `ℝ_+^G`.
* `Cslib.GameTheory.Market.FisherMarket.IsEisenbergKKT.expenditure_eq_budget`,
  `Cslib.GameTheory.Market.FisherMarket.IsEisenbergKKT.isEquilibrium`,
  `Cslib.GameTheory.Market.FisherMarket.IsEisenbergKKT.exists_isEquilibrium_exactClearing`: KKT
  sufficiency for Fisher market equilibrium (free-disposal and exact-clearing).
* `Cslib.GameTheory.Market.FisherMarket.exists_isEisenbergKKT_of_isMaxOn`: unconditional KKT
  existence from Eisenberg optimality via Farkas' lemma.
* `Cslib.GameTheory.Market.FisherMarket.exists_isEquilibrium_of_isMaxOn_eisenbergObjective`,
  `FisherMarket.exists_isEquilibrium_exactClearing_of_isMaxOn_eisenbergObjective`,
  `Cslib.GameTheory.Market.FisherMarket.IsEquilibrium.isMaxOn_eisenbergObjective`,
  `Cslib.GameTheory.Market.FisherMarket.exists_isEquilibrium_iff_isMaxOn_eisenbergObjective`:
  unconditional equilibrium theorems for Eisenberg's convex program ([CodenottiVaradarajan2007],
  Section 6.2, pp. 141–142).
* `Cslib.GameTheory.Market.hasFDerivAt_cesUtility`,
  `Cslib.GameTheory.Market.cesFisherMarket_pos_of_isMaxOn`,
  `Cslib.GameTheory.Market.cesFisherMarket_exists_isEquilibrium_of_isMaxOn`: Fréchet derivative of
  CES utilities, automatic interiority of CES Eisenberg maximizers, and unconditional CES Fisher
  equilibrium theorem.

## References

* [CodenottiVaradarajan2007], Section 6.1.5, p. 139 and Section 6.2, pp. 141–142
-/

public section

namespace Cslib.GameTheory.Market

open Finset Filter Matrix Set
open scoped BigOperators Topology

/-! ### Positive homogeneity of degree `1` and Euler's identity -/

section Euler

variable {G : Type*}

/-- A utility function `u : (G → ℝ) → ℝ` is **positively homogeneous of degree `1`** on `ℝ_+^G`
([CodenottiVaradarajan2007], Section 6.1.5, p. 139) if `u (c • b) = c * u b` for every nonnegative
bundle `b` and scalar `c > 0`. -/
@[expose] def IsHomogeneousDegOne (u : (G → ℝ) → ℝ) : Prop :=
  ∀ ⦃b : G → ℝ⦄, (∀ g, 0 ≤ b g) → ∀ ⦃c : ℝ⦄, 0 < c → u (c • b) = c * u b

private theorem continuousLinearMap_apply_eq_sum [Fintype G] [DecidableEq G]
    (L : (G → ℝ) →L[ℝ] ℝ) (v : G → ℝ) :
    L v = ∑ g : G, L (Pi.single g 1) * v g := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  rw [map_sum]
  refine sum_congr rfl fun g _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

/-- **Euler's identity for positively homogeneous degree-`1` functions**
([CodenottiVaradarajan2007], Section 6.2, p. 142): if `u` is positively homogeneous of degree `1` on
`ℝ_+^G` and has Fréchet derivative `L` within `ℝ_+^G` at `x ∈ ℝ_+^G`, then `L x = u x`. -/
theorem IsHomogeneousDegOne.fderivWithin_self_eq [Finite G] {u : (G → ℝ) → ℝ}
    (hhom : IsHomogeneousDegOne u) {x : G → ℝ} (hx : ∀ g, 0 ≤ x g)
    {L : (G → ℝ) →L[ℝ] ℝ} (hL : HasFDerivWithinAt u L {b : G → ℝ | ∀ g, 0 ≤ b g} x) :
    L x = u x := by
  have : Fintype G := Fintype.ofFinite G
  have hray : HasDerivWithinAt (fun t : ℝ => t • x) x (Ioi (0 : ℝ)) 1 := by
    have h1 : HasDerivAt (fun t : ℝ => t • x) ((1 : ℝ) • x) 1 :=
      (hasDerivAt_id' (1 : ℝ)).smul_const x
    rw [one_smul] at h1
    exact h1.hasDerivWithinAt
  have hmaps : MapsTo (fun t : ℝ => t • x) (Ioi (0 : ℝ)) {b : G → ℝ | ∀ g, 0 ≤ b g} :=
    fun t ht g => mul_nonneg (mem_Ioi.1 ht).le (hx g)
  have hL1 : HasFDerivWithinAt u L {b : G → ℝ | ∀ g, 0 ≤ b g} ((1 : ℝ) • x) := by
    simpa only [one_smul] using hL
  have hcomp : HasDerivAt (fun t : ℝ => u (t • x)) (L x) 1 :=
    (hL1.comp_hasDerivWithinAt (1 : ℝ) hray hmaps).hasDerivAt (Ioi_mem_nhds zero_lt_one)
  have hlin : HasDerivAt (fun t : ℝ => t * u x) (u x) 1 := by
    simpa only [one_mul] using (hasDerivAt_id' (1 : ℝ)).mul_const (u x)
  have heq : (fun t : ℝ => u (t • x)) =ᶠ[𝓝 (1 : ℝ)] (fun t : ℝ => t * u x) :=
    Filter.eventually_of_mem (Ioi_mem_nhds zero_lt_one) fun t ht => hhom hx (mem_Ioi.1 ht)
  exact hcomp.unique (hlin.congr_of_eventuallyEq heq)

/-- Partial-derivative coordinate form of **Euler's identity** ([CodenottiVaradarajan2007],
Section 6.2, p. 142): `∑ g, L (Pi.single g 1) * x g = u x`. -/
theorem IsHomogeneousDegOne.sum_partial_mul_eq [Fintype G] [DecidableEq G] {u : (G → ℝ) → ℝ}
    (hhom : IsHomogeneousDegOne u) {x : G → ℝ} (hx : ∀ g, 0 ≤ x g)
    {L : (G → ℝ) →L[ℝ] ℝ} (hL : HasFDerivWithinAt u L {b : G → ℝ | ∀ g, 0 ≤ b g} x) :
    ∑ g : G, L (Pi.single g 1) * x g = u x := by
  rw [← continuousLinearMap_apply_eq_sum L x]
  exact hhom.fderivWithin_self_eq hx hL

end Euler

/-! ### §6.2 Eisenberg's convex program for homogeneous Fisher markets -/

namespace FisherMarket

section EisenbergProgram

variable {I G : Type*} [Fintype I] (M : FisherMarket I G)

/-- **Eisenberg's convex program objective** `∑ i, M.budget i * Real.log (M.utility i (x i))`
(Eisenberg 1961; [CodenottiVaradarajan2007], Section 6.2, p. 141). -/
noncomputable def eisenbergObjective (x : I → G → ℝ) : ℝ :=
  ∑ i : I, M.budget i * Real.log (M.utility i (x i))

theorem eisenbergObjective_eq (x : I → G → ℝ) :
    M.eisenbergObjective x = ∑ i : I, M.budget i * Real.log (M.utility i (x i)) := by rfl

/-- Feasible allocations of `M` giving every buyer strictly positive utility, forming the effective
domain of `M.eisenbergObjective`. -/
@[expose] def IsPositiveUtilityAllocation (x : I → G → ℝ) : Prop :=
  M.IsFeasibleAllocation x ∧ ∀ i : I, 0 < M.utility i (x i)

/-- **Karush–Kuhn–Tucker optimality conditions `(6.2)`–`(6.4)`** for Eisenberg's convex program
([CodenottiVaradarajan2007], Section 6.2, p. 141), with Fréchet derivatives `L i` of `M.utility i`
within `ℝ_+^G` at `x i`, supply multipliers (prices) `π ≥ 0`, and nonnegativity multipliers
`lam ≥ 0`. -/
structure IsEisenbergKKT [DecidableEq G] (x : I → G → ℝ) (L : I → (G → ℝ) →L[ℝ] ℝ)
    (π : G → ℝ) (lam : I → G → ℝ) : Prop where
  /-- Primal allocation is feasible and gives every buyer positive utility. -/
  pos_alloc : M.IsPositiveUtilityAllocation x
  /-- Each buyer's utility is differentiable within `ℝ_+^G` at `x i` with derivative `L i`. -/
  hasFDeriv : ∀ i : I, HasFDerivWithinAt (M.utility i) (L i) {b : G → ℝ | ∀ g, 0 ≤ b g} (x i)
  /-- Prices are nonnegative (`π_j ≥ 0`). -/
  price_nonneg : ∀ g : G, 0 ≤ π g
  /-- Nonnegativity multipliers are nonnegative (`λ_{ij} ≥ 0`). -/
  lam_nonneg : ∀ (i : I) (g : G), 0 ≤ lam i g
  /-- Equation `(6.2)`: supply complementary slackness `π_j * (∑_i x_{ij} - q_j) = 0`. -/
  supply_slackness : ∀ g : G, π g * ((∑ i : I, x i g) - M.supply g) = 0
  /-- Equation `(6.3)`: nonnegativity complementary slackness `λ_{ij} * x_{ij} = 0`. -/
  nonneg_slackness : ∀ (i : I) (g : G), lam i g * x i g = 0
  /-- Equation `(6.4)`: stationarity `(e_i / u_i(x_i)) * ∂u_i/∂x_{ij}(x_i) = π_j - λ_{ij}`. -/
  stationarity : ∀ (i : I) (g : G),
    (M.budget i / M.utility i (x i)) * L i (Pi.single g 1) = π g - lam i g

/-- **Budget exhaustion from Eisenberg KKT `(6.3)`–`(6.4)` and Euler's identity**
([CodenottiVaradarajan2007], Section 6.2, p. 142): `expenditure π (x i) = M.budget i`. -/
theorem IsEisenbergKKT.expenditure_eq_budget [Fintype G] [DecidableEq G] {M : FisherMarket I G}
    {x : I → G → ℝ} {L : I → (G → ℝ) →L[ℝ] ℝ} {π : G → ℝ} {lam : I → G → ℝ}
    (hkkt : M.IsEisenbergKKT x L π lam) (hhom : ∀ i, IsHomogeneousDegOne (M.utility i)) (i : I) :
    expenditure π (x i) = M.budget i := by
  have heuler := (hhom i).sum_partial_mul_eq (hkkt.pos_alloc.1.1 i) (hkkt.hasFDeriv i)
  have hUi : 0 < M.utility i (x i) := hkkt.pos_alloc.2 i
  have hsum : (M.budget i / M.utility i (x i)) * ∑ g : G, L i (Pi.single g 1) * x i g =
      ∑ g : G, (π g - lam i g) * x i g := by
    rw [mul_sum]
    refine sum_congr rfl fun g _ => ?_
    rw [← mul_assoc, hkkt.stationarity i g]
  rw [heuler, div_mul_cancel₀ _ hUi.ne'] at hsum
  have hrhs : ∑ g : G, (π g - lam i g) * x i g = expenditure π (x i) := by
    simp only [sub_mul, hkkt.nonneg_slackness i, sub_zero, expenditure_eq_sum]
  exact hrhs.symm.trans hsum.symm

/-- **Individual demand optimality from Eisenberg KKT** ([CodenottiVaradarajan2007], Section 6.2,
p. 142): for concave homogeneous utilities and positive budgets, `x i ∈ M.demandSet π i`. -/
theorem IsEisenbergKKT.mem_demandSet [Fintype G] [DecidableEq G] {M : FisherMarket I G}
    {x : I → G → ℝ} {L : I → (G → ℝ) →L[ℝ] ℝ} {π : G → ℝ} {lam : I → G → ℝ}
    (hkkt : M.IsEisenbergKKT x L π lam)
    (hbudget : ∀ i, 0 < M.budget i)
    (hconc : ∀ i, ConcaveOn ℝ {b : G → ℝ | ∀ g, 0 ≤ b g} (M.utility i))
    (hhom : ∀ i, IsHomogeneousDegOne (M.utility i)) (i : I) :
    x i ∈ M.demandSet π i := by
  have hexp : expenditure π (x i) = M.budget i := hkkt.expenditure_eq_budget hhom i
  have hUi : 0 < M.utility i (x i) := hkkt.pos_alloc.2 i
  have hei : 0 < M.budget i := hbudget i
  rw [FisherMarket.mem_demandSet, Market.mem_demandSet]
  refine ⟨⟨hkkt.pos_alloc.1.1 i, hexp.le⟩, fun y hy => ?_⟩
  have htan := (hconc i).neg.add_le_of_hasFDerivWithinAt
    (hkkt.pos_alloc.1.1 i) hy.1 (hkkt.hasFDeriv i).neg
  simp only [Pi.neg_apply, neg_apply] at htan
  have hdiff_le : M.utility i y - M.utility i (x i) ≤ L i (y - x i) := by linarith
  have hgrad : ∀ g : G, L i (Pi.single g 1) =
      (M.utility i (x i) / M.budget i) * (π g - lam i g) := fun g => by
    have hs := hkkt.stationarity i g
    field_simp [hUi.ne', hei.ne'] at hs ⊢
    linarith
  have hL_eq : L i (y - x i) =
      (M.utility i (x i) / M.budget i) *
        ((expenditure π y - ∑ g : G, lam i g * y g) - M.budget i) := by
    rw [continuousLinearMap_apply_eq_sum]
    simp_rw [hgrad, mul_assoc, ← mul_sum]
    congr 1
    simp only [Pi.sub_apply]
    have h1 : ∑ g : G, (π g - lam i g) * (y g - x i g) =
        (expenditure π y - ∑ g : G, lam i g * y g) -
          (expenditure π (x i) - ∑ g : G, lam i g * x i g) := by
      simp only [expenditure_eq_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun g _ => by ring
    have hlam0 : ∑ g : G, lam i g * x i g = 0 := sum_eq_zero fun g _ => hkkt.nonneg_slackness i g
    rw [h1, hexp, hlam0, sub_zero]
  have hlamy_nn : 0 ≤ ∑ g : G, lam i g * y g :=
    sum_nonneg fun g _ => mul_nonneg (hkkt.lam_nonneg i g) (hy.1 g)
  have hbracket_nonpos : (expenditure π y - ∑ g : G, lam i g * y g) - M.budget i ≤ 0 := by
    linarith [hy.2]
  have hL_nonpos : L i (y - x i) ≤ 0 := by
    rw [hL_eq]
    exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg hUi.le hei.le) hbracket_nonpos
  linarith

/-- **KKT sufficiency for free-disposal Fisher market equilibrium** ([CodenottiVaradarajan2007],
Section 6.2, pp. 141–142): any Eisenberg KKT solution `(x, L, π, λ)` for concave homogeneous
utilities with positive budgets forms a Fisher market equilibrium `(x, π)`. -/
theorem IsEisenbergKKT.isEquilibrium [Fintype G] [DecidableEq G] {M : FisherMarket I G}
    {x : I → G → ℝ} {L : I → (G → ℝ) →L[ℝ] ℝ} {π : G → ℝ} {lam : I → G → ℝ}
    (hkkt : M.IsEisenbergKKT x L π lam)
    (hbudget : ∀ i, 0 < M.budget i)
    (hconc : ∀ i, ConcaveOn ℝ {b : G → ℝ | ∀ g, 0 ≤ b g} (M.utility i))
    (hhom : ∀ i, IsHomogeneousDegOne (M.utility i)) :
    M.IsEquilibrium x π := by
  refine ⟨hkkt.price_nonneg, fun i => hkkt.mem_demandSet hbudget hconc hhom i,
    hkkt.pos_alloc.1.2, fun g => ?_⟩
  linarith [hkkt.supply_slackness g]

/-- **Exact-clearing Fisher equilibrium via zero-price surplus reassignment**
([CodenottiVaradarajan2007], Section 6.2, p. 142): given a designated buyer `i₀` whose utility is
monotone on `ℝ_+^G`, reassigning any unsold zero-price surplus `M.supply g - ∑ k, x k g` to `i₀`
preserves `M.IsEquilibrium` and achieves exact market clearing `∑ i, x' i g = M.supply g` for every
good `g`. -/
theorem IsEisenbergKKT.exists_isEquilibrium_exactClearing [Fintype G] [DecidableEq G]
    {M : FisherMarket I G}
    {x : I → G → ℝ} {L : I → (G → ℝ) →L[ℝ] ℝ} {π : G → ℝ} {lam : I → G → ℝ}
    (hkkt : M.IsEisenbergKKT x L π lam)
    (hbudget : ∀ i, 0 < M.budget i)
    (hconc : ∀ i, ConcaveOn ℝ {b : G → ℝ | ∀ g, 0 ≤ b g} (M.utility i))
    (hhom : ∀ i, IsHomogeneousDegOne (M.utility i))
    (i₀ : I)
    (hmono : ∀ ⦃b₁ b₂ : G → ℝ⦄, (∀ g, 0 ≤ b₁ g) → (∀ g, b₁ g ≤ b₂ g) →
      M.utility i₀ b₁ ≤ M.utility i₀ b₂) :
    ∃ x' : I → G → ℝ, M.IsEquilibrium x' π ∧ ∀ g : G, ∑ i : I, x' i g = M.supply g := by
  classical
  have heq := hkkt.isEquilibrium hbudget hconc hhom
  let surplus : G → ℝ := fun g => M.supply g - ∑ k : I, x k g
  have hsurp_nn : ∀ g, 0 ≤ surplus g := fun g => sub_nonneg.2 (hkkt.pos_alloc.1.2 g)
  let x' : I → G → ℝ := fun i g => if i = i₀ then x i₀ g + surplus g else x i g
  have hclear : ∀ g : G, ∑ i : I, x' i g = M.supply g := fun g => by
    have hsplit : ∑ i : I, x' i g = (∑ i : I, x i g) + surplus g := by
      have hsub : ∀ i : I, x' i g = x i g + if i = i₀ then surplus g else 0 := fun i => by
        dsimp only [x']; split_ifs with h <;> simp [h]
      simp_rw [hsub, sum_add_distrib, sum_ite_eq']
      simp only [Finset.mem_univ, ↓reduceIte]
    rw [hsplit]
    dsimp only [surplus]; ring
  refine ⟨x', ⟨hkkt.price_nonneg, fun i => ?_, fun g => (hclear g).le,
    fun g => by rw [hclear g, sub_self, mul_zero]⟩, hclear⟩
  by_cases hi : i = i₀
  · subst i
    have hdem₀ := Market.mem_demandSet.1 (M.mem_demandSet.1 (heq.2.1 i₀))
    rw [FisherMarket.mem_demandSet, Market.mem_demandSet]
    have hx'i₀_nn : ∀ g, 0 ≤ x' i₀ g := fun g => by
      simp only [x', ↓reduceIte]
      exact add_nonneg (hkkt.pos_alloc.1.1 i₀ g) (hsurp_nn g)
    have hexp_eq : expenditure π (x' i₀) = expenditure π (x i₀) := by
      simp only [expenditure_eq_sum, x', ↓reduceIte, mul_add, sum_add_distrib]
      have hzero : ∑ g : G, π g * surplus g = 0 := sum_eq_zero fun g _ => by
        dsimp only [surplus]; linarith [hkkt.supply_slackness g]
      rw [hzero, add_zero]
    have hu_ge : M.utility i₀ (x i₀) ≤ M.utility i₀ (x' i₀) :=
      hmono (hkkt.pos_alloc.1.1 i₀) fun g => by simp only [x', ↓reduceIte]; linarith [hsurp_nn g]
    exact ⟨⟨hx'i₀_nn, hexp_eq.le.trans hdem₀.1.2⟩, fun y hy => (hdem₀.2 y hy).trans hu_ge⟩
  · have hxeq : x' i = x i := funext fun g => by simp [x', hi]
    rw [hxeq]
    exact heq.2.1 i

/-- **Unconditional KKT existence for Eisenberg's convex program via Farkas' lemma**
([CodenottiVaradarajan2007], Section 6.2, p. 141): every maximizer `x` of `M.eisenbergObjective`
over `{y | M.IsPositiveUtilityAllocation y}` at which each `M.utility i` has Fréchet derivative
`L i` within `ℝ_+^G` admits nonnegative KKT multipliers `(π, lam)` satisfying `(6.2)`–`(6.4)`. -/
theorem exists_isEisenbergKKT_of_isMaxOn [Finite G] [DecidableEq G] {M : FisherMarket I G}
    {x : I → G → ℝ} {L : I → (G → ℝ) →L[ℝ] ℝ}
    (hx : M.IsPositiveUtilityAllocation x)
    (hmax : IsMaxOn M.eisenbergObjective {y | M.IsPositiveUtilityAllocation y} x)
    (hL : ∀ i : I, HasFDerivWithinAt (M.utility i) (L i) {b : G → ℝ | ∀ g, 0 ≤ b g} (x i)) :
    ∃ (π : G → ℝ) (lam : I → G → ℝ), M.IsEisenbergKKT x L π lam := by
  classical
  have : Fintype G := Fintype.ofFinite G
  -- Step 1: Every feasible first-order direction `d` has nonpositive directional derivative.
  have hno : ∀ d : I → G → ℝ,
      (∀ i g, x i g = 0 → 0 ≤ d i g) →
      (∀ g, ∑ i : I, x i g = M.supply g → ∑ i : I, d i g ≤ 0) →
      ∑ i : I, ∑ g : G, ((M.budget i / M.utility i (x i)) * L i (Pi.single g 1)) * d i g ≤ 0 := by
    intro d hd_nn hd_sup
    have hnn_ev : ∀ i : I, ∀ᶠ t in 𝓝[≥] (0 : ℝ), ∀ g : G, 0 ≤ x i g + t * d i g := fun i =>
      eventually_all.2 fun g => eventually_add_mul_nonneg_nhdsGE (hx.1.1 i g) (hd_nn i g)
    have hsup_ev : ∀ᶠ t in 𝓝[≥] (0 : ℝ), ∀ g : G, ∑ i : I, (x i g + t * d i g) ≤ M.supply g :=
      eventually_all.2 fun g =>
        (eventually_add_mul_le_nhdsGE (hx.1.2 g) (hd_sup g)).mono fun t ht => by
          simpa only [sum_add_distrib, ← mul_sum] using ht
    -- Positive utility holds eventually by continuity of `M.utility i` along the feasible ray.
    have hray_pos : ∀ i : I, ∀ᶠ t in 𝓝[≥] (0 : ℝ), 0 < M.utility i (x i + t • d i) := by
      intro i
      have hcont_ray : ContinuousWithinAt (fun t : ℝ => x i + t • d i) (Ici 0) 0 :=
        (continuous_const.add (continuous_id.smul continuous_const)).continuousWithinAt
      have htend : Tendsto (fun t : ℝ => x i + t • d i) (𝓝[≥] (0 : ℝ))
          (𝓝[{b : G → ℝ | ∀ g, 0 ≤ b g}] (x i)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨by simpa only [zero_smul, add_zero] using hcont_ray.tendsto, ?_⟩
        exact (hnn_ev i).mono fun t ht g => by
          simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using ht g
      have hcont_u : Tendsto (M.utility i) (𝓝[{b : G → ℝ | ∀ g, 0 ≤ b g}] (x i))
          (𝓝 (M.utility i (x i))) := (hL i).continuousWithinAt
      exact (hcont_u.comp htend).eventually (Ioi_mem_nhds (hx.2 i))
    have hfeas_ev : ∀ᶠ t in 𝓝[≥] (0 : ℝ),
        M.IsPositiveUtilityAllocation (fun i => x i + t • d i) := by
      filter_upwards [eventually_all.2 hnn_ev, hsup_ev, eventually_all.2 hray_pos] with t h1 h2 h3
      refine ⟨⟨fun i g => by simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h1 i g,
        fun g => by simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h2 g⟩, h3⟩
    have hmax_ev : ∀ᶠ t in 𝓝[≥] (0 : ℝ),
        M.eisenbergObjective (fun i => x i + t • d i) ≤
          M.eisenbergObjective (fun i => x i + (0 : ℝ) • d i) :=
      hfeas_ev.mono fun t ht => by
        simpa only [zero_smul, add_zero] using isMaxOn_iff.1 hmax _ ht
    -- Differentiate `t ↦ M.eisenbergObjective (fun i => x i + t • d i)` at `t = 0` within `Ici 0`.
    have hderiv_i : ∀ i : I, HasDerivWithinAt (fun t : ℝ => M.utility i (x i + t • d i))
        (L i (d i)) (Ici 0) 0 := by
      intro i
      obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.1 (hnn_ev i)
      have hlin : HasDerivWithinAt (fun t : ℝ => x i + t • d i) (d i) (Icc 0 (δ / 2)) 0 := by
        simpa only [one_smul] using
          (((hasDerivAt_id' (0 : ℝ)).smul_const (d i)).const_add (x i)).hasDerivWithinAt
            (s := Icc 0 (δ / 2))
      have hmaps : MapsTo (fun t : ℝ => x i + t • d i) (Icc 0 (δ / 2))
          {b : G → ℝ | ∀ g, 0 ≤ b g} := fun t ht g => by
        have hmem : t ∈ Metric.ball (0 : ℝ) δ ∩ Ici (0 : ℝ) := by
          refine ⟨?_, ht.1⟩
          rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
          linarith [ht.2]
        simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hsub hmem g
      have hL0 : HasFDerivWithinAt (M.utility i) (L i) {b : G → ℝ | ∀ g, 0 ≤ b g}
          (x i + (0 : ℝ) • d i) := by simpa only [zero_smul, add_zero] using hL i
      exact (hL0.comp_hasDerivWithinAt 0 hlin hmaps).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE (half_pos hδ))
    have hderiv_log : ∀ i : I, HasDerivWithinAt
        (fun t : ℝ => M.budget i * Real.log (M.utility i (x i + t • d i)))
        ((M.budget i / M.utility i (x i)) * L i (d i)) (Ici 0) 0 := fun i => by
      have hlog : HasDerivAt Real.log (M.utility i (x i))⁻¹
          (M.utility i (x i + (0 : ℝ) • d i)) := by
        simpa only [zero_smul, add_zero] using Real.hasDerivAt_log (hx.2 i).ne'
      have hcomp := (hlog.comp_hasDerivWithinAt 0 (hderiv_i i)).const_mul (M.budget i)
      simp only [Function.comp_apply] at hcomp
      convert hcomp using 1
      ring
    have hderiv_obj : HasDerivWithinAt (fun t : ℝ => M.eisenbergObjective (fun i => x i + t • d i))
        (∑ i : I, (M.budget i / M.utility i (x i)) * L i (d i)) (Ici 0) 0 :=
      HasDerivWithinAt.fun_sum fun i _ => hderiv_log i
    have hnonpos := hasDerivWithinAt_nonpos_of_eventually_le hderiv_obj hmax_ev
    have heq : (∑ i : I, (M.budget i / M.utility i (x i)) * L i (d i)) =
        ∑ i : I, ∑ g : G, ((M.budget i / M.utility i (x i)) * L i (Pi.single g 1)) * d i g := by
      refine sum_congr rfl fun i _ => ?_
      rw [continuousLinearMap_apply_eq_sum (L i) (d i), mul_sum]
      exact sum_congr rfl fun g _ => by ring
    linarith
  -- Step 2: Apply Farkas' lemma (`Matrix.exists_nonneg_mulVec_eq_iff`) to the active cone.
  let c : I × G → ℝ := fun ig =>
    (M.budget ig.1 / M.utility ig.1 (x ig.1)) * L ig.1 (Pi.single ig.2 1)
  let A : Matrix (I × G) (G ⊕ (I × G)) ℝ := Matrix.of fun ig col =>
    match col with
    | Sum.inl g => if ig.2 = g ∧ ∑ i : I, x i g = M.supply g then 1 else 0
    | Sum.inr ig' => if ig' = ig ∧ x ig.1 ig.2 = 0 then -1 else 0
  have hfarkas : ∀ y : I × G → ℝ, 0 ≤ y ᵥ* A → 0 ≤ y ⬝ᵥ c := by
    intro y hy
    have hd_nn : ∀ i g, x i g = 0 → 0 ≤ -y (i, g) := fun i g hx0 => by
      have h1 : 0 ≤ (y ᵥ* A) (Sum.inr (i, g)) := hy (Sum.inr (i, g))
      have hcalc : (y ᵥ* A) (Sum.inr (i, g)) = -y (i, g) := by
        simp only [Matrix.vecMul, dotProduct, A, Matrix.of_apply]
        rw [Finset.sum_eq_single (i, g)]
        · simp [hx0]
        · intro ig' _ hne; simp [hne.symm]
        · intro h; exact (h (mem_univ (i, g))).elim
      linarith
    have hd_sup : ∀ g, ∑ i : I, x i g = M.supply g → ∑ i : I, (-y (i, g)) ≤ 0 := fun g hsup => by
      have h1 : 0 ≤ (y ᵥ* A) (Sum.inl g) := hy (Sum.inl g)
      have hcalc : (y ᵥ* A) (Sum.inl g) = ∑ i : I, y (i, g) := by
        simp only [Matrix.vecMul, dotProduct, A, Matrix.of_apply, hsup, and_true]
        rw [Fintype.sum_prod_type]
        refine sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single g (fun g' _ hne => by simp [hne]) (fun h => (h (mem_univ g)).elim)]
        simp
      rw [hcalc] at h1
      rw [sum_neg_distrib]
      linarith
    have hdir := hno (fun i g => -y (i, g)) hd_nn hd_sup
    have hdot : y ⬝ᵥ c = -(∑ i : I, ∑ g : G,
        ((M.budget i / M.utility i (x i)) * L i (Pi.single g 1)) * (-y (i, g))) := by
      simp only [dotProduct, c, Fintype.sum_prod_type, ← sum_neg_distrib]
      exact sum_congr rfl fun i _ => sum_congr rfl fun g _ => by ring
    linarith
  obtain ⟨u, hu0, hAu⟩ := (Matrix.exists_nonneg_mulVec_eq_iff A c).2 hfarkas
  let π : G → ℝ := fun g => if ∑ i : I, x i g = M.supply g then u (Sum.inl g) else 0
  let lam : I → G → ℝ := fun i g => if x i g = 0 then u (Sum.inr (i, g)) else 0
  refine ⟨π, lam, hx, hL, ?_, ?_, ?_, ?_, ?_⟩
  · intro g; dsimp only [π]; split_ifs; exacts [hu0 (Sum.inl g), le_rfl]
  · intro i g; dsimp only [lam]; split_ifs; exacts [hu0 (Sum.inr (i, g)), le_rfl]
  · intro g; dsimp only [π]; split_ifs with h
    · rw [h, sub_self, mul_zero]
    · rw [zero_mul]
  · intro i g; dsimp only [lam]; split_ifs with h
    · rw [h, mul_zero]
    · rw [zero_mul]
  · intro i g
    have h1 := congrFun hAu (i, g)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, A, Matrix.of_apply, c] at h1
    have hLsum :
        (∑ g' : G, (if g = g' ∧ ∑ k : I, x k g' = M.supply g' then (1 : ℝ) else 0) *
          u (Sum.inl g')) = π g := by
      rw [Finset.sum_eq_single g (fun g' _ hne => by simp [hne.symm])
        (fun h => (h (mem_univ g)).elim)]
      dsimp only [π]
      by_cases h : ∑ k : I, x k g = M.supply g <;> simp [h]
    have hRsum :
        (∑ ig' : I × G, (if ig' = (i, g) ∧ x i g = 0 then (-1 : ℝ) else 0) *
          u (Sum.inr ig')) = -lam i g := by
      rw [Finset.sum_eq_single (i, g) (fun ig' _ hne => by simp [hne])
        (fun h => (h (mem_univ (i, g))).elim)]
      dsimp only [lam]
      by_cases h : x i g = 0 <;> simp [h]
    rw [hLsum, hRsum] at h1
    linarith

/-- **Eisenberg's Equilibrium Theorem (unconditional headline)** (Eisenberg 1961;
[CodenottiVaradarajan2007], Section 6.2, pp. 141–142): in a Fisher market with positive buyer
budgets and concave, positively homogeneous-of-degree-`1` utilities, any optimal solution `x` of
Eisenberg's convex program `max ∑ i, e_i log u_i(x_i)` over positive-utility feasible allocations
at which each `u_i` is differentiable within `ℝ_+^G` admits nonnegative prices `π` forming a Fisher
market equilibrium `(x, π)` with exact budget exhaustion `expenditure π (x i) = M.budget i`. -/
theorem exists_isEquilibrium_of_isMaxOn_eisenbergObjective [Fintype G] {M : FisherMarket I G}
    (hbudget : ∀ i, 0 < M.budget i)
    (hconc : ∀ i, ConcaveOn ℝ {b : G → ℝ | ∀ g, 0 ≤ b g} (M.utility i))
    (hhom : ∀ i, IsHomogeneousDegOne (M.utility i))
    {x : I → G → ℝ} (hx : M.IsPositiveUtilityAllocation x)
    (hmax : IsMaxOn M.eisenbergObjective {y | M.IsPositiveUtilityAllocation y} x)
    (hdiff : ∀ i : I, DifferentiableWithinAt ℝ (M.utility i) {b : G → ℝ | ∀ g, 0 ≤ b g} (x i)) :
    ∃ π : G → ℝ, M.IsEquilibrium x π ∧ ∀ i : I, expenditure π (x i) = M.budget i := by
  classical
  let L : I → (G → ℝ) →L[ℝ] ℝ := fun i =>
    fderivWithin ℝ (M.utility i) {b : G → ℝ | ∀ g, 0 ≤ b g} (x i)
  have hL : ∀ i : I, HasFDerivWithinAt (M.utility i) (L i) {b : G → ℝ | ∀ g, 0 ≤ b g} (x i) :=
    fun i => (hdiff i).hasFDerivWithinAt
  obtain ⟨π, lam, hkkt⟩ := exists_isEisenbergKKT_of_isMaxOn hx hmax hL
  exact ⟨π, hkkt.isEquilibrium hbudget hconc hhom, hkkt.expenditure_eq_budget hhom⟩

/-- **Exact-clearing Eisenberg Equilibrium Theorem** ([CodenottiVaradarajan2007], Section 6.2,
p. 142): under the hypotheses of `exists_isEquilibrium_of_isMaxOn_eisenbergObjective` together with
a designated buyer `i₀` whose utility is monotone on `ℝ_+^G`, reassigning any zero-price surplus
yields an exact-clearing Fisher market equilibrium `(x', π)` (`∑ i, x' i g = M.supply g`). -/
theorem exists_isEquilibrium_exactClearing_of_isMaxOn_eisenbergObjective [Fintype G]
    {M : FisherMarket I G}
    (hbudget : ∀ i, 0 < M.budget i)
    (hconc : ∀ i, ConcaveOn ℝ {b : G → ℝ | ∀ g, 0 ≤ b g} (M.utility i))
    (hhom : ∀ i, IsHomogeneousDegOne (M.utility i))
    (i₀ : I)
    (hmono : ∀ ⦃b₁ b₂ : G → ℝ⦄, (∀ g, 0 ≤ b₁ g) → (∀ g, b₁ g ≤ b₂ g) →
      M.utility i₀ b₁ ≤ M.utility i₀ b₂)
    {x : I → G → ℝ} (hx : M.IsPositiveUtilityAllocation x)
    (hmax : IsMaxOn M.eisenbergObjective {y | M.IsPositiveUtilityAllocation y} x)
    (hdiff : ∀ i : I, DifferentiableWithinAt ℝ (M.utility i) {b : G → ℝ | ∀ g, 0 ≤ b g} (x i)) :
    ∃ (x' : I → G → ℝ) (π : G → ℝ),
      M.IsEquilibrium x' π ∧ ∀ g : G, ∑ i : I, x' i g = M.supply g := by
  classical
  let L : I → (G → ℝ) →L[ℝ] ℝ := fun i =>
    fderivWithin ℝ (M.utility i) {b : G → ℝ | ∀ g, 0 ≤ b g} (x i)
  have hL : ∀ i : I, HasFDerivWithinAt (M.utility i) (L i) {b : G → ℝ | ∀ g, 0 ≤ b g} (x i) :=
    fun i => (hdiff i).hasFDerivWithinAt
  obtain ⟨π, lam, hkkt⟩ := exists_isEisenbergKKT_of_isMaxOn hx hmax hL
  obtain ⟨x', heq, hclr⟩ := hkkt.exists_isEquilibrium_exactClearing hbudget hconc hhom i₀ hmono
  exact ⟨x', π, heq, hclr⟩

/-- **Converse of Eisenberg's theorem**: in any Fisher market with positive budgets and positively
homogeneous degree-`1` utilities (no concavity or differentiability required), every
positive-utility equilibrium allocation `x` globally maximizes `M.eisenbergObjective` over all
positive-utility feasible allocations. -/
theorem IsEquilibrium.isMaxOn_eisenbergObjective [Fintype G] {M : FisherMarket I G}
    {x : I → G → ℝ} {π : G → ℝ} (heq : M.IsEquilibrium x π)
    (hbudget : ∀ i, 0 < M.budget i)
    (hhom : ∀ i, IsHomogeneousDegOne (M.utility i))
    (hpos : ∀ i, 0 < M.utility i (x i)) :
    IsMaxOn M.eisenbergObjective {y | M.IsPositiveUtilityAllocation y} x := by
  -- Every buyer exhausts their budget by degree-1 homogeneity and `u_i(x_i) > 0`.
  have hexp_eq : ∀ i : I, expenditure π (x i) = M.budget i := fun i => by
    have hdem := Market.mem_demandSet.1 (M.mem_demandSet.1 (heq.2.1 i))
    refine le_antisymm hdem.1.2 (le_of_not_gt fun hlt => ?_)
    rcases (expenditure_nonneg heq.1 hdem.1.1).eq_or_lt with hexp0 | hexp_pos
    · have h2 : IsBudgetFeasible π (M.budget i) ((2 : ℝ) • x i) :=
        ⟨fun g => mul_nonneg (by norm_num) (hdem.1.1 g),
          by rw [expenditure_smul_right, ← hexp0, mul_zero]; exact (hbudget i).le⟩
      have hle := hdem.2 _ h2
      rw [hhom i hdem.1.1 two_pos] at hle
      linarith [hpos i]
    · set c : ℝ := M.budget i / expenditure π (x i)
      have hc1 : 1 < c := (one_lt_div hexp_pos).2 hlt
      have hc_feas : IsBudgetFeasible π (M.budget i) (c • x i) :=
        ⟨fun g => mul_nonneg (by linarith) (hdem.1.1 g),
          by rw [expenditure_smul_right, div_mul_cancel₀ _ hexp_pos.ne']⟩
      have hle := hdem.2 _ hc_feas
      rw [hhom i hdem.1.1 (by linarith)] at hle
      nlinarith [hpos i]
  have hsup_eq : expenditure π M.supply = M.totalBudget := by
    calc expenditure π M.supply
        = ∑ g : G, π g * ∑ i : I, x i g :=
            (expenditure_eq_sum π M.supply).trans
              (sum_congr rfl fun g _ => by linarith [heq.2.2.2 g])
      _ = ∑ i : I, expenditure π (x i) := by
            simp only [expenditure_eq_sum, mul_sum]; exact sum_comm
      _ = M.totalBudget := (sum_congr rfl fun i _ => hexp_eq i).trans M.totalBudget_eq_sum.symm
  rw [isMaxOn_iff]
  intro y hy
  -- For each buyer `i`, homogeneity and optimality give `u_i(y_i) / u_i(x_i) ≤ π · y_i / e_i`.
  have hratio : ∀ i : I, M.utility i (y i) / M.utility i (x i) ≤
      expenditure π (y i) / M.budget i := fun i => by
    have hdem := Market.mem_demandSet.1 (M.mem_demandSet.1 (heq.2.1 i))
    have hpy_pos : 0 < expenditure π (y i) := by
      refine lt_of_le_of_ne (expenditure_nonneg heq.1 (hy.1.1 i)) fun h0 => ?_
      set c : ℝ := (M.utility i (x i) + 1) / M.utility i (y i)
      have hc : 0 < c := div_pos (by linarith [hpos i]) (hy.2 i)
      have hc_feas : IsBudgetFeasible π (M.budget i) (c • y i) :=
        ⟨fun g => mul_nonneg hc.le (hy.1.1 i g),
          by rw [expenditure_smul_right, ← h0, mul_zero]; exact (hbudget i).le⟩
      have hle := hdem.2 _ hc_feas
      rw [hhom i (hy.1.1 i) hc, div_mul_cancel₀ _ (hy.2 i).ne'] at hle
      linarith
    set c : ℝ := M.budget i / expenditure π (y i)
    have hc : 0 < c := div_pos (hbudget i) hpy_pos
    have hc_feas : IsBudgetFeasible π (M.budget i) (c • y i) :=
      ⟨fun g => mul_nonneg hc.le (hy.1.1 i g),
        by rw [expenditure_smul_right, div_mul_cancel₀ _ hpy_pos.ne']⟩
    have hle := hdem.2 _ hc_feas
    rw [hhom i (hy.1.1 i) hc] at hle
    have hmul : M.budget i * M.utility i (y i) ≤ M.utility i (x i) * expenditure π (y i) := by
      have h1 := (div_mul_eq_mul_div (M.budget i) (expenditure π (y i)) (M.utility i (y i))).symm ▸
        hle
      exact (div_le_iff₀ hpy_pos).1 h1
    exact (div_le_div_iff₀ (hpos i) (hbudget i)).2 (by linarith)
  have hdiff : M.eisenbergObjective y - M.eisenbergObjective x ≤ 0 := by
    calc M.eisenbergObjective y - M.eisenbergObjective x
        = ∑ i : I, M.budget i * (Real.log (M.utility i (y i)) - Real.log (M.utility i (x i))) := by
            simp only [eisenbergObjective, ← sum_sub_distrib, ← mul_sub]
      _ ≤ ∑ i : I, M.budget i * (M.utility i (y i) / M.utility i (x i) - 1) :=
            sum_le_sum fun i _ => by
              rw [← Real.log_div (hy.2 i).ne' (hpos i).ne']
              exact mul_le_mul_of_nonneg_left
                (Real.log_le_sub_one_of_pos (div_pos (hy.2 i) (hpos i))) (hbudget i).le
      _ ≤ ∑ i : I, (expenditure π (y i) - M.budget i) :=
            sum_le_sum fun i _ => by
              have h1 := mul_le_mul_of_nonneg_left (sub_le_sub_right (hratio i) 1) (hbudget i).le
              have h2 : M.budget i * (expenditure π (y i) / M.budget i - 1) =
                  expenditure π (y i) - M.budget i := by
                rw [mul_sub, mul_one, mul_div_cancel₀ _ (hbudget i).ne']
              exact h1.trans_eq h2
      _ = (∑ g : G, π g * ∑ i : I, y i g) - M.totalBudget := by
            rw [sum_sub_distrib, ← M.totalBudget_eq_sum]
            congr 1
            simp only [expenditure_eq_sum, mul_sum]
            exact sum_comm
      _ ≤ expenditure π M.supply - M.totalBudget :=
            sub_le_sub_right ((expenditure_eq_sum π M.supply).symm ▸
              sum_le_sum fun g _ => mul_le_mul_of_nonneg_left (hy.1.2 g) (heq.1 g)) _
      _ = 0 := by rw [hsup_eq, sub_self]
  linarith

/-- **Full equivalence of Eisenberg's convex program** (Eisenberg 1961;
[CodenottiVaradarajan2007], Section 6.2, pp. 141–142): for a Fisher market with positive budgets,
concave positively homogeneous-of-degree-`1` utilities, and a positive-utility feasible allocation
`x` at which each `M.utility i` is differentiable within `ℝ_+^G`, `x` participates in a Fisher
market equilibrium `(x, π)` if and only if `x` maximizes `M.eisenbergObjective` over
`{y | M.IsPositiveUtilityAllocation y}`. -/
theorem exists_isEquilibrium_iff_isMaxOn_eisenbergObjective [Fintype G] {M : FisherMarket I G}
    (hbudget : ∀ i, 0 < M.budget i)
    (hconc : ∀ i, ConcaveOn ℝ {b : G → ℝ | ∀ g, 0 ≤ b g} (M.utility i))
    (hhom : ∀ i, IsHomogeneousDegOne (M.utility i))
    {x : I → G → ℝ} (hx : M.IsPositiveUtilityAllocation x)
    (hdiff : ∀ i : I, DifferentiableWithinAt ℝ (M.utility i) {b : G → ℝ | ∀ g, 0 ≤ b g} (x i)) :
    (∃ π : G → ℝ, M.IsEquilibrium x π) ↔
      IsMaxOn M.eisenbergObjective {y | M.IsPositiveUtilityAllocation y} x :=
  ⟨fun ⟨_, heq⟩ => heq.isMaxOn_eisenbergObjective hbudget hhom hx.2,
    fun hmax =>
      let ⟨π, heq, _⟩ :=
        exists_isEquilibrium_of_isMaxOn_eisenbergObjective hbudget hconc hhom hx hmax hdiff
      ⟨π, heq⟩⟩

end EisenbergProgram

end FisherMarket

/-! ### Concrete instances: Linear Fisher markets and CES Fisher markets -/

section Instances

variable {I G : Type*} [Fintype G]

/-- Linear utility `linearUtility v` is positively homogeneous of degree `1` on `ℝ_+^G`. -/
theorem isHomogeneousDegOne_linearUtility (v : G → ℝ) :
    IsHomogeneousDegOne (linearUtility v) := by
  intro b _ c _
  simp only [linearUtility_eq_sum, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun g _ => by ring

/-- Linear utility `linearUtility v` is concave on `ℝ_+^G`. -/
theorem concaveOn_linearUtility (v : G → ℝ) :
    ConcaveOn ℝ {b : G → ℝ | ∀ g, 0 ≤ b g} (linearUtility v) := by
  refine ⟨fun x hx y hy a b ha hb _ g => add_nonneg (mul_nonneg ha (hx g)) (mul_nonneg hb (hy g)),
    fun x _ y _ a b _ _ _ => le_of_eq ?_⟩
  simp only [linearUtility_eq_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    sum_add_distrib, mul_sum]
  congr 1 <;> exact sum_congr rfl fun g _ => by ring

/-- Linear utility `linearUtility v` is Fréchet differentiable everywhere. -/
theorem differentiableAt_linearUtility (v b : G → ℝ) :
    DifferentiableAt ℝ (linearUtility v) b := by
  have heq : linearUtility v = fun x : G → ℝ => ∑ g : G, v g * x g :=
    funext fun x => linearUtility_eq_sum v x
  rw [heq]
  exact DifferentiableAt.fun_sum fun g _ =>
    (differentiableAt_const (v g)).mul (differentiableAt_pi.1 differentiableAt_id g)

/-- On `LinearFisherMarket`, `toFisherMarket.eisenbergObjective` coincides with
`LinearFisherMarket.eisenbergGaleObjective`. -/
theorem LinearFisherMarket.toFisherMarket_eisenbergObjective [Fintype I]
    (M : LinearFisherMarket I G) (x : I → G → ℝ) :
    M.toFisherMarket.eisenbergObjective x = M.eisenbergGaleObjective x := by
  simp only [FisherMarket.eisenbergObjective_eq, LinearFisherMarket.eisenbergGaleObjective_eq,
    LinearFisherMarket.toFisherMarket_budget, LinearFisherMarket.toFisherMarket_utility,
    LinearFisherMarket.buyerUtility_eq]

/-- CES utility `cesUtility α ρ` (`α ≥ 0`, `ρ ≠ 0`) is positively homogeneous of degree `1`. -/
theorem isHomogeneousDegOne_cesUtility {α : G → ℝ} {ρ : ℝ}
    (hα : ∀ g, 0 ≤ α g) (hρ : ρ ≠ 0) :
    IsHomogeneousDegOne (cesUtility α ρ) :=
  fun _ hb _ hc => cesUtility_smul hα hρ hb hc

/-- Explicit Fréchet derivative of `cesUtility α ρ` at any strictly positive bundle `b > 0`
(`α > 0`, `ρ ≠ 0`). -/
theorem hasFDerivAt_cesUtility [Nonempty G] {α b : G → ℝ} {ρ : ℝ}
    (hα : ∀ g, 0 < α g) (hρ : ρ ≠ 0) (hb : ∀ g, 0 < b g) :
    HasFDerivAt (cesUtility α ρ)
      (((∑ k : G, α k * (b k) ^ ρ) ^ (1 / ρ - 1)) •
        ∑ g : G, (α g * (b g) ^ (ρ - 1)) • ContinuousLinearMap.proj (R := ℝ) g) b := by
  set S : ℝ := ∑ k : G, α k * (b k) ^ ρ
  have hS_pos : 0 < S :=
    sum_pos (fun k _ => mul_pos (hα k) (Real.rpow_pos_of_pos (hb k) ρ)) univ_nonempty
  have hterm : ∀ g : G,
      HasFDerivAt (fun x : G → ℝ => α g * (x g) ^ ρ)
        ((α g * (ρ * (b g) ^ (ρ - 1))) • ContinuousLinearMap.proj (R := ℝ) g) b := fun g => by
    have hproj : HasFDerivAt (fun x : G → ℝ => x g) (ContinuousLinearMap.proj (R := ℝ) g) b :=
      hasFDerivAt_apply g b
    have hrpow : HasDerivAt (fun t : ℝ => t ^ ρ) (ρ * (b g) ^ (ρ - 1)) (b g) :=
      Real.hasDerivAt_rpow_const (Or.inl (hb g).ne')
    have hcomp := (hrpow.comp_hasFDerivAt b hproj).const_mul (α g)
    simp only [Function.comp_apply, smul_smul] at hcomp
    exact hcomp
  have hsum : HasFDerivAt (fun x : G → ℝ => ∑ g : G, α g * (x g) ^ ρ)
      (∑ g : G, (α g * (ρ * (b g) ^ (ρ - 1))) • ContinuousLinearMap.proj (R := ℝ) g) b :=
    HasFDerivAt.fun_sum fun g _ => hterm g
  have houter : HasDerivAt (fun t : ℝ => t ^ (1 / ρ)) ((1 / ρ) * S ^ (1 / ρ - 1)) S :=
    Real.hasDerivAt_rpow_const (Or.inl hS_pos.ne')
  have hcomp := houter.comp_hasFDerivAt b hsum
  have hev : cesUtility α ρ =ᶠ[𝓝 b] fun x : G → ℝ => (∑ g : G, α g * (x g) ^ ρ) ^ (1 / ρ) := by
    have hopen : IsOpen {x : G → ℝ | ∀ g, 0 < x g} := by
      simpa only [Set.ofPred_forall] using
        isOpen_iInter_of_finite fun g : G => isOpen_lt continuous_const (continuous_apply g)
    exact Filter.eventually_of_mem (hopen.mem_nhds hb) fun x hx => cesUtility_of_bundle_pos α ρ hx
  have hfinal := hcomp.congr_of_eventuallyEq hev
  convert hfinal using 1
  ext v
  simp only [smul_apply, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun g _ => ?_
  field_simp [hρ]

/-- **Automatic strict positivity of CES Eisenberg maximizers**: in a Fisher market with CES
utilities `cesUtility (α i) (ρ i)` (`α > 0`, `ρ < 1`, `ρ ≠ 0`), positive buyer budgets, and
positive good supplies, every maximizer `x` of `M.eisenbergObjective` over positive-utility feasible
allocations assigns strictly positive quantity `0 < x i g` of every good to every buyer. -/
theorem cesFisherMarket_pos_of_isMaxOn [Fintype I] {M : FisherMarket I G}
    {α : I → G → ℝ} {ρ : I → ℝ}
    (hutil : ∀ i, M.utility i = cesUtility (α i) (ρ i))
    (hα : ∀ i g, 0 < α i g) (hρ1 : ∀ i, ρ i < 1) (hρ0 : ∀ i, ρ i ≠ 0)
    (hbudget : ∀ i, 0 < M.budget i) (hsupply : ∀ g, 0 < M.supply g)
    {x : I → G → ℝ} (hx : M.IsPositiveUtilityAllocation x)
    (hmax : IsMaxOn M.eisenbergObjective {y | M.IsPositiveUtilityAllocation y} x)
    (i₀ : I) (g₀ : G) :
    0 < x i₀ g₀ := by
  classical
  by_contra hnot
  have hx0 : x i₀ g₀ = 0 := le_antisymm (not_lt.1 hnot) (hx.1.1 i₀ g₀)
  rcases lt_or_gt_of_ne (hρ0 i₀) with hneg | hpos
  · have hu0 : M.utility i₀ (x i₀) = 0 := by
      rw [hutil i₀]
      exact cesUtility_of_neg_of_exists_nonpos (α i₀) hneg ⟨g₀, hx0.le⟩
    linarith [hx.2 i₀]
  · -- When `0 < ρ i₀ < 1`, `∂u_{i₀}/∂x_{i₀ g₀} = +∞` at `x i₀ g₀ = 0`, contradicting optimality.
    have hsum_le : ∑ i : I, x i g₀ ≤ M.supply g₀ := hx.1.2 g₀
    rcases hsum_le.eq_or_lt with hfull | hslack
    · -- Good `g₀` is fully allocated; some buyer `i₁ ≠ i₀` holds `x i₁ g₀ > 0`.
      obtain ⟨i₁, -, hi₁_pos⟩ := Finset.exists_lt_of_sum_lt (s := univ) (f := fun _ => (0 : ℝ))
        (g := fun i => x i g₀) (by rw [sum_const_zero, hfull]; exact hsupply g₀)
      have hne : i₀ ≠ i₁ := fun h => by rw [← h, hx0] at hi₁_pos; exact lt_irrefl _ hi₁_pos
      have hsum_pos_of_pos : ∀ i : I, 0 < ρ i → 0 < ∑ g : G, α i g * (x i g) ^ (ρ i) :=
        fun i hρi => by
          have h1 : 0 < M.utility i (x i) := hx.2 i
          rw [hutil i, cesUtility_of_pos_exp hρi] at h1
          by_contra hle
          have h0 : ∑ g : G, α i g * (x i g) ^ (ρ i) = 0 := le_antisymm (not_lt.1 hle)
            (sum_nonneg fun g _ => mul_nonneg (hα i g).le (Real.rpow_nonneg (hx.1.1 i g) _))
          rw [h0, Real.zero_rpow (one_div_ne_zero hρi.ne')] at h1
          exact lt_irrefl _ h1
      -- Transfer `ε > 0` of good `g₀` from `i₁` to `i₀`.
      set U₀ : ℝ := ∑ g : G, α i₀ g * (x i₀ g) ^ (ρ i₀)
      have hU₀_pos : 0 < U₀ := hsum_pos_of_pos i₀ hpos
      -- Bound the utility loss of `i₁` linearly in `ε` using concavity / derivative along `g₀`.
      set a₀ : ℝ := α i₀ g₀
      have ha₀ : 0 < a₀ := hα i₀ g₀
      -- Build a Lipschitz constant `K > 0` for `ε ↦ e₁ (log u₁(x₁) - log u₁(x₁ - ε e_{g₀}))`.
      have hloss : ∃ (δ₁ : ℝ) (K : ℝ), 0 < δ₁ ∧ δ₁ ≤ x i₁ g₀ ∧ 0 ≤ K ∧
          ∀ ε : ℝ, 0 < ε → ε ≤ δ₁ →
            0 < M.utility i₁ (Function.update (x i₁) g₀ (x i₁ g₀ - ε)) ∧
            M.budget i₁ * Real.log (M.utility i₁ (x i₁)) -
              M.budget i₁ * Real.log (M.utility i₁ (Function.update (x i₁) g₀ (x i₁ g₀ - ε))) ≤
              K * ε := by
        let φ₁ : ℝ → ℝ := fun ε => M.utility i₁ (Function.update (x i₁) g₀ (x i₁ g₀ - ε))
        have hφ₁_0 : φ₁ 0 = M.utility i₁ (x i₁) := by simp [φ₁]
        have hφ₁_pos0 : 0 < φ₁ 0 := hφ₁_0 ▸ hx.2 i₁
        -- `φ₁` is continuous at `0` (in fact differentiable at `0` since `x i₁ g₀ > 0`!).
        have hφ₁_deriv : ∃ d : ℝ, HasDerivAt φ₁ d 0 := by
          rcases lt_or_gt_of_ne (hρ0 i₁) with hρ₁_neg | hρ₁_pos
          · have hx₁_pos : ∀ g, 0 < x i₁ g := by
              by_contra hnot1; push Not at hnot1
              have hu0 : M.utility i₁ (x i₁) = 0 := by
                rw [hutil i₁]; exact cesUtility_of_neg_of_exists_nonpos (α i₁) hρ₁_neg hnot1
              linarith [hx.2 i₁]
            have hupd_eq : (fun ε : ℝ => Function.update (x i₁) g₀ (x i₁ g₀ - ε)) =
                fun ε : ℝ => x i₁ + ε • Pi.single g₀ (-1 : ℝ) := by
              funext ε g
              by_cases hg : g = g₀
              · subst hg; simp [sub_eq_add_neg]
              · simp [hg]
            have hupd_deriv : HasDerivAt (fun ε : ℝ => Function.update (x i₁) g₀ (x i₁ g₀ - ε))
                (Pi.single g₀ (-1 : ℝ)) 0 := by
              rw [hupd_eq]
              simpa only [one_smul] using
                ((hasDerivAt_id' (0 : ℝ)).smul_const (Pi.single g₀ (-1 : ℝ))).const_add (x i₁)
            have hI : Nonempty G := ⟨g₀⟩
            have hf := hasFDerivAt_cesUtility (hα i₁) (hρ0 i₁) hx₁_pos
            rw [← hutil i₁] at hf
            have hupd0 : Function.update (x i₁) g₀ (x i₁ g₀ - (0 : ℝ)) = x i₁ := by simp
            have hcomp := (hupd0.symm ▸ hf).comp_hasDerivAt 0 hupd_deriv
            exact ⟨_, hcomp⟩
          · set S₁ : ℝ := ∑ g : G, α i₁ g * (x i₁ g) ^ (ρ i₁)
            have hS₁_pos : 0 < S₁ := hsum_pos_of_pos i₁ hρ₁_pos
            have hsum_eq : ∀ ε : ℝ,
                ∑ g : G, α i₁ g * (Function.update (x i₁) g₀ (x i₁ g₀ - ε) g) ^ (ρ i₁) =
                  S₁ - α i₁ g₀ * (x i₁ g₀) ^ (ρ i₁) + α i₁ g₀ * (x i₁ g₀ - ε) ^ (ρ i₁) := by
              intro ε
              have h1 : ∀ g : G,
                  α i₁ g * (Function.update (x i₁) g₀ (x i₁ g₀ - ε) g) ^ (ρ i₁) -
                    α i₁ g * (x i₁ g) ^ (ρ i₁) =
                  if g = g₀ then
                    α i₁ g₀ * (x i₁ g₀ - ε) ^ (ρ i₁) - α i₁ g₀ * (x i₁ g₀) ^ (ρ i₁)
                  else 0 := fun g => by by_cases hg : g = g₀ <;> simp [hg]
              have hdiff :
                  (∑ g : G, α i₁ g * (Function.update (x i₁) g₀ (x i₁ g₀ - ε) g) ^ (ρ i₁)) - S₁ =
                    α i₁ g₀ * (x i₁ g₀ - ε) ^ (ρ i₁) - α i₁ g₀ * (x i₁ g₀) ^ (ρ i₁) := by
                dsimp only [S₁]
                rw [← sum_sub_distrib, sum_congr rfl fun g _ => h1 g, sum_ite_eq']
                simp only [Finset.mem_univ, ↓reduceIte]
              linarith
            have hinner : HasDerivAt
                (fun ε : ℝ => S₁ - α i₁ g₀ * (x i₁ g₀) ^ (ρ i₁) + α i₁ g₀ * (x i₁ g₀ - ε) ^ (ρ i₁))
                (-(α i₁ g₀ * (ρ i₁ * (x i₁ g₀) ^ (ρ i₁ - 1)))) 0 := by
              have hsub : HasDerivAt (fun ε : ℝ => x i₁ g₀ - ε) (-1) 0 :=
                (hasDerivAt_id' (0 : ℝ)).const_sub (x i₁ g₀)
              have h0 : x i₁ g₀ - (0 : ℝ) = x i₁ g₀ := sub_zero _
              have hr := (h0 ▸ Real.hasDerivAt_rpow_const (x := x i₁ g₀) (p := ρ i₁)
                (Or.inl hi₁_pos.ne')).comp 0 hsub
              have h2 := (hr.const_mul (α i₁ g₀)).const_add (S₁ - α i₁ g₀ * (x i₁ g₀) ^ (ρ i₁))
              simp only [Function.comp_def, sub_zero] at h2
              convert h2 using 1; ring
            have houter : HasDerivAt (fun t : ℝ => t ^ (1 / ρ i₁))
                ((1 / ρ i₁) * S₁ ^ (1 / ρ i₁ - 1))
                (S₁ - α i₁ g₀ * (x i₁ g₀) ^ (ρ i₁) + α i₁ g₀ * (x i₁ g₀ - 0) ^ (ρ i₁)) := by
              simpa only [sub_zero, sub_add_cancel] using
                Real.hasDerivAt_rpow_const (x := S₁) (p := 1 / ρ i₁) (Or.inl hS₁_pos.ne')
            have hφ_eq : φ₁ = fun ε =>
                (S₁ - α i₁ g₀ * (x i₁ g₀) ^ (ρ i₁) +
                  α i₁ g₀ * (x i₁ g₀ - ε) ^ (ρ i₁)) ^ (1 / ρ i₁) := by
              funext ε
              dsimp only [φ₁]
              rw [hutil i₁, cesUtility_of_pos_exp hρ₁_pos, hsum_eq ε]
            rw [hφ_eq]
            have hcomp := houter.comp 0 hinner
            simp only [Function.comp_def] at hcomp
            exact ⟨_, hcomp⟩
        obtain ⟨d, hd⟩ := hφ₁_deriv
        let g1 : ℝ → ℝ := fun ε => M.budget i₁ * Real.log (φ₁ ε)
        have hg1_deriv : HasDerivAt g1 (M.budget i₁ * (d / φ₁ 0)) 0 := by
          have hlog := ((Real.hasDerivAt_log hφ₁_pos0.ne').comp 0 hd).const_mul (M.budget i₁)
          simp only [Function.comp_apply] at hlog
          convert hlog using 1; ring
        have hpos_ev : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < φ₁ ε :=
          hd.continuousAt.eventually (Ioi_mem_nhds hφ₁_pos0)
        set D : ℝ := M.budget i₁ * (d / φ₁ 0)
        have hslope_ev : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), D - 1 < slope g1 0 ε :=
          (hasDerivAt_iff_tendsto_slope.1 hg1_deriv).eventually (Ioi_mem_nhds (by linarith))
        obtain ⟨δ, hδ_pos, hδ_both⟩ := Metric.mem_nhdsWithin_iff.1
          ((hpos_ev.filter_mono nhdsWithin_le_nhds).and hslope_ev)
        set δ₁ : ℝ := min (x i₁ g₀) (δ / 2)
        have hδ₁_pos : 0 < δ₁ := lt_min hi₁_pos (half_pos hδ_pos)
        refine ⟨δ₁, |D| + 1, hδ₁_pos, min_le_left _ _, by positivity, fun ε hε0 hεδ₁ => ?_⟩
        have hε_ball : ε ∈ Metric.ball (0 : ℝ) δ ∩ ({0} : Set ℝ)ᶜ := by
          refine ⟨?_, hε0.ne'⟩
          rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε0]
          linarith [hεδ₁.trans (min_le_right _ _)]
        obtain ⟨hφ_pos, hslope_gt⟩ := hδ_both hε_ball
        rw [slope_def_field, sub_zero] at hslope_gt
        have hmul := (lt_div_iff₀ hε0).1 hslope_gt
        refine ⟨hφ_pos, ?_⟩
        dsimp only [g1] at hmul
        rw [hφ₁_0] at hmul
        have hD_le : -D ≤ |D| := neg_le_abs D
        nlinarith
      obtain ⟨δ₁, K, hδ₁_pos, hδ₁_le, hK_nn, hloss_bound⟩ := hloss
      -- Gain for buyer `i₀`: `e_{i₀} (log u₀(x₀ + ε e_{g₀}) - log u₀(x₀)) ≥ c₀ * ε^{ρ₀}`
      -- for small `ε > 0`, where `0 < ρ₀ < 1`.
      set c₀ : ℝ := M.budget i₀ * a₀ / (2 * ρ i₀ * U₀)
      have hc₀_pos : 0 < c₀ :=
        div_pos (mul_pos (hbudget i₀) ha₀) (mul_pos (mul_pos two_pos hpos) hU₀_pos)
      -- Choose `ε > 0` with `ε ≤ δ₁`, `a₀ * ε ^ (ρ i₀) ≤ U₀`, and `K * ε < c₀ * ε ^ (ρ i₀)`.
      have h1sub_pos : 0 < 1 - ρ i₀ := by linarith [hρ1 i₀]
      set ε : ℝ := min δ₁ (min ((U₀ / a₀) ^ (1 / ρ i₀)) ((c₀ / (2 * (K + 1))) ^ (1 / (1 - ρ i₀))))
      have hε_pos : 0 < ε := lt_min hδ₁_pos
        (lt_min (Real.rpow_pos_of_pos (div_pos hU₀_pos ha₀) _)
          (Real.rpow_pos_of_pos (div_pos hc₀_pos (by positivity)) _))
      have hε_le_δ₁ : ε ≤ δ₁ := min_le_left _ _
      have hε_le_U : a₀ * ε ^ (ρ i₀) ≤ U₀ := by
        have h1 : ε ≤ (U₀ / a₀) ^ (1 / ρ i₀) := (min_le_right _ _).trans (min_le_left _ _)
        have h2 := Real.rpow_le_rpow hε_pos.le h1 hpos.le
        rw [← Real.rpow_mul (div_pos hU₀_pos ha₀).le, one_div_mul_cancel hpos.ne',
          Real.rpow_one] at h2
        exact (le_div_iff₀' ha₀).1 h2
      have hK_lt_gain : K * ε < c₀ * ε ^ (ρ i₀) := by
        have h1 : ε ≤ (c₀ / (2 * (K + 1))) ^ (1 / (1 - ρ i₀)) :=
          (min_le_right _ _).trans (min_le_right _ _)
        have h2 := Real.rpow_le_rpow hε_pos.le h1 h1sub_pos.le
        rw [← Real.rpow_mul (div_pos hc₀_pos (by positivity)).le,
          one_div_mul_cancel h1sub_pos.ne', Real.rpow_one] at h2
        have h3 : 2 * (K + 1) * ε ^ (1 - ρ i₀) ≤ c₀ := (le_div_iff₀' (by positivity)).1 h2
        have h4 : (K + 1) * ε ^ (1 - ρ i₀) < c₀ := by
          have : 0 < (K + 1) * ε ^ (1 - ρ i₀) :=
            mul_pos (by linarith) (Real.rpow_pos_of_pos hε_pos _)
          linarith
        have h5 := mul_lt_mul_of_pos_right h4 (Real.rpow_pos_of_pos hε_pos (ρ i₀))
        have hexp : ε ^ (1 - ρ i₀) * ε ^ (ρ i₀) = ε := by
          rw [← Real.rpow_add hε_pos, sub_add_cancel, Real.rpow_one]
        rw [mul_assoc, hexp] at h5
        nlinarith
      -- Construct feasible allocation `y` transferring `ε` of `g₀` from `i₁` to `i₀`.
      let y : I → G → ℝ := fun i =>
        if i = i₀ then Function.update (x i₀) g₀ ε
        else if i = i₁ then Function.update (x i₁) g₀ (x i₁ g₀ - ε)
        else x i
      have hy_u0 : M.utility i₀ (y i₀) = (U₀ + a₀ * ε ^ (ρ i₀)) ^ (1 / ρ i₀) := by
        simp only [y, ↓reduceIte, hutil i₀, cesUtility_of_pos_exp hpos]
        congr 1
        have hterm : ∀ g : G,
            α i₀ g * (Function.update (x i₀) g₀ ε g) ^ (ρ i₀) - α i₀ g * (x i₀ g) ^ (ρ i₀) =
              if g = g₀ then a₀ * ε ^ (ρ i₀) else 0 := fun g => by
          by_cases hg : g = g₀
          · subst hg; simp [a₀, hx0, Real.zero_rpow hpos.ne']
          · simp [hg]
        have hdiff : (∑ g : G, α i₀ g * (Function.update (x i₀) g₀ ε g) ^ (ρ i₀)) - U₀ =
            a₀ * ε ^ (ρ i₀) := by
          dsimp only [U₀]
          rw [← sum_sub_distrib, sum_congr rfl fun g _ => hterm g, sum_ite_eq']
          simp only [Finset.mem_univ, ↓reduceIte]
        linarith
      have hy_u0_pos : 0 < M.utility i₀ (y i₀) := by
        rw [hy_u0]
        exact Real.rpow_pos_of_pos (add_pos hU₀_pos (mul_pos ha₀ (Real.rpow_pos_of_pos hε_pos _))) _
      have hloss1 := hloss_bound ε hε_pos hε_le_δ₁
      have hy_feas : M.IsPositiveUtilityAllocation y := by
        refine ⟨⟨fun i g => ?_, fun g => ?_⟩, fun i => ?_⟩
        · dsimp only [y]
          split_ifs with h1 h2
          · by_cases hg : g = g₀
            · subst hg; simp [hε_pos.le]
            · simp [hg, hx.1.1 i₀ g]
          · by_cases hg : g = g₀
            · subst hg; simp; linarith [hε_le_δ₁.trans hδ₁_le]
            · simp [hg, hx.1.1 i₁ g]
          · exact hx.1.1 i g
        · by_cases hg : g = g₀
          · subst g
            have hsum_y : ∑ i : I, y i g₀ = ∑ i : I, x i g₀ := by
              have hdiff_i : ∀ i : I, y i g₀ - x i g₀ =
                  if i = i₀ then ε else if i = i₁ then -ε else 0 := fun i => by
                dsimp only [y]
                split_ifs with h1 h2
                · subst i; simp [hx0]
                · subst i; simp
                · simp
              have h0 : (∑ i : I, y i g₀) - (∑ i : I, x i g₀) = 0 := by
                rw [← sum_sub_distrib, sum_congr rfl fun i _ => hdiff_i i,
                  Fintype.sum_eq_add i₀ i₁ hne fun i hi => by simp [hi.1, hi.2]]
                simp [hne.symm]
              linarith
            rw [hsum_y]; exact hx.1.2 g₀
          · have hyeq : ∀ i : I, y i g = x i g := fun i => by
              dsimp only [y]
              split_ifs with h1 h2
              · subst i; simp [hg]
              · subst i; simp [hg]
              · rfl
            simp_rw [hyeq]; exact hx.1.2 g
        · dsimp only [y]
          split_ifs with h1 h2
          · subst i; simpa only [y, ↓reduceIte] using hy_u0_pos
          · subst i; exact hloss1.1
          · exact hx.2 i
      -- Compare `M.eisenbergObjective y` and `M.eisenbergObjective x`.
      have hgain0 : c₀ * ε ^ (ρ i₀) ≤
          M.budget i₀ * Real.log (M.utility i₀ (y i₀)) -
            M.budget i₀ * Real.log (M.utility i₀ (x i₀)) := by
        have hux0 : M.utility i₀ (x i₀) = U₀ ^ (1 / ρ i₀) := by
          rw [hutil i₀, cesUtility_of_pos_exp hpos]
        rw [hy_u0, hux0, ← mul_sub, ← Real.log_div
          (Real.rpow_pos_of_pos (by positivity) _).ne' (Real.rpow_pos_of_pos hU₀_pos _).ne',
          ← Real.div_rpow (by positivity) hU₀_pos.le, Real.log_rpow (by positivity)]
        set z : ℝ := a₀ * ε ^ (ρ i₀) / U₀
        have hz_pos : 0 < z := div_pos (mul_pos ha₀ (Real.rpow_pos_of_pos hε_pos _)) hU₀_pos
        have hz_le1 : z ≤ 1 := (div_le_one hU₀_pos).2 hε_le_U
        have hlog_ge : z / 2 ≤ Real.log (1 + z) := by
          have h1 := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1 + z)
          have h2 : z / 2 ≤ 1 - (1 + z)⁻¹ := by
            have : 1 - (1 + z)⁻¹ = z / (1 + z) := by field_simp [(by linarith : 1 + z ≠ 0)]; ring
            rw [this]
            exact div_le_div_of_nonneg_left hz_pos.le (by linarith) (by linarith)
          exact h2.trans h1
        have harg : (U₀ + a₀ * ε ^ (ρ i₀)) / U₀ = 1 + z := by
          dsimp only [z]; field_simp [hU₀_pos.ne']
        rw [harg]
        have hmul := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hlog_ge (one_div_pos.2 hpos).le) (hbudget i₀).le
        have hsimp : M.budget i₀ * (1 / ρ i₀ * (z / 2)) = c₀ * ε ^ (ρ i₀) := by
          dsimp only [c₀, z]; field_simp [hpos.ne', hU₀_pos.ne']
        linarith
      have hobj_diff : M.eisenbergObjective y - M.eisenbergObjective x =
          (M.budget i₀ * Real.log (M.utility i₀ (y i₀)) -
            M.budget i₀ * Real.log (M.utility i₀ (x i₀))) -
          (M.budget i₁ * Real.log (M.utility i₁ (x i₁)) -
            M.budget i₁ * Real.log (M.utility i₁ (y i₁))) := by
        simp only [FisherMarket.eisenbergObjective_eq, ← sum_sub_distrib]
        rw [Fintype.sum_eq_add i₀ i₁ hne fun i hi => by
          have : y i = x i := by simp [y, hi.1, hi.2]
          rw [this, sub_self]]
        ring
      have hy1_eq : y i₁ = Function.update (x i₁) g₀ (x i₁ g₀ - ε) := by simp [y, hne.symm]
      have hobj_le : M.eisenbergObjective y ≤ M.eisenbergObjective x :=
        isMaxOn_iff.1 hmax y hy_feas
      rw [hy1_eq] at hobj_diff
      linarith [hloss1.2]
    · -- Good `g₀` has unused supply `M.supply g₀ - ∑ i, x i g₀ > 0`; give it to `i₀`.
      set δ : ℝ := M.supply g₀ - ∑ i : I, x i g₀
      have hδ : 0 < δ := sub_pos.2 hslack
      let y : I → G → ℝ := fun i => if i = i₀ then Function.update (x i₀) g₀ δ else x i
      have hU_lt : M.utility i₀ (x i₀) < M.utility i₀ (y i₀) := by
        simp only [y, ↓reduceIte, hutil i₀, cesUtility_of_pos_exp hpos]
        have hsum_lt : ∑ g : G, α i₀ g * (x i₀ g) ^ (ρ i₀) <
            ∑ g : G, α i₀ g * (Function.update (x i₀) g₀ δ g) ^ (ρ i₀) :=
          sum_lt_sum (fun g _ => by
              by_cases hg : g = g₀
              · subst hg
                simp only [Function.update_self, hx0, Real.zero_rpow hpos.ne', mul_zero]
                exact mul_nonneg (hα i₀ g).le (Real.rpow_nonneg hδ.le _)
              · simp [hg])
            ⟨g₀, Finset.mem_univ g₀, by
              simp only [Function.update_self, hx0, Real.zero_rpow hpos.ne', mul_zero]
              exact mul_pos (hα i₀ g₀) (Real.rpow_pos_of_pos hδ _)⟩
        exact Real.rpow_lt_rpow
          (sum_nonneg fun g _ => mul_nonneg (hα i₀ g).le (Real.rpow_nonneg (hx.1.1 i₀ g) _))
          hsum_lt (one_div_pos.2 hpos)
      have hy_feas : M.IsPositiveUtilityAllocation y := by
        refine ⟨⟨fun i g => ?_, fun g => ?_⟩, fun i => ?_⟩
        · dsimp only [y]
          split_ifs with h1
          · by_cases hg : g = g₀
            · subst hg; simp [hδ.le]
            · simp [hg, hx.1.1 i₀ g]
          · exact hx.1.1 i g
        · by_cases hg : g = g₀
          · subst g
            have hdiff_i : ∀ i : I, y i g₀ - x i g₀ = if i = i₀ then δ else 0 := fun i => by
              dsimp only [y]; split_ifs with h1
              · subst i; simp [hx0]
              · simp
            have hsum_y : ∑ i : I, y i g₀ = M.supply g₀ := by
              have h0 : (∑ i : I, y i g₀) - (∑ i : I, x i g₀) = δ := by
                rw [← sum_sub_distrib, sum_congr rfl fun i _ => hdiff_i i, sum_ite_eq']
                simp only [Finset.mem_univ, ↓reduceIte]
              dsimp only [δ] at h0; linarith
            exact hsum_y.le
          · have hyeq : ∀ i : I, y i g = x i g := fun i => by
              dsimp only [y]
              split_ifs with h1
              · subst i; simp [hg]
              · rfl
            simp_rw [hyeq]; exact hx.1.2 g
        · by_cases h1 : i = i₀
          · subst i; exact (hx.2 i₀).trans hU_lt
          · have : y i = x i := by simp [y, h1]
            rw [this]; exact hx.2 i
      have hobj_lt : M.eisenbergObjective x < M.eisenbergObjective y := by
        simp only [FisherMarket.eisenbergObjective_eq]
        refine sum_lt_sum (fun i _ => ?_) ⟨i₀, Finset.mem_univ i₀,
          mul_lt_mul_of_pos_left (Real.log_lt_log (hx.2 i₀) hU_lt) (hbudget i₀)⟩
        by_cases h1 : i = i₀
        · subst i
          exact (mul_lt_mul_of_pos_left (Real.log_lt_log (hx.2 i₀) hU_lt) (hbudget i₀)).le
        · have : y i = x i := by simp [y, h1]
          rw [this]
      linarith [isMaxOn_iff.1 hmax y hy_feas]

/-- **Unconditional CES Fisher Market Equilibrium via Eisenberg's Program**
([CodenottiVaradarajan2007], Section 6.2, pp. 141–142): in any Fisher market with CES utilities
`cesUtility (α i) (ρ i)` (`α > 0`, `ρ < 1`, `ρ ≠ 0`), positive budgets, and positive supplies,
every maximizer `x` of `M.eisenbergObjective` over positive-utility feasible allocations is
strictly positive and admits strictly positive prices `π` forming an exact-clearing Fisher market
equilibrium `(x, π)`. -/
theorem cesFisherMarket_exists_isEquilibrium_of_isMaxOn [Fintype I] [Nonempty I] [Nonempty G]
    {M : FisherMarket I G} {α : I → G → ℝ} {ρ : I → ℝ}
    (hutil : ∀ i, M.utility i = cesUtility (α i) (ρ i))
    (hα : ∀ i g, 0 < α i g) (hρ1 : ∀ i, ρ i < 1) (hρ0 : ∀ i, ρ i ≠ 0)
    (hbudget : ∀ i, 0 < M.budget i) (hsupply : ∀ g, 0 < M.supply g)
    {x : I → G → ℝ} (hx : M.IsPositiveUtilityAllocation x)
    (hmax : IsMaxOn M.eisenbergObjective {y | M.IsPositiveUtilityAllocation y} x) :
    ∃ π : G → ℝ, (∀ g, 0 < π g) ∧ M.IsEquilibrium x π ∧ ∀ g : G, ∑ i : I, x i g = M.supply g := by
  classical
  have hx_pos : ∀ i g, 0 < x i g :=
    cesFisherMarket_pos_of_isMaxOn hutil hα hρ1 hρ0 hbudget hsupply hx hmax
  have hconc : ∀ i, ConcaveOn ℝ {b : G → ℝ | ∀ g, 0 ≤ b g} (M.utility i) := fun i =>
    hutil i ▸ concaveOn_cesUtility (hα i) (hρ1 i).le (hρ0 i)
  have hhom : ∀ i, IsHomogeneousDegOne (M.utility i) := fun i =>
    hutil i ▸ isHomogeneousDegOne_cesUtility (fun g => (hα i g).le) (hρ0 i)
  let L : I → (G → ℝ) →L[ℝ] ℝ := fun i =>
    ((∑ k : G, α i k * (x i k) ^ (ρ i)) ^ (1 / ρ i - 1)) •
      ∑ g : G, (α i g * (x i g) ^ (ρ i - 1)) • ContinuousLinearMap.proj (R := ℝ) g
  have hL : ∀ i, HasFDerivWithinAt (M.utility i) (L i) {b : G → ℝ | ∀ g, 0 ≤ b g} (x i) :=
    fun i => (hutil i ▸ hasFDerivAt_cesUtility (hα i) (hρ0 i) (hx_pos i)).hasFDerivWithinAt
  obtain ⟨π, lam, hkkt⟩ := FisherMarket.exists_isEisenbergKKT_of_isMaxOn hx hmax hL
  have hπ_pos : ∀ g : G, 0 < π g := fun g => by
    let i₀ : I := Classical.arbitrary I
    have hlam0 : lam i₀ g = 0 :=
      (mul_eq_zero.1 (hkkt.nonneg_slackness i₀ g)).resolve_right (hx_pos i₀ g).ne'
    have hstat := hkkt.stationarity i₀ g
    rw [hlam0, sub_zero] at hstat
    have hLi_pos : 0 < L i₀ (Pi.single g 1) := by
      dsimp only [L]
      simp only [smul_apply, FunLike.coe_sum, Finset.sum_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul]
      have hsum_val :
          ∑ k : G, α i₀ k * (x i₀ k) ^ (ρ i₀ - 1) * (Pi.single (M := fun _ => ℝ) g (1 : ℝ)) k =
            α i₀ g * (x i₀ g) ^ (ρ i₀ - 1) := by
        rw [Finset.sum_eq_single g (fun k _ hkg => by simp [Pi.single_eq_of_ne hkg])
          (fun h => (h (Finset.mem_univ g)).elim)]
        simp only [Pi.single_eq_same, mul_one]
      rw [hsum_val]
      have hS_pos : 0 < ∑ k : G, α i₀ k * (x i₀ k) ^ (ρ i₀) :=
        sum_pos (fun k _ => mul_pos (hα i₀ k) (Real.rpow_pos_of_pos (hx_pos i₀ k) _)) univ_nonempty
      exact mul_pos (Real.rpow_pos_of_pos hS_pos _)
        (mul_pos (hα i₀ g) (Real.rpow_pos_of_pos (hx_pos i₀ g) _))
    rw [← hstat]
    exact mul_pos (div_pos (hbudget i₀) (hx.2 i₀)) hLi_pos
  have heq := hkkt.isEquilibrium hbudget hconc hhom
  exact ⟨π, hπ_pos, heq, fun g => heq.sum_eq_supply_of_price_pos (hπ_pos g)⟩

end Instances

end Cslib.GameTheory.Market
