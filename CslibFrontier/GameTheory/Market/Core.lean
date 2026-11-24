/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Market.Welfare
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The core of an exchange economy and the Debreu–Scarf replica theorem

In an Arrow–Debreu exchange economy `E : ExchangeMarket I G`, a nonempty coalition `S : Finset I`
**blocks** (improves upon) an allocation `x` if `S` can redistribute its own initial endowments
`∑ i ∈ S, E.endowment i` among its members so that every member of `S` is weakly better off and at
least one member is strictly better off. The **core** (`ExchangeMarket.IsInCore`) consists of all
feasible allocations that no coalition can block ([DebreuScarf1963]).

Building on `CslibFrontier.GameTheory.Market.Welfare`, this module formalizes the cooperative-to-
competitive core theory of exchange economies:

1. **Core inclusion of competitive equilibria**
   (`ExchangeMarket.IsCompetitiveEquilibrium.isInCore`): in any locally nonsatiated exchange
   economy (with no convexity or continuity assumptions), every competitive equilibrium allocation
   belongs to the core, strengthening the First Welfare Theorem (`IsInCore.isParetoOptimal`) and
   individual rationality (`IsInCore.individuallyRational`).
2. **`r`-fold replica economies and equal treatment (`ExchangeMarket.replica`,
   `ExchangeMarket.eq_of_isInCore_replica`):** replicating each trader type `r ≥ 1` times on
   `I × Fin r` preserves competitive equilibria (hence every competitive equilibrium remains in the
   core of `E.replica r` for all `r ≥ 1`). Conversely, when utilities are strictly concave on
   `ℝ_+^G` (`StrictConcaveOn`), the **equal-treatment theorem** ([DebreuScarf1963]) shows via the
   underdog coalition of minimum-utility replicas that every allocation in the core of `E.replica r`
   assigns identical consumption bundles to all replicas of the same type.
3. **Debreu–Scarf core shrinking / equivalence theorem
   (`ExchangeMarket.exists_priceQuasiEquilibrium_of_forall_replica_isInCore`,
   `ExchangeMarket.exists_isCompetitiveEquilibrium_iff_forall_replica_isInCore`):** if a symmetric
   allocation `x` belongs to the core of `E.replica r` for **every** `r ≥ 1` in a locally
   nonsatiated economy with convex preferences (`HasConvexPreferences`), separating `negOrthant G`
   from the finite convex hull of strictly preferred net trades via integer replica coalitions
   produces a nonzero nonnegative price vector `p` supporting `(x, p)` as a price quasi-equilibrium
   of `E` **without lump-sum transfers** (`∀ i, expenditure p (x i) = E.income p i`). Under
   continuity on `ℝ_+^G` and strictly positive endowments (`∀ i g, 0 < E.endowment i g`), `x`
   participates in a competitive equilibrium of `E` if and only if its replication lies in the core
   of `E.replica r` for every `r ≥ 1`.

## Main definitions

* `Cslib.GameTheory.Market.ExchangeMarket.IsBlockedBy`,
  `Cslib.GameTheory.Market.ExchangeMarket.IsInCore`: coalition blocking and the core of an exchange
  market ([DebreuScarf1963]).
* `Cslib.GameTheory.Market.ExchangeMarket.replica`: `r`-fold replica exchange economy on
  `I × Fin r`.

## Main results

* `Cslib.GameTheory.Market.ExchangeMarket.IsInCore.isParetoOptimal`,
  `Cslib.GameTheory.Market.ExchangeMarket.IsInCore.individuallyRational`: core allocations are
  Pareto optimal and individually rational.
* `Cslib.GameTheory.Market.ExchangeMarket.IsCompetitiveEquilibrium.isInCore`: every competitive
  equilibrium allocation of a locally nonsatiated exchange economy lies in the core.
* `Cslib.GameTheory.Market.ExchangeMarket.eq_of_isInCore_replica`: **equal-treatment property** of
  replica-core allocations under strictly concave utilities ([DebreuScarf1963]).
* `ExchangeMarket.exists_priceQuasiEquilibrium_of_forall_replica_isInCore`,
  `ExchangeMarket.exists_isCompetitiveEquilibrium_of_forall_replica_isInCore`,
  `ExchangeMarket.exists_isCompetitiveEquilibrium_iff_forall_replica_isInCore`:
  **Debreu–Scarf core shrinking / equivalence theorem** ([DebreuScarf1963]).

## References

* [ArrowDebreu1954]
* [DebreuScarf1963] (primary PDF unverified)
-/

public section

namespace Cslib.GameTheory.Market

open Finset
open scoped BigOperators

namespace ExchangeMarket

/-! ### Coalition blocking, core allocations, and inclusion of competitive equilibria -/

section Core

variable {I G : Type*} [Fintype I] [Fintype G] (E : ExchangeMarket I G)

/-- Nonempty coalition `S : Finset I` **blocks** allocation `x` via `z : I → G → ℝ` if `z` is
nonnegative on `S`, uses at most the coalition's aggregate endowment `∑ i ∈ S, E.endowment i g` of
every good, leaves every member of `S` weakly better off, and makes at least one member strictly
better off ([DebreuScarf1963]). -/
@[expose] def IsBlockedBy (S : Finset I) (z x : I → G → ℝ) : Prop :=
  S.Nonempty ∧
    (∀ i ∈ S, ∀ g, 0 ≤ z i g) ∧
    (∀ g : G, ∑ i ∈ S, z i g ≤ ∑ i ∈ S, E.endowment i g) ∧
    (∀ i ∈ S, E.utility i (x i) ≤ E.utility i (z i)) ∧
    ∃ i ∈ S, E.utility i (x i) < E.utility i (z i)

/-- A feasible allocation `x` belongs to the **core** of `E` if no nonempty coalition blocks `x`. -/
@[expose] def IsInCore (x : I → G → ℝ) : Prop :=
  E.IsFeasibleAllocation x ∧ ∀ (S : Finset I) (z : I → G → ℝ), ¬ E.IsBlockedBy S z x

omit [Fintype G] in
/-- Blocking by the grand coalition `Finset.univ` rules out Pareto improvements, so every core
allocation is Pareto optimal when `I` is nonempty. -/
theorem IsInCore.isParetoOptimal [Nonempty I] {E : ExchangeMarket I G} {x : I → G → ℝ}
    (hcore : E.IsInCore x) : E.IsParetoOptimal x := by
  refine ⟨hcore.1, ?_⟩
  rintro ⟨y, hy_feas, hy_le, ⟨i₀, hi₀⟩⟩
  exact hcore.2 univ y ⟨univ_nonempty, fun i _ => hy_feas.1 i,
    fun g => by simpa only [← E.totalSupply_eq_sum] using hy_feas.2 g,
    fun i _ => hy_le i, ⟨i₀, mem_univ i₀, hi₀⟩⟩

omit [Fintype G] in
/-- Blocking by singleton coalitions `{i}` ensures **individual rationality**: every trader weakly
prefers their core bundle `x i` to their initial endowment `E.endowment i`. -/
theorem IsInCore.individuallyRational {E : ExchangeMarket I G} {x : I → G → ℝ}
    (hcore : E.IsInCore x) (i : I) :
    E.utility i (E.endowment i) ≤ E.utility i (x i) := by
  by_contra hlt
  push Not at hlt
  refine hcore.2 {i} E.endowment ⟨singleton_nonempty i, ?_, ?_, ?_, ⟨i, mem_singleton_self i, hlt⟩⟩
  · intro j hj g
    rw [mem_singleton.1 hj]
    exact E.endowment_nonneg i g
  · intro g
    simp
  · intro j hj
    rw [mem_singleton.1 hj]
    exact hlt.le

/-- **Competitive equilibria belong to the core** ([DebreuScarf1963]): in any locally nonsatiated
exchange economy (with no convexity hypothesis), no coalition can block a competitive equilibrium
allocation. -/
theorem IsCompetitiveEquilibrium.isInCore {E : ExchangeMarket I G} {x : I → G → ℝ} {p : G → ℝ}
    (heq : E.IsCompetitiveEquilibrium x p)
    (hlns : ∀ i, IsLocallyNonsatiated (E.utility i)) :
    E.IsInCore x := by
  refine ⟨heq.isFeasibleAllocation, fun S z hblock => ?_⟩
  obtain ⟨_, hz_nn, hz_endow, hz_le, ⟨i₀, hi₀S, hi₀_lt⟩⟩ := hblock
  have hdem : ∀ i, x i ∈ Market.demandSet (E.utility i) p (E.income p i) :=
    fun i => (E.mem_demandSet).1 (heq.2.1 i)
  have hall_le : ∀ i ∈ S, E.income p i ≤ expenditure p (z i) :=
    fun i hi => (hlns i).le_expenditure_of_mem_demandSet (hdem i) (hz_nn i hi) (hz_le i hi)
  have hstrict : E.income p i₀ < expenditure p (z i₀) :=
    lt_expenditure_of_mem_demandSet (hdem i₀) (hz_nn i₀ hi₀S) hi₀_lt
  have hsum_lt : ∑ i ∈ S, E.income p i < ∑ i ∈ S, expenditure p (z i) :=
    sum_lt_sum hall_le ⟨i₀, hi₀S, hstrict⟩
  have hsum_le : ∑ i ∈ S, expenditure p (z i) ≤ ∑ i ∈ S, E.income p i := by
    calc
      ∑ i ∈ S, expenditure p (z i) = ∑ g : G, p g * ∑ i ∈ S, z i g := by
        simp only [expenditure_eq_sum, mul_sum]
        exact sum_comm
      _ ≤ ∑ g : G, p g * ∑ i ∈ S, E.endowment i g :=
        sum_le_sum fun g _ => mul_le_mul_of_nonneg_left (hz_endow g) (heq.1 g)
      _ = ∑ i ∈ S, E.income p i := by
        simp only [income_eq, expenditure_eq_sum, mul_sum]
        exact sum_comm
  linarith

end Core

/-! ### `r`-fold replica economies and the equal-treatment theorem -/

section Replica

variable {I G : Type*} [Fintype I] [Fintype G]

/-- The **`r`-fold replica exchange economy** ([DebreuScarf1963]): replaces each trader `i : I` with
`r` identical traders `(i, c) : I × Fin r` having endowment `E.endowment i` and utility
`E.utility i`. -/
def replica (E : ExchangeMarket I G) (r : ℕ) : ExchangeMarket (I × Fin r) G where
  endowment ic := E.endowment ic.1
  utility ic := E.utility ic.1
  endowment_nonneg ic := E.endowment_nonneg ic.1

omit [Fintype I] [Fintype G] in
@[simp] theorem replica_endowment (E : ExchangeMarket I G) (r : ℕ) (ic : I × Fin r) :
    (E.replica r).endowment ic = E.endowment ic.1 := by rfl

omit [Fintype I] [Fintype G] in
@[simp] theorem replica_utility (E : ExchangeMarket I G) (r : ℕ) (ic : I × Fin r) :
    (E.replica r).utility ic = E.utility ic.1 := by rfl

omit [Fintype I] in
@[simp] theorem replica_income (E : ExchangeMarket I G) (r : ℕ) (p : G → ℝ) (ic : I × Fin r) :
    (E.replica r).income p ic = E.income p ic.1 := by
  rw [income_eq, replica_endowment, ← income_eq]

omit [Fintype G] in
theorem replica_totalSupply (E : ExchangeMarket I G) (r : ℕ) (g : G) :
    (E.replica r).totalSupply g = (r : ℝ) * E.totalSupply g := by
  simp only [totalSupply_eq_sum, replica_endowment, Fintype.sum_prod_type, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_sum]

omit [Fintype G] in
theorem replica_excessDemand (E : ExchangeMarket I G) (r : ℕ) (x : I → G → ℝ) (g : G) :
    (E.replica r).excessDemand (fun ic => x ic.1) g = (r : ℝ) * E.excessDemand x g := by
  simp only [excessDemand_eq, replica_totalSupply, Fintype.sum_prod_type, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_sub, mul_sum]

/-- Every competitive equilibrium `(x, p)` of `E` lifts to a symmetric competitive equilibrium of
`E.replica r` for every `r : ℕ`. -/
theorem IsCompetitiveEquilibrium.replica {E : ExchangeMarket I G} {x : I → G → ℝ} {p : G → ℝ}
    (heq : E.IsCompetitiveEquilibrium x p) (r : ℕ) :
    (E.replica r).IsCompetitiveEquilibrium (fun ic => x ic.1) p := by
  refine ⟨heq.1, fun ic => ?_, fun g => ?_, fun g => ?_⟩
  · rw [mem_demandSet, replica_utility, replica_income]
    exact (E.mem_demandSet).1 (heq.2.1 ic.1)
  · rw [E.replica_excessDemand r x g]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg r) (heq.2.2.1 g)
  · rw [E.replica_excessDemand r x g]
    calc
      p g * ((r : ℝ) * E.excessDemand x g) = (r : ℝ) * (p g * E.excessDemand x g) := by ring
      _ = 0 := by rw [heq.2.2.2 g, mul_zero]

/-- Consequently, in any locally nonsatiated exchange economy, the symmetric replication of every
competitive equilibrium allocation belongs to the core of `E.replica r` for all `r`. -/
theorem IsCompetitiveEquilibrium.replica_isInCore {E : ExchangeMarket I G} {x : I → G → ℝ}
    {p : G → ℝ} (heq : E.IsCompetitiveEquilibrium x p)
    (hlns : ∀ i, IsLocallyNonsatiated (E.utility i)) (r : ℕ) :
    (E.replica r).IsInCore (fun ic => x ic.1) :=
  (heq.replica r).isInCore fun ic => hlns ic.1

omit [Fintype G] in
/-- **Equal-treatment theorem in the core** ([DebreuScarf1963]): if every trader's utility function
is strictly concave on `ℝ_+^G` (`StrictConcaveOn`), then for any `r ≥ 1`, every allocation `y` in
the core of `E.replica r` assigns identical consumption bundles `y (i, c₁) = y (i, c₂)` to all
replicas of the same type `i`. -/
theorem eq_of_isInCore_replica {E : ExchangeMarket I G} {r : ℕ} [NeZero r]
    (hsc : ∀ i : I, StrictConcaveOn ℝ {b : G → ℝ | ∀ g, 0 ≤ b g} (E.utility i))
    {y : I × Fin r → G → ℝ} (hcore : (E.replica r).IsInCore y)
    (i : I) (c₁ c₂ : Fin r) :
    y (i, c₁) = y (i, c₂) := by
  classical
  by_contra hne
  have hr_pos : 0 < r := NeZero.pos r
  have hr_rpos : 0 < (r : ℝ) := Nat.cast_pos.2 hr_pos
  have : Nonempty (Fin r) := Fin.pos_iff_nonempty.1 hr_pos
  -- For each type `k : I`, pick a worst-off replica `cMin k : Fin r`.
  have hmin_ex : ∀ k : I, ∃ cm : Fin r, ∀ c : Fin r,
      E.utility k (y (k, cm)) ≤ E.utility k (y (k, c)) := by
    intro k
    obtain ⟨cm, -, hcm⟩ :=
      exists_min_image univ (fun c : Fin r => E.utility k (y (k, c))) univ_nonempty
    exact ⟨cm, fun c => hcm c (mem_univ c)⟩
  choose cMin hcMin using hmin_ex
  -- Form the underdog coalition `U = {(k, cMin k) | k : I}` and type-average allocation `avg`.
  let emb : I ↪ I × Fin r := ⟨fun k => (k, cMin k), fun _ _ h => (Prod.mk.inj h).1⟩
  have hemb : ∀ k : I, emb k = (k, cMin k) := fun _ => rfl
  let U : Finset (I × Fin r) := univ.map emb
  let avg : I → G → ℝ := fun k => ∑ c : Fin r, (1 / (r : ℝ)) • y (k, c)
  let z : I × Fin r → G → ℝ := fun ic => avg ic.1
  have hw_pos : ∀ _c ∈ (univ : Finset (Fin r)), (0 : ℝ) < 1 / (r : ℝ) :=
    fun _ _ => one_div_pos.2 hr_rpos
  have hw_sum : ∑ _c : Fin r, (1 / (r : ℝ)) = 1 := by
    simp [hr_rpos.ne']
  have havg_nn : ∀ (k : I) (g : G), 0 ≤ avg k g := fun k g => by
    simp only [avg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact sum_nonneg fun c _ => mul_nonneg (one_div_nonneg.2 hr_rpos.le) (hcore.1.1 (k, c) g)
  have hmin_le : ∀ k : I, E.utility k (y (k, cMin k)) ≤
      ∑ c : Fin r, (1 / (r : ℝ)) * E.utility k (y (k, c)) := fun k => by
    calc
      E.utility k (y (k, cMin k))
        = ∑ _c : Fin r, (1 / (r : ℝ)) * E.utility k (y (k, cMin k)) := by
          rw [← sum_mul, hw_sum, one_mul]
      _ ≤ ∑ c : Fin r, (1 / (r : ℝ)) * E.utility k (y (k, c)) :=
          sum_le_sum fun c _ =>
            mul_le_mul_of_nonneg_left (hcMin k c) (one_div_nonneg.2 hr_rpos.le)
  -- Show `U` blocks `y` via `z`.
  refine hcore.2 U z ⟨⟨emb i, mem_map.2 ⟨i, mem_univ i, rfl⟩⟩, ?_, ?_, ?_, ?_⟩
  · intro ic _ g
    exact havg_nn ic.1 g
  · intro g
    simp only [U, z, sum_map, hemb, replica_endowment]
    have hsum_avg : ∑ k : I, avg k g = (1 / (r : ℝ)) * ∑ ic : I × Fin r, y ic g := by
      simp only [avg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← mul_sum,
        Fintype.sum_prod_type]
    rw [hsum_avg, ← E.totalSupply_eq_sum]
    have hfeas := hcore.1.2 g
    rw [E.replica_totalSupply r g] at hfeas
    have := mul_le_mul_of_nonneg_left hfeas (one_div_nonneg.2 hr_rpos.le)
    rwa [← mul_assoc, one_div_mul_cancel hr_rpos.ne', one_mul] at this
  · intro ic hic
    obtain ⟨k, -, rfl⟩ := mem_map.1 hic
    simp only [emb, replica_utility, z]
    have hjensen : ∑ c : Fin r, (1 / (r : ℝ)) * E.utility k (y (k, c)) ≤ E.utility k (avg k) := by
      simpa only [smul_eq_mul] using
        (hsc k).concaveOn.le_map_sum (fun c hc => (hw_pos c hc).le) hw_sum
          (fun c _ => hcore.1.1 (k, c))
    exact (hmin_le k).trans hjensen
  · refine ⟨emb i, mem_map.2 ⟨i, mem_univ i, rfl⟩, ?_⟩
    simp only [emb, replica_utility, z]
    have hstrict : ∑ c : Fin r, (1 / (r : ℝ)) * E.utility i (y (i, c)) < E.utility i (avg i) :=
      StrictConcaveOn.sum_mul_lt_of_ne (hsc i) hw_pos hw_sum (fun c _ => hcore.1.1 (i, c))
        ⟨c₁, mem_univ c₁, c₂, mem_univ c₂, hne⟩
    exact lt_of_le_of_lt (hmin_le i) hstrict

end Replica

/-! ### Debreu–Scarf core shrinking and core equivalence theorem -/

section DebreuScarf

variable {I G : Type*} [Fintype I] [Fintype G]

/-- **Debreu–Scarf core shrinking theorem (price quasi-equilibrium form)** ([DebreuScarf1963]):
let `E` be a locally nonsatiated exchange economy (`[Nonempty I]`, `[Nonempty G]`) whose traders
have convex preferences (`HasConvexPreferences`). If an allocation `x : I → G → ℝ` belongs to the
core of `E.replica r` for **every** `r ≥ 1`, then there exists a nonzero nonnegative price vector
`p` supporting `(x, p)` as a price quasi-equilibrium of the **original** economy `E` (with no
transfers, satisfying `∀ i, expenditure p (x i) = E.income p i`). -/
theorem exists_priceQuasiEquilibrium_of_forall_replica_isInCore [Nonempty I] [Nonempty G]
    (E : ExchangeMarket I G)
    (hlns : ∀ i, IsLocallyNonsatiated (E.utility i))
    (hconv : ∀ i, HasConvexPreferences (E.utility i))
    {x : I → G → ℝ}
    (hcore : ∀ (r : ℕ) [NeZero r], (E.replica r).IsInCore (fun ic => x ic.1)) :
    ∃ p : G → ℝ, E.IsPriceQuasiEquilibrium x p ∧
      ∀ i : I, expenditure p (x i) = E.income p i := by
  classical
  have hfeas1 := (hcore 1).1
  have hx_feas : E.IsFeasibleAllocation x := by
    refine ⟨fun i g => hfeas1.1 (i, 0) g, fun g => ?_⟩
    have h := hfeas1.2 g
    rw [E.replica_totalSupply 1 g, Nat.cast_one, one_mul] at h
    simpa only [Fintype.sum_prod_type, Fin.sum_univ_one] using h
  -- Convex hull of strictly-preferred net trades with free disposal, represented directly via
  -- nonempty `S : Finset I` and convex weights `α`.
  let K : Set (G → ℝ) :=
    {z | ∃ (S : Finset I) (α : I → ℝ) (b : I → G → ℝ),
      S.Nonempty ∧ (∀ i ∈ S, 0 < α i) ∧ ∑ i ∈ S, α i = 1 ∧
      (∀ i ∈ S, ∀ g, 0 ≤ b i g) ∧
      (∀ i ∈ S, E.utility i (x i) < E.utility i (b i)) ∧
      ∀ g : G, ∑ i ∈ S, α i * (b i g - E.endowment i g) ≤ z g}
  have hK_conv : Convex ℝ K := by
    rintro z₁ ⟨S₁, α₁, b₁, hS₁, hα₁_pos, hα₁_sum, hb₁_nn, hb₁_gt, hz₁⟩
      z₂ ⟨S₂, α₂, b₂, hS₂, hα₂_pos, hα₂_sum, hb₂_nn, hb₂_gt, hz₂⟩ t₁ t₂ ht₁ ht₂ ht
    rcases eq_or_lt_of_le ht₁ with rfl | ht₁_pos
    · have ht₂1 : t₂ = 1 := by linarith
      subst ht₂1
      simpa using ⟨S₂, α₂, b₂, hS₂, hα₂_pos, hα₂_sum, hb₂_nn, hb₂_gt, hz₂⟩
    rcases eq_or_lt_of_le ht₂ with rfl | ht₂_pos
    · have ht₁1 : t₁ = 1 := by linarith
      subst ht₁1
      simpa using ⟨S₁, α₁, b₁, hS₁, hα₁_pos, hα₁_sum, hb₁_nn, hb₁_gt, hz₁⟩
    · let S : Finset I := S₁ ∪ S₂
      let w₁ : I → ℝ := fun i => if i ∈ S₁ then t₁ * α₁ i else 0
      let w₂ : I → ℝ := fun i => if i ∈ S₂ then t₂ * α₂ i else 0
      let α : I → ℝ := fun i => w₁ i + w₂ i
      have hα_pos : ∀ i ∈ S, 0 < α i := by
        intro i hi
        rcases mem_union.1 hi with hi₁ | hi₂
        · have hw₁_pos : 0 < w₁ i := by simp [w₁, hi₁, mul_pos ht₁_pos (hα₁_pos i hi₁)]
          have hw₂_nn : 0 ≤ w₂ i := by
            dsimp only [w₂]; split_ifs with hi₂'
            · exact mul_nonneg ht₂_pos.le (hα₂_pos i hi₂').le
            · exact le_rfl
          linarith
        · have hw₂_pos : 0 < w₂ i := by simp [w₂, hi₂, mul_pos ht₂_pos (hα₂_pos i hi₂)]
          have hw₁_nn : 0 ≤ w₁ i := by
            dsimp only [w₁]; split_ifs with hi₁'
            · exact mul_nonneg ht₁_pos.le (hα₁_pos i hi₁').le
            · exact le_rfl
          linarith
      have hsum_w₁ : ∑ i ∈ S, w₁ i = t₁ := by
        have : ∑ i ∈ S, w₁ i = ∑ i ∈ S₁, t₁ * α₁ i := by
          rw [← sum_subset subset_union_left]
          · exact sum_congr rfl fun i hi => by simp [w₁, hi]
          · intro i _ hi₁; simp [w₁, hi₁]
        rw [this, ← mul_sum, hα₁_sum, mul_one]
      have hsum_w₂ : ∑ i ∈ S, w₂ i = t₂ := by
        have : ∑ i ∈ S, w₂ i = ∑ i ∈ S₂, t₂ * α₂ i := by
          rw [← sum_subset subset_union_right]
          · exact sum_congr rfl fun i hi => by simp [w₂, hi]
          · intro i _ hi₂; simp [w₂, hi₂]
        rw [this, ← mul_sum, hα₂_sum, mul_one]
      have hα_sum : ∑ i ∈ S, α i = 1 := by
        simp only [α, sum_add_distrib, hsum_w₁, hsum_w₂, ht]
      let b : I → G → ℝ := fun i =>
        if i ∈ S₁ then
          if i ∈ S₂ then (w₁ i / α i) • b₁ i + (w₂ i / α i) • b₂ i
          else b₁ i
        else b₂ i
      have hb_props : ∀ i ∈ S, (∀ g, 0 ≤ b i g) ∧ E.utility i (x i) < E.utility i (b i) ∧
          ∀ g, α i * (b i g - E.endowment i g) =
            w₁ i * (b₁ i g - E.endowment i g) + w₂ i * (b₂ i g - E.endowment i g) := by
        intro i hi
        by_cases hi₁ : i ∈ S₁
        · by_cases hi₂ : i ∈ S₂
          · have hαi : 0 < α i := hα_pos i hi
            have hc₁_nn : 0 ≤ w₁ i / α i := by
              refine div_nonneg ?_ hαi.le
              simp only [w₁, hi₁, ↓reduceIte]
              exact mul_nonneg ht₁_pos.le (hα₁_pos i hi₁).le
            have hc₂_nn : 0 ≤ w₂ i / α i := by
              refine div_nonneg ?_ hαi.le
              simp only [w₂, hi₂, ↓reduceIte]
              exact mul_nonneg ht₂_pos.le (hα₂_pos i hi₂).le
            have hc_sum : w₁ i / α i + w₂ i / α i = 1 := by
              rw [← add_div]
              exact div_self hαi.ne'
            have hcomb := hconv i (hx_feas.1 i) ⟨hb₁_nn i hi₁, hb₁_gt i hi₁⟩
              ⟨hb₂_nn i hi₂, hb₂_gt i hi₂⟩ hc₁_nn hc₂_nn hc_sum
            have hbi_eq : b i = (w₁ i / α i) • b₁ i + (w₂ i / α i) • b₂ i := by simp [b, hi₁, hi₂]
            refine ⟨by rw [hbi_eq]; exact hcomb.1, by rw [hbi_eq]; exact hcomb.2, fun g => ?_⟩
            rw [hbi_eq]
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            have hα_def : α i = w₁ i + w₂ i := rfl
            field_simp [hαi.ne']
            rw [hα_def]
            ring
          · have hbi_eq : b i = b₁ i := by simp [b, hi₁, hi₂]
            have hw₂0 : w₂ i = 0 := by simp [w₂, hi₂]
            refine ⟨by rw [hbi_eq]; exact hb₁_nn i hi₁, by rw [hbi_eq]; exact hb₁_gt i hi₁,
              fun g => ?_⟩
            rw [hbi_eq]
            simp only [α, hw₂0, add_zero, zero_mul]
        · have hi₂ : i ∈ S₂ := (mem_union.1 hi).resolve_left hi₁
          have hbi_eq : b i = b₂ i := by simp [b, hi₁]
          have hw₁0 : w₁ i = 0 := by simp [w₁, hi₁]
          refine ⟨by rw [hbi_eq]; exact hb₂_nn i hi₂, by rw [hbi_eq]; exact hb₂_gt i hi₂,
            fun g => ?_⟩
          rw [hbi_eq]
          simp only [α, hw₁0, zero_add, zero_mul]
      refine ⟨S, α, b, hS₁.mono subset_union_left, hα_pos, hα_sum,
        fun i hi => (hb_props i hi).1, fun i hi => (hb_props i hi).2.1, fun g => ?_⟩
      have hsum_eq : ∑ i ∈ S, α i * (b i g - E.endowment i g) =
          t₁ * (∑ i ∈ S₁, α₁ i * (b₁ i g - E.endowment i g)) +
            t₂ * (∑ i ∈ S₂, α₂ i * (b₂ i g - E.endowment i g)) := by
        rw [sum_congr rfl fun i hi => (hb_props i hi).2.2 g, sum_add_distrib]
        congr 1
        · rw [← sum_subset subset_union_left]
          · rw [mul_sum]
            refine sum_congr rfl fun i hi => ?_
            simp only [w₁, hi, ↓reduceIte]
            ring
          · intro i _ hi₁; simp [w₁, hi₁]
        · rw [← sum_subset subset_union_right]
          · rw [mul_sum]
            refine sum_congr rfl fun i hi => ?_
            simp only [w₂, hi, ↓reduceIte]
            ring
          · intro i _ hi₂; simp [w₂, hi₂]
      rw [hsum_eq]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hz₁ g, hz₂ g]
  have hK_ne : K.Nonempty := by
    obtain ⟨i₀⟩ := ‹Nonempty I›
    obtain ⟨b₀, hb₀_nn, -, hb₀_gt⟩ := hlns i₀ (x i₀) (hx_feas.1 i₀) 1 zero_lt_one
    refine ⟨fun g => b₀ g - E.endowment i₀ g, {i₀}, fun _ => 1, fun _ => b₀,
      singleton_nonempty i₀, fun _ _ => zero_lt_one, by simp, fun _ _ => hb₀_nn,
      fun i hi => by rw [mem_singleton.1 hi]; exact hb₀_gt, fun g => by simp⟩
  -- Key Debreu–Scarf step: `K` is disjoint from `negOrthant G` by rounding `M * α i` up to `k i`!
  have hdisj : Disjoint (negOrthant G) K := by
    rw [Set.disjoint_left]
    rintro z hz_neg ⟨S, α, b, hS, hα_pos, _, hb_nn, hb_gt, hz_le⟩
    rw [mem_negOrthant] at hz_neg
    let D : G → ℝ := fun g => ∑ i ∈ S, α i * (b i g - E.endowment i g)
    have hD_neg : ∀ g : G, 0 < -D g := fun g => neg_pos.2 (lt_of_le_of_lt (hz_le g) (hz_neg g))
    obtain ⟨g₀, -, hg₀⟩ := exists_min_image univ (fun g : G => -D g) univ_nonempty
    set δ : ℝ := -D g₀
    have hδ_pos : 0 < δ := hD_neg g₀
    have hD_le : ∀ g : G, D g ≤ -δ := fun g => by
      have := hg₀ g (mem_univ g)
      linarith
    set B : ℝ := ∑ i ∈ S, ∑ g : G, |b i g - E.endowment i g|
    have hB_nn : 0 ≤ B := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
    set M : ℕ := Nat.floor ((B + 1) / δ) + 1
    have hM_gt : (B + 1) / δ < (M : ℝ) := by
      dsimp only [M]
      push_cast
      exact Nat.lt_floor_add_one _
    have hMδ_gt : B + 1 < (M : ℝ) * δ := (div_lt_iff₀ hδ_pos).1 hM_gt
    let k : I → ℕ := fun i => Nat.floor ((M : ℝ) * α i) + 1
    have hk_pos : ∀ i ∈ S, 0 < k i := fun _ _ => Nat.succ_pos _
    set r : ℕ := S.sup' hS k
    obtain ⟨i₀, hi₀S⟩ := hS
    have hr_pos : 0 < r := lt_of_lt_of_le (hk_pos i₀ hi₀S) (le_sup' k hi₀S)
    have : NeZero r := ⟨hr_pos.ne'⟩
    -- Build blocking coalition `C ⊆ I × Fin r` taking the first `k i` replicas of each `i ∈ S`.
    let slice : I → Finset (I × Fin r) := fun i =>
      (univ.filter (fun c : Fin r => c.val < k i)).map
        ⟨fun c => (i, c), fun _ _ h => (Prod.mk.inj h).2⟩
    let C : Finset (I × Fin r) := S.biUnion slice
    have hslice_disj : (S : Set I).PairwiseDisjoint slice := by
      intro i₁ _ i₂ _ hne
      change Disjoint (slice i₁) (slice i₂)
      rw [Finset.disjoint_left]
      intro ic hic₁ hic₂
      obtain ⟨c₁, -, rfl⟩ := mem_map.1 hic₁
      obtain ⟨c₂, -, heq⟩ := mem_map.1 hic₂
      exact hne (Prod.mk.inj heq).1.symm
    have hcard_slice : ∀ i ∈ S, (slice i).card = k i := by
      intro i hi
      have hki_le : k i ≤ r := le_sup' k hi
      simp only [slice, card_map]
      have hbij : (univ.filter (fun c : Fin r => c.val < k i)).card = (Finset.range (k i)).card :=
        Finset.card_bij (fun (c : Fin r) _ => c.val)
          (fun c hc => mem_range.2 (mem_filter.1 hc).2)
          (fun _ _ _ _ h => Fin.ext h)
          (fun m hm => ⟨⟨m, lt_of_lt_of_le (mem_range.1 hm) hki_le⟩,
            mem_filter.2 ⟨mem_univ _, mem_range.1 hm⟩, rfl⟩)
      rw [hbij, card_range]
    have hmem_C : ∀ {ic : I × Fin r}, ic ∈ C ↔ ic.1 ∈ S ∧ ic.2.val < k ic.1 := by
      intro ⟨i, c⟩
      simp only [C, mem_biUnion, slice, mem_map, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨j, hjS, c', hc', heq⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        exact ⟨hjS, hc'⟩
      · rintro ⟨hiS, hc⟩
        exact ⟨i, hiS, c, hc, rfl⟩
    have hc₀_lt : 0 < r := hr_pos
    have hic₀_mem : (i₀, (⟨0, hc₀_lt⟩ : Fin r)) ∈ C :=
      hmem_C.2 ⟨hi₀S, hk_pos i₀ hi₀S⟩
    refine (hcore r).2 C (fun ic => b ic.1) ⟨⟨_, hic₀_mem⟩, ?_, ?_, ?_, ?_⟩
    · intro ic hic g
      exact hb_nn ic.1 (hmem_C.1 hic).1 g
    · intro g
      have hsum_L : ∑ ic ∈ C, b ic.1 g = ∑ i ∈ S, (k i : ℝ) * b i g := by
        dsimp only [C]
        rw [Finset.sum_biUnion hslice_disj]
        refine sum_congr rfl fun i hi => ?_
        have hconst : ∀ ic ∈ slice i, b ic.1 g = b i g := by
          intro ic hic
          obtain ⟨c, -, rfl⟩ := mem_map.1 hic
          rfl
        rw [sum_congr rfl hconst, sum_const, hcard_slice i hi, nsmul_eq_mul]
      have hsum_R : ∑ ic ∈ C, (E.replica r).endowment ic g =
          ∑ i ∈ S, (k i : ℝ) * E.endowment i g := by
        dsimp only [C]
        rw [Finset.sum_biUnion hslice_disj]
        refine sum_congr rfl fun i hi => ?_
        have hconst : ∀ ic ∈ slice i, (E.replica r).endowment ic g = E.endowment i g := by
          intro ic hic
          obtain ⟨c, -, rfl⟩ := mem_map.1 hic
          rfl
        rw [sum_congr rfl hconst, sum_const, hcard_slice i hi, nsmul_eq_mul]
      rw [hsum_L, hsum_R]
      -- Bound `∑ i ∈ S, k i * (b i g - w i g) = M * D g + ∑ i ∈ S, (k i - M * α i) * (...) < 0`.
      suffices hneg_diff : ∑ i ∈ S, (k i : ℝ) * (b i g - E.endowment i g) ≤ 0 by
        simp only [mul_sub, sum_sub_distrib] at hneg_diff
        linarith
      have hsplit_k : ∑ i ∈ S, (k i : ℝ) * (b i g - E.endowment i g) =
          (M : ℝ) * D g + ∑ i ∈ S, ((k i : ℝ) - (M : ℝ) * α i) * (b i g - E.endowment i g) := by
        dsimp only [D]
        rw [mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun i _ => by ring
      have herr_le_B :
          ∑ i ∈ S, ((k i : ℝ) - (M : ℝ) * α i) * (b i g - E.endowment i g) ≤ B := by
        calc
          ∑ i ∈ S, ((k i : ℝ) - (M : ℝ) * α i) * (b i g - E.endowment i g)
            ≤ ∑ i ∈ S, 1 * |b i g - E.endowment i g| := by
              refine sum_le_sum fun i hi => ?_
              have hrem_nn : 0 ≤ (k i : ℝ) - (M : ℝ) * α i := by
                dsimp only [k]
                push_cast
                linarith [Nat.lt_floor_add_one ((M : ℝ) * α i)]
              have hrem_le_1 : (k i : ℝ) - (M : ℝ) * α i ≤ 1 := by
                dsimp only [k]
                push_cast
                have hfl : (Nat.floor ((M : ℝ) * α i) : ℝ) ≤ (M : ℝ) * α i :=
                  Nat.floor_le (mul_nonneg (Nat.cast_nonneg M) (hα_pos i hi).le)
                linarith
              calc
                ((k i : ℝ) - (M : ℝ) * α i) * (b i g - E.endowment i g)
                  ≤ ((k i : ℝ) - (M : ℝ) * α i) * |b i g - E.endowment i g| :=
                    mul_le_mul_of_nonneg_left (le_abs_self _) hrem_nn
                _ ≤ 1 * |b i g - E.endowment i g| :=
                    mul_le_mul_of_nonneg_right hrem_le_1 (abs_nonneg _)
          _ = ∑ i ∈ S, |b i g - E.endowment i g| := by simp
          _ ≤ B := by
              dsimp only [B]
              exact sum_le_sum fun i _ =>
                single_le_sum (fun l _ => abs_nonneg (b i l - E.endowment i l)) (mem_univ g)
      have hMD_le : (M : ℝ) * D g ≤ -(M : ℝ) * δ := by
        have := mul_le_mul_of_nonneg_left (hD_le g) (Nat.cast_nonneg M)
        linarith
      linarith
    · intro ic hic
      exact (hb_gt ic.1 (hmem_C.1 hic).1).le
    · exact ⟨_, hic₀_mem, hb_gt i₀ hi₀S⟩
  have hzero : ∀ ε : ℝ, 0 < ε → ∃ z ∈ K, ∀ g : G, |z g| < ε := fun ε hε => by
    obtain ⟨b, hb_nn, hb_gt, hb_le⟩ :=
      hx_feas.exists_forall_utility_lt_sum_sub_totalSupply_le hlns (half_pos hε)
    set m : ℝ := (Fintype.card I : ℝ)
    have hm_ge_1 : 1 ≤ m := Nat.one_le_cast.2 Fintype.card_pos
    have hm_pos : 0 < m := lt_of_lt_of_le zero_lt_one hm_ge_1
    let α : I → ℝ := fun _ => 1 / m
    refine ⟨fun g => max (∑ i : I, α i * (b i g - E.endowment i g)) 0,
      ⟨univ, α, b, univ_nonempty, fun _ _ => one_div_pos.2 hm_pos, by simp [α, m, hm_pos.ne'],
        fun i _ => hb_nn i, fun i _ => hb_gt i, fun g => le_max_left _ _⟩, fun g => ?_⟩
    have havg_le : ∑ i : I, α i * (b i g - E.endowment i g) ≤ ε / 2 := by
      have hrew : ∑ i : I, α i * (b i g - E.endowment i g) =
          (1 / m) * ((∑ i : I, b i g) - E.totalSupply g) := by
        rw [E.totalSupply_eq_sum, ← sum_sub_distrib, mul_sum]
      have h1m_le : 1 / m ≤ 1 := div_le_one_of_le₀ hm_ge_1 hm_pos.le
      have hmul : (1 / m) * ((∑ i : I, b i g) - E.totalSupply g) ≤ (1 / m) * (ε / 2) :=
        mul_le_mul_of_nonneg_left (hb_le g) (by positivity)
      nlinarith [hrew]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_lt (havg_le.trans_lt (half_lt_self hε)) hε
  obtain ⟨p, hp_nn, hp_pos, hsep⟩ :=
    exists_price_of_convex_disjoint_negOrthant hK_conv hK_ne hdisj hzero
  -- Singleton `S = {i}` gives `E.income p i ≤ expenditure p b` whenever `u_i(x_i) < u_i(b)`.
  have hsupp_i : ∀ (i : I) (b : G → ℝ), (∀ g, 0 ≤ b g) → E.utility i (x i) < E.utility i b →
      E.income p i ≤ expenditure p b := by
    intro i b hb_nn hub
    have hz_mem : (fun g => b g - E.endowment i g) ∈ K :=
      ⟨{i}, fun _ => 1, fun _ => b, singleton_nonempty i, fun _ _ => zero_lt_one, by simp,
        fun _ _ => hb_nn, fun j hj => by rw [mem_singleton.1 hj]; exact hub,
        fun g => by simp⟩
    have hge0 : 0 ≤ expenditure p (fun g => b g - E.endowment i g) := hsep _ hz_mem
    have hsub : expenditure p (fun g => b g - E.endowment i g) =
        expenditure p b - E.income p i := by
      rw [E.income_eq]
      exact expenditure_sub p b (E.endowment i)
    linarith
  -- Approaching `x i` via `hlns i` gives `E.income p i ≤ expenditure p (x i)` for every `i`.
  have hinc_le_exp : ∀ i : I, E.income p i ≤ expenditure p (x i) := fun i => by
    by_contra hlt
    obtain ⟨b, hb_nn, hub, hb_exp⟩ :=
      (hlns i).exists_lt_expenditure_lt hp_nn (hx_feas.1 i) (sub_pos.2 (not_le.1 hlt))
    linarith [hsupp_i i b hb_nn hub]
  -- Feasibility of `x` gives the reverse sum inequality, forcing equality for every trader!
  have hsum_le : ∑ i : I, expenditure p (x i) ≤ ∑ i : I, E.income p i := by
    rw [E.sum_income p]
    exact hx_feas.sum_expenditure_le_totalSupply hp_nn
  have hexp_eq_inc : ∀ i : I, expenditure p (x i) = E.income p i := by
    intro i
    by_contra hne
    have hlt : E.income p i < expenditure p (x i) := lt_of_le_of_ne (hinc_le_exp i) (Ne.symm hne)
    have : ∑ j : I, E.income p j < ∑ j : I, expenditure p (x j) :=
      sum_lt_sum (fun j _ => hinc_le_exp j) ⟨i, mem_univ i, hlt⟩
    linarith
  have hex0 : expenditure p (E.excessDemand x) = 0 := by
    rw [E.expenditure_excessDemand]
    exact sum_eq_zero fun i _ => by rw [hexp_eq_inc i, sub_self]
  have hcs : ∀ g : G, p g * E.excessDemand x g = 0 :=
    hx_feas.price_mul_excessDemand_eq_zero hp_nn hex0
  refine ⟨p, ⟨hp_nn, hp_pos, fun i => ⟨⟨hx_feas.1 i, (hexp_eq_inc i).le⟩, hsupp_i i⟩,
    fun g => by rw [E.excessDemand_eq]; exact sub_nonpos.2 (hx_feas.2 g), hcs⟩, hexp_eq_inc⟩

/-- **Debreu–Scarf core shrinking theorem (full competitive equilibrium)** ([DebreuScarf1963]):
under local nonsatiation, convex preferences, continuity on `ℝ_+^G`, and strictly positive initial
endowments (`∀ i g, 0 < E.endowment i g`), any allocation whose symmetric replication lies in the
core of `E.replica r` for all `r ≥ 1` is a competitive equilibrium allocation of `E`. -/
theorem exists_isCompetitiveEquilibrium_of_forall_replica_isInCore [Nonempty I] [Nonempty G]
    (E : ExchangeMarket I G)
    (hlns : ∀ i, IsLocallyNonsatiated (E.utility i))
    (hconv : ∀ i, HasConvexPreferences (E.utility i))
    (hcont : ∀ i, ContinuousOn (E.utility i) {b : G → ℝ | ∀ g, 0 ≤ b g})
    (hendow_pos : ∀ (i : I) (g : G), 0 < E.endowment i g)
    {x : I → G → ℝ}
    (hcore : ∀ (r : ℕ) [NeZero r], (E.replica r).IsInCore (fun ic => x ic.1)) :
    ∃ p : G → ℝ, (∃ g, 0 < p g) ∧ E.IsCompetitiveEquilibrium x p := by
  obtain ⟨p, hquasi, _⟩ :=
    E.exists_priceQuasiEquilibrium_of_forall_replica_isInCore hlns hconv hcore
  obtain ⟨g₀, hpg₀⟩ := hquasi.2.1
  refine ⟨p, ⟨g₀, hpg₀⟩, hquasi.isCompetitiveEquilibrium_of_income_pos hcont fun i => ?_⟩
  rw [income_eq, expenditure_eq_sum]
  exact lt_of_lt_of_le (mul_pos hpg₀ (hendow_pos i g₀))
    (single_le_sum (fun g _ => mul_nonneg (hquasi.1 g) (E.endowment_nonneg i g)) (mem_univ g₀))

/-- **Debreu–Scarf core equivalence theorem** ([DebreuScarf1963]): in a locally nonsatiated
exchange economy (`[Nonempty I]`, `[Nonempty G]`) with continuous utilities, convex preferences,
and strictly positive initial endowments, an allocation `x` is a competitive equilibrium allocation
if and only if its symmetric replication belongs to the core of `E.replica r` for every `r ≥ 1`. -/
theorem exists_isCompetitiveEquilibrium_iff_forall_replica_isInCore [Nonempty I] [Nonempty G]
    (E : ExchangeMarket I G)
    (hlns : ∀ i, IsLocallyNonsatiated (E.utility i))
    (hconv : ∀ i, HasConvexPreferences (E.utility i))
    (hcont : ∀ i, ContinuousOn (E.utility i) {b : G → ℝ | ∀ g, 0 ≤ b g})
    (hendow_pos : ∀ (i : I) (g : G), 0 < E.endowment i g)
    (x : I → G → ℝ) :
    (∃ p : G → ℝ, E.IsCompetitiveEquilibrium x p) ↔
      ∀ (r : ℕ) [NeZero r], (E.replica r).IsInCore (fun ic => x ic.1) := by
  refine ⟨fun ⟨p, heq⟩ r _ => heq.replica_isInCore hlns r, fun hcore => ?_⟩
  obtain ⟨p, -, heq⟩ :=
    E.exists_isCompetitiveEquilibrium_of_forall_replica_isInCore hlns hconv hcont hendow_pos hcore
  exact ⟨p, heq⟩

end DebreuScarf

end ExchangeMarket

end Cslib.GameTheory.Market
