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
    (hcore : E.IsInCore x) : E.IsParetoOptimal x :=
  ⟨hcore.1, fun ⟨y, hy_feas, hy_le, ⟨i₀, hi₀⟩⟩ =>
    hcore.2 univ y ⟨univ_nonempty, fun i _ => hy_feas.1 i,
      fun g => by simpa only [← E.totalSupply_eq_sum] using hy_feas.2 g,
      fun i _ => hy_le i, ⟨i₀, mem_univ i₀, hi₀⟩⟩⟩

omit [Fintype G] in
/-- Blocking by singleton coalitions `{i}` ensures **individual rationality**: every trader weakly
prefers their core bundle `x i` to their initial endowment `E.endowment i`. -/
theorem IsInCore.individuallyRational {E : ExchangeMarket I G} {x : I → G → ℝ}
    (hcore : E.IsInCore x) (i : I) :
    E.utility i (E.endowment i) ≤ E.utility i (x i) := by
  by_contra! hlt
  exact hcore.2 {i} E.endowment ⟨singleton_nonempty i,
    fun j hj g => mem_singleton.1 hj ▸ E.endowment_nonneg i g, fun _ => le_rfl,
    fun j hj => mem_singleton.1 hj ▸ hlt.le, ⟨i, mem_singleton_self i, hlt⟩⟩

/-- **Competitive equilibria belong to the core** ([DebreuScarf1963]): in any locally nonsatiated
exchange economy (with no convexity hypothesis), no coalition can block a competitive equilibrium
allocation. -/
theorem IsCompetitiveEquilibrium.isInCore {E : ExchangeMarket I G} {x : I → G → ℝ} {p : G → ℝ}
    (heq : E.IsCompetitiveEquilibrium x p)
    (hlns : ∀ i, IsLocallyNonsatiated (E.utility i)) :
    E.IsInCore x := by
  refine ⟨heq.isFeasibleAllocation, fun S z hblock => ?_⟩
  obtain ⟨_, hz_nn, hz_endow, hz_le, ⟨i₀, hi₀S, hi₀_lt⟩⟩ := hblock
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
  exact not_exists_paretoImprovementOn (X := fun _ => {b | ∀ g, 0 ≤ b g})
    (fun i _ => mem_demandSetOn.2 <| by
      obtain ⟨hx, hmax⟩ := Market.mem_demandSet.1 ((E.mem_demandSet).1 (heq.2.1 i))
      exact ⟨⟨hx.1, hx.2⟩, fun b' ⟨hb'1, hb'2⟩ => hmax b' ⟨hb'1, hb'2⟩⟩)
    (fun i _ => hlns i) (fun i hi => hz_nn i hi) hsum_le ⟨hz_le, i₀, hi₀S, hi₀_lt⟩

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
  refine ⟨heq.1, fun ic => (mem_demandSet ..).2 ((replica_income E r p ic).symm ▸
      (E.mem_demandSet).1 (heq.2.1 ic.1)),
    fun g => E.replica_excessDemand r x g ▸
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg r) (heq.2.2.1 g), fun g => ?_⟩
  rw [E.replica_excessDemand r x g]
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
  choose cMin hcMin using fun k : I =>
    Finite.exists_min (fun c : Fin r => E.utility k (y (k, c)))
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
    simp only [z, avg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact sum_nonneg fun c _ => mul_nonneg (one_div_nonneg.2 hr_rpos.le) (hcore.1.1 (ic.1, c) g)
  · intro g
    simp only [U, z, avg, sum_map, hemb, replica_endowment, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, ← mul_sum]
    rw [one_div_mul_eq_div, div_le_iff₀' hr_rpos, ← E.totalSupply_eq_sum, ← E.replica_totalSupply]
    simpa only [Fintype.sum_prod_type] using hcore.1.2 g
  · intro ic hic
    obtain ⟨k, -, rfl⟩ := mem_map.1 hic
    exact (hmin_le k).trans (by
      simpa only [hemb, replica_utility, z, smul_eq_mul] using
        (hsc k).concaveOn.le_map_sum (fun c hc => (hw_pos c hc).le)
          hw_sum fun c _ => hcore.1.1 (k, c))
  · exact ⟨emb i, mem_map.2 ⟨i, mem_univ i, rfl⟩, (hmin_le i).trans_lt
      (StrictConcaveOn.sum_mul_lt_of_ne (hsc i) hw_pos hw_sum
        (fun c _ => hcore.1.1 (i, c)) ⟨c₁, mem_univ c₁, c₂, mem_univ c₂, hne⟩)⟩

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
  have hx_feas : E.IsFeasibleAllocation x :=
    ⟨fun i g => hfeas1.1 (i, 0) g, fun g => by
      simpa only [E.replica_totalSupply 1 g, Nat.cast_one, one_mul, Fintype.sum_prod_type,
        Fin.sum_univ_one] using hfeas1.2 g⟩
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
    · obtain rfl : t₂ = 1 := by linarith
      simpa using ⟨S₂, α₂, b₂, hS₂, hα₂_pos, hα₂_sum, hb₂_nn, hb₂_gt, hz₂⟩
    rcases eq_or_lt_of_le ht₂ with rfl | ht₂_pos
    · obtain rfl : t₁ = 1 := by linarith
      simpa using ⟨S₁, α₁, b₁, hS₁, hα₁_pos, hα₁_sum, hb₁_nn, hb₁_gt, hz₁⟩
    · let S : Finset I := S₁ ∪ S₂
      let w₁ : I → ℝ := fun i => if i ∈ S₁ then t₁ * α₁ i else 0
      let w₂ : I → ℝ := fun i => if i ∈ S₂ then t₂ * α₂ i else 0
      let α : I → ℝ := fun i => w₁ i + w₂ i
      have hw_nn {S' : Finset I} {t : ℝ} {α' : I → ℝ} (ht' : 0 ≤ t) (hα' : ∀ i ∈ S', 0 < α' i)
          (i : I) : 0 ≤ if i ∈ S' then t * α' i else 0 := by
        split_ifs with h
        exacts [mul_nonneg ht' (hα' i h).le, le_rfl]
      have hα_pos : ∀ i ∈ S, 0 < α i := fun i hi => by
        rcases mem_union.1 hi with hi₁ | hi₂
        · exact add_pos_of_pos_of_nonneg
            (lt_of_lt_of_eq (mul_pos ht₁_pos (hα₁_pos i hi₁)) (ite_eq_left hi₁).symm)
            (hw_nn ht₂_pos.le hα₂_pos i)
        · exact add_pos_of_nonneg_of_pos (hw_nn ht₁_pos.le hα₁_pos i)
            (lt_of_lt_of_eq (mul_pos ht₂_pos (hα₂_pos i hi₂)) (ite_eq_left hi₂).symm)
      have hsum_w₁ : ∑ i ∈ S, w₁ i = t₁ := by
        rw [sum_ite_mem, inter_eq_right.2 subset_union_left, ← mul_sum, hα₁_sum, mul_one]
      have hsum_w₂ : ∑ i ∈ S, w₂ i = t₂ := by
        rw [sum_ite_mem, inter_eq_right.2 subset_union_right, ← mul_sum, hα₂_sum, mul_one]
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
            obtain ⟨h1, h2⟩ := hconv i (hx_feas.1 i) ⟨hb₁_nn i hi₁, hb₁_gt i hi₁⟩
              ⟨hb₂_nn i hi₂, hb₂_gt i hi₂⟩ (div_nonneg (hw_nn ht₁_pos.le hα₁_pos i) hαi.le)
              (div_nonneg (hw_nn ht₂_pos.le hα₂_pos i) hαi.le)
              (by rw [← add_div, div_self hαi.ne'])
            simp only [b, hi₁, hi₂, ↓reduceIte]
            refine ⟨h1, h2, fun g => ?_⟩
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            field_simp [hαi.ne']
            dsimp only [α]
            ring
          · simp only [b, w₂, α, hi₁, hi₂, ↓reduceIte, add_zero, zero_mul]
            exact ⟨hb₁_nn i hi₁, hb₁_gt i hi₁, fun _ => trivial⟩
        · have hi₂ : i ∈ S₂ := (mem_union.1 hi).resolve_left hi₁
          simp only [b, w₁, α, hi₁, ↓reduceIte, zero_add, zero_mul]
          exact ⟨hb₂_nn i hi₂, hb₂_gt i hi₂, fun _ => trivial⟩
      refine ⟨S, α, b, hS₁.mono subset_union_left, hα_pos, hα_sum,
        fun i hi => (hb_props i hi).1, fun i hi => (hb_props i hi).2.1, fun g => ?_⟩
      have hsum_eq : ∑ i ∈ S, α i * (b i g - E.endowment i g) =
          t₁ * (∑ i ∈ S₁, α₁ i * (b₁ i g - E.endowment i g)) +
            t₂ * (∑ i ∈ S₂, α₂ i * (b₂ i g - E.endowment i g)) := by
        rw [sum_congr rfl fun i hi => (hb_props i hi).2.2 g, sum_add_distrib]
        simp only [w₁, w₂, ite_mul, zero_mul]
        rw [sum_ite_mem, sum_ite_mem, inter_eq_right.2 subset_union_left,
          inter_eq_right.2 subset_union_right, mul_sum, mul_sum]
        congr 1 <;> exact sum_congr rfl fun i _ => by ring
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
    obtain ⟨g₀, hg₀⟩ := Finite.exists_min (fun g : G => -D g)
    set δ : ℝ := -D g₀
    have hδ_pos : 0 < δ := hD_neg g₀
    have hD_le : ∀ g : G, D g ≤ -δ := fun g => by linarith [hg₀ g]
    set B : ℝ := ∑ i ∈ S, ∑ g : G, |b i g - E.endowment i g|
    set M : ℕ := Nat.floor ((B + 1) / δ) + 1
    have hMδ_gt : B + 1 < (M : ℝ) * δ :=
      (div_lt_iff₀ hδ_pos).1 (by exact_mod_cast Nat.lt_floor_add_one ((B + 1) / δ))
    let k : I → ℕ := fun i => Nat.floor ((M : ℝ) * α i) + 1
    have hk_pos : ∀ i ∈ S, 0 < k i := fun _ _ => Nat.succ_pos _
    set r : ℕ := S.sup' hS k
    obtain ⟨i₀, hi₀S⟩ := hS
    have hr_pos : 0 < r := lt_of_lt_of_le (hk_pos i₀ hi₀S) (le_sup' k hi₀S)
    have : NeZero r := ⟨hr_pos.ne'⟩
    -- Build blocking coalition `C ⊆ I × Fin r` taking the first `k i` replicas of each `i ∈ S`.
    let slice : I → Finset (I × Fin r) := fun i =>
      (univ.filter (fun c : Fin r => c.val < k i)).map ⟨fun c => (i, c), Prod.mk_right_injective i⟩
    let C : Finset (I × Fin r) := S.biUnion slice
    have hslice_disj : (S : Set I).PairwiseDisjoint slice := fun i₁ _ i₂ _ hne =>
      Finset.disjoint_left.2 fun _ hic₁ hic₂ => by
        obtain ⟨_, -, rfl⟩ := mem_map.1 hic₁
        obtain ⟨_, -, heq⟩ := mem_map.1 hic₂
        exact hne (Prod.mk.inj heq).1.symm
    have hcard_slice : ∀ i ∈ S, (slice i).card = k i := by
      intro i hi
      have hki_le : k i ≤ r := le_sup' k hi
      simp only [slice, card_map]
      exact (Finset.card_bij (fun (c : Fin r) _ => c.val)
        (fun c hc => mem_range.2 (mem_filter.1 hc).2)
        (fun _ _ _ _ h => Fin.ext h)
        (fun m hm => ⟨⟨m, lt_of_lt_of_le (mem_range.1 hm) hki_le⟩,
          mem_filter.2 ⟨mem_univ _, mem_range.1 hm⟩, rfl⟩)).trans (card_range _)
    have hmem_C : ∀ {ic : I × Fin r}, ic ∈ C ↔ ic.1 ∈ S ∧ ic.2.val < k ic.1 := by
      intro ⟨i, c⟩
      simp [C, slice]
    have hic₀_mem : (i₀, (⟨0, hr_pos⟩ : Fin r)) ∈ C :=
      hmem_C.2 ⟨hi₀S, hk_pos i₀ hi₀S⟩
    refine (hcore r).2 C (fun ic => b ic.1)
      ⟨⟨_, hic₀_mem⟩, fun ic hic g => hb_nn ic.1 (hmem_C.1 hic).1 g, ?_,
        fun ic hic => (hb_gt ic.1 (hmem_C.1 hic).1).le, _, hic₀_mem, hb_gt i₀ hi₀S⟩
    · intro g
      have hsum_C (f : I → ℝ) : ∑ ic ∈ C, f ic.1 = ∑ i ∈ S, (k i : ℝ) * f i := by
        rw [Finset.sum_biUnion hslice_disj]
        refine sum_congr rfl fun i hi => ?_
        rw [← hcard_slice i hi, ← nsmul_eq_mul, ← sum_const]
        simp [slice]
      simp only [replica_endowment]
      rw [hsum_C (fun i => b i g), hsum_C (fun i => E.endowment i g)]
      -- Bound `∑ i ∈ S, k i * (b i g - w i g) = M * D g + ∑ i ∈ S, (k i - M * α i) * (...) < 0`.
      suffices hneg_diff : ∑ i ∈ S, (k i : ℝ) * (b i g - E.endowment i g) ≤ 0 by
        simp only [mul_sub, sum_sub_distrib] at hneg_diff; linarith
      have hsplit_k : ∑ i ∈ S, (k i : ℝ) * (b i g - E.endowment i g) =
          (M : ℝ) * D g + ∑ i ∈ S, ((k i : ℝ) - (M : ℝ) * α i) * (b i g - E.endowment i g) := by
        dsimp only [D]
        rw [mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun i _ => by ring
      have herr_le_B :
          ∑ i ∈ S, ((k i : ℝ) - (M : ℝ) * α i) * (b i g - E.endowment i g) ≤ B :=
        calc ∑ i ∈ S, ((k i : ℝ) - (M : ℝ) * α i) * (b i g - E.endowment i g)
            ≤ ∑ i ∈ S, |b i g - E.endowment i g| := sum_le_sum fun i hi => by
              have hk_cast : (k i : ℝ) = ↑⌊(M : ℝ) * α i⌋₊ + 1 := by simp [k]
              have hrem_nn : 0 ≤ (k i : ℝ) - (M : ℝ) * α i := by
                linarith [hk_cast, Nat.lt_floor_add_one ((M : ℝ) * α i)]
              have hrem_le_1 : (k i : ℝ) - (M : ℝ) * α i ≤ 1 := by
                linarith [hk_cast, Nat.floor_le (mul_nonneg (Nat.cast_nonneg M) (hα_pos i hi).le)]
              calc ((k i : ℝ) - (M : ℝ) * α i) * (b i g - E.endowment i g)
                  ≤ ((k i : ℝ) - (M : ℝ) * α i) * |b i g - E.endowment i g| :=
                    mul_le_mul_of_nonneg_left (le_abs_self _) hrem_nn
                _ ≤ |b i g - E.endowment i g| :=
                    mul_le_of_le_one_left (abs_nonneg _) hrem_le_1
          _ ≤ B := sum_le_sum fun i _ =>
              single_le_sum (fun l _ => abs_nonneg (b i l - E.endowment i l)) (mem_univ g)
      linarith [mul_le_mul_of_nonneg_left (hD_le g) (Nat.cast_nonneg M)]
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
      simp only [α, ← mul_sum, sum_sub_distrib, ← E.totalSupply_eq_sum]
      exact (mul_le_mul_of_nonneg_left (hb_le g) (one_div_nonneg.2 hm_pos.le)).trans
        (mul_le_of_le_one_left (half_pos hε).le (div_le_one_of_le₀ hm_ge_1 hm_pos.le))
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_lt (havg_le.trans_lt (half_lt_self hε)) hε
  obtain ⟨p, hp_nn, hp_pos, hsep⟩ :=
    exists_price_of_convex_disjoint_negOrthant hK_conv hK_ne hdisj hzero
  -- Singleton `S = {i}` gives `E.income p i ≤ expenditure p b` whenever `u_i(x_i) < u_i(b)`.
  have hsupp_i : ∀ (i : I) (b : G → ℝ), (∀ g, 0 ≤ b g) → E.utility i (x i) < E.utility i b →
      E.income p i ≤ expenditure p b := fun i b hb_nn hub => by
    have hge0 := hsep (b - E.endowment i)
      ⟨{i}, fun _ => 1, fun _ => b, singleton_nonempty i, fun _ _ => zero_lt_one, by simp,
        fun _ _ => hb_nn, fun j hj => mem_singleton.1 hj ▸ hub, fun _ => by simp⟩
    rw [expenditure_sub, ← E.income_eq] at hge0; linarith
  -- Approaching `x i` via `hlns i` gives `E.income p i ≤ expenditure p (x i)` for every `i`.
  have hinc_le_exp : ∀ i : I, E.income p i ≤ expenditure p (x i) := fun i => by
    by_contra hlt
    obtain ⟨b, hb_nn, hub, hb_exp⟩ :=
      (hlns i).exists_lt_expenditure_lt hp_nn (hx_feas.1 i) (sub_pos.2 (not_le.1 hlt))
    linarith [hsupp_i i b hb_nn hub]
  -- Feasibility of `x` gives the reverse sum inequality, forcing equality for every trader!
  have hsum_le : ∑ i : I, expenditure p (x i) ≤ ∑ i : I, E.income p i :=
    E.sum_income p ▸ hx_feas.sum_expenditure_le_totalSupply hp_nn
  have hexp_eq_inc : ∀ i : I, expenditure p (x i) = E.income p i := fun i =>
    ((sum_eq_sum_iff_of_le fun j _ => hinc_le_exp j).1
      (le_antisymm (sum_le_sum fun j _ => hinc_le_exp j) hsum_le) i (mem_univ i)).symm
  have hex0 : expenditure p (E.excessDemand x) = 0 :=
    (E.expenditure_excessDemand p x).trans (sum_eq_zero fun i _ => sub_eq_zero.2 (hexp_eq_inc i))
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
