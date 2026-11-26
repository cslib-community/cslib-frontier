/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.Digraph.Layered
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import CslibFrontier.Foundations.MeasureTheory.Integral.PiUpdate
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Probabilistic Threshold and Cascade Models of Network Influence

This module formalizes the general threshold and probabilistic cascade models of social contagion
on finite directed graphs from [Kleinberg2007], Section 24.3 (pp. 618–622), due to
[KempeKleinbergTardos2003] and [KempeKleinbergTardos2005]:

1. **General Threshold Model** (`GeneralThresholdModel G`, pp. 619–620): each vertex `v` carries a
   monotone `[0, 1]`-valued threshold function `thresholdFn v : Finset V → ℝ` (`g_v(∅) = 0`)
   depending only on its active in-neighbors `inNeighbors G v`, draws an independent uniform
   threshold `θ v ∈ [0, 1]`, and activates once `θ v ≤ g_v(A)`.
2. **Linear Threshold Model** (`LinearThresholdModel G`, p. 619): specialization with nonnegative
   incoming edge weights `weight u v` summing to at most `1` at each vertex
   (`toGeneralThresholdModel`).
3. **Order-Independent Cascade Model** (`CascadeModel G`, pp. 620–621): active vertices attempt to
   activate inactive out-neighbors sequentially with incremental success probability `prob v u X`,
   whose sequential survival probability is invariant under reordering of attempts, together with
   the diminishing-returns predicate (`HasDiminishingReturns`) and the **Independent Cascade Model**
   (`IndependentCascadeModel G`, p. 621).
4. **Equivalence of General Threshold and Cascade Models** ([KempeKleinbergTardos2005];
   [Kleinberg2007], Section 24.3, pp. 620–621): explicit forward and backward translations
   `GeneralThresholdModel.toCascadeModel` and `CascadeModel.toGeneralThresholdModel` produce
   identical distributions over final active sets
   (`CascadeModel.activeSetProb_eq_toGeneralThresholdModel`,
   `GeneralThresholdModel.activeSetProb_toCascadeModel`) and identical expected influence under
   every valid edge-attempt schedule.
5. **Time-layered DAG reduction** ([KempeKleinbergTardos2003]; [Kleinberg2007], Section 24.3,
   pp. 621–622): `T` steps of a synchronous nonprogressive threshold process on `G` coincide slice
   by slice with the progressive threshold process on the layered digraph `timeLayeredDigraph G T`
   over `V × Fin (T + 1)` (`mem_thresholdFinal_toTimeLayered_iff`).

## Main definitions

* `Cslib.GameTheory.Network.inNeighbors`: finite set of incoming neighbors `{u | G.Adj u v}`.
* `Cslib.GameTheory.Network.GeneralThresholdModel`: monotone local threshold model on `Digraph V`,
  with `thresholdStep`, `thresholdFinal`, `thresholdMeasure`, `activeSetProb`, and `influence`.
* `Cslib.GameTheory.Network.LinearThresholdModel`: weighted linear threshold model and embedding
  `LinearThresholdModel.toGeneralThresholdModel`.
* `Cslib.GameTheory.Network.CascadeModel`: order-independent incremental cascade model, survival
  product `survivalProb`, `HasDiminishingReturns`, `ValidNextEdge`, `activeSetProb`, and
  `influence`.
* `Cslib.GameTheory.Network.IndependentCascadeModel`: edge-independent cascade model and embedding
  `IndependentCascadeModel.toCascadeModel`.
* `Cslib.GameTheory.Network.GeneralThresholdModel.toCascadeModel`,
  `Cslib.GameTheory.Network.CascadeModel.toGeneralThresholdModel`: bidirectional model translations.
* `Cslib.GameTheory.Network.timeLayeredDigraph`,
  `Cslib.GameTheory.Network.GeneralThresholdModel.toTimeLayered`,
  `Cslib.GameTheory.Network.GeneralThresholdModel.nonprogActive`: `T`-step time-layered DAG
  reduction.

## Main results

* `Cslib.GameTheory.Network.GeneralThresholdModel.thresholdFinal_subset_of_lt`: `thresholdFinal` is
  the least post-fixed point containing the initial seed set.
* `Cslib.GameTheory.Network.GeneralThresholdModel.toGeneralThresholdModel_toCascadeModel`:
  translating a general threshold model to a cascade model and back recovers the original model.
* `Cslib.GameTheory.Network.CascadeModel.activeSetProb_eq_toGeneralThresholdModel`,
  `Cslib.GameTheory.Network.GeneralThresholdModel.activeSetProb_toCascadeModel`: operational
  cascade dynamics under any valid schedule and uniform random thresholds induce the exact same
  final active-set distribution and expected influence.
* `Cslib.GameTheory.Network.GeneralThresholdModel.mem_thresholdFinal_toTimeLayered_iff`: exact
  slice correspondence between `T`-step nonprogressive dynamics on `G` and progressive dynamics on
  `timeLayeredDigraph G T`.

## References

* [KempeKleinbergTardos2003]
* [KempeKleinbergTardos2005]
* [Kleinberg2007]
-/

public section

open MeasureTheory Set

namespace Cslib.GameTheory.Network

/-! ## Directed in-neighborhoods -/

/-- Incoming neighbors `{u | G.Adj u v}` of vertex `v` in `G : Digraph V`, matching the neighbor
convention of [Kleinberg2007], Section 24.3, p. 619, Footnote 1. -/
def inNeighbors {V : Type*} [Fintype V] (G : Digraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  Finset.univ.filter (G.Adj · v)

@[simp]
theorem mem_inNeighbors {V : Type*} [Fintype V] {G : Digraph V} [DecidableRel G.Adj]
    {u v : V} : u ∈ inNeighbors G v ↔ G.Adj u v := by
  simp [inNeighbors]

/-! ## General and Linear Threshold Models -/

/-- **General Threshold Model** on a finite directed graph `G : Digraph V`
([Kleinberg2007], Section 24.3, pp. 619–620): each vertex `v` has a monotone `[0, 1]`-valued
threshold function `thresholdFn v` (`g_v(∅) = 0`) determined by its active incoming neighbors
`inNeighbors G v`. -/
@[ext]
structure GeneralThresholdModel {V : Type*} [DecidableEq V] [Fintype V]
    (G : Digraph V) [DecidableRel G.Adj] where
  /-- Local threshold function `g_v(X)` for cumulative influence of active set `X` on `v`. -/
  thresholdFn : V → Finset V → ℝ
  /-- Empty active set exerts zero influence (`g_v(∅) = 0`, [Kleinberg2007], Section 24.4,
  p. 623). -/
  thresholdFn_empty : ∀ v, thresholdFn v ∅ = 0
  /-- Local threshold values are at most `1`. -/
  thresholdFn_le_one : ∀ v X, thresholdFn v X ≤ 1
  /-- Adding active vertices never decreases `g_v(X)`. -/
  monotone : ∀ v, Monotone (thresholdFn v)
  /-- `g_v(X)` depends only on active incoming neighbors `X ∩ inNeighbors G v`. -/
  inNeighbors_congr : ∀ v X, thresholdFn v (X ∩ inNeighbors G v) = thresholdFn v X

/-- **Linear Threshold Model** on `G : Digraph V` ([Kleinberg2007], Section 24.3, p. 619): each
directed edge `(u, v)` carries weight `weight u v ≥ 0` with incoming sum at most `1` at every
vertex `v`. -/
structure LinearThresholdModel {V : Type*} [Fintype V]
    (G : Digraph V) [DecidableRel G.Adj] where
  /-- Nonnegative influence weight `b_{vu} = weight u v` exerted by `u` on `v`. -/
  weight : V → V → ℝ
  /-- Edge weights are nonnegative. -/
  weight_nonneg : ∀ u v, 0 ≤ weight u v
  /-- Weights vanish on non-edges of `G`. -/
  weight_eq_zero_of_not_adj : ∀ u v, ¬ G.Adj u v → weight u v = 0
  /-- Incoming weights into each vertex sum to at most `1`. -/
  sum_inNeighbors_le_one : ∀ v, ∑ u ∈ inNeighbors G v, weight u v ≤ 1

/-- Embed a `LinearThresholdModel` as a `GeneralThresholdModel` via additive neighbor sums
`g_v(X) = ∑ u ∈ X ∩ N(v), weight u v` ([Kleinberg2007], Section 24.3, pp. 619–620). -/
def LinearThresholdModel.toGeneralThresholdModel {V : Type*} [DecidableEq V] [Fintype V]
    {G : Digraph V} [DecidableRel G.Adj] (L : LinearThresholdModel G) :
    GeneralThresholdModel G where
  thresholdFn v X := ∑ u ∈ X ∩ inNeighbors G v, L.weight u v
  thresholdFn_empty v := by simp
  thresholdFn_le_one v X :=
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      fun u _ _ => L.weight_nonneg u v).trans (L.sum_inNeighbors_le_one v)
  monotone v A B hAB :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_inter_right hAB)
      fun u _ _ => L.weight_nonneg u v
  inNeighbors_congr v X := by
    rw [Finset.inter_assoc, Finset.inter_self]

@[simp]
theorem LinearThresholdModel.toGeneralThresholdModel_thresholdFn {V : Type*} [DecidableEq V]
    [Fintype V] {G : Digraph V} [DecidableRel G.Adj] (L : LinearThresholdModel G)
    (v : V) (X : Finset V) :
    L.toGeneralThresholdModel.thresholdFn v X = ∑ u ∈ X, L.weight u v := by
  change ∑ u ∈ X ∩ inNeighbors G v, L.weight u v = ∑ u ∈ X, L.weight u v
  refine Finset.sum_subset Finset.inter_subset_left fun u huX hnot => ?_
  have hadj : ¬ G.Adj u v := fun h => hnot (Finset.mem_inter.mpr ⟨huX, mem_inNeighbors.mpr h⟩)
  exact L.weight_eq_zero_of_not_adj u v hadj

/-! ## Uniform `[0, 1]` product measure -/

/-- Uniform probability measure on `[0, 1] ⊆ ℝ`. -/
noncomputable def unitMeasure : Measure ℝ :=
  volume.restrict (Icc (0 : ℝ) 1)

theorem unitMeasure_def : unitMeasure = volume.restrict (Icc (0 : ℝ) 1) := by
  rfl

instance instIsProbabilityMeasureUnitMeasure : IsProbabilityMeasure unitMeasure :=
  ⟨by rw [unitMeasure, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]⟩

/-- Product uniform probability measure on `[0, 1]^V` governing node thresholds
([Kleinberg2007], Section 24.3, pp. 619–620). -/
noncomputable def thresholdMeasure (V : Type*) [Fintype V] : Measure (V → ℝ) :=
  Measure.pi fun _ : V => unitMeasure

theorem thresholdMeasure_def (V : Type*) [Fintype V] :
    thresholdMeasure V = Measure.pi fun _ : V => unitMeasure := by
  rfl

instance instIsProbabilityMeasureThresholdMeasure (V : Type*) [Fintype V] :
    IsProbabilityMeasure (thresholdMeasure V) := by
  unfold thresholdMeasure
  infer_instance

private theorem unitMeasure_real_Iic {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    unitMeasure.real (Iic a) = a := by
  have hset : Iic a ∩ Icc (0 : ℝ) 1 = Icc 0 a :=
    Set.Subset.antisymm (fun _ ⟨h1, h2, _⟩ => ⟨h2, h1⟩) fun _ ⟨h1, h2⟩ => ⟨h2, h1, h2.trans ha1⟩
  rw [unitMeasure, measureReal_def, Measure.restrict_apply measurableSet_Iic, hset,
    Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal ha0]

private theorem unitMeasure_real_Ioi {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    unitMeasure.real (Ioi a) = 1 - a := by
  simpa only [compl_Iic, unitMeasure_real_Iic ha0 ha1] using
    probReal_compl_eq_one_sub (μ := unitMeasure) (s := Iic a) measurableSet_Iic

private theorem unitMeasure_real_Ioc {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    unitMeasure.real (Ioc a b) = b - a := by
  have hset : Ioc a b ∩ Icc (0 : ℝ) 1 = Ioc a b :=
    inter_eq_left.mpr fun t ht => ⟨ha0.trans ht.1.le, ht.2.trans hb1⟩
  rw [unitMeasure, measureReal_def, Measure.restrict_apply measurableSet_Ioc, hset,
    Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

/-- Under `thresholdMeasure V`, almost every threshold draw satisfies `θ v ∈ (0, 1)` at every
vertex `v : V`. -/
theorem ae_mem_Ioo_thresholdMeasure (V : Type*) [Fintype V] :
    ∀ᵐ θ ∂thresholdMeasure V, ∀ v : V, θ v ∈ Ioo 0 1 := by
  have hae_unit : ∀ᵐ z ∂unitMeasure, z ∈ Ioo 0 1 := by
    have hm : MeasurableSet {z : ℝ | z ∉ Ioo (0 : ℝ) 1} := measurableSet_Ioo.compl
    rw [ae_iff, unitMeasure, Measure.restrict_apply hm]
    have hsub : {z : ℝ | z ∉ Ioo (0 : ℝ) 1} ∩ Icc (0 : ℝ) 1 ⊆ ({0} : Set ℝ) ∪ {1} :=
      fun z ⟨hnot, h0, h1⟩ => (eq_or_lt_of_le h0).imp Eq.symm fun hgt0 =>
        eq_of_le_of_not_lt h1 fun hlt1 => hnot ⟨hgt0, hlt1⟩
    exact nonpos_iff_eq_zero.mp <| (measure_mono hsub).trans <|
      (measure_union_le _ _).trans_eq (by simp)
  rw [thresholdMeasure_def, ae_all_iff]
  exact fun v =>
    (MeasureTheory.measurePreserving_eval (fun _ : V => unitMeasure) v).quasiMeasurePreserving.ae
      hae_unit

private theorem insert_inter_inNeighbors_of_not_adj {V : Type*} [DecidableEq V] [Fintype V]
    {G : Digraph V} [DecidableRel G.Adj] {u v : V} (hadj : ¬ G.Adj u v) (X : Finset V) :
    insert u X ∩ inNeighbors G v = X ∩ inNeighbors G v :=
  Finset.insert_inter_of_notMem (mt mem_inNeighbors.mp hadj)

/-! ## Progressive Threshold Dynamics and Outcome Distribution -/

namespace GeneralThresholdModel

variable {V : Type*} [DecidableEq V] [Fintype V] {G : Digraph V} [DecidableRel G.Adj]
  (M : GeneralThresholdModel G)

theorem thresholdFn_nonneg (v : V) (X : Finset V) : 0 ≤ M.thresholdFn v X :=
  M.thresholdFn_empty v ▸ M.monotone v (Finset.empty_subset X)

/-- One synchronous progressive activation step under threshold realization `θ : V → ℝ`
([Kleinberg2007], Section 24.3, p. 620): active vertices stay active, and every vertex `v` with
`θ v ≤ g_v(A)` becomes active. -/
noncomputable def thresholdStep (θ : V → ℝ) (A : Finset V) : Finset V :=
  haveI := Classical.decPred fun v => θ v ≤ M.thresholdFn v A
  A ∪ Finset.univ.filter fun v => θ v ≤ M.thresholdFn v A

@[simp]
theorem mem_thresholdStep {θ : V → ℝ} {A : Finset V} {v : V} :
    v ∈ M.thresholdStep θ A ↔ v ∈ A ∨ θ v ≤ M.thresholdFn v A := by
  unfold thresholdStep
  simp

theorem subset_thresholdStep (θ : V → ℝ) (A : Finset V) : A ⊆ M.thresholdStep θ A :=
  fun _ hv => M.mem_thresholdStep.mpr (Or.inl hv)

theorem thresholdStep_mono (θ : V → ℝ) : Monotone (M.thresholdStep θ) := by
  intro A B hAB v hv
  exact M.mem_thresholdStep.mpr <|
    (M.mem_thresholdStep.mp hv).imp (fun hvA => hAB hvA) fun hle => hle.trans (M.monotone v hAB)

/-- Final active set after `|V|` progressive steps from seed set `S` under thresholds `θ`
([Kleinberg2007], Section 24.4, p. 623). -/
noncomputable def thresholdFinal (θ : V → ℝ) (S : Finset V) : Finset V :=
  (M.thresholdStep θ)^[Fintype.card V] S

private theorem subset_thresholdStep_iterate (θ : V → ℝ) (S : Finset V) :
    ∀ t, S ⊆ (M.thresholdStep θ)^[t] S
  | 0 => Finset.Subset.refl S
  | t + 1 => by
    rw [Function.iterate_succ_apply']
    exact (subset_thresholdStep_iterate θ S t).trans (M.subset_thresholdStep θ _)

theorem subset_thresholdFinal (θ : V → ℝ) (S : Finset V) : S ⊆ M.thresholdFinal θ S :=
  M.subset_thresholdStep_iterate θ S (Fintype.card V)

theorem thresholdFinal_mono_seed (θ : V → ℝ) : Monotone (M.thresholdFinal θ) :=
  (M.thresholdStep_mono θ).iterate (Fintype.card V)

omit [DecidableEq V] in
/-- Any inflationary operator on `Finset V` stabilizes within `Fintype.card V` steps. -/
private theorem fixed_iterate_card {f : Finset V → Finset V} (hsub : ∀ X, X ⊆ f X)
    (S : Finset V) : f (f^[Fintype.card V] S) = f^[Fintype.card V] S := by
  classical
  by_contra hne
  have hstrict : ∀ k ≤ Fintype.card V, k ≤ (f^[k] S).card := by
    intro k hk
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hne_k : f (f^[k] S) ≠ f^[k] S := fun heq => hne <| by
        have hN := Function.iterate_fixed heq (Fintype.card V - k)
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_succ_le hk)] at hN
        exact hN ▸ heq
      rw [Function.iterate_succ_apply']
      exact Nat.succ_le_of_lt <| lt_of_le_of_lt (ih (Nat.le_of_succ_le hk)) <|
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub _, Ne.symm hne_k⟩)
  have hcard := hstrict _ le_rfl
  have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub _, Ne.symm hne⟩)
  have hle_univ := Finset.card_le_univ (f (f^[Fintype.card V] S))
  omega

theorem thresholdStep_thresholdFinal (θ : V → ℝ) (S : Finset V) :
    M.thresholdStep θ (M.thresholdFinal θ S) = M.thresholdFinal θ S :=
  fixed_iterate_card (M.subset_thresholdStep θ) S

theorem thresholdStep_iterate_eq_thresholdFinal (θ : V → ℝ) (S : Finset V) {t : ℕ}
    (ht : Fintype.card V ≤ t) :
    (M.thresholdStep θ)^[t] S = M.thresholdFinal θ S := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact Function.iterate_fixed (M.thresholdStep_thresholdFinal θ S) d

/-- Every vertex remaining inactive at `thresholdFinal θ S` has threshold strictly above
`g_v(thresholdFinal θ S)`. -/
theorem thresholdFn_lt_of_notMem_thresholdFinal {θ : V → ℝ} {S : Finset V} {v : V}
    (hv : v ∉ M.thresholdFinal θ S) :
    M.thresholdFn v (M.thresholdFinal θ S) < θ v := by
  rw [← M.thresholdStep_thresholdFinal θ S, M.mem_thresholdStep, not_or, not_le] at hv
  exact hv.2

/-- **Least post-fixed point property** of `thresholdFinal`: if `S ⊆ B` and every vertex outside `B`
has threshold strictly above `g_v(B)`, then `thresholdFinal θ S ⊆ B`. -/
theorem thresholdFinal_subset_of_lt {θ : V → ℝ} {S B : Finset V}
    (hSB : S ⊆ B) (hclosed : ∀ v ∉ B, M.thresholdFn v B < θ v) :
    M.thresholdFinal θ S ⊆ B := by
  have hfix : M.thresholdStep θ B = B := Finset.Subset.antisymm (fun v hv =>
    (M.mem_thresholdStep.mp hv).elim id fun hle =>
      by_contra fun hvnot => (hclosed v hvnot).not_ge hle) (M.subset_thresholdStep θ B)
  simpa only [thresholdFinal, Function.iterate_fixed hfix] using M.thresholdFinal_mono_seed θ hSB

/-- **Piecemeal growth identity** ([MosselRoch2007]): running from `S` first and then adding `T`
under the same thresholds `θ` produces the exact same final set as starting from `S ∪ T`. -/
theorem thresholdFinal_union_eq (θ : V → ℝ) (S T : Finset V) :
    M.thresholdFinal θ (M.thresholdFinal θ S ∪ T) = M.thresholdFinal θ (S ∪ T) := by
  refine Finset.Subset.antisymm ?_
    (M.thresholdFinal_mono_seed θ (Finset.union_subset_union_left (M.subset_thresholdFinal θ S)))
  refine M.thresholdFinal_subset_of_lt
    (Finset.union_subset (M.thresholdFinal_mono_seed θ Finset.subset_union_left)
      (Finset.subset_union_right.trans (M.subset_thresholdFinal θ (S ∪ T))))
    fun v hv => M.thresholdFn_lt_of_notMem_thresholdFinal hv

/-- Overwriting `θ` on coordinates already inside the seed set `S` leaves `thresholdFinal`
unchanged. -/
private theorem thresholdFinal_congr_outside {θ₁ θ₂ : V → ℝ} {S : Finset V}
    (h : ∀ v ∉ S, θ₁ v = θ₂ v) : M.thresholdFinal θ₁ S = M.thresholdFinal θ₂ S := by
  suffices ∀ t, (M.thresholdStep θ₁)^[t] S = (M.thresholdStep θ₂)^[t] S from this (Fintype.card V)
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    ext v
    simp only [mem_thresholdStep]
    by_cases hvA : v ∈ (M.thresholdStep θ₂)^[t] S
    · simp [hvA]
    · rw [h v fun hvS => hvA (M.subset_thresholdStep_iterate θ₂ S t hvS)]

/-- Factorization of the event `M.thresholdFinal θ S = K` into coordinates inside `K` and
independent survival inequalities `g_v(K) < θ v` on `Kᶜ`. -/
theorem thresholdFinal_eq_iff_piecewise (θ : V → ℝ) (S K : Finset V) :
    M.thresholdFinal θ S = K ↔
      M.thresholdFinal (K.piecewise θ fun _ => 2) S = K ∧ ∀ v ∉ K, M.thresholdFn v K < θ v := by
  set θK := K.piecewise θ fun _ => (2 : ℝ)
  have hstep_eq : ∀ {A : Finset V}, A ⊆ K → (∀ v ∉ K, M.thresholdFn v K < θ v) →
      M.thresholdStep θ A = M.thresholdStep θK A := fun {A} hAK hlt => by
    ext v
    simp only [mem_thresholdStep]
    by_cases hvK : v ∈ K
    · simp [θK, Finset.piecewise_eq_of_mem _ _ _ hvK]
    · have hnot1 : ¬ θ v ≤ M.thresholdFn v A :=
        not_le.mpr ((M.monotone v hAK).trans_lt (hlt v hvK))
      have hnot2 : ¬ θK v ≤ M.thresholdFn v A := by
        simp only [θK, Finset.piecewise_eq_of_notMem _ _ _ hvK]
        linarith [M.thresholdFn_le_one v A]
      simp [hnot1, hnot2]
  have hiter_eq : (∀ t, (M.thresholdStep θ)^[t] S ⊆ K) ∨ (∀ t, (M.thresholdStep θK)^[t] S ⊆ K) →
      (∀ v ∉ K, M.thresholdFn v K < θ v) →
      ∀ t, (M.thresholdStep θ)^[t] S = (M.thresholdStep θK)^[t] S := fun hsub hlt t => by
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact hstep_eq (hsub.elim (fun h1 => ih ▸ h1 t) (fun h2 => h2 t)) hlt
  have hsub_of_eq : ∀ {θ' : V → ℝ}, M.thresholdFinal θ' S = K →
      ∀ t, (M.thresholdStep θ')^[t] S ⊆ K := fun {θ'} heq' t => by
    have hle := M.subset_thresholdStep_iterate θ' ((M.thresholdStep θ')^[t] S) (Fintype.card V)
    rwa [← Function.iterate_add_apply,
      M.thresholdStep_iterate_eq_thresholdFinal θ' S (Nat.le_add_right _ _), heq'] at hle
  constructor
  · intro heq
    have hlt : ∀ v ∉ K, M.thresholdFn v K < θ v := fun v hvK =>
      heq ▸ M.thresholdFn_lt_of_notMem_thresholdFinal (v := v) (heq.symm ▸ hvK)
    exact ⟨(hiter_eq (Or.inl (hsub_of_eq heq)) hlt (Fintype.card V)).symm.trans heq, hlt⟩
  · rintro ⟨heqK, hlt⟩
    exact (hiter_eq (Or.inr (hsub_of_eq heqK)) hlt (Fintype.card V)).trans heqK

private theorem measurableSet_thresholdStep_eq (A B : Finset V) :
    MeasurableSet {θ : V → ℝ | M.thresholdStep θ A = B} := by
  have heq : {θ : V → ℝ | M.thresholdStep θ A = B} =
      univ.pi fun v =>
        if v ∈ A then (if v ∈ B then univ else ∅)
        else (if v ∈ B then Iic (M.thresholdFn v A) else Ioi (M.thresholdFn v A)) := by
    ext θ
    simp only [mem_ofPred_eq, Finset.ext_iff, M.mem_thresholdStep, mem_univ_pi]
    exact forall_congr' fun v => by
      by_cases hvA : v ∈ A <;> by_cases hvB : v ∈ B <;> simp [hvA, hvB]
  refine heq ▸ MeasurableSet.univ_pi fun v => ?_
  split_ifs
  exacts [.univ, .empty, measurableSet_Iic, measurableSet_Ioi]

theorem measurableSet_thresholdFinal_eq (S A : Finset V) :
    MeasurableSet {θ : V → ℝ | M.thresholdFinal θ S = A} := by
  suffices ∀ t (B : Finset V), MeasurableSet {θ : V → ℝ | (M.thresholdStep θ)^[t] S = B} from
    this (Fintype.card V) A
  intro t
  induction t with
  | zero =>
    intro B
    by_cases h : S = B <;> simp [h]
  | succ t ih =>
    intro B
    have hunion : {θ : V → ℝ | (M.thresholdStep θ)^[t + 1] S = B} =
        ⋃ C : Finset V,
          {θ | (M.thresholdStep θ)^[t] S = C} ∩ {θ | M.thresholdStep θ C = B} := by
      ext θ
      simp [Function.iterate_succ_apply']
    exact hunion ▸ MeasurableSet.iUnion fun C => (ih C).inter (M.measurableSet_thresholdStep_eq C B)

/-- Probability `(thresholdMeasure V).real {θ | M.thresholdFinal θ S = A}` that the progressive
threshold process starting from `S` terminates at exact active set `A`. -/
noncomputable def activeSetProb (S A : Finset V) : ℝ :=
  (thresholdMeasure V).real {θ : V → ℝ | M.thresholdFinal θ S = A}

/-- Expected number of active nodes `f(S) = E_θ[|thresholdFinal θ S|]` at the end of the process
([Kleinberg2007], Section 24.4, p. 623). -/
noncomputable def influence (S : Finset V) : ℝ :=
  ∫ θ, ((M.thresholdFinal θ S).card : ℝ) ∂thresholdMeasure V

theorem influence_def (S : Finset V) :
    M.influence S = ∫ θ, ((M.thresholdFinal θ S).card : ℝ) ∂thresholdMeasure V := by
  rfl

private theorem apply_thresholdFinal_eq_sum (S : Finset V) (φ : Finset V → ℝ) :
    (fun θ : V → ℝ => φ (M.thresholdFinal θ S)) =
      fun θ => ∑ A : Finset V,
        ({θ' : V → ℝ | M.thresholdFinal θ' S = A}).indicator (fun _ => φ A) θ := by
  ext θ
  rw [Finset.sum_eq_single (M.thresholdFinal θ S) (fun _ _ hne => indicator_of_notMem hne.symm _)
    (fun h => absurd (Finset.mem_univ _) h)]
  simp

theorem integrable_of_finset (S : Finset V) (φ : Finset V → ℝ) :
    Integrable (fun θ : V → ℝ => φ (M.thresholdFinal θ S)) (thresholdMeasure V) := by
  rw [M.apply_thresholdFinal_eq_sum S φ]
  exact integrable_finsetSum _ fun A _ =>
    (integrable_const (φ A)).indicator (M.measurableSet_thresholdFinal_eq S A)

theorem integral_thresholdFinal_eq_sum (S : Finset V) (φ : Finset V → ℝ) :
    (∫ θ, φ (M.thresholdFinal θ S) ∂thresholdMeasure V) =
      ∑ A : Finset V, M.activeSetProb S A * φ A := by
  rw [M.apply_thresholdFinal_eq_sum S φ, integral_finsetSum _ fun A _ =>
    (integrable_const (φ A)).indicator (M.measurableSet_thresholdFinal_eq S A)]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [integral_indicator_const _ (M.measurableSet_thresholdFinal_eq S A), smul_eq_mul,
    activeSetProb]

theorem influence_eq_sum_activeSetProb (S : Finset V) :
    M.influence S = ∑ A : Finset V, M.activeSetProb S A * (A.card : ℝ) :=
  M.integral_thresholdFinal_eq_sum S fun A => (A.card : ℝ)

theorem monotone_influence : Monotone M.influence := by
  intro A B hAB
  exact integral_mono (M.integrable_of_finset A fun X => (X.card : ℝ))
    (M.integrable_of_finset B fun X => (X.card : ℝ)) fun θ =>
    Nat.cast_le.mpr (Finset.card_le_card (M.thresholdFinal_mono_seed θ hAB))

/-- If every inactive vertex outside `S` has zero threshold value `g_v(S) = 0`, no additional
vertices activate almost surely and `M.influence S = S.card`. -/
theorem influence_eq_card_of_forall_eq_zero {S : Finset V}
    (hzero : ∀ v ∉ S, M.thresholdFn v S = 0) :
    M.influence S = (S.card : ℝ) := by
  have hae : ∀ᵐ θ ∂thresholdMeasure V, ((M.thresholdFinal θ S).card : ℝ) = (S.card : ℝ) := by
    filter_upwards [ae_mem_Ioo_thresholdMeasure V] with θ hθ
    rw [Finset.Subset.antisymm
      (M.thresholdFinal_subset_of_lt (Finset.Subset.refl S) fun v hv =>
        (hzero v hv).symm ▸ (hθ v).1)
      (M.subset_thresholdFinal θ S)]
  rw [influence, integral_congr_ae hae, integral_const, probReal_univ, one_smul]

/-- If every inactive vertex outside `S` already has saturated threshold `g_v(S) = 1`, the entire
vertex set activates in one step almost surely and `M.influence S = Fintype.card V`. -/
theorem influence_eq_card_univ_of_forall_eq_one {S : Finset V}
    (hone : ∀ v ∉ S, M.thresholdFn v S = 1) :
    M.influence S = (Fintype.card V : ℝ) := by
  have hae : ∀ᵐ θ ∂thresholdMeasure V,
      ((M.thresholdFinal θ S).card : ℝ) = (Fintype.card V : ℝ) := by
    filter_upwards [ae_mem_Ioo_thresholdMeasure V] with θ hθ
    have hstep_univ : M.thresholdStep θ S = Finset.univ := Finset.eq_univ_of_forall fun v =>
      M.mem_thresholdStep.mpr <| (em (v ∈ S)).imp_right fun hv =>
        (hθ v).2.le.trans (hone v hv).symm.le
    have hfin_univ : M.thresholdFinal θ S = Finset.univ := by
      rcases isEmpty_or_nonempty V with hE | hNE
      · exact Subsingleton.elim _ _
      · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Fintype.card_pos (α := V))
        rw [thresholdFinal, hk, Nat.add_comm 1 k, Function.iterate_add_apply, Function.iterate_one,
          hstep_univ]
        exact Finset.eq_univ_of_forall fun v =>
          M.subset_thresholdStep_iterate θ Finset.univ k (Finset.mem_univ v)
    rw [hfin_univ, Finset.card_univ]
  rw [influence, integral_congr_ae hae, integral_const, probReal_univ, one_smul]

@[simp]
theorem influence_empty : M.influence ∅ = 0 := by
  simpa using M.influence_eq_card_of_forall_eq_zero fun v _ => M.thresholdFn_empty v

end GeneralThresholdModel

/-! ## Order-Independent and Independent Cascade Models -/

/-- Sequential survival probability `∏_{i=1}^k (1 - p_v(u_i, X_{i-1}))` when neighbors in `us`
attempt to activate `v` in list order after failed set `X` ([Kleinberg2007], Section 24.3,
p. 621). -/
def seqSurvival {V : Type*} [DecidableEq V] (p : V → V → Finset V → ℝ) (v : V) :
    List V → Finset V → ℝ
  | [], _ => 1
  | u :: us, X => (1 - p v u X) * seqSurvival p v us (insert u X)

/-- **Order-Independent Cascade Model** on `G : Digraph V` ([KempeKleinbergTardos2005];
[Kleinberg2007], Section 24.3, pp. 620–621): active in-neighbors `u` attempt to activate inactive
`v` with incremental success probability `prob v u X`, where sequential survival is invariant under
permuting attempt order (`swap_survival`). -/
structure CascadeModel {V : Type*} [DecidableEq V] [Fintype V]
    (G : Digraph V) [DecidableRel G.Adj] where
  /-- Incremental probability `p_v(u, X)` that `u` activates `v` given failed set `X`. -/
  prob : V → V → Finset V → ℝ
  /-- Incremental probabilities are nonnegative. -/
  prob_nonneg : ∀ v u X, 0 ≤ prob v u X
  /-- Incremental probabilities are at most `1`. -/
  prob_le_one : ∀ v u X, prob v u X ≤ 1
  /-- Non-neighbors exert zero activation probability. -/
  prob_eq_zero_of_not_adj : ∀ v u X, ¬ G.Adj u v → prob v u X = 0
  /-- Failed-history dependence looks only at incoming neighbors `X ∩ inNeighbors G v`. -/
  inNeighbors_congr : ∀ v u X, prob v u (X ∩ inNeighbors G v) = prob v u X
  /-- Order-independence of two-step survival probabilities for distinct untried vertices. -/
  swap_survival : ∀ v u₁ u₂ (X : Finset V), u₁ ≠ u₂ → u₁ ∉ X → u₂ ∉ X →
    (1 - prob v u₁ X) * (1 - prob v u₂ (insert u₁ X)) =
      (1 - prob v u₂ X) * (1 - prob v u₁ (insert u₂ X))

/-- **Independent Cascade Model** on `G : Digraph V` ([KempeKleinbergTardos2003];
[Kleinberg2007], Section 24.3, p. 621): activation attempts across `(u, v)` succeed independently
with parameter `edgeProb u v ∈ [0, 1]`. -/
structure IndependentCascadeModel {V : Type*} (G : Digraph V) where
  /-- Edge activation probability `p_{uv}`. -/
  edgeProb : V → V → ℝ
  /-- Edge probabilities are nonnegative. -/
  edgeProb_nonneg : ∀ u v, 0 ≤ edgeProb u v
  /-- Edge probabilities are at most `1`. -/
  edgeProb_le_one : ∀ u v, edgeProb u v ≤ 1
  /-- Edge probabilities vanish outside `G`. -/
  edgeProb_eq_zero_of_not_adj : ∀ u v, ¬ G.Adj u v → edgeProb u v = 0

/-- Embed an `IndependentCascadeModel` into `CascadeModel` via history-independent probabilities
`p_v(u, X) = edgeProb u v` ([Kleinberg2007], Section 24.3, p. 621). -/
def IndependentCascadeModel.toCascadeModel {V : Type*} [DecidableEq V] [Fintype V]
    {G : Digraph V} [DecidableRel G.Adj] (IC : IndependentCascadeModel G) :
    CascadeModel G where
  prob v u _ := IC.edgeProb u v
  prob_nonneg v u _ := IC.edgeProb_nonneg u v
  prob_le_one v u _ := IC.edgeProb_le_one u v
  prob_eq_zero_of_not_adj v u _ h := IC.edgeProb_eq_zero_of_not_adj u v h
  inNeighbors_congr _ _ _ := rfl
  swap_survival _ _ _ _ _ _ _ := mul_comm _ _

@[simp]
theorem IndependentCascadeModel.toCascadeModel_prob {V : Type*} [DecidableEq V] [Fintype V]
    {G : Digraph V} [DecidableRel G.Adj] (IC : IndependentCascadeModel G)
    (v u : V) (X : Finset V) :
    IC.toCascadeModel.prob v u X = IC.edgeProb u v := by
  rfl

namespace CascadeModel

variable {V : Type*} [DecidableEq V] [Fintype V] {G : Digraph V} [DecidableRel G.Adj]
  (C : CascadeModel G)

/-- Diminishing-returns condition on incremental cascade probabilities
([Kleinberg2007], Section 24.3, p. 621): `X ⊆ Y → p_v(u, Y) ≤ p_v(u, X)` for untried `u ∉ Y`. -/
@[expose] def HasDiminishingReturns : Prop :=
  ∀ v u ⦃X Y : Finset V⦄, X ⊆ Y → u ∉ Y → C.prob v u Y ≤ C.prob v u X

theorem _root_.Cslib.GameTheory.Network.IndependentCascadeModel.hasDiminishingReturns_toCascadeModel
    (IC : IndependentCascadeModel G) : IC.toCascadeModel.HasDiminishingReturns :=
  fun _ _ _ _ _ _ => le_rfl

/-- `seqSurvival C.prob v us X` is invariant under permuting any duplicate-free list `us` disjoint
from `X`, confirming multi-step order-independence ([Kleinberg2007], Section 24.3, pp. 620–621). -/
theorem seqSurvival_perm (v : V) {us₁ us₂ : List V} (hp : us₁.Perm us₂) :
    ∀ {X : Finset V}, us₁.Nodup → (∀ u ∈ us₁, u ∉ X) →
      seqSurvival C.prob v us₁ X = seqSurvival C.prob v us₂ X := by
  induction hp with
  | nil => intro _ _ _; rfl
  | @cons u l₁ l₂ _ ih =>
    intro X hnd hdisj
    rw [List.nodup_cons] at hnd
    simp only [seqSurvival]
    congr 1
    refine ih hnd.2 fun w hw => ?_
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun hwu => hnd.1 (hwu ▸ hw), hdisj w (List.mem_cons_of_mem u hw)⟩
  | @swap u₂ u₁ l =>
    intro X hnd hdisj
    rw [List.nodup_cons, List.nodup_cons] at hnd
    have hne : u₁ ≠ u₂ := fun h => hnd.1 (h ▸ List.mem_cons_self)
    have hu₁ : u₁ ∉ X := hdisj u₁ List.mem_cons_self
    have hu₂ : u₂ ∉ X := hdisj u₂ (List.mem_cons_of_mem u₁ List.mem_cons_self)
    simp only [seqSurvival, ← mul_assoc]
    rw [C.swap_survival v u₁ u₂ X hne hu₁ hu₂, Finset.insert_comm u₁ u₂ X]
  | @trans l₁ l₂ l₃ hp₁ _ ih₁ ih₂ =>
    intro X hnd hdisj
    exact (ih₁ hnd hdisj).trans
      (ih₂ (hp₁.nodup_iff.mp hnd) fun u hu => hdisj u (hp₁.mem_iff.mpr hu))

private theorem seqSurvival_append (v : V) (us₁ us₂ : List V) :
    ∀ X : Finset V,
      seqSurvival C.prob v (us₁ ++ us₂) X =
        seqSurvival C.prob v us₁ X * seqSurvival C.prob v us₂ (us₁.toFinset ∪ X) := by
  induction us₁ with
  | nil => intro X; simp [seqSurvival]
  | cons u us₁ ih =>
    intro X
    simp only [List.cons_append, seqSurvival, ih (insert u X), mul_assoc]
    congr 3
    ext w
    simp

/-- Order-independent survival probability `∏_{i=1}^k (1 - p_v(u_i, X_{i-1}))` that vertex `v`
is *not* activated when all vertices in `X` attempt to activate it ([Kleinberg2007], Section 24.3,
p. 621). -/
noncomputable def survivalProb (v : V) (X : Finset V) : ℝ :=
  seqSurvival C.prob v X.toList ∅

@[simp]
theorem survivalProb_empty (v : V) : C.survivalProb v ∅ = 1 := by
  simp [survivalProb, seqSurvival]

private theorem survivalProb_eq_seqSurvival (v : V) {us : List V} (hnd : us.Nodup) :
    C.survivalProb v us.toFinset = seqSurvival C.prob v us ∅ := by
  unfold survivalProb
  have hperm : us.toFinset.toList.Perm us :=
    List.perm_ext_iff_of_nodup (Finset.nodup_toList _) hnd |>.mpr fun x => by simp
  exact C.seqSurvival_perm v hperm (Finset.nodup_toList _) fun _ _ => Finset.notMem_empty _

theorem survivalProb_insert (v : V) {u : V} {X : Finset V} (hu : u ∉ X) :
    C.survivalProb v (insert u X) = C.survivalProb v X * (1 - C.prob v u X) := by
  have hnd : (X.toList ++ [u]).Nodup := List.nodup_append_comm.mp
    (List.nodup_cons.mpr ⟨mt Finset.mem_toList.mp hu, Finset.nodup_toList X⟩)
  have hfin : (X.toList ++ [u]).toFinset = insert u X := Finset.ext fun _ => by simp
  rw [← hfin, C.survivalProb_eq_seqSurvival v hnd, C.seqSurvival_append, Finset.toList_toFinset,
    Finset.union_empty]
  simp [survivalProb, seqSurvival]

theorem survivalProb_nonneg (v : V) (X : Finset V) : 0 ≤ C.survivalProb v X := by
  induction X using Finset.induction with
  | empty => simp
  | insert u X hu ih =>
    rw [C.survivalProb_insert v hu]
    exact mul_nonneg ih (sub_nonneg.mpr (C.prob_le_one v u X))

theorem survivalProb_le_one (v : V) (X : Finset V) : C.survivalProb v X ≤ 1 := by
  induction X using Finset.induction with
  | empty => simp
  | insert u X hu ih =>
    rw [C.survivalProb_insert v hu]
    have h1 : 1 - C.prob v u X ≤ 1 := sub_le_self 1 (C.prob_nonneg v u X)
    exact (mul_le_of_le_one_right (C.survivalProb_nonneg v X) h1).trans ih

theorem survivalProb_anti (v : V) ⦃X Y : Finset V⦄ (hXY : X ⊆ Y) :
    C.survivalProb v Y ≤ C.survivalProb v X := by
  have hdiff : Y = X ∪ (Y \ X) := (Finset.union_sdiff_of_subset hXY).symm
  rw [hdiff]
  have hdisj : Disjoint X (Y \ X) := Finset.disjoint_sdiff
  generalize Y \ X = D at hdisj
  induction D using Finset.induction with
  | empty => simp
  | insert u D huD ih =>
    rcases Finset.disjoint_insert_right.mp hdisj with ⟨huX, hdisj'⟩
    have huXD : u ∉ X ∪ D := by simp [huX, huD]
    rw [Finset.union_insert, C.survivalProb_insert v huXD]
    have h1 : 1 - C.prob v u (X ∪ D) ≤ 1 := sub_le_self 1 (C.prob_nonneg v u _)
    exact (mul_le_of_le_one_right (C.survivalProb_nonneg v _) h1).trans (ih hdisj')

private theorem survivalProb_inNeighbors_inter (v : V) (X : Finset V) :
    C.survivalProb v (X ∩ inNeighbors G v) = C.survivalProb v X := by
  induction X using Finset.induction with
  | empty => simp
  | insert u X hu ih =>
    by_cases hadj : G.Adj u v
    · have hu' : u ∉ X ∩ inNeighbors G v := fun h => hu (Finset.mem_inter.mp h).1
      rw [Finset.insert_inter_of_mem (mem_inNeighbors.mpr hadj), C.survivalProb_insert v hu',
        C.survivalProb_insert v hu, ih, C.inNeighbors_congr v u X]
    · rw [insert_inter_inNeighbors_of_not_adj hadj X, C.survivalProb_insert v hu,
        C.prob_eq_zero_of_not_adj v u X hadj, sub_zero, mul_one, ih]

/-- Translate an order-independent `CascadeModel` to its equivalent `GeneralThresholdModel` via
`g_v(X) = 1 - survivalProb C v X` ([KempeKleinbergTardos2005]; [Kleinberg2007], Section 24.3,
p. 621). -/
noncomputable def toGeneralThresholdModel : GeneralThresholdModel G where
  thresholdFn v X := 1 - C.survivalProb v X
  thresholdFn_empty v := by simp
  thresholdFn_le_one v X := sub_le_self 1 (C.survivalProb_nonneg v X)
  monotone v X Y hXY := sub_le_sub_left (C.survivalProb_anti v hXY) 1
  inNeighbors_congr v X := by rw [C.survivalProb_inNeighbors_inter]

@[simp]
theorem toGeneralThresholdModel_thresholdFn (v : V) (X : Finset V) :
    C.toGeneralThresholdModel.thresholdFn v X = 1 - C.survivalProb v X := by
  rfl

end CascadeModel

/-! ## Forward Translation `GeneralThresholdModel → CascadeModel` and Equivalence -/

namespace GeneralThresholdModel

variable {V : Type*} [DecidableEq V] [Fintype V] {G : Digraph V} [DecidableRel G.Adj]
  (M : GeneralThresholdModel G)

private theorem one_sub_thresholdFn_mul_one_sub_div (v u : V) (X : Finset V) :
    (1 - M.thresholdFn v X) *
      (1 - (M.thresholdFn v (insert u X) - M.thresholdFn v X) / (1 - M.thresholdFn v X)) =
      1 - M.thresholdFn v (insert u X) := by
  by_cases h1 : M.thresholdFn v X = 1
  · have h2 : M.thresholdFn v (insert u X) = 1 :=
      le_antisymm (M.thresholdFn_le_one v _) (h1 ▸ M.monotone v (Finset.subset_insert u X))
    simp [h1, h2]
  · have hne : 1 - M.thresholdFn v X ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    field_simp [hne]
    ring

/-- Translate a `GeneralThresholdModel` to an order-independent `CascadeModel` via
`p_v(u, X) = (g_v(insert u X) - g_v(X)) / (1 - g_v(X))` ([KempeKleinbergTardos2005];
[Kleinberg2007], Section 24.3, p. 621). When `g_v(X) = 1`, Lean's `0 / 0 = 0` sets `p_v(u, X) = 0`
and preserves `(1 - g_v(X)) * (1 - p_v(u, X)) = 1 - g_v(insert u X)` unconditionally. -/
noncomputable def toCascadeModel : CascadeModel G where
  prob v u X := (M.thresholdFn v (insert u X) - M.thresholdFn v X) / (1 - M.thresholdFn v X)
  prob_nonneg v u X :=
    div_nonneg (sub_nonneg.mpr (M.monotone v (Finset.subset_insert u X)))
      (sub_nonneg.mpr (M.thresholdFn_le_one v X))
  prob_le_one v u X := by
    by_cases h1 : M.thresholdFn v X = 1
    · have h2 : M.thresholdFn v (insert u X) = 1 :=
        le_antisymm (M.thresholdFn_le_one v _) (h1 ▸ M.monotone v (Finset.subset_insert u X))
      simp [h1, h2]
    · have hpos : 0 < 1 - M.thresholdFn v X :=
        sub_pos.mpr (lt_of_le_of_ne (M.thresholdFn_le_one v X) h1)
      rw [div_le_one hpos]
      linarith [M.thresholdFn_le_one v (insert u X)]
  prob_eq_zero_of_not_adj v u X hadj := by
    have heq : M.thresholdFn v (insert u X) = M.thresholdFn v X := by
      rw [← M.inNeighbors_congr v (insert u X), insert_inter_inNeighbors_of_not_adj hadj X,
        M.inNeighbors_congr v X]
    simp [heq]
  inNeighbors_congr v u X := by
    rw [M.inNeighbors_congr v X]
    congr 2
    rw [← M.inNeighbors_congr v (insert u (X ∩ inNeighbors G v)),
      ← M.inNeighbors_congr v (insert u X)]
    congr 1
    ext w
    simp only [Finset.mem_inter, Finset.mem_insert, mem_inNeighbors]
    tauto
  swap_survival v u₁ u₂ X _ _ _ := by
    have key : ∀ a b Y,
        (1 - (M.thresholdFn v (insert a Y) - M.thresholdFn v Y) / (1 - M.thresholdFn v Y)) *
          (1 - (M.thresholdFn v (insert b (insert a Y)) - M.thresholdFn v (insert a Y)) /
            (1 - M.thresholdFn v (insert a Y))) =
        if M.thresholdFn v Y = 1 then 1
        else if M.thresholdFn v (insert a Y) = 1 then 0
        else (1 - M.thresholdFn v (insert b (insert a Y))) / (1 - M.thresholdFn v Y) := by
      intro a b Y
      split_ifs with hY haY
      · have ha : M.thresholdFn v (insert a Y) = 1 :=
          le_antisymm (M.thresholdFn_le_one v _) (hY ▸ M.monotone v (Finset.subset_insert a Y))
        have hab : M.thresholdFn v (insert b (insert a Y)) = 1 :=
          le_antisymm (M.thresholdFn_le_one v _) (ha ▸ M.monotone v (Finset.subset_insert b _))
        simp [hY, ha, hab]
      · have hneY : 1 - M.thresholdFn v Y ≠ 0 := sub_ne_zero.mpr (Ne.symm hY)
        have h1 :
            1 - (M.thresholdFn v (insert a Y) - M.thresholdFn v Y) /
              (1 - M.thresholdFn v Y) = 0 := by
          rw [haY, div_self hneY, sub_self]
        rw [h1, zero_mul]
      · have hneY : 1 - M.thresholdFn v Y ≠ 0 := sub_ne_zero.mpr (Ne.symm hY)
        have hnea : 1 - M.thresholdFn v (insert a Y) ≠ 0 := sub_ne_zero.mpr (Ne.symm haY)
        field_simp [hneY, hnea]
        ring
    rw [key u₁ u₂ X, key u₂ u₁ X, Finset.insert_comm u₂ u₁ X]
    by_cases hX : M.thresholdFn v X = 1
    · simp [hX]
    · simp only [hX, ↓reduceIte]
      by_cases h1 : M.thresholdFn v (insert u₁ X) = 1
      · have hab : M.thresholdFn v (insert u₁ (insert u₂ X)) = 1 := by
          rw [Finset.insert_comm u₁ u₂ X]
          exact le_antisymm (M.thresholdFn_le_one v _)
            (h1 ▸ M.monotone v (Finset.subset_insert u₂ _))
        split_ifs
        · rfl
        · simp [hab]
      · simp only [h1, ↓reduceIte]
        split_ifs with h2
        · have hab : M.thresholdFn v (insert u₁ (insert u₂ X)) = 1 :=
            le_antisymm (M.thresholdFn_le_one v _) (h2 ▸ M.monotone v (Finset.subset_insert u₁ _))
          simp [hab]
        · rfl

@[simp]
theorem toCascadeModel_prob (v u : V) (X : Finset V) :
    M.toCascadeModel.prob v u X =
      (M.thresholdFn v (insert u X) - M.thresholdFn v X) / (1 - M.thresholdFn v X) := by
  rfl

/-- Translating a `GeneralThresholdModel` to `CascadeModel` and back is the identity
([KempeKleinbergTardos2005]; [Kleinberg2007], Section 24.3, p. 621). -/
@[simp]
theorem toGeneralThresholdModel_toCascadeModel :
    M.toCascadeModel.toGeneralThresholdModel = M := by
  ext v X
  suffices M.toCascadeModel.survivalProb v X = 1 - M.thresholdFn v X by
    simp [CascadeModel.toGeneralThresholdModel, this]
  induction X using Finset.induction with
  | empty => simp [M.thresholdFn_empty v]
  | insert u X hu ih =>
    rw [M.toCascadeModel.survivalProb_insert v hu, ih]
    exact M.one_sub_thresholdFn_mul_one_sub_div v u X

end GeneralThresholdModel

/-! ## Operational Cascade Dynamics and Equivalence of Final Active-Set Distributions -/

namespace CascadeModel

variable {V : Type*} [DecidableEq V] [Fintype V] {G : Digraph V} [DecidableRel G.Adj]
  (C : CascadeModel G)

/-- Set of remaining untried active-to-inactive directed edges `(u, v)` at cascade state
`(active, tried)`. -/
def untriedEdges (G : Digraph V) [DecidableRel G.Adj]
    (active : Finset V) (tried : V → Finset V) : Finset (V × V) :=
  (active ×ˢ (Finset.univ \ active)).filter fun e => G.Adj e.1 e.2 ∧ e.1 ∉ tried e.2

@[simp]
theorem mem_untriedEdges {active : Finset V} {tried : V → Finset V} {e : V × V} :
    e ∈ untriedEdges G active tried ↔
      e.1 ∈ active ∧ e.2 ∉ active ∧ G.Adj e.1 e.2 ∧ e.1 ∉ tried e.2 := by
  simp only [untriedEdges, Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff,
    Finset.mem_univ, true_and, and_assoc]

/-- Default edge-attempt selector choosing an untried active-to-inactive edge from
`untriedEdges G active tried` when nonempty and returning `none` otherwise. -/
noncomputable def defaultNextEdge (G : Digraph V) [DecidableRel G.Adj]
    (active : Finset V) (tried : V → Finset V) : Option (V × V) :=
  if h : (untriedEdges G active tried).Nonempty then some h.choose else none

private theorem card_sq_sub_sum_card_update_lt {tried : V → Finset V} {v u : V}
    (hu : u ∉ tried v) :
    Fintype.card V * Fintype.card V -
        ∑ w : V, (Function.update tried v (insert u (tried v)) w).card <
      Fintype.card V * Fintype.card V - ∑ w : V, (tried w).card := by
  have hcard_lt : ∑ w : V, (tried w).card <
      ∑ w : V, (Function.update tried v (insert u (tried v)) w).card := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v),
      ← Finset.add_sum_erase _ (fun w => (Function.update tried v _ w).card) (Finset.mem_univ v),
      Function.update_self, Finset.card_insert_of_notMem hu]
    exact Nat.add_lt_add_of_lt_of_le (Nat.lt_succ_self _) (Finset.sum_le_sum fun w hw => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)])
  have hbound : ∑ w : V, (Function.update tried v (insert u (tried v)) w).card ≤
      Fintype.card V * Fintype.card V :=
    (Finset.sum_le_sum fun _ _ => Finset.card_le_univ _).trans (by simp)
  omega

/-- Operational sequential cascade probability from intermediate state `(active, tried)` under
attempt selector `nextEdge` ([Kleinberg2007], Section 24.3, p. 620): if `nextEdge` selects an
untried edge `(u, v)` (`u ∈ active`, `v ∉ active`, `G.Adj u v`, `u ∉ tried v`), `u` activates `v`
with probability `C.prob v u (tried v)` and fails with probability `1 - C.prob v u (tried v)`,
recording `u ∈ tried' v` in both branches; otherwise the process terminates at `active`. -/
private noncomputable def cascadeProbFrom (nextEdge : Finset V → (V → Finset V) → Option (V × V))
    (active : Finset V) (tried : V → Finset V) (A : Finset V) : ℝ :=
  match nextEdge active tried with
  | none => if active = A then 1 else 0
  | some (u, v) =>
    if h : (u, v) ∈ untriedEdges G active tried then
      let p := C.prob v u (tried v)
      let tried' := Function.update tried v (insert u (tried v))
      p * cascadeProbFrom nextEdge (insert v active) tried' A +
        (1 - p) * cascadeProbFrom nextEdge active tried' A
    else
      if active = A then 1 else 0
termination_by Fintype.card V * Fintype.card V - ∑ w : V, (tried w).card
decreasing_by
  all_goals exact card_sq_sub_sum_card_update_lt (mem_untriedEdges.mp h).2.2.2

/-- An edge selector `nextEdge` is valid if it picks an untried active-to-inactive edge whenever
one exists and returns `none` when none exists. -/
@[expose] def ValidNextEdge (G : Digraph V) [DecidableRel G.Adj]
    (nextEdge : Finset V → (V → Finset V) → Option (V × V)) : Prop :=
  ∀ active tried,
    ((untriedEdges G active tried).Nonempty →
      ∃ e ∈ untriedEdges G active tried, nextEdge active tried = some e) ∧
    (untriedEdges G active tried = ∅ → nextEdge active tried = none)

theorem validNextEdge_defaultNextEdge : ValidNextEdge G (defaultNextEdge G) := by
  intro active tried
  refine ⟨fun hne => ⟨hne.choose, hne.choose_spec, by simp [defaultNextEdge, hne]⟩, fun hemp => ?_⟩
  simp [defaultNextEdge, hemp]

/-- Probability that the Cascade Model starting from seed set `S` (with empty initial `tried`
histories) under selector `nextEdge` terminates at active set `A`. -/
noncomputable def activeSetProb (nextEdge : Finset V → (V → Finset V) → Option (V × V))
    (S A : Finset V) : ℝ :=
  C.cascadeProbFrom nextEdge S (fun _ => ∅) A

/-- Expected number of final active nodes in the Cascade Model starting from `S`
([Kleinberg2007], Section 24.4, p. 623). -/
noncomputable def influence (S : Finset V) : ℝ :=
  ∑ A : Finset V, C.activeSetProb (defaultNextEdge G) S A * (A.card : ℝ)

theorem influence_def (S : Finset V) :
    C.influence S = ∑ A : Finset V, C.activeSetProb (defaultNextEdge G) S A * (A.card : ℝ) := by
  rfl

/-- Cylinder event of threshold draws `θ` surviving the already-tried history `tried` on inactive
vertices `activeᶜ`, intersected with terminating at `A`. -/
private def survEvent (M : GeneralThresholdModel G) (active : Finset V) (tried : V → Finset V)
    (A : Finset V) : Set (V → ℝ) :=
  {θ : V → ℝ | (∀ w ∉ active, M.thresholdFn w (tried w) < θ w) ∧ M.thresholdFinal θ active = A}

private theorem measurableSet_survEvent (M : GeneralThresholdModel G)
    (active : Finset V) (tried : V → Finset V) (A : Finset V) :
    MeasurableSet (survEvent M active tried A) := by
  have heq : survEvent M active tried A =
      (univ.pi fun w => if w ∈ active then univ else Ioi (M.thresholdFn w (tried w))) ∩
        {θ | M.thresholdFinal θ active = A} := by
    ext θ
    simp only [survEvent, mem_ofPred_eq, mem_inter_iff, mem_univ_pi]
    refine and_congr_left' ⟨fun h w => ?_, fun h w hw => ?_⟩
    · by_cases hw : w ∈ active <;> simp [hw, h]
    · simpa [hw] using h w
  rw [heq]
  refine (MeasurableSet.univ_pi fun w => ?_).inter (M.measurableSet_thresholdFinal_eq active A)
  split_ifs
  exacts [.univ, measurableSet_Ioi]

private theorem survivalProd_mul_cascadeProbFrom_eq
    {nextEdge : Finset V → (V → Finset V) → Option (V × V)} (hvalid : ValidNextEdge G nextEdge)
    (A : Finset V) (F : Finset V → (V → Finset V) → ℝ)
    (hbase : ∀ active tried, (∀ w ∉ active, tried w = active ∩ inNeighbors G w) →
      F active tried = if active = A then ∏ w ∈ activeᶜ, C.survivalProb w (tried w) else 0)
    (hstep : ∀ active tried, (∀ w ∉ active, tried w ⊆ active ∩ inNeighbors G w) →
      ∀ u v, u ∈ active → v ∉ active → G.Adj u v → u ∉ tried v →
        F active tried =
          C.prob v u (tried v) * C.survivalProb v (tried v) *
              F (insert v active) (Function.update tried v (insert u (tried v))) +
            F active (Function.update tried v (insert u (tried v))))
    (active : Finset V) (tried : V → Finset V)
    (hinv : ∀ w ∉ active, tried w ⊆ active ∩ inNeighbors G w) :
    (∏ w ∈ activeᶜ, C.survivalProb w (tried w)) *
        C.cascadeProbFrom nextEdge active tried A =
      F active tried := by
  suffices ∀ n, Fintype.card V * Fintype.card V - ∑ w : V, (tried w).card = n →
      (∏ w ∈ activeᶜ, C.survivalProb w (tried w)) *
          C.cascadeProbFrom nextEdge active tried A =
        F active tried from this _ rfl
  intro n
  induction n using Nat.strong_induction_on generalizing active tried with
  | _ n ih =>
    intro hn
    by_cases hne : (untriedEdges G active tried).Nonempty
    · obtain ⟨⟨u, v⟩, huv_mem, hnext⟩ := (hvalid active tried).1 hne
      rcases mem_untriedEdges.mp huv_mem with ⟨hu_act, hv_inact, hadj, hu_untried⟩
      dsimp only at hu_act hv_inact hadj hu_untried
      let tried' := Function.update tried v (insert u (tried v))
      have hm_lt : Fintype.card V * Fintype.card V - ∑ w : V, (tried' w).card < n :=
        hn ▸ card_sq_sub_sum_card_update_lt hu_untried
      have hinv_succ : ∀ w ∉ insert v active, tried' w ⊆ insert v active ∩ inNeighbors G w :=
        fun w hw => by
          rw [Finset.mem_insert, not_or] at hw
          simpa only [tried', Function.update_of_ne hw.1] using
            (hinv w hw.2).trans (Finset.inter_subset_inter_right (Finset.subset_insert v active))
      have hinv_fail : ∀ w ∉ active, tried' w ⊆ active ∩ inNeighbors G w := fun w hw => by
        rcases eq_or_ne w v with rfl | hwv
        · simpa only [tried', Function.update_self] using
            Finset.insert_subset (Finset.mem_inter.mpr ⟨hu_act, mem_inNeighbors.mpr hadj⟩)
              (hinv w hw)
        · simpa only [tried', Function.update_of_ne hwv] using hinv w hw
      have ih_succ := ih _ hm_lt (insert v active) tried' hinv_succ rfl
      have ih_fail := ih _ hm_lt active tried' hinv_fail rfl
      have hv_compl : v ∈ activeᶜ := Finset.mem_compl.mpr hv_inact
      have hcompl_erase : activeᶜ.erase v = (insert v active)ᶜ := Finset.ext fun _ => by simp
      have hprod_split : ∏ w ∈ activeᶜ, C.survivalProb w (tried w) =
          C.survivalProb v (tried v) * ∏ w ∈ (insert v active)ᶜ, C.survivalProb w (tried' w) := by
        rw [← Finset.mul_prod_erase _ _ hv_compl, hcompl_erase]
        exact congrArg _ (Finset.prod_congr rfl fun w hw => by
          simp only [tried', Function.update_of_ne
            (fun h : w = v => Finset.mem_compl.mp (h ▸ hw) (Finset.mem_insert_self v active))])
      have hprod_fail : (∏ w ∈ activeᶜ, C.survivalProb w (tried w)) *
          (1 - C.prob v u (tried v)) = ∏ w ∈ activeᶜ, C.survivalProb w (tried' w) := by
        rw [hprod_split, mul_right_comm, ← C.survivalProb_insert v hu_untried, ← hcompl_erase,
          ← Finset.mul_prod_erase activeᶜ (fun w => C.survivalProb w (tried' w)) hv_compl]
        simp only [tried', Function.update_self]
      rw [cascadeProbFrom]
      simp only [hnext, huv_mem, ↓reduceDIte]
      change (∏ w ∈ activeᶜ, C.survivalProb w (tried w)) *
          (C.prob v u (tried v) * C.cascadeProbFrom nextEdge (insert v active) tried' A +
            (1 - C.prob v u (tried v)) * C.cascadeProbFrom nextEdge active tried' A) =
        F active tried
      rw [hstep active tried hinv u v hu_act hv_inact hadj hu_untried]
      change _ = C.prob v u (tried v) * C.survivalProb v (tried v) * F (insert v active) tried' +
          F active tried'
      rw [← ih_succ, ← ih_fail, ← hprod_fail, hprod_split]
      ring
    · have hemp := Finset.not_nonempty_iff_eq_empty.mp hne
      have htr_eq : ∀ w ∉ active, tried w = active ∩ inNeighbors G w := fun w hw =>
        Finset.Subset.antisymm (hinv w hw) fun u hu => by
          rcases Finset.mem_inter.mp hu with ⟨hu_act, hadj⟩
          by_contra hu_not
          have hmem : (u, w) ∈ untriedEdges G active tried :=
            (mem_untriedEdges (e := (u, w))).mpr ⟨hu_act, hw, mem_inNeighbors.mp hadj, hu_not⟩
          exact Finset.notMem_empty _ (hemp ▸ hmem)
      rw [cascadeProbFrom, (hvalid active tried).2 hemp, hbase active tried htr_eq]
      split_ifs <;> ring

/-- Structural recursion characterizing `C.activeSetProb nextEdge S A`: any state invariant
`F active tried` matching the terminal survival product when all active-to-inactive edges have been
tried and satisfying the one-step survival-weighted recurrence along each untried edge `(u, v)`
agrees with `C.activeSetProb nextEdge S A` at `(S, fun _ => ∅)`. -/
theorem activeSetProb_eq_of_step
    {nextEdge : Finset V → (V → Finset V) → Option (V × V)} (hvalid : ValidNextEdge G nextEdge)
    (S A : Finset V) (F : Finset V → (V → Finset V) → ℝ)
    (hbase : ∀ active tried, (∀ w ∉ active, tried w = active ∩ inNeighbors G w) →
      F active tried = if active = A then ∏ w ∈ activeᶜ, C.survivalProb w (tried w) else 0)
    (hstep : ∀ active tried, (∀ w ∉ active, tried w ⊆ active ∩ inNeighbors G w) →
      ∀ u v, u ∈ active → v ∉ active → G.Adj u v → u ∉ tried v →
        F active tried =
          C.prob v u (tried v) * C.survivalProb v (tried v) *
              F (insert v active) (Function.update tried v (insert u (tried v))) +
            F active (Function.update tried v (insert u (tried v)))) :
    C.activeSetProb nextEdge S A = F S (fun _ => ∅) := by
  have key := C.survivalProd_mul_cascadeProbFrom_eq hvalid A F hbase hstep S (fun _ => ∅)
    (fun _ _ => Finset.empty_subset _)
  rw [Finset.prod_eq_one fun w _ => C.survivalProb_empty w, one_mul] at key
  exact key

/-- **Equivalence of Order-Independent Cascade and General Threshold Models**
([KempeKleinbergTardos2005]; [Kleinberg2007], Section 24.3, pp. 620–621): under any valid
edge-attempt schedule `nextEdge`, the Cascade Model `C` produces the exact same probability
distribution over final active sets as `C.toGeneralThresholdModel`. -/
theorem activeSetProb_eq_toGeneralThresholdModel
    {nextEdge : Finset V → (V → Finset V) → Option (V × V)} (hvalid : ValidNextEdge G nextEdge)
    (S A : Finset V) :
    C.activeSetProb nextEdge S A = C.toGeneralThresholdModel.activeSetProb S A := by
  set M := C.toGeneralThresholdModel
  have h0 := C.activeSetProb_eq_of_step hvalid S A
    (fun active tried => (thresholdMeasure V).real (survEvent M active tried A))
    (fun active tried htr_eq => by
      have hfin_const : ∀ θ : V → ℝ, (∀ w ∉ active, M.thresholdFn w (tried w) < θ w) →
          M.thresholdFinal θ active = active := fun θ hsurv =>
        Finset.Subset.antisymm
          (M.thresholdFinal_subset_of_lt (Finset.Subset.refl active) fun w hw => by
            rw [← M.inNeighbors_congr w active, ← htr_eq w hw]
            exact hsurv w hw)
          (M.subset_thresholdFinal θ active)
      by_cases hA : active = A
      · subst hA
        have hset : survEvent M active tried active =
            univ.pi fun w => if w ∈ active then univ else Ioi (M.thresholdFn w (tried w)) := by
          ext θ
          simp only [survEvent, mem_ofPred_eq, mem_univ_pi]
          refine ⟨fun ⟨hsurv, _⟩ w => by by_cases hw : w ∈ active <;> simp [hw, hsurv], fun h => ?_⟩
          have hsurv : ∀ w ∉ active, M.thresholdFn w (tried w) < θ w := fun w hw => by
            simpa [hw] using h w
          exact ⟨hsurv, hfin_const θ hsurv⟩
        simp only [↓reduceIte]
        rw [hset, thresholdMeasure, measureReal_def, Measure.pi_pi,
          ENNReal.toReal_prod, ← Finset.prod_compl_mul_prod active,
          Finset.prod_eq_one (s := active) fun w hw => by simp [hw], mul_one]
        refine Finset.prod_congr rfl fun w hw => ?_
        have hwnot : w ∉ active := Finset.mem_compl.mp hw
        simp only [hwnot, ↓reduceIte, ← measureReal_def]
        rw [unitMeasure_real_Ioi (M.thresholdFn_nonneg w _) (M.thresholdFn_le_one w _)]
        simp only [M, toGeneralThresholdModel_thresholdFn, sub_sub_cancel]
      · have hemp_set : survEvent M active tried A = ∅ := Set.eq_empty_iff_forall_notMem.mpr
          fun θ ⟨hsurv, hfin⟩ => hA ((hfin_const θ hsurv).symm.trans hfin)
        simp [hA, hemp_set])
    (fun active tried hinv u v hu_act hv_inact hadj hu_untried => by
      let tried' := Function.update tried v (insert u (tried v))
      set g0 := M.thresholdFn v (tried v)
      set g1 := M.thresholdFn v (insert u (tried v))
      have hg_diff : C.prob v u (tried v) * C.survivalProb v (tried v) = g1 - g0 := by
        simp only [g0, g1, M, toGeneralThresholdModel_thresholdFn,
          C.survivalProb_insert v hu_untried]
        ring
      change (thresholdMeasure V).real (survEvent M active tried A) =
        C.prob v u (tried v) * C.survivalProb v (tried v) *
          (thresholdMeasure V).real (survEvent M (insert v active) tried' A) +
          (thresholdMeasure V).real (survEvent M active tried' A)
      rw [hg_diff]
      let E1 : Set (V → ℝ) := {θ ∈ survEvent M active tried A | θ v ≤ g1}
      let E2 : Set (V → ℝ) := survEvent M active tried' A
      have hE_union : survEvent M active tried A = E1 ∪ E2 := by
        ext θ
        simp only [E1, E2, survEvent, mem_union, mem_ofPred_eq]
        constructor
        · rintro ⟨hsurv, hfin⟩
          by_cases hle : θ v ≤ g1
          · exact Or.inl ⟨⟨hsurv, hfin⟩, hle⟩
          · refine Or.inr ⟨fun w hw => ?_, hfin⟩
            rcases eq_or_ne w v with rfl | hwv
            · simpa only [tried', Function.update_self] using not_le.mp hle
            · simpa only [tried', Function.update_of_ne hwv] using hsurv w hw
        · rintro (⟨⟨hsurv, hfin⟩, _⟩ | ⟨hsurv', hfin⟩)
          · exact ⟨hsurv, hfin⟩
          · refine ⟨fun w hw => ?_, hfin⟩
            rcases eq_or_ne w v with rfl | hwv
            · exact (M.monotone w (Finset.subset_insert u _)).trans_lt
                (by simpa only [tried', Function.update_self] using hsurv' w hw)
            · simpa only [tried', Function.update_of_ne hwv] using hsurv' w hw
      have hE_disj : Disjoint E1 E2 := Set.disjoint_left.mpr fun θ h1 h2 =>
        not_lt_of_ge h1.2 (by simpa only [tried', Function.update_self] using h2.1 v hv_inact)
      have hmE2 : MeasurableSet E2 := measurableSet_survEvent M active tried' A
      have hmE1 : MeasurableSet E1 :=
        (measurableSet_survEvent M active tried A).inter
          (measurableSet_Iic.preimage (measurable_pi_apply v))
      rw [hE_union, measureReal_union hE_disj hmE2]
      congr 1
      let S_succ := survEvent M (insert v active) tried' A
      have hS_indep : ∀ θ z, S_succ.indicator (fun _ => (1 : ℝ)) (Function.update θ v z) =
          S_succ.indicator (fun _ => (1 : ℝ)) θ := fun θ z => by
        have hmem_iff : Function.update θ v z ∈ S_succ ↔ θ ∈ S_succ := by
          simp only [S_succ, survEvent, mem_ofPred_eq]
          rw [M.thresholdFinal_congr_outside fun w hw =>
            Function.update_of_ne (fun h => hw (Finset.mem_insert.mpr (Or.inl h))) _ _]
          refine and_congr_left' (forall_congr' fun w => imp_congr_right fun hw => ?_)
          rw [Function.update_of_ne fun h => hw (Finset.mem_insert.mpr (Or.inl h))]
        by_cases hθ : θ ∈ S_succ <;> simp [hθ, hmem_iff]
      have hE1_eq : E1 = {θ | θ v ∈ Ioc g0 g1 ∧ θ ∈ S_succ} := by
        ext θ
        simp only [E1, S_succ, survEvent, mem_Ioc, mem_ofPred_eq]
        have hins_sub : insert u (tried v) ⊆ active :=
          Finset.insert_subset hu_act ((hinv v hv_inact).trans Finset.inter_subset_left)
        have hfin_ins_of_le : θ v ≤ g1 →
            M.thresholdFinal θ (insert v active) = M.thresholdFinal θ active := fun hle1 =>
          Finset.Subset.antisymm
            (calc M.thresholdFinal θ (insert v active)
                ⊆ M.thresholdFinal θ (M.thresholdStep θ active) :=
                  M.thresholdFinal_mono_seed θ (Finset.insert_subset
                    (M.mem_thresholdStep.mpr (Or.inr (hle1.trans (M.monotone v hins_sub))))
                    (M.subset_thresholdStep θ active))
              _ = (M.thresholdStep θ)^[Fintype.card V + 1] active := by
                  rw [GeneralThresholdModel.thresholdFinal, ← Function.iterate_succ_apply]
              _ = M.thresholdFinal θ active :=
                  M.thresholdStep_iterate_eq_thresholdFinal θ active (Nat.le_succ _))
            (M.thresholdFinal_mono_seed θ (Finset.subset_insert v active))
        constructor
        · rintro ⟨⟨hsurv, hfin⟩, hle1⟩
          refine ⟨⟨hsurv v hv_inact, hle1⟩, fun w hw => ?_, (hfin_ins_of_le hle1).trans hfin⟩
          rw [Finset.mem_insert, not_or] at hw
          simpa only [tried', Function.update_of_ne hw.1] using hsurv w hw.2
        · rintro ⟨⟨hgt0, hle1⟩, hsurv', hfin'⟩
          refine ⟨⟨fun w hw => ?_, (hfin_ins_of_le hle1).symm.trans hfin'⟩, hle1⟩
          rcases eq_or_ne w v with rfl | hwv
          · exact hgt0
          · simpa only [tried', Function.update_of_ne hwv] using
              hsurv' w (by simp [hwv, hw])
      have hmS : MeasurableSet S_succ := measurableSet_survEvent M (insert v active) tried' A
      let Φ : (V → ℝ) → ℝ → ℝ := fun θ z =>
        (Ioc g0 g1).indicator (fun _ => (1 : ℝ)) z * S_succ.indicator (fun _ => (1 : ℝ)) θ
      have hΦ_diag : (fun θ => Φ θ (θ v)) = E1.indicator (fun _ => (1 : ℝ)) := by
        ext θ
        rw [hE1_eq]
        by_cases h1 : θ v ∈ Ioc g0 g1 <;> by_cases h2 : θ ∈ S_succ <;>
          simp only [Φ, indicator, mem_ofPred_eq, h1, h2, and_self, and_false, false_and,
            ↓reduceIte, mul_one, mul_zero]
      have hcalc := MeasureTheory.integral_apply_eval_eq_integral_integral
        (fun _ : V => unitMeasure)
        (fun θ z => funext fun y => by simp only [Φ, hS_indep θ z])
        (hΦ_diag.symm ▸ (integrable_const (1 : ℝ)).indicator hmE1)
      change ∫ θ, Φ θ (θ v) ∂thresholdMeasure V =
        ∫ θ, ∫ z, Φ θ z ∂unitMeasure ∂thresholdMeasure V at hcalc
      rw [hΦ_diag, integral_indicator_const _ hmE1, smul_eq_mul, mul_one] at hcalc
      have hinner : ∀ θ, (∫ z, Φ θ z ∂unitMeasure) =
          (g1 - g0) * S_succ.indicator (fun _ => (1 : ℝ)) θ := fun θ => by
        simp only [Φ, integral_mul_const]
        rw [integral_indicator_const _ measurableSet_Ioc, smul_eq_mul, mul_one,
          unitMeasure_real_Ioc (M.thresholdFn_nonneg v _)
            (M.monotone v (Finset.subset_insert u _)) (M.thresholdFn_le_one v _)]
      simp_rw [hinner] at hcalc
      rwa [integral_const_mul, integral_indicator_const _ hmS, smul_eq_mul, mul_one] at hcalc)
  rw [h0, GeneralThresholdModel.activeSetProb]
  refine measureReal_congr ?_
  filter_upwards [ae_mem_Ioo_thresholdMeasure V] with θ hθ
  simp [survEvent, M.thresholdFn_empty, fun w => (hθ w).1]

/-- Schedule-invariance of the Order-Independent Cascade Model: any two valid edge-attempt
schedules induce identical final active-set distributions. -/
theorem activeSetProb_congr_schedule
    {nextEdge₁ nextEdge₂ : Finset V → (V → Finset V) → Option (V × V)}
    (hv₁ : ValidNextEdge G nextEdge₁) (hv₂ : ValidNextEdge G nextEdge₂)
    (S A : Finset V) :
    C.activeSetProb nextEdge₁ S A = C.activeSetProb nextEdge₂ S A := by
  rw [C.activeSetProb_eq_toGeneralThresholdModel hv₁,
    C.activeSetProb_eq_toGeneralThresholdModel hv₂]

/-- Expected influence of `C` equals the expected influence of `C.toGeneralThresholdModel`. -/
theorem influence_eq_toGeneralThresholdModel (S : Finset V) :
    C.influence S = C.toGeneralThresholdModel.influence S := by
  rw [influence, C.toGeneralThresholdModel.influence_eq_sum_activeSetProb]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [C.activeSetProb_eq_toGeneralThresholdModel validNextEdge_defaultNextEdge]

@[simp]
theorem influence_empty : C.influence ∅ = 0 := by
  rw [C.influence_eq_toGeneralThresholdModel, C.toGeneralThresholdModel.influence_empty]

theorem monotone_influence : Monotone C.influence := by
  intro A B hAB
  rw [C.influence_eq_toGeneralThresholdModel, C.influence_eq_toGeneralThresholdModel]
  exact C.toGeneralThresholdModel.monotone_influence hAB

end CascadeModel

/-- **Forward Equivalence (`GeneralThresholdModel → CascadeModel`)** ([KempeKleinbergTardos2005];
[Kleinberg2007], Section 24.3, pp. 620–621): translating `M : GeneralThresholdModel G` to
`M.toCascadeModel` preserves the final active-set distribution under every valid schedule. -/
theorem GeneralThresholdModel.activeSetProb_toCascadeModel
    {V : Type*} [DecidableEq V] [Fintype V] {G : Digraph V} [DecidableRel G.Adj]
    (M : GeneralThresholdModel G)
    {nextEdge : Finset V → (V → Finset V) → Option (V × V)}
    (hvalid : CascadeModel.ValidNextEdge G nextEdge) (S A : Finset V) :
    M.toCascadeModel.activeSetProb nextEdge S A = M.activeSetProb S A := by
  rw [M.toCascadeModel.activeSetProb_eq_toGeneralThresholdModel hvalid,
    M.toGeneralThresholdModel_toCascadeModel]

/-! ## Time-Layered DAG Reduction for Nonprogressive Processes -/

section TimeLayered

/-- `T`-step time-layered directed acyclic graph on `V × Fin (T + 1)`
([KempeKleinbergTardos2003]; [Kleinberg2007], Section 24.3, p. 622): copy `(u, t)` has a directed
edge to `(v, t + 1)` whenever `G.Adj u v`. -/
def timeLayeredDigraph {V : Type*} (G : Digraph V) (T : ℕ) :
    Cslib.LayeredDigraph (V × Fin (T + 1)) where
  Adj x y := (y.2 : ℕ) = (x.2 : ℕ) + 1 ∧ G.Adj x.1 y.1
  layer x := (x.2 : ℕ)
  layer_adj h := h.1

instance instDecidableRelTimeLayeredDigraph {V : Type*} (G : Digraph V) [DecidableRel G.Adj]
    (T : ℕ) : DecidableRel (timeLayeredDigraph G T).toDigraph.Adj :=
  fun x y => inferInstanceAs (Decidable ((y.2 : ℕ) = (x.2 : ℕ) + 1 ∧ G.Adj x.1 y.1))

/-- Embed an initial seed set `S : Finset V` into layer `0` of `V × Fin (T + 1)`. -/
def seedLayer0 {V : Type*} (T : ℕ) (S : Finset V) : Finset (V × Fin (T + 1)) :=
  S.map ⟨fun v => (v, 0), fun _ _ h => congrArg Prod.fst h⟩

@[simp]
theorem mem_seedLayer0 {V : Type*} {T : ℕ} {S : Finset V} {x : V × Fin (T + 1)} :
    x ∈ seedLayer0 T S ↔ x.2 = 0 ∧ x.1 ∈ S := by
  rcases x with ⟨v, t⟩
  rw [seedLayer0, Finset.mem_map]
  change (∃ u ∈ S, (u, (0 : Fin (T + 1))) = (v, t)) ↔ t = 0 ∧ v ∈ S
  simp [and_comm, eq_comm]

theorem seedLayer0_union {V : Type*} [DecidableEq V] (T : ℕ) (A B : Finset V) :
    seedLayer0 T (A ∪ B) = seedLayer0 T A ∪ seedLayer0 T B := by
  ext x
  simp only [Finset.mem_union, mem_seedLayer0]
  tauto

theorem seedLayer0_inter {V : Type*} [DecidableEq V] (T : ℕ) (A B : Finset V) :
    seedLayer0 T (A ∩ B) = seedLayer0 T A ∩ seedLayer0 T B := by
  ext x
  simp only [Finset.mem_inter, mem_seedLayer0]
  tauto

namespace GeneralThresholdModel

variable {V : Type*} [DecidableEq V] [Fintype V] {G : Digraph V} [DecidableRel G.Adj]
  (M : GeneralThresholdModel G)

/-- Lift a `GeneralThresholdModel` on `G` to a progressive `GeneralThresholdModel` on
`timeLayeredDigraph G T` ([Kleinberg2007], Section 24.3, p. 622): vertices at layer `0` have zero
threshold function, and `(v, t + 1)` evaluates `M.thresholdFn v` on `{u | (u, t) ∈ X}`. -/
def toTimeLayered (T : ℕ) : GeneralThresholdModel (timeLayeredDigraph G T).toDigraph where
  thresholdFn vt X :=
    if h0 : (vt.2 : ℕ) = 0 then 0
    else
      let prev : Fin (T + 1) := ⟨(vt.2 : ℕ) - 1, by omega⟩
      M.thresholdFn vt.1 (Finset.univ.filter fun u => (u, prev) ∈ X)
  thresholdFn_empty vt := by
    split_ifs
    · rfl
    · simp [M.thresholdFn_empty]
  thresholdFn_le_one vt X := by
    split_ifs
    · exact zero_le_one
    · exact M.thresholdFn_le_one _ _
  monotone vt A B hAB := by
    split_ifs
    · exact le_rfl
    · refine M.monotone vt.1 fun u hu => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      exact hAB hu
  inNeighbors_congr vt X := by
    split_ifs with h0
    · rfl
    · rw [← M.inNeighbors_congr vt.1 (Finset.univ.filter fun u =>
        (u, (⟨(vt.2 : ℕ) - 1, by omega⟩ : Fin (T + 1))) ∈ X)]
      refine congrArg (M.thresholdFn vt.1) ?_
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
        mem_inNeighbors]
      change ((u, _) ∈ X ∧ ((vt.2 : ℕ) = ((vt.2 : ℕ) - 1) + 1 ∧ G.Adj u vt.1)) ↔ _
      have hsucc : (vt.2 : ℕ) = (vt.2 : ℕ) - 1 + 1 := by omega
      exact ⟨fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, hsucc, h2⟩⟩

theorem toTimeLayered_thresholdFn (T : ℕ) (vt : V × Fin (T + 1))
    (X : Finset (V × Fin (T + 1))) :
    (M.toTimeLayered T).thresholdFn vt X =
      if h0 : (vt.2 : ℕ) = 0 then 0
      else
        M.thresholdFn vt.1
          (Finset.univ.filter fun u => (u, (⟨(vt.2 : ℕ) - 1, by omega⟩ : Fin (T + 1))) ∈ X) := by
  rfl

/-- `T`-step synchronous **nonprogressive** active set helper under threshold realizations
`θ : V × Fin (T + 1) → ℝ`. -/
private noncomputable def nonprogActiveAux {T : ℕ} (θ : V × Fin (T + 1) → ℝ) (S : Finset V) :
    ∀ k : ℕ, k ≤ T → Finset V
  | 0, _ => S
  | k + 1, hk =>
    let prev := nonprogActiveAux θ S k (Nat.le_of_succ_le hk)
    haveI := Classical.decPred fun v => θ (v, ⟨k + 1, Nat.lt_succ_of_le hk⟩) ≤ M.thresholdFn v prev
    Finset.univ.filter fun v => θ (v, ⟨k + 1, Nat.lt_succ_of_le hk⟩) ≤ M.thresholdFn v prev

/-- Nonprogressive active set at step `t : Fin (T + 1)`. -/
noncomputable def nonprogActive {T : ℕ} (θ : V × Fin (T + 1) → ℝ) (S : Finset V)
    (t : Fin (T + 1)) : Finset V :=
  M.nonprogActiveAux θ S t.val (Nat.le_of_lt_succ t.isLt)

@[simp]
theorem nonprogActive_zero {T : ℕ} (θ : V × Fin (T + 1) → ℝ) (S : Finset V) :
    M.nonprogActive θ S 0 = S := by
  rfl

theorem mem_nonprogActive_succ {T : ℕ} (θ : V × Fin (T + 1) → ℝ) (S : Finset V)
    {k : ℕ} (hk : k + 1 ≤ T) (v : V) :
    v ∈ M.nonprogActive θ S ⟨k + 1, Nat.lt_succ_of_le hk⟩ ↔
      θ (v, ⟨k + 1, Nat.lt_succ_of_le hk⟩) ≤
        M.thresholdFn v (M.nonprogActive θ S ⟨k, Nat.lt_succ_of_le (Nat.le_of_succ_le hk)⟩) := by
  simp [nonprogActive, nonprogActiveAux]

/-- **Time-Layered DAG Reduction** ([KempeKleinbergTardos2003]; [Kleinberg2007], Section 24.3,
p. 622): whenever layer-`0` thresholds are positive (`0 < θ (v, 0)`, which holds almost everywhere
under `thresholdMeasure`), vertex `(v, t)` is activated in the progressive process on
`timeLayeredDigraph G T` starting from `seedLayer0 T S` if and only if `v` is active at step `t`
of the nonprogressive process on `G`. -/
theorem mem_thresholdFinal_toTimeLayered_iff {T : ℕ} {θ : V × Fin (T + 1) → ℝ}
    (hθ0 : ∀ v, 0 < θ (v, 0)) (S : Finset V) (v : V) (t : Fin (T + 1)) :
    (v, t) ∈ (M.toTimeLayered T).thresholdFinal θ (seedLayer0 T S) ↔
      v ∈ M.nonprogActive θ S t := by
  let B : Finset (V × Fin (T + 1)) :=
    Finset.univ.filter fun x => x.1 ∈ M.nonprogActive θ S x.2
  suffices hEq : (M.toTimeLayered T).thresholdFinal θ (seedLayer0 T S) = B by
    simpa [B] using congrArg ((v, t) ∈ ·) hEq
  refine Finset.Subset.antisymm ?_ ?_
  · refine (M.toTimeLayered T).thresholdFinal_subset_of_lt
      (fun x hx => by
        rcases mem_seedLayer0.mp hx with ⟨hx0, hxS⟩
        simp [B, hx0, hxS])
      fun x hxnot => ?_
    rcases x with ⟨w, ⟨_ | k, hk⟩⟩
    · exact hθ0 w
    · simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hxnot
      have hk' : k + 1 ≤ T := Nat.le_of_lt_succ hk
      rw [M.mem_nonprogActive_succ θ S hk' w, not_le] at hxnot
      have hfilt : (Finset.univ.filter fun u =>
          (u, (⟨k, Nat.lt_succ_of_le (Nat.le_of_succ_le hk')⟩ : Fin (T + 1))) ∈ B) =
          M.nonprogActive θ S ⟨k, Nat.lt_succ_of_le (Nat.le_of_succ_le hk')⟩ := by
        ext u
        simp [B]
      simpa only [toTimeLayered, Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel, hfilt]
        using hxnot
  · intro ⟨w, ⟨k, hk⟩⟩ hB
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hB
    induction k generalizing w with
    | zero =>
      exact (M.toTimeLayered T).subset_thresholdFinal θ _ (mem_seedLayer0.mpr ⟨rfl, hB⟩)
    | succ k ih =>
      have hk' : k + 1 ≤ T := Nat.le_of_lt_succ hk
      rw [M.mem_nonprogActive_succ θ S hk' w] at hB
      have hsub : M.nonprogActive θ S ⟨k, Nat.lt_succ_of_le (Nat.le_of_succ_le hk')⟩ ⊆
          Finset.univ.filter fun u =>
            (u, (⟨k, Nat.lt_succ_of_le (Nat.le_of_succ_le hk')⟩ : Fin (T + 1))) ∈
              (M.toTimeLayered T).thresholdFinal θ (seedLayer0 T S) := fun u hu => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ih u (Nat.lt_trans (Nat.lt_succ_self k) hk) hu
      have hmem_step : (w, (⟨k + 1, hk⟩ : Fin (T + 1))) ∈
          (M.toTimeLayered T).thresholdStep θ
            ((M.toTimeLayered T).thresholdFinal θ (seedLayer0 T S)) :=
        (M.toTimeLayered T).mem_thresholdStep.mpr <| Or.inr <| by
          simpa only [toTimeLayered, Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel] using
            hB.trans (M.monotone w hsub)
      rwa [(M.toTimeLayered T).thresholdStep_thresholdFinal] at hmem_step

/-- Expected number of active vertices at step `t` of the `T`-step synchronous nonprogressive
threshold process starting from `S`. -/
noncomputable def nonprogStepInfluence (T : ℕ) (t : Fin (T + 1)) (S : Finset V) : ℝ :=
  ∫ θ, ((M.nonprogActive θ S t).card : ℝ) ∂thresholdMeasure (V × Fin (T + 1))

/-- Expected step-`t` nonprogressive influence on `G` equals the expected layer-`t` progressive
slice cardinality on `timeLayeredDigraph G T`. -/
theorem nonprogStepInfluence_eq_toTimeLayered (T : ℕ) (t : Fin (T + 1)) (S : Finset V) :
    M.nonprogStepInfluence T t S =
      ∫ θ,
        ((((M.toTimeLayered T).thresholdFinal θ (seedLayer0 T S)).filter (·.2 = t)).card : ℝ)
        ∂thresholdMeasure (V × Fin (T + 1)) := by
  refine integral_congr_ae ?_
  filter_upwards [ae_mem_Ioo_thresholdMeasure (V × Fin (T + 1))] with θ hθ
  congr 1
  let emb : V ↪ V × Fin (T + 1) := ⟨fun v => (v, t), fun _ _ h => congrArg Prod.fst h⟩
  have hemb : ∀ a, emb a = (a, t) := fun _ => rfl
  rw [← Finset.card_map emb]
  congr 2
  ext ⟨v, s⟩
  rcases eq_or_ne s t with rfl | hst
  · simp [hemb, M.mem_thresholdFinal_toTimeLayered_iff fun w => (hθ (w, 0)).1]
  · simp [hemb, hst, hst.symm]

end GeneralThresholdModel

end TimeLayered

end Cslib.GameTheory.Network
