/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.PartitionFunction
public import Mathlib.Data.Finset.Pi
import CslibFrontier.Foundations.Data.List.Boole
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Finite.List

/-!
# Algebraic laws and separator conditioning for weighted CSP partition functions

This module extends `Cslib.Logic.PL.CSP.partitionFunction` over finite domains and arbitrary
semirings with the algebraic identities needed by variable-elimination and separator-based
algorithms:

* `Cslib.Logic.PL.CSP.partitionFunctionOn`: partition function over a declared variable universe
  `declared : Finset V`, scaling by `|D| ^ (declared \ F.vars.toFinset).card` for isolated
  variables (`partitionFunctionOn_eq_card_pow_mul_partitionFunction`) and recovering `modelCountOn`
  at `0`/`1` weights (`partitionFunctionOn_boole`).
* Variable relabeling (`partitionFunctionOn_relabel_equiv`, `partitionFunction_relabel_equiv`,
  `partitionFunctionOn_denseRelabel`).
* Constraint conditioning (`PinnedRel`, `Constraint.restrictOn`, `restrictOn`): pinning a subset
  `S` of variables to an assignment yields a restricted CSP over free variables outside `S`, and
  summing conditioned partition functions recovers the global partition function
  (`partitionFunctionOn_eq_sum_restrictOn`).
* Disjoint-union product factorization (`partitionFunctionOn_append_of_disjoint`,
  `partitionFunction_append_of_disjoint`) and separator conditioning over commutative semirings: if
  every shared variable of `F₁` and `F₂` lies in `S`, conditioning on an assignment to `S`
  factorizes the conditioned partition function of `F₁ ++ F₂` as a product, and summing over
  assignments to `S` recovers the partition function of `F₁ ++ F₂`
  (`partitionFunctionOn_separator`, `partitionFunction_separator`).

## Main definitions

* `Cslib.Logic.PL.CSP.partitionFunctionOn`: declared-variable weighted partition function.
* `Cslib.Logic.PL.CSP.PinnedRel`, `Cslib.Logic.PL.CSP.Constraint.restrictOn`,
  `Cslib.Logic.PL.CSP.restrictOn`: syntactic conditioning of constraints under partial assignments.
* `Cslib.Logic.PL.CSP.pinnedWeight`: weight evaluator for conditioned constraints.

## Main results

* `Cslib.Logic.PL.CSP.partitionFunctionOn_eq_card_pow_mul_partitionFunction`: isolated variables
  contribute a multiplicative power of `|D|`.
* `Cslib.Logic.PL.CSP.partitionFunctionOn_relabel_equiv`: renaming bijection invariance.
* `Cslib.Logic.PL.CSP.partitionFunctionOn_eq_sum_restrictOn`: conditioning identity.
* `Cslib.Logic.PL.CSP.partitionFunctionOn_append_of_disjoint`: disjoint union multiplicativity.
* `Cslib.Logic.PL.CSP.partitionFunctionOn_separator`,
  `Cslib.Logic.PL.CSP.partitionFunction_separator`: separator conditioning factorization and sum
  recovery.
-/

public section

namespace Cslib.Logic.PL.CSP

section WeightLaws

variable {Rel V W D R : Type*}

/-- Weights are invariant under assignments agreeing on every occurring variable. -/
theorem weight_congr [Monoid R] {wt : Rel → List D → R} {F : CSP Rel V} {σ τ : V → D}
    (h : ∀ v ∈ F.vars, σ v = τ v) : F.weight wt σ = F.weight wt τ := by
  simp only [weight]
  congr 1
  exact List.map_congr_left fun c hc => by
    congr 1
    exact List.map_congr_left fun v hv => h v (List.mem_flatMap.mpr ⟨c, hc, hv⟩)

/-- The weight of the empty CSP is `1`. -/
@[simp]
theorem weight_nil [Monoid R] (wt : Rel → List D → R) (σ : V → D) :
    weight wt ([] : CSP Rel V) σ = 1 := by
  simp [weight]

/-- Weight of a single prepended constraint. -/
@[simp]
theorem weight_cons [Monoid R] (wt : Rel → List D → R) (c : Constraint Rel V) (F : CSP Rel V)
    (σ : V → D) : weight wt (c :: F) σ = wt c.rel (c.scope.map σ) * F.weight wt σ := by
  simp [weight]

/-- Weight multiplies over list append. -/
@[simp]
theorem weight_append [Monoid R] (wt : Rel → List D → R) (F₁ F₂ : CSP Rel V) (σ : V → D) :
    weight wt (F₁ ++ F₂) σ = F₁.weight wt σ * F₂.weight wt σ := by
  simp [weight]

/-- Relabeling variables precomposes the assignment. -/
@[simp]
theorem weight_relabel [Monoid R] (wt : Rel → List D → R) (f : V → W) (F : CSP Rel V)
    (σ : W → D) : (F.relabel f).weight wt σ = F.weight wt (σ ∘ f) := by
  simp [weight, relabel, Constraint.relabel, List.map_map, Function.comp_def]

end WeightLaws

section PartitionFunctionOn

variable {Rel V W D R : Type*}

/-- Weighted partition function of `F` over a declared variable set `declared` (extending
assignments outside `declared` by `default`). -/
@[expose] def partitionFunctionOn [Semiring R] [DecidableEq V] [Fintype D] [Inhabited D]
    (wt : Rel → List D → R) (F : CSP Rel V) (declared : Finset V) : R :=
  ∑ σ : declared → D, F.weight wt fun v => if h : v ∈ declared then σ ⟨v, h⟩ else default

/-- The occurring-variable partition function agrees with `partitionFunctionOn` on
`F.vars.toFinset`. -/
theorem partitionFunction_eq_partitionFunctionOn [Semiring R] [DecidableEq V] [Fintype D]
    [Inhabited D] (wt : Rel → List D → R) (F : CSP Rel V) :
    F.partitionFunction wt = F.partitionFunctionOn wt F.vars.toFinset := rfl

/-- Over `ℕ` with `0`/`1` weights, `partitionFunctionOn` recovers `modelCountOn`. -/
theorem partitionFunctionOn_boole [DecidableEq V] [Fintype D] [Inhabited D]
    (sem : Rel → List D → Bool) (F : CSP Rel V) (declared : Finset V) :
    F.partitionFunctionOn (fun r w => if sem r w then (1 : ℕ) else 0) declared =
      F.modelCountOn sem declared := by
  rw [partitionFunctionOn, modelCountOn, Finset.card_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [weight, List.prod_map_boole]
  refine if_congr ?_ rfl rfl
  simp only [CSP.eval, Constraint.eval, List.all_eq_true]

/-- Semiring homomorphisms commute with `partitionFunctionOn`. -/
theorem map_partitionFunctionOn {S : Type*} [Semiring R] [Semiring S] [DecidableEq V]
    [Fintype D] [Inhabited D] (f : R →+* S) (wt : Rel → List D → R) (F : CSP Rel V)
    (declared : Finset V) :
    f (F.partitionFunctionOn wt declared) =
      F.partitionFunctionOn (fun r w => f (wt r w)) declared := by
  simp only [partitionFunctionOn, map_sum, weight, map_list_prod, List.map_map, Function.comp_def]

/-- The partition function of the empty instance over `declared` counts all `D`-assignments. -/
theorem partitionFunctionOn_nil [Semiring R] [DecidableEq V] [Fintype D] [Inhabited D]
    (wt : Rel → List D → R) (declared : Finset V) :
    partitionFunctionOn wt ([] : CSP Rel V) declared = (Fintype.card D : R) ^ declared.card := by
  simp only [partitionFunctionOn, weight_nil, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_coe, nsmul_eq_mul, mul_one, Nat.cast_pow]

/-- Prepending a constraint with empty scope scales `partitionFunctionOn` by its constant
weight. -/
theorem partitionFunctionOn_cons_nil [Semiring R] [DecidableEq V] [Fintype D] [Inhabited D]
    (wt : Rel → List D → R) (r : Rel) (F : CSP Rel V) (declared : Finset V) :
    partitionFunctionOn wt (⟨r, []⟩ :: F) declared =
      wt r [] * F.partitionFunctionOn wt declared := by
  simp only [partitionFunctionOn, weight_cons, List.map_nil, Finset.mul_sum]

/-- Split assignments on `T` into assignments on `S ⊆ T` and `T \ S`, derived from
`Equiv.piFinsetUnion` along `S ∪ (T \ S) = T`. -/
def sdiffPiEquiv {V D : Type*} [DecidableEq V] {S T : Finset V} (hST : S ⊆ T) :
    (T → D) ≃ (S → D) × ((T \ S : Finset V) → D) :=
  ((Equiv.piFinsetUnion (fun _ => D) (disjoint_sdiff_self_right (x := S) (y := T))).trans
    (Equiv.piCongrLeft' (fun _ => D)
      (Equiv.subtypeEquivRight fun v => by
        rw [Finset.mem_union, ← Finset.mem_coe, ← Finset.mem_coe, ← Finset.mem_coe,
          ← Set.mem_union, ← Finset.coe_union, Finset.union_sdiff_of_subset hST]))).symm

@[simp]
theorem sdiffPiEquiv_symm_apply_left {V D : Type*} [DecidableEq V] {S T : Finset V}
    (hST : S ⊆ T) (p : (S → D) × ((T \ S : Finset V) → D)) {v : V}
    (hvS : v ∈ S) (hvT : v ∈ T) :
    (sdiffPiEquiv hST).symm p ⟨v, hvT⟩ = p.1 ⟨v, hvS⟩ := by
  simp only [sdiffPiEquiv, Equiv.symm_symm, Equiv.trans_apply, Equiv.piCongrLeft'_apply,
    Equiv.subtypeEquivRight_symm_apply]
  exact Equiv.piFinsetUnion_left (fun _ => D) disjoint_sdiff_self_right hvS _

@[simp]
theorem sdiffPiEquiv_symm_apply_right {V D : Type*} [DecidableEq V] {S T : Finset V}
    (hST : S ⊆ T) (p : (S → D) × ((T \ S : Finset V) → D)) {v : V}
    (hvRest : v ∈ T \ S) (hvT : v ∈ T) :
    (sdiffPiEquiv hST).symm p ⟨v, hvT⟩ = p.2 ⟨v, hvRest⟩ := by
  simp only [sdiffPiEquiv, Equiv.symm_symm, Equiv.trans_apply, Equiv.piCongrLeft'_apply,
    Equiv.subtypeEquivRight_symm_apply]
  exact Equiv.piFinsetUnion_right (fun _ => D) disjoint_sdiff_self_right hvRest _

private theorem partitionFunctionOn_split [Semiring R] [DecidableEq V] [Fintype D] [Inhabited D]
    (wt : Rel → List D → R) (F : CSP Rel V) {S T : Finset V} (hST : S ⊆ T) :
    F.partitionFunctionOn wt T =
      ∑ p : (S → D) × ((T \ S : Finset V) → D),
        F.weight wt (fun v =>
          if hv : v ∈ S then p.1 ⟨v, hv⟩
          else if hrest : v ∈ T \ S then p.2 ⟨v, hrest⟩
          else default) := by
  rw [partitionFunctionOn]
  refine (Fintype.sum_equiv (sdiffPiEquiv (D := D) hST).symm _ _ fun p => ?_).symm
  refine weight_congr fun v _ => ?_
  by_cases hvS : v ∈ S
  · simp [hvS, hST hvS]
  · by_cases hvT : v ∈ T
    · simp [hvS, hvT, Finset.mem_sdiff.mpr ⟨hvT, hvS⟩]
    · simp [hvS, hvT]

/-- Enlarging `declared` multiplies `partitionFunctionOn` by `|D| ^ (T \ S).card` whenever all
occurring variables already lie in `S`. -/
theorem partitionFunctionOn_eq_card_pow_mul_of_subset [Semiring R] [DecidableEq V] [Fintype D]
    [Inhabited D] (wt : Rel → List D → R) {F : CSP Rel V} {S T : Finset V}
    (hvars : F.vars.toFinset ⊆ S) (hST : S ⊆ T) :
    F.partitionFunctionOn wt T =
      ((Fintype.card D : R) ^ (T \ S).card) * F.partitionFunctionOn wt S := by
  rw [partitionFunctionOn_split wt F hST, partitionFunctionOn]
  have hcongr : (∑ p : (S → D) × ((T \ S : Finset V) → D),
      F.weight wt fun v => if hv : v ∈ S then p.1 ⟨v, hv⟩
        else if hrest : v ∈ T \ S then p.2 ⟨v, hrest⟩ else default) =
      ∑ p : (S → D) × ((T \ S : Finset V) → D),
        F.weight wt fun v => if h : v ∈ S then p.1 ⟨v, h⟩ else default :=
    Finset.sum_congr rfl fun p _ => weight_congr fun v hv => by
      simp [hvars (List.mem_toFinset.mpr hv)]
  rw [hcongr, Fintype.sum_prod_type_right]
  simp [Finset.sum_const, nsmul_eq_mul, Nat.cast_pow]

/-- Over a declared set containing all occurring variables, isolated variables contribute a factor
of `|D| ^ (declared \ F.vars.toFinset).card`. -/
theorem partitionFunctionOn_eq_card_pow_mul_partitionFunction [Semiring R] [DecidableEq V]
    [Fintype D] [Inhabited D] (wt : Rel → List D → R) {F : CSP Rel V} {declared : Finset V}
    (hvars : F.vars.toFinset ⊆ declared) :
    F.partitionFunctionOn wt declared =
      ((Fintype.card D : R) ^ (declared \ F.vars.toFinset).card) * F.partitionFunction wt := by
  rw [partitionFunction_eq_partitionFunctionOn]
  exact partitionFunctionOn_eq_card_pow_mul_of_subset wt Finset.Subset.rfl hvars

/-- Variable renaming via an equivalence preserves `partitionFunctionOn`. -/
theorem partitionFunctionOn_relabel_equiv [Semiring R] [DecidableEq V] [DecidableEq W]
    [Fintype D] [Inhabited D] (wt : Rel → List D → R) (e : V ≃ W) (F : CSP Rel V)
    (declared : Finset V) :
    (F.relabel e).partitionFunctionOn wt (declared.map e.toEmbedding) =
      F.partitionFunctionOn wt declared := by
  let eDom : declared ≃ declared.map e.toEmbedding :=
    { toFun := fun v => ⟨e v.1, Finset.mem_map.mpr ⟨v.1, v.2, rfl⟩⟩
      invFun := fun w => ⟨e.symm w.1, by
        rcases Finset.mem_map.mp w.2 with ⟨v, hv, hvw⟩
        simpa [← hvw] using hv⟩
      left_inv := fun v => Subtype.ext (e.symm_apply_apply v.1)
      right_inv := fun w => Subtype.ext (e.apply_symm_apply w.1) }
  let eAssign : (declared.map e.toEmbedding → D) ≃ (declared → D) :=
    Equiv.piCongrLeft' (fun _ => D) eDom.symm
  rw [partitionFunctionOn, partitionFunctionOn]
  refine Fintype.sum_equiv eAssign _ _ fun σ => ?_
  rw [weight_relabel]
  refine weight_congr fun v _ => ?_
  by_cases hv : v ∈ declared
  · have hev : e v ∈ declared.map e.toEmbedding := Finset.mem_map.mpr ⟨v, hv, rfl⟩
    simp only [Function.comp_def, hv, hev, dite_true, eAssign]
    simp [eDom]
  · simp [hv]

/-- Variable renaming via an equivalence preserves `partitionFunction`. -/
theorem partitionFunction_relabel_equiv [Semiring R] [DecidableEq V] [DecidableEq W]
    [Fintype D] [Inhabited D] (wt : Rel → List D → R) (e : V ≃ W) (F : CSP Rel V) :
    (F.relabel e).partitionFunction wt = F.partitionFunction wt := by
  have hvars : (F.relabel e).vars.toFinset = F.vars.toFinset.map e.toEmbedding := by
    ext w
    simp only [Finset.mem_map, Equiv.coe_toEmbedding, List.mem_toFinset, vars, relabel,
      Constraint.relabel, List.mem_flatMap, List.mem_map]
    exact ⟨fun ⟨_, ⟨c, hc, rfl⟩, hw⟩ =>
        let ⟨v, hv, hvw⟩ := List.mem_map.mp hw; ⟨v, ⟨c, hc, hv⟩, hvw⟩,
      fun ⟨v, ⟨c, hc, hv⟩, hvw⟩ => ⟨_, ⟨c, hc, rfl⟩, List.mem_map.mpr ⟨v, hv, hvw⟩⟩⟩
  rw [partitionFunction_eq_partitionFunctionOn, hvars]
  exact partitionFunctionOn_relabel_equiv wt e F F.vars.toFinset

/-- Dense variable relabeling preserves `partitionFunctionOn` on `Finset.range F.numVars` and hence
equals `F.partitionFunction wt`. -/
theorem partitionFunctionOn_denseRelabel [Semiring R] [DecidableEq V] [Fintype D] [Inhabited D]
    (wt : Rel → List D → R) (F : CSP Rel V) :
    F.denseRelabel.partitionFunctionOn wt (Finset.range F.numVars) = F.partitionFunction wt := by
  let S := F.vars.toFinset
  let Rng := Finset.range F.numVars
  have hmem (v : V) (hv : v ∈ S) : F.distinctVars.idxOf v ∈ Rng := by
    rw [Finset.mem_range, ← length_distinctVars]
    exact List.idxOf_lt_length_iff.mpr (mem_distinctVars.mpr (List.mem_toFinset.mp hv))
  let eVar : S ≃ Rng := Equiv.ofBijective (fun v => ⟨F.distinctVars.idxOf v.1, hmem v.1 v.2⟩)
    ⟨fun v w h => Subtype.ext ((List.idxOf_inj
        (mem_distinctVars.mpr (List.mem_toFinset.mp v.2))).mp (Subtype.mk.inj h)),
     fun i => by
       have hi' : i.1 ∈ F.denseRelabel.vars.toFinset := by
         simpa only [vars_denseRelabel_toFinset, Rng] using i.2
       simp only [denseRelabel, vars_relabel, List.mem_toFinset, List.mem_map] at hi'
       obtain ⟨v, hv, hvi⟩ := hi'
       exact ⟨⟨v, List.mem_toFinset.mpr hv⟩, Subtype.ext hvi⟩⟩
  let eAssign : (Rng → D) ≃ (S → D) := Equiv.piCongrLeft' (fun _ => D) eVar.symm
  rw [partitionFunctionOn, partitionFunction_eq_partitionFunctionOn, partitionFunctionOn]
  refine Fintype.sum_equiv eAssign _ _ fun σ => ?_
  rw [denseRelabel, weight_relabel]
  refine weight_congr fun v hv => ?_
  have hvS : v ∈ S := List.mem_toFinset.mpr hv
  dsimp only [Function.comp_apply]
  rw [dite_eq_left (hmem v hvS), dite_eq_left hvS]
  simp only [eAssign, Equiv.piCongrLeft'_apply, Equiv.symm_symm]
  rfl

end PartitionFunctionOn

section Conditioning

variable {Rel V D R : Type*}

/-- A relation symbol paired with a partial-assignment template specifying which positions of the
original constraint scope were pinned (`some d`) or kept as free variables (`none`). -/
structure PinnedRel (Rel D : Type*) where
  /-- Underlying relation symbol. -/
  rel : Rel
  /-- Pattern of pinned domain values and remaining free slots. -/
  template : List (Option D)
  deriving DecidableEq, Repr

/-- Merge free argument values into the `none` slots of a `template`. -/
@[expose] def fillTemplate : List (Option D) → List D → List D
  | [], _ => []
  | some d :: tmpl, xs => d :: fillTemplate tmpl xs
  | none :: tmpl, [] => fillTemplate tmpl []
  | none :: tmpl, x :: xs => x :: fillTemplate tmpl xs

/-- Weight evaluator for conditioned constraints. -/
@[expose] def pinnedWeight (wt : Rel → List D → R) (pr : PinnedRel Rel D) (xs : List D) : R :=
  wt pr.rel (fillTemplate pr.template xs)

/-- `fillTemplate` over a mapped partial template recovers pointwise lookup. -/
private theorem fillTemplate_map_ite [DecidableEq V] (S : Finset V) (α σ : V → D) :
    ∀ vs : List V,
      fillTemplate (vs.map fun v => if v ∈ S then some (α v) else none)
        ((vs.filter fun v => decide (v ∉ S)).map σ) =
      vs.map fun v => if v ∈ S then α v else σ v
  | [] => rfl
  | v :: vs => by
    by_cases hv : v ∈ S <;>
      simp only [List.map_cons, List.filter_cons, hv, not_true_eq_false, not_false_eq_true,
        decide_false, decide_true, Bool.false_eq_true, ↓reduceIte, fillTemplate,
        fillTemplate_map_ite S α σ vs]

/-- Condition one constraint by pinning all variables in `S` to `α`. -/
@[expose] def Constraint.restrictOn [DecidableEq V] (S : Finset V) (α : V → D)
    (c : Constraint Rel V) : Constraint (PinnedRel Rel D) V :=
  ⟨⟨c.rel, c.scope.map fun v => if v ∈ S then some (α v) else none⟩,
    c.scope.filter fun v => decide (v ∉ S)⟩

/-- Condition every constraint in `F` by pinning variables in `S` to `α`. -/
@[expose] def restrictOn [DecidableEq V] (S : Finset V) (α : V → D) (F : CSP Rel V) :
    CSP (PinnedRel Rel D) V :=
  F.map (Constraint.restrictOn S α)

/-- Restricting over append maps cleanly across `F₁ ++ F₂`. -/
@[simp]
theorem restrictOn_append [DecidableEq V] (S : Finset V) (α : V → D) (F₁ F₂ : CSP Rel V) :
    restrictOn S α (F₁ ++ F₂) = F₁.restrictOn S α ++ F₂.restrictOn S α := by
  simp [restrictOn]

/-- Variables remaining in a restricted CSP are exactly the variables outside `S`. -/
theorem mem_vars_restrictOn [DecidableEq V] (S : Finset V) (α : V → D) (F : CSP Rel V) (v : V) :
    v ∈ (F.restrictOn S α).vars ↔ v ∈ F.vars ∧ v ∉ S := by
  simp only [restrictOn, vars, List.mem_flatMap, List.mem_map, Constraint.restrictOn]
  exact ⟨fun ⟨_, ⟨c, hc, rfl⟩, hv⟩ =>
      let ⟨hvc, hvS⟩ := List.mem_filter.mp hv; ⟨⟨c, hc, hvc⟩, of_decide_eq_true hvS⟩,
    fun ⟨⟨c, hc, hvc⟩, hvS⟩ =>
      ⟨_, ⟨c, hc, rfl⟩, List.mem_filter.mpr ⟨hvc, decide_eq_true hvS⟩⟩⟩

/-- Occurring variables of `F.restrictOn S α` equal `F.vars.toFinset \ S`. -/
@[simp]
theorem vars_restrictOn [DecidableEq V] (S : Finset V) (α : V → D) (F : CSP Rel V) :
    (F.restrictOn S α).vars.toFinset = F.vars.toFinset \ S := by
  ext v
  simp [mem_vars_restrictOn]

/-- Weight of a restricted CSP agrees with weight of the combined assignment. -/
theorem weight_restrictOn [Monoid R] [DecidableEq V] (wt : Rel → List D → R) (S : Finset V)
    (α σ : V → D) (F : CSP Rel V) :
    (F.restrictOn S α).weight (pinnedWeight wt) σ =
      F.weight wt (fun v => if v ∈ S then α v else σ v) := by
  simp only [weight, restrictOn, List.map_map]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  simp only [Function.comp_def, Constraint.restrictOn, pinnedWeight]
  rw [fillTemplate_map_ite]

/-- Conditioning on a subset `S ⊆ declared` partitions the sum over `declared → D` into an outer
sum over `S → D` and inner conditioned partition functions on `declared \ S`. -/
theorem partitionFunctionOn_eq_sum_restrictOn [Semiring R] [DecidableEq V] [Fintype D]
    [Inhabited D] (wt : Rel → List D → R) (F : CSP Rel V) {S declared : Finset V}
    (hS : S ⊆ declared) :
    F.partitionFunctionOn wt declared =
      ∑ α : S → D,
        (F.restrictOn S (fun v => if h : v ∈ S then α ⟨v, h⟩ else default)).partitionFunctionOn
          (pinnedWeight wt) (declared \ S) := by
  rw [partitionFunctionOn_split wt F hS, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [partitionFunctionOn]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [weight_restrictOn]
  congr 1
  exact funext fun v => by by_cases hv : v ∈ S <;> simp [hv]

end Conditioning

section DisjointAndSeparator

variable {Rel V D R : Type*}

/-- Product factorization of disjoint components over a commutative semiring. -/
theorem partitionFunctionOn_append_of_disjoint [CommSemiring R] [DecidableEq V] [Fintype D]
    [Inhabited D] (wt : Rel → List D → R) {F₁ F₂ : CSP Rel V} {d₁ d₂ : Finset V}
    (hdisj : Disjoint d₁ d₂) (h₁ : F₁.vars.toFinset ⊆ d₁) (h₂ : F₂.vars.toFinset ⊆ d₂) :
    partitionFunctionOn wt (F₁ ++ F₂) (d₁ ∪ d₂) =
      F₁.partitionFunctionOn wt d₁ * F₂.partitionFunctionOn wt d₂ := by
  rw [partitionFunctionOn, partitionFunctionOn, partitionFunctionOn, Finset.sum_mul_sum]
  let e := Equiv.piFinsetUnion (fun _ => D) hdisj
  rw [← Fintype.sum_equiv e _
      (fun σ => weight wt (F₁ ++ F₂) fun v => if h : v ∈ d₁ ∪ d₂ then σ ⟨v, h⟩ else default)
      (fun _ => rfl),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ₁ _ => Finset.sum_congr rfl fun σ₂ _ => ?_
  rw [weight_append]
  congr 1
  · refine weight_congr fun v hv => ?_
    have hv₁ := h₁ (List.mem_toFinset.mpr hv)
    simpa [e, hv₁, Finset.mem_union_left d₂ hv₁] using
      Equiv.piFinsetUnion_left (fun _ => D) hdisj hv₁ (Finset.mem_union_left d₂ hv₁)
  · refine weight_congr fun v hv => ?_
    have hv₂ := h₂ (List.mem_toFinset.mpr hv)
    simpa [e, hv₂, Finset.mem_union_right d₁ hv₂] using
      Equiv.piFinsetUnion_right (fun _ => D) hdisj hv₂ (Finset.mem_union_right d₁ hv₂)

/-- Disjoint occurring variable sets yield multiplicative partition functions. -/
theorem partitionFunction_append_of_disjoint [CommSemiring R] [DecidableEq V] [Fintype D]
    [Inhabited D] (wt : Rel → List D → R) {F₁ F₂ : CSP Rel V}
    (hdisj : Disjoint F₁.vars.toFinset F₂.vars.toFinset) :
    partitionFunction wt (F₁ ++ F₂) = F₁.partitionFunction wt * F₂.partitionFunction wt := by
  have hvars : (vars (F₁ ++ F₂)).toFinset = F₁.vars.toFinset ∪ F₂.vars.toFinset := by
    ext v; simp [vars]
  rw [partitionFunction_eq_partitionFunctionOn, hvars, partitionFunction_eq_partitionFunctionOn,
    partitionFunction_eq_partitionFunctionOn]
  exact partitionFunctionOn_append_of_disjoint wt hdisj Finset.Subset.rfl Finset.Subset.rfl

/-- Conditioning on a separator `S` makes the conditioned partition functions of the two
components variable-disjoint, so the conditioned partition function factorizes as a product. -/
theorem restrictOn_append_partitionFunction_of_separator [CommSemiring R] [DecidableEq V]
    [Fintype D] [Inhabited D] (wt : Rel → List D → R) {S : Finset V} {F₁ F₂ : CSP Rel V}
    (hsep : F₁.vars.toFinset ∩ F₂.vars.toFinset ⊆ S) (α : V → D) :
    (restrictOn S α (F₁ ++ F₂)).partitionFunction (pinnedWeight wt) =
      (F₁.restrictOn S α).partitionFunction (pinnedWeight wt) *
        (F₂.restrictOn S α).partitionFunction (pinnedWeight wt) := by
  have hdisj : Disjoint (F₁.restrictOn S α).vars.toFinset (F₂.restrictOn S α).vars.toFinset := by
    rw [vars_restrictOn, vars_restrictOn, Finset.disjoint_left]
    intro v hv₁ hv₂
    rw [Finset.mem_sdiff] at hv₁ hv₂
    exact hv₁.2 (hsep (Finset.mem_inter.mpr ⟨hv₁.1, hv₂.1⟩))
  rw [restrictOn_append]
  exact partitionFunction_append_of_disjoint (pinnedWeight wt) hdisj

/-- General separator conditioning over declared variables: if `S ⊆ declared` contains all
shared variables of `F₁` and `F₂`, and `d₁ ∪ d₂ = declared \ S` splits the remaining declared
variables around `F₁` and `F₂`, then `partitionFunctionOn wt (F₁ ++ F₂) declared` is the sum over
assignments `α : S → D` of the product of conditioned component partition functions. -/
theorem partitionFunctionOn_separator [CommSemiring R] [DecidableEq V] [Fintype D] [Inhabited D]
    (wt : Rel → List D → R) {S d₁ d₂ declared : Finset V} {F₁ F₂ : CSP Rel V}
    (hS : S ⊆ declared) (hpart : d₁ ∪ d₂ = declared \ S) (hdisj : Disjoint d₁ d₂)
    (h₁ : F₁.vars.toFinset \ S ⊆ d₁) (h₂ : F₂.vars.toFinset \ S ⊆ d₂) :
    partitionFunctionOn wt (F₁ ++ F₂) declared =
      ∑ α : S → D,
        let ext : V → D := fun v => if h : v ∈ S then α ⟨v, h⟩ else default
        (F₁.restrictOn S ext).partitionFunctionOn (pinnedWeight wt) d₁ *
          (F₂.restrictOn S ext).partitionFunctionOn (pinnedWeight wt) d₂ := by
  rw [partitionFunctionOn_eq_sum_restrictOn wt (F₁ ++ F₂) hS]
  refine Finset.sum_congr rfl fun α _ => ?_
  dsimp only
  rw [← hpart, restrictOn_append]
  refine partitionFunctionOn_append_of_disjoint (pinnedWeight wt) hdisj ?_ ?_
  · rwa [vars_restrictOn]
  · rwa [vars_restrictOn]

/-- Separator conditioning on occurring variables: whenever `S ⊆ (F₁ ++ F₂).vars.toFinset`
separates `F₁` and `F₂` (`F₁.vars.toFinset ∩ F₂.vars.toFinset ⊆ S`), summing the products of the
conditioned component partition functions over `S → D` recovers
`partitionFunction wt (F₁ ++ F₂)`. -/
theorem partitionFunction_separator [CommSemiring R] [DecidableEq V] [Fintype D] [Inhabited D]
    (wt : Rel → List D → R) {S : Finset V} {F₁ F₂ : CSP Rel V}
    (hsep : F₁.vars.toFinset ∩ F₂.vars.toFinset ⊆ S)
    (hS : S ⊆ (vars (F₁ ++ F₂)).toFinset) :
    partitionFunction wt (F₁ ++ F₂) =
      ∑ α : S → D,
        let ext : V → D := fun v => if h : v ∈ S then α ⟨v, h⟩ else default
        (F₁.restrictOn S ext).partitionFunction (pinnedWeight wt) *
          (F₂.restrictOn S ext).partitionFunction (pinnedWeight wt) := by
  have hpart :
      (F₁.vars.toFinset \ S) ∪ (F₂.vars.toFinset \ S) = (vars (F₁ ++ F₂)).toFinset \ S := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset, vars, List.flatMap_append,
      List.mem_append]
    tauto
  have hdisj : Disjoint (F₁.vars.toFinset \ S) (F₂.vars.toFinset \ S) :=
    Finset.disjoint_left.mpr fun _ hv₁ hv₂ =>
      (Finset.mem_sdiff.mp hv₁).2
        (hsep (Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hv₁).1, (Finset.mem_sdiff.mp hv₂).1⟩))
  rw [partitionFunction_eq_partitionFunctionOn,
    partitionFunctionOn_separator wt hS hpart hdisj Finset.Subset.rfl Finset.Subset.rfl]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp [partitionFunction_eq_partitionFunctionOn]

end DisjointAndSeparator

end Cslib.Logic.PL.CSP
