/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Classes.Promise.Reduction
public import CslibFrontier.Computability.Complexity.Problems.SetCover
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD
import Mathlib.Data.Rat.Init

/-!
# Approximation-preserving reductions and Set Cover gap problems

General minimization-problem interface (`MinOptProblem`), approximation guarantees (`IsApprox`),
approximation-preserving reductions (`ApproxPreservingReducible`), and the gap promise problems for
unweighted and weighted Set Cover (`GapSetCover`, `GapWeightedSetCover`), formulated for this
library's multi-tape polynomial-time model.

An approximation-preserving reduction between minimization problems maps instances in polynomial
time and lifts feasible solutions back in polynomial time while controlling the blowup of the
approximation ratio (`ApproxPreservingReducible.comp_isApprox`). This directly yields a reduction
from unweighted Set Cover to weighted Set Cover by assigning unit weights
(`approxPreservingReducible_setCover_weightedSetCover`,
`polyTimeReducible_GapSetCover_GapWeightedSetCover`).

Hardness of `GapSetCover` at gap `r` rules out polynomial-time `ρ`-approximation algorithms for
every `0 ≤ ρ < r` unless `P = NP` (`P_eq_NP_of_setCover_approx`,
`P_eq_NP_of_weightedSetCover_approx`), using rational thresholds between `ρ` and `r` so the
induced decider runs in native multi-tape polynomial time.

## Main definitions

* `Cslib.Complexity.MinOptProblem`: minimization problems with induced gap promise problems
  (`gapProblem`) and approximation ratios (`IsApprox`).
* `Cslib.Complexity.ApproxPreservingReducible`: polynomial-time approximation-preserving reductions
  between minimization problems, closed under identity and composition.
* `Cslib.Complexity.minSetCover`, `Cslib.Complexity.minWeightedSetCover`: optimization-problem
  views of unweighted and weighted Set Cover.
* `Cslib.Complexity.GapSetCoverFn`, `Cslib.Complexity.GapSetCover`,
  `Cslib.Complexity.GapWeightedSetCoverFn`, `Cslib.Complexity.GapWeightedSetCover`: Set Cover
  gap promise problems on coverable instances.

## Main results

* `Cslib.Complexity.ApproxPreservingReducible.refl`,
  `Cslib.Complexity.ApproxPreservingReducible.trans`,
  `Cslib.Complexity.ApproxPreservingReducible.comp_isApprox`: composition and algorithm transfer.
* `Cslib.Complexity.approxPreservingReducible_setCover_weightedSetCover`,
  `Cslib.Complexity.polyTimeReducible_GapSetCover_GapWeightedSetCover`: unweighted Set Cover
  reduces to weighted Set Cover preserving approximation and gap.
* `Cslib.Complexity.P_eq_NP_of_setCover_approx`,
  `Cslib.Complexity.P_eq_NP_of_weightedSetCover_approx`: `ρ`-approximation with `ρ < r` implies
  `P = NP` whenever `GapSetCover r` (resp. `GapWeightedSetCover r`) is `NP`-hard.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

/-! ### Optimization problems and approximation-preserving reductions -/

/-- A combinatorial minimization problem over valid instances `IsValid`, feasible solutions
`Feasible`, real cost `cost`, and attained optimum `opt`. -/
structure MinOptProblem (Instance Solution : Type) where
  /-- Predicate picking out well-formed/feasible instances. -/
  IsValid : Instance → Prop
  /-- Feasible solutions for a given instance. -/
  Feasible : Instance → Solution → Prop
  /-- Objective cost to minimize. -/
  cost : Instance → Solution → ℝ
  /-- Optimal value on an instance. -/
  opt : Instance → ℝ
  /-- Every feasible solution on a valid instance costs at least `opt`. -/
  opt_le : ∀ x y, IsValid x → Feasible x y → opt x ≤ cost x y
  /-- Valid instances admit a feasible solution achieving `opt`. -/
  exists_opt : ∀ x, IsValid x → ∃ y, Feasible x y ∧ cost x y = opt x

/-- The gap promise problem induced by a minimization problem `P` with completeness threshold `c`
and soundness threshold `s`, restricted to valid instances. -/
@[expose] noncomputable def MinOptProblem.gapProblem {α σ : Type} (P : MinOptProblem α σ)
    (c s : α → ℝ) : PromiseProblem α :=
  (PromiseProblem.gapMin P.opt c s).restrict {x | P.IsValid x}

/-- An algorithm `A` is a `ρ`-approximation for minimization problem `P` when on every valid
instance it returns a feasible solution of cost at most `ρ x * P.opt x`. -/
@[expose] def MinOptProblem.IsApprox {α σ : Type} (P : MinOptProblem α σ) (ρ : α → ℝ)
    (A : α → σ) : Prop :=
  ∀ x, P.IsValid x → P.Feasible x (A x) ∧ P.cost x (A x) ≤ ρ x * P.opt x

/-- Polynomial-time **approximation-preserving reduction** from minimization problem `P₁` to `P₂`
with ratio transformer `g : α₁ → ℝ → ℝ`: polynomial-time maps `toInst` and `liftSol` preserve
validity and feasibility and transform any `ρ₂`-approximate solution of `toInst x` into a
`g x ρ₂`-approximate solution of `x`. -/
@[expose] def ApproxPreservingReducible {α₁ α₂ σ₁ σ₂ : Type}
    (P₁ : MinOptProblem α₁ σ₁) (P₂ : MinOptProblem α₂ σ₂)
    (encα₁ : α₁ ↪ List Bool) (encα₂ : α₂ ↪ List Bool)
    (encσ₁ : σ₁ ↪ List Bool) (encσ₂ : σ₂ ↪ List Bool)
    (g : α₁ → ℝ → ℝ) : Prop :=
  ∃ (toInst : α₁ → α₂) (liftSol : α₁ → σ₂ → σ₁),
    ComputableInPolyTime toInst encα₁ encα₂ ∧
    ComputableInPolyTime (fun p : α₁ × σ₂ => liftSol p.1 p.2) (encPair encα₁ encσ₂) encσ₁ ∧
    (∀ x, P₁.IsValid x → P₂.IsValid (toInst x)) ∧
    (∀ x y₂, P₁.IsValid x → P₂.Feasible (toInst x) y₂ → P₁.Feasible x (liftSol x y₂)) ∧
    (∀ x ρ₂ y₂, P₁.IsValid x → P₂.Feasible (toInst x) y₂ →
      P₂.cost (toInst x) y₂ ≤ ρ₂ * P₂.opt (toInst x) →
      P₁.cost x (liftSol x y₂) ≤ g x ρ₂ * P₁.opt x)

namespace ApproxPreservingReducible

/-- Identity approximation-preserving reduction. -/
theorem refl {α σ : Type} (P : MinOptProblem α σ) (encα : α ↪ List Bool)
    (encσ : σ ↪ List Bool) :
    ApproxPreservingReducible P P encα encα encσ encσ (fun _ ρ => ρ) :=
  ⟨id, fun _ y => y, ComputableInPolyTime.id', ComputableInPolyTime.snd _ _,
    fun _ hx => hx, fun _ _ _ hy => hy, fun _ _ _ _ _ h => h⟩

/-- Transitivity of approximation-preserving reductions. -/
theorem trans {α₁ α₂ α₃ σ₁ σ₂ σ₃ : Type}
    {P₁ : MinOptProblem α₁ σ₁} {P₂ : MinOptProblem α₂ σ₂} {P₃ : MinOptProblem α₃ σ₃}
    {encα₁ : α₁ ↪ List Bool} {encα₂ : α₂ ↪ List Bool} {encα₃ : α₃ ↪ List Bool}
    {encσ₁ : σ₁ ↪ List Bool} {encσ₂ : σ₂ ↪ List Bool} {encσ₃ : σ₃ ↪ List Bool}
    {g₁ : α₁ → ℝ → ℝ} {g₂ : ℝ → ℝ}
    (h₁₂ : ApproxPreservingReducible P₁ P₂ encα₁ encα₂ encσ₁ encσ₂ g₁)
    (h₂₃ : ApproxPreservingReducible P₂ P₃ encα₂ encα₃ encσ₂ encσ₃ (fun _ => g₂)) :
    ApproxPreservingReducible P₁ P₃ encα₁ encα₃ encσ₁ encσ₃ (fun x ρ => g₁ x (g₂ ρ)) := by
  obtain ⟨f₁₂, l₁₂, hf₁₂, hl₁₂, hv₁₂, hfe₁₂, hcost₁₂⟩ := h₁₂
  obtain ⟨f₂₃, l₂₃, hf₂₃, hl₂₃, hv₂₃, hfe₂₃, hcost₂₃⟩ := h₂₃
  let hleft := fst encα₁ encσ₃
  exact ⟨f₂₃ ∘ f₁₂, fun x y₃ => l₁₂ x (l₂₃ (f₁₂ x) y₃), hf₂₃.comp hf₁₂,
    hl₁₂.comp (hleft.prod (hl₂₃.comp ((hf₁₂.comp hleft).prod (snd encα₁ encσ₃)))),
    fun x hx => hv₂₃ (f₁₂ x) (hv₁₂ x hx),
    fun x y₃ hx hy₃ => hfe₁₂ x _ hx (hfe₂₃ (f₁₂ x) y₃ (hv₁₂ x hx) hy₃),
    fun x ρ₃ y₃ hx hy₃ hbound => hcost₁₂ x (g₂ ρ₃) _ hx (hfe₂₃ (f₁₂ x) y₃ (hv₁₂ x hx) hy₃)
      (hcost₂₃ (f₁₂ x) ρ₃ y₃ (hv₁₂ x hx) hy₃ hbound)⟩

/-- Pulling a polynomial-time `ρ₂`-approximation algorithm back through an
approximation-preserving reduction yields a polynomial-time approximation algorithm for `P₁`. -/
theorem comp_isApprox {α₁ α₂ σ₁ σ₂ : Type}
    {P₁ : MinOptProblem α₁ σ₁} {P₂ : MinOptProblem α₂ σ₂}
    {encα₁ : α₁ ↪ List Bool} {encα₂ : α₂ ↪ List Bool}
    {encσ₁ : σ₁ ↪ List Bool} {encσ₂ : σ₂ ↪ List Bool}
    {g : α₁ → ℝ → ℝ}
    (hred : ApproxPreservingReducible P₁ P₂ encα₁ encα₂ encσ₁ encσ₂ g)
    {A₂ : α₂ → σ₂} {ρ₂ : α₂ → ℝ}
    (hA₂ : ComputableInPolyTime A₂ encα₂ encσ₂)
    (happrox : P₂.IsApprox ρ₂ A₂) :
    ∃ A₁ : α₁ → σ₁, ComputableInPolyTime A₁ encα₁ encσ₁ ∧
      P₁.IsApprox (fun x => g x (ρ₂ (Classical.choose hred x))) A₁ := by
  classical
  let f := Classical.choose hred
  have hrest := Classical.choose_spec hred
  let l := Classical.choose hrest
  obtain ⟨hf, hl, hv, hfe, hcost⟩ := Classical.choose_spec hrest
  refine ⟨fun x => l x (A₂ (f x)), hl.comp (id'.prod (hA₂.comp hf)), fun x hx => ?_⟩
  obtain ⟨hfeas, hratio⟩ := happrox (f x) (hv x hx)
  exact ⟨hfe x _ hx hfeas, hcost x (ρ₂ (f x)) (A₂ (f x)) hx hfeas hratio⟩

end ApproxPreservingReducible

/-! ### Set Cover optimization problems and gap promise problems -/

private theorem coverIndices_isCover_of_isCoverList {S : SetSystem} {I : List ℕ}
    (hI : S.isCoverList I = true) :
    S.IsCover (Finset.univ.filter fun i : Fin S.sets.length => (i : ℕ) ∈ I.toFinset) := by
  intro u hu
  obtain ⟨i, hiI, hi, hui⟩ := ((S.isCoverList_eq_true_iff I).1 hI).2 u hu
  exact ⟨⟨i, hi⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, List.mem_toFinset.2 hiI⟩, hui⟩

private theorem card_coverIndices_le_length (S : SetSystem) (I : List ℕ) :
    (Finset.univ.filter fun i : Fin S.sets.length => (i : ℕ) ∈ I.toFinset).card ≤ I.length :=
  (card_filter_mem_le_card I.toFinset).trans (List.toFinset_card_le I)

private theorem sum_toFinset_le_map_sum (I : List ℕ) (f : ℕ → ℕ) :
    ∑ x ∈ I.toFinset, f x ≤ (I.map f).sum := by
  rw [← List.toFinset_dedup, List.sum_toFinset f (List.nodup_dedup I)]
  exact ((List.dedup_sublist I).map f).sum_le_sum (fun _ _ => Nat.zero_le _)

private theorem coverWeight_coverIndices_le_sum (W : WeightedSetSystem) (I : List ℕ) :
    W.coverWeight (Finset.univ.filter fun i : Fin W.sets.length => (i : ℕ) ∈ I.toFinset) ≤
      (I.map fun i => (W.sets.getD i ⟨[], 0⟩).weight).sum := by
  rw [WeightedSetSystem.coverWeight]
  let f (i : ℕ) := (W.sets.getD i ⟨[], 0⟩).weight
  calc ∑ i ∈ Finset.univ.filter (fun i : Fin W.sets.length => (i : ℕ) ∈ I.toFinset),
        W.sets[i].weight
      = ∑ x ∈ Finset.image Fin.val
          (Finset.univ.filter fun i : Fin W.sets.length => (i : ℕ) ∈ I.toFinset), f x := by
        rw [Finset.sum_image fun _ _ _ _ h => Fin.ext h]
        exact Finset.sum_congr rfl fun i _ =>
          (congrArg WeightedSet.weight (List.getD_eq_getElem _ _ i.isLt)).symm
    _ ≤ ∑ x ∈ I.toFinset, f x :=
        Finset.sum_le_sum_of_subset fun x hx => by
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
          exact (Finset.mem_filter.1 hi).2
    _ ≤ (I.map f).sum := sum_toFinset_le_map_sum I f

/-- Minimization problem view of unweighted Set Cover with index-list witnesses. -/
@[expose] noncomputable def minSetCover : MinOptProblem SetSystem (List ℕ) where
  IsValid := SetSystem.Coverable
  Feasible S I := S.isCoverList I = true
  cost _ I := (I.length : ℝ)
  opt S := (S.optCoverSize : ℝ)
  opt_le S I _ hI := by
    exact_mod_cast (SetSystem.optCoverSize_le (coverIndices_isCover_of_isCoverList hI)).trans
      (card_coverIndices_le_length S I)
  exists_opt S hS := by
    obtain ⟨C, hC, hcard⟩ := SetSystem.exists_isCover_optCoverSize hS
    refine ⟨(C.image Fin.val).toList, (S.isCoverList_eq_true_iff _).2 ⟨?_, ?_⟩, ?_⟩
    · intro i hi
      rw [Finset.mem_toList] at hi
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hi
      exact j.isLt
    · intro u hu
      obtain ⟨j, hjC, huj⟩ := hC u hu
      exact ⟨j, Finset.mem_toList.2 (Finset.mem_image.2 ⟨j, hjC, rfl⟩), j.isLt, huj⟩
    · simp only [Finset.length_toList, Finset.card_image_of_injective _ Fin.val_injective, hcard]

/-- Minimization problem view of weighted Set Cover with index-list witnesses. -/
@[expose] noncomputable def minWeightedSetCover : MinOptProblem WeightedSetSystem (List ℕ) where
  IsValid := WeightedSetSystem.Coverable
  Feasible W I := W.toSetSystem.isCoverList I = true
  cost W I := ((I.map fun i => (W.sets.getD i ⟨[], 0⟩).weight).sum : ℝ)
  opt W := (W.optCoverWeight : ℝ)
  opt_le W I _ hI := by
    have hlt' : ∀ i ∈ I, i < W.toSetSystem.sets.length :=
      (W.toSetSystem.isCoverList_eq_true_iff I).1 hI |>.1
    have hlt : ∀ i ∈ I, i < W.sets.length := fun i hi => by
      simpa [WeightedSetSystem.toSetSystem] using hlt' i hi
    have hcov : W.IsCover
        (Finset.univ.filter fun i : Fin W.sets.length => (i : ℕ) ∈ I.toFinset) := by
      intro u hu
      obtain ⟨i, hiI, hi, hui⟩ := ((W.toSetSystem.isCoverList_eq_true_iff I).1 hI).2 u hu
      have hi' : i < W.sets.length := hlt i hiI
      have h0 := hui
      simp only [WeightedSetSystem.toSetSystem, List.getElem_map] at h0
      exact ⟨⟨i, hi'⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, List.mem_toFinset.2 hiI⟩, h0⟩
    exact_mod_cast (WeightedSetSystem.optCoverWeight_le hcov).trans
      (coverWeight_coverIndices_le_sum W I)
  exists_opt W hW := by
    obtain ⟨C, hC, hwt⟩ := WeightedSetSystem.exists_isCover_optCoverWeight hW
    let I := (C.image Fin.val).toList
    have hnd : I.Nodup := Finset.nodup_toList _
    have hlt : ∀ i ∈ I, i < W.sets.length := fun i hi => by
      rw [Finset.mem_toList] at hi
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hi
      exact j.isLt
    refine ⟨I, (W.toSetSystem.isCoverList_eq_true_iff I).2 ⟨?_, ?_⟩, ?_⟩
    · intro i hi
      simpa [WeightedSetSystem.toSetSystem] using hlt i hi
    · intro u hu
      obtain ⟨j, hjC, huj⟩ := hC u hu
      refine ⟨j, Finset.mem_toList.2 (Finset.mem_image.2 ⟨j, hjC, rfl⟩),
        by simp [WeightedSetSystem.toSetSystem, j.isLt], ?_⟩
      simpa [WeightedSetSystem.toSetSystem] using huj
    · have hsum : (I.map fun i => (W.sets.getD i ⟨[], 0⟩).weight).sum = W.coverWeight C := by
        rw [← List.sum_toFinset _ hnd]
        have hI : I.toFinset = C.image Fin.val := by ext x; simp [I]
        rw [hI, Finset.sum_image (fun _ _ _ _ h => Fin.ext h), WeightedSetSystem.coverWeight]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [List.getD_eq_getElem _ _ j.isLt]
        rfl
      exact_mod_cast hsum.trans hwt

/-- Unweighted Set Cover gap problem with instance-dependent threshold ratio `r : SetSystem → ℝ`,
restricted to coverable set systems: yes-instances satisfy `optCoverSize S ≤ k`, while
no-instances satisfy `k < r S * k ≤ optCoverSize S`. -/
@[expose] noncomputable def GapSetCoverFn (r : SetSystem → ℝ) : PromiseProblem (SetSystem × ℕ) :=
  (PromiseProblem.gapMin (fun p => (p.1.optCoverSize : ℝ)) (fun p => (p.2 : ℝ))
    (fun p => r p.1 * p.2)).restrict {p | p.1.Coverable}

/-- Unweighted Set Cover gap problem at constant ratio `r`. -/
@[expose] noncomputable def GapSetCover (r : ℝ) : PromiseProblem (SetSystem × ℕ) :=
  GapSetCoverFn (fun _ => r)

/-- Weighted Set Cover gap problem with instance-dependent threshold ratio
`r : WeightedSetSystem → ℝ`, restricted to coverable weighted set systems. -/
@[expose] noncomputable def GapWeightedSetCoverFn (r : WeightedSetSystem → ℝ) :
    PromiseProblem (WeightedSetSystem × ℕ) :=
  (PromiseProblem.gapMin (fun p => (p.1.optCoverWeight : ℝ)) (fun p => (p.2 : ℝ))
    (fun p => r p.1 * p.2)).restrict {p | p.1.Coverable}

/-- Weighted Set Cover gap problem at constant ratio `r`. -/
@[expose] noncomputable def GapWeightedSetCover (r : ℝ) : PromiseProblem (WeightedSetSystem × ℕ) :=
  GapWeightedSetCoverFn (fun _ => r)

theorem mem_yes_GapSetCoverFn {r : SetSystem → ℝ} {S : SetSystem} {k : ℕ} :
    (S, k) ∈ (GapSetCoverFn r).yes ↔ S.Coverable ∧ S.optCoverSize ≤ k := by
  simp [GapSetCoverFn, Nat.cast_le, and_comm]

theorem mem_no_GapSetCoverFn {r : SetSystem → ℝ} {S : SetSystem} {k : ℕ} :
    (S, k) ∈ (GapSetCoverFn r).no ↔
      S.Coverable ∧ r S * k ≤ S.optCoverSize ∧ (k : ℝ) < r S * k := by
  simp [GapSetCoverFn, and_comm, and_left_comm]

theorem mem_yes_GapWeightedSetCoverFn {r : WeightedSetSystem → ℝ}
    {W : WeightedSetSystem} {k : ℕ} :
    (W, k) ∈ (GapWeightedSetCoverFn r).yes ↔ W.Coverable ∧ W.optCoverWeight ≤ k := by
  simp [GapWeightedSetCoverFn, Nat.cast_le, and_comm]

theorem mem_no_GapWeightedSetCoverFn {r : WeightedSetSystem → ℝ}
    {W : WeightedSetSystem} {k : ℕ} :
    (W, k) ∈ (GapWeightedSetCoverFn r).no ↔
      W.Coverable ∧ r W * k ≤ W.optCoverWeight ∧ (k : ℝ) < r W * k := by
  simp [GapWeightedSetCoverFn, and_comm, and_left_comm]

/-! ### Unweighted to Weighted Set Cover -/

/-- Equip every subset of `S : SetSystem` with weight `1`. -/
@[expose] def SetSystem.toWeighted (S : SetSystem) : WeightedSetSystem :=
  ⟨S.ground, S.sets.map fun A => ⟨A, 1⟩⟩

@[fun_prop] theorem computableInPolyTime_toWeighted :
    ComputableInPolyTime SetSystem.toWeighted encSetSystem encWeightedSetSystem := by
  fun_prop [SetSystem.toWeighted]

theorem toSetSystem_toWeighted (S : SetSystem) : S.toWeighted.toSetSystem = S := by
  simp only [SetSystem.toWeighted, WeightedSetSystem.toSetSystem, List.map_map]
  rw [show (WeightedSet.elements ∘ fun A : List ℕ => WeightedSet.mk A 1) = id from rfl,
    List.map_id]

theorem coverable_toWeighted_iff (S : SetSystem) : S.toWeighted.Coverable ↔ S.Coverable := by
  rw [WeightedSetSystem.coverable_iff_toSetSystem, toSetSystem_toWeighted]

theorem optCoverWeight_toWeighted (S : SetSystem) :
    S.toWeighted.optCoverWeight = S.optCoverSize := by
  by_cases hS : S.Coverable
  · refine le_antisymm ?_ ?_
    · obtain ⟨C, hC, hcard⟩ := SetSystem.exists_isCover_optCoverSize hS
      let emb : Fin S.sets.length ↪ Fin S.toWeighted.sets.length :=
        ⟨fun i => ⟨i.val, by simp [SetSystem.toWeighted, i.isLt]⟩,
          fun _ _ h => Fin.ext (Fin.mk.inj h)⟩
      have hC' : S.toWeighted.IsCover (C.map emb) := fun u hu => by
        obtain ⟨i, hi, hui⟩ := hC u hu
        exact ⟨⟨i.val, by simp [SetSystem.toWeighted, i.isLt]⟩, Finset.mem_map.2 ⟨i, hi, rfl⟩,
          by simpa [SetSystem.toWeighted] using hui⟩
      refine (WeightedSetSystem.optCoverWeight_le hC').trans_eq ?_
      rw [WeightedSetSystem.coverWeight, Finset.sum_map]
      calc ∑ x ∈ C, S.toWeighted.sets[emb x].weight
          = ∑ _x ∈ C, 1 := Finset.sum_congr rfl fun x _ => by
              simp [emb, Fin.getElem_fin, SetSystem.toWeighted]
        _ = S.optCoverSize := by simp [hcard]
    · obtain ⟨C, hC, hwt⟩ := WeightedSetSystem.exists_isCover_optCoverWeight
        ((coverable_toWeighted_iff S).2 hS)
      let emb : Fin S.toWeighted.sets.length ↪ Fin S.sets.length :=
        ⟨fun i => ⟨i.val, by simpa [SetSystem.toWeighted] using i.isLt⟩,
          fun _ _ h => Fin.ext (Fin.mk.inj h)⟩
      have hmap (i : Fin S.toWeighted.sets.length) : S.toWeighted.sets[i] =
          ⟨S.sets[i.val]'(by simpa [SetSystem.toWeighted] using i.isLt), 1⟩ :=
        List.getElem_map _
      have hC' : S.IsCover (C.map emb) := fun u hu => by
        obtain ⟨i, hi, hui⟩ := hC u hu
        exact ⟨⟨i.val, by simpa [SetSystem.toWeighted] using i.isLt⟩, Finset.mem_map.2 ⟨i, hi, rfl⟩,
          by simpa only [hmap i, Fin.getElem_fin] using hui⟩
      have hwt' : S.toWeighted.coverWeight C = C.card := by
        rw [WeightedSetSystem.coverWeight]
        calc ∑ i ∈ C, S.toWeighted.sets[i].weight
            = ∑ _i ∈ C, 1 := Finset.sum_congr rfl fun i _ => by rw [hmap i]
          _ = C.card := by simp
      exact (SetSystem.optCoverSize_le hC').trans_eq
        ((Finset.card_map _).trans (hwt'.symm.trans hwt))
  · rw [WeightedSetSystem.optCoverWeight_eq_zero_of_not_coverable
      (mt (coverable_toWeighted_iff S).1 hS),
      SetSystem.optCoverSize_eq_zero_of_not_coverable hS]

/-- **Unweighted Set Cover approximation-preservingly reduces to Weighted Set Cover** with unit
weights and identity ratio transformation. -/
theorem approxPreservingReducible_setCover_weightedSetCover :
    ApproxPreservingReducible minSetCover minWeightedSetCover
      encSetSystem encWeightedSetSystem (encList encNat) (encList encNat) (fun _ ρ => ρ) := by
  refine ⟨SetSystem.toWeighted, fun _ I => I, computableInPolyTime_toWeighted, snd _ _,
    fun S hS => (coverable_toWeighted_iff S).2 hS,
    fun _ _ _ hI => by simpa [minSetCover, minWeightedSetCover, toSetSystem_toWeighted] using hI,
    fun S ρ₂ I _ hI hcost => ?_⟩
  have hlt (i) (hi : i ∈ I) : i < S.toWeighted.sets.length := by
    have := ((S.toWeighted.toSetSystem.isCoverList_eq_true_iff I).1 hI).1 i hi
    simpa [WeightedSetSystem.toSetSystem] using this
  have hsum : (I.map fun i => (S.toWeighted.sets.getD i ⟨[], 0⟩).weight).sum = I.length := by
    calc (I.map fun i => (S.toWeighted.sets.getD i ⟨[], 0⟩).weight).sum
        = (I.map fun _ => 1).sum := congrArg List.sum <| List.map_congr_left fun i hi => by
            rw [List.getD_eq_getElem _ _ (hlt i hi)]
            simp [SetSystem.toWeighted]
      _ = I.length := by simp
  simpa only [minSetCover, minWeightedSetCover, hsum, optCoverWeight_toWeighted] using hcost

/-- **Unweighted Set Cover gap reduces in polynomial time to Weighted Set Cover gap** with the
same threshold ratio `r`. -/
theorem polyTimeReducible_GapSetCover_GapWeightedSetCover (r : ℝ) :
    PromiseProblem.PolyTimeReducible encSetCover encWeightedSetCover
      (GapSetCover r) (GapWeightedSetCover r) := by
  refine ⟨fun p => (p.1.toWeighted, p.2),
    (computableInPolyTime_toWeighted.comp (fst encSetSystem encNat)).prod
      (snd encSetSystem encNat), fun ⟨S, k⟩ hp => ?_, fun ⟨S, k⟩ hp => ?_⟩
  · simpa only [GapSetCover, GapWeightedSetCover, mem_yes_GapSetCoverFn,
      mem_yes_GapWeightedSetCoverFn, coverable_toWeighted_iff, optCoverWeight_toWeighted] using hp
  · simpa only [GapSetCover, GapWeightedSetCover, mem_no_GapSetCoverFn,
      mem_no_GapWeightedSetCoverFn, coverable_toWeighted_iff, optCoverWeight_toWeighted] using hp

/-! ### From Set Cover approximation algorithms to `P = NP` -/

private theorem exists_nat_rat_between {ρ r : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < r) :
    ∃ p q : ℕ, 0 < q ∧ ρ * q ≤ p ∧ (p : ℝ) < r * q := by
  obtain ⟨⟨num, den, hden, hcop⟩, hq0⟩ := exists_rat_btwn hρ
  rw [Rat.cast_def] at hq0
  have hden0 : 0 < den := Nat.pos_of_ne_zero hden
  have hden_pos : (0 : ℝ) < den := by exact_mod_cast hden0
  have hnum_nn : 0 ≤ num := by
    by_contra! h
    linarith [hρ0, hq0.1, div_neg_of_neg_of_pos (Int.cast_lt_zero.2 h) hden_pos]
  have hcast : (num.toNat : ℝ) = (num : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hnum_nn
  exact ⟨num.toNat, den, hden0, hcast ▸ (le_div_iff₀ hden_pos).1 hq0.1.le,
    hcast ▸ (div_lt_iff₀ hden_pos).1 hq0.2⟩

private theorem gapOpt_mem_PromiseP_of_approx {α : Type} {enc : α ↪ List Bool}
    {Valid : α → Prop} {opt cost : α → ℕ} {ρ r : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < r)
    (hcost : ComputableInPolyTime cost enc encNat)
    (hlb : ∀ x, Valid x → (opt x : ℝ) ≤ cost x)
    (hub : ∀ x, Valid x → (cost x : ℝ) ≤ ρ * opt x)
    (G : PromiseProblem (α × ℕ))
    (hyes : ∀ x k, (x, k) ∈ G.yes → Valid x ∧ opt x ≤ k)
    (hno : ∀ x k, (x, k) ∈ G.no → Valid x ∧ r * k ≤ opt x ∧ (k : ℝ) < r * k) :
    G ∈ PromiseP (encPair enc encNat) := by
  obtain ⟨p, q, hq, hlow, hhigh⟩ := exists_nat_rat_between hρ0 hρ
  refine mem_PromiseP_iff.2 ⟨fun x => decide (q * cost x.1 ≤ p * x.2),
    binary_le' (binary_mul' (const q) (hcost.comp (fst enc encNat)))
      (binary_mul' (const p) (snd enc encNat)),
    fun ⟨x, k⟩ hx => ?_, fun ⟨x, k⟩ hx => ?_⟩
  · obtain ⟨hxV, hk⟩ := hyes x k hx
    rw [decide_eq_true_eq]
    have hreal : (q * cost x : ℝ) ≤ p * k :=
      calc (q * cost x : ℝ)
          ≤ q * (ρ * opt x) := mul_le_mul_of_nonneg_left (hub x hxV) (Nat.cast_nonneg _)
        _ = (ρ * q) * opt x := by ring
        _ ≤ (p : ℝ) * k :=
            mul_le_mul hlow (by exact_mod_cast hk) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    exact_mod_cast hreal
  · obtain ⟨hxV, hopt, hlt⟩ := hno x k hx
    rw [decide_eq_false_iff_not, not_le]
    have hk0 : (0 : ℝ) < k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp at hlt
      · exact_mod_cast h
    have hreal : (p : ℝ) * k < q * cost x :=
      calc (p : ℝ) * k
          < (r * q) * k := mul_lt_mul_of_pos_right hhigh hk0
        _ = q * (r * k) := by ring
        _ ≤ q * opt x := mul_le_mul_of_nonneg_left hopt (Nat.cast_nonneg _)
        _ ≤ q * cost x := mul_le_mul_of_nonneg_left (hlb x hxV) (Nat.cast_nonneg _)
    exact_mod_cast hreal

/-- Any polynomial-time `ρ`-approximation algorithm (`0 ≤ ρ < r`) for unweighted Set Cover places
`GapSetCover r` in `PromiseP`. -/
theorem gapSetCover_mem_PromiseP_of_approx {A : SetSystem → List ℕ} {ρ r : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ < r)
    (hA : ComputableInPolyTime A encSetSystem (encList encNat))
    (happrox : minSetCover.IsApprox (fun _ => ρ) A) :
    GapSetCover r ∈ PromiseP encSetCover := by
  have hcost : ComputableInPolyTime (fun S : SetSystem => (A S).length) encSetSystem encNat :=
    ComputableInPolyTime.unary_to_binary.comp
      ((ComputableInPolyTime.length_list encNat).comp hA)
  exact gapOpt_mem_PromiseP_of_approx (Valid := SetSystem.Coverable) hρ0 hρ hcost
    (fun S hS => minSetCover.opt_le S (A S) hS (happrox S hS).1)
    (fun S hS => (happrox S hS).2) (GapSetCover r)
    (fun S k hx => by rw [GapSetCover, mem_yes_GapSetCoverFn] at hx; exact hx)
    (fun S k hx => by rw [GapSetCover, mem_no_GapSetCoverFn] at hx; exact hx)

/-- If `GapSetCover r` is `NP`-hard, no polynomial-time `ρ`-approximation algorithm with `0 ≤ ρ < r`
exists for unweighted Set Cover unless `P = NP`. -/
theorem P_eq_NP_of_setCover_approx {A : SetSystem → List ℕ} {ρ r : ℝ}
    (hhard : PromiseProblem.NPHard encSetCover (GapSetCover r))
    (hρ0 : 0 ≤ ρ) (hρ : ρ < r)
    (hA : ComputableInPolyTime A encSetSystem (encList encNat))
    (happrox : minSetCover.IsApprox (fun _ => ρ) A)
    {α : Type} (enc : α ↪ List Bool) : P enc = NP enc :=
  hhard.P_eq_NP_of_mem_PromiseP (gapSetCover_mem_PromiseP_of_approx hρ0 hρ hA happrox) enc

/-- Any polynomial-time `ρ`-approximation algorithm (`0 ≤ ρ < r`) for weighted Set Cover places
`GapWeightedSetCover r` in `PromiseP`. -/
theorem gapWeightedSetCover_mem_PromiseP_of_approx {A : WeightedSetSystem → List ℕ} {ρ r : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ρ < r)
    (hA : ComputableInPolyTime A encWeightedSetSystem (encList encNat))
    (happrox : minWeightedSetCover.IsApprox (fun _ => ρ) A) :
    GapWeightedSetCover r ∈ PromiseP encWeightedSetCover := by
  have hcost : ComputableInPolyTime
      (fun W : WeightedSetSystem => ((A W).map fun i => (W.sets.getD i ⟨[], 0⟩).weight).sum)
      encWeightedSetSystem encNat :=
    binary_sum.comp (mapWithInput hA (computableInPolyTime_weightedSetWeight.comp
      (listGetD_binary (⟨[], 0⟩ : WeightedSet)
        (by fun_prop : ComputableInPolyTime (fun q : WeightedSetSystem × ℕ => q.1.sets)
          (encPair encWeightedSetSystem encNat) (encList encWeightedSet))
        (snd encWeightedSetSystem encNat))))
  exact gapOpt_mem_PromiseP_of_approx (Valid := WeightedSetSystem.Coverable) hρ0 hρ hcost
    (fun W hW => minWeightedSetCover.opt_le W (A W) hW (happrox W hW).1)
    (fun W hW => (happrox W hW).2) (GapWeightedSetCover r)
    (fun _ _ hx => by rwa [GapWeightedSetCover, mem_yes_GapWeightedSetCoverFn] at hx)
    (fun _ _ hx => by rwa [GapWeightedSetCover, mem_no_GapWeightedSetCoverFn] at hx)

/-- If `GapWeightedSetCover r` is `NP`-hard, no polynomial-time `ρ`-approximation algorithm with
`0 ≤ ρ < r` exists for weighted Set Cover unless `P = NP`. -/
theorem P_eq_NP_of_weightedSetCover_approx {A : WeightedSetSystem → List ℕ} {ρ r : ℝ}
    (hhard : PromiseProblem.NPHard encWeightedSetCover (GapWeightedSetCover r))
    (hρ0 : 0 ≤ ρ) (hρ : ρ < r)
    (hA : ComputableInPolyTime A encWeightedSetSystem (encList encNat))
    (happrox : minWeightedSetCover.IsApprox (fun _ => ρ) A)
    {α : Type} (enc : α ↪ List Bool) : P enc = NP enc :=
  hhard.P_eq_NP_of_mem_PromiseP (gapWeightedSetCover_mem_PromiseP_of_approx hρ0 hρ hA happrox) enc

end Cslib.Complexity
