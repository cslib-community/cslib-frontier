/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Simulation
public import CslibFrontier.Computability.Circuit.SourceComplexity
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import CslibFrontier.Computability.Circuit.Simulation
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Ring

/-!
# Internal weighted circuit synthesis primitives

Internal `CostSynthesis` engine and zero-weight binary addition combinators shared by
`AdditiveBound`, `BlockCols`, `Decomposition`, `Complexity`, `StageStep`, and `UpperBound`; never
re-exported through `Zhegalkin`.

## Main definitions

* `Cslib.Circuits.CostSynthesis`: simultaneous total-gate and weight synthesis predicate.

## Main results

* `Cslib.Circuits.CostSynthesis.comp`, `CostSynthesis.trans`, `CostSynthesis.union`,
  `CostSynthesis.gate`, `CostSynthesis.biUnion`, `CostSynthesis.exists_circuit_outputs`,
  `CostSynthesis.exists_circuit`: synthesis combinators.
* `Cslib.Circuits.add_two_of_mem`, `nonempty_sum_of_mem`, `sum_of_mem_of_zero`,
  `block_nonempty_subSums`: zero-weight addition primitives.
-/

public section

open Finset

namespace Cslib.Circuits

section Engine

universe v u
variable {σ : Signature.{v}} {U : Type u} {n : ℕ}

/-- Simultaneous synthesis tracking both total gate count and an auxiliary per-gate weight `w`
(such as `andCost` over `{⊕, ∧, 1}`). -/
def CostSynthesis (I : Interpretation σ U) (w : σ.Op → ℕ)
    (sources targets : Set ((Fin n → U) → U)) (totalCost weightCost : ℕ) : Prop :=
  ∀ (g₁ : ℕ) (p₁ : Program σ n g₁), sources ⊆ available I p₁ →
    ∃ (g₂ : ℕ) (p₂ : Program σ n g₂),
      g₂ ≤ g₁ + totalCost ∧
      p₂.cost w ≤ p₁.cost w + weightCost ∧
      available I p₁ ⊆ available I p₂ ∧
      targets ⊆ available I p₂

namespace CostSynthesis

variable {I : Interpretation σ U} {w : σ.Op → ℕ}
variable {s t t₁ : Set ((Fin n → U) → U)} {a b wa wb : ℕ}

theorem of_subset (h : t ⊆ s) : CostSynthesis I w s t 0 0 :=
  fun g p hp => ⟨g, p, by omega, by omega, Set.Subset.rfl, h.trans hp⟩

theorem of_mem {f : (Fin n → U) → U} (hf : f ∈ s) : CostSynthesis I w s {f} 0 0 :=
  of_subset (Set.singleton_subset_iff.mpr hf)

theorem mono (h : CostSynthesis I w s t a wa) {s' t' : Set ((Fin n → U) → U)}
    {a' wa' : ℕ} (hs : s ⊆ s') (ht : t' ⊆ t) (ha : a ≤ a') (hwa : wa ≤ wa') :
    CostSynthesis I w s' t' a' wa' := by
  intro g₁ p₁ hp₁
  obtain ⟨g₂, p₂, hg, hw, hkeep, hout⟩ := h g₁ p₁ (hs.trans hp₁)
  exact ⟨g₂, p₂, by omega, by omega, hkeep, ht.trans hout⟩

theorem comp (h : CostSynthesis I w s t a wa) (h' : CostSynthesis I w (s ∪ t) t₁ b wb) :
    CostSynthesis I w s (t ∪ t₁) (a + b) (wa + wb) := by
  intro g₁ p₁ hp₁
  obtain ⟨g₂, p₂, hg₂, hw₂, hp₁₂, ht⟩ := h g₁ p₁ hp₁
  obtain ⟨g₃, p₃, hg₃, hw₃, hp₂₃, ht₁⟩ := h' g₂ p₂ (Set.union_subset (hp₁.trans hp₁₂) ht)
  exact ⟨g₃, p₃, by omega, by omega, hp₁₂.trans hp₂₃, Set.union_subset (ht.trans hp₂₃) ht₁⟩

theorem trans (h : CostSynthesis I w s t a wa) (h' : CostSynthesis I w (s ∪ t) t₁ b wb) :
    CostSynthesis I w s t₁ (a + b) (wa + wb) :=
  (h.comp h').mono Set.Subset.rfl Set.subset_union_right le_rfl le_rfl

theorem union (h : CostSynthesis I w s t a wa) (h' : CostSynthesis I w s t₁ b wb) :
    CostSynthesis I w s (t ∪ t₁) (a + b) (wa + wb) :=
  h.comp (h'.mono Set.subset_union_left Set.Subset.rfl le_rfl le_rfl)

theorem gate (op : σ.Op) (args : Fin (σ.Arity op) → (Fin n → U) → U)
    (hargs : ∀ i, args i ∈ s) :
    CostSynthesis I w s {fun x => I op (fun i => args i x)} 1 (w op) := by
  intro g₁ p₁ hp₁
  choose wires hw using fun i => mem_available.mp (hp₁ (hargs i))
  let line : Line σ n g₁ := ⟨op, wires⟩
  refine ⟨g₁ + 1, p₁.gate line, le_rfl, by simp [Program.cost_gate, line], ?_, ?_⟩
  · intro f hf
    obtain ⟨wire, hwire⟩ := mem_available.mp hf
    exact mem_available.mpr
      ⟨wire.castSucc, fun x => (Program.trace_gate_castSucc _ _ _ _ _).trans (hwire x)⟩
  · rw [Set.singleton_subset_iff, mem_available]
    refine ⟨.gate (Fin.last g₁), fun x => (Program.eval_gate_last p₁ line I x).trans ?_⟩
    change I op (fun i => p₁.trace I x (wires i)) = _
    simp only [hw]

theorem biUnion {ι : Type*} (indices : Finset ι) (targets : ι → Set ((Fin n → U) → U))
    (tc wc : ι → ℕ) (h : ∀ i ∈ indices, CostSynthesis I w s (targets i) (tc i) (wc i)) :
    CostSynthesis I w s (⋃ i ∈ indices, targets i) (∑ i ∈ indices, tc i) (∑ i ∈ indices, wc i) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
    simpa only [notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, sum_empty] using
      of_subset (Set.empty_subset s)
  | @insert i indices hi ih =>
    have hstep := (h i (mem_insert_self i indices)).union
      (ih fun j hj => h j (mem_insert_of_mem hj))
    rwa [set_biUnion_insert, sum_insert hi, sum_insert hi]

theorem exists_circuit_outputs {m : ℕ} {f : Fin m → (Fin n → U) → U}
    (h : CostSynthesis I w (inputs n) (Set.range f) a wa) :
    ∃ c : Circuit σ n m, c.Computes I (fun x j => f j x) ∧ c.size ≤ a ∧ c.program.cost w ≤ wa := by
  obtain ⟨g, p, hg, hw, _, hout⟩ := h 0 .empty (inputs_subset_available _)
  choose wires hwires using fun j => mem_available.mp (hout ⟨j, rfl⟩)
  exact ⟨⟨p, wires⟩, fun x => funext fun j => hwires j x, by simpa using hg, by simpa using hw⟩

theorem exists_circuit {f : (Fin n → U) → U}
    (h : CostSynthesis I w (inputs n) {f} a wa) :
    ∃ c : Circuit σ n 1, c.Computes I (single f) ∧ c.size ≤ a ∧ c.program.cost w ≤ wa := by
  exact (h.mono (t' := Set.range fun _ : Fin 1 => f) Set.Subset.rfl Set.range_const_subset le_rfl
    le_rfl).exists_circuit_outputs

end CostSynthesis

/-! #### Zero-weight binary addition primitives -/

section AddPrimitives

variable {G : Type u} [AddCommMonoid G] {I : Interpretation σ G} {w : σ.Op → ℕ}
variable {addOp : σ.Op}

theorem add_two_of_mem (hArity : σ.Arity addOp = 2)
    (hEval : ∀ args : Fin (σ.Arity addOp) → G,
      I addOp args = args ⟨0, by omega⟩ + args ⟨1, by omega⟩)
    (hZeroW : w addOp = 0) {s : Set ((Fin n → G) → G)} {f g : (Fin n → G) → G}
    (hf : f ∈ s) (hg : g ∈ s) :
    CostSynthesis I w s {fun x => f x + g x} 1 0 := by
  let args : Fin (σ.Arity addOp) → (Fin n → G) → G :=
    fun i => if i.val = 0 then f else g
  have h := CostSynthesis.gate (I := I) (w := w) (s := s) addOp args fun i => by
    dsimp only [args]
    split_ifs <;> assumption
  refine h.mono Set.Subset.rfl ?_ le_rfl (by omega)
  rintro _ rfl
  refine funext fun x => ?_
  simp [hEval, args]

/-- Summing a nonempty finite family of already-available wires uses `#S - 1` binary addition gates
and zero weight, with no constant or zero gate needed. -/
theorem nonempty_sum_of_mem {ι : Type*} (hArity : σ.Arity addOp = 2)
    (hEval : ∀ args : Fin (σ.Arity addOp) → G,
      I addOp args = args ⟨0, by omega⟩ + args ⟨1, by omega⟩)
    (hZeroW : w addOp = 0) {s : Set ((Fin n → G) → G)}
    (S : Finset ι) (hS : S.Nonempty) (F : ι → (Fin n → G) → G) (hF : ∀ i ∈ S, F i ∈ s) :
    CostSynthesis I w s {fun x => ∑ i ∈ S, F i x} (#S - 1) 0 := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton a =>
    simpa only [sum_singleton, card_singleton] using
      CostSynthesis.of_mem (hF a (mem_singleton_self a))
  | cons a T haT hT ih =>
    have htot := (ih fun i hi => hF i (mem_cons_of_mem hi)).trans
      (add_two_of_mem hArity hEval hZeroW (s := s ∪ {fun x => ∑ i ∈ T, F i x})
        (Or.inl (hF a (mem_cons_self a T))) (Or.inr rfl))
    have := hT.card_pos
    simp only [sum_cons, card_cons]
    exact htot.mono Set.Subset.rfl Set.Subset.rfl (by omega) le_rfl

/-- Summing a finite family when `(fun _ => 0)` is already available uses at most `#S - 1` binary
addition gates (in particular `0` gates when `#S ≤ 1`). -/
theorem sum_of_mem_of_zero {ι : Type*} (hArity : σ.Arity addOp = 2)
    (hEval : ∀ args : Fin (σ.Arity addOp) → G,
      I addOp args = args ⟨0, by omega⟩ + args ⟨1, by omega⟩)
    (hZeroW : w addOp = 0) {s : Set ((Fin n → G) → G)} (hzero : (fun _ => (0 : G)) ∈ s)
    (S : Finset ι) (F : ι → (Fin n → G) → G) (hF : ∀ i ∈ S, F i ∈ s) :
    CostSynthesis I w s {fun x => ∑ i ∈ S, F i x} (#S - 1) 0 := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simpa only [sum_empty, card_empty] using CostSynthesis.of_mem hzero
  · exact nonempty_sum_of_mem hArity hEval hZeroW S hS F hF

/-! #### Nonempty subset sums of a block of `b` wires -/

theorem mul_sub_two_pow_le {b s : ℕ} (hbs : b ≤ s) :
    s * (2 ^ b - b - 1) ≤ b * 2 ^ s := by
  rcases b.eq_zero_or_pos with rfl | hb
  · simp
  · have hmono : ∀ k, b ≤ k → k * 2 ^ b ≤ b * 2 ^ k := by
      intro k hbk
      induction k, hbk using Nat.le_induction with
      | base => exact le_rfl
      | succ k hbk ih =>
        have := Nat.le_mul_of_pos_left (2 ^ b) (lt_of_lt_of_le hb hbk)
        rw [pow_succ, add_mul, one_mul, ← mul_assoc]
        omega
    exact (Nat.mul_le_mul_left s ((Nat.sub_le _ _).trans (Nat.sub_le _ _))).trans (hmono s hbs)

/-- All `2 ^ b - 1` nonempty subset sums of `b` available functions cost `2 ^ b - b - 1` binary
addition gates (since the `b` singletons are already available). -/
theorem block_nonempty_subSums (hArity : σ.Arity addOp = 2)
    (hEval : ∀ args : Fin (σ.Arity addOp) → G,
      I addOp args = args ⟨0, by omega⟩ + args ⟨1, by omega⟩)
    (hZeroW : w addOp = 0) {s : Set ((Fin n → G) → G)} :
    ∀ {b : ℕ} (v : Fin b → (Fin n → G) → G), (∀ j, v j ∈ s) →
      CostSynthesis I w s
        {f | ∃ T : Finset (Fin b), T.Nonempty ∧ f = fun x => ∑ j ∈ T, v j x}
        (2 ^ b - b - 1) 0
  | 0, _, _ => by
    refine (CostSynthesis.of_subset (Set.empty_subset s)).mono Set.Subset.rfl ?_ (by omega) le_rfl
    rintro _ ⟨T, ⟨j, _⟩, _⟩
    exact j.elim0
  | b + 1, v, hv => by
    let v' : Fin b → (Fin n → G) → G := v ∘ Fin.castSucc
    let prevSet : Set ((Fin n → G) → G) :=
      {f | ∃ T' : Finset (Fin b), T'.Nonempty ∧ f = fun x => ∑ j ∈ T', v' j x}
    have ih := block_nonempty_subSums hArity hEval hZeroW v' (fun j => hv j.castSucc)
    let nonempB : Finset (Finset (Fin b)) := univ.erase ∅
    have hstep (T' : Finset (Fin b)) (hT' : T' ∈ nonempB) :
        CostSynthesis I w (s ∪ prevSet)
          {fun x => v (Fin.last b) x + ∑ j ∈ T', v' j x} 1 0 := by
      have hne : T'.Nonempty := ne_empty_iff_nonempty.mp (mem_erase.mp hT').1
      exact add_two_of_mem hArity hEval hZeroW
        (Or.inl (hv (Fin.last b))) (Or.inr ⟨T', hne, rfl⟩)
    have hall := CostSynthesis.biUnion nonempB
      (fun T' => {fun x => v (Fin.last b) x + ∑ j ∈ T', v' j x})
      (fun _ => 1) (fun _ => 0) hstep
    have htot := (CostSynthesis.of_subset (I := I) (w := w) Set.Subset.rfl).union (ih.comp hall)
    have hcard_nonempB : #nonempB = 2 ^ b - 1 := by
      simp only [nonempB, card_erase_of_mem (mem_univ ∅), card_univ, Fintype.card_finset,
        Fintype.card_fin]
    have hbudget : 0 + ((2 ^ b - b - 1) + ∑ _ ∈ nonempB, 1) ≤ 2 ^ (b + 1) - (b + 1) - 1 := by
      rw [sum_const, smul_eq_mul, mul_one, hcard_nonempB, pow_succ]
      have := b.lt_two_pow_self
      omega
    refine htot.mono Set.Subset.rfl ?_ hbudget (by simp)
    rintro _ ⟨T, hT, rfl⟩
    let T' : Finset (Fin b) := univ.filter fun j => j.castSucc ∈ T
    by_cases hlast : Fin.last b ∈ T
    · have hT_decomp : T = insert (Fin.last b) (T'.map Fin.castSuccEmb) := by
        ext k
        refine Fin.lastCases ?_ (fun j => ?_) k
        · simp [T', hlast]
        · simp [T', Fin.castSucc_ne_last]
      rcases T'.eq_empty_or_nonempty with hT'0 | hT'ne
      · have hT_sing : T = {Fin.last b} := by simp [hT_decomp, hT'0]
        subst hT_sing
        exact Or.inl (by simpa only [sum_singleton] using hv (Fin.last b))
      · refine Or.inr (Or.inr (Set.mem_iUnion₂.mpr
          ⟨T', mem_erase.mpr ⟨hT'ne.ne_empty, mem_univ T'⟩, funext fun x => ?_⟩))
        rw [hT_decomp, sum_insert (by simp [Fin.castSucc_ne_last]), sum_map]
        rfl
    · have hT_decomp : T = T'.map Fin.castSuccEmb := by
        ext k
        refine Fin.lastCases ?_ (fun j => ?_) k
        · simp [T', hlast]
        · simp [T']
      have hT'ne : T'.Nonempty := by
        rw [hT_decomp] at hT
        exact map_nonempty.mp hT
      refine Or.inr (Or.inl ⟨T', hT'ne, ?_⟩)
      funext x
      rw [hT_decomp, sum_map]
      rfl

end AddPrimitives

end Engine

end Cslib.Circuits
