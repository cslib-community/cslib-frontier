/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Circuit.Boolean.Complexity
public import Cslib.Computability.Circuit.Simulation
public import CslibFrontier.Computability.Circuit.SourceComplexity
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Nat.Log
import Cslib.Foundations.Data.Nat.Asymptotics
import CslibFrontier.Computability.Circuit.Simulation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Additive matrix synthesis and multiplicative-to-total complexity over `{⊕, ∧, 1}`

This file formalizes the constructive upper bounds of Igor S. Sergeev on additive matrix synthesis
and total-from-multiplicative circuit complexity over the Zhegalkin basis `{⊕, ∧, 1}`
[Sergeev2013AdditiveMultiplicative]:

1. **Active-square additive matrix synthesis**
   ([Sergeev, Lemma 1, pp. 2–3][Sergeev2013AdditiveMultiplicative], reformulating a special case of
   Nechiporuk): for an `m × n` Boolean matrix `A`, its *active square* `A.activeSquare` (`S(A)`)
   counts the entries `(i, j)` within horizontal distance `Nat.log 2 m` of a `true` entry in row
   `i`. Over any additive commutative monoid `G`, the linear operator
   `x ↦ (i ↦ ∑ j, if A i j then x j else 0)` can be computed by an additive circuit of size at most
   `(n * 2 ^ s) / s + A.activeSquare / (2 * s) + m * p + (m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s)` whenever
   `0 < s ≤ Nat.log 2 m + 1` and `0 < p` (`Additive.exists_circuit_matrix_le_bound`), hence
   asymptotically `A.activeSquare / (2 * Real.logb 2 m) + ε * (m + n) ^ 2 / Real.logb 2 m`
   (`Additive.exists_circuit_matrix_le`).
2. **Multiplicative-to-total complexity upper bound over `{⊕, ∧, 1}`**
   ([Sergeev, Theorem 1 (upper bound), pp. 1, 3][Sergeev2013AdditiveMultiplicative]): every
   `n`-variable Boolean function computed by a `{⊕, ∧, 1}`-circuit with at most `M` conjunction
   (`∧`) gates can be computed by an acyclic `{⊕, ∧, 1}`-circuit using no more `∧`-gates and total
   gate count at most `Zhegalkin.totalBound n M s p`
   (`Zhegalkin.exists_circuit_of_andCost_le_bound`), giving
   `(1 / 2 + ε) * M * (M + 2 * n) / Real.logb 2 M` uniformly in `n` for all sufficiently large `M`
   (`Zhegalkin.exists_circuit_of_andCost_le`,
   `Zhegalkin.complexity_le_of_multiplicativeComplexity_le`).

To keep the `{⊕, ∧, 1}` circuit strictly acyclic while sharing paired column sums across all `2 M`
conjunction-input rows, the `M` topologically ordered `∧`-gates are processed in stages of `s`
consecutive gates: every paired sum `y_{r₁, r₂}` between rows `r₁ < r₂` reads only original inputs
and `∧`-gate blocks completed strictly before `r₁`'s stage, while the `< s` intra-stage `∧`-gates
preceding a gate are added directly with `O(M s)` XOR gates.

## Main definitions

* `Matrix.activeSquare`: active square `S(A)` of an `m × n` Boolean matrix.
* `Cslib.Circuits.Additive.Op`, `Cslib.Circuits.Additive.signature`,
  `Cslib.Circuits.Additive.interpretation`, `Cslib.Circuits.Additive.matrixBound`: the additive
  circuit basis `{0, +}` and explicit `(s, p)` gate budget of Lemma 1.
* `Cslib.Circuits.Boolean.Zhegalkin.Op`, `Cslib.Circuits.Boolean.Zhegalkin.signature`,
  `Cslib.Circuits.Boolean.Zhegalkin.interpretation`: the Zhegalkin Boolean basis `{⊕, ∧, 1}`.
* `Cslib.Circuits.Boolean.Zhegalkin.andCost`,
  `Cslib.Circuits.Boolean.Zhegalkin.multiplicativeComplexity`: conjunction-gate cost and
  multiplicative complexity `L_∧(f)`.
* `Cslib.Circuits.Boolean.Zhegalkin.totalBound`: explicit `(n, M, s, p)` total gate budget for the
  upper bound of Theorem 1.

## Main results

* `Cslib.Circuits.Additive.exists_circuit_matrix_le_bound`: explicit active-square additive matrix
  synthesis bound ([Sergeev, Lemma 1, pp. 2–3][Sergeev2013AdditiveMultiplicative]).
* `Cslib.Circuits.Additive.exists_circuit_matrix_le`: asymptotic active-square additive matrix
  bound `S(A) / (2 log₂ m) + ε (m + n)² / log₂ m`
  ([Sergeev, Lemma 1, p. 2][Sergeev2013AdditiveMultiplicative]).
* `Cslib.Circuits.Boolean.Zhegalkin.exists_circuit_of_andCost_le_bound`: explicit staged acyclic
  `{⊕, ∧, 1}`-circuit synthesis bound preserving conjunction count
  ([Sergeev, Theorem 1 (upper bound), p. 3][Sergeev2013AdditiveMultiplicative]).
* `Cslib.Circuits.Boolean.Zhegalkin.exists_circuit_of_andCost_le`,
  `Cslib.Circuits.Boolean.Zhegalkin.complexity_le_of_multiplicativeComplexity_le`: asymptotic
  `(1 / 2 + ε) * M * (M + 2 * n) / log₂ M` total complexity upper bound from multiplicative
  complexity ([Sergeev, Theorem 1 (upper bound), p. 1][Sergeev2013AdditiveMultiplicative]).

## References

* [I. S. Sergeev, *A relation between additive and multiplicative complexity of Boolean
  functions*][Sergeev2013AdditiveMultiplicative]
-/

public section

open Finset

/-! ### Active square of a Boolean matrix -/

namespace Matrix

/-- The *active square* `S(A)` of an `m × n` Boolean matrix `A`
([Sergeev, p. 2][Sergeev2013AdditiveMultiplicative]): the number of entries `(i, j)` located within
horizontal distance `Nat.log 2 m` of a `true` entry in the same row `i`. Because column distances
are natural numbers, for `1 ≤ m` the condition `Nat.dist j j' ≤ Nat.log 2 m` is equivalent to
`(Nat.dist j j' : ℝ) ≤ Real.logb 2 m`. -/
@[expose] def activeSquare {m n : ℕ} (A : Matrix (Fin m) (Fin n) Bool) : ℕ :=
  #{p : Fin m × Fin n | ∃ j' : Fin n, A p.1 j' = true ∧ Nat.dist p.2.val j'.val ≤ Nat.log 2 m}

/-- The active square of an `m × n` Boolean matrix is at most `m * n`. -/
theorem activeSquare_le_mul {m n : ℕ} (A : Matrix (Fin m) (Fin n) Bool) :
    A.activeSquare ≤ m * n :=
  (card_filter_le _ _).trans_eq (by simp)

end Matrix

namespace Cslib.Circuits

/-! ### Additive circuits -/

namespace Additive

/-- Operations of the additive monoid circuit basis `{0, +}`. -/
inductive Op where
  /-- The additive identity `0`. -/
  | zero
  /-- Binary addition `+`. -/
  | add
  deriving DecidableEq

instance : Fintype Op :=
  ⟨{.zero, .add}, fun op => by cases op <;> simp⟩

/-- The additive circuit signature: nullary `zero` and binary `add`. -/
abbrev signature : Signature where
  Op := Op
  Arity
    | .zero => 0
    | .add => 2

/-- Interpretation of the additive signature in any type with `0` and `+`. -/
@[expose] def interpretation (G : Type*) [AddZeroClass G] : Interpretation signature G
  | .zero, _ => 0
  | .add, x => x 0 + x 1

@[simp] theorem interpretation_zero (G : Type*) [AddZeroClass G] (x : Fin 0 → G) :
    interpretation G .zero x = 0 := rfl

@[simp] theorem interpretation_add (G : Type*) [AddZeroClass G] (x : Fin 2 → G) :
    interpretation G .add x = x 0 + x 1 := rfl

/-- Explicit gate budget of [Sergeev, Lemma 1, p. 3][Sergeev2013AdditiveMultiplicative] for an
`m × n` Boolean matrix `A` with column-group width `s` and horizontal section height `p`. -/
@[expose] def matrixBound {m n : ℕ} (A : Matrix (Fin m) (Fin n) Bool) (s p : ℕ) : ℕ :=
  (n * 2 ^ s) / s + A.activeSquare / (2 * s) + m * p + (m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s)

end Additive

/-! ### Shared weighted synthesis and block-section combinatorics -/

section Engine

universe v u
variable {σ : Signature.{v}} {U : Type u} {n : ℕ}

/-- Simultaneous synthesis tracking both total gate count and an auxiliary per-gate weight `w`
(such as `andCost` over `{⊕, ∧, 1}`). -/
private def CostSynthesis (I : Interpretation σ U) (w : σ.Op → ℕ)
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

private theorem of_subset (h : t ⊆ s) : CostSynthesis I w s t 0 0 :=
  fun g p hp => ⟨g, p, by omega, by omega, Set.Subset.rfl, h.trans hp⟩

private theorem of_mem {f : (Fin n → U) → U} (hf : f ∈ s) : CostSynthesis I w s {f} 0 0 :=
  of_subset (Set.singleton_subset_iff.mpr hf)

private theorem mono (h : CostSynthesis I w s t a wa) {s' t' : Set ((Fin n → U) → U)}
    {a' wa' : ℕ} (hs : s ⊆ s') (ht : t' ⊆ t) (ha : a ≤ a') (hwa : wa ≤ wa') :
    CostSynthesis I w s' t' a' wa' := by
  intro g₁ p₁ hp₁
  obtain ⟨g₂, p₂, hg, hw, hkeep, hout⟩ := h g₁ p₁ (hs.trans hp₁)
  exact ⟨g₂, p₂, by omega, by omega, hkeep, ht.trans hout⟩

private theorem comp (h : CostSynthesis I w s t a wa) (h' : CostSynthesis I w (s ∪ t) t₁ b wb) :
    CostSynthesis I w s (t ∪ t₁) (a + b) (wa + wb) := by
  intro g₁ p₁ hp₁
  obtain ⟨g₂, p₂, hg₂, hw₂, hp₁₂, ht⟩ := h g₁ p₁ hp₁
  obtain ⟨g₃, p₃, hg₃, hw₃, hp₂₃, ht₁⟩ := h' g₂ p₂ (Set.union_subset (hp₁.trans hp₁₂) ht)
  exact ⟨g₃, p₃, by omega, by omega, hp₁₂.trans hp₂₃, Set.union_subset (ht.trans hp₂₃) ht₁⟩

private theorem trans (h : CostSynthesis I w s t a wa) (h' : CostSynthesis I w (s ∪ t) t₁ b wb) :
    CostSynthesis I w s t₁ (a + b) (wa + wb) :=
  (h.comp h').mono Set.Subset.rfl Set.subset_union_right le_rfl le_rfl

private theorem union (h : CostSynthesis I w s t a wa) (h' : CostSynthesis I w s t₁ b wb) :
    CostSynthesis I w s (t ∪ t₁) (a + b) (wa + wb) :=
  h.comp (h'.mono Set.subset_union_left Set.Subset.rfl le_rfl le_rfl)

private theorem gate (op : σ.Op) (args : Fin (σ.Arity op) → (Fin n → U) → U)
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

private theorem biUnion {ι : Type*} (indices : Finset ι) (targets : ι → Set ((Fin n → U) → U))
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
    have hset : targets i ∪ (⋃ j ∈ indices, targets j) = ⋃ j ∈ insert i indices, targets j := by
      ext f
      simp only [Set.mem_union, Set.mem_iUnion, mem_insert]
      constructor
      · rintro (hf | ⟨j, hj, hf⟩)
        · exact ⟨i, Or.inl rfl, hf⟩
        · exact ⟨j, Or.inr hj, hf⟩
      · rintro ⟨j, rfl | hj, hf⟩
        · exact Or.inl hf
        · exact Or.inr ⟨j, hj, hf⟩
    rw [hset, ← sum_insert hi, ← sum_insert hi] at hstep
    exact hstep

private theorem exists_circuit_outputs {m : ℕ} {f : Fin m → (Fin n → U) → U}
    (h : CostSynthesis I w (inputs n) (Set.range f) a wa) :
    ∃ c : Circuit σ n m, c.Computes I (fun x j => f j x) ∧ c.size ≤ a ∧ c.program.cost w ≤ wa := by
  obtain ⟨g, p, hg, hw, _, hout⟩ := h 0 .empty (inputs_subset_available _)
  choose wires hwires using fun j => mem_available.mp (hout ⟨j, rfl⟩)
  exact ⟨⟨p, wires⟩, fun x => funext fun j => hwires j x, by simpa using hg, by simpa using hw⟩

private theorem exists_circuit {f : (Fin n → U) → U}
    (h : CostSynthesis I w (inputs n) {f} a wa) :
    ∃ c : Circuit σ n 1, c.Computes I (single f) ∧ c.size ≤ a ∧ c.program.cost w ≤ wa := by
  have h' : CostSynthesis I w (inputs n) (Set.range fun _ : Fin 1 => f) a wa := by
    refine h.mono Set.Subset.rfl ?_ le_rfl le_rfl
    rintro _ ⟨_, rfl⟩
    exact rfl
  exact h'.exists_circuit_outputs

end CostSynthesis

/-! #### Zero-weight binary addition primitives -/

section AddPrimitives

variable {G : Type u} [AddCommMonoid G] {I : Interpretation σ G} {w : σ.Op → ℕ}
variable {addOp : σ.Op}

private theorem add_two_of_mem (hArity : σ.Arity addOp = 2)
    (hEval : ∀ args : Fin (σ.Arity addOp) → G,
      I addOp args = args ⟨0, by omega⟩ + args ⟨1, by omega⟩)
    (hZeroW : w addOp = 0) {s : Set ((Fin n → G) → G)} {f g : (Fin n → G) → G}
    (hf : f ∈ s) (hg : g ∈ s) :
    CostSynthesis I w s {fun x => f x + g x} 1 0 := by
  let args : Fin (σ.Arity addOp) → (Fin n → G) → G :=
    fun i => if i.1 = 0 then f else g
  have h := CostSynthesis.gate (I := I) (w := w) (s := s) addOp args fun i => by
    dsimp only [args]
    split_ifs <;> assumption
  refine h.mono Set.Subset.rfl ?_ le_rfl (by omega)
  rintro _ rfl
  have heq : (fun x => f x + g x) = fun x => I addOp (fun i => args i x) := by
    funext x
    rw [hEval]
    dsimp only [args]
    simp
  rw [heq]
  exact rfl

/-- Summing a nonempty finite family of already-available wires uses `#S - 1` binary addition gates
and zero weight, with no constant or zero gate needed. -/
private theorem nonempty_sum_of_mem {ι : Type*} (hArity : σ.Arity addOp = 2)
    (hEval : ∀ args : Fin (σ.Arity addOp) → G,
      I addOp args = args ⟨0, by omega⟩ + args ⟨1, by omega⟩)
    (hZeroW : w addOp = 0) {s : Set ((Fin n → G) → G)}
    (S : Finset ι) (hS : S.Nonempty) (F : ι → (Fin n → G) → G) (hF : ∀ i ∈ S, F i ∈ s) :
    CostSynthesis I w s {fun x => ∑ i ∈ S, F i x} (#S - 1) 0 := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton a =>
    have heq : (fun x => ∑ i ∈ ({a} : Finset ι), F i x) = F a := by
      funext x
      exact sum_singleton (fun i => F i x) a
    rw [heq, card_singleton]
    exact CostSynthesis.of_mem (hF a (mem_singleton_self a))
  | cons a T haT hT ih =>
    have hsub := ih fun i hi => hF i (mem_cons_of_mem hi)
    have hadd := add_two_of_mem hArity hEval hZeroW (s := s ∪ {fun x => ∑ i ∈ T, F i x})
      (Or.inl (hF a (mem_cons.mpr (Or.inl rfl)))) (Or.inr rfl)
    have htot := hsub.trans hadd
    have heq : (fun x => F a x + ∑ i ∈ T, F i x) = fun x => ∑ i ∈ cons a T haT, F i x := by
      funext x
      exact (sum_cons (f := fun i => F i x) haT).symm
    rw [heq] at htot
    rw [card_cons]
    have hcard : 1 ≤ #T := hT.card_pos
    exact htot.mono Set.Subset.rfl Set.Subset.rfl (by omega) le_rfl

/-- Summing a finite family when `(fun _ => 0)` is already available uses at most `#S - 1` binary
addition gates (in particular `0` gates when `#S ≤ 1`). -/
private theorem sum_of_mem_of_zero {ι : Type*} (hArity : σ.Arity addOp = 2)
    (hEval : ∀ args : Fin (σ.Arity addOp) → G,
      I addOp args = args ⟨0, by omega⟩ + args ⟨1, by omega⟩)
    (hZeroW : w addOp = 0) {s : Set ((Fin n → G) → G)} (hzero : (fun _ => (0 : G)) ∈ s)
    (S : Finset ι) (F : ι → (Fin n → G) → G) (hF : ∀ i ∈ S, F i ∈ s) :
    CostSynthesis I w s {fun x => ∑ i ∈ S, F i x} (#S - 1) 0 := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simpa only [sum_empty, card_empty] using CostSynthesis.of_mem hzero
  · exact nonempty_sum_of_mem hArity hEval hZeroW S hS F hF

/-! #### Nonempty subset sums of a block of `b` wires -/

private theorem add_one_le_two_pow (b : ℕ) : b + 1 ≤ 2 ^ b := by
  induction b with
  | zero => decide
  | succ b ih =>
    have := Nat.one_le_two_pow (n := b)
    rw [pow_succ]
    omega

private theorem mul_sub_two_pow_le {b s : ℕ} (hbs : b ≤ s) :
    s * (2 ^ b - b - 1) ≤ b * 2 ^ s := by
  rcases b.eq_zero_or_pos with rfl | hb
  · simp
  · have hmono : ∀ k, b ≤ k → k * 2 ^ b ≤ b * 2 ^ k := by
      intro k hbk
      induction k, hbk using Nat.le_induction with
      | base => exact le_rfl
      | succ k hbk ih =>
        calc (k + 1) * 2 ^ b = k * 2 ^ b + 2 ^ b := by ring
          _ ≤ k * 2 ^ b + k * 2 ^ b :=
              Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (lt_of_lt_of_le hb hbk)) _
          _ = 2 * (k * 2 ^ b) := by ring
          _ ≤ 2 * (b * 2 ^ k) := Nat.mul_le_mul_left 2 ih
          _ = b * 2 ^ (k + 1) := by rw [pow_succ]; ring
    exact (Nat.mul_le_mul_left s (Nat.sub_le _ _)).trans
      ((Nat.mul_le_mul_left s (Nat.sub_le _ _)).trans (hmono s hbs))

/-- All `2 ^ b - 1` nonempty subset sums of `b` available functions cost `2 ^ b - b - 1` binary
addition gates (since the `b` singletons are already available). -/
private theorem block_nonempty_subSums (hArity : σ.Arity addOp = 2)
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
      have hne : T'.Nonempty := nonempty_iff_ne_empty.mpr (mem_erase.mp hT').1
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
      have := add_one_le_two_pow b
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
        rw [hT_sing]
        have heq : (fun x => ∑ j ∈ ({Fin.last b} : Finset (Fin (b + 1))), v j x) =
            v (Fin.last b) := by
          funext x
          exact sum_singleton (fun j => v j x) (Fin.last b)
        rw [heq]
        exact Or.inl (hv (Fin.last b))
      · refine Or.inr (Or.inr ?_)
        rw [Set.mem_iUnion₂]
        refine ⟨T', mem_erase.mpr ⟨hT'ne.ne_empty, mem_univ T'⟩, ?_⟩
        funext x
        rw [hT_decomp, sum_insert (by simp [Fin.castSucc_ne_last]), sum_map]
        rfl
    · have hT_decomp : T = T'.map Fin.castSuccEmb := by
        ext k
        refine Fin.lastCases ?_ (fun j => ?_) k
        · simp [T', hlast]
        · simp [T']
      have hT'ne : T'.Nonempty := by
        rcases T'.eq_empty_or_nonempty with h0 | hne
        · exfalso
          rw [h0, map_empty] at hT_decomp
          exact Finset.Nonempty.ne_empty hT hT_decomp
        · exact hne
      refine Or.inr (Or.inl ⟨T', hT'ne, ?_⟩)
      funext x
      rw [hT_decomp, sum_map]
      rfl

private theorem div_lt_ceilDiv {j m p : ℕ} (hj : j < m) (hp : 0 < p) :
    j / p < m ⌈/⌉ p :=
  (Nat.div_lt_iff_lt_mul hp).mpr <| by
    rw [mul_comm]
    exact lt_of_lt_of_le hj ((ceilDiv_le_iff_le_smul hp).mp le_rfl)

/-- Partition `Fin k` into `k ⌈/⌉ width` blocks of length at most `width` and synthesize every
nonempty block subset sum within `(k * 2 ^ width) / width` binary addition gates. -/
private def blockIndices (k width q : ℕ) : Finset (Fin k) :=
  univ.filter fun j : Fin k => j.1 / width = q

private theorem sum_card_blockIndices (k width : ℕ) (hw : 0 < width) :
    ∑ q ∈ range (k ⌈/⌉ width), #(blockIndices k width q) = k := by
  simpa only [blockIndices, card_univ, Fintype.card_fin] using
    (card_eq_sum_card_fiberwise (s := univ) (t := range (k ⌈/⌉ width))
      (f := fun j : Fin k => j.1 / width) fun j _ =>
        mem_range.mpr (div_lt_ceilDiv j.isLt hw)).symm

private theorem card_blockIndices_le (k width q : ℕ) (hw : 0 < width) :
    #(blockIndices k width q) ≤ width := by
  have hinj : Set.InjOn (fun j : Fin k => (⟨j.1 % width, Nat.mod_lt _ hw⟩ : Fin width))
      (blockIndices k width q) := by
    intro j₁ hj₁ j₂ hj₂ heq
    have hq₁ : j₁.1 / width = q := (mem_filter.mp hj₁).2
    have hq₂ : j₂.1 / width = q := (mem_filter.mp hj₂).2
    have hm : j₁.1 % width = j₂.1 % width := congrArg Fin.val heq
    apply Fin.ext
    rw [← Nat.div_add_mod j₁.1 width, ← Nat.div_add_mod j₂.1 width, hq₁, hq₂, hm]
  exact (card_le_card_of_injOn _ (fun _ _ => mem_univ _) hinj).trans_eq (by simp)

/-- All nonempty subset sums within each width-`width` block of `v : Fin k → (Fin n → G) → G`
cost at most `(k * 2 ^ width) / width` binary addition gates. -/
private theorem all_group_subSums {k width : ℕ} (hw : 0 < width)
    (hArity : σ.Arity addOp = 2)
    (hEval : ∀ args : Fin (σ.Arity addOp) → G,
      I addOp args = args ⟨0, by omega⟩ + args ⟨1, by omega⟩)
    (hZeroW : w addOp = 0) {s : Set ((Fin n → G) → G)}
    (v : Fin k → (Fin n → G) → G) (hv : ∀ j, v j ∈ s) :
    CostSynthesis I w s
      {f | ∃ (q : ℕ) (T : Finset (Fin k)),
        T.Nonempty ∧ (∀ j ∈ T, j.1 / width = q) ∧ f = fun x => ∑ j ∈ T, v j x}
      ((k * 2 ^ width) / width) 0 := by
  let B (q : ℕ) := blockIndices k width q
  let emb (q : ℕ) : Fin #(B q) ↪o Fin k := (B q).orderEmbOfFin rfl
  let blockTarget (q : ℕ) : Set ((Fin n → G) → G) :=
    {f | ∃ T' : Finset (Fin #(B q)), T'.Nonempty ∧ f = fun x => ∑ i ∈ T', v (emb q i) x}
  have hq (q : ℕ) : CostSynthesis I w s (blockTarget q) (2 ^ #(B q) - #(B q) - 1) 0 :=
    block_nonempty_subSums hArity hEval hZeroW (fun i => v (emb q i)) fun i => hv (emb q i)
  have hall := CostSynthesis.biUnion (range (k ⌈/⌉ width)) blockTarget
    (fun q => 2 ^ #(B q) - #(B q) - 1) (fun _ => 0) fun q _ => hq q
  have hsum_le :
      ∑ q ∈ range (k ⌈/⌉ width), (2 ^ #(B q) - #(B q) - 1) ≤ (k * 2 ^ width) / width := by
    apply (Nat.le_div_iff_mul_le hw).mpr
    rw [mul_comm, mul_sum]
    calc ∑ q ∈ range (k ⌈/⌉ width), width * (2 ^ #(B q) - #(B q) - 1)
        ≤ ∑ q ∈ range (k ⌈/⌉ width), #(B q) * 2 ^ width :=
          sum_le_sum fun q _ => mul_sub_two_pow_le (card_blockIndices_le k width q hw)
      _ = (∑ q ∈ range (k ⌈/⌉ width), #(B q)) * 2 ^ width := (sum_mul _ _ _).symm
      _ = k * 2 ^ width := by rw [sum_card_blockIndices k width hw]
  refine hall.mono Set.Subset.rfl ?_ hsum_le (by simp)
  rintro _ ⟨q, T, hT, hTq, rfl⟩
  obtain ⟨j₀, hj₀⟩ := hT
  have hq_lt : q < k ⌈/⌉ width := hTq j₀ hj₀ ▸ div_lt_ceilDiv j₀.isLt hw
  rw [Set.mem_iUnion₂]
  let T' : Finset (Fin #(B q)) := univ.filter fun i => emb q i ∈ T
  have hT_map : T'.map (emb q).toEmbedding = T := by
    ext j
    simp only [T', mem_map, mem_filter, mem_univ, true_and, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hjT
      have hjB : j ∈ B q := mem_filter.mpr ⟨mem_univ j, hTq j hjT⟩
      have hjRange : j ∈ Set.range (emb q) := by rwa [range_orderEmbOfFin]
      obtain ⟨i, rfl⟩ := hjRange
      exact ⟨i, hjT, rfl⟩
  have hT'ne : T'.Nonempty := by
    rcases T'.eq_empty_or_nonempty with h0 | hne
    · exfalso
      rw [h0, map_empty] at hT_map
      exact notMem_empty j₀ (hT_map ▸ hj₀)
    · exact hne
  refine ⟨q, mem_range.mpr hq_lt, T', hT'ne, ?_⟩
  funext x
  rw [← hT_map, sum_map]
  rfl

end AddPrimitives

/-! #### Section column-pairing partition -/

section SectionPairing

variable {Col : Type*} [Fintype Col] {m : ℕ}

/-- Rows in horizontal section `u` that have `true` in column `c`. -/
private def activeRows (hasCol : Fin m → Col → Bool) (p u : ℕ) (c : Col) : Finset (Fin m) :=
  univ.filter fun r : Fin m => r.1 / p = u ∧ hasCol r c = true

/-- Columns in which rows `r₁ < r₂` of section `u` form one of the consecutive pairs of `1`s. -/
private def pairedCols (hasCol : Fin m → Col → Bool) (p u : ℕ) (r₁ r₂ : Fin m) : Finset Col :=
  univ.filter fun c : Col =>
    ∃ t : Fin (#(activeRows hasCol p u c) / 2),
      (activeRows hasCol p u c).orderEmbOfFin rfl
        ⟨2 * t.1, by have := t.isLt; omega⟩ = r₁ ∧
      (activeRows hasCol p u c).orderEmbOfFin rfl
        ⟨2 * t.1 + 1, by have := t.isLt; omega⟩ = r₂

/-- Columns in which row `r` is the unique unpaired leftover `1` in its section `r.1 / p`. -/
private def oddCols (hasCol : Fin m → Col → Bool) (p : ℕ) (r : Fin m) : Finset Col :=
  univ.filter fun c : Col =>
    ∃ h : 2 * (#(activeRows hasCol p (r.1 / p) c) / 2) < #(activeRows hasCol p (r.1 / p) c),
      (activeRows hasCol p (r.1 / p) c).orderEmbOfFin rfl
        ⟨2 * (#(activeRows hasCol p (r.1 / p) c) / 2), h⟩ = r

private theorem mem_pairedCols_imp {hasCol : Fin m → Col → Bool} {p u : ℕ} {r₁ r₂ : Fin m}
    {c : Col} (hc : c ∈ pairedCols hasCol p u r₁ r₂) :
    r₁ < r₂ ∧ r₁.1 / p = u ∧ r₂.1 / p = u ∧ hasCol r₁ c = true ∧ hasCol r₂ c = true := by
  unfold pairedCols at hc
  rw [mem_filter] at hc
  obtain ⟨_, t, hr₁, hr₂⟩ := hc
  let S := activeRows hasCol p u c
  have ht_lt : t.1 < #S / 2 := t.isLt
  have hlt : (⟨2 * t.1, by omega⟩ : Fin #S) < ⟨2 * t.1 + 1, by omega⟩ := by simp
  have hord : r₁ < r₂ := hr₁ ▸ hr₂ ▸ (S.orderEmbOfFin rfl).strictMono hlt
  have hm₁ : r₁ ∈ S := hr₁ ▸ S.orderEmbOfFin_mem rfl _
  have hm₂ : r₂ ∈ S := hr₂ ▸ S.orderEmbOfFin_mem rfl _
  obtain ⟨_, hu₁, hc₁⟩ := mem_filter.mp hm₁
  obtain ⟨_, hu₂, hc₂⟩ := mem_filter.mp hm₂
  exact ⟨hord, hu₁, hu₂, hc₁, hc₂⟩

private theorem mem_oddCols_imp {hasCol : Fin m → Col → Bool} {p : ℕ} {r : Fin m} {c : Col}
    (hc : c ∈ oddCols hasCol p r) : hasCol r c = true := by
  obtain ⟨_, h, hr⟩ := mem_filter.mp hc
  set S := activeRows hasCol p (r.1 / p) c
  have hm : S.orderEmbOfFin rfl ⟨2 * (#S / 2), h⟩ ∈ S := S.orderEmbOfFin_mem rfl _
  rw [hr] at hm
  exact (mem_filter.mp hm).2.2

/-- Other rows in the same horizontal section of height `p` as row `r`. -/
private def sectionPeers (p : ℕ) (r : Fin m) : Finset (Fin m) :=
  univ.filter fun r' : Fin m => r'.1 / p = r.1 / p ∧ r' ≠ r

private theorem card_sectionPeers_le {p : ℕ} (hp : 0 < p) (r : Fin m) :
    #(sectionPeers p r) ≤ p - 1 := by
  have hpeers_eq : sectionPeers p r = (blockIndices m p (r.1 / p)).erase r := by
    ext r'
    simp only [sectionPeers, blockIndices, mem_filter, mem_univ, true_and, mem_erase]
    tauto
  have hr_mem : r ∈ blockIndices m p (r.1 / p) := mem_filter.mpr ⟨mem_univ r, rfl⟩
  rw [hpeers_eq, card_erase_of_mem hr_mem]
  exact Nat.sub_le_sub_right (card_blockIndices_le m p (r.1 / p) hp) 1

/-- Every row's active columns partition into its paired columns with peers in the same section and
its odd-leftover columns. This holds in any additive commutative monoid, without cancellation. -/
private theorem sum_filter_hasCol_eq {G : Type*} [AddCommMonoid G]
    (hasCol : Fin m → Col → Bool) (p : ℕ) (val : Col → G) (r : Fin m) :
    (∑ c with hasCol r c = true, val c) =
      (∑ r' ∈ sectionPeers p r,
        ∑ c ∈ pairedCols hasCol p (r.1 / p) (min r r') (max r r'), val c) +
      ∑ c ∈ oddCols hasCol p r, val c := by
  classical
  let peerSet (r' : Fin m) : Finset Col :=
    pairedCols hasCol p (r.1 / p) (min r r') (max r r')
  have hdisj_peers : (sectionPeers p r : Set (Fin m)).PairwiseDisjoint peerSet := by
    intro r₁ hr₁ r₂ hr₂ hne
    change Disjoint (peerSet r₁) (peerSet r₂)
    rw [Finset.disjoint_left]
    intro c hc₁ hc₂
    dsimp only [peerSet, pairedCols] at hc₁ hc₂
    rw [mem_filter] at hc₁ hc₂
    obtain ⟨_, t₁, ha₁, hb₁⟩ := hc₁
    obtain ⟨_, t₂, ha₂, hb₂⟩ := hc₂
    let S := activeRows hasCol p (r.1 / p) c
    let emb := S.orderEmbOfFin rfl
    have ht₁_lt : t₁.1 < #S / 2 := t₁.isLt
    have ht₂_lt : t₂.1 < #S / 2 := t₂.isLt
    have ha₁' : emb ⟨2 * t₁.1, by omega⟩ = min r r₁ := ha₁
    have hb₁' : emb ⟨2 * t₁.1 + 1, by omega⟩ = max r r₁ := hb₁
    have ha₂' : emb ⟨2 * t₂.1, by omega⟩ = min r r₂ := ha₂
    have hb₂' : emb ⟨2 * t₂.1 + 1, by omega⟩ = max r r₂ := hb₂
    have h₁ : r = emb ⟨2 * t₁.1, by omega⟩ ∨ r = emb ⟨2 * t₁.1 + 1, by omega⟩ := by
      rcases min_cases r r₁ with ⟨hm, _⟩ | ⟨hm, _⟩
      · exact Or.inl (ha₁'.trans hm).symm
      · have hM : max r r₁ = r := max_eq_left (min_eq_right_iff.mp hm)
        exact Or.inr (hb₁'.trans hM).symm
    have h₂ : r = emb ⟨2 * t₂.1, by omega⟩ ∨ r = emb ⟨2 * t₂.1 + 1, by omega⟩ := by
      rcases min_cases r r₂ with ⟨hm, _⟩ | ⟨hm, _⟩
      · exact Or.inl (ha₂'.trans hm).symm
      · have hM : max r r₂ = r := max_eq_left (min_eq_right_iff.mp hm)
        exact Or.inr (hb₂'.trans hM).symm
    have ht : t₁ = t₂ := by
      rcases h₁ with hr_e₁ | hr_o₁ <;> rcases h₂ with hr_e₂ | hr_o₂
      · have hv := congrArg Fin.val (emb.injective (hr_e₁.symm.trans hr_e₂))
        dsimp only at hv
        exact Fin.ext (by omega)
      · have hv := congrArg Fin.val (emb.injective (hr_e₁.symm.trans hr_o₂))
        dsimp only at hv
        omega
      · have hv := congrArg Fin.val (emb.injective (hr_o₁.symm.trans hr_e₂))
        dsimp only at hv
        omega
      · have hv := congrArg Fin.val (emb.injective (hr_o₁.symm.trans hr_o₂))
        dsimp only at hv
        exact Fin.ext (by omega)
    subst ht
    have hmin_eq : min r r₁ = min r r₂ := ha₁.symm.trans ha₂
    have hmax_eq : max r r₁ = max r r₂ := hb₁.symm.trans hb₂
    have hne₁ : r₁ ≠ r := (mem_filter.mp hr₁).2.2
    have hne₂ : r₂ ≠ r := (mem_filter.mp hr₂).2.2
    apply hne
    rcases lt_trichotomy r r₁ with hlt₁ | rfl | hgt₁
    · rw [min_eq_left hlt₁.le] at hmin_eq
      rw [max_eq_right hlt₁.le] at hmax_eq
      rcases lt_trichotomy r r₂ with hlt₂ | rfl | hgt₂
      · rw [max_eq_right hlt₂.le] at hmax_eq
        exact hmax_eq
      · exact (hne₂ rfl).elim
      · rw [min_eq_right hgt₂.le] at hmin_eq
        exact (hne₂ hmin_eq.symm).elim
    · exact (hne₁ rfl).elim
    · rw [min_eq_right hgt₁.le] at hmin_eq
      rcases lt_trichotomy r r₂ with hlt₂ | rfl | hgt₂
      · rw [min_eq_left hlt₂.le] at hmin_eq
        exact (hne₁ hmin_eq).elim
      · exact (hne₂ rfl).elim
      · rw [min_eq_right hgt₂.le] at hmin_eq
        exact hmin_eq
  rw [← sum_biUnion hdisj_peers]
  have hdisj_odd : Disjoint ((sectionPeers p r).biUnion peerSet) (oddCols hasCol p r) := by
    rw [Finset.disjoint_left]
    intro c hc_pair hc_odd
    rw [mem_biUnion] at hc_pair
    obtain ⟨r', _, hc_p⟩ := hc_pair
    dsimp only [peerSet, pairedCols, oddCols] at hc_p hc_odd
    rw [mem_filter] at hc_p hc_odd
    obtain ⟨_, t, ha, hb⟩ := hc_p
    obtain ⟨_, hodd_lt, hodd_eq⟩ := hc_odd
    let S := activeRows hasCol p (r.1 / p) c
    let emb := S.orderEmbOfFin rfl
    have ht_lt : t.1 < #S / 2 := t.isLt
    rcases min_cases r r' with ⟨hm, _⟩ | ⟨hm, _⟩
    · have heq : emb ⟨2 * t.1, by omega⟩ = emb ⟨2 * (#S / 2), hodd_lt⟩ :=
        (ha.trans hm).trans hodd_eq.symm
      have hv := congrArg Fin.val (emb.injective heq)
      dsimp only at hv
      omega
    · have hM : max r r' = r := max_eq_left (min_eq_right_iff.mp hm)
      have heq : emb ⟨2 * t.1 + 1, by omega⟩ = emb ⟨2 * (#S / 2), hodd_lt⟩ :=
        (hb.trans hM).trans hodd_eq.symm
      have hv := congrArg Fin.val (emb.injective heq)
      dsimp only at hv
      omega
  rw [← sum_union hdisj_odd]
  congr 1
  ext c
  simp only [mem_filter, mem_univ, true_and, mem_union, mem_biUnion]
  constructor
  · intro hc
    set S := activeRows hasCol p (r.1 / p) c with hS_def
    let emb := S.orderEmbOfFin rfl
    have hrS : r ∈ S := mem_filter.mpr ⟨mem_univ r, rfl, hc⟩
    have hrRange : r ∈ Set.range emb := by rwa [range_orderEmbOfFin]
    obtain ⟨idx, hidx⟩ := hrRange
    by_cases hlt : idx.1 < 2 * (#S / 2)
    · refine Or.inl ?_
      let t : Fin (#S / 2) := ⟨idx.1 / 2, by omega⟩
      by_cases heven : idx.1 % 2 = 0
      · let r' := emb ⟨2 * t.1 + 1, by have := t.isLt; omega⟩
        have hr_eq : emb ⟨2 * t.1, by have := t.isLt; omega⟩ = r := by
          refine (congrArg emb ?_).trans hidx
          exact Fin.ext (by dsimp [t]; omega)
        have hlt_rr' : r < r' := by
          rw [← hr_eq]
          exact emb.strictMono (by simp : (⟨2 * t.1, _⟩ : Fin #S) < ⟨2 * t.1 + 1, _⟩)
        have hr'S : r' ∈ S := S.orderEmbOfFin_mem rfl _
        refine ⟨r', mem_filter.mpr ⟨mem_univ r', (mem_filter.mp hr'S).2.1, hlt_rr'.ne'⟩, ?_⟩
        dsimp only [peerSet]
        rw [min_eq_left hlt_rr'.le, max_eq_right hlt_rr'.le]
        exact mem_filter.mpr ⟨mem_univ c, t, hr_eq, rfl⟩
      · let r' := emb ⟨2 * t.1, by have := t.isLt; omega⟩
        have hr_eq : emb ⟨2 * t.1 + 1, by have := t.isLt; omega⟩ = r := by
          refine (congrArg emb ?_).trans hidx
          exact Fin.ext (by dsimp [t]; omega)
        have hlt_r'r : r' < r := by
          rw [← hr_eq]
          exact emb.strictMono (by simp : (⟨2 * t.1, _⟩ : Fin #S) < ⟨2 * t.1 + 1, _⟩)
        have hr'S : r' ∈ S := S.orderEmbOfFin_mem rfl _
        refine ⟨r', mem_filter.mpr ⟨mem_univ r', (mem_filter.mp hr'S).2.1, hlt_r'r.ne⟩, ?_⟩
        dsimp only [peerSet]
        rw [min_eq_right hlt_r'r.le, max_eq_left hlt_r'r.le]
        exact mem_filter.mpr ⟨mem_univ c, t, rfl, hr_eq⟩
    · refine Or.inr ?_
      have hidx_eq : idx.1 = 2 * (#S / 2) := by
        have := idx.isLt
        omega
      have hodd_lt : 2 * (#S / 2) < #S := hidx_eq ▸ idx.isLt
      refine mem_filter.mpr ⟨mem_univ c, hodd_lt, ?_⟩
      refine (congrArg emb ?_).trans hidx
      exact Fin.ext hidx_eq.symm
  · rintro (⟨r', _, hc_p⟩ | hc_odd)
    · obtain ⟨_, _, _, hc₁, hc₂⟩ := mem_pairedCols_imp hc_p
      rcases min_cases r r' with ⟨hm, _⟩ | ⟨hm, _⟩
      · exact hm ▸ hc₁
      · have hM : max r r' = r := max_eq_left (min_eq_right_iff.mp hm)
        exact hM ▸ hc₂
    · exact mem_oddCols_imp hc_odd

/-- Twice the total number of paired columns across all sections is at most the weight of
`hasCol`. -/
private theorem two_mul_sum_card_pairedCols_le (hasCol : Fin m → Col → Bool) {p : ℕ} (hp : 0 < p) :
    2 * (∑ u ∈ range (m ⌈/⌉ p), ∑ pair : Fin m × Fin m,
      #(pairedCols hasCol p u pair.1 pair.2)) ≤
      ∑ r : Fin m, #{c : Col | hasCol r c = true} := by
  classical
  have hsec_sum (u : ℕ) :
      ∑ pair : Fin m × Fin m, #(pairedCols hasCol p u pair.1 pair.2) =
        ∑ c : Col, #(activeRows hasCol p u c) / 2 := by
    simp only [pairedCols, card_filter]
    rw [sum_comm]
    refine sum_congr rfl fun c _ => ?_
    set S := activeRows hasCol p u c
    let f : Fin (#S / 2) → Fin m × Fin m := fun t =>
      (S.orderEmbOfFin rfl ⟨2 * t.1, by have := t.isLt; omega⟩,
        S.orderEmbOfFin rfl ⟨2 * t.1 + 1, by have := t.isLt; omega⟩)
    have hf_inj : Function.Injective f := by
      intro t₁ t₂ heq
      have h₁ := congrArg Prod.fst heq
      have h₂ := congrArg Fin.val ((S.orderEmbOfFin rfl).injective h₁)
      exact Fin.ext (by dsimp at h₂; omega)
    have hcard_img : #(univ.image f) = #S / 2 := by
      rw [card_image_of_injective _ hf_inj, card_univ, Fintype.card_fin]
    have hsum_img :
        (∑ pair : Fin m × Fin m,
          if ∃ t : Fin (#S / 2),
            S.orderEmbOfFin rfl ⟨2 * t.1, by have := t.isLt; omega⟩ = pair.1 ∧
            S.orderEmbOfFin rfl ⟨2 * t.1 + 1, by have := t.isLt; omega⟩ = pair.2
          then 1 else 0) = #(univ.image f) := by
      rw [sum_boole, Nat.cast_id]
      congr 1
      ext ⟨r₁, r₂⟩
      simp only [mem_filter, mem_univ, true_and, mem_image, f, Prod.mk.injEq]
    exact hsum_img.trans hcard_img
  calc 2 * ∑ u ∈ range (m ⌈/⌉ p), ∑ pair : Fin m × Fin m, #(pairedCols hasCol p u pair.1 pair.2)
      = 2 * ∑ u ∈ range (m ⌈/⌉ p), ∑ c : Col, #(activeRows hasCol p u c) / 2 := by
        congr 1
        exact sum_congr rfl fun u _ => hsec_sum u
    _ = ∑ u ∈ range (m ⌈/⌉ p), ∑ c : Col, 2 * (#(activeRows hasCol p u c) / 2) := by
        rw [mul_sum]
        exact sum_congr rfl fun u _ => mul_sum _ _ _
    _ ≤ ∑ u ∈ range (m ⌈/⌉ p), ∑ c : Col, #(activeRows hasCol p u c) :=
        sum_le_sum fun u _ => sum_le_sum fun c _ => Nat.mul_div_le _ 2
    _ = ∑ c : Col, ∑ u ∈ range (m ⌈/⌉ p), #(activeRows hasCol p u c) := sum_comm
    _ = ∑ c : Col, #{r : Fin m | hasCol r c = true} := by
        refine sum_congr rfl fun c _ => ?_
        have hpart := card_eq_sum_card_fiberwise
          (s := univ.filter fun r : Fin m => hasCol r c = true)
          (t := range (m ⌈/⌉ p)) (f := fun r : Fin m => r.1 / p)
          fun r _ => mem_range.mpr (div_lt_ceilDiv r.isLt hp)
        rw [hpart]
        refine sum_congr rfl fun u _ => congrArg card ?_
        ext r
        simp only [activeRows, mem_filter, mem_univ, true_and]
        tauto
    _ = ∑ r : Fin m, #{c : Col | hasCol r c = true} := by
        simp only [card_filter]
        exact sum_comm

/-- The total number of odd-leftover columns across all rows is at most `(m ⌈/⌉ p) * |Col|`. -/
private theorem sum_card_oddCols_le (hasCol : Fin m → Col → Bool) {p : ℕ} (hp : 0 < p) :
    (∑ r : Fin m, #(oddCols hasCol p r)) ≤ (m ⌈/⌉ p) * Fintype.card Col := by
  rw [← sum_fiberwise_of_maps_to (t := range (m ⌈/⌉ p))
    fun r _ => mem_range.mpr (div_lt_ceilDiv r.isLt hp)]
  calc ∑ u ∈ range (m ⌈/⌉ p),
        ∑ r ∈ univ.filter (fun r : Fin m => r.1 / p = u), #(oddCols hasCol p r)
      ≤ ∑ _u ∈ range (m ⌈/⌉ p), Fintype.card Col := by
        refine sum_le_sum fun u _ => ?_
        simp only [oddCols, card_filter]
        rw [sum_comm]
        calc ∑ c : Col, ∑ r ∈ univ.filter (fun r : Fin m => r.1 / p = u),
              (if ∃ h : 2 * (#(activeRows hasCol p (r.1 / p) c) / 2) <
                  #(activeRows hasCol p (r.1 / p) c),
                (activeRows hasCol p (r.1 / p) c).orderEmbOfFin rfl ⟨_, h⟩ = r then 1 else 0)
            ≤ ∑ _c : Col, 1 := by
              refine sum_le_sum fun c _ => ?_
              let S := activeRows hasCol p u c
              by_cases hlt : 2 * (#S / 2) < #S
              · let r₀ := S.orderEmbOfFin rfl ⟨2 * (#S / 2), hlt⟩
                have hr₀_sec : r₀.1 / p = u := (mem_filter.mp (S.orderEmbOfFin_mem rfl _)).2.1
                rw [sum_eq_single r₀]
                · simp only [hr₀_sec]
                  split_ifs
                  · exact le_rfl
                  · exact Nat.zero_le 1
                · intro r hr hne
                  have hr_u : r.1 / p = u := (mem_filter.mp hr).2
                  rw [ite_eq_right]
                  rintro ⟨h', heq⟩
                  simp only [hr_u] at h' heq
                  exact hne heq.symm
                · intro habs
                  exact (habs (mem_filter.mpr ⟨mem_univ r₀, hr₀_sec⟩)).elim
              · rw [sum_eq_zero]
                · exact Nat.zero_le 1
                · intro r hr
                  have hr_u : r.1 / p = u := (mem_filter.mp hr).2
                  rw [ite_eq_right]
                  rintro ⟨h', _⟩
                  simp only [hr_u] at h'
                  exact hlt h'
          _ = Fintype.card Col := by simp
    _ = (m ⌈/⌉ p) * Fintype.card Col := by simp

end SectionPairing

end Engine

/-! ### Proof of Lemma 1 (Explicit active-square additive matrix bound) -/

namespace Additive

section MatrixSynthesis

variable {G : Type*} [AddCommMonoid G] {m n : ℕ}

private def fullBlockEmb {n s : ℕ} (q : Fin (n / s)) : Fin s ↪ Fin n where
  toFun a := ⟨q.1 * s + a.1, by
    have hq : (q.1 + 1) * s ≤ n :=
      (Nat.mul_le_mul_right s (Nat.succ_le_of_lt q.isLt)).trans (Nat.div_mul_le_self n s)
    have := a.isLt
    nlinarith⟩
  inj' a₁ a₂ h := Fin.ext (by
    have hv : q.1 * s + a₁.1 = q.1 * s + a₂.1 := congrArg Fin.val h
    omega)

private theorem fullBlockEmb_div {n s : ℕ} (q : Fin (n / s)) (a : Fin s) :
    (fullBlockEmb q a).1 / s = q.1 := by
  have hs : 0 < s := Nat.zero_lt_of_lt a.isLt
  change (q.1 * s + a.1) / s = q.1
  rw [mul_comm, Nat.mul_add_div hs, Nat.div_eq_of_lt a.isLt, add_zero]

/-- Subset of `Fin s` where row `r` of `A` has `true` in full width-`s` block `q < n / s`. -/
private def fullRowPattern (A : Matrix (Fin m) (Fin n) Bool) (s : ℕ) (r : Fin m)
    (q : Fin (n / s)) : Finset (Fin s) :=
  univ.filter fun a : Fin s => A r (fullBlockEmb q a) = true

/-- Columns of the compressed full-block matrix: pairs `(q, T)` with `q < n / s` and `T` a nonempty
subset of `Fin s`. -/
private abbrev FullCol (n s : ℕ) := Fin (n / s) × {T : Finset (Fin s) // T.Nonempty}

private theorem card_nonempty_finset_fin (s : ℕ) :
    Fintype.card {T : Finset (Fin s) // T.Nonempty} = 2 ^ s - 1 := by
  have heq : univ.filter (fun T : Finset (Fin s) => T.Nonempty) = univ.erase ∅ := by
    ext T
    simp [nonempty_iff_ne_empty]
  rw [Fintype.card_subtype, heq, card_erase_of_mem (mem_univ ∅), card_univ,
    Fintype.card_finset, Fintype.card_fin]

private theorem card_fullCol_le (n s : ℕ) (hs : 0 < s) :
    Fintype.card (FullCol n s) ≤ 2 ^ s * (n ⌈/⌉ s) := by
  have hdiv : n / s ≤ n ⌈/⌉ s := by
    apply (Nat.div_le_iff_le_mul_add_pred hs).mpr
    have hceil : n ≤ s * (n ⌈/⌉ s) := (ceilDiv_le_iff_le_smul hs).mp le_rfl
    nlinarith
  rw [Fintype.card_prod, Fintype.card_fin, Additive.card_nonempty_finset_fin]
  calc (n / s) * (2 ^ s - 1) ≤ (n ⌈/⌉ s) * 2 ^ s :=
        Nat.mul_le_mul hdiv (Nat.sub_le _ _)
    _ = 2 ^ s * (n ⌈/⌉ s) := mul_comm _ _

private def hasFullCol (A : Matrix (Fin m) (Fin n) Bool) (s : ℕ) (r : Fin m)
    (c : FullCol n s) : Bool :=
  decide (fullRowPattern A s r c.1 = c.2.1)

/-- Each nonempty full block of width `s ≤ Nat.log 2 m + 1` in row `r` activates all `s` entries
of that block in `A.activeSquare`. -/
private theorem mul_sum_hasFullCol_le_activeSquare (A : Matrix (Fin m) (Fin n) Bool)
    {s : ℕ} (hs_log : s ≤ Nat.log 2 m + 1) :
    s * (∑ r : Fin m, #{c : FullCol n s | hasFullCol A s r c = true}) ≤ A.activeSquare := by
  have hrow (r : Fin m) :
      #{c : FullCol n s | hasFullCol A s r c = true} =
        #{q : Fin (n / s) | (fullRowPattern A s r q).Nonempty} := by
    let activeQ := univ.filter fun q : Fin (n / s) => (fullRowPattern A s r q).Nonempty
    let φ : {q : Fin (n / s) // q ∈ activeQ} → FullCol n s :=
      fun q => (q.1, ⟨fullRowPattern A s r q.1, (mem_filter.mp q.2).2⟩)
    have hφ_inj : Function.Injective φ := fun q₁ q₂ h =>
      Subtype.ext (congrArg Prod.fst h)
    have himg : univ.filter (fun c : FullCol n s => hasFullCol A s r c = true) =
        univ.image φ := by
      ext ⟨q, T, hT⟩
      simp only [hasFullCol, decide_eq_true_eq, mem_filter, mem_univ, true_and, mem_image, φ,
        Prod.mk.injEq, Subtype.mk.injEq]
      constructor
      · rintro rfl
        exact ⟨⟨q, mem_filter.mpr ⟨mem_univ q, hT⟩⟩, rfl, rfl⟩
      · rintro ⟨⟨q', _⟩, rfl, rfl⟩
        rfl
    rw [himg, card_image_of_injective _ hφ_inj, card_univ, Fintype.card_coe]
  simp_rw [hrow]
  rw [mul_sum]
  let blockPts (r : Fin m) : Finset (Fin m × Fin n) :=
    (univ.filter fun q : Fin (n / s) => (fullRowPattern A s r q).Nonempty).biUnion fun q =>
      univ.image fun a : Fin s => (r, fullBlockEmb q a)
  have hcard_pts (r : Fin m) :
      s * #{q : Fin (n / s) | (fullRowPattern A s r q).Nonempty} = #(blockPts r) := by
    dsimp only [blockPts]
    rw [card_biUnion]
    · have hcard_one (q : Fin (n / s)) :
          #(univ.image fun a : Fin s => (r, fullBlockEmb q a)) = s := by
        rw [card_image_of_injective]
        · simp
        · intro a₁ a₂ h
          exact (fullBlockEmb q).injective (congrArg Prod.snd h)
      rw [sum_congr rfl fun q _ => hcard_one q, sum_const, smul_eq_mul, mul_comm]
    · intro q₁ _ q₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro p hp₁ hp₂
      obtain ⟨a₁, _, rfl⟩ := mem_image.mp hp₁
      obtain ⟨a₂, _, heq⟩ := mem_image.mp hp₂
      have hemb : fullBlockEmb q₂ a₂ = fullBlockEmb q₁ a₁ := congrArg Prod.snd heq
      exact hne (Fin.ext (by rw [← fullBlockEmb_div q₁ a₁, ← hemb, fullBlockEmb_div q₂ a₂]))
  simp_rw [hcard_pts]
  have hdisj_rows : ((univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint blockPts := by
    intro r₁ _ r₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    dsimp only [blockPts] at hp₁ hp₂
    rw [mem_biUnion] at hp₁ hp₂
    obtain ⟨_, _, hp₁⟩ := hp₁
    obtain ⟨_, _, hp₂⟩ := hp₂
    obtain ⟨_, _, rfl⟩ := mem_image.mp hp₁
    obtain ⟨_, _, heq⟩ := mem_image.mp hp₂
    exact hne (congrArg Prod.fst heq).symm
  rw [← card_biUnion hdisj_rows]
  refine card_le_card fun p hp => ?_
  rw [mem_biUnion] at hp
  obtain ⟨r, _, hp⟩ := hp
  dsimp only [blockPts] at hp
  rw [mem_biUnion] at hp
  obtain ⟨q, hq, hp⟩ := hp
  obtain ⟨a, _, rfl⟩ := mem_image.mp hp
  obtain ⟨a₀, ha₀⟩ := (mem_filter.mp hq).2
  have hA₀ := (mem_filter.mp ha₀).2
  refine mem_filter.mpr ⟨mem_univ _, fullBlockEmb q a₀, hA₀, ?_⟩
  change Nat.dist (q.1 * s + a.1) (q.1 * s + a₀.1) ≤ Nat.log 2 m
  unfold Nat.dist
  have := a.isLt
  have := a₀.isLt
  omega

private def fullColVal {n s : ℕ} (c : FullCol n s) (x : Fin n → G) : G :=
  ∑ a ∈ c.2.1, x (fullBlockEmb c.1 a)

private def matrixPairVal (A : Matrix (Fin m) (Fin n) Bool) (s p : ℕ)
    (up : ℕ × (Fin m × Fin m)) (x : Fin n → G) : G :=
  ∑ c ∈ pairedCols (hasFullCol A s) p up.1 up.2.1 up.2.2, fullColVal c x

private def matrixOddVal (A : Matrix (Fin m) (Fin n) Bool) (s p : ℕ)
    (r : Fin m) (x : Fin n → G) : G :=
  ∑ c ∈ oddCols (hasFullCol A s) p r, fullColVal c x

private def matrixTailSet (A : Matrix (Fin m) (Fin n) Bool) (s : ℕ) (r : Fin m) :
    Finset (Fin n) :=
  univ.filter fun j : Fin n => n / s ≤ j.1 / s ∧ A r j = true

private theorem div_eq_of_mem_matrixTailSet {A : Matrix (Fin m) (Fin n) Bool} {s : ℕ}
    {r : Fin m} {j : Fin n} (hj : j ∈ matrixTailSet A s r) : j.1 / s = n / s := by
  have hge : n / s ≤ j.1 / s := (mem_filter.mp hj).2.1
  have hle : j.1 / s ≤ n / s := Nat.div_le_div_right j.isLt.le
  omega

private def matrixRowParts (A : Matrix (Fin m) (Fin n) Bool) (s p : ℕ) (r : Fin m) :
    Finset (Fin m ⊕ Bool) :=
  ((sectionPeers p r).filter fun r' =>
      (pairedCols (hasFullCol A s) p (r.1 / p) (min r r') (max r r')).Nonempty).map
        Function.Embedding.inl ∪
    (if (oddCols (hasFullCol A s) p r).Nonempty then {Sum.inr false} else ∅) ∪
    (if (matrixTailSet A s r).Nonempty then {Sum.inr true} else ∅)

private def matrixPartVal (A : Matrix (Fin m) (Fin n) Bool) (s p : ℕ) (r : Fin m) :
    Fin m ⊕ Bool → (Fin n → G) → G
  | .inl r' => matrixPairVal A s p (r.1 / p, (min r r', max r r'))
  | .inr false => matrixOddVal A s p r
  | .inr true => fun x => ∑ j ∈ matrixTailSet A s r, x j

private theorem card_matrixRowParts_le (A : Matrix (Fin m) (Fin n) Bool) (s : ℕ)
    {p : ℕ} (hp : 0 < p) (r : Fin m) :
    #(matrixRowParts A s p r) ≤ p + 1 := by
  unfold matrixRowParts
  set peerPart := ((sectionPeers p r).filter fun r' =>
      (pairedCols (hasFullCol A s) p (r.1 / p) (min r r') (max r r')).Nonempty).map
        Function.Embedding.inl
  set oddPart : Finset (Fin m ⊕ Bool) :=
    if (oddCols (hasFullCol A s) p r).Nonempty then {Sum.inr false} else ∅
  set tailPart : Finset (Fin m ⊕ Bool) :=
    if (matrixTailSet A s r).Nonempty then {Sum.inr true} else ∅
  have hc1 : #peerPart ≤ p - 1 := by
    rw [card_map]
    exact (card_le_card (filter_subset _ _)).trans (card_sectionPeers_le hp r)
  have hc2 : #oddPart ≤ 1 := by
    dsimp only [oddPart]
    split_ifs <;> simp
  have hc3 : #tailPart ≤ 1 := by
    dsimp only [tailPart]
    split_ifs <;> simp
  have hu1 := card_union_le (peerPart ∪ oddPart) tailPart
  have hu2 := card_union_le peerPart oddPart
  omega

private theorem sum_fullCol_lt_eq {m K s Q : ℕ} (A : Matrix (Fin m) (Fin K) Bool)
    (hs : 0 < s) (hQ : Q ≤ K / s) (r : Fin m) (v : Fin K → G) :
    (∑ c : FullCol K s with decide (c.1.1 < Q ∧ fullRowPattern A s r c.1 = c.2.1) = true,
      fullColVal c v) =
    ∑ j ∈ univ.filter (fun j : Fin K => j.1 / s < Q ∧ A r j = true), v j := by
  rw [sum_filter, Fintype.sum_prod_type]
  have hblocks :
      (∑ q : Fin (K / s), ∑ T : {T : Finset (Fin s) // T.Nonempty},
        if decide (q.1 < Q ∧ fullRowPattern A s r q = T.1) = true then
          fullColVal (q, T) v
        else 0) =
      ∑ q : Fin (K / s),
        if q.1 < Q then
          ∑ a ∈ fullRowPattern A s r q, v (fullBlockEmb q a)
        else 0 := by
    refine sum_congr rfl fun q _ => ?_
    by_cases hq : q.1 < Q
    · simp only [hq, true_and, ↓reduceIte]
      rcases (fullRowPattern A s r q).eq_empty_or_nonempty with hempty | hne
      · rw [hempty, sum_empty, sum_eq_zero]
        intro ⟨T, hT⟩ _
        have hneT : (∅ : Finset (Fin s)) ≠ T := hT.ne_empty.symm
        simp [hneT]
      · rw [sum_eq_single ⟨fullRowPattern A s r q, hne⟩]
        · simp [fullColVal]
        · intro ⟨T, _⟩ _ hne_sub
          have hneT : fullRowPattern A s r q ≠ T :=
            fun h => hne_sub (Subtype.ext h.symm)
          simp [hneT]
        · intro habs
          exact (habs (mem_univ _)).elim
    · simp only [hq, false_and, ↓reduceIte]
      rw [sum_eq_zero]
      intro _ _
      simp
  rw [hblocks, ← sum_filter]
  let blockJ (q : Fin (K / s)) : Finset (Fin K) :=
    (fullRowPattern A s r q).map (fullBlockEmb q)
  have hdisj_q :
      ((univ.filter fun q : Fin (K / s) => q.1 < Q) :
        Set (Fin (K / s))).PairwiseDisjoint blockJ := by
    intro q₁ _ q₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro j hj₁ hj₂
    obtain ⟨a₁, _, rfl⟩ := mem_map.mp hj₁
    obtain ⟨a₂, _, heq⟩ := mem_map.mp hj₂
    exact hne (Fin.ext (by rw [← fullBlockEmb_div q₁ a₁, ← heq, fullBlockEmb_div q₂ a₂]))
  have hbi :
      (univ.filter fun q : Fin (K / s) => q.1 < Q).biUnion blockJ =
        univ.filter (fun j : Fin K => j.1 / s < Q ∧ A r j = true) := by
    ext j
    simp only [mem_biUnion, mem_filter, mem_univ, true_and, blockJ, mem_map, fullRowPattern]
    constructor
    · rintro ⟨q, hq, a, hA, rfl⟩
      exact ⟨by rwa [fullBlockEmb_div], hA⟩
    · rintro ⟨hlt, hA⟩
      refine ⟨⟨j.1 / s, lt_of_lt_of_le hlt hQ⟩, hlt, ⟨j.1 % s, Nat.mod_lt _ hs⟩, ?_, ?_⟩
      · have heq : (j.1 / s) * s + j.1 % s = j.1 := Nat.div_add_mod' j.1 s
        convert hA using 2
        exact Fin.ext heq
      · exact Fin.ext (Nat.div_add_mod' j.1 s)
  rw [← hbi, sum_biUnion hdisj_q]
  refine sum_congr rfl fun q _ => ?_
  rw [sum_map]

private theorem sum_row_eq_fullCol_add_tail (A : Matrix (Fin m) (Fin n) Bool) {s : ℕ} (hs : 0 < s)
    (r : Fin m) (x : Fin n → G) :
    (∑ j : Fin n, if A r j then x j else 0) =
      (∑ c : FullCol n s with hasFullCol A s r c = true, fullColVal c x) +
      ∑ j ∈ matrixTailSet A s r, x j := by
  have hsplit_j :
      (∑ j : Fin n, if A r j then x j else 0) =
        (∑ j ∈ univ.filter (fun j : Fin n => j.1 / s < n / s ∧ A r j = true), x j) +
        ∑ j ∈ matrixTailSet A s r, x j := by
    unfold matrixTailSet
    rw [← sum_filter]
    have hunion :
        (univ.filter fun j : Fin n => A r j = true) =
          (univ.filter fun j : Fin n => j.1 / s < n / s ∧ A r j = true) ∪
          (univ.filter fun j : Fin n => n / s ≤ j.1 / s ∧ A r j = true) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_union]
      by_cases h : j.1 / s < n / s
      · simp [h]
      · have h' : n / s ≤ j.1 / s := Nat.le_of_not_lt h
        simp [h, h']
    rw [hunion, sum_union]
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have h1 := (mem_filter.mp hj1).2.1
    have h2 := (mem_filter.mp hj2).2.1
    omega
  rw [hsplit_j]
  congr 1
  rw [← sum_fullCol_lt_eq A hs le_rfl r x]
  refine sum_congr ?_ fun _ _ => rfl
  ext c
  simp [hasFullCol]

private theorem sum_matrixRowParts_eq (A : Matrix (Fin m) (Fin n) Bool) {s : ℕ} (hs : 0 < s)
    (p : ℕ) (r : Fin m) (x : Fin n → G) :
    (∑ k ∈ matrixRowParts A s p r, matrixPartVal A s p r k x) =
      ∑ j : Fin n, if A r j then x j else 0 := by
  unfold matrixRowParts
  set peerPart := ((sectionPeers p r).filter fun r' =>
      (pairedCols (hasFullCol A s) p (r.1 / p) (min r r') (max r r')).Nonempty).map
        Function.Embedding.inl
  set oddPart : Finset (Fin m ⊕ Bool) :=
    if (oddCols (hasFullCol A s) p r).Nonempty then {Sum.inr false} else ∅
  set tailPart : Finset (Fin m ⊕ Bool) :=
    if (matrixTailSet A s r).Nonempty then {Sum.inr true} else ∅
  have hd12 : Disjoint peerPart oddPart := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨_, _, rfl⟩ := mem_map.mp hz1
    dsimp only [oddPart] at hz2
    split_ifs at hz2 <;> simp at hz2
  have hd123 : Disjoint (peerPart ∪ oddPart) tailPart := by
    rw [Finset.disjoint_left]
    intro z hz12 hz3
    dsimp only [tailPart] at hz3
    split_ifs at hz3 with hne
    · rw [mem_singleton.mp hz3] at hz12
      rcases mem_union.mp hz12 with hz1 | hz2
      · obtain ⟨_, _, habs⟩ := mem_map.mp hz1
        nomatch habs
      · dsimp only [oddPart] at hz2
        split_ifs at hz2 <;> simp at hz2
    · exact notMem_empty _ hz3
  rw [sum_union hd123, sum_union hd12, sum_map]
  have hpeers_sum :
      (∑ r' ∈ (sectionPeers p r).filter (fun r' =>
          (pairedCols (hasFullCol A s) p (r.1 / p) (min r r') (max r r')).Nonempty),
        matrixPairVal A s p (r.1 / p, (min r r', max r r')) x) =
      ∑ r' ∈ sectionPeers p r, matrixPairVal A s p (r.1 / p, (min r r', max r r')) x := by
    rw [sum_filter]
    refine sum_congr rfl fun r' _ => ?_
    split_ifs with hne
    · rfl
    · rw [not_nonempty_iff_eq_empty] at hne
      simp [matrixPairVal, hne]
  have hodd_sum :
      (∑ k ∈ oddPart, matrixPartVal A s p r k x) = matrixOddVal A s p r x := by
    dsimp only [oddPart]
    split_ifs with hne
    · simp [matrixPartVal]
    · rw [not_nonempty_iff_eq_empty] at hne
      simp [matrixOddVal, hne]
  have htail_sum :
      (∑ k ∈ tailPart, matrixPartVal A s p r k x) = ∑ j ∈ matrixTailSet A s r, x j := by
    dsimp only [tailPart]
    split_ifs with hne
    · simp [matrixPartVal]
    · rw [not_nonempty_iff_eq_empty] at hne
      simp [hne]
  change (∑ r' ∈ (sectionPeers p r).filter _,
        matrixPairVal A s p (r.1 / p, (min r r', max r r')) x) +
      (∑ k ∈ oddPart, matrixPartVal A s p r k x) +
      (∑ k ∈ tailPart, matrixPartVal A s p r k x) = _
  rw [hpeers_sum, hodd_sum, htail_sum]
  have hfull := (sum_filter_hasCol_eq (hasFullCol A s) p (fun c => fullColVal c x) r).symm
  unfold matrixPairVal matrixOddVal
  rw [hfull, sum_row_eq_fullCol_add_tail A hs r x]

/-- **Explicit active-square additive matrix bound**
([Sergeev, Lemma 1, pp. 2–3][Sergeev2013AdditiveMultiplicative]):
over any additive commutative monoid `G`, every `m × n` Boolean matrix `A` is computed by an
additive `{0, +}`-circuit of size at most `matrixBound A s p` whenever `0 < s ≤ Nat.log 2 m + 1`
and `0 < p` (`AddCommMonoid G` supplies `0` for all-zero rows on total output wires, whereas
Sergeev's p. 2 footnote 4 states a commutative semigroup `(G, +)` and the construction here emits
zero `Op.zero` gates whenever every row of `A` has a `true` entry). -/
theorem exists_circuit_matrix_le_bound (G : Type*) [AddCommMonoid G]
    (A : Matrix (Fin m) (Fin n) Bool) {s p : ℕ} (hs : 0 < s) (hs_log : s ≤ Nat.log 2 m + 1)
    (hp : 0 < p) :
    ∃ c : Circuit signature n m,
      c.Computes (interpretation G) (fun x i => ∑ j : Fin n, if A i j then x j else 0) ∧
      c.size ≤ matrixBound A s p := by
  classical
  rcases m.eq_zero_or_pos with rfl | hm
  · exact ⟨Circuit.wiring signature Fin.elim0, fun _ => funext fun i => i.elim0, by simp⟩
  let I := interpretation G
  let w0 : Op → ℕ := fun _ => 0
  have hArity : signature.Arity Op.add = 2 := rfl
  have hEval : ∀ args : Fin (signature.Arity Op.add) → G, I Op.add args = args 0 + args 1 :=
    fun _ => rfl
  have hZeroW : w0 Op.add = 0 := rfl
  -- Step 1: All nonempty subset sums in each width-`s` input block.
  have hgroup := all_group_subSums (I := I) (w := w0) (s := inputs n) hs hArity hEval hZeroW
    (fun j (x : Fin n → G) => x j) (fun j => ⟨j, rfl⟩)
  set groupSet : Set ((Fin n → G) → G) :=
    {f | ∃ (q : ℕ) (T : Finset (Fin n)),
      T.Nonempty ∧ (∀ j ∈ T, j.1 / s = q) ∧ f = fun x => ∑ j ∈ T, x j}
  have hcolVal_mem (c : FullCol n s) : fullColVal c ∈ inputs n ∪ groupSet := by
    refine Or.inr ⟨c.1.1, c.2.1.map (fullBlockEmb c.1), c.2.2.map, ?_, ?_⟩
    · intro j hj
      obtain ⟨a, _, rfl⟩ := mem_map.mp hj
      exact fullBlockEmb_div c.1 a
    · funext x
      rw [sum_map]
      rfl
  -- Step 2: Nonempty paired sums.
  set pairIdx : Finset (ℕ × (Fin m × Fin m)) :=
    ((range (m ⌈/⌉ p)).product univ).filter fun up =>
      (pairedCols (hasFullCol A s) p up.1 up.2.1 up.2.2).Nonempty
  have hpair_step (up : ℕ × (Fin m × Fin m)) (hup : up ∈ pairIdx) :
      CostSynthesis I w0 (inputs n ∪ groupSet) {matrixPairVal A s p up}
        (#(pairedCols (hasFullCol A s) p up.1 up.2.1 up.2.2) - 1) 0 :=
    nonempty_sum_of_mem hArity hEval hZeroW _ (mem_filter.mp hup).2 fullColVal
      fun c _ => hcolVal_mem c
  have hpairs := CostSynthesis.biUnion pairIdx (fun up => {matrixPairVal A s p up})
    (fun up => #(pairedCols (hasFullCol A s) p up.1 up.2.1 up.2.2) - 1) (fun _ => 0) hpair_step
  have hpairs_cost :
      ∑ up ∈ pairIdx, (#(pairedCols (hasFullCol A s) p up.1 up.2.1 up.2.2) - 1) ≤
        A.activeSquare / (2 * s) := by
    have h₁ : ∑ up ∈ pairIdx, (#(pairedCols (hasFullCol A s) p up.1 up.2.1 up.2.2) - 1) ≤
        ∑ u ∈ range (m ⌈/⌉ p), ∑ pair : Fin m × Fin m,
          #(pairedCols (hasFullCol A s) p u pair.1 pair.2) :=
      ((sum_le_sum_of_subset (filter_subset _ _)).trans
        (sum_le_sum fun _ _ => Nat.sub_le _ _)).trans_eq (sum_product _ _ _)
    apply (Nat.le_div_iff_mul_le (Nat.mul_pos two_pos hs)).mpr
    have h₂ := two_mul_sum_card_pairedCols_le (hasFullCol A s) hp
    have h₃ := mul_sum_hasFullCol_le_activeSquare A hs_log
    nlinarith only [h₁, h₂, h₃]
  -- Step 3: Nonempty odd-one sums.
  set oddIdx : Finset (Fin m) :=
    univ.filter fun r : Fin m => (oddCols (hasFullCol A s) p r).Nonempty
  have hodd_step (r : Fin m) (hr : r ∈ oddIdx) :
      CostSynthesis I w0 (inputs n ∪ groupSet) {matrixOddVal A s p r}
        (#(oddCols (hasFullCol A s) p r) - 1) 0 :=
    nonempty_sum_of_mem hArity hEval hZeroW _ (mem_filter.mp hr).2 fullColVal
      fun c _ => hcolVal_mem c
  have hodds := CostSynthesis.biUnion oddIdx (fun r => {matrixOddVal A s p r})
    (fun r => #(oddCols (hasFullCol A s) p r) - 1) (fun _ => 0) hodd_step
  have hodds_cost :
      ∑ r ∈ oddIdx, (#(oddCols (hasFullCol A s) p r) - 1) ≤ (m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s) := by
    calc ∑ r ∈ oddIdx, (#(oddCols (hasFullCol A s) p r) - 1)
        ≤ ∑ r : Fin m, #(oddCols (hasFullCol A s) p r) :=
          (sum_le_sum_of_subset (filter_subset _ _)).trans
            (sum_le_sum fun _ _ => Nat.sub_le _ _)
      _ ≤ (m ⌈/⌉ p) * Fintype.card (FullCol n s) :=
          sum_card_oddCols_le (hasFullCol A s) hp
      _ ≤ (m ⌈/⌉ p) * (2 ^ s * (n ⌈/⌉ s)) :=
          Nat.mul_le_mul_left _ (card_fullCol_le n s hs)
      _ = (m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s) := by ring
  set stage3Set : Set ((Fin n → G) → G) :=
    inputs n ∪ (groupSet ∪
      ((⋃ up ∈ pairIdx, {matrixPairVal A s p up}) ∪ ⋃ r ∈ oddIdx, {matrixOddVal A s p r}))
  have hpre : CostSynthesis I w0 (inputs n) stage3Set
      ((n * 2 ^ s) / s + A.activeSquare / (2 * s) + (m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s)) 0 := by
    have h123 := (CostSynthesis.of_subset (I := I) (w := w0) Set.Subset.rfl).union
      (hgroup.comp (hpairs.union hodds))
    exact h123.mono Set.Subset.rfl Set.Subset.rfl
      (by linarith only [hpairs_cost, hodds_cost]) (by simp)
  -- Step 4: Row assembly.
  have hpartVal_mem (r : Fin m) (k : Fin m ⊕ Bool) (hk : k ∈ matrixRowParts A s p r) :
      matrixPartVal A s p r k ∈ stage3Set := by
    unfold matrixRowParts at hk
    rcases mem_union.mp hk with hk12 | hktail
    · rcases mem_union.mp hk12 with hkpeer | hkodd
      · obtain ⟨r', hr', rfl⟩ := mem_map.mp hkpeer
        have hne := (mem_filter.mp hr').2
        refine Or.inr (Or.inr (Or.inl ?_))
        rw [Set.mem_iUnion₂]
        exact ⟨(r.1 / p, (min r r', max r r')),
          mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (div_lt_ceilDiv r.isLt hp), mem_univ _⟩,
            hne⟩, rfl⟩
      · split_ifs at hkodd with hne
        · rw [mem_singleton.mp hkodd]
          refine Or.inr (Or.inr (Or.inr ?_))
          rw [Set.mem_iUnion₂]
          exact ⟨r, mem_filter.mpr ⟨mem_univ r, hne⟩, rfl⟩
        · exact (notMem_empty _ hkodd).elim
    · split_ifs at hktail with hne
      · rw [mem_singleton.mp hktail]
        exact Or.inr (Or.inl ⟨n / s, matrixTailSet A s r, hne,
          fun _ hj => div_eq_of_mem_matrixTailSet hj, rfl⟩)
      · exact (notMem_empty _ hktail).elim
  let rowFn (r : Fin m) (x : Fin n → G) : G := ∑ j : Fin n, if A r j then x j else 0
  set nonempRows : Finset (Fin m) := univ.filter fun r : Fin m => (matrixRowParts A s p r).Nonempty
  have hrow_synth (r : Fin m) (hr : r ∈ nonempRows) :
      CostSynthesis I w0 stage3Set {rowFn r} p 0 := by
    have hne := (mem_filter.mp hr).2
    have hs_r := nonempty_sum_of_mem hArity hEval hZeroW (matrixRowParts A s p r) hne
      (matrixPartVal A s p r) (hpartVal_mem r)
    have hfun : (fun x => ∑ k ∈ matrixRowParts A s p r, matrixPartVal A s p r k x) = rowFn r :=
      funext (sum_matrixRowParts_eq A hs p r)
    rw [hfun] at hs_r
    have hcard := card_matrixRowParts_le A s hp r
    exact hs_r.mono Set.Subset.rfl Set.Subset.rfl (by omega) le_rfl
  by_cases hall_ne : #nonempRows = m
  · have hrows := CostSynthesis.biUnion nonempRows (fun r => {rowFn r})
      (fun _ => p) (fun _ => 0) hrow_synth
    have htot := hpre.trans (hrows.mono Set.subset_union_right Set.Subset.rfl le_rfl le_rfl)
    have hall_univ : nonempRows = univ := eq_univ_of_card nonempRows (by simp [hall_ne])
    have htarget : Set.range rowFn ⊆ ⋃ r ∈ nonempRows, {rowFn r} := by
      rintro _ ⟨r, rfl⟩
      rw [hall_univ, Set.mem_iUnion₂]
      exact ⟨r, mem_univ r, rfl⟩
    have hcost :
        ((n * 2 ^ s) / s + A.activeSquare / (2 * s) + (m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s)) +
          ∑ _ ∈ nonempRows, p ≤ matrixBound A s p := by
      rw [sum_const, smul_eq_mul, hall_ne]
      unfold matrixBound
      omega
    obtain ⟨c, hc, hsize, -⟩ :=
      (htot.mono Set.Subset.rfl htarget hcost (wa' := 0) (by simp)).exists_circuit_outputs
    exact ⟨c, hc, hsize⟩
  · have hle_m1 : #nonempRows ≤ m - 1 := by
      have hle : #nonempRows ≤ m := (card_filter_le _ _).trans_eq (by simp)
      omega
    have hzero_gate : CostSynthesis I w0 stage3Set {fun _ => (0 : G)} 1 0 := by
      simpa only [I, w0, interpretation_zero] using
        CostSynthesis.gate (I := I) (w := w0) (s := stage3Set) Op.zero Fin.elim0 fun i => i.elim0
    have hrows := CostSynthesis.biUnion nonempRows (fun r => {rowFn r})
      (fun _ => p) (fun _ => 0) hrow_synth
    have htot := hpre.trans
      ((hzero_gate.union hrows).mono Set.subset_union_right Set.Subset.rfl le_rfl le_rfl)
    have htarget : Set.range rowFn ⊆ {fun _ => (0 : G)} ∪ ⋃ r ∈ nonempRows, {rowFn r} := by
      rintro _ ⟨r, rfl⟩
      by_cases hr : r ∈ nonempRows
      · refine Or.inr ?_
        rw [Set.mem_iUnion₂]
        exact ⟨r, hr, rfl⟩
      · refine Or.inl ?_
        have hempty : matrixRowParts A s p r = ∅ := by
          rcases (matrixRowParts A s p r).eq_empty_or_nonempty with h0 | hne
          · exact h0
          · exact (hr (mem_filter.mpr ⟨mem_univ r, hne⟩)).elim
        funext x
        dsimp only [rowFn]
        rw [← sum_matrixRowParts_eq A hs p r x, hempty, sum_empty]
    have hcost4 : 1 + ∑ _ ∈ nonempRows, p ≤ m * p := by
      rw [sum_const, smul_eq_mul]
      calc 1 + #nonempRows * p ≤ p + (m - 1) * p :=
            Nat.add_le_add hp (Nat.mul_le_mul_right p hle_m1)
        _ = (1 + (m - 1)) * p := by ring
        _ = m * p := by rw [Nat.add_sub_of_le hm]
    have hcost :
        ((n * 2 ^ s) / s + A.activeSquare / (2 * s) + (m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s)) +
          (1 + ∑ _ ∈ nonempRows, p) ≤ matrixBound A s p := by
      unfold matrixBound
      omega
    obtain ⟨c, hc, hsize, -⟩ :=
      (htot.mono Set.Subset.rfl htarget hcost (wa' := 0) (by simp)).exists_circuit_outputs
    exact ⟨c, hc, hsize⟩

end MatrixSynthesis

end Additive

/-! ### Shared logarithmic parameter estimates -/

section ParameterBounds

private theorem ceilDiv_div_sq_add_one_le (k : ℕ) {L : ℕ} (hL : 0 < L) :
    k ⌈/⌉ (k / L ^ 2 + 1) ≤ L ^ 2 := by
  have hp : 0 < k / L ^ 2 + 1 := Nat.succ_pos _
  rw [ceilDiv_le_iff_le_smul hp, smul_eq_mul]
  have hmod : k % L ^ 2 < L ^ 2 := Nat.mod_lt k (by positivity)
  have hdiv := Nat.div_add_mod k (L ^ 2)
  have hexp : (k / L ^ 2 + 1) * L ^ 2 = L ^ 2 * (k / L ^ 2) + L ^ 2 := by ring
  linarith

private theorem mul_ceilDiv_le_add (N : ℕ) {s : ℕ} (hs : 0 < s) :
    s * (N ⌈/⌉ s) ≤ N + s := by
  have hceil : N ⌈/⌉ s ≤ N / s + 1 := by
    rw [ceilDiv_le_iff_le_smul hs, smul_eq_mul]
    have hmod : N % s < s := Nat.mod_lt N hs
    have hdiv := Nat.div_add_mod N s
    have hexp : s * (N / s + 1) = s * (N / s) + s := by ring
    linarith
  calc s * (N ⌈/⌉ s) ≤ s * (N / s + 1) := Nat.mul_le_mul_left s hceil
    _ = s * (N / s) + s := by ring
    _ ≤ N + s := Nat.add_le_add_right (Nat.mul_div_le N s) s

private theorem exists_log_threshold (C : ℕ) :
    ∃ L₁ : ℕ, 8 ≤ L₁ ∧ C ≤ L₁ ∧
      ∀ {L : ℕ}, L₁ ≤ L → C * Nat.log 2 L ≤ L ∧ 6 * Nat.log 2 L ≤ L ∧ L ^ 2 ≤ 2 ^ L := by
  have hev := (Filter.eventually_ge_atTop (max 8 C)).and
    ((Nat.eventually_mul_log_le (max C 6) one_lt_two).and
      (Nat.eventually_mul_pow_le_pow 1 2 one_lt_two))
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨hge₀, _, _⟩ := hL₁ L₁ le_rfl
  refine ⟨L₁, le_trans (le_max_left 8 C) hge₀, le_trans (le_max_right 8 C) hge₀,
    fun {L} hL => ?_⟩
  obtain ⟨_, hlog, hpow⟩ := hL₁ L hL
  refine ⟨?_, ?_, by simpa only [one_mul] using hpow⟩
  · exact (Nat.mul_le_mul_right _ (le_max_left C 6)).trans hlog
  · exact (Nat.mul_le_mul_right _ (le_max_right C 6)).trans hlog

private theorem log_param_props {M : ℕ} (hL8 : 8 ≤ Nat.log 2 M)
    (hlog6 : 6 * Nat.log 2 (Nat.log 2 M) ≤ Nat.log 2 M)
    (hpow2 : (Nat.log 2 M) ^ 2 ≤ 2 ^ Nat.log 2 M) :
    let L := Nat.log 2 M
    let s := L - 3 * Nat.log 2 L
    0 < s ∧ s ≤ L ∧ L ≤ 2 * s ∧ 1 ≤ Nat.log 2 L ∧ L ^ 2 ≤ M ∧ L ^ 3 * 2 ^ s ≤ 8 * M := by
  dsimp only
  set L := Nat.log 2 M
  set s := L - 3 * Nat.log 2 L
  have hM0 : M ≠ 0 := by
    intro h0
    subst h0
    simp [L] at hL8
  have hpowM : 2 ^ L ≤ M := Nat.pow_log_le_self 2 hM0
  have hs_pos : 0 < s := by omega
  have hs_le : s ≤ L := Nat.sub_le _ _
  have hL_2s : L ≤ 2 * s := by omega
  have hlogL1 : 1 ≤ Nat.log 2 L :=
    Nat.le_log_of_pow_le one_lt_two (by omega : 2 ^ 1 ≤ L)
  have hL2M : L ^ 2 ≤ M := hpow2.trans hpowM
  have hL_lt : L ≤ 2 * 2 ^ Nat.log 2 L := by
    have h := Nat.lt_pow_succ_log_self one_lt_two L
    rw [pow_succ'] at h
    exact h.le
  have hcubes : (2 * 2 ^ Nat.log 2 L) ^ 3 = 8 * 2 ^ (3 * Nat.log 2 L) := by
    rw [mul_pow, ← pow_mul, mul_comm (Nat.log 2 L) 3]
    norm_num
  have hL3 : L ^ 3 * 2 ^ s ≤ 8 * M := by
    calc L ^ 3 * 2 ^ s
        ≤ (2 * 2 ^ Nat.log 2 L) ^ 3 * 2 ^ s :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hL_lt 3)
      _ = 8 * (2 ^ (3 * Nat.log 2 L) * 2 ^ s) := by
          rw [hcubes]
          ring
      _ = 8 * 2 ^ (3 * Nat.log 2 L + s) := by rw [← pow_add]
      _ = 8 * 2 ^ L := by
          congr 2
          omega
      _ ≤ 8 * M := Nat.mul_le_mul_left 8 hpowM
  exact ⟨hs_pos, hs_le, hL_2s, hlogL1, hL2M, hL3⟩

private theorem natLog_le_logb {m : ℕ} (hm : 1 ≤ m) :
    (Nat.log 2 m : ℝ) ≤ Real.logb 2 m := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
  exact_mod_cast Nat.pow_log_le_self 2 (by omega)

private theorem logb_le_natLog_add_one {m : ℕ} (hm : 1 ≤ m) :
    Real.logb 2 m ≤ (Nat.log 2 m : ℝ) + 1 := by
  have h := Nat.lt_pow_succ_log_self one_lt_two m
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity)]
  have hcast : ((Nat.log 2 m + 1 : ℕ) : ℝ) = (Nat.log 2 m : ℝ) + 1 := by push_cast; ring
  rw [← hcast, Real.rpow_natCast]
  exact_mod_cast h.le

private theorem logb_two_ge_one {m : ℕ} (hm : 2 ≤ m) :
    1 ≤ Real.logb 2 m := by
  have h1 : 1 ≤ Nat.log 2 m := Nat.le_log_of_pow_le one_lt_two hm
  exact le_trans (by exact_mod_cast h1) (natLog_le_logb (by omega))

private theorem div_two_sub_add_rem_le {M S U rem K : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hL8 : 8 ≤ Nat.log 2 M)
    (h6log : 6 * Nat.log 2 (Nat.log 2 M) ≤ Nat.log 2 M)
    (hpow2 : (Nat.log 2 M) ^ 2 ≤ 2 ^ Nat.log 2 M)
    (hClog : (⌈((4 + 2 * K : ℕ) : ℝ) / ε⌉₊ + 10) * Nat.log 2 (Nat.log 2 M) ≤ Nat.log 2 M)
    (hSU : S ≤ U)
    (hrem : (Nat.log 2 M) ^ 2 * rem ≤ K * U) :
    ((S / (2 * (Nat.log 2 M - 3 * Nat.log 2 (Nat.log 2 M))) : ℕ) : ℝ) + (rem : ℝ) ≤
      (S : ℝ) / (2 * Real.logb 2 M) + ε * ((U : ℝ) / Real.logb 2 M) := by
  have hM_ge2 : 2 ≤ M := by
    have hpow := Nat.pow_log_le_self 2 (x := M) (by rintro rfl; simp at hL8)
    have h2 : 2 ^ 1 ≤ 2 ^ Nat.log 2 M := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨hs_pos, hs_le, hL_2s, hlogL1, _, _⟩ := log_param_props hL8 h6log hpow2
  set L := Nat.log 2 M
  set s := L - 3 * Nat.log 2 L
  set logM := Real.logb 2 M
  have hlogM_pos : 0 < logM := lt_of_lt_of_le zero_lt_one (logb_two_ge_one hM_ge2)
  have hLR_pos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hsR_pos : (0 : ℝ) < s := by exact_mod_cast hs_pos
  have hlogM_hi : logM ≤ 2 * (L : ℝ) := by
    have h1 := logb_le_natLog_add_one (m := M) (by omega)
    have h2 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
    linarith
  have hSU_R : (S : ℝ) ≤ (U : ℝ) := Nat.cast_le.mpr hSU
  have hmain_part :
      ((S / (2 * s) : ℕ) : ℝ) ≤
        (S : ℝ) / (2 * logM) + (4 * (Nat.log 2 L : ℝ) / L) * ((U : ℝ) / logM) := by
    have hdiv_le : ((S / (2 * s) : ℕ) : ℝ) ≤ (S : ℝ) / (2 * s) := by
      exact_mod_cast Nat.cast_div_le (m := S) (n := 2 * s) (α := ℝ)
    have hdiff_eq :
        (S : ℝ) / (2 * s) =
          (S : ℝ) / (2 * logM) + (S : ℝ) * (logM - s) / (2 * s * logM) := by
      field_simp
      ring
    have hsR_eq : (s : ℝ) = (L : ℝ) - 3 * (Nat.log 2 L : ℝ) := by
      have hle3 : 3 * Nat.log 2 L ≤ L := by omega
      exact_mod_cast Nat.cast_sub (R := ℝ) hle3
    have hgap_nonneg : 0 ≤ logM - (s : ℝ) := by
      have hsL : (s : ℝ) ≤ L := by exact_mod_cast hs_le
      have hL_le_logM : (L : ℝ) ≤ logM := natLog_le_logb (by omega)
      linarith
    have hgap_le : logM - (s : ℝ) ≤ 4 * (Nat.log 2 L : ℝ) := by
      have h1 := logb_le_natLog_add_one (m := M) (by omega)
      have hlogL1R : (1 : ℝ) ≤ Nat.log 2 L := by exact_mod_cast hlogL1
      linarith
    have h2s_ge : (L : ℝ) ≤ 2 * (s : ℝ) := by exact_mod_cast hL_2s
    have hnum : (S : ℝ) * (logM - s) ≤ (U : ℝ) * (4 * (Nat.log 2 L : ℝ)) :=
      mul_le_mul hSU_R hgap_le hgap_nonneg (by positivity)
    have hden : (L : ℝ) * logM ≤ 2 * (s : ℝ) * logM :=
      mul_le_mul_of_nonneg_right h2s_ge hlogM_pos.le
    have hfrac :
        (S : ℝ) * (logM - s) / (2 * s * logM) ≤
          (4 * (Nat.log 2 L : ℝ) / L) * ((U : ℝ) / logM) := by
      calc (S : ℝ) * (logM - s) / (2 * s * logM)
          ≤ (U : ℝ) * (4 * (Nat.log 2 L : ℝ)) / (2 * s * logM) :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ (U : ℝ) * (4 * (Nat.log 2 L : ℝ)) / ((L : ℝ) * logM) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hden
        _ = (4 * (Nat.log 2 L : ℝ) / L) * ((U : ℝ) / logM) := by ring
    linarith
  have hrem_part :
      (rem : ℝ) ≤ ((2 * (K : ℝ)) * (Nat.log 2 L : ℝ) / L) * ((U : ℝ) / logM) := by
    have hrem_R : (L : ℝ) ^ 2 * (rem : ℝ) ≤ (K : ℝ) * (U : ℝ) := by
      have hcast : ((L ^ 2 * rem : ℕ) : ℝ) ≤ ((K * U : ℕ) : ℝ) := Nat.cast_le.mpr hrem
      push_cast at hcast
      exact hcast
    have hrem_div : (rem : ℝ) ≤ (K : ℝ) * (U : ℝ) / (L : ℝ) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hlogL1R : (1 : ℝ) ≤ Nat.log 2 L := by exact_mod_cast hlogL1
    have hstep :
        (K : ℝ) * (U : ℝ) / (L : ℝ) ^ 2 ≤
          ((2 * (K : ℝ)) * (Nat.log 2 L : ℝ) / L) * ((U : ℝ) / logM) := by
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      calc ((K : ℝ) * (U : ℝ)) * ((L : ℝ) * logM)
          = (L : ℝ) * (logM * ((K : ℝ) * (U : ℝ))) := by ring
        _ ≤ (L : ℝ) * ((2 * (L : ℝ)) * ((K : ℝ) * (U : ℝ))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hlogM_hi (by positivity)) (by positivity)
        _ = 1 * ((L : ℝ) ^ 2 * (2 * (K : ℝ) * (U : ℝ))) := by ring
        _ ≤ (Nat.log 2 L : ℝ) * ((L : ℝ) ^ 2 * (2 * (K : ℝ) * (U : ℝ))) :=
            mul_le_mul_of_nonneg_right hlogL1R (by positivity)
        _ = ((2 * (K : ℝ)) * (Nat.log 2 L : ℝ) * (U : ℝ)) * (L : ℝ) ^ 2 := by ring
    exact hrem_div.trans hstep
  set C : ℕ := ⌈((4 + 2 * K : ℕ) : ℝ) / ε⌉₊ + 10
  have hcoeff : (4 + 2 * (K : ℝ)) * (Nat.log 2 L : ℝ) / L ≤ ε := by
    have hCL_R : (C : ℝ) * (Nat.log 2 L : ℝ) ≤ L := by exact_mod_cast hClog
    have h42K_cast : ((4 + 2 * K : ℕ) : ℝ) = 4 + 2 * (K : ℝ) := by push_cast; ring
    have hC_ge : (4 + 2 * (K : ℝ)) / ε ≤ (C : ℝ) := by
      have hceil : ((4 + 2 * K : ℕ) : ℝ) / ε ≤ (⌈((4 + 2 * K : ℕ) : ℝ) / ε⌉₊ : ℝ) :=
        Nat.le_ceil _
      have hcast : (C : ℝ) = (⌈((4 + 2 * K : ℕ) : ℝ) / ε⌉₊ : ℝ) + 10 := by
        exact_mod_cast rfl
      have hle : ((4 + 2 * K : ℕ) : ℝ) / ε ≤ (C : ℝ) := by linarith
      rwa [h42K_cast] at hle
    have h42K : 4 + 2 * (K : ℝ) ≤ ε * C := by
      have hmul := (div_le_iff₀ hε).mp hC_ge
      linarith
    rw [div_le_iff₀ hLR_pos]
    calc (4 + 2 * (K : ℝ)) * (Nat.log 2 L : ℝ)
        ≤ (ε * C) * (Nat.log 2 L : ℝ) :=
          mul_le_mul_of_nonneg_right h42K (Nat.cast_nonneg _)
      _ = ε * ((C : ℝ) * (Nat.log 2 L : ℝ)) := by ring
      _ ≤ ε * L := mul_le_mul_of_nonneg_left hCL_R hε.le
  have herr := mul_le_mul_of_nonneg_right hcoeff (show 0 ≤ (U : ℝ) / logM by positivity)
  have hsum :
      (4 * (Nat.log 2 L : ℝ) / L) * ((U : ℝ) / logM) +
        ((2 * (K : ℝ)) * (Nat.log 2 L : ℝ) / L) * ((U : ℝ) / logM) =
        ((4 + 2 * (K : ℝ)) * (Nat.log 2 L : ℝ) / L) * ((U : ℝ) / logM) := by ring
  linarith

end ParameterBounds

namespace Additive

private theorem matrixRem_mul_sq_le (m n : ℕ)
    (hL8 : 8 ≤ Nat.log 2 m)
    (hlog6 : 6 * Nat.log 2 (Nat.log 2 m) ≤ Nat.log 2 m)
    (hpow2 : (Nat.log 2 m) ^ 2 ≤ 2 ^ Nat.log 2 m) :
    let L := Nat.log 2 m
    let s := L - 3 * Nat.log 2 L
    let p := m / L ^ 2 + 1
    L ^ 2 * ((n * 2 ^ s) / s + m * p + (m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s)) ≤
      34 * (m + n) ^ 2 := by
  dsimp only
  obtain ⟨hs_pos, hs_le, hL_2s, _, hL2m, hL3⟩ := log_param_props hL8 hlog6 hpow2
  set L := Nat.log 2 m
  set s := L - 3 * Nat.log 2 L
  set p := m / L ^ 2 + 1
  have hs_le_m : s ≤ m := by
    have hLL2 : L ≤ L ^ 2 := by nlinarith
    exact hs_le.trans (hLL2.trans hL2m)
  have ht1 : L ^ 2 * ((n * 2 ^ s) / s) ≤ 16 * (m + n) ^ 2 := by
    have hdiv : L * ((n * 2 ^ s) / s) ≤ 2 * (n * 2 ^ s) := by
      calc L * ((n * 2 ^ s) / s)
          ≤ (2 * s) * ((n * 2 ^ s) / s) := Nat.mul_le_mul_right _ hL_2s
        _ = 2 * (s * ((n * 2 ^ s) / s)) := by ring
        _ ≤ 2 * (n * 2 ^ s) := Nat.mul_le_mul_left 2 (Nat.mul_div_le _ s)
    calc L ^ 2 * ((n * 2 ^ s) / s)
        ≤ L ^ 3 * ((n * 2 ^ s) / s) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num))
      _ = L ^ 2 * (L * ((n * 2 ^ s) / s)) := by ring
      _ ≤ L ^ 2 * (2 * (n * 2 ^ s)) := Nat.mul_le_mul_left _ hdiv
      _ ≤ L ^ 3 * (2 * (n * 2 ^ s)) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num))
      _ = 2 * n * (L ^ 3 * 2 ^ s) := by ring
      _ ≤ 2 * n * (8 * m) := Nat.mul_le_mul_left _ hL3
      _ ≤ 16 * (m + n) ^ 2 := by nlinarith
  have ht2 : L ^ 2 * (m * p) ≤ 2 * (m + n) ^ 2 := by
    have hsq : 2 * (m + n) ^ 2 = m * m + m * m + 4 * m * n + 2 * n * n := by ring
    calc L ^ 2 * (m * (m / L ^ 2 + 1))
        = m * (L ^ 2 * (m / L ^ 2)) + m * L ^ 2 := by ring
      _ ≤ m * m + m * m :=
          Nat.add_le_add (Nat.mul_le_mul_left m (Nat.mul_div_le m (L ^ 2)))
            (Nat.mul_le_mul_left m hL2m)
      _ ≤ 2 * (m + n) ^ 2 := by rw [hsq]; omega
  have ht3 : L ^ 2 * ((m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s)) ≤ 16 * (m + n) ^ 2 := by
    have hmp : m ⌈/⌉ p ≤ L ^ 2 := ceilDiv_div_sq_add_one_le m (by omega)
    have hns : s * (n ⌈/⌉ s) ≤ n + s := mul_ceilDiv_le_add n hs_pos
    have hL2_le : L ^ 2 ≤ 2 * s * L := by nlinarith
    calc L ^ 2 * ((m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s))
        ≤ (2 * s * L) * ((m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s)) :=
          Nat.mul_le_mul_right _ hL2_le
      _ = 2 * ((m ⌈/⌉ p) * (L * 2 ^ s)) * (s * (n ⌈/⌉ s)) := by ring
      _ ≤ 2 * (L ^ 2 * (L * 2 ^ s)) * (n + s) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hmp)) hns
      _ = 2 * (L ^ 3 * 2 ^ s) * (n + s) := by ring
      _ ≤ 2 * (8 * m) * (n + m) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 hL3) (Nat.add_le_add_left hs_le_m n)
      _ ≤ 16 * (m + n) ^ 2 := by nlinarith
  calc L ^ 2 * ((n * 2 ^ s) / s + m * p + (m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s))
      = L ^ 2 * ((n * 2 ^ s) / s) + L ^ 2 * (m * p) +
          L ^ 2 * ((m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s)) := by ring
    _ ≤ 16 * (m + n) ^ 2 + 2 * (m + n) ^ 2 + 16 * (m + n) ^ 2 :=
        Nat.add_le_add (Nat.add_le_add ht1 ht2) ht3
    _ = 34 * (m + n) ^ 2 := by ring

/-- **Asymptotic active-square additive matrix bound**
([Sergeev, Lemma 1, p. 2][Sergeev2013AdditiveMultiplicative]):
for every `ε > 0`, for all sufficiently large `m + n` with `2 ≤ m`, every `m × n` Boolean matrix `A`
over any additive commutative monoid `G` is computed by an additive `{0, +}`-circuit of size at most
`A.activeSquare / (2 * Real.logb 2 m) + ε * ((m + n) ^ 2 / Real.logb 2 m)`. -/
theorem exists_circuit_matrix_le {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ {m n : ℕ}, 2 ≤ m → N₀ ≤ m + n →
      ∀ (G : Type*) [AddCommMonoid G] (A : Matrix (Fin m) (Fin n) Bool),
        ∃ c : Circuit signature n m,
          c.Computes (interpretation G) (fun x i => ∑ j : Fin n, if A i j then x j else 0) ∧
          (c.size : ℝ) ≤
            (A.activeSquare : ℝ) / (2 * Real.logb 2 m) +
              ε * ((m + n : ℝ) ^ 2 / Real.logb 2 m) := by
  let C : ℕ := ⌈((4 + 2 * 34 : ℕ) : ℝ) / ε⌉₊ + 10
  obtain ⟨L₁, hL₁8, _, hL₁⟩ := exists_log_threshold C
  let M₁ : ℕ := 2 ^ L₁
  have hM₁_ge2 : 2 ≤ M₁ := by
    have : 2 ^ 1 ≤ 2 ^ L₁ := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [M₁] using this
  let B : ℝ := (3 * (M₁ : ℝ) + 3) * Real.logb 2 M₁
  let N₀ : ℕ := M₁ + ⌈B / ε⌉₊ + 1
  refine ⟨N₀, fun {m n} hm hN₀ G _ A => ?_⟩
  have hlogm_ge1 : 1 ≤ Real.logb 2 m := logb_two_ge_one hm
  have hlogm_pos : 0 < Real.logb 2 m := lt_of_lt_of_le zero_lt_one hlogm_ge1
  by_cases hmM₁ : M₁ ≤ m
  · have hL_ge : L₁ ≤ Nat.log 2 m := Nat.le_log_of_pow_le one_lt_two hmM₁
    obtain ⟨hClog, h6log, hpow2⟩ := hL₁ hL_ge
    have hL8 : 8 ≤ Nat.log 2 m := hL₁8.trans hL_ge
    obtain ⟨hs_pos, hs_le, _, _, _, _⟩ := log_param_props hL8 h6log hpow2
    set L := Nat.log 2 m
    set s := L - 3 * Nat.log 2 L
    set p := m / L ^ 2 + 1
    obtain ⟨c, hc, hsize⟩ := exists_circuit_matrix_le_bound G A hs_pos
      (hs_le.trans (Nat.le_succ L)) (Nat.succ_pos _)
    refine ⟨c, hc, (Nat.cast_le.mpr hsize).trans ?_⟩
    set rem : ℕ := (n * 2 ^ s) / s + m * p + (m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s)
    have hmb_eq : matrixBound A s p = A.activeSquare / (2 * s) + rem := by
      unfold matrixBound rem
      ring
    rw [hmb_eq, Nat.cast_add]
    have hSU : A.activeSquare ≤ (m + n) ^ 2 :=
      A.activeSquare_le_mul.trans (by nlinarith)
    have hbound := div_two_sub_add_rem_le hε hL8 h6log hpow2 hClog hSU
      (matrixRem_mul_sq_le m n hL8 h6log hpow2)
    have hsq_cast : (((m + n) ^ 2 : ℕ) : ℝ) = (m + n : ℝ) ^ 2 := by push_cast; ring
    rw [hsq_cast] at hbound
    exact hbound
  · -- Bounded-row regime `2 ≤ m < M₁`: take `s = 1` and `p = 1`.
    have hm_lt : m < M₁ := Nat.lt_of_not_ge hmM₁
    obtain ⟨c, hc, hsize⟩ := exists_circuit_matrix_le_bound G A Nat.one_pos
      (Nat.succ_le_succ (Nat.zero_le _)) Nat.one_pos
    refine ⟨c, hc, (Nat.cast_le.mpr hsize).trans ?_⟩
    have hmb11 : matrixBound A 1 1 ≤ (3 * M₁ + 3) * (m + n) := by
      have hS_mn : A.activeSquare / 2 ≤ m * n :=
        (Nat.div_le_self _ _).trans A.activeSquare_le_mul
      unfold matrixBound
      simp only [ceilDiv_one, pow_one, Nat.div_one, mul_one]
      nlinarith
    have hcast11 : (matrixBound A 1 1 : ℝ) ≤ (3 * (M₁ : ℝ) + 3) * (m + n : ℝ) := by
      exact_mod_cast hmb11
    have hlog_le : Real.logb 2 m ≤ Real.logb 2 M₁ := by
      unfold Real.logb
      exact div_le_div_of_nonneg_right
        (Real.log_le_log (by positivity) (by exact_mod_cast hm_lt.le))
        (Real.log_nonneg (by norm_num))
    have hB_le : B ≤ ε * (m + n : ℝ) := by
      have hceil_B : B / ε ≤ (⌈B / ε⌉₊ : ℝ) := Nat.le_ceil _
      have hmn_ge : (⌈B / ε⌉₊ : ℝ) ≤ (m + n : ℝ) := by
        have : ⌈B / ε⌉₊ ≤ m + n := by omega
        exact_mod_cast this
      have hdiv : B / ε ≤ m + n := hceil_B.trans hmn_ge
      rwa [div_le_iff₀ hε, mul_comm] at hdiv
    have herr_ge : (3 * (M₁ : ℝ) + 3) * (m + n : ℝ) ≤ ε * ((m + n : ℝ) ^ 2 / Real.logb 2 m) := by
      rw [mul_div_assoc', le_div_iff₀ hlogm_pos]
      calc (3 * (M₁ : ℝ) + 3) * (m + n : ℝ) * Real.logb 2 m
          ≤ (3 * (M₁ : ℝ) + 3) * (m + n : ℝ) * Real.logb 2 M₁ :=
            mul_le_mul_of_nonneg_left hlog_le (by positivity)
        _ = B * (m + n : ℝ) := by
            dsimp only [B]
            ring
        _ ≤ (ε * (m + n : ℝ)) * (m + n : ℝ) :=
            mul_le_mul_of_nonneg_right hB_le (by positivity)
        _ = ε * (m + n : ℝ) ^ 2 := by ring
    have hS_nonneg : 0 ≤ (A.activeSquare : ℝ) / (2 * Real.logb 2 m) := by positivity
    linarith

end Additive

/-! ### The Zhegalkin Boolean basis `{⊕, ∧, 1}` and Theorem 1 (upper bound) -/

namespace Boolean.Zhegalkin

/-- Operations of the Zhegalkin (algebraic normal form) Boolean circuit basis `{⊕, ∧, 1}`. -/
inductive Op where
  /-- The Boolean constant `true` (`1`). -/
  | one
  /-- Binary exclusive-or `⊕` (`xor`, addition in `GF(2)`). -/
  | xor
  /-- Binary conjunction `∧` (`and`, multiplication in `GF(2)`). -/
  | and
  deriving DecidableEq

/-- Finite enumeration of the Zhegalkin basis operations. -/
instance : Fintype Op :=
  ⟨{.one, .xor, .and}, fun op => by cases op <;> simp⟩

/-- The Zhegalkin signature: nullary `one` and binary `xor` and `and`. -/
abbrev signature : Signature where
  Op := Op
  Arity
    | .one => 0
    | .xor | .and => 2

/-- Standard Boolean interpretation of the Zhegalkin basis `{⊕, ∧, 1}`. -/
@[expose] def interpretation : Interpretation signature Bool
  | .one, _ => true
  | .xor, x => x 0 ^^ x 1
  | .and, x => x 0 && x 1

/-- Under `interpretation`, `.one` evaluates to `true`. -/
@[simp] theorem interpretation_one (x : Fin 0 → Bool) :
    interpretation .one x = true := rfl

/-- Under `interpretation`, `.xor` evaluates to `x 0 ^^ x 1`. -/
@[simp] theorem interpretation_xor (x : Fin 2 → Bool) :
    interpretation .xor x = (x 0 ^^ x 1) := rfl

/-- Under `interpretation`, `.and` evaluates to `x 0 && x 1`. -/
@[simp] theorem interpretation_and (x : Fin 2 → Bool) :
    interpretation .and x = (x 0 && x 1) := rfl

/-- Conjunction-gate weight charging `1` for each `.and` gate and `0` for `.xor` and `.one`. -/
@[expose] def andCost : Op → ℕ
  | .and => 1
  | .one | .xor => 0

/-- A conjunction gate has `andCost` equal to `1`. -/
@[simp] theorem andCost_and : andCost .and = 1 := rfl

/-- An XOR gate has `andCost` equal to `0`. -/
@[simp] theorem andCost_xor : andCost .xor = 0 := rfl

/-- A constant-`1` gate has `andCost` equal to `0`. -/
@[simp] theorem andCost_one : andCost .one = 0 := rfl

/-- The number of conjunction gates in a `{⊕, ∧, 1}`-program is at most its total gate count. -/
theorem cost_andCost_le {n g : ℕ} (p : Program signature n g) : p.cost andCost ≤ g := by
  simpa only [one_mul] using p.cost_le_mul (b := 1) (fun op => by cases op <;> decide)

private def constOne (n : ℕ) : BooleanFunction n := fun _ => true
private def constZero (n : ℕ) : BooleanFunction n := fun _ => false

private theorem synth_consts (n : ℕ) :
    CostSynthesis interpretation andCost (inputs n) {constZero n, constOne n} 2 0 := by
  have h1 : CostSynthesis interpretation andCost (inputs n) {constOne n} 1 0 :=
    (CostSynthesis.gate (I := interpretation) (w := andCost) (s := inputs n)
      Op.one Fin.elim0 fun i => i.elim0).mono Set.Subset.rfl (by rintro _ rfl; rfl) le_rfl le_rfl
  have h0 : CostSynthesis interpretation andCost (inputs n ∪ {constOne n}) {constZero n} 1 0 := by
    have h := add_two_of_mem (G := Bool) (I := interpretation) (w := andCost) (addOp := Op.xor)
      rfl (fun _ => rfl) rfl (s := inputs n ∪ {constOne n}) (Or.inr rfl) (Or.inr rfl)
    refine h.mono Set.Subset.rfl ?_ le_rfl le_rfl
    rintro _ rfl
    exact rfl
  have h10 := h1.comp h0
  refine h10.mono Set.Subset.rfl ?_ le_rfl le_rfl
  intro f hf
  rcases hf with rfl | h1'
  · exact Or.inr rfl
  · exact Or.inl h1'

/-- The Zhegalkin basis `{⊕, ∧, 1}` simulates the De Morgan basis `{0, 1, ¬, ∧, ∨}`. -/
theorem simulates_deMorgan : interpretation.Simulates Boolean.interpretation := by
  rw [Interpretation.simulates_iff]
  intro op
  cases op with
  | const b =>
    cases b
    · obtain ⟨c, hc, -, -⟩ := ((synth_consts 0).mono Set.Subset.rfl
        (Set.singleton_subset_iff.mpr (Or.inl rfl)) le_rfl le_rfl).exists_circuit
      exact ⟨c, hc⟩
    · obtain ⟨c, hc, -, -⟩ := ((synth_consts 0).mono Set.Subset.rfl
        (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl le_rfl).exists_circuit
      exact ⟨c, hc⟩
  | not =>
    have h1 := synth_consts 1
    have hnot : CostSynthesis interpretation andCost
        (inputs 1 ∪ {constZero 1, constOne 1}) {Boolean.interpretation .not} 1 0 := by
      have hx0 : (fun x : Fin 1 → Bool => x 0) ∈ inputs 1 ∪ {constZero 1, constOne 1} :=
        Or.inl ⟨0, rfl⟩
      have hc1 : constOne 1 ∈ inputs 1 ∪ {constZero 1, constOne 1} := Or.inr (Or.inr rfl)
      have h := add_two_of_mem (G := Bool) (I := interpretation) (w := andCost) (addOp := Op.xor)
        rfl (fun _ => rfl) rfl hx0 hc1
      refine h.mono Set.Subset.rfl ?_ le_rfl le_rfl
      rintro _ rfl
      funext x
      change (!x 0) = (x 0 ^^ true)
      cases x 0 <;> rfl
    obtain ⟨c, hc, -, -⟩ := (h1.trans hnot).exists_circuit
    exact ⟨c, hc⟩
  | and =>
    let args : Fin 2 → BooleanFunction 2 := fun i x => x i
    have hand_raw := CostSynthesis.gate (I := interpretation) (w := andCost) (s := inputs 2)
      Op.and args fun i => ⟨i, rfl⟩
    have hand : CostSynthesis interpretation andCost (inputs 2)
        {Boolean.interpretation .and} 1 1 :=
      hand_raw.mono Set.Subset.rfl (by rintro _ rfl; rfl) le_rfl le_rfl
    obtain ⟨c, hc, -, -⟩ := hand.exists_circuit
    exact ⟨c, hc⟩
  | or =>
    let args : Fin 2 → BooleanFunction 2 := fun i x => x i
    have hand : CostSynthesis interpretation andCost (inputs 2)
        {fun x : Fin 2 → Bool => x 0 && x 1} 1 1 :=
      (CostSynthesis.gate (I := interpretation) (w := andCost) (s := inputs 2)
        Op.and args fun i => ⟨i, rfl⟩).mono Set.Subset.rfl (by rintro _ rfl; rfl) le_rfl le_rfl
    have hxor : CostSynthesis interpretation andCost (inputs 2)
        {fun x : Fin 2 → Bool => x 0 ^^ x 1} 1 0 :=
      (CostSynthesis.gate (I := interpretation) (w := andCost) (s := inputs 2)
        Op.xor args fun i => ⟨i, rfl⟩).mono Set.Subset.rfl (by rintro _ rfl; rfl) le_rfl le_rfl
    have hor : CostSynthesis interpretation andCost
        (inputs 2 ∪ ({fun x : Fin 2 → Bool => x 0 && x 1} ∪
          {fun x : Fin 2 → Bool => x 0 ^^ x 1}))
        {Boolean.interpretation .or} 1 0 := by
      have ha : (fun x : Fin 2 → Bool => x 0 && x 1) ∈
          inputs 2 ∪ ({fun x => x 0 && x 1} ∪ {fun x => x 0 ^^ x 1}) :=
        Or.inr (Or.inl rfl)
      have hx : (fun x : Fin 2 → Bool => x 0 ^^ x 1) ∈
          inputs 2 ∪ ({fun x => x 0 && x 1} ∪ {fun x => x 0 ^^ x 1}) :=
        Or.inr (Or.inr rfl)
      have h := add_two_of_mem (G := Bool) (I := interpretation) (w := andCost) (addOp := Op.xor)
        rfl (fun _ => rfl) rfl hx ha
      refine h.mono Set.Subset.rfl ?_ le_rfl le_rfl
      rintro _ rfl
      funext x
      change (x 0 || x 1) = ((x 0 ^^ x 1) ^^ (x 0 && x 1))
      cases x 0 <;> cases x 1 <;> rfl
    obtain ⟨c, hc, -, -⟩ := ((hand.union hxor).trans hor).exists_circuit
    exact ⟨c, hc⟩

/-- The Zhegalkin basis `{⊕, ∧, 1}` is functionally complete. -/
instance : interpretation.IsComplete :=
  simulates_deMorgan.isComplete

/-- The *multiplicative complexity* `L_∧(f)` of a Boolean operator `f` over `{⊕, ∧, 1}`
([Sergeev, p. 1][Sergeev2013AdditiveMultiplicative]): the least number of conjunction (`∧`) gates
in a `{⊕, ∧, 1}`-circuit computing `f`, with `.xor` and `.one` gates free. -/
noncomputable def multiplicativeComplexity {n m : ℕ} (f : (Fin n → Bool) → Fin m → Bool) : ℕ :=
  (ecomplexityFrom interpretation andCost f id).untop <|
    ecomplexityFrom_ne_top_iff.mpr (Interpretation.IsComplete.exists_computes f)

@[simp] theorem natCast_multiplicativeComplexity {n m : ℕ} (f : (Fin n → Bool) → Fin m → Bool) :
    (multiplicativeComplexity f : ℕ∞) = ecomplexityFrom interpretation andCost f id :=
  WithTop.coe_untop _ _

/-- Every `{⊕, ∧, 1}`-circuit computing `f` bounds `multiplicativeComplexity f` by its `andCost`. -/
theorem multiplicativeComplexity_le_of_computes {n m : ℕ} {f : (Fin n → Bool) → Fin m → Bool}
    (c : Circuit signature n m) (hc : c.Computes interpretation f) :
    multiplicativeComplexity f ≤ c.program.cost andCost := by
  have h := ecomplexityFrom_le_of_computesFrom (cost := andCost) (sources := id) c hc
  rw [← natCast_multiplicativeComplexity] at h
  exact_mod_cast h

/-- `multiplicativeComplexity f ≤ M` holds iff some `{⊕, ∧, 1}`-circuit computes `f` using at most
`M` conjunction gates. -/
theorem multiplicativeComplexity_le_iff {n m M : ℕ} {f : (Fin n → Bool) → Fin m → Bool} :
    multiplicativeComplexity f ≤ M ↔
      ∃ c : Circuit signature n m, c.Computes interpretation f ∧ c.program.cost andCost ≤ M := by
  have h := ecomplexityFrom_le_iff (I := interpretation) (cost := andCost) (target := f)
    (sources := id) (k := M)
  rw [← natCast_multiplicativeComplexity] at h
  exact (Nat.cast_le (α := ℕ∞)).symm.trans h

/-- Some `{⊕, ∧, 1}`-circuit computing `f` attains `multiplicativeComplexity f`. -/
theorem exists_computes_cost_eq_multiplicativeComplexity {n m : ℕ}
    (f : (Fin n → Bool) → Fin m → Bool) :
    ∃ c : Circuit signature n m,
      c.Computes interpretation f ∧ c.program.cost andCost = multiplicativeComplexity f := by
  obtain ⟨c, hc, hcost⟩ := exists_computesFrom_cost_eq_ecomplexityFrom (I := interpretation)
    (cost := andCost) (target := f) (sources := id) (Interpretation.IsComplete.exists_computes f)
  rw [← natCast_multiplicativeComplexity] at hcost
  exact ⟨c, hc, by exact_mod_cast hcost⟩

/-- Multiplicative complexity never exceeds total `{⊕, ∧, 1}` circuit complexity. -/
theorem multiplicativeComplexity_le_complexity {n m : ℕ} (f : (Fin n → Bool) → Fin m → Bool) :
    multiplicativeComplexity f ≤ complexity interpretation f := by
  obtain ⟨c, hc, hsize⟩ := exists_computes_size_eq_complexity (I := interpretation) (f := f)
  exact (multiplicativeComplexity_le_of_computes c hc).trans (c.program.cost_le_mul (b := 1)
    (fun op => by cases op <;> decide) |>.trans_eq (by simp [hsize]))

/-- Explicit total gate budget over `{⊕, ∧, 1}` for the upper bound of [Sergeev, Theorem 1, p. 3]
[Sergeev2013AdditiveMultiplicative] for an `n`-input Boolean function of multiplicative complexity
at most `M`, with block/stage width `s` and horizontal section height `p`. -/
@[expose] def totalBound (n M s p : ℕ) : ℕ :=
  ((n + M) * 2 ^ s) / s + (M * (M + 2 * n)) / (2 * s) + 2 * M * (p + s + 1) +
    ((2 * M) ⌈/⌉ p) * 2 ^ s * ((n + M) ⌈/⌉ s) + n + M + 2

/-! #### Topological affine decomposition of `{⊕, ∧, 1}`-programs -/

section Decomposition

private def linForm {n k : ℕ} (c₀ : Bool) (cX : Fin n → Bool) (cG : Fin k → Bool)
    (gFn : Fin k → BooleanFunction n) (x : Fin n → Bool) : Bool :=
  (if c₀ then true else (0 : Bool)) +
    (∑ j : Fin n, if cX j then x j else 0) +
    (∑ ℓ : Fin k, if cG ℓ then gFn ℓ x else 0)

private theorem bool_ite_add (a b z : Bool) :
    (if a + b then z else (0 : Bool)) = (if a then z else 0) + (if b then z else 0) := by
  cases a <;> cases b <;> cases z <;> rfl

private theorem linForm_add {n k : ℕ} (c₀ d₀ : Bool) (cX dX : Fin n → Bool)
    (cG dG : Fin k → Bool) (gFn : Fin k → BooleanFunction n) (x : Fin n → Bool) :
    linForm (c₀ + d₀) (fun j => cX j + dX j) (fun ℓ => cG ℓ + dG ℓ) gFn x =
      linForm c₀ cX cG gFn x + linForm d₀ dX dG gFn x := by
  unfold linForm
  simp only [bool_ite_add, sum_add_distrib]
  abel

private theorem linForm_snoc_false {n k : ℕ} (c₀ : Bool) (cX : Fin n → Bool) (cG : Fin k → Bool)
    (gFn : Fin k → BooleanFunction n) (gLast : BooleanFunction n) (x : Fin n → Bool) :
    linForm c₀ cX (Fin.snoc cG false) (Fin.snoc gFn gLast) x = linForm c₀ cX cG gFn x := by
  unfold linForm
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Bool.false_eq_true, ↓reduceIte, add_zero]

private structure ProgDecomp {n g : ℕ} (p : Program signature n g) (k : ℕ) where
  gFn : Fin k → BooleanFunction n
  cH : Fin (2 * k) → Bool
  aX : Fin (2 * k) → Fin n → Bool
  aG : Fin (2 * k) → Fin k → Bool
  cW : Wire n g → Bool
  wX : Wire n g → Fin n → Bool
  wG : Wire n g → Fin k → Bool
  causal : ∀ (r : Fin (2 * k)) (ℓ : Fin k), r.1 / 2 ≤ ℓ.1 → aG r ℓ = false
  gFn_eq : ∀ (i : Fin k) (x : Fin n → Bool),
    gFn i x =
      (linForm (cH ⟨2 * i.1, by omega⟩) (aX ⟨2 * i.1, by omega⟩)
          (aG ⟨2 * i.1, by omega⟩) gFn x &&
        linForm (cH ⟨2 * i.1 + 1, by omega⟩) (aX ⟨2 * i.1 + 1, by omega⟩)
          (aG ⟨2 * i.1 + 1, by omega⟩) gFn x)
  trace_eq : ∀ (w : Wire n g) (x : Fin n → Bool),
    p.trace interpretation x w = linForm (cW w) (wX w) (wG w) gFn x

private theorem progDecomp_empty (n : ℕ) :
    Nonempty (ProgDecomp (Program.empty : Program signature n 0) 0) := by
  refine ⟨{
    gFn := Fin.elim0
    cH := Fin.elim0
    aX := Fin.elim0
    aG := Fin.elim0
    cW := fun _ => false
    wX := Wire.elim (fun i j => decide (j = i)) Fin.elim0
    wG := fun _ => Fin.elim0
    causal := fun r => r.elim0
    gFn_eq := fun i => i.elim0
    trace_eq := fun w x => ?_ }⟩
  cases w with
  | gate j => exact j.elim0
  | input i =>
    unfold linForm
    simp only [Program.trace_input, Wire.elim_input, Bool.false_eq_true, ↓reduceIte, zero_add,
      decide_eq_true_eq]
    rw [sum_ite_eq', Fintype.sum_empty, add_zero]
    simp

private theorem progDecomp_one {n g k : ℕ} {q : Program signature n g}
    (ih : ProgDecomp q k) (wires : Fin (signature.Arity Op.one) → Wire n g) :
    Nonempty (ProgDecomp (q.gate ⟨Op.one, wires⟩) k) := by
  refine ⟨{
    gFn := ih.gFn
    cH := ih.cH
    aX := ih.aX
    aG := ih.aG
    cW := Wire.lastCases true ih.cW
    wX := Wire.lastCases (fun _ => false) ih.wX
    wG := Wire.lastCases (fun _ => false) ih.wG
    causal := ih.causal
    gFn_eq := ih.gFn_eq
    trace_eq := fun w x => ?_ }⟩
  refine Wire.lastCases ?_ (fun w₀ => ?_) w
  · change (q.gate ⟨Op.one, wires⟩).eval interpretation x (Fin.last g) = _
    rw [Program.eval_gate_last]
    unfold linForm
    simp [Line.eval, Wire.lastCases]
  · rw [Program.trace_gate_castSucc, ih.trace_eq w₀ x]
    cases w₀ <;> simp [Wire.lastCases]

private theorem progDecomp_xor {n g k : ℕ} {q : Program signature n g}
    (ih : ProgDecomp q k) (wires : Fin (signature.Arity Op.xor) → Wire n g) :
    Nonempty (ProgDecomp (q.gate ⟨Op.xor, wires⟩) k) := by
  let u₀ := wires 0
  let u₁ := wires 1
  refine ⟨{
    gFn := ih.gFn
    cH := ih.cH
    aX := ih.aX
    aG := ih.aG
    cW := Wire.lastCases (ih.cW u₀ + ih.cW u₁) ih.cW
    wX := Wire.lastCases (fun j => ih.wX u₀ j + ih.wX u₁ j) ih.wX
    wG := Wire.lastCases (fun ℓ => ih.wG u₀ ℓ + ih.wG u₁ ℓ) ih.wG
    causal := ih.causal
    gFn_eq := ih.gFn_eq
    trace_eq := fun w x => ?_ }⟩
  refine Wire.lastCases ?_ (fun w₀ => ?_) w
  · change (q.gate ⟨Op.xor, wires⟩).eval interpretation x (Fin.last g) = _
    rw [Program.eval_gate_last]
    change (q.trace interpretation x u₀ + q.trace interpretation x u₁) = _
    rw [ih.trace_eq u₀ x, ih.trace_eq u₁ x, ← linForm_add]
    simp [Wire.lastCases]
  · rw [Program.trace_gate_castSucc, ih.trace_eq w₀ x]
    cases w₀ <;> simp [Wire.lastCases]

private theorem progDecomp_and {n g k : ℕ} {q : Program signature n g}
    (ih : ProgDecomp q k) (wires : Fin (signature.Arity Op.and) → Wire n g) :
    Nonempty (ProgDecomp (q.gate ⟨Op.and, wires⟩) (k + 1)) := by
  let u₀ := wires 0
  let u₁ := wires 1
  let gLast : BooleanFunction n := fun x =>
    q.trace interpretation x u₀ && q.trace interpretation x u₁
  let gFn' : Fin (k + 1) → BooleanFunction n := Fin.snoc ih.gFn gLast
  let cH' : Fin (2 * (k + 1)) → Bool := fun r =>
    if hr : r.1 < 2 * k then ih.cH ⟨r.1, hr⟩
    else if r.1 = 2 * k then ih.cW u₀ else ih.cW u₁
  let aX' : Fin (2 * (k + 1)) → Fin n → Bool := fun r =>
    if hr : r.1 < 2 * k then ih.aX ⟨r.1, hr⟩
    else if r.1 = 2 * k then ih.wX u₀ else ih.wX u₁
  let aG' : Fin (2 * (k + 1)) → Fin (k + 1) → Bool := fun r =>
    if hr : r.1 < 2 * k then Fin.snoc (ih.aG ⟨r.1, hr⟩) false
    else if r.1 = 2 * k then Fin.snoc (ih.wG u₀) false
    else Fin.snoc (ih.wG u₁) false
  refine ⟨{
    gFn := gFn'
    cH := cH'
    aX := aX'
    aG := aG'
    cW := Wire.lastCases false ih.cW
    wX := Wire.lastCases (fun _ => false) ih.wX
    wG := Wire.lastCases (fun ℓ => decide (ℓ = Fin.last k))
      (fun w₀ => Fin.snoc (ih.wG w₀) false)
    causal := fun r => Fin.lastCases
      (fun _ => by
        dsimp only [aG']
        split_ifs <;> exact Fin.snoc_last _ _)
      (fun j hle => by
        simp only [Fin.val_castSucc] at hle
        have hr : r.1 < 2 * k := by
          have hj : j.1 < k := j.isLt
          omega
        dsimp only [aG']
        simp only [hr, ↓reduceDIte, Fin.snoc_castSucc]
        exact ih.causal ⟨r.1, hr⟩ j hle)
    gFn_eq := fun i x => ?_
    trace_eq := fun w x => ?_ }⟩
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · have h0_not : ¬ (2 * k < 2 * k) := by omega
      have h1_not : ¬ (2 * k + 1 < 2 * k) := by omega
      have h1_ne : 2 * k + 1 ≠ 2 * k := by omega
      dsimp only [gFn', cH', aX', aG']
      simp only [Fin.snoc_last, Fin.val_last, h0_not, h1_not, h1_ne, ↓reduceDIte, ↓reduceIte,
        linForm_snoc_false, ← ih.trace_eq u₀ x, ← ih.trace_eq u₁ x]
      rfl
    · have hj0 : 2 * j.castSucc.1 < 2 * k := by
        have := j.isLt
        simp only [Fin.val_castSucc]
        omega
      have hj1 : 2 * j.castSucc.1 + 1 < 2 * k := by
        have := j.isLt
        simp only [Fin.val_castSucc]
        omega
      dsimp only [gFn', cH', aX', aG']
      simp only [Fin.snoc_castSucc, hj0, hj1, ↓reduceDIte, linForm_snoc_false]
      exact ih.gFn_eq j x
  · refine Wire.lastCases ?_ (fun w₀ => ?_) w
    · change (q.gate ⟨Op.and, wires⟩).eval interpretation x (Fin.last g) = _
      rw [Program.eval_gate_last]
      change gLast x = _
      unfold linForm
      simp only [Wire.lastCases, Fin.lastCases_last, Bool.false_eq_true, ↓reduceIte, zero_add,
        sum_const_zero, decide_eq_true_eq]
      rw [sum_ite_eq']
      simp [gFn']
    · rw [Program.trace_gate_castSucc, ih.trace_eq w₀ x]
      have hw :
          Wire.lastCases false ih.cW w₀.castSucc = ih.cW w₀ ∧
            Wire.lastCases (fun _ => false) ih.wX w₀.castSucc = ih.wX w₀ ∧
            Wire.lastCases (fun ℓ => decide (ℓ = Fin.last k))
              (fun v => Fin.snoc (ih.wG v) false) w₀.castSucc = Fin.snoc (ih.wG w₀) false := by
        cases w₀ <;> simp [Wire.lastCases]
      rw [hw.1, hw.2.1, hw.2.2, linForm_snoc_false]

private theorem exists_progDecomp {n g : ℕ} (p : Program signature n g) :
    Nonempty (ProgDecomp p (p.cost andCost)) := by
  induction p with
  | empty => exact progDecomp_empty n
  | gate q line ih =>
    obtain ⟨d⟩ := ih
    rcases line with ⟨op, wires⟩
    cases op with
    | one =>
      have hk : (q.gate ⟨Op.one, wires⟩).cost andCost = q.cost andCost := by simp
      exact hk ▸ progDecomp_one d wires
    | xor =>
      have hk : (q.gate ⟨Op.xor, wires⟩).cost andCost = q.cost andCost := by simp
      exact hk ▸ progDecomp_xor d wires
    | and =>
      have hk : (q.gate ⟨Op.and, wires⟩).cost andCost = q.cost andCost + 1 := by simp
      exact hk ▸ progDecomp_and d wires

private structure PaddedDecomp {n : ℕ} (f : BooleanFunction n) (M k : ℕ) where
  gFn : Fin M → BooleanFunction n
  cH : Fin (2 * M) → Bool
  aX : Fin (2 * M) → Fin n → Bool
  aG : Fin (2 * M) → Fin M → Bool
  outC : Bool
  outX : Fin n → Bool
  outG : Fin M → Bool
  causal : ∀ (r : Fin (2 * M)) (ℓ : Fin M), r.1 / 2 ≤ ℓ.1 → aG r ℓ = false
  gFn_lt : ∀ (i : Fin M), i.1 < k → ∀ x : Fin n → Bool,
    gFn i x =
      (linForm (cH ⟨2 * i.1, by omega⟩) (aX ⟨2 * i.1, by omega⟩)
          (aG ⟨2 * i.1, by omega⟩) gFn x &&
        linForm (cH ⟨2 * i.1 + 1, by omega⟩) (aX ⟨2 * i.1 + 1, by omega⟩)
          (aG ⟨2 * i.1 + 1, by omega⟩) gFn x)
  gFn_ge : ∀ (i : Fin M), k ≤ i.1 → gFn i = constZero n
  out_eq : ∀ x : Fin n → Bool, f x = linForm outC outX outG gFn x

private def padBool {k M : ℕ} (v : Fin k → Bool) (ℓ : Fin M) : Bool :=
  if h : ℓ.1 < k then v ⟨ℓ.1, h⟩ else false

private def padFn {n k M : ℕ} (gFn : Fin k → BooleanFunction n) (ℓ : Fin M) : BooleanFunction n :=
  if h : ℓ.1 < k then gFn ⟨ℓ.1, h⟩ else constZero n

private theorem linForm_pad {n k M : ℕ} (hkM : k ≤ M) (c₀ : Bool) (cX : Fin n → Bool)
    (cG : Fin k → Bool) (gFn : Fin k → BooleanFunction n) (x : Fin n → Bool) :
    linForm c₀ cX (padBool (M := M) cG) (padFn (M := M) gFn) x = linForm c₀ cX cG gFn x := by
  unfold linForm
  congr 1
  have hsub : (univ.map (Fin.castLEEmb hkM)) ⊆ (univ : Finset (Fin M)) := subset_univ _
  rw [← sum_subset hsub]
  · rw [sum_map]
    refine sum_congr rfl fun i _ => ?_
    simp [padBool, padFn, i.isLt]
  · intro ℓ _ hnot
    have hge : ¬ (ℓ.1 < k) := by
      intro hlt
      exact hnot (mem_map.mpr ⟨⟨ℓ.1, hlt⟩, mem_univ _, Fin.ext rfl⟩)
    simp [padBool, hge]

private theorem exists_paddedDecomp {n M : ℕ} {f : BooleanFunction n} (c : Circuit signature n 1)
    (hc : c.Computes interpretation (single f)) (hkM : c.program.cost andCost ≤ M) :
    Nonempty (PaddedDecomp f M (c.program.cost andCost)) := by
  let k := c.program.cost andCost
  obtain ⟨pd⟩ := exists_progDecomp c.program
  let outW := c.outputs 0
  refine ⟨{
    gFn := padFn (M := M) pd.gFn
    cH := fun r => if hr : r.1 < 2 * k then pd.cH ⟨r.1, hr⟩ else false
    aX := fun r => if hr : r.1 < 2 * k then pd.aX ⟨r.1, hr⟩ else fun _ => false
    aG := fun r =>
      if hr : r.1 < 2 * k then padBool (M := M) (pd.aG ⟨r.1, hr⟩) else fun _ => false
    outC := pd.cW outW
    outX := pd.wX outW
    outG := padBool (M := M) (pd.wG outW)
    causal := fun r ℓ hle => ?_
    gFn_lt := fun i hi x => ?_
    gFn_ge := fun i hi => ?_
    out_eq := fun x => ?_ }⟩
  · split_ifs with hr
    · unfold padBool
      split_ifs with hℓ
      · exact pd.causal ⟨r.1, hr⟩ ⟨ℓ.1, hℓ⟩ hle
      · rfl
    · rfl
  · have hr0 : 2 * i.1 < 2 * k := by omega
    have hr1 : 2 * i.1 + 1 < 2 * k := by omega
    dsimp only [padFn]
    simp only [hi, hr0, hr1, ↓reduceDIte, linForm_pad hkM]
    exact pd.gFn_eq ⟨i.1, hi⟩ x
  · have hnot : ¬ (i.1 < c.program.cost andCost) := Nat.not_lt.mpr hi
    simp only [padFn, hnot, ↓reduceDIte]
  · have heval : c.eval interpretation x 0 = f x := congrFun (hc x) 0
    rw [← heval]
    change c.program.trace interpretation x outW = _
    rw [pd.trace_eq outW x, linForm_pad hkM]

end Decomposition

/-! #### Staged acyclic synthesis over `{⊕, ∧, 1}` -/

section ZhegalkinSynthesis

variable {n M k : ℕ} {f : BooleanFunction n}

private abbrev ZhegCol (n M s : ℕ) := Additive.FullCol n s ⊕ Additive.FullCol M s

private theorem card_zhegCol_le (n M s : ℕ) (hs : 0 < s) :
    Fintype.card (ZhegCol n M s) ≤ 2 ^ s * ((n + M) ⌈/⌉ s) := by
  have hdiv : n / s + M / s ≤ (n + M) ⌈/⌉ s := by
    apply Nat.lt_succ_iff.mp
    apply Nat.lt_of_mul_lt_mul_left (a := s)
    calc s * (n / s + M / s)
        = s * (n / s) + s * (M / s) := by ring
      _ ≤ n + M := Nat.add_le_add (Nat.mul_div_le n s) (Nat.mul_div_le M s)
      _ ≤ s * ((n + M) ⌈/⌉ s) := (ceilDiv_le_iff_le_smul hs).mp le_rfl
      _ < s * ((n + M) ⌈/⌉ s + 1) := by nlinarith
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    Additive.card_nonempty_finset_fin]
  calc (n / s) * (2 ^ s - 1) + (M / s) * (2 ^ s - 1)
      = (n / s + M / s) * (2 ^ s - 1) := by ring
    _ ≤ ((n + M) ⌈/⌉ s) * 2 ^ s := Nat.mul_le_mul hdiv (Nat.sub_le _ _)
    _ = 2 ^ s * ((n + M) ⌈/⌉ s) := mul_comm _ _

private def zhegColVal {s : ℕ} (d : PaddedDecomp f M k) :
    ZhegCol n M s → BooleanFunction n
  | .inl cx => Additive.fullColVal cx
  | .inr cg => fun x => ∑ a ∈ cg.2.1, d.gFn (Additive.fullBlockEmb cg.1 a) x

private def hasZhegCol (d : PaddedDecomp f M k) (s : ℕ) (r : Fin (2 * M)) :
    ZhegCol n M s → Bool
  | .inl cx => Additive.hasFullCol d.aX s r cx
  | .inr cg => decide (cg.1.1 < (r.1 / 2) / s ∧ Additive.fullRowPattern d.aG s r cg.1 = cg.2.1)

private theorem mul_sum_hasZhegCol_le (d : PaddedDecomp f M k) (s : ℕ) :
    s * (∑ r : Fin (2 * M), #{c : ZhegCol n M s | hasZhegCol d s r c = true}) ≤
      M * (M + 2 * n) := by
  have hrow (r : Fin (2 * M)) :
      #{c : ZhegCol n M s | hasZhegCol d s r c = true} ≤ n / s + (r.1 / 2) / s := by
    have hsplit : #{c : ZhegCol n M s | hasZhegCol d s r c = true} =
        #{cx : Additive.FullCol n s | Additive.hasFullCol d.aX s r cx = true} +
        #{cg : Additive.FullCol M s |
          decide (cg.1.1 < (r.1 / 2) / s ∧
            Additive.fullRowPattern d.aG s r cg.1 = cg.2.1) = true} := by
      simp only [card_filter]
      rw [Fintype.sum_sum_type]
      rfl
    rw [hsplit]
    apply Nat.add_le_add
    · let activeX := univ.filter fun cx : Additive.FullCol n s =>
        Additive.hasFullCol d.aX s r cx = true
      have hinj : Set.InjOn Prod.fst (activeX : Set (Additive.FullCol n s)) := by
        intro ⟨q₁, T₁, _⟩ hx₁ ⟨q₂, T₂, _⟩ hx₂ hq
        dsimp only at hq
        subst hq
        have heq₁ : Additive.fullRowPattern d.aX s r q₁ = T₁ :=
          of_decide_eq_true (mem_filter.mp hx₁).2
        have heq₂ : Additive.fullRowPattern d.aX s r q₁ = T₂ :=
          of_decide_eq_true (mem_filter.mp hx₂).2
        exact Prod.ext rfl (Subtype.ext (heq₁.symm.trans heq₂))
      exact (card_le_card_of_injOn Prod.fst (fun _ _ => mem_univ _) hinj).trans_eq (by simp)
    · let targetQ : Finset (Fin (M / s)) := univ.filter fun q => q.1 < (r.1 / 2) / s
      let activeG := univ.filter fun cg : Additive.FullCol M s =>
        decide (cg.1.1 < (r.1 / 2) / s ∧
          Additive.fullRowPattern d.aG s r cg.1 = cg.2.1) = true
      have hinj : Set.InjOn Prod.fst (activeG : Set (Additive.FullCol M s)) := by
        intro ⟨q₁, T₁, _⟩ hx₁ ⟨q₂, T₂, _⟩ hx₂ hq
        dsimp only at hq
        subst hq
        have heq₁ : Additive.fullRowPattern d.aG s r q₁ = T₁ :=
          (of_decide_eq_true (mem_filter.mp hx₁).2).2
        have heq₂ : Additive.fullRowPattern d.aG s r q₁ = T₂ :=
          (of_decide_eq_true (mem_filter.mp hx₂).2).2
        exact Prod.ext rfl (Subtype.ext (heq₁.symm.trans heq₂))
      have hmaps : ∀ cg ∈ univ.filter (fun cg : Additive.FullCol M s =>
          decide (cg.1.1 < (r.1 / 2) / s ∧
            Additive.fullRowPattern d.aG s r cg.1 = cg.2.1) = true), cg.1 ∈ targetQ :=
        fun cg hcg => mem_filter.mpr ⟨mem_univ _, (of_decide_eq_true (mem_filter.mp hcg).2).1⟩
      have hcardQ : #targetQ ≤ (r.1 / 2) / s := by
        have hinjVal : Set.InjOn Fin.val (targetQ : Set (Fin (M / s))) :=
          fun _ _ _ _ h => Fin.ext h
        exact (card_le_card_of_injOn Fin.val
          (fun q hq => mem_range.mpr (mem_filter.mp hq).2) hinjVal).trans_eq (card_range _)
      exact (card_le_card_of_injOn Prod.fst hmaps hinj).trans hcardQ
  calc s * (∑ r : Fin (2 * M), #{c : ZhegCol n M s | hasZhegCol d s r c = true})
      ≤ s * (∑ r : Fin (2 * M), (n / s + (r.1 / 2) / s)) :=
        Nat.mul_le_mul_left s (sum_le_sum fun r _ => hrow r)
    _ = ∑ r : Fin (2 * M), (s * (n / s) + s * ((r.1 / 2) / s)) := by
        rw [mul_sum]
        exact sum_congr rfl fun r _ => by ring
    _ ≤ ∑ r : Fin (2 * M), (n + r.1 / 2) :=
        sum_le_sum fun r _ => Nat.add_le_add (Nat.mul_div_le n s) (Nat.mul_div_le _ s)
    _ = 2 * M * n + ∑ r ∈ range (2 * M), r / 2 := by
        rw [Fin.sum_univ_eq_sum_range (fun t => n + t / 2), sum_add_distrib, sum_const,
          card_range, smul_eq_mul]
    _ ≤ M * (M + 2 * n) := by
        have hsum_div : ∑ r ∈ range (2 * M), r / 2 ≤ M * M := by
          clear * -
          induction M with
          | zero => simp
          | succ m ih =>
            have h2 : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
            rw [h2, sum_range_succ, sum_range_succ]
            have hd1 : (2 * m) / 2 = m := by omega
            have hd2 : (2 * m + 1) / 2 = m := by omega
            nlinarith
        nlinarith

private def zhegPairVal (d : PaddedDecomp f M k) (s p : ℕ)
    (up : ℕ × (Fin (2 * M) × Fin (2 * M))) (x : Fin n → Bool) : Bool :=
  ∑ c ∈ pairedCols (hasZhegCol d s) p up.1 up.2.1 up.2.2, zhegColVal d c x

private def zhegOddVal (d : PaddedDecomp f M k) (s p : ℕ) (r : Fin (2 * M))
    (x : Fin n → Bool) : Bool :=
  ∑ c ∈ oddCols (hasZhegCol d s) p r, zhegColVal d c x

private def intraGSet (d : PaddedDecomp f M k) (s : ℕ) (r : Fin (2 * M)) : Finset (Fin M) :=
  univ.filter fun ℓ : Fin M => ℓ.1 / s = (r.1 / 2) / s ∧ ℓ.1 < r.1 / 2 ∧ d.aG r ℓ = true

private theorem card_intraGSet_le (d : PaddedDecomp f M k) {s : ℕ} (hs : 0 < s)
    (r : Fin (2 * M)) : #(intraGSet d s r) ≤ s - 1 := by
  let mod0 : Fin s := ⟨(r.1 / 2) % s, Nat.mod_lt _ hs⟩
  have hmaps : ∀ ℓ ∈ intraGSet d s r,
      (⟨ℓ.1 % s, Nat.mod_lt _ hs⟩ : Fin s) ∈ univ.erase mod0 := by
    intro ℓ hℓ
    obtain ⟨_, hdiv, hlt, _⟩ := mem_filter.mp hℓ
    refine mem_erase.mpr ⟨fun heq => ?_, mem_univ _⟩
    have hm : ℓ.1 % s = (r.1 / 2) % s := congrArg Fin.val heq
    have h1 := Nat.div_add_mod ℓ.1 s
    have h2 := Nat.div_add_mod (r.1 / 2) s
    rw [hdiv, hm] at h1
    omega
  have hinj : Set.InjOn (fun ℓ : Fin M => (⟨ℓ.1 % s, Nat.mod_lt _ hs⟩ : Fin s))
      (intraGSet d s r) := by
    intro ℓ₁ h₁ ℓ₂ h₂ heq
    have hd₁ := (mem_filter.mp h₁).2.1
    have hd₂ := (mem_filter.mp h₂).2.1
    have hm : ℓ₁.1 % s = ℓ₂.1 % s := congrArg Fin.val heq
    apply Fin.ext
    rw [← Nat.div_add_mod ℓ₁.1 s, ← Nat.div_add_mod ℓ₂.1 s, hd₁, hd₂, hm]
  exact (card_le_card_of_injOn _ hmaps hinj).trans_eq
    (by rw [card_erase_of_mem (mem_univ mod0), card_univ, Fintype.card_fin])

private def hFn (d : PaddedDecomp f M k) (r : Fin (2 * M)) : BooleanFunction n :=
  linForm (d.cH r) (d.aX r) (d.aG r) d.gFn

private inductive ZhegPartIdx (M : ℕ) where
  | constOne
  | peer (r' : Fin (2 * M))
  | odd
  | xTail
  | intraG (ℓ : Fin M)
  deriving DecidableEq

private def peerEmb (M : ℕ) : Fin (2 * M) ↪ ZhegPartIdx M :=
  ⟨.peer, fun _ _ h => by injection h⟩

private def intraEmb (M : ℕ) : Fin M ↪ ZhegPartIdx M :=
  ⟨.intraG, fun _ _ h => by injection h⟩

private def zhegRowParts (d : PaddedDecomp f M k) (s p : ℕ) (r : Fin (2 * M)) :
    Finset (ZhegPartIdx M) :=
  (if d.cH r then {.constOne} else ∅) ∪
    ((sectionPeers p r).filter fun r' =>
        (pairedCols (hasZhegCol d s) p (r.1 / p) (min r r') (max r r')).Nonempty).map
      (peerEmb M) ∪
    (if (oddCols (hasZhegCol d s) p r).Nonempty then {.odd} else ∅) ∪
    (if (Additive.matrixTailSet d.aX s r).Nonempty then {.xTail} else ∅) ∪
    (intraGSet d s r).map (intraEmb M)

private def zhegPartVal (d : PaddedDecomp f M k) (s p : ℕ) (r : Fin (2 * M)) :
    ZhegPartIdx M → BooleanFunction n
  | .constOne => Boolean.Zhegalkin.constOne n
  | .peer r' => zhegPairVal d s p (r.1 / p, (min r r', max r r'))
  | .odd => zhegOddVal d s p r
  | .xTail => fun x => ∑ j ∈ Additive.matrixTailSet d.aX s r, x j
  | .intraG ℓ => d.gFn ℓ

private theorem card_zhegRowParts_le (d : PaddedDecomp f M k) {s p : ℕ} (hs : 0 < s) (hp : 0 < p)
    (r : Fin (2 * M)) :
    #(zhegRowParts d s p r) ≤ p + s + 1 := by
  unfold zhegRowParts
  set p1 : Finset (ZhegPartIdx M) := if d.cH r then {.constOne} else ∅
  set p2 : Finset (ZhegPartIdx M) :=
    ((sectionPeers p r).filter fun r' =>
        (pairedCols (hasZhegCol d s) p (r.1 / p) (min r r') (max r r')).Nonempty).map (peerEmb M)
  set p3 : Finset (ZhegPartIdx M) :=
    if (oddCols (hasZhegCol d s) p r).Nonempty then {.odd} else ∅
  set p4 : Finset (ZhegPartIdx M) :=
    if (Additive.matrixTailSet d.aX s r).Nonempty then {.xTail} else ∅
  set p5 : Finset (ZhegPartIdx M) := (intraGSet d s r).map (intraEmb M)
  have hc1 : #p1 ≤ 1 := by dsimp only [p1]; split_ifs <;> simp
  have hc2 : #p2 ≤ p - 1 := by
    rw [card_map]
    exact (card_le_card (filter_subset _ _)).trans (card_sectionPeers_le hp r)
  have hc3 : #p3 ≤ 1 := by dsimp only [p3]; split_ifs <;> simp
  have hc4 : #p4 ≤ 1 := by dsimp only [p4]; split_ifs <;> simp
  have hc5 : #p5 ≤ s - 1 := by
    rw [card_map]
    exact card_intraGSet_le d hs r
  have hu4 := card_union_le (p1 ∪ p2 ∪ p3 ∪ p4) p5
  have hu3 := card_union_le (p1 ∪ p2 ∪ p3) p4
  have hu2 := card_union_le (p1 ∪ p2) p3
  have hu1 := card_union_le p1 p2
  omega

private theorem sum_zhegRowParts_eq (d : PaddedDecomp f M k) {s : ℕ} (hs : 0 < s) (p : ℕ)
    (r : Fin (2 * M)) (x : Fin n → Bool) :
    (∑ idx ∈ zhegRowParts d s p r, zhegPartVal d s p r idx x) = hFn d r x := by
  unfold zhegRowParts
  set p1 : Finset (ZhegPartIdx M) := if d.cH r then {.constOne} else ∅
  set p2 : Finset (ZhegPartIdx M) :=
    ((sectionPeers p r).filter fun r' =>
        (pairedCols (hasZhegCol d s) p (r.1 / p) (min r r') (max r r')).Nonempty).map (peerEmb M)
  set p3 : Finset (ZhegPartIdx M) :=
    if (oddCols (hasZhegCol d s) p r).Nonempty then {.odd} else ∅
  set p4 : Finset (ZhegPartIdx M) :=
    if (Additive.matrixTailSet d.aX s r).Nonempty then {.xTail} else ∅
  set p5 : Finset (ZhegPartIdx M) := (intraGSet d s r).map (intraEmb M)
  have hd12 : Disjoint p1 p2 := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨_, _, rfl⟩ := mem_map.mp hz2
    dsimp only [p1] at hz1
    split_ifs at hz1 <;> simp [peerEmb] at hz1
  have hd123 : Disjoint (p1 ∪ p2) p3 := by
    rw [Finset.disjoint_left]
    intro z hz12 hz3
    dsimp only [p3] at hz3
    split_ifs at hz3 with hne
    · rw [mem_singleton.mp hz3] at hz12
      rcases mem_union.mp hz12 with hz1 | hz2
      · dsimp only [p1] at hz1; split_ifs at hz1 <;> simp at hz1
      · obtain ⟨_, _, habs⟩ := mem_map.mp hz2; nomatch habs
    · exact notMem_empty _ hz3
  have hd1234 : Disjoint (p1 ∪ p2 ∪ p3) p4 := by
    rw [Finset.disjoint_left]
    intro z hz123 hz4
    dsimp only [p4] at hz4
    split_ifs at hz4 with hne
    · rw [mem_singleton.mp hz4] at hz123
      rcases mem_union.mp hz123 with hz12 | hz3
      · rcases mem_union.mp hz12 with hz1 | hz2
        · dsimp only [p1] at hz1; split_ifs at hz1 <;> simp at hz1
        · obtain ⟨_, _, habs⟩ := mem_map.mp hz2; nomatch habs
      · dsimp only [p3] at hz3; split_ifs at hz3 <;> simp at hz3
    · exact notMem_empty _ hz4
  have hd12345 : Disjoint (p1 ∪ p2 ∪ p3 ∪ p4) p5 := by
    rw [Finset.disjoint_left]
    intro z hz1234 hz5
    obtain ⟨_, _, rfl⟩ := mem_map.mp hz5
    rcases mem_union.mp hz1234 with hz123 | hz4
    · rcases mem_union.mp hz123 with hz12 | hz3
      · rcases mem_union.mp hz12 with hz1 | hz2
        · dsimp only [p1] at hz1; split_ifs at hz1 <;> simp [intraEmb] at hz1
        · obtain ⟨_, _, habs⟩ := mem_map.mp hz2; nomatch habs
      · dsimp only [p3] at hz3; split_ifs at hz3 <;> simp [intraEmb] at hz3
    · dsimp only [p4] at hz4; split_ifs at hz4 <;> simp [intraEmb] at hz4
  rw [sum_union hd12345, sum_union hd1234, sum_union hd123, sum_union hd12, sum_map, sum_map]
  have hs1 : (∑ z ∈ p1, zhegPartVal d s p r z x) = if d.cH r then true else (0 : Bool) := by
    dsimp only [p1]
    split_ifs <;> simp [zhegPartVal, constOne]
  have hs2 :
      (∑ r' ∈ (sectionPeers p r).filter (fun r' =>
          (pairedCols (hasZhegCol d s) p (r.1 / p) (min r r') (max r r')).Nonempty),
        zhegPartVal d s p r (peerEmb M r') x) =
      ∑ r' ∈ sectionPeers p r, zhegPairVal d s p (r.1 / p, (min r r', max r r')) x := by
    rw [sum_filter]
    refine sum_congr rfl fun r' _ => ?_
    split_ifs with hne
    · rfl
    · rw [not_nonempty_iff_eq_empty] at hne
      simp [zhegPairVal, hne]
  have hs3 : (∑ z ∈ p3, zhegPartVal d s p r z x) = zhegOddVal d s p r x := by
    dsimp only [p3]
    split_ifs with hne
    · simp [zhegPartVal]
    · rw [not_nonempty_iff_eq_empty] at hne
      simp [zhegOddVal, hne]
  have hs4 : (∑ z ∈ p4, zhegPartVal d s p r z x) =
      ∑ j ∈ Additive.matrixTailSet d.aX s r, x j := by
    dsimp only [p4]
    split_ifs with hne
    · simp [zhegPartVal]
    · rw [not_nonempty_iff_eq_empty] at hne
      simp [hne]
  change (∑ z ∈ p1, zhegPartVal d s p r z x) +
      (∑ r' ∈ (sectionPeers p r).filter _, zhegPartVal d s p r (peerEmb M r') x) +
      (∑ z ∈ p3, zhegPartVal d s p r z x) +
      (∑ z ∈ p4, zhegPartVal d s p r z x) +
      (∑ ℓ ∈ intraGSet d s r, d.gFn ℓ x) = _
  rw [hs1, hs2, hs3, hs4]
  have hcol_sum :
      (∑ r' ∈ sectionPeers p r, zhegPairVal d s p (r.1 / p, (min r r', max r r')) x) +
        zhegOddVal d s p r x =
      (∑ cx : Additive.FullCol n s with Additive.hasFullCol d.aX s r cx = true,
        Additive.fullColVal cx x) +
      (∑ cg : Additive.FullCol M s with
        decide (cg.1.1 < (r.1 / 2) / s ∧
          Additive.fullRowPattern d.aG s r cg.1 = cg.2.1) = true,
        ∑ a ∈ cg.2.1, d.gFn (Additive.fullBlockEmb cg.1 a) x) := by
    have hfull := (sum_filter_hasCol_eq (hasZhegCol d s) p (fun c => zhegColVal d c x) r).symm
    unfold zhegPairVal zhegOddVal
    rw [hfull, sum_filter, Fintype.sum_sum_type, ← sum_filter, ← sum_filter]
    rfl
  -- Combine `p2 + p3` using `hcol_sum`.
  have hassoc :
      (if d.cH r then true else (0 : Bool)) +
        (∑ r' ∈ sectionPeers p r, zhegPairVal d s p (r.1 / p, (min r r', max r r')) x) +
        zhegOddVal d s p r x +
        (∑ j ∈ Additive.matrixTailSet d.aX s r, x j) +
        (∑ ℓ ∈ intraGSet d s r, d.gFn ℓ x) =
      (if d.cH r then true else (0 : Bool)) +
        (((∑ r' ∈ sectionPeers p r, zhegPairVal d s p (r.1 / p, (min r r', max r r')) x) +
          zhegOddVal d s p r x)) +
        (∑ j ∈ Additive.matrixTailSet d.aX s r, x j) +
        (∑ ℓ ∈ intraGSet d s r, d.gFn ℓ x) := by abel
  rw [hassoc, hcol_sum]
  have hx_eq := Additive.sum_row_eq_fullCol_add_tail d.aX hs r x
  -- Show the `g`-blocks plus `intraGSet` equal `∑ ℓ : Fin M, if d.aG r ℓ then d.gFn ℓ x else 0`.
  have hg_early :
      (∑ cg : Additive.FullCol M s with
        decide (cg.1.1 < (r.1 / 2) / s ∧
          Additive.fullRowPattern d.aG s r cg.1 = cg.2.1) = true,
        ∑ a ∈ cg.2.1, d.gFn (Additive.fullBlockEmb cg.1 a) x) =
      ∑ ℓ ∈ univ.filter (fun ℓ : Fin M => ℓ.1 / s < (r.1 / 2) / s ∧ d.aG r ℓ = true),
        d.gFn ℓ x := by
    have hQ : (r.1 / 2) / s ≤ M / s := Nat.div_le_div_right (by omega)
    exact Additive.sum_fullCol_lt_eq d.aG hs hQ r (fun ℓ => d.gFn ℓ x)
  have hg_split :
      (∑ ℓ ∈ univ.filter (fun ℓ : Fin M => ℓ.1 / s < (r.1 / 2) / s ∧ d.aG r ℓ = true),
        d.gFn ℓ x) +
      (∑ ℓ ∈ intraGSet d s r, d.gFn ℓ x) =
      ∑ ℓ : Fin M, if d.aG r ℓ then d.gFn ℓ x else 0 := by
    rw [← sum_filter]
    have hunion :
        (univ.filter fun ℓ : Fin M => ℓ.1 / s < (r.1 / 2) / s ∧ d.aG r ℓ = true) ∪
          intraGSet d s r =
        univ.filter fun ℓ : Fin M => d.aG r ℓ = true := by
      ext ℓ
      simp only [intraGSet, mem_union, mem_filter, mem_univ, true_and]
      constructor
      · rintro (⟨_, h⟩ | ⟨_, _, h⟩) <;> exact h
      · intro haG
        have hlt : ℓ.1 < r.1 / 2 := by
          by_contra hge
          have hc := d.causal r ℓ (Nat.le_of_not_lt hge)
          rw [hc] at haG
          exact Bool.false_ne_true haG
        have hdiv_le : ℓ.1 / s ≤ (r.1 / 2) / s := Nat.div_le_div_right hlt.le
        rcases lt_or_eq_of_le hdiv_le with hdiv_lt | hdiv_eq
        · exact Or.inl ⟨hdiv_lt, haG⟩
        · exact Or.inr ⟨hdiv_eq, hlt, haG⟩
    have hdisj :
        Disjoint (univ.filter fun ℓ : Fin M => ℓ.1 / s < (r.1 / 2) / s ∧ d.aG r ℓ = true)
          (intraGSet d s r) := by
      rw [Finset.disjoint_left]
      intro ℓ h1 h2
      have hlt := (mem_filter.mp h1).2.1
      have heq := (mem_filter.mp h2).2.1
      omega
    rw [← sum_union hdisj, hunion]
  rw [hg_early]
  unfold hFn linForm
  rw [hx_eq, ← hg_split]
  abel

private def xGroupSet (n s : ℕ) : Set (BooleanFunction n) :=
  {g | ∃ (q : ℕ) (T : Finset (Fin n)),
    T.Nonempty ∧ (∀ j ∈ T, j.1 / s = q) ∧ g = fun x => ∑ j ∈ T, x j}

private def zhegPairIdx (d : PaddedDecomp f M k) (s p : ℕ) :
    Finset (ℕ × (Fin (2 * M) × Fin (2 * M))) :=
  ((range ((2 * M) ⌈/⌉ p)).product univ).filter fun up =>
    (pairedCols (hasZhegCol d s) p up.1 up.2.1 up.2.2).Nonempty

private def zhegOddIdx (d : PaddedDecomp f M k) (s p : ℕ) : Finset (Fin (2 * M)) :=
  univ.filter fun r : Fin (2 * M) => (oddCols (hasZhegCol d s) p r).Nonempty

private def stageSet (d : PaddedDecomp f M k) (s p q₀ : ℕ) : Set (BooleanFunction n) :=
  inputs n ∪ {constZero n, constOne n} ∪ xGroupSet n s ∪
    {g | ∃ i : Fin M, i.1 / s < q₀ ∧ g = d.gFn i} ∪
    {g | ∃ cg : Additive.FullCol M s, cg.1.1 < q₀ ∧ g = zhegColVal d (.inr cg)} ∪
    {g | ∃ up ∈ zhegPairIdx d s p, (up.2.1.1 / 2) / s < q₀ ∧ g = zhegPairVal d s p up}

private def midSet (d : PaddedDecomp f M k) (s p q₀ : ℕ) : Set (BooleanFunction n) :=
  stageSet d s p q₀ ∪
    (⋃ up ∈ (zhegPairIdx d s p).filter (fun up => (up.2.1.1 / 2) / s = q₀),
      {zhegPairVal d s p up}) ∪
    (⋃ r ∈ (zhegOddIdx d s p).filter (fun r => (r.1 / 2) / s = q₀),
      {zhegOddVal d s p r})

private def intraSet (d : PaddedDecomp f M k) (s q₀ b : ℕ) : Set (BooleanFunction n) :=
  {g | ∃ i : Fin M, i.1 / s = q₀ ∧ i.1 % s < b ∧ g = d.gFn i}

private def stageGates (M s q₀ b : ℕ) : Finset (Fin M) :=
  univ.filter fun i : Fin M => i.1 / s = q₀ ∧ i.1 % s < b

private theorem synth_row_in_stage (d : PaddedDecomp f M k) {s p : ℕ} (hs : 0 < s) (hp : 0 < p)
    (q₀ b : ℕ) (r : Fin (2 * M)) (hr_stage : (r.1 / 2) / s = q₀) (hr_mod : (r.1 / 2) % s = b) :
    CostSynthesis interpretation andCost (midSet d s p q₀ ∪ intraSet d s q₀ b)
      {hFn d r} (p + s) 0 := by
  have hzero_mem : constZero n ∈ midSet d s p q₀ ∪ intraSet d s q₀ b := by
    have h0 : constZero n ∈ ({constZero n, constOne n} : Set (BooleanFunction n)) := Or.inl rfl
    simp only [midSet, stageSet, Set.mem_union]
    tauto
  have hmem : ∀ idx ∈ zhegRowParts d s p r,
      zhegPartVal d s p r idx ∈ midSet d s p q₀ ∪ intraSet d s q₀ b := by
    intro idx hidx
    unfold zhegRowParts at hidx
    rcases mem_union.mp hidx with h1234 | h5
    · rcases mem_union.mp h1234 with h123 | h4
      · rcases mem_union.mp h123 with h12 | h3
        · rcases mem_union.mp h12 with h1 | h2
          · split_ifs at h1 with hcH
            · rw [mem_singleton.mp h1]
              have h1' : zhegPartVal d s p r .constOne ∈
                  ({constZero n, constOne n} : Set (BooleanFunction n)) := Or.inr rfl
              simp only [midSet, stageSet, Set.mem_union]
              tauto
            · exact (notMem_empty _ h1).elim
          · obtain ⟨r', hr', rfl⟩ := mem_map.mp h2
            have hne := (mem_filter.mp hr').2
            let up : ℕ × (Fin (2 * M) × Fin (2 * M)) := (r.1 / p, (min r r', max r r'))
            have hup_mem : up ∈ zhegPairIdx d s p :=
              mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (div_lt_ceilDiv r.isLt hp),
                mem_univ _⟩, hne⟩
            have hmin_le : ((min r r').1 / 2) / s ≤ q₀ := by
              rw [← hr_stage]
              exact Nat.div_le_div_right (Nat.div_le_div_right (min_le_left r r'))
            rcases lt_or_eq_of_le hmin_le with hlt_q | heq_q
            · have hp_mem : zhegPartVal d s p r (peerEmb M r') ∈
                  {g | ∃ up ∈ zhegPairIdx d s p,
                    (up.2.1.1 / 2) / s < q₀ ∧ g = zhegPairVal d s p up} :=
                ⟨up, hup_mem, hlt_q, rfl⟩
              simp only [midSet, stageSet, Set.mem_union]
              tauto
            · have hp_mem : zhegPartVal d s p r (peerEmb M r') ∈
                  ⋃ up ∈ (zhegPairIdx d s p).filter (fun up => (up.2.1.1 / 2) / s = q₀),
                    {zhegPairVal d s p up} := by
                rw [Set.mem_iUnion₂]
                exact ⟨up, mem_filter.mpr ⟨hup_mem, heq_q⟩, rfl⟩
              simp only [midSet, Set.mem_union]
              tauto
        · split_ifs at h3 with hne
          · rw [mem_singleton.mp h3]
            have ho_mem : zhegPartVal d s p r .odd ∈
                ⋃ r ∈ (zhegOddIdx d s p).filter (fun r => (r.1 / 2) / s = q₀),
                  {zhegOddVal d s p r} := by
              rw [Set.mem_iUnion₂]
              exact ⟨r, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ r, hne⟩, hr_stage⟩, rfl⟩
            simp only [midSet, Set.mem_union]
            tauto
          · exact (notMem_empty _ h3).elim
      · split_ifs at h4 with hne
        · rw [mem_singleton.mp h4]
          have htail_mem : zhegPartVal d s p r .xTail ∈ xGroupSet n s :=
            ⟨n / s, Additive.matrixTailSet d.aX s r, hne,
              fun _ hj => Additive.div_eq_of_mem_matrixTailSet hj, rfl⟩
          simp only [midSet, stageSet, Set.mem_union]
          tauto
        · exact (notMem_empty _ h4).elim
    · obtain ⟨ℓ, hℓ, rfl⟩ := mem_map.mp h5
      obtain ⟨_, hdiv, hlt, _⟩ := mem_filter.mp hℓ
      have hmod_lt : ℓ.1 % s < b := by
        have h1 := Nat.div_add_mod ℓ.1 s
        have h2 := Nat.div_add_mod (r.1 / 2) s
        rw [hdiv, hr_stage] at h1
        rw [hr_stage, hr_mod] at h2
        omega
      exact Or.inr ⟨ℓ, hdiv.trans hr_stage, hmod_lt, rfl⟩
  have hsum := sum_of_mem_of_zero (G := Bool) (I := interpretation) (w := andCost)
    (addOp := Op.xor) rfl (fun _ => rfl) rfl hzero_mem (zhegRowParts d s p r)
    (zhegPartVal d s p r) hmem
  have hfun : (fun x => ∑ idx ∈ zhegRowParts d s p r, zhegPartVal d s p r idx x) = hFn d r :=
    funext (sum_zhegRowParts_eq d hs p r)
  rw [hfun] at hsum
  have hcard := card_zhegRowParts_le d hs hp r
  exact hsum.mono Set.Subset.rfl Set.Subset.rfl (by omega) le_rfl

private theorem synth_intra_loop (d : PaddedDecomp f M k) {s p : ℕ} (hs : 0 < s) (hp : 0 < p)
    (q₀ b : ℕ) :
    CostSynthesis interpretation andCost (midSet d s p q₀) (intraSet d s q₀ b)
      (∑ _ ∈ stageGates M s q₀ b, (2 * (p + s) + 1))
      (∑ i ∈ stageGates M s q₀ b, if i.1 < k then 1 else 0) := by
  induction b with
  | zero =>
    have hempty_gates : stageGates M s q₀ 0 = ∅ := by
      ext i
      simp [stageGates]
    have hempty_set : intraSet d s q₀ 0 = ∅ := by
      ext g
      simp [intraSet]
    rw [hempty_gates, hempty_set, sum_empty, sum_empty]
    exact CostSynthesis.of_subset (Set.empty_subset _)
  | succ b ih =>
    by_cases hvalid : b < s ∧ q₀ * s + b < M
    · obtain ⟨hbs, hiM⟩ := hvalid
      let i₀ : Fin M := ⟨q₀ * s + b, hiM⟩
      have hi₀_div : i₀.1 / s = q₀ := by
        dsimp only [i₀]
        rw [mul_comm, Nat.mul_add_div hs, Nat.div_eq_of_lt hbs, add_zero]
      have hi₀_mod : i₀.1 % s = b := by
        dsimp only [i₀]
        rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hbs]
      let r₀ : Fin (2 * M) := ⟨2 * i₀.1, by omega⟩
      let r₁ : Fin (2 * M) := ⟨2 * i₀.1 + 1, by omega⟩
      have hr₀_half : r₀.1 / 2 = i₀.1 := by dsimp [r₀]; omega
      have hr₁_half : r₁.1 / 2 = i₀.1 := by dsimp [r₁]; omega
      have hh0 := synth_row_in_stage d hs hp q₀ b r₀ (hr₀_half ▸ hi₀_div) (hr₀_half ▸ hi₀_mod)
      have hh1 := synth_row_in_stage d hs hp q₀ b r₁ (hr₁_half ▸ hi₀_div) (hr₁_half ▸ hi₀_mod)
      have hg_step : CostSynthesis interpretation andCost
          (midSet d s p q₀ ∪ intraSet d s q₀ b) {d.gFn i₀}
          (2 * (p + s) + 1) (if i₀.1 < k then 1 else 0) := by
        by_cases hik : i₀.1 < k
        · let args : Fin 2 → BooleanFunction n := fun t => if t.1 = 0 then hFn d r₀ else hFn d r₁
          have hand_raw := CostSynthesis.gate (I := interpretation) (w := andCost)
            (s := (midSet d s p q₀ ∪ intraSet d s q₀ b) ∪ ({hFn d r₀} ∪ {hFn d r₁}))
            Op.and args fun t => by
              dsimp only [args]
              split_ifs
              · exact Or.inr (Or.inl rfl)
              · exact Or.inr (Or.inr rfl)
          have hfun_eq : (fun x => interpretation Op.and (fun t => args t x)) = d.gFn i₀ := by
            funext x
            rw [d.gFn_lt i₀ hik x]
            rfl
          rw [hfun_eq] at hand_raw
          have hcomb := (hh0.union hh1).trans hand_raw
          exact hcomb.mono Set.Subset.rfl Set.Subset.rfl (by omega) (by simp [hik])
        · have hge : k ≤ i₀.1 := Nat.le_of_not_lt hik
          have h0_mem : d.gFn i₀ ∈ midSet d s p q₀ ∪ intraSet d s q₀ b := by
            rw [d.gFn_ge i₀ hge]
            have h0 : constZero n ∈ ({constZero n, constOne n} : Set (BooleanFunction n)) :=
              Or.inl rfl
            simp only [midSet, stageSet, Set.mem_union]
            tauto
          exact (CostSynthesis.of_mem h0_mem).mono Set.Subset.rfl Set.Subset.rfl
            (by omega) (by simp [hik])
      have htot := ih.comp hg_step
      have hset_eq : intraSet d s q₀ b ∪ {d.gFn i₀} = intraSet d s q₀ (b + 1) := by
        ext g
        simp only [intraSet, Set.mem_union, Set.mem_ofPred, Set.mem_singleton_iff]
        constructor
        · rintro (⟨i, hd, hm, rfl⟩ | rfl)
          · exact ⟨i, hd, Nat.lt_succ_of_lt hm, rfl⟩
          · exact ⟨i₀, hi₀_div, by omega, rfl⟩
        · rintro ⟨i, hd, hm, rfl⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | heq
          · exact Or.inl ⟨i, hd, hlt, rfl⟩
          · refine Or.inr (congrArg d.gFn (Fin.ext ?_))
            rw [← Nat.div_add_mod i.1 s, hd, heq]
            dsimp only [i₀]
            ring
      have hgates_eq : stageGates M s q₀ (b + 1) = insert i₀ (stageGates M s q₀ b) := by
        ext i
        simp only [stageGates, mem_filter, mem_univ, true_and, mem_insert]
        constructor
        · rintro ⟨hd, hm⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | heq
          · exact Or.inr ⟨hd, hlt⟩
          · refine Or.inl (Fin.ext ?_)
            rw [← Nat.div_add_mod i.1 s, hd, heq]
            dsimp only [i₀]
            ring
        · rintro (rfl | ⟨hd, hlt⟩)
          · exact ⟨hi₀_div, by omega⟩
          · exact ⟨hd, Nat.lt_succ_of_lt hlt⟩
      have hi₀_notMem : i₀ ∉ stageGates M s q₀ b := by
        simp [stageGates, hi₀_mod]
      rw [hset_eq] at htot
      rw [hgates_eq, sum_insert hi₀_notMem, sum_insert hi₀_notMem]
      exact htot.mono Set.Subset.rfl Set.Subset.rfl (by omega) (by omega)
    · have hsame_gates : stageGates M s q₀ (b + 1) = stageGates M s q₀ b := by
        ext i
        simp only [stageGates, mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨hd, hm⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | heq
          · exact ⟨hd, hlt⟩
          · exfalso
            apply hvalid
            refine ⟨heq ▸ Nat.mod_lt i.1 hs, ?_⟩
            have hi_eq : q₀ * s + b = i.1 := by
              have hdiv := Nat.div_add_mod' i.1 s
              rwa [hd, heq] at hdiv
            exact hi_eq ▸ i.isLt
        · rintro ⟨hd, hlt⟩
          exact ⟨hd, Nat.lt_succ_of_lt hlt⟩
      have hsame_set : intraSet d s q₀ (b + 1) = intraSet d s q₀ b := by
        ext g
        simp only [intraSet, Set.mem_ofPred]
        constructor
        · rintro ⟨i, hd, hm, rfl⟩
          have hmem : i ∈ stageGates M s q₀ (b + 1) := mem_filter.mpr ⟨mem_univ i, hd, hm⟩
          rw [hsame_gates] at hmem
          exact ⟨i, (mem_filter.mp hmem).2.1, (mem_filter.mp hmem).2.2, rfl⟩
        · rintro ⟨i, hd, hlt, rfl⟩
          exact ⟨i, hd, Nat.lt_succ_of_lt hlt, rfl⟩
      rw [hsame_gates, hsame_set]
      exact ih

private theorem synth_stage_step (d : PaddedDecomp f M k) {s p : ℕ} (hs : 0 < s) (hp : 0 < p)
    (q₀ : ℕ) :
    CostSynthesis interpretation andCost (stageSet d s p q₀) (stageSet d s p (q₀ + 1))
      ((∑ up ∈ (zhegPairIdx d s p).filter (fun up => (up.2.1.1 / 2) / s = q₀),
          (#(pairedCols (hasZhegCol d s) p up.1 up.2.1 up.2.2) - 1)) +
        (∑ r ∈ (zhegOddIdx d s p).filter (fun r => (r.1 / 2) / s = q₀),
          (#(oddCols (hasZhegCol d s) p r) - 1)) +
        (∑ _ ∈ (univ : Finset (Fin M)).filter (fun i => i.1 / s = q₀), (2 * (p + s) + 1)) +
        (if q₀ < M / s then 2 ^ s - s - 1 else 0))
      (∑ i ∈ (univ : Finset (Fin M)).filter (fun i => i.1 / s = q₀),
        if i.1 < k then 1 else 0) := by
  have hcol_avail (c : ZhegCol n M s)
      (hc : match c with | .inl _ => True | .inr cg => cg.1.1 < q₀) :
      zhegColVal d c ∈ stageSet d s p q₀ := by
    cases c with
    | inl cx =>
      have hx : zhegColVal d (.inl cx) ∈ xGroupSet n s := by
        refine ⟨cx.1.1, cx.2.1.map (Additive.fullBlockEmb cx.1), cx.2.2.map, ?_, ?_⟩
        · intro j hj
          obtain ⟨a, _, rfl⟩ := mem_map.mp hj
          exact Additive.fullBlockEmb_div cx.1 a
        · funext x
          rw [sum_map]
          rfl
      simp only [stageSet, Set.mem_union]
      tauto
    | inr cg =>
      have hg : zhegColVal d (.inr cg) ∈
          {g | ∃ cg' : Additive.FullCol M s, cg'.1.1 < q₀ ∧ g = zhegColVal d (.inr cg')} :=
        ⟨cg, hc, rfl⟩
      simp only [stageSet, Set.mem_union]
      tauto
  -- Substep A1: Paired sums first needed at stage `q₀`.
  let pairQ := (zhegPairIdx d s p).filter fun up => (up.2.1.1 / 2) / s = q₀
  have hpair_one (up : ℕ × (Fin (2 * M) × Fin (2 * M))) (hup : up ∈ pairQ) :
      CostSynthesis interpretation andCost (stageSet d s p q₀) {zhegPairVal d s p up}
        (#(pairedCols (hasZhegCol d s) p up.1 up.2.1 up.2.2) - 1) 0 := by
    obtain ⟨hup_idx, hup_q⟩ := mem_filter.mp hup
    refine nonempty_sum_of_mem (G := Bool) (I := interpretation) (w := andCost) (addOp := Op.xor)
      rfl (fun _ => rfl) rfl _ (mem_filter.mp hup_idx).2 (zhegColVal d) fun c hc => ?_
    apply hcol_avail c
    cases c with
    | inl _ => trivial
    | inr cg =>
      have hc₁ := (mem_pairedCols_imp hc).2.2.2.1
      have hlt := (of_decide_eq_true hc₁).1
      omega
  have hpairs := CostSynthesis.biUnion pairQ (fun up => {zhegPairVal d s p up})
    (fun up => #(pairedCols (hasZhegCol d s) p up.1 up.2.1 up.2.2) - 1) (fun _ => 0) hpair_one
  -- Substep A2: Odd sums at stage `q₀`.
  let oddQ := (zhegOddIdx d s p).filter fun r => (r.1 / 2) / s = q₀
  have hodd_one (r : Fin (2 * M)) (hr : r ∈ oddQ) :
      CostSynthesis interpretation andCost (stageSet d s p q₀) {zhegOddVal d s p r}
        (#(oddCols (hasZhegCol d s) p r) - 1) 0 := by
    obtain ⟨hr_idx, hr_q⟩ := mem_filter.mp hr
    refine nonempty_sum_of_mem (G := Bool) (I := interpretation) (w := andCost) (addOp := Op.xor)
      rfl (fun _ => rfl) rfl _ (mem_filter.mp hr_idx).2 (zhegColVal d) fun c hc => ?_
    apply hcol_avail c
    cases c with
    | inl _ => trivial
    | inr cg =>
      have hc_r := mem_oddCols_imp hc
      have hlt := (of_decide_eq_true hc_r).1
      omega
  have hodds := CostSynthesis.biUnion oddQ (fun r => {zhegOddVal d s p r})
    (fun r => #(oddCols (hasZhegCol d s) p r) - 1) (fun _ => 0) hodd_one
  have hmid : CostSynthesis interpretation andCost (stageSet d s p q₀) (midSet d s p q₀)
      ((∑ up ∈ pairQ, (#(pairedCols (hasZhegCol d s) p up.1 up.2.1 up.2.2) - 1)) +
        (∑ r ∈ oddQ, (#(oddCols (hasZhegCol d s) p r) - 1))) 0 := by
    have h := ((CostSynthesis.of_subset Set.Subset.rfl).union hpairs).union hodds
    exact h.mono Set.Subset.rfl Set.Subset.rfl (by omega) (by simp)
  -- Substep B: Sequential conjunction gates in stage `q₀`.
  have hintra := synth_intra_loop d hs hp q₀ s
  have hgates_s : stageGates M s q₀ s = univ.filter (fun i : Fin M => i.1 / s = q₀) := by
    ext i
    simp [stageGates, Nat.mod_lt i.1 hs]
  rw [hgates_s] at hintra
  have hmid_intra := hmid.comp
    (hintra.mono Set.subset_union_right Set.Subset.rfl le_rfl le_rfl)
  -- Substep C: Full `g`-block subset sums if `q₀ < M / s`.
  let curGBlockSet : Set (BooleanFunction n) :=
    {g | ∃ cg : Additive.FullCol M s, cg.1.1 = q₀ ∧ g = zhegColVal d (.inr cg)}
  have hgblock_step : CostSynthesis interpretation andCost
      (stageSet d s p q₀ ∪ (midSet d s p q₀ ∪ intraSet d s q₀ s)) curGBlockSet
      (if q₀ < M / s then 2 ^ s - s - 1 else 0) 0 := by
    by_cases hq_lt : q₀ < M / s
    · let qFin : Fin (M / s) := ⟨q₀, hq_lt⟩
      let Fg : Fin s → BooleanFunction n := fun a => d.gFn (Additive.fullBlockEmb qFin a)
      have hFg_mem : ∀ a : Fin s, Fg a ∈ stageSet d s p q₀ ∪
          (midSet d s p q₀ ∪ intraSet d s q₀ s) := fun a =>
        Or.inr (Or.inr ⟨Additive.fullBlockEmb qFin a, Additive.fullBlockEmb_div qFin a,
          Nat.mod_lt _ hs, rfl⟩)
      have hgblock := block_nonempty_subSums (G := Bool) (I := interpretation) (w := andCost)
        (addOp := Op.xor) rfl (fun _ => rfl) rfl Fg hFg_mem
      refine hgblock.mono Set.Subset.rfl ?_ (by simp [hq_lt]) le_rfl
      rintro _ ⟨⟨q', T, hT⟩, hcg, rfl⟩
      have hq_eq : q' = qFin := Fin.ext hcg
      subst hq_eq
      exact ⟨T, hT, rfl⟩
    · refine (CostSynthesis.of_subset ?_).mono Set.Subset.rfl Set.Subset.rfl (by simp [hq_lt])
        le_rfl
      rintro _ ⟨cg, hcg, rfl⟩
      exact (hq_lt (hcg ▸ cg.1.isLt)).elim
  have hall := hmid_intra.comp hgblock_step
  refine hall.mono Set.Subset.rfl ?_ (by dsimp only [pairQ, oddQ]; rfl) (by simp)
  -- Prove `stageSet d s p (q₀ + 1)` is contained in the synthesized union.
  intro g hg
  rcases hg with
    (((((hg_in | hg_c) | hg_x) | ⟨i, hi, rfl⟩) | ⟨cg, hcg, rfl⟩) | ⟨up, hup, hq, rfl⟩)
  · simp only [midSet, stageSet, Set.mem_union]; tauto
  · simp only [midSet, stageSet, Set.mem_union]; tauto
  · simp only [midSet, stageSet, Set.mem_union]; tauto
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · have h_old : d.gFn i ∈ {g | ∃ i' : Fin M, i'.1 / s < q₀ ∧ g = d.gFn i'} :=
        ⟨i, hlt, rfl⟩
      simp only [midSet, stageSet, Set.mem_union]; tauto
    · have h_new : d.gFn i ∈ intraSet d s q₀ s := ⟨i, heq, Nat.mod_lt i.1 hs, rfl⟩
      simp only [Set.mem_union]; tauto
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hcg with hlt | heq
    · have h_old : zhegColVal d (.inr cg) ∈
          {g | ∃ cg' : Additive.FullCol M s, cg'.1.1 < q₀ ∧ g = zhegColVal d (.inr cg')} :=
        ⟨cg, hlt, rfl⟩
      simp only [midSet, stageSet, Set.mem_union]; tauto
    · exact Or.inr ⟨cg, heq, rfl⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hlt | heq
    · have h_old : zhegPairVal d s p up ∈
          {g | ∃ up' ∈ zhegPairIdx d s p,
            (up'.2.1.1 / 2) / s < q₀ ∧ g = zhegPairVal d s p up'} :=
        ⟨up, hup, hlt, rfl⟩
      simp only [midSet, stageSet, Set.mem_union]; tauto
    · have h_new : zhegPairVal d s p up ∈
          ⋃ up' ∈ (zhegPairIdx d s p).filter (fun up' => (up'.2.1.1 / 2) / s = q₀),
            {zhegPairVal d s p up'} := by
        rw [Set.mem_iUnion₂]
        exact ⟨up, mem_filter.mpr ⟨hup, heq⟩, rfl⟩
      simp only [midSet, Set.mem_union]; tauto

private inductive OutPartIdx (n M : ℕ) where
  | constOne
  | inX (j : Fin n)
  | gateG (ℓ : Fin M)
  deriving DecidableEq

private def outParts (d : PaddedDecomp f M k) : Finset (OutPartIdx n M) :=
  (if d.outC then {.constOne} else ∅) ∪
    ((univ.filter fun j : Fin n => d.outX j = true).map ⟨.inX, fun _ _ h => by injection h⟩) ∪
    ((univ.filter fun ℓ : Fin M => d.outG ℓ = true).map ⟨.gateG, fun _ _ h => by injection h⟩)

private def outPartVal (d : PaddedDecomp f M k) : OutPartIdx n M → BooleanFunction n
  | .constOne => Boolean.Zhegalkin.constOne n
  | .inX j => fun x => x j
  | .gateG ℓ => d.gFn ℓ

private theorem card_outParts_le (d : PaddedDecomp f M k) :
    #(outParts d) ≤ n + M + 1 := by
  unfold outParts
  set p1 : Finset (OutPartIdx n M) := if d.outC then {.constOne} else ∅
  set p2 : Finset (OutPartIdx n M) :=
    (univ.filter fun j : Fin n => d.outX j = true).map ⟨.inX, fun _ _ h => by injection h⟩
  set p3 : Finset (OutPartIdx n M) :=
    (univ.filter fun ℓ : Fin M => d.outG ℓ = true).map ⟨.gateG, fun _ _ h => by injection h⟩
  have hc1 : #p1 ≤ 1 := by dsimp only [p1]; split_ifs <;> simp
  have hc2 : #p2 ≤ n := by
    rw [card_map]
    exact (card_filter_le _ _).trans_eq (by simp)
  have hc3 : #p3 ≤ M := by
    rw [card_map]
    exact (card_filter_le _ _).trans_eq (by simp)
  have hu2 := card_union_le (p1 ∪ p2) p3
  have hu1 := card_union_le p1 p2
  omega

private theorem sum_outParts_eq (d : PaddedDecomp f M k) (x : Fin n → Bool) :
    (∑ idx ∈ outParts d, outPartVal d idx x) = f x := by
  rw [d.out_eq x]
  unfold outParts linForm
  set p1 : Finset (OutPartIdx n M) := if d.outC then {.constOne} else ∅
  set p2 : Finset (OutPartIdx n M) :=
    (univ.filter fun j : Fin n => d.outX j = true).map ⟨.inX, fun _ _ h => by injection h⟩
  set p3 : Finset (OutPartIdx n M) :=
    (univ.filter fun ℓ : Fin M => d.outG ℓ = true).map ⟨.gateG, fun _ _ h => by injection h⟩
  have hd12 : Disjoint p1 p2 := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨_, _, rfl⟩ := mem_map.mp hz2
    dsimp only [p1] at hz1; split_ifs at hz1 <;> simp at hz1
  have hd123 : Disjoint (p1 ∪ p2) p3 := by
    rw [Finset.disjoint_left]
    intro z hz12 hz3
    obtain ⟨_, _, rfl⟩ := mem_map.mp hz3
    rcases mem_union.mp hz12 with hz1 | hz2
    · dsimp only [p1] at hz1; split_ifs at hz1 <;> simp at hz1
    · obtain ⟨_, _, habs⟩ := mem_map.mp hz2; nomatch habs
  rw [sum_union hd123, sum_union hd12, sum_map, sum_map]
  have hs1 : (∑ z ∈ p1, outPartVal d z x) = if d.outC then true else (0 : Bool) := by
    dsimp only [p1]
    split_ifs <;> simp [outPartVal, constOne]
  rw [hs1, ← sum_filter, ← sum_filter]
  rfl

/-- **Explicit staged multiplicative-to-total synthesis bound over `{⊕, ∧, 1}`**
([Sergeev, Theorem 1 (upper bound), p. 3][Sergeev2013AdditiveMultiplicative]):
every `n`-input Boolean function `f` computed by a `{⊕, ∧, 1}`-circuit `c` with at most `M`
conjunction gates (`c.program.cost andCost ≤ M`) can be computed by an acyclic `{⊕, ∧, 1}`-circuit
`c'` using no more conjunction gates (`c'.program.cost andCost ≤ c.program.cost andCost`) and total
size at most `totalBound n M s p`, for any block/stage width `0 < s` and horizontal section height
`0 < p`. -/
theorem exists_circuit_of_andCost_le_bound {n M : ℕ} {f : BooleanFunction n}
    (c : Circuit signature n 1) (hc : c.Computes interpretation (single f))
    (hM : c.program.cost andCost ≤ M) {s p : ℕ} (hs : 0 < s) (hp : 0 < p) :
    ∃ c' : Circuit signature n 1,
      c'.Computes interpretation (single f) ∧
      c'.program.cost andCost ≤ c.program.cost andCost ∧
      c'.size ≤ totalBound n M s p := by
  classical
  let k := c.program.cost andCost
  obtain ⟨d⟩ := exists_paddedDecomp c hc hM
  -- Stage 0 setup: `{constZero, constOne}` and `xGroupSet`.
  have hconsts := synth_consts n
  have hxgroup := all_group_subSums (G := Bool) (I := interpretation) (w := andCost)
    (addOp := Op.xor) (s := inputs n) hs rfl (fun _ => rfl) rfl
    (fun j x => x j) (fun j => ⟨j, rfl⟩)
  have hstage0 : CostSynthesis interpretation andCost (inputs n) (stageSet d s p 0)
      (2 + (n * 2 ^ s) / s) 0 := by
    have h0 := ((CostSynthesis.of_subset Set.Subset.rfl).union hconsts).union hxgroup
    refine h0.mono Set.Subset.rfl ?_ (by omega) (by simp)
    intro g hg
    rcases hg with (((((hg_in | hg_c) | hg_x) | ⟨i, hi, _⟩) | ⟨cg, hcg, _⟩) | ⟨up, _, hq, _⟩)
    · exact Or.inl (Or.inl hg_in)
    · exact Or.inl (Or.inr hg_c)
    · exact Or.inr hg_x
    · exact (Nat.not_lt_zero _ hi).elim
    · exact (Nat.not_lt_zero _ hcg).elim
    · exact (Nat.not_lt_zero _ hq).elim
  -- Inductive run across stages `q₀ = 0 .. M / s` (`Q = M / s + 1` stages).
  let Q := M / s + 1
  let stageTC (q₀ : ℕ) : ℕ :=
    (∑ up ∈ (zhegPairIdx d s p).filter (fun up => (up.2.1.1 / 2) / s = q₀),
        (#(pairedCols (hasZhegCol d s) p up.1 up.2.1 up.2.2) - 1)) +
      (∑ r ∈ (zhegOddIdx d s p).filter (fun r => (r.1 / 2) / s = q₀),
        (#(oddCols (hasZhegCol d s) p r) - 1)) +
      (∑ _ ∈ (univ : Finset (Fin M)).filter (fun i => i.1 / s = q₀), (2 * (p + s) + 1)) +
      (if q₀ < M / s then 2 ^ s - s - 1 else 0)
  let stageWC (q₀ : ℕ) : ℕ :=
    ∑ i ∈ (univ : Finset (Fin M)).filter (fun i => i.1 / s = q₀),
      if i.1 < k then 1 else 0
  have hstages : ∀ T : ℕ,
      CostSynthesis interpretation andCost (stageSet d s p 0) (stageSet d s p T)
        (∑ q₀ ∈ range T, stageTC q₀) (∑ q₀ ∈ range T, stageWC q₀) := by
    intro T
    induction T with
    | zero =>
      simpa only [range_zero, sum_empty] using CostSynthesis.of_subset Set.Subset.rfl
    | succ T ih =>
      have hstep := ih.trans
        ((synth_stage_step d hs hp T).mono Set.subset_union_right Set.Subset.rfl le_rfl le_rfl)
      rw [sum_range_succ, sum_range_succ]
      exact hstep
  have hall_stages := hstage0.trans
    ((hstages Q).mono Set.subset_union_right Set.Subset.rfl le_rfl le_rfl)
  -- Final output linear form from `stageSet d s p Q`.
  have hdiv_Q {j : ℕ} (hj : j ≤ M) : j / s < Q :=
    Nat.lt_succ_of_le (Nat.div_le_div_right hj)
  have hzero_Q : constZero n ∈ stageSet d s p Q :=
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl rfl)))))
  have hout_mem : ∀ idx ∈ outParts d, outPartVal d idx ∈ stageSet d s p Q := by
    intro idx _
    cases idx with
    | constOne => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr rfl)))))
    | inX j => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨j, rfl⟩))))
    | gateG ℓ => exact Or.inl (Or.inl (Or.inr ⟨ℓ, hdiv_Q ℓ.isLt.le, rfl⟩))
  have hout_raw := sum_of_mem_of_zero (G := Bool) (I := interpretation) (w := andCost)
    (addOp := Op.xor) rfl (fun _ => rfl) rfl hzero_Q (outParts d) (outPartVal d) hout_mem
  have hout_fn : (fun x => ∑ idx ∈ outParts d, outPartVal d idx x) = f :=
    funext (sum_outParts_eq d)
  rw [hout_fn] at hout_raw
  have hout_card := card_outParts_le d
  have hout : CostSynthesis interpretation andCost (stageSet d s p Q) {f} (n + M) 0 :=
    hout_raw.mono Set.Subset.rfl Set.Subset.rfl (by omega) le_rfl
  have hfull_synth := hall_stages.trans
    (hout.mono Set.subset_union_right Set.Subset.rfl le_rfl le_rfl)
  -- Sum the stage gate budgets and compare with `totalBound n M s p` and `k`.
  have hpair_sum :
      (∑ q₀ ∈ range Q,
        ∑ up ∈ (zhegPairIdx d s p).filter (fun up => (up.2.1.1 / 2) / s = q₀),
          (#(pairedCols (hasZhegCol d s) p up.1 up.2.1 up.2.2) - 1)) ≤
      (M * (M + 2 * n)) / (2 * s) := by
    have hmaps : ∀ up ∈ zhegPairIdx d s p, (up.2.1.1 / 2) / s ∈ range Q := fun up _ =>
      mem_range.mpr (hdiv_Q (by omega))
    rw [sum_fiberwise_of_maps_to hmaps]
    have h₁ : ∑ up ∈ zhegPairIdx d s p,
          (#(pairedCols (hasZhegCol d s) p up.1 up.2.1 up.2.2) - 1) ≤
        ∑ u ∈ range ((2 * M) ⌈/⌉ p), ∑ pair : Fin (2 * M) × Fin (2 * M),
          #(pairedCols (hasZhegCol d s) p u pair.1 pair.2) :=
      ((sum_le_sum_of_subset (filter_subset _ _)).trans
        (sum_le_sum fun _ _ => Nat.sub_le _ _)).trans_eq (sum_product _ _ _)
    apply (Nat.le_div_iff_mul_le (Nat.mul_pos two_pos hs)).mpr
    have h₂ := two_mul_sum_card_pairedCols_le (hasZhegCol d s) hp
    have h₃ := mul_sum_hasZhegCol_le d s
    nlinarith only [h₁, h₂, h₃]
  have hodd_sum :
      (∑ q₀ ∈ range Q,
        ∑ r ∈ (zhegOddIdx d s p).filter (fun r => (r.1 / 2) / s = q₀),
          (#(oddCols (hasZhegCol d s) p r) - 1)) ≤
      ((2 * M) ⌈/⌉ p) * 2 ^ s * ((n + M) ⌈/⌉ s) := by
    have hmaps : ∀ r ∈ zhegOddIdx d s p, (r.1 / 2) / s ∈ range Q := fun r _ =>
      mem_range.mpr (hdiv_Q (by omega))
    rw [sum_fiberwise_of_maps_to hmaps]
    calc ∑ r ∈ zhegOddIdx d s p, (#(oddCols (hasZhegCol d s) p r) - 1)
        ≤ ∑ r : Fin (2 * M), #(oddCols (hasZhegCol d s) p r) :=
          (sum_le_sum_of_subset (filter_subset _ _)).trans
            (sum_le_sum fun _ _ => Nat.sub_le _ _)
      _ ≤ ((2 * M) ⌈/⌉ p) * Fintype.card (ZhegCol n M s) :=
          sum_card_oddCols_le (hasZhegCol d s) hp
      _ ≤ ((2 * M) ⌈/⌉ p) * (2 ^ s * ((n + M) ⌈/⌉ s)) :=
          Nat.mul_le_mul_left _ (card_zhegCol_le n M s hs)
      _ = ((2 * M) ⌈/⌉ p) * 2 ^ s * ((n + M) ⌈/⌉ s) := by ring
  have hgates_sum :
      (∑ q₀ ∈ range Q,
        ∑ _ ∈ (univ : Finset (Fin M)).filter (fun i => i.1 / s = q₀), (2 * (p + s) + 1)) ≤
      2 * M * (p + s + 1) := by
    have hmaps : ∀ i ∈ (univ : Finset (Fin M)), i.1 / s ∈ range Q := fun i _ =>
      mem_range.mpr (hdiv_Q i.isLt.le)
    rw [sum_fiberwise_of_maps_to hmaps, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    nlinarith
  have hgblock_sum :
      (n * 2 ^ s) / s +
        (∑ q₀ ∈ range Q, if q₀ < M / s then 2 ^ s - s - 1 else 0) ≤
      ((n + M) * 2 ^ s) / s := by
    have hsub_sum :
        (∑ q₀ ∈ range Q, if q₀ < M / s then 2 ^ s - s - 1 else 0) =
          (M / s) * (2 ^ s - s - 1) := by
      rw [← sum_filter]
      have hfilt : (range Q).filter (fun q₀ => q₀ < M / s) = range (M / s) := by
        ext q₀
        simp only [Q, mem_filter, mem_range]
        omega
      rw [hfilt, sum_const, card_range, smul_eq_mul]
    rw [hsub_sum]
    have hMs : (M / s) * (2 ^ s - s - 1) ≤ (M * 2 ^ s) / s := by
      have hsub : 2 ^ s - s - 1 ≤ 2 ^ s := (Nat.sub_le _ _).trans (Nat.sub_le _ _)
      apply (Nat.le_div_iff_mul_le hs).mpr
      calc (M / s) * (2 ^ s - s - 1) * s
          ≤ (M / s) * 2 ^ s * s :=
            Nat.mul_le_mul_right s (Nat.mul_le_mul_left _ hsub)
        _ = (s * (M / s)) * 2 ^ s := by ring
        _ ≤ M * 2 ^ s := Nat.mul_le_mul_right _ (Nat.mul_div_le M s)
    have hadd_div : (n * 2 ^ s) / s + (M * 2 ^ s) / s ≤ ((n + M) * 2 ^ s) / s := by
      apply (Nat.le_div_iff_mul_le hs).mpr
      calc ((n * 2 ^ s) / s + (M * 2 ^ s) / s) * s
          = s * ((n * 2 ^ s) / s) + s * ((M * 2 ^ s) / s) := by ring
        _ ≤ n * 2 ^ s + M * 2 ^ s :=
            Nat.add_le_add (Nat.mul_div_le _ s) (Nat.mul_div_le _ s)
        _ = (n + M) * 2 ^ s := by ring
    exact (Nat.add_le_add_left hMs _).trans hadd_div
  have hwc_sum : (∑ q₀ ∈ range Q, stageWC q₀) ≤ k := by
    have hmaps : ∀ i ∈ (univ : Finset (Fin M)), i.1 / s ∈ range Q := fun i _ =>
      mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right i.isLt.le))
    dsimp only [stageWC]
    rw [sum_fiberwise_of_maps_to hmaps, sum_boole, Nat.cast_id]
    have hinj : Set.InjOn Fin.val
        ((univ.filter fun i : Fin M => i.1 < k) : Set (Fin M)) :=
      fun _ _ _ _ h => Fin.ext h
    exact (card_le_card_of_injOn Fin.val
      (fun i hi => mem_range.mpr (mem_filter.mp hi).2) hinj).trans_eq (card_range _)
  have htc_total :
      (2 + (n * 2 ^ s) / s + ∑ q₀ ∈ range Q, stageTC q₀) + (n + M) ≤ totalBound n M s p := by
    dsimp only [stageTC]
    rw [sum_add_distrib, sum_add_distrib, sum_add_distrib]
    unfold totalBound
    linarith only [hpair_sum, hodd_sum, hgates_sum, hgblock_sum]
  obtain ⟨c', hc', hsize, hcost⟩ :=
    (hfull_synth.mono Set.Subset.rfl Set.Subset.rfl htc_total
      (by linarith only [hwc_sum])).exists_circuit
  exact ⟨c', hc', hcost, hsize⟩

end ZhegalkinSynthesis

/-! #### Asymptotic deduction of Theorem 1 (upper bound) -/

private theorem zhegRem_mul_sq_le (n M : ℕ)
    (hL8 : 8 ≤ Nat.log 2 M)
    (hlog6 : 6 * Nat.log 2 (Nat.log 2 M) ≤ Nat.log 2 M)
    (hpow2 : (Nat.log 2 M) ^ 2 ≤ 2 ^ Nat.log 2 M) :
    let L := Nat.log 2 M
    let s := L - 3 * Nat.log 2 L
    let p := (2 * M) / L ^ 2 + 1
    L ^ 2 * (((n + M) * 2 ^ s) / s + 2 * M * (p + s + 1) +
        ((2 * M) ⌈/⌉ p) * 2 ^ s * ((n + M) ⌈/⌉ s) + n + M + 2) ≤
      88 * (M * (M + 2 * n)) := by
  dsimp only
  obtain ⟨hs_pos, hs_le, hL_2s, _, hL2M, hL3⟩ := log_param_props hL8 hlog6 hpow2
  set L := Nat.log 2 M
  set s := L - 3 * Nat.log 2 L
  set p := (2 * M) / L ^ 2 + 1
  have hM_ge2 : 2 ≤ M := by
    have : 8 ^ 2 ≤ L ^ 2 := Nat.pow_le_pow_left hL8 2
    omega
  have hs_le_M : s ≤ M := by
    have hLL2 : L ≤ L ^ 2 := by nlinarith
    exact hs_le.trans (hLL2.trans hL2M)
  have ht1 : L ^ 2 * (((n + M) * 2 ^ s) / s) ≤ 16 * (M * (M + 2 * n)) := by
    have hdiv : L * (((n + M) * 2 ^ s) / s) ≤ 2 * ((n + M) * 2 ^ s) := by
      calc L * (((n + M) * 2 ^ s) / s)
          ≤ (2 * s) * (((n + M) * 2 ^ s) / s) := Nat.mul_le_mul_right _ hL_2s
        _ = 2 * (s * (((n + M) * 2 ^ s) / s)) := by ring
        _ ≤ 2 * ((n + M) * 2 ^ s) := Nat.mul_le_mul_left 2 (Nat.mul_div_le _ s)
    calc L ^ 2 * (((n + M) * 2 ^ s) / s)
        ≤ L ^ 4 * (((n + M) * 2 ^ s) / s) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num))
      _ = L ^ 3 * (L * (((n + M) * 2 ^ s) / s)) := by ring
      _ ≤ L ^ 3 * (2 * ((n + M) * 2 ^ s)) := Nat.mul_le_mul_left _ hdiv
      _ = 2 * (n + M) * (L ^ 3 * 2 ^ s) := by ring
      _ ≤ 2 * (n + M) * (8 * M) := Nat.mul_le_mul_left _ hL3
      _ ≤ 16 * (M * (M + 2 * n)) := by nlinarith
  have ht2 : L ^ 2 * (2 * M * (p + s + 1)) ≤ 38 * (M * (M + 2 * n)) := by
    have hp_le : L ^ 2 * p ≤ 3 * M := by
      calc L ^ 2 * ((2 * M) / L ^ 2 + 1)
          = L ^ 2 * ((2 * M) / L ^ 2) + L ^ 2 := by ring
        _ ≤ 2 * M + M := Nat.add_le_add (Nat.mul_div_le _ _) hL2M
        _ = 3 * M := by ring
    have hs1_le : L ^ 2 * (s + 1) ≤ 16 * M := by
      have hs1_2L : s + 1 ≤ 2 * L := by omega
      have hL3_le : L ^ 3 ≤ L ^ 3 * 2 ^ s :=
        Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) s)
      calc L ^ 2 * (s + 1)
          ≤ L ^ 2 * (2 * L) := Nat.mul_le_mul_left _ hs1_2L
        _ = 2 * L ^ 3 := by ring
        _ ≤ 2 * (L ^ 3 * 2 ^ s) := Nat.mul_le_mul_left 2 hL3_le
        _ ≤ 2 * (8 * M) := Nat.mul_le_mul_left 2 hL3
        _ = 16 * M := by ring
    calc L ^ 2 * (2 * M * (p + s + 1))
        = 2 * M * (L ^ 2 * p + L ^ 2 * (s + 1)) := by ring
      _ ≤ 2 * M * (3 * M + 16 * M) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add hp_le hs1_le)
      _ ≤ 38 * (M * (M + 2 * n)) := by nlinarith
  have ht3 : L ^ 2 * (((2 * M) ⌈/⌉ p) * 2 ^ s * ((n + M) ⌈/⌉ s)) ≤
      32 * (M * (M + 2 * n)) := by
    have hMp : (2 * M) ⌈/⌉ p ≤ L ^ 2 := ceilDiv_div_sq_add_one_le (2 * M) (by omega)
    have hnMs : s * ((n + M) ⌈/⌉ s) ≤ 2 * (M + 2 * n) := by
      have h1 := mul_ceilDiv_le_add (n + M) hs_pos
      omega
    have hL2_le : L ^ 2 ≤ 2 * s * L := by nlinarith
    calc L ^ 2 * (((2 * M) ⌈/⌉ p) * 2 ^ s * ((n + M) ⌈/⌉ s))
        ≤ (2 * s * L) * (((2 * M) ⌈/⌉ p) * 2 ^ s * ((n + M) ⌈/⌉ s)) :=
          Nat.mul_le_mul_right _ hL2_le
      _ = 2 * (((2 * M) ⌈/⌉ p) * (L * 2 ^ s)) * (s * ((n + M) ⌈/⌉ s)) := by ring
      _ ≤ 2 * (L ^ 2 * (L * 2 ^ s)) * (2 * (M + 2 * n)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hMp)) hnMs
      _ = 4 * (L ^ 3 * 2 ^ s) * (M + 2 * n) := by ring
      _ ≤ 4 * (8 * M) * (M + 2 * n) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hL3)
      _ = 32 * (M * (M + 2 * n)) := by ring
  have ht4 : L ^ 2 * (n + M + 2) ≤ 2 * (M * (M + 2 * n)) := by
    calc L ^ 2 * (n + M + 2)
        = L ^ 2 * n + L ^ 2 * M + L ^ 2 * 2 := by ring
      _ ≤ M * n + M * M + M * M :=
          Nat.add_le_add
            (Nat.add_le_add (Nat.mul_le_mul_right n hL2M) (Nat.mul_le_mul_right M hL2M))
            (Nat.mul_le_mul hL2M hM_ge2)
      _ ≤ 2 * (M * (M + 2 * n)) := by nlinarith
  calc L ^ 2 * (((n + M) * 2 ^ s) / s + 2 * M * (p + s + 1) +
          ((2 * M) ⌈/⌉ p) * 2 ^ s * ((n + M) ⌈/⌉ s) + n + M + 2)
      = L ^ 2 * (((n + M) * 2 ^ s) / s) + L ^ 2 * (2 * M * (p + s + 1)) +
          L ^ 2 * (((2 * M) ⌈/⌉ p) * 2 ^ s * ((n + M) ⌈/⌉ s)) + L ^ 2 * (n + M + 2) := by ring
    _ ≤ 16 * (M * (M + 2 * n)) + 38 * (M * (M + 2 * n)) +
          32 * (M * (M + 2 * n)) + 2 * (M * (M + 2 * n)) :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ht1 ht2) ht3) ht4
    _ = 88 * (M * (M + 2 * n)) := by ring

/-- **Asymptotic multiplicative-to-total circuit synthesis upper bound over `{⊕, ∧, 1}`**
([Sergeev, Theorem 1 (upper bound), p. 1][Sergeev2013AdditiveMultiplicative]):
for every `ε > 0`, there exists `M₀` such that for all `M ≥ M₀`, all `n : ℕ`, and every Boolean
function `f : BooleanFunction n` computed by a `{⊕, ∧, 1}`-circuit `c` with at most `M` conjunction
gates, `f` is computed by a `{⊕, ∧, 1}`-circuit `c'` with no more conjunction gates than `c` and
total gate count at most `(1 / 2 + ε) * M * (M + 2 * n) / Real.logb 2 M`.

Sergeev states Theorem 1 under `M = Ω(n)` and separately notes asymptotic optimality on pp. 1–2;
bounding the explicit `(s, p)` synthesis budget `totalBound n M s p` directly gives a uniform
threshold in `M` for all `n : ℕ` and recovers the published upper bound when `M = Ω(n)`. -/
theorem exists_circuit_of_andCost_le {ε : ℝ} (hε : 0 < ε) :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ {n M : ℕ}, M₀ ≤ M →
      ∀ {f : BooleanFunction n} (c : Circuit signature n 1),
        c.Computes interpretation (single f) →
        c.program.cost andCost ≤ M →
        ∃ c' : Circuit signature n 1,
          c'.Computes interpretation (single f) ∧
          c'.program.cost andCost ≤ c.program.cost andCost ∧
          (c'.size : ℝ) ≤
            (1 / 2 + ε) * (M : ℝ) * (M + 2 * n : ℝ) / Real.logb 2 M := by
  let C : ℕ := ⌈((4 + 2 * 88 : ℕ) : ℝ) / ε⌉₊ + 10
  obtain ⟨L₁, hL₁8, _, hL₁⟩ := exists_log_threshold C
  let M₀ : ℕ := 2 ^ L₁
  have hM₀_ge2 : 2 ≤ M₀ := by
    have : 2 ^ 1 ≤ 2 ^ L₁ := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [M₀] using this
  refine ⟨M₀, hM₀_ge2, fun {n M} hMM₀ {f} c hc hM => ?_⟩
  have hL_ge : L₁ ≤ Nat.log 2 M := Nat.le_log_of_pow_le one_lt_two hMM₀
  obtain ⟨hClog, h6log, hpow2⟩ := hL₁ hL_ge
  have hL8 : 8 ≤ Nat.log 2 M := hL₁8.trans hL_ge
  obtain ⟨hs_pos, _, _, _, _, _⟩ := log_param_props hL8 h6log hpow2
  set L := Nat.log 2 M
  set s := L - 3 * Nat.log 2 L
  set p := (2 * M) / L ^ 2 + 1
  obtain ⟨c', hc', hcost, hsize⟩ :=
    exists_circuit_of_andCost_le_bound c hc hM hs_pos (Nat.succ_pos _)
  refine ⟨c', hc', hcost, (Nat.cast_le.mpr hsize).trans ?_⟩
  set W : ℕ := M * (M + 2 * n)
  set rem : ℕ := ((n + M) * 2 ^ s) / s + 2 * M * (p + s + 1) +
    ((2 * M) ⌈/⌉ p) * 2 ^ s * ((n + M) ⌈/⌉ s) + n + M + 2
  have htb_eq : totalBound n M s p = W / (2 * s) + rem := by
    unfold totalBound W rem
    ring
  rw [htb_eq, Nat.cast_add]
  have hbound := div_two_sub_add_rem_le hε hL8 h6log hpow2 hClog (le_refl W)
    (zhegRem_mul_sq_le n M hL8 h6log hpow2)
  have hW_cast : (W : ℝ) = (M : ℝ) * (M + 2 * n : ℝ) := by
    dsimp only [W]
    push_cast
    ring
  refine hbound.trans_eq ?_
  rw [hW_cast]
  ring

/-- **Multiplicative-to-total complexity upper bound over `{⊕, ∧, 1}`**
([Sergeev, Theorem 1 (upper bound), p. 1][Sergeev2013AdditiveMultiplicative]):
for every `ε > 0`, there exists `M₀` such that for all `M ≥ M₀`, all `n : ℕ`, and every
`n`-variable Boolean function `f` of multiplicative complexity at most `M`
(`multiplicativeComplexity (single f) ≤ M`), the total `{⊕, ∧, 1}` circuit complexity satisfies
`complexity interpretation (single f) ≤ (1 / 2 + ε) * M * (M + 2 * n) / Real.logb 2 M`. -/
theorem complexity_le_of_multiplicativeComplexity_le {ε : ℝ} (hε : 0 < ε) :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ {n M : ℕ}, M₀ ≤ M →
      ∀ (f : BooleanFunction n),
        multiplicativeComplexity (single f) ≤ M →
        (complexity interpretation (single f) : ℝ) ≤
          (1 / 2 + ε) * (M : ℝ) * (M + 2 * n : ℝ) / Real.logb 2 M := by
  obtain ⟨M₀, hM₀, hsynth⟩ := exists_circuit_of_andCost_le hε
  refine ⟨M₀, hM₀, fun {n M} hMM₀ f hmc => ?_⟩
  obtain ⟨c, hc, hcost⟩ := multiplicativeComplexity_le_iff.mp hmc
  obtain ⟨c', hc', -, hsize⟩ := hsynth hMM₀ c hc hcost
  exact (Nat.cast_le.mpr (complexity_le_of_computes c' hc')).trans hsize

end Boolean.Zhegalkin

end Cslib.Circuits
