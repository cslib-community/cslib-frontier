/-
Copyright (c) 2026 Vincent Palma, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Palma, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Algebraic.Boolean

import CslibFrontier.Foundations.Data.MvPolynomial.CoefficientDegree

/-!
# Algebraic functional pigeonhole principle (`algFPHP`)

This module defines the algebraic functional pigeonhole principle `algFPHP m n R` for `m` pigeons
and `n` holes over a commutative ring `R`, following [ImpagliazzoPudlakSgall1999].

The variables are indexed by `Fin m × Fin n`, where `x_{ij} = 1` indicates that pigeon `i`
occupies hole `j`. The system consists of:
- pigeon axioms `algFPHPPigeonPoly i := 1 - ∑ j, X (i, j)` for each pigeon `i : Fin m`;
- functionality axioms `X (i, j) * X (i, j')` for each pigeon `i` and holes `j < j'`;
- hole (injectivity) axioms `X (i, j) * X (i', j)` for each hole `j` and pigeons `i < i'`;
- Boolean axioms `boolAxiom (i, j) := X (i, j) ^ 2 - X (i, j)`.

## Main definitions

- `Cslib.Logic.PL.Algebraic.algFPHP`: the full `algFPHP(m, n)` polynomial system over `R`.
- `Cslib.Logic.PL.Algebraic.algFPHPConstraints`: the non-Boolean constraints (pigeon, functionality,
  and hole axioms), so `algFPHP m n R = algFPHPConstraints m n R ++ boolAxioms (Fin m × Fin n) R`.
- `Cslib.Logic.PL.Algebraic.pigeonIndicator`: the Boolean indicator assignment of a map
  `Fin m → Fin n`.
- `Cslib.Logic.PL.Algebraic.boolSolutionEquivEmbedding`: equivalence between Boolean solutions of
  `algFPHP m n R` (over any nontrivial commutative ring) and embeddings `Fin m ↪ Fin n`.
- `Cslib.Logic.PL.Algebraic.commonZeroEquivEmbedding`: equivalence between arbitrary common zeros of
  `algFPHP m n R` (over any integral domain) and embeddings `Fin m ↪ Fin n`.

## Main results

- `Cslib.Logic.PL.Algebraic.exists_isBoolSolution_algFPHP_iff` and
  `Cslib.Logic.PL.Algebraic.exists_commonZero_algFPHP_iff`: satisfiability holds iff `m ≤ n`.
- `Cslib.Logic.PL.Algebraic.pc_refutableInDegree_algFPHP_zero`: when `n = 0 < m`, `1` is already
  a pigeon axiom, yielding an explicit degree-`0` Polynomial Calculus refutation.
- `Cslib.Logic.PL.Algebraic.exists_pc_refutableInDegree_algFPHP_iff`: over any field, `algFPHP m n`
  is refutable in Polynomial Calculus iff `n < m`.

## References

* [R. Impagliazzo, P. Pudlák, and J. Sgall, *Lower Bounds for the Polynomial Calculus and the
  Gröbner Basis Algorithm*][ImpagliazzoPudlakSgall1999]
-/

public section

namespace Cslib.Logic.PL.Algebraic

open MvPolynomial

/-! ### Encoding definitions -/

private def orderedPairs (k : ℕ) : List (Fin k × Fin k) :=
  (List.finRange k).flatMap fun a =>
    ((List.finRange k).filter (a < ·)).map (a, ·)

private theorem mem_orderedPairs {k : ℕ} {p : Fin k × Fin k} :
    p ∈ orderedPairs k ↔ p.1 < p.2 := by
  simp only [orderedPairs, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, decide_eq_true_eq]
  exact ⟨fun ⟨_, _, hab, hp⟩ => hp ▸ hab, fun h => ⟨p.1, p.2, h, Prod.eta p⟩⟩

/-- The algebraic pigeon axiom `1 - ∑ j, X (i, j)` asserting that pigeon `i` occupies at least one
hole (when combined with functionality axioms and Boolean variables). -/
@[expose] noncomputable def algFPHPPigeonPoly {m n : ℕ} {R : Type*} [CommRing R] (i : Fin m) :
    MvPolynomial (Fin m × Fin n) R :=
  1 - ∑ j : Fin n, X (i, j)

/-- The list of pigeon axioms for `algFPHP m n R`. -/
noncomputable def algFPHPPigeons (m n : ℕ) (R : Type*) [CommRing R] :
    List (MvPolynomial (Fin m × Fin n) R) :=
  (List.finRange m).map algFPHPPigeonPoly

/-- The list of functionality axioms `X (i, j) * X (i, j')` (`j < j'`) for `algFPHP m n R`. -/
noncomputable def algFPHPFunc (m n : ℕ) (R : Type*) [CommRing R] :
    List (MvPolynomial (Fin m × Fin n) R) :=
  (List.finRange m).flatMap fun i =>
    (orderedPairs n).map fun p => X (i, p.1) * X (i, p.2)

/-- The list of hole (injectivity) axioms `X (i, j) * X (i', j)` (`i < i'`) for `algFPHP m n R`. -/
noncomputable def algFPHPHole (m n : ℕ) (R : Type*) [CommRing R] :
    List (MvPolynomial (Fin m × Fin n) R) :=
  (List.finRange n).flatMap fun j =>
    (orderedPairs m).map fun p => X (p.1, j) * X (p.2, j)

/-- The non-Boolean constraints of `algFPHP m n R`: pigeon, functionality, and hole axioms. -/
noncomputable def algFPHPConstraints (m n : ℕ) (R : Type*) [CommRing R] :
    List (MvPolynomial (Fin m × Fin n) R) :=
  algFPHPPigeons m n R ++ algFPHPFunc m n R ++ algFPHPHole m n R

/-- The algebraic functional pigeonhole system `algFPHP(m, n)` over `R`, consisting of the pigeon,
functionality, hole, and Boolean axioms. -/
noncomputable def algFPHP (m n : ℕ) (R : Type*) [CommRing R] :
    List (MvPolynomial (Fin m × Fin n) R) :=
  algFPHPConstraints m n R ++ boolAxioms (Fin m × Fin n) R

/-- The Boolean assignment encoding `f : Fin m → Fin n`, mapping `(i, j)` to `true` iff
`j = f i`. -/
@[expose] def pigeonIndicator {m n : ℕ} (f : Fin m → Fin n) : Fin m × Fin n → Bool :=
  fun p => decide (p.2 = f p.1)

/-! ### Membership and structural properties -/

section Membership

variable {m n : ℕ} {R : Type*} [CommRing R]

/-- `algFPHPConstraints` decomposes as pigeon, functionality, and hole axioms. -/
theorem algFPHPConstraints_eq :
    algFPHPConstraints m n R = algFPHPPigeons m n R ++ algFPHPFunc m n R ++ algFPHPHole m n R := by
  rfl

/-- `algFPHP` is `algFPHPConstraints` followed by `boolAxioms`. -/
theorem algFPHP_eq_append_boolAxioms :
    algFPHP m n R = algFPHPConstraints m n R ++ boolAxioms (Fin m × Fin n) R := by
  rfl

/-- Membership characterization for `algFPHPPigeons`. -/
theorem mem_algFPHPPigeons {p : MvPolynomial (Fin m × Fin n) R} :
    p ∈ algFPHPPigeons m n R ↔ ∃ i : Fin m, algFPHPPigeonPoly i = p := by
  simp [algFPHPPigeons]

/-- Membership characterization for `algFPHPFunc`. -/
theorem mem_algFPHPFunc {p : MvPolynomial (Fin m × Fin n) R} :
    p ∈ algFPHPFunc m n R ↔
      ∃ i : Fin m, ∃ j j' : Fin n, j < j' ∧ X (i, j) * X (i, j') = p := by
  simp only [algFPHPFunc, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map,
    mem_orderedPairs]
  exact ⟨fun ⟨i, q, hq, hp⟩ => ⟨i, q.1, q.2, hq, hp⟩,
    fun ⟨i, j, j', hjj', hp⟩ => ⟨i, (j, j'), hjj', hp⟩⟩

/-- Membership characterization for `algFPHPHole`. -/
theorem mem_algFPHPHole {p : MvPolynomial (Fin m × Fin n) R} :
    p ∈ algFPHPHole m n R ↔
      ∃ i i' : Fin m, ∃ j : Fin n, i < i' ∧ X (i, j) * X (i', j) = p := by
  simp only [algFPHPHole, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map,
    mem_orderedPairs]
  exact ⟨fun ⟨j, q, hq, hp⟩ => ⟨q.1, q.2, j, hq, hp⟩,
    fun ⟨i, i', j, hii', hp⟩ => ⟨j, (i, i'), hii', hp⟩⟩

/-- Every pigeon axiom lies in `algFPHP m n R`. -/
theorem algFPHPPigeonPoly_mem_algFPHP (i : Fin m) :
    (algFPHPPigeonPoly i : MvPolynomial (Fin m × Fin n) R) ∈ algFPHP m n R := by
  simp [algFPHP, algFPHPConstraints, mem_algFPHPPigeons]

/-- Every functionality axiom `X (i, j) * X (i, j')` (`j ≠ j'`) lies in `algFPHP m n R`. -/
theorem algFPHPFunc_mem_algFPHP (i : Fin m) {j j' : Fin n} (h : j ≠ j') :
    (X (i, j) * X (i, j') : MvPolynomial (Fin m × Fin n) R) ∈ algFPHP m n R := by
  simp only [algFPHP, algFPHPConstraints, List.mem_append, mem_algFPHPFunc]
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact Or.inl (Or.inl (Or.inr ⟨i, j, j', hlt, rfl⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨i, j', j, hlt, mul_comm _ _⟩))

/-- Every hole axiom `X (i, j) * X (i', j)` (`i ≠ i'`) lies in `algFPHP m n R`. -/
theorem algFPHPHole_mem_algFPHP {i i' : Fin m} (h : i ≠ i') (j : Fin n) :
    (X (i, j) * X (i', j) : MvPolynomial (Fin m × Fin n) R) ∈ algFPHP m n R := by
  simp only [algFPHP, algFPHPConstraints, List.mem_append, mem_algFPHPHole]
  rcases lt_or_gt_of_ne h with hlt | hlt
  · exact Or.inl (Or.inr ⟨i, i', j, hlt, rfl⟩)
  · exact Or.inl (Or.inr ⟨i', i, j, hlt, mul_comm _ _⟩)

/-- Every Boolean axiom lies in `algFPHP m n R`. -/
theorem boolAxiom_mem_algFPHP (v : Fin m × Fin n) :
    (boolAxiom v : MvPolynomial (Fin m × Fin n) R) ∈ algFPHP m n R :=
  List.mem_append_right _ (boolAxiom_mem_boolAxioms v)

/-- Membership characterization for `algFPHPConstraints`. -/
theorem mem_algFPHPConstraints {p : MvPolynomial (Fin m × Fin n) R} :
    p ∈ algFPHPConstraints m n R ↔
      (∃ i : Fin m, algFPHPPigeonPoly i = p) ∨
      (∃ i : Fin m, ∃ j j' : Fin n, j < j' ∧ X (i, j) * X (i, j') = p) ∨
      (∃ i i' : Fin m, ∃ j : Fin n, i < i' ∧ X (i, j) * X (i', j) = p) := by
  simp only [algFPHPConstraints, List.mem_append, mem_algFPHPPigeons, mem_algFPHPFunc,
    mem_algFPHPHole, or_assoc]

/-- Membership characterization for `algFPHP`. -/
theorem mem_algFPHP {p : MvPolynomial (Fin m × Fin n) R} :
    p ∈ algFPHP m n R ↔
      p ∈ algFPHPConstraints m n R ∨ ∃ v : Fin m × Fin n, boolAxiom v = p := by
  simp only [algFPHP, List.mem_append, mem_boolAxioms]

private theorem totalDegree_X_mul_X_le {σ : Type*} (u v : σ) :
    (X u * X v : MvPolynomial σ R).totalDegree ≤ 2 :=
  (totalDegree_mul _ _).trans
    (add_le_add (MvPolynomial.totalDegree_X_le u) (MvPolynomial.totalDegree_X_le v))

/-- Every pigeon axiom has total degree at most `1`. -/
theorem totalDegree_algFPHPPigeonPoly_le (i : Fin m) :
    (algFPHPPigeonPoly i : MvPolynomial (Fin m × Fin n) R).totalDegree ≤ 1 :=
  (totalDegree_sub _ _).trans <|
    max_le (by simp) (totalDegree_finsetSum_le fun j _ => MvPolynomial.totalDegree_X_le (i, j))

/-- Every constraint of `algFPHPConstraints m n R` has total degree at most `2`. -/
theorem totalDegree_le_two_of_mem_algFPHPConstraints {p : MvPolynomial (Fin m × Fin n) R}
    (hp : p ∈ algFPHPConstraints m n R) : p.totalDegree ≤ 2 := by
  rcases mem_algFPHPConstraints.1 hp with ⟨i, rfl⟩ | ⟨i, j, j', _, rfl⟩ | ⟨i, i', j, _, rfl⟩
  · exact (totalDegree_algFPHPPigeonPoly_le i).trans (by decide)
  · exact totalDegree_X_mul_X_le (i, j) (i, j')
  · exact totalDegree_X_mul_X_le (i, j) (i', j)

/-- Every axiom of `algFPHP m n R` has total degree at most `2`. -/
theorem totalDegree_le_two_of_mem_algFPHP {p : MvPolynomial (Fin m × Fin n) R}
    (hp : p ∈ algFPHP m n R) : p.totalDegree ≤ 2 := by
  rcases mem_algFPHP.1 hp with h | ⟨v, rfl⟩
  · exact totalDegree_le_two_of_mem_algFPHPConstraints h
  · exact totalDegree_boolAxiom_le v

/-- With no holes (`n = 0`), every pigeon axiom equals `1`. -/
theorem algFPHPPigeonPoly_zero (i : Fin m) :
    (algFPHPPigeonPoly (n := 0) (R := R) i) = 1 := by
  simp [algFPHPPigeonPoly]

/-- When `n = 0 < m`, `1` is directly an axiom of `algFPHP m 0 R`. -/
theorem one_mem_algFPHP_zero (hm : 0 < m) :
    (1 : MvPolynomial (Fin m × Fin 0) R) ∈ algFPHP m 0 R :=
  algFPHPPigeonPoly_zero (R := R) ⟨0, hm⟩ ▸ algFPHPPigeonPoly_mem_algFPHP ⟨0, hm⟩

end Membership

/-! ### Assignment semantics and common zeros -/

section Semantics

private theorem bitPoint_pigeonIndicator {m n : ℕ} (R : Type*) [CommRing R]
    (f : Fin m → Fin n) (i : Fin m) (j : Fin n) :
    Cslib.BitString.bitPoint (pigeonIndicator f) (i, j) = if j = f i then (1 : R) else 0 := by
  simp only [Cslib.BitString.bitPoint, pigeonIndicator, Cslib.BitString.bitVal]
  by_cases h : j = f i <;> simp [h]

private theorem bitPoint_pigeonIndicator_of_ne {m n : ℕ} (R : Type*) [CommRing R]
    {f : Fin m → Fin n} {i : Fin m} {j : Fin n} (h : j ≠ f i) :
    Cslib.BitString.bitPoint (pigeonIndicator f) (i, j) = (0 : R) := by
  simp only [bitPoint_pigeonIndicator, h, ↓reduceIte]

private theorem pigeonIndicator_eval_eq_zero {m n : ℕ} {R : Type*} [CommRing R]
    {f : Fin m → Fin n} (hf : Function.Injective f) {p : MvPolynomial (Fin m × Fin n) R}
    (hp : p ∈ algFPHP m n R) :
    eval (Cslib.BitString.bitPoint (pigeonIndicator f)) p = 0 := by
  rcases mem_algFPHP.1 hp with h | ⟨v, rfl⟩
  · rcases mem_algFPHPConstraints.1 h with ⟨i, rfl⟩ | ⟨i, j, j', hjj', rfl⟩ |
        ⟨i, i', j, hii', rfl⟩
    · simp [algFPHPPigeonPoly, bitPoint_pigeonIndicator, Finset.sum_ite_eq']
    · simp only [map_mul, eval_X]
      by_cases hj : j = f i
      · rw [bitPoint_pigeonIndicator_of_ne R (fun e => hjj'.ne (hj.trans e.symm)), mul_zero]
      · rw [bitPoint_pigeonIndicator_of_ne R hj, zero_mul]
    · simp only [map_mul, eval_X]
      by_cases hi : j = f i
      · rw [bitPoint_pigeonIndicator_of_ne R (fun e => hii'.ne (hf (hi.symm.trans e))), mul_zero]
      · rw [bitPoint_pigeonIndicator_of_ne R hi, zero_mul]
  · exact eval_boolAxiom _ v

private theorem exists_injective_eq_bitPoint {m n : ℕ} {R : Type*} [CommRing R] [Nontrivial R]
    {a : Fin m × Fin n → R} (ha_bin : ∀ v, a v = 0 ∨ a v = 1)
    (ha_c : ∀ p ∈ algFPHPConstraints m n R, eval a p = 0) :
    ∃ f : Fin m → Fin n, Function.Injective f ∧
      a = Cslib.BitString.bitPoint (pigeonIndicator f) := by
  have hfunc (i : Fin m) {j j' : Fin n} (hne : j ≠ j') (h1 : a (i, j) = 1) : a (i, j') = 0 := by
    have hmul : a (i, j) * a (i, j') = 0 := by
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · simpa using ha_c _ (mem_algFPHPConstraints.2 (Or.inr (Or.inl ⟨i, j, j', hlt, rfl⟩)))
      · simpa [mul_comm] using
          ha_c _ (mem_algFPHPConstraints.2 (Or.inr (Or.inl ⟨i, j', j, hlt, rfl⟩)))
    simpa [h1] using hmul
  have hex (i : Fin m) : ∃ j : Fin n, a (i, j) = 1 := by
    by_contra! hnone
    have hp := ha_c (algFPHPPigeonPoly i) (mem_algFPHPConstraints.2 (Or.inl ⟨i, rfl⟩))
    simp only [algFPHPPigeonPoly, map_sub, map_one, map_sum, eval_X,
      fun j => (ha_bin (i, j)).resolve_right (hnone j), Finset.sum_const_zero, sub_zero] at hp
    exact one_ne_zero hp
  choose f hf1 using hex
  refine ⟨f, fun i i' hii' => by_contra fun hne => ?_, funext fun ⟨i, j⟩ => ?_⟩
  · have hmul : a (i, f i) * a (i', f i) = 0 := by
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · simpa using ha_c _ (mem_algFPHPConstraints.2 (Or.inr (Or.inr ⟨i, i', f i, hlt, rfl⟩)))
      · simpa [mul_comm] using
          ha_c _ (mem_algFPHPConstraints.2 (Or.inr (Or.inr ⟨i', i, f i, hlt, rfl⟩)))
    rw [hf1 i, hii', hf1 i', one_mul] at hmul
    exact one_ne_zero hmul
  · rw [bitPoint_pigeonIndicator]
    split_ifs with h
    · exact h ▸ hf1 i
    · exact hfunc i (Ne.symm h) (hf1 i)

private theorem pigeonIndicator_eq_of_bitPoint_eq {m n : ℕ} {R : Type*} [CommRing R] [Nontrivial R]
    {f g : Fin m → Fin n}
    (h : Cslib.BitString.bitPoint (pigeonIndicator f) =
      (Cslib.BitString.bitPoint (pigeonIndicator g) : Fin m × Fin n → R)) :
    f = g := by
  funext i
  have hfi := congrFun h (i, f i)
  by_cases hfg : f i = g i
  · exact hfg
  · simp [Cslib.BitString.bitPoint, pigeonIndicator, hfg] at hfi

private theorem pigeonIndicator_injective {m n : ℕ} :
    Function.Injective (pigeonIndicator : (Fin m → Fin n) → Fin m × Fin n → Bool) := by
  intro f g h
  funext i
  have hfi := congrFun h (i, f i)
  simp only [pigeonIndicator, decide_true] at hfi
  exact of_decide_eq_true hfi.symm

/-- Rewriting `IsBoolSolution` on `algFPHP` in terms of `algFPHPConstraints`. -/
theorem isBoolSolution_algFPHP_iff_constraints {m n : ℕ} {R : Type*} [CommRing R]
    (x : Fin m × Fin n → Bool) :
    IsBoolSolution (algFPHP m n R) x ↔ IsBoolSolution (algFPHPConstraints m n R) x :=
  isBoolSolution_append_boolAxioms (algFPHPConstraints m n R) x

/-- Over any commutative ring, an injective map `f : Fin m → Fin n` yields a Boolean solution of
`algFPHP m n R`. -/
theorem isBoolSolution_algFPHP_pigeonIndicator {m n : ℕ} {R : Type*} [CommRing R]
    {f : Fin m → Fin n} (hf : Function.Injective f) :
    IsBoolSolution (algFPHP m n R) (pigeonIndicator f) :=
  fun _ hp => pigeonIndicator_eval_eq_zero hf hp

/-- Over any nontrivial commutative ring, `pigeonIndicator f` is a Boolean solution of
`algFPHP m n R` iff `f` is injective. -/
theorem isBoolSolution_algFPHP_pigeonIndicator_iff {m n : ℕ} {R : Type*} [CommRing R] [Nontrivial R]
    (f : Fin m → Fin n) :
    IsBoolSolution (algFPHP m n R) (pigeonIndicator f) ↔ Function.Injective f := by
  refine ⟨fun h => ?_, isBoolSolution_algFPHP_pigeonIndicator⟩
  intro i i' hii'
  by_contra hne
  have hp := h (X (i, f i) * X (i', f i)) (algFPHPHole_mem_algFPHP hne (f i))
  simp only [map_mul, eval_X, Cslib.BitString.bitPoint, pigeonIndicator, decide_true,
    Cslib.BitString.bitVal_true, hii', one_mul] at hp
  exact one_ne_zero hp

/-- Over any nontrivial commutative ring, a Boolean assignment satisfies `algFPHP m n R` iff it is
`pigeonIndicator f` for some injective `f : Fin m → Fin n`. -/
theorem isBoolSolution_algFPHP_iff {m n : ℕ} {R : Type*} [CommRing R] [Nontrivial R]
    (x : Fin m × Fin n → Bool) :
    IsBoolSolution (algFPHP m n R) x ↔
      ∃ f : Fin m → Fin n, Function.Injective f ∧ x = pigeonIndicator f := by
  refine ⟨fun hx => ?_, fun ⟨_, hf, hx⟩ => hx ▸ isBoolSolution_algFPHP_pigeonIndicator hf⟩
  rcases exists_injective_eq_bitPoint
      (fun v => by cases hxv : x v <;> simp [Cslib.BitString.bitPoint, hxv])
      (fun p hp => hx p (mem_algFPHP.2 (Or.inl hp))) with ⟨f, hf, hpt⟩
  refine ⟨f, hf, funext fun v => ?_⟩
  have hv := congrFun hpt v
  cases hxv : x v <;> cases hfv : pigeonIndicator f v <;> simp_all [Cslib.BitString.bitPoint]

/-- Equivalence between Boolean solutions of `algFPHP m n R` and embeddings `Fin m ↪ Fin n`,
over any nontrivial commutative ring `R`. -/
noncomputable def boolSolutionEquivEmbedding (m n : ℕ) (R : Type*) [CommRing R] [Nontrivial R] :
    {x : Fin m × Fin n → Bool // IsBoolSolution (algFPHP m n R) x} ≃ (Fin m ↪ Fin n) where
  toFun s :=
    let hex := (isBoolSolution_algFPHP_iff s.val).1 s.property
    ⟨Classical.choose hex, (Classical.choose_spec hex).1⟩
  invFun e := ⟨pigeonIndicator e, isBoolSolution_algFPHP_pigeonIndicator e.injective⟩
  left_inv := by
    rintro ⟨x, hx⟩
    ext v
    have hspec := (isBoolSolution_algFPHP_iff (R := R) x).1 hx
    exact congrFun (Classical.choose_spec hspec).2.symm v
  right_inv e := by
    refine DFunLike.ext _ _ fun i => ?_
    have hspec := Classical.choose_spec
      ((isBoolSolution_algFPHP_iff (R := R) (pigeonIndicator e)).1
        (isBoolSolution_algFPHP_pigeonIndicator e.injective))
    exact congrFun (pigeonIndicator_injective hspec.2.symm) i

/-- The embedding assigned by `boolSolutionEquivEmbedding` represents the Boolean solution. -/
theorem pigeonIndicator_boolSolutionEquivEmbedding {m n : ℕ} {R : Type*} [CommRing R] [Nontrivial R]
    (s : {x : Fin m × Fin n → Bool // IsBoolSolution (algFPHP m n R) x}) :
    pigeonIndicator (boolSolutionEquivEmbedding m n R s) = s.val :=
  (Classical.choose_spec ((isBoolSolution_algFPHP_iff (R := R) s.val).1 s.property)).2.symm

/-- `boolSolutionEquivEmbedding`'s inverse sends an embedding `e` to `pigeonIndicator e`. -/
theorem boolSolutionEquivEmbedding_symm_val {m n : ℕ} {R : Type*} [CommRing R] [Nontrivial R]
    (e : Fin m ↪ Fin n) :
    Subtype.val ((boolSolutionEquivEmbedding m n R).symm e) = pigeonIndicator e := by
  rfl

/-- `algFPHP m n R` has a Boolean solution iff `m ≤ n`, over any nontrivial commutative ring. -/
theorem exists_isBoolSolution_algFPHP_iff {m n : ℕ} {R : Type*} [CommRing R] [Nontrivial R] :
    (∃ x : Fin m × Fin n → Bool, IsBoolSolution (algFPHP m n R) x) ↔ m ≤ n := by
  refine ⟨fun ⟨x, hx⟩ => ?_, fun hmn =>
    ⟨pigeonIndicator (Fin.castLE hmn),
      isBoolSolution_algFPHP_pigeonIndicator (Fin.castLE_injective hmn)⟩⟩
  rcases (isBoolSolution_algFPHP_iff (R := R) x).1 hx with ⟨f, hf, _⟩
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

/-- Over any integral domain, an arbitrary assignment `a : Fin m × Fin n → R` is a common zero of
`algFPHP m n R` iff it equals `bitPoint (pigeonIndicator f)` for some injective `f : Fin m → Fin n`.
-/
theorem eval_algFPHP_eq_zero_iff {m n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (a : Fin m × Fin n → R) :
    (∀ p ∈ algFPHP m n R, eval a p = 0) ↔
      ∃ f : Fin m → Fin n, Function.Injective f ∧
        a = Cslib.BitString.bitPoint (pigeonIndicator f) := by
  refine ⟨fun ha => exists_injective_eq_bitPoint (fun v => ?_)
      (fun p hp => ha p (mem_algFPHP.2 (Or.inl hp))),
    fun ⟨_, hf, ha⟩ _ hp => ha ▸ pigeonIndicator_eval_eq_zero hf hp⟩
  have hv := ha (boolAxiom v) (boolAxiom_mem_algFPHP v)
  simp only [boolAxiom, map_sub, map_pow, eval_X] at hv
  have hmul : a v * (a v - 1) = 0 :=
    calc a v * (a v - 1) = a v ^ 2 - a v := by ring
      _ = 0 := hv
  exact (mul_eq_zero.1 hmul).imp_right sub_eq_zero.1

/-- Equivalence between arbitrary common zeros of `algFPHP m n R` and embeddings `Fin m ↪ Fin n`,
over any integral domain `R`. -/
noncomputable def commonZeroEquivEmbedding (m n : ℕ) (R : Type*) [CommRing R] [IsDomain R] :
    {a : Fin m × Fin n → R // ∀ p ∈ algFPHP m n R, eval a p = 0} ≃ (Fin m ↪ Fin n) where
  toFun s :=
    let hex := (eval_algFPHP_eq_zero_iff s.val).1 s.property
    ⟨Classical.choose hex, (Classical.choose_spec hex).1⟩
  invFun e :=
    ⟨Cslib.BitString.bitPoint (pigeonIndicator e),
      fun _ hp => pigeonIndicator_eval_eq_zero e.injective hp⟩
  left_inv := by
    rintro ⟨a, ha⟩
    ext v
    have hspec := (eval_algFPHP_eq_zero_iff a).1 ha
    exact congrFun (Classical.choose_spec hspec).2.symm v
  right_inv e := by
    refine DFunLike.ext _ _ fun i => ?_
    have hspec := Classical.choose_spec
      ((eval_algFPHP_eq_zero_iff (Cslib.BitString.bitPoint (pigeonIndicator e) :
        Fin m × Fin n → R)).1 (fun _ hp => pigeonIndicator_eval_eq_zero e.injective hp))
    exact congrFun (pigeonIndicator_eq_of_bitPoint_eq (R := R) hspec.2.symm) i

/-- The embedding assigned by `commonZeroEquivEmbedding` represents the common zero. -/
theorem bitPoint_commonZeroEquivEmbedding {m n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (s : {a : Fin m × Fin n → R // ∀ p ∈ algFPHP m n R, eval a p = 0}) :
    Cslib.BitString.bitPoint (pigeonIndicator (commonZeroEquivEmbedding m n R s)) = s.val :=
  (Classical.choose_spec ((eval_algFPHP_eq_zero_iff (R := R) s.val).1 s.property)).2.symm

/-- `commonZeroEquivEmbedding`'s inverse sends an embedding `e` to its `0`/`1` indicator. -/
theorem commonZeroEquivEmbedding_symm_val {m n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (e : Fin m ↪ Fin n) :
    Subtype.val ((commonZeroEquivEmbedding m n R).symm e) =
      Cslib.BitString.bitPoint (pigeonIndicator e) := by
  rfl

/-- `algFPHP m n R` has a common zero in an integral domain `R` iff `m ≤ n`. -/
theorem exists_commonZero_algFPHP_iff {m n : ℕ} {R : Type*} [CommRing R] [IsDomain R] :
    (∃ a : Fin m × Fin n → R, ∀ p ∈ algFPHP m n R, eval a p = 0) ↔ m ≤ n := by
  refine ⟨fun ⟨a, ha⟩ => ?_, fun hmn =>
    ⟨Cslib.BitString.bitPoint (pigeonIndicator (Fin.castLE hmn)),
      fun _ hp => pigeonIndicator_eval_eq_zero (Fin.castLE_injective hmn) hp⟩⟩
  rcases (eval_algFPHP_eq_zero_iff (R := R) a).1 ha with ⟨f, hf, _⟩
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

end Semantics

/-! ### Polynomial Calculus refutability -/

section PC

/-- For `n = 0 < m`, `algFPHP m 0 R` has an explicit degree-`0` Polynomial Calculus refutation
because pigeon `0`'s axiom is `1`. -/
theorem pc_refutableInDegree_algFPHP_zero {m : ℕ} (hm : 0 < m) (R : Type*) [CommRing R] :
    PC.RefutableInDegree (algFPHP m 0 R) 0 :=
  ⟨[1], PC.IsProof.mem PC.IsProof.nil (one_mem_algFPHP_zero hm), by simp,
    by simp [PC.degree_cons, PC.degree_nil]⟩

/-- Soundness: when `m ≤ n`, `algFPHP m n R` has no Polynomial Calculus refutation of any degree
over any nontrivial commutative ring `R`. -/
theorem not_pc_refutableInDegree_algFPHP {m n : ℕ} {R : Type*} [CommRing R] [Nontrivial R]
    (h : m ≤ n) (d : ℕ) : ¬ PC.RefutableInDegree (algFPHP m n R) d := fun href => by
  rcases (exists_isBoolSolution_algFPHP_iff (R := R)).2 h with ⟨x, hx⟩
  rw [algFPHP_eq_append_boolAxioms] at href
  exact href.not_isBoolSolution x ((isBoolSolution_algFPHP_iff_constraints x).1 hx)

/-- Completeness over fields: when `n < m`, `algFPHP m n K` has a Polynomial Calculus refutation
of degree at most `m * n + 2`. -/
theorem pc_refutableInDegree_algFPHP_of_lt {m n : ℕ} {K : Type*} [Field K] (h : n < m) :
    PC.RefutableInDegree (algFPHP m n K) (m * n + 2) := by
  have hcard : m * n + 2 = Fintype.card (Fin m × Fin n) + 2 := by simp
  rw [algFPHP_eq_append_boolAxioms, hcard]
  exact (PC.refutableInDegree_iff (D := 2)
    fun _ hf => totalDegree_le_two_of_mem_algFPHPConstraints hf).2 fun x hx =>
      h.not_ge (exists_isBoolSolution_algFPHP_iff.1
        ⟨x, (isBoolSolution_algFPHP_iff_constraints x).2 hx⟩)

/-- Over any field, `algFPHP m n K` is refutable in Polynomial Calculus iff `n < m`. -/
theorem exists_pc_refutableInDegree_algFPHP_iff {m n : ℕ} {K : Type*} [Field K] :
    (∃ d, PC.RefutableInDegree (algFPHP m n K) d) ↔ n < m :=
  ⟨fun ⟨d, hd⟩ => lt_of_not_ge fun h => not_pc_refutableInDegree_algFPHP (R := K) h d hd,
   fun h => ⟨m * n + 2, pc_refutableInDegree_algFPHP_of_lt h⟩⟩

end PC

end Cslib.Logic.PL.Algebraic
