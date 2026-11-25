/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Finsupp.OddSupport
public import CslibFrontier.Logics.Propositional.Algebraic.SumOfSquares.Basic
public import CslibFrontier.Logics.Propositional.ParitySystem
public import Mathlib.Algebra.Order.Ring.Defs
import CslibFrontier.Foundations.BooleanAnalysis.Fourier
import CslibFrontier.Foundations.Data.BitString.Sign
import CslibFrontier.Foundations.Data.Finset.SymmDiff
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Sum-of-squares degree lower bounds for parity systems

Over `±1` variables the parity equation `⊕_{i ∈ S} xᵢ = b` reads `∏_{i ∈ S} xᵢ = (-1) ^ b`. The
**`±1` encoding** `ParitySystem.toPolys R P` of a parity system `P` has, for every equation, the
polynomial `∏_{i ∈ S} Xᵢ - (-1) ^ b` (`ParitySystem.parityPoly`), and for every variable the
axiom `Xᵢ ^ 2 - 1`. Its common zeros in an ordered field are the `±1` points of the satisfying
assignments (`ParitySystem.exists_eval_eq_zero_iff`).

**Schoenebeck's lemma.** If width-`d` derivations from `P` do not reach `0 = 1`, the encoding has
a pseudo-expectation of degree `d` (`ParitySystem.pseudoExpectation`), so it has no sum-of-squares
refutation of degree at most `d` (`ParitySystem.not_sos_refutableInDegree_toPolys`). This is the
main lemma of [Schoenebeck, Lemma 13][Schoenebeck2008], in the sum-of-squares form of
[Barak and Steurer, lecture "Higher-degree integrality gaps", Lemma 7 and the proof of Theorem 2]
[BarakSteurer2016], for an arbitrary parity system: no expansion or randomness is assumed.
Schoenebeck states it for width-`w` resolution on XOR formulas and a round of the Lasserre
hierarchy proportional to `w`. In the author's copy consulted (TeX output dated December 2008,
p. 8) that round is `w/2`; versions of the paper differ on this constant, and the Lasserre vector
solution is not constructed here. Round `r` of [Schoenebeck, Definition 5][Schoenebeck2008] has a
vector for every `r`-junta, so it constrains moments of degree up to `2 r`; degree-`d`
sum-of-squares corresponds to roughly round `d/2`. Here degree `d` plays the role of `w`, and
width counts the variables of every line, axioms included
(`Cslib.Logic.PL.ParitySystem.Derives`), which makes the hypothesis weaker than the source's. The
construction is that of the sources:

* `Ẽ[∏_{i ∈ T} Xᵢ] = (-1) ^ c` if width-`d` derivations reach `⊕_{i ∈ T} xᵢ = c`, and `0`
  otherwise (`ParitySystem.parityValue`). Since `0 = 1` is not derivable, at most one `c` is
  derivable.
* A monomial `X ^ m` is reduced modulo `Xᵢ ^ 2 = 1` to the product over its odd support
  (`Finsupp.oddSupport`), and `Ẽ` is extended linearly.
* `Ẽ (q (∏_{i ∈ S} Xᵢ - (-1) ^ b)) = 0` when the product has degree at most `d`: the equation
  `⟨S, b⟩` and every monomial of `q` have total width at most `d`, and summing a derivable equation
  shifts `parityValue` by its sign (`ParitySystem.parityValue_symmDiff`).
* The moment matrix is positive semidefinite (`ParitySystem.sum_sum_mul_parityValue_nonneg`): on
  sets of size at most `d / 2`, "`A ∆ B` is derivable" is an equivalence relation, and
  `parityValue (A ∆ B)` factors as `τ A τ B` within a class and vanishes across classes, so the
  quadratic form is a sum of squares, one per class.

## Main definitions

* `Cslib.Logic.PL.ParitySystem.parityPoly`: the `±1` polynomial of a parity equation.
* `Cslib.Logic.PL.ParitySystem.toPolys`: the `±1` encoding of a parity system.
* `Cslib.Logic.PL.ParitySystem.parityValue`: Schoenebeck's pseudo-moments.
* `Cslib.Logic.PL.ParitySystem.pseudoExpectation`: Schoenebeck's pseudo-expectation.

## Main results

* `Cslib.Logic.PL.ParitySystem.exists_eval_eq_zero_iff`: the common zeros of the encoding are the
  satisfying assignments.
* `Cslib.Logic.PL.ParitySystem.sum_sum_mul_parityValue_nonneg`: positive semidefiniteness of the
  moment matrix.
* `Cslib.Logic.PL.ParitySystem.not_sos_refutableInDegree_toPolys`: **Schoenebeck's lemma**, if
  width-`d` derivations do not reach `0 = 1` there is no sum-of-squares refutation of degree at
  most `d`.

## References

* [G. Schoenebeck, *Linear level Lasserre lower bounds for certain k-CSPs*][Schoenebeck2008]
* [B. Barak, D. Steurer, *Proofs, beliefs, and algorithms through the lens of sum-of-squares*,
  lecture notes][BarakSteurer2016]
* [D. Grigoriev, *Linear lower bound on degrees of Positivstellensatz calculus proofs for the
  parity*][Grigoriev2001]
-/

public section

namespace Cslib.Logic.PL.ParitySystem

open MvPolynomial Finset
open Finsupp (single oddSupport oddSupport_zero oddSupport_add oddSupport_single_two
  oddSupport_sum_single card_oddSupport_le_degree)
open scoped symmDiff

variable {σ : Type*}

/-! ### The `±1` encoding -/

section Encoding

variable (R : Type*) [CommRing R]

/-- The `±1` polynomial `∏_{i ∈ S} Xᵢ - (-1) ^ b` of the parity equation `⊕_{i ∈ S} xᵢ = b`. -/
@[expose] noncomputable def parityPoly (S : Finset σ) (b : Bool) : MvPolynomial σ R :=
  ∏ i ∈ S, X i - C ((-1) ^ b.toNat)

/-- The **`±1` encoding** of a parity system: the polynomial of every equation, followed by the
axioms `Xᵢ ^ 2 - 1` for all variables. -/
noncomputable def toPolys [Fintype σ] (P : ParitySystem σ) : List (MvPolynomial σ R) :=
  P.map (fun e => parityPoly R e.vars e.rhs) ++ univ.toList.map fun i => X i ^ 2 - 1

variable {R}

/-- The members of the `±1` encoding. -/
theorem mem_toPolys [Fintype σ] {P : ParitySystem σ} {f : MvPolynomial σ R} :
    f ∈ P.toPolys R ↔ (∃ e ∈ P, parityPoly R e.vars e.rhs = f) ∨ ∃ i, X i ^ 2 - 1 = f := by
  simp [toPolys]

/-- The polynomial of an equation of `P` belongs to the encoding. -/
theorem parityPoly_mem_toPolys [Fintype σ] {P : ParitySystem σ} {S : Finset σ} {b : Bool}
    (h : ⟨S, b⟩ ∈ P) : parityPoly R S b ∈ P.toPolys R :=
  mem_toPolys.2 (.inl ⟨_, h, rfl⟩)

/-- The axiom `Xᵢ ^ 2 - 1` belongs to the encoding. -/
theorem X_sq_sub_one_mem_toPolys [Fintype σ] (P : ParitySystem σ) (i : σ) :
    (X i ^ 2 - 1 : MvPolynomial σ R) ∈ P.toPolys R :=
  mem_toPolys.2 (.inr ⟨i, rfl⟩)

private theorem prod_X_eq_monomial (S : Finset σ) :
    (∏ i ∈ S, X i : MvPolynomial σ R) = monomial (∑ i ∈ S, single i 1) 1 := by
  rw [monomial_sum_one]; rfl

/-- The polynomial of an equation with `k` variables has total degree at most `k`. -/
theorem totalDegree_parityPoly_le (S : Finset σ) (b : Bool) :
    (parityPoly R S b).totalDegree ≤ #S := by
  refine (totalDegree_sub _ _).trans (max_le ?_ (by rw [totalDegree_C]; exact Nat.zero_le _))
  refine (totalDegree_finsetProd _ _).trans ?_
  rw [card_eq_sum_ones]
  exact sum_le_sum fun i _ => (totalDegree_monomial_le (single i 1) (1 : R)).trans (by simp)

/-- Over a nontrivial ring, the polynomial of an equation with `k` variables has total degree
exactly `k`. -/
theorem totalDegree_parityPoly [Nontrivial R] (S : Finset σ) (b : Bool) :
    (parityPoly R S b).totalDegree = #S := by
  refine le_antisymm (totalDegree_parityPoly_le S b) ?_
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  classical
  have hdeg : (∑ i ∈ S, single i 1).degree = #S := by simp [map_sum]
  refine hdeg ▸ le_totalDegree (mem_support_iff.2 ?_)
  have hne : (0 : σ →₀ ℕ) ≠ ∑ i ∈ S, single i 1 :=
    fun h => hS.card_pos.ne (by simpa [← h] using hdeg)
  rw [parityPoly, prod_X_eq_monomial, coeff_sub, coeff_monomial, coeff_C, ite_eq_right hne]
  simp

end Encoding

/-- **The common zeros of the `±1` encoding are the satisfying assignments**: over a strictly
ordered field, the encoding of `P` has a common zero exactly when `P` is satisfiable. -/
theorem exists_eval_eq_zero_iff {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype σ] (P : ParitySystem σ) :
    (∃ x : σ → R, ∀ f ∈ P.toPolys R, eval x f = 0) ↔ ∃ a, P.Holds a := by
  have h1 : (1 : R) ≠ -1 := (neg_one_lt_zero.trans zero_lt_one).ne'
  have heval (a : σ → Bool) (S : Finset σ) (b : Bool) :
      eval (fun i => (-1 : R) ^ (a i).toNat) (parityPoly R S b) = 0 ↔ parityOn S a = b := by
    have hc := BitString.chi_eq_neg_one_pow_parityOn (R := R) S a
    rw [BitString.chi] at hc
    simp only [parityPoly, eval_sub, eval_prod, eval_C, eval_X, sub_eq_zero, hc]
    cases parityOn S a <;> cases b <;> simp [h1, h1.symm]
  refine ⟨fun ⟨x, hx⟩ => ?_, fun ⟨a, ha⟩ => ⟨fun i => (-1) ^ (a i).toNat, ?_⟩⟩
  · have hx' : x = fun i => (-1) ^ (decide (x i = -1)).toNat := funext fun i => by
      have h := sub_eq_zero.1 (by simpa using hx _ (X_sq_sub_one_mem_toPolys P i))
      rcases sq_eq_one_iff.1 h with hi | hi <;> simp [hi, h1]
    exact ⟨_, fun e he => (heval _ e.vars e.rhs).1 (hx' ▸ hx _ (parityPoly_mem_toPolys he))⟩
  · rintro f hf
    rcases mem_toPolys.1 hf with ⟨e, he, rfl⟩ | ⟨i, rfl⟩
    · exact (heval a e.vars e.rhs).2 (ha e he)
    · rw [eval_sub, eval_pow, eval_X, map_one, sub_eq_zero, ← pow_mul]
      cases a i <;> norm_num

/-! ### Schoenebeck's pseudo-moments -/

variable [DecidableEq σ]

open Classical in
/-- **Schoenebeck's pseudo-moments**: `parityValue P w T` is `1` if width-`w` derivations reach
`⊕_{i ∈ T} xᵢ = 0`, `-1` if they reach `⊕_{i ∈ T} xᵢ = 1` but not `⊕_{i ∈ T} xᵢ = 0`, and `0`
otherwise. -/
noncomputable def parityValue {R : Type*} [CommRing R] (P : ParitySystem σ) (w : ℕ)
    (T : Finset σ) : R :=
  if P.Derives w T false then 1 else if P.Derives w T true then -1 else 0

variable {P : ParitySystem σ} {w : ℕ}

/-- If `0 = 1` is not derivable, `parityValue` is the sign of the derivable right-hand side. -/
theorem parityValue_eq_of_derives {R : Type*} [CommRing R] (hP : ¬ P.Derives w ∅ true)
    {T : Finset σ} {c : Bool} (h : P.Derives w T c) :
    (parityValue P w T : R) = (-1) ^ c.toNat := by
  cases c with
  | false => simp [parityValue, h]
  | true =>
    have hf : ¬ P.Derives w T false := fun hf => hP (by simpa using hf.symmDiff h (by simp))
    simp [parityValue, hf, h]

/-- `parityValue` vanishes on sets of which no equation is derivable. -/
theorem parityValue_eq_zero {R : Type*} [CommRing R] {T : Finset σ}
    (h : ∀ c, ¬ P.Derives w T c) : (parityValue P w T : R) = 0 := by
  simp [parityValue, h]

/-- `parityValue P w ∅ = 1`. -/
@[simp] theorem parityValue_empty {R : Type*} [CommRing R] : (parityValue P w ∅ : R) = 1 := by
  simp [parityValue, Derives.empty]

/-- **The shift identity**: if `⊕_{i ∈ S} xᵢ = b` is derivable and `#T + #S ≤ w`, then
`parityValue (T ∆ S) = (-1) ^ b * parityValue T`. -/
theorem parityValue_symmDiff {R : Type*} [CommRing R] (hP : ¬ P.Derives w ∅ true)
    {S T : Finset σ} {b : Bool} (hS : P.Derives w S b) (hST : #T + #S ≤ w) :
    (parityValue P w (T ∆ S) : R) = (-1) ^ b.toNat * parityValue P w T := by
  have hw : #(T ∆ S) ≤ w := (card_symmDiff_le T S).trans hST
  by_cases hT : ∃ c, P.Derives w T c
  · obtain ⟨c, hc⟩ := hT
    rw [parityValue_eq_of_derives hP (hc.symmDiff hS hw), parityValue_eq_of_derives hP hc,
      BitString.neg_one_pow_toNat_xor, mul_comm]
  · push Not at hT
    rw [parityValue_eq_zero hT, mul_zero]
    exact parityValue_eq_zero fun c hc => hT (c ^^ b) <| by
      simpa using hc.symmDiff hS (by rw [symmDiff_symmDiff_cancel_right]; omega)

/-! ### Positive semidefiniteness -/

private theorem sum_sum_ite_nonneg {R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]
    {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (g : ι → κ) (b : ι → R) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, if g i = g j then b i * b j else 0 := by
  rw [← sum_fiberwise_of_maps_to fun _ => mem_image_of_mem g]
  refine sum_nonneg fun k _ => ?_
  have hk : ∑ i ∈ s with g i = k, ∑ j ∈ s, (if g i = g j then b i * b j else 0) =
      (∑ i ∈ s with g i = k, b i) * ∑ i ∈ s with g i = k, b i := by
    rw [sum_mul]
    refine sum_congr rfl fun i hi => ?_
    rw [(mem_filter.1 hi).2, mul_sum, sum_filter]
    exact sum_congr rfl fun _ _ => if_congr eq_comm rfl rfl
  exact hk ▸ mul_self_nonneg _

open Classical in
/-- A representative of the class of `A` under "`A ∆ B` is derivable". -/
private noncomputable def rep (P : ParitySystem σ) (w : ℕ) (A : Finset σ) : Finset σ :=
  Classical.epsilon fun B => 2 * #B ≤ w ∧ ∃ c, P.Derives w (A ∆ B) c

private theorem rep_spec {A : Finset σ} (hA : 2 * #A ≤ w) :
    2 * #(rep P w A) ≤ w ∧ ∃ c, P.Derives w (A ∆ rep P w A) c :=
  Classical.epsilon_spec (p := fun B => 2 * #B ≤ w ∧ ∃ c, P.Derives w (A ∆ B) c)
    ⟨A, hA, false, by rw [symmDiff_self]; exact Derives.empty⟩

/-- On sets of size at most `w / 2`, "`A ∆ B` is derivable" is transitive. -/
private theorem derives_symmDiff_trans {A B C : Finset σ} (hA : 2 * #A ≤ w) (hC : 2 * #C ≤ w)
    {b c : Bool} (hAB : P.Derives w (A ∆ B) b) (hBC : P.Derives w (B ∆ C) c) :
    P.Derives w (A ∆ C) (b ^^ c) := by
  have hAC : A ∆ B ∆ (B ∆ C) = A ∆ C := by rw [symmDiff_assoc, symmDiff_symmDiff_cancel_left]
  exact hAC ▸ hAB.symmDiff hBC (hAC.symm ▸ (card_symmDiff_le A C).trans (by omega))

private theorem rep_eq {A B : Finset σ} (hA : 2 * #A ≤ w) (hB : 2 * #B ≤ w) {c : Bool}
    (h : P.Derives w (A ∆ B) c) : rep P w A = rep P w B := by
  simp only [rep]
  congr 1; ext C
  exact and_congr_right fun hC =>
    ⟨fun ⟨_, hc⟩ => ⟨_, derives_symmDiff_trans hB hC (symmDiff_comm A B ▸ h) hc⟩,
     fun ⟨_, hc⟩ => ⟨_, derives_symmDiff_trans hA hC h hc⟩⟩

/-- **The moment matrix is positive semidefinite**: if `0 = 1` is not derivable in width `w`,
then for sets `A i` of size at most `w / 2` and any coefficients `a i`,
`∑ᵢ ∑ⱼ a i a j parityValue (A i ∆ A j) ≥ 0`. -/
theorem sum_sum_mul_parityValue_nonneg {R : Type*} [CommRing R] [LinearOrder R]
    [IsOrderedRing R] (hP : ¬ P.Derives w ∅ true) {ι : Type*} (s : Finset ι)
    (A : ι → Finset σ) (hA : ∀ i ∈ s, 2 * #(A i) ≤ w) (a : ι → R) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, a i * a j * parityValue P w (A i ∆ A j) := by
  classical
  let g (i : ι) := rep P w (A i)
  let b (i : ι) : R := a i * parityValue P w (A i ∆ g i)
  have key : ∀ i ∈ s, ∀ j ∈ s, a i * a j * parityValue P w (A i ∆ A j) =
      if g i = g j then b i * b j else 0 := fun i hi j hj => by
    split_ifs with h
    · dsimp only [g] at h
      obtain ⟨-, ci, hci⟩ := rep_spec (P := P) (hA i hi)
      obtain ⟨-, cj, hcj⟩ := rep_spec (P := P) (hA j hj)
      have hd := derives_symmDiff_trans (hA i hi) (hA j hj) (h ▸ hci) (symmDiff_comm (A j) _ ▸ hcj)
      simp only [b, g, parityValue_eq_of_derives hP hd, parityValue_eq_of_derives hP hci,
        parityValue_eq_of_derives hP hcj, BitString.neg_one_pow_toNat_xor]
      ring
    · rw [parityValue_eq_zero (fun c hc => h (rep_eq (hA i hi) (hA j hj) hc)), mul_zero]
  rw [sum_congr rfl fun i hi => sum_congr rfl fun j hj => key i hi j hj]
  exact sum_sum_ite_nonneg s g b

/-! ### The pseudo-expectation -/

section PseudoExpectation

variable {R : Type*} [CommRing R]

/-- The linear map `X ^ m ↦ parityValue (oddSupport m)`. -/
private noncomputable def fn (P : ParitySystem σ) (w : ℕ) : MvPolynomial σ R →ₗ[R] R :=
  (basisMonomials σ R).constr R fun m => parityValue P w (oddSupport m)

private theorem fn_monomial (m : σ →₀ ℕ) (c : R) :
    fn P w (monomial m c) = c * parityValue P w (oddSupport m) := by
  rw [show monomial m c = c • basisMonomials σ R m by simp [smul_monomial],
    map_smul, fn, Module.Basis.constr_basis, smul_eq_mul]

private theorem fn_eq_sum (p : MvPolynomial σ R) :
    fn P w p = ∑ m ∈ p.support, p.coeff m * parityValue P w (oddSupport m) := by
  conv_lhs => rw [p.as_sum, map_sum]
  exact sum_congr rfl fun m _ => fn_monomial m _

private theorem fn_mul_monomial (p : MvPolynomial σ R) (n : σ →₀ ℕ) :
    fn P w (p * monomial n 1) =
      ∑ m ∈ p.support, p.coeff m * parityValue P w (oddSupport m ∆ oddSupport n) := by
  conv_lhs => rw [p.as_sum]
  simp only [sum_mul, map_sum, monomial_mul_monomial, mul_one, fn_monomial, oddSupport_add]

private theorem fn_mul_C (q : MvPolynomial σ R) (c : R) : fn P w (q * C c) = c * fn P w q := by
  rw [mul_comm, C_mul', map_smul, smul_eq_mul]

private theorem fn_one : fn (R := R) P w 1 = 1 := by
  rw [← C_1, ← monomial_zero', fn_monomial, oddSupport_zero, one_mul, parityValue_empty]

private theorem fn_mul_X_sq_sub_one (q : MvPolynomial σ R) (i : σ) :
    fn P w (q * (X i ^ 2 - 1)) = 0 := by
  rw [mul_sub, mul_one, map_sub, X_pow_eq_monomial, fn_mul_monomial, oddSupport_single_two,
    fn_eq_sum, sub_eq_zero]
  exact sum_congr rfl fun m _ => by
    rw [show oddSupport m ∆ (∅ : Finset σ) = oddSupport m from symmDiff_bot _]

variable [LinearOrder R] [IsStrictOrderedRing R]

private theorem fn_mul_parityPoly (hP : ¬ P.Derives w ∅ true) {S : Finset σ} {b : Bool}
    (hS : ⟨S, b⟩ ∈ P) (q : MvPolynomial σ R) (hq : (q * parityPoly R S b).totalDegree ≤ w) :
    fn P w (q * parityPoly R S b) = 0 := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp
  rcases eq_or_ne (parityPoly R S b) 0 with hp | hp0
  · simp [hp]
  rw [totalDegree_mul_of_isDomain hq0 hp0, totalDegree_parityPoly] at hq
  have hd : P.Derives w S b := Derives.mem hS (by omega)
  rw [parityPoly, mul_sub, map_sub, prod_X_eq_monomial, fn_mul_monomial, fn_mul_C, fn_eq_sum,
    oddSupport_sum_single, mul_sum, sub_eq_zero]
  refine sum_congr rfl fun m hm => ?_
  have := (card_oddSupport_le_degree m).trans (le_totalDegree hm)
  rw [parityValue_symmDiff hP hd (by omega), mul_left_comm]

private theorem fn_sq_nonneg (hP : ¬ P.Derives w ∅ true) (s : MvPolynomial σ R)
    (hs : 2 * s.totalDegree ≤ w) : 0 ≤ fn P w (s ^ 2) := by
  have h : fn P w (s ^ 2) = ∑ m ∈ s.support, ∑ n ∈ s.support,
      s.coeff m * s.coeff n * parityValue P w (oddSupport m ∆ oddSupport n) := by
    rw [sq]
    conv_lhs => rw [s.as_sum, sum_mul_sum]
    simp only [map_sum, monomial_mul_monomial, fn_monomial, oddSupport_add]
  rw [h]
  exact sum_sum_mul_parityValue_nonneg hP s.support oddSupport
    (fun m hm => (Nat.mul_le_mul_left 2
      ((card_oddSupport_le_degree m).trans (le_totalDegree hm))).trans hs) s.coeff

variable [Fintype σ]

/-- **Schoenebeck's pseudo-expectation**: if width-`w` derivations from `P` do not reach `0 = 1`,
the map `X ^ m ↦ parityValue P w (oddSupport m)` is a pseudo-expectation of degree `w` for the
`±1` encoding of `P` [Schoenebeck, Lemma 13][Schoenebeck2008]. -/
noncomputable def pseudoExpectation (hP : ¬ P.Derives w ∅ true) :
    SOS.PseudoExpectation (P.toPolys R) w where
  toLinearMap := fn P w
  map_one := fn_one
  map_sq_nonneg := fn_sq_nonneg hP
  map_mul_eq_zero f hf q hq := by
    rcases mem_toPolys.1 hf with ⟨⟨S, b⟩, hS, rfl⟩ | ⟨i, rfl⟩
    · exact fn_mul_parityPoly hP hS q hq
    · exact fn_mul_X_sq_sub_one q i

/-- Schoenebeck's pseudo-expectation sends `c X ^ m` to `c parityValue (oddSupport m)`. -/
theorem pseudoExpectation_monomial (hP : ¬ P.Derives w ∅ true) (m : σ →₀ ℕ) (c : R) :
    (pseudoExpectation hP).toLinearMap (monomial m c) = c * parityValue P w (oddSupport m) :=
  fn_monomial m c

/-- Schoenebeck's pseudo-expectation sends `∏_{i ∈ T} Xᵢ` to `parityValue T`. -/
theorem pseudoExpectation_prod_X (hP : ¬ P.Derives w ∅ true) (T : Finset σ) :
    (pseudoExpectation (R := R) hP).toLinearMap (∏ i ∈ T, X i) = parityValue P w T := by
  rw [prod_X_eq_monomial, pseudoExpectation_monomial, oddSupport_sum_single, one_mul]

/-- **Schoenebeck's lemma** [Schoenebeck, Lemma 13][Schoenebeck2008]: over a strictly ordered
ring, if width-`d` derivations from the parity system `P` do not reach `0 = 1`, its `±1` encoding
has no sum-of-squares refutation of degree at most `d`. -/
theorem not_sos_refutableInDegree_toPolys {d : ℕ} (hP : ¬ P.Derives d ∅ true) :
    ¬ SOS.RefutableInDegree (P.toPolys R) d :=
  (pseudoExpectation hP).not_refutableInDegree

end PseudoExpectation

end Cslib.Logic.PL.ParitySystem
