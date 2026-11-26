/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.DictatorVsNoNotables
public import CslibFrontier.Foundations.BooleanAnalysis.HastadTest
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# Håstad's test as a Max-E3-Lin instance

The predicates of Max-E3-Lin are the 3-variable linear equations `x₁ + x₂ + x₃ = b` over `F₂`
[O'Donnell, Definition 7.22][ODonnell2014]: the parity relations `Logic.PL.CSP.paritySem`
of `CslibFrontier.Logics.Propositional.CSP.Boolean`, the relation symbol `b` holding when the XOR
of the bits is `b`, at the arity `Logic.PL.CSP.e3LinArity` three. A check of Håstad's test is
such an equation on the answers to three queries, so the test is a Max-E3-Lin instance on the
strings
[O'Donnell, Section 7.3, p. 187][ODonnell2014]. With every sign of a randomized assignment `g`
of mean `g w`, an equation `g(x) + g(y) + g(z) = b` holds with probability
`1/2 + 1/2 b g(x) g(y) g(z)`, `b` read as a sign (`Logic.PL.CSP.satProb_paritySem`).

The noise of Håstad's test, flipping each bit with probability `δ / 2`, is a finite uniform choice
when the flip probability `a / q` is rational: bit `i` flips when an independent uniform digit
`m i ∈ Fin q` is below `a` (`BitString.expect_fin_lt_eq_bernoulliAverage`). So for `a ≤ q`,
`Logic.PL.CSP.hastadTest a q n` lists one check for each choice of `x`, `y`, `b` and `m`, and on
every real `g` its value is Håstad's acceptance probability at noise rate `2 a / q`
(`Logic.PL.CSP.expectedSatFraction_hastadTest`), so that its value at a Boolean `f` is
`BitString.hastadAcceptance (2 a / q) f` (`Logic.PL.CSP.satFraction_hastadTest`). The test realizes
the noise at a rational rate, as the identification of testers with CSP instances requires; the
book ignores irrational rates there [O'Donnell, Section 7.3, p. 187][ODonnell2014].

By (7.4) for functions with values in `[-1, 1]` [O'Donnell, Exercise 7.22][ODonnell2014], for
`0 < a` and `2 a < q` this is a `(1/2, 1 - a / q)`-Dictator-vs.-No-Notables test using the
Max-E3-Lin predicates (`Logic.PL.CSP.isDictatorVsNoNotables_hastadTest`). For every real
`0 < δ < 1/2`, a rational `a / q ≤ δ` then gives a `(1/2, 1 - δ)` test
(`Logic.PL.CSP.exists_isDictatorVsNoNotables_e3Lin`) [O'Donnell, Theorem 7.42][ODonnell2014].
Through Theorem 7.40, which is not formalized, this gives UG-hardness of
`(1/2 + δ, 1 - δ)`-approximating Max-E3-Lin [O'Donnell, Corollary 7.44][ODonnell2014]. The gap
problem on linear systems over `F₂` is `Complexity.GapLin` in
`CslibFrontier.Computability.PCP.Approximation.GapLin`, NP-hard for one constant gap
(`Complexity.GapLin_npHard`).

## Usage

Open `Cslib.Logic.PL` and `Cslib.Logic.PL.CSP`. `Logic.PL.CSP.hastadTest a q n` has
`2 ^ (2 n + 1) q ^ n` checks, one `Logic.PL.CSP.hastadCheck a x y b m` for each `x`, `y`, `b` and
`m` (`Logic.PL.CSP.mem_hastadTest`); the checks are exposed, so a concrete check can be
evaluated with `decide`. For its value on a concrete function, rewrite with
`Logic.PL.CSP.satFraction_hastadTest` or `Logic.PL.CSP.expectedSatFraction_hastadTest` and use
the lemmas of `CslibFrontier.Foundations.BooleanAnalysis.HastadTest`. The checked clients in
[CslibFrontierTests/BooleanAnalysisHastadTest.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisHastadTest.lean)
check Theorem 7.42 at flip probability `1/4` and at the irrational `δ = 1/(2√2)`, the passing
probability `3/4` of a dictator in `hastadTest 1 4 5`, membership and evaluation of concrete
checks, and the value `1/2` of the constant `0`, each query a fair coin. Run
`scripts/build.sh CslibFrontierTests.BooleanAnalysisHastadTest` from the repository root to check
them.

## Main definitions

* `Cslib.Logic.PL.CSP.e3LinArity`: the arity of the Max-E3-Lin predicates `paritySem`.
* `Cslib.Logic.PL.CSP.hastadCheck`, `Cslib.Logic.PL.CSP.hastadTest`: Håstad's test at a rational
  flip probability, as a Max-E3-Lin instance.

## Main results

* `Cslib.Logic.PL.CSP.satProb_paritySem`: an equation at a randomized assignment.
* `Cslib.Logic.PL.CSP.mem_hastadTest`, `Cslib.Logic.PL.CSP.wellFormed_hastadTest`: the checks of
  the test, which are Max-E3-Lin equations.
* `Cslib.Logic.PL.CSP.expectedSatFraction_hastadTest`, `Cslib.Logic.PL.CSP.satFraction_hastadTest`:
  the value of the test is Håstad's acceptance probability.
* `Cslib.Logic.PL.CSP.isDictatorVsNoNotables_hastadTest`,
  `Cslib.Logic.PL.CSP.exists_isDictatorVsNoNotables_e3Lin`: Theorem 7.42.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.Logic.PL.CSP

open Finset Filter Topology Cslib.BitString
open scoped BigOperators

/-- The arity of the **Max-E3-Lin predicates** [O'Donnell, Definition 7.22][ODonnell2014]: three.
With the parity relations `paritySem`, the relation symbol `b` at arity three is the equation
`x₁ + x₂ + x₃ = b` over `F₂` (`paritySem_three`). -/
@[expose] def e3LinArity (_ : Bool) : ℕ := 3

/-- **An equation at a randomized assignment**: with independent signs of means `g u`, `g v` and
`g w`, the equation `u + v + w = b` holds with probability `1/2 + 1/2 b g(u) g(v) g(w)`, `b` read
as a sign. -/
theorem satProb_paritySem {V : Type*} (g : V → ℝ) (b : Bool) (u v w : V) :
    (⟨b, [u, v, w]⟩ : Constraint Bool V).satProb paritySem g =
      1 / 2 + 1 / 2 * (signVal b * g u * g v * g w) := by
  have hind (a : Fin 3 → Bool) : (if paritySem b (List.ofFn a) then (1 : ℝ) else 0) =
      1 / 2 * chi ℝ ∅ a + 1 / 2 * signVal b * chi ℝ univ a := by
    simp only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      paritySem_three, chi_eq_prod_signVal, Fin.prod_univ_three, prod_empty]
    generalize a 0 = a₀
    generalize a 1 = a₁
    generalize a 2 = a₂
    cases a₀ <;> cases a₁ <;> cases a₂ <;> cases b <;> norm_num
  rw [Constraint.satProb_def]
  change ∑ a : Fin 3 → Bool, _ = _
  simp only [hind, mul_add, sum_add_distrib, mul_left_comm _ (1 / 2 : ℝ),
    mul_left_comm _ (1 / 2 * signVal b), ← mul_sum, sum_meanWeight_mul_chi, prod_empty,
    Fin.prod_univ_three]
  simp only [Fin.isValue, Fin.getElem_fin, Fin.val_zero, Fin.val_one, Fin.val_two,
    List.getElem_cons_zero, List.getElem_cons_succ]
  ring

/-- The check of Håstad's test for the outcome `x`, `y`, `b`, `m`, at flip probability `a / q`:
query the strings `x`, `y` and `z' = x + y + (b, …, b) + P`, where the mask `P` flips bit `i`
exactly when the digit `m i ∈ Fin q` is below `a`, and accept when the three answers sum to `b`
in `F₂`. -/
@[expose] def hastadCheck (a : ℕ) {n q : ℕ} (x y : Fin n → Bool) (b : Bool) (m : Fin n → Fin q) :
    Constraint Bool (Fin n → Bool) :=
  ⟨b, [x, y, x + y + (fun _ => b) + fun i => decide ((m i : ℕ) < a)]⟩

/-- **Håstad's test** on `n` bits at the rational flip probability `a / q`, as a Max-E3-Lin
instance on the strings: one check `hastadCheck a x y b m` for each choice of strings `x`, `y`, a
bit `b` and digits `m : Fin n → Fin q`, so that a uniformly random check is Håstad's test at noise
rate `2 a / q` [O'Donnell, proof of Theorem 7.42][ODonnell2014]. -/
noncomputable def hastadTest (a q n : ℕ) : CSP Bool (Fin n → Bool) :=
  (univ : Finset ((Fin n → Bool) × (Fin n → Bool) × Bool × (Fin n → Fin q))).toList.map
    fun (x, y, b, m) => hastadCheck a x y b m

/-- The checks of Håstad's test are the checks `hastadCheck a x y b m`. -/
theorem mem_hastadTest {a q n : ℕ} {c : Constraint Bool (Fin n → Bool)} :
    c ∈ hastadTest a q n ↔
      ∃ (x y : Fin n → Bool) (b : Bool) (m : Fin n → Fin q), hastadCheck a x y b m = c := by
  simp [hastadTest]

/-- The checks of Håstad's test are Max-E3-Lin equations. -/
theorem wellFormed_hastadTest (a q n : ℕ) : (hastadTest a q n).WellFormed e3LinArity := by
  intro c hc
  obtain ⟨x, y, b, m, rfl⟩ := mem_hastadTest.1 hc
  rfl

/-- **The value of Håstad's test** at a real function `g` is the acceptance probability of
Håstad's test at noise rate `2 a / q`, for `a ≤ q`. -/
theorem expectedSatFraction_hastadTest {a q : ℕ} (hq : 0 < q) (ha : a ≤ q) {n : ℕ}
    (g : (Fin n → Bool) → ℝ) :
    (hastadTest a q n).expectedSatFraction paritySem g = hastadValue (2 * a / q) g := by
  rw [hastadTest, expectedSatFraction_map_toList _ _ ⟨(0, 0, false, fun _ => ⟨0, hq⟩), mem_univ _⟩,
    hastadValue_def]
  simp only [Fintype.expect_prod_type, hastadCheck, satProb_paritySem, noiseOp,
    show (1 - (1 - 2 * (a : ℝ) / q)) / 2 = a / q by ring]
  refine Finset.expect_congr rfl fun x _ => Finset.expect_congr rfl fun y _ =>
    Finset.expect_congr rfl fun b _ => ?_
  exact expect_fin_lt_eq_bernoulliAverage hq ha
    fun P => 1 / 2 + 1 / 2 * (signVal b * g x * g y * g (x + y + (fun _ => b) + P))

/-- **The value of Håstad's test** at a Boolean function `f` is the acceptance probability
`hastadAcceptance (2 a / q) f` of Håstad's test at noise rate `2 a / q`, for `a ≤ q`. -/
theorem satFraction_hastadTest {a q : ℕ} (hq : 0 < q) (ha : a ≤ q) {n : ℕ}
    (f : (Fin n → Bool) → Bool) :
    (hastadTest a q n).satFraction paritySem f = hastadAcceptance (2 * a / q) f := by
  rw [← expectedSatFraction_signVal, expectedSatFraction_hastadTest hq ha,
    hastadAcceptance_eq_hastadValue]

/-- **Håstad's test is a Dictator-vs.-No-Notables test** [O'Donnell, Theorem 7.42 and
Exercise 7.22][ODonnell2014]: for `0 < a` and `2 a < q`, flipping each bit with probability
`a / q`, it is a `(1/2, 1 - a / q)`-Dictator-vs.-No-Notables test using the Max-E3-Lin predicates,
with error `err(ε) = √ε / 2` for `ε ≤ 2 a / q` and `1/2` otherwise. -/
theorem isDictatorVsNoNotables_hastadTest {a q : ℕ} (ha : 0 < a) (haq : 2 * a < q) :
    IsDictatorVsNoNotables e3LinArity paritySem (1 / 2) (1 - a / q) (hastadTest a q) := by
  have hq : 0 < q := by omega
  have ha' : a ≤ q := by omega
  have hqR : (0 : ℝ) < q := Nat.cast_pos.2 hq
  have hδ : 0 < 2 * (a : ℝ) / q := by positivity
  have hδ1 : 2 * (a : ℝ) / q < 1 := by
    rw [div_lt_one hqR]
    exact_mod_cast haq
  have hδeq : 2 * (a : ℝ) / q = 2 * (a / q) := by ring
  refine ⟨inferInstance, by norm_num, by linarith, by linarith,
    fun n _ => wellFormed_hastadTest a q n, fun n i => ?_,
    fun ε => if ε ≤ 2 * a / q then √ε / 2 else 1 / 2, ?_, fun ε hε _ n _ g hg hinf => ?_⟩
  · rw [satFraction_hastadTest hq ha', hastadAcceptance_dictator]
    exact le_of_eq (by ring)
  · refine (tendsto_nhdsWithin_of_tendsto_nhds
      (by simpa using (Real.continuous_sqrt.tendsto 0).div_const 2)).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    rw [ite_eq_left hε.2.le]
  · rw [expectedSatFraction_hastadTest hq ha']
    dsimp only
    split_ifs with hεδ
    · linarith [hastadValue_le_of_stableInfluence_le hε.le hεδ hδ1.le hg hinf]
    · linarith [hastadValue_le_one hδ.le (by linarith) hg]

/-- **Theorem 7.42** [O'Donnell, Theorem 7.42 and Exercise 7.22][ODonnell2014]: for every
`0 < δ < 1/2` there is a `(1/2, 1 - δ)`-Dictator-vs.-No-Notables test using the Max-E3-Lin
predicates, the 3-variable `F₂`-linear equations. It is Håstad's test flipping each bit with a
probability `1 / q ≤ δ` (`hastadTest`), whose completeness `1 - 1 / q` is at least `1 - δ`. -/
theorem exists_isDictatorVsNoNotables_e3Lin {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1 / 2) :
    ∃ T : ∀ n : ℕ, CSP Bool (Fin n → Bool),
      IsDictatorVsNoNotables e3LinArity paritySem (1 / 2) (1 - δ) T := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  have hk2 : 2 * 1 < k + 1 := by
    have h : (1 : ℝ) / (k + 1) < 1 / 2 := hk.trans hδ1
    rw [one_div_lt_one_div (by positivity) (by norm_num)] at h
    exact_mod_cast h
  refine ⟨hastadTest 1 (k + 1), (isDictatorVsNoNotables_hastadTest one_pos hk2).of_le
    (by linarith) ?_⟩
  push_cast
  linarith

end Cslib.Logic.PL.CSP
