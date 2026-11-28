/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module

import CslibFrontier.Computability.Circuit.Pi
import CslibFrontier.Crypto.Protocols.FAEST.Conversion
import CslibFrontier.Crypto.Protocols.VOLE.Circuit
import CslibFrontier.Crypto.Protocols.VOLE.HigherDegreeCheck
import CslibFrontier.Crypto.Protocols.VOLE.MulCheck
import CslibFrontier.Foundations.FieldTheory.Finite.BinaryField
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Higher-degree QuickSilver, ACT Spend degree-9 parameters, and ACT V1 RLC clients

Exercises `CslibFrontier.Crypto.Protocols.VOLE.HigherDegreeCheck` across:
- Completeness and full honest-receiver view simulation at `d = 1`, `d = 2` (local `MulCheck`/
  `Circuit` compatibility checks), and `d = actSpendDegree = 9` over prime fields (`ZMod 5`,
  `ZMod 11`), binary fields (`BinaryField 2`, `BinaryField 4`), and a non-field ring with zero
  divisors (`ZMod 4`).
- Negative ZK and completeness witnesses (unmasked view leakage separating valid witnesses at
  `d = 9`, and a non-vanishing witness diverging from the zero-knowledge simulator).
- Sharpness of the Schwartz–Zippel bound `d / |F|` at `d = 9` (`9 / 11`) and small-field failure
  over `ZMod 2` (`100%` acceptance on `X ^ 9 - X`).
- Independent-weight batching (`toOuterMeasure_qsHomogLinearBatch_le` and
  `toOuterMeasure_qsMaskedCheckValue_le`), scalar-batched soundness (`t / |F| + d / |C|`), and
  single-shot FAEST grinding subsets.
- ACT Spend degree witness (`9 ∉ {7, 14}`), `"rata\x00l0"` trailing domain byte `0x30`, and local
  `FAEST.Conversion` VOLE lifting into characteristic-2 rings.
- ACT V1 RLC (`actSpendRLCCount = 45`) single-oracle, domain-separated single-RO FAEST+ACT, and
  folded Round-2+3 QuickSilver bounds, paired with negative witnesses for omitted domain
  separation (shared/colliding bytes), predictable challenges (`q * δ_K = 1`), and small challenge
  fields (`ZMod 2`).
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.VOLEHigherDegreeCheck

open Cslib Cslib.Circuits Cslib.Probability Cslib.Interactive Cslib.Interactive.Spec
open Cslib.Crypto.FAEST Cslib.Crypto.Protocols.VOLE
open scoped BigOperators ENNReal Matrix

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance : Fact (Nat.Prime 11) := ⟨by decide⟩
private instance : Fact (Nat.Prime 13) := ⟨by decide⟩
private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- Degree of `vole-mole`'s segmented-Keccak ACT Spend QuickSilver circuit (`d_zk = 9`). -/
private abbrev actSpendDegree : ℕ := 9

/-- Number of field components in ACT Spend's V1 RLC (`m_uov = 45`). -/
private abbrev actSpendRLCCount : ℕ := 45

/-- Degree-`9` (`actSpendDegree`) polynomial constraint `w 0 ^ 9 - w 1 = 0` over any `CommRing`. -/
private noncomputable def spendPoly {R : Type} [CommRing R] : MvPolynomial (Fin 2) R :=
  MvPolynomial.X 0 ^ 9 - MvPolynomial.X 1

private theorem totalDegree_spendPoly_le {R : Type} [CommRing R] :
    (spendPoly (R := R)).totalDegree ≤ actSpendDegree := by
  rw [spendPoly, actSpendDegree, sub_eq_add_neg]
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.totalDegree_pow _ _).trans ?_
    rcases subsingleton_or_nontrivial R with hsub | _
    · have h0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) R) = 0 := Subsingleton.eq_zero _
      simp [h0]
    · rw [MvPolynomial.totalDegree_X]
  · rw [MvPolynomial.totalDegree_neg]
    rcases subsingleton_or_nontrivial R with hsub | _
    · have h0 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) R) = 0 := Subsingleton.eq_zero _
      simp [h0]
    · rw [MvPolynomial.totalDegree_X]
      omega

private theorem spendPoly_eval_eq {R : Type} [CommRing R] (w : Fin 2 → R) :
    MvPolynomial.eval w spendPoly = w 0 ^ 9 - w 1 := by
  simp [spendPoly]

/-! ### Completeness and Full-View Zero-Knowledge Simulation (`d = 1`, `d = 2`, `d = 9`) -/

private noncomputable def linPoly : MvPolynomial (Fin 1) (ZMod 5) :=
  MvPolynomial.X 0 - MvPolynomial.C 2

-- Degree `d = 1` consumes zero extra mask coordinates (`Fin (1 - 1)` is empty).
example :
    qsMaskedCheckView 1 (fun _ : Fin 1 => linPoly) (fun _ => 2) =
      ProbComp.eval (qsMaskedCheckSimulate 1 (fun _ : Fin 1 => linPoly)) := by
  refine qsMaskedCheckView_eq_simulate (by omega) (fun _ : Fin 1 => linPoly) ?_ (fun _ => 2) ?_
  · intro _
    rw [linPoly, sub_eq_add_neg]
    have hx : (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) (ZMod 5)).totalDegree ≤ 1 :=
      (MvPolynomial.totalDegree_X (0 : Fin 1)).le
    have hc : (-MvPolynomial.C (2 : ZMod 5) : MvPolynomial (Fin 1) (ZMod 5)).totalDegree ≤ 1 := by
      rw [MvPolynomial.totalDegree_neg, MvPolynomial.totalDegree_C]
      exact Nat.zero_le 1
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le hx hc)
  · intro _
    rw [linPoly, MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_self]

-- Over `ZMod 5`, both `![1, 1]` and `![2, 2]` satisfy `w 0 ^ 9 = w 1` (since `2 ^ 9 = 512 ≡ 2`)
-- and produce identical full honest-receiver views under `(d - 1) = 8` VOLE masks.
example :
    (qsMaskedCheck actSpendDegree (fun _ : Fin 1 => (spendPoly (R := ZMod 5)))).Complete
      (voleWorld (ZMod 5) (2 + (actSpendDegree - 1)))
      (fun _ w => ∀ i : Fin 1, MvPolynomial.eval w ((fun _ => spendPoly) i) = 0)
      Accept 0 :=
  qsMaskedCheck_complete actSpendDegree (fun _ => spendPoly) (fun _ => totalDegree_spendPoly_le)

example :
    qsMaskedCheckView actSpendDegree (fun _ : Fin 1 => (spendPoly (R := ZMod 5))) ![1, 1] =
      qsMaskedCheckView actSpendDegree (fun _ : Fin 1 => (spendPoly (R := ZMod 5))) ![2, 2] := by
  rw [qsMaskedCheckView_eq_simulate (by decide : 1 ≤ actSpendDegree) _
      (fun _ => totalDegree_spendPoly_le) ![1, 1] (fun _ => by simp [spendPoly_eval_eq]),
    qsMaskedCheckView_eq_simulate (by decide : 1 ≤ actSpendDegree) _
      (fun _ => totalDegree_spendPoly_le) ![2, 2] (fun _ => by
        rw [spendPoly_eval_eq]
        decide)]

-- Full-view ZK at `d = 9` requires no field hypothesis; `ZMod 4` has zero divisors (`2 ^ 9 ≡ 0`).
example :
    qsMaskedCheckView actSpendDegree (fun _ : Fin 1 => (spendPoly (R := ZMod 4))) ![2, 0] =
      ProbComp.eval
        (qsMaskedCheckSimulate actSpendDegree (fun _ : Fin 1 => (spendPoly (R := ZMod 4)))) := by
  apply qsMaskedCheckView_eq_simulate (by decide : 1 ≤ actSpendDegree) _
    (fun _ => totalDegree_spendPoly_le)
  intro _
  rw [spendPoly_eval_eq]
  decide

private theorem coeff_qsHomogPoly_zero_v_lt {R : Type} [CommRing R] {n d : ℕ}
    (F_poly : MvPolynomial (Fin n) R) (hdeg : F_poly.totalDegree ≤ d) (w : Fin n → R)
    {k : ℕ} (hk : k < d) :
    (qsHomogPoly d F_poly w 0).coeff k = 0 := by
  rw [qsHomogPoly, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hm_le : (m.sum fun _ e => e) ≤ d :=
    (show m.sum (fun _ e => e) ≤ F_poly.totalDegree from MvPolynomial.le_totalDegree hm).trans hdeg
  have hprod : (∏ i : Fin n, qsWirePoly w 0 i ^ m i) =
      Polynomial.C (∏ i : Fin n, w i ^ m i) * Polynomial.X ^ (m.sum fun _ e => e) := by
    have hwire : ∀ i : Fin n, qsWirePoly w 0 i ^ m i =
        Polynomial.C (w i ^ m i) * Polynomial.X ^ m i := fun i => by
      simp [qsWirePoly, mul_pow, ← map_pow]
    simp_rw [hwire, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
    have hsum_eq : ∑ x : Fin n, m x = m.sum fun _ e => e := by
      simp only [Finsupp.sum]
      symm
      exact Finset.sum_subset (Finset.subset_univ m.support) fun i _ hi =>
        Finsupp.notMem_support_iff.mp hi
    rw [hsum_eq]
  rw [hprod]
  have hterm : Polynomial.C (F_poly.coeff m) * Polynomial.X ^ (d - m.sum fun _ e => e) *
      (Polynomial.C (∏ i : Fin n, w i ^ m i) * Polynomial.X ^ (m.sum fun _ e => e)) =
      Polynomial.C (F_poly.coeff m * ∏ i : Fin n, w i ^ m i) * Polynomial.X ^ d := by
    have hpow : Polynomial.X ^ (d - m.sum fun _ e => e) *
        (Polynomial.X : Polynomial R) ^ (m.sum fun _ e => e) = Polynomial.X ^ d := by
      rw [← pow_add, Nat.sub_add_cancel hm_le]
    calc Polynomial.C (F_poly.coeff m) * Polynomial.X ^ (d - m.sum fun _ e => e) *
          (Polynomial.C (∏ i : Fin n, w i ^ m i) * Polynomial.X ^ (m.sum fun _ e => e))
        = (Polynomial.C (F_poly.coeff m) * Polynomial.C (∏ i : Fin n, w i ^ m i)) *
            (Polynomial.X ^ (d - m.sum fun _ e => e) * Polynomial.X ^ (m.sum fun _ e => e)) := by
          ring
      _ = Polynomial.C (F_poly.coeff m * ∏ i : Fin n, w i ^ m i) * Polynomial.X ^ d := by
          rw [map_mul, hpow]
  rw [hterm, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ite_eq_right hk.ne, mul_zero]

private noncomputable def badDeg9View :
    ((ZMod 5) × (Fin 10 → ZMod 5)) ×
      Transcript (qsMaskedCheckSpec (ZMod 5) (Fin 1) 2 9) :=
  ((1, fun _ => 0), (![2, 0], (fun _ => 1, (fun _ => 0, ()))))

-- Negative test 1: a false witness (`![2, 0]`, `2 ^ 9 - 0 = 2 ≠ 0`) produces a real view
-- rejected by the verifier, separating `qsMaskedCheckView` from `qsMaskedCheckSimulate`.
example :
    qsMaskedCheckView 9 (fun _ : Fin 1 => (spendPoly (R := ZMod 5))) ![2, 0] ≠
      ProbComp.eval
        (qsMaskedCheckSimulate 9 (fun _ : Fin 1 => (spendPoly (R := ZMod 5)))) := by
  intro heq
  have hdeg9 : (spendPoly (R := ZMod 5)).totalDegree ≤ 9 := totalDegree_spendPoly_le
  have hreal : badDeg9View ∈
      (qsMaskedCheckView 9 (fun _ : Fin 1 => (spendPoly (R := ZMod 5))) ![2, 0]).support := by
    rw [qsMaskedCheckView_eq]
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff]
    refine ⟨voleSample 0 0 1,
      (mem_support_voleIdealDist_iff _).mpr (valid_voleSample _ _ _),
      (fun _ => 1), PMF.mem_support_uniformOfFintype _, ?_⟩
    have hcorr : voleCommitWitness ![2, 0]
        (fun i => (voleSample (0 : Fin 10 → ZMod 5) 0 1).u (Fin.castAdd (9 - 1) i)) =
        ![2, 0] := by
      funext i
      simp [voleCommitWitness, voleSample]
    have hrep : qsMaskedCheckReply 9 (fun _ : Fin 1 => (spendPoly (R := ZMod 5)))
        ![2, 0] (0 : Fin 10 → ZMod 5) 0 (fun _ => 1) = fun _ => 0 := by
      funext j
      simp only [qsMaskedCheckReply, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
        Finset.sum_singleton, one_mul, qsMaskCoeff, Pi.zero_apply]
      split_ifs <;> simp only [add_zero] <;>
        exact coeff_qsHomogPoly_zero_v_lt spendPoly hdeg9 ![2, 0] j.isLt
    have hrec : (voleSample (0 : Fin 10 → ZMod 5) 0 1).receiverView = (1, fun _ => 0) := by
      ext <;> simp [voleSample, VOLECorrelation.receiverView]
    have hview : ((voleSample (0 : Fin 10 → ZMod 5) 0 1).receiverView,
        (voleCommitWitness ![2, 0]
          (fun i => (voleSample (0 : Fin 10 → ZMod 5) 0 1).u (Fin.castAdd (9 - 1) i)),
          (fun _ => 1, (qsMaskedCheckReply 9 (fun _ : Fin 1 => (spendPoly (R := ZMod 5)))
            ![2, 0] (voleSample (0 : Fin 10 → ZMod 5) 0 1).u
            (voleSample (0 : Fin 10 → ZMod 5) 0 1).v (fun _ => 1), ())))) = badDeg9View := by
      have hu0 : (voleSample (0 : Fin 10 → ZMod 5) 0 1).u = 0 := rfl
      have hv0 : (voleSample (0 : Fin 10 → ZMod 5) 0 1).v = 0 := rfl
      rw [hrec, hcorr, hu0, hv0, hrep]
      rfl
    exact hview.symm
  rw [heq] at hreal
  have hacc := qsMaskedCheckSimulate_accepts (by decide : 1 ≤ 9)
    (fun _ : Fin 1 => (spendPoly (R := ZMod 5))) hreal
  have hval : qsMaskedCheckValue 9 (fun _ : Fin 1 => (spendPoly (R := ZMod 5)))
      1 (fun _ => 0) ![2, 0] (fun _ => 1) = 2 := by
    let c0 : VOLECorrelation (ZMod 5) 2 := voleSample 0 0 1
    have hc0 : c0.Valid := valid_voleSample _ _ _
    have hzero_poly : ∀ k : Fin 9, (qsHomogPoly 9 (spendPoly (R := ZMod 5)) ![2, 0] c0.v).coeff k =
        0 := fun k => coeff_qsHomogPoly_zero_v_lt spendPoly hdeg9 ![2, 0] k.isLt
    have hcw : (fun _ : Fin 2 => (0 : ZMod 5)) = c0.w := by
      funext i
      simp [c0, voleSample]
    have hcu : ![2, 0] = voleCommitWitness ![2, 0] c0.u := by
      funext i
      simp [c0, voleSample, voleCommitWitness]
    rw [qsMaskedCheckValue]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton,
      one_mul, qsMaskValue]
    have hmask0 : (∑ k : Fin (9 - 1), (0 : ZMod 5) * 1 ^ (k : ℕ)) = 0 := by simp
    have hq0 : (fun _ : Fin 2 => (0 : ZMod 5)) = c0.w := hcw
    rw [hmask0, add_zero, hcu]
    have hdelta0 : (1 : ZMod 5) = c0.delta := rfl
    rw [hq0, hdelta0]
    rw [qsHomogVerifierValue_eq_eval hdeg9 ![2, 0] c0 hc0]
    have hsum0 : qsPolySum 9 (fun k => (qsHomogPoly 9 spendPoly ![2, 0] c0.v).coeff k) c0.delta =
        0 := by
      simp [qsPolySum, hzero_poly]
    rw [hsum0, add_zero, spendPoly_eval_eq]
    change ((2 : ZMod 5) ^ 9 - 0) * (1 : ZMod 5) ^ 9 = 2
    decide
  dsimp only [QSMaskedCheckAccepts, badDeg9View] at hacc
  rw [hval] at hacc
  have hpoly0 : qsPolySum 9 (fun _ : Fin 9 => (0 : ZMod 5)) 1 = 0 := by
    simp [qsPolySum]
  rw [hpoly0] at hacc
  exact (by decide : (2 : ZMod 5) ≠ 0) hacc

-- Negative test 2: omitting the `d - 1 = 8` VOLE masks exposes the degree-1 homogenized
-- coefficient, separating valid witnesses `![0, 0]` and `![1, 1]` over `ZMod 5`.
private noncomputable def unmaskedDeg9View (w : Fin 2 → ZMod 5) :
    PMF ((ZMod 5 × (Fin 2 → ZMod 5)) × (Fin 2 → ZMod 5) × ZMod 5) :=
  (voleIdealDist (ZMod 5) 2).map fun c =>
    (c.receiverView, voleCommitWitness w c.u, (qsHomogPoly 9 spendPoly w c.v).coeff 1)

private noncomputable def leakedDeg9Event :
    (ZMod 5 × (Fin 2 → ZMod 5)) × (Fin 2 → ZMod 5) × ZMod 5 :=
  ((1, ![2, 0]), ![0, 0], 0)

private theorem coeff1_spendPoly_eq (w v : Fin 2 → ZMod 5) :
    (qsHomogPoly 9 (spendPoly (R := ZMod 5)) w v).coeff 1 =
      (qsWirePoly w v 0 ^ 9).coeff 1 := by
  classical
  let m0 : Fin 2 →₀ ℕ := Finsupp.single 0 9
  let m1 : Fin 2 →₀ ℕ := Finsupp.single 1 1
  have hsp : (spendPoly (R := ZMod 5)) =
      MvPolynomial.monomial m0 1 - MvPolynomial.monomial m1 1 := by
    simp [spendPoly, m0, m1, MvPolynomial.X, MvPolynomial.monomial_pow]
  have hm_ne : m0 ≠ m1 := by
    intro h
    have h0 := DFunLike.congr_fun h 0
    simp [m0, m1] at h0
  have hsub_supp : (spendPoly (R := ZMod 5)).support ⊆ ({m0, m1} : Finset (Fin 2 →₀ ℕ)) := by
    intro m hm
    rw [hsp, MvPolynomial.mem_support_iff, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
      MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial] at hm
    rw [Finset.mem_insert, Finset.mem_singleton]
    by_cases h0 : m0 = m
    · exact Or.inl h0.symm
    · by_cases h1 : m1 = m
      · exact Or.inr h1.symm
      · simp [h0, h1] at hm
  rw [qsHomogPoly]
  have hrewrite : (spendPoly (R := ZMod 5)).support.sum (fun m =>
      Polynomial.C ((spendPoly (R := ZMod 5)).coeff m) *
        Polynomial.X ^ (9 - m.sum fun _ e => e) * ∏ i : Fin 2, qsWirePoly w v i ^ m i) =
      ({m0, m1} : Finset (Fin 2 →₀ ℕ)).sum (fun m =>
        Polynomial.C ((spendPoly (R := ZMod 5)).coeff m) *
          Polynomial.X ^ (9 - m.sum fun _ e => e) * ∏ i : Fin 2, qsWirePoly w v i ^ m i) := by
    refine Finset.sum_subset hsub_supp fun m _ hm => ?_
    simp [MvPolynomial.notMem_support_iff.mp hm]
  rw [hrewrite, Finset.sum_pair hm_ne, Polynomial.coeff_add]
  have hc0 : (spendPoly (R := ZMod 5)).coeff m0 = 1 := by
    rw [hsp, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, MvPolynomial.coeff_monomial,
      MvPolynomial.coeff_monomial, ite_eq_left rfl, ite_eq_right hm_ne.symm, sub_zero]
  have hc1 : (spendPoly (R := ZMod 5)).coeff m1 = -1 := by
    rw [hsp, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, MvPolynomial.coeff_monomial,
      MvPolynomial.coeff_monomial, ite_eq_right hm_ne, ite_eq_left rfl, zero_sub]
  have hs0 : (m0.sum fun _ e => e) = 9 := Finsupp.sum_single_index rfl
  have hs1 : (m1.sum fun _ e => e) = 1 := Finsupp.sum_single_index rfl
  have hp0 : (∏ i : Fin 2, qsWirePoly w v i ^ m0 i) = qsWirePoly w v 0 ^ 9 := by
    rw [Fin.prod_univ_two]
    simp [m0]
  have hp1 : (∏ i : Fin 2, qsWirePoly w v i ^ m1 i) = qsWirePoly w v 1 := by
    rw [Fin.prod_univ_two]
    simp [m1]
  rw [hc0, hc1, hs0, hs1, hp0, hp1]
  have hterm1 : (Polynomial.C (-1 : ZMod 5) * Polynomial.X ^ (9 - 1) * qsWirePoly w v 1).coeff 1 =
      0 := by
    have hfac : Polynomial.C (-1 : ZMod 5) * Polynomial.X ^ (9 - 1) * qsWirePoly w v 1 =
        Polynomial.X ^ 8 * (Polynomial.C (-1 : ZMod 5) * qsWirePoly w v 1) := by
      rw [show 9 - 1 = 8 by rfl]
      ring
    rw [hfac, Polynomial.coeff_X_pow_mul']
    simp
  rw [hterm1, add_zero]
  simp

example :
    leakedDeg9Event ∈ (unmaskedDeg9View ![0, 0]).support ∧
      leakedDeg9Event ∉ (unmaskedDeg9View ![1, 1]).support := by
  constructor
  · simp only [unmaskedDeg9View, PMF.mem_support_map_iff]
    refine ⟨voleSample 0 ![2, 0] 1,
      (mem_support_voleIdealDist_iff _).mpr (valid_voleSample _ _ _), ?_⟩
    have hc1 : (qsHomogPoly 9 (spendPoly (R := ZMod 5)) ![0, 0] ![2, 0]).coeff 1 = 0 := by
      rw [coeff1_spendPoly_eq]
      have hw0 : qsWirePoly ![0, 0] ![2, 0] 0 = Polynomial.C (2 : ZMod 5) := by
        simp [qsWirePoly]
      rw [hw0, ← map_pow, Polynomial.coeff_C_of_ne_zero (by decide : (1 : ℕ) ≠ 0)]
    refine Prod.ext (Prod.ext rfl ?_) (Prod.ext ?_ hc1)
    · funext i
      fin_cases i <;> decide
    · funext i
      fin_cases i <;> simp [voleCommitWitness, voleSample, leakedDeg9Event]
  · simp only [unmaskedDeg9View, PMF.mem_support_map_iff, not_exists, not_and]
    intro c hc heq
    have hrec : c.delta = 1 ∧ c.w = ![2, 0] := by
      have h1 := congrArg Prod.fst heq
      exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩
    have hcorr : voleCommitWitness ![1, 1] c.u = ![0, 0] := congrArg (fun x => x.2.1) heq
    have hc1 : (qsHomogPoly 9 (spendPoly (R := ZMod 5)) ![1, 1] c.v).coeff 1 = 0 :=
      congrArg (fun x => x.2.2) heq
    have hu0 : c.u 0 = 1 := by
      have h0 := congrFun hcorr 0
      simp only [voleCommitWitness, Pi.sub_apply, Matrix.cons_val_zero] at h0
      exact sub_eq_zero.mp h0 |>.symm
    have hv0 : c.v 0 = 1 := by
      have hvalid := (mem_support_voleIdealDist_iff c).mp hc 0
      have hw0 := congrFun hrec.2 0
      rw [hvalid, hrec.1, hu0] at hw0
      change 1 * 1 + c.v 0 = 2 at hw0
      calc c.v 0 = (1 * 1 + c.v 0) - 1 := by ring
        _ = 2 - 1 := by rw [hw0]
        _ = 1 := by decide
    rw [coeff1_spendPoly_eq] at hc1
    have hwire : qsWirePoly ![1, 1] c.v 0 = Polynomial.X + Polynomial.C (1 : ZMod 5) := by
      simp [qsWirePoly, hv0, add_comm]
    rw [hwire, Polynomial.coeff_X_add_C_pow] at hc1
    have hbad : ((1 : ZMod 5) ^ (9 - 1) * ↑(Nat.choose 9 1) : ZMod 5) = 0 := hc1
    exact (by decide : ((1 : ZMod 5) ^ (9 - 1) * ↑(Nat.choose 9 1) : ZMod 5) ≠ 0) hbad

/-! ### Soundness Bounds, Tightness at `d = 9`, Small-Field Failure, and FAEST Grinding -/

private noncomputable def nineRootPoly : Polynomial (ZMod 11) :=
  ∏ k : Fin 9, (Polynomial.X - Polynomial.C (k.val : ZMod 11))

private theorem natDegree_nineRootPoly : nineRootPoly.natDegree ≤ actSpendDegree := by
  rw [nineRootPoly, actSpendDegree]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  rw [Finset.sum_congr rfl fun k _ => Polynomial.natDegree_X_sub_C (k.val : ZMod 11)]
  simp

private theorem coeff_nineRootPoly_nine : nineRootPoly.coeff 9 = 1 := by
  have hmonic : nineRootPoly.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun k _ => Polynomial.monic_X_sub_C _
  have hdeg : nineRootPoly.natDegree = 9 := by
    rw [nineRootPoly, Polynomial.natDegree_prod_of_monic _ _ fun k _ => Polynomial.monic_X_sub_C _]
    rw [Finset.sum_congr rfl fun k _ => Polynomial.natDegree_X_sub_C (k.val : ZMod 11)]
    simp
  rw [← hdeg]
  exact hmonic.leadingCoeff

-- Over `ZMod 11`, `toOuterMeasure_qsCheck_le` bounds acceptance by `9 / 11`, and `nineRootPoly`
-- meets `9 / 11` with exact equality.
example :
    (PMF.uniformOfFintype (ZMod 11)).toOuterMeasure
        {delta | nineRootPoly.eval delta = qsPolySum actSpendDegree (fun _ => 0) delta} ≤
      9 / (11 : ℝ≥0∞) := by
  have hne : nineRootPoly.coeff actSpendDegree ≠ 0 := by
    rw [actSpendDegree, coeff_nineRootPoly_nine]
    decide
  simpa only [ZMod.card, actSpendDegree, Nat.cast_ofNat] using
    toOuterMeasure_qsCheck_le natDegree_nineRootPoly hne (fun _ => 0)

example :
    (PMF.uniformOfFintype (ZMod 11)).toOuterMeasure
        {delta | nineRootPoly.eval delta = qsPolySum actSpendDegree (fun _ => 0) delta} =
      9 / (11 : ℝ≥0∞) := by
  rw [PMF.toOuterMeasure_uniformOfFintype, ZMod.card]
  have hset : ({delta | delta ∈
      {delta : ZMod 11 | nineRootPoly.eval delta = qsPolySum actSpendDegree (fun _ => 0) delta}} :
      Finset (ZMod 11)) = Finset.univ.image (fun k : Fin 9 => (k.val : ZMod 11)) := by
    ext delta
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, qsPolySum,
      zero_mul, Finset.sum_const_zero, Finset.mem_image, nineRootPoly, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff]
    simp [sub_eq_zero, eq_comm]
  rw [hset, Finset.card_image_of_injective]
  · norm_num [div_eq_mul_inv]
  · intro a b hab
    have hval : a.val % 11 = b.val % 11 := by
      simpa [ZMod.val_natCast] using congrArg ZMod.val hab
    ext
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hval
    exact hval

-- Small-field negative test: over `ZMod 2`, a degree-9 polynomial `X ^ 9 - X` with nonzero top
-- coefficient vanishes on EVERY element of the challenge field (`100%` false-claim acceptance).
example :
    (Polynomial.X ^ 9 - Polynomial.X : Polynomial (ZMod 2)).natDegree ≤ 9 ∧
      (Polynomial.X ^ 9 - Polynomial.X : Polynomial (ZMod 2)).coeff 9 = 1 ∧
      (PMF.uniformOfFintype (ZMod 2)).toOuterMeasure
        {delta : ZMod 2 | (Polynomial.X ^ 9 - Polynomial.X : Polynomial (ZMod 2)).eval delta =
          qsPolySum 9 (fun _ => 0) delta} = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact Polynomial.natDegree_X_pow_le 9
    · exact Polynomial.natDegree_X_le.trans (by omega)
  · simp [Polynomial.coeff_X_pow, Polynomial.coeff_X_of_ne_one (by decide : (9 : ℕ) ≠ 1)]
  · have huniv : {delta : ZMod 2 |
        (Polynomial.X ^ 9 - Polynomial.X : Polynomial (ZMod 2)).eval delta =
          qsPolySum 9 (fun _ => 0) delta} = Set.univ := by
      ext delta
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, qsPolySum, zero_mul, Finset.sum_const_zero]
      fin_cases delta <;> decide
    rw [huniv, PMF.toOuterMeasure_apply_eq_one_iff]
    exact Set.subset_univ _

-- Scalar-batched degree-9 soundness (`t / |F| + d / |C|`) on a false `spendPoly` instance.
example (a : ZMod 13 → PMF (Fin actSpendDegree → ZMod 13)) :
    (do
      let chi ← PMF.uniformOfFintype (ZMod 13)
      let reply ← a chi
      let delta ← PMF.uniformOfFintype (ZMod 13)
      let P_batch : Polynomial (ZMod 13) := ∑ i : Fin 2, Polynomial.C (quickSilverWeight chi i) *
        qsHomogPoly actSpendDegree spendPoly ![2, 0] 0
      return decide (P_batch.eval delta = qsPolySum actSpendDegree reply delta)).toOuterMeasure
        {true} ≤ 2 / (13 : ℝ≥0∞) + 9 / (13 : ℝ≥0∞) := by
  have h := toOuterMeasure_qsHomogScalarBatch_le (Function.Embedding.refl (ZMod 13))
    (fun _ : Fin 2 => (spendPoly (R := ZMod 13))) (fun _ => totalDegree_spendPoly_le)
    ![2, 0] 0 ⟨0, by rw [spendPoly_eval_eq]; decide⟩ a
  conv at h =>
    lhs
    simp only [Function.Embedding.refl_apply]
  conv at h =>
    rhs
    rw [ZMod.card, show actSpendDegree = 9 from rfl]
    simp only [Nat.cast_ofNat]
  exact h

-- Single-shot FAEST grinding subsets over `BinaryField 4` (`2 ^ 4 = 16` accepted challenges vs
-- `2 ^ 6 = 64` raw challenges at `d = actSpendDegree = 9`).
private def toyGrindParams : ChallengeParams where
  securityBits := 6
  repetitions := 2
  grindingBits := 2
  grindingBits_le := by decide
  repetitions_pos := by decide
  repetitions_le := by decide

example (a : Fin actSpendDegree → BinaryField 4) :
    (PMF.uniformOfFintype
        {c : BitString toyGrindParams.securityBits //
          grindingAccepted toyGrindParams c = true}).toOuterMeasure
        {c | (qsHomogPoly actSpendDegree (spendPoly (R := BinaryField 4)) ![1, 0] 0).eval
            (BinaryField.embed (w := 4) (by decide) (le_refl 4)
              (grindingAcceptedEquiv toyGrindParams c)) =
          qsPolySum actSpendDegree a
            (BinaryField.embed (w := 4) (by decide) (le_refl 4)
              (grindingAcceptedEquiv toyGrindParams c))} ≤
      9 / (2 ^ 4 : ℝ≥0∞) := by
  have hdeg : (qsHomogPoly actSpendDegree (spendPoly (R := BinaryField 4)) ![1, 0] 0).natDegree ≤
      actSpendDegree := natDegree_qsHomogPoly_le totalDegree_spendPoly_le _ _
  have hne : (qsHomogPoly actSpendDegree (spendPoly (R := BinaryField 4)) ![1, 0] 0).coeff
      actSpendDegree ≠ 0 := by
    rw [coeff_qsHomogPoly_eq_eval totalDegree_spendPoly_le, spendPoly_eval_eq]
    simp
  have h := toOuterMeasure_qsCheck_grinding_accepted_le toyGrindParams
    (BinaryField.embed (w := 4) (by decide) (le_refl 4)) hdeg hne a
  conv at h =>
    rhs
    rw [show toyGrindParams.nonGrindingBits = 4 from rfl, show actSpendDegree = 9 from rfl]
    simp only [Nat.cast_ofNat]
  exact h

example (a : Fin actSpendDegree → BinaryField 4) :
    (PMF.uniformOfFintype (BitString toyGrindParams.securityBits)).toOuterMeasure
        {c | ∃ h : grindingAccepted toyGrindParams c = true,
          (qsHomogPoly actSpendDegree (spendPoly (R := BinaryField 4)) ![1, 0] 0).eval
              (BinaryField.embed (w := 4) (by decide) (le_refl 4)
                (grindingAcceptedEquiv toyGrindParams ⟨c, h⟩)) =
            qsPolySum actSpendDegree a
              (BinaryField.embed (w := 4) (by decide) (le_refl 4)
                (grindingAcceptedEquiv toyGrindParams ⟨c, h⟩))} ≤
      9 / (2 ^ 6 : ℝ≥0∞) := by
  have hdeg : (qsHomogPoly actSpendDegree (spendPoly (R := BinaryField 4)) ![1, 0] 0).natDegree ≤
      actSpendDegree := natDegree_qsHomogPoly_le totalDegree_spendPoly_le _ _
  have hne : (qsHomogPoly actSpendDegree (spendPoly (R := BinaryField 4)) ![1, 0] 0).coeff
      actSpendDegree ≠ 0 := by
    rw [coeff_qsHomogPoly_eq_eval totalDegree_spendPoly_le, spendPoly_eval_eq]
    simp
  have h := toOuterMeasure_qsCheck_grinding_raw_le toyGrindParams
    (BinaryField.embed (w := 4) (by decide) (le_refl 4)) hdeg hne a
  conv at h =>
    rhs
    rw [show toyGrindParams.securityBits = 6 from rfl, show actSpendDegree = 9 from rfl]
    simp only [Nat.cast_ofNat]
  exact h

-- Independent-weight degree-9 soundness (`1 / |F| + (1 - 1 / |F|) * (d / |C|)`) on `spendPoly`.
example (a : (Fin 2 → ZMod 13) → PMF (Fin actSpendDegree → ZMod 13)) :
    (do
      let r ← PMF.uniformOfFintype (Fin 2 → ZMod 13)
      let reply ← a r
      let delta ← PMF.uniformOfFintype (ZMod 13)
      let P_batch : Polynomial (ZMod 13) := ∑ i : Fin 2, Polynomial.C (r i) *
        qsHomogPoly actSpendDegree spendPoly ![2, 0] 0
      return decide (P_batch.eval delta = qsPolySum actSpendDegree reply delta)).toOuterMeasure
        {true} ≤ (13 : ℝ≥0∞)⁻¹ + (1 - (13 : ℝ≥0∞)⁻¹) * (9 / (13 : ℝ≥0∞)) := by
  have h := toOuterMeasure_qsHomogLinearBatch_le (Function.Embedding.refl (ZMod 13))
    (fun _ : Fin 2 => (spendPoly (R := ZMod 13))) (fun _ => totalDegree_spendPoly_le)
    ![2, 0] 0 ⟨0, by rw [spendPoly_eval_eq]; decide⟩ a
  simpa only [Function.Embedding.refl_apply, ZMod.card, show actSpendDegree = 9 from rfl,
    Nat.cast_ofNat] using h

-- Independent-weight degree-9 soundness of `qsMaskedCheckValue` with nonzero VOLE masks `(u, v)`.
example (a : (Fin 2 → ZMod 13) → PMF (Fin actSpendDegree → ZMod 13)) :
    (do
      let r ← PMF.uniformOfFintype (Fin 2 → ZMod 13)
      let reply ← a r
      let delta ← PMF.uniformOfFintype (ZMod 13)
      let u : Fin (2 + (actSpendDegree - 1)) → ZMod 13 := fun _ => 1
      let v : Fin (2 + (actSpendDegree - 1)) → ZMod 13 := fun j => (j.val : ZMod 13)
      let d_corr : Fin 2 → ZMod 13 := ![1, -1]
      let q : Fin (2 + (actSpendDegree - 1)) → ZMod 13 := fun j => u j * delta + v j
      return decide (qsMaskedCheckValue actSpendDegree (fun _ : Fin 2 => spendPoly)
        delta q d_corr r = qsPolySum actSpendDegree reply delta)).toOuterMeasure {true} ≤
      (13 : ℝ≥0∞)⁻¹ + (1 - (13 : ℝ≥0∞)⁻¹) * (9 / (13 : ℝ≥0∞)) := by
  have hfalse : ∃ i : Fin 2, MvPolynomial.eval
      (fun j => (1 : ZMod 13) + (![1, -1] : Fin 2 → ZMod 13) j) spendPoly ≠ 0 := by
    refine ⟨0, ?_⟩
    rw [spendPoly_eval_eq]
    decide
  have h := toOuterMeasure_qsMaskedCheckValue_le (Function.Embedding.refl (ZMod 13))
    (fun _ : Fin 2 => (spendPoly (R := ZMod 13))) (fun _ => totalDegree_spendPoly_le)
    (fun _ => 1) (fun j => (j.val : ZMod 13)) ![1, -1] hfalse a
  simpa only [Function.Embedding.refl_apply, ZMod.card, show actSpendDegree = 9 from rfl,
    Nat.cast_ofNat] using h

/-! ### Bridges to `VOLE.MulCheck`, `VOLE.Circuit`, and `FAEST.Conversion` -/

section Bridges

variable {R : Type} [CommRing R]

private theorem mvTotalDegree_X_le {n : ℕ} (i : Fin n) :
    (MvPolynomial.X i : MvPolynomial (Fin n) R).totalDegree ≤ 1 := by
  rcases subsingleton_or_nontrivial R with hsub | _
  · have : (MvPolynomial.X i : MvPolynomial (Fin n) R) = 0 := Subsingleton.eq_zero _
    simp [this]
  · exact (MvPolynomial.totalDegree_X i).le

private noncomputable def mulGatePoly {n : ℕ} (a b c : Fin n) : MvPolynomial (Fin n) R :=
  MvPolynomial.X a * MvPolynomial.X b - MvPolynomial.X c

private theorem totalDegree_mulGatePoly_le {n : ℕ} (a b c : Fin n) :
    (mulGatePoly (R := R) a b c).totalDegree ≤ 2 := by
  rw [mulGatePoly, sub_eq_add_neg]
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · exact (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add (mvTotalDegree_X_le a) (mvTotalDegree_X_le b))
  · rw [MvPolynomial.totalDegree_neg]
    exact (mvTotalDegree_X_le c).trans (by omega)

private theorem qsHomogVerifierValue_add {n : ℕ} (d : ℕ)
    (F₁ F₂ : MvPolynomial (Fin n) R) (delta : R) (q' : Fin n → R) :
    qsHomogVerifierValue d (F₁ + F₂) delta q' =
      qsHomogVerifierValue d F₁ delta q' + qsHomogVerifierValue d F₂ delta q' := by
  let term (F : MvPolynomial (Fin n) R) (m : Fin n →₀ ℕ) : R :=
    F.coeff m * delta ^ (d - m.sum fun _ e => e) * ∏ i : Fin n, q' i ^ m i
  have hzero : ∀ (F : MvPolynomial (Fin n) R) m, m ∉ F.support → term F m = 0 := by
    intro F m hm
    simp [term, MvPolynomial.notMem_support_iff.mp hm]
  have h1 : qsHomogVerifierValue d (F₁ + F₂) delta q' =
      (F₁.support ∪ F₂.support).sum (term (F₁ + F₂)) :=
    Finset.sum_subset MvPolynomial.support_add fun m _ hm => hzero _ m hm
  have h2 : qsHomogVerifierValue d F₁ delta q' =
      (F₁.support ∪ F₂.support).sum (term F₁) :=
    Finset.sum_subset Finset.subset_union_left fun m _ hm => hzero _ m hm
  have h3 : qsHomogVerifierValue d F₂ delta q' =
      (F₁.support ∪ F₂.support).sum (term F₂) :=
    Finset.sum_subset Finset.subset_union_right fun m _ hm => hzero _ m hm
  rw [h1, h2, h3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  dsimp only [term]
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  ring

private theorem qsHomogVerifierValue_neg {n : ℕ} (d : ℕ)
    (F : MvPolynomial (Fin n) R) (delta : R) (q' : Fin n → R) :
    qsHomogVerifierValue d (-F) delta q' = -qsHomogVerifierValue d F delta q' := by
  rw [qsHomogVerifierValue, qsHomogVerifierValue]
  rw [MvPolynomial.support_neg (p := F), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply]
  ring

private theorem qsHomogVerifierValue_sub {n : ℕ} (d : ℕ)
    (F₁ F₂ : MvPolynomial (Fin n) R) (delta : R) (q' : Fin n → R) :
    qsHomogVerifierValue d (F₁ - F₂) delta q' =
      qsHomogVerifierValue d F₁ delta q' - qsHomogVerifierValue d F₂ delta q' := by
  rw [sub_eq_add_neg, qsHomogVerifierValue_add, qsHomogVerifierValue_neg, sub_eq_add_neg]

private theorem qsHomogPoly_add {n : ℕ} (d : ℕ)
    (F₁ F₂ : MvPolynomial (Fin n) R) (w v : Fin n → R) :
    qsHomogPoly d (F₁ + F₂) w v = qsHomogPoly d F₁ w v + qsHomogPoly d F₂ w v := by
  let term (F : MvPolynomial (Fin n) R) (m : Fin n →₀ ℕ) : Polynomial R :=
    Polynomial.C (F.coeff m) * Polynomial.X ^ (d - m.sum fun _ e => e) *
      ∏ i : Fin n, qsWirePoly w v i ^ m i
  have hzero : ∀ (F : MvPolynomial (Fin n) R) m, m ∉ F.support → term F m = 0 := by
    intro F m hm
    simp [term, MvPolynomial.notMem_support_iff.mp hm]
  have h1 : qsHomogPoly d (F₁ + F₂) w v = (F₁.support ∪ F₂.support).sum (term (F₁ + F₂)) :=
    Finset.sum_subset MvPolynomial.support_add fun m _ hm => hzero _ m hm
  have h2 : qsHomogPoly d F₁ w v = (F₁.support ∪ F₂.support).sum (term F₁) :=
    Finset.sum_subset Finset.subset_union_left fun m _ hm => hzero _ m hm
  have h3 : qsHomogPoly d F₂ w v = (F₁.support ∪ F₂.support).sum (term F₂) :=
    Finset.sum_subset Finset.subset_union_right fun m _ hm => hzero _ m hm
  rw [h1, h2, h3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  dsimp only [term]
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add]
  ring

private theorem qsHomogPoly_neg {n : ℕ} (d : ℕ)
    (F : MvPolynomial (Fin n) R) (w v : Fin n → R) :
    qsHomogPoly d (-F) w v = -qsHomogPoly d F w v := by
  rw [qsHomogPoly, qsHomogPoly, MvPolynomial.support_neg (p := F), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, map_neg]
  ring

private theorem qsHomogPoly_sub {n : ℕ} (d : ℕ)
    (F₁ F₂ : MvPolynomial (Fin n) R) (w v : Fin n → R) :
    qsHomogPoly d (F₁ - F₂) w v = qsHomogPoly d F₁ w v - qsHomogPoly d F₂ w v := by
  rw [sub_eq_add_neg, qsHomogPoly_add, qsHomogPoly_neg, sub_eq_add_neg]

private theorem qsHomogPoly_monomial {n : ℕ} (d : ℕ) (m : Fin n →₀ ℕ) (c : R)
    (w v : Fin n → R) :
    qsHomogPoly d (MvPolynomial.monomial m c) w v =
      Polynomial.C c * Polynomial.X ^ (d - m.sum fun _ e => e) *
        ∏ i : Fin n, qsWirePoly w v i ^ m i := by
  classical
  by_cases hc : c = 0
  · subst hc
    simp [qsHomogPoly]
  · rw [qsHomogPoly, MvPolynomial.support_monomial, ite_eq_right hc, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, ite_eq_left rfl]

private theorem prod_pow_finsupp_single {n : ℕ} {M : Type} [CommMonoid M] (g : Fin n → M)
    (a : Fin n) : (∏ j : Fin n, g j ^ (Finsupp.single a 1 : Fin n →₀ ℕ) j) = g a := by
  rw [Finset.prod_eq_single a]
  · simp
  · intro j _ hj
    simp [hj.symm]
  · intro ha
    exact (ha (Finset.mem_univ a)).elim

private theorem prod_pow_finsupp_pair {n : ℕ} {M : Type} [CommMonoid M] (g : Fin n → M)
    (a b : Fin n) :
    (∏ j : Fin n, g j ^ ((Finsupp.single a 1 + Finsupp.single b 1 : Fin n →₀ ℕ) j)) =
      g a * g b := by
  calc (∏ j : Fin n, g j ^ ((Finsupp.single a 1 + Finsupp.single b 1 : Fin n →₀ ℕ) j))
      = (∏ j : Fin n, g j ^ (Finsupp.single a 1 : Fin n →₀ ℕ) j *
          g j ^ (Finsupp.single b 1 : Fin n →₀ ℕ) j) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        simp only [Finsupp.add_apply, pow_add]
    _ = (∏ j : Fin n, g j ^ (Finsupp.single a 1 : Fin n →₀ ℕ) j) *
        (∏ j : Fin n, g j ^ (Finsupp.single b 1 : Fin n →₀ ℕ) j) := Finset.prod_mul_distrib
    _ = g a * g b := by
        rw [prod_pow_finsupp_single g a, prod_pow_finsupp_single g b]

private theorem qsHomogVerifierValue_C_mul_X {n : ℕ} (d : ℕ)
    (c : R) (i : Fin n) (delta : R) (q' : Fin n → R) :
    qsHomogVerifierValue d (MvPolynomial.C c * MvPolynomial.X i) delta q' =
      c * q' i * delta ^ (d - 1) := by
  classical
  by_cases hc : c = 0
  · subst hc
    simp [qsHomogVerifierValue]
  · have hmon : MvPolynomial.C c * MvPolynomial.X i =
        MvPolynomial.monomial (Finsupp.single i 1) c := by
      rw [MvPolynomial.C_mul_X_eq_monomial]
    rw [hmon, qsHomogVerifierValue, MvPolynomial.support_monomial, ite_eq_right hc,
      Finset.sum_singleton, MvPolynomial.coeff_monomial, ite_eq_left rfl,
      Finsupp.sum_single_index rfl, prod_pow_finsupp_single]
    ring

private theorem X_mul_X_eq_monomial {n : ℕ} (a b : Fin n) :
    (MvPolynomial.X a * MvPolynomial.X b : MvPolynomial (Fin n) R) =
      MvPolynomial.monomial (Finsupp.single a 1 + Finsupp.single b 1) 1 := by
  rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]

private theorem sum_single_add_single {n : ℕ} (a b : Fin n) :
    (Finsupp.single a 1 + Finsupp.single b 1 : Fin n →₀ ℕ).sum (fun _ e => e) = 2 := by
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]

private theorem qsHomogVerifierValue_X_mul_X {n : ℕ} (d : ℕ)
    (a b : Fin n) (delta : R) (q' : Fin n → R) :
    qsHomogVerifierValue d (MvPolynomial.X a * MvPolynomial.X b) delta q' =
      q' a * q' b * delta ^ (d - 2) := by
  classical
  by_cases h1 : (1 : R) = 0
  · have hzero : ∀ x : R, x = 0 := fun x => by rw [← one_mul x, h1, zero_mul]
    rw [hzero (qsHomogVerifierValue _ _ _ _), hzero (_ * _ * _)]
  · rw [X_mul_X_eq_monomial, qsHomogVerifierValue, MvPolynomial.support_monomial, ite_eq_right h1,
      Finset.sum_singleton, MvPolynomial.coeff_monomial, ite_eq_left rfl,
      sum_single_add_single, prod_pow_finsupp_pair q' a b, one_mul]
    ring

private theorem qsHomogVerifierValue_mulGatePoly {n : ℕ} (a b c : Fin n)
    (delta : R) (q' : Fin n → R) :
    qsHomogVerifierValue 2 (mulGatePoly a b c) delta q' = q' a * q' b - q' c * delta := by
  rw [mulGatePoly, qsHomogVerifierValue_sub, qsHomogVerifierValue_X_mul_X 2,
    show MvPolynomial.X c = MvPolynomial.C (1 : R) * MvPolynomial.X c by simp,
    qsHomogVerifierValue_C_mul_X 2]
  simp

private theorem qsHomogPoly_mulGatePoly {n : ℕ} (a b c : Fin n) (w v : Fin n → R) :
    qsHomogPoly 2 (mulGatePoly a b c) w v =
      Polynomial.C (w a * w b - w c) * Polynomial.X ^ 2 +
        Polynomial.C (voleMulCrossTerm (w a) (v a) (w b) (v b) (v c)) * Polynomial.X +
        Polynomial.C (voleMulConstTerm (v a) (v b)) := by
  classical
  rw [mulGatePoly, qsHomogPoly_sub, X_mul_X_eq_monomial, qsHomogPoly_monomial,
    sum_single_add_single, prod_pow_finsupp_pair (qsWirePoly w v) a b, MvPolynomial.X,
    qsHomogPoly_monomial, Finsupp.sum_single_index rfl,
    prod_pow_finsupp_single (qsWirePoly w v) c]
  simp only [Nat.sub_self, pow_zero, map_one, one_mul, mul_one,
    show 2 - 1 = 1 by rfl, pow_one, qsWirePoly, voleMulCrossTerm, voleMulConstTerm, map_sub,
    map_add, map_mul]
  ring

private noncomputable def circuitLinearRowPoly {p k m : ℕ}
    (C_circ : Circuit (arithSignature R) (p + k) m) (x : Fin p → R) (y : Fin m → R)
    (row : Fin p ⊕ Fin C_circ.size ⊕ Fin m) : MvPolynomial (Fin ((p + k) + C_circ.size)) R :=
  (∑ j : Fin ((p + k) + C_circ.size),
    MvPolynomial.C (circuitLinearCoeffs C_circ row j) * MvPolynomial.X j) -
    MvPolynomial.C (circuitLinearTargets C_circ x y row)

private noncomputable def circuitConstraintPoly {p k m : ℕ}
    (C_circ : Circuit (arithSignature R) (p + k) m) (x : Fin p → R) (y : Fin m → R) :
    (Fin p ⊕ Fin C_circ.size ⊕ Fin m) ⊕ CircuitMulGate C_circ →
      MvPolynomial (Fin ((p + k) + C_circ.size)) R
  | .inl row => circuitLinearRowPoly C_circ x y row
  | .inr g =>
    mulGatePoly (circuitMulInput C_circ g 0) (circuitMulInput C_circ g 1)
      (circuitMulOutput C_circ g)

private theorem totalDegree_circuitConstraintPoly_le {p k m : ℕ}
    (C_circ : Circuit (arithSignature R) (p + k) m) (x : Fin p → R) (y : Fin m → R)
    (idx : (Fin p ⊕ Fin C_circ.size ⊕ Fin m) ⊕ CircuitMulGate C_circ) :
    (circuitConstraintPoly C_circ x y idx).totalDegree ≤ 2 := by
  rcases idx with row | g
  · rw [circuitConstraintPoly, circuitLinearRowPoly, sub_eq_add_neg]
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
      exact (MvPolynomial.totalDegree_mul _ _).trans <| by
        simpa using (mvTotalDegree_X_le j).trans (by omega)
    · rw [MvPolynomial.totalDegree_neg]
      simp
  · exact totalDegree_mulGatePoly_le _ _ _

private theorem eval_circuitLinearRowPoly {p k m : ℕ}
    (C_circ : Circuit (arithSignature R) (p + k) m) (x : Fin p → R) (y : Fin m → R)
    (row : Fin p ⊕ Fin C_circ.size ⊕ Fin m) (a : Fin ((p + k) + C_circ.size) → R) :
    MvPolynomial.eval a (circuitLinearRowPoly C_circ x y row) =
      (circuitLinearCoeffs C_circ *ᵥ a) row - circuitLinearTargets C_circ x y row := by
  simp [circuitLinearRowPoly, Matrix.mulVec, dotProduct]

private theorem eval_circuitConstraintPoly_circuitTrace {p k m : ℕ}
    (C_circ : Circuit (arithSignature R) (p + k) m) (x : Fin p → R) (w : Fin k → R)
    (y : Fin m → R) (hy : C_circ.eval (arithInterpretation R) (Fin.append x w) = y)
    (idx : (Fin p ⊕ Fin C_circ.size ⊕ Fin m) ⊕ CircuitMulGate C_circ) :
    MvPolynomial.eval (circuitTrace C_circ x w) (circuitConstraintPoly C_circ x y idx) = 0 := by
  rcases idx with row | g
  · rw [circuitConstraintPoly, eval_circuitLinearRowPoly,
      circuitTrace_linear C_circ x w y hy, sub_self]
  · simp [circuitConstraintPoly, mulGatePoly, circuitTrace_mul C_circ x w g]

private theorem exists_witness_of_eval_circuitConstraintPoly_eq_zero {p k m : ℕ}
    (C_circ : Circuit (arithSignature R) (p + k) m) (x : Fin p → R) (y : Fin m → R)
    (a : Fin ((p + k) + C_circ.size) → R)
    (h : ∀ idx, MvPolynomial.eval a (circuitConstraintPoly C_circ x y idx) = 0) :
    ∃ w : Fin k → R, C_circ.eval (arithInterpretation R) (Fin.append x w) = y := by
  refine exists_witness_of_circuitChecks C_circ x y a ?_ ?_
  · funext row
    have hr := h (.inl row)
    rw [circuitConstraintPoly, eval_circuitLinearRowPoly, sub_eq_zero] at hr
    exact hr
  · intro g
    have hg := h (.inr g)
    simp only [circuitConstraintPoly, mulGatePoly, map_sub, map_mul, MvPolynomial.eval_X,
      sub_eq_zero] at hg
    exact hg

private def boolToChar2 (b : Bool) : R :=
  if b then 1 else 0

private theorem boolToChar2_xor [CharP R 2] (a b : Bool) :
    boolToChar2 (R := R) (a != b) = boolToChar2 a + boolToChar2 b := by
  cases a <;> cases b <;> simp [boolToChar2]
  have h2 : (2 : R) = 0 := (CharP.cast_eq_zero_iff R 2 2).mpr (dvd_refl 2)
  simpa only [one_add_one_eq_two] using h2.symm

private theorem boolToChar2_and (a b : Bool) :
    boolToChar2 (R := R) (a && b) = boolToChar2 a * boolToChar2 b := by
  cases a <;> cases b <;> simp [boolToChar2]

private def faestConversionVOLE {depth outputLength : ℕ}
    (rows : Fin (2 ^ depth) → BitString outputLength) (delta : Fin (2 ^ depth))
    (beta : Fin depth → R) :
    VOLECorrelation R outputLength where
  u i := boolToChar2 ((convertExpandedRows depth rows).u i)
  v i := ∑ j : Fin depth, boolToChar2 ((convertExpandedRows depth rows).columns j i) * beta j
  delta := ∑ j : Fin depth, boolToChar2 ((BitString.equivFin depth).symm delta j) * beta j
  w i := ∑ j : Fin depth,
    boolToChar2 ((convertExpandedRows depth (verifierRows rows delta)).columns j i) * beta j

private theorem faestConversionVOLE_valid [CharP R 2] {depth outputLength : ℕ}
    (rows : Fin (2 ^ depth) → BitString outputLength) (delta : Fin (2 ^ depth))
    (beta : Fin depth → R) :
    (faestConversionVOLE rows delta beta).Valid := by
  intro i
  simp only [faestConversionVOLE, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hvalid := conversionCorrelation_valid rows delta j i
  change boolToChar2 ((conversionCorrelation rows delta j).w i) * beta j = _
  rw [hvalid]
  have hadd :
      (conversionCorrelation rows delta j).u i * (conversionCorrelation rows delta j).delta +
        (conversionCorrelation rows delta j).v i =
      (((conversionCorrelation rows delta j).u i &&
        (conversionCorrelation rows delta j).delta) !=
        (conversionCorrelation rows delta j).v i) := by
    cases (conversionCorrelation rows delta j).u i <;>
      cases (conversionCorrelation rows delta j).delta <;>
      cases (conversionCorrelation rows delta j).v i <;> rfl
  rw [hadd, boolToChar2_xor, boolToChar2_and]
  simp only [conversionCorrelation, add_mul, mul_assoc]

private theorem faestConversionVOLE_u_binary {depth outputLength : ℕ}
    (rows : Fin (2 ^ depth) → BitString outputLength) (delta : Fin (2 ^ depth))
    (beta : Fin depth → R) (i : Fin outputLength) :
    (faestConversionVOLE rows delta beta).u i = 0 ∨
      (faestConversionVOLE rows delta beta).u i = 1 := by
  cases h : (convertExpandedRows depth rows).u i <;> simp [faestConversionVOLE, boolToChar2, h]

end Bridges

example (w v : Fin 3 → ZMod 5) (q' : Fin 3 → ZMod 5) (delta : ZMod 5) :
    qsHomogVerifierValue 2 (mulGatePoly 0 1 2) delta q' = q' 0 * q' 1 - q' 2 * delta ∧
      qsHomogPoly 2 (mulGatePoly 0 1 2) w v =
        Polynomial.C (w 0 * w 1 - w 2) * Polynomial.X ^ 2 +
          Polynomial.C (voleMulCrossTerm (w 0) (v 0) (w 1) (v 1) (v 2)) * Polynomial.X +
          Polynomial.C (voleMulConstTerm (v 0) (v 1)) :=
  ⟨qsHomogVerifierValue_mulGatePoly 0 1 2 delta q', qsHomogPoly_mulGatePoly 0 1 2 w v⟩

private def sqCirc : Circuit (arithSignature (ZMod 5)) (1 + 0) 1 :=
  Circuit.oneGate .mul (fun _ => 0)

example :
    (∀ idx, (circuitConstraintPoly sqCirc ![2] ![4] idx).totalDegree ≤ 2) ∧
      (∀ idx, MvPolynomial.eval (circuitTrace sqCirc ![2] Fin.elim0)
        (circuitConstraintPoly sqCirc ![2] ![4] idx) = 0) ∧
      ∃ w : Fin 0 → ZMod 5,
        sqCirc.eval (arithInterpretation (ZMod 5)) (Fin.append ![2] w) = ![4] := by
  have heval : sqCirc.eval (arithInterpretation (ZMod 5)) (Fin.append ![2] Fin.elim0) = ![4] := by
    funext i
    fin_cases i
    change (2 : ZMod 5) * 2 = 4
    decide
  have hvanish : ∀ idx, MvPolynomial.eval (circuitTrace sqCirc ![2] Fin.elim0)
      (circuitConstraintPoly sqCirc ![2] ![4] idx) = 0 :=
    eval_circuitConstraintPoly_circuitTrace sqCirc ![2] Fin.elim0 ![4] heval
  exact ⟨fun idx => totalDegree_circuitConstraintPoly_le sqCirc ![2] ![4] idx, hvanish,
    exists_witness_of_eval_circuitConstraintPoly_eq_zero sqCirc ![2] ![4]
      (circuitTrace sqCirc ![2] Fin.elim0) hvanish⟩

private def convRows : Fin (2 ^ 2) → BitString 3 :=
  ![![true, false, false],
    ![false, true, false],
    ![false, false, true],
    ![true, true, false]]

private def convHidden : Fin (2 ^ 2) := ⟨3, by decide⟩

example (beta : Fin 2 → ZMod 2) :
    (faestConversionVOLE (R := ZMod 2) convRows convHidden beta).Valid ∧
      ∀ j : Fin 3,
        (faestConversionVOLE (R := ZMod 2) convRows convHidden beta).u j = 0 ∨
        (faestConversionVOLE (R := ZMod 2) convRows convHidden beta).u j = 1 :=
  ⟨faestConversionVOLE_valid convRows convHidden beta,
    fun j => faestConversionVOLE_u_binary convRows convHidden beta j⟩

example {R : Type} [CommRing R] [CharP R 2] (beta : Fin 2 → R) :
    (faestConversionVOLE (R := R) convRows convHidden beta).Valid :=
  faestConversionVOLE_valid convRows convHidden beta

/-! ### ACT Spend Parameter Checks and Domain Separation -/

-- ACT Spend uses degree 9 ∉ {7, 14}, exceeding FAEST v3.0 Lemma 10.40's {7, 14} hypothesis.
example : actSpendDegree ∉ ({7, 14} : Finset ℕ) := by decide

/-- Full 7-byte domain separation tag `"rata\x00l0"` defining `ACT_SPEND_COMBINE_DST` in
[VoleMole2026] (`src/dst.hpp:44`; invoked at `src/act/spend.hpp:383`). -/
private def actSpendCombineDst : List (Fin 256) := [0x72, 0x61, 0x74, 0x61, 0x00, 0x6c, 0x30]

example :
    actRLCDomainByte ∉ faestTrailingDomainBytes ∧
      actSpendCombineDst.getLast? = some actRLCDomainByte ∧
      Disjoint (Set.range (appendDomainByteFin (n := 4) actRLCDomainByte))
        (Set.range (appendFaestDomainByteFin (n := 4))) :=
  ⟨actRLCDomainByte_notMem_faest, by decide, disjoint_range_actRLC_faestDomainByteFin 4⟩

example :
    (PMF.uniformOfFintype (Fin 4 → Bool)).map
        (fun H => (fun k₁ : Fin 2 => H (Fin.castLE (by decide) k₁),
          fun k₂ : Fin 2 => H ⟨k₂.val + 2, by omega⟩)) =
      (PMF.uniformOfFintype (Fin 2 → Bool)).bind fun H₁ =>
        (PMF.uniformOfFintype (Fin 2 → Bool)).map fun H₂ => (H₁, H₂) := by
  let ι₁ : Fin 2 ↪ Fin 4 :=
    ⟨Fin.castLE (by decide), fun a b h => Fin.ext (by
      have hv := congrArg Fin.val h
      simpa only [Fin.val_castLE] using hv)⟩
  let ι₂ : Fin 2 ↪ Fin 4 := ⟨fun k => ⟨k.val + 2, by omega⟩, fun a b h => by
    ext
    have := congrArg Fin.val h
    dsimp only at this
    omega⟩
  refine uniform_split_of_disjoint_range ι₁ ι₂ ?_
  rw [Set.disjoint_left]
  rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
  have h1 : (ι₁ a).val < 2 := a.isLt
  have h2 : (ι₂ b).val = b.val + 2 := rfl
  have hval := congrArg Fin.val hb
  rw [hval] at h2
  omega

/-! ### ACT V1 RLC (`m = 45`), Single-RO Domain Separation, Round-2+3, and Negative Boundaries -/

private theorem qsPolySum_zero {R : Type} [CommRing R] (d : ℕ) (x : R) :
    qsPolySum d 0 x = 0 := by
  simp [qsPolySum]

-- Concrete single-RO FAEST / `vole-mole` (`H_0` + `H_2^4`) domain-separated QuickSilver check
-- against `H : ByteMsg 2 → Fin 2 → ZMod 17`, querying `H_0` (`b = 0`) at zero ACT budget and
-- ACT's `0x30` table once (`cost = 1`), exercising
-- `toOuterMeasure_actV1_domainSeparated_qs_of_zkBinding_le` and
-- `disjoint_range_actRLC_faestDomainByteFin`.
private noncomputable def singleROMixedAdversary :
    ProbOracleComp
      ((fun _ : ByteMsg 1 => Fin 2 → ZMod 17) ⊕ₒ (fun _ : FaestTaggedMsg 1 => Fin 2 → ZMod 17))
      (Fin 2 → ZMod 17) := do
  let h0 ← ProbOracleComp.query (.inr ((fun _ => 0), ⟨0, by decide⟩))
  let act ← ProbOracleComp.query (.inl (fun _ => 0))
  return ![1, h0 0 + act 0]

example :
    OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0)))
        singleROMixedAdversary 1 ∧
      (do
        let H ← PMF.uniformOfFintype (ByteMsg 2 → Fin 2 → ZMod 17)
        let s ← OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle
            (OracleComp.sumHandler
              (fun msg => PMF.pure (H (appendDomainByteFin actRLCDomainByte msg)))
              (fun p => PMF.pure (H (appendFaestDomainByteFin p))))) singleROMixedAdversary
        let k ← PMF.uniformOfFintype (ByteMsg 1)
        let l := H (appendDomainByteFin actRLCDomainByte k)
        let c ← PMF.uniformOfFintype (ZMod 17)
        let P : Fin 2 → Polynomial (ZMod 17) :=
          fun j => Polynomial.C (s j) * Polynomial.X ^ actSpendDegree
        let Q : Polynomial (ZMod 17) :=
          if k = (fun _ => 0) then 0 else foldedConstraint P l
        return decide ((∃ j, (P j).coeff actSpendDegree ≠ 0) ∧ True ∧ Q.eval c = 0)).toOuterMeasure
          {true} ≤
      1 * (1 / (256 : ℝ≥0∞)) + ((17 : ℝ≥0∞)⁻¹ +
        (1 - (17 : ℝ≥0∞)⁻¹) * (1 / (256 : ℝ≥0∞) + 9 / (17 : ℝ≥0∞))) := by
  have hq : OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0)))
      singleROMixedAdversary 1 := by
    unfold singleROMixedAdversary
    have hfaest := ProbOracleComp.isCostBounded_query
      (spec := (fun _ : ByteMsg 1 => Fin 2 → ZMod 17) ⊕ₒ
        (fun _ : FaestTaggedMsg 1 => Fin 2 → ZMod 17))
      (Sum.elim (fun _ => 1) (fun _ => 0)) (.inr ((fun _ => 0), ⟨0, by decide⟩))
    have hact := ProbOracleComp.isCostBounded_query
      (spec := (fun _ : ByteMsg 1 => Fin 2 → ZMod 17) ⊕ₒ
        (fun _ : FaestTaggedMsg 1 => Fin 2 → ZMod 17))
      (Sum.elim (fun _ => 1) (fun _ => 0)) (.inl (fun _ => 0))
    simpa only [Sum.elim_inr, Sum.elim_inl, Nat.zero_add, Nat.add_zero] using
      hfaest.bind fun _ => hact.bind fun _ => OracleComp.IsCostBounded.pure _ 0
  refine ⟨hq, ?_⟩
  let P : (Fin 2 → ZMod 17) → Fin 2 → Polynomial (ZMod 17) :=
    fun s j => Polynomial.C (s j) * Polynomial.X ^ actSpendDegree
  let Q : (Fin 2 → ZMod 17) → ByteMsg 1 → (Fin 2 → ZMod 17) → Polynomial (ZMod 17) :=
    fun s k l => if k = (fun _ => 0) then 0 else foldedConstraint (P s) l
  have hdegQ : ∀ s k l, (Q s k l).natDegree ≤ actSpendDegree := fun s k l => by
    dsimp only [Q]
    split_ifs
    · simp
    · exact natDegree_foldedConstraint_le (fun j =>
        (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le _)) l
  have hdist : ∀ k₀ : ByteMsg 1, PMF.uniformOfFintype (ByteMsg 1) k₀ ≤ 1 / (256 : ℝ≥0∞) := by
    intro _
    simp [PMF.uniformOfFintype_apply, one_div]
  have h := toOuterMeasure_actV1_domainSeparated_qs_of_zkBinding_le
    (appendDomainByteFin actRLCDomainByte) appendFaestDomainByteFin
    (disjoint_range_actRLC_faestDomainByteFin 1) (Function.Embedding.refl (ZMod 17))
    singleROMixedAdversary hq (PMF.uniformOfFintype (ByteMsg 1)) hdist P Q hdegQ
    (fun _ _ _ => 0) (fun _ _ _ => True) (ε_zk := 1 / (256 : ℝ≥0∞)) (fun s l hl => by
      have hsub : {k : ByteMsg 1 | True ∧ (Q s k l).coeff actSpendDegree = 0} ⊆
          {fun _ => 0} := by
        intro k hk
        by_contra hne
        have hne' : k ≠ (fun _ => 0) := Set.mem_singleton_iff.not.mp hne
        have hmem := (Set.mem_ofPred_eq.mp hk).2
        have hqeq : Q s k l = foldedConstraint (P s) l := by
          dsimp only [Q]
          rw [ite_eq_right_iff.mpr fun h0 => (hne' h0).elim]
        rw [hqeq] at hmem
        exact hl hmem
      refine (MeasureTheory.measure_mono hsub).trans_eq ?_
      rw [PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply, Fintype.card_fun,
        Fintype.card_fin 1, pow_one, one_div]
      norm_num)
  simp only [Function.Embedding.refl_apply, qsPolySum_zero] at h
  have hrhs : (1 : ℝ≥0∞) * (1 / (256 : ℝ≥0∞)) + ((Fintype.card (ZMod 17) : ℝ≥0∞)⁻¹ +
      (1 - (Fintype.card (ZMod 17) : ℝ≥0∞)⁻¹) *
        (1 / (256 : ℝ≥0∞) + (actSpendDegree : ℝ≥0∞) / (Fintype.card (ZMod 17) : ℝ≥0∞))) =
      1 * (1 / (256 : ℝ≥0∞)) + ((17 : ℝ≥0∞)⁻¹ +
        (1 - (17 : ℝ≥0∞)⁻¹) * (1 / (256 : ℝ≥0∞) + 9 / (17 : ℝ≥0∞))) := by
    rw [ZMod.card, show actSpendDegree = 9 from rfl]
    norm_num
  rw [Nat.cast_one] at h
  exact h.trans_eq hrhs

-- Concrete degree-9 folded QuickSilver polynomial family (`P j = X^9 - 1` at `j = 0`, `0` else)
-- exercising `natDegree_foldedConstraint_le`, unconditional `toOuterMeasure_actV1_foldedQS_le`,
-- and `toOuterMeasure_actV1_qs_of_zkBinding_le` (linking `Q` genuinely to `foldedConstraint`).
private noncomputable def spendRLCPolys : Fin actSpendRLCCount → Polynomial (ZMod 17) :=
  fun j => if j = 0 then Polynomial.X ^ actSpendDegree - 1 else 0

private theorem natDegree_spendRLCPolys (j : Fin actSpendRLCCount) :
    (spendRLCPolys j).natDegree ≤ actSpendDegree := by
  unfold spendRLCPolys
  split_ifs
  · exact (Polynomial.natDegree_sub_le _ _).trans (max_le (Polynomial.natDegree_X_pow_le _)
      (by simp))
  · simp

private theorem foldedConstraint_spendRLCPolys_coeff9 (l : Fin actSpendRLCCount → ZMod 17) :
    (foldedConstraint spendRLCPolys l).coeff actSpendDegree = l 0 := by
  rw [coeff_foldedConstraint, Finset.sum_eq_single 0]
  · simp [spendRLCPolys, actSpendDegree, Polynomial.coeff_one]
  · intro j _ hj
    simp [spendRLCPolys, hj]
  · simp

example (l : Fin actSpendRLCCount → ZMod 17) :
    (foldedConstraint spendRLCPolys l).natDegree ≤ actSpendDegree ∧
      (foldedConstraint spendRLCPolys l).coeff actSpendDegree = l 0 :=
  ⟨natDegree_foldedConstraint_le natDegree_spendRLCPolys l,
    foldedConstraint_spendRLCPolys_coeff9 l⟩

private noncomputable def qsQuery0Adversary :
    ProbOracleComp (fun _ : Fin 64 => Fin actSpendRLCCount → ZMod 17) Unit := do
  let _ ← ProbOracleComp.query 0
  return ()

private theorem isQueryBounded_qsQuery0 :
    ProbOracleComp.IsQueryBounded qsQuery0Adversary 1 := by
  unfold qsQuery0Adversary
  simpa only [Nat.add_zero] using
    (ProbOracleComp.IsQueryBounded.query
      (spec := fun _ : Fin 64 => Fin actSpendRLCCount → ZMod 17) 0).bind fun _ =>
      OracleComp.IsCostBounded.pure _ 0

example :
    (do
      let H ← PMF.uniformOfFintype (Fin 64 → Fin actSpendRLCCount → ZMod 17)
      let _ ← OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle (fun k => PMF.pure (H k)))
        qsQuery0Adversary
      let k ← PMF.uniformOfFintype (Fin 64)
      let l := H k
      let c ← PMF.uniformOfFintype (ZMod 17)
      return decide ((∃ j, (spendRLCPolys j).coeff actSpendDegree ≠ 0) ∧
        (foldedConstraint spendRLCPolys l).eval c = 0)).toOuterMeasure {true} ≤
      1 * (1 / (64 : ℝ≥0∞)) + ((17 : ℝ≥0∞)⁻¹ +
        (1 - (17 : ℝ≥0∞)⁻¹) * (9 / (17 : ℝ≥0∞))) := by
  have hdist : ∀ k₀ : Fin 64, PMF.uniformOfFintype (Fin 64) k₀ ≤ 1 / (64 : ℝ≥0∞) := fun _ => by
    simp [PMF.uniformOfFintype_apply, one_div]
  have h := toOuterMeasure_actV1_foldedQS_le (Function.Embedding.refl (ZMod 17))
    qsQuery0Adversary isQueryBounded_qsQuery0 (PMF.uniformOfFintype (Fin 64)) hdist
    (fun _ => spendRLCPolys) (fun _ => natDegree_spendRLCPolys) (fun _ _ _ => 0)
  simp only [Function.Embedding.refl_apply, qsPolySum_zero] at h
  have hrhs : (1 : ℝ≥0∞) * (1 / (64 : ℝ≥0∞)) + ((Fintype.card (ZMod 17) : ℝ≥0∞)⁻¹ +
      (1 - (Fintype.card (ZMod 17) : ℝ≥0∞)⁻¹) *
        ((actSpendDegree : ℝ≥0∞) / (Fintype.card (ZMod 17) : ℝ≥0∞))) =
      1 * (1 / (64 : ℝ≥0∞)) + ((17 : ℝ≥0∞)⁻¹ + (1 - (17 : ℝ≥0∞)⁻¹) * (9 / (17 : ℝ≥0∞))) := by
    rw [ZMod.card, show actSpendDegree = 9 from rfl]
    norm_num
  rw [Nat.cast_one] at h
  exact h.trans_eq hrhs

private noncomputable def spendRLCQ :
    Unit → Fin 64 → (Fin actSpendRLCCount → ZMod 17) → Polynomial (ZMod 17) :=
  fun _ k l => if k = 0 then 0 else foldedConstraint spendRLCPolys l

private theorem spendRLCQ_ne_zero (k : Fin 64) (hk : k ≠ 0)
    (l : Fin actSpendRLCCount → ZMod 17) :
    spendRLCQ () k l = foldedConstraint spendRLCPolys l := by
  dsimp only [spendRLCQ]
  rw [ite_eq_right_iff.mpr fun h0 => (hk h0).elim]

example :
    (do
      let H ← PMF.uniformOfFintype (Fin 64 → Fin actSpendRLCCount → ZMod 17)
      let s ← OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle (fun k => PMF.pure (H k)))
        qsQuery0Adversary
      let k ← PMF.uniformOfFintype (Fin 64)
      let l := H k
      let c ← PMF.uniformOfFintype (ZMod 17)
      return decide ((∃ j, (spendRLCPolys j).coeff actSpendDegree ≠ 0) ∧ True ∧
        (spendRLCQ s k l).eval c = 0)).toOuterMeasure {true} ≤
      1 * (1 / (64 : ℝ≥0∞)) + ((17 : ℝ≥0∞)⁻¹ +
        (1 - (17 : ℝ≥0∞)⁻¹) * (1 / (64 : ℝ≥0∞) + 9 / (17 : ℝ≥0∞))) := by
  have hdegQ : ∀ s k l, (spendRLCQ s k l).natDegree ≤ actSpendDegree := fun _ k l => by
    dsimp only [spendRLCQ]
    split_ifs
    · simp
    · exact natDegree_foldedConstraint_le natDegree_spendRLCPolys l
  have hdist : ∀ k₀ : Fin 64, PMF.uniformOfFintype (Fin 64) k₀ ≤ 1 / (64 : ℝ≥0∞) := fun _ => by
    simp [PMF.uniformOfFintype_apply, one_div]
  have h := toOuterMeasure_actV1_qs_of_zkBinding_le (Function.Embedding.refl (ZMod 17))
    qsQuery0Adversary isQueryBounded_qsQuery0 (PMF.uniformOfFintype (Fin 64)) hdist
    (fun _ => spendRLCPolys) spendRLCQ hdegQ (fun _ _ _ => 0) (fun _ _ _ => True)
    (ε_zk := 1 / (64 : ℝ≥0∞)) (fun s l hl => by
      cases s
      have hsub : {k : Fin 64 | True ∧ (spendRLCQ () k l).coeff actSpendDegree = 0} ⊆ {0} := by
        intro k hk
        by_contra hne
        have hne' : k ≠ 0 := Set.mem_singleton_iff.not.mp hne
        have hmem := (Set.mem_ofPred_eq.mp hk).2
        rw [spendRLCQ_ne_zero k hne' l, foldedConstraint_spendRLCPolys_coeff9] at hmem
        rw [coeff_foldedConstraint] at hl
        rw [Finset.sum_eq_single 0] at hl
        · have hl' : l 0 * (spendRLCPolys 0).coeff actSpendDegree ≠ 0 := hl
          have hc9 : (spendRLCPolys 0).coeff actSpendDegree = 1 := by
            simp [spendRLCPolys, actSpendDegree, Polynomial.coeff_one]
          rw [hc9, mul_one] at hl'
          exact hl' hmem
        · intro j _ hj
          simp [spendRLCPolys, hj]
        · exact fun h0 => absurd (Finset.mem_univ 0) h0
      refine (MeasureTheory.measure_mono hsub).trans_eq ?_
      rw [PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply, Fintype.card_fin,
        one_div]
      norm_num)
  simp only [Function.Embedding.refl_apply, qsPolySum_zero] at h
  have hrhs : (1 : ℝ≥0∞) * (1 / (64 : ℝ≥0∞)) + ((Fintype.card (ZMod 17) : ℝ≥0∞)⁻¹ +
      (1 - (Fintype.card (ZMod 17) : ℝ≥0∞)⁻¹) *
        (1 / (64 : ℝ≥0∞) + (actSpendDegree : ℝ≥0∞) / (Fintype.card (ZMod 17) : ℝ≥0∞))) =
      1 * (1 / (64 : ℝ≥0∞)) + ((17 : ℝ≥0∞)⁻¹ +
        (1 - (17 : ℝ≥0∞)⁻¹) * (1 / (64 : ℝ≥0∞) + 9 / (17 : ℝ≥0∞))) := by
    rw [ZMod.card, show actSpendDegree = 9 from rfl]
    norm_num
  rw [Nat.cast_one] at h
  exact h.trans_eq hrhs

-- Negative test 3a (omitting domain separation):
-- (1) Reading the SAME random oracle `H` does not yield an independent pair `(H₁, H₂)`.
-- (2) If the FAEST side uses the SAME trailing byte `0` as ACT (`b₁ = b₂ = 0`), a single query
--     through the other slice (`cost = 0` on ACT's budget) leaks `l = H_all (snoc k 0)` and
--     cancels `foldedResidual = 0` on 100% of runs.
example :
    (PMF.uniformOfFintype (Bool → Bool)).map (fun H => (H, H)) ≠
      (PMF.uniformOfFintype (Bool → Bool)).bind fun H₁ =>
        (PMF.uniformOfFintype (Bool → Bool)).map fun H₂ => (H₁, H₂) := by
  intro heq
  let badPair : (Bool → Bool) × (Bool → Bool) := (fun _ => false, fun _ => true)
  have h1 : ((PMF.uniformOfFintype (Bool → Bool)).map (fun H => (H, H))) badPair = 0 := by
    simp only [PMF.map_apply, tsum_eq_zero_iff]
    intro H
    by_cases hH : badPair = (H, H)
    · have h0 : H false = false := (congrFun (congrArg Prod.fst hH) false).symm
      have h1' : H false = true := (congrFun (congrArg Prod.snd hH) false).symm
      exact False.elim (Bool.false_ne_true (h0.symm.trans h1'))
    · simp [hH]
  have h2 : ((PMF.uniformOfFintype (Bool → Bool)).bind fun H₁ =>
      (PMF.uniformOfFintype (Bool → Bool)).map fun H₂ => (H₁, H₂)) badPair ≠ 0 := by
    rw [← PMF.mem_support_iff, PMF.mem_support_bind_iff]
    refine ⟨fun _ => false, PMF.mem_support_uniformOfFintype _, ?_⟩
    rw [PMF.mem_support_map_iff]
    exact ⟨fun _ => true, PMF.mem_support_uniformOfFintype _, rfl⟩
  rw [heq] at h1
  exact h2 h1

private def foldedResidual {F : Type} [CommRing F] {m : ℕ}
    (lhs rhs : Fin m → F) (l : Fin m → F) : F :=
  ∑ j : Fin m, l j * (lhs j - rhs j)

private noncomputable def collidingByteAdversary :
    ProbOracleComp
      ((fun _ : ByteMsg 0 => Fin 2 → ZMod 11) ⊕ₒ (fun _ : ByteMsg 0 => Fin 2 → ZMod 11))
      (Fin 2 → ZMod 11) := do
  let l ← ProbOracleComp.query (.inr Fin.elim0)
  return if l = 0 then ![1, 0] else ![l 1, -l 0]

example :
    OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0)))
        collidingByteAdversary 0 ∧
      (do
        let H ← PMF.uniformOfFintype (ByteMsg 1 → Fin 2 → ZMod 11)
        let res ← OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle
            (OracleComp.sumHandler (fun msg => PMF.pure (H (appendDomainByteFin 0 msg)))
              (fun msg => PMF.pure (H (appendDomainByteFin 0 msg))))) collidingByteAdversary
        let k ← PMF.uniformOfFintype (ByteMsg 0)
        return decide ((∃ j, res j ≠ 0) ∧
          foldedResidual res 0 (H (appendDomainByteFin 0 k)) = 0)).toOuterMeasure {true} = 1 := by
  constructor
  · unfold collidingByteAdversary
    have hfaest := ProbOracleComp.isCostBounded_query
      (spec := (fun _ : ByteMsg 0 => Fin 2 → ZMod 11) ⊕ₒ (fun _ : ByteMsg 0 => Fin 2 → ZMod 11))
      (Sum.elim (fun _ => 1) (fun _ => 0)) (.inr (Fin.elim0 : ByteMsg 0))
    simpa only [Sum.elim_inr, Nat.zero_add] using
      hfaest.bind fun _ => OracleComp.IsCostBounded.pure _ 0
  · have htrue : ∀ l : Fin 2 → ZMod 11,
        (∃ j : Fin 2, (if l = 0 then ![1, 0] else ![l 1, -l 0]) j ≠ 0) ∧
        foldedResidual (if l = 0 then ![1, 0] else ![l 1, -l 0]) 0 l = 0 := by
      intro l
      by_cases h0 : l = 0
      · simp [h0, foldedResidual]
      · constructor
        · by_contra hzero
          push Not at hzero
          have hj0 := hzero 0
          have hj1 := hzero 1
          simp only [h0, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one,
            neg_eq_zero] at hj0 hj1
          apply h0
          ext j
          fin_cases j <;> simp [hj1, hj0]
        · simp only [h0, ↓reduceIte, foldedResidual, Fin.sum_univ_two, Pi.zero_apply, sub_zero,
            Matrix.cons_val_zero, Matrix.cons_val_one]
          ring
    have heval :
        (do
          let H ← PMF.uniformOfFintype (ByteMsg 1 → Fin 2 → ZMod 11)
          let res ← OracleComp.interpret
            (OracleComp.sumHandler ProbComp.unifOracle
              (OracleComp.sumHandler (fun msg => PMF.pure (H (appendDomainByteFin 0 msg)))
                (fun msg => PMF.pure (H (appendDomainByteFin 0 msg))))) collidingByteAdversary
          let k ← PMF.uniformOfFintype (ByteMsg 0)
          return decide ((∃ j, res j ≠ 0) ∧
            foldedResidual res 0 (H (appendDomainByteFin 0 k)) = 0)) = PMF.pure true := by
      simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, collidingByteAdversary,
        OracleComp.interpret_bind, ProbOracleComp.interpret_query, OracleComp.sumHandler,
        OracleComp.interpret_pure, PMF.pure_bind]
      trans ((PMF.uniformOfFintype (ByteMsg 1 → Fin 2 → ZMod 11)).bind fun _ => PMF.pure true)
      · congr 1 with H : 1
        trans ((PMF.uniformOfFintype (ByteMsg 0)).bind fun _ => PMF.pure true)
        · congr 1 with k : 1
          have hk : k = Fin.elim0 := Subsingleton.elim k Fin.elim0
          rw [hk]
          exact congrArg PMF.pure (decide_eq_true (htrue (H (appendDomainByteFin 0 Fin.elim0))))
        · simp [PMF.bind_const]
      · simp [PMF.bind_const]
    rw [heval]
    simp

-- Negative test 3b (`q * δ_K` tightness for predictable challenge `K = Unit`):
-- querying `H ()` (`1` query, `δ_K = 1`) before committing forces `foldedResidual = 0` with
-- probability `1`, matching `q * δ_K = 1 * 1` in `toOuterMeasure_actV1_qs_of_zkBinding_le`.
private noncomputable def adaptiveCancelAdversary :
    ProbOracleComp (fun _ : Unit => Fin 2 → ZMod 11) (Fin 2 → ZMod 11) := do
  let l ← ProbOracleComp.query ()
  return if l = 0 then ![1, 0] else ![l 1, -l 0]

example :
    ProbOracleComp.IsQueryBounded adaptiveCancelAdversary 1 ∧
      (do
        let H ← PMF.uniformOfFintype (Unit → Fin 2 → ZMod 11)
        let res ← OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle (fun k => PMF.pure (H k)))
          adaptiveCancelAdversary
        let k ← PMF.uniformOfFintype Unit
        return decide ((∃ j, res j ≠ 0) ∧
          foldedResidual res 0 (H k) = 0)).toOuterMeasure {true} = 1 := by
  constructor
  · unfold adaptiveCancelAdversary
    simpa only [Nat.add_zero] using
      (ProbOracleComp.IsQueryBounded.query (spec := fun _ : Unit => Fin 2 → ZMod 11) ()).bind
        fun _ => OracleComp.IsCostBounded.pure _ 0
  · have htrue : ∀ H : Unit → Fin 2 → ZMod 11,
        (∃ j : Fin 2, (if H () = 0 then ![1, 0] else ![H () 1, -H () 0]) j ≠ 0) ∧
        foldedResidual (if H () = 0 then ![1, 0] else ![H () 1, -H () 0]) 0 (H ()) = 0 := by
      intro H
      by_cases h0 : H () = 0
      · simp [h0, foldedResidual]
      · constructor
        · by_contra hzero
          push Not at hzero
          have hj0 := hzero 0
          have hj1 := hzero 1
          simp only [h0, ↓reduceIte, Matrix.cons_val_zero, Matrix.cons_val_one,
            neg_eq_zero] at hj0 hj1
          apply h0
          ext j
          fin_cases j <;> simp [hj1, hj0]
        · simp only [h0, ↓reduceIte, foldedResidual, Fin.sum_univ_two, Pi.zero_apply, sub_zero,
            Matrix.cons_val_zero, Matrix.cons_val_one]
          ring
    have hH (H : Unit → Fin 2 → ZMod 11) :
        OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle (fun k => PMF.pure (H k)))
          adaptiveCancelAdversary =
          PMF.pure (if H () = 0 then ![1, 0] else ![H () 1, -H () 0]) := by
      simp [adaptiveCancelAdversary]
    have heval : (do
        let H ← PMF.uniformOfFintype (Unit → Fin 2 → ZMod 11)
        let res ← OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle (fun k => PMF.pure (H k)))
          adaptiveCancelAdversary
        let k ← PMF.uniformOfFintype Unit
        return decide ((∃ j, res j ≠ 0) ∧ foldedResidual res 0 (H k) = 0)) =
        PMF.pure true := by
      simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, hH, PMF.pure_bind]
      trans ((PMF.uniformOfFintype (Unit → Fin 2 → ZMod 11)).bind fun _ => PMF.pure true)
      · congr 1 with H : 1
        trans ((PMF.uniformOfFintype Unit).bind fun _ => PMF.pure true)
        · congr 1 with k : 1
          cases k
          exact congrArg PMF.pure (decide_eq_true (htrue H))
        · simp [PMF.bind_const]
      · simp [PMF.bind_const]
    rw [heval]
    simp

-- Negative test 4 (small challenge field in ACT V1 RLC): over `ZMod 2`, random linear combination
-- cancellation probability is `1 / 2`, while at degree `actSpendDegree = 9` the `d / |F|` term is
-- `9 / 2 ≥ 1`, making the Round-2+3 bound vacuous (`≥ 1`).
example :
    (PMF.uniformOfFintype (Fin 2 → ZMod 2)).toOuterMeasure
        {l | foldedResidual ![1, 0] ![0, 0] l = 0} = 1 / (2 : ℝ≥0∞) ∧
      1 ≤ (actSpendDegree : ℝ≥0∞) / (Fintype.card (ZMod 2) : ℝ≥0∞) := by
  constructor
  · rw [PMF.toOuterMeasure_uniformOfFintype, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have hcard : ({l | l ∈ {l : Fin 2 → ZMod 2 | foldedResidual ![1, 0] ![0, 0] l = 0}} :
        Finset (Fin 2 → ZMod 2)).card = 2 := by
      decide
    rw [hcard, show ((2 ^ 2 : ℕ) : ℝ≥0∞) = 2 * 2 by norm_num,
      ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
      ← mul_assoc]
    simp only [Nat.cast_ofNat]
    rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul, one_div]
  · rw [ZMod.card, actSpendDegree, ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
      (Or.inl (by norm_num))]
    norm_num

end CslibFrontierTests.Crypto.VOLEHigherDegreeCheck
