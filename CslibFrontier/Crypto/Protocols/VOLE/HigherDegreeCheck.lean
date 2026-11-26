/-
Copyright (c) 2026 Samuel Schlesinger, Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Interactive.Security
public import CslibFrontier.Computability.Interactive.ThreeMove
public import CslibFrontier.Crypto.Protocols.FAEST.Challenge
public import CslibFrontier.Crypto.Protocols.VOLE.Basic
public import CslibFrontier.Crypto.Protocols.VOLE.ScalarMulCheck
public import CslibFrontier.Crypto.Protocols.VOLE.World
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.RandomOracle
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
import CslibFrontier.Probability.LinearCombination
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.PolynomialAgreement
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformBound
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.UniformRelabel
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Card

/-!
# Arbitrary-degree QuickSilver VOLE checks and ACT V1 challenge-dependent batching

This module formalizes QuickSilver / VOLE-IT-MAC polynomial constraint checks of arbitrary degree
`d ≥ 1` over a finite field or commutative ring, full honest-receiver view zero-knowledge via
`(d - 1)` VOLE masks, independent-weight and scalar-power batching soundness over arbitrary
challenge embeddings (including single-shot FAEST grinding subsets), and the ACT V1 domain-separated
random linear combination (`l = H(chal2 || domain)`) check in the random oracle model.

For a multivariate constraint `F_poly` of total degree at most `d` evaluated on VOLE-authenticated
wires `ρ_i(X) = v_i + w_i * X`, homogenizing every monomial of total degree `deg ≤ d` by
`X ^ (d - deg)` yields a univariate polynomial `qsHomogPoly d F_poly w v` of degree at most `d`
whose degree-`d` coefficient is `MvPolynomial.eval w F_poly`. Adding `(d - 1)` fresh VOLE
mask correlations `(u_m, v_m, q_m)` blinds the lower `d` coefficients via the telescoping
QuickSilver mask coefficients `qsMaskCoeff` so the entire honest receiver view is perfectly
simulatable for all `d ≥ 1` over arbitrary finite commutative rings. Completeness and
honest-receiver zero-knowledge are proved for `qsMaskedCheck`, and single-shot independent-weight
soundness (`1 / |F| + (1 - 1 / |F|) * (d / |C|)`) is proved at the value level for
`qsMaskedCheckValue` (`toOuterMeasure_qsMaskedCheckValue_le`, via
`toOuterMeasure_qsHomogLinearBatch_le`); unmasked challenge-embedding soundness (`d / |C|`) and
scalar-power batching (`t / |F| + d / |C|`) are proved in `toOuterMeasure_qsCheck_le_of_embedding`
and `toOuterMeasure_qsHomogScalarBatch_le`.

For any fixed polynomial `P` of degree at most `d` with nonzero degree-`d` coefficient and any
challenge embedding `ι : C ↪ F`, univariate Schwartz–Zippel bounds the acceptance probability over
`c ← uniformOfFintype C` by `d / |C|`. Combining `FAEST.Challenge` grinding-bit filtering gives
single-shot bounds `d / 2 ^ λ` (raw uniform `λ`-bit challenge with rejection) and
`d / 2 ^ (λ - w_grind)` (uniform over accepted challenges); these single-shot bounds do not model
Fiat–Shamir grinding amplification or state-restoration soundness.

For VOLE-ACT's Spending relation (`m_uov = 45` in [VOLEACT2026], Instantiations /
VOLE-ACT-KP800 Table `vole-act-kp800-parameters`) as realized in `vole-mole` ([VoleMole2026],
commit `87af6871f`: `d_zk = 9`, `ℓ' = 6784`, `C' = 12283`, and `"rata\x00l0"` RLC), suffixing the
trailing domain byte `0x30` onto fixed-length byte messages `ByteMsg n := Fin n → Fin 256`
separates ACT's RLC trailing byte from the FAEST v3 `H_i` trailing bytes (`0, 1, 3..5, 8..11`) plus
`vole-mole`'s `H_2^4 = 12` in `faestTrailingDomainBytes`, splitting a single uniform finite random
oracle `H_all : ByteMsg (n + 1) → Fin m → F` into independent uniform tables (`vole-mole`'s own
7-byte `ACT_*_DST` / IHAT / PoMFRIT tags mostly end in `'0' = 0x30`, separated by their penultimate
purpose byte such as `'l'` in `"rata\x00l0"`, and are outside this single-trailing-byte model).
This gives the conditional single-shot Round-2+3 interactive QuickSilver steps
`toOuterMeasure_actV1_qs_of_zkBinding_le` (single oracle) and
`toOuterMeasure_actV1_domainSeparated_qs_of_zkBinding_le` (single-RO domain-separated) with error
`q * δ_K + (1 / |F| + (1 - 1 / |F|) * (ε_zk + d / |C|))`, together with the specialization
`toOuterMeasure_actV1_foldedQS_le` on `foldedConstraint`. Note that FAEST v3.0 Lemmas 4.6
(`ℓ' ≤ 2^12`), 4.7 (`C' ≤ 2^13`), and 10.40 (`d_zk ∈ {7, 14}`) are stated under hypotheses that
exclude ACT's `d_zk = 9`, `ℓ' = 6784`, `C' = 12283`; concrete `VOLEHash` / `ZKHash` constructions
and Fiat–Shamir multi-round soundness are not formalized here.

## Source correspondence and gaps

* [YangSarkarWengWang2021]: Sections 3.1 and 4.2 describe the circuit-satisfiability protocol
  background (`VOLE.Circuit` / `VOLE.MulCheck`); the arbitrary-degree polynomial-set construction
  is in Section 3.2 and Section 5 (Figure 6), with security stated in Theorem 3 (Section 5.1)
  and proved in Appendix C (the Lean results remain finite algebraic and conditional).
* [BaumBMRS2023Eprint], Appendix B.1 (printed p. 46; full version of [BaumBMRS2023]): sketches
  generalization of sVOLE checks to arbitrary degree `d` via `(d - 1)` masks.
* [BaumEtAl2023FAEST], Section 2.3.2: affine masking and scalar-power batched VOLE checks.
* [BaumEtAl2026FAEST], Section 2.2 ("Adding Zero-Knowledge", `ZK.OWFProve` Figure 7.19), Section 3.3
  (`H_0`..`H_5` domain separation bytes), Section 5.4 (Figure 5.6 / Proposition 5.2), and
  Section 5.5 (Figure 5.7): QuickSilver `(d_zk - 1)` telescoping masking and `Challenge`
  grinding structure, and (cf. Lemmas 4.6–4.7 and Lemma 10.40, stated under
  `d_zk ∈ {7, 14}`, `ℓ' ≤ 2 ^ 12`, `C' ≤ 2 ^ 13`) FAEST v3 parameter regimes. Concrete FAEST
  `VOLEHash` / `ZKHash` / BAVC / signature reductions remain tracked in #4987.
* [VOLEACT2026], Instantiations / VOLE-ACT-KP800 (`m_uov = 45` in Table `vole-act-kp800-parameters`,
  leaving constraint expansion as TODO) and Spending (checks V1–V4).
* [VoleMole2026], commit `87af6871f49d29f9613ee893485c50566ca7d620`: segmented Keccak Spend
  parameters (`d_zk = 9`, `ℓ' = 6784`, `C' = 12283` in `src/keccak/segmented.hpp` and
  `src/act/spend.hpp`), `"rata\x00l0"` RLC (`ACT_SPEND_COMBINE_DST` in `src/dst.hpp:44`, invoked
  in `src/act/spend.hpp:383` and hashed at `src/uov/circuit.hpp:63–64`), and `H_2^4` (`12`) in
  `src/voleith.hpp:126`. VOLEitH ROM extraction, end-to-end ACT protocol security, and consolidating
  `MaskedMulCheck` (`maskedMulCheck`, `maskedMulCheckView`, `maskedMulCheckSimulate` and clients
  `AdaptiveMulCheck`, `CircuitPrivacy`, `Circuit`, `CircuitSound`, `Native`) as the `d = 2`
  instance of `qsMaskedCheck` (generalizing adaptive-receiver simulation to `d ≥ 1` and migrating
  those `F × F` / `(left, right, output)` clients as a separate redesign) remain tracked in
  #7068.

## Main definitions

* `Cslib.Crypto.Protocols.VOLE.qsPolySum`, `qsHomogPoly`, `qsHomogVerifierValue`: arbitrary-degree
  QuickSilver homogenized wire evaluation and verifier check.
* `Cslib.Crypto.Protocols.VOLE.qsMaskCoeff`, `qsMaskValue`: `(d - 1)`-coordinate VOLE masking.
* `Cslib.Crypto.Protocols.VOLE.qsMaskedCheckSpec`, `qsMaskedCheck`, `qsMaskedCheckView`,
  `qsMaskedCheckSimulate`: ideal-world masked degree-`d` QuickSilver protocol and simulator.
* `Cslib.Crypto.Protocols.VOLE.grindingAcceptedEquiv`: bijection for `FAEST.Challenge` zero suffix.
* `Cslib.Crypto.Protocols.VOLE.foldedConstraint`, `actRLCDomainByte`, `faestTrailingDomainBytes`,
  `ByteMsg`, `FaestTaggedMsg`, `appendDomainByteFin`, `appendFaestDomainByteFin`: ACT V1 RLC and
  finite trailing-byte domain separation.

## Main results

* `Cslib.Crypto.Protocols.VOLE.natDegree_qsHomogPoly_le`,
  `Cslib.Crypto.Protocols.VOLE.coeff_qsHomogPoly_eq_eval`,
  `Cslib.Crypto.Protocols.VOLE.qsHomogVerifierValue_complete`: degree, leading term, and algebraic
  completeness of homogenized polynomial checks.
* `Cslib.Crypto.Protocols.VOLE.qsMaskedCheck_complete`,
  `Cslib.Crypto.Protocols.VOLE.qsMaskedCheckView_eq_simulate`,
  `Cslib.Crypto.Protocols.VOLE.toOuterMeasure_qsHomogLinearBatch_le`,
  `Cslib.Crypto.Protocols.VOLE.toOuterMeasure_qsMaskedCheckValue_le`: perfect completeness,
  full-view honest-receiver ZK (`d ≥ 1`), and independent-weight single-shot soundness
  (`1 / |F| + (1 - 1 / |F|) * (d / |C|)`) for degree-`d` homogenized and masked checks.
* `Cslib.Crypto.Protocols.VOLE.toOuterMeasure_qsCheck_le_of_embedding`,
  `Cslib.Crypto.Protocols.VOLE.toOuterMeasure_qsHomogScalarBatch_le`,
  `Cslib.Crypto.Protocols.VOLE.toOuterMeasure_qsCheck_grinding_accepted_le`,
  `Cslib.Crypto.Protocols.VOLE.toOuterMeasure_qsCheck_grinding_raw_le`: at-most `d / |C|` soundness,
  `(t / |F| + d / |C|)` scalar-power batch bound, and single-shot FAEST grinding soundness.
* `Cslib.Crypto.Protocols.VOLE.uniform_split_of_disjoint_range`,
  `Cslib.Crypto.Protocols.VOLE.disjoint_range_actRLC_faestDomainByteFin`,
  `Cslib.Crypto.Protocols.VOLE.toOuterMeasure_actV1_qs_of_zkBinding_le`,
  `Cslib.Crypto.Protocols.VOLE.toOuterMeasure_actV1_domainSeparated_qs_of_zkBinding_le`,
  `Cslib.Crypto.Protocols.VOLE.toOuterMeasure_actV1_foldedQS_le`: domain-separated single-RO
  splitting, conditional Round-2+3 QuickSilver steps, and unconditional `foldedConstraint`
  specialization.

## References

* [K. Yang, P. Sarkar, C. Weng, X. Wang, *QuickSilver: Efficient and Affordable Zero-Knowledge
  Proofs for Circuits and Polynomials over Any Field*][YangSarkarWengWang2021]
* [C. Baum et al., *Publicly Verifiable Zero-Knowledge and Post-Quantum Signatures from
  VOLE-in-the-Head* (full version, ePrint 2023/996)][BaumBMRS2023Eprint]
* [C. Baum et al., *FAEST: Algorithm Specifications*, version 1.0][BaumEtAl2023FAEST]
* [C. Baum et al., *FAEST v3: Algorithm Specifications*, version 3.0][BaumEtAl2026FAEST]
* [T. Zhang, C. Patton, S. Schlesinger, *VOLE-ACT*][VOLEACT2026]
* [C. Patton, T. Zhang, *vole-mole* (commit `87af6871f`)][VoleMole2026]
-/

public section

namespace Cslib.Crypto.Protocols.VOLE

open Interactive Interactive.Spec Probability RandomOracle
open Cslib.Crypto.FAEST
open scoped BigOperators ENNReal Matrix

/-! ### Arbitrary-Degree QuickSilver Homogenized Checks and VOLE Masking -/

section Algebra

variable {R : Type} [CommRing R]

/-- The degree-`1` authenticated wire polynomial `v i + w i * X` whose evaluation at `Δ` equals the
adjusted receiver tag `w i * Δ + v i`. -/
@[expose] noncomputable def qsWirePoly {n : ℕ} (w v : Fin n → R) (i : Fin n) : Polynomial R :=
  Polynomial.C (v i) + Polynomial.C (w i) * Polynomial.X

/-- Verifier evaluation of a degree-`< d` QuickSilver reply vector `a : Fin d → R` at `Δ`:
`∑ k : Fin d, a k * Δ ^ k`. -/
@[expose] def qsPolySum (d : ℕ) (a : Fin d → R) (delta : R) : R :=
  ∑ k : Fin d, a k * delta ^ (k : ℕ)

/-- Any polynomial of degree at most `d` decomposes at `delta` into `P.coeff d * delta ^ d` plus the
verifier linear combination of its `d` lower coefficients. -/
private theorem eval_eq_coeff_pow_add_qsPolySum {d : ℕ} {P : Polynomial R} (hdeg : P.natDegree ≤ d)
    (delta : R) :
    P.eval delta = P.coeff d * delta ^ d + qsPolySum d (fun k => P.coeff k) delta := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), Finset.sum_range_succ, add_comm,
    qsPolySum, ← Fin.sum_univ_eq_sum_range (fun k => P.coeff k * delta ^ k) d]

private theorem coeff_qsWirePoly_eq_one {n : ℕ} (w v : Fin n → R) (i : Fin n) :
    (qsWirePoly w v i).natDegree ≤ 1 ∧ (qsWirePoly w v i).coeff 1 = w i := by
  exact ⟨(Polynomial.natDegree_add_le _ _).trans
    (max_le (by simp) ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le)),
    by simp [qsWirePoly]⟩

private theorem natDegree_mul_le_and_coeff {p q : Polynomial R} {kp kq : ℕ}
    (hp : p.natDegree ≤ kp) (hq : q.natDegree ≤ kq) :
    (p * q).natDegree ≤ kp + kq ∧ (p * q).coeff (kp + kq) = p.coeff kp * q.coeff kq := by
  refine ⟨Polynomial.natDegree_mul_le.trans (Nat.add_le_add hp hq), ?_⟩
  rw [Polynomial.coeff_mul, Finset.sum_eq_single (kp, kq)]
  · intro ⟨a, b⟩ hab hne
    rw [Finset.mem_antidiagonal] at hab
    simp only [ne_eq, Prod.mk.injEq] at hne
    by_cases ha : kp < a
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp ha), zero_mul]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq (by omega)), mul_zero]
  · simp

private theorem natDegree_pow_le_and_coeff (p : Polynomial R) {k : ℕ}
    (hp : p.natDegree ≤ k) (e : ℕ) :
    (p ^ e).natDegree ≤ e * k ∧ (p ^ e).coeff (e * k) = (p.coeff k) ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, pow_succ, Nat.succ_mul]
    exact natDegree_mul_le_and_coeff ih.1 hp |>.imp id fun h => by rw [h, ih.2]

private theorem natDegree_prod_le_and_coeff {ι : Type} (s : Finset ι)
    (f : ι → Polynomial R) (k : ι → ℕ) (hf : ∀ i ∈ s, (f i).natDegree ≤ k i) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, k i ∧
      (∏ i ∈ s, f i).coeff (∑ i ∈ s, k i) = ∏ i ∈ s, (f i).coeff (k i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    obtain ⟨hdeg, hcoeff⟩ := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi]
    exact (natDegree_mul_le_and_coeff (hf i (Finset.mem_insert_self i s)) hdeg).imp id
      fun h => by rw [h, hcoeff]

/-- Homogenizing a multivariate polynomial `F_poly` of total degree at most `d` over `Fin n` on
authenticated wire polynomials `v i + w i * X` multiplies each monomial `m` of degree `deg ≤ d`
by `X ^ (d - deg)`. -/
@[expose] noncomputable def qsHomogPoly {n : ℕ} (d : ℕ) (F_poly : MvPolynomial (Fin n) R)
    (w v : Fin n → R) : Polynomial R :=
  F_poly.support.sum fun m =>
    Polynomial.C (F_poly.coeff m) * Polynomial.X ^ (d - m.sum fun _ e => e) *
      ∏ i : Fin n, qsWirePoly w v i ^ m i

/-- Receiver/verifier evaluation of a homogenized degree-`d` polynomial constraint from adjusted
wire tags `q' : Fin n → R` and global key `delta : R`. -/
@[expose] noncomputable def qsHomogVerifierValue {n : ℕ} (d : ℕ)
    (F_poly : MvPolynomial (Fin n) R) (delta : R) (q' : Fin n → R) : R :=
  F_poly.support.sum fun m =>
    F_poly.coeff m * delta ^ (d - m.sum fun _ e => e) * ∏ i : Fin n, q' i ^ m i

/-- Evaluating `qsHomogPoly d F_poly w v` at `delta` agrees with `qsHomogVerifierValue` on
`fun i => w i * delta + v i`, unconditionally over any commutative ring. -/
theorem eval_qsHomogPoly {n : ℕ} (d : ℕ) (F_poly : MvPolynomial (Fin n) R)
    (w v : Fin n → R) (delta : R) :
    (qsHomogPoly d F_poly w v).eval delta =
      qsHomogVerifierValue d F_poly delta (fun i => w i * delta + v i) := by
  rw [qsHomogPoly, qsHomogVerifierValue, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.eval_pow, qsWirePoly, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, add_comm, mul_comm (w i) delta]

private theorem monomial_degree_le_totalDegree {n : ℕ} {F_poly : MvPolynomial (Fin n) R}
    {m : Fin n →₀ ℕ} (hm : m ∈ F_poly.support) :
    (m.sum fun _ e => e) ≤ F_poly.totalDegree := by
  simpa only [Finsupp.sum] using MvPolynomial.le_totalDegree hm

/-- When `F_poly.totalDegree ≤ d`, the homogenized QuickSilver polynomial has degree at most `d`
and degree-`d` coefficient equal to `MvPolynomial.eval w F_poly`. -/
private theorem natDegree_and_coeff_qsHomogPoly {n : ℕ} (d : ℕ) (F_poly : MvPolynomial (Fin n) R)
    (hdeg : F_poly.totalDegree ≤ d) (w v : Fin n → R) :
    (qsHomogPoly d F_poly w v).natDegree ≤ d ∧
      (qsHomogPoly d F_poly w v).coeff d = MvPolynomial.eval w F_poly := by
  have hterm : ∀ m ∈ F_poly.support,
      (Polynomial.C (F_poly.coeff m) * Polynomial.X ^ (d - m.sum fun _ e => e) *
        ∏ i : Fin n, qsWirePoly w v i ^ m i).natDegree ≤ d ∧
      (Polynomial.C (F_poly.coeff m) * Polynomial.X ^ (d - m.sum fun _ e => e) *
        ∏ i : Fin n, qsWirePoly w v i ^ m i).coeff d =
        F_poly.coeff m * ∏ i : Fin n, w i ^ m i := by
    intro m hm
    have hm_le : (m.sum fun _ e => e) ≤ d := (monomial_degree_le_totalDegree hm).trans hdeg
    have hm_sum : (∑ i : Fin n, m i * 1) = m.sum fun _ e => e := by
      simpa only [mul_one, Finsupp.sum] using
        (Finset.sum_subset (Finset.subset_univ m.support) fun _ _ hi =>
          Finsupp.notMem_support_iff.mp hi).symm
    have hprod := natDegree_prod_le_and_coeff (Finset.univ : Finset (Fin n))
      (fun i => qsWirePoly w v i ^ m i) (fun i => m i * 1) fun i _ =>
        (natDegree_pow_le_and_coeff (qsWirePoly w v i) (coeff_qsWirePoly_eq_one w v i).1
          (m i)).1
    rw [hm_sum] at hprod
    have hpow_coeff : (∏ i : Fin n, (qsWirePoly w v i ^ m i).coeff (m i * 1)) =
        ∏ i : Fin n, w i ^ m i :=
      Finset.prod_congr rfl fun i _ => by
        rw [(natDegree_pow_le_and_coeff (qsWirePoly w v i)
          (coeff_qsWirePoly_eq_one w v i).1 (m i)).2, (coeff_qsWirePoly_eq_one w v i).2]
    have hleft : (Polynomial.C (F_poly.coeff m) *
        Polynomial.X ^ (d - m.sum fun _ e => e)).natDegree ≤
        d - m.sum fun _ e => e :=
      (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le _)
    have hmul := natDegree_mul_le_and_coeff hleft hprod.1
    rw [Nat.sub_add_cancel hm_le] at hmul
    refine ⟨hmul.1, ?_⟩
    simp only [hmul.2, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one]
    congr 1
    simpa only [hm_sum, hpow_coeff] using hprod.2
  refine ⟨Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => (hterm m hm).1, ?_⟩
  rw [qsHomogPoly, Polynomial.finsetSum_coeff, MvPolynomial.eval_eq']
  exact Finset.sum_congr rfl fun m hm => (hterm m hm).2

/-- When `F_poly.totalDegree ≤ d`, the homogenized polynomial `qsHomogPoly d F_poly w v` has
`natDegree ≤ d`. -/
theorem natDegree_qsHomogPoly_le {n : ℕ} {d : ℕ} {F_poly : MvPolynomial (Fin n) R}
    (hdeg : F_poly.totalDegree ≤ d) (w v : Fin n → R) :
    (qsHomogPoly d F_poly w v).natDegree ≤ d :=
  (natDegree_and_coeff_qsHomogPoly d F_poly hdeg w v).1

/-- When `F_poly.totalDegree ≤ d`, the coefficient of `X ^ d` in `qsHomogPoly d F_poly w v`
equals `MvPolynomial.eval w F_poly`. -/
theorem coeff_qsHomogPoly_eq_eval {n : ℕ} {d : ℕ} {F_poly : MvPolynomial (Fin n) R}
    (hdeg : F_poly.totalDegree ≤ d) (w v : Fin n → R) :
    (qsHomogPoly d F_poly w v).coeff d = MvPolynomial.eval w F_poly :=
  (natDegree_and_coeff_qsHomogPoly d F_poly hdeg w v).2

/-- With a valid VOLE correlation `c`, the receiver's adjusted check value for `F_poly` equals
`MvPolynomial.eval w F_poly * c.delta ^ d` plus the verifier evaluation of the `d` lower
coefficients of `qsHomogPoly d F_poly w c.v`. -/
theorem qsHomogVerifierValue_eq_eval {n : ℕ} {d : ℕ} {F_poly : MvPolynomial (Fin n) R}
    (hdeg : F_poly.totalDegree ≤ d) (w : Fin n → R) (c : VOLECorrelation R n) (hc : c.Valid) :
    qsHomogVerifierValue d F_poly c.delta
        (voleAdjustReceiver c.w (voleCommitWitness w c.u) c.delta) =
      MvPolynomial.eval w F_poly * c.delta ^ d +
        qsPolySum d (fun k => (qsHomogPoly d F_poly w c.v).coeff k) c.delta := by
  have hadj : voleAdjustReceiver c.w (voleCommitWitness w c.u) c.delta =
      fun i => w i * c.delta + c.v i :=
    funext fun i => voleAdjustReceiver_voleCommitWitness hc w i
  rw [hadj, ← eval_qsHomogPoly, eval_eq_coeff_pow_add_qsPolySum
    (natDegree_qsHomogPoly_le hdeg w c.v), coeff_qsHomogPoly_eq_eval hdeg w c.v]

/-- Algebraic completeness for a vanishing degree-`≤ d` constraint: the adjusted receiver value
equals `qsPolySum` on the lower `d` coefficients. -/
theorem qsHomogVerifierValue_complete {n : ℕ} {d : ℕ} {F_poly : MvPolynomial (Fin n) R}
    (hdeg : F_poly.totalDegree ≤ d) (w : Fin n → R) (c : VOLECorrelation R n) (hc : c.Valid)
    (hzero : MvPolynomial.eval w F_poly = 0) :
    qsHomogVerifierValue d F_poly c.delta
        (voleAdjustReceiver c.w (voleCommitWitness w c.u) c.delta) =
      qsPolySum d (fun k => (qsHomogPoly d F_poly w c.v).coeff k) c.delta := by
  rw [qsHomogVerifierValue_eq_eval hdeg w c hc, hzero, zero_mul, zero_add]

/-- QuickSilver telescoping mask coefficients from `(d - 1)` extra VOLE mask pairs `(u, v)`
([BaumEtAl2026FAEST], Section 2.2 "Adding Zero-Knowledge" and `ZK.OWFProve` Figure 7.19):
`p_0 = v_0`, `p_j = v_j + u_{j-1}`, `p_{d-1} = u_{d-2}`. -/
@[expose] def qsMaskCoeff (d : ℕ) (u v : Fin (d - 1) → R) (j : Fin d) : R :=
  (if hj : j.val < d - 1 then v ⟨j.val, hj⟩ else 0) +
    (if hj0 : 0 < j.val then u ⟨j.val - 1, by omega⟩ else 0)

/-- The receiver's scalar combination of the `(d - 1)` mask tags: `∑ k, q_m k * delta ^ k`. -/
@[expose] def qsMaskValue (d : ℕ) (q_m : Fin (d - 1) → R) (delta : R) : R :=
  ∑ k : Fin (d - 1), q_m k * delta ^ (k : ℕ)

/-- Evaluating the telescoping mask coefficients `qsMaskCoeff d u v` at `delta` produces
`∑ k : Fin (d - 1), (u k * delta + v k) * delta ^ k` for all `d : ℕ`. -/
theorem qsPolySum_qsMaskCoeff (d : ℕ) (u v : Fin (d - 1) → R) (delta : R) :
    qsPolySum d (qsMaskCoeff d u v) delta =
      ∑ k : Fin (d - 1), (u k * delta + v k) * delta ^ (k : ℕ) := by
  rcases d with _ | _ | m
  · simp [qsPolySum, qsMaskCoeff]
  · simp [qsPolySum, qsMaskCoeff]
  · simp only [qsPolySum, qsMaskCoeff, add_mul, Finset.sum_add_distrib]
    rw [Fin.sum_univ_castSucc (n := m + 1), Fin.sum_univ_succ (n := m + 1)]
    simp only [Fin.val_castSucc, Fin.is_lt, Fin.val_last, Fin.val_zero, Fin.val_succ, lt_irrefl,
      Nat.succ_pos, Nat.add_sub_cancel, ↓reduceDIte, Fin.eta, zero_mul, add_zero, zero_add,
      pow_succ', ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring

/-- When `q_m k = u k * delta + v k` for all `k : Fin (d - 1)`, `qsPolySum` on `qsMaskCoeff`
equals `qsMaskValue d q_m delta`. -/
theorem qsPolySum_qsMaskCoeff_eq_qsMaskValue (d : ℕ) (u v q_m : Fin (d - 1) → R) (delta : R)
    (hvalid : ∀ k, q_m k = u k * delta + v k) :
    qsPolySum d (qsMaskCoeff d u v) delta = qsMaskValue d q_m delta := by
  rw [qsPolySum_qsMaskCoeff, qsMaskValue]
  refine Finset.sum_congr rfl fun k _ => by rw [hvalid k]

end Algebra

/-! ### Full Honest-Receiver View Zero-Knowledge for Masked Degree-`d` QuickSilver -/

section MaskedZK

variable {F ι : Type} {n d : ℕ}

/-- Three-move interaction specification for masked degree-`d` QuickSilver checks: wire
corrections, public batch weights, then the `d` masked lower coefficients. -/
abbrev qsMaskedCheckSpec (F ι : Type) (n d : ℕ) : Spec :=
  threeMoveSpec (Fin n → F) (ι → F) (Fin d → F)

variable [CommRing F] [Fintype ι]

/-- Honest reply coefficients `0 .. d - 1` of the masked batched degree-`d` constraint polynomial.
Setup wires `0 .. n - 1` commit the witness, while setup coordinates `n .. n + (d - 1) - 1`
provide the `(d - 1)` VOLE masks. -/
@[expose] noncomputable def qsMaskedCheckReply (d : ℕ) (constraints : ι → MvPolynomial (Fin n) F)
    (w : Fin n → F) (u v : Fin (n + (d - 1)) → F) (r : ι → F) : Fin d → F :=
  let v_w : Fin n → F := fun i => v (Fin.castAdd (d - 1) i)
  let u_m : Fin (d - 1) → F := fun k => u (Fin.natAdd n k)
  let v_m : Fin (d - 1) → F := fun k => v (Fin.natAdd n k)
  fun j => (∑ i, r i * (qsHomogPoly d (constraints i) w v_w).coeff j.val) +
    qsMaskCoeff d u_m v_m j

/-- Receiver's scalar evaluation of the batched homogenized constraints plus the `(d - 1)` mask
tags. -/
@[expose] noncomputable def qsMaskedCheckValue (d : ℕ) (constraints : ι → MvPolynomial (Fin n) F)
    (delta : F) (q : Fin (n + (d - 1)) → F) (d_corr : Fin n → F) (r : ι → F) : F :=
  let q_w : Fin n → F := fun i => q (Fin.castAdd (d - 1) i)
  let q_m : Fin (d - 1) → F := fun k => q (Fin.natAdd n k)
  let adjusted := voleAdjustReceiver q_w d_corr delta
  (∑ i, r i * qsHomogVerifierValue d (constraints i) delta adjusted) +
    qsMaskValue d q_m delta

/-- Verification predicate for a masked degree-`d` QuickSilver transcript. -/
abbrev QSMaskedCheckAccepts (d : ℕ) (constraints : ι → MvPolynomial (Fin n) F) :
    F × (Fin (n + (d - 1)) → F) → Transcript (qsMaskedCheckSpec F ι n d) → Prop :=
  fun (delta, q) (d_corr, r, reply, ()) =>
    qsMaskedCheckValue d constraints delta q d_corr r = qsPolySum d reply delta

/-- Algebraic completeness of `qsMaskedCheckReply` under any valid `VOLECorrelation` of length
`n + (d - 1)` for any degree-`≤ d` constraint family vanishing on `w`. -/
theorem qsMaskedCheckReply_correct (d : ℕ) (constraints : ι → MvPolynomial (Fin n) F)
    (hdeg : ∀ i, (constraints i).totalDegree ≤ d) (w : Fin n → F)
    (c : VOLECorrelation F (n + (d - 1))) (hc : c.Valid) (r : ι → F)
    (hzero : ∀ i, MvPolynomial.eval w (constraints i) = 0) :
    qsMaskedCheckValue d constraints c.delta c.w
        (voleCommitWitness w (fun i => c.u (Fin.castAdd (d - 1) i))) r =
      qsPolySum d (qsMaskedCheckReply d constraints w c.u c.v r) c.delta := by
  let c_w : VOLECorrelation F n :=
    ⟨fun i => c.u (Fin.castAdd (d - 1) i), fun i => c.v (Fin.castAdd (d - 1) i), c.delta,
      fun i => c.w (Fin.castAdd (d - 1) i)⟩
  have hcw : c_w.Valid := fun i => hc (Fin.castAdd (d - 1) i)
  have hmask : qsPolySum d (qsMaskCoeff d (fun k => c.u (Fin.natAdd n k))
      (fun k => c.v (Fin.natAdd n k))) c.delta =
      qsMaskValue d (fun k => c.w (Fin.natAdd n k)) c.delta :=
    qsPolySum_qsMaskCoeff_eq_qsMaskValue d _ _ _ c.delta fun k => hc (Fin.natAdd n k)
  rw [qsMaskedCheckValue]
  change (∑ i, r i * qsHomogVerifierValue d (constraints i) c_w.delta
      (voleAdjustReceiver c_w.w (voleCommitWitness w c_w.u) c_w.delta)) +
      qsMaskValue d (fun k => c.w (Fin.natAdd n k)) c.delta = _
  simp_rw [qsHomogVerifierValue_complete (hdeg _) w c_w hcw (hzero _)]
  rw [← hmask]
  simp only [qsPolySum, qsMaskedCheckReply, c_w, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
    ← mul_assoc]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]

variable [Fintype F] [DecidableEq F] [DecidableEq ι]

/-- Public-coin role-local reduction for masked degree-`d` QuickSilver checks in `voleWorld`. -/
@[expose] noncomputable def qsMaskedCheck (d : ℕ)
    (constraints : ι → MvPolynomial (Fin n) F) :
    Reduction (voleSenderSpec F (n + (d - 1))) (voleReceiverSpec F (n + (d - 1)))
      (qsMaskedCheckSpec F ι n d) Unit (Fin n → F) Unit Unit where
  prover _ w := do
    let (u, v) ← ProbOracleComp.query ()
    return (show ProbOracleComp (voleSenderSpec F (n + (d - 1)))
      ((Fin n → F) × ((ι → F) → ProbOracleComp (voleSenderSpec F (n + (d - 1)))
        (ProbOracleComp (voleSenderSpec F (n + (d - 1))) ((Fin d → F) × (Unit × Unit))))) from
      pure (voleCommitWitness w (fun i => u (Fin.castAdd (d - 1) i)), fun r => pure
        (pure (qsMaskedCheckReply d constraints w u v r, ((), ())))))
  verifier := {
    samplers := (ProbComp.uniform (ι → F), ())
    decide := fun _ challenges => do
      let (delta, q) ← OracleComp.query
        (spec := voleReceiverSpec F (n + (d - 1)) ⊕ₒ msgSpec (qsMaskedCheckSpec F ι n d))
        (.inl ())
      let d_corr : Fin n → F ← OracleComp.query
        (spec := voleReceiverSpec F (n + (d - 1)) ⊕ₒ msgSpec (qsMaskedCheckSpec F ι n d))
        (.inr (.inl ()))
      let reply : Fin d → F ← OracleComp.query
        (spec := voleReceiverSpec F (n + (d - 1)) ⊕ₒ msgSpec (qsMaskedCheckSpec F ι n d))
        (.inr (.inr (.inl ())))
      return if qsMaskedCheckValue d constraints delta q d_corr challenges.1 =
          qsPolySum d reply delta then some () else none }

private theorem qsMaskedCheck_output (d : ℕ) (constraints : ι → MvPolynomial (Fin n) F)
    (t : Transcript (qsMaskedCheckSpec F ι n d)) :
    (qsMaskedCheck d constraints).verifier.output
      (oP := voleSenderSpec F (n + (d - 1))) () t = (do
      let (delta, q) ← ProbOracleComp.query
        (spec := voleSenderSpec F (n + (d - 1)) ⊕ₒ voleReceiverSpec F (n + (d - 1))) (.inr ())
      return if QSMaskedCheckAccepts d constraints (delta, q) t then some () else none) := by
  unfold Verifier.output qsMaskedCheck
  rw [OracleComp.interpret_bind, OracleComp.interpret_query]
  simp only [OracleComp.sumHandler]
  congr 1

/-- Full honest receiver view `(receiverShare, transcript)` in `voleWorld F (n + (d - 1))`. -/
@[expose] noncomputable def qsMaskedCheckView (d : ℕ)
    (constraints : ι → MvPolynomial (Fin n) F) (w : Fin n → F) :
    PMF ((F × (Fin (n + (d - 1)) → F)) × Transcript (qsMaskedCheckSpec F ι n d)) :=
  (voleWorld F (n + (d - 1))).eval do
    let receiver ← ProbOracleComp.query (.inr ())
    let result ← (qsMaskedCheck d constraints).run () w
    return (receiver, result.1)

/-- Assemble the full `Fin d` reply from its constant coefficient and `d - 1` higher coefficients
when `1 ≤ d`. -/
private def consReply (d : ℕ) (c0 : F) (hi : Fin (d - 1) → F) : Fin d → F :=
  fun j => if hj : j.val = 0 then c0 else hi ⟨j.val - 1, by omega⟩

omit [Fintype F] [DecidableEq F] [DecidableEq ι] in
private theorem qsPolySum_consReply {d : ℕ} (hd : 1 ≤ d) (c0 : F) (hi : Fin (d - 1) → F)
    (delta : F) :
    qsPolySum d (consReply d c0 hi) delta =
      c0 + ∑ k : Fin (d - 1), hi k * delta ^ (k.val + 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hd
  rw [qsPolySum, Fin.sum_univ_succ]
  simp only [consReply, Fin.val_zero, ↓reduceDIte, pow_zero, mul_one, Fin.val_succ,
    Nat.succ_ne_zero, add_tsub_cancel_right]
  rfl

/-- Witness-free simulator for the complete honest receiver share and public transcript, for every
constraint degree `d ≥ 1`. -/
noncomputable def qsMaskedCheckSimulate (d : ℕ)
    (constraints : ι → MvPolynomial (Fin n) F) :
    ProbComp ((F × (Fin (n + (d - 1)) → F)) × Transcript (qsMaskedCheckSpec F ι n d)) := do
  let delta ← ProbComp.uniform F
  let q ← ProbComp.uniform (Fin (n + (d - 1)) → F)
  let d_corr ← ProbComp.uniform (Fin n → F)
  let r ← ProbComp.uniform (ι → F)
  let hiReply ← ProbComp.uniform (Fin (d - 1) → F)
  let c0 := qsMaskedCheckValue d constraints delta q d_corr r -
    ∑ k : Fin (d - 1), hiReply k * delta ^ (k.val + 1)
  return ((delta, q), (d_corr, (r, (consReply d c0 hiReply, ()))))

omit [DecidableEq F] in
/-- Every simulated view satisfies `QSMaskedCheckAccepts` when `1 ≤ d`. -/
theorem qsMaskedCheckSimulate_accepts {d : ℕ} (hd : 1 ≤ d)
    (constraints : ι → MvPolynomial (Fin n) F)
    {view : (F × (Fin (n + (d - 1)) → F)) × Transcript (qsMaskedCheckSpec F ι n d)}
    (hv : view ∈ (ProbComp.eval (qsMaskedCheckSimulate d constraints)).support) :
    QSMaskedCheckAccepts d constraints view.1 view.2 := by
  simp only [qsMaskedCheckSimulate, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbComp.eval_pure, PMF.mem_support_bind_iff, PMF.mem_support_uniformOfFintype,
    true_and, PMF.mem_support_pure_iff] at hv
  obtain ⟨delta, q, d_corr, r, hiReply, rfl⟩ := hv
  change qsMaskedCheckValue d constraints delta q d_corr r =
    qsPolySum d (consReply d _ hiReply) delta
  rw [qsPolySum_consReply hd]
  ring

omit [DecidableEq F] in
private theorem bind_runWith_voleWorld_sample_uniform {α : Type} (d : ℕ)
    (c : VOLECorrelation F (n + (d - 1)))
    (g : (ι → F) × Option (VOLECorrelation F (n + (d - 1))) → PMF α) :
    ((ProbOracleComp.runWith (voleWorld F (n + (d - 1))).impl
        (ProbOracleComp.sample
          (spec := voleSenderSpec F (n + (d - 1)) ⊕ₒ voleReceiverSpec F (n + (d - 1)))
          (ProbComp.uniform (ι → F)))
        (some c)).bind g) =
      (PMF.uniformOfFintype (ι → F)).bind fun r => g (r, some c) := by
  let oracle : (q : Unit ⊕ Unit) →
      StateT (Option (VOLECorrelation F (n + (d - 1)))) PMF
        ((voleSenderSpec F (n + (d - 1)) ⊕ₒ voleReceiverSpec F (n + (d - 1))) q) :=
    (voleWorld F (n + (d - 1))).impl
  change (ProbOracleComp.runWith oracle
    (ProbOracleComp.sample
      (spec := voleSenderSpec F (n + (d - 1)) ⊕ₒ voleReceiverSpec F (n + (d - 1)))
      (ProbComp.uniform (ι → F))) (some c)).bind g = _
  rw [ProbOracleComp.runWith_sample, PMF.bind_map]
  simp only [pmf_norm, ProbComp.eval_uniform]

/-- Perfect completeness of `qsMaskedCheck d constraints` in `voleWorld F (n + (d - 1))` for any
degree-`≤ d` constraint family. -/
theorem qsMaskedCheck_complete (d : ℕ) (constraints : ι → MvPolynomial (Fin n) F)
    (hdeg : ∀ i, (constraints i).totalDegree ≤ d) :
    (qsMaskedCheck d constraints).Complete (voleWorld F (n + (d - 1)))
      (fun _ w => ∀ i, MvPolynomial.eval w (constraints i) = 0) Interactive.Accept 0 := by
  intro statement w h
  cases statement
  have hrun : (voleWorld F (n + (d - 1))).eval ((qsMaskedCheck d constraints).run () w) =
      (do
        let c ← voleIdealDist F (n + (d - 1))
        let r ← PMF.uniformOfFintype (ι → F)
        return ((voleCommitWitness w (fun i => c.u (Fin.castAdd (d - 1) i)),
          (r, (qsMaskedCheckReply d constraints w c.u c.v r, ()))),
            some (), ((), ()))) := by
    simp only [World.eval, Reduction.run, Verifier.execute, qsMaskedCheck_output]
    simp only [interp_norm, pmf_norm, qsMaskedCheck, liftProver, runStrategy, qsMaskedCheckSpec,
      threeMoveSpec, voleWorld, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
      ProbOracleComp.runWith_pure, pure_bind, VOLECorrelation.senderView]
    refine PMF.bind_congr_on_support _ _ _ fun c hc => ?_
    rw [← OracleComp.substitute_eq_interpret]
    erw [bind_runWith_voleWorld_sample_uniform]
    congr 1 with r : 1
    simp only [pmf_norm, VOLECorrelation.receiverView, QSMaskedCheckAccepts,
      qsMaskedCheckReply_correct d constraints hdeg w c (valid_of_mem_support_voleIdealDist hc)
        r h, ite_true]
  rw [hrun]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.toOuterMeasure_bind_apply,
    PMF.toOuterMeasure_pure_apply, Set.mem_ofPred_eq, Interactive.Accept]
  simp

theorem qsMaskedCheckView_eq (d : ℕ) (constraints : ι → MvPolynomial (Fin n) F)
    (w : Fin n → F) :
    qsMaskedCheckView d constraints w = (do
      let c ← voleIdealDist F (n + (d - 1))
      let r ← PMF.uniformOfFintype (ι → F)
      return (c.receiverView, (voleCommitWitness w (fun i => c.u (Fin.castAdd (d - 1) i)),
        (r, (qsMaskedCheckReply d constraints w c.u c.v r, ()))))) := by
  simp only [interp_norm, pmf_norm, qsMaskedCheckView, qsMaskedCheck, qsMaskedCheckSpec,
    threeMoveSpec, World.eval, Reduction.run, Verifier.execute, Verifier.output, liftProver,
    runStrategy, Transcript.challenges, OracleInterface.full, voleWorld, VOLECorrelation.senderView,
    ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure,
    pure_bind]
  congr 1 with c : 1
  rw [← OracleComp.substitute_eq_interpret]
  erw [bind_runWith_voleWorld_sample_uniform]
  simp [PMF.bind_const]

omit [DecidableEq F] [DecidableEq ι] in
private theorem qsMaskedView_fixed {d : ℕ} (hd : 1 ≤ d)
    (constraints : ι → MvPolynomial (Fin n) F) (hdeg : ∀ i, (constraints i).totalDegree ≤ d)
    (w : Fin n → F) (delta : F) (r : ι → F)
    (hzero : ∀ i, MvPolynomial.eval w (constraints i) = 0) :
    (do
      let u ← PMF.uniformOfFintype (Fin (n + (d - 1)) → F)
      let v ← PMF.uniformOfFintype (Fin (n + (d - 1)) → F)
      return ((voleSample u v delta).receiverView,
        (voleCommitWitness w (fun i => u (Fin.castAdd (d - 1) i)),
          (r, (qsMaskedCheckReply d constraints w u v r, ()))))) = (do
      let q ← PMF.uniformOfFintype (Fin (n + (d - 1)) → F)
      let d_corr ← PMF.uniformOfFintype (Fin n → F)
      let hiReply ← PMF.uniformOfFintype (Fin (d - 1) → F)
      let c0 := qsMaskedCheckValue d constraints delta q d_corr r -
        ∑ k : Fin (d - 1), hiReply k * delta ^ (k.val + 1)
      return ((delta, q), (d_corr, (r, (consReply d c0 hiReply, ()))))) := by
  relabel_uniform (fun uv : (Fin (n + (d - 1)) → F) × (Fin (n + (d - 1)) → F) =>
    ((voleSample uv.1 uv.2 delta).w,
      (voleCommitWitness w (fun i => uv.1 (Fin.castAdd (d - 1) i)),
      fun k : Fin (d - 1) =>
        qsMaskedCheckReply d constraints w uv.1 uv.2 r ⟨k.val + 1, by omega⟩)))
    with uv
  · rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ h
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨hq, hd_corr, hhi⟩
    have hu_w : ∀ i : Fin n,
        u₁ (Fin.castAdd (d - 1) i) = u₂ (Fin.castAdd (d - 1) i) := fun i => by
      simpa [voleCommitWitness] using congrFun hd_corr i
    have hv_w_fun :
        (fun i => v₁ (Fin.castAdd (d - 1) i)) = fun i => v₂ (Fin.castAdd (d - 1) i) :=
      funext fun i => by
        simpa [voleSample, hu_w i] using congrFun hq (Fin.castAdd (d - 1) i)
    have hm_ind (bound : ℕ) : ∀ k : Fin (d - 1), (d - 1) - k.val ≤ bound →
        u₁ (Fin.natAdd n k) = u₂ (Fin.natAdd n k) ∧
        v₁ (Fin.natAdd n k) = v₂ (Fin.natAdd n k) := by
      induction bound with
      | zero => exact fun k _ => absurd k.isLt (by omega)
      | succ b ih =>
        intro k hk
        have hhi_k := congrFun hhi k
        simp only [qsMaskedCheckReply, hv_w_fun, qsMaskCoeff, Nat.succ_pos, ↓reduceDIte,
          Nat.add_sub_cancel] at hhi_k
        have hu_k : u₁ (Fin.natAdd n k) = u₂ (Fin.natAdd n k) := by
          by_cases hk_lt : k.val + 1 < d - 1
          · have hv_next := (ih ⟨k.val + 1, hk_lt⟩ (by dsimp only; omega)).2
            simp only [hk_lt, ↓reduceDIte, hv_next] at hhi_k
            exact add_left_cancel (add_left_cancel hhi_k)
          · simp only [hk_lt, ↓reduceDIte, zero_add] at hhi_k
            exact add_left_cancel hhi_k
        exact ⟨hu_k, by simpa [voleSample, hu_k] using congrFun hq (Fin.natAdd n k)⟩
    have hu : u₁ = u₂ := funext fun x => by
      cases x using Fin.addCases with
      | left i => exact hu_w i
      | right k => exact (hm_ind (d - 1) k (Nat.sub_le _ _)).1
    refine Prod.ext hu (funext fun x => ?_)
    subst hu
    exact add_left_cancel (congrFun hq x)
  · simp [Fintype.card_prod, pow_add]
  · have hc := qsMaskedCheckReply_correct d constraints hdeg w
      (voleSample uv.1 uv.2 delta) (valid_voleSample _ _ _) r hzero
    dsimp only [voleSample, VOLECorrelation.receiverView] at hc ⊢
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hd
    have hsum : qsPolySum (m + 1) (qsMaskedCheckReply (m + 1) constraints w uv.1 uv.2 r) delta =
        qsMaskedCheckReply (m + 1) constraints w uv.1 uv.2 r ⟨0, Nat.succ_pos _⟩ +
          ∑ k : Fin m,
            qsMaskedCheckReply (m + 1) constraints w uv.1 uv.2 r ⟨k.val + 1, by omega⟩ *
              delta ^ (k.val + 1) := by
      simp only [qsPolySum, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
      rfl
    have hc0 :
        qsMaskedCheckValue (m + 1) constraints delta (fun x => uv.1 x * delta + uv.2 x)
            (voleCommitWitness w (fun i => uv.1 (Fin.castAdd ((m + 1) - 1) i))) r -
          ∑ k : Fin m,
            qsMaskedCheckReply (m + 1) constraints w uv.1 uv.2 r ⟨k.val + 1, by omega⟩ *
              delta ^ (k.val + 1) =
          qsMaskedCheckReply (m + 1) constraints w uv.1 uv.2 r ⟨0, Nat.succ_pos _⟩ :=
      sub_eq_iff_eq_add.mpr (by rw [hc, hsum, add_comm])
    refine congrArg PMF.pure
      (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext (funext fun j => ?_) rfl))))
    by_cases hj : j.val = 0
    · simp only [consReply, hj, ↓reduceDIte]
      rw [show (j : Fin (m + 1)) = ⟨0, Nat.succ_pos _⟩ from Fin.ext hj]
      exact hc0.symm
    · simp only [consReply, hj, ↓reduceDIte]
      exact congrArg (qsMaskedCheckReply (m + 1) constraints w uv.1 uv.2 r)
        (Fin.ext (Nat.sub_add_cancel (Nat.pos_of_ne_zero hj)).symm)

/-- Exact simulation of the entire honest receiver view in `voleWorld F (n + (d - 1))` for any
degree `d ≥ 1` and any degree-`≤ d` constraint family over a finite commutative ring. The view
includes the receiver's private key and tags, all witness corrections, the public batch weights,
and all `d` masked reply coefficients. -/
theorem qsMaskedCheckView_eq_simulate {d : ℕ} (hd : 1 ≤ d)
    (constraints : ι → MvPolynomial (Fin n) F) (hdeg : ∀ i, (constraints i).totalDegree ≤ d)
    (w : Fin n → F) (hzero : ∀ i, MvPolynomial.eval w (constraints i) = 0) :
    qsMaskedCheckView d constraints w = ProbComp.eval (qsMaskedCheckSimulate d constraints) := by
  rw [qsMaskedCheckView_eq]
  simp only [pmf_norm, voleIdealDist, qsMaskedCheckSimulate, ProbComp.eval_uniform]
  pmf_swap with delta r
  exact qsMaskedView_fixed hd constraints hdeg w delta r hzero

end MaskedZK

/-! ### Soundness over Challenge Embeddings, Scalar Batching, and FAEST Grinding -/

section Soundness

variable {F : Type} [Field F]

/-- Residual difference polynomial `P - ∑ k < d, a k * X ^ k` tested by degree-`d` QuickSilver. -/
private noncomputable def qsDiffPoly (d : ℕ) (P : Polynomial F) (a : Fin d → F) :
    Polynomial F :=
  P - ∑ k : Fin d, Polynomial.C (a k) * Polynomial.X ^ (k : ℕ)

private theorem eval_qsDiffPoly (d : ℕ) (P : Polynomial F) (a : Fin d → F) (delta : F) :
    (qsDiffPoly d P a).eval delta = P.eval delta - qsPolySum d a delta := by
  simp only [qsDiffPoly, qsPolySum, Polynomial.eval_sub, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

private theorem coeff_qsDiffPoly_top (d : ℕ) (P : Polynomial F) (a : Fin d → F) :
    (qsDiffPoly d P a).coeff d = P.coeff d := by
  rw [qsDiffPoly, Polynomial.coeff_sub, Polynomial.finsetSum_coeff]
  refine sub_eq_self.mpr (Finset.sum_eq_zero fun k _ => ?_)
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    ite_eq_right_iff.mpr fun h => (Nat.ne_of_gt k.isLt h).elim, mul_zero]

private theorem qsDiffPoly_ne_zero (d : ℕ) (P : Polynomial F) (a : Fin d → F)
    (hne : P.coeff d ≠ 0) :
    qsDiffPoly d P a ≠ 0 := by
  exact fun h => hne ((coeff_qsDiffPoly_top d P a).symm.trans (by simp [h]))

private theorem natDegree_qsDiffPoly_le {d : ℕ} {P : Polynomial F} (hdeg : P.natDegree ≤ d)
    (a : Fin d → F) :
    (qsDiffPoly d P a).natDegree ≤ d := by
  rw [qsDiffPoly]
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le hdeg ?_)
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  exact (Polynomial.natDegree_C_mul_le _ _).trans <|
    (Polynomial.natDegree_X_pow_le _).trans (Nat.le_of_lt k.isLt)

/-- For any injective challenge map `ι : C ↪ F` and any polynomial `P` of degree at most `d` with
nonzero degree-`d` coefficient, at most `d` challenges satisfy `P.eval (ι c) = qsPolySum d a (ι c)`.
-/
theorem card_filter_qsCheck_le {C : Type} [Fintype C] [DecidableEq F]
    {d : ℕ} (ι : C ↪ F) {P : Polynomial F} (hdeg : P.natDegree ≤ d) (hne : P.coeff d ≠ 0)
    (a : Fin d → F) :
    (Finset.univ.filter fun c : C => P.eval (ι c) = qsPolySum d a (ι c)).card ≤ d := by
  have hp : qsDiffPoly d P a ≠ 0 := qsDiffPoly_ne_zero d P a hne
  have hsub : (Finset.univ.filter fun c : C => P.eval (ι c) = qsPolySum d a (ι c)).image ι ⊆
      (qsDiffPoly d P a).roots.toFinset := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
    simpa only [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def,
      eval_qsDiffPoly, sub_eq_zero] using (Finset.mem_filter.mp hc).2
  calc (Finset.univ.filter fun c : C => P.eval (ι c) = qsPolySum d a (ι c)).card
      = ((Finset.univ.filter fun c : C =>
          P.eval (ι c) = qsPolySum d a (ι c)).image ι).card :=
        (Finset.card_image_of_injective _ ι.injective).symm
    _ ≤ (qsDiffPoly d P a).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ (qsDiffPoly d P a).roots.card := Multiset.toFinset_card_le _
    _ ≤ (qsDiffPoly d P a).natDegree := Polynomial.card_roots' _
    _ ≤ d := natDegree_qsDiffPoly_le hdeg a

/-- **Degree-`d` QuickSilver soundness over an arbitrary challenge embedding `ι : C ↪ F`**: a fixed
degree-`≤ d` polynomial with nonzero degree-`d` coefficient passes against an arbitrary reply `a`
for a uniform challenge in `C` with probability at most `d / |C|`. -/
theorem toOuterMeasure_qsCheck_le_of_embedding {C : Type} [Fintype C] [Nonempty C]
    {d : ℕ} (ι : C ↪ F) {P : Polynomial F} (hdeg : P.natDegree ≤ d) (hne : P.coeff d ≠ 0)
    (a : Fin d → F) :
    (PMF.uniformOfFintype C).toOuterMeasure {c | P.eval (ι c) = qsPolySum d a (ι c)} ≤
      (d : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞) := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype, div_eq_mul_inv]
  gcongr
  exact_mod_cast card_filter_qsCheck_le ι hdeg hne a

/-- Full-field specialization (`ι = Function.Embedding.refl F`) giving error at most `d / |F|`. -/
theorem toOuterMeasure_qsCheck_le [Fintype F] {d : ℕ} {P : Polynomial F}
    (hdeg : P.natDegree ≤ d) (hne : P.coeff d ≠ 0) (a : Fin d → F) :
    (PMF.uniformOfFintype F).toOuterMeasure {delta | P.eval delta = qsPolySum d a delta} ≤
      (d : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  toOuterMeasure_qsCheck_le_of_embedding (Function.Embedding.refl F) hdeg hne a

private theorem toOuterMeasure_qsHomogSum_bind_le [DecidableEq F] {C ι : Type}
    [Fintype C] [Nonempty C] [Fintype ι] {n d : ℕ} (ι_C : C ↪ F)
    (constraints : ι → MvPolynomial (Fin n) F)
    (hdeg : ∀ i, (constraints i).totalDegree ≤ d) (w v : Fin n → F) (weights : ι → F)
    (hne : ∑ i : ι, weights i * MvPolynomial.eval w (constraints i) ≠ 0)
    (replies : PMF (Fin d → F)) :
    (replies.bind fun reply => (PMF.uniformOfFintype C).bind fun c =>
      PMF.pure (decide ((∑ i : ι, Polynomial.C (weights i) *
        qsHomogPoly d (constraints i) w v).eval (ι_C c) =
          qsPolySum d reply (ι_C c)))).toOuterMeasure {true} ≤
      (d : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞) := by
  classical
  rw [PMF.toOuterMeasure_bind_apply]
  refine PMF.tsum_mul_le_of_forall_le replies fun reply => ?_
  let P_batch : Polynomial F :=
    ∑ i : ι, Polynomial.C (weights i) * qsHomogPoly d (constraints i) w v
  change ((PMF.uniformOfFintype C).map fun c =>
      decide (P_batch.eval (ι_C c) = qsPolySum d reply (ι_C c))).toOuterMeasure {true} ≤ _
  rw [PMF.toOuterMeasure_map_apply]
  have hdeg_b : P_batch.natDegree ≤ d := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    exact (Polynomial.natDegree_C_mul_le _ _).trans (natDegree_qsHomogPoly_le (hdeg i) w v)
  have hcoeff_b : P_batch.coeff d =
      ∑ i : ι, weights i * MvPolynomial.eval w (constraints i) := by
    simp only [P_batch, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
      coeff_qsHomogPoly_eq_eval (hdeg _) w v]
  have hne_b : P_batch.coeff d ≠ 0 := hcoeff_b ▸ hne
  exact (MeasureTheory.measure_mono fun c hc => of_decide_eq_true hc).trans
    (toOuterMeasure_qsCheck_le_of_embedding ι_C hdeg_b hne_b reply)

private theorem uniform_linearBatch_split_le [Fintype F]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (coeff : ι → F) (hfalse : ∃ i₀, coeff i₀ ≠ 0)
    (kernel : (ι → F) → PMF Bool) {ε : ℝ≥0∞}
    (hnoncancel : ∀ r : ι → F, ∑ i, r i * coeff i ≠ 0 →
      (kernel r).toOuterMeasure {true} ≤ ε) :
    ((PMF.uniformOfFintype (ι → F)).bind kernel).toOuterMeasure {true} ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ + (1 - (Fintype.card F : ℝ≥0∞)⁻¹) * ε := by
  classical
  let cancel : Set (ι → F) := {r | ∑ i, r i * coeff i = 0}
  obtain ⟨i₀, hi₀⟩ := hfalse
  have hcancel : (PMF.uniformOfFintype (ι → F)).toOuterMeasure cancel =
      (Fintype.card F : ℝ≥0∞)⁻¹ := by
    simpa only [cancel, one_div] using toOuterMeasure_uniform_linearComb_eq_zero (d := coeff) hi₀
  have hcompl := PMF.toOuterMeasure_compl_le_one_sub
    (PMF.uniformOfFintype (ι → F)) cancel hcancel.ge
  rw [PMF.toOuterMeasure_bind_apply]
  calc ∑' r, PMF.uniformOfFintype (ι → F) r * (kernel r).toOuterMeasure {true}
      ≤ ∑' r, PMF.uniformOfFintype (ι → F) r * (if r ∈ cancel then 1 else ε) := by
        refine tsum_le_tsum fun r => mul_le_mul_of_nonneg_left ?_ zero_le
        split_ifs with hr
        · exact PMF.toOuterMeasure_le_one _ _
        · exact hnoncancel r hr
    _ = (PMF.uniformOfFintype (ι → F)).toOuterMeasure cancel +
        (PMF.uniformOfFintype (ι → F)).toOuterMeasure cancelᶜ * ε := by
        simp only [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right, ← tsum_add]
        refine tsum_congr fun r => ?_
        by_cases hr : r ∈ cancel <;> simp [hr]
    _ ≤ (Fintype.card F : ℝ≥0∞)⁻¹ + (1 - (Fintype.card F : ℝ≥0∞)⁻¹) * ε := by
        rw [hcancel]
        gcongr

/-- Scalar-batched arbitrary-degree QuickSilver soundness: given `t` degree-`≤ d` multivariate
constraints `constraints`, scalar challenge `chi ← uniformOfFintype F`, adaptive reply
`a chi`, and hidden key `c ← uniformOfFintype C` via `ι : C ↪ F`, any false witness passes with
probability at most `t / |F| + d / |C|`, generalizing `ScalarMulCheck` from `d = 2` to any `d`. -/
theorem toOuterMeasure_qsHomogScalarBatch_le [Fintype F] [DecidableEq F] {C : Type}
    [Fintype C] [Nonempty C] {n t d : ℕ} (ι : C ↪ F)
    (constraints : Fin t → MvPolynomial (Fin n) F)
    (hdeg : ∀ i, (constraints i).totalDegree ≤ d) (w v : Fin n → F)
    (hfalse : ∃ i, MvPolynomial.eval w (constraints i) ≠ 0)
    (a : F → PMF (Fin d → F)) :
    (do
      let chi ← PMF.uniformOfFintype F
      let reply ← a chi
      let c ← PMF.uniformOfFintype C
      let P_batch := ∑ i : Fin t,
        Polynomial.C (quickSilverWeight chi i) * qsHomogPoly d (constraints i) w v
      return decide (P_batch.eval (ι c) = qsPolySum d reply (ι c))).toOuterMeasure {true} ≤
      (t : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) + (d : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞) := by
  classical
  let cancel : Set F :=
    {chi | ∑ i : Fin t, quickSilverWeight chi i * MvPolynomial.eval w (constraints i) = 0}
  have hcancel : (PMF.uniformOfFintype F).toOuterMeasure cancel ≤
      (t : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
    toOuterMeasure_quickSilverWeight_sum_eq_zero_le
      (fun i => MvPolynomial.eval w (constraints i)) hfalse
  let kernel (chi : F) : PMF Bool := do
    let reply ← a chi
    let c ← PMF.uniformOfFintype C
    let P_batch := ∑ i : Fin t,
      Polynomial.C (quickSilverWeight chi i) * qsHomogPoly d (constraints i) w v
    return decide (P_batch.eval (ι c) = qsPolySum d reply (ι c))
  change ((PMF.uniformOfFintype F).bind kernel).toOuterMeasure {true} ≤ _
  rw [PMF.toOuterMeasure_bind_apply]
  calc ∑' chi, PMF.uniformOfFintype F chi * (kernel chi).toOuterMeasure {true}
      ≤ ∑' chi, PMF.uniformOfFintype F chi *
          (if chi ∈ cancel then 1 else (d : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞)) := by
        refine tsum_le_tsum fun chi => mul_le_mul_of_nonneg_left ?_ zero_le
        split_ifs with hchi
        · exact PMF.toOuterMeasure_le_one _ _
        · simpa only [kernel, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure] using
            toOuterMeasure_qsHomogSum_bind_le ι constraints hdeg w v (quickSilverWeight chi)
              hchi (a chi)
    _ = (PMF.uniformOfFintype F).toOuterMeasure cancel +
        (PMF.uniformOfFintype F).toOuterMeasure cancelᶜ *
          ((d : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞)) := by
        simp only [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right, ← tsum_add]
        refine tsum_congr fun chi => ?_
        by_cases hchi : chi ∈ cancel <;> simp [hchi]
    _ ≤ (t : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) +
        1 * ((d : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞)) := by
        gcongr
        exact PMF.toOuterMeasure_le_one _ _
    _ = (t : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) + (d : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞) := by
        rw [one_mul]

/-- Independent-weight arbitrary-degree QuickSilver soundness: given fixed degree-`≤ d`
constraints, witness/mask vectors `(w, v)` violating at least one constraint, uniform independent
weights `r ← uniformOfFintype (ι → F)`, adaptive reply `a r`, and hidden key
`c ← uniformOfFintype C` via `ι_C : C ↪ F`, any false witness passes with probability at most
`1 / |F| + (1 - 1 / |F|) * (d / |C|)`. -/
theorem toOuterMeasure_qsHomogLinearBatch_le [Fintype F] [DecidableEq F] {C ι : Type}
    [Fintype C] [Nonempty C] [Fintype ι] [DecidableEq ι] {n d : ℕ} (ι_C : C ↪ F)
    (constraints : ι → MvPolynomial (Fin n) F)
    (hdeg : ∀ i, (constraints i).totalDegree ≤ d) (w v : Fin n → F)
    (hfalse : ∃ i, MvPolynomial.eval w (constraints i) ≠ 0)
    (a : (ι → F) → PMF (Fin d → F)) :
    (do
      let r ← PMF.uniformOfFintype (ι → F)
      let reply ← a r
      let c ← PMF.uniformOfFintype C
      let P_batch := ∑ i : ι, Polynomial.C (r i) * qsHomogPoly d (constraints i) w v
      return decide (P_batch.eval (ι_C c) = qsPolySum d reply (ι_C c))).toOuterMeasure {true} ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ +
        (1 - (Fintype.card F : ℝ≥0∞)⁻¹) * ((d : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞)) := by
  classical
  refine uniform_linearBatch_split_le (fun i => MvPolynomial.eval w (constraints i)) hfalse
    (fun r => (a r).bind fun reply => (PMF.uniformOfFintype C).bind fun c =>
      PMF.pure (decide ((∑ i : ι, Polynomial.C (r i) * qsHomogPoly d (constraints i) w v).eval
        (ι_C c) = qsPolySum d reply (ι_C c)))) fun r hr => ?_
  exact toOuterMeasure_qsHomogSum_bind_le ι_C constraints hdeg w v r hr (a r)

/-- Single-shot independent-weight soundness of `qsMaskedCheckValue`: for any fixed sender VOLE
vectors `(u, v)` and correction `d_corr : Fin n → F` whose effective committed witness
`w' i := u (Fin.castAdd (d - 1) i) + d_corr i` violates at least one constraint, an adaptive
prover receiving uniform weights `r ← uniformOfFintype (ι → F)` and verified against an
independent hidden key `c ← uniformOfFintype C` via `ι_C : C ↪ F` (where `q := fun j =>
u j * ι_C c + v j`) passes with probability at most `1 / |F| + (1 - 1 / |F|) * (d / |C|)`. -/
theorem toOuterMeasure_qsMaskedCheckValue_le [Fintype F] [DecidableEq F] {C ι : Type}
    [Fintype C] [Nonempty C] [Fintype ι] [DecidableEq ι] {n d : ℕ} (ι_C : C ↪ F)
    (constraints : ι → MvPolynomial (Fin n) F)
    (hdeg : ∀ i, (constraints i).totalDegree ≤ d)
    (u v : Fin (n + (d - 1)) → F) (d_corr : Fin n → F)
    (hfalse : ∃ i, MvPolynomial.eval (fun j => u (Fin.castAdd (d - 1) j) + d_corr j)
      (constraints i) ≠ 0)
    (a : (ι → F) → PMF (Fin d → F)) :
    (do
      let r ← PMF.uniformOfFintype (ι → F)
      let reply ← a r
      let c ← PMF.uniformOfFintype C
      let q : Fin (n + (d - 1)) → F := fun j => u j * ι_C c + v j
      return decide (qsMaskedCheckValue d constraints (ι_C c) q d_corr r =
        qsPolySum d reply (ι_C c))).toOuterMeasure {true} ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ +
        (1 - (Fintype.card F : ℝ≥0∞)⁻¹) * ((d : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞)) := by
  let w' : Fin n → F := fun j => u (Fin.castAdd (d - 1) j) + d_corr j
  let v_w : Fin n → F := fun j => v (Fin.castAdd (d - 1) j)
  let mask : Fin d → F :=
    qsMaskCoeff d (fun k => u (Fin.natAdd n k)) (fun k => v (Fin.natAdd n k))
  have hadj : ∀ (delta : F) (i : Fin n),
      voleAdjustReceiver (fun j => u (Fin.castAdd (d - 1) j) * delta +
          v (Fin.castAdd (d - 1) j)) d_corr delta i =
        w' i * delta + v_w i := fun delta i => by
    simp only [voleAdjustReceiver, w', v_w]
    ring
  have hval : ∀ (r : ι → F) (c : C) (reply : Fin d → F),
      (qsMaskedCheckValue d constraints (ι_C c) (fun j => u j * ι_C c + v j) d_corr r =
        qsPolySum d reply (ι_C c)) ↔
      ((∑ i : ι, Polynomial.C (r i) * qsHomogPoly d (constraints i) w' v_w).eval (ι_C c) =
        qsPolySum d (reply - mask) (ι_C c)) := by
    intro r c reply
    have hsum : (∑ i : ι, r i * qsHomogVerifierValue d (constraints i) (ι_C c)
        (voleAdjustReceiver (fun j => u (Fin.castAdd (d - 1) j) * ι_C c +
          v (Fin.castAdd (d - 1) j)) d_corr (ι_C c))) =
        (∑ i : ι, Polynomial.C (r i) * qsHomogPoly d (constraints i) w' v_w).eval (ι_C c) := by
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        eval_qsHomogPoly]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [funext (hadj (ι_C c))]
    change (∑ i : ι, r i * qsHomogVerifierValue d (constraints i) (ι_C c) _) +
        qsMaskValue d _ (ι_C c) = qsPolySum d reply (ι_C c) ↔ _
    rw [hsum, qsMaskValue, ← qsPolySum_qsMaskCoeff]
    simp only [qsPolySum, mask, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, eq_sub_iff_add_eq]
  have heq : (do
        let r ← PMF.uniformOfFintype (ι → F)
        let reply ← a r
        let c ← PMF.uniformOfFintype C
        let q : Fin (n + (d - 1)) → F := fun j => u j * ι_C c + v j
        return decide (qsMaskedCheckValue d constraints (ι_C c) q d_corr r =
          qsPolySum d reply (ι_C c))) =
      (do
        let r ← PMF.uniformOfFintype (ι → F)
        let reply ← (a r).map (fun rep => rep - mask)
        let c ← PMF.uniformOfFintype C
        let P_batch := ∑ i : ι, Polynomial.C (r i) * qsHomogPoly d (constraints i) w' v_w
        return decide (P_batch.eval (ι_C c) = qsPolySum d reply (ι_C c))) := by
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_map, Function.comp_def]
    refine congrArg (PMF.bind (PMF.uniformOfFintype (ι → F))) (funext fun r => ?_)
    refine congrArg (PMF.bind (a r)) (funext fun reply => ?_)
    refine congrArg (PMF.bind (PMF.uniformOfFintype C)) (funext fun c => ?_)
    exact congrArg PMF.pure (decide_eq_decide.mpr (hval r c reply))
  rw [heq]
  exact toOuterMeasure_qsHomogLinearBatch_le ι_C constraints hdeg w' v_w hfalse
    fun r => (a r).map fun rep => rep - mask

/-- Exact bijection between grinding-accepted `λ`-bit challenges
(`FAEST.Challenge.grindingAccepted`) and `BitString (λ - w_grind)`. -/
@[expose] def grindingAcceptedEquiv (p : ChallengeParams) :
    {c : BitString p.securityBits // grindingAccepted p c = true} ≃
      BitString p.nonGrindingBits where
  toFun c j := c.1 ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.sub_le _ _)⟩
  invFun x :=
    ⟨fun idx => if h : idx.val < p.nonGrindingBits then x ⟨idx.val, h⟩ else false, by
      rw [grindingAccepted_eq_true_iff]
      intro j
      have hnot : ¬ p.nonGrindingBits + j.val < p.nonGrindingBits := by omega
      simp [hnot]⟩
  left_inv c := by
    ext idx
    by_cases h : idx.val < p.nonGrindingBits
    · simp [h]
    · simp only [h, ↓reduceDIte]
      have hsub : p.nonGrindingBits + (idx.val - p.nonGrindingBits) = idx.val := by omega
      let j : Fin p.grindingBits := ⟨idx.val - p.nonGrindingBits, by
        have := idx.isLt
        have := p.grindingBits_le
        simp only [ChallengeParams.nonGrindingBits] at *
        omega⟩
      have hgc := (grindingAccepted_eq_true_iff p c.1).mp c.2 j
      have hidx : (⟨p.nonGrindingBits + j.val, by
          have hj := j.isLt
          have hgrind := p.grindingBits_le
          simp only [ChallengeParams.nonGrindingBits]
          omega⟩ : Fin p.securityBits) = idx := Fin.ext hsub
      rw [hidx] at hgc
      exact hgc.symm
  right_inv x := by
    ext j
    simp [j.isLt]

/-- The subset of grinding-accepted `λ`-bit FAEST challenges is nonempty (witnessed by `0`). -/
instance instNonemptyGrindingAccepted (p : ChallengeParams) :
    Nonempty {c : BitString p.securityBits // grindingAccepted p c = true} :=
  ⟨(grindingAcceptedEquiv p).symm (fun _ => false)⟩

/-- Single-shot soundness conditioned on uniform accepted FAEST grinding challenges: for any
embedding `ι : BitString (λ - w_grind) ↪ F`, acceptance over uniform accepted challenges has
probability at most `d / 2 ^ (λ - w_grind)`. This is a single-shot uniform-challenge bound, not
Fiat–Shamir grinding amplification. -/
theorem toOuterMeasure_qsCheck_grinding_accepted_le (p : ChallengeParams) {d : ℕ}
    (ι : BitString p.nonGrindingBits ↪ F) {P : Polynomial F} (hdeg : P.natDegree ≤ d)
    (hne : P.coeff d ≠ 0) (a : Fin d → F) :
    (PMF.uniformOfFintype
        {c : BitString p.securityBits // grindingAccepted p c = true}).toOuterMeasure
        {c | P.eval (ι (grindingAcceptedEquiv p c)) =
          qsPolySum d a (ι (grindingAcceptedEquiv p c))} ≤
      (d : ℝ≥0∞) / (2 ^ p.nonGrindingBits : ℝ≥0∞) := by
  have hcard : Fintype.card {c : BitString p.securityBits // grindingAccepted p c = true} =
      2 ^ p.nonGrindingBits := by
    rw [Fintype.card_congr (grindingAcceptedEquiv p), BitString.card]
  simpa only [Equiv.toEmbedding_apply, Function.Embedding.trans_apply, hcard,
    Nat.cast_pow, Nat.cast_ofNat] using
    toOuterMeasure_qsCheck_le_of_embedding ((grindingAcceptedEquiv p).toEmbedding.trans ι)
      hdeg hne a

/-- Single-shot soundness over raw uniform `λ`-bit FAEST challenges (including the trailing
`w_grind` zero-bit check): acceptance has probability at most `d / 2 ^ λ` ([BaumEtAl2026FAEST],
Section 5.5, Figure 5.7; cf. Lemma 10.40 for RBR soundness under FAEST parameters). This models
single-shot verifier rejection, not Fiat–Shamir grinding amplification. -/
theorem toOuterMeasure_qsCheck_grinding_raw_le (p : ChallengeParams) {d : ℕ}
    (ι : BitString p.nonGrindingBits ↪ F) {P : Polynomial F} (hdeg : P.natDegree ≤ d)
    (hne : P.coeff d ≠ 0) (a : Fin d → F) :
    (PMF.uniformOfFintype (BitString p.securityBits)).toOuterMeasure
        {c | ∃ h : grindingAccepted p c = true,
          P.eval (ι (grindingAcceptedEquiv p ⟨c, h⟩)) =
            qsPolySum d a (ι (grindingAcceptedEquiv p ⟨c, h⟩))} ≤
      (d : ℝ≥0∞) / (2 ^ p.securityBits : ℝ≥0∞) := by
  classical
  let proj : BitString p.securityBits → BitString p.nonGrindingBits := fun c j =>
    c ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.sub_le _ _)⟩
  have hcard_le : (Finset.univ.filter fun c : BitString p.securityBits =>
      ∃ h : grindingAccepted p c = true,
        P.eval (ι (grindingAcceptedEquiv p ⟨c, h⟩)) =
          qsPolySum d a (ι (grindingAcceptedEquiv p ⟨c, h⟩))).card ≤ d := by
    have hinj : Set.InjOn (fun c : BitString p.securityBits => ι (proj c))
        (Finset.univ.filter fun c : BitString p.securityBits =>
          ∃ h : grindingAccepted p c = true,
            P.eval (ι (grindingAcceptedEquiv p ⟨c, h⟩)) =
              qsPolySum d a (ι (grindingAcceptedEquiv p ⟨c, h⟩))) := by
      intro c₁ hc₁ c₂ hc₂ heq
      obtain ⟨h₁, _⟩ := (Finset.mem_filter.mp hc₁).2
      obtain ⟨h₂, _⟩ := (Finset.mem_filter.mp hc₂).2
      exact congrArg Subtype.val <| (grindingAcceptedEquiv p).injective (a₁ := ⟨c₁, h₁⟩)
        (a₂ := ⟨c₂, h₂⟩) (ι.injective heq)
    have hmap : ((Finset.univ.filter fun c : BitString p.securityBits =>
        ∃ h : grindingAccepted p c = true,
          P.eval (ι (grindingAcceptedEquiv p ⟨c, h⟩)) =
            qsPolySum d a (ι (grindingAcceptedEquiv p ⟨c, h⟩))).image
        (fun c => ι (proj c))) ⊆ (qsDiffPoly d P a).roots.toFinset := by
      intro x hx
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨_, heval⟩ := (Finset.mem_filter.mp hc).2
      rwa [Multiset.mem_toFinset, Polynomial.mem_roots (qsDiffPoly_ne_zero d P a hne),
        Polynomial.IsRoot.def, eval_qsDiffPoly, sub_eq_zero]
    calc _ = ((Finset.univ.filter fun c : BitString p.securityBits =>
          ∃ h : grindingAccepted p c = true,
            P.eval (ι (grindingAcceptedEquiv p ⟨c, h⟩)) =
              qsPolySum d a (ι (grindingAcceptedEquiv p ⟨c, h⟩))).image
          (fun c => ι (proj c))).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (qsDiffPoly d P a).roots.toFinset.card := Finset.card_le_card hmap
      _ ≤ (qsDiffPoly d P a).roots.card := Multiset.toFinset_card_le _
      _ ≤ (qsDiffPoly d P a).natDegree := Polynomial.card_roots' _
      _ ≤ d := natDegree_qsDiffPoly_le hdeg a
  rw [PMF.toOuterMeasure_uniformOfFintype, BitString.card, div_eq_mul_inv]
  gcongr
  · exact_mod_cast hcard_le
  · norm_num [Nat.cast_pow]

end Soundness

/-! ### ACT V1 Domain-Separated Random Linear Combination and Conditional Round-2+3 Composition -/

section ACTV1RLC

/-- Trailing byte `'0' = 0x30` of `vole-mole`'s ACT Spend RLC domain separator `"rata\x00l0"`
([VoleMole2026], `src/dst.hpp:44`,
`ACT_SPEND_COMBINE_DST = make_dst("rata", act::VERSION, 'l', '0')`, appended after `chal2` in
`src/act/spend.hpp:383` and hashed in `src/uov/circuit.hpp:63–64`). -/
@[expose] def actRLCDomainByte : Fin 256 := 0x30

/-- Trailing domain-separator bytes reserved by FAEST v3 ([BaumEtAl2026FAEST], Section 3.3:
`0` for `H_0` BAVC commitment key derivation, `1` for `H_1`, `3..5` for `H_3..H_5`,
`8..11` for `H_2^0..H_2^3`) together with `12` (`H_2^4` in [VoleMole2026], `src/voleith.hpp:126`).
-/
@[expose] def faestTrailingDomainBytes : Finset (Fin 256) := {0, 1, 3, 4, 5, 8, 9, 10, 11, 12}

/-- ACT's RLC trailing byte `0x30` does not collide with the FAEST v3 `H_i` bytes or `vole-mole`'s
`H_2^4 = 12` in `faestTrailingDomainBytes` (`vole-mole`'s own 7-byte tags share `0x30` via a
separate penultimate purpose byte and are outside this single-trailing-byte model). -/
theorem actRLCDomainByte_notMem_faest : actRLCDomainByte ∉ faestTrailingDomainBytes := by
  decide

/-- Fixed-length `n`-byte message (`Fin n → Fin 256`), forming a finite key domain for uniform
random oracle tables. -/
abbrev ByteMsg (n : ℕ) : Type := Fin n → Fin 256

/-- Fixed-length `n`-byte message paired with a trailing FAEST v3 `H_i` / `vole-mole` `H_2^4` byte
in `faestTrailingDomainBytes`. -/
abbrev FaestTaggedMsg (n : ℕ) : Type :=
  ByteMsg n × {b : Fin 256 // b ∈ faestTrailingDomainBytes}

/-- Append trailing domain-separator byte `b` to a fixed-length message `msg : ByteMsg n`,
producing an `(n + 1)`-byte message in `ByteMsg (n + 1)`. -/
@[expose] def appendDomainByteFin {n : ℕ} (b : Fin 256) : ByteMsg n ↪ ByteMsg (n + 1) where
  toFun msg := Fin.snoc (α := fun _ => Fin 256) msg b
  inj' m₁ m₂ h := by
    funext i
    have hi := congrFun h (Fin.castSucc i)
    simpa only [Fin.snoc_castSucc] using hi

/-- Embed a `(msg, b) : FaestTaggedMsg n` pair into `ByteMsg (n + 1)` by appending its trailing
FAEST v3 `H_i` / `H_2^4` separator byte `b.1`. -/
@[expose] def appendFaestDomainByteFin {n : ℕ} : FaestTaggedMsg n ↪ ByteMsg (n + 1) where
  toFun | ⟨msg, b, _⟩ => Fin.snoc (α := fun _ => Fin 256) msg b
  inj' p₁ p₂ h := by
    rcases p₁ with ⟨m₁, b₁, hb₁⟩
    rcases p₂ with ⟨m₂, b₂, hb₂⟩
    refine Prod.ext (funext fun i => ?_) (Subtype.ext ?_)
    · have hi := congrFun h (Fin.castSucc i)
      change Fin.snoc (α := fun _ => Fin 256) m₁ b₁ (Fin.castSucc i) =
        Fin.snoc (α := fun _ => Fin 256) m₂ b₂ (Fin.castSucc i) at hi
      simpa only [Fin.snoc_castSucc] using hi
    · have hlast := congrFun h (Fin.last n)
      change Fin.snoc (α := fun _ => Fin 256) m₁ b₁ (Fin.last n) =
        Fin.snoc (α := fun _ => Fin 256) m₂ b₂ (Fin.last n) at hlast
      simpa only [Fin.snoc_last] using hlast

private theorem last_eq_of_snoc_eq {n : ℕ} {b₁ b₂ : Fin 256} {m₁ m₂ : ByteMsg n}
    (h : Fin.snoc (α := fun _ => Fin 256) m₁ b₁ = Fin.snoc (α := fun _ => Fin 256) m₂ b₂) :
    b₁ = b₂ := by
  have hlast := congrFun h (Fin.last n)
  simpa only [Fin.snoc_last] using hlast

/-- ACT's trailing byte `actRLCDomainByte` (`0x30`) separates `ByteMsg n` RLC queries from all
`FaestTaggedMsg n` queries (FAEST v3 `H_i` bytes plus `vole-mole`'s `H_2^4 = 12`) inside the
shared finite domain `ByteMsg (n + 1)`. -/
theorem disjoint_range_actRLC_faestDomainByteFin (n : ℕ) :
    Disjoint (Set.range (appendDomainByteFin (n := n) actRLCDomainByte))
      (Set.range (appendFaestDomainByteFin (n := n))) := by
  rw [Set.disjoint_left]
  rintro _ ⟨m₁, rfl⟩ ⟨⟨m₂, b⟩, heq⟩
  exact actRLCDomainByte_notMem_faest (last_eq_of_snoc_eq heq ▸ b.2)

/-- Restricting a single uniform random oracle table `H : K_all → V` along embeddings `ι₁, ι₂` with
disjoint ranges produces two independent uniform random oracle tables. -/
theorem uniform_split_of_disjoint_range {K_all K₁ K₂ V : Type*}
    [Fintype K_all] [DecidableEq K_all] [Fintype K₁] [DecidableEq K₁]
    [Fintype K₂] [DecidableEq K₂] [Fintype V] [Nonempty V]
    (ι₁ : K₁ ↪ K_all) (ι₂ : K₂ ↪ K_all) (hdisj : Disjoint (Set.range ι₁) (Set.range ι₂)) :
    (PMF.uniformOfFintype (K_all → V)).map
        (fun H => (fun k₁ => H (ι₁ k₁), fun k₂ => H (ι₂ k₂))) =
      (PMF.uniformOfFintype (K₁ → V)).bind fun H₁ =>
        (PMF.uniformOfFintype (K₂ → V)).map fun H₂ => (H₁, H₂) := by
  let I : Finset K_all := Finset.univ.image ι₁ ∪ Finset.univ.image ι₂
  let fSum : K₁ ⊕ K₂ → I := fun x => match x with
    | .inl k₁ => ⟨ι₁ k₁, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩
    | .inr k₂ => ⟨ι₂ k₂, Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩
  have hfSum : Function.Bijective fSum := by
    refine ⟨fun x₁ x₂ h => ?_, fun ⟨y, hy⟩ => ?_⟩
    · have hval := congrArg Subtype.val h
      rcases x₁ with k₁ | k₁ <;> rcases x₂ with k₂ | k₂
      · exact congrArg Sum.inl (ι₁.injective hval)
      · exact False.elim (Set.disjoint_left.mp hdisj ⟨k₁, rfl⟩ ⟨k₂, hval.symm⟩)
      · exact False.elim (Set.disjoint_left.mp hdisj ⟨k₂, rfl⟩ ⟨k₁, hval⟩)
      · exact congrArg Sum.inr (ι₂.injective hval)
    · rcases Finset.mem_union.mp hy with hy1 | hy2
      · obtain ⟨k₁, _, hk₁⟩ := Finset.mem_image.mp hy1
        exact ⟨.inl k₁, Subtype.ext hk₁⟩
      · obtain ⟨k₂, _, hk₂⟩ := Finset.mem_image.mp hy2
        exact ⟨.inr k₂, Subtype.ext hk₂⟩
  let eIdx : K₁ ⊕ K₂ ≃ I := Equiv.ofBijective fSum hfSum
  let eProd : (I → V) ≃ (K₁ → V) × (K₂ → V) :=
    (Equiv.piCongrLeft' (fun _ => V) eIdx.symm).trans (Equiv.sumArrowEquivProdArrow K₁ K₂ V)
  have hcomp : (fun H : K_all → V => (fun k₁ => H (ι₁ k₁), fun k₂ => H (ι₂ k₂))) =
      eProd ∘ I.restrict := by
    funext H
    ext k <;> rfl
  rw [hcomp, ← PMF.map_comp, PMF.uniformOfFintype_pi_map_restrict I,
    PMF.uniformOfFintype_map_equiv eProd, ← PMF.uniformOfFintype_prod]

section FoldedRLC

variable {F : Type} [CommRing F]

/-- Folded degree-`≤ d` constraint polynomial `∑ j, C (l j) * P j` produced by Round-2 RLC
coefficients `l : Fin m → F`. -/
@[expose] noncomputable def foldedConstraint {m : ℕ} (P : Fin m → Polynomial F)
    (l : Fin m → F) : Polynomial F :=
  ∑ j : Fin m, Polynomial.C (l j) * P j

theorem natDegree_foldedConstraint_le {m d : ℕ} {P : Fin m → Polynomial F}
    (hdeg : ∀ j, (P j).natDegree ≤ d) (l : Fin m → F) :
    (foldedConstraint P l).natDegree ≤ d := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  exact (Polynomial.natDegree_C_mul_le _ _).trans (hdeg j)

theorem coeff_foldedConstraint {m : ℕ} (P : Fin m → Polynomial F) (l : Fin m → F) (d : ℕ) :
    (foldedConstraint P l).coeff d = ∑ j : Fin m, l j * (P j).coeff d := by
  simp only [foldedConstraint, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]

end FoldedRLC

section RLCSoundness

variable {F K S : Type} [Field F] [Fintype F]

private theorem toOuterMeasure_answer_query_le_add_swapped {V : Type}
    [Fintype K] [DecidableEq K] [Fintype V] [Nonempty V] {q : ℕ}
    (M : ProbOracleComp (fun _ : K => V) S) (hbound : ProbOracleComp.IsQueryBounded M q)
    (distK : PMF K) {δ_K : ℝ≥0∞} (hdist : ∀ k₀, distK k₀ ≤ δ_K)
    (body : S → K → V → PMF Bool) {ε : ℝ≥0∞}
    (hbody : ∀ s : S,
      ((PMF.uniformOfFintype V).bind fun v =>
        distK.bind fun k => body s k v).toOuterMeasure {true} ≤ ε) :
    (do
      let H ← PMF.uniformOfFintype (K → V)
      let s ← OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle (fun k => PMF.pure (H k))) M
      let k ← distK
      body s k (H k)).toOuterMeasure {true} ≤ (q : ℝ≥0∞) * δ_K + ε := by
  classical
  let d : K → PMF V := fun _ => PMF.uniformOfFintype V
  let post : S × (K → V) → PMF Bool := fun sh => distK.bind fun k => body sh.1 k (sh.2 k)
  have hcomp := congrArg (PMF.bind · post) (run_interpret_answer_complete_prob d M (fun _ => none))
  have heq_eager : (do
        let H ← PMF.uniformOfFintype (K → V)
        let s ← OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle (fun k => PMF.pure (H k))) M
        let k ← distK
        body s k (H k)) =
      (ProbOracleComp.runWith (memoize d) M []).bind fun sc =>
        distK.bind fun k => (complete d (ofList sc.2)).bind fun H => body sc.1 k (H k) := by
    have hcomp' : (ProbOracleComp.runWith (answer d) M (fun _ => none)).bind (fun sc =>
          (complete d sc.2).bind fun H => distK.bind fun k => body sc.1 k (H k)) =
        (PMF.uniformOfFintype (K → V)).bind fun H =>
          (OracleComp.interpret
            (OracleComp.sumHandler ProbComp.unifOracle (fun k => PMF.pure (H k))) M).bind
            fun s => distK.bind fun k => body s k (H k) := by
      simpa only [PMF.monad_bind_eq_bind, PMF.bind_bind, PMF.bind_map, Function.comp_def,
        complete_empty, d, PMF.pi_uniformOfFintype, post] using hcomp
    have hmemo := congrArg
      (PMF.bind · (fun sc : S × Cache (fun _ : K => V) =>
        (complete d sc.2).bind fun H => distK.bind fun k => body sc.1 k (H k)))
      (run_interpret_memoize_prob d M [])
    simp only [PMF.bind_map, ofList_nil] at hmemo
    simp only [PMF.monad_bind_eq_bind, ← hcomp', ← hmemo, Function.comp_def]
    congr 1 with sc : 1
    exact PMF.bind_comm _ _ _
  rw [heq_eager, PMF.toOuterMeasure_apply_singleton]
  refine PMF.bind_apply_le_on_support _ fun sc hsc => ?_
  rcases sc with ⟨s, cache⟩
  obtain ⟨hlen, _⟩ := memoize_cache_bounds_prob d M (fun _ => 0) q 0 hbound
    (ProbOracleComp.QueriesSatisfy.of_forall (fun _ => le_rfl) M) [] cache s hsc
  have hcache_le : cache.length ≤ q := by simpa using hlen
  let T : Finset K := Finset.univ.filter fun k : K => (cache.lookup k).isSome = true
  have hT_card : T.card ≤ q := (card_filter_lookup_isSome_le cache).trans hcache_le
  let g : K → ℝ≥0∞ := fun k => ((PMF.uniformOfFintype V).bind fun v => body s k v) true
  have hpt : ∀ k : K,
      ((complete d (ofList cache)).bind fun H => body s k (H k)) true ≤
        (if k ∈ T then (1 : ℝ≥0∞) else 0) + g k := by
    intro k
    have hproj : ((complete d (ofList cache)).bind fun H => body s k (H k)) =
        (((ofList cache k).elim (d k) PMF.pure).bind fun v => body s k v) := by
      rw [← PMF.pi_map_eval (fun k' => (ofList cache k').elim (d k') PMF.pure) k,
        PMF.bind_map]
      rfl
    rw [hproj]
    cases hlook : cache.lookup k with
    | some v =>
      have hkT : k ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ k, by rw [hlook]; rfl⟩
      simp only [hkT, ↓reduceIte]
      exact (PMF.coe_le_one _ _).trans le_self_add
    | none =>
      have hkT : k ∉ T := by
        simp only [T, Finset.mem_filter, hlook, Option.isSome_none, Bool.false_eq_true, and_false,
          not_false_eq_true]
      simp [hkT, show ofList cache k = none from hlook, d, g]
  rw [PMF.bind_apply]
  calc ∑' k, distK k * ((complete d (ofList cache)).bind fun H => body s k (H k)) true
      ≤ ∑' k, (distK k * (if k ∈ T then (1 : ℝ≥0∞) else 0) + distK k * g k) := by
        refine tsum_le_tsum fun k => ?_
        exact (mul_le_mul_right (hpt k) _).trans_eq (mul_add _ _ _)
    _ = (∑' k, distK k * (if k ∈ T then (1 : ℝ≥0∞) else 0)) + ∑' k, distK k * g k := by
        exact tsum_add
    _ ≤ (q : ℝ≥0∞) * δ_K + ε := by
        refine add_le_add ?_ ?_
        · rw [tsum_eq_sum (s := T) fun k hk => by simp only [hk, ↓reduceIte, mul_zero]]
          calc ∑ k ∈ T, distK k * (if k ∈ T then (1 : ℝ≥0∞) else 0)
              = ∑ k ∈ T, distK k := Finset.sum_congr rfl fun k hk => by simp [hk]
            _ ≤ ∑ _k ∈ T, δ_K := Finset.sum_le_sum fun k _ => hdist k
            _ = (T.card : ℝ≥0∞) * δ_K := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (q : ℝ≥0∞) * δ_K := by gcongr
        · dsimp only [g]
          rw [← PMF.bind_apply, PMF.bind_comm, ← PMF.toOuterMeasure_apply_singleton]
          exact hbody s

private theorem toOuterMeasure_domainSeparated_query_le_add_swapped
    {K_all K₁ K₂ V : Type} [Fintype K_all] [DecidableEq K_all] [Fintype V] [Nonempty V]
    {q : ℕ} (ι₁ : K₁ ↪ K_all) (ι₂ : K₂ ↪ K_all)
    (hdisj : Disjoint (Set.range ι₁) (Set.range ι₂))
    (M : ProbOracleComp ((fun _ : K₁ => V) ⊕ₒ (fun _ : K₂ => V)) S)
    (hbound : OracleComp.IsCostBounded
      (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0))) M q)
    (distK : PMF K₁) {δ_K : ℝ≥0∞} (hdist : ∀ k₀, distK k₀ ≤ δ_K)
    (body : S → K₁ → V → PMF Bool) {ε : ℝ≥0∞}
    (hbody : ∀ s : S,
      ((PMF.uniformOfFintype V).bind fun v =>
        distK.bind fun k => body s k v).toOuterMeasure {true} ≤ ε) :
    (do
      let H ← PMF.uniformOfFintype (K_all → V)
      let s ← OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle
          (OracleComp.sumHandler (fun k₁ => PMF.pure (H (ι₁ k₁)))
            (fun k₂ => PMF.pure (H (ι₂ k₂))))) M
      let k ← distK
      body s k (H (ι₁ k))).toOuterMeasure {true} ≤ (q : ℝ≥0∞) * δ_K + ε := by
  classical
  have : Finite K₁ := Finite.of_injective ι₁ ι₁.injective
  have : Finite K₂ := Finite.of_injective ι₂ ι₂.injective
  let : Fintype K₁ := Fintype.ofFinite K₁
  let : Fintype K₂ := Fintype.ofFinite K₂
  let split : (K_all → V) → (K₁ → V) × (K₂ → V) :=
    fun H => (fun k₁ => H (ι₁ k₁), fun k₂ => H (ι₂ k₂))
  let post : (K₁ → V) × (K₂ → V) → PMF Bool := fun H₁₂ => do
    let s ← OracleComp.interpret
      (OracleComp.sumHandler ProbComp.unifOracle
        (OracleComp.sumHandler (fun k₁ => PMF.pure (H₁₂.1 k₁))
          (fun k₂ => PMF.pure (H₁₂.2 k₂)))) M
    let k ← distK
    body s k (H₁₂.1 k)
  have hfactor :
      (do
        let H ← PMF.uniformOfFintype (K_all → V)
        let s ← OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle
            (OracleComp.sumHandler (fun k₁ => PMF.pure (H (ι₁ k₁)))
              (fun k₂ => PMF.pure (H (ι₂ k₂))))) M
        let k ← distK
        body s k (H (ι₁ k))) =
      ((PMF.uniformOfFintype (K₂ → V)).bind fun H₂ =>
        (PMF.uniformOfFintype (K₁ → V)).bind fun H₁ => post (H₁, H₂)) := by
    calc (PMF.uniformOfFintype (K_all → V)).bind (fun H => post (split H))
        = ((PMF.uniformOfFintype (K_all → V)).map split).bind post := by rw [PMF.bind_map]; rfl
      _ = ((PMF.uniformOfFintype (K₁ → V)).bind fun H₁ =>
            (PMF.uniformOfFintype (K₂ → V)).map fun H₂ => (H₁, H₂)).bind post := by
          rw [uniform_split_of_disjoint_range ι₁ ι₂ hdisj]
      _ = (PMF.uniformOfFintype (K₁ → V)).bind fun H₁ =>
            (PMF.uniformOfFintype (K₂ → V)).bind fun H₂ => post (H₁, H₂) := by
          simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
      _ = _ := PMF.bind_comm _ _ _
  rw [hfactor, PMF.toOuterMeasure_bind_apply]
  refine PMF.tsum_mul_le_of_forall_le _ fun H₂ => ?_
  let M' : ProbOracleComp (fun _ : K₁ => V) S :=
    OracleComp.interpret
      (OracleComp.sumHandler
        (fun u : ℕ => OracleComp.query (spec := probOracleSpec (fun _ : K₁ => V)) (Sum.inl u))
        (OracleComp.sumHandler (fun k₁ => ProbOracleComp.query k₁) (fun k₂ => pure (H₂ k₂))))
      M
  have hbound' : ProbOracleComp.IsQueryBounded M' q := by
    refine OracleComp.IsCostBounded.interpret (fun q' => ?_) hbound
    rcases q' with u | (k₁ | k₂)
    · simpa [OracleComp.sumHandler] using
        OracleComp.IsCostBounded.query (spec := probOracleSpec (fun _ : K₁ => V))
          (cost := Sum.elim (fun _ => 0) (fun _ => 1)) (Sum.inl u)
    · simpa [OracleComp.sumHandler] using
        ProbOracleComp.IsQueryBounded.query (spec := fun _ : K₁ => V) k₁
    · simpa [OracleComp.sumHandler] using
        OracleComp.IsCostBounded.pure (cost := Sum.elim (fun _ => 0) (fun _ => 1)) (H₂ k₂) 0
  have hfun : (fun H₁ : K₁ → V => post (H₁, H₂)) = fun H₁ =>
      (do
        let s ← OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle (fun k₁ => PMF.pure (H₁ k₁))) M'
        let k ← distK
        body s k (H₁ k)) := funext fun H₁ => by
    dsimp only [post, M']
    congr 1
    rw [OracleComp.interpret_interpret]
    congr 1 with q'
    rcases q' with u | (k₁ | k₂) <;>
      simp [OracleComp.sumHandler, ProbOracleComp.query]
  simpa only [hfun, PMF.monad_bind_eq_bind] using
    toOuterMeasure_answer_query_le_add_swapped M' hbound' distK hdist body hbody

private theorem actV1_qs_inner_le {C : Type}
    [DecidableEq F] [Fintype C] [Nonempty C] {m d : ℕ} (ι : C ↪ F)
    (distK : PMF K) (P : Fin m → Polynomial F)
    (Q : K → (Fin m → F) → Polynomial F) (hdegQ : ∀ k l, (Q k l).natDegree ≤ d)
    (a : K → (Fin m → F) → Fin d → F)
    (ZKAccepts : K → (Fin m → F) → Prop) [∀ k l, Decidable (ZKAccepts k l)]
    {ε_zk : ℝ≥0∞}
    (hzk : ∀ l : Fin m → F, (foldedConstraint P l).coeff d ≠ 0 →
      distK.toOuterMeasure {k | ZKAccepts k l ∧ (Q k l).coeff d = 0} ≤ ε_zk) :
    ((PMF.uniformOfFintype (Fin m → F)).bind fun l =>
      distK.bind fun k => (PMF.uniformOfFintype C).map fun c =>
        decide ((∃ j, (P j).coeff d ≠ 0) ∧ ZKAccepts k l ∧
          (Q k l).eval (ι c) = qsPolySum d (a k l) (ι c))).toOuterMeasure {true} ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ +
        (1 - (Fintype.card F : ℝ≥0∞)⁻¹) * (ε_zk + (d : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞)) := by
  classical
  by_cases hs : ∃ j, (P j).coeff d ≠ 0
  · refine (uniform_linearBatch_split_le (fun j => (P j).coeff d) hs _ fun l hl => ?_).trans_eq
      rfl
    have hl' : (foldedConstraint P l).coeff d ≠ 0 := by
      simpa only [coeff_foldedConstraint] using hl
    rw [PMF.toOuterMeasure_bind_apply]
    have hk_bound : ∀ k : K,
        ((PMF.uniformOfFintype C).map fun c => decide ((∃ j, (P j).coeff d ≠ 0) ∧
          ZKAccepts k l ∧ (Q k l).eval (ι c) = qsPolySum d (a k l) (ι c))).toOuterMeasure
            {true} ≤
          (if ZKAccepts k l ∧ (Q k l).coeff d = 0 then (1 : ℝ≥0∞) else 0) +
            (d : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞) := by
      intro k
      rw [PMF.toOuterMeasure_map_apply]
      by_cases hzk_bad : ZKAccepts k l ∧ (Q k l).coeff d = 0
      · simp only [hzk_bad]
        exact (PMF.toOuterMeasure_le_one _ _).trans le_self_add
      · simp only [hzk_bad, ↓reduceIte, zero_add]
        by_cases hacc : ZKAccepts k l
        · have hne : (Q k l).coeff d ≠ 0 := fun hz => hzk_bad ⟨hacc, hz⟩
          refine (MeasureTheory.measure_mono fun c hc => ?_).trans
            (toOuterMeasure_qsCheck_le_of_embedding ι (hdegQ k l) hne (a k l))
          exact (of_decide_eq_true hc).2.2
        · rw [PMF.toOuterMeasure_apply]
          simp [hacc]
    calc ∑' k, distK k * ((PMF.uniformOfFintype C).map fun c => decide _).toOuterMeasure {true}
        ≤ ∑' k, (distK k * (if ZKAccepts k l ∧ (Q k l).coeff d = 0 then (1 : ℝ≥0∞) else 0) +
            distK k * ((d : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞))) := by
          refine tsum_le_tsum fun k => ?_
          exact (mul_le_mul_right (hk_bound k) _).trans_eq (mul_add _ _ _)
      _ = (∑' k, distK k * (if ZKAccepts k l ∧ (Q k l).coeff d = 0 then (1 : ℝ≥0∞) else 0)) +
            (∑' k, distK k * ((d : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞))) := tsum_add
      _ ≤ ε_zk + (d : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞) := by
          refine add_le_add ?_ ?_
          · have hmem : (∑' k, distK k *
                (if ZKAccepts k l ∧ (Q k l).coeff d = 0 then (1 : ℝ≥0∞) else 0)) =
                distK.toOuterMeasure {k | ZKAccepts k l ∧ (Q k l).coeff d = 0} := by
              rw [PMF.toOuterMeasure_eq_tsum_mul_indicator]
              refine tsum_congr fun k => ?_
              by_cases hk : ZKAccepts k l ∧ (Q k l).coeff d = 0 <;> simp [hk]
            rw [hmem]
            exact hzk l hl'
          · rw [ENNReal.tsum_mul_right, distK.tsum_coe, one_mul]
  · simp [hs]

/-- Conditional step (Round-2 + Round-3 interactive QuickSilver): given an adaptive `q`-query
adversary `M` outputting degree-`≤ d` constraint polynomials `P s : Fin m → Polynomial F`, and an
auxiliary Round-2 polynomial `Q s k l` of degree `≤ d` and acceptance predicate `ZKAccepts s k l`
whose cheating event `ZKAccepts s k l ∧ (Q s k l).coeff d = 0` has `distK`-probability at most
`ε_zk` whenever `(foldedConstraint (P s) l).coeff d ≠ 0`, joint Round-2+3 verification succeeds
with probability at most `q * δ_K + (1 / |F| + (1 - 1 / |F|) * (ε_zk + d / |C|))`. This models a
single-shot interactive step conditional on `hzk` and `hdegQ`; it does not verify how Round 2 binds
`Q` to `P` and `l`, nor does it model Fiat–Shamir soundness. -/
theorem toOuterMeasure_actV1_qs_of_zkBinding_le {C : Type} [Fintype K] [DecidableEq K]
    [DecidableEq F] [Fintype C] [Nonempty C] {m q d : ℕ} (ι : C ↪ F)
    (M : ProbOracleComp (fun _ : K => Fin m → F) S) (hbound : ProbOracleComp.IsQueryBounded M q)
    (distK : PMF K) {δ_K : ℝ≥0∞} (hdist : ∀ k₀, distK k₀ ≤ δ_K)
    (P : S → Fin m → Polynomial F)
    (Q : S → K → (Fin m → F) → Polynomial F) (hdegQ : ∀ s k l, (Q s k l).natDegree ≤ d)
    (a : S → K → (Fin m → F) → Fin d → F)
    (ZKAccepts : S → K → (Fin m → F) → Prop) [∀ s k l, Decidable (ZKAccepts s k l)]
    {ε_zk : ℝ≥0∞}
    (hzk : ∀ s : S, ∀ l : Fin m → F, (foldedConstraint (P s) l).coeff d ≠ 0 →
      distK.toOuterMeasure {k | ZKAccepts s k l ∧ (Q s k l).coeff d = 0} ≤ ε_zk) :
    (do
      let H ← PMF.uniformOfFintype (K → Fin m → F)
      let s ← OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle (fun k => PMF.pure (H k))) M
      let k ← distK
      let l := H k
      let c ← PMF.uniformOfFintype C
      return decide ((∃ j, (P s j).coeff d ≠ 0) ∧ ZKAccepts s k l ∧
        (Q s k l).eval (ι c) = qsPolySum d (a s k l) (ι c))).toOuterMeasure {true} ≤
      (q : ℝ≥0∞) * δ_K + ((Fintype.card F : ℝ≥0∞)⁻¹ +
        (1 - (Fintype.card F : ℝ≥0∞)⁻¹) * (ε_zk + (d : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞))) :=
  toOuterMeasure_answer_query_le_add_swapped M hbound distK hdist
    (fun s k l => (PMF.uniformOfFintype C).map fun c => decide ((∃ j, (P s j).coeff d ≠ 0) ∧
      ZKAccepts s k l ∧ (Q s k l).eval (ι c) = qsPolySum d (a s k l) (ι c)))
    fun s => actV1_qs_inner_le ι distK (P s) (Q s) (hdegQ s) (a s) (ZKAccepts s) (hzk s)

/-- Conditional step (domain-separated single-RO Round-2 + Round-3 interactive QuickSilver):
against a single shared random oracle `H : K_all → Fin m → F` accessed through disjoint embeddings
`ι₁ : K₁ ↪ K_all` (the ACT RLC slice, queried at most `q` times) and `ι₂ : K₂ ↪ K_all` (other
protocol slices, queried arbitrarily many times), any adversary `M` outputting `(P s)` with
Round-2 polynomial `Q s k l` and acceptance `ZKAccepts s k l` satisfies the same conditional bound
`q * δ_K + (1 / |F| + (1 - 1 / |F|) * (ε_zk + d / |C|))` under `hzk` and `hdegQ`. Models a
single-shot interactive step, not Fiat–Shamir soundness. -/
theorem toOuterMeasure_actV1_domainSeparated_qs_of_zkBinding_le {K_all K₁ K₂ C : Type}
    [Fintype K_all] [DecidableEq K_all] [DecidableEq F] [Fintype C] [Nonempty C]
    {m q d : ℕ} (ι₁ : K₁ ↪ K_all) (ι₂ : K₂ ↪ K_all)
    (hdisj : Disjoint (Set.range ι₁) (Set.range ι₂)) (ι : C ↪ F)
    (M : ProbOracleComp ((fun _ : K₁ => Fin m → F) ⊕ₒ (fun _ : K₂ => Fin m → F)) S)
    (hbound : OracleComp.IsCostBounded
      (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0))) M q)
    (distK : PMF K₁) {δ_K : ℝ≥0∞} (hdist : ∀ k₀, distK k₀ ≤ δ_K)
    (P : S → Fin m → Polynomial F)
    (Q : S → K₁ → (Fin m → F) → Polynomial F) (hdegQ : ∀ s k l, (Q s k l).natDegree ≤ d)
    (a : S → K₁ → (Fin m → F) → Fin d → F)
    (ZKAccepts : S → K₁ → (Fin m → F) → Prop) [∀ s k l, Decidable (ZKAccepts s k l)]
    {ε_zk : ℝ≥0∞}
    (hzk : ∀ s : S, ∀ l : Fin m → F, (foldedConstraint (P s) l).coeff d ≠ 0 →
      distK.toOuterMeasure {k | ZKAccepts s k l ∧ (Q s k l).coeff d = 0} ≤ ε_zk) :
    (do
      let H ← PMF.uniformOfFintype (K_all → Fin m → F)
      let s ← OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle
          (OracleComp.sumHandler (fun k₁ => PMF.pure (H (ι₁ k₁)))
            (fun k₂ => PMF.pure (H (ι₂ k₂))))) M
      let k ← distK
      let l := H (ι₁ k)
      let c ← PMF.uniformOfFintype C
      return decide ((∃ j, (P s j).coeff d ≠ 0) ∧ ZKAccepts s k l ∧
        (Q s k l).eval (ι c) = qsPolySum d (a s k l) (ι c))).toOuterMeasure {true} ≤
      (q : ℝ≥0∞) * δ_K + ((Fintype.card F : ℝ≥0∞)⁻¹ +
        (1 - (Fintype.card F : ℝ≥0∞)⁻¹) * (ε_zk + (d : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞))) :=
  toOuterMeasure_domainSeparated_query_le_add_swapped ι₁ ι₂ hdisj M hbound distK hdist
    (fun s k l => (PMF.uniformOfFintype C).map fun c => decide ((∃ j, (P s j).coeff d ≠ 0) ∧
      ZKAccepts s k l ∧ (Q s k l).eval (ι c) = qsPolySum d (a s k l) (ι c)))
    fun s => actV1_qs_inner_le ι distK (P s) (Q s) (hdegQ s) (a s) (ZKAccepts s) (hzk s)

/-- Single-shot interactive folded-polynomial ACT V1 Round-2 + Round-3 QuickSilver check:
instantiating Round 2's check directly with `Q := foldedConstraint (P s) l` eliminates `ZKAccepts`
and `ε_zk = 0`, bounding false-instance acceptance against an adaptive `q`-query adversary `M` by
`q * δ_K + (1 / |F| + (1 - 1 / |F|) * (d / |C|))`. Like `toOuterMeasure_actV1_qs_of_zkBinding_le`,
this models a single-shot interactive Round-2+3 step, not Fiat–Shamir soundness. -/
theorem toOuterMeasure_actV1_foldedQS_le {C : Type} [Fintype K] [DecidableEq K]
    [DecidableEq F] [Fintype C] [Nonempty C] {m q d : ℕ} (ι : C ↪ F)
    (M : ProbOracleComp (fun _ : K => Fin m → F) S) (hbound : ProbOracleComp.IsQueryBounded M q)
    (distK : PMF K) {δ_K : ℝ≥0∞} (hdist : ∀ k₀, distK k₀ ≤ δ_K)
    (P : S → Fin m → Polynomial F) (hdegP : ∀ s j, (P s j).natDegree ≤ d)
    (a : S → K → (Fin m → F) → Fin d → F) :
    (do
      let H ← PMF.uniformOfFintype (K → Fin m → F)
      let s ← OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle (fun k => PMF.pure (H k))) M
      let k ← distK
      let l := H k
      let c ← PMF.uniformOfFintype C
      return decide ((∃ j, (P s j).coeff d ≠ 0) ∧
        (foldedConstraint (P s) l).eval (ι c) = qsPolySum d (a s k l) (ι c))).toOuterMeasure
        {true} ≤
      (q : ℝ≥0∞) * δ_K + ((Fintype.card F : ℝ≥0∞)⁻¹ +
        (1 - (Fintype.card F : ℝ≥0∞)⁻¹) * ((d : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞))) := by
  simpa only [true_and, zero_add] using
    toOuterMeasure_actV1_qs_of_zkBinding_le ι M hbound distK hdist P
      (fun s _ l => foldedConstraint (P s) l)
      (fun s _ l => natDegree_foldedConstraint_le (hdegP s) l)
      a (fun _ _ _ => True) (ε_zk := 0) fun _ _ hl => by simp [hl]

end RLCSoundness

end ACTV1RLC

end Cslib.Crypto.Protocols.VOLE
