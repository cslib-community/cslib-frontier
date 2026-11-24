/-
Copyright (c) 2026 Samuel Schlesinger, Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Interpolation
public import Mathlib.Algebra.Field.ZMod
import CslibFrontier.Foundations.Data.Polynomial.LagrangeEval

/-!
# Feldman Verifiable Secret Sharing over Prime-Order Modules

This module formalizes Feldman's verifiable secret sharing (VSS) over `ZMod q` (for prime `q`)
acting on an additive commutative group `G` equipped with a `ZMod q`-module structure (`g : G`
playing the role of the group generator, written additively), building on
`CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Interpolation`:

1. **Polynomial Commitments and Share Verification (`evalCommit`, `commitPoly`, `commit`,
   `verifyShare`):** given a sharing polynomial `f(X) = a₀ + ∑_{k=1}^t r_k X^k` of degree `≤ t`,
   the dealer publishes commitments `C_k = a_k • g` (`k = 0, ..., t`). Party `i` checks its share
   `s : ZMod q` via `s • g = ∑_{k=0}^t (point i)^k • C_k`.
2. **Completeness (`verifyShare_commit`):** every share produced by `Shamir.share` verifies against
   `Feldman.commit`.
3. **Lagrange Interpolation in `G` and Polynomial Soundness (`evalCommit_eq_sum_eval_basis_smul`,
   `reconstruct_smul_eq_commit_zero`, `existsUnique_poly_of_verified`,
   `reconstruct_eq_of_verified`):** for any commitment vector `C : Fin (t + 1) → G` (even from a
   corrupt dealer) and any authorized set `J` (`t + 1 ≤ J.card`) of verified shares, whenever
   `g ≠ 0` (so `· • g` is injective over `ZMod q`), there is a unique polynomial `f` of degree
   `≤ t` such that `C = commitPoly t g f` and every verified share `s` of any party `i` equals
   `f.eval (point i)`. Consequently, any two authorized coalitions of verified shares reconstruct
   the same secret `a₀` satisfying `a₀ • g = C 0`.

## Protocol model and source note

Feldman's 1987 scheme is presented in [BonehShoup2023], Chapter 22 (building on Shamir sharing and
interpolation in the exponent from Lemma 22.1 and Corollary 22.2, pp. 928–929, and Section 22.5.2,
pp. 977–978; exact section and page locators for Feldman VSS in Chapter 22 are not verified from a
rendered PDF). The group is written additively as `[AddCommGroup G] [Module (ZMod q) G]`, matching
`Shamir.Interpolation` and `PrimeOrderGroupFamily`. This module proves algebraic completeness and
unconditional polynomial-consistency soundness given `g ≠ 0`; hiding of `a₀ • g` is computational
under discrete-logarithm/DDH assumptions and is not modeled here.

## Main definitions

* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Feldman.evalCommit`: evaluate a degree-`≤ t`
  group-commitment vector `C : Fin (t + 1) → G` at `x : ZMod q`.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Feldman.commitPoly`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.Feldman.commit`: coefficient-wise commitments to a
  polynomial or Shamir sharing `(r, a₀)`.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Feldman.verifyShare`: Feldman share verification
  predicate `s • g = evalCommit C (params.point i)`.

## Main results

* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Feldman.verifyShare_commit`: honest completeness.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Feldman.evalCommit_eq_sum_eval_basis_smul`:
  Lagrange interpolation of `evalCommit C x` in `G` from any `t + 1 ≤ J.card` parties.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Feldman.reconstruct_smul_eq_commit_zero`:
  any authorized verified coalition reconstructs `a` with `a • g = C 0`.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Feldman.existsUnique_poly_of_verified`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.Feldman.reconstruct_eq_of_verified`: unique
  degree-`≤ t` polynomial extraction and cross-coalition reconstruction consistency for `g ≠ 0`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Chapter 22 (Lemma 22.1, Corollary 22.2, pp. 928–929; Section
  22.5.2, pp. 977–978; exact Feldman VSS locators not verified from rendered PDF).
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing.Shamir.Feldman

open Finset
open Cslib.Crypto.Protocols.SecretSharing.Shamir

/-! ### Commitments and share verification -/

/-- Evaluate a commitment vector `C : Fin (t + 1) → G` at point `x : ZMod q`:
`∑ k : Fin (t + 1), (x ^ k.1) • C k`. -/
@[expose] def evalCommit {q t : ℕ} {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (C : Fin (t + 1) → G) (x : ZMod q) : G :=
  ∑ k : Fin (t + 1), (x ^ k.1) • C k

@[simp] theorem evalCommit_zero {q t : ℕ} {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (C : Fin (t + 1) → G) :
    evalCommit C (0 : ZMod q) = C 0 := by
  simp only [evalCommit, Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    zero_pow (Nat.succ_ne_zero _), zero_smul, sum_const_zero, add_zero]

theorem evalCommit_add {q t : ℕ} {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (C₁ C₂ : Fin (t + 1) → G) (x : ZMod q) :
    evalCommit (C₁ + C₂) x = evalCommit C₁ x + evalCommit C₂ x := by
  simp only [evalCommit, Pi.add_apply, smul_add, sum_add_distrib]

/-- Coefficient-wise commitment vector `k ↦ (f.coeff k.1) • g` of a polynomial `f` up to degree
`t`. -/
@[expose] def commitPoly {q : ℕ} {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (t : ℕ) (g : G) (f : _root_.Polynomial (ZMod q)) : Fin (t + 1) → G :=
  fun k => (f.coeff k.1) • g

/-- Feldman commitment vector `C_0 = a₀ • g`, `C_{k+1} = r_k • g` for Shamir sharing randomness
`r : Randomness params` and secret `a₀ : ZMod q`. -/
@[expose] def commit {q : ℕ} [Fact (Nat.Prime q)] {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) (g : G) (r : Randomness params) (a₀ : ZMod q) :
    Fin (params.threshold + 1) → G :=
  Fin.cons (a₀ • g) (fun k => r k • g)

@[simp] theorem commit_zero {q : ℕ} [Fact (Nat.Prime q)] {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) (g : G) (r : Randomness params) (a₀ : ZMod q) :
    commit params g r a₀ 0 = a₀ • g :=
  rfl

@[simp] theorem commit_succ {q : ℕ} [Fact (Nat.Prime q)] {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) (g : G) (r : Randomness params) (a₀ : ZMod q)
    (k : Fin params.threshold) :
    commit params g r a₀ k.succ = r k • g :=
  rfl

/-- `commit params g r a₀` equals `commitPoly params.threshold g` applied to the Shamir sharing
polynomial `Polynomial.sharingPolynomial a₀ (Polynomial.tailPolynomial params.threshold r)`. -/
theorem commit_eq_commitPoly {q : ℕ} [Fact (Nat.Prime q)] {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) (g : G) (r : Randomness params) (a₀ : ZMod q) :
    commit params g r a₀ =
      commitPoly params.threshold g
        (Polynomial.sharingPolynomial a₀ (Polynomial.tailPolynomial params.threshold r)) := by
  ext k
  refine Fin.cases ?_ ?_ k
  · simp [commitPoly, Polynomial.coeff_zero_sharingPolynomial]
  · intro j
    simp [commitPoly, Polynomial.sharingPolynomial, Polynomial.tailPolynomial_coeff]

/-- Evaluating `commitPoly t g f` at `x` equals `(f.eval x) • g` whenever `f.degree < t + 1`. -/
theorem evalCommit_commitPoly {q t : ℕ} [Fact (Nat.Prime q)]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (g : G) {f : _root_.Polynomial (ZMod q)} (hf : f.degree < (t + 1 : WithBot ℕ))
    (x : ZMod q) :
    evalCommit (commitPoly t g f) x = (f.eval x) • g := by
  have hnat : f.natDegree < t + 1 := by
    by_cases h0 : f = 0
    · rw [h0]; simp
    · rw [_root_.Polynomial.degree_eq_natDegree h0] at hf
      exact_mod_cast hf
  have hev : f.eval x = ∑ k : Fin (t + 1), (x ^ k.1) * f.coeff k.1 := by
    rw [_root_.Polynomial.eval_eq_sum_range' hnat, ← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun k _ => by ring
  simp only [evalCommit, commitPoly, hev, sum_smul, mul_smul]

/-- Evaluating `commit params g r a₀` at `params.point i` equals `(share params r a₀ i) • g`. -/
theorem evalCommit_commit {q : ℕ} [Fact (Nat.Prime q)] {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) (g : G) (r : Randomness params) (a₀ : ZMod q) (i : Party) :
    evalCommit (commit params g r a₀) (params.point i) = (share params r a₀ i) • g := by
  rw [commit_eq_commitPoly, evalCommit_commitPoly g
    (Polynomial.degree_sharingPolynomial_tailPolynomial_lt_succ a₀ params.threshold r)]
  rfl

/-- Feldman share verification predicate: checks `s • g = evalCommit C (params.point i)`. -/
@[expose] def verifyShare {q : ℕ} {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) (g : G) (C : Fin (params.threshold + 1) → G)
    (i : Party) (s : ZMod q) : Prop :=
  s • g = evalCommit C (params.point i)

instance {q : ℕ} {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G] [DecidableEq G]
    (params : Params (ZMod q) Party) (g : G) (C : Fin (params.threshold + 1) → G)
    (i : Party) (s : ZMod q) :
    Decidable (verifyShare params g C i s) :=
  inferInstanceAs (Decidable (_ = _))

/-- **Completeness of Feldman VSS**: every honest Shamir share `share params r a₀ i` verifies
against `commit params g r a₀`. -/
theorem verifyShare_commit {q : ℕ} [Fact (Nat.Prime q)] {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) (g : G) (r : Randomness params) (a₀ : ZMod q) (i : Party) :
    verifyShare params g (commit params g r a₀) i (share params r a₀ i) :=
  (evalCommit_commit params g r a₀ i).symm

/-! ### Lagrange interpolation in `G` and polynomial-consistency soundness -/

/-- **Lagrange interpolation of commitment evaluations in `G`**: for any commitment vector
`C : Fin (params.threshold + 1) → G`, any authorized set `J` (`params.threshold + 1 ≤ J.card`), and
any `x : ZMod q`, `evalCommit C x` is the Lagrange combination of `evalCommit C (params.point j)`
over `j ∈ J`. -/
theorem evalCommit_eq_sum_eval_basis_smul {q : ℕ} [Fact (Nat.Prime q)]
    {Party : Type*} [Fintype Party] [DecidableEq Party]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) (C : Fin (params.threshold + 1) → G)
    {J : Finset Party} (hJ : authorized params J) (x : ZMod q) :
    evalCommit C x =
      ∑ j ∈ J, (Lagrange.basis J params.point j).eval x • evalCommit C (params.point j) := by
  have hinj : Set.InjOn params.point (J : Set Party) := params.point_injective.injOn
  have hterm : ∀ k : Fin (params.threshold + 1),
      (x ^ k.1) • C k =
        ∑ j ∈ J, ((Lagrange.basis J params.point j).eval x * (params.point j) ^ k.1) • C k := by
    intro k
    have hdeg : ((_root_.Polynomial.X : _root_.Polynomial (ZMod q)) ^ k.1).degree < J.card := by
      calc ((_root_.Polynomial.X : _root_.Polynomial (ZMod q)) ^ k.1).degree
          ≤ (k.1 : WithBot ℕ) := _root_.Polynomial.degree_X_pow_le k.1
        _ < (params.threshold + 1 : WithBot ℕ) := by exact_mod_cast k.2
        _ ≤ J.card := by exact_mod_cast hJ
    have hxpow := Lagrange.eval_eq_sum_eval_basis_mul_eval hinj hdeg x
    simp only [_root_.Polynomial.eval_pow, _root_.Polynomial.eval_X] at hxpow
    rw [hxpow, sum_smul]
  calc evalCommit C x
      = ∑ k : Fin (params.threshold + 1),
          ∑ j ∈ J, ((Lagrange.basis J params.point j).eval x * (params.point j) ^ k.1) • C k :=
        sum_congr rfl fun k _ => hterm k
    _ = ∑ j ∈ J, ∑ k : Fin (params.threshold + 1),
          (Lagrange.basis J params.point j).eval x • ((params.point j) ^ k.1 • C k) := by
        rw [sum_comm]
        refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => by rw [mul_smul]
    _ = ∑ j ∈ J, (Lagrange.basis J params.point j).eval x • evalCommit C (params.point j) := by
        refine sum_congr rfl fun j _ => by simp only [evalCommit, smul_sum]

/-- At `x = 0`, `C 0 = evalCommit C 0` is the `lagrangeWeightAtZero`-weighted sum of
`evalCommit C (params.point j)` over any authorized set `J` (shared with `Pedersen`). -/
theorem commit_zero_eq_sum_lagrangeWeightAtZero_smul_evalCommit {q : ℕ} [Fact (Nat.Prime q)]
    {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) (C : Fin (params.threshold + 1) → G)
    {J : Finset Party} (hJ : authorized params J) :
    C 0 =
      ∑ j : J, Polynomial.lagrangeWeightAtZero (fun j : J => params.point j) j •
        evalCommit C (params.point j.1) := by
  classical
  have hev := evalCommit_eq_sum_eval_basis_smul params C hJ 0
  rw [evalCommit_zero] at hev
  rw [hev, ← sum_coe_sort J]
  refine sum_congr rfl fun j _ => ?_
  rw [Polynomial.lagrangeWeightAtZero_eq_eval_basis]
  congr 1
  have hbasis :
      Lagrange.basis (Finset.univ : Finset J) (fun x : J => params.point x.1) j =
        Lagrange.basis J params.point j.1 := by
    unfold Lagrange.basis
    refine Finset.prod_bij (fun x _ => x.1)
      (fun x hx => Finset.mem_erase.mpr
        ⟨fun h => (Finset.mem_erase.mp hx).1 (Subtype.ext h), x.2⟩)
      (fun _ _ _ _ h => Subtype.ext h)
      (fun y hy => ⟨⟨y, (Finset.mem_erase.mp hy).2⟩,
        Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hy).1 (congrArg Subtype.val h),
          Finset.mem_univ _⟩, rfl⟩)
      (fun _ _ => rfl)
  rw [hbasis]

/-- **Secret-commitment consistency**: for any authorized coalition `J` holding verified Feldman
shares `σ : J → ZMod q` against `C`, `(reconstruct params J σ) • g = C 0`. -/
theorem reconstruct_smul_eq_commit_zero_of_verified {q : ℕ} [Fact (Nat.Prime q)]
    {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) (g : G) (C : Fin (params.threshold + 1) → G)
    {J : Finset Party} (hJ : authorized params J) (σ : J → ZMod q)
    (hver : ∀ j : J, verifyShare params g C j.1 (σ j)) :
    (reconstruct params J σ) • g = C 0 := by
  rw [reconstruct, Polynomial.reconstruct_eq_sum_lagrangeWeightAtZero, sum_smul,
    commit_zero_eq_sum_lagrangeWeightAtZero_smul_evalCommit params C hJ]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_smul, smul_comm, ← hver j]

/-- Each entry `C m` of any commitment vector `C : Fin (t + 1) → G` is uniquely determined by
`evalCommit C (params.point j)` over any subset `J₀` of size `t + 1`. -/
private theorem commit_entry_eq_sum_coeff_basis_smul {q : ℕ} [Fact (Nat.Prime q)]
    {Party : Type*} [Fintype Party] [DecidableEq Party]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) (C : Fin (params.threshold + 1) → G)
    {J₀ : Finset Party} (hJ₀ : J₀.card = params.threshold + 1)
    (m : Fin (params.threshold + 1)) :
    C m =
      ∑ j ∈ J₀, (Lagrange.basis J₀ params.point j).coeff m.1 • evalCommit C (params.point j) := by
  have hinj : Set.InjOn params.point (J₀ : Set Party) := params.point_injective.injOn
  have hcoeff : ∀ k : Fin (params.threshold + 1),
      ∑ j ∈ J₀, (params.point j) ^ k.1 * (Lagrange.basis J₀ params.point j).coeff m.1 =
        if k = m then 1 else 0 := by
    intro k
    have hdeg : ((_root_.Polynomial.X : _root_.Polynomial (ZMod q)) ^ k.1).degree < J₀.card := by
      calc ((_root_.Polynomial.X : _root_.Polynomial (ZMod q)) ^ k.1).degree
          ≤ (k.1 : WithBot ℕ) := _root_.Polynomial.degree_X_pow_le k.1
        _ < (params.threshold + 1 : WithBot ℕ) := by exact_mod_cast k.2
        _ = J₀.card := by exact_mod_cast hJ₀.symm
    have hpoly :
        ((_root_.Polynomial.X : _root_.Polynomial (ZMod q)) ^ k.1) =
          Lagrange.interpolate J₀ params.point (fun j => (params.point j) ^ k.1) := by
      simpa only [_root_.Polynomial.eval_pow, _root_.Polynomial.eval_X] using
        Lagrange.eq_interpolate hinj hdeg
    have hc := congrArg (fun p : _root_.Polynomial (ZMod q) => p.coeff m.1) hpoly
    rw [Lagrange.interpolate_apply, _root_.Polynomial.finsetSum_coeff] at hc
    simp only [_root_.Polynomial.coeff_X_pow, _root_.Polynomial.coeff_C_mul] at hc
    rw [← hc]
    simp only [Fin.ext_iff, eq_comm]
  calc C m
      = ∑ k : Fin (params.threshold + 1), (if k = m then (1 : ZMod q) else 0) • C k := by
          simp
    _ = ∑ k : Fin (params.threshold + 1),
          (∑ j ∈ J₀, (params.point j) ^ k.1 * (Lagrange.basis J₀ params.point j).coeff m.1) •
            C k :=
        sum_congr rfl fun k _ => by rw [hcoeff k]
    _ = ∑ j ∈ J₀, ∑ k : Fin (params.threshold + 1),
          (Lagrange.basis J₀ params.point j).coeff m.1 • ((params.point j) ^ k.1 • C k) := by
        simp_rw [sum_smul]
        rw [sum_comm]
        refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => by
          rw [mul_comm, mul_smul]
    _ = ∑ j ∈ J₀, (Lagrange.basis J₀ params.point j).coeff m.1 • evalCommit C (params.point j) := by
        refine sum_congr rfl fun j _ => by simp only [evalCommit, smul_sum]

private theorem smul_injective_of_ne_zero {q : ℕ} [Fact (Nat.Prime q)]
    {G : Type*} [AddCommGroup G] [Module (ZMod q) G] {g : G} (hg : g ≠ 0) :
    Function.Injective (fun x : ZMod q => x • g) := by
  intro x y hxy
  dsimp only at hxy
  have hsub : (x - y) • g = 0 := by
    rw [sub_smul, hxy, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hg)

/-- **Soundness / unique degree-`≤ t` polynomial reconstruction**: given prime `q`, `g ≠ 0` in
`G`, any commitment vector `C : Fin (params.threshold + 1) → G`, and any authorized coalition `J`
holding verified shares `σ : J → ZMod q`, there exists a unique polynomial `f` of degree
`< params.threshold + 1` such that `C = commitPoly params.threshold g f` and every verified share
`s` of any party `i` equals `f.eval (params.point i)`. -/
theorem existsUnique_poly_of_verified {q : ℕ} [Fact (Nat.Prime q)]
    {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommGroup G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) {g : G} (hg : g ≠ 0)
    (C : Fin (params.threshold + 1) → G)
    {J : Finset Party} (hJ : authorized params J) (σ : J → ZMod q)
    (hver : ∀ j : J, verifyShare params g C j.1 (σ j)) :
    ∃! f : _root_.Polynomial (ZMod q),
      f.degree < (params.threshold + 1 : WithBot ℕ) ∧
      C = commitPoly params.threshold g f ∧
      (∀ i : Party, ∀ s : ZMod q, verifyShare params g C i s ↔ s = f.eval (params.point i)) := by
  classical
  obtain ⟨J₀, hJ₀sub, hJ₀card⟩ := Finset.exists_subset_card_eq hJ
  let vals : Party → ZMod q := fun j => if hj : j ∈ J then σ ⟨j, hj⟩ else 0
  let f : _root_.Polynomial (ZMod q) := Lagrange.interpolate J₀ params.point vals
  have hdeg : f.degree < (params.threshold + 1 : WithBot ℕ) := by
    have hlt := Lagrange.degree_interpolate_lt vals (params.point_injective.injOn (s := ↑J₀))
    rwa [hJ₀card] at hlt
  have hC : C = commitPoly params.threshold g f := by
    ext m
    rw [commit_entry_eq_sum_coeff_basis_smul params C hJ₀card m, commitPoly]
    have hfcoeff :
        f.coeff m.1 =
          ∑ j ∈ J₀, vals j * (Lagrange.basis J₀ params.point j).coeff m.1 := by
      simp only [f, Lagrange.interpolate_apply, _root_.Polynomial.finsetSum_coeff,
        _root_.Polynomial.coeff_C_mul]
    rw [hfcoeff, sum_smul]
    refine sum_congr rfl fun j hj₀ => ?_
    have hj : j ∈ J := hJ₀sub hj₀
    have hv : evalCommit C (params.point j) = (vals j) • g := by
      simpa [vals, hj] using (hver ⟨j, hj⟩).symm
    rw [hv, mul_smul, smul_comm]
  have hinj := smul_injective_of_ne_zero (q := q) hg
  have hiff :
      ∀ i : Party, ∀ s : ZMod q, verifyShare params g C i s ↔ s = f.eval (params.point i) := by
    intro i s
    rw [verifyShare, hC, evalCommit_commitPoly g hdeg (params.point i)]
    exact hinj.eq_iff
  refine ⟨f, ⟨hdeg, hC, hiff⟩, ?_⟩
  rintro f' ⟨hdeg', hC', _⟩
  have hcoeffEq : ∀ m : ℕ, m < params.threshold + 1 → f'.coeff m = f.coeff m := by
    intro m hm
    have hm' : (commitPoly params.threshold g f') ⟨m, hm⟩ =
        (commitPoly params.threshold g f) ⟨m, hm⟩ :=
      congrFun (hC'.symm.trans hC) ⟨m, hm⟩
    exact hinj hm'
  have hnat : f.natDegree < params.threshold + 1 := by
    by_cases h0 : f = 0
    · rw [h0]; simp
    · rw [_root_.Polynomial.degree_eq_natDegree h0] at hdeg
      exact_mod_cast hdeg
  have hnat' : f'.natDegree < params.threshold + 1 := by
    by_cases h0 : f' = 0
    · rw [h0]; simp
    · rw [_root_.Polynomial.degree_eq_natDegree h0] at hdeg'
      exact_mod_cast hdeg'
  ext m
  by_cases hm : m < params.threshold + 1
  · exact hcoeffEq m hm
  · rw [_root_.Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),
      _root_.Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- **Cross-coalition reconstruction consistency**: whenever `g ≠ 0` and two authorized coalitions
`J₁, J₂` both hold verified Feldman shares against the same commitment vector `C`, they
reconstruct the exact same secret `reconstruct params J₁ σ₁ = reconstruct params J₂ σ₂`. -/
theorem reconstruct_eq_of_verified {q : ℕ} [Fact (Nat.Prime q)]
    {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommGroup G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) {g : G} (hg : g ≠ 0)
    (C : Fin (params.threshold + 1) → G)
    {J₁ J₂ : Finset Party} (hJ₁ : authorized params J₁) (hJ₂ : authorized params J₂)
    (σ₁ : J₁ → ZMod q) (σ₂ : J₂ → ZMod q)
    (hver₁ : ∀ j : J₁, verifyShare params g C j.1 (σ₁ j))
    (hver₂ : ∀ j : J₂, verifyShare params g C j.1 (σ₂ j)) :
    reconstruct params J₁ σ₁ = reconstruct params J₂ σ₂ := by
  apply smul_injective_of_ne_zero hg
  dsimp only
  rw [reconstruct_smul_eq_commit_zero_of_verified params g C hJ₁ σ₁ hver₁,
    reconstruct_smul_eq_commit_zero_of_verified params g C hJ₂ σ₂ hver₂]

end Cslib.Crypto.Protocols.SecretSharing.Shamir.Feldman
