/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Uniform
public import Cslib.Crypto.Protocols.SecretSharing.Shamir
import CslibFrontier.Foundations.Data.Polynomial.LagrangeEval
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Shamir Secret-Sharing Algebraic Homomorphisms, Multiplicative Property, and Marginal Uniformity

This module extends `Cslib.Crypto.Protocols.SecretSharing.Shamir` with the linear and
multiplicative algebraic homomorphisms of Shamir secret sharing, Lagrange weight functional
identities at zero, and unauthorized-coalition marginal uniformity ([Shamir1979];
[BenOrGoldwasserWigderson1988]; [GennaroRabinRabin1998]; [AsharovLindell2017]; [Goldreich2004];
[KatzLindell2020]):

1. **Shamir Algebraic Homomorphisms and Lagrange Weights at Zero:**
   - Linearity of `Polynomial.tailPolynomial`, `Polynomial.sharingPolynomial`, and `Shamir.share`
     under addition, scalar multiplication, constant shifts, and finite sums (`share_zero`,
     `share_zero_randomness`, `share_add`, `share_smul`, `share_add_const`, `share_sum`).
   - Explicit Lagrange weights at zero (`Polynomial.lagrangeWeightAtZero`) and the
     linear-functional expansion `Polynomial.reconstruct_eq_sum_lagrangeWeightAtZero`, yielding
     linearity of `Polynomial.reconstruct` and `Shamir.reconstruct` (`Polynomial.reconstruct_add`,
     `Polynomial.reconstruct_smul`, `Polynomial.reconstruct_sum`, `reconstruct_add`,
     `reconstruct_smul`, `reconstruct_sum`) and homomorphic secret recovery on authorized
     coalitions (`reconstruct_share_add`, `reconstruct_share_smul`, `reconstruct_share_sum`).
2. **Multiplicative Property of Shamir Shares ($2t < |\text{Party}|$):**
   - Multiplying two degree-$\le t$ Shamir sharing polynomials with secrets $a, b$ and randomness
     $r_1, r_2$ produces a degree-$\le 2t$ sharing polynomial with secret $a \cdot b$ and tail
     coefficient vector `mulTailCoeffs a r₁ b r₂`
     (`sharingPolynomial_mul_eq_sharingPolynomial_mulTailCoeffs`, `eval_sharingPolynomial_mul`).
   - When $2t < |\text{Party}|$ (i.e., $t < n / 2$), Lagrange reconstruction of pointwise share
     products `share params r₁ a i * share params r₂ b i` recovers $a \cdot b$
     (`reconstruct_mul_share_eq_mul`).
3. **Lagrange Share Interpolation and Unauthorized-Coalition Marginal Uniformity:**
   - Given any unauthorized coalition $I \subseteq \text{Party}$ with $|I| \le t$, secret $y$, and
     target coalition shares $\sigma : I \to F$, `interpCoeffs params I hI y σ` interpolates a
     degree-$< t$ tail polynomial whose shares of $y$ restrict to $\sigma$ on $I$
     (`share_interpCoeffs`).
   - Via `uniformOfFintype_map_addHom`, the zero-secret restriction homomorphism
     `shareZeroRestrictHom params I` is surjective for $|I| \le t$, so for every secret $y \in F$
     the marginal distribution of $I$'s Shamir shares under uniform randomness is uniform on
     $I \to F$ (`uniformOfFintype_map_restrict_share`).

## Main definitions

* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.lagrangeWeightAtZero`: explicit Lagrange
  interpolation weight at `0` for evaluation points `x : ι → F`.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.mulTailPolynomial`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.mulTailCoeffs`: degree-$2t$ product tail polynomial
  and coefficient vector.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.interpTailPolynomial`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.interpCoeffs`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.shareZeroRestrictHom`: Lagrange tail interpolation
  and zero-secret coalition restriction homomorphism.

## Main results

* `Cslib.Crypto.Protocols.SecretSharing.Shamir.share_add`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.share_smul`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.share_sum`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct_eq_sum_lagrangeWeightAtZero`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct_add`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct_smul`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct_sum`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial.reconstruct_share_eq_secret`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.reconstruct_add`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.reconstruct_smul`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.reconstruct_sum`: linearity of Shamir sharing and
  Lagrange reconstruction.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.reconstruct_mul_share_eq_mul`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.eval_sharingPolynomial_mul`: multiplicative
  property of Shamir shares for $2t < |\text{Party}|$.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.share_interpCoeffs`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.uniformOfFintype_map_restrict_share`: Lagrange share
  interpolation and marginal uniformity of unauthorized coalitions ($|I| \le t$).

## References

* [A. Shamir, *How to Share a Secret*][Shamir1979].
* [M. Ben-Or, S. Goldwasser, A. Wigderson, *Completeness Theorems for Non-Cryptographic
  Fault-Tolerant Distributed Computation*][BenOrGoldwasserWigderson1988].
* [R. Gennaro, M. O. Rabin, T. Rabin, *Simplified VSS and Fast-Track Multiparty Computations with
  Applications to Threshold Cryptography*][GennaroRabinRabin1998].
* [G. Asharov, Y. Lindell, *A Full Proof of the BGW Protocol for Perfectly Secure Multiparty
  Computation*][AsharovLindell2017].
* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Chapter 7.
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020].
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing.Shamir

namespace Polynomial

variable {F : Type*} [Field F]

/-! ### 1. Polynomial and Lagrange reconstruction linearity -/

/-- `Polynomial.tailPolynomial` maps the zero coefficient vector to the zero polynomial. -/
@[simp] theorem tailPolynomial_zero (n : ℕ) :
    tailPolynomial (F := F) n 0 = 0 := by
  simp [tailPolynomial]

/-- `Polynomial.tailPolynomial` is `F`-linear with respect to scalar multiplication. -/
theorem tailPolynomial_smul (n : ℕ) (c : F) (a : Fin n → F) :
    tailPolynomial (F := F) n (c • a) = c • tailPolynomial n a := by
  simp [tailPolynomial]

/-- `Polynomial.tailPolynomial` commutes with finite sums of coefficient vectors. -/
theorem tailPolynomial_sum {ι : Type*} (S : Finset ι) (n : ℕ) (f : ι → Fin n → F) :
    tailPolynomial (F := F) n (∑ j ∈ S, f j) =
      ∑ j ∈ S, tailPolynomial n (f j) := by
  simp only [tailPolynomial, map_sum, Submodule.coe_sum]

/-- The sharing polynomial with zero secret and zero tail is the zero polynomial. -/
@[simp] theorem sharingPolynomial_zero :
    sharingPolynomial (0 : F) 0 = 0 := by
  simp [sharingPolynomial]

/-- `Polynomial.sharingPolynomial` is additive in the secret and tail polynomial. -/
theorem sharingPolynomial_add (s₁ s₂ : F) (t₁ t₂ : _root_.Polynomial F) :
    sharingPolynomial (s₁ + s₂) (t₁ + t₂) =
      sharingPolynomial s₁ t₁ + sharingPolynomial s₂ t₂ := by
  simp only [sharingPolynomial, map_add]
  ring

/-- `Polynomial.sharingPolynomial` is homogeneous under scalar multiplication by `c : F`. -/
theorem sharingPolynomial_smul (c s : F) (t : _root_.Polynomial F) :
    sharingPolynomial (c * s) (c • t) =
      c • sharingPolynomial s t := by
  simp only [sharingPolynomial, _root_.Polynomial.smul_eq_C_mul, map_mul]
  ring

/-- `Polynomial.sharingPolynomial` commutes with finite sums of secrets and tail polynomials. -/
theorem sharingPolynomial_sum {ι : Type*} (S : Finset ι)
    (s : ι → F) (t : ι → _root_.Polynomial F) :
    sharingPolynomial (∑ j ∈ S, s j) (∑ j ∈ S, t j) =
      ∑ j ∈ S, sharingPolynomial (s j) (t j) := by
  simp only [sharingPolynomial, map_sum, Finset.mul_sum, Finset.sum_add_distrib]

/-- Explicit Lagrange interpolation weight at `0` for evaluation points `x : ι → F`: the constant
coefficient of the `i`-th Lagrange basis polynomial over `Finset.univ`. -/
noncomputable def lagrangeWeightAtZero {ι : Type*} [Fintype ι] (x : ι → F) (i : ι) : F :=
  open scoped Classical in
  (_root_.Lagrange.basis Finset.univ x i).constantCoeff

/-- `Polynomial.reconstruct` is the `F`-linear combination of share values weighted by
`lagrangeWeightAtZero`. -/
theorem reconstruct_eq_sum_lagrangeWeightAtZero {ι : Type*} [Fintype ι] (x σ : ι → F) :
    reconstruct x σ = ∑ i : ι, σ i * lagrangeWeightAtZero x i := by
  classical
  simp [reconstruct, _root_.Lagrange.interpolate_apply, lagrangeWeightAtZero,
    _root_.Polynomial.constantCoeff_apply]

/-- The Lagrange interpolation weight at `0` for `x : ι → F` is nonzero whenever `x` is injective
and takes nonzero values (specialization of `Lagrange.eval_basis_ne_zero` at `0`). -/
theorem lagrangeWeightAtZero_ne_zero {ι : Type*} [Fintype ι] {x : ι → F}
    (hinj : Function.Injective x) (hnz : ∀ i, x i ≠ 0) (i : ι) :
    lagrangeWeightAtZero x i ≠ 0 := by
  classical
  rw [lagrangeWeightAtZero, _root_.Polynomial.constantCoeff_apply,
    _root_.Polynomial.coeff_zero_eq_eval_zero]
  exact _root_.Lagrange.eval_basis_ne_zero hinj.injOn (Finset.mem_univ i)
    fun j _ _ => (hnz j).symm

/-- Reconstructing a single-coordinate vector `Pi.single i c` evaluates to `c` times the Lagrange
weight at `0`. -/
theorem reconstruct_single {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → F) (i : ι) (c : F) :
    reconstruct x (Pi.single i c) = c * lagrangeWeightAtZero x i := by
  simp only [reconstruct_eq_sum_lagrangeWeightAtZero, Pi.single_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- Reconstructing the zero share vector returns `0`. -/
@[simp] theorem reconstruct_zero {ι : Type*} [Fintype ι] (x : ι → F) :
    reconstruct x (0 : ι → F) = 0 := by
  simp [reconstruct_eq_sum_lagrangeWeightAtZero]

/-- `Polynomial.reconstruct` is additive in the share vector `σ`. -/
theorem reconstruct_add {ι : Type*} [Fintype ι] (x σ₁ σ₂ : ι → F) :
    reconstruct x (σ₁ + σ₂) =
      reconstruct x σ₁ + reconstruct x σ₂ := by
  simp only [reconstruct_eq_sum_lagrangeWeightAtZero, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]

/-- `Polynomial.reconstruct` is homogeneous with respect to scalar multiplication. -/
theorem reconstruct_smul {ι : Type*} [Fintype ι] (x : ι → F) (c : F) (σ : ι → F) :
    reconstruct x (c • σ) = c * reconstruct x σ := by
  simp only [reconstruct_eq_sum_lagrangeWeightAtZero, Pi.smul_apply, smul_eq_mul, mul_assoc,
    ← Finset.mul_sum]

/-- `Polynomial.reconstruct` commutes with finite sums of share vectors. -/
theorem reconstruct_sum {ι κ : Type*} [Fintype ι] (S : Finset κ) (x : ι → F) (σ : κ → ι → F) :
    reconstruct x (∑ k ∈ S, σ k) =
      ∑ k ∈ S, reconstruct x (σ k) := by
  simp only [reconstruct_eq_sum_lagrangeWeightAtZero, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-- Reconstructing a Shamir sharing across all parties via `Polynomial.reconstruct params.point`
recovers `secretValue`. -/
@[simp] theorem reconstruct_share_eq_secret {Party : Type*} [Fintype Party]
    (params : Params F Party) (coeffs : Randomness params) (secretValue : F) :
    reconstruct params.point (fun i => share params coeffs secretValue i) =
      secretValue := by
  exact reconstruct_sharingPolynomial_eq_secret params.point_injective <|
    (degree_sharingPolynomial_tailPolynomial_lt_succ secretValue params.threshold coeffs).trans_le
      (mod_cast Nat.succ_le_of_lt params.threshold_lt_card)

end Polynomial

open Cslib.Probability

variable {F Party : Type*} [Field F] [Fintype Party]

/-! ### 2. Shamir secret-sharing algebraic homomorphisms -/

/-- Sharing secret `s` with zero randomness gives constant share `s` at every party. -/
@[simp] theorem share_zero_randomness (params : Params F Party) (s : F) (i : Party) :
    share params 0 s i = s := by
  simp [share]

/-- Sharing secret `0` with zero randomness gives share `0` at every party. -/
theorem share_zero (params : Params F Party) (i : Party) :
    share params 0 0 i = 0 :=
  share_zero_randomness params 0 i

/-- Additive homomorphism of Shamir sharing ([AsharovLindell2017], Section 4.1, addition gates):
adding two share values at party `i` produces party `i`'s share of `s₁ + s₂` under randomness
`r₁ + r₂`. -/
theorem share_add (params : Params F Party) (r₁ r₂ : Randomness params) (s₁ s₂ : F) (i : Party) :
    share params (r₁ + r₂) (s₁ + s₂) i = share params r₁ s₁ i + share params r₂ s₂ i := by
  simp only [share, Polynomial.sharingPolynomial_eval, Polynomial.tailPolynomial_add,
    _root_.Polynomial.eval_add]
  ring

/-- Scalar-multiplication homomorphism of Shamir sharing: scaling party `i`'s share by `c`
produces party `i`'s share of `c * s` under randomness `c • r`. -/
theorem share_smul (params : Params F Party) (c : F) (r : Randomness params) (s : F) (i : Party) :
    share params (c • r) (c * s) i = c * share params r s i := by
  simp only [share, Polynomial.sharingPolynomial_eval, Polynomial.tailPolynomial_smul,
    _root_.Polynomial.eval_smul, smul_eq_mul]
  ring

/-- Adding a public constant `c` to party `i`'s share shifts the shared secret by `c` under the
same randomness `r`. -/
theorem share_add_const (params : Params F Party) (r : Randomness params) (s c : F) (i : Party) :
    share params r (s + c) i = share params r s i + c := by
  simp only [share, Polynomial.sharingPolynomial_eval]
  ring

/-- Multi-party summation homomorphism of Shamir sharing: summing shares across a finite index set
`S` yields the share of `∑ j ∈ S, s j` under randomness `∑ j ∈ S, r j`. -/
theorem share_sum {ι : Type*} (S : Finset ι) (params : Params F Party)
    (r : ι → Randomness params) (s : ι → F) (i : Party) :
    share params (∑ j ∈ S, r j) (∑ j ∈ S, s j) i =
      ∑ j ∈ S, share params (r j) (s j) i := by
  simp only [share, Polynomial.sharingPolynomial_eval, Polynomial.tailPolynomial_sum,
    _root_.Polynomial.eval_finsetSum, Finset.mul_sum, Finset.sum_add_distrib]

/-- Reconstructing the zero coalition share vector returns `0`. -/
@[simp] theorem reconstruct_zero (params : Params F Party) (s : Finset Party) :
    reconstruct params s (0 : s → F) = 0 :=
  Polynomial.reconstruct_zero (fun i : s => params.point i)

/-- `Shamir.reconstruct` is additive in the coalition's share vector. -/
theorem reconstruct_add (params : Params F Party) (s : Finset Party) (σ₁ σ₂ : s → F) :
    reconstruct params s (σ₁ + σ₂) = reconstruct params s σ₁ + reconstruct params s σ₂ :=
  Polynomial.reconstruct_add (fun i : s => params.point i) σ₁ σ₂

/-- `Shamir.reconstruct` commutes with scalar multiplication of the coalition's share vector. -/
theorem reconstruct_smul (params : Params F Party) (s : Finset Party) (c : F) (σ : s → F) :
    reconstruct params s (c • σ) = c * reconstruct params s σ :=
  Polynomial.reconstruct_smul (fun i : s => params.point i) c σ

/-- `Shamir.reconstruct` commutes with finite sums of coalition share vectors. -/
theorem reconstruct_sum {κ : Type*} (S : Finset κ) (params : Params F Party)
    (s : Finset Party) (σ : κ → s → F) :
    reconstruct params s (∑ k ∈ S, σ k) = ∑ k ∈ S, reconstruct params s (σ k) :=
  Polynomial.reconstruct_sum S (fun i : s => params.point i) σ

/-- Reconstructing a Shamir sharing over any authorized coalition `s`
(`params.threshold + 1 ≤ s.card`) recovers `secretValue` directly, without requiring a
`TailSampler`. -/
@[simp] theorem reconstruct_share_eq_secret (params : Params F Party)
    (coeffs : Randomness params) (secretValue : F) {s : Finset Party}
    (hs : authorized params s) :
    reconstruct params s (fun i : s => share params coeffs secretValue i) = secretValue := by
  have hdeg :
      (Polynomial.sharingPolynomial secretValue
          (Polynomial.tailPolynomial params.threshold coeffs)).degree < Fintype.card s :=
    (Polynomial.degree_sharingPolynomial_tailPolynomial_lt_succ
        secretValue params.threshold coeffs).trans_le
      (by rw [Fintype.card_coe]; exact_mod_cast hs)
  exact Polynomial.reconstruct_sharingPolynomial_eq_secret
    (fun _ _ hij => Subtype.ext (params.point_injective hij)) hdeg

/-- Reconstructing the pointwise sum of two Shamir sharings over any authorized coalition `s`
recovers the sum of the secrets `s₁ + s₂`. -/
theorem reconstruct_share_add (params : Params F Party) (r₁ r₂ : Randomness params) (s₁ s₂ : F)
    {s : Finset Party} (hs : authorized params s) :
    reconstruct params s (fun i : s => share params r₁ s₁ i + share params r₂ s₂ i) = s₁ + s₂ := by
  simp_rw [← share_add params r₁ r₂ s₁ s₂]
  exact reconstruct_share_eq_secret params (r₁ + r₂) (s₁ + s₂) hs

/-- Reconstructing a scalar multiple of a Shamir sharing over any authorized coalition `s`
recovers `c * secretValue`. -/
theorem reconstruct_share_smul (params : Params F Party) (c : F) (r : Randomness params)
    (secretValue : F) {s : Finset Party} (hs : authorized params s) :
    reconstruct params s (fun i : s => c * share params r secretValue i) = c * secretValue := by
  simp_rw [← share_smul params c r secretValue]
  exact reconstruct_share_eq_secret params (c • r) (c * secretValue) hs

/-- Reconstructing the pointwise sum of a finite family of Shamir sharings over any authorized
coalition `s` recovers the sum of the secrets. -/
theorem reconstruct_share_sum {κ : Type*} (S : Finset κ) (params : Params F Party)
    (r : κ → Randomness params) (sec : κ → F) {s : Finset Party} (hs : authorized params s) :
    reconstruct params s (fun i : s => ∑ k ∈ S, share params (r k) (sec k) i) =
      ∑ k ∈ S, sec k := by
  simp_rw [← share_sum S params r sec]
  exact reconstruct_share_eq_secret params (∑ k ∈ S, r k) (∑ k ∈ S, sec k) hs

/-! ### 3. Multiplicative property of Shamir shares -/

/-- Tail polynomial of the product of two Shamir sharing polynomials
`sharingPolynomial a t₁ * sharingPolynomial b t₂`. -/
noncomputable def mulTailPolynomial (a : F) (t₁ : _root_.Polynomial F)
    (b : F) (t₂ : _root_.Polynomial F) : _root_.Polynomial F :=
  _root_.Polynomial.C a * t₂ + _root_.Polynomial.C b * t₁ + _root_.Polynomial.X * (t₁ * t₂)

/-- Multiplying two Shamir sharing polynomials with secrets `a` and `b` yields a Shamir sharing
polynomial with secret `a * b` and tail `mulTailPolynomial a t₁ b t₂`. -/
theorem sharingPolynomial_mul_sharingPolynomial (a : F) (t₁ : _root_.Polynomial F)
    (b : F) (t₂ : _root_.Polynomial F) :
    Polynomial.sharingPolynomial a t₁ * Polynomial.sharingPolynomial b t₂ =
      Polynomial.sharingPolynomial (a * b) (mulTailPolynomial a t₁ b t₂) := by
  simp only [Polynomial.sharingPolynomial, mulTailPolynomial, map_mul]
  ring

/-- If `t₁` and `t₂` have degree `< t`, then `mulTailPolynomial a t₁ b t₂` has degree `< 2 * t`. -/
theorem degree_mulTailPolynomial_lt {t : ℕ} (a : F) {t₁ : _root_.Polynomial F}
    (ht₁ : t₁.degree < t) (b : F) {t₂ : _root_.Polynomial F} (ht₂ : t₂.degree < t) :
    (mulTailPolynomial a t₁ b t₂).degree < (2 * t : WithBot ℕ) := by
  rcases t with _ | k
  · have h0 {p : _root_.Polynomial F} (hp : p.degree < (0 : ℕ)) : p = 0 :=
      _root_.Polynomial.degree_eq_bot.mp (WithBot.lt_coe_bot.mp (by simpa using hp))
    simp [mulTailPolynomial, h0 ht₁, h0 ht₂]
  · have hle {p : _root_.Polynomial F} (hp : p.degree < ((k + 1 : ℕ) : WithBot ℕ)) :
        p.degree ≤ (k : WithBot ℕ) := by
      cases h : p.degree with
      | bot => exact bot_le
      | coe d =>
        exact WithBot.coe_le_coe.mpr (Nat.lt_succ_iff.mp (WithBot.coe_lt_coe.mp (h ▸ hp)))
    have hlt : ((k + 1 : ℕ) : WithBot ℕ) ≤ (2 * (k + 1 : ℕ) : WithBot ℕ) := by
      exact_mod_cast (by omega : k + 1 ≤ 2 * (k + 1))
    have hC (c : F) (p : _root_.Polynomial F) : (_root_.Polynomial.C c * p).degree ≤ p.degree :=
      _root_.Polynomial.smul_eq_C_mul c ▸ _root_.Polynomial.degree_smul_le c p
    have h1 : (_root_.Polynomial.C a * t₂).degree < (2 * (k + 1 : ℕ) : WithBot ℕ) :=
      (hC a t₂).trans_lt (ht₂.trans_le hlt)
    have h2 : (_root_.Polynomial.C b * t₁).degree < (2 * (k + 1 : ℕ) : WithBot ℕ) :=
      (hC b t₁).trans_lt (ht₁.trans_le hlt)
    have h3 : (_root_.Polynomial.X * (t₁ * t₂)).degree < (2 * (k + 1 : ℕ) : WithBot ℕ) := calc
      (_root_.Polynomial.X * (t₁ * t₂)).degree
          ≤ _root_.Polynomial.X.degree + (t₁ * t₂).degree := _root_.Polynomial.degree_mul_le _ _
      _ ≤ 1 + (t₁.degree + t₂.degree) := by
          rw [_root_.Polynomial.degree_X]
          exact add_le_add_right (_root_.Polynomial.degree_mul_le t₁ t₂) _
      _ ≤ (1 : WithBot ℕ) + ((k : WithBot ℕ) + (k : WithBot ℕ)) :=
          add_le_add_right (add_le_add (hle ht₁) (hle ht₂)) _
      _ < (2 * (k + 1 : ℕ) : WithBot ℕ) := by
          exact_mod_cast (by omega : 1 + (k + k) < 2 * (k + 1))
    exact (_root_.Polynomial.degree_add_le _ _).trans_lt
      (max_lt ((_root_.Polynomial.degree_add_le _ _).trans_lt (max_lt h1 h2)) h3)

/-- Coefficient vector in `Fin (2 * t) → F` of the degree-`< 2 * t` tail polynomial of the product
of two degree-$\le t$ Shamir sharing polynomials. -/
noncomputable def mulTailCoeffs {t : ℕ} (a : F) (r₁ : Fin t → F) (b : F) (r₂ : Fin t → F) :
    Fin (2 * t) → F :=
  _root_.Polynomial.degreeLTEquiv F (2 * t)
    ⟨mulTailPolynomial a (Polynomial.tailPolynomial t r₁) b (Polynomial.tailPolynomial t r₂),
      _root_.Polynomial.mem_degreeLT.2
        (by
          have h := degree_mulTailPolynomial_lt a (Polynomial.tailPolynomial_degree_lt t r₁)
            b (Polynomial.tailPolynomial_degree_lt t r₂)
          exact_mod_cast h)⟩

@[simp] theorem tailPolynomial_mulTailCoeffs {t : ℕ} (a : F) (r₁ : Fin t → F)
    (b : F) (r₂ : Fin t → F) :
    Polynomial.tailPolynomial (2 * t) (mulTailCoeffs a r₁ b r₂) =
      mulTailPolynomial a (Polynomial.tailPolynomial t r₁) b (Polynomial.tailPolynomial t r₂) := by
  simp [mulTailCoeffs, Polynomial.tailPolynomial]

/-- Multiplying two degree-$\le t$ Shamir sharing polynomials produces the degree-$\le 2t$ Shamir
sharing polynomial with secret `a * b` and tail coefficients `mulTailCoeffs a r₁ b r₂`. -/
theorem sharingPolynomial_mul_eq_sharingPolynomial_mulTailCoeffs {t : ℕ}
    (a : F) (r₁ : Fin t → F) (b : F) (r₂ : Fin t → F) :
    Polynomial.sharingPolynomial a (Polynomial.tailPolynomial t r₁) *
        Polynomial.sharingPolynomial b (Polynomial.tailPolynomial t r₂) =
      Polynomial.sharingPolynomial (a * b)
        (Polynomial.tailPolynomial (2 * t) (mulTailCoeffs a r₁ b r₂)) := by
  rw [tailPolynomial_mulTailCoeffs, sharingPolynomial_mul_sharingPolynomial]

/-- Pointwise product of party `i`'s degree-$t$ Shamir shares of `a` and `b` equals the evaluation
at `params.point i` of the degree-$\le 2t$ sharing polynomial with secret `a * b` and tail
coefficients `mulTailCoeffs a r₁ b r₂`. -/
theorem eval_sharingPolynomial_mul (params : Params F Party)
    (r₁ r₂ : Randomness params) (a b : F) (i : Party) :
    (Polynomial.sharingPolynomial (a * b)
      (Polynomial.tailPolynomial (2 * params.threshold) (mulTailCoeffs a r₁ b r₂))).eval
        (params.point i) =
      share params r₁ a i * share params r₂ b i := by
  rw [← sharingPolynomial_mul_eq_sharingPolynomial_mulTailCoeffs, _root_.Polynomial.eval_mul]
  rfl

/-- When `2 * params.threshold < Fintype.card Party` ($t < n / 2$), Lagrange reconstruction of the
pointwise product of degree-$t$ Shamir shares over `Party` recovers `a * b`. -/
theorem reconstruct_mul_share_eq_mul (params : Params F Party)
    (h2t : 2 * params.threshold < Fintype.card Party)
    (r₁ r₂ : Randomness params) (a b : F) :
    Polynomial.reconstruct params.point (fun i => share params r₁ a i * share params r₂ b i) =
      a * b := by
  simp_rw [← eval_sharingPolynomial_mul params r₁ r₂ a b]
  exact Polynomial.reconstruct_sharingPolynomial_eq_secret params.point_injective <|
    (Polynomial.degree_sharingPolynomial_tailPolynomial_lt_succ _ _ _).trans_le
      (mod_cast Nat.succ_le_of_lt h2t)

/-! ### 4. Lagrange share interpolation and unauthorized-coalition marginal uniformity -/

/-- Interpolating tail polynomial of degree `< |I|` that maps each `i : I` to
`(σ i - y) / params.point i`, so that `sharingPolynomial y` evaluates to `σ i` at `params.point i`.
-/
noncomputable def interpTailPolynomial (params : Params F Party) (I : Finset Party)
    (y : F) (σ : I → F) : _root_.Polynomial F :=
  open scoped Classical in
  _root_.Lagrange.interpolate I.attach (fun i : I => params.point i)
    (fun i : I => (σ i - y) / params.point i)

private theorem points_injOn_attach (params : Params F Party) (I : Finset Party) :
    Set.InjOn (fun i : I => params.point i) (I.attach : Finset I) := by
  intro i _ j _ hij
  exact Subtype.ext (params.point_injective hij)

theorem interpTailPolynomial_eval (params : Params F Party) (I : Finset Party)
    (y : F) (σ : I → F) (i : I) :
    (interpTailPolynomial params I y σ).eval (params.point i) =
      (σ i - y) / params.point i := by
  classical
  simpa [interpTailPolynomial] using
    _root_.Lagrange.eval_interpolate_at_node _ (points_injOn_attach params I)
      (Finset.mem_attach I i)

theorem interpTailPolynomial_degree_lt (params : Params F Party) (I : Finset Party)
    (hI : I.card ≤ params.threshold) (y : F) (σ : I → F) :
    (interpTailPolynomial params I y σ).degree < params.threshold := by
  classical
  rw [interpTailPolynomial]
  exact (_root_.Lagrange.degree_interpolate_lt _ (points_injOn_attach params I)).trans_le
    (by simp [hI])

/-- Coefficient vector in `Randomness params` interpolating target shares `σ : I → F` on an
unauthorized coalition `I` (`I.card ≤ params.threshold`) for secret `y : F`. -/
noncomputable def interpCoeffs (params : Params F Party) (I : Finset Party)
    (hI : I.card ≤ params.threshold) (y : F) (σ : I → F) : Randomness params :=
  _root_.Polynomial.degreeLTEquiv F params.threshold
    ⟨interpTailPolynomial params I y σ,
      _root_.Polynomial.mem_degreeLT.2 (interpTailPolynomial_degree_lt params I hI y σ)⟩

@[simp] theorem tailPolynomial_interpCoeffs (params : Params F Party) (I : Finset Party)
    (hI : I.card ≤ params.threshold) (y : F) (σ : I → F) :
    Polynomial.tailPolynomial params.threshold (interpCoeffs params I hI y σ) =
      interpTailPolynomial params I y σ := by
  simp [interpCoeffs, Polynomial.tailPolynomial]

/-- Sharing secret `y` with randomness `interpCoeffs params I hI y σ` reproduces `σ i` at every
coalition member `i : I`. -/
@[simp] theorem share_interpCoeffs (params : Params F Party) (I : Finset Party)
    (hI : I.card ≤ params.threshold) (y : F) (σ : I → F) (i : I) :
    share params (interpCoeffs params I hI y σ) y i = σ i := by
  rw [share, Polynomial.sharingPolynomial_eval, tailPolynomial_interpCoeffs,
    interpTailPolynomial_eval, mul_div_cancel₀ _ (params.point_nonzero i), add_sub_cancel]

/-- Additive group homomorphism restricting a zero-secret Shamir sharing to a coalition `I`. -/
noncomputable def shareZeroRestrictHom (params : Params F Party) (I : Finset Party) :
    Randomness params →+ (I → F) where
  toFun r i := share params r 0 i
  map_zero' := by ext i; exact share_zero params i
  map_add' r₁ r₂ := by
    ext i
    simpa using share_add params r₁ r₂ 0 0 i

/-- For any unauthorized coalition `I` (`I.card ≤ params.threshold`), `shareZeroRestrictHom` is
surjective. -/
theorem shareZeroRestrictHom_surjective (params : Params F Party) (I : Finset Party)
    (hI : I.card ≤ params.threshold) :
    Function.Surjective (shareZeroRestrictHom params I) := by
  exact fun σ => ⟨interpCoeffs params I hI 0 σ, funext (share_interpCoeffs params I hI 0 σ)⟩

/-- **Unauthorized-Coalition Marginal Uniformity** ([Shamir1979]; [AsharovLindell2017],
Section 3.2, Claim 3.2): for any coalition `I` with `I.card ≤ params.threshold` and any secret
`secret : F`, the restriction of `share params coeffs secret` to `I` under uniform
`coeffs : Randomness params` is uniformly distributed on `I → F`. -/
theorem uniformOfFintype_map_restrict_share [Fintype F] [DecidableEq Party]
    (params : Params F Party) (I : Finset Party) (hI : I.card ≤ params.threshold) (secret : F) :
    (PMF.uniformOfFintype (Randomness params)).map
        (fun coeffs (i : I) => share params coeffs secret i) =
      PMF.uniformOfFintype (I → F) := by
  have hshift :
      (fun coeffs (i : I) => share params coeffs secret i) =
        (Equiv.addLeft (fun _ : I => secret)) ∘ shareZeroRestrictHom params I := by
    ext coeffs i
    simpa [shareZeroRestrictHom] using share_add params 0 coeffs secret 0 i
  rw [hshift, ← PMF.map_comp,
    Cslib.Probability.PMF.uniformOfFintype_map_addHom (shareZeroRestrictHom params I)
      (shareZeroRestrictHom_surjective params I hI),
    PMF.uniformOfFintype_map_equiv]

end Cslib.Crypto.Protocols.SecretSharing.Shamir
