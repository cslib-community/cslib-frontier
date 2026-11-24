/-
Copyright (c) 2026 Samuel Schlesinger, Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Crypto.Protocols.SecretSharing.Shamir
public import CslibFrontier.Foundations.Data.Code.BerlekampWelch
public import CslibFrontier.Foundations.Data.Code.ReedSolomon
import Cslib.Crypto.Protocols.SecretSharing.Shamir.Polynomial
import CslibFrontier.Foundations.Data.Hamming

/-!
# Robust Shamir Secret Reconstruction and Welch–Berlekamp Decoding

Bridges Shamir `(t, n)` secret sharing (`Cslib.Crypto.Protocols.SecretSharing.Shamir`) to
Reed–Solomon codes (`Cslib.Code.reedSolomon`) and the Welch–Berlekamp decoder
(`Cslib.Code.berlekampWelch`) [Shamir1979], [ReedSolomon1960], [WelchBerlekamp1986], supporting
active malicious share corruption as used in perfectly secure MPC (`n ≥ 3t + 1`)
[BenOrGoldwasserWigderson1988], [AsharovLindell2017].

## Main definitions

* `Cslib.Crypto.Protocols.SecretSharing.Shamir.robustReconstruct`: Welch–Berlekamp secret
  reconstruction for `Params F Party` with error budget `e`, evaluating the decoded degree-`≤ t`
  polynomial at `0` (specializing to pure error detection at `e = 0`).

## Main results

* `Cslib.Crypto.Protocols.SecretSharing.Shamir.share_mem_reedSolomon`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.mem_reedSolomon_iff_exists_share`: Shamir sharings
  coincide with codewords of `Cslib.Code.reedSolomon params.point (params.threshold + 1)`.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.hammingDist_share_ge`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.card_filter_share_eq_le`: distinct Shamir
  sharings disagree on at least `n - t` parties and agree on at most `t` parties.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.eq_of_hammingDist_le_share`: unique decoding
  radius `2 * e + t < n` (in particular `3 * t < n` at `e = t`).
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.robustReconstruct_share_eq_some`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.robustReconstruct_eq_some_iff`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.robustReconstruct_bgw_eq_some`: completeness,
  soundness, and BGW threshold (`3 * t < n`) recovery for `robustReconstruct`.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.robustReconstruct_zero_share`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.robustReconstruct_zero_eq_none_of_errors`:
  error detection (`e = 0`) accepts valid sharings and rejects any nonzero tampering of weight
  `< n - t` (hence `≤ t` when `2 * t < n`).
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.keyEquation_exists`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.keyEquation_div_eq`: existence and exact division
  for arbitrary nonzero Welch–Berlekamp key-equation solutions `(E, Q)` without requiring `E` to be
  monic of full degree `e`.

## References

* [A. Shamir, *How to Share a Secret*][Shamir1979].
* [I. S. Reed, G. Solomon, *Polynomial codes over certain finite fields*][ReedSolomon1960].
* [L. R. Welch, E. R. Berlekamp, *Error correction for algebraic block codes*][WelchBerlekamp1986].
* [M. Ben-Or, S. Goldwasser, A. Wigderson, *Completeness Theorems for Non-Cryptographic
  Fault-Tolerant Distributed Computation*][BenOrGoldwasserWigderson1988] (BGW `n ≥ 3t + 1`
  threshold; exact page/section locators not verified from rendered PDF).
* [G. Asharov, Y. Lindell, *A Full Proof of the BGW Protocol for Perfectly Secure Multiparty
  Computation*][AsharovLindell2017] (exact page/section locators not verified from rendered PDF).
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SecretSharing.Shamir

open Finset

variable {F Party : Type*} [Field F] [Fintype Party]

/-! ### Shamir sharings as Reed–Solomon codewords -/

private lemma sharingPolynomial_eq_of_degree_lt (params : Params F Party)
    {p : _root_.Polynomial F} (hp : p.degree < (params.threshold + 1 : ℕ)) :
    Polynomial.sharingPolynomial (p.eval 0)
        (Polynomial.tailPolynomial params.threshold fun k => p.coeff (k.1 + 1)) =
      p := by
  ext m
  cases m with
  | zero =>
    rw [Polynomial.coeff_zero_sharingPolynomial, _root_.Polynomial.coeff_zero_eq_eval_zero]
  | succ k =>
    simp only [Polynomial.sharingPolynomial, _root_.Polynomial.coeff_add,
      _root_.Polynomial.coeff_C_succ, zero_add, _root_.Polynomial.coeff_X_mul]
    by_cases hk : k < params.threshold
    · exact Polynomial.tailPolynomial_coeff params.threshold
        (fun j => p.coeff (j.1 + 1)) ⟨k, hk⟩
    · have ht : (Polynomial.tailPolynomial params.threshold
          fun j => p.coeff (j.1 + 1)).coeff k = 0 :=
        _root_.Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le
          (Polynomial.tailPolynomial_degree_lt params.threshold _)
          (by exact_mod_cast (not_lt.1 hk)))
      have hp0 : p.coeff (k + 1) = 0 :=
        _root_.Polynomial.coeff_eq_zero_of_degree_lt
          (lt_of_lt_of_le hp (by exact_mod_cast (by omega : params.threshold + 1 ≤ k + 1)))
      rw [ht, hp0]

/-- Every Shamir share vector `share params r a₀` belongs to the Reed–Solomon code
`Cslib.Code.reedSolomon params.point (params.threshold + 1)`. -/
theorem share_mem_reedSolomon (params : Params F Party) (r : Randomness params) (a₀ : F) :
    share params r a₀ ∈ Cslib.Code.reedSolomon params.point (params.threshold + 1) := by
  refine Cslib.Code.eval_mem_reedSolomon params.point ?_
  simpa only [Nat.cast_add, Nat.cast_one] using
    Polynomial.degree_sharingPolynomial_tailPolynomial_lt_succ a₀ params.threshold r

/-- A share vector `w : Party → F` is a codeword of `Cslib.Code.reedSolomon params.point (t + 1)`
if and only if it is `share params r a₀` for some `(r, a₀)`. -/
theorem mem_reedSolomon_iff_exists_share (params : Params F Party) {w : Party → F} :
    w ∈ Cslib.Code.reedSolomon params.point (params.threshold + 1) ↔
      ∃ (r : Randomness params) (a₀ : F), share params r a₀ = w := by
  constructor
  · intro hw
    obtain ⟨p, hp, rfl⟩ := Cslib.Code.mem_reedSolomon.1 hw
    refine ⟨fun k => p.coeff (k.1 + 1), p.eval 0, ?_⟩
    funext i
    change (Polynomial.sharingPolynomial (p.eval 0) _).eval (params.point i) =
      p.eval (params.point i)
    rw [sharingPolynomial_eq_of_degree_lt params hp]
  · rintro ⟨r, a₀, rfl⟩
    exact share_mem_reedSolomon params r a₀

/-- Two Shamir sharings `(r₁, a₁)` and `(r₂, a₂)` produce identical share vectors if and only if
both their randomness vectors and their secrets agree. -/
theorem share_eq_share_iff (params : Params F Party) {r₁ r₂ : Randomness params} {a₁ a₂ : F} :
    share params r₁ a₁ = share params r₂ a₂ ↔ r₁ = r₂ ∧ a₁ = a₂ := by
  constructor
  · intro h
    classical
    let p₁ := Polynomial.sharingPolynomial a₁ (Polynomial.tailPolynomial params.threshold r₁)
    let p₂ := Polynomial.sharingPolynomial a₂ (Polynomial.tailPolynomial params.threshold r₂)
    have hdeg₁ := Polynomial.degree_sharingPolynomial_tailPolynomial_lt_succ a₁ params.threshold r₁
    have hdeg₂ := Polynomial.degree_sharingPolynomial_tailPolynomial_lt_succ a₂ params.threshold r₂
    have hsub : (p₁ - p₂).degree < (univ.image params.point).card := by
      rw [card_image_of_injective _ params.point_injective, card_univ]
      have hlt : (p₁ - p₂).degree < (params.threshold + 1 : WithBot ℕ) :=
        lt_of_le_of_lt (_root_.Polynomial.degree_sub_le p₁ p₂) (max_lt hdeg₁ hdeg₂)
      exact lt_of_lt_of_le hlt (by exact_mod_cast params.threshold_lt_card)
    have hp : p₁ = p₂ := _root_.Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq
      (univ.image params.point) hsub fun x hx => by
        obtain ⟨i, -, rfl⟩ := mem_image.1 hx
        exact congrFun h i
    constructor
    · ext k
      have hk := congrArg (fun q : _root_.Polynomial F => q.coeff (k.1 + 1)) hp
      simpa only [p₁, p₂, Polynomial.sharingPolynomial, _root_.Polynomial.coeff_add,
        _root_.Polynomial.coeff_C_succ, zero_add, _root_.Polynomial.coeff_X_mul,
        Polynomial.tailPolynomial_coeff] using hk
    · have h0 := congrArg (fun q : _root_.Polynomial F => q.coeff 0) hp
      simpa only [p₁, p₂, Polynomial.coeff_zero_sharingPolynomial] using h0
  · rintro ⟨rfl, rfl⟩
    rfl

/-! ### Minimum Hamming distance and unique decoding radius -/

/-- **Minimum Hamming distance (`d = n - t`)**: any two distinct Shamir sharings disagree on at
least `Fintype.card Party - params.threshold` parties. -/
theorem hammingDist_share_ge [DecidableEq F] (params : Params F Party)
    {r₁ r₂ : Randomness params} {a₁ a₂ : F}
    (hne : share params r₁ a₁ ≠ share params r₂ a₂) :
    Fintype.card Party - params.threshold ≤
      hammingDist (share params r₁ a₁) (share params r₂ a₂) := by
  have hw : share params r₁ a₁ - share params r₂ a₂ ∈
      Cslib.Code.reedSolomon params.point (params.threshold + 1) :=
    (Cslib.Code.reedSolomon params.point (params.threshold + 1)).sub_mem
      (share_mem_reedSolomon params r₁ a₁) (share_mem_reedSolomon params r₂ a₂)
  have hnorm := Cslib.Code.le_hammingNorm_of_mem_reedSolomon params.point_injective hw
    (sub_ne_zero.2 hne)
  have hdist : hammingNorm (share params r₁ a₁ - share params r₂ a₂) =
      hammingDist (share params r₁ a₁) (share params r₂ a₂) := by
    simp only [hammingNorm, hammingDist, Pi.sub_apply, sub_ne_zero]
  have hlt := params.threshold_lt_card
  omega

/-- Any two distinct Shamir sharings agree on at most `params.threshold` parties. -/
theorem card_filter_share_eq_le [DecidableEq F] (params : Params F Party)
    {r₁ r₂ : Randomness params} {a₁ a₂ : F}
    (hne : share params r₁ a₁ ≠ share params r₂ a₂) :
    #{i : Party | share params r₁ a₁ i = share params r₂ a₂ i} ≤ params.threshold := by
  have hsum := card_filter_eq_add_hammingDist (share params r₁ a₁) (share params r₂ a₂)
  have hdist := hammingDist_share_ge params hne
  omega

/-- **Unique decoding radius (`2 * e + t < n`)**: any received vector `w : Party → F` lies within
Hamming distance `e` of at most one Shamir sharing `(r, a₀)`. In particular, taking `e = t` under
the BGW threshold `3 * t < n` uniquely identifies the secret and sharing polynomial. -/
theorem eq_of_hammingDist_le_share [DecidableEq F] (params : Params F Party) {e : ℕ}
    (huniq : 2 * e + params.threshold < Fintype.card Party) {w : Party → F}
    {r₁ r₂ : Randomness params} {a₁ a₂ : F}
    (hd₁ : hammingDist w (share params r₁ a₁) ≤ e)
    (hd₂ : hammingDist w (share params r₂ a₂) ≤ e) :
    r₁ = r₂ ∧ a₁ = a₂ := by
  have hceq := Cslib.Code.eq_of_hammingDist_le_reedSolomon params.point_injective
    (by omega : 2 * e + (params.threshold + 1) ≤ Fintype.card Party)
    (share_mem_reedSolomon params r₁ a₁) (share_mem_reedSolomon params r₂ a₂) hd₁ hd₂
  exact (share_eq_share_iff params).1 hceq

/-! ### Welch–Berlekamp robust reconstruction and error detection -/

/-- Robust Shamir reconstruction up to `e` adversarial errors via the Welch–Berlekamp decoder
`Cslib.Code.berlekampWelch`, returning the constant term `p.eval 0` of the decoded polynomial.
At `e = 0`, this performs exact error detection. -/
noncomputable def robustReconstruct [DecidableEq F] (params : Params F Party) (e : ℕ)
    (w : Party → F) : Option F :=
  (Cslib.Code.berlekampWelch params.point e (params.threshold + 1) w).map (fun p => p.eval 0)

/-- **Error-correction completeness (`2 * e + t < n`)**: whenever `w` differs from an honest
sharing `share params r a₀` at `≤ e` coordinates, `robustReconstruct params e w = some a₀`. -/
theorem robustReconstruct_share_eq_some [DecidableEq F] (params : Params F Party) {e : ℕ}
    (huniq : 2 * e + params.threshold < Fintype.card Party) {r : Randomness params} {a₀ : F}
    {w : Party → F} (he : hammingDist (share params r a₀) w ≤ e) :
    robustReconstruct params e w = some a₀ := by
  have hdeg :
      (Polynomial.sharingPolynomial a₀ (Polynomial.tailPolynomial params.threshold r)).degree <
        ((params.threshold + 1 : ℕ) : WithBot ℕ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      Polynomial.degree_sharingPolynomial_tailPolynomial_lt_succ a₀ params.threshold r
  have hbw := Cslib.Code.berlekampWelch_eq_some params.point_injective
    (by omega : 2 * e + (params.threshold + 1) ≤ Fintype.card Party) hdeg he
  rw [robustReconstruct, hbw, Option.map_some, ← _root_.Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_zero_sharingPolynomial]

/-- **BGW robust reconstruction (`n ≥ 3t + 1`)**: under `3 * params.threshold < Fintype.card Party`,
`robustReconstruct params params.threshold w` recovers `some a₀` despite up to `t` corrupted shares.
-/
theorem robustReconstruct_bgw_eq_some [DecidableEq F] (params : Params F Party)
    (hbgw : 3 * params.threshold < Fintype.card Party) {r : Randomness params} {a₀ : F}
    {w : Party → F} (he : hammingDist (share params r a₀) w ≤ params.threshold) :
    robustReconstruct params params.threshold w = some a₀ :=
  robustReconstruct_share_eq_some params (by omega) he

/-- Exact characterization of `robustReconstruct params e w = some a₀` inside `2 * e + t < n`. -/
theorem robustReconstruct_eq_some_iff [DecidableEq F] (params : Params F Party) {e : ℕ}
    (huniq : 2 * e + params.threshold < Fintype.card Party) {w : Party → F} {a₀ : F} :
    robustReconstruct params e w = some a₀ ↔
      ∃ r : Randomness params, hammingDist (share params r a₀) w ≤ e := by
  constructor
  · intro h
    unfold robustReconstruct at h
    rcases hbw : Cslib.Code.berlekampWelch params.point e (params.threshold + 1) w with _ | p
    · simp [hbw] at h
    · rw [hbw, Option.map_some, Option.some.injEq] at h
      have hspec := (Cslib.Code.berlekampWelch_eq_some_iff params.point_injective
        (by omega : 2 * e + (params.threshold + 1) ≤ Fintype.card Party)).1 hbw
      refine ⟨fun k => p.coeff (k.1 + 1), ?_⟩
      have hshare :
          share params (fun k => p.coeff (k.1 + 1)) a₀ = fun i => p.eval (params.point i) := by
        funext i
        change (Polynomial.sharingPolynomial a₀ _).eval (params.point i) = p.eval (params.point i)
        rw [← h, sharingPolynomial_eq_of_degree_lt params hspec.1]
      rw [hshare]
      exact hspec.2
  · rintro ⟨r, he⟩
    exact robustReconstruct_share_eq_some params huniq he

/-- Exact failure characterization for `robustReconstruct params e w = none` inside `2 * e + t < n`.
-/
theorem robustReconstruct_eq_none_iff [DecidableEq F] (params : Params F Party) {e : ℕ}
    (huniq : 2 * e + params.threshold < Fintype.card Party) {w : Party → F} :
    robustReconstruct params e w = none ↔
      ∀ (r : Randomness params) (a₀ : F), e < hammingDist (share params r a₀) w := by
  constructor
  · intro h r a₀
    refine not_le.1 fun he => ?_
    rw [robustReconstruct_share_eq_some params huniq he] at h
    exact Option.some_ne_none _ h
  · intro h
    rcases hrec : robustReconstruct params e w with _ | a₀
    · rfl
    · obtain ⟨r, hr⟩ := (robustReconstruct_eq_some_iff params huniq).1 hrec
      exact absurd hr (not_le.2 (h r a₀))

/-- **Error-detection completeness**: at `e = 0`, any valid Shamir sharing is accepted and returns
`some a₀` unconditionally (since `params.threshold < Fintype.card Party`). -/
theorem robustReconstruct_zero_share [DecidableEq F] (params : Params F Party)
    (r : Randomness params) (a₀ : F) :
    robustReconstruct params 0 (share params r a₀) = some a₀ :=
  robustReconstruct_share_eq_some params (by have := params.threshold_lt_card; omega)
    (by rw [hammingDist_self])

/-- **Error-detection soundness (`e = 0`)**: if `w` differs from an honest sharing on at least `1`
and strictly fewer than `n - t` positions (in particular `1 ≤ d ≤ t` when `2 * t < n`), then
`robustReconstruct params 0 w = none`. -/
theorem robustReconstruct_zero_eq_none_of_errors [DecidableEq F] (params : Params F Party)
    {r : Randomness params} {a₀ : F} {w : Party → F}
    (hpos : 1 ≤ hammingDist (share params r a₀) w)
    (hlt : hammingDist (share params r a₀) w < Fintype.card Party - params.threshold) :
    robustReconstruct params 0 w = none := by
  rcases hrec : robustReconstruct params 0 w with _ | a₁
  · rfl
  · obtain ⟨r₁, hr₁⟩ := (robustReconstruct_eq_some_iff params
      (by have := params.threshold_lt_card; omega)).1 hrec
    have hw : share params r₁ a₁ = w := hammingDist_eq_zero.1 (Nat.le_zero.1 hr₁)
    have hne : share params r a₀ ≠ share params r₁ a₁ := by
      intro heq
      rw [← hw, heq, hammingDist_self] at hpos
      omega
    have hge := hammingDist_share_ge params hne
    rw [hw] at hge
    omega

/-! ### Arbitrary nonzero-error-locator Welch–Berlekamp key equation -/

private lemma degree_sharingPolynomial_mul_lt (params : Params F Party) {e : ℕ}
    (r : Randomness params) (a₀ : F) {E : _root_.Polynomial F} (hE0 : E ≠ 0)
    (hEdeg : E.natDegree ≤ e) :
    (Polynomial.sharingPolynomial a₀ (Polynomial.tailPolynomial params.threshold r) * E).degree <
      ((e + (params.threshold + 1) : ℕ) : WithBot ℕ) := by
  let f := Polynomial.sharingPolynomial a₀ (Polynomial.tailPolynomial params.threshold r)
  rcases eq_or_ne f 0 with hf0 | hf0
  · change (f * E).degree < _
    rw [hf0, zero_mul, _root_.Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  · have hfdeg : f.degree < (params.threshold + 1 : WithBot ℕ) :=
      Polynomial.degree_sharingPolynomial_tailPolynomial_lt_succ a₀ params.threshold r
    have hfnat : f.natDegree < params.threshold + 1 :=
      (_root_.Polynomial.natDegree_lt_iff_degree_lt hf0).2 hfdeg
    calc (f * E).degree
        ≤ f.degree + E.degree := _root_.Polynomial.degree_mul_le f E
      _ = ((f.natDegree + E.natDegree : ℕ) : WithBot ℕ) := by
          rw [_root_.Polynomial.degree_eq_natDegree hf0, _root_.Polynomial.degree_eq_natDegree hE0,
            Nat.cast_add]
      _ < ((e + (params.threshold + 1) : ℕ) : WithBot ℕ) := by
          exact_mod_cast (by omega : f.natDegree + E.natDegree < e + (params.threshold + 1))

/-- **Key-equation existence without degree padding**: if `w` differs from `share params r a₀` on
at most `e` positions, then `E = Lagrange.nodal {i | share params r a₀ i ≠ w i} params.point`
(monic of degree `≤ e`) and `Q = f * E` satisfy `Q(αᵢ) = wᵢ · E(αᵢ)` with
`deg Q < e + params.threshold + 1`. -/
theorem keyEquation_exists [DecidableEq F] (params : Params F Party) {e : ℕ}
    {r : Randomness params} {a₀ : F} {w : Party → F}
    (he : hammingDist (share params r a₀) w ≤ e) :
    ∃ E Q : _root_.Polynomial F,
      E ≠ 0 ∧ E.natDegree ≤ e ∧ Q.degree < ((e + (params.threshold + 1) : ℕ) : WithBot ℕ) ∧
      (∀ i, Q.eval (params.point i) = w i * E.eval (params.point i)) := by
  classical
  let errors : Finset Party := {i | share params r a₀ i ≠ w i}
  have herrors : errors.card ≤ e := he
  let E := Lagrange.nodal errors params.point
  let f := Polynomial.sharingPolynomial a₀ (Polynomial.tailPolynomial params.threshold r)
  have hE0 : E ≠ 0 := (Lagrange.nodal_monic (s := errors) (v := params.point)).ne_zero
  have hEdeg : E.natDegree ≤ e := by
    rw [Lagrange.natDegree_nodal]
    exact herrors
  refine ⟨E, f * E, hE0, hEdeg, degree_sharingPolynomial_mul_lt params r a₀ hE0 hEdeg, fun i => ?_⟩
  rw [_root_.Polynomial.eval_mul]
  by_cases hi : i ∈ errors
  · rw [Lagrange.eval_nodal_at_node hi, mul_zero, mul_zero]
  · have hEq : f.eval (params.point i) = w i := by
      simpa [errors, f, share] using hi
    rw [hEq]

/-- **Welch–Berlekamp division theorem for arbitrary nonzero `(E, Q)`**: under
`2 * e + t < n`, if `w` is within distance `e` of `share params r a₀` and *any* pair `(E, Q)`
with `E ≠ 0`, `E.natDegree ≤ e`, `Q.degree < e + t + 1` satisfies `Q(αᵢ) = wᵢ · E(αᵢ)` at all
parties `i`, then `Q = f * E`, `E ∣ Q`, and `(Q / E).eval 0 = a₀`. -/
theorem keyEquation_div_eq [DecidableEq F] (params : Params F Party) {e : ℕ}
    (huniq : 2 * e + params.threshold < Fintype.card Party) {r : Randomness params} {a₀ : F}
    {w : Party → F} (he : hammingDist (share params r a₀) w ≤ e)
    {E Q : _root_.Polynomial F} (hE0 : E ≠ 0) (hEdeg : E.natDegree ≤ e)
    (hQdeg : Q.degree < ((e + (params.threshold + 1) : ℕ) : WithBot ℕ))
    (heval : ∀ i, Q.eval (params.point i) = w i * E.eval (params.point i)) :
    Q = Polynomial.sharingPolynomial a₀ (Polynomial.tailPolynomial params.threshold r) * E ∧
      E ∣ Q ∧ (Q / E).eval 0 = a₀ := by
  classical
  let f := Polynomial.sharingPolynomial a₀ (Polynomial.tailPolynomial params.threshold r)
  let correct : Finset Party := {i | share params r a₀ i = w i}
  have hcorrect : correct.card + hammingDist (share params r a₀) w = Fintype.card Party :=
    card_filter_eq_add_hammingDist _ _
  have hQeq : Q = f * E := by
    refine sub_eq_zero.1 (_root_.Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
      (correct.image params.point) ?_ ?_)
    · rw [card_image_of_injective _ params.point_injective]
      calc (Q - f * E).degree
          ≤ max Q.degree (f * E).degree := _root_.Polynomial.degree_sub_le Q (f * E)
        _ < ((e + (params.threshold + 1) : ℕ) : WithBot ℕ) :=
            max_lt hQdeg (degree_sharingPolynomial_mul_lt params r a₀ hE0 hEdeg)
        _ ≤ correct.card := by exact_mod_cast (by omega)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
      have hwi : share params r a₀ i = w i := (mem_filter.1 hi).2
      rw [_root_.Polynomial.eval_sub, _root_.Polynomial.eval_mul, heval i]
      have hfi : f.eval (params.point i) = w i := hwi
      rw [hfi, sub_self]
  refine ⟨hQeq, ⟨f, by rw [hQeq, mul_comm]⟩, ?_⟩
  rw [hQeq, mul_div_cancel_right₀ _ hE0, ← _root_.Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_zero_sharingPolynomial]

end Cslib.Crypto.Protocols.SecretSharing.Shamir
