/-
Copyright (c) 2026 Samuel Schlesinger, Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Feldman
public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Uniform

/-!
# Pedersen Verifiable Secret Sharing: Completeness, Perfect Hiding, and Discrete-Log Binding

This module formalizes Pedersen's information-theoretically hiding verifiable secret sharing (VSS)
scheme ([Pedersen1991]; [BonehShoup2023], Chapter 22) over `ZMod q` (for prime `q`) acting on an
additive group `G` equipped with a `ZMod q`-module structure, reusing `Feldman.evalCommit` and
`Feldman.commit` from `CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Feldman`:

1. **Commitments and Share Verification (`commit`, `verifyShare`, `dealDist`):** given public
   bases `g, h : G`, the dealer samples a degree-`≤ t` sharing polynomial for the secret `a₀` and an
   independent random degree-`≤ t` blinding polynomial `(b₀, r_b)`, publishes
   `C_k = a_k • g + b_k • h` (`commit`), and gives party `i` the share pair
   `(share params r_a a₀ i, share params r_b b₀ i)`. Verification checks
   `s • g + t • h = Feldman.evalCommit C (params.point i)`.
2. **Completeness (`verifyShare_commit`):** honest shares verify against `commit`.
3. **Perfect Information-Theoretic Hiding (`coalitionViewDist`, `coalitionViewDist_eq`):**
   whenever `h = β • g` with `β ≠ 0`, for every unauthorized coalition `I` (`I.card ≤ t`) and
   every pair of secrets `a₀, a₁ : ZMod q`, the joint distribution of *all* commitments
   `C_0, ..., C_t` together with the coalition's share pairs `(s_i, u_i)_{i ∈ I}` is identical for
   `a₀` and `a₁`.
4. **Explicit Binding / Discrete-Log Extraction (`extractDLog`,
   `extractDLog_smul_eq_of_reconstruct_ne`, `extractDLog_smul_eq_of_verifyShare_eq`):** given
   `g ≠ 0` and any two authorized sets of verified shares reconstructing distinct secrets `s₁ ≠ s₂`
   against the same commitment vector `C` (or two distinct verified shares for the same party),
   `extractDLog` explicitly returns a witness `b : ZMod q` solving `b • g = h`.

## Protocol model and source note

[Pedersen1991] (and [BonehShoup2023], Chapter 22; exact section and page locators for Pedersen VSS
are not verified from a rendered PDF, whereas the underlying Pedersen commitment laws in
[Pedersen1991], Section 3 and [BonehShoup2023], Section 10.6.1 are verified in
`CslibFrontier.Crypto.Computational.PedersenCommitment`). The group is written additively as
`[AddCommGroup G] [Module (ZMod q) G]`.

## Main definitions

* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Pedersen.commit`: Pedersen VSS commitment vector
  `C_k = a_k • g + b_k • h`.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Pedersen.verifyShare`: Pedersen VSS share
  verification `s • g + t • h = Feldman.evalCommit C (params.point i)`.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Pedersen.dealDist`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.Pedersen.coalitionViewDist`: joint distribution of
  the commitment vector and all (resp. coalition `I`) share pairs under uniform dealing coins.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Pedersen.extractDLog`: explicit discrete-logarithm
  witness `(t₂ - t₁)⁻¹ * (s₁ - s₂)`.

## Main results

* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Pedersen.verifyShare_commit`: honest completeness.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Pedersen.reconstruct_smul_add_reconstruct_smul_eq`:
  any authorized verified coalition `(σ, τ)` satisfies
  `reconstruct σ • g + reconstruct τ • h = C 0`.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Pedersen.coalitionViewDist_eq`: exact equality of
  joint commitment-and-coalition-view distributions for any `I.card ≤ params.threshold` and any
  two secrets `a₀, a₁` when `∃ β ≠ 0, h = β • g`.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Pedersen.extractDLog_smul_eq_of_reconstruct_ne`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.Pedersen.extractDLog_smul_eq_of_verifyShare_eq`:
  explicit discrete-log witness extraction from inconsistent verified shares when `g ≠ 0`.

## References

* [T. P. Pedersen, *Non-Interactive and Information-Theoretic Secure Verifiable Secret
  Sharing*][Pedersen1991].
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Chapter 22 (exact Pedersen VSS locators not verified from rendered
  PDF).
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing.Shamir.Pedersen

open Finset Cslib.Probability
open Cslib.Crypto.Protocols.SecretSharing.Shamir

/-! ### Commitments and share verification -/

/-- Pedersen VSS commitment vector `C_0 = a₀ • g + b₀ • h`, `C_{k+1} = r_a k • g + r_b k • h`,
reusing `Feldman.commit`. -/
@[expose] def commit {q : ℕ} [Fact (Nat.Prime q)] {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) (g h : G)
    (r_a : Randomness params) (a₀ : ZMod q) (r_b : Randomness params) (b₀ : ZMod q) :
    Fin (params.threshold + 1) → G :=
  Feldman.commit params g r_a a₀ + Feldman.commit params h r_b b₀

@[simp] theorem commit_zero {q : ℕ} [Fact (Nat.Prime q)] {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) (g h : G)
    (r_a : Randomness params) (a₀ : ZMod q) (r_b : Randomness params) (b₀ : ZMod q) :
    commit params g h r_a a₀ r_b b₀ 0 = a₀ • g + b₀ • h :=
  rfl

@[simp] theorem commit_succ {q : ℕ} [Fact (Nat.Prime q)] {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) (g h : G)
    (r_a : Randomness params) (a₀ : ZMod q) (r_b : Randomness params) (b₀ : ZMod q)
    (k : Fin params.threshold) :
    commit params g h r_a a₀ r_b b₀ k.succ = r_a k • g + r_b k • h :=
  rfl

/-- Evaluating `commit params g h r_a a₀ r_b b₀` at `params.point i` equals
`(share params r_a a₀ i) • g + (share params r_b b₀ i) • h`. -/
theorem evalCommit_commit {q : ℕ} [Fact (Nat.Prime q)] {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) (g h : G)
    (r_a : Randomness params) (a₀ : ZMod q) (r_b : Randomness params) (b₀ : ZMod q) (i : Party) :
    Feldman.evalCommit (commit params g h r_a a₀ r_b b₀) (params.point i) =
      (share params r_a a₀ i) • g + (share params r_b b₀ i) • h := by
  rw [commit, Feldman.evalCommit_add, Feldman.evalCommit_commit, Feldman.evalCommit_commit]

/-- Pedersen share verification predicate: checks `s • g + t • h = Feldman.evalCommit C (point i)`.
-/
@[expose] def verifyShare {q : ℕ} {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) (g h : G) (C : Fin (params.threshold + 1) → G)
    (i : Party) (s t : ZMod q) : Prop :=
  s • g + t • h = Feldman.evalCommit C (params.point i)

instance {q : ℕ} {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G] [DecidableEq G]
    (params : Params (ZMod q) Party) (g h : G) (C : Fin (params.threshold + 1) → G)
    (i : Party) (s t : ZMod q) :
    Decidable (verifyShare params g h C i s t) :=
  inferInstanceAs (Decidable (_ = _))

/-- **Completeness of Pedersen VSS**: every honest share pair
`(share params r_a a₀ i, share params r_b b₀ i)` verifies against `commit params g h r_a a₀ r_b b₀`.
-/
theorem verifyShare_commit {q : ℕ} [Fact (Nat.Prime q)] {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) (g h : G)
    (r_a : Randomness params) (a₀ : ZMod q) (r_b : Randomness params) (b₀ : ZMod q) (i : Party) :
    verifyShare params g h (commit params g h r_a a₀ r_b b₀) i
      (share params r_a a₀ i) (share params r_b b₀ i) :=
  (evalCommit_commit params g h r_a a₀ r_b b₀ i).symm

/-! ### Perfect information-theoretic hiding (given all commitments `C_0..C_t` and `|I| ≤ t`) -/

/-- Full Pedersen VSS dealing distribution for secret `a₀ : ZMod q`: samples uniform `b₀ : ZMod q`
and uniform tail coefficient vectors `r_a, r_b : Randomness params`, and outputs the commitment
vector `C` together with every party's share pair `(s_i, u_i)`. -/
@[expose] noncomputable def dealDist {q : ℕ} [Fact (Nat.Prime q)]
    {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) (g h : G) (a₀ : ZMod q) :
    PMF ((Fin (params.threshold + 1) → G) × (Party → ZMod q × ZMod q)) :=
  (PMF.uniformOfFintype (ZMod q × Randomness params × Randomness params)).map
    fun (b₀, r_a, r_b) =>
      (commit params g h r_a a₀ r_b b₀, fun i => (share params r_a a₀ i, share params r_b b₀ i))

/-- Joint distribution of all commitments `C_0, ..., C_t` and an unauthorized coalition `I`'s
share pairs `(s_i, u_i)_{i ∈ I}`. -/
@[expose] noncomputable def coalitionViewDist {q : ℕ} [Fact (Nat.Prime q)]
    {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) (g h : G) (I : Finset Party) (a₀ : ZMod q) :
    PMF ((Fin (params.threshold + 1) → G) × (I → ZMod q × ZMod q)) :=
  (dealDist params g h a₀).map fun out => (out.1, fun i : I => out.2 i.1)

/-- **Perfect information-theoretic hiding of Pedersen VSS** ([Pedersen1991]): whenever
`h = β • g` with `β ≠ 0`, for every coalition `I` of size `I.card ≤ params.threshold` and every
pair of secrets `a₀, a₁ : ZMod q`, the joint distribution of *all* `t + 1` commitments
`C_0, ..., C_t` together with `I`'s shares `(s_i, u_i)_{i ∈ I}` is identical for `a₀` and `a₁`. -/
theorem coalitionViewDist_eq {q : ℕ} [Fact (Nat.Prime q)]
    {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommGroup G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) {g h : G} (hh : ∃ β : ZMod q, β ≠ 0 ∧ h = β • g)
    (I : Finset Party) (hI : I.card ≤ params.threshold) (a₀ a₁ : ZMod q) :
    coalitionViewDist params g h I a₀ = coalitionViewDist params g h I a₁ := by
  classical
  obtain ⟨β, hβ, rfl⟩ := hh
  let Δ : ZMod q := a₁ - a₀
  let δ : Randomness params := interpCoeffs params I hI (β⁻¹ * Δ) 0
  have hδ : ∀ i : I, share params δ (β⁻¹ * Δ) i.1 = 0 := fun i =>
    share_interpCoeffs params I hI (β⁻¹ * Δ) 0 i
  let equiv :
      (ZMod q × Randomness params × Randomness params) ≃
        (ZMod q × Randomness params × Randomness params) :=
    { toFun := fun (b₀, r_a, r_b) => (b₀ + β⁻¹ * Δ, r_a - β • δ, r_b + δ)
      invFun := fun (b₀, r_a, r_b) => (b₀ - β⁻¹ * Δ, r_a + β • δ, r_b - δ)
      left_inv := fun ⟨b₀, r_a, r_b⟩ => by ext <;> simp
      right_inv := fun ⟨b₀, r_a, r_b⟩ => by ext <;> simp }
  have hmap :
      coalitionViewDist params g (β • g) I a₀ =
        (PMF.uniformOfFintype (ZMod q × Randomness params × Randomness params)).map
          (fun (b₀, r_a, r_b) =>
            (commit params g (β • g) r_a a₀ r_b b₀,
              fun i : I => (share params r_a a₀ i.1, share params r_b b₀ i.1))) := by
    simp only [coalitionViewDist, dealDist, PMF.map_comp]
    rfl
  have hmap₁ :
      coalitionViewDist params g (β • g) I a₁ =
        (PMF.uniformOfFintype (ZMod q × Randomness params × Randomness params)).map
          (fun (b₀, r_a, r_b) =>
            (commit params g (β • g) r_a a₁ r_b b₀,
              fun i : I => (share params r_a a₁ i.1, share params r_b b₀ i.1))) := by
    simp only [coalitionViewDist, dealDist, PMF.map_comp]
    rfl
  rw [hmap, hmap₁]
  conv_lhs => rw [← PMF.uniformOfFintype_map_equiv equiv, PMF.map_comp]
  congr 1
  funext ⟨b₀, r_a, r_b⟩
  change (commit params g (β • g) (r_a - β • δ) a₀ (r_b + δ) (b₀ + β⁻¹ * Δ),
      fun i : I => (share params (r_a - β • δ) a₀ i.1, share params (r_b + δ) (b₀ + β⁻¹ * Δ) i.1)) =
    (commit params g (β • g) r_a a₁ r_b b₀,
      fun i : I => (share params r_a a₁ i.1, share params r_b b₀ i.1))
  have ha₀ : a₀ = a₁ + -(β * (β⁻¹ * Δ)) := by
    rw [← mul_assoc, mul_inv_cancel₀ hβ, one_mul]
    simp [Δ]
  refine Prod.ext ?_ ?_
  · ext k
    refine Fin.cases ?_ ?_ k
    · simp only [commit_zero, smul_smul, ← add_smul]
      congr 1
      calc a₀ + (b₀ + β⁻¹ * Δ) * β
          = a₀ + b₀ * β + (β * β⁻¹) * Δ := by ring
        _ = a₁ + b₀ * β := by rw [mul_inv_cancel₀ hβ, one_mul]; simp [Δ]; ring
    · intro j
      simp only [commit_succ, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, smul_smul,
        ← add_smul]
      congr 1
      ring
  · ext ⟨i, hi⟩
    · have hs : share params (r_a - β • δ) a₀ i = share params r_a a₁ i := by
        rw [sub_eq_add_neg, ha₀, share_add,
          show -(β • δ) = (-β) • δ from (neg_smul β δ).symm,
          show -(β * (β⁻¹ * Δ)) = (-β) * (β⁻¹ * Δ) from (neg_mul _ _).symm,
          share_smul, hδ ⟨i, hi⟩, mul_zero, add_zero]
      exact hs
    · have hu : share params (r_b + δ) (b₀ + β⁻¹ * Δ) i = share params r_b b₀ i := by
        rw [share_add, hδ ⟨i, hi⟩, add_zero]
      exact hu

/-! ### Secret-commitment consistency and explicit discrete-log binding -/

/-- Any authorized coalition `(J, σ, τ)` of verified Pedersen shares satisfies
`(reconstruct params J σ) • g + (reconstruct params J τ) • h = C 0`. -/
theorem reconstruct_smul_add_reconstruct_smul_eq {q : ℕ} [Fact (Nat.Prime q)]
    {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommMonoid G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) (g h : G) (C : Fin (params.threshold + 1) → G)
    {J : Finset Party} (hJ : authorized params J) (σ τ : J → ZMod q)
    (hver : ∀ j : J, verifyShare params g h C j.1 (σ j) (τ j)) :
    (reconstruct params J σ) • g + (reconstruct params J τ) • h = C 0 := by
  classical
  rw [reconstruct, reconstruct, Polynomial.reconstruct_eq_sum_lagrangeWeightAtZero,
    Polynomial.reconstruct_eq_sum_lagrangeWeightAtZero, sum_smul, sum_smul, ← sum_add_distrib,
    Feldman.commit_zero_eq_sum_lagrangeWeightAtZero_smul_evalCommit params C hJ]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_smul, mul_smul, smul_comm (σ j), smul_comm (τ j), ← smul_add, ← hver j]

/-- Explicit discrete-logarithm extraction formula `(t₂ - t₁)⁻¹ * (s₁ - s₂)` solving `b • g = h`
from colliding Pedersen openings `s₁ • g + t₁ • h = s₂ • g + t₂ • h` with `s₁ ≠ s₂`. -/
@[expose] def extractDLog {q : ℕ} (s₁ t₁ s₂ t₂ : ZMod q) : ZMod q :=
  (t₂ - t₁)⁻¹ * (s₁ - s₂)

private theorem extractDLog_of_eq {q : ℕ} [Fact (Nat.Prime q)]
    {G : Type*} [AddCommGroup G] [Module (ZMod q) G]
    {g h : G} (hg : g ≠ 0) {s₁ t₁ s₂ t₂ : ZMod q}
    (heq : s₁ • g + t₁ • h = s₂ • g + t₂ • h) (hne : s₁ ≠ s₂) :
    t₂ ≠ t₁ ∧ extractDLog s₁ t₁ s₂ t₂ • g = h := by
  have hsub : (s₁ - s₂) • g = (t₂ - t₁) • h := by
    rw [sub_smul, sub_smul]
    exact eq_sub_of_add_eq (by
      calc (s₁ • g - s₂ • g) + t₁ • h = (s₁ • g + t₁ • h) - s₂ • g := by abel
        _ = (s₂ • g + t₂ • h) - s₂ • g := by rw [heq]
        _ = t₂ • h := by abel)
  have htne : t₂ ≠ t₁ := by
    intro hteq
    rw [hteq, sub_self, zero_smul] at hsub
    exact hne (sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hg))
  refine ⟨htne, ?_⟩
  rw [extractDLog, mul_smul, hsub, ← mul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr htne), one_smul]

/-- **Explicit Pedersen VSS binding / discrete-log extraction (authorized coalitions)**: given
`g ≠ 0` and two authorized sets `J₁, J₂` of verified shares `(σ₁, τ₁)` and `(σ₂, τ₂)` under the
same commitment vector `C` reconstructing different secrets
`reconstruct params J₁ σ₁ ≠ reconstruct params J₂ σ₂`, `extractDLog` explicitly returns a witness
`b` solving `b • g = h`. -/
theorem extractDLog_smul_eq_of_reconstruct_ne {q : ℕ} [Fact (Nat.Prime q)]
    {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommGroup G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) {g h : G} (hg : g ≠ 0)
    (C : Fin (params.threshold + 1) → G)
    {J₁ J₂ : Finset Party} (hJ₁ : authorized params J₁) (hJ₂ : authorized params J₂)
    (σ₁ τ₁ : J₁ → ZMod q) (σ₂ τ₂ : J₂ → ZMod q)
    (hver₁ : ∀ j : J₁, verifyShare params g h C j.1 (σ₁ j) (τ₁ j))
    (hver₂ : ∀ j : J₂, verifyShare params g h C j.1 (σ₂ j) (τ₂ j))
    (hne : reconstruct params J₁ σ₁ ≠ reconstruct params J₂ σ₂) :
    reconstruct params J₂ τ₂ ≠ reconstruct params J₁ τ₁ ∧
      extractDLog (reconstruct params J₁ σ₁) (reconstruct params J₁ τ₁)
        (reconstruct params J₂ σ₂) (reconstruct params J₂ τ₂) • g = h := by
  have h1 := reconstruct_smul_add_reconstruct_smul_eq params g h C hJ₁ σ₁ τ₁ hver₁
  have h2 := reconstruct_smul_add_reconstruct_smul_eq params g h C hJ₂ σ₂ τ₂ hver₂
  exact extractDLog_of_eq hg (h1.trans h2.symm) hne

/-- **Explicit Pedersen VSS binding (single-party double opening)**: if a single party `i` holds two
verified share pairs `(s₁, t₁)` and `(s₂, t₂)` against the same `C` with `s₁ ≠ s₂`, then
`extractDLog s₁ t₁ s₂ t₂` solves `b • g = h` whenever `g ≠ 0`. -/
theorem extractDLog_smul_eq_of_verifyShare_eq {q : ℕ} [Fact (Nat.Prime q)]
    {Party : Type*} [Fintype Party]
    {G : Type*} [AddCommGroup G] [Module (ZMod q) G]
    (params : Params (ZMod q) Party) {g h : G} (hg : g ≠ 0)
    (C : Fin (params.threshold + 1) → G) (i : Party) {s₁ t₁ s₂ t₂ : ZMod q}
    (hver₁ : verifyShare params g h C i s₁ t₁)
    (hver₂ : verifyShare params g h C i s₂ t₂)
    (hne : s₁ ≠ s₂) :
    t₂ ≠ t₁ ∧ extractDLog s₁ t₁ s₂ t₂ • g = h :=
  extractDLog_of_eq hg (hver₁.trans hver₂.symm) hne

end Cslib.Crypto.Protocols.SecretSharing.Shamir.Pedersen
