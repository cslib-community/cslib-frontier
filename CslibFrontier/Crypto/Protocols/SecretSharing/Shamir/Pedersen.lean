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
# Pedersen VSS: Completeness, Perfect Hiding, and Discrete-Log Witness Extraction

This module formalizes Pedersen's information-theoretically hiding verifiable secret sharing (VSS)
scheme ([Pedersen1991]) over a field `F` acting on an additive group `G` equipped with an
`F`-module structure, reusing `Feldman.evalCommit` and `Feldman.commit` from
`CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Feldman`. The cryptographic instance is
`F = ZMod q` for a prime `q` and `G` a group of order `q`.

1. **Commitments and Share Verification (`commit`, `verifyShare`, `dealDist`):** given public
   bases `g, h : G`, the dealer samples a degree-`≤ t` sharing polynomial for the secret `a₀` and an
   independent random degree-`≤ t` blinding polynomial `(b₀, r_b)`, publishes
   `C_k = a_k • g + b_k • h` (`commit`), and gives party `i` the `Share` with `value`
   `share params r_a a₀ i` and `blinding` `share params r_b b₀ i`. Verification of a pair `(s, u)`
   checks `s • g + u • h = Feldman.evalCommit C (params.point i)`.
2. **Completeness (`verifyShare_commit`):** honest shares verify against `commit`.
3. **Perfect Information-Theoretic Hiding (`coalitionViewDist`, `coalitionViewDist_eq`):**
   whenever `h = β • g` with `β ≠ 0`, for every unauthorized coalition `I` (`I.card ≤ t`) and
   every pair of secrets `a₀, a₁ : F`, the joint distribution of *all* commitments
   `C_0, ..., C_t` together with the coalition's shares `(s_i, u_i)_{i ∈ I}` is identical for
   `a₀` and `a₁`.
4. **Discrete-Logarithm Witness Extraction from Inconsistent Verified Shares (`extractDLog`,
   `extractDLog_smul_eq_of_reconstruct_ne`, `extractDLog_smul_eq_of_verifyShare_eq`):** given
   `g ≠ 0` and any two authorized sets of verified shares reconstructing distinct secrets `s₁ ≠ s₂`
   against the same commitment vector `C` (or two verified shares with distinct values for the
   same party), `extractDLog` explicitly returns a witness `b : F` solving `b • g = h`.

## Protocol model

The group is written additively as `[AddCommGroup G] [Module F G]`; the underlying Pedersen
commitment is `CslibFrontier.Crypto.Computational.PedersenCommitment`. The extraction theorems are
algebraic: they turn a dealer's inconsistency into a discrete-logarithm witness, and do not state a
computational binding game. Computational game reductions and complaint/broadcast protocols are
out of scope here (tracked in #5684).

## Main definitions

* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Pedersen.Share`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.Pedersen.Dealing`: a party's share pair and the
  commitment vector together with the shares of a family of parties.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Pedersen.commit`: Pedersen VSS commitment vector
  `C_k = a_k • g + b_k • h`.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Pedersen.verifyShare`: Pedersen VSS share
  verification `s • g + u • h = Feldman.evalCommit C (params.point i)`.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Pedersen.dealDist`,
  `Cslib.Crypto.Protocols.SecretSharing.Shamir.Pedersen.coalitionViewDist`: joint distribution of
  the commitment vector and all (resp. coalition `I`) shares under uniform dealing coins.
* `Cslib.Crypto.Protocols.SecretSharing.Shamir.Pedersen.extractDLog`: explicit discrete-logarithm
  witness `(u₂ - u₁)⁻¹ * (s₁ - s₂)`.

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
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing.Shamir.Pedersen

open Finset Cslib.Probability
open Cslib.Crypto.Protocols.SecretSharing.Shamir

/-! ### Shares and dealings -/

/-- A Pedersen VSS share held by one party: its Shamir share of the secret polynomial and its
Shamir share of the blinding polynomial. -/
@[ext] structure Share (F : Type*) where
  /-- The party's Shamir share of the secret polynomial. -/
  value : F
  /-- The party's Shamir share of the blinding polynomial. -/
  blinding : F

/-- The public commitment vector `C_0, ..., C_t` together with the `Share` of every party in `ι`.
With `ι = Party` this is the dealer's full output (`dealDist`); with `ι` a coalition `I` it is that
coalition's view (`coalitionViewDist`). -/
@[ext] structure Dealing (F G ι : Type*) (t : ℕ) where
  /-- The published commitment vector. -/
  commitments : Fin (t + 1) → G
  /-- The share delivered to each party. -/
  shares : ι → Share F

/-- Restrict a dealing to the parties of a coalition `I`, keeping all commitments. -/
@[expose] def Dealing.restrict {F G ι : Type*} {t : ℕ} (d : Dealing F G ι t) (I : Finset ι) :
    Dealing F G I t where
  commitments := d.commitments
  shares i := d.shares i.1

variable {F Party G : Type*} [Field F] [Fintype Party]

section AddCommMonoid

variable [AddCommMonoid G] [Module F G]

/-! ### Commitments and share verification -/

/-- Pedersen VSS commitment vector `C_0 = a₀ • g + b₀ • h`, `C_{k+1} = r_a k • g + r_b k • h`,
reusing `Feldman.commit`. -/
@[expose] def commit (params : Params F Party) (g h : G)
    (r_a : Randomness params) (a₀ : F) (r_b : Randomness params) (b₀ : F) :
    Fin (params.threshold + 1) → G :=
  Feldman.commit params g r_a a₀ + Feldman.commit params h r_b b₀

@[simp] theorem commit_zero (params : Params F Party) (g h : G)
    (r_a : Randomness params) (a₀ : F) (r_b : Randomness params) (b₀ : F) :
    commit params g h r_a a₀ r_b b₀ 0 = a₀ • g + b₀ • h :=
  rfl

@[simp] theorem commit_succ (params : Params F Party) (g h : G)
    (r_a : Randomness params) (a₀ : F) (r_b : Randomness params) (b₀ : F)
    (k : Fin params.threshold) :
    commit params g h r_a a₀ r_b b₀ k.succ = r_a k • g + r_b k • h :=
  rfl

/-- Evaluating `commit params g h r_a a₀ r_b b₀` at `params.point i` equals
`(share params r_a a₀ i) • g + (share params r_b b₀ i) • h`. -/
theorem evalCommit_commit (params : Params F Party) (g h : G)
    (r_a : Randomness params) (a₀ : F) (r_b : Randomness params) (b₀ : F) (i : Party) :
    Feldman.evalCommit (commit params g h r_a a₀ r_b b₀) (params.point i) =
      (share params r_a a₀ i) • g + (share params r_b b₀ i) • h := by
  rw [commit, Feldman.evalCommit_add, Feldman.evalCommit_commit, Feldman.evalCommit_commit]

/-- Pedersen share verification predicate for a secret share `s` and blinding share `u`: checks
`s • g + u • h = Feldman.evalCommit C (params.point i)`. -/
@[expose] def verifyShare (params : Params F Party) (g h : G) (C : Fin (params.threshold + 1) → G)
    (i : Party) (s u : F) : Prop :=
  s • g + u • h = Feldman.evalCommit C (params.point i)

instance [DecidableEq G] (params : Params F Party) (g h : G) (C : Fin (params.threshold + 1) → G)
    (i : Party) (s u : F) :
    Decidable (verifyShare params g h C i s u) :=
  inferInstanceAs (Decidable (_ = _))

/-- **Completeness of Pedersen VSS**: every honest share pair
`(share params r_a a₀ i, share params r_b b₀ i)` verifies against `commit params g h r_a a₀ r_b b₀`.
-/
theorem verifyShare_commit (params : Params F Party) (g h : G)
    (r_a : Randomness params) (a₀ : F) (r_b : Randomness params) (b₀ : F) (i : Party) :
    verifyShare params g h (commit params g h r_a a₀ r_b b₀) i
      (share params r_a a₀ i) (share params r_b b₀ i) :=
  (evalCommit_commit params g h r_a a₀ r_b b₀ i).symm

/-! ### Secret-commitment consistency -/

/-- Any authorized coalition `(J, σ, τ)` of verified Pedersen shares satisfies
`(reconstruct params J σ) • g + (reconstruct params J τ) • h = C 0`. -/
theorem reconstruct_smul_add_reconstruct_smul_eq
    (params : Params F Party) (g h : G) (C : Fin (params.threshold + 1) → G)
    {J : Finset Party} (hJ : authorized params J) (σ τ : J → F)
    (hver : ∀ j : J, verifyShare params g h C j.1 (σ j) (τ j)) :
    (reconstruct params J σ) • g + (reconstruct params J τ) • h = C 0 := by
  classical
  rw [reconstruct, reconstruct, Polynomial.reconstruct_eq_sum_lagrangeWeightAtZero,
    Polynomial.reconstruct_eq_sum_lagrangeWeightAtZero, sum_smul, sum_smul, ← sum_add_distrib,
    Feldman.commit_zero_eq_sum_lagrangeWeightAtZero_smul_evalCommit params C hJ]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_smul, mul_smul, smul_comm (σ j), smul_comm (τ j), ← smul_add, ← hver j]

/-! ### Perfect information-theoretic hiding (given all commitments `C_0..C_t` and `|I| ≤ t`) -/

/-- Full Pedersen VSS dealing distribution for secret `a₀ : F`: samples uniform `b₀ : F` and
uniform tail coefficient vectors `r_a, r_b : Randomness params`, and outputs the commitment vector
together with every party's `Share`. -/
@[expose] noncomputable def dealDist [Fintype F] (params : Params F Party) (g h : G) (a₀ : F) :
    PMF (Dealing F G Party params.threshold) :=
  (PMF.uniformOfFintype (F × Randomness params × Randomness params)).map
    fun (b₀, r_a, r_b) =>
      { commitments := commit params g h r_a a₀ r_b b₀
        shares i := ⟨share params r_a a₀ i, share params r_b b₀ i⟩ }

/-- Joint distribution of all commitments `C_0, ..., C_t` and a coalition `I`'s shares
`(s_i, u_i)_{i ∈ I}`. -/
@[expose] noncomputable def coalitionViewDist [Fintype F] (params : Params F Party) (g h : G)
    (I : Finset Party) (a₀ : F) : PMF (Dealing F G I params.threshold) :=
  (dealDist params g h a₀).map (·.restrict I)

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup G] [Module F G]

/-- **Perfect information-theoretic hiding of Pedersen VSS** ([Pedersen1991]): whenever
`h = β • g` with `β ≠ 0`, for every coalition `I` of size `I.card ≤ params.threshold` and every
pair of secrets `a₀, a₁ : F`, the joint distribution of *all* `t + 1` commitments
`C_0, ..., C_t` together with `I`'s shares `(s_i, u_i)_{i ∈ I}` is identical for `a₀` and `a₁`. -/
theorem coalitionViewDist_eq [Fintype F]
    (params : Params F Party) {g h : G} (hh : ∃ β : F, β ≠ 0 ∧ h = β • g)
    (I : Finset Party) (hI : I.card ≤ params.threshold) (a₀ a₁ : F) :
    coalitionViewDist params g h I a₀ = coalitionViewDist params g h I a₁ := by
  classical
  obtain ⟨β, hβ, rfl⟩ := hh
  let Δ : F := a₁ - a₀
  let δ : Randomness params := interpCoeffs params I hI (β⁻¹ * Δ) 0
  have hδ : ∀ i : I, share params δ (β⁻¹ * Δ) i.1 = 0 := fun i =>
    share_interpCoeffs params I hI (β⁻¹ * Δ) 0 i
  let equiv :
      (F × Randomness params × Randomness params) ≃ (F × Randomness params × Randomness params) :=
    { toFun := fun (b₀, r_a, r_b) => (b₀ + β⁻¹ * Δ, r_a - β • δ, r_b + δ)
      invFun := fun (b₀, r_a, r_b) => (b₀ - β⁻¹ * Δ, r_a + β • δ, r_b - δ)
      left_inv := fun ⟨b₀, r_a, r_b⟩ => by ext <;> simp
      right_inv := fun ⟨b₀, r_a, r_b⟩ => by ext <;> simp }
  have hmap : ∀ a : F,
      coalitionViewDist params g (β • g) I a =
        (PMF.uniformOfFintype (F × Randomness params × Randomness params)).map
          (fun (b₀, r_a, r_b) =>
            { commitments := commit params g (β • g) r_a a r_b b₀
              shares i := ⟨share params r_a a i.1, share params r_b b₀ i.1⟩ }) := by
    intro a
    simp only [coalitionViewDist, dealDist, PMF.map_comp]
    rfl
  rw [hmap a₀, hmap a₁]
  conv_lhs => rw [← PMF.uniformOfFintype_map_equiv equiv, PMF.map_comp]
  congr 1
  funext ⟨b₀, r_a, r_b⟩
  change ({ commitments := commit params g (β • g) (r_a - β • δ) a₀ (r_b + δ) (b₀ + β⁻¹ * Δ)
            shares i := ⟨share params (r_a - β • δ) a₀ i.1,
              share params (r_b + δ) (b₀ + β⁻¹ * Δ) i.1⟩ } : Dealing F G I params.threshold) =
    { commitments := commit params g (β • g) r_a a₁ r_b b₀
      shares i := ⟨share params r_a a₁ i.1, share params r_b b₀ i.1⟩ }
  have ha₀ : a₀ = a₁ + -(β * (β⁻¹ * Δ)) := by
    rw [← mul_assoc, mul_inv_cancel₀ hβ, one_mul]
    simp [Δ]
  refine Dealing.ext ?_ ?_
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
  · funext ⟨i, hi⟩
    refine Share.ext ?_ ?_
    · change share params (r_a - β • δ) a₀ i = share params r_a a₁ i
      rw [sub_eq_add_neg, ha₀, share_add,
        show -(β • δ) = (-β) • δ from (neg_smul β δ).symm,
        show -(β * (β⁻¹ * Δ)) = (-β) * (β⁻¹ * Δ) from (neg_mul _ _).symm,
        share_smul, hδ ⟨i, hi⟩, mul_zero, add_zero]
    · change share params (r_b + δ) (b₀ + β⁻¹ * Δ) i = share params r_b b₀ i
      rw [share_add, hδ ⟨i, hi⟩, add_zero]

/-! ### Discrete-log witness extraction -/

/-- Explicit discrete-logarithm extraction formula `(u₂ - u₁)⁻¹ * (s₁ - s₂)` solving `b • g = h`
from colliding Pedersen openings `s₁ • g + u₁ • h = s₂ • g + u₂ • h` with `s₁ ≠ s₂`. -/
@[expose] def extractDLog (s₁ u₁ s₂ u₂ : F) : F :=
  (u₂ - u₁)⁻¹ * (s₁ - s₂)

private theorem extractDLog_of_eq {g h : G} (hg : g ≠ 0) {s₁ u₁ s₂ u₂ : F}
    (heq : s₁ • g + u₁ • h = s₂ • g + u₂ • h) (hne : s₁ ≠ s₂) :
    u₂ ≠ u₁ ∧ extractDLog s₁ u₁ s₂ u₂ • g = h := by
  have hsub : (s₁ - s₂) • g = (u₂ - u₁) • h := by
    rw [sub_smul, sub_smul]
    exact eq_sub_of_add_eq (by
      calc (s₁ • g - s₂ • g) + u₁ • h = (s₁ • g + u₁ • h) - s₂ • g := by abel
        _ = (s₂ • g + u₂ • h) - s₂ • g := by rw [heq]
        _ = u₂ • h := by abel)
  have hune : u₂ ≠ u₁ := by
    intro hueq
    rw [hueq, sub_self, zero_smul] at hsub
    exact hne (sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hg))
  refine ⟨hune, ?_⟩
  rw [extractDLog, mul_smul, hsub, ← mul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hune), one_smul]

/-- **Discrete-logarithm witness extraction from inconsistent verified shares (authorized
coalitions)**: given `g ≠ 0` and two authorized sets `J₁, J₂` of verified shares `(σ₁, τ₁)` and
`(σ₂, τ₂)` under the same commitment vector `C` reconstructing different secrets
`reconstruct params J₁ σ₁ ≠ reconstruct params J₂ σ₂`, `extractDLog` explicitly returns a witness
`b` solving `b • g = h`. -/
theorem extractDLog_smul_eq_of_reconstruct_ne
    (params : Params F Party) {g h : G} (hg : g ≠ 0)
    (C : Fin (params.threshold + 1) → G)
    {J₁ J₂ : Finset Party} (hJ₁ : authorized params J₁) (hJ₂ : authorized params J₂)
    (σ₁ τ₁ : J₁ → F) (σ₂ τ₂ : J₂ → F)
    (hver₁ : ∀ j : J₁, verifyShare params g h C j.1 (σ₁ j) (τ₁ j))
    (hver₂ : ∀ j : J₂, verifyShare params g h C j.1 (σ₂ j) (τ₂ j))
    (hne : reconstruct params J₁ σ₁ ≠ reconstruct params J₂ σ₂) :
    reconstruct params J₂ τ₂ ≠ reconstruct params J₁ τ₁ ∧
      extractDLog (reconstruct params J₁ σ₁) (reconstruct params J₁ τ₁)
        (reconstruct params J₂ σ₂) (reconstruct params J₂ τ₂) • g = h := by
  have h1 := reconstruct_smul_add_reconstruct_smul_eq params g h C hJ₁ σ₁ τ₁ hver₁
  have h2 := reconstruct_smul_add_reconstruct_smul_eq params g h C hJ₂ σ₂ τ₂ hver₂
  exact extractDLog_of_eq hg (h1.trans h2.symm) hne

/-- **Discrete-logarithm witness extraction from inconsistent verified shares (single party)**:
if a single party `i` holds two verified share pairs `(s₁, u₁)` and `(s₂, u₂)` against the same
`C` with `s₁ ≠ s₂`, then `extractDLog s₁ u₁ s₂ u₂` solves `b • g = h` whenever `g ≠ 0`. -/
theorem extractDLog_smul_eq_of_verifyShare_eq
    (params : Params F Party) {g h : G} (hg : g ≠ 0)
    (C : Fin (params.threshold + 1) → G) (i : Party) {s₁ u₁ s₂ u₂ : F}
    (hver₁ : verifyShare params g h C i s₁ u₁)
    (hver₂ : verifyShare params g h C i s₂ u₂)
    (hne : s₁ ≠ s₂) :
    u₂ ≠ u₁ ∧ extractDLog s₁ u₁ s₂ u₂ • g = h :=
  extractDLog_of_eq hg (hver₁.trans hver₂.symm) hne

end AddCommGroup

end Cslib.Crypto.Protocols.SecretSharing.Shamir.Pedersen
