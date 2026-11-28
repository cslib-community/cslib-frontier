/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.SpanProgram.Basic
public import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Basic
public import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Sources

/-!
# Linear Secret Sharing from Monotone Span Programs

This module formalizes the linear secret-sharing scheme derived from a monotone span program
`P : MonotoneSpanProgram F Party` ([BonehShoup2023], Construction 22.2, Definition 22.22 and
Remark 22.15, pp. 978–982), with its correctness and privacy identities. These identities are a
step toward Theorem 22.13 (p. 980), not that theorem. Theorem 22.13 says that Construction 22.2 is
a secret sharing scheme in the sense of Definition 22.19 (p. 975), whose sharing and combining
algorithms are efficient. Here the combiner `linearReconstruct` picks its row weights with
`Classical.choose`, and no efficiency certificate for sharing or combining is proved (#5293).

In [BonehShoup2023] (Definition 22.21, p. 978), `P` *recognizes* an access structure `A` iff
`P.accessStructure = A`.

Given key `k : Fin P.tailDim → F` and `secret : F`, `linearShare P k secret i` evaluates
`P.matrix i *ᵥ Fin.cons secret k`. Any coalition row-weight vector `w` satisfying
`∑ i : s, vecMul (w i) (P.matrix i.1) = P.target` reconstructs `secret` as
`∑ i : s, dotProduct (w i) (linearShare P k secret i.1)` (`sum_dotProduct_linearShare_eq_secret`).
The total function `linearReconstruct` selects one such `w` via `Classical.choose` when
`P.Accepts s` and outputs `0` otherwise; it supplies the deterministic `reconstruct` field of
`AccessScheme` and carries no algorithmic or efficiency claim. For parties `Fin N` over a field
with decidable equality, `Cslib.Circuits.MonotoneSpanProgram.recombination` computes such a `w`
by elimination, and `Cslib.Circuits.Synthesis.full_recombination` bounds its circuits.

Privacy (`linearView_eq_of_not_accepts`) holds for every translation-invariant key distribution
`Q ∈ SourceClass.translationInvariant (LinearKey P)`. Note that when `F` is infinite and
`P.tailDim ≥ 1`, no translation-invariant `PMF` on `Fin P.tailDim → F` exists
(`SourceClass.translationInvariant (LinearKey P) = ∅`), so `linearAccessScheme P` has vacuous
privacy over infinite fields while correctness still holds for every key; use
`linearUniformAccessScheme P` over finite fields.

## Main definitions

* `Cslib.Circuits.MonotoneSpanProgram.accessStructure`: the monotone access structure recognized
  by `P`.
* `Cslib.Crypto.Protocols.SecretSharing.linearShare`,
  `Cslib.Crypto.Protocols.SecretSharing.linearReconstruct`: sharing and (choice-based)
  reconstruction of Construction 22.2.
* `Cslib.Crypto.Protocols.SecretSharing.linearAccessScheme`,
  `Cslib.Crypto.Protocols.SecretSharing.linearUniformAccessScheme`: `AccessScheme` instances
  (Definition 22.22), bundling the identities toward Theorem 22.13.

## Main results

* `Cslib.Crypto.Protocols.SecretSharing.sum_dotProduct_linearShare_eq_secret`: explicit
  reconstruction identity for any valid row-weight witness `w`.
* `Cslib.Crypto.Protocols.SecretSharing.linearReconstruct_linearShare`: correctness of
  `linearReconstruct`.
* `Cslib.Crypto.Protocols.SecretSharing.linearShare_add`,
  `Cslib.Crypto.Protocols.SecretSharing.linearReconstruct_linearShare_add`: additive
  homomorphisms (Remark 22.15).
* `Cslib.Crypto.Protocols.SecretSharing.linearShare_smul`: scalar multiplication homomorphism
  (not in [BonehShoup2023], Remark 22.15 states sums only).
* `Cslib.Crypto.Protocols.SecretSharing.linearView_eq_of_not_accepts`: secret-independence of
  unauthorized views under translation-invariant key sources, a step toward Theorem 22.13.

## References

* [BonehShoup2023] Dan Boneh and Victor Shoup, *A Graduate Course in Applied Cryptography*, v0.6,
  Section 22.5.2.
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing

open Cslib.Circuits Cslib.Probability Cslib.Probability.PMF

section LinearScheme

variable {F Party : Type*} [Field F]

/-- The monotone access structure recognized by a monotone span program `P`
([BonehShoup2023], Definition 22.21, p. 978). `P` recognizes `A` iff `P.accessStructure = A`. -/
@[expose] def _root_.Cslib.Circuits.MonotoneSpanProgram.accessStructure
    (P : MonotoneSpanProgram F Party) : AccessStructure Party where
  authorized := P.Accepts
  mono := P.accepts_mono

@[simp]
theorem _root_.Cslib.Circuits.MonotoneSpanProgram.accessStructure_authorized_iff
    (P : MonotoneSpanProgram F Party) (s : Finset Party) :
    P.accessStructure.authorized s ↔ P.Accepts s :=
  Iff.rfl

/-- Randomness (key) type for Construction 22.2: the auxiliary vector
`ρ = (ρ₂, …, ρ_d) : Fin P.tailDim → F` ([BonehShoup2023], Construction 22.2, p. 979). -/
abbrev LinearKey (P : MonotoneSpanProgram F Party) : Type _ :=
  Fin P.tailDim → F

/-- Share type for party `i` in Construction 22.2: a column vector `α_i ∈ F^{d_i}`
([BonehShoup2023], Construction 22.2, p. 979). -/
abbrev LinearShare (P : MonotoneSpanProgram F Party) (i : Party) : Type _ :=
  Fin (P.rowDim i) → F

/-- Sharing map `G(α)` of Construction 22.2 ([BonehShoup2023], p. 979): forms
`r = Fin.cons secret k` and assigns `P.matrix i *ᵥ r` to party `i`. -/
@[expose] def linearShare (P : MonotoneSpanProgram F Party) (k : LinearKey P) (secret : F)
    (i : Party) : LinearShare P i :=
  Matrix.mulVec (P.matrix i) (Fin.cons secret k)

/-- Explicit reconstruction identity for Construction 22.2 ([BonehShoup2023], pp. 979–980):
any row-weight family `w` satisfying `∑ i : s, Matrix.vecMul (w i) (P.matrix i.1) = P.target`
recombines the shares `{linearShare P k secret i.1}_{i ∈ s}` to `secret`. -/
theorem sum_dotProduct_linearShare_eq_secret (P : MonotoneSpanProgram F Party)
    (k : LinearKey P) (secret : F) {s : Finset Party}
    (w : (i : s) → Fin (P.rowDim i.val) → F)
    (hw : ∑ i : s, Matrix.vecMul (w i) (P.matrix i.val) = P.target) :
    ∑ i : s, dotProduct (w i) (linearShare P k secret i.val) = secret := by
  calc
    ∑ i : s, dotProduct (w i) (linearShare P k secret i.val)
      = ∑ i : s, dotProduct (Matrix.vecMul (w i) (P.matrix i.val)) (Fin.cons secret k) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact Matrix.dotProduct_mulVec (w i) (P.matrix i.val) (Fin.cons secret k)
    _ = dotProduct (∑ i : s, Matrix.vecMul (w i) (P.matrix i.val)) (Fin.cons secret k) := by
          rw [sum_dotProduct]
    _ = dotProduct P.target (Fin.cons secret k) := by rw [hw]
    _ = secret := by
          rw [MonotoneSpanProgram.target, single_one_dotProduct, Fin.cons_zero]

/-- Deterministic reconstruction map `C(J, {α_j}_{j ∈ J})` of Construction 22.2
([BonehShoup2023], pp. 979–980). When `P.Accepts s`, it selects a valid row-weight family via
`Classical.choose` and outputs its dot product with the shares; otherwise it outputs `0`. This
choice-based wrapper carries no efficiency claim. -/
@[expose] noncomputable def linearReconstruct (P : MonotoneSpanProgram F Party) (s : Finset Party)
    (v : (i : s) → LinearShare P i.val) : F :=
  open Classical in
  if hs : P.Accepts s then
    let w := Classical.choose ((P.accepts_iff_exists_vecMul s).mp hs)
    ∑ i : s, dotProduct (w i) (v i)
  else
    0

/-- Correctness of `linearReconstruct` ([BonehShoup2023], Construction 22.2, p. 980): every accepted
coalition `s` reconstructs `secret` for every key `k`. -/
theorem linearReconstruct_linearShare (P : MonotoneSpanProgram F Party)
    (k : LinearKey P) (secret : F) {s : Finset Party} (hs : P.Accepts s) :
    linearReconstruct P s (fun i => linearShare P k secret i.val) = secret := by
  classical
  simp only [linearReconstruct, hs, ↓reduceDIte]
  exact sum_dotProduct_linearShare_eq_secret P k secret
    (Classical.choose ((P.accepts_iff_exists_vecMul s).mp hs))
    (Classical.choose_spec ((P.accepts_iff_exists_vecMul s).mp hs))

/-- Additive homomorphism of Construction 22.2 sharing (Remark 22.15, [BonehShoup2023], p. 982). -/
theorem linearShare_add (P : MonotoneSpanProgram F Party) (k₁ k₂ : LinearKey P)
    (secret₁ secret₂ : F) (i : Party) :
    linearShare P (k₁ + k₂) (secret₁ + secret₂) i =
      linearShare P k₁ secret₁ i + linearShare P k₂ secret₂ i := by
  simp only [linearShare, ← Matrix.mulVec_add]
  exact congrArg _ (Matrix.cons_add_cons secret₁ k₁ secret₂ k₂).symm

/-- Scalar multiplication homomorphism of Construction 22.2 sharing (not in [BonehShoup2023];
Remark 22.15 states sums only). -/
theorem linearShare_smul (P : MonotoneSpanProgram F Party) (c : F) (k : LinearKey P)
    (secret : F) (i : Party) :
    linearShare P (c • k) (c * secret) i = c • linearShare P k secret i := by
  simp only [linearShare, ← Matrix.mulVec_smul]
  exact congrArg _ (Matrix.smul_cons c secret k).symm

/-- Reconstructing the pointwise sum of two Construction 22.2 sharings over an accepted
coalition `s` recovers `secret₁ + secret₂` (Remark 22.15, [BonehShoup2023], p. 982). -/
theorem linearReconstruct_linearShare_add (P : MonotoneSpanProgram F Party)
    (k₁ k₂ : LinearKey P) (secret₁ secret₂ : F) {s : Finset Party} (hs : P.Accepts s) :
    linearReconstruct P s
      (fun i => linearShare P k₁ secret₁ i.val + linearShare P k₂ secret₂ i.val) =
      secret₁ + secret₂ := by
  simp only [← linearShare_add]
  exact linearReconstruct_linearShare P (k₁ + k₂) (secret₁ + secret₂) hs

/-- The privacy identity of Construction 22.2, a step toward [BonehShoup2023], Theorem 22.13
(p. 980), not that theorem: under any translation-invariant key distribution
`Q ∈ SourceClass.translationInvariant (LinearKey P)`, every unauthorized coalition's view
distribution is independent of the secret, the condition of Definition 22.20 (p. 976).
Theorem 22.13 also says that Construction 22.2 is a secret sharing scheme in the sense of
Definition 22.19 (p. 975), whose sharing and combining algorithms are efficient. Here the combiner
`linearReconstruct` picks its row weights with `Classical.choose`, and no efficiency certificate
for sharing or combining is proved (#5293). -/
theorem linearView_eq_of_not_accepts (P : MonotoneSpanProgram F Party)
    {Q : PMF (LinearKey P)} (hQ : Q ∈ SourceClass.translationInvariant (LinearKey P))
    {s : Finset Party} (hs : ¬ P.Accepts s) (secret₀ secret₁ : F) :
    AccessStructure.viewDistOf Q (linearShare P) s secret₀ =
      AccessStructure.viewDistOf Q (linearShare P) s secret₁ := by
  obtain ⟨v, hv0, hv_null⟩ := P.exists_nullVector_of_not_accepts hs
  let δ : LinearKey P := fun k => (secret₁ - secret₀) * v k.succ
  refine AccessStructure.viewDistOf_eq_of_map_add_eq (hQ δ) fun r => ?_
  ext i row
  have hcons : Fin.cons secret₀ r + (secret₁ - secret₀) • v = Fin.cons secret₁ (r + δ) := by
    ext j
    induction j using Fin.cases with
    | zero => simp [hv0]
    | succ k => simp [δ, smul_eq_mul]
  simp only [linearShare]
  rw [← hcons, Matrix.mulVec_add, Matrix.mulVec_smul, hv_null i.val i.property, smul_zero, add_zero]

/-- The linear secret-sharing scheme derived from a monotone span program `P` ([BonehShoup2023],
Construction 22.2 and Definition 22.22, pp. 979–980), over
`SourceClass.translationInvariant (LinearKey P)`. It bundles the correctness and privacy
identities, a step toward Theorem 22.13 (p. 980): its combiner `linearReconstruct` picks its row
weights with `Classical.choose` and carries no efficiency claim (#5293). When `F` is infinite and
`P.tailDim ≥ 1`, `SourceClass.translationInvariant (LinearKey P) = ∅`, so privacy is vacuous
(only universal correctness holds nontrivially); use `linearUniformAccessScheme` for finite
fields. -/
@[expose] noncomputable def linearAccessScheme (P : MonotoneSpanProgram F Party) :
    AccessScheme F (LinearKey P) Party (LinearShare P) where
  access := P.accessStructure
  sources := SourceClass.translationInvariant (LinearKey P)
  share := linearShare P
  reconstruct := linearReconstruct P
  correct r secret _ hs := linearReconstruct_linearShare P r secret hs
  view_indist _ hQ _ hs := linearView_eq_of_not_accepts P hQ hs

@[simp]
theorem linearAccessScheme_access (P : MonotoneSpanProgram F Party) :
    (linearAccessScheme P).access = P.accessStructure :=
  rfl

/-- Canonical finite-field linear secret-sharing scheme derived from `P` with uniform randomness. -/
@[expose] noncomputable def linearUniformAccessScheme (P : MonotoneSpanProgram F Party)
    [Fintype F] :
    AccessScheme F (LinearKey P) Party (LinearShare P) :=
  (linearAccessScheme P).monoSources
    (Set.singleton_subset_iff.mpr (SourceClass.uniformOfFintype_mem_translationInvariant _))

@[simp]
theorem linearUniformAccessScheme_access (P : MonotoneSpanProgram F Party)
    [Fintype F] :
    (linearUniformAccessScheme P).access = P.accessStructure :=
  rfl

end LinearScheme

end Cslib.Crypto.Protocols.SecretSharing
