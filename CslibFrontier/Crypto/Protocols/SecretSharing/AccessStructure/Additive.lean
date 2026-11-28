/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Basic
public import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Privacy
public import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Designs
public import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Sources
public import CslibFrontier.Languages.Probabilistic.Sharing

/-!
# Additive All-of-n Secret Sharing as an Access-Structure Instance

This module instantiates `Cslib.Crypto.Protocols.SecretSharing.AccessScheme` for `(m + 1)`-out-of-
`(m + 1)` additive secret sharing over an `AddCommGroup G` ([KatzLindell2020]) by wrapping
`Cslib.ProbComp.completeShares` and `Cslib.ProbComp.uniformOfFintype_map_restrict_completeShares`
from `CslibFrontier/Languages/Probabilistic/Sharing.lean`:

- `additiveShare`: delegates to `Cslib.ProbComp.completeShares (m + 1) secret r`.
- `additiveAccessScheme`: universally correct over all keys and private over
  `SourceClass.translationInvariant (Fin m → G)`. When `G` is finite, this source class is
  `{uniformOfFintype}`; when `G` is infinite and `m ≥ 1`, no translation-invariant `PMF` on
  `Fin m → G` exists (`SourceClass.translationInvariant (Fin m → G) = ∅`), so privacy of
  `additiveAccessScheme` is vacuous over infinite groups (only correctness holds non-vacuously).
- `additiveUniformAccessScheme`: canonical finite-group uniform instance, with
  `additiveUniform_viewDist_eq` derived directly from
  `Cslib.ProbComp.uniformOfFintype_map_restrict_completeShares`.
- `additivePaddedSources`, `additivePaddedAccessScheme`: auxiliary-key padding of
  `additiveAccessScheme` via `comapKey Prod.fst` ignoring `Aux` (not an imperfect-randomness
  construction in [Aggarwal2026]'s sense).
- `additiveToTwoTwo`: `(m + 1, m + 1) → (2, 2)` design composition for `1 ≤ m` via
  `AccessScheme.toTwoTwo` ([Aggarwal2026], Section 5; [ACOR22] attribution unverified directly).

## Main definitions

* `Cslib.Crypto.Protocols.SecretSharing.additiveAccessStructure`: `(m + 1)`-threshold access
  structure on `Fin (m + 1)`.
* `Cslib.Crypto.Protocols.SecretSharing.additiveShare`,
  `Cslib.Crypto.Protocols.SecretSharing.additiveReconstruct`: additive sharing and reconstruction.
* `Cslib.Crypto.Protocols.SecretSharing.additiveAccessScheme`,
  `Cslib.Crypto.Protocols.SecretSharing.additiveUniformAccessScheme`: additive `AccessScheme`
  instances over `SourceClass.translationInvariant (Fin m → G)` (`{uniform}` for finite `G` and
  `∅` for infinite `G`, `m ≥ 1`).
* `Cslib.Crypto.Protocols.SecretSharing.additivePaddedSources`,
  `Cslib.Crypto.Protocols.SecretSharing.additivePaddedAccessScheme`: auxiliary-key padding of
  additive sharing (ignores `Aux`).
* `Cslib.Crypto.Protocols.SecretSharing.additiveToTwoTwo`: `(2, 2)` scheme via design composition
  from `(m + 1)`-out-of-`(m + 1)` sharing (`1 ≤ m`).

## Main results

* `Cslib.Crypto.Protocols.SecretSharing.additiveUniform_viewDist_eq`: every proper coalition has a
  uniform marginal share distribution under uniform additive pads.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020].
* [D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*][Aggarwal2026],
  Section 5 (checked locator for design composition).
* [D. Aggarwal, E. Chung, M. Obremski, J. Ribeiro, *On Secret Sharing, Randomness, and
  Random-less Reductions for Secret Sharing*][ACOR22] (unverified directly; attributed via
  [Aggarwal2026], Section 5).
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing

open Cslib.Probability Cslib.Probability.PMF

section AdditiveInstance

/-- The `(m + 1)`-out-of-`(m + 1)` threshold access structure on `Fin (m + 1)`. -/
@[expose] def additiveAccessStructure (m : ℕ) : AccessStructure (Fin (m + 1)) :=
  AccessStructure.threshold (Fin (m + 1)) (m + 1)

@[simp]
theorem additiveAccessStructure_authorized_iff (m : ℕ) (s : Finset (Fin (m + 1))) :
    (additiveAccessStructure m).authorized s ↔ s = Finset.univ := by
  simp only [additiveAccessStructure, AccessStructure.threshold_authorized_iff]
  exact ⟨fun h => Finset.eq_univ_of_card s (le_antisymm s.card_le_univ (by simpa using h)),
    fun h => by simp [h]⟩

/-- Additive secret sharing of `secret : G` among `m + 1` parties using `m` pads `r : Fin m → G`,
delegated to `Cslib.ProbComp.completeShares (m + 1)`. -/
@[expose] def additiveShare {m : ℕ} {G : Type*} [AddCommGroup G]
    (r : Fin m → G) (secret : G) (j : Fin (m + 1)) : G :=
  Cslib.ProbComp.completeShares (m + 1) secret r j

/-- Reconstruction for `(m + 1)`-out-of-`(m + 1)` additive sharing sums all parties' shares when
all `m + 1` parties are present. -/
@[expose] def additiveReconstruct {m : ℕ} {G : Type*} [AddCommGroup G]
    (s : Finset (Fin (m + 1))) (v : (j : s) → G) : G :=
  open scoped Classical in
  if hs : ∀ j : Fin (m + 1), j ∈ s then ∑ j : Fin (m + 1), v ⟨j, hs j⟩ else 0

theorem additiveReconstruct_share {m : ℕ} {G : Type*} [AddCommGroup G]
    (r : Fin m → G) (secret : G) {s : Finset (Fin (m + 1))}
    (hs : (additiveAccessStructure m).authorized s) :
    additiveReconstruct s (fun j => additiveShare r secret j.val) = secret := by
  classical
  have huniv := (additiveAccessStructure_authorized_iff m s).mp hs
  simp [additiveReconstruct, additiveShare, huniv, Cslib.ProbComp.sum_completeShares]

private theorem additiveView_eq_of_not_authorized {m : ℕ} {G : Type*} [AddCommGroup G]
    {P : PMF (Fin m → G)} (hP : ∀ δ, P.map (· + δ) = P)
    {s : Finset (Fin (m + 1))} (hs : ¬ (additiveAccessStructure m).authorized s)
    (m₀ m₁ : G) :
    AccessStructure.viewDistOf P additiveShare s m₀ =
      AccessStructure.viewDistOf P additiveShare s m₁ := by
  have hne : s ≠ Finset.univ := mt (additiveAccessStructure_authorized_iff m s).mpr hs
  obtain ⟨j₀, hj₀⟩ : ∃ j : Fin (m + 1), j ∉ s :=
    not_forall.mp (mt Finset.eq_univ_iff_forall.mpr hne)
  induction j₀ using Fin.lastCases with
  | last =>
    have hfun : (fun r (j : s) => additiveShare r m₀ j.val) =
        fun r (j : s) => additiveShare r m₁ j.val := by
      ext r j
      obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr fun h => hj₀ (h ▸ j.property)
      have hcast : j.val = Fin.castLE (Nat.sub_le (m + 1) 1) i := hi.symm
      simp only [hcast, additiveShare, Cslib.ProbComp.completeShares_castLE]
    simp only [AccessStructure.viewDistOf, hfun]
  | cast i₀ =>
    let δ : Fin m → G := Pi.single i₀ (m₁ - m₀)
    refine AccessStructure.viewDistOf_eq_of_map_add_eq (hP δ) fun r => ?_
    ext ⟨j, hj⟩
    induction j using Fin.lastCases with
    | last =>
      have hsum : ∑ i : Fin m, (r i + δ i) = (∑ i : Fin m, r i) + (m₁ - m₀) := by
        simp [Finset.sum_add_distrib, δ]
      simp only [additiveShare, show (Fin.last m : Fin (m + 1)) = ⊤ from rfl,
        Cslib.ProbComp.completeShares_top]
      change m₀ - ∑ i : Fin m, r i = m₁ - ∑ i : Fin m, (r + δ) i
      simp only [Pi.add_apply, hsum]
      abel
    | cast i =>
      have hi : i ≠ i₀ := fun h => hj₀ (h ▸ hj)
      simp only [additiveShare, show i.castSucc = Fin.castLE (Nat.sub_le (m + 1) 1) i from rfl,
        Cslib.ProbComp.completeShares_castLE, Pi.add_apply, δ, Pi.single_eq_of_ne hi, add_zero]

/-- `(m + 1)`-out-of-`(m + 1)` additive secret sharing over
`SourceClass.translationInvariant (Fin m → G)`. For infinite `G` with `m ≥ 1`,
`SourceClass.translationInvariant (Fin m → G) = ∅` so privacy is vacuous (only correctness holds
nontrivially); use `additiveUniformAccessScheme` for finite groups. -/
@[expose] noncomputable def additiveAccessScheme (m : ℕ) (G : Type*) [AddCommGroup G] :
    AccessScheme G (Fin m → G) (Fin (m + 1)) (fun _ => G) where
  access := additiveAccessStructure m
  sources := SourceClass.translationInvariant (Fin m → G)
  share := additiveShare
  reconstruct := additiveReconstruct
  correct r secret _ hs := by exact additiveReconstruct_share r secret hs
  view_indist _ hP _ hs := by exact additiveView_eq_of_not_authorized hP hs

@[simp]
theorem additiveAccessScheme_access (m : ℕ) (G : Type*) [AddCommGroup G] :
    (additiveAccessScheme m G).access = additiveAccessStructure m :=
  rfl

/-- Canonical finite-group `(m + 1)`-out-of-`(m + 1)` additive secret sharing with uniform pads. -/
@[expose] noncomputable def additiveUniformAccessScheme (m : ℕ) (G : Type*)
    [AddCommGroup G] [Fintype G] :
    AccessScheme G (Fin m → G) (Fin (m + 1)) (fun _ => G) :=
  (additiveAccessScheme m G).monoSources
    (Set.singleton_subset_iff.mpr (SourceClass.uniformOfFintype_mem_translationInvariant _))

@[simp]
theorem additiveUniformAccessScheme_access (m : ℕ) (G : Type*)
    [AddCommGroup G] [Fintype G] :
    (additiveUniformAccessScheme m G).access = additiveAccessStructure m :=
  rfl

/-- Under uniform additive pads, every proper coalition's view distribution is uniform on `s → G`
(via `Cslib.ProbComp.uniformOfFintype_map_restrict_completeShares`). -/
theorem additiveUniform_viewDist_eq (m : ℕ) (G : Type*)
    [AddCommGroup G] [Fintype G] [Nonempty G]
    {s : Finset (Fin (m + 1))} (hs : ¬ (additiveAccessStructure m).authorized s)
    (secret : G) :
    (additiveUniformAccessScheme m G).viewDist (uniformOfFintype (Fin m → G)) s secret =
      uniformOfFintype (s → G) := by
  have hne : s ≠ Finset.univ := mt (additiveAccessStructure_authorized_iff m s).mpr hs
  change (uniformOfFintype (Fin (m + 1 - 1) → G)).map
      (s.restrict ∘ Cslib.ProbComp.completeShares (m + 1) secret) =
    uniformOfFintype (s → G)
  exact Cslib.ProbComp.uniformOfFintype_map_restrict_completeShares s hne secret

/-- Auxiliary-key-padded sources for additive `(m + 1)`-out-of-`(m + 1)` sharing: pairs `(r, aux)`
whose pad marginal is translation-invariant (uniform when `G` is finite), with unused `aux`. -/
@[expose] noncomputable def additivePaddedSources (m : ℕ) (G Aux : Type*) [AddCommGroup G] :
    SourceClass ((Fin m → G) × Aux) :=
  { P | P.map Prod.fst ∈ SourceClass.translationInvariant (Fin m → G) }

/-- Auxiliary-key padding of `additiveAccessScheme` onto `(Fin m → G) × Aux` via
`comapKey Prod.fst` (ignores `Aux`; not an imperfect-randomness construction in [Aggarwal2026]'s
sense). -/
@[expose] noncomputable def additivePaddedAccessScheme (m : ℕ) (G Aux : Type*) [AddCommGroup G] :
    AccessScheme G ((Fin m → G) × Aux) (Fin (m + 1)) (fun _ => G) :=
  (additiveAccessScheme m G).comapKey Prod.fst (additivePaddedSources m G Aux) (fun _ hP => hP)

@[simp]
theorem additivePaddedAccessScheme_access (m : ℕ) (G Aux : Type*) [AddCommGroup G] :
    (additivePaddedAccessScheme m G Aux).access = additiveAccessStructure m :=
  rfl

/-- `(m + 1, m + 1) → (2, 2)` distribution-design reduction applied to additive sharing for
`1 ≤ m` ([Aggarwal2026], Section 5; [ACOR22] attribution unverified directly). -/
@[expose] noncomputable def additiveToTwoTwo (m : ℕ) (G : Type*) [AddCommGroup G]
    (hm : 1 ≤ m) :=
  (additiveAccessScheme m G).toTwoTwo (rfl : (additiveAccessScheme m G).access =
    AccessStructure.threshold (Fin (m + 1)) (m + 1))
    (by omega) (by simp)

@[simp]
theorem additiveToTwoTwo_access (m : ℕ) (G : Type*) [AddCommGroup G] (hm : 1 ≤ m) :
    (additiveToTwoTwo m G hm).access = AccessStructure.threshold (Fin 2) 2 :=
  rfl

end AdditiveInstance

end Cslib.Crypto.Protocols.SecretSharing
