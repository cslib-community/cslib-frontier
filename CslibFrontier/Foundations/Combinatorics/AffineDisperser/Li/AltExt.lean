/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Li.SumsetCorrelationBreaker
import CslibFrontier.Foundations.FieldTheory.Finite.BinaryField
public import CslibFrontier.Probability.Extractor.Basic
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Foundations.Data.BitString.Block
import CslibFrontier.Probability.Conditioning
import CslibFrontier.Probability.Extractor.TwoSource
import CslibFrontier.Probability.MinEntropy.ChainRule
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.StatisticalDistance
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Alternating extraction and polynomial `𝔽₂`-linear correlation breakers

This module develops alternating extraction (`altExt`) and polynomial weak-seed correlation
breakers (`vanderCB`) toward #7793, building on `CslibFrontier.Probability.MinEntropy.ChainRule`
and `CslibFrontier.Foundations.Combinatorics.AffineDisperser.Li.SumsetCorrelationBreaker`:

1. **Strong extraction with imperfect seeds**:
   * `dist_strongExtractor_nearUniform_seed_le`: a strong `(k, ε)`-extractor evaluated on an
     independent `k`-source and a seed `η`-close to uniform yields output `(η + ε)`-close to
     uniform jointly with any side information determining the seed (no factor-of-2 loss).
   * `dist_strongExtractor_nearUniform_seed_add_le`: same bound with an arbitrary seed-side XOR
     shift, enabling linear extraction on sumset sources `A + B`.
   * `dist_strongExtractor_weakSeed_le`: weak-seed bootstrap bound `|Seed| * 2 ^ (-kSeed) * ε`
     when the seed only has min-entropy `kSeed`.

2. **Alternating extraction (`altExt`)**:
   * Defined abstractly over any pair of seeded extractors
     `ext1 : BitString nX → BitString d1 → BitString d2` and
     `ext2 : BitString nY → BitString d2 → BitString d1`.
   * **Per-round active-source linearity** (`altExtR_add_source`, `altExtS_add_source`): when
     `ext1` / `ext2` are `𝔽₂`-linear in their source argument (`IsLinearStrongExtractor`), each
     individual alternating-extraction step is `𝔽₂`-linear in its active source (while multi-round
     `altExt` is nonlinear in the seed and across ≥ 2 rounds).
   * **Exact look-ahead / conditional-independence theorem (`dist_altExt_lookAhead_le`)**: for
     independent `(X, X')` and `(Y, Y', S_0, S'_0)` with `r` tampered copies, the `k`-th output
     `R_k` is within `η₀ + (k + 1) * ε₁ + k * ε₂ + (2 * k + 2) * δ` of uniform jointly with
     `(Y, Y', S₀, S'₀, R_0..R_{k-1}, R'_0..R'_k)` (and hence jointly with the entire preceding
     transcript `(S_0..S_k, S'_0..S'_k, R_0..R_{k-1}, R'_0..R'_k)`).
   * **Sumset alternating extraction (`dist_altExt_sumset_lookAhead_le`)**: when `ext1` and `ext2`
     are `IsLinearStrongExtractor`, running `altExt` on a sumset `A + B` satisfies the same
     look-ahead theorem by absorbing passive-source evaluations as XOR shifts.

3. **Polynomial (`BinaryField`) linear weak-seed correlation breaker (`vanderCB`)**:
   * Directly satisfies `#8213`'s strictly-linear `IsLinearWeakSeedCB` interface over `Advice =
     BitString ℓ` (`2 ^ ℓ` advice strings) using only `(t + 1) * ℓ` source bits (an exponential
     advice-length compression over `blockDotCB`'s `2 ^ ℓ * ℓ` bits), via polynomial evaluation
     over `BinaryField ℓ` and Chor–Goldreich (`isLinearWeakSeedCB_vander`). Like `blockDotCB`,
     it still requires high source min-entropy `kSrc > t * ℓ`.

These theorems are **intermediate building blocks** toward #7793, not [Li2023] Theorem 7.13;
the Cohen–Chattopadhyay–Li flip-flop primitive (`flipFlop`) and logarithmic-entropy
sumset instantiation into `SumsetBridge` remain open in #7793.

## Main definitions

* `Cslib.AffineDisperser.Li.altExt`, `Cslib.AffineDisperser.Li.altExtR`,
  `Cslib.AffineDisperser.Li.altExtS`: alternating extraction protocol.
* `Cslib.AffineDisperser.Li.vanderCB`: Vandermonde / polynomial `𝔽₂`-linear weak-seed
  correlation breaker over `BinaryField ℓ`.

## Main results

* `Cslib.AffineDisperser.Li.dist_strongExtractor_nearUniform_seed_le`,
  `Cslib.AffineDisperser.Li.dist_strongExtractor_nearUniform_seed_add_le`,
  `Cslib.AffineDisperser.Li.dist_strongExtractor_weakSeed_le`: strong extraction with imperfect
  seeds.
* `Cslib.AffineDisperser.Li.altExtR_add_source`, `Cslib.AffineDisperser.Li.altExtS_add_source`:
  per-round `𝔽₂`-linearity in the active source.
* `Cslib.AffineDisperser.Li.dist_altExt_lookAhead_le`,
  `Cslib.AffineDisperser.Li.dist_altExt_sumset_lookAhead_le`: two-source and sumset alternating
  extraction look-ahead theorems.
* `Cslib.AffineDisperser.Li.isLinearWeakSeedCB_vander`: polynomial `IsLinearWeakSeedCB` instance.

## References

* [E. Chattopadhyay and D. Zuckerman, *Explicit Two-Source Extractors and Resilient
  Functions*][ChattopadhyayZuckerman2019] (locator not verified against primary PDF)
* [B. Chor and O. Goldreich, *Unbiased Bits from Sources of Weak Randomness and Probabilistic
  Communication Complexity*][ChorGoldreich1988]
* [Y. Dodis, R. Ostrovsky, L. Reyzin, A. Smith, *Fuzzy Extractors: How to Generate Strong Keys from
  Biometrics and Other Noisy Data*][DodisOstrovskyReyzinSmith2008] (locator not verified against
  primary PDF)
* [X. Li, *Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More*][Li2023],
  ECCC TR23-023 revision 1 (alternating extraction and sumset correlation breakers; locator not
  verified against primary PDF beyond Definition 1.1 and Theorem 7.13)
-/

public section

namespace Cslib.AffineDisperser.Li

open Cslib Cslib.BitString Cslib.Probability Cslib.Probability.PMF Finset

/-! ### 1. Strong extraction with imperfect seeds -/

section ImperfectSeed

/-- **Strong extraction with a near-uniform seed (exact, no factor-of-2 loss)**:
if `ext` is a strong `(k, ε)`-extractor and `k ≤ minEntropy PX`, then evaluating `ext` on `PX`
and a seed `seed Y` driven by an independent distribution `PY` yields output within
`dist (PY.map seed) U_Seed + ε` of uniform jointly with `Y`. -/
theorem dist_strongExtractor_nearUniform_seed_le
    {Input Seed Output β : Type*} [Fintype Seed] [Nonempty Seed]
    [Fintype Output] [Nonempty Output] [Fintype β]
    {ext : Input → Seed → Output} {k ε : ℝ}
    (hext : IsStrongExtractor ext k ε)
    {PX : PMF Input} (hPX : k ≤ minEntropy PX)
    (PY : PMF β) (seed : β → Seed) :
    dist
      (PY.bind fun y => PX.map fun x => (y, ext x (seed y)))
      (PY.bind fun y => (PMF.uniformOfFintype Output).map fun u => (y, u)) ≤
      dist (PY.map seed) (PMF.uniformOfFintype Seed) + ε := by
  have hmapL (y : β) :
      (PX.map fun x => (y, ext x (seed y))) = (PX.map fun x => ext x (seed y)).map (y, ·) :=
    (PMF.map_comp _ _ _).symm
  simp only [hmapL]
  rw [dist_bind_pair, ← sum_map_mul PY seed
    (fun s => dist (PX.map fun x => ext x s) (PMF.uniformOfFintype Output))]
  set p := PY.map seed
  set q := PMF.uniformOfFintype Seed
  let f : Seed → ℝ := fun s => dist (PX.map fun x => ext x s) (PMF.uniformOfFintype Output)
  have hf_sum : ∑ s : Seed, (q s).toReal * f s ≤ ε := by
    rw [sum_uniform_dist_strongExtractor]
    exact hext PX hPX
  have hdiff : ∑ s : Seed, (p s).toReal * f s - ∑ s : Seed, (q s).toReal * f s ≤ dist p q := by
    rw [← Finset.sum_sub_distrib, dist_eq_sum_filter_lt, Finset.sum_filter]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [← sub_mul]
    split_ifs with hlt
    · exact mul_le_of_le_one_right (sub_pos.mpr hlt).le (dist_le_one _ _)
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (not_lt.mp hlt)) dist_nonneg
  linarith

/-- **Shifted strong extraction with a near-uniform seed**: adding a `Y`-determined XOR mask
`shift y` to the output preserves `dist_strongExtractor_nearUniform_seed_le`. -/
theorem dist_strongExtractor_nearUniform_seed_add_le
    {Input Seed β : Type*} {m : ℕ} [Fintype Seed] [Nonempty Seed] [Fintype β]
    {ext : Input → Seed → BitString m} {k ε : ℝ}
    (hext : IsStrongExtractor ext k ε)
    {PX : PMF Input} (hPX : k ≤ minEntropy PX)
    (PY : PMF β) (seed : β → Seed) (shift : β → BitString m) :
    dist
      (PY.bind fun y => PX.map fun x => (y, ext x (seed y) + shift y))
      (PY.bind fun y => (PMF.uniformOfFintype (BitString m)).map fun u => (y, u)) ≤
      dist (PY.map seed) (PMF.uniformOfFintype Seed) + ε := by
  let e : β × BitString m ≃ β × BitString m :=
    { toFun := fun ⟨y, z⟩ => (y, z + shift y)
      invFun := fun ⟨y, z⟩ => (y, z + shift y)
      left_inv := fun ⟨y, z⟩ => Prod.ext rfl (by simp [add_assoc, BitString.add_self])
      right_inv := fun ⟨y, z⟩ => Prod.ext rfl (by simp [add_assoc, BitString.add_self]) }
  have hL :
      (PY.bind fun y => PX.map fun x => (y, ext x (seed y) + shift y)) =
      (PY.bind fun y => PX.map fun x => (y, ext x (seed y))).map e := by
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, e, Equiv.coe_fn_mk]
  have hR :
      (PY.bind fun y => (PMF.uniformOfFintype (BitString m)).map fun u => (y, u)) =
      (PY.bind fun y => (PMF.uniformOfFintype (BitString m)).map fun u => (y, u)).map e := by
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, e, Equiv.coe_fn_mk]
    refine congrArg (PY.bind ·) (funext fun y => ?_)
    have hshift : ((PMF.uniformOfFintype (BitString m)).map fun u => (y, u + shift y)) =
        ((PMF.uniformOfFintype (BitString m)).map (Equiv.addRight (shift y))).map (y, ·) :=
      (PMF.map_comp _ _ _).symm
    rw [hshift, PMF.uniformOfFintype_map_equiv]
  rw [hL, hR]
  exact (dist_map_le _ _ e).trans
    (dist_strongExtractor_nearUniform_seed_le hext hPX PY seed)

/-- **Weak-seed bootstrap for strong extractors**: if `PY.map seed` has min-entropy at least
`kSeed`, then evaluating a strong `(k, ε)`-extractor on `PX` and `seed Y` yields output within
`|Seed| * 2 ^ (-kSeed) * ε` of uniform jointly with `Y`. -/
theorem dist_strongExtractor_weakSeed_le
    {Input Seed Output β : Type*} [Fintype Seed] [Nonempty Seed]
    [Fintype Output] [Nonempty Output] [Fintype β]
    {ext : Input → Seed → Output} {k kSeed ε : ℝ}
    (hext : IsStrongExtractor ext k ε)
    {PX : PMF Input} (hPX : k ≤ minEntropy PX)
    (PY : PMF β) (seed : β → Seed)
    (hseed : kSeed ≤ minEntropy (PY.map seed)) :
    dist
      (PY.bind fun y => PX.map fun x => (y, ext x (seed y)))
      (PY.bind fun y => (PMF.uniformOfFintype Output).map fun u => (y, u)) ≤
      (Fintype.card Seed : ℝ) * (2 : ℝ) ^ (-kSeed) * ε := by
  have hmapL (y : β) :
      (PX.map fun x => (y, ext x (seed y))) = (PX.map fun x => ext x (seed y)).map (y, ·) :=
    (PMF.map_comp _ _ _).symm
  simp only [hmapL]
  rw [dist_bind_pair, ← sum_map_mul PY seed
    (fun s => dist (PX.map fun x => ext x s) (PMF.uniformOfFintype Output))]
  have hcard_pos : (0 : ℝ) < Fintype.card Seed := by exact_mod_cast Fintype.card_pos
  calc ∑ s : Seed, ((PY.map seed) s).toReal *
        dist (PX.map fun x => ext x s) (PMF.uniformOfFintype Output)
      ≤ ∑ s : Seed, ((Fintype.card Seed : ℝ) * (2 : ℝ) ^ (-kSeed)) *
          (((PMF.uniformOfFintype Seed) s).toReal *
            dist (PX.map fun x => ext x s) (PMF.uniformOfFintype Output)) := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ dist_nonneg
        rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
        have hmul : (Fintype.card Seed : ℝ) * (2 : ℝ) ^ (-kSeed) * (Fintype.card Seed : ℝ)⁻¹ =
            (2 : ℝ) ^ (-kSeed) := by field_simp
        rw [hmul]
        exact (le_minEntropy_iff _).mp hseed s
    _ = ((Fintype.card Seed : ℝ) * (2 : ℝ) ^ (-kSeed)) *
          ∑ s : Seed, ((PMF.uniformOfFintype Seed) s).toReal *
            dist (PX.map fun x => ext x s) (PMF.uniformOfFintype Output) :=
        (Finset.mul_sum ..).symm
    _ ≤ (Fintype.card Seed : ℝ) * (2 : ℝ) ^ (-kSeed) * ε := by
        rw [sum_uniform_dist_strongExtractor]
        exact mul_le_mul_of_nonneg_left (hext PX hPX) (by positivity)

end ImperfectSeed

/-! ### 2. Conditional-independence engine (`CondState`) -/

section CondEngine

/-- Support-preserving uniform-lifting: refines
`exists_dist_le_and_le_minEntropy_map_of_dist_uniform` so that `A'.support ⊆ A.support`. -/
private theorem exists_support_subset_lift_uniform {α β : Type*}
    [Fintype α] [Fintype β] [Nonempty β]
    (A : PMF α) (f : α → β) {γ : ℝ} (hγ1 : γ < 1)
    (hdist : dist (A.map f) (PMF.uniformOfFintype β) ≤ γ) :
    ∃ A' : PMF α, A'.support ⊆ A.support ∧ dist A A' ≤ γ ∧
      Real.logb 2 (Fintype.card β) + Real.logb 2 (1 - γ) ≤ minEntropy (A'.map f) := by
  classical
  let Sub := {a : α // a ∈ A.support}
  have hsum : ∑ a : Sub, A a.1 = 1 := by
    have htsum : ∑' a : α, A a = 1 := A.tsum_coe
    rw [tsum_fintype] at htsum
    rw [← htsum]
    have hfilter : ∑ a : Sub, A a.1 = ∑ a ∈ Finset.univ.filter (fun x => x ∈ A.support), A a := by
      rw [← Finset.sum_coe_sort (Finset.univ.filter fun x => x ∈ A.support)]
      exact Fintype.sum_equiv (Equiv.subtypeEquivRight fun x => by simp) _ _ fun _ => rfl
    rw [hfilter]
    refine Finset.sum_subset (Finset.filter_subset _ _) fun x _ hx => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact (A.apply_eq_zero_iff x).mpr hx
  let Asub : PMF Sub := PMF.ofFintype (fun a => A a.1) hsum
  have hval : Asub.map Subtype.val = A := by
    ext a
    rw [PMF.map_apply]
    by_cases ha : a ∈ A.support
    · rw [tsum_eq_single ⟨a, ha⟩]
      · simp [Asub]
      · intro b hb
        have hne : a ≠ b.1 := fun h => hb (Subtype.ext h.symm)
        simp [hne]
    · rw [(A.apply_eq_zero_iff a).mpr ha]
      have hzero : ∀ b : Sub, (if a = b.1 then Asub b else 0) = 0 := fun b => by
        have hne : a ≠ b.1 := fun h => ha (h ▸ b.2)
        simp [hne]
      simp [hzero]
  have hdist_sub : dist (Asub.map (f ∘ Subtype.val)) (PMF.uniformOfFintype β) ≤ γ := by
    have hcomp : Asub.map (f ∘ Subtype.val) = (Asub.map Subtype.val).map f := by
      rw [PMF.map_comp]
    rw [hcomp, hval]
    exact hdist
  obtain ⟨Asub', hd, hmin⟩ :=
    exists_dist_le_and_le_minEntropy_map_of_dist_uniform Asub (f ∘ Subtype.val) hγ1 hdist_sub
  refine ⟨Asub'.map Subtype.val, ?_, ?_, ?_⟩
  · intro a ha
    rw [PMF.mem_support_map_iff] at ha
    obtain ⟨b, -, rfl⟩ := ha
    exact b.2
  · calc dist A (Asub'.map Subtype.val)
        = dist (Asub.map Subtype.val) (Asub'.map Subtype.val) := by rw [hval]
      _ ≤ dist Asub Asub' := dist_map_le Asub Asub' Subtype.val
      _ ≤ γ := hd
  · have hcomp : (Asub'.map Subtype.val).map f = Asub'.map (f ∘ Subtype.val) := by
      rw [PMF.map_comp]
    rwa [hcomp]

/-- A conditioned product state `(μ, PX, PY)` together with a high-probability good transcript set
`good` whose complement has probability at most `bad`. -/
private structure CondState (α β T : Type) where
  μ : PMF T
  PX : T → PMF α
  PY : T → PMF β
  good : Set T
  bad : ℝ
  hbad : (μ.toOuterMeasure goodᶜ).toReal ≤ bad

namespace CondState

/-- Joint distribution `(τ, (x, y))` of a conditioned product state. -/
private noncomputable def joint {α β T : Type} (S : CondState α β T) : PMF (T × (α × β)) :=
  S.μ.bind fun τ => (S.PX τ).bind fun x => (S.PY τ).map fun y => (τ, (x, y))

private theorem support_of_mem_joint {α β T : Type} (S : CondState α β T)
    {τ : T} {x : α} {y : β} (hmem : (τ, (x, y)) ∈ S.joint.support) :
    τ ∈ S.μ.support ∧ x ∈ (S.PX τ).support ∧ y ∈ (S.PY τ).support := by
  simp only [joint, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hmem
  obtain ⟨τ', hτ', x', hx', y', hy', heq⟩ := hmem
  have h1 := congrArg Prod.fst heq
  have h2 := congrArg (fun p : T × _ => p.2.1) heq
  have h3 := congrArg (fun p : T × _ => p.2.2) heq
  dsimp only at h1 h2 h3
  rw [← h1, ← h2, ← h3]
  exact ⟨hτ', hx', hy'⟩

/-- Joint distribution `(obs x y, (x, y))` of independent `PX₀, PY₀`. -/
private noncomputable def realJoint {α β T : Type} (PX₀ : PMF α) (PY₀ : PMF β)
    (obs : α → β → T) : PMF (T × (α × β)) :=
  PX₀.bind fun x => PY₀.map fun y => (obs x y, (x, y))

open Classical in
/-- Average distance from uniform of a `Y`-measurable seed over good transcripts. -/
private noncomputable def seedErrY {α β T Seed : Type} [Fintype T] [Fintype Seed] [Nonempty Seed]
    (S : CondState α β T) (seed : T → β → Seed) : ℝ :=
  ∑ τ, if τ ∈ S.good then
    (S.μ τ).toReal * dist ((S.PY τ).map (seed τ)) (PMF.uniformOfFintype Seed)
  else 0

/-- Swap the roles of `X` and `Y`. -/
private noncomputable def swap {α β T : Type} (S : CondState α β T) : CondState β α T where
  μ := S.μ
  PX := S.PY
  PY := S.PX
  good := S.good
  bad := S.bad
  hbad := S.hbad

/-- Average distance from uniform of an `X`-measurable seed over good transcripts. -/
private noncomputable def seedErrX {α β T Seed : Type} [Fintype T] [Fintype Seed] [Nonempty Seed]
    (S : CondState α β T) (seed : T → α → Seed) : ℝ :=
  S.swap.seedErrY seed

private theorem seedErrY_nonneg {α β T Seed : Type} [Fintype T] [Fintype Seed] [Nonempty Seed]
    (S : CondState α β T) (seed : T → β → Seed) : 0 ≤ S.seedErrY seed :=
  Finset.sum_nonneg fun _ _ => by
    split_ifs
    · exact mul_nonneg ENNReal.toReal_nonneg dist_nonneg
    · exact le_rfl

private theorem seedErrY_equiv {α β T Seed1 Seed2 : Type}
    [Fintype T] [Fintype Seed1] [Nonempty Seed1] [Fintype Seed2] [Nonempty Seed2]
    (S : CondState α β T) (seed : T → β → Seed1) (e : Seed1 ≃ Seed2) :
    S.seedErrY (fun τ y => e (seed τ y)) = S.seedErrY seed := by
  classical
  refine Finset.sum_congr rfl fun τ _ => ?_
  split_ifs
  · congr 1
    have hmap : (S.PY τ).map (fun y => e (seed τ y)) = ((S.PY τ).map (seed τ)).map e :=
      (PMF.map_comp _ _ _).symm
    rw [hmap, ← PMF.uniformOfFintype_map_equiv e]
    exact le_antisymm (dist_map_le _ _ e) (by
      have hback := dist_map_le (((S.PY τ).map (seed τ)).map e)
        ((PMF.uniformOfFintype Seed1).map e) e.symm
      simpa only [PMF.map_comp, ← Function.comp_assoc, Equiv.symm_comp_self,
        Function.id_comp, PMF.map_id] using hback)
  · rfl

private theorem seedErrY_fst_le {α β T A B : Type}
    [Fintype T] [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (S : CondState α β T) (f : T → β → A) (g : T → β → B) :
    S.seedErrY f ≤ S.seedErrY (fun τ y => (f τ y, g τ y)) := by
  classical
  refine Finset.sum_le_sum fun τ _ => ?_
  split_ifs
  · refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    have hm : (S.PY τ).map (f τ) = ((S.PY τ).map fun y => (f τ y, g τ y)).map Prod.fst := by
      rw [PMF.map_comp]; rfl
    rw [hm, ← uniformOfFintype_prod_map_fst (α := A) (β := B)]
    exact dist_map_le _ _ Prod.fst
  · exact le_rfl

private theorem swap_joint {α β T : Type} (S : CondState α β T) :
    S.swap.joint = S.joint.map fun ⟨τ, x, y⟩ => (τ, (y, x)) := by
  simp only [swap, joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  refine congrArg (S.μ.bind ·) (funext fun τ => ?_)
  simp only [PMF.map, Function.comp_def]
  exact PMF.bind_comm (S.PY τ) (S.PX τ) _

/-- Initial unconditioned state on `Unit`. -/
private noncomputable def init {α β : Type} (PX₀ : PMF α) (PY₀ : PMF β) :
    CondState α β Unit where
  μ := PMF.pure ()
  PX _ := PX₀
  PY _ := PY₀
  good := Set.univ
  bad := 0
  hbad := by simp

private theorem init_joint {α β : Type} (PX₀ : PMF α) (PY₀ : PMF β) :
    (init PX₀ PY₀).joint = realJoint PX₀ PY₀ (fun _ _ => ()) := by
  simp only [init, joint, realJoint, PMF.pure_bind]

open Classical in
/-- Condition the `Y`-side on a deterministic leakage `leak : T → β → L`. -/
private noncomputable def condY {α β T L : Type} [Fintype T] [Fintype L]
    (S : CondState α β T) (leak : T → β → L) {δ : ℝ} (hδ : 0 ≤ δ) :
    CondState α β (T × L) where
  μ := S.μ.bind fun τ => (((S.PY τ).map fun y => (leak τ y, y)).map Prod.fst).map (τ, ·)
  PX p := S.PX p.1
  PY p := conditionalSnd ((S.PY p.1).map fun y => (leak p.1 y, y)) p.2
  good := {p | p.1 ∈ S.good ∧
    δ / Fintype.card L ≤ ((((S.PY p.1).map fun y => (leak p.1 y, y)).map Prod.fst) p.2).toReal}
  bad := S.bad + δ
  hbad := by
    classical
    let ν (τ : T) : PMF L := ((S.PY τ).map fun y => (leak τ y, y)).map Prod.fst
    rw [toOuterMeasure_apply_toReal, Fintype.sum_prod_type]
    have hpt (τ : T) (ℓ : L) :
        (if (τ, ℓ) ∈ ({p : T × L | p.1 ∈ S.good ∧ δ / Fintype.card L ≤ ((ν p.1) p.2).toReal})ᶜ
          then ((S.μ.bind fun t => (ν t).map (t, ·)) (τ, ℓ)).toReal else 0) ≤
        (S.μ τ).toReal * ((ν τ) ℓ).toReal * (if τ ∈ S.goodᶜ then (1 : ℝ) else 0) +
        (S.μ τ).toReal *
          (if ((ν τ) ℓ).toReal < δ / Fintype.card L then ((ν τ) ℓ).toReal else 0) := by
      have happ : ((S.μ.bind fun t => (ν t).map (t, ·)) (τ, ℓ)).toReal =
          (S.μ τ).toReal * ((ν τ) ℓ).toReal := by
        rw [bind_map_prodMk_apply, ENNReal.toReal_mul]
      rw [happ]
      by_cases hG : τ ∈ S.good
      · by_cases hL : δ / Fintype.card L ≤ ((ν τ) ℓ).toReal
        · have hnot : (τ, ℓ) ∉ ({p : T × L | p.1 ∈ S.good ∧
              δ / Fintype.card L ≤ ((ν p.1) p.2).toReal})ᶜ := fun h => h ⟨hG, hL⟩
          have hnotlt : ¬ ((ν τ) ℓ).toReal < δ / Fintype.card L := not_lt.mpr hL
          have hnotG : τ ∉ S.goodᶜ := not_not.mpr hG
          simp [hnot, hnotlt, hnotG]
        · have hmem : (τ, ℓ) ∈ ({p : T × L | p.1 ∈ S.good ∧
              δ / Fintype.card L ≤ ((ν p.1) p.2).toReal})ᶜ := fun h => hL h.2
          have hlt : ((ν τ) ℓ).toReal < δ / Fintype.card L := not_le.mp hL
          have hnotG : τ ∉ S.goodᶜ := not_not.mpr hG
          simp [hmem, hlt, hnotG]
      · have hmem : (τ, ℓ) ∈ ({p : T × L | p.1 ∈ S.good ∧
            δ / Fintype.card L ≤ ((ν p.1) p.2).toReal})ᶜ := fun h => hG h.1
        have hmemG : τ ∈ S.goodᶜ := hG
        simp only [hmem, hmemG, ↓reduceIte, mul_one]
        have hnn : 0 ≤ (S.μ τ).toReal *
            (if ((ν τ) ℓ).toReal < δ / Fintype.card L then ((ν τ) ℓ).toReal else 0) := by
          split_ifs <;> positivity
        linarith
    refine (Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun ℓ _ => by convert hpt τ ℓ).trans ?_
    have hsum1 (τ : T) :
        (∑ ℓ : L, ((S.μ τ).toReal * ((ν τ) ℓ).toReal * (if τ ∈ S.goodᶜ then (1 : ℝ) else 0) +
          (S.μ τ).toReal *
            (if ((ν τ) ℓ).toReal < δ / Fintype.card L then ((ν τ) ℓ).toReal else 0))) =
        (if τ ∈ S.goodᶜ then (S.μ τ).toReal else 0) +
        (S.μ τ).toReal *
          ((ν τ).toOuterMeasure {ℓ | ((ν τ) ℓ).toReal < δ / Fintype.card L}).toReal := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, PMF.sum_toReal, mul_one,
        ← Finset.mul_sum, toOuterMeasure_apply_toReal]
      congr 1
      by_cases h : τ ∈ S.goodᶜ <;> simp [h]
    calc ∑ τ : T, ∑ ℓ : L,
            ((S.μ τ).toReal * ((ν τ) ℓ).toReal * (if τ ∈ S.goodᶜ then (1 : ℝ) else 0) +
             (S.μ τ).toReal *
               (if ((ν τ) ℓ).toReal < δ / Fintype.card L then ((ν τ) ℓ).toReal else 0))
        = (∑ τ : T, if τ ∈ S.goodᶜ then (S.μ τ).toReal else 0) +
          (∑ τ : T, (S.μ τ).toReal *
            ((ν τ).toOuterMeasure {ℓ | ((ν τ) ℓ).toReal < δ / Fintype.card L}).toReal) := by
          simp_rw [hsum1, Finset.sum_add_distrib]
      _ ≤ (S.μ.toOuterMeasure S.goodᶜ).toReal + ∑ τ : T, (S.μ τ).toReal * δ := by
          refine add_le_add ?_ (Finset.sum_le_sum fun τ _ => ?_)
          · rw [toOuterMeasure_apply_toReal]
            exact Finset.sum_le_sum fun τ _ => by convert le_rfl
          · exact mul_le_mul_of_nonneg_left (toOuterMeasure_badLeak_le (ν τ) hδ)
              ENNReal.toReal_nonneg
      _ ≤ S.bad + δ := by
          rw [← Finset.sum_mul, PMF.sum_toReal, one_mul]
          linarith [S.hbad]

private theorem condY_joint {α β T L : Type} [Fintype T] [Fintype L]
    (S : CondState α β T) (leak : T → β → L) {δ : ℝ} (hδ : 0 ≤ δ) :
    (S.condY leak hδ).joint = S.joint.map fun ⟨τ, x, y⟩ => ((τ, leak τ y), (x, y)) := by
  simp only [condY, joint, PMF.bind_bind, PMF.map_bind, PMF.map_comp, Function.comp_def]
  refine congrArg (S.μ.bind ·) (funext fun τ => ?_)
  let J := (S.PY τ).map fun y => (leak τ y, y)
  have hrec := bind_conditionalSnd J
  have hlhs :
      ((J.map Prod.fst).bind fun ℓ =>
        (S.PX τ).bind fun x => (conditionalSnd J ℓ).map fun y => ((τ, ℓ), (x, y))) =
      (S.PX τ).bind fun x =>
        ((J.map Prod.fst).bind fun ℓ => (conditionalSnd J ℓ).map (ℓ, ·)).map
          fun ⟨ℓ, y⟩ => ((τ, ℓ), (x, y)) := by
    rw [PMF.bind_comm]
    refine congrArg ((S.PX τ).bind ·) (funext fun x => ?_)
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hrhs :
      (S.PX τ).bind (fun x => J.map fun ⟨ℓ, y⟩ => ((τ, ℓ), (x, y))) =
      (S.PX τ).bind fun x => (S.PY τ).map fun y => ((τ, leak τ y), (x, y)) := by
    refine congrArg ((S.PX τ).bind ·) (funext fun x => ?_)
    simp only [J, PMF.map_comp, Function.comp_def]
  calc _ = (J.map Prod.fst).bind fun ℓ =>
          (S.PX τ).bind fun x => (conditionalSnd J ℓ).map fun y => ((τ, ℓ), (x, y)) := by
        simp only [PMF.bind_map, Function.comp_def, J]
    _ = (S.PX τ).bind fun x => J.map fun ⟨ℓ, y⟩ => ((τ, ℓ), (x, y)) := by
        rw [hlhs, hrec]
    _ = (S.PX τ).bind fun x => (S.PY τ).map fun y => ((τ, leak τ y), (x, y)) := hrhs

private theorem condY_support {α β T L : Type} [Fintype T] [Fintype L]
    (S : CondState α β T) (leak : T → β → L) {δ : ℝ} (hδ : 0 ≤ δ)
    {τ : T} {ℓ : L} (hp : (τ, ℓ) ∈ (S.condY leak hδ).μ.support)
    {x : α} (hx : x ∈ ((S.condY leak hδ).PX (τ, ℓ)).support)
    {y : β} (hy : y ∈ ((S.condY leak hδ).PY (τ, ℓ)).support) :
    τ ∈ S.μ.support ∧ x ∈ (S.PX τ).support ∧ y ∈ (S.PY τ).support ∧ leak τ y = ℓ := by
  have hp' : τ ∈ S.μ.support ∧
      ℓ ∈ (((S.PY τ).map fun b => (leak τ b, b)).map Prod.fst).support := by
    have hnz : (S.condY leak hδ).μ (τ, ℓ) ≠ 0 := hp
    simp only [condY, bind_map_prodMk_apply, mul_ne_zero_iff] at hnz
    exact hnz
  have hmy := mem_support_and_eq_of_conditionalSnd_map (S.PY τ) (leak τ) hp'.2 hy
  exact ⟨hp'.1, hx, hmy.1, hmy.2⟩

private theorem condY_fst_mem_support {α β T L : Type} [Fintype T] [Fintype L]
    (S : CondState α β T) (leak : T → β → L) {δ : ℝ} (hδ : 0 ≤ δ)
    {p : T × L} (hp : p ∈ (S.condY leak hδ).μ.support) : p.1 ∈ S.μ.support := by
  rcases p with ⟨τ, ℓ⟩
  have hnz : (S.condY leak hδ).μ (τ, ℓ) ≠ 0 := hp
  simp only [condY, bind_map_prodMk_apply, mul_ne_zero_iff] at hnz
  exact hnz.1

private theorem condY_minEntropy_Y {α β T L γ : Type} [Fintype T] [Fintype L]
    (S : CondState α β T) (leak : T → β → L) {δ k : ℝ} (hδ : 0 < δ) (f : β → γ)
    (hY : ∀ τ ∈ S.good, τ ∈ S.μ.support → k ≤ minEntropy ((S.PY τ).map f))
    {p : T × L} (hpG : p ∈ (S.condY leak hδ.le).good)
    (hpS : p ∈ (S.condY leak hδ.le).μ.support) :
    k - Real.logb 2 (Fintype.card L) - Real.logb 2 δ⁻¹ ≤
      minEntropy (((S.condY leak hδ.le).PY p).map f) := by
  have h1 : p.1 ∈ S.μ.support := condY_fst_mem_support S leak hδ.le hpS
  have hJ_snd : (((S.PY p.1).map fun y => (leak p.1 y, y)).map Prod.snd).map f =
      (S.PY p.1).map f := by
    simp only [PMF.map_comp, Function.comp_def]
  exact minEntropy_map_conditionalSnd_ge_of_apply_ge
    ((S.PY p.1).map fun y => (leak p.1 y, y)) f hδ (hJ_snd.symm ▸ hY p.1 hpG.1 h1) hpG.2

private theorem condY_minEntropy_X {α β T L γ : Type} [Fintype T] [Fintype L]
    (S : CondState α β T) (leak : T → β → L) {δ k : ℝ} (hδ : 0 ≤ δ) (f : α → γ)
    (hX : ∀ τ ∈ S.good, τ ∈ S.μ.support → k ≤ minEntropy ((S.PX τ).map f))
    {p : T × L} (hpG : p ∈ (S.condY leak hδ).good)
    (hpS : p ∈ (S.condY leak hδ).μ.support) :
    k ≤ minEntropy (((S.condY leak hδ).PX p).map f) :=
  hX p.1 hpG.1 (condY_fst_mem_support S leak hδ hpS)

/-- Condition the `X`-side on a deterministic leakage `leak : T → α → L`. -/
private noncomputable def condX {α β T L : Type} [Fintype T] [Fintype L]
    (S : CondState α β T) (leak : T → α → L) {δ : ℝ} (hδ : 0 ≤ δ) :
    CondState α β (T × L) :=
  (S.swap.condY leak hδ).swap

private theorem condX_joint {α β T L : Type} [Fintype T] [Fintype L]
    (S : CondState α β T) (leak : T → α → L) {δ : ℝ} (hδ : 0 ≤ δ) :
    (S.condX leak hδ).joint = S.joint.map fun ⟨τ, x, y⟩ => ((τ, leak τ x), (x, y)) := by
  rw [condX, swap_joint, condY_joint, swap_joint, PMF.map_comp, PMF.map_comp]
  rfl

private theorem condX_support {α β T L : Type} [Fintype T] [Fintype L]
    (S : CondState α β T) (leak : T → α → L) {δ : ℝ} (hδ : 0 ≤ δ)
    {τ : T} {ℓ : L} (hp : (τ, ℓ) ∈ (S.condX leak hδ).μ.support)
    {x : α} (hx : x ∈ ((S.condX leak hδ).PX (τ, ℓ)).support)
    {y : β} (hy : y ∈ ((S.condX leak hδ).PY (τ, ℓ)).support) :
    τ ∈ S.μ.support ∧ x ∈ (S.PX τ).support ∧ y ∈ (S.PY τ).support ∧ leak τ x = ℓ := by
  obtain ⟨hτ, hy', hx', hle⟩ := condY_support S.swap leak hδ hp hy hx
  exact ⟨hτ, hx', hy', hle⟩

private theorem condX_minEntropy_X {α β T L γ : Type} [Fintype T] [Fintype L]
    (S : CondState α β T) (leak : T → α → L) {δ k : ℝ} (hδ : 0 < δ) (f : α → γ)
    (hX : ∀ τ ∈ S.good, τ ∈ S.μ.support → k ≤ minEntropy ((S.PX τ).map f))
    {p : T × L} (hpG : p ∈ (S.condX leak hδ.le).good)
    (hpS : p ∈ (S.condX leak hδ.le).μ.support) :
    k - Real.logb 2 (Fintype.card L) - Real.logb 2 δ⁻¹ ≤
      minEntropy (((S.condX leak hδ.le).PX p).map f) :=
  condY_minEntropy_Y S.swap leak hδ f hX hpG hpS

private theorem condX_minEntropy_Y {α β T L γ : Type} [Fintype T] [Fintype L]
    (S : CondState α β T) (leak : T → α → L) {δ k : ℝ} (hδ : 0 ≤ δ) (f : β → γ)
    (hY : ∀ τ ∈ S.good, τ ∈ S.μ.support → k ≤ minEntropy ((S.PY τ).map f))
    {p : T × L} (hpG : p ∈ (S.condX leak hδ).good)
    (hpS : p ∈ (S.condX leak hδ).μ.support) :
    k ≤ minEntropy (((S.condX leak hδ).PY p).map f) :=
  condY_minEntropy_X S.swap leak hδ f hY hpG hpS

/-- Conditioning the `Y`-side preserves `seedErrX` for any `X`-measurable seed depending only on
the old transcript. -/
private theorem condY_seedErrX_le {α β T L Seed : Type}
    [Fintype T] [Fintype L] [Fintype Seed] [Nonempty Seed]
    (S : CondState α β T) (leak : T → β → L) {δ : ℝ} (hδ : 0 ≤ δ) (seed : T → α → Seed) :
    (S.condY leak hδ).seedErrX (fun p => seed p.1) ≤ S.seedErrX seed := by
  classical
  simp only [seedErrX, seedErrY, swap, condY]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun τ _ => ?_
  by_cases hG : τ ∈ S.good
  · simp only [hG, ↓reduceIte]
    let ν : PMF L := ((S.PY τ).map fun y => (leak τ y, y)).map Prod.fst
    have hbound : ∑ ℓ : L, ((S.μ τ).toReal * (ν ℓ).toReal) *
        dist ((S.PX τ).map (seed τ)) (PMF.uniformOfFintype Seed) =
        (S.μ τ).toReal * dist ((S.PX τ).map (seed τ)) (PMF.uniformOfFintype Seed) := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, ← Finset.sum_mul, PMF.sum_toReal, one_mul]
    rw [← hbound]
    refine Finset.sum_le_sum fun ℓ _ => ?_
    rw [bind_map_prodMk_apply, ENNReal.toReal_mul]
    by_cases hmem : (τ, ℓ) ∈ {p : T × L | p.1 ∈ S.good ∧
        δ / Fintype.card L ≤
          ((((S.PY p.1).map fun y => (leak p.1 y, y)).map Prod.fst) p.2).toReal}
    · simp only [hmem, ↓reduceIte]; exact le_rfl
    · simp only [hmem, ↓reduceIte]
      exact mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) dist_nonneg
  · simp only [hG, ↓reduceIte]
    refine le_of_eq (Finset.sum_eq_zero fun ℓ _ => ?_)
    have hnot : (τ, ℓ) ∉ {p : T × L | p.1 ∈ S.good ∧
        δ / Fintype.card L ≤
          ((((S.PY p.1).map fun y => (leak p.1 y, y)).map Prod.fst) p.2).toReal} :=
      fun h => hG h.1
    simp only [hnot, ↓reduceIte]

/-- Conditioning the `X`-side preserves `seedErrY` for any `Y`-measurable seed depending only on
the old transcript. -/
private theorem condX_seedErrY_le {α β T L Seed : Type}
    [Fintype T] [Fintype L] [Fintype Seed] [Nonempty Seed]
    (S : CondState α β T) (leak : T → α → L) {δ : ℝ} (hδ : 0 ≤ δ) (seed : T → β → Seed) :
    (S.condX leak hδ).seedErrY (fun p => seed p.1) ≤ S.seedErrY seed :=
  condY_seedErrX_le S.swap leak hδ seed

open Classical in
/-- **Core good-transcript extraction sum**: applying a strong extractor `ext` on the `X`-side with
a `Y`-measurable seed (and optional `Y`-measurable XOR shift) produces output whose good-transcript
average distance from uniform jointly with `Y` is at most `S.seedErrY seed + ε`. -/
private theorem extractX_good_sum {α β T Seed : Type} {nX m : ℕ}
    [Fintype T] [Fintype β] [Fintype Seed] [Nonempty Seed]
    (S : CondState α β T) (projX : α → BitString nX)
    {ext : BitString nX → Seed → BitString m} {k ε : ℝ} (hε : 0 ≤ ε)
    (hext : IsStrongExtractor ext k ε)
    (hX : ∀ τ ∈ S.good, τ ∈ S.μ.support → k ≤ minEntropy ((S.PX τ).map projX))
    (seed : T → β → Seed) (shift : T → β → BitString m) :
    (∑ τ : T, if τ ∈ S.good then
      (S.μ τ).toReal * dist
        ((S.PY τ).bind fun y => (S.PX τ).map fun x => (y, ext (projX x) (seed τ y) + shift τ y))
        ((S.PY τ).bind fun y => (PMF.uniformOfFintype (BitString m)).map fun u => (y, u))
      else 0) ≤ S.seedErrY seed + ε := by
  classical
  calc ∑ τ : T, (if τ ∈ S.good then
          (S.μ τ).toReal * dist
            ((S.PY τ).bind fun y => (S.PX τ).map fun x =>
              (y, ext (projX x) (seed τ y) + shift τ y))
            ((S.PY τ).bind fun y => (PMF.uniformOfFintype (BitString m)).map fun u => (y, u))
        else 0)
      ≤ ∑ τ : T, ((if τ ∈ S.good then
            (S.μ τ).toReal * dist ((S.PY τ).map (seed τ)) (PMF.uniformOfFintype Seed) else 0) +
          (S.μ τ).toReal * ε) := by
        refine Finset.sum_le_sum fun τ _ => ?_
        by_cases hG : τ ∈ S.good
        · simp only [hG, ↓reduceIte]
          by_cases hS : τ ∈ S.μ.support
          · have hrew : ((S.PY τ).bind fun y => (S.PX τ).map fun x =>
                  (y, ext (projX x) (seed τ y) + shift τ y)) =
                (S.PY τ).bind fun y => ((S.PX τ).map projX).map fun z =>
                  (y, ext z (seed τ y) + shift τ y) := by
              refine congrArg ((S.PY τ).bind ·) (funext fun y => ?_)
              rw [PMF.map_comp]; rfl
            rw [hrew]
            have hstep := dist_strongExtractor_nearUniform_seed_add_le hext (hX τ hG hS)
              (S.PY τ) (seed τ) (shift τ)
            have hmul := mul_le_mul_of_nonneg_left hstep (ENNReal.toReal_nonneg (a := S.μ τ))
            linarith
          · rw [(S.μ.apply_eq_zero_iff τ).mpr hS, ENNReal.toReal_zero]
            simp
        · simp only [hG, ↓reduceIte, zero_add]
          exact mul_nonneg ENNReal.toReal_nonneg hε
    _ = S.seedErrY seed + ε := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, PMF.sum_toReal, one_mul]
        rfl

/-- **Extraction followed by `condY`**: after extracting `ext (projX x) (seed τ y) + shift τ y`
and revealing a `Y`-side leakage `leak` that determines both `seed` and `shift`, the extracted
output is `X`-measurable with `seedErrX ≤ S.seedErrY seed + ε`. -/
private theorem extractX_condY_seedErrX_le {α β T L Seed : Type} {nX m : ℕ}
    [Fintype T] [Finite β] [Fintype L] [Fintype Seed] [Nonempty Seed]
    (S : CondState α β T) (projX : α → BitString nX)
    {ext : BitString nX → Seed → BitString m} {k ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hext : IsStrongExtractor ext k ε)
    (hX : ∀ τ ∈ S.good, τ ∈ S.μ.support → k ≤ minEntropy ((S.PX τ).map projX))
    (leak : T → β → L) (seedOf : T × L → Seed) (shiftOf : T × L → BitString m) :
    (S.condY leak hδ).seedErrX (fun p x => ext (projX x) (seedOf p) + shiftOf p) ≤
      S.seedErrY (fun τ y => seedOf (τ, leak τ y)) + ε := by
  classical
  let _ := Fintype.ofFinite β
  have hsum := extractX_good_sum S projX hε hext hX
    (fun τ y => seedOf (τ, leak τ y)) (fun τ y => shiftOf (τ, leak τ y))
  refine le_trans ?_ hsum
  simp only [seedErrX, seedErrY, swap, condY]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun τ _ => ?_
  by_cases hG : τ ∈ S.good
  · simp only [hG, ↓reduceIte]
    let ν : PMF L := ((S.PY τ).map fun y => (leak τ y, y)).map Prod.fst
    have hinner :
        ∑ ℓ : L, (ν ℓ).toReal *
            dist ((S.PX τ).map fun x => ext (projX x) (seedOf (τ, ℓ)) + shiftOf (τ, ℓ))
              (PMF.uniformOfFintype (BitString m)) ≤
          dist ((S.PY τ).bind fun y => (S.PX τ).map fun x =>
              (y, ext (projX x) (seedOf (τ, leak τ y)) + shiftOf (τ, leak τ y)))
            ((S.PY τ).bind fun y => (PMF.uniformOfFintype (BitString m)).map fun u => (y, u)) := by
      rw [← dist_bind_pair ν
        (fun ℓ => (S.PX τ).map fun x => ext (projX x) (seedOf (τ, ℓ)) + shiftOf (τ, ℓ))
        (fun _ => PMF.uniformOfFintype (BitString m))]
      have hmapL :
          (ν.bind fun ℓ =>
            ((S.PX τ).map fun x => ext (projX x) (seedOf (τ, ℓ)) + shiftOf (τ, ℓ)).map (ℓ, ·)) =
          ((S.PY τ).bind fun y => (S.PX τ).map fun x =>
            (y, ext (projX x) (seedOf (τ, leak τ y)) + shiftOf (τ, leak τ y))).map
              fun ⟨y, z⟩ => (leak τ y, z) := by
        simp only [ν, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
      have hmapR :
          (ν.bind fun ℓ => (PMF.uniformOfFintype (BitString m)).map (ℓ, ·)) =
          ((S.PY τ).bind fun y =>
            (PMF.uniformOfFintype (BitString m)).map fun u => (y, u)).map
              fun ⟨y, z⟩ => (leak τ y, z) := by
        simp only [ν, PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
      rw [hmapL, hmapR]
      exact dist_map_le _ _ _
    have hbound : ∑ ℓ : L, (S.μ τ).toReal * ((ν ℓ).toReal *
          dist ((S.PX τ).map fun x => ext (projX x) (seedOf (τ, ℓ)) + shiftOf (τ, ℓ))
            (PMF.uniformOfFintype (BitString m))) ≤
        (S.μ τ).toReal *
          dist ((S.PY τ).bind fun y => (S.PX τ).map fun x =>
              (y, ext (projX x) (seedOf (τ, leak τ y)) + shiftOf (τ, leak τ y)))
            ((S.PY τ).bind fun y => (PMF.uniformOfFintype (BitString m)).map fun u => (y, u)) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hinner (ENNReal.toReal_nonneg (a := S.μ τ))
    refine (Finset.sum_le_sum (g := fun ℓ : L => (S.μ τ).toReal * ((ν ℓ).toReal *
      dist ((S.PX τ).map fun x => ext (projX x) (seedOf (τ, ℓ)) + shiftOf (τ, ℓ))
        (PMF.uniformOfFintype (BitString m)))) fun ℓ _ => ?_).trans hbound
    rw [bind_map_prodMk_apply, ENNReal.toReal_mul, mul_assoc]
    by_cases hmem : (τ, ℓ) ∈ {p : T × L | p.1 ∈ S.good ∧
        δ / Fintype.card L ≤
          ((((S.PY p.1).map fun y => (leak p.1 y, y)).map Prod.fst) p.2).toReal}
    · simp only [hmem, ↓reduceIte]; exact le_rfl
    · simp only [hmem, ↓reduceIte]
      exact mul_nonneg ENNReal.toReal_nonneg (mul_nonneg ENNReal.toReal_nonneg dist_nonneg)
  · simp only [hG, ↓reduceIte]
    refine le_of_eq (Finset.sum_eq_zero fun ℓ _ => ?_)
    have hnot : (τ, ℓ) ∉ {p : T × L | p.1 ∈ S.good ∧
        δ / Fintype.card L ≤
          ((((S.PY p.1).map fun y => (leak p.1 y, y)).map Prod.fst) p.2).toReal} :=
      fun h => hG h.1
    simp only [hnot, ↓reduceIte]

/-- Symmetric `Y`-side extraction followed by `condX`. -/
private theorem extractY_condX_seedErrY_le {α β T L Seed : Type} {nY m : ℕ}
    [Fintype T] [Finite α] [Fintype L] [Fintype Seed] [Nonempty Seed]
    (S : CondState α β T) (projY : β → BitString nY)
    {ext : BitString nY → Seed → BitString m} {k ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hext : IsStrongExtractor ext k ε)
    (hY : ∀ τ ∈ S.good, τ ∈ S.μ.support → k ≤ minEntropy ((S.PY τ).map projY))
    (leak : T → α → L) (seedOf : T × L → Seed) (shiftOf : T × L → BitString m) :
    (S.condX leak hδ).seedErrY (fun p y => ext (projY y) (seedOf p) + shiftOf p) ≤
      S.seedErrX (fun τ x => seedOf (τ, leak τ x)) + ε :=
  extractX_condY_seedErrX_le S.swap projY hε hδ hext hY leak seedOf shiftOf

/-- **Final extraction readout**: converts `extractX_good_sum` into a joint statistical distance
bound against an independent uniform string alongside any `(τ, y)`-measurable observation
`obsOut`. -/
private theorem extractX_dist_le {α β T Seed Obs : Type} {nX m : ℕ}
    [Fintype T] [Finite β] [Fintype Seed] [Nonempty Seed] [Fintype Obs]
    (S : CondState α β T) (projX : α → BitString nX)
    {ext : BitString nX → Seed → BitString m} {k ε : ℝ} (hε : 0 ≤ ε)
    (hext : IsStrongExtractor ext k ε)
    (hX : ∀ τ ∈ S.good, τ ∈ S.μ.support → k ≤ minEntropy ((S.PX τ).map projX))
    (seed : T → β → Seed) (shift : T → β → BitString m) (obsOut : T → β → Obs) :
    dist
      (S.joint.map fun ⟨τ, x, y⟩ => (obsOut τ y, ext (projX x) (seed τ y) + shift τ y))
      ((S.joint.map fun ⟨τ, _, y⟩ => obsOut τ y).bind fun o =>
        (PMF.uniformOfFintype (BitString m)).map fun u => (o, u)) ≤
      S.bad + S.seedErrY seed + ε := by
  classical
  let _ := Fintype.ofFinite β
  let P (τ : T) : PMF (β × BitString m) :=
    (S.PY τ).bind fun y => (S.PX τ).map fun x => (y, ext (projX x) (seed τ y) + shift τ y)
  let Q (τ : T) : PMF (β × BitString m) :=
    (S.PY τ).bind fun y => (PMF.uniformOfFintype (BitString m)).map fun u => (y, u)
  let f : T × (β × BitString m) → Obs × BitString m := fun ⟨τ, y, z⟩ => (obsOut τ y, z)
  have hL : (S.joint.map fun ⟨τ, x, y⟩ => (obsOut τ y, ext (projX x) (seed τ y) + shift τ y)) =
      (S.μ.bind fun τ => (P τ).map (τ, ·)).map f := by
    simp only [joint, P, f, PMF.map_bind, PMF.map_comp, Function.comp_def]
    refine congrArg (S.μ.bind ·) (funext fun τ => ?_)
    simp only [PMF.map, Function.comp_def]
    exact PMF.bind_comm (S.PX τ) (S.PY τ) _
  have hR : ((S.joint.map fun ⟨τ, _, y⟩ => obsOut τ y).bind fun o =>
        (PMF.uniformOfFintype (BitString m)).map fun u => (o, u)) =
      (S.μ.bind fun τ => (Q τ).map (τ, ·)).map f := by
    simp only [joint, Q, f, PMF.map_bind, PMF.bind_bind, PMF.bind_map, PMF.map_comp,
      Function.comp_def]
    refine congrArg (S.μ.bind ·) (funext fun τ => ?_)
    exact PMF.bind_const (S.PX τ) _
  rw [hL, hR]
  refine (dist_map_le _ _ f).trans ?_
  rw [dist_bind_pair]
  have hsplit : ∑ τ : T, (S.μ τ).toReal * dist (P τ) (Q τ) ≤
      (S.μ.toOuterMeasure S.goodᶜ).toReal +
      ∑ τ : T, if τ ∈ S.good then (S.μ τ).toReal * dist (P τ) (Q τ) else 0 := by
    rw [toOuterMeasure_apply_toReal, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun τ _ => ?_
    by_cases hG : τ ∈ S.good
    · have hnot : τ ∉ S.goodᶜ := not_not.mpr hG
      simp only [hG, hnot, ↓reduceIte, zero_add, le_rfl]
    · have hmem : τ ∈ S.goodᶜ := hG
      simp only [hG, hmem, ↓reduceIte, add_zero]
      exact mul_le_of_le_one_right ENNReal.toReal_nonneg (dist_le_one _ _)
  have hgood := extractX_good_sum S projX hε hext hX seed shift
  linarith [S.hbad]

/-- **Seed readout**: if `seed : T → β → Output` has `S.seedErrY seed ≤ η`, then
`(obs τ x, seed τ y)` is within `S.bad + η` of `(obs τ x, U)` because `PX τ` and `PY τ` are
conditionally independent. -/
private theorem seedErrY_dist_le {α β T Output Obs : Type}
    [Fintype T] [Finite α] [Fintype Output] [Nonempty Output] [Fintype Obs]
    (S : CondState α β T) (seed : T → β → Output) (obsOut : T → α → Obs) :
    dist
      (S.joint.map fun ⟨τ, x, y⟩ => (obsOut τ x, seed τ y))
      ((S.joint.map fun ⟨τ, x, _⟩ => obsOut τ x).bind fun o =>
        (PMF.uniformOfFintype Output).map fun u => (o, u)) ≤
      S.bad + S.seedErrY seed := by
  classical
  let _ := Fintype.ofFinite α
  let P (τ : T) : PMF (α × Output) :=
    (S.PX τ).bind fun x => ((S.PY τ).map (seed τ)).map (x, ·)
  let Q (τ : T) : PMF (α × Output) :=
    (S.PX τ).bind fun x => (PMF.uniformOfFintype Output).map (x, ·)
  let f : T × (α × Output) → Obs × Output := fun ⟨τ, x, z⟩ => (obsOut τ x, z)
  have hL : (S.joint.map fun ⟨τ, x, y⟩ => (obsOut τ x, seed τ y)) =
      (S.μ.bind fun τ => (P τ).map (τ, ·)).map f := by
    simp only [joint, P, f, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hR : ((S.joint.map fun ⟨τ, x, _⟩ => obsOut τ x).bind fun o =>
        (PMF.uniformOfFintype Output).map fun u => (o, u)) =
      (S.μ.bind fun τ => (Q τ).map (τ, ·)).map f := by
    simp only [joint, Q, f, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
    refine congrArg (S.μ.bind ·) (funext fun τ => congrArg ((S.PX τ).bind ·) (funext fun x => ?_))
    exact PMF.bind_const (S.PY τ) _
  rw [hL, hR]
  refine (dist_map_le _ _ f).trans ?_
  rw [dist_bind_pair]
  have hPQ (τ : T) :
      dist (P τ) (Q τ) = dist ((S.PY τ).map (seed τ)) (PMF.uniformOfFintype Output) := by
    rw [dist_bind_pair, ← Finset.sum_mul, PMF.sum_toReal, one_mul]
  simp_rw [hPQ]
  have hsplit : ∑ τ : T, (S.μ τ).toReal *
        dist ((S.PY τ).map (seed τ)) (PMF.uniformOfFintype Output) ≤
      (S.μ.toOuterMeasure S.goodᶜ).toReal + S.seedErrY seed := by
    rw [toOuterMeasure_apply_toReal, seedErrY, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun τ _ => ?_
    by_cases hG : τ ∈ S.good
    · have hnot : τ ∉ S.goodᶜ := not_not.mpr hG
      simp only [hG, hnot, ↓reduceIte, zero_add, le_rfl]
    · have hmem : τ ∈ S.goodᶜ := hG
      simp only [hG, hmem, ↓reduceIte, add_zero]
      exact mul_le_of_le_one_right ENNReal.toReal_nonneg (dist_le_one _ _)
  linarith [S.hbad]

/-- **Support-preserving uniform-lifting on `CondState`**:
if `(g τ y, f τ y)` has `S.seedErrY ≤ η` on `BitString d1 × BitString m1`, there is a nearby state
`S'` with the same `μ, PX`, support `(S'.PY τ).support ⊆ (S.PY τ).support`, `dist S.joint S'.joint
≤ η`, `S'.bad = S.bad + 2 * η`, `S'.seedErrY g ≤ 2 * η`, and exact min-entropy `m1 - 1` on
`(S'.PY τ).map (f τ)` for every `τ ∈ S'.good`. -/
private theorem liftY_pair {α β T : Type} {d1 m1 : ℕ} [Fintype α] [Fintype β] [Fintype T]
    (S : CondState α β T) (g : T → β → BitString d1) (f : T → β → BitString m1)
    {η : ℝ} (hη : S.seedErrY (fun τ y => (g τ y, f τ y)) ≤ η) :
    ∃ S' : CondState α β T,
      S'.μ = S.μ ∧ S'.PX = S.PX ∧ S'.good ⊆ S.good ∧
      S'.bad = S.bad + 2 * η ∧
      (∀ τ, (S'.PY τ).support ⊆ (S.PY τ).support) ∧
      dist S.joint S'.joint ≤ η ∧
      S'.seedErrY g ≤ 2 * η ∧
      (∀ τ ∈ S'.good, (m1 : ℝ) - 1 ≤ minEntropy ((S'.PY τ).map (f τ))) := by
  classical
  let e (τ : T) : ℝ :=
    dist ((S.PY τ).map fun y => (g τ y, f τ y))
      (PMF.uniformOfFintype (BitString d1 × BitString m1))
  let good' : Set T := {τ | τ ∈ S.good ∧ e τ ≤ 1 / 2}
  have he_snd (τ : T) : dist ((S.PY τ).map (f τ)) (PMF.uniformOfFintype (BitString m1)) ≤ e τ := by
    have hm : (S.PY τ).map (f τ) = ((S.PY τ).map fun y => (g τ y, f τ y)).map Prod.snd := by
      rw [PMF.map_comp]; rfl
    rw [hm, ← uniformOfFintype_prod_map_snd (α := BitString d1) (β := BitString m1)]
    exact dist_map_le _ _ Prod.snd
  have he_fst (τ : T) : dist ((S.PY τ).map (g τ)) (PMF.uniformOfFintype (BitString d1)) ≤ e τ := by
    have hm : (S.PY τ).map (g τ) = ((S.PY τ).map fun y => (g τ y, f τ y)).map Prod.fst := by
      rw [PMF.map_comp]; rfl
    rw [hm, ← uniformOfFintype_prod_map_fst (α := BitString d1) (β := BitString m1)]
    exact dist_map_le _ _ Prod.fst
  have hlifted (τ : T) :
      ∃ q : PMF β, q.support ⊆ (S.PY τ).support ∧
        (τ ∈ good' → dist (S.PY τ) q ≤ e τ ∧ (m1 : ℝ) - 1 ≤ minEntropy (q.map (f τ))) ∧
        (τ ∉ good' → q = S.PY τ) := by
    by_cases hG : τ ∈ good'
    · have he_lt : e τ < 1 := lt_of_le_of_lt hG.2 (by norm_num)
      obtain ⟨q, hsupp, hd, hmin⟩ :=
        exists_support_subset_lift_uniform (S.PY τ) (f τ) he_lt (he_snd τ)
      refine ⟨q, hsupp, fun _ => ⟨hd, ?_⟩, fun h => absurd hG h⟩
      have hcard : Real.logb 2 (Fintype.card (BitString m1)) = (m1 : ℝ) := by
        simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
          Nat.cast_ofNat, Real.logb_two_pow]
      have hlog_ge : (-1 : ℝ) ≤ Real.logb 2 (1 - e τ) := by
        have hhalf : Real.logb 2 (2 : ℝ)⁻¹ = -1 := by
          rw [Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
        rw [← hhalf]
        exact Real.logb_le_logb_of_le one_lt_two (by norm_num) (by linarith [hG.2])
      linarith
    · exact ⟨S.PY τ, Set.Subset.rfl, fun h => absurd h hG, fun _ => rfl⟩
  choose PY' hsupp' hgood' hbad_eq using hlifted
  have hbad' : (S.μ.toOuterMeasure good'ᶜ).toReal ≤ S.bad + 2 * η := by
    rw [toOuterMeasure_apply_toReal]
    have hpt (τ : T) :
        (if τ ∈ good'ᶜ then (S.μ τ).toReal else 0) ≤
        (if τ ∈ S.goodᶜ then (S.μ τ).toReal else 0) +
        2 * (if τ ∈ S.good then (S.μ τ).toReal * e τ else 0) := by
      by_cases hG : τ ∈ S.good
      · by_cases he : e τ ≤ 1 / 2
        · have hnot : τ ∉ good'ᶜ := fun h => h ⟨hG, he⟩
          have hnotG : τ ∉ S.goodᶜ := not_not.mpr hG
          simp only [hnot, hnotG, hG, ↓reduceIte, zero_add]
          exact mul_nonneg zero_le_two (mul_nonneg ENNReal.toReal_nonneg dist_nonneg)
        · have hmem : τ ∈ good'ᶜ := fun h => he h.2
          have hnotG : τ ∉ S.goodᶜ := not_not.mpr hG
          have hgt : 1 / 2 < e τ := not_le.mp he
          simp only [hmem, hnotG, hG, ↓reduceIte, zero_add]
          nlinarith [ENNReal.toReal_nonneg (a := S.μ τ)]
      · have hmem : τ ∈ good'ᶜ := fun h => hG h.1
        have hmemG : τ ∈ S.goodᶜ := hG
        simp [hmem, hmemG, hG]
    refine (Finset.sum_le_sum fun τ _ => by convert hpt τ).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 : (∑ τ : T, if τ ∈ S.goodᶜ then (S.μ τ).toReal else 0) =
        (S.μ.toOuterMeasure S.goodᶜ).toReal := by
      rw [toOuterMeasure_apply_toReal]
      exact Finset.sum_congr rfl fun τ _ => by convert rfl
    have h2 : (∑ τ : T, if τ ∈ S.good then (S.μ τ).toReal * e τ else 0) =
        S.seedErrY (fun τ y => (g τ y, f τ y)) :=
      Finset.sum_congr rfl fun τ _ => by convert rfl
    rw [h1, h2]
    linarith [S.hbad, hη]
  let S' : CondState α β T := ⟨S.μ, S.PX, PY', good', S.bad + 2 * η, hbad'⟩
  refine ⟨S', rfl, rfl, fun _ h => h.1, rfl, hsupp', ?_, ?_, fun τ hτ => (hgood' τ hτ).2⟩
  · have hj (P : T → PMF β) :
        (S.μ.bind fun τ => (S.PX τ).bind fun x => (P τ).map fun y => (τ, (x, y))) =
        S.μ.bind fun τ => ((S.PX τ).bind fun x => (P τ).map fun y => (x, y)).map (τ, ·) := by
      refine congrArg (S.μ.bind ·) (funext fun τ => ?_)
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    change dist (S.μ.bind fun τ => (S.PX τ).bind fun x => (S.PY τ).map fun y => (τ, (x, y)))
        (S.μ.bind fun τ => (S.PX τ).bind fun x => (PY' τ).map fun y => (τ, (x, y))) ≤ η
    rw [hj S.PY, hj PY', dist_bind_pair]
    have hinner (τ : T) :
        dist ((S.PX τ).bind fun x => (S.PY τ).map fun y => (x, y))
          ((S.PX τ).bind fun x => (PY' τ).map fun y => (x, y)) = dist (S.PY τ) (PY' τ) := by
      rw [dist_bind_pair, ← Finset.sum_mul, PMF.sum_toReal, one_mul]
    simp_rw [hinner]
    calc ∑ τ : T, (S.μ τ).toReal * dist (S.PY τ) (PY' τ)
        ≤ S.seedErrY (fun τ y => (g τ y, f τ y)) := by
          refine Finset.sum_le_sum fun τ _ => ?_
          by_cases hG : τ ∈ good'
          · simp only [hG.1, ↓reduceIte]
            exact mul_le_mul_of_nonneg_left (hgood' τ hG).1 ENNReal.toReal_nonneg
          · rw [hbad_eq τ hG, dist_self, mul_zero]
            split_ifs
            · exact mul_nonneg ENNReal.toReal_nonneg dist_nonneg
            · exact le_rfl
      _ ≤ η := hη
  · calc S'.seedErrY g
        ≤ ∑ τ : T, 2 * (if τ ∈ S.good then (S.μ τ).toReal * e τ else 0) := by
          refine Finset.sum_le_sum fun τ _ => ?_
          by_cases hG : τ ∈ good'
          · simp only [S', hG, hG.1, ↓reduceIte]
            have htri := dist_triangle ((PY' τ).map (g τ)) ((S.PY τ).map (g τ))
              (PMF.uniformOfFintype (BitString d1))
            have h1 : dist ((PY' τ).map (g τ)) ((S.PY τ).map (g τ)) ≤ e τ := by
              rw [dist_comm]
              exact (dist_map_le _ _ (g τ)).trans (hgood' τ hG).1
            have h2 := he_fst τ
            nlinarith [ENNReal.toReal_nonneg (a := S.μ τ)]
          · simp only [S', hG, ↓reduceIte]
            split_ifs
            · exact mul_nonneg zero_le_two (mul_nonneg ENNReal.toReal_nonneg dist_nonneg)
            · norm_num
      _ = 2 * S.seedErrY (fun τ y => (g τ y, f τ y)) := (Finset.mul_sum ..).symm
      _ ≤ 2 * η := by linarith

end CondState

/-- Reusable log-cardinality helpers for leakage spaces. -/
private theorem logb_card_fin_bitString (r m : ℕ) :
    Real.logb 2 (Fintype.card (Fin r → BitString m)) = ((r * m : ℕ) : ℝ) := by
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← pow_mul, mul_comm,
    Nat.cast_pow, Nat.cast_ofNat, Real.logb_two_pow]

private theorem logb_card_prod {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    Real.logb 2 (Fintype.card (A × B)) =
      Real.logb 2 (Fintype.card A) + Real.logb 2 (Fintype.card B) := by
  rw [Fintype.card_prod, Nat.cast_mul, Real.logb_mul
    (by exact_mod_cast Fintype.card_ne_zero) (by exact_mod_cast Fintype.card_ne_zero)]

end CondEngine

/-! ### 3. Alternating extraction (`altExt`) -/

section AltExt

/-- **Alternating extraction (`altExt`)**: given `ext1` and `ext2`, sources `x, y`,
and initial seed `s0`, round `k` outputs `(R_k, S_{k+1})` where `S_0 = s0`, `R_k = ext1 x S_k`,
and `S_{k+1} = ext2 y R_k`. -/
@[expose] def altExt {nX nY d1 d2 : ℕ}
    (ext1 : BitString nX → BitString d1 → BitString d2)
    (ext2 : BitString nY → BitString d2 → BitString d1)
    (x : BitString nX) (y : BitString nY) (s0 : BitString d1) :
    ℕ → BitString d2 × BitString d1
  | 0 =>
      let r0 := ext1 x s0
      (r0, ext2 y r0)
  | k + 1 =>
      let prev := altExt ext1 ext2 x y s0 k
      let r := ext1 x prev.2
      (r, ext2 y r)

/-- The `k`-th `X`-extracted string `R_k` in alternating extraction. -/
@[expose] def altExtR {nX nY d1 d2 : ℕ}
    (ext1 : BitString nX → BitString d1 → BitString d2)
    (ext2 : BitString nY → BitString d2 → BitString d1)
    (x : BitString nX) (y : BitString nY) (s0 : BitString d1) (k : ℕ) : BitString d2 :=
  (altExt ext1 ext2 x y s0 k).1

/-- The `k`-th `Y`-side seed `S_k` in alternating extraction (`S₀ = s0`,
`S_{k+1} = ext2 y R_k`). -/
@[expose] def altExtS {nX nY d1 d2 : ℕ}
    (ext1 : BitString nX → BitString d1 → BitString d2)
    (ext2 : BitString nY → BitString d2 → BitString d1)
    (x : BitString nX) (y : BitString nY) (s0 : BitString d1) : ℕ → BitString d1
  | 0 => s0
  | k + 1 => (altExt ext1 ext2 x y s0 k).2

theorem altExtR_eq {nX nY d1 d2 : ℕ}
    (ext1 : BitString nX → BitString d1 → BitString d2)
    (ext2 : BitString nY → BitString d2 → BitString d1)
    (x : BitString nX) (y : BitString nY) (s0 : BitString d1) (k : ℕ) :
    altExtR ext1 ext2 x y s0 k = ext1 x (altExtS ext1 ext2 x y s0 k) := by
  cases k <;> rfl

theorem altExtS_succ {nX nY d1 d2 : ℕ}
    (ext1 : BitString nX → BitString d1 → BitString d2)
    (ext2 : BitString nY → BitString d2 → BitString d1)
    (x : BitString nX) (y : BitString nY) (s0 : BitString d1) (k : ℕ) :
    altExtS ext1 ext2 x y s0 (k + 1) = ext2 y (altExtR ext1 ext2 x y s0 k) := by
  cases k <;> rfl

/-- **Per-round active-source linearity in `X`**: when `ext1` is `𝔽₂`-linear in its source argument,
`altExtR` splits linearly on `x₁ + x₂` at the round's seed `S_k`. In particular, round `k = 0`
satisfies `altExtR (x₁ + x₂) y s0 0 = altExtR x₁ y s0 0 + altExtR x₂ y s0 0`. -/
theorem altExtR_add_source {nX nY d1 d2 : ℕ}
    {ext1 : BitString nX → BitString d1 → BitString d2}
    (ext2 : BitString nY → BitString d2 → BitString d1)
    {k1 ε1 : ℝ} (h1 : IsLinearStrongExtractor ext1 k1 ε1)
    (x₁ x₂ : BitString nX) (y : BitString nY) (s0 : BitString d1) (k : ℕ) :
    altExtR ext1 ext2 (x₁ + x₂) y s0 k =
      ext1 x₁ (altExtS ext1 ext2 (x₁ + x₂) y s0 k) +
      ext1 x₂ (altExtS ext1 ext2 (x₁ + x₂) y s0 k) := by
  rw [altExtR_eq, h1.2]

/-- **Per-round active-source linearity in `Y`**: when `ext2` is `𝔽₂`-linear in its source argument,
`altExtS ... (k + 1)` splits linearly on `y₁ + y₂` at the round's seed `R_k`. -/
theorem altExtS_add_source {nX nY d1 d2 : ℕ}
    (ext1 : BitString nX → BitString d1 → BitString d2)
    {ext2 : BitString nY → BitString d2 → BitString d1}
    {k2 ε2 : ℝ} (h2 : IsLinearStrongExtractor ext2 k2 ε2)
    (x : BitString nX) (y₁ y₂ : BitString nY) (s0 : BitString d1) (k : ℕ) :
    altExtS ext1 ext2 x (y₁ + y₂) s0 (k + 1) =
      ext2 y₁ (altExtR ext1 ext2 x (y₁ + y₂) s0 k) +
      ext2 y₂ (altExtR ext1 ext2 x (y₁ + y₂) s0 k) := by
  rw [altExtS_succ, h2.2]

/-- Generic alternating-extraction look-ahead engine parameterized by shift encodings
(`LShiftX = Unit, LShiftY = Unit` yields two-source `altExt`; `LShiftX = BitString d2,
LShiftY = BitString d1` yields sumset `altExt`). -/
private theorem altExt_round_state {α β LShiftX LShiftY : Type} {nX nY d1 d2 r : ℕ}
    [Finite α] [Finite β] [Fintype LShiftX] [Nonempty LShiftX]
    [Fintype LShiftY] [Nonempty LShiftY]
    {ext1 : BitString nX → BitString d1 → BitString d2}
    {ext2 : BitString nY → BitString d2 → BitString d1}
    {k1 k2 ε1 ε2 kX kY η0 δ : ℝ}
    (hε1 : 0 ≤ ε1) (hε2 : 0 ≤ ε2) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hext1 : IsStrongExtractor ext1 k1 ε1) (hext2 : IsStrongExtractor ext2 k2 ε2)
    (PX₀ : PMF α) (PY₀ : PMF β)
    (projX : α → BitString nX) (projY : β → BitString nY)
    (shXEnc : β → BitString d1 → LShiftX) (shXDec : LShiftX → BitString d2)
    (shYEnc : α → BitString d2 → LShiftY) (shYDec : LShiftY → BitString d1)
    (tR : Fin r → α → BitString d1 → BitString d2)
    (tS : Fin r → β → BitString d2 → BitString d1)
    (s0 : β → BitString d1) (s0' : Fin r → β → BitString d1)
    (hPX₀ : kX ≤ minEntropy (PX₀.map projX))
    (hPY₀ : kY ≤ minEntropy (PY₀.map projY))
    (hη0 : dist (PY₀.map fun y => ((fun j => s0' j y), s0 y))
      ((PY₀.map fun y => fun j => s0' j y).bind fun s' =>
        (PMF.uniformOfFintype (BitString d1)).map (s', ·)) ≤ η0)
    (k : ℕ)
    (hX_ent : k1 ≤ kX - (((k + 1) * r + k) * d2 : ℕ) -
      (k : ℝ) * Real.logb 2 (Fintype.card LShiftY) - (k + 1 : ℕ) * Real.logb 2 δ⁻¹)
    (hY_ent : k2 ≤ kY - (((k + 1) * r + k) * d1 : ℕ) -
      (k : ℝ) * Real.logb 2 (Fintype.card LShiftX) - (k + 1 : ℕ) * Real.logb 2 δ⁻¹) :
    let fR (x : α) (y : β) (s : BitString d1) : BitString d2 :=
      ext1 (projX x) s + shXDec (shXEnc y s)
    let fS (x : α) (y : β) (q : BitString d2) : BitString d1 :=
      ext2 (projY y) q + shYDec (shYEnc x q)
    let recS (x : α) (y : β) : ℕ → BitString d1 := fun i =>
      Nat.rec (s0 y) (fun _ prev => fS x y (fR x y prev)) i
    let recR (x : α) (y : β) (i : ℕ) : BitString d2 := fR x y (recS x y i)
    let recS' (j : Fin r) (x : α) (y : β) : ℕ → BitString d1 := fun i =>
      Nat.rec (s0' j y) (fun _ prev => tS j y (tR j x prev)) i
    let recR' (j : Fin r) (x : α) (y : β) (i : ℕ) : BitString d2 := tR j x (recS' j x y i)
    ∃ (T : Type) (_ : Fintype T) (S : CondState α β T) (obs : α → β → T)
      (curS : T → β → BitString d1)
      (histR : T → Fin k → BitString d2)
      (histR' : T → Fin (k + 1) → Fin r → BitString d2),
      S.joint = CondState.realJoint PX₀ PY₀ obs ∧
      S.bad ≤ (2 * k + 2 : ℕ) * δ ∧
      S.seedErrY curS ≤ η0 + k * (ε1 + ε2) ∧
      (∀ τ ∈ S.good, τ ∈ S.μ.support →
        kX - (((k + 1) * r + k) * d2 : ℕ) -
          (k : ℝ) * Real.logb 2 (Fintype.card LShiftY) - (k + 1 : ℕ) * Real.logb 2 δ⁻¹ ≤
            minEntropy ((S.PX τ).map projX)) ∧
      (∀ τ ∈ S.good, τ ∈ S.μ.support →
        kY - (((k + 1) * r + k) * d1 : ℕ) -
          (k : ℝ) * Real.logb 2 (Fintype.card LShiftX) - (k + 1 : ℕ) * Real.logb 2 δ⁻¹ ≤
            minEntropy ((S.PY τ).map projY)) ∧
      (∀ τ ∈ S.μ.support, ∀ x ∈ (S.PX τ).support, ∀ y ∈ (S.PY τ).support,
        obs x y = τ ∧
        curS τ y = recS x y k ∧
        (∀ i : Fin k, histR τ i = recR x y i.1) ∧
        (∀ i : Fin (k + 1), ∀ j : Fin r, histR' τ i j = recR' j x y i.1)) := by
  classical
  let _ := Fintype.ofFinite α
  let _ := Fintype.ofFinite β
  dsimp only
  let fR (x : α) (y : β) (s : BitString d1) : BitString d2 :=
    ext1 (projX x) s + shXDec (shXEnc y s)
  let fS (x : α) (y : β) (q : BitString d2) : BitString d1 :=
    ext2 (projY y) q + shYDec (shYEnc x q)
  let recS (x : α) (y : β) : ℕ → BitString d1 := fun i =>
    Nat.rec (s0 y) (fun _ prev => fS x y (fR x y prev)) i
  let recR (x : α) (y : β) (i : ℕ) : BitString d2 := fR x y (recS x y i)
  let recS' (j : Fin r) (x : α) (y : β) : ℕ → BitString d1 := fun i =>
    Nat.rec (s0' j y) (fun _ prev => tS j y (tR j x prev)) i
  let recR' (j : Fin r) (x : α) (y : β) (i : ℕ) : BitString d2 := tR j x (recS' j x y i)
  have hlogδ : 0 ≤ Real.logb 2 δ⁻¹ :=
    Real.logb_nonneg one_lt_two ((one_le_inv₀ hδ).mpr hδ1)
  have hlogShX : 0 ≤ Real.logb 2 (Fintype.card LShiftX) :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast Fintype.card_pos)
  have hlogShY : 0 ≤ Real.logb 2 (Fintype.card LShiftY) :=
    Real.logb_nonneg one_lt_two (by exact_mod_cast Fintype.card_pos)
  induction k with
  | zero =>
    let S0 := CondState.init PX₀ PY₀
    let leakY0 : Unit → β → (Fin r → BitString d1) := fun _ y j => s0' j y
    let S1 := S0.condY leakY0 hδ.le
    let leakX0 : (Unit × (Fin r → BitString d1)) → α → (Fin r → BitString d2) :=
      fun ⟨_, s'⟩ x j => tR j x (s' j)
    let S2 := S1.condX leakX0 hδ.le
    let obs : α → β → (Unit × (Fin r → BitString d1)) × (Fin r → BitString d2) :=
      fun x y => (((), fun j => s0' j y), fun j => tR j x (s0' j y))
    refine ⟨_, inferInstance, S2, obs, fun _ y => s0 y, fun _ i => Fin.elim0 i,
      fun ⟨_, r'⟩ _ j => r' j, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [CondState.condX_joint, CondState.condY_joint, CondState.init_joint]
      simp only [CondState.realJoint, PMF.map_bind, PMF.map_comp, Function.comp_def,
        leakY0, leakX0, obs]
    · simp only [S2, S1, S0, CondState.condX, CondState.condY, CondState.swap, CondState.init]
      norm_num; linarith
    · have h12 : S2.seedErrY (fun _ y => s0 y) ≤ S1.seedErrY (fun _ y => s0 y) :=
        CondState.condX_seedErrY_le S1 leakX0 hδ.le (fun _ y => s0 y)
      have hdist_eq :
          dist (PY₀.map fun y => ((fun j => s0' j y), s0 y))
            ((PY₀.map fun y => fun j => s0' j y).bind fun s' =>
              (PMF.uniformOfFintype (BitString d1)).map (s', ·)) =
          ∑ s' : Fin r → BitString d1,
            ((PY₀.map fun y => fun j => s0' j y) s').toReal *
              dist ((conditionalSnd (PY₀.map fun y => (leakY0 () y, y)) s').map s0)
                (PMF.uniformOfFintype (BitString d1)) := by
        let J := PY₀.map fun y => (leakY0 () y, y)
        have hJfst : J.map Prod.fst = PY₀.map fun y => fun j => s0' j y := by
          rw [PMF.map_comp]; rfl
        have hL : (PY₀.map fun y => ((fun j => s0' j y), s0 y)) =
            (J.map Prod.fst).bind fun s' => ((conditionalSnd J s').map s0).map (s', ·) := by
          have h := congrArg (PMF.map fun ⟨s', y⟩ => (s', s0 y)) (bind_conditionalSnd J)
          simp only [J, PMF.map_bind, PMF.map_comp, Function.comp_def, leakY0] at h ⊢
          exact h.symm
        rw [hL, hJfst]
        exact dist_bind_pair _ _ _
      refine h12.trans (le_trans ?_ (le_trans hη0 (by simp)))
      simp only [CondState.seedErrY, S1, S0, CondState.condY, CondState.init]
      rw [Fintype.sum_prod_type, Fintype.sum_unique]
      refine (Finset.sum_le_sum fun s' _ => ?_).trans_eq hdist_eq.symm
      have hμeq : ((PMF.pure ()).bind fun τ =>
          (((PY₀.map fun y => (leakY0 τ y, y)).map Prod.fst).map (τ, ·))) (default, s') =
          (PY₀.map fun y => fun j => s0' j y) s' := by
        simp only [PMF.pure_bind, PMF.map_comp, Function.comp_def, PMF.map_apply, leakY0]
        exact tsum_congr fun y => by simp [Subsingleton.elim default ()]
      split_ifs
      · rw [hμeq]
      · exact mul_nonneg ENNReal.toReal_nonneg dist_nonneg
    · intro p hpG hpS
      have h := CondState.condX_minEntropy_X S1 leakX0 hδ projX (fun _ _ _ => hPX₀) hpG hpS
      rw [logb_card_fin_bitString] at h
      simpa using h
    · intro p hpG hpS
      have h := CondState.condX_minEntropy_Y S1 leakX0 hδ.le projY
        (fun τ hτG hτS => CondState.condY_minEntropy_Y S0 leakY0 hδ projY
          (fun _ _ _ => hPY₀) hτG hτS) hpG hpS
      rw [logb_card_fin_bitString] at h
      simpa using h
    · intro ⟨⟨⟨⟩, a⟩, b⟩ hp x hx y hy
      obtain ⟨h1, hx1, hy1, hle1⟩ := CondState.condX_support S1 leakX0 hδ.le hp hx hy
      obtain ⟨-, -, -, hle2⟩ := CondState.condY_support S0 leakY0 hδ.le h1 hx1 hy1
      have ha : a = fun j => s0' j y := hle2.symm
      have hb : b = fun j => tR j x (s0' j y) := by
        rw [← hle1]; simp only [leakX0, ha]
      refine ⟨Prod.ext (Prod.ext rfl ha.symm) hb.symm, rfl, fun i => Fin.elim0 i, fun i j => ?_⟩
      have hi0 : i.1 = 0 := by omega
      simp only [hb]
      rw [hi0]
      rfl
  | succ k ih =>
    have hent_prev {k0 kSrc : ℝ} {d : ℕ} {c : ℝ} (hc : 0 ≤ c)
        (h : k0 ≤ kSrc - (((k + 1 + 1) * r + (k + 1)) * d : ℕ) -
          ((k + 1 : ℕ) : ℝ) * c - (k + 1 + 1 : ℕ) * Real.logb 2 δ⁻¹) :
        k0 ≤ kSrc - (((k + 1) * r + k) * d : ℕ) -
          (k : ℝ) * c - (k + 1 : ℕ) * Real.logb 2 δ⁻¹ := by
      have hnat : ((k + 1) * r + k) * d ≤ ((k + 1 + 1) * r + (k + 1)) * d :=
        Nat.mul_le_mul_right d (by nlinarith)
      have hcast : ((((k + 1) * r + k) * d : ℕ) : ℝ) ≤ (((k + 1 + 1) * r + (k + 1)) * d : ℕ) :=
        Nat.cast_le.mpr hnat
      push_cast at h hcast ⊢
      nlinarith
    have hX_prev := hent_prev hlogShY hX_ent
    have hY_prev := hent_prev hlogShX hY_ent
    obtain ⟨T, hFT, S, obs, curS, histR, histR', hJ, hbad, herr, hminX, hminY, hsupp⟩ :=
      ih hX_prev hY_prev
    -- Half-step 1: extract `R_k = ext1 (projX x) (curS τ y) + shiftX`,
    -- reveal `(S_k, shX, S'_{k+1})`.
    let LY := (BitString d1 × LShiftX) × (Fin r → BitString d1)
    let leakY : T → β → LY := fun τ y =>
      ((curS τ y, shXEnc y (curS τ y)), fun j => tS j y (histR' τ (Fin.last k) j))
    let S1 := S.condY leakY hδ.le
    let curR : T × LY → α → BitString d2 := fun ⟨_, ⟨⟨s, sh⟩, _⟩⟩ x =>
      ext1 (projX x) s + shXDec sh
    have hS1_err : S1.seedErrX curR ≤ S.seedErrY curS + ε1 := by
      have h := CondState.extractX_condY_seedErrX_le S projX hε1 hδ.le hext1
        (fun τ hG hS => hX_prev.trans (hminX τ hG hS)) leakY
        (fun ⟨_, ⟨⟨s, _⟩, _⟩⟩ => s) (fun ⟨_, ⟨⟨_, sh⟩, _⟩⟩ => shXDec sh)
      exact h
    have hlogLY : Real.logb 2 (Fintype.card LY) =
        (((r + 1) * d1 : ℕ) : ℝ) + Real.logb 2 (Fintype.card LShiftX) := by
      dsimp only [LY]
      rw [logb_card_prod, logb_card_prod, BitString.logb_card, logb_card_fin_bitString]
      push_cast; ring
    have hS1_minY : ∀ τ1 ∈ S1.good, τ1 ∈ S1.μ.support →
        kY - (((k + 1 + 1) * r + (k + 1)) * d1 : ℕ) -
          ((k + 1 : ℕ) : ℝ) * Real.logb 2 (Fintype.card LShiftX) -
          (k + 1 + 1 : ℕ) * Real.logb 2 δ⁻¹ ≤ minEntropy ((S1.PY τ1).map projY) := by
      intro τ1 hG hS
      have h := CondState.condY_minEntropy_Y S leakY hδ projY hminY hG hS
      rw [hlogLY] at h
      have hmul : ((k + 1 + 1) * r + (k + 1)) * d1 = ((k + 1) * r + k) * d1 + (r + 1) * d1 := by
        ring
      rw [hmul]; push_cast at h ⊢; linarith
    -- Half-step 2: extract `S_{k+1} = ext2 (projY y) (curR τ1 x) + shiftY`,
    -- reveal `(R_k, shY, R'_{k+1})`.
    let LX := (BitString d2 × LShiftY) × (Fin r → BitString d2)
    let leakX : T × LY → α → LX := fun ⟨τ, ⟨⟨s, sh⟩, s'⟩⟩ x =>
      let q := curR (τ, ((s, sh), s')) x
      ((q, shYEnc x q), fun j => tR j x (s' j))
    let S2 := S1.condX leakX hδ.le
    let curS_next : (T × LY) × LX → β → BitString d1 := fun ⟨_, ⟨⟨q, sh⟩, _⟩⟩ y =>
      ext2 (projY y) q + shYDec sh
    have hS2_err : S2.seedErrY curS_next ≤ S1.seedErrX curR + ε2 :=
      CondState.extractY_condX_seedErrY_le S1 projY hε2 hδ.le hext2
        (fun τ1 hG hS => hY_ent.trans (hS1_minY τ1 hG hS)) leakX
        (fun ⟨_, ⟨⟨q, _⟩, _⟩⟩ => q) (fun ⟨_, ⟨⟨_, sh⟩, _⟩⟩ => shYDec sh)
    have hlogLX : Real.logb 2 (Fintype.card LX) =
        (((r + 1) * d2 : ℕ) : ℝ) + Real.logb 2 (Fintype.card LShiftY) := by
      dsimp only [LX]
      rw [logb_card_prod, logb_card_prod, BitString.logb_card, logb_card_fin_bitString]
      push_cast; ring
    let obs2 : α → β → (T × LY) × LX := fun x y =>
      let τ := obs x y
      let ly := leakY τ y
      ((τ, ly), leakX (τ, ly) x)
    let histR_next : (T × LY) × LX → Fin (k + 1) → BitString d2 := fun ⟨⟨τ, _⟩, ⟨⟨q, _⟩, _⟩⟩ i =>
      Fin.lastCases q (histR τ) i
    let histR'_next : (T × LY) × LX → Fin (k + 2) → Fin r → BitString d2 :=
      fun ⟨⟨τ, _⟩, ⟨_, r'⟩⟩ i j => Fin.lastCases (r' j) (fun m => histR' τ m j) i
    refine ⟨_, inferInstance, S2, obs2, curS_next, histR_next, histR'_next,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [CondState.condX_joint, CondState.condY_joint, hJ]
      simp only [CondState.realJoint, PMF.map_bind, PMF.map_comp, Function.comp_def, obs2]
    · have hb2 : S2.bad = S.bad + δ + δ := rfl
      rw [hb2]; push_cast at hbad ⊢; linarith
    · push_cast; linarith
    · intro τ2 hG hS
      have h1 := CondState.condX_minEntropy_X S1 leakX hδ projX
        (fun τ1 hG1 hS1 => CondState.condY_minEntropy_X S leakY hδ.le projX hminX hG1 hS1) hG hS
      rw [hlogLX] at h1
      have hmul : ((k + 1 + 1) * r + (k + 1)) * d2 = ((k + 1) * r + k) * d2 + (r + 1) * d2 := by
        ring
      rw [hmul]; push_cast at h1 ⊢; linarith
    · intro τ2 hG hS
      exact CondState.condX_minEntropy_Y S1 leakX hδ.le projY hS1_minY hG hS
    · intro ⟨⟨τ, ⟨⟨s, shX⟩, s'⟩⟩, ⟨⟨q, shY⟩, r'⟩⟩ hp x hx y hy
      obtain ⟨h1, hx1, hy1, hleX⟩ := CondState.condX_support S1 leakX hδ.le hp hx hy
      obtain ⟨h0, hx0, hy0, hleY⟩ := CondState.condY_support S leakY hδ.le h1 hx1 hy1
      obtain ⟨hobs, hcurS, hhistR, hhistR'⟩ := hsupp τ h0 x hx0 y hy0
      have hobs2 : obs2 x y = ((τ, ((s, shX), s')), ((q, shY), r')) := by
        dsimp only [obs2]
        rw [hobs, hleY, hleX]
      have hs : s = recS x y k := by
        have h := congrArg (fun p : LY => p.1.1) hleY
        exact h.symm.trans hcurS
      have hshX : shX = shXEnc y (recS x y k) := by
        have h := congrArg (fun p : LY => p.1.2) hleY
        change shXEnc y (curS τ y) = shX at h
        rw [← h, hcurS]
      have hs' (j : Fin r) : s' j = recS' j x y (k + 1) := by
        have h := congrFun (congrArg Prod.snd hleY) j
        have hlast := hhistR' (Fin.last k) j
        change tS j y (histR' τ (Fin.last k) j) = s' j at h
        rw [← h, hlast]
        rfl
      have hq : q = recR x y k := by
        have h := congrArg (fun p : LX => p.1.1) hleX
        change ext1 (projX x) s + shXDec shX = q at h
        rw [← h, hs, hshX]
      have hshY : shY = shYEnc x (recR x y k) := by
        have h := congrArg (fun p : LX => p.1.2) hleX
        change shYEnc x (ext1 (projX x) s + shXDec shX) = shY at h
        rw [← h, hs, hshX]
      have hr' (j : Fin r) : r' j = recR' j x y (k + 1) := by
        have h := congrFun (congrArg Prod.snd hleX) j
        change tR j x (s' j) = r' j at h
        rw [← h, hs' j]
      refine ⟨hobs2, ?_, ?_, ?_⟩
      · simp only [curS_next, hq, hshY]
        rfl
      · intro i
        refine Fin.lastCases ?_ (fun m => ?_) i
        · simp only [histR_next, Fin.lastCases_last, hq, Fin.val_last]; rfl
        · simp only [histR_next, Fin.lastCases_castSucc, hhistR m, Fin.val_castSucc]
      · intro i j
        refine Fin.lastCases ?_ (fun m => ?_) i
        · simp only [histR'_next, Fin.lastCases_last, hr' j, Fin.val_last]; rfl
        · simp only [histR'_next, Fin.lastCases_castSucc, hhistR' m j, Fin.val_castSucc]

/-- **Two-source alternating-extraction look-ahead theorem**:
for independent `PX` (with `(X, X')` where `X` has min-entropy `≥ kX`) and `PY` (with `(Y, Y',
S₀, S'₀)` where `Y` has min-entropy `≥ kY` and `S₀` is `η₀`-close to uniform jointly with `S'₀`),
the `k`-th output `R_k = altExtR ext1 ext2 X Y S₀ k` is within
`η₀ + (k + 1) * ε₁ + k * ε₂ + (2 * k + 2) * δ` of an independent uniform string jointly with
`((Y, Y', S₀, S'₀), (R_0, …, R_{k-1}), (R'_0, …, R'_k))` (which deterministically fixes
`(S_0, …, S_k)` and `(S'_0, …, S'_k)` as well). -/
theorem dist_altExt_lookAhead_le {nX nY d1 d2 r : ℕ}
    {ext1 : BitString nX → BitString d1 → BitString d2}
    {ext2 : BitString nY → BitString d2 → BitString d1}
    {k1 k2 ε1 ε2 kX kY η0 δ : ℝ}
    (hε1 : 0 ≤ ε1) (hε2 : 0 ≤ ε2) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hext1 : IsStrongExtractor ext1 k1 ε1) (hext2 : IsStrongExtractor ext2 k2 ε2)
    (PX : PMF (BitString nX × (Fin r → BitString nX)))
    (PY : PMF ((BitString nY × (Fin r → BitString nY)) × (BitString d1 × (Fin r → BitString d1))))
    (hPX : kX ≤ minEntropy (PX.map Prod.fst))
    (hPY : kY ≤ minEntropy (PY.map fun ⟨⟨y, _⟩, _⟩ => y))
    (hη0 : dist (PY.map fun ⟨_, ⟨s0, s0'⟩⟩ => (s0', s0))
      ((PY.map fun ⟨_, ⟨_, s0'⟩⟩ => s0').bind fun s' =>
        (PMF.uniformOfFintype (BitString d1)).map (s', ·)) ≤ η0)
    (k : ℕ)
    (hX_ent : k1 ≤ kX - (((k + 1) * r + k) * d2 : ℕ) - (k + 1 : ℕ) * Real.logb 2 δ⁻¹)
    (hY_ent : k2 ≤ kY - (((k + 1) * r + k) * d1 : ℕ) - (k + 1 : ℕ) * Real.logb 2 δ⁻¹) :
    let view
        (px : BitString nX × (Fin r → BitString nX))
        (py : (BitString nY × (Fin r → BitString nY)) × (BitString d1 × (Fin r → BitString d1))) :=
      let (x, x') := px
      let ((y, y'), (s0, s0')) := py
      (py, (fun i : Fin k => altExtR ext1 ext2 x y s0 i.1,
            fun i : Fin (k + 1) => fun j : Fin r =>
              altExtR ext1 ext2 (x' j) (y' j) (s0' j) i.1))
    dist
      (PX.bind fun px =>
        let (x, _) := px
        PY.map fun py =>
          let ((y, _), (s0, _)) := py
          (view px py, altExtR ext1 ext2 x y s0 k))
      ((PX.bind fun px => PY.map fun py => view px py).bind fun v =>
        (PMF.uniformOfFintype (BitString d2)).map fun u => (v, u)) ≤
      η0 + (k + 1 : ℕ) * ε1 + k * ε2 + (2 * k + 2 : ℕ) * δ := by
  classical
  have hlogU : Real.logb 2 (Fintype.card Unit) = 0 := by simp
  obtain ⟨T, hFT, S, obs, curS, histR, histR', hJ, hbad, herr, hminX, -, hsupp⟩ :=
    altExt_round_state (LShiftX := Unit) (LShiftY := Unit)
      hε1 hε2 hδ hδ1 hext1 hext2 PX PY Prod.fst (fun ⟨⟨y, _⟩, _⟩ => y)
      (fun _ _ => ()) (fun _ => 0) (fun _ _ => ()) (fun _ => 0)
      (fun j ⟨_, x'⟩ s => ext1 (x' j) s) (fun j ⟨⟨_, y'⟩, _⟩ q => ext2 (y' j) q)
      (fun ⟨_, ⟨s0, _⟩⟩ => s0) (fun j ⟨_, ⟨_, s0'⟩⟩ => s0' j)
      hPX hPY hη0 k (by simpa [hlogU] using hX_ent) (by simpa [hlogU] using hY_ent)
  have hrecS_eq (x : BitString nX) (y : BitString nY) (s : BitString d1) (i : ℕ) :
      Nat.rec s (fun _ prev => ext2 y (ext1 x prev + 0) + 0) i = altExtS ext1 ext2 x y s i := by
    induction i with
    | zero => rfl
    | succ i ih =>
      dsimp only
      rw [add_zero, add_zero, ih, altExtS_succ, altExtR_eq]
  have hrecS'_eq (x : BitString nX) (y : BitString nY) (s : BitString d1) (i : ℕ) :
      Nat.rec s (fun _ prev => ext2 y (ext1 x prev)) i = altExtS ext1 ext2 x y s i := by
    induction i with
    | zero => rfl
    | succ i ih =>
      dsimp only
      rw [ih, altExtS_succ, altExtR_eq]
  have hX_ent' : k1 ≤ kX - (((k + 1) * r + k) * d2 : ℕ) - (k + 1 : ℕ) * Real.logb 2 δ⁻¹ :=
    hX_ent
  have hstep := CondState.extractX_dist_le S Prod.fst hε1 hext1
    (fun τ hG hS => le_trans (by simpa [hlogU] using hX_ent') (hminX τ hG hS))
    curS (fun _ _ => 0) (fun τ y => (y, (histR τ, histR' τ)))
  have hL :
      (S.joint.map fun ⟨τ, x, y⟩ => ((y, (histR τ, histR' τ)), ext1 x.1 (curS τ y) + 0)) =
      PX.bind fun px =>
        let (x, x') := px
        PY.map fun py =>
          let ((y, y'), (s0, s0')) := py
          ((py,
            (fun i : Fin k => altExtR ext1 ext2 x y s0 i.1,
             fun i : Fin (k + 1) => fun j : Fin r =>
               altExtR ext1 ext2 (x' j) (y' j) (s0' j) i.1)),
           altExtR ext1 ext2 x y s0 k) := by
    have hcongr :
        (S.joint.map fun ⟨τ, x, y⟩ => ((y, (histR τ, histR' τ)), ext1 x.1 (curS τ y) + 0)) =
        S.joint.map fun ⟨_, ⟨x1, x2⟩, ⟨⟨y1, y2⟩, ⟨s0, s0'⟩⟩⟩ =>
          ((((y1, y2), (s0, s0')),
            (fun i : Fin k => altExtR ext1 ext2 x1 y1 s0 i.1,
             fun i : Fin (k + 1) => fun j : Fin r =>
               altExtR ext1 ext2 (x2 j) (y2 j) (s0' j) i.1)),
           altExtR ext1 ext2 x1 y1 s0 k) := by
      simp only [PMF.map]
      refine PMF.bind_congr_on_support S.joint _ _
        fun ⟨τ, ⟨x1, x2⟩, ⟨⟨y1, y2⟩, ⟨s0, s0'⟩⟩⟩ hmem => ?_
      have hmem' := CondState.support_of_mem_joint S hmem
      obtain ⟨-, hcurS, hhistR, hhistR'⟩ :=
        hsupp τ hmem'.1 (x1, x2) hmem'.2.1 ((y1, y2), (s0, s0')) hmem'.2.2
      refine congrArg PMF.pure (Prod.ext (Prod.ext rfl (Prod.ext (funext fun i => ?_)
        (funext fun i => funext fun j => ?_))) ?_)
      · dsimp only; rw [hhistR i]; dsimp only; rw [add_zero, hrecS_eq, altExtR_eq]
      · dsimp only; rw [hhistR' i j]; dsimp only; rw [hrecS'_eq, altExtR_eq]
      · dsimp only; rw [hcurS]; dsimp only; rw [add_zero, hrecS_eq, altExtR_eq]
    rw [hcongr, hJ]
    simp only [CondState.realJoint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hR :
      ((S.joint.map fun ⟨τ, _, y⟩ => (y, (histR τ, histR' τ))).bind fun o =>
        (PMF.uniformOfFintype (BitString d2)).map fun u => (o, u)) =
      ((PX.bind fun px =>
        let (x, x') := px
        PY.map fun py =>
          let ((y, y'), (s0, s0')) := py
          (py, (fun i : Fin k => altExtR ext1 ext2 x y s0 i.1,
                fun i : Fin (k + 1) => fun j : Fin r =>
                  altExtR ext1 ext2 (x' j) (y' j) (s0' j) i.1))).bind fun v =>
        (PMF.uniformOfFintype (BitString d2)).map fun u => (v, u)) := by
    congr 1
    have hfst := congrArg (PMF.map Prod.fst) hL
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at hfst
    exact hfst.trans (congrArg (PX.bind ·) (funext fun ⟨x, x'⟩ =>
      congrArg (PY.map ·) (funext fun ⟨⟨y, y'⟩, ⟨s0, s0'⟩⟩ => rfl)))
  rw [hL, hR] at hstep
  refine hstep.trans ?_
  push_cast at hbad herr ⊢
  linarith

/-- **Sumset alternating-extraction look-ahead theorem**:
when `ext1` and `ext2` are `𝔽₂`-linear strong extractors (`IsLinearStrongExtractor`), running
`altExt ext1 ext2 (a + b) (a + b) s0` on a sumset `A + B` (where `A` is independent of `(B, s0)`)
preserves look-ahead uniformity: `R_k` is within `η₀ + (k + 1) * ε₁ + k * ε₂ + (2 * k + 2) * δ`
of uniform jointly with `(B, s0, R_0..R_{k-1})`. -/
theorem dist_altExt_sumset_lookAhead_le {n d1 d2 : ℕ}
    {ext1 : BitString n → BitString d1 → BitString d2}
    {ext2 : BitString n → BitString d2 → BitString d1}
    {k1 k2 ε1 ε2 kA kB η0 δ : ℝ}
    (hε1 : 0 ≤ ε1) (hε2 : 0 ≤ ε2) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hext1 : IsLinearStrongExtractor ext1 k1 ε1) (hext2 : IsLinearStrongExtractor ext2 k2 ε2)
    (A : PMF (BitString n)) (JB : PMF (BitString n × BitString d1))
    (hA : kA ≤ minEntropy A) (hB : kB ≤ minEntropy (JB.map Prod.fst))
    (hη0 : dist (JB.map Prod.snd) (PMF.uniformOfFintype (BitString d1)) ≤ η0)
    (k : ℕ)
    (hA_ent : k1 ≤ kA - (k * d2 : ℕ) - (k * d1 : ℕ) - (k + 1 : ℕ) * Real.logb 2 δ⁻¹)
    (hB_ent : k2 ≤ kB - (k * d1 : ℕ) - (k * d2 : ℕ) - (k + 1 : ℕ) * Real.logb 2 δ⁻¹) :
    let view (a : BitString n) (bs : BitString n × BitString d1) :=
      (bs, fun i : Fin k => altExtR ext1 ext2 (a + bs.1) (a + bs.1) bs.2 i.1)
    dist
      (A.bind fun a => JB.map fun bs =>
        (view a bs, altExtR ext1 ext2 (a + bs.1) (a + bs.1) bs.2 k))
      ((A.bind fun a => JB.map fun bs => view a bs).bind fun v =>
        (PMF.uniformOfFintype (BitString d2)).map fun u => (v, u)) ≤
      η0 + (k + 1 : ℕ) * ε1 + k * ε2 + (2 * k + 2 : ℕ) * δ := by
  classical
  have hη0' : dist (JB.map fun bs => ((fun j => Fin.elim0 j), bs.2))
      ((JB.map fun _ => (fun j => (Fin.elim0 : Fin 0 → BitString d1) j)).bind fun s' =>
        (PMF.uniformOfFintype (BitString d1)).map (s', ·)) ≤ η0 := by
    let e : BitString d1 ≃ (Fin 0 → BitString d1) × BitString d1 :=
      { toFun := fun s => (Fin.elim0, s)
        invFun := Prod.snd
        left_inv := fun _ => rfl
        right_inv := fun ⟨f, s⟩ => Prod.ext (funext fun j => Fin.elim0 j) rfl }
    have hL : (JB.map fun bs => ((fun j => Fin.elim0 j), bs.2)) = (JB.map Prod.snd).map e := by
      rw [PMF.map_comp]; rfl
    have hR : ((JB.map fun _ => (fun j => (Fin.elim0 : Fin 0 → BitString d1) j)).bind fun s' =>
          (PMF.uniformOfFintype (BitString d1)).map (s', ·)) =
        (PMF.uniformOfFintype (BitString d1)).map e := by
      have hconst : (JB.map (Function.const _ (fun j => (Fin.elim0 : Fin 0 → BitString d1) j))) =
          PMF.pure Fin.elim0 := PMF.map_const ..
      change ((JB.map (Function.const _ (fun j => (Fin.elim0 : Fin 0 → BitString d1) j))).bind
          fun s' => (PMF.uniformOfFintype (BitString d1)).map (s', ·)) = _
      rw [hconst, PMF.pure_bind]; rfl
    rw [hL, hR]
    exact (dist_map_le _ _ e).trans hη0
  have hA' : k1 ≤ kA - (((k + 1) * 0 + k) * d2 : ℕ) -
      (k : ℝ) * Real.logb 2 (Fintype.card (BitString d1)) - (k + 1 : ℕ) * Real.logb 2 δ⁻¹ := by
    rw [BitString.logb_card]; push_cast at hA_ent ⊢; linarith
  have hB' : k2 ≤ kB - (((k + 1) * 0 + k) * d1 : ℕ) -
      (k : ℝ) * Real.logb 2 (Fintype.card (BitString d2)) - (k + 1 : ℕ) * Real.logb 2 δ⁻¹ := by
    rw [BitString.logb_card]; push_cast at hB_ent ⊢; linarith
  obtain ⟨T, hFT, S, obs, curS, histR, _, hJ, hbad, herr, hminX, _, hsupp⟩ :=
    altExt_round_state (LShiftX := BitString d2) (LShiftY := BitString d1) (r := 0)
      hε1 hε2 hδ hδ1 hext1.1 hext2.1 A JB id Prod.fst
      (fun bs s => ext1 bs.1 s) id (fun a q => ext2 a q) id
      (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) Prod.snd (fun j _ => Fin.elim0 j)
      (by rwa [PMF.map_id]) hB hη0' k hA' hB'
  have hrecS_eq (a b : BitString n) (s : BitString d1) (i : ℕ) :
      Nat.rec s (fun _ prev => ext2 b (ext1 a prev + ext1 b prev) +
        ext2 a (ext1 a prev + ext1 b prev)) i =
      altExtS ext1 ext2 (a + b) (a + b) s i := by
    induction i with
    | zero => rfl
    | succ i ih =>
      simp only [ih]
      rw [altExtS_succ, altExtR_eq, hext1.2, hext2.2, add_comm (ext2 b _)]
  have hstep := CondState.extractX_dist_le S id hε1 hext1.1
    (fun τ hG hS => hA'.trans (hminX τ hG hS))
    curS (fun τ bs => ext1 bs.1 (curS τ bs)) (fun τ bs => (bs, histR τ))
  change dist
      (S.joint.map fun ⟨τ, a, bs⟩ => ((bs, histR τ), ext1 a (curS τ bs) + ext1 bs.1 (curS τ bs)))
      ((S.joint.map fun ⟨τ, _, bs⟩ => (bs, histR τ)).bind fun o =>
        (PMF.uniformOfFintype (BitString d2)).map fun u => (o, u)) ≤
      S.bad + S.seedErrY curS + ε1 at hstep
  have hL :
      (S.joint.map fun ⟨τ, a, bs⟩ => ((bs, histR τ), ext1 a (curS τ bs) + ext1 bs.1 (curS τ bs))) =
      A.bind fun a => JB.map fun bs =>
        ((bs, fun i : Fin k => altExtR ext1 ext2 (a + bs.1) (a + bs.1) bs.2 i.1),
         altExtR ext1 ext2 (a + bs.1) (a + bs.1) bs.2 k) := by
    have hcongr :
        (S.joint.map fun ⟨τ, a, bs⟩ =>
          ((bs, histR τ), ext1 a (curS τ bs) + ext1 bs.1 (curS τ bs))) =
        S.joint.map fun ⟨_, a, bs⟩ =>
          ((bs, fun i : Fin k => altExtR ext1 ext2 (a + bs.1) (a + bs.1) bs.2 i.1),
           altExtR ext1 ext2 (a + bs.1) (a + bs.1) bs.2 k) := by
      simp only [PMF.map]
      refine PMF.bind_congr_on_support S.joint _ _ fun ⟨τ, a, bs⟩ hmem => ?_
      have hmem' := CondState.support_of_mem_joint S hmem
      obtain ⟨-, hcurS, hhistR, -⟩ := hsupp τ hmem'.1 a hmem'.2.1 bs hmem'.2.2
      refine congrArg PMF.pure (Prod.ext (Prod.ext rfl (funext fun i => ?_)) ?_)
      · dsimp only; rw [hhistR i]; dsimp only [id]; rw [hrecS_eq, ← hext1.2, altExtR_eq]
      · dsimp only; rw [hcurS]; dsimp only [id]; rw [hrecS_eq, ← hext1.2, altExtR_eq]
    rw [hcongr, hJ]
    simp only [CondState.realJoint, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hR :
      ((S.joint.map fun ⟨τ, _, bs⟩ => (bs, histR τ)).bind fun o =>
        (PMF.uniformOfFintype (BitString d2)).map fun u => (o, u)) =
      ((A.bind fun a => JB.map fun bs =>
          (bs, fun i : Fin k => altExtR ext1 ext2 (a + bs.1) (a + bs.1) bs.2 i.1)).bind fun v =>
        (PMF.uniformOfFintype (BitString d2)).map fun u => (v, u)) := by
    congr 1
    have hfst := congrArg (PMF.map Prod.fst) hL
    simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using hfst
  rw [hL, hR] at hstep
  refine hstep.trans ?_
  push_cast at hbad herr ⊢
  linarith

end AltExt

/-! ### 4. Polynomial `𝔽₂`-linear weak-seed correlation breaker (`vanderCB`) -/

section VanderCB

/-- **Polynomial (`BinaryField ℓ`) evaluation correlation breaker**:
partitions `b : BitString ((t + 1) * ℓ)` into `t + 1` coefficients over `BinaryField ℓ`, evaluates
the resulting degree-`≤ t` polynomial at `α : BitString ℓ` (viewed in `BinaryField ℓ`), and takes
the inner product with `y : BitString ℓ`. -/
noncomputable def vanderCB (t ℓ : ℕ) (hℓ : ℓ ≠ 0)
    (b : BitString ((t + 1) * ℓ)) (y : BitString ℓ) (α : BitString ℓ) : Bool :=
  let a := (BinaryField.equivBits hℓ).symm α
  let val : BinaryField ℓ :=
    ∑ i : Fin (t + 1), (BinaryField.equivBits hℓ).symm (BitString.block b i) * a ^ i.1
  BinaryField.equivBits hℓ val ⬝ᵥ y

/-- **Unconditional polynomial `IsLinearWeakSeedCB` over `2 ^ ℓ` advice strings**:
for `ℓ ≠ 0`, `t + 1 ≤ 2 ^ ℓ`, and `δ > 0`, `vanderCB t ℓ hℓ` is an `𝔽₂`-linear weak-seed
`t`-correlation breaker over `Advice = BitString ℓ` using only `(t + 1) * ℓ` source bits (compared
to `2 ^ ℓ * ℓ` bits for `blockDotCB`). -/
theorem isLinearWeakSeedCB_vander {t ℓ : ℕ} (hℓ : ℓ ≠ 0) (ht : t + 1 ≤ 2 ^ ℓ)
    {kSrc kSeed δ : ℝ} (hδ : 0 < δ) :
    IsLinearWeakSeedCB (vanderCB t ℓ hℓ) kSrc kSeed t
      (δ + 2 ^ (((((t + 1) * ℓ : ℕ) : ℝ) - kSrc - kSeed + Real.logb 2 δ⁻¹) / 2) / 2) := by
  classical
  let evalB (b : BitString ((t + 1) * ℓ)) (a : BinaryField ℓ) : BinaryField ℓ :=
    ∑ i : Fin (t + 1), (BinaryField.equivBits hℓ).symm (BitString.block b i) * a ^ i.1
  refine ⟨fun y α b₁ b₂ => ?_, ?_⟩
  · unfold vanderCB
    have hadd : evalB (b₁ + b₂) ((BinaryField.equivBits hℓ).symm α) =
        evalB b₁ ((BinaryField.equivBits hℓ).symm α) +
        evalB b₂ ((BinaryField.equivBits hℓ).symm α) := by
      simp only [evalB, ← Finset.sum_add_distrib, ← add_mul, ← map_add]
      rfl
    change BinaryField.equivBits hℓ (evalB (b₁ + b₂) ((BinaryField.equivBits hℓ).symm α)) ⬝ᵥ y =
      BinaryField.equivBits hℓ (evalB b₁ ((BinaryField.equivBits hℓ).symm α)) ⬝ᵥ y +
      BinaryField.equivBits hℓ (evalB b₂ ((BinaryField.equivBits hℓ).symm α)) ⬝ᵥ y
    rw [hadd, map_add, add_dotProduct]
  intro r hr α α' hα' B J hB hJ
  let a₀ : BinaryField ℓ := (BinaryField.equivBits hℓ).symm α
  let a' : Fin r → BinaryField ℓ := fun j => (BinaryField.equivBits hℓ).symm (α' j)
  have ha'_ne : ∀ j, a' j ≠ a₀ := fun j h =>
    hα' j ((BinaryField.equivBits hℓ).symm.injective h)
  let S₀ : Finset (BinaryField ℓ) := Finset.univ.image a'
  let U : Finset (BinaryField ℓ) := Finset.univ.erase a₀
  have hS₀_sub : S₀ ⊆ U := fun x hx => by
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_erase.mpr ⟨ha'_ne j, Finset.mem_univ _⟩
  have hS₀_card : S₀.card ≤ t := (Finset.card_image_le.trans (by simp)).trans hr
  have hU_card : t ≤ U.card := by
    have hcard : Fintype.card (BinaryField ℓ) = 2 ^ ℓ := BinaryField.card hℓ
    have hU : U.card = Fintype.card (BinaryField ℓ) - 1 := by simp [U, Finset.card_erase_of_mem]
    omega
  have hdiff_card : t - S₀.card ≤ (U \ S₀).card := by
    rw [Finset.card_sdiff_of_subset hS₀_sub]; omega
  obtain ⟨extra, hextra_sub, hextra_card⟩ := Finset.exists_subset_card_eq hdiff_card
  let pts : Finset (BinaryField ℓ) := S₀ ∪ extra
  have hpts_card : pts.card = t := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_sdiff.mono_right hextra_sub), hextra_card]
    omega
  have ha₀_notMem : a₀ ∉ pts := fun hm => by
    rcases Finset.mem_union.mp hm with h | h
    · exact (Finset.mem_erase.mp (hS₀_sub h)).1 rfl
    · exact (Finset.mem_erase.mp (Finset.mem_sdiff.mp (hextra_sub h)).1).1 rfl
  have ha'_mem (j : Fin r) : a' j ∈ pts :=
    Finset.mem_union_left _ (Finset.mem_image_of_mem a' (Finset.mem_univ j))
  let Leak := pts → BinaryField ℓ
  let leak : BitString ((t + 1) * ℓ) → Leak := fun b p => evalB b p.1
  let JB : PMF (Leak × BitString ((t + 1) * ℓ)) := B.map fun b => (leak b, b)
  let μ : PMF Leak := JB.map Prod.fst
  have hlog_leak : Real.logb 2 (Fintype.card Leak) = (t * ℓ : ℕ) := by
    have hc : Fintype.card Leak = 2 ^ (t * ℓ) := by
      simp only [Leak, Fintype.card_fun, Fintype.card_coe, BinaryField.card hℓ, hpts_card,
        ← pow_mul, mul_comm]
    rw [hc, Nat.cast_pow, Nat.cast_ofNat, Real.logb_two_pow]
  have hrec : μ.bind (conditionalSnd JB) = B := bind_conditionalSnd_of_map B leak
  let P (rest : Leak) : PMF (Bool × (Fin r → Bool)) :=
    (conditionalSnd JB rest).bind fun b =>
      J.map fun ⟨y, y'⟩ => (vanderCB t ℓ hℓ b y α, fun j => vanderCB t ℓ hℓ b (y' j) (α' j))
  let Q (rest : Leak) : PMF (Bool × (Fin r → Bool)) :=
    (PMF.uniformOfFintype Bool).bind fun u =>
      (conditionalSnd JB rest).bind fun b =>
        J.map fun ⟨_, y'⟩ => (u, fun j => vanderCB t ℓ hℓ b (y' j) (α' j))
  have hLHS :
      (B.bind fun b => J.map fun yy =>
        (vanderCB t ℓ hℓ b yy.1 α, fun j => vanderCB t ℓ hℓ b (yy.2 j) (α' j))) = μ.bind P := by
    conv_lhs => rw [← hrec]
    simp only [P, PMF.bind_bind]
  have hRHS :
      ((PMF.uniformOfFintype Bool).bind fun u =>
        B.bind fun b => J.map fun yy => (u, fun j => vanderCB t ℓ hℓ b (yy.2 j) (α' j))) =
      μ.bind Q := by
    conv_lhs => rw [← hrec]
    rw [PMF.bind_comm]
    simp only [Q, PMF.bind_bind]
    exact congrArg (μ.bind ·) (funext fun _ => PMF.bind_comm _ _ _)
  rw [hLHS, hRHS]
  let G : Set Leak := {rest | δ / Fintype.card Leak ≤ (μ rest).toReal}
  have hGc : Gᶜ = {rest | (μ rest).toReal < δ / Fintype.card Leak} := by ext; simp [G, not_le]
  refine dist_bind_le_of_compl_le μ P Q G (by positivity)
    (hGc ▸ toOuterMeasure_badLeak_le μ hδ.le) fun rest hrest hsupp => ?_
  have hfix : ∀ b ∈ (conditionalSnd JB rest).support, leak b = rest := fun b hb =>
    (mem_support_and_eq_of_conditionalSnd_map B leak hsupp hb).2
  have hinj : Set.InjOn (fun b => BinaryField.equivBits hℓ (evalB b a₀))
      (conditionalSnd JB rest).support := by
    intro b₁ hb₁ b₂ hb₂ heq
    have hev₀ : evalB b₁ a₀ = evalB b₂ a₀ := (BinaryField.equivBits hℓ).injective heq
    let poly : Polynomial (BinaryField ℓ) :=
      ∑ i : Fin (t + 1), Polynomial.C
        ((BinaryField.equivBits hℓ).symm (BitString.block b₁ i) -
         (BinaryField.equivBits hℓ).symm (BitString.block b₂ i)) * Polynomial.X ^ i.1
    have hpoly_eval (x : BinaryField ℓ) : poly.eval x = evalB b₁ x - evalB b₂ x := by
      dsimp only [poly, evalB]
      rw [← Polynomial.coe_evalRingHom, map_sum]
      simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, sub_mul, Finset.sum_sub_distrib]
    have hdeg : poly.natDegree ≤ t := by
      refine (Polynomial.natDegree_sum_le _ _).trans ?_
      rw [Finset.fold_max_le]
      refine ⟨Nat.zero_le t, fun i _ => (Polynomial.natDegree_mul_le).trans ?_⟩
      simp only [Polynomial.natDegree_C, zero_add, Polynomial.natDegree_X_pow]
      omega
    have hpoly_zero : poly = 0 := by
      by_contra hne
      have hroots : ∀ x ∈ insert a₀ pts, x ∈ poly.roots := fun x hx => by
        rw [Polynomial.mem_roots hne, Polynomial.IsRoot, hpoly_eval, sub_eq_zero]
        rcases Finset.mem_insert.mp hx with rfl | hpx
        · exact hev₀
        · exact (congrFun (hfix b₁ hb₁) ⟨x, hpx⟩).trans (congrFun (hfix b₂ hb₂) ⟨x, hpx⟩).symm
      have hcard_le : (insert a₀ pts).card ≤ poly.roots.card :=
        Multiset.card_le_card
          ((Multiset.le_iff_subset (insert a₀ pts).nodup).mpr fun x hx => hroots x hx)
      have hcard_ins : (insert a₀ pts).card = t + 1 := by
        rw [Finset.card_insert_of_notMem ha₀_notMem, hpts_card]
      have hle_deg := Polynomial.card_roots' poly
      omega
    apply BitString.blocksEquiv.injective
    funext i
    have hcoeff : poly.coeff i.1 = 0 := by rw [hpoly_zero, Polynomial.coeff_zero]
    dsimp only [poly] at hcoeff
    rw [← Polynomial.lcoeff_apply, map_sum] at hcoeff
    simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at hcoeff
    rw [Finset.sum_eq_single i] at hcoeff
    · simp only [↓reduceIte, mul_one, sub_eq_zero] at hcoeff
      exact (BinaryField.equivBits hℓ).symm.injective hcoeff
    · intro j _ hji
      by_cases heq : i.1 = j.1
      · exact absurd (Fin.ext heq.symm) hji
      · simp [heq]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hkα : kSrc - (t * ℓ : ℕ) - Real.logb 2 δ⁻¹ ≤
      minEntropy ((conditionalSnd JB rest).map fun b => BinaryField.equivBits hℓ (evalB b a₀)) := by
    refine le_minEntropy_map_of_injOn (conditionalSnd JB rest) hinj ?_
    have hB_id : (JB.map Prod.snd).map id = B := by
      simp only [JB, PMF.map_comp, Function.comp_def, PMF.map_id]
    have hchain := minEntropy_map_conditionalSnd_ge_of_apply_ge JB id (k := kSrc) hδ
      (hB_id ▸ hB) hrest
    rwa [PMF.map_id, hlog_leak] at hchain
  let tamper (j : Fin r) : BitString ℓ := BinaryField.equivBits hℓ (rest ⟨a' j, ha'_mem j⟩)
  have hP_eq : P rest = (conditionalSnd JB rest).bind fun b =>
      J.map fun ⟨y, y'⟩ =>
        (BinaryField.equivBits hℓ (evalB b a₀) ⬝ᵥ y, fun j => tamper j ⬝ᵥ y' j) :=
    PMF.bind_congr_on_support _ _ _ fun b hb => congrArg (J.map ·) (funext fun ⟨y, y'⟩ =>
      Prod.ext rfl (funext fun j => by
        have hrestj := congrFun (hfix b hb) ⟨a' j, ha'_mem j⟩
        simp only [vanderCB, evalB, tamper, leak, a'] at hrestj ⊢
        rw [hrestj]))
  have hQ_eq : Q rest = (PMF.uniformOfFintype Bool).bind fun u =>
      (conditionalSnd JB rest).bind fun _ =>
        J.map fun ⟨_, y'⟩ => (u, fun j => tamper j ⬝ᵥ y' j) :=
    congrArg ((PMF.uniformOfFintype Bool).bind ·) (funext fun u =>
      PMF.bind_congr_on_support _ _ _ fun b hb => congrArg (J.map ·) (funext fun ⟨_, y'⟩ =>
        Prod.ext rfl (funext fun j => by
          have hrestj := congrFun (hfix b hb) ⟨a' j, ha'_mem j⟩
          simp only [vanderCB, evalB, tamper, leak, a'] at hrestj ⊢
          rw [hrestj])))
  rw [hP_eq, hQ_eq]
  refine (dist_dotProduct_fiber_le _ J _ tamper hkα hJ).trans_eq ?_
  congr 2; push_cast; ring

end VanderCB

end Cslib.AffineDisperser.Li
