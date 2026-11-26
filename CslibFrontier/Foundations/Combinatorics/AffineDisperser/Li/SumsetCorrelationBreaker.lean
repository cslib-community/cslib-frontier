/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Li.AffineSource
public import CslibFrontier.Foundations.Data.BitString.Block
public import CslibFrontier.Probability.BitString.LinearHash
public import CslibFrontier.Probability.Extractor.Basic
public import CslibFrontier.Probability.Resilience
public import CslibFrontier.Probability.SmallBias
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Probability.Extractor.LeftoverHash
import CslibFrontier.Probability.Extractor.TwoSource
import CslibFrontier.Probability.MinEntropy.ChainRule
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Linear strong extractors, weak-seed correlation breakers, and the sumset-to-NOBF reduction

This module formalizes the core reduction engine behind explicit low-entropy sumset extractors
(following the linear-seeded-extractor + correlation-breaker + resilient-function paradigm of
Chattopadhyay–Liao 2022 and [Li2023]):

1. **Linear strong seeded extractors (`IsLinearStrongExtractor`)**: strong `(k, ε)`-seeded
   extractors `BitString n → Seed → BitString m` that are `𝔽₂`-linear in the source for every fixed
   seed. `BitString.LinearHash` supplies an unconditional instance
   (`isLinearStrongExtractor_linearHash`). Linearity allows a linear strong extractor to extract
   uniform bits from a sumset `A + B` even when the entire second source `B` is revealed
   (`dist_sumset_linearStrongExtractor_le`), and Markov's inequality bounds the set of bad seeds
   (`card_badSeed_le_of_isStrongExtractor`).

2. **Linear-in-source weak-seed correlation breakers (`IsLinearWeakSeedCB`)**: functions
   `cb : BitString n → BitString m → Advice → Bool`, `𝔽₂`-linear in the source, whose output on an
   independent source `B` and weak seed `Y` with advice `α` stays close to uniform even jointly with
   up to `t` tampered outputs using distinct advice strings `α' j ≠ α`. Two unconditional concrete
   instances verify non-vacuity:
   * `t = 0`: `dotProduct` (`isLinearWeakSeedCB_dotProduct`) via Chor–Goldreich;
   * arbitrary `t : ℕ`: `blockDotCB` on `D` disjoint blocks (`isLinearWeakSeedCB_blockDot`) via
     Chor–Goldreich and the min-entropy chain rule
     (`CslibFrontier.Probability.MinEntropy.ChainRule`).

3. **Sumset-to-almost-independent-NOBF reduction**:
   evaluating `sumsetTable LExt LCB x s := LCB x (LExt x s) s` on a sumset `A + B` yields a bit
   table on `Seed` such that, outside the bad seed set `Q` of size at most `(ε₁ / γ) · |Seed|`:
   * every good coordinate `s₀ ∉ Q` is within `2 * γ + δA + δB + εCB` of uniform jointly with any
     `r ≤ t` other coordinates (`dist_sumsetTable_coord_le`);
   * the restriction of the table to `Qᶜ` is `(t + 1)`-wise `(2 * (2 * γ + δA + δB + εCB))`-biased
     (`isKWiseSmallBias_sumsetTable_restrict_compl`);
   * composing `sumsetTable LExt LCB` with any function `R : (Seed → Bool) → Bool` whose bias and
     coalition influence are bounded under `(t + 1)`-wise `η`-biased distributions yields an
     `IsSumsetExtractor` (`isSumsetExtractor_of_linearStrongExtractor_weakSeedCB`).

These theorems are **intermediate reduction steps** toward #7793, not [Li2023] Theorem 7.13 itself:
constructing an explicit logarithmic-seed linear strong extractor, an explicit logarithmic-entropy
correlation breaker, and an explicit polynomial-time resilient function to instantiate them remains
open in #7793.

## Main definitions

* `Cslib.AffineDisperser.Li.IsLinearStrongExtractor`: `𝔽₂`-linear strong seeded extractors.
* `Cslib.AffineDisperser.Li.IsLinearWeakSeedCB`: `𝔽₂`-linear-in-source weak-seed `t`-correlation
  breakers with advice.
* `Cslib.AffineDisperser.Li.blockDotCB`: unconditional arbitrary-`t` block inner-product witness.
* `Cslib.AffineDisperser.Li.sumsetTable`: correlation-broken table `s ↦ LCB x (LExt x s) s`.

## Main results

* `Cslib.AffineDisperser.Li.isLinearStrongExtractor_linearHash`: `LinearHash` is a linear strong
  seeded extractor.
* `Cslib.AffineDisperser.Li.dist_sumset_linearStrongExtractor_le`: linear strong extraction from
  `A + B` remains uniform jointly with `(s, B)`.
* `Cslib.AffineDisperser.Li.card_badSeed_le_of_isStrongExtractor`: Markov bound on bad seeds.
* `Cslib.AffineDisperser.Li.isLinearWeakSeedCB_dotProduct`,
  `Cslib.AffineDisperser.Li.isLinearWeakSeedCB_blockDot`: concrete `t = 0` and arbitrary-`t`
  weak-seed correlation breakers.
* `Cslib.AffineDisperser.Li.dist_sumsetTable_coord_le`: per-coordinate correlation-breaking bound on
  sumset sources.
* `Cslib.AffineDisperser.Li.isKWiseSmallBias_sumsetTable_restrict_compl`: good-seed coordinates of
  `sumsetTable` form a `(t + 1)`-wise small-bias distribution.
* `Cslib.AffineDisperser.Li.isSumsetExtractor_of_linearStrongExtractor_weakSeedCB`: reduction step
  from linear strong extractor + weak-seed correlation breaker + resilient function to
  `IsSumsetExtractor`.

## References

* [E. Chattopadhyay and D. Zuckerman, *Explicit Two-Source Extractors and Resilient
  Functions*][ChattopadhyayZuckerman2019] (NOBF reduction paradigm; locator not verified against
  primary PDF)
* [B. Chor and O. Goldreich, *Unbiased Bits from Sources of Weak Randomness and Probabilistic
  Communication Complexity*][ChorGoldreich1988]
* [X. Li, *Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More*][Li2023],
  ECCC TR23-023 revision 1, Definition 1.1 (p. 1) and Theorem 7.13 (p. 36)
-/

public section

namespace Cslib.AffineDisperser.Li

open Cslib.BitString Cslib.Probability Cslib.Probability.PMF Finset

/-! ### Linear strong seeded extractors -/

section LinearStrongExtractor

/-- A **linear strong `(k, ε)`-seeded extractor** over `𝔽₂`: a strong `(k, ε)`-extractor
`ext : BitString n → Seed → BitString m` that is `𝔽₂`-linear in its source input for every fixed
seed. -/
@[expose] def IsLinearStrongExtractor {n m : ℕ} {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (ext : BitString n → Seed → BitString m) (k ε : ℝ) : Prop :=
  IsStrongExtractor ext k ε ∧
    ∀ (s : Seed) (x y : BitString n), ext (x + y) s = ext x s + ext y s

/-- **Boolean matrix hashing is a linear strong seeded extractor**: `BitString.LinearHash.hash`
provides an unconditional `IsLinearStrongExtractor` whenever `m + 2 log₂ δ⁻¹ ≤ k`. -/
theorem isLinearStrongExtractor_linearHash (n m : ℕ) {δ : ℝ} (hδ : 0 < δ) {k : ℝ}
    (hk : m + 2 * Real.logb 2 δ⁻¹ ≤ k) :
    IsLinearStrongExtractor (fun (x : BitString n) (rows : Fin m → BitString n) =>
      LinearHash.hash rows x) k (δ / 2) :=
  ⟨LinearHash.isStrongExtractor n m hδ hk, fun rows x y => by
    funext i
    simp only [LinearHash.hash, Pi.add_apply, dotProduct_add]⟩

/-- **Linear strong extraction from a sumset source given the second summand**: if `ext` is a
linear strong `(k₁, ε)`-extractor and `k₁ ≤ minEntropy A`, then for every independent source `B`
(with no entropy assumption on `B`), the triple `(s, b, ext (a + b) s)` is within statistical
distance `ε` of `(s, b, u)` where `u` is independent uniform on `BitString m`. -/
theorem dist_sumset_linearStrongExtractor_le {n m : ℕ} {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    {ext : BitString n → Seed → BitString m} {k₁ ε : ℝ}
    (hext : IsLinearStrongExtractor ext k₁ ε) {A B : PMF (BitString n)}
    (hA : k₁ ≤ minEntropy A) :
    dist
      (B.bind fun b => A.bind fun a =>
        (PMF.uniformOfFintype Seed).map fun s => (b, (s, ext (a + b) s)))
      (B.bind fun b =>
        (PMF.uniformOfFintype (Seed × BitString m)).map fun su => (b, su)) ≤ ε := by
  have hinner (b : BitString n) :
      dist (A.bind fun a => (PMF.uniformOfFintype Seed).map fun s => (s, ext (a + b) s))
        (PMF.uniformOfFintype (Seed × BitString m)) ≤ ε := by
    let shift : Seed × BitString m ≃ Seed × BitString m :=
      { toFun := fun p => (p.1, p.2 + ext b p.1)
        invFun := fun p => (p.1, p.2 + ext b p.1)
        left_inv := fun ⟨s, y⟩ => Prod.ext rfl (by simp [add_assoc, BitString.add_self])
        right_inv := fun ⟨s, y⟩ => Prod.ext rfl (by simp [add_assoc, BitString.add_self]) }
    have hmap : (A.bind fun a => (PMF.uniformOfFintype Seed).map fun s => (s, ext (a + b) s)) =
        (A.bind fun a => (PMF.uniformOfFintype Seed).map fun s => (s, ext a s)).map shift := by
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, shift, Equiv.coe_fn_mk,
        hext.2]
    rw [hmap, ← PMF.uniformOfFintype_map_equiv shift]
    exact (dist_map_le _ _ shift).trans (hext.1 A hA)
  have hrewrite :
      (B.bind fun b => A.bind fun a =>
        (PMF.uniformOfFintype Seed).map fun s => (b, (s, ext (a + b) s))) =
      B.bind fun b =>
        (A.bind fun a => (PMF.uniformOfFintype Seed).map fun s => (s, ext (a + b) s)).map
          (b, ·) := by
    refine congrArg (B.bind ·) (funext fun b => ?_)
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [hrewrite, dist_bind_pair]
  exact sum_mul_le B _ ε fun b => hinner b

/-- Average strong-extractor distance over uniform seeds equals the strong-extractor distance. -/
theorem sum_uniform_dist_strongExtractor {Input Seed Output : Type*}
    [Fintype Seed] [Nonempty Seed] [Fintype Output] [Nonempty Output]
    (ext : Input → Seed → Output) (PX : PMF Input) :
    ∑ s : Seed, ((PMF.uniformOfFintype Seed) s).toReal *
        dist (PX.map fun x => ext x s) (PMF.uniformOfFintype Output) =
      dist (PX.bind fun x => (PMF.uniformOfFintype Seed).map fun s => (s, ext x s))
        (PMF.uniformOfFintype (Seed × Output)) := by
  have hcomm :
      (PX.bind fun x => (PMF.uniformOfFintype Seed).map fun s => (s, ext x s)) =
      (PMF.uniformOfFintype Seed).bind fun s => (PX.map fun x => ext x s).map (s, ·) := by
    simp only [PMF.map, Function.comp_def]
    rw [PMF.bind_comm]
    refine congrArg ((PMF.uniformOfFintype Seed).bind ·) (funext fun s => ?_)
    simp only [PMF.bind_bind, PMF.pure_bind]
  rw [hcomm, ← uniformOfFintype_prod, dist_bind_pair]

/-- **Markov bad-seed bound for strong extractors**: if `ext` is a strong `(k, ε)`-extractor and
`k ≤ minEntropy A`, then for any threshold `γ > 0`, at most `(ε / γ) · |Seed|` seeds fail to make
`A.map (ext · s)` `γ`-close to uniform. -/
theorem card_badSeed_le_of_isStrongExtractor {Input Seed Output : Type*}
    [Fintype Seed] [Nonempty Seed] [Fintype Output] [Nonempty Output]
    {ext : Input → Seed → Output} {k ε γ : ℝ} (hγ : 0 < γ)
    (hext : IsStrongExtractor ext k ε) {A : PMF Input} (hA : k ≤ minEntropy A) :
    ((Finset.univ.filter fun s : Seed =>
        γ < dist (A.map fun a => ext a s) (PMF.uniformOfFintype Output)).card : ℝ) ≤
      ε / γ * Fintype.card Seed := by
  classical
  have havg : ∑ s : Seed, ((PMF.uniformOfFintype Seed) s).toReal *
      dist (A.map fun a => ext a s) (PMF.uniformOfFintype Output) ≤ ε := by
    rw [sum_uniform_dist_strongExtractor]
    exact hext A hA
  set Q := Finset.univ.filter fun s : Seed =>
    γ < dist (A.map fun a => ext a s) (PMF.uniformOfFintype Output)
  have hcard_pos : (0 : ℝ) < Fintype.card Seed := by exact_mod_cast Fintype.card_pos
  have hmarkov : (Q.card : ℝ) * (γ / Fintype.card Seed) ≤ ε := by
    calc (Q.card : ℝ) * (γ / Fintype.card Seed)
        = ∑ _s ∈ Q, (Fintype.card Seed : ℝ)⁻¹ * γ := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ s ∈ Q, ((PMF.uniformOfFintype Seed) s).toReal *
            dist (A.map fun a => ext a s) (PMF.uniformOfFintype Output) := by
          refine Finset.sum_le_sum fun s hs => ?_
          rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
          exact mul_le_mul_of_nonneg_left (le_of_lt (Finset.mem_filter.mp hs).2) (by positivity)
      _ ≤ ∑ s : Seed, ((PMF.uniformOfFintype Seed) s).toReal *
            dist (A.map fun a => ext a s) (PMF.uniformOfFintype Output) :=
          Finset.sum_le_univ_sum_of_nonneg fun s =>
            mul_nonneg ENNReal.toReal_nonneg dist_nonneg
      _ ≤ ε := havg
  have h1 : (Q.card : ℝ) * γ ≤ ε * Fintype.card Seed := by
    have := mul_le_mul_of_nonneg_right hmarkov hcard_pos.le
    have hlhs : (Q.card : ℝ) * (γ / Fintype.card Seed) * Fintype.card Seed = (Q.card : ℝ) * γ := by
      field_simp
    linarith
  calc (Q.card : ℝ) = (Q.card : ℝ) * γ / γ := by field_simp
    _ ≤ ε * Fintype.card Seed / γ := div_le_div_of_nonneg_right h1 hγ.le
    _ = ε / γ * Fintype.card Seed := by ring

end LinearStrongExtractor

/-! ### Linear-in-source weak-seed correlation breakers -/

section WeakSeedCB

/-- A **weak-seed `t`-correlation breaker with advice, linear in the source**:
`cb : BitString n → BitString m → Advice → Bool` is `𝔽₂`-linear in its first argument and, for
every independent source `B` with `kSrc ≤ minEntropy B`, every joint seed tuple `(Y, Y')` with
`kSeed ≤ minEntropy (J.map Prod.fst)`, and any `r ≤ t` advice strings `α' : Fin r → Advice` all
distinct from `α`, the bit `cb B Y α` is within statistical distance `ε` of an independent uniform
bit jointly with `(cb B (Y' j) (α' j))_{j : Fin r}`. -/
@[expose] def IsLinearWeakSeedCB {n m : ℕ} {Advice : Type*}
    (cb : BitString n → BitString m → Advice → Bool)
    (kSrc kSeed : ℝ) (t : ℕ) (ε : ℝ) : Prop :=
  (∀ (y : BitString m) (α : Advice) (a b : BitString n), cb (a + b) y α = cb a y α + cb b y α) ∧
  ∀ (r : ℕ), r ≤ t → ∀ (α : Advice) (α' : Fin r → Advice), (∀ j, α' j ≠ α) →
    ∀ (B : PMF (BitString n)) (J : PMF (BitString m × (Fin r → BitString m))),
      kSrc ≤ minEntropy B → kSeed ≤ minEntropy (J.map Prod.fst) →
      dist
        (B.bind fun b => J.map fun yy => (cb b yy.1 α, fun j => cb b (yy.2 j) (α' j)))
        ((PMF.uniformOfFintype Bool).bind fun u =>
          B.bind fun b => J.map fun yy => (u, fun j => cb b (yy.2 j) (α' j))) ≤ ε

/-- **Unconditional `t = 0` linear weak-seed correlation breaker** via Chor–Goldreich: the inner
product `b ⬝ᵥ y` satisfies `IsLinearWeakSeedCB` at `t = 0` with error
`2 ^ ((n - kSrc - kSeed) / 2) / 2`. -/
theorem isLinearWeakSeedCB_dotProduct {n : ℕ} {Advice : Type*} (kSrc kSeed : ℝ) :
    IsLinearWeakSeedCB (fun (b y : BitString n) (_ : Advice) => b ⬝ᵥ y)
      kSrc kSeed 0 (2 ^ (((n : ℝ) - kSrc - kSeed) / 2) / 2) := by
  refine ⟨fun y _ a b => add_dotProduct a b y, ?_⟩
  intro r hr α α' _ B J hB hJ
  have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
  subst hr0
  let e : Bool ≃ Bool × (Fin 0 → Bool) :=
    { toFun := fun z => (z, Fin.elim0)
      invFun := Prod.fst
      left_inv := fun _ => rfl
      right_inv := fun ⟨z, f⟩ => Prod.ext rfl (funext fun j => Fin.elim0 j) }
  have h1 :
      (B.bind fun b => J.map fun yy => (b ⬝ᵥ yy.1, fun j : Fin 0 => b ⬝ᵥ yy.2 j)) =
      (B.bind fun b => (J.map Prod.fst).map fun y => b ⬝ᵥ y).map e := by
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, e, Equiv.coe_fn_mk]
    refine congrArg (B.bind ·) (funext fun b => congrArg (J.map ·) (funext fun yy => ?_))
    exact Prod.ext rfl (funext fun j => Fin.elim0 j)
  have h2 :
      ((PMF.uniformOfFintype Bool).bind fun u =>
        B.bind fun b => J.map fun yy => (u, fun j : Fin 0 => b ⬝ᵥ yy.2 j)) =
      (PMF.uniformOfFintype Bool).map e := by
    simp only [PMF.map, Function.comp_def, e, Equiv.coe_fn_mk]
    refine congrArg ((PMF.uniformOfFintype Bool).bind ·) (funext fun u => ?_)
    have hconst : ∀ b : BitString n,
        (J.bind fun yy => PMF.pure (u, fun j : Fin 0 => b ⬝ᵥ yy.2 j)) =
        PMF.pure (u, Fin.elim0) := fun b => by
      have : (fun yy : BitString n × (Fin 0 → BitString n) =>
          PMF.pure (u, fun j : Fin 0 => b ⬝ᵥ yy.2 j)) =
          fun _ => PMF.pure (u, Fin.elim0) :=
        funext fun yy => congrArg PMF.pure (Prod.ext rfl (funext fun j => Fin.elim0 j))
      rw [this, PMF.bind_const]
    simp only [hconst, PMF.bind_const]
  rw [h1, h2]
  refine (dist_map_le _ _ e).trans ?_
  have hcg := isTwoSourceExtractor_dotProduct (ι := Fin n) kSrc kSeed B (J.map Prod.fst) hB hJ
  simpa only [Fintype.card_fin] using hcg

/-- **Block-partitioned inner-product correlation breaker**: on `D` disjoint blocks of length `ℓ`,
returns the inner product of block `α` with the seed `y`. -/
@[expose] def blockDotCB (D ℓ : ℕ) (b : BitString (D * ℓ)) (y : BitString ℓ) (α : Fin D) : Bool :=
  BitString.block b α ⬝ᵥ y

/-- Deterministic pairing `(f x, x)` recovers `P` on the second coordinate. -/
private theorem map_snd_pair {α β : Type*} (P : PMF α) (f : α → β) :
    (P.map fun x => (f x, x)).map Prod.snd = P := by
  rw [PMF.map_comp]
  exact PMF.map_id P

/-- Conditioning `P` on `f x` and mixing back recovers `P`. -/
theorem bind_conditionalSnd_of_map {α β : Type*} (P : PMF α) (f : α → β) :
    ((P.map fun x => (f x, x)).map Prod.fst).bind
      (conditionalSnd (P.map fun x => (f x, x))) = P := by
  have h := congrArg (PMF.map Prod.snd) (bind_conditionalSnd (P.map fun x => (f x, x)))
  rw [map_snd_pair, PMF.map_bind] at h
  have hsimp : ∀ a : β,
      ((conditionalSnd (P.map fun x => (f x, x)) a).map (a, ·)).map Prod.snd =
      conditionalSnd (P.map fun x => (f x, x)) a := fun a => by
    rw [PMF.map_comp]
    exact PMF.map_id _
  simpa only [hsimp] using h

/-- Every element in the support of `P` conditioned on `f x = ℓ` satisfies `f x = ℓ` and lies in
`P.support`. -/
theorem mem_support_and_eq_of_conditionalSnd_map {α β : Type*} (P : PMF α) (f : α → β) {ℓ : β}
    (hℓ : ℓ ∈ ((P.map fun x => (f x, x)).map Prod.fst).support)
    {x : α} (hx : x ∈ (conditionalSnd (P.map fun x => (f x, x)) ℓ).support) :
    x ∈ P.support ∧ f x = ℓ := by
  have hpair : (ℓ, x) ∈ (P.map fun a => (f a, a)).support :=
    (mem_support_conditionalSnd_iff _ ℓ hℓ x).mp hx
  rw [PMF.mem_support_map_iff] at hpair
  obtain ⟨x', hx', heq⟩ := hpair
  have h1 := congrArg Prod.fst heq
  have h2 := congrArg Prod.snd heq
  dsimp only at h1 h2
  rw [← h2]
  exact ⟨hx', h1⟩

/-- Chor–Goldreich distance bound for a conditioned fiber with fixed tampered outputs. -/
theorem dist_dotProduct_fiber_le {n ℓ r : ℕ} {kSrc kSeed : ℝ}
    (B : PMF (BitString n)) (J : PMF (BitString ℓ × (Fin r → BitString ℓ)))
    (proj : BitString n → BitString ℓ) (tamper : Fin r → BitString ℓ)
    (hB : kSrc ≤ minEntropy (B.map proj)) (hJ : kSeed ≤ minEntropy (J.map Prod.fst)) :
    dist
      (B.bind fun b => J.map fun ⟨y, y'⟩ => (proj b ⬝ᵥ y, fun j => tamper j ⬝ᵥ y' j))
      ((PMF.uniformOfFintype Bool).bind fun u =>
        B.bind fun _ => J.map fun ⟨_, y'⟩ => (u, fun j => tamper j ⬝ᵥ y' j)) ≤
      2 ^ (((ℓ : ℝ) - kSrc - kSeed) / 2) / 2 := by
  let post : (BitString ℓ × (Fin r → BitString ℓ)) × Bool → Bool × (Fin r → Bool) :=
    fun ⟨⟨_, y'⟩, z⟩ => (z, fun j => tamper j ⬝ᵥ y' j)
  have hL :
      (B.bind fun b => J.map fun ⟨y, y'⟩ => (proj b ⬝ᵥ y, fun j => tamper j ⬝ᵥ y' j)) =
      (J.bind fun ⟨y, y'⟩ => (B.map proj).map fun x => ((y, y'), x ⬝ᵥ y)).map post := by
    simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def, post]
    exact PMF.bind_comm B J _
  have hR :
      ((PMF.uniformOfFintype Bool).bind fun u =>
        B.bind fun _ => J.map fun ⟨_, y'⟩ => (u, fun j => tamper j ⬝ᵥ y' j)) =
      (J.bind fun yy => (PMF.uniformOfFintype Bool).map fun u => (yy, u)).map post := by
    simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def, post]
    have hconst (u : Bool) :
        (B.bind fun _ => J.bind fun ⟨_, y'⟩ => PMF.pure (u, fun j => tamper j ⬝ᵥ y' j)) =
        J.bind fun ⟨_, y'⟩ => PMF.pure (u, fun j => tamper j ⬝ᵥ y' j) := PMF.bind_const B _
    simp_rw [hconst]
    exact PMF.bind_comm (PMF.uniformOfFintype Bool) J _
  rw [hL, hR]
  refine (dist_map_le _ _ post).trans ?_
  have hpair :
      dist (J.bind fun ⟨y, y'⟩ => (B.map proj).map fun x => ((y, y'), x ⬝ᵥ y))
        (J.bind fun yy => (PMF.uniformOfFintype Bool).map fun u => (yy, u)) =
      ∑ yy, (J yy).toReal *
        dist ((B.map proj).map fun x => x ⬝ᵥ yy.1) (PMF.uniformOfFintype Bool) := by
    have hmapL (yy : BitString ℓ × (Fin r → BitString ℓ)) :
        ((B.map proj).map fun x => (yy, x ⬝ᵥ yy.1)) =
          ((B.map proj).map fun x => x ⬝ᵥ yy.1).map (yy, ·) := (PMF.map_comp _ _ _).symm
    have hrew : (J.bind fun ⟨y, y'⟩ => (B.map proj).map fun x => ((y, y'), x ⬝ᵥ y)) =
        J.bind fun yy => ((B.map proj).map fun x => x ⬝ᵥ yy.1).map (yy, ·) :=
      congrArg (J.bind ·) (funext fun ⟨y, y'⟩ => hmapL (y, y'))
    rw [hrew]
    exact dist_bind_pair J _ _
  rw [hpair, ← sum_map_mul J Prod.fst
    (fun y => dist ((B.map proj).map fun x => x ⬝ᵥ y) (PMF.uniformOfFintype Bool))]
  simp only [dist_map_uniformOfFintype_bool, mul_div_assoc', ← Finset.sum_div]
  have hcg := sum_mul_abs_bias_dotProduct_le hB hJ
  rw [Fintype.card_fin] at hcg
  exact div_le_div_of_nonneg_right hcg zero_le_two

/-- **Unconditional arbitrary-`t` linear weak-seed correlation breaker**: for every `D ≥ 1`, `ℓ`,
`t : ℕ`, and `δ > 0`, `blockDotCB D ℓ` satisfies `IsLinearWeakSeedCB` with error
`δ + 2 ^ ((D * ℓ - kSrc - kSeed + log₂ δ⁻¹) / 2) / 2`. -/
theorem isLinearWeakSeedCB_blockDot {D ℓ : ℕ} (hD : 1 ≤ D) (t : ℕ) {kSrc kSeed δ : ℝ}
    (hδ : 0 < δ) :
    IsLinearWeakSeedCB (blockDotCB D ℓ) kSrc kSeed t
      (δ + 2 ^ ((((D * ℓ : ℕ) : ℝ) - kSrc - kSeed + Real.logb 2 δ⁻¹) / 2) / 2) := by
  classical
  refine ⟨fun y α a b => ?_, ?_⟩
  · unfold blockDotCB
    have hblock : BitString.block (a + b) α = BitString.block a α + BitString.block b α := rfl
    rw [hblock, add_dotProduct]
  intro r _ α α' hα' B J hB hJ
  let Other := {j : Fin D // j ≠ α} → BitString ℓ
  let leak : BitString (D * ℓ) → Other := fun b j => BitString.block b j.1
  let JB : PMF (Other × BitString (D * ℓ)) := B.map fun b => (leak b, b)
  let μ : PMF Other := JB.map Prod.fst
  have hJB_snd : JB.map Prod.snd = B := map_snd_pair B leak
  have hrec : μ.bind (fun rest => conditionalSnd JB rest) = B := bind_conditionalSnd_of_map B leak
  have hcard_other : Fintype.card Other = 2 ^ ((D - 1) * ℓ) := by
    simp only [Other, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Fintype.card_subtype_compl, Fintype.card_unique, ← pow_mul, mul_comm]
  have hlog_other : Real.logb 2 (Fintype.card Other) = ((D - 1) * ℓ : ℕ) := by
    rw [hcard_other, Nat.cast_pow, Nat.cast_ofNat, Real.logb_two_pow]
  -- Re-express both sides as mixtures over `rest ~ μ` with `b ~ conditionalSnd JB rest`.
  let P (rest : Other) : PMF (Bool × (Fin r → Bool)) :=
    (conditionalSnd JB rest).bind fun b =>
      J.map fun yy => (blockDotCB D ℓ b yy.1 α, fun j => blockDotCB D ℓ b (yy.2 j) (α' j))
  let Q (rest : Other) : PMF (Bool × (Fin r → Bool)) :=
    (PMF.uniformOfFintype Bool).bind fun u =>
      (conditionalSnd JB rest).bind fun b =>
        J.map fun yy => (u, fun j => blockDotCB D ℓ b (yy.2 j) (α' j))
  have hLHS :
      (B.bind fun b => J.map fun yy =>
        (blockDotCB D ℓ b yy.1 α, fun j => blockDotCB D ℓ b (yy.2 j) (α' j))) =
      μ.bind P := by
    conv_lhs => rw [← hrec]
    simp only [P, PMF.bind_bind]
  have hRHS :
      ((PMF.uniformOfFintype Bool).bind fun u =>
        B.bind fun b => J.map fun yy => (u, fun j => blockDotCB D ℓ b (yy.2 j) (α' j))) =
      μ.bind Q := by
    conv_lhs => rw [← hrec]
    rw [PMF.bind_comm]
    simp only [Q, PMF.bind_bind]
    refine congrArg (μ.bind ·) (funext fun rest => ?_)
    rw [PMF.bind_comm]
  rw [hLHS, hRHS]
  let G : Set Other := {rest | δ / Fintype.card Other ≤ (μ rest).toReal}
  have hGcompl : Gᶜ = {rest | (μ rest).toReal < δ / Fintype.card Other} := by
    ext rest
    simp [G, not_le]
  refine dist_bind_le_of_compl_le μ P Q G (by positivity)
    (hGcompl ▸ toOuterMeasure_badLeak_le μ hδ.le) fun rest hrest hsupp => ?_
  -- Conditioned on `rest`, all blocks other than `α` are fixed to `rest`.
  have hfix : ∀ b ∈ (conditionalSnd JB rest).support, leak b = rest := fun b hb =>
    (mem_support_and_eq_of_conditionalSnd_map B leak hsupp hb).2
  have hinj : Set.InjOn (fun b => BitString.block b α) (conditionalSnd JB rest).support := by
    intro b₁ hb₁ b₂ hb₂ hαeq
    apply BitString.blocksEquiv.injective
    funext j
    by_cases hj : j = α
    · subst hj; exact hαeq
    · exact (congrFun (hfix b₁ hb₁) ⟨j, hj⟩).trans (congrFun (hfix b₂ hb₂) ⟨j, hj⟩).symm
  have hkα : kSrc - ((D - 1) * ℓ : ℕ) - Real.logb 2 δ⁻¹ ≤
      minEntropy ((conditionalSnd JB rest).map fun b => BitString.block b α) := by
    refine le_minEntropy_map_of_injOn (conditionalSnd JB rest) hinj ?_
    have hchain := minEntropy_map_conditionalSnd_ge_of_apply_ge JB id (k := kSrc) hδ
      (by rw [hJB_snd, PMF.map_id]; exact hB) hrest
    rwa [PMF.map_id, hlog_other] at hchain
  let tamper (j : Fin r) : BitString ℓ := rest ⟨α' j, hα' j⟩
  have hP_eq : P rest = (conditionalSnd JB rest).bind fun b =>
      J.map fun ⟨y, y'⟩ => (BitString.block b α ⬝ᵥ y, fun j => tamper j ⬝ᵥ y' j) :=
    PMF.bind_congr_on_support _ _ _ fun b hb => congrArg (J.map ·) (funext fun ⟨y, y'⟩ =>
      Prod.ext rfl (funext fun j => by
        have hrestj := congrFun (hfix b hb) ⟨α' j, hα' j⟩
        simp only [blockDotCB, tamper, leak] at hrestj ⊢
        rw [hrestj]))
  have hQ_eq : Q rest = (PMF.uniformOfFintype Bool).bind fun u =>
      (conditionalSnd JB rest).bind fun _ =>
        J.map fun ⟨_, y'⟩ => (u, fun j => tamper j ⬝ᵥ y' j) :=
    congrArg ((PMF.uniformOfFintype Bool).bind ·) (funext fun u =>
      PMF.bind_congr_on_support _ _ _ fun b hb => congrArg (J.map ·) (funext fun ⟨_, y'⟩ =>
        Prod.ext rfl (funext fun j => by
          have hrestj := congrFun (hfix b hb) ⟨α' j, hα' j⟩
          simp only [blockDotCB, tamper, leak] at hrestj ⊢
          rw [hrestj])))
  rw [hP_eq, hQ_eq]
  refine (dist_dotProduct_fiber_le _ J _ tamper hkα hJ).trans_eq ?_
  congr 2
  rw [show D * ℓ = (D - 1) * ℓ + ℓ by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left ℓ hD)]]
  push_cast
  ring

end WeakSeedCB

/-! ### Sumset-to-NOBF correlation-breaking reduction -/

section SumsetReduction

/-- The correlation-broken bit table on `Seed`: for each seed `s`, feeds `LExt x s` into `LCB`
with advice `s`. -/
@[expose] def sumsetTable {n m : ℕ} {Seed : Type*}
    (LExt : BitString n → Seed → BitString m)
    (LCB : BitString n → BitString m → Seed → Bool) (x : BitString n) (s : Seed) : Bool :=
  LCB x (LExt x s) s

/-- **Per-coordinate correlation breaking for sumset sources** (reduction step of Chattopadhyay–Liao
2022 / [Li2023]): if `LExt` is a linear strong seeded extractor, `LCB` is a linear-in-source
weak-seed `t`-correlation breaker, and `s₀` is a `γ`-good seed for `A`, then for any `r ≤ t`
other seeds `s' j ≠ s₀`, the bit `sumsetTable LExt LCB (A + B) s₀` is within
`2 * γ + δA + δB + εCB` of uniform jointly with `(sumsetTable LExt LCB (A + B) (s' j))_{j}`. -/
theorem dist_sumsetTable_coord_le {n m t : ℕ} {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    {LExt : BitString n → Seed → BitString m} {LCB : BitString n → BitString m → Seed → Bool}
    {k₁ k₂ : ℕ} {ε₁ kSrc kSeed εCB γ δA δB : ℝ}
    (hLExt : IsLinearStrongExtractor LExt k₁ ε₁)
    (hCB : IsLinearWeakSeedCB LCB kSrc kSeed t εCB)
    {A B : PMF (BitString n)} (hB : (k₂ : ℝ) ≤ minEntropy B)
    (hγ1 : γ < 1) (hδA : 0 < δA) (hδB : 0 < δB)
    (hεCB : 0 ≤ εCB)
    (hkSrc : kSrc ≤ (k₂ : ℝ) - (((t + 1) * m : ℕ) : ℝ) - Real.logb 2 δB⁻¹)
    (hkSeed : kSeed ≤ (m : ℝ) + Real.logb 2 (1 - γ) - ((t + 1 : ℕ) : ℝ) - Real.logb 2 δA⁻¹)
    {s₀ : Seed} (hs₀ : dist (A.map fun a => LExt a s₀) (PMF.uniformOfFintype (BitString m)) ≤ γ)
    {r : ℕ} (hr : r ≤ t) (s' : Fin r → Seed) (hs' : ∀ j, s' j ≠ s₀) :
    dist
      ((A.bind fun a => B.map fun b => a + b).map fun x =>
        (sumsetTable LExt LCB x s₀, fun j => sumsetTable LExt LCB x (s' j)))
      ((PMF.uniformOfFintype Bool).bind fun u =>
        (A.bind fun a => B.map fun b => a + b).map fun x =>
          (u, fun j => sumsetTable LExt LCB x (s' j))) ≤
      2 * γ + δA + δB + εCB := by
  classical
  -- Step 1: Lift `dist (A.map (LExt · s₀)) U_m ≤ γ` to `A'` with `dist A A' ≤ γ` and exact
  -- min-entropy `m + log₂ (1 - γ)` on `A'.map (LExt · s₀)`.
  obtain ⟨A', hAA', hA'min⟩ :=
    exists_dist_le_and_le_minEntropy_map_of_dist_uniform A (fun a => LExt a s₀) hγ1 hs₀
  have hA'min' : (m : ℝ) + Real.logb 2 (1 - γ) ≤ minEntropy (A'.map fun a => LExt a s₀) := by
    have hcard : Real.logb 2 (Fintype.card (BitString m)) = (m : ℝ) := by
      simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
        Nat.cast_ofNat, Real.logb_two_pow]
    rwa [hcard] at hA'min
  let P (P_A : PMF (BitString n)) : PMF (Bool × (Fin r → Bool)) :=
    (P_A.bind fun a => B.map fun b => a + b).map fun x =>
      (sumsetTable LExt LCB x s₀, fun j => sumsetTable LExt LCB x (s' j))
  let Q (P_A : PMF (BitString n)) : PMF (Bool × (Fin r → Bool)) :=
    (PMF.uniformOfFintype Bool).bind fun u =>
      (P_A.bind fun a => B.map fun b => a + b).map fun x =>
        (u, fun j => sumsetTable LExt LCB x (s' j))
  have hP_AA' : dist (P A) (P A') ≤ γ := by
    refine (dist_map_le _ _ _).trans ((dist_bind_le A A' _).trans hAA')
  have hQ_A'A : dist (Q A') (Q A) ≤ γ := by
    have hQbind (P_A : PMF (BitString n)) :
        Q P_A = P_A.bind fun a => (PMF.uniformOfFintype Bool).bind fun u =>
          B.map fun b => (u, fun j => sumsetTable LExt LCB (a + b) (s' j)) := by
      simp only [Q, PMF.map_bind, PMF.map_comp, Function.comp_def]
      rw [PMF.bind_comm]
    rw [hQbind A', hQbind A]
    exact (dist_bind_le A' A _).trans (dist_comm A' A ▸ hAA')
  -- Step 2: Bound `dist (P A') (Q A') ≤ δA + δB + εCB` by conditioning first on `B`'s linear
  -- extractor outputs and then on `A'`'s correlation-breaker contributions.
  have hcore : dist (P A') (Q A') ≤ δA + δB + εCB := by
    let LeakB := BitString m × (Fin r → BitString m)
    let leakB : BitString n → LeakB := fun b => (LExt b s₀, fun j => LExt b (s' j))
    let JB : PMF (LeakB × BitString n) := B.map fun b => (leakB b, b)
    let μB : PMF LeakB := JB.map Prod.fst
    have hlogB : Real.logb 2 (Fintype.card LeakB) ≤ ((t + 1) * m : ℕ) := by
      have hcard : Fintype.card LeakB = 2 ^ ((r + 1) * m) := by
        simp only [LeakB, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
          ← pow_mul, ← pow_add]
        congr 1
        ring
      rw [hcard, Nat.cast_pow, Nat.cast_ofNat, Real.logb_two_pow]
      exact_mod_cast Nat.mul_le_mul_right m (Nat.add_le_add_right hr 1)
    let PB (ℓ : LeakB) : PMF (Bool × (Fin r → Bool)) :=
      (A'.bind fun a => (conditionalSnd JB ℓ).map fun b => a + b).map fun x =>
        (sumsetTable LExt LCB x s₀, fun j => sumsetTable LExt LCB x (s' j))
    let QB (ℓ : LeakB) : PMF (Bool × (Fin r → Bool)) :=
      (PMF.uniformOfFintype Bool).bind fun u =>
        (A'.bind fun a => (conditionalSnd JB ℓ).map fun b => a + b).map fun x =>
          (u, fun j => sumsetTable LExt LCB x (s' j))
    have hPA' : P A' = μB.bind PB := by
      dsimp only [P, PB, μB, JB]
      conv_lhs => rw [← bind_conditionalSnd_of_map B leakB]
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
      exact PMF.bind_comm A' _ _
    have hQA' : Q A' = μB.bind QB := by
      dsimp only [Q, QB, μB, JB]
      conv_lhs => rw [← bind_conditionalSnd_of_map B leakB]
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
      refine (congrArg ((PMF.uniformOfFintype Bool).bind ·)
        (funext fun _ => PMF.bind_comm A' _ _)).trans ?_
      exact PMF.bind_comm (PMF.uniformOfFintype Bool) _ _
    rw [hPA', hQA', show δA + δB + εCB = δB + (δA + εCB) by ring]
    let GB : Set LeakB := {ℓ | δB / Fintype.card LeakB ≤ (μB ℓ).toReal}
    have hGBc : GBᶜ = {ℓ | (μB ℓ).toReal < δB / Fintype.card LeakB} := by
      ext ℓ; simp [GB, not_le]
    refine dist_bind_le_of_compl_le μB PB QB GB (by linarith)
      (hGBc ▸ toOuterMeasure_badLeak_le μB hδB.le) fun ℓ hℓ hsuppB => ?_
    -- Conditioned on good `ℓ = (u₀, u')`, `B_ℓ` has min-entropy `≥ kSrc` and fixes `LExt b`.
    let Bℓ := conditionalSnd JB ℓ
    have hBℓ_min : kSrc ≤ minEntropy Bℓ := by
      have hchain := minEntropy_map_conditionalSnd_ge_of_apply_ge JB id (k := (k₂ : ℝ)) hδB
        (by rw [map_snd_pair B leakB, PMF.map_id]; exact hB) hℓ
      rw [PMF.map_id] at hchain
      linarith
    have hBℓ_fix : ∀ b ∈ Bℓ.support, LExt b s₀ = ℓ.1 ∧ ∀ j, LExt b (s' j) = ℓ.2 j := fun b hb => by
      have h := (mem_support_and_eq_of_conditionalSnd_map B leakB hsuppB hb).2
      exact ⟨congrArg Prod.fst h, fun j => congrFun (congrArg Prod.snd h) j⟩
    -- Step 2b: Condition `A'` on `A'`'s linear correlation-breaker outputs.
    let LeakA := Bool × (Fin r → Bool)
    let seedOf (a : BitString n) : BitString m × (Fin r → BitString m) :=
      (LExt a s₀ + ℓ.1, fun j => LExt a (s' j) + ℓ.2 j)
    let leakA (a : BitString n) : LeakA :=
      (LCB a (seedOf a).1 s₀, fun j => LCB a ((seedOf a).2 j) (s' j))
    let JA : PMF (LeakA × BitString n) := A'.map fun a => (leakA a, a)
    let μA : PMF LeakA := JA.map Prod.fst
    have hlogA : Real.logb 2 (Fintype.card LeakA) ≤ ((t + 1 : ℕ) : ℝ) := by
      have hcard : Fintype.card LeakA = 2 ^ (r + 1) := by
        simp only [LeakA, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
        rw [pow_succ']
      rw [hcard, Nat.cast_pow, Nat.cast_ofNat, Real.logb_two_pow]
      exact_mod_cast Nat.add_le_add_right hr 1
    let PA (w : LeakA) : PMF (Bool × (Fin r → Bool)) :=
      ((conditionalSnd JA w).bind fun a => Bℓ.map fun b => a + b).map fun x =>
        (sumsetTable LExt LCB x s₀, fun j => sumsetTable LExt LCB x (s' j))
    let QA (w : LeakA) : PMF (Bool × (Fin r → Bool)) :=
      (PMF.uniformOfFintype Bool).bind fun u =>
        ((conditionalSnd JA w).bind fun a => Bℓ.map fun b => a + b).map fun x =>
          (u, fun j => sumsetTable LExt LCB x (s' j))
    have hPB_eq : PB ℓ = μA.bind PA := by
      dsimp only [PB, PA, Bℓ, μA, JA]
      conv_lhs => rw [← bind_conditionalSnd_of_map A' leakA]
      simp only [PMF.map_bind, PMF.bind_bind]
    have hQB_eq : QB ℓ = μA.bind QA := by
      dsimp only [QB, QA, Bℓ, μA, JA]
      conv_lhs => rw [← bind_conditionalSnd_of_map A' leakA]
      simp only [PMF.map_bind, PMF.bind_bind]
      exact PMF.bind_comm (PMF.uniformOfFintype Bool) _ _
    rw [hPB_eq, hQB_eq]
    let GA : Set LeakA := {w | δA / Fintype.card LeakA ≤ (μA w).toReal}
    have hGAc : GAᶜ = {w | (μA w).toReal < δA / Fintype.card LeakA} := by
      ext w; simp [GA, not_le]
    refine dist_bind_le_of_compl_le μA PA QA GA hεCB
      (hGAc ▸ toOuterMeasure_badLeak_le μA hδA.le) fun w hw hsuppA => ?_
    let Aw := conditionalSnd JA w
    have hAw_fix : ∀ a ∈ Aw.support, leakA a = w := fun a ha =>
      (mem_support_and_eq_of_conditionalSnd_map A' leakA hsuppA ha).2
    let Jw : PMF (BitString m × (Fin r → BitString m)) := Aw.map seedOf
    have hJw_min : kSeed ≤ minEntropy (Jw.map Prod.fst) := by
      have hmarg : (JA.map Prod.snd).map (Prod.fst ∘ seedOf) =
          (A'.map fun a => LExt a s₀).map (· + ℓ.1) := by
        rw [map_snd_pair A' leakA, PMF.map_comp]
        rfl
      have hmin_shift : (m : ℝ) + Real.logb 2 (1 - γ) ≤
          minEntropy ((JA.map Prod.snd).map (Prod.fst ∘ seedOf)) := by
        rw [hmarg, le_minEntropy_iff]
        intro y
        change (((A'.map fun a => LExt a s₀).map (Equiv.addRight ℓ.1)) y).toReal ≤ _
        rw [PMF.map_equiv_apply]
        exact (le_minEntropy_iff _).mp hA'min' _
      have hchain := minEntropy_map_conditionalSnd_ge_of_apply_ge JA (Prod.fst ∘ seedOf) hδA
        hmin_shift hw
      have hJw_eq : Jw.map Prod.fst = Aw.map (Prod.fst ∘ seedOf) := PMF.map_comp _ _ _
      rw [hJw_eq]
      linarith
    -- On `Aw.support × Bℓ.support`, `sumsetTable (a + b)` is `w + (LCB b (seedOf a))`.
    let addW : Bool × (Fin r → Bool) ≃ Bool × (Fin r → Bool) := Equiv.addLeft w
    have htab (a b : BitString n) (ha : a ∈ Aw.support) (hb : b ∈ Bℓ.support) :
        (sumsetTable LExt LCB (a + b) s₀, fun j => sumsetTable LExt LCB (a + b) (s' j)) =
        addW (LCB b (seedOf a).1 s₀, fun j => LCB b ((seedOf a).2 j) (s' j)) := by
      have hfa := hAw_fix a ha
      have hfb := hBℓ_fix b hb
      refine Prod.ext ?_ (funext fun j => ?_)
      · simp only [sumsetTable, hLExt.2, hfb.1, hCB.1]
        exact congrArg (· + _) (congrArg Prod.fst hfa)
      · simp only [sumsetTable, hLExt.2, hfb.2, hCB.1]
        exact congrArg (· + _) (congrFun (congrArg Prod.snd hfa) j)
    have hPA_eq : PA w =
        (Bℓ.bind fun b => Jw.map fun yy =>
          (LCB b yy.1 s₀, fun j => LCB b (yy.2 j) (s' j))).map addW := by
      simp only [PA, Jw, Aw, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
      rw [PMF.bind_comm (conditionalSnd JA w) Bℓ]
      refine PMF.bind_congr_on_support Bℓ _ _ fun b hb => ?_
      refine PMF.bind_congr_on_support (conditionalSnd JA w) _ _ fun a ha => ?_
      exact congrArg PMF.pure (htab a b ha hb)
    have hQA_eq : QA w =
        ((PMF.uniformOfFintype Bool).bind fun u =>
          Bℓ.bind fun b => Jw.map fun yy => (u, fun j => LCB b (yy.2 j) (s' j))).map addW := by
      simp only [QA, Jw, Aw, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
      -- Adding `w.1` to the uniform bit `u` preserves uniformity.
      rw [← uniformOfFintype_bind_equiv (Equiv.addLeft w.1)]
      refine congrArg ((PMF.uniformOfFintype Bool).bind ·) (funext fun u => ?_)
      rw [PMF.bind_comm (conditionalSnd JA w) Bℓ]
      refine PMF.bind_congr_on_support Bℓ _ _ fun b hb => ?_
      refine PMF.bind_congr_on_support (conditionalSnd JA w) _ _ fun a ha => ?_
      refine congrArg PMF.pure (Prod.ext (by simp [addW, Equiv.addLeft]) (funext fun j => ?_))
      exact congrFun (congrArg Prod.snd (htab a b ha hb)) j
    rw [hPA_eq, hQA_eq]
    exact (dist_map_le _ _ addW).trans (hCB.2 r hr s₀ s' hs' Bℓ Jw hBℓ_min hJw_min)
  linarith [dist_triangle (P A) (P A') (Q A), dist_triangle (P A') (Q A') (Q A),
    hP_AA', hcore, hQ_A'A]

/-- **Good-seed coordinates of `sumsetTable` are `(t + 1)`-wise small-bias** (reduction step):
for the bad seed set `Q := {s | γ < dist (A.map (LExt · s)) U_m}`, the restriction of
`sumsetTable LExt LCB (A + B)` to `Qᶜ` is `(t + 1)`-wise `(2 * (2 * γ + δA + δB + εCB))`-biased. -/
theorem isKWiseSmallBias_sumsetTable_restrict_compl {n m t : ℕ} {Seed : Type*}
    [Fintype Seed] [DecidableEq Seed] [Nonempty Seed]
    {LExt : BitString n → Seed → BitString m} {LCB : BitString n → BitString m → Seed → Bool}
    {k₁ k₂ : ℕ} {ε₁ kSrc kSeed εCB γ δA δB : ℝ}
    (hLExt : IsLinearStrongExtractor LExt k₁ ε₁)
    (hCB : IsLinearWeakSeedCB LCB kSrc kSeed t εCB)
    {A B : PMF (BitString n)} (hB : (k₂ : ℝ) ≤ minEntropy B)
    (hγ1 : γ < 1) (hδA : 0 < δA) (hδB : 0 < δB) (hεCB : 0 ≤ εCB)
    (hkSrc : kSrc ≤ (k₂ : ℝ) - (((t + 1) * m : ℕ) : ℝ) - Real.logb 2 δB⁻¹)
    (hkSeed : kSeed ≤ (m : ℝ) + Real.logb 2 (1 - γ) - ((t + 1 : ℕ) : ℝ) - Real.logb 2 δA⁻¹) :
    let Q : Finset Seed := Finset.univ.filter fun s : Seed =>
      γ < dist (A.map fun a => LExt a s) (PMF.uniformOfFintype (BitString m))
    IsKWiseSmallBias (t + 1) (2 * (2 * γ + δA + δB + εCB))
      (((A.bind fun a => B.map fun b => a + b).map (sumsetTable LExt LCB)).map Qᶜ.restrict) := by
  classical
  intro Q S hS hScard
  obtain ⟨x₀, hx₀⟩ := hS
  let S' : Finset ↥Qᶜ := S.erase x₀
  have hS'_card : S'.card ≤ t := by
    dsimp only [S']
    have := Finset.card_erase_of_mem hx₀
    omega
  let e : Fin S'.card ≃ S' := (Fintype.equivFinOfCardEq (Fintype.card_coe S')).symm
  let s' : Fin S'.card → Seed := fun j => let ⟨⟨x, _⟩, _⟩ := e j; x
  have hs'_ne : ∀ j, s' j ≠ x₀.1 := fun j h =>
    (Finset.mem_erase.mp (e j).2).1 (Subtype.ext h)
  have hx₀_good : dist (A.map fun a => LExt a x₀.1) (PMF.uniformOfFintype (BitString m)) ≤ γ := by
    have hnot : x₀.1 ∉ Q := Finset.mem_compl.mp x₀.2
    simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnot
    exact hnot
  have hcoord := dist_sumsetTable_coord_le hLExt hCB hB hγ1 hδA hδB hεCB hkSrc hkSeed
    hx₀_good hS'_card s' hs'_ne
  let score : Bool × (Fin S'.card → Bool) → ℝ := fun p =>
    signVal p.1 * ∏ j, signVal (p.2 j)
  have hscore_bound (p : Bool × (Fin S'.card → Bool)) : |score p| ≤ 1 := by
    simp [score, Finset.abs_prod, abs_signVal]
  set X := A.bind fun a => B.map fun b => a + b
  let P := X.map fun x => (sumsetTable LExt LCB x x₀.1, fun j => sumsetTable LExt LCB x (s' j))
  let R := (PMF.uniformOfFintype Bool).bind fun u =>
    X.map fun x => (u, fun j => sumsetTable LExt LCB x (s' j))
  have hP_exp : ∑ p, (P p).toReal * score p =
      bias ((X.map (sumsetTable LExt LCB)).map Qᶜ.restrict) S := by
    rw [bias_map, sum_map_mul, sum_map_mul]
    refine Finset.sum_congr rfl fun x _ => congrArg ((X x).toReal * ·) ?_
    rw [chi_eq_prod_signVal, ← Finset.mul_prod_erase S _ hx₀]
    dsimp only [score, Finset.restrict]
    congr 1
    rw [← Finset.prod_attach S', ← Finset.univ_eq_attach]
    exact Fintype.prod_equiv e (fun j => signVal (sumsetTable LExt LCB x (s' j)))
      (fun a : S' => let ⟨⟨y, _⟩, _⟩ := a; signVal (sumsetTable LExt LCB x y)) (fun _ => rfl)
  have hR_exp : ∑ p, (R p).toReal * score p = 0 := by
    rw [sum_bind_mul]
    have hinner (u : Bool) :
        ∑ p, ((X.map fun x => (u, fun j => sumsetTable LExt LCB x (s' j))) p).toReal * score p =
          signVal u * ∑ x, (X x).toReal * ∏ j, signVal (sumsetTable LExt LCB x (s' j)) := by
      rw [sum_map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => by dsimp only [score]; ring
    simp_rw [hinner, ← mul_assoc]
    rw [← Finset.sum_mul, Fintype.sum_bool]
    simp [PMF.uniformOfFintype_apply, signVal]
  have habs := abs_sum_mul_sub_le P R score hscore_bound
  rw [hP_exp, hR_exp, sub_zero, mul_one] at habs
  exact habs.trans (mul_le_mul_of_nonneg_left hcoord zero_le_two)

/-! ### Private NOBF glue from `(t + 1)`-wise small bias to `IsSumsetExtractor` -/

/-- Extend the `Qᶜ`-marginal of `D` by independent uniform bits on `Q`. -/
private noncomputable def extendOutside {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Finset ι) (D : PMF (ι → Bool)) : PMF (ι → Bool) :=
  (D.map Qᶜ.restrict).bind fun z =>
    (PMF.uniformOfFintype (Q → Bool)).map fun u i =>
      if h : i ∈ Q then u ⟨i, h⟩ else z ⟨i, Finset.mem_compl.mpr h⟩

private theorem map_restrict_compl_extendOutside {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Finset ι) (D : PMF (ι → Bool)) :
    (extendOutside Q D).map Qᶜ.restrict = D.map Qᶜ.restrict := by
  simp only [extendOutside, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have hconst (z : ↥Qᶜ → Bool) :
      ((PMF.uniformOfFintype (Q → Bool)).map fun u =>
        Qᶜ.restrict fun i => if h : i ∈ Q then u ⟨i, h⟩ else z ⟨i, Finset.mem_compl.mpr h⟩) =
      PMF.pure z := by
    have hfun : (fun u : Q → Bool =>
        Qᶜ.restrict fun i => if h : i ∈ Q then u ⟨i, h⟩ else z ⟨i, Finset.mem_compl.mpr h⟩) =
        fun _ => z := funext fun u => funext fun ⟨i, hi⟩ => by
      have hnot : i ∉ Q := Finset.mem_compl.mp hi
      simp [Finset.restrict, hnot]
    rw [hfun]
    change (PMF.uniformOfFintype (Q → Bool)).map (Function.const _ z) = PMF.pure z
    exact PMF.map_const ..
  simp only [hconst, PMF.bind_pure]

private theorem isKWiseSmallBias_extendOutside {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : Finset ι} {D : PMF (ι → Bool)} {k : ℕ} {η : ℝ} (hη : 0 ≤ η)
    (hD : IsKWiseSmallBias k η (D.map Qᶜ.restrict)) :
    IsKWiseSmallBias k η (extendOutside Q D) := by
  intro S hS hSk
  by_cases hsub : S ⊆ Qᶜ
  · let S' : Finset ↥Qᶜ := S.attach.map
      ⟨fun i => ⟨i.1, hsub i.2⟩, fun _ _ h => Subtype.ext (Subtype.mk.inj h)⟩
    have hS'_map : S'.map (Function.Embedding.subtype (· ∈ Qᶜ)) = S := by
      ext i
      simp only [S', Finset.mem_map, Finset.mem_attach, Function.Embedding.subtype_apply,
        true_and, Subtype.exists]
      exact ⟨fun ⟨_, _, ⟨_, hmem, heq⟩, rfl⟩ => by cases congrArg Subtype.val heq; exact hmem,
        fun hi => ⟨i, hsub hi, ⟨i, hi, rfl⟩, rfl⟩⟩
    have hbias : bias (extendOutside Q D) S = bias (D.map Qᶜ.restrict) S' := by
      rw [← map_restrict_compl_extendOutside Q D, bias_map_restrict, hS'_map]
    rw [hbias]
    refine hD S' ?_ ?_
    · obtain ⟨i, hi⟩ := hS
      exact ⟨⟨i, hsub hi⟩, Finset.mem_map.mpr ⟨⟨i, hi⟩, Finset.mem_attach _ _, rfl⟩⟩
    · simpa [S'] using hSk
  · -- Some coordinate `i₀ ∈ S` lies in `Q`, so the independent uniform bit `u i₀` kills the bias.
    obtain ⟨i₀, hi₀S, hi₀Q⟩ : ∃ i₀ ∈ S, i₀ ∈ Q := by simpa [Finset.subset_iff] using hsub
    have hzero : bias (extendOutside Q D) S = 0 := by
      rw [bias, extendOutside, sum_bind_mul]
      refine Finset.sum_eq_zero fun z _ => mul_eq_zero_of_right _ ?_
      rw [sum_map_mul]
      -- Flip bit `⟨i₀, hi₀Q⟩` in `u` to cancel terms pairwise.
      let flip : (Q → Bool) ≃ (Q → Bool) :=
        Function.Involutive.toPerm (fun u => Function.update u ⟨i₀, hi₀Q⟩ !(u ⟨i₀, hi₀Q⟩))
          fun u => funext fun j => by
            by_cases hj : j = ⟨i₀, hi₀Q⟩
            · subst hj; simp
            · simp [hj]
      have hneg (u : Q → Bool) :
          chi ℝ S (fun i => if h : i ∈ Q then flip u ⟨i, h⟩ else z ⟨i, Finset.mem_compl.mpr h⟩) =
          -chi ℝ S (fun i => if h : i ∈ Q then u ⟨i, h⟩ else z ⟨i, Finset.mem_compl.mpr h⟩) := by
        rw [chi_eq_prod_signVal, chi_eq_prod_signVal, ← Finset.mul_prod_erase S _ hi₀S,
          ← Finset.mul_prod_erase S _ hi₀S]
        have hhead :
            signVal (if h : i₀ ∈ Q then flip u ⟨i₀, h⟩ else z ⟨i₀, Finset.mem_compl.mpr h⟩) =
            -signVal (if h : i₀ ∈ Q then u ⟨i₀, h⟩ else z ⟨i₀, Finset.mem_compl.mpr h⟩) := by
          simp only [hi₀Q, ↓reduceDIte, flip, Function.Involutive.toPerm, Equiv.coe_fn_mk,
            Function.update_self]
          cases u ⟨i₀, hi₀Q⟩ <;> norm_num [signVal]
        have hrest :
            (∏ i ∈ S.erase i₀, signVal (if h : i ∈ Q then flip u ⟨i, h⟩
              else z ⟨i, Finset.mem_compl.mpr h⟩)) =
            ∏ i ∈ S.erase i₀, signVal (if h : i ∈ Q then u ⟨i, h⟩
              else z ⟨i, Finset.mem_compl.mpr h⟩) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
          split_ifs with h
          · simp only [flip, Function.Involutive.toPerm, Equiv.coe_fn_mk,
              Function.update_of_ne (show (⟨i, h⟩ : Q) ≠ ⟨i₀, hi₀Q⟩ from fun h' =>
                hne (congrArg Subtype.val h'))]
          · rfl
        rw [hhead, hrest, neg_mul]
      have hsum_neg :
          (∑ u : Q → Bool, ((PMF.uniformOfFintype (Q → Bool)) u).toReal *
            chi ℝ S (fun i => if h : i ∈ Q then u ⟨i, h⟩ else z ⟨i, Finset.mem_compl.mpr h⟩)) =
          -(∑ u : Q → Bool, ((PMF.uniformOfFintype (Q → Bool)) u).toReal *
            chi ℝ S (fun i => if h : i ∈ Q then u ⟨i, h⟩ else z ⟨i, Finset.mem_compl.mpr h⟩)) := by
        conv_lhs =>
          rw [← Fintype.sum_equiv flip _
            (fun u => ((PMF.uniformOfFintype (Q → Bool)) u).toReal *
              chi ℝ S (fun i => if h : i ∈ Q then u ⟨i, h⟩ else z ⟨i, Finset.mem_compl.mpr h⟩))
            (fun _ => rfl)]
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        simp only [PMF.uniformOfFintype_apply, hneg, mul_neg]
      linarith
    rw [hzero, abs_zero]
    exact hη

/-- NOBF perturbation bound: if `D` and `D'` agree on `Qᶜ`, then
`|Pr_D[R = true] - Pr_{D'}[R = true]|` is at most `coalitionInfluence D' Q R`. -/
private theorem abs_sub_prob_true_le_coalitionInfluence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Finset ι) (R : (ι → Bool) → Bool) {D D' : PMF (ι → Bool)}
    (heq : D.map Qᶜ.restrict = D'.map Qᶜ.restrict) :
    |((D.map R) true).toReal - ((D'.map R) true).toReal| ≤ coalitionInfluence D' Q R := by
  classical
  let pad0 (z : ↥Qᶜ → Bool) : ι → Bool :=
    fun i => if h : i ∈ Q then false else z ⟨i, Finset.mem_compl.mpr h⟩
  let lo (z : ↥Qᶜ → Bool) : ℝ :=
    if IsUndetermined Q R (pad0 z) then 0 else if R (pad0 z) = true then 1 else 0
  let hi (z : ↥Qᶜ → Bool) : ℝ :=
    if IsUndetermined Q R (pad0 z) then 1 else if R (pad0 z) = true then 1 else 0
  have hagree (x : ι → Bool) : ∀ i ∉ Q, pad0 (Qᶜ.restrict x) i = x i := fun i hi => by
    simp [pad0, hi, Finset.restrict]
  have hdet (x : ι → Bool) (hu : ¬ IsUndetermined Q R (pad0 (Qᶜ.restrict x))) :
      R x = R (pad0 (Qᶜ.restrict x)) := by
    by_contra hne
    exact hu ⟨x, pad0 (Qᶜ.restrict x), fun i hi => (hagree x i hi).symm, fun _ _ => rfl, hne⟩
  have hbounds (P : PMF (ι → Bool)) :
      ∑ z, ((P.map Qᶜ.restrict) z).toReal * lo z ≤ ((P.map R) true).toReal ∧
      ((P.map R) true).toReal ≤ ∑ z, ((P.map Qᶜ.restrict) z).toReal * hi z := by
    have hPtrue : ((P.map R) true).toReal =
        ∑ x, (P x).toReal * if R x = true then (1 : ℝ) else 0 := by
      rw [map_apply_toReal]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases h : R x = true <;> simp [h, eq_comm]
    rw [hPtrue, sum_map_mul, sum_map_mul]
    constructor <;> refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_
      ENNReal.toReal_nonneg <;> dsimp only [lo, hi] <;>
      by_cases hu : IsUndetermined Q R (pad0 (Qᶜ.restrict x))
    all_goals first
      | rw [ite_eq_left hu]; split_ifs <;> norm_num
      | rw [ite_eq_right hu, hdet x hu]
  have hdiff : ∑ z, ((D'.map Qᶜ.restrict) z).toReal * hi z -
      ∑ z, ((D'.map Qᶜ.restrict) z).toReal * lo z = coalitionInfluence D' Q R := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    rw [sum_map_mul, coalitionInfluence]
    refine Finset.sum_congr rfl fun x _ => congrArg ((D' x).toReal * ·) ?_
    have hiff : IsUndetermined Q R (pad0 (Qᶜ.restrict x)) ↔ IsUndetermined Q R x :=
      isUndetermined_congr (hagree x)
    dsimp only [hi, lo]
    by_cases hu : IsUndetermined Q R x
    · rw [ite_eq_left (hiff.mpr hu), ite_eq_left (hiff.mpr hu), ite_eq_left hu, sub_zero]
    · rw [ite_eq_right (mt hiff.mp hu), ite_eq_right (mt hiff.mp hu), ite_eq_right hu, sub_self]
  obtain ⟨hDlo, hDhi⟩ := hbounds D
  obtain ⟨hD'lo, hD'hi⟩ := hbounds D'
  rw [heq] at hDlo hDhi
  rw [abs_le]
  constructor <;> linarith

/-- **Reduction step from linear strong extractor, linear weak-seed correlation breaker, and
resilient function to `IsSumsetExtractor`** (reduction step of Chattopadhyay–Liao 2022 / [Li2023];
does not itself construct the explicit `O(log n)` family of [Li2023] Theorem 7.13, which remains
open in #7793):

Given a linear strong `(k₁, ε₁)`-extractor `LExt`, a linear weak-seed `t`-correlation breaker `LCB`,
and a Boolean function `R : (Seed → Bool) → Bool` whose bias and coalition influence (for coalitions
of size at most `q`) are bounded by `εBias` and `εInf` on every `(t + 1)`-wise `η`-biased
distribution (with `η = 2 * (2 * γ + δA + δB + εCB)` and `ε₁ / γ * |Seed| ≤ q`),
`x ↦ R (sumsetTable LExt LCB x)` is a `(k₁, k₂, εBias + εInf)` sumset extractor. -/
theorem isSumsetExtractor_of_linearStrongExtractor_weakSeedCB {n m t q : ℕ} {Seed : Type*}
    [Fintype Seed] [DecidableEq Seed] [Nonempty Seed]
    {LExt : BitString n → Seed → BitString m} {LCB : BitString n → BitString m → Seed → Bool}
    {R : (Seed → Bool) → Bool}
    {k₁ k₂ : ℕ} {ε₁ kSrc kSeed εCB γ δA δB εBias εInf : ℝ}
    (hLExt : IsLinearStrongExtractor LExt k₁ ε₁)
    (hCB : IsLinearWeakSeedCB LCB kSrc kSeed t εCB)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hδA : 0 < δA) (hδB : 0 < δB) (hεCB : 0 ≤ εCB)
    (hq : ε₁ / γ * Fintype.card Seed ≤ q)
    (hkSrc : kSrc ≤ (k₂ : ℝ) - (((t + 1) * m : ℕ) : ℝ) - Real.logb 2 δB⁻¹)
    (hkSeed : kSeed ≤ (m : ℝ) + Real.logb 2 (1 - γ) - ((t + 1 : ℕ) : ℝ) - Real.logb 2 δA⁻¹)
    (hR_bias : ∀ D : PMF (Seed → Bool),
      IsKWiseSmallBias (t + 1) (2 * (2 * γ + δA + δB + εCB)) D →
      |((D.map R) true).toReal - 1 / 2| ≤ εBias)
    (hR_res : ∀ (Q : Finset Seed), Q.card ≤ q → ∀ D : PMF (Seed → Bool),
      IsKWiseSmallBias (t + 1) (2 * (2 * γ + δA + δB + εCB)) D →
      coalitionInfluence D Q R ≤ εInf) :
    IsSumsetExtractor (fun x : BitString n => fun _ : Fin 1 => R (sumsetTable LExt LCB x))
      k₁ k₂ (εBias + εInf) := by
  classical
  intro A B hA hB
  let D : PMF (Seed → Bool) := (A.bind fun a => B.map fun b => a + b).map (sumsetTable LExt LCB)
  let Q : Finset Seed := Finset.univ.filter fun s : Seed =>
    γ < dist (A.map fun a => LExt a s) (PMF.uniformOfFintype (BitString m))
  have hQ_card : Q.card ≤ q := by
    have hcard_r : (Q.card : ℝ) ≤ q :=
      (card_badSeed_le_of_isStrongExtractor hγ0 hLExt.1 hA).trans hq
    exact_mod_cast hcard_r
  have hsmall_compl := isKWiseSmallBias_sumsetTable_restrict_compl (A := A) hLExt hCB hB
    hγ1 hδA hδB hεCB hkSrc hkSeed
  let D' : PMF (Seed → Bool) := extendOutside Q D
  have hsmall_D' : IsKWiseSmallBias (t + 1) (2 * (2 * γ + δA + δB + εCB)) D' :=
    isKWiseSmallBias_extendOutside (by linarith) hsmall_compl
  have hpert := abs_sub_prob_true_le_coalitionInfluence Q R
    (map_restrict_compl_extendOutside Q D).symm
  have hbias := hR_bias D' hsmall_D'
  have hinf := hR_res Q hQ_card D' hsmall_D'
  have hbool : dist (D.map R) (PMF.uniformOfFintype Bool) ≤ εBias + εInf := by
    rw [dist_uniformOfFintype_bool]
    have htri := abs_sub_le ((D.map R) true).toReal ((D'.map R) true).toReal (1 / 2)
    linarith
  let e : BitString 1 ≃ Bool := Equiv.funUnique (Fin 1) Bool
  have hlaw : ((A.bind fun a => B.map fun b => a + b).map
      fun x : BitString n => fun _ : Fin 1 => R (sumsetTable LExt LCB x)) =
      (D.map R).map e.symm := by
    simp only [D, PMF.map_comp]
    rfl
  have hunif : PMF.uniformOfFintype (BitString 1) =
      (PMF.uniformOfFintype Bool).map e.symm :=
    (PMF.uniformOfFintype_map_equiv e.symm).symm
  rw [hlaw, hunif]
  exact (dist_map_le _ _ e.symm).trans hbool

end SumsetReduction

end Cslib.AffineDisperser.Li
