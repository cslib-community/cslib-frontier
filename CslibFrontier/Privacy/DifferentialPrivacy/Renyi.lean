/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Privacy.DifferentialPrivacy.Composition
public import CslibFrontier.Privacy.DifferentialPrivacy.Hamming
public import CslibFrontier.Privacy.DifferentialPrivacy.PrivacyLoss
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Hyperbolic

/-!
# Rényi differential privacy

A randomized mechanism `M : D → PMF R` satisfies `(α, ε)`-*Rényi differential privacy* (`RDP`)
relative to an adjacency relation `Adj` when `1 < α`, `0 ≤ ε`, and `D_α(M x ‖ M y) ≤ ε` for every
adjacent pair `(x, y)` (`RenyiDifferentiallyPrivate`, [Mironov2017, Definition 4]). Enforcing
`1 < α` and `0 ≤ ε` in the predicate avoids both the `α = 1` collapse of the finite-order ratio
formula `log M / (α - 1)` to `0` (where [Mironov2017, Definition 3] takes the `α → 1`
Kullback–Leibler limit) and the `ENNReal.ofReal` truncation of negative budgets `ε < 0` to `0`.

Rényi differential privacy enjoys post-processing (`RenyiDifferentiallyPrivate.bind`,
`RenyiDifferentiallyPrivate.map`, [Mironov2017, Section III]), additive sequential composition
under adaptive mechanism choice (`RenyiDifferentiallyPrivate.bind_pair`,
`RenyiDifferentiallyPrivate.adaptiveComposition`, [Mironov2017, Proposition 1]), coordinatewise
parallel composition for local randomizers under Hamming adjacency
(`RenyiDifferentiallyPrivate.pi`), conversion to `(ε + log (1 / δ) / (α - 1), δ)`-differential
privacy (`RenyiDifferentiallyPrivate.differentiallyPrivate`, [Mironov2017, Proposition 3]), a
`tanh` privacy-loss refinement from pure `(ε, 0)`-differential privacy
(`DifferentiallyPrivate.renyiDifferentiallyPrivate_tanh`), and the quadratic `(α, α ε² / 2)`-RDP
bound (`DifferentiallyPrivate.renyiDifferentiallyPrivate_of_pure`,
[BunSteinke2016, Proposition 3.3], cited in [Mironov2017, Section V]).

## Main definitions

* `Cslib.Privacy.RenyiDifferentiallyPrivate`: `(α, ε)`-Rényi differential privacy (`1 < α`,
  `0 ≤ ε`) relative to `Adj` [Mironov2017, Definition 4].

## Main results

* `Cslib.Privacy.RenyiDifferentiallyPrivate.bind`,
  `Cslib.Privacy.RenyiDifferentiallyPrivate.map`: post-processing [Mironov2017, Section III].
* `Cslib.Privacy.RenyiDifferentiallyPrivate.bind_pair`,
  `Cslib.Privacy.RenyiDifferentiallyPrivate.adaptiveComposition`: adaptive sequential composition
  [Mironov2017, Proposition 1].
* `Cslib.Privacy.RenyiDifferentiallyPrivate.pi`: products of local randomizers under
  `HammingAdjacent`.
* `Cslib.Privacy.RenyiDifferentiallyPrivate.differentiallyPrivate`: conversion from `(α, ε)`-RDP
  to `(ε + log (1 / δ) / (α - 1), δ)`-DP [Mironov2017, Proposition 3].
* `Cslib.Privacy.DifferentiallyPrivate.renyiDifferentiallyPrivate_tanh`: privacy-loss refinement
  from pure `(ε, 0)`-DP to `(α, ε tanh (ε / 2) + (α - 1) ε² / 2)`-RDP.
* `Cslib.Privacy.DifferentiallyPrivate.renyiDifferentiallyPrivate_of_pure`: pure `(ε, 0)`-DP
  mechanisms are `(α, α ε² / 2)`-RDP [BunSteinke2016, Proposition 3.3].

## References

* [M. Bun and T. Steinke, *Concentrated Differential Privacy: Simplifications, Extensions, and
  Lower Bounds*][BunSteinke2016]
* [I. Mironov, *Rényi differential privacy*][Mironov2017]
-/

open scoped ENNReal
open Cslib.Probability.PMF (monad_bind_eq_bind monad_pure_eq_pure)

public section

namespace Cslib.Privacy

universe u v w

/-- A mechanism `M : D → PMF R` is `(α, ε)`-Rényi differentially private relative to `Adj` when
`1 < α`, `0 ≤ ε`, and `renyiDiv α (M x) (M y) ≤ ofReal ε` for all `Adj x y`
[Mironov2017, Definition 4]. -/
@[expose] def RenyiDifferentiallyPrivate {D : Type u} {R : Type v}
    (Adj : D → D → Prop) (M : D → PMF R) (α ε : ℝ) : Prop :=
  1 < α ∧ 0 ≤ ε ∧ ∀ ⦃x y⦄, Adj x y → Probability.PMF.renyiDiv α (M x) (M y) ≤ ENNReal.ofReal ε

namespace RenyiDifferentiallyPrivate

section Basic

variable {D : Type u} {R : Type v} {R' : Type w} {Adj : D → D → Prop} {M : D → PMF R} {α ε : ℝ}

/-- Rényi differential privacy is monotone in the privacy budget `ε`. -/
theorem mono {ε' : ℝ} (h : RenyiDifferentiallyPrivate Adj M α ε) (hε : ε ≤ ε') :
    RenyiDifferentiallyPrivate Adj M α ε' :=
  ⟨h.1, h.2.1.trans hε, fun _ _ hxy => (h.2.2 hxy).trans (ENNReal.ofReal_le_ofReal hε)⟩

/-- **Post-processing** [Mironov2017, Section III]: applying a Markov kernel `K` preserves
`(α, ε)`-Rényi differential privacy. -/
theorem bind (h : RenyiDifferentiallyPrivate Adj M α ε) (K : R → PMF R') :
    RenyiDifferentiallyPrivate Adj (fun x => (M x).bind K) α ε :=
  ⟨h.1, h.2.1, fun _ _ hxy => (Probability.PMF.renyiDiv_bind_le h.1 _ _ K).trans (h.2.2 hxy)⟩

/-- Deterministic post-processing preserves `(α, ε)`-Rényi differential privacy
[Mironov2017, Section III]. -/
theorem map (h : RenyiDifferentiallyPrivate Adj M α ε) (f : R → R') :
    RenyiDifferentiallyPrivate Adj (fun x => (M x).map f) α ε :=
  ⟨h.1, h.2.1, fun _ _ hxy => (Probability.PMF.renyiDiv_map_le h.1 _ _ f).trans (h.2.2 hxy)⟩

/-- **Conversion from RDP to approximate DP** [Mironov2017, Proposition 3]: if `M` is
`(α, ε)`-Rényi differentially private, then for every `0 < δ`, `M` is
`(ε + log (1 / δ) / (α - 1), ofReal δ)`-differentially private. -/
theorem differentiallyPrivate {δ : ℝ} (hδ : 0 < δ)
    (h : RenyiDifferentiallyPrivate Adj M α ε) :
    DifferentiallyPrivate Adj M (ε + Real.log (1 / δ) / (α - 1)) (ENNReal.ofReal δ) :=
  DifferentiallyPrivate.iff_hockeyStick_le.mpr fun _ _ hxy =>
    Probability.PMF.hockeyStick_le_of_renyiDiv_le h.1 h.2.1 hδ (h.2.2 hxy)

end Basic

section Composition

variable {D : Type u} {R₁ R₂ R : Type v} {Adj : D → D → Prop} {α ε₁ ε₂ : ℝ}

/-- Adaptive sequential composition when the second stage is `(α, ε₂)`-RDP on outputs satisfying
`P` and the first stage produces only such outputs. -/
private theorem bind_pair_of_support {M₁ : D → PMF R₁} {M₂ : R₁ → D → PMF R₂}
    (hε₂ : 0 ≤ ε₂) (h₁ : RenyiDifferentiallyPrivate Adj M₁ α ε₁) (P : R₁ → Prop)
    (hP : ∀ x r₁, r₁ ∈ (M₁ x).support → P r₁)
    (h₂ : ∀ r₁, P r₁ → RenyiDifferentiallyPrivate Adj (M₂ r₁) α ε₂) :
    RenyiDifferentiallyPrivate Adj
      (fun x => do
        let r₁ ← M₁ x
        let r₂ ← M₂ r₁ x
        return (r₁, r₂)) α (ε₁ + ε₂) := by
  refine ⟨h₁.1, add_nonneg h₁.2.1 hε₂, fun x y hxy => ?_⟩
  simp only [monad_bind_eq_bind, monad_pure_eq_pure]
  rw [ENNReal.ofReal_add h₁.2.1 hε₂]
  exact (Probability.PMF.renyiDiv_bind_pair_le h₁.1 (M₁ x) (M₁ y)
    fun r₁ hr₁ => (h₂ r₁ (hP x r₁ hr₁)).2.2 hxy).trans (add_le_add (h₁.2.2 hxy) le_rfl)

/-- **Adaptive sequential composition** [Mironov2017, Proposition 1]: running an `(α, ε₁)`-RDP
mechanism `M₁` followed by an adaptively chosen `(α, ε₂)`-RDP mechanism `M₂ r₁` (`0 ≤ ε₂`) and
releasing both outputs is `(α, ε₁ + ε₂)`-RDP. -/
theorem bind_pair {M₁ : D → PMF R₁} {M₂ : R₁ → D → PMF R₂}
    (hε₂ : 0 ≤ ε₂)
    (h₁ : RenyiDifferentiallyPrivate Adj M₁ α ε₁)
    (h₂ : ∀ r₁, RenyiDifferentiallyPrivate Adj (M₂ r₁) α ε₂) :
    RenyiDifferentiallyPrivate Adj
      (fun x => do
        let r₁ ← M₁ x
        let r₂ ← M₂ r₁ x
        return (r₁, r₂)) α (ε₁ + ε₂) :=
  bind_pair_of_support hε₂ h₁ (fun _ => True) (fun _ _ _ => trivial) fun r₁ _ => h₂ r₁

/-- **`k`-fold adaptive sequential composition** [Mironov2017, Proposition 1]: if `1 < α` and
round `i < k` is `(α, ε i)`-RDP for every history of length `i`, the `k`-round transcript is
`(α, ∑ i < k, ε i)`-RDP. -/
theorem adaptiveComposition {M : List R → D → PMF R} {ε : ℕ → ℝ}
    (hα : 1 < α) (k : ℕ) (hε : ∀ i < k, 0 ≤ ε i)
    (h : ∀ history : List R,
      history.length < k → RenyiDifferentiallyPrivate Adj (M history) α (ε history.length)) :
    RenyiDifferentiallyPrivate Adj (Privacy.adaptiveComposition M k) α
      (∑ i ∈ Finset.range k, ε i) := by
  induction k with
  | zero => exact ⟨hα, by simp, fun _ _ _ => by simp [Privacy.adaptiveComposition_zero]⟩
  | succ k ih =>
    rw [Finset.sum_range_succ]
    convert ((ih (fun i hi => hε i (Nat.lt_succ_of_lt hi))
      fun history hlen => h history (Nat.lt_succ_of_lt hlen)).bind_pair_of_support (M₂ := M)
      (hε k k.lt_succ_self) (fun history => history.length = k)
      (fun x _ => length_of_mem_support_adaptiveComposition M k x)
      (fun history hl => hl ▸ h history (hl.symm ▸ k.lt_succ_self))).map
      (fun p => p.2 :: p.1) using 2 with x
    simp [Privacy.adaptiveComposition_succ, monad_bind_eq_bind, monad_pure_eq_pure,
      PMF.map_bind, PMF.pure_map]

/-- Products of local randomizers under `HammingAdjacent`: if `1 < α`, `0 ≤ ε`, and each coordinate
randomizer `M i` is `(α, ε)`-RDP against arbitrary changes of its own input, their independent
product is `(α, ε)`-RDP for `HammingAdjacent`. -/
theorem pi {ι X Y : Type*} [Fintype ι] [Finite Y] {M : ι → X → PMF Y} {α ε : ℝ}
    (hα : 1 < α) (hε : 0 ≤ ε)
    (h : ∀ i, RenyiDifferentiallyPrivate (fun _ _ => True) (M i) α ε) :
    RenyiDifferentiallyPrivate HammingAdjacent
      (fun x => Probability.PMF.pi fun i => M i (x i)) α ε := by
  classical
  refine ⟨hα, hε, fun x y hxy => ?_⟩
  by_cases hxy_eq : x = y
  · subst hxy_eq
    simp
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy_eq
  have hupdate : (fun j => M j (y j)) = Function.update (fun j => M j (x j)) i (M i (y i)) := by
    funext j
    rcases eq_or_ne j i with rfl | hji
    · simp
    · rw [Function.update_of_ne hji, Classical.not_not.mp fun hne => hji (hxy hne hi)]
  have hR := Probability.PMF.pi_bind_update (Function.update (fun j => M j (x j)) i (M i (y i))) i
  simp only [Function.update_self, Function.update_idem] at hR
  dsimp only
  rw [hupdate, ← Probability.PMF.pi_bind_update (fun j => M j (x j)) i, ← hR]
  exact ((h i).bind _).2.2 trivial

end Composition

end RenyiDifferentiallyPrivate

section FromPureDP

variable {D : Type u} {R : Type v} {Adj : D → D → Prop} {M : D → PMF R} {ε α : ℝ}

/-- Privacy-loss refinement for pure `(ε, 0)`-differential privacy: any `(ε, 0)`-differentially
private mechanism for a symmetric adjacency relation satisfies
`(α, ε tanh (ε / 2) + (α - 1) ε² / 2)`-Rényi differential privacy for all `1 < α`. -/
theorem DifferentiallyPrivate.renyiDifferentiallyPrivate_tanh
    (hAdj : ∀ ⦃x y⦄, Adj x y → Adj y x) (hε : 0 ≤ ε) (hα : 1 < α)
    (h : DifferentiallyPrivate Adj M ε 0) :
    RenyiDifferentiallyPrivate Adj M α (ε * Real.tanh (ε / 2) + (α - 1) * ε ^ 2 / 2) := by
  have ht : 0 < α - 1 := sub_pos.mpr hα
  have hε_rhs : 0 ≤ ε * Real.tanh (ε / 2) + (α - 1) * ε ^ 2 / 2 :=
    add_nonneg (mul_nonneg hε (Real.tanh_nonneg_iff.mpr (by linarith))) (by positivity)
  exact ⟨hα, hε_rhs, fun _ _ hxy => renyiDiv_le_of_le_mul hε hα
    (DifferentiallyPrivate.iff_apply_le.mp h hxy)
    (DifferentiallyPrivate.iff_apply_le.mp h (hAdj hxy))⟩

/-- **Pure-DP to RDP conversion** [BunSteinke2016, Proposition 3.3] (cited in
[Mironov2017, Section V], where Lemma 1 proves `2 α ε²`): any pure `(ε, 0)`-differentially
private mechanism for a symmetric adjacency relation satisfies `(α, α ε² / 2)`-Rényi differential
privacy for all `1 < α`. -/
theorem DifferentiallyPrivate.renyiDifferentiallyPrivate_of_pure
    (hAdj : ∀ ⦃x y⦄, Adj x y → Adj y x) (hε : 0 ≤ ε) (hα : 1 < α)
    (h : DifferentiallyPrivate Adj M ε 0) :
    RenyiDifferentiallyPrivate Adj M α (α * ε ^ 2 / 2) := by
  refine (h.renyiDifferentiallyPrivate_tanh hAdj hε hα).mono ?_
  have := mul_le_mul_of_nonneg_left (Real.tanh_le_self (by linarith : 0 ≤ ε / 2)) hε
  linarith

end FromPureDP

end Cslib.Privacy
