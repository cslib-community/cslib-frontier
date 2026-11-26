/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.BitBudget
import CslibFrontier.Foundations.Data.Finset.Density
import CslibFrontier.Foundations.Probability.TwoStage

/-!
# Regime-Switched Child-Router and Node-Level Hash Seeds

This file formalizes the regime-switched child-router seed family (`RouterSeed`), grouped per-node
hash-seed spaces (`NodeSeed`), and unified seed-failure concentration bounds for the multi-level
dictionary tree of Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic Dictionary
with Subconstant Wasted Bits per Key* ([LiLiangYuZhou2024, Sections 5.4 and 5.5];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 32–34 / printed pp. 31–33).
Pure node storage structures, Section 5.6 metadata separation, and deterministic tree operations
follow in Stage 2 (#5349).

## Regime-switched child routing (formalization adaptation)

In [LiLiangYuZhou2024, Section 5.4, Lemma 5.1 & Appendix B, Claim B.2], child routing uses Mikkel
Thorup's double-tabulation family [Thorup2013] uniformly across all tree levels under an idealized
asymptotic threshold. In `FeistelPerm`, the explicit finite-size uniqueness threshold
`FeistelPerm.childRouterThreshold epsInv alphaInv` is doubly exponential, so deep internal levels
can satisfy `nLow ℓ < childRouterThreshold epsInv alphaInv` at moderate `n`. We therefore switch
statically per level `0 ≤ ℓ < depth` via `TreeSchedule.usesDoubleTabRouter`:

* **Large-node regime (`childRouterThreshold epsInv alphaInv ≤ nLow ℓ`):** uses
  `FeistelPerm.ChildRouterSeed` (`DoubleTabulation`) and bounds bucket-load deviation via
  `FeistelPerm.dens_childRouter_bucketLoad_outside_le_of_threshold`.
* **Small-node regime (`nLow ℓ < childRouterThreshold epsInv alphaInv`):** uses exact
  `(2 * childRouterHalfInd (nHigh ℓ))`-wise `Cslib.Probability.trinomialPolyHash`, whose degree is
  bounded by the capacity-independent constant `smallRouterMaxDegree epsInv alphaInv`
  (`TreeSchedule.smallRouterDegree_le`) for constant-time Horner evaluation, and bounds bucket-load
  deviation via `FeistelPerm.dens_exists_bucketLoad_sub_ge_le`.

Both regimes satisfy the identical bucket-window failure bound `≤ 1 / (nFloor ℓ) ^ 2`
(`TreeSchedule.dens_routerRound_outside_bounds_le`) and exact bit-budget match
`Fintype.card (P.RouterSeed ℓ) = 2 ^ P.routerSeedBits ℓ`.

## Main definitions

* `Cslib.DataStructure.Dictionary.SubconstantRedundancy.smallRouterMaxDegree`,
  `TreeSchedule.usesDoubleTabRouter`, `TreeSchedule.RouterSeed`, `TreeSchedule.routerRound`,
  `TreeSchedule.routerPerm`: regime-switched child-router seed family and Feistel bijection.
* `TreeSchedule.PrimId`, `TreeSchedule.NodeSeed`, `TreeSchedule.IsGoodNodeSeed`: grouped per-node
  hash seed `g_u` (`Section 5.5`, PDF p. 34 / printed p. 33) and collision/load-balance predicate.

## Main results

* `TreeSchedule.card_routerSeed`, `TreeSchedule.card_nodeSeed`: seed cardinalities match
  `2 ^ routerSeedBits ℓ` and `2 ^ nodeHashSeedBits ℓ`.
* `TreeSchedule.smallRouterDegree_le`: constant `O_{ε, α}(1)` polynomial degree below threshold.
* `TreeSchedule.dens_routerRound_outside_bounds_le`: unified `1 / (nFloor ℓ) ^ 2` child-load failure
  bound across both child-router regimes (`Lemma 5.1(c)`, PDF p. 32 / printed p. 31).
* `TreeSchedule.dens_not_isGoodNodeSeed_le`, `TreeSchedule.exists_isGoodNodeSeed`,
  `TreeSchedule.exists_isGoodNodeSeed_pair`: unified `3 / (nFloor ℓ) ^ 2` node-seed failure bound
  and good-seed existence (`Section 5.5`, PDF p. 34 / printed p. 33).

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
* [M. Pătrașcu, *Succincter*][Patrascu2008]
* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation, and High
  Independence*][Thorup2013]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure.Dictionary
open Cslib.Probability
open Finset

/-- Capacity-independent upper bound on the polynomial degree `2 * childRouterHalfInd (nHigh ℓ)`
whenever `nLow ℓ < childRouterThreshold epsInv alphaInv` (`Section 5.4` small-node adaptation). -/
@[expose]
def smallRouterMaxDegree (epsInv alphaInv : ℕ) : ℕ :=
  2 * FeistelPerm.childRouterHalfInd (4 * FeistelPerm.childRouterThreshold epsInv alphaInv)


namespace TreeSchedule

variable (P : TreeSchedule)

/-! ## Section 1: Regime-switched child-router seed family and load concentration -/

/-- Static level predicate selecting `DoubleTabulation` (`childRouterThreshold ≤ nLow ℓ`) versus
small-node `trinomialPolyHash` (`nLow ℓ < childRouterThreshold`). -/
@[expose]
def usesDoubleTabRouter (ℓ : ℕ) : Prop :=
  FeistelPerm.childRouterThreshold P.epsInv P.alphaInv ≤ P.nLow ℓ

instance instDecidableUsesDoubleTabRouter (ℓ : ℕ) : Decidable (P.usesDoubleTabRouter ℓ) := by
  unfold usesDoubleTabRouter
  infer_instance

/-- Double-tabulation child-router seed type at level `ℓ` above `childRouterThreshold`. -/
abbrev LargeRouterSeed (ℓ : ℕ) : Type :=
  FeistelPerm.ChildRouterSeed
    (FeistelPerm.childRouterChars P.epsInv)
    (FeistelPerm.childRouterRep P.epsInv P.alphaInv)
    (FeistelPerm.childRouterCharBits (FeistelPerm.childRouterChars P.epsInv) (P.routerRightUniv ℓ))
    (P.branchBits ℓ)

/-- Exact `(2 * childRouterHalfInd (nHigh ℓ))`-wise trinomial seed type at level `ℓ` below
`childRouterThreshold`. -/
abbrev SmallRouterSeed (ℓ : ℕ) : Type :=
  Fin (2 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ)) →
    Fin (2 ^ trinomialDeg (P.routerRightUniv ℓ) (P.branchBits ℓ))

/-- Regime-switched child-router seed at level `0 ≤ ℓ < depth`. -/
inductive RouterSeed (P : TreeSchedule) (ℓ : ℕ) : Type
  | doubleTab (h : P.usesDoubleTabRouter ℓ) (seed : P.LargeRouterSeed ℓ)
  | trinomial (h : ¬ P.usesDoubleTabRouter ℓ) (seed : P.SmallRouterSeed ℓ)
  deriving DecidableEq

/-- Canonical equivalence with `LargeRouterSeed ℓ` when `usesDoubleTabRouter ℓ` holds. -/
def routerSeedDoubleTabEquiv {ℓ : ℕ} (h : P.usesDoubleTabRouter ℓ) :
    P.LargeRouterSeed ℓ ≃ P.RouterSeed ℓ where
  toFun := RouterSeed.doubleTab h
  invFun
    | .doubleTab _ s => s
    | .trinomial hn _ => False.elim (hn h)
  left_inv _ := rfl
  right_inv
    | .doubleTab _ _ => rfl
    | .trinomial hn _ => False.elim (hn h)

/-- Canonical equivalence with `SmallRouterSeed ℓ` when `¬ usesDoubleTabRouter ℓ` holds. -/
def routerSeedTrinomialEquiv {ℓ : ℕ} (h : ¬ P.usesDoubleTabRouter ℓ) :
    P.SmallRouterSeed ℓ ≃ P.RouterSeed ℓ where
  toFun := RouterSeed.trinomial h
  invFun
    | .doubleTab hp _ => False.elim (h hp)
    | .trinomial _ s => s
  left_inv _ := rfl
  right_inv
    | .doubleTab hp _ => False.elim (h hp)
    | .trinomial _ _ => rfl

@[simp]
theorem routerSeedDoubleTabEquiv_apply {ℓ : ℕ} (h : P.usesDoubleTabRouter ℓ)
    (seed : P.LargeRouterSeed ℓ) :
    P.routerSeedDoubleTabEquiv h seed = .doubleTab h seed := by rfl

@[simp]
theorem routerSeedTrinomialEquiv_apply {ℓ : ℕ} (h : ¬ P.usesDoubleTabRouter ℓ)
    (seed : P.SmallRouterSeed ℓ) :
    P.routerSeedTrinomialEquiv h seed = .trinomial h seed := by rfl

instance instFintypeRouterSeed (ℓ : ℕ) : Fintype (P.RouterSeed ℓ) :=
  if h : P.usesDoubleTabRouter ℓ then
    Fintype.ofEquiv (P.LargeRouterSeed ℓ) (P.routerSeedDoubleTabEquiv h)
  else
    Fintype.ofEquiv (P.SmallRouterSeed ℓ) (P.routerSeedTrinomialEquiv h)

instance instInhabitedRouterSeed (ℓ : ℕ) : Inhabited (P.RouterSeed ℓ) :=
  if h : P.usesDoubleTabRouter ℓ then
    ⟨.doubleTab h (fun _ _ _ => ⟨0, Nat.two_pow_pos _⟩, fun _ _ => ⟨0, Nat.two_pow_pos _⟩)⟩
  else
    ⟨.trinomial h fun _ => ⟨0, Nat.two_pow_pos _⟩⟩

/-- `RouterSeed P ℓ` has exact cardinality `2 ^ P.routerSeedBits ℓ`. -/
theorem card_routerSeed (ℓ : ℕ) :
    Fintype.card (P.RouterSeed ℓ) = 2 ^ P.routerSeedBits ℓ := by
  dsimp only [routerSeedBits]
  split_ifs with h
  · rw [← Fintype.card_congr (P.routerSeedDoubleTabEquiv h)]
    exact FeistelPerm.card_childRouterSeed _ _ _ _
  · rw [← Fintype.card_congr (P.routerSeedTrinomialEquiv h)]
    simp only [SmallRouterSeed, Fintype.card_fun, Fintype.card_fin, ← Nat.pow_mul]
    exact congrArg (2 ^ ·) (by ring)

/-- Below `childRouterThreshold`, the trinomial child-router polynomial degree is bounded by the
capacity-independent constant `smallRouterMaxDegree P.epsInv P.alphaInv`. -/
theorem smallRouterDegree_le (hcr : P.ConcentrationReady) {ℓ : ℕ} (hℓ : ℓ < P.depth)
    (hsmall : ¬ P.usesDoubleTabRouter ℓ) :
    2 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ) ≤
      smallRouterMaxDegree P.epsInv P.alphaInv := by
  have hlt : P.nLow ℓ < FeistelPerm.childRouterThreshold P.epsInv P.alphaInv := not_le.mp hsmall
  have hnhi : P.nHigh ℓ ≤ 4 * FeistelPerm.childRouterThreshold P.epsInv P.alphaInv := by
    rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
    · have hcap : 2 ≤ P.cap := P.two_le_cap
      simp only [nLow, nHigh, ↓reduceIte] at hlt ⊢
      omega
    · have h2d := hcr.two_mul_delta_le_nFloor ℓ hpos hℓ.le
      dsimp only [nLow, nHigh] at hlt ⊢
      rw [ite_eq_right hpos.ne'] at hlt ⊢
      omega
  dsimp only [smallRouterMaxDegree]
  rw [FeistelPerm.childRouterHalfInd_eq, FeistelPerm.childRouterHalfInd_eq]
  have hclog : Nat.clog 2 (max (P.nHigh ℓ) 2) ≤
      Nat.clog 2 (max (4 * FeistelPerm.childRouterThreshold P.epsInv P.alphaInv) 2) :=
    Nat.clog_mono_right 2 (max_le_max_right 2 hnhi)
  omega

/-- Zero-pad a small-node trinomial router seed from `2 * childRouterHalfInd (nHigh ℓ)`
coefficients to the static capacity-independent degree `smallRouterMaxDegree P.epsInv P.alphaInv`,
so Word-RAM polynomial evaluation (`KWise.evalCode`) can use a single `O(1)`-degree circuit across
all small-node levels. -/
@[expose]
def padSmallRouterSeed (ℓ : ℕ) (seed : P.SmallRouterSeed ℓ) :
    Fin (smallRouterMaxDegree P.epsInv P.alphaInv) →
      Fin (2 ^ trinomialDeg (P.routerRightUniv ℓ) (P.branchBits ℓ)) :=
  fun i =>
    if hi : i.val < 2 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ) then
      seed ⟨i.val, hi⟩
    else
      ⟨0, Nat.two_pow_pos _⟩

/-- Regime-switched Feistel round function `Fin (routerRightUniv ℓ) → Fin (2 ^ branchBits ℓ)`. -/
noncomputable def routerRound (ℓ : ℕ) :
    P.RouterSeed ℓ → Fin (P.routerRightUniv ℓ) → Fin (2 ^ P.branchBits ℓ)
  | .doubleTab _ seed =>
    FeistelPerm.childRouterRound
      (FeistelPerm.childRouterChars P.epsInv)
      (FeistelPerm.childRouterRep P.epsInv P.alphaInv)
      (FeistelPerm.childRouterCharBits (FeistelPerm.childRouterChars P.epsInv)
        (P.routerRightUniv ℓ))
      (P.branchBits ℓ) (P.routerRightUniv ℓ) seed
  | .trinomial _ seed =>
    trinomialPolyHash
      (trinomialStep (P.routerRightUniv ℓ) (P.branchBits ℓ))
      (2 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ))
      (P.routerRightUniv ℓ) (P.branchBits ℓ) seed

/-- Below `childRouterThreshold`, evaluating `routerRound` on a `.trinomial` seed equals evaluating
`trinomialPolyHash` at the static degree `smallRouterMaxDegree P.epsInv P.alphaInv` on
`padSmallRouterSeed ℓ seed`. -/
theorem routerRound_trinomial_eq_padded (hcr : P.ConcentrationReady) {ℓ : ℕ} (hℓ : ℓ < P.depth)
    (hsmall : ¬ P.usesDoubleTabRouter ℓ) (seed : P.SmallRouterSeed ℓ)
    (x : Fin (P.routerRightUniv ℓ)) :
    P.routerRound ℓ (.trinomial hsmall seed) x =
      trinomialPolyHash
        (trinomialStep (P.routerRightUniv ℓ) (P.branchBits ℓ))
        (smallRouterMaxDegree P.epsInv P.alphaInv)
        (P.routerRightUniv ℓ) (P.branchBits ℓ) (P.padSmallRouterSeed ℓ seed) x := by
  have hkM : 2 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ) ≤
      smallRouterMaxDegree P.epsInv P.alphaInv := P.smallRouterDegree_le hcr hℓ hsmall
  let t := trinomialStep (P.routerRightUniv ℓ) (P.branchBits ℓ)
  let k := 2 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ)
  let M := smallRouterMaxDegree P.epsInv P.alphaInv
  apply Fin.ext
  dsimp only [routerRound, trinomialPolyHash, trinomialPolyEval, polynomialHash,
    SmallRouterSeed, trinomialDeg] at seed ⊢
  apply congrArg (· % 2 ^ P.branchBits ℓ)
  apply congrArg Fin.val
  apply congrArg (TrinomialField.equivFin t)
  rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin M)))
    (p := fun i : Fin M => i.val < k)]
  have htail : ∑ i ∈ Finset.univ.filter (fun i : Fin M => ¬ i.val < k),
      (TrinomialField.equivFin t).symm (P.padSmallRouterSeed ℓ seed i) *
        AdjoinRoot.mk (trinomial t) (polyOfCode x.val) ^ (i : ℕ) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hnot : ¬ i.val < 2 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ) := (mem_filter.mp hi).2
    dsimp only [padSmallRouterSeed, trinomialDeg]
    rw [dite_eq_right hnot, TrinomialField.equivFin_symm_eq_mk_polyOfCode]
    simp
  rw [htail, add_zero]
  refine Finset.sum_bij (fun (j : Fin k) _ => (⟨j.val, j.isLt.trans_le hkM⟩ : Fin M))
    (fun j _ => mem_filter.mpr ⟨mem_univ _, j.isLt⟩)
    (fun _ _ _ _ h => Fin.ext (Fin.mk.inj h))
    (fun i hi => ⟨⟨i.val, (mem_filter.mp hi).2⟩, mem_univ _, rfl⟩)
    fun j _ => ?_
  dsimp only [padSmallRouterSeed, trinomialDeg]
  rw [dite_eq_left j.isLt]

/-- Regime-switched child-router Feistel involution on
`Fin (2 ^ branchBits ℓ) × Fin (routerRightUniv ℓ)`. -/
noncomputable def routerPerm (ℓ : ℕ) (θ : P.RouterSeed ℓ) :
    Equiv.Perm (Fin (2 ^ P.branchBits ℓ) × Fin (P.routerRightUniv ℓ)) :=
  FeistelPerm.feistelPairEquiv (P.routerRound ℓ θ)

@[simp]
theorem routerPerm_apply (ℓ : ℕ) (θ : P.RouterSeed ℓ)
    (x : Fin (2 ^ P.branchBits ℓ) × Fin (P.routerRightUniv ℓ)) :
    P.routerPerm ℓ θ x = FeistelPerm.feistelPair (P.routerRound ℓ θ) x := by rfl

@[simp]
theorem routerPerm_symm (ℓ : ℕ) (θ : P.RouterSeed ℓ) :
    (P.routerPerm ℓ θ).symm = P.routerPerm ℓ θ := by rfl

theorem routerPerm_involutive (ℓ : ℕ) (θ : P.RouterSeed ℓ) :
    Function.Involutive (P.routerPerm ℓ θ) :=
  FeistelPerm.feistelPair_involutive (P.routerRound ℓ θ)

private theorem nFloor_le_two_mul_of_nLow_le (hcr : P.ConcentrationReady) {ℓ m : ℕ}
    (hℓ : ℓ ≤ P.depth) (hlo : P.nLow ℓ ≤ m) :
    P.nFloor ℓ ≤ 2 * m := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
  · have h6 := hcr.six_le_nFloor 0 (Nat.zero_le _)
    have h0 := P.nFloor_zero
    simp only [nLow, ↓reduceIte] at hlo
    omega
  · have h2d := hcr.two_mul_delta_le_nFloor ℓ hpos hℓ
    dsimp only [nLow] at hlo
    rw [ite_eq_right hpos.ne'] at hlo
    omega

open scoped Classical in
/-- **Unified child-router bucket-load concentration (`Lemma 5.1(c)` across both regimes)**:
for any level `0 ≤ ℓ < depth` and input set `S` with `nLow ℓ ≤ #S ≤ nHigh ℓ`, under
`P.ConcentrationReady`, at most a `1 / (nFloor ℓ) ^ 2` fraction of seeds in `P.RouterSeed ℓ` let
any child bucket load fall outside `[nLow (ℓ + 1), nHigh (ℓ + 1)]` ([LiLiangYuZhou2024, Section
5.4, Lemma 5.1(c)]; [arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF p. 32 /
printed p. 31). -/
theorem dens_routerRound_outside_bounds_le (hcr : P.ConcentrationReady) {ℓ : ℕ}
    (hℓ : ℓ < P.depth)
    (S : Finset (Fin (2 ^ P.branchBits ℓ) × Fin (P.routerRightUniv ℓ)))
    (hlo : P.nLow ℓ ≤ #S) (hhi : #S ≤ P.nHigh ℓ) :
    (dens {θ : P.RouterSeed ℓ |
      ¬ ∀ b : Fin (2 ^ P.branchBits ℓ),
        P.nLow (ℓ + 1) ≤ FeistelPerm.bucketLoad (P.routerRound ℓ θ) S b ∧
          FeistelPerm.bucketLoad (P.routerRound ℓ θ) S b ≤ P.nHigh (ℓ + 1)} : ℝ) ≤
      1 / (P.nFloor ℓ : ℝ) ^ 2 := by
  let s := P.branchBits ℓ
  let T := P.routerRightUniv ℓ
  let μ : ℝ := (#S : ℝ) / (2 ^ s : ℝ)
  let a : ℝ := ((1 : ℝ) / 5) * μ ^ ((2 : ℝ) / 3)
  have hnF_pos : (0 : ℝ) < (P.nFloor ℓ : ℝ) :=
    Nat.cast_pos.mpr (P.nFloor_pos ℓ hℓ.le)
  have h2m : P.nFloor ℓ ≤ 2 * #S := P.nFloor_le_two_mul_of_nLow_le hcr hℓ.le hlo
  have hwin_imp : ∀ f : Fin T → Fin (2 ^ s),
      (∀ b : Fin (2 ^ s), μ - a ≤ (FeistelPerm.bucketLoad f S b : ℝ) ∧
        (FeistelPerm.bucketLoad f S b : ℝ) ≤ μ + a) →
      ∀ b : Fin (2 ^ s),
        P.nLow (ℓ + 1) ≤ FeistelPerm.bucketLoad f S b ∧
          FeistelPerm.bucketLoad f S b ≤ P.nHigh (ℓ + 1) := fun f hf b =>
    hcr.window_contained ℓ hℓ #S (FeistelPerm.bucketLoad f S b) hlo hhi (hf b).1 (hf b).2
  by_cases hdt : P.usesDoubleTabRouter ℓ
  · rw [← Fintype.dens_filter_comp_equiv (P.routerSeedDoubleTabEquiv hdt)]
    have hthresh : FeistelPerm.childRouterThreshold P.epsInv P.alphaInv ≤ #S := hdt.trans hlo
    have hm_mono : FeistelPerm.childRouterHalfInd #S ≤
        FeistelPerm.childRouterHalfInd (P.nHigh ℓ) := by
      rw [FeistelPerm.childRouterHalfInd_eq, FeistelPerm.childRouterHalfInd_eq]
      have hc := Nat.clog_mono_right 2 (max_le_max_right 2 hhi)
      omega
    have hconc : 2 ^ s * (150 * FeistelPerm.childRouterHalfInd #S) ^ 3 ≤ #S :=
      (Nat.mul_le_mul_left (2 ^ s) (Nat.pow_le_pow_left (by omega) 3)).trans
        ((hcr.conc_bound ℓ hℓ).trans hlo)
    have h4S : (P.nFloor ℓ : ℝ) ^ 2 ≤ 4 * (#S : ℝ) ^ 2 := by
      have : (P.nFloor ℓ : ℝ) ≤ 2 * #S := by exact_mod_cast h2m
      nlinarith
    refine (NNRat.cast_le.mpr (dens_le_dens fun seed hseed => ?_)).trans
      ((FeistelPerm.dens_childRouter_bucketLoad_outside_le_of_threshold (hcr.gap_bound ℓ hℓ) S
        hthresh hconc).trans (one_div_le_one_div_of_le (sq_pos_of_pos hnF_pos) h4S))
    simp only [mem_filter, Finset.mem_univ, true_and, routerSeedDoubleTabEquiv_apply,
      routerRound] at hseed ⊢
    exact fun hgood => hseed (hwin_imp _ hgood)
  · rw [← Fintype.dens_filter_comp_equiv (P.routerSeedTrinomialEquiv hdt)]
    let m_hi := FeistelPerm.childRouterHalfInd (P.nHigh ℓ)
    let L_hi := Nat.clog 2 (max (P.nHigh ℓ) 2)
    have hm_eq : m_hi = 3 * L_hi + 4 := FeistelPerm.childRouterHalfInd_eq (P.nHigh ℓ)
    have hm1 : 1 ≤ m_hi := by omega
    have hconc_hi : 2 ^ s * (150 * m_hi) ^ 3 ≤ #S := (hcr.conc_bound ℓ hℓ).trans hlo
    have hS_pos : 0 < #S := (by positivity : 0 < 2 ^ s * (150 * m_hi) ^ 3).trans_le hconc_hi
    have hμ_pos : 0 < μ := div_pos (Nat.cast_pos.mpr hS_pos) (pow_pos two_pos s)
    let u : ℝ := μ ^ ((1 : ℝ) / 3)
    have hu_pos : 0 < u := Real.rpow_pos_of_pos hμ_pos _
    have hu_pow (k : ℕ) : μ ^ ((k : ℝ) / 3) = u ^ k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hμ_pos.le]
      exact congrArg (μ ^ ·) (by ring)
    have hu3 : u ^ 3 = μ := by rw [← hu_pow]; norm_num
    have h150 : 150 * (m_hi : ℝ) ≤ u := by
      refine (pow_le_pow_iff_left₀ (by positivity) hu_pos.le (Nat.succ_ne_zero 2)).mp ?_
      rw [hu3, le_div_iff₀ (pow_pos two_pos s), mul_comm]
      exact_mod_cast hconc_hi
    have ha_pos : 0 < a := mul_pos (by norm_num) (Real.rpow_pos_of_pos hμ_pos _)
    have hm_real : (1 : ℝ) ≤ m_hi := by exact_mod_cast hm1
    have hmμ : 2 * (m_hi : ℝ) ≤ 3 * μ := by
      rw [← hu3]
      linarith [le_self_pow₀ (by linarith : (1 : ℝ) ≤ u) (by norm_num : 3 ≠ 0)]
    have hrat : 3 * (m_hi : ℝ) * μ / a ^ 2 ≤ (1 : ℝ) / 2 := by
      have ha2 : a ^ 2 = ((1 : ℝ) / 25) * u ^ 4 := by
        dsimp only [a]
        rw [show (2 : ℝ) / 3 = ((2 : ℕ) : ℝ) / 3 by norm_num, hu_pow]
        ring
      rw [div_le_iff₀ (pow_pos ha_pos 2), ha2, ← hu3]
      linarith [mul_le_mul_of_nonneg_right h150 (pow_nonneg hu_pos.le 3)]
    have hkw : IsKWiseIndependentHash (2 * m_hi)
        (trinomialPolyHash (trinomialStep T s) (2 * m_hi) T s) :=
      isKWiseIndependentHash_trinomialPolyHash (le_two_pow_trinomialDeg T s) (le_trinomialDeg T s)
    have h2s_le : 2 ^ s ≤ 2 ^ L_hi :=
      calc 2 ^ s ≤ 2 ^ s * (150 * m_hi) ^ 3 := Nat.le_mul_of_pos_right _ (by positivity)
        _ ≤ #S := hconc_hi
        _ ≤ max (P.nHigh ℓ) 2 := hhi.trans (le_max_left _ 2)
        _ ≤ 2 ^ L_hi := Nat.le_pow_clog Nat.one_lt_two _
    have hnF_le : P.nFloor ℓ ≤ 2 ^ L_hi := by
      have hnF_hi : P.nFloor ℓ ≤ P.nHigh ℓ := by
        dsimp only [nHigh]
        rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
        · simp [P.nFloor_zero]
        · rw [ite_eq_right hpos.ne']; omega
      exact (hnF_hi.trans (le_max_left _ 2)).trans (Nat.le_pow_clog Nat.one_lt_two _)
    have hpow_nat : 2 ^ (s + 1) * (P.nFloor ℓ) ^ 2 ≤ 2 ^ m_hi :=
      calc 2 ^ (s + 1) * (P.nFloor ℓ) ^ 2
          ≤ 2 * 2 ^ L_hi * (2 ^ L_hi) ^ 2 := by
            rw [Nat.pow_succ']
            exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 h2s_le) (Nat.pow_le_pow_left hnF_le 2)
        _ = 2 ^ (3 * L_hi + 1) := by
            rw [← Nat.pow_mul, ← Nat.pow_succ', ← Nat.pow_add]
            congr 1; omega
        _ ≤ 2 ^ m_hi := Nat.pow_le_pow_right Nat.two_pos (by omega)
    have hpow_real : (2 ^ (s + 1) : ℝ) * ((1 : ℝ) / 2) ^ m_hi ≤
        1 / (P.nFloor ℓ : ℝ) ^ 2 := by
      rw [one_div_pow, mul_one_div, div_le_div_iff₀ (pow_pos two_pos m_hi) (sq_pos_of_pos hnF_pos),
        one_mul]
      exact_mod_cast hpow_nat
    refine (NNRat.cast_le.mpr (dens_le_dens fun seed hseed => ?_)).trans
      (((FeistelPerm.dens_exists_bucketLoad_sub_ge_le hm1 hkw S hmμ ha_pos).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hrat m_hi)
          (pow_nonneg (by norm_num) _))).trans hpow_real)
    simp only [mem_filter, Finset.mem_univ, true_and, routerSeedTrinomialEquiv_apply,
      routerRound] at hseed
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    by_contra! hno
    refine hseed (hwin_imp _ fun b => ?_)
    have hb := abs_lt.mp (hno b)
    exact ⟨by linarith only [hb.1], by linarith only [hb.2]⟩

/-! ## Section 2: Grouped per-node hash seeds `g_u` and unified `3 / n_ℓ ^ 2` bound -/

/-- Level-`ℓ` primitive key-ID domain (`Section 5.5` input `x_prim` to `g_u`):
`Fin (2 ^ branchBits 0) × Fin (routerRightUniv 0)` at `ℓ = 0`, and
`Fin (2 ^ idBits ℓ) × Fin (idCompRightUniv ℓ)` at `ℓ ≥ 1`. -/
abbrev PrimId (P : TreeSchedule) : ℕ → Type
  | 0 => Fin (2 ^ P.branchBits 0) × Fin (P.routerRightUniv 0)
  | ℓ + 1 => Fin (2 ^ P.idBits (ℓ + 1)) × Fin (P.idCompRightUniv (ℓ + 1))

instance instFintypePrimId (ℓ : ℕ) : Fintype (P.PrimId ℓ) := by
  cases ℓ <;> dsimp only [PrimId] <;> infer_instance

instance instDecidableEqPrimId (ℓ : ℕ) : DecidableEq (P.PrimId ℓ) := by
  cases ℓ <;> dsimp only [PrimId] <;> infer_instance

/-- Grouped per-node hash seed `g_u ∈ G_ℓ` (`Section 5.5`, PDF p. 34 / printed p. 33):
`RouterSeed 0` at `ℓ = 0`, `(IdCompressorSeed, RouterSeed ℓ)` for `1 ≤ ℓ < depth`, and
`IdCompressorSeed` at leaf level `ℓ ≥ depth`. -/
inductive NodeSeed (P : TreeSchedule) : ℕ → Type
  | top (router : P.RouterSeed 0) : NodeSeed P 0
  | inner {ℓ : ℕ} (hlt : ℓ + 1 < P.depth)
      (idSeed : FeistelPerm.IdCompressorSeed (P.idBits (ℓ + 1)) (P.idCompRightUniv (ℓ + 1)))
      (router : P.RouterSeed (ℓ + 1)) : NodeSeed P (ℓ + 1)
  | leaf {ℓ : ℕ} (hge : ¬ (ℓ + 1 < P.depth))
      (idSeed : FeistelPerm.IdCompressorSeed (P.idBits (ℓ + 1)) (P.idCompRightUniv (ℓ + 1))) :
      NodeSeed P (ℓ + 1)
  deriving DecidableEq

/-- Equivalence `RouterSeed 0 ≃ NodeSeed 0` at the top router. -/
def nodeSeedZeroEquiv : P.RouterSeed 0 ≃ P.NodeSeed 0 where
  toFun := NodeSeed.top
  invFun | .top r => r
  left_inv _ := rfl
  right_inv | .top _ => rfl

/-- Equivalence `(IdCompressorSeed × RouterSeed) ≃ NodeSeed (ℓ + 1)` for `ℓ + 1 < depth`. -/
def nodeSeedInnerEquiv {ℓ : ℕ} (hlt : ℓ + 1 < P.depth) :
    (FeistelPerm.IdCompressorSeed (P.idBits (ℓ + 1)) (P.idCompRightUniv (ℓ + 1)) ×
      P.RouterSeed (ℓ + 1)) ≃ P.NodeSeed (ℓ + 1) where
  toFun p := .inner hlt p.1 p.2
  invFun
    | .inner _ idS r => (idS, r)
    | .leaf hge _ => False.elim (hge hlt)
  left_inv _ := rfl
  right_inv
    | .inner _ _ _ => rfl
    | .leaf hge _ => False.elim (hge hlt)

/-- Equivalence `IdCompressorSeed ≃ NodeSeed (ℓ + 1)` for `¬ (ℓ + 1 < depth)`. -/
def nodeSeedLeafEquiv {ℓ : ℕ} (hge : ¬ (ℓ + 1 < P.depth)) :
    FeistelPerm.IdCompressorSeed (P.idBits (ℓ + 1)) (P.idCompRightUniv (ℓ + 1)) ≃
      P.NodeSeed (ℓ + 1) where
  toFun idS := .leaf hge idS
  invFun
    | .inner hlt _ _ => False.elim (hge hlt)
    | .leaf _ idS => idS
  left_inv _ := rfl
  right_inv
    | .inner hlt _ _ => False.elim (hge hlt)
    | .leaf _ _ => rfl

@[simp]
theorem nodeSeedZeroEquiv_apply (r : P.RouterSeed 0) :
    P.nodeSeedZeroEquiv r = .top r := by rfl

@[simp]
theorem nodeSeedInnerEquiv_apply {ℓ : ℕ} (hlt : ℓ + 1 < P.depth)
    (p : FeistelPerm.IdCompressorSeed (P.idBits (ℓ + 1)) (P.idCompRightUniv (ℓ + 1)) ×
      P.RouterSeed (ℓ + 1)) :
    P.nodeSeedInnerEquiv hlt p = .inner hlt p.1 p.2 := by rfl

@[simp]
theorem nodeSeedLeafEquiv_apply {ℓ : ℕ} (hge : ¬ (ℓ + 1 < P.depth))
    (idS : FeistelPerm.IdCompressorSeed (P.idBits (ℓ + 1)) (P.idCompRightUniv (ℓ + 1))) :
    P.nodeSeedLeafEquiv hge idS = .leaf hge idS := by rfl

instance instFintypeNodeSeed : ∀ ℓ, Fintype (P.NodeSeed ℓ)
  | 0 => Fintype.ofEquiv _ P.nodeSeedZeroEquiv
  | ℓ + 1 =>
    if hlt : ℓ + 1 < P.depth then
      Fintype.ofEquiv _ (P.nodeSeedInnerEquiv hlt)
    else
      Fintype.ofEquiv _ (P.nodeSeedLeafEquiv hlt)

instance instInhabitedNodeSeed : ∀ ℓ, Inhabited (P.NodeSeed ℓ)
  | 0 => ⟨.top default⟩
  | ℓ + 1 =>
    if hlt : ℓ + 1 < P.depth then
      ⟨.inner hlt (fun _ => ⟨0, Nat.two_pow_pos _⟩) default⟩
    else
      ⟨.leaf hlt fun _ => ⟨0, Nat.two_pow_pos _⟩⟩

/-- `NodeSeed P ℓ` has exact cardinality `2 ^ P.nodeHashSeedBits ℓ`. -/
theorem card_nodeSeed (ℓ : ℕ) :
    Fintype.card (P.NodeSeed ℓ) = 2 ^ P.nodeHashSeedBits ℓ := by
  cases ℓ with
  | zero =>
    rw [← Fintype.card_congr P.nodeSeedZeroEquiv, P.card_routerSeed 0]
    rfl
  | succ j =>
    dsimp only [nodeHashSeedBits]
    rw [ite_eq_right (Nat.succ_ne_zero j)]
    by_cases hlt : j + 1 < P.depth
    · rw [ite_eq_left hlt, ← Fintype.card_congr (P.nodeSeedInnerEquiv hlt), Fintype.card_prod,
        FeistelPerm.card_idCompressorSeed, P.card_routerSeed (j + 1), ← Nat.pow_add, Nat.add_comm]
    · rw [ite_eq_right hlt, Nat.zero_add, ← Fintype.card_congr (P.nodeSeedLeafEquiv hlt),
        FeistelPerm.card_idCompressorSeed]

/-- Extract the ID-compressor seed component of `g : P.NodeSeed (ℓ + 1)`. -/
@[expose]
def idSeedOfNodeSeed {ℓ : ℕ} :
    P.NodeSeed (ℓ + 1) →
      FeistelPerm.IdCompressorSeed (P.idBits (ℓ + 1)) (P.idCompRightUniv (ℓ + 1))
  | .inner _ idS _ => idS
  | .leaf _ idS => idS

/-- Extract the child-router seed component of `g : P.NodeSeed ℓ` when `ℓ < P.depth`. -/
@[expose]
def routerSeedOfNodeSeed : ∀ {ℓ : ℕ}, ℓ < P.depth → P.NodeSeed ℓ → P.RouterSeed ℓ
  | 0, _, .top r => r
  | _ + 1, _, .inner _ _ r => r
  | _ + 1, hlt, .leaf hge _ => False.elim (hge hlt)

/-- Node-seed goodness predicate (`Section 5.5` "does not fail", PDF p. 34 / printed p. 33):
no ID collision on `S` (`ℓ ≥ 1`), and every child bucket load lies in
`[nLow (ℓ + 1), nHigh (ℓ + 1)]` (`ℓ < depth`). -/
@[expose]
def IsGoodNodeSeed : ∀ ℓ : ℕ, P.NodeSeed ℓ → Finset (P.PrimId ℓ) → Prop
  | 0, .top router, S =>
    ∀ b : Fin (2 ^ P.branchBits 0),
      P.nLow 1 ≤ FeistelPerm.bucketLoad (P.routerRound 0 router) S b ∧
        FeistelPerm.bucketLoad (P.routerRound 0 router) S b ≤ P.nHigh 1
  | ℓ + 1, .inner hlt idSeed router, S =>
    have hsL : P.branchBits (ℓ + 1) ≤ P.idBits (ℓ + 1) := by
      have := P.idBits_step_le (ℓ + 1) (by omega) hlt
      omega
    Set.InjOn (FeistelPerm.idCompressorHead (P.idBits (ℓ + 1)) (P.idCompRightUniv (ℓ + 1)) idSeed)
        (S : Set (P.PrimId (ℓ + 1))) ∧
      ∀ b : Fin (2 ^ P.branchBits (ℓ + 1)),
        let S_id := (S.image
          (FeistelPerm.idCompressorHead (P.idBits (ℓ + 1)) (P.idCompRightUniv (ℓ + 1)) idSeed)).map
          (FeistelPerm.bitDomainEquiv hsL).toEmbedding
        P.nLow (ℓ + 2) ≤ FeistelPerm.bucketLoad (P.routerRound (ℓ + 1) router) S_id b ∧
          FeistelPerm.bucketLoad (P.routerRound (ℓ + 1) router) S_id b ≤ P.nHigh (ℓ + 2)
  | ℓ + 1, .leaf _ idSeed, S =>
    Set.InjOn (FeistelPerm.idCompressorHead (P.idBits (ℓ + 1)) (P.idCompRightUniv (ℓ + 1)) idSeed)
      (S : Set (P.PrimId (ℓ + 1)))

open scoped Classical in
/-- **Unified `3 / n_ℓ ^ 2` single-set node-seed failure bound (`Section 5.5`)**:
for any `0 ≤ ℓ ≤ depth` and primitive-ID set `S` with `nLow ℓ ≤ #S ≤ nHigh ℓ`, under
`P.ConcentrationReady`, a uniform seed `g : P.NodeSeed ℓ` fails on `S` with density at most
`3 / (nFloor ℓ) ^ 2` ([LiLiangYuZhou2024, Section 5.5];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF p. 34 / printed p. 33). -/
theorem dens_not_isGoodNodeSeed_le (hcr : P.ConcentrationReady) {ℓ : ℕ} (hℓ : ℓ ≤ P.depth)
    (S : Finset (P.PrimId ℓ)) (hlo : P.nLow ℓ ≤ #S) (hhi : #S ≤ P.nHigh ℓ) :
    (dens {g : P.NodeSeed ℓ | ¬ P.IsGoodNodeSeed ℓ g S} : ℝ) ≤
      3 / (P.nFloor ℓ : ℝ) ^ 2 := by
  have hle (c : ℝ) (hc : c ≤ 3) : c / (P.nFloor ℓ : ℝ) ^ 2 ≤ 3 / (P.nFloor ℓ : ℝ) ^ 2 := by
    gcongr
  cases ℓ with
  | zero =>
    rw [← Fintype.dens_filter_comp_equiv P.nodeSeedZeroEquiv]
    refine (NNRat.cast_le.mpr (dens_le_dens fun θ hθ => ?_)).trans
      ((P.dens_routerRound_outside_bounds_le hcr (by have := P.two_le_depth; omega) S hlo
        hhi).trans (hle 1 (by norm_num)))
    simpa [IsGoodNodeSeed] using hθ
  | succ j =>
    let S0 : Finset (Fin (2 ^ P.idBits (j + 1)) × Fin (P.idCompRightUniv (j + 1))) := S
    have hid_le := FeistelPerm.dens_not_injOn_idCompressorHead_le_two_div_sq S0 hhi
      (P.nFloor_pos (j + 1) hℓ) (hcr.id_collision_bound (j + 1) (by omega) hℓ)
    by_cases hlt : j + 1 < P.depth
    · rw [← Fintype.dens_filter_comp_equiv (P.nodeSeedInnerEquiv hlt)]
      have hsL : P.branchBits (j + 1) ≤ P.idBits (j + 1) := by
        have := P.idBits_step_le (j + 1) (by omega) hlt
        omega
      refine (dens_prod_le_add_of_good _
        (fun p => ¬ P.IsGoodNodeSeed (j + 1) (.inner hlt p.1 p.2) S)
        (p := 1 / (P.nFloor (j + 1) : ℝ) ^ 2) hid_le (by positivity) fun idS hinj => ?_).trans_eq
        (by ring)
      let S_id := (S0.image
        (FeistelPerm.idCompressorHead (P.idBits (j + 1)) (P.idCompRightUniv (j + 1)) idS)).map
        (FeistelPerm.bitDomainEquiv hsL).toEmbedding
      have hcard_id : #S_id = #S := (card_map _).trans (card_image_of_injOn hinj)
      refine (NNRat.cast_le.mpr (dens_le_dens fun r hr => ?_)).trans
        (P.dens_routerRound_outside_bounds_le hcr hlt S_id (hcard_id.symm ▸ hlo)
          (hcard_id.symm ▸ hhi))
      simp only [mem_filter, Finset.mem_univ, true_and, IsGoodNodeSeed] at hr ⊢
      exact fun hall => hr ⟨hinj, hall⟩
    · rw [← Fintype.dens_filter_comp_equiv (P.nodeSeedLeafEquiv hlt)]
      refine (NNRat.cast_le.mpr (dens_le_dens fun θ hθ => ?_)).trans
        (hid_le.trans (hle 2 (by norm_num)))
      simpa [IsGoodNodeSeed] using hθ

open scoped Classical in
/-- Under `P.ConcentrationReady`, at least `(1 - 3 / n_ℓ ^ 2) ≥ 11 / 12` of all seeds in
`P.NodeSeed ℓ` satisfy `IsGoodNodeSeed ℓ g S`. -/
theorem card_isGoodNodeSeed_ge (hcr : P.ConcentrationReady) {ℓ : ℕ} (hℓ : ℓ ≤ P.depth)
    (S : Finset (P.PrimId ℓ)) (hlo : P.nLow ℓ ≤ #S) (hhi : #S ≤ P.nHigh ℓ) :
    ((P.nFloor ℓ) ^ 2 - 3) * Fintype.card (P.NodeSeed ℓ) ≤
      (P.nFloor ℓ) ^ 2 * #{g : P.NodeSeed ℓ | P.IsGoodNodeSeed ℓ g S} := by
  have hbad := P.dens_not_isGoodNodeSeed_le hcr hℓ S hlo hhi
  have := P.nFloor_pos ℓ hℓ
  rw [dens_eq_card_div_card, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast,
    div_le_div_iff₀ (Nat.cast_pos.mpr Fintype.card_pos) (by positivity)] at hbad
  have hbad' : #{g : P.NodeSeed ℓ | ¬ P.IsGoodNodeSeed ℓ g S} * (P.nFloor ℓ) ^ 2 ≤
      3 * Fintype.card (P.NodeSeed ℓ) := by exact_mod_cast hbad
  have hpart : (P.nFloor ℓ) ^ 2 * #{g : P.NodeSeed ℓ | P.IsGoodNodeSeed ℓ g S} +
      #{g : P.NodeSeed ℓ | ¬ P.IsGoodNodeSeed ℓ g S} * (P.nFloor ℓ) ^ 2 =
      (P.nFloor ℓ) ^ 2 * Fintype.card (P.NodeSeed ℓ) := by
    rw [Nat.mul_comm _ ((P.nFloor ℓ) ^ 2), ← Nat.mul_add, card_filter_add_card_filter_not,
      card_univ]
  rw [Nat.sub_mul]; omega

open scoped Classical in
private theorem dens_not_isGoodNodeSeed_lt_half (hcr : P.ConcentrationReady) {ℓ : ℕ}
    (hℓ : ℓ ≤ P.depth) (S : Finset (P.PrimId ℓ)) (hlo : P.nLow ℓ ≤ #S) (hhi : #S ≤ P.nHigh ℓ) :
    (dens {g : P.NodeSeed ℓ | ¬ P.IsGoodNodeSeed ℓ g S} : ℝ) < 1 / 2 := by
  have h6 : (6 : ℝ) ≤ P.nFloor ℓ := by exact_mod_cast hcr.six_le_nFloor ℓ hℓ
  refine (P.dens_not_isGoodNodeSeed_le hcr hℓ S hlo hhi).trans_lt ?_
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

/-- Every valid primitive-ID set `S` (`nLow ℓ ≤ #S ≤ nHigh ℓ`) admits at least one good seed
`g : P.NodeSeed ℓ`. -/
theorem exists_isGoodNodeSeed (hcr : P.ConcentrationReady) {ℓ : ℕ} (hℓ : ℓ ≤ P.depth)
    (S : Finset (P.PrimId ℓ)) (hlo : P.nLow ℓ ≤ #S) (hhi : #S ≤ P.nHigh ℓ) :
    ∃ g : P.NodeSeed ℓ, P.IsGoodNodeSeed ℓ g S := by
  classical
  by_contra hno
  have h := P.dens_not_isGoodNodeSeed_lt_half hcr hℓ S hlo hhi
  rw [filter_true_of_mem fun g _ => not_exists.mp hno g, dens_univ, NNRat.cast_one] at h
  norm_num at h

/-- Every pair of valid primitive-ID sets `S₁, S₂` (`nLow ℓ ≤ #Sᵢ ≤ nHigh ℓ`) admits a single
seed `g : P.NodeSeed ℓ` simultaneously satisfying `IsGoodNodeSeed` on both `S₁` and `S₂`. -/
theorem exists_isGoodNodeSeed_pair (hcr : P.ConcentrationReady) {ℓ : ℕ} (hℓ : ℓ ≤ P.depth)
    (S₁ S₂ : Finset (P.PrimId ℓ))
    (hlo₁ : P.nLow ℓ ≤ #S₁) (hhi₁ : #S₁ ≤ P.nHigh ℓ)
    (hlo₂ : P.nLow ℓ ≤ #S₂) (hhi₂ : #S₂ ≤ P.nHigh ℓ) :
    ∃ g : P.NodeSeed ℓ, P.IsGoodNodeSeed ℓ g S₁ ∧ P.IsGoodNodeSeed ℓ g S₂ := by
  classical
  by_contra hno
  have hcov : (Finset.univ : Finset (P.NodeSeed ℓ)) ⊆
      (Finset.univ.filter fun g => ¬ P.IsGoodNodeSeed ℓ g S₁) ∪
        Finset.univ.filter fun g => ¬ P.IsGoodNodeSeed ℓ g S₂ := fun g _ => by
    rw [mem_union, mem_filter, mem_filter]
    exact (not_and_or.mp (not_exists.mp hno g)).imp (⟨mem_univ g, ·⟩) (⟨mem_univ g, ·⟩)
  have h : ((dens (Finset.univ : Finset (P.NodeSeed ℓ)) : ℚ≥0) : ℝ) ≤ _ :=
    NNRat.cast_le.mpr ((dens_le_dens hcov).trans (dens_union_le _ _))
  rw [dens_univ, NNRat.cast_one, NNRat.cast_add] at h
  linarith [P.dens_not_isGoodNodeSeed_lt_half hcr hℓ S₁ hlo₁ hhi₁,
    P.dens_not_isGoodNodeSeed_lt_half hcr hℓ S₂ hlo₂ hhi₂]

end TreeSchedule

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
