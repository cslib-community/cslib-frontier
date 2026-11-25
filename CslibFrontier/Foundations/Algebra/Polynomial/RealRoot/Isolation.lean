/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.RatPoly
public import Mathlib.FieldTheory.Perfect

/-!
# Certified Real-Root Isolation via Sturm Bisection

This module implements executable Sturm-count bisection over `ℚ[X]` (`isolateRoots`), returning
sorted rational isolating intervals `RootInterval`. It proves soundness, completeness, Cauchy
enclosure, root ordering, and an exact strictly monotone bijection with the real roots of any
separable (equivalently squarefree) rational polynomial.

## Main definitions

* `Cslib.RealRoot.RootInterval`: rational interval `[lower, upper]` together with
  `RootInterval.IsIsolatingFor` and `RootInterval.IsHalfOpenIsolatingFor`.
* `Cslib.RealRoot.refineLeftLoop`, `Cslib.RealRoot.refineLeftRoot`,
  `Cslib.RealRoot.isolateIoc`, `Cslib.RealRoot.isolateRoots`: computable Sturm-bisection
  real-root isolator on `List ℚ`.
* `Cslib.RealRoot.isolatedRoot`: subtype map sending each interval index to the unique real root
  inside that interval.
* `Cslib.RealRoot.isolatePolyRoots`, `Cslib.RealRoot.polyIsolatedRoot`: `Polynomial ℚ` wrappers via
  `Polynomial.coeffsBelow`.

## Main results

* `Cslib.RealRoot.isolateRoots_isIsolatingFor`, `Cslib.RealRoot.isolateRoots_pairwise`,
  `Cslib.RealRoot.isolateRoots_complete`, `Cslib.RealRoot.isolateRoots_length_eq_card_roots`,
  `Cslib.RealRoot.isolatedRoot_strictMono`, `Cslib.RealRoot.isolateRoots_bijective`:
  correctness, ordering, completeness, and strictly monotone bijection onto real roots of any
  separable (squarefree) polynomial.
* `Cslib.RealRoot.not_two_roots_of_width_le`: at the Mignotte bisection depth, an interval of
  the dyadic width contains at most one real root.
* `Cslib.RealRoot.polyIsolatedRoot_mem`, `Cslib.RealRoot.polyIsolatedRoot_strictMono`,
  `Cslib.RealRoot.isolatePolyRoots_bijective`: squarefree `Polynomial ℚ` versions.

## References

The `List ℚ` Sturm-bisection isolator `isolateRoots` (which can return touching intervals
`I₁.upper ≤ I₂.lower`) and left-endpoint root refinement are this library's own construction,
built on the Sturm counting and root-separation ingredients below; [BasuPollackRoy2006], §10.2,
Algorithm 10.4 (pp. 373–374, over integer coefficients using Bernstein coefficient variation and
returning open rational intervals and singleton rational roots) is related work.

* [BasuPollackRoy2006], Theorem 2.50, p. 52 (Sturm counting ingredient; adapted to `(a, b]` over
  `ℝ`)
* [Mahler1964], pp. 257–262 (discriminant/Mahler-measure separation ingredient; equation locator
  unverified)
* [Mignotte1982], Theorem 3 (pp. 260–261) and Theorem 5 with integral corollary (p. 262; Landau
  norm comparison and root-separation ingredients)
-/

public section

namespace Cslib.RealRoot

open Polynomial

/-- Closed rational interval `[lower, upper]` representing an isolated real root. -/
structure RootInterval where
  /-- Left rational endpoint of the isolating interval. -/
  lower : ℚ
  /-- Right rational endpoint of the isolating interval. -/
  upper : ℚ
  deriving @[expose] DecidableEq, Repr

/-- Closed-interval root isolation predicate: `I.lower ≤ I.upper` and `[I.lower, I.upper]`
contains a unique real root of `p`. -/
@[expose] def RootInterval.IsIsolatingFor (I : RootInterval) (p : ℝ[X]) : Prop :=
  I.lower ≤ I.upper ∧
    ∃! r : ℝ, (I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) ∧ p.IsRoot r

/-- Half-open-interval root isolation predicate: `I.lower < I.upper` and `(I.lower, I.upper]`
contains a unique real root of `p`. -/
def RootInterval.IsHalfOpenIsolatingFor (I : RootInterval) (p : ℝ[X]) : Prop :=
  I.lower < I.upper ∧
    ∃! r : ℝ, (I.lower : ℝ) < r ∧ r ≤ (I.upper : ℝ) ∧ p.IsRoot r

/-- Inner loop shrinking `(u, v]` away from a root at `u` when `(u, v]` contains a unique root
of `t`. -/
@[expose] def refineLeftLoop (t : List ℚ) (seq : List (List ℚ)) :
    ℕ → ℚ → ℚ → ℕ → RootInterval
  | 0, u, v, _ => { lower := u, upper := v }
  | fuel + 1, u, v, vu =>
    let m := (u + v) / 2
    let vm := sturmVariationsList seq m
    if vm = vu then
      { lower := m, upper := v }
    else if evalCoeffList m t = 0 then
      { lower := m, upper := m }
    else
      refineLeftLoop t seq fuel u m vu

/-- Convert a half-open isolating interval `(u, v]` (`u < v`, `V(u) - V(v) = 1`) into a closed
isolating interval `[a, b] ⊆ [u, v]`, strictly separating `u` when `t` vanishes at `u`. -/
@[expose] def refineLeftRoot (t : List ℚ) (seq : List (List ℚ)) (fuel : ℕ)
    (u v : ℚ) (vu : ℕ) : RootInterval :=
  if evalCoeffList v t = 0 then
    { lower := v, upper := v }
  else if evalCoeffList u t ≠ 0 then
    { lower := u, upper := v }
  else
    refineLeftLoop t seq fuel u v vu

/-- Recursive Sturm-count bisection on `(u, v]` with cached endpoint variation counts `vu` and
`vv`. -/
@[expose] def isolateIoc (t : List ℚ) (seq : List (List ℚ)) (depthBound : ℕ) :
    ℕ → ℚ → ℚ → ℕ → ℕ → List RootInterval
  | fuel, u, v, vu, vv =>
    let count := vu - vv
    if count = 0 then
      []
    else if count = 1 then
      [refineLeftRoot t seq depthBound u v vu]
    else
      match fuel with
      | 0 => []
      | fuel' + 1 =>
        let m := (u + v) / 2
        let vm := sturmVariationsList seq m
        isolateIoc t seq depthBound fuel' u m vu vm ++
          isolateIoc t seq depthBound fuel' m v vm vv

/-- Executable Sturm-count real-root isolator returning sorted isolating rational intervals for
`ofCoeffList cs`. -/
@[expose] def isolateRoots (cs : List ℚ) : List RootInterval :=
  let t := CoeffList.trim cs
  if t.isEmpty then
    []
  else
    let seq := sturmSeqList cs
    let b : ℚ := (cauchyBoundNat cs : ℚ)
    let depth := mignotteBisectionDepth cs
    let vLeft := sturmVariationsList seq (-b)
    let vRight := sturmVariationsList seq b
    isolateIoc t seq depth depth (-b) b vLeft vRight

theorem sturmVariationsList_antitone {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    {u v : ℚ} (huv : u ≤ v) :
    sturmVariationsList (sturmSeqList cs) v ≤ sturmVariationsList (sturmSeqList cs) u := by
  simp only [sturmVariationsList_eq_sturmVariations]
  exact Polynomial.sturmVariations_antitone hsep.map (Rat.cast_le.mpr huv)

theorem eval_rat_eq_zero_iff (cs : List ℚ) (x : ℚ) :
    evalCoeffList x (CoeffList.trim cs) = 0 ↔
      ((ofCoeffList cs).map (algebraMap ℚ ℝ)).eval (x : ℝ) = 0 := by
  rw [← CoeffList.ofCoeffList_trim cs, show (x : ℝ) = algebraMap ℚ ℝ x from rfl,
    Polynomial.eval_map, Polynomial.eval₂_hom, eval_ofCoeffList]
  exact Rat.cast_eq_zero.symm

theorem card_roots_Ioc_eq {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    {u v : ℚ} (huv : u ≤ v) :
    sturmVariationsList (sturmSeqList cs) u - sturmVariationsList (sturmSeqList cs) v =
      (((ofCoeffList cs).map (algebraMap ℚ ℝ)).roots.toFinset.filter
        (fun r : ℝ => (u : ℝ) < r ∧ r ≤ (v : ℝ))).card := by
  rw [sturmVariationsList_eq_sturmVariations, sturmVariationsList_eq_sturmVariations]
  exact sturmVariations_sub_eq_card_roots_Ioc hsep.map (Rat.cast_le.mpr huv)

private theorem exists_two_roots_Ioc_of_two_le {pR : ℝ[X]} (hpR : pR ≠ 0) {u v : ℝ}
    (hcard : 2 ≤ (pR.roots.toFinset.filter (fun r => u < r ∧ r ≤ v)).card) :
    ∃ α β : ℝ, pR.IsRoot α ∧ pR.IsRoot β ∧ u < α ∧ α < β ∧ β ≤ v := by
  obtain ⟨α, hα, β, hβ, hne⟩ := Finset.one_lt_card.mp (Nat.lt_of_lt_of_le one_lt_two hcard)
  simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hpR] at hα hβ
  exact (lt_or_gt_of_ne hne).elim
    (fun hlt => ⟨α, β, hα.1, hβ.1, hα.2.1, hlt, hβ.2.2⟩)
    (fun hgt => ⟨β, α, hβ.1, hα.1, hβ.2.1, hgt, hα.2.2⟩)

theorem natDegree_ge_two_of_two_roots {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    {α β : ℝ} (hα : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot α)
    (hβ : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot β) (hne : α ≠ β) :
    2 ≤ (ofCoeffList cs).natDegree := by
  let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
  have hpR0 : pR ≠ 0 := Polynomial.map_ne_zero hsep.ne_zero
  have hsub : ({α, β} : Finset ℝ) ⊆ pR.roots.toFinset := Finset.insert_subset
    (Multiset.mem_toFinset.mpr ((mem_roots hpR0).mpr hα))
    (Finset.singleton_subset_iff.mpr (Multiset.mem_toFinset.mpr ((mem_roots hpR0).mpr hβ)))
  calc 2 = ({α, β} : Finset ℝ).card := (Finset.card_pair hne).symm
    _ ≤ pR.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ pR.natDegree := (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' pR)
    _ = (ofCoeffList cs).natDegree :=
      Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective _

/-- At the Mignotte bisection depth, an interval `[a, b]` of the dyadic width
`2 * cauchyBoundNat cs / 2 ^ depth` contains no two distinct real roots of a separable
`ofCoeffList cs`. -/
theorem not_two_roots_of_width_le {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    {α β : ℝ} (hα : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot α)
    (hβ : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot β) (hαβ : α < β) {a b : ℚ}
    (haα : (a : ℝ) ≤ α) (hβb : β ≤ (b : ℝ)) {depth : ℕ}
    (hdepth : depth = mignotteBisectionDepth cs)
    (hwidth : (b - a : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ depth) : False := by
  have hsep_w := dyadic_width_lt_root_sep hsep
    (natDegree_ge_two_of_two_roots hsep hα hβ hαβ.ne) hα hβ hαβ.ne
  rw [← hdepth, abs_of_neg (sub_neg.mpr hαβ), neg_sub] at hsep_w
  linarith [show (b : ℝ) - (a : ℝ) = (b - a : ℝ) from rfl]

private theorem mem_roots_filter_iff {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    {u v : ℚ} {r : ℝ} :
    r ∈ ((ofCoeffList cs).map (algebraMap ℚ ℝ)).roots.toFinset.filter
        (fun x : ℝ => (u : ℝ) < x ∧ x ≤ (v : ℝ)) ↔
      (u : ℝ) < r ∧ r ≤ (v : ℝ) ∧ ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot r := by
  simp only [Finset.mem_filter, Multiset.mem_toFinset,
    mem_roots (Polynomial.map_ne_zero hsep.ne_zero)]
  tauto

private theorem unique_root_Ioc_of_card_eq_one {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    {u v : ℚ} (huv : u ≤ v)
    (hcnt : sturmVariationsList (sturmSeqList cs) u -
      sturmVariationsList (sturmSeqList cs) v = 1) :
    ∃! r : ℝ, (u : ℝ) < r ∧ r ≤ (v : ℝ) ∧
      ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot r := by
  rw [card_roots_Ioc_eq hsep huv] at hcnt
  obtain ⟨r₀, hr₀⟩ := Finset.card_eq_one.mp hcnt
  refine ⟨r₀, (mem_roots_filter_iff hsep).mp (hr₀ ▸ Finset.mem_singleton_self r₀), fun r hr => ?_⟩
  exact Finset.mem_singleton.mp (hr₀ ▸ (mem_roots_filter_iff hsep).mpr hr)

theorem no_root_Ioc_of_card_eq_zero {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    {u v : ℚ} (huv : u ≤ v)
    (hcnt : sturmVariationsList (sturmSeqList cs) u -
      sturmVariationsList (sturmSeqList cs) v = 0)
    {r : ℝ} (hur : (u : ℝ) < r) (hrv : r ≤ (v : ℝ)) :
    ¬((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot r := fun hroot => by
  rw [card_roots_Ioc_eq hsep huv, Finset.card_eq_zero] at hcnt
  exact Finset.notMem_empty r (hcnt ▸ (mem_roots_filter_iff hsep).mpr ⟨hur, hrv, hroot⟩)

private theorem dyadic_half_width_le {cs : List ℚ} {u v : ℚ} {depth : ℕ}
    (hw : (v - u : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ depth) :
    (((u + v) / 2 : ℚ) - u : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ (depth + 1) ∧
      ((v : ℝ) - ((u + v) / 2 : ℚ) : ℝ) ≤
        2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ (depth + 1) := by
  have hbound : (v - u : ℝ) / 2 ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ (depth + 1) := by
    rw [pow_succ, ← div_div]; linarith
  exact ⟨by push_cast; linarith, by push_cast; linarith⟩

private theorem singleton_isolating_of_Ioc {pR : ℝ[X]} {u v m : ℚ} (hum : u < m) (hmv : m ≤ v)
    (hm_root : pR.IsRoot (m : ℝ))
    (huniq : ∀ r : ℝ, (u : ℝ) < r → r ≤ (v : ℝ) → pR.IsRoot r → r = (m : ℝ)) :
    ({ lower := m, upper := m } : RootInterval).IsIsolatingFor pR ∧
      ∀ r : ℝ, ((m : ℝ) ≤ r ∧ r ≤ (m : ℝ) ∧ pR.IsRoot r) ↔
        ((u : ℝ) < r ∧ r ≤ (v : ℝ) ∧ pR.IsRoot r) :=
  ⟨⟨le_rfl, m, ⟨le_rfl, le_rfl, hm_root⟩, fun _ ⟨h1, h2, _⟩ => le_antisymm h2 h1⟩, fun r =>
    ⟨fun ⟨h1, h2, _⟩ => by
        rw [le_antisymm h2 h1]
        exact ⟨Rat.cast_lt.mpr hum, Rat.cast_le.mpr hmv, hm_root⟩,
      fun ⟨hur, hrv, hrr⟩ => by rw [huniq r hur hrv hrr]; exact ⟨le_rfl, le_rfl, hm_root⟩⟩⟩

private theorem closed_isolating_of_Ioc_not_left {pR : ℝ[X]} {u v : ℚ} (huv : u ≤ v)
    (hu_not : ¬pR.IsRoot (u : ℝ))
    (huniq : ∃! r : ℝ, (u : ℝ) < r ∧ r ≤ (v : ℝ) ∧ pR.IsRoot r) :
    ({ lower := u, upper := v } : RootInterval).IsIsolatingFor pR ∧
      ∀ r : ℝ, ((u : ℝ) ≤ r ∧ r ≤ (v : ℝ) ∧ pR.IsRoot r) ↔
        ((u : ℝ) < r ∧ r ≤ (v : ℝ) ∧ pR.IsRoot r) := by
  have heq (r : ℝ) : ((u : ℝ) ≤ r ∧ r ≤ (v : ℝ) ∧ pR.IsRoot r) ↔
      ((u : ℝ) < r ∧ r ≤ (v : ℝ) ∧ pR.IsRoot r) :=
    ⟨fun ⟨hur, hrv, hrr⟩ => ⟨lt_of_le_of_ne hur fun h => hu_not (h ▸ hrr), hrv, hrr⟩,
      fun ⟨hur, hrv, hrr⟩ => ⟨hur.le, hrv, hrr⟩⟩
  obtain ⟨r₀, ⟨hur₀, hr₀v, hr₀⟩, hr₀_uniq⟩ := huniq
  exact ⟨⟨huv, r₀, ⟨hur₀.le, hr₀v, hr₀⟩, fun r hr => hr₀_uniq r ((heq r).mp hr)⟩, heq⟩

private theorem refineLeftLoop_spec {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    ∀ (fuel depth : ℕ) (u v : ℚ) (vu vv : ℕ),
      depth + fuel = mignotteBisectionDepth cs →
      u < v →
      vu = sturmVariationsList (sturmSeqList cs) u →
      vv = sturmVariationsList (sturmSeqList cs) v →
      vu - vv = 1 →
      evalCoeffList u (CoeffList.trim cs) = 0 →
      (v - u : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ depth →
      let I := refineLeftLoop (CoeffList.trim cs) (sturmSeqList cs) fuel u v vu
      let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
      I.IsIsolatingFor pR ∧ u < I.lower ∧ I.upper ≤ v ∧
        ∀ r : ℝ, ((I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) ∧ pR.IsRoot r) ↔
          ((u : ℝ) < r ∧ r ≤ (v : ℝ) ∧ pR.IsRoot r)
  | 0, depth, u, v, _, _, hsum, huv, hvu, hvv, hcnt, hu_root, hwidth => by
    obtain ⟨r, ⟨hur, hrv, hr_root⟩, _⟩ :=
      unique_root_Ioc_of_card_eq_one hsep huv.le (hvu ▸ hvv ▸ hcnt)
    exact (not_two_roots_of_width_le hsep ((eval_rat_eq_zero_iff cs u).mp hu_root) hr_root
      hur le_rfl hrv (by omega) hwidth).elim
  | fuel + 1, depth, u, v, vu, vv, hsum, huv, hvu, hvv, hcnt, hu_root, hwidth => by
    let m := (u + v) / 2
    let vm := sturmVariationsList (sturmSeqList cs) m
    have hum : u < m := by dsimp only [m]; linarith
    have hmv : m < v := by dsimp only [m]; linarith
    have hleL : vm ≤ vu := hvu ▸ sturmVariationsList_antitone hsep hum.le
    have hleR : vv ≤ vm := hvv ▸ sturmVariationsList_antitone hsep hmv.le
    simp only [refineLeftLoop]
    by_cases hvm_eq : vm = vu
    · rw [ite_eq_left hvm_eq]
      have hcntL : sturmVariationsList (sturmSeqList cs) u - vm = 0 := by rw [← hvu]; omega
      have hcntR : vm - sturmVariationsList (sturmSeqList cs) v = 1 := by rw [← hvv]; omega
      have hnoL {r : ℝ} := no_root_Ioc_of_card_eq_zero hsep hum.le hcntL (r := r)
      obtain ⟨hiso, heq_mv⟩ := closed_isolating_of_Ioc_not_left hmv.le
        (hnoL (Rat.cast_lt.mpr hum) le_rfl) (unique_root_Ioc_of_card_eq_one hsep hmv.le hcntR)
      refine ⟨hiso, hum, le_rfl, fun r => (heq_mv r).trans ⟨fun ⟨hmr, hrv, hrr⟩ =>
        ⟨(Rat.cast_lt.mpr hum).trans hmr, hrv, hrr⟩, fun ⟨hur, hrv, hrr⟩ =>
        ⟨lt_of_not_ge fun hrm => hnoL hur hrm hrr, hrv, hrr⟩⟩⟩
    · rw [ite_eq_right hvm_eq]
      have hcntL : sturmVariationsList (sturmSeqList cs) u - vm = 1 := by
        rw [← hvu]; omega
      have hcntR : vm - sturmVariationsList (sturmSeqList cs) v = 0 := by rw [← hvv]; omega
      have hle_m : ∀ {r : ℝ}, r ≤ v →
          ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot r → r ≤ m := fun hrv hrr =>
        le_of_not_gt fun hmr => no_root_Ioc_of_card_eq_zero hsep hmv.le hcntR hmr hrv hrr
      by_cases hem : evalCoeffList m (CoeffList.trim cs) = 0
      · rw [ite_eq_left hem]
        have hm_root : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot (m : ℝ) :=
          (eval_rat_eq_zero_iff cs m).mp hem
        obtain ⟨_, _, hr₀_uniq⟩ := unique_root_Ioc_of_card_eq_one hsep hum.le hcntL
        obtain ⟨hiso, hequiv⟩ := singleton_isolating_of_Ioc hum hmv.le hm_root fun r hur hrv hrr =>
          (hr₀_uniq r ⟨hur, hle_m hrv hrr, hrr⟩).trans
            (hr₀_uniq m ⟨Rat.cast_lt.mpr hum, le_rfl, hm_root⟩).symm
        exact ⟨hiso, hum, hmv.le, hequiv⟩
      · rw [ite_eq_right hem]
        obtain ⟨ih_iso, ih_low, ih_up, ih_eq⟩ := refineLeftLoop_spec hsep fuel (depth + 1)
          u m vu vm (by omega) hum hvu rfl (by omega) hu_root (dyadic_half_width_le hwidth).1
        exact ⟨ih_iso, ih_low, ih_up.trans hmv.le, fun r => (ih_eq r).trans
          ⟨fun ⟨hur, hrm, hrr⟩ => ⟨hur, hrm.trans (Rat.cast_le.mpr hmv.le), hrr⟩,
            fun ⟨hur, hrv, hrr⟩ => ⟨hur, hle_m hrv hrr, hrr⟩⟩⟩

private theorem refineLeftRoot_spec {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    {u v : ℚ} (huv : u < v) {vu vv : ℕ}
    (hvu : vu = sturmVariationsList (sturmSeqList cs) u)
    (hvv : vv = sturmVariationsList (sturmSeqList cs) v)
    (hcnt : vu - vv = 1)
    (hwidth : (v - u : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ)) :
    let I := refineLeftRoot (CoeffList.trim cs) (sturmSeqList cs)
      (mignotteBisectionDepth cs) u v vu
    let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
    I.IsIsolatingFor pR ∧ u ≤ I.lower ∧ I.upper ≤ v ∧
      (evalCoeffList u (CoeffList.trim cs) = 0 → u < I.lower) ∧
      ∀ r : ℝ, ((I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) ∧ pR.IsRoot r) ↔
        ((u : ℝ) < r ∧ r ≤ (v : ℝ) ∧ pR.IsRoot r) := by
  have huniq := unique_root_Ioc_of_card_eq_one hsep huv.le (hvu ▸ hvv ▸ hcnt)
  simp only [refineLeftRoot]
  split_ifs with hev heu
  · have hv_root := (eval_rat_eq_zero_iff cs v).mp hev
    obtain ⟨hiso, hequiv⟩ := singleton_isolating_of_Ioc huv le_rfl hv_root fun r hur hrv hrr =>
      huniq.unique ⟨hur, hrv, hrr⟩ ⟨Rat.cast_lt.mpr huv, le_rfl, hv_root⟩
    exact ⟨hiso, huv.le, le_rfl, fun _ => huv, hequiv⟩
  · obtain ⟨hiso, hequiv⟩ := closed_isolating_of_Ioc_not_left huv.le
      (fun h => heu ((eval_rat_eq_zero_iff cs u).mpr h)) huniq
    exact ⟨hiso, le_rfl, le_rfl, fun h0 => absurd h0 heu, hequiv⟩
  · obtain ⟨hiso, hlow, hup, hequiv⟩ := refineLeftLoop_spec hsep (mignotteBisectionDepth cs) 0
      u v vu vv (Nat.zero_add _) huv hvu hvv hcnt (not_not.mp heu)
      (by simpa only [pow_zero, div_one] using hwidth)
    exact ⟨hiso, hlow.le, hup, fun _ => hlow, hequiv⟩

/-- Separation invariant between consecutive isolating intervals: either `I₁.upper < I₂.lower`, or
`I₁.upper = I₂.lower` and that shared rational boundary point is not a root of `p`. -/
@[expose] def IntervalGapOk (p : ℝ[X]) (I₁ I₂ : RootInterval) : Prop :=
  I₁.upper < I₂.lower ∨ (I₁.upper = I₂.lower ∧ p.eval (I₁.upper : ℝ) ≠ 0)

private theorem intervalGapOk_of_mid {p : ℝ[X]} {m : ℚ} {I₁ I₂ : RootInterval}
    (h1 : I₁.upper ≤ m) (h2 : m ≤ I₂.lower) (hstrict : p.eval (m : ℝ) = 0 → m < I₂.lower) :
    IntervalGapOk p I₁ I₂ := by
  rcases lt_or_eq_of_le h1 with h1lt | rfl
  · exact Or.inl (lt_of_lt_of_le h1lt h2)
  · exact (lt_or_eq_of_le h2).imp id fun h2eq => ⟨h2eq, fun hm0 => (hstrict hm0).ne h2eq⟩

private theorem IntervalGapOk.lt_of_le {p : ℝ[X]} {I₁ I₂ : RootInterval}
    (hgap : IntervalGapOk p I₁ I₂) {r₁ r₂ : ℝ} (h1 : r₁ ≤ (I₁.upper : ℝ))
    (h2 : (I₂.lower : ℝ) ≤ r₂) (hr₁ : p.IsRoot r₁) : r₁ < r₂ := by
  rcases hgap with hlt | ⟨heq, hnot0⟩
  · exact lt_of_le_of_lt h1 (lt_of_lt_of_le (Rat.cast_lt.mpr hlt) h2)
  · have hcast : (I₁.upper : ℝ) = (I₂.lower : ℝ) := congrArg Rat.cast heq
    refine lt_of_le_of_ne (h1.trans (hcast.trans_le h2)) fun hreq => hnot0 ?_
    have : (I₁.upper : ℝ) = r₁ := le_antisymm (hcast.trans_le (hreq ▸ h2)) h1
    exact this ▸ hr₁.eq_zero

private def IocSpec (cs : List ℚ) (u v : ℚ) (cnt : ℕ) (L : List RootInterval) : Prop :=
  let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
  (∀ I ∈ L, I.IsIsolatingFor pR ∧ u ≤ I.lower ∧ I.upper ≤ v ∧
      (evalCoeffList u (CoeffList.trim cs) = 0 → u < I.lower)) ∧
    L.Pairwise (IntervalGapOk pR) ∧
    L.length = cnt ∧
    (∀ I ∈ L, ∀ r : ℝ, ((I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) ∧ pR.IsRoot r) →
      (u : ℝ) < r ∧ r ≤ (v : ℝ)) ∧
    (∀ r : ℝ, ((u : ℝ) < r ∧ r ≤ (v : ℝ) ∧ pR.IsRoot r) →
      ∃ I ∈ L, (I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ))

private theorem iocSpec_append {cs : List ℚ} {u m v : ℚ} (hum : u < m) (hmv : m ≤ v)
    {c₁ c₂ : ℕ} {L₁ L₂ : List RootInterval}
    (hL : IocSpec cs u m c₁ L₁) (hR : IocSpec cs m v c₂ L₂) :
    IocSpec cs u v (c₁ + c₂) (L₁ ++ L₂) := by
  refine ⟨fun I hI => (List.mem_append.mp hI).elim
    (fun h => let ⟨hi, hl, hu, hs⟩ := hL.1 I h; ⟨hi, hl, hu.trans hmv, hs⟩)
    (fun h => let ⟨hi, hl, hu, _⟩ := hR.1 I h
      ⟨hi, hum.le.trans hl, hu, fun _ => lt_of_lt_of_le hum hl⟩),
    List.pairwise_append.mpr ⟨hL.2.1, hR.2.1, fun I₁ hI₁ I₂ hI₂ =>
      intervalGapOk_of_mid (hL.1 I₁ hI₁).2.2.1 (hR.1 I₂ hI₂).2.1 fun hm0 =>
        (hR.1 I₂ hI₂).2.2.2 ((eval_rat_eq_zero_iff cs m).mpr hm0)⟩,
    by rw [List.length_append, hL.2.2.1, hR.2.2.1],
    fun I hI r hr => (List.mem_append.mp hI).elim
      (fun h => let ⟨hur, hrm⟩ := hL.2.2.2.1 I h r hr; ⟨hur, hrm.trans (Rat.cast_le.mpr hmv)⟩)
      (fun h => let ⟨hmr, hrv⟩ := hR.2.2.2.1 I h r hr
        ⟨lt_of_le_of_lt (Rat.cast_le.mpr hum.le) hmr, hrv⟩),
    fun r ⟨hur, hrv, hrr⟩ => (le_or_gt r m).elim
      (fun hrm => let ⟨I, hIL, hl, hu⟩ := hL.2.2.2.2 r ⟨hur, hrm, hrr⟩
        ⟨I, List.mem_append_left _ hIL, hl, hu⟩)
      (fun hmr => let ⟨I, hIR, hl, hu⟩ := hR.2.2.2.2 r ⟨hmr, hrv, hrr⟩
        ⟨I, List.mem_append_right _ hIR, hl, hu⟩)⟩

private theorem isolateIoc_spec {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    ∀ (fuel depth : ℕ) (u v : ℚ) (vu vv : ℕ),
      depth + fuel = mignotteBisectionDepth cs →
      u ≤ v →
      vu = sturmVariationsList (sturmSeqList cs) u →
      vv = sturmVariationsList (sturmSeqList cs) v →
      (v - u : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ depth →
      IocSpec cs u v (vu - vv)
        (isolateIoc (CoeffList.trim cs) (sturmSeqList cs)
          (mignotteBisectionDepth cs) fuel u v vu vv)
  | fuel, depth, u, v, vu, vv, hsum, huv, hvu, hvv, hwidth => by
    have hvu_ge : vv ≤ vu := hvu ▸ hvv ▸ sturmVariationsList_antitone hsep huv
    unfold isolateIoc; dsimp only
    split_ifs with hc0 hc1
    · exact ⟨fun _ h => (nomatch h), List.Pairwise.nil, by rw [hc0, List.length_nil],
        fun _ h => (nomatch h), fun _ ⟨hur, hrv, hrr⟩ =>
          (no_root_Ioc_of_card_eq_zero hsep huv (hvu ▸ hvv ▸ hc0) hur hrv hrr).elim⟩
    · have huv_lt : u < v := lt_of_le_of_ne huv fun h => by subst h; omega
      have hwidth0 : (v - u : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) := hwidth.trans
        (div_le_self (by positivity) (by exact_mod_cast Nat.one_le_pow depth 2 (by omega)))
      obtain ⟨hiso, hlow, hup, hstrict, hequiv⟩ :=
        refineLeftRoot_spec hsep huv_lt hvu hvv hc1 hwidth0
      exact ⟨List.forall_mem_singleton.mpr ⟨hiso, hlow, hup, hstrict⟩,
        List.pairwise_singleton _ _, by rw [List.length_singleton, hc1],
        List.forall_mem_singleton.mpr fun r hr => ((hequiv r).mp hr).imp_right And.left,
        fun r hr => ⟨_, List.mem_singleton_self _, ((hequiv r).mpr hr).imp_right And.left⟩⟩
    · cases fuel with
      | zero =>
        exfalso
        have hcard : 2 ≤ (((ofCoeffList cs).map (algebraMap ℚ ℝ)).roots.toFinset.filter
            (fun r => (u : ℝ) < r ∧ r ≤ (v : ℝ))).card := by
          rw [← card_roots_Ioc_eq hsep huv, ← hvu, ← hvv]; omega
        obtain ⟨_, _, hα, hβ, huα, hαβ, hβv⟩ := exists_two_roots_Ioc_of_two_le
          (Polynomial.map_ne_zero hsep.ne_zero) hcard
        exact not_two_roots_of_width_le hsep hα hβ hαβ huα.le hβv (by omega) hwidth
      | succ fuel' =>
        let m := (u + v) / 2
        let vm := sturmVariationsList (sturmSeqList cs) m
        have huv_lt : u < v := lt_of_le_of_ne huv fun h => by subst h; omega
        have hum : u < m := by dsimp only [m]; linarith
        have hmv : m ≤ v := by dsimp only [m]; linarith
        have hvm_le : vm ≤ vu := hvu ▸ sturmVariationsList_antitone hsep hum.le
        have hvv_le : vv ≤ vm := hvv ▸ sturmVariationsList_antitone hsep hmv
        have ⟨hwL, hwR⟩ := dyadic_half_width_le hwidth
        have hspec := iocSpec_append hum hmv
          (isolateIoc_spec hsep fuel' (depth + 1) u m vu vm (by omega) hum.le hvu rfl hwL)
          (isolateIoc_spec hsep fuel' (depth + 1) m v vm vv (by omega) hmv rfl hvv hwR)
        rwa [show (vu - vm) + (vm - vv) = vu - vv by omega] at hspec

private theorem isEmpty_trim_false {cs : List ℚ} (h0 : ofCoeffList cs ≠ 0) :
    (CoeffList.trim cs).isEmpty = false :=
  List.isEmpty_eq_false_iff.mpr (mt (CoeffList.trim_eq_nil_iff cs).mp h0)

private theorem isRoot_mem_cauchyIoc {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) {r : ℝ}
    (hr : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot r) :
    ((-(cauchyBoundNat cs : ℚ) : ℚ) : ℝ) < r ∧ r ≤ ((cauchyBoundNat cs : ℚ) : ℝ) := by
  have hcb := abs_lt.mp (abs_lt_cauchyBoundNat_of_isRoot hsep.ne_zero hr)
  push_cast
  exact ⟨hcb.1, hcb.2.le⟩

private theorem isolateRoots_spec_aux {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    let b : ℚ := (cauchyBoundNat cs : ℚ)
    let seq := sturmSeqList cs
    let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
    (∀ I ∈ isolateRoots cs, I.IsIsolatingFor pR ∧ -b ≤ I.lower ∧ I.upper ≤ b) ∧
      (isolateRoots cs).Pairwise (IntervalGapOk pR) ∧
      (isolateRoots cs).length =
        sturmVariationsList seq (-b) - sturmVariationsList seq b ∧
      ∀ r : ℝ, (((-b : ℚ) : ℝ) < r ∧ r ≤ (b : ℝ) ∧ pR.IsRoot r) →
        ∃ I ∈ isolateRoots cs, (I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) := by
  let b : ℚ := (cauchyBoundNat cs : ℚ)
  have hspec := isolateIoc_spec hsep (mignotteBisectionDepth cs) 0 (-b) b _ _
    (Nat.zero_add _) (by have : (0 : ℚ) ≤ b := Nat.cast_nonneg _; linarith) rfl rfl
    (by simp [b, two_mul])
  have heq : isolateRoots cs =
      isolateIoc (CoeffList.trim cs) (sturmSeqList cs) (mignotteBisectionDepth cs)
        (mignotteBisectionDepth cs) (-b) b (sturmVariationsList (sturmSeqList cs) (-b))
        (sturmVariationsList (sturmSeqList cs) b) := by
    simp only [isolateRoots, isEmpty_trim_false hsep.ne_zero, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [heq]
  exact ⟨fun I hI => ⟨(hspec.1 I hI).1, (hspec.1 I hI).2.1, (hspec.1 I hI).2.2.1⟩,
    hspec.2.1, hspec.2.2.1, hspec.2.2.2.2⟩

/-- Soundness: every rational interval returned by `isolateRoots cs` isolates a unique real root
of `(ofCoeffList cs).map (algebraMap ℚ ℝ)`. -/
theorem isolateRoots_isIsolatingFor {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    ∀ I ∈ isolateRoots cs, I.IsIsolatingFor ((ofCoeffList cs).map (algebraMap ℚ ℝ)) :=
  fun I hI => ((isolateRoots_spec_aux hsep).1 I hI).1

/-- Cauchy enclosure: every interval returned by `isolateRoots cs` lies within
`[-cauchyBoundNat cs, cauchyBoundNat cs]`. -/
theorem isolateRoots_mem_cauchy {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    ∀ I ∈ isolateRoots cs,
      -(cauchyBoundNat cs : ℚ) ≤ I.lower ∧ I.upper ≤ (cauchyBoundNat cs : ℚ) :=
  fun I hI => ((isolateRoots_spec_aux hsep).1 I hI).2

/-- Ordering: consecutive intervals returned by `isolateRoots cs` satisfy `I₁.upper ≤ I₂.lower`. -/
theorem isolateRoots_pairwise {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    (isolateRoots cs).Pairwise (fun I₁ I₂ => I₁.upper ≤ I₂.lower) :=
  (isolateRoots_spec_aux hsep).2.1.imp fun hgap => hgap.elim le_of_lt (fun h => h.1.le)

/-- Pairwise boundary-gap invariant `IntervalGapOk` across `isolateRoots cs`. -/
theorem isolateRoots_intervalGapOk {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    (isolateRoots cs).Pairwise (IntervalGapOk ((ofCoeffList cs).map (algebraMap ℚ ℝ))) :=
  (isolateRoots_spec_aux hsep).2.1

/-- Completeness: every real root of `(ofCoeffList cs).map (algebraMap ℚ ℝ)` belongs to at least
one isolating interval in `isolateRoots cs`, and that interval is unique in the list. -/
theorem isolateRoots_complete {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) {r : ℝ}
    (hr : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot r) :
    ∃! i : Fin (isolateRoots cs).length,
      let I := (isolateRoots cs)[i]
      (I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) := by
  have ⟨hmemL, hmemR⟩ := isRoot_mem_cauchyIoc hsep hr
  obtain ⟨I, hI_mem, hlow, hup⟩ := (isolateRoots_spec_aux hsep).2.2.2 r ⟨hmemL, hmemR, hr⟩
  obtain ⟨k, hk_lt, hk_eq⟩ := List.mem_iff_getElem.mp hI_mem
  have hpw := List.pairwise_iff_getElem.mp (isolateRoots_intervalGapOk hsep)
  refine ⟨⟨k, hk_lt⟩, by dsimp only; rw [Fin.getElem_fin, hk_eq]; exact ⟨hlow, hup⟩,
    fun j ⟨hj_low, hj_up⟩ => by_contra fun hne => ?_⟩
  rw [Fin.getElem_fin] at hj_low hj_up
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · exact (hpw j.1 k j.2 hk_lt hlt).lt_of_le hj_up (by rw [hk_eq]; exact hlow) hr |>.false
  · exact (hpw k j.1 hk_lt j.2 hlt).lt_of_le (by rw [hk_eq]; exact hup) hj_low hr |>.false

/-- The number of isolating intervals returned by `isolateRoots cs` equals the number of real
roots of `(ofCoeffList cs).map (algebraMap ℚ ℝ)`. -/
theorem isolateRoots_length_eq_card_roots {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    (isolateRoots cs).length =
      ((ofCoeffList cs).map (algebraMap ℚ ℝ)).roots.toFinset.card := by
  let b : ℚ := (cauchyBoundNat cs : ℚ)
  rw [(isolateRoots_spec_aux hsep).2.2.1,
    card_roots_Ioc_eq hsep (by have : (0 : ℚ) ≤ b := Nat.cast_nonneg _; linarith)]
  congr 1; ext r
  simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots', and_iff_left_iff_imp]
  exact fun hr => isRoot_mem_cauchyIoc hsep hr.2

/-- The unique real root inside the `i`-th isolating interval of `isolateRoots cs`. -/
noncomputable def isolatedRoot {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    (i : Fin (isolateRoots cs).length) :
    {r : ℝ // ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot r} :=
  let I := (isolateRoots cs)[i]
  let hex := (isolateRoots_isIsolatingFor hsep I (List.getElem_mem i.2)).2.exists
  ⟨Classical.choose hex, let ⟨_, _, hroot⟩ := Classical.choose_spec hex; hroot⟩

/-- Membership of `isolatedRoot hsep i` in the `i`-th isolating interval of `isolateRoots cs`. -/
theorem isolatedRoot_mem {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    (i : Fin (isolateRoots cs).length) :
    let I := (isolateRoots cs)[i]
    let r := (isolatedRoot hsep i).1
    (I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) :=
  let hex := (isolateRoots_isIsolatingFor hsep (isolateRoots cs)[i] (List.getElem_mem i.2)).2.exists
  ⟨(Classical.choose_spec hex).1, (Classical.choose_spec hex).2.1⟩

/-- The isolated real roots are strictly increasing across `Fin (isolateRoots cs).length`. -/
theorem isolatedRoot_strictMono {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    StrictMono (fun i : Fin (isolateRoots cs).length => (isolatedRoot hsep i).1) := fun i j hij =>
  (List.pairwise_iff_getElem.mp (isolateRoots_intervalGapOk hsep) i.1 j.1 i.2 j.2 hij).lt_of_le
    (isolatedRoot_mem hsep i).2 (isolatedRoot_mem hsep j).1 (isolatedRoot hsep i).2

/-- Exact bijection between isolating interval indices `Fin (isolateRoots cs).length` and the set
of real roots `{r : ℝ // ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot r}`. -/
theorem isolateRoots_bijective {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    Function.Bijective (isolatedRoot hsep) :=
  ⟨fun _ _ h => (isolatedRoot_strictMono hsep).injective (congrArg Subtype.val h),
    fun ⟨r, hr⟩ => by
      obtain ⟨i, hi_mem, _⟩ := isolateRoots_complete hsep hr
      have huniq := (isolateRoots_isIsolatingFor hsep _ (List.getElem_mem i.2)).2
      exact ⟨i, Subtype.ext (huniq.unique
        ⟨(isolatedRoot_mem hsep i).1, (isolatedRoot_mem hsep i).2, (isolatedRoot hsep i).2⟩
        ⟨hi_mem.1, hi_mem.2, hr⟩)⟩⟩

theorem sturmVariationsList_cauchy_sub_le {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    sturmVariationsList (sturmSeqList cs) (-(cauchyBoundNat cs : ℚ)) -
      sturmVariationsList (sturmSeqList cs) (cauchyBoundNat cs : ℚ) ≤
      (ofCoeffList cs).natDegree := by
  have hb0 : (0 : ℚ) ≤ cauchyBoundNat cs := Nat.cast_nonneg _
  rw [card_roots_Ioc_eq hsep (by linarith)]
  exact ((Finset.card_filter_le _ _).trans (Multiset.toFinset_card_le _)).trans
    ((Polynomial.card_roots' _).trans_eq
      (Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective _))

/-- Soundness for squarefree `ofCoeffList cs`: every interval in `isolateRoots cs` isolates a
unique real root. -/
theorem isolateRoots_isIsolatingFor_of_squarefree {cs : List ℚ}
    (hsq : Squarefree (ofCoeffList cs)) :
    ∀ I ∈ isolateRoots cs, I.IsIsolatingFor ((ofCoeffList cs).map (algebraMap ℚ ℝ)) :=
  isolateRoots_isIsolatingFor (PerfectField.separable_iff_squarefree.mpr hsq)

/-- Bijection onto real roots for squarefree `ofCoeffList cs`. -/
theorem isolateRoots_bijective_of_squarefree {cs : List ℚ}
    (hsq : Squarefree (ofCoeffList cs)) :
    Function.Bijective (isolatedRoot (PerfectField.separable_iff_squarefree.mpr hsq)) :=
  isolateRoots_bijective (PerfectField.separable_iff_squarefree.mpr hsq)

/-- Real-root isolation for an arbitrary polynomial `p : ℚ[X]` via `Polynomial.coeffsBelow`. -/
noncomputable def isolatePolyRoots (p : ℚ[X]) : List RootInterval :=
  isolateRoots (p.coeffsBelow (p.natDegree + 1))

theorem isolatePolyRoots_eq (p : ℚ[X]) :
    isolatePolyRoots p = isolateRoots (p.coeffsBelow (p.natDegree + 1)) := by rfl

/-- Soundness for `isolatePolyRoots p` on squarefree `p : ℚ[X]`. -/
theorem isolatePolyRoots_isIsolatingFor {p : ℚ[X]} (hsq : Squarefree p) :
    ∀ I ∈ isolatePolyRoots p, I.IsIsolatingFor (p.map (algebraMap ℚ ℝ)) := by
  have heq := Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)
  exact fun I hI => by
    rw [← heq]
    exact isolateRoots_isIsolatingFor_of_squarefree (heq.symm ▸ hsq) I hI

/-- Ordering: consecutive intervals in `isolatePolyRoots p` satisfy `I₁.upper ≤ I₂.lower`. -/
theorem isolatePolyRoots_pairwise {p : ℚ[X]} (hsq : Squarefree p) :
    (isolatePolyRoots p).Pairwise (fun I₁ I₂ => I₁.upper ≤ I₂.lower) :=
  isolateRoots_pairwise (PerfectField.separable_iff_squarefree.mpr
    ((Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)).symm ▸ hsq))

theorem polySeparable {p : ℚ[X]} (hsq : Squarefree p) :
    (ofCoeffList (p.coeffsBelow (p.natDegree + 1))).Separable :=
  PerfectField.separable_iff_squarefree.mpr
    ((Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)).symm ▸ hsq)

/-- The unique real root of `p.map (algebraMap ℚ ℝ)` inside the `i`-th isolating interval of
`isolatePolyRoots p`. -/
noncomputable def polyIsolatedRoot {p : ℚ[X]} (hsq : Squarefree p)
    (i : Fin (isolatePolyRoots p).length) :
    {r : ℝ // (p.map (algebraMap ℚ ℝ)).IsRoot r} :=
  let r := (isolatedRoot (polySeparable hsq) i).1
  ⟨r, (congrArg (fun q : ℚ[X] => (q.map (algebraMap ℚ ℝ)).IsRoot r)
      (Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree))).mp
      (isolatedRoot (polySeparable hsq) i).2⟩

/-- Membership of `polyIsolatedRoot hsq i` in the `i`-th isolating interval of
`isolatePolyRoots p`. -/
theorem polyIsolatedRoot_mem {p : ℚ[X]} (hsq : Squarefree p)
    (i : Fin (isolatePolyRoots p).length) :
    let I := (isolatePolyRoots p)[i]
    let r := (polyIsolatedRoot hsq i).1
    (I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) :=
  isolatedRoot_mem (polySeparable hsq) i

/-- The isolated real roots of `p.map (algebraMap ℚ ℝ)` are strictly increasing across
`Fin (isolatePolyRoots p).length`. -/
theorem polyIsolatedRoot_strictMono {p : ℚ[X]} (hsq : Squarefree p) :
    StrictMono (fun i : Fin (isolatePolyRoots p).length => (polyIsolatedRoot hsq i).1) :=
  isolatedRoot_strictMono (polySeparable hsq)

/-- For any squarefree `p : ℚ[X]`, `polyIsolatedRoot hsq` is a bijection from
`Fin (isolatePolyRoots p).length` onto the real roots of `p.map (algebraMap ℚ ℝ)`. -/
theorem isolatePolyRoots_bijective {p : ℚ[X]} (hsq : Squarefree p) :
    Function.Bijective (polyIsolatedRoot hsq) := by
  have hbij := isolateRoots_bijective (polySeparable hsq)
  exact ⟨fun _ _ hij => hbij.1 (Subtype.ext (congrArg Subtype.val hij : _)), fun ⟨r, hr⟩ =>
    let ⟨i, hi⟩ := hbij.2 ⟨r,
      (Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)).symm ▸ hr⟩
    ⟨i, Subtype.ext (show (polyIsolatedRoot hsq i).1 = r from congrArg Subtype.val hi)⟩⟩

end Cslib.RealRoot
