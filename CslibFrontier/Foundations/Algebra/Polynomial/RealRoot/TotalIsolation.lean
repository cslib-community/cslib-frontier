/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.BitBounds

/-!
# Certified Real-Root Isolation with Disjoint Closed Isolating Intervals

This module refines the Sturm-bisection isolator `isolateRoots` into `isolateRootsTotal` (together
with the `Polynomial ℚ` wrapper `isolatePolyRootsTotal`), separating any adjacent isolating
intervals that share a non-root midpoint (`separateTouching`) so that consecutive intervals satisfy
strict separation `J₁.upper < J₂.lower` and define pairwise disjoint closed real intervals
`Set.Icc (J.lower : ℝ) (J.upper : ℝ)`.

For every squarefree `p : ℚ[X]` (represented computably by any `cs : List ℚ` with
`ofCoeffList cs = p`, or via `isolatePolyRootsTotal p`), the returned intervals are in strictly
monotone bijection with `{x : ℝ // Polynomial.aeval x p = 0}`, and every endpoint satisfies
explicit polynomial dyadic numerator and denominator bit bounds under `HasCoeffBitBound B cs`.

## Main definitions

* `Cslib.RealRoot.separateMidLoop`, `Cslib.RealRoot.separatePair`, `Cslib.RealRoot.separateChain`,
  `Cslib.RealRoot.separateTouching`: computable boundary separation producing strictly disjoint
  closed intervals (`J₁.upper < J₂.lower`).
* `Cslib.RealRoot.isolateRootsTotal`, `Cslib.RealRoot.totalIsolatedRoot`: computable real-root
  isolator returning pairwise disjoint closed intervals and root bijection on `List ℚ`.
* `Cslib.RealRoot.isolatePolyRootsTotal`, `Cslib.RealRoot.polyTotalIsolatedRoot`: `Polynomial ℚ`
  wrappers.

## Main results

* `Cslib.RealRoot.isolateRootsTotal_isIsolatingFor`,
  `Cslib.RealRoot.isolateRootsTotal_pairwise_lt`,
  `Cslib.RealRoot.isolateRootsTotal_pairwise_disjoint`,
  `Cslib.RealRoot.isolateRootsTotal_bijective`,
  `Cslib.RealRoot.isolateRootsTotal_bijective_of_squarefree`: soundness, strict separation,
  closed-interval disjointness, and strictly monotone bijection onto
  `{x : ℝ // Polynomial.aeval x p = 0}`.
* `Cslib.RealRoot.isolateRootsTotal_endpoint_bounds`,
  `Cslib.RealRoot.isolateRootsTotal_endpoint_bounds_of_bitBound`: dyadic numerator and denominator
  bounds on all returned endpoints.
* `Cslib.RealRoot.isolateRootsTotal_spec_of_eq`: combined specification on `List ℚ`.
* `Cslib.RealRoot.isolatePolyRootsTotal_bijective`,
  `Cslib.RealRoot.isolatePolyRootsTotal_pairwise_disjoint`,
  `Cslib.RealRoot.isolatePolyRootsTotal_endpoint_bounds_of_bitBound`: `Polynomial ℚ` theorems.

## References

`separateTouching`, `isolateRootsTotal` (refining `isolateRoots`, which may return touching
intervals, into strictly separated pairwise-disjoint closed intervals on squarefree input, with
dyadic endpoint bit bounds under `HasCoeffBitBound B cs`), and the polynomial-time certification
in `CslibFrontier.Computability.Complexity.RealAlgebraic.RootIsolation` are this library's own
construction, distinct from the mathematical Sturm-counting and root-separation ingredients below;
[BasuPollackRoy2006], §10.2, Algorithm 10.4 (pp. 373–374, over integer coefficients using
Bernstein coefficient variation and returning open rational intervals and singleton rational roots)
is related work.

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

/-! ### Boundary separation into strictly disjoint closed intervals -/

/-- Bisect `(a, m]` and `(m, b]` around a non-root midpoint `m` until finding `(u₁', l₂')` with
`u₁' < l₂'`, no roots in `(u₁', m]`, and no roots in `(m, l₂']`. -/
@[expose] def separateMidLoop (seq : List (List ℚ)) :
    ℕ → ℚ → ℚ → ℚ → ℕ → ℚ × ℚ
  | 0, a, _, b, _ => (a, b)
  | fuel + 1, a, m, b, vm =>
    let m₁ := (a + m) / 2
    if sturmVariationsList seq m₁ = vm then
      (m₁, m)
    else
      let m₂ := (m + b) / 2
      if sturmVariationsList seq m₂ = vm then
        (m, m₂)
      else
        separateMidLoop seq fuel m₁ m m₂ vm

/-- Dyadic bound for `separateMidLoop`: `fuel` steps increase the dyadic exponent by at most
`fuel`. -/
theorem separateMidLoop_dyadicBounded (seq : List (List ℚ)) :
    ∀ (fuel B e : ℕ) (a m b : ℚ) (vm : ℕ),
      DyadicBounded B e a → DyadicBounded B e m → DyadicBounded B e b →
      let p := separateMidLoop seq fuel a m b vm
      DyadicBounded B (e + fuel) p.1 ∧ DyadicBounded B (e + fuel) p.2
  | 0, _, _, _, _, _, _, ha, _, hb => ⟨ha, hb⟩
  | fuel + 1, B, e, a, m, b, vm, ha, hm, hb => by
    simp only [separateMidLoop]
    have hm1 := ha.mid hm
    have hm2 := hm.mid hb
    split_ifs
    · exact ⟨hm1.mono (by omega), hm.mono (by omega)⟩
    · exact ⟨hm.mono (by omega), hm2.mono (by omega)⟩
    · simpa only [Nat.add_right_comm, Nat.add_assoc] using
        separateMidLoop_dyadicBounded seq fuel B (e + 1) _ m _ vm hm1 (hm.mono (by omega)) hm2

private theorem exists_root_Ioc_of_var_pos {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    {u v : ℚ} (huv : u ≤ v)
    (hpos : 1 ≤ sturmVariationsList (sturmSeqList cs) u -
      sturmVariationsList (sturmSeqList cs) v) :
    ∃ r : ℝ, (u : ℝ) < r ∧ r ≤ (v : ℝ) ∧ ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot r := by
  have hpR0 : (ofCoeffList cs).map (algebraMap ℚ ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr hsep.ne_zero
  rw [card_roots_Ioc_eq hsep huv] at hpos
  obtain ⟨r, hr⟩ := Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one hpos)
  simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hpR0] at hr
  exact ⟨r, hr.2.1, hr.2.2, hr.1⟩

private theorem separateMidLoop_spec {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    ∀ (fuel depth : ℕ) (a m b : ℚ) (vm : ℕ),
      depth + fuel = mignotteBisectionDepth cs →
      a < m →
      m < b →
      vm = sturmVariationsList (sturmSeqList cs) m →
      sturmVariationsList (sturmSeqList cs) a - vm = 1 →
      vm - sturmVariationsList (sturmSeqList cs) b = 1 →
      ¬((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot (m : ℝ) →
      (b - a : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ depth →
      let res := separateMidLoop (sturmSeqList cs) fuel a m b vm
      let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
      a ≤ res.1 ∧ res.1 ≤ m ∧ m ≤ res.2 ∧ res.2 ≤ b ∧ res.1 < res.2 ∧
        (∀ r : ℝ, (res.1 : ℝ) < r → r ≤ (m : ℝ) → ¬pR.IsRoot r) ∧
        (∀ r : ℝ, (m : ℝ) < r → r ≤ (res.2 : ℝ) → ¬pR.IsRoot r)
  | 0, depth, a, m, b, vm, hsum, ham, hmb, hvm, hca, hcb, hnotm, hwidth => by
    subst hvm
    obtain ⟨r₁, har₁, hr₁m, hr₁⟩ := exists_root_Ioc_of_var_pos hsep ham.le (by omega)
    obtain ⟨r₂, hmr₂, hr₂b, hr₂⟩ := exists_root_Ioc_of_var_pos hsep hmb.le (by omega)
    exact (not_two_roots_of_width_le hsep hr₁ hr₂
      ((lt_of_le_of_ne hr₁m fun h => hnotm (h ▸ hr₁)).trans hmr₂) har₁.le hr₂b
      (by omega) hwidth).elim
  | fuel + 1, depth, a, m, b, vm, hsum, ham, hmb, hvm, hca, hcb, hnotm, hwidth => by
    let seq := sturmSeqList cs
    let m₁ := (a + m) / 2
    let m₂ := (m + b) / 2
    have ham1 : a < m₁ := by dsimp only [m₁]; linarith
    have hm1m : m₁ < m := by dsimp only [m₁]; linarith
    have hmm2 : m < m₂ := by dsimp only [m₂]; linarith
    have hm2b : m₂ < b := by dsimp only [m₂]; linarith
    have h1l := sturmVariationsList_antitone hsep ham1.le
    have h1r := hvm ▸ sturmVariationsList_antitone hsep hm1m.le
    have h2l := hvm ▸ sturmVariationsList_antitone hsep hmm2.le
    have h2r := sturmVariationsList_antitone hsep hm2b.le
    dsimp only [seq, m₁, m₂] at h1l h1r h2l h2r
    simp only [separateMidLoop]
    split_ifs with h1 h2
    · exact ⟨ham1.le, hm1m.le, le_rfl, hmb.le, hm1m,
        fun r h1r' hrm => no_root_Ioc_of_card_eq_zero hsep hm1m.le
          (by rw [← hvm]; dsimp only [m₁]; omega) h1r' hrm,
        fun _ _ _ => by linarith⟩
    · exact ⟨ham.le, le_rfl, hmm2.le, hm2b.le, hmm2, fun _ _ _ => by linarith,
        fun r hmr hrm2 => no_root_Ioc_of_card_eq_zero hsep hmm2.le
          (by rw [← hvm]; dsimp only [m₂]; omega) hmr hrm2⟩
    · have hw_next : (m₂ - m₁ : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ (depth + 1) := by
        have : (m₂ - m₁ : ℝ) = (b - a : ℝ) / 2 := by dsimp only [m₁, m₂]; push_cast; ring
        rw [this, pow_succ, ← div_div]; linarith
      rcases separateMidLoop_spec hsep fuel (depth + 1) m₁ m m₂ vm (by omega) hm1m hmm2
          hvm (by dsimp only [m₁]; omega) (by dsimp only [m₂]; omega) hnotm hw_next with
        ⟨i1, i2, i3, i4, ilt, in1, in2⟩
      exact ⟨ham1.le.trans i1, i2, i3, i4.trans hm2b.le, ilt, in1, in2⟩

/-- Separate the boundary between two consecutive isolating intervals `I₁` and `I₂`, returning
`(u₁', l₂')` with `I₁.lower ≤ u₁' ≤ I₁.upper`, `I₂.lower ≤ l₂' ≤ I₂.upper`, and `u₁' < l₂'`. -/
@[expose] def separatePair (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ)
    (I₁ I₂ : RootInterval) : ℚ × ℚ :=
  if I₁.upper < I₂.lower then
    (I₁.upper, I₂.lower)
  else if evalCoeffList I₁.lower t = 0 then
    (I₁.lower, I₂.lower)
  else
    let vm := sturmVariationsList seq I₁.upper
    separateMidLoop seq depth I₁.lower I₁.upper I₂.upper vm

/-- Dyadic bound for `separatePair`. -/
theorem separatePair_dyadicBounded (t : List ℚ) (seq : List (List ℚ))
    (depth B e : ℕ) (I₁ I₂ : RootInterval)
    (h1l : DyadicBounded B e I₁.lower) (h1u : DyadicBounded B e I₁.upper)
    (h2l : DyadicBounded B e I₂.lower) (h2u : DyadicBounded B e I₂.upper) :
    let p := separatePair t seq depth I₁ I₂
    DyadicBounded B (e + depth) p.1 ∧ DyadicBounded B (e + depth) p.2 := by
  simp only [separatePair]
  split_ifs
  · exact ⟨h1u.mono (by omega), h2l.mono (by omega)⟩
  · exact ⟨h1l.mono (by omega), h2l.mono (by omega)⟩
  · exact separateMidLoop_dyadicBounded seq depth B e I₁.lower I₁.upper I₂.upper _
      h1l h1u h2u

private theorem sturmVariationsList_sub_eq_one_of_unique_Ioc {cs : List ℚ}
    (hsep : (ofCoeffList cs).Separable) {u v : ℚ} {r₀ : ℝ} (huv : u ≤ v)
    (hr₀ : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot r₀)
    (hur₀ : (u : ℝ) < r₀) (hr₀v : r₀ ≤ (v : ℝ))
    (huniq : ∀ x : ℝ, (u : ℝ) < x → x ≤ (v : ℝ) →
      ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot x → x = r₀) :
    sturmVariationsList (sturmSeqList cs) u - sturmVariationsList (sturmSeqList cs) v = 1 := by
  let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
  have hpR0 : pR ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr hsep.ne_zero
  rw [card_roots_Ioc_eq hsep huv]
  have hset : pR.roots.toFinset.filter (fun r : ℝ => (u : ℝ) < r ∧ r ≤ (v : ℝ)) = {r₀} := by
    ext x
    simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hpR0, Finset.mem_singleton]
    exact ⟨fun ⟨hx, hxl, hxu⟩ => huniq x hxl hxu hx, fun h => h ▸ ⟨hr₀, hur₀, hr₀v⟩⟩
  rw [hset, Finset.card_singleton]

private theorem separatePair_spec {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    {I₁ I₂ : RootInterval}
    (hiso₁ : I₁.IsIsolatingFor ((ofCoeffList cs).map (algebraMap ℚ ℝ)))
    (hiso₂ : I₂.IsIsolatingFor ((ofCoeffList cs).map (algebraMap ℚ ℝ)))
    (hb₁ : -(cauchyBoundNat cs : ℚ) ≤ I₁.lower)
    (hb₂ : I₂.upper ≤ (cauchyBoundNat cs : ℚ))
    (hgap : IntervalGapOk ((ofCoeffList cs).map (algebraMap ℚ ℝ)) I₁ I₂) :
    let res := separatePair (CoeffList.trim cs) (sturmSeqList cs)
      (mignotteBisectionDepth cs) I₁ I₂
    let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
    I₁.lower ≤ res.1 ∧ res.1 ≤ I₁.upper ∧ I₂.lower ≤ res.2 ∧ res.2 ≤ I₂.upper ∧
      res.1 < res.2 ∧
      (∀ r : ℝ, (I₁.lower : ℝ) ≤ r ∧ r ≤ (I₁.upper : ℝ) ∧ pR.IsRoot r → r ≤ (res.1 : ℝ)) ∧
      (∀ r : ℝ, (I₂.lower : ℝ) ≤ r ∧ r ≤ (I₂.upper : ℝ) ∧ pR.IsRoot r → (res.2 : ℝ) ≤ r) := by
  simp only [separatePair]
  split_ifs with hlt hel
  · exact ⟨hiso₁.1, le_rfl, le_rfl, hiso₂.1, hlt, fun _ h => h.2.1, fun _ h => h.1⟩
  · obtain ⟨heq_m, hnotm⟩ := Or.resolve_left hgap hlt
    have hl_root : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot (I₁.lower : ℝ) :=
      IsRoot.def.mpr ((eval_rat_eq_zero_iff cs I₁.lower).mp hel)
    have hl_lt : I₁.lower < I₁.upper :=
      lt_of_le_of_ne hiso₁.1 fun h => hnotm (h ▸ hl_root)
    obtain ⟨_, _, huniq⟩ := hiso₁.2
    refine ⟨le_rfl, hiso₁.1, le_rfl, hiso₂.1, heq_m ▸ hl_lt, fun r hr => ?_, fun _ h => h.1⟩
    rw [huniq r hr, ← huniq _ ⟨le_rfl, Rat.cast_le.mpr hiso₁.1, hl_root⟩]
  · obtain ⟨heq_m, hnotm⟩ := Or.resolve_left hgap hlt
    have hnotl : ¬((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot (I₁.lower : ℝ) :=
      fun h => hel ((eval_rat_eq_zero_iff cs I₁.lower).mpr h.eq_zero)
    have heqR : (I₁.upper : ℝ) = (I₂.lower : ℝ) := congrArg Rat.cast heq_m
    obtain ⟨r₁, ⟨hr₁l, hr₁u, hr₁r⟩, hr₁_uniq⟩ := hiso₁.2
    obtain ⟨r₂, ⟨hr₂l, hr₂u, hr₂r⟩, hr₂_uniq⟩ := hiso₂.2
    have hr₁_gt : (I₁.lower : ℝ) < r₁ := lt_of_le_of_ne hr₁l fun h => hnotl (h ▸ hr₁r)
    have hr₁_lt : r₁ < (I₁.upper : ℝ) := lt_of_le_of_ne hr₁u fun h => hnotm (h.symm ▸ hr₁r)
    have hr₂_gt : (I₁.upper : ℝ) < r₂ :=
      lt_of_le_of_ne (heqR ▸ hr₂l) fun h => hnotm (h ▸ hr₂r)
    have ham : I₁.lower < I₁.upper := Rat.cast_lt.mp (hr₁_gt.trans hr₁_lt)
    have hmb : I₁.upper < I₂.upper := Rat.cast_lt.mp (hr₂_gt.trans_le hr₂u)
    have hca := sturmVariationsList_sub_eq_one_of_unique_Ioc hsep ham.le hr₁r hr₁_gt hr₁u
      fun x hxl hxu hx => hr₁_uniq x ⟨hxl.le, hxu, hx⟩
    have hcb := sturmVariationsList_sub_eq_one_of_unique_Ioc hsep hmb.le hr₂r hr₂_gt hr₂u
      fun x hxl hxu hx => hr₂_uniq x ⟨(heqR ▸ hxl).le, hxu, hx⟩
    have hw0 : (I₂.upper - I₁.lower : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ 0 := by
      have := Rat.cast_le (K := ℝ).mpr hb₁
      have := Rat.cast_le (K := ℝ).mpr hb₂
      push_cast at *
      simp only [pow_zero, div_one]; linarith
    rcases separateMidLoop_spec hsep (mignotteBisectionDepth cs) 0 I₁.lower I₁.upper I₂.upper
        _ (Nat.zero_add _) ham hmb rfl hca hcb hnotm hw0 with
      ⟨hm1, hm2, hm3, hm4, hmlt, hno1, hno2⟩
    refine ⟨hm1, hm2, heq_m ▸ hm3, hm4, hmlt,
      fun r ⟨_, hru, hrr⟩ => le_of_not_gt fun hgt => hno1 r hgt hru hrr,
      fun r ⟨hrl, _, hrr⟩ => le_of_not_gt fun hgt =>
        hno2 r (lt_of_le_of_ne (heqR.symm ▸ hrl) fun h => hnotm (h ▸ hrr)) hgt.le hrr⟩

/-- Walk a chain of isolating intervals carrying an updated `curLower` endpoint and separating
every adjacent pair. -/
@[expose] def separateChain (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ)
    (curLower : ℚ) : List RootInterval → List RootInterval
  | [] => []
  | [I] => [{ lower := curLower, upper := I.upper }]
  | I₁ :: I₂ :: rest =>
    let p := separatePair t seq depth I₁ I₂
    { lower := curLower, upper := p.1 } :: separateChain t seq depth p.2 (I₂ :: rest)

/-- Separate all touching adjacent boundaries in a list of isolating intervals. -/
@[expose] def separateTouching (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ) :
    List RootInterval → List RootInterval
  | [] => []
  | I₀ :: rest => separateChain t seq depth I₀.lower (I₀ :: rest)

private theorem separateChain_length (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ) :
    ∀ (L : List RootInterval) (curLower : ℚ),
      (separateChain t seq depth curLower L).length = L.length
  | [], _ => rfl
  | [_], _ => rfl
  | I₁ :: I₂ :: rest, _ => by
    simp only [separateChain, List.length_cons, separateChain_length t seq depth (I₂ :: rest)]

theorem separateTouching_length (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ)
    (L : List RootInterval) :
    (separateTouching t seq depth L).length = L.length := by
  cases L with
  | nil => rfl
  | cons I₀ rest => exact separateChain_length t seq depth (I₀ :: rest) I₀.lower

/-- Dyadic bound for `separateChain`. -/
theorem separateChain_dyadicBounded (t : List ℚ) (seq : List (List ℚ))
    (depth B e : ℕ) :
    ∀ (L : List RootInterval) (curLower : ℚ),
      DyadicBounded B (e + depth) curLower →
      (∀ I ∈ L, DyadicBounded B e I.lower ∧ DyadicBounded B e I.upper) →
      ∀ J ∈ separateChain t seq depth curLower L,
        DyadicBounded B (e + depth) J.lower ∧ DyadicBounded B (e + depth) J.upper
  | [], _, _, _ => by simp [separateChain]
  | [I], curLower, hcur, hL => by
    simp only [separateChain, List.mem_singleton]
    rintro J rfl
    exact ⟨hcur, (hL I List.mem_cons_self).2.mono (by omega)⟩
  | I₁ :: I₂ :: rest, curLower, hcur, hL => by
    simp only [separateChain, List.mem_cons]
    have h1 := hL I₁ List.mem_cons_self
    have h2 := hL I₂ (List.mem_cons_of_mem I₁ List.mem_cons_self)
    have hp := separatePair_dyadicBounded t seq depth B e I₁ I₂ h1.1 h1.2 h2.1 h2.2
    rintro J (rfl | hmem)
    · exact ⟨hcur, hp.1⟩
    · exact separateChain_dyadicBounded t seq depth B e (I₂ :: rest) _ hp.2
        (fun I hI => hL I (List.mem_cons_of_mem I₁ hI)) J hmem

private theorem isolating_shrink {pR : ℝ[X]} {I : RootInterval} {l u : ℚ}
    (hiso : I.IsIsolatingFor pR) (hl : I.lower ≤ l) (hu : u ≤ I.upper)
    (hrl : ∀ r : ℝ, (I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) ∧ pR.IsRoot r → (l : ℝ) ≤ r)
    (hru : ∀ r : ℝ, (I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) ∧ pR.IsRoot r → r ≤ (u : ℝ)) :
    ({ lower := l, upper := u } : RootInterval).IsIsolatingFor pR ∧
      I.lower ≤ l ∧ u ≤ I.upper ∧
      ∀ r : ℝ, ((l : ℝ) ≤ r ∧ r ≤ (u : ℝ) ∧ pR.IsRoot r) ↔
        ((I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) ∧ pR.IsRoot r) := by
  have heq : ∀ r : ℝ, ((l : ℝ) ≤ r ∧ r ≤ (u : ℝ) ∧ pR.IsRoot r) ↔
      ((I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) ∧ pR.IsRoot r) := fun r =>
    ⟨fun ⟨h1, h2, h3⟩ => ⟨(Rat.cast_le.mpr hl).trans h1, h2.trans (Rat.cast_le.mpr hu), h3⟩,
      fun h => ⟨hrl r h, hru r h, h.2.2⟩⟩
  obtain ⟨r₀, hr₀, huniq⟩ := hiso.2
  exact ⟨⟨Rat.cast_le.mp ((hrl r₀ hr₀).trans (hru r₀ hr₀)),
    r₀, (heq r₀).mpr hr₀, fun r hr => huniq r ((heq r).mp hr)⟩, hl, hu, heq⟩

private theorem separateChain_spec {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    ∀ (rest : List RootInterval) (I₀ : RootInterval) (curLower : ℚ),
      let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
      let b : ℚ := (cauchyBoundNat cs : ℚ)
      (∀ I ∈ I₀ :: rest, I.IsIsolatingFor pR ∧ -b ≤ I.lower ∧ I.upper ≤ b) →
      (I₀ :: rest).Pairwise (IntervalGapOk pR) →
      I₀.lower ≤ curLower →
      (∀ r : ℝ, (I₀.lower : ℝ) ≤ r ∧ r ≤ (I₀.upper : ℝ) ∧ pR.IsRoot r → (curLower : ℝ) ≤ r) →
      let out := separateChain (CoeffList.trim cs) (sturmSeqList cs) (mignotteBisectionDepth cs)
        curLower (I₀ :: rest)
      (∃ J₀ Js, out = J₀ :: Js ∧ J₀.lower = curLower) ∧
      out.Pairwise (fun A B => A.upper < B.lower) ∧
      ∀ (k : ℕ) (hk : k < (I₀ :: rest).length),
        let I := (I₀ :: rest)[k]
        let J := out[k]'(by
          rw [separateChain_length]
          exact hk)
        J.IsIsolatingFor pR ∧ I.lower ≤ J.lower ∧ J.upper ≤ I.upper ∧
          ∀ r : ℝ, ((J.lower : ℝ) ≤ r ∧ r ≤ (J.upper : ℝ) ∧ pR.IsRoot r) ↔
            ((I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) ∧ pR.IsRoot r)
  | [], I₀, curLower, hiso_all, _, hcur_le, hcur_root => by
    have h0 := isolating_shrink (hiso_all I₀ List.mem_cons_self).1
      hcur_le le_rfl hcur_root (fun _ h => h.2.1)
    simp only [separateChain]
    refine ⟨⟨_, [], rfl, rfl⟩, List.pairwise_singleton _ _, fun k hk => ?_⟩
    obtain rfl : k = 0 := by simp only [List.length_singleton] at hk; omega
    exact h0
  | I₁ :: rest', I₀, curLower, hiso_all, hpw, hcur_le, hcur_root => by
    have hI₀ := hiso_all I₀ List.mem_cons_self
    have hI₁ := hiso_all I₁ (List.mem_cons_of_mem I₀ List.mem_cons_self)
    rcases List.pairwise_cons.mp hpw with ⟨hgap, hpw_tail⟩
    rcases separatePair_spec hsep hI₀.1 hI₁.1 hI₀.2.1 hI₁.2.2
        (hgap I₁ List.mem_cons_self) with ⟨_, hp2, hp3, _, hplt, hproot1, hproot2⟩
    rcases separateChain_spec hsep rest' I₁ _
        (fun I hI => hiso_all I (List.mem_cons_of_mem I₀ hI)) hpw_tail hp3 hproot2 with
      ⟨⟨J₁, Js, htail_eq, hJ₁_low⟩, htail_pw, htail_idx⟩
    have hJ₁_le : J₁.lower ≤ J₁.upper := by
      simpa only [htail_eq, List.getElem_cons_zero] using (htail_idx 0 (Nat.zero_lt_succ _)).1.1
    simp only [separateChain]
    refine ⟨⟨_, _, rfl, rfl⟩, List.pairwise_cons.mpr ⟨fun B hB => ?_, htail_pw⟩, ?_⟩
    · rw [htail_eq] at hB htail_pw
      rcases List.mem_cons.mp hB with rfl | hBs
      · exact hJ₁_low ▸ hplt
      · exact lt_of_lt_of_le (hJ₁_low ▸ hplt) hJ₁_le |>.trans
          ((List.pairwise_cons.mp htail_pw).1 B hBs)
    · rintro (_ | k') hk
      · exact isolating_shrink hI₀.1 hcur_le hp2 hcur_root hproot1
      · exact htail_idx k' (Nat.lt_of_succ_lt_succ hk)

/-! ### Computable isolator returning strictly disjoint closed intervals -/

/-- Computable Sturm-bisection real-root isolator on `List ℚ` returning strictly disjoint closed
rational intervals (`J₁.upper < J₂.lower`). -/
@[expose] def isolateRootsTotal (cs : List ℚ) : List RootInterval :=
  let t := CoeffList.trim cs
  if t.isEmpty then
    []
  else
    let seq := sturmSeqList cs
    let b : ℚ := (cauchyBoundNat cs : ℚ)
    let depth := mignotteBisectionDepth cs
    let vLeft := sturmVariationsList seq (-b)
    let vRight := sturmVariationsList seq b
    let raw := isolateIoc t seq depth depth (-b) b vLeft vRight
    separateTouching t seq depth raw

theorem isolateRootsTotal_eq_separateTouching (cs : List ℚ) :
    isolateRootsTotal cs =
      separateTouching (CoeffList.trim cs) (sturmSeqList cs) (mignotteBisectionDepth cs)
        (isolateRoots cs) := by
  simp only [isolateRootsTotal, isolateRoots]
  by_cases he : (CoeffList.trim cs).isEmpty = true
  · simp only [he, ↓reduceIte, separateTouching]
  · simp only [he, Bool.false_eq_true, ↓reduceIte]

/-- `isolateRootsTotal cs` has the exact same length as `isolateRoots cs`. -/
theorem isolateRootsTotal_length_eq (cs : List ℚ) :
    (isolateRootsTotal cs).length = (isolateRoots cs).length := by
  rw [isolateRootsTotal_eq_separateTouching, separateTouching_length]

/-- Unconditional dyadic numerator and denominator bounds on every endpoint in
`isolateRootsTotal cs`. -/
theorem isolateRootsTotal_endpoint_bounds (cs : List ℚ) :
    ∀ J ∈ isolateRootsTotal cs,
      let b := cauchyBoundNat cs
      let e := 3 * mignotteBisectionDepth cs
      DyadicBounded b e J.lower ∧ DyadicBounded b e J.upper ∧
        J.lower.den ≤ 2 ^ e ∧ J.upper.den ≤ 2 ^ e ∧
        Int.natAbs J.lower.num ≤ b * 2 ^ e ∧ Int.natAbs J.upper.num ≤ b * 2 ^ e := by
  rw [isolateRootsTotal_eq_separateTouching]
  have hraw := isolateRoots_dyadicBounded cs
  cases hL : isolateRoots cs with
  | nil => simp only [separateTouching]; rintro _ ⟨⟩
  | cons I₀ rest =>
    intro J hJ
    have ⟨hlow, hup⟩ := separateChain_dyadicBounded (CoeffList.trim cs) (sturmSeqList cs)
      (mignotteBisectionDepth cs) (cauchyBoundNat cs) (2 * mignotteBisectionDepth cs)
      (I₀ :: rest) I₀.lower ((hraw I₀ (hL ▸ List.mem_cons_self)).1.mono (by omega))
      (fun I hI => hraw I (hL ▸ hI)) J hJ
    rw [show 2 * mignotteBisectionDepth cs + mignotteBisectionDepth cs =
      3 * mignotteBisectionDepth cs by omega] at hlow hup
    exact ⟨hlow, hup, hlow.den_le, hup.den_le, hlow.natAbs_num_le, hup.natAbs_num_le⟩

private theorem isolateRootsTotal_index_spec {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    (idx : ℕ) (hidx : idx < (isolateRoots cs).length) :
    let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
    let I := (isolateRoots cs)[idx]
    let J := (isolateRootsTotal cs)[idx]'(by rw [isolateRootsTotal_length_eq]; exact hidx)
    J.IsIsolatingFor pR ∧ I.lower ≤ J.lower ∧ J.upper ≤ I.upper ∧
      ∀ r : ℝ, ((J.lower : ℝ) ≤ r ∧ r ≤ (J.upper : ℝ) ∧ pR.IsRoot r) ↔
        ((I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) ∧ pR.IsRoot r) := by
  obtain ⟨I₀, rest, hL⟩ := List.exists_cons_of_length_pos (Nat.zero_lt_of_lt hidx)
  have h := (separateChain_spec hsep rest I₀ I₀.lower
    (fun I hI => ⟨isolateRoots_isIsolatingFor hsep I (hL ▸ hI),
      isolateRoots_mem_cauchy hsep I (hL ▸ hI)⟩)
    (hL ▸ isolateRoots_intervalGapOk hsep) le_rfl (fun _ h => h.1)).2.2 idx (hL ▸ hidx)
  have htot : isolateRootsTotal cs = separateChain (CoeffList.trim cs) (sturmSeqList cs)
      (mignotteBisectionDepth cs) I₀.lower (I₀ :: rest) := by
    simp only [isolateRootsTotal_eq_separateTouching, hL, separateTouching]
  dsimp only at h ⊢
  rwa [List.getElem_of_eq hL hidx, List.getElem_of_eq htot _]

/-- Soundness: every interval in `isolateRootsTotal cs` isolates a unique real root of
`(ofCoeffList cs).map (algebraMap ℚ ℝ)`. -/
theorem isolateRootsTotal_isIsolatingFor {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    ∀ J ∈ isolateRootsTotal cs, J.IsIsolatingFor ((ofCoeffList cs).map (algebraMap ℚ ℝ)) := by
  intro J hJ
  obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hJ
  exact (isolateRootsTotal_index_spec hsep idx (isolateRootsTotal_length_eq cs ▸ hidx)).1

/-- Soundness in `Polynomial.aeval` form: every interval `J ∈ isolateRootsTotal cs` satisfies
`J.lower ≤ J.upper` and contains a unique `x : ℝ` with `Polynomial.aeval x (ofCoeffList cs) = 0`. -/
theorem isolateRootsTotal_aeval_unique {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    ∀ J ∈ isolateRootsTotal cs, J.lower ≤ J.upper ∧
      ∃! x : ℝ, x ∈ Set.Icc (J.lower : ℝ) (J.upper : ℝ) ∧
        Polynomial.aeval x (ofCoeffList cs) = 0 := by
  intro J hJ
  obtain ⟨hle, r₀, ⟨hl, hu, hr₀⟩, huniq⟩ := isolateRootsTotal_isIsolatingFor hsep J hJ
  simp only [IsRoot.def, Polynomial.eval_map_algebraMap] at hr₀ huniq
  exact ⟨hle, r₀, ⟨⟨hl, hu⟩, hr₀⟩, fun x ⟨⟨hxl, hxu⟩, hx0⟩ => huniq x ⟨hxl, hxu, hx0⟩⟩

/-- Strict separation: every pair of intervals in `isolateRootsTotal cs` satisfies
`J₁.upper < J₂.lower`. -/
theorem isolateRootsTotal_pairwise_lt {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    (isolateRootsTotal cs).Pairwise (fun J₁ J₂ => J₁.upper < J₂.lower) := by
  rw [isolateRootsTotal_eq_separateTouching]
  cases hL : isolateRoots cs with
  | nil => exact List.Pairwise.nil
  | cons I₀ rest =>
    exact (separateChain_spec hsep rest I₀ I₀.lower
      (fun I hI => ⟨isolateRoots_isIsolatingFor hsep I (hL ▸ hI),
        isolateRoots_mem_cauchy hsep I (hL ▸ hI)⟩)
      (hL ▸ isolateRoots_intervalGapOk hsep) le_rfl (fun _ h => h.1)).2.1

/-- Closed-interval disjointness: the closed intervals `Set.Icc (J.lower : ℝ) (J.upper : ℝ)` of
`isolateRootsTotal cs` are pairwise disjoint. -/
theorem isolateRootsTotal_pairwise_disjoint {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    (isolateRootsTotal cs).Pairwise
      (Function.onFun Disjoint fun J => Set.Icc (J.lower : ℝ) (J.upper : ℝ)) :=
  (isolateRootsTotal_pairwise_lt hsep).imp fun hlt =>
    Set.disjoint_left.mpr fun _ hx₁ hx₂ =>
      (hx₁.2.trans_lt (Rat.cast_lt.mpr hlt)).not_ge hx₂.1

/-- The unique real root `x : ℝ` with `Polynomial.aeval x (ofCoeffList cs) = 0` inside the `i`-th
interval of `isolateRootsTotal cs`. -/
noncomputable def totalIsolatedRoot {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    (i : Fin (isolateRootsTotal cs).length) :
    {x : ℝ // Polynomial.aeval x (ofCoeffList cs) = 0} :=
  let i₀ : Fin (isolateRoots cs).length := ⟨i.1, (isolateRootsTotal_length_eq cs) ▸ i.2⟩
  let r := isolatedRoot hsep i₀
  ⟨r.1, by
    have h := r.2
    rwa [IsRoot.def, Polynomial.eval_map_algebraMap] at h⟩

/-- `totalIsolatedRoot hsep i` lies in the `i`-th closed interval of `isolateRootsTotal cs`. -/
theorem totalIsolatedRoot_mem {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    (i : Fin (isolateRootsTotal cs).length) :
    let J := (isolateRootsTotal cs)[i]
    (totalIsolatedRoot hsep i).1 ∈ Set.Icc (J.lower : ℝ) (J.upper : ℝ) :=
  let i₀ : Fin (isolateRoots cs).length := ⟨i.1, isolateRootsTotal_length_eq cs ▸ i.2⟩
  let h := ((isolateRootsTotal_index_spec hsep i.1 i₀.2).2.2.2 _).mpr
    ⟨(isolatedRoot_mem hsep i₀).1, (isolatedRoot_mem hsep i₀).2, (isolatedRoot hsep i₀).2⟩
  ⟨h.1, h.2.1⟩

/-- The real roots indexed by `totalIsolatedRoot hsep` are strictly increasing. -/
theorem totalIsolatedRoot_strictMono {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    StrictMono (fun i : Fin (isolateRootsTotal cs).length => (totalIsolatedRoot hsep i).1) :=
  fun _ _ hij => isolatedRoot_strictMono hsep hij

/-- Bijection between `Fin (isolateRootsTotal cs).length` and
`{x : ℝ // Polynomial.aeval x (ofCoeffList cs) = 0}` for separable `ofCoeffList cs`. -/
theorem isolateRootsTotal_bijective {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    Function.Bijective (totalIsolatedRoot hsep) := by
  have hbij := isolateRoots_bijective hsep
  refine ⟨fun i j hij => ?_, fun ⟨x, hx⟩ => ?_⟩
  · have hv : (totalIsolatedRoot hsep i).1 = (totalIsolatedRoot hsep j).1 :=
      congrArg Subtype.val hij
    have heq := hbij.1 (Subtype.ext hv)
    exact Fin.ext (congrArg (Fin.val : Fin (isolateRoots cs).length → ℕ) heq)
  · obtain ⟨i₀, hi₀⟩ := hbij.2 ⟨x, by rwa [IsRoot.def, Polynomial.eval_map_algebraMap]⟩
    exact ⟨⟨i₀.1, (isolateRootsTotal_length_eq cs).symm ▸ i₀.2⟩,
      Subtype.ext (show (isolatedRoot hsep i₀).1 = x from congrArg Subtype.val hi₀)⟩

/-- Squarefree bijection form for `isolateRootsTotal cs`. -/
theorem isolateRootsTotal_bijective_of_squarefree {cs : List ℚ}
    (hsq : Squarefree (ofCoeffList cs)) :
    Function.Bijective (totalIsolatedRoot (PerfectField.separable_iff_squarefree.mpr hsq)) :=
  isolateRootsTotal_bijective (PerfectField.separable_iff_squarefree.mpr hsq)

/-- Explicit polynomial endpoint numerator and denominator bounds in `(cs.length, B)` under
`HasCoeffBitBound B cs`: every returned endpoint has denominator `≤ 2 ^ E` and numerator
`natAbs ≤ 3 * 2 ^ (2 * B + E)`, where `E = 3 * (cs.length + 2) ^ 2 * (B + 2)`. -/
theorem isolateRootsTotal_endpoint_bounds_of_bitBound {B : ℕ} {cs : List ℚ}
    (hB : HasCoeffBitBound B cs) :
    ∀ J ∈ isolateRootsTotal cs,
      let E := 3 * (cs.length + 2) ^ 2 * (B + 2)
      J.lower.den ≤ 2 ^ E ∧ J.upper.den ≤ 2 ^ E ∧
        Int.natAbs J.lower.num ≤ 3 * 2 ^ (2 * B + E) ∧
        Int.natAbs J.upper.num ≤ 3 * 2 ^ (2 * B + E) := by
  intro J hJ
  rcases isolateRootsTotal_endpoint_bounds cs J hJ with ⟨_, _, hlden, huden, hlnum, hunum⟩
  have hpow : 2 ^ (3 * mignotteBisectionDepth cs) ≤ 2 ^ (3 * (cs.length + 2) ^ 2 * (B + 2)) :=
    Nat.pow_le_pow_right (by omega) <|
      (Nat.mul_le_mul_left 3 (mignotteBisectionDepth_le_of_bitBound hB)).trans_eq (by ring)
  have hmul : cauchyBoundNat cs * 2 ^ (3 * mignotteBisectionDepth cs) ≤
      3 * 2 ^ (2 * B + 3 * (cs.length + 2) ^ 2 * (B + 2)) := by
    have hb : cauchyBoundNat cs ≤ 3 * 2 ^ (2 * B) := by
      have := cauchyBoundNat_le_of_bitBound hB
      have := Nat.one_le_pow (2 * B) 2 (by omega)
      omega
    calc _ ≤ 3 * 2 ^ (2 * B) * 2 ^ (3 * (cs.length + 2) ^ 2 * (B + 2)) := by gcongr
      _ = _ := by rw [mul_assoc, ← Nat.pow_add]
  exact ⟨hlden.trans hpow, huden.trans hpow, hlnum.trans hmul, hunum.trans hmul⟩

/-- Combined specification of the computable isolator `isolateRootsTotal cs` for any squarefree
`p : ℚ[X]` represented by `cs : List ℚ` (`ofCoeffList cs = p`) with coefficient bit bound `B`:
isolating `aeval` soundness, strict separation `J₁.upper < J₂.lower`, pairwise disjoint closed real
intervals `Set.Icc`, strictly monotone bijection onto `{x : ℝ // Polynomial.aeval x p = 0}`, and
polynomial dyadic endpoint numerator/denominator bounds. -/
theorem isolateRootsTotal_spec_of_eq {B : ℕ} {cs : List ℚ} {p : ℚ[X]}
    (hp : ofCoeffList cs = p) (hsq : Squarefree p) (hB : HasCoeffBitBound B cs) :
    (∀ J ∈ isolateRootsTotal cs, J.lower ≤ J.upper ∧
      ∃! x : ℝ, x ∈ Set.Icc (J.lower : ℝ) (J.upper : ℝ) ∧ Polynomial.aeval x p = 0) ∧
    (isolateRootsTotal cs).Pairwise (fun J₁ J₂ => J₁.upper < J₂.lower) ∧
    (isolateRootsTotal cs).Pairwise
      (Function.onFun Disjoint fun J => Set.Icc (J.lower : ℝ) (J.upper : ℝ)) ∧
    (∃ f : Fin (isolateRootsTotal cs).length → {x : ℝ // Polynomial.aeval x p = 0},
      Function.Bijective f ∧
      StrictMono (fun i => (f i).1) ∧
      ∀ i,
        let J := (isolateRootsTotal cs)[i]
        (f i).1 ∈ Set.Icc (J.lower : ℝ) (J.upper : ℝ)) ∧
    (∀ J ∈ isolateRootsTotal cs,
      let E := 3 * (cs.length + 2) ^ 2 * (B + 2)
      J.lower.den ≤ 2 ^ E ∧ J.upper.den ≤ 2 ^ E ∧
        Int.natAbs J.lower.num ≤ 3 * 2 ^ (2 * B + E) ∧
        Int.natAbs J.upper.num ≤ 3 * 2 ^ (2 * B + E)) := by
  subst hp
  have hsep : (ofCoeffList cs).Separable := PerfectField.separable_iff_squarefree.mpr hsq
  exact ⟨isolateRootsTotal_aeval_unique hsep,
    isolateRootsTotal_pairwise_lt hsep,
    isolateRootsTotal_pairwise_disjoint hsep,
    ⟨totalIsolatedRoot hsep, isolateRootsTotal_bijective hsep,
      totalIsolatedRoot_strictMono hsep, totalIsolatedRoot_mem hsep⟩,
    isolateRootsTotal_endpoint_bounds_of_bitBound hB⟩

/-! ### `Polynomial ℚ` wrappers -/

/-- Pure list of strictly disjoint isolating rational intervals for `p : ℚ[X]`. -/
noncomputable def isolatePolyRootsTotal (p : ℚ[X]) : List RootInterval :=
  isolateRootsTotal (p.coeffsBelow (p.natDegree + 1))

theorem isolatePolyRootsTotal_eq (p : ℚ[X]) :
    isolatePolyRootsTotal p = isolateRootsTotal (p.coeffsBelow (p.natDegree + 1)) := by rfl

/-- Recovering `p.coeffsBelow (p.natDegree + 1)` from a coefficient list `cs` of length
`p.natDegree + 1` representing `p`. -/
theorem coeffsBelow_eq_of_ofCoeffList {cs : List ℚ} {p : ℚ[X]}
    (hp : ofCoeffList cs = p) (hlen : cs.length = p.natDegree + 1) :
    p.coeffsBelow (p.natDegree + 1) = cs := by
  have heq : ofCoeffList (p.coeffsBelow (p.natDegree + 1)) = ofCoeffList cs := by
    rw [Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree), hp]
  refine List.ext_getElem (by rw [Polynomial.length_coeffsBelow, hlen]) fun i hi1 hi2 => ?_
  simpa only [Polynomial.coeff_ofCoeffList, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2, Option.getD_some] using
    congrArg (fun q : ℚ[X] => q.coeff i) heq

/-- Soundness for `isolatePolyRootsTotal p` on squarefree `p : ℚ[X]`. -/
theorem isolatePolyRootsTotal_isIsolatingFor {p : ℚ[X]} (hsq : Squarefree p) :
    ∀ J ∈ isolatePolyRootsTotal p, J.IsIsolatingFor (p.map (algebraMap ℚ ℝ)) := by
  have heq : ofCoeffList (p.coeffsBelow (p.natDegree + 1)) = p :=
    Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)
  have hmap : p.map (algebraMap ℚ ℝ) =
      (ofCoeffList (p.coeffsBelow (p.natDegree + 1))).map (algebraMap ℚ ℝ) := by rw [heq]
  rw [isolatePolyRootsTotal, hmap]
  exact isolateRootsTotal_isIsolatingFor (polySeparable hsq)

/-- `Polynomial.aeval` soundness for `isolatePolyRootsTotal p` on squarefree `p : ℚ[X]`. -/
theorem isolatePolyRootsTotal_aeval_unique {p : ℚ[X]} (hsq : Squarefree p) :
    ∀ J ∈ isolatePolyRootsTotal p, J.lower ≤ J.upper ∧
      ∃! x : ℝ, x ∈ Set.Icc (J.lower : ℝ) (J.upper : ℝ) ∧ Polynomial.aeval x p = 0 := by
  intro J hJ
  simpa only [Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)] using
    isolateRootsTotal_aeval_unique (polySeparable hsq) J hJ

/-- Strict separation `J₁.upper < J₂.lower` for `isolatePolyRootsTotal p`. -/
theorem isolatePolyRootsTotal_pairwise_lt {p : ℚ[X]} (hsq : Squarefree p) :
    (isolatePolyRootsTotal p).Pairwise (fun J₁ J₂ => J₁.upper < J₂.lower) :=
  isolateRootsTotal_pairwise_lt (polySeparable hsq)

/-- Pairwise disjointness of closed intervals `Set.Icc (J.lower : ℝ) (J.upper : ℝ)` for
`isolatePolyRootsTotal p`. -/
theorem isolatePolyRootsTotal_pairwise_disjoint {p : ℚ[X]} (hsq : Squarefree p) :
    (isolatePolyRootsTotal p).Pairwise
      (Function.onFun Disjoint fun J => Set.Icc (J.lower : ℝ) (J.upper : ℝ)) :=
  isolateRootsTotal_pairwise_disjoint (polySeparable hsq)

/-- The unique real root `x : ℝ` with `Polynomial.aeval x p = 0` inside the `i`-th interval of
`isolatePolyRootsTotal p`. -/
noncomputable def polyTotalIsolatedRoot {p : ℚ[X]} (hsq : Squarefree p)
    (i : Fin (isolatePolyRootsTotal p).length) :
    {x : ℝ // Polynomial.aeval x p = 0} :=
  let r := totalIsolatedRoot (polySeparable hsq) i
  ⟨r.1, by
    have heq : ofCoeffList (p.coeffsBelow (p.natDegree + 1)) = p :=
      Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)
    simpa only [heq] using r.2⟩

/-- Membership of `polyTotalIsolatedRoot hsq i` in the `i`-th closed interval of
`isolatePolyRootsTotal p`. -/
theorem polyTotalIsolatedRoot_mem {p : ℚ[X]} (hsq : Squarefree p)
    (i : Fin (isolatePolyRootsTotal p).length) :
    let J := (isolatePolyRootsTotal p)[i]
    (polyTotalIsolatedRoot hsq i).1 ∈ Set.Icc (J.lower : ℝ) (J.upper : ℝ) :=
  totalIsolatedRoot_mem (polySeparable hsq) i

/-- `polyTotalIsolatedRoot hsq` is strictly increasing across
`Fin (isolatePolyRootsTotal p).length`. -/
theorem polyTotalIsolatedRoot_strictMono {p : ℚ[X]} (hsq : Squarefree p) :
    StrictMono (fun i : Fin (isolatePolyRootsTotal p).length => (polyTotalIsolatedRoot hsq i).1) :=
  totalIsolatedRoot_strictMono (polySeparable hsq)

/-- For every squarefree `p : ℚ[X]`, `polyTotalIsolatedRoot hsq` is a bijection onto
`{x : ℝ // Polynomial.aeval x p = 0}`. -/
theorem isolatePolyRootsTotal_bijective {p : ℚ[X]} (hsq : Squarefree p) :
    Function.Bijective (polyTotalIsolatedRoot hsq) := by
  have hbij := isolateRootsTotal_bijective (polySeparable hsq)
  refine ⟨fun i j hij => ?_, fun ⟨x, hx⟩ => ?_⟩
  · have hv : (polyTotalIsolatedRoot hsq i).1 = (polyTotalIsolatedRoot hsq j).1 :=
      congrArg Subtype.val hij
    exact hbij.1 (Subtype.ext hv)
  · obtain ⟨i, hi⟩ := hbij.2 ⟨x, by rwa [Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self _)]⟩
    exact ⟨i, Subtype.ext (show (polyTotalIsolatedRoot hsq i).1 = x from congrArg Subtype.val hi)⟩

private theorem hasCoeffBitBound_coeffsBelow {B : ℕ} {p : ℚ[X]}
    (hB : ∀ i ≤ p.natDegree, Int.natAbs (p.coeff i).num ≤ 2 ^ B ∧ (p.coeff i).den ≤ 2 ^ B) :
    HasCoeffBitBound B (p.coeffsBelow (p.natDegree + 1)) := by
  intro _ hc
  simp only [Polynomial.coeffsBelow, List.mem_map, List.mem_range] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  exact hB i (Nat.lt_succ_iff.mp hi)

/-- Polynomial dyadic numerator/denominator bounds on all endpoints of `isolatePolyRootsTotal p`
given a bit-length bound `B` on `p`'s coefficients. -/
theorem isolatePolyRootsTotal_endpoint_bounds_of_bitBound {B : ℕ} {p : ℚ[X]}
    (hB : ∀ i ≤ p.natDegree, Int.natAbs (p.coeff i).num ≤ 2 ^ B ∧ (p.coeff i).den ≤ 2 ^ B) :
    ∀ J ∈ isolatePolyRootsTotal p,
      let E := 3 * (p.natDegree + 3) ^ 2 * (B + 2)
      J.lower.den ≤ 2 ^ E ∧ J.upper.den ≤ 2 ^ E ∧
        Int.natAbs J.lower.num ≤ 3 * 2 ^ (2 * B + E) ∧
        Int.natAbs J.upper.num ≤ 3 * 2 ^ (2 * B + E) := fun J hJ => by
  have h := isolateRootsTotal_endpoint_bounds_of_bitBound (hasCoeffBitBound_coeffsBelow hB) J hJ
  rwa [Polynomial.length_coeffsBelow] at h

end Cslib.RealRoot
