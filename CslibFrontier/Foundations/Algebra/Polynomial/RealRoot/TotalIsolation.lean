/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.TotalRatPoly
import CslibFrontier.Algorithms.Lean.TimeM.Simps

/-!
# End-to-End `TimeM`-Charged Real-Root Isolation with Disjoint Isolating Intervals

This module completes the end-to-end `TimeM ℕ`-charged computable Sturm-bisection real-root
isolator `isolateRootsTotalM` (and its pure projection `isolateRootsTotal`, together with
`Polynomial ℚ` wrappers `isolatePolyRootsTotalM` and `isolatePolyRootsTotal`).

Unlike the bisection-only `isolateRootsM` in `Isolation.lean`:
1. **All preprocessing and control operations are charged in `TimeM ℕ`:** `trimM`,
   `sturmSeqListM` (including `derivListM` and Euclidean polynomial divisions), `cauchyBoundNatM`,
   `mignotteBisectionDepthM` (including `lcmDensM`, `clearDenomsListM`, `sqNormListM`, `powNatM`,
   and `clog4M`), midpoint arithmetic, comparisons, variation subtractions, list appends
   (`appendM`), and boundary-disjointness refinement (`separateTouchingM`).
2. **Strictly disjoint closed rational intervals:** adjacent intervals touching at a non-root
   midpoint are separated via `separateTouchingM`, guaranteeing `I₁.upper < I₂.lower` and pairwise
   disjoint closed real intervals `Set.Icc (I.lower : ℝ) (I.upper : ℝ)`.
3. **Complete `aeval` bijection and polynomial bit-parameterized cost bounds:** for every
   squarefree `p : ℚ[X]` (represented computably by any `cs : List ℚ` with `ofCoeffList cs = p`, or
   via `isolatePolyRootsTotal p`), the returned intervals are in strictly monotone bijection with
   `{x : ℝ // Polynomial.aeval x p = 0}`, with proved `TimeM ℕ` operation-count bounds and dyadic
   endpoint numerator/denominator bounds in `(cs.length, B)` under `HasCoeffBitBound B cs`.

**Model boundary note.** `isolateRootsTotalM` and `isolateRootsTotal` on `List ℚ` are executable
(`decide +kernel` / `#eval`), whereas the `Polynomial ℚ` wrappers `isolatePolyRootsTotalM` and
`isolatePolyRootsTotal` are `noncomputable` (inheriting `Polynomial`'s noncomputable `Finsupp`
representation) and measure the `TimeM ℕ` cost of `isolateRootsTotalM` on
`p.coeffsBelow (p.natDegree + 1)` without charging coefficient extraction from `Polynomial ℚ`.
`TimeM ℕ` counts algebraic/RAM operations where primitive `ℚ`, `ℤ`, and `ℕ` scalar operations cost
`O(1)` ticks; compiling Euclidean Sturm remainders to a multi-tape bit-level Turing machine would
additionally track intermediate rational remainder bit-lengths (or use subresultant
pseudo-remainders), whereas all bisection query points and returned interval endpoints here are
dyadic rationals whose bit-lengths are bounded polynomially by `isolateRootsTotal_endpoint_bounds`
and `mignotteBisectionDepth_le_of_bitBound`.

## Main definitions

* `Cslib.RealRoot.refineLeftLoopTotalM`, `Cslib.RealRoot.refineLeftRootTotalM`,
  `Cslib.RealRoot.isolateIocTotalM`: fully step-charged bisection and left-root refinement.
* `Cslib.RealRoot.separateMidLoopM`, `Cslib.RealRoot.separatePairM`,
  `Cslib.RealRoot.separateTouchingM`: `TimeM ℕ`-charged boundary separation producing strictly
  disjoint closed intervals (`I₁.upper < I₂.lower`).
* `Cslib.RealRoot.isolateRootsTotalM`, `Cslib.RealRoot.isolateRootsTotal`,
  `Cslib.RealRoot.totalIsolatedRoot`: computable end-to-end isolator and root bijection on
  `List ℚ`.
* `Cslib.RealRoot.isolatePolyRootsTotalM`, `Cslib.RealRoot.isolatePolyRootsTotal`,
  `Cslib.RealRoot.polyTotalIsolatedRoot`: `Polynomial ℚ` wrappers.

## Main results

* `Cslib.RealRoot.isolateRootsTotal_isIsolatingFor`,
  `Cslib.RealRoot.isolateRootsTotal_pairwise_lt`,
  `Cslib.RealRoot.isolateRootsTotal_pairwise_disjoint`,
  `Cslib.RealRoot.isolateRootsTotal_bijective`: soundness, strict separation, closed-interval
  disjointness, and strictly monotone bijection onto `{x : ℝ // Polynomial.aeval x p = 0}`.
* `Cslib.RealRoot.isolateRootsTotal_endpoint_bounds`: unconditional dyadic numerator/denominator
  bounds on all returned endpoints.
* `Cslib.RealRoot.isolateRootsTotalM_time_le` and
  `Cslib.RealRoot.isolateRootsTotalM_time_le_of_bitBound`: explicit end-to-end `TimeM ℕ` cost
  bounds in `(cs.length, natDegree, mignotteBisectionDepth)` and in `(cs.length, B)`.
* `Cslib.RealRoot.isolatePolyRootsTotal_bijective`,
  `Cslib.RealRoot.isolatePolyRootsTotal_pairwise_disjoint`,
  `Cslib.RealRoot.isolatePolyRootsTotalM_time_le`,
  `Cslib.RealRoot.isolatePolyRootsTotalM_time_le_of_bitBound`: `Polynomial ℚ` theorems.

## References

* [BasuPollackRoy2006] (locator unverified)
* [Mahler1964], pp. 257–262 (locator unverified)
* [Mignotte1982], pp. 259–263 (locator unverified; end-to-end `TimeM ℕ` cost charging and
  `separateTouchingM` boundary refinement are specific to this module)
-/

public section

namespace Cslib.RealRoot

open Polynomial Cslib.Algorithms.Lean

/-! ### Step-charged bisection and left-endpoint refinement -/

/-- Step-charged inner loop shrinking `(u, v]` away from a root at `u`. -/
@[expose] def refineLeftLoopTotalM (t : List ℚ) (seq : List (List ℚ)) :
    ℕ → ℚ → ℚ → ℕ → TimeM ℕ RootInterval
  | 0, u, v, _ => do
    TimeM.tick 1
    pure { lower := u, upper := v }
  | fuel + 1, u, v, vu => do
    TimeM.tick 2
    let m := (u + v) / 2
    let vm ← sturmVariationsListM seq m
    TimeM.tick 1
    if vm = vu then
      pure { lower := m, upper := v }
    else do
      let em ← evalCoeffListM m t
      TimeM.tick 1
      if em = 0 then
        pure { lower := m, upper := m }
      else
        refineLeftLoopTotalM t seq fuel u m vu

@[simp]
theorem refineLeftLoopTotalM_ret (t : List ℚ) (seq : List (List ℚ)) :
    ∀ (fuel : ℕ) (u v : ℚ) (vu : ℕ),
      (refineLeftLoopTotalM t seq fuel u v vu).ret = (refineLeftLoopM t seq fuel u v vu).ret
  | 0, u, v, _ => by
    simp only [refineLeftLoopTotalM, refineLeftLoopM, TimeM.ret_bind, TimeM.ret_pure]
  | fuel + 1, u, v, vu => by
    simp only [refineLeftLoopTotalM, refineLeftLoopM, TimeM.ret_bind, sturmVariationsListM_ret,
      sturmVariationsM_ret]
    split_ifs with hvm
    · simp only [TimeM.ret_pure]
    · simp only [TimeM.ret_bind, evalCoeffListM_ret, evalListM_ret]
      split_ifs with hem
      · simp only [TimeM.ret_pure]
      · exact refineLeftLoopTotalM_ret t seq fuel u ((u + v) / 2) vu

theorem refineLeftLoopTotalM_time_le (t : List ℚ) (seq : List (List ℚ)) :
    ∀ (fuel : ℕ) (u v : ℚ) (vu : ℕ),
      let vCost := 2 * (seq.map List.length).sum + 6 * seq.length + 7
      let eCost := 2 * t.length + 1
      (refineLeftLoopTotalM t seq fuel u v vu).time ≤ fuel * (vCost + eCost + 4) + 1
  | 0, _, _, _ => by simp only [refineLeftLoopTotalM, time_simps, zero_mul, le_refl]
  | fuel + 1, u, v, vu => by
    have hsv := sturmVariationsListM_time_le seq ((u + v) / 2)
    simp only [refineLeftLoopTotalM, time_simps]
    rw [Nat.succ_mul fuel]
    split_ifs
    · simp only [TimeM.time_pure]; omega
    · simp only [time_simps]
      split_ifs
      · simp only [TimeM.time_pure]; omega
      · have ih := refineLeftLoopTotalM_time_le t seq fuel u ((u + v) / 2) vu
        dsimp only at ih
        omega

/-- Step-charged conversion of a half-open isolating interval `(u, v]` into a closed isolating
interval `[a, b] ⊆ [u, v]`. -/
@[expose] def refineLeftRootTotalM (t : List ℚ) (seq : List (List ℚ)) (fuel : ℕ)
    (u v : ℚ) (vu : ℕ) : TimeM ℕ RootInterval := do
  let ev ← evalCoeffListM v t
  TimeM.tick 1
  if ev = 0 then
    pure { lower := v, upper := v }
  else do
    let eu ← evalCoeffListM u t
    TimeM.tick 1
    if eu ≠ 0 then
      pure { lower := u, upper := v }
    else
      refineLeftLoopTotalM t seq fuel u v vu

@[simp, time_simps]
theorem refineLeftRootTotalM_ret (t : List ℚ) (seq : List (List ℚ)) (fuel : ℕ)
    (u v : ℚ) (vu : ℕ) :
    (refineLeftRootTotalM t seq fuel u v vu).ret = (refineLeftRootM t seq fuel u v vu).ret := by
  simp only [refineLeftRootTotalM, refineLeftRootM, time_simps]
  split_ifs with hev
  · simp only [TimeM.ret_pure]
  · simp only [time_simps]
    split_ifs with heu
    · simp only [TimeM.ret_pure]
    · exact refineLeftLoopTotalM_ret t seq fuel u v vu

theorem refineLeftRootTotalM_time_le (t : List ℚ) (seq : List (List ℚ)) (fuel : ℕ)
    (u v : ℚ) (vu : ℕ) :
    let vCost := 2 * (seq.map List.length).sum + 6 * seq.length + 7
    let eCost := 2 * t.length + 1
    (refineLeftRootTotalM t seq fuel u v vu).time ≤
      2 * eCost + 3 + fuel * (vCost + eCost + 4) := by
  simp only [refineLeftRootTotalM, time_simps]
  split_ifs
  · simp only [TimeM.time_pure]; omega
  · simp only [time_simps]
    split_ifs
    · simp only [TimeM.time_pure]; omega
    · have hloop := refineLeftLoopTotalM_time_le t seq fuel u v vu
      dsimp only at hloop
      omega

/-- Step-charged recursive Sturm-count bisection on `(u, v]`, charging arithmetic, comparisons,
and list appends (`appendM`). -/
@[expose] def isolateIocTotalM (t : List ℚ) (seq : List (List ℚ)) (depthBound : ℕ) :
    ℕ → ℚ → ℚ → ℕ → ℕ → TimeM ℕ (List RootInterval)
  | fuel, u, v, vu, vv => do
    TimeM.tick 2
    let count := vu - vv
    if count = 0 then
      pure []
    else do
      TimeM.tick 1
      if count = 1 then do
        let rint ← refineLeftRootTotalM t seq depthBound u v vu
        TimeM.tick 1
        pure [rint]
      else
        match fuel with
        | 0 => do
          TimeM.tick 1
          pure []
        | fuel' + 1 => do
          TimeM.tick 2
          let m := (u + v) / 2
          let vm ← sturmVariationsListM seq m
          let left ← isolateIocTotalM t seq depthBound fuel' u m vu vm
          let right ← isolateIocTotalM t seq depthBound fuel' m v vm vv
          appendM left right

@[simp, time_simps]
theorem isolateIocTotalM_ret (t : List ℚ) (seq : List (List ℚ)) (depthBound : ℕ) :
    ∀ (fuel : ℕ) (u v : ℚ) (vu vv : ℕ),
      (isolateIocTotalM t seq depthBound fuel u v vu vv).ret =
        (isolateIocM t seq depthBound fuel u v vu vv).ret
  | fuel, u, v, vu, vv => by
    unfold isolateIocTotalM isolateIocM
    dsimp only
    simp only [TimeM.ret_bind]
    split_ifs with hc0 hc1
    · simp only [TimeM.ret_pure]
    · simp only [time_simps]
    · cases fuel with
      | zero => simp only [time_simps]
      | succ fuel' =>
        simp only [time_simps, isolateIocTotalM_ret t seq depthBound fuel']

private theorem isolateIocM_length_le {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    (t : List ℚ) (depthBound : ℕ) :
    ∀ (fuel : ℕ) (u v : ℚ) (vu vv : ℕ),
      u ≤ v →
      vu = sturmVariationsList (sturmSeqList cs) u →
      vv = sturmVariationsList (sturmSeqList cs) v →
      ((isolateIocM t (sturmSeqList cs) depthBound fuel u v vu vv).ret).length ≤ vu - vv
  | fuel, u, v, vu, vv, huv, hvu, hvv => by
    unfold isolateIocM
    dsimp only
    split_ifs with hc0 hc1
    · simp only [time_simps, Nat.zero_le]
    · simp only [time_simps, List.length_singleton, hc1, le_refl]
    · cases fuel with
      | zero => simp only [time_simps, Nat.zero_le]
      | succ fuel' =>
        simp only [time_simps, List.length_append]
        have hum : u ≤ (u + v) / 2 := by linarith
        have hmv : (u + v) / 2 ≤ v := by linarith
        have := hvu ▸ sturmVariationsList_antitone hsep hum
        have := hvv ▸ sturmVariationsList_antitone hsep hmv
        have := isolateIocM_length_le hsep t depthBound fuel' u _ vu _ hum hvu rfl
        have := isolateIocM_length_le hsep t depthBound fuel' _ v _ vv hmv rfl hvv
        omega

private theorem sturmVariationsList_le_length (seq : List (List ℚ)) (x : ℚ) :
    sturmVariationsList seq x ≤ seq.length :=
  (Nat.sub_le _ _).trans <| (List.destutter_sublist _ _).length_le.trans <|
    (List.length_filter_le _ _).trans_eq (by simp only [List.length_map])

private theorem isolateIocTotalM_time_le {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    (t : List ℚ) (depthBound : ℕ) :
    ∀ (fuel : ℕ) (u v : ℚ) (vu vv : ℕ),
      u ≤ v →
      vu = sturmVariationsList (sturmSeqList cs) u →
      vv = sturmVariationsList (sturmSeqList cs) v →
      let seq := sturmSeqList cs
      let c := vu - vv
      let vCost := 2 * (seq.map List.length).sum + 6 * seq.length + 7
      let eCost := 2 * t.length + 1
      let sTotal := vCost + seq.length + 10
      let rTotal := 2 * eCost + 6 + depthBound * (vCost + eCost + 4)
      (isolateIocTotalM t seq depthBound fuel u v vu vv).time ≤
        2 + (if c ≤ 1 then 0 else fuel * (c / 2)) * sTotal + c * rTotal
  | fuel, u, v, vu, vv, huv, hvu, hvv => by
    unfold isolateIocTotalM
    simp only [time_simps]
    by_cases hc0 : vu - vv = 0
    · simp only [eq_true hc0, ↓reduceIte, TimeM.time_pure]; omega
    · simp only [eq_false hc0, ↓reduceIte, time_simps]
      by_cases hc1 : vu - vv = 1
      · have href := refineLeftRootTotalM_time_le t (sturmSeqList cs) depthBound u v vu
        dsimp only at href
        simp only [hc1, le_refl, ↓reduceIte, time_simps, zero_mul, one_mul]
        omega
      · simp only [eq_false hc1, show ¬(vu - vv ≤ 1) by omega, ↓reduceIte]
        set seq := sturmSeqList cs
        let vC := 2 * (seq.map List.length).sum + 6 * seq.length + 7
        let eC := 2 * t.length + 1
        let sT := vC + seq.length + 10
        let rT := 2 * eC + 6 + depthBound * (vC + eC + 4)
        cases fuel with
        | zero =>
          have : 2 ≤ (vu - vv) * rT :=
            Nat.mul_le_mul (show 2 ≤ vu - vv by omega) (show 1 ≤ rT by omega)
          simp only [time_simps, zero_mul]
          dsimp only [seq, vC, eC, rT] at this ⊢
          omega
        | succ fuel' =>
          simp only [time_simps]
          let m := (u + v) / 2
          let vm := sturmVariationsList seq m
          have hum : u ≤ m := by dsimp only [m]; linarith
          have hmv : m ≤ v := by dsimp only [m]; linarith
          have : vm ≤ vu := hvu ▸ sturmVariationsList_antitone hsep hum
          have : vv ≤ vm := hvv ▸ sturmVariationsList_antitone hsep hmv
          have hsum_c : (vu - vm) + (vm - vv) = vu - vv := by omega
          have hsv := sturmVariationsListM_time_le seq m
          have hl1 := isolateIocM_length_le hsep t depthBound fuel' u m vu vm hum hvu rfl
          have hl2 : vu ≤ seq.length := hvu ▸ sturmVariationsList_le_length seq u
          have ihL := isolateIocTotalM_time_le hsep t depthBound fuel' u m vu vm hum hvu rfl
          have ihR := isolateIocTotalM_time_le hsep t depthBound fuel' m v vm vv hmv rfl hvv
          have hbudget : ((if vu - vm ≤ 1 then 0 else fuel' * ((vu - vm) / 2)) * sT +
              (if vm - vv ≤ 1 then 0 else fuel' * ((vm - vv) / 2)) * sT + sT) ≤
              (fuel' + 1) * ((vu - vv) / 2) * sT := by
            have hdiv := hsum_c ▸ bisect_split_budget_le fuel' (vu - vm) (vm - vv) (by omega)
            simpa only [add_mul, one_mul] using Nat.mul_le_mul_right sT hdiv
          have hr : (vu - vm) * rT + (vm - vv) * rT = (vu - vv) * rT := by rw [← add_mul, hsum_c]
          dsimp only [seq, m, vm, vC, eC, sT, rT] at ihL ihR hsv hl1 hl2 hbudget hr ⊢
          omega

/-! ### Step-charged boundary separation into strictly disjoint closed intervals -/

/-- Bisect `(a, m]` and `(m, b]` around a non-root midpoint `m` until finding `(u₁', l₂')` with
`u₁' < l₂'`, no roots in `(u₁', m]`, and no roots in `(m, l₂']`. -/
@[expose] def separateMidLoopM (seq : List (List ℚ)) :
    ℕ → ℚ → ℚ → ℚ → ℕ → TimeM ℕ (ℚ × ℚ)
  | 0, a, _, b, _ => do
    TimeM.tick 1
    pure (a, b)
  | fuel + 1, a, m, b, vm => do
    TimeM.tick 2
    let m₁ := (a + m) / 2
    let vm₁ ← sturmVariationsListM seq m₁
    TimeM.tick 1
    if vm₁ = vm then
      pure (m₁, m)
    else do
      TimeM.tick 2
      let m₂ := (m + b) / 2
      let vm₂ ← sturmVariationsListM seq m₂
      TimeM.tick 1
      if vm₂ = vm then
        pure (m, m₂)
      else
        separateMidLoopM seq fuel m₁ m m₂ vm

theorem separateMidLoopM_time_le (seq : List (List ℚ)) :
    ∀ (fuel : ℕ) (a m b : ℚ) (vm : ℕ),
      let vCost := 2 * (seq.map List.length).sum + 6 * seq.length + 7
      (separateMidLoopM seq fuel a m b vm).time ≤ fuel * (2 * vCost + 6) + 1
  | 0, _, _, _, _ => by simp only [separateMidLoopM, time_simps, zero_mul, le_refl]
  | fuel + 1, a, m, b, vm => by
    have hsv1 := sturmVariationsListM_time_le seq ((a + m) / 2)
    have hsv2 := sturmVariationsListM_time_le seq ((m + b) / 2)
    simp only [separateMidLoopM, time_simps]
    rw [Nat.succ_mul fuel]
    split_ifs
    · simp only [TimeM.time_pure]; omega
    · simp only [time_simps]
      split_ifs
      · simp only [TimeM.time_pure]; omega
      · have ih := separateMidLoopM_time_le seq fuel ((a + m) / 2) m ((m + b) / 2) vm
        dsimp only at ih
        omega

private theorem separateMidLoopM_dyadicBounded (seq : List (List ℚ)) :
    ∀ (fuel B e : ℕ) (a m b : ℚ) (vm : ℕ),
      DyadicBounded B e a → DyadicBounded B e m → DyadicBounded B e b →
      let p := (separateMidLoopM seq fuel a m b vm).ret
      DyadicBounded B (e + fuel) p.1 ∧ DyadicBounded B (e + fuel) p.2
  | 0, _, _, _, _, _, _, ha, _, hb => ⟨ha, hb⟩
  | fuel + 1, B, e, a, m, b, vm, ha, hm, hb => by
    simp only [separateMidLoopM, time_simps]
    have hm1 := ha.mid hm
    have hm2 := hm.mid hb
    split_ifs
    · exact ⟨hm1.mono (by omega), hm.mono (by omega)⟩
    · simp only [time_simps]
      split_ifs
      · exact ⟨hm.mono (by omega), hm2.mono (by omega)⟩
      · simpa only [Nat.add_right_comm, Nat.add_assoc] using
          separateMidLoopM_dyadicBounded seq fuel B (e + 1) _ m _ vm hm1 (hm.mono (by omega)) hm2

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

private theorem separateMidLoopM_spec {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    ∀ (fuel depth : ℕ) (a m b : ℚ) (vm : ℕ),
      depth + fuel = mignotteBisectionDepth cs →
      a < m →
      m < b →
      vm = sturmVariationsList (sturmSeqList cs) m →
      sturmVariationsList (sturmSeqList cs) a - vm = 1 →
      vm - sturmVariationsList (sturmSeqList cs) b = 1 →
      ¬((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot (m : ℝ) →
      (b - a : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ depth →
      let res := (separateMidLoopM (sturmSeqList cs) fuel a m b vm).ret
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
    simp only [separateMidLoopM, time_simps]
    split_ifs with h1
    · simp only [TimeM.ret_pure]
      exact ⟨ham1.le, hm1m.le, le_rfl, hmb.le, hm1m,
        fun r h1r' hrm => no_root_Ioc_of_card_eq_zero hsep hm1m.le
          (by rw [← hvm]; dsimp only [m₁]; omega) h1r' hrm,
        fun _ _ _ => by linarith⟩
    · simp only [time_simps]
      split_ifs with h2
      · simp only [TimeM.ret_pure]
        exact ⟨ham.le, le_rfl, hmm2.le, hm2b.le, hmm2, fun _ _ _ => by linarith,
          fun r hmr hrm2 => no_root_Ioc_of_card_eq_zero hsep hmm2.le
            (by rw [← hvm]; dsimp only [m₂]; omega) hmr hrm2⟩
      · have hw_next : (m₂ - m₁ : ℝ) ≤ 2 * (cauchyBoundNat cs : ℝ) / (2 : ℝ) ^ (depth + 1) := by
          have : (m₂ - m₁ : ℝ) = (b - a : ℝ) / 2 := by dsimp only [m₁, m₂]; push_cast; ring
          rw [this, pow_succ, ← div_div]; linarith
        rcases separateMidLoopM_spec hsep fuel (depth + 1) m₁ m m₂ vm (by omega) hm1m hmm2
            hvm (by dsimp only [m₁]; omega) (by dsimp only [m₂]; omega) hnotm hw_next with
          ⟨i1, i2, i3, i4, ilt, in1, in2⟩
        exact ⟨ham1.le.trans i1, i2, i3, i4.trans hm2b.le, ilt, in1, in2⟩

/-- Separate the boundary between two consecutive isolating intervals `I₁` and `I₂` in `TimeM ℕ`,
returning `(u₁', l₂')` with `I₁.lower ≤ u₁' ≤ I₁.upper`, `I₂.lower ≤ l₂' ≤ I₂.upper`, and
`u₁' < l₂'`. -/
@[expose] def separatePairM (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ)
    (I₁ I₂ : RootInterval) : TimeM ℕ (ℚ × ℚ) := do
  TimeM.tick 1
  if I₁.upper < I₂.lower then
    pure (I₁.upper, I₂.lower)
  else do
    let el ← evalCoeffListM I₁.lower t
    TimeM.tick 1
    if el = 0 then
      pure (I₁.lower, I₂.lower)
    else do
      let vm ← sturmVariationsListM seq I₁.upper
      separateMidLoopM seq depth I₁.lower I₁.upper I₂.upper vm

theorem separatePairM_time_le (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ)
    (I₁ I₂ : RootInterval) :
    let vCost := 2 * (seq.map List.length).sum + 6 * seq.length + 7
    let eCost := 2 * t.length + 1
    (separatePairM t seq depth I₁ I₂).time ≤
      eCost + vCost + depth * (2 * vCost + 6) + 3 := by
  simp only [separatePairM, time_simps]
  split_ifs
  · simp only [TimeM.time_pure]; omega
  · simp only [time_simps]
    split_ifs
    · simp only [TimeM.time_pure]; omega
    · simp only [time_simps]
      have := sturmVariationsListM_time_le seq I₁.upper
      have hmid := separateMidLoopM_time_le seq depth I₁.lower I₁.upper I₂.upper
        (sturmVariationsList seq I₁.upper)
      dsimp only at hmid
      omega

private theorem separatePairM_dyadicBounded (t : List ℚ) (seq : List (List ℚ))
    (depth B e : ℕ) (I₁ I₂ : RootInterval)
    (h1l : DyadicBounded B e I₁.lower) (h1u : DyadicBounded B e I₁.upper)
    (h2l : DyadicBounded B e I₂.lower) (h2u : DyadicBounded B e I₂.upper) :
    let p := (separatePairM t seq depth I₁ I₂).ret
    DyadicBounded B (e + depth) p.1 ∧ DyadicBounded B (e + depth) p.2 := by
  simp only [separatePairM, time_simps]
  split_ifs
  · exact ⟨h1u.mono (by omega), h2l.mono (by omega)⟩
  · simp only [time_simps]
    split_ifs
    · exact ⟨h1l.mono (by omega), h2l.mono (by omega)⟩
    · simp only [time_simps]
      exact separateMidLoopM_dyadicBounded seq depth B e I₁.lower I₁.upper I₂.upper _
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

private theorem separatePairM_spec {cs : List ℚ} (hsep : (ofCoeffList cs).Separable)
    {I₁ I₂ : RootInterval}
    (hiso₁ : I₁.IsIsolatingFor ((ofCoeffList cs).map (algebraMap ℚ ℝ)))
    (hiso₂ : I₂.IsIsolatingFor ((ofCoeffList cs).map (algebraMap ℚ ℝ)))
    (hb₁ : -(cauchyBoundNat cs : ℚ) ≤ I₁.lower)
    (hb₂ : I₂.upper ≤ (cauchyBoundNat cs : ℚ))
    (hgap : IntervalGapOk ((ofCoeffList cs).map (algebraMap ℚ ℝ)) I₁ I₂) :
    let res := (separatePairM (trim cs) (sturmSeqList cs) (mignotteBisectionDepth cs) I₁ I₂).ret
    let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
    I₁.lower ≤ res.1 ∧ res.1 ≤ I₁.upper ∧ I₂.lower ≤ res.2 ∧ res.2 ≤ I₂.upper ∧
      res.1 < res.2 ∧
      (∀ r : ℝ, (I₁.lower : ℝ) ≤ r ∧ r ≤ (I₁.upper : ℝ) ∧ pR.IsRoot r → r ≤ (res.1 : ℝ)) ∧
      (∀ r : ℝ, (I₂.lower : ℝ) ≤ r ∧ r ≤ (I₂.upper : ℝ) ∧ pR.IsRoot r → (res.2 : ℝ) ≤ r) := by
  simp only [separatePairM, TimeM.ret_bind]
  split_ifs with hlt
  · exact ⟨hiso₁.1, le_rfl, le_rfl, hiso₂.1, hlt, fun _ h => h.2.1, fun _ h => h.1⟩
  · rcases hgap with hlt' | ⟨heq_m, hnotm⟩
    · exact (hlt hlt').elim
    · simp only [time_simps]
      split_ifs with hel
      · simp only [TimeM.ret_pure]
        have hl_root : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).IsRoot (I₁.lower : ℝ) :=
          IsRoot.def.mpr ((eval_rat_eq_zero_iff cs I₁.lower).mp hel)
        have hl_lt : I₁.lower < I₁.upper :=
          lt_of_le_of_ne hiso₁.1 fun h => hnotm (h ▸ hl_root)
        obtain ⟨_, _, huniq⟩ := hiso₁.2
        refine ⟨le_rfl, hiso₁.1, le_rfl, hiso₂.1, heq_m ▸ hl_lt, fun r hr => ?_, fun _ h => h.1⟩
        rw [huniq r hr, ← huniq _ ⟨le_rfl, Rat.cast_le.mpr hiso₁.1, hl_root⟩]
      · simp only [time_simps]
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
        rcases separateMidLoopM_spec hsep (mignotteBisectionDepth cs) 0 I₁.lower I₁.upper I₂.upper
            _ (Nat.zero_add _) ham hmb rfl hca hcb hnotm hw0 with
          ⟨hm1, hm2, hm3, hm4, hmlt, hno1, hno2⟩
        refine ⟨hm1, hm2, heq_m ▸ hm3, hm4, hmlt,
          fun r ⟨_, hru, hrr⟩ => le_of_not_gt fun hgt => hno1 r hgt hru hrr,
          fun r ⟨hrl, _, hrr⟩ => le_of_not_gt fun hgt =>
            hno2 r (lt_of_le_of_ne (heqR.symm ▸ hrl) fun h => hnotm (h ▸ hrr)) hgt.le hrr⟩

/-- Walk a chain of isolating intervals carrying an updated `curLower` endpoint and separating
every adjacent pair in `TimeM ℕ`. -/
@[expose] def separateChainM (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ)
    (curLower : ℚ) : List RootInterval → TimeM ℕ (List RootInterval)
  | [] => do
    TimeM.tick 1
    pure []
  | [I] => do
    TimeM.tick 1
    pure [{ lower := curLower, upper := I.upper }]
  | I₁ :: I₂ :: rest => do
    let p ← separatePairM t seq depth I₁ I₂
    let tail ← separateChainM t seq depth p.2 (I₂ :: rest)
    TimeM.tick 1
    pure ({ lower := curLower, upper := p.1 } :: tail)

/-- Separate all touching adjacent boundaries in a list of isolating intervals in `TimeM ℕ`. -/
@[expose] def separateTouchingM (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ) :
    List RootInterval → TimeM ℕ (List RootInterval)
  | [] => do
    TimeM.tick 1
    pure []
  | I₀ :: rest => do
    TimeM.tick 1
    separateChainM t seq depth I₀.lower (I₀ :: rest)

@[time_simps]
private theorem separateChainM_length (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ) :
    ∀ (L : List RootInterval) (curLower : ℚ),
      ((separateChainM t seq depth curLower L).ret).length = L.length := by
  time_spec separateChainM

theorem separateTouchingM_length (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ)
    (L : List RootInterval) :
    ((separateTouchingM t seq depth L).ret).length = L.length := by
  time_spec separateTouchingM

private theorem separateChainM_time_le (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ) :
    ∀ (L : List RootInterval) (curLower : ℚ),
      let vCost := 2 * (seq.map List.length).sum + 6 * seq.length + 7
      let eCost := 2 * t.length + 1
      let pCost := eCost + vCost + depth * (2 * vCost + 6) + 4
      (separateChainM t seq depth curLower L).time ≤ L.length * pCost + 1
  | [], _ => by simp only [separateChainM, time_simps, zero_mul, le_refl]
  | [_], _ => by simp only [separateChainM, time_simps, List.length_singleton, one_mul]; omega
  | I₁ :: I₂ :: rest, _ => by
    have hp := separatePairM_time_le t seq depth I₁ I₂
    have ih := separateChainM_time_le t seq depth (I₂ :: rest)
      (separatePairM t seq depth I₁ I₂).ret.2
    dsimp only at hp ih
    simp only [separateChainM, time_simps, List.length_cons] at ih ⊢
    rw [Nat.succ_mul]
    omega

theorem separateTouchingM_time_le (t : List ℚ) (seq : List (List ℚ)) (depth : ℕ)
    (L : List RootInterval) :
    let vCost := 2 * (seq.map List.length).sum + 6 * seq.length + 7
    let eCost := 2 * t.length + 1
    let pCost := eCost + vCost + depth * (2 * vCost + 6) + 4
    (separateTouchingM t seq depth L).time ≤ L.length * pCost + 2 := by
  cases L with
  | nil => simp only [separateTouchingM, time_simps, List.length_nil, zero_mul]; omega
  | cons I₀ rest =>
    have h := separateChainM_time_le t seq depth (I₀ :: rest) I₀.lower
    dsimp only at h
    simp only [separateTouchingM, TimeM.time_bind, TimeM.time_tick]
    omega

private theorem separateChainM_dyadicBounded (t : List ℚ) (seq : List (List ℚ))
    (depth B e : ℕ) :
    ∀ (L : List RootInterval) (curLower : ℚ),
      DyadicBounded B (e + depth) curLower →
      (∀ I ∈ L, DyadicBounded B e I.lower ∧ DyadicBounded B e I.upper) →
      ∀ J ∈ (separateChainM t seq depth curLower L).ret,
        DyadicBounded B (e + depth) J.lower ∧ DyadicBounded B (e + depth) J.upper
  | [], _, _, _ => by
    simp only [separateChainM, time_simps]
    intro _ h; cases h
  | [I], curLower, hcur, hL => by
    simp only [separateChainM, time_simps, List.mem_singleton]
    rintro J rfl
    exact ⟨hcur, (hL I List.mem_cons_self).2.mono (by omega)⟩
  | I₁ :: I₂ :: rest, curLower, hcur, hL => by
    simp only [separateChainM, time_simps, List.mem_cons]
    have h1 := hL I₁ List.mem_cons_self
    have h2 := hL I₂ (List.mem_cons_of_mem I₁ List.mem_cons_self)
    have hp := separatePairM_dyadicBounded t seq depth B e I₁ I₂ h1.1 h1.2 h2.1 h2.2
    rintro J (rfl | hmem)
    · exact ⟨hcur, hp.1⟩
    · exact separateChainM_dyadicBounded t seq depth B e (I₂ :: rest) _ hp.2
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

private theorem separateChainM_spec {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    ∀ (rest : List RootInterval) (I₀ : RootInterval) (curLower : ℚ),
      let pR := (ofCoeffList cs).map (algebraMap ℚ ℝ)
      let b : ℚ := (cauchyBoundNat cs : ℚ)
      (∀ I ∈ I₀ :: rest, I.IsIsolatingFor pR ∧ -b ≤ I.lower ∧ I.upper ≤ b) →
      (I₀ :: rest).Pairwise (IntervalGapOk pR) →
      I₀.lower ≤ curLower →
      (∀ r : ℝ, (I₀.lower : ℝ) ≤ r ∧ r ≤ (I₀.upper : ℝ) ∧ pR.IsRoot r → (curLower : ℝ) ≤ r) →
      let out := (separateChainM (trim cs) (sturmSeqList cs) (mignotteBisectionDepth cs)
        curLower (I₀ :: rest)).ret
      (∃ J₀ Js, out = J₀ :: Js ∧ J₀.lower = curLower) ∧
      out.Pairwise (fun A B => A.upper < B.lower) ∧
      ∀ (k : ℕ) (hk : k < (I₀ :: rest).length),
        let I := (I₀ :: rest)[k]
        let J := out[k]'(by
          rw [separateChainM_length]
          exact hk)
        J.IsIsolatingFor pR ∧ I.lower ≤ J.lower ∧ J.upper ≤ I.upper ∧
          ∀ r : ℝ, ((J.lower : ℝ) ≤ r ∧ r ≤ (J.upper : ℝ) ∧ pR.IsRoot r) ↔
            ((I.lower : ℝ) ≤ r ∧ r ≤ (I.upper : ℝ) ∧ pR.IsRoot r)
  | [], I₀, curLower, hiso_all, _, hcur_le, hcur_root => by
    have h0 := isolating_shrink (hiso_all I₀ List.mem_cons_self).1
      hcur_le le_rfl hcur_root (fun _ h => h.2.1)
    simp only [separateChainM, TimeM.ret_bind, TimeM.ret_pure]
    refine ⟨⟨_, [], rfl, rfl⟩, List.pairwise_singleton _ _, fun k hk => ?_⟩
    obtain rfl : k = 0 := by simp only [List.length_singleton] at hk; omega
    exact h0
  | I₁ :: rest', I₀, curLower, hiso_all, hpw, hcur_le, hcur_root => by
    have hI₀ := hiso_all I₀ List.mem_cons_self
    have hI₁ := hiso_all I₁ (List.mem_cons_of_mem I₀ List.mem_cons_self)
    rcases List.pairwise_cons.mp hpw with ⟨hgap, hpw_tail⟩
    rcases separatePairM_spec hsep hI₀.1 hI₁.1 hI₀.2.1 hI₁.2.2
        (hgap I₁ List.mem_cons_self) with ⟨_, hp2, hp3, _, hplt, hproot1, hproot2⟩
    rcases separateChainM_spec hsep rest' I₁ _
        (fun I hI => hiso_all I (List.mem_cons_of_mem I₀ hI)) hpw_tail hp3 hproot2 with
      ⟨⟨J₁, Js, htail_eq, hJ₁_low⟩, htail_pw, htail_idx⟩
    have hJ₁_le : J₁.lower ≤ J₁.upper := by
      have h0 := (htail_idx 0 (Nat.zero_lt_succ _)).1.1
      simpa only [htail_eq, List.getElem_cons_zero] using h0
    simp only [separateChainM, TimeM.ret_bind, TimeM.ret_pure]
    refine ⟨⟨_, _, rfl, rfl⟩, List.pairwise_cons.mpr ⟨fun B hB => ?_, htail_pw⟩, ?_⟩
    · rw [htail_eq] at hB htail_pw
      rcases List.mem_cons.mp hB with rfl | hBs
      · exact hJ₁_low ▸ hplt
      · exact lt_of_lt_of_le (hJ₁_low ▸ hplt) hJ₁_le |>.trans
          ((List.pairwise_cons.mp htail_pw).1 B hBs)
    · rintro (_ | k') hk
      · exact isolating_shrink hI₀.1 hcur_le hp2 hcur_root hproot1
      · exact htail_idx k' (Nat.lt_of_succ_lt_succ hk)

/-! ### End-to-end `TimeM ℕ`-charged computable isolator -/

/-- End-to-end `TimeM ℕ`-charged computable Sturm-bisection real-root isolator on `List ℚ`,
charging all preprocessing, bisection, left-root refinement, and boundary-disjointness steps. -/
@[expose] def isolateRootsTotalM (cs : List ℚ) : TimeM ℕ (List RootInterval) := do
  let t ← trimM cs
  let emp ← isEmptyM t
  if emp then
    pure []
  else do
    let seq ← sturmSeqListM cs
    let bNat ← cauchyBoundNatM cs
    TimeM.tick 2
    let b : ℚ := (bNat : ℚ)
    let depth ← mignotteBisectionDepthM cs
    let vLeft ← sturmVariationsListM seq (-b)
    let vRight ← sturmVariationsListM seq b
    let raw ← isolateIocTotalM t seq depth depth (-b) b vLeft vRight
    separateTouchingM t seq depth raw

/-- Pure list of strictly disjoint isolating rational intervals returned by `isolateRootsTotalM`. -/
@[expose] def isolateRootsTotal (cs : List ℚ) : List RootInterval :=
  (isolateRootsTotalM cs).ret

@[simp]
theorem isolateRootsTotalM_ret (cs : List ℚ) :
    (isolateRootsTotalM cs).ret = isolateRootsTotal cs := rfl

private theorem isolateRootsTotal_eq_separateTouching (cs : List ℚ) :
    isolateRootsTotal cs =
      (separateTouchingM (trim cs) (sturmSeqList cs) (mignotteBisectionDepth cs)
        (isolateRoots cs)).ret := by
  simp only [isolateRootsTotal, isolateRootsTotalM, isolateRoots, isolateRootsM, time_simps]
  by_cases he : (trim cs).isEmpty = true
  · simp only [he, ↓reduceIte, time_simps, separateTouchingM]
  · simp only [he, Bool.false_eq_true, ↓reduceIte, time_simps]

/-- `isolateRootsTotal cs` has the exact same length as `isolateRoots cs`. -/
theorem isolateRootsTotal_length_eq (cs : List ℚ) :
    (isolateRootsTotal cs).length = (isolateRoots cs).length := by
  rw [isolateRootsTotal_eq_separateTouching, separateTouchingM_length]

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
  | nil => simp only [separateTouchingM, time_simps]; rintro _ ⟨⟩
  | cons I₀ rest =>
    intro J hJ
    have ⟨hlow, hup⟩ := separateChainM_dyadicBounded (trim cs) (sturmSeqList cs)
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
  obtain ⟨I₀, rest, hL⟩ : ∃ I₀ rest, isolateRoots cs = I₀ :: rest := by
    cases h : isolateRoots cs with
    | nil => simp only [h, List.length_nil] at hidx; omega
    | cons I₀ rest => exact ⟨I₀, rest, rfl⟩
  have h := (separateChainM_spec hsep rest I₀ I₀.lower
    (fun I hI => ⟨isolateRoots_isIsolatingFor hsep I (hL ▸ hI),
      isolateRoots_mem_cauchy hsep I (hL ▸ hI)⟩)
    (hL ▸ isolateRoots_intervalGapOk hsep) le_rfl (fun _ h => h.1)).2.2 idx (hL ▸ hidx)
  have htot : isolateRootsTotal cs = (separateChainM (trim cs) (sturmSeqList cs)
      (mignotteBisectionDepth cs) I₀.lower (I₀ :: rest)).ret := by
    simp only [isolateRootsTotal_eq_separateTouching, hL, separateTouchingM, TimeM.ret_bind]
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
    exact (separateChainM_spec hsep rest I₀ I₀.lower
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

/-- Explicit end-to-end `TimeM ℕ` operation-count bound on `isolateRootsTotalM cs` in terms of
`cs.length`, `natDegree`, and `mignotteBisectionDepth cs`. -/
theorem isolateRootsTotalM_time_le {cs : List ℚ} (hsep : (ofCoeffList cs).Separable) :
    let n := cs.length
    let d := (ofCoeffList cs).natDegree
    let k := mignotteBisectionDepth cs
    let vCost := 2 * (d + 1) ^ 2 + 6 * (d + 1) + 7
    let eCost := 2 * (d + 1) + 1
    let prepCost := (n + 2) ^ 2 * (20 * n + 35) + 35 * n + k + 52
    let bisectCost := 2 * vCost + 2 + k * (d / 2) * (vCost + (d + 1) + 10) +
      d * (2 * eCost + 6 + k * (vCost + eCost + 4))
    let sepCost := d * (eCost + vCost + k * (2 * vCost + 6) + 4) + 2
    (isolateRootsTotalM cs).time ≤ prepCost + bisectCost + sepCost := by
  let d := (ofCoeffList cs).natDegree
  let k := mignotteBisectionDepth cs
  let seq := sturmSeqList cs
  let vC := 2 * (seq.map List.length).sum + 6 * seq.length + 7
  let eC := 2 * (trim cs).length + 1
  have htnil : trim cs ≠ [] := fun h =>
    hsep.ne_zero (by simpa only [h, ofCoeffList_nil] using (ofCoeffList_trim cs).symm)
  have hte : (trim cs).isEmpty = false := List.isEmpty_eq_false_iff.mpr htnil
  have ht_deg : (trim cs).length = d + 1 :=
    (ofCoeffList_trim cs ▸ (isTrimmed_trim cs).natDegree_add_one htnil).symm
  have hseq_len : seq.length ≤ d + 1 := sturmSeqList_length_le cs
  have hseq_sum : (seq.map List.length).sum ≤ (d + 1) ^ 2 :=
    (List.sum_le_length_nsmul (seq.map List.length) (d + 1) fun _ hm => by
      obtain ⟨_, hf, rfl⟩ := List.mem_map.mp hm
      exact (sturmSeqList_entry_length_le cs hf).trans (by omega)).trans <| by
        rw [smul_eq_mul, List.length_map, sq]; gcongr
  let b : ℚ := (cauchyBoundNat cs : ℚ)
  have hbb : -b ≤ b := by linarith [show (0 : ℚ) ≤ b from Nat.cast_nonneg _]
  let vL := sturmVariationsList seq (-b)
  let vR := sturmVariationsList seq b
  have hc_le : vL - vR ≤ d := sturmVariationsList_cauchy_sub_le hsep
  have hraw_len : ((isolateIocM (trim cs) seq k k (-b) b vL vR).ret).length ≤ d :=
    (isolateIocM_length_le hsep (trim cs) k k (-b) b vL vR hbb rfl rfl).trans hc_le
  have hsplit_le : (if vL - vR ≤ 1 then 0 else k * ((vL - vR) / 2)) ≤ k * (d / 2) := by
    split_ifs; · exact Nat.zero_le _
    exact Nat.mul_le_mul_left k (Nat.div_le_div_right hc_le)
  have hvL := sturmVariationsListM_time_le seq (-b)
  have hvR := sturmVariationsListM_time_le seq b
  have hbis := isolateIocTotalM_time_le hsep (trim cs) k k (-b) b vL vR hbb rfl rfl
  have hsep_t := separateTouchingM_time_le (trim cs) seq k
    (isolateIocM (trim cs) seq k k (-b) b vL vR).ret
  have := trimM_time_le cs; have := sturmSeqListM_time_le cs
  have := cauchyBoundNatM_time_le cs; have := mignotteBisectionDepthM_time_le cs
  simp only [isolateRootsTotalM, time_simps, hte, Bool.false_eq_true, ↓reduceIte]
  calc _ ≤ ((cs.length + 2) ^ 2 * (20 * cs.length + 35) + 35 * cs.length + k + 52) +
        (2 * vC + 2 + (if vL - vR ≤ 1 then 0 else k * ((vL - vR) / 2)) * (vC + seq.length + 10) +
          (vL - vR) * (2 * eC + 6 + k * (vC + eC + 4))) +
        (((isolateIocM (trim cs) seq k k (-b) b vL vR).ret).length *
          (eC + vC + k * (2 * vC + 6) + 4) + 2) := by
          dsimp only [seq, b, k, vL, vR, vC, eC] at hbis hsep_t hvL hvR ⊢; omega
    _ ≤ _ := by dsimp only [vC, eC]; rw [ht_deg]; gcongr

/-- Squarefree form of `isolateRootsTotalM_time_le`. -/
theorem isolateRootsTotalM_time_le_of_squarefree {cs : List ℚ}
    (hsq : Squarefree (ofCoeffList cs)) :
    let n := cs.length
    let d := (ofCoeffList cs).natDegree
    let k := mignotteBisectionDepth cs
    let vCost := 2 * (d + 1) ^ 2 + 6 * (d + 1) + 7
    let eCost := 2 * (d + 1) + 1
    let prepCost := (n + 2) ^ 2 * (20 * n + 35) + 35 * n + k + 52
    let bisectCost := 2 * vCost + 2 + k * (d / 2) * (vCost + (d + 1) + 10) +
      d * (2 * eCost + 6 + k * (vCost + eCost + 4))
    let sepCost := d * (eCost + vCost + k * (2 * vCost + 6) + 4) + 2
    (isolateRootsTotalM cs).time ≤ prepCost + bisectCost + sepCost :=
  isolateRootsTotalM_time_le (PerfectField.separable_iff_squarefree.mpr hsq)

private theorem totalTime_poly_bound {n d k B : ℕ}
    (hd : d ≤ n) (hk : k ≤ (n + 2) ^ 2 * (B + 2)) :
    let vCost := 2 * (d + 1) ^ 2 + 6 * (d + 1) + 7
    let eCost := 2 * (d + 1) + 1
    let prepCost := (n + 2) ^ 2 * (20 * n + 35) + 35 * n + k + 52
    let bisectCost := 2 * vCost + 2 + k * (d / 2) * (vCost + (d + 1) + 10) +
      d * (2 * eCost + 6 + k * (vCost + eCost + 4))
    let sepCost := d * (eCost + vCost + k * (2 * vCost + 6) + 4) + 2
    prepCost + bisectCost + sepCost ≤ 84 * (n + 2) ^ 5 * (B + 2) := by
  set N := n + 2
  set M := B + 2
  have h2N : 2 ≤ N := by omega
  have h1M : 1 ≤ M := by omega
  have h4 : 4 ≤ N ^ 2 := Nat.pow_le_pow_left h2N 2
  have hN2 : N ≤ N ^ 2 := Nat.le_self_pow (by omega) N
  have hv : 2 * (d + 1) ^ 2 + 6 * (d + 1) + 7 ≤ 10 * N ^ 2 := by
    have : (d + 1) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (by omega) 2; omega
  have he : 2 * (d + 1) + 1 ≤ 3 * N := by omega
  have hp : ∀ {a c : ℕ}, a ≤ 5 → c * 2 ^ (5 - a) * N ^ a ≤ c * N ^ 5 := fun {a c} ha =>
    calc c * 2 ^ (5 - a) * N ^ a ≤ c * N ^ (5 - a) * N ^ a := by gcongr
      _ = c * N ^ 5 := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel ha]
  dsimp only
  calc _ ≤ (N ^ 2 * (20 * N) + 35 * N + N ^ 2 * M + 52) +
          (2 * (10 * N ^ 2) + 2 + N ^ 2 * M * N * (14 * N ^ 2) +
            N * (2 * (3 * N) + 6 + N ^ 2 * M * (14 * N ^ 2))) +
          (N * (3 * N + 10 * N ^ 2 + N ^ 2 * M * (22 * N ^ 2) + 4) + 2) := by
            gcongr <;> omega
    _ = 50 * (N ^ 5 * M) + 20 * N ^ 3 + 10 * N ^ 3 + 29 * N ^ 2 + 45 * N + N ^ 2 * M + 56 := by
          ring
    _ ≤ 50 * (N ^ 5 * M) + 8 * N ^ 5 + 4 * N ^ 5 + 3 * N ^ 5 + N ^ 5 * M + 2 * N ^ 5 := by
          have := hp (a := 3) (c := 8) (by omega)
          have := hp (a := 2) (c := 4) (by omega)
          have := hp (a := 1) (c := 3) (by omega)
          have := hp (a := 0) (c := 2) (by omega)
          have : N ^ 2 * M ≤ N ^ 5 * M :=
            Nat.mul_le_mul_right M (Nat.pow_le_pow_right (by omega) (by omega))
          norm_num at *; omega
    _ ≤ 84 * (N ^ 5 * M) := by
          have : N ^ 5 ≤ N ^ 5 * M := Nat.le_mul_of_pos_right _ h1M
          omega
    _ = 84 * N ^ 5 * M := by ring

/-- Closed-form polynomial operation-count bound on `isolateRootsTotalM cs` purely in terms of
input list length `cs.length` and coefficient bit-length bound `B` (`O(n ^ 5 * (B + 2))`). -/
theorem isolateRootsTotalM_time_le_of_bitBound {B : ℕ} {cs : List ℚ}
    (hsq : Squarefree (ofCoeffList cs)) (hB : HasCoeffBitBound B cs) :
    (isolateRootsTotalM cs).time ≤ 84 * (cs.length + 2) ^ 5 * (B + 2) :=
  (isolateRootsTotalM_time_le_of_squarefree hsq).trans
    (totalTime_poly_bound ((natDegree_ofCoeffList_le cs).trans (Nat.sub_le _ _))
      (mignotteBisectionDepth_le_of_bitBound hB))

/-- Specialization of `isolateRootsTotalM_time_le_of_bitBound` to the computable bound
`coeffBitBound cs`. -/
theorem isolateRootsTotalM_time_le_coeffBitBound {cs : List ℚ}
    (hsq : Squarefree (ofCoeffList cs)) :
    (isolateRootsTotalM cs).time ≤ 84 * (cs.length + 2) ^ 5 * (coeffBitBound cs + 2) :=
  isolateRootsTotalM_time_le_of_bitBound hsq (hasCoeffBitBound_coeffBitBound cs)

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

/-- Combined specification of the computable `TimeM ℕ`-charged isolator `isolateRootsTotalM cs` for
any squarefree `p : ℚ[X]` represented by `cs : List ℚ` (`ofCoeffList cs = p`) with coefficient bit
bound `B`: isolating `aeval` soundness, strict separation `J₁.upper < J₂.lower`, pairwise disjoint
closed real intervals `Set.Icc`, strictly monotone bijection onto
`{x : ℝ // Polynomial.aeval x p = 0}`, polynomial dyadic endpoint numerator/denominator bounds, and
`O(n ^ 5 * (B + 2))` total `TimeM ℕ` operation count. -/
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
        Int.natAbs J.upper.num ≤ 3 * 2 ^ (2 * B + E)) ∧
    (isolateRootsTotalM cs).time ≤ 84 * (cs.length + 2) ^ 5 * (B + 2) := by
  subst hp
  have hsep : (ofCoeffList cs).Separable := PerfectField.separable_iff_squarefree.mpr hsq
  exact ⟨isolateRootsTotal_aeval_unique hsep,
    isolateRootsTotal_pairwise_lt hsep,
    isolateRootsTotal_pairwise_disjoint hsep,
    ⟨totalIsolatedRoot hsep, isolateRootsTotal_bijective hsep,
      totalIsolatedRoot_strictMono hsep, totalIsolatedRoot_mem hsep⟩,
    isolateRootsTotal_endpoint_bounds_of_bitBound hB,
    isolateRootsTotalM_time_le_of_bitBound hsq hB⟩

/-! ### `Polynomial ℚ` wrappers -/

/-- End-to-end `TimeM ℕ`-charged real-root isolation for `p : ℚ[X]` via `Polynomial.coeffsBelow`. -/
noncomputable def isolatePolyRootsTotalM (p : ℚ[X]) : TimeM ℕ (List RootInterval) :=
  isolateRootsTotalM (p.coeffsBelow (p.natDegree + 1))

/-- Pure list of strictly disjoint isolating rational intervals for `p : ℚ[X]`. -/
noncomputable def isolatePolyRootsTotal (p : ℚ[X]) : List RootInterval :=
  (isolatePolyRootsTotalM p).ret

theorem isolatePolyRootsTotalM_eq (p : ℚ[X]) :
    isolatePolyRootsTotalM p = isolateRootsTotalM (p.coeffsBelow (p.natDegree + 1)) := by
  rfl

theorem isolatePolyRootsTotal_eq (p : ℚ[X]) :
    isolatePolyRootsTotal p = isolateRootsTotal (p.coeffsBelow (p.natDegree + 1)) := by
  rfl

/-- Recovering `p.coeffsBelow (p.natDegree + 1)` from a coefficient list `cs` of length
`p.natDegree + 1` representing `p`. -/
theorem coeffsBelow_eq_of_ofCoeffList {cs : List ℚ} {p : ℚ[X]}
    (hp : ofCoeffList cs = p) (hlen : cs.length = p.natDegree + 1) :
    p.coeffsBelow (p.natDegree + 1) = cs := by
  have heq : ofCoeffList (p.coeffsBelow (p.natDegree + 1)) = ofCoeffList cs := by
    rw [Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree), hp]
  refine List.ext_getElem (by rw [Polynomial.length_coeffsBelow, hlen]) fun i hi1 hi2 => ?_
  have hc := congrArg (fun q : ℚ[X] => q.coeff i) heq
  simpa only [Polynomial.coeff_ofCoeffList, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2, Option.getD_some] using hc

@[simp]
theorem isolatePolyRootsTotalM_ret (p : ℚ[X]) :
    (isolatePolyRootsTotalM p).ret = isolatePolyRootsTotal p := by
  rfl

/-- Soundness for `isolatePolyRootsTotal p` on squarefree `p : ℚ[X]`. -/
theorem isolatePolyRootsTotal_isIsolatingFor {p : ℚ[X]} (hsq : Squarefree p) :
    ∀ J ∈ isolatePolyRootsTotal p, J.IsIsolatingFor (p.map (algebraMap ℚ ℝ)) := by
  have heq : ofCoeffList (p.coeffsBelow (p.natDegree + 1)) = p :=
    Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)
  have hmap : p.map (algebraMap ℚ ℝ) =
      (ofCoeffList (p.coeffsBelow (p.natDegree + 1))).map (algebraMap ℚ ℝ) := by rw [heq]
  rw [isolatePolyRootsTotal, isolatePolyRootsTotalM, isolateRootsTotalM_ret, hmap]
  exact isolateRootsTotal_isIsolatingFor (polySeparable hsq)

/-- `Polynomial.aeval` soundness for `isolatePolyRootsTotal p` on squarefree `p : ℚ[X]`. -/
theorem isolatePolyRootsTotal_aeval_unique {p : ℚ[X]} (hsq : Squarefree p) :
    ∀ J ∈ isolatePolyRootsTotal p, J.lower ≤ J.upper ∧
      ∃! x : ℝ, x ∈ Set.Icc (J.lower : ℝ) (J.upper : ℝ) ∧ Polynomial.aeval x p = 0 := by
  have heq : ofCoeffList (p.coeffsBelow (p.natDegree + 1)) = p :=
    Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)
  intro J hJ
  have h := isolateRootsTotal_aeval_unique (polySeparable hsq) J hJ
  simpa only [heq] using h

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

/-- End-to-end `TimeM ℕ` operation-count bound for `isolatePolyRootsTotalM p` on squarefree
`p : ℚ[X]`. -/
theorem isolatePolyRootsTotalM_time_le {p : ℚ[X]} (hsq : Squarefree p) :
    let cs := p.coeffsBelow (p.natDegree + 1)
    let d := p.natDegree
    let k := mignotteBisectionDepth cs
    let vCost := 2 * (d + 1) ^ 2 + 6 * (d + 1) + 7
    let eCost := 2 * (d + 1) + 1
    let prepCost := (d + 3) ^ 2 * (20 * (d + 1) + 35) + 35 * (d + 1) + k + 52
    let bisectCost := 2 * vCost + 2 + k * (d / 2) * (vCost + (d + 1) + 10) +
      d * (2 * eCost + 6 + k * (vCost + eCost + 4))
    let sepCost := d * (eCost + vCost + k * (2 * vCost + 6) + 4) + 2
    (isolatePolyRootsTotalM p).time ≤ prepCost + bisectCost + sepCost := by
  have heq := Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)
  have hle := isolateRootsTotalM_time_le_of_squarefree (heq.symm ▸ hsq)
  dsimp only [isolatePolyRootsTotalM] at hle ⊢
  rw [heq, Polynomial.length_coeffsBelow] at hle
  exact hle

private theorem hasCoeffBitBound_coeffsBelow {B : ℕ} {p : ℚ[X]}
    (hB : ∀ i ≤ p.natDegree, Int.natAbs (p.coeff i).num ≤ 2 ^ B ∧ (p.coeff i).den ≤ 2 ^ B) :
    HasCoeffBitBound B (p.coeffsBelow (p.natDegree + 1)) := by
  intro _ hc
  simp only [Polynomial.coeffsBelow, List.mem_map, List.mem_range] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  exact hB i (Nat.lt_succ_iff.mp hi)

/-- Closed-form polynomial `TimeM ℕ` cost bound on `isolatePolyRootsTotalM p` in terms of
`p.natDegree` and a bound `B` on the numerator/denominator bit-lengths of `p`'s coefficients. -/
theorem isolatePolyRootsTotalM_time_le_of_bitBound {B : ℕ} {p : ℚ[X]}
    (hsq : Squarefree p)
    (hB : ∀ i ≤ p.natDegree, Int.natAbs (p.coeff i).num ≤ 2 ^ B ∧ (p.coeff i).den ≤ 2 ^ B) :
    (isolatePolyRootsTotalM p).time ≤ 84 * (p.natDegree + 3) ^ 5 * (B + 2) := by
  have heq := Polynomial.ofCoeffList_coeffsBelow (Nat.lt_succ_self p.natDegree)
  have h := isolateRootsTotalM_time_le_of_bitBound (heq.symm ▸ hsq)
    (hasCoeffBitBound_coeffsBelow hB)
  rw [Polynomial.length_coeffsBelow] at h
  exact h

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
  rw [Polynomial.length_coeffsBelow] at h
  exact h

end Cslib.RealRoot
