/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.RatPoly
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# Kernel-checked sign conditions for rational polynomials on intervals

For a rational coefficient list `cs` and a closed rational interval `[a, b]`, or a half-line
`[a, ∞)` (`hi = none`), two Boolean checks decide sign conditions of the real polynomial
`p = (ofCoeffList cs).map (algebraMap ℚ ℝ)` on the whole interval from finitely many rational
evaluations of `p`, `p'` and the Sturm sequence `Cslib.RealRoot.sturmSeqList cs`.

* `Cslib.RealRoot.rootFreeOn cs a hi`: `p` has no root on the interval. It checks `p a ≠ 0`,
  `p b ≠ 0` and that the Sturm sign variations agree at `a` and `b`, so that no root lies in
  `(a, b]`.
* `Cslib.RealRoot.nonnegOn cs a hi`: `0 ≤ p` on the interval. It checks `p a ≥ 0`, `p b ≥ 0`,
  that neither endpoint is a multiple root (`p ≠ 0` or `p' ≠ 0` there), that the Sturm count on
  `(a, b]` is `1` if `p b = 0` and `0` otherwise, so that no root lies in the open interval, and
  that `p` is positive at the midpoint. A root of odd multiplicity strictly inside the interval
  changes the sign, so nothing is lost by excluding interior roots; a root of even multiplicity
  inside the interval (a tangency) is rejected, and so is a multiple root at an endpoint.

The Sturm count is the general form of Sturm's theorem,
`Polynomial.sturmVariations_sub_eq_card_roots_Ioc_of_gcd_eval_ne_zero`, which needs no
squarefree hypothesis: it applies because the multiple-root divisor `gcd p p'` does not vanish at
an endpoint where `p` or `p'` does not.

For the half-line, the right endpoint is `b = max (a + 1) B` (or `max a B` for `rootFreeOn`) with
the Cauchy bound `B = Cslib.RealRoot.cauchyBoundNat cs`, beyond which `p` has no root
(`Cslib.RealRoot.abs_lt_cauchyBoundNat_of_isRoot`), and the sign at `b` decides the sign on
`[b, ∞)`.

## Main definitions

* `Cslib.RealRoot.rootFreeOn`, `Cslib.RealRoot.nonnegOn`: the checks.

## Main results

* `Cslib.RealRoot.eval_ne_zero_of_rootFreeOn`, `Cslib.RealRoot.eval_nonneg_of_nonnegOn`: their
  soundness over `ℝ`.
-/

public section

namespace Cslib.RealRoot

open Polynomial Set

/-- The interval `[a, b]`, or `[a, ∞)` when `hi = none`, as a set of reals. -/
@[expose] def bandSet (a : ℚ) (hi : Option ℚ) : Set ℝ :=
  {x | (a : ℝ) ≤ x ∧ ∀ b ∈ hi, x ≤ (b : ℝ)}

/-- The value at `x` of the polynomial with coefficient list `cs`, as a rational. -/
@[expose, reducible] def evalAt (cs : List ℚ) (x : ℚ) : ℚ := evalCoeffList x cs

/-- Whether `x` is not a multiple root of `cs`: the value or the derivative is nonzero there. -/
@[expose] def notMultipleRootAt (cs : List ℚ) (x : ℚ) : Bool :=
  evalAt cs x != 0 || evalAt (CoeffList.deriv cs) x != 0

/-- The check of `rootFreeOn` on a closed interval `[a, b]`. -/
@[expose] def rootFreeIcc (cs : List ℚ) (a b : ℚ) : Bool :=
  let seq := sturmSeqList cs
  decide (a ≤ b) && evalAt cs a != 0 && evalAt cs b != 0 &&
    sturmVariationsList seq a == sturmVariationsList seq b

/-- The check of `nonnegOn` on a closed interval `[a, b]`. -/
@[expose] def nonnegIcc (cs : List ℚ) (a b : ℚ) : Bool :=
  let seq := sturmSeqList cs
  decide (a < b) && decide (0 ≤ evalAt cs a) && decide (0 ≤ evalAt cs b) &&
    notMultipleRootAt cs a && notMultipleRootAt cs b &&
    sturmVariationsList seq a - sturmVariationsList seq b ==
      (if evalAt cs b = 0 then 1 else 0) &&
    decide (0 < evalAt cs ((a + b) / 2))

/-- **No root on an interval.** Whether the polynomial with coefficient list `cs` has no real root
on `[a, b]`, or on `[a, ∞)` when `hi = none`. -/
@[expose] def rootFreeOn (cs : List ℚ) (a : ℚ) : Option ℚ → Bool
  | some b => rootFreeIcc cs a b
  | none => rootFreeIcc cs a (max a (cauchyBoundNat cs))

/-- **Nonnegativity on an interval.** Whether the polynomial with coefficient list `cs` is
nonnegative on `[a, b]`, or on `[a, ∞)` when `hi = none`. -/
@[expose] def nonnegOn (cs : List ℚ) (a : ℚ) : Option ℚ → Bool
  | some b => nonnegIcc cs a b
  | none =>
    let b := max (a + 1) (cauchyBoundNat cs)
    nonnegIcc cs a b && decide (0 < evalAt cs b)

/-! ### Soundness -/

section Soundness

variable {cs : List ℚ}

private noncomputable abbrev realPoly (cs : List ℚ) : ℝ[X] := (ofCoeffList cs).map (algebraMap ℚ ℝ)

private theorem eval_ratCast (cs : List ℚ) (x : ℚ) :
    (realPoly cs).eval (x : ℝ) = (evalAt cs x : ℝ) := by
  rw [show (x : ℝ) = algebraMap ℚ ℝ x from rfl, eval_map, eval₂_hom, eval_ofCoeffList]
  rfl

private theorem ne_zero_of_eval_ne_zero {x : ℚ} (h : evalAt cs x ≠ 0) : (realPoly cs) ≠ 0 := by
  rintro h0
  have := eval_ratCast cs x
  rw [h0, eval_zero] at this
  exact h (by exact_mod_cast this.symm)

private theorem gcd_eval_ne_zero {x : ℚ} (h : notMultipleRootAt cs x = true) :
    (open Classical in
      EuclideanDomain.gcd (realPoly cs) (derivative (realPoly cs))).eval (x : ℝ) ≠ 0 := by
  classical
  intro hg
  simp only [notMultipleRootAt, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  rcases h with h | h
  · obtain ⟨q, hq⟩ := EuclideanDomain.gcd_dvd_left (realPoly cs) (derivative (realPoly cs))
    have h0 : (realPoly cs).eval (x : ℝ) = 0 := by
      convert congrArg (eval (x : ℝ)) hq using 1
      rw [eval_mul, hg, zero_mul]
    rw [eval_ratCast] at h0
    exact h (by exact_mod_cast h0)
  · obtain ⟨q, hq⟩ := EuclideanDomain.gcd_dvd_right (realPoly cs) (derivative (realPoly cs))
    have h0 : (derivative (realPoly cs)).eval (x : ℝ) = 0 := by
      convert congrArg (eval (x : ℝ)) hq using 1
      rw [eval_mul, hg, zero_mul]
    rw [derivative_map, ← CoeffList.ofCoeffList_deriv, eval_ratCast] at h0
    exact h (by exact_mod_cast h0)

/-- The Sturm count on `(a, b]` with endpoints that are not multiple roots. -/
private theorem card_roots_eq {a b : ℚ} (hab : a ≤ b) (hP : (realPoly cs) ≠ 0)
    (ha : notMultipleRootAt cs a = true) (hb : notMultipleRootAt cs b = true) :
    sturmVariationsList (sturmSeqList cs) a - sturmVariationsList (sturmSeqList cs) b =
      ((realPoly cs).roots.toFinset.filter (fun r => (a : ℝ) < r ∧ r ≤ b)).card := by
  rw [sturmVariationsList_eq_sturmVariations, sturmVariationsList_eq_sturmVariations]
  exact sturmVariations_sub_eq_card_roots_Ioc_of_gcd_eval_ne_zero hP (by exact_mod_cast hab)
    (gcd_eval_ne_zero ha) (gcd_eval_ne_zero hb)

private theorem mem_filter_roots {a b : ℚ} (hP : (realPoly cs) ≠ 0) {r : ℝ} (har : (a : ℝ) < r)
    (hrb : r ≤ b) (hr : (realPoly cs).eval r = 0) :
    r ∈ (realPoly cs).roots.toFinset.filter (fun r => (a : ℝ) < r ∧ r ≤ b) := by
  simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hP, IsRoot.def]
  exact ⟨hr, har, hrb⟩

private theorem notMultipleRootAt_of_ne {x : ℚ} (h : evalAt cs x ≠ 0) :
    notMultipleRootAt cs x = true := by
  simp [notMultipleRootAt, h]

/-- An accepted `rootFreeIcc` check: no root on `[a, b]`. -/
private theorem eval_ne_zero_of_rootFreeIcc {a b : ℚ} (h : rootFreeIcc cs a b = true) {x : ℝ}
    (hax : (a : ℝ) ≤ x) (hxb : x ≤ b) : (realPoly cs).eval x ≠ 0 := by
  simp only [rootFreeIcc, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨hab, ha⟩, hb⟩, hV⟩ := h
  have hP := ne_zero_of_eval_ne_zero ha
  intro hx
  rcases hax.eq_or_lt with rfl | hax
  · exact ha (by exact_mod_cast (eval_ratCast cs a).symm.trans hx)
  · have hcard := card_roots_eq hab hP (notMultipleRootAt_of_ne ha) (notMultipleRootAt_of_ne hb)
    rw [hV, Nat.sub_self, eq_comm, Finset.card_eq_zero] at hcard
    exact Finset.notMem_empty x (hcard ▸ mem_filter_roots hP hax hxb hx)

/-- A polynomial without roots on an order-connected set that is positive at one point of it is
positive on all of it. -/
private theorem pos_of_no_root {s : Set ℝ} (hs : s.OrdConnected) {m x : ℝ} (hm : m ∈ s)
    (hx : x ∈ s) (hpm : 0 < (realPoly cs).eval m) (hroot : ∀ y ∈ s, (realPoly cs).eval y ≠ 0) :
    0 < (realPoly cs).eval x := by
  by_contra hneg
  have hx0 : (realPoly cs).eval x < 0 := lt_of_le_of_ne (not_lt.1 hneg) (hroot x hx)
  obtain ⟨c, hc, hc0⟩ := intermediate_value_uIcc (a := x) (b := m)
    (realPoly cs).continuous.continuousOn (mem_uIcc.2 (Or.inl ⟨hx0.le, hpm.le⟩))
  exact hroot c (hs.uIcc_subset hx hm hc) hc0

/-- An accepted `nonnegIcc` check: `0 ≤ p` on `[a, b]`, and `0 < p` on `(a, b)`. -/
private theorem eval_pos_of_nonnegIcc {a b : ℚ} (h : nonnegIcc cs a b = true) {x : ℝ}
    (hax : (a : ℝ) < x) (hxb : x < b) : 0 < (realPoly cs).eval x := by
  simp only [nonnegIcc, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hab, -⟩, -⟩, ha⟩, hb⟩, hV⟩, hmid⟩ := h
  have hP := ne_zero_of_eval_ne_zero hmid.ne'
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  have hcard := card_roots_eq hab.le hP ha hb
  have hroot : ∀ y ∈ Ioo (a : ℝ) b, (realPoly cs).eval y ≠ 0 := by
    rintro y ⟨hay, hyb⟩ hy
    have hy_mem := mem_filter_roots hP hay hyb.le hy
    split_ifs at hV with hb0
    · have hb_mem := mem_filter_roots hP habR le_rfl (by rw [eval_ratCast, hb0, Rat.cast_zero])
      rw [hV] at hcard
      obtain ⟨r, hr⟩ := Finset.card_eq_one.1 hcard.symm
      rw [hr, Finset.mem_singleton] at hy_mem hb_mem
      exact hyb.ne (hy_mem.trans hb_mem.symm)
    · rw [hV, eq_comm, Finset.card_eq_zero] at hcard
      exact Finset.notMem_empty y (hcard ▸ hy_mem)
  refine pos_of_no_root ordConnected_Ioo (m := (((a + b) / 2 : ℚ) : ℝ)) ?_ ⟨hax, hxb⟩
    (by rw [eval_ratCast]; exact_mod_cast hmid) hroot
  push_cast
  constructor <;> linarith

private theorem eval_nonneg_of_nonnegIcc {a b : ℚ} (h : nonnegIcc cs a b = true) {x : ℝ}
    (hax : (a : ℝ) ≤ x) (hxb : x ≤ b) : 0 ≤ (realPoly cs).eval x := by
  have h' := h
  simp only [nonnegIcc, Bool.and_eq_true, decide_eq_true_eq] at h'
  obtain ⟨⟨⟨⟨⟨⟨-, ha⟩, hb⟩, -⟩, -⟩, -⟩, -⟩ := h'
  rcases hax.eq_or_lt with rfl | hax
  · rw [eval_ratCast]; exact_mod_cast ha
  rcases hxb.eq_or_lt with rfl | hxb
  · rw [eval_ratCast]; exact_mod_cast hb
  exact (eval_pos_of_nonnegIcc h hax hxb).le

private theorem le_of_isRoot {x : ℝ} (hP : (realPoly cs) ≠ 0) (hx : (realPoly cs).eval x = 0) :
    x < cauchyBoundNat cs := by
  have hP' : ofCoeffList cs ≠ 0 := fun h0 => hP (by rw [realPoly, h0, Polynomial.map_zero])
  exact (le_abs_self x).trans_lt (abs_lt_cauchyBoundNat_of_isRoot hP' hx)

/-- **Soundness of `rootFreeOn`.** An accepted check proves that the real polynomial has no root
on `[a, b]`, or on `[a, ∞)` when `hi = none`. -/
theorem eval_ne_zero_of_rootFreeOn {a : ℚ} {hi : Option ℚ} (h : rootFreeOn cs a hi = true)
    {x : ℝ} (hx : x ∈ bandSet a hi) : ((ofCoeffList cs).map (algebraMap ℚ ℝ)).eval x ≠ 0 := by
  obtain ⟨hax, hxb⟩ := hx
  cases hi with
  | some b => exact eval_ne_zero_of_rootFreeIcc h hax (hxb b rfl)
  | none =>
    set b : ℚ := max a (cauchyBoundNat cs)
    by_cases hxb : x ≤ b
    · exact eval_ne_zero_of_rootFreeIcc h hax hxb
    · have ha : evalAt cs a ≠ 0 := by
        simp only [rootFreeOn, rootFreeIcc, Bool.and_eq_true, bne_iff_ne] at h
        exact h.1.1.2
      intro hx
      have := le_of_isRoot (ne_zero_of_eval_ne_zero ha) hx
      have hb : ((cauchyBoundNat cs : ℚ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast le_max_right _ _
      push_cast at hb
      linarith [not_le.1 hxb]

/-- **Soundness of `nonnegOn`.** An accepted check proves that the real polynomial is nonnegative
on `[a, b]`, or on `[a, ∞)` when `hi = none`. -/
theorem eval_nonneg_of_nonnegOn {a : ℚ} {hi : Option ℚ} (h : nonnegOn cs a hi = true) {x : ℝ}
    (hx : x ∈ bandSet a hi) : 0 ≤ ((ofCoeffList cs).map (algebraMap ℚ ℝ)).eval x := by
  obtain ⟨hax, hxb⟩ := hx
  cases hi with
  | some b => exact eval_nonneg_of_nonnegIcc h hax (hxb b rfl)
  | none =>
    simp only [nonnegOn, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hI, hb⟩ := h
    set b : ℚ := max (a + 1) (cauchyBoundNat cs)
    by_cases hxb : x ≤ b
    · exact eval_nonneg_of_nonnegIcc hI hax hxb
    · have hP := ne_zero_of_eval_ne_zero hb.ne'
      have hB : ((cauchyBoundNat cs : ℚ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast le_max_right _ _
      push_cast at hB
      refine (pos_of_no_root (s := Ici (b : ℝ)) ordConnected_Ici (m := (b : ℝ)) le_rfl
        (not_le.1 hxb).le (by rw [eval_ratCast]; exact_mod_cast hb) fun y hy hy0 => ?_).le
      linarith [le_of_isRoot hP hy0, mem_Ici.1 hy]

end Soundness

end Cslib.RealRoot
