/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Rectifier
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Order.Filter.AtTopBot.Basic
import Cslib.Foundations.Data.Nat.Asymptotics
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lupanov's asymptotic upper bound for rectifier circuits

The blocked row-pattern construction yields the upper bound of
[Lupanov, section 2°, Theorem 1][Lupanov1956]. For any positive `ε`, a Boolean matrix with `p`
input rows and `q` output columns has a two-layer rectifier circuit with at most
`(1 + ε) * p * q / log₂ p` wires once `p` is large enough and `q` is at least a suitable
constant times `log₂ p`. The threshold is uniform in the matrix. The theorem therefore applies
along any sequences with `p → ∞` and `q / log₂ p → ∞`. A two-layer circuit is a rectifier
`(p, q)`-circuit of rank at most two in Lupanov's sense, as explained in the documentation of
`IsTwoLayer` and of its module, so these are bounds on his `B₂`.

There is a discrepancy in the displayed hypotheses of the available English translation:
Theorem 1 prints `log₂ p / q → ∞`. Here we use `q / log₂ p → ∞`, the regime required to
absorb the final incomplete block in its upper-bound proof. This regime also appears as
`log n ≪ m ≤ n` in [Jukna's account](https://web.vu.lt/mif/s.jukna/boolean/Lupanov-decomposition.html).
The formal statement therefore corrects the displayed condition in that translation; no
claim is made about the wording of the uninspected Russian original.

The source also assumes `p ≥ q`. The upper construction does not need that condition, so it is
omitted here. The counting lower bound and the resulting asymptotic equivalence of Theorem 1
are not proved here; the series is tracked in
[#7621](https://github.com/cslib-community/cslib-frontier/issues/7621).

We use blocks of `s = ⌊log₂ p⌋ - 2 * ⌊log₂ ⌊log₂ p⌋⌋` columns. Their width approaches
`log₂ p`, while their row-pattern output cost is lower order. The numerical estimates are
proved in natural numbers after multiplying by `P * (⌊log₂ p⌋ + 1)`, then converted to the
real logarithm in the final statement.

## Main results

* `Cslib.Circuits.Boolean.Rectifier.exists_depth_two_asymptotic_upper`: uniform thresholds in
  the two matrix dimensions.
* `Cslib.Circuits.Boolean.Rectifier.exists_depth_two_eventually`: the upper bound under the
  corrected growth condition above, with explicit native circuit witnesses.
* `Cslib.Circuits.orDepthComplexity_two_asymptotic_upper`: the same bound for
  `orDepthComplexity 2`, a weaker statement than Lupanov's.

## References

* [O. B. Lupanov, *On rectifier and switching-and-rectifier circuits*][Lupanov1956],
  section 2°, Theorem 1, part 1 of the proof (English translation, PDF p. 3).
* [S. Jukna, *Lupanov's decomposition lemma*](https://web.vu.lt/mif/s.jukna/boolean/Lupanov-decomposition.html),
  the author's companion note to [Jukna2012, Lemma 1.2], for the growth regime.
-/

public section

namespace Cslib.Circuits.Boolean.Rectifier

open Filter

private def blockWidth (p : ℕ) : ℕ :=
  Nat.log2 p - 2 * Nat.log2 (Nat.log2 p)

private theorem pattern_le (c l : ℕ) (hc : 4 * c ≤ l) (hl : 2 * Nat.log2 l ≤ l) :
    c * l * 2 ^ (l - 2 * Nat.log2 l) ≤ 2 ^ l := by
  let a := 2 ^ Nat.log2 l
  have hla : l < 2 * a := by
    simpa [a, pow_succ, Nat.mul_comm] using Nat.lt_log2_self (n := l)
  have hca : 2 * c ≤ a := by omega
  have hpoly : c * l ≤ a ^ 2 := by
    calc
      c * l ≤ c * (2 * a) := Nat.mul_le_mul_left c hla.le
      _ = (2 * c) * a := by ring
      _ ≤ a * a := Nat.mul_le_mul_right a hca
      _ = a ^ 2 := by ring
  calc
    c * l * 2 ^ (l - 2 * Nat.log2 l) ≤ a ^ 2 * 2 ^ (l - 2 * Nat.log2 l) :=
      Nat.mul_le_mul_right _ hpoly
    _ = 2 ^ l := by
      dsimp [a]
      rw [← pow_mul, ← pow_add]
      congr 1
      omega

private theorem scaled_bound (P p q : ℕ) (hP : 0 < P) (hp : 0 < p)
    (hlarge : 32 * P ≤ Nat.log2 p)
    (hlog : 4 * (2 * P + 1) * Nat.log2 (Nat.log2 p) ≤ Nat.log2 p)
    (hq : 8 * P * Nat.log2 p ≤ q) :
    0 < blockWidth p ∧
      P * (Nat.log2 p + 1) *
        ((q ⌈/⌉ blockWidth p) * p + q * 2 ^ (blockWidth p - 1)) ≤
          (P + 1) * p * q := by
  let Q := 2 * P
  let l := Nat.log2 p
  let s := blockWidth p
  have hl2 : 2 ≤ l := by dsimp [l]; omega
  have hll : 1 ≤ Nat.log2 l := (Nat.le_log2 (by omega)).2 (by simpa using hl2)
  change 4 * (Q + 1) * Nat.log2 l ≤ l at hlog
  have hremoved : 2 * Nat.log2 l < l := by dsimp [Q] at hlog; nlinarith
  have hs : 0 < s := by
    dsimp [s, blockWidth]
    exact Nat.sub_pos_of_lt hremoved
  have hsadd : s + 2 * Nat.log2 l = l := Nat.sub_add_cancel hremoved.le
  have hpad : (Q + 1) * (2 * Nat.log2 l) + Q ≤ l := by
    have hQl := Nat.mul_le_mul_left Q hll
    nlinarith only [hlog, hQl]
  have hcoef : Q * (l + 1) ≤ (Q + 1) * s := by
    have hmul := congrArg (fun t => (Q + 1) * t) hsadd
    nlinarith only [hmul, hpad]
  have hL : l + 1 ≤ 2 * l := by omega
  have hcol : 2 * Q * (l + 1) ≤ q := by
    have h := Nat.mul_le_mul_left (2 * Q) hL
    dsimp [Q] at h
    dsimp [l] at h
    dsimp [Q, l]
    nlinarith only [h, hq]
  have hpattern : 2 * Q * (l + 1) * 2 ^ s ≤ p := by
    calc
      2 * Q * (l + 1) * 2 ^ s ≤ 2 * Q * (2 * l) * 2 ^ s :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hL)
      _ = (4 * Q) * l * 2 ^ s := by ring
      _ ≤ 2 ^ l := pattern_le (4 * Q) l (by dsimp [Q, l]; omega) hremoved.le
      _ ≤ p := Nat.log2_self_le hp.ne'
  have hmain : Q * (l + 1) * (q / s * p) ≤ (Q + 1) * p * q := by
    calc
      Q * (l + 1) * (q / s * p) ≤ (Q + 1) * s * (q / s * p) :=
        Nat.mul_le_mul_right _ hcoef
      _ = (Q + 1) * p * (q / s * s) := by ring
      _ ≤ (Q + 1) * p * q := Nat.mul_le_mul_left _ (Nat.div_mul_le_self q s)
  have herr₁ : 2 * Q * (l + 1) * p ≤ p * q := by
    simpa only [Nat.mul_comm p] using Nat.mul_le_mul_left p hcol
  have herr₂ : 2 * Q * (l + 1) * (q * 2 ^ s) ≤ p * q := by
    nlinarith only [Nat.mul_le_mul_right q hpattern]
  have hceil : q ⌈/⌉ s ≤ q / s + 1 :=
    (ceilDiv_le_iff_le_mul hs).2 (Nat.lt_mul_div_succ q hs).le
  have hbudget : (q ⌈/⌉ s) * p + q * 2 ^ (s - 1) ≤ q / s * p + p + q * 2 ^ s := by
    calc
      (q ⌈/⌉ s) * p + q * 2 ^ (s - 1) ≤ (q / s + 1) * p + q * 2 ^ s :=
        Nat.add_le_add (Nat.mul_le_mul_right p hceil)
          (Nat.mul_le_mul_left q (Nat.pow_le_pow_right (by omega) (Nat.sub_le s 1)))
      _ = q / s * p + p + q * 2 ^ s := by ring
  have htotal : Q * (l + 1) * ((q ⌈/⌉ s) * p + q * 2 ^ (s - 1)) ≤
      (Q + 2) * p * q := by
    have h := Nat.mul_le_mul_left (Q * (l + 1)) hbudget
    nlinarith only [h, hmain, herr₁, herr₂]
  refine ⟨hs, ?_⟩
  dsimp [Q, l, s] at htotal
  nlinarith only [htotal]

private theorem eventually_scaled_bound (P : ℕ) (hP : 0 < P) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ p ≥ N, 0 < blockWidth p ∧
      ∀ q, 8 * P * Nat.log2 p ≤ q →
        P * (Nat.log2 p + 1) *
          ((q ⌈/⌉ blockWidth p) * p + q * 2 ^ (blockWidth p - 1)) ≤
            (P + 1) * p * q := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp (Nat.eventually_mul_log2_le (4 * (2 * P + 1)))
  let L := max M (32 * P + 2)
  refine ⟨2 ^ L, ?_, ?_⟩
  · have hL : 1 ≤ L := (by dsimp [L]; omega)
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) hL
  · intro p hp
    have hp0 : 0 < p := (pow_pos (by omega : 0 < 2) L).trans_le hp
    have hl : L ≤ Nat.log2 p := (Nat.le_log2 hp0.ne').2 hp
    have hlarge : 32 * P ≤ Nat.log2 p := by dsimp [L] at hl; omega
    have hlog := hM (Nat.log2 p) ((le_max_left _ _).trans hl)
    refine ⟨(scaled_bound P p (8 * P * Nat.log2 p) hP hp0 hlarge hlog le_rfl).1, ?_⟩
    intro q hq
    exact (scaled_bound P p q hP hp0 hlarge hlog hq).2

/-- The upper bound of [Lupanov1956], section 2°, Theorem 1 (part 1 of the proof; English
translation, PDF p. 3), with thresholds uniform in the matrix: for each `ε > 0`, once `p` is
large enough and `q` is at least a suitable constant times `log₂ p`, every Boolean matrix with
`p` input rows and `q` output columns is computed by a two-layer rectifier circuit with at most
`(1 + ε) * p * q / log₂ p` wires. As for `exists_depth_two`, the witness is a `(p, q)`-circuit
of rank at most two in Lupanov's sense, so the statement bounds his `B₂`.
This uses the growth regime of the upper-bound proof; the English translation displays the
reciprocal condition, as explained in the module documentation.
The source's additional restriction `p ≥ q` is unnecessary for this upper bound. -/
theorem exists_depth_two_asymptotic_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ N K : ℕ, 2 ≤ N ∧ ∀ p ≥ N, ∀ q : ℕ,
      (K : ℝ) * Real.logb 2 p ≤ q → ∀ A : Matrix (Fin p) (Fin q) Bool,
        ∃ c : Circuit signature p q,
          IsTwoLayer c ∧ c.Computes interpretation (matrixAction A) ∧
            (c.program.cost id : ℝ) ≤ (1 + ε) * p * q / Real.logb 2 p := by
  obtain ⟨P, hP⟩ := exists_nat_gt (1 / ε)
  have hP0 : (0 : ℝ) < P := lt_trans (by positivity) hP
  have hPN : 0 < P := by exact_mod_cast hP0
  have hcoef : (P : ℝ) + 1 ≤ (1 + ε) * P := by
    have := (div_lt_iff₀ hε).1 hP
    nlinarith
  obtain ⟨N, hN, hb⟩ := eventually_scaled_bound P hPN
  refine ⟨N, 8 * P, hN, ?_⟩
  intro p hp q hq A
  have hp2 : 2 ≤ p := hN.trans hp
  have hlogpos : 0 < Real.logb 2 p := Real.logb_pos (by norm_num) (by exact_mod_cast hp2)
  have hf : ⌊Real.logb (2 : ℝ) p⌋₊ = Nat.log2 p := by
    simpa only [Nat.cast_ofNat, Nat.log2_eq_log_two] using Real.natFloor_logb_natCast 2 p
  have hfloor : (Nat.log2 p : ℝ) ≤ Real.logb 2 p := by
    rw [← hf]
    exact Nat.floor_le hlogpos.le
  have hceil : Real.logb 2 p ≤ (Nat.log2 p : ℝ) + 1 := by
    rw [← hf]
    exact (Nat.lt_floor_add_one (Real.logb (2 : ℝ) p)).le
  have hqN : 8 * P * Nat.log2 p ≤ q := by
    have hqR : (8 : ℝ) * P * Nat.log2 p ≤ q := by
      exact (mul_le_mul_of_nonneg_left hfloor (by positivity : (0 : ℝ) ≤ 8 * P)).trans
        (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hq)
    exact_mod_cast hqR
  obtain ⟨hs, hbound⟩ := hb p hp
  obtain ⟨c, hl, hc, hw⟩ := exists_depth_two_blocked_exact A hs
  refine ⟨c, hl, hc, ?_⟩
  have hscaled : (P : ℝ) * (Nat.log2 p + 1) * c.program.cost id ≤ (P + 1) * p * q := by
    exact_mod_cast (by rw [hw]; exact hbound q hqN)
  have hcost : (P : ℝ) * Real.logb 2 p * c.program.cost id ≤ (P + 1) * p * q := by
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hceil hP0.le)
      (by positivity)).trans hscaled
  apply (le_div_iff₀ hlogpos).2
  apply (mul_le_mul_iff_right₀ hP0).1
  calc
    (P : ℝ) * (c.program.cost id * Real.logb 2 p) = P * Real.logb 2 p * c.program.cost id := by
      ring
    _ ≤ (P + 1) * p * q := hcost
    _ ≤ P * ((1 + ε) * p * q) := by
      nlinarith only [mul_le_mul_of_nonneg_right hcoef
        (by positivity : (0 : ℝ) ≤ (p : ℝ) * q)]

/-- The upper bound of [Lupanov1956], section 2°, Theorem 1 (part 1 of the proof; English
translation, PDF p. 3), along sequences of matrix dimensions: if `p → ∞` and
`q / log₂ p → ∞`, then eventually every Boolean matrix with `p` input rows and `q` output
columns is computed by a two-layer rectifier circuit with at most `(1 + ε) * p * q / log₂ p`
wires, for the exact real logarithm. As for `exists_depth_two`, the witness is a
`(p, q)`-circuit of rank at most two in Lupanov's sense, so the statement bounds his `B₂`.
The displayed growth hypothesis in the English translation is corrected to the regime required
by its upper-bound proof; see the module documentation for the source discrepancy. -/
theorem exists_depth_two_eventually {p q : ℕ → ℕ}
    (hp : Tendsto p atTop atTop)
    (hq : Tendsto (fun n => (q n : ℝ) / Real.logb 2 (p n)) atTop atTop)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ A : Matrix (Fin (p n)) (Fin (q n)) Bool,
      ∃ c : Circuit signature (p n) (q n),
        IsTwoLayer c ∧ c.Computes interpretation (matrixAction A) ∧
          (c.program.cost id : ℝ) ≤ (1 + ε) * p n * q n / Real.logb 2 (p n) := by
  obtain ⟨N, K, hN, h⟩ := exists_depth_two_asymptotic_upper ε hε
  filter_upwards [hp.eventually_ge_atTop N, hq.eventually_ge_atTop (K : ℝ)] with n hn hqn
  have hlog : 0 < Real.logb 2 (p n) :=
    Real.logb_pos (by norm_num) (by exact_mod_cast hN.trans hn)
  exact h (p n) hn (q n) ((le_div_iff₀ hlog).1 hqn)

end Cslib.Circuits.Boolean.Rectifier

namespace Cslib.Circuits

open Boolean.Rectifier
open scoped Matrix

/-- The asymptotic upper bound for the library's graph measure. This is a weaker statement than
the upper bound of [Lupanov1956], section 2°, Theorem 1, and is not that result: a
`RectifierCircuit` may have edges into input poles and out of output poles, which a
`(p, q)`-circuit may not, so a bound on `orDepthComplexity 2` does not bound Lupanov's `B₂`.
The cited bound is `Cslib.Circuits.Boolean.Rectifier.exists_depth_two_asymptotic_upper`.

For each `ε > 0`, once `p` is large enough and `q` is at least a suitable constant times
`log₂ p`, every Boolean matrix with `q` output rows and `p` input columns, the convention of
`RectifierCircuit.Computes`, has depth-two rectifier complexity at most
`⌊(1 + ε) * p * q / log₂ p⌋`. -/
theorem orDepthComplexity_two_asymptotic_upper (ε : ℝ) (hε : 0 < ε) :
    ∃ N K : ℕ, 2 ≤ N ∧ ∀ p ≥ N, ∀ q : ℕ,
      (K : ℝ) * Real.logb 2 p ≤ q → ∀ A : Matrix (Fin q) (Fin p) Bool,
        orDepthComplexity 2 A ≤ ((⌊(1 + ε) * p * q / Real.logb 2 p⌋₊ : ℕ) : ℕ∞) := by
  obtain ⟨N, K, hN, h⟩ := exists_depth_two_asymptotic_upper ε hε
  refine ⟨N, K, hN, fun p hp q hq A => ?_⟩
  obtain ⟨c, hl, hc, hw⟩ := h p hp q hq Aᵀ
  exact (hl.orDepthComplexity_two_le hc).trans (Nat.cast_le.mpr (Nat.le_floor hw))

end Cslib.Circuits
