/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Polynomial error functions

Robustness theorems for nonlocal games, low-degree tests and property testing are stated with an
error function: a strategy that wins with probability `1 - ε` is `δ(ε)`-close to an ideal one,
where `δ(ε) = poly(ε)`; the convention `poly(a) ≤ C a^C` is fixed in
[Ji, Natarajan, Vidick, Wright and Yuen, §3, p. 25][JNVWY2020]. The papers never track the
polynomial; they only use that such functions are closed under the operations their proofs
perform. `Cslib.PolyErr δ` is that notion: `|δ x| ≤ C (|x|^lo + |x|^hi)` for some constant `C` and
exponents `0 < lo ≤ hi`. The lower exponent makes `δ` small near `0`, the upper exponent keeps it
polynomially bounded for large arguments, which is what makes the class closed under composition
across fractional powers. This two-exponent formulation is introduced here; it is not taken from
the source.

`PolyErr` is a `fun_prop` predicate. The identity, `√`, `|·|` and positive powers are polynomial
errors, and the class is closed under sums, differences, products, scalar multiples, negation,
`max` and composition, so `fun_prop` proves goals such as
`PolyErr fun ε => 3 * √ε + (ε + √(2 * ε)) ^ 2`. Nonconstant bounds are compared with
`Cslib.PolyErr.mono`, and `Cslib.PolyErr.exists_le` turns a polynomial error back into an explicit
bound `δ ε ≤ C ε^c` on `[0, 1]`.

## Main definitions

* `Cslib.PolyErr`: polynomial error functions.

## Main results

* `Cslib.PolyErr.add`, `Cslib.PolyErr.mul`, `Cslib.PolyErr.comp`, ...: the closure properties,
  registered with `fun_prop`.
* `Cslib.PolyErr.exists_le`: an explicit bound `|δ ε| ≤ C ε^c` on `[0, 1]`.
* `Cslib.PolyErr.tendsto_zero`: a polynomial error tends to `0` at `0`.

## References

* [Z. Ji, A. Natarajan, T. Vidick, J. Wright and H. Yuen, *MIP* = RE*][JNVWY2020]
-/

@[expose] public section

namespace Cslib

open Real

/-- `t^a ≤ t^lo + t^hi` for exponents `0 < lo ≤ a ≤ hi` and `t ≥ 0`. -/
private theorem rpow_le_rpow_add_rpow {t a lo hi : ℝ} (ht : 0 ≤ t) (hlo : 0 < lo) (h₁ : lo ≤ a)
    (h₂ : a ≤ hi) : t ^ a ≤ t ^ lo + t ^ hi := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [zero_rpow (by linarith)]; positivity
  rcases le_total t 1 with h | h
  · linarith [rpow_le_rpow_of_exponent_ge ht h h₁, rpow_nonneg ht.le hi]
  · linarith [rpow_le_rpow_of_exponent_le h h₂, rpow_nonneg ht.le lo]

/-- `(p + q)^a ≤ 2^a (p^a + q^a)` for `p, q ≥ 0` and `a ≥ 0`. -/
private theorem add_rpow_le_two_rpow_mul {p q a : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a) :
    (p + q) ^ a ≤ 2 ^ a * (p ^ a + q ^ a) := by
  wlog h : p ≤ q generalizing p q
  · simpa only [add_comm] using this hq hp (le_of_not_ge h)
  calc (p + q) ^ a ≤ (2 * q) ^ a := rpow_le_rpow (by positivity) (by linarith) ha
    _ = 2 ^ a * q ^ a := mul_rpow (by norm_num) hq
    _ ≤ 2 ^ a * (p ^ a + q ^ a) := by gcongr; linarith [rpow_nonneg hp a]

/-- `f` is bounded by `C (|x|^lo + |x|^hi)` with `0 ≤ C` and `0 < lo ≤ hi`. -/
def PolyErrBound (f : ℝ → ℝ) (C lo hi : ℝ) : Prop :=
  0 ≤ C ∧ 0 < lo ∧ lo ≤ hi ∧ ∀ x, |f x| ≤ C * (|x| ^ lo + |x| ^ hi)

/-- A **polynomial error function**: `|f x| ≤ C (|x|^lo + |x|^hi)` for a constant `C` and
exponents `0 < lo ≤ hi`, the `δ = poly(ε)` of robustness theorems. -/
@[fun_prop]
def PolyErr (f : ℝ → ℝ) : Prop :=
  ∃ C lo hi, PolyErrBound f C lo hi

namespace PolyErrBound

variable {f g : ℝ → ℝ} {C D lo hi lo' hi' : ℝ}

theorem polyErr (h : PolyErrBound f C lo hi) : PolyErr f :=
  ⟨C, lo, hi, h⟩

/-- A bound holds with any wider range of exponents, at twice the constant. -/
theorem widen (h : PolyErrBound f C lo hi) (hlo' : 0 < lo') (hl : lo' ≤ lo) (hh : hi ≤ hi') :
    PolyErrBound f (2 * C) lo' hi' := by
  obtain ⟨hC, hlo, hle, hf⟩ := h
  refine ⟨by positivity, hlo', hl.trans (hle.trans hh), fun x => (hf x).trans ?_⟩
  nlinarith [rpow_le_rpow_add_rpow (abs_nonneg x) hlo' hl (hle.trans hh),
    rpow_le_rpow_add_rpow (abs_nonneg x) hlo' (hl.trans hle) hh]

theorem mono (h : PolyErrBound f C lo hi) (hg : ∀ x, |g x| ≤ |f x|) : PolyErrBound g C lo hi :=
  ⟨h.1, h.2.1, h.2.2.1, fun x => (hg x).trans (h.2.2.2 x)⟩

end PolyErrBound

namespace PolyErr

variable {f g : ℝ → ℝ}

/-- A function dominated by a polynomial error is a polynomial error. -/
theorem mono (hf : PolyErr f) (hg : ∀ x, |g x| ≤ |f x|) : PolyErr g :=
  let ⟨_, _, _, h⟩ := hf; (h.mono hg).polyErr

/-- A nonnegative function below a polynomial error is a polynomial error. -/
theorem of_le (hf : PolyErr f) (hg₀ : ∀ x, 0 ≤ g x) (hg : ∀ x, g x ≤ f x) : PolyErr g :=
  hf.mono fun x => by rw [abs_of_nonneg (hg₀ x)]; exact (hg x).trans (le_abs_self _)

@[fun_prop]
theorem zero : PolyErr fun _ => 0 :=
  ⟨0, 1, 1, le_rfl, one_pos, le_rfl, fun x => by simp⟩

@[fun_prop]
theorem id' : PolyErr fun x => x :=
  ⟨1, 1, 1, zero_le_one, one_pos, le_rfl, fun x => by
    simp only [rpow_one, one_mul]; linarith [abs_nonneg x]⟩

theorem id : PolyErr id :=
  id'

@[fun_prop]
theorem abs (hf : PolyErr f) : PolyErr fun x => |f x| :=
  hf.mono fun x => by rw [abs_abs]

@[fun_prop]
theorem neg (hf : PolyErr f) : PolyErr fun x => -f x :=
  hf.mono fun x => by rw [abs_neg]

@[fun_prop]
theorem const_mul (c : ℝ) (hf : PolyErr f) : PolyErr fun x => c * f x :=
  let ⟨C, lo, hi, _, hlo, hle, h⟩ := hf
  ⟨|c| * C, lo, hi, by positivity, hlo, hle, fun x => by
    rw [abs_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left (h x) (abs_nonneg c)⟩

@[fun_prop]
theorem mul_const (c : ℝ) (hf : PolyErr f) : PolyErr fun x => f x * c := by
  simpa only [mul_comm] using hf.const_mul c

@[fun_prop]
theorem div_const (c : ℝ) (hf : PolyErr f) : PolyErr fun x => f x / c := by
  simpa only [div_eq_mul_inv] using hf.mul_const c⁻¹

@[fun_prop]
theorem add (hf : PolyErr f) (hg : PolyErr g) : PolyErr fun x => f x + g x := by
  obtain ⟨C, lo, hi, hf⟩ := hf; obtain ⟨D, lo', hi', hg⟩ := hg
  have hl := lt_min hf.2.1 hg.2.1
  have hf' := hf.widen hl (min_le_left _ _) (le_max_left hi hi')
  have hg' := hg.widen hl (min_le_right _ _) (le_max_right hi hi')
  exact ⟨2 * C + 2 * D, min lo lo', max hi hi', by linarith [hf'.1, hg'.1], hl,
    (min_le_left _ _).trans (hf.2.2.1.trans (le_max_left _ _)), fun x =>
      (abs_add_le _ _).trans (by linarith [hf'.2.2.2 x, hg'.2.2.2 x])⟩

@[fun_prop]
theorem sub (hf : PolyErr f) (hg : PolyErr g) : PolyErr fun x => f x - g x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

@[fun_prop]
theorem max (hf : PolyErr f) (hg : PolyErr g) : PolyErr fun x => max (f x) (g x) :=
  (hf.abs.add hg.abs).mono fun x => by
    rw [abs_of_nonneg (add_nonneg (abs_nonneg (f x)) (abs_nonneg (g x)))]
    exact abs_max_le_max_abs_abs.trans (max_le (by linarith [abs_nonneg (g x)])
      (by linarith [abs_nonneg (f x)]))

@[fun_prop]
theorem mul (hf : PolyErr f) (hg : PolyErr g) : PolyErr fun x => f x * g x := by
  obtain ⟨C, a, b, hC, ha, hab, hf⟩ := hf
  obtain ⟨D, c, d, hD, hc, hcd, hg⟩ := hg
  refine ⟨4 * (C * D), a + c, b + d, by positivity, by linarith, by linarith, fun x => ?_⟩
  have ht := abs_nonneg x
  have w (u v : ℝ) (h1 : a + c ≤ u + v) (h2 : u + v ≤ b + d) :
      |x| ^ u * |x| ^ v ≤ |x| ^ (a + c) + |x| ^ (b + d) := by
    rw [← rpow_add' ht (by linarith)]
    exact rpow_le_rpow_add_rpow ht (by linarith) h1 h2
  have hprod : (|x| ^ a + |x| ^ b) * (|x| ^ c + |x| ^ d) ≤
      4 * (|x| ^ (a + c) + |x| ^ (b + d)) := by
    linarith [w a c le_rfl (by linarith), w a d (by linarith) (by linarith),
      w b c (by linarith) (by linarith), w b d (by linarith) le_rfl]
  rw [abs_mul]
  calc |f x| * |g x| ≤ (C * (|x| ^ a + |x| ^ b)) * (D * (|x| ^ c + |x| ^ d)) :=
        mul_le_mul (hf x) (hg x) (abs_nonneg _) (by positivity)
    _ = C * D * ((|x| ^ a + |x| ^ b) * (|x| ^ c + |x| ^ d)) := by ring
    _ ≤ C * D * (4 * (|x| ^ (a + c) + |x| ^ (b + d))) := by gcongr
    _ = 4 * (C * D) * (|x| ^ (a + c) + |x| ^ (b + d)) := by ring

@[fun_prop]
theorem pow (hf : PolyErr f) (n : ℕ) [NeZero n] : PolyErr fun x => f x ^ n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  induction n with
  | zero => simpa using hf
  | succ n ih => simpa only [pow_succ] using ih.mul hf

/-- The composition of polynomial errors is a polynomial error. -/
@[fun_prop]
theorem comp {f g : ℝ → ℝ} (hf : PolyErr f) (hg : PolyErr g) : PolyErr fun x => f (g x) := by
  obtain ⟨C, a, b, hC, ha, hab, hf⟩ := hf
  obtain ⟨D, c, d, hD, hc, hcd, hg⟩ := hg
  have key (e : ℝ) (hae : a ≤ e) (heb : e ≤ b) (x : ℝ) :
      |g x| ^ e ≤ (2 * D) ^ e * (2 * (|x| ^ (c * a) + |x| ^ (d * b))) := by
    have he : 0 ≤ e := by linarith
    have ht := abs_nonneg x
    have h₃ := add_rpow_le_two_rpow_mul (rpow_nonneg ht c) (rpow_nonneg ht d) he
    rw [← rpow_mul ht, ← rpow_mul ht] at h₃
    have hlo := mul_pos hc ha
    have h₄ := rpow_le_rpow_add_rpow ht hlo (mul_le_mul_of_nonneg_left hae hc.le)
      (mul_le_mul hcd heb (by linarith) (by linarith))
    have h₅ := rpow_le_rpow_add_rpow ht hlo (mul_le_mul hcd hae ha.le (by linarith))
      (mul_le_mul_of_nonneg_left heb (by linarith))
    calc |g x| ^ e ≤ (D * (|x| ^ c + |x| ^ d)) ^ e := rpow_le_rpow (abs_nonneg _) (hg x) he
      _ = D ^ e * (|x| ^ c + |x| ^ d) ^ e := mul_rpow hD (by positivity)
      _ ≤ D ^ e * (2 ^ e * (|x| ^ (c * e) + |x| ^ (d * e))) := by gcongr
      _ ≤ D ^ e * (2 ^ e * (2 * (|x| ^ (c * a) + |x| ^ (d * b)))) := by gcongr; linarith
      _ = (2 * D) ^ e * (2 * (|x| ^ (c * a) + |x| ^ (d * b))) := by
          rw [mul_rpow (by norm_num) hD]; ring
  refine ⟨C * ((2 * D) ^ a * 2 + (2 * D) ^ b * 2), c * a, d * b, by positivity,
    mul_pos hc ha, mul_le_mul hcd hab ha.le (by linarith), fun x => ?_⟩
  calc |f (g x)| ≤ C * (|g x| ^ a + |g x| ^ b) := hf (g x)
    _ ≤ C * ((2 * D) ^ a * (2 * (|x| ^ (c * a) + |x| ^ (d * b))) +
        (2 * D) ^ b * (2 * (|x| ^ (c * a) + |x| ^ (d * b)))) := by
          gcongr; exacts [key a le_rfl hab x, key b hab le_rfl x]
    _ = C * ((2 * D) ^ a * 2 + (2 * D) ^ b * 2) * (|x| ^ (c * a) + |x| ^ (d * b)) := by ring

/-- `x ↦ |x|^r` is a polynomial error for `r > 0`. -/
theorem abs_rpow {r : ℝ} (hr : 0 < r) : PolyErr fun x => |x| ^ r :=
  ⟨1, r, r, zero_le_one, hr, le_rfl, fun x => by
    rw [abs_of_nonneg (rpow_nonneg (abs_nonneg x) r)]
    linarith [rpow_nonneg (abs_nonneg x) r]⟩

@[fun_prop]
theorem sqrt' : PolyErr Real.sqrt :=
  (abs_rpow (by norm_num : (0 : ℝ) < 1 / 2)).mono fun x => by
    rw [abs_of_nonneg (Real.sqrt_nonneg x), abs_of_nonneg (rpow_nonneg (abs_nonneg x) _),
      ← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt (le_abs_self x)

@[fun_prop]
theorem sqrt (hf : PolyErr f) : PolyErr fun x => √(f x) :=
  sqrt'.comp hf

/-- An explicit bound on `[0, 1]`: `|f ε| ≤ C ε^c` with `c > 0`. -/
theorem exists_le (hf : PolyErr f) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ ε, 0 ≤ ε → ε ≤ 1 → |f ε| ≤ C * ε ^ c := by
  obtain ⟨C, lo, hi, hC, hlo, hle, h⟩ := hf
  refine ⟨2 * C, lo, by positivity, hlo, fun ε h0 h1 => (h ε).trans ?_⟩
  rw [abs_of_nonneg h0]
  rcases h0.eq_or_lt with rfl | hpos
  · simp [zero_rpow hlo.ne', zero_rpow (show hi ≠ 0 by linarith)]
  · nlinarith [rpow_le_rpow_of_exponent_ge hpos h1 hle]

/-- A polynomial error vanishes at `0`. -/
theorem apply_zero (hf : PolyErr f) : f 0 = 0 := by
  obtain ⟨C, lo, hi, -, hlo, hle, h⟩ := hf
  exact abs_nonpos_iff.mp
    (by simpa [zero_rpow hlo.ne', zero_rpow (show hi ≠ 0 by linarith)] using h 0)

/-- A polynomial error tends to `0` at `0`. -/
theorem tendsto_zero (hf : PolyErr f) : Filter.Tendsto f (nhds 0) (nhds 0) := by
  obtain ⟨C, lo, hi, -, hlo, hle, h⟩ := hf
  have hc : Continuous fun x : ℝ => C * (|x| ^ lo + |x| ^ hi) :=
    continuous_const.mul ((continuous_abs.rpow_const fun _ => .inr hlo.le).add
      (continuous_abs.rpow_const fun _ => .inr (by linarith)))
  exact squeeze_zero_norm h
    (by simpa [zero_rpow hlo.ne', zero_rpow (show hi ≠ 0 by linarith)] using hc.tendsto 0)

end PolyErr

end Cslib
