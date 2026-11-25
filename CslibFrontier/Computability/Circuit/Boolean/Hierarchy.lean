/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.PPoly
public import Cslib.Computability.Circuit.Boolean.Shannon
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import CslibFrontier.Foundations.Data.Nat.Asymptotics
import CslibFrontier.Foundations.Data.Nat.IntermediateValue

/-!
# The circuit size hierarchy

Changing one value of a Boolean function on `n` inputs changes its circuit complexity by at most
`2 n + 3` (`complexity_update_le`). Walking from a constant function, which costs exactly one gate
(`complexity_const`), to a hard one, one value at a time, the complexity therefore takes every
value up to the complexity of the hard function, up to `2 n + 3` (`exists_complexity_mem_Ioc`).
With Shannon's lower bound [Shannon1949], every size below `2 ^ n / n` is the complexity of some
function, up to `2 n + 3`, and so more gates allow strictly more languages (`SIZE_ssubset`).
Walking from a constant function to any function `f` shows that `f` costs at most
`2 ^ n (2 n + 3) + 1` gates (`complexity_le_two_pow_mul_add_one`).

## Main results

* `Cslib.Circuits.Boolean.complexity_const`: a constant costs exactly one gate.
* `Cslib.Circuits.Boolean.complexity_update_le`: changing one value costs `2 n + 3` gates.
* `Cslib.Circuits.Boolean.complexity_ite_mem_le`, `Cslib.Circuits.Boolean.complexity_mask_le`,
  `Cslib.Circuits.Boolean.complexity_le_two_pow_mul_add_one`,
  `Cslib.Circuits.Boolean.complexity_le_of_dependsOn`: the sparse and truth-table bounds, for
  finite supports, all functions, and functions depending on few inputs.
* `Cslib.Circuits.Boolean.exists_complexity_mem_Ioc`: complexities below that of a given function
  are attained, up to `2 n + 3`.
* `Cslib.Circuits.Boolean.SIZE_ssubset`: the size hierarchy.
* `Cslib.Circuits.Boolean.SIZE_pow_ssubset`: `SIZE ((n + 1) ^ k) ⊂ SIZE ((n + 1) ^ (k + 1))`.
* `Cslib.Circuits.Boolean.SIZE_sub_ssubset_of_isLittleO`: the hierarchy under the hypotheses of
  [AroraBarak07, Theorem 6.17], with sizes counting input vertices.

## References

* [C. E. Shannon, *The synthesis of two-terminal switching circuits*][Shannon1949]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft
  2007-01-08][AroraBarak07]
-/

public section

namespace Cslib.Circuits.Boolean

open Filter
open scoped Finset

variable {n : ℕ}

/-- Changing one value of a Boolean function costs at most `2 n + 3` gates. -/
theorem complexity_update_le (f : BooleanFunction n) (a : Fin n → Bool) (b : Bool) :
    complexity interpretation (single (Function.update f a b)) ≤
      complexity interpretation (single f) + (2 * n + 3) := by
  let m : BooleanFunction n := fun x => decide ((fun i => x (id i)) = a)
  have hm : complexity interpretation (single m) ≤ 2 * n + 1 :=
    (synthesis_minterm (n := n) id a).complexity_le
  cases b
  · rw [show Function.update f a false = fun x => f x && !m x from
      funext fun x => by by_cases h : x = a <;> simp [h, m]]
    refine (complexity_and_le _ _).trans ?_
    refine (Nat.add_le_add_right (Nat.add_le_add_left (complexity_not_le m) _) _).trans ?_
    omega
  · rw [show Function.update f a true = fun x => f x || m x from
      funext fun x => by by_cases h : x = a <;> simp [h, m]]
    exact (complexity_or_le _ _).trans (by omega)

/-- **Finite override of a constant.** Returning `f x` on a finite set `S` and the constant `c`
outside `S` costs at most `#S * (2 * n + 3) + 1` gates: start from the constant `c` and change
one value in `S` at a time. -/
theorem complexity_ite_mem_le (f : BooleanFunction n) (S : Finset (Fin n → Bool)) (c : Bool) :
    complexity interpretation (single fun x => if x ∈ S then f x else c) ≤
      #S * (2 * n + 3) + 1 := by
  induction S using Finset.induction_on with
  | empty => simpa using (Synthesis.const (n := n) c).complexity_le
  | @insert a S ha ih =>
    rw [show (fun x => if x ∈ insert a S then f x else c) =
        Function.update (fun x => if x ∈ S then f x else c) a (f a) from
      funext fun x => by by_cases hx : x = a <;> simp [hx], Finset.card_insert_of_notMem ha,
      add_one_mul]
    exact (complexity_update_le _ a (f a)).trans (by linarith)

/-- Restricting a Boolean function `f` to `S` and returning `false` outside `S` costs at most
`#S * (2 * n + 3) + 1` gates (`complexity_ite_mem_le` with the constant `false`). -/
theorem complexity_mask_le (f : BooleanFunction n) (S : Finset (Fin n → Bool)) :
    complexity interpretation (single fun x => decide (x ∈ S) && f x) ≤
      #S * (2 * n + 3) + 1 := by
  rw [show (fun x => decide (x ∈ S) && f x) = fun x => if x ∈ S then f x else false from
    funext fun x => by by_cases hx : x ∈ S <;> simp [hx]]
  exact complexity_ite_mem_le f S false

/-- **The truth-table bound.** A Boolean function on `n` inputs costs at most
`2 ^ n * (2 * n + 3) + 1` gates: start from a constant and change one value at a time. -/
theorem complexity_le_two_pow_mul_add_one (f : BooleanFunction n) :
    complexity interpretation (single f) ≤ 2 ^ n * (2 * n + 3) + 1 := by
  classical
  simpa using complexity_mask_le f Finset.univ

/-- A Boolean function that depends only on the inputs in `s` costs at most
`2 ^ #s * (2 * #s + 3) + 1` gates. -/
theorem complexity_le_of_dependsOn {f : BooleanFunction n} {s : Finset (Fin n)}
    (hf : DependsOn f s) : complexity interpretation (single f) ≤ 2 ^ #s * (2 * #s + 3) + 1 := by
  let g : BooleanFunction #s := fun y =>
    f fun i => if h : i ∈ s then y ((s.orderIsoOfFin rfl).symm ⟨i, h⟩) else false
  have hfg : single f = single g ∘ fun x => x ∘ s.orderEmbOfFin rfl := by
    funext x j
    exact hf fun i hi => by
      simp only [dite_eq_left (Finset.mem_coe.1 hi), Function.comp_apply,
        ← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  rw [hfg]
  refine (complexity_comp_le _ _).trans ?_
  rw [complexity_wiring, zero_add]
  exact complexity_le_two_pow_mul_add_one g

/-- A constant function costs exactly one gate: a circuit without gates outputs an input. -/
theorem complexity_const (b : Bool) :
    complexity interpretation (single fun _ : BitString n => b) = 1 := by
  refine le_antisymm (Synthesis.const b).complexity_le (Nat.one_le_iff_ne_zero.2 fun h0 => ?_)
  obtain ⟨c, hc, hsize⟩ := exists_computes_size_eq_complexity (I := interpretation)
    (f := single fun _ : BitString n => b)
  rw [h0] at hsize
  cases hw : c.outputs 0 with
  | input i =>
    have := congrFun (hc fun _ => !b) 0
    simp only [Circuit.eval, Function.comp_apply, hw] at this
    exact Bool.not_ne_self b this
  | gate k => exact (Fin.cast hsize k).elim0

/-- Every complexity below that of a given function is exceeded by at most `2 n + 3` by the
complexity of some function. -/
theorem exists_complexity_mem_Ioc {t : ℕ} (g : BooleanFunction n)
    (hg : t < complexity interpretation (single g)) :
    ∃ f : BooleanFunction n, t < complexity interpretation (single f) ∧
      complexity interpretation (single f) ≤ t + (2 * n + 3) := by
  classical
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact ⟨fun _ => false, by rw [complexity_const]; omega, by rw [complexity_const]; omega⟩
  · exact Nat.exists_lt_le_add_of_update_le (fun f => complexity interpretation (single f))
      complexity_update_le (u := fun _ => false) ((complexity_const false).trans_le ht) hg

/-- **The circuit size hierarchy.** If `s ≤ t`, `t` is positive, eventually
`s n + 2 n + 3 ≤ t n`, and infinitely often `s n < 2 ^ n / n`, then some language has circuits of
size `t` but not of size `s`. -/
theorem SIZE_ssubset {s t : ℕ → ℕ} (hst : s ≤ t) (ht : ∀ n, 1 ≤ t n)
    (hgap : ∀ᶠ n in atTop, s n + (2 * n + 3) ≤ t n)
    (hs : ∃ᶠ n in atTop, (s n : ℝ) < 2 ^ n / n) : SIZE s ⊂ SIZE t := by
  classical
  obtain ⟨N, hN⟩ := Shannon.lt_complexity
  let P n := N ≤ n ∧ s n + (2 * n + 3) ≤ t n ∧ (s n : ℝ) < 2 ^ n / n
  have hf (n) : ∃ f : BooleanFunction n, complexity interpretation (single f) ≤ t n ∧
      (P n → s n < complexity interpretation (single f)) := by
    by_cases hn : P n
    · obtain ⟨g, hg⟩ := hN n hn.1
      obtain ⟨f, hf₁, hf₂⟩ := exists_complexity_mem_Ioc g (mod_cast hn.2.2.trans hg)
      exact ⟨f, hf₂.trans hn.2.1, fun _ => hf₁⟩
    · exact ⟨fun _ => false, (Synthesis.const false).complexity_le.trans (ht n), (absurd · hn)⟩
  choose f hft hfs using hf
  refine ⟨SIZE_mono hst, fun hsub => ?_⟩
  obtain ⟨n, hlt, hn, hgap'⟩ := (hs.and_eventually ((eventually_ge_atTop N).and hgap)).exists
  have hL : Language.ofSlices f ∈ SIZE t := fun m => by rw [Language.slice_ofSlices]; exact hft m
  have := hsub hL n
  rw [Language.slice_ofSlices] at this
  exact (hfs n ⟨hn, hgap', hlt⟩).not_ge this

/-- **The polynomial size hierarchy.** For `k ≥ 1`, circuits of size `(n + 1) ^ (k + 1)` decide
strictly more languages than circuits of size `(n + 1) ^ k`. -/
theorem SIZE_pow_ssubset {k : ℕ} (hk : 1 ≤ k) :
    SIZE (fun n => (n + 1) ^ k) ⊂ SIZE (fun n => (n + 1) ^ (k + 1)) := by
  have hlt : ∀ᶠ n : ℕ in atTop, (((n + 1) ^ k : ℕ) : ℝ) < 2 ^ n / n := by
    filter_upwards [Nat.eventually_add_one_pow_mul_lt_pow k Nat.one_lt_two,
      eventually_ge_atTop 1] with n hn hn1
    exact (lt_div_iff₀ (mod_cast hn1)).mpr (mod_cast hn)
  refine SIZE_ssubset (fun n => Nat.pow_le_pow_right n.succ_pos k.le_succ)
    (fun n => Nat.one_le_pow _ _ n.succ_pos) ?_ hlt.frequently
  filter_upwards [eventually_ge_atTop 3] with n hn
  rw [pow_succ]; nlinarith [Nat.le_self_pow (by omega : k ≠ 0) (n + 1)]

/-- **The circuit size hierarchy under the draft's hypotheses** [AroraBarak07, Theorem 6.17]. If
`n < T n < T' n` for every `n`, eventually `T' n < 2 ^ n / (100 n)`, and `T log T = o(T')`, then
circuits with `T' n` vertices decide strictly more languages than circuits with `T n` vertices.

The draft counts the `n` input vertices in the size of a circuit, so its `SIZE (T(n))` is
`SIZE (fun n => T n - n)` here, under the convention of `SIZE`: the library's circuits may also
use constant gates and need no separate output vertex. The cap `2 ^ n / (100 n) > T'(n)` is
read eventually, as is standard for asymptotic hypotheses: the literal every-`n` reading cannot
hold for `n ≤ 14` and would make the theorem vacuous. The other two bounds are assumed for every
`n`, as printed. The proof reduces to `SIZE_ssubset`: `T log T = o(T')` gives the gap of
`2 n + 3` gates, and the draft's bound keeps `T` below Shannon's `2 ^ n / n`. -/
theorem SIZE_sub_ssubset_of_isLittleO {T T' : ℕ → ℕ} (hT : ∀ n, n < T n)
    (hTT' : ∀ n, T n < T' n) (hT' : ∀ᶠ n in atTop, (T' n : ℝ) < 2 ^ n / (100 * n))
    (hlog : (fun n => (T n : ℝ) * Real.log (T n)) =o[atTop] fun n => (T' n : ℝ)) :
    SIZE (fun n => T n - n) ⊂ SIZE (fun n => T' n - n) := by
  refine SIZE_ssubset (fun n => Nat.sub_le_sub_right (hTT' n).le n)
    (fun n => by have := hT n; have := hTT' n; omega) ?_ ?_
  · filter_upwards [hlog.bound one_pos, eventually_ge_atTop 55] with n hn hn55
    have hT55 : (55 : ℝ) ≤ T n := mod_cast hn55.trans (hT n).le
    have hlog4 : 4 ≤ Real.log (T n) := by
      rw [Real.le_log_iff_exp_le (by linarith), show (4 : ℝ) = (4 : ℕ) * 1 by norm_num,
        Real.exp_nat_mul]
      have : Real.exp 1 ^ 4 < 2.7182818286 ^ 4 :=
        pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by decide)
      linarith [show (2.7182818286 : ℝ) ^ 4 < 55 by norm_num]
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (by linarith)), one_mul,
      Real.norm_of_nonneg (by positivity)] at hn
    have : 4 * T n ≤ T' n := mod_cast (by nlinarith : (4 : ℝ) * T n ≤ T' n)
    have := hT n; omega
  · refine (hT'.and (eventually_ge_atTop 1)).frequently.mono fun n ⟨h, hn⟩ => ?_
    exact (Nat.cast_le.2 ((Nat.sub_le _ _).trans (hTT' n).le)).trans_lt <|
      h.trans_le (div_le_div_of_nonneg_left (by positivity) (mod_cast hn) (by linarith))

end Cslib.Circuits.Boolean
