/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.ApproxAccel
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.ApproxMain
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Approximate

/-! Tests of the Laurent-polynomial bookkeeping of approximate accelerators (Appendix N of
[AnthropicVPVNP2026]) under ordinary imports:

* constants have order `0`, and orders add under products;
* every Laurent polynomial has a span, and spans multiply;
* the logarithm bound used to choose the scales;
* the coefficient of `ε^0` under the counter, for exponents of both signs;
* the parts of low degree of an approximated polynomial, with an error term of high degree;
* an approximate accelerator (the universal program at `v = 1`) made exact. -/

set_option linter.privateModule false

namespace CslibFrontierTests.ApproxAccel

open Cslib.Circuits.Arithmetic.Separation.Interpreter LaurentPolynomial

/-- Constants have no terms below `ε ^ 0`, and products of such have none either. -/
example (a b : ℤ) :
    OrderGE 0 (algebraMap ℤ ℤ[T;T⁻¹] a * algebraMap ℤ ℤ[T;T⁻¹] b) := by
  simpa using (OrderGE.of_algebraMap (E := ℤ) a).mul (OrderGE.of_algebraMap (E := ℤ) b)

/-- Every Laurent polynomial has exponents within some span. -/
example (P : ℤ[T;T⁻¹]) : ∃ n, Span n P := exists_span P

/-- Spans add under products: `Span 0 1` and `Span n P` give `Span n P`. -/
example (n : ℕ) (P : ℤ[T;T⁻¹]) (h : Span n P) : Span (0 + n) (1 * P) := (Span.one 0).mul h

/-- `4 lg u ≤ lg (u ^ 5)` for `u ≥ 8`. -/
example : 4 * lg 8 ≤ lg (8 ^ 5) := le_lg_four le_rfl

/-- The coefficients of a monomial. -/
theorem coeff_T' (n i : ℤ) : (T n : ℤ[T;T⁻¹]).coeff i = if i = n then 1 else 0 := by
  rw [T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

/-- The span of a monomial `T n` is `|n|`. -/
theorem span_T (n : ℤ) : Span n.natAbs (T n : ℤ[T;T⁻¹]) := fun i hi => by
  rw [coeff_T'] at hi
  split_ifs at hi with h
  · rw [h]
  · exact absurd rfl hi

/-- `coeff_wrap_zero` on `ε⁻¹ + 3 + ε²`, with exponents of both signs: the counter modulo `4` does
not mix up the coefficient of `ε^0`. -/
example : (wrap ℤ 2 (T (-1) + 3 + T 2 : ℤ[T;T⁻¹])).coeff 0 = 3 := by
  have h : Span 2 (T (-1) + 3 + T 2 : ℤ[T;T⁻¹]) :=
    (((span_T (-1)).mono (by norm_num)).add (Span.of_algebraMap (E := ℤ) (3 : ℤ) 2)).add (span_T 2)
  rw [coeff_wrap_zero h (by norm_num)]
  simp

variable (θ : List Bool → ℤ)

open Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree in
/-- The empty tree is a plain sum of one step. -/
theorem plain_nil : Plain θ 1 .nil := by
  have e := Dt.quote (θ := θ) .nil .nil
  have e' : Ev θ (Fm.ofTree (nil : Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree).hd) nil.tl
      [.det 1 .nil] := by
    rw [hd_nil, tl_nil, Fm.ofTree.eq_1]
    exact e
  refine ⟨e'.hl, fun r hr => ?_⟩
  rw [e'.evl, List.mem_singleton] at hr
  subst hr
  simp [Run.det]

/-- The only tree of size `1` is the empty one. -/
theorem eq_nil_of_size_le {z : Tree} (hz : z.size ≤ 1) : z = .nil := by
  cases z with
  | nil => rfl
  | cons a b =>
    cases a <;> cases b <;>
      simp [Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree.size] at hz

/-- A non-vacuous approximate accelerator: at `v = 1` the only instance is the empty tree, which
is plain, and the universal program computes its value with no constants. -/
theorem isAccA_UF (H B : ℕ) : IsAccA (E := ℤ) θ H 1 6 KT.none B UF.code := by
  have h := UF_preA (E := ℤ) θ H 1 B
  rw [one_pow] at h
  refine ⟨fun z hz => ?_, h.val⟩
  obtain rfl := eq_nil_of_size_le (by simpa using hz)
  exact h.run _ hz (by simpa using plain_nil θ)

/-- `prop_approx_acc_exact` turns it into an exact accelerator. -/
example (H : ℕ) : ∃ (t' : ℕ) (K' : KT ℤ) (D' : Tree), IsAccT θ H 1 t' K' 1 D' := by
  obtain ⟨K', D', h, -⟩ := prop_approx_acc_exact (isAccA_UF θ H 0) (J := 3) (m := 0) (W := 0)
    (Δ := 0) (M := 0) (by norm_num) trivial trivial (by norm_num) (by simp) le_rfl
  exact ⟨_, K', D', h⟩

/-- The polynomial `1 + ε X²` agrees with `f = 1` up to `ε`; its error has degree `2 > n = 1`. -/
noncomputable def pε : MvPolynomial (Fin 1 × Option Bool) ℤ[T;T⁻¹] :=
  1 + MvPolynomial.C (T 1) * MvPolynomial.X ((0 : Fin 1), (none : Option Bool)) ^ 2

theorem coeff_pε (e : Fin 1 × Option Bool →₀ ℕ) (i : ℤ) (hi : i ≤ 0) :
    (pε.coeff e).coeff i = if i = 0 then (1 : MvPolynomial (Fin 1 × Option Bool) ℤ).coeff e
      else 0 := by
  have h2 : Finsupp.single ((0 : Fin 1), (none : Option Bool)) 2 ≠ 0 := by simp
  rw [pε, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_X_pow, MvPolynomial.coeff_one, MvPolynomial.coeff_one]
  have h1 : (T 1 : ℤ[T;T⁻¹]).coeff i = 0 := by rw [coeff_T']; simp; omega
  have h0 : (1 : ℤ[T;T⁻¹]).coeff i = if i = 0 then 1 else 0 := by rw [← T_zero, coeff_T']
  split_ifs <;> simp_all

/-- `orderGE_sum_coeff_sub` for `f = 1` and `p = 1 + ε X²`: the error term has degree `2`, above
`n = 1 > d = 0`. -/
example (w : List Bool) :
    OrderGE 1 (∑ i ∈ Finset.range 1, (MvPolynomial.line (codeB ℤ[T;T⁻¹] 1 w) pε).coeff i -
        algebraMap ℤ ℤ[T;T⁻¹] 1) :=
  orderGE_sum_coeff_sub (f := 1) (d := 0) (hp := coeff_pε) (hd := by simp) (hn := by norm_num)
    (hval := by simp)

end CslibFrontierTests.ApproxAccel
