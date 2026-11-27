/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.ComputedWithin
public import CslibFrontier.Foundations.RingTheory.LaurentSeries

/-!
# Approximate (border) circuits and the class VPBar

A polynomial `P` over `K` is *approximated* by a polynomial `Q` over the Laurent series `K⸨X⸩` in a
parameter `ε` (written `X` for the series) when `Q = P + ε * G` for a polynomial `G` whose
coefficients are power series in `ε` (`Approximates`): no coefficient of `Q` has a term with a
negative power of `ε`, and the terms without `ε` are those of `P`. `P` is *approximated within `s`
nodes* (`ApproximatedWithin`) when such a `Q` is computed within `s` nodes over `K⸨X⸩`, the
circuit's
constants being Laurent series. This is approximative (border) complexity in the form of
[Claude, *VP ≠ VNP over every field*][AnthropicVPVNP2026]. The closure `VPBar K` of
`VP K` consists of the p-families approximated within polynomially many nodes.

The constants of an approximating circuit may be cut off at a high power of `ε`: changing every
constant by terms of order at least `T` changes the computed polynomial only by terms of order at
least `T - B * s`, where `B` bounds the poles of the gate values. So they can be taken to be
Laurent polynomials (`ApproximatedWithin.exists_laurentPolynomial`).

## Main definitions

* `Cslib.Circuits.Arithmetic.Approximates`: `Q = P + ε * G` with power-series coefficients in `G`.
* `Cslib.Circuits.Arithmetic.ApproximatedWithin`: approximation by a circuit with at most `s` nodes.
* `Cslib.Circuits.Arithmetic.VPBar`: the closure of `VP`.

## Main results

* `Cslib.Circuits.Arithmetic.ComputedWithin.approximatedWithin`,
  `Cslib.Circuits.Arithmetic.VP_subset_VPBar`: exact circuits approximate.
* `Cslib.Circuits.Arithmetic.ApproximatedWithin.of_isAffineProjection`: affine projections cost at
  most a factor five.
* `Cslib.Circuits.Arithmetic.ApproximatedWithin.exists_laurentPolynomial`: the constants can be
  taken to be Laurent polynomials.

## References

* [Claude, *VP ≠ VNP over every field*][AnthropicVPVNP2026]
-/

public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial
open scoped LaurentSeries LaurentPolynomial

universe u

variable {K : Type u} [CommRing K] {σ τ : Type*}

/-- `Q`, a polynomial over the Laurent series in `ε`, *approximates* `P`: `Q = P + ε * G` for a
polynomial `G` whose coefficients are power series in `ε`. No coefficient of `Q` has a term with a
negative power of `ε`, and its terms without `ε` are the coefficients of `P`. -/
@[expose] def Approximates (Q : MvPolynomial σ K⸨X⸩) (P : MvPolynomial σ K) : Prop :=
  ∀ (d : σ →₀ ℕ) (i : ℤ), i ≤ 0 → (Q.coeff d).coeff i = if i = 0 then P.coeff d else 0

/-- `P` is *approximated within `s` nodes*: a polynomial approximating `P` is computed within `s`
nodes by a circuit whose constants are Laurent series. -/
@[expose] def ApproximatedWithin (P : MvPolynomial σ K) (s : ℕ) : Prop :=
  ∃ Q : MvPolynomial σ K⸨X⸩, Approximates Q P ∧ ComputedWithin Q s

/-- A polynomial approximates itself. -/
theorem approximates_map_C (P : MvPolynomial σ K) : Approximates (map HahnSeries.C P) P := by
  intro d i hi
  rw [coeff_map, HahnSeries.C_apply, HahnSeries.coeff_single]
  split_ifs <;> rfl

/-- A polynomial computed within `s` nodes is approximated within `s` nodes. -/
theorem ComputedWithin.approximatedWithin {P : MvPolynomial σ K} {s : ℕ}
    (h : ComputedWithin P s) : ApproximatedWithin P s :=
  ⟨_, approximates_map_C P, h.map _⟩

/-- A bound on the number of nodes may be raised. -/
theorem ApproximatedWithin.mono {P : MvPolynomial σ K} {s t : ℕ} (h : ApproximatedWithin P s)
    (hst : s ≤ t) : ApproximatedWithin P t :=
  let ⟨Q, hQ, hc⟩ := h
  ⟨Q, hQ, hc.mono hst⟩

/-- An affine polynomial over `K` stays affine over `K⸨X⸩`. -/
private theorem IsAffine.map_C {P : MvPolynomial σ K} (h : IsAffine P) :
    IsAffine (map (HahnSeries.C : K →+* K⸨X⸩) P) := by
  rcases h with ⟨b, rfl⟩ | ⟨j, a, b, rfl⟩
  · exact Or.inl ⟨HahnSeries.C b, MvPolynomial.map_C _ _⟩
  · exact Or.inr ⟨j, HahnSeries.C a, HahnSeries.C b, by simp⟩

/-- **Affine projections cost at most a factor five** for approximating circuits too: the
substitution is made over `K⸨X⸩`, where it commutes with taking terms of order zero. -/
theorem ApproximatedWithin.of_isAffineProjection {P : MvPolynomial σ K} {Q : MvPolynomial τ K}
    {s : ℕ} (hQ : ApproximatedWithin Q s) (h : IsAffineProjection P Q) :
    ApproximatedWithin P (5 * s) := by
  obtain ⟨ρ, hρ, rfl⟩ := h
  obtain ⟨Q', hQ', hc⟩ := hQ
  refine ⟨_, ?_, ComputedWithin.of_isAffineProjection hc
    ⟨_, fun i => (hρ i).map_C, rfl⟩⟩
  intro d i hi
  classical
  have hsub : Q.support ⊆ Q'.support := fun b hb => mem_support_iff.2 fun h0 =>
    mem_support_iff.1 hb (by simpa [h0] using (hQ' b 0 le_rfl).symm)
  have e1 : (aeval (fun i => map HahnSeries.C (ρ i)) Q').coeff d =
      ∑ b ∈ Q'.support, Q'.coeff b * HahnSeries.C ((aeval ρ (monomial b (1 : K))).coeff d) := by
    conv_lhs => rw [Q'.as_sum, map_sum, coeff_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_one (Q'.coeff b), ← C_mul_monomial, map_mul, aeval_C, algebraMap_eq, coeff_C_mul,
      mul_one, ← coeff_map, aeval_monomial, aeval_monomial, map_one, map_one, one_mul, one_mul,
      map_finsuppProd]
    simp only [map_pow]
  have e2 : (aeval ρ Q).coeff d =
      ∑ b ∈ Q'.support, Q.coeff b * (aeval ρ (monomial b (1 : K))).coeff d := by
    conv_lhs => rw [Q.as_sum, map_sum, coeff_sum]
    rw [Finset.sum_subset hsub fun b _ hb => by
      simp [notMem_support_iff.1 hb]]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_one (Q.coeff b), ← C_mul_monomial, map_mul, aeval_C, algebraMap_eq, coeff_C_mul,
      mul_one]
  have e3 (a : K⸨X⸩) (r : K) : (a * HahnSeries.C r).coeff i = a.coeff i * r := by
    rw [mul_comm, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, mul_comm]
  rw [e1, HahnSeries.coeff_sum]
  simp only [e3, hQ' _ i hi]
  split_ifs with h0
  · exact e2.symm
  · simp

/-! ### The closure of VP -/

/-- The closure `VPBar K` of `VP K` [Claude, *VP ≠ VNP over every field*][AnthropicVPVNP2026]:
the p-families whose members are approximated within a polynomially bounded number of nodes. -/
@[expose] def VPBar (K : Type u) [CommRing K] : Set (PolynomialFamily K) :=
  {f | f.IsPFamily ∧ ∃ b : ℕ → ℕ, PolynomiallyBounded b ∧ ∀ n, ApproximatedWithin (f.poly n) (b n)}

/-- `VP` is contained in its closure. -/
theorem VP_subset_VPBar : VP K ⊆ VPBar K := fun f hf => by
  obtain ⟨hp, b, hb, h⟩ := mem_VP_iff.1 hf
  exact ⟨hp, b, hb, fun n => (h n).approximatedWithin⟩

/-! ### Truncating the constants -/

section Truncate

/-- No coefficient of `u` has a term below `ε ^ t`. -/
private def OrdGe (t : ℤ) (u : MvPolynomial σ K⸨X⸩) : Prop :=
  ∀ (d : σ →₀ ℕ) (i : ℤ), i < t → (u.coeff d).coeff i = 0

private theorem OrdGe.mono {t t' : ℤ} {u : MvPolynomial σ K⸨X⸩} (h : OrdGe t u) (ht : t' ≤ t) :
    OrdGe t' u :=
  fun d i hi => h d i (by omega)

private theorem OrdGe.add {t : ℤ} {u v : MvPolynomial σ K⸨X⸩} (hu : OrdGe t u) (hv : OrdGe t v) :
    OrdGe t (u + v) :=
  fun d i hi => by
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, HahnSeries.coeff_add, hu d i hi, hv d i hi,
      add_zero]

private theorem OrdGe.mul {t t' : ℤ} {u v : MvPolynomial σ K⸨X⸩} (hu : OrdGe t u)
    (hv : OrdGe t' v) : OrdGe (t + t') (u * v) := fun d i hi => by
  classical
  rw [coeff_mul, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  have h := (Finset.mem_antidiagonal.1 hij).2.2
  by_cases h1 : ij.1 < t
  · rw [hu x.1 _ h1, zero_mul]
  · rw [hv x.2 ij.2 (by omega), mul_zero]

private theorem ordGe_zero (t : ℤ) : OrdGe t (0 : MvPolynomial σ K⸨X⸩) :=
  fun d i _ => by simp

/-- A constant polynomial has no terms below the order of the constant. -/
private theorem ordGe_C {t : ℤ} {a : K⸨X⸩} (ha : ∀ i < t, a.coeff i = 0) :
    OrdGe t (C a : MvPolynomial σ K⸨X⸩) := fun d i hi => by
  classical
  rw [coeff_C]
  split_ifs
  exacts [ha i hi, rfl]

/-- A variable has no terms below `ε ^ 0`. -/
private theorem ordGe_X (j : σ) : OrdGe 0 (X j : MvPolynomial σ K⸨X⸩) := fun d i hi => by
  classical
  rw [coeff_X]
  split_ifs
  · simp [HahnSeries.coeff_one, hi.ne]
  · rfl

/-- Every polynomial over `K⸨X⸩` has bounded poles. -/
private theorem exists_ordGe (u : MvPolynomial σ K⸨X⸩) : ∃ B : ℤ, 0 ≤ B ∧ OrdGe (-B) u := by
  induction u using MvPolynomial.induction_on' with
  | monomial e a =>
    refine ⟨|a.order|, abs_nonneg _, fun d i hi => ?_⟩
    classical
    rw [coeff_monomial]
    split_ifs
    exacts [HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hi (neg_abs_le _)), rfl]
  | add p q hp hq =>
    obtain ⟨B, hB, h⟩ := hp
    obtain ⟨B', hB', h'⟩ := hq
    exact ⟨B + B', by omega, (h.mono (by omega)).add (h'.mono (by omega))⟩

/-- Renaming the variables keeps the orders of the coefficients. -/
private theorem OrdGe.rename {t : ℤ} {u : MvPolynomial σ K⸨X⸩} (h : OrdGe t u) (f : σ → τ) :
    OrdGe t (rename f u) := by
  classical
  rw [u.as_sum, map_sum]
  refine Finset.sum_induction _ (OrdGe t) (fun _ _ => OrdGe.add) (ordGe_zero t) fun e _ => ?_
  rw [rename_monomial]
  intro d i hi
  rw [coeff_monomial]
  split_ifs
  exacts [h e i hi, rfl]

variable {n g : ℕ}

/-- A constant truncated below `ε ^ T`. -/
private noncomputable def truncate (T : ℤ) (a : K⸨X⸩) : K[T;T⁻¹] :=
  (LaurentSeries.exists_laurentPolynomial_coeff_eq a T).choose

private theorem coeff_truncate {T : ℤ} (a : K⸨X⸩) {i : ℤ} (hi : i < T) :
    (LaurentPolynomial.toLaurentSeries (truncate T a)).coeff i = a.coeff i :=
  (LaurentSeries.exists_laurentPolynomial_coeff_eq a T).choose_spec i hi

/-- The position of a wire in the program order: inputs first, then the gates. -/
private def wireIndex : Wire n g → ℕ
  | .input _ => 0
  | .gate k => k + 1

/-- **Truncation along a program.** Truncating the constants of a program below `ε ^ T` changes
the value of a wire `w` only by terms of order at least `T - B * wireIndex w`, when `B ≥ 0` bounds
the poles of all exact gate values and `T ≥ B * (g + 1)`. -/
private theorem ordGe_trace_sub (p : Program (arithSignature K⸨X⸩) n g) {B T : ℤ} (hB : 0 ≤ B)
    (hT : B * (g + 1) ≤ T)
    (hpole : ∀ k, OrdGe (-B) (p.trace (arithInterpretationWith _ C) X (.gate k))) (w : Wire n g) :
    OrdGe (T - B * wireIndex w)
      (p.trace (arithInterpretationWith _ (C ∘ LaurentPolynomial.toLaurentSeries ∘ truncate T)) X
          w -
        p.trace (arithInterpretationWith _ C) X w) := by
  set I := arithInterpretationWith K⸨X⸩ (C : K⸨X⸩ → MvPolynomial (Fin n) K⸨X⸩)
  set J := arithInterpretationWith K⸨X⸩
    (C ∘ LaurentPolynomial.toLaurentSeries ∘ truncate T : K⸨X⸩ → MvPolynomial (Fin n) K⸨X⸩)
  have hpole' (w : Wire n g) : OrdGe (-B) (p.trace I X w) := by
    cases w with
    | input i => exact (ordGe_X i).mono (by omega)
    | gate k => exact hpole k
  refine p.wire_induction
    (P := fun w => OrdGe (T - B * wireIndex w) (p.trace J X w - p.trace I X w))
    (fun i => by simpa only [Program.trace_input, sub_self] using ordGe_zero _) (fun k ih => ?_) w
  have hk : ∀ a, OrdGe (T - B * k)
      (p.trace J X ((p.lines k).wires a) - p.trace I X ((p.lines k).wires a)) := fun a => by
    refine (ih a).mono ?_
    cases hw : (p.lines k).wires a with
    | input i => simp only [wireIndex, Nat.cast_zero, mul_zero, sub_zero]; nlinarith
    | gate j =>
      have : ((j : ℕ) + 1 : ℤ) ≤ k := mod_cast p.lt_of_lines_wires_eq_gate k a j hw
      simp only [wireIndex]
      push_cast; nlinarith
  have hkg : (k : ℤ) < g := by exact_mod_cast k.isLt
  rw [p.trace_gate, p.trace_gate]
  generalize p.lines k = line at hk
  obtain ⟨op, wires⟩ := line
  cases op with
  | add =>
    change OrdGe _ ((_ + _) - (_ + _))
    rw [add_sub_add_comm]
    exact ((hk 0).add (hk 1)).mono (by simp only [wireIndex]; push_cast; nlinarith)
  | mul =>
    change OrdGe _ (_ * _ - _ * _)
    set a₀ := p.trace I X (wires 0)
    set a₁ := p.trace I X (wires 1)
    rw [show p.trace J X (wires 0) * p.trace J X (wires 1) - a₀ * a₁ =
      (p.trace J X (wires 0) - a₀) * a₁ + a₀ * (p.trace J X (wires 1) - a₁) +
        (p.trace J X (wires 0) - a₀) * (p.trace J X (wires 1) - a₁) by ring]
    simp only [wireIndex]
    push_cast
    refine (((hk 0).mul (hpole' _)).mono ?_ |>.add (((hpole' _).mul (hk 1)).mono ?_)).add
      (((hk 0).mul (hk 1)).mono ?_) <;> nlinarith
  | const a =>
    change OrdGe _ (C (LaurentPolynomial.toLaurentSeries (truncate T a)) - C a)
    rw [← map_sub]
    refine (ordGe_C fun i hi => ?_).mono (by simp only [wireIndex]; push_cast; nlinarith)
    rw [HahnSeries.coeff_sub, coeff_truncate a hi, sub_self]

/-- **The constants of an approximating circuit can be taken to be Laurent polynomials.** A
polynomial approximated within `s` nodes is approximated within `s` nodes by a circuit whose
constants are Laurent polynomials in `ε`. -/
theorem ApproximatedWithin.exists_laurentPolynomial {P : MvPolynomial σ K} {s : ℕ}
    (h : ApproximatedWithin P s) :
    ∃ Q : MvPolynomial σ K[T;T⁻¹], ComputedWithin Q s ∧
      Approximates (map LaurentPolynomial.toLaurentSeries Q) P := by
  obtain ⟨_, hQ, n, x, c, hs, rfl⟩ := h
  set I := arithInterpretationWith K⸨X⸩ (C : K⸨X⸩ → MvPolynomial (Fin n) K⸨X⸩)
  choose B hB hBk using fun k => exists_ordGe (c.program.trace I X (.gate k))
  set B₀ : ℤ := ∑ k, B k
  have hB₀ : 0 ≤ B₀ := Finset.sum_nonneg fun k _ => hB k
  have hpole (k : Fin c.size) : OrdGe (-B₀) (c.program.trace I X (.gate k)) :=
    (hBk k).mono (neg_le_neg (Finset.single_le_sum (fun k _ => hB k) (Finset.mem_univ k)))
  set T : ℤ := B₀ * (c.size + 1) + 1
  have herr := ordGe_trace_sub c.program hB₀ (le_of_lt (lt_add_one _)) hpole (c.outputs 0)
  refine ⟨rename x ((c.mapOp (ArithOp.map (truncate T))).polynomial 0), ⟨n, x, _, hs, rfl⟩,
    fun d i hi => ?_⟩
  have e :
      map LaurentPolynomial.toLaurentSeries ((c.mapOp (ArithOp.map (truncate T))).polynomial 0) =
      c.polynomial 0 + (c.program.trace (arithInterpretationWith _
        (C ∘ LaurentPolynomial.toLaurentSeries ∘ truncate T)) X (c.outputs 0) -
          c.program.trace I X (c.outputs 0)) := by
    rw [Circuit.polynomial_mapOp, Circuit.map_eval_arith]
    refine Eq.trans ?_ (add_sub_cancel (c.program.trace I X (c.outputs 0)) _).symm
    simp only [Function.comp_def, map_X]
    exact congrArg (fun f => c.eval (arithInterpretationWith _ f) X 0) (funext fun a => map_C _ _)
  have hbound : (1 : ℤ) ≤ T - B₀ * wireIndex (c.outputs 0) := by
    cases c.outputs 0 with
    | input j => simp only [wireIndex]; push_cast; nlinarith
    | gate k => simp only [wireIndex]; push_cast; nlinarith [k.isLt]
  rw [map_rename, e, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, HahnSeries.coeff_add,
    (herr.rename x).mono hbound d i (by omega), add_zero]
  exact hQ d i hi

end Truncate

end Cslib.Circuits.Arithmetic
