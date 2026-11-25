/-
Copyright (c) 2026 lean-canny contributors and Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.TraceExponential
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Charpoly.TraceExponential
import CslibFrontier.Foundations.FieldTheory.Finite.Basic

/-!
# Indexed characteristic coefficients from uniform power traces

`traceExponentialCoefficient` is a total modular evaluator: it forms the divided negative
trace coefficients by powering, evaluates their finite exponential, extracts one coefficient,
and returns zero for addresses above the matrix dimension. Given uniform `F_a` trace residues,
its certificate is `F_(max (a + 1) 3 + 2)`; the modulus, dimension and address are binary
polynomial-time functions. No matrix or trace evaluator is constructed by this generic step.

At a prime with `D * D < p - 1`, the output is the canonical characteristic coefficient
of a `D`-dimensional matrix when the supplied residues give its traces for powers `1, …, D`.
The zero trace slot is ignored, so the empty matrix is included.

Adapted from the trace-to-coefficient construction in
[lean-canny](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/TraceCoefficients.lean)
and its
[matrix correctness proof](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/CharacteristicCoefficientEvaluation.lean).
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Cslib Cslib.Complexity Turing.MultiTapeTM Polynomial Matrix
open scoped BigOperators

/-- The zero logarithm slot is masked before Fermat inversion, including at p=2. -/
@[expose] def traceLogarithmResidue (p k t : ℕ) : ℕ :=
  if k = 0 then 0 else (p - (t * powMod p k (p - 2) % p)) % p

private theorem traceLogarithmResidue_polyTime :
    ComputableInPolyTime (fun q : ℕ × ℕ × ℕ => let (p, k, t) := q; traceLogarithmResidue p k t)
      encNat3 encNat := by
  have hp : ComputableInPolyTime (fun q : ℕ × ℕ × ℕ => q.1) encNat3 encNat := by fun_prop
  have hk : ComputableInPolyTime (fun q : ℕ × ℕ × ℕ => q.2.1) encNat3 encNat := by fun_prop
  have ht : ComputableInPolyTime (fun q : ℕ × ℕ × ℕ => q.2.2) encNat3 encNat := by fun_prop
  have hmod := ComputableInPolyTime.binary_mod.comp
    ((ComputableInPolyTime.binary_mul' ht
      (computableInPolyTime_powMod hp hk (ComputableInPolyTime.binary_sub' hp (.const 2)))).prod hp)
  have hres := ComputableInPolyTime.binary_mod.comp
    ((ComputableInPolyTime.binary_sub' hp hmod).prod hp)
  have hzero : ComputableInPolyTime (fun q : ℕ × ℕ × ℕ => decide (q.2.1 = 0)) encNat3 encBool := by
    fun_prop
  simpa only [traceLogarithmResidue, decide_eq_true_eq, Function.comp_apply] using
    ComputableInPolyTime.ite' hzero (ComputableInPolyTime.const 0) hres

theorem traceLogarithmResidue_cast {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : k < p) (t : ℕ) :
    (traceLogarithmResidue p k t : ZMod p) = -(t : ZMod p) / (k : ZMod p) := by
  have hp : p.Prime := Fact.out
  by_cases hk0 : k = 0
  · simp [traceLogarithmResidue, hk0]
  · have hkcast : (k : ZMod p) ≠ 0 :=
      fun hz => Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk0) hk
        ((ZMod.natCast_eq_zero_iff k p).mp hz)
    rw [traceLogarithmResidue, ite_eq_right hk0, ZMod.natCast_mod,
      Nat.cast_sub (Nat.mod_lt _ hp.pos).le, ZMod.natCast_self, ZMod.natCast_mod,
      zero_sub, Nat.cast_mul, powMod_of_ne_zero hp.ne_zero, ZMod.natCast_mod,
      Nat.cast_pow, ZMod.pow_card_sub_two_eq_inv hkcast]
    simp only [div_eq_mul_inv, neg_mul]

/-- The addressed reversed coefficient, with a total zero default above the dimension. -/
@[expose] noncomputable def traceExponentialCoefficient (p D d : ℕ) (t : ℕ → ℕ) : ℕ :=
  if d ≤ D then truncatedExponentialCoefficient p D (D - d)
    (fun k => traceLogarithmResidue p k (t k)) else 0

/-- The reconstructed expression is exactly the one with coefficients `-t_k/k`. -/
theorem traceExponentialCoefficient_eq {p : ℕ} [Fact p.Prime] {D d : ℕ}
    (hdegree : D * D < p - 1) (hd : d ≤ D) (t : ℕ → ℕ) :
    traceExponentialCoefficient p D d t =
      ((finiteExponential D
        (ofFn (D + 1) (fun k => -(t k : ZMod p) / ((k : ℕ) : ZMod p)))).coeff
          (D - d)).val := by
  have hD : D < p - 1 := (Nat.le_mul_self D).trans_lt hdegree
  have hpoly : ofFn (D + 1) (fun k => (traceLogarithmResidue p k (t k) : ZMod p)) =
      ofFn (D + 1) (fun k => -(t k : ZMod p) / ((k : ℕ) : ZMod p)) :=
    congrArg (ofFn (D + 1)) (funext fun k => traceLogarithmResidue_cast (by omega) (t k))
  rw [traceExponentialCoefficient, ite_eq_left hd,
    truncatedExponentialCoefficient_eq hdegree ((Nat.sub_le D d).trans_lt hD), hpoly]

variable {α : Type} {enc : α ↪ List Bool} {a : ℕ}

/-- Forming the divided negative trace costs no additional counting level. -/
theorem traceLogarithmResidue_mem {p k t : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hk : ComputableInPolyTime k enc encNat)
    (ht : t ∈ CountingFunction a enc encNat) :
    (fun w => traceLogarithmResidue (p w) (k w) (t w)) ∈ CountingFunction a enc encNat :=
  CountingFunction.map
    (CountingFunction.prod (CountingFunction.of_polyTime hp)
      (CountingFunction.prod (CountingFunction.of_polyTime hk) ht)) traceLogarithmResidue_polyTime

/-- The trace-to-exponential-coefficient stage has fixed depth for binary dimensions. -/
theorem traceExponentialCoefficient_mem (E : Decoder enc) {p D d : α → ℕ}
    {t : α × ℕ → ℕ} (hp : ComputableInPolyTime p enc encNat)
    (hD : ComputableInPolyTime D enc encNat) (hd : ComputableInPolyTime d enc encNat)
    (ht : t ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => traceExponentialCoefficient (p w) (D w) (d w) (fun k => t (w, k))) ∈
      CountingFunction (max (a + 1) 3 + 2) enc encNat := by
  have hc := truncatedExponentialCoefficient_mem E hp hD (ComputableInPolyTime.binary_sub' hD hd)
    (traceLogarithmResidue_mem (hp.comp (.fst enc encNat)) (.snd enc encNat) ht)
  have hguard : ComputableInPolyTime (fun w => decide (d w ≤ D w)) enc encBool := by fun_prop
  simpa only [traceExponentialCoefficient, decide_eq_true_eq, Function.comp_apply] using
    CountingFunction.ite (CountingFunction.of_polyTime hguard) hc
      (CountingFunction.of_polyTime (ComputableInPolyTime.const 0))

/-- From the positive power traces through the dimension, the evaluator returns the actual
characteristic coefficient, including the zero default above the dimension. The prime cutoff
also ensures that every required factorial denominator is invertible. -/
theorem traceExponentialCoefficient_eq_charpoly {p : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (ZMod p))
    (hdegree : Fintype.card ι * Fintype.card ι < p - 1) (d : ℕ) (t : ℕ → ℕ)
    (ht : ∀ k, 1 ≤ k → k ≤ Fintype.card ι → (t k : ZMod p) = (M ^ k).trace) :
    traceExponentialCoefficient p (Fintype.card ι) d t = (M.charpoly.coeff d).val := by
  have hD : Fintype.card ι < p - 1 := (Nat.le_mul_self _).trans_lt hdegree
  by_cases hd : d ≤ Fintype.card ι
  · have hpoly : ofFn (Fintype.card ι + 1) (fun k => -(t k : ZMod p) / ((k : ℕ) : ZMod p)) =
        ofFn (Fintype.card ι + 1) (fun k => -(M ^ (k : ℕ)).trace / ((k : ℕ) : ZMod p)) :=
      congrArg (ofFn _) (funext fun k => by
        by_cases hk : (k : ℕ) = 0
        · simp [hk]
        · rw [ht k (by omega) (by omega)])
    rw [traceExponentialCoefficient_eq hdegree hd, hpoly,
      Matrix.trace_exponential_coeff_eq_charpoly M (fun j _ _ hz =>
        Nat.not_dvd_of_pos_of_lt (by omega) (by omega) ((ZMod.natCast_eq_zero_iff j p).mp hz)) d hd]
  · rw [traceExponentialCoefficient, ite_eq_right hd,
      coeff_eq_zero_of_natDegree_lt (by rw [Matrix.charpoly_natDegree_eq_dim]; omega),
      ZMod.val_zero]

end Cslib.Complexity.RealAlgebraic
