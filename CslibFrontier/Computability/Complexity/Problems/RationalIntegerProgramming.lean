/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.GeneralIntegerProgramming.Hardness
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Rat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.ListProd
import CslibFrontier.Foundations.Data.Rat.ClearDenom
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Mathlib.Data.List.GetD

/-!
# Rational-input integer programming

Theorem 2.17 of the January 8, 2007 web draft of [AroraBarak07], printed p. 52 / PDF p. 68,
asks whether rational linear inequalities admit a **nonnegative integer** assignment.
`RationalIntegerProgram.Feasible` states this problem, with unary dimension and binary rational
numerators and denominators. Lists are padded with zero or truncated to the declared dimension;
all supplied coefficients are charged in the encoding.

`clearDenominators` multiplies each row by the product of its positive denominators (including
the right-hand side), then adds nonnegativity rows. `satisfies_clearDenominators_iff` preserves
exactly the integer assignments, with no new unknowns. Binary product, division and multiplication
certificates prove polynomial time, including the bit cost of the denominator products.
NP membership follows from the integer-input small-solution theorem. Hardness reuses the
zero-one reduction to integer inequalities, casting its coefficients to rationals.

## Main results

* `RationalIntegerProgram.satisfies_clearDenominators_iff`: preservation of each assignment.
* `RationalIntegerProgram.computableInPolyTime_clearDenominators`: certified denominator clearing.
* `RationalIntegerProgram.npComplete`: the rational-input problem is NP-complete.
-/

public section

namespace Cslib.Complexity
open Finset Turing.MultiTapeTM ComputableInPolyTime

namespace RationalIntegerProgram

/-- A rational inequality in variable order. -/
structure Inequality where
  /-- Coefficient list, padded with zero or truncated to the declared dimension. -/
  coeffs : List ℚ
  /-- Rational upper bound. -/
  rhs : ℚ
  deriving DecidableEq, Repr

/-- Framed list of binary rationals followed by the binary rational bound. Each rational uses
its reduced signed-binary numerator, framed, followed by its positive binary denominator. -/
enc_structure encInequality : Inequality where
  coeffs : (encList encRat), rhs : encRat

end RationalIntegerProgram

/-- Rational linear inequalities whose unknowns range over nonnegative integers. -/
structure RationalIntegerProgram where
  /-- Number of variables, charged in unary. -/
  numVars : ℕ
  /-- The rational inequality rows. -/
  constraints : List RationalIntegerProgram.Inequality
  deriving DecidableEq, Repr

namespace RationalIntegerProgram

/-- Unary dimension, framed, then a framed list of rows under `encInequality`.
Rational coefficients use explicit signed-binary numerators and positive binary denominators. -/
enc_structure enc : RationalIntegerProgram where
  numVars : encUnary, constraints : (encList encInequality)

/-- Feasibility with nonnegative integer coordinates, as in draft Theorem 2.17. -/
@[expose] def Feasible : Set RationalIntegerProgram := {P | ∃ x : Fin P.numVars → ℤ,
  (∀ j, 0 ≤ x j) ∧ ∀ c ∈ P.constraints,
    ∑ j : Fin P.numVars, c.coeffs.getD j 0 * (x j : ℚ) ≤ c.rhs}

private def denominator (c : Inequality) : ℕ :=
  c.rhs.den * (c.coeffs.map Rat.den).prod

private def clearEntry (d : ℕ) (q : ℚ) : ℤ := q.num * (d / q.den : ℕ)

private def clearRow (c : Inequality) : IntegerProgram.Inequality :=
  ⟨c.coeffs.map (clearEntry (denominator c)), clearEntry (denominator c) c.rhs⟩

private def nonnegRow (n j : ℕ) : IntegerProgram.Inequality :=
  ⟨IntegerProgram.unitCoeffs n j (-1), 0⟩

/-- Clear each row by its positive denominator product, including the bound, and append
`-x j ≤ 0` for every variable. The dimension and integer solution set are preserved. -/
def clearDenominators (P : RationalIntegerProgram) : IntegerProgram :=
  ⟨P.numVars, P.constraints.map clearRow ++ (List.range P.numVars).map (nonnegRow P.numVars)⟩

/-- Denominator clearing does not introduce auxiliary variables. -/
@[simp] theorem clearDenominators_numVars (P : RationalIntegerProgram) :
    P.clearDenominators.numVars = P.numVars := by simp [clearDenominators]

private theorem clearRow_iff (c : Inequality) (n : ℕ) (x : Fin n → ℤ) :
    (∑ j : Fin n, (clearRow c).coeffs.getD j 0 * x j ≤ (clearRow c).rhs) ↔
      ∑ j : Fin n, c.coeffs.getD j 0 * (x j : ℚ) ≤ c.rhs := by
  have hpos : 0 < denominator c := by
    exact Nat.mul_pos c.rhs.pos (List.prod_pos (by simp [Rat.pos]))
  have hdvd (q : ℚ) (hq : q ∈ c.coeffs ∨ q = c.rhs) : q.den ∣ denominator c := by
    rcases hq with hq | rfl
    · exact dvd_mul_of_dvd_right (List.dvd_prod (List.mem_map.mpr ⟨q, hq, rfl⟩)) _
    · exact dvd_mul_right _ _
  have hentry (j : Fin n) :
      (((clearRow c).coeffs.getD j 0 : ℤ) : ℚ) =
        (denominator c : ℚ) * c.coeffs.getD j 0 := by
    have hmap : (clearRow c).coeffs.getD j 0 =
        clearEntry (denominator c) (c.coeffs.getD j 0) := by
      simpa [clearRow, clearEntry] using
        (List.getD_map (l := c.coeffs) (d := 0) (n := j.val)
          (clearEntry (denominator c)))
    rw [hmap]
    rcases List.getD_mem_or c.coeffs j.val 0 with hj | hj
    · exact (Rat.clearDenom_entry (hdvd _ (Or.inl hj))).symm
    · rw [hj]
      simp [clearEntry]
  have hrhs : ((clearRow c).rhs : ℚ) = (denominator c : ℚ) * c.rhs :=
    (Rat.clearDenom_entry (hdvd _ (Or.inr rfl))).symm
  have hcast : (∑ j : Fin n, (clearRow c).coeffs.getD j 0 * x j ≤ (clearRow c).rhs) ↔
      (∑ j : Fin n, (((clearRow c).coeffs.getD j 0 : ℤ) : ℚ) * (x j : ℚ) ≤
        ((clearRow c).rhs : ℚ)) := by exact_mod_cast Iff.rfl
  rw [hcast, hrhs]
  simp only [hentry, mul_assoc, ← Finset.mul_sum]
  exact mul_le_mul_iff_right₀ (show (0 : ℚ) < denominator c by exact_mod_cast hpos)

private theorem nonnegRow_iff {n j : ℕ} (hj : j < n) (x : Fin n → ℤ) :
    (∑ k : Fin n, (nonnegRow n j).coeffs.getD k 0 * x k ≤ (nonnegRow n j).rhs) ↔
      0 ≤ x ⟨j, hj⟩ := by
  simp only [nonnegRow, IntegerProgram.sum_unitCoeffs hj, neg_one_mul, neg_nonpos]

/-- Denominator clearing preserves exactly the nonnegative integer assignments, with no change
of dimension. In particular it does not substitute rational witnesses for integer ones. -/
theorem satisfies_clearDenominators_iff (P : RationalIntegerProgram) (x : Fin P.numVars → ℤ) :
    (∀ c ∈ P.clearDenominators.constraints,
      ∑ j : Fin P.numVars, c.coeffs.getD j 0 * x j ≤ c.rhs) ↔
    (∀ j, 0 ≤ x j) ∧ (∀ c ∈ P.constraints,
      ∑ j : Fin P.numVars, c.coeffs.getD j 0 * (x j : ℚ) ≤ c.rhs) := by
  simp only [clearDenominators, List.mem_append, or_imp, forall_and, List.forall_mem_map,
    List.mem_range, clearRow_iff]
  constructor
  · rintro ⟨hc, hn⟩
    exact ⟨fun j => (nonnegRow_iff j.isLt x).mp (hn j j.isLt), hc⟩
  · rintro ⟨hn, hc⟩
    exact ⟨hc, fun j hj => (nonnegRow_iff hj x).mpr (hn ⟨j, hj⟩)⟩

@[local fun_prop]
private theorem computableInPolyTime_denominator :
    ComputableInPolyTime denominator encInequality encNat := by
  fun_prop [denominator]

open scoped IntegerProgram in
/-- Native polynomial-time denominator clearing, charging the binary sizes of products. -/
theorem computableInPolyTime_clearDenominators :
    ComputableInPolyTime clearDenominators enc IntegerProgram.enc := by
  fun_prop [clearDenominators, clearRow, clearEntry, nonnegRow, IntegerProgram.unitCoeffs]

/-- The explicit denominator-clearing many-one reduction to integer-input feasibility. -/
theorem polyTimeReducible_integerProgram :
    PolyTimeReducible enc IntegerProgram.enc Feasible IntegerProgram.Feasible :=
  ⟨clearDenominators, computableInPolyTime_clearDenominators,
    fun P => exists_congr (satisfies_clearDenominators_iff P) |>.symm⟩

/-- Rational-input feasibility belongs to NP by the proved integer small-solution bound. -/
theorem mem_NP : Feasible ∈ NP enc :=
  polyTimeReducible_integerProgram.mem_NP IntegerProgram.mem_NP

/-- View integer inequalities as rational inequalities. Nonnegativity is imposed by the target
language; thus this cast preserves assignments that already satisfy that restriction. -/
private def ofInteger (P : IntegerProgram) : RationalIntegerProgram :=
  ⟨P.numVars, P.constraints.map fun c => ⟨c.coeffs.map Int.cast, c.rhs⟩⟩

private theorem satisfies_ofInteger_iff (P : IntegerProgram) (x : Fin P.numVars → ℤ) :
    (∀ c ∈ (ofInteger P).constraints,
      ∑ j : Fin P.numVars, c.coeffs.getD j 0 * (x j : ℚ) ≤ c.rhs) ↔
      ∀ c ∈ P.constraints, ∑ j : Fin P.numVars, c.coeffs.getD j 0 * x j ≤ c.rhs := by
  simp only [ofInteger, List.forall_mem_map]
  apply forall_congr'
  intro c
  apply forall_congr'
  intro _
  have hm (j : Fin P.numVars) : (c.coeffs.map (Int.cast : ℤ → ℚ)).getD j 0 =
      (c.coeffs.getD j 0 : ℚ) :=
        List.getD_map (l := c.coeffs) (d := 0) (n := j.val) (Int.cast : ℤ → ℚ)
  simp only [hm]
  exact_mod_cast Iff.rfl

open scoped IntegerProgram in
private theorem poly_ofInteger : ComputableInPolyTime ofInteger IntegerProgram.enc enc := by
  fun_prop [ofInteger]

private theorem ofZeroOne_mem_iff (C : List ZeroOneIP.Equation) :
    ofInteger (IntegerProgram.ofZeroOne C) ∈ Feasible ↔ C ∈ ZeroOneIP := by
  let P := IntegerProgram.ofZeroOne C
  have hcast : ofInteger P ∈ Feasible ↔ ∃ x : Fin P.numVars → ℤ,
      (∀ j, 0 ≤ x j) ∧ ∀ c ∈ P.constraints,
        ∑ j : Fin P.numVars, c.coeffs.getD j 0 * x j ≤ c.rhs := by
    exact exists_congr fun x => and_congr_right fun _ => satisfies_ofInteger_iff P x
  rw [hcast, ← IntegerProgram.ofZeroOne_mem_iff C]
  constructor
  · rintro ⟨x, _, hx⟩
    exact ⟨x, hx⟩
  · intro h
    obtain ⟨x, hx⟩ := h
    have hn := (IntegerProgram.satisfies_ofZeroOne_iff C x).mp hx
    exact ⟨x, fun j => (hn.1 j).1, hx⟩

/-- Rational-input integer programming with nonnegative integer unknowns is NP-complete
([AroraBarak07], January 8, 2007 draft, Theorem 2.17, printed p. 52 / PDF p. 68).
The explicit encoding uses unary dimension and binary reduced numerators/denominators. -/
theorem npComplete : NPComplete enc Feasible :=
  ⟨mem_NP, ZeroOneIP_npHard.trans
    ⟨fun C => ofInteger (IntegerProgram.ofZeroOne C),
      poly_ofInteger.comp IntegerProgram.computableInPolyTime_ofZeroOne,
      fun C => (ofZeroOne_mem_iff C).symm⟩⟩

end RationalIntegerProgram
end Cslib.Complexity
