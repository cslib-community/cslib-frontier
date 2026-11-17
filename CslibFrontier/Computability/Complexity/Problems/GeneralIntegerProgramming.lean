/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.IntegerSolution
public import CslibFrontier.Foundations.Data.List.DotProduct
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.List.OfFn
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.PolyTime.Int.DotProduct
import CslibFrontier.Foundations.Data.List.GetD
import Mathlib.Data.List.GetD

/-!
# Integer feasibility with unrestricted integer unknowns

`IntegerProgram` stores a unary variable count and signed-binary inequality rows. Every
unknown ranges over all integers. A row's coefficient list is padded with zeros or truncated
to the declared number of variables. The complete list is charged in the input encoding.

The verifier uses a signed-binary list of integer coordinates. Its completeness follows from
the integer small-solution theorem, not the rational basic-solution theorem.
-/

public section

namespace Cslib.Complexity

open Finset Matrix Turing.MultiTapeTM ComputableInPolyTime Mathlib.Tactic.Matrix

namespace IntegerProgram

/-- One integer inequality, with coefficients in variable order and an upper bound. -/
structure Inequality where
  /-- Coefficients of variables `0, 1, …`, padded or truncated to the variable count. -/
  coeffs : List ℤ
  /-- The upper bound on the linear expression. -/
  rhs : ℤ
  deriving DecidableEq, Repr

/-- A framed list of signed-binary coefficients followed by the signed-binary upper bound. -/
enc_structure encInequality : Inequality where
  coeffs : (encList encIntBin), rhs : encIntBin

end IntegerProgram

/-- A finite system of integer linear inequalities, with unrestricted integer unknowns. -/
structure IntegerProgram where
  /-- Number of unknowns, encoded in unary so dimension is charged to the input. -/
  numVars : ℕ
  /-- The inequality rows. -/
  constraints : List IntegerProgram.Inequality
  deriving DecidableEq, Repr

namespace IntegerProgram

/-- Unary variable count, framed, followed by a framed list of signed-binary inequality rows. -/
enc_structure enc : IntegerProgram where
  numVars : encUnary, constraints : (encList encInequality)

/-- Integer feasibility of a system, with a coordinate for every declared variable. -/
@[expose] def Feasible : Set IntegerProgram := {P | ∃ x : Fin P.numVars → ℤ,
  ∀ c ∈ P.constraints, ∑ j : Fin P.numVars, c.coeffs.getD j 0 * x j ≤ c.rhs}

/-- Verify integer coordinates by padded integer dot products, without division. -/
@[expose] def check (p : IntegerProgram × List ℤ) : Bool :=
  p.1.constraints.all fun c =>
    decide (ListMatrix.dotProduct p.1.numVars c.coeffs p.2 ≤ c.rhs)

/-- Soundness of the integer verifier, including short certificates padded with zero. -/
theorem mem_of_check {P : IntegerProgram} {w : List ℤ} (h : check (P, w) = true) :
    P ∈ Feasible := by
  simp only [check, List.all_eq_true, decide_eq_true_eq] at h
  refine ⟨fun j => w.getD j 0, fun c hc => ?_⟩
  simpa only [ListMatrix.dotProduct_eq, _root_.dotProduct, ofList_apply] using h c hc

private theorem length_le (P : IntegerProgram) :
    P.numVars ≤ (enc P).length ∧ P.constraints.length ≤ (enc P).length := by
  constructor
  · have h := enc_numVars_length_le P
    change (List.replicate P.numVars true).length ≤ _ at h
    simpa only [List.length_replicate] using h
  · exact (length_le_length_encList _ _).trans (enc_constraints_length_le P)

private theorem abs_entry_le {P : IntegerProgram} {c : Inequality} (hc : c ∈ P.constraints)
    {z : ℤ} (hz : z ∈ c.coeffs ∨ z = c.rhs) : |z| ≤ (2 ^ (enc P).length : ℕ) := by
  have hlen : (encIntBin z).length ≤ (enc P).length := by
    refine le_trans ?_ ((length_le_encList_of_mem _ hc).trans (enc_constraints_length_le P))
    rcases hz with hz | rfl
    · exact (length_le_encList_of_mem _ hz).trans (encInequality_coeffs_length_le c)
    · exact encInequality_rhs_length_le c
  rw [length_encIntBin] at hlen
  have hsize : z.natAbs < 2 ^ (enc P).length :=
    (Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  rw [Int.abs_eq_natAbs]
  exact_mod_cast hsize.le

private noncomputable def witnessPoly : Polynomial ℕ :=
  let k := (3 * Polynomial.X) ^ 2 + 2 +
    3 * Polynomial.X * (Polynomial.X + 2 * (3 * Polynomial.X + (Polynomial.X + 2) + 1) + 3)
  let e := k + (3 * Polynomial.X) ^ 2 + 2 +
    3 * Polynomial.X * (Polynomial.X + 2 * (2 * (Polynomial.X + 2) + 3 * Polynomial.X + k + 1) + 3)
  Polynomial.X * (2 * e + 3)

private theorem exists_check {P : IntegerProgram} (hP : P ∈ Feasible) :
    ∃ w : List ℤ, check (P, w) = true ∧
      (encList encIntBin w).length ≤ witnessPoly.eval (enc P).length := by
  classical
  let L := (enc P).length
  let A : Matrix (Fin P.constraints.length) (Fin P.numVars) ℤ :=
    fun i j => P.constraints[i.val].coeffs.getD j.val 0
  let b : Fin P.constraints.length → ℤ := fun i => P.constraints[i.val].rhs
  have hA : ∀ i j, |A i j| ≤ (2 ^ L : ℕ) := by
    intro i j
    rcases List.getD_mem_or P.constraints[i.val].coeffs j.val 0 with h | h
    · exact abs_entry_le (List.getElem_mem i.isLt) (Or.inl h)
    · simp only [A, h, abs_zero]
      positivity
  have hb : ∀ i, |b i| ≤ (2 ^ L : ℕ) := fun i =>
    abs_entry_le (List.getElem_mem i.isLt) (Or.inr rfl)
  obtain ⟨x₀, hx₀⟩ := hP
  have hAx₀ : A *ᵥ x₀ ≤ b := fun i => hx₀ _ (List.getElem_mem i.isLt)
  obtain ⟨x, hx, hxB⟩ := exists_int_mulVec_le_abs_le hA hb hAx₀
  let D := nonnegIntSolutionBound P.constraints.length (2 * P.numVars + P.constraints.length)
    (2 ^ L + 1)
  let E := nonnegIntSolutionBits L (3 * L) (L + 2)
  have hdim := length_le P
  have hbits : D.size ≤ E := by
    have h := size_nonnegIntSolutionBound_le P.constraints.length
      (2 * P.numVars + P.constraints.length) (2 ^ L + 1)
    apply h.trans
    dsimp only [nonnegIntSolutionBits, E]
    gcongr
    all_goals first | omega | simpa [Nat.size_pow] using Nat.size_add_le_max (2 ^ L) 1
  refine ⟨List.ofFn x, ?_, ?_⟩
  · simp only [check, List.all_eq_true, decide_eq_true_eq]
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    simpa only [ListMatrix.dotProduct_eq, _root_.dotProduct, ofList_apply,
      List.getD_ofFn, A, b, mulVec, dotProduct] using hx ⟨i, hi⟩
  · have hlen : ∀ z ∈ List.ofFn x, (encIntBin z).length ≤ E + 1 := by
      intro z hz
      obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).mp hz
      rw [length_encIntBin]
      have h := hxB j
      simp only [Fintype.card_fin] at h
      have habs : (x j).natAbs ≤ D := by
        rw [Int.abs_eq_natAbs] at h
        exact_mod_cast h
      exact Nat.add_le_add_right ((Nat.size_le_size habs).trans hbits) 1
    have hlen' := length_encList_le encIntBin (List.ofFn x) hlen
    rw [List.length_ofFn] at hlen'
    have heval : witnessPoly.eval L = L * (2 * E + 3) := by
      simp [witnessPoly, E, nonnegIntSolutionBits, pow_two]
    change _ ≤ witnessPoly.eval L
    rw [heval]
    calc _ ≤ P.numVars * (2 * (E + 1) + 1) := hlen'
      _ ≤ L * (2 * (E + 1) + 1) := Nat.mul_le_mul_right _ hdim.1
      _ = L * (2 * E + 3) := by ring

/-- The integer feasibility verifier runs in native polynomial time. -/
theorem computableInPolyTime_check :
    ComputableInPolyTime check (encPair enc (encList encIntBin)) encBool := by
  unfold check
  apply allWithInput (by fun_prop)
  apply intBin_le' ?_ (by fun_prop)
  exact listDotProduct.comp (g := fun q : (IntegerProgram × List ℤ) × Inequality =>
    (q.1.1.numVars, (q.2.coeffs, q.1.2))) (by fun_prop)

/-- General integer inequality feasibility is in NP, with unary dimension and signed-binary
coefficients. Integer coordinates are unrestricted; their certificate length follows from the
integer small-solution bound. -/
theorem mem_NP : Feasible ∈ NP enc :=
  mem_NP_of_check (.list .intBin) computableInPolyTime_check
    (fun _ _ h => mem_of_check h) (fun _ h => exists_check h)

end IntegerProgram
end Cslib.Complexity
