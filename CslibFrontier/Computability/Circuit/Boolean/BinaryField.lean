/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Synthesis
public import CslibFrontier.Foundations.FieldTheory.Finite.BinaryField
public import CslibFrontier.Probability.HashFamily.Polynomial
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Boolean circuits for binary field polynomials

In the power basis of the explicit degree-`n` binary field, form the coefficients of the
ordinary polynomial product and then apply the fixed linear reduction modulo the defining
polynomial. Grouping the products of input bits by degree makes both stages quadratic in `n`.
Horner evaluation reuses this multiplier once per coefficient.
-/

public section

namespace Cslib.Circuits.Boolean

open Finset Cslib.BitString

variable {n a : ℕ}

private def degreeIndex (ij : Fin n × Fin n) : Fin (2 * n) :=
  ⟨ij.1.val + ij.2.val, by have := ij.1.isLt; have := ij.2.isLt; lia⟩

private def diagonal (e : Fin (2 * n)) : Finset (Fin n × Fin n) :=
  univ.filter (degreeIndex · = e)

private def productCoeff (x y : BitString n) (e : Fin (2 * n)) : Bool :=
  ∑ ij ∈ diagonal e, x ij.1 * y ij.2

private theorem mul_bit (hn : n ≠ 0) (x y : BinaryField n) (j : Fin n) :
    BinaryField.equivBits hn (x * y) j =
      ∑ e : Fin (2 * n), productCoeff (BinaryField.equivBits hn x) (BinaryField.equivBits hn y) e *
        BinaryField.equivBits hn (AdjoinRoot.root (leastIrreducible n) ^ e.val) j := by
  let B := BinaryField.equivBits hn
  let r := AdjoinRoot.root (leastIrreducible n)
  have expand (z : BinaryField n) : z = ∑ i, bitEquiv.symm (B z i) • r ^ i.val := by
    simpa only [BinaryField.basis_apply hn, B, r, AddEquiv.symm_apply_apply] using
      BinaryField.equivBits_symm_apply hn (B z)
  have hxy : x * y = ∑ ij : Fin n × Fin n,
      bitEquiv.symm (B x ij.1 * B y ij.2) • r ^ (degreeIndex ij).val := by
    conv_lhs => rw [expand x, expand y, Finset.sum_mul_sum]
    rw [Fintype.sum_prod_type]
    exact sum_congr rfl fun i _ => sum_congr rfl fun k _ => by
      rw [smul_mul_smul_comm, map_mul, ← pow_add]
      rfl
  have group : ∑ e : Fin (2 * n), ∑ ij ∈ diagonal e,
      (bitEquiv.symm (B x ij.1 * B y ij.2) • r ^ (degreeIndex ij).val : BinaryField n) =
      x * y := (Finset.sum_fiberwise univ degreeIndex _).trans hxy.symm
  rw [← group, map_sum, Finset.sum_apply]
  refine sum_congr rfl fun e _ => ?_
  rw [map_sum, Finset.sum_apply, productCoeff, Finset.sum_mul]
  refine sum_congr rfl fun ij hij => ?_
  rw [show degreeIndex ij = e from (Finset.mem_filter.mp hij).2]
  cases B x ij.1 * B y ij.2 <;> simp [r, ← Bool.zero_eq_false, ← Bool.one_eq_true]

/-- Multiply two available field elements in power-basis coordinates, sharing the unreduced
product coefficients across all output bits. The De Morgan gate count includes constants. -/
theorem synthesis_binaryFieldMul (hn : n ≠ 0) (s : Set (BooleanFunction a))
    (x y : BitString a → BinaryField n)
    (hx : ∀ i, (fun z => BinaryField.equivBits hn (x z) i) ∈ s)
    (hy : ∀ i, (fun z => BinaryField.equivBits hn (y z) i) ∈ s) :
    Synthesis interpretation s (Set.range fun j z => BinaryField.equivBits hn (x z * y z) j)
      (13 * n ^ 2 + 3 * n) := by
  let B := BinaryField.equivBits hn
  let c (e : Fin (2 * n)) (z : BitString a) := productCoeff (B (x z)) (B (y z)) e
  have hcoeff (e) : Synthesis interpretation s {c e} ((diagonal e).card * 5 + 1) := by
    have h := Synthesis.sum (diagonal e)
      (fun ij z => B (x z) ij.1 * B (y z) ij.2) (fun _ => 1)
      fun ij _ => (Synthesis.of_mem (hx ij.1)).and (Synthesis.of_mem (hy ij.2))
    simpa only [sum_const, smul_eq_mul, c, productCoeff, Nat.reduceAdd] using h
  have hcard : ∑ e : Fin (2 * n), (diagonal e).card = n * n := by
    have h := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n × Fin n)))
      (t := (univ : Finset (Fin (2 * n)))) (f := degreeIndex) (fun _ _ => mem_univ _)
    simpa [diagonal] using h.symm
  have hc := Synthesis.family c (fun e => (diagonal e).card * 5 + 1) hcoeff
  let s' := s ∪ Set.range c
  let b (e : Fin (2 * n)) (j : Fin n) := B (AdjoinRoot.root (leastIrreducible n) ^ e.val) j
  have hout (j : Fin n) : Synthesis interpretation s' {fun z => B (x z * y z) j}
      (2 * n * 4 + 1) := by
    let active := univ.filter fun e => b e j = true
    have hs := Synthesis.sum active c (fun _ => 0) fun e _ =>
      Synthesis.of_mem (s := s') (Or.inr ⟨e, rfl⟩)
    have he (z : BitString a) : (∑ e ∈ active, c e z) = B (x z * y z) j := by
      rw [mul_bit hn, sum_filter]
      refine sum_congr rfl fun e _ => ?_
      change (if b e j = true then c e z else 0) = c e z * b e j
      cases b e j <;> cases c e z <;> rfl
    refine (hs.congr_iff (fun z => by rw [he])).mono Set.Subset.rfl Set.Subset.rfl ?_
    have hsz : active.card ≤ 2 * n := by
      simpa [active] using card_filter_le univ (fun e => b e j = true)
    simpa only [sum_const, smul_eq_mul] using Nat.add_le_add_right (Nat.mul_le_mul_right 4 hsz) 1
  have h := hc.trans (Synthesis.family _ _ hout)
  refine h.mono Set.Subset.rfl Set.Subset.rfl (le_of_eq ?_)
  simp only [sum_add_distrib, ← sum_mul, hcard, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul]
  ring

/-- A fixed vector of `k` field coefficients gives an `n`-input, `n`-output circuit for the
corresponding polynomial. Only the input point varies when this circuit is evaluated. -/
theorem exists_binaryFieldPolynomial_circuit (hn : n ≠ 0) {k : ℕ}
    (coeff : Fin k → BinaryField n) :
    ∃ q : Circuit signature n n, q.Computes interpretation (fun z =>
      BinaryField.equivBits hn
        (Probability.polynomialHash coeff ((BinaryField.equivBits hn).symm z))) ∧
      q.size ≤ n + k * (13 * n ^ 2 + 8 * n) := by
  let B := BinaryField.equivBits hn
  let value {m : ℕ} (v : Fin m → BinaryField n) (z : BitString n) :=
    Probability.polynomialHash v (B.symm z)
  have build {m : ℕ} (v : Fin m → BinaryField n) :
      Synthesis interpretation (inputs n) (Set.range fun j z => B (value v z) j)
        (n + m * (13 * n ^ 2 + 8 * n)) := by
    induction m with
    | zero =>
      have hz := Synthesis.family (fun (_ : Fin n) (_ : BitString n) => false) (fun _ => 1)
        (fun _ => Synthesis.const (s := inputs n) false)
      simpa [value, Probability.polynomialHash, Bool.zero_eq_false] using hz
    | succ m ih =>
      let tail := fun i : Fin m => v i.succ
      let s := inputs n ∪ Set.range fun j z => B (value tail z) j
      have hm := synthesis_binaryFieldMul hn s (value tail) B.symm
        (fun j => Or.inr ⟨j, rfl⟩) (fun j => Or.inl ⟨j, by simp [B]⟩)
      let p := fun j z => B (value tail z * B.symm z) j
      have ha (j) : Synthesis interpretation (s ∪ Set.range p)
          {fun z => p j z ^^ B (v 0) j} 5 :=
        (Synthesis.of_mem (Or.inr ⟨j, rfl⟩)).xor (Synthesis.const _)
      have step (z : BitString n) : value v z = value tail z * B.symm z + v 0 := by
        simp only [value, Probability.polynomialHash, Fin.sum_univ_succ, Fin.val_zero, pow_zero,
          mul_one, sum_mul, tail, Fin.val_succ, pow_succ, mul_assoc, add_comm (v 0)]
      have ht := (ih tail).trans (hm.trans (Synthesis.family _ _ ha))
      refine ht.mono Set.Subset.rfl ?_ (le_of_eq ?_)
      · rintro _ ⟨j, rfl⟩
        refine ⟨j, funext fun z => ?_⟩
        change (p j z ^^ B (v 0) j) = B (value v z) j
        rw [step, map_add]
        rfl
      · simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
        ring
  exact (build coeff).exists_circuit_outputs

end Cslib.Circuits.Boolean
