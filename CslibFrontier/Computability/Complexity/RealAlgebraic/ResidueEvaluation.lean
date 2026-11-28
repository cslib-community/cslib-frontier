/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.PowerProductCoefficients
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.Residue
import CslibFrontier.Foundations.Data.List.Blocks
import Mathlib.Tactic.Ring

/-!
# Uniform modular evaluation of finite pure-power residues

The evaluator sums coefficients of the geometric-series numerators over short base-addresses.
A degree mask removes the noncontributing indices before coefficient extraction. Unary arity
and binary modulus, degree and exponents keep each address polynomial in the encoded input;
the number of summands may be exponential. Uniform numerator and relation evaluators in
`CountingFunction a` give a residue evaluator in `CountingFunction (a + 5)`.

Correctness identifies this constructed evaluator with the actual finite residue over
`ZMod p` when the source degree and prime bounds hold. No residue oracle is assumed.
Ported and simplified from `LeanCanny.CountingHierarchy.ResidueEvaluation` and
`ResidueEnumeration` at lean-canny commit `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
Critical-system evaluation and the full real-counting endpoints remain
[#6560](https://github.com/cslib-community/cslib-frontier/issues/6560).
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM MvPolynomial MvPolynomial.PurePower
open scoped BigOperators

/-- The top-box exponent shifted by `ell` times the geometric-series index. -/
@[expose] def residueAddress (ell : ℕ) (j : List ℕ) : List ℕ :=
  j.map (fun k => ell - 1 + ell * k)

/-- A total residue evaluator. The degree mask discards indices outside
 the finite simplex before invoking coefficient extraction. -/
@[expose] noncomputable def residueValue (p n ell B : ℕ)
    (v : List ℕ → ℕ) (r : ℕ → List ℕ → ℕ) : ℕ :=
  (∑ s ∈ Finset.range ((B + 1) ^ n),
    let j := gridPoint (B + 1) n s
    if j.sum ≤ B then powerProductCoefficient p n (residueAddress ell j) j v r else 0) % p

/-- Shifting every binary geometric-series index preserves polynomial-time access. -/
theorem residueAddress_polyTime {α : Type} {enc : α ↪ List Bool}
    {ell : α → ℕ} {j : α → List ℕ}
    (hell : ComputableInPolyTime ell enc encNat)
    (hj : ComputableInPolyTime j enc (encList encNat)) :
    ComputableInPolyTime (fun w => residueAddress (ell w) (j w)) enc (encList encNat) :=
  ComputableInPolyTime.mapWithInput hj (by fun_prop)

/-- Constructing the residue from uniform modular numerator and relation
 evaluations costs five function levels, independently of arity and degree. -/
theorem residueValue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n ell B : α → ℕ}
    {v : α × List ℕ → ℕ} {r : α × (ℕ × List ℕ) → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat)
    (hB : ComputableInPolyTime B enc encNat)
    (hv : v ∈ CountingFunction a (encPair enc (encList encNat)) encNat)
    (hr : r ∈ CountingFunction a (encPair enc (encPair encNat (encList encNat))) encNat) :
    (fun w => residueValue (p w) (n w) (ell w) (B w)
      (fun z => v (w, z)) (fun i z => r (w, i, z))) ∈
        CountingFunction (a + 5) enc encNat := by
  have fst := ComputableInPolyTime.fst enc encNat
  have hj := gridPoint_polyTime (.binary_add' (hB.comp fst) (.const 1)) (hn.comp fst)
    (.snd enc encNat)
  have hv' : (fun q : (α × ℕ) × List ℕ => v (q.1.1, q.2)) ∈
      CountingFunction a (encPair (encPair enc encNat) (encList encNat)) encNat :=
    CountingFunction.preprocess hv (by fun_prop)
  have hr' : (fun q : (α × ℕ) × (ℕ × List ℕ) => r (q.1.1, q.2)) ∈
      CountingFunction a (encPair (encPair enc encNat) (encPair encNat (encList encNat))) encNat :=
    CountingFunction.preprocess hr (by fun_prop)
  have hc := powerProductCoefficient_mem (Decoder.pair E Decoder.nat) (hp.comp fst) (hn.comp fst)
    (residueAddress_polyTime (hell.comp fst) hj) hj hv' hr'
  have hguard : ComputableInPolyTime
      (fun q : α × ℕ => decide ((gridPoint (B q.1 + 1) (n q.1) q.2).sum ≤ B q.1))
      (encPair enc encNat) encBool := by
    have hsum := ComputableInPolyTime.binary_sum.comp hj
    fun_prop
  simpa only [residueValue, decide_eq_true_eq, Function.comp_apply] using
    CountingFunction.nat_mod
      (CountingFunction.sum_range E
        (CountingFunction.ite (CountingFunction.of_polyTime hguard) hc
          (CountingFunction.of_polyTime (.const 0)))
        (.binary_pow' (.binary_add' hB (.const 1)) hn))
      (CountingFunction.of_polyTime hp)

private theorem sum_residue_grid {M : Type*} [AddCommMonoid M] (B n : ℕ)
    (F : (Fin n → ℕ) → M) :
    (∑ s ∈ Finset.range ((B + 1) ^ n),
      F (fun i => (gridPoint (B + 1) n s)[i.val]?.getD 0)) =
        ∑ j ∈ indices n B, F j := by
  classical
  simp_rw [fun s (i : Fin n) => gridPoint_get (p := B + 1) (r := s) i.isLt]
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ z : Fin n → Fin (B + 1), F (fun i => (z i).val) :=
      (finFunctionFinEquiv : (Fin n → Fin (B + 1)) ≃ Fin ((B + 1) ^ n)).symm.sum_comp
        (fun z => F (fun i => (z i).val))
    _ = ∑ j ∈ indices n B, F j :=
      Finset.sum_bij (fun z _ i => (z i).val)
        (fun z _ => mem_indices.mpr fun i => Nat.lt_succ_iff.mp (z i).isLt)
        (fun _ _ _ _ h => funext fun i => Fin.ext (congrFun h i))
        (fun j hj => ⟨fun i => ⟨j i, Nat.lt_succ_iff.mpr (mem_indices.mp hj i)⟩,
          Finset.mem_univ _, rfl⟩)
        fun _ _ => rfl

private theorem grid_sum (b n s : ℕ) :
    (gridPoint b n s).sum =
      (∑ i : Fin n, (gridPoint b n s)[i.val]?.getD 0) := by
  change ((List.range n).map (fun i => s / b ^ i % b)).sum = _
  rw [List.sum_map_range_eq_sum_range, Finset.sum_range]
  exact Finset.sum_congr rfl fun i _ => (gridPoint_get i.isLt).symm

/-- The constructed evaluator computes the actual residue, using only
 canonical finite-field evaluation points and bounded base-address indices. -/
theorem residueValue_cast {p n ell B : ℕ} [Fact p.Prime] (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) (ZMod p))
    (hr : ∀ i, (r i).totalDegree < ell)
    (v : MvPolynomial (Fin n) (ZMod p)) (hv : v.totalDegree ≤ B)
    (hcut : ell * (B + 1) + 1 < p)
    (value : List ℕ → ℕ) (rvalue : ℕ → List ℕ → ℕ)
    (hvalue : ∀ s < p ^ n, (value (gridPoint p n s) : ZMod p) =
      eval (fun i : Fin n => (((gridPoint p n s)[i.val]?.getD 0 : ℕ) : ZMod p)) v)
    (hrvalue : ∀ i : Fin n, ∀ s < p ^ n, (rvalue i.val (gridPoint p n s) : ZMod p) =
      eval (fun k : Fin n => (((gridPoint p n s)[k.val]?.getD 0 : ℕ) : ZMod p)) (r i)) :
    (residueValue p n ell B value rvalue : ZMod p) = residue ell r v := by
  have hbound (s : ℕ) (i : Fin n) : (gridPoint (B + 1) n s)[i.val]?.getD 0 ≤ B := by
    rw [gridPoint_get i.isLt]
    exact Nat.lt_succ_iff.mp (Nat.mod_lt _ (Nat.succ_pos B))
  have hterm (s : ℕ) :
      ((if (gridPoint (B + 1) n s).sum ≤ B then
        powerProductCoefficient p n (residueAddress ell (gridPoint (B + 1) n s))
          (gridPoint (B + 1) n s) value rvalue else 0 : ℕ) : ZMod p) =
        term ell r v (fun i => (gridPoint (B + 1) n s)[i.val]?.getD 0) := by
    let j : Fin n → ℕ := fun i => (gridPoint (B + 1) n s)[i.val]?.getD 0
    by_cases hs : (gridPoint (B + 1) n s).sum ≤ B
    · rw [ite_eq_left hs]
      have hsum : (∑ i, j i) ≤ B := by simpa only [grid_sum] using hs
      have heq : B + (ell - 1) * B = ell * B := calc
        _ = (1 + (ell - 1)) * B := by ring
        _ = _ := congrArg (· * B) (by omega)
      have hdeg : (v * ∏ i, r i ^ j i).totalDegree < p - 1 := by
        have hb := (numerator_degree r hr v j).trans
          (Nat.add_le_add hv (Nat.mul_le_mul_left (ell - 1) hsum))
        rw [heq] at hb
        rw [Nat.mul_add, Nat.mul_one] at hcut
        omega
      have he (i : Fin n) : target ell j i < p - 1 := by
        have hi : ell * j i ≤ ell * B := Nat.mul_le_mul_left ell (hbound s i)
        change ell - 1 + ell * j i < p - 1
        rw [Nat.mul_add, Nat.mul_one] at hcut
        omega
      exact powerProductCoefficient_cast v r j (target ell j)
        (residueAddress ell (gridPoint (B + 1) n s)) (gridPoint (B + 1) n s) value rvalue hdeg he
        (fun i => by simp [residueAddress, gridPoint, i.isLt, target, j]) (fun _ => rfl)
        hvalue hrvalue
    · rw [ite_eq_right hs, Nat.cast_zero]
      refine (term_eq_zero_of_degree_lt hell r hr v j ?_).symm
      have : B < ∑ i, j i := Nat.lt_of_not_ge (grid_sum (B + 1) n s ▸ hs)
      change v.totalDegree < n * (ell - 1) + ∑ i, j i
      omega
  rw [residueValue, ZMod.natCast_mod, Nat.cast_sum]
  simp_rw [hterm]
  exact (sum_residue_grid B n (term ell r v)).trans (residue_eq_truncated hell r hr v hv).symm

end Cslib.Complexity.RealAlgebraic
