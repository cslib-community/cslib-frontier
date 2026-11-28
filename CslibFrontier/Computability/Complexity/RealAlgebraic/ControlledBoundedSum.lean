/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.Controlled
import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Range

/-!
# Bounded sums of controlled polynomials

A family indexed by binary naturals supplies a controlled sum below a polynomial-time
binary bound. The modular evaluator uses a single counting-level sum. This also gives
sums of squares, since modular powering preserves the summand's level.

Adapted from lean-canny's `ControlledBoundedSum` and `ControlledSumSquares` at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Cslib.Complexity.RealAlgebraic.Controlled

open Turing.MultiTapeTM ComputableInPolyTime MvPolynomial
open scoped BigOperators

variable {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {P : (w : α) → ℕ → MvPolynomial (Fin (n w)) ℤ}

/-- Sum the polynomials with indices below a binary bound at one extra counting level.
The degree, coefficient norm and prime cutoff need only be bounded on those indices. -/
noncomputable def boundedSum
    (C : Controlled (fun q : α × ℕ => P q.1 q.2) (encPair enc encNat) a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (N D b cutoff : α → ℕ)
    (hN : ComputableInPolyTime N enc encNat) (hD : ComputableInPolyTime D enc encNat)
    (hb : ComputableInPolyTime b enc encNat) (hcut : ComputableInPolyTime cutoff enc encNat)
    (hdeg : ∀ w i, i < N w → (P w i).totalDegree ≤ D w)
    (hmass : ∀ w i, i < N w → (P w i).coeffNorm1 ≤ 2 ^ b w)
    (hcutoff : ∀ w i, i < N w → C.cutoff (w, i) ≤ cutoff w) :
    Controlled (fun w => ∑ i ∈ Finset.range (N w), P w i) enc (a + 1) where
  arity_computable := hn
  degreeBound := D
  degree_computable := hD
  degree_le w := totalDegree_finsetSum_le (fun i hi => hdeg w i (Finset.mem_range.mp hi))
  massExponent w := b w + (N w).size
  mass_computable := binary_add' hb (unary_to_binary.comp (binary_size.comp hN))
  mass_le w := by
    apply (MvPolynomial.coeffNorm1_sum_le _ _).trans
    calc
      _ ≤ ∑ _i ∈ Finset.range (N w), 2 ^ b w :=
        Finset.sum_le_sum (fun i hi => hmass w i (Finset.mem_range.mp hi))
      _ = N w * 2 ^ b w := by simp
      _ ≤ 2 ^ (N w).size * 2 ^ b w := Nat.mul_le_mul_right _ (Nat.lt_size_self _).le
      _ = 2 ^ (b w + (N w).size) := by rw [pow_add, Nat.mul_comm]
  cutoff := cutoff
  cutoff_computable := hcut
  evaluate := fun (w, p, z) => (∑ i ∈ Finset.range (N w), C.evaluate ((w, i), p, z)) % p
  evaluate_mem := by
    have hterms : (fun ((w, p, z), i) => C.evaluate ((w, i), p, z)) ∈
        CountingFunction a (encPair (encEvaluation enc) encNat) encNat :=
      CountingFunction.preprocess C.evaluate_mem (by fun_prop)
    have hN' := hN.comp (fst enc (encPair encNat (encList encNat)))
    have hsum := CountingFunction.sum_range
      (Decoder.pair E (Decoder.pair Decoder.nat (Decoder.list Decoder.nat))) hterms hN'
    have hp : ComputableInPolyTime (fun (_, p, _) => p) (encEvaluation enc) encNat :=
      (fst encNat (encList encNat)).comp (snd enc (encPair encNat (encList encNat)))
    exact CountingFunction.nat_mod hsum (CountingFunction.of_polyTime hp)
  evaluate_eq w p z hp hc := by
    let : NeZero p := ⟨hp.ne_zero⟩
    have hcast : ((∑ i ∈ Finset.range (N w), C.evaluate ((w, i), p, z) : ℕ) : ZMod p) =
        eval₂ (Int.castRingHom (ZMod p)) (fun i : Fin (n w) => (z[i.val]?.getD 0 : ZMod p))
          (∑ i ∈ Finset.range (N w), P w i) := by
      rw [Nat.cast_sum, MvPolynomial.eval₂_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [C.evaluate_eq (w, i) p z hp ((hcutoff w i (Finset.mem_range.mp hi)).trans_lt hc)]
      exact ZMod.natCast_zmod_val _
    simpa only [ZMod.val_natCast, evaluation] using congrArg ZMod.val hcast

/-- Aggregate squared equations with the same one-level cost as a bounded sum. -/
noncomputable def sumSquares
    (C : Controlled (fun q : α × ℕ => P q.1 q.2) (encPair enc encNat) a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (N D b cutoff : α → ℕ)
    (hN : ComputableInPolyTime N enc encNat) (hD : ComputableInPolyTime D enc encNat)
    (hb : ComputableInPolyTime b enc encNat) (hcut : ComputableInPolyTime cutoff enc encNat)
    (hdeg : ∀ w i, i < N w → (P w i).totalDegree ≤ D w)
    (hmass : ∀ w i, i < N w → (P w i).coeffNorm1 ≤ 2 ^ b w)
    (hcutoff : ∀ w i, i < N w → C.cutoff (w, i) ≤ cutoff w) :
    Controlled (fun w => ∑ i ∈ Finset.range (N w), P w i ^ 2) enc (a + 1) := by
  refine (C.pow (fun _ => 2) (.const 2)).boundedSum E hn N
    (fun w => 2 * D w) (fun w => b w * 2) cutoff hN
    (binary_mul' (.const 2) hD) (binary_mul' hb (.const 2)) hcut ?_ ?_ hcutoff
  · intro w i hi
    exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (hdeg w i hi))
  · intro w i hi
    rw [pow_mul]
    exact (MvPolynomial.coeffNorm1_pow_le _ _).trans (Nat.pow_le_pow_left (hmass w i hi) 2)

/-- Squaring the summands uses the supplied prime cutoff. -/
@[simp] theorem cutoff_sumSquares
    (C : Controlled (fun q : α × ℕ => P q.1 q.2) (encPair enc encNat) a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (N D b cutoff : α → ℕ)
    (hN : ComputableInPolyTime N enc encNat) (hD : ComputableInPolyTime D enc encNat)
    (hb : ComputableInPolyTime b enc encNat) (hcut : ComputableInPolyTime cutoff enc encNat)
    (hdeg : ∀ w i, i < N w → (P w i).totalDegree ≤ D w)
    (hmass : ∀ w i, i < N w → (P w i).coeffNorm1 ≤ 2 ^ b w)
    (hcutoff : ∀ w i, i < N w → C.cutoff (w, i) ≤ cutoff w) :
    (C.sumSquares E hn N D b cutoff hN hD hb hcut hdeg hmass hcutoff).cutoff = cutoff := by
  simp only [sumSquares, boundedSum]

end Cslib.Complexity.RealAlgebraic.Controlled
