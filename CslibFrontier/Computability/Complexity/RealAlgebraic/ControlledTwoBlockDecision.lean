/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.Controlled
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledFeasibility
import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledPowerSection
import CslibFrontier.Computability.Complexity.RealAlgebraic.RelativeWordCriterion
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# A counting-level decision for controlled two-block polynomial zero avoidance

A shared fixed-width word selects a degree piece and a coordinate candidate. The two
controlled feasibility tests check that the candidate exists and that its real fiber has
no zero. The family index is the encoded input. A separate reduction from encoded
sentences would supply the family.

## Main results

* `Controlled.twoBlock_mem`: two-block real zero avoidance at level `C_(a+60)P`.

## References

This adapts `nonnegative_twoBlock_mem` and `twoBlock_mem` in lean-canny's
`ControlledTwoBlockDecision` at `970f28a5ecefc1327402ade16c068aa4b1b2c183`, the
controlled-family step in [OpenAI2026CountingHierarchy].
-/

public section

namespace Cslib.Complexity.RealAlgebraic.Controlled

open Turing.MultiTapeTM ComputableInPolyTime MvPolynomial MvPolynomial.CriticalSystem

variable {α : Type} {n m : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {P : (w : α) → MvPolynomial (Fin (n w + m w)) ℤ}

private theorem nonnegative_twoBlock_mem (C : Controlled P enc a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (hm : ComputableInPolyTime m enc encUnary)
    (hpos : ∀ w (x : Fin (m w) → ℝ) (z : Fin (n w) → ℝ),
      0 ≤ eval₂ (Int.castRingHom ℝ) (Fin.addCases z x) (P w)) :
    {w | ∃ x : Fin (m w) → ℝ, ∀ z : Fin (n w) → ℝ,
      eval₂ (Int.castRingHom ℝ) (Fin.addCases z x) (P w) ≠ 0} ∈
        CountingLevel (a + 60) enc := by
  let ell (w : α) := 2 * (C.degreeBound w + 1) + 1
  have hell (w : α) : 1 ≤ ell w := by dsimp only [ell]; omega
  have heven (w : α) : Even (ell w + 1) := by
    refine ⟨C.degreeBound w + 2, ?_⟩
    dsimp only [ell]
    omega
  have hP (w : α) : (P w).totalDegree ≤ ell w :=
    (C.degree_le w).trans (by dsimp only [ell]; omega)
  let sectionFamily := C.relativeValueSection E hn hm
  let N := sectionFamily.degreeBound
  let b := sectionFamily.massExponent
  let D (w : α) := 2 * (N w + 1)
  let d (w : α) := 2 * (D w + 1)
  let liftFamily := sectionFamily.wordDegreePiece E hm
  let squareFamily := liftFamily.pow (fun _ => 2) (.const 2)
  let decoder := Decoder.pair E Decoder.bits
  have hinput := fst enc encBits
  have harity := unary_add' hm (.const 1)
  have hD := binary_mul' (.const 2) (binary_add' sectionFamily.degree_computable (.const 1))
  have hd := binary_mul' (.const 2) (binary_add' hD (.const 1))
  have hdegree (q : α × List Bool) : squareFamily.degreeBound q = D q.1 * 2 := by
    change liftFamily.degreeBound q * 2 = _
    simp only [liftFamily, wordDegreePiece, degreeBound_boundedDegreePiece]
    rfl
  have hmass (q : α × List Bool) :
      squareFamily.massExponent q = degreePieceMassExponent (N q.1) (b q.1) * 2 := by
    change liftFamily.massExponent q * 2 = _
    simp only [liftFamily, wordDegreePiece, massExponent_boundedDegreePiece]
    rfl
  have hbounded (q : α × List Bool) :=
    (squareFamily.degree_le q).trans (show squareFamily.degreeBound q ≤ d q.1 + 1 by
      rw [hdegree]
      dsimp only [d]
      omega)
  let suffix (q : α × List Bool) := q.2.drop (N q.1).size
  have hsuffix : ComputableInPolyTime suffix (encPair enc encBits) encBits :=
    bitsDropWithInput (snd enc encBits)
      (binary_size.comp (sectionFamily.degree_computable.comp hinput))
  have hpositive (q : α × List Bool) : 0 < m q.1 + 1 := Nat.succ_pos _
  have hdpos (q : α × List Bool) : 1 ≤ d q.1 := by dsimp only [d]; omega
  let selection := squareFamily.selectionFeasibility decoder hpositive hdpos hbounded
    (hd.comp hinput) suffix hsuffix
  let counterexample := ((C.counterexampleOrder hn hm).preprocess Prod.fst hinput).mono
    (show a ≤ (a + 10 + 2) + 20 by omega)
  let rejection := squareFamily.selectionCounterexample counterexample (hn.comp hinput) decoder
    hpositive hdpos hbounded (hd.comp hinput) suffix hsuffix
  let width (w : α) :=
    (N w).size + coordinateFingerprintWitnessWidth ((d w + 1) ^ (m w + 1)) (m w + 1)
  have hwidth : ComputableInPolyTime width enc encUnary :=
    unary_add' (binary_size.comp sectionFamily.degree_computable)
      (coordinateFingerprintWitnessWidth_polyTime
        (binary_pow' (binary_add' hd (.const 1)) harity) harity)
  have hdecision := selection.boundedFeasibilityTests_mem rejection E width hwidth
  convert hdecision using 1
  ext w
  simp only [Set.mem_ofPred_eq, hmass]
  exact exists_emptyFiber_iff_selectionWord (hell w) (heven w) (P w) (hP w) (hpos w)
    (N w) (b w) (sectionFamily.degree_le w) (sectionFamily.mass_le w)

/-- Two-block real zero avoidance for a controlled integer polynomial family at level `a`
belongs to `C_(a+60)P`. The block sizes are computable in unary. Squaring the input
preserves its real zeros and the counting level of its modular evaluator. -/
theorem twoBlock_mem (C : Controlled P enc a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (hm : ComputableInPolyTime m enc encUnary) :
    {w | ∃ x : Fin (m w) → ℝ, ∀ z : Fin (n w) → ℝ,
      eval₂ (Int.castRingHom ℝ) (Fin.addCases z x) (P w) ≠ 0} ∈
        CountingLevel (a + 60) enc := by
  have h := (C.pow (fun _ => 2) (.const 2)).nonnegative_twoBlock_mem E hn hm
    (fun w x z => by
      rw [eval₂_pow]
      exact sq_nonneg _)
  simpa only [eval₂_pow, pow_ne_zero_iff (by decide : (2 : ℕ) ≠ 0)] using h

end Cslib.Complexity.RealAlgebraic.Controlled
