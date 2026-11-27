/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.MIP.SumcheckVerifier.Soundness
public import CslibFrontier.Computability.Complexity.Classes.MIP.SumcheckVerifier.Completeness
public import CslibFrontier.Computability.Complexity.Classes.MIP.Arithmetization
import CslibFrontier.Probability.PMF.BindFailure
import CslibFrontier.Probability.PMF.Uniform

/-!
# Static sumcheck proofs for the succinct tableau

The verifier samples an external point to choose the tableau constraint polynomial. Independent
sumcheck challenges then test its claimed Boolean-cube sum against its actual evaluation. This
is a prime-field adaptation of the oracle satisfiability arithmetization. A random multilinear
equality weight detects a nonsatisfying assignment over a finite field.

## Main results

* `Cslib.Complexity.MIP.SumcheckProof.exists_proof_of_satisfiable` supplies one static proof
  correct on all challenge pairs and preserving the other proof keys.
* `Cslib.Complexity.MIP.SumcheckProof.transcript_sound_of_unsatisfiable` combines both sources
  of error for an unsatisfiable succinct CNF and an arbitrary fixed proof.

## References

* [Babai, Fortnow, and Lund, §§3 and 4.2–4.5][BabaiFortnowLund1991]
-/

public section

namespace Cslib.Complexity.MIP.SumcheckProof

open Circuits Circuits.Boolean Probability Interactive.Sumcheck MvPolynomial
open scoped ENNReal

/-- Satisfiability gives a multilinear assignment and one proof serving every pair of
challenges. Coefficients outside the sumcheck namespace retain the chosen background table. -/
theorem exists_proof_of_satisfiable {Q L p d : ℕ} [Fact p.Prime]
    (c : Circuit signature Q (3 * (L + 1))) (h : (SuccinctVerifier.toCNF c).Satisfiable)
    (hd : 1 + 3 * c.size + 3 * (L + 1) ≤ d)
    (other : MvPolynomial (Fin L) (ZMod p) → List Bool → ℕ) :
    ∃ A ∈ restrictDegree (Fin L) (ZMod p) 1, ∃ π : List Bool → Bool,
      (∀ r z : Fin (Q + c.size) → ZMod p, ∀ w, p ≤ 2 ^ w →
        let s := transcript π p (List.ofFn fun j => (r j).val) d w (List.ofFn fun j => (z j).val)
        s.ok = true ∧ (s.claim : ZMod p) = eval z (tableauConstraintPoly c A r)) ∧
      ∀ key w, key.take 3 ≠ [true, true, false] →
        ProofWord.value π key w = other A key % 2 ^ w := by
  obtain ⟨A, hA, hsum⟩ := sumcheck_proof_complete_of_satisfiable (F := ZMod p) c h hd
  let point (ext : List ℕ) (j : Fin (Q + c.size)) : ZMod p := ext.getD j 0
  let P (ext : List ℕ) := tableauConstraintPoly c A (point ext)
  obtain ⟨π, hπ, hrest⟩ := exists_proof_transcript_complete P (other A)
    (fun ext j => (tableauConstraintPoly_degreeOf_le c hA (point ext) j).trans hd)
  refine ⟨A, hA, π, ?_, hrest⟩
  intro r z w hw
  have hp : point (List.ofFn fun j => (r j).val) = r := by
    funext j
    simp [point, List.getD_eq_getElem?_getD, j.isLt]
  have hzero : partialSum (P (List.ofFn fun j => (r j).val)) Fin.elim0 = 0 := by
    simpa only [P, hp] using (show partialSum (tableauConstraintPoly c A r) Fin.elim0 = 0 from
      (hsum r).1)
  simpa only [P, hp, ZMod.natCast_zmod_val] using
    hπ (List.ofFn fun j => (r j).val) w (fun j => (z j).val) hw hzero

/-- For an unsatisfiable succinct CNF and any multilinear assignment polynomial, the ideal
terminal evaluation agrees with an accepted static sumcheck transcript with probability at most
`(Q + c.size) * (d + 1) / p`. The external point and the sumcheck challenges are independent. -/
theorem transcript_sound_of_unsatisfiable {Q L p d : ℕ} [Fact p.Prime]
    (c : Circuit signature Q (3 * (L + 1))) (h : ¬ (SuccinctVerifier.toCNF c).Satisfiable)
    {A : MvPolynomial (Fin L) (ZMod p)} (hA : A ∈ restrictDegree (Fin L) (ZMod p) 1)
    (hd : 1 + 3 * c.size + 3 * (L + 1) ≤ d) (π : List Bool → Bool) (w : ℕ) :
    (PMF.uniformOfFintype
      ((Fin (Q + c.size) → ZMod p) × (Fin (Q + c.size) → ZMod p))).toOuterMeasure
      {rz | let s := transcript π p (List.ofFn fun i => (rz.1 i).val) d w
              (List.ofFn fun i => (rz.2 i).val)
            s.ok = true ∧ (s.claim : ZMod p) = eval rz.2 (tableauConstraintPoly c A rz.1)} ≤
      (Q + c.size : ℕ) * ((d : ℝ≥0∞) + 1) / p := by
  classical
  let R := Q + c.size
  let bad : Set (Fin R → ZMod p) := {r | partialSum (tableauConstraintPoly c A r) Fin.elim0 = 0}
  have hdeg := fun r v => (tableauConstraintPoly_degreeOf_le c hA r v).trans hd
  have hcard := (sumcheck_sound_of_not_satisfiable c h A hdeg).1
  have hbad : (PMF.uniformOfFintype (Fin R → ZMod p)).toOuterMeasure bad ≤ (R : ℝ≥0∞) / p := by
    rw [PMF.toOuterMeasure_uniformOfFintype, ← div_eq_mul_inv,
      ENNReal.le_div_iff_mul_le
        (Or.inl (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) (by simp),
      ← ENNReal.mul_div_right_comm,
      ENNReal.div_le_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)]
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card] at hcard ⊢
    exact_mod_cast hcard
  rw [← PMF.uniformOfFintype_prod]
  refine (PMF.toOuterMeasure_bind_le_add _ _ bad _ ((R : ℝ≥0∞) * (d / p)) ?_).trans ?_
  · intro r _ hr
    rw [PMF.toOuterMeasure_map_apply]
    simpa only [Set.preimage, Set.mem_ofPred_eq] using transcript_sound
      (tableauConstraintPoly c A r) (hdeg r) hr π (List.ofFn fun i => (r i).val) w
  · calc _ ≤ R / (p : ℝ≥0∞) + R * ((d : ℝ≥0∞) / p) := add_le_add hbad le_rfl
         _ = _ := by simp [R, div_eq_mul_inv, mul_add, add_mul, mul_assoc, add_comm]

end Cslib.Complexity.MIP.SumcheckProof
