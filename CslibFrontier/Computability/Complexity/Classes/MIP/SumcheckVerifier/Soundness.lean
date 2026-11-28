/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.MIP.SumcheckVerifier
import CslibFrontier.Probability.PMF.PolynomialAgreement
import CslibFrontier.Probability.PMF.BindFailure
import CslibFrontier.Probability.PMF.Uniform

/-!
# Soundness of prefix-indexed static sumcheck rows

Fix any static proof. On a false initial claim its round checks and terminal evaluation can all
agree only if some accepted row first repairs a false claim. Conditional on the previous prefix,
this requires two different degree-bounded polynomials to agree at a fresh uniform challenge.

## Main results

* `Cslib.Complexity.MIP.SumcheckProof.transcript_sound` gives the sumcheck error bound against
  arbitrary static proofs for a uniformly drawn field vector.
-/

public section

namespace Cslib.Complexity.MIP.SumcheckProof

open Probability Interactive.Sumcheck
open scoped ENNReal

private theorem uniform_snoc (F : Type) [Fintype F] [Nonempty F] (i : ℕ) :
    PMF.uniformOfFintype (Fin (i + 1) → F) =
      (PMF.uniformOfFintype (Fin i → F)).bind fun z =>
        (PMF.uniformOfFintype F).map (Fin.snoc z) := by
  let e := (Equiv.prodComm (Fin i → F) F).trans (Fin.snocEquiv fun _ => F)
  rw [← PMF.uniformOfFintype_map_equiv e, ← PMF.uniformOfFintype_prod, PMF.map_bind]
  simp [PMF.map_comp, e, Function.comp_def]

private abbrev fieldWords {p i : ℕ} (z : Fin i → ZMod p) := List.ofFn fun j => (z j).val

private theorem fieldWords_snoc {p i : ℕ} (z : Fin i → ZMod p) (u : ZMod p) :
    fieldWords (Fin.snoc z u) = fieldWords z ++ [u.val] := by
  rw [fieldWords, List.ofFn_succ']
  simp [fieldWords, List.concat_eq_append]

/-- A false claim of zero Boolean-cube sum survives all consistency checks and the terminal
evaluation with probability at most `n * d / p`. A static proof can choose unrelated coefficient
rows at every external challenge and every public prefix. -/
theorem transcript_sound {n p d : ℕ} [Fact p.Prime] (P : MvPolynomial (Fin n) (ZMod p))
    (hP : ∀ j, P.degreeOf j ≤ d) (hfalse : partialSum P Fin.elim0 ≠ 0)
    (π : List Bool → Bool) (ext : List ℕ) (w : ℕ) :
    (PMF.uniformOfFintype (Fin n → ZMod p)).toOuterMeasure
      {z | let s := transcript π p ext d w (List.ofFn fun j => (z j).val)
           s.ok = true ∧ (s.claim : ZMod p) = MvPolynomial.eval z P} ≤
      n * ((d : ℝ≥0∞) / p) := by
  let good (i : ℕ) : Set (Fin i → ZMod p) :=
    {z | let s := transcript π p ext d w (fieldWords z)
         s.ok = true ∧ (s.claim : ZMod p) = partialSum P z}
  have hprefix (i : ℕ) (hi : i ≤ n) :
      (PMF.uniformOfFintype (Fin i → ZMod p)).toOuterMeasure (good i) ≤
        i * ((d : ℝ≥0∞) / p) := by
    induction i with
    | zero =>
      have hempty : good 0 = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have he : z = Fin.elim0 := Subsingleton.elim _ _
        subst z
        exact hfalse (by simpa [fieldWords] using hz.2.symm)
      simp [hempty]
    | succ i ih =>
      have hi' : i < n := hi
      rw [uniform_snoc, Nat.cast_succ, add_mul, one_mul]
      refine (PMF.toOuterMeasure_bind_le_add _ _ (good i) _ _ ?_).trans
        (add_le_add (ih hi'.le) le_rfl)
      intro z _ hz
      rw [PMF.toOuterMeasure_map_apply]
      let s := transcript π p ext d w (fieldWords z)
      let g := rowPolynomial π p ext (fieldWords z) d w
      have hdeg : g.natDegree ≤ d := natDegree_rowPolynomial_le ..
      have hnext (u : ZMod p) (hu : Fin.snoc z u ∈ good (i + 1)) :
          s.ok = true ∧ accepts d (s.claim : ZMod p) g ∧
            g.eval u = partialSum P (Fin.snoc z u) := by
        change (transcript π p ext d w (fieldWords (Fin.snoc z u))).ok = true ∧ _ at hu
        rw [fieldWords_snoc, transcript_snoc, transcript_challenges] at hu
        have hacc := (WordState.advance_ok_iff _ _ _ hdeg).mp hu.1
        refine ⟨hacc.1, hacc.2, ?_⟩
        have hc := hu.2
        simp only [WordState.advance, Polynomial.natCast_evalCoeffListMod,
          ZMod.natCast_zmod_val] at hc
        exact hc
      by_cases hg : g = roundPoly P z
      · have hempty : Fin.snoc z ⁻¹' good (i + 1) = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro u hu
          obtain ⟨hok, hacc, _⟩ := hnext u hu
          apply hz
          exact ⟨hok, hacc.2.symm.trans (hg ▸ roundPoly_eval_zero_add_one P hi' z)⟩
        simp [hempty]
      · simpa only [ZMod.card, Set.preimage, Set.mem_ofPred_eq] using
          PMF.toOuterMeasure_uniformOfFintype_le_of_eval_eq
          (S := {u : ZMod p | Fin.snoc z u ∈ good (i + 1)}) hg hdeg
          (natDegree_roundPoly_le d P hP hi' z)
          (fun u hu => (hnext u hu).2.2.trans (eval_roundPoly_eq P z u).symm)
  simpa [good, fieldWords, partialSum_self] using hprefix n le_rfl

end Cslib.Complexity.MIP.SumcheckProof
