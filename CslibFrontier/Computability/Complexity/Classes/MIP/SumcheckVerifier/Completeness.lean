/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.MIP.SumcheckVerifier
import Mathlib.Data.List.OfFn

/-!
# Perfect completeness of static sumcheck transcripts

If a polynomial sums to zero on the Boolean cube, its honest coefficient rows pass every round
for every tape of challenges. The final integer claim represents the polynomial evaluated at
that tape.

## Main results

* `Cslib.Complexity.MIP.SumcheckProof.exists_proof_transcript_complete` realizes all honest
  computations using a single static proof and preserves the other components of that proof.
-/

public section

namespace Cslib.Complexity.MIP.SumcheckProof

open Interactive.Sumcheck

private theorem roundPoly_cast_length {p n i : ℕ} [Fact p.Prime]
    (P : MvPolynomial (Fin n) (ZMod p)) (rs : List ℕ) (z : Fin i → ℕ)
    (hlen : rs.length = i) (hz : ∀ j, rs.get j = z (j.cast hlen)) :
    roundPoly P (fun j => (rs.get j : ZMod p)) = roundPoly P (fun j => (z j : ZMod p)) := by
  subst i
  congr 1
  funext j
  exact congrArg (Nat.cast : ℕ → ZMod p) (hz j)

/-- With honest rows and a zero Boolean-cube sum, every tape of `n` challenges passes all
consistency checks, and the final claim is `P` at the point represented by the tape. -/
theorem transcript_complete {p n d width : ℕ} [Fact p.Prime] (π : List Bool → Bool)
    (P : MvPolynomial (Fin n) (ZMod p)) (ext : List ℕ)
    (hzero : partialSum P Fin.elim0 = 0)
    (hπ : ∀ rs : List ℕ, rs.length < n → rowPolynomial π p ext rs d width =
      roundPoly P (fun j => (rs.get j : ZMod p))) (z : Fin n → ℕ) :
    (transcript π p ext d width (List.ofFn z)).ok = true ∧
      ((transcript π p ext d width (List.ofFn z)).claim : ZMod p) =
        MvPolynomial.eval (fun j => (z j : ZMod p)) P := by
  suffices H : ∀ (i : ℕ), i ≤ n → ∀ ys : Fin i → ℕ,
      (transcript π p ext d width (List.ofFn ys)).ok = true ∧
      ((transcript π p ext d width (List.ofFn ys)).claim : ZMod p) =
        partialSum P (fun j => (ys j : ZMod p)) by
    simpa only [partialSum_self] using H n le_rfl z
  intro i hi ys
  induction i with
  | zero =>
    rw [List.ofFn_zero, transcript_nil]
    refine ⟨rfl, ?_⟩
    simp only [Nat.cast_zero]
    convert hzero.symm using 2
  | succ i ih =>
    let xs := List.ofFn fun j => ys (Fin.castSucc j)
    let r := ys (Fin.last i)
    have hlen : xs.length = i := List.length_ofFn
    have hx : List.ofFn ys = xs ++ [r] := by
      simpa only [List.concat_eq_append] using List.ofFn_succ' ys
    have hround : rowPolynomial π p ext xs d width =
        roundPoly P (fun j => (ys (Fin.castSucc j) : ZMod p)) :=
      (hπ xs (by omega)).trans
        (roundPoly_cast_length P xs (fun j => ys (Fin.castSucc j)) hlen (by
          intro j
          simp only [xs, List.get_eq_getElem, List.getElem_ofFn]
          rfl))
    have hdegree := natDegree_rowPolynomial_le π p ext xs d width
    have ⟨hok, hv⟩ := ih (by omega) (fun j => ys (Fin.castSucc j))
    rw [hx, transcript_snoc, transcript_challenges]
    constructor
    · refine (WordState.advance_ok_iff _ _ _ hdegree).mpr ⟨hok, hdegree, ?_⟩
      change (rowPolynomial π p ext xs d width).eval 0 +
        (rowPolynomial π p ext xs d width).eval 1 = _
      rw [hround, roundPoly_eval_zero_add_one P (by omega)]
      exact hv.symm
    · change (Polynomial.evalCoeffListMod p r (row π ext xs d width) : ZMod p) = _
      rw [Polynomial.natCast_evalCoeffListMod]
      change (rowPolynomial π p ext xs d width).eval (r : ZMod p) = _
      rw [hround, eval_roundPoly_eq]
      exact congrArg (partialSum P) (Fin.snoc_init_self (q := fun j => (ys j : ZMod p)))

/-- A single static bit proof yields accepting transcripts and the correct final values for all
honest zero-sum instances and all challenge tapes. Other tags retain the chosen table. -/
theorem exists_proof_transcript_complete {p n d : ℕ} [Fact p.Prime]
    (P : List ℕ → MvPolynomial (Fin n) (ZMod p)) (other : List Bool → ℕ)
    (hP : ∀ ext i, (P ext).degreeOf i ≤ d) :
    ∃ π : List Bool → Bool,
      (∀ ext w (z : Fin n → ℕ), p ≤ 2 ^ w → partialSum (P ext) Fin.elim0 = 0 →
        (transcript π p ext d w (List.ofFn z)).ok = true ∧
        ((transcript π p ext d w (List.ofFn z)).claim : ZMod p) =
          MvPolynomial.eval (fun j => (z j : ZMod p)) (P ext)) ∧
      ∀ key w, key.take 3 ≠ [true, true, false] →
        ProofWord.value π key w = other key % 2 ^ w := by
  obtain ⟨π, hπ, hout⟩ := exists_proof_roundPoly P other hP
  exact ⟨π, fun ext w z hw hzero => transcript_complete π (P ext) ext hzero
    (fun rs hlen => hπ ext rs w hlen hw) z, hout⟩

end Cslib.Complexity.MIP.SumcheckProof
