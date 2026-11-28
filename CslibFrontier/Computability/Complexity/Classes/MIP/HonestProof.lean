/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.MIP.CorrectionHonest
public import CslibFrontier.Computability.Complexity.Classes.MIP.SumcheckVerifier.Tableau

/-!
# A shared honest bit proof for the algebraic tableau verifier

A satisfying assignment supplies one multilinear polynomial. The verifier queries its point
values, affine axis restrictions, arbitrary line restrictions, and sumcheck transcripts in
disjoint address ranges of one static proof.

## Main results

* `Cslib.Complexity.MIP.exists_honestProof_of_satisfiable` supplies one proof giving the correct
  results in all three verifier phases for every choice of field challenges.
-/

public section

namespace Cslib.Complexity.MIP

open Circuits Circuits.Boolean Code MvPolynomial SumcheckProof

private theorem exists_lineTables {n p : ℕ} [NeZero n] [Fact p.Prime]
    {A : MvPolynomial (Fin n) (ZMod p)} (hA : A ∈ restrictDegree (Fin n) (ZMod p) 1) :
    ∃ table : List Bool → ℕ, ∀ π : List Bool → Bool,
      (∀ key w, key.take 3 ≠ [true, true, false] →
        ProofWord.value π key w = table key % 2 ^ w) →
      proofPoint π p = (fun x => eval x A) ∧
        (∀ prec, (Prover.ofProof π).run (axisRound n p prec) () = PMF.pure (true, ())) ∧
        ∀ x v, correctionAnswer π x v = some (eval x A).val := by
  obtain ⟨lines, hlines⟩ := exists_axisTable_of_mem_restrictDegree hA
  have hf := isMultilinear_eval_of_mem_restrictDegree hA
  let lineTable := extendCorrectionTable hf (fun _ => 0)
  let table := extendAxisTable (fun x => eval x A) lines lineTable
  refine ⟨table, fun π hπ => ?_⟩
  have haxis (key : List Bool) (hk : key.take 2 ≠ [true, true]) :
      ProofWord.value π key p.size = table key % 2 ^ p.size := by
    apply hπ
    intro h
    apply hk
    simpa only [List.take_take, show min 2 3 = 2 by decide, List.take_succ_cons, List.take_zero]
      using congrArg (List.take 2) h
  obtain ⟨hpoint, hround⟩ := hlines lineTable π haxis
  refine ⟨hpoint, hround, correctionAnswer_extendCorrectionTable hf (fun _ => 0) π hpoint ?_⟩
  intro key hk
  rw [hπ key _ (by rw [hk]; decide)]
  have hkey : key = [true, true, true] ++ key.drop 3 :=
    (List.take_append_drop 3 key).symm.trans (congrArg (· ++ key.drop 3) hk)
  rw [hkey]
  exact congrArg (· % 2 ^ QBFProtocol.replyLimit p n)
    (extendAxisTable_reserved _ lines lineTable (true :: key.drop 3))

/-- A satisfiable succinct 3CNF admits one proof that passes the axis test, corrects to the
same multilinear assignment on every line, and passes sumcheck at its correct terminal value.
All challenges vary after the proof has been fixed. -/
theorem exists_honestProof_of_satisfiable {Q L p d : ℕ} [NeZero L] [Fact p.Prime]
    (c : Circuit signature Q (3 * (L + 1))) (hsat : (SuccinctVerifier.toCNF c).Satisfiable)
    (hd : 1 + 3 * c.size + 3 * (L + 1) ≤ d) :
    ∃ A ∈ restrictDegree (Fin L) (ZMod p) 1, ∃ π : List Bool → Bool,
      proofPoint π p = (fun x => eval x A) ∧
      (∀ prec, (Prover.ofProof π).run (axisRound L p prec) () = PMF.pure (true, ())) ∧
      (∀ x v, correctionAnswer π x v = some (eval x A).val) ∧
      ∀ r z : Fin (Q + c.size) → ZMod p,
        let s := transcript π p (List.ofFn fun j => (r j).val) d p.size
          (List.ofFn fun j => (z j).val)
        s.ok = true ∧ (s.claim : ZMod p) = eval z (tableauConstraintPoly c A r) := by
  classical
  let table (A : MvPolynomial (Fin L) (ZMod p)) (hA : A ∈ restrictDegree (Fin L) (ZMod p) 1) :=
    Classical.choose (exists_lineTables hA)
  obtain ⟨A, hA, π, hsum, hrest⟩ := exists_proof_of_satisfiable (p := p) c hsat hd table
  obtain ⟨hpoint, haxis, hcorrect⟩ := Classical.choose_spec (exists_lineTables hA) π hrest
  exact ⟨A, hA, π, hpoint, haxis, hcorrect, fun r z => hsum r z _ (Nat.lt_size_self p).le⟩

end Cslib.Complexity.MIP
