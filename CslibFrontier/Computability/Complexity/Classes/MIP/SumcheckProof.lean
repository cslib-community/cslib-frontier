/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PCP.ProofWord
public import CslibFrontier.Computability.Interactive.Sumcheck.Words
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Foundations.Data.Polynomial.CoeffList
public import Mathlib.Algebra.Field.ZMod
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Static coefficient tables for sumcheck

A row contains the prover's round polynomial at a public challenge history. The row key includes
the external challenges and the challenges in earlier sumcheck rounds. All coefficients are fixed
before the next challenge, including for dishonest bit tables.

## Main definitions

* `Cslib.Complexity.MIP.SumcheckProof.readRow` reads the coefficients in order of increasing degree.
* `Cslib.Complexity.MIP.SumcheckProof.rowPolynomial` interprets a row over `ZMod p`.
* `Cslib.Complexity.MIP.SumcheckProof.extendTable` adds honest sumcheck rows to another table.

## Main results

* `Cslib.Complexity.MIP.SumcheckProof.isOraclePPTOn_readRow` certifies the query program.
* `Cslib.Complexity.MIP.SumcheckProof.exists_proof_roundPoly` realizes all honest rounds
  simultaneously and preserves the other components of the static proof.
-/

public section

namespace Cslib.Complexity.MIP.SumcheckProof

open Turing.MultiTapeTM Probability

/-- The address of one coefficient in a prefix-indexed sumcheck table. -/
structure Address where
  /-- External challenges fixing the sumcheck instance. -/
  external : List ℕ
  /-- Challenges disclosed in earlier rounds. -/
  challenges : List ℕ
  /-- Exponent of this coefficient. -/
  exponent : ℕ

/-- The framed list of external binary residues, the framed list of earlier binary challenges,
and the binary exponent, in that order. -/
enc_structure encAddress : Address where
  external : (encList encNat),
  challenges : (encList encNat),
  exponent : encNat

/-- Sumcheck coefficient keys have tag `110` followed by the framed binary address. -/
@[expose] def coefficientKey : Address ↪ List Bool :=
  ⟨fun a => true :: true :: false :: encAddress a, fun _ _ h =>
    encAddress.injective (List.cons.inj (List.cons.inj (List.cons.inj h).2).2).2⟩

private def keys (external challenges : List ℕ) (d : ℕ) : List (List Bool) :=
  (List.range (d + 1)).map fun i => coefficientKey ⟨external, challenges, i⟩

/-- Read the coefficients of the next polynomial, from its constant coefficient through degree
`d` inclusive. -/
def readRow (external challenges : List ℕ) (d width : ℕ) : WordOracleComp Unit (List ℕ) :=
  ProofWord.readValues (keys external challenges d) width

/-- Values in a row of a bit table, indexed just by the public history and exponent. -/
@[expose] def row (π : List Bool → Bool) (external challenges : List ℕ) (d width : ℕ) : List ℕ :=
  (List.range (d + 1)).map fun i =>
    ProofWord.value π (coefficientKey ⟨external, challenges, i⟩) width

/-- A strict oracle-PPT verifier can read the row if it computes the public challenge lists and
the unary degree and bit-width bounds in polynomial time. -/
theorem isOraclePPTOn_readRow {α : Type} {enc : α ↪ List Bool} {external challenges : α → List ℕ}
    {d width : α → ℕ} (he : ComputableInPolyTime external enc (encList encNat))
    (hc : ComputableInPolyTime challenges enc (encList encNat))
    (hd : ComputableInPolyTime d enc encUnary) (hw : ComputableInPolyTime width enc encUnary) :
    IsOraclePPTOn enc (encList encNat)
      (fun a => readRow (external a) (challenges a) (d a) (width a)) := by
  apply ProofWord.isOraclePPTOn_readValues _ hw
  have hi := ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd enc encUnary)
  have ha : ComputableInPolyTime (fun q : α × ℕ => (⟨external q.1, challenges q.1, q.2⟩ : Address))
      (encPair enc encUnary) encAddress := by fun_prop
  have hbody := ComputableInPolyTime.bitsCons (ComputableInPolyTime.const true)
    (ComputableInPolyTime.bitsCons (ComputableInPolyTime.const true)
      (ComputableInPolyTime.bitsCons (ComputableInPolyTime.const false)
        (ComputableInPolyTime.encoding_comp ha)))
  exact ComputableInPolyTime.mapWithInput (by fun_prop :
    ComputableInPolyTime (fun a => List.range (d a + 1)) enc (encList encUnary)) hbody

/-- The row lookup is deterministic under a fixed static proof. -/
theorem run_readRow (π : List Bool → Bool) (external challenges : List ℕ) (d width : ℕ) :
    (Prover.ofProof π).run (readRow external challenges d width) () =
      PMF.pure (row π external challenges d width, ()) := by
  simp [readRow, ProofWord.run_readValues, keys, row, List.map_map, Function.comp_def]

/-- The polynomial over the residue ring obtained from this public history. -/
@[expose] noncomputable def rowPolynomial (π : List Bool → Bool) (p : ℕ) (external challenges : List ℕ)
    (d width : ℕ) : Polynomial (ZMod p) :=
  Polynomial.ofCoeffList ((row π external challenges d width).map Nat.cast)

/-- Even a dishonest proof's polynomial has degree at most the requested degree. -/
theorem natDegree_rowPolynomial_le (π : List Bool → Bool) (p : ℕ) (external challenges : List ℕ)
    (d width : ℕ) : (rowPolynomial π p external challenges d width).natDegree ≤ d := by
  apply (Polynomial.natDegree_ofCoeffList_le _).trans
  simp [row]

/-- Read the polynomial for the current public history and advance at the given challenge.
The row address depends only on the earlier challenges. -/
@[expose] def advance (p : ℕ) (external : List ℕ) (d width r : ℕ) (s : Interactive.Sumcheck.WordState) :
    WordOracleComp Unit Interactive.Sumcheck.WordState :=
  (fun cs => s.advance p cs r) <$> readRow external s.challenges d width

/-- The complete static-proof round update is strict oracle PPT for every oracle. -/
theorem isOraclePPTOn_advance {α : Type} {enc : α ↪ List Bool} {p d width r : α → ℕ}
    {ext : α → List ℕ} {s : α → Interactive.Sumcheck.WordState}
    (hp : ComputableInPolyTime p enc encNat) (he : ComputableInPolyTime ext enc (encList encNat))
    (hd : ComputableInPolyTime d enc encUnary) (hw : ComputableInPolyTime width enc encUnary)
    (hr : ComputableInPolyTime r enc encNat)
    (hs : ComputableInPolyTime s enc Interactive.Sumcheck.encWordState) :
    IsOraclePPTOn enc Interactive.Sumcheck.encWordState
      (fun x => advance (p x) (ext x) (d x) (width x) (r x) (s x)) :=
  IsOraclePPTOn.map_with
    (isOraclePPTOn_readRow he (Interactive.Sumcheck.encWordState_challenges_polyTime hs) hd hw)
    (Interactive.Sumcheck.WordState.computableInPolyTime_advance (hs.comp (.fst _ _))
      (hp.comp (.fst _ _)) (.snd _ _) (hr.comp (.fst _ _)))

/-- The round under a fixed proof performs exactly the update for its stored coefficients. -/
theorem run_advance (π : List Bool → Bool) (p : ℕ) (ext : List ℕ) (d width r : ℕ)
    (s : Interactive.Sumcheck.WordState) :
    (Prover.ofProof π).run (advance p ext d width r s) () =
      PMF.pure (s.advance p (row π ext s.challenges d width) r, ()) := by
  simp only [advance, Prover.run, ProbOracleComp.runWith_map]
  change PMF.map _ ((Prover.ofProof π).run (readRow ext s.challenges d width) ()) = _
  rw [run_readRow, PMF.pure_map]
  rfl

/-- Extend a natural-valued table on all other proof keys with coefficient rows. -/
noncomputable def extendTable {p : ℕ} (F : List ℕ → List ℕ → Polynomial (ZMod p))
    (other : List Bool → ℕ) : List Bool → ℕ :=
  Function.extend coefficientKey (fun a => ((F a.external a.challenges).coeff a.exponent).val) other

/-- The extension stores the coefficients of its designated row. -/
theorem extendTable_coefficientKey {p : ℕ} (F : List ℕ → List ℕ → Polynomial (ZMod p))
    (other : List Bool → ℕ) (a : Address) :
    extendTable F other (coefficientKey a) = ((F a.external a.challenges).coeff a.exponent).val :=
  coefficientKey.injective.extend_apply _ _ a

/-- Queries outside the sumcheck tag access the supplied background table. -/
theorem extendTable_of_tag_ne {p : ℕ} (F : List ℕ → List ℕ → Polynomial (ZMod p))
    (other : List Bool → ℕ) {q : List Bool} (hq : q.take 3 ≠ [true, true, false]) :
    extendTable F other q = other q := by
  apply Function.extend_apply'
  rintro ⟨a, rfl⟩
  exact hq rfl

/-- Reconstruct a row of an honest table whenever the modulus fits the word width and the
requested degree covers the polynomial. The proof may serve all rows and other kinds of keys. -/
theorem rowPolynomial_eq {p : ℕ} [NeZero p] (F : List ℕ → List ℕ → Polynomial (ZMod p))
    (other : List Bool → ℕ) (π : List Bool → Bool) (external challenges : List ℕ) (d width : ℕ)
    (hπ : ∀ key, ProofWord.value π key width = extendTable F other key % 2 ^ width)
    (hp : p ≤ 2 ^ width) (hd : (F external challenges).natDegree ≤ d) :
    rowPolynomial π p external challenges d width = F external challenges := by
  unfold rowPolynomial row
  rw [List.map_map]
  convert Polynomial.ofCoeffList_coeffsBelow (P := F external challenges) (n := d + 1)
    (by omega) using 2
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, hπ, extendTable_coefficientKey,
    Nat.mod_eq_of_lt ((ZMod.val_lt _).trans_le hp), ZMod.natCast_zmod_val]

/-- One static proof realizes the honest sumcheck polynomial for every external challenge, every
valid prefix and every sufficiently large access width. Its values outside the sumcheck tag
are the low bits of the prescribed background table. -/
theorem exists_proof_roundPoly {n p d : ℕ} [Fact p.Prime]
    (P : List ℕ → MvPolynomial (Fin n) (ZMod p)) (other : List Bool → ℕ)
    (hP : ∀ external j, (P external).degreeOf j ≤ d) :
    ∃ π : List Bool → Bool,
      (∀ external (challenges : List ℕ) width, challenges.length < n → p ≤ 2 ^ width →
        rowPolynomial π p external challenges d width =
          Interactive.Sumcheck.roundPoly (P external) (fun j => (challenges.get j : ZMod p))) ∧
      ∀ key width, key.take 3 ≠ [true, true, false] →
        ProofWord.value π key width = other key % 2 ^ width := by
  let F (external challenges : List ℕ) : Polynomial (ZMod p) :=
    Interactive.Sumcheck.roundPoly (P external) (fun j => (challenges.get j : ZMod p))
  obtain ⟨π, hπ⟩ := ProofWord.exists_value_eq_mod (extendTable F other)
  refine ⟨π, fun e c w hc hw => rowPolynomial_eq F other π e c d w (fun k => hπ k w) hw ?_,
    fun q w hq => (hπ q w).trans (congrArg (· % 2 ^ w) (extendTable_of_tag_ne _ _ hq))⟩
  exact Interactive.Sumcheck.natDegree_roundPoly_le d (P e) (hP e) hc _

end Cslib.Complexity.MIP.SumcheckProof
