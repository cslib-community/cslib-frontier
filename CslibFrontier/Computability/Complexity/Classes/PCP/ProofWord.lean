/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PCP.Oracle
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Words
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Complexity.Classes.SharpP.MetricOracle
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Languages.Probabilistic.Oracle.EvalPure

/-!
# Reading integer words from a bit-valued proof oracle

The bit at position `i` of the value at key `q` has address `encPair encBits encNat (q, i)`.
A verifier can read any polynomial number of low bits and interpret them in little-endian order.

## Main definitions

* `Cslib.Complexity.ProofWord.readValue` reads a natural number from a static proof.

## Main results

* `Cslib.Complexity.ProofWord.isOraclePPTOn_readValue` gives the strict oracle-PPT certificate.
* `Cslib.Complexity.ProofWord.run_readValue` identifies the deterministic value under every proof.
* `Cslib.Complexity.ProofWord.exists_value_eq_mod` represents an arbitrary table at all widths.
-/

public section

namespace Cslib.Complexity.ProofWord

open Turing.MultiTapeTM Probability

/-- The low `width` bits of the value stored at `key` in the proof, least significant first. -/
@[expose] def value (π : List Bool → Bool) (key : List Bool) (width : ℕ) : ℕ :=
  ofBits (List.ofFn fun i : Fin width => π (encPair encBits encNat (key, i.val)))

/-- Even a dishonest proof can return only a value with at most the requested number of bits. -/
theorem value_lt_two_pow (π : List Bool → Bool) (key : List Bool) (width : ℕ) :
    value π key width < 2 ^ width := by
  simpa only [value, List.length_ofFn] using ofBits_lt_two_pow
    (List.ofFn fun i : Fin width => π (encPair encBits encNat (key, i.val)))

/-- Read `width` bits at distinct addresses framed by `key`, and return their binary value. -/
def readValue (key : List Bool) (width : ℕ) : WordOracleComp Unit ℕ :=
  OracleComp.interpret ProbOracleComp.query (ofBits <$> readBitsProgram
    (fun (p : List Bool × ℕ) i => encPair encBits encNat (p.1, i)) Prod.snd (key, width))

/-- Polynomial-time keys and unary widths give a strict oracle-PPT binary read. -/
theorem isOraclePPTOn_readValue {α : Type} {enc : α ↪ List Bool}
    {key : α → List Bool} {width : α → ℕ} (hk : ComputableInPolyTime key enc encBits)
    (hw : ComputableInPolyTime width enc encUnary) :
    IsOraclePPTOn enc encNat (fun a => readValue (key a) (width a)) := by
  let e := encPair encBits encUnary
  let req (p : List Bool × ℕ) (i : ℕ) := encPair encBits encNat (p.1, i)
  have hreq : ComputableInPolyTime (fun p : (List Bool × ℕ) × ℕ => req p.1 p.2)
      (encPair e encUnary) encBits :=
    .encoding_comp (((ComputableInPolyTime.fst _ _).comp (.fst _ _)).prod
      (ComputableInPolyTime.unary_to_binary.comp (.snd _ _)))
  have hread := isOraclePPTOn_readBitsProgram (req := req) hreq (ComputableInPolyTime.snd _ _)
  apply IsOraclePPTOn.preprocess (program := fun p : List Bool × ℕ => readValue p.1 p.2) _ (hk.prod hw)
  simpa only [readValue, OracleComp.interpret_map] using
    hread.map_with (f := fun _ bits => ofBits bits) (ComputableInPolyTime.bitsToNat.comp (.snd _ _))

/-- Reading a fixed proof table returns its value with certainty, including when the key is
queried repeatedly from different verifier histories. -/
theorem run_readValue (π : List Bool → Bool) (key : List Bool) (width : ℕ) :
    (Prover.ofProof π).run (readValue key width) () = PMF.pure (value π key width, ()) := by
  classical
  let A : Set (List Bool) := {q | π q}
  let program := ofBits <$> readBitsProgram
    (fun (p : List Bool × ℕ) i => encPair encBits encNat (p.1, i)) Prod.snd (key, width)
  have hquery (q : Unit × List Bool) (s : Unit) :
      ProbOracleComp.runWith (Prover.ofProof π).respond (ProbOracleComp.query q) s =
        (PMF.pure (languageOracle A q)).map (·, s) := by
    simp [ProbOracleComp.runWith_query, Prover.ofProof, languageOracle_apply, A]
  rw [readValue, Prover.run_eq_runWith, ProbOracleComp.runWith_interpret]
  change OracleComp.runWith _ program () = _
  rw [funext (fun q => funext (hquery q))]
  rw [OracleComp.runWith_memoryless, OracleComp.evalWith_pure_oracle]
  rw [PMF.pure_map]
  congr 2
  change OracleComp.interpret (m := Id) (languageOracle A) (ofBits <$> _) = _
  rw [OracleComp.interpret_map, interpret_readBitsProgram]
  change ofBits (List.ofFn _) = _
  apply congrArg ofBits
  apply congrArg List.ofFn
  funext i
  exact Bool.eq_iff_iff.mpr (@decide_eq_true_iff _ (Classical.propDecidable _))

/-- One static bit proof realizes the low bits of every entry of any natural-valued table,
simultaneously for all access widths. -/
theorem exists_value_eq_mod (table : List Bool → ℕ) :
    ∃ π : List Bool → Bool, ∀ key width, value π key width = table key % 2 ^ width := by
  classical
  refine ⟨fun q => decide (q ∈ bitGraph encBits table), fun key width => ?_⟩
  have hbits : (List.ofFn fun i : Fin width =>
      decide (encPair encBits encNat (key, i.val) ∈ bitGraph encBits table)) =
      BitString.lowBits width (table key) := by
    apply List.ext_getElem (by simp [BitString.lowBits])
    intro i hi hj
    simp only [List.getElem_ofFn, BitString.lowBits, List.getElem_map, List.getElem_range]
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact answersBits_bitGraph encBits table key i
  rw [value, hbits, ← BitString.lowBits_mod_two_pow,
    ofBits_lowBits (Nat.mod_lt _ (by positivity))]

end Cslib.Complexity.ProofWord
