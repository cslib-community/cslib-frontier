/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle.Diagonal
public import CslibFrontier.Computability.Complexity.Classes.Oracle.Deterministic
public import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# An oracle relative to which `P` and `NP` differ

For an oracle language `B`, the unary length language `Cslib.Complexity.unaryLengthLanguage B`
consists of the words `1ⁿ` such that `B` has a word of length `n`. Baker, Gill and Solovay
construct an oracle `B` for which this language is not in `P` relative to `B`. For every `B`, its
unary length language is in `NP` relative to that same `B` (a certificate is a word of length `n`
in `B`) [BakerGillSolovay1975]. We follow [Arora and Barak, Theorem 3.7][AroraBarak09].

The oracle diagonalizes against all candidate deciders at once
(`Cslib.Complexity.exists_oracle_diagonal`). The candidates are the fair-coin tables with one
oracle channel and control states `Fin m`, under the clocks `c * (n + 1) ^ d`, run on `1ⁿ` with
every coin fixed to `false`. They are countably many, and each makes at most one request per
instruction, hence fewer than `2 ^ n` requests for all large `n`. Every decider in `P` relative to
`B` is one of them on the instances `1ⁿ`
(`Cslib.Probability.IsOraclePPTOn.exists_fin_run_pure_false`), so none decides the unary length
language (`Cslib.Complexity.exists_unaryLengthLanguage_notMem_PWithOracle`).

The verifier checks that the instance consists of `true` symbols, by a two-state transducer, and
makes one request: the certificate itself
(`Cslib.Complexity.unaryLengthLanguage_mem_NPWithOracle`).
Relative to the diagonal oracle, `P` is therefore strictly contained in `NP`
(`Cslib.Complexity.exists_PWithOracle_ssubset_NPWithOracle`).

The query argument also applies to reductions into a fixed language. Test the machine's output
for membership in the encoded target after its last oracle query. This test need not be
efficient, since the diagonalization bounds only the oracle queries of the candidate reduction.
Taking 3SAT as the target gives Exercise 3 §6 of the January 2007 draft [AroraBarak07].

## Main definitions

* `Cslib.Complexity.unaryLengthLanguage`: the words `1ⁿ` such that the oracle has a word of
  length `n`.
* `Cslib.Complexity.BakerGillSolovay.Candidate.output`: the output of a clocked oracle machine on
  `1ⁿ`.

## Main results

* `Cslib.Complexity.exists_unaryLengthLanguage_not_reducibleWithOracle`: for any fixed target, some
  oracle's unary length language is in relative `NP` and has no polynomial-time oracle reduction
  to that target.
* `Cslib.Complexity.exists_unaryLengthLanguage_notMem_PWithOracle`: for some oracle `B`, the unary
  length language of `B` is not in `P` relative to `B`.
* `Cslib.Complexity.unaryLengthLanguage_mem_NPWithOracle`: the unary length language of every
  oracle is in `NP` relative to it.
* `Cslib.Complexity.exists_PWithOracle_ssubset_NPWithOracle`,
  `Cslib.Complexity.exists_PWithOracle_ne_NPWithOracle`: relative to some oracle, `P ⊊ NP`.

## References

* [T. Baker, J. Gill, R. Solovay, *Relativizations of the P =? NP Question*][BakerGillSolovay1975]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM Probability

/-- The words `1ⁿ` such that `B` has a word of length `n`. -/
def unaryLengthLanguage (B : Set (List Bool)) : Set (List Bool) :=
  {x | (∀ b ∈ x, b = true) ∧ ∃ w ∈ B, w.length = x.length}

theorem replicate_mem_unaryLengthLanguage {B : Set (List Bool)} {n : ℕ} :
    List.replicate n true ∈ unaryLengthLanguage B ↔ ∃ w ∈ B, w.length = n := by
  simp only [unaryLengthLanguage, Set.mem_ofPred_eq, List.length_replicate]
  exact and_iff_right fun b hb => (List.eq_of_mem_replicate hb)

namespace BakerGillSolovay

/-- A candidate decider: a fair-coin table with `k` work tapes, control `Fin m` and one oracle
channel, together with the constants `c` and `d` of its clock `c * (n + 1) ^ d`. -/
abbrev Candidate : Type := Σ k m : ℕ, MultiTapePTM k Bool (Fin m) Unit × ℕ × ℕ

/-- The clock `c * (n + 1) ^ d` of a candidate on inputs of length `n`. -/
def Candidate.clock (candidate : Candidate) (n : ℕ) : ℕ :=
  candidate.2.2.2.1 * (n + 1) ^ candidate.2.2.2.2

/-- The output of a candidate on `1ⁿ` after its clocked run with all coins fixed to false. -/
def Candidate.output (candidate : Candidate) (n : ℕ) : WordQueryComp Unit (List Bool) :=
  candidate.2.2.1.run (pure false)
    (fun op word => OracleComp.query (op, word)) (candidate.clock n) (List.replicate n true)

/-- A candidate makes at most one request per instruction. -/
private theorem Candidate.length_queriesWith_output_le (candidate : Candidate) (n : ℕ)
    (A : Set (List Bool)) :
    (OracleComp.queriesWith (languageOracle A) (candidate.output n)).length ≤
      candidate.clock n := by
  simp only [output, MultiTapePTM.run, MultiTapePTM.runFrom, OracleComp.queriesWith_map]
  exact MultiTapeMachine.length_queriesWith_runConfigFrom_le candidate.2.2.1
    (fun choices => choices false) _ _ _

/-- Every clock is eventually below `2 ^ n`. -/
private theorem Candidate.eventually_clock_lt (candidate : Candidate) :
    ∀ᶠ n in Filter.atTop, candidate.clock n < 2 ^ n :=
  PolynomiallyBounded.eventually_lt_two_pow (f := candidate.clock)
    (by unfold Candidate.clock; fun_prop)

/-- Whether the first word consists of `true` symbols only, beside a Boolean, in polynomial
time. -/
private theorem computableInPolyTime_all_and :
    ComputableInPolyTime
      (fun pair : (List Bool × List Bool) × Bool => pair.1.1.all id && pair.2)
      (encPair (encPair encBits encBits) encBool) encBool :=
  ComputableInPolyTime.bool_and.comp
    ((ComputableInPolyTime.bitsAllWithInput (test := fun _ => id)
      ((ComputableInPolyTime.fst _ _).comp (.fst _ _)) (.snd _ _)).prod (.snd _ _))

end BakerGillSolovay

open Classical in
/-- **The unary length language is in `NP` relative to its oracle**: a certificate for `1ⁿ` is a
word of length `n` in the oracle, checked with one request. -/
theorem unaryLengthLanguage_mem_NPWithOracle (B : Set (List Bool)) :
    unaryLengthLanguage B ∈ NPWithOracle B encBits := by
  refine ⟨Polynomial.X, fun xu : List Bool × List Bool => xu.1.all id && decide (xu.2 ∈ B),
    ((computableInPolyTimeWithOracle_mem B).preprocess
      (.snd encBits encBits)).map_with
      (g := fun (xu : List Bool × List Bool) b => xu.1.all id && b)
      BakerGillSolovay.computableInPolyTime_all_and, fun x => ?_⟩
  · simp only [unaryLengthLanguage, Set.mem_ofPred_eq, Polynomial.eval_X, encBits,
      Function.Embedding.refl_apply, Bool.and_eq_true, List.all_eq_true, id, decide_eq_true_eq]
    exact ⟨fun ⟨hall, w, hw, hlen⟩ => ⟨w, hlen, hall, hw⟩,
      fun ⟨w, hlen, hall, hw⟩ => ⟨hall, w, hw, hlen⟩⟩

open Classical BakerGillSolovay in
/-- For any fixed encoded target `L`, some oracle `B` defeats every polynomial-time many-one
reduction of its unary length language to `L`, even with access to `B`. The source language lies
in `NPWithOracle B encBits`. Taking 3SAT as the target gives Exercise 3 §6 of [AroraBarak07]. -/
theorem exists_unaryLengthLanguage_not_reducibleWithOracle {α : Type}
    (enc : α ↪ List Bool) (L : Set α) :
    ∃ B : Set (List Bool), unaryLengthLanguage B ∈ NPWithOracle B encBits ∧
      ¬ManyOneReducibleBy (ComputableInPolyTimeWithOracle B · encBits enc)
        (unaryLengthLanguage B) L := by
  let test (w : List Bool) := decide (w ∈ enc '' L)
  obtain ⟨B, hB⟩ := exists_oracle_diagonal (fun c n => test <$> Candidate.output c n)
    Candidate.clock Candidate.eventually_clock_lt
    (fun c n A => by
      simpa only [OracleComp.queriesWith_map] using c.length_queriesWith_output_le n A)
  refine ⟨B, unaryLengthLanguage_mem_NPWithOracle B,
    fun ⟨f, ⟨program, hcertificate, hprogram⟩, hf⟩ => ?_⟩
  obtain ⟨k, m, machine, c, d, hrun⟩ := hcertificate.exists_fin_run_pure_false
  obtain ⟨n, hn⟩ := hB ⟨k, m, machine, c, d⟩
  apply hn
  have houtput := hrun (List.replicate n true) (languageOracle B)
  simp only [hprogram, encBits, Function.Embedding.refl_apply, List.length_replicate] at houtput
  simp only [Candidate.output, Candidate.clock, OracleComp.interpret_map, houtput]
  change decide (enc (f (List.replicate n true)) ∈ enc '' L) = true ↔ _
  rw [decide_eq_true_eq, enc.injective.mem_set_image, ← hf, replicate_mem_unaryLengthLanguage]

/-- **Baker–Gill–Solovay, the lower bound** [Arora and Barak, Theorem 3.7][AroraBarak09]: for some
oracle language `B`, the unary length language of `B` is not decidable in polynomial time relative
to `B`. A decider would be a reduction to the singleton language containing `true`. -/
theorem exists_unaryLengthLanguage_notMem_PWithOracle :
    ∃ B : Set (List Bool), unaryLengthLanguage B ∉ PWithOracle B encBits := by
  obtain ⟨B, hB⟩ := exists_unaryLengthLanguage_not_reducibleWithOracle encBool {true}
  exact ⟨B, fun ⟨f, hf, hcorrect⟩ => hB.2 ⟨f, hf, fun x => by simpa using hcorrect x⟩⟩

/-- **Baker–Gill–Solovay** [BakerGillSolovay1975], [Arora and Barak, Theorem 3.7][AroraBarak09]:
relative to some oracle language, `P` is strictly contained in `NP`. -/
theorem exists_PWithOracle_ssubset_NPWithOracle :
    ∃ B : Set (List Bool), PWithOracle B encBits ⊂ NPWithOracle B encBits := by
  obtain ⟨B, hB⟩ := exists_unaryLengthLanguage_notMem_PWithOracle
  exact ⟨B, Set.ssubset_iff_subset_ne.mpr ⟨PWithOracle_subset_NPWithOracle B encBits,
    fun h => hB (h ▸ unaryLengthLanguage_mem_NPWithOracle B)⟩⟩

/-- **Baker–Gill–Solovay**: relative to some oracle language, `P ≠ NP`. -/
theorem exists_PWithOracle_ne_NPWithOracle :
    ∃ B : Set (List Bool), PWithOracle B encBits ≠ NPWithOracle B encBits :=
  let ⟨B, hB⟩ := exists_PWithOracle_ssubset_NPWithOracle
  ⟨B, hB.ne⟩

end Cslib.Complexity
