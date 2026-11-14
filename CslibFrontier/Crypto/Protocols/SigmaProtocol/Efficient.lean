/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Composition
public import CslibFrontier.Computability.Interactive.Security
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.DPi
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Languages.Probabilistic.Vector
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Extension
import CslibFrontier.Computability.Probabilistic.Traverse
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.StatisticalDistance.Product

/-!
# Efficient special soundness and special HVZK

`SigmaProtocol.SpecialSoundness` and `SigmaProtocol.SpecialHVZK` name their extractor and
simulator but accept arbitrary functions and distributions. Boneh and Shoup require an efficient
deterministic extractor (Definition 19.4) and an efficient probabilistic simulator
(Definition 19.5). Without that requirement the notions say little: a Sigma protocol has some
extractor exactly when two accepting conversations with a common commitment and distinct
challenges certify that the statement has a witness, and for a relation in which every statement
has exactly one witness, even the protocol that reveals its witness is special HVZK (test module
`CslibFrontierTests.UnboundedSimulators`). This module adds the efficient variants; the test module
`CslibFrontierTests.EfficientSimulators` shows that, under the discrete-logarithm assumption, they
rule out both examples.

Efficiency is uniform over a family `P i` of Sigma protocols indexed by `i : I`, typically a
unary security parameter together with a system parameter such as a group description
([BonehShoup2023], Definition 2.9). The types of statements, commitments, challenges and responses
may depend on the index, so the algorithms are certified on words, through the encodings
collected in a `SigmaProtocol.Encoding`.

* `EfficientSpecialSoundness P R enc encW extract`: at every index `extract i` is a witness
  extractor, and one deterministic polynomial-time function of words computes the whole family
  (`ExtractorRealizedBy`).
* `EfficientSpecialHVZK P R enc simulate δ`: at every index `simulate i` is a perfect simulator,
  and one typed simulator family `sim : Simulator I Y T C Z` is uniform strict PPT
  (`Simulator.IsPPT`) and within statistical distance `δ i` of `simulate i`
  (`SimulatorRealizedBy`). The simulator takes and returns typed values; encodings appear only in
  `Simulator.IsPPT`, which reads the record `SimulatorInput` of the index, the statement and the
  challenge and writes the encoded commitment and response. The error is needed because a strict
  PPT machine has a fixed clock and only fair coins, so it cannot sample `ZMod q` exactly when `q`
  is not a power of two; with `ProbComp.sampleModNat` the error is exponentially small. Boneh and
  Shoup's efficient algorithms (Definition 2.8) may instead exceed their time bound with negligible
  probability, which permits exact rejection sampling.

Both variants contain the exact property at every index with the same extractor or simulator, so
every theorem about `SpecialSoundness` and `SpecialHVZK` applies to them. An efficient simulator is
`δ i`-close to honest transcripts (`SimulatorRealizedBy.closeTo_transcript`) and outputs an
accepting conversation except with probability `δ i` (`SimulatorRealizedBy.one_sub_le_accepts`),
which relaxes Definition 19.5 (i). A simulator certified by `Simulator.IsPPT` is computed on words
by a uniform strict PPT program that agrees with it on every encoded input
(`Simulator.IsPPT.exists_word`), and conversely a word program that agrees with a typed simulator
certifies it (`Simulator.IsPPT.of_word`). Note that `δ` in `EfficientSpecialHVZK` is an
unconstrained parameter of the predicate rather than a bundled `Negligible` condition: at `δ i ≥ 1`
(since event probabilities are at most `1`), `SimulatorRealizedBy` holds trivially for every
simulator, reducing `EfficientSpecialHVZK` to the unbounded `SpecialHVZK` field
(`not_efficientSpecialHVZK_sendWitness` in `CslibFrontierTests.EfficientSimulators` requires
`δ i ≤ 1 / 2`). Computational special HVZK ([BonehShoup2023], Definition 20.6) is defined in
`CslibFrontier.Crypto.Protocols.SigmaProtocol.Computational`
(`SigmaProtocol.ComputationalSpecialHVZK`); when `δ` is bounded along the setup distribution by a
negligible function, `EfficientSpecialHVZK.exists_computationalSpecialHVZK` derives it.

## Main definitions

* `SigmaProtocol.Encoding`: word encodings of an indexed family of Sigma protocols.
* `SigmaProtocol.SimulatorInput`, `SigmaProtocol.encSimulatorInput`: a simulator's input
  `(index, statement, challenge)` and its encoding.
* `SigmaProtocol.encSimulatorWordInput`, `SigmaProtocol.encExtractorWordInput`,
  `SigmaProtocol.encSubChallengeWordInput`: encodings of the inputs to word simulator, word
  extractor, and word challenge-subtraction programs.
* `SigmaProtocol.Simulator`, `SigmaProtocol.Simulator.IsPPT`: typed simulator families and their
  uniform strict PPT admissibility.
* `SigmaProtocol.ExtractorRealizedBy`: a word function computes an extractor family on encodings.
* `SigmaProtocol.SimulatorRealizedBy`: a typed simulator family is `δ`-close to a family of
  distributions.
* `SigmaProtocol.WordSimulatorRealizedBy`: a word program is `δ`-close to the encoded output of a
  family of distributions, the word-level form provided by `SimulatorRealizedBy.exists_word`.
* `SigmaProtocol.EfficientSpecialSoundness`: special soundness with a polynomial-time extractor.
* `SigmaProtocol.EfficientSpecialHVZK`: special HVZK with a strict PPT simulator, up to `δ`.
* `SigmaProtocol.Encoding.andProof`, `SigmaProtocol.Encoding.orProof`,
  `SigmaProtocol.Encoding.parallelRepetition`: composite encodings for `andProof`, `orProof`, and
  `parallelRepetition`.
* `SigmaProtocol.andExtractWord`, `SigmaProtocol.andSimulator`, `SigmaProtocol.orExtractWord`,
  `SigmaProtocol.orSimulator`, `SigmaProtocol.parallelExtractWord`,
  `SigmaProtocol.parallelSimulator`: word extractors and typed simulators for composed protocols.

## Main results

* `SigmaProtocol.Simulator.IsPPT.of_word`, `SigmaProtocol.Simulator.IsPPT.exists_word`: a typed
  simulator is uniform strict PPT exactly when a uniform strict PPT word program computes it on
  encodings.
* `SigmaProtocol.SimulatorRealizedBy.closeTo_transcript`: an efficient simulator is `δ i`-close to
  the honest prover's commitment and response at every challenge.
* `SigmaProtocol.SimulatorRealizedBy.one_sub_le_accepts`: an efficient simulator outputs an
  accepting conversation with probability at least `1 - δ i`.
* `SigmaProtocol.EfficientSpecialSoundness.andProof`,
  `SigmaProtocol.EfficientSpecialHVZK.andProof`: efficiency transfer through `andProof`.
* `SigmaProtocol.EfficientSpecialSoundness.orProof`,
  `SigmaProtocol.EfficientSpecialHVZK.orProof`: efficiency transfer through `orProof`.
* `SigmaProtocol.EfficientSpecialSoundness.parallelRepetition`,
  `SigmaProtocol.EfficientSpecialHVZK.parallelRepetition`: efficiency transfer through `k`-fold
  parallel repetition.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Definitions 2.8, 2.9, 19.4, 19.5 and 20.6.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Turing.MultiTapeTM Interactive
open scoped ENNReal

/-- Word encodings for a family of Sigma protocols indexed by `I`, with statements in `Y i`,
commitments in `T i`, challenges in `C i` and responses in `Z i` at the index `i`. -/
structure Encoding (I : Type) (Y T C Z : I → Type) where
  /-- The index, such as a unary security parameter with a system parameter. -/
  index : I ↪ List Bool
  /-- The statements at each index. -/
  statement : ∀ i, Y i ↪ List Bool
  /-- The commitments at each index. -/
  commitment : ∀ i, T i ↪ List Bool
  /-- The challenges at each index. -/
  challenge : ∀ i, C i ↪ List Bool
  /-- The responses at each index. -/
  response : ∀ i, Z i ↪ List Bool

variable {I : Type} {X Y T C Z W : I → Type}

/-- The word function `f` computes the extractor family `extract` on encodings: from the index,
the encoded statement and the encoded conversations `(t, c, z)` and `(t, c', z')`, it returns the
encoded witness. -/
def ExtractorRealizedBy (enc : Encoding I Y T C Z) (encW : ∀ i, W i ↪ List Bool)
    (extract : ∀ i, Y i → T i → C i → Z i → C i → Z i → W i)
    (f : I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool → List Bool) :
    Prop :=
  ∀ i y t c z c' z', f (i, enc.statement i y, enc.commitment i t, enc.challenge i c,
    enc.response i z, enc.challenge i c', enc.response i z') = encW i (extract i y t c z c' z')

variable (I Y C) in
/-- The input of a special HVZK simulator: an index, a statement and a challenge at that index. -/
structure SimulatorInput where
  /-- The index. -/
  index : I
  /-- The statement. -/
  statement : Y index
  /-- The challenge. -/
  challenge : C index

/-- The encoding of a simulator's input: the index, then the words of the statement and the
challenge under `enc` at that index, each framed except the last (`encSimulatorInput_apply`). -/
enc_structure encSimulatorInput (enc : Encoding I Y T C Z) : SimulatorInput I Y C where
  index : enc.index,
  statement : (enc.statement index) using (enc.statement index).injective,
  challenge : (enc.challenge index) using (enc.challenge index).injective

variable (I Y T C Z) in
/-- A family of special HVZK simulators: at index `i`, a probabilistic program from a statement and
a challenge to a commitment and a response. `Simulator.IsPPT` states its efficiency on encodings. -/
abbrev Simulator : Type :=
  ∀ i, Y i → C i → ProbComp (T i × Z i)

/-- A simulator family is uniform strict PPT: one machine reads `encSimulatorInput enc` and writes
the encoded commitment and response, framing the commitment. -/
def Simulator.IsPPT (enc : Encoding I Y T C Z) (sim : Simulator I Y T C Z) : Prop :=
  IsPPTOn (encSimulatorInput enc) (encPair encBits encBits) fun s =>
    Prod.map (enc.commitment s.index) (enc.response s.index) <$>
      sim s.index s.statement s.challenge

/-- Input `(i, y, c)` of a word program computing a special HVZK simulator: the index `i` encoded by
`encI`, then the encoded statement and the encoded challenge as bit words. The index and the
statement are framed. -/
abbrev encSimulatorWordInput (encI : I ↪ List Bool) : I × List Bool × List Bool ↪ List Bool :=
  encPair encI (encPair encBits encBits)

/-- The word program `program` realizes the simulator family `simulate` on encodings up to
statistical distance `δ`: on the index, the encoded statement and the encoded challenge, its output
is within `δ i` of the encoded commitment and response sampled by `simulate i`. This is the
word-level form of `SimulatorRealizedBy` that `SimulatorRealizedBy.exists_word` provides. -/
def WordSimulatorRealizedBy (enc : Encoding I Y T C Z)
    (simulate : ∀ i, Y i → C i → PMF (T i × Z i))
    (program : I × List Bool × List Bool → ProbComp (List Bool × List Bool)) (δ : I → ℝ≥0∞) :
    Prop :=
  ∀ i y c, CloseTo ((simulate i y c).map (Prod.map (enc.commitment i) (enc.response i)))
    (ProbComp.eval (program (i, enc.statement i y, enc.challenge i c))) (δ i)

/-- A uniform strict PPT word program on the index and the encoded statement and challenge that
computes a typed program on encodings certifies the typed program. Its output type `β` and its
output encoding `out` are arbitrary, so this also certifies simulators with aborts. -/
theorem isPPTOn_encSimulatorInput_of_word {β : Type} {out : β ↪ List Bool}
    (enc : Encoding I Y T C Z) {typed : SimulatorInput I Y C → ProbComp β}
    {program : I × List Bool × List Bool → ProbComp β}
    (hprogram : IsPPTOn (encSimulatorWordInput enc.index) out program)
    (heq : ∀ s : SimulatorInput I Y C, ProbComp.eval (typed s) = ProbComp.eval
      (program (s.index, enc.statement s.index s.statement, enc.challenge s.index s.challenge))) :
    IsPPTOn (encSimulatorInput enc) out typed :=
  (hprogram.preprocess (prepare := fun s : SimulatorInput I Y C =>
      (s.index, enc.statement s.index s.statement, enc.challenge s.index s.challenge))
    (ComputableInPolyTime.of_eq fun _ => rfl)).congr fun s => (heq s).symm

/-- A uniform strict PPT word program that computes a typed simulator on encodings certifies it. -/
theorem Simulator.IsPPT.of_word {enc : Encoding I Y T C Z} {sim : Simulator I Y T C Z}
    {program : I × List Bool × List Bool → ProbComp (List Bool × List Bool)}
    (hprogram : IsPPTOn (encSimulatorWordInput enc.index) (encPair encBits encBits) program)
    (heq : ∀ i y c, (ProbComp.eval (sim i y c)).map (Prod.map (enc.commitment i) (enc.response i)) =
      ProbComp.eval (program (i, enc.statement i y, enc.challenge i c))) :
    Simulator.IsPPT enc sim :=
  isPPTOn_encSimulatorInput_of_word enc hprogram fun s => by
    rw [ProbComp.eval_map]
    exact heq s.index s.statement s.challenge

/-- A uniform strict PPT simulator family is computed on words by a uniform strict PPT program of
the index and arbitrary statement and challenge words, which agrees with it on every encoded
input. -/
theorem Simulator.IsPPT.exists_word {enc : Encoding I Y T C Z} {sim : Simulator I Y T C Z}
    (h : Simulator.IsPPT enc sim) :
    ∃ program : I × List Bool × List Bool → ProbComp (List Bool × List Bool),
      IsPPTOn (encSimulatorWordInput enc.index) (encPair encBits encBits) program ∧
      ∀ i y c, (ProbComp.eval (sim i y c)).map (Prod.map (enc.commitment i) (enc.response i)) =
        ProbComp.eval (program (i, enc.statement i y, enc.challenge i c)) := by
  obtain ⟨extension, hext, hagree⟩ := IsPPTOn.exists_extension h
    (decode := fun w => (unframe w, dropFrame w))
    (ComputableInPolyTime.unframe.prod ComputableInPolyTime.dropFrame)
    fun p => Prod.ext (unframe_encPair encBits encBits p.1 p.2)
      (dropFrame_encPair encBits encBits p.1 p.2)
  refine ⟨fun p => extension (encSimulatorWordInput enc.index p),
    hext.preprocess (ComputableInPolyTime.of_eq fun _ => rfl), fun i y c => ?_⟩
  rw [← ProbComp.eval_map]
  exact (hagree ⟨i, y, c⟩).symm

/-- The typed simulator family `sim` realizes the family of distributions `simulate` up to
statistical distance `δ`: on every statement and challenge at index `i`, its output law is within
`δ i` of `simulate i`. The outputs `O i` are commitment-response pairs for `EfficientSpecialHVZK`
and optional pairs for simulators with aborts. -/
def SimulatorRealizedBy {O : I → Type} (simulate : ∀ i, Y i → C i → PMF (O i))
    (sim : ∀ i, Y i → C i → ProbComp (O i)) (δ : I → ℝ≥0∞) : Prop :=
  ∀ i y c, CloseTo (simulate i y c) (ProbComp.eval (sim i y c)) (δ i)

/-- A uniform strict PPT simulator family within `δ` of `simulate` yields a uniform strict PPT word
program of the index and arbitrary statement and challenge words whose output on every encoded input
is within `δ i` of the encoded `simulate i`. -/
theorem SimulatorRealizedBy.exists_word {enc : Encoding I Y T C Z}
    {simulate : ∀ i, Y i → C i → PMF (T i × Z i)} {sim : Simulator I Y T C Z} {δ : I → ℝ≥0∞}
    (h : SimulatorRealizedBy simulate sim δ) (hppt : Simulator.IsPPT enc sim) :
    ∃ program : I × List Bool × List Bool → ProbComp (List Bool × List Bool),
      IsPPTOn (encSimulatorWordInput enc.index) (encPair encBits encBits) program ∧
      WordSimulatorRealizedBy enc simulate program δ := by
  obtain ⟨program, hprogram, hword⟩ := hppt.exists_word
  refine ⟨program, hprogram, fun i y c => ?_⟩
  rw [← hword]
  exact (h i y c).map _

/-- Input `(i, y, t, c, z, c', z')` of a word function computing a special-soundness extractor:
the index `i` encoded by `encI`, then the encoded statement, commitment, and two challenge-response
pairs as bit words. -/
abbrev encExtractorWordInput (encI : I ↪ List Bool) :
    I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool ↪ List Bool :=
  encPair encI (encPair encBits (encPair encBits (encPair encBits
    (encPair encBits (encPair encBits encBits)))))

/-- Input `(i, c, c₀)` of a word function computing challenge subtraction for `orProof`:
the index `i` encoded by `encI`, then the two encoded challenges as bit words. -/
abbrev encSubChallengeWordInput (encI : I ↪ List Bool) :
    I × List Bool × List Bool ↪ List Bool :=
  encPair encI (encPair encBits encBits)

/-- **Efficient special soundness** ([BonehShoup2023], Definition 19.4). At every index,
`extract i` is a witness extractor for `P i`, and one deterministic polynomial-time function of the
index and words computes the whole family on encodings. As in `SpecialSoundness`, the extracted
witness has a type `W i` and a relation `R i` of its own. -/
structure EfficientSpecialSoundness (P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i))
    (R : ∀ i, W i → Y i → Prop) (enc : Encoding I Y T C Z) (encW : ∀ i, W i ↪ List Bool)
    (extract : ∀ i, Y i → T i → C i → Z i → C i → Z i → W i) : Prop where
  /-- `extract i` is a witness extractor at every index. -/
  specialSoundness : ∀ i, (P i).SpecialSoundness (R i) (extract i)
  /-- One polynomial-time word function computes the extractor family. -/
  polyTime : ∃ f, ComputableInPolyTime f (encExtractorWordInput enc.index) encBits ∧
    ExtractorRealizedBy enc encW extract f

/-- **Efficient special HVZK** ([BonehShoup2023], Definition 19.5), up to a statistical error
`δ`. At every index, `simulate i` is a perfect special HVZK simulator for `P i`, and one uniform
strict PPT simulator family realizes the whole family up to `δ`, for every statement and
challenge. -/
structure EfficientSpecialHVZK (P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i))
    (R : ∀ i, X i → Y i → Prop) (enc : Encoding I Y T C Z)
    (simulate : ∀ i, Y i → C i → PMF (T i × Z i)) (δ : I → ℝ≥0∞) : Prop where
  /-- `simulate i` is a perfect special HVZK simulator at every index. -/
  specialHVZK : ∀ i, (P i).SpecialHVZK (R i) (simulate i)
  /-- One uniform strict PPT simulator family realizes `simulate` up to `δ`. -/
  realized : ∃ sim : Simulator I Y T C Z, Simulator.IsPPT enc sim ∧
    SimulatorRealizedBy simulate sim δ

variable {P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i)} {R : ∀ i, X i → Y i → Prop}
  {simulate : ∀ i, Y i → C i → PMF (T i × Z i)} {sim : Simulator I Y T C Z} {δ : I → ℝ≥0∞}

/-- A simulator realizing a perfect simulator is `δ i`-close to the honest prover's commitment and
response, for every witness-statement pair and every challenge. -/
theorem SimulatorRealizedBy.closeTo_transcript (hS : ∀ i, (P i).SpecialHVZK (R i) (simulate i))
    (h : SimulatorRealizedBy simulate sim δ) {i : I} {x : X i} {y : Y i} (hxy : R i x y)
    (c : C i) :
    CloseTo ((P i).transcript x y c) (ProbComp.eval (sim i y c)) (δ i) := by
  rw [← (hS i).transcript_eq x y hxy c]
  exact h i y c

/-- A simulator realizing a perfect simulator outputs an accepting conversation with probability at
least `1 - δ i`, for every statement and challenge (a relaxation of [BonehShoup2023],
Definition 19.5 (i)). -/
theorem SimulatorRealizedBy.one_sub_le_accepts (hS : ∀ i, (P i).SpecialHVZK (R i) (simulate i))
    (h : SimulatorRealizedBy simulate sim δ) (i : I) (y : Y i) (c : C i) :
    1 - δ i ≤ (ProbComp.eval (sim i y c)).toOuterMeasure {tz | (P i).Accepts y tz.1 c tz.2} := by
  have hone : (simulate i y c).toOuterMeasure {tz | (P i).Accepts y tz.1 c tz.2} = 1 :=
    (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr fun tz htz => (hS i).accepts y c tz htz
  exact tsub_le_iff_right.mpr (hone ▸ h i y c _)

/-! ### Efficiency transfer through `andProof` -/

section And

variable {X₀ Y₀ T₀ Z₀ W₀ X₁ Y₁ T₁ Z₁ W₁ : I → Type}

/-- Combined encodings for `andProof`: statements, commitments, and responses are paired with
`encPair`, while the index and challenge encodings are taken from `enc₀`. -/
def Encoding.andProof (enc₀ : Encoding I Y₀ T₀ C Z₀) (enc₁ : Encoding I Y₁ T₁ C Z₁) :
    Encoding I (fun i => Y₀ i × Y₁ i) (fun i => T₀ i × T₁ i) C (fun i => Z₀ i × Z₁ i) where
  index := enc₀.index
  statement i := encPair (enc₀.statement i) (enc₁.statement i)
  commitment i := encPair (enc₀.commitment i) (enc₁.commitment i)
  challenge := enc₀.challenge
  response i := encPair (enc₀.response i) (enc₁.response i)

/-- Word-level extractor for `andProof`: unframe the paired statement, commitment, and responses,
run `f₀` and `f₁` on their respective halves at the shared challenges, and pair the encoded
witnesses. -/
def andExtractWord
    (f₀ f₁ : I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool → List Bool)
    (input : I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool) :
    List Bool :=
  let (i, y, t, c, z, c', z') := input
  encPair encBits encBits
    (f₀ (i, unframe y, unframe t, c, unframe z, c', unframe z'),
     f₁ (i, dropFrame y, dropFrame t, c, dropFrame z, c', dropFrame z'))

/-- `andExtractWord` is computable in polynomial time when both component word extractors are and
they share the same index encoding. -/
theorem computableInPolyTime_andExtractWord
    {enc₀ : Encoding I Y₀ T₀ C Z₀} {enc₁ : Encoding I Y₁ T₁ C Z₁}
    (hI : enc₀.index = enc₁.index)
    {f₀ f₁ : I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool → List Bool}
    (hf₀ : ComputableInPolyTime f₀ (encExtractorWordInput enc₀.index) encBits)
    (hf₁ : ComputableInPolyTime f₁ (encExtractorWordInput enc₁.index) encBits) :
    ComputableInPolyTime (andExtractWord f₀ f₁)
      (encExtractorWordInput (enc₀.andProof enc₁).index) encBits := by
  have hf₀' := hf₀.tidy
  have hf₁' : ComputableTidilyInPolyTime f₁ (encExtractorWordInput enc₀.index) encBits :=
    hI ▸ hf₁.tidy
  unfold andExtractWord Encoding.andProof encExtractorWordInput
  exact ComputableInPolyTime.of_tidy (by fun_prop)

/-- `andExtractWord` realizes `andExtract` on `enc₀.andProof enc₁` when `f₀` and `f₁` realize
`extract₀` and `extract₁` and share the same challenge encoding. -/
theorem extractorRealizedBy_andExtractWord
    {enc₀ : Encoding I Y₀ T₀ C Z₀} {enc₁ : Encoding I Y₁ T₁ C Z₁}
    (hC : ∀ i, enc₀.challenge i = enc₁.challenge i)
    {encW₀ : ∀ i, W₀ i ↪ List Bool} {encW₁ : ∀ i, W₁ i ↪ List Bool}
    {extract₀ : ∀ i, Y₀ i → T₀ i → C i → Z₀ i → C i → Z₀ i → W₀ i}
    {extract₁ : ∀ i, Y₁ i → T₁ i → C i → Z₁ i → C i → Z₁ i → W₁ i}
    {f₀ f₁ : I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool → List Bool}
    (h₀ : ExtractorRealizedBy enc₀ encW₀ extract₀ f₀)
    (h₁ : ExtractorRealizedBy enc₁ encW₁ extract₁ f₁) :
    ExtractorRealizedBy (enc₀.andProof enc₁) (fun i => encPair (encW₀ i) (encW₁ i))
      (fun i => andExtract (extract₀ i) (extract₁ i)) (andExtractWord f₀ f₁) := by
  intro i ⟨y₀, y₁⟩ ⟨t₀, t₁⟩ c ⟨z₀, z₁⟩ c' ⟨z₀', z₁'⟩
  simp only [andExtractWord, Encoding.andProof, unframe_encPair, dropFrame_encPair]
  rw [h₀, hC i, h₁]
  rfl

/-- **Efficient special soundness of `andProof`.** -/
theorem EfficientSpecialSoundness.andProof
    {P₀ : ∀ i, SigmaProtocol (X₀ i) (Y₀ i) (T₀ i) (C i) (Z₀ i)}
    {P₁ : ∀ i, SigmaProtocol (X₁ i) (Y₁ i) (T₁ i) (C i) (Z₁ i)}
    {R₀ : ∀ i, W₀ i → Y₀ i → Prop} {R₁ : ∀ i, W₁ i → Y₁ i → Prop}
    {enc₀ : Encoding I Y₀ T₀ C Z₀} {enc₁ : Encoding I Y₁ T₁ C Z₁}
    {encW₀ : ∀ i, W₀ i ↪ List Bool} {encW₁ : ∀ i, W₁ i ↪ List Bool}
    {extract₀ : ∀ i, Y₀ i → T₀ i → C i → Z₀ i → C i → Z₀ i → W₀ i}
    {extract₁ : ∀ i, Y₁ i → T₁ i → C i → Z₁ i → C i → Z₁ i → W₁ i}
    (hI : enc₀.index = enc₁.index) (hC : ∀ i, enc₀.challenge i = enc₁.challenge i)
    (h₀ : EfficientSpecialSoundness P₀ R₀ enc₀ encW₀ extract₀)
    (h₁ : EfficientSpecialSoundness P₁ R₁ enc₁ encW₁ extract₁) :
    EfficientSpecialSoundness (fun i => (P₀ i).andProof (P₁ i))
      (fun i x y => R₀ i x.1 y.1 ∧ R₁ i x.2 y.2)
      (enc₀.andProof enc₁) (fun i => encPair (encW₀ i) (encW₁ i))
      (fun i => andExtract (extract₀ i) (extract₁ i)) where
  specialSoundness i := andProof_specialSoundness (h₀.specialSoundness i) (h₁.specialSoundness i)
  polyTime := by
    obtain ⟨f₀, hf₀, hreal₀⟩ := h₀.polyTime
    obtain ⟨f₁, hf₁, hreal₁⟩ := h₁.polyTime
    exact ⟨andExtractWord f₀ f₁, computableInPolyTime_andExtractWord hI hf₀ hf₁,
      extractorRealizedBy_andExtractWord hC hreal₀ hreal₁⟩

/-- Combined typed simulator for `andProof`: run `sim₀` and `sim₁` independently at the shared
challenge `c` and pair their commitments and responses. -/
def andSimulator
    (sim₀ : Simulator I Y₀ T₀ C Z₀) (sim₁ : Simulator I Y₁ T₁ C Z₁) :
    Simulator I (fun i => Y₀ i × Y₁ i) (fun i => T₀ i × T₁ i) C (fun i => Z₀ i × Z₁ i) :=
  fun i y c => do
    let a ← sim₀ i y.1 c
    let b ← sim₁ i y.2 c
    return ((a.1, b.1), (a.2, b.2))

/-- Word-level simulator for `andProof`: unframe the paired statement word, run `prog₀` and `prog₁`
at the shared challenge word, and pair their commitment and response words. -/
private def andSimulateWord
    (prog₀ prog₁ : I × List Bool × List Bool → ProbComp (List Bool × List Bool))
    (input : I × List Bool × List Bool) : ProbComp (List Bool × List Bool) := do
  let (i, y, c) := input
  let a ← prog₀ (i, unframe y, c)
  let b ← prog₁ (i, dropFrame y, c)
  return (encPair encBits encBits (a.1, b.1), encPair encBits encBits (a.2, b.2))

/-- `andSimulator` is uniform strict PPT when both component simulators are and they share the same
index and challenge encodings. -/
theorem isPPT_andSimulator
    {enc₀ : Encoding I Y₀ T₀ C Z₀} {enc₁ : Encoding I Y₁ T₁ C Z₁}
    {sim₀ : Simulator I Y₀ T₀ C Z₀} {sim₁ : Simulator I Y₁ T₁ C Z₁}
    (hI : enc₀.index = enc₁.index) (hC : ∀ i, enc₀.challenge i = enc₁.challenge i)
    (hppt₀ : Simulator.IsPPT enc₀ sim₀) (hppt₁ : Simulator.IsPPT enc₁ sim₁) :
    Simulator.IsPPT (enc₀.andProof enc₁) (andSimulator sim₀ sim₁) := by
  obtain ⟨prog₀, hprog₀, hword₀⟩ := hppt₀.exists_word
  obtain ⟨prog₁, hprog₁, hword₁⟩ := hppt₁.exists_word
  have hprog₁' : IsPPTOn (encSimulatorWordInput enc₀.index) (encPair encBits encBits) prog₁ :=
    hI ▸ hprog₁
  refine Simulator.IsPPT.of_word (program := andSimulateWord prog₀ prog₁) ?_ ?_
  · unfold andSimulateWord
    refine (hprog₀.preprocess (input := encSimulatorWordInput enc₀.index)
      (prepare := fun p : I × List Bool × List Bool => (p.1, unframe p.2.1, p.2.2))
      (by fun_prop)).bind_with ?_
    refine (hprog₁'.preprocess
      (input := encPair (encSimulatorWordInput enc₀.index) (encPair encBits encBits))
      (prepare := fun p : (I × List Bool × List Bool) × List Bool × List Bool =>
        (p.1.1, dropFrame p.1.2.1, p.1.2.2))
      (by fun_prop)).bind_with ?_
    exact (ComputableInPolyTime.tidy (by fun_prop)).isPPTOn
  · intro i ⟨y₀, y₁⟩ c
    simp only [andSimulator, andSimulateWord, Encoding.andProof, unframe_encPair, dropFrame_encPair,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, PMF.pure_map]
    rw [← hword₀ i y₀ c, hC i, ← hword₁ i y₁ c]
    simp only [PMF.bind_map, Function.comp_def, Prod.map_apply, encPair_apply, encBits_apply]
    rfl

/-- `andSimulator` realizes `andSimulate` with statistical error `δ₀ i + δ₁ i`. -/
theorem simulatorRealizedBy_andSimulator
    {simulate₀ : ∀ i, Y₀ i → C i → PMF (T₀ i × Z₀ i)}
    {simulate₁ : ∀ i, Y₁ i → C i → PMF (T₁ i × Z₁ i)}
    {sim₀ : Simulator I Y₀ T₀ C Z₀} {sim₁ : Simulator I Y₁ T₁ C Z₁}
    {δ₀ δ₁ : I → ℝ≥0∞}
    (h₀ : SimulatorRealizedBy simulate₀ sim₀ δ₀)
    (h₁ : SimulatorRealizedBy simulate₁ sim₁ δ₁) :
    SimulatorRealizedBy (fun i => andSimulate (simulate₀ i) (simulate₁ i))
      (andSimulator sim₀ sim₁) (fun i => δ₀ i + δ₁ i) := by
  intro i y c
  simp only [andSimulate, andSimulator, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  exact (h₀ i y.1 c).bind fun a _ => (h₁ i y.2 c).bind_left _

/-- **Efficient special HVZK of `andProof`.** -/
theorem EfficientSpecialHVZK.andProof
    {P₀ : ∀ i, SigmaProtocol (X₀ i) (Y₀ i) (T₀ i) (C i) (Z₀ i)}
    {P₁ : ∀ i, SigmaProtocol (X₁ i) (Y₁ i) (T₁ i) (C i) (Z₁ i)}
    {R₀ : ∀ i, X₀ i → Y₀ i → Prop} {R₁ : ∀ i, X₁ i → Y₁ i → Prop}
    {enc₀ : Encoding I Y₀ T₀ C Z₀} {enc₁ : Encoding I Y₁ T₁ C Z₁}
    {simulate₀ : ∀ i, Y₀ i → C i → PMF (T₀ i × Z₀ i)}
    {simulate₁ : ∀ i, Y₁ i → C i → PMF (T₁ i × Z₁ i)}
    {δ₀ δ₁ : I → ℝ≥0∞}
    (hI : enc₀.index = enc₁.index) (hC : ∀ i, enc₀.challenge i = enc₁.challenge i)
    (h₀ : EfficientSpecialHVZK P₀ R₀ enc₀ simulate₀ δ₀)
    (h₁ : EfficientSpecialHVZK P₁ R₁ enc₁ simulate₁ δ₁) :
    EfficientSpecialHVZK (fun i => (P₀ i).andProof (P₁ i))
      (fun i x y => R₀ i x.1 y.1 ∧ R₁ i x.2 y.2)
      (enc₀.andProof enc₁) (fun i => andSimulate (simulate₀ i) (simulate₁ i))
      (fun i => δ₀ i + δ₁ i) where
  specialHVZK i := andProof_specialHVZK (h₀.specialHVZK i) (h₁.specialHVZK i)
  realized := by
    obtain ⟨sim₀, hppt₀, hreal₀⟩ := h₀.realized
    obtain ⟨sim₁, hppt₁, hreal₁⟩ := h₁.realized
    exact ⟨andSimulator sim₀ sim₁, isPPT_andSimulator hI hC hppt₀ hppt₁,
      simulatorRealizedBy_andSimulator hreal₀ hreal₁⟩

end And

/-! ### Efficiency transfer through `orProof` -/

section Or

variable {X₀ Y₀ T₀ Z₀ W₀ X₁ Y₁ T₁ Z₁ W₁ : I → Type}

/-- Combined encodings for `orProof`: statements and commitments are paired with `encPair`,
responses `(c₀, z₀, z₁)` are encoded by `encPair (enc₀.challenge i) (encPair (enc₀.response i)
(enc₁.response i))`, and the index and challenge encodings are taken from `enc₀`. -/
def Encoding.orProof (enc₀ : Encoding I Y₀ T₀ C Z₀) (enc₁ : Encoding I Y₁ T₁ C Z₁) :
    Encoding I (fun i => Y₀ i × Y₁ i) (fun i => T₀ i × T₁ i) C
      (fun i => C i × Z₀ i × Z₁ i) where
  index := enc₀.index
  statement i := encPair (enc₀.statement i) (enc₁.statement i)
  commitment i := encPair (enc₀.commitment i) (enc₁.commitment i)
  challenge := enc₀.challenge
  response i := encPair (enc₀.challenge i) (encPair (enc₀.response i) (enc₁.response i))

/-- Word-level extractor for `orProof`: compare the first side's challenge words `unframe z` and
`unframe z'`, and run `f₁` with subtracted challenges `subWord (i, c, unframe z)` when they agree,
or `f₀` on the first side when they differ, tagging the output with `true` or `false` (`encSum`).
-/
def orExtractWord
    (subWord : I × List Bool × List Bool → List Bool)
    (f₀ f₁ : I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool → List Bool)
    (input : I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool) :
    List Bool :=
  let (i, y, t, c, z, c', z') := input
  let c₀ := unframe z
  let z₀ := unframe (dropFrame z)
  let z₁ := dropFrame (dropFrame z)
  let c₀' := unframe z'
  let z₀' := unframe (dropFrame z')
  let z₁' := dropFrame (dropFrame z')
  if c₀ == c₀' then
    true :: f₁ (i, dropFrame y, dropFrame t, subWord (i, c, c₀), z₁, subWord (i, c', c₀'), z₁')
  else
    false :: f₀ (i, unframe y, unframe t, c₀, z₀, c₀', z₀')

/-- `orExtractWord` is computable in polynomial time when `subWord`, `f₀`, and `f₁` are and `enc₀`
and `enc₁` share the same index encoding. -/
theorem computableInPolyTime_orExtractWord
    {enc₀ : Encoding I Y₀ T₀ C Z₀} {enc₁ : Encoding I Y₁ T₁ C Z₁}
    (hI : enc₀.index = enc₁.index)
    {subWord : I × List Bool × List Bool → List Bool}
    (hsub : ComputableInPolyTime subWord (encSubChallengeWordInput enc₀.index) encBits)
    {f₀ f₁ : I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool → List Bool}
    (hf₀ : ComputableInPolyTime f₀ (encExtractorWordInput enc₀.index) encBits)
    (hf₁ : ComputableInPolyTime f₁ (encExtractorWordInput enc₁.index) encBits) :
    ComputableInPolyTime (orExtractWord subWord f₀ f₁)
      (encExtractorWordInput (enc₀.orProof enc₁).index) encBits := by
  have hsub' := hsub.tidy
  have hf₀' := hf₀.tidy
  have hf₁' : ComputableTidilyInPolyTime f₁ (encExtractorWordInput enc₀.index) encBits :=
    hI ▸ hf₁.tidy
  let encIn := encExtractorWordInput enc₀.index
  have hcond : ComputableTidilyInPolyTime
      (fun input : I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool =>
        unframe input.2.2.2.2.1 == unframe input.2.2.2.2.2.2)
      encIn encBool := by fun_prop
  have hthen : ComputableTidilyInPolyTime
      (fun input : I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool =>
        true :: f₁ (input.1, dropFrame input.2.1, dropFrame input.2.2.1,
          subWord (input.1, input.2.2.2.1, unframe input.2.2.2.2.1),
          dropFrame (dropFrame input.2.2.2.2.1),
          subWord (input.1, input.2.2.2.2.2.1, unframe input.2.2.2.2.2.2),
          dropFrame (dropFrame input.2.2.2.2.2.2)))
      encIn encBits := by fun_prop
  have helse : ComputableTidilyInPolyTime
      (fun input : I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool =>
        false :: f₀ (input.1, unframe input.2.1, unframe input.2.2.1,
          unframe input.2.2.2.2.1, unframe (dropFrame input.2.2.2.2.1),
          unframe input.2.2.2.2.2.2, unframe (dropFrame input.2.2.2.2.2.2)))
      encIn encBits := by fun_prop
  unfold orExtractWord Encoding.orProof
  exact ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.cond hcond hthen helse)

/-- `orExtractWord` realizes `orExtract` on `enc₀.orProof enc₁` with witness encoding `encSum`. -/
theorem extractorRealizedBy_orExtractWord [∀ i, AddCommGroup (C i)] [∀ i, DecidableEq (C i)]
    {enc₀ : Encoding I Y₀ T₀ C Z₀} {enc₁ : Encoding I Y₁ T₁ C Z₁}
    (hC : ∀ i, enc₀.challenge i = enc₁.challenge i)
    {subWord : I × List Bool × List Bool → List Bool}
    (hsub_eq : ∀ i (c c₀ : C i),
      subWord (i, enc₀.challenge i c, enc₀.challenge i c₀) = enc₀.challenge i (c - c₀))
    {encW₀ : ∀ i, W₀ i ↪ List Bool} {encW₁ : ∀ i, W₁ i ↪ List Bool}
    {extract₀ : ∀ i, Y₀ i → T₀ i → C i → Z₀ i → C i → Z₀ i → W₀ i}
    {extract₁ : ∀ i, Y₁ i → T₁ i → C i → Z₁ i → C i → Z₁ i → W₁ i}
    {f₀ f₁ : I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool → List Bool}
    (h₀ : ExtractorRealizedBy enc₀ encW₀ extract₀ f₀)
    (h₁ : ExtractorRealizedBy enc₁ encW₁ extract₁ f₁) :
    ExtractorRealizedBy (enc₀.orProof enc₁) (fun i => encSum (encW₀ i) (encW₁ i))
      (fun i => orExtract (extract₀ i) (extract₁ i)) (orExtractWord subWord f₀ f₁) := by
  intro i ⟨y₀, y₁⟩ ⟨t₀, t₁⟩ c ⟨c₀, z₀, z₁⟩ c' ⟨c₀', z₀', z₁'⟩
  have hbeq : (enc₀.challenge i c₀ == enc₀.challenge i c₀') = decide (c₀ = c₀') := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, (enc₀.challenge i).injective.eq_iff]
  simp only [orExtractWord, Encoding.orProof, unframe_encPair, dropFrame_encPair, hbeq, hsub_eq,
    orExtract]
  by_cases hc₀ : c₀ = c₀'
  · simp only [hc₀, decide_true, ↓reduceIte, encSum_inr]
    rw [hC i, h₁]
  · simp only [hc₀, decide_false, Bool.false_eq_true, ↓reduceIte, encSum_inl]
    rw [h₀]

/-- **Efficient special soundness of `orProof`.** -/
theorem EfficientSpecialSoundness.orProof
    [∀ i, AddCommGroup (C i)] [∀ i, Fintype (C i)] [∀ i, DecidableEq (C i)]
    {P₀ : ∀ i, SigmaProtocol (X₀ i) (Y₀ i) (T₀ i) (C i) (Z₀ i)}
    {P₁ : ∀ i, SigmaProtocol (X₁ i) (Y₁ i) (T₁ i) (C i) (Z₁ i)}
    {simulate₀ : ∀ i, Y₀ i → C i → PMF (T₀ i × Z₀ i)}
    {simulate₁ : ∀ i, Y₁ i → C i → PMF (T₁ i × Z₁ i)}
    {R₀ : ∀ i, W₀ i → Y₀ i → Prop} {R₁ : ∀ i, W₁ i → Y₁ i → Prop}
    {enc₀ : Encoding I Y₀ T₀ C Z₀} {enc₁ : Encoding I Y₁ T₁ C Z₁}
    {encW₀ : ∀ i, W₀ i ↪ List Bool} {encW₁ : ∀ i, W₁ i ↪ List Bool}
    {extract₀ : ∀ i, Y₀ i → T₀ i → C i → Z₀ i → C i → Z₀ i → W₀ i}
    {extract₁ : ∀ i, Y₁ i → T₁ i → C i → Z₁ i → C i → Z₁ i → W₁ i}
    {subWord : I × List Bool × List Bool → List Bool}
    (hI : enc₀.index = enc₁.index) (hC : ∀ i, enc₀.challenge i = enc₁.challenge i)
    (hsub : ComputableInPolyTime subWord (encSubChallengeWordInput enc₀.index) encBits)
    (hsub_eq : ∀ i (c c₀ : C i),
      subWord (i, enc₀.challenge i c, enc₀.challenge i c₀) = enc₀.challenge i (c - c₀))
    (h₀ : EfficientSpecialSoundness P₀ R₀ enc₀ encW₀ extract₀)
    (h₁ : EfficientSpecialSoundness P₁ R₁ enc₁ encW₁ extract₁) :
    EfficientSpecialSoundness
      (fun i => SigmaProtocol.orProof (P₀ i) (P₁ i) (simulate₀ i) (simulate₁ i))
      (fun i => orRelation (R₀ i) (R₁ i))
      (enc₀.orProof enc₁) (fun i => encSum (encW₀ i) (encW₁ i))
      (fun i => orExtract (extract₀ i) (extract₁ i)) where
  specialSoundness i := orProof_specialSoundness (h₀.specialSoundness i) (h₁.specialSoundness i)
  polyTime := by
    obtain ⟨f₀, hf₀, hreal₀⟩ := h₀.polyTime
    obtain ⟨f₁, hf₁, hreal₁⟩ := h₁.polyTime
    exact ⟨orExtractWord subWord f₀ f₁, computableInPolyTime_orExtractWord hI hsub hf₀ hf₁,
      extractorRealizedBy_orExtractWord hC hsub_eq hreal₀ hreal₁⟩

/-- Combined typed simulator for `orProof`: sample `c₀ ← sampleChallenge i`, run `sim₀ i y.1 c₀`
and `sim₁ i y.2 (c - c₀)`, and return `((a.1, b.1), c₀, a.2, b.2)`. -/
def orSimulator [∀ i, Sub (C i)]
    (sampleChallenge : ∀ i, ProbComp (C i))
    (sim₀ : Simulator I Y₀ T₀ C Z₀) (sim₁ : Simulator I Y₁ T₁ C Z₁) :
    Simulator I (fun i => Y₀ i × Y₁ i) (fun i => T₀ i × T₁ i) C
      (fun i => C i × Z₀ i × Z₁ i) :=
  fun i y c => do
    let c₀ ← sampleChallenge i
    let a ← sim₀ i y.1 c₀
    let b ← sim₁ i y.2 (c - c₀)
    return ((a.1, b.1), c₀, a.2, b.2)

/-- Word-level simulator for `orProof`: sample an encoded challenge word `c₀`, run `prog₀` at `c₀`
and `prog₁` at `subWord (i, c, c₀)`, and frame the resulting commitment and response words. -/
private def orSimulateWord
    (sampleChallengeWord : I → ProbComp (List Bool))
    (subWord : I × List Bool × List Bool → List Bool)
    (prog₀ prog₁ : I × List Bool × List Bool → ProbComp (List Bool × List Bool))
    (input : I × List Bool × List Bool) : ProbComp (List Bool × List Bool) := do
  let (i, y, c) := input
  let c₀ ← sampleChallengeWord i
  let a ← prog₀ (i, unframe y, c₀)
  let b ← prog₁ (i, dropFrame y, subWord (i, c, c₀))
  return (encPair encBits encBits (a.1, b.1),
    encPair encBits (encPair encBits encBits) (c₀, a.2, b.2))

/-- `orSimulator` is uniform strict PPT when the challenge sampler, challenge subtraction, and both
component simulators are. -/
theorem isPPT_orSimulator [∀ i, Sub (C i)]
    {enc₀ : Encoding I Y₀ T₀ C Z₀} {enc₁ : Encoding I Y₁ T₁ C Z₁}
    {sampleChallenge : ∀ i, ProbComp (C i)}
    {subWord : I × List Bool × List Bool → List Bool}
    {sim₀ : Simulator I Y₀ T₀ C Z₀} {sim₁ : Simulator I Y₁ T₁ C Z₁}
    (hI : enc₀.index = enc₁.index) (hC : ∀ i, enc₀.challenge i = enc₁.challenge i)
    (hsample : IsPPTOn enc₀.index encBits (fun i => enc₀.challenge i <$> sampleChallenge i))
    (hsub : ComputableInPolyTime subWord (encSubChallengeWordInput enc₀.index) encBits)
    (hsub_eq : ∀ i (c c₀ : C i),
      subWord (i, enc₀.challenge i c, enc₀.challenge i c₀) = enc₀.challenge i (c - c₀))
    (hppt₀ : Simulator.IsPPT enc₀ sim₀) (hppt₁ : Simulator.IsPPT enc₁ sim₁) :
    Simulator.IsPPT (enc₀.orProof enc₁) (orSimulator sampleChallenge sim₀ sim₁) := by
  obtain ⟨prog₀, hprog₀, hword₀⟩ := hppt₀.exists_word
  obtain ⟨prog₁, hprog₁, hword₁⟩ := hppt₁.exists_word
  have hprog₁' : IsPPTOn (encSimulatorWordInput enc₀.index) (encPair encBits encBits) prog₁ :=
    hI ▸ hprog₁
  have hsub' := hsub.tidy
  refine Simulator.IsPPT.of_word
    (program := orSimulateWord (fun i => enc₀.challenge i <$> sampleChallenge i)
      subWord prog₀ prog₁) ?_ ?_
  · unfold orSimulateWord
    refine (hsample.preprocess (input := encSimulatorWordInput enc₀.index)
      (prepare := fun p : I × List Bool × List Bool => p.1)
      (by fun_prop)).bind_with ?_
    refine (hprog₀.preprocess (input := encPair (encSimulatorWordInput enc₀.index) encBits)
      (prepare := fun p : (I × List Bool × List Bool) × List Bool =>
        (p.1.1, unframe p.1.2.1, p.2))
      (by fun_prop)).bind_with ?_
    refine (hprog₁'.preprocess
      (input := encPair (encPair (encSimulatorWordInput enc₀.index) encBits)
        (encPair encBits encBits))
      (prepare := fun p : ((I × List Bool × List Bool) × List Bool) × List Bool × List Bool =>
        (p.1.1.1, dropFrame p.1.1.2.1, subWord (p.1.1.1, p.1.1.2.2, p.1.2)))
      (ComputableInPolyTime.of_tidy (by fun_prop))).bind_with ?_
    exact (ComputableInPolyTime.tidy (by fun_prop)).isPPTOn
  · intro i ⟨y₀, y₁⟩ c
    simp only [orSimulator, orSimulateWord, Encoding.orProof, unframe_encPair, dropFrame_encPair,
      ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.map_bind, PMF.bind_map,
      PMF.pure_map, Function.comp_def]
    refine PMF.bind_congr_on_support _ _ _ fun c₀ _ => ?_
    rw [hsub_eq, ← hword₀ i y₀ c₀, hC i, ← hword₁ i y₁ (c - c₀)]
    simp only [PMF.bind_map, Function.comp_def, Prod.map_apply, encPair_apply, encBits_apply]
    rfl

/-- `orSimulator` realizes `orSimulate` with statistical error `δC i + (δ₀ i + δ₁ i)`. -/
theorem simulatorRealizedBy_orSimulator [∀ i, AddCommGroup (C i)] [∀ i, Fintype (C i)]
    {sampleChallenge : ∀ i, ProbComp (C i)}
    {simulate₀ : ∀ i, Y₀ i → C i → PMF (T₀ i × Z₀ i)}
    {simulate₁ : ∀ i, Y₁ i → C i → PMF (T₁ i × Z₁ i)}
    {sim₀ : Simulator I Y₀ T₀ C Z₀} {sim₁ : Simulator I Y₁ T₁ C Z₁}
    {δC δ₀ δ₁ : I → ℝ≥0∞}
    (hsample : ∀ i, CloseTo (PMF.uniformOfFintype (C i)) (ProbComp.eval (sampleChallenge i)) (δC i))
    (h₀ : SimulatorRealizedBy simulate₀ sim₀ δ₀)
    (h₁ : SimulatorRealizedBy simulate₁ sim₁ δ₁) :
    SimulatorRealizedBy (fun i => orSimulate (simulate₀ i) (simulate₁ i))
      (orSimulator sampleChallenge sim₀ sim₁) (fun i => δC i + (δ₀ i + δ₁ i)) := by
  intro i y c
  simp only [orSimulate, orSimulator, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  exact (hsample i).bind fun c₀ _ =>
    (h₀ i y.1 c₀).bind fun a _ => (h₁ i y.2 (c - c₀)).bind_left _

/-- **Efficient special HVZK of `orProof`.** -/
theorem EfficientSpecialHVZK.orProof [∀ i, AddCommGroup (C i)] [∀ i, Fintype (C i)]
    {P₀ : ∀ i, SigmaProtocol (X₀ i) (Y₀ i) (T₀ i) (C i) (Z₀ i)}
    {P₁ : ∀ i, SigmaProtocol (X₁ i) (Y₁ i) (T₁ i) (C i) (Z₁ i)}
    {R₀ : ∀ i, X₀ i → Y₀ i → Prop} {R₁ : ∀ i, X₁ i → Y₁ i → Prop}
    {enc₀ : Encoding I Y₀ T₀ C Z₀} {enc₁ : Encoding I Y₁ T₁ C Z₁}
    {sampleChallenge : ∀ i, ProbComp (C i)}
    {subWord : I × List Bool × List Bool → List Bool}
    {simulate₀ : ∀ i, Y₀ i → C i → PMF (T₀ i × Z₀ i)}
    {simulate₁ : ∀ i, Y₁ i → C i → PMF (T₁ i × Z₁ i)}
    {δC δ₀ δ₁ : I → ℝ≥0∞}
    (hI : enc₀.index = enc₁.index) (hC : ∀ i, enc₀.challenge i = enc₁.challenge i)
    (hsample_ppt : IsPPTOn enc₀.index encBits (fun i => enc₀.challenge i <$> sampleChallenge i))
    (hsample_close :
      ∀ i, CloseTo (PMF.uniformOfFintype (C i)) (ProbComp.eval (sampleChallenge i)) (δC i))
    (hsub : ComputableInPolyTime subWord (encSubChallengeWordInput enc₀.index) encBits)
    (hsub_eq : ∀ i (c c₀ : C i),
      subWord (i, enc₀.challenge i c, enc₀.challenge i c₀) = enc₀.challenge i (c - c₀))
    (h₀ : EfficientSpecialHVZK P₀ R₀ enc₀ simulate₀ δ₀)
    (h₁ : EfficientSpecialHVZK P₁ R₁ enc₁ simulate₁ δ₁) :
    EfficientSpecialHVZK
      (fun i => SigmaProtocol.orProof (P₀ i) (P₁ i) (simulate₀ i) (simulate₁ i))
      (fun i => orRelation (R₀ i) (R₁ i))
      (enc₀.orProof enc₁) (fun i => orSimulate (simulate₀ i) (simulate₁ i))
      (fun i => δC i + (δ₀ i + δ₁ i)) where
  specialHVZK i := orProof_specialHVZK (h₀.specialHVZK i) (h₁.specialHVZK i)
  realized := by
    obtain ⟨sim₀, hppt₀, hreal₀⟩ := h₀.realized
    obtain ⟨sim₁, hppt₁, hreal₁⟩ := h₁.realized
    exact ⟨orSimulator sampleChallenge sim₀ sim₁,
      isPPT_orSimulator hI hC hsample_ppt hsub hsub_eq hppt₀ hppt₁,
      simulatorRealizedBy_orSimulator hsample_close hreal₀ hreal₁⟩

end Or

/-! ### Efficiency transfer through `parallelRepetition` -/

section Parallel

/-- Encodings for `k`-fold parallel repetition `(P i).parallelRepetition (k i)`: statements and
indices keep their encodings from `enc`, while commitment, challenge, and response tuples are
encoded by `encFinFn (k i)`. -/
def Encoding.parallelRepetition (enc : Encoding I Y T C Z) (k : I → ℕ) :
    Encoding I Y (fun i => Fin (k i) → T i) (fun i => Fin (k i) → C i)
      (fun i => Fin (k i) → Z i) where
  index := enc.index
  statement := enc.statement
  commitment i := encFinFn (k i) (enc.commitment i)
  challenge i := encFinFn (k i) (enc.challenge i)
  response i := encFinFn (k i) (enc.response i)

/-- Word-level extractor for `parallelRepetition`: split the tuple words into their framed
coordinate words, find the first index where the two challenge words differ, and run `f` on that
coordinate's words (falling back to `defaultWord i` when all coordinate challenge words agree). -/
def parallelExtractWord
    (defaultWord : I → List Bool)
    (f : I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool → List Bool)
    (input : I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool) :
    List Bool :=
  let (i, y, t, c, z, c', z') := input
  let ts := frames t
  let cs := frames c
  let zs := frames z
  let cs' := frames c'
  let zs' := frames z'
  ((List.range cs.length).find? (fun idx => cs.getD idx [] != cs'.getD idx [])).elim
    (defaultWord i)
    (fun idx =>
      f (i, y, ts.getD idx [], cs.getD idx [], zs.getD idx [], cs'.getD idx [], zs'.getD idx []))

/-- `parallelExtractWord` is computable in polynomial time when `defaultWord` and `f` are. -/
theorem computableInPolyTime_parallelExtractWord
    {enc : Encoding I Y T C Z} {k : I → ℕ}
    {defaultWord : I → List Bool}
    (hdef : ComputableInPolyTime defaultWord enc.index encBits)
    {f : I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool → List Bool}
    (hf : ComputableInPolyTime f (encExtractorWordInput enc.index) encBits) :
    ComputableInPolyTime (parallelExtractWord defaultWord f)
      (encExtractorWordInput (enc.parallelRepetition k).index) encBits := by
  let encIn := encExtractorWordInput enc.index
  have hframes := computableInPolyTime_frames.tidy
  have hdef' := hdef.tidy
  have hf' := hf.tidy
  have hfind : ComputableInPolyTime
      (fun input : I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool =>
        (List.range (frames input.2.2.2.1).length).find?
          (fun idx => (frames input.2.2.2.1).getD idx [] !=
            (frames input.2.2.2.2.2.1).getD idx []))
      encIn (encOption encUnary) := by
    have hget1 : ComputableTidilyInPolyTime
        (fun p : (I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool) × ℕ =>
          (frames p.1.2.2.2.1).getD p.2 [])
        (encPair encIn encUnary) encBits := by fun_prop
    have hget2 : ComputableTidilyInPolyTime
        (fun p : (I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool) × ℕ =>
          (frames p.1.2.2.2.2.1).getD p.2 [])
        (encPair encIn encUnary) encBits := by fun_prop
    simp only [bne]
    exact ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.findWithInput (by fun_prop) (by fun_prop))
  have hfallback : ComputableInPolyTime
      (fun input : I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool =>
        defaultWord input.1)
      encIn encBits :=
    ComputableInPolyTime.of_tidy (by fun_prop)
  have hbody : ComputableInPolyTime
      (fun p : (I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool) × ℕ =>
        f (p.1.1, p.1.2.1, (frames p.1.2.2.1).getD p.2 [], (frames p.1.2.2.2.1).getD p.2 [],
          (frames p.1.2.2.2.2.1).getD p.2 [], (frames p.1.2.2.2.2.2.1).getD p.2 [],
          (frames p.1.2.2.2.2.2.2).getD p.2 []))
      (encPair encIn encUnary) encBits :=
    ComputableInPolyTime.of_tidy (by fun_prop)
  unfold parallelExtractWord Encoding.parallelRepetition
  exact hfind.optionElimWithInput hfallback hbody

/-- `parallelExtractWord` realizes `parallelExtract` on `enc.parallelRepetition k`. -/
theorem extractorRealizedBy_parallelExtractWord
    [∀ i, DecidableEq (C i)] [∀ i, Inhabited (W i)]
    {enc : Encoding I Y T C Z} {encW : ∀ i, W i ↪ List Bool}
    {k : I → ℕ} {defaultWord : I → List Bool}
    (hdef_eq : ∀ i, defaultWord i = encW i default)
    {extract : ∀ i, Y i → T i → C i → Z i → C i → Z i → W i}
    {f : I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool → List Bool}
    (hf : ExtractorRealizedBy enc encW extract f) :
    ExtractorRealizedBy (enc.parallelRepetition k) encW
      (fun i => parallelExtract (extract i) (k i)) (parallelExtractWord defaultWord f) := by
  intro i y t c z c' z'
  have hrange : (List.finRange (k i)).map Fin.val = List.range (k i) :=
    List.ext_getElem (by simp) fun _ _ _ => by simp
  simp only [parallelExtractWord, Encoding.parallelRepetition, encFinFn_apply, frames_encList,
    List.length_map, List.length_ofFn, ← hrange, List.find?_map]
  have hpred :
      ((fun idx => ((List.ofFn c).map (enc.challenge i)).getD idx [] !=
        ((List.ofFn c').map (enc.challenge i)).getD idx []) ∘ Fin.val) =
      fun j : Fin (k i) => c j != c' j := by
    funext j
    simp only [Function.comp_apply, List.map_ofFn, List.getD_ofFn]
    rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne, (enc.challenge i).injective.ne_iff]
  rw [hpred]
  unfold parallelExtract
  cases hfind : (List.finRange (k i)).find? (fun j => c j != c' j) with
  | none => exact hdef_eq i
  | some j =>
    simp only [Option.map_some, Option.elim_some, List.map_ofFn, List.getD_ofFn,
      Function.comp_apply]
    exact hf i y (t j) (c j) (z j) (c' j) (z' j)

/-- **Efficient special soundness of `parallelRepetition`.** -/
theorem EfficientSpecialSoundness.parallelRepetition
    [∀ i, DecidableEq (C i)] [∀ i, Inhabited (W i)]
    {P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i)}
    {R : ∀ i, W i → Y i → Prop}
    {enc : Encoding I Y T C Z} {encW : ∀ i, W i ↪ List Bool}
    {extract : ∀ i, Y i → T i → C i → Z i → C i → Z i → W i}
    {k : I → ℕ}
    (hdefault : ComputableInPolyTime (fun i : I => encW i default) enc.index encBits)
    (h : EfficientSpecialSoundness P R enc encW extract) :
    EfficientSpecialSoundness (fun i => (P i).parallelRepetition (k i)) R
      (enc.parallelRepetition k) encW (fun i => parallelExtract (extract i) (k i)) where
  specialSoundness i := parallelRepetition_specialSoundness (h.specialSoundness i)
  polyTime := by
    obtain ⟨f, hf, hreal⟩ := h.polyTime
    exact ⟨parallelExtractWord (fun i => encW i default) f,
      computableInPolyTime_parallelExtractWord hdefault hf,
      extractorRealizedBy_parallelExtractWord (fun _ => rfl) hreal⟩

/-- Typed simulator for `parallelRepetition`: run `sim i y (c j)` independently at each coordinate
`j : Fin (k i)` and unzip the resulting commitments and responses. -/
def parallelSimulator (sim : Simulator I Y T C Z) (k : I → ℕ) :
    Simulator I Y (fun i => Fin (k i) → T i) (fun i => Fin (k i) → C i)
      (fun i => Fin (k i) → Z i) :=
  fun i y c =>
    (fun tz => (fun j => (tz j).1, fun j => (tz j).2)) <$> OracleComp.pi (fun j => sim i y (c j))

/-- Word-level simulator for `parallelRepetition`: split the challenge word into its framed
coordinate challenge words, traverse them with `prog`, and re-encode the resulting commitment and
response word lists. -/
private def parallelSimulateWord
    (prog : I × List Bool × List Bool → ProbComp (List Bool × List Bool))
    (input : I × List Bool × List Bool) : ProbComp (List Bool × List Bool) :=
  let (i, y, c) := input
  (fun pairs => (encList encBits (pairs.map Prod.fst), encList encBits (pairs.map Prod.snd))) <$>
    (frames c).mapM (fun c_j => prog (i, y, c_j))

/-- `parallelSimulator` is uniform strict PPT whenever `sim` is. -/
theorem isPPT_parallelSimulator
    {enc : Encoding I Y T C Z} {sim : Simulator I Y T C Z} (k : I → ℕ)
    (hppt : Simulator.IsPPT enc sim) :
    Simulator.IsPPT (enc.parallelRepetition k) (parallelSimulator sim k) := by
  obtain ⟨prog, hprog, hword⟩ := hppt.exists_word
  refine Simulator.IsPPT.of_word (program := parallelSimulateWord prog) ?_ ?_
  · unfold parallelSimulateWord
    have hstep : IsPPTOn (encPair (encSimulatorWordInput enc.index) encBits)
        (encPair encBits encBits)
        (fun p : (I × List Bool × List Bool) × List Bool => prog (p.1.1, p.1.2.1, p.2)) :=
      hprog.preprocess (input := encPair (encSimulatorWordInput enc.index) encBits) (by fun_prop)
    have hlist : ComputableInPolyTime (fun input : I × List Bool × List Bool => frames input.2.2)
        (encSimulatorWordInput enc.index) (encList encBits) := by fun_prop
    have hpost : ComputableInPolyTime
        (fun pairs : List (List Bool × List Bool) =>
          (encList encBits (pairs.map Prod.fst), encList encBits (pairs.map Prod.snd)))
        (encList (encPair encBits encBits)) (encPair encBits encBits) :=
      ComputableInPolyTime.of_tidy (by fun_prop)
    exact (IsPPTOn.mapMWith
      (program := fun (input : I × List Bool × List Bool) (c_j : List Bool) =>
        prog (input.1, input.2.1, c_j)) hstep hlist).map hpost
  · intro i y c
    simp only [parallelSimulator, parallelSimulateWord, Encoding.parallelRepetition,
      encFinFn_apply, frames_encList, List.ofFn_eq_map, List.map_map, List.mapM_map,
      Function.comp_def, ProbComp.eval_map, ← ProbComp.eval_pi_map_ofFn, ProbComp.eval_pi_eq_piFin]
    have hcoord :
        (PMF.piFin fun j => ProbComp.eval (prog (i, enc.statement i y, enc.challenge i (c j)))) =
          (PMF.piFin fun j => ProbComp.eval (sim i y (c j))).map
            (fun tz j => (enc.commitment i (tz j).1, enc.response i (tz j).2)) := by
      simp only [← hword, PMF.piFin_map]
      rfl
    rw [hcoord]
    simp only [PMF.map_comp]
    refine congrArg (PMF.map · _) ?_
    funext tz
    simp [Function.comp_def, Prod.map_apply, encList_eq_encList_bits_map, List.ofFn_eq_map,
      List.map_map]

/-- `parallelSimulator` realizes `parallelSimulate` with statistical error `(k i : ℝ≥0∞) * δ i`. -/
theorem simulatorRealizedBy_parallelSimulator
    {simulate : ∀ i, Y i → C i → PMF (T i × Z i)} {sim : Simulator I Y T C Z}
    {δ : I → ℝ≥0∞} (k : I → ℕ)
    (hreal : SimulatorRealizedBy simulate sim δ) :
    SimulatorRealizedBy (fun i => parallelSimulate (simulate i) (k i))
      (parallelSimulator sim k) (fun i => (k i : ℝ≥0∞) * δ i) := by
  intro i y c
  simp only [parallelSimulate, parallelSimulator, ProbComp.eval_map, ProbComp.eval_pi_eq_piFin]
  exact (CloseTo.piFin fun j => hreal i y (c j)).map _

/-- **Efficient special HVZK of `parallelRepetition`.** -/
theorem EfficientSpecialHVZK.parallelRepetition
    {P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i)}
    {R : ∀ i, X i → Y i → Prop}
    {enc : Encoding I Y T C Z}
    {simulate : ∀ i, Y i → C i → PMF (T i × Z i)}
    {δ : I → ℝ≥0∞} (k : I → ℕ)
    (h : EfficientSpecialHVZK P R enc simulate δ) :
    EfficientSpecialHVZK (fun i => (P i).parallelRepetition (k i)) R
      (enc.parallelRepetition k) (fun i => parallelSimulate (simulate i) (k i))
      (fun i => (k i : ℝ≥0∞) * δ i) where
  specialHVZK i := parallelRepetition_specialHVZK (h.specialHVZK i)
  realized := by
    obtain ⟨sim, hppt, hreal⟩ := h.realized
    exact ⟨parallelSimulator sim k, isPPT_parallelSimulator k hppt,
      simulatorRealizedBy_parallelSimulator k hreal⟩

end Parallel

end Cslib.Crypto.Protocols.SigmaProtocol
