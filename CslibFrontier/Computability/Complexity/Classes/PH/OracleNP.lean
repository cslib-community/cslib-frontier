/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle.BoundedQuery
public import CslibFrontier.Computability.Complexity.Classes.PH.Oracle
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Oracle
import CslibFrontier.Computability.Complexity.Classes.Oracle.Lowness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# `P^NP ⊆ Σ₂ ∩ Π₂`

A polynomial-time computation with an oracle `A ∈ NP` is simulated in `Σ₂` by guessing its
transcript of oracle replies (`Turing.MultiTapePTM.oracleReplies`). A guessed transcript is the
canonical one exactly when every `true` reply answers a query in `A`, an `NP` condition
(`Cslib.Complexity.oracleTranscriptYes_mem_NP`), and every `false` reply answers a query outside
`A`, a `coNP` condition (`Cslib.Complexity.oracleTranscriptNo_mem_coNP`)
(`Cslib.Complexity.mem_oracleTranscriptYes_inter_oracleTranscriptNo`). The pairs of an instance
and an accepted canonical transcript therefore form a problem in `Σ₂`, and so does its projection
(`Cslib.Complexity.mem_SigmaP_of_exists`). Since `P^A` is closed under complement, it also lies in
`Π₂`. This is the inclusion `Δ₂ᵖ ⊆ Σ₂ᵖ ∩ Π₂ᵖ` of the polynomial hierarchy
[Stockmeyer][Stockmeyer1976].

In particular `P^{NP[O(log n)]} ⊆ Σ₂ ∩ Π₂ ⊆ PH`
(`Cslib.Complexity.PNPLog_subset_SigmaP_two_inter_PiP_two`), the inclusion `Θ₂ᵖ ⊆ Σ₂ᵖ` used by
[Hemaspaandra and Ogihara, Theorem 1.14][HemaspaandraOgihara2002] in the proof of Kadin's theorem.

## Main definitions

* `Cslib.Complexity.oracleTranscriptYes`, `Cslib.Complexity.oracleTranscriptNo`: the transcripts
  whose `true`, respectively `false`, query replies are correct for the oracle.

## Main results

* `Cslib.Complexity.ComputableInPolyTimeWithOracle.encoded_mem_SigmaP_two`: a polynomial-time
  predicate of an `FP^NP` output defines a problem in `Σ₂`.
* `Cslib.Complexity.PWithOracle_subset_SigmaP_two_inter_PiP_two`: `P^A ⊆ Σ₂ ∩ Π₂` for `A ∈ NP`.
* `Cslib.Complexity.PNPLog_subset_SigmaP_two_inter_PiP_two`, `Cslib.Complexity.PNPLog_subset_PH`:
  `P^{NP[O(log n)]} ⊆ Σ₂ ∩ Π₂ ⊆ PH`.

## References

* [L. J. Stockmeyer, *The polynomial-time hierarchy*][Stockmeyer1976]
* [L. A. Hemaspaandra, M. Ogihara, *The Complexity Theory Companion*][HemaspaandraOgihara2002]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

open _root_.Turing

/-- The positive replies of an NP-oracle transcript form an NP language. -/
theorem oracleTranscriptYes_mem_NP {t : ℕ} {Control Operation : Type}
    [DecidableEq Operation] [Finite Control] [Finite Operation]
    {machine : MultiTapePTM t Bool Control Operation} {A : Set (List Bool)}
    (hA : A ∈ NP encBits) : oracleTranscriptYes machine enc A ∈ NP (encPair enc encBits) := by
  rw [← SigmaP_one] at hA ⊢
  exact oracleTranscriptYes_mem_SigmaP hA

/-- The negative replies of an NP-oracle transcript form a coNP language. -/
theorem oracleTranscriptNo_mem_coNP {t : ℕ} {Control Operation : Type}
    [DecidableEq Operation] [Finite Control] [Finite Operation]
    {machine : MultiTapePTM t Bool Control Operation} {A : Set (List Bool)}
    (hA : A ∈ NP encBits) : oracleTranscriptNo machine enc A ∈ coNP (encPair enc encBits) := by
  rw [← SigmaP_one] at hA
  rw [← PiP_one_eq_coNP]
  exact oracleTranscriptNo_mem_PiP hA

/-! ### `P^NP ⊆ Σ₂ ∩ Π₂` -/

section PNP

open _root_.Turing _root_.Turing.MultiTapePTM

variable {β : Type} {output : β ↪ List Bool} {A : Set (List Bool)}

open Classical in
/-- **Polynomial-time predicates of `FP^NP` outputs lie in `Σ₂`.** If `A ∈ NP`, `f` is computable
in polynomial time relative to `A`, and `P` is a polynomial-time predicate of an instance and an
encoded output, then `{a | P (a, output (f a)) = true} ∈ Σ₂`. Guess the transcript of oracle
replies: its `true` bits are certified existentially and its `false` bits universally. -/
theorem ComputableInPolyTimeWithOracle.encoded_mem_SigmaP_two {f : α → β}
    {P : α × List Bool → Bool} (hA : A ∈ NP encBits)
    (hf : ComputableInPolyTimeWithOracle A f enc output)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBool) :
    {a | P (a, output (f a)) = true} ∈ SigmaP 2 enc :=
  hf.encoded_mem_SigmaP_succ (k := 1) (SigmaP_one ▸ hA) hP

/-- **`P^A ⊆ Σ₂` for `A ∈ NP`.** -/
theorem PWithOracle_subset_SigmaP_two (hA : A ∈ NP encBits) :
    PWithOracle A enc ⊆ SigmaP 2 enc :=
  PWithOracle_subset_SigmaP_succ (k := 1) (SigmaP_one ▸ hA)

/-- **`P^A ⊆ Π₂` for `A ∈ NP`**: `P^A` is closed under complement. -/
theorem PWithOracle_subset_PiP_two (hA : A ∈ NP encBits) :
    PWithOracle A enc ⊆ PiP 2 enc := fun L hL => by
  simpa only [compl_compl] using
    compl_mem_PiP_of_mem_SigmaP (PWithOracle_subset_SigmaP_two hA (compl_mem_PWithOracle hL))

/-- **`P^NP ⊆ Σ₂ ∩ Π₂`** [Stockmeyer][Stockmeyer1976]. -/
theorem PWithOracle_subset_SigmaP_two_inter_PiP_two (hA : A ∈ NP encBits) :
    PWithOracle A enc ⊆ SigmaP 2 enc ∩ PiP 2 enc :=
  Set.subset_inter (PWithOracle_subset_SigmaP_two hA) (PWithOracle_subset_PiP_two hA)

/-- **`P^{NP[O(log n)]} ⊆ Σ₂ ∩ Π₂`.** -/
theorem PNPLog_subset_SigmaP_two_inter_PiP_two (enc : α ↪ List Bool) :
    PNPLog enc ⊆ SigmaP 2 enc ∩ PiP 2 enc := fun L hL => by
  obtain ⟨A, hA, hLA⟩ := Set.mem_iUnion₂.mp (PNPLog_subset_PWithOracle enc hL)
  exact PWithOracle_subset_SigmaP_two_inter_PiP_two hA hLA

/-- **`P^{NP[O(log n)]} ⊆ PH`.** -/
theorem PNPLog_subset_PH (enc : α ↪ List Bool) : PNPLog enc ⊆ PH enc := fun _ hL =>
  SigmaP_subset_PH 2 (PNPLog_subset_SigmaP_two_inter_PiP_two enc hL).1

end PNP

end Cslib.Complexity
