/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Crypto.Negligible
public import CslibFrontier.Probability.PMF.Uniform
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
import CslibFrontier.Probability.PMF.Map

/-!
# Noninteractive statistical and perfect zero knowledge

A common random string is sampled uniformly at the length prescribed for the instance. The
unrestricted prover uses the string and its own private randomness to send one proof, and a
deterministic polynomial-time verifier decides whether it accepts. The verifier sees the
common string and the proof as two consecutive blocks of predetermined lengths, as for the
library's Arthur–Merlin verifier. The fixed-length convention permits padding proofs.

The experiment records the common string, proof and decision together. The instance indexes
the experiment, so it can be omitted from the transcript. A strict polynomial-time simulator
receives only the instance and samples this joint distribution. Perfect zero knowledge asks
for equality on yes-instances. Statistical zero knowledge allows an error negligible in the
encoded instance length. Both variants use completeness and soundness errors at most one third,
following [Dixon, Gayen, Pavan and Vinodchandran][DixonGayenPavanVinodchandran2020],
Definitions 2.2–2.3, printed p. 5.

A bounded-error problem has a trivial noninteractive proof: the verifier reads the common string
as the coins of the bounded-error solver and the proof is empty, so a simulator sampling the
common string itself reproduces the transcript exactly
(`Cslib.Complexity.PromiseBPP_subset_PromiseNIPZK`).

## Main definitions

* `Cslib.Complexity.CRSProtocol`: the common-random-string experiment and its proof obligations.
* `Cslib.Complexity.CRSTranscriptSimulator`: a polynomial-time sampler for the transcript.
* `Cslib.Complexity.PromiseNISZK` and `Cslib.Complexity.PromiseNIPZK`: the promise classes.
* `Cslib.Complexity.NISZK` and `Cslib.Complexity.NIPZK`: their language specializations.

## Main results

* `Cslib.Complexity.PromiseNIPZK_subset_PromiseNISZK`, `Cslib.Complexity.NIPZK_subset_NISZK`:
  perfect simulation is statistical simulation.
* `Cslib.Complexity.PromiseBPP_subset_PromiseNIPZK`, `Cslib.Complexity.BPP_subset_NIPZK`:
  `BPP ⊆ NIPZK`, with the common string as the verifier's coins.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Cslib.Probability
open scoped NNReal ENNReal

variable {α : Type}

/-- The transcript observed at a fixed instance of a common-random-string protocol. -/
structure CRSTranscript where
  /-- The publicly sampled common random string. -/
  commonString : List Bool
  /-- The message sent by the prover. -/
  proof : List Bool
  /-- The verifier's acceptance bit. -/
  accepted : Bool

/-- Encode the framed common string, the framed proof, and the final decision bit. -/
enc_structure encCRSTranscript : CRSTranscript where
  commonString : encBits, proof : encBits, accepted : encBool

/-- A noninteractive proof protocol over one uniform common random string.
The prover uses a finite number of private random bits on each instance. Neither that number nor
the prover's computation has a polynomial bound. -/
structure CRSProtocol (enc : α ↪ List Bool) where
  /-- The common random string length as a polynomial in the encoded instance length. -/
  commonLength : Polynomial ℕ
  /-- The proof length as a polynomial in the encoded instance length. -/
  proofLength : Polynomial ℕ
  /-- The decision on an instance and the common string concatenated with the proof. -/
  verify : α × List Bool → Bool
  /-- On the permitted input lengths, this certificate gives polynomial time in the instance. -/
  computableInPolyTime_verify : ComputableInPolyTime verify (encPair enc encBits) encBool
  /-- The honest prover's private coin count, which can depend on the entire instance. -/
  privateCoins : α → ℕ
  /-- Produce one proof given the instance, common randomness and private coins. -/
  respond : (a : α) → (Fin (commonLength.eval (enc a).length) → Bool) →
    (Fin (privateCoins a) → Bool) → Fin (proofLength.eval (enc a).length) → Bool

namespace CRSProtocol

variable {enc : α ↪ List Bool}

/-- Sample the shared coins, then the honest prover's coins, and retain the full transcript. -/
@[expose] noncomputable def transcript (P : CRSProtocol enc) (a : α) : PMF CRSTranscript :=
  (PMF.uniformOfFintype (Fin (P.commonLength.eval (enc a).length) → Bool)).bind fun common =>
    (PMF.uniformOfFintype (Fin (P.privateCoins a) → Bool)).map fun coins =>
      let r := List.ofFn common
      let w := List.ofFn (P.respond a common coins)
      ⟨r, w, P.verify (a, r ++ w)⟩

/-- The honest experiment accepts yes-instances with probability at least two thirds.
On no-instances at most one third of the shared strings admit any accepting proof. This
soundness condition takes the best possible response separately at each shared string. -/
def Solves (P : CRSProtocol enc) (A : PromiseProblem α) : Prop :=
  (∀ a ∈ A.yes, 2 / 3 ≤ ((P.transcript a).map CRSTranscript.accepted) true) ∧
    ∀ a ∈ A.no,
      BoundedErrorAt enc P.commonLength (arthurMerlinSlice enc P.proofLength P.verify) a false

end CRSProtocol

/-- A strict randomized polynomial-time algorithm for emitting a transcript from an instance. -/
structure CRSTranscriptSimulator (enc : α ↪ List Bool) where
  /-- The number of uniformly sampled private bits. -/
  coinLength : Polynomial ℕ
  /-- The transcript evaluated on the instance and its private bits. -/
  sample : α × List Bool → CRSTranscript
  /-- The sampler is a native polynomial-time function of the instance and the private bits. -/
  computableInPolyTime_sample :
    ComputableInPolyTime sample (encPair enc encBits) encCRSTranscript

/-- The simulator's output law, with only the instance as input. -/
noncomputable def CRSTranscriptSimulator.run {enc : α ↪ List Bool}
    (S : CRSTranscriptSimulator enc) (a : α) : PMF CRSTranscript :=
  (PMF.uniformOfFintype (Fin (S.coinLength.eval (enc a).length) → Bool)).map
    fun r => S.sample (a, List.ofFn r)

/-- Noninteractive perfect zero knowledge for promise problems. -/
def PromiseNIPZK (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {A | ∃ (P : CRSProtocol enc) (S : CRSTranscriptSimulator enc),
    P.Solves A ∧ ∀ a ∈ A.yes, S.run a = P.transcript a}

/-- Noninteractive statistical zero knowledge for promise problems. One negligible error bound
holds uniformly across all yes-instances of each encoded length. -/
def PromiseNISZK (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {A | ∃ (P : CRSProtocol enc) (S : CRSTranscriptSimulator enc) (error : ℕ → ℝ≥0),
    P.Solves A ∧ Cslib.Crypto.Negligible error ∧ ∀ a ∈ A.yes,
      CloseTo (S.run a) (P.transcript a) (error (enc a).length)}

/-- Languages with noninteractive perfect zero-knowledge proofs. -/
def NIPZK (enc : α ↪ List Bool) : Set (Set α) :=
  {A | PromiseProblem.ofSet A ∈ PromiseNIPZK enc}

/-- Languages with noninteractive statistical zero-knowledge proofs. -/
def NISZK (enc : α ↪ List Bool) : Set (Set α) :=
  {A | PromiseProblem.ofSet A ∈ PromiseNISZK enc}

/-- Perfect simulation gives statistical simulation with zero error. -/
theorem PromiseNIPZK_subset_PromiseNISZK (enc : α ↪ List Bool) :
    PromiseNIPZK enc ⊆ PromiseNISZK enc := by
  rintro A ⟨P, S, hP, hS⟩
  exact ⟨P, S, fun _ => 0, hP, Cslib.Crypto.negligible_zero, fun a ha => by
    simpa only [hS a ha, ENNReal.coe_zero] using CloseTo.refl (P.transcript a)⟩

/-- Every noninteractive perfect zero-knowledge language is statistically zero knowledge. -/
theorem NIPZK_subset_NISZK (enc : α ↪ List Bool) : NIPZK enc ⊆ NISZK enc :=
  fun _ hA => PromiseNIPZK_subset_PromiseNISZK enc hA

/-- **`PromiseBPP ⊆ PromiseNIPZK`**: the verifier decides alone, reading the common random string
as the coins of a bounded-error solver, and the proof is empty. The simulator samples the
common string itself and outputs the honest transcript, so the simulation is perfect. This is the
standard observation that bounded-error problems have trivial noninteractive proofs, under the
definitions of [Dixon, Gayen, Pavan and Vinodchandran][DixonGayenPavanVinodchandran2020],
Definitions 2.2–2.3. -/
theorem PromiseBPP_subset_PromiseNIPZK (enc : α ↪ List Bool) :
    PromiseBPP enc ⊆ PromiseNIPZK enc := by
  rintro Q ⟨p, V, hV, hQ⟩
  let proof : CRSProtocol enc :=
    { commonLength := p, proofLength := 0, verify := V, computableInPolyTime_verify := hV
      privateCoins := fun _ => 0, respond := fun _ _ _ _ => false }
  let sim : CRSTranscriptSimulator enc :=
    { coinLength := p, sample := fun x => ⟨x.2, [], V x⟩
      computableInPolyTime_sample := by fun_prop }
  have hreal (a : α) : proof.transcript a = sim.run a := by
    simp only [CRSProtocol.transcript, CRSTranscriptSimulator.run, proof, sim,
      Polynomial.eval_zero, List.ofFn_zero, List.append_nil]
    exact (congrArg _ (funext fun _ => PMF.map_const _ _)).trans (PMF.bind_pure_comp _ _)
  refine ⟨proof, sim, ⟨fun a ha => ?_, fun a ha => ?_⟩, fun a _ => (hreal a).symm⟩
  · rw [hreal, CRSTranscriptSimulator.run, PMF.map_comp, Probability.PMF.uniformOfFintype_map_apply,
      Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, ENNReal.le_div_iff_mul_le (by simp) (by simp), mul_comm, ← mul_div_assoc,
      ENNReal.div_le_iff (by norm_num) (by norm_num), mul_comm _ (2 : ℝ≥0∞), mul_comm _ (3 : ℝ≥0∞)]
    exact_mod_cast (hQ a).1 ha
  · exact ((hQ a).2 ha).congr fun r => by simp [arthurMerlinSlice, proof]

/-- **`BPP ⊆ NIPZK`**: a bounded-error decider, run on the common random string, is a
noninteractive proof with an empty proof and a perfect simulator. -/
theorem BPP_subset_NIPZK (enc : α ↪ List Bool) : BPP enc ⊆ NIPZK enc :=
  fun _ hA => PromiseBPP_subset_PromiseNIPZK enc hA

end Cslib.Complexity
