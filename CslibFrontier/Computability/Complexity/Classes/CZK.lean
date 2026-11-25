/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.IP
public import CslibFrontier.Computability.Complexity.Classes.Promise.Basic
public import CslibFrontier.Crypto.Computational.Nonuniform.Basic

/-!
# Auxiliary-input computational zero knowledge

The honest prover family is fixed before the deviating verifier is chosen. A deviating
verifier accepts the instance and an auxiliary word, interacts with the same prover, and
outputs a word. This includes the verifier that records its random tape and received
messages as its output. For each verifier and polynomial bound on auxiliary input, one
strict polynomial-time simulator takes only the instance and auxiliary word.

The real and simulated outputs must be nonuniformly indistinguishable on yes-instances.
An ensemble chooses one valid instance and auxiliary word at each instance length.
Lengths without a chosen instance use the same dummy output in both experiments.
Quantification over all such choices tests indistinguishability uniformly across the
yes-instances, even if the promise has gaps in its lengths.

This is the auxiliary-input presentation of [Vadhan2006, Definitions 2.12 and 2.18]
using the library's polynomial-advice indistinguishability interface.

## Main definitions

* `Cslib.Complexity.ComputationalZeroKnowledge.verifierOutput`: the adversarial output law.
* `Cslib.Complexity.ComputationalZeroKnowledge.HasSimulation`: the simulation requirement.
* `Cslib.Complexity.PromiseCZK` and `Cslib.Complexity.CZK`: promise and language classes.

## Main results

* `Cslib.Complexity.CZK_subset_IP`: forgetting simulation gives an interactive proof.
-/

public section

namespace Cslib.Complexity

open Cslib.Probability Turing.MultiTapeTM
open scoped ENNReal

namespace ComputationalZeroKnowledge

/-- The output law of a word-producing verifier interacting with the fixed prover. -/
@[expose] noncomputable def verifierOutput (V : WordOracleComp Unit (List Bool))
    (P : Prover Unit) : PMF (List Bool) :=
  (P.run V P.init).map Prod.fst

/-- Index a family of output laws by the instance length, with equal fallback at unused lengths. -/
noncomputable def selectLaw {α : Type} (select : ℕ → Option (α × List Bool))
    (law : α × List Bool → PMF (List Bool)) (n : ℕ) : PMF (List Bool) :=
  (select n).elim (PMF.pure []) law

/-- An adversarial verifier with auxiliary input admits one simulator for each polynomial
auxiliary length. The simulator is uniform over the yes-instances and auxiliary words. -/
@[expose] def HasSimulation {α : Type} (enc : α ↪ List Bool) (yes : Set α)
    (P : α → Prover Unit) : Prop :=
  let input := encPair enc encBits
  ∀ V : α × List Bool → WordOracleComp Unit (List Bool), IsOraclePPTOn input encBits V →
    ∀ p : Polynomial ℕ, ∃ S : α × List Bool → ProbComp (List Bool),
      IsPPTOn input encBits S ∧
      ∀ select : ℕ → Option (α × List Bool),
        (∀ n a z, select n = some (a, z) → a ∈ yes ∧ (enc a).length = n ∧ z.length = p.eval n) →
        Crypto.NonuniformlyIndistinguishable
          (selectLaw select fun x => verifierOutput (V x) (P x.1))
          (selectLaw select fun x => ProbComp.eval (S x))

end ComputationalZeroKnowledge

/-- Computational zero knowledge for promise problems with an information-theoretic soundness
condition against arbitrary provers. -/
@[expose] def PromiseCZK {α : Type} (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {X | ∃ (V : α → WordOracleComp Unit Bool) (P : α → Prover Unit),
    IsOraclePPTOn enc encBool V ∧
    (∀ a ∈ X.yes, 2 / 3 ≤ acceptProb (V a) (P a)) ∧
    (∀ a ∈ X.no, ∀ P', acceptProb (V a) P' ≤ 1 / 3) ∧
    ComputationalZeroKnowledge.HasSimulation enc X.yes P}

/-- Computational zero knowledge for languages. -/
@[expose] def CZK {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | PromiseProblem.ofSet A ∈ PromiseCZK enc}

/-- A computational zero-knowledge proof is an interactive proof. -/
theorem CZK_subset_IP {α : Type} (enc : α ↪ List Bool) : CZK enc ⊆ IP enc := by
  rintro A ⟨V, P, hV, hc, hs, _⟩
  exact ⟨V, hV, ⟨fun a ha => ⟨P a, hc a ha⟩, hs⟩⟩

end Cslib.Complexity
