/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Quantified
public import CslibFrontier.Computability.Complexity.Classes.Promise.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat

/-!
# The mixed-state quantum polynomial hierarchy

Each level fixes a number of alternating quantifiers over polynomial-width density
operators. The verifier receives the tensor product of the witnesses. On yes-instances,
the existential-first level begins with an existential choice and requires the acceptance
probability to be at least the completeness threshold. On no-instances, the prefix is
dualized and the acceptance probability is at most the soundness threshold.

The thresholds are polynomial-time computable rationals with an inverse-polynomial gap,
following [GharibianSanthaSikoraSundaramYirka2022, arXiv:1805.11139v2, Definitions 2.7–2.9].
The published definitions also permit polynomial-time computable real thresholds.
Rational approximations to accuracy smaller than a constant fraction of the gap
suffice, using a lower completeness threshold and a higher soundness threshold.

## Main definitions

* `Cslib.Complexity.PromiseQPHLevel`: a level with the chosen first quantifier.
* `Cslib.Complexity.PromiseQPH` and `Cslib.Complexity.QPH`: the unions over fixed finite levels.
-/

public section

namespace Cslib.Complexity

open Cslib.Quantum Turing.MultiTapeTM

/-- Alternate a fixed number of quantifiers over a common witness type. A true flag
starts with an existential quantifier. -/
@[expose] def quantifiedProofs (W : Type*) : (k : ℕ) → Bool → ((Fin k → W) → Prop) → Prop
  | 0, _, accepts => accepts Fin.elim0
  | k + 1, true, accepts => ∃ w, quantifiedProofs W k false fun ws => accepts (Fin.cons w ws)
  | k + 1, false, accepts => ∀ w, quantifiedProofs W k true fun ws => accepts (Fin.cons w ws)

/-- Level `k` with the given initial quantifier, separately bounded completeness and
soundness, and one independent mixed state per proof register. -/
@[expose] def PromiseQPHLevel {α : Type} (enc : α ↪ List Bool) (k : ℕ) (existsFirst : Bool) :
    Set (PromiseProblem α) :=
  {X | ∃ (V : UniformQuantifiedVerifier k) (complete sound : ℕ → ℚ) (C d : ℕ),
    ComputableInPolyTime complete encUnary encRat ∧
    ComputableInPolyTime sound encUnary encRat ∧
    0 < C ∧
    (∀ n, 0 ≤ sound n ∧ complete n ≤ 1 ∧ (1 : ℚ) / ↑(C * (n + 1) ^ d) ≤ complete n - sound n) ∧
    (∀ a ∈ X.yes, quantifiedProofs _ k existsFirst fun states =>
      (complete (enc a).length : ℝ) ≤ V.acceptProb (enc a) states) ∧
    (∀ a ∈ X.no, quantifiedProofs _ k (!existsFirst) fun states =>
      V.acceptProb (enc a) states ≤ (sound (enc a).length : ℝ))}

/-- Quantum polynomial hierarchy of promise problems, the union of the existential-first levels. -/
@[expose] def PromiseQPH {α : Type} (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  ⋃ k, PromiseQPHLevel enc k true

/-- Quantum polynomial hierarchy of languages. -/
@[expose] def QPH {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | PromiseProblem.ofSet A ∈ PromiseQPH enc}

end Cslib.Complexity
