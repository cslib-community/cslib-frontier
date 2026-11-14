/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.Concrete

/-!
# Componentwise resources for concrete security

Concrete reductions need to retain static descriptions and charge online execution without
identifying unrelated units. `AttackResources` names the common coordinates, while `Fits` and
`IsPolynomial` keep every comparison and asymptotic bound componentwise. Static descriptions are
charged once per retained copy; offline generation is not online time unless the attack executes
it. Output production and copying remain part of `onlineTime`.

This module supplies no scalar total. A client that combines coordinates must state the intended
units and prove its aggregation separately. It also supplies no program, circuit or controller:
callers provide exact retained artifacts and prove that their executions fit the declared budget.

## Main definitions

* `Cslib.Crypto.Game.AttackResources`: static, online, oracle and communication coordinates.
* `Cslib.Crypto.Game.AttackResources.Fits`: componentwise finite-budget comparison.
* `Cslib.Crypto.Game.AttackResources.IsPolynomial`: componentwise polynomial resource families.

## Main results

* `Cslib.Crypto.Game.IndistinguishableWithin.indistinguishable_attackResources`: specialize the
  existing finite-to-asymptotic bridge to componentwise attack resources.

## References

This resource interface and bridge are original infrastructure.
-/

public section

namespace Cslib.Crypto.Game

/-- Independent resources of an explicitly retained and executed attack. Static descriptions are
charged once per retained copy and must not also be included in another static field. Online time
must include parsing, dispatch, marshalling, output production and copying actually performed by
the attack. -/
structure AttackResources where
  /-- Encoded bits of the retained main adversary or reduction program or circuit. -/
  programBits : ℕ
  /-- Encoded bits of the retained uniform generator program. -/
  generatorBits : ℕ
  /-- Encoded bits of the retained universal interpreter. -/
  interpreterBits : ℕ
  /-- Encoded bits of retained wrapper and controller code. -/
  controllerBits : ℕ
  /-- Online execution steps, excluding offline generation that the attack does not execute. -/
  onlineTime : ℕ
  /-- Peak online workspace, rather than the sum of workspace across sequential phases. -/
  onlineWorkspace : ℕ
  /-- Fair random bits consumed online. -/
  randomBits : ℕ
  /-- Classical oracle calls. -/
  classicalQueries : ℕ
  /-- Coherent quantum-oracle calls. -/
  quantumQueries : ℕ
  /-- Maximum simultaneously active qubits, including inputs and ancillas. -/
  qubits : ℕ
  /-- Executed elementary quantum gates. -/
  gates : ℕ
  /-- Maximum encoded request length. -/
  requestBits : ℕ
  /-- Maximum encoded reply length read by the attack. -/
  replyBits : ℕ
  /-- Maximum encoded output length emitted by the attack. -/
  outputBits : ℕ
  deriving DecidableEq

namespace AttackResources

/-- `used` fits `budget` when every named coordinate fits independently. This intentionally does
not turn the coordinates into a scalar total. -/
@[expose] def Fits (used budget : AttackResources) : Prop :=
  used.programBits ≤ budget.programBits ∧
    used.generatorBits ≤ budget.generatorBits ∧
    used.interpreterBits ≤ budget.interpreterBits ∧
    used.controllerBits ≤ budget.controllerBits ∧
    used.onlineTime ≤ budget.onlineTime ∧
    used.onlineWorkspace ≤ budget.onlineWorkspace ∧
    used.randomBits ≤ budget.randomBits ∧
    used.classicalQueries ≤ budget.classicalQueries ∧
    used.quantumQueries ≤ budget.quantumQueries ∧
    used.qubits ≤ budget.qubits ∧
    used.gates ≤ budget.gates ∧
    used.requestBits ≤ budget.requestBits ∧
    used.replyBits ≤ budget.replyBits ∧
    used.outputBits ≤ budget.outputBits

instance (used budget : AttackResources) : Decidable (used.Fits budget) := by
  unfold Fits
  infer_instance

/-- Every exact resource profile fits itself. -/
theorem fits_refl (r : AttackResources) : r.Fits r := by
  simp [Fits]

/-- A resource schedule is polynomial when each coordinate is polynomially bounded independently. -/
structure IsPolynomial (schedule : ℕ → AttackResources) : Prop where
  programBits : PolynomiallyBounded fun n => (schedule n).programBits
  generatorBits : PolynomiallyBounded fun n => (schedule n).generatorBits
  interpreterBits : PolynomiallyBounded fun n => (schedule n).interpreterBits
  controllerBits : PolynomiallyBounded fun n => (schedule n).controllerBits
  onlineTime : PolynomiallyBounded fun n => (schedule n).onlineTime
  onlineWorkspace : PolynomiallyBounded fun n => (schedule n).onlineWorkspace
  randomBits : PolynomiallyBounded fun n => (schedule n).randomBits
  classicalQueries : PolynomiallyBounded fun n => (schedule n).classicalQueries
  quantumQueries : PolynomiallyBounded fun n => (schedule n).quantumQueries
  qubits : PolynomiallyBounded fun n => (schedule n).qubits
  gates : PolynomiallyBounded fun n => (schedule n).gates
  requestBits : PolynomiallyBounded fun n => (schedule n).requestBits
  replyBits : PolynomiallyBounded fun n => (schedule n).replyBits
  outputBits : PolynomiallyBounded fun n => (schedule n).outputBits

end AttackResources

namespace IndistinguishableWithin

/-- Exact finite advantage bounds yield asymptotic indistinguishability when every admissible
adversary supplies an explicit componentwise-polynomial resource schedule and the finite error is
negligible along every such schedule. The schedule premise does not extract any program or circuit
from an existential efficiency hypothesis. -/
theorem indistinguishable_attackResources {Adversary : Type*}
    {game1 game2 : Adversary → ℕ → Game}
    {Within : ℕ → AttackResources → Adversary → Prop}
    {ε : ℕ → AttackResources → ℝ≥0}
    {Admissible : Adversary → Prop}
    (h : IndistinguishableWithin game1 game2 Within ε)
    (hsched : ∀ adversary, Admissible adversary →
      ∃ r : ℕ → AttackResources, r.IsPolynomial ∧ ∀ n, Within n (r n) adversary)
    (hneg : ∀ r : ℕ → AttackResources, r.IsPolynomial →
      Negligible (fun n => ε n (r n))) :
    Indistinguishable game1 game2 Admissible :=
  h.indistinguishable AttackResources.IsPolynomial hsched hneg

end IndistinguishableWithin

end Cslib.Crypto.Game
