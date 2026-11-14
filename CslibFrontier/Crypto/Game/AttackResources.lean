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
identifying unrelated units. An explicit `InstalledArtifact` list records each stored occurrence.
Per-kind description sizes are sums over that inventory, so distinct stored copies contribute
separately, while components inlined into a final artifact are not charged again. `AttackResources`
adds the common execution coordinates; `Fits` and `IsPolynomial` keep every comparison and
asymptotic bound componentwise.

Offline generation is not online time unless the attack executes it. A generated artifact is still
an installed occurrence, whether its compiler ran online or offline. When compilation runs inside
the experiment, its time, workspace and output length are recorded separately, and its work also
contributes to the aggregate online time and peak workspace. Emitted output length stays explicit,
and producing and copying it remain part of `onlineTime`.

This module supplies no scalar total. A client that combines coordinates must state the intended
units and prove its aggregation separately. It also supplies no program, circuit or controller:
callers provide exact retained artifacts and prove that their executions fit the declared budget.

## Main definitions

* `Cslib.Crypto.Game.InstalledArtifact`: one occurrence in the installed static inventory.
* `Cslib.Crypto.Game.AttackExecutionResources`: online, compiler, oracle and communication costs.
* `Cslib.Crypto.Game.AttackResources`: installed inventory plus execution resources.
* `Cslib.Crypto.Game.AttackResources.Fits`: componentwise finite-budget comparison.
* `Cslib.Crypto.Game.AttackResources.AccountsForExecutedCompiler`: an online compiler and its
  emitted installed program are both charged.
* `Cslib.Crypto.Game.AttackResources.IsPolynomial`: componentwise polynomial resource families.

## Main results

* `Cslib.Crypto.Game.IndistinguishableWithin.indistinguishable_attackResources`: specialize the
  existing finite-to-asymptotic bridge to componentwise attack resources.

## References

This resource interface and bridge are original infrastructure.
-/

public section

namespace Cslib.Crypto.Game

/-- The role of one separately installed static artifact occurrence. A final artifact containing
inlined components is one `program` occurrence; those components are not additional occurrences. -/
inductive InstalledArtifactKind
  /-- A retained adversary, reduction program or circuit description. -/
  | program
  /-- A retained uniform generator description. -/
  | generator
  /-- A retained compiler description. -/
  | compiler
  /-- A retained universal interpreter description. -/
  | interpreter
  /-- A separately retained wrapper or controller description. -/
  | controller
  deriving DecidableEq

/-- One occurrence in the installed static inventory. Repeating the same value in the inventory
models distinct stored copies and charges each copy once. -/
structure InstalledArtifact where
  /-- The role under which this occurrence is installed. -/
  kind : InstalledArtifactKind
  /-- Exact encoded length of this occurrence. -/
  bits : ℕ
  deriving DecidableEq

namespace InstalledArtifact

/-- Description bits of the occurrences of `kind` in an explicit installed inventory. -/
@[expose] def installedBits : List InstalledArtifact → InstalledArtifactKind → ℕ
  | [], _ => 0
  | artifact :: inventory, kind =>
      (if artifact.kind = kind then artifact.bits else 0) + installedBits inventory kind

/-- Concatenating inventories adds their per-kind occurrence sums. In particular, separately
stored copies appearing in both inventories are charged separately. -/
theorem installedBits_append (first second : List InstalledArtifact)
    (kind : InstalledArtifactKind) :
    installedBits (first ++ second) kind =
      installedBits first kind + installedBits second kind := by
  induction first with
  | nil => simp [installedBits]
  | cons artifact first ih =>
      simp only [List.cons_append, installedBits, ih, Nat.add_assoc]

end InstalledArtifact

/-- Execution resources of an explicitly realized attack. Compiler coordinates are zero when
compilation is offline. If compilation executes in the experiment, its time is included in
`onlineTime`, its workspace is bounded by `onlineWorkspace`, and its emitted description length is
recorded in `compilerOutputBits`; the generated artifact is also an installed occurrence. -/
structure AttackExecutionResources where
  /-- Online steps, including marshalling, tags, dispatch, queries, interpreter/controller work,
  and output production/copying, but excluding offline generation the attack does not execute. -/
  onlineTime : ℕ
  /-- Peak online workspace, rather than the sum of workspace across sequential phases. -/
  onlineWorkspace : ℕ
  /-- Steps of a compiler executed inside the attack experiment; zero for offline compilation. -/
  compilerTime : ℕ
  /-- Peak workspace of a compiler executed inside the experiment; zero when it is offline. -/
  compilerWorkspace : ℕ
  /-- Encoded compiler output length when compilation executes in the experiment. -/
  compilerOutputBits : ℕ
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

/-- Independent resources of an explicitly retained and executed attack. Static description sizes
are derived from the occurrence inventory rather than supplied as unaudited numeric labels. -/
structure AttackResources where
  /-- Every separately retained static occurrence, charged once. -/
  installedArtifacts : List InstalledArtifact
  /-- Online, compiler, oracle and communication coordinates. -/
  execution : AttackExecutionResources
  deriving DecidableEq

namespace AttackResources

/-- Construct a profile from its explicit installed-occurrence inventory and execution costs. -/
@[expose] def ofInventory (inventory : List InstalledArtifact)
    (execution : AttackExecutionResources) : AttackResources :=
  ⟨inventory, execution⟩

/-- Per-kind installed description bits of a resource profile. -/
@[expose] def artifactBits (resources : AttackResources)
    (kind : InstalledArtifactKind) : ℕ :=
  InstalledArtifact.installedBits resources.installedArtifacts kind

/-- Installed main-program or circuit bits, summed once per retained occurrence. -/
@[expose] def programBits (resources : AttackResources) : ℕ :=
  resources.artifactBits .program

/-- Installed generator bits, summed once per retained occurrence. -/
@[expose] def generatorBits (resources : AttackResources) : ℕ :=
  resources.artifactBits .generator

/-- Installed compiler bits, summed once per retained occurrence. -/
@[expose] def compilerBits (resources : AttackResources) : ℕ :=
  resources.artifactBits .compiler

/-- Installed interpreter bits, summed once per retained occurrence. -/
@[expose] def interpreterBits (resources : AttackResources) : ℕ :=
  resources.artifactBits .interpreter

/-- Installed separately retained wrapper/controller bits, summed once per occurrence. -/
@[expose] def controllerBits (resources : AttackResources) : ℕ :=
  resources.artifactBits .controller

/-- An executed compiler is fully represented when its own installed description and its emitted
program occurrence are in the inventory, and its time and workspace are included in the overall
online coordinates. Use zero compiler execution coordinates instead when compilation is offline;
the offline-generated program occurrence still belongs in the inventory. -/
@[expose] def AccountsForExecutedCompiler (resources : AttackResources) : Prop :=
  (∃ bits, { kind := .compiler, bits := bits } ∈ resources.installedArtifacts) ∧
    { kind := .program, bits := resources.execution.compilerOutputBits } ∈
      resources.installedArtifacts ∧
    resources.execution.compilerTime ≤ resources.execution.onlineTime ∧
    resources.execution.compilerWorkspace ≤ resources.execution.onlineWorkspace

/-- `used` fits `budget` when every named coordinate fits independently. This intentionally does
not turn the coordinates into a scalar total. -/
@[expose] def Fits (used budget : AttackResources) : Prop :=
  used.programBits ≤ budget.programBits ∧
    used.generatorBits ≤ budget.generatorBits ∧
    used.compilerBits ≤ budget.compilerBits ∧
    used.interpreterBits ≤ budget.interpreterBits ∧
    used.controllerBits ≤ budget.controllerBits ∧
    used.execution.onlineTime ≤ budget.execution.onlineTime ∧
    used.execution.onlineWorkspace ≤ budget.execution.onlineWorkspace ∧
    used.execution.compilerTime ≤ budget.execution.compilerTime ∧
    used.execution.compilerWorkspace ≤ budget.execution.compilerWorkspace ∧
    used.execution.compilerOutputBits ≤ budget.execution.compilerOutputBits ∧
    used.execution.randomBits ≤ budget.execution.randomBits ∧
    used.execution.classicalQueries ≤ budget.execution.classicalQueries ∧
    used.execution.quantumQueries ≤ budget.execution.quantumQueries ∧
    used.execution.qubits ≤ budget.execution.qubits ∧
    used.execution.gates ≤ budget.execution.gates ∧
    used.execution.requestBits ≤ budget.execution.requestBits ∧
    used.execution.replyBits ≤ budget.execution.replyBits ∧
    used.execution.outputBits ≤ budget.execution.outputBits

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
  compilerBits : PolynomiallyBounded fun n => (schedule n).compilerBits
  interpreterBits : PolynomiallyBounded fun n => (schedule n).interpreterBits
  controllerBits : PolynomiallyBounded fun n => (schedule n).controllerBits
  onlineTime : PolynomiallyBounded fun n => (schedule n).execution.onlineTime
  onlineWorkspace : PolynomiallyBounded fun n => (schedule n).execution.onlineWorkspace
  compilerTime : PolynomiallyBounded fun n => (schedule n).execution.compilerTime
  compilerWorkspace : PolynomiallyBounded fun n => (schedule n).execution.compilerWorkspace
  compilerOutputBits : PolynomiallyBounded fun n => (schedule n).execution.compilerOutputBits
  randomBits : PolynomiallyBounded fun n => (schedule n).execution.randomBits
  classicalQueries : PolynomiallyBounded fun n => (schedule n).execution.classicalQueries
  quantumQueries : PolynomiallyBounded fun n => (schedule n).execution.quantumQueries
  qubits : PolynomiallyBounded fun n => (schedule n).execution.qubits
  gates : PolynomiallyBounded fun n => (schedule n).execution.gates
  requestBits : PolynomiallyBounded fun n => (schedule n).execution.requestBits
  replyBits : PolynomiallyBounded fun n => (schedule n).execution.replyBits
  outputBits : PolynomiallyBounded fun n => (schedule n).execution.outputBits

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
