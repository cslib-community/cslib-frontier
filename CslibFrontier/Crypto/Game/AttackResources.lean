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
the experiment, its input, time, workspace, output and output-copy time are recorded separately,
connected to a model-specific execution certificate, and included in the online time and peak
workspace. Initial attack input, emitted output and output-copy time stay separate too.

This module supplies no scalar total. A client that combines coordinates must state the intended
units and prove its aggregation separately. It also supplies no program, circuit or controller:
callers provide exact retained artifacts and prove that their executions fit the declared budget.

## Main definitions

* `Cslib.Crypto.Game.InstalledArtifact`: one occurrence in the installed static inventory.
* `Cslib.Crypto.Game.ExecutedCompilerResources`: executed compiler input, output and costs.
* `Cslib.Crypto.Game.AttackExecutionResources`: online, compiler, oracle and communication costs.
* `Cslib.Crypto.Game.AttackResources`: installed inventory plus execution resources.
* `Cslib.Crypto.Game.CompilerInstallation`: separate or inlined representation of compiler logic.
* `Cslib.Crypto.Game.AttackResources.Fits`: componentwise finite-budget comparison.
* `Cslib.Crypto.Game.AttackResources.AccountsForExecutedCompiler`: an online compiler and its
  emitted installed program are certified and charged without duplicating inlined code.
* `Cslib.Crypto.Game.AttackResources.AccountsForOutput`: initial input, emitted output and copying
  are connected to a model-specific execution certificate.
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
  /-- A retained program or circuit emitted by a compiler. -/
  | generatedProgram
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

/-- Componentwise resources of a compiler executed inside the attack experiment. `time` includes
reading the compiler input and producing the emitted description; `outputCopyTime` separately
charges retaining or copying that description after it is produced. All coordinates are zero when
compilation is offline. -/
structure ExecutedCompilerResources where
  /-- Encoded compiler-input length, independent of the attack's initial input. -/
  inputBits : ℕ
  /-- Compiler execution steps, including emitted-description production. -/
  time : ℕ
  /-- Peak compiler workspace. -/
  workspace : ℕ
  /-- Encoded length emitted by the compiler. -/
  outputBits : ℕ
  /-- Online steps charged for retaining or copying the emitted description. -/
  outputCopyTime : ℕ
  deriving DecidableEq

/-- Execution resources of an explicitly realized attack. Compiler coordinates are zero when
compilation is offline. Model-specific execution certificates separately justify that the declared
input/output lengths and step/workspace bounds describe the actual programs. -/
structure AttackExecutionResources where
  /-- Encoded length of the attack's initial input, distinct from oracle requests. -/
  inputBits : ℕ
  /-- Online steps, including marshalling, tags, dispatch, queries, interpreter/controller work,
  compiler work, and output production/copying, but excluding offline generation. -/
  onlineTime : ℕ
  /-- Peak online workspace, rather than the sum of workspace across sequential phases. -/
  onlineWorkspace : ℕ
  /-- Executed compiler coordinates; all zero when compilation is offline. -/
  compiler : ExecutedCompilerResources
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
  /-- Online steps charged specifically for retaining or copying the attack's emitted output. -/
  outputCopyTime : ℕ
  deriving DecidableEq

/-- Independent resources of an explicitly retained and executed attack. Static description sizes
are derived from the occurrence inventory rather than supplied as unaudited numeric labels. -/
structure AttackResources where
  /-- Every separately retained static occurrence, charged once. -/
  installedArtifacts : List InstalledArtifact
  /-- Online, compiler, oracle and communication coordinates. -/
  execution : AttackExecutionResources
  deriving DecidableEq

/-- How compiler logic used online is represented in the installed inventory. A separate compiler
is its own occurrence; an inlined compiler is part of one retained main-program occurrence and is
not also charged under `compiler`. The payload is that occurrence's exact encoded length. -/
inductive CompilerInstallation
  | separatelyInstalled (bits : ℕ)
  | inlinedIntoProgram (bits : ℕ)
  deriving DecidableEq

namespace CompilerInstallation

/-- The installed occurrence selected by a compiler-installation mode. -/
@[expose] def IsInInventory (installation : CompilerInstallation)
    (inventory : List InstalledArtifact) : Prop :=
  match installation with
  | .separatelyInstalled bits => { kind := .compiler, bits := bits } ∈ inventory
  | .inlinedIntoProgram bits => { kind := .program, bits := bits } ∈ inventory

instance (installation : CompilerInstallation) (inventory : List InstalledArtifact) :
    Decidable (installation.IsInInventory inventory) := by
  cases installation <;> unfold IsInInventory <;> infer_instance

end CompilerInstallation

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

/-- Installed compiler-emitted program or circuit bits, summed once per retained occurrence. -/
@[expose] def generatedProgramBits (resources : AttackResources) : ℕ :=
  resources.artifactBits .generatedProgram

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

/-- An executed compiler is fully accounted for relative to a model-specific execution
certificate. `Certifies certificate resources.execution.compiler` is the caller's explicit
obligation connecting the declared compiler input/output, production time, workspace and copy time
to an actual compiler execution. The installation mode charges either a separate compiler or the
single main program containing inlined compiler logic. The emitted description is a distinct
`generatedProgram` occurrence, and compiler execution plus copying fits the overall online costs. -/
@[expose] def AccountsForExecutedCompiler {Certificate : Type*}
    (Certifies : Certificate → ExecutedCompilerResources → Prop)
    (certificate : Certificate) (installation : CompilerInstallation)
    (resources : AttackResources) : Prop :=
  installation.IsInInventory resources.installedArtifacts ∧
    { kind := .generatedProgram, bits := resources.execution.compiler.outputBits } ∈
      resources.installedArtifacts ∧
    Certifies certificate resources.execution.compiler ∧
    resources.execution.compiler.time + resources.execution.compiler.outputCopyTime ≤
      resources.execution.onlineTime ∧
    resources.execution.compiler.workspace ≤ resources.execution.onlineWorkspace

/-- The attack's initial input, emitted output and copying are accounted for relative to a
model-specific execution certificate. This proposition is intended as an explicit part of a
concrete `Within` certificate; it does not manufacture an execution witness. -/
@[expose] def AccountsForOutput {Certificate : Type*}
    (Certifies : Certificate → AttackExecutionResources → Prop)
    (certificate : Certificate) (resources : AttackResources) : Prop :=
  Certifies certificate resources.execution ∧
    resources.execution.outputCopyTime ≤ resources.execution.onlineTime

/-- `used` fits `budget` when every named coordinate fits independently. This intentionally does
not turn the coordinates into a scalar total. -/
@[expose] def Fits (used budget : AttackResources) : Prop :=
  used.programBits ≤ budget.programBits ∧
    used.generatedProgramBits ≤ budget.generatedProgramBits ∧
    used.generatorBits ≤ budget.generatorBits ∧
    used.compilerBits ≤ budget.compilerBits ∧
    used.interpreterBits ≤ budget.interpreterBits ∧
    used.controllerBits ≤ budget.controllerBits ∧
    used.execution.inputBits ≤ budget.execution.inputBits ∧
    used.execution.onlineTime ≤ budget.execution.onlineTime ∧
    used.execution.onlineWorkspace ≤ budget.execution.onlineWorkspace ∧
    used.execution.compiler.inputBits ≤ budget.execution.compiler.inputBits ∧
    used.execution.compiler.time ≤ budget.execution.compiler.time ∧
    used.execution.compiler.workspace ≤ budget.execution.compiler.workspace ∧
    used.execution.compiler.outputBits ≤ budget.execution.compiler.outputBits ∧
    used.execution.compiler.outputCopyTime ≤ budget.execution.compiler.outputCopyTime ∧
    used.execution.randomBits ≤ budget.execution.randomBits ∧
    used.execution.classicalQueries ≤ budget.execution.classicalQueries ∧
    used.execution.quantumQueries ≤ budget.execution.quantumQueries ∧
    used.execution.qubits ≤ budget.execution.qubits ∧
    used.execution.gates ≤ budget.execution.gates ∧
    used.execution.requestBits ≤ budget.execution.requestBits ∧
    used.execution.replyBits ≤ budget.execution.replyBits ∧
    used.execution.outputBits ≤ budget.execution.outputBits ∧
    used.execution.outputCopyTime ≤ budget.execution.outputCopyTime

instance (used budget : AttackResources) : Decidable (used.Fits budget) := by
  unfold Fits
  infer_instance

/-- Every exact resource profile fits itself. -/
theorem fits_refl (r : AttackResources) : r.Fits r := by
  simp [Fits]

/-- A resource schedule is polynomial when each coordinate is polynomially bounded independently. -/
structure IsPolynomial (schedule : ℕ → AttackResources) : Prop where
  programBits : PolynomiallyBounded fun n => (schedule n).programBits
  generatedProgramBits : PolynomiallyBounded fun n => (schedule n).generatedProgramBits
  generatorBits : PolynomiallyBounded fun n => (schedule n).generatorBits
  compilerBits : PolynomiallyBounded fun n => (schedule n).compilerBits
  interpreterBits : PolynomiallyBounded fun n => (schedule n).interpreterBits
  controllerBits : PolynomiallyBounded fun n => (schedule n).controllerBits
  inputBits : PolynomiallyBounded fun n => (schedule n).execution.inputBits
  onlineTime : PolynomiallyBounded fun n => (schedule n).execution.onlineTime
  onlineWorkspace : PolynomiallyBounded fun n => (schedule n).execution.onlineWorkspace
  compilerInputBits : PolynomiallyBounded fun n => (schedule n).execution.compiler.inputBits
  compilerTime : PolynomiallyBounded fun n => (schedule n).execution.compiler.time
  compilerWorkspace : PolynomiallyBounded fun n => (schedule n).execution.compiler.workspace
  compilerOutputBits : PolynomiallyBounded fun n => (schedule n).execution.compiler.outputBits
  compilerOutputCopyTime :
    PolynomiallyBounded fun n => (schedule n).execution.compiler.outputCopyTime
  randomBits : PolynomiallyBounded fun n => (schedule n).execution.randomBits
  classicalQueries : PolynomiallyBounded fun n => (schedule n).execution.classicalQueries
  quantumQueries : PolynomiallyBounded fun n => (schedule n).execution.quantumQueries
  qubits : PolynomiallyBounded fun n => (schedule n).execution.qubits
  gates : PolynomiallyBounded fun n => (schedule n).execution.gates
  requestBits : PolynomiallyBounded fun n => (schedule n).execution.requestBits
  replyBits : PolynomiallyBounded fun n => (schedule n).execution.replyBits
  outputBits : PolynomiallyBounded fun n => (schedule n).execution.outputBits
  outputCopyTime : PolynomiallyBounded fun n => (schedule n).execution.outputCopyTime

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
