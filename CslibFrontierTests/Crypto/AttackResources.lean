/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Game.AttackResources
import CslibFrontier.Tactic.PolyTime

/-!
# Checked clients for componentwise attack resources

The finite client uses a nonconstant explicit installed-artifact inventory and every execution
coordinate. Two separate program occurrences verify per-copy charging. Separate handler and
table/advice occurrences contrast with a main program containing hardwired versions, which are not
charged again. The family client proves all per-kind inventory sums and execution coordinates
polynomial, then applies the reusable concrete-to-asymptotic bridge. Equal games isolate the
resource API; this test asserts no cryptographic security endpoint.
-/

namespace Cslib.Tests.AttackResources

open Cslib Cslib.Crypto
open scoped NNReal

/-- A nonconstant installed inventory. The two `program` entries are distinct stored copies, so
both contribute. The other entries, including the handler and static table/advice, are separately
installed occurrences. -/
def sampleInventory (n : ℕ) : List Game.InstalledArtifact :=
  [{ kind := .program, bits := n + 1 },
    { kind := .program, bits := 2 * n + 1 },
    { kind := .generatedProgram, bits := 3 * n + 1 },
    { kind := .generator, bits := 4 * n + 1 },
    { kind := .compiler, bits := 5 * n + 1 },
    { kind := .interpreter, bits := 6 * n + 1 },
    { kind := .controller, bits := 7 * n + 1 },
    { kind := .handler, bits := 8 * n + 1 },
    { kind := .table, bits := 9 * n + 1 }]

/-- Executed compiler coordinates used by both separate and inlined installation clients. -/
def sampleCompilerExecution (n : ℕ) : Game.ExecutedCompilerResources where
  inputBits := 2 * n + 1
  time := 6 * n + 3
  workspace := 3 * n + 1
  outputBits := 3 * n + 1
  outputCopyTime := 3 * n + 1

/-- Full execution coordinates, including initial input and final-output copying. -/
def sampleExecution (n : ℕ) : Game.AttackExecutionResources where
  inputBits := 8 * n + 1
  onlineTime := 30 * n + 5
  onlineWorkspace := 8 * n + 1
  compiler := sampleCompilerExecution n
  randomBits := 9 * n + 1
  classicalQueries := 10 * n + 1
  quantumQueries := 11 * n + 1
  qubits := 12 * n + 1
  gates := 13 * n + 1
  requestBits := 14 * n + 1
  replyBits := 15 * n + 1
  outputBits := 16 * n + 1
  outputCopyTime := 16 * n + 1

/-- A nonconstant profile exercising every installed, compiler, online, oracle and communication
coordinate. The compiler runs online here: its time is included in `onlineTime`, its workspace fits
the online peak, and its generated program is a distinct installed occurrence. -/
def sampleResources (n : ℕ) : Game.AttackResources :=
  Game.AttackResources.ofInventory (sampleInventory n) (sampleExecution n)

/-- Per-kind sums charge both installed program copies and every other retained occurrence once. -/
theorem sampleInstalledBits_at_two :
    (sampleResources 2).programBits = 8 ∧
      (sampleResources 2).generatedProgramBits = 7 ∧
      (sampleResources 2).generatorBits = 9 ∧
      (sampleResources 2).compilerBits = 11 ∧
      (sampleResources 2).interpreterBits = 13 ∧
      (sampleResources 2).controllerBits = 15 ∧
      (sampleResources 2).handlerBits = 17 ∧
      (sampleResources 2).tableBits = 19 := by
  decide

/-- A handler and table/advice hardwired into the retained main program are not separately
installed occurrences and therefore are not charged again under their independent categories. -/
def hardwiredStaticResources (n : ℕ) : Game.AttackResources :=
  Game.AttackResources.ofInventory
    [{ kind := .program, bits := 10 * n + 3 }]
    (sampleExecution n)

theorem hardwiredStatic_not_doubleCounted (n : ℕ) :
    (hardwiredStaticResources n).programBits = 10 * n + 3 ∧
      (hardwiredStaticResources n).handlerBits = 0 ∧
      (hardwiredStaticResources n).tableBits = 0 := by
  exact ⟨rfl, rfl, rfl⟩

/-- A model-specific certificate predicate for the test compiler. Besides exact input, output,
clock and workspace coordinates, it asserts that production and copying each pay for the emitted
bit length. -/
@[expose] def SampleCompilerCertifies (n : ℕ)
    (resources : Game.ExecutedCompilerResources) : Prop :=
  resources.inputBits = 2 * n + 1 ∧
    resources.outputBits = 3 * n + 1 ∧
    resources.time = 6 * n + 3 ∧
    resources.workspace = 3 * n + 1 ∧
    resources.outputCopyTime = 3 * n + 1 ∧
    resources.outputBits ≤ resources.time ∧
    resources.outputBits ≤ resources.outputCopyTime

/-- Separate compiler installation charges the compiler occurrence and emitted generated-program
occurrence, and connects every compiler coordinate to the model-specific certificate. -/
theorem sampleCompiler_accounted (n : ℕ) :
    Game.AttackResources.AccountsForExecutedCompiler SampleCompilerCertifies n
      (.separatelyInstalled (5 * n + 1)) (sampleResources n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Game.CompilerInstallation.IsInInventory, sampleResources, sampleInventory,
      Game.AttackResources.ofInventory]
  · simp [sampleResources, sampleInventory, sampleExecution, sampleCompilerExecution,
      Game.AttackResources.ofInventory]
  · exact ⟨rfl, rfl, rfl, rfl, rfl, by omega, le_rfl⟩
  · change (6 * n + 3) + (3 * n + 1) ≤ 30 * n + 5
    omega
  · change 3 * n + 1 ≤ 8 * n + 1
    omega

/-- The same executed compiler may be inlined into one installed main program. No separate
compiler occurrence is present or charged; the emitted program remains a distinct occurrence. -/
def inlinedCompilerResources (n : ℕ) : Game.AttackResources :=
  Game.AttackResources.ofInventory
    [{ kind := .program, bits := 9 * n + 2 },
      { kind := .generatedProgram, bits := 3 * n + 1 }]
    (sampleExecution n)

theorem inlinedCompiler_accounted (n : ℕ) :
    (inlinedCompilerResources n).compilerBits = 0 ∧
      Game.AttackResources.AccountsForExecutedCompiler SampleCompilerCertifies n
        (.inlinedIntoProgram (9 * n + 2)) (inlinedCompilerResources n) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Game.CompilerInstallation.IsInInventory, inlinedCompilerResources,
      Game.AttackResources.ofInventory]
  · simp [inlinedCompilerResources, sampleExecution, sampleCompilerExecution,
      Game.AttackResources.ofInventory]
  · exact ⟨rfl, rfl, rfl, rfl, rfl, by omega, le_rfl⟩
  · change (6 * n + 3) + (3 * n + 1) ≤ 30 * n + 5
    omega
  · change 3 * n + 1 ≤ 8 * n + 1
    omega

/-- A model-specific whole-attack certificate connects initial input, emitted output, production
and output copying to the declared online execution. -/
@[expose] def SampleAttackCertifies (n : ℕ)
    (resources : Game.AttackExecutionResources) : Prop :=
  resources.inputBits = 8 * n + 1 ∧
    resources.outputBits = 16 * n + 1 ∧
    resources.outputCopyTime = 16 * n + 1 ∧
    resources.onlineTime = 30 * n + 5 ∧
    resources.onlineWorkspace = 8 * n + 1 ∧
    resources.outputBits ≤ resources.onlineTime ∧
    resources.outputBits ≤ resources.outputCopyTime

theorem sampleOutput_accounted (n : ℕ) :
    Game.AttackResources.AccountsForOutput SampleAttackCertifies n (sampleResources n) := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, by omega, le_rfl⟩, ?_⟩
  change 16 * n + 1 ≤ 30 * n + 5
  omega

/-- Offline compilation contributes no compiler execution costs, while its generated program is
still a nonconstant installed occurrence and the attack's own output remains explicit. -/
def offlineCompiledResources (n : ℕ) : Game.AttackResources :=
  Game.AttackResources.ofInventory
    [{ kind := .program, bits := 2 * n + 1 },
      { kind := .generatedProgram, bits := n + 1 }] {
    inputBits := n
    onlineTime := 4 * n + 2
    onlineWorkspace := n + 1
    compiler := { inputBits := 0, time := 0, workspace := 0, outputBits := 0,
      outputCopyTime := 0 }
    randomBits := n
    classicalQueries := n
    quantumQueries := n
    qubits := n + 1
    gates := 2 * n + 1
    requestBits := n
    replyBits := n
    outputBits := n + 1
    outputCopyTime := n + 1 }

theorem offlineCompilation_separate (n : ℕ) :
    (offlineCompiledResources n).programBits = 2 * n + 1 ∧
      (offlineCompiledResources n).generatedProgramBits = n + 1 ∧
      (offlineCompiledResources n).compilerBits = 0 ∧
      (offlineCompiledResources n).execution.compiler.inputBits = 0 ∧
      (offlineCompiledResources n).execution.compiler.time = 0 ∧
      (offlineCompiledResources n).execution.compiler.workspace = 0 ∧
      (offlineCompiledResources n).execution.compiler.outputBits = 0 ∧
      (offlineCompiledResources n).execution.compiler.outputCopyTime = 0 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The sample family is componentwise polynomial; no scalar resource sum is used. -/
theorem sampleResources_isPolynomial :
    Game.AttackResources.IsPolynomial sampleResources where
  programBits := by
    change PolynomiallyBounded fun n => (n + 1) + (2 * n + 1)
    fun_prop
  generatedProgramBits := by
    change PolynomiallyBounded fun n => 3 * n + 1
    fun_prop
  generatorBits := by
    change PolynomiallyBounded fun n => 4 * n + 1
    fun_prop
  compilerBits := by
    change PolynomiallyBounded fun n => 5 * n + 1
    fun_prop
  interpreterBits := by
    change PolynomiallyBounded fun n => 6 * n + 1
    fun_prop
  controllerBits := by
    change PolynomiallyBounded fun n => 7 * n + 1
    fun_prop
  handlerBits := by
    change PolynomiallyBounded fun n => 8 * n + 1
    fun_prop
  tableBits := by
    change PolynomiallyBounded fun n => 9 * n + 1
    fun_prop
  inputBits := by
    change PolynomiallyBounded fun n => 8 * n + 1
    fun_prop
  onlineTime := by
    change PolynomiallyBounded fun n => 30 * n + 5
    fun_prop
  onlineWorkspace := by
    change PolynomiallyBounded fun n => 8 * n + 1
    fun_prop
  compilerInputBits := by
    change PolynomiallyBounded fun n => 2 * n + 1
    fun_prop
  compilerTime := by
    change PolynomiallyBounded fun n => 6 * n + 3
    fun_prop
  compilerWorkspace := by
    change PolynomiallyBounded fun n => 3 * n + 1
    fun_prop
  compilerOutputBits := by
    change PolynomiallyBounded fun n => 3 * n + 1
    fun_prop
  compilerOutputCopyTime := by
    change PolynomiallyBounded fun n => 3 * n + 1
    fun_prop
  randomBits := by
    change PolynomiallyBounded fun n => 9 * n + 1
    fun_prop
  classicalQueries := by
    change PolynomiallyBounded fun n => 10 * n + 1
    fun_prop
  quantumQueries := by
    change PolynomiallyBounded fun n => 11 * n + 1
    fun_prop
  qubits := by
    change PolynomiallyBounded fun n => 12 * n + 1
    fun_prop
  gates := by
    change PolynomiallyBounded fun n => 13 * n + 1
    fun_prop
  requestBits := by
    change PolynomiallyBounded fun n => 14 * n + 1
    fun_prop
  replyBits := by
    change PolynomiallyBounded fun n => 15 * n + 1
    fun_prop
  outputBits := by
    change PolynomiallyBounded fun n => 16 * n + 1
    fun_prop
  outputCopyTime := by
    change PolynomiallyBounded fun n => 16 * n + 1
    fun_prop

/-- The finite predicate records the exact profile and requires the model-specific compiler and
whole-execution certificates. It derives no existential program. -/
@[expose] def WithinSample (n : ℕ) (budget : Game.AttackResources)
    (_adversary : ℕ → Bool) : Prop :=
  (sampleResources n).Fits budget ∧
    Game.AttackResources.AccountsForExecutedCompiler SampleCompilerCertifies n
      (.separatelyInstalled (5 * n + 1)) (sampleResources n) ∧
    Game.AttackResources.AccountsForOutput SampleAttackCertifies n (sampleResources n)

/-- A deliberately neutral game family used to isolate the resource bridge. -/
def sampleGame (adversary : ℕ → Bool) (n : ℕ) : Game :=
  PMF.pure (adversary n)

/-- Finite indistinguishability under the exact nonconstant componentwise profile. -/
theorem indistinguishableWithin_sampleGame :
    Game.IndistinguishableWithin sampleGame sampleGame WithinSample (fun _ _ => 0) :=
  Game.IndistinguishableWithin.refl sampleGame WithinSample

/-- The finite bound lifts along the supplied nonconstant polynomial schedule. -/
theorem indistinguishable_sampleGame :
    Game.Indistinguishable sampleGame sampleGame (fun _ => True) := by
  refine indistinguishableWithin_sampleGame.indistinguishable_attackResources ?_ ?_
  · intro adversary _
    exact ⟨sampleResources, sampleResources_isPolynomial, fun n => by
      exact ⟨Game.AttackResources.fits_refl (sampleResources n),
        sampleCompiler_accounted n, sampleOutput_accounted n⟩⟩
  · intro schedule _
    simpa using negligible_zero

end Cslib.Tests.AttackResources
