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
coordinate. Two separate program occurrences verify per-copy charging. The family client proves
all per-kind inventory sums and execution coordinates polynomial, then applies the reusable
concrete-to-asymptotic bridge. Equal games isolate the resource API; this test asserts no
cryptographic security endpoint.
-/

namespace Cslib.Tests.AttackResources

open Cslib Cslib.Crypto
open scoped NNReal

/-- A nonconstant installed inventory. The two `program` entries are distinct stored copies, so
both contribute. The generator, compiler, interpreter and controller are separate occurrences. -/
def sampleInventory (n : ℕ) : List Game.InstalledArtifact :=
  [{ kind := .program, bits := n + 1 },
    { kind := .program, bits := 2 * n + 1 },
    { kind := .generator, bits := 3 * n + 1 },
    { kind := .compiler, bits := 4 * n + 1 },
    { kind := .interpreter, bits := 5 * n + 1 },
    { kind := .controller, bits := 6 * n + 1 }]

/-- A nonconstant profile exercising every installed, compiler, online, oracle and communication
coordinate. The compiler runs online here: its time is included in `onlineTime`, its workspace fits
the online peak, and its generated program is the first installed occurrence. -/
def sampleResources (n : ℕ) : Game.AttackResources :=
  Game.AttackResources.ofInventory (sampleInventory n) {
    onlineTime := 7 * n + 1
    onlineWorkspace := 8 * n + 1
    compilerTime := 2 * n + 1
    compilerWorkspace := 3 * n + 1
    compilerOutputBits := n + 1
    randomBits := 9 * n + 1
    classicalQueries := 10 * n + 1
    quantumQueries := 11 * n + 1
    qubits := 12 * n + 1
    gates := 13 * n + 1
    requestBits := 14 * n + 1
    replyBits := 15 * n + 1
    outputBits := 16 * n + 1 }

/-- Per-kind sums charge both installed program copies and every other retained occurrence once. -/
theorem sampleInstalledBits_at_two :
    (sampleResources 2).programBits = 8 ∧
      (sampleResources 2).generatorBits = 7 ∧
      (sampleResources 2).compilerBits = 9 ∧
      (sampleResources 2).interpreterBits = 11 ∧
      (sampleResources 2).controllerBits = 13 := by
  decide

/-- Executed compilation charges the installed compiler and emitted program occurrences, and its
work is included in the overall online time and peak workspace. -/
theorem sampleCompiler_accounted (n : ℕ) :
    Game.AttackResources.AccountsForExecutedCompiler (sampleResources n) := by
  refine ⟨⟨4 * n + 1, ?_⟩, ?_, ?_, ?_⟩
  · simp [sampleResources, sampleInventory, Game.AttackResources.ofInventory]
  · simp [sampleResources, sampleInventory, Game.AttackResources.ofInventory]
  · change 2 * n + 1 ≤ 7 * n + 1
    omega
  · change 3 * n + 1 ≤ 8 * n + 1
    omega

/-- Offline compilation contributes no compiler execution costs, while its generated program is
still a nonconstant installed occurrence and the attack's own output remains explicit. -/
def offlineCompiledResources (n : ℕ) : Game.AttackResources :=
  Game.AttackResources.ofInventory [{ kind := .program, bits := n + 1 }] {
    onlineTime := 2 * n + 1
    onlineWorkspace := n + 1
    compilerTime := 0
    compilerWorkspace := 0
    compilerOutputBits := 0
    randomBits := n
    classicalQueries := n
    quantumQueries := n
    qubits := n + 1
    gates := 2 * n + 1
    requestBits := n
    replyBits := n
    outputBits := n + 1 }

theorem offlineCompilation_separate (n : ℕ) :
    (offlineCompiledResources n).programBits = n + 1 ∧
      (offlineCompiledResources n).compilerBits = 0 ∧
      (offlineCompiledResources n).execution.compilerTime = 0 ∧
      (offlineCompiledResources n).execution.compilerWorkspace = 0 ∧
      (offlineCompiledResources n).execution.compilerOutputBits = 0 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The sample family is componentwise polynomial; no scalar resource sum is used. -/
theorem sampleResources_isPolynomial :
    Game.AttackResources.IsPolynomial sampleResources where
  programBits := by
    change PolynomiallyBounded fun n => (n + 1) + (2 * n + 1)
    fun_prop
  generatorBits := by
    change PolynomiallyBounded fun n => 3 * n + 1
    fun_prop
  compilerBits := by
    change PolynomiallyBounded fun n => 4 * n + 1
    fun_prop
  interpreterBits := by
    change PolynomiallyBounded fun n => 5 * n + 1
    fun_prop
  controllerBits := by
    change PolynomiallyBounded fun n => 6 * n + 1
    fun_prop
  onlineTime := by
    change PolynomiallyBounded fun n => 7 * n + 1
    fun_prop
  onlineWorkspace := by
    change PolynomiallyBounded fun n => 8 * n + 1
    fun_prop
  compilerTime := by
    change PolynomiallyBounded fun n => 2 * n + 1
    fun_prop
  compilerWorkspace := by
    change PolynomiallyBounded fun n => 3 * n + 1
    fun_prop
  compilerOutputBits := by
    change PolynomiallyBounded fun n => n + 1
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

/-- The finite predicate records the exact profile instead of deriving an existential program. -/
@[expose] def WithinSample (n : ℕ) (budget : Game.AttackResources)
    (_adversary : ℕ → Bool) : Prop :=
  (sampleResources n).Fits budget

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
      simpa only [WithinSample] using Game.AttackResources.fits_refl (sampleResources n)⟩
  · intro schedule _
    simpa using negligible_zero

end Cslib.Tests.AttackResources
