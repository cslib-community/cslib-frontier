/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Game.AttackResources
import CslibFrontier.Tactic.PolyTime

/-!
# Checked clients for componentwise attack resources

The finite client uses a nonconstant exact profile containing every coordinate. The family client
proves those coordinates polynomial separately and applies the reusable concrete-to-asymptotic
bridge. Equal games isolate the resource API; this test asserts no cryptographic security endpoint.
-/

namespace Cslib.Tests.AttackResources

open Cslib Cslib.Crypto
open scoped NNReal

/-- A nonconstant profile exercising every static, online, oracle and communication coordinate. -/
def sampleResources (n : ℕ) : Game.AttackResources where
  programBits := n + 1
  generatorBits := 2 * n + 1
  interpreterBits := 3 * n + 1
  controllerBits := 4 * n + 1
  onlineTime := 5 * n + 1
  onlineWorkspace := 6 * n + 1
  randomBits := 7 * n + 1
  classicalQueries := 8 * n + 1
  quantumQueries := 9 * n + 1
  qubits := 10 * n + 1
  gates := 11 * n + 1
  requestBits := 12 * n + 1
  replyBits := 13 * n + 1
  outputBits := 14 * n + 1

/-- All coordinates of the finite profile have their declared nonconstant values. -/
theorem sampleResources_at_two : sampleResources 2 = {
    programBits := 3
    generatorBits := 5
    interpreterBits := 7
    controllerBits := 9
    onlineTime := 11
    onlineWorkspace := 13
    randomBits := 15
    classicalQueries := 17
    quantumQueries := 19
    qubits := 21
    gates := 23
    requestBits := 25
    replyBits := 27
    outputBits := 29 } := by
  rfl

/-- The sample family is componentwise polynomial; no scalar resource sum is used. -/
theorem sampleResources_isPolynomial :
    Game.AttackResources.IsPolynomial sampleResources where
  programBits := by fun_prop
  generatorBits := by fun_prop
  interpreterBits := by fun_prop
  controllerBits := by fun_prop
  onlineTime := by fun_prop
  onlineWorkspace := by fun_prop
  randomBits := by fun_prop
  classicalQueries := by fun_prop
  quantumQueries := by fun_prop
  qubits := by fun_prop
  gates := by fun_prop
  requestBits := by fun_prop
  replyBits := by fun_prop
  outputBits := by fun_prop

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
