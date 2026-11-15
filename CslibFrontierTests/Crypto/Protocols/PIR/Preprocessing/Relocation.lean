/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/
module

import CslibFrontier.Crypto.Protocols.PIR.Preprocessing.Relocation

/-! # Tests for the Wang–Ren Relocation Data Structure

Concrete execution traces, invariant checks, and theorem instantiations for
`CslibFrontier.Crypto.Protocols.PIR.Preprocessing.Relocation`.
-/

set_option linter.privateModule false

namespace CslibTests.Crypto.Protocols.PIR.Preprocessing.Relocation

open Cslib.Crypto.Protocols.PIR.Preprocessing.Relocation

/-! ### Axiom Footprint Checks -/

/-- info: 'Cslib.Crypto.Protocols.PIR.Preprocessing.Relocation.valid_init' depends on axioms: [propext] -/
#guard_msgs in
#print axioms valid_init

/--
info: 'Cslib.Crypto.Protocols.PIR.Preprocessing.Relocation.inEdge?_perm_castLE_eq_none' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms inEdge?_perm_castLE_eq_none

/--
info: 'Cslib.Crypto.Protocols.PIR.Preprocessing.Relocation.valid_relocate' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms valid_relocate

/-! ### Concrete Permutation and Multi-Step Relocation Trace (`m = 2, m' = 4`) -/

/-- Concrete permutation on `Fin 4` swapping `0 ↔ 1` and `2 ↔ 3`:
initial element `0` is at `1`, initial element `1` is at `0`, spare slot `2` maps to `3`,
and spare slot `3` maps to `2`. -/
def testPerm : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3

/-- Initial state for `m = 2, m' = 4` under `testPerm`. -/
def s₀ : RelocationState 2 4 := init testPerm

/-- Relocate physical position `1` (which initially holds logical element `0`).
This adds edge `1 → testPerm 2 = 3`, moving element `0` to position `3`. -/
def s₁ : RelocationState 2 4 := relocate s₀ 1

/-- Relocate physical position `3` (which now holds logical element `0` after the first
relocation). This adds edge `3 → testPerm 3 = 2`, forming a length-2 chain `1 → 3 → 2`. -/
def s₂ : RelocationState 2 4 := relocate s₁ 3

theorem valid_s₀ : s₀.Valid := valid_init testPerm

theorem valid_s₁ : s₁.Valid := valid_relocate valid_s₀ (by decide) (by decide)

theorem valid_s₂ : s₂.Valid := valid_relocate valid_s₁ (by decide) (by decide)

-- Initial positions and access values in `s₀`:
example : locate s₀ 0 = 1 := rfl
example : locate s₀ 1 = 0 := rfl
example : access s₀ 0 = some 1 := rfl
example : access s₀ 1 = some 0 := rfl
example : access s₀ 2 = none := rfl
example : access s₀ 3 = none := rfl

-- After relocating position `1` in `s₁`, element `0` moves to `3` while element `1` stays at `0`:
example : outEdge? s₁ 1 = some 3 := rfl
example : inEdge? s₁ 3 = some 1 := rfl
example : locate s₁ 0 = 3 := rfl
example : locate s₁ 1 = 0 := rfl
example : access s₁ 3 = some 0 := rfl
example : access s₁ 0 = some 1 := rfl
example : access s₁ 2 = none := rfl

-- After relocating position `3` in `s₂`, element `0` traverses `1 → 3 → 2` to position `2`:
example : outEdge? s₂ 1 = some 3 := rfl
example : outEdge? s₂ 3 = some 2 := rfl
example : outEdge? s₂ 2 = none := rfl
example : startOfChain s₂ 2 = 1 := rfl
example : endOfChain s₂ 1 = 2 := rfl
example : locate s₂ 0 = 2 := rfl
example : locate s₂ 1 = 0 := rfl
example : access s₂ 2 = some 0 := rfl
example : access s₂ 0 = some 1 := rfl

-- Concrete `realRunSteps` trace on `[1, 3]`:
example : (realRunSteps s₀ [1, 3]).2 = [some 3, some 2] := rfl

-- Concrete `realRunSteps` trace when relocating an empty slot (`2`) then an occupied slot (`1`):
example : (realRunSteps s₀ [2, 1]).2 = [none, some 3] := rfl

-- Concrete ideal array coupled with `s₀`, `s₁`, `s₂`:
example : emptyPositions (stateToIdealArray s₀) = ({2, 3} : Finset (Fin 4)) := by decide
example : emptyPositions (stateToIdealArray s₁) = ({2} : Finset (Fin 4)) := by decide
example : emptyPositions (stateToIdealArray s₂) = (∅ : Finset (Fin 4)) := by decide

/-! ### Concrete Instantiations of Lemmas 3.13–3.16 and Theorem 3.3 -/

/-- Concrete instantiation of Lemma 3.13 (`existsUnique_access_eq`) on `s₂`. -/
example (e : Fin 2) : ∃! c : Fin 4, c ∉ s₂.history ∧ access s₂ c = some e :=
  existsUnique_access_eq valid_s₂ e

/-- Concrete instantiation of Lemma 3.14 (`locate_eq_iff_access_eq`) on `s₂` and unconsumed
position `2`. -/
example (e : Fin 2) : locate s₂ e = 2 ↔ access s₂ 2 = some e :=
  locate_eq_iff_access_eq valid_s₂ (by decide) e

/-- Concrete instantiation of Lemma 3.15 (i) (`locate_relocate_of_ne`) on `s₁` relocating `3` for
element `1`. -/
example : locate s₂ 1 = locate s₁ 1 :=
  locate_relocate_of_ne valid_s₁ (by decide) (by decide) (by decide) (by decide)

/-- Concrete instantiation of Lemma 3.15 (ii) (`relocate_destination_empty`) on `s₁` relocating
`3` for element `0`. -/
example : locate s₂ 0 ∉ s₂.history ∧ access s₁ (locate s₂ 0) = none :=
  relocate_destination_empty valid_s₁ (by decide) (by decide) (e := 0) (by decide) rfl

/-- Concrete query sequence `c : Fin 2 → Fin 4` relocating positions `1` then `3`. -/
def testQueries : Fin 2 → Fin 4 := ![1, 3]

theorem testQueries_injective : Function.Injective testQueries := by decide

/-- Concrete instantiation of Lemma 3.16 (`eval_realExperiment_eq_idealExperiment`) for
`m = 2, m' = 4, Q = 2`. -/
example : (realExperiment 2 4 2 testQueries).eval = (idealExperiment 2 4 2 testQueries).eval :=
  eval_realExperiment_eq_idealExperiment testQueries_injective (by decide)

/-- Concrete instantiation of Theorem 3.3 (`correctAndSecure`) for `m = 2, m' = 4`. -/
example : CorrectAndSecure 2 4 := correctAndSecure 2 4

end CslibTests.Crypto.Protocols.PIR.Preprocessing.Relocation
