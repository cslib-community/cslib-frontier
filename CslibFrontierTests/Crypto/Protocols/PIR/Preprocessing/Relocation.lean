/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/
module

import CslibFrontier.Crypto.Protocols.PIR.Preprocessing.Relocation
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-! # Tests for the Wang–Ren Relocation Data Structure

Concrete execution traces, invariant checks, and theorem instantiations for
`CslibFrontier.Crypto.Protocols.PIR.Preprocessing.Relocation`.
-/

set_option linter.privateModule false

namespace CslibTests.Crypto.Protocols.PIR.Preprocessing.Relocation

open Cslib Cslib.Crypto.Protocols.PIR.Preprocessing.Relocation

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

private theorem hm24 : 2 ≤ 4 := by omega

theorem valid_s₀ : s₀.Valid := valid_init testPerm hm24

theorem valid_s₁ : s₁.Valid := valid_relocate valid_s₀ (by decide) (by decide)

theorem valid_s₂ : s₂.Valid := valid_relocate valid_s₁ (by decide) (by decide)

-- Initial positions and access values in `s₀`:
example : locate s₀ 0 hm24 = 1 := rfl
example : locate s₀ 1 hm24 = 0 := rfl
example : access s₀ 0 = some 1 := rfl
example : access s₀ 1 = some 0 := rfl
example : access s₀ 2 = none := rfl
example : access s₀ 3 = none := rfl

-- After relocating position `1` in `s₁`, element `0` moves to `3` while element `1` stays at `0`:
example : outEdge? s₁ 1 = some 3 := rfl
example : inEdge? s₁ 3 = some 1 := rfl
example : locate s₁ 0 hm24 = 3 := rfl
example : locate s₁ 1 hm24 = 0 := rfl
example : access s₁ 3 = some 0 := rfl
example : access s₁ 0 = some 1 := rfl
example : access s₁ 2 = none := rfl

-- After relocating position `3` in `s₂`, element `0` traverses `1 → 3 → 2` to position `2`:
example : outEdge? s₂ 1 = some 3 := rfl
example : outEdge? s₂ 3 = some 2 := rfl
example : outEdge? s₂ 2 = none := rfl
example : startOfChain s₂ 2 = 1 := rfl
example : endOfChain s₂ 1 = 2 := rfl
example : locate s₂ 0 hm24 = 2 := rfl
example : locate s₂ 1 hm24 = 0 := rfl
example : access s₂ 2 = some 0 := rfl
example : access s₂ 0 = some 1 := rfl

-- Concrete `realRunSteps` trace on `[1, 3]`:
example : (realRunSteps s₀ [1, 3] hm24).2 = [some 3, some 2] := rfl

-- Concrete `realRunSteps` trace when relocating an empty slot (`2`) then an occupied slot (`1`):
example : (realRunSteps s₀ [2, 1] hm24).2 = [none, some 3] := rfl

-- Ideal arrays coupled with `s₀`, `s₁`, `s₂` (empty cells: `{2, 3}`, then `{2}`, then none):
example : stateToIdealArray s₀ 0 = .elem 1 ∧ stateToIdealArray s₀ 1 = .elem 0 ∧
    stateToIdealArray s₀ 2 = .empty ∧ stateToIdealArray s₀ 3 = .empty := ⟨rfl, rfl, rfl, rfl⟩
example : stateToIdealArray s₁ 0 = .elem 1 ∧ stateToIdealArray s₁ 1 = .consumed ∧
    stateToIdealArray s₁ 2 = .empty ∧ stateToIdealArray s₁ 3 = .elem 0 := ⟨rfl, rfl, rfl, rfl⟩
example : stateToIdealArray s₂ 0 = .elem 1 ∧ stateToIdealArray s₂ 1 = .consumed ∧
    stateToIdealArray s₂ 2 = .elem 0 ∧ stateToIdealArray s₂ 3 = .consumed := ⟨rfl, rfl, rfl, rfl⟩

/-! ### Concrete Instantiations of Lemmas 3.13–3.16 -/

/-- Concrete instantiation of Lemma 3.13 (`existsUnique_access_eq`) on `s₂`. -/
example (e : Fin 2) : ∃! c : Fin 4, c ∉ s₂.history ∧ access s₂ c = some e :=
  existsUnique_access_eq valid_s₂ e

/-- Concrete instantiation of Lemma 3.14 (`access_eq_some_iff_locate_eq`) on `s₂` and unconsumed
position `2`. -/
example (e : Fin 2) : access s₂ 2 = some e ↔ locate s₂ e hm24 = 2 :=
  access_eq_some_iff_locate_eq valid_s₂ (by decide) e hm24

/-- Concrete instantiation of Lemma 3.15 (i) (`locate_relocate_of_ne`) on `s₁` relocating `3` for
element `1`. -/
example : locate s₂ 1 hm24 = locate s₁ 1 hm24 :=
  locate_relocate_of_ne valid_s₁ (by decide) (by decide) hm24 (by decide)

/-- Concrete instantiation of Lemma 3.15 (ii) (`relocate_destination_empty`) on `s₁` relocating
`3` for element `0`. -/
example : locate s₂ 0 hm24 ∉ s₂.history ∧ access s₁ (locate s₂ 0 hm24) = none :=
  relocate_destination_empty valid_s₁ (by decide) (by decide) (e := 0) hm24 rfl

/-- Concrete query sequence `c : Fin 2 → Fin 4` relocating positions `1` then `3`. -/
def testQueries : Fin 2 → Fin 4 := ![1, 3]

theorem testQueries_injective : Function.Injective testQueries := by decide

/-- Concrete instantiation of Lemma 3.16 (`eval_realExperiment_eq_idealExperiment`) for
`m = 2, m' = 4, Q = 2`. -/
example :
    (realExperiment 2 4 2 testQueries hm24).eval =
      (idealExperiment 2 4 2 testQueries hm24).eval :=
  eval_realExperiment_eq_idealExperiment testQueries_injective (by decide) hm24

/-- Concrete output produced by `realExperiment 2 4 2 testQueries hm24` when the sampled permutation
is `testPerm`; both relocation steps take the occupied (`some _`) branch. -/
def testOutput : RelocationOutput 2 4 :=
  ⟨fun e => locate s₀ e hm24, [some 3, some 2]⟩

/-- The support of `realExperiment 2 4 2 testQueries hm24` (and hence of `idealExperiment`, by
Lemma 3.16) contains `testOutput`, witnessing that the non-empty relocation branch is exercised. -/
theorem testOutput_mem_support_realExperiment :
    testOutput ∈ (realExperiment 2 4 2 testQueries hm24).eval.support := by
  simp only [realExperiment, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
  exact ⟨testPerm, Cslib.Probability.PMF.mem_support_uniformOfFintype testPerm, rfl⟩

/-! ### Necessity of Distinct Relocated Positions (`history.Nodup`) -/

/-- State obtained by relocating position `1` twice (`history = [1, 1]`), violating
`RelocationState.Valid`. -/
def s₁_dup : RelocationState 2 4 := relocate s₁ 1

theorem not_valid_s₁_dup : ¬ s₁_dup.Valid := by
  simp [RelocationState.Valid, s₁_dup, s₁, s₀, init, relocate]

-- Without `history.Nodup`, both unconsumed positions `2` and `3` trace back to `1` via `inEdge?`,
-- so element `0` appears at two distinct unconsumed positions and `locate`/`access` invertibility
-- (Lemmas 3.13 and 3.14) fails:
example : (2 : Fin 4) ∉ s₁_dup.history ∧ (3 : Fin 4) ∉ s₁_dup.history := by decide
example : access s₁_dup 2 = some 0 ∧ access s₁_dup 3 = some 0 := ⟨rfl, rfl⟩
example :
    locate s₁_dup 0 hm24 = 3 ∧ access s₁_dup 2 = some 0 ∧ locate s₁_dup 0 hm24 ≠ 2 := by decide

/-! ### Empty Queried Cell Selecting Itself (Experiment 3.2) -/

/-- Ideal array for `m = 1, m' = 2`: element `0` at position `0`, position `1` empty. -/
def selfA : Fin 2 → IdealCell 1 := ![.elem 0, .empty]

/-- Querying the empty position `1` when the only empty destination is `1` itself: the cell ends
up consumed, and the output is `none`, read from the cell before the update (proof of
Lemma 3.16, p. 16). The literal pseudocode of Experiment 3.2 would output `some 1` here. -/
example : (idealUpdate selfA 1 1).2 = none := rfl
example : (idealUpdate selfA 1 1).1 1 = .consumed ∧ (idealUpdate selfA 1 1).1 0 = .elem 0 :=
  ⟨rfl, rfl⟩

/-- The real experiment agrees: with the identity permutation on `Fin 2` and `m = 1`, relocating
the empty position `1` outputs `none`. -/
example : (realRunSteps (init (m := 1) (1 : Equiv.Perm (Fin 2))) [1] (by omega)).2 = [none] := rfl

end CslibTests.Crypto.Protocols.PIR.Preprocessing.Relocation
