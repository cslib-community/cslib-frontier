/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.Completeness

open Cslib.Complexity Cslib.Complexity.SelfClosingDoor

set_option linter.privateModule false

namespace CslibFrontierTests.SelfClosingDoor

private def loopNetwork : Instance :=
  ⟨[⟨⟨0, 0⟩, ⟨0, 1⟩, false⟩], 0, 1⟩

-- An identified entry and exit still flips the door before the second traversal.
example : loopNetwork ∈ Reachability := by
  have h₁ : Step loopNetwork.doors loopNetwork.initial ⟨0, [true]⟩ :=
    (checkStep_eq_true_iff _ _ _).1 (by decide +kernel)
  have h₂ : Step loopNetwork.doors ⟨0, [true]⟩ ⟨1, [false]⟩ :=
    (checkStep_eq_true_iff _ _ _).1 (by decide +kernel)
  exact ⟨⟨1, [false]⟩, (Relation.ReflTransGen.single h₁).tail h₂, rfl⟩

private def oneWay : Instance :=
  ⟨[⟨⟨0, 1⟩, ⟨2, 3⟩, false⟩], 0, 1⟩

-- The final bit may differ from its prescribed initial value.
example : oneWay ∈ Reachability := by
  have h : Step oneWay.doors oneWay.initial ⟨1, [true]⟩ :=
    (checkStep_eq_true_iff _ _ _).1 (by decide +kernel)
  exact ⟨⟨1, [true]⟩, Relation.ReflTransGen.single h, rfl⟩

private def blockedDoor : Instance :=
  ⟨[⟨⟨1, 2⟩, ⟨0, 3⟩, false⟩], 0, 3⟩

-- The tunnel starting at the player is disabled, so no accepting path starts.
example : blockedDoor ∉ Reachability := by
  have hblocked (s : State) : ¬ Step blockedDoor.doors blockedDoor.initial s := by
    rintro ⟨_, i, hp, _⟩
    have hi : i.val = 0 := by have := i.isLt; change i.val < 1 at this; omega
    norm_num [blockedDoor, Instance.initial, Door.tunnel, hi] at hp
  rintro ⟨s, hr, hp⟩
  rcases hr.cases_head with he | ⟨t, ht, _⟩
  · subst s
    change 0 = 3 at hp
    omega
  · exact hblocked t ht

private def parallel : List Door :=
  [⟨⟨0, 1⟩, ⟨1, 0⟩, false⟩, ⟨⟨0, 1⟩, ⟨1, 0⟩, false⟩]

-- Equal tunnel records remain independent list entries.
example : Step parallel ⟨0, [false, false]⟩ ⟨1, [false, true]⟩ :=
  (checkStep_eq_true_iff _ _ _).1 (by decide +kernel)

-- The enabled tunnel is directed; its destination does not serve as an entry.
example : ¬ Step oneWay.doors ⟨1, [false]⟩ ⟨0, [true]⟩ := by
  rw [← checkStep_eq_true_iff]
  decide +kernel

-- A short bit list cannot obtain an enabled tunnel through the lookup fallback.
example : ¬ Step oneWay.doors ⟨0, []⟩ ⟨1, []⟩ := by
  rw [← checkStep_eq_true_iff]
  decide +kernel

-- With no doors, an empty path accepts when already at the target.
example : (⟨[], 5, 5⟩ : Instance) ∈ Reachability :=
  ⟨⟨5, []⟩, Relation.ReflTransGen.refl, rfl⟩

-- The headline theorem is available through its ordinary public module interface.
example : PSPACEComplete encInstance Reachability := Reachability_pspaceComplete

end CslibFrontierTests.SelfClosingDoor
