/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate (Mathlib)

public import CslibFrontier.Init
public import Mathlib.Logic.Equiv.Option

/-!
# First return after removing two permutation points

Removing the two `Option` points keeps the first retained successor. Permutation injectivity
rules out revisiting a deleted point before reaching a retained point, so at most three
successor steps are needed. The five possible directed paths are explicit, with no finite
carrier or equality-decision assumption. This is an original elementary reconstruction for
bounded rotation-certificate restriction.
-/

public section

namespace Equiv.Perm

/-- The five possible first-return paths through two removed points. In each case the
retained endpoint is exactly the twice-`removeNone` successor; the two three-step cases
preserve the order of visits to the removed points. -/
theorem removeNone_removeNone_paths {α : Type*} (f : Perm (Option (Option α))) (a : α) :
    let b := Equiv.removeNone (Equiv.removeNone f) a
    f (some (some a)) = some (some b) ∨
      (f (some (some a)) = none ∧ f none = some (some b)) ∨
      (f (some (some a)) = some none ∧ f (some none) = some (some b)) ∨
      (f (some (some a)) = none ∧ f none = some none ∧
        f (some none) = some (some b)) ∨
      (f (some (some a)) = some none ∧ f (some none) = none ∧
        f none = some (some b)) := by
  rcases ha : f (some (some a)) with _ | (_ | c)
  · rcases hb : f none with _ | (_ | c)
    · cases f.injective (ha.trans hb.symm)
    · rcases hc : f (some none) with _ | (_ | c)
      · cases f.injective (ha.trans hc.symm)
      · cases f.injective (hb.trans hc.symm)
      · simp [Equiv.removeNone, Equiv.removeNoneAux, ha, hb, hc]
    · simp [Equiv.removeNone, Equiv.removeNoneAux, ha, hb]
  · rcases hb : f (some none) with _ | (_ | c)
    · rcases hc : f none with _ | (_ | c)
      · cases f.injective (hb.trans hc.symm)
      · cases f.injective (ha.trans hc.symm)
      · simp [Equiv.removeNone, Equiv.removeNoneAux, ha, hb, hc]
    · cases f.injective (ha.trans hb.symm)
    · simp [Equiv.removeNone, Equiv.removeNoneAux, ha, hb]
  · simp [Equiv.removeNone, Equiv.removeNoneAux, ha]

end Equiv.Perm
