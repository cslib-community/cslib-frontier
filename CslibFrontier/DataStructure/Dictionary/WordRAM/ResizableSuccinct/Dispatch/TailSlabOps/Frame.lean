/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Dispatch.SlotOps

/-!
# Compacted Operation Memory Frame (`CompOpFrame`)

Defines the memory frame relation `CompOpFrame` for compacted slot and slab operations modifying
only compacted metadata in `[metaBase + offCompLM U w N, metaBase + offCompItems U w N)` and dense
items in `[itemBase, itemBase + compactedItemWords U V w N m_cap)`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompOpFrame`: memory frame relation
  preserving `frontier` and all outside words.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.CompOpFrame.refl`,
  `CompOpFrame.trans`: reflexivity and transitivity of `CompOpFrame`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.DataStructure Cslib.DataStructure.Memory

/-- Memory frame relation for compacted operations modifying only metadata in
`[metaBase + offCompLM U w N, metaBase + offCompItems U w N)` and dense items in
`[itemBase, itemBase + compactedItemWords U V w N m_cap)`. -/
structure CompOpFrame (metaBase itemBase U V w N m_cap : ℕ) (s s' : Memory.State) : Prop where
  frontier_eq : s'.frontier = s.frontier
  outside_eq : ∀ a,
    ¬(metaBase + offCompLM U w N ≤ a ∧ a < metaBase + offCompItems U w N) →
    ¬(itemBase ≤ a ∧ a < itemBase + compactedItemWords U V w N m_cap) →
    s'.mem a = s.mem a

theorem CompOpFrame.refl {metaBase itemBase U V w N m_cap : ℕ} (s : Memory.State) :
    CompOpFrame metaBase itemBase U V w N m_cap s s :=
  ⟨rfl, fun _ _ _ => rfl⟩

theorem CompOpFrame.trans {metaBase itemBase U V w N m_cap : ℕ} {s₁ s₂ s₃ : Memory.State}
    (h₁ : CompOpFrame metaBase itemBase U V w N m_cap s₁ s₂)
    (h₂ : CompOpFrame metaBase itemBase U V w N m_cap s₂ s₃) :
    CompOpFrame metaBase itemBase U V w N m_cap s₁ s₃ :=
  ⟨h₂.frontier_eq.trans h₁.frontier_eq,
    fun a hm hi => (h₂.outside_eq a hm hi).trans (h₁.outside_eq a hm hi)⟩

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

end
