/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Image collisions in query caches

`Cslib.RandomOracle.HasImageCollision` records two distinct keys in an association list whose
images under a map agree. It is decidable from equality of keys and images, and it persists when
the cache grows.
-/

public section

namespace Cslib.RandomOracle

variable {M Y Z : Type}

/-- Two distinct keys of the cache have the same image under `φ`. Unlike
`RandomOracle.HasOutputCollision` (which records a collision between two cached answers),
`HasImageCollision` records a collision of cached queries under `φ` and does not involve the
answers. -/
@[expose] def HasImageCollision (φ : M → Y) (cache : List (M × Z)) : Prop :=
  ∃ e ∈ cache, ∃ e' ∈ cache, e.1 ≠ e'.1 ∧ φ e.1 = φ e'.1

instance [DecidableEq M] [DecidableEq Y] (φ : M → Y) (cache : List (M × Z)) :
    Decidable (HasImageCollision φ cache) := by
  unfold HasImageCollision
  infer_instance

/-- `HasImageCollision` depends only on the list of cached queries. -/
theorem hasImageCollision_iff (φ : M → Y) (cache : List (M × Z)) :
    HasImageCollision φ cache ↔
      ∃ m ∈ cache.map Prod.fst, ∃ m' ∈ cache.map Prod.fst, m ≠ m' ∧ φ m = φ m' := by
  simp only [HasImageCollision, List.mem_map]
  constructor
  · rintro ⟨e, he, e', he', h1, h2⟩
    exact ⟨e.1, ⟨e, he, rfl⟩, e'.1, ⟨e', he', rfl⟩, h1, h2⟩
  · rintro ⟨m, ⟨e, he, rfl⟩, m', ⟨e', he', rfl⟩, h1, h2⟩
    exact ⟨e, he, e', he', h1, h2⟩

/-- A collision persists after adding entries to the cache. -/
theorem HasImageCollision.mono {φ : M → Y} {s t : List (M × Z)} (hst : s ⊆ t)
    (h : HasImageCollision φ s) : HasImageCollision φ t :=
  let ⟨e, he, e', he', h1, h2⟩ := h
  ⟨e, hst he, e', hst he', h1, h2⟩

end Cslib.RandomOracle
