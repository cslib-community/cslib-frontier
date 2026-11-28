/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Fin.Tuple

/-!
# Finite embeddings with prescribed endpoints

This module constructs embeddings between finite ordinals that send one or two selected source
points to selected target points. The endpoint equations let machine constructions choose work
tapes without classical choice or existential extraction.

## Main definitions

* `Fin.embeddingAt`: place one source point at a target point.
* `Fin.embeddingAt₂`: place two distinct source points at two distinct target points.

## Main results

* `Fin.embeddingAt_source`, `Fin.embeddingAt₂_first`, `Fin.embeddingAt₂_second`: the selected
  endpoints have their prescribed images.
* `Fin.exists_embedding_eq`, `Fin.exists_embedding_eq₂`: existential forms for callers that do
  not need to retain the concrete embedding.
-/

@[expose] public section

namespace Fin

/-- Embed `Fin m` in `Fin K`, sending `source` to `target`. -/
def embeddingAt {m K : ℕ} (h : m ≤ K) (source : Fin m) (target : Fin K) : Fin m ↪ Fin K :=
  (castLEEmb h).trans (Equiv.swap (castLE h source) target).toEmbedding

/-- The selected source has its prescribed image. -/
@[simp] theorem embeddingAt_source {m K : ℕ} (h : m ≤ K) (source : Fin m)
    (target : Fin K) : embeddingAt h source target source = target := by
  simp [embeddingAt]

/-- Embed `Fin m` in `Fin K`, sending two distinct source points to two distinct targets. -/
def embeddingAt₂ {m K : ℕ} (h : m ≤ K) {first second : Fin m}
    (_hSource : first ≠ second) {firstTarget secondTarget : Fin K}
    (_hTarget : firstTarget ≠ secondTarget) : Fin m ↪ Fin K :=
  let placedFirst := embeddingAt h first firstTarget
  placedFirst.trans (Equiv.swap (placedFirst second) secondTarget).toEmbedding

/-- The first selected source has its prescribed image. -/
@[simp] theorem embeddingAt₂_first {m K : ℕ} (h : m ≤ K) {first second : Fin m}
    (hSource : first ≠ second) {firstTarget secondTarget : Fin K}
    (hTarget : firstTarget ≠ secondTarget) :
    embeddingAt₂ h hSource hTarget first = firstTarget := by
  let placedFirst := embeddingAt h first firstTarget
  have hSecond : placedFirst second ≠ firstTarget := fun heq =>
    hSource (placedFirst.injective
      (heq.trans (embeddingAt_source h first firstTarget).symm)).symm
  simp only [embeddingAt₂, Function.Embedding.trans_apply]
  rw [embeddingAt_source]
  exact Equiv.swap_apply_of_ne_of_ne hSecond.symm hTarget

/-- The second selected source has its prescribed image. -/
@[simp] theorem embeddingAt₂_second {m K : ℕ} (h : m ≤ K) {first second : Fin m}
    (hSource : first ≠ second) {firstTarget secondTarget : Fin K}
    (hTarget : firstTarget ≠ secondTarget) :
    embeddingAt₂ h hSource hTarget second = secondTarget := by
  simp [embeddingAt₂]

/-- An embedding into a larger finite ordinal can place one selected source at any target. -/
theorem exists_embedding_eq {m K : ℕ} (h : m ≤ K) (source : Fin m) (target : Fin K) :
    ∃ embedding : Fin m ↪ Fin K, embedding source = target :=
  ⟨embeddingAt h source target, embeddingAt_source h source target⟩

/-- An embedding into a larger finite ordinal can place two distinct selected sources at any two
distinct targets. -/
theorem exists_embedding_eq₂ {m K : ℕ} (h : m ≤ K) {i o : Fin m}
    (hio : i ≠ o) {a b : Fin K} (hab : a ≠ b) :
    ∃ embedding : Fin m ↪ Fin K,
      embedding i = a ∧ embedding o = b :=
  ⟨embeddingAt₂ h hio hab, embeddingAt₂_first h hio hab,
    embeddingAt₂_second h hio hab⟩

end Fin
