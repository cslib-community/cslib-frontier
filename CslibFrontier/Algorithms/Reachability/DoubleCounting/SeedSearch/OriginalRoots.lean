/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting.SeedSearch
public import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator
public import CslibFrontier.Algorithms.Reachability.MinIsolation.Subdivision

/-!
# Ordered isolation-seed search from the original roots

The source list contains the entry of each original vertex's subdivision chain. Auxiliary
vertices may be reached by a scan, but are not added as sources. Hoza's seed-existence theorem
and the subdivision scan criterion give a passing seed for the ordered monadic search.

## Main results

* `runGeneratedSeedSearch_correct`: under the exact controller contract, the ordered search
  has one outcome, selects the least min-isolating seed, and returns the reachability answer
  in its indexed subdivision. Native loop and controller composition remain separate.
-/

public section

namespace Cslib.Reachability.Hoza

open Code.JustesenFamily DoubleCounting LayeredDigraph.Subdivision

variable {w h bound N : ℕ}

/-- The indexed roots in row-major order, with one entry for each original vertex. -/
def originalRootIDs (index : Vertex (Fin (h + 1) × Fin w) bound ≃ Fin N) : List (Fin N) :=
  List.ofFn fun i : Fin ((h + 1) * w) => index (root bound (finProdFinEquiv.symm i))

/-- Membership means being the root of an original vertex. -/
theorem mem_originalRootIDs_iff (index : Vertex (Fin (h + 1) × Fin w) bound ≃ Fin N)
    (i : Fin N) : i ∈ originalRootIDs index ↔ ∃ v, i = index (root bound v) := by
  rw [originalRootIDs, List.mem_ofFn]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨finProdFinEquiv.symm j, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨finProdFinEquiv v, by rw [Equiv.symm_apply_apply]⟩

/-- The adjacency relation searched at a seed, with vertices given by their subdivision IDs. -/
abbrev generatedSubdivisionAdj (G : LayeredDigraph (Fin (h + 1) × Fin w))
    (index : Vertex (Fin (h + 1) × Fin w) bound ≃ Fin N)
    (seed : Fin (codeLength w h) → Bool) (a b : Fin N) : Prop :=
  (graph G (generatedWeight seed) bound).Adj (index.symm a) (index.symm b)

private theorem root_passes_iff (G : LayeredDigraph (Fin (h + 1) × Fin w))
    (index : Vertex (Fin (h + 1) × Fin w) bound ≃ Fin N)
    (seed : Fin (codeLength w h) → Bool) (source : Fin (h + 1) × Fin w)
    (hb : ∀ v, generatedWeight seed v ≤ bound) :
    ((∀ j, ∃! p, Passes (generatedSubdivisionAdj G index seed) (index (root bound source)) j p) ∧
      ∀ s ∈ originalRootIDs index, ∀ j, ∃! p, Passes (generatedSubdivisionAdj G index seed) s j p)
      ↔ G.IsMinIsolating (generatedWeight seed) := by
  have hi (v : Fin (h + 1) × Fin w) (j : ℕ)
      (hs : G.IsMinIsolating (generatedWeight seed)) :
      ∃! p, Passes (generatedSubdivisionAdj G index seed) (index (root bound v)) j p :=
    (existsUnique_passes_reindex index _ _ j).mp (existsUnique_passes_of_isMinIsolating hb hs v j)
  refine ⟨fun hs => ?_, fun hs => ⟨fun j => hi source j hs, ?_⟩⟩
  · apply (isMinIsolating_iff_indexedPasses index hb (k := N) (by simp)).mpr
    intro v
    exact hs.2 _ ((mem_originalRootIDs_iff index _).mpr ⟨v, rfl⟩) N
  · intro s hmem j
    obtain ⟨v, rfl⟩ := (mem_originalRootIDs_iff index s).mp hmem
    exact hi v j hs

/-- Run the ordered search from the designated root and test all original roots. The
exact controller contract gives one outcome, with the least min-isolating seed and its
reachability answer. This applies in particular to the multiplicity-sensitive list monad. -/
theorem runGeneratedSeedSearch_correct {m : Type → Type} [AlternativeMonad m] [LawfulMonad m]
    (G : LayeredDigraph (Fin (h + 1) × Fin w)) (hlayer : ∀ v, G.layer v = v.1.val)
    (index : Vertex (Fin (h + 1) × Fin w) bound ≃ Fin N)
    (hb : ∀ (seed : Fin (codeLength w h) → Bool) (v : Fin (h + 1) × Fin w),
      generatedWeight seed v ≤ bound)
    (source target : Fin (h + 1) × Fin w)
    (controller : (Fin (codeLength w h) → Bool) → Fin N → m (Option ControllerVerdict))
    (hc : ∀ seed s, ∃ verdict, controller seed s = pure (some verdict) ∧
      match verdict with
      | .bad j => ¬ ∃! p, Passes (generatedSubdivisionAdj G index seed) s j p
      | .decided b => (∀ j, ∃! p, Passes (generatedSubdivisionAdj G index seed) s j p) ∧
          (b = true ↔ Relation.ReflTransGen (generatedSubdivisionAdj G index seed) s
            (index (root bound target)))) :
    ∃ result, runSeedSearch controller (originalRootIDs index) (index (root bound source)) =
        pure (some result) ∧
      G.IsMinIsolating (generatedWeight ((BitString.equivFin _).symm result.seed)) ∧
      (∀ i < result.seed, ¬ G.IsMinIsolating (generatedWeight ((BitString.equivFin _).symm i))) ∧
      (result.reachable = true ↔ Relation.ReflTransGen
        (generatedSubdivisionAdj G index ((BitString.equivFin _).symm result.seed))
        (index (root bound source)) (index (root bound target))) := by
  have hpass seed := root_passes_iff G index seed source (hb seed)
  obtain ⟨seed, hseed⟩ := exists_generatedWeight_isMinIsolating G hlayer
  obtain ⟨result, hrun, hgood, hleast, hreach⟩ :=
    runSeedSearch_correct (originalRootIDs index) hc ⟨seed, (hpass seed).mpr hseed⟩
  exact ⟨result, hrun, (hpass _).mp hgood, fun i hi hs => hleast i hi ((hpass _).mpr hs), hreach⟩

end Cslib.Reachability.Hoza
