/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.PlantedClique.Encoding

/-!
# Representing semantic planted-clique inputs and answers

`RecoveryInput.ofGraph` presents a finite simple graph by its full row-major adjacency word,
together with its vertex count and the public target size. Decoding this presentation returns
the original graph. This describes which input words represent a mathematical graph; it is not
a sampling primitive or a computation performed by the recovery program.

The program returns a list of natural vertex identifiers. `vertexSet` interprets those identifiers
in the graph's finite vertex type. When the list's finite set is exactly the image of a vertex
set under `Fin.val`, this interpretation recovers that set. The recovery program's correctness
theorem establishes that image equality for the actual list it computes and writes.
-/

public section

namespace Cslib.Algorithms.PlantedClique

namespace RecoveryInput

open scoped Classical in
/-- Present a graph by all `n²` adjacency bits in row-major order and its public target size. -/
@[expose] noncomputable def ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : RecoveryInput where
  vertexCount := n
  cliqueSize := k
  adjacencyBits := (DenseGraphInput.ofGraph G).adjacencyBits

/-- The canonical dense presentation decodes to the original graph. -/
@[simp] theorem graph_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    (ofGraph G k).graph = G := by
  exact DenseGraphInput.graph_ofGraph G

/-- The canonical input uses `n²` raw adjacency bits and two framed unary parameters. -/
theorem length_encRecoveryInput_ofGraph {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    (encRecoveryInput (ofGraph G k)).length = n * n + 2 * n + 2 * k + 2 := by
  simp [encRecoveryInput_apply, ofGraph, DenseGraphInput.ofGraph, List.length_flatMap]
  omega

end RecoveryInput

/-- Interpret a list of natural identifiers as the set of vertices it names in `Fin n`. -/
@[expose] def vertexSet (n : ℕ) (vertices : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun vertex => vertex.val ∈ vertices

/-- Interpreting a vertex list and forgetting the bounded-index proofs keeps exactly the
identifiers below the declared dimension, with duplicates removed. -/
theorem image_vertexSet (n : ℕ) (vertices : List ℕ) :
    (vertexSet n vertices).image Fin.val = vertices.toFinset.filter (· < n) := by
  ext i
  simp only [Finset.mem_image, vertexSet, Finset.mem_filter, Finset.mem_univ, true_and,
    List.mem_toFinset]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨hv, v.isLt⟩
  · rintro ⟨hi, hin⟩
    exact ⟨⟨i, hin⟩, hi, rfl⟩

/-- A bounded duplicate-free vertex list and its interpreted set have the same size. -/
theorem card_vertexSet_of_nodup {n : ℕ} (vertices : List ℕ) (hnodup : vertices.Nodup)
    (hbound : ∀ i ∈ vertices, i < n) : (vertexSet n vertices).card = vertices.length := by
  have himage : (vertexSet n vertices).image Fin.val = vertices.toFinset := by
    rw [image_vertexSet, Finset.filter_eq_self]
    simpa only [List.mem_toFinset] using hbound
  have hcard := Finset.card_image_of_injective (vertexSet n vertices) Fin.val_injective
  rw [himage, List.toFinset_card_of_nodup hnodup] at hcard
  exact hcard.symm

/-- A list representing exactly the natural identifiers of `S` is interpreted as `S`. -/
theorem vertexSet_eq_of_toFinset_eq_image {n : ℕ} {vertices : List ℕ} {S : Finset (Fin n)}
    (h : vertices.toFinset = S.image Fin.val) : vertexSet n vertices = S := by
  ext vertex
  simp only [vertexSet, Finset.mem_filter, Finset.mem_univ, true_and,
    ← List.mem_toFinset, h, Finset.mem_image, Fin.val_inj]
  simp

end Cslib.Algorithms.PlantedClique
