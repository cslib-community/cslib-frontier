/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PlantedClique.Model
public import CslibFrontier.Probability.PMF.Uniform
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.CommonNeighborhood
public import Mathlib.Data.Finset.Sort

/-!
# Exposing the common neighborhood of a planted seed

The seed-touching edges determine the common neighborhood. All other edges may be resampled
independently without changing it. Increasing enumeration of the neighborhood identifies the
remaining graph with a fresh planted-clique experiment on the smaller vertex set.

The statements use an explicit exposure coupling, so no conditioning on a positive-probability
event or unproved independence hypothesis is needed.

## References

* [N. Alon, M. Krivelevich, B. Sudakov, *Finding a large hidden clique in a random
  graph*][AlonKrivelevichSudakov1998], Section 2.3, the seed-edge exposure argument.
-/

public section

namespace Cslib.Probability.PlantedClique

open Cslib.Probability.PMF

/-- Restriction along an increasing vertex embedding preserves the planted-graph sampler. -/
theorem sample_comap_orderEmbedding {n m : ℕ} (S : Finset (Fin n)) (ω : Coins n)
    (e : Fin m ↪o Fin n) :
    (sample S ω).comap e =
      sample (Finset.univ.filter fun i => e i ∈ S)
        (fun p => ω (e p.1, e p.2)) := by
  ext i j
  change (e i ≠ e j ∧ ((e i ∈ S ∧ e j ∈ S) ∨
    ω (min (e i) (e j), max (e i) (e j)) = true)) ↔ _
  simp only [sample, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq,
    e.injective.eq_iff, e.monotone.map_min, e.monotone.map_max]

/-- A fixed induced subgraph of a planted graph has the planted law on the retained vertices. -/
theorem uniform_sample_comap_orderEmbedding {n m : ℕ} (S : Finset (Fin n))
    (e : Fin m ↪o Fin n) :
    (PMF.uniformOfFintype (Coins n)).map (fun ω => (sample S ω).comap e) =
      (PMF.uniformOfFintype (Coins m)).map
        (sample (Finset.univ.filter fun i => e i ∈ S)) := by
  let ep : Fin m × Fin m ↪ Fin n × Fin n := e.toEmbedding.prodMap e.toEmbedding
  rw [← uniformOfFintype_pi_map_comp_embedding (α := Bool) ep, PMF.map_comp]
  congr 1
  funext ω
  exact sample_comap_orderEmbedding S ω e

/-- Retain the edges touching `T` from `exposed`, and use `fresh` on every other coordinate. -/
@[expose] def resampleOffSeed {n : ℕ} (T : Finset (Fin n))
    (exposed fresh : Coins n) : Coins n :=
  fun p => if p.1 ∈ T ∨ p.2 ∈ T then exposed p else fresh p

/-- Resampling all coordinates away from a seed preserves the uniform coin law, even inside
an arbitrary subsequent randomized experiment. -/
theorem uniform_bind_bind_resampleOffSeed {n : ℕ} {α : Type*} (T : Finset (Fin n))
    (f : Coins n → PMF α) :
    ((PMF.uniformOfFintype (Coins n)).bind fun ω =>
      (PMF.uniformOfFintype (Coins n)).bind fun η => f (resampleOffSeed T ω η)) =
    (PMF.uniformOfFintype (Coins n)).bind f := by
  let swap : Coins n × Coins n → Coins n × Coins n :=
    fun p => (resampleOffSeed T p.1 p.2, resampleOffSeed T p.2 p.1)
  have hs : Function.Involutive swap := by
    intro p
    ext q <;> simp only [swap, resampleOffSeed] <;> split_ifs <;> rfl
  exact uniformOfFintype_bind_bind_fst_equiv hs.toPerm f

/-- Exposing the seed-touching coordinates fixes the common neighborhood: subsequent fresh
coins cannot change which vertices survive. -/
theorem commonNeighborhood_resampleOffSeed {n : ℕ} (S T : Finset (Fin n))
    (ω η : Coins n) :
    (sample S (resampleOffSeed T ω η)).commonNeighborhood T =
      (sample S ω).commonNeighborhood T := by
  ext v
  simp only [SimpleGraph.mem_commonNeighborhood]
  refine and_congr_right fun _ => forall₂_congr fun t ht => ?_
  have hp : min t v ∈ T ∨ max t v ∈ T := by
    rcases le_total t v with h | h
    · exact Or.inl (by simpa only [min_eq_left h] using ht)
    · exact Or.inr (by simpa only [max_eq_left h] using ht)
  simp [sample, resampleOffSeed, hp]

/-- Away from the exposed seed, the graph reads only the fresh coins. -/
theorem sample_resampleOffSeed_comap {n m : ℕ} (S T : Finset (Fin n)) (ω η : Coins n)
    (e : Fin m ↪o Fin n) (he : ∀ i, e i ∉ T) :
    (sample S (resampleOffSeed T ω η)).comap e =
      sample (Finset.univ.filter fun i => e i ∈ S) (fun p => η (e p.1, e p.2)) := by
  rw [sample_comap_orderEmbedding]
  congr 1
  funext p
  simp [resampleOffSeed, he]

/-- A fixed increasing enumeration of vertices away from the exposed seed has a fresh planted
graph law. This version accepts any enumeration, including an executable list-based one. -/
theorem uniform_sample_resampleOffSeed_comap {n m : ℕ} (S T : Finset (Fin n)) (ω : Coins n)
    (e : Fin m ↪o Fin n) (he : ∀ i, e i ∉ T) :
    (PMF.uniformOfFintype (Coins n)).map
        (fun η => (sample S (resampleOffSeed T ω η)).comap e) =
      (PMF.uniformOfFintype (Coins m)).map
        (sample (Finset.univ.filter fun i => e i ∈ S)) := by
  let ep : Fin m × Fin m ↪ Fin n × Fin n := e.toEmbedding.prodMap e.toEmbedding
  rw [← uniformOfFintype_pi_map_comp_embedding (α := Bool) ep, PMF.map_comp]
  congr 1
  funext η
  exact sample_resampleOffSeed_comap S T ω η e he

/-- After any fixed exposure, the graph induced on its common neighborhood is exactly a fresh
planted-clique graph, with its planted vertices transported through the increasing enumeration. -/
theorem uniform_sample_commonNeighborhood {n : ℕ} (S T : Finset (Fin n)) (ω : Coins n) :
    let U := (sample S ω).commonNeighborhood T
    let e := U.orderEmbOfFin rfl
    (PMF.uniformOfFintype (Coins n)).map
        (fun η => (sample S (resampleOffSeed T ω η)).comap e) =
      (PMF.uniformOfFintype (Coins U.card)).map
        (sample (Finset.univ.filter fun i => e i ∈ S)) := by
  intro U e
  apply uniform_sample_resampleOffSeed_comap
  intro i
  exact (sample S ω).not_mem_of_mem_commonNeighborhood (U.orderEmbOfFin_mem rfl i)

/-- Any injective enumeration of the common neighborhood transports exactly `|S| - |T|`
planted vertices. This permits both canonical and executable increasing enumerations. -/
theorem card_filter_commonNeighborhood {n m : ℕ} (S T : Finset (Fin n)) (hT : T ⊆ S)
    (ω : Coins n) (e : Fin m ↪ Fin n)
    (he : Finset.univ.image e = (sample S ω).commonNeighborhood T) :
    (Finset.univ.filter fun i => e i ∈ S).card = S.card - T.card := by
  rw [← Finset.card_sdiff_of_subset hT]
  have hclique : (sample S ω).IsClique (S : Set (Fin n)) :=
    fun _ hi _ hj hij => sample_adj_of_mem S ω hi hj hij
  change (Finset.univ.filter ((· ∈ S) ∘ e)).card = _
  rw [← Finset.card_map e, ← Finset.filter_map, Finset.map_eq_image, he]
  congr 1
  ext v
  rw [Finset.mem_filter, Finset.mem_sdiff]
  exact ⟨fun ⟨hv, hvS⟩ => ⟨hvS, (sample S ω).not_mem_of_mem_commonNeighborhood hv⟩,
    fun hv => ⟨(sample S ω).sdiff_subset_commonNeighborhood hT hclique
      (Finset.mem_sdiff.mpr hv), hv.1⟩⟩

end Cslib.Probability.PlantedClique
