/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.MinIsolation.Collisions
public import CslibFrontier.Foundations.Combinatorics.Digraph.Layered.MinIsolation

import Mathlib.Tactic.Ring

/-!
# All-pairs min-isolation from Hoza's weights

For a simple layered digraph on `n + 1` layers, a union bound over the endpoint
pairs and the two columns at their dominant internal layer bounds the number
of seeds that fail to min-isolate the graph. This proves the combinatorial
conclusion of [Hoza2026NLUL, Theorem 2.4].

## Main results

* `Cslib.Reachability.Hoza.card_nonisolatingSeeds_le`: the all-pairs union bound.
* `Cslib.Reachability.Hoza.exists_minIsolating_seed`: existence when the bound
  is smaller than the seed space.
-/

public section

namespace Cslib.Reachability.Hoza

open Finset LayeredDigraph

variable {V W : Type*} {ℓ n : ℕ}

open Classical in
private theorem card_equal_constrained_minima_le
    {G : LayeredDigraph V} [Finite V] (col : V → W) (code : W → Fin ℓ → Bool)
    {a b u v : V} {k : ℕ}
    (hk : k ∈ Icc (G.layer a + 1) (G.layer b - 1))
    (hmax : ∀ i ∈ Icc (G.layer a + 1) (G.layer b - 1),
      multiplicity 2 i ≤ multiplicity 2 k)
    (hu : G.layer u = k) (hv : G.layer v = k) :
    let weight seed (z : V) := vertexWeight code seed (G.layer z) (col z)
    (univ.filter fun seed =>
      ∃ p ∈ G.pathsThrough a b u, ∃ q ∈ G.pathsThrough a b v,
        IsMinOn (Path.internalWeight (weight seed)) (G.pathsThrough a b u) p ∧
        IsMinOn (Path.internalWeight (weight seed)) (G.pathsThrough a b v) q ∧
          p.internalWeight (weight seed) = q.internalWeight (weight seed)).card ≤
      2 ^ (ℓ - hammingDist (code (col u)) (code (col v))) := by
  classical
  let weight seed (z : V) := vertexWeight code seed (G.layer z) (col z)
  let layers := Icc (G.layer a + 1) (G.layer b - 1)
  let column (p : G.Path a b) (i : ℕ) := col (p.vertexAtLayer i)
  let paths (z : V) := (G.pathsThrough a b z).toFinite.toFinset
  have hmem {z : V} {p : G.Path a b} : p ∈ paths z ↔ p ∈ G.pathsThrough a b z := by
    simp [paths]
  have hcol (z : V) (hz : G.layer z = k) (p : G.Path a b) (hp : p ∈ paths z) :
      column p k = col z := by
    change col (p.vertexAtLayer k) = col z
    rw [p.vertexAtLayer_eq (p.mem_internalVertices_iff.mp (hmem.mp hp)).1 hz]
  have hweight (seed : Fin ℓ → Bool) (p : G.Path a b) :
      intervalWeight code seed layers (column p) = p.internalWeight (weight seed) := by
    rw [p.internalWeight_eq_sum_layers, intervalWeight]
    refine sum_congr rfl fun i hi => ?_
    have ⟨hi₁, hi₂⟩ := mem_Icc.mp hi
    obtain ⟨z, ⟨hz, hzi⟩, _⟩ := p.existsUnique_vertex (by omega : G.layer a ≤ i)
      (by omega : i ≤ G.layer b)
    change vertexWeight code seed i (col (p.vertexAtLayer i)) =
      vertexWeight code seed (G.layer (p.vertexAtLayer i)) (col (p.vertexAtLayer i))
    rw [p.vertexAtLayer_eq hz hzi, hzi]
  have hmin (seed : Fin ℓ → Bool) {z : V} {p : G.Path a b}
      (hne : (paths z).Nonempty) (hp : p ∈ G.pathsThrough a b z)
      (hpmin : IsMinOn (Path.internalWeight (weight seed)) (G.pathsThrough a b z) p) :
      minIntervalWeight code seed layers column (paths z) hne = p.internalWeight (weight seed) := by
    obtain ⟨q, hq, hqeq⟩ := exists_minIntervalWeight code seed layers column hne
    apply le_antisymm
    · rw [← hweight seed p]
      exact minIntervalWeight_le code seed layers column hne (hmem.mpr hp)
    · rw [← hqeq, hweight seed q]
      exact isMinOn_iff.mp hpmin q (hmem.mp hq)
  by_cases h : (paths u).Nonempty ∧ (paths v).Nonempty
  · refine le_trans (card_le_card ?_) (card_tyingSeeds_le code (by omega) hk hmax
      column h.1 h.2 (col u) (col v) (hcol u hu) (hcol v hv))
    intro seed hseed
    obtain ⟨p, hp, q, hq, hpmin, hqmin, heq⟩ := (mem_filter.mp hseed).2
    exact mem_filter.mpr ⟨mem_univ _, (hmin seed h.1 hp hpmin).trans
      (heq.trans (hmin seed h.2 hq hqmin).symm)⟩
  · refine (card_le_card (t := ∅) fun seed hs => ?_).trans (by simp)
    obtain ⟨p, hp, q, hq, _⟩ := (mem_filter.mp hs).2
    exact (h ⟨⟨p, hmem.mpr hp⟩, q, hmem.mpr hq⟩).elim

local notation "Vertex" => Fin (n + 1) × W

private noncomputable def dominantLayer (a b : Vertex) (h : a.1.val + 1 < b.1.val) : ℕ :=
  (Nat.existsUnique_max_multiplicity_two_Icc (a := a.1.val + 1) (b := b.1.val - 1)
    (by omega) (by omega)).exists.choose

private theorem dominantLayer_spec (a b : Vertex) (h : a.1.val + 1 < b.1.val) :
    dominantLayer a b h ∈ Icc (a.1.val + 1) (b.1.val - 1) ∧
      ∀ i ∈ Icc (a.1.val + 1) (b.1.val - 1),
        multiplicity 2 i ≤ multiplicity 2 (dominantLayer a b h) :=
  (Nat.existsUnique_max_multiplicity_two_Icc (a := a.1.val + 1) (b := b.1.val - 1)
    (by omega) (by omega)).exists.choose_spec

private noncomputable def dominantVertex (a b : Vertex) (h : a.1.val + 1 < b.1.val)
    (u : W) : Vertex :=
  (⟨dominantLayer a b h, by
    have hk := (mem_Icc.mp (dominantLayer_spec a b h).1).2
    have := b.1.isLt
    omega⟩, u)

open Classical in
/-- The number of bad seeds is at most the number of candidate collision events
times the bound on seeds for a single event. -/
theorem card_nonisolatingSeeds_le [Fintype W]
    (G : LayeredDigraph Vertex) (hlayer : ∀ v, G.layer v = v.1.val)
    (code : W → Fin ℓ → Bool) {d : ℕ}
    (hd : ∀ u v, u ≠ v → d ≤ hammingDist (code u) (code v)) :
    (univ.filter fun seed =>
      ¬G.IsMinIsolating (fun z => vertexWeight code seed (G.layer z) z.2)).card ≤
      ((n + 1) ^ 2 * Fintype.card W ^ 4) * 2 ^ (ℓ - d) := by
  classical
  let weight seed (z : Vertex) := vertexWeight code seed (G.layer z) z.2
  let events : (Vertex × Vertex) × (W × W) → Finset (Fin ℓ → Bool) :=
    fun ((a, b), (x, y)) =>
      if h : a.1.val + 1 < b.1.val ∧ x ≠ y then
        let u := dominantVertex a b h.1 x
        let v := dominantVertex a b h.1 y
        univ.filter fun seed =>
          ∃ p ∈ G.pathsThrough a b u, ∃ q ∈ G.pathsThrough a b v,
            IsMinOn (Path.internalWeight (weight seed)) (G.pathsThrough a b u) p ∧
            IsMinOn (Path.internalWeight (weight seed)) (G.pathsThrough a b v) q ∧
              p.internalWeight (weight seed) = q.internalWeight (weight seed)
      else ∅
  have hevent (t : (Vertex × Vertex) × (W × W)) : (events t).card ≤ 2 ^ (ℓ - d) := by
    obtain ⟨⟨a, b⟩, x, y⟩ := t
    by_cases ht : a.1.val + 1 < b.1.val ∧ x ≠ y
    · dsimp only [events]
      rw [dite_eq_left ht]
      have hs := dominantLayer_spec a b ht.1
      have hk : dominantLayer a b ht.1 ∈ Icc (G.layer a + 1) (G.layer b - 1) := by
        simpa only [hlayer] using hs.1
      have hmax : ∀ i ∈ Icc (G.layer a + 1) (G.layer b - 1),
          multiplicity 2 i ≤ multiplicity 2 (dominantLayer a b ht.1) := by
        simpa only [hlayer] using hs.2
      exact (card_equal_constrained_minima_le Prod.snd code hk hmax (hlayer _) (hlayer _)).trans
        (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_left (hd x y ht.2) ℓ))
    · simp [events, ht]
  have hcover : (univ.filter fun seed => ¬G.IsMinIsolating (weight seed)) ⊆
      univ.biUnion events := by
    intro seed hseed
    by_contra hout
    apply (mem_filter.mp hseed).2
    apply G.isMinIsolating_of_separated (weight seed)
    intro a b hab
    have h : a.1.val + 1 < b.1.val := by simpa only [hlayer] using hab
    have hk := mem_Icc.mp (dominantLayer_spec a b h).1
    refine ⟨dominantLayer a b h, by rw [hlayer]; omega, by rw [hlayer]; omega, ?_⟩
    intro u v hu hv hne p q hp hq hpmin hqmin heq
    have huv : u.2 ≠ v.2 := fun hcol =>
      hne (Prod.ext (Fin.ext ((hlayer u).symm.trans (hu.trans (hv.symm.trans (hlayer v))))) hcol)
    have ht : a.1.val + 1 < b.1.val ∧ u.2 ≠ v.2 := ⟨h, huv⟩
    have hue : dominantVertex a b h u.2 = u :=
      Prod.ext (Fin.ext (hu.symm.trans (hlayer u))) rfl
    have hve : dominantVertex a b h v.2 = v :=
      Prod.ext (Fin.ext (hv.symm.trans (hlayer v))) rfl
    apply hout
    refine mem_biUnion.mpr ⟨((a, b), (u.2, v.2)), mem_univ _, ?_⟩
    simp only [events, dite_eq_left ht, hue, hve]
    exact mem_filter.mpr ⟨mem_univ _, p, hp, q, hq, hpmin, hqmin, heq⟩
  calc
    _ ≤ (univ.biUnion events).card := card_le_card hcover
    _ ≤ ∑ t, (events t).card := card_biUnion_le
    _ ≤ ∑ _ : (Vertex × Vertex) × (W × W), 2 ^ (ℓ - d) := sum_le_sum fun t _ => hevent t
    _ = _ := by
      simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
      ring

/-- A seed min-isolates the graph whenever the collision sum is smaller than the seed space. -/
theorem exists_minIsolating_seed [Fintype W]
    (G : LayeredDigraph Vertex) (hlayer : ∀ v, G.layer v = v.1.val)
    (code : W → Fin ℓ → Bool) {d : ℕ}
    (hd : ∀ u v, u ≠ v → d ≤ hammingDist (code u) (code v))
    (hsize : ((n + 1) ^ 2 * Fintype.card W ^ 4) * 2 ^ (ℓ - d) < 2 ^ ℓ) :
    ∃ seed, G.IsMinIsolating (fun z => vertexWeight code seed (G.layer z) z.2) := by
  classical
  by_contra hne
  have h := (card_nonisolatingSeeds_le G hlayer code hd).trans_lt hsize
  simp only [not_exists] at hne
  simp [hne] at h

end Cslib.Reachability.Hoza
