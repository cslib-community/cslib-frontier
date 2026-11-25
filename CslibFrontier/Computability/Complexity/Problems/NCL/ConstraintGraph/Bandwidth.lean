/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Basic
public import Mathlib.Data.Nat.Dist
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

/-!
# Explicit bandwidth certificates for constraint graphs

A certificate orders every vertex and bounds the distance between any two occurrences of the
same edge. On a well-formed graph, these occurrences are its two endpoints.

## Main definitions

* `ConstraintGraph.BandwidthCertificate`: a vertex enumeration and a bound on edge spans.

## References

* [T. C. van der Zanden, *Parameterized Complexity of Graph Constraint Logic*]
  [VanDerZanden2015], Definition 4.
-/

public section

namespace Cslib.Complexity.NCL.ConstraintGraph

/-- An explicit vertex order in which every edge has span at most `bound`. -/
structure BandwidthCertificate {V E : Type*} (G : ConstraintGraph V E) (bound : ℕ) where
  /-- The number of vertices. -/
  size : ℕ
  /-- Each vertex appears exactly once in the order. -/
  order : V ≃ Fin size
  /-- Every pair of occurrences of an edge lies within the specified span. -/
  span : ∀ u v, ∀ p ∈ (G u).ports, ∀ r ∈ (G v).ports,
    p.port.edge = r.port.edge → Nat.dist (order u).val (order v).val ≤ bound

/-- A constraint graph admits a vertex order whose edges have span at most `bound`. -/
@[expose] def HasBandwidth {V E : Type*} (G : ConstraintGraph V E) (bound : ℕ) : Prop :=
  Nonempty (BandwidthCertificate G bound)

/-- Ordering equally sized blocks gives span below twice the block size when edges join
only vertices in the same or consecutive blocks. -/
@[expose] def BandwidthCertificate.ofBlocks {V E : Type*} {n k : ℕ} (G : ConstraintGraph V E)
    (blocks : V ≃ Fin n × Fin k)
    (hneighbours : ∀ u v, ∀ p ∈ (G u).ports, ∀ r ∈ (G v).ports,
      p.port.edge = r.port.edge → Nat.dist (blocks u).1.val (blocks v).1.val ≤ 1) :
    BandwidthCertificate G (2 * k - 1) where
  size := n * k
  order := blocks.trans finProdFinEquiv
  span u v p hp r hr he := by
    have hrows := hneighbours u v p hp r hr he
    have huv : (blocks u).1.val ≤ (blocks v).1.val + 1 := by
      simp only [Nat.dist] at hrows
      omega
    have hvu : (blocks v).1.val ≤ (blocks u).1.val + 1 := by
      simp only [Nat.dist] at hrows
      omega
    have hmuv := Nat.mul_le_mul_left k huv
    have hmvu := Nat.mul_le_mul_left k hvu
    have hu := (blocks u).2.isLt
    have hv := (blocks v).2.isLt
    change Nat.dist ((blocks u).2.val + k * (blocks u).1.val)
      ((blocks v).2.val + k * (blocks v).1.val) ≤ _
    simp only [Nat.dist, Nat.mul_add, Nat.mul_one] at *
    omega

private theorem dist_le_of_strictMono {m n : ℕ} (f : Fin m → Fin n) (hf : StrictMono f)
    (i j : Fin m) : Nat.dist i.val j.val ≤ Nat.dist (f i).val (f j).val := by
  have hle (i j : Fin m) (hij : i ≤ j) : j.val - i.val ≤ (f j).val - (f i).val := by
    have hsub : (Finset.Icc i j).image f ⊆ Finset.Icc (f i) (f j) := by
      rintro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_Icc.mpr ⟨hf.monotone (Finset.mem_Icc.mp hk).1,
        hf.monotone (Finset.mem_Icc.mp hk).2⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hf.injective, Fin.card_Icc, Fin.card_Icc] at hc
    have hfj := hf.monotone hij
    change i.val ≤ j.val at hij
    change (f i).val ≤ (f j).val at hfj
    omega
  rcases le_total i j with hij | hji
  · have h := hle i j hij
    have hfij := hf.monotone hij
    change i.val ≤ j.val at hij
    change (f i).val ≤ (f j).val at hfij
    simp only [Nat.dist]
    omega
  · have h := hle j i hji
    have hfji := hf.monotone hji
    change j.val ≤ i.val at hji
    change (f j).val ≤ (f i).val at hfji
    simp only [Nat.dist]
    omega

/-- Removing unused positions from an injective vertex layout cannot increase edge spans. -/
noncomputable def BandwidthCertificate.ofInjection {V E : Type*} [Fintype V] {n bound : ℕ}
    (G : ConstraintGraph V E) (index : V → Fin n) (hi : Function.Injective index)
    (hspan : ∀ u v, ∀ p ∈ (G u).ports, ∀ r ∈ (G v).ports,
      p.port.edge = r.port.edge → Nat.dist (index u).val (index v).val ≤ bound) :
    BandwidthCertificate G bound := by
  classical
  let s := Finset.univ.image index
  let e : V ≃ s := Equiv.ofBijective (fun v => ⟨index v, Finset.mem_image.mpr ⟨v, by simp, rfl⟩⟩)
    ⟨fun u v h => hi (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hx
      exact ⟨v, Subtype.ext hv⟩⟩
  let order := e.trans (s.orderIsoOfFin rfl).symm.toEquiv
  have ho (v : V) : s.orderEmbOfFin rfl (order v) = index v :=
    congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply (e v))
  refine ⟨s.card, order, ?_⟩
  intro u v p hp r hr he
  exact (dist_le_of_strictMono (s.orderEmbOfFin rfl) (s.orderEmbOfFin rfl).strictMono
    (order u) (order v)).trans (by simpa only [ho] using hspan u v p hp r hr he)

end Cslib.Complexity.NCL.ConstraintGraph
