/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Bandwidth
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Bandwidth of a supplied row-sorted vertex order

Every row contains at most `B` vertices, and endpoints of the same edge are at most `d` rows
apart. Any supplied vertex enumeration sorted by row has bandwidth at most `(d + 1) * B - 1`.
The certificate retains that enumeration exactly.

## Main definitions

* `ConstraintGraph.BandwidthCertificate.ofRowOrder`: certify the supplied row-sorted order.
-/

public section

namespace Cslib.Complexity.NCL.ConstraintGraph

open scoped BigOperators

private theorem row_interval_card_le {n B d : ℕ} (row : Fin n → ℕ) (hs : Monotone row)
    (hB : ∀ r, Nat.card {i // row i = r} ≤ B) (i j : Fin n)
    (hd : Nat.dist (row i) (row j) ≤ d) : j.val + 1 - i.val ≤ (d + 1) * B := by
  classical
  have hj : row j ≤ row i + d :=
    (Nat.dist_tri_right (row i) (row j)).trans (Nat.add_le_add_left hd (row i))
  have hm : (↑(Finset.Icc i j) : Set (Fin n)).MapsTo row (↑(Finset.Icc (row i) (row i + d))) := by
    intro k hk
    obtain ⟨hik, hkj⟩ := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨hs hik, (hs hkj).trans hj⟩
  have hf (r : ℕ) : ((Finset.Icc i j).filter (fun k => row k = r)).card ≤ B := by
    have hall : (Finset.univ.filter (fun k => row k = r)).card ≤ B := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hB r
    exact (Finset.card_le_card
      (Finset.filter_subset_filter _ (Finset.subset_univ (Finset.Icc i j)))).trans hall
  calc
    j.val + 1 - i.val = (Finset.Icc i j).card := (Fin.card_Icc i j).symm
    _ = ∑ r ∈ Finset.Icc (row i) (row i + d),
        ((Finset.Icc i j).filter (fun k => row k = r)).card :=
      Finset.card_eq_sum_card_fiberwise hm
    _ ≤ ∑ _r ∈ Finset.Icc (row i) (row i + d), B := Finset.sum_le_sum (fun r _ => hf r)
    _ = (d + 1) * B := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_assoc,
        Nat.add_sub_cancel_left, Nat.cast_id]

private theorem rank_dist_le {n B d : ℕ} (row : Fin n → ℕ) (hs : Monotone row)
    (hB : ∀ r, Nat.card {i // row i = r} ≤ B) (i j : Fin n)
    (hd : Nat.dist (row i) (row j) ≤ d) : Nat.dist i.val j.val ≤ (d + 1) * B - 1 := by
  have hij := row_interval_card_le row hs hB i j hd
  have hji := row_interval_card_le row hs hB j i (by simpa only [Nat.dist_comm] using hd)
  simp only [Nat.dist]
  omega

/-- A row-sorted supplied order has bandwidth below the capacity of `d + 1` consecutive rows. -/
@[expose] def BandwidthCertificate.ofRowOrder {V E : Type*} {n B d : ℕ}
    (G : ConstraintGraph V E) (order : V ≃ Fin n) (row : V → ℕ)
    (hB : ∀ r, Nat.card {v // row v = r} ≤ B)
    (hs : Monotone (fun i => row (order.symm i)))
    (hneighbours : ∀ u v, ∀ p ∈ (G u).ports, ∀ q ∈ (G v).ports,
      p.port.edge = q.port.edge → Nat.dist (row u) (row v) ≤ d) :
    BandwidthCertificate G ((d + 1) * B - 1) where
  size := n
  order := order
  span u v p hp q hq he := by
    have hb (r : ℕ) : Nat.card {i : Fin n // row (order.symm i) = r} ≤ B := by
      have hc : Nat.card {i : Fin n // row (order.symm i) = r} =
          Nat.card {v // row v = r} :=
        Nat.card_congr (order.symm.subtypeEquiv (q := fun v => row v = r) (fun _ => Iff.rfl))
      exact hc.trans_le (hB r)
    apply rank_dist_le (fun i => row (order.symm i)) hs hb (order u) (order v)
    simpa only [Equiv.symm_apply_apply] using hneighbours u v p hp q hq he

end Cslib.Complexity.NCL.ConstraintGraph
