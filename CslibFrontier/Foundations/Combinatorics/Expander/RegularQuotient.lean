/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Basic
import CslibFrontier.Foundations.Data.Nat.Card
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Data.Fintype.EquivFin

/-!
# Placing a bounded-degree multigraph on fewer sites

At most `q` vertices occupy each site and each vertex has at most `k` incident edge ends.
Packing the incident ends in `q*k` slots per site and fixing unused slots in the rotation map
gives a regular multigraph. Every original edge occurs with its original orientation.
A partial placement of terminals can be completed by distributing the remaining vertices
with at most one more than the average number of extra vertices per site.
-/

public section

open Finset

namespace Cslib.RotationMap

private theorem exists_fiber_embedding {T S : Type*} [Finite T] (f : T → S)
    {q : ℕ} (hq : ∀ s, Nat.card {t // f t = s} ≤ q) :
    ∃ j : T ↪ S × Fin q, ∀ t, (j t).1 = f t := by
  classical
  let (s : S) := Fintype.ofFinite {t // f t = s}
  have hj (s : S) : Nonempty ({t // f t = s} ↪ Fin q) :=
    Function.Embedding.nonempty_of_card_le (by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hq s)
  let j := (Equiv.sigmaFiberEquiv f).symm.toEmbedding.trans <|
    (Function.Embedding.sigmaMap (Function.Embedding.refl S) (fun s => (hj s).some)).trans
      (Equiv.sigmaEquivProd S (Fin q)).toEmbedding
  exact ⟨j, fun _ => rfl⟩

/-- A multigraph of incidence degree at most `k`, placed with at most `q` vertices at each
site, gives a regular walk with `q*k` darts at each site. Every original edge occurs among
the darts in its original orientation, even when several vertices have the same site. -/
theorem exists_regular_of_fiber_bounds {V E S : Type*} [Finite V] [Fintype E] [Fintype S]
    (a b : E → V) (place : V → S) {q k : ℕ}
    (hlocal : ∀ v, Nat.card {t : E ⊕ E // Sum.elim a b t = v} ≤ k)
    (hsite : ∀ s, Nat.card {v // place v = s} ≤ q) :
    ∃ G : RotationMap S (Fin q × Fin k), ∀ w : S → S → ℝ, (∀ x y, 0 ≤ w x y) →
      (∑ e, w (place (a e)) (place (b e))) ≤ ∑ p : S × (Fin q × Fin k), w p.1 (G.rot p).1 := by
  classical
  obtain ⟨slots, hslots⟩ := exists_fiber_embedding _ hlocal
  obtain ⟨sites, hsites⟩ := exists_fiber_embedding _ hsite
  let j := slots.trans ((sites.prodMap (Function.Embedding.refl (Fin k))).trans
    (Equiv.prodAssoc S (Fin q) (Fin k)).toEmbedding)
  have hj (t : E ⊕ E) : (j t).1 = place (Sum.elim a b t) :=
    (hsites (slots t).1).trans (congrArg place (hslots t))
  let reverse : Equiv.Perm (E ⊕ E) := Equiv.sumComm E E
  let rot := reverse.viaEmbedding j
  have hjrot (t : E ⊕ E) : rot (j t) = j (reverse t) := reverse.viaEmbedding_apply j t
  have invol : Function.Involutive rot := by
    intro p
    by_cases hp : p ∈ Set.range j
    · obtain ⟨t, rfl⟩ := hp
      rw [hjrot, hjrot]
      cases t <;> rfl
    · rw [show rot p = p from reverse.viaEmbedding_apply_of_notMem j p hp]
      exact reverse.viaEmbedding_apply_of_notMem j p hp
  refine ⟨⟨rot, invol⟩, fun w hw => ?_⟩
  let start : E ↪ S × (Fin q × Fin k) := Function.Embedding.inl.trans j
  let cost (p : S × (Fin q × Fin k)) := w p.1 (rot p).1
  have hcost (e : E) : cost (start e) = w (place (a e)) (place (b e)) := by
    change w (j (.inl e)).1 (rot (j (.inl e))).1 = _
    rw [hjrot, hj, hj]
    rfl
  calc
    _ = ∑ e, cost (start e) := sum_congr rfl fun e _ => (hcost e).symm
    _ = ∑ p ∈ univ.map start, cost p := (sum_map _ _ _).symm
    _ ≤ _ := sum_le_univ_sum_of_nonneg fun p => hw p.1 (rot p).1

end Cslib.RotationMap

namespace Cslib

/-- Complete a placement by distributing the remaining vertices evenly. The fixed terminals
keep their sites, and the extra load at each site is at most `|V| / |S| + 1`. -/
theorem exists_balanced_sum_placement {S V I : Type*} [Fintype S] [Nonempty S] [Fintype V]
    [Finite I] (fixed : I → S) {k : ℕ} (hfixed : ∀ s, Nat.card {i // fixed i = s} ≤ k) :
    ∃ place : V ⊕ I → S, (∀ i, place (.inr i) = fixed i) ∧
      ∀ s, Nat.card {v // place v = s} ≤ Fintype.card V / Fintype.card S + 1 + k := by
  classical
  let m := Fintype.card V / Fintype.card S + 1
  obtain ⟨j⟩ : Nonempty (V ↪ S × Fin m) := Function.Embedding.nonempty_of_card_le (by
    simpa only [Fintype.card_prod, Fintype.card_fin] using
      (Nat.lt_mul_div_succ (Fintype.card V) (Fintype.card_pos (α := S))).le)
  refine ⟨Sum.elim (fun v => (j v).1) fixed, fun _ => rfl, fun s => ?_⟩
  have hcap : Nat.card {v : V // (j v).1 = s} ≤ m := by
    calc
      _ ≤ Nat.card (Fin m) :=
        Nat.card_le_card_of_injective (fun v : {v : V // (j v).1 = s} => (j v.val).2)
          fun a b h => Subtype.ext (j.injective (Prod.ext (a.property.trans b.property.symm) h))
      _ = m := Nat.card_fin _
  rw [Nat.card_subtype_sum]
  exact Nat.add_le_add hcap (hfixed s)

end Cslib
