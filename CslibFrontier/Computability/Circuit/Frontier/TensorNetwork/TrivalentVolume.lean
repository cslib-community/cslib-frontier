/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.Open
import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.Substitution
import Mathlib.Order.Lattice.Nat

/-!
# Minimum volume of a trivalent realization

Minimize over every finite internal graph realizing a specified exterior table. A minimum
for a product table may connect its factors internally. Any trivalent realization witnesses
attainment, including a disjoint union of implementations for the individual factors.
-/

namespace Cslib.Circuits.Frontier.OpenBitNetwork

variable {R : Type*} [CommSemiring R]

variable {J : Type} [Fintype J] (table : (J → Bool) → R)

private def realizationVolumes : Set ℕ :=
  {s : ℕ | ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (_ : DecidableEq E)
    (N : OpenBitNetwork R J V E), N.Trivalent ∧
      (∀ x, N.contraction x = table x) ∧ N.volume = s}

/-- The minimum volume among exact trivalent realizations of an exterior table with finite
vertex and edge sets in `Type`. As usual for natural infima, an empty set has infimum zero. -/
public noncomputable def minTrivalentVolume : ℕ := sInf (realizationVolumes table)

variable {V' E' : Type} [Fintype V'] [Fintype E'] [DecidableEq E']
  (N' : OpenBitNetwork R J V' E') (hN : N'.Trivalent) (htable : ∀ x, N'.contraction x = table x)

include hN htable in
/-- Every exact trivalent realization is an upper bound for the minimum. -/
public theorem minTrivalentVolume_le : minTrivalentVolume table ≤ N'.volume :=
  Nat.sInf_le ⟨V', E', inferInstance, inferInstance, inferInstance, N', hN, htable, rfl⟩

include hN htable in
/-- If there is a trivalent realization, one with minimum volume attains the same table. -/
public theorem exists_volume_eq_minTrivalentVolume :
    ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (_ : DecidableEq E)
      (M : OpenBitNetwork R J V E), M.Trivalent ∧ (∀ x, M.contraction x = table x) ∧
        M.volume = minTrivalentVolume table :=
  Nat.sInf_mem (s := realizationVolumes table)
    ⟨N'.volume, V', E', inferInstance, inferInstance, inferInstance, N', hN, htable, rfl⟩

/-- Disjoint realizations give a tensor power of at most the sum of their volumes. -/
public theorem exists_tensorPower {R J V E : Type} [CommSemiring R] [Finite J] [Fintype V]
    [Fintype E] [DecidableEq E] (N : OpenBitNetwork R J V E) (hN : N.Trivalent) (j : ℕ) :
    ∃ (V' E' : Type) (_ : Fintype V') (_ : Fintype E') (_ : DecidableEq E')
      (M : OpenBitNetwork R (Fin j × J) V' E'), M.Trivalent ∧ M.volume ≤ j * N.volume ∧
        ∀ x, M.contraction x = ∏ i : Fin j, N.contraction (fun k => x (i, k)) := by
  classical
  let B := fun _ : Fin j => N
  let D := disjointUnion B
  let e := (Equiv.sigmaEquivProd (Fin j) J).symm
  obtain ⟨M, hM, hv, hc⟩ := D.exists_reindex (trivalent_disjointUnion B fun _ => hN) e
  refine ⟨_, _, inferInstance, inferInstance, inferInstance, M, hM, ?_, fun x => ?_⟩
  · simp [hv, D, B, volume_disjointUnion]
  · rw [hc, contraction_disjointUnion]
    rfl

end Cslib.Circuits.Frontier.OpenBitNetwork
