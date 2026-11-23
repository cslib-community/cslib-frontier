/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Basic
public import CslibFrontier.Computability.QueryComplexity.Quantum.ValueQuery
import all CslibFrontier.Computability.Circuit.Quantum.Oracle.Basic
import all CslibFrontier.Computability.QueryComplexity.Quantum.ValueQuery

/-!
# Placed XOR queries and the quantum value-query model

A placed coherent XOR query agrees with the existing `valueOracle addStep` after reindexing its
query, response and unused registers. This bridge includes arbitrary superpositions and workspace
states. The circuit code layer does not depend on the abstract value-query simulation machinery.

## Main results

* `Cslib.Quantum.xorQuery_eq_valueOracle`: agreement of the placed and value-query semantics.
* `Cslib.Quantum.runValue_lookupXorSteps`: implement a placed lookup with two calls to a
  separate XOR oracle, restoring its scratch registers for the next instruction.
-/

public section

namespace Cslib.Quantum

variable {a b m : ℕ}

private theorem bitString_sub_eq_add {n : ℕ} (u v : BitString n) : u - v = u + v :=
  funext fun j => BooleanRing.sub_eq_add (u j) (v j)

/-- Reindexing the placed gate into its three registers gives the existing value oracle.
This equality covers arbitrary superpositions and arbitrary states of the unused wires. -/
theorem xorQuery_eq_valueOracle (H : (Fin a → Bool) → Fin b → Bool)
    (A : Fin (a + b) ↪ Fin m) (ψ : Qubits m) :
    let reindex := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (queryRegisters A)
    reindex ((xorQuery H A).eval ψ) = valueOracle addStep H (reindex ψ) := by
  intro reindex
  ext ⟨x, y, w⟩
  change ((xorQuery H A).eval ψ).ofLp ((queryRegisters A).symm (x, y, w)) = _
  rw [xorQuery_eval_apply, valueOracle_apply, addStep_apply]
  simp [reindex, bitString_sub_eq_add]

section Lookup

variable {n d : ℕ}

/-- Embed a native register alongside two zero work registers for the lookup address and value. -/
noncomputable def cleanLookupState :
    Qubits m →ₗᵢ[ℂ] ValueState (BitString n) (BitString d) (BitString m) :=
  LinearIsometry.piLpExtendByZero 2 ℂ ℂ (fiberEmb (Equiv.prodAssoc _ _ _).symm (0, 0))

private theorem cleanLookupState_apply (ψ : Qubits m) (i : BitString n) (v : BitString d)
    (z : BitString m) :
    (cleanLookupState ψ).ofLp (i, v, z) = if i = 0 ∧ v = 0 then ψ.ofLp z else 0 := by
  rw [cleanLookupState, piLpExtendByZero_fiberEmb_apply]
  simp [Prod.ext_iff]

/-- The three table-independent operations surrounding a pair of XOR queries: compute the
lookup address, apply the placed XOR response, and uncompute the address. -/
noncomputable def lookupXorSteps (wires : Fin (a + b) ↪ Fin m)
    (select : BitString a → BitString n) (reply : BitString a → BitString d → BitString b) :
    ℕ → ValueState (BitString n) (BitString d) (BitString m) →ₗᵢ[ℂ]
      ValueState (BitString n) (BitString d) (BitString m) :=
  let address (z : BitString m) := select (queryRegisters wires z).1
  let route : Equiv.Perm (BitString n × BitString d × BitString m) :=
    { toFun := fun (i, v, z) => (i + address z, v, z)
      invFun := fun (i, v, z) => (i - address z, v, z)
      left_inv := by rintro ⟨i, v, z⟩; simp
      right_inv := by rintro ⟨i, v, z⟩; simp }
  let post : Equiv.Perm (BitString n × BitString d × BitString m) :=
    Equiv.prodCongrRight fun _ => Equiv.prodCongrRight fun v => queryPerm (fun x => reply x v) wires
  let routing := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ route
  fun k => match k with
    | 0 => routing.toLinearIsometry
    | 1 => (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ post).toLinearIsometry
    | 2 => routing.symm.toLinearIsometry
    | _ + 3 => .id

private theorem double_sub {k : ℕ} (u v : BitString k) : u - v - v = u := by
  funext j
  change u j - v j - v j = u j
  rw [sub_sub, BooleanRing.add_self, sub_zero]

/-- The compiled query implements the native placed XOR gate and restores both scratch
registers, with the same encoding for all choices of wires. -/
theorem runValue_lookupXorSteps (wires : Fin (a + b) ↪ Fin m)
    (select : BitString a → BitString n) (reply : BitString a → BitString d → BitString b)
    (D : BitString n → BitString d) (ψ : Qubits m) :
    runValue addStep (lookupXorSteps wires select reply) (cleanLookupState ψ) D 2 =
      cleanLookupState ((xorQuery (fun x => reply x (D (select x))) wires).eval ψ) := by
  ext ⟨i, v, z⟩
  obtain ⟨⟨x, y, w⟩, rfl⟩ := (queryRegisters wires).symm.surjective z
  have undo (v' : BitString d) :
      (queryPerm (fun x => reply x v') wires).symm ((queryRegisters wires).symm (x, y, w)) =
        (queryRegisters wires).symm (x, y + reply x v', w) := by
    apply (queryPerm _ wires).injective
    rw [Equiv.apply_symm_apply]
    simp [queryPerm, Equiv.prodCongr, Equiv.addRight]
  simp only [runValue, lookupXorSteps, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.piLpCongrLeft_symm, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply, Equiv.symm_symm, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
    Equiv.prodCongrRight_symm, Equiv.prodCongrRight_apply, Function.comp_apply, undo,
    Equiv.apply_symm_apply, valueOracle_apply, addStep_apply, add_sub_cancel_right, double_sub,
    cleanLookupState_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp only [zero_add, bitString_sub_eq_add, xorQuery_eval_apply]
  · rfl

end Lookup

end Cslib.Quantum
