/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.RefuterProofs
public meta import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n.RefuterProofs

/-!
# Tests for the deterministic `4n - 9d` refuter
-/

set_option linter.hashCommand false

public section

namespace CslibFrontierTests.AffineDisperser4nRefuter

open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean
open Cslib.Circuits.Boolean.AffineDisperserCore
open Cslib.Circuits.Boolean.AffineDisperser4n
open Cslib.Circuits.Boolean.SemiCircuit

/-- A `0`-gate circuit on `100` bits. -/
def proj100Circuit : Circuit (fullSignature 2 Bool) 100 1 :=
  ⟨Program.empty, fun _ => Wire.input ⟨0, by decide⟩⟩

#guard (chooseStep? (initialState proj100Circuit)).isNone

/-- There exists a genuine `11`-affine disperser on `100` bits on which `refute` produces a
disagreeing input against `proj100Circuit`. -/
theorem exists_disperser_refute_disagrees :
    ∃ f : BitString 100 → Bool, IsAffineDisperser f 11 ∧
      proj100Circuit.eval fullInterpretation (@refute 100 11 proj100Circuit f) 0 ≠
        f (@refute 100 11 proj100Circuit f) := by
  obtain ⟨f, hf⟩ := exists_isAffineDisperser (n := 100) (d := 11) (by norm_num)
  exact ⟨f, hf, refute_correct proj100Circuit f hf (by decide)⟩

/-- Append `k` unary negation gates to a `1`-output circuit (`size` grows by `k`, while
`binaryB2Cost` stays `0` when the base circuit has cost `0`). -/
def addNotGates {n : ℕ} : ℕ → Circuit (fullSignature 2 Bool) n 1 →
    Circuit (fullSignature 2 Bool) n 1
  | 0, C => C
  | k + 1, C =>
    let C' := addNotGates k C
    ⟨C'.program.gate ⟨FullOp.fn fun xs => !xs 0, fun _ => C'.outputs 0⟩,
      fun _ => Wire.gate (Fin.last C'.size)⟩

private theorem addNotGates_size {n : ℕ} (k : ℕ) (C : Circuit (fullSignature 2 Bool) n 1) :
    (addNotGates k C).size = C.size + k := by
  induction k with
  | zero => simp [addNotGates]
  | succ k ih => change (addNotGates k C).size + 1 = _; omega

private theorem addNotGates_cost {n : ℕ} (k : ℕ) (C : Circuit (fullSignature 2 Bool) n 1) :
    (addNotGates k C).program.cost binaryB2Cost = C.program.cost binaryB2Cost := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ((addNotGates k C).program.gate _).cost binaryB2Cost = _
    rw [Program.cost_gate, ih]
    rfl

#guard (addNotGates 10 proj100Circuit).size == 10
#guard (addNotGates 10 proj100Circuit).program.cost binaryB2Cost == 0
#guard (chooseStep? (initialState (addNotGates 10 proj100Circuit))).isNone

/-- `refute_correct_of_cost_lt` certifies `refute` on `addNotGates 302 proj100Circuit`, whose total
size is `302` (`302 + 9 * 11 = 401 > 4 * 100`, exceeding the `size` threshold) while its binary
gate cost is `0` (`0 + 9 * 11 = 99 < 4 * 100`). -/
theorem exists_disperser_bloated_refute_disagrees :
    let C := addNotGates 302 proj100Circuit
    C.size = 302 ∧ C.program.cost binaryB2Cost = 0 ∧
      ∃ f : BitString 100 → Bool, IsAffineDisperser f 11 ∧
        C.eval fullInterpretation (@refute 100 11 C f) 0 ≠ f (@refute 100 11 C f) := by
  intro C
  have hsize : C.size = 302 := addNotGates_size 302 proj100Circuit
  have hcost : C.program.cost binaryB2Cost = 0 := addNotGates_cost 302 proj100Circuit
  obtain ⟨f, hf⟩ := exists_isAffineDisperser (n := 100) (d := 11) (by norm_num)
  exact ⟨hsize, hcost, f, hf, refute_correct_of_cost_lt C f hf (by rw [hcost]; decide)⟩

/-- A nonterminal circuit on `3` bits with one XOR gate. -/
def xor3Circuit : Circuit (fullSignature 2 Bool) 3 1 :=
  ⟨Program.gate Program.empty
    ⟨FullOp.fn fun xs => xs 0 ^^ xs 1,
      fun i => if _ : i.val = 0 then Wire.input ⟨0, by decide⟩ else Wire.input ⟨1, by decide⟩⟩,
    fun _ => Wire.gate ⟨0, by decide⟩⟩

#guard (chooseStep? (initialState xor3Circuit)).isSome

/-- Opposite-bias paired Case 5a state (`pairs = {(0, false, 1, false), (2, true, 3, false)}`,
`gate 4 = x₀ ∧ x₂`, `gate 5 = x₁ ∧ x₃`, `gate 6 = gate 4 ∧ gate 5`): `chooseStep?` selects
`.andOnPair 4 0` and `applyStep` deletes all three gates (`4`, `6`, `5`) in one step (`Δs = -3`). -/
def oppAndOnPairCircuit : Circuit (fullSignature 2 Bool) 4 1 :=
  let p0 : Program (fullSignature 2 Bool) 4 0 := Program.empty
  let p1 := p0.gate ⟨FullOp.fn fun xs => xs 0 && xs 1,
    fun i => if _ : i.val = 0 then Wire.input ⟨0, by decide⟩ else Wire.input ⟨2, by decide⟩⟩
  let p2 := p1.gate ⟨FullOp.fn fun xs => xs 0 && xs 1,
    fun i => if _ : i.val = 0 then Wire.input ⟨1, by decide⟩ else Wire.input ⟨3, by decide⟩⟩
  let p3 := p2.gate ⟨FullOp.fn fun xs => xs 0 && xs 1,
    fun i => if _ : i.val = 0 then Wire.gate ⟨0, by decide⟩ else Wire.gate ⟨1, by decide⟩⟩
  ⟨p3, fun _ => Wire.gate ⟨2, by decide⟩⟩

def oppAndOnPairState : State 4 :=
  ((initialState oppAndOnPairCircuit).addPair ⟨0, false, 1, false⟩).addPair ⟨2, true, 3, false⟩

#guard (chooseStep? oppAndOnPairState).isSome
#guard oppAndOnPairState.s == 3
#guard (applyStep oppAndOnPairState (.andOnPair 4 0)).s == 0

end CslibFrontierTests.AffineDisperser4nRefuter
