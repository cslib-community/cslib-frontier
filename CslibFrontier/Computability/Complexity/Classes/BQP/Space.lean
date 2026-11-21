/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.PhaseCode
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.HaltsAt

/-!
# Bounded-error quantum space

For each input, a deterministic space-bounded transducer with a read-only input tape produces
a unitary circuit on a space-bounded register. The circuit starts in the all-zero state. Its
first qubit is measured after all gates have used the same register. The generator's write-only
output tape does not count toward its workspace.

This is the unitary circuit presentation of [Fefferman and Remscrim][FeffermanRemscrim2021],
arXiv:2006.03530v2, Definitions 4–5, printed p. 6. Their Theorem 1 equates it with the general
bounded-error quantum space class when the space bound is at least logarithmic under their
constructibility hypotheses. The library uses its elementary phase gate set. The independence
of that choice follows from the space-efficient gate approximation cited after Definition 5.
These equivalences are cited results.

## Main definitions

* `Cslib.Quantum.UnitarySpaceCircuitFamily`: a uniform family whose generator and quantum
  register share a space bound.
* `Cslib.Complexity.BQUSpace`: bounded-error unitary quantum space.
* `Cslib.Complexity.BQL` and `Cslib.Complexity.BQPSPACE`: logarithmic and polynomial
  space, using the unitary characterization.
-/

public section

namespace Cslib.Quantum

open Turing Turing.MultiTapeTM

/-- A unitary circuit on a single work register, with the first qubit as its output. -/
structure UnitarySpaceCircuitDescription where
  /-- The number of qubits in the work register. -/
  width : ℕ
  /-- The elementary gates, applied in list order. -/
  gates : List PhaseGateCode

/-- A framed unary width followed by the framed list of phase-gate codes. -/
enc_structure encUnitarySpaceCircuitDescription : UnitarySpaceCircuitDescription where
  width : encUnary, gates : (encList encPhaseGateCode)

/-- Each elementary gate contributes at least one bit to the encoded description. -/
theorem UnitarySpaceCircuitDescription.gates_length_le_encoding_length
    (D : UnitarySpaceCircuitDescription) :
    D.gates.length ≤ (encUnitarySpaceCircuitDescription D).length := by
  have h := length_le_length_encList encPhaseGateCode D.gates
  simp only [encUnitarySpaceCircuitDescription_apply, encUnitarySpaceCircuitDescriptionFields,
    length_encPair]
  omega

/-- A circuit family with a shared space budget for the classical generator and quantum
register. The generator streams its output without charging its length to workspace. -/
structure UnitarySpaceCircuitFamily {α : Type} (enc : α ↪ List Bool) (space : ℕ → ℕ) where
  /-- The generated circuit for the full classical instance. -/
  description : α → UnitarySpaceCircuitDescription
  /-- One halting transducer computes the circuit description within the workspace budget. -/
  generator : ∃ time, ComputableInTimeAndSpace description enc encUnitarySpaceCircuitDescription
    time (fun a => space (enc a).length)
  /-- The quantum register stays within the same budget. -/
  width_le : ∀ a, (description a).width ≤ space (enc a).length
  /-- The output qubit exists. -/
  width_pos : ∀ a, 0 < (description a).width
  /-- All gates act on valid wires and belong to the elementary gate set. -/
  wellFormed : ∀ a, ∀ g ∈ (description a).gates, g.WellFormed (description a).width

namespace UnitarySpaceCircuitFamily

variable {α : Type} {enc : α ↪ List Bool} {space : ℕ → ℕ}

/-- The probability of measuring one on the first qubit after starting from the all-zero state. -/
@[expose] noncomputable def acceptProb (F : UnitarySpaceCircuitFamily enc space) (a : α) : ℝ :=
  PhaseGateCode.acceptProb (F.description a).width (F.description a).gates []

/-- Reuse the same generator and circuits under a larger space budget. -/
def enlargeSpace (F : UnitarySpaceCircuitFamily enc space) {space' : ℕ → ℕ}
    (h : ∀ n, space n ≤ space' n) : UnitarySpaceCircuitFamily enc space' where
  description := F.description
  generator := by
    obtain ⟨t, ht⟩ := F.generator
    exact ⟨t, ht.mono (fun _ => le_rfl) fun a => h (enc a).length⟩
  width_le a := (F.width_le a).trans (h (enc a).length)
  width_pos := F.width_pos
  wellFormed := F.wellFormed

@[simp] theorem acceptProb_enlargeSpace (F : UnitarySpaceCircuitFamily enc space) {space' : ℕ → ℕ}
    (h : ∀ n, space n ≤ space' n) (a : α) :
    (F.enlargeSpace h).acceptProb a = F.acceptProb a := by
  simp only [acceptProb, enlargeSpace]

/-- The gate count is at most exponential in the classical workspace, with the input head
contributing a factor of `n + 2`. A halting generator never repeats a nonhalting core. -/
theorem exists_gate_count_bound (F : UnitarySpaceCircuitFamily enc space) :
    ∃ C d : ℕ, ∀ a, (F.description a).gates.length ≤
      ((enc a).length + 2) * (C * 2 ^ (d * space (enc a).length)) := by
  obtain ⟨t, k, State, hState, tm, ht⟩ := F.generator
  let := Fintype.ofFinite State
  refine ⟨storageBoundBase Bool State k, storageBoundExp Bool k, fun a => ?_⟩
  have hcore := (ht a).of_card
  obtain ⟨u, hle, hhalt⟩ := exists_haltsAt_of_runsInTime hcore.2.1
  have hout : (encUnitarySpaceCircuitDescription (F.description a)).length ≤ u := by
    rw [← output_haltsAt hcore.1 hhalt]
    simpa [MultiTapeNTM.initCfg] using tm.length_output_runFrom_le (tm.initCfg (enc a)) u
  exact (F.description a).gates_length_le_encoding_length.trans
    (hout.trans (hle.trans (Nat.mul_le_mul_left _ (storageBound_le_base_mul_pow _))))

/-- With logarithmic workspace the gate count is polynomial in the input length. -/
theorem polyBounded_gate_count_of_log {c : ℕ}
    (F : UnitarySpaceCircuitFamily enc (fun n => c * (Nat.log2 n + 1))) :
    PolyBounded (fun a => (enc a).length) (fun a => (F.description a).gates.length) := by
  obtain ⟨t, ht⟩ := F.generator
  exact (ComputableInLogSpace.polyBounded_length ⟨t, c, ht⟩).mono
    fun a => (F.description a).gates_length_le_encoding_length

end UnitarySpaceCircuitFamily

end Cslib.Quantum

namespace Cslib.Complexity

open Quantum

variable {α : Type}

/-- Bounded-error unitary quantum space: the workspace and the number of quantum wires are
bounded by a constant times `s(n) + 1`. The gate count is controlled by the generator's space. -/
@[expose] def BQUSpace (enc : α ↪ List Bool) (s : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ (c : ℕ) (F : UnitarySpaceCircuitFamily enc (fun n => c * (s n + 1))), ∀ a,
    (a ∈ A → 2 / 3 ≤ F.acceptProb a) ∧ (a ∉ A → F.acceptProb a ≤ 1 / 3)}

/-- Bounded-error quantum logarithmic space, in its equivalent unitary presentation. -/
@[expose] def BQL (enc : α ↪ List Bool) : Set (Set α) := BQUSpace enc Nat.log2

/-- Bounded-error quantum polynomial space, in its equivalent unitary presentation.
Polynomial space permits exponentially long gate sequences. -/
@[expose] def BQPSPACE (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ p : Polynomial ℕ, A ∈ BQUSpace enc p.eval}

/-- Increasing the space allowance preserves a bounded-error unitary computation. -/
theorem BQUSpace.mono {enc : α ↪ List Bool} {s t : ℕ → ℕ} (h : ∀ n, s n ≤ t n) :
    BQUSpace enc s ⊆ BQUSpace enc t := by
  rintro A ⟨c, F, hF⟩
  refine ⟨c, F.enlargeSpace (fun n => Nat.mul_le_mul_left c (Nat.succ_le_succ (h n))), ?_⟩
  simpa only [UnitarySpaceCircuitFamily.acceptProb_enlargeSpace] using hF

/-- Logarithmic quantum space is contained in polynomial quantum space. -/
theorem BQL_subset_BQPSPACE (enc : α ↪ List Bool) : BQL enc ⊆ BQPSPACE enc := by
  intro A hA
  refine ⟨Polynomial.X, BQUSpace.mono (fun n => ?_) hA⟩
  simpa using Nat.log2_le_self n

end Cslib.Complexity
