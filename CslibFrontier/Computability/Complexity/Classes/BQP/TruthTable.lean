/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Basic
public import CslibFrontier.Computability.Circuit.Quantum.Input
public import CslibFrontier.Computability.Circuit.Quantum.PhaseCode
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Quantum truth-table queries with classical advice

A pre-query circuit prepares disjoint address registers, which can be entangled with each
other and the workspace. One coherent oracle layer writes all answers into fresh qubits.
A post-query circuit acts on the whole state and a final measurement reads one output bit.

`BQPTruthTablePoly` models the relativized class BQPₜₜᴬ/poly of
[Nishimura and Yamakami, §7.1][NishimuraYamakami2004Nonadaptive]. The pre- and post-query
QTMs are represented by uniformly generated elementary quantum circuits, the alternative
allowed there. Each address block decodes a framed bit string so queries of different lengths
can occur in one superposition. Advice is classical and polynomially bounded. The probability
guarantee applies to the selected advice for each original input length.

## Main definitions

* `Cslib.Quantum.TruthTableCircuitDescription`: the pre-query circuit, address layout and
  post-query circuit.
* `Cslib.Quantum.UniformTruthTableCircuitFamily`: native polynomial-time generation of those
  descriptions.
* `Cslib.Complexity.BQPTruthTablePoly`: bounded-error quantum truth-table computation with
  polynomial-length classical advice.
-/

public section

namespace Cslib.Quantum

open Turing.MultiTapeTM

/-- The two elementary circuits and the register layout for a single truth-table oracle layer. -/
structure TruthTableCircuitDescription where
  /-- The active qubits before the answer bits are appended. -/
  width : ℕ
  /-- The number of disjoint address blocks, hence the number of oracle calls. -/
  queryCount : ℕ
  /-- The common width of the consecutive address blocks at the start of the register. -/
  queryWidth : ℕ
  /-- The measured wire after post-query computation. -/
  outputWire : ℕ
  /-- The gates before the oracle layer, on `width` wires. -/
  preQuery : List PhaseGateCode
  /-- The gates after the layer, on `width + queryCount` wires. -/
  postQuery : List PhaseGateCode

/-- Frame the four unary layout fields, then the pre-query gate list, and end with the
post-query gate list. Both lists use the framed phase-gate encoding. -/
enc_structure encTruthTableCircuitDescription : TruthTableCircuitDescription where
  width : encUnary, queryCount : encUnary, queryWidth : encUnary, outputWire : encUnary,
  preQuery : (encList encPhaseGateCode), postQuery : (encList encPhaseGateCode)

namespace TruthTableCircuitDescription

/-- The encoded description bounds the total number of wires and the number of gates. Each
query contributes an answer wire, so it is also charged by this bound. -/
theorem resources_le_encoding_length (D : TruthTableCircuitDescription) :
    D.width + D.queryCount + D.preQuery.length + D.postQuery.length ≤
      (encTruthTableCircuitDescription D).length := by
  have hpre := length_le_length_encList encPhaseGateCode D.preQuery
  have hpost := length_le_length_encList encPhaseGateCode D.postQuery
  simp only [encTruthTableCircuitDescription_apply, encTruthTableCircuitDescriptionFields,
    length_encPair, encUnary_apply, List.length_replicate]
  omega

/-- The input, address blocks and measured wire fit, and every elementary gate is valid.
The input is the framed instance followed by the raw advice. -/
structure WellFormed (D : TruthTableCircuitDescription) (n k : ℕ) : Prop where
  /-- All encoded input bits fit before the answer bits are appended. -/
  input_le : 2 * n + 1 + k ≤ D.width
  /-- Every address block fits in the initial register. -/
  query_le : D.queryCount * D.queryWidth ≤ D.width
  /-- The final measurement reads a valid wire. -/
  output_lt : D.outputWire < D.width + D.queryCount
  /-- The pre-query gates use only the initial register. -/
  preQuery : ∀ g ∈ D.preQuery, g.WellFormed D.width
  /-- The post-query gates can use the appended answers as well as the initial register. -/
  postQuery : ∀ g ∈ D.postQuery, g.WellFormed (D.width + D.queryCount)

/-- Read one address block from a basis string and decode its framed word. Bits after the frame
are padding. On arbitrary basis strings the same total decoder defines the oracle action. -/
@[expose] def queryWord (D : TruthTableCircuitDescription)
    (h : D.queryCount * D.queryWidth ≤ D.width)
    (z : Fin D.width → Bool) (i : Fin D.queryCount) : List Bool :=
  unframe (List.ofFn (fun j : Fin D.queryWidth => z
    ⟨i.val * D.queryWidth + j.val,
      calc
        i.val * D.queryWidth + j.val < (i.val + 1) * D.queryWidth := by
          rw [Nat.add_mul, Nat.one_mul]
          exact Nat.add_lt_add_left j.isLt _
        _ ≤ D.queryCount * D.queryWidth := Nat.mul_le_mul_right _ i.isLt
        _ ≤ D.width := h⟩))

/-- The simultaneous oracle layer preserves the original register and XORs one answer per
address into the appended register. -/
noncomputable def queryLayer (D : TruthTableCircuitDescription)
    (h : D.queryCount * D.queryWidth ≤ D.width) (A : Set (List Bool)) :
    PlacedGate (D.width + D.queryCount) := by
  classical
  exact xorQuery (fun z i => decide (D.queryWord h z i ∈ A))
    (Function.Embedding.refl _)

/-- On every basis state the layer preserves the original wires and XORs the oracle's
membership bits into the answer wires, in the order of the address blocks. -/
theorem queryLayer_eval_ket (D : TruthTableCircuitDescription)
    (h : D.queryCount * D.queryWidth ≤ D.width) (A : Set (List Bool))
    [DecidablePred (· ∈ A)] (z : Fin D.width → Bool) (r : Fin D.queryCount → Bool) :
    (D.queryLayer h A).eval (ket (Fin.append z r)) =
      ket (Fin.append z (r + fun i => decide (D.queryWord h z i ∈ A))) := by
  classical
  let E := Function.Embedding.refl (Fin (D.width + D.queryCount))
  let w : {j // ¬∃ i, E i = j} → Bool := fun _ => false
  have layout (s : Fin D.queryCount → Bool) :
      (queryRegisters E).symm (z, s, w) = Fin.append z s := by
    apply (queryRegisters E).injective
    simp only [Equiv.apply_symm_apply, queryRegisters_apply, E, Function.Embedding.refl_apply,
      Fin.append_left, Fin.append_right, Prod.mk.injEq, true_and]
    exact funext fun j => (j.property ⟨j.val, rfl⟩).elim
  rw [← layout r, queryLayer, xorQuery_eval_ket, layout]
  congr 2
  funext i
  exact Bool.eq_iff_iff.mpr (by simp)

/-- Execute the pre-query circuit, append clean answer qubits, apply the oracle layer and
execute the post-query circuit. The returned state includes all active qubits. -/
@[expose] noncomputable def run (D : TruthTableCircuitDescription) (x a : List Bool)
    (h : D.WellFormed x.length a.length)
    (A : Set (List Bool)) : Qubits (D.width + D.queryCount) :=
  let prepared := (Circuit.ofPhaseCodes D.width D.preQuery).run
    (inputState D.width (encPair encBits encBits (x, a)))
  let withAnswers := embedState (Fin.castLEEmb (Nat.le_add_right D.width D.queryCount))
    (fun _ => false) prepared
  (Circuit.ofPhaseCodes (D.width + D.queryCount) D.postQuery).eval
    ((D.queryLayer h.query_le A).eval withAnswers)

/-- The probability of observing `true` on the declared output wire. -/
@[expose] noncomputable def acceptProb (D : TruthTableCircuitDescription) (x a : List Bool)
    (h : D.WellFormed x.length a.length) (A : Set (List Bool)) : ℝ :=
  measureProb (D.run x a h A) (onesAt (D.width + D.queryCount) [D.outputWire])

end TruthTableCircuitDescription

/-- A native polynomial-time generator receives the unary instance and advice lengths.
The encoded description pays for every wire, query and elementary gate. -/
structure UniformTruthTableCircuitFamily where
  /-- The layout and circuits, determined by the two lengths. -/
  description : ℕ → ℕ → TruthTableCircuitDescription
  /-- One generator on the framed pair of unary lengths computes the complete description. -/
  computableInPolyTime_description : ComputableInPolyTime
    (fun s : ℕ × ℕ => description s.1 s.2)
    (encPair encUnary encUnary) encTruthTableCircuitDescription
  /-- The resulting circuits are valid at every instance and advice length. -/
  wellFormed : ∀ n k, (description n k).WellFormed n k

/-- The generated circuit's probability of accepting the instance and advice. -/
@[expose] noncomputable def UniformTruthTableCircuitFamily.acceptProb
    (F : UniformTruthTableCircuitFamily) (A : Set (List Bool)) (x a : List Bool) : ℝ :=
  (F.description x.length a.length).acceptProb x a (F.wellFormed x.length a.length) A

end Cslib.Quantum

namespace Cslib.Complexity

open Quantum

/-- BQPₜₜᴬ/poly relative to the language oracle `A`: one coherent batch of membership queries
and polynomial-length classical advice. The advice used on an input depends only on its
original encoded length. -/
@[expose] def BQPTruthTablePoly {α : Type} (enc : α ↪ List Bool)
    (A : Set (List Bool)) : Set (Set α) :=
  {L | ∃ (F : UniformTruthTableCircuitFamily) (advice : ℕ → List Bool),
    PolynomiallyBounded (fun n => (advice n).length) ∧ ∀ x,
      let p := F.acceptProb A (enc x) (advice (enc x).length)
      (x ∈ L → 2 / 3 ≤ p) ∧ (x ∉ L → p ≤ 1 / 3)}

end Cslib.Complexity
