/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.Resources
public import CslibFrontier.Computability.Complexity.Problems.NCL.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Structural word encodings

A layer records its tag, unary offset, colored boundaries and local vertex data. Local edges
carry a boundary side and a unary index. The encoding is injective and pays for every new wire
position created by a run.

## Main definitions

* `Cslib.Complexity.NCL.Slice.Data`: layer data with named fields.
* `Cslib.Complexity.NCL.encColor`, `Cslib.Complexity.NCL.encSlice`,
  `Cslib.Complexity.NCL.encWord`: structural encodings of diagram words.

## Main results

* `Cslib.Complexity.NCL.Word.cost_le_length_encWord`: encoded length bounds resource use.
* `Cslib.Complexity.NCL.Diagram.computableInPolyTime_toWord`:
  polynomial-time fixed-diagram emission.
-/

public section

namespace Cslib.Complexity.NCL

open _root_.Turing.MultiTapeTM

/-- Encode a local boundary edge by its side and index. -/
@[expose] def Slice.localIndex {n m : ℕ} : Fin n ⊕ Fin m → Bool × ℕ
  | .inl i => (true, i.val)
  | .inr j => (false, j.val)

/-- Side tags and local indices distinguish all boundary edges. -/
theorem Slice.localIndex_injective {n m : ℕ} :
    Function.Injective (Slice.localIndex (n := n) (m := m)) :=
  fun x y h => by cases x <;> cases y <;> simp_all [Slice.localIndex, Fin.ext_iff]

/-- Side-tagged local vertex data, together with a layer tag, offset and colored boundaries. -/
structure Slice.Data where
  /-- Whether the layer exchanges two adjacent wires. -/
  isSwap : Bool
  /-- The layer's unary offset in the wire stack. -/
  offset : ℕ
  /-- The colors consumed by a generator layer. -/
  inputs : List Color
  /-- The colors created by a generator layer. -/
  outputs : List Color
  /-- Local vertices whose edges are side-tagged unary boundary indices. -/
  vertices : List (Vertex (Bool × ℕ))

/-- Forget the dependent local edge bounds while retaining the complete layer data. -/
@[expose] def Slice.data : Slice → Slice.Data
  | .gen k a b vs => ⟨false, k, a, b, vs.map (Vertex.map Slice.localIndex)⟩
  | .swap k => ⟨true, k, [], [], []⟩

private theorem Slice.data_injective : Function.Injective Slice.data := by
  rintro (⟨k, a, b, vs⟩ | k) (⟨k', a', b', vs'⟩ | k') h
  · injection h with _ hk ha hb hv
    subst hk ha hb
    exact congrArg _
      (List.map_injective_iff.mpr (Vertex.map_injective Slice.localIndex_injective) hv)
  · exact Bool.noConfusion (congrArg Slice.Data.isSwap h)
  · exact Bool.noConfusion (congrArg Slice.Data.isSwap h)
  · exact congrArg Slice.swap (congrArg Slice.Data.offset h)

/-- Encode a wire color by one Boolean. -/
@[expose] def encColor : Color ↪ List Bool :=
  (⟨fun c => c == .blue, by
    intro c d h
    cases c <;> cases d <;> simp_all⟩ : Color ↪ Bool).trans encBool

/-- Structural layer data with unary offsets and local indices. -/
enc_structure Slice.encData : Slice.Data where isSwap : encBool, offset : encUnary,
  inputs : (encList encColor), outputs : (encList encColor),
  vertices : (encList (encVertex (encPair encBool encUnary)))

/-- Encode a layer structurally, using unary wire offsets and local indices. -/
@[expose] def encSlice : Slice ↪ List Bool :=
  (⟨Slice.data, by exact Slice.data_injective⟩ : Slice ↪ Slice.Data).trans Slice.encData

/-- Encode a diagram word as its list of structurally encoded layers. -/
@[expose] def encWord : Word ↪ List Bool := encList encSlice

/-- Read the structural data represented by a layer encoding in polynomial time. -/
@[fun_prop]
theorem Slice.computableInPolyTime_data :
    ComputableInPolyTime Slice.data encSlice Slice.encData :=
  ComputableInPolyTime.of_eq (fun _ => rfl)

/-- Emit a fixed layer at a computed unary offset in polynomial time. -/
@[fun_prop]
theorem Slice.computableInPolyTime_shift (sl : Slice) :
    ComputableInPolyTime (fun k => sl.shift k) encUnary encSlice :=
  (by cases sl <;> unfold Slice.shift Slice.data Slice.encData <;> fun_prop :
    ComputableInPolyTime (fun k => (sl.shift k).data) encUnary Slice.encData).of_enc_eq
    fun _ => rfl

/-- Emit a fixed word at a computed unary offset in polynomial time. -/
theorem Word.computableInPolyTime_shift (w : Word) :
    ComputableInPolyTime (fun k => w.map (Slice.shift k)) encUnary encWord :=
  ComputableInPolyTime.mapConst w fun sl _ => sl.computableInPolyTime_shift

/-- Emit the word of a fixed diagram at a computed unary offset in polynomial time. -/
theorem Diagram.computableInPolyTime_toWord {Γ : List Color → List Color → Type}
    (I : Diagram.Interp Γ) {a b : List Color} (D : Diagram Γ a b) :
    ComputableInPolyTime (D.toWord I) encUnary encWord := by
  simpa only [← Diagram.toWord_shift, Nat.add_zero] using
    Word.computableInPolyTime_shift (D.toWord I 0)


private theorem Slice.cost_le_encoded_length (sl : Slice) : sl.cost ≤ (encSlice sl).length := by
  cases sl with
  | gen k a b vs =>
    have := length_le_length_encList encColor b
    simp only [encSlice, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk, Slice.data,
      Slice.cost, Slice.encData_apply, Slice.encDataFields, length_encPair]
    omega
  | swap k => simp [encSlice, Slice.data, Slice.cost, Slice.encData_apply, Slice.encDataFields]

/-- The structural encoding pays for every new wire position created by the word. -/
theorem Word.cost_le_length_encWord (w : Word) : w.cost ≤ (encWord w).length :=
  (List.sum_le_sum (fun sl _ => sl.cost_le_encoded_length)).trans
    (sum_length_le_length_encList encSlice w)


end Cslib.Complexity.NCL
