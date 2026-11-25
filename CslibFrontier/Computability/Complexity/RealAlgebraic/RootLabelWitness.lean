/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.SparseIntegerRootLabel
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.ModularArithmetic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size

/-!
# Bounded derivative-sign witnesses

Only the first `N` entries of the witness are used. A binary index is reduced modulo the
source degree bound `D` and then incremented to a positive derivative order. The sign is
read modulo three. Slot zero is the qualifying test, and missing slots have target zero.

Adapted from `CodedRootLabelData` and `CodedRootLabelCorrectness` in lean-canny at commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- A derivative-sign witness entry before its fields are reduced to the allowed ranges. -/
structure RootLabelTestCode where
  /-- Zero-based derivative index, read modulo the degree bound. -/
  index : ℕ
  /-- Target sign, read modulo three as `0`, `1`, or `-1`, respectively. -/
  sign : ℕ
  deriving DecidableEq

/-- A framed pair containing the binary derivative index followed by the binary sign code. -/
enc_structure encRootLabelTestCode : RootLabelTestCode where
  index : encNat,
  sign : encNat

/-- Framed list of derivative-sign entries in test order. Each entry stores the binary index
before the binary sign code. -/
abbrev encRootLabelCode : List RootLabelTestCode ↪ List Bool := encList encRootLabelTestCode

private def decodeSign (k : ℕ) : SignType :=
  if k % 3 = 0 then 0 else if k % 3 = 1 then 1 else -1

private def encodeSign (s : SignType) : ℕ :=
  if s = 0 then 0 else if s = 1 then 1 else 2

private theorem decodeSign_encodeSign (s : SignType) : decodeSign (encodeSign s) = s := by
  cases s <;> decide

/-- Decode at most `N` signed derivative indices from an arbitrary binary witness. -/
def decodeRootLabel {D : ℕ} (hD : 0 < D) (N : ℕ)
    (data : List RootLabelTestCode) : List (Fin D × SignType) :=
  (data.take N).map fun t => (⟨t.index % D, Nat.mod_lt _ hD⟩, decodeSign t.sign)

/-- Encode each derivative-sign entry directly. -/
def encodeRootLabel {D : ℕ} (L : List (Fin D × SignType)) : List RootLabelTestCode :=
  L.map fun (i, s) => ⟨i.val, encodeSign s⟩

/-- The bounded decoder always yields an allowed number of entries. -/
theorem decodeRootLabel_length_le {D : ℕ} (hD : 0 < D) (N : ℕ) (data : List RootLabelTestCode) :
    (decodeRootLabel hD N data).length ≤ N := by
  simp [decodeRootLabel]

/-- Every allowed mathematical label is recovered from its direct encoding. -/
theorem decodeRootLabel_encodeRootLabel {D N : ℕ} (hD : 0 < D) (L : List (Fin D × SignType))
    (hL : L.length ≤ N) : decodeRootLabel hD N (encodeRootLabel L) = L := by
  rw [decodeRootLabel, List.take_of_length_le (by simpa only [encodeRootLabel, List.length_map]
    using hL), encodeRootLabel, List.map_map]
  exact (congrArg L.map (funext fun t =>
    Prod.ext (Fin.ext (Nat.mod_eq_of_lt t.1.isLt)) (decodeSign_encodeSign t.2))).trans L.map_id

/-- The direct encoding of a bounded label has bit length linear in its number of
entries and in the binary size of the derivative bound. -/
theorem length_encRootLabelCode_encodeRootLabel_le {D N : ℕ}
    (L : List (Fin D × SignType)) (hL : L.length ≤ N) :
    (encRootLabelCode (encodeRootLabel L)).length ≤ N * (4 * D.size + 7) := by
  have hentry (t : RootLabelTestCode) (ht : t ∈ encodeRootLabel L) :
      (encRootLabelTestCode t).length ≤ 2 * D.size + 3 := by
    obtain ⟨⟨i, s⟩, _, rfl⟩ := List.mem_map.mp ht
    have := Nat.size_le_size i.isLt.le
    have : (encodeSign s).size ≤ 2 := by cases s <;> decide
    simp only [encRootLabelTestCode_apply, encRootLabelTestCodeFields, length_encPair,
      encNat_apply, Nat.size_eq_bits_len]
    omega
  have hcode := length_encList_le encRootLabelTestCode (encodeRootLabel L) hentry
  rw [encodeRootLabel, List.length_map, show 2 * (2 * D.size + 3) + 1 = 4 * D.size + 7 by omega]
    at hcode
  exact hcode.trans (Nat.mul_le_mul_right _ hL)

/-- Convert the bounded prefix into the positive orders read by the sparse label evaluator. -/
def rootLabelCodeOrders (D N : ℕ) (data : List RootLabelTestCode) : List ℕ :=
  (data.take N).map fun t => t.index % D + 1

/-- The order program uses the successor of the decoded zero-based derivative index. -/
theorem rootLabelCodeOrders_eq {D : ℕ} (hD : 0 < D) (N : ℕ) (data : List RootLabelTestCode) :
    rootLabelCodeOrders D N data = (decodeRootLabel hD N data).map (fun t => t.1.val + 1) := by
  simp only [rootLabelCodeOrders, decodeRootLabel, List.map_map]; rfl

private def signResidue (p k : ℕ) : ℕ :=
  if k % 3 = 0 then 0 else if k % 3 = 1 then 1 else modularSub p 0 1

/-- Read a target residue by binary slot. Slot zero targets a positive qualifying value.
An absent witness entry targets zero. -/
def rootLabelCodeTarget (p : ℕ) (data : List RootLabelTestCode) (i : ℕ) : ℕ :=
  if i = 0 then 1 else signResidue p (data.getD (i - 1) ⟨0, 0⟩).sign

private theorem signResidue_polyTime {α : Type} {enc : α ↪ List Bool} {p k : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hk : ComputableInPolyTime k enc encNat) :
    ComputableInPolyTime (fun w => signResidue (p w) (k w)) enc encNat := by
  have hmod := binary_mod.comp (hk.prod (.const 3))
  simpa only [signResidue, decide_eq_true_eq, Function.comp_apply] using
    ite' (decide_eq' hmod (.const 0)) (.const 0)
      (ite' (decide_eq' hmod (.const 1)) (.const 1)
        (modularSub_polyTime hp (.const 0) (.const 1)))

/-- The order list is computable in polynomial time with a unary prefix bound. -/
theorem rootLabelCodeOrders_polyTime {α : Type} {enc : α ↪ List Bool} {D N : α → ℕ}
    {data : α → List RootLabelTestCode}
    (hD : ComputableInPolyTime D enc encNat) (hN : ComputableInPolyTime N enc encUnary)
    (hdata : ComputableInPolyTime data enc encRootLabelCode) :
    ComputableInPolyTime (fun w => rootLabelCodeOrders (D w) (N w) (data w))
      enc (encList encNat) := by
  have hi := encRootLabelTestCode_index_polyTime (snd enc encRootLabelTestCode)
  simpa only [rootLabelCodeOrders, Function.comp_apply] using
    mapWithInput (listTakeWithInput hdata hN)
      (binary_add' (binary_mod.comp (hi.prod (hD.comp (fst enc encRootLabelTestCode)))) (.const 1))

/-- Binary addressing of the target costs time polynomial in the encoded input and slot. -/
theorem rootLabelCodeTarget_polyTime {α : Type} {enc : α ↪ List Bool} {p i : α → ℕ}
    {data : α → List RootLabelTestCode}
    (hp : ComputableInPolyTime p enc encNat) (hi : ComputableInPolyTime i enc encNat)
    (hdata : ComputableInPolyTime data enc encRootLabelCode) :
    ComputableInPolyTime (fun w => rootLabelCodeTarget (p w) (data w) (i w)) enc encNat := by
  have hk := encRootLabelTestCode_sign_polyTime
    (listGetD_binary (encA := encRootLabelTestCode) ⟨0, 0⟩ hdata (binary_sub' hi (.const 1)))
  simpa only [rootLabelCodeTarget, decide_eq_true_eq, Function.comp_apply] using
    ite' (decide_eq' hi (.const 0)) (.const 1) (signResidue_polyTime hp hk)

private theorem signResidue_cast {p : ℕ} (hp : 0 < p) (k : ℕ) :
    (signResidue p k : ZMod p) = ((decodeSign k : ℤ) : ZMod p) := by
  unfold signResidue decodeSign
  split_ifs <;> simp [modularSub_cast hp]

/-- The target program agrees with the mathematical label on every used slot, including the
qualifying slot and padding. Entries past the prefix cannot affect the label. -/
theorem rootLabelCodeTarget_cast {p D N : ℕ} (hp : 0 < p) (hD : 0 < D)
    (data : List RootLabelTestCode) (q b₀ : Polynomial ℤ) (i : Fin (N + 1)) :
    (rootLabelCodeTarget p data i.val : ZMod p) =
      Int.castRingHom (ZMod p)
        ((Polynomial.sparseRootLabelTests q b₀ N (decodeRootLabel hD N data) i).2 : ℤ) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [rootLabelCodeTarget, Polynomial.sparseRootLabelTests]
  · simp only [rootLabelCodeTarget, Fin.val_succ, Nat.add_one_ne_zero, ite_false,
      Nat.add_sub_cancel, List.getD_eq_getElem?_getD, Polynomial.sparseRootLabelTests,
      Fin.cases_succ]
    rw [decodeRootLabel, List.getElem?_map, List.getElem?_take_of_lt j.isLt]
    cases data[j.val]? with
    | none => simp [signResidue]
    | some t => exact signResidue_cast hp t.sign

end Cslib.Complexity.RealAlgebraic
