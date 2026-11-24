/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.ZModTwo
public import CslibFrontier.Foundations.Data.BitString.List.Operations
public import Mathlib.LinearAlgebra.Basis.Defs
import CslibFrontier.Foundations.Data.List.OfFn
import CslibFrontier.Foundations.Data.List.Blocks
import Mathlib.Data.List.GetD

/-!
# Binary-field arithmetic in coordinates

A basis over `ZMod 2` identifies field elements with bit coordinates. A multiplication table
lists the products of basis vectors; `fieldMul` uses it to multiply arbitrary coordinate lists.
These operations are shared by affine dispersers, hardness encodings and small-bias spaces.

## Main definitions

* `Cslib.BinaryField.ofBits`, `Cslib.BinaryField.fieldOfBits`: elements with given coordinates.
* `Cslib.BinaryField.IsMulTable`: the specification of a multiplication table.
* `Cslib.BinaryField.fieldMul`: multiplication using that table.

## Main results

* `Cslib.BinaryField.fieldOfBits_fieldMul`: correctness of multiplication.
* `Cslib.BinaryField.fieldOfBits_foldl_fieldMul`: products computed by a fold.
-/

@[expose] public section

namespace Cslib.BinaryField

open Module Cslib.BitString

variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {ι : Type*} [Fintype ι] {n : ℕ}

/-- The element of `F` whose coordinates in the basis `b` are the bits `v j`. -/
noncomputable def ofBits (b : Basis ι (ZMod 2) F) (v : ι → Bool) : F :=
  ∑ j, bitEquiv.symm (v j) • b j

/-- The field element whose coordinates in the basis `B` are the first `n` bits of `a`; missing
bits are zero. -/
noncomputable def fieldOfBits (B : Basis (Fin n) (ZMod 2) F) (a : List Bool) : F :=
  ofBits B fun u => a.getD u false

theorem repr_fieldOfBits (B : Basis (Fin n) (ZMod 2) F) (a : List Bool) (u : Fin n) :
    B.repr (fieldOfBits B a) u = bitEquiv.symm (a.getD u false) := by
  rw [fieldOfBits, ofBits, Basis.repr_sum_self]

@[simp]
theorem fieldOfBits_nil (B : Basis (Fin n) (ZMod 2) F) : fieldOfBits B [] = 0 := by
  simp [fieldOfBits, ofBits]

/-- The coordinates of a sum: `listXor` adds coordinate words. -/
theorem fieldOfBits_listXor (B : Basis (Fin n) (ZMod 2) F) (words : List (List Bool)) :
    fieldOfBits B (listXor n words) = (words.map (fieldOfBits B)).sum := by
  have hget (u : Fin n) : (listXor n words).getD u false =
      (words.map fun w => w.getD u false).foldl xor false := by
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp [listXor, List.getD_eq_getElem?_getD]
  simp only [fieldOfBits, ofBits, hget, bitEquiv_symm_foldl_xor, List.map_map]
  clear hget
  induction words with
  | nil => simp
  | cons w words ih =>
    simp only [List.map_cons, List.sum_cons, add_smul, Finset.sum_add_distrib, ← ih,
      Function.comp_apply]
    rfl

/-- The coordinates of the product `B u * B w` in the multiplication table `tab`. -/
def tableEntry (tab : List (List (List Bool))) (u w : ℕ) : List Bool :=
  (tab.getD u []).getD w []

/-- **Multiplication in coordinates**: the coordinates of the product of the elements with
coordinates `a` and `b`, the sum of the products `B u * B w` read from the multiplication table
`tab` of the basis, for the bits `a u = b w = 1`. -/
def fieldMul (tab : List (List (List Bool))) (a b : List Bool) : List Bool :=
  listXor tab.length ((List.range tab.length).flatMap fun u => (List.range tab.length).map fun w =>
    if a.getD u false && b.getD w false then tableEntry tab u w else [])

/-- A multiplication table of the basis `B`: `tab` lists, for `u, w < n`, the coordinates of the
product `B u * B w`. -/
def IsMulTable (B : Basis (Fin n) (ZMod 2) F) (tab : List (List (List Bool))) : Prop :=
  tab.length = n ∧ ∀ u w : Fin n, B u * B w = fieldOfBits B (tableEntry tab u w)

/-- With a multiplication table of the basis `B`, `fieldMul` multiplies: the element with
coordinates `fieldMul tab a b` is the product of those with coordinates `a` and `b`. -/
theorem fieldOfBits_fieldMul {B : Basis (Fin n) (ZMod 2) F} {tab : List (List (List Bool))}
    (htab : IsMulTable B tab) (a b : List Bool) :
    fieldOfBits B (fieldMul tab a b) = fieldOfBits B a * fieldOfBits B b := by
  rw [fieldMul, htab.1, fieldOfBits_listXor, List.sum_map_flatMap, List.sum_map_range]
  simp_rw [List.map_map, Function.comp_def, List.sum_map_range]
  rw [fieldOfBits, fieldOfBits, ofBits, ofBits, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
  rw [smul_mul_smul_comm, htab.2 u w]
  cases a.getD u false <;> cases b.getD w false <;>
    simp

/-- A fold of products in coordinates, skipping the elements with `c x`, multiplies the selected
factors. -/
theorem fieldOfBits_foldl_ite {B : Basis (Fin n) (ZMod 2) F} {tab : List (List (List Bool))}
    (htab : IsMulTable B tab) {X : Type*} (c : X → Prop) [DecidablePred c]
    (f : X → List Bool) (l : List X) (init : List Bool) :
    fieldOfBits B (l.foldl (fun acc x => if c x then acc else fieldMul tab acc (f x)) init) =
      fieldOfBits B init *
        ((l.filter fun x => !decide (c x)).map fun x => fieldOfBits B (f x)).prod := by
  induction l generalizing init with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, List.filter_cons]
    by_cases hx : c x
    · simp [hx]
    · simp only [hx, ↓reduceIte, decide_false, Bool.not_false, List.map_cons, List.prod_cons,
        fieldOfBits_fieldMul htab]
      ring

/-- A fold of products in coordinates multiplies all the factors. -/
theorem fieldOfBits_foldl_fieldMul {B : Basis (Fin n) (ZMod 2) F}
    {tab : List (List (List Bool))} (htab : IsMulTable B tab) {X : Type*} (f : X → List Bool)
    (l : List X) (init : List Bool) :
    fieldOfBits B (l.foldl (fun acc x => fieldMul tab acc (f x)) init) =
      fieldOfBits B init * (l.map fun x => fieldOfBits B (f x)).prod := by
  simpa using fieldOfBits_foldl_ite htab (fun _ : X => False) f l init

end Cslib.BinaryField
