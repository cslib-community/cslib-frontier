/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Assembly.Basic
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Reorient

/-!
# Local reference directions in component assemblies

Each component can read the shared edge bits in its own reference directions. This permits
arbitrary incidences when connecting shorthand cells, including auxiliary red ports.

## Main definitions

* `Cslib.Complexity.NCL.Component.reorient`: read the boundary through an XOR mask.
* `Cslib.Complexity.NCL.Realizes.reorient`: transport a local implementation through that mask.
-/

public section

namespace Cslib.Complexity.NCL

/-- Read a component's boundary in the reference directions selected by the mask. -/
@[expose] def Component.reorient {E : Type*} (C : Component E) (mask : E → Bool) : Component E where
  State := C.State
  Legal s x := C.Legal (mask + s) x
  InnerStep s x y := C.InnerStep (mask + s) x y

/-- Changing the shared-edge references leaves private graph bits unchanged. -/
theorem ConstraintGraph.legal_reorient_boundary {V E I : Type*}
    (H : ConstraintGraph V (E ⊕ I)) (mask s : E → Bool) (x : I → Bool) :
    (H.reorient (Sum.elim mask (fun _ => false))).Legal (Sum.elim s x) ↔
      H.Legal (Sum.elim (mask + s) x) := by
  have heq : Sum.elim mask (fun _ : I => false) + Sum.elim s x = Sum.elim (mask + s) x := by
    funext e
    cases e with
    | inl e => rfl
    | inr i =>
      change (false : Bool) + x i = x i
      simp only [Bool.add_eq_xor, Bool.false_xor]
  rw [ConstraintGraph.legal_reorient, heq]

/-- A boundary change of reference directions preserves an open vertex implementation. -/
@[expose] def Realizes.reorient {E : Type*} [DecidableEq E] {C : Component E} {v : Vertex E}
    (R : Realizes C v) (mask : E → Bool) : Realizes (C.reorient mask) (v.reorient mask) where
  canon s := R.canon (mask + s)
  sound hs := (Vertex.sat_reorient mask v _).2 (R.sound hs)
  legal_canon hs := R.legal_canon ((Vertex.sat_reorient mask v _).1 hs)
  move {s} e hs ht := by
    have hs' := (Vertex.sat_reorient mask v s).1 hs
    have ht' : v.Sat (reverse (mask + s) e) := by
      rw [reverse_add_left]
      exact (Vertex.sat_reorient mask v _).1 ht
    obtain ⟨u, hp, hu, hq⟩ := R.move e hs' ht'
    refine ⟨u, hp, ?_, ?_⟩
    · change C.Legal (mask + reverse s e) u
      simpa only [reverse_add_left] using hu
    · change Relation.ReflTransGen (C.Step (mask + reverse s e)) u
        (R.canon (mask + reverse s e))
      simpa only [reverse_add_left] using hq

end Cslib.Complexity.NCL
