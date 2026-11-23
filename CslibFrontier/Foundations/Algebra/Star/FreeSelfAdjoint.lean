/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Algebra/Star/Free.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.Module

/-!
# The free star algebra on self-adjoint generators

The involution conjugates the coefficients and reverses the words. Its universal property
extends any assignment of the generators to self-adjoint elements uniquely to a star-algebra
homomorphism.
-/

public section

/-- The free algebra with an involution fixing the generators and acting by the scalar
involution on coefficients. -/
@[expose] def FreeSelfAdjoint (R X : Type*) [CommRing R] := FreeAlgebra R X

namespace FreeSelfAdjoint

variable {R X : Type*} [CommRing R]

instance : Ring (FreeSelfAdjoint R X) := inferInstanceAs (Ring (FreeAlgebra R X))
instance : Algebra R (FreeSelfAdjoint R X) := inferInstanceAs (Algebra R (FreeAlgebra R X))

/-- The generator corresponding to a variable. -/
def of (x : X) : FreeSelfAdjoint R X := FreeAlgebra.ι R x

variable [StarRing R]

private def reverse : FreeAlgebra R X →+* (FreeAlgebra R X)ᵐᵒᵖ :=
  let _ : Algebra R (FreeAlgebra R X)ᵐᵒᵖ := Algebra.compHom _ (starRingEnd R)
  (FreeAlgebra.lift R (fun x : X => MulOpposite.op (FreeAlgebra.ι R x))).toRingHom

private theorem reverse_of (x : X) :
    (reverse (FreeAlgebra.ι R x)).unop = FreeAlgebra.ι R x := by
  let _ : Algebra R (FreeAlgebra R X)ᵐᵒᵖ := Algebra.compHom _ (starRingEnd R)
  change (FreeAlgebra.lift R (fun y : X => MulOpposite.op (FreeAlgebra.ι R y))
    (FreeAlgebra.ι R x)).unop = _
  rw [FreeAlgebra.lift_ι_apply]
  rfl

private theorem reverse_algebraMap (r : R) :
    (reverse (algebraMap R (FreeAlgebra R X) r)).unop =
      algebraMap R (FreeAlgebra R X) (star r) := by
  let _ : Algebra R (FreeAlgebra R X)ᵐᵒᵖ := Algebra.compHom _ (starRingEnd R)
  change (FreeAlgebra.lift R (fun y : X => MulOpposite.op (FreeAlgebra.ι R y))
    (algebraMap R (FreeAlgebra R X) r)).unop = _
  rw [AlgHom.commutes]
  rfl

private theorem reverse_twice (a : FreeAlgebra R X) :
    (reverse (reverse a).unop).unop = a := by
  induction a with
  | grade0 r => rw [reverse_algebraMap, reverse_algebraMap, star_star]
  | grade1 x => rw [reverse_of, reverse_of]
  | mul a b ha hb => rw [map_mul, MulOpposite.unop_mul, map_mul, MulOpposite.unop_mul, ha, hb]
  | add a b ha hb => rw [map_add, MulOpposite.unop_add, map_add, MulOpposite.unop_add, ha, hb]

@[no_expose] instance : StarRing (FreeSelfAdjoint R X) := by
  exact {
    star a := (reverse a).unop
    star_involutive := reverse_twice
    star_mul a b := by
      exact congrArg MulOpposite.unop (map_mul reverse
        (a : FreeAlgebra R X) (b : FreeAlgebra R X))
    star_add a b := by
      exact congrArg MulOpposite.unop (map_add reverse
        (a : FreeAlgebra R X) (b : FreeAlgebra R X)) }

@[simp] theorem star_of (x : X) : star (of x : FreeSelfAdjoint R X) = of x := by
  exact reverse_of (R := R) x

theorem star_algebraMap (r : R) :
    star (algebraMap R (FreeSelfAdjoint R X) r) = algebraMap R _ (star r) := by
  exact reverse_algebraMap (X := X) r

instance : StarModule R (FreeSelfAdjoint R X) where
  star_smul r a := by
    rw [Algebra.smul_def, star_mul, star_algebraMap, ← Algebra.commutes, ← Algebra.smul_def]

variable {B : Type*} [Ring B] [Algebra R B] [StarRing B] [StarModule R B]

/-- Extend an assignment of self-adjoint elements to the free algebra. -/
def lift (f : X → B) (hf : ∀ x, IsSelfAdjoint (f x)) : FreeSelfAdjoint R X →⋆ₐ[R] B where
  __ := FreeAlgebra.lift R f
  map_star' a := by
    let f' : FreeSelfAdjoint R X →ₐ[R] B := FreeAlgebra.lift R f
    change f' (star a) = star (f' a)
    refine FreeAlgebra.induction R X
      (motive := fun a : FreeAlgebra R X =>
        f' (star (R := FreeSelfAdjoint R X) a) = star (f' a)) ?_ ?_ ?_ ?_ a
    · intro r
      change f' (star (algebraMap R (FreeSelfAdjoint R X) r)) =
        star (f' (algebraMap R (FreeSelfAdjoint R X) r))
      rw [star_algebraMap, AlgHom.commutes, AlgHom.commutes,
        Algebra.algebraMap_eq_smul_one (R := R) (A := B) r, star_smul, star_one,
        ← Algebra.algebraMap_eq_smul_one]
    · intro x
      change f' (star (of x)) = star (f' (of x))
      have hx : f' (of x) = f x := FreeAlgebra.lift_ι_apply f x
      rw [star_of, hx, (hf x).star_eq]
    · intro a b ha hb
      let a' : FreeSelfAdjoint R X := a
      let b' : FreeSelfAdjoint R X := b
      have ha' : f' (star a') = star (f' a') := ha
      have hb' : f' (star b') = star (f' b') := hb
      change f' (star (a' * b')) = star (f' (a' * b'))
      rw [star_mul, map_mul, map_mul, star_mul, ha', hb']
    · intro a b ha hb
      let a' : FreeSelfAdjoint R X := a
      let b' : FreeSelfAdjoint R X := b
      have ha' : f' (star a') = star (f' a') := ha
      have hb' : f' (star b') = star (f' b') := hb
      change f' (star (a' + b')) = star (f' (a' + b'))
      rw [star_add, map_add, map_add, star_add, ha', hb']

@[simp] theorem lift_of (f : X → B) (hf : ∀ x, IsSelfAdjoint (f x)) (x : X) :
    lift f hf (of x : FreeSelfAdjoint R X) = f x := FreeAlgebra.lift_ι_apply f x

omit [StarModule R B] in
/-- A star-algebra homomorphism out of the free algebra is determined by the generators. -/
@[ext] theorem hom_ext {f g : FreeSelfAdjoint R X →⋆ₐ[R] B}
    (h : ∀ x, f (of x) = g (of x)) : f = g := by
  have he : f.toAlgHom = g.toAlgHom := FreeAlgebra.hom_ext (funext h)
  exact DFunLike.ext f g fun a => congrArg (fun F : FreeSelfAdjoint R X →ₐ[R] B => F a) he

end FreeSelfAdjoint
