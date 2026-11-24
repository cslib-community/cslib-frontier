/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame
public import Mathlib.Algebra.Star.StarAlgHom
public import CslibFrontier.Foundations.Algebra.Star.FreeSelfAdjoint
import Mathlib.Algebra.Star.BigOperators
public import Mathlib.Algebra.Star.RingQuot
import all Mathlib.Algebra.RingQuot
import all Mathlib.Algebra.Star.RingQuot

/-!
# The algebra of a synchronous game

For each question and answer there is a self-adjoint projection. The projections
for a fixed question sum to one, and a rejected tuple forces the product of the
corresponding two generators to be zero. The universal property takes these
projection relations directly, giving the algebra of
[Helton, Meyer, Paulsen and Satriano, §3.1][HeltonEtAl2019] for a synchronous
predicate. The source presents the projections as spectral projections of the finite-order
unitaries in a free product of cyclic groups. Here they are generators themselves, and
synchrony gives orthogonality for distinct answers to the same question. Taking adjoints
also kills the reversed products associated to rejected tuples. The question distribution
plays no role in the algebra.

## Main definitions

* `Cslib.PCP.TwoProverGame.IsSynchronous`: unequal answers to equal questions are rejected.
* `Cslib.PCP.TwoProverGame.GameAlgebra`: the universal complex star algebra.
* `Cslib.PCP.TwoProverGame.GameAlgebra.lift`: the representation from an assignment of operators
  satisfying the relations.
-/

public section

namespace Cslib.PCP.TwoProverGame

variable {X A : Type*}

/-- Equal questions require equal answers. -/
@[expose] def IsSynchronous (G : TwoProverGame X X A A) : Prop :=
  ∀ x a b, a ≠ b → ¬ G.accepts x x a b

variable [Fintype A] (G : TwoProverGame X X A A)

local notation "Raw" => FreeSelfAdjoint ℂ (X × A)

/-- The defining relations on the free star algebra, closed under adjoints. -/
inductive GameAlgebraRel : FreeSelfAdjoint ℂ (X × A) → FreeSelfAdjoint ℂ (X × A) → Prop
  | projective (x : X) (a : A) :
    GameAlgebraRel (FreeSelfAdjoint.of (x, a) * FreeSelfAdjoint.of (x, a))
      (FreeSelfAdjoint.of (x, a))
  | normalized (x : X) : GameAlgebraRel (∑ a, FreeSelfAdjoint.of (x, a)) 1
  | rejected (x y : X) (a b : A) (h : ¬ G.accepts x y a b) :
    GameAlgebraRel (FreeSelfAdjoint.of (x, a) * FreeSelfAdjoint.of (y, b)) 0
  | adjoint {v w : Raw} : GameAlgebraRel v w → GameAlgebraRel (star v) (star w)

/-- The universal complex star algebra of the verifier's predicate. -/
@[expose] def GameAlgebra := RingQuot (GameAlgebraRel G)

namespace GameAlgebra

@[no_expose] instance : Ring G.GameAlgebra :=
  inferInstanceAs (Ring (RingQuot (GameAlgebraRel G)))

@[no_expose] instance : Algebra ℂ G.GameAlgebra :=
  inferInstanceAs (Algebra ℂ (RingQuot (GameAlgebraRel G)))

@[no_expose] instance : StarRing G.GameAlgebra :=
  RingQuot.starRing _ (fun _ _ => GameAlgebraRel.adjoint)

private def quotient : Raw →ₐ[ℂ] G.GameAlgebra :=
  RingQuot.mkAlgHom ℂ (GameAlgebraRel G)

/-- The generator associated to question `x` and answer `a`. -/
def effect (x : X) (a : A) : G.GameAlgebra :=
  quotient G (FreeSelfAdjoint.of (x, a))

private theorem star_quotient (v : Raw) :
    star (quotient G v) = quotient G (star v) := by
  rfl

instance : StarModule ℂ G.GameAlgebra where
  star_smul r z := by
    obtain ⟨v, rfl⟩ := RingQuot.mkAlgHom_surjective ℂ (GameAlgebraRel G) z
    change star (r • quotient G v) = star r • star (quotient G v)
    rw [← map_smul, star_quotient, star_smul, map_smul, star_quotient]

@[simp] theorem star_effect (x : X) (a : A) :
    star (effect G x a) = effect G x a := by
  unfold effect
  rw [star_quotient]
  exact congrArg (quotient G) (FreeSelfAdjoint.star_of (x, a))

@[simp] theorem effect_mul_self (x : X) (a : A) :
    effect G x a * effect G x a = effect G x a := by
  unfold effect
  rw [← map_mul]
  exact RingQuot.mkAlgHom_rel ℂ (GameAlgebraRel.projective x a : GameAlgebraRel G _ _)

theorem sum_effect (x : X) : ∑ a, effect G x a = 1 := by
  simp only [effect, ← map_sum, ← map_one (quotient G)]
  exact RingQuot.mkAlgHom_rel ℂ (GameAlgebraRel.normalized x : GameAlgebraRel G _ _)

theorem effect_mul_eq_zero_of_rejected (x y : X) (a b : A) (h : ¬ G.accepts x y a b) :
    effect G x a * effect G y b = 0 := by
  simp only [effect, ← map_mul, ← map_zero (quotient G)]
  exact RingQuot.mkAlgHom_rel ℂ (GameAlgebraRel.rejected x y a b h)

variable {B : Type*} [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]

private theorem lift_rel (P : X → A → B) (hs : ∀ x a, IsSelfAdjoint (P x a))
    (hp : ∀ x a, P x a * P x a = P x a) (hn : ∀ x, ∑ a, P x a = 1)
    (hr : ∀ x y a b, ¬ G.accepts x y a b → P x a * P y b = 0) {v w}
    (h : GameAlgebraRel G v w) :
    FreeSelfAdjoint.lift (fun p : X × A => P p.1 p.2) (fun p => hs p.1 p.2) v =
    FreeSelfAdjoint.lift (fun p : X × A => P p.1 p.2) (fun p => hs p.1 p.2) w := by
  induction h with
  | projective x a => simpa only [map_mul, FreeSelfAdjoint.lift_of] using hp x a
  | normalized x => simpa only [map_sum, map_one, FreeSelfAdjoint.lift_of] using hn x
  | rejected x y a b h =>
    simpa only [map_mul, map_zero, FreeSelfAdjoint.lift_of] using hr x y a b h
  | adjoint _ ih => simp only [map_star, ih]

/-- The star representation given by a self-adjoint assignment satisfying the game relations. -/
def lift (P : X → A → B) (hs : ∀ x a, IsSelfAdjoint (P x a))
    (hp : ∀ x a, P x a * P x a = P x a) (hn : ∀ x, ∑ a, P x a = 1)
    (hr : ∀ x y a b, ¬ G.accepts x y a b → P x a * P y b = 0) : G.GameAlgebra →⋆ₐ[ℂ] B where
  __ := RingQuot.liftAlgHom ℂ ⟨(FreeSelfAdjoint.lift (fun p : X × A => P p.1 p.2)
      (fun p => hs p.1 p.2)).toAlgHom, fun _ _ => lift_rel G P hs hp hn hr⟩
  map_star' z := by
    obtain ⟨v, rfl⟩ := RingQuot.mkAlgHom_surjective ℂ (GameAlgebraRel G) z
    let f : Raw →⋆ₐ[ℂ] B :=
      FreeSelfAdjoint.lift (fun p : X × A => P p.1 p.2) (fun p => hs p.1 p.2)
    let F : G.GameAlgebra →ₐ[ℂ] B :=
      RingQuot.liftAlgHom ℂ ⟨f.toAlgHom, fun _ _ => lift_rel G P hs hp hn hr⟩
    change F (star (quotient G v)) = star (F (quotient G v))
    rw [star_quotient]
    change (RingQuot.liftAlgHom ℂ ⟨f.toAlgHom, _⟩) (RingQuot.mkAlgHom ℂ _ (star v)) =
      star ((RingQuot.liftAlgHom ℂ ⟨f.toAlgHom, _⟩) (RingQuot.mkAlgHom ℂ _ v))
    simp only [RingQuot.liftAlgHom_mkAlgHom_apply, StarAlgHom.coe_toAlgHom, map_star]

@[simp] theorem lift_effect (P : X → A → B) (hs : ∀ x a, IsSelfAdjoint (P x a))
    (hp : ∀ x a, P x a * P x a = P x a) (hn : ∀ x, ∑ a, P x a = 1)
    (hr : ∀ x y a b, ¬ G.accepts x y a b → P x a * P y b = 0) (x : X) (a : A) :
    lift G P hs hp hn hr (effect G x a) = P x a := by
  let f : Raw →⋆ₐ[ℂ] B :=
    FreeSelfAdjoint.lift (fun p : X × A => P p.1 p.2) (fun p => hs p.1 p.2)
  change (RingQuot.liftAlgHom ℂ ⟨f.toAlgHom, _⟩)
    (RingQuot.mkAlgHom ℂ (GameAlgebraRel G) (FreeSelfAdjoint.of (x, a))) = P x a
  rw [RingQuot.liftAlgHom_mkAlgHom_apply, StarAlgHom.coe_toAlgHom]
  exact FreeSelfAdjoint.lift_of _ _ (x, a)

omit [StarModule ℂ B] in
/-- Representations agreeing on the projection generators agree everywhere. -/
@[ext] theorem hom_ext {f g : G.GameAlgebra →⋆ₐ[ℂ] B}
    (h : ∀ x a, f (effect G x a) = g (effect G x a)) : f = g := by
  let q : Raw →⋆ₐ[ℂ] G.GameAlgebra :=
    { __ := quotient G
      map_star' := fun a => (star_quotient G a).symm }
  have he : f.comp q = g.comp q := FreeSelfAdjoint.hom_ext fun (x, a) => h x a
  apply DFunLike.ext
  intro z
  obtain ⟨v, rfl⟩ := RingQuot.mkAlgHom_surjective ℂ (GameAlgebraRel G) z
  exact DFunLike.congr_fun he v

end GameAlgebra

end Cslib.PCP.TwoProverGame
