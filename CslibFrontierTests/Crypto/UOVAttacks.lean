/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.UOV.Attacks
public import Mathlib.Algebra.Field.ZMod

/-!
# Clients of the UOV rescaling attack interface

The field with five elements supplies nonidentity squared scalars without invoking UOV parameter
generation. These clients use the public probability-one attack theorems and check a nonzero-tail
instance together with the excluded squared-scalar-one case.
-/

public section

namespace CslibFrontierTests.Crypto.UOVAttacks

open Cslib Cslib.Crypto Cslib.Crypto.UOV Probability

/-- The concrete attack clients use the field with five elements. -/
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def square : QuadraticMap (ZMod 5) (ZMod 5) (ZMod 5) := QuadraticMap.sq

private def squareFront : QuadraticMap (ZMod 5) (ZMod 5) (ZMod 5 × ZMod 5) :=
  (LinearMap.inl (ZMod 5) (ZMod 5) (ZMod 5)).compQuadraticMap square

private def squareBoth : QuadraticMap (ZMod 5) (ZMod 5) (ZMod 5 × ZMod 5) :=
  ((LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5).prod LinearMap.id).compQuadraticMap square

/-- The concrete strategy stays within a one-query external budget. -/
theorem rescaleAttack_queryBound_zmod5 :
    (rescaleAttack (X := ZMod 5) (2 : ZMod 5) (4 : ZMod 5)).IsQueryBounded 1 :=
  rescaleAttack_queryBound _ _

example :
    (ProbComp.eval ((rescaleAttack (X := ZMod 5) (2 : ZMod 5)
      (((2 : ZMod 5) * 2)⁻¹ • (1 : ZMod 5))).runLog (fun _ => pure 2))).map
      (fun result => decide (square result.1 = 1 ∧
        (1 : ZMod 5) ∉ result.2.map Prod.fst ∧ result.2.length = 1)) = PMF.pure true := by
  apply rescaleAttack_freshTarget square 2 1 (by decide) (by decide) (by decide)
  intro answer hmem
  simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hmem
  subst answer
  norm_num [square, QuadraticMap.sq_apply, smul_eq_mul]
  exact (inv_eq_of_mul_eq_one_left (by decide : (4 : ZMod 5) * 4 = 1)).symm

example :
    (ProbComp.eval ((rescaleAttack (X := ZMod 5) (2 : ZMod 5)
      ((1 : ZMod 5), (0 : ZMod 5))).runLog (fun _ => pure 1))).map
      (fun result => decide
        (squareFront result.1 =
          structuredTarget (fun _ : ZMod 5 => (0 : ZMod 5)) (fun _ => (0 : ZMod 5))
            (((2 : ZMod 5) * 2) • (1 : ZMod 5)) 0 ∧
          ((2 : ZMod 5) * 2) • (1 : ZMod 5) ∉
            result.2.map (fun ((message, _), _) => message) ∧
          result.2.length = 1)) = PMF.pure true := by
  apply rescaleAttack_zeroOpening squareFront (fun _ => 0) (fun _ => 0)
    rfl rfl 2 (by decide) 1 (by decide)
  intro answer hmem
  simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hmem
  subst answer
  decide

example (message : ZMod 5) :
    squareBoth ((2 : ZMod 5) • (1 : ZMod 5)) ≠
      structuredTarget (fun _ : ZMod 5 => (0 : ZMod 5)) (fun _ => (1 : ZMod 5)) message 0 :=
  rescale_ne_zeroOpening_of_tail_ne_zero (K := ZMod 5) (X := ZMod 5)
    (Message := ZMod 5) (Tail := ZMod 5) (Opening := ZMod 5)
    squareBoth (fun _ => 0) (fun _ => 1) (by decide) 2 (by decide)
    (answer := 1) (message := 1) (by decide) message

/-- The excluded square-one case really does preserve the nonzero tail. -/
example :
    squareBoth ((-1 : ZMod 5) • (1 : ZMod 5)) =
      structuredTarget (fun _ : ZMod 5 => (0 : ZMod 5)) (fun _ => (1 : ZMod 5)) 1 0 := by
  decide

end CslibFrontierTests.Crypto.UOVAttacks
