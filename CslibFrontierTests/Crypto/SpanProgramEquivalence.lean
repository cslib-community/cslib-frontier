/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.LinearEquivalence
public import Mathlib.Algebra.Field.ZMod
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Data.Fin.VecNotation

/-!
# Equivalent monotone span programs: checked instances

Checks of Lemma 22.15 and Definition 22.23 ([BonehShoup2023], pp. 981–982) over `ZMod 5`:

* the two-out-of-three program of Example 22.2 multiplied by an invertible matrix with top row
  `e₁` accepts the same coalition and gives the same distribution of shares;
* each hypothesis of Lemma 22.15 is needed: an invertible `R` whose top row is not `e₁`, and a
  singular `R` whose top row is `e₁`, each change the distribution of shares, and each changes
  the accepted coalitions of some program;
* Definition 22.23 compares programs with different numbers of columns.
-/

public section

namespace CslibFrontierTests.SpanProgramEquivalence

open Cslib.Circuits Cslib.Crypto.Protocols.SecretSharing
open Cslib.Probability Cslib.Probability.PMF
open scoped Matrix

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Example 22.2 ([BonehShoup2023], p. 979) with `t = 2`, `N = 3`, `q = 5`: party `i` holds the
row `(1, i + 1)`. -/
def shamir23 : MonotoneSpanProgram (ZMod 5) (Fin 3) where
  tailDim := 1
  rowDim := fun _ => 1
  matrix i := !![1, (i.val + 1 : ZMod 5)]

/-- The coalition `{0, 1}` is accepted, with weights `2` and `4`. -/
theorem shamir23_accepts_01 : shamir23.Accepts {0, 1} := by
  rw [MonotoneSpanProgram.accepts_iff_exists_vecMul]
  let w : (i : ({0, 1} : Finset (Fin 3))) → Fin (shamir23.rowDim i.val) → ZMod 5 :=
    fun i => match i with
      | ⟨0, _⟩ => ![2]
      | ⟨1, _⟩ => ![4]
  refine ⟨w, ?_⟩
  ext j
  fin_cases j <;> decide

/-- An invertible matrix with top row `e₁`: it adds three times the first coordinate to the
second. -/
def shear : Matrix (Fin 2) (Fin 2) (ZMod 5) := !![1, 0; 3, 1]

/-- `shear` is invertible: its determinant is `1`. -/
theorem isUnit_det_shear : IsUnit shear.det := by
  rw [shear, Matrix.det_fin_two_of]
  exact IsUnit.mk0 _ (by decide)

/-- The top row of `shear` is `e₁`. -/
theorem shear_zero : shear 0 = Pi.single 0 1 := by
  funext c
  fin_cases c <;> rfl

/-- `accepts_mulRight`: the program with matrices `M_i * shear` accepts the coalition `{0, 1}`
that the two-out-of-three program accepts. -/
example : (shamir23.mulRight shear).Accepts {0, 1} :=
  (shamir23.accepts_mulRight isUnit_det_shear shear_zero _).2 shamir23_accepts_01

/-- Lemma 22.15 on the two-out-of-three program: multiplying by `shear` gives an equivalent
program. -/
example (secret : ZMod 5) :
    (linearUniformAccessScheme (shamir23.mulRight shear)).shareDist
        (uniformOfFintype (LinearKey (shamir23.mulRight shear))) secret =
      (linearUniformAccessScheme shamir23).shareDist (uniformOfFintype (LinearKey shamir23))
        secret :=
  shareDist_linearUniformAccessScheme_mulRight shamir23 isUnit_det_shear shear_zero secret

/-- One party holding the row `(1)`: the share is the secret. -/
def unitProgram : MonotoneSpanProgram (ZMod 5) (Fin 1) := ⟨0, fun _ => 1, fun _ => !![1]⟩

/-- One party holding the row `(0, 1)`: the share is the random field element `ρ₂`. -/
def maskProgram : MonotoneSpanProgram (ZMod 5) (Fin 1) := ⟨1, fun _ => 1, fun _ => !![0, 1]⟩

/-- One party holding the row `(1, 0)`: the share is the secret, as for `unitProgram`. -/
def paddedProgram : MonotoneSpanProgram (ZMod 5) (Fin 1) := ⟨1, fun _ => 1, fun _ => !![1, 0]⟩

/-- **Definition 22.23 compares programs with different numbers of columns.** The equation of
share distributions needs the same row dimensions and nothing about the number of columns:
`unitProgram` has one column, `paddedProgram` two, and they are equivalent. -/
example (secret : ZMod 5) :
    (linearUniformAccessScheme paddedProgram).shareDist
        (uniformOfFintype (LinearKey paddedProgram)) secret =
      (linearUniformAccessScheme unitProgram).shareDist
        (uniformOfFintype (LinearKey unitProgram)) secret := by
  have e₁ : ∀ (k : Fin 1 → ZMod 5) (row : Fin 1),
      ((!![1, 0] : Matrix (Fin 1) (Fin 2) (ZMod 5)) *ᵥ
        (Fin.cons secret k : Fin 2 → ZMod 5)) row = secret := by
    intro k row
    fin_cases row
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have e₂ : ∀ (k : Fin 0 → ZMod 5) (row : Fin 1),
      ((!![1] : Matrix (Fin 1) (Fin 1) (ZMod 5)) *ᵥ
        (Fin.cons secret k : Fin 1 → ZMod 5)) row = secret := by
    intro k row
    fin_cases row
    simp [Matrix.mulVec, dotProduct]
  have h₁ : (fun k : LinearKey paddedProgram => linearShare paddedProgram k secret) =
      Function.const _ fun _ _ => secret :=
    funext fun k => funext fun _ => funext fun row => e₁ k row
  have h₂ : (fun k : LinearKey unitProgram => linearShare unitProgram k secret) =
      Function.const _ fun _ _ => secret :=
    funext fun k => funext fun _ => funext fun row => e₂ k row
  change (uniformOfFintype _).map (fun k => linearShare paddedProgram k secret) =
    (uniformOfFintype _).map (fun k => linearShare unitProgram k secret)
  rw [h₁, h₂, PMF.map_const, PMF.map_const]
  rfl

/-- **Lemma 22.15 needs the top row `e₁`.** For `M = (1)` and the invertible `R = (2)` over
`ZMod 5` the share is `2 * secret` instead of `secret`. -/
example : IsUnit (!![2] : Matrix (Fin 1) (Fin 1) (ZMod 5)).det ∧
    (linearUniformAccessScheme (unitProgram.mulRight !![2])).shareDist
        (uniformOfFintype (LinearKey (unitProgram.mulRight !![2]))) 1 ≠
      (linearUniformAccessScheme unitProgram).shareDist
        (uniformOfFintype (LinearKey unitProgram)) 1 := by
  refine ⟨?_, fun h => ?_⟩
  · rw [Matrix.det_fin_one]
    exact IsUnit.mk0 _ (by decide)
  · have hmem : (fun _ _ => (1 : ZMod 5)) ∈ ((linearUniformAccessScheme unitProgram).shareDist
        (uniformOfFintype (LinearKey unitProgram)) 1).support := by
      refine (PMF.mem_support_map_iff _ _ _).2
        ⟨fun i => i.elim0, mem_support_uniformOfFintype _, ?_⟩
      funext i row
      fin_cases i
      fin_cases row
      decide
    rw [← h] at hmem
    obtain ⟨k, -, hk⟩ := (PMF.mem_support_map_iff _ _ _).1 hmem
    have h2 : linearShare (unitProgram.mulRight !![2]) k 1 0 (0 : Fin 1) = 1 :=
      congrFun (congrFun hk 0) (0 : Fin 1)
    have e : ∀ k' : Fin 0 → ZMod 5,
        ((!![1] * !![2] : Matrix (Fin 1) (Fin 1) (ZMod 5)) *ᵥ
          (Fin.cons 1 k' : Fin 1 → ZMod 5)) 0 = 2 := by
      intro k'
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    exact absurd ((e k).symm.trans h2) (by decide)

/-- **Lemma 22.15 needs an invertible matrix.** For `M = (0, 1)` and the singular matrix `R`
with rows `e₁` and `0` over `ZMod 5` the share is `0` instead of the uniform `ρ₂`. -/
example : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 = Pi.single 0 1 ∧
    (linearUniformAccessScheme (maskProgram.mulRight !![1, 0; 0, 0])).shareDist
        (uniformOfFintype (LinearKey (maskProgram.mulRight !![1, 0; 0, 0]))) 0 ≠
      (linearUniformAccessScheme maskProgram).shareDist
        (uniformOfFintype (LinearKey maskProgram)) 0 := by
  refine ⟨?_, fun h => ?_⟩
  · funext c
    fin_cases c <;> rfl
  · have hmem : (fun _ _ => (1 : ZMod 5)) ∈ ((linearUniformAccessScheme maskProgram).shareDist
        (uniformOfFintype (LinearKey maskProgram)) 0).support := by
      refine (PMF.mem_support_map_iff _ _ _).2 ⟨![1], mem_support_uniformOfFintype _, ?_⟩
      funext i row
      fin_cases i
      fin_cases row
      decide
    rw [← h] at hmem
    obtain ⟨k, -, hk⟩ := (PMF.mem_support_map_iff _ _ _).1 hmem
    have h2 : linearShare (maskProgram.mulRight !![1, 0; 0, 0]) k 0 0 (0 : Fin 1) = 1 :=
      congrFun (congrFun hk 0) (0 : Fin 1)
    have e : ∀ k' : Fin 1 → ZMod 5,
        (((!![0, 1] : Matrix (Fin 1) (Fin 2) (ZMod 5)) *
            (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (ZMod 5))) *ᵥ
          (Fin.cons 0 k' : Fin 2 → ZMod 5)) 0 = 0 := by
      intro k'
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_succ]
    exact absurd ((e k).symm.trans h2) (by decide)

/-- One party holding the row `(1, 1)`. -/
def onesProgram : MonotoneSpanProgram (ZMod 5) (Fin 1) := ⟨1, fun _ => 1, fun _ => !![1, 1]⟩

/-- `accepts_mulRight` needs an invertible `R`: with the singular `R` of rows `e₁` and `0`, the
program `(1, 1) * R = (1, 0)` accepts `{0}` and `(1, 1)` does not. -/
example : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 = Pi.single 0 1 ∧
    (onesProgram.mulRight !![1, 0; 0, 0]).Accepts {0} ∧ ¬ onesProgram.Accepts {0} := by
  refine ⟨?_, ?_, ?_⟩
  · funext c
    fin_cases c <;> rfl
  · rw [MonotoneSpanProgram.accepts_iff_exists_vecMul]
    refine ⟨fun _ => ![1], ?_⟩
    ext j
    fin_cases j <;> decide
  · exact onesProgram.not_accepts_of_exists_nullVector ![1, 4] rfl (by decide)

/-- `accepts_mulRight` needs the top row `e₁`: with the invertible swap matrix, `(1, 0)` accepts
`{0}` and `(1, 0) * R = (0, 1)` does not. -/
example : IsUnit (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 5)).det ∧
    paddedProgram.Accepts {0} ∧ ¬ (paddedProgram.mulRight !![0, 1; 1, 0]).Accepts {0} := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    exact IsUnit.mk0 _ (by decide)
  · rw [MonotoneSpanProgram.accepts_iff_exists_vecMul]
    refine ⟨fun _ => ![1], ?_⟩
    ext j
    fin_cases j <;> decide
  · exact (paddedProgram.mulRight !![0, 1; 1, 0]).not_accepts_of_exists_nullVector ![1, 0] rfl
      (by decide)

end CslibFrontierTests.SpanProgramEquivalence
