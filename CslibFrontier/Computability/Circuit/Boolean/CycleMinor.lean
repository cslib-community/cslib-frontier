/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.MultilinearExtension
public import CslibFrontier.Foundations.Data.Matrix.HamiltonianCycle
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import CslibFrontier.Foundations.Data.MvPolynomial.DisjointVars
import CslibFrontier.Foundations.Data.MvPolynomial.LowestComponent

/-!
# The cycle-and-minor function

The *cycle-and-minor function* reads a bit `b`, a vector `x : Fin d → Bool` and a `d × d` Boolean
matrix `Y`. For `b = 0` it tests whether `Y` is the permutation matrix of a single cycle through all
indices (`Cslib.Circuits.IsCycleMatrix`); for `b = 1` it computes the determinant over `F₂` of the
minor of `Y` on its first `d / 2` rows and on the columns where `x` is one, and is zero unless there
are `d / 2` of them (`Cslib.Circuits.minorBit`). It is the hard function of the lower bounds tracked
by #8623.

Each branch has a multilinear representative:

* **The cycle branch** (`Cslib.Circuits.cyclePoly`) is the sum of the indicator polynomials of the
  cycle matrices. Its homogeneous component of degree `d` is the Hamiltonian cycle sum of the
  generic matrix (`Cslib.Circuits.homogeneousComponent_cyclePoly`): from the indicator
  `∏ (i, j), (if σ i = j then X (i, j) else 1 - X (i, j))` of the matrix of a cycle `σ` it keeps
  `∏ i, X (i, σ i)`.
* **The minor branch** (`Cslib.Circuits.minorPoly`) is the determinant of the generic minor. It is
  multilinear (`Cslib.Circuits.minorPoly_mem_restrictDegree`), agrees with the minor bit on the
  Boolean points in characteristic two (`Cslib.Circuits.eval_bitPoint_minorPoly`), and at the
  matrix whose first `d / 2` rows are `C` and whose other rows are zero it is the minor of `C` on
  the columns of `x` (`Cslib.Circuits.eval_padRows_minorPoly`).

## Main definitions

* `Cslib.Circuits.IsCycleMatrix`, `Cslib.Circuits.minorBit`, `Cslib.Circuits.cycleMinor`: the two
  branches and the cycle-and-minor function.
* `Cslib.Circuits.cyclePoly`, `Cslib.Circuits.minorPoly`: their multilinear representatives.
* `Cslib.Circuits.CycleMinor.permBoolMatrix`, `Cslib.Circuits.CycleMinor.selected`,
  `Cslib.Circuits.CycleMinor.padRows`: the permutation matrix of a permutation, the coordinates
  where a vector is one, and the matrix whose first `d / 2` rows are those of a given matrix.

## Main results

* `Cslib.Circuits.isCycleMatrix_permBoolMatrix_iff`, `Cslib.Circuits.minorBit_of_card_ne`,
  `Cslib.Circuits.minorBit_eq_det`: evaluating the two branches.
* `Cslib.Circuits.homogeneousComponent_cyclePoly`: the Hamiltonian cycle sum is the component of
  degree `d` of the cycle branch.
* `Cslib.Circuits.minorPoly_mem_restrictDegree`, `Cslib.Circuits.eval_bitPoint_minorPoly`,
  `Cslib.Circuits.eval_padRows_minorPoly`: the minor branch.
-/

public section

namespace Cslib.Circuits

open MvPolynomial BitString Equiv Finset

variable {d : ℕ}

/-! ### The function -/

namespace CycleMinor

/-- The permutation matrix of `σ`, with entry `(i, j)` true when `σ i = j`. -/
@[expose]
def permBoolMatrix (σ : Perm (Fin d)) : Fin d × Fin d → Bool :=
  fun v => decide (σ v.1 = v.2)

/-- The coordinates where `x` is one. -/
@[expose]
def selected (x : Fin d → Bool) : Finset (Fin d) :=
  univ.filter fun i => x i = true

@[simp] theorem mem_selected {x : Fin d → Bool} {i : Fin d} : i ∈ selected x ↔ x i = true := by
  simp [selected]

end CycleMinor

open CycleMinor

private theorem permBoolMatrix_injective : Function.Injective (permBoolMatrix (d := d)) := by
  intro σ τ h
  ext i
  have := congrFun h (i, σ i)
  simp only [permBoolMatrix, decide_true] at this
  have h' : τ i = σ i := of_decide_eq_true this.symm
  exact congrArg Fin.val h'.symm

/-- A Boolean matrix is a *cycle matrix* when it is the permutation matrix of a single cycle through
all indices. -/
@[expose]
def IsCycleMatrix (Y : Fin d × Fin d → Bool) : Prop :=
  ∃ σ : Perm (Fin d), σ.IsCycleOn Set.univ ∧ permBoolMatrix σ = Y

/-- The matrix of a permutation is a cycle matrix exactly when the permutation is a single cycle
through all indices. -/
@[simp] theorem isCycleMatrix_permBoolMatrix_iff (σ : Perm (Fin d)) :
    IsCycleMatrix (permBoolMatrix σ) ↔ σ.IsCycleOn Set.univ :=
  ⟨fun ⟨_, hτ, h⟩ => permBoolMatrix_injective h ▸ hτ, fun h => ⟨σ, h, rfl⟩⟩

/-- The *minor bit*: the determinant over `F₂` of the minor of `Y` on its first `d / 2` rows and on
the columns where `x` is one, or `0` unless there are `d / 2` of them. -/
@[expose]
noncomputable def minorBit (x : Fin d → Bool) (Y : Fin d × Fin d → Bool) : Bool :=
  if h : (selected x).card = d / 2 then
    decide ((Matrix.of fun r c => bitVal (ZMod 2)
      (Y (Fin.castLE (Nat.div_le_self d 2) r, (selected x).orderEmbOfFin h c))).det ≠ 0)
  else false

/-- The minor bit is zero unless `x` selects `d / 2` columns. -/
@[simp] theorem minorBit_of_card_ne {x : Fin d → Bool} (Y : Fin d × Fin d → Bool)
    (h : (selected x).card ≠ d / 2) : minorBit x Y = false := by
  simp [minorBit, h]

/-- The minor bit through any increasing enumeration `f` of the `d / 2` columns that `x`
selects. -/
theorem minorBit_eq_det {x : Fin d → Bool} (Y : Fin d × Fin d → Bool) (f : Fin (d / 2) ↪o Fin d)
    (hf : ∀ c, x (f c) = true) (h : (selected x).card = d / 2) :
    minorBit x Y = decide ((Matrix.of fun r c => bitVal (ZMod 2)
      (Y (Fin.castLE (Nat.div_le_self d 2) r, f c))).det ≠ 0) := by
  simp only [minorBit, h, ↓reduceDIte]
  rw [← orderEmbOfFin_unique' h fun c => mem_selected.mpr (hf c)]

/-- The *cycle-and-minor function*: for `b = 0` whether `Y` is a cycle matrix, for `b = 1` the minor
bit. -/
noncomputable def cycleMinor (b : Bool) (x : Fin d → Bool) (Y : Fin d × Fin d → Bool) : Bool :=
  open Classical in
  if b then minorBit x Y else decide (IsCycleMatrix Y)

/-- For `b = 1` the function is the minor bit. -/
@[simp] theorem cycleMinor_true (x : Fin d → Bool) (Y : Fin d × Fin d → Bool) :
    cycleMinor true x Y = minorBit x Y := by
  simp [cycleMinor]

/-- For `b = 0` the function tests whether `Y` is a cycle matrix. -/
@[simp] theorem cycleMinor_false (x : Fin d → Bool) (Y : Fin d × Fin d → Bool) :
    cycleMinor false x Y = open Classical in decide (IsCycleMatrix Y) := by
  simp [cycleMinor]

/-! ### Products of distinct variables -/

/-- A product of distinct variables is multilinear. -/
private theorem prod_X_mem_restrictDegree {ι σ R : Type*} [CommRing R] (s : Finset ι) {f : ι → σ}
    (hf : Set.InjOn f s) : (∏ i ∈ s, X (f i) : MvPolynomial σ R) ∈ restrictDegree σ R 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using C_mem_restrictDegree (σ := σ) 1 (1 : R)
  | insert a s ha ih =>
    rw [prod_insert ha]
    refine mul_mem_restrictDegree_of_disjoint_vars (X_mem_restrictDegree le_rfl _)
      (ih (hf.mono (subset_insert a s))) ?_
    refine Finset.disjoint_left.mpr fun v hva hvs => ?_
    rw [Finset.mem_singleton.mp (vars_X_subset _ hva)] at hvs
    obtain ⟨i, hi, hfi⟩ := Finset.mem_biUnion.mp (vars_prod _ hvs)
    have hfi : f a = f i := Finset.mem_singleton.mp (vars_X_subset _ hfi)
    exact ha (hf (mem_insert_self a s) (mem_insert_of_mem hi) hfi ▸ hi)

/-! ### The minor branch -/

variable (K : Type*) [CommRing K]

/-- The *generic minor*: the determinant of the minor of the generic matrix on its first `d / 2`
rows and on the columns where `x` is one, or `0` unless there are `d / 2` of them. -/
noncomputable def minorPoly (x : Fin d → Bool) : MvPolynomial (Fin d × Fin d) K :=
  if h : (selected x).card = d / 2 then
    (Matrix.of fun r c =>
      (X (Fin.castLE (Nat.div_le_self d 2) r, (selected x).orderEmbOfFin h c) :
        MvPolynomial _ K)).det
  else 0

variable {K}

/-- The generic minor is multilinear: each term of the determinant is a product of distinct
variables. -/
theorem minorPoly_mem_restrictDegree (x : Fin d → Bool) :
    minorPoly K x ∈ restrictDegree (Fin d × Fin d) K 1 := by
  unfold minorPoly
  split_ifs with h
  · rw [Matrix.det_apply]
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [Units.smul_def]
    refine zsmul_mem (prod_X_mem_restrictDegree univ fun i _ j _ hij => ?_) _
    exact (selected x).orderEmbOfFin h |>.injective (congrArg Prod.snd hij)
  · exact Submodule.zero_mem _

/-- **The minor branch on the Boolean points.** In characteristic two the generic minor at a
Boolean matrix is the minor bit. -/
theorem eval_bitPoint_minorPoly [CharP K 2] (x : Fin d → Bool) (Y : Fin d × Fin d → Bool) :
    eval (bitPoint Y) (minorPoly K x) = bitVal K (minorBit x Y) := by
  unfold minorPoly minorBit
  split_ifs with h
  · let ψ : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
    have hψ (b : Bool) : ψ (bitVal (ZMod 2) b) = bitVal K b := by cases b <;> simp [bitVal, ψ]
    have hdet (D : ZMod 2) : ψ D = bitVal K (decide (D ≠ 0)) := by
      have h01 : ∀ D : ZMod 2, D = 0 ∨ D = 1 := by decide
      rcases h01 D with rfl | rfl <;> simp [bitVal]
    rw [RingHom.map_det, ← hdet, RingHom.map_det]
    congr 1
    ext r c
    simp [hψ]
  · simp [bitVal]

/-- The matrix whose first `d / 2` rows are those of `C` and whose other rows are zero. -/
@[expose]
def CycleMinor.padRows (C : Matrix (Fin (d / 2)) (Fin d) K) : Fin d × Fin d → K :=
  fun v => if h : (v.1 : ℕ) < d / 2 then C ⟨v.1, h⟩ v.2 else 0

/-- **The minor branch at a padded matrix.** At the matrix whose first `d / 2` rows are `C` and
whose other rows are zero, the generic minor is the minor of `C` on the columns where `x` is one,
or `0` unless there are `d / 2` of them. -/
theorem eval_padRows_minorPoly (C : Matrix (Fin (d / 2)) (Fin d) K) (x : Fin d → Bool) :
    eval (padRows C) (minorPoly K x) = if h : (selected x).card = d / 2 then
      (C.submatrix id ((selected x).orderEmbOfFin h)).det else 0 := by
  unfold minorPoly
  split_ifs with h
  · rw [RingHom.map_det]
    congr 1
    ext r c
    simp [padRows, r.isLt]
  · simp

/-! ### The cycle branch -/

variable (K)

/-- The multilinear representative of the cycle branch: the multilinear extension of the
indicator of the cycle matrices. -/
noncomputable def cyclePoly : MvPolynomial (Fin d × Fin d) K :=
  open Classical in
  multilinearExtension fun Y => bitVal K (decide (IsCycleMatrix Y))

variable {K}

/-- The cycle branch is the multilinear extension of the indicator of the cycle matrices. -/
theorem cyclePoly_eq_multilinearExtension : open Classical in
    cyclePoly (d := d) K = multilinearExtension fun Y => bitVal K (decide (IsCycleMatrix Y)) := by
  rw [cyclePoly]

/-- The cycle branch is multilinear. -/
theorem cyclePoly_mem_restrictDegree :
    cyclePoly (d := d) K ∈ restrictDegree (Fin d × Fin d) K 1 :=
  multilinearExtension_mem_restrictDegree _

/-- The cycle branch on the Boolean points is the indicator of the cycle matrices. -/
theorem eval_bitPoint_cyclePoly (Y : Fin d × Fin d → Bool) :
    eval (bitPoint Y) (cyclePoly K) = open Classical in bitVal K (decide (IsCycleMatrix Y)) := by
  classical
  exact eval_multilinearExtension _ Y

/-- The cycle branch is the sum of the indicator polynomials of the matrices of the cycles. -/
private theorem cyclePoly_eq_sum : open Classical in cyclePoly (d := d) K =
    ∑ σ : Perm (Fin d) with σ.IsCycleOn Set.univ, indicatorPoly (permBoolMatrix σ) := by
  classical
  set S := univ.filter fun σ : Perm (Fin d) => σ.IsCycleOn Set.univ
  have hmem (a : Fin d × Fin d → Bool) : IsCycleMatrix a ↔ a ∈ S.image permBoolMatrix := by
    simp [IsCycleMatrix, S]
  unfold cyclePoly multilinearExtension
  calc ∑ a, C (bitVal K (decide (IsCycleMatrix a))) * indicatorPoly a
      = ∑ a, if a ∈ S.image permBoolMatrix then indicatorPoly a else 0 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases h : a ∈ S.image permBoolMatrix <;> simp [h, hmem a, bitVal]
    _ = ∑ a ∈ S.image permBoolMatrix, indicatorPoly a := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ σ ∈ S, indicatorPoly (permBoolMatrix σ) :=
        Finset.sum_image fun σ _ τ _ h => permBoolMatrix_injective h

/-- The component of degree `d` of the indicator polynomial of the matrix of a permutation keeps,
from each row, the variable at the entry of the permutation. -/
private theorem homogeneousComponent_indicatorPoly_permBoolMatrix (σ : Perm (Fin d)) :
    homogeneousComponent d (indicatorPoly (permBoolMatrix σ) : MvPolynomial (Fin d × Fin d) K) =
      ∏ i, X (i, σ i) := by
  classical
  set T := univ.filter fun v : Fin d × Fin d => permBoolMatrix σ v = true
  have hT : T = univ.image fun i => (i, σ i) := by
    ext ⟨i, j⟩
    simp [T, permBoolMatrix, eq_comm]
  have hinj : Function.Injective fun i : Fin d => (i, σ i) := fun i j h => congrArg Prod.fst h
  have hq : (∏ v ∈ T, X v : MvPolynomial (Fin d × Fin d) K) = ∏ i, X (i, σ i) := by
    rw [hT, Finset.prod_image fun i _ j _ h => hinj h]
  have hhom : (∏ i, X (i, σ i) : MvPolynomial (Fin d × Fin d) K) ∈
      homogeneousSubmodule (Fin d × Fin d) K d := by
    have := IsHomogeneous.prod (univ : Finset (Fin d)) (fun i => (X (i, σ i) :
      MvPolynomial (Fin d × Fin d) K)) (fun _ => 1) fun i _ => isHomogeneous_X K (i, σ i)
    simpa using this
  rw [indicatorPoly, Finset.prod_ite, mul_comm]
  change homogeneousComponent d ((∏ v ∈ univ.filter fun v => ¬permBoolMatrix σ v = true,
    (1 - X v)) * ∏ v ∈ T, X v) = _
  rw [hq, homogeneousComponent_mul (fun j hj => by
    rw [homogeneousComponent_of_mem hhom]
    simp [hj.ne]), homogeneousComponent_of_mem hhom]
  simp only [↓reduceIte]
  rw [← constantCoeff_eq, map_prod]
  simp

/-- **The Hamiltonian cycle sum is the component of degree `d` of the cycle branch.** -/
theorem homogeneousComponent_cyclePoly :
    homogeneousComponent d (cyclePoly (d := d) K) =
      (Matrix.of fun i j => (X (i, j) : MvPolynomial (Fin d × Fin d) K)).hamiltonianCycleSum := by
  classical
  rw [cyclePoly_eq_sum, map_sum, Matrix.hamiltonianCycleSum]
  refine Finset.sum_congr (by ext; simp) fun σ _ => ?_
  rw [homogeneousComponent_indicatorPoly_permBoolMatrix]
  rfl

end Cslib.Circuits
