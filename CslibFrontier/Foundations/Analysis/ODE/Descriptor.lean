/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Analysis/ODE/Descriptor.lean`)

public import CslibFrontier.Foundations.Analysis.ODE.LinearLyapunov
public import CslibFrontier.Foundations.Analysis.ODE.StateSpace
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Linear descriptor systems and their index-one decoupling

A *descriptor system* (differential-algebraic equation) `E ż = F z + G u + b` has square real
matrices `E` and `F` over an index type `ι` of unknowns, an input matrix `G` and a constant term
`b`. Nothing is assumed about `E`: it is singular for every electrical circuit with a resistor
or a source, and the rows it annihilates are algebraic constraints. A solution on a time set `s`
is a curve `z` such that `E z` (not necessarily `z`) has derivative `F z + G u + b` within `s`
(`DescriptorSystem.IsSolutionOn`). An algebraic component of `z` therefore needs no
differentiability, and follows the input `u` instantaneously.

## Index-one decoupling

`DescriptorSystem.IndexOneDecoupling S κ ρ` consists of matrices `P = [P₁; P₂]` (row operations)
and `Q = [Q₁ Q₂]` (a change of unknowns `z = Q₁ x + Q₂ y`) bringing the pencil into the form

  `P E Q = [[1, 0], [0, 0]]`,  `P F Q = [[A, 0], [0, 1]]`,

with `P` left invertible (`P₁' P₁ + P₂' P₂ = 1`) and `Q` invertible (`Q₁ Q₁' + Q₂ Q₂' = 1`,
`Q₁' Q₁ = 1`, `Q₁' Q₂ = 0`). This is the Weierstrass form of a pencil with a zero nilpotent part,
i.e. of index at most one. Then `S` decouples into the ODE `ẋ = A x + B u + c` on the
differential coordinates `x = Q₁' z`, with `B = P₁ G` and `c = P₁ b`, and the algebraic
equation `y = -P₂ (G u + b)`, which has a unique solution for every input value. Every quantity
is recovered: `z = Q₁ x - Q₂ P₂ (G u + b)` (`IndexOneDecoupling.reconstruct`). Nothing is
discarded; the theorems below are an exact correspondence between solutions of `S` and of the
ODE, with existence and uniqueness for every consistent initial state.

The decoupling is data, so an untrusted tool can find it and a checker can verify its identities
exactly (`Cslib.LinearAlgebra.DecouplingCert`). A system that has no decoupling of this form, for
example one of higher index, whose solutions depend on derivatives of the input, or one whose
algebraic part is singular, is outside the supported class; no claim is made about it.

## Stability

`DescriptorSystem.IsExponentiallyStableAt S z₀` says that all solutions with zero input converge
to `z₀` exponentially, uniformly, in the Euclidean norm of the full vector of unknowns. On its own
this would hold vacuously for an inconsistent model without solutions, so the theorems that prove
it also give the constant solution `z₀` (`IsEquilibrium.isSolutionOn`) and a solution through
every consistent initial state (`IndexOneDecoupling.exists_isSolutionOn_Ici_iff`).

## Main definitions

* `DescriptorSystem ι m`: the data `E`, `F`, `G`, `b` of `E ż = F z + G u + b`.
* `DescriptorSystem.IsSolutionOn`, `DescriptorSystem.IsEquilibrium`,
  `DescriptorSystem.deviation`, `DescriptorSystem.IsExponentiallyStableAt`.
* `DescriptorSystem.IndexOneDecoupling`, with the reduced matrices `A`, `B`, `c`, the
  reconstruction `reconstruct` and the realization `realization H` for an output map `H`.

## Main results

* `DescriptorSystem.IsEquilibrium.isSolutionOn_iff`: deviations from an equilibrium solve the
  system with `b = 0`.
* `DescriptorSystem.IndexOneDecoupling.isSolutionOn_iff`: `z` solves `S` exactly when it is
  reconstructed from `x = Q₁' z` and the input, and `x` solves `ẋ = A x + B u + c`.
* `DescriptorSystem.IndexOneDecoupling.isSolutionOn_reconstruct`: conversely every solution of
  the ODE yields a solution of `S`.
* `DescriptorSystem.IndexOneDecoupling.exists_isSolutionOn_Ici_iff`: for continuous inputs, an
  initial state `z₀` starts a solution on `[0, ∞)` exactly when it satisfies the algebraic
  constraint `z₀ = reconstruct (Q₁' z₀) (u 0)`.
* `DescriptorSystem.IndexOneDecoupling.eqOn_of_isSolutionOn_Ici`: uniqueness of solutions with a
  given input and initial state.
* `DescriptorSystem.IndexOneDecoupling.isSolutionOn_iff_realization`: after the equilibrium
  shift, solutions of `S` are the solutions of the proper realization
  `ẋ = A x + B u`, `y = (H Q₁) x - (H Q₂ P₂ G) u` with output `H (z - z₀)`.
* `DescriptorSystem.IndexOneDecoupling.isExponentiallyStableAt`: if `ẋ = A x` is exponentially
  stable, so is every equilibrium of `S`.
-/

public section

open Set Matrix

/-- A linear time-invariant descriptor system `E ż = F z + G u + b`, with unknowns indexed by
`ι` and inputs indexed by `m`. `E` may be singular. -/
structure DescriptorSystem (ι m : Type*) where
  /-- The matrix of the derivative terms. -/
  E : Matrix ι ι ℝ
  /-- The matrix of the undifferentiated terms. -/
  F : Matrix ι ι ℝ
  /-- The input matrix. -/
  G : Matrix ι m ℝ
  /-- The constant term (constant sources). -/
  b : ι → ℝ

namespace DescriptorSystem

variable {ι m : Type*} [Fintype ι] [Fintype m] (S : DescriptorSystem ι m)

/-- `z` solves `E ż = F z + G u + b` on the time set `s`: at each `t ∈ s`, the curve `E z` has
derivative `F z t + G u t + b` within `s`. No differentiability of `z` itself is required. -/
@[expose] def IsSolutionOn (u : ℝ → m → ℝ) (z : ℝ → ι → ℝ) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivWithinAt (fun τ => S.E *ᵥ z τ) (S.F *ᵥ z t + S.G *ᵥ u t + S.b) s t

/-- `z₀` is an equilibrium for zero input: `F z₀ + b = 0`. -/
@[expose] def IsEquilibrium (z₀ : ι → ℝ) : Prop := S.F *ᵥ z₀ + S.b = 0

/-- The deviation system `E ż = F z + G u`, without the constant term. -/
@[expose] def deviation : DescriptorSystem ι m := { S with b := 0 }

/-- `z₀` is (globally, uniformly) exponentially stable: there are constants `M` and `α > 0` such
that every solution with zero input on `[0, ∞)` satisfies
`‖z t - z₀‖ ≤ M * exp (-(α * t)) * ‖z 0 - z₀‖` in the Euclidean norm. This alone is vacuous for a
system without solutions; see the module documentation. -/
@[expose] def IsExponentiallyStableAt (z₀ : ι → ℝ) : Prop :=
  ∃ M α : ℝ, 0 < α ∧ ∀ z : ℝ → ι → ℝ, S.IsSolutionOn 0 z (Ici 0) → ∀ t ≥ 0,
    ‖WithLp.toLp 2 (z t - z₀)‖ ≤ M * Real.exp (-(α * t)) * ‖WithLp.toLp 2 (z 0 - z₀)‖

variable {S}

omit [Fintype m] in
private theorem hasDerivWithinAt_mulVec {κ : Type*} [Fintype κ] (M : Matrix κ ι ℝ)
    {f : ℝ → ι → ℝ} {f' : ι → ℝ} {s : Set ℝ} {t : ℝ} (h : HasDerivWithinAt f f' s t) :
    HasDerivWithinAt (fun τ => M *ᵥ f τ) (M *ᵥ f') s t := by
  refine hasDerivWithinAt_pi.2 fun i => ?_
  simp only [mulVec, dotProduct]
  refine HasDerivWithinAt.fun_sum fun j _ => ?_
  have hj : HasDerivWithinAt (fun τ => f τ j) (f' j) s t := hasDerivWithinAt_pi.1 h j
  exact HasDerivWithinAt.const_mul (M i j) hj

/-- An equilibrium is a constant solution with zero input. -/
theorem IsEquilibrium.isSolutionOn {z₀ : ι → ℝ} (h : S.IsEquilibrium z₀) (s : Set ℝ) :
    S.IsSolutionOn 0 (fun _ => z₀) s := fun t _ => by
  have h' : S.F *ᵥ z₀ + S.b = 0 := h
  rw [Pi.zero_apply, mulVec_zero, add_zero, h']
  exact hasDerivWithinAt_const t s (S.E *ᵥ z₀)

/-- **Deviation dynamics.** If `z₀` is an equilibrium, `z` solves `S` exactly when `z - z₀`
solves the deviation system, with the same input. -/
theorem IsEquilibrium.isSolutionOn_iff {z₀ : ι → ℝ} (h : S.IsEquilibrium z₀)
    {u : ℝ → m → ℝ} {z : ℝ → ι → ℝ} {s : Set ℝ} :
    S.IsSolutionOn u z s ↔ S.deviation.IsSolutionOn u (fun t => z t - z₀) s := by
  have hb : S.b = -(S.F *ᵥ z₀) := eq_neg_of_add_eq_zero_right h
  refine forall₂_congr fun t _ => ?_
  simp only [deviation, mulVec_sub, add_zero]
  rw [hb, show S.F *ᵥ z t - S.F *ᵥ z₀ + S.G *ᵥ u t = S.F *ᵥ z t + S.G *ᵥ u t + -(S.F *ᵥ z₀) by
    abel]
  refine ⟨fun h => h.sub_const _, fun h => ?_⟩
  convert h.add_const (S.E *ᵥ z₀) using 1
  funext τ
  simp

variable (S) in
/-- An index-one decoupling of `S`: row operations `P = [P₁; P₂]` with left inverse
`[P₁' P₂']` and a change of unknowns `z = Q₁ x + Q₂ y` with inverse `[Q₁'; Q₂']`, such that
`P E Q = [[1, 0], [0, 0]]` and `P F Q = [[A, 0], [0, 1]]` for some `A`. The differential
coordinates are indexed by `κ`, the algebraic ones by `ρ`. -/
structure IndexOneDecoupling (κ ρ : Type*) [Fintype κ] [Fintype ρ] [DecidableEq ι]
    [DecidableEq κ] [DecidableEq ρ] where
  /-- Rows producing the differential equations. -/
  P₁ : Matrix κ ι ℝ
  /-- Rows producing the algebraic equations. -/
  P₂ : Matrix ρ ι ℝ
  /-- Left inverse of `P`, first block. -/
  P₁' : Matrix ι κ ℝ
  /-- Left inverse of `P`, second block. -/
  P₂' : Matrix ι ρ ℝ
  /-- Unknowns from the differential coordinates. -/
  Q₁ : Matrix ι κ ℝ
  /-- Unknowns from the algebraic coordinates. -/
  Q₂ : Matrix ι ρ ℝ
  /-- Differential coordinates of the unknowns. -/
  Q₁' : Matrix κ ι ℝ
  /-- Algebraic coordinates of the unknowns. -/
  Q₂' : Matrix ρ ι ℝ
  E₁₁ : P₁ * S.E * Q₁ = 1
  E₁₂ : P₁ * S.E * Q₂ = 0
  E₂₁ : P₂ * S.E * Q₁ = 0
  E₂₂ : P₂ * S.E * Q₂ = 0
  F₁₂ : P₁ * S.F * Q₂ = 0
  F₂₁ : P₂ * S.F * Q₁ = 0
  F₂₂ : P₂ * S.F * Q₂ = 1
  P_inv : P₁' * P₁ + P₂' * P₂ = 1
  Q_inv : Q₁ * Q₁' + Q₂ * Q₂' = 1
  Q₁'_Q₁ : Q₁' * Q₁ = 1
  Q₁'_Q₂ : Q₁' * Q₂ = 0

namespace IndexOneDecoupling

variable {κ ρ : Type*} [Fintype κ] [Fintype ρ] [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ]
  (D : S.IndexOneDecoupling κ ρ)

/-- The state matrix `P₁ F Q₁` of the reduced ODE. -/
@[expose] def A : Matrix κ κ ℝ := D.P₁ * S.F * D.Q₁

/-- The input matrix `P₁ G` of the reduced ODE. -/
@[expose] def B : Matrix κ m ℝ := D.P₁ * S.G

/-- The constant term `P₁ b` of the reduced ODE. -/
@[expose] def c : κ → ℝ := D.P₁ *ᵥ S.b

/-- The unknowns determined by the differential coordinates `x` and the input value `v`:
`Q₁ x - Q₂ P₂ (G v + b)`. -/
@[expose] def reconstruct (x : κ → ℝ) (v : m → ℝ) : ι → ℝ :=
  D.Q₁ *ᵥ x - D.Q₂ *ᵥ (D.P₂ *ᵥ (S.G *ᵥ v + S.b))

/-- The same decoupling, for the deviation system (it only involves `E` and `F`). -/
@[expose] def deviation : S.deviation.IndexOneDecoupling κ ρ :=
  { D with }

variable {D}

omit [Fintype m] in
private theorem decomp (z : ι → ℝ) : z = D.Q₁ *ᵥ (D.Q₁' *ᵥ z) + D.Q₂ *ᵥ (D.Q₂' *ᵥ z) := by
  rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec, D.Q_inv, one_mulVec]

omit [Fintype m] in
private theorem mul_Q_inv {α : Type*} (M : Matrix α ι ℝ) :
    M = M * D.Q₁ * D.Q₁' + M * D.Q₂ * D.Q₂' := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, D.Q_inv, Matrix.mul_one]

omit [Fintype m] in
private theorem E_Q₂ : S.E * D.Q₂ = 0 := by
  rw [← Matrix.one_mul (S.E * D.Q₂), ← D.P_inv, Matrix.add_mul, Matrix.mul_assoc,
    Matrix.mul_assoc, ← Matrix.mul_assoc D.P₁, ← Matrix.mul_assoc D.P₂, D.E₁₂, D.E₂₂,
    Matrix.mul_zero, Matrix.mul_zero, add_zero]

omit [Fintype m] in
/-- `E` factors through the differential coordinates: `E = E Q₁ Q₁'`. In particular `E = 0`
when there are no differential coordinates. -/
theorem E_eq_mul_Q₁_mul_Q₁' : S.E = S.E * D.Q₁ * D.Q₁' := by
  conv_lhs => rw [mul_Q_inv (D := D) S.E]
  rw [E_Q₂, Matrix.zero_mul, add_zero]

omit [Fintype m] in
private theorem E_mulVec (z : ι → ℝ) : S.E *ᵥ z = (S.E * D.Q₁) *ᵥ (D.Q₁' *ᵥ z) := by
  rw [mulVec_mulVec, ← E_eq_mul_Q₁_mul_Q₁']

omit [Fintype m] in
private theorem P₁_E : D.P₁ * S.E = D.Q₁' := by
  rw [E_eq_mul_Q₁_mul_Q₁' (D := D), ← Matrix.mul_assoc, ← Matrix.mul_assoc, D.E₁₁,
    Matrix.one_mul]

omit [Fintype m] in
private theorem P₂_E : D.P₂ * S.E = 0 := by
  rw [E_eq_mul_Q₁_mul_Q₁' (D := D), ← Matrix.mul_assoc, ← Matrix.mul_assoc, D.E₂₁,
    Matrix.zero_mul]

omit [Fintype m] in
private theorem P₁_F : D.P₁ * S.F = D.A * D.Q₁' := by
  rw [mul_Q_inv (D := D) (D.P₁ * S.F), D.F₁₂, Matrix.zero_mul, add_zero, A]

omit [Fintype m] in
private theorem P₂_F : D.P₂ * S.F = D.Q₂' := by
  rw [mul_Q_inv (D := D) (D.P₂ * S.F), D.F₂₁, D.F₂₂, Matrix.zero_mul, zero_add, Matrix.one_mul]

omit [Fintype m] in
private theorem P₁_E_mulVec (z : ι → ℝ) : D.P₁ *ᵥ (S.E *ᵥ z) = D.Q₁' *ᵥ z := by
  rw [mulVec_mulVec, P₁_E]

omit [Fintype m] in
private theorem P₂_E_mulVec (z : ι → ℝ) : D.P₂ *ᵥ (S.E *ᵥ z) = 0 := by
  rw [mulVec_mulVec, P₂_E, zero_mulVec]

omit [Fintype m] in
private theorem P₁_F_mulVec (z : ι → ℝ) : D.P₁ *ᵥ (S.F *ᵥ z) = D.A *ᵥ (D.Q₁' *ᵥ z) := by
  rw [mulVec_mulVec, mulVec_mulVec, P₁_F]

omit [Fintype m] in
private theorem P₂_F_mulVec (z : ι → ℝ) : D.P₂ *ᵥ (S.F *ᵥ z) = D.Q₂' *ᵥ z := by
  rw [mulVec_mulVec, P₂_F]

omit [Fintype m] in
private theorem P₂_F_Q₁ (x : κ → ℝ) : D.P₂ *ᵥ (S.F *ᵥ (D.Q₁ *ᵥ x)) = 0 := by
  rw [mulVec_mulVec, mulVec_mulVec, D.F₂₁, zero_mulVec]

omit [Fintype m] in
private theorem P₂_F_Q₂ (y : ρ → ℝ) : D.P₂ *ᵥ (S.F *ᵥ (D.Q₂ *ᵥ y)) = y := by
  rw [mulVec_mulVec, mulVec_mulVec, D.F₂₂, one_mulVec]

omit [Fintype m] in
private theorem P₁_E_Q₁ (w : κ → ℝ) : D.P₁ *ᵥ ((S.E * D.Q₁) *ᵥ w) = w := by
  rw [mulVec_mulVec, ← Matrix.mul_assoc, D.E₁₁, one_mulVec]

omit [Fintype m] in
private theorem P₂_E_Q₁ (w : κ → ℝ) : D.P₂ *ᵥ ((S.E * D.Q₁) *ᵥ w) = 0 := by
  rw [mulVec_mulVec, ← Matrix.mul_assoc, D.E₂₁, zero_mulVec]

omit [Fintype m] in
private theorem eq_of_P (v : ι → ℝ) : v = D.P₁' *ᵥ (D.P₁ *ᵥ v) + D.P₂' *ᵥ (D.P₂ *ᵥ v) := by
  rw [mulVec_mulVec, mulVec_mulVec, ← add_mulVec, D.P_inv, one_mulVec]

private theorem P₁_rhs (z : ι → ℝ) (v : m → ℝ) :
    D.P₁ *ᵥ (S.F *ᵥ z + S.G *ᵥ v + S.b) = D.A *ᵥ (D.Q₁' *ᵥ z) + D.B *ᵥ v + D.c := by
  simp only [mulVec_add, mulVec_mulVec, P₁_F, B, c]

/-- The differential coordinates of a reconstructed vector are the given ones. -/
@[simp]
theorem Q₁'_mulVec_reconstruct (x : κ → ℝ) (v : m → ℝ) : D.Q₁' *ᵥ D.reconstruct x v = x := by
  rw [reconstruct, mulVec_sub, mulVec_mulVec, mulVec_mulVec, D.Q₁'_Q₁, D.Q₁'_Q₂, one_mulVec,
    zero_mulVec, sub_zero]

private theorem P₂_rhs_reconstruct (x : κ → ℝ) (v : m → ℝ) :
    D.P₂ *ᵥ (S.F *ᵥ D.reconstruct x v + S.G *ᵥ v + S.b) = 0 := by
  rw [reconstruct, mulVec_sub, mulVec_add, mulVec_add, mulVec_sub, P₂_F_Q₁, P₂_F_Q₂, zero_sub,
    add_assoc, ← mulVec_add, neg_add_cancel]

/-- **Exact decoupling.** On a time set with unique derivatives (such as `[0, ∞)`), `z` solves
`E ż = F z + G u + b` exactly when (i) at every time it is reconstructed from its differential
coordinates `x = Q₁' z` and the input value, and (ii) `x` solves `ẋ = A x + B u + c`. -/
theorem isSolutionOn_iff {u : ℝ → m → ℝ} {z : ℝ → ι → ℝ} {s : Set ℝ} (hs : UniqueDiffOn ℝ s) :
    S.IsSolutionOn u z s ↔
      (∀ t ∈ s, z t = D.reconstruct (D.Q₁' *ᵥ z t) (u t)) ∧
      ∀ t ∈ s, HasDerivWithinAt (fun τ => D.Q₁' *ᵥ z τ)
        (D.A *ᵥ (D.Q₁' *ᵥ z t) + D.B *ᵥ u t + D.c) s t := by
  constructor
  · intro hz
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · -- The algebraic rows: `P₂ E z = 0`, so its derivative `P₂ (F z + G u + b)` vanishes.
      have h0 : HasDerivWithinAt (fun τ => D.P₂ *ᵥ (S.E *ᵥ z τ))
          (D.P₂ *ᵥ (S.F *ᵥ z t + S.G *ᵥ u t + S.b)) s t := hasDerivWithinAt_mulVec _ (hz t ht)
      simp only [P₂_E_mulVec] at h0
      have h1 := (hs t ht).eq_deriv _ h0 (hasDerivWithinAt_const t s 0)
      rw [mulVec_add, mulVec_add, P₂_F_mulVec, add_assoc, ← mulVec_add] at h1
      conv_lhs => rw [decomp (D := D) (z t)]
      rw [reconstruct, eq_neg_of_add_eq_zero_left h1, mulVec_neg, sub_eq_add_neg]
    · have h := hasDerivWithinAt_mulVec D.P₁ (hz t ht)
      simp only [P₁_E_mulVec, P₁_rhs] at h
      exact h
  · rintro ⟨hrec, hx⟩ t ht
    have h := hasDerivWithinAt_mulVec (S.E * D.Q₁) (hx t ht)
    simp only [← E_mulVec] at h
    convert h using 1
    set w := D.A *ᵥ (D.Q₁' *ᵥ z t) + D.B *ᵥ u t + D.c
    have hP₂ : D.P₂ *ᵥ (S.F *ᵥ z t + S.G *ᵥ u t + S.b) = 0 := by
      rw [hrec t ht]
      exact P₂_rhs_reconstruct _ _
    rw [eq_of_P (D := D) (S.F *ᵥ z t + S.G *ᵥ u t + S.b), eq_of_P (D := D) ((S.E * D.Q₁) *ᵥ w),
      hP₂, P₁_E_Q₁, P₂_E_Q₁, P₁_rhs]

/-- **Reconstruction.** Every solution `x` of the reduced ODE `ẋ = A x + B u + c` on `s` yields
the solution `t ↦ reconstruct (x t) (u t)` of `S`, whose differential coordinates are `x`. -/
theorem isSolutionOn_reconstruct {u : ℝ → m → ℝ} {x : ℝ → κ → ℝ} {s : Set ℝ}
    (hx : ∀ t ∈ s, HasDerivWithinAt x (D.A *ᵥ x t + D.B *ᵥ u t + D.c) s t) :
    S.IsSolutionOn u (fun t => D.reconstruct (x t) (u t)) s := by
  have hs := (isSolutionOn_iff (D := D) (u := u) (z := fun t => D.reconstruct (x t) (u t))
    (s := s))
  -- The backward direction of `isSolutionOn_iff` does not use `UniqueDiffOn`.
  intro t ht
  have hx' : ∀ t ∈ s, HasDerivWithinAt (fun τ => D.Q₁' *ᵥ D.reconstruct (x τ) (u τ))
      (D.A *ᵥ (D.Q₁' *ᵥ D.reconstruct (x t) (u t)) + D.B *ᵥ u t + D.c) s t := by
    simpa only [Q₁'_mulVec_reconstruct] using hx
  have h := hasDerivWithinAt_mulVec (S.E * D.Q₁) (hx' t ht)
  simp only [← E_mulVec] at h
  convert h using 1
  clear hs
  set w := D.A *ᵥ x t + D.B *ᵥ u t + D.c
  simp only [Q₁'_mulVec_reconstruct]
  rw [eq_of_P (D := D) (S.F *ᵥ _ + S.G *ᵥ u t + S.b), eq_of_P (D := D) ((S.E * D.Q₁) *ᵥ w),
    P₂_rhs_reconstruct, P₁_E_Q₁, P₂_E_Q₁, P₁_rhs, Q₁'_mulVec_reconstruct]

/-- **Existence and consistent initial states.** For an input continuous on `[0, ∞)`, an
initial state `z₀` starts a solution of `S` on `[0, ∞)` exactly when it satisfies the algebraic
constraint `z₀ = reconstruct (Q₁' z₀) (u 0)`. In particular every `x₀ : κ → ℝ` is the
differential part of a consistent initial state, `reconstruct x₀ (u 0)`. -/
theorem exists_isSolutionOn_Ici_iff {u : ℝ → m → ℝ} (hu : ContinuousOn u (Ici 0))
    (z₀ : ι → ℝ) :
    (∃ z, S.IsSolutionOn u z (Ici 0) ∧ z 0 = z₀) ↔ z₀ = D.reconstruct (D.Q₁' *ᵥ z₀) (u 0) := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ((isSolutionOn_iff (D := D) (uniqueDiffOn_Ici 0)).1 hz).1 0 self_mem_Ici
  · intro h₀
    -- The affine term `c` is a constant extra input.
    let L : LTISystem κ (m ⊕ Unit) κ :=
      { A := D.A, B := fromCols D.B (replicateCol Unit D.c), C := 0, D := 0 }
    have hu' : ContinuousOn (fun t => Sum.elim (u t) (fun _ : Unit => (1 : ℝ))) (Ici 0) :=
      continuousOn_pi.2 fun j => by
        cases j with
        | inl j => exact (continuousOn_pi.1 hu) j
        | inr _ => exact continuousOn_const
    have hL := L.isSolutionOn_Ici (D.Q₁' *ᵥ z₀) hu'
    have hB : ∀ s, L.B *ᵥ Sum.elim (u s) (fun _ : Unit => (1 : ℝ)) = D.B *ᵥ u s + D.c :=
      fun s => by
        simp only [L, fromCols_mulVec_sumElim]
        congr 1
        ext i
        simp [replicateCol, mulVec, dotProduct]
    simp only [hB] at hL
    refine ⟨_, isSolutionOn_reconstruct (D := D) fun t ht => (hL t ht).congr_deriv ?_, ?_⟩
    · simp only [hB]
      exact (add_assoc _ _ _).symm
    · simp only [zero_smul, NormedSpace.exp_zero, one_mulVec, intervalIntegral.integral_same,
        add_zero]
      exact h₀.symm

/-- **Uniqueness.** Two solutions of `S` on `[0, ∞)` with the same input and the same initial
state agree at all times `t ≥ 0`. No regularity of the input is needed: the differential
coordinates of the two solutions differ by a solution of `ẋ = A x` starting at `0`, and the
algebraic coordinates are determined by the differential ones and the input. -/
theorem eqOn_of_isSolutionOn_Ici (D : S.IndexOneDecoupling κ ρ) {u : ℝ → m → ℝ}
    {z z' : ℝ → ι → ℝ} (hz : S.IsSolutionOn u z (Ici 0)) (hz' : S.IsSolutionOn u z' (Ici 0))
    (h0 : z 0 = z' 0) :
    EqOn z z' (Ici 0) := by
  obtain ⟨hr, hx⟩ := (isSolutionOn_iff (D := D) (uniqueDiffOn_Ici 0)).1 hz
  obtain ⟨hr', hx'⟩ := (isSolutionOn_iff (D := D) (uniqueDiffOn_Ici 0)).1 hz'
  have hd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt (fun τ => D.Q₁' *ᵥ z τ - D.Q₁' *ᵥ z' τ)
      (D.A *ᵥ (D.Q₁' *ᵥ z t - D.Q₁' *ᵥ z' t)) (Ici 0) t := fun t ht => by
    convert (hx t ht).sub (hx' t ht) using 1
    rw [mulVec_sub]
    abel
  intro t ht
  have h := Matrix.eq_exp_smul_mulVec_of_hasDerivWithinAt hd ht
  rw [h0, sub_self, mulVec_zero, sub_eq_zero] at h
  rw [hr t ht, hr' t ht, h]

/-- The proper realization of `S` with output `H z`, after the equilibrium shift:
`ẋ = A x + B u`, `y = (H Q₁) x - (H Q₂ P₂ G) u`. -/
@[expose] def realization {p : Type*} (H : Matrix p ι ℝ) : LTISystem κ m p :=
  { A := D.A, B := D.B, C := H * D.Q₁, D := -(H * D.Q₂ * D.P₂ * S.G) }

/-- **Proper realization about an equilibrium.** Let `z₀` be an equilibrium and `H` an output
map. On a time set with unique derivatives, `z` solves `S` with input `u` exactly when
(i) `z t = z₀ + Q₁ x t - Q₂ P₂ G u t` with `x = Q₁' (z - z₀)`, and (ii) `x` solves the state
equation of `realization H` with input `u`. Then the output deviation is
`H (z t - z₀) = C x t + D u t` (`IndexOneDecoupling.output_eq`). No derivative of `u` occurs. -/
theorem isSolutionOn_iff_realization {p : Type*} (H : Matrix p ι ℝ) {z₀ : ι → ℝ}
    (hz₀ : S.IsEquilibrium z₀) {u : ℝ → m → ℝ} {z : ℝ → ι → ℝ} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) :
    S.IsSolutionOn u z s ↔
      (∀ t ∈ s, z t = z₀ + D.Q₁ *ᵥ (D.Q₁' *ᵥ (z t - z₀)) - D.Q₂ *ᵥ (D.P₂ *ᵥ (S.G *ᵥ u t))) ∧
      (D.realization H).IsSolutionOn u (fun t => D.Q₁' *ᵥ (z t - z₀)) s := by
  rw [hz₀.isSolutionOn_iff, (isSolutionOn_iff (D := D.deviation) hs)]
  refine and_congr (forall₂_congr fun t _ => ?_) (forall₂_congr fun t _ => ?_)
  · simp only [IndexOneDecoupling.reconstruct, IndexOneDecoupling.deviation,
      DescriptorSystem.deviation, add_zero]
    constructor <;> intro h
    · rw [add_sub_assoc, ← h, add_sub_cancel]
    · rw [add_sub_assoc] at h
      exact sub_eq_of_eq_add' h
  · simp [realization, IndexOneDecoupling.deviation, DescriptorSystem.deviation, A, B, c,
]

/-- The output deviation of a solution in the form of `isSolutionOn_iff_realization` (i). -/
theorem output_eq {p : Type*} (H : Matrix p ι ℝ) {z₀ v : ι → ℝ} {w : m → ℝ}
    (h : v = z₀ + D.Q₁ *ᵥ (D.Q₁' *ᵥ (v - z₀)) - D.Q₂ *ᵥ (D.P₂ *ᵥ (S.G *ᵥ w))) :
    H *ᵥ v - H *ᵥ z₀ = (D.realization H).C *ᵥ (D.Q₁' *ᵥ (v - z₀)) + (D.realization H).D *ᵥ w := by
  conv_lhs => rw [h]
  simp only [realization, mulVec_add, mulVec_sub, mulVec_mulVec, neg_mulVec, Matrix.mul_assoc]
  abel

omit [Fintype m] in
private theorem exists_norm_mulVec_le {α β : Type*} [Fintype α] [Fintype β] (M : Matrix α β ℝ) :
    ∃ K, ∀ v : β → ℝ, ‖WithLp.toLp 2 (M *ᵥ v)‖ ≤ K * ‖WithLp.toLp 2 v‖ := by
  let f : EuclideanSpace ℝ β →ₗ[ℝ] EuclideanSpace ℝ α :=
    (WithLp.linearEquiv 2 ℝ (α → ℝ)).symm.toLinearMap ∘ₗ M.mulVecLin ∘ₗ
      (WithLp.linearEquiv 2 ℝ (β → ℝ)).toLinearMap
  exact ⟨‖LinearMap.toContinuousLinearMap f‖, fun v =>
    (LinearMap.toContinuousLinearMap f).le_opNorm (WithLp.toLp 2 v)⟩

/-- **Stability of the descriptor system from the reduced ODE.** If `ẋ = A x` is exponentially
stable in the Euclidean norm, then every equilibrium `z₀` of `S` is exponentially stable: all
solutions with zero input converge to `z₀`, with constants from those of `A` and the norms of
`Q₁` and `Q₁'`. Solutions exist through every consistent initial state
(`exists_isSolutionOn_Ici_iff`), so this is not vacuous. -/
theorem isExponentiallyStableAt {z₀ : ι → ℝ} (hz₀ : S.IsEquilibrium z₀)
    (hA : (toEuclideanCLM (𝕜 := ℝ) D.A).IsExponentiallyStable) : S.IsExponentiallyStableAt z₀ := by
  obtain ⟨M, α, hα, hM⟩ := hA
  obtain ⟨K₁, hK₁⟩ := exists_norm_mulVec_le D.Q₁
  obtain ⟨K₂, hK₂⟩ := exists_norm_mulVec_le D.Q₁'
  refine ⟨|K₁| * |M| * |K₂|, α, hα, fun z hz t ht => ?_⟩
  obtain ⟨hrec, hx⟩ := (isSolutionOn_iff_realization (D := D) (0 : Matrix Unit ι ℝ) hz₀
    (uniqueDiffOn_Ici 0)).1 hz
  set x := fun t => D.Q₁' *ᵥ (z t - z₀)
  have htraj : (toEuclideanCLM (𝕜 := ℝ) D.A).IsTrajectoryOn (fun t => WithLp.toLp 2 (x t))
      (Ici 0) := Matrix.isTrajectoryOn_toEuclideanCLM_iff.2 fun τ hτ => by
    simpa [realization, LTISystem.IsSolutionOn] using hx τ hτ
  have hzt : z t - z₀ = D.Q₁ *ᵥ x t := by
    have := hrec t ht
    simp only [Pi.zero_apply, mulVec_zero, sub_zero] at this
    rw [this]; simp [x]
  have h1 : ‖WithLp.toLp 2 (x t)‖ ≤ |M| * Real.exp (-(α * t)) * ‖WithLp.toLp 2 (x 0)‖ :=
    (hM _ htraj t ht).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le) (norm_nonneg _))
  have h2 : ‖WithLp.toLp 2 (x 0)‖ ≤ |K₂| * ‖WithLp.toLp 2 (z 0 - z₀)‖ :=
    (hK₂ _).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  have h3 : ‖WithLp.toLp 2 (D.Q₁ *ᵥ x t)‖ ≤ |K₁| * ‖WithLp.toLp 2 (x t)‖ :=
    (hK₁ _).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  rw [hzt]
  have he := (Real.exp_pos (-(α * t))).le
  calc ‖WithLp.toLp 2 (D.Q₁ *ᵥ x t)‖ ≤ |K₁| * (|M| * Real.exp (-(α * t)) *
        (|K₂| * ‖WithLp.toLp 2 (z 0 - z₀)‖)) := by
        refine h3.trans (mul_le_mul_of_nonneg_left (h1.trans ?_) (abs_nonneg _))
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = |K₁| * |M| * |K₂| * Real.exp (-(α * t)) * ‖WithLp.toLp 2 (z 0 - z₀)‖ := by ring

end IndexOneDecoupling

end DescriptorSystem
