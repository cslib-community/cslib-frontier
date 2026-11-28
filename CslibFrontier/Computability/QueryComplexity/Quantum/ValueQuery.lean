/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.Search
public import CslibFrontier.Foundations.Quantum.Measurement.Readout
import CslibFrontier.Foundations.LinearAlgebra.UnitarySpectrum

/-!
# Quantum value-query algorithms

This module extends the phase-oracle quantum query model (`Cslib.Quantum.run`) to the quantum
value-query model (`Cslib.Quantum.ValueState`, `Cslib.Quantum.valueOracle`,
`Cslib.Quantum.runValue`) over an arbitrary finite query index type `ι`, finite value/answer
register `V`, and finite workspace `W`, where each oracle call applies an input-dependent unitary
`step (x i)` to the `V` register controlled by the query index `i`. Diagonal phase kickback
(`Cslib.Quantum.phaseStep`, recovering `Cslib.Quantum.phaseOracle` and `Cslib.Quantum.run` via
`Cslib.Quantum.valueOracle_phaseStep` and `Cslib.Quantum.runValue_phaseStep`), permutation oracles
(`Cslib.Quantum.permStep`), group-addition oracles (`Cslib.Quantum.addStep`), and XOR oracles
(`BitString` as an additive group) are special cases. Multi-outcome computational-basis readouts
(`Cslib.Quantum.measureOut`) are provided by
`CslibFrontier/Foundations/Quantum/Measurement/Readout.lean`.

For lower bounds, restricting a value-query algorithm to inputs taking only two values `a₀` and
`a₁` can be simulated in the Boolean phase-oracle model (`Cslib.Quantum.run`) on `N = |ι|` bits:

* When the relative step `(step a₀).symm.trans (step a₁)` is an involution (such as an XOR
  oracle), one binary phase query simulates each value query
  (`Cslib.Quantum.exists_sim_involution`).
* For an arbitrary unitary step `step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V)`,
  simultaneously diagonalizing the Hermitian and skew-Hermitian parts of the relative unitary
  (`UnitarySpectrum` -> `LinearIsometryEquiv.exists_orthonormalBasis_eigenvectors`) simulates
  each value query with two binary phase queries (`Cslib.Quantum.exists_sim_value`).
* Index-returning `T`-query algorithms that read one value can be turned into `(T + 1)`-query
  value-returning algorithms (`Cslib.Quantum.exists_sim_index_to_value`,
  `Cslib.Quantum.exists_sim_index_to_value_perm`).

## Main definitions

* `Cslib.Quantum.ValueState`: quantum states over `ι × V × W`.
* `Cslib.Quantum.valueOracle`, `Cslib.Quantum.phaseStep`, `Cslib.Quantum.permStep`,
  `Cslib.Quantum.addStep`: value-query oracles and canonical per-symbol steps.
* `Cslib.Quantum.runValue`: final state of a `T`-query value-query algorithm.
* `Cslib.Quantum.embedOutcome`: embedding value-query outcomes into `Fin N × Bool × V × W`.

## Main results

* `Cslib.Quantum.runValue_phaseStep`: `phaseStep` identifies `Cslib.Quantum.run` as a
  specialization of `runValue` on `State N W = ValueState (Fin N) Bool W`.
* `Cslib.Quantum.norm_runValue`: value-query algorithms preserve norms.
* `Cslib.Quantum.exists_sim_involution`: simulating a two-valued restriction with an involutive
  difference by `T` binary phase queries.
* `Cslib.Quantum.exists_sim_value`: simulating an arbitrary two-valued restriction by `2 * T`
  binary phase queries.
* `Cslib.Quantum.exists_sim_index_to_value`, `Cslib.Quantum.exists_sim_index_to_value_perm`:
  simulating a `T`-query index-returning value-query algorithm with `T + 1` value queries.
-/

public section

namespace Cslib.Quantum

open Finset

/-! ### Fibered unitary helpers -/

section FiberHelpers

private def sliceSecond {A B : Type*} (ψ : EuclideanSpace ℂ (A × B)) (a : A) :
    EuclideanSpace ℂ B :=
  WithLp.toLp 2 fun b => ψ.ofLp (a, b)

@[simp] private theorem sliceSecond_apply {A B : Type*} (ψ : EuclideanSpace ℂ (A × B))
    (a : A) (b : B) : (sliceSecond ψ a).ofLp b = ψ.ofLp (a, b) := rfl

private noncomputable def reindexProd {P Q : Type*} [Fintype P] [Fintype Q] (e : P ≃ Q) :
    EuclideanSpace ℂ P ≃ₗᵢ[ℂ] EuclideanSpace ℂ Q :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

@[simp] private theorem reindexProd_apply {P Q : Type*} [Fintype P] [Fintype Q] (e : P ≃ Q)
    (ψ : EuclideanSpace ℂ P) (q : Q) :
    (reindexProd e ψ).ofLp q = ψ.ofLp (e.symm q) :=
  rfl

@[simp] private theorem reindexProd_symm_apply {P Q : Type*} [Fintype P] [Fintype Q] (e : P ≃ Q)
    (ψ : EuclideanSpace ℂ Q) (p : P) :
    ((reindexProd e).symm ψ).ofLp p = ψ.ofLp (e p) := by
  simp [reindexProd]

private noncomputable def prodCurryIso (A B : Type*) [Fintype A] [Fintype B] :
    EuclideanSpace ℂ (A × B) ≃ₗᵢ[ℂ] PiLp 2 (fun _ : A => EuclideanSpace ℂ B) :=
  (reindexProd (Equiv.sigmaEquivProd A B).symm).trans
    (LinearIsometryEquiv.piLpCurry ℂ 2 fun _ : A => fun _ : B => ℂ)

/-- Applying unitaries `F a : ℂ^B₁ ≃ₗᵢ[ℂ] ℂ^B₂` fiberwise over `a : A` using Mathlib's
`LinearIsometryEquiv.piLpCongrLeft`, `piLpCurry`, and `piLpCongrRight`. -/
private noncomputable def fiberIso {A B₁ B₂ : Type*} [Fintype A] [Fintype B₁] [Fintype B₂]
    (F : A → (EuclideanSpace ℂ B₁ ≃ₗᵢ[ℂ] EuclideanSpace ℂ B₂)) :
    EuclideanSpace ℂ (A × B₁) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (A × B₂) :=
  (prodCurryIso A B₁).trans
    ((LinearIsometryEquiv.piLpCongrRight 2 F).trans (prodCurryIso A B₂).symm)

@[simp] private theorem fiberIso_apply {A B₁ B₂ : Type*} [Fintype A] [Fintype B₁] [Fintype B₂]
    (F : A → (EuclideanSpace ℂ B₁ ≃ₗᵢ[ℂ] EuclideanSpace ℂ B₂))
    (ψ : EuclideanSpace ℂ (A × B₁)) (a : A) (b : B₂) :
    (fiberIso F ψ).ofLp (a, b) = (F a (sliceSecond ψ a)).ofLp b :=
  rfl

/-- Conjugate a fiberwise unitary on `A × B` along a coordinate equivalence `e : P ≃ A × B`. -/
private noncomputable def conjFiberIso {P A B : Type*} [Fintype P] [Fintype A] [Fintype B]
    (e : P ≃ A × B) (F : A → (EuclideanSpace ℂ B ≃ₗᵢ[ℂ] EuclideanSpace ℂ B)) :
    EuclideanSpace ℂ P ≃ₗᵢ[ℂ] EuclideanSpace ℂ P :=
  (reindexProd e).trans ((fiberIso F).trans (reindexProd e).symm)

@[simp] private theorem conjFiberIso_apply {P A B : Type*} [Fintype P] [Fintype A] [Fintype B]
    (e : P ≃ A × B) (F : A → (EuclideanSpace ℂ B ≃ₗᵢ[ℂ] EuclideanSpace ℂ B))
    (ψ : EuclideanSpace ℂ P) (p : P) :
    (conjFiberIso e F ψ).ofLp p =
      (F (e p).1 (sliceSecond (reindexProd e ψ) (e p).1)).ofLp (e p).2 := by
  simpa only [conjFiberIso, LinearIsometryEquiv.trans_apply, reindexProd_symm_apply] using
    fiberIso_apply F (reindexProd e ψ) (e p).1 (e p).2

private noncomputable def piLpCongrRightLI {A B : Type*} [Fintype A] [Fintype B]
    (F : A → (EuclideanSpace ℂ B →ₗᵢ[ℂ] EuclideanSpace ℂ B)) :
    PiLp 2 (fun _ : A => EuclideanSpace ℂ B) →ₗᵢ[ℂ]
      PiLp 2 (fun _ : A => EuclideanSpace ℂ B) where
  toFun x := WithLp.toLp 2 fun a => F a (x a)
  map_add' x y := by ext a b; simp [map_add]
  map_smul' r x := by ext a b; simp [map_smul]
  norm_map' x := by
    have hsq : ‖(WithLp.toLp 2 fun a => F a (x a) :
        PiLp 2 (fun _ : A => EuclideanSpace ℂ B))‖ ^ 2 = ‖x‖ ^ 2 := by
      simp [PiLp.norm_sq_eq_of_L2, (F _).norm_map]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Lifting a family of linear isometries `F : A → (ℂ^B →ₗᵢ[ℂ] ℂ^B)` along `e : P ≃ A × B`. -/
private noncomputable def liftFiberIso {P A B : Type*} [Fintype P] [Fintype A] [Fintype B]
    (e : P ≃ A × B) (F : A → (EuclideanSpace ℂ B →ₗᵢ[ℂ] EuclideanSpace ℂ B)) :
    EuclideanSpace ℂ P →ₗᵢ[ℂ] EuclideanSpace ℂ P :=
  (reindexProd e).symm.toLinearIsometry.comp
    ((prodCurryIso A B).symm.toLinearIsometry.comp
      ((piLpCongrRightLI F).comp
        ((prodCurryIso A B).toLinearIsometry.comp (reindexProd e).toLinearIsometry)))

@[simp] private theorem liftFiberIso_apply {P A B : Type*} [Fintype P] [Fintype A] [Fintype B]
    (e : P ≃ A × B) (F : A → (EuclideanSpace ℂ B →ₗᵢ[ℂ] EuclideanSpace ℂ B))
    (φ : EuclideanSpace ℂ P) (p : P) :
    (liftFiberIso e F φ).ofLp p =
      (F (e p).1 (sliceSecond (reindexProd e φ) (e p).1)).ofLp (e p).2 := by
  simp only [liftFiberIso, LinearIsometry.coe_comp, Function.comp_apply,
    LinearIsometryEquiv.coe_toLinearIsometry, reindexProd_symm_apply, prodCurryIso,
    piLpCongrRightLI]
  rfl

private noncomputable def liftFiberIsoAt {P A B : Type*} [Fintype P] [Fintype A] [Fintype B]
    [DecidableEq A] (e : P ≃ A × B) (a₀ : A)
    (f : EuclideanSpace ℂ B →ₗᵢ[ℂ] EuclideanSpace ℂ B) :
    EuclideanSpace ℂ P →ₗᵢ[ℂ] EuclideanSpace ℂ P :=
  liftFiberIso e fun a => if a = a₀ then f else .id

private def fiberEmb {P A B : Type*} (e : P ≃ A × B) (a₀ : A) : B ↪ P where
  toFun b := e.symm (a₀, b)
  inj' _ _ h := (Prod.ext_iff.mp (e.symm.injective h)).2

@[simp] private theorem fiberEmb_apply {P A B : Type*} (e : P ≃ A × B) (a₀ : A) (b : B) :
    fiberEmb e a₀ b = e.symm (a₀, b) := rfl

private theorem piLpExtendByZero_fiberEmb_apply {P A B : Type*} [Fintype P] [Fintype B]
    [DecidableEq A] (e : P ≃ A × B) (a₀ : A) (ψ : EuclideanSpace ℂ B) (p : P) :
    (LinearIsometry.piLpExtendByZero 2 ℂ ℂ (fiberEmb e a₀) ψ).ofLp p =
      if (e p).1 = a₀ then ψ.ofLp (e p).2 else 0 := by
  split_ifs with h
  · have hp : p = fiberEmb e a₀ (e p).2 := by
      rw [fiberEmb_apply, ← (Prod.ext h rfl : e p = (a₀, (e p).2)), e.symm_apply_apply]
    conv_lhs => rw [hp]
    change Function.extend (fiberEmb e a₀) ψ.ofLp 0 (fiberEmb e a₀ (e p).2) = _
    exact (fiberEmb e a₀).injective.extend_apply ψ.ofLp 0 (e p).2
  · exact LinearIsometry.piLpExtendByZero_apply_eq_zero
      (fun ⟨b, hb⟩ => h (by simp [← hb])) ψ

private theorem liftFiberIsoAt_piLpExtendByZero {P A B : Type*} [Fintype P] [Fintype A]
    [Fintype B] [DecidableEq A] (e : P ≃ A × B) (a₀ : A)
    (f : EuclideanSpace ℂ B →ₗᵢ[ℂ] EuclideanSpace ℂ B) (ψ : EuclideanSpace ℂ B) :
    liftFiberIsoAt e a₀ f (LinearIsometry.piLpExtendByZero 2 ℂ ℂ (fiberEmb e a₀) ψ) =
      LinearIsometry.piLpExtendByZero 2 ℂ ℂ (fiberEmb e a₀) (f ψ) := by
  ext p
  simp only [liftFiberIsoAt, liftFiberIso_apply, piLpExtendByZero_fiberEmb_apply]
  split_ifs with h
  · refine congrArg (fun u => (f u).ofLp (e p).2) ?_
    ext b
    simp only [sliceSecond_apply, reindexProd_apply, piLpExtendByZero_fiberEmb_apply,
      Equiv.apply_symm_apply, h, ↓reduceIte]
  · simp only [LinearIsometry.id_apply, sliceSecond_apply, reindexProd_apply,
      piLpExtendByZero_fiberEmb_apply, Equiv.apply_symm_apply, h, ↓reduceIte]

end FiberHelpers

/-! ### Value-query model -/

/-- The quantum state space of a value-query algorithm with query index register `ι`, value
register `V`, and workspace `W`. -/
abbrev ValueState (ι V W : Type*) := EuclideanSpace ℂ (ι × V × W)

section ValueModel

variable {ι V W α : Type*} [Fintype ι] [Fintype V] [Fintype W]

private def valSlice (ψ : ValueState ι V W) (i : ι) (w : W) : EuclideanSpace ℂ V :=
  WithLp.toLp 2 fun v => ψ.ofLp (i, v, w)

omit [Fintype ι] [Fintype V] [Fintype W] in
@[simp] private theorem valSlice_apply (ψ : ValueState ι V W) (i : ι) (w : W) (v : V) :
    (valSlice ψ i w).ofLp v = ψ.ofLp (i, v, w) := rfl

private def valueFiberEquiv {ι V W : Type*} : (ι × V × W) ≃ ((ι × W) × V) where
  toFun | (i, v, w) => ((i, w), v)
  invFun | ((i, w), v) => (i, v, w)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Value oracle**: given per-symbol unitaries `step : α → (ℂ^V ≃ₗᵢ[ℂ] ℂ^V)` and an input
`x : ι → α`, applies `step (x i)` to the value register controlled by the query index `i`. -/
noncomputable def valueOracle
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V)) (x : ι → α) :
    ValueState ι V W ≃ₗᵢ[ℂ] ValueState ι V W :=
  conjFiberIso valueFiberEquiv fun p : ι × W => step (x p.1)

/-- Coordinate evaluation of `valueOracle step x ψ` at `(i, v, w)`. -/
@[simp] theorem valueOracle_apply (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (x : ι → α) (ψ : ValueState ι V W) (i : ι) (v : V) (w : W) :
    (valueOracle step x ψ).ofLp (i, v, w) =
      (step (x i) (WithLp.toLp 2 fun v' => ψ.ofLp (i, v', w))).ofLp v := by
  rfl

/-- Unitary step arising from a family of permutations `π : α → Equiv.Perm V`, acting as
`|v⟩ ↦ |π a v⟩`. -/
@[expose] noncomputable def permStep (π : α → Equiv.Perm V) (a : α) :
    EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (π a)

/-- Coordinate evaluation of `permStep π a φ`. -/
@[simp] theorem permStep_apply (π : α → Equiv.Perm V) (a : α) (φ : EuclideanSpace ℂ V) (v : V) :
    (permStep π a φ).ofLp v = φ.ofLp ((π a).symm v) :=
  rfl

/-- Unitary step for an additive group value register `V`: `|v⟩ ↦ |v + a⟩`. This covers modular
addition on `ZMod M` as well as bitwise XOR on `BitString m`. -/
@[expose] noncomputable def addStep [AddGroup V] (a : V) :
    EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V :=
  permStep (fun b => Equiv.addRight b) a

/-- Coordinate evaluation of `addStep a φ`. -/
@[simp] theorem addStep_apply [AddGroup V] (a : V) (φ : EuclideanSpace ℂ V) (v : V) :
    (addStep a φ).ofLp v = φ.ofLp (v - a) := by
  simp [addStep, sub_eq_add_neg]

/-- Coordinate evaluation of `(addStep a).symm φ`. -/
@[simp] theorem addStep_symm_apply [AddGroup V] (a : V) (φ : EuclideanSpace ℂ V) (v : V) :
    ((addStep a).symm φ).ofLp v = φ.ofLp (v + a) := by
  simp [addStep, permStep]

/-- Action of `addStep a` on computational-basis state `ket v`. -/
theorem addStep_ket [DecidableEq V] [AddGroup V] (a v : V) :
    addStep a (ket v) = ket (v + a) := by
  ext u
  simp only [addStep_apply, ket_apply, sub_eq_iff_eq_add]

/-- When every element of `V` has order dividing `2` (such as `BitString m`), the relative step
`(addStep a₀).symm.trans (addStep a₁)` is an involution. -/
theorem addStep_rel_involutive [AddCommGroup V] (h2 : ∀ v : V, v + v = 0) (a₀ a₁ : V)
    (φ : EuclideanSpace ℂ V) :
    ((addStep a₀).symm.trans (addStep a₁))
      (((addStep a₀).symm.trans (addStep a₁)) φ) = φ := by
  have hneg : ∀ x : V, -x = x := fun x => neg_eq_iff_add_eq_zero.mpr (h2 x)
  ext v
  simp only [LinearIsometryEquiv.trans_apply, addStep_apply, addStep_symm_apply]
  refine congrArg φ.ofLp ?_
  rw [sub_eq_add_neg, sub_eq_add_neg, hneg a₁]
  calc
    v + a₁ + a₀ + a₁ + a₀ = v + (a₁ + a₁) + (a₀ + a₀) := by abel
    _ = v := by rw [h2 a₁, h2 a₀, add_zero, add_zero]

/-- Diagonal phase unitary on a `Bool` response qubit: `|b⟩ ↦ (-1)^{b && bit} |b⟩`.
Specializing `valueOracle` and `runValue` to `phaseStep` on `State N W = ValueState (Fin N) Bool W`
recovers `Cslib.Quantum.phaseOracle` and `Cslib.Quantum.run`. -/
@[expose] noncomputable def phaseStep (bit : Bool) :
    EuclideanSpace ℂ Bool ≃ₗᵢ[ℂ] EuclideanSpace ℂ Bool where
  toFun ψ := WithLp.toLp 2 fun b => (if b && bit then (-1 : ℂ) else 1) * ψ.ofLp b
  invFun ψ := WithLp.toLp 2 fun b => (if b && bit then (-1 : ℂ) else 1) * ψ.ofLp b
  map_add' ψ₁ ψ₂ := by
    ext b; simp only [WithLp.ofLp_add, Pi.add_apply]; ring
  map_smul' r ψ := by
    ext b; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
  left_inv ψ := by ext b; cases bit <;> cases b <;> simp
  right_inv ψ := by ext b; cases bit <;> cases b <;> simp
  norm_map' ψ := by
    have hsq : ‖(WithLp.toLp 2 fun b => (if b && bit then (-1 : ℂ) else 1) * ψ.ofLp b :
        EuclideanSpace ℂ Bool)‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      refine sum_congr rfl fun b _ => ?_
      cases bit <;> cases b <;> simp
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Coordinate evaluation of `phaseStep bit φ`. -/
@[simp] theorem phaseStep_apply (bit : Bool) (φ : EuclideanSpace ℂ Bool) (b : Bool) :
    (phaseStep bit φ).ofLp b = (if b && bit then (-1 : ℂ) else 1) * φ.ofLp b :=
  rfl

/-- The state after `t` queries of a value-query algorithm `U` starting from `ψ₀` on input
`x : ι → α`. -/
@[expose] noncomputable def runValue
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    (ψ₀ : ValueState ι V W) (x : ι → α) : ℕ → ValueState ι V W
  | 0 => U 0 ψ₀
  | t + 1 => U (t + 1) (valueOracle step x (runValue step U ψ₀ x t))

/-- Value-query algorithms preserve norms. -/
theorem norm_runValue (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    (ψ₀ : ValueState ι V W) (x : ι → α) (t : ℕ) :
    ‖runValue step U ψ₀ x t‖ = ‖ψ₀‖ := by
  induction t with
  | zero => exact (U 0).norm_map ψ₀
  | succ t ih => rw [runValue, LinearIsometry.norm_map, LinearIsometryEquiv.norm_map, ih]

/-- On `State N W = ValueState (Fin N) Bool W`, `valueOracle phaseStep` agrees with the controlled
phase oracle `phaseOracle`. -/
@[simp] theorem valueOracle_phaseStep {N : ℕ} (x : Fin N → Bool) (ψ : State N W) :
    valueOracle phaseStep x ψ = phaseOracle x ψ := by
  ext ⟨i, b, w⟩
  rfl

/-- On `State N W = ValueState (Fin N) Bool W`, `runValue phaseStep` agrees with the phase-query
execution `run`. -/
@[simp] theorem runValue_phaseStep {N : ℕ}
    (U : ℕ → State N W →ₗᵢ[ℂ] State N W) (ψ₀ : State N W) (x : Fin N → Bool) (t : ℕ) :
    runValue phaseStep U ψ₀ x t = run U ψ₀ x t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [runValue, run, ih]

end ValueModel

/-! ### Simulating two-valued restrictions in the Boolean phase-oracle model -/

/-- The injective embedding of value-query computational basis outcomes `ι × V × W` into the
`ctrl = false` sector of `Fin N × Bool × V × W` along `e : ι ≃ Fin N`. -/
@[expose] def embedOutcome {ι V W : Type*} {N : ℕ} (e : ι ≃ Fin N) :
    (ι × V × W) ↪ (Fin N × Bool × V × W) where
  toFun p := (e p.1, false, p.2)
  inj' p₁ p₂ h := by
    obtain ⟨i₁, vw₁⟩ := p₁
    obtain ⟨i₂, vw₂⟩ := p₂
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (e.injective h.1) h.2.2

/-- Application formula for `embedOutcome`. -/
@[simp] theorem embedOutcome_apply {ι V W : Type*} {N : ℕ} (e : ι ≃ Fin N)
    (i : ι) (v : V) (w : W) :
    embedOutcome (V := V) (W := W) e (i, v, w) = (e i, false, v, w) :=
  rfl

section TwoValueSim

variable {ι V W : Type*} [Fintype ι] [Fintype V] [Fintype W]

private def valueStateEquiv {ι V W : Type*} {N : ℕ} (e : ι ≃ Fin N) :
    (Fin N × Bool × V × W) ≃ (Bool × (ι × V × W)) where
  toFun | (j, c, v, w) => (c, e.symm j, v, w)
  invFun | (c, i, v, w) => (e i, c, v, w)
  left_inv := fun ⟨_, _, _, _⟩ => by simp
  right_inv := fun ⟨_, _, _, _⟩ => by simp

/-- Embedding `ValueState ι V W` into the `ctrl = false` sector of `State N (V × W)` along
`e : ι ≃ Fin N`. -/
private noncomputable def embedState {N : ℕ} (e : ι ≃ Fin N) :
    ValueState ι V W →ₗᵢ[ℂ] State N (V × W) :=
  LinearIsometry.piLpExtendByZero 2 ℂ ℂ (fiberEmb (valueStateEquiv e) false)

@[simp] private theorem embedState_apply {N : ℕ} (e : ι ≃ Fin N) (ψ : ValueState ι V W)
    (j : Fin N) (c : Bool) (v : V) (w : W) :
    (embedState e ψ).ofLp (j, c, v, w) = if c then 0 else ψ.ofLp (e.symm j, v, w) := by
  rw [embedState, piLpExtendByZero_fiberEmb_apply]
  cases c <;> simp [valueStateEquiv]

private theorem measureProb_embedState {N : ℕ} (e : ι ≃ Fin N) (ψ : ValueState ι V W)
    (S : Finset (ι × V × W)) :
    measureProb (embedState e ψ) (S.map (embedOutcome e)) = measureProb ψ S := by
  rw [measureProb, sum_map, measureProb]
  exact sum_congr rfl fun ⟨i, v, w⟩ _ => by simp

/-- Lifting any linear isometry `f : ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W` to
`State N (V × W)`, acting as `f` on the `ctrl = false` sector and the identity on `ctrl = true`. -/
private noncomputable def liftValueIso {N : ℕ} (e : ι ≃ Fin N)
    (f : ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) :
    State N (V × W) →ₗᵢ[ℂ] State N (V × W) :=
  liftFiberIsoAt (valueStateEquiv e) false f

private theorem liftValueIso_embedState {N : ℕ} (e : ι ≃ Fin N)
    (f : ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) (ψ : ValueState ι V W) :
    liftValueIso e f (embedState e ψ) = embedState e (f ψ) :=
  liftFiberIsoAt_piLpExtendByZero (valueStateEquiv e) false f ψ

private def bvSlice {N : ℕ} (φ : State N (V × W)) (j : Fin N) (w : W) :
    EuclideanSpace ℂ (Bool × V) :=
  WithLp.toLp 2 fun ⟨c, v⟩ => φ.ofLp (j, c, v, w)

omit [Fintype ι] [Fintype V] [Fintype W] in
@[simp] private theorem bvSlice_apply {N : ℕ} (φ : State N (V × W)) (j : Fin N) (w : W)
    (c : Bool) (v : V) : (bvSlice φ j w).ofLp (c, v) = φ.ofLp (j, c, v, w) := rfl

private def bvFiberEquiv {N : ℕ} : (Fin N × Bool × V × W) ≃ ((Fin N × W) × (Bool × V)) where
  toFun | (j, c, v, w) => ((j, w), (c, v))
  invFun | ((j, w), (c, v)) => (j, c, v, w)
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def liftBoolV {N : ℕ}
    (G : EuclideanSpace ℂ (Bool × V) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × V)) :
    State N (V × W) ≃ₗᵢ[ℂ] State N (V × W) :=
  conjFiberIso (bvFiberEquiv (N := N) (V := V) (W := W)) fun _ : Fin N × W => G

private theorem bvSlice_liftBoolV {N : ℕ}
    (G : EuclideanSpace ℂ (Bool × V) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × V))
    (φ : State N (V × W)) (j : Fin N) (w : W) :
    bvSlice (liftBoolV G φ) j w = G (bvSlice φ j w) := by
  ext ⟨c, v⟩
  rfl

private theorem inv_sqrt_two_sq : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ 2 = 1 / 2 := by
  rw [sq, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt zero_le_two]
  push_cast; ring

private def boolSwapEquiv (B : Type*) : (Bool × B) ≃ (B × Bool) where
  toFun p := (p.2, p.1)
  invFun q := (q.2, q.1)
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def liftBoolLeft {B : Type*} [Fintype B]
    (Q : B → (EuclideanSpace ℂ Bool ≃ₗᵢ[ℂ] EuclideanSpace ℂ Bool)) :
    EuclideanSpace ℂ (Bool × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × B) :=
  conjFiberIso (boolSwapEquiv B) Q

@[simp] private theorem liftBoolLeft_apply {B : Type*} [Fintype B]
    (Q : B → (EuclideanSpace ℂ Bool ≃ₗᵢ[ℂ] EuclideanSpace ℂ Bool))
    (φ : EuclideanSpace ℂ (Bool × B)) (c : Bool) (k : B) :
    (liftBoolLeft Q φ).ofLp (c, k) = (Q k (WithLp.toLp 2 fun b => φ.ofLp (b, k))).ofLp c :=
  rfl

/-- Controlled `Z` on `Bool × B`: negates amplitudes with `c = true` when `flag = true`. -/
private noncomputable def ctrlZ {B : Type*} [Fintype B] (flag : Bool) :
    EuclideanSpace ℂ (Bool × B) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × B) :=
  liftBoolLeft fun _ => phaseStep flag

@[simp] private theorem ctrlZ_apply {B : Type*} [Fintype B] (flag : Bool)
    (φ : EuclideanSpace ℂ (Bool × B)) (c : Bool) (v : B) :
    (ctrlZ flag φ).ofLp (c, v) = (if c && flag then (-1 : ℂ) else 1) * φ.ofLp (c, v) :=
  rfl

omit [Fintype ι] [Fintype W] in
private theorem bvSlice_phaseOracle {N : ℕ} (b : Fin N → Bool) (φ : State N (V × W))
    (j : Fin N) (w : W) :
    bvSlice (phaseOracle b φ) j w = ctrlZ (b j) (bvSlice φ j w) := by
  ext ⟨c, v⟩
  rcases hbj : b j with _ | _ <;> cases c <;> simp [phaseOracle_apply, hbj]

private def embedBoolFalse (φ : EuclideanSpace ℂ V) : EuclideanSpace ℂ (Bool × V) :=
  WithLp.toLp 2 fun ⟨c, v⟩ => if c then 0 else φ.ofLp v

private theorem bvSlice_embedState {N : ℕ} (e : ι ≃ Fin N) (ψ : ValueState ι V W)
    (j : Fin N) (w : W) :
    bvSlice (embedState e ψ) j w = embedBoolFalse (valSlice ψ (e.symm j) w) := by
  ext ⟨c, v⟩
  cases c <;> simp [embedBoolFalse]

private theorem eq_embedState_of_bvSlice {N : ℕ} (e : ι ≃ Fin N)
    (φ : State N (V × W)) (ψ : ValueState ι V W)
    (h : ∀ j w, bvSlice φ j w = embedBoolFalse (valSlice ψ (e.symm j) w)) :
    φ = embedState e ψ := by
  ext ⟨j, c, v, w⟩
  have hjw := congrArg (fun u => u.ofLp (c, v)) (h j w)
  cases c <;> simpa [embedBoolFalse] using hjw

/-! #### 1-query simulation for involutive relative step -/

/-- Real 2D rotation on `ℂ^Bool`: `[[c, -s], [s, c]]`. -/
private noncomputable def rotBool (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    EuclideanSpace ℂ Bool ≃ₗᵢ[ℂ] EuclideanSpace ℂ Bool where
  toFun ψ := WithLp.toLp 2 fun b => if b then (s : ℂ) * ψ.ofLp false + (c : ℂ) * ψ.ofLp true
    else (c : ℂ) * ψ.ofLp false - (s : ℂ) * ψ.ofLp true
  invFun ψ := WithLp.toLp 2 fun b => if b then -(s : ℂ) * ψ.ofLp false + (c : ℂ) * ψ.ofLp true
    else (c : ℂ) * ψ.ofLp false + (s : ℂ) * ψ.ofLp true
  map_add' ψ₁ ψ₂ := by
    ext b
    cases b <;> simp only [WithLp.ofLp_add, Pi.add_apply, ite_true,
      Bool.false_eq_true, ite_false] <;> ring
  map_smul' r ψ := by
    ext b
    cases b <;> simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply,
      ite_true, Bool.false_eq_true, ite_false] <;> ring
  left_inv ψ := by
    have hcsC : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
    ext b
    cases b <;> simp only [ite_true, Bool.false_eq_true, ite_false]
    · linear_combination (ψ.ofLp false) * hcsC
    · linear_combination (ψ.ofLp true) * hcsC
  right_inv ψ := by
    have hcsC : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
    ext b
    cases b <;> simp only [ite_true, Bool.false_eq_true, ite_false]
    · linear_combination (ψ.ofLp false) * hcsC
    · linear_combination (ψ.ofLp true) * hcsC
  norm_map' ψ := by
    have hsq : ‖(WithLp.toLp 2 fun b : Bool =>
        if b then (s : ℂ) * ψ.ofLp false + (c : ℂ) * ψ.ofLp true
        else (c : ℂ) * ψ.ofLp false - (s : ℂ) * ψ.ofLp true :
        EuclideanSpace ℂ Bool)‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_bool, Fintype.sum_bool]
      simp only [ite_true, Bool.false_eq_true, ite_false, Complex.sq_norm, Complex.normSq_apply,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
      linear_combination
        ((ψ.ofLp false).re ^ 2 + (ψ.ofLp false).im ^ 2 +
          (ψ.ofLp true).re ^ 2 + (ψ.ofLp true).im ^ 2) * hcs
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

private theorem rotBool_apply (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (ψ : EuclideanSpace ℂ Bool) (b : Bool) :
    (rotBool c s hcs ψ).ofLp b =
      if b then (s : ℂ) * ψ.ofLp false + (c : ℂ) * ψ.ofLp true
      else (c : ℂ) * ψ.ofLp false - (s : ℂ) * ψ.ofLp true :=
  rfl

private theorem inv_sqrt_two_real_sq : (Real.sqrt 2)⁻¹ ^ 2 + (Real.sqrt 2)⁻¹ ^ 2 = 1 := by
  rw [inv_pow, Real.sq_sqrt zero_le_two]
  norm_num

/-- 1-qubit Hadamard gate on `ℂ^Bool`. -/
private noncomputable def hadBool :
    EuclideanSpace ℂ Bool ≃ₗᵢ[ℂ] EuclideanSpace ℂ Bool :=
  (phaseStep true).trans (rotBool (Real.sqrt 2)⁻¹ (Real.sqrt 2)⁻¹ inv_sqrt_two_real_sq)

private theorem hadBool_apply (ψ : EuclideanSpace ℂ Bool) (c : Bool) :
    (hadBool ψ).ofLp c = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
      (if c then ψ.ofLp false - ψ.ofLp true else ψ.ofLp false + ψ.ofLp true) := by
  cases c <;> simp [hadBool, rotBool_apply, phaseStep_apply] <;> ring

private theorem hadBool_self (ψ : EuclideanSpace ℂ Bool) : hadBool (hadBool ψ) = ψ := by
  ext c
  cases c <;> simp only [hadBool_apply, ite_true, Bool.false_eq_true, ite_false] <;>
    (ring_nf; simp only [inv_sqrt_two_sq]; ring)

private noncomputable def swapBool :
    EuclideanSpace ℂ Bool ≃ₗᵢ[ℂ] EuclideanSpace ℂ Bool :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.swap false true)

@[simp] private theorem swapBool_apply (ψ : EuclideanSpace ℂ Bool) (c : Bool) :
    (swapBool ψ).ofLp c = ψ.ofLp (!c) := by
  cases c <;> rfl

private theorem hadBool_phaseStep_hadBool (flag : Bool) (ψ : EuclideanSpace ℂ Bool) :
    hadBool (phaseStep flag (hadBool ψ)) = if flag then swapBool ψ else ψ := by
  ext c
  cases flag <;> cases c <;>
    simp only [ite_true, hadBool_apply, phaseStep_apply, swapBool_apply, Bool.false_eq_true,
      ite_false, Bool.and_true, Bool.and_false, Bool.not_false, Bool.not_true] <;>
    (ring_nf; simp only [inv_sqrt_two_sq]; ring)

private noncomputable def ctrlUnit (R : EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V) :
    EuclideanSpace ℂ (Bool × V) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × V) :=
  fiberIso fun c => if c then R else .refl ℂ (EuclideanSpace ℂ V)

/-- Unitary `G` on `ℂ^(Bool × V)` turning controlled `Z` into controlled `R` when `R² = 1`. -/
private noncomputable def invBoolV (R : EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V) :
    EuclideanSpace ℂ (Bool × V) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × V) :=
  (liftBoolLeft fun _ => hadBool).trans ((ctrlUnit R).trans (liftBoolLeft fun _ => hadBool))

private theorem invBoolV_ctrlZ_invBoolV (R : EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V)
    (hR : ∀ φ, R (R φ) = φ) (flag : Bool) (φ : EuclideanSpace ℂ V) :
    invBoolV R (ctrlZ flag (invBoolV R (embedBoolFalse φ))) =
      embedBoolFalse (if flag then R φ else φ) := by
  have hmid (x : EuclideanSpace ℂ (Bool × V)) :
      liftBoolLeft (fun _ => hadBool) (ctrlZ flag (liftBoolLeft (fun _ => hadBool) x)) =
        if flag then liftBoolLeft (fun _ => swapBool) x else x := by
    ext ⟨c, v⟩
    cases flag <;> simp only [ctrlZ, liftBoolLeft_apply, WithLp.toLp_ofLp,
      hadBool_phaseStep_hadBool, ite_true, Bool.false_eq_true, ite_false]
  have hH (x : EuclideanSpace ℂ (Bool × V)) :
      liftBoolLeft (fun _ => hadBool) (liftBoolLeft (fun _ => hadBool) x) = x := by
    ext ⟨c, v⟩
    simp [hadBool_self]
  simp only [invBoolV, LinearIsometryEquiv.trans_apply, hmid]
  cases flag
  · simp only [Bool.false_eq_true, ite_false]
    have hRR (x : EuclideanSpace ℂ (Bool × V)) : ctrlUnit R (ctrlUnit R x) = x := by
      ext ⟨c, v⟩
      cases c <;> simp [ctrlUnit, sliceSecond, hR]
    rw [hRR, hH]
  · simp only [ite_true]
    have hctrl : ∀ (x : EuclideanSpace ℂ (Bool × V)) (c : Bool),
        sliceSecond (ctrlUnit R x) c = if c then R (sliceSecond x true) else sliceSecond x false :=
      fun x c => by ext v; cases c <;> simp [ctrlUnit, sliceSecond]
    have hemb : ∀ (u : EuclideanSpace ℂ V) (c : Bool),
        sliceSecond (liftBoolLeft (fun _ => hadBool) (embedBoolFalse u)) c =
          (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • u := fun u c => by
      ext v
      cases c <;> simp [liftBoolLeft_apply, hadBool_apply, embedBoolFalse]
    have hswap : ctrlUnit R (liftBoolLeft (fun _ => swapBool)
        (ctrlUnit R (liftBoolLeft (fun _ => hadBool) (embedBoolFalse φ)))) =
        liftBoolLeft (fun _ => hadBool) (embedBoolFalse (R φ)) := by
      ext ⟨c, v⟩
      rw [← sliceSecond_apply, ← sliceSecond_apply]
      have hs : ∀ (x : EuclideanSpace ℂ (Bool × V)) (b : Bool),
          sliceSecond (liftBoolLeft (fun _ => swapBool) x) b = sliceSecond x (!b) :=
        fun _ b => by ext u; cases b <;> simp [liftBoolLeft_apply, swapBool_apply]
      cases c <;> simp only [hctrl, hs, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ite_false, ite_true, hemb, map_smul]
    rw [hswap, hH]

private theorem bvSlice_liftValueIso_valueOracle {N : ℕ} {α : Type*} (e : ι ≃ Fin N)
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V)) (a₀ : α)
    (y : ValueState ι V W) (j : Fin N) (w : W) :
    bvSlice (liftValueIso e (valueOracle step fun _ => a₀).toLinearIsometry (embedState e y)) j
        w =
      embedBoolFalse (step a₀ (valSlice y (e.symm j) w)) := by
  rw [liftValueIso_embedState, bvSlice_embedState]
  rfl

private theorem step_rel_ite_apply {N : ℕ} {α : Type*} (e : ι ≃ Fin N)
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (a₀ a₁ : α) (b : Fin N → Bool) (y : ValueState ι V W) (j : Fin N) (v : V) (w : W) :
    (if b j then ((step a₀).symm.trans (step a₁)) ((step a₀) (valSlice y (e.symm j) w))
      else (step a₀) (valSlice y (e.symm j) w)).ofLp v =
      (valueOracle step (fun i => if b (e i) then a₁ else a₀) y).ofLp (e.symm j, v, w) := by
  rw [valueOracle_apply, Equiv.apply_symm_apply]
  cases b j <;> simp only [valSlice, Bool.false_eq_true, ite_false, ite_true,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]

private theorem exists_sim_stride {N : ℕ} {α : Type*} (e : ι ≃ Fin N)
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (a₀ a₁ : α) (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    (ψ₀ : ValueState ι V W) (T stride : ℕ) (hstride : 0 < stride)
    (Gpre Gpost : EuclideanSpace ℂ (Bool × V) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × V))
    (Vmid : State N (V × W) →ₗᵢ[ℂ] State N (V × W))
    (hstep : ∀ (b : Fin N → Bool) (y : ValueState ι V W),
      liftBoolV Gpost (phaseOracle b (Nat.iterate (fun u => Vmid (phaseOracle b u))
        (stride - 1) (liftBoolV Gpre (liftValueIso e
          (valueOracle step fun _ => a₀).toLinearIsometry (embedState e y))))) =
        embedState e (valueOracle step (fun i => if b (e i) then a₁ else a₀) y)) :
    ∃ (Vsim : ℕ → State N (V × W) →ₗᵢ[ℂ] State N (V × W)) (φ₀ : State N (V × W)),
      ‖φ₀‖ = ‖ψ₀‖ ∧
        ∀ (b : Fin N → Bool) (S : Finset (ι × V × W)),
          measureProb (run Vsim φ₀ b (stride * T)) (S.map (embedOutcome e)) =
            measureProb (runValue step U ψ₀ (fun i => if b (e i) then a₁ else a₀) T) S := by
  classical
  let A0 : State N (V × W) →ₗᵢ[ℂ] State N (V × W) :=
    liftValueIso e (valueOracle step fun _ => a₀).toLinearIsometry
  let pre : State N (V × W) →ₗᵢ[ℂ] State N (V × W) := (liftBoolV Gpre).toLinearIsometry.comp A0
  let Vsim : ℕ → State N (V × W) →ₗᵢ[ℂ] State N (V × W) := fun q =>
    if q = 0 then
      if 0 < T then pre.comp (liftValueIso e (U 0)) else liftValueIso e (U 0)
    else if q % stride ≠ 0 then
      Vmid
    else
      let r := q / stride - 1
      if r + 1 < T then
        pre.comp ((liftValueIso e (U (r + 1))).comp (liftBoolV Gpost).toLinearIsometry)
      else if r + 1 = T then
        (liftValueIso e (U T)).comp (liftBoolV Gpost).toLinearIsometry
      else LinearIsometry.id
  refine ⟨Vsim, embedState e ψ₀, (embedState e).norm_map ψ₀, fun b S => ?_⟩
  let x : ι → α := fun i => if b (e i) then a₁ else a₀
  have hrun (t : ℕ) (ht : t ≤ T) :
      run Vsim (embedState e ψ₀) b (stride * t) =
        if t < T then pre (embedState e (runValue step U ψ₀ x t))
        else embedState e (runValue step U ψ₀ x T) := by
    induction t with
    | zero =>
      rcases Nat.eq_zero_or_pos T with rfl | hT <;>
        simp [run, Vsim, pre, liftValueIso_embedState, runValue, *]
    | succ t ih =>
      have ht' : t < T := by omega
      have hiter (k : ℕ) (hk : k < stride) :
          run Vsim (embedState e ψ₀) b (stride * t + k) =
            Nat.iterate (fun u => Vmid (phaseOracle b u)) k
              (pre (embedState e (runValue step U ψ₀ x t))) := by
        induction k with
        | zero => simpa [ht'] using ih ht'.le
        | succ k ihk =>
          have hmod : (stride * t + k + 1) % stride ≠ 0 := by
            rw [add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt hk]; omega
          have hVmid : Vsim (stride * t + k + 1) = Vmid := by simp [Vsim, hmod]
          rw [← add_assoc, run, hVmid, ihk (by omega), Function.iterate_succ_apply']
      have hq : stride * (t + 1) = (stride * t + (stride - 1)) + 1 := by
        rw [Nat.mul_succ]; omega
      have hVend : Vsim (stride * (t + 1)) =
          if t + 1 < T then
            pre.comp ((liftValueIso e (U (t + 1))).comp (liftBoolV Gpost).toLinearIsometry)
          else (liftValueIso e (U T)).comp (liftBoolV Gpost).toLinearIsometry := by
        have hdiv : stride * (t + 1) / stride - 1 = t := by
          rw [Nat.mul_div_right _ hstride]; omega
        simp only [Vsim, Nat.ne_of_gt (Nat.mul_pos hstride (Nat.succ_pos t)), ite_false,
          Nat.mul_mod_right, ne_eq, not_true_eq_false, hdiv]
        split_ifs <;> first | rfl | omega
      rw [hq, run, hiter (stride - 1) (by omega), ← hq, hVend]
      split_ifs with hlt <;> simp only [pre, A0, LinearIsometry.coe_comp, Function.comp_apply,
        LinearIsometryEquiv.coe_toLinearIsometry]
      · rw [hstep, liftValueIso_embedState, ← runValue]
      · obtain rfl : T = t + 1 := by omega
        rw [hstep, liftValueIso_embedState, ← runValue]
  simpa only [lt_irrefl, ite_false, measureProb_embedState] using
    congrArg (measureProb · (S.map (embedOutcome e))) (hrun T le_rfl)

/-- **1-query simulation of an involutive two-valued oracle restriction**: if
`(step a₀).symm.trans (step a₁)` is an involution, any `T`-query value-query algorithm restricted
to `{a₀, a₁}` along `e : ι ≃ Fin N` can be simulated by `T` binary phase-oracle queries. -/
theorem exists_sim_involution {N : ℕ}
    {α : Type*} (e : ι ≃ Fin N)
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (a₀ a₁ : α)
    (hR : ∀ φ, ((step a₀).symm.trans (step a₁)) (((step a₀).symm.trans (step a₁)) φ) = φ)
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    (ψ₀ : ValueState ι V W) (T : ℕ) :
    ∃ (Vsim : ℕ → State N (V × W) →ₗᵢ[ℂ] State N (V × W)) (φ₀ : State N (V × W)),
      ‖φ₀‖ = ‖ψ₀‖ ∧
        ∀ (b : Fin N → Bool) (S : Finset (ι × V × W)),
          measureProb (run Vsim φ₀ b T) (S.map (embedOutcome e)) =
            measureProb (runValue step U ψ₀ (fun i => if b (e i) then a₁ else a₀) T) S := by
  classical
  let R := (step a₀).symm.trans (step a₁)
  let G := invBoolV R
  have hstep : ∀ (b : Fin N → Bool) (y : ValueState ι V W),
      liftBoolV G (phaseOracle b (liftBoolV G (liftValueIso e
        (valueOracle step fun _ => a₀).toLinearIsometry (embedState e y)))) =
        embedState e (valueOracle step (fun i => if b (e i) then a₁ else a₀) y) := fun b y => by
    refine eq_embedState_of_bvSlice e _ _ fun j w => ?_
    rw [bvSlice_liftBoolV, bvSlice_phaseOracle, bvSlice_liftBoolV,
      bvSlice_liftValueIso_valueOracle, invBoolV_ctrlZ_invBoolV R hR]
    congr 1
    ext v
    exact step_rel_ite_apply e step a₀ a₁ b y j v w
  simpa only [one_mul] using exists_sim_stride e step a₀ a₁ U ψ₀ T 1 Nat.one_pos G G
    LinearIsometry.id fun b y => by simpa using hstep b y

/-! #### 2-query simulation for arbitrary unitary relative step -/

/-- Choosing `(c, s)` with `c² + s² = 1`, `c² - s² = μ`, and `2 c s = ν` for any point `(μ, ν)`
on the unit circle. -/
private theorem exists_half_angle (μ ν : ℝ) (h : μ ^ 2 + ν ^ 2 = 1) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧ c ^ 2 - s ^ 2 = μ ∧ 2 * c * s = ν := by
  by_cases hm : μ = -1
  · refine ⟨0, 1, by norm_num, ?_, by nlinarith⟩
    norm_num [hm]
  · have hm_le : -1 ≤ μ := by nlinarith [sq_nonneg (μ + 1), sq_nonneg ν]
    have hpos : 0 < (1 + μ) / 2 := by linarith [lt_of_le_of_ne hm_le (Ne.symm hm)]
    let c := Real.sqrt ((1 + μ) / 2)
    have hc_pos : 0 < c := Real.sqrt_pos.mpr hpos
    have hc2 : c ^ 2 = (1 + μ) / 2 := Real.sq_sqrt hpos.le
    let s := ν / (2 * c)
    have hs2 : s ^ 2 = (1 - μ) / 2 := by
      have h1 : ν ^ 2 = (1 - μ) * (1 + μ) := by linarith
      have hden : (2 * c) ^ 2 = 2 * (1 + μ) := by rw [mul_pow, hc2]; ring
      rw [div_pow, h1, hden]
      field_simp [ne_of_gt (by linarith : (0 : ℝ) < 1 + μ)]
    exact ⟨c, s, by linarith, by linarith, mul_div_cancel₀ ν (mul_ne_zero two_ne_zero hc_pos.ne')⟩

private noncomputable def phaseSBool :
    EuclideanSpace ℂ Bool ≃ₗᵢ[ℂ] EuclideanSpace ℂ Bool where
  toFun ψ := WithLp.toLp 2 fun c => (if c then Complex.I else 1) * ψ.ofLp c
  invFun ψ := WithLp.toLp 2 fun c => (if c then -Complex.I else 1) * ψ.ofLp c
  map_add' ψ₁ ψ₂ := by ext c; simp only [WithLp.ofLp_add, Pi.add_apply]; ring
  map_smul' r ψ := by ext c; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
  left_inv ψ := by ext c; cases c <;> simp [← mul_assoc, Complex.I_mul_I]
  right_inv ψ := by ext c; cases c <;> simp [← mul_assoc, Complex.I_mul_I]
  norm_map' ψ := by
    have hsq : ‖(WithLp.toLp 2 fun c => (if c then Complex.I else 1) * ψ.ofLp c :
        EuclideanSpace ℂ Bool)‖ ^ 2 = ‖ψ‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      refine sum_congr rfl fun c _ => ?_
      cases c <;> simp
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

private theorem phaseSBool_symm_apply (ψ : EuclideanSpace ℂ Bool) (c : Bool) :
    (phaseSBool.symm ψ).ofLp c = (if c then -Complex.I else 1) * ψ.ofLp c :=
  rfl

/-- 1-qubit preparation mapping `|false⟩ ↦ (|false⟩ + i |true⟩) / √2` and
`|true⟩ ↦ (|false⟩ - i |true⟩) / √2`. -/
private noncomputable def prepYBool :
    EuclideanSpace ℂ Bool ≃ₗᵢ[ℂ] EuclideanSpace ℂ Bool :=
  hadBool.trans phaseSBool

private theorem prepYBool_apply (ψ : EuclideanSpace ℂ Bool) (c : Bool) :
    (prepYBool ψ).ofLp c = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
      (if c then Complex.I * (ψ.ofLp false - ψ.ofLp true)
      else ψ.ofLp false + ψ.ofLp true) := by
  cases c <;> simp [prepYBool, phaseSBool, hadBool_apply]
  ring

private theorem prepYBool_symm_apply (ψ : EuclideanSpace ℂ Bool) (c : Bool) :
    (prepYBool.symm ψ).ofLp c = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) *
      (if c then ψ.ofLp false + Complex.I * ψ.ofLp true
      else ψ.ofLp false - Complex.I * ψ.ofLp true) := by
  have hsym : hadBool.symm = hadBool :=
    LinearIsometryEquiv.ext fun x => hadBool.symm_apply_eq.mpr (hadBool_self x).symm
  cases c <;> simp [prepYBool, hsym, hadBool_apply, phaseSBool_symm_apply]
  ring

private theorem prepY_rotBool_gadget (c s μ ν : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (hmu : c ^ 2 - s ^ 2 = μ) (hnu : 2 * c * s = ν) (flag : Bool) (z : ℂ) :
    (rotBool c (-s) (by nlinarith)).trans prepYBool.symm
        (phaseStep flag (rotBool c s hcs (phaseStep flag (prepYBool (WithLp.toLp 2 fun b =>
          if b then 0 else z))))) =
      WithLp.toLp 2 fun b =>
        if b then 0 else (if flag then (μ : ℂ) + Complex.I * ν else 1) * z := by
  have hcs' : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  have hmu' : (c : ℂ) ^ 2 - (s : ℂ) ^ 2 = μ := by exact_mod_cast hmu
  have hnu' : 2 * (c : ℂ) * s = ν := by exact_mod_cast hnu
  have hc2 : (c : ℂ) ^ 2 = (1 + (μ : ℂ)) / 2 := by linear_combination (hcs' + hmu') / 2
  have hs2 : (s : ℂ) ^ 2 = (1 - (μ : ℂ)) / 2 := by linear_combination (hcs' - hmu') / 2
  ext b
  cases flag <;> cases b <;>
    simp only [LinearIsometryEquiv.trans_apply, prepYBool_symm_apply, rotBool_apply,
      phaseStep_apply, prepYBool_apply, ite_true, Bool.false_eq_true, ite_false,
      Complex.ofReal_neg, Bool.and_self, Bool.and_false, Bool.false_and] <;>
    ring_nf <;> simp only [inv_sqrt_two_sq, Complex.I_sq, hc2, hs2]
  · ring
  · ring
  · linear_combination Complex.I * z * hnu'
  · ring

private noncomputable def liftBasis {B₁ B₂ : Type*} [Fintype B₁] [Fintype B₂]
    (U : EuclideanSpace ℂ B₁ ≃ₗᵢ[ℂ] EuclideanSpace ℂ B₂) :
    EuclideanSpace ℂ (Bool × B₁) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × B₂) :=
  fiberIso fun _ : Bool => U

private theorem liftBasis_ctrlZ {B₁ B₂ : Type*} [Fintype B₁] [Fintype B₂]
    (U : EuclideanSpace ℂ B₁ ≃ₗᵢ[ℂ] EuclideanSpace ℂ B₂) (flag : Bool)
    (φ : EuclideanSpace ℂ (Bool × B₁)) :
    liftBasis U (ctrlZ flag φ) = ctrlZ flag (liftBasis U φ) := by
  ext ⟨c, k⟩
  have hslice : sliceSecond (ctrlZ flag φ) c =
      (if c && flag then (-1 : ℂ) else 1) • sliceSecond φ c := by
    ext v
    cases flag <;> cases c <;> simp [sliceSecond]
  change (U (sliceSecond (ctrlZ flag φ) c)).ofLp k =
    (if c && flag then (-1 : ℂ) else 1) * (U (sliceSecond φ c)).ofLp k
  rw [hslice, map_smul, PiLp.smul_apply, smul_eq_mul]

private theorem liftBasis_embedBoolFalse {B₁ B₂ : Type*} [Fintype B₁] [Fintype B₂]
    (U : EuclideanSpace ℂ B₁ ≃ₗᵢ[ℂ] EuclideanSpace ℂ B₂) (x : EuclideanSpace ℂ B₁) :
    liftBasis U (embedBoolFalse x) = embedBoolFalse (U x) := by
  ext ⟨b, k⟩
  have hz : (WithLp.toLp 2 fun _ : B₁ => (0 : ℂ)) = 0 := rfl
  cases b <;> simp [liftBasis, embedBoolFalse, sliceSecond, hz]

/-- **2-query simulation of an arbitrary two-valued oracle restriction**: any `T`-query
value-query algorithm restricted to `{a₀, a₁}` along `e : ι ≃ Fin N` can be simulated by `2 * T`
binary phase-oracle queries. -/
theorem exists_sim_value {N : ℕ}
    {α : Type*} (e : ι ≃ Fin N)
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (a₀ a₁ : α)
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    (ψ₀ : ValueState ι V W) (T : ℕ) :
    ∃ (Vsim : ℕ → State N (V × W) →ₗᵢ[ℂ] State N (V × W)) (φ₀ : State N (V × W)),
      ‖φ₀‖ = ‖ψ₀‖ ∧
        ∀ (b : Fin N → Bool) (S : Finset (ι × V × W)),
          measureProb (run Vsim φ₀ b (2 * T)) (S.map (embedOutcome e)) =
            measureProb (runValue step U ψ₀ (fun i => if b (e i) then a₁ else a₀) T) S := by
  classical
  let R := (step a₀).symm.trans (step a₁)
  obtain ⟨bas, μ, ν, hunit, heig⟩ := LinearIsometryEquiv.exists_orthonormalBasis_eigenvectors R
  let d := Module.finrank ℂ (EuclideanSpace ℂ V)
  choose c s hcs hmu hnu using fun k : Fin d => exists_half_angle (μ k) (ν k) (hunit k)
  let Bchg : EuclideanSpace ℂ (Bool × V) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × Fin d) :=
    liftBasis bas.repr
  let Qpre : EuclideanSpace ℂ (Bool × Fin d) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × Fin d) :=
    liftBoolLeft fun _ => prepYBool
  let Qmid : EuclideanSpace ℂ (Bool × Fin d) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × Fin d) :=
    liftBoolLeft fun k => rotBool (c k) (s k) (hcs k)
  let Qpost : EuclideanSpace ℂ (Bool × Fin d) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × Fin d) :=
    liftBoolLeft fun k => (rotBool (c k) (-s k) (by nlinarith [hcs k])).trans prepYBool.symm
  let Gpre : EuclideanSpace ℂ (Bool × V) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × V) :=
    Bchg.trans (Qpre.trans Bchg.symm)
  let Gmid : EuclideanSpace ℂ (Bool × V) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × V) :=
    Bchg.trans (Qmid.trans Bchg.symm)
  let Gpost : EuclideanSpace ℂ (Bool × V) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Bool × V) :=
    Bchg.trans (Qpost.trans Bchg.symm)
  have hgadget (flag : Bool) (φ : EuclideanSpace ℂ V) :
      Gpost (ctrlZ flag (Gmid (ctrlZ flag (Gpre (embedBoolFalse φ))))) =
        embedBoolFalse (if flag then R φ else φ) := by
    simp only [Gpost, Gmid, Gpre, Bchg, LinearIsometryEquiv.trans_apply, liftBasis_ctrlZ,
      LinearIsometryEquiv.apply_symm_apply, liftBasis_embedBoolFalse]
    have hQ : Qpost (ctrlZ flag (Qmid (ctrlZ flag (Qpre (embedBoolFalse (bas.repr φ)))))) =
        embedBoolFalse (WithLp.toLp 2 fun k =>
          (if flag then (μ k : ℂ) + Complex.I * ν k else 1) * (bas.repr φ).ofLp k) := by
      ext ⟨b, k⟩
      have hmid_k (x : EuclideanSpace ℂ (Bool × Fin d)) :
          (WithLp.toLp 2 fun b' => (ctrlZ flag x).ofLp (b', k)) =
            phaseStep flag (WithLp.toLp 2 fun b' => x.ofLp (b', k)) := rfl
      simp only [Qpost, Qmid, Qpre, liftBoolLeft_apply, hmid_k]
      exact congrArg (fun u => u.ofLp b)
        (prepY_rotBool_gadget (c k) (s k) (μ k) (ν k) (hcs k) (hmu k) (hnu k) flag
          ((bas.repr φ).ofLp k))
    have hRbas : (WithLp.toLp 2 fun k =>
        (if flag then (μ k : ℂ) + Complex.I * ν k else 1) * (bas.repr φ).ofLp k) =
        bas.repr (if flag then R φ else φ) := by
      cases flag
      · simp
      · simp only [ite_true]
        ext k
        conv_rhs => rw [← bas.sum_repr φ]
        simp only [map_sum, map_smul, heig, bas.repr_self, WithLp.ofLp_sum, Finset.sum_apply,
          PiLp.smul_apply, EuclideanSpace.single, PiLp.single_apply, smul_eq_mul]
        simp [mul_comm]
    rw [hQ, hRbas, ← liftBasis_embedBoolFalse bas.repr, LinearIsometryEquiv.symm_apply_apply]
  have hstep : ∀ (b : Fin N → Bool) (y : ValueState ι V W),
      liftBoolV Gpost (phaseOracle b ((liftBoolV Gmid).toLinearIsometry (phaseOracle b
        (liftBoolV Gpre (liftValueIso e (valueOracle step fun _ => a₀).toLinearIsometry
          (embedState e y)))))) =
        embedState e (valueOracle step (fun i => if b (e i) then a₁ else a₀) y) := fun b y => by
    refine eq_embedState_of_bvSlice e _ _ fun j w => ?_
    simp only [LinearIsometryEquiv.coe_toLinearIsometry, bvSlice_liftBoolV, bvSlice_phaseOracle]
    rw [bvSlice_liftValueIso_valueOracle, hgadget]
    congr 1
    ext v
    exact step_rel_ite_apply e step a₀ a₁ b y j v w
  exact exists_sim_stride e step a₀ a₁ U ψ₀ T 2 (by omega) Gpre Gpost
    (liftBoolV Gmid).toLinearIsometry hstep

end TwoValueSim

section IndexToValue

private def indexRouteFun {ι V W : Type*} [DecidableEq ι] [DecidableEq V]
    (idx : ι × V × W → ι) (v₀ : V) (i₀ : ι) :
    ι × V × Bool × V × W × ι → ι × V × Bool × V × W × ι
  | (i, v, false, v', w, i') =>
    if v' = v₀ ∧ i' = i₀ then (idx (i, v, w), v₀, true, v, w, i)
    else (i, v, false, v', w, i')
  | (i, v, true, v', w, i') =>
    if v = v₀ ∧ idx (i', v', w) = i then (i', v', false, v₀, w, i₀)
    else (i, v, true, v', w, i')

private theorem indexRouteFun_involutive {ι V W : Type*} [DecidableEq ι] [DecidableEq V]
    (idx : ι × V × W → ι) (v₀ : V) (i₀ : ι) (q : ι × V × Bool × V × W × ι) :
    indexRouteFun idx v₀ i₀ (indexRouteFun idx v₀ i₀ q) = q := by
  rcases q with ⟨i, v, b, v', w, i'⟩
  cases b <;> dsimp only [indexRouteFun] <;> split_ifs <;> simp_all

private def indexRoutePerm {ι V W : Type*} [DecidableEq ι] [DecidableEq V]
    (idx : ι × V × W → ι) (v₀ : V) (i₀ : ι) :
    Equiv.Perm (ι × V × Bool × V × W × ι) where
  toFun := indexRouteFun idx v₀ i₀
  invFun := indexRouteFun idx v₀ i₀
  left_inv := indexRouteFun_involutive idx v₀ i₀
  right_inv := indexRouteFun_involutive idx v₀ i₀

private def extProdEquiv {ι V W : Type*} :
    (ι × V × Bool × V × W × ι) ≃ ((Bool × V × ι) × (ι × V × W)) where
  toFun | (i, v, b, v', w, i') => ((b, v', i'), (i, v, w))
  invFun | ((b, v', i'), (i, v, w)) => (i, v, b, v', w, i')
  left_inv _ := rfl
  right_inv _ := rfl

private def idxProdEquiv {ι V W : Type*} :
    (ι × V × Bool × V × W × ι) ≃ ((ι × V × W) × Bool × ι × V) where
  toFun | (j, vout, b, v, w, i) => ((i, v, w), b, j, vout)
  invFun | ((i, v, w), b, j, vout) => (j, vout, b, v, w, i)
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def embedFalse {ι V W : Type*} [Fintype ι] [Fintype V] [Fintype W]
    (v₀ : V) (i₀ : ι) :
    ValueState ι V W →ₗᵢ[ℂ] ValueState ι V (Bool × V × W × ι) :=
  LinearIsometry.piLpExtendByZero 2 ℂ ℂ (fiberEmb extProdEquiv (false, v₀, i₀))

@[simp] private theorem embedFalse_apply {ι V W : Type*} [Fintype ι] [Fintype V] [Fintype W]
    [DecidableEq ι] [DecidableEq V] (v₀ : V) (i₀ : ι) (ψ : ValueState ι V W) (i : ι) (v : V)
    (b : Bool) (v' : V) (w : W) (i' : ι) :
    (embedFalse v₀ i₀ ψ).ofLp (i, v, b, v', w, i') =
      if b = false ∧ v' = v₀ ∧ i' = i₀ then ψ.ofLp (i, v, w) else 0 := by
  rw [embedFalse, piLpExtendByZero_fiberEmb_apply]
  simp [extProdEquiv]

private noncomputable def liftFalse {ι V W : Type*} [Fintype ι] [Fintype V] [Fintype W]
    [DecidableEq ι] [DecidableEq V] (v₀ : V) (i₀ : ι)
    (U : ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) :
    ValueState ι V (Bool × V × W × ι) →ₗᵢ[ℂ] ValueState ι V (Bool × V × W × ι) :=
  liftFiberIsoAt extProdEquiv (false, v₀, i₀) U

private theorem liftFalse_embedFalse {ι V W : Type*} [Fintype ι] [Fintype V] [Fintype W]
    [DecidableEq ι] [DecidableEq V] (v₀ : V) (i₀ : ι)
    (U : ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) (ψ : ValueState ι V W) :
    liftFalse v₀ i₀ U (embedFalse v₀ i₀ ψ) = embedFalse v₀ i₀ (U ψ) :=
  liftFiberIsoAt_piLpExtendByZero extProdEquiv (false, v₀, i₀) U ψ

/-- **Index-to-value `(T + 1)`-query simulation**: given a `T`-query value-query algorithm
`(U, ψ₀)` returning a query index `idx : ι × V × W → ι`, a basis state `ket v₀` and readout
`read : V → α` such that querying `step (X i)` prepares `read v = X i` with probability `1`
turn it into a `(T + 1)`-query value-returning algorithm with the exact same outcome
distribution. -/
theorem exists_sim_index_to_value {ι V W α : Type*} [Fintype ι] [Fintype V] [Fintype W]
    [Nonempty ι]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (v₀ : V) (read : V → α)
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    (ψ₀ : ValueState ι V W) (T : ℕ) (idx : ι × V × W → ι) :
    ∃ (U' : ℕ → ValueState ι V (Bool × V × W × ι) →ₗᵢ[ℂ] ValueState ι V (Bool × V × W × ι))
      (ψ₀' : ValueState ι V (Bool × V × W × ι)) (out' : ι × V × Bool × V × W × ι → α),
      ‖ψ₀'‖ = ‖ψ₀‖ ∧
        ∀ (X : ι → α),
          (∀ i : ι, (open Classical in
            measureProb (step (X i) (ket v₀)) (univ.filter fun v => read v = X i)) = 1) →
          ∀ (Pred : α → Prop) [DecidablePred Pred],
          measureProb (runValue step U' ψ₀' X (T + 1)) (univ.filter fun q => Pred (out' q)) =
            measureProb (runValue step U ψ₀ X T) (univ.filter fun p => Pred (X (idx p))) := by
  classical
  let i₀ : ι := Classical.arbitrary ι
  let route : ValueState ι V (Bool × V × W × ι) ≃ₗᵢ[ℂ] ValueState ι V (Bool × V × W × ι) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (indexRoutePerm idx v₀ i₀)
  let U' : ℕ → ValueState ι V (Bool × V × W × ι) →ₗᵢ[ℂ] ValueState ι V (Bool × V × W × ι) :=
    fun t =>
      if t < T then liftFalse v₀ i₀ (U t)
      else if t = T then route.toLinearIsometry.comp (liftFalse v₀ i₀ (U T))
      else LinearIsometry.id
  let ψ₀' := embedFalse v₀ i₀ ψ₀
  let out' : ι × V × Bool × V × W × ι → α := fun (_, v, _, _, _, _) => read v
  refine ⟨U', ψ₀', out', (embedFalse v₀ i₀).norm_map ψ₀, fun X hread Pred _ => ?_⟩
  have hvo (ψ : ValueState ι V W) :
      valueOracle step X (embedFalse v₀ i₀ ψ) = embedFalse v₀ i₀ (valueOracle step X ψ) := by
    ext ⟨i, v, b, v', w, i'⟩
    have hs : (WithLp.toLp 2 fun v₁ => (embedFalse v₀ i₀ ψ).ofLp (i, v₁, b, v', w, i')) =
        if b = false ∧ v' = v₀ ∧ i' = i₀ then WithLp.toLp 2 fun v₁ => ψ.ofLp (i, v₁, w)
        else 0 := by
      ext u; split_ifs <;> simp_all
    rw [valueOracle_apply, hs]
    split_ifs with h <;> simp_all [valueOracle_apply]
  have hlt_run (t : ℕ) (ht : t ≤ T) :
      runValue step U' ψ₀' X t =
        if t < T then embedFalse v₀ i₀ (runValue step U ψ₀ X t)
        else route (embedFalse v₀ i₀ (runValue step U ψ₀ X T)) := by
    induction t with
    | zero =>
      rcases Nat.eq_zero_or_pos T with rfl | h0 <;>
        simp [runValue, U', ψ₀', liftFalse_embedFalse, *]
    | succ t ih =>
      have ht' : t < T := by omega
      rw [runValue, ih ht'.le]
      simp only [ht', ite_true, hvo]
      by_cases hlt : t + 1 < T
      · simp only [hlt, ite_true, U', liftFalse_embedFalse, runValue]
      · obtain rfl : t + 1 = T := by omega
        simp [U', liftFalse_embedFalse, runValue]
  have hU_succ : U' (T + 1) = LinearIsometry.id := by simp [U', Nat.not_lt.mpr (Nat.le_succ T)]
  rw [runValue, hU_succ, hlt_run T le_rfl]
  simp only [lt_irrefl, ite_false, LinearIsometry.id_apply]
  set ψT := runValue step U ψ₀ X T
  have hprob_step : ∀ j' : ι,
      measureProb (step (X j') (ket v₀)) (univ.filter fun v => Pred (read v)) =
        if Pred (X j') then 1 else 0 := fun j' => by
    have hnorm : measureProb (step (X j') (ket v₀)) univ = 1 := by
      rw [measureProb_univ, (step (X j')).norm_map, norm_ket, one_pow]
    have hzero : ∀ v, read v ≠ X j' → ‖(step (X j') (ket v₀)).ofLp v‖ ^ 2 = 0 := fun v hv => by
      rw [ofLp_eq_zero_of_measureProb_eq_one (by rw [(step _).norm_map, norm_ket]) (hread j')
        (by simpa using hv), norm_zero, zero_pow two_ne_zero]
    split_ifs with hp
    · rw [← hnorm, measureProb, measureProb]
      exact sum_subset (subset_univ _) fun v _ hv =>
        hzero v fun heq => hv (mem_filter.mpr ⟨mem_univ _, heq ▸ hp⟩)
    · exact sum_eq_zero fun v hv => hzero v fun heq => hp (heq ▸ (mem_filter.mp hv).2)
  have hroute_apply (j : ι) (v' : V) (b : Bool) (v : V) (w : W) (i : ι) :
      (route (embedFalse v₀ i₀ ψT)).ofLp (j, v', b, v, w, i) =
        if b = true ∧ v' = v₀ ∧ idx (i, v, w) = j then ψT.ofLp (i, v, w) else 0 := by
    change (embedFalse v₀ i₀ ψT).ofLp (indexRouteFun idx v₀ i₀ (j, v', b, v, w, i)) = _
    cases b <;> dsimp only [indexRouteFun]
    · by_cases h : v = v₀ ∧ i = i₀ <;> simp [h]
    · by_cases h : v' = v₀ ∧ idx (i, v, w) = j <;> simp [h]
  have hslice (j : ι) (b : Bool) (v : V) (w : W) (i : ι) :
      (WithLp.toLp 2 fun v' => (route (embedFalse v₀ i₀ ψT)).ofLp (j, v', b, v, w, i)) =
        if b = true ∧ idx (i, v, w) = j then ψT.ofLp (i, v, w) • ket v₀ else 0 := by
    ext v'
    rw [hroute_apply]
    by_cases hb : b = true <;> by_cases hj : idx (i, v, w) = j <;> by_cases hv' : v' = v₀ <;>
      simp [hb, hj, hv', ket_apply]
  rw [measureProb, measureProb, sum_filter, sum_filter, Fintype.sum_equiv idxProdEquiv
    (fun q => if Pred (out' q) then
      ‖(valueOracle step X (route (embedFalse v₀ i₀ ψT))).ofLp q‖ ^ 2 else 0)
    (fun q => if Pred (read q.2.2.2) then
      ‖(valueOracle step X (route (embedFalse v₀ i₀ ψT))).ofLp
        (q.2.2.1, q.2.2.2, q.2.1, q.1.2.1, q.1.2.2, q.1.1)‖ ^ 2 else 0)
    (fun ⟨_, _, _, _, _, _⟩ => rfl), Fintype.sum_prod_type]
  refine sum_congr rfl fun p _ => ?_
  have hzero_slice : ∀ (j : ι) (b : Bool), ¬ (b = true ∧ idx p = j) →
      ∑ vout : V, (if Pred (read vout) then
        ‖(valueOracle step X (route (embedFalse v₀ i₀ ψT))).ofLp
          (j, vout, b, p.2.1, p.2.2, p.1)‖ ^ 2 else 0) = 0 := fun j b h =>
    sum_eq_zero fun vout _ => by
      simp only [valueOracle_apply, hslice, h, ite_false, map_zero, WithLp.ofLp_zero,
        Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        ite_self]
  rw [Fintype.sum_prod_type, Fintype.sum_bool, add_comm, Fintype.sum_prod_type,
    sum_eq_zero (fun j _ => hzero_slice j false (by simp)), zero_add, Fintype.sum_prod_type,
    sum_eq_single (idx p) (fun j _ hj => hzero_slice j true fun h => hj h.2.symm)
      (fun h => absurd (mem_univ _) h)]
  have hval_eq : ∑ vout : V, (if Pred (read vout) then
      ‖(valueOracle step X (route (embedFalse v₀ i₀ ψT))).ofLp
        (idx p, vout, true, p.2.1, p.2.2, p.1)‖ ^ 2 else 0) =
      ‖ψT.ofLp p‖ ^ 2 *
        measureProb (step (X (idx p)) (ket v₀)) (univ.filter fun vout => Pred (read vout)) := by
    rw [← measureProb_smul (ψT.ofLp p), measureProb, sum_filter]
    refine sum_congr rfl fun vout _ => ?_
    simp only [valueOracle_apply, hslice, and_self, ite_true, map_smul, PiLp.smul_apply,
      smul_eq_mul]
  rw [hval_eq, hprob_step]
  split_ifs <;> ring

/-- Index-to-value `(T + 1)`-query simulation specialized to a permutation oracle `permStep π` on
two values `a₀, a₁` distinguished at `v₀ : V`. -/
theorem exists_sim_index_to_value_perm {ι V W α : Type*} [Fintype ι] [Fintype V] [Fintype W]
    [Nonempty ι]
    (π : α → Equiv.Perm V) (v₀ : V) (a₀ a₁ : α) (hne : π a₀ v₀ ≠ π a₁ v₀)
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    (ψ₀ : ValueState ι V W) (T : ℕ) (idx : ι × V × W → ι) :
    ∃ (U' : ℕ → ValueState ι V (Bool × V × W × ι) →ₗᵢ[ℂ] ValueState ι V (Bool × V × W × ι))
      (ψ₀' : ValueState ι V (Bool × V × W × ι)) (out' : ι × V × Bool × V × W × ι → α),
      ‖ψ₀'‖ = ‖ψ₀‖ ∧
        ∀ (X : ι → α), (∀ i : ι, X i = a₀ ∨ X i = a₁) →
          ∀ (Pred : α → Prop) [DecidablePred Pred],
          measureProb (runValue (permStep π) U' ψ₀' X (T + 1))
              (univ.filter fun q => Pred (out' q)) =
            measureProb (runValue (permStep π) U ψ₀ X T)
              (univ.filter fun p => Pred (X (idx p))) := by
  classical
  let read : V → α := fun v => if v = π a₀ v₀ then a₀ else a₁
  obtain ⟨U', ψ₀', out', hnorm, hsim⟩ :=
    exists_sim_index_to_value (permStep π) v₀ read U ψ₀ T idx
  refine ⟨U', ψ₀', out', hnorm, fun X hX Pred _ => hsim X (fun i => ?_) Pred⟩
  have hket : permStep π (X i) (ket v₀) = ket (π (X i) v₀) := by
    ext v
    simp [permStep_apply, ket_apply, Equiv.symm_apply_eq]
  rw [hket, measureProb_ket]
  rcases hX i with hi | hi <;> simp [hi, read, hne.symm]

end IndexToValue

end Cslib.Quantum
