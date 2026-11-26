/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.LinearAlgebra.LyapunovCertificate
public import CslibFrontier.Foundations.Analysis.ODE.ImpulseBounds
import Mathlib.Data.List.GetD

/-!
# Kernel-checked energy and decay certificates for LTI impulse responses

A rational model `Cslib.LinearAlgebra.RatLTI n m p` lists the rows of `A`, `B`, `C`, `D` of
`ẋ = A x + B u`, `y = C x + D u`, and `RatLTI.toSystem` reads it as a real `LTISystem` on
`Fin n → ℝ`. An untrusted tool (for example SciPy's Lyapunov solver followed by rational
reconstruction and SymPy's `LDLdecomposition`) proposes a certificate. A Boolean checker, which the
kernel evaluates by `decide +kernel`, recomputes every residual matrix from the model and the
certificate and checks it with the `LDLᵀ` checker of `Cslib.LinearAlgebra.LDLCert`. Soundness
theorems turn acceptance into statements about the impulse response
`h t = C exp (t A) B` of the same model, through the analysis in
`CslibFrontier.Foundations.Analysis.ODE.ImpulseBounds`.

* `Cslib.LinearAlgebra.EnergyCert` (exact energy): a Lyapunov certificate for stability, a
  Gramian `W` with `Aᵀ W + W A + Cᵀ C = 0` exactly, and the energy `tr (Bᵀ W B)`. Acceptance
  proves `∫₀^∞ ‖h t‖_F² dt = energy`, with integrability. `W` may be singular.
* `Cslib.LinearAlgebra.EnergyBoundCert` (energy upper bound): `W ⪰ 0` with
  `Aᵀ W + W A + Cᵀ C ⪯ 0`, so inexact rational reconstructions are accepted. Acceptance proves
  `∫₀^∞ ‖h t‖_F² dt ≤ bound`. It proves nothing about internal stability.
* `Cslib.LinearAlgebra.EnergyLowerCert` (energy lower bound): a Lyapunov certificate for
  stability and a `Q`, not necessarily positive semidefinite, with `Aᵀ Q + Q A + Cᵀ C ⪰ 0`.
  Acceptance proves `bound ≤ ∫₀^∞ ‖h t‖_F² dt`, and with an `EnergyBoundCert` the enclosure
  `∫₀^∞ ‖h t‖_F² dt ∈ [lower, upper]` with exact rational endpoints.
* `Cslib.LinearAlgebra.DecayCert` (decay): `P` with `Aᵀ P + P A + 2 α P ⪯ 0`, `lo 1 ⪯ P ⪯ hi 1`,
  `Cᵀ C ⪯ γ P` and `Bᵀ P B ⪯ β 1`. Acceptance proves the real inequalities
  `Cslib.LinearAlgebra.DecayInequalities`, from which follow exponential stability, the state
  bound `‖x t‖₂² ≤ (hi / lo) exp (-2 α t) ‖x 0‖₂²`, the envelopes
  `‖h t v‖₂² ≤ γ β exp (-2 α t) ‖v‖₂²` and `‖h t‖_F² ≤ γ tr (Bᵀ P B) exp (-2 α t)`, a peak bound,
  the output bound `‖C x t‖₂² ≤ γ hi exp (-2 α t) ‖x 0‖₂²`, the energy tail
  `∫_T^∞ ‖h t‖_F² ≤ γ tr (Bᵀ P B) exp (-2 α T) / (2 α)`, and numerical settling times and tail
  values (`DecayConstants.impulseSettles`, `DecayConstants.stateSettles`,
  `DecayConstants.tailBelow`). The sparse checker of
  `CslibFrontier.Algorithms.LinearAlgebra.SparseImpulseCertificate` proves the same inequalities,
  so these bounds are stated once, for `DecayInequalities`.

## Normalization and units

`‖y‖₂²` is `y ⬝ᵥ y` and `‖M‖_F²` is `∑ i, ∑ j, M i j ^ 2`. Time is in the model's unit, and `h`
carries the units of output per unit of input impulse (input times time). Impulse bounds are per
input direction `v` or summed over the input basis (Frobenius), and state bounds are normalized by
`‖x 0‖₂²`. Nothing is normalized by the initial output, which may vanish (`h 0 = C B = 0` for the
repeated-pole client) although the impulse stores energy in the state.

## Feedthrough

Every certificate first checks `RatLTI.check`: exact shapes, and `D = 0` (`RatLTI.toSystem_D`).
A model with direct feedthrough has the impulse response `D δ₀ + h`, whose energy is infinite, and
it receives none of these certificates. The analysis module states bounds on `h` alone.

## Certified, not optimal

Each accepted certificate gives a valid bound. It need not be the best one: a different `W`, `P`,
`α`, `γ` or `β` may give a smaller bound, and no optimality is claimed. A rejected certificate
proves nothing: rejection is not evidence of instability or of a larger energy.

## Numerical times

`Cslib.LinearAlgebra.expLower N x = ∑_{k < N} x ^ k / k!` is a rational lower bound for `exp x`
when `x ≥ 0` (`Cslib.LinearAlgebra.expLower_le_exp`, from `Real.sum_le_exp_of_nonneg`). A
settling check `γ β vmax² ≤ ε² expLower N (2 α T)` therefore certifies
`γ β vmax² exp (-2 α T) ≤ ε²` in exact rational arithmetic. The symbolic bounds hold without it.

## Main results

* `Cslib.LinearAlgebra.EnergyCert.integrableOn_Ioi_and_integral_eq`,
  `Cslib.LinearAlgebra.EnergyCert.isExponentiallyStable`.
* `Cslib.LinearAlgebra.EnergyBoundCert.integrableOn_Ioi_and_integral_le`.
* `Cslib.LinearAlgebra.EnergyLowerCert.integrableOn_Ioi_and_le_integral`,
  `Cslib.LinearAlgebra.EnergyLowerCert.integrableOn_Ioi_and_integral_mem_Icc`.
* `Cslib.LinearAlgebra.DecayCert.decayInequalities`, and for `DecayInequalities`:
  `DecayInequalities.isExponentiallyStable`, `DecayInequalities.dotProduct_self_le`,
  `DecayInequalities.output_dotProduct_le`,
  `DecayInequalities.integral_Ioi_frobeniusSq_le_of_tailBelow`,
  `DecayInequalities.responseKernel_mulVec_sq_le`,
  `DecayInequalities.responseKernel_mulVec_sq_le_peak`, `DecayInequalities.frobeniusSq_le`,
  `DecayInequalities.integrableOn_Ioi_and_integral_Ioi_frobeniusSq_le`,
  `DecayInequalities.responseKernel_mulVec_sq_le_of_impulseSettles`,
  `DecayInequalities.dotProduct_self_le_of_stateSettles`.

## References

* S. Boyd and C. Barratt, *Linear Controller Design: Limits of Performance*, 1991, §5.6.1.
* S. Boyd, L. El Ghaoui, E. Feron and V. Balakrishnan, *Linear Matrix Inequalities in System and
  Control Theory*, 1994, §5.1.3 and §6.2.
-/

public section

open Set Matrix Mathlib.Tactic.Matrix MeasureTheory

namespace Cslib.LinearAlgebra

/-! ### Rows of the matrices that the certificates check -/

/-- The rows of the `n × n` identity matrix. -/
@[expose] def rowsOne (n : ℕ) : List (List ℚ) :=
  (List.range n).map fun i => (List.range n).map fun j => if i = j then 1 else 0

theorem ofLists_rowsOne (n : ℕ) : ofLists n n (rowsOne n) = 1 := by
  ext i j
  rw [Matrix.one_apply]
  simp [rowsOne, ofLists_apply, ofList_apply, List.getD_eq_getElem?_getD, Fin.val_inj]

/-- Whether every entry of `rows` is `0`. -/
@[expose] def allZero (rows : List (List ℚ)) : Bool := rows.all (·.all (· == 0))

theorem ofLists_eq_zero_of_allZero {k l : ℕ} {rows : List (List ℚ)} (h : allZero rows = true) :
    ofLists k l rows = 0 := by
  ext i j
  simp only [allZero, List.all_eq_true, beq_iff_eq] at h
  rw [ofLists_apply, ofList_apply, Matrix.zero_apply]
  by_cases hi : (i : ℕ) < rows.length
  · rw [List.getD_eq_getElem _ _ hi]
    by_cases hj : (j : ℕ) < rows[(i : ℕ)].length
    · exact List.getD_eq_getElem _ _ hj ▸ h _ (List.getElem_mem hi) _ (List.getElem_mem hj)
    · exact List.getD_eq_default _ _ (not_lt.1 hj)
  · rw [List.getD_eq_default _ _ (not_lt.1 hi), List.getD_nil]

/-- The rows of `Cᵀ * C` for `C` with rows `C`, read as `p × n`. -/
@[expose] def rowsGram (n p : ℕ) (C : List (List ℚ)) : List (List ℚ) :=
  rowsMul n p n (ListMatrix.transpose n C) C

/-- The rows of `Bᵀ * P * B` for `B` read as `n × m` and `P` as `n × n`. -/
@[expose] def rowsCongr (n m : ℕ) (B P : List (List ℚ)) : List (List ℚ) :=
  rowsMul m n m (ListMatrix.transpose m B) (rowsMul n n m P B)

theorem ofLists_rowsGram (n p : ℕ) (C : List (List ℚ)) :
    ofLists n n (rowsGram n p C) = (ofLists p n C)ᵀ * ofLists p n C := by
  rw [rowsGram, ofLists_rowsMul, ofLists_transpose]

theorem ofLists_rowsCongr (n m : ℕ) (B P : List (List ℚ)) :
    ofLists m m (rowsCongr n m B P) = (ofLists n m B)ᵀ * ofLists n n P * ofLists n m B := by
  rw [rowsCongr, ofLists_rowsMul, ofLists_rowsMul, ofLists_transpose, Matrix.mul_assoc]

/-- The real matrix of a rational matrix given by its rows. -/
private abbrev re {k l : ℕ} (M : Matrix (Fin k) (Fin l) ℚ) : Matrix (Fin k) (Fin l) ℝ :=
  M.map ((↑) : ℚ → ℝ)

private theorem re_mul {k l o : ℕ} (M : Matrix (Fin k) (Fin l) ℚ) (N : Matrix (Fin l) (Fin o) ℚ) :
    re (M * N) = re M * re N :=
  Matrix.map_mul (f := Rat.castHom ℝ)

private theorem re_add {k l : ℕ} (M N : Matrix (Fin k) (Fin l) ℚ) : re (M + N) = re M + re N :=
  Matrix.map_add _ Rat.cast_add M N

private theorem re_neg {k l : ℕ} (M : Matrix (Fin k) (Fin l) ℚ) : re (-M) = -re M :=
  Matrix.map_neg _ Rat.cast_neg M

private theorem re_transpose {k l : ℕ} (M : Matrix (Fin k) (Fin l) ℚ) : re Mᵀ = (re M)ᵀ :=
  transpose_map

/-! ### Rational LTI models -/

/-- A finite-dimensional continuous-time LTI model `ẋ = A x + B u`, `y = C x + D u` with rational
data, given by rows: `A` is `n × n`, `B` is `n × m`, `C` is `p × n` and `D` is `p × m`. -/
structure RatLTI (n m p : ℕ) where
  /-- The rows of the state matrix. -/
  A : List (List ℚ)
  /-- The rows of the input matrix. -/
  B : List (List ℚ)
  /-- The rows of the output matrix. -/
  C : List (List ℚ)
  /-- The rows of the direct-feedthrough matrix. -/
  D : List (List ℚ)

namespace RatLTI

variable {n m p : ℕ} (G : RatLTI n m p)

/-- The real system whose matrices are those of `G`, read over `ℝ`. -/
@[expose] noncomputable def toSystem : LTISystem (Fin n) (Fin m) (Fin p) where
  A := (ofLists n n G.A).map (↑)
  B := (ofLists n m G.B).map (↑)
  C := (ofLists p n G.C).map (↑)
  D := (ofLists p m G.D).map (↑)

/-- Whether `G` is a well-formed model without direct feedthrough: every matrix has exactly the
declared shape, and every entry of `D` is `0`. Impulse-response guarantees are reported only for
such models, since the impulse response of a model with `D ≠ 0` contains the impulse `D δ₀`. -/
@[expose] def check : Bool :=
  isShape n n G.A && isShape n m G.B && isShape p n G.C && isShape p m G.D && allZero G.D

theorem toSystem_D (h : G.check = true) : G.toSystem.D = 0 := by
  simp only [check, Bool.and_eq_true] at h
  simp [toSystem, ofLists_eq_zero_of_allZero h.2]

end RatLTI

/-! ### Residual matrices, recomputed from the model and the certificate -/

/-- The rows of `a • M - b • N` for `M`, `N` read as `k × k`. -/
@[expose] def rowsLin (k : ℕ) (a b : ℚ) (M N : List (List ℚ)) : List (List ℚ) :=
  rowsMap₂ (fun x y => a * x - b * y) k k M N

private theorem re_rowsLin (k : ℕ) (a b : ℚ) (M N : List (List ℚ)) :
    re (ofLists k k (rowsLin k a b M N)) =
      (a : ℝ) • re (ofLists k k M) - (b : ℝ) • re (ofLists k k N) := by
  ext i j
  simp [rowsLin, ofLists_rowsMap₂]

private theorem re_lyapunovResidual (n : ℕ) (A P : List (List ℚ)) :
    re (ofLists n n (lyapunovResidual n A P)) =
      -((re (ofLists n n A))ᵀ * re (ofLists n n P) + re (ofLists n n P) * re (ofLists n n A)) := by
  rw [ofLists_lyapunovResidual, re_neg, re_add, re_mul, re_mul, re_transpose]

private theorem re_rowsOne (k : ℕ) : re (ofLists k k (rowsOne k)) = 1 := by
  rw [ofLists_rowsOne]
  exact Matrix.map_one _ Rat.cast_zero Rat.cast_one

private theorem re_rowsGram (n p : ℕ) (C : List (List ℚ)) :
    re (ofLists n n (rowsGram n p C)) = (re (ofLists p n C))ᵀ * re (ofLists p n C) := by
  rw [ofLists_rowsGram, re_mul, re_transpose]

private theorem re_rowsCongr (n m : ℕ) (B P : List (List ℚ)) :
    re (ofLists m m (rowsCongr n m B P)) =
      (re (ofLists n m B))ᵀ * re (ofLists n n P) * re (ofLists n m B) := by
  rw [ofLists_rowsCongr, re_mul, re_mul, re_transpose]

/-- `tr (Bᵀ P B)` over `ℝ` is the cast of its rational value, computed on rows. -/
private theorem trace_re_rowsCongr (n m : ℕ) (B P : List (List ℚ)) :
    trace ((re (ofLists n m B))ᵀ * re (ofLists n n P) * re (ofLists n m B)) =
      ((rowsTrace m (rowsCongr n m B P) : ℚ) : ℝ) := by
  rw [← re_rowsCongr, ← trace_ofLists]
  simp [trace, Rat.cast_sum]

/-- `tr (Bᵀ P B)` for the real system of a model, computed on rows. -/
private theorem trace_toSystem {n m p : ℕ} (G : RatLTI n m p) (P : List (List ℚ)) :
    trace (G.toSystem.Bᵀ * re (ofLists n n P) * G.toSystem.B) =
      ((rowsTrace m (rowsCongr n m G.B P) : ℚ) : ℝ) :=
  trace_re_rowsCongr n m G.B P

/-! ### Certified lower bounds for the exponential -/

/-- The Taylor partial sum `∑_{k < N} x ^ k / k!`, which the kernel evaluates exactly. For `x ≥ 0`
it is a lower bound for `exp x` (`Cslib.LinearAlgebra.expLower_le_exp`), so a check
`a ≤ b * expLower N x` certifies `a exp (-x) ≤ b` without trusting floating-point arithmetic. -/
@[expose] def expLower (N : ℕ) (x : ℚ) : ℚ := ∑ k ∈ Finset.range N, x ^ k / k.factorial

theorem expLower_le_exp (N : ℕ) {x : ℚ} (hx : 0 ≤ x) : (expLower N x : ℝ) ≤ Real.exp x := by
  simpa [expLower] using Real.sum_le_exp_of_nonneg (x := (x : ℝ)) (by exact_mod_cast hx) N

/-- From `a ≤ b * expLower N x` with `x ≥ 0` and `b ≥ 0`: `a * exp (-x) ≤ b`. -/
private theorem mul_exp_neg_le {a b x : ℚ} {N : ℕ} (hx : 0 ≤ x) (hb : 0 ≤ b)
    (h : a ≤ b * expLower N x) : (a : ℝ) * Real.exp (-x) ≤ b := by
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  exact (by exact_mod_cast h : (a : ℝ) ≤ b * (expLower N x : ℝ)).trans
    (mul_le_mul_of_nonneg_left (expLower_le_exp N hx) (by exact_mod_cast hb))

/-- A settling check `K ≤ ε² expLower N (2 α T)` gives `X exp (-2 α t) ≤ ε²` for `0 ≤ X ≤ K` and
`t ≥ T ≥ 0`. -/
private theorem mul_exp_le_of_settles {α T eps2 K : ℚ} {N : ℕ} (hα : 0 < α) (hT : 0 ≤ T)
    (he : 0 < eps2) (hs : K ≤ eps2 * expLower N (2 * α * T)) {X t : ℝ} (hX0 : 0 ≤ X)
    (hX : X ≤ K) (ht : T ≤ t) : X * Real.exp (-(2 * α) * t) ≤ eps2 := by
  have hmono : Real.exp (-(2 * (α : ℝ)) * t) ≤ Real.exp (-(2 * (α : ℝ)) * T) :=
    Real.exp_le_exp.2 (by nlinarith [(by exact_mod_cast hα : (0 : ℝ) < α)])
  calc X * Real.exp (-(2 * α) * t) ≤ K * Real.exp (-(2 * α) * T) := by
        gcongr
        exact hX0.trans hX
    _ = (K : ℝ) * Real.exp (-((2 * α * T : ℚ) : ℝ)) := by
        push_cast; ring_nf
    _ ≤ eps2 := mul_exp_neg_le (by positivity) he.le hs

/-! ### Decay inequalities and their consequences -/

/-- The rational constants of a decay certificate. -/
structure DecayConstants where
  /-- The certified rate `α > 0`: the energy `xᵀ P x` decays like `exp (-2 α t)`. -/
  α : ℚ
  /-- A lower bound `lo > 0` with `lo 1 ⪯ P`. -/
  lo : ℚ
  /-- An upper bound with `P ⪯ hi 1`. -/
  hi : ℚ
  /-- The output gain `γ ≥ 0` with `Cᵀ C ⪯ γ P`. -/
  γ : ℚ
  /-- The input gain `β ≥ 0` with `Bᵀ P B ⪯ β 1`. -/
  β : ℚ

/-- The real facts that a decay certificate establishes for the system `S`, the real matrix `P`
and the constants `k`, with `τ` the exact value of `tr (Bᵀ P B)`: `α > 0`, `0 < lo ≤ hi`,
`γ ≥ 0`, `β ≥ 0`, `Aᵀ P + P A + 2 α P ⪯ 0`, `lo 1 ⪯ P ⪯ hi 1`, `Cᵀ C ⪯ γ P` and
`Bᵀ P B ⪯ β 1`. Both the dense checker (`Cslib.LinearAlgebra.DecayCert.decayInequalities`) and
the sparse one establish it, and every decay bound is proved from it once. -/
structure DecayInequalities {n m p : ℕ} (S : LTISystem (Fin n) (Fin m) (Fin p))
    (P : Matrix (Fin n) (Fin n) ℝ) (k : DecayConstants) (τ : ℚ) : Prop where
  α_pos : 0 < k.α
  lo_pos : 0 < k.lo
  lo_le_hi : k.lo ≤ k.hi
  γ_nonneg : 0 ≤ k.γ
  β_nonneg : 0 ≤ k.β
  decay : (-(S.Aᵀ * P + P * S.A + (2 * (k.α : ℝ)) • P)).PosSemidef
  lo_le : (P - (k.lo : ℝ) • 1).PosSemidef
  le_hi : ((k.hi : ℝ) • 1 - P).PosSemidef
  output : ((k.γ : ℝ) • P - S.Cᵀ * S.C).PosSemidef
  input : ((k.β : ℝ) • 1 - S.Bᵀ * P * S.B).PosSemidef
  trace_eq : trace (S.Bᵀ * P * S.B) = (τ : ℝ)

namespace DecayConstants

variable (k : DecayConstants)

/-- Whether the constants `k` certify settling of the impulse response below `ε` after time `T`
for inputs with `‖v‖₂² ≤ vmax2`: `T ≥ 0`, `vmax2 ≥ 0`, `eps2 = ε² > 0`, and
`γ β vmax2 ≤ ε² expLower N (2 α T)`. It reads only the constants, so it means something only
together with `DecayInequalities` for the same constants. -/
@[expose] def impulseSettles (vmax2 eps2 T : ℚ) (N : ℕ) : Bool :=
  decide (0 ≤ T) && decide (0 ≤ vmax2) && decide (0 < eps2) &&
    decide (k.γ * k.β * vmax2 ≤ eps2 * expLower N (2 * k.α * T))

/-- Whether the constants `k` certify settling of the state below `ε` after time `T` for initial
states with `‖x 0‖₂² ≤ r2`: `T ≥ 0`, `r2 ≥ 0`, `eps2 = ε² > 0`, and
`(hi / lo) r2 ≤ ε² expLower N (2 α T)`. It reads only the constants, so it means something only
together with `DecayInequalities` for the same constants. -/
@[expose] def stateSettles (r2 eps2 T : ℚ) (N : ℕ) : Bool :=
  decide (0 ≤ T) && decide (0 ≤ r2) && decide (0 < eps2) &&
    decide (k.hi / k.lo * r2 ≤ eps2 * expLower N (2 * k.α * T))

/-- Whether the constants `k` and the trace `τ = tr (Bᵀ P B)` certify the numerical energy tail
`∫_T^∞ ‖h t‖_F² ≤ tail`: `T ≥ 0`, `tail ≥ 0` and
`γ τ / (2 α) ≤ tail · expLower N (2 α T)`. -/
@[expose] def tailBelow (τ tail T : ℚ) (N : ℕ) : Bool :=
  decide (0 ≤ T) && decide (0 ≤ tail) &&
    decide (k.γ * τ / (2 * k.α) ≤ tail * expLower N (2 * k.α * T))

end DecayConstants

namespace DecayInequalities

variable {n m p : ℕ} {S : LTISystem (Fin n) (Fin m) (Fin p)} {P : Matrix (Fin n) (Fin n) ℝ}
  {k : DecayConstants} {τ : ℚ}

/-- **Certified state decay.** Every solution `x : ℝ → Fin n → ℝ` of `x' = A *ᵥ x` on `[0, ∞)`
satisfies `‖x t‖₂² ≤ (hi / lo) exp (-2 α t) ‖x 0‖₂²` for `t ≥ 0`, where `‖y‖₂² = y ⬝ᵥ y`. -/
theorem dotProduct_self_le (h : DecayInequalities S P k τ) {x : ℝ → Fin n → ℝ}
    (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x (S.A *ᵥ x t) (Ici 0) t) {t : ℝ}
    (ht : 0 ≤ t) : x t ⬝ᵥ x t ≤ k.hi / k.lo * Real.exp (-(2 * k.α) * t) * (x 0 ⬝ᵥ x 0) :=
  dotProduct_self_le_exp_neg_mul hx h.decay (by exact_mod_cast h.lo_pos) h.lo_le h.le_hi ht

/-- **Decay inequalities prove internal stability.** `ẋ = A x` is exponentially stable in the
Euclidean norm, with constants `√(hi / lo)` and `α`. -/
theorem isExponentiallyStable (h : DecayInequalities S P k τ) :
    (toEuclideanCLM (𝕜 := ℝ) S.A).IsExponentiallyStable := by
  have hq : ∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ ^ 2 = y.ofLp ⬝ᵥ y.ofLp := fun y => by
    rw [EuclideanSpace.norm_sq_eq]
    simp [dotProduct, sq]
  refine ⟨Real.sqrt (k.hi / k.lo), k.α, by exact_mod_cast h.α_pos, fun x hx t ht => ?_⟩
  have hx' := (isTrajectoryOn_toEuclideanCLM_iff (A := S.A)
    (x := fun t => (x t).ofLp) (s := Ici 0)).1 (by simpa using hx)
  have hb := h.dotProduct_self_le hx' ht
  rw [← hq, ← hq] at hb
  have hhl : (0 : ℝ) ≤ k.hi / k.lo := by
    exact_mod_cast div_nonneg (h.lo_pos.le.trans h.lo_le_hi) h.lo_pos.le
  have hr : 0 ≤ Real.sqrt (k.hi / k.lo) * Real.exp (-(k.α * t)) * ‖x 0‖ := by positivity
  refine pow_le_pow_iff_left₀ (norm_nonneg _) hr two_ne_zero |>.1 ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt hhl, ← Real.exp_nat_mul]
  convert hb using 3
  push_cast; ring_nf

/-- **Certified output decay from an initial state.** Every solution of `x' = A *ᵥ x` on
`[0, ∞)` has `‖C x t‖₂² ≤ γ hi exp (-2 α t) ‖x 0‖₂²` for `t ≥ 0`. The bound is normalized by
the initial state, not by the initial output. -/
theorem output_dotProduct_le (h : DecayInequalities S P k τ) {x : ℝ → Fin n → ℝ}
    (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x (S.A *ᵥ x t) (Ici 0) t) {t : ℝ}
    (ht : 0 ≤ t) :
    S.C *ᵥ x t ⬝ᵥ S.C *ᵥ x t ≤ k.γ * k.hi * Real.exp (-(2 * k.α) * t) * (x 0 ⬝ᵥ x 0) :=
  mulVec_dotProduct_le_exp_neg_mul hx h.decay h.output (by exact_mod_cast h.γ_nonneg) h.le_hi ht

/-- **Certified impulse-response envelope.** `‖h t v‖₂² ≤ γ β exp (-2 α t) ‖v‖₂²` for every
input direction `v` and `t ≥ 0`. -/
theorem responseKernel_mulVec_sq_le (h : DecayInequalities S P k τ) (v : Fin m → ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    S.responseKernel t *ᵥ v ⬝ᵥ S.responseKernel t *ᵥ v ≤
      k.γ * k.β * Real.exp (-(2 * k.α) * t) * (v ⬝ᵥ v) :=
  LTISystem.responseKernel_mulVec_sq_le h.decay h.output h.input (by exact_mod_cast h.γ_nonneg)
    v ht

/-- **Certified peak bound.** `‖h t v‖₂² ≤ γ β ‖v‖₂²` for all `t ≥ 0`. This is an upper bound on
the peak, not its value. -/
theorem responseKernel_mulVec_sq_le_peak (h : DecayInequalities S P k τ) (v : Fin m → ℝ)
    {t : ℝ} (ht : 0 ≤ t) :
    S.responseKernel t *ᵥ v ⬝ᵥ S.responseKernel t *ᵥ v ≤ k.γ * k.β * (v ⬝ᵥ v) := by
  refine (h.responseKernel_mulVec_sq_le v ht).trans ?_
  have he : Real.exp (-(2 * (k.α : ℝ)) * t) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [(by exact_mod_cast h.α_pos : (0 : ℝ) < k.α)])
  have hv0 : 0 ≤ v ⬝ᵥ v := by simpa using dotProduct_self_star_nonneg v
  have hgb : (0 : ℝ) ≤ k.γ * k.β := by exact_mod_cast mul_nonneg h.γ_nonneg h.β_nonneg
  nlinarith [mul_nonneg hgb hv0]

/-- **Certified impulse-response settling.** If `k.impulseSettles vmax2 eps2 T N`, then every
input direction with `‖v‖₂² ≤ vmax2` has `‖h t v‖₂² ≤ eps2` for all `t ≥ T`: the impulse
response stays within `ε = √eps2` of `0` from time `T` on. This concerns the response to an
impulse, not to persistent forcing. -/
theorem responseKernel_mulVec_sq_le_of_impulseSettles (h : DecayInequalities S P k τ)
    {vmax2 eps2 T : ℚ} {N : ℕ} (hs : k.impulseSettles vmax2 eps2 T N = true) {v : Fin m → ℝ}
    (hv : v ⬝ᵥ v ≤ vmax2) {t : ℝ} (ht : T ≤ t) :
    S.responseKernel t *ᵥ v ⬝ᵥ S.responseKernel t *ᵥ v ≤ eps2 := by
  simp only [DecayConstants.impulseSettles, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨hT, -⟩, he⟩, hs⟩ := hs
  have hgb : (0 : ℝ) ≤ k.γ * k.β := by exact_mod_cast mul_nonneg h.γ_nonneg h.β_nonneg
  have hv0 : 0 ≤ v ⬝ᵥ v := by simpa using dotProduct_self_star_nonneg v
  calc _ ≤ k.γ * k.β * Real.exp (-(2 * k.α) * t) * (v ⬝ᵥ v) :=
        h.responseKernel_mulVec_sq_le v ((by exact_mod_cast hT : (0 : ℝ) ≤ T).trans ht)
    _ = k.γ * k.β * (v ⬝ᵥ v) * Real.exp (-(2 * k.α) * t) := by ring
    _ ≤ eps2 := mul_exp_le_of_settles h.α_pos hT he hs (by positivity)
        (by push_cast; gcongr) ht

/-- **Certified state settling from a declared initial-state set.** If
`k.stateSettles r2 eps2 T N`, every solution of `x' = A *ᵥ x` on `[0, ∞)` with
`‖x 0‖₂² ≤ r2` has `‖x t‖₂² ≤ eps2` for all `t ≥ T`. -/
theorem dotProduct_self_le_of_stateSettles (h : DecayInequalities S P k τ) {r2 eps2 T : ℚ}
    {N : ℕ} (hs : k.stateSettles r2 eps2 T N = true) {x : ℝ → Fin n → ℝ}
    (hx : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x (S.A *ᵥ x t) (Ici 0) t)
    (hr : x 0 ⬝ᵥ x 0 ≤ r2) {t : ℝ} (ht : T ≤ t) : x t ⬝ᵥ x t ≤ eps2 := by
  simp only [DecayConstants.stateSettles, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨hT, -⟩, he⟩, hs⟩ := hs
  have hv0 : 0 ≤ x 0 ⬝ᵥ x 0 := by simpa using dotProduct_self_star_nonneg (x 0)
  have hhl : (0 : ℝ) ≤ k.hi / k.lo := by
    exact_mod_cast div_nonneg (h.lo_pos.le.trans h.lo_le_hi) h.lo_pos.le
  calc x t ⬝ᵥ x t ≤ k.hi / k.lo * Real.exp (-(2 * k.α) * t) * (x 0 ⬝ᵥ x 0) :=
        h.dotProduct_self_le hx ((by exact_mod_cast hT : (0 : ℝ) ≤ T).trans ht)
    _ = k.hi / k.lo * (x 0 ⬝ᵥ x 0) * Real.exp (-(2 * k.α) * t) := by ring
    _ ≤ eps2 := mul_exp_le_of_settles h.α_pos hT he hs (by positivity)
        (by push_cast; gcongr) ht

/-- **Certified Frobenius envelope.** `‖h t‖_F² ≤ γ τ exp (-2 α t)` for `t ≥ 0`, where
`τ = tr (Bᵀ P B)`. -/
theorem frobeniusSq_le (h : DecayInequalities S P k τ) {t : ℝ} (ht : 0 ≤ t) :
    ∑ i, ∑ j, S.responseKernel t i j ^ 2 ≤ k.γ * τ * Real.exp (-(2 * k.α) * t) := by
  simpa only [h.trace_eq] using
    LTISystem.frobeniusSq_responseKernel_le h.decay h.output (by exact_mod_cast h.γ_nonneg) ht

/-- **Certified energy tail.** For `T ≥ 0` the impulse response energy after `T` is finite and
`∫_T^∞ ‖h t‖_F² ≤ γ τ exp (-2 α T) / (2 α)`, where `τ = tr (Bᵀ P B)`. -/
theorem integrableOn_Ioi_and_integral_Ioi_frobeniusSq_le (h : DecayInequalities S P k τ)
    {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (fun t => ∑ i, ∑ j, S.responseKernel t i j ^ 2) (Ioi T) ∧
      ∫ t in Ioi T, ∑ i, ∑ j, S.responseKernel t i j ^ 2 ≤
        k.γ * τ * Real.exp (-(2 * k.α) * T) / (2 * k.α) := by
  have := LTISystem.integrableOn_Ioi_and_integral_Ioi_frobeniusSq_le
    (by exact_mod_cast h.α_pos) h.decay h.output (by exact_mod_cast h.γ_nonneg) hT
  rwa [h.trace_eq] at this

/-- **Certified numerical energy tail.** If `k.tailBelow τ tail T N`, then
`∫_T^∞ ‖h t‖_F² dt ≤ tail`, the integrand being integrable
(`DecayInequalities.integrableOn_Ioi_and_integral_Ioi_frobeniusSq_le`). -/
theorem integral_Ioi_frobeniusSq_le_of_tailBelow (h : DecayInequalities S P k τ)
    {tail T : ℚ} {N : ℕ} (hs : k.tailBelow τ tail T N = true) :
    ∫ t in Ioi (T : ℝ), ∑ i, ∑ j, S.responseKernel t i j ^ 2 ≤ tail := by
  simp only [DecayConstants.tailBelow, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨hT, htail⟩, hs⟩ := hs
  have hα := h.α_pos
  refine (h.integrableOn_Ioi_and_integral_Ioi_frobeniusSq_le (by exact_mod_cast hT)).2.trans ?_
  refine le_of_eq_of_le ?_ (mul_exp_neg_le (by positivity) htail hs)
  push_cast; ring_nf

end DecayInequalities

/-! ### Dense decay certificates -/

/-- A certificate for decay of the state and of the impulse response of a `RatLTI n m p` model:
the constants, a matrix `P` (rows) and `LDLᵀ` witnesses for the five inequalities
`Aᵀ P + P A + 2 α P ⪯ 0`, `lo 1 ⪯ P`, `P ⪯ hi 1`, `Cᵀ C ⪯ γ P` and `Bᵀ P B ⪯ β 1`. Each
residual is recomputed from the model and `P` by the checker. -/
structure DecayCert extends DecayConstants where
  /-- The rows of the Lyapunov matrix `P`. -/
  P : List (List ℚ)
  /-- A witness for `-(Aᵀ P + P A + 2 α P) ⪰ 0`. -/
  decayW : LDLCert
  /-- A witness for `P - lo 1 ⪰ 0`. -/
  loW : LDLCert
  /-- A witness for `hi 1 - P ⪰ 0`. -/
  hiW : LDLCert
  /-- A witness for `γ P - Cᵀ C ⪰ 0`. -/
  outputW : LDLCert
  /-- A witness for `β 1 - Bᵀ P B ⪰ 0`. -/
  inputW : LDLCert

namespace DecayCert

variable {n m p : ℕ} (c : DecayCert) (G : RatLTI n m p)

/-- Whether `c` is a decay certificate for the model `G`: `G` is well formed without direct
feedthrough, `P` is `n × n`, `α > 0`, `0 < lo ≤ hi`, `γ ≥ 0`, `β ≥ 0`, and the five residuals,
recomputed from `G` and `P`, are accepted as positive semidefinite. -/
@[expose] def check : Bool :=
  G.check && isShape n n c.P && decide (0 < c.α) && decide (0 < c.lo) && decide (c.lo ≤ c.hi) &&
    decide (0 ≤ c.γ) && decide (0 ≤ c.β) &&
    c.decayW.checkPosSemidef n (rowsLin n 1 (2 * c.α) (lyapunovResidual n G.A c.P) c.P) &&
    c.loW.checkPosSemidef n (rowsLin n 1 c.lo c.P (rowsOne n)) &&
    c.hiW.checkPosSemidef n (rowsLin n c.hi 1 (rowsOne n) c.P) &&
    c.outputW.checkPosSemidef n (rowsLin n c.γ 1 c.P (rowsGram n p G.C)) &&
    c.inputW.checkPosSemidef m (rowsLin m c.β 1 (rowsOne m) (rowsCongr n m G.B c.P))

variable {c G}

/-- **Soundness of the dense decay checker.** If the kernel accepts `c` for `G`, the decay
inequalities hold for the real system of `G` and the real matrix `P`, with `τ = tr (Bᵀ P B)`
computed exactly on rows. The bounds then follow from `DecayInequalities`: stability
(`DecayInequalities.isExponentiallyStable`), state, output and impulse-response envelopes,
settling and energy tails. -/
theorem decayInequalities (h : c.check G = true) :
    DecayInequalities G.toSystem ((ofLists n n c.P).map ((↑) : ℚ → ℝ)) c.toDecayConstants
      (rowsTrace m (rowsCongr n m G.B c.P)) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hα⟩, hlo⟩, hlh⟩, hγ⟩, hβ⟩, hd⟩, hl⟩, hh⟩, ho⟩, hi⟩ := h
  have hd := c.decayW.posSemidef_of_checkPosSemidef hd
  have hl := c.loW.posSemidef_of_checkPosSemidef hl
  have hh := c.hiW.posSemidef_of_checkPosSemidef hh
  have ho := c.outputW.posSemidef_of_checkPosSemidef ho
  have hi := c.inputW.posSemidef_of_checkPosSemidef hi
  change (re _).PosSemidef at hd hl hh ho hi
  simp only [re_rowsLin, re_lyapunovResidual, re_rowsOne, re_rowsGram,
    re_rowsCongr] at hd hl hh ho hi
  refine ⟨hα, hlo, hlh, hγ, hβ, ?_, ?_, ?_, ?_, ?_, trace_toSystem G c.P⟩
  · convert hd using 1
    simp only [RatLTI.toSystem, Rat.cast_one, one_smul, Rat.cast_mul, Rat.cast_ofNat]; abel
  · simpa using hl
  · simpa using hh
  · simpa [RatLTI.toSystem] using ho
  · simpa [RatLTI.toSystem] using hi

end DecayCert

/-! ### Exact Gramian energy certificates -/

/-- The rows of `-(Aᵀ W + W A) - Cᵀ C = -(Aᵀ W + W A + Cᵀ C)`, recomputed from the model. -/
@[expose] def gramianResidual {n m p : ℕ} (G : RatLTI n m p) (W : List (List ℚ)) :
    List (List ℚ) :=
  rowsLin n 1 1 (lyapunovResidual n G.A W) (rowsGram n p G.C)

private theorem re_gramianResidual {n m p : ℕ} (G : RatLTI n m p) (W : List (List ℚ)) :
    re (ofLists n n (gramianResidual G W)) = -(G.toSystem.Aᵀ * re (ofLists n n W) +
      re (ofLists n n W) * G.toSystem.A + G.toSystem.Cᵀ * G.toSystem.C) := by
  rw [gramianResidual, re_rowsLin, re_lyapunovResidual, re_rowsGram]
  simp only [Rat.cast_one, one_smul, RatLTI.toSystem]; abel

/-- An exact energy certificate for a `RatLTI n m p` model: a Lyapunov certificate (`P` and its
witnesses) proving exponential stability, a symmetric-or-not `W` with
`Aᵀ W + W A + Cᵀ C = 0` exactly, and the claimed energy `tr (Bᵀ W B)`. `W` need not be positive
definite, so singular Gramians of unobservable models are accepted. -/
structure EnergyCert where
  /-- The rows of the Lyapunov matrix `P` that proves stability. -/
  P : List (List ℚ)
  /-- The witnesses for `P ≻ 0` and `-(Aᵀ P + P A) ≻ 0`. -/
  stable : LyapunovCert
  /-- The rows of the Gramian `W`. -/
  W : List (List ℚ)
  /-- The claimed impulse-response energy `tr (Bᵀ W B)`. -/
  energy : ℚ

namespace EnergyCert

variable {n m p : ℕ} (c : EnergyCert) (G : RatLTI n m p)

/-- Whether `c` is an exact energy certificate for `G`: `G` is well formed without direct
feedthrough, the Lyapunov certificate is accepted, `W` is `n × n`, the recomputed residual
`Aᵀ W + W A + Cᵀ C` is exactly `0`, and `tr (Bᵀ W B)` is exactly `c.energy`. -/
@[expose] def check : Bool :=
  G.check && c.stable.check n G.A c.P && isShape n n c.W && allZero (gramianResidual G c.W) &&
    rowsTrace m (rowsCongr n m G.B c.W) == c.energy

variable {c G}

/-- An accepted exact energy certificate proves exponential stability of `ẋ = A x`. -/
theorem isExponentiallyStable (h : c.check G = true) :
    (toEuclideanCLM (𝕜 := ℝ) G.toSystem.A).IsExponentiallyStable := by
  simp only [check, Bool.and_eq_true] at h
  exact LyapunovCert.isExponentiallyStable_of_check h.1.1.1.2

/-- **Exact impulse-response energy.** If the kernel accepts `c` for `G`, the squared Frobenius
norm of the impulse response is integrable on `(0, ∞)` and `∫₀^∞ ‖h t‖_F² dt = c.energy`. The
model has no direct feedthrough (`RatLTI.toSystem_D`), so `h` is its whole impulse response. -/
theorem integrableOn_Ioi_and_integral_eq (h : c.check G = true) :
    IntegrableOn (fun t => ∑ i, ∑ j, G.toSystem.responseKernel t i j ^ 2) (Ioi 0) ∧
      ∫ t in Ioi 0, ∑ i, ∑ j, G.toSystem.responseKernel t i j ^ 2 = c.energy := by
  have hA := isExponentiallyStable h
  simp only [check, Bool.and_eq_true, beq_iff_eq] at h
  have hR := congrArg re (ofLists_eq_zero_of_allZero (k := n) (l := n) h.1.2)
  rw [re_gramianResidual, show re (0 : Matrix (Fin n) (Fin n) ℚ) = 0 from Matrix.map_zero _
    Rat.cast_zero, neg_eq_zero] at hR
  have := LTISystem.integrableOn_Ioi_and_integral_frobeniusSq_eq hR hA
  rwa [trace_toSystem, h.2] at this

end EnergyCert

/-! ### Energy upper-bound certificates -/

/-- An energy upper-bound certificate for a `RatLTI n m p` model: a matrix `W` with `LDLᵀ`
witnesses for `W ⪰ 0` and `-(Aᵀ W + W A + Cᵀ C) ⪰ 0`, and a claimed bound on `tr (Bᵀ W B)`.
Inexact rational reconstructions of a Gramian are accepted when the inequality holds. -/
structure EnergyBoundCert where
  /-- The rows of `W`. -/
  W : List (List ℚ)
  /-- A witness for `W ⪰ 0`. -/
  posW : LDLCert
  /-- A witness for `-(Aᵀ W + W A + Cᵀ C) ⪰ 0`. -/
  dissipationW : LDLCert
  /-- The claimed bound on the impulse-response energy. -/
  bound : ℚ

namespace EnergyBoundCert

variable {n m p : ℕ} (c : EnergyBoundCert) (G : RatLTI n m p)

/-- Whether `c` is an energy upper-bound certificate for `G`: `G` is well formed without direct
feedthrough, `W ⪰ 0` and the recomputed `-(Aᵀ W + W A + Cᵀ C) ⪰ 0` are accepted, and
`tr (Bᵀ W B) ≤ c.bound`. -/
@[expose] def check : Bool :=
  G.check && c.posW.checkPosSemidef n c.W &&
    c.dissipationW.checkPosSemidef n (gramianResidual G c.W) &&
    decide (rowsTrace m (rowsCongr n m G.B c.W) ≤ c.bound)

variable {c G}

/-- **Certified impulse-response energy bound.** If the kernel accepts `c` for `G`, the squared
Frobenius norm of the impulse response is integrable on `(0, ∞)` and
`∫₀^∞ ‖h t‖_F² dt ≤ c.bound`. This is a certified upper bound, not the optimal one, and it says
nothing about internal stability: unobservable modes may be unstable. -/
theorem integrableOn_Ioi_and_integral_le (h : c.check G = true) :
    IntegrableOn (fun t => ∑ i, ∑ j, G.toSystem.responseKernel t i j ^ 2) (Ioi 0) ∧
      ∫ t in Ioi 0, ∑ i, ∑ j, G.toSystem.responseKernel t i j ^ 2 ≤ c.bound := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨-, hW⟩, hR⟩, hb⟩ := h
  have hR : (re _).PosSemidef := c.dissipationW.posSemidef_of_checkPosSemidef hR
  rw [re_gramianResidual] at hR
  have := LTISystem.integrableOn_Ioi_and_integral_frobeniusSq_le
    (c.posW.posSemidef_of_checkPosSemidef hW) hR
  rw [trace_toSystem] at this
  exact ⟨this.1, this.2.trans (by exact_mod_cast hb)⟩

end EnergyBoundCert

/-! ### Energy lower-bound certificates -/

private theorem re_supply {n m p : ℕ} (G : RatLTI n m p) (Q : List (List ℚ)) :
    re (ofLists n n (rowsLin n 1 1 (rowsGram n p G.C) (lyapunovResidual n G.A Q))) =
      G.toSystem.Aᵀ * re (ofLists n n Q) + re (ofLists n n Q) * G.toSystem.A +
        G.toSystem.Cᵀ * G.toSystem.C := by
  rw [re_rowsLin, re_lyapunovResidual, re_rowsGram]
  simp only [Rat.cast_one, one_smul, RatLTI.toSystem, sub_neg_eq_add]; abel

/-- An energy lower-bound certificate for a `RatLTI n m p` model: a Lyapunov certificate (`P` and
its witnesses) proving exponential stability, a matrix `Q` with an `LDLᵀ` witness for
`Aᵀ Q + Q A + Cᵀ C ⪰ 0`, and a claimed lower bound on `tr (Bᵀ Q B)`. `Q` need not be positive
semidefinite. -/
structure EnergyLowerCert where
  /-- The rows of the Lyapunov matrix `P` that proves stability. -/
  P : List (List ℚ)
  /-- The witnesses for `P ≻ 0` and `-(Aᵀ P + P A) ≻ 0`. -/
  stable : LyapunovCert
  /-- The rows of `Q`. -/
  Q : List (List ℚ)
  /-- A witness for `Aᵀ Q + Q A + Cᵀ C ⪰ 0`. -/
  supplyW : LDLCert
  /-- The claimed lower bound on the impulse-response energy. -/
  bound : ℚ

namespace EnergyLowerCert

variable {n m p : ℕ} (c : EnergyLowerCert) (G : RatLTI n m p)

/-- Whether `c` is an energy lower-bound certificate for `G`: `G` is well formed without direct
feedthrough, the Lyapunov certificate is accepted, the recomputed `Aᵀ Q + Q A + Cᵀ C ⪰ 0` is
accepted, and `c.bound ≤ tr (Bᵀ Q B)`. -/
@[expose] def check : Bool :=
  G.check && c.stable.check n G.A c.P &&
    c.supplyW.checkPosSemidef n (rowsLin n 1 1 (rowsGram n p G.C) (lyapunovResidual n G.A c.Q)) &&
    decide (c.bound ≤ rowsTrace m (rowsCongr n m G.B c.Q))

variable {c G}

/-- **Certified impulse-response energy lower bound.** If the kernel accepts `c` for `G`, the
squared Frobenius norm of the impulse response is integrable on `(0, ∞)` and
`c.bound ≤ ∫₀^∞ ‖h t‖_F² dt`. The proof is `Q ⪯ W` for the observability Gramian `W`, since
`W - Q = ∫₀^∞ exp (t Aᵀ) (Aᵀ Q + Q A + Cᵀ C) exp (t A) dt`; it uses the stability of `A`. -/
theorem integrableOn_Ioi_and_le_integral (h : c.check G = true) :
    IntegrableOn (fun t => ∑ i, ∑ j, G.toSystem.responseKernel t i j ^ 2) (Ioi 0) ∧
      c.bound ≤ ∫ t in Ioi 0, ∑ i, ∑ j, G.toSystem.responseKernel t i j ^ 2 := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨-, hs⟩, hR⟩, hb⟩ := h
  have hR : (re _).PosSemidef := c.supplyW.posSemidef_of_checkPosSemidef hR
  rw [re_supply] at hR
  have := LTISystem.integrableOn_Ioi_and_le_integral_frobeniusSq hR
    (LyapunovCert.isExponentiallyStable_of_check hs)
  rw [trace_toSystem] at this
  exact ⟨this.1, (by exact_mod_cast hb : (c.bound : ℝ) ≤ _).trans this.2⟩

/-- **Certified energy enclosure.** If the kernel accepts a lower-bound certificate `c` and an
upper-bound certificate `d` for `G`, the impulse-response energy is finite and lies in the
interval `[c.bound, d.bound]`: `c.bound ≤ ∫₀^∞ ‖h t‖_F² dt ≤ d.bound`. -/
theorem integrableOn_Ioi_and_integral_mem_Icc (h : c.check G = true) {d : EnergyBoundCert}
    (hd : d.check G = true) :
    IntegrableOn (fun t => ∑ i, ∑ j, G.toSystem.responseKernel t i j ^ 2) (Ioi 0) ∧
      ∫ t in Ioi 0, ∑ i, ∑ j, G.toSystem.responseKernel t i j ^ 2 ∈
        Icc (c.bound : ℝ) d.bound :=
  ⟨(integrableOn_Ioi_and_le_integral h).1, (integrableOn_Ioi_and_le_integral h).2,
    (EnergyBoundCert.integrableOn_Ioi_and_integral_le hd).2⟩

end EnergyLowerCert

end Cslib.LinearAlgebra
