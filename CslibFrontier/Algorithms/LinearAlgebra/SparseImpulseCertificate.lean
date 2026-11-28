/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.LinearAlgebra.ImpulseCertificate
public import CslibFrontier.Algorithms.LinearAlgebra.SparseLyapunovCertificate
import Mathlib.Data.List.GetD
import Mathlib.LinearAlgebra.Matrix.Integer

/-!
# Sparse decay and energy certificates for LTI impulse responses

The certificates of `CslibFrontier.Algorithms.LinearAlgebra.ImpulseCertificate` check every
residual with the dense `LDLᵀ` checker, on residuals computed with dense products, at a cost of
order `n³` whatever the sparsity. This module gives them sparse counterparts: the model, the
certificate matrices and the residuals are sparse rows (`Cslib.LinearAlgebra.ofSparse`), the
products are `Cslib.LinearAlgebra.sparseMul` and `Cslib.LinearAlgebra.sparseResidual`, and every
semidefiniteness claim is checked by the envelope checker `Cslib.LinearAlgebra.EnvLDLCert`. Their
soundness theorems state the same real facts as the dense ones, with `ofSparse` in place of
`ofLists`, so the bounds proved there apply unchanged.

* `Cslib.LinearAlgebra.SparseRatLTI`: a rational model without direct feedthrough by sparse
  rows, with the rows of `Aᵀ`, `Bᵀ` and `Cᵀ`, which `SparseRatLTI.check` verifies.
* `Cslib.LinearAlgebra.SparseDecayCert`: the five inequalities of `DecayCert`. Acceptance proves
  `Cslib.LinearAlgebra.DecayInequalities`, hence stability, the state, output and
  impulse-response envelopes, settling and the energy tails.
* `Cslib.LinearAlgebra.SparseEnergyBoundCert`: `W ⪰ 0` and `Aᵀ W + W A + Cᵀ C ⪯ 0`. Acceptance
  proves `∫₀^∞ ‖h t‖_F² ≤ bound`.
* `Cslib.LinearAlgebra.SparseEnergyLowerCert`: a sparse Lyapunov certificate for `A` and a `Q`
  with `Aᵀ Q + Q A + Cᵀ C ⪰ 0`. Acceptance proves `bound ≤ ∫₀^∞ ‖h t‖_F²`, and together with an
  upper-bound certificate the enclosure `∫₀^∞ ‖h t‖_F² ∈ [lower, upper]`.

The exact-energy `EnergyCert` has no sparse counterpart: the observability Gramian is generally
dense even for sparse `A`, while banded `P` and `Q` can enclose the energy.

## Main results

* `Cslib.LinearAlgebra.SparseDecayCert.decayInequalities`.
* `Cslib.LinearAlgebra.SparseEnergyBoundCert.integrableOn_Ioi_and_integral_le`.
* `Cslib.LinearAlgebra.SparseEnergyLowerCert.integrableOn_Ioi_and_le_integral`,
  `Cslib.LinearAlgebra.SparseEnergyLowerCert.integrableOn_Ioi_and_integral_mem_Icc`.
-/

public section

open Set Matrix MeasureTheory

namespace Cslib.LinearAlgebra

/-! ### Sparse rows of identities, linear combinations and traces -/

/-- The sparse rows of the `n × n` identity matrix. -/
@[expose] def sparseOne (n : ℕ) : List (List (ℕ × ℚ)) := (List.range n).map fun i => [(i, 1)]

theorem ofSparse_sparseOne (n : ℕ) : ofSparse n n (sparseOne n) = 1 := by
  ext i j
  rw [ofSparse_apply, List.getD_eq_getElem _ _ (by simp [sparseOne]), Matrix.one_apply]
  simp [sparseOne, sparseGet_cons, Fin.val_inj]

/-- The sparse rows of `a • M - b • N`, with repeated columns merged. -/
@[expose] def sparseLin (a b : ℚ) (M N : List (List (ℕ × ℚ))) : List (List (ℕ × ℚ)) :=
  subRows (M.map (sparseScale a)) (N.map (sparseScale b))

theorem ofSparse_sparseLin {k : ℕ} (a b : ℚ) {M N : List (List (ℕ × ℚ))} (hM : M.length = k) :
    ofSparse k k (sparseLin a b M N) = a • ofSparse k k M - b • ofSparse k k N := by
  ext i j
  have hmap : ∀ (c : ℚ) (R : List (List (ℕ × ℚ))),
      (R.map (sparseScale c)).getD i [] = sparseScale c (R.getD i []) :=
    fun _ _ => List.getD_map _ [] _
  rw [ofSparse_apply, sparseLin, sparseGet_subRows _ _ _ _ (by simp [hM]), hmap, hmap,
    sparseGet_sparseScale, sparseGet_sparseScale]
  simp [ofSparse_apply]

/-- The trace `∑ i < k, M i i` of the `k × k` matrix with sparse rows `rows`. -/
@[expose] def sparseTrace (k : ℕ) (rows : List (List (ℕ × ℚ))) : ℚ :=
  ∑ i ∈ Finset.range k, sparseGet (rows.getD i []) i

theorem trace_ofSparse (k : ℕ) (rows : List (List (ℕ × ℚ))) :
    trace (ofSparse k k rows) = sparseTrace k rows := by
  simp [trace, ofSparse_apply, sparseTrace, Finset.sum_range]

/-! ### Sparse rational LTI models -/

/-- A finite-dimensional continuous-time LTI model `ẋ = A x + B u`, `y = C x` without direct
feedthrough, with rational data given by sparse rows: `A` is `n × n`, `B` is `n × m` and `C` is
`p × n`. The model also lists the sparse rows of `Aᵀ`, `Bᵀ` and `Cᵀ`, so that the residuals are
products of rows by rows; `SparseRatLTI.check` verifies them. -/
structure SparseRatLTI (n m p : ℕ) where
  /-- The sparse rows of the state matrix. -/
  A : List (List (ℕ × ℚ))
  /-- The sparse rows of `Aᵀ`. -/
  At : List (List (ℕ × ℚ))
  /-- The sparse rows of the input matrix. -/
  B : List (List (ℕ × ℚ))
  /-- The sparse rows of `Bᵀ`. -/
  Bt : List (List (ℕ × ℚ))
  /-- The sparse rows of the output matrix. -/
  C : List (List (ℕ × ℚ))
  /-- The sparse rows of `Cᵀ`. -/
  Ct : List (List (ℕ × ℚ))

namespace SparseRatLTI

variable {n m p : ℕ} (G : SparseRatLTI n m p)

/-- The real system whose matrices are those of `G`, read over `ℝ`, with `D = 0`. -/
@[expose] noncomputable def toSystem : LTISystem (Fin n) (Fin m) (Fin p) where
  A := (ofSparse n n G.A).map (↑)
  B := (ofSparse n m G.B).map (↑)
  C := (ofSparse p n G.C).map (↑)
  D := 0

/-- Whether `G` is well formed: `A`, `B`, `C` and the listed transposes have exactly the
declared shapes, with strictly increasing columns in every row, and the transposes are those of
`A`, `B` and `C`. -/
@[expose] def check : Bool :=
  isSparseShape n n G.A && isSparseShape n n G.At && isTransposeOf G.A G.At &&
    isSparseShape n m G.B && isSparseShape m n G.Bt && isTransposeOf G.B G.Bt &&
    isSparseShape p n G.C && isSparseShape n p G.Ct && isTransposeOf G.C G.Ct

/-- The sparse rows of `Cᵀ C`. -/
@[expose] def gram : List (List (ℕ × ℚ)) := sparseMul G.Ct G.C

/-- The sparse rows of `Bᵀ P B`. -/
@[expose] def congrB (P : List (List (ℕ × ℚ))) : List (List (ℕ × ℚ)) :=
  sparseMul G.Bt (sparseMul P G.B)

variable {G}

private theorem lengths (h : G.check = true) :
    G.A.length = n ∧ G.At.length = n ∧ isTransposeOf G.A G.At = true ∧ G.B.length = n ∧
      G.Bt.length = m ∧ isTransposeOf G.B G.Bt = true ∧ G.C.length = p ∧ G.Ct.length = n ∧
      isTransposeOf G.C G.Ct = true := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hA, hAt⟩, hTA⟩, hB⟩, hBt⟩, hTB⟩, hC⟩, hCt⟩, hTC⟩ := h
  exact ⟨length_of_isSparseShape hA, length_of_isSparseShape hAt, hTA, length_of_isSparseShape hB,
    length_of_isSparseShape hBt, hTB, length_of_isSparseShape hC, length_of_isSparseShape hCt,
    hTC⟩

private theorem length_gram (h : G.check = true) : G.gram.length = n := by
  rw [gram, length_sparseMul, (lengths h).2.2.2.2.2.2.2.1]

private theorem length_sparseResidual (h : G.check = true) {P : List (List (ℕ × ℚ))}
    (hP : P.length = n) : (sparseResidual G.A G.At P).length = n := by
  simp [sparseResidual, sparseScaledResidual, length_sparseMul, (lengths h).2.1, hP]

/-- The rational sparse residual of `G` and `P` reads as `-(Aᵀ P + P A)` over `ℝ`. -/
private theorem map_ofSparse_sparseResidual (h : G.check = true) {P : List (List (ℕ × ℚ))}
    (hP : P.length = n) :
    (ofSparse n n (sparseResidual G.A G.At P)).map ((↑) : ℚ → ℝ) =
      -(G.toSystem.Aᵀ * (ofSparse n n P).map (↑) + (ofSparse n n P).map (↑) * G.toSystem.A) := by
  obtain ⟨hA, hAt, hT, -⟩ := lengths h
  rw [ofSparse_sparseResidual hA hAt hP hT, Matrix.map_neg _ Rat.cast_neg,
    Matrix.map_add _ Rat.cast_add, Matrix.map_mul_ratCast, Matrix.map_mul_ratCast, transpose_map]
  rfl

private theorem map_ofSparse_gram (h : G.check = true) :
    (ofSparse n n G.gram).map ((↑) : ℚ → ℝ) = G.toSystem.Cᵀ * G.toSystem.C := by
  obtain ⟨-, -, -, -, -, -, hC, -, hT⟩ := lengths h
  rw [gram, ofSparse_sparseMul _ _ hC.le, ofSparse_eq_transpose_of_isTransposeOf hT,
    Matrix.map_mul_ratCast, transpose_map]
  rfl

private theorem map_ofSparse_congrB (h : G.check = true) {P : List (List (ℕ × ℚ))}
    (hP : P.length = n) :
    (ofSparse m m (G.congrB P)).map ((↑) : ℚ → ℝ) =
      G.toSystem.Bᵀ * (ofSparse n n P).map (↑) * G.toSystem.B := by
  obtain ⟨-, -, -, hB, -, hT, -⟩ := lengths h
  rw [congrB, ofSparse_sparseMul (m := n) _ _ (by rw [length_sparseMul, hP]),
    ofSparse_sparseMul _ _ hB.le, ofSparse_eq_transpose_of_isTransposeOf hT,
    Matrix.map_mul_ratCast, Matrix.map_mul_ratCast, transpose_map, Matrix.mul_assoc]
  rfl

/-- `tr (Bᵀ P B)` for the real system of a model is the cast of its rational value. -/
private theorem trace_toSystem (h : G.check = true) {P : List (List (ℕ × ℚ))} (hP : P.length = n) :
    trace (G.toSystem.Bᵀ * (ofSparse n n P).map (↑) * G.toSystem.B) =
      ((sparseTrace m (G.congrB P) : ℚ) : ℝ) := by
  rw [← map_ofSparse_congrB h hP, ← trace_ofSparse]
  simp [trace, Rat.cast_sum]

end SparseRatLTI

/-- The real matrix of `a • M - b • N`, for sparse `M` and `N`. -/
private theorem map_ofSparse_sparseLin {k : ℕ} (a b : ℚ) {M N : List (List (ℕ × ℚ))}
    (hM : M.length = k) :
    (ofSparse k k (sparseLin a b M N)).map ((↑) : ℚ → ℝ) =
      (a : ℝ) • (ofSparse k k M).map (↑) - (b : ℝ) • (ofSparse k k N).map (↑) := by
  rw [ofSparse_sparseLin a b hM]
  ext i j
  simp

private theorem length_sparseOne (k : ℕ) : (sparseOne k).length = k := by
  simp [sparseOne]

private theorem map_ofSparse_sparseOne (k : ℕ) :
    (ofSparse k k (sparseOne k)).map ((↑) : ℚ → ℝ) = 1 := by
  rw [ofSparse_sparseOne]
  exact Matrix.map_one _ Rat.cast_zero Rat.cast_one

/-! ### Sparse decay certificates -/

/-- A sparse certificate for decay of the state and of the impulse response of a
`SparseRatLTI n m p` model: the constants, a matrix `P` (sparse rows) and envelope witnesses for
the five inequalities `Aᵀ P + P A + 2 α P ⪯ 0`, `lo 1 ⪯ P`, `P ⪯ hi 1`, `Cᵀ C ⪯ γ P` and
`Bᵀ P B ⪯ β 1`, as in `Cslib.LinearAlgebra.DecayCert`. Each residual is recomputed from the
model and `P` by the checker. -/
structure SparseDecayCert extends DecayConstants where
  /-- The sparse rows of the Lyapunov matrix `P`. -/
  P : List (List (ℕ × ℚ))
  /-- A witness for `-(Aᵀ P + P A + 2 α P) ⪰ 0`. -/
  decayW : EnvLDLCert
  /-- A witness for `P - lo 1 ⪰ 0`. -/
  loW : EnvLDLCert
  /-- A witness for `hi 1 - P ⪰ 0`. -/
  hiW : EnvLDLCert
  /-- A witness for `γ P - Cᵀ C ⪰ 0`. -/
  outputW : EnvLDLCert
  /-- A witness for `β 1 - Bᵀ P B ⪰ 0`. -/
  inputW : EnvLDLCert

namespace SparseDecayCert

variable {n m p : ℕ} (c : SparseDecayCert) (G : SparseRatLTI n m p)

/-- Whether `c` is a decay certificate for the model `G`: `G` is well formed, `P` is `n × n`,
`α > 0`, `0 < lo ≤ hi`, `γ ≥ 0`, `β ≥ 0`, and the five residuals, recomputed from `G` and `P`,
are accepted as positive semidefinite by the envelope checker. -/
@[expose] def check : Bool :=
  G.check && isSparseShape n n c.P && decide (0 < c.α) && decide (0 < c.lo) &&
    decide (c.lo ≤ c.hi) && decide (0 ≤ c.γ) && decide (0 ≤ c.β) &&
    c.decayW.checkPosSemidef n (sparseLin 1 (2 * c.α) (sparseResidual G.A G.At c.P) c.P) &&
    c.loW.checkPosSemidef n (sparseLin 1 c.lo c.P (sparseOne n)) &&
    c.hiW.checkPosSemidef n (sparseLin c.hi 1 (sparseOne n) c.P) &&
    c.outputW.checkPosSemidef n (sparseLin c.γ 1 c.P G.gram) &&
    c.inputW.checkPosSemidef m (sparseLin c.β 1 (sparseOne m) (G.congrB c.P))

variable {c G}

/-- **Soundness of the sparse decay checker.** If the kernel accepts `c` for `G`, the decay
inequalities hold for the real system of `G` and the real matrix `P`, with `τ = tr (Bᵀ P B)`
computed exactly on sparse rows. This is the statement of `DecayCert.decayInequalities` with
`ofSparse` in place of `ofLists`; the bounds follow from `DecayInequalities`. -/
theorem decayInequalities (h : c.check G = true) :
    DecayInequalities G.toSystem ((ofSparse n n c.P).map ((↑) : ℚ → ℝ)) c.toDecayConstants
      (sparseTrace m (G.congrB c.P)) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hG, hP⟩, hα⟩, hlo⟩, hlh⟩, hγ⟩, hβ⟩, hd⟩, hl⟩, hh⟩, ho⟩, hi⟩ := h
  have hPl := length_of_isSparseShape hP
  have hRl := SparseRatLTI.length_sparseResidual hG hPl
  have hd := c.decayW.posSemidef_of_checkPosSemidef hd
  have hl := c.loW.posSemidef_of_checkPosSemidef hl
  have hh := c.hiW.posSemidef_of_checkPosSemidef hh
  have ho := c.outputW.posSemidef_of_checkPosSemidef ho
  have hi := c.inputW.posSemidef_of_checkPosSemidef hi
  rw [map_ofSparse_sparseLin _ _ hRl, SparseRatLTI.map_ofSparse_sparseResidual hG hPl] at hd
  rw [map_ofSparse_sparseLin _ _ hPl, map_ofSparse_sparseOne] at hl
  rw [map_ofSparse_sparseLin _ _ (length_sparseOne n),
    map_ofSparse_sparseOne] at hh
  rw [map_ofSparse_sparseLin _ _ hPl, SparseRatLTI.map_ofSparse_gram hG] at ho
  rw [map_ofSparse_sparseLin _ _ (length_sparseOne m), map_ofSparse_sparseOne,
    SparseRatLTI.map_ofSparse_congrB hG hPl] at hi
  refine ⟨hα, hlo, hlh, hγ, hβ, ?_, ?_, ?_, ?_, ?_, SparseRatLTI.trace_toSystem hG hPl⟩
  · convert hd using 1
    simp only [Rat.cast_one, one_smul, Rat.cast_mul, Rat.cast_ofNat]; abel
  · simpa using hl
  · simpa using hh
  · simpa using ho
  · simpa using hi

end SparseDecayCert

/-! ### Sparse energy bounds -/

/-- A sparse energy upper-bound certificate for a `SparseRatLTI n m p` model: a matrix `W`
(sparse rows) with envelope witnesses for `W ⪰ 0` and `-(Aᵀ W + W A + Cᵀ C) ⪰ 0`, and a claimed
bound on `tr (Bᵀ W B)`, as in `Cslib.LinearAlgebra.EnergyBoundCert`. -/
structure SparseEnergyBoundCert where
  /-- The sparse rows of `W`. -/
  W : List (List (ℕ × ℚ))
  /-- A witness for `W ⪰ 0`. -/
  posW : EnvLDLCert
  /-- A witness for `-(Aᵀ W + W A + Cᵀ C) ⪰ 0`. -/
  dissipationW : EnvLDLCert
  /-- The claimed bound on the impulse-response energy. -/
  bound : ℚ

namespace SparseEnergyBoundCert

variable {n m p : ℕ} (c : SparseEnergyBoundCert) (G : SparseRatLTI n m p)

/-- Whether `c` is an energy upper-bound certificate for `G`: `G` is well formed, `W` is
`n × n`, `W ⪰ 0` and the recomputed `-(Aᵀ W + W A + Cᵀ C) ⪰ 0` are accepted by the envelope
checker, and `tr (Bᵀ W B) ≤ c.bound`. -/
@[expose] def check : Bool :=
  G.check && isSparseShape n n c.W && c.posW.checkPosSemidef n c.W &&
    c.dissipationW.checkPosSemidef n (sparseLin 1 1 (sparseResidual G.A G.At c.W) G.gram) &&
    decide (sparseTrace m (G.congrB c.W) ≤ c.bound)

variable {c G}

/-- **Certified impulse-response energy bound.** If the kernel accepts `c` for `G`, the squared
Frobenius norm of the impulse response is integrable on `(0, ∞)` and
`∫₀^∞ ‖h t‖_F² dt ≤ c.bound`. This is the statement of
`EnergyBoundCert.integrableOn_Ioi_and_integral_le` for the sparse model. It says nothing about
internal stability. -/
theorem integrableOn_Ioi_and_integral_le (h : c.check G = true) :
    IntegrableOn (fun t => ∑ i, ∑ j, G.toSystem.responseKernel t i j ^ 2) (Ioi 0) ∧
      ∫ t in Ioi 0, ∑ i, ∑ j, G.toSystem.responseKernel t i j ^ 2 ≤ c.bound := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hG, hWs⟩, hW⟩, hR⟩, hb⟩ := h
  have hWl := length_of_isSparseShape hWs
  have hRl := SparseRatLTI.length_sparseResidual hG hWl
  have hR := c.dissipationW.posSemidef_of_checkPosSemidef hR
  rw [map_ofSparse_sparseLin _ _ hRl, SparseRatLTI.map_ofSparse_sparseResidual hG hWl,
    SparseRatLTI.map_ofSparse_gram hG] at hR
  have hR : (-(G.toSystem.Aᵀ * (ofSparse n n c.W).map ((↑) : ℚ → ℝ) +
      (ofSparse n n c.W).map ((↑) : ℚ → ℝ) *
      G.toSystem.A + G.toSystem.Cᵀ * G.toSystem.C)).PosSemidef := by
    convert hR using 1
    simp only [Rat.cast_one, one_smul]; abel
  have := LTISystem.integrableOn_Ioi_and_integral_frobeniusSq_le
    (c.posW.posSemidef_of_checkPosSemidef hW) hR
  rw [SparseRatLTI.trace_toSystem hG hWl] at this
  exact ⟨this.1, this.2.trans (by exact_mod_cast hb)⟩

end SparseEnergyBoundCert

/-- A sparse energy lower-bound certificate for a `SparseRatLTI n m p` model: a sparse Lyapunov
certificate (`P` and its witnesses) proving exponential stability, a matrix `Q` (sparse rows)
with an envelope witness for `Aᵀ Q + Q A + Cᵀ C ⪰ 0`, and a claimed lower bound on
`tr (Bᵀ Q B)`, as in `Cslib.LinearAlgebra.EnergyLowerCert`. `Q` need not be positive
semidefinite. -/
structure SparseEnergyLowerCert where
  /-- The sparse rows of the Lyapunov matrix `P` that proves stability. -/
  P : List (List (ℕ × ℚ))
  /-- The witnesses for `P ≻ 0` and `-(Aᵀ P + P A) ≻ 0`. -/
  stable : SparseLyapunovCert
  /-- The sparse rows of `Q`. -/
  Q : List (List (ℕ × ℚ))
  /-- A witness for `Aᵀ Q + Q A + Cᵀ C ⪰ 0`. -/
  supplyW : EnvLDLCert
  /-- The claimed lower bound on the impulse-response energy. -/
  bound : ℚ

namespace SparseEnergyLowerCert

variable {n m p : ℕ} (c : SparseEnergyLowerCert) (G : SparseRatLTI n m p)

/-- Whether `c` is an energy lower-bound certificate for `G`: `G` is well formed, the sparse
Lyapunov certificate is accepted for `A` and `P`, `Q` is `n × n`, the recomputed
`Aᵀ Q + Q A + Cᵀ C ⪰ 0` is accepted by the envelope checker, and `c.bound ≤ tr (Bᵀ Q B)`. -/
@[expose] def check : Bool :=
  G.check && c.stable.check n G.A c.P && isSparseShape n n c.Q &&
    c.supplyW.checkPosSemidef n (sparseLin 1 1 G.gram (sparseResidual G.A G.At c.Q)) &&
    decide (c.bound ≤ sparseTrace m (G.congrB c.Q))

variable {c G}

/-- **Certified impulse-response energy lower bound.** If the kernel accepts `c` for `G`, the
squared Frobenius norm of the impulse response is integrable on `(0, ∞)` and
`c.bound ≤ ∫₀^∞ ‖h t‖_F² dt`. This is the statement of
`EnergyLowerCert.integrableOn_Ioi_and_le_integral` for the sparse model. -/
theorem integrableOn_Ioi_and_le_integral (h : c.check G = true) :
    IntegrableOn (fun t => ∑ i, ∑ j, G.toSystem.responseKernel t i j ^ 2) (Ioi 0) ∧
      c.bound ≤ ∫ t in Ioi 0, ∑ i, ∑ j, G.toSystem.responseKernel t i j ^ 2 := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hG, hs⟩, hQs⟩, hR⟩, hb⟩ := h
  have hQl := length_of_isSparseShape hQs
  have hR := c.supplyW.posSemidef_of_checkPosSemidef hR
  rw [map_ofSparse_sparseLin _ _ (SparseRatLTI.length_gram hG), SparseRatLTI.map_ofSparse_gram hG,
    SparseRatLTI.map_ofSparse_sparseResidual hG hQl] at hR
  have hR : (G.toSystem.Aᵀ * (ofSparse n n c.Q).map ((↑) : ℚ → ℝ) +
      (ofSparse n n c.Q).map ((↑) : ℚ → ℝ) *
      G.toSystem.A + G.toSystem.Cᵀ * G.toSystem.C).PosSemidef := by
    convert hR using 1
    simp only [Rat.cast_one, one_smul, sub_neg_eq_add]; abel
  have := LTISystem.integrableOn_Ioi_and_le_integral_frobeniusSq hR
    (SparseLyapunovCert.isExponentiallyStable_of_check hs)
  rw [SparseRatLTI.trace_toSystem hG hQl] at this
  exact ⟨this.1, (by exact_mod_cast hb : (c.bound : ℝ) ≤ _).trans this.2⟩

/-- **Certified energy enclosure.** If the kernel accepts a sparse lower-bound certificate `c`
and a sparse upper-bound certificate `d` for `G`, the impulse-response energy is finite and lies
in the interval `[c.bound, d.bound]`. -/
theorem integrableOn_Ioi_and_integral_mem_Icc (h : c.check G = true)
    {d : SparseEnergyBoundCert} (hd : d.check G = true) :
    IntegrableOn (fun t => ∑ i, ∑ j, G.toSystem.responseKernel t i j ^ 2) (Ioi 0) ∧
      ∫ t in Ioi 0, ∑ i, ∑ j, G.toSystem.responseKernel t i j ^ 2 ∈
        Icc (c.bound : ℝ) d.bound :=
  ⟨(integrableOn_Ioi_and_le_integral h).1, (integrableOn_Ioi_and_le_integral h).2,
    (SparseEnergyBoundCert.integrableOn_Ioi_and_integral_le hd).2⟩

end SparseEnergyLowerCert

end Cslib.LinearAlgebra
