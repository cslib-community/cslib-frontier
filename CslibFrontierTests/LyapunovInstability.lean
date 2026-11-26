/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.LinearAlgebra.LyapunovCertificate
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

/-! # Tests for kernel-checked instability certificates

* A negative-resistance oscillator `A = !![0, 1; -1, 1/2]`, with eigenvalues `1/4 ± i √15/4`. The
  certificate has rate `ε = 1/8`, the negative definite `P = !![-67, 16; 16, -63]` and residual
  `-((A - ε • 1)ᵀ P + P (A - ε • 1)) = (61/4) • 1`. Acceptance (`decide +kernel`) gives
  instability, an unbounded trajectory, the growth bound and an eigenvalue with `re μ ≥ 1/8`.
* A saddle `A = !![0, 1; 1, 0]` (eigenvalues `±1`) with the indefinite `P = !![0, -1; -1, 0]`,
  the sharp rate `ε = 1` and a singular residual witness (`d = (2, 0)`).
* Corrupted certificates are rejected.
* Bracketing: the instability certificate at rate `1/8` and a stability certificate for
  `A - (3/8) • 1` give `1/8 ≤ α(A) < 3/8` for the oscillator.
* A negative rate: for the stable `!![0, 1; -2, -3]`, rate `-1` with `P = -ℓ ℓᵀ` certifies that
  some trajectory decays no faster than `exp (-t)`, a lower bound on settling.
* The ideal LC matrix `!![0, 1; -1, 0]`: a rate-`0` certificate with `P = -1` refutes asymptotic
  stability, the matrix is Lyapunov stable (`P = 1`), and every accepted certificate has rate
  `≤ 0`, because its eigenvalues `±i` lie on the imaginary axis.
* The double integrator `!![0, 1; 0, 0]`: it has the unbounded trajectory `(t, 1)`, but every
  accepted certificate has rate `≤ 0`, since its only eigenvalue is `0`. The certificate does not
  decide the boundary `α(A) = 0`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.LyapunovInstability

open Set Filter Topology Matrix Mathlib.Tactic.Matrix Cslib.LinearAlgebra

/-! ### An unstable oscillator -/

/-- A negative-resistance oscillator: eigenvalues `1/4 ± i √15/4`. -/
def Aosc : List (List ℚ) := [[0, 1], [-1, (1/2 : ℚ)]]

/-- A negative definite `P` with `(A - (1/8) • 1)ᵀ P + P (A - (1/8) • 1) = -(61/4) • 1`. -/
def Posc : List (List ℚ) := [[-67, 16], [16, -63]]

/-- Rate `1/8`, initial state `(1, 0)` of energy `-67`, residual witness `L = 1`,
`d = (61/4, 61/4)`. -/
def certOsc : InstabilityCert := ⟨(1/8 : ℚ), [1, 0], ⟨[[1], [0, 1]], [(61/4 : ℚ), (61/4 : ℚ)]⟩⟩

theorem certOsc_ok : certOsc.check 2 Aosc Posc = true := by decide +kernel

/-- The recomputed shifted residual is `(61/4) • 1`. -/
example : lyapunovResidual 2 (shiftRows 2 (1/8) Aosc) Posc =
    [[(61/4 : ℚ), 0], [0, (61/4 : ℚ)]] := by decide +kernel

example : ¬(toEuclideanCLM (𝕜 := ℝ) ((ofLists 2 2 Aosc).map ((↑) : ℚ → ℝ))).IsLyapunovStable :=
  InstabilityCert.not_isLyapunovStable_of_check certOsc_ok (by decide +kernel)

example : Tendsto (fun t : ℝ => ‖WithLp.toLp 2 (NormedSpace.exp
    (t • (ofLists 2 2 Aosc).map ((↑) : ℚ → ℝ)) *ᵥ (fun i => ((ofList 2 certOsc.x₀ i : ℚ) : ℝ)))‖)
    atTop atTop :=
  InstabilityCert.tendsto_norm_of_check certOsc_ok (by decide +kernel)

/-- The spectral consequence: an eigenvalue with real part at least `1/8`. -/
example : ∃ μ ∈ spectrum ℂ (((ofLists 2 2 Aosc).map ((↑) : ℚ → ℝ)).map (algebraMap ℝ ℂ)),
    (1/8 : ℝ) ≤ μ.re := by
  simpa [certOsc] using InstabilityCert.exists_mem_spectrum_le_re_of_check certOsc_ok

/-- Rejections: a zero initial state has energy `0`; a wrong residual diagonal; the same
witness at another rate, whose residual differs. -/
example : (⟨(1/8 : ℚ), [0, 0], certOsc.Q⟩ : InstabilityCert).check 2 Aosc Posc = false := by
  decide +kernel

example : (⟨(1/8 : ℚ), [1, 0], ⟨[[1], [0, 1]], [15, 15]⟩⟩ : InstabilityCert).check 2 Aosc Posc =
    false := by decide +kernel

example : (⟨(-1/8 : ℚ), [1, 0], certOsc.Q⟩ : InstabilityCert).check 2 Aosc Posc = false := by
  decide +kernel

/-- The stability checker rejects the same matrices, whatever the witnesses. -/
example : (⟨certOsc.Q, certOsc.Q⟩ : LyapunovCert).check 2 Aosc Posc = false := by decide +kernel

/-! ### A saddle, with an indefinite `P` and a singular witness -/

def Asad : List (List ℚ) := [[0, 1], [1, 0]]

def Psad : List (List ℚ) := [[0, -1], [-1, 0]]

/-- Rate `1`, the eigenvalue itself; the residual `!![2, -2; -2, 2]` is singular. -/
def certSad : InstabilityCert := ⟨1, [1, 1], ⟨[[1], [-1, 1]], [2, 0]⟩⟩

theorem certSad_ok : certSad.check 2 Asad Psad = true := by decide +kernel

example : ¬(toEuclideanCLM (𝕜 := ℝ) ((ofLists 2 2 Asad).map ((↑) : ℚ → ℝ))).IsLyapunovStable :=
  InstabilityCert.not_isLyapunovStable_of_check certSad_ok (by decide +kernel)

/-- Rate `2` exceeds the eigenvalue `1`: the residual `2 • 1 - 4 • A` is indefinite and the
witness is rejected. -/
example : (⟨2, [1, 1], certSad.Q⟩ : InstabilityCert).check 2 Asad Psad = false := by
  decide +kernel

/-! ### Bracketing the spectral abscissa

The oscillator has `α(A) = 1/4`. The instability certificate above gives `α(A) ≥ 1/8`, and a
stability certificate for `A - (3/8) • 1` (`P = !![63, -16; -16, 67]`, residual `(61/4) • 1`)
gives `α(A) < 3/8`. -/

def certOscStab : LyapunovCert :=
  ⟨⟨[[1], [(-16/63 : ℚ), 1]], [63, (3965/63 : ℚ)]⟩, ⟨[[1], [0, 1]], [(61/4 : ℚ), (61/4 : ℚ)]⟩⟩

theorem certOscStab_ok : certOscStab.check 2 (shiftRows 2 (3/8) Aosc) [[63, -16], [-16, 67]] =
    true := by decide +kernel

theorem bracket_osc :
    (∃ μ ∈ spectrum ℂ (((ofLists 2 2 Aosc).map ((↑) : ℚ → ℝ)).map (algebraMap ℝ ℂ)),
      (1/8 : ℝ) ≤ μ.re) ∧
    ∀ μ ∈ spectrum ℂ (((ofLists 2 2 Aosc).map ((↑) : ℚ → ℝ)).map (algebraMap ℝ ℂ)),
      μ.re < 3/8 := by
  refine ⟨by simpa [certOsc] using InstabilityCert.exists_mem_spectrum_le_re_of_check certOsc_ok,
    fun μ hμ => ?_⟩
  simpa using LyapunovCert.re_lt_of_check_shiftRows certOscStab_ok μ hμ

/-! ### A negative rate: slow decay of a stable system

`A = !![0, 1; -2, -3]` (eigenvalues `-1`, `-2`) is the stable example of #8320. With the left
eigenvector `ℓ = (2, 1)` of `-1` and `P = -ℓ ℓᵀ`, `Aᵀ P + P A = -2 P`, so the residual at rate
`-1` vanishes: some trajectory decays no faster than `exp (-t)`, and `-1 ≤ α(A)`. -/

def Astab : List (List ℚ) := [[0, 1], [-2, -3]]

def Pslow : List (List ℚ) := [[-4, -2], [-2, -1]]

def certSlow : InstabilityCert := ⟨-1, [1, 0], ⟨[[1], [0, 1]], [0, 0]⟩⟩

theorem certSlow_ok : certSlow.check 2 Astab Pslow = true := by decide +kernel

/-- The squared state from `x₀ = (1, 0)` stays above `r` at every time `t ≥ 0` with
`‖P‖ r < 4 exp (-2 t)`. -/
example {r t : ℝ} (ht : 0 ≤ t)
    (hr : ‖toEuclideanCLM (𝕜 := ℝ) ((ofLists 2 2 Pslow).map ((↑) : ℚ → ℝ))‖ * r <
      4 * Real.exp (-2 * t)) :
    r < NormedSpace.exp (t • (ofLists 2 2 Astab).map ((↑) : ℚ → ℝ)) *ᵥ
        (fun i => ((ofList 2 certSlow.x₀ i : ℚ) : ℝ)) ⬝ᵥ
      NormedSpace.exp (t • (ofLists 2 2 Astab).map ((↑) : ℚ → ℝ)) *ᵥ
        (fun i => ((ofList 2 certSlow.x₀ i : ℚ) : ℝ)) := by
  refine InstabilityCert.lt_dotProduct_self_of_check certSlow_ok ht (hr.trans_le (le_of_eq ?_))
  simp [certSlow, Pslow, ofLists_apply, ofList_apply, dotProduct, mulVec, Fin.sum_univ_two]
  ring

example : ∃ μ ∈ spectrum ℂ (((ofLists 2 2 Astab).map ((↑) : ℚ → ℝ)).map (algebraMap ℝ ℂ)),
    (-1 : ℝ) ≤ μ.re := by
  simpa [certSlow] using InstabilityCert.exists_mem_spectrum_le_re_of_check certSlow_ok

/-! ### Systems on the boundary `α(A) = 0` -/

/-- An eigenvalue `μ` with `μ ^ k = a` for the scalar `a`, whenever `M ^ k = algebraMap a`. -/
private theorem pow_eq_of_mem_spectrum {M : Matrix (Fin 2) (Fin 2) ℂ} {k : ℕ} {a : ℂ}
    (hM : M ^ k = algebraMap ℂ _ a) {μ : ℂ} (hμ : μ ∈ spectrum ℂ M) : μ ^ k = a := by
  have h := spectrum.pow_mem_pow M k hμ
  rwa [hM, spectrum.scalar_eq, Set.mem_singleton_iff] at h

/-- An accepted certificate for a rational `2 × 2` matrix whose eigenvalues all have real part
`0` has rate `≤ 0`. -/
private theorem rate_nonpos {A P : List (List ℚ)} {c : InstabilityCert}
    (h : c.check 2 A P = true)
    (hre : ∀ μ ∈ spectrum ℂ (((ofLists 2 2 A).map ((↑) : ℚ → ℝ)).map (algebraMap ℝ ℂ)),
      μ.re = 0) : c.rate ≤ 0 := by
  obtain ⟨μ, hμ, hle⟩ := InstabilityCert.exists_mem_spectrum_le_re_of_check h
  rw [hre μ hμ] at hle
  exact_mod_cast hle

/-- The ideal LC matrix. -/
def ALC : List (List ℚ) := [[0, 1], [-1, 0]]

theorem map_ALC : ((ofLists 2 2 ALC).map ((↑) : ℚ → ℝ)) = !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ALC, ofLists_apply, ofList_apply]

/-- Rate `0` with `P = -1`: the residual `Aᵀ + A` vanishes. -/
def certLC : InstabilityCert := ⟨0, [1, 0], ⟨[[1], [0, 1]], [0, 0]⟩⟩

theorem certLC_ok : certLC.check 2 ALC [[-1, 0], [0, -1]] = true := by decide +kernel

/-- The LC matrix is not asymptotically stable. -/
example :
    ¬(toEuclideanCLM (𝕜 := ℝ) ((ofLists 2 2 ALC).map ((↑) : ℚ → ℝ))).IsAsymptoticallyStable :=
  InstabilityCert.not_isAsymptoticallyStable_of_check certLC_ok le_rfl

/-- The LC matrix is Lyapunov stable: `P = 1` and `-(Aᵀ + A) = 0`. -/
theorem isLyapunovStable_LC :
    (toEuclideanCLM (𝕜 := ℝ) ((ofLists 2 2 ALC).map ((↑) : ℚ → ℝ))).IsLyapunovStable := by
  refine isLyapunovStable_toEuclideanCLM_of_posDef_of_posSemidef PosDef.one ?_
  have hT : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = !![0, -1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  convert PosSemidef.zero using 1
  rw [map_ALC, hT, mul_one, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **No instability certificate for the LC matrix.** Every accepted certificate has rate `≤ 0`:
the eigenvalues satisfy `μ ^ 2 = -1`, so `re μ = 0`. -/
theorem rate_nonpos_of_check_LC {c : InstabilityCert} {P : List (List ℚ)}
    (h : c.check 2 ALC P = true) : c.rate ≤ 0 := by
  refine rate_nonpos h fun μ hμ => ?_
  have hM : (((ofLists 2 2 ALC).map ((↑) : ℚ → ℝ)).map (algebraMap ℝ ℂ)) ^ 2 =
      algebraMap ℂ _ (-1) := by
    rw [map_ALC, algebraMap_eq_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]
  have h2 := pow_eq_of_mem_spectrum hM hμ
  have hre := congrArg Complex.re h2
  have him := congrArg Complex.im h2
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.one_re, Complex.one_im, neg_zero] at hre him
  rcases mul_eq_zero.1 (show μ.re * μ.im = 0 by linarith) with h | h
  · exact h
  · nlinarith

/-- The double integrator. -/
def ADI : List (List ℚ) := [[0, 1], [0, 0]]

theorem map_ADI : ((ofLists 2 2 ADI).map ((↑) : ℚ → ℝ)) = !![0, 1; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ADI, ofLists_apply, ofList_apply]

/-- **The double integrator is unstable**: `(t, 1)` is a trajectory, and it is unbounded. -/
theorem exists_unbounded_DI : ∃ x : ℝ → EuclideanSpace ℝ (Fin 2),
    (toEuclideanCLM (𝕜 := ℝ) ((ofLists 2 2 ADI).map ((↑) : ℚ → ℝ))).IsTrajectoryOn x (Ici 0) ∧
      Tendsto (fun t => ‖x t‖) atTop atTop := by
  refine ⟨fun t => WithLp.toLp 2 ![t, 1], ?_, ?_⟩
  · rw [isTrajectoryOn_toEuclideanCLM_iff, map_ADI]
    intro t _
    refine (hasDerivAt_pi.2 fun i => ?_).hasDerivWithinAt
    fin_cases i
    · convert hasDerivAt_id' t using 1
      · rfl
      · change (!![0, 1; 0, 0] *ᵥ ![t, 1]) 0 = 1
        simp [mulVec, dotProduct, Fin.sum_univ_two]
    · convert hasDerivAt_const t (1 : ℝ) using 1
      · rfl
      · change (!![0, 1; 0, 0] *ᵥ ![t, 1]) 1 = 0
        simp [mulVec, dotProduct, Fin.sum_univ_two]
  · refine tendsto_atTop_mono (fun t => ?_) tendsto_id
    have := PiLp.norm_apply_le (WithLp.toLp 2 ![t, (1 : ℝ)]) 0
    simp only [Matrix.cons_val_zero, Real.norm_eq_abs] at this
    exact (le_abs_self t).trans this

/-- **No instability certificate for the double integrator.** Every accepted certificate has rate
`≤ 0`: the matrix is nilpotent, so its only eigenvalue is `0`. -/
theorem rate_nonpos_of_check_DI {c : InstabilityCert} {P : List (List ℚ)}
    (h : c.check 2 ADI P = true) : c.rate ≤ 0 := by
  refine rate_nonpos h fun μ hμ => ?_
  have hM : (((ofLists 2 2 ADI).map ((↑) : ℚ → ℝ)).map (algebraMap ℝ ℂ)) ^ 2 =
      algebraMap ℂ _ 0 := by
    rw [map_ADI, algebraMap_eq_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]
  simp [pow_eq_zero_iff two_ne_zero |>.1 (pow_eq_of_mem_spectrum hM hμ)]

end CslibFrontierTests.LyapunovInstability
