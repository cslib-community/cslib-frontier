/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.LinearAlgebra.ImpulseCertificate
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.IntervalSign
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.Isolation
public import CslibFrontier.Foundations.Analysis.ODE.TransferFunction
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Charpoly.TraceExponential
import Mathlib.Data.List.GetD

/-!
# Kernel-checked gain bounds on frequency intervals

For a rational model `G : Cslib.LinearAlgebra.RatLTI n m p` and a SISO entry `h = H i j` of its
transfer function `H s = C (s I - A)⁻¹ B + D` (`LTISystem.transferFunction`), this module computes,
exactly over `ℚ`, real polynomials `N` and `Q` with

  `‖H (ω * I) i j‖² = N (ω²) / Q (ω²)`,  `Q (ω²) = |χ (i ω)|²`,

and checks gain specifications on frequency bands with the Sturm sign checks of
`CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.IntervalSign`. Every check is a Boolean
function that the kernel evaluates by `decide +kernel`.

## The resolvent

The Faddeev–LeVerrier recurrence (`Cslib.LinearAlgebra.resolvent`) computes matrices
`Y₀, …, Yₙ₋₁` and coefficients `c₀, …, cₙ` (with `cₙ = 1`) such that, in exact arithmetic,
`Σ Yₖ sᵏ = adj (s I - A)` and `Σ cₖ sᵏ = det (s I - A)`. Its correctness is not proved here.
Instead `Cslib.LinearAlgebra.resolventCheck` checks the coefficients of the polynomial identity
`(s I - A) (Σ Yₖ sᵏ) = (Σ cₖ sᵏ) I`, that is `Yₖ₋₁ - A Yₖ = cₖ I` for `k = 0, …, n`, together with
the trace identities `tr Yₖ = (k + 1) cₖ₊₁` that the recurrence also satisfies. Whenever the
check passes, `χ = Σ cₖ sᵏ` is the characteristic polynomial of `A`
(`Cslib.LinearAlgebra.resolventCheck_charpoly`, from the trace identities and Jacobi's formula
`Matrix.derivative_det_adjugate`), at every complex `s` with `χ(s) ≠ 0` the matrix `s I - A` has
the inverse `χ(s)⁻¹ Σ Yₖ sᵏ` (`Cslib.LinearAlgebra.resolventCheck_inv`), and
`H s i j = num(s) / χ(s)` for the numerator `num = c_i Y b_j + d_ij χ`
(`Cslib.LinearAlgebra.RatLTI.transferFunction_apply_eq`).

## Squared gain on the imaginary axis

A real polynomial `f (s) = E (s²) + s O (s²)` takes the value `E (-ω²) + i ω O (-ω²)` at `s = i ω`;
`Cslib.LinearAlgebra.evenOdd` computes the coefficient lists of `u ↦ E (-u)` and `u ↦ O (-u)`, so
that `|f (i ω)|² = E² + u O²` at `u = ω²` (`Cslib.LinearAlgebra.sqAbsImag`). The gain polynomials
`RatLTI.gainNum` and `RatLTI.gainDen` are these for the numerator and for `χ`. They are polynomials
in `u = ω²`, which halves the degree that the Sturm checks see and makes `|h|²` even in `ω`, so a
band constrains `|ω|`.

## Gain checks

A `Cslib.LinearAlgebra.FreqBand` is `lo ≤ |ω| ≤ hi`, or `lo ≤ |ω|` when `hi = none`, with rational
`0 ≤ lo`. `RatLTI.gainLe G i j B γ²` checks that `Q` has no root for `ω²` in the band (so `iωI - A`
is invertible there) and `γ² Q - N ≥ 0`; `RatLTI.gainGe` checks `N - γ² Q ≥ 0` instead.
Acceptance gives `‖H (ω * I) i j‖ ≤ γ` (`RatLTI.norm_le_of_gainLe`) or `γ ≤ ‖H (ω * I) i j‖`
(`RatLTI.le_norm_of_gainGe`) on the band. A bound that the gain attains in the interior of the
band, or at an endpoint where `γ² Q - N` has a multiple root, is rejected (see `nonnegOn`), so a
tight bound may need a slightly larger `γ`.

## Decibels

A rational level `L = p / q` dB bounds the gain by `10 ^ (L / 20)`, which is irrational in general.
The bound goes through a rational `γ²`: `Cslib.LinearAlgebra.dbLe γ² L` checks
`(γ²) ^ (10 q) ≤ 10 ^ p` exactly, so `γ² ≤ 10 ^ (L / 10)`, and `RatLTI.norm_le_db_of_gainLe`
gives `‖H (ω * I) i j‖ ≤ 10 ^ (L / 20)`, the statement `20 log₁₀ ‖H‖ ≤ L` without the junk value
`log 0 = 0`. Lower bounds are stated as `L ≤ 20 * Real.logb 10 ‖H (ω * I) i j‖`
(`RatLTI.db_le_of_gainGe`).

## Violation witnesses

A rejected check does not by itself tell a violated specification from a certificate that is
only too tight, such as a bound that the gain touches. `RatLTI.gainLeVerdict`,
`RatLTI.gainGeVerdict`, `RatLTI.dbLeVerdict` and `RatLTI.dbGeVerdict` return a
`Cslib.LinearAlgebra.GainVerdict`: `proved` when the check accepts, `violated ω` for a rational
`ω` in the band at which the specification fails, or `inconclusive`. The witness is searched
(untrusted) where the checked polynomial `P (ω²)` is negative, at the band's edges and near the
roots of `P (ω²)` from `Cslib.RealRoot.isolateRoots` (`Cslib.LinearAlgebra.witnessCandidates`).
Only the final check is trusted: `RatLTI.pointOk` checks that `ω` is in the band and
`Q (ω²) ≠ 0`, and then `i ω I - A` is invertible and `‖H (ω * I) i j‖² = N (ω²) / Q (ω²)` is
the rational `RatLTI.sqGainAt i j ω` (`RatLTI.sq_norm_eq_sqGainAt`), which is compared with `γ²`,
or with the decibel level through `dbLe` and `dbGe`, exactly. At a root of `Q` the matrix
inverse in `H` is a junk value, so no witness is reported there. `GainVerdict.Holds` states what
each outcome means. A bound attained exactly, like the `0 dB` bound of a low-pass at `ω = 0`, has
no witness and is reported `inconclusive`.

## DC gain

`RatLTI.dcGain` is `D + c₀⁻¹ C Y₀ B`, which is `D - C A⁻¹ B` since `-A Y₀ = c₀ I`.
`RatLTI.dcCheck` checks the resolvent and `c₀ ≠ 0`; acceptance proves that `A` is invertible, that
`D - C A⁻¹ B` is `dcGain` exactly (`RatLTI.dcGain_eq`) and that `H 0` is its image in `ℂ`
(`RatLTI.transferFunction_zero_eq`).

## Main definitions

* `Cslib.LinearAlgebra.resolvent`, `Cslib.LinearAlgebra.resolventCheck`: the Faddeev–LeVerrier
  data and its check.
* `Cslib.LinearAlgebra.RatLTI.numCoeffs`, `RatLTI.gainNum`, `RatLTI.gainDen`.
* `Cslib.LinearAlgebra.FreqBand`, `RatLTI.gainLe`, `RatLTI.gainGe`, `Cslib.LinearAlgebra.dbLe`,
  `Cslib.LinearAlgebra.dbGe`, `RatLTI.dcGain`, `RatLTI.dcCheck`.
* `Cslib.LinearAlgebra.GainVerdict`, `GainVerdict.Holds`, `RatLTI.sqGainAt`, `RatLTI.pointOk`,
  `RatLTI.gainLeVerdict`, `RatLTI.gainGeVerdict`, `RatLTI.dbLeVerdict`, `RatLTI.dbGeVerdict`, and
  the untrusted search `Cslib.LinearAlgebra.witnessCandidates`.

## Main results

* `Cslib.LinearAlgebra.resolventCheck_charpoly`, `RatLTI.ofCoeffList_charCoeffs`: an accepted
  resolvent computes the characteristic polynomial.
* `RatLTI.gainDen_eq_normSq_det`, `RatLTI.gainDen_ne_zero_iff`,
  `RatLTI.sq_norm_transferFunction`: `Q (ω²) = |det (iωI - A)|²`, and
  `‖H (ω * I) i j‖² = N (ω²) / Q (ω²)` wherever `iωI - A` is invertible.
* `RatLTI.sq_norm_le_of_gainLe`, `RatLTI.norm_le_of_gainLe`, `RatLTI.le_sq_norm_of_gainGe`,
  `RatLTI.le_norm_of_gainGe`: gain bounds on a band.
* `RatLTI.norm_le_db_of_gainLe`, `RatLTI.rpow_le_norm_of_gainGe`, `RatLTI.db_le_of_gainGe`:
  decibel forms.
* `Cslib.LinearAlgebra.dbLe_eq_true_iff`, `Cslib.LinearAlgebra.dbGe_eq_true_iff`: the decibel
  checks decide `x ≤ 10 ^ (L / 10)` and `10 ^ (L / 10) ≤ x`.
* `RatLTI.sq_norm_eq_sqGainAt`: the exact squared gain at an accepted rational frequency.
* `RatLTI.gainLeVerdict_holds`, `RatLTI.gainGeVerdict_holds`, `RatLTI.dbLeVerdict_holds`,
  `RatLTI.dbGeVerdict_holds`: each verdict is correct.
* `RatLTI.dcGain_eq`, `RatLTI.transferFunction_zero_eq`: the DC gain.
-/

public section

open Matrix Mathlib.Tactic.Matrix Polynomial Complex Set

namespace Cslib.LinearAlgebra

/-! ### The resolvent `adj (s I - A)` and its check -/

/-- The rows of the `n × n` matrix `c • 1`. -/
@[expose] def rowsScalar (n : ℕ) (c : ℚ) : List (List ℚ) :=
  (List.range n).map fun i => (List.range n).map fun j => if i = j then c else 0

theorem ofLists_rowsScalar (n : ℕ) (c : ℚ) : ofLists n n (rowsScalar n c) = c • 1 := by
  ext i j
  rw [Matrix.smul_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp [rowsScalar, ofLists_apply, ofList_apply, List.getD_eq_getElem?_getD]
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
    simp [rowsScalar, ofLists_apply, ofList_apply, List.getD_eq_getElem?_getD, h, h']

/-- The Faddeev–LeVerrier loop: with `Y = Yᵣ` and `r + 1` steps left, it records
`cᵣ = -tr (A Yᵣ) / (n - r)` and `Yᵣ`, and continues with `Yᵣ₋₁ = A Yᵣ + cᵣ I`. -/
@[expose] def resolventLoop (n : ℕ) (A : List (List ℚ)) :
    ℕ → List (List ℚ) → List (List (List ℚ)) → List ℚ → List (List (List ℚ)) × List ℚ
  | 0, _, Ys, cs => (Ys, cs)
  | r + 1, Y, Ys, cs =>
    let AY := rowsMul n n n A Y
    let c : ℚ := -rowsTrace n AY / ((n - r : ℕ) : ℚ)
    resolventLoop n A r (rowsMap₂ (· + ·) n n AY (rowsScalar n c)) (Y :: Ys) (c :: cs)

/-- The Faddeev–LeVerrier data of the `n × n` matrix with rows `A`: the matrices `[Y₀, …, Yₙ₋₁]`,
with `Σ Yₖ sᵏ = adj (s I - A)`, and the coefficients `[c₀, …, cₙ]` of `det (s I - A)` in exact
arithmetic. Only `resolventCheck` is trusted. -/
@[expose] def resolvent (n : ℕ) (A : List (List ℚ)) : List (List (List ℚ)) × List ℚ :=
  resolventLoop n A n (rowsOne n) [] [1]

/-- The rows of `Yₖ₋₁`, with `Y₋₁ = 0`. -/
@[expose] def prevRows (Ys : List (List (List ℚ))) : ℕ → List (List ℚ)
  | 0 => []
  | k + 1 => Ys.getD k []

/-- The rows of `Yₖ₋₁ - A Yₖ - cₖ I`. -/
@[expose] def resolventResidual (n : ℕ) (A : List (List ℚ)) (Ys : List (List (List ℚ)))
    (cs : List ℚ) (k : ℕ) : List (List ℚ) :=
  rowsMap₂ (· - ·) n n (rowsMap₂ (· - ·) n n (prevRows Ys k) (rowsMul n n n A (Ys.getD k [])))
    (rowsScalar n (cs.getD k 0))

/-- **The resolvent check.** `Ys` has `n` matrices, `cs` has `n + 1` coefficients ending in `1`,
`Yₖ₋₁ - A Yₖ = cₖ I` for `k = 0, …, n` (with `Y₋₁ = Yₙ = 0`), and `tr Yₖ = (k + 1) cₖ₊₁`. -/
@[expose] def resolventCheck (n : ℕ) (A : List (List ℚ)) (Ys : List (List (List ℚ)))
    (cs : List ℚ) : Bool :=
  Ys.length == n && cs.length == n + 1 && cs.getD n 0 == 1 &&
    (List.range (n + 1)).all (fun k => allZero (resolventResidual n A Ys cs k)) &&
    (List.range n).all fun k => rowsTrace n (Ys.getD k []) == ((k + 1 : ℕ) : ℚ) * cs.getD (k + 1) 0

section Resolvent

variable {n : ℕ} {A : List (List ℚ)} {Ys : List (List (List ℚ))} {cs : List ℚ}
variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The matrix of rational rows, read in a `ℚ`-algebra `R`. -/
noncomputable abbrev ratMat (R : Type*) [CommRing R] [Algebra ℚ R] (k l : ℕ)
    (rows : List (List ℚ)) : Matrix (Fin k) (Fin l) R :=
  (ofLists k l rows).map (algebraMap ℚ R)

/-- The complex matrix of rational rows. -/
noncomputable abbrev cplx (k l : ℕ) (rows : List (List ℚ)) : Matrix (Fin k) (Fin l) ℂ :=
  ratMat ℂ k l rows

private theorem ofLists_nil (k l : ℕ) : ofLists k l ([] : List (List ℚ)) = 0 :=
  ofLists_eq_zero_of_allZero rfl

/-- The coefficient identities `Yₖ₋₁ - A Yₖ = cₖ I` of an accepted resolvent, over `ℚ`. -/
private theorem coeff_identity_rat (h : resolventCheck n A Ys cs = true) {k : ℕ}
    (hk : k < n + 1) :
    ofLists n n (prevRows Ys k) - ofLists n n A * ofLists n n (Ys.getD k []) =
      cs.getD k 0 • 1 := by
  simp only [resolventCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have h0 := ofLists_eq_zero_of_allZero (k := n) (l := n) (h.1.2 k hk)
  rw [resolventResidual, ofLists_rowsMap₂, ofLists_rowsMap₂, ofLists_rowsScalar] at h0
  rw [← sub_eq_zero, ← ofLists_rowsMul n n n A (Ys.getD k [])]
  ext i j
  simpa using congrFun (congrFun h0 i) j

/-- The coefficient identities `Yₖ₋₁ - A Yₖ = cₖ I` of an accepted resolvent, in `R`. -/
private theorem coeff_identity (h : resolventCheck n A Ys cs = true) {k : ℕ} (hk : k < n + 1) :
    ratMat R n n (prevRows Ys k) - ratMat R n n A * ratMat R n n (Ys.getD k []) =
      algebraMap ℚ R (cs.getD k 0) • 1 := by
  change (algebraMap ℚ R).mapMatrix _ - (algebraMap ℚ R).mapMatrix _ *
    (algebraMap ℚ R).mapMatrix _ = _
  rw [← map_mul, ← map_sub, coeff_identity_rat h hk]
  ext i j
  by_cases hij : i = j <;> simp [hij]

private theorem length_eq (h : resolventCheck n A Ys cs = true) :
    Ys.length = n ∧ cs.length = n + 1 := by
  simp only [resolventCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2⟩

/-- The value of a polynomial with at most `N` coefficients at `s`. -/
private theorem aeval_eq_sum {l : List ℚ} {N : ℕ} (hl : l.length ≤ N) (s : R) :
    aeval s (ofCoeffList l) = ∑ k ∈ Finset.range N, algebraMap ℚ R (l.getD k 0) * s ^ k := by
  by_cases hl0 : l = []
  · subst hl0; simp
  have := List.length_pos_of_ne_nil hl0
  rw [aeval_eq_sum_range' (n := N) (lt_of_le_of_lt (natDegree_ofCoeffList_le l) (by omega))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_ofCoeffList, Algebra.smul_def]

/-- **The resolvent identity.** If the resolvent check accepts, then for every `s` in a
commutative `ℚ`-algebra, `(s I - A) (Σₖ sᵏ Yₖ) = χ(s) I` with `χ = ofCoeffList cs`. -/
theorem resolventCheck_mul (h : resolventCheck n A Ys cs = true) (s : R) :
    (s • (1 : Matrix (Fin n) (Fin n) R) - ratMat R n n A) *
        ∑ k ∈ Finset.range n, s ^ k • ratMat R n n (Ys.getD k []) =
      aeval s (ofCoeffList cs) • 1 := by
  obtain ⟨hYl, hcl⟩ := length_eq h
  have hYn : ratMat R n n (Ys.getD n []) = 0 := by
    rw [List.getD_eq_default _ _ (by omega), ratMat, ofLists_nil, Matrix.map_zero _ (map_zero _)]
  have hZ0 : ratMat R n n (prevRows Ys 0) = 0 := by
    rw [prevRows, ratMat, ofLists_nil, Matrix.map_zero _ (map_zero _)]
  have step : ∀ k, (s • (1 : Matrix (Fin n) (Fin n) R) - ratMat R n n A) *
      (s ^ k • ratMat R n n (Ys.getD k [])) =
        s ^ (k + 1) • ratMat R n n (prevRows Ys (k + 1)) -
          s ^ k • (ratMat R n n A * ratMat R n n (Ys.getD k [])) := fun k => by
    rw [sub_mul, smul_mul_assoc, one_mul, smul_smul, ← pow_succ', mul_smul_comm, prevRows]
  have hsum₁ : ∑ k ∈ Finset.range n, s ^ (k + 1) • ratMat R n n (prevRows Ys (k + 1)) =
      ∑ k ∈ Finset.range (n + 1), s ^ k • ratMat R n n (prevRows Ys k) := by
    rw [Finset.sum_range_succ', hZ0, smul_zero, add_zero]
  have hsum₂ : ∑ k ∈ Finset.range n, s ^ k • (ratMat R n n A * ratMat R n n (Ys.getD k [])) =
      ∑ k ∈ Finset.range (n + 1), s ^ k • (ratMat R n n A * ratMat R n n (Ys.getD k [])) := by
    rw [Finset.sum_range_succ, hYn, mul_zero, smul_zero, add_zero]
  rw [Finset.mul_sum, Finset.sum_congr rfl fun k _ => step k, Finset.sum_sub_distrib, hsum₁,
    hsum₂, ← Finset.sum_sub_distrib, aeval_eq_sum hcl.le, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← smul_sub, coeff_identity h (Finset.mem_range.1 hk), smul_smul, mul_comm]

/-- At every `s` in a field with `χ(s) ≠ 0`, an accepted resolvent inverts `s I - A`:
`(s I - A)⁻¹ = χ(s)⁻¹ Σₖ sᵏ Yₖ`. -/
theorem resolventCheck_inv {K : Type*} [Field K] [Algebra ℚ K]
    (h : resolventCheck n A Ys cs = true) {s : K} (hs : aeval s (ofCoeffList cs) ≠ 0) :
    (s • (1 : Matrix (Fin n) (Fin n) K) - ratMat K n n A)⁻¹ =
      (aeval s (ofCoeffList cs))⁻¹ • ∑ k ∈ Finset.range n, s ^ k • ratMat K n n (Ys.getD k []) :=
  Matrix.inv_eq_right_inv (by rw [mul_smul_comm, resolventCheck_mul h, smul_smul,
    inv_mul_cancel₀ hs, one_smul])

/-- Two monic polynomials of the same degree over a field of characteristic zero with
`g f' = f g'` are equal: their difference `h` satisfies `g h' = h g'`, and comparing the
coefficients of degree `deg g + deg h - 1` forces `h = 0`. -/
private theorem eq_of_monic_of_mul_derivative_eq {K : Type*} [Field K] [CharZero K]
    {f g : K[X]} {N : ℕ} (hf : f.Monic) (hg : g.Monic) (hfN : f.natDegree = N)
    (hgN : g.natDegree = N) (h : g * derivative f = f * derivative g) : f = g := by
  by_contra hne
  have hh0 : f - g ≠ 0 := sub_ne_zero.2 hne
  have hdeg : (f - g).natDegree < N := by
    have hlt := degree_sub_lt_left (p := f) (q := g) (by rw [degree_eq_natDegree hf.ne_zero,
      degree_eq_natDegree hg.ne_zero, hfN, hgN]) hf.ne_zero (by rw [hf.leadingCoeff,
      hg.leadingCoeff])
    rw [← hfN]
    exact natDegree_lt_natDegree hh0 hlt
  have key : g * derivative (f - g) = (f - g) * derivative g := by
    rw [derivative_sub]; linear_combination h
  set d := (f - g).natDegree
  have hlc : (f - g).coeff d ≠ 0 := leadingCoeff_ne_zero.2 hh0
  have hN : 1 ≤ N := by omega
  rcases Nat.eq_zero_or_pos d with hd | hd
  · have hc := eq_C_of_natDegree_eq_zero hd
    rw [hc, derivative_C, mul_zero, eq_comm, mul_eq_zero, C_eq_zero] at key
    rcases key with key | key
    · exact hlc (by rw [hd]; exact key)
    · have := congrArg (fun q : K[X] => q.coeff (N - 1)) key
      simp only [coeff_derivative, coeff_zero] at this
      rw [Nat.sub_add_cancel hN, ← hgN, hg.coeff_natDegree, one_mul] at this
      have hne' : ((g.natDegree - 1 : ℕ) : K) + 1 ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero (g.natDegree - 1)
      exact hne' this
  · have h1 : (g * derivative (f - g)).coeff (N + (d - 1)) =
        ((f - g) * derivative g).coeff (N + (d - 1)) := by rw [key]
    rw [coeff_mul_add_eq_of_natDegree_le hgN.le ((natDegree_derivative_le _).trans le_rfl),
      show N + (d - 1) = d + (N - 1) by omega,
      coeff_mul_add_eq_of_natDegree_le le_rfl ((natDegree_derivative_le _).trans (by omega)),
      coeff_derivative, coeff_derivative, Nat.sub_add_cancel hd, Nat.sub_add_cancel hN,
      ← hgN, show g.coeff g.natDegree = 1 from hg, hgN] at h1
    change 1 * ((f - g).coeff d * (((d - 1 : ℕ) : K) + 1)) =
      (f - g).coeff d * (1 * (((N - 1 : ℕ) : K) + 1)) at h1
    rw [one_mul, one_mul] at h1
    have : ((d - 1 : ℕ) : K) + 1 = ((N - 1 : ℕ) : K) + 1 := mul_left_cancel₀ hlc h1
    have : d = N := by
      have := (by exact_mod_cast this : (d - 1) + 1 = (N - 1) + 1)
      omega
    omega

/-- `(charmatrix M)' = 1` entrywise. -/
private theorem charmatrix_map_derivative {k : ℕ} (M : Matrix (Fin k) (Fin k) ℚ) :
    (charmatrix M).map derivative = 1 := by
  refine Matrix.ext fun i j => ?_
  by_cases hij : i = j
  · subst hij; simp [Matrix.map_apply, charmatrix_apply_eq]
  · simp [Matrix.map_apply, charmatrix_apply_ne _ _ _ hij, Matrix.one_apply_ne hij]

/-- **The resolvent check pins down the characteristic polynomial.** If it accepts, then
`ofCoeffList cs` is the characteristic polynomial of `A`: multiplying the identity
`(X I - A) Y = χ I` by `adj (X I - A)` gives `charpoly A • Y = χ • adj (X I - A)`; its trace,
with Jacobi's formula `tr adj (X I - A) = (charpoly A)'` and the checked `tr Y = χ'`, gives
`charpoly A * χ' = χ * (charpoly A)'`, and both polynomials are monic of degree `n`. -/
theorem resolventCheck_charpoly (h : resolventCheck n A Ys cs = true) :
    ofCoeffList cs = (ofLists n n A).charpoly := by
  obtain ⟨hYl, hcl⟩ := length_eq h
  set M := ofLists n n A
  set Yp : Matrix (Fin n) (Fin n) ℚ[X] :=
    ∑ k ∈ Finset.range n, (X : ℚ[X]) ^ k • ratMat ℚ[X] n n (Ys.getD k []) with hYp
  have h1 := resolventCheck_mul (R := ℚ[X]) h X
  rw [aeval_X_left_apply] at h1
  have hcm : (X : ℚ[X]) • (1 : Matrix (Fin n) (Fin n) ℚ[X]) - ratMat ℚ[X] n n A =
      charmatrix M := by
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j
    · subst hij; simp [charmatrix_apply_eq, M, Polynomial.algebraMap_eq]
    · simp [hij, M, Polynomial.algebraMap_eq]
  rw [hcm] at h1
  have h2 : M.charpoly • Yp = ofCoeffList cs • adjugate (charmatrix M) := by
    calc M.charpoly • Yp = (adjugate (charmatrix M) * charmatrix M) * Yp := by
          rw [adjugate_mul, Matrix.charpoly, smul_mul_assoc, one_mul]
      _ = ofCoeffList cs • adjugate (charmatrix M) := by
          rw [Matrix.mul_assoc, h1, mul_smul_comm, mul_one]
  have h3 := congrArg Matrix.trace h2
  rw [trace_smul, trace_smul, smul_eq_mul, smul_eq_mul] at h3
  have hJ : (adjugate (charmatrix M)).trace = derivative M.charpoly := by
    rw [Matrix.charpoly, derivative_det_adjugate, charmatrix_map_derivative, Matrix.mul_one]
  have hT : Yp.trace = derivative (ofCoeffList cs) := by
    simp only [resolventCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
      beq_iff_eq] at h
    have htr : ∀ k ∈ Finset.range n, (ratMat ℚ[X] n n (Ys.getD k [])).trace =
        C (((k + 1 : ℕ) : ℚ) * cs.getD (k + 1) 0) := by
      intro k hk
      rw [← h.2 k (Finset.mem_range.1 hk), ← trace_ofLists]
      simp [Matrix.trace, ratMat, Polynomial.algebraMap_eq, map_sum]
    ext i
    rw [coeff_derivative, coeff_ofCoeffList, hYp, trace_sum,
      Finset.sum_congr rfl fun k hk => by rw [trace_smul, htr k hk, smul_eq_mul, mul_comm],
      finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    split_ifs with hi
    · push_cast; ring
    · rw [Finset.mem_range] at hi
      rw [List.getD_eq_default _ _ (by omega), zero_mul]
  rw [hJ, hT] at h3
  have hmon : (ofCoeffList cs).Monic ∧ (ofCoeffList cs).natDegree = n := by
    have hle : (ofCoeffList cs).natDegree ≤ n := (natDegree_ofCoeffList_le cs).trans (by omega)
    have h1 : (ofCoeffList cs).coeff n = 1 := by
      simp only [resolventCheck, Bool.and_eq_true, beq_iff_eq] at h
      rw [coeff_ofCoeffList]; exact h.1.1.2
    exact ⟨monic_of_natDegree_le_of_coeff_eq_one n hle h1,
      natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [h1]; exact one_ne_zero)⟩
  exact eq_of_monic_of_mul_derivative_eq hmon.1 (charpoly_monic M) hmon.2
    (charpoly_natDegree_eq_dim M |>.trans (Fintype.card_fin n)) (by linear_combination h3)

end Resolvent

/-! ### Squared modulus on the imaginary axis -/

/-- The coefficient lists of `u ↦ E (-u)` and `u ↦ O (-u)` for `f (s) = E (s²) + s O (s²)`, so
that `f (i ω) = E' (ω²) + i ω O' (ω²)` (`Cslib.LinearAlgebra.aeval_evenOdd`). -/
@[expose] def evenOdd : List ℚ → List ℚ × List ℚ
  | [] => ([], [])
  | a :: l =>
    let eo := evenOdd l
    (CoeffList.sub [a] (CoeffList.shift 1 eo.2), eo.1)

/-- The coefficient list, in `u = ω²`, of `|f (i ω)|²` for a real polynomial `f`. -/
@[expose] def sqAbsImag (f : List ℚ) : List ℚ :=
  let eo := evenOdd f
  CoeffList.add (CoeffList.mul eo.1 eo.1) (CoeffList.shift 1 (CoeffList.mul eo.2 eo.2))

/-- The value of a real polynomial at `i ω` from its even and odd parts. -/
theorem aeval_evenOdd (f : List ℚ) (ω : ℝ) :
    aeval ((ω : ℂ) * I) (ofCoeffList f) =
      ((aeval (ω ^ 2) (ofCoeffList (evenOdd f).1) : ℝ) : ℂ) +
        (ω : ℂ) * I * ((aeval (ω ^ 2) (ofCoeffList (evenOdd f).2) : ℝ) : ℂ) := by
  induction f with
  | nil => simp [evenOdd]
  | cons a l ih =>
    simp only [evenOdd, ofCoeffList_cons, map_add, aeval_C, map_mul, aeval_X, ih,
      CoeffList.ofCoeffList_sub, CoeffList.ofCoeffList_shift, map_sub, map_pow, eq_ratCast]
    simp only [ofCoeffList_nil, mul_zero, add_zero, pow_one, map_zero]
    push_cast
    linear_combination ((ω : ℂ) ^ 2 * ((aeval (ω ^ 2) (ofCoeffList (evenOdd l).2) : ℝ) : ℂ)) *
      I_sq

/-- `|f (i ω)|²` is the value of `sqAbsImag f` at `ω²`. -/
theorem normSq_aeval (f : List ℚ) (ω : ℝ) :
    normSq (aeval ((ω : ℂ) * I) (ofCoeffList f)) = aeval (ω ^ 2) (ofCoeffList (sqAbsImag f)) := by
  rw [aeval_evenOdd, sqAbsImag]
  simp only [CoeffList.ofCoeffList_add, CoeffList.ofCoeffList_mul, CoeffList.ofCoeffList_shift,
    map_add, map_mul, map_pow, aeval_X]
  rw [show ∀ x y : ℝ, (x : ℂ) + (ω : ℂ) * I * (y : ℂ) = (x : ℂ) + ((ω * y : ℝ) : ℂ) * I by
    intro x y; push_cast; ring, normSq_add_mul_I]
  ring

/-! ### Transfer functions of rational models -/

namespace RatLTI

variable {n m p : ℕ} (G : RatLTI n m p)

/-- The Faddeev–LeVerrier data of `A`. -/
@[expose] def resolventData : List (List (List ℚ)) × List ℚ := resolvent n G.A

/-- The coefficients of `χ (s) = det (s I - A)`, as computed by `resolvent`. -/
@[expose] def charCoeffs : List ℚ := (resolvent n G.A).2

/-- Whether the resolvent of `A` passes `resolventCheck`. -/
@[expose] def resolventOk : Bool :=
  resolventCheck n G.A (resolvent n G.A).1 (resolvent n G.A).2

/-- The coefficients of the numerator `num (s) = c_i (Σ Yₖ sᵏ) b_j + d_ij χ (s)` of
`H s i j = num (s) / χ (s)`. -/
@[expose] def numCoeffs (i j : ℕ) : List ℚ :=
  CoeffList.add
    ((List.range n).map fun k =>
      ((rowsMul p n m G.C (rowsMul n n m ((resolvent n G.A).1.getD k []) G.B)).getD i []).getD j 0)
    (CoeffList.smul ((G.D.getD i []).getD j 0) (resolvent n G.A).2)

/-- The gain numerator `N`, in `u = ω²`: `N (ω²) = |num (i ω)|²`. -/
@[expose] def gainNum (i j : ℕ) : List ℚ := sqAbsImag (G.numCoeffs i j)

/-- The gain denominator `Q`, in `u = ω²`: `Q (ω²) = |χ (i ω)|²`. -/
@[expose] def gainDen : List ℚ := sqAbsImag G.charCoeffs

private theorem cplx_toSystem_A :
    G.toSystem.A.map (algebraMap ℝ ℂ) = cplx n n G.A := by
  ext; simp [toSystem]

private theorem cplx_toSystem_B :
    G.toSystem.B.map (algebraMap ℝ ℂ) = cplx n m G.B := by
  ext; simp [toSystem]

private theorem cplx_toSystem_C :
    G.toSystem.C.map (algebraMap ℝ ℂ) = cplx p n G.C := by
  ext; simp [toSystem]

private theorem cplx_toSystem_D :
    G.toSystem.D.map (algebraMap ℝ ℂ) = cplx p m G.D := by
  ext; simp [toSystem]

private theorem cplx_mul {k l o : ℕ} (M : List (List ℚ)) (N : List (List ℚ)) :
    cplx k l M * cplx l o N = cplx k o (rowsMul k l o M N) := by
  rw [cplx, cplx, cplx, ratMat, ratMat, ratMat, ← Matrix.map_mul, ofLists_rowsMul]

/-- **The transfer function from the resolvent.** If the resolvent check accepts and
`χ (s) ≠ 0`, then `H s i j = num (s) / χ (s)`. -/
theorem transferFunction_apply_eq (hc : G.resolventOk = true) {s : ℂ}
    (hs : aeval s (ofCoeffList G.charCoeffs) ≠ 0) (i : Fin p) (j : Fin m) :
    G.toSystem.transferFunction s i j =
      aeval s (ofCoeffList (G.numCoeffs i j)) / aeval s (ofCoeffList G.charCoeffs) := by
  have hc' : resolventCheck n G.A (resolvent n G.A).1 (resolvent n G.A).2 = true := hc
  set χ := aeval s (ofCoeffList (resolvent n G.A).2)
  have hχ : χ ≠ 0 := hs
  set e : ℕ → ℚ := fun k =>
    ((rowsMul p n m G.C (rowsMul n n m ((resolvent n G.A).1.getD k []) G.B)).getD i []).getD j 0
  have hW : cplx p n G.C * (χ⁻¹ • ∑ k ∈ Finset.range n,
      s ^ k • ratMat ℂ n n ((resolvent n G.A).1.getD k [])) * cplx n m G.B =
      χ⁻¹ • ∑ k ∈ Finset.range n,
        s ^ k • cplx p m
          (rowsMul p n m G.C (rowsMul n n m ((resolvent n G.A).1.getD k []) G.B)) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, cplx_mul, cplx_mul]
  have hS : ∑ k ∈ Finset.range n, s ^ k * cplx p m (rowsMul p n m G.C
      (rowsMul n n m ((resolvent n G.A).1.getD k []) G.B)) i j =
      ∑ k ∈ Finset.range n, algebraMap ℚ ℂ
        (((List.range n).map e).getD k 0) * s ^ k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [List.getD_eq_getElem ((List.range n).map e) 0 (by simpa using hk), List.getElem_map,
      List.getElem_range, mul_comm]
    simp [cplx, ratMat, ofLists_apply, ofList_apply, e]
  have hD : cplx p m G.D i j = algebraMap ℚ ℂ ((G.D.getD i []).getD j 0) := by
    simp [cplx, ratMat, ofLists_apply, ofList_apply]
  rw [LTISystem.transferFunction, cplx_toSystem_A, cplx_toSystem_B, cplx_toSystem_C,
    cplx_toSystem_D, resolventCheck_inv hc' hs, Matrix.add_apply, hW, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [hS, hD, numCoeffs, CoeffList.ofCoeffList_add, CoeffList.ofCoeffList_smul, map_add, map_mul,
    aeval_C, aeval_eq_sum (N := n) (by simp)]
  change _ = (_ + _ * χ) / χ
  field_simp
  simp only [e]

/-- **`χ` is the characteristic polynomial of `A`**, for an accepted resolvent. -/
theorem ofCoeffList_charCoeffs (hc : G.resolventOk = true) :
    ofCoeffList G.charCoeffs = (ofLists n n G.A).charpoly :=
  resolventCheck_charpoly hc

/-- **`Q (ω²) = |det (i ω I - A)|²`**, for an accepted resolvent. -/
theorem gainDen_eq_normSq_det (hc : G.resolventOk = true) (ω : ℝ) :
    aeval (ω ^ 2) (ofCoeffList G.gainDen) =
      normSq (((ω : ℂ) * I) • (1 : Matrix (Fin n) (Fin n) ℂ) -
        G.toSystem.A.map (algebraMap ℝ ℂ)).det := by
  rw [gainDen, ← normSq_aeval, G.ofCoeffList_charCoeffs hc, cplx_toSystem_A, ←
    eval_map_algebraMap, ← charpoly_map, eval_charpoly, scalar_apply, smul_one_eq_diagonal]

/-- `Q (ω²) ≠ 0` exactly where `i ω I - A` is invertible, for an accepted resolvent. -/
theorem gainDen_ne_zero_iff (hc : G.resolventOk = true) (ω : ℝ) :
    aeval (ω ^ 2) (ofCoeffList G.gainDen) ≠ 0 ↔
      IsUnit (((ω : ℂ) * I) • (1 : Matrix (Fin n) (Fin n) ℂ) -
        G.toSystem.A.map (algebraMap ℝ ℂ)) := by
  rw [G.gainDen_eq_normSq_det hc, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ne_eq,
    ne_eq, normSq_eq_zero]

/-- **Squared gain as a ratio of polynomials.** If the resolvent check accepts, then at every real
`ω` where `i ω I - A` is invertible, `‖H (ω * I) i j‖² = N (ω²) / Q (ω²)`, and `Q (ω²) > 0`. -/
theorem sq_norm_transferFunction (hc : G.resolventOk = true) (i : Fin p) (j : Fin m) {ω : ℝ}
    (hω : IsUnit (((ω : ℂ) * I) • (1 : Matrix (Fin n) (Fin n) ℂ) -
      G.toSystem.A.map (algebraMap ℝ ℂ))) :
    ‖G.toSystem.transferFunction ((ω : ℂ) * I) i j‖ ^ 2 =
      aeval (ω ^ 2) (ofCoeffList (G.gainNum i j)) / aeval (ω ^ 2) (ofCoeffList G.gainDen) := by
  have hQ := (G.gainDen_ne_zero_iff hc ω).2 hω
  have hs : aeval ((ω : ℂ) * I) (ofCoeffList G.charCoeffs) ≠ 0 := fun h0 => hQ (by
    rw [gainDen, ← normSq_aeval, h0, map_zero])
  rw [G.transferFunction_apply_eq hc hs, Complex.sq_norm, normSq_div, gainNum, gainDen,
    normSq_aeval, normSq_aeval]

end RatLTI

/-! ### Gain checks on frequency bands -/

/-- A **frequency band** `lo ≤ |ω| ≤ hi`, or `lo ≤ |ω|` when `hi = none`. The checks require
`0 ≤ lo`. -/
structure FreqBand where
  /-- The lower edge, in the model's angular-frequency unit. -/
  lo : ℚ
  /-- The upper edge, or `none` for a half-line. -/
  hi : Option ℚ

namespace FreqBand

/-- Membership of a real angular frequency in a band. -/
@[expose] def Mem (B : FreqBand) (ω : ℝ) : Prop :=
  (B.lo : ℝ) ≤ |ω| ∧ ∀ b ∈ B.hi, |ω| ≤ (b : ℝ)

/-- The band of `u = ω²`. -/
@[expose] def sqHi (B : FreqBand) : Option ℚ := B.hi.map fun b => b * b

theorem sq_mem_bandSet {B : FreqBand} (hlo : 0 ≤ B.lo) {ω : ℝ} (hω : B.Mem ω) :
    ω ^ 2 ∈ Cslib.RealRoot.bandSet (B.lo * B.lo) B.sqHi := by
  obtain ⟨h1, h2⟩ := hω
  have hlo' : (0 : ℝ) ≤ B.lo := by exact_mod_cast hlo
  refine ⟨?_, fun b hb => ?_⟩
  · rw [← sq_abs ω]; push_cast; nlinarith
  · obtain ⟨b, hb', rfl⟩ := Option.mem_map.1 hb
    have := h2 b hb'
    rw [← sq_abs ω]; push_cast; nlinarith [abs_nonneg ω]

end FreqBand

namespace RatLTI

open Cslib.RealRoot

variable {n m p : ℕ} (G : RatLTI n m p)

/-- **Upper gain check.** On the band `B`: the resolvent check, `0 ≤ B.lo`, no root of `Q`, and
`γ² Q - N ≥ 0`, for the entry `(i, j)` and `γsq = γ²`. -/
@[expose] def gainLe (i : Fin p) (j : Fin m) (B : FreqBand) (γsq : ℚ) : Bool :=
  G.resolventOk && decide (0 ≤ B.lo) && rootFreeOn G.gainDen (B.lo * B.lo) B.sqHi &&
    nonnegOn (CoeffList.sub (CoeffList.smul γsq G.gainDen) (G.gainNum i j)) (B.lo * B.lo) B.sqHi

/-- **Lower gain check.** As `gainLe`, with `N - γ² Q ≥ 0`. -/
@[expose] def gainGe (i : Fin p) (j : Fin m) (B : FreqBand) (γsq : ℚ) : Bool :=
  G.resolventOk && decide (0 ≤ B.lo) && rootFreeOn G.gainDen (B.lo * B.lo) B.sqHi &&
    nonnegOn (CoeffList.sub (G.gainNum i j) (CoeffList.smul γsq G.gainDen)) (B.lo * B.lo) B.sqHi

private theorem eval_real (cs : List ℚ) (x : ℝ) :
    ((ofCoeffList cs).map (algebraMap ℚ ℝ)).eval x = aeval x (ofCoeffList cs) :=
  eval_map_algebraMap _ _

/-- The common part of the gain checks: on the band, `Q (ω²) > 0`,
`‖H (ω * I) i j‖² = N (ω²) / Q (ω²)`, and the checked polynomial `P` is nonnegative at `ω²`. -/
private theorem band_facts (hc : G.resolventOk = true) {B : FreqBand} (hlo : 0 ≤ B.lo)
    (hQ : rootFreeOn G.gainDen (B.lo * B.lo) B.sqHi = true) {P : List ℚ}
    (hP : nonnegOn P (B.lo * B.lo) B.sqHi = true) (i : Fin p) (j : Fin m) {ω : ℝ}
    (hω : B.Mem ω) :
    0 < aeval (ω ^ 2) (ofCoeffList G.gainDen) ∧
      ‖G.toSystem.transferFunction ((ω : ℂ) * I) i j‖ ^ 2 =
        aeval (ω ^ 2) (ofCoeffList (G.gainNum i j)) / aeval (ω ^ 2) (ofCoeffList G.gainDen) ∧
      0 ≤ aeval (ω ^ 2) (ofCoeffList P) := by
  have hne := eval_ne_zero_of_rootFreeOn hQ (FreqBand.sq_mem_bandSet hlo hω)
  rw [eval_real] at hne
  have hQpos : 0 < aeval (ω ^ 2) (ofCoeffList G.gainDen) := by
    refine lt_of_le_of_ne ?_ hne.symm
    rw [gainDen, ← normSq_aeval]
    exact normSq_nonneg _
  refine ⟨hQpos, G.sq_norm_transferFunction hc i j ((G.gainDen_ne_zero_iff hc ω).1 hne), ?_⟩
  rw [← eval_real]
  exact eval_nonneg_of_nonnegOn hP (FreqBand.sq_mem_bandSet hlo hω)

/-- **Soundness of the upper gain check**: `‖H (ω * I) i j‖² ≤ γ²` on the band. -/
theorem sq_norm_le_of_gainLe {i : Fin p} {j : Fin m} {B : FreqBand} {γsq : ℚ}
    (h : G.gainLe i j B γsq = true) {ω : ℝ} (hω : B.Mem ω) :
    ‖G.toSystem.transferFunction ((ω : ℂ) * I) i j‖ ^ 2 ≤ γsq := by
  simp only [gainLe, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hc, hlo⟩, hQ⟩, hP⟩ := h
  obtain ⟨hQpos, hH, hP'⟩ := G.band_facts hc hlo hQ hP i j hω
  simp only [CoeffList.ofCoeffList_sub, CoeffList.ofCoeffList_smul, map_sub, map_mul, aeval_C,
    eq_ratCast, sub_nonneg] at hP'
  rw [hH, div_le_iff₀ hQpos]
  exact hP'

/-- **Soundness of the lower gain check**: `γ² ≤ ‖H (ω * I) i j‖²` on the band. -/
theorem le_sq_norm_of_gainGe {i : Fin p} {j : Fin m} {B : FreqBand} {γsq : ℚ}
    (h : G.gainGe i j B γsq = true) {ω : ℝ} (hω : B.Mem ω) :
    (γsq : ℝ) ≤ ‖G.toSystem.transferFunction ((ω : ℂ) * I) i j‖ ^ 2 := by
  simp only [gainGe, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hc, hlo⟩, hQ⟩, hP⟩ := h
  obtain ⟨hQpos, hH, hP'⟩ := G.band_facts hc hlo hQ hP i j hω
  simp only [CoeffList.ofCoeffList_sub, CoeffList.ofCoeffList_smul, map_sub, map_mul, aeval_C,
    eq_ratCast, sub_nonneg] at hP'
  rw [hH, le_div_iff₀ hQpos]
  exact hP'

/-- **Upper gain bound** `‖H (ω * I) i j‖ ≤ γ` on the band, from `gainLe` with `γ²`. -/
theorem norm_le_of_gainLe {i : Fin p} {j : Fin m} {B : FreqBand} {γ : ℚ} (hγ : 0 ≤ γ)
    (h : G.gainLe i j B (γ ^ 2) = true) {ω : ℝ} (hω : B.Mem ω) :
    ‖G.toSystem.transferFunction ((ω : ℂ) * I) i j‖ ≤ γ := by
  have := G.sq_norm_le_of_gainLe h hω
  push_cast at this
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by exact_mod_cast hγ) two_ne_zero).1 this

/-- **Lower gain bound** `γ ≤ ‖H (ω * I) i j‖` on the band, from `gainGe` with `γ²`. -/
theorem le_norm_of_gainGe {i : Fin p} {j : Fin m} {B : FreqBand} {γ : ℚ} (hγ : 0 ≤ γ)
    (h : G.gainGe i j B (γ ^ 2) = true) {ω : ℝ} (hω : B.Mem ω) :
    (γ : ℝ) ≤ ‖G.toSystem.transferFunction ((ω : ℂ) * I) i j‖ := by
  have := G.le_sq_norm_of_gainGe h hω
  push_cast at this
  exact (pow_le_pow_iff_left₀ (by exact_mod_cast hγ) (norm_nonneg _) two_ne_zero).1 this

end RatLTI

/-! ### Decibels -/

/-- Whether `0 ≤ x ≤ 10 ^ (L / 10)`, decided in `ℚ` as `x ^ (10 q) ≤ 10 ^ p` for `L = p / q` in
lowest terms. -/
@[expose] def dbLe (x L : ℚ) : Bool :=
  decide (0 ≤ x) &&
    if 0 ≤ L.num then decide (x ^ (10 * L.den) ≤ 10 ^ L.num.toNat)
    else decide (x ^ (10 * L.den) * 10 ^ (-L.num).toNat ≤ 1)

/-- Whether `10 ^ (L / 10) ≤ x`, decided in `ℚ` as `10 ^ p ≤ x ^ (10 q)` for `L = p / q` in lowest
terms (and `0 < x`). -/
@[expose] def dbGe (x L : ℚ) : Bool :=
  decide (0 < x) &&
    if 0 ≤ L.num then decide (10 ^ L.num.toNat ≤ x ^ (10 * L.den))
    else decide (1 ≤ x ^ (10 * L.den) * 10 ^ (-L.num).toNat)

private theorem ten_zpow_num (L : ℚ) :
    (10 : ℝ) ^ ((L.num : ℝ)) =
      if 0 ≤ L.num then ((10 ^ L.num.toNat : ℚ) : ℝ) else (((10 ^ (-L.num).toNat : ℚ) : ℝ))⁻¹ := by
  split_ifs with h
  · have h2 : ((L.num.toNat : ℕ) : ℤ) = L.num := Int.toNat_of_nonneg h
    rw [show (L.num : ℝ) = ((L.num.toNat : ℕ) : ℝ) by rw [← Int.cast_natCast, h2],
      Real.rpow_natCast]
    push_cast; rfl
  · have h2 : (((-L.num).toNat : ℕ) : ℤ) = -L.num := Int.toNat_of_nonneg (by omega)
    rw [show (L.num : ℝ) = -(((-L.num).toNat : ℕ) : ℝ) by rw [← Int.cast_natCast, h2]; simp,
      Real.rpow_neg (by norm_num), Real.rpow_natCast]
    push_cast; rfl

/-- `(10 ^ p) ^ (1 / (10 q)) = 10 ^ (L / 10)` for `L = p / q`. -/
private theorem ten_rpow_num_div (L : ℚ) :
    ((10 : ℝ) ^ (L.num : ℝ)) ^ (((10 * L.den : ℕ) : ℝ)⁻¹) = (10 : ℝ) ^ ((L : ℝ) / 10) := by
  rw [← Real.rpow_mul (by norm_num)]
  congr 1
  rw [Rat.cast_def]
  push_cast
  field_simp

private theorem pow_le_ten_rpow_iff {x : ℝ} {L : ℚ} (hx : 0 ≤ x) :
    x ^ (10 * L.den) ≤ (10 : ℝ) ^ (L.num : ℝ) ↔ x ≤ (10 : ℝ) ^ ((L : ℝ) / 10) := by
  have hN : (10 * L.den : ℕ) ≠ 0 := by positivity
  conv_rhs => rw [← ten_rpow_num_div, ← Real.pow_rpow_inv_natCast hx hN]
  exact (Real.rpow_le_rpow_iff (by positivity) (by positivity)
    (inv_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hN : (0 : ℝ) < ((10 * L.den : ℕ) : ℝ)))).symm

private theorem ten_rpow_le_pow_iff {x : ℝ} {L : ℚ} (hx : 0 ≤ x) :
    (10 : ℝ) ^ (L.num : ℝ) ≤ x ^ (10 * L.den) ↔ (10 : ℝ) ^ ((L : ℝ) / 10) ≤ x := by
  have hN : (10 * L.den : ℕ) ≠ 0 := by positivity
  conv_rhs => rw [← ten_rpow_num_div, ← Real.pow_rpow_inv_natCast hx hN]
  exact (Real.rpow_le_rpow_iff (by positivity) (by positivity)
    (inv_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hN : (0 : ℝ) < ((10 * L.den : ℕ) : ℝ)))).symm

/-- **`dbLe` decides** `0 ≤ x ≤ 10 ^ (L / 10)`. -/
theorem dbLe_eq_true_iff {x L : ℚ} :
    dbLe x L = true ↔ 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ (10 : ℝ) ^ ((L : ℝ) / 10) := by
  rw [Rat.cast_nonneg]
  simp only [dbLe, Bool.and_eq_true, decide_eq_true_eq]
  refine and_congr_right fun hx => ?_
  have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
  rw [← pow_le_ten_rpow_iff hx', ten_zpow_num]
  split_ifs with hL
  · rw [decide_eq_true_iff]
    constructor <;> intro h <;> exact_mod_cast h
  · have hpos : (0 : ℝ) < ((10 ^ (-L.num).toNat : ℚ) : ℝ) := by positivity
    rw [decide_eq_true_iff, ← one_div, le_div_iff₀ hpos]
    constructor <;> intro h <;> exact_mod_cast h

/-- **`dbGe` decides** `0 < x` and `10 ^ (L / 10) ≤ x`. -/
theorem dbGe_eq_true_iff {x L : ℚ} :
    dbGe x L = true ↔ 0 < (x : ℝ) ∧ (10 : ℝ) ^ ((L : ℝ) / 10) ≤ (x : ℝ) := by
  rw [Rat.cast_pos]
  simp only [dbGe, Bool.and_eq_true, decide_eq_true_eq]
  refine and_congr_right fun hx => ?_
  have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx.le
  rw [← ten_rpow_le_pow_iff hx', ten_zpow_num]
  split_ifs with hL
  · rw [decide_eq_true_iff]
    constructor <;> intro h <;> exact_mod_cast h
  · have hpos : (0 : ℝ) < ((10 ^ (-L.num).toNat : ℚ) : ℝ) := by positivity
    rw [decide_eq_true_iff, inv_le_iff_one_le_mul₀ hpos]
    constructor <;> intro h <;> exact_mod_cast h

namespace RatLTI

variable {n m p : ℕ} (G : RatLTI n m p)

private theorem sq_ten_rpow (L : ℝ) : ((10 : ℝ) ^ (L / 20)) ^ 2 = (10 : ℝ) ^ (L / 10) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  push_cast
  ring

/-- **Upper gain bound in decibels**: `‖H (ω * I) i j‖ ≤ 10 ^ (L / 20)`, that is
`20 log₁₀ ‖H (ω * I) i j‖ ≤ L` where the gain is nonzero, on the band, from `gainLe` with a
rational `γ²` accepted by `dbLe γ² L`. -/
theorem norm_le_db_of_gainLe {i : Fin p} {j : Fin m} {B : FreqBand} {γsq L : ℚ}
    (h : G.gainLe i j B γsq = true) (hdb : dbLe γsq L = true) {ω : ℝ} (hω : B.Mem ω) :
    ‖G.toSystem.transferFunction ((ω : ℂ) * I) i j‖ ≤ (10 : ℝ) ^ ((L : ℝ) / 20) := by
  have h1 := G.sq_norm_le_of_gainLe h hω
  have h2 := (dbLe_eq_true_iff.1 hdb).2
  rw [← sq_ten_rpow] at h2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (h1.trans h2)

/-- **Lower gain bound in decibels**: `10 ^ (L / 20) ≤ ‖H (ω * I) i j‖` on the band, from
`gainGe` with a rational `γ²` accepted by `dbGe γ² L`. -/
theorem rpow_le_norm_of_gainGe {i : Fin p} {j : Fin m} {B : FreqBand} {γsq L : ℚ}
    (h : G.gainGe i j B γsq = true) (hdb : dbGe γsq L = true) {ω : ℝ} (hω : B.Mem ω) :
    (10 : ℝ) ^ ((L : ℝ) / 20) ≤ ‖G.toSystem.transferFunction ((ω : ℂ) * I) i j‖ := by
  have h1 := G.le_sq_norm_of_gainGe h hω
  have h2 := (dbGe_eq_true_iff.1 hdb).2
  rw [← sq_ten_rpow] at h2
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 (h2.trans h1)

/-- **Lower gain bound in decibels**, logarithmic form: `L ≤ 20 log₁₀ ‖H (ω * I) i j‖`. -/
theorem db_le_of_gainGe {i : Fin p} {j : Fin m} {B : FreqBand} {γsq L : ℚ}
    (h : G.gainGe i j B γsq = true) (hdb : dbGe γsq L = true) {ω : ℝ} (hω : B.Mem ω) :
    (L : ℝ) ≤ 20 * Real.logb 10 ‖G.toSystem.transferFunction ((ω : ℂ) * I) i j‖ := by
  have h1 := G.rpow_le_norm_of_gainGe h hdb hω
  have hpos : 0 < ‖G.toSystem.transferFunction ((ω : ℂ) * I) i j‖ :=
    lt_of_lt_of_le (by positivity) h1
  have := (Real.le_logb_iff_rpow_le (by norm_num) hpos).2 h1
  linarith

/-! ### DC gain -/

/-- The rows of the DC gain `D + c₀⁻¹ C Y₀ B`, which is `D - C A⁻¹ B` when the resolvent is
accepted and `c₀ ≠ 0`. -/
@[expose] def dcGain : List (List ℚ) :=
  rowsMap₂ (fun d e => d + e / (resolvent n G.A).2.getD 0 0) p m G.D
    (rowsMul p n m G.C (rowsMul n n m ((resolvent n G.A).1.getD 0 []) G.B))

/-- **DC-gain check**: the resolvent check, and `c₀ = χ (0) ≠ 0`. -/
@[expose] def dcCheck : Bool := G.resolventOk && (resolvent n G.A).2.getD 0 0 != 0

/-- `-c₀⁻¹ Y₀`, the inverse of `A` for an accepted DC-gain check. -/
private abbrev invA : Matrix (Fin n) (Fin n) ℚ :=
  -((resolvent n G.A).2.getD 0 0)⁻¹ • ofLists n n ((resolvent n G.A).1.getD 0 [])

private theorem mul_invA (h : G.dcCheck = true) : ofLists n n G.A * G.invA = 1 := by
  simp only [dcCheck, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨hc, h0⟩ := h
  have hq : ofLists n n (prevRows (resolvent n G.A).1 0) -
      ofLists n n G.A * ofLists n n ((resolvent n G.A).1.getD 0 []) =
        (resolvent n G.A).2.getD 0 0 • 1 := coeff_identity_rat hc (Nat.succ_pos n)
  rw [prevRows, ofLists_nil, zero_sub] at hq
  rw [invA, mul_smul_comm, neg_smul, ← smul_neg, hq, smul_smul, inv_mul_cancel₀ h0, one_smul]

private theorem dcGain_rows :
    ofLists p n G.C * G.invA * ofLists n m G.B = ofLists p m G.D - ofLists p m G.dcGain := by
  ext i j
  simp only [dcGain, ofLists_rowsMap₂, ofLists_rowsMul, Matrix.sub_apply, of_apply, invA,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, Matrix.mul_assoc]
  ring

private theorem map_mul_invA {K : Type*} [Field K] [Algebra ℚ K] (h : G.dcCheck = true) :
    ratMat K n n G.A * G.invA.map (algebraMap ℚ K) = 1 := by
  have := congrArg (algebraMap ℚ K).mapMatrix (G.mul_invA h)
  rw [map_mul, map_one] at this
  exact this

private theorem map_dcGain {K : Type*} [Field K] [Algebra ℚ K] :
    ratMat K p m G.D - ratMat K p n G.C * G.invA.map (algebraMap ℚ K) * ratMat K n m G.B =
      ratMat K p m G.dcGain := by
  have := congrArg (·.map (algebraMap ℚ K)) G.dcGain_rows
  simp only [Matrix.map_mul, Matrix.map_sub _ (map_sub (algebraMap ℚ K))] at this
  rw [this, sub_sub_cancel]

private theorem ratMat_toSystem_A : G.toSystem.A = ratMat ℝ n n G.A := by
  ext; simp [toSystem, ratMat]

private theorem ratMat_toSystem_B : G.toSystem.B = ratMat ℝ n m G.B := by
  ext; simp [toSystem, ratMat]

private theorem ratMat_toSystem_C : G.toSystem.C = ratMat ℝ p n G.C := by
  ext; simp [toSystem, ratMat]

private theorem ratMat_toSystem_D : G.toSystem.D = ratMat ℝ p m G.D := by
  ext; simp [toSystem, ratMat]

/-- **The DC gain.** An accepted DC-gain check proves that `A` is invertible and that
`D - C A⁻¹ B` is the rational matrix `dcGain`, read over `ℝ`. -/
theorem dcGain_eq (h : G.dcCheck = true) :
    IsUnit G.toSystem.A ∧
      G.toSystem.D - G.toSystem.C * G.toSystem.A⁻¹ * G.toSystem.B =
        (ofLists p m G.dcGain).map ((↑) : ℚ → ℝ) := by
  have hm := G.map_mul_invA (K := ℝ) h
  rw [ratMat_toSystem_A, ratMat_toSystem_B, ratMat_toSystem_C, ratMat_toSystem_D,
    Matrix.inv_eq_right_inv hm, map_dcGain]
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hm), ?_⟩
  ext; simp [ratMat]

/-- **The transfer function at `s = 0`** is the DC gain: `H 0 = D - C A⁻¹ B`, computed exactly
over `ℚ`. -/
theorem transferFunction_zero_eq (h : G.dcCheck = true) :
    G.toSystem.transferFunction 0 = (ofLists p m G.dcGain).map ((↑) : ℚ → ℂ) := by
  have hm := G.map_mul_invA (K := ℂ) h
  have hinv : (-cplx n n G.A)⁻¹ = -G.invA.map (algebraMap ℚ ℂ) :=
    Matrix.inv_eq_right_inv (by rw [neg_mul_neg]; exact hm)
  rw [LTISystem.transferFunction, cplx_toSystem_A, cplx_toSystem_B, cplx_toSystem_C,
    cplx_toSystem_D, zero_smul, zero_sub, hinv, Matrix.mul_neg, Matrix.neg_mul, add_comm,
    ← sub_eq_add_neg, cplx, cplx, cplx, map_dcGain]
  ext; simp [ratMat]

end RatLTI

/-! ### Violation witnesses -/

namespace FreqBand

/-- Whether a rational frequency lies in the band. -/
@[expose] def memRat (B : FreqBand) (ω : ℚ) : Bool :=
  decide (B.lo ≤ |ω|) && B.hi.all fun b => decide (|ω| ≤ b)

private theorem mem_of_memRat {B : FreqBand} {ω : ℚ} (h : B.memRat ω = true) :
    B.Mem (ω : ℝ) := by
  simp only [memRat, Bool.and_eq_true, decide_eq_true_eq, Option.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [← Rat.cast_abs]; exact_mod_cast h1, fun b hb => ?_⟩
  rw [← Rat.cast_abs]
  exact_mod_cast (by simpa using h2 b hb)

end FreqBand

/-- The outcome of a gain check on a band: the specification is proved on the whole band, it is
violated at a stated rational frequency, or neither is established. -/
inductive GainVerdict
  /-- The specification holds on the whole band. -/
  | proved
  /-- The specification fails at the rational frequency `ω` of the band. -/
  | violated (ω : ℚ)
  /-- Neither a proof nor a violation was found. -/
  | inconclusive
  deriving @[expose] DecidableEq, Repr

namespace GainVerdict

variable {n m p : ℕ}

/-- What a verdict asserts about a specification `spec ω` of the frequency response of `G` on the
band `B`. `proved`: `spec` holds on the whole band. `violated ω`: `ω` is in the band,
`i ω I - A` is invertible (so `H (ω * I)` is the value of the transfer function, not a junk value
of the matrix inverse), and `spec` fails at `ω`. `inconclusive`: nothing. -/
@[expose] def Holds (v : GainVerdict) (G : RatLTI n m p) (B : FreqBand) (spec : ℝ → Prop) :
    Prop :=
  match v with
  | proved => ∀ ω, B.Mem ω → spec ω
  | violated ω => B.Mem ω ∧
      IsUnit ((((ω : ℝ) : ℂ) * I) • (1 : Matrix (Fin n) (Fin n) ℂ) -
        G.toSystem.A.map (algebraMap ℝ ℂ)) ∧ ¬ spec ω
  | inconclusive => True

/-- `proved` if the check `ok` accepts, otherwise `violated ω` for a found witness `ω`, otherwise
`inconclusive`. -/
@[expose] def ofCheck (ok : Bool) (w : Option ℚ) : GainVerdict :=
  if ok then proved else match w with
    | some ω => violated ω
    | none => inconclusive

end GainVerdict

/-- The coefficient list of `ω ↦ P (ω²)` from that of `P`. -/
@[expose] def spreadSq : List ℚ → List ℚ
  | [] => []
  | a :: l => a :: 0 :: spreadSq l

/-- Sign bisection of `[a, b]` for the polynomial with coefficient list `P`: while the values at the
ends have strictly opposite signs, keep the half on which they still do, for at most `fuel`
steps; the result is the final pair of ends. -/
@[expose] def bisectSign (P : List ℚ) : ℕ → ℚ → ℚ → List ℚ
  | 0, a, b => [a, b]
  | fuel + 1, a, b =>
    let m := (a + b) / 2
    let sm := Cslib.RealRoot.evalAt P m
    if Cslib.RealRoot.evalAt P a * sm < 0 then bisectSign P fuel a m
    else if sm * Cslib.RealRoot.evalAt P b < 0 then bisectSign P fuel m b
    else [a, b]

/-- **Candidate witnesses** (untrusted search). Rational frequencies at which to look for a
negative value of `P (ω²)` on the band `B`: the band's edges (for a half-line, a point beyond the
Cauchy bound of `P (ω²)`, past which its sign is constant), the ends inside the band of the
isolating intervals of the real roots of `P (ω²)` (`Cslib.RealRoot.isolateRoots`), each refined
by `32` steps of `bisectSign`, and the midpoints of consecutive such points. Between consecutive
roots `P (ω²)` has constant sign, so these points sample every sign of `P (ω²)` on the band, and
the refined ends lie close to the roots, which matters where the negative values are confined
near a pole of the gain. Nothing about the list is proved: every candidate is checked by
`RatLTI.pointOk`. -/
@[expose] def witnessCandidates (P : List ℚ) (B : FreqBand) : List ℚ :=
  let Pω := spreadSq P
  let lo := max B.lo 0
  let hi := B.hi.getD (max (lo + 1) (Cslib.RealRoot.cauchyBoundNat Pω))
  let ends := ((Cslib.RealRoot.isolateRoots Pω).flatMap fun I =>
    bisectSign Pω 32 I.lower I.upper).filter fun x => decide (lo < x ∧ x < hi)
  let pts := lo :: ends ++ [hi]
  lo :: hi :: List.zipWith (fun a b => (a + b) / 2) pts pts.tail ++ ends

namespace RatLTI

open Cslib.RealRoot

variable {n m p : ℕ} (G : RatLTI n m p)

/-- The squared gain `N (ω²) / Q (ω²)` at a rational frequency, computed in `ℚ`. -/
@[expose] def sqGainAt (i : Fin p) (j : Fin m) (ω : ℚ) : ℚ :=
  evalAt (G.gainNum i j) (ω * ω) / evalAt G.gainDen (ω * ω)

/-- **Witness-point check.** The resolvent check, `ω` in the band `B`, and `Q (ω²) ≠ 0`, so that
`i ω I - A` is invertible. -/
@[expose] def pointOk (B : FreqBand) (ω : ℚ) : Bool :=
  G.resolventOk && B.memRat ω && evalAt G.gainDen (ω * ω) != 0

private theorem aeval_sq_ratCast (cs : List ℚ) (ω : ℚ) :
    aeval ((ω : ℝ) ^ 2) (ofCoeffList cs) = ((evalAt cs (ω * ω) : ℚ) : ℝ) := by
  rw [show ((ω : ℝ)) ^ 2 = algebraMap ℚ ℝ (ω * ω) by
    rw [eq_ratCast, Rat.cast_mul, sq], aeval_algebraMap_apply,
    coe_aeval_eq_eval, eval_ofCoeffList]
  rfl

/-- **Soundness of the witness-point check.** At an accepted rational `ω`: `ω` is in the band,
`i ω I - A` is invertible, and `‖H (ω * I) i j‖² = sqGainAt i j ω` exactly. -/
theorem sq_norm_eq_sqGainAt {B : FreqBand} {ω : ℚ} (h : G.pointOk B ω = true) (i : Fin p)
    (j : Fin m) :
    B.Mem ω ∧ IsUnit ((((ω : ℝ) : ℂ) * I) • (1 : Matrix (Fin n) (Fin n) ℂ) -
        G.toSystem.A.map (algebraMap ℝ ℂ)) ∧
      ‖G.toSystem.transferFunction (((ω : ℝ) : ℂ) * I) i j‖ ^ 2 = G.sqGainAt i j ω := by
  simp only [pointOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hc, hB⟩, hQ⟩ := h
  have hQ' : aeval ((ω : ℝ) ^ 2) (ofCoeffList G.gainDen) ≠ 0 := by
    rw [aeval_sq_ratCast]; exact_mod_cast hQ
  have hU := (G.gainDen_ne_zero_iff hc ω).1 hQ'
  refine ⟨FreqBand.mem_of_memRat hB, hU, ?_⟩
  rw [G.sq_norm_transferFunction hc i j hU, aeval_sq_ratCast, aeval_sq_ratCast, sqGainAt,
    Rat.cast_div]

/-- The first candidate `ω` of `witnessCandidates P B` that passes `pointOk` and at which the
squared gain satisfies `bad`. -/
@[expose] def findWitness (i : Fin p) (j : Fin m) (P : List ℚ) (B : FreqBand)
    (bad : ℚ → Bool) : Option ℚ :=
  (witnessCandidates P B).find? fun ω => G.pointOk B ω && bad (G.sqGainAt i j ω)

/-- The common part of the verdict theorems: an accepting check proves the specification, and a
found witness violates it if `bad` at an accepted point refutes it. -/
private theorem holds_ofCheck {i : Fin p} {j : Fin m} {B : FreqBand} {ok : Bool} {P : List ℚ}
    {bad : ℚ → Bool} {spec : ℝ → Prop} (hok : ok = true → ∀ ω, B.Mem ω → spec ω)
    (hbad : ∀ ω : ℚ, G.pointOk B ω = true → bad (G.sqGainAt i j ω) = true → ¬ spec ω) :
    (GainVerdict.ofCheck ok (G.findWitness i j P B bad)).Holds G B spec := by
  unfold GainVerdict.ofCheck
  split_ifs with h
  · exact hok h
  · rcases hw : G.findWitness i j P B bad with _ | ω
    · trivial
    · have hf := List.find?_some hw
      simp only [Bool.and_eq_true] at hf
      obtain ⟨hB, hU, -⟩ := G.sq_norm_eq_sqGainAt hf.1 i j
      exact ⟨hB, hU, hbad ω hf.1 hf.2⟩

/-- **Upper gain verdict**: `gainLe`, or a rational `ω` in the band with `γ² < N (ω²) / Q (ω²)`,
searched where `γ² Q - N` is negative. -/
@[expose] def gainLeVerdict (i : Fin p) (j : Fin m) (B : FreqBand) (γsq : ℚ) : GainVerdict :=
  .ofCheck (G.gainLe i j B γsq) (G.findWitness i j
    (CoeffList.sub (CoeffList.smul γsq G.gainDen) (G.gainNum i j)) B fun g => decide (γsq < g))

/-- **Lower gain verdict**: `gainGe`, or a rational `ω` in the band with `N (ω²) / Q (ω²) < γ²`,
searched where `N - γ² Q` is negative. -/
@[expose] def gainGeVerdict (i : Fin p) (j : Fin m) (B : FreqBand) (γsq : ℚ) : GainVerdict :=
  .ofCheck (G.gainGe i j B γsq) (G.findWitness i j
    (CoeffList.sub (G.gainNum i j) (CoeffList.smul γsq G.gainDen)) B fun g => decide (g < γsq))

/-- **Upper decibel verdict** for the level `L`: `gainLe` with `γ²` and `dbLe γ² L`, or a
rational `ω` in the band whose squared gain `g` fails `dbLe g L`, that is `10 ^ (L / 10) < g`,
searched as in `gainLeVerdict`. -/
@[expose] def dbLeVerdict (i : Fin p) (j : Fin m) (B : FreqBand) (γsq L : ℚ) : GainVerdict :=
  .ofCheck (G.gainLe i j B γsq && dbLe γsq L) (G.findWitness i j
    (CoeffList.sub (CoeffList.smul γsq G.gainDen) (G.gainNum i j)) B fun g => !dbLe g L)

/-- **Lower decibel verdict** for the level `L`: `gainGe` with `γ²` and `dbGe γ² L`, or a
rational `ω` in the band whose squared gain `g > 0` fails `dbGe g L`, that is
`g < 10 ^ (L / 10)`, searched as in `gainGeVerdict`. -/
@[expose] def dbGeVerdict (i : Fin p) (j : Fin m) (B : FreqBand) (γsq L : ℚ) : GainVerdict :=
  .ofCheck (G.gainGe i j B γsq && dbGe γsq L) (G.findWitness i j
    (CoeffList.sub (G.gainNum i j) (CoeffList.smul γsq G.gainDen)) B
    fun g => decide (0 < g) && !dbGe g L)

/-- **The upper gain verdict is correct**: proved means `‖H (ω * I) i j‖² ≤ γ²` on the band;
`violated ω` means `γ² < ‖H (ω * I) i j‖²` at `ω` in the band, where `i ω I - A` is invertible. -/
theorem gainLeVerdict_holds (i : Fin p) (j : Fin m) (B : FreqBand) (γsq : ℚ) :
    (G.gainLeVerdict i j B γsq).Holds G B
      fun ω => ‖G.toSystem.transferFunction ((ω : ℂ) * I) i j‖ ^ 2 ≤ γsq :=
  G.holds_ofCheck (fun h _ hω => G.sq_norm_le_of_gainLe h hω) fun ω hω hg => by
    rw [(G.sq_norm_eq_sqGainAt hω i j).2.2, not_le]
    exact_mod_cast of_decide_eq_true hg

/-- **The lower gain verdict is correct**: proved means `γ² ≤ ‖H (ω * I) i j‖²` on the band;
`violated ω` means `‖H (ω * I) i j‖² < γ²` at `ω` in the band, where `i ω I - A` is invertible. -/
theorem gainGeVerdict_holds (i : Fin p) (j : Fin m) (B : FreqBand) (γsq : ℚ) :
    (G.gainGeVerdict i j B γsq).Holds G B
      fun ω => (γsq : ℝ) ≤ ‖G.toSystem.transferFunction ((ω : ℂ) * I) i j‖ ^ 2 :=
  G.holds_ofCheck (fun h _ hω => G.le_sq_norm_of_gainGe h hω) fun ω hω hg => by
    rw [(G.sq_norm_eq_sqGainAt hω i j).2.2, not_le]
    exact_mod_cast of_decide_eq_true hg

/-- **The upper decibel verdict is correct**: proved means `‖H (ω * I) i j‖ ≤ 10 ^ (L / 20)` on
the band; `violated ω` means `10 ^ (L / 20) < ‖H (ω * I) i j‖` at `ω` in the band, where
`i ω I - A` is invertible. -/
theorem dbLeVerdict_holds (i : Fin p) (j : Fin m) (B : FreqBand) (γsq L : ℚ) :
    (G.dbLeVerdict i j B γsq L).Holds G B
      fun ω => ‖G.toSystem.transferFunction ((ω : ℂ) * I) i j‖ ≤ (10 : ℝ) ^ ((L : ℝ) / 20) := by
  refine G.holds_ofCheck (fun h _ hω => ?_) fun ω hω hg hle => ?_
  · simp only [Bool.and_eq_true] at h
    exact G.norm_le_db_of_gainLe h.1 h.2 hω
  · have hsq := (G.sq_norm_eq_sqGainAt hω i j).2.2
    have hg' : dbLe (G.sqGainAt i j ω) L = false := by simpa using hg
    refine Bool.false_ne_true (hg' ▸ dbLe_eq_true_iff.2 ⟨hsq ▸ sq_nonneg _, ?_⟩)
    rw [← hsq, ← sq_ten_rpow]
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2

/-- **The lower decibel verdict is correct**: proved means `L ≤ 20 log₁₀ ‖H (ω * I) i j‖` on the
band; `violated ω` means that this fails at `ω` in the band, where `i ω I - A` is invertible and
the gain is nonzero, so that `‖H (ω * I) i j‖ < 10 ^ (L / 20)`. -/
theorem dbGeVerdict_holds (i : Fin p) (j : Fin m) (B : FreqBand) (γsq L : ℚ) :
    (G.dbGeVerdict i j B γsq L).Holds G B
      fun ω => (L : ℝ) ≤ 20 * Real.logb 10 ‖G.toSystem.transferFunction ((ω : ℂ) * I) i j‖ := by
  refine G.holds_ofCheck (fun h _ hω => ?_) fun ω hω hg hle => ?_
  · simp only [Bool.and_eq_true] at h
    exact G.db_le_of_gainGe h.1 h.2 hω
  · have hsq := (G.sq_norm_eq_sqGainAt hω i j).2.2
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hg
    obtain ⟨hpos, hg'⟩ := hg
    have hpos' : (0 : ℝ) < G.sqGainAt i j ω := by exact_mod_cast hpos
    have hH : 0 < ‖G.toSystem.transferFunction (((ω : ℝ) : ℂ) * I) i j‖ := by
      by_contra h0
      rw [not_lt, norm_le_zero_iff] at h0
      rw [h0, norm_zero] at hsq
      linarith [hsq ▸ hpos']
    have h1 := (Real.le_logb_iff_rpow_le (b := 10) (by norm_num) hH).1
      (show (L : ℝ) / 20 ≤ _ by linarith)
    refine Bool.false_ne_true (hg' ▸ dbGe_eq_true_iff.2 ⟨hpos', ?_⟩)
    rw [← hsq, ← sq_ten_rpow]
    exact pow_le_pow_left₀ (by positivity) h1 2

end RatLTI

end Cslib.LinearAlgebra
