/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.LatticeReduction.Reduced
public import CslibFrontier.Crypto.Computational.Lattice.GIVP
public import CslibFrontier.Foundations.Analysis.Lattice.Minimum

/-!
# Shortest-vector problems

The worst-case lattice problems behind lattice-based cryptography, stated for a `ℤ`-submodule `L`
of a real normed space with first minimum `λ₁(L)` (`ZLattice.minimum`) and successive minima
`λ_k(L)` (`ZLattice.successiveMinimum`), following [MicciancioGoldwasser2002], Chapter 1:

* search `SVP_γ`: find a nonzero `v ∈ L` with `‖v‖ ≤ γ · λ₁(L)` (`Cslib.Crypto.SVP.IsSolution`);
* the promise problem `GapSVP_γ`: on input `(L, d)`, accept when `λ₁(L) ≤ d` and reject when
  `γ · d < λ₁(L)` (`Cslib.Crypto.GapSVP.IsCorrect`);
* `SIVP_γ`: find `n = rank L` linearly independent vectors of `L`, each of norm at most
  `γ · λ_n(L)` (`Cslib.Crypto.SIVP.IsSolution`, the `φ(L) = λ_n(L)` specialization of
  `Cslib.Crypto.GIVP.IsSolution`); the number of vectors is fixed by `L`, not chosen by the
  solver;
* Hermite `HSVP_γ` in `EuclideanSpace ℝ ι`, `n = |ι|`: find a nonzero `v ∈ L` with
  `‖v‖ ≤ γ · det(L)^{1/n}` (`Cslib.Crypto.HSVP.IsSolution`).

These are predicates on a single lattice. They fix no encoding of lattices as inputs and no
running-time bound, so they state what an algorithm must output, not that it is efficient.

On a discrete nonzero lattice in a proper space an exact solution of `SVP_1` exists, and `SVP_γ`
has solutions only for `γ ≥ 1`. Comparing the norm of an `SVP_γ` solution with `γ · d` decides
`GapSVP_γ` on `(L, d)` (`Cslib.Crypto.GapSVP.isCorrect_decideOfSVP`), the standard reduction
from the decision problem to the search problem. The first vector of a `3/4`-reduced family
`b : Fin (n + 1) → E` solves `SVP_γ` with `γ = (√2)ⁿ` on the integer span of `b`
(`Cslib.Crypto.SVP.isSolution_of_isReduced`), by Proposition (1.11) of [LenstraLenstraLovasz1982].
By Minkowski's bound `λ₁(L) ≤ √n · det(L)^{1/n}`, every `SVP_γ` solution in `EuclideanSpace ℝ ι`
solves `HSVP_{γ√n}` (`Cslib.Crypto.SVP.IsSolution.hsvp`).

## Main definitions

* `Cslib.Crypto.SVP.IsSolution`: solutions of search `SVP_γ`.
* `Cslib.Crypto.GapSVP.IsYes`, `Cslib.Crypto.GapSVP.IsNo`: the promise sets of `GapSVP_γ`.
* `Cslib.Crypto.GapSVP.IsCorrect`: correct answers for `GapSVP_γ`.
* `Cslib.Crypto.GapSVP.decideOfSVP`: the decision rule of the reduction to `SVP_γ`.
* `Cslib.Crypto.SIVP.IsSolution`: solutions of `SIVP_γ`.
* `Cslib.Crypto.HSVP.IsSolution`: solutions of Hermite `HSVP_γ`.

## Main results

* `Cslib.Crypto.SVP.exists_isSolution_one`: an exact shortest vector exists.
* `Cslib.Crypto.SVP.IsSolution.one_le`, `Cslib.Crypto.SIVP.IsSolution.one_le`: approximation
  factors below `1` have no solutions.
* `Cslib.Crypto.GapSVP.not_isYes_and_isNo`: for `γ ≥ 1` the promise sets are disjoint.
* `Cslib.Crypto.GapSVP.isCorrect_decideOfSVP`: `GapSVP_γ` reduces to `SVP_γ`.
* `Cslib.Crypto.SVP.isSolution_of_isReduced`: reduced bases solve `SVP_{(√2)ⁿ}`.
* `Cslib.Crypto.SVP.IsSolution.hsvp`: `SVP_γ` solutions solve `HSVP_{γ√n}`.

## References

* [D. Micciancio and S. Goldwasser, *Complexity of Lattice Problems: A Cryptographic
  Perspective*][MicciancioGoldwasser2002]
* [A. K. Lenstra, H. W. Lenstra Jr. and L. Lovász, *Factoring polynomials with rational
  coefficients*][LenstraLenstraLovasz1982]
-/

public section

namespace Cslib.Crypto

open ZLattice Module

section Normed

variable {E : Type*} [NormedAddCommGroup E]

/-- `v` solves search `SVP_γ` on `L`: it is a nonzero vector of `L` with `‖v‖ ≤ γ · λ₁(L)`. -/
structure SVP.IsSolution (γ : ℝ) (L : Submodule ℤ E) (v : E) : Prop where
  /-- The solution is a vector of `L`. -/
  mem : v ∈ L
  /-- The solution is nonzero. -/
  ne_zero : v ≠ 0
  /-- The solution is within the factor `γ` of the first minimum: `‖v‖ ≤ γ · λ₁(L)`. -/
  norm_le : ‖v‖ ≤ γ * minimum L

/-- A YES instance `(L, d)` of `GapSVP_γ`: `λ₁(L) ≤ d`. -/
def GapSVP.IsYes (L : Submodule ℤ E) (d : ℝ) : Prop :=
  minimum L ≤ d

/-- A NO instance `(L, d)` of `GapSVP_γ`: `γ · d < λ₁(L)`. -/
def GapSVP.IsNo (γ : ℝ) (L : Submodule ℤ E) (d : ℝ) : Prop :=
  γ * d < minimum L

/-- The answer `b` is correct for `GapSVP_γ` on `(L, d)`: it accepts YES instances and rejects
NO instances. Any answer is correct outside the promise. -/
def GapSVP.IsCorrect (γ : ℝ) (L : Submodule ℤ E) (d : ℝ) (b : Bool) : Prop :=
  (GapSVP.IsYes L d → b = true) ∧ (GapSVP.IsNo γ L d → b = false)

/-- The decision rule of the reduction from `GapSVP_γ` to `SVP_γ`: accept `(L, d)` when the
vector `v` returned for `L` has norm at most `γ · d`. -/
noncomputable def GapSVP.decideOfSVP (γ d : ℝ) (v : E) : Bool :=
  decide (‖v‖ ≤ γ * d)

theorem SVP.IsSolution.mono {γ γ' : ℝ} {L : Submodule ℤ E} {v : E} (hv : SVP.IsSolution γ L v)
    (hγ : γ ≤ γ') : SVP.IsSolution γ' L v :=
  ⟨hv.mem, hv.ne_zero, hv.norm_le.trans (mul_le_mul_of_nonneg_right hγ (minimum_nonneg L))⟩

/-- For `γ ≥ 1` no instance of `GapSVP_γ` is both a YES and a NO instance. -/
theorem GapSVP.not_isYes_and_isNo {γ : ℝ} (hγ : 1 ≤ γ) (L : Submodule ℤ E) (d : ℝ) :
    ¬ (GapSVP.IsYes L d ∧ GapSVP.IsNo γ L d) := by
  rintro ⟨hy, hn⟩
  unfold GapSVP.IsYes at hy
  unfold GapSVP.IsNo at hn
  nlinarith [minimum_nonneg L, mul_nonneg (by linarith : (0 : ℝ) ≤ γ) (sub_nonneg.2 hy)]

/-- The reduction from `GapSVP_γ` to `SVP_γ`: for `γ ≥ 0`, comparing the norm of an `SVP_γ`
solution with `γ · d` answers `GapSVP_γ` correctly on `(L, d)`. -/
theorem GapSVP.isCorrect_decideOfSVP {γ : ℝ} (hγ : 0 ≤ γ) {L : Submodule ℤ E} {v : E}
    (hv : SVP.IsSolution γ L v) (d : ℝ) : GapSVP.IsCorrect γ L d (GapSVP.decideOfSVP γ d v) :=
  ⟨fun hy => decide_eq_true (hv.norm_le.trans (mul_le_mul_of_nonneg_left hy hγ)),
    fun hn => decide_eq_false (not_le.2 (hn.trans_le (minimum_le_norm hv.mem hv.ne_zero)))⟩

variable [ProperSpace E]

/-- A discrete nonzero lattice in a proper space has an exact `SVP_1` solution. -/
theorem SVP.exists_isSolution_one {L : Submodule ℤ E} [DiscreteTopology L] (hL : L ≠ ⊥) :
    ∃ v, SVP.IsSolution 1 L v := by
  obtain ⟨v, hv, hv0, hvm⟩ := exists_norm_eq_minimum hL
  exact ⟨v, hv, hv0, by rw [one_mul, hvm]⟩

/-- On a discrete lattice, `SVP_γ` has solutions only for `γ ≥ 1`. -/
theorem SVP.IsSolution.one_le {γ : ℝ} {L : Submodule ℤ E} [DiscreteTopology L] {v : E}
    (hv : SVP.IsSolution γ L v) : 1 ≤ γ := by
  have hL : L ≠ ⊥ := (Submodule.ne_bot_iff L).2 ⟨v, hv.mem, hv.ne_zero⟩
  have hpos := minimum_pos hL
  have h := (minimum_le_norm hv.mem hv.ne_zero).trans hv.norm_le
  by_contra hγ
  nlinarith

end Normed

section SIVP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `v` solves `SIVP_γ` on `L`: the `φ(L) = λ_n(L)` (`ZLattice.successiveMinimum L (finrank ℤ L)`)
specialization of `GIVP.IsSolution`, asking for `n = rank L` linearly independent vectors of `L`,
each of norm at most `γ · λ_n(L)`. -/
noncomputable abbrev SIVP.IsSolution (γ : ℝ) (L : Submodule ℤ E)
    (v : Fin (finrank ℤ L) → E) : Prop :=
  GIVP.IsSolution (fun L => successiveMinimum L (finrank ℤ L)) γ L v

/-- Enlarging the approximation factor `γ` preserves `SIVP_γ` solutions. -/
theorem SIVP.IsSolution.mono {γ γ' : ℝ} {L : Submodule ℤ E} {v : Fin (finrank ℤ L) → E}
    (hv : SIVP.IsSolution γ L v) (hγ : γ ≤ γ') : SIVP.IsSolution γ' L v :=
  GIVP.IsSolution.mono hv (successiveMinimum_nonneg L _) hγ

/-- On a full-rank discrete lattice of positive dimension `n` in a finite-dimensional space,
`SIVP_γ` has solutions only for `γ ≥ 1`. -/
theorem SIVP.IsSolution.one_le [FiniteDimensional ℝ E] [ProperSpace E] {γ : ℝ}
    {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] {v : Fin (finrank ℤ L) → E}
    (hv : SIVP.IsSolution γ L v) (hn : 0 < finrank ℝ E) : 1 ≤ γ := by
  have hrank : finrank ℤ L = finrank ℝ E := ZLattice.rank ℝ L
  have hn' : 1 ≤ finrank ℤ L := by omega
  let i₀ : Fin (finrank ℤ L) := ⟨0, hn'⟩
  have hL : L ≠ ⊥ :=
    (Submodule.ne_bot_iff L).2 ⟨v i₀, hv.mem i₀, hv.linearIndependent.ne_zero i₀⟩
  have hle := successiveMinimum_le_of_linearIndependent hv.linearIndependent hv.mem
    ((norm_nonneg _).trans (hv.norm_le i₀)) hv.norm_le
  have := (minimum_pos hL).trans_le (minimum_le_successiveMinimum L hL hn' hrank.le)
  by_contra
  nlinarith

end SIVP

section LLL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The first vector of a `3/4`-reduced family `b : Fin (n + 1) → E` with `b₀ ≠ 0` solves
`SVP_γ` with `γ = (√2)ⁿ` on the integer span of `b` ([LenstraLenstraLovasz1982],
Proposition (1.11)). -/
theorem SVP.isSolution_of_isReduced {b : Fin (n + 1) → E}
    (hb : Algorithms.LatticeReduction.IsReduced (3 / 4) b) (hb0 : b 0 ≠ 0) :
    SVP.IsSolution (Real.sqrt 2 ^ n) (Submodule.span ℤ (Set.range b)) (b 0) := by
  have hmem : b 0 ∈ Submodule.span ℤ (Set.range b) := Submodule.subset_span ⟨0, rfl⟩
  have hL : Submodule.span ℤ (Set.range b) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).2 ⟨b 0, hmem, hb0⟩
  have hpos : 0 < Real.sqrt 2 ^ n := by positivity
  exact ⟨hmem, hb0, (div_le_iff₀' hpos).1 <| (le_minimum_iff hL).2 fun _ hx hx0 =>
    (div_le_iff₀' hpos).2 (hb.norm_le_sqrt_two_pow_mul hx hx0)⟩

end LLL

section Hermite

variable {ι : Type*} [Fintype ι]

/-- `v` solves Hermite `HSVP_γ` on a lattice `L` in `EuclideanSpace ℝ ι`, `n = |ι|`: it is a
nonzero vector of `L` with `‖v‖ ≤ γ · det(L)^{1/n}`. The predicate carries no full-rank or
discreteness assumption, and `covolume L` has its meaning as the lattice determinant only for
full-rank discrete lattices (`[DiscreteTopology L] [IsZLattice ℝ L]`), which is where the
predicate should be read. -/
structure HSVP.IsSolution (γ : ℝ) (L : Submodule ℤ (EuclideanSpace ℝ ι))
    (v : EuclideanSpace ℝ ι) : Prop where
  /-- The solution is a vector of `L`. -/
  mem : v ∈ L
  /-- The solution is nonzero. -/
  ne_zero : v ≠ 0
  /-- The solution is within the factor `γ` of the root determinant: `‖v‖ ≤ γ · det(L)^{1/n}`. -/
  norm_le : ‖v‖ ≤ γ * covolume L ^ ((Fintype.card ι : ℝ)⁻¹)

/-- By Minkowski's bound `λ₁(L) ≤ √n · det(L)^{1/n}`, an `SVP_γ` solution with `γ ≥ 0` on a
full-rank lattice in `EuclideanSpace ℝ ι`, `n = |ι| ≥ 1`, solves `HSVP_{γ√n}`. -/
theorem SVP.IsSolution.hsvp [Nonempty ι] {γ : ℝ} (hγ : 0 ≤ γ)
    {L : Submodule ℤ (EuclideanSpace ℝ ι)} [DiscreteTopology L] [IsZLattice ℝ L]
    {v : EuclideanSpace ℝ ι} (hv : SVP.IsSolution γ L v) :
    HSVP.IsSolution (γ * Real.sqrt (Fintype.card ι)) L v := by
  refine ⟨hv.mem, hv.ne_zero, hv.norm_le.trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (minimum_le_sqrt_mul_covolume_rpow L) hγ

end Hermite

end Cslib.Crypto
