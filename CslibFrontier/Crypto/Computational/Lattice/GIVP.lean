/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Generalized independent vectors and guaranteed distance decoding

The lattice problems used in the worst-case to average-case reductions of [MicciancioRegev2007]
(§2, p. 7; §5.2, p. 19), stated for a `ℤ`-submodule `L` of a real normed space in the same
single-lattice predicate style as `CslibFrontier/Crypto/Computational/Lattice/ShortestVector.lean`:

* `GIVP^φ_γ` ([MicciancioRegev2007], Definition 2.6, §2, p. 7): given a lattice `L`, find
  `n = rank L` linearly independent vectors of `L`, each of norm at most `γ · φ(L)`
  (`Cslib.Crypto.GIVP.IsSolution`). `SIVP_γ` in
  `CslibFrontier/Crypto/Computational/Lattice/ShortestVector.lean` is the specialization
  `φ(L) = λ_n(L)`.
* `GDD^φ_γ` ([MicciancioRegev2007], Definition 2.7, §2, p. 7): given a lattice `L` and a target
  point `t`, find a lattice point `x ∈ L` within distance `γ · φ(L)` of `t`
  (`Cslib.Crypto.GDD.IsSolution`).
* `IncGDD^φ_{γ, g}` ([MicciancioRegev2007], Definition 5.6, §5.2, p. 19): given a lattice `L`,
  a set `S` of `n = rank L` linearly independent vectors of `L`, a target point `t`, and a radius
  `r > γ · φ(L)` (`Cslib.Crypto.IncGDD.IsValidInstance`), find `x ∈ L` satisfying
  `‖x - t‖ ≤ ‖S‖ / g + r` (`Cslib.Crypto.IncGDD.IsSolution`), where `‖S‖` is Mathlib's canonical
  `Pi` supremum norm (`max_i ‖S i‖` in positive rank, `0` in rank `0`).

These are predicates on a single lattice (and target/radius). They fix no encoding of lattices or
targets and no running-time bound, so they state what an algorithm must output rather than that it
is efficient.

## Main definitions

* `Cslib.Crypto.GDD.IsSolution`: solutions of `GDD^φ_γ` ([MicciancioRegev2007], Definition 2.7).
* `Cslib.Crypto.GIVP.IsSolution`: solutions of `GIVP^φ_γ` ([MicciancioRegev2007], Definition 2.6).
* `Cslib.Crypto.IncGDD.IsValidInstance`: valid `(L, S, r)` instances of `IncGDD^φ_{γ, g}`
  ([MicciancioRegev2007], Definition 5.6).
* `Cslib.Crypto.IncGDD.IsSolution`: solutions of `IncGDD^φ_{γ, g}` ([MicciancioRegev2007],
  Definition 5.6).

## Main results

* `Cslib.Crypto.GDD.IsSolution.mono`: monotonicity of `GDD^φ_γ` solutions in `γ`.
* `Cslib.Crypto.GIVP.IsSolution.mono`: monotonicity of `GIVP^φ_γ` solutions in `γ`.
* `Cslib.Crypto.GIVP.IsSolution.of_param_le`: transferring `GIVP^φ_γ` solutions across a parameter
  comparison `φ L ≤ c · ψ L`.

## References

* [D. Micciancio and O. Regev, *Worst-Case to Average-Case Reductions Based on Gaussian
  Measures*][MicciancioRegev2007]
-/

public section

namespace Cslib.Crypto

open Module

section GDD

variable {E : Type*} [NormedAddCommGroup E]

/-- `x` solves guaranteed distance decoding `GDD^φ_γ` on `(L, t)`: `x` lies in `L` and satisfies
`‖x - t‖ ≤ γ · φ(L)` ([MicciancioRegev2007], Definition 2.7, §2, p. 7). -/
structure GDD.IsSolution (φ : Submodule ℤ E → ℝ) (γ : ℝ) (L : Submodule ℤ E) (t x : E) : Prop where
  /-- The solution is a vector of `L`. -/
  mem : x ∈ L
  /-- The solution is within distance `γ · φ(L)` of the target `t`. -/
  dist_le : ‖x - t‖ ≤ γ * φ L

/-- Enlarging the approximation factor `γ` preserves `GDD^φ_γ` solutions when `0 ≤ φ L`. -/
theorem GDD.IsSolution.mono {φ : Submodule ℤ E → ℝ} {γ γ' : ℝ} {L : Submodule ℤ E} {t x : E}
    (hx : GDD.IsSolution φ γ L t x) (hφ : 0 ≤ φ L) (hγ : γ ≤ γ') :
    GDD.IsSolution φ γ' L t x :=
  ⟨hx.mem, hx.dist_le.trans (mul_le_mul_of_nonneg_right hγ hφ)⟩

end GDD

section GIVP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `v` solves the generalized independent vectors problem `GIVP^φ_γ` on `L`: its `n = rank L`
vectors are linearly independent over `ℝ`, lie in `L`, and each have norm at most `γ · φ(L)`
([MicciancioRegev2007], Definition 2.6, §2, p. 7). The family is indexed by `Fin (finrank ℤ L)`,
so a solver cannot return fewer vectors than the rank; for a full-rank lattice `n` is the dimension
of the space (`ZLattice.rank`). For a discrete lattice in a finite-dimensional space `finrank ℤ L`
is its rank; on a `ℤ`-submodule that is not finitely generated `finrank ℤ L` is the junk value `0`,
so the predicate is meant for discrete lattices. -/
structure GIVP.IsSolution (φ : Submodule ℤ E → ℝ) (γ : ℝ) (L : Submodule ℤ E)
    (v : Fin (finrank ℤ L) → E) : Prop where
  /-- The vectors are linearly independent over `ℝ`. -/
  linearIndependent : LinearIndependent ℝ v
  /-- Every vector lies in `L`. -/
  mem : ∀ i, v i ∈ L
  /-- Every vector has norm at most `γ · φ(L)`. -/
  norm_le : ∀ i, ‖v i‖ ≤ γ * φ L

/-- Enlarging the approximation factor `γ` preserves `GIVP^φ_γ` solutions when `0 ≤ φ L`. -/
theorem GIVP.IsSolution.mono {φ : Submodule ℤ E → ℝ} {γ γ' : ℝ} {L : Submodule ℤ E}
    {v : Fin (finrank ℤ L) → E} (hv : GIVP.IsSolution φ γ L v) (hφ : 0 ≤ φ L) (hγ : γ ≤ γ') :
    GIVP.IsSolution φ γ' L v :=
  ⟨hv.linearIndependent, hv.mem, fun i => (hv.norm_le i).trans (mul_le_mul_of_nonneg_right hγ hφ)⟩

/-- Comparing lattice parameters `φ L ≤ c · ψ L` transfers any `GIVP^φ_γ` solution (for `γ ≥ 0`)
to a `GIVP^ψ_{γ · c}` solution. -/
theorem GIVP.IsSolution.of_param_le {φ ψ : Submodule ℤ E → ℝ} {γ c : ℝ} {L : Submodule ℤ E}
    {v : Fin (finrank ℤ L) → E} (hv : GIVP.IsSolution φ γ L v) (hγ : 0 ≤ γ)
    (hφψ : φ L ≤ c * ψ L) : GIVP.IsSolution ψ (γ * c) L v :=
  ⟨hv.linearIndependent, hv.mem, fun i => (hv.norm_le i).trans <| by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hφψ hγ⟩

/-- Validity of the `(L, S, r)` inputs of incremental guaranteed distance decoding
`IncGDD^φ_{γ, g}` ([MicciancioRegev2007], Definition 5.6, §5.2, p. 19): `S` is a family of
`n = rank L` linearly independent vectors of `L`, and the target radius satisfies `r > γ · φ(L)`.
Any target `t : E` pairs with `(L, S, r)` to form an `IncGDD` instance. -/
structure IncGDD.IsValidInstance (φ : Submodule ℤ E → ℝ) (γ : ℝ) (L : Submodule ℤ E)
    (S : Fin (finrank ℤ L) → E) (r : ℝ) : Prop where
  /-- The full-rank set `S` is linearly independent over `ℝ`. -/
  linearIndependent : LinearIndependent ℝ S
  /-- Every vector of `S` lies in `L`. -/
  mem : ∀ i, S i ∈ L
  /-- The radius strictly exceeds `γ · φ(L)`. -/
  radius_gt : γ * φ L < r

end GIVP

section IncGDD

variable {E : Type*} [NormedAddCommGroup E]

/-- `x` solves incremental guaranteed distance decoding `IncGDD^φ_{γ, g}` on `(L, S, t, r)`:
`x ∈ L` and `‖x - t‖ ≤ ‖S‖ / g + r` ([MicciancioRegev2007], Definition 5.6, §5.2, p. 19). Here
`‖S‖` is Mathlib's canonical `Pi` supremum norm (`Pi.norm_def`), which equals `max_i ‖S i‖` in
positive rank and `0` in rank `0`. -/
structure IncGDD.IsSolution (g : ℝ) (L : Submodule ℤ E) (S : Fin (finrank ℤ L) → E) (t : E)
    (r : ℝ) (x : E) : Prop where
  /-- The solution is a vector of `L`. -/
  mem : x ∈ L
  /-- The solution is within distance `‖S‖ / g + r` of the target `t`. -/
  dist_le : ‖x - t‖ ≤ ‖S‖ / g + r

end IncGDD

end Cslib.Crypto
