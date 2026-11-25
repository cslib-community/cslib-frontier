/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Rational.Certificates

/-!
# Rational hitting lists: the generator

The generator evaluates the polynomial lifts of the certificate pencils at every point of a
three-dimensional integer grid, keeps the points at which the normalizing matrix is invertible,
and emits the normalized rational matrix tuples. For every admissible nonzero formula with at most
`s` nodes, the certificate determinants are nonzero polynomials of bounded degree, so some grid
point avoids all their zeros; the tuple emitted there gives the formula a defined invertible value.
The parameters are polynomial in the number of variables and the node-count bound.

## Main definitions

* `Cslib.Circuits.Rational.Generator.matrixDimension`,
  `Cslib.Circuits.Rational.Generator.regular`, `Cslib.Circuits.Rational.Generator.grid`,
  `Cslib.Circuits.Rational.Generator.specializedLift`,
  `Cslib.Circuits.Rational.Generator.rationalLift`,
  `Cslib.Circuits.Rational.Generator.tupleAt`, `Cslib.Circuits.Rational.Generator.atPoint`,
  `Cslib.Circuits.Rational.Generator.output`: the regular representation, specialization grid,
  normalized tuple at a grid point, and list emitted for given parameters.
* `Cslib.Circuits.Rational.Parameters.w`, `Cslib.Circuits.Rational.Parameters.rankBound`,
  `Cslib.Circuits.Rational.Parameters.delta`, `Cslib.Circuits.Rational.Parameters.exponent`,
  `Cslib.Circuits.Rational.Parameters.ambientDimension`,
  `Cslib.Circuits.Rational.Parameters.truncation`,
  `Cslib.Circuits.Rational.Parameters.gridSize`: the parameters chosen for `n` variables and `s`
  nodes.
* `Cslib.Circuits.Rational.Generator.list`: the list with these parameters.

## Main results

* `Cslib.Circuits.Rational.Generator.output_hits`: the emitted list hits all formulas of bounded
  node count, once the parameters are large enough.
* `Cslib.Circuits.Rational.Generator.list_hits`,
  `Cslib.Circuits.Rational.Generator.list_dimension_bound`,
  `Cslib.Circuits.Rational.Generator.list_length_bound`: the list hits, with polynomially bounded
  dimension and length.

## References

* Adapted from OpenAI's formalization [OpenAI2026RationalHitting] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Computability/RationalHitting/Generator.lean), via the complexitylib port
  [Schlesinger2026RationalHitting] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.Circuits

namespace Rational.Generator
open Matrix MvPolynomial
open scoped BigOperators
noncomputable section

/-- Dimension after expanding the cyclotomic matrix representation over the rationals. -/
def matrixDimension (e : ℕ) : ℕ := CyclotomicRing.dimension e * CyclotomicRing.degree e

/-- Entrywise regular representation, flattening and fixed row-major reindexing. -/
def regular (e : ℕ) :
    Matrix (ZMod (CyclotomicRing.dimension e)) (ZMod (CyclotomicRing.dimension e))
      (CyclotomicRing.R e) →+* Mat (matrixDimension e) :=
  (Matrix.reindexRingEquiv ℚ
    ((Equiv.prodCongr (ZMod.finEquiv (CyclotomicRing.dimension e)).symm.toEquiv
      (Equiv.refl (Fin (CyclotomicRing.degree e)))).trans finProdFinEquiv)).toRingHom.comp
    ((Matrix.compRingEquiv _ _ ℚ).toRingHom.comp (CyclotomicRing.rho e).toRingHom.mapMatrix)

/-- The fixed lexicographic three-dimensional integer grid, encoded by Fin H. -/
def grid (H : ℕ) : List (Fin 3 → Fin H) :=
  (List.finRange H).flatMap fun t => (List.finRange H).flatMap fun p =>
    (List.finRange H).map fun r => ![t, p, r]

/-- Every point `x : Fin 3 → Fin H` belongs to `grid H`. -/
lemma mem_grid (H : ℕ) (x : Fin 3 → Fin H) : x ∈ grid H := by
  simp only [grid, List.mem_flatMap, List.mem_map]
  refine ⟨x 0, by simp, x 1, by simp, x 2, by simp, ?_⟩
  funext i
  fin_cases i <;> rfl

private lemma grid_length (H : ℕ) : (grid H).length = H ^ 3 := by
  simp [grid, List.length_flatMap, pow_succ, Nat.mul_assoc]

/-- The polynomial lift is evaluated over the exact rational quotient. -/
def specializedLift (n N e : ℕ) (x : Fin 3 → ℕ) (i : Fin (n + 1)) :
    Matrix (ZMod (CyclotomicRing.dimension e)) (ZMod (CyclotomicRing.dimension e))
      (CyclotomicRing.R e) :=
  (eval₂Hom (RingHom.id _) (fun j => (x j : CyclotomicRing.R e))).mapMatrix
    (PencilCertificates.lifts (CyclotomicRing.character e) N n i)

/-- Expand a specialized lift as a rational matrix. -/
def rationalLift (n N e : ℕ) (x : Fin 3 → ℕ) (i : Fin (n + 1)) : Mat (matrixDimension e) :=
  regular e (specializedLift n N e x i)

/-- Normalize all variable matrices by the zeroth matrix. -/
def tupleAt (n N e : ℕ) (x : Fin 3 → ℕ) : Tuple n (matrixDimension e) :=
  fun i => (rationalLift n N e x 0)⁻¹ * rationalLift n N e x i.succ

/-- The filtering step tests only the zeroth lifted matrix, and receives no formula. -/
def atPoint (n N e : ℕ) (x : Fin 3 → ℕ) : Option (Tuple n (matrixDimension e)) :=
  if (rationalLift n N e x 0).det = 0 then none else some (tupleAt n N e x)

/-- Collect the normalized tuples emitted at all grid points. -/
def output (n N e H : ℕ) : Output n where
  dimension := matrixDimension e
  dimension_pos := Nat.mul_pos (CyclotomicRing.dimension_pos e) (CyclotomicRing.degree_pos e)
  tuples := (grid H).filterMap (fun x => atPoint n N e (fun i => (x i).val + 1))

private lemma length_output_le (n N e H : ℕ) : (output n N e H).tuples.length ≤ H ^ 3 :=
  (List.length_filterMap_le _ _).trans_eq (grid_length H)

/-- The actual emitted rational normalization is the homomorphic image of the
quotient normalization. Consequently every original inverse occurrence is kept. -/
private lemma transfer {n N e : ℕ} (x : Fin 3 → ℕ) (f : Formula n)
    (z : (Matrix (ZMod (CyclotomicRing.dimension e)) (ZMod (CyclotomicRing.dimension e))
      (CyclotomicRing.R e))ˣ)
    (hz : (z : Matrix _ _ _) = specializedLift n N e x 0)
    (v : Matrix (ZMod (CyclotomicRing.dimension e)) (ZMod (CyclotomicRing.dimension e))
      (CyclotomicRing.R e))
    (hf : f.Eval (algebraMap ℚ _)
      (fun i => (↑z⁻¹ : Matrix _ _ _) * specializedLift n N e x i.succ) v)
    (hu : IsUnit v) :
    ∃ a, Evaluates f (tupleAt n N e x) a ∧ IsUnit a := by
  have hzinv : regular e (↑z⁻¹ : Matrix _ _ _) = (rationalLift n N e x 0)⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    change regular e (↑z⁻¹ : Matrix _ _ _) * regular e (specializedLift n N e x 0) = 1
    simp only [← map_mul, ← hz, Units.inv_mul, map_one]
  refine ⟨regular e v, ?_, hu.map (regular e)⟩
  change f.Eval (algebraMap ℚ _) (tupleAt n N e x) (regular e v)
  change f.Eval (algebraMap ℚ _)
    (fun i => (regular e (specializedLift n N e x 0))⁻¹ * regular e
      (specializedLift n N e x i.succ)) (regular e v)
  simpa only [map_mul, hzinv, rationalLift] using hf.map_algebraMap (regular e)

private lemma emitted {n N e H : ℕ} (x : Fin 3 → Fin H)
    (hz : IsUnit (specializedLift n N e (fun i => (x i).val + 1) 0)) :
    tupleAt n N e (fun i => (x i).val + 1) ∈ (output n N e H).tuples :=
  have hne : (rationalLift n N e (fun i => (x i).val + 1) 0).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (hz.map (regular e))).ne_zero
  List.mem_filterMap.mpr ⟨x, mem_grid H x, by simp [atPoint, hne]⟩

end
end Rational.Generator

namespace Rational.Generator
open Matrix MvPolynomial
open scoped BigOperators Rational.PolynomialHahn
noncomputable section

/-- The Hahn field containing the algebraic witnesses for the generator. -/
private abbrev WitnessField := HahnSeries QuantumLift.Exponents ℂ

/-- Embed the cyclotomic field into the Hahn witness field. -/
private def witnessEmbedding (e : ℕ) : CyclotomicRing.R e →+* WitnessField :=
  (HahnSeries.C : ℂ →+* WitnessField).comp (CyclotomicRing.intoComplex e).toRingHom

/-- Reindex the formula's pencil by its explicit finite dimension. -/
private def finPencil {n : ℕ} (f : Formula n) :
    Matrix (Fin (Fintype.card f.Index)) (Fin (Fintype.card f.Index)) (Affine.Form n) :=
  (Formula.pencil f).reindex (Fintype.equivFin f.Index) (Fintype.equivFin f.Index)

private lemma finPencil_unit {n : ℕ} {R : Type*} [Ring R] (c : ℚ →+* R)
    (X : Fin n → R) (f : Formula n) :
    IsUnit ((finPencil f).map (Affine.eval c X)) ↔ IsUnit (Formula.realized c X f) := by
  let E := Matrix.reindexRingEquiv R (Fintype.equivFin f.Index)
  change IsUnit (E (Formula.realized c X f)) ↔ IsUnit (Formula.realized c X f)
  exact ⟨fun h => by simpa [E] using h.map E.symm, fun h => h.map E⟩

/-- A one-by-one constant pencil used to enforce normalization. -/
private def onePencil (n : ℕ) :
    Matrix (Fin 1) (Fin 1) (Affine.Form n) := fun _ _ => Affine.constant 1

/-- Determinant polynomials whose simultaneous nonvanishing certifies a hit. -/
private def conditions {n : ℕ} (N e : ℕ) (f : Formula n) :
    List (MvPolynomial (Fin 3) (CyclotomicRing.R e)) :=
  PencilCertificates.determinant (CyclotomicRing.character e) N (onePencil n) ::
    f.certificates.map fun h =>
      PencilCertificates.determinant (CyclotomicRing.character e) N (finPencil h)

private lemma condition_nonzero {n s N e : ℕ} (hs : 1 ≤ s) (f : Formula n) (hf : f.nodeCount ≤ s)
    (hnz : Nonzero f)
    (hN : 1 ≤ N) (hMN : CyclotomicRing.dimension e = N + 2 * (n + 1) ^ 3 * (2 * s + 1))
    (hM : (2 * s + 1) * (2 * (n + 1) ^ 3 * (2 * s + 1)) < CyclotomicRing.dimension e) :
    ∀ p ∈ conditions N e f, p ≠ 0 := by
  obtain ⟨d, hd, W, a, ha, ha0⟩ := hnz
  obtain ⟨X, v, hv, hvu⟩ := formula_invertible_witness hd f W a ha ha0
  let C : WitnessField →+* LaurentReduction.F WitnessField := HahnSeries.C
  let Y : Fin n → Matrix (Fin d) (Fin d) (LaurentReduction.F WitnessField) := fun i =>
    C.mapMatrix (X i)
  have hcert : ∀ h ∈ f.certificates, IsUnit (Formula.realized (algebraMap ℚ _) Y h) :=
    (Formula.certificates_iff (algebraMap ℚ _) Y f).mpr
      ⟨_, hv.map_algebraMap C.mapMatrix, hvu.map C.mapMatrix⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · apply PencilCertificates.determinant_ne_zero (CyclotomicRing.character e)
      (CyclotomicRing.character_primitive e) (witnessEmbedding e) (onePencil n)
      (2 * s + 1) 1 (by omega) (by omega) hN hMN hM (by omega) (fun _ => 0)
    convert isUnit_one
    ext i j
    simp [onePencil, Affine.eval_constant, Matrix.one_apply, Subsingleton.elim i j]
  · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
    have hb := (Formula.certificate_bounds f s hs hf).2 h hh
    apply PencilCertificates.determinant_ne_zero (CyclotomicRing.character e)
      (CyclotomicRing.character_primitive e) (witnessEmbedding e) (finPencil h)
      (2 * s + 1) d hb.1 hb.2 hN hMN hM hd Y
    exact (finPencil_unit _ _ h).mpr (hcert h hh)

private lemma condition_degree {n s N e : ℕ} (hs : 1 ≤ s) (f : Formula n) (hf : f.nodeCount ≤ s) :
    (conditions N e f).length ≤ s + 2 ∧
    ∀ p ∈ conditions N e f, p.totalDegree ≤ 3 * (2 * s + 1) * (CyclotomicRing.dimension e) ^ 2 := by
  refine ⟨?_, ?_⟩
  · have hh := (Formula.certificate_bounds f s hs hf).1
    simpa only [conditions, List.length_cons, List.length_map] using Nat.succ_le_succ hh
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact (PencilCertificates.degree_le _ _).trans (by gcongr; omega)
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
      exact (PencilCertificates.degree_le _ _).trans (by
        gcongr
        exact ((Formula.certificate_bounds f s hs hf).2 h hh).2)

lemma integer_grid {K : Type*} [Field K] [CharZero K] (P : List (MvPolynomial (Fin 3) K))
    (hP : ∀ p ∈ P, p ≠ 0) (d H : ℕ) (hd : ∀ p ∈ P, p.totalDegree ≤ d)
    (hH : P.length * d < H) :
    ∃ x : Fin 3 → Fin H, ∀ p ∈ P, eval (fun i => (((x i).val + 1 : ℕ) : K)) p ≠ 0 := by
  classical
  let S : Finset K := (Finset.range H).image (fun i => ((i + 1 : ℕ) : K))
  have hS : S.card = H := by
    rw [Finset.card_image_of_injective _ fun _ _ h => Nat.add_right_cancel (Nat.cast_injective h),
      Finset.card_range]
  obtain ⟨x, hx, hxp⟩ := FiniteGrid.simultaneous P hP d hd S (hS ▸ hH)
  choose y hy using fun i => Finset.mem_image.mp (hx i)
  exact ⟨fun i => ⟨y i, Finset.mem_range.mp (hy i).1⟩,
    fun p hp => (funext fun i => (hy i).2) ▸ hxp p hp⟩

private lemma specialized_unit {K : Type*} [Field K] [CharZero K] {n q M N : ℕ} [NeZero M]
    (χ : AddChar (ZMod M) K) (L : Matrix (Fin q) (Fin q) (Affine.Form n)) (x : Fin 3 → K)
    (hx : eval x (PencilCertificates.determinant χ N L) ≠ 0) :
    IsUnit (L.map (Affine.homogeneous (algebraMap ℚ _) (fun i =>
      (eval₂Hom (RingHom.id K) x).mapMatrix (PencilCertificates.lifts χ N n i)))) := by
  have hd : IsUnit ((eval₂Hom (RingHom.id K) x).mapMatrix (PencilCertificates.polynomial χ N L)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (by rwa [← RingHom.map_det]))
  rw [PencilCertificates.specialized] at hd
  simpa using hd.map (Matrix.compRingEquiv (Fin q) (ZMod M) K).symm

private lemma onePencil_unit {K : Type*} [Field K] [CharZero K] {n : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι] (rationalLift : Fin (n + 1) → Matrix ι ι K)
    (h : IsUnit ((onePencil n).map (Affine.homogeneous (algebraMap ℚ _) rationalLift))) : IsUnit
      (rationalLift 0) := by
  have hh : IsUnit ((Matrix.uniqueRingEquiv (m := Fin 1) (A := Matrix ι ι K))
      ((onePencil n).map (Affine.homogeneous (algebraMap ℚ _) rationalLift))) :=
    h.map (Matrix.uniqueRingEquiv (m := Fin 1) (A := Matrix ι ι K)).toRingHom
  simpa [Matrix.uniqueRingEquiv, onePencil, Affine.homogeneous, Affine.coeff, Affine.constant,
    Fin.sum_univ_succ] using hh

/-- The finite formula-independent list hits every admissible nonzero formula
at a defined and invertible original-tree value. -/
theorem output_hits {n s N e H : ℕ} (hs : 1 ≤ s)
    (hN : 1 ≤ N) (hMN : CyclotomicRing.dimension e = N + 2 * (n + 1) ^ 3 * (2 * s + 1))
    (hM : (2 * s + 1) * (2 * (n + 1) ^ 3 * (2 * s + 1)) < CyclotomicRing.dimension e)
    (hH : (s + 2) * (3 * (2 * s + 1) * (CyclotomicRing.dimension e) ^ 2) < H) :
    Hits s (output n N e H) := by
  intro f hf _ha hnz
  have hb := condition_degree hs f hf (N := N) (e := e)
  obtain ⟨x, hx⟩ := integer_grid (conditions N e f)
    (condition_nonzero hs f hf hnz hN hMN hM) _ H hb.2 (lt_of_le_of_lt (Nat.mul_le_mul_right _
      hb.1) hH)
  let t : Fin 3 → ℕ := fun i => (x i).val + 1
  let Zr := specializedLift n N e t
  obtain ⟨z, hz'⟩ : IsUnit (Zr 0) :=
    onePencil_unit Zr (specialized_unit _ _ _ (hx _ (List.mem_cons_self ..)))
  obtain ⟨v, hv, hu⟩ := (Formula.certificates_iff _ _ f).mp fun h hh =>
    (finPencil_unit _ _ h).mp <| Affine.normalized_pencil_unit (finPencil h) Zr z hz' <|
      specialized_unit _ _ _ (hx _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨h, hh, rfl⟩)))
  obtain ⟨a, ha, hua⟩ := transfer t f z hz' v hv hu
  exact ⟨tupleAt n N e t, emitted x ⟨z, hz'⟩, a, ha, hua⟩

end
end Rational.Generator

namespace Rational.Parameters

/-- The number `n + 1` of matrices in a lifted tuple: one per variable, and the normalizing
matrix. -/
def w (n : ℕ) := n + 1
/-- Rank parameter for formulas of the given node count. -/
def rankBound (s : ℕ) := 2 * s + 1
/-- Dimension allowance in the rank expansion argument. -/
def delta (n s : ℕ) := 2 * (w n) ^ 3 * rankBound s
/-- Binary logarithm used to choose the next cyclotomic dimension. -/
def exponent (n s : ℕ) := Nat.log 2 (rankBound s * delta n s)
/-- The least power of two strictly above the rank expansion threshold. -/
def ambientDimension (n s : ℕ) := 2 ^ (exponent n s + 1)
/-- Number of retained columns after the dimension allowance. -/
def truncation (n s : ℕ) := ambientDimension n s-delta n s
/-- Side length of the integer grid used for specialization. -/
def gridSize (n s : ℕ) := 1 + 3 * (s + 2) * rankBound s * (ambientDimension n s) ^ 3

/-- The rank-expansion threshold `rankBound s * delta n s` is positive. -/
theorem threshold_pos (n s : ℕ) : 0 < rankBound s * delta n s := by
  simp only [rankBound, delta, w]
  positivity

private theorem threshold_lt (n s : ℕ) : rankBound s * delta n s < ambientDimension n s :=
  Nat.lt_pow_succ_log_self (by omega) _

private theorem M_le (n s : ℕ) : ambientDimension n s ≤ 2 * (rankBound s * delta n s) := by
  have h := Nat.pow_log_le_self 2 (threshold_pos n s).ne'
  unfold ambientDimension exponent at *
  rw [pow_succ]; omega

/-- `ambientDimension n s` is at most any power of two strictly above
`rankBound s * delta n s`. -/
theorem M_minimal (n s k : ℕ) (hk : rankBound s * delta n s < 2 ^ k) :
    ambientDimension n s ≤ 2 ^ k := by
  apply Nat.pow_le_pow_right (by omega)
  exact Nat.succ_le_of_lt (Nat.log_lt_of_lt_pow (threshold_pos n s).ne' hk)

/-- The truncation parameter `truncation n s` is at least `1`. -/
theorem N_pos (n s : ℕ) : 1 ≤ truncation n s := by
  have hh := threshold_lt n s
  have hd : delta n s ≤ rankBound s * delta n s := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  unfold truncation
  omega

private theorem M_eq (n s : ℕ) : ambientDimension n s = truncation n s + delta n s := by
  have hh := N_pos n s
  unfold truncation at *
  omega

private theorem grid_large (n s : ℕ) :
    (s + 2) * (3 * rankBound s * (ambientDimension n s) ^ 2) < gridSize n s := by
  have hpow : (ambientDimension n s) ^ 2 ≤ (ambientDimension n s) ^ 3 :=
    Nat.pow_le_pow_right (Nat.one_le_two_pow) (by omega)
  unfold gridSize
  nlinarith [Nat.mul_le_mul_left (3 * (s + 2) * rankBound s) hpow]

private theorem w_bound (n s : ℕ) : w n ≤ n + s + 1 := by unfold w; omega

private theorem B_bound (n s : ℕ) : rankBound s ≤ 2 * (n + s + 1) := by unfold rankBound; omega

private theorem delta_bound (n s : ℕ) : delta n s ≤ 4 * (n + s + 1) ^ 4 := by
  calc delta n s ≤ 2 * (n + s + 1) ^ 3 * (2 * (n + s + 1)) := by
         unfold delta
         gcongr
         · exact w_bound n s
         · exact B_bound n s
       _ = _ := by ring

/-- `ambientDimension n s` is at most `16 * (n + s + 1) ^ 5`. -/
theorem polynomial_M (n s : ℕ) : ambientDimension n s ≤ 16 * (n + s + 1) ^ 5 := by
  calc ambientDimension n s ≤ 2 * (rankBound s * delta n s) := M_le n s
       _ ≤ 2 * ((2 * (n + s + 1)) * (4 * (n + s + 1) ^ 4)) := by
          gcongr
          · exact B_bound n s
          · exact delta_bound n s
       _ = _ := by ring

/-- The grid side length is polynomial in `n + s + 1`, for every `n`, including `n = 0`: the
factor `s + 2` is bounded by `2 * (n + s + 1)`. -/
theorem polynomial_H (n s : ℕ) : gridSize n s ≤ 49153 * (n + s + 1) ^ 17 := by
  have hp : 1 ≤ (n + s + 1) ^ 17 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hs : s + 2 ≤ 2 * (n + s + 1) := by omega
  calc gridSize n s ≤
        1 + 3 * (2 * (n + s + 1)) * (2 * (n + s + 1)) * (16 * (n + s + 1) ^ 5) ^ 3 := by
         unfold gridSize
         have hB := B_bound n s
         have hM := polynomial_M n s
         gcongr
       _ = 1 + 49152 * (n + s + 1) ^ 17 := by ring
       _ ≤ _ := by omega

end Rational.Parameters

namespace Rational.Generator
noncomputable section

/-- The list with all parameters fixed by `n` and `s`. -/
def list (n s : ℕ) : Output n :=
  output n (Parameters.truncation n s) (Parameters.exponent n s) (Parameters.gridSize n s)

/-- When `1 ≤ s`, `list n s` hits all admissible nonzero formulas of node count at most `s`. -/
theorem list_hits (n s : ℕ) (hs : 1 ≤ s) : Hits s (list n s) := by
  exact output_hits hs (Parameters.N_pos n s) (Parameters.M_eq n s) (Parameters.threshold_lt n s)
    (Parameters.grid_large n s)

/-- The matrix dimension of `list n s` is at most `256 * (n + s + 1) ^ 10`. -/
theorem list_dimension_bound (n s : ℕ) : (list n s).dimension ≤ 256 * (n + s + 1) ^ 10 := by
  have hd : CyclotomicRing.degree (Parameters.exponent n s) ≤ Parameters.ambientDimension n s := by
    grind [CyclotomicRing.degree, Parameters.ambientDimension]
  change Parameters.ambientDimension n s * CyclotomicRing.degree (Parameters.exponent n s) ≤ _
  calc _ ≤ (16 * (n + s + 1) ^ 5) * (16 * (n + s + 1) ^ 5) :=
             Nat.mul_le_mul (Parameters.polynomial_M n s) (hd.trans (Parameters.polynomial_M n s))
       _ = _ := by ring

/-- The number of tuples in `list n s` is at most `49153 ^ 3 * (n + s + 1) ^ 51`. -/
theorem list_length_bound (n s : ℕ) :
    (list n s).tuples.length ≤ 49153 ^ 3 * (n + s + 1) ^ 51 := by
  calc _ ≤ (Parameters.gridSize n s) ^ 3 := length_output_le ..
       _ ≤ (49153 * (n + s + 1) ^ 17) ^ 3 := Nat.pow_le_pow_left (Parameters.polynomial_H n s) 3
       _ = _ := by rw [mul_pow, ← pow_mul]

/-- The algebraic hitting property and the polynomial list-cardinality bound. -/
theorem algebraic_generator : ∃ G : (n s : ℕ) → Output n,
    ∀ n s, 1 ≤ s →
      (G n s).dimension ≤ 256 * (n + s + 1) ^ 10 ∧
      (G n s).tuples.length ≤ 49153 ^ 3 * (n + s + 1) ^ 51 ∧ Hits s (G n s) := by
  exact ⟨list, fun n s hs =>
    ⟨list_dimension_bound n s, list_length_bound n s, list_hits n s hs⟩⟩

end
end Rational.Generator

end Cslib.Circuits
