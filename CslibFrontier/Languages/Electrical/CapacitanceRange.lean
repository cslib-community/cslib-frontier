/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Electrical.NetlistCertificate
import Mathlib.Data.List.GetD

/-!
# Certified stability of a circuit for every capacitance in an interval

The checker `Cslib.Electrical.Text.NetlistCert.check` certifies a circuit with fixed element
values. This module certifies the circuits obtained from one netlist by giving one capacitor every
capacitance `C` in an interval `[lo, hi]` (`Cslib.Electrical.Netlist.setCapacitance`), with a
decay rate `α` that does not depend on `C`.

## The generalized Lyapunov inequality

A structured decoupling (`Cslib.LinearAlgebra.SparseDecouplingCert`) reduces the modified nodal
equations to `E₁₁ ẋ = Â x` with `Â = F₁₁ - F₁₂ K`, and the reduced state matrix is
`A = E₁₁⁻¹ Â`. A capacitance `C` enters only `E`, as `E + (C - C₀) ΔE` with the stamp `ΔE` of
the capacitor (`Cslib.Electrical.Netlist.capacitanceRows`), and when the transforms of the
decoupling map `ΔE` into the differential block (`T ΔE U = [[Δ₁₁, 0], [0, 0]]`, checked), the
same transforms decouple every value
(`Cslib.LinearAlgebra.SparseDecouplingCert.exists_decoupling_of_add`), with
`E₁₁ (C) = E₁₁ + (C - C₀) Δ₁₁` and the same `Â`. So `A (C)` depends on `C` through `E₁₁ (C)⁻¹`,
and a check of `A (C)` at the ends of an interval says nothing about its inside.

The energy `V = (E₁₁ x)ᵀ Q (E₁₁ x)`, a quadratic form in the charges and fluxes `E₁₁ x` with a
fixed `Q ≻ 0`, decays at the rate `α` along `E₁₁ ẋ = Â x` when the *generalized Lyapunov
residual*

  `R (E₁₁) = -(Âᵀ Q E₁₁ + (Âᵀ Q E₁₁)ᵀ + 2 α E₁₁ᵀ Q E₁₁)`

is positive definite (`Matrix.genLyapunovResidual`). Then `E₁₁` is invertible and `A = E₁₁⁻¹ Â`
satisfies `Aᵀ P + P A + 2 α P = -R ⪯ 0` for `P = E₁₁ᵀ Q E₁₁ ≻ 0`
(`Matrix.exists_norm_le_exp_of_genLyapunovResidual`). For a fixed `Q` the residual is concave
in `E₁₁` along a line: `R (E₀ + c Δ)` is a combination of its values at `a` and `b` with
nonnegative weights, plus `2 α (c - a) (b - c) Δᵀ Q Δ ⪰ 0`, so positivity at the two ends of
`[a, b]` gives positivity on all of it (`Matrix.posDef_genLyapunovResidual_of_mem_Icc`). This
is the generalized (descriptor) Lyapunov inequality in the reduced coordinates, with the
Lyapunov matrix taken in the coordinates `E₁₁ x`, where it can be held fixed; the parameter is
fixed but unknown (frozen), not varying in time.

## The certificate

`Cslib.Electrical.CapacitanceRangeCert` holds a structured decoupling of the nominal netlist, its
operating point, the branch of the capacitor, the blocks `E₁₁` and `Δ₁₁`, the rate `α`, the
interval `[lo, hi]` and a cover of it by consecutive intervals, each with its own `Q`. The checker
recomputes everything else in exact rational arithmetic; the positivity of `Q` and of the two
residuals of each interval is checked on factorizations that the kernel computes itself
(`Cslib.LinearAlgebra.LDLCert.checkPosDefComputed`).

## Main definitions

* `Cslib.Electrical.Netlist.setCapacitance`, `Cslib.Electrical.Netlist.capacitanceRows`.
* `Matrix.genLyapunovResidual`.
* `Cslib.Electrical.CapacitanceRangeCert`, `CapacitanceRangeCert.check`,
  `CapacitanceRangeCert.Guarantee`, `Cslib.Electrical.Text.checkTextRange`.

## Main results

* `Matrix.posDef_genLyapunovResidual_of_mem_Icc`,
  `Matrix.exists_norm_le_exp_of_genLyapunovResidual`.
* `Cslib.Electrical.CapacitanceRangeCert.guarantee_of_check`: for every capacitance in
  `[lo, hi]`, the circuit is exponentially stable at the rate `α`.
* `Cslib.Electrical.Text.exists_parse_of_checkTextRange`: the same, for the netlist read from a
  text.
-/

public section

open Set Matrix Mathlib.Tactic.Matrix Cslib.LinearAlgebra

namespace Matrix

variable {n : Type*} [Fintype n]

/-- The residual `-(Âᵀ Q E + (Âᵀ Q E)ᵀ + 2 α Eᵀ Q E)` of the generalized Lyapunov inequality of
`E ẋ = Â x` for the energy `(E x)ᵀ Q (E x)` and the rate `α`. -/
def genLyapunovResidual {R : Type*} [CommRing R] (Â Q E : Matrix n n R) (α : R) :
    Matrix n n R :=
  -(Âᵀ * Q * E + (Âᵀ * Q * E)ᵀ + (2 * α) • (Eᵀ * Q * E))

theorem genLyapunovResidual_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (Â Q E : Matrix n n R) (α : R) :
    (genLyapunovResidual Â Q E α).map f =
      genLyapunovResidual (Â.map f) (Q.map f) (E.map f) (f α) := by
  simp only [genLyapunovResidual, Matrix.map_neg _ (map_neg f), Matrix.map_add _ (map_add f),
    Matrix.map_mul, Matrix.transpose_map, Matrix.map_smul' _ _ _ (map_mul f), map_mul, map_ofNat]

/-- The residual along `E₀ + c Δ` is concave in `c`: an identity for `a ≤ c ≤ b`. -/
private theorem genLyapunovResidual_combination (Â Q E₀ Δ : Matrix n n ℝ) (α a b c : ℝ) :
    (b - a) • genLyapunovResidual Â Q (E₀ + c • Δ) α =
      (b - c) • genLyapunovResidual Â Q (E₀ + a • Δ) α +
        (c - a) • genLyapunovResidual Â Q (E₀ + b • Δ) α +
          (2 * α * (c - a) * (b - c) * (b - a)) • (Δᵀ * Q * Δ) := by
  simp only [genLyapunovResidual, transpose_add, transpose_smul, transpose_mul, Matrix.add_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, transpose_transpose, smul_add, smul_neg,
    smul_smul]
  module

/-- **The generalized Lyapunov inequality on a segment.** For a fixed `Q ⪰ 0` and `α ≥ 0`, if
the residual is positive definite at `E₀ + a Δ` and at `E₀ + b Δ`, it is positive definite at
`E₀ + c Δ` for every `c ∈ [a, b]`. -/
theorem posDef_genLyapunovResidual_of_mem_Icc {Â Q E₀ Δ : Matrix n n ℝ} {α a b c : ℝ}
    (hQ : Q.PosSemidef) (hα : 0 ≤ α) (hc : c ∈ Icc a b)
    (ha : (genLyapunovResidual Â Q (E₀ + a • Δ) α).PosDef)
    (hb : (genLyapunovResidual Â Q (E₀ + b • Δ) α).PosDef) :
    (genLyapunovResidual Â Q (E₀ + c • Δ) α).PosDef := by
  obtain ⟨hac, hcb⟩ := hc
  rcases eq_or_lt_of_le hcb with rfl | hcb'
  · exact hb
  have hba : 0 < b - a := by linarith
  have hD : (Δᵀ * Q * Δ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hQ.conjTranspose_mul_mul_same Δ
  have hw : 0 ≤ 2 * α * (c - a) * (b - c) * (b - a) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hα) (sub_nonneg.2 hac))
      (sub_nonneg.2 hcb)) hba.le
  have hsum : ((b - c) • genLyapunovResidual Â Q (E₀ + a • Δ) α +
      (c - a) • genLyapunovResidual Â Q (E₀ + b • Δ) α +
        (2 * α * (c - a) * (b - c) * (b - a)) • (Δᵀ * Q * Δ)).PosDef :=
    ((ha.smul (by linarith)).add_posSemidef (hb.posSemidef.smul (by linarith))).add_posSemidef
      (hD.smul hw)
  rw [← genLyapunovResidual_combination] at hsum
  simpa [smul_smul, inv_mul_cancel₀ hba.ne'] using hsum.smul (inv_pos.2 hba)

variable [DecidableEq n]

/-- **The generalized Lyapunov criterion.** If `Q ≻ 0` and the residual
`-(Âᵀ Q E + (Âᵀ Q E)ᵀ + 2 α Eᵀ Q E)` is positive definite, then `E` is invertible, and every
trajectory of `ẋ = E⁻¹ Â x` on `[0, ∞)` satisfies `‖x t‖ ≤ M exp (-α t) ‖x 0‖` in the Euclidean
norm, for a constant `M`: with `P = Eᵀ Q E ≻ 0`, `Aᵀ P + P A + 2 α P` is minus the residual. -/
theorem exists_norm_le_exp_of_genLyapunovResidual {Â Q E : Matrix n n ℝ} {α : ℝ}
    (hQ : Q.PosDef) (hR : (genLyapunovResidual Â Q E α).PosDef) :
    IsUnit E.det ∧ ∃ M : ℝ, ∀ x : ℝ → EuclideanSpace ℝ n,
      (toEuclideanCLM (𝕜 := ℝ) (E⁻¹ * Â)).IsTrajectoryOn x (Ici 0) →
        ∀ t ≥ 0, ‖x t‖ ≤ M * Real.exp (-(α * t)) * ‖x 0‖ := by
  have hQt : Qᵀ = Q := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hQ.isHermitian.eq
  have hE : IsUnit E.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv, hEv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hpos := hR.dotProduct_mulVec_pos hv
    have h1 : (Âᵀ * Q * E) *ᵥ v = 0 := by rw [← mulVec_mulVec, hEv, mulVec_zero]
    have h2 : v ⬝ᵥ (Âᵀ * Q * E)ᵀ *ᵥ v = 0 := by
      rw [dotProduct_mulVec, vecMul_transpose, h1, zero_dotProduct]
    have h3 : (Eᵀ * Q * E) *ᵥ v = 0 := by rw [← mulVec_mulVec, hEv, mulVec_zero]
    simp only [genLyapunovResidual, star_trivial, neg_mulVec, add_mulVec, smul_mulVec, h1, h3,
      dotProduct_neg, h2, zero_add, smul_zero, add_zero, neg_zero, lt_irrefl] at hpos
  refine ⟨hE, ?_⟩
  have hinj : Function.Injective E.mulVec := by
    intro v w hvw
    have := congrArg (fun u => E⁻¹ *ᵥ u) hvw
    simpa [mulVec_mulVec, nonsing_inv_mul _ hE] using this
  have hP : (Eᵀ * Q * E).PosDef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hQ.conjTranspose_mul_mul_same hinj
  refine exists_norm_le_exp_toEuclideanCLM_of_posDef hP (α := α) ?_
  have hEE : (E⁻¹)ᵀ * Eᵀ = 1 := by rw [← transpose_mul, mul_nonsing_inv _ hE, transpose_one]
  have hAP : (E⁻¹ * Â)ᵀ * (Eᵀ * Q * E) = Âᵀ * Q * E :=
    calc (E⁻¹ * Â)ᵀ * (Eᵀ * Q * E) = Âᵀ * ((E⁻¹)ᵀ * Eᵀ) * Q * E := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = Âᵀ * Q * E := by rw [hEE, Matrix.mul_one]
  have hPA : Eᵀ * Q * E * (E⁻¹ * Â) = (Âᵀ * Q * E)ᵀ :=
    calc Eᵀ * Q * E * (E⁻¹ * Â) = Eᵀ * Q * (E * E⁻¹) * Â := by simp only [Matrix.mul_assoc]
      _ = (Âᵀ * Q * E)ᵀ := by
          rw [mul_nonsing_inv _ hE, Matrix.mul_one]
          simp only [transpose_mul, transpose_transpose, hQt, Matrix.mul_assoc]
  rw [hAP, hPA]
  exact hR.posSemidef

end Matrix

namespace Cslib.Electrical

namespace Netlist

variable (c : Netlist)

/-- The capacitance of branch `b`, if it is a capacitor. -/
@[expose] def capacitance? (b : ℕ) : Option ℚ :=
  match (c.branch b).elem with
  | .capacitor C => some C
  | _ => none

/-- The netlist with the element of branch `b` replaced by a capacitor of capacitance `C`
between the same terminals. -/
@[expose] def setCapacitance (b : ℕ) (C : ℚ) : Netlist :=
  { c with branches := c.branches.set b { c.branch b with elem := .capacitor C } }

/-- The sparse rows of the stamp `∂E/∂C` of the capacitance of branch `b`: the voltage row of
the branch, in row `nodes + b`. -/
@[expose] def capacitanceRows (b : ℕ) : List (List (ℕ × ℚ)) :=
  List.replicate (c.nodes + b) [] ++ [vSparse c.nodes (c.branch b).pos (c.branch b).neg]

variable {c} {b : ℕ} {C C₀ : ℚ}

@[simp] theorem nodes_setCapacitance : (c.setCapacitance b C).nodes = c.nodes := rfl

@[simp] theorem size_setCapacitance : (c.setCapacitance b C).size = c.size := by
  simp [setCapacitance, size]

private theorem branch_setCapacitance (hb : b < c.branches.length) (i : ℕ) :
    (c.setCapacitance b C).branch i =
      if i = b then { c.branch b with elem := .capacitor C } else c.branch i := by
  by_cases hi : i = b
  · subst hi
    simp only [branch, setCapacitance, List.getD_eq_getElem?_getD, List.getElem?_set_self hb,
      Option.getD_some, ite_true]
  · simp only [hi, ↓reduceIte]
    simp only [branch, setCapacitance, List.getD_eq_getElem?_getD,
      List.getElem?_set_ne (Ne.symm hi)]

private theorem elem_of_capacitance? (h : c.capacitance? b = some C₀) :
    (c.branch b).elem = .capacitor C₀ := by
  unfold capacitance? at h
  split at h <;> simp_all

theorem check_setCapacitance (hc : c.check = true) (hb : b < c.branches.length)
    (hC : 0 < C) : (c.setCapacitance b C).check = true := by
  have hmem : c.branch b ∈ c.branches := by
    simp [branch, List.getD_eq_getElem?_getD, hb]
  simp only [check, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc ⊢
  intro br hbr
  rcases List.mem_or_eq_of_mem_set hbr with h | rfl
  · exact hc br h
  · obtain ⟨⟨h₁, h₂⟩, -⟩ := hc _ hmem
    exact ⟨⟨h₁, h₂⟩, by simpa [Element.check] using hC⟩

private theorem eEntry_setCapacitance (hb : b < c.branches.length)
    (h : c.capacitance? b = some C₀) (r j : ℕ) :
    (c.setCapacitance b C).eEntry r j = c.eEntry r j +
      (C - C₀) * (if r = c.nodes + b then vrow c.nodes (c.branch b).pos (c.branch b).neg j
        else 0) := by
  have he := elem_of_capacitance? h
  simp only [eEntry, nodes_setCapacitance, branch_setCapacitance hb]
  by_cases h₁ : r < c.nodes
  · simp [h₁, show r ≠ c.nodes + b by omega]
  · by_cases h₂ : r = c.nodes + b
    · subst h₂
      simp [he, Element.stamp]
      ring
    · have : r - c.nodes ≠ b := by omega
      simp [h₁, h₂, this]

private theorem fEntry_setCapacitance (hb : b < c.branches.length)
    (h : c.capacitance? b = some C₀) (r j : ℕ) :
    (c.setCapacitance b C).fEntry r j = c.fEntry r j := by
  have he := elem_of_capacitance? h
  simp only [fEntry, nodes_setCapacitance]
  by_cases h₁ : r < c.nodes
  · simp only [h₁, ↓reduceIte]
    by_cases hj : j - c.nodes = b
    · simp [branch_setCapacitance hb, hj, Branch.incidence]
    · simp [branch_setCapacitance hb, hj]
  · simp only [h₁, ↓reduceIte]
    by_cases hr : r - c.nodes = b
    · simp [branch_setCapacitance hb, hr, he, Element.stamp]
    · simp [branch_setCapacitance hb, hr]

theorem bList_setCapacitance (hb : b < c.branches.length)
    (h : c.capacitance? b = some C₀) : (c.setCapacitance b C).bList = c.bList := by
  have he := elem_of_capacitance? h
  simp only [bList, size_setCapacitance]
  refine List.map_congr_left fun r _ => ?_
  simp only [bEntry, nodes_setCapacitance]
  by_cases h₁ : r < c.nodes
  · simp only [h₁, ↓reduceIte]
  · simp only [h₁, ↓reduceIte]
    by_cases hr : r - c.nodes = b
    · simp [branch_setCapacitance hb, hr, he, Element.stamp]
    · simp [branch_setCapacitance hb, hr]

theorem length_capacitanceRows (hb : b < c.branches.length) :
    (c.capacitanceRows b).length ≤ c.size := by
  simp [capacitanceRows, size]; omega

private theorem sparseGet_capacitanceRows (r j : ℕ) :
    sparseGet ((c.capacitanceRows b).getD r []) j =
      if r = c.nodes + b then vrow c.nodes (c.branch b).pos (c.branch b).neg j else 0 := by
  rcases Nat.lt_trichotomy r (c.nodes + b) with h | rfl | h
  · rw [capacitanceRows, List.getD_append _ _ _ _ (by simpa using h)]
    simp only [show r ≠ c.nodes + b by omega, ↓reduceIte]
    simp [List.getD_eq_getElem?_getD, h]
  · simp only [↓reduceIte]
    rw [capacitanceRows, List.getD_append_right _ _ _ _ (by simp)]
    simp [sparseGet_vSparse]
  · simp only [show r ≠ c.nodes + b by omega, ↓reduceIte]
    rw [capacitanceRows, List.getD_eq_default _ _ (by simp; omega)]
    rfl

/-- The sparse rows of `E` of `c.setCapacitance b C` read as those of `c` plus `C - C₀` times
the stamp `capacitanceRows`. -/
theorem ofSparse_eSparse_setCapacitance (hb : b < c.branches.length)
    (h : c.capacitance? b = some C₀) :
    ofSparse c.size c.size (c.setCapacitance b C).eSparse =
      ofSparse c.size c.size c.eSparse +
        (C - C₀) • ofSparse c.size c.size (c.capacitanceRows b) := by
  ext i j
  have hi : (i : ℕ) < (c.setCapacitance b C).size := by simp
  simp only [Matrix.add_apply, Matrix.smul_apply, ofSparse_apply, smul_eq_mul,
    sparseGet_eSparse hi, sparseGet_eSparse i.is_lt, sparseGet_capacitanceRows,
    eEntry_setCapacitance hb h]

/-- The sparse rows of `F` of `c.setCapacitance b C` read as those of `c`. -/
theorem ofSparse_fSparse_setCapacitance (hb : b < c.branches.length)
    (h : c.capacitance? b = some C₀) :
    ofSparse c.size c.size (c.setCapacitance b C).fSparse = ofSparse c.size c.size c.fSparse := by
  ext i j
  have hi : (i : ℕ) < (c.setCapacitance b C).size := by simp
  have hj : (j : ℕ) < (c.setCapacitance b C).size := by simp
  simp only [ofSparse_apply, sparseGet_fSparse hi hj, sparseGet_fSparse i.is_lt j.is_lt,
    fEntry_setCapacitance hb h]

end Netlist

/-! ### The certificate -/

/-- One interval `[lo, hi]` of a cover, with its Lyapunov matrix `Q` in the coordinates
`E₁₁ x`. -/
structure CapacitanceInterval where
  /-- The lower end. -/
  lo : ℚ
  /-- The upper end. -/
  hi : ℚ
  /-- The rows of the Lyapunov matrix. -/
  Q : List (List ℚ)

/-- Whether consecutive intervals `ps` cover `[a, b]`: the first starts at `a`, each starts where
the previous one ends, and the last ends at `b`. -/
@[expose] def coversIcc : ℚ → ℚ → List CapacitanceInterval → Bool
  | _, _, [] => false
  | a, b, p :: ps => p.lo == a && match ps with
    | [] => p.hi == b
    | _ :: _ => coversIcc p.hi b ps

theorem exists_mem_of_coversIcc :
    ∀ {a b : ℚ} {ps : List CapacitanceInterval}, coversIcc a b ps = true → ∀ {C : ℚ},
      a ≤ C → C ≤ b → ∃ p ∈ ps, p.lo ≤ C ∧ C ≤ p.hi
  | _, _, [], h, _, _, _ => absurd h Bool.false_ne_true
  | a, b, p :: ps, h, C, haC, hCb => by
    simp only [coversIcc, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hlo, h⟩ := h
    rcases ps with _ | ⟨q, qs⟩
    · simp only [beq_iff_eq] at h
      exact ⟨p, List.mem_singleton_self p, hlo ▸ haC, h ▸ hCb⟩
    · rcases le_or_gt C p.hi with hC | hC
      · exact ⟨p, List.mem_cons_self .., hlo ▸ haC, hC⟩
      · obtain ⟨r, hr, h'⟩ := exists_mem_of_coversIcc h hC.le hCb
        exact ⟨r, List.mem_cons_of_mem _ hr, h'⟩

/-- The rows of `-(Âᵀ Q E + (Âᵀ Q E)ᵀ + 2 α Eᵀ Q E)` (`Matrix.genLyapunovResidual`) for the
`n × n` matrices with rows `Â`, `Q` and `E`. -/
@[expose] def genLyapunovResidualRows (n : ℕ) (Â Q E : List (List ℚ)) (α : ℚ) :
    List (List ℚ) :=
  let X := rowsMul n n n (ListMatrix.transpose n Â) (rowsMul n n n Q E)
  let Z := rowsMul n n n (ListMatrix.transpose n E) (rowsMul n n n Q E)
  rowsMap₂ (fun x y => -(x + y)) n n X
    (rowsMap₂ (fun y z => y + 2 * α * z) n n (ListMatrix.transpose n X) Z)

theorem ofLists_genLyapunovResidualRows (n : ℕ) (Â Q E : List (List ℚ)) (α : ℚ) :
    ofLists n n (genLyapunovResidualRows n Â Q E α) =
      genLyapunovResidual (ofLists n n Â) (ofLists n n Q) (ofLists n n E) α := by
  ext i j
  simp only [genLyapunovResidualRows, ofLists_rowsMap₂, of_apply, ofLists_transpose,
    ofLists_rowsMul, genLyapunovResidual, Matrix.neg_apply, Matrix.add_apply, Matrix.smul_apply,
    transpose_apply, smul_eq_mul, Matrix.mul_assoc]
  ring

/-- The rows of `E + s Δ`. -/
@[expose] def linRows (n : ℕ) (E Δ : List (List ℚ)) (s : ℚ) : List (List ℚ) :=
  rowsMap₂ (fun x y => x + s * y) n n E Δ

theorem ofLists_linRows (n : ℕ) (E Δ : List (List ℚ)) (s : ℚ) :
    ofLists n n (linRows n E Δ s) = ofLists n n E + s • ofLists n n Δ := by
  rw [linRows, ofLists_rowsMap₂]
  ext i j
  simp

/-- Whether the interval `p` is accepted for the reduced data `Â`, `E₁₁`, `Δ₁₁` (all `k × k`),
the nominal capacitance `C₀` and the rate `α`: `Q ≻ 0` and both residuals
`R (E₁₁ + (lo - C₀) Δ₁₁)`, `R (E₁₁ + (hi - C₀) Δ₁₁)` are positive definite. -/
@[expose] def CapacitanceInterval.check (p : CapacitanceInterval) (k : ℕ)
    (Â E₁₁ Δ₁₁ : List (List ℚ)) (C₀ α : ℚ) : Bool :=
  LDLCert.checkPosDefComputed k p.Q &&
    LDLCert.checkPosDefComputed k
      (genLyapunovResidualRows k Â p.Q (linRows k E₁₁ Δ₁₁ (p.lo - C₀)) α) &&
    LDLCert.checkPosDefComputed k
      (genLyapunovResidualRows k Â p.Q (linRows k E₁₁ Δ₁₁ (p.hi - C₀)) α)

/-- An untrusted certificate of stability of a netlist for every capacitance of one capacitor in
`[lo, hi]`, at the rate `α`: a structured decoupling and the operating point of the nominal
netlist, the capacitor's branch, the differential blocks `E₁₁` of `T E U` and `Δ₁₁` of
`T ΔE U` (dense `k × k` rows, checked), and a cover of `[lo, hi]` by intervals with their
Lyapunov matrices. -/
structure CapacitanceRangeCert where
  /-- The structured decoupling of the nominal netlist. -/
  dec : SparseDecouplingCert
  /-- The operating point: all node potentials, then all branch currents. -/
  z₀ : List ℚ
  /-- The branch of the capacitor (0-based). -/
  branch : ℕ
  /-- The differential block of `T E U`. -/
  E₁₁ : List (List ℚ)
  /-- The differential block of `T ΔE U`, for the stamp `ΔE` of the capacitance. -/
  Δ₁₁ : List (List ℚ)
  /-- The decay rate. -/
  α : ℚ
  /-- The lower end of the range of capacitances. -/
  lo : ℚ
  /-- The upper end of the range of capacitances. -/
  hi : ℚ
  /-- The intervals of the cover, with their Lyapunov matrices. -/
  pieces : List CapacitanceInterval

namespace CapacitanceRangeCert

variable (cert : CapacitanceRangeCert)

/-- Whether `cert` is accepted for the netlist `c`: branch `cert.branch` is a capacitor, of
capacitance `C₀`; the netlist is well formed, the decoupling and the operating point are
accepted for it (`SparseDecouplingCert.check`, `isEquilibriumSparse`); the transforms map the
stamp of the capacitance into the differential block, where it is `Δ₁₁`, and the differential
block of `T E U` is `E₁₁`; `α > 0`, `lo > 0`; the intervals cover `[lo, hi]`; and every interval
is accepted with `Â = E₁₁ A` for the reduced matrix `A` of the decoupling. -/
@[expose] def check (c : Netlist) : Bool :=
  match c.capacitance? cert.branch with
  | none => false
  | some C₀ =>
    c.check && Nat.blt cert.branch c.branches.length &&
      cert.dec.check c.size c.eSparse c.fSparse &&
      isEquilibriumSparse c.size c.fSparse c.bList cert.z₀ &&
      isZeroSparse (blk₁₂ cert.dec.k (cert.dec.bar (c.capacitanceRows cert.branch))) &&
      isZeroSparse (blk₂₁ cert.dec.k (cert.dec.bar (c.capacitanceRows cert.branch))) &&
      isZeroSparse (blk₂₂ cert.dec.k (cert.dec.bar (c.capacitanceRows cert.branch))) &&
      eqSparse (sparseOfRows cert.E₁₁) (blk₁₁ cert.dec.k (cert.dec.bar c.eSparse)) &&
      eqSparse (sparseOfRows cert.Δ₁₁)
        (blk₁₁ cert.dec.k (cert.dec.bar (c.capacitanceRows cert.branch))) &&
      decide (0 < cert.α) && decide (0 < cert.lo) && coversIcc cert.lo cert.hi cert.pieces &&
      cert.pieces.all fun p => p.check cert.dec.k
        (rowsMul cert.dec.k cert.dec.k cert.dec.k cert.E₁₁ cert.dec.A) cert.E₁₁ cert.Δ₁₁ C₀
        cert.α

/-- **The guarantee of an accepted range certificate** for the netlist `c`: for every
capacitance `C ∈ [lo, hi]` of the capacitor on branch `cert.branch`, the netlist
`c.setCapacitance cert.branch C` is well formed and, with the operating point `z₀ = cert.z₀`,

1. `z₀` is a constant trajectory with zero input;
2. every differential state, read through the first `cert.dec.k` rows of `cert.dec.Uᵢ`, starts a
   trajectory on `[0, ∞)`;
3. every trajectory with zero input converges to `z₀` at the rate `cert.α`:
   `‖z t - z₀‖ ≤ M exp (-α t) ‖z 0 - z₀‖` in the Euclidean norm of all node potentials and
   branch currents, for a constant `M` that may depend on `C` but not on the trajectory. -/
@[expose] def Guarantee (c : Netlist) : Prop :=
  ∀ C : ℚ, cert.lo ≤ C → C ≤ cert.hi →
    (c.setCapacitance cert.branch C).check = true ∧
    (c.setCapacitance cert.branch C).IsTrajectoryOn 0
      (fun _ j => realOfList (c.setCapacitance cert.branch C).size cert.z₀ (Fin.castAdd _ j))
      (fun _ b => realOfList (c.setCapacitance cert.branch C).size cert.z₀ (Fin.natAdd _ b))
      (Ici 0) ∧
    (∀ x₀ : Fin cert.dec.k → ℝ, ∃ φ i,
      (c.setCapacitance cert.branch C).IsTrajectoryOn 0 φ i (Ici 0) ∧
      realOfSparse cert.dec.k (c.setCapacitance cert.branch C).size cert.dec.Uᵢ *ᵥ
        Fin.append (φ 0) (i 0) = x₀) ∧
    ∃ M : ℝ, ∀ φ i, (c.setCapacitance cert.branch C).IsTrajectoryOn 0 φ i (Ici 0) → ∀ t ≥ 0,
      ‖WithLp.toLp 2 (Fin.append (φ t) (i t) -
          realOfList (c.setCapacitance cert.branch C).size cert.z₀)‖ ≤
        M * Real.exp (-(cert.α * t)) *
          ‖WithLp.toLp 2 (Fin.append (φ 0) (i 0) -
            realOfList (c.setCapacitance cert.branch C).size cert.z₀)‖

private theorem realOfRows_genLyapunovResidualRows (n : ℕ) (Â Q E : List (List ℚ)) (α : ℚ) :
    realOfRows n n (genLyapunovResidualRows n Â Q E α) =
      genLyapunovResidual (realOfRows n n Â) (realOfRows n n Q) (realOfRows n n E) (α : ℝ) := by
  rw [realOfRows, ofLists_genLyapunovResidualRows]
  exact genLyapunovResidual_map (Rat.castHom ℝ) _ _ _ _

private theorem realOfRows_linRows (n : ℕ) (E Δ : List (List ℚ)) (s : ℚ) :
    realOfRows n n (linRows n E Δ s) = realOfRows n n E + (s : ℝ) • realOfRows n n Δ := by
  rw [realOfRows, ofLists_linRows]
  ext i j
  simp

private theorem realOfRows_rowsMul (n : ℕ) (X Y : List (List ℚ)) :
    realOfRows n n (rowsMul n n n X Y) = realOfRows n n X * realOfRows n n Y := by
  rw [realOfRows, ofLists_rowsMul]
  exact Matrix.map_mul (f := Rat.castHom ℝ)

variable {cert} {c : Netlist}

/-- **Soundness of the range checker.** If `cert` is accepted for the netlist `c`, then for
every capacitance `C ∈ [cert.lo, cert.hi]` of the capacitor on branch `cert.branch`, the circuit
`c.setCapacitance cert.branch C` is exponentially stable at the rate `cert.α`
(`CapacitanceRangeCert.Guarantee`). The proof decouples each such circuit with the transforms of
`cert.dec` (`SparseDecouplingCert.exists_decoupling_of_add`), finds an interval of the cover
containing `C`, and applies the generalized Lyapunov inequality on that interval
(`Matrix.posDef_genLyapunovResidual_of_mem_Icc`,
`Matrix.exists_norm_le_exp_of_genLyapunovResidual`). -/
theorem guarantee_of_check (h : cert.check c = true) : cert.Guarantee c := by
  unfold check at h
  split at h
  · exact absurd h Bool.false_ne_true
  rename_i C₀ hcap
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.blt_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc, hb⟩, hd⟩, hz⟩, h₁₂⟩, h₂₁⟩, h₂₂⟩, hE₁₁⟩, hΔ₁₁⟩, hα⟩, hlo⟩, hcov⟩,
    hps⟩ := h
  intro C hCl hCh
  have hN : (c.setCapacitance cert.branch C).size = c.size := Netlist.size_setCapacitance
  have hc' := Netlist.check_setCapacitance hc hb (hlo.trans_le hCl)
  obtain ⟨p, hp, hpl, hph⟩ := exists_mem_of_coversIcc hcov hCl hCh
  have hpc := hps p hp
  simp only [CapacitanceInterval.check, Bool.and_eq_true] at hpc
  obtain ⟨⟨hQ, hRl⟩, hRh⟩ := hpc
  set k := cert.dec.k
  set E₀ : Matrix (Fin k) (Fin k) ℝ := realOfRows k k cert.E₁₁
  set Δ : Matrix (Fin k) (Fin k) ℝ := realOfRows k k cert.Δ₁₁
  set Â : Matrix (Fin k) (Fin k) ℝ := E₀ * realOfRows k k cert.dec.A
  have hQ' : (realOfRows k k p.Q).PosDef := LDLCert.posDef_of_checkPosDefComputed hQ
  have hres : ∀ s : ℚ, LDLCert.checkPosDefComputed k (genLyapunovResidualRows k
      (rowsMul k k k cert.E₁₁ cert.dec.A) p.Q (linRows k cert.E₁₁ cert.Δ₁₁ s) cert.α) = true →
      (genLyapunovResidual Â (realOfRows k k p.Q) (E₀ + (s : ℝ) • Δ) cert.α).PosDef := by
    intro s hs
    have := LDLCert.posDef_of_checkPosDefComputed hs
    rwa [← realOfRows, realOfRows_genLyapunovResidualRows, realOfRows_rowsMul,
      realOfRows_linRows] at this
  have hRC : (genLyapunovResidual Â (realOfRows k k p.Q)
      (E₀ + ((C - C₀ : ℚ) : ℝ) • Δ) cert.α).PosDef :=
    Matrix.posDef_genLyapunovResidual_of_mem_Icc hQ'.posSemidef (by exact_mod_cast hα.le)
      ⟨by exact_mod_cast (by linarith : p.lo - C₀ ≤ C - C₀),
        by exact_mod_cast (by linarith : C - C₀ ≤ p.hi - C₀)⟩ (hres _ hRl) (hres _ hRh)
  obtain ⟨hunit, M, hM⟩ := Matrix.exists_norm_le_exp_of_genLyapunovResidual hQ' hRC
  have hdN : cert.dec.check (c.setCapacitance cert.branch C).size c.eSparse c.fSparse = true := by
    rw [hN]; exact hd
  have hΔl : (c.capacitanceRows cert.branch).length ≤ (c.setCapacitance cert.branch C).size := by
    rw [hN]; exact Netlist.length_capacitanceRows hb
  have hE : (c.setCapacitance cert.branch C).mna.E =
      realOfSparse (c.setCapacitance cert.branch C).size (c.setCapacitance cert.branch C).size
          c.eSparse + ((C - C₀ : ℚ) : ℝ) •
        realOfSparse (c.setCapacitance cert.branch C).size (c.setCapacitance cert.branch C).size
          (c.capacitanceRows cert.branch) := by
    rw [Netlist.mna_E_eq, hN, realOfSparse, Netlist.ofSparse_eSparse_setCapacitance hb hcap]
    ext i j
    simp
  have hF : (c.setCapacitance cert.branch C).mna.F =
      realOfSparse (c.setCapacitance cert.branch C).size (c.setCapacitance cert.branch C).size
        c.fSparse := by
    rw [Netlist.mna_F_eq, hN, realOfSparse, Netlist.ofSparse_fSparse_setCapacitance hb hcap]
  have hE₁₁' : realOfSparse k k (blk₁₁ k (cert.dec.bar c.eSparse)) = E₀ := by
    change _ = realOfRows k k cert.E₁₁
    rw [← realOfSparse_sparseOfRows]
    exact congrArg (Matrix.map · _) (ofSparse_eq_of_eqSparse hE₁₁).symm
  have hΔ₁₁' : realOfSparse k k (blk₁₁ k (cert.dec.bar (c.capacitanceRows cert.branch))) = Δ := by
    change _ = realOfRows k k cert.Δ₁₁
    rw [← realOfSparse_sparseOfRows]
    exact congrArg (Matrix.map · _) (ofSparse_eq_of_eqSparse hΔ₁₁).symm
  obtain ⟨D, hDA, hDQ⟩ := SparseDecouplingCert.exists_decoupling_of_add hdN hΔl h₁₂ h₂₁ h₂₂ hE hF
    (by rw [hE₁₁', hΔ₁₁']; exact hunit)
  have hDA' : D.A = (E₀ + ((C - C₀ : ℚ) : ℝ) • Δ)⁻¹ * Â := by
    rw [hDA, ← (SparseDecouplingCert.spec hdN).hA, hE₁₁', hΔ₁₁']
  have heq : (c.setCapacitance cert.branch C).mna.IsEquilibrium
      (realOfList (c.setCapacitance cert.branch C).size cert.z₀) :=
    isEquilibrium_of_isEquilibriumSparse (b := c.bList) hF
      (by rw [← Netlist.bList_setCapacitance hb hcap]; rfl) (by rw [hN]; exact hz)
  have hM' : ∀ x : ℝ → EuclideanSpace ℝ (Fin k),
      (toEuclideanCLM (𝕜 := ℝ) D.A).IsTrajectoryOn x (Ici 0) →
        ∀ t ≥ 0, ‖x t‖ ≤ M * Real.exp (-(cert.α * t)) * ‖x 0‖ := by
    rw [hDA']; exact hM
  obtain ⟨h1, h2, -⟩ := Netlist.isExponentiallyStable_of_decoupling hc' D heq
    ⟨M, cert.α, by exact_mod_cast hα, hM'⟩
  obtain ⟨M', hM''⟩ := D.exists_norm_le_exp heq hM'
  refine ⟨hc', h1, fun x₀ => ?_, M', fun φ i hφ t ht =>
    hM'' _ ((Netlist.isTrajectoryOn_iff hc' (uniqueDiffOn_Ici 0)).1 hφ) t ht⟩
  obtain ⟨φ, i, hφ, hx⟩ := h2 x₀
  exact ⟨φ, i, hφ, hDQ ▸ hx⟩

end CapacitanceRangeCert

namespace Text

/-- **The end-to-end range checker**: whether the text `s` parses and `cert` is accepted for the
circuit it describes. -/
@[expose] def checkTextRange (s : String) (cert : CapacitanceRangeCert) : Bool :=
  match parse s with
  | .ok P => cert.check P.netlist
  | .error _ => false

/-- **Certified stability over a range of capacitances, from a netlist text.** If
`checkTextRange s cert` holds, then `s` parses to a netlist `P`, and for every capacitance
`C ∈ [cert.lo, cert.hi]` of the capacitor on branch `cert.branch` the circuit
`P.netlist.setCapacitance cert.branch C` is exponentially stable at the rate `cert.α`. -/
theorem exists_parse_of_checkTextRange {s : String} {cert : CapacitanceRangeCert}
    (h : checkTextRange s cert = true) : ∃ P, parse s = .ok P ∧ cert.Guarantee P.netlist := by
  unfold checkTextRange at h
  split at h
  · rename_i P hP
    exact ⟨P, hP, CapacitanceRangeCert.guarantee_of_check h⟩
  · exact absurd h Bool.false_ne_true

end Text

end Cslib.Electrical
