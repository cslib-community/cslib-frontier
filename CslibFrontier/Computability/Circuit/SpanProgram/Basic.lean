/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Monotone Span Programs

A monotone span program over a field `F` for a party type `Party` ([BonehShoup2023], Definition
22.21, p. 978) assigns to each party `i : Party` a `rowDim i × (tailDim + 1)` matrix `matrix i`
over `F`. The book's column count `d` is `tailDim + 1 ≥ 1` so that the target row vector
`e₁ = (1, 0, …, 0) ∈ F^{tailDim + 1}` is always well-defined and nonzero. A coalition `s` is
accepted iff `target = e₁` lies in the `F`-linear span of all rows of `{matrix i}_{i ∈ s}`.

## Main definitions

* `Cslib.Circuits.MonotoneSpanProgram`: a monotone span program over field `F` and `Party`.
* `Cslib.Circuits.MonotoneSpanProgram.target`: the unit row vector `e₁ = Pi.single 0 1`.
* `Cslib.Circuits.MonotoneSpanProgram.rowSpan`: the row span of `{P.matrix i}_{i ∈ s}`.
* `Cslib.Circuits.MonotoneSpanProgram.Accepts`: acceptance predicate `P.target ∈ P.rowSpan s`.

## Main results

* `Cslib.Circuits.MonotoneSpanProgram.accepts_mono`: acceptance is monotone under coalition
  inclusion.
* `Cslib.Circuits.MonotoneSpanProgram.not_accepts_empty`: the empty coalition is never accepted.
* `Cslib.Circuits.MonotoneSpanProgram.accepts_iff_exists_vecMul`: acceptance iff there exist
  per-party row weights summing to `P.target`.
* `Cslib.Circuits.MonotoneSpanProgram.exists_nullVector_of_not_accepts`: every unauthorized
  coalition admits a right-kernel vector `v` with `v 0 = 1`.

## References

* [BonehShoup2023] Dan Boneh and Victor Shoup, *A Graduate Course in Applied Cryptography*, v0.6,
  Section 22.5.2.
-/

public section

namespace Cslib.Circuits

/-- A monotone span program over a field `F` for party/input type `Party`
([BonehShoup2023], Definition 22.21, p. 978).

Each party `i` holds a `rowDim i × (tailDim + 1)` matrix `matrix i` over `F`. The book's column
dimension `d` is `tailDim + 1 ≥ 1` so that `target = e₁ = (1, 0, …, 0)` is well-defined and
nonzero. -/
structure MonotoneSpanProgram (F Party : Type*) where
  /-- Number of auxiliary columns beyond the first (target) coordinate (`d = tailDim + 1`). -/
  tailDim : ℕ
  /-- Number of rows `d_i` assigned to each party `i`. -/
  rowDim : Party → ℕ
  /-- Matrix `M_i` of size `d_i × (tailDim + 1)` for each party `i`. -/
  matrix : (i : Party) → Matrix (Fin (rowDim i)) (Fin (tailDim + 1)) F

namespace MonotoneSpanProgram

section Span

variable {F Party : Type*} [Field F]

/-- The target row vector `e₁ = (1, 0, …, 0) ∈ F^{tailDim + 1}`
([BonehShoup2023], Definition 22.21, p. 978). -/
@[expose] def target (P : MonotoneSpanProgram F Party) : Fin (P.tailDim + 1) → F :=
  Pi.single 0 1

@[simp]
theorem target_zero (P : MonotoneSpanProgram F Party) : P.target 0 = 1 :=
  Pi.single_eq_same 0 1

theorem target_ne_zero (P : MonotoneSpanProgram F Party) : P.target ≠ 0 :=
  Pi.single_ne_zero_iff.mpr one_ne_zero

/-- The `F`-linear span of all rows of `{P.matrix i}_{i ∈ s}` for coalition `s`
([BonehShoup2023], Definition 22.21, p. 978). -/
def rowSpan (P : MonotoneSpanProgram F Party) (s : Finset Party) :
    Submodule F (Fin (P.tailDim + 1) → F) :=
  Submodule.span F (Set.range fun p : (i : s) × Fin (P.rowDim i.val) => P.matrix p.1.val p.2)

/-- A monotone span program `P` accepts coalition `s` iff `P.target ∈ P.rowSpan s`
([BonehShoup2023], Definition 22.21, p. 978). -/
def Accepts (P : MonotoneSpanProgram F Party) (s : Finset Party) : Prop :=
  P.target ∈ P.rowSpan s

/-- Acceptance by a monotone span program is monotone under coalition inclusion
([BonehShoup2023], Definition 22.21, p. 978). -/
theorem accepts_mono (P : MonotoneSpanProgram F Party) : Monotone P.Accepts := by
  intro s t hst hs
  refine Submodule.span_mono ?_ hs
  rintro v ⟨⟨⟨i, hi⟩, r⟩, rfl⟩
  exact ⟨⟨⟨i, hst hi⟩, r⟩, rfl⟩

/-- The empty coalition is never accepted by a monotone span program over a field. -/
theorem not_accepts_empty (P : MonotoneSpanProgram F Party) : ¬ P.Accepts ∅ := by
  simp [Accepts, rowSpan, Set.range_eq_empty, P.target_ne_zero]

/-- A coalition `s` is accepted iff there exist per-party row coefficient vectors `w i` whose
weighted sum of rows equals `P.target = e₁` ([BonehShoup2023], Construction 22.2, p. 980). -/
theorem accepts_iff_exists_vecMul (P : MonotoneSpanProgram F Party) (s : Finset Party) :
    P.Accepts s ↔
      ∃ w : (i : s) → Fin (P.rowDim i.val) → F,
        ∑ i : s, Matrix.vecMul (w i) (P.matrix i.val) = P.target := by
  rw [Accepts, rowSpan, Submodule.mem_span_range_iff_exists_fun]
  simp_rw [Fintype.sum_sigma, ← Matrix.vecMul_eq_sum]
  exact ⟨fun ⟨c, hc⟩ => ⟨fun i r => c ⟨i, r⟩, hc⟩, fun ⟨w, hw⟩ => ⟨fun p => w p.1 p.2, hw⟩⟩

/-- Sufficient certificate of non-acceptance: any column vector `v` with `v 0 = 1` in the right
kernel of `P.matrix i` for all `i ∈ s` witnesses `¬ P.Accepts s`. -/
theorem not_accepts_of_exists_nullVector (P : MonotoneSpanProgram F Party) {s : Finset Party}
    (v : Fin (P.tailDim + 1) → F) (hv0 : v 0 = 1)
    (hv_null : ∀ i ∈ s, Matrix.mulVec (P.matrix i) v = 0) : ¬ P.Accepts s := by
  intro hs
  obtain ⟨w, hw⟩ := (P.accepts_iff_exists_vecMul s).mp hs
  have h0 : dotProduct P.target v = 0 := by
    rw [← hw, sum_dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Matrix.dotProduct_mulVec, hv_null i.val i.property, dotProduct_zero]
  rw [target, single_one_dotProduct, hv0] at h0
  exact one_ne_zero h0

/-- For every unauthorized coalition `s`, there exists a column vector `v : Fin (P.tailDim + 1) → F`
with `v 0 = 1` that lies in the right kernel of `P.matrix i` for every `i ∈ s`. -/
theorem exists_nullVector_of_not_accepts (P : MonotoneSpanProgram F Party) {s : Finset Party}
    (hs : ¬ P.Accepts s) :
    ∃ v : Fin (P.tailDim + 1) → F, v 0 = 1 ∧ ∀ i ∈ s, Matrix.mulVec (P.matrix i) v = 0 := by
  obtain ⟨φ, hφ_target, hφ_span⟩ :=
    Submodule.exists_dual_map_eq_bot_of_notMem hs (inferInstance : Module.Projective F _)
  refine ⟨fun j => φ (Pi.single j 1) / φ P.target, div_self hφ_target, fun i hi => ?_⟩
  ext r
  have hφ_row : φ (P.matrix i r) = 0 := by
    rw [← Submodule.mem_bot F, ← hφ_span]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨⟨⟨i, hi⟩, r⟩, rfl⟩)
  rw [pi_eq_sum_univ' (P.matrix i r), map_sum] at hφ_row
  simp only [map_smul, smul_eq_mul] at hφ_row
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, div_eq_mul_inv, ← mul_assoc,
    ← Finset.sum_mul, hφ_row, zero_mul]

end Span

end MonotoneSpanProgram

end Cslib.Circuits
