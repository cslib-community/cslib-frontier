/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.PacketEntry
public import CslibFrontier.Foundations.Data.BitString.FieldEnumeration

/-!
# Coefficient extraction as a padded binary sum of products

Each row chooses its local term or one dense mode, using a fixed-width, most-significant-first
field. Codes above the number of modes contribute zero. One extra factor checks that selected
modes belong to the target set and occur with the prescribed multiplicities. Consequently the
ordinary binary sum of products equals `TensorNetwork.listCoeff`, including an empty list of
rows. The extra factor is essential in that case: a nonzero prescribed target-mode exponent
gives zero.

This is an original representation bridge for the packet circuit. The arithmetic values remain
explicit input factors; this module makes no running-time claim for computing them.

## Main results

* `Cslib.Circuits.Frontier.TensorNetwork.CoeffWordSum.sum_factor`: the binary sum of products
  equals coefficient extraction.
-/

public section

namespace Cslib.Circuits.Frontier.TensorNetwork.CoeffWordSum

open Finset BitString

variable {R : Type*} [CommRing R]

/-- A binary row-choice word has no padding codes, chooses only target modes, and has the
prescribed multiplicity of every target mode. Fields occur in row order, most significant first. -/
@[expose] def Valid (modes rows width : ℕ) (targets : Finset (Fin modes))
    (exponent : Fin modes → ℕ) (assignment : ℕ) : Prop :=
  (∀ j : Fin rows, binaryField rows width assignment j ≤ modes) ∧
  (∀ (j : Fin rows) (k : Fin modes),
    fieldChoice modes (binaryField rows width assignment j) = some k → k ∈ targets) ∧
  ∀ k ∈ targets,
    #{j : Fin rows | fieldChoice modes (binaryField rows width assignment j) = some k} = exponent k

open Classical in
/-- The first `rows` factors are the chosen row terms. The final factor is the validity bit,
viewed in the coefficient ring. No filtered-mode rank or expanded coefficient table is used. -/
@[expose] noncomputable def factor (modes rows width : ℕ) (targets : Finset (Fin modes))
    (term : Fin rows → Option (Fin modes) → R) (exponent : Fin modes → ℕ)
    (assignment vertex : ℕ) : R :=
  if h : vertex < rows then
    term ⟨vertex, h⟩ (fieldChoice modes (binaryField rows width assignment vertex))
  else if Valid modes rows width targets exponent assignment then 1 else 0

open Classical in
private theorem prod_factor (modes rows width : ℕ) (targets : Finset (Fin modes))
    (term : Fin rows → Option (Fin modes) → R) (exponent : Fin modes → ℕ)
    (assignment : ℕ) :
    (∏ vertex ∈ range (rows + 1), factor modes rows width targets term exponent assignment vertex) =
      if Valid modes rows width targets exponent assignment then
        ∏ j, term j (fieldChoice modes (binaryField rows width assignment j)) else 0 := by
  classical
  rw [prod_range_succ, prod_range]
  have hrows : (∏ j : Fin rows, factor modes rows width targets term exponent assignment j) =
      ∏ j, term j (fieldChoice modes (binaryField rows width assignment j)) := by
    apply prod_congr rfl
    intro j _
    simp only [factor, j.isLt, ↓reduceDIte]
  rw [hrows]
  simp only [factor, lt_self_iff_false, ↓reduceDIte]
  split_ifs <;> simp

/-- The binary sum of the row factors and their validity factor is exactly the requested
coefficient of the product of affine row forms. Every local/mode choice occurs once. -/
theorem sum_factor (modes rows width : ℕ) (hwidth : modes + 1 ≤ 2 ^ width)
    (targets : Finset (Fin modes)) (term : Fin rows → Option (Fin modes) → R)
    (exponent : Fin modes → ℕ) :
    (∑ assignment ∈ range (2 ^ (rows * width)),
      ∏ vertex ∈ range (rows + 1),
        factor modes rows width targets term exponent assignment vertex) =
      listCoeff targets (List.ofFn term) exponent := by
  classical
  simp only [prod_factor]
  have hsplit (assignment : ℕ) :
      (if Valid modes rows width targets exponent assignment then
        ∏ j, term j (fieldChoice modes (binaryField rows width assignment j)) else 0) =
      if ∀ j : Fin rows, binaryField rows width assignment j ≤ modes then
        (if (∀ (j : Fin rows) (k : Fin modes),
            fieldChoice modes (binaryField rows width assignment j) = some k → k ∈ targets) ∧
          (∀ k ∈ targets,
            #{j : Fin rows | fieldChoice modes (binaryField rows width assignment j) = some k} =
              exponent k) then
          ∏ j, term j (fieldChoice modes (binaryField rows width assignment j)) else 0)
      else 0 := by
    by_cases h : ∀ j : Fin rows, binaryField rows width assignment j ≤ modes
    · simp [Valid, h]
    · simp [Valid, h]
  simp_rw [hsplit]
  rw [sum_binaryFields modes rows width hwidth (fun φ =>
    if (∀ j k, φ j = some k → k ∈ targets) ∧
      (∀ k ∈ targets, #{j | φ j = some k} = exponent k) then ∏ j, term j (φ j) else 0)]
  convert! sum_eq_listCoeff targets rows term exponent using 1
  apply sum_congr rfl
  intro φ _
  split_ifs <;> rfl

end Cslib.Circuits.Frontier.TensorNetwork.CoeffWordSum
