/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.VerticalAxis
public import CslibFrontier.Foundations.Quantum.Algebra.CommutatorTransfer
import CslibFrontier.Foundations.Quantum.Algebra.CStar
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Point commutation from diagonal lines

At the full prefix, the diagonal verifier can compare either of two independent
uniform points with the same line measurement. The two evaluations of this
projective measurement commute. Transferring their commutation to the point
measurements proves an estimate of the kind used in
[Ji, Natarajan, Vidick, Wright and Yuen, §10][JNVWY2020LowIndividualDegree].

## Main results

* `Cslib.PCP.LowIndividualDegree.decodedPoint_prefixCommutatorDefect_le` handles
  points separated by a uniform direction in any fixed prefix.
* `Cslib.PCP.LowIndividualDegree.decodedPoint_pairCommutatorDefect_le` handles
  independent uniform points by choosing the full prefix.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Finset Cslib.Quantum
open scoped BigOperators

variable {F A : Type*} {n : ℕ} [Field F] [Fintype F] [DecidableEq F]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

local notation "Q" => Question F (n + 1)
local notation "Ans" => Answer F (n + 1)

/-- Read a line answer at a point. Missing points and point-only answers decode to zero. -/
private def lineValue (u : Point F (n + 1)) : Ans → F
  | .inl _ => 0
  | .inr a => if h : u ∈ a.1 then a.2 ⟨u, h⟩ else 0

private noncomputable def evaluatedDiagonal (M : Q → Measurement Ans A)
    (L : Finset (Point F (n + 1))) (u : Point F (n + 1)) : Measurement F A :=
  (M (.diagonal L)).map (lineValue u)

private theorem diagonal_eval_copy_le (S : CommutingStrategy Q Q Ans Ans A)
    (d : ℕ) (L : Finset (Point F (n + 1))) (u : Point F (n + 1)) :
    Measurement.copyDefect S.state (decodedPoint S.alice u) (evaluatedDiagonal S.bob L u) ≤
      2 * (1 - acceptScore S d (.point u) (.diagonal L)) := by
  classical
  have hscore : acceptScore S d (.point u) (.diagonal L) ≤
      Measurement.agreement S.state (decodedPoint S.alice u) (evaluatedDiagonal S.bob L u) := by
    simp only [acceptScore_eq_sum, decodedPoint, evaluatedDiagonal, Measurement.agreement_map_map]
    refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
    by_cases h : accepts d (.point u) (.diagonal L) a b
    · obtain ⟨g, z, rfl, rfl, hu, he⟩ := exists_agree_of_accepts_point_diagonal d L u a b h
      simp only [ite_eq_left h, decodePoint_inl, lineValue, dite_eq_left hu, he, ite_true,
        CommutingStrategy.prob, le_refl]
    · rw [ite_eq_right h]
      exact ite_nonneg (S.prob_nonneg _ _ _ _) le_rfl
  have hn := Measurement.sum_norm_sub_sq_le S.state (decodedPoint S.alice u)
    (evaluatedDiagonal S.bob L u) (fun a =>
      Measurement.commute_map_map _ _ (S.commute (.point u) (.diagonal L)) _ _ a a)
  unfold Measurement.copyDefect
  linarith

omit [DecidableEq F] in
private theorem expect_translate_base {ι : Type*} [Fintype ι]
    (shift : ι → Point F (n + 1)) (f : Point F (n + 1) → ι → ℝ) :
    (𝔼 u : Point F (n + 1), 𝔼 v, f (u + shift v) v) =
      𝔼 u : Point F (n + 1), 𝔼 v, f u v := by
  rw [expect_comm univ univ, expect_comm (f := f) univ univ]
  refine expect_congr rfl fun v _ => ?_
  exact Fintype.expect_equiv (Equiv.addRight (shift v)) _ _ (fun _ => rfl)

/-- The average squared commutator defect of the decoded point measurements is controlled
by the diagonal branch's rejection probability. The two points differ by a uniform
direction in the chosen prefix. -/
theorem decodedPoint_prefixCommutatorDefect_le (S : CommutingStrategy Q Q Ans Ans A)
    (hPoint : ∀ u, (S.alice (.point u)).IsProjective)
    (hLine : ∀ L, (S.bob (.diagonal L)).IsProjective) (d : ℕ) (i : Fin (n + 1)) :
    (𝔼 u : Point F (n + 1), 𝔼 v : Fin (i.val + 1) → F, Measurement.pairCommutatorDefect S.state
      (decodedPoint S.alice u) (decodedPoint S.alice (u + prefixDirection i v))) ≤
      64 * (n + 1 : ℝ) * (1 - (branchGame (F := F) n d .diagonal).commutingWinProb S) := by
  classical
  let direction := prefixDirection (F := F) i
  let err (u : Point F (n + 1)) (v : Fin (i.val + 1) → F) :=
    Measurement.copyDefect S.state (decodedPoint S.alice u)
      (evaluatedDiagonal S.bob (linePoints u (direction v)) u)
  have herr : (𝔼 u : Point F (n + 1), 𝔼 v, err u v) ≤
      4 * (n + 1 : ℝ) * (1 - (branchGame (F := F) n d .diagonal).commutingWinProb S) := by
    calc
      _ ≤ 𝔼 u : Point F (n + 1), 𝔼 v,
          (2 * (1 - acceptScore S d (.point u) (.diagonal (linePoints u (direction v))))) :=
        expect_le_expect fun u _ => expect_le_expect fun v _ => diagonal_eval_copy_le S d _ u
      _ ≤ _ := by
        simp only [← mul_expect, direction]
        have hloss := diagonalPointLossAt_le n d S i
        linarith
  have htranslate (u v : Point F (n + 1)) : linePoints (u + v) v = linePoints u v := by
    simpa only [one_smul] using linePoints_translate_direction u v (1 : F)
  calc
    _ ≤ 𝔼 u : Point F (n + 1), 𝔼 v, (8 * (err u v + err (u + direction v) v)) := by
      refine expect_le_expect fun u _ => expect_le_expect fun v _ => ?_
      let w := u + direction v
      let L := linePoints u (direction v)
      have hPt (x : Point F (n + 1)) : (decodedPoint S.alice x).IsProjective :=
        (hPoint x).map decodePoint
      have hLn (x : Point F (n + 1)) : (evaluatedDiagonal S.bob L x).IsProjective :=
        (hLine L).map (lineValue x)
      have hcross (x y : Point F (n + 1)) (a b : F) :
          Commute ((decodedPoint S.alice x).effect a)
            ((evaluatedDiagonal S.bob L y).effect b) :=
        Measurement.commute_map_map _ _ (S.commute (.point x) (.diagonal L)) _ _ a b
      have hline (a b : F) : Commute ((evaluatedDiagonal S.bob L u).effect a)
          ((evaluatedDiagonal S.bob L w).effect b) :=
        Measurement.commute_map_map _ _ (hLine L).commute_effect _ _ a b
      have h := Measurement.pairCommutatorDefect_le_of_commuting_copies S.state
        _ _ _ _ (hPt u) (hPt w) (hLn u) (hLn w)
        (hcross u w) (fun a b => (hcross w u b a).symm) hline
      simpa only [err, htranslate, L, w, direction] using h
    _ ≤ _ := by
      simp only [← mul_expect, expect_add_distrib, expect_translate_base]
      linarith

/-- For two independent uniform points the squared commutator defect is at most
`64 (n + 1)` times the diagonal-branch loss. -/
theorem decodedPoint_pairCommutatorDefect_le (S : CommutingStrategy Q Q Ans Ans A)
    (hPoint : ∀ u, (S.alice (.point u)).IsProjective)
    (hLine : ∀ L, (S.bob (.diagonal L)).IsProjective) (d : ℕ) :
    (𝔼 u : Point F (n + 1), 𝔼 w : Point F (n + 1), Measurement.pairCommutatorDefect S.state
      (decodedPoint S.alice u) (decodedPoint S.alice w)) ≤
      64 * (n + 1 : ℝ) * (1 - (branchGame (F := F) n d .diagonal).commutingWinProb S) := by
  have h := decodedPoint_prefixCommutatorDefect_le S hPoint hLine d (Fin.last n)
  simp only [prefixDirection_last] at h
  refine le_of_eq_of_le (expect_congr rfl fun u _ => ?_) h
  exact (Fintype.expect_equiv (Equiv.addLeft u) _ _ (fun _ => rfl)).symm

end Cslib.PCP.LowIndividualDegree
