/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.LocallyDecodable.Hadamard
import CslibFrontier.Computability.LocallyDecodable.LowerBound
import CslibFrontier.Computability.LocallyDecodable.OneQuery
import Mathlib.Tactic.NormNum

/-!
# Tests: locally decodable codes

The Hadamard code of three bits is a `(2, 1/8, 1/4)` locally decodable code and a `(2, 2, 1/2)`
smooth code, and the Katz–Trevisan smoothing of its decoder is a `(2, 16, 1/4)` smooth decoder
(or `(2, 16, 1/8)` via the general adaptive-capable smoothing reduction). The repetition code of one
bit, read at a uniform position, is a `(1, 1, 1/2)` smooth code; it attains the one-query bound
`4 |ι| ε² ≤ c² (|Γ| - 1)` with equality. No binary code of two message bits is a `(1, 1, 1/2)`
smooth code, and no binary code of a hundred message bits is a `(1, 1/4, 1/4)` locally decodable
code, whatever its length.

Additional tests exercise the adaptive-to-non-adaptive reduction (`Code.nonadaptivize`) on a
genuinely adaptive two-query decoder, hypergraph matching extraction (`Code.DecodingMatching`), and
the Katz–Trevisan `Ω(k ^ (q / (q - 1)))` lower bound (`Code.IsLocallyDecodable.rpow_le_card`),
including non-vacuity on the Hadamard code and superlinear impossibility for linear-rate binary
two-query LDCs.
-/

namespace CslibFrontierTests.LocallyDecodable

open Cslib Cslib.Code Cslib.BitString Probability

/-! ### The Hadamard code -/

/-- The Hadamard decoder recovers each of three bits with probability `3/4` from a word that
differs from the codeword on an eighth of the positions. -/
private theorem isLocalDecoder_hadamard :
    IsLocalDecoder hadamardCode 2 (1 / 8) (1 / 4) (hadamardDecoder (ι := Fin 3)) := by
  have h := isLocalDecoder_hadamardDecoder (ι := Fin 3) (1 / 8)
  have hε : (1 / 2 - 2 * (1 / 8) : ℝ) = 1 / 4 := by norm_num
  rw [hε] at h
  exact h

example : IsLocallyDecodable (hadamardCode (ι := Fin 3)) 2 (1 / 8) (1 / 4) :=
  isLocalDecoder_hadamard.isLocallyDecodable

example : IsSmoothCode (hadamardCode (ι := Fin 3)) 2 2 (1 / 2) :=
  isSmoothDecoder_hadamardDecoder.isSmoothCode

/-- Katz–Trevisan smoothing turns the `(2, 1/8, 1/4)` Hadamard decoder into a `(2, 16, 1/4)`
smooth decoder. -/
example : IsSmoothCode (hadamardCode (ι := Fin 3)) 2 16 (1 / 4) := by
  have h := isLocalDecoder_hadamard.isSmoothCode hasObliviousReads_hadamardDecoder
    (by norm_num : (0 : ℝ) < 1 / 8)
  have h16 : ((2 : ℕ) : ℝ) / (1 / 8) = 16 := by norm_num
  rw [h16] at h
  exact h

/-! ### The repetition code -/

/-- The repetition code of one bit, of length three. -/
private def repetition : (Unit → Bool) → Fin 3 → Bool := fun x _ => x ()

/-- Read a uniform position and output it. -/
private noncomputable def repetitionDecoder : LocalDecoder Unit (Fin 3) Bool := fun _ =>
  nonadaptive (ProbComp.uniform (Fin 3)) (fun r => ![r]) (fun _ a => a 0)

/-- The repetition code of one bit is a `(1, 1, 1/2)` smooth code. -/
private theorem isSmoothDecoder_repetitionDecoder :
    IsSmoothDecoder repetition 1 1 (1 / 2) repetitionDecoder := by
  have h := isSmoothDecoder_nonadaptive_of_uniform (C := repetition) (ε := 1 / 2)
    (fun _ => ProbComp.uniform (Fin 3)) (fun _ r => ![r]) (fun _ _ a => a 0)
    (fun _ k => by
      rw [ProbComp.eval_uniform]
      fin_cases k
      exact PMF.map_id _)
    (fun x _ => by
      rw [decodeLaw_nonadaptive, ProbComp.eval_uniform]
      have hconst : (fun r : Fin 3 => (fun (_ : Fin 3) (a : Fin 1 → Bool) => a 0) r
          (repetition x ∘ ![r])) = Function.const _ (x ()) := rfl
      rw [hconst, PMF.map_const, PMF.pure_apply_self, ENNReal.toReal_one]
      norm_num)
  rw [Nat.cast_one] at h
  exact h

/-- The repetition code attains the one-query bound with equality. -/
example : 4 * Fintype.card Unit * (1 / 2 : ℝ) ^ 2 ≤ 1 ^ 2 * (Fintype.card Bool - 1) :=
  isSmoothDecoder_repetitionDecoder.four_mul_card_mul_sq_le (by norm_num)

example : 4 * Fintype.card Unit * (1 / 2 : ℝ) ^ 2 = 1 ^ 2 * (Fintype.card Bool - 1) := by
  norm_num

/-- The repetition code of one bit, of length three, is a `(1, 1/3, 1/6)` locally decodable code:
a word with at most one corrupted position agrees with the codeword on at least two of the three
positions, so a uniform read recovers the bit with probability at least `2/3`. -/
private theorem isLocalDecoder_repetitionDecoder :
    IsLocalDecoder repetition 1 (1 / 3) (1 / 6) repetitionDecoder where
  isQueryBounded _ := isQueryBounded_nonadaptive _ _ _
  correct x y i hy := by
    have h3 : (1 / 3 : ℝ) * Fintype.card (Fin 3) = 1 := by norm_num
    rw [h3] at hy
    have hd : hammingDist y (repetition x) ≤ 1 := by exact_mod_cast hy
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 3))) (fun r => y r = x i)
    have hdist : (Finset.univ.filter fun r : Fin 3 => ¬ y r = x i).card =
        hammingDist y (repetition x) := rfl
    rw [Finset.card_univ, Fintype.card_fin, hdist] at hsplit
    have hgood : (2 : ℝ) ≤ (Finset.univ.filter fun r : Fin 3 => y r = x i).card := by
      exact_mod_cast (by omega : 2 ≤ (Finset.univ.filter fun r : Fin 3 => y r = x i).card)
    rw [repetitionDecoder, decodeLaw_nonadaptive, ProbComp.eval_uniform,
      PMF.toReal_uniformOfFintype_map_apply, Finset.nnratCast_dens, Fintype.card_fin]
    change 1 / 2 + 1 / 6 ≤ ((Finset.univ.filter fun r : Fin 3 => y r = x i).card : ℝ) / (3 : ℕ)
    rw [Nat.cast_ofNat, le_div_iff₀ (by norm_num)]
    linarith

example : IsLocallyDecodable repetition 1 (1 / 3) (1 / 6) :=
  isLocalDecoder_repetitionDecoder.isLocallyDecodable

/-- Katz–Trevisan smoothing of a concrete one-query code: the `(1, 1/3, 1/6)` repetition code is a
`(1, 3, 1/6)` smooth code. -/
example : IsSmoothCode repetition 1 3 (1 / 6) := by
  have h := isLocalDecoder_repetitionDecoder.isSmoothCode_of_one (by norm_num)
  have h3 : (1 : ℝ) / (1 / 3) = 3 := by norm_num
  rw [h3] at h
  exact h

/-! ### Codes that are not one-query decodable -/

/-- No binary code of two message bits is a `(1, 1, 1/2)` smooth code. -/
example {P : Type} [Fintype P] [DecidableEq P] (C : (Fin 2 → Bool) → P → Bool) :
    ¬ IsSmoothCode C 1 1 (1 / 2) := by
  intro hC
  obtain ⟨A, hA⟩ := isSmoothCode_iff.mp hC
  have h := hA.four_mul_card_mul_sq_le (by norm_num)
  norm_num at h

/-- No binary code of a hundred message bits is a `(1, 1/4, 1/4)` locally decodable code, whatever
its length. -/
example {P : Type} [Fintype P] (C : (Fin 100 → Bool) → P → Bool) :
    ¬ IsLocallyDecodable C 1 (1 / 4) (1 / 4) := by
  intro hC
  obtain ⟨A, hA⟩ := isLocallyDecodable_iff.mp hC
  have h := hA.four_mul_sq_mul_card_mul_sq_le (by norm_num) (by norm_num)
  norm_num at h

/-! ### Adaptive smoothing, matching extraction, and the Katz–Trevisan lower bound -/

/-- A genuinely adaptive two-query program: the second query position (`1` vs `2`) depends on the
symbol read at position `0`. -/
private def adaptiveTwoQuery : ProbOracleComp (fun _ : Fin 3 => Bool) Bool := do
  let a ← ProbOracleComp.query (0 : Fin 3)
  if a then ProbOracleComp.query (1 : Fin 3) else ProbOracleComp.query (2 : Fin 3)

private theorem isQueryBounded_adaptiveTwoQuery : adaptiveTwoQuery.IsQueryBounded 2 := by
  have h : adaptiveTwoQuery.IsQueryBounded (1 + 1) :=
    (ProbOracleComp.IsQueryBounded.query (0 : Fin 3)).bind fun a => by
      cases a
      · exact ProbOracleComp.IsQueryBounded.query (2 : Fin 3)
      · exact ProbOracleComp.IsQueryBounded.query (1 : Fin 3)
  exact h.mono (by omega)

/-- On every codeword of the 3-bit repetition code, `nonadaptivize` attenuates the exact
probability `1` of the adaptive two-query decoder to `3 / 4`. -/
example (x : Unit → Bool) :
    (decodeLaw (nonadaptivize 2 adaptiveTwoQuery isQueryBounded_adaptiveTwoQuery)
      (repetition x) (x ())).toReal = 3 / 4 := by
  rw [toReal_decodeLaw_nonadaptivize]
  have hlaw : decodeLaw adaptiveTwoQuery (repetition x) = PMF.pure (x ()) := by
    simp only [adaptiveTwoQuery, decodeLaw_bind, decodeLaw_query, PMF.pure_bind]
    cases hx : x () <;> simp [repetition, hx]
  rw [hlaw, PMF.pure_apply_self, ENNReal.toReal_one]
  norm_num

/-- General (adaptive-capable) Katz–Trevisan smoothing applied to the Hadamard code. -/
example : IsSmoothCode (hadamardCode (ι := Fin 3)) 2 16 (1 / 8) := by
  have h := isLocalDecoder_hadamard.isLocallyDecodable.isSmoothCode
    (by norm_num : (0 : ℝ) < 1 / 8)
  have h16 : ((2 : ℕ) : ℝ) / (1 / 8) = 16 := by norm_num
  have h8 : (1 / 4 : ℝ) / (Fintype.card Bool : ℝ) ^ (2 - 1) = 1 / 8 := by norm_num
  rw [h16, h8] at h
  exact h

/-- Matching extraction from the smooth Hadamard decoder is non-vacuous. -/
example (i : Fin 3) :
    ∃ M : DecodingMatching (hadamardCode (ι := Fin 3)) i 2 (1 / 4), 1 ≤ M.edges.card := by
  obtain ⟨M, hM⟩ := isSmoothDecoder_hadamardDecoder.exists_decodingMatching_of_nonadaptive
    (by norm_num : (0 : ℝ) < 1 / 2) i
  have h4 : (1 / 2 / 2 : ℝ) = 1 / 4 := by norm_num
  refine ⟨⟨M.edges, M.pairwiseDisjoint, M.nonempty_of_mem, M.card_le_of_mem, M.predict,
    fun e he => by rw [← h4]; exact M.correct e he⟩, ?_⟩
  have hcard : (Fintype.card (Fin 3 → Bool) : ℝ) = 8 := by norm_num
  rw [hcard] at hM
  norm_num at hM
  exact Finset.card_pos.mpr hM

/-- Non-vacuity of the general Katz–Trevisan lower bound on the Hadamard code. -/
example :
    ((1 / 8 : ℝ) * (1 / 4 : ℝ) ^ (2 * 2 + 1) /
      ((2 : ℝ) ^ 2 * (Fintype.card Bool : ℝ) ^ ((2 - 1) * (2 * 2 + 1)) *
        (4 * Real.logb 2 (Fintype.card Bool)) ^ 2)) ^ (1 / ((2 : ℝ) - 1)) *
      (Fintype.card (Fin 3) : ℝ) ^ ((2 : ℝ) / ((2 : ℝ) - 1)) ≤
    Fintype.card (Fin 3 → Bool) :=
  isLocalDecoder_hadamard.isLocallyDecodable.rpow_le_card le_rfl (by decide)
    (by norm_num) (by norm_num)

/-- Explicit Katz–Trevisan quadratic bound for binary `(2, 1/4, 1/4)` locally decodable codes:
every (possibly adaptive) such code satisfies `k² ≤ 8388608 · n`. -/
example {k n : ℕ} (C : (Fin k → Bool) → Fin n → Bool)
    (hC : IsLocallyDecodable C 2 (1 / 4) (1 / 4)) :
    (k : ℝ) ^ 2 ≤ 8388608 * (n : ℝ) := by
  have h := hC.rpow_le_card le_rfl (by decide) (by norm_num) (by norm_num)
  have hlog : Real.logb 2 (Fintype.card Bool : ℝ) = 1 := by
    rw [Fintype.card_bool, Nat.cast_ofNat, Real.logb_self_eq_one one_lt_two]
  rw [hlog, Fintype.card_bool, Fintype.card_fin, Fintype.card_fin] at h
  have hexp1 : (1 / (((2 : ℕ) : ℝ) - 1)) = 1 := by norm_num
  have hexp2 : (((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) - 1)) = 2 := by norm_num
  rw [hexp1, hexp2, Real.rpow_one, Real.rpow_two] at h
  norm_num at h
  linarith

/-- Superlinear impossibility from Katz–Trevisan: no linear-rate (`n = k`) binary code of
`10^7` message bits is a `(2, 1/4, 1/4)` locally decodable code (adaptive or not). -/
example (C : (Fin 10000000 → Bool) → Fin 10000000 → Bool) :
    ¬ IsLocallyDecodable C 2 (1 / 4) (1 / 4) := by
  intro hC
  have h := hC.rpow_le_card le_rfl (by decide) (by norm_num) (by norm_num)
  have hlog : Real.logb 2 (Fintype.card Bool : ℝ) = 1 := by
    rw [Fintype.card_bool, Nat.cast_ofNat, Real.logb_self_eq_one one_lt_two]
  rw [hlog, Fintype.card_bool, Fintype.card_fin] at h
  have hexp1 : (1 / (((2 : ℕ) : ℝ) - 1)) = 1 := by norm_num
  have hexp2 : (((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) - 1)) = 2 := by norm_num
  rw [hexp1, hexp2, Real.rpow_one, Real.rpow_two] at h
  norm_num at h

end CslibFrontierTests.LocallyDecodable
