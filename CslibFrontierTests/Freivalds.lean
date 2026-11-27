/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Init
import CslibFrontier.Algorithms.Lean.Freivalds
import CslibFrontier.Algorithms.WordRAM.Freivalds
meta import CslibFrontier.Algorithms.WordRAM.Freivalds
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Algebra.Field.ZMod
meta import Mathlib.Algebra.Field.ZMod

/-!
# Freivalds verifier tests

Ordinary-module client checks for both the pure `ProbComp` verifier
(`Cslib.Algorithms.Lean.Freivalds`) and the compiled randomized word-RAM verifier
(`Cslib.Algorithms.WordRAM.Freivalds`).
`A * B` and `C` below differ in one entry, so one vector exposes the error and another does not:
the verifier needs randomness, and its soundness error is not zero. A `1 × 1` instance accepts an
incorrect product with probability exactly `1/2`, so the `0`/`1` bound is attained on both the
pure `ProbComp` model (`eval_verify_one_true`) and the compiled word-RAM program
(`verifyProgram_one_true`). Zero-dimension (`0 × 0` and `2 × 0`) instances check the `cols = 0`
encoding branch and zero-trip loop exits. Over `ZMod 4` the encoding `id` violates the injectivity
hypothesis, and the counting bound it supports fails there; the `0`/`1` encoding satisfies it.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace CslibFrontierTests.Freivalds

open Cslib Cslib.Algorithms.Lean.Freivalds Cslib.Probability Cslib.WordRAM
open Cslib.Algorithms.WordRAM.Freivalds
open scoped Matrix ENNReal

private def A : Matrix (Fin 2) (Fin 2) ℤ := !![1, 2; 3, 4]
private def B : Matrix (Fin 2) (Fin 2) ℤ := !![5, 6; 7, 8]
/-- `A * B = !![19, 22; 43, 50]`; `C` is wrong only in the bottom-right entry. -/
private def C : Matrix (Fin 2) (Fin 2) ℤ := !![19, 22; 43, 51]

/-! ## Executable checks on pure `check` -/

-- The correct product passes on every vector.
#guard check A B !![19, 22; 43, 50] ![1, 1]
-- The vector `(1, 0)` misses the wrong entry, `(0, 1)` exposes it.
#guard check A B C ![1, 0]
#guard !check A B C ![0, 1]

/-! ## Completeness and soundness on the pure `ProbComp` model -/

theorem mul_ne : A * B ≠ C := by decide

example (k : ℕ) : ProbComp.eval (verify bit k A B !![19, 22; 43, 50]) = PMF.pure true :=
  eval_verify_of_mul_eq _ _ (by decide)

example : ProbComp.eval (verify bit 10 A B C) true ≤ 2⁻¹ ^ 10 :=
  eval_verify_bool_true_le 10 mul_ne

/-! ## Finite-field soundness -/

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def A5 : Matrix (Fin 2) (Fin 3) (ZMod 5) := !![1, 2, 3; 4, 0, 1]
private def B5 : Matrix (Fin 3) (Fin 2) (ZMod 5) := !![1, 0; 2, 1; 0, 3]
private def C5 : Matrix (Fin 2) (Fin 2) (ZMod 5) := !![0, 0; 0, 0]

example : ProbComp.eval (verify id 3 A5 B5 C5) true ≤ (5⁻¹ : ℝ≥0∞) ^ 3 := by
  have h := eval_verify_field_true_le 3 (A := A5) (B := B5) (C := C5) (by decide)
  rwa [ZMod.card, Nat.cast_ofNat] at h

/-! ## The `1/2` bound is attained -/

/-- Over any nontrivial ring, with `A = B = [1]` and `C = [0]`, a single `0`/`1` trial accepts
with probability `1/2`, namely when the random bit is `0`. -/
theorem eval_verify_one_true {R : Type} [Ring R] [DecidableEq R] [Nontrivial R] :
    ProbComp.eval (verify bit 1 (1 : Matrix (Fin 1) (Fin 1) R) (1 : Matrix (Fin 1) (Fin 1) R) 0)
      true = 2⁻¹ := by
  classical
  rw [eval_verify, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_uniformOfFintype]
  have hfilter : (Finset.univ.filter fun xs : Fin 1 → Fin 1 → Bool => xs ∈
      (fun xs : Fin 1 → Fin 1 → Bool =>
        decide (∀ t, ((1 : Matrix (Fin 1) (Fin 1) R) * 1) *ᵥ (bit ∘ xs t) =
          (0 : Matrix (Fin 1) (Fin 1) R) *ᵥ (bit ∘ xs t))) ⁻¹' {true}) =
      {fun _ _ => false} := by
    ext xs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_preimage,
      Set.mem_singleton_iff, decide_eq_true_eq, Finset.mem_singleton, mul_one,
      Matrix.one_mulVec, Matrix.zero_mulVec]
    constructor
    · intro h
      funext t i
      have h0 := congrFun (h t) i
      rw [Subsingleton.elim t 0, Subsingleton.elim i 0] at h0 ⊢
      cases hx : xs 0 0
      · rfl
      · simp [hx, bit_true, one_ne_zero] at h0
    · intro h t
      funext i
      simp [h, bit_false]
  rw [hfilter, Finset.card_singleton, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool]
  norm_num

example :
    ProbComp.eval (verify bit 1 (1 : Matrix (Fin 1) (Fin 1) ℤ) (1 : Matrix (Fin 1) (Fin 1) ℤ) 0)
      true = 2⁻¹ :=
  eval_verify_one_true

/-! ## The encoding hypothesis -/

/-- Over `ZMod 4`, multiplying by `2` is not injective, so `id` is not an admissible encoding. -/
theorem not_injective_two_mul_zmod4 : ¬ Function.Injective fun s : ZMod 4 => (2 : ZMod 4) * s := by
  decide

/-- Without the hypothesis the counting bound fails: `M = [2]` and `N = [0]` agree on two of the
four vectors `x : Fin 1 → ZMod 4`, not on at most one. -/
example : (Finset.univ.filter fun x : Fin 1 → ZMod 4 =>
    (!![2] : Matrix (Fin 1) (Fin 1) (ZMod 4)) *ᵥ (id ∘ x) = (0 : Matrix (Fin 1) (Fin 1) _) *ᵥ
      (id ∘ x)).card * Fintype.card (ZMod 4) > Fintype.card (ZMod 4) ^ Fintype.card (Fin 1) := by
  decide

/-- The `0`/`1` encoding is admissible over `ZMod 4`, so the bound applies there with `1/2`. -/
example : (Finset.univ.filter fun x : Fin 1 → Bool =>
    (!![2] : Matrix (Fin 1) (Fin 1) (ZMod 4)) *ᵥ (bit ∘ x) = (0 : Matrix (Fin 1) (Fin 1) _) *ᵥ
      (bit ∘ x)).card * Fintype.card Bool ≤ Fintype.card Bool ^ Fintype.card (Fin 1) :=
  card_filter_mulVec_eq_mul_card_le injective_mul_bit (by decide)

/-! ## Randomized Word-RAM verifier checks -/

private def A2 : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![1, 0; 1, 1]
private def B2 : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![1, 1; 0, 1]
private def C2_ok : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![1, 1; 1, 0]
private def C2_bad : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![1, 1; 1, 1]

-- Encoding layout and non-vacuous word-fit check at width `w = 8` (`2^8 = 256`).
#guard encode 2 4 A2 B2 C2_ok =
  [2, 4, 2, 2, 2, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0]
#guard decide (Fits 8 (wordBound 2 4 2 2 2))
#guard decide (InputFits 8 (encode 2 4 A2 B2 C2_ok))

-- Deterministic `k = 0` execution on `verifyProgram` halts within `verifySquareTime 0 2 = 26`
-- instructions with output `1`.
#guard WordRAM.run 8 verifyProgram (verifySquareTime 0 2) (State.init (encode 2 0 A2 B2 C2_ok)) =
  some (1, 26)

/-- The `1/2` false-acceptance bound is attained on `verifyProgram` for `1 × 1` matrices over
`ZMod 2`. -/
theorem verifyProgram_one_true :
    let one1 : Matrix (Fin 1) (Fin 1) (ZMod 2) := 1
    let zero1 : Matrix (Fin 1) (Fin 1) (ZMod 2) := 0
    let T := verifySquareTime 1 1
    ((evalRand 8 verifyProgram T (State.init (encode 2 1 one1 one1 zero1))).map
      RandCfg.accepts) true = 2⁻¹ := by
  intro one1 zero1 T
  have hw : Fits 8 (wordBound 2 1 1 1 1) := by decide
  rw [(verifyProgram_spec one1 one1 zero1 hw (verifyTime_square_eq 1 1).le).2.2.2]
  exact eval_verify_one_true

-- Zero-dimension boundary runs (`0 × 0` and `2 × 2` by `2 × 0`, exercising `cols = 0` and
-- zero-trip loops).
private def zero00 : Matrix (Fin 0) (Fin 0) (ZMod 2) := 0
private def zero20 : Matrix (Fin 2) (Fin 0) (ZMod 2) := 0

#guard encode 2 3 zero00 zero00 zero00 = [2, 3, 0, 0, 0]
#guard (WordRAM.run 8 verifyProgram (verifySquareTime 3 0)
  (State.init (encode 2 3 zero00 zero00 zero00))).map Prod.fst = some 1
#guard (WordRAM.run 8 verifyProgram (verifyTime 2 2 2 0)
  (State.init (encode 2 2 A2 zero20 zero20))).map Prod.fst = some 1

/-- Zero-column (`n = 0`) specification check on `verifyProgram`: `0` `rand` calls and acceptance
with probability `1`. -/
example :
    let B0 : Matrix (Fin 2) (Fin 0) (ZMod 2) := 0
    let C0 : Matrix (Fin 2) (Fin 0) (ZMod 2) := 0
    let T := verifyTime 2 2 2 0
    RandHaltsWithin 8 verifyProgram (State.init (encode 2 2 A2 B0 C0)) T ∧
      RandCallsBounded 8 verifyProgram (State.init (encode 2 2 A2 B0 C0)) T 0 ∧
      (evalRand 8 verifyProgram T (State.init (encode 2 2 A2 B0 C0))).map RandCfg.accepts =
        PMF.pure true := by
  intro B0 C0 T
  have hw : Fits 8 (wordBound 2 2 2 2 0) := by decide
  obtain ⟨hhalt, hcalls, _, _⟩ := verifyProgram_spec A2 B0 C0 hw (T := T) le_rfl
  exact ⟨hhalt, hcalls, verifyProgram_accept_of_mul_eq (Subsingleton.elim _ _) hw le_rfl⟩

/-- Square `ZMod 2` completeness and `2 ^ (-4)` soundness at width `w = 8` within
`verifySquareTime 4 2` instructions and `8` random bit draws. -/
theorem wordRAM_zmod2_square_checks :
    let T := verifySquareTime 4 2
    RandHaltsWithin 8 verifyProgram (State.init (encode 2 4 A2 B2 C2_ok)) T ∧
      RandCallsBounded 8 verifyProgram (State.init (encode 2 4 A2 B2 C2_ok)) T 8 ∧
      RandBitsBounded 8 verifyProgram (State.init (encode 2 4 A2 B2 C2_ok)) T 8 ∧
      (evalRand 8 verifyProgram T (State.init (encode 2 4 A2 B2 C2_ok))).map RandCfg.accepts =
        PMF.pure true ∧
      ((evalRand 8 verifyProgram T (State.init (encode 2 4 A2 B2 C2_bad))).map RandCfg.accepts)
        true ≤ 2⁻¹ ^ 4 := by
  intro T
  have hw_ok : Fits 8 (wordBound 2 4 2 2 2) := by decide
  obtain ⟨hhalt, hcalls, hbits, hcomp, _⟩ :=
    verifyProgram_square_spec A2 B2 C2_ok hw_ok (T := T) le_rfl
  have hbad := verifyProgram_accept_le_of_mul_ne (A := A2) (B := B2) (C := C2_bad)
    (by decide) hw_ok (T := T) (verifyTime_square_eq 4 2).le
  exact ⟨hhalt, hcalls, hbits, hcomp (by decide), hbad⟩

/-- Rectangular `2 × 3` by `3 × 2` soundness over `ZMod 5` at width `w = 8`. -/
example :
    let T := verifyTime 3 2 3 2
    RandHaltsWithin 8 verifyProgram (State.init (encode 5 3 A5 B5 C5)) T ∧
      RandCallsBounded 8 verifyProgram (State.init (encode 5 3 A5 B5 C5)) T 6 ∧
      ((evalRand 8 verifyProgram T (State.init (encode 5 3 A5 B5 C5))).map RandCfg.accepts) true ≤
        2⁻¹ ^ 3 := by
  intro T
  have hw : Fits 8 (wordBound 5 3 2 3 2) := by decide
  obtain ⟨hhalt, hcalls, _, _⟩ := verifyProgram_spec A5 B5 C5 hw (T := T) le_rfl
  exact ⟨hhalt, hcalls, verifyProgram_accept_le_of_mul_ne (by decide) hw le_rfl⟩

/-- Composite modulus `ZMod 100` representing the `2 × 2` example `!![1, 2; 3, 4] * !![5, 6; 7, 8]`
without overflow at word width `w = 16`. -/
private def A100 : Matrix (Fin 2) (Fin 2) (ZMod 100) := !![1, 2; 3, 4]
private def B100 : Matrix (Fin 2) (Fin 2) (ZMod 100) := !![5, 6; 7, 8]
private def C100_bad : Matrix (Fin 2) (Fin 2) (ZMod 100) := !![19, 22; 43, 51]

example :
    let T := verifySquareTime 10 2
    RandHaltsWithin 16 verifyProgram (State.init (encode 100 10 A100 B100 C100_bad)) T ∧
      RandCallsBounded 16 verifyProgram (State.init (encode 100 10 A100 B100 C100_bad)) T 20 ∧
      ((evalRand 16 verifyProgram T (State.init (encode 100 10 A100 B100 C100_bad))).map
        RandCfg.accepts) true ≤ 2⁻¹ ^ 10 := by
  intro T
  have hw : Fits 16 (wordBound 100 10 2 2 2) := by decide
  obtain ⟨hhalt, hcalls, _, _, hsound⟩ :=
    verifyProgram_square_spec A100 B100 C100_bad hw (T := T) le_rfl
  exact ⟨hhalt, hcalls, hsound (by decide)⟩

end CslibFrontierTests.Freivalds
