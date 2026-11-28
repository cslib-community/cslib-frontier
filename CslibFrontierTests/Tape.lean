/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Samuel Schlesinger
-/

module
-- upstream: local-only

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.ProgRun
import CslibFrontier.Foundations.Data.List.StairRefinement
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.RunGood
import CslibFrontier.Foundations.LinearAlgebra.Matrix.ListProd
import Mathlib.Data.List.ReduceOption

/-! Tests of the weighted automata / tape-channel layer (M1, part 1/3):
rational series bounds (`RatLe`), multi-channel projection and matched runs (`emit`, `Matched`),
common staircase refinement (`IsRef` holding and non-`Stair` rejection), matched-run certificate
witness (`exists_good`), and path expansion via `Matrix.list_prod_ofFn_apply`. -/

namespace CslibFrontierTests.Tape

open Cslib.Automata.Weighted
open Cslib.Circuits.Arithmetic.Separation.Tape
open List.StairRefinement

/-! ### Linear representations and rational series -/

/-- A one-word series over `Bool` has dimension at most `2 * len + 1`. -/
example : RatLe (2 * 2 + 1) (Series.word [true, false] : Series ℤ Bool) :=
  RatLe.word [true, false]

/-- Evaluation of `Series.word` at matching and mismatched words. -/
example :
    (Series.word [true, false] : Series ℤ Bool) [true, false] = 1 ∧
      (Series.word [true, false] : Series ℤ Bool) [false, true] = 0 := by
  decide

/-! ### Common refinement (staircase matrices) -/

/-- Concrete `2 × 2` staircase refinement of `[true, false] ++ [true] = [true] ++ [false, true]`. -/
example :
    let A : Fin 2 → List Bool := ![ [true, false], [true] ]
    let B : Fin 2 → List Bool := ![ [true], [false, true] ]
    let X : Fin 2 → Fin 2 → List Bool :=
      fun i j =>
        match i, j with
        | 0, 0 => [true]
        | 0, 1 => [false]
        | 1, 0 => []
        | 1, 1 => [true]
    IsRef A B X := by
  refine ⟨?_, ?_, ?_⟩
  · intro a a' b b' h1 h2 hlt
    fin_cases a <;> fin_cases a' <;> fin_cases b <;> fin_cases b' <;> simp_all
  · intro a; fin_cases a <;> rfl
  · intro b; fin_cases b <;> rfl

/-- Anti-diagonal non-empty support fails `Stair` (negative check). -/
example :
    ¬ Stair (fun i j : Fin 2 =>
      match i, j with
      | 0, 1 => [true]
      | 1, 0 => [false]
      | _, _ => []) := by
  intro h
  have hle := h 0 1 1 0 (by simp) (by simp) (by decide)
  exact absurd hle (by decide)

/-! ### Channel projection, matched runs, and certificates -/

/-- A balanced tape run matches equal words on both sides of `Unit` and the single input `u`. -/
example :
    let o : List (Letter Unit (Fin 1) Bool) :=
      [ some (.tp () false, true)
      , some (.tp () true, true)
      , some (.inp 0, false)
      , none ]
    let u : Fin 1 → List Bool := fun _ => [false]
    Matched o u := by
  refine ⟨fun s => ?_, fun j => ?_⟩
  · cases s; simp [emit, proj]
  · fin_cases j; simp [emit, proj]

/-- Unbalanced tape run fails `Matched` (negative check). -/
example :
    ¬ Matched ([some (.tp () false, true)] : List (Letter Unit (Fin 1) Bool))
      (fun _ => []) := by
  rintro ⟨h1, -⟩
  have htp := h1 ()
  simp [emit, proj] at htp

/-- Every matched run yields a valid `Good` certificate when `N + t < M`. -/
example :
    let u : Fin 1 → List Bool := fun _ => [false]
    let o : Fin 3 → Letter Unit (Fin 1) Bool :=
      ![some (.tp () false, true), some (.tp () true, true), some (.inp 0, false)]
    let q : Fin 4 → Unit := fun _ => ()
    ∃ (P : Ch Unit (Fin 1) → Fin 4 → Fin 6) (c : Unit → Fin 6 → Option Bool),
      Good () () (code 2 u) o q P c := by
  refine exists_good (N := 2) (M := 6) (by decide) (by decide) ?_ rfl rfl
  refine ⟨fun s => ?_, fun j => ?_⟩
  · cases s; simp [emit, proj]
  · fin_cases j; simp [emit, proj]

/-- `Matrix.list_prod_ofFn_apply` replaces `Nc.RunGood.prod_ofFn_apply` directly via
`List.map_ofFn`. -/
example {F Q A : Type*} [CommRing F] [Fintype Q] [DecidableEq Q]
    (mu : A → Matrix Q Q F) (t : ℕ) (o : Fin t → A) (i e : Q) :
    ((List.ofFn o).map mu).prod i e = ∑ q : Fin (t + 1) → Q,
      if q 0 = i ∧ q (Fin.last t) = e then
        ∏ τ : Fin t, mu (o τ) (q τ.castSucc) (q τ.succ)
      else 0 := by
  rw [List.map_ofFn]
  exact Matrix.list_prod_ofFn_apply (fun τ => mu (o τ)) i e

end CslibFrontierTests.Tape
