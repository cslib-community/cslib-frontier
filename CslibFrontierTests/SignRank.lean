/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (regression tests)

import CslibFrontier.Computability.Communication.Equality
import CslibFrontier.Computability.Communication.PaturiSimon
import Mathlib.Tactic.FinCases

/-!
Regression clients for sign-rank and unbounded-error communication under module encapsulation:
sign-representations that hold and fail, the exact sign-rank of equality across input sizes,
protocols that solve and fail to solve with unbounded error, both directions of the Paturi–Simon
theorem (including the sharpened leaf-output lower bound), and the exact unbounded-error cost of
equality (`2` on two inputs, `3` on three or more).
-/

set_option linter.privateModule false

open Cslib Cslib.Communication Finset

namespace SignRankTests

/-! ### Sign-representations -/

-- The sign matrix sign-represents its function, and `3 •` it does too.
example : SignRepresents (signMatrix ℝ (equality (X := Fin 2))) equality :=
  signRepresents_signMatrix _

example : SignRepresents ((3 : ℝ) • signMatrix ℝ (equality (X := Fin 2))) equality :=
  (signRepresents_signMatrix _).smul (by norm_num)

-- The zero matrix sign-represents nothing: its entries are not negative where `f` is true.
example (f : Fin 2 → Fin 2 → Bool) : ¬SignRepresents (0 : Matrix (Fin 2) (Fin 2) ℝ) f :=
  fun h => h.ne_zero 0 0 rfl

-- A matrix with the wrong sign at one entry does not sign-represent equality.
example : ¬SignRepresents (Matrix.of fun (_ : Fin 2) (_ : Fin 2) => (-1 : ℝ)) equality := by
  intro h
  have := h.pos_of_false (x := 0) (y := 1) (by decide)
  norm_num at this

/-! ### Sign-rank of equality -/

/-- On two inputs, equality is sign-represented by the rank-one matrix `-u x * u y` with
`u = (1, -1)`. -/
theorem signRank_equality_fin_two : signRank (equality (X := Fin 2)) = 1 := by
  refine le_antisymm ?_ (signRank_pos _)
  let U : Matrix (Fin 2) (Fin 1) ℝ := Matrix.of fun x _ => ![1, -1] x
  let V : Matrix (Fin 1) (Fin 2) ℝ := Matrix.of fun _ y => ![-1, 1] y
  have h : SignRepresents (U * V) equality := by
    intro x y
    fin_cases x <;> fin_cases y <;>
      simp [U, V, Matrix.mul_apply, equality]
  simpa using signRank_le_card_of_mul h

/-- On three inputs, equality has sign-rank exactly two: the lower bound is
`two_le_signRank_equality`, and three vectors in the plane at mutual angles of `120°` give a
sign-representation of rank two. -/
theorem signRank_equality_fin_three : signRank (equality (X := Fin 3)) = 2 := by
  refine le_antisymm ?_ (two_le_signRank_equality (by simp))
  let U : Matrix (Fin 3) (Fin 2) ℝ := Matrix.of fun x i => ![![1, 0], ![-1, 2], ![-1, -2]] x i
  let V : Matrix (Fin 2) (Fin 3) ℝ := Matrix.of fun i y => -![![1, 0], ![-1, 2], ![-1, -2]] y i
  have h : SignRepresents (U * V) equality := by
    intro x y
    fin_cases x <;> fin_cases y <;>
      simp [U, V, Matrix.mul_apply, Fin.sum_univ_two, equality] <;> norm_num
  simpa using signRank_le_card_of_mul h

-- On four or more inputs, equality has sign-rank exactly three.
theorem signRank_equality_fin_four : signRank (equality (X := Fin 4)) = 3 :=
  signRank_equality_eq_three (by decide)

example : signRank (equality (X := Fin 1024)) = 3 :=
  signRank_equality_eq_three (by simp)

-- Sign-rank is at most rank: equality on `Fin 5` has sign-rank at most `5`, and at most `3`.
example : signRank (equality (X := Fin 5)) ≤ 5 := by
  simpa using signRank_le_card_left (equality (X := Fin 5))

example : signRank (equality (X := Fin 5)) ≤ 3 := signRank_equality_le_three

-- Monotonicity under submatrices: restricting equality on `Fin 5` to `Fin 3`.
example : signRank (fun x y : Fin 3 => equality (Fin.castLE (by omega) x : Fin 5)
    (Fin.castLE (by omega) y)) ≤ signRank (equality (X := Fin 5)) :=
  signRank_comap_le _ _ _

/-! ### Unbounded-error protocols -/

/-- A deterministic protocol for equality on `Bool`, read as a private-coin protocol with no
random bits: Alice sends her bit and Bob announces whether it equals his. -/
private def eqBool : PrivateCoin 0 0 Bool Bool Bool :=
  .alice (fun xr => xr.1) (.bob (fun yr => yr.1) (.output true) (.output false))
    (.bob (fun yr => yr.1) (.output false) (.output true))

private theorem eqBool_run (x y : Bool) (r : BitString 0) (s : BitString 0) :
    eqBool.run (x, r) (y, s) = equality x y := by
  cases x <;> cases y <;> rfl

-- It solves equality with unbounded error (its error is zero).
example : eqBool.SolvesUnbounded (fun x y z => equality x y = z) Set.univ Set.univ := by
  intro x _ y _
  classical
  rw [PrivateCoin.errorProb_eq_card]
  simp [eqBool_run]

/-- A protocol that answers `true` on every input, with no communication. -/
private def alwaysTrue : PrivateCoin 0 0 Bool Bool Bool := .output true

-- It does not solve equality with unbounded error: on `true ≠ false` its error is `1`.
example : ¬alwaysTrue.SolvesUnbounded (fun x y z => equality x y = z) Set.univ Set.univ := by
  intro h
  have := h true trivial false trivial
  classical
  rw [PrivateCoin.errorProb_eq_card] at this
  simp [alwaysTrue, equality] at this
  norm_num at this

/-- A fair coin: Alice's single random bit is the answer, with no communication. -/
private def fairCoin : PrivateCoin 1 0 Bool Bool Bool :=
  .alice (fun xr => xr.2 0) (.output false) (.output true)

-- It has error exactly `1 / 2` on every input, so it does not solve equality with unbounded
-- error, even though it is correct "half of the time".
example : ¬fairCoin.SolvesUnbounded (fun x y z => equality x y = z) Set.univ Set.univ := by
  intro h
  have := (PrivateCoin.errorProb_lt_half_iff fairCoin equality true true).mp
    (h true trivial true trivial)
  have hsum : ∑ s : BitString 1, ∑ t : BitString 0,
      BitString.signVal (fairCoin.run (true, s) (true, t)) = 0 := by
    rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
    simp [fairCoin]
  rw [hsum, mul_zero] at this
  exact lt_irrefl _ this

/-! ### The Paturi–Simon theorem -/

-- The upper bound: equality on any finite set costs at most three bits with unbounded error,
-- and on three or more inputs it costs exactly three bits.
example : PrivateCoin.uppComplexityFun (equality (X := Fin 1024)) ≤ 3 :=
  PrivateCoin.uppComplexityFun_equality_le_three

example : PrivateCoin.uppComplexityFun (equality (X := Fin 3)) = 3 :=
  PrivateCoin.uppComplexityFun_equality_eq_three (by decide)

example : PrivateCoin.uppComplexityFun (equality (X := Fin 4)) = 3 :=
  PrivateCoin.uppComplexityFun_equality_eq_three (by decide)

example : PrivateCoin.uppComplexityFun (equality (X := Fin 1024)) = 3 :=
  PrivateCoin.uppComplexityFun_equality_eq_three (by simp)

-- Sharpness of `2 < Fintype.card X`: on two inputs (`Bool`), equality costs exactly two bits.
example : PrivateCoin.uppComplexityFun (equality (X := Bool)) = 2 := by
  refine le_antisymm ?_ (PrivateCoin.le_uppComplexityFun_iff.mpr fun a b P hP => ?_)
  · have hsol : eqBool.SolvesUnbounded (fun x y z => equality x y = z) Set.univ Set.univ := by
      intro x _ y _
      classical
      rw [PrivateCoin.errorProb_eq_card]
      simp [eqBool_run]
    exact (PrivateCoin.uppComplexityFun_le_depth hsol).trans (by decide)
  · by_contra! hd
    have hd' : P.depth ≤ 1 := by
      have : P.depth < 2 := by exact_mod_cast hd
      omega
    have htt := (PrivateCoin.errorProb_lt_half_iff P equality true true).mp
      (hP true trivial true trivial)
    have htf := (PrivateCoin.errorProb_lt_half_iff P equality true false).mp
      (hP true trivial false trivial)
    have hft := (PrivateCoin.errorProb_lt_half_iff P equality false true).mp
      (hP false trivial true trivial)
    simp only [signMatrix_apply, equality, decide_true, ite_true, Bool.true_eq_false,
      Bool.false_eq_true, decide_false, ite_false, neg_one_mul, one_mul, neg_pos] at htt htf hft
    rcases P with z | ⟨sA, q₀, q₁⟩ | ⟨sB, q₀, q₁⟩
    · simp only [Protocol.run_output] at htt htf
      linarith
    · simp only [Protocol.depth_alice] at hd'
      rcases q₀ with z₀ | _ | _ <;>
        try (simp only [Protocol.depth_alice, Protocol.depth_bob] at hd'; omega)
      rcases q₁ with z₁ | _ | _ <;>
        try (simp only [Protocol.depth_alice, Protocol.depth_bob] at hd'; omega)
      simp only [Protocol.run_alice, Protocol.run_output] at htt htf
      linarith
    · simp only [Protocol.depth_bob] at hd'
      rcases q₀ with z₀ | _ | _ <;>
        try (simp only [Protocol.depth_alice, Protocol.depth_bob] at hd'; omega)
      rcases q₁ with z₁ | _ | _ <;>
        try (simp only [Protocol.depth_alice, Protocol.depth_bob] at hd'; omega)
      simp only [Protocol.run_bob, Protocol.run_output] at htt hft
      linarith

-- Sharpness of `2 ≤ signRank f` in `clog_signRank_add_one_le_uppComplexityFun`: a constant
-- function on `Bool` has sign-rank `1` and unbounded-error complexity `0`.
example : signRank (fun _ _ : Bool => false) = 1 ∧
    PrivateCoin.uppComplexityFun (fun _ _ : Bool => false) = 0 := by
  refine ⟨le_antisymm ?_ (signRank_pos _), nonpos_iff_eq_zero.mp ?_⟩
  · simpa [communicationMatrix] using
      (signRank_le_rank_communicationMatrix_add_one (fun _ _ : Bool => false)).trans
        (by simp [show communicationMatrix ℝ (fun _ _ : Bool => false) = 0 by ext; simp])
  · have h0 : PrivateCoin.SolvesUnbounded (X := Bool) (Y := Bool) (a := 0) (b := 0)
        (Protocol.output false) (fun _ _ z => false = z) Set.univ Set.univ := by
      intro x _ y _
      classical
      rw [PrivateCoin.errorProb_eq_card]
      simp
    exact (PrivateCoin.uppComplexityFun_le_depth h0).trans (by simp)

-- Deterministically, equality on `Fin 1024` costs `⌈log₂ 1024⌉ + 1 = 11` bits.
example : Protocol.ecomplexityFun (equality (X := Fin 1024)) = 11 := by
  rw [ecomplexityFun_equality (by simp), Fintype.card_fin]
  rfl

-- The lower bounds on a concrete function: equality on `Fin 3` has sign-rank two, so
-- `clog_signRank_le_uppComplexityFun` gives `1` bit and `clog_signRank_add_one_le_uppComplexityFun`
-- sharpens this to `2` bits.
example : (1 : ℕ∞) ≤ PrivateCoin.uppComplexityFun (equality (X := Fin 3)) := by
  have h := PrivateCoin.clog_signRank_le_uppComplexityFun (equality (X := Fin 3))
  rwa [signRank_equality_fin_three, show Nat.clog 2 2 = 1 by decide, Nat.cast_one] at h

example : (2 : ℕ∞) ≤ PrivateCoin.uppComplexityFun (equality (X := Fin 3)) := by
  have h := PrivateCoin.clog_signRank_add_one_le_uppComplexityFun
    (f := equality (X := Fin 3)) (by rw [signRank_equality_fin_three])
  rwa [signRank_equality_fin_three, show Nat.clog 2 2 = 1 by decide, Nat.cast_one,
    show (1 : ℕ∞) + 1 = 2 by rfl] at h

-- Both directions at once, on an arbitrary function on finite sets.
example (f : Fin 4 → Fin 6 → Bool) :
    (Nat.clog 2 (signRank f) : ℕ∞) ≤ PrivateCoin.uppComplexityFun f ∧
      PrivateCoin.uppComplexityFun f ≤ Nat.log 2 (signRank f) + 2 :=
  PrivateCoin.clog_signRank_le_uppComplexityFun_le f

-- The protocol form of the upper bound is nonvacuous: it produces a protocol.
example (f : Fin 4 → Fin 6 → Bool) : ∃ (a b : ℕ) (P : PrivateCoin a b (Fin 4) (Fin 6) Bool),
    P.SolvesUnbounded (fun x y z => f x y = z) Set.univ Set.univ ∧
      P.depth ≤ Nat.clog 2 (signRank f + 1) + 1 :=
  PrivateCoin.exists_solvesUnbounded_depth_le f

-- Unbounded error is the infimum of bounded error, and at most deterministic communication.
example (f : Fin 4 → Fin 6 → Bool) : PrivateCoin.uppComplexityFun f =
    ⨅ (ε : ℝ) (_ : ε < 1 / 2), PrivateCoin.ecomplexity ε (fun x y z => f x y = z) Set.univ
      Set.univ :=
  PrivateCoin.uppComplexity_eq_iInf

example (f : Fin 4 → Fin 6 → Bool) :
    PrivateCoin.uppComplexityFun f ≤ Protocol.ecomplexityFun f :=
  PrivateCoin.uppComplexityFun_le_protocol

end SignRankTests
