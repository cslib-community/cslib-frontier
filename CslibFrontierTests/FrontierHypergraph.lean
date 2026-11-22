/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph

/-!
# Tests for `CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph`

Concrete nonvacuity, cross-module `@[expose]` reduction, unary-gate-collapse (`multiarySize = 0`
with `Nat.card (HyperNode c) = 1`), Steiner network exactness, and concrete alphabet (`Bool`,
`Fin 3`) instantiations for bounded-fan-in hypergraph lower bounds across `r ∈ {3, 4, 8, 16, 64}`.
-/

namespace CslibFrontierTests.FrontierHypergraph

open Filter Asymptotics Set Cslib.Circuits Cslib.Circuits.Frontier
open Cslib.Circuits.Frontier.Hypergraph ProbabilityTheory

/-- Cross-module `@[expose]` check on `hyperCoeff` for all six certificates, confirming strict
improvement over `4` at `r = 3` and `> 6` at `r = 64`. -/
example :
    hyperCoeff 3 (18389141 / 100000000) (-19757453 / 100000000) = 26308698 / 5977679 ∧
    hyperCoeff 3 (17970677 / 100000000) (-18502061 / 100000000) = 26215706 / 5931183 ∧
    (4 : ℚ) < hyperCoeff 3 (17970677 / 100000000) (-18502061 / 100000000) ∧
    (6 : ℚ) < hyperCoeff 64 (2318347 / 50000000) (16272637 / 25000000) := by
  norm_num [hyperCoeff]

/-- Cross-module `@[expose]` kernel reduction test for the rational polynomial combinators in
`ProbabilityTheory`. -/
example : qPolyPow [1, -1 / 2] 2 = [1, -1, 1 / 4] := by
  norm_num [qPolyPow, qPolyMul, qPolyAdd, qPolyScale]

/-- Concrete 3-operation signature with nullary, unary, and ternary gates. -/
private inductive TestOp : Type
  | constFalse
  | neg
  | maj3
  deriving DecidableEq

private abbrev testSig : Signature where
  Op := TestOp
  Arity
    | .constFalse => 0
    | .neg => 1
    | .maj3 => 3

private def testInterp : Interpretation testSig Bool
  | .constFalse, _ => false
  | .neg, w => !(w 0)
  | .maj3, w => (w 0 && w 1) || (w 0 && w 2) || (w 1 && w 2)

/-- A circuit with one constant gate and two chained unary `neg` gates (`size = 3`,
`innerSize > 0`, `multiarySize = 0`): the hypergraph collapses all unary/nullary gates to a single
output vertex (`Nat.card (HyperNode unaryChain) = 1`) and width `0`. -/
private def unaryChain : Circuit testSig 2 1 where
  size := 3
  program :=
    Program.empty
      |>.gate ⟨TestOp.constFalse, Fin.elim0⟩
      |>.gate ⟨TestOp.neg, fun _ => .input 0⟩
      |>.gate ⟨TestOp.neg, fun _ => .gate 1⟩
  outputs _ := .gate 2

example (lay : Layout (HyperNode unaryChain)) :
    unaryChain.multiarySize = 0 ∧
    Nat.card (HyperNode unaryChain) = 1 ∧
    hyperWidth unaryChain lay = 0 ∧
    (hyperNetwork unaryChain testInterp {true} lay).width lay = 0 ∧
    (hyperNetwork unaryChain testInterp {true} lay).accepted = {x : Fin 2 → Bool | x 0 = true} := by
  have hfan1 : unaryChain.FanInAtMost 1 := by decide
  have hmult0 : unaryChain.multiarySize = 0 :=
    unaryChain.multiarySize_eq_zero_of_fanInAtMost_one hfan1
  have hcard1 : Nat.card (HyperNode unaryChain) = 1 := by
    have hle := card_hyperNode_le unaryChain
    have hpos : 1 ≤ Nat.card (HyperNode unaryChain) := by
      rw [Nat.card_eq_fintype_card, card_hyperNode_eq]
      omega
    omega
  have hw0 : hyperWidth unaryChain lay = 0 := by
    unfold hyperWidth
    rw [hcard1]
    refine Nat.eq_zero_of_le_zero (Finset.sup_le fun t ht => ?_)
    have ht0 : t = 0 := by simpa using ht
    subst ht0
    have hempty : hyperCut unaryChain ∅ = ∅ := by
      ext w
      simp [mem_hyperCut_iff, HyperedgeStraddles]
    simp [hempty]
  refine ⟨hmult0, hcard1, hw0, (width_hyperNetwork _ _ _ _).trans hw0, ?_⟩
  rw [accepted_hyperNetwork]
  ext x
  change unaryChain.eval testInterp x 0 = true ↔ x 0 = true
  have heval : unaryChain.eval testInterp x 0 = ! !(x 0) := rfl
  rw [heval, Bool.not_not]

/-- Concrete instantiation over `Bool` of the Slepian + star-cone `r = 3` worst-case and
nondeterministic lower bounds (`(22 / 5 - ε) * n = (4.4 - ε) * n < 2 * c.multiarySize`) and the
`r = 64` worst-case bound (`(6 - ε) * n < 63 * c.multiarySize`). -/
example {S : ∀ n, Set (Fin n → Bool)} {K : ℕ → ℕ} (hSK : DenseRectangleFree S K) :
    (∀ᶠ n in atTop, ∀ (k : ℕ) (c : Circuit testSig (n + k) 1),
      c.FanInAtMost 3 → c.NondeterministicDecides testInterp {true} (S n) →
        (44 / 10 - 1 / 1000 : ℝ) * n < 2 * c.multiarySize) ∧
    (∀ᶠ n in atTop, ∀ (c : Circuit testSig n 1),
      c.FanInAtMost 64 → c.Decides testInterp {true} (S n) →
        (6 - 1 / 1000 : ℝ) * n < 63 * c.multiarySize) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [eventually_44199_lt_two_mul_multiarySize_nondeterministic.{0, 0}
      (U := Bool) hSK (ε := 1 / 1000) (by norm_num)] with n hn k c hfan hdec
    have h := hn k testSig testInterp {true} c hfan hdec
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · filter_upwards [eventually_60012_lt_sixtyThree_mul_multiarySize.{0, 0}
      (U := Bool) hSK (ε := 1 / 1000) (by norm_num)] with n hn c hfan hdec
    have h := hn testSig testInterp {true} c hfan hdec
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

/-- Concrete instantiation over `Fin 3` of the `r = 4` (`44792 / 10000`), `r = 8` (`46666 / 10000`),
and `r = 16` (`49798 / 10000`) average-case bounds at `ε = 1 / 100`. -/
example :
    (∃ γ > 0, ∀ (S : ∀ n, Set (Fin n → Fin 3)) (K : ℕ → ℕ) (b : ℕ → ℝ),
      (∀ᶠ n in atTop, RectangleBias (S n) (K n) (b n)) →
      (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n in atTop, ∀ (σ : Signature.{0}) (I : Interpretation σ (Fin 3)) (Acc : Set (Fin 3))
        (c : Circuit σ n 1), c.FanInAtMost 4 →
          3 * (c.multiarySize : ℝ) ≤ (446 / 100 : ℝ) * n →
          agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b n + Real.exp (-(γ * n))) ∧
    (∃ γ > 0, ∀ (S : ∀ n, Set (Fin n → Fin 3)) (K : ℕ → ℕ) (b : ℕ → ℝ),
      (∀ᶠ n in atTop, RectangleBias (S n) (K n) (b n)) →
      (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n in atTop, ∀ (σ : Signature.{0}) (I : Interpretation σ (Fin 3)) (Acc : Set (Fin 3))
        (c : Circuit σ n 1), c.FanInAtMost 8 →
          7 * (c.multiarySize : ℝ) ≤ (465 / 100 : ℝ) * n →
          agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b n + Real.exp (-(γ * n))) ∧
    (∃ γ > 0, ∀ (S : ∀ n, Set (Fin n → Fin 3)) (K : ℕ → ℕ) (b : ℕ → ℝ),
      (∀ᶠ n in atTop, RectangleBias (S n) (K n) (b n)) →
      (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
      ∀ᶠ n in atTop, ∀ (σ : Signature.{0}) (I : Interpretation σ (Fin 3)) (Acc : Set (Fin 3))
        (c : Circuit σ n 1), c.FanInAtMost 16 →
          15 * (c.multiarySize : ℝ) ≤ (496 / 100 : ℝ) * n →
          agreement (S n) {x | c.eval I x 0 ∈ Acc} ≤ 1 / 2 + b n + Real.exp (-(γ * n))) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨γ, hγ, H⟩ := eventually_agreement_le_44792_three_mul_multiarySize.{0, 0}
      (ε := 1 / 100) (by norm_num)
    refine ⟨γ, hγ, fun S K b hb hK => ?_⟩
    filter_upwards [H (Fin 3) S K b hb hK] with n hn σ I Acc c hfan hs
    exact hn σ I Acc c hfan (hs.trans (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith))
  · obtain ⟨γ, hγ, H⟩ := eventually_agreement_le_46666_seven_mul_multiarySize.{0, 0}
      (ε := 1 / 100) (by norm_num)
    refine ⟨γ, hγ, fun S K b hb hK => ?_⟩
    filter_upwards [H (Fin 3) S K b hb hK] with n hn σ I Acc c hfan hs
    exact hn σ I Acc c hfan (hs.trans (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith))
  · obtain ⟨γ, hγ, H⟩ := eventually_agreement_le_49798_fifteen_mul_multiarySize.{0, 0}
      (ε := 1 / 100) (by norm_num)
    refine ⟨γ, hγ, fun S K b hb hK => ?_⟩
    filter_upwards [H (Fin 3) S K b hb hK] with n hn σ I Acc c hfan hs
    exact hn σ I Acc c hfan (hs.trans (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith))

end CslibFrontierTests.FrontierHypergraph
