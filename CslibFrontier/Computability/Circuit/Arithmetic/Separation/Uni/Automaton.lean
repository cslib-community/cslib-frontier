/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Util
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.Run
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Tape.ProgRun
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.Exact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The universal tape automaton

One tape automaton with one input evaluates every plain instance: on the word of an instance `z`,
its bits `Interpreter.tbits z` in preorder written with two different letters, its value in `t`
steps is the plain sum `Interpreter.pv θ z` whenever `z` is `τ`-plain and
`C * (|z| + τ) * lg (|z| + τ) ^ 2 ≤ t` (`Uni.exists_universal_automaton`). It is the automaton
that `Tape.exists_run_val` gives for the series of the universal machine
(`Uni.exists_series_universal`), whose input word is `tbits z` in the letters `Uni.Sy.bit`.

## Main results

* `Uni.exists_universal_automaton`: a universal tape automaton.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition I.1 (p. 49); module `Paper.Universal`. That the two letters are different is a
  separate theorem of the source (`universal_symbols_ne`, for a nonzero ring; p. 69), and here a
  part of the statement, for every ring
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Uni

open Finset Tape Interpreter

variable {A : Type} [CommRing A]

/-- **A universal tape automaton** (Proposition I.1). If only finitely many names have a nonzero
weight under `θ`, then there are a tape automaton with one input, two different letters `bt false`
and `bt true`, and a constant `C` such that the value of the automaton in `t` steps on the word of
an instance `z` (its bits `tbits z`, as the letters `bt`) is `pv θ z` whenever `z` is `τ`-plain
and `C * (|z| + τ) * lg (|z| + τ) ^ 2 ≤ t`. -/
theorem exists_universal_automaton (θ : List Bool → A) (hθ : (Function.support θ).Finite) :
    ∃ (S Γ Q : Type) (_ : Fintype S) (_ : DecidableEq S) (_ : Fintype Γ) (_ : DecidableEq Γ)
      (_ : Fintype Q) (_ : DecidableEq Q) (mu : Letter S Unit Γ → Matrix Q Q A) (i e : Q)
      (bt : Bool → Γ) (C : ℕ), Function.Injective bt ∧
        ∀ (τ : ℕ) (z : Tree) (t : ℕ), Plain θ τ z → C * (z.size + τ) * lg (z.size + τ) ^ 2 ≤ t →
          runVal mu i e t (fun _ => (tbits z).map bt) = pv θ z := by
  obtain ⟨S₀, hS₀, C, hC⟩ := exists_series_universal θ hθ.toFinset fun q hq => by simpa using hq
  obtain ⟨Q, iQ, dQ, mu, i, e, -, hrun⟩ := exists_run_val hS₀
  refine ⟨_, _, Q, inferInstance, inferInstance, inferInstance, inferInstance, iQ, dQ, mu, i, e,
    Sy.bit, 54 * C + 2, fun _ _ => Sy.bit.inj, fun τ z t hz ht => ?_⟩
  obtain ⟨hbdd, hval⟩ := hC τ z hz
  rw [← hval]
  refine hrun _ _ _ hbdd (le_trans ?_ ht)
  simp only [univ_unique, sum_singleton, List.length_map, length_tbits]
  set n := z.size + τ
  have hz1 : 1 ≤ z.size := Tree.size_pos z
  have hzn : z.size ≤ n := Nat.le_add_right _ _
  have hlg : lg (n + 2) ≤ 3 * lg n := by
    have h := Nat.log_mono_right (b := 2) (show n + 2 ≤ n * 2 * 2 by omega)
    rw [Nat.log_mul_base one_lt_two (by omega), Nat.log_mul_base one_lt_two (by omega)] at h
    simp only [lg]
    omega
  have h1 : (n + 2) * lg (n + 2) ^ 2 ≤ 27 * (n * lg n ^ 2) :=
    calc (n + 2) * lg (n + 2) ^ 2 ≤ (3 * n) * (3 * lg n) ^ 2 := by gcongr; omega
      _ = 27 * (n * lg n ^ 2) := by ring
  have h2 : n ≤ n * lg n ^ 2 := Nat.le_mul_of_pos_right _ (by simp [lg])
  linarith [Nat.mul_le_mul_left C h1]

end Cslib.Circuits.Arithmetic.Separation.Uni
