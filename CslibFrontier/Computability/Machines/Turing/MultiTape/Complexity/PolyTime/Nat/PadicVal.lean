/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time 2-adic valuation on unary naturals

Repeated division by two while the current value is positive and even counts the binary trailing
zeros `padicValNat 2 n` in at most `n` unary steps, keeping the encoded `(value, count)` pair
linearly bounded.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.unary_padicValNat_two`: `padicValNat 2` is polynomial
  time with unary input and output.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

private def padicValStep (state : ℕ × ℕ) : ℕ × ℕ :=
  if decide (state.1 = 0) then state
  else if decide (state.1 % 2 = 0) then (state.1 / 2, state.2 + 1)
  else state

/-- The 2-adic valuation `padicValNat 2` is polynomial-time with both input and output in unary. -/
@[fun_prop]
theorem unary_padicValNat_two :
    ComputableInPolyTime (padicValNat 2) encUnary encUnary := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstep : ComputableInPolyTime padicValStep (encPair encUnary encUnary)
      (encPair encUnary encUnary) := by
    unfold padicValStep
    have h0 : ComputableInPolyTime (fun state : ℕ × ℕ => decide (state.1 = 0))
        (encPair encUnary encUnary) encBool :=
      unary_eq' (fst encUnary encUnary) (const 0)
    have hmod : ComputableInPolyTime (fun state : ℕ × ℕ => decide (state.1 % 2 = 0))
        (encPair encUnary encUnary) encBool :=
      unary_eq' (unary_mod.comp ((fst encUnary encUnary).prod (const 2))) (const 0)
    have hnext : ComputableInPolyTime (fun state : ℕ × ℕ => (state.1 / 2, state.2 + 1))
        (encPair encUnary encUnary) (encPair encUnary encUnary) := by
      fun_prop
    exact ite_decide h0 id' (ite_decide hmod hnext id')
  obtain ⟨hefficient, hspec⟩ := iterate_spec (count := id)
    (init := fun n => (n, 0)) (encIn := encUnary) id' (by fun_prop) hstep
    (fun n i state => state.1 + state.2 ≤ n ∧ (n = 0 → state = (0, 0)) ∧
      (0 < n → 0 < state.1 ∧ (state.1 % 2 = 1 ∨ state.1 + i ≤ n) ∧
        padicValNat 2 state.1 + state.2 = padicValNat 2 n))
    (fun n => by
      refine ⟨by simp, fun hn0 => by simp [hn0], fun hn => ?_⟩
      exact ⟨hn, Or.inr (by omega), by simp⟩)
    (fun n i state _ h => by
      dsimp only [padicValStep]
      by_cases h0 : state.1 = 0
      · have h0_b : decide (state.1 = 0) = true := decide_eq_true h0
        simp only [h0_b, ↓reduceIte]
        refine ⟨h.1, h.2.1, fun hn_pos => ?_⟩
        exact absurd h0 (h.2.2 hn_pos).1.ne'
      · have h0_b : decide (state.1 = 0) = false := decide_eq_false h0
        simp only [h0_b, Bool.false_eq_true, ↓reduceIte]
        have hpos : 0 < n := Nat.pos_of_ne_zero fun hn0 => h0 (congrArg Prod.fst (h.2.1 hn0))
        obtain ⟨hs1, hdisj, hval⟩ := h.2.2 hpos
        by_cases hmod : state.1 % 2 = 0
        · have hmod_b : decide (state.1 % 2 = 0) = true := decide_eq_true hmod
          simp only [hmod_b, ↓reduceIte]
          have hdiv_pos : 0 < state.1 / 2 := by omega
          have hdiv_eq : state.1 = 2 * (state.1 / 2) := by omega
          have hprog : state.1 + i ≤ n := hdisj.resolve_left (by omega)
          have hdiv_val : padicValNat 2 state.1 = padicValNat 2 (state.1 / 2) + 1 := by
            simp only [Nat.padicValNat_def]
            conv_lhs => rw [hdiv_eq, Nat.multiplicity_mul (by decide) (by omega),
              Nat.Prime.multiplicity_self, add_comm]
          refine ⟨by omega, fun hn0 => absurd hn0 hpos.ne', fun _ => ?_⟩
          refine ⟨hdiv_pos, Or.inr (by omega), ?_⟩
          rw [hdiv_val] at hval
          omega
        · have hmod_b : decide (state.1 % 2 = 0) = false := decide_eq_false hmod
          simp only [hmod_b, Bool.false_eq_true, ↓reduceIte]
          exact ⟨h.1, fun hn0 => absurd hn0 hpos.ne', fun _ => ⟨hs1, Or.inl (by omega), hval⟩⟩)
    (size := fun n => 2 * n + 2)
    (polyBounded (show ComputableInPolyTime
      (fun n : ℕ => 2 * n + 2) encUnary encUnary from by fun_prop))
    (fun n i state _ h => by
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      omega)
  have hresult (n : ℕ) : (padicValStep^[n] (n, 0)).2 = padicValNat 2 n := by
    have h := hspec n
    simp only [id_eq] at h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [h.2.1 rfl]
      simp [Nat.padicValNat_def]
    · obtain ⟨hs1, hdisj, hval⟩ := h.2.2 hn
      have hodd : (padicValStep^[n] (n, 0)).1 % 2 = 1 :=
        hdisj.resolve_right (by omega)
      have hnot_dvd : ¬ 2 ∣ (padicValStep^[n] (n, 0)).1 :=
        Nat.dvd_iff_mod_eq_zero.not.mpr (by omega)
      have hzero : padicValNat 2 (padicValStep^[n] (n, 0)).1 = 0 := by
        rw [Nat.padicValNat_def]
        exact multiplicity_eq_zero_of_not_dvd hnot_dvd
      rw [hzero, zero_add] at hval
      exact hval
  simpa only [Function.comp_def, id_eq, hresult] using hefficient.snd'

end Turing.MultiTapeTM.ComputableInPolyTime
