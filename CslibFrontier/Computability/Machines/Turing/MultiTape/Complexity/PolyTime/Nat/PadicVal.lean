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
    exact ite_decide h0 id' (ite_decide hmod (by fun_prop) id')
  obtain ⟨hefficient, hspec⟩ := iterate_spec (count := id)
    (init := fun n => (n, 0)) (encIn := encUnary) id' (by fun_prop) hstep
    (fun n i state => state.1 + state.2 ≤ n ∧ (n = 0 → state = (0, 0)) ∧
      (0 < n → 0 < state.1 ∧ (state.1 % 2 = 1 ∨ state.1 + i ≤ n) ∧
        padicValNat 2 state.1 + state.2 = padicValNat 2 n))
    (fun n => ⟨by simp, fun hn0 => by simp [hn0], fun hn => ⟨hn, Or.inr (by omega), by simp⟩⟩)
    (fun n i state _ ⟨hle, hz, hpos⟩ => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · obtain rfl := hz rfl
        simp [padicValStep]
      obtain ⟨hs1, hdisj, hval⟩ := hpos hn
      simp only [padicValStep, decide_eq_true_eq, hs1.ne', ↓reduceIte]
      split_ifs with hmod
      · have hd := Nat.dvd_of_mod_eq_zero hmod
        have := Nat.multiplicity_div hd
        have := one_le_multiplicity_of_dvd hs1.ne' hd
        simp only [Nat.padicValNat_def] at hval ⊢
        exact ⟨by omega, fun h => absurd h hn.ne', fun _ => ⟨by omega, by omega, by omega⟩⟩
      · exact ⟨hle, fun h => absurd h hn.ne', fun _ => ⟨hs1, Or.inl (by omega), hval⟩⟩)
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
    · simp [h.2.1 rfl, Nat.padicValNat_def]
    obtain ⟨hs1, hdisj, hval⟩ := h.2.2 hn
    rwa [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd (by omega), zero_add] at hval
  simpa only [Function.comp_def, id_eq, hresult] using hefficient.snd'

end Turing.MultiTapeTM.ComputableInPolyTime
