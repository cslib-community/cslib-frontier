/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (after crei/tidy-universal lands)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Comp
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.IterateWhile
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NormalForm
import Mathlib.Tactic.Linarith

/-!
# Iterating a polynomial-time step until it stops

A loop whose number of rounds is not known in advance: apply a polynomial-time `step` to a
polynomial-time start value until the result has the empty encoding, then apply a polynomial-time
`fin` to the last value before the empty one. Neither the number of rounds `r a` nor a bound on the
intermediate values needs to be computable. They only need to hold along the trajectory from the
start value of each instance. The loop then runs within time `c (r a + 1) N ^ d` and space
`c N ^ d`, where `N` is one more than a bound on the encoded intermediate values and the encoded
instance.

This is the loop of algorithms that iterate until a fixed point, such as breadth-first search until
no new element is found, where the number of rounds is bounded only through the analysis. It is
built from the machine-level loop `Turing.MultiTapeTM.iterateWhile`, which needs the round count
only along the trajectory.

## Main results

* `Turing.MultiTapeTM.exists_computableInTimeAndSpace_iterateWhile`: iterating a polynomial-time
  step until the empty encoding is computable within the number of rounds times a polynomial in
  the size of the intermediate values.
-/

public section

namespace Turing.MultiTapeTM

variable {α β γ : Type} {encIn : α ↪ List Bool} {encState : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- **Iterating a polynomial-time step until it stops.** Let `init`, `step` and `fin` be
polynomial-time, and along the trajectory from `init a` let `step` produce a value with the empty
encoding first after `r a + 1` rounds, with the values up to round `r a` encoded within `l a` bits.
Then `fin` of the value after `r a` rounds is computable within time `c (r a + 1) N ^ d` and space
`c N ^ d`, for `N = l a + |encIn a| + 1`. Neither `r` nor `l` needs to be computable. -/
theorem exists_computableInTimeAndSpace_iterateWhile {init : α → β} {step : β → β} {fin : β → γ}
    (hinit : ComputableInPolyTime init encIn encState)
    (hstep : ComputableInPolyTime step encState encState)
    (hfin : ComputableInPolyTime fin encState encOut) {r l : α → ℕ}
    (hl : ∀ a, ∀ n ≤ r a, (encState (step^[n] (init a))).length ≤ l a)
    (hne : ∀ a, ∀ n < r a, encState (step^[n + 1] (init a)) ≠ [])
    (hnil : ∀ a, encState (step^[r a + 1] (init a)) = []) :
    ∃ c d, ComputableInTimeAndSpace (fun a => fin (step^[r a] (init a))) encIn encOut
      (fun a => c * (r a + 1) * (l a + (encIn a).length + 1) ^ d)
      (fun a => c * (l a + (encIn a).length + 1) ^ d) := by
  obtain ⟨ci, di, ki, Si, _, tmi, hi⟩ := Internal.NormalForm.polyTime hinit
  obtain ⟨cs, ds, ks, Ss, _, tms, hs⟩ := Internal.NormalForm.polyTime hstep
  obtain ⟨cf, df, kf, Sf, _, tmf, hf⟩ := Internal.NormalForm.polyTime hfin
  -- the loop, along the trajectory from `init a`
  have hloop (a : α) := computesTidily_iterateWhile (tm := tms)
    (w := fun n => encState (step^[n] (init a))) (r := r a)
    (t := cs * (l a + 1) ^ ds) (s := cs * (l a + 1) ^ ds) (l := l a)
    (fun n hn => by
      have hb := Nat.mul_le_mul_left cs
        (Nat.pow_le_pow_left (Nat.add_le_add_right (hl a n hn) 1) ds)
      simpa only [Function.iterate_succ_apply'] using (hs (step^[n] (init a))).mono hb hb)
    (hl a) (hne a) (hnil a) true
  -- the start followed by the loop
  let main := (tms.iterateWhile true).comp tmi true
  let kMain := (fun {k : ℕ} {S : Type} (_ : MultiTapeTM k Bool S) => k) main
  let c₀ := 6 * max kMain kf + 29
  have hmain (a : α) := (hi a).comp (hloop a) true
  let hmainTime := fun a => (fun {k S} {tm : MultiTapeTM k Bool S} {i o : List Bool}
      {t s : ℕ} (_ : tm.ComputesTidilyInTimeAndSpace i o t s) => t) (hmain a)
  let hmainSpace := fun a => (fun {k S} {tm : MultiTapeTM k Bool S} {i o : List Bool}
      {t s : ℕ} (_ : tm.ComputesTidilyInTimeAndSpace i o t s) => s) (hmain a)
  have hraw (a : α) := (hmain a).comp (hf (step^[r a] (init a))) true
  have h : ComputableInTimeAndSpace (fun a => fin (step^[r a] (init a))) encIn encOut
      (fun a => (hmainTime a) + (cf * ((encState (step^[r a] (init a))).length + 1) ^ df) +
        c₀ * ((encState (step^[r a] (init a))).length + 1))
      (fun a => (hmainSpace a) + (cf * ((encState (step^[r a] (init a))).length + 1) ^ df) +
        c₀ * ((encState (step^[r a] (init a))).length + 1)) := by
    refine ⟨_, _, inferInstance, tmf.comp main true, ?_⟩
    exact ComputesFunInTimeAndSpace.mono
      (fun a => (hraw a).computesInTimeAndSpace)
      (fun a => by
        have ho : 4 * (encState (step^[r a] (init a))).length + 9 ≤
            c₀ * ((encState (step^[r a] (init a))).length + 1) := by
          calc _ ≤ 29 * ((encState (step^[r a] (init a))).length + 1) := by omega
               _ ≤ _ := Nat.mul_le_mul_right _ (by dsimp only [c₀]; omega)
        dsimp only [hmainTime] at ⊢
        omega)
      (fun a => by
        have ho : 5 * (encState (step^[r a] (init a))).length +
            (6 * max kMain kf + 20) ≤
            c₀ * ((encState (step^[r a] (init a))).length + 1) := by
          have hm := Nat.mul_le_mul_right (encState (step^[r a] (init a))).length
            (show 5 ≤ c₀ by dsimp only [c₀]; omega)
          dsimp only [c₀] at hm ⊢
          rw [Nat.mul_add, Nat.mul_one]
          omega
        dsimp only [hmainSpace, kMain, main] at ho ⊢
        omega)
  -- the bounds, with `P = (l a + |encIn a| + 1) ^ D` bounding every polynomial term
  obtain ⟨E, hE⟩ : ∃ E, E = 2 * (ks + 3) := ⟨_, rfl⟩
  set D := di + ds + df + 1
  have hpow (a : α) {e : ℕ} (he : e ≤ D) {x : ℕ} (hx : x + 1 ≤ l a + (encIn a).length + 1) :
      (x + 1) ^ e ≤ (l a + (encIn a).length + 1) ^ D :=
    (Nat.pow_le_pow_left hx e).trans (Nat.pow_le_pow_right (by omega) he)
  refine ⟨2 * ci + cs + E * cs + 2 * cf + 2 * c₀ + 6 * ki + E * (6 * ks + 54) + 10 * ks + 200,
    D, ?_⟩
  refine ComputableInTimeAndSpace.mono h (fun a => ?_) (fun a => ?_)
  all_goals
    dsimp only [hmainTime, hmainSpace] at ⊢
    have h₁ := Nat.mul_le_mul_left ci
      (hpow a (show di ≤ D by omega) (x := (encIn a).length) (by omega))
    have h₂ := Nat.mul_le_mul_left cs (hpow a (show ds ≤ D by omega) (x := l a) (by omega))
    have hlast := hl a (r a) le_rfl
    have h₃ := Nat.mul_le_mul_left cf
      (hpow a (show df ≤ D by omega) (x := (encState (step^[r a] (init a))).length) (by omega))
    have hlP := hpow a (show 1 ≤ D by omega) (x := l a) (by omega)
    have hfirst := hl a 0 (Nat.zero_le _)
    have hmax : max ki (ks + 1 + 2) ≤ ki + ks + 3 := by omega
    rw [pow_one] at hlP
    generalize (l a + (encIn a).length + 1) ^ D = P at h₁ h₂ h₃ hlP ⊢
  · -- time
    have hloopT : cs * (l a + 1) ^ ds + 10 * l a + 24 ≤ (cs + 34) * P := by linarith
    calc _ ≤ (r a + 1) * ((cs + 34) * P) + (ci + cf + 2 * c₀ + 50) * P := by
          have := Nat.mul_le_mul_left (r a + 1) hloopT
          simp only [Function.iterate_zero, id_eq] at hfirst ⊢
          nlinarith
      _ ≤ (r a + 1) * ((cs + 34) * P) + (r a + 1) * ((ci + cf + 2 * c₀ + 50) * P) :=
          Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)) _
      _ = (cs + 34 + (ci + cf + 2 * c₀ + 50)) * ((r a + 1) * P) := by ring
      _ ≤ _ := by rw [mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
  · -- space
    have hY : cs * (l a + 1) ^ ds + 10 * l a + 6 * ks + 44 ≤ (cs + 6 * ks + 54) * P := by
      have : 6 * ks + 44 ≤ (6 * ks + 44) * P := Nat.le_mul_of_pos_right _ (by omega)
      nlinarith
    have hEY := Nat.mul_le_mul_left E hY
    rw [← hE] at ⊢
    simp only [Function.iterate_zero, id_eq] at hfirst ⊢
    have : 6 * ki + 10 * ks + 94 ≤ (6 * ki + 10 * ks + 94) * P :=
      Nat.le_mul_of_pos_right _ (by omega)
    nlinarith

end Turing.MultiTapeTM
