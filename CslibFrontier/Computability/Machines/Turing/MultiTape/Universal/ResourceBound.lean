/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Machine
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial resource bounds for the universal simulator

The resource functions of Christian Reitwiessner's universal simulator admit explicit polynomial
bounds in the encoded description length, encoded input length, clock length, and number of
simulated steps. These estimates are shared by unary-clock polynomial-time simulation and the
time-hierarchy construction.

The generic implementation expressions are also shared by specialization and encoded-interpreter
resource accounting; both clients use the same time and workspace formulas.

## Main results

* `Turing.MultiTapeTM.Universal.runBound_mono`: the space bound grows with the number of steps.
* `Turing.MultiTapeTM.Universal.universal_bounds_le`: for `D, N, L ≤ B` and `1 ≤ J`, the time
  expression is at most `100000 * (B + 1) ^ 4 * J ^ 2` and the space bound is at most
  `200 * (B + 1) ^ 2 * J`.
* `Turing.MultiTapeTM.Universal.computableInO_universal_polynomialBound`: the plain simulator
  certificate with polynomial input-size and clock bounds.
-/

public section

namespace Turing.MultiTapeTM.Universal

/-- The resource expression used by the native universal-machine implementation before its
constant-factor machine compilation. -/
@[expose] def universalImplementationTime (i : Desc × List ℕ × ℕ) : ℕ :=
  let (description, input, clock) := i
  (clock + 1) *
      (stepBound (descLen description) (encList encUnary input).length clock +
        runBound (descLen description) (encList encUnary input).length clock +
          ((encNat clock).length + 1) ^ 2) +
    ((eIn i).length + 1) ^ 2

/-- The workspace expression used by the native universal-machine implementation before its
constant-factor machine compilation. -/
@[expose] def universalImplementationSpace (i : Desc × List ℕ × ℕ) : ℕ :=
  let (description, input, clock) := i
  runBound (descLen description) (encList encUnary input).length clock + (eIn i).length

/-- The universal simulator's space bound grows with the number of simulated steps. -/
theorem runBound_mono {D N t t' : ℕ} (h : t ≤ t') : runBound D N t ≤ runBound D N t' := by
  unfold runBound ctxBound cfgBound tapeBound
  gcongr

/-- **The resources of the universal run.** If the encoded description, the encoded input and the
number of digits `L` of the clock have length at most `B`, the time of the universal function on
`J ≥ 1` steps is `O((B + 1) ^ 4 * J ^ 2)` and its space `O((B + 1) ^ 2 * J)`.
Here `B` includes the encoded input length, so this is not a fixed-machine quadratic-time
simulation bound when the input length varies. The buffered logarithmic-overhead simulation
requires a different tape representation. -/
theorem universal_bounds_le {D N J B L : ℕ} (hD : D ≤ B) (hN : N ≤ B) (hL : L ≤ B) (hJ : 1 ≤ J) :
    (J + 1) * (stepBound D N J + runBound D N J + (L + 1) ^ 2) ≤ 100000 * (B + 1) ^ 4 * J ^ 2 ∧
      runBound D N J ≤ 200 * (B + 1) ^ 2 * J := by
  set M := B + 1
  have hM1 : 1 ≤ M := by omega
  have hDM : D + 1 ≤ M := by omega
  have hNM : N + 1 ≤ M := by omega
  have hJM := Nat.le_mul_of_pos_left J hM1; have hMJ := Nat.le_mul_of_pos_right M hJ
  have hM2 := Nat.le_self_pow two_ne_zero M; have hM2J := Nat.le_mul_of_pos_right (M ^ 2) hJ
  have hMJM2J := Nat.mul_le_mul_right J hM2
  have htape : tapeBound D J ≤ 36 * (M * J) := by
    have := (Nat.mul_le_mul_left (3 * (2 * J)) (show 2 * D + 3 ≤ 5 * M by omega)).trans
      (le_of_eq (show 3 * (2 * J) * (5 * M) = 30 * (M * J) by ring))
    unfold tapeBound; omega
  have hcfg : cfgBound D N J ≤ 80 * (M ^ 2 * J) := by
    have := (Nat.mul_le_mul (by omega : D ≤ M)
      (show 2 * tapeBound D J + 1 ≤ 74 * (M * J) by omega)).trans
      (le_of_eq (show M * (74 * (M * J)) = 74 * (M ^ 2 * J) by ring))
    unfold cfgBound; omega
  have hctx : ctxBound D N J ≤ 89 * (M ^ 2 * J) := by unfold ctxBound; omega
  have hrun : runBound D N J ≤ 200 * M ^ 2 * J := by
    have := (Nat.mul_le_mul_left J (show 2 * D + 1 ≤ 2 * M by omega)).trans
      (le_of_eq (show J * (2 * M) = 2 * (M * J) by ring))
    have : 200 * (M ^ 2 * J) = 200 * M ^ 2 * J := by ring
    unfold runBound; omega
  refine ⟨?_, hrun⟩
  have hM34 := (Nat.pow_le_pow_right hM1 (by omega : 3 ≤ 4)).trans (Nat.le_mul_of_pos_right _ hJ)
  have hM4 := Nat.mul_le_mul_right J (Nat.pow_le_pow_right hM1 (by omega : 2 ≤ 4))
  have hstep : stepBound D N J ≤ 190 * (M ^ 4 * J) := by
    unfold stepBound
    have hfirst : (2 * D + 1) * (D + 1) * (ctxBound D N J + 1) ≤ 180 * (M ^ 4 * J) :=
      (Nat.mul_le_mul (Nat.mul_le_mul (show 2 * D + 1 ≤ 2 * M by omega) hDM)
        (show ctxBound D N J + 1 ≤ 90 * (M ^ 2 * J) by omega)).trans (le_of_eq (by ring))
    have hbits := length_encNat_le (N + 1)
    have hdigits : ((encNat (N + 1)).length + 1) ^ 2 ≤ 4 * M ^ 2 :=
      (Nat.pow_le_pow_left (show (encNat (N + 1)).length + 1 ≤ 2 * M by omega) 2).trans
        (le_of_eq (by ring))
    have hlookup : (N + 1) * ((encNat (N + 1)).length + 1) ^ 2 ≤ 4 * M ^ 3 :=
      (Nat.mul_le_mul hNM hdigits).trans (le_of_eq (by ring))
    omega
  have hL2 : (L + 1) ^ 2 ≤ M ^ 4 * J := (Nat.pow_le_pow_left (by omega) 2).trans (hM2J.trans hM4)
  have hsum : stepBound D N J + runBound D N J + (L + 1) ^ 2 ≤ 391 * (M ^ 4 * J) := by
    have : 200 * M ^ 2 * J = 200 * (M ^ 2 * J) := by ring
    omega
  calc (J + 1) * (stepBound D N J + runBound D N J + (L + 1) ^ 2)
      ≤ (2 * J) * (391 * (M ^ 4 * J)) := Nat.mul_le_mul (by omega) hsum
    _ = 782 * (M ^ 4 * J ^ 2) := by ring
    _ ≤ 100000 * (M ^ 4 * J ^ 2) := by omega
    _ = 100000 * M ^ 4 * J ^ 2 := by ring

attribute [local irreducible] ComputableInO eDesc in
/-- The universal function with separate polynomial dependence on encoded input size and clock:
time `O((I + 1) ^ 4 * (t + 1) ^ 2)` and space `O((I + 1) ^ 2 * (t + 1))`.
This absorbs the detailed machine resource expressions before composing simulator certificates. -/
theorem computableInO_universal_polynomialBound : ComputableInO universal eIn eOut
    (fun i => ((eIn i).length + 1) ^ 4 * (i.2.2 + 1) ^ 2)
    (fun i => ((eIn i).length + 1) ^ 2 * (i.2.2 + 1)) := by
  have hresources (i : Desc × List ℕ × ℕ) := by
    let I := (eIn i).length
    have hI : I = 2 * descLen i.1 + 1 +
        (2 * (encList encUnary i.2.1).length + 1 + (encNat i.2.2).length) := by
      simp only [I, length_encPair, descLen]
    obtain ⟨ht, hs⟩ := universal_bounds_le
      (D := descLen i.1) (N := (encList encUnary i.2.1).length)
      (L := (encNat i.2.2).length) (J := i.2.2 + 1) (B := I)
      (by omega) (by omega) (by omega) (by omega)
    have hstep := stepBound_mono (le_refl (descLen i.1))
      (le_refl (encList encUnary i.2.1).length) (Nat.le_succ i.2.2)
    have hrun := runBound_mono (D := descLen i.1)
      (N := (encList encUnary i.2.1).length) (Nat.le_succ i.2.2)
    have htime :
        (i.2.2 + 1) * (stepBound (descLen i.1) (encList encUnary i.2.1).length i.2.2 +
          runBound (descLen i.1) (encList encUnary i.2.1).length i.2.2 +
          ((encNat i.2.2).length + 1) ^ 2) ≤
        100000 * (I + 1) ^ 4 * (i.2.2 + 1) ^ 2 := by
      apply le_trans ?_ ht
      gcongr; exact Nat.le_succ _
    have hpad : (I + 1) ^ 2 ≤ (I + 1) ^ 4 * (i.2.2 + 1) ^ 2 := by
      have hp := Nat.pow_le_pow_right (by omega : 1 ≤ I + 1) (by omega : 2 ≤ 4)
      exact hp.trans (Nat.le_mul_of_pos_right _ (by positivity))
    have hspace : I ≤ (I + 1) ^ 2 * (i.2.2 + 1) := by
      have hp := Nat.le_self_pow (by norm_num : 2 ≠ 0) (I + 1)
      exact (Nat.le_succ I).trans (hp.trans (Nat.le_mul_of_pos_right _ (by omega)))
    refine And.intro (show
      (i.2.2 + 1) * (stepBound (descLen i.1) (encList encUnary i.2.1).length i.2.2 +
        runBound (descLen i.1) (encList encUnary i.2.1).length i.2.2 +
        ((encNat i.2.2).length + 1) ^ 2) + (I + 1) ^ 2 ≤
      100001 * ((I + 1) ^ 4 * (i.2.2 + 1) ^ 2 + 1) from ?_)
      (show runBound (descLen i.1) (encList encUnary i.2.1).length i.2.2 + I ≤
        100001 * ((I + 1) ^ 2 * (i.2.2 + 1) + 1) from ?_)
    · nlinarith
    · nlinarith [hrun.trans hs]
  exact computableInO_universal.mono 100001 (fun i => (hresources i).1)
    (fun i => (hresources i).2)

end Turing.MultiTapeTM.Universal
