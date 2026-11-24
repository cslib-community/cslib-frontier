/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.GenericRAM.Native.ExpTimePolySpace

/-!
# Binary-counted iteration in factored time and polynomial space

A native binary-counted iteration (`Cslib.GenericRAM.NativeCertificate.iterate`) runs in time
`(count a + 1) * K a` times a polynomial and in polynomial space whenever the round count and
initial state are produced in polynomial time, every reached state has polynomially bounded encoded
length, and every reached round runs in time `K a` times a polynomial and polynomial space.

## Main results

* `Cslib.GenericRAM.NativeCertificate.FactorTimePolySpace.iterate_of_bounds`,
  `Cslib.GenericRAM.NativeCertificate.FactorTimePolySpace.iterate`: binary-counted iteration with
  general runtime round count `count a`.
* `Cslib.GenericRAM.NativeCertificate.ExpTimePolySpace.iterate_of_bounds`: iteration under a
  polynomially bounded round count without increasing the common exponent.
-/

public section

namespace Cslib.GenericRAM.NativeCertificate

open Turing.MultiTapeTM

variable {α β : Type} {enc : α ↪ List Bool} {encState : β ↪ List Bool}
  {count : α → ℕ} {init : α → β} {step : β → β}

namespace FactorTimePolySpace

/-- **Binary-counted iteration under explicit reachable-round bounds.** Every reached round
`j ≤ count a` uses time at most `K a * R a` and workspace at most `Q a`, where `R`, `Q` and the
live-state bound `B` are polynomially bounded in the input length. -/
theorem iterate_of_bounds (cn : NativeCertificate count enc encNat)
    (ci : NativeCertificate init enc encState) (cs : NativeCertificate step encState encState)
    (hcn : cn.IsPolynomial) (hci : ci.IsPolynomial) {K R Q B : α → ℕ} (hK : ∀ a, 1 ≤ K a)
    (hR : PolyBounded (fun a => (enc a).length) R) (hQ : PolyBounded (fun a => (enc a).length) Q)
    (hB : PolyBounded (fun a => (enc a).length) B)
    (ht : ∀ a j, j ≤ count a → cs.time (step^[j] (init a)) ≤ K a * R a)
    (hs : ∀ a j, j ≤ count a → cs.space (step^[j] (init a)) ≤ Q a)
    (hb : ∀ a j, j ≤ count a → (encState (step^[j] (init a))).length ≤ B a) :
    (NativeCertificate.iterate cn ci cs).FactorTimePolySpace (fun a => (count a + 1) * K a) := by
  have hclock := (cn.polyTime hcn).polyBounded_length
  refine of_polyBounded ((((hcn.1.add hci.1).add hR).add hB).add ((hclock.add (.const 1)).pow 2))
    (((((hcn.2.add hci.2).add hQ).add hB).add hclock).mono fun a => ?_) fun a => ?_
  · have := maxRoundSpace_le cs (count a) (init a) (hs a)
    have := maxStateLength_le encState step (count a) (init a) (hb a)
    simp only [iterate_space]; omega
  · have hmaxT := maxRoundTime_le cs (count a) (init a) (ht a)
    have hmaxB := maxStateLength_le encState step (count a) (init a) (hb a)
    have hKa := hK a; have hpos : 1 ≤ (count a + 1) * K a := Nat.mul_pos (Nat.succ_pos _) hKa
    have hbody : maxRoundTime cs (count a) (init a) +
        maxStateLength encState step (count a) (init a) +
        ((encNat (count a)).length + 1) ^ 2 ≤
          K a * (R a + B a + ((encNat (count a)).length + 1) ^ 2) := by
      have := hmaxB.trans (Nat.le_mul_of_pos_left _ hKa)
      have := Nat.le_mul_of_pos_left (((encNat (count a)).length + 1) ^ 2) hKa
      have : K a * R a + K a * B a + K a * ((encNat (count a)).length + 1) ^ 2 =
        K a * (R a + B a + ((encNat (count a)).length + 1) ^ 2) := by ring
      omega
    rw [iterate_time]
    calc _ ≤ ((count a + 1) * K a) * (cn.time a + ci.time a) +
          (count a + 1) * (K a * (R a + B a + ((encNat (count a)).length + 1) ^ 2)) :=
          Nat.add_le_add (Nat.le_mul_of_pos_left _ hpos) (Nat.mul_le_mul_left _ hbody)
      _ = _ := by ring

/-- **Binary-counted iteration of a `FactorTimePolySpace` step certificate** under a polynomial
reachable-state length bound `B` and a per-input bound `K a` on the step factor. -/
theorem iterate (cn : NativeCertificate count enc encNat)
    (ci : NativeCertificate init enc encState) (cs : NativeCertificate step encState encState)
    {Ks : β → ℕ} {K B : α → ℕ} (hcn : cn.IsPolynomial) (hci : ci.IsPolynomial)
    (hcs : cs.FactorTimePolySpace Ks) (hK : ∀ a, 1 ≤ K a)
    (hB : PolyBounded (fun a => (enc a).length) B)
    (hKs : ∀ a j, j ≤ count a → Ks (step^[j] (init a)) ≤ K a)
    (hb : ∀ a j, j ≤ count a → (encState (step^[j] (init a))).length ≤ B a) :
    (NativeCertificate.iterate cn ci cs).FactorTimePolySpace (fun a => (count a + 1) * K a) := by
  obtain ⟨Cs, ds, hcs⟩ := hcs
  have hP := polyBounded_pow_of_polyBounded hB Cs ds
  refine iterate_of_bounds cn ci cs hcn hci hK hP hP hB (fun a j hj => ?_) (fun a j hj => ?_) hb
  · exact ((hcs _).1.trans (Nat.mul_le_mul (Nat.mul_le_mul_left Cs (hKs a j hj))
      (Nat.pow_le_pow_left (Nat.add_le_add_right (hb a j hj) 1) ds))).trans_eq (by ring)
  · exact (hcs _).2.trans
      (Nat.mul_le_mul_left Cs (Nat.pow_le_pow_left (Nat.add_le_add_right (hb a j hj) 1) ds))

end FactorTimePolySpace

namespace ExpTimePolySpace

variable {E R Q B : α → ℕ}

/-- **Polynomially many adaptive calls preserve the common exponential time factor.** The
round count and state bounds are measured against the original encoded input. Every reached
round, including the terminal state, must use time at most `R a * 2 ^ E a` and space at most
`Q a`, where `R`, `Q` and the live-state bound `B` are polynomially bounded. -/
theorem iterate_of_bounds (cn : NativeCertificate count enc encNat)
    (ci : NativeCertificate init enc encState) (cs : NativeCertificate step encState encState)
    (hcn : cn.IsPolynomial) (hci : ci.IsPolynomial)
    (hcount : PolyBounded (fun a => (enc a).length) count)
    (hR : PolyBounded (fun a => (enc a).length) R) (hQ : PolyBounded (fun a => (enc a).length) Q)
    (hB : PolyBounded (fun a => (enc a).length) B)
    (ht : ∀ a j, j ≤ count a → cs.time (step^[j] (init a)) ≤ R a * 2 ^ E a)
    (hs : ∀ a j, j ≤ count a → cs.space (step^[j] (init a)) ≤ Q a)
    (hb : ∀ a j, j ≤ count a → (encState (step^[j] (init a))).length ≤ B a) :
    (NativeCertificate.iterate cn ci cs).ExpTimePolySpace E :=
  (FactorTimePolySpace.iterate_of_bounds cn ci cs hcn hci (fun _ => Nat.two_pow_pos _) hR hQ hB
    (fun a j hj => (ht a j hj).trans_eq (Nat.mul_comm _ _)) hs hb).absorb_polyBounded
    (hcount.add (.const 1))

end ExpTimePolySpace

end Cslib.GenericRAM.NativeCertificate
