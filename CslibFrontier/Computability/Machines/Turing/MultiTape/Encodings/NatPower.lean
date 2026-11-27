/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts

/-!
# Powers of two in binary

The binary digits of `2 ^ n`, least significant first, are `n` zeros followed by a one
(`Turing.MultiTapeTM.encNat_two_pow`). So an exponential clock `2 ^ n` is written in linear time,
by a transducer replacing every symbol of a word of length `n` by `false` and appending `true`,
without ever writing `2 ^ n` in unary.

## Main results

* `Turing.MultiTapeTM.encNat_two_pow`: the binary digits of `2 ^ n`.
* `Turing.MultiTapeTM.ComputableInDegree.two_pow_length`: `2 ^ (encIn a).length` is linear.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- The binary digits of `2 ^ n`, least significant first: `n` zeros followed by a one. -/
theorem encNat_two_pow (n : ℕ) : encNat (2 ^ n) = List.replicate n false ++ [true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [encNat_apply, pow_succ, mul_comm, Nat.bit0_bits _ (by positivity), ← encNat_apply, ih,
      List.replicate_succ, List.cons_append]

/-- The binary encoding of `2 ^ n` uses exactly `n + 1` digits. -/
theorem length_encNat_two_pow (n : ℕ) : (encNat (2 ^ n)).length = n + 1 := by
  rw [encNat_two_pow, List.length_append, List.length_replicate, List.length_singleton]

/-- A number at most `2 ^ n` uses at most `n + 1` binary digits. -/
theorem length_encNat_le_of_le_two_pow {a n : ℕ} (h : a ≤ 2 ^ n) :
    (encNat a).length ≤ n + 1 := by
  rw [← length_encNat_two_pow n]
  exact length_encNat_mono h

/-- Replaces every symbol by `false` and appends `true`. -/
def twoPowT : Transducer Bool Unit where
  q₀ := ()
  step _ _ := ((), [false])
  final _ := [true]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

theorem twoPowT_run (w : List Bool) :
    twoPowT.run () w = List.replicate w.length false ++ [true] := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [Transducer.run_cons, ih]
    rfl

/-- **An exponential clock in binary.** `2 ^ (encIn a).length` is computable in linear time and
work space, with linear output length, for every encoding of the input. -/
theorem ComputableInDegree.two_pow_length {α : Type*} (encIn : α ↪ List Bool) :
    ComputableInDegree (fun a => 2 ^ (encIn a).length) encIn encNat 1 1 := by
  refine ⟨⟨fun a => 2 * (encIn a).length + 3, fun _ => 0,
    ⟨3, fun _ => by simp only [pow_one]; omega⟩, DegreeBounded.const 0,
    0, _, inferInstance, twoPowT.toTM, fun a => ?_⟩,
    ⟨1, fun a => by simpa only [pow_one, one_mul] using (length_encNat_two_pow _).le⟩⟩
  have heq : encNat (2 ^ (encIn a).length) = twoPowT.run twoPowT.q₀ (encIn a) := by
    rw [encNat_two_pow, show twoPowT.q₀ = () from rfl, twoPowT_run]
  simpa only [heq] using twoPowT.computesInTimeAndSpace_toTM (encIn a)

end Turing.MultiTapeTM
