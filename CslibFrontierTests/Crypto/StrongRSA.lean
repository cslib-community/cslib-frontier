/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.StrongRSA
import Mathlib.FieldTheory.Finite.Basic

/-!
# The strong RSA assumption: checked instances

Checks for `CslibFrontier/Crypto/Computational/StrongRSA.lean`:

* For `N = 15` and `g = 2`, `(8, 3)` is a solution: `8 ^ 3 = 512 ≡ 2 [MOD 15]`. The exponent `1`
  never wins: `(2, 1)` is not a solution although `2 ^ 1 = 2`.
* The known-order root: `2 ^ 4 ≡ 1 [MOD 15]` and `3` is coprime to `4`, and
  `knownOrderRoot 15 4 3 2 = 8`, the solution above, as `powMod_knownOrderRoot` says.
* `0 < u` is needed in `powMod_knownOrderRoot`: `2 ^ 0 ≡ 1 [MOD 5]` and `1` is coprime to `0`, but
  `knownOrderRoot 5 0 1 2 = 1`, and `1 ^ 1` is not `2` modulo `5`.
* `not_strongRSA_rsaGUOSetup_const`: the book's `GGen` with a fixed RSA key does not satisfy the
  assumption. Every drawn base is a unit, so `not_strongRSA_of_knownOrder` applies with the
  constant exponents `u = φ(N)` and `v = φ(N) + 1`.
* The unit condition in `not_strongRSA_const` (`AssumptionNonvacuity.lean`) is needed:
  for `(N, g) = (4, 2)` no output is a solution (`isStrongRSASolution_four_two`), so the strong
  RSA assumption holds for that constant setup (`strongRSA_const_four_two`).
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.StrongRSA

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

/-! ### A solution and the known-order root -/

example : isStrongRSASolution ⟨15, 2⟩ (8, 3) = true := by decide

example : isStrongRSASolution ⟨15, 2⟩ (2, 1) = false := by decide

example : knownOrderRoot 15 4 3 2 = 8 := by
  unfold knownOrderRoot BinaryGcd.modInv
  decide

example : powMod 15 (knownOrderRoot 15 4 3 2) 3 = 2 :=
  powMod_knownOrderRoot (by norm_num) (by decide) (by decide)

/-! ### `0 < u` is needed -/

example : 2 ^ 0 ≡ 1 [MOD 5] ∧ Nat.Coprime 1 0 ∧ knownOrderRoot 5 0 1 2 = 1 ∧
    powMod 5 (knownOrderRoot 5 0 1 2) 1 ≠ 2 % 5 := by
  refine ⟨rfl, by decide, ?_, ?_⟩ <;>
  · unfold knownOrderRoot BinaryGcd.modInv
    decide

/-! ### The book's `GGen` with a fixed key -/

/-- **`rsaGUOSetup` with a fixed RSA key does not satisfy the strong RSA assumption**: every base it
draws is a unit modulo `N`, so `g ^ φ(N) ≡ 1 [MOD N]`, and the known-order adversary with `u = φ(N)`
and `v = φ(N) + 1` wins with probability `1`. -/
theorem not_strongRSA_rsaGUOSetup_const (desc : RSADesc) :
    ¬ StrongRSA (rsaGUOSetup fun _ => PMF.pure desc) := by
  have hpos : 0 < desc.modulus.totient := Nat.totient_pos.mpr (Nat.pos_of_neZero _)
  refine not_strongRSA_of_knownOrder (u := fun _ _ => desc.modulus.totient)
    (v := fun _ _ => desc.modulus.totient + 1)
    (ComputableInPolyTime.const _) (ComputableInPolyTime.const _) fun n p hp => ?_
  simp only [rsaGUOSetup, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind,
    PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_singleton_iff] at hp
  obtain ⟨g, -, rfl⟩ := hp
  exact ⟨Nat.ModEq.pow_totient (ZMod.val_coe_unit_coprime g), by simp, by omega⟩

/-! ### A base that is not a unit -/

/-- Modulo `4`, no `x ^ e` with `e ≠ 1` is `2`: for `e = 0` it is `1`, and for `e ≥ 2` an even
`x ^ e` is divisible by `4`. -/
theorem isStrongRSASolution_four_two (s : ℕ × ℕ) : isStrongRSASolution ⟨4, 2⟩ s = false := by
  obtain ⟨x, _ | _ | e⟩ := s
  · simp [isStrongRSASolution, powMod]
  · simp [isStrongRSASolution]
  · have h4 : ¬ x ^ (e + 2) % 4 = 2 := by
      intro h
      have hx : Even x :=
        (Nat.even_pow.mp (Nat.even_iff.mpr (show x ^ (e + 2) % 2 = 0 by omega))).1
      obtain ⟨k, rfl⟩ := hx
      have : 4 ∣ (k + k) ^ (e + 2) := Dvd.intro (k ^ 2 * (k + k) ^ e) (by ring)
      omega
    simp [isStrongRSASolution, powMod, h4]

/-- **The unit condition in `not_strongRSA_const` is needed**: the strong RSA assumption holds for
the constant setup `(N, g) = (4, 2)`, since no output wins (`isStrongRSASolution_four_two`). -/
theorem strongRSA_const_four_two : StrongRSA fun _ => PMF.pure ⟨4, 2⟩ := by
  intro A _
  have hfalse : isStrongRSASolution ⟨4, 2⟩ = fun _ => false := funext isStrongRSASolution_four_two
  have hgame (n : ℕ) : strongRSAGame (fun _ => PMF.pure ⟨4, 2⟩) A n = PMF.pure false := by
    simp only [strongRSAGame, Game.withSetup, PMF.pure_bind, ProbComp.eval_bind,
      ProbComp.eval_pure, hfalse]
    exact PMF.bind_const _ _
  simp [hgame, Game.succProbability]

end CslibFrontierTests.Crypto.StrongRSA
