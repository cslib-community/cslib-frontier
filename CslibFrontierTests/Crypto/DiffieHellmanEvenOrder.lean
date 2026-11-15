/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.DiffieHellman.EvenOrder

/-!
# DDH in groups of even order: checked instances

Concrete checks for `CslibFrontier/Crypto/Computational/DiffieHellman/EvenOrder.lean`, through
ordinary imports of its public API:

* In `ZMod 6` with `g = 1`, Lemmas 16.1 and 16.2 hold on sample exponents, the parity
  distinguisher accepts a Diffie–Hellman triple and rejects a non-Diffie–Hellman one, and its DDH
  advantage is exactly `1 / 2`.
* For odd `q` Lemma 16.1 fails: in `ZMod 5`, `a = 2` is even but `(5 / 2) • (2 • 1) ≠ 0`.
* In `(ZMod 7)ˣ` with generator `3`, and in `(ZMod p)ˣ` for every odd prime `p`, the distinguisher
  has DDH advantage `1 / 2`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.DiffieHellmanEvenOrder

open Cslib Cslib.Probability Cslib.Crypto

/-! ### The group `ZMod 6` with generator `1` -/

theorem zmod6_injective : Function.Injective fun c : ZMod 6 => c • (1 : ZMod 6) := by
  intro a b h
  simpa using h

theorem even_six : Even 6 := ⟨3, rfl⟩

-- Lemma 16.1 on the exponents `2` (even) and `3` (odd).
example : (6 / 2) • ((2 : ZMod 6) • (1 : ZMod 6)) = 0 :=
  (div_two_nsmul_smul_eq_zero_iff even_six zmod6_injective 2).mpr ⟨1, rfl⟩

example : (6 / 2) • ((3 : ZMod 6) • (1 : ZMod 6)) ≠ 0 := fun h =>
  absurd ((div_two_nsmul_smul_eq_zero_iff even_six zmod6_injective 3).mp h) (by decide)

-- Lemma 16.2: `3 * 5 = 3` in `ZMod 6` is odd, and neither `3` nor `5` is even.
example : ¬((6 / 2) • ((3 : ZMod 6) • (1 : ZMod 6)) = 0 ∨
    (6 / 2) • ((5 : ZMod 6) • (1 : ZMod 6)) = 0) := fun h =>
  absurd ((even_val_mul_iff even_six zmod6_injective 3 5).mpr h) (by decide)

-- The distinguisher accepts the Diffie–Hellman triple for `a = 3`, `b = 5` and rejects `w = 4`.
example : ddhParityDistinguisher 6 (3 : ZMod 6) 5 3 = pure true := congrArg pure (by decide)

example : ddhParityDistinguisher 6 (3 : ZMod 6) 5 4 = pure false := congrArg pure (by decide)

example : Pr[ddhRealExperiment 6 (1 : ZMod 6) (ddhParityDistinguisher 6)] = 1 :=
  probability_ddhRealExperiment_ddhParityDistinguisher 6 1 even_six zmod6_injective

example : Pr[ddhRandomExperiment 6 (1 : ZMod 6) (ddhParityDistinguisher 6)] = 1 / 2 :=
  probability_ddhRandomExperiment_ddhParityDistinguisher 6 1 even_six zmod6_injective

/-- In `ZMod 6` with `g = 1` the parity distinguisher has DDH advantage exactly `1 / 2`. -/
theorem ddhAdvantage_zmod6 : ddhAdvantage 6 (1 : ZMod 6) (ddhParityDistinguisher 6) = 1 / 2 :=
  ddhAdvantage_ddhParityDistinguisher 6 1 even_six zmod6_injective

/-! ### Lemma 16.1 needs an even order -/

/-- In `ZMod 5` (odd order) Lemma 16.1 fails at `a = 2`: the exponent is even, yet
`(5 / 2) • (2 • 1) = 4 ≠ 0`. The element `g = 1` still has order `5`. -/
theorem not_lemma16_1_zmod5 :
    ¬((5 / 2) • ((2 : ZMod 5) • (1 : ZMod 5)) = 0 ↔ Even (2 : ZMod 5).val) := by
  decide

example : Function.Injective fun c : ZMod 5 => c • (1 : ZMod 5) := by
  intro a b h
  simpa using h

/-! ### The group `(ZMod p)ˣ` -/

section Units

attribute [local instance] neZero_sub_one_of_prime zmodUnitsModule

instance : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

/-- The residue `3` as a unit modulo `7`. -/
def three : (ZMod 7)ˣ := ZMod.unitOfCoprime 3 (by norm_num)

/-- `3` generates `(ZMod 7)ˣ`: its order is `6`, the order of the group. -/
theorem three_generates : ∀ x, x ∈ Subgroup.zpowers three := by
  have horder : orderOf three = 6 := by
    rw [orderOf_eq_iff (by norm_num)]
    decide
  have htop : Subgroup.zpowers three = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, horder, Nat.card_eq_fintype_card, ZMod.card_units]
  intro x
  rw [htop]
  exact Subgroup.mem_top x

/-- In `(ZMod 7)ˣ` with generator `3`, written additively, the parity distinguisher has DDH
advantage exactly `1 / 2`. -/
example : ddhAdvantage (7 - 1) (Additive.ofMul three) (ddhParityDistinguisher (7 - 1)) = 1 / 2 :=
  ddhAdvantage_units_ddhParityDistinguisher 7 (by norm_num) three_generates

/-- For every odd prime `p`, some generator of `(ZMod p)ˣ` exists, and with it the parity
distinguisher has DDH advantage `1 / 2`: the hypotheses of
`ddhAdvantage_units_ddhParityDistinguisher` are satisfiable. -/
example (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ∃ g : (ZMod p)ˣ,
      ddhAdvantage (p - 1) (Additive.ofMul g) (ddhParityDistinguisher (p - 1)) = 1 / 2 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  exact ⟨g, ddhAdvantage_units_ddhParityDistinguisher p hp hg⟩

end Units

end CslibFrontierTests.Crypto.DiffieHellmanEvenOrder
