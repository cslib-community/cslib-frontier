/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.GenericGroup.Basic
public import CslibFrontier.Languages.Probabilistic.Oracle.EvalPure
public import CslibFrontier.Languages.Probabilistic.QueryCount
public import Mathlib.Data.Nat.Log

/-!
# Exponentiation by products in the generic group model

Group multiplication (`product`) and repeated-squaring exponentiation (`power`) over
`GroupOracleSpec n S` ([BonehShoup2023], Section 16.1.2, pp. 684–686). `power ℓ k` returns
`pure ℓ` for `k ≤ 1` because no label of `0` is held, so `evalPure_power` assumes `1 ≤ k`.
Bounds count only `GroupQuery.IsProduct` calls (worst case over oracle replies); the constant
`2` is this library's, exponent arithmetic is not costed, and no machine-model bound is claimed.

## Main definitions

* `Cslib.Crypto.GenericGroup.product`, `Cslib.Crypto.GenericGroup.power`.

## Main results

* `Cslib.Crypto.GenericGroup.evalPure_product`, `Cslib.Crypto.GenericGroup.evalPure_power`,
  `Cslib.Crypto.GenericGroup.queriesSatisfy_product`,
  `Cslib.Crypto.GenericGroup.isQueryBounded_product`,
  `Cslib.Crypto.GenericGroup.queriesSatisfy_power`,
  `Cslib.Crypto.GenericGroup.isQueryBounded_power`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 16.1.2, pp. 684–686.
-/

public section

namespace Cslib.Crypto.GenericGroup

variable {n : ℕ} {S : Type}

/-- Multiply `a` and `b` via one `.op a b 1 1` call; a rejected call (`none`) returns `a`. -/
def product (a b : S) : OracleComp (GroupOracleSpec n S) S :=
  (fun r : Option S => r.getD a) <$>
    OracleComp.query (spec := GroupOracleSpec n S) (.op a b 1 1)

/-- Repeated-squaring exponentiation in `GroupOracleSpec n S`; returns `pure ℓ` for `k ≤ 1`. -/
def power (ℓ : S) (k : ℕ) : OracleComp (GroupOracleSpec n S) S :=
  if _h : k ≤ 1 then pure ℓ else do
    let half ← power ℓ (k / 2)
    let sq ← product half half
    if k % 2 = 0 then pure sq else product sq ℓ

/-- Every query made by `product` is a product (`GroupQuery.IsProduct`). -/
theorem queriesSatisfy_product (a b : S) :
    OracleComp.QueriesSatisfy GroupQuery.IsProduct (product (n := n) a b) :=
  (OracleComp.queriesSatisfy_map_iff _ _).mpr
    (OracleComp.QueriesSatisfy.query (by simp [GroupQuery.IsProduct]))

/-- `product` makes at most `1` oracle query on every path. -/
theorem isQueryBounded_product (a b : S) :
    OracleComp.IsQueryBounded (product (n := n) a b) 1 :=
  (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)

/-- Every query made by `power` is a product (`GroupQuery.IsProduct`). -/
theorem queriesSatisfy_power (ℓ : S) (k : ℕ) :
    OracleComp.QueriesSatisfy GroupQuery.IsProduct (power (n := n) ℓ k) := by
  fun_induction power (n := n) ℓ k with
  | case1 => exact .pure _ -- k ≤ 1
  | case2 k hk ih => -- 1 < k: square `power ℓ (k / 2)`
    refine .bind ih fun h => .bind (queriesSatisfy_product h h) fun sq => ?_
    split_ifs <;> [exact .pure _; exact queriesSatisfy_product sq ℓ]

/-- `power` makes at most `2 * Nat.log 2 k` product queries on every path, whatever the oracle
returns; the factor `2` is this library's and exponent arithmetic is not costed. -/
theorem isQueryBounded_power (ℓ : S) (k : ℕ) :
    OracleComp.IsQueryBounded (power (n := n) ℓ k) (2 * Nat.log 2 k) := by
  fun_induction power (n := n) ℓ k with
  | case1 => exact (OracleComp.IsCostBounded.pure _ 0).mono (Nat.zero_le _) -- k ≤ 1
  | case2 k hk ih => -- 1 < k: square `power ℓ (k / 2)`
    have hk1 : 1 < k := by omega
    have hlog : Nat.log 2 k = Nat.log 2 (k / 2) + 1 := Nat.log_of_one_lt_of_le (by omega) hk1
    refine .mono (n := 2 * Nat.log 2 (k / 2) + (1 + 1))
      (.bind ih fun half => .bind (isQueryBounded_product half half) fun sq => ?_)
      (by rw [hlog]; omega)
    split_ifs
    · exact (OracleComp.IsCostBounded.pure _ 0).mono (Nat.zero_le 1)
    · exact isQueryBounded_product sq ℓ

/-- Against any oracle that multiplies labels of `L`, `product` outputs `L (β₁ + β₂)`. -/
theorem evalPure_product {L : ZMod n → S} {O : (q : GroupQuery n S) → GroupOracleSpec n S q}
    (hO : ∀ β₁ β₂, O (.op (L β₁) (L β₂) 1 1) = some (L (β₁ + β₂))) (β₁ β₂ : ZMod n) :
    (product (n := n) (L β₁) (L β₂)).evalPure O = L (β₁ + β₂) := by
  simp [product, OracleComp.evalPure_map, OracleComp.evalPure_query, hO]

/-- Against any oracle that multiplies labels of `L`, `power (L β) k` outputs `L (k * β)` for
`1 ≤ k`. -/
theorem evalPure_power {L : ZMod n → S} {O : (q : GroupQuery n S) → GroupOracleSpec n S q}
    (hO : ∀ β₁ β₂, O (.op (L β₁) (L β₂) 1 1) = some (L (β₁ + β₂)))
    (β : ZMod n) {k : ℕ} (hk : 1 ≤ k) :
    (power (n := n) (L β) k).evalPure O = L ((k : ZMod n) * β) := by
  fun_induction power (n := n) (L β) k with
  | case1 k hk1 => -- k ≤ 1
    obtain rfl : k = 1 := by omega
    rw [OracleComp.evalPure_pure, Nat.cast_one, one_mul]
  | case2 k hk1 ih => -- 1 < k: square `power (L β) (k / 2)`
    rw [OracleComp.evalPure_bind, ih (by omega), OracleComp.evalPure_bind, evalPure_product hO]
    split_ifs with hmod
    · rw [OracleComp.evalPure_pure, ← add_mul, ← two_mul]
      norm_cast; rw [show 2 * (k / 2) = k by omega]
    · rw [evalPure_product hO]; congr 1
      nth_rw 3 [← one_mul β]
      rw [← add_mul, ← add_mul]
      norm_cast; rw [show k / 2 + k / 2 + 1 = k by omega]

end Cslib.Crypto.GenericGroup
