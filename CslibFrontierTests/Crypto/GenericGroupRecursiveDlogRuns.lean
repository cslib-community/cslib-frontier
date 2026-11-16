/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

-- `import all`: evaluates the unexposed bodies of `answer`, `groupAnswer`, `product`, `power`,
-- `subgroupDlog`, and `recursiveDlog` on concrete inputs.
import all CslibFrontier.Crypto.Computational.GenericGroup.Basic
import all CslibFrontier.Crypto.Computational.GenericGroup.BabyStepGiantStep
import all CslibFrontier.Crypto.Computational.GenericGroup.Power
import all CslibFrontier.Crypto.Computational.GenericGroup.RecursiveDlog

public meta import Mathlib.Data.ZMod.Defs
public meta import CslibFrontier.Crypto.Computational.GenericGroup.Basic
public meta import CslibFrontier.Crypto.Computational.GenericGroup.BabyStepGiantStep
public meta import CslibFrontier.Crypto.Computational.GenericGroup.Power
public meta import CslibFrontier.Crypto.Computational.GenericGroup.RecursiveDlog

/-!
# Recursive discrete logarithm: concrete runs and failing cases

Evaluates `power` and `recursiveDlog (subgroupDlog q)` against `groupAnswer`, tracks oracle query
counts via `runCount`, and gives concrete witnesses showing that each side condition of
`evalPure_power`, `evalPure_recursiveDlog`, and `isQueryBounded_recursiveDlog` is needed.
-/

-- This regression module uses `#guard` runs and exports no test fixtures.
set_option linter.privateModule false
set_option linter.hashCommand false

namespace CslibFrontierTests.Crypto.GenericGroupRecursiveDlogRuns

open Cslib Cslib.Crypto.GenericGroup

private meta def runCount {q : Type} {spec : OracleSpec q} {α : Type}
    (h : (x : q) → spec x) (prog : OracleComp spec α) : α × ℕ :=
  (OracleComp.interpret (m := StateM ℕ) (fun x => do modify (· + 1); pure (h x)) prog).run 0

/-! ### `power` runs and `k = 0` -/

#guard
  let res := runCount (groupAnswer 257 1) (power (n := 257) (3 : ZMod 257) 255)
  res.1 == (255 : ZMod 257) * 3 && res.2 == 14 && res.2 ≤ 2 * Nat.log 2 255

#guard
  let res := runCount (groupAnswer 257 1) (power (n := 257) (3 : ZMod 257) 256)
  res.1 == (256 : ZMod 257) * 3 && res.2 == 8 && res.2 ≤ 2 * Nat.log 2 256

-- `1 ≤ k` is needed in `evalPure_power`: `power ℓ 0` returns `ℓ`, not `0`.
#guard
  (runCount (groupAnswer 5 1) (power (n := 5) (3 : ZMod 5) 0)).1 == 3

/-! ### `recursiveDlog` runs (`ZMod 64`, `ZMod 81`, subgroup in `ZMod 48`, `ZMod 216`) -/

#guard
  let runs := (List.range 64).map fun α =>
    (α, runCount (groupAnswer 64 1)
      (recursiveDlog (subgroupDlog (q := 64) 2) 2 6 (1 : ZMod 64) (α : ZMod 64)))
  runs.all (fun p => p.2.1 == p.1 && p.2.2 ≤ 120) &&
    (runs.foldl (fun m p => max m p.2.2) 0) ≤ 120

#guard
  (List.range 81).all fun α =>
    let res := runCount (groupAnswer 81 1)
      (recursiveDlog (subgroupDlog (q := 81) 3) 3 4 (1 : ZMod 81) (α : ZMod 81))
    res.1 == α && res.2 ≤ 104

#guard
  (List.range 16).all fun α =>
    let res := runCount (groupAnswer 48 1)
      (recursiveDlog (subgroupDlog (q := 48) 2) 2 4 (3 : ZMod 48) ((α : ZMod 48) * 3))
    res.1 == α && res.2 ≤ 56

#guard
  (List.range 216).all fun α =>
    let res := runCount (groupAnswer 216 1)
      (recursiveDlog (subgroupDlog (q := 216) 6) 6 3 (1 : ZMod 216) (α : ZMod 216))
    res.1 == α && res.2 ≤ 120

/-! ### Hypotheses are needed -/

-- `addOrderOf s = q ^ e` is needed: base `2` has order `4` in `ZMod 8`, and running as
-- `2 ^ 3` at `α = 5` outputs `3`, with `3 • 2 ≠ 5 • 2`.
#guard
  let out := (runCount (groupAnswer 8 1)
    (recursiveDlog (subgroupDlog (q := 8) 2) 2 3 (2 : ZMod 8) (5 • 2))).1
  out == 3 && ((out : ℕ) • (2 : ZMod 8) != 5 • (2 : ZMod 8))

/-- A base-case solver for order `3` in `ZMod 9` that answers `1` at the label of `0`. -/
private def zeroBase (g u : ZMod 9) : OracleComp (GroupOracleSpec 9 (ZMod 9)) ℕ :=
  if g = 0 then pure 1 else subgroupDlog 3 g u

/-- `1 ≤ e` is needed in `evalPure_recursiveDlog`: with `L = id` and `O = answer id`, every other
premise holds at `q = 3`, `e = 0`, `s = 0` (of order `3 ^ 0`) and `α = 0 < 3 ^ 0`, including
correctness of `zeroBase` on every element of order `3`, yet the output is `1 ≠ 0`. -/
example :
    (∀ β₁ β₂ : ZMod 9, answer id (.op (id β₁) (id β₂) 1 1) = some (id (β₁ + β₂))) ∧
    (∀ t : ZMod 9, addOrderOf t = 3 → ∀ a : ℕ, a < 3 →
      (zeroBase (id t) (id (a * t))).evalPure (answer id) = a) ∧
    addOrderOf (0 : ZMod 9) = 3 ^ 0 ∧ 0 < 3 ^ 0 ∧
    (recursiveDlog zeroBase 3 0 (id 0) (id ((0 : ℕ) * 0))).evalPure (answer id) = 1 := by
  have hO : ∀ β₁ β₂ : ZMod 9, answer id (.op (id β₁) (id β₂) 1 1) = some (id (β₁ + β₂)) :=
    fun β₁ β₂ => by rw [answer_op_label Function.injective_id, one_mul, one_mul]
  refine ⟨hO, fun t ht a ha => ?_, by simp, by norm_num, ?_⟩
  · have ht0 : t ≠ 0 := by rintro rfl; simp at ht
    dsimp only [zeroBase, id]
    rw [ite_eq_right ht0]
    exact evalPure_subgroupDlog Function.injective_id hO ht ha
  · rw [recursiveDlog_of_le_one _ _ (by omega)]
    simp [zeroBase, OracleComp.evalPure_pure]

-- `1 ≤ e` is needed in `isQueryBounded_recursiveDlog`: at `e = 0`, `subgroupDlog 3` makes
-- `2` oracle queries, contradicting the `0` value of the bound formula.
#guard
  (runCount (groupAnswer 9 1)
    (recursiveDlog (subgroupDlog (q := 9) 3) 3 0 (1 : ZMod 9) (1 : ZMod 9))).2 == 2

-- `2 ≤ q` is needed in `isQueryBounded_recursiveDlog`: at `q = 1`, `e = 2`, the program makes
-- `1` product query while `e * 0 + 6 * e * Nat.clog 2 e * Nat.clog 2 1 = 0`.
#guard
  (runCount (groupAnswer 2 1)
    (recursiveDlog (subgroupDlog (q := 2) 1) 1 2 (1 : ZMod 2) (1 : ZMod 2))).2 == 1

end CslibFrontierTests.Crypto.GenericGroupRecursiveDlogRuns
