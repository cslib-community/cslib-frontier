/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.GenericGroup.RecursiveDlog

/-!
# Recursive discrete logarithm: an ordinary client

Exercises the public API of `Power`, `BabyStepGiantStep.subgroupDlog`, and `RecursiveDlog` through
ordinary imports (no `import all`), plus a counterexample showing why `Function.Injective L` is
needed in `evalPure_subgroupDlog`, and the values of the query-bound formula of
`isQueryBounded_recursiveDlog` at `q = 1` and `e = 0`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.GenericGroupRecursiveDlog

open Cslib Cslib.Crypto.GenericGroup

private theorem injective_smul_one_64 :
    Function.Injective fun β : ZMod 64 => β • (1 : ZMod 64) :=
  fun _ _ h => by simpa using h

/-! ### Public `recursiveDlog`, `subgroupDlog`, and `power` clients -/

example (α : ZMod 64) :
    (recursiveDlog (subgroupDlog 2) 2 6 (1 : ZMod 64) (α • (1 : ZMod 64))).evalPure
      (groupAnswer 64 1) = α.val :=
  evalPure_groupAnswer_recursiveDlog injective_smul_one_64 (by norm_num) (by norm_num) α

example (α : ZMod 64) :
    OracleComp.IsQueryBounded
      (recursiveDlog (subgroupDlog (q := 64) 2) 2 6 (1 : ZMod 64) (α • (1 : ZMod 64))) 120 := by
  have hb : ∀ g u : ZMod 64,
      OracleComp.IsQueryBounded (subgroupDlog (q := 64) 2 g u) 2 :=
    fun g u => by simpa using isQueryBounded_subgroupDlog (q := 64) 2 g u
  have h := isQueryBounded_recursiveDlog hb (q := 2) (by omega) 6 (by omega) 1 (α • (1 : ZMod 64))
  rwa [show 6 * 2 + 6 * 6 * Nat.clog 2 6 * Nat.clog 2 2 = 120 by decide] at h

example (g u : ZMod 64) :
    OracleComp.QueriesSatisfy GroupQuery.IsProduct
      (recursiveDlog (subgroupDlog (q := 64) 2) 2 6 g u) :=
  queriesSatisfy_recursiveDlog (subgroupDlog (q := 64) 2)
    (fun a b => queriesSatisfy_subgroupDlog 2 a b) 2 6 g u

example (α : ZMod (2 ^ 4)) :
    (recursiveDlog (subgroupDlog 2) 2 4 (1 : ZMod (2 ^ 4)) α).evalPure (answer id) = α.val ∧
      OracleComp.IsQueryBounded
        (recursiveDlog (subgroupDlog (q := 2 ^ 4) 2) 2 4 (1 : ZMod (2 ^ 4)) α) 56 := by
  have h₄ : Nat.clog 2 4 = 2 := by decide
  simpa [h₄] using
    recursiveDlog_two_pow (by omega : 1 ≤ 4) (Function.injective_id : Function.Injective id) α

example (a : ℕ) (ha : a < 3) :
    (subgroupDlog (q := 12) 3 (4 : ZMod 12) (a * 4)).evalPure (answer id) = a := by
  have hO : ∀ β₁ β₂ : ZMod 12, answer id (.op β₁ β₂ 1 1) = some (β₁ + β₂) := fun β₁ β₂ => by
    change answer id (.op (id β₁) (id β₂) 1 1) = some (id (β₁ + β₂))
    rw [answer_op_label Function.injective_id, one_mul, one_mul]
  have hdvd : addOrderOf (4 : ZMod 12) ∣ 3 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by decide : (3 : ℕ) • (4 : ZMod 12) = 0)
  have ht : addOrderOf (4 : ZMod 12) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · have h1 : (1 : ℕ) • (4 : ZMod 12) = 0 := h ▸ addOrderOf_nsmul_eq_zero (x := (4 : ZMod 12))
      exact absurd h1 (by decide)
    · exact h
  exact evalPure_subgroupDlog Function.injective_id hO ht ha

example (β : ZMod 11) :
    (power (n := 11) β 5).evalPure (answer id) = (5 : ZMod 11) * β ∧
      OracleComp.IsQueryBounded (power (n := 11) β 5) 4 ∧
      OracleComp.QueriesSatisfy GroupQuery.IsProduct (power (n := 11) β 5) := by
  have hO : ∀ β₁ β₂ : ZMod 11, answer id (.op β₁ β₂ 1 1) = some (β₁ + β₂) := fun β₁ β₂ => by
    change answer id (.op (id β₁) (id β₂) 1 1) = some (id (β₁ + β₂))
    rw [answer_op_label Function.injective_id, one_mul, one_mul]
  have hlog : Nat.log 2 5 = 2 := by decide
  refine ⟨evalPure_power hO β (by omega), ?_, queriesSatisfy_power β 5⟩
  simpa [hlog] using isQueryBounded_power (n := 11) β 5

/-! ### Hypotheses are needed -/

/-- `Function.Injective L` is needed in `evalPure_subgroupDlog`: the constant labeling of `ZMod 4`
satisfies `hO` but collapses `α = 0` and `α = 1`, so no program, `subgroupDlog 4` included,
recovers every `α < 4` from the labels of `1` and `α`. `evalPure_recursiveDlog` has no
injectivity premise; under this labeling no `base` satisfies its premise `hbase` at `q = 4`. -/
example :
    ∃ (L : ZMod 4 → ℕ) (O : (q : GroupQuery 4 ℕ) → GroupOracleSpec 4 ℕ q),
      (∀ β₁ β₂, O (.op (L β₁) (L β₂) 1 1) = some (L (β₁ + β₂))) ∧
      (∀ prog : ℕ → ℕ → OracleComp (GroupOracleSpec 4 ℕ) ℕ,
        ¬ ((∀ α : ℕ, α < 4 → (prog (L 1) (L (α * 1))).evalPure O = α))) := by
  let O : (q : GroupQuery 4 ℕ) → GroupOracleSpec 4 ℕ q := fun q =>
    match q with | .op _ _ _ _ => some 0 | .label _ => 0
  refine ⟨fun _ => 0, O, fun _ _ => rfl, fun prog h => ?_⟩
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  exact absurd (h0.symm.trans h1) (by decide)

/-- `2 ≤ q` is needed in `isQueryBounded_recursiveDlog`: at `q = 1`, the bound formula vanishes. -/
example (e T : ℕ) : e * T + 6 * e * Nat.clog 2 e * Nat.clog 2 1 = e * T := by
  have h : Nat.clog 2 1 = 0 := by decide
  simp [h]

/-- `1 ≤ e` is needed in `isQueryBounded_recursiveDlog`: at `e = 0`, the bound formula vanishes. -/
example (q T : ℕ) : 0 * T + 6 * 0 * Nat.clog 2 0 * Nat.clog 2 q = 0 := by simp

end CslibFrontierTests.Crypto.GenericGroupRecursiveDlog
