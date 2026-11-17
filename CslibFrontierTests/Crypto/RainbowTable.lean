/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.RainbowTable
import CslibFrontier.Crypto.Computational.RainbowTable.RunCost

/-!
# Rainbow tables and Hellman time-space tradeoff: client tests

Concrete finite instances and hypothesis-necessity checks for
`CslibFrontier.Crypto.Computational.RainbowTable` and
`CslibFrontier.Crypto.Computational.RainbowTable.RunCost` under module encapsulation (ordinary
`import`, no `import all`).
-/

-- Regression module checking ordinary imports; exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.RainbowTable

open Cslib Cslib.Crypto

/-! ### Three-column rainbow table (`τ = 3`) with distinct column reductions -/

/-- Hash `h(x) = x + 1` on `ℕ` (injective, with `0` outside its range). -/
private def shiftHash (x : ℕ) : ℕ :=
  x + 1

private theorem shiftHash_injective : Function.Injective shiftHash :=
  fun _ _ h => Nat.succ.inj h

/-- Column-dependent reduction `g j y = (y + j) % 7` for 0-indexed column `j`. -/
private def modSevenRed (j y : ℕ) : ℕ :=
  (y + j) % 7

/-- Preprocessed rainbow table of length `τ = 3` from starting points `[0, 2]`:
* chain from `0`: `0 → 1 → 3 → 6` (endpoint `6`),
* chain from `2`: `2 → 3 → 5 → 1` (endpoint `1`).
Although both chains pass through `3`, they hit `3` in different columns (`col = 2` vs `col = 1`)
and therefore do not merge ([BonehShoup2023], Section 18.7, p. 745). -/
private def demoRainbowTable : List (ℕ × ℕ) :=
  (rainbowPreprocess modSevenRed 3 [0, 2]).evalPure shiftHash

private theorem nodup_demoRainbowEndpoints :
    ([0, 2].map (rainbowChainPure shiftHash modSevenRed 0 3)).Nodup := by
  simp only [List.map_cons, List.map_nil, rainbowChainPure_succ, rainbowChainPure_zero,
    shiftHash, modSevenRed]
  decide

example : demoRainbowTable = [(6, 0), (1, 2)] := by
  unfold demoRainbowTable
  rw [evalPure_rainbowPreprocess]
  simp only [List.map_cons, List.map_nil, rainbowChainPure_succ, rainbowChainPure_zero,
    shiftHash, modSevenRed]

/-- Endpoint lookup in `A₀`'s table recovers each starting point directly via
`lookup_evalPure_rainbowPreprocess_of_nodup`. -/
example :
    demoRainbowTable.lookup (rainbowChainPure shiftHash modSevenRed 0 3 2) = some 2 :=
  lookup_evalPure_rainbowPreprocess_of_nodup (by decide) nodup_demoRainbowEndpoints

/-- Preprocessing `2` chains of length `3` is query-bounded by `2 * 3 = 6`. -/
example : OracleComp.IsQueryBounded (rainbowPreprocess modSevenRed 3 [0, 2]) 6 :=
  isQueryBounded_rainbowPreprocess modSevenRed 3 [0, 2]

/-- Two-phase inversion of a covered intermediate password (`pw = 5` at `col = 2` of the chain from
`2`, with `y = shiftHash 5 = 6`) via `evalPure_rainbowAttack_rainbowPreprocess_of_injective`
without unfolding `rainbowPreprocess`. -/
example :
    (rainbowAttack modSevenRed 3 (shiftHash 5)).evalPure
      (OracleComp.sumPure shiftHash (List.lookup · demoRainbowTable)) = some 5 := by
  refine evalPure_rainbowAttack_rainbowPreprocess_of_injective shiftHash_injective
    (starts := [0, 2]) (pw₀ := 2) (col := 2) (by decide) nodup_demoRainbowEndpoints (by decide)
    ?_ rfl
  simp only [rainbowChainPure_succ, rainbowChainPure_zero, shiftHash, modSevenRed]

/-- Two-phase non-injective-form completeness (`exists_evalPure_rainbowAttack_rainbowPreprocess`)
and exact recovery on `pw = 1` at `col = 1` of the chain from `0` (`y = shiftHash 1 = 2`), together
with soundness `shiftHash pw = 2`. -/
example :
    (∃ pw', (rainbowAttack modSevenRed 3 2).evalPure
      (OracleComp.sumPure shiftHash (List.lookup · demoRainbowTable)) = some pw' ∧
      shiftHash pw' = 2) ∧
    (rainbowAttack modSevenRed 3 2).evalPure
      (OracleComp.sumPure shiftHash (List.lookup · demoRainbowTable)) = some 1 ∧
    shiftHash 1 = 2 := by
  have hcol1 : rainbowChainPure shiftHash modSevenRed 0 1 0 = 1 := by
    simp only [rainbowChainPure_succ, rainbowChainPure_zero, shiftHash, modSevenRed]
  have hex : ∃ pw', (rainbowAttack modSevenRed 3 2).evalPure
      (OracleComp.sumPure shiftHash (List.lookup · demoRainbowTable)) = some pw' ∧
      shiftHash pw' = 2 :=
    exists_evalPure_rainbowAttack_rainbowPreprocess (starts := [0, 2]) (pw₀ := 0) (col := 1)
      (by decide) nodup_demoRainbowEndpoints (by decide) (by rw [hcol1]; rfl)
  have heval :
      (rainbowAttack modSevenRed 3 2).evalPure
        (OracleComp.sumPure shiftHash (List.lookup · demoRainbowTable)) = some 1 :=
    evalPure_rainbowAttack_rainbowPreprocess_of_injective shiftHash_injective
      (starts := [0, 2]) (pw₀ := 0) (col := 1) (by decide) nodup_demoRainbowEndpoints (by decide)
      hcol1 rfl
  exact ⟨hex, heval, rainbowAttack_sound heval⟩

/-- On `y = 6` (`shiftHash 5`), the candidate endpoints across `k = 0, 1, 2` are `1` (`some 2`,
preimage `5` with `shiftHash 5 = 6`), `3` (`none`), and `0` (`none`), so no hit is a false alarm
and total hash cost is at most `3 * (3 + 1) / 2 = 6` (with lookup cost at most `3`). -/
example :
    ((OracleComp.queriesWith (OracleComp.sumPure shiftHash (List.lookup · demoRainbowTable))
      (rainbowAttack modSevenRed 3 6)).map TableAttackSpec.hashCost).sum ≤ 6 ∧
    ((OracleComp.queriesWith (OracleComp.sumPure shiftHash (List.lookup · demoRainbowTable))
      (rainbowAttack modSevenRed 3 6)).map TableAttackSpec.lookupCost).sum ≤ 3 := by
  refine ⟨?_, sum_map_lookupCost_queriesWith_rainbowAttack_le _ _ _ 3 6⟩
  refine sum_map_hashCost_queriesWith_rainbowAttack_le_of_no_false_alarm ?_
  intro k hk pw₀ hlk
  have htab : demoRainbowTable = [(6, 0), (1, 2)] := by
    unfold demoRainbowTable
    rw [evalPure_rainbowPreprocess]
    simp only [List.map_cons, List.map_nil, rainbowChainPure_succ, rainbowChainPure_zero,
      shiftHash, modSevenRed]
  have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk_cases with rfl | rfl | rfl
  · rw [htab] at hlk
    simp only [Nat.reduceSub, rainbowChainPure_succ, rainbowChainPure_zero, shiftHash,
      modSevenRed] at hlk ⊢
    decide +revert
  · rw [htab] at hlk
    simp only [rainbowChainPure_succ, rainbowChainPure_zero, shiftHash, modSevenRed] at hlk
    decide +revert
  · rw [htab] at hlk
    simp only [rainbowChainPure_succ, rainbowChainPure_zero, shiftHash, modSevenRed] at hlk
    decide +revert

/-- Complete miss on `y = 0` (`0` has no preimage under `shiftHash`; candidate endpoints `2, 4, 5`
all miss `demoRainbowTable`): `rainbowAttack` returns `none`, makes `3 * (3 - 1) / 2 = 3` hash
queries, and makes `3` table lookups. -/
example :
    (rainbowAttack modSevenRed 3 0).evalPure
      (OracleComp.sumPure shiftHash (List.lookup · demoRainbowTable)) = none ∧
    ((OracleComp.queriesWith (OracleComp.sumPure shiftHash (List.lookup · demoRainbowTable))
      (rainbowAttack modSevenRed 3 0)).map TableAttackSpec.hashCost).sum = 3 ∧
    ((OracleComp.queriesWith (OracleComp.sumPure shiftHash (List.lookup · demoRainbowTable))
      (rainbowAttack modSevenRed 3 0)).map TableAttackSpec.lookupCost).sum = 3 := by
  have hmiss : ∀ k < 3,
      demoRainbowTable.lookup
        (rainbowChainPure shiftHash modSevenRed (3 - k) k (modSevenRed (3 - 1 - k) 0)) = none := by
    intro k hk
    unfold demoRainbowTable
    rw [lookup_evalPure_rainbowPreprocess]
    have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk_cases with rfl | rfl | rfl <;>
      · simp only [List.find?_cons, List.find?_nil, rainbowChainPure_succ, rainbowChainPure_zero,
          shiftHash, modSevenRed]
        decide
  have heval :
      (rainbowAttack modSevenRed 3 0).evalPure
        (OracleComp.sumPure shiftHash (List.lookup · demoRainbowTable)) = none := by
    rw [evalPure_rainbowAttack, List.findSome?_eq_none_iff]
    intro k hk
    rw [hmiss k (List.mem_range.mp hk)]
  exact ⟨heval,
    sum_map_hashCost_queriesWith_rainbowAttack_of_forall_lookup_eq_none hmiss,
    sum_map_lookupCost_queriesWith_rainbowAttack_of_evalPure_eq_none heval⟩

/-- At `τ = 4` against an empty table, a miss run makes `4 * (4 - 1) / 2 = 6` hash evaluations
(strictly exceeding `τ = 4`) and `4` lookups. -/
example :
    ((OracleComp.queriesWith (OracleComp.sumPure shiftHash (fun _ => none))
      (rainbowAttack modSevenRed 4 0)).map TableAttackSpec.hashCost).sum = 6 ∧
    ((OracleComp.queriesWith (OracleComp.sumPure shiftHash (fun _ => none))
      (rainbowAttack modSevenRed 4 0)).map TableAttackSpec.lookupCost).sum = 4 := by
  have heval :
      (rainbowAttack modSevenRed 4 0).evalPure
        (OracleComp.sumPure shiftHash (fun _ => none)) = none := by
    rw [evalPure_rainbowAttack]
    decide
  exact ⟨sum_map_hashCost_queriesWith_rainbowAttack_of_forall_lookup_eq_none fun _ _ => rfl,
    sum_map_lookupCost_queriesWith_rainbowAttack_of_evalPure_eq_none heval⟩

/-! ### Hellman chains, colliding chains, and false alarms
(Fig. 18.13a, p. 744, and Fig. 18.14, p. 745) -/

/-- Single reduction `g₀` with a chain merge `0 → 1 → 2 ↔ 3` (and `4 → 4` disjoint). -/
private def mergeRed : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 2
  | _ => 4

/-- Single-chain Hellman table (`τ = 2`, starting point `[0]`, endpoint `2`): no false alarms on
`y = 1` or on `y = 4`. -/
private def cleanHellmanTable : List (ℕ × ℕ) :=
  (rainbowPreprocess (fun _ => mergeRed) 2 [0]).evalPure id

/-- Without false alarms, two-phase `hellmanAttack` on covered `y = 1` recovers `some 1` using
`τ = 2` hash evaluations and at most `2` lookups; on uncovered `y = 4` it also uses `τ = 2` hash
evaluations. -/
example :
    (hellmanAttack mergeRed 2 1).evalPure
      (OracleComp.sumPure id (List.lookup · cleanHellmanTable)) = some 1 ∧
    ((OracleComp.queriesWith (OracleComp.sumPure id (List.lookup · cleanHellmanTable))
      (hellmanAttack mergeRed 2 1)).map TableAttackSpec.hashCost).sum = 2 ∧
    ((OracleComp.queriesWith (OracleComp.sumPure id (List.lookup · cleanHellmanTable))
      (hellmanAttack mergeRed 2 4)).map TableAttackSpec.hashCost).sum = 2 ∧
    ((OracleComp.queriesWith (OracleComp.sumPure id (List.lookup · cleanHellmanTable))
      (hellmanAttack mergeRed 2 1)).map TableAttackSpec.lookupCost).sum ≤ 2 := by
  have hclean : cleanHellmanTable = [(2, 0)] := by
    unfold cleanHellmanTable
    rw [evalPure_rainbowPreprocess]
    simp only [List.map_cons, List.map_nil, rainbowChainPure_const]
    rfl
  have heval :
      (hellmanAttack mergeRed 2 1).evalPure
        (OracleComp.sumPure id (List.lookup · cleanHellmanTable)) = some 1 :=
    evalPure_hellmanAttack_rainbowPreprocess_of_injective Function.injective_id
      (starts := [0]) (pw₀ := 0) (col := 1) (by decide) (by decide) (by decide) rfl rfl
  have hcost₁ :
      ((OracleComp.queriesWith (OracleComp.sumPure id (List.lookup · cleanHellmanTable))
        (hellmanAttack mergeRed 2 1)).map TableAttackSpec.hashCost).sum = 2 := by
    refine sum_map_hashCost_queriesWith_hellmanAttack_of_no_false_alarm ?_
    intro k hk pw₀ hlk
    rw [hclean] at hlk
    have hk_cases : k = 0 ∨ k = 1 := by omega
    rcases hk_cases with rfl | rfl <;> decide +revert
  have hcost₄ :
      ((OracleComp.queriesWith (OracleComp.sumPure id (List.lookup · cleanHellmanTable))
        (hellmanAttack mergeRed 2 4)).map TableAttackSpec.hashCost).sum = 2 := by
    refine sum_map_hashCost_queriesWith_hellmanAttack_of_no_false_alarm ?_
    intro k hk pw₀ hlk
    rw [hclean] at hlk
    have hk_cases : k = 0 ∨ k = 1 := by omega
    rcases hk_cases with rfl | rfl <;> decide +revert
  exact ⟨heval, hcost₁, hcost₄, sum_map_lookupCost_queriesWith_hellmanAttack_le _ _ _ 2 1⟩

/-- Merged two-chain table (`τ = 2`, starting points `[0, 3]`, storing `[(2, 0), (3, 3)]`),
modeling Fig. 18.14 ([BonehShoup2023], pp. 744–745): on `y = 3`, step `k = 0` computes
`mergeRed 3 = 2`, hitting `(2, 0)` as a false alarm (`mergeRed 0 = 1 ≠ 3`), before step `k = 1`
hits `(3, 3)` and recovers `3`. -/
private def mergedHellmanTable : List (ℕ × ℕ) :=
  (rainbowPreprocess (fun _ => mergeRed) 2 [0, 3]).evalPure id

/-- **False-alarm rejection and recovery + necessity of the no-false-alarm hypothesis.**
On `mergedHellmanTable` and `y = 3`:
1. both `rainbowAttack` and `hellmanAttack` reject the false alarm `1 ≠ 3` at `k = 0` and still
   recover the true preimage `some 3` via two-phase completeness (verified by
   `hellmanAttack_sound`),
2. `rainbowAttack`'s run hash cost stays within `τ * (τ - 1) / 2 + hits * τ = 5`, and
3. `hellmanAttack` makes at least `4 > 2 = τ` hash evaluations (bounded above by
   `τ * (τ + 3) / 2 = 5`), showing that
   `add_le_sum_map_hashCost_queriesWith_hellmanAttack_of_false_alarm` is non-vacuous and that the
   no-false-alarm hypothesis of `sum_map_hashCost_queriesWith_hellmanAttack_of_no_false_alarm`
   cannot be dropped. -/
example :
    (rainbowAttack (fun _ => mergeRed) 2 3).evalPure
      (OracleComp.sumPure id (List.lookup · mergedHellmanTable)) = some 3 ∧
    (∃ pw', (hellmanAttack mergeRed 2 3).evalPure
      (OracleComp.sumPure id (List.lookup · mergedHellmanTable)) = some pw' ∧ id pw' = 3) ∧
    (hellmanAttack mergeRed 2 3).evalPure
      (OracleComp.sumPure id (List.lookup · mergedHellmanTable)) = some 3 ∧
    id 3 = 3 ∧
    ((OracleComp.queriesWith (OracleComp.sumPure id (List.lookup · mergedHellmanTable))
      (rainbowAttack (fun _ => mergeRed) 2 3)).map TableAttackSpec.hashCost).sum ≤ 5 ∧
    2 < ((OracleComp.queriesWith (OracleComp.sumPure id (List.lookup · mergedHellmanTable))
      (hellmanAttack mergeRed 2 3)).map TableAttackSpec.hashCost).sum ∧
    ((OracleComp.queriesWith (OracleComp.sumPure id (List.lookup · mergedHellmanTable))
      (hellmanAttack mergeRed 2 3)).map TableAttackSpec.hashCost).sum ≤ 5 := by
  have htable : mergedHellmanTable = [(2, 0), (3, 3)] := by
    unfold mergedHellmanTable
    rw [evalPure_rainbowPreprocess]
    simp only [List.map_cons, List.map_nil, rainbowChainPure_const]
    rfl
  have hnodup_rb : ([0, 3].map (rainbowChainPure id (fun _ => mergeRed) 0 2)).Nodup := by
    simp only [List.map_cons, List.map_nil, rainbowChainPure_const]
    decide
  have hrainbow :
      (rainbowAttack (fun _ => mergeRed) 2 3).evalPure
        (OracleComp.sumPure id (List.lookup · mergedHellmanTable)) = some 3 :=
    evalPure_rainbowAttack_rainbowPreprocess_of_injective Function.injective_id
      (starts := [0, 3]) (pw₀ := 3) (col := 0) (by decide) hnodup_rb (by decide)
      (rainbowChainPure_zero _ _ _ _) rfl
  have hhellman_ex :
      ∃ pw', (hellmanAttack mergeRed 2 3).evalPure
        (OracleComp.sumPure id (List.lookup · mergedHellmanTable)) = some pw' ∧ id pw' = 3 :=
    exists_evalPure_hellmanAttack_rainbowPreprocess (starts := [0, 3]) (pw₀ := 3) (col := 0)
      (by decide) (by decide) (by decide) rfl
  have hhellman :
      (hellmanAttack mergeRed 2 3).evalPure
        (OracleComp.sumPure id (List.lookup · mergedHellmanTable)) = some 3 :=
    evalPure_hellmanAttack_rainbowPreprocess_of_injective Function.injective_id
      (starts := [0, 3]) (pw₀ := 3) (col := 0) (by decide) (by decide) (by decide) rfl rfl
  have hrb_cost :
      ((OracleComp.queriesWith (OracleComp.sumPure id (List.lookup · mergedHellmanTable))
        (rainbowAttack (fun _ => mergeRed) 2 3)).map TableAttackSpec.hashCost).sum ≤ 5 := by
    refine (sum_map_hashCost_queriesWith_rainbowAttack_le id
      (List.lookup · mergedHellmanTable) (fun _ => mergeRed) 2 3).trans ?_
    rw [htable]
    simp only [rainbowChainPure_const]
    decide
  have hhm_fa :
      2 + (2 - 0) ≤ ((OracleComp.queriesWith
        (OracleComp.sumPure id (List.lookup · mergedHellmanTable))
        (hellmanAttack mergeRed 2 3)).map TableAttackSpec.hashCost).sum := by
    refine add_le_sum_map_hashCost_queriesWith_hellmanAttack_of_false_alarm (pw₀ := 0)
      (by decide) (fun _ hj => absurd hj (Nat.not_lt_zero _)) ?_ (by decide)
    rw [htable]
    decide
  exact ⟨hrainbow, hhellman_ex, hhellman, hellmanAttack_sound hhellman, hrb_cost, by omega,
    sum_map_hashCost_queriesWith_hellmanAttack_le id
      (List.lookup · mergedHellmanTable) mergeRed 2 3⟩

/-- **Tightness of Hellman's `τ * (τ + 3) / 2` worst-case hash budget.** At `τ = 2`, when `y = 0`
has no preimage under `shiftHash` and every lookup hits `[(0, 0)]` as a false alarm,
`hellmanAttack` spends `3 + 2 = 5 = 2 * (2 + 3) / 2` hash evaluations, matching
`isCostBounded_hashCost_hellmanAttack` and `sum_map_hashCost_queriesWith_hellmanAttack_le` with
equality. -/
example :
    OracleComp.IsCostBounded TableAttackSpec.hashCost (hellmanAttack (fun _ : ℕ => 0) 2 0) 5 ∧
    ((OracleComp.queriesWith (OracleComp.sumPure shiftHash (List.lookup · [(0, 0)]))
      (hellmanAttack (fun _ => 0) 2 0)).map TableAttackSpec.hashCost).sum = 5 := by
  refine ⟨isCostBounded_hashCost_hellmanAttack (fun _ => 0) 2 0, ?_⟩
  rw [hellmanAttack, sum_map_hashCost_queriesWith_hellmanLoop_succ,
    sum_map_hashCost_queriesWith_hellmanLoop_succ, sum_map_hashCost_queriesWith_hellmanLoop_zero]
  simp only [shiftHash]
  decide

/-! ### Necessity of hypotheses -/

/-- **Necessity of distinct endpoints (`Nodup` / no earlier duplicate endpoint).** When `starts =
[0, 1]` merge to the same `1`-step endpoint `0` under `g _ _ = 0`, `List.lookup` recovers the first
start `0` (`lookup_evalPure_rainbowPreprocess_eq_some_iff`), while the shadowed start `1` is not
inverted on `y = 1` ([BonehShoup2023], Section 18.7, p. 745). -/
example :
    ((rainbowPreprocess (fun _ _ : ℕ => 0) 1 [0, 1]).evalPure id).lookup 0 = some 0 ∧
    (rainbowAttack (fun _ _ : ℕ => 0) 1 1).evalPure
      (OracleComp.sumPure id
        (List.lookup · ((rainbowPreprocess (fun _ _ : ℕ => 0) 1 [0, 1]).evalPure id))) = none := by
  refine ⟨lookup_evalPure_rainbowPreprocess_eq_some_iff.mpr
    ⟨by simp only [rainbowChainPure_succ, rainbowChainPure_zero], [], [1], rfl,
      fun _ h => False.elim (List.not_mem_nil h)⟩, ?_⟩
  rw [evalPure_rainbowAttack, evalPure_rainbowPreprocess]
  simp only [List.range_one, List.findSome?_cons, List.findSome?_nil, Nat.reduceSub,
    rainbowChainPure_succ, rainbowChainPure_zero]
  decide

/-- **Necessity of `Function.Injective h` for exact password recovery.** With a non-injective hash
`h(x) = x % 2`, `h 2 = h 0 = 0`; a table storing starting point `0` inverts `y = h 2` to `some 0`
(a valid preimage, `0 % 2 = 0`), not `some 2`, showing that `Function.Injective h` in
`evalPure_rainbowAttack_of_injective` cannot be dropped. -/
example :
    (rainbowAttack (fun _ y => y) 1 ((· % 2) 2)).evalPure
      (OracleComp.sumPure (· % 2) (List.lookup · [(0, 0)])) = some 0 ∧
    (0 : ℕ) % 2 = 2 % 2 := by
  refine ⟨?_, rfl⟩
  rw [evalPure_rainbowAttack]
  simp only [List.range_one, List.findSome?_cons, List.findSome?_nil, Nat.reduceSub,
    rainbowChainPure_zero]
  decide

end CslibFrontierTests.Crypto.RainbowTable
