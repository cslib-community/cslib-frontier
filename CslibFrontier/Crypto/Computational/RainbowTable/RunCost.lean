/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.RainbowTable
import CslibFrontier.Languages.Probabilistic.QueriesWith.Cost
import CslibFrontier.Languages.Probabilistic.QueryCount.Sum
import CslibFrontier.Languages.Probabilistic.Traverse.FindM
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Deterministic run-cost analysis of rainbow-table and Hellman inversion

Deterministic request-trace (`OracleComp.queriesWith`) cost bounds for `rainbowAttack` and
`hellmanAttack` ([BonehShoup2023], Section 18.7, pp. 743–746), consuming the four decomposition
lemmas of `CslibFrontier.Languages.Probabilistic.QueriesWith.Cost`.

## Correspondence with [BonehShoup2023], Section 18.7

* **Rainbow tables (p. 746; Fig. 18.13b, p. 744).** Algorithm `A₁` loops `i = τ` down to `1` (step
  index `k = 0, ..., τ - 1` testing column `τ - 1 - k`).
  - As printed, line (2) computes `z ← f_τ(⋯ f_{i+1}(g_i(y)) ⋯)`, evaluating `f` `τ - i = k` times
    at iteration `i` (`0` times at `i = τ`, `1` time at `i = τ - 1`, ..., `τ - 1` times at `i = 1`),
    so `0 + 1 + ⋯ + (τ - 1) = τ * (τ - 1) / 2` hash evaluations across all `τ` steps when every
    lookup misses (`sum_map_hashCost_queriesWith_rainbowAttack_of_forall_lookup_eq_none`).
  - Line (3) makes `1` lookup in `L` per executed step, so at most `τ` lookups on any run
    (`sum_map_lookupCost_queriesWith_rainbowAttack_le`) and `τ` lookups whenever the search returns
    `none` (`sum_map_lookupCost_queriesWith_rainbowAttack_of_evalPure_eq_none`).
  - On a table hit at step `k < τ`, lines (4)–(5) spend `(τ - 1 - k) + 1 = τ - k` additional hash
    evaluations (`k + (τ - k) = τ` total for step `k`:
    `sum_map_hashCost_queriesWith_rainbowAttackStep`). Across any run with `hits` candidate
    endpoints present in `L`, total hash cost is at most `τ * (τ - 1) / 2 + hits * τ`
    (`sum_map_hashCost_queriesWith_rainbowAttack_le`). When no table hit along the run is a false
    alarm, the first hit terminates `findSomeM?`, giving at most
    `τ * (τ - 1) / 2 + τ = τ * (τ + 1) / 2` hash evaluations
    (`sum_map_hashCost_queriesWith_rainbowAttack_le_of_no_false_alarm`). Note on p. 746: the book
    states `1 + 2 + ⋯ + τ = τ(τ + 1)/2 ≈ τ²/2` for the worst-case work *of line (2)* alone and sets
    maximum running time `t := τ²/2`; our `τ * (τ + 1) / 2` bound sums line (2)'s printed
    `0 + ⋯ + (τ - 1)` count *plus* lines (4)–(5) on a single hit, coinciding numerically with the
    book's line-(2) figure.
* **Hellman's basic tradeoff (pp. 743–745; Fig. 18.13a, p. 744, and Fig. 18.14, p. 745).**
  `hellmanAttack` advances `z ← g₀(h(z))` by one step per iteration instead of recomputing from `y`:
  - Across arbitrary oracle replies (even if every lookup is a false alarm), a run makes at most `τ`
    lookups and at most `τ * (τ + 3) / 2` hash evaluations
    (`sum_map_lookupCost_queriesWith_hellmanAttack_le`,
    `sum_map_hashCost_queriesWith_hellmanAttack_le`), and at least `τ` hash evaluations
    (`le_sum_map_hashCost_queriesWith_hellmanAttack`).
  - Without false alarms, every run—whether inverted at step `k` (`k + (τ - 1 - k) + 1 = τ`) or
    missing on all `τ` lookups (`τ` single-step advances)—makes `τ` hash evaluations
    (`sum_map_hashCost_queriesWith_hellmanAttack_of_no_false_alarm`), matching p. 744 ("`τ`
    evaluations of `f` and at most `τ` lookups in `L`").
  - A false alarm reached at iteration `k < τ` (with only misses or false alarms before `k`) adds at
    least `τ - k` extra hash evaluations above `τ`
    (`add_le_sum_map_hashCost_queriesWith_hellmanAttack_of_false_alarm`).

## Main results

* `Cslib.Crypto.sum_map_lookupCost_queriesWith_rainbowAttackStep`,
  `Cslib.Crypto.sum_map_hashCost_queriesWith_rainbowAttackStep`: per-step lookup (`1`) and hash
  (`k` on miss, `τ` on hit for `k < τ`) query counts of `rainbowAttackStep`.
* `Cslib.Crypto.sum_map_lookupCost_queriesWith_rainbowAttack_le`,
  `Cslib.Crypto.sum_map_lookupCost_queriesWith_rainbowAttack_of_evalPure_eq_none`: run lookup count
  `≤ τ`, with equality `= τ` when `rainbowAttack` returns `none`.
* `Cslib.Crypto.sum_map_hashCost_queriesWith_rainbowAttack_of_forall_lookup_eq_none`: exact
  `τ * (τ - 1) / 2` hash query count when all `τ` lookups miss.
* `Cslib.Crypto.sum_map_hashCost_queriesWith_rainbowAttack_le`,
  `Cslib.Crypto.sum_map_hashCost_queriesWith_rainbowAttack_le_of_no_false_alarm`: run hash bound
  `τ * (τ - 1) / 2 + hits * τ`, specializing to `τ * (τ + 1) / 2` without false alarms.
* `Cslib.Crypto.sum_map_lookupCost_queriesWith_hellmanAttack_le`,
  `Cslib.Crypto.sum_map_hashCost_queriesWith_hellmanAttack_le`: unconditional run lookup (`≤ τ`) and
  hash (`≤ τ * (τ + 3) / 2`) bounds for `hellmanAttack`.
* `Cslib.Crypto.sum_map_hashCost_queriesWith_hellmanLoop_succ`,
  `Cslib.Crypto.le_sum_map_hashCost_queriesWith_hellmanAttack`,
  `Cslib.Crypto.sum_map_hashCost_queriesWith_hellmanAttack_of_no_false_alarm`,
  `Cslib.Crypto.add_le_sum_map_hashCost_queriesWith_hellmanAttack_of_false_alarm`: per-iteration
  recursion, lower bound `τ`, exact no-false-alarm count `= τ`, and `τ + (τ - k)` false-alarm lower
  bound for `hellmanAttack`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 18.7, pp. 742–746.
-/

public section

namespace Cslib.Crypto

open Cslib

variable {P Y : Type}

/-! ### Private trace and summation helpers -/

private theorem interpret_id_eq_evalPure {ι α : Type} {spec : OracleSpec ι}
    (answer : (q : ι) → spec q) (prog : OracleComp spec α) :
    OracleComp.interpret (m := Id) answer prog = prog.evalPure answer := by
  rfl

private theorem sum_map_queriesWith_liftLeft_bind {α β : Type} {cost : P ⊕ P → ℕ} {c : ℕ}
    (hc : ∀ x, cost (.inl x) = c) (h : P → Y) (lookup : P → Option P)
    (prog : OracleComp (fun _ : P => Y) α) (k : α → OracleComp (TableAttackSpec P Y) β) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (OracleComp.liftLeft prog >>= k)).map cost).sum =
      (OracleComp.queriesWith h prog).length * c +
        ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
          (k (prog.evalPure h))).map cost).sum := by
  rw [OracleComp.queriesWith_bind, interpret_id_eq_evalPure, OracleComp.evalPure_liftLeft,
    List.map_append, List.sum_append, OracleComp.queriesWith_liftLeft, List.map_map]
  have hconst : (cost ∘ @Sum.inl P P) = fun _ => c := funext hc
  rw [hconst, List.map_const', List.sum_replicate, smul_eq_mul]

private theorem sum_map_hashCost_queriesWith_liftLeft_query_bind {β : Type} (h : P → Y)
    (lookup : P → Option P) (x : P) (k : Y → OracleComp (TableAttackSpec P Y) β) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (OracleComp.liftLeft (OracleComp.query x) >>= k)).map TableAttackSpec.hashCost).sum =
      1 + ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
        (k (h x))).map TableAttackSpec.hashCost).sum := by
  rw [sum_map_queriesWith_liftLeft_bind TableAttackSpec.hashCost_inl, OracleComp.evalPure_query,
    OracleComp.queriesWith_query, List.length_singleton, Nat.mul_one]

private theorem sum_map_queriesWith_liftRight_query_bind {β : Type} (cost : P ⊕ P → ℕ)
    (h : P → Y) (lookup : P → Option P) (z : P)
    (k : Option P → OracleComp (TableAttackSpec P Y) β) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (OracleComp.liftRight (OracleComp.query z) >>= k)).map cost).sum =
      cost (.inr z) + ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
        (k (lookup z))).map cost).sum := by
  rw [OracleComp.liftRight_query, OracleComp.queriesWith_query_bind, List.map_cons, List.sum_cons,
    OracleComp.sumPure_inr]

private theorem sum_range_eq (τ : ℕ) : (List.range τ).sum = τ * (τ - 1) / 2 := by
  suffices (List.range τ).sum = ∑ i ∈ Finset.range τ, i by rw [this, Finset.sum_range_id]
  induction τ with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.sum_append, List.sum_singleton, ih, Finset.sum_range_succ]

private theorem range_sum_add_self (τ : ℕ) :
    τ * (τ - 1) / 2 + τ = τ * (τ + 1) / 2 := by
  rw [← Finset.sum_range_id τ, ← Finset.sum_range_succ (fun i => i) τ,
    Finset.sum_range_id (τ + 1), Nat.add_sub_cancel, Nat.mul_comm]

/-! ### Run-cost analysis of `rainbowAttack` -/

section RainbowRunCost

variable [DecidableEq Y]

/-- Every step `k` of `rainbowAttack` makes `1` table lookup along a deterministic run. -/
@[simp]
theorem sum_map_lookupCost_queriesWith_rainbowAttackStep (h : P → Y) (lookup : P → Option P)
    (g : ℕ → Y → P) (τ : ℕ) (y : Y) (k : ℕ) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (rainbowAttackStep g τ y k)).map TableAttackSpec.lookupCost).sum = 1 := by
  unfold rainbowAttackStep
  rw [sum_map_queriesWith_liftLeft_bind TableAttackSpec.lookupCost_inl, Nat.mul_zero, Nat.zero_add,
    evalPure_rainbowChain, sum_map_queriesWith_liftRight_query_bind, TableAttackSpec.lookupCost_inr]
  cases lookup (rainbowChainPure h g (τ - k) k (g (τ - 1 - k) y)) with
  | none => simp only [OracleComp.queriesWith_pure, List.map_nil, List.sum_nil, Nat.add_zero]
  | some pw₀ =>
    rw [sum_map_queriesWith_liftLeft_bind TableAttackSpec.lookupCost_inl, Nat.mul_zero,
      Nat.zero_add, evalPure_rainbowChain,
      sum_map_queriesWith_liftLeft_bind TableAttackSpec.lookupCost_inl, Nat.mul_zero, Nat.zero_add,
      OracleComp.evalPure_query]
    split_ifs <;>
      simp only [OracleComp.queriesWith_pure, List.map_nil, List.sum_nil, Nat.add_zero]

/-- At step `k < τ`, `rainbowAttackStep` makes `k` hash queries when `lookup` misses and `τ` hash
queries (`k` forward, `τ - 1 - k` backward from `pw₀`, `1` verification) when `lookup` hits. -/
theorem sum_map_hashCost_queriesWith_rainbowAttackStep (h : P → Y) (lookup : P → Option P)
    (g : ℕ → Y → P) {τ : ℕ} (y : Y) {k : ℕ} (hk : k < τ) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (rainbowAttackStep g τ y k)).map TableAttackSpec.hashCost).sum =
      if (lookup (rainbowChainPure h g (τ - k) k (g (τ - 1 - k) y))).isSome then τ else k := by
  unfold rainbowAttackStep
  rw [sum_map_queriesWith_liftLeft_bind TableAttackSpec.hashCost_inl, Nat.mul_one,
    evalPure_rainbowChain, length_queriesWith_rainbowChain,
    sum_map_queriesWith_liftRight_query_bind, TableAttackSpec.hashCost_inr, Nat.zero_add]
  cases lookup (rainbowChainPure h g (τ - k) k (g (τ - 1 - k) y)) with
  | none =>
    simp only [OracleComp.queriesWith_pure, List.map_nil, List.sum_nil, Nat.add_zero,
      Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  | some pw₀ =>
    rw [sum_map_queriesWith_liftLeft_bind TableAttackSpec.hashCost_inl, Nat.mul_one,
      evalPure_rainbowChain, length_queriesWith_rainbowChain,
      sum_map_hashCost_queriesWith_liftLeft_query_bind]
    simp only [Option.isSome_some, ↓reduceIte]
    split_ifs <;> simp only [OracleComp.queriesWith_pure, List.map_nil, List.sum_nil] <;> omega

/-- Along any deterministic run, `rainbowAttack` makes at most `τ` table lookups
([BonehShoup2023], Section 18.7, p. 746). -/
theorem sum_map_lookupCost_queriesWith_rainbowAttack_le (h : P → Y) (lookup : P → Option P)
    (g : ℕ → Y → P) (τ : ℕ) (y : Y) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (rainbowAttack g τ y)).map TableAttackSpec.lookupCost).sum ≤ τ :=
  OracleComp.IsCostBounded.sum_map_queriesWith_le (OracleComp.sumPure h lookup)
    (isCostBounded_lookupCost_rainbowAttack g τ y)

/-- When `rainbowAttack` returns `none`, all `τ` steps execute and the run makes `τ` table
lookups. -/
theorem sum_map_lookupCost_queriesWith_rainbowAttack_of_evalPure_eq_none {h : P → Y}
    {lookup : P → Option P} {g : ℕ → Y → P} {τ : ℕ} {y : Y}
    (heval : (rainbowAttack g τ y).evalPure (OracleComp.sumPure h lookup) = none) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (rainbowAttack g τ y)).map TableAttackSpec.lookupCost).sum = τ := by
  rw [rainbowAttack, OracleComp.evalPure_findSomeM?, List.findSome?_eq_none_iff] at heval
  rw [rainbowAttack, OracleComp.queriesWith_findSomeM?_of_forall_eq_none _ _ heval,
    List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map]
  simp only [Function.comp_def, sum_map_lookupCost_queriesWith_rainbowAttackStep, List.map_const',
    List.length_range, List.sum_replicate, smul_eq_mul, Nat.mul_one]

/-- **Exact miss-run hash count of `rainbowAttack`** ([BonehShoup2023], Section 18.7, line 2 of
Algorithm `A₁`, p. 746): when no candidate endpoint hits the table, `rainbowAttack` evaluates
`0 + 1 + ⋯ + (τ - 1) = τ * (τ - 1) / 2` hashes (`τ - i` evaluations at iteration `i = τ` down to
`1` as printed on line 2). -/
theorem sum_map_hashCost_queriesWith_rainbowAttack_of_forall_lookup_eq_none {h : P → Y}
    {lookup : P → Option P} {g : ℕ → Y → P} {τ : ℕ} {y : Y}
    (hmiss : ∀ k < τ, lookup (rainbowChainPure h g (τ - k) k (g (τ - 1 - k) y)) = none) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (rainbowAttack g τ y)).map TableAttackSpec.hashCost).sum = τ * (τ - 1) / 2 := by
  have hsteps : ∀ k ∈ List.range τ,
      (rainbowAttackStep g τ y k).evalPure (OracleComp.sumPure h lookup) = none := by
    intro k hk
    rw [evalPure_rainbowAttackStep, hmiss k (List.mem_range.mp hk)]
  rw [rainbowAttack, OracleComp.queriesWith_findSomeM?_of_forall_eq_none _ _ hsteps,
    List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map]
  rw [List.map_congr_left (g := id) fun k hk => ?_, List.map_id, sum_range_eq]
  simp only [Function.comp_apply, id_eq,
    sum_map_hashCost_queriesWith_rainbowAttackStep h lookup g y (List.mem_range.mp hk),
    hmiss k (List.mem_range.mp hk), Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

private theorem sum_map_hashCost_findSomeM?_le (h : P → Y) (lookup : P → Option P)
    (g : ℕ → Y → P) (τ : ℕ) (y : Y) (xs : List ℕ) (hxs : ∀ k ∈ xs, k < τ) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (xs.findSomeM? (rainbowAttackStep g τ y))).map TableAttackSpec.hashCost).sum ≤
      xs.sum +
        (xs.countP fun k =>
          (lookup (rainbowChainPure h g (τ - k) k (g (τ - 1 - k) y))).isSome) * τ := by
  induction xs with
  | nil =>
    rw [List.findSomeM?_nil]
    simp only [OracleComp.queriesWith_pure, List.map_nil, List.sum_nil, List.countP_nil,
      Nat.zero_mul, Nat.zero_le]
  | cons k ks ih =>
    have hk : k < τ := hxs k List.mem_cons_self
    rw [OracleComp.queriesWith_findSomeM?_cons, List.map_append, List.sum_append,
      sum_map_hashCost_queriesWith_rainbowAttackStep h lookup g y hk, List.sum_cons,
      List.countP_cons]
    have htail :
        ((if ((rainbowAttackStep g τ y k).evalPure (OracleComp.sumPure h lookup)).isSome then []
          else OracleComp.queriesWith (OracleComp.sumPure h lookup)
            (ks.findSomeM? (rainbowAttackStep g τ y))).map TableAttackSpec.hashCost).sum ≤
          ks.sum +
            (ks.countP fun k' =>
              (lookup (rainbowChainPure h g (τ - k') k' (g (τ - 1 - k') y))).isSome) * τ := by
      split_ifs
      · simp only [List.map_nil, List.sum_nil, Nat.zero_le]
      · exact ih fun k' hk' => hxs k' (List.mem_cons_of_mem k hk')
    cases lookup (rainbowChainPure h g (τ - k) k (g (τ - 1 - k) y)) <;>
      simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte,
        Nat.add_mul, Nat.one_mul, Nat.add_zero] <;> omega

/-- **General run hash bound of `rainbowAttack`.** Along any deterministic run (including early
termination when a preimage is found), total hash evaluations are at most
`τ * (τ - 1) / 2 + hits * τ`, where `hits` counts steps `k < τ` whose candidate endpoint hits
`lookup`. -/
theorem sum_map_hashCost_queriesWith_rainbowAttack_le (h : P → Y) (lookup : P → Option P)
    (g : ℕ → Y → P) (τ : ℕ) (y : Y) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (rainbowAttack g τ y)).map TableAttackSpec.hashCost).sum ≤
      τ * (τ - 1) / 2 +
        ((List.range τ).countP fun k =>
          (lookup (rainbowChainPure h g (τ - k) k (g (τ - 1 - k) y))).isSome) * τ := by
  have hle := sum_map_hashCost_findSomeM?_le h lookup g τ y (List.range τ)
    fun k hk => List.mem_range.mp hk
  rwa [sum_range_eq] at hle

private theorem sum_map_hashCost_findSomeM?_le_of_no_false_alarm {h : P → Y}
    {lookup : P → Option P} {g : ℕ → Y → P} {τ : ℕ} {y : Y} (xs : List ℕ)
    (hxs : ∀ k ∈ xs, k < τ)
    (hnofa : ∀ k ∈ xs, ∀ pw₀,
      lookup (rainbowChainPure h g (τ - k) k (g (τ - 1 - k) y)) = some pw₀ →
        h (rainbowChainPure h g 0 (τ - 1 - k) pw₀) = y) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (xs.findSomeM? (rainbowAttackStep g τ y))).map TableAttackSpec.hashCost).sum ≤
      xs.sum + τ := by
  induction xs with
  | nil =>
    rw [List.findSomeM?_nil]
    simp only [OracleComp.queriesWith_pure, List.map_nil, List.sum_nil, Nat.zero_le]
  | cons k ks ih =>
    have hk : k < τ := hxs k List.mem_cons_self
    rw [OracleComp.queriesWith_findSomeM?_cons, List.map_append, List.sum_append,
      sum_map_hashCost_queriesWith_rainbowAttackStep h lookup g y hk, List.sum_cons]
    cases hlk : lookup (rainbowChainPure h g (τ - k) k (g (τ - 1 - k) y)) with
    | none =>
      simp only [evalPure_rainbowAttackStep, hlk, Option.isSome_none, Bool.false_eq_true,
        ↓reduceIte]
      have htail := ih (fun k' hk' => hxs k' (List.mem_cons_of_mem k hk'))
        fun k' hk' => hnofa k' (List.mem_cons_of_mem k hk')
      omega
    | some pw₀ =>
      simp only [evalPure_rainbowAttackStep, hlk, hnofa k List.mem_cons_self pw₀ hlk,
        Option.isSome_some, ↓reduceIte, List.map_nil, List.sum_nil, Nat.add_zero]
      omega

/-- **Rainbow-table run hash bound without false alarms** (cf. [BonehShoup2023], Section 18.7,
p. 746): when every table hit along the candidate endpoints yields a valid preimage of `y`, the
first hit terminates `rainbowAttack`, so the run makes at most `τ * (τ + 1) / 2` hash evaluations
(`0 + ⋯ + (τ - 1) = τ * (τ - 1) / 2` from line 2 as printed across `i = τ` down to `1`, plus at
most `τ` from lines 4–5 reconstructing and verifying a single hit; this total coincides numerically
with p. 746's `1 + 2 + ⋯ + τ = τ(τ + 1)/2 ≈ τ²/2` figure stated for the worst-case work of line 2
alone in setting `t := τ²/2`). -/
theorem sum_map_hashCost_queriesWith_rainbowAttack_le_of_no_false_alarm {h : P → Y}
    {lookup : P → Option P} {g : ℕ → Y → P} {τ : ℕ} {y : Y}
    (hnofa : ∀ k < τ, ∀ pw₀,
      lookup (rainbowChainPure h g (τ - k) k (g (τ - 1 - k) y)) = some pw₀ →
        h (rainbowChainPure h g 0 (τ - 1 - k) pw₀) = y) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (rainbowAttack g τ y)).map TableAttackSpec.hashCost).sum ≤ τ * (τ + 1) / 2 := by
  have hle := sum_map_hashCost_findSomeM?_le_of_no_false_alarm (List.range τ)
    (fun k hk => List.mem_range.mp hk) fun k hk => hnofa k (List.mem_range.mp hk)
  rwa [sum_range_eq, range_sum_add_self] at hle

end RainbowRunCost

/-! ### Run-cost analysis of `hellmanAttack` -/

section HellmanRunCost

variable [DecidableEq Y]

/-- Along any deterministic run, `hellmanAttack` makes at most `τ` table lookups
([BonehShoup2023], Section 18.7, p. 744). -/
theorem sum_map_lookupCost_queriesWith_hellmanAttack_le (h : P → Y) (lookup : P → Option P)
    (g₀ : Y → P) (τ : ℕ) (y : Y) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (hellmanAttack g₀ τ y)).map TableAttackSpec.lookupCost).sum ≤ τ :=
  OracleComp.IsCostBounded.sum_map_queriesWith_le (OracleComp.sumPure h lookup)
    (isCostBounded_lookupCost_hellmanAttack g₀ τ y)

/-- Along any deterministic run (even when every lookup is a false alarm), `hellmanAttack` makes at
most `τ * (τ + 3) / 2` hash evaluations. -/
theorem sum_map_hashCost_queriesWith_hellmanAttack_le (h : P → Y) (lookup : P → Option P)
    (g₀ : Y → P) (τ : ℕ) (y : Y) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (hellmanAttack g₀ τ y)).map TableAttackSpec.hashCost).sum ≤ τ * (τ + 3) / 2 :=
  OracleComp.IsCostBounded.sum_map_queriesWith_le (OracleComp.sumPure h lookup)
    (isCostBounded_hashCost_hellmanAttack g₀ τ y)

/-- Zero remaining iterations of `hellmanLoop` make `0` hash evaluations. -/
@[simp]
theorem sum_map_hashCost_queriesWith_hellmanLoop_zero (h : P → Y) (lookup : P → Option P)
    (g₀ : Y → P) (y : Y) (z : P) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (hellmanLoop g₀ y 0 z)).map TableAttackSpec.hashCost).sum = 0 := by
  rfl

/-- One iteration of `hellmanLoop` at remaining depth `m + 1` makes `1` hash evaluation before
recursing on a lookup miss, `m + 1` hash evaluations on a verified hit, and `m + 2` hash
evaluations before recursing on a false alarm. -/
theorem sum_map_hashCost_queriesWith_hellmanLoop_succ (h : P → Y) (lookup : P → Option P)
    (g₀ : Y → P) (y : Y) (m : ℕ) (z : P) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (hellmanLoop g₀ y (m + 1) z)).map TableAttackSpec.hashCost).sum =
      match lookup z with
      | none =>
        1 + ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
          (hellmanLoop g₀ y m (g₀ (h z)))).map TableAttackSpec.hashCost).sum
      | some pw₀ =>
        if h ((fun x => g₀ (h x))^[m] pw₀) = y then
          m + 1
        else
          m + 2 + ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
            (hellmanLoop g₀ y m (g₀ (h z)))).map TableAttackSpec.hashCost).sum := by
  conv_lhs => unfold hellmanLoop
  rw [sum_map_queriesWith_liftRight_query_bind, TableAttackSpec.hashCost_inr, Nat.zero_add]
  cases lookup z with
  | none =>
    exact sum_map_hashCost_queriesWith_liftLeft_query_bind h lookup z _
  | some pw₀ =>
    simp only
    rw [sum_map_queriesWith_liftLeft_bind TableAttackSpec.hashCost_inl, Nat.mul_one,
      evalPure_rainbowChain, rainbowChainPure_const, length_queriesWith_rainbowChain,
      sum_map_hashCost_queriesWith_liftLeft_query_bind]
    split_ifs with hcheck
    · simp only [OracleComp.queriesWith_pure, List.map_nil, List.sum_nil, Nat.add_zero]
    · rw [sum_map_hashCost_queriesWith_liftLeft_query_bind]; omega

private theorem le_sum_map_hashCost_hellmanLoop (h : P → Y) (lookup : P → Option P)
    (g₀ : Y → P) (y : Y) (rem : ℕ) (z : P) :
    rem ≤ ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (hellmanLoop g₀ y rem z)).map TableAttackSpec.hashCost).sum := by
  induction rem generalizing z with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    rw [sum_map_hashCost_queriesWith_hellmanLoop_succ]
    have hrec := ih (g₀ (h z))
    cases lookup z with
    | none => simp only; omega
    | some pw₀ => simp only; split_ifs <;> omega

/-- Every deterministic run of `hellmanAttack` makes at least `τ` hash evaluations. -/
theorem le_sum_map_hashCost_queriesWith_hellmanAttack (h : P → Y) (lookup : P → Option P)
    (g₀ : Y → P) (τ : ℕ) (y : Y) :
    τ ≤ ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (hellmanAttack g₀ τ y)).map TableAttackSpec.hashCost).sum :=
  le_sum_map_hashCost_hellmanLoop h lookup g₀ y τ (g₀ y)

private theorem sum_map_hashCost_hellmanLoop_of_no_false_alarm {h : P → Y}
    {lookup : P → Option P} {g₀ : Y → P} {y : Y} (rem : ℕ) (z : P)
    (hnofa : ∀ k < rem, ∀ pw₀,
      lookup ((fun x => g₀ (h x))^[k] z) = some pw₀ →
        h ((fun x => g₀ (h x))^[rem - 1 - k] pw₀) = y) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (hellmanLoop g₀ y rem z)).map TableAttackSpec.hashCost).sum = rem := by
  induction rem generalizing z with
  | zero => rfl
  | succ m ih =>
    rw [sum_map_hashCost_queriesWith_hellmanLoop_succ]
    cases hlk : lookup z with
    | none =>
      have hrec := ih (g₀ (h z)) fun k hk pw₀ hlk' => by
        rw [← Function.iterate_succ_apply (fun x => g₀ (h x)) k z] at hlk'
        simpa only [Nat.add_sub_cancel, Nat.sub_add_eq, Nat.sub_right_comm] using
          hnofa (k + 1) (Nat.succ_lt_succ hk) pw₀ hlk'
      simp only [hrec]; omega
    | some pw₀ =>
      have hgood : h ((fun x => g₀ (h x))^[m] pw₀) = y := by
        simpa only [Nat.add_sub_cancel, Nat.sub_zero] using hnofa 0 (Nat.zero_lt_succ m) pw₀ hlk
      simp only [hgood, ↓reduceIte]

/-- **Hellman's hash count without false alarms** ([BonehShoup2023], Section 18.7, p. 744): when
every table hit along the queried orbit yields a valid preimage of `y`, `hellmanAttack` makes `τ`
hash evaluations (`k` single-step advances prior to a hit at step `k`, `τ - 1 - k` steps to
reconstruct `pw`, and `1` evaluation to check `h(pw) = y`; or `τ` single-step advances when all `τ`
lookups miss). -/
theorem sum_map_hashCost_queriesWith_hellmanAttack_of_no_false_alarm {h : P → Y}
    {lookup : P → Option P} {g₀ : Y → P} {τ : ℕ} {y : Y}
    (hnofa : ∀ k < τ, ∀ pw₀,
      lookup ((fun x => g₀ (h x))^[k] (g₀ y)) = some pw₀ →
        h ((fun x => g₀ (h x))^[τ - 1 - k] pw₀) = y) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (hellmanAttack g₀ τ y)).map TableAttackSpec.hashCost).sum = τ :=
  sum_map_hashCost_hellmanLoop_of_no_false_alarm τ (g₀ y) hnofa

private theorem add_le_sum_map_hashCost_hellmanLoop_of_false_alarm {h : P → Y}
    {lookup : P → Option P} {g₀ : Y → P} {y : Y} {k rem : ℕ} {z pw₀ : P} (hk : k < rem)
    (hbefore : ∀ j < k, ∀ pw₁,
      lookup ((fun x => g₀ (h x))^[j] z) = some pw₁ →
        h ((fun x => g₀ (h x))^[rem - 1 - j] pw₁) ≠ y)
    (hhit : lookup ((fun x => g₀ (h x))^[k] z) = some pw₀)
    (hfa : h ((fun x => g₀ (h x))^[rem - 1 - k] pw₀) ≠ y) :
    rem + (rem - k) ≤ ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (hellmanLoop g₀ y rem z)).map TableAttackSpec.hashCost).sum := by
  induction k generalizing rem z with
  | zero =>
    obtain ⟨m, rfl⟩ : ∃ m, rem = m + 1 := ⟨rem - 1, by omega⟩
    rw [Function.iterate_zero_apply] at hhit
    simp only [Nat.add_sub_cancel, Nat.sub_zero] at hfa
    rw [sum_map_hashCost_queriesWith_hellmanLoop_succ, hhit]
    simp only [hfa, ↓reduceIte]
    have := le_sum_map_hashCost_hellmanLoop h lookup g₀ y m (g₀ (h z))
    omega
  | succ k ih =>
    obtain ⟨m, rfl⟩ : ∃ m, rem = m + 1 := ⟨rem - 1, by omega⟩
    rw [Function.iterate_succ_apply] at hhit
    rw [Nat.add_sub_cancel, Nat.sub_add_eq, Nat.sub_right_comm] at hfa
    have hrec := ih (Nat.lt_of_succ_lt_succ hk) (fun j hj pw₁ hlk' => by
      rw [← Function.iterate_succ_apply (fun x => g₀ (h x)) j z] at hlk'
      simpa only [Nat.add_sub_cancel, Nat.sub_add_eq, Nat.sub_right_comm] using
        hbefore (j + 1) (Nat.succ_lt_succ hj) pw₁ hlk') hhit hfa
    rw [sum_map_hashCost_queriesWith_hellmanLoop_succ]
    cases hlk : lookup z with
    | none => simp only; omega
    | some pw₁ =>
      have hne₀ : h ((fun x => g₀ (h x))^[m] pw₁) ≠ y := by
        simpa only [Nat.add_sub_cancel, Nat.sub_zero] using hbefore 0 (Nat.zero_lt_succ k) pw₁ hlk
      simp only [hne₀, ↓reduceIte]; omega

/-- **Extra hash cost of a false alarm in Hellman's attack** ([BonehShoup2023], Section 18.7,
pp. 744–745; Fig. 18.14, p. 745): a false alarm reached at iteration `k < τ` (with only misses or
false alarms at earlier iterations `j < k`) adds at least `τ - k` hash evaluations above `τ`. -/
theorem add_le_sum_map_hashCost_queriesWith_hellmanAttack_of_false_alarm {h : P → Y}
    {lookup : P → Option P} {g₀ : Y → P} {τ k : ℕ} {y : Y} {pw₀ : P} (hk : k < τ)
    (hbefore : ∀ j < k, ∀ pw₁,
      lookup ((fun x => g₀ (h x))^[j] (g₀ y)) = some pw₁ →
        h ((fun x => g₀ (h x))^[τ - 1 - j] pw₁) ≠ y)
    (hhit : lookup ((fun x => g₀ (h x))^[k] (g₀ y)) = some pw₀)
    (hfa : h ((fun x => g₀ (h x))^[τ - 1 - k] pw₀) ≠ y) :
    τ + (τ - k) ≤ ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (hellmanAttack g₀ τ y)).map TableAttackSpec.hashCost).sum :=
  add_le_sum_map_hashCost_hellmanLoop_of_false_alarm hk hbefore hhit hfa

end HellmanRunCost

end Cslib.Crypto
