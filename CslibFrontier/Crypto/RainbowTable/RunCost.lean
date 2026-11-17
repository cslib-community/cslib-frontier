/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.RainbowTable
import CslibFrontier.Languages.Probabilistic.QueriesWith.Cost
import CslibFrontier.Languages.Probabilistic.QueryCount.Sum
import CslibFrontier.Languages.Probabilistic.Traverse.FindM
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Deterministic run-cost analysis of rainbow-table and Hellman inversion

Deterministic request-trace (`OracleComp.queriesWith`) cost bounds for `rainbowAttack` and
Hellman's single-reduction stateful online search `hellmanAttack` ([BonehShoup2023], Section 18.7,
pp. 743–746), consuming the four decomposition lemmas of
`CslibFrontier.Languages.Probabilistic.QueriesWith.Cost`.

## Correspondence with [BonehShoup2023], Section 18.7

* **Rainbow tables (p. 746, Fig. 18.13b).** Algorithm `A₁` loops `i = τ` down to `1` (step index
  `k = 0, ..., τ - 1` testing column `τ - 1 - k`).
  - Line 2 computes `z ← f_τ(⋯ f_{i+1}(g_i(y)) ⋯)` using `k` hash evaluations (`0 + 1 + ⋯ +
    (τ - 1) = τ * (τ - 1) / 2` across all `τ` steps when every lookup misses:
    `sum_map_hashCost_queriesWith_rainbowAttack_of_forall_lookup_eq_none`).
  - Line 3 makes `1` lookup in `L` per executed step, so at most `τ` lookups on any run
    (`sum_map_lookupCost_queriesWith_rainbowAttack_le`) and `τ` lookups whenever the search returns
    `none` (`sum_map_lookupCost_queriesWith_rainbowAttack_of_evalPure_eq_none`).
  - On a table hit at step `k < τ`, lines 4–5 spend `(τ - 1 - k) + 1 = τ - k` additional hash
    evaluations (`k + (τ - k) = τ` total for step `k`:
    `sum_map_hashCost_queriesWith_rainbowAttackStep`). Across any run with `hits` candidate
    endpoints present in `L`, total hash cost is at most `τ * (τ - 1) / 2 + hits * τ`
    (`sum_map_hashCost_queriesWith_rainbowAttack_le`). When no table hit along the run is a false
    alarm, the first hit terminates `findSomeM?`, giving at most `τ * (τ - 1) / 2 + τ =
    τ * (τ + 1) / 2` hash evaluations
    (`sum_map_hashCost_queriesWith_rainbowAttack_le_of_no_false_alarm`), matching p. 746's
    statement that `A₁` makes at most `τ` lookups and `τ(τ + 1)/2` evaluations in the worst case
    (before accounting for false alarms).
* **Hellman's basic tradeoff (pp. 744–745, Fig. 18.13a and Fig. 18.14).** `hellmanAttack` advances
  `z ← g₀(h(z))` by one step per iteration instead of recomputing from `y`:
  - Without false alarms, every run—whether inverted at step `k` (`k + (τ - 1 - k) + 1 = τ`) or
    missing on all `τ` lookups (`τ` single-step advances)—makes `τ` hash evaluations and at most
    `τ` lookups (`sum_map_hashCost_queriesWith_hellmanAttack_of_no_false_alarm`,
    `sum_map_lookupCost_queriesWith_hellmanAttack_le`), matching p. 744 ("`τ` evaluations of `f`
    and at most `τ` lookups in `L`").
  - A false alarm reached at iteration `k < τ` adds at least `τ - k` extra hash evaluations above
    `τ` (`add_le_sum_map_hashCost_queriesWith_hellmanAttack_of_false_alarm`).

## Main definitions

* `Cslib.Crypto.hellmanAttack`: Hellman's stateful online inversion algorithm `A₁` (Fig. 18.13a,
  p. 744).

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
* `Cslib.Crypto.hellmanAttack_sound`,
  `Cslib.Crypto.exists_evalPure_hellmanAttack_of_lookup_eq_some`,
  `Cslib.Crypto.evalPure_hellmanAttack_of_injective`: soundness and completeness of `hellmanAttack`.
* `Cslib.Crypto.isCostBounded_lookupCost_hellmanAttack`,
  `Cslib.Crypto.sum_map_lookupCost_queriesWith_hellmanAttack_le`: pathwise and run lookup bound
  `≤ τ` for `hellmanAttack`.
* `Cslib.Crypto.le_sum_map_hashCost_queriesWith_hellmanAttack`,
  `Cslib.Crypto.sum_map_hashCost_queriesWith_hellmanAttack_of_no_false_alarm`,
  `Cslib.Crypto.add_le_sum_map_hashCost_queriesWith_hellmanAttack_of_false_alarm`: lower bound `τ`,
  exact no-false-alarm count `= τ`, and `τ + (τ - k)` false-alarm lower bound for `hellmanAttack`.

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

private theorem sum_map_hashCost_queriesWith_liftLeft {α : Type} (h : P → Y)
    (lookup : P → Option P) (prog : OracleComp (fun _ : P => Y) α) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (OracleComp.liftLeft prog)).map hashCost).sum =
      (OracleComp.queriesWith h prog).length := by
  rw [OracleComp.queriesWith_liftLeft, List.map_map]
  have hconst : (hashCost ∘ @Sum.inl P P) = fun _ => 1 := funext hashCost_inl
  rw [hconst, List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_one]

private theorem sum_map_lookupCost_queriesWith_liftLeft {α : Type} (h : P → Y)
    (lookup : P → Option P) (prog : OracleComp (fun _ : P => Y) α) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (OracleComp.liftLeft prog)).map lookupCost).sum = 0 := by
  rw [OracleComp.queriesWith_liftLeft, List.map_map]
  have hconst : (lookupCost ∘ @Sum.inl P P) = fun _ => 0 := funext lookupCost_inl
  rw [hconst, List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_zero]

private theorem sum_flatMap {α : Type} (xs : List α) (f : α → List ℕ) :
    (xs.flatMap f).sum = (xs.map fun x => (f x).sum).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, ih]

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
      (rainbowAttackStep g τ y k)).map lookupCost).sum = 1 := by
  unfold rainbowAttackStep
  rw [OracleComp.queriesWith_bind, interpret_id_eq_evalPure, OracleComp.evalPure_liftLeft,
    evalPure_rainbowChain, List.map_append, List.sum_append,
    sum_map_lookupCost_queriesWith_liftLeft, Nat.zero_add, OracleComp.liftRight_query,
    OracleComp.queriesWith_query_bind, List.map_cons, List.sum_cons, OracleComp.sumPure_inr,
    lookupCost_inr]
  cases lookup (rainbowChainPure h g (τ - k) k (g (τ - 1 - k) y)) with
  | none => simp only [OracleComp.queriesWith_pure, List.map_nil, List.sum_nil, Nat.add_zero]
  | some pw₀ =>
    rw [OracleComp.queriesWith_bind, interpret_id_eq_evalPure, OracleComp.evalPure_liftLeft,
      evalPure_rainbowChain, List.map_append, List.sum_append,
      sum_map_lookupCost_queriesWith_liftLeft, Nat.zero_add, OracleComp.queriesWith_bind,
      interpret_id_eq_evalPure, OracleComp.evalPure_liftLeft, OracleComp.evalPure_query,
      List.map_append, List.sum_append, sum_map_lookupCost_queriesWith_liftLeft, Nat.zero_add]
    split_ifs <;>
      simp only [OracleComp.queriesWith_pure, List.map_nil, List.sum_nil, Nat.add_zero]

/-- At step `k < τ`, `rainbowAttackStep` makes `k` hash queries when `lookup` misses and `τ` hash
queries (`k` forward, `τ - 1 - k` backward from `pw₀`, `1` verification) when `lookup` hits. -/
theorem sum_map_hashCost_queriesWith_rainbowAttackStep (h : P → Y) (lookup : P → Option P)
    (g : ℕ → Y → P) {τ : ℕ} (y : Y) {k : ℕ} (hk : k < τ) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (rainbowAttackStep g τ y k)).map hashCost).sum =
      if (lookup (rainbowChainPure h g (τ - k) k (g (τ - 1 - k) y))).isSome then τ else k := by
  unfold rainbowAttackStep
  rw [OracleComp.queriesWith_bind, interpret_id_eq_evalPure, OracleComp.evalPure_liftLeft,
    evalPure_rainbowChain, List.map_append, List.sum_append,
    sum_map_hashCost_queriesWith_liftLeft, length_queriesWith_rainbowChain,
    OracleComp.liftRight_query, OracleComp.queriesWith_query_bind, List.map_cons, List.sum_cons,
    OracleComp.sumPure_inr, hashCost_inr, Nat.zero_add]
  cases lookup (rainbowChainPure h g (τ - k) k (g (τ - 1 - k) y)) with
  | none =>
    simp only [OracleComp.queriesWith_pure, List.map_nil, List.sum_nil, Nat.add_zero,
      Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  | some pw₀ =>
    rw [OracleComp.queriesWith_bind, interpret_id_eq_evalPure, OracleComp.evalPure_liftLeft,
      evalPure_rainbowChain, List.map_append, List.sum_append,
      sum_map_hashCost_queriesWith_liftLeft, length_queriesWith_rainbowChain,
      OracleComp.queriesWith_bind, interpret_id_eq_evalPure, OracleComp.evalPure_liftLeft,
      OracleComp.evalPure_query, List.map_append, List.sum_append,
      sum_map_hashCost_queriesWith_liftLeft, OracleComp.queriesWith_query, List.length_singleton]
    have hrest :
        ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
          (if h (rainbowChainPure h g 0 (τ - 1 - k) pw₀) = y then
            pure (some (rainbowChainPure h g 0 (τ - 1 - k) pw₀))
          else pure none)).map hashCost).sum = 0 := by
      split_ifs <;> simp only [OracleComp.queriesWith_pure, List.map_nil, List.sum_nil]
    rw [hrest]
    simp only [Option.isSome_some, ↓reduceIte]
    omega

/-- Along any deterministic run, `rainbowAttack` makes at most `τ` table lookups
([BonehShoup2023], Section 18.7, p. 746). -/
theorem sum_map_lookupCost_queriesWith_rainbowAttack_le (h : P → Y) (lookup : P → Option P)
    (g : ℕ → Y → P) (τ : ℕ) (y : Y) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (rainbowAttack g τ y)).map lookupCost).sum ≤ τ :=
  OracleComp.IsCostBounded.sum_map_queriesWith_le (OracleComp.sumPure h lookup)
    (isCostBounded_lookupCost_rainbowAttack g τ y)

/-- When `rainbowAttack` returns `none`, all `τ` steps execute and the run makes `τ` table
lookups. -/
theorem sum_map_lookupCost_queriesWith_rainbowAttack_of_evalPure_eq_none {h : P → Y}
    {lookup : P → Option P} {g : ℕ → Y → P} {τ : ℕ} {y : Y}
    (heval : (rainbowAttack g τ y).evalPure (OracleComp.sumPure h lookup) = none) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (rainbowAttack g τ y)).map lookupCost).sum = τ := by
  have hsteps : ∀ k ∈ List.range τ,
      (rainbowAttackStep g τ y k).evalPure (OracleComp.sumPure h lookup) = none := by
    rw [rainbowAttack, OracleComp.evalPure_findSomeM?, List.findSome?_eq_none_iff] at heval
    exact heval
  rw [rainbowAttack,
    OracleComp.queriesWith_findSomeM?_of_forall_eq_none _ _ hsteps, List.map_flatMap, sum_flatMap]
  simp only [sum_map_lookupCost_queriesWith_rainbowAttackStep, List.map_const', List.length_range,
    List.sum_replicate, smul_eq_mul, Nat.mul_one]

/-- **Exact miss-run hash count of `rainbowAttack`** ([BonehShoup2023], Section 18.7, line 2 of
Algorithm `A₁`, p. 746): when no candidate endpoint hits the table, `rainbowAttack` evaluates
`0 + 1 + ⋯ + (τ - 1) = τ * (τ - 1) / 2` hashes. -/
theorem sum_map_hashCost_queriesWith_rainbowAttack_of_forall_lookup_eq_none {h : P → Y}
    {lookup : P → Option P} {g : ℕ → Y → P} {τ : ℕ} {y : Y}
    (hmiss : ∀ k < τ, lookup (rainbowChainPure h g (τ - k) k (g (τ - 1 - k) y)) = none) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (rainbowAttack g τ y)).map hashCost).sum = τ * (τ - 1) / 2 := by
  have hsteps : ∀ k ∈ List.range τ,
      (rainbowAttackStep g τ y k).evalPure (OracleComp.sumPure h lookup) = none := by
    intro k hk
    rw [evalPure_rainbowAttackStep, hmiss k (List.mem_range.mp hk)]
  rw [rainbowAttack,
    OracleComp.queriesWith_findSomeM?_of_forall_eq_none _ _ hsteps, List.map_flatMap, sum_flatMap]
  have hmap : ((List.range τ).map fun k =>
      ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
        (rainbowAttackStep g τ y k)).map hashCost).sum) = (List.range τ).map id := by
    refine List.map_congr_left fun k hk => ?_
    rw [sum_map_hashCost_queriesWith_rainbowAttackStep h lookup g y (List.mem_range.mp hk),
      hmiss k (List.mem_range.mp hk)]
    rfl
  rw [hmap, List.map_id, sum_range_eq]

private theorem sum_map_hashCost_findSomeM?_le (h : P → Y) (lookup : P → Option P)
    (g : ℕ → Y → P) (τ : ℕ) (y : Y) (xs : List ℕ) (hxs : ∀ k ∈ xs, k < τ) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (xs.findSomeM? (rainbowAttackStep g τ y))).map hashCost).sum ≤
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
    have hks : ∀ k' ∈ ks, k' < τ := fun k' hk' => hxs k' (List.mem_cons_of_mem k hk')
    rw [OracleComp.queriesWith_findSomeM?_cons, List.map_append, List.sum_append,
      sum_map_hashCost_queriesWith_rainbowAttackStep h lookup g y hk, List.sum_cons,
      List.countP_cons]
    have htail :
        ((if ((rainbowAttackStep g τ y k).evalPure (OracleComp.sumPure h lookup)).isSome then []
          else OracleComp.queriesWith (OracleComp.sumPure h lookup)
            (ks.findSomeM? (rainbowAttackStep g τ y))).map hashCost).sum ≤
          ks.sum +
            (ks.countP fun k' =>
              (lookup (rainbowChainPure h g (τ - k') k' (g (τ - 1 - k') y))).isSome) * τ := by
      split_ifs
      · simp only [List.map_nil, List.sum_nil, Nat.zero_le]
      · exact ih hks
    cases lookup (rainbowChainPure h g (τ - k) k (g (τ - 1 - k) y)) with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      omega
    | some pw₀ =>
      simp only [Option.isSome_some, ↓reduceIte, Nat.add_mul, Nat.one_mul]
      omega

/-- **General run hash bound of `rainbowAttack`.** Along any deterministic run (including early
termination when a preimage is found), total hash evaluations are at most
`τ * (τ - 1) / 2 + hits * τ`, where `hits` counts steps `k < τ` whose candidate endpoint hits
`lookup`. -/
theorem sum_map_hashCost_queriesWith_rainbowAttack_le (h : P → Y) (lookup : P → Option P)
    (g : ℕ → Y → P) (τ : ℕ) (y : Y) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (rainbowAttack g τ y)).map hashCost).sum ≤
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
      (xs.findSomeM? (rainbowAttackStep g τ y))).map hashCost).sum ≤ xs.sum + τ := by
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
      have heval :
          (rainbowAttackStep g τ y k).evalPure (OracleComp.sumPure h lookup) = none := by
        rw [evalPure_rainbowAttackStep, hlk]
      rw [heval]
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      have htail := ih (fun k' hk' => hxs k' (List.mem_cons_of_mem k hk'))
        fun k' hk' => hnofa k' (List.mem_cons_of_mem k hk')
      omega
    | some pw₀ =>
      have hgood : h (rainbowChainPure h g 0 (τ - 1 - k) pw₀) = y :=
        hnofa k List.mem_cons_self pw₀ hlk
      have heval :
          (rainbowAttackStep g τ y k).evalPure (OracleComp.sumPure h lookup) =
            some (rainbowChainPure h g 0 (τ - 1 - k) pw₀) := by
        rw [evalPure_rainbowAttackStep, hlk]
        simp only [hgood, ↓reduceIte]
      rw [heval]
      simp only [Option.isSome_some, ↓reduceIte, List.map_nil, List.sum_nil, Nat.add_zero]
      omega

/-- **Worst-case rainbow-table hash bound without false alarms** ([BonehShoup2023], Section 18.7,
p. 746): when every table hit along the candidate endpoints yields a valid preimage of `y`, the
first hit terminates `rainbowAttack`, so the run makes at most `τ * (τ + 1) / 2` hash evaluations
(`τ * (τ - 1) / 2` from line 2 across `i = τ` down to `1`, plus at most `τ` from reconstructing and
verifying the first hit). -/
theorem sum_map_hashCost_queriesWith_rainbowAttack_le_of_no_false_alarm {h : P → Y}
    {lookup : P → Option P} {g : ℕ → Y → P} {τ : ℕ} {y : Y}
    (hnofa : ∀ k < τ, ∀ pw₀,
      lookup (rainbowChainPure h g (τ - k) k (g (τ - 1 - k) y)) = some pw₀ →
        h (rainbowChainPure h g 0 (τ - 1 - k) pw₀) = y) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (rainbowAttack g τ y)).map hashCost).sum ≤ τ * (τ + 1) / 2 := by
  have hle := sum_map_hashCost_findSomeM?_le_of_no_false_alarm (List.range τ)
    (fun k hk => List.mem_range.mp hk) fun k hk => hnofa k (List.mem_range.mp hk)
  rwa [sum_range_eq, range_sum_add_self] at hle

end RainbowRunCost

/-! ### Hellman's stateful online attack (Fig. 18.13a, p. 744) -/

private def hellmanLoop [DecidableEq Y] (g₀ : Y → P) (y : Y) :
    ℕ → P → OracleComp (TableAttackSpec P Y) (Option P)
  | 0, _ => pure none
  | m + 1, z => do
    match ← OracleComp.liftRight (OracleComp.query (spec := fun _ : P => Option P) z) with
    | some pw₀ =>
      let pw ← OracleComp.liftLeft (rainbowChain (fun _ => g₀) 0 m pw₀)
      let y' ← OracleComp.liftLeft (OracleComp.query (spec := fun _ : P => Y) pw)
      if y' = y then
        pure (some pw)
      else
        let yz ← OracleComp.liftLeft (OracleComp.query (spec := fun _ : P => Y) z)
        hellmanLoop g₀ y m (g₀ yz)
    | none =>
      let yz ← OracleComp.liftLeft (OracleComp.query (spec := fun _ : P => Y) z)
      hellmanLoop g₀ y m (g₀ yz)

/-- **Hellman's online inversion algorithm `A₁`** ([BonehShoup2023], Section 18.7, Fig. 18.13a,
p. 744): initializes `z ← g₀(y)` and iterates `τ` times, looking `z` up in `L`, reconstructing
`pw ← (g₀ ∘ h)^[τ - i](pw₀)` and checking `h(pw) = y` on a hit, and advancing `z ← g₀(h(z))`
step-by-step between iterations. -/
def hellmanAttack [DecidableEq Y] (g₀ : Y → P) (τ : ℕ) (y : Y) :
    OracleComp (TableAttackSpec P Y) (Option P) :=
  hellmanLoop g₀ y τ (g₀ y)

section Hellman

variable [DecidableEq Y]

private theorem hellmanLoop_sound {h : P → Y} {lookup : P → Option P} {g₀ : Y → P} {y : Y}
    {rem : ℕ} {z pw : P}
    (heval : (hellmanLoop g₀ y rem z).evalPure (OracleComp.sumPure h lookup) = some pw) :
    h pw = y := by
  induction rem generalizing z with
  | zero => cases heval
  | succ m ih =>
    simp only [hellmanLoop, OracleComp.evalPure_bind, OracleComp.evalPure_liftRight,
      OracleComp.evalPure_query] at heval
    cases hlk : lookup z with
    | none =>
      rw [hlk] at heval
      simp only [OracleComp.evalPure_bind, OracleComp.evalPure_liftLeft,
        OracleComp.evalPure_query] at heval
      exact ih heval
    | some pw₀ =>
      rw [hlk] at heval
      simp only [OracleComp.evalPure_bind, OracleComp.evalPure_liftLeft, evalPure_rainbowChain,
        rainbowChainPure_const, OracleComp.evalPure_query] at heval
      split_ifs at heval with hcheck
      · simp only [OracleComp.evalPure_pure, Option.some.injEq] at heval
        exact heval ▸ hcheck
      · simp only [OracleComp.evalPure_bind, OracleComp.evalPure_liftLeft,
          OracleComp.evalPure_query] at heval
        exact ih heval

/-- **Soundness of Hellman's inversion** ([BonehShoup2023], Section 18.7, line 5 of Algorithm `A₁`,
p. 744): every password output by `hellmanAttack` satisfies `h pw = y`. -/
theorem hellmanAttack_sound {h : P → Y} {lookup : P → Option P} {g₀ : Y → P} {τ : ℕ}
    {y : Y} {pw : P}
    (heval : (hellmanAttack g₀ τ y).evalPure (OracleComp.sumPure h lookup) = some pw) :
    h pw = y :=
  hellmanLoop_sound heval

private theorem exists_evalPure_hellmanLoop_of_lookup_eq_some {h : P → Y} {lookup : P → Option P}
    {g₀ : Y → P} {y : Y} {d rem : ℕ} {z pw₀ : P} (hd : d < rem)
    (hy : h ((fun x => g₀ (h x))^[rem - 1 - d] pw₀) = y)
    (hlookup : lookup ((fun x => g₀ (h x))^[d] z) = some pw₀) :
    ∃ pw', (hellmanLoop g₀ y rem z).evalPure (OracleComp.sumPure h lookup) = some pw' ∧
      h pw' = y := by
  induction d generalizing rem z with
  | zero =>
    obtain ⟨m, rfl⟩ : ∃ m, rem = m + 1 := ⟨rem - 1, by omega⟩
    simp only [Function.iterate_zero_apply] at hlookup
    simp only [Nat.add_sub_cancel, Nat.sub_zero] at hy
    refine ⟨(fun x => g₀ (h x))^[m] pw₀, ?_, hy⟩
    simp only [hellmanLoop, OracleComp.evalPure_bind, OracleComp.evalPure_liftRight,
      OracleComp.evalPure_query, hlookup, OracleComp.evalPure_liftLeft, evalPure_rainbowChain,
      rainbowChainPure_const, hy, ↓reduceIte, OracleComp.evalPure_pure]
  | succ d ih =>
    obtain ⟨m, rfl⟩ : ∃ m, rem = m + 1 := ⟨rem - 1, by omega⟩
    have hdm : d < m := by omega
    have hy' : h ((fun x => g₀ (h x))^[m - 1 - d] pw₀) = y := by
      have hidx : m + 1 - 1 - (d + 1) = m - 1 - d := by omega
      rwa [hidx] at hy
    rw [Function.iterate_succ_apply] at hlookup
    simp only [hellmanLoop, OracleComp.evalPure_bind, OracleComp.evalPure_liftRight,
      OracleComp.evalPure_query]
    cases lookup z with
    | none =>
      simp only [OracleComp.evalPure_bind, OracleComp.evalPure_liftLeft, OracleComp.evalPure_query]
      exact ih hdm hy' hlookup
    | some pw₁ =>
      simp only [OracleComp.evalPure_bind, OracleComp.evalPure_liftLeft, evalPure_rainbowChain,
        rainbowChainPure_const, OracleComp.evalPure_query]
      split_ifs with hcheck
      · exact ⟨(fun x => g₀ (h x))^[m] pw₁, rfl, hcheck⟩
      · simp only [OracleComp.evalPure_bind, OracleComp.evalPure_liftLeft,
          OracleComp.evalPure_query]
        exact ih hdm hy' hlookup

/-- **Completeness of Hellman's inversion on covered points** ([BonehShoup2023], Section 18.7,
pp. 743–744): if `y = h(pw)` for a point `pw = (g₀ ∘ h)^[col](pw₀)` at column `col < τ` whose
`τ`-step endpoint maps to `some pw₀` under `lookup`, then `hellmanAttack` outputs a valid preimage
of `y`. -/
theorem exists_evalPure_hellmanAttack_of_lookup_eq_some {h : P → Y} {lookup : P → Option P}
    {g₀ : Y → P} {τ col : ℕ} {pw₀ : P} {y : Y} (hcol : col < τ)
    (hy : h ((fun x => g₀ (h x))^[col] pw₀) = y)
    (hlookup : lookup ((fun x => g₀ (h x))^[τ] pw₀) = some pw₀) :
    ∃ pw', (hellmanAttack g₀ τ y).evalPure (OracleComp.sumPure h lookup) = some pw' ∧
      h pw' = y := by
  have hd : τ - 1 - col < τ := by omega
  have hsub : τ - 1 - (τ - 1 - col) = col := by omega
  have hend : (fun x => g₀ (h x))^[τ - 1 - col] (g₀ y) = (fun x => g₀ (h x))^[τ] pw₀ := by
    rw [← hy, ← Function.iterate_succ_apply (fun x => g₀ (h x)) (τ - 1 - col),
      ← Function.iterate_add_apply]
    congr 1
    omega
  exact exists_evalPure_hellmanLoop_of_lookup_eq_some hd (hsub.symm ▸ hy) (hend.symm ▸ hlookup)

/-- When `h` is injective, `hellmanAttack` recovers `pw` itself on any covered chain point. -/
theorem evalPure_hellmanAttack_of_injective {h : P → Y} {lookup : P → Option P} {g₀ : Y → P}
    {τ col : ℕ} {pw₀ pw : P} {y : Y} (hinj : Function.Injective h) (hcol : col < τ)
    (hpw : (fun x => g₀ (h x))^[col] pw₀ = pw) (hy : h pw = y)
    (hlookup : lookup ((fun x => g₀ (h x))^[τ] pw₀) = some pw₀) :
    (hellmanAttack g₀ τ y).evalPure (OracleComp.sumPure h lookup) = some pw := by
  obtain ⟨pw', heval, hy'⟩ :=
    exists_evalPure_hellmanAttack_of_lookup_eq_some hcol (hpw ▸ hy) hlookup
  exact heval.trans (congrArg some (hinj (hy'.trans hy.symm)))

private theorem isCostBounded_lookupCost_hellmanLoop (g₀ : Y → P) (y : Y) (rem : ℕ) (z : P) :
    OracleComp.IsCostBounded lookupCost (hellmanLoop g₀ y rem z) rem := by
  induction rem generalizing z with
  | zero => exact .pure none 0
  | succ m ih =>
    refine (?_ : OracleComp.IsCostBounded lookupCost (hellmanLoop g₀ y (m + 1) z)
      (1 + (0 + (0 + (0 + m))))).mono (by omega)
    conv_lhs => unfold hellmanLoop
    refine ((OracleComp.IsCostBounded.query (cost := fun _ : P => 1) z).liftRight
      fun q => (lookupCost_inr q).le).bind fun hit => ?_
    cases hit with
    | none =>
      exact ((OracleComp.IsCostBounded.liftLeft_of_cost_inl_eq_zero lookupCost_inl _).bind
        fun yz => ih (g₀ yz)).mono (by omega)
    | some pw₀ =>
      refine (OracleComp.IsCostBounded.liftLeft_of_cost_inl_eq_zero lookupCost_inl _).bind
        fun pw => ?_
      refine (OracleComp.IsCostBounded.liftLeft_of_cost_inl_eq_zero lookupCost_inl _).bind
        fun y' => ?_
      split_ifs
      · exact .pure _ _
      · exact (OracleComp.IsCostBounded.liftLeft_of_cost_inl_eq_zero lookupCost_inl _).bind
          fun yz => ih (g₀ yz)

/-- **Pathwise lookup budget of Hellman's `A₁`.** `hellmanAttack` makes at most `τ` table lookups
on every path ([BonehShoup2023], Section 18.7, p. 744). -/
theorem isCostBounded_lookupCost_hellmanAttack (g₀ : Y → P) (τ : ℕ) (y : Y) :
    OracleComp.IsCostBounded lookupCost (hellmanAttack g₀ τ y) τ :=
  isCostBounded_lookupCost_hellmanLoop g₀ y τ (g₀ y)

/-- Along any deterministic run, `hellmanAttack` makes at most `τ` table lookups
([BonehShoup2023], Section 18.7, p. 744). -/
theorem sum_map_lookupCost_queriesWith_hellmanAttack_le (h : P → Y) (lookup : P → Option P)
    (g₀ : Y → P) (τ : ℕ) (y : Y) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (hellmanAttack g₀ τ y)).map lookupCost).sum ≤ τ :=
  OracleComp.IsCostBounded.sum_map_queriesWith_le (OracleComp.sumPure h lookup)
    (isCostBounded_lookupCost_hellmanAttack g₀ τ y)

private theorem sum_map_hashCost_hellmanLoop_step (h : P → Y) (lookup : P → Option P)
    (g₀ : Y → P) (y : Y) (m : ℕ) (z : P) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (hellmanLoop g₀ y (m + 1) z)).map hashCost).sum =
      match lookup z with
      | none =>
        1 + ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
          (hellmanLoop g₀ y m (g₀ (h z)))).map hashCost).sum
      | some pw₀ =>
        if h ((fun x => g₀ (h x))^[m] pw₀) = y then
          m + 1
        else
          m + 2 + ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
            (hellmanLoop g₀ y m (g₀ (h z)))).map hashCost).sum := by
  conv_lhs => unfold hellmanLoop
  rw [OracleComp.liftRight_query, OracleComp.queriesWith_query_bind, List.map_cons, List.sum_cons,
    OracleComp.sumPure_inr, hashCost_inr, Nat.zero_add]
  cases lookup z with
  | none =>
    simp only
    rw [OracleComp.queriesWith_bind, interpret_id_eq_evalPure, OracleComp.evalPure_liftLeft,
      OracleComp.evalPure_query, List.map_append, List.sum_append,
      sum_map_hashCost_queriesWith_liftLeft, OracleComp.queriesWith_query, List.length_singleton]
  | some pw₀ =>
    simp only
    rw [OracleComp.queriesWith_bind, interpret_id_eq_evalPure, OracleComp.evalPure_liftLeft,
      evalPure_rainbowChain, rainbowChainPure_const, List.map_append, List.sum_append,
      sum_map_hashCost_queriesWith_liftLeft, length_queriesWith_rainbowChain,
      OracleComp.queriesWith_bind, interpret_id_eq_evalPure, OracleComp.evalPure_liftLeft,
      OracleComp.evalPure_query, List.map_append, List.sum_append,
      sum_map_hashCost_queriesWith_liftLeft, OracleComp.queriesWith_query, List.length_singleton]
    split_ifs with hcheck
    · simp only [OracleComp.queriesWith_pure, List.map_nil, List.sum_nil, Nat.add_zero]
    · rw [OracleComp.queriesWith_bind, interpret_id_eq_evalPure, OracleComp.evalPure_liftLeft,
        OracleComp.evalPure_query, List.map_append, List.sum_append,
        sum_map_hashCost_queriesWith_liftLeft, OracleComp.queriesWith_query, List.length_singleton]
      omega

private theorem le_sum_map_hashCost_hellmanLoop (h : P → Y) (lookup : P → Option P)
    (g₀ : Y → P) (y : Y) (rem : ℕ) (z : P) :
    rem ≤ ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (hellmanLoop g₀ y rem z)).map hashCost).sum := by
  induction rem generalizing z with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    rw [sum_map_hashCost_hellmanLoop_step]
    have hrec := ih (g₀ (h z))
    cases lookup z with
    | none => simp only; omega
    | some pw₀ => simp only; split_ifs <;> omega

/-- Every deterministic run of `hellmanAttack` makes at least `τ` hash evaluations. -/
theorem le_sum_map_hashCost_queriesWith_hellmanAttack (h : P → Y) (lookup : P → Option P)
    (g₀ : Y → P) (τ : ℕ) (y : Y) :
    τ ≤ ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (hellmanAttack g₀ τ y)).map hashCost).sum :=
  le_sum_map_hashCost_hellmanLoop h lookup g₀ y τ (g₀ y)

private theorem sum_map_hashCost_hellmanLoop_of_no_false_alarm {h : P → Y}
    {lookup : P → Option P} {g₀ : Y → P} {y : Y} (rem : ℕ) (z : P)
    (hnofa : ∀ k < rem, ∀ pw₀,
      lookup ((fun x => g₀ (h x))^[k] z) = some pw₀ →
        h ((fun x => g₀ (h x))^[rem - 1 - k] pw₀) = y) :
    ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (hellmanLoop g₀ y rem z)).map hashCost).sum = rem := by
  induction rem generalizing z with
  | zero => rfl
  | succ m ih =>
    rw [sum_map_hashCost_hellmanLoop_step]
    cases hlk : lookup z with
    | none =>
      simp only
      have hrec := ih (g₀ (h z)) fun k hk pw₀ hlk' => by
        have hk' : k + 1 < m + 1 := by omega
        rw [← Function.iterate_succ_apply (fun x => g₀ (h x)) k z] at hlk'
        have hidx : m + 1 - 1 - (k + 1) = m - 1 - k := by omega
        exact hidx ▸ hnofa (k + 1) hk' pw₀ hlk'
      omega
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
      (hellmanAttack g₀ τ y)).map hashCost).sum = τ :=
  sum_map_hashCost_hellmanLoop_of_no_false_alarm τ (g₀ y) hnofa

private theorem add_le_sum_map_hashCost_hellmanLoop_of_false_alarm {h : P → Y}
    {lookup : P → Option P} {g₀ : Y → P} {y : Y} {k rem : ℕ} {z pw₀ : P} (hk : k < rem)
    (hbefore : ∀ j < k, ∀ pw₁,
      lookup ((fun x => g₀ (h x))^[j] z) = some pw₁ →
        h ((fun x => g₀ (h x))^[rem - 1 - j] pw₁) ≠ y)
    (hhit : lookup ((fun x => g₀ (h x))^[k] z) = some pw₀)
    (hfa : h ((fun x => g₀ (h x))^[rem - 1 - k] pw₀) ≠ y) :
    rem + (rem - k) ≤ ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (hellmanLoop g₀ y rem z)).map hashCost).sum := by
  induction k generalizing rem z with
  | zero =>
    obtain ⟨m, rfl⟩ : ∃ m, rem = m + 1 := ⟨rem - 1, by omega⟩
    simp only [Function.iterate_zero_apply] at hhit
    simp only [Nat.add_sub_cancel, Nat.sub_zero] at hfa
    rw [sum_map_hashCost_hellmanLoop_step, hhit]
    simp only [hfa, ↓reduceIte]
    have hrec := le_sum_map_hashCost_hellmanLoop h lookup g₀ y m (g₀ (h z))
    omega
  | succ k ih =>
    obtain ⟨m, rfl⟩ : ∃ m, rem = m + 1 := ⟨rem - 1, by omega⟩
    have hkm : k < m := by omega
    rw [Function.iterate_succ_apply] at hhit
    have hfa' : h ((fun x => g₀ (h x))^[m - 1 - k] pw₀) ≠ y := by
      have hidx : m + 1 - 1 - (k + 1) = m - 1 - k := by omega
      rwa [hidx] at hfa
    have hbefore' : ∀ j < k, ∀ pw₁,
        lookup ((fun x => g₀ (h x))^[j] (g₀ (h z))) = some pw₁ →
          h ((fun x => g₀ (h x))^[m - 1 - j] pw₁) ≠ y := by
      intro j hj pw₁ hlk'
      rw [← Function.iterate_succ_apply (fun x => g₀ (h x)) j z] at hlk'
      have hidx : m + 1 - 1 - (j + 1) = m - 1 - j := by omega
      exact hidx ▸ hbefore (j + 1) (by omega) pw₁ hlk'
    have hrec := ih hkm hbefore' hhit hfa'
    rw [sum_map_hashCost_hellmanLoop_step]
    cases hlk : lookup z with
    | none => simp only; omega
    | some pw₁ =>
      have hne₀ : h ((fun x => g₀ (h x))^[m] pw₁) ≠ y := by
        simpa only [Nat.add_sub_cancel, Nat.sub_zero] using
          hbefore 0 (Nat.zero_lt_succ k) pw₁ hlk
      simp only [hne₀, ↓reduceIte]
      omega

/-- **Extra hash cost of a false alarm in Hellman's attack** ([BonehShoup2023], Section 18.7,
Fig. 18.14, pp. 744–745): a false alarm reached at iteration `k < τ` (with no true hit at any
earlier iteration `j < k`) adds at least `τ - k` hash evaluations above `τ`. -/
theorem add_le_sum_map_hashCost_queriesWith_hellmanAttack_of_false_alarm {h : P → Y}
    {lookup : P → Option P} {g₀ : Y → P} {τ k : ℕ} {y : Y} {pw₀ : P} (hk : k < τ)
    (hbefore : ∀ j < k, ∀ pw₁,
      lookup ((fun x => g₀ (h x))^[j] (g₀ y)) = some pw₁ →
        h ((fun x => g₀ (h x))^[τ - 1 - j] pw₁) ≠ y)
    (hhit : lookup ((fun x => g₀ (h x))^[k] (g₀ y)) = some pw₀)
    (hfa : h ((fun x => g₀ (h x))^[τ - 1 - k] pw₀) ≠ y) :
    τ + (τ - k) ≤ ((OracleComp.queriesWith (OracleComp.sumPure h lookup)
      (hellmanAttack g₀ τ y)).map hashCost).sum :=
  add_le_sum_map_hashCost_hellmanLoop_of_false_alarm hk hbefore hhit hfa

end Hellman

end Cslib.Crypto
