/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.EvalPure
public import CslibFrontier.Languages.Probabilistic.QueriesWith
public import CslibFrontier.Languages.Probabilistic.QueryCount
public import CslibFrontier.Languages.Probabilistic.Sum
import CslibFrontier.Languages.Probabilistic.QueryCount.Sum
import CslibFrontier.Languages.Probabilistic.Traverse.FindM
import CslibFrontier.Languages.Probabilistic.Traverse.SupportWith
import Mathlib.Data.List.Nodup

/-!
# Rainbow and Hellman tables for two-phase hash inversion

Two-phase table precomputation and online inversion of a hash function `h : P → Y` from
[BonehShoup2023], Section 18.7 (pp. 742–746; Fig. 18.13 on p. 744), modeled as oracle programs over
`h` and an endpoint lookup oracle.

Given column reduction functions `g : ℕ → Y → P` defining `f_j(pw) := g j (h pw)` on 0-indexed
columns `j = 0, ..., τ - 1` (corresponding to the book's `g_1, ..., g_τ`):

* `rainbowChainPure` and `rainbowChain` evaluate `len` consecutive columns starting at `start`,
  specializing when `g = fun _ => g₀` to Hellman's single-reduction iterate `(g₀ ∘ h)^[len]`
  (p. 743; Fig. 18.13a, p. 744).
* `rainbowPreprocess` (Algorithm `A₀`, pp. 743, 745) maps starting points `starts : List P` to
  endpoint-keyed pairs `(z_i, pw_i)` using at most `starts.length * τ` hash queries, so that
  `List.lookup` recovers every starting point `pw₀ ∈ starts` whose `τ`-step endpoint is shared by
  no earlier entry of `starts` (in particular whenever endpoints are distinct, matching `A₀`'s
  duplicate-endpoint discarding on p. 745).
* `rainbowAttack` (rainbow Algorithm `A₁`, p. 746; Fig. 18.13b, p. 744) runs over
  `TableAttackSpec P Y`—hash queries on the left (`TableAttackSpec.hashCost`) and table lookups on
  the right (`TableAttackSpec.lookupCost`)—searching steps `k = 0, ..., τ - 1` (columns `τ - 1`
  down to `0`, corresponding to `for i = τ downto 1`) with `List.findSomeM?`, reconstructing a
  candidate preimage on each table hit and verifying `h(pw) = y` before returning `some pw`.
* `hellmanAttack` (Hellman's Algorithm `A₁` and Fig. 18.13a, p. 744) initializes `z ← g₀(y)` and
  advances `z ← g₀(h(z))` step-by-step across `τ` iterations, reconstructing `(g₀ ∘ h)^[τ - i](pw₀)`
  and verifying `h(pw) = y` on each hit.

Deterministic per-run request-trace counts (`OracleComp.queriesWith`) for both `rainbowAttack` and
`hellmanAttack` are proved in `CslibFrontier.Crypto.Computational.RainbowTable.RunCost`.

This formalization differs from the book's presentation as follows:

1. **0-indexed columns.** Reduction functions are indexed `0, ..., τ - 1` rather than `1, ..., τ`;
   loop step `k ∈ {0, ..., τ - 1}` tests column `col = τ - 1 - k` (`i = τ - k` in `for i = τ
   downto 1`).
2. **Explicit starting list.** Sampling `ℓ` random starting points `pw_1, ..., pw_ℓ ∈ P` is
   factored out into the parameter `starts : List P`.
3. **Endpoint-keyed table and abstract lookup oracle.** `rainbowPreprocess` stores `(z_i, pw_i)`
   rather than `(pw_i, z_i)` so that `List.lookup` implements table lookup directly, as in
   `Cslib.Crypto.dictionaryTable`. Online inversion accesses the table through the right-hand
   oracle `P → Option P` of `TableAttackSpec P Y`, separating hash evaluations
   (`TableAttackSpec.hashCost`) from table lookups (`TableAttackSpec.lookupCost`) without claiming
   constant machine time for `List.lookup`.
4. **Failure output.** Inversion returns `Option P` (`none` for "fail").
5. **Limitations.** Soundness and two-phase inversion on covered chains are proved pointwise for
   arbitrary `h` and `g`. Hellman's multiple-table remedy (`m` small independent tables with
   distinct reduction functions searched separately by `A₁`, p. 745), the book's heuristic
   success-probability approximations modeling `h` and `g_j` as random functions (pp. 743–746), and
   machine-level running-time bounds are not formalized here (#5752).

## Main definitions

* `Cslib.Crypto.rainbowChainPure`: pure evaluation of `len` columns starting at `start`.
* `Cslib.Crypto.rainbowChain`: oracle program evaluating `len` columns against `h : P → Y`.
* `Cslib.Crypto.rainbowPreprocess`: preprocessing algorithm `A₀` producing `(z_i, pw_i)` pairs.
* `Cslib.Crypto.TableAttackSpec`: summed oracle interface of hash queries and table lookups.
* `Cslib.Crypto.TableAttackSpec.hashCost`, `Cslib.Crypto.TableAttackSpec.lookupCost`: per-call
  weights counting hash evaluations and table lookups.
* `Cslib.Crypto.rainbowAttackStep`, `Cslib.Crypto.rainbowAttack`: online rainbow-table inversion
  algorithm `A₁` (p. 746).
* `Cslib.Crypto.hellmanLoop`, `Cslib.Crypto.hellmanAttack`: Hellman's stateful online inversion
  algorithm `A₁` (p. 744).

## Main results

* `Cslib.Crypto.rainbowChainPure_add`, `Cslib.Crypto.rainbowChainPure_const`: chain splitting and
  specialization of constant reduction functions `fun _ => g₀` to `(fun x => g₀ (h x))^[len]`.
* `Cslib.Crypto.evalPure_rainbowChain`, `Cslib.Crypto.isQueryBounded_rainbowChain`,
  `Cslib.Crypto.length_queriesWith_rainbowChain`: deterministic semantics and `len` query count of
  `rainbowChain`.
* `Cslib.Crypto.evalPure_rainbowPreprocess`, `Cslib.Crypto.isQueryBounded_rainbowPreprocess`,
  `Cslib.Crypto.lookup_evalPure_rainbowPreprocess`,
  `Cslib.Crypto.lookup_evalPure_rainbowPreprocess_eq_some_iff`,
  `Cslib.Crypto.lookup_evalPure_rainbowPreprocess_of_nodup`: output list, `starts.length * τ` query
  bound, and `List.lookup` characterization of `rainbowPreprocess`.
* `Cslib.Crypto.rainbowAttack_sound`, `Cslib.Crypto.hellmanAttack_sound`: every returned password
  satisfies `h pw = y` (false alarms are rejected).
* `Cslib.Crypto.exists_evalPure_rainbowAttack_of_lookup_eq_some`,
  `Cslib.Crypto.evalPure_rainbowAttack_of_injective`,
  `Cslib.Crypto.exists_evalPure_rainbowAttack_rainbowPreprocess`,
  `Cslib.Crypto.evalPure_rainbowAttack_rainbowPreprocess_of_injective`: completeness of
  `rainbowAttack` against an abstract lookup oracle and against `rainbowPreprocess`, with exact
  preimage recovery when `h` is injective.
* `Cslib.Crypto.exists_evalPure_hellmanAttack_of_lookup_eq_some`,
  `Cslib.Crypto.evalPure_hellmanAttack_of_injective`,
  `Cslib.Crypto.exists_evalPure_hellmanAttack_rainbowPreprocess`,
  `Cslib.Crypto.evalPure_hellmanAttack_rainbowPreprocess_of_injective`: completeness of
  `hellmanAttack` against an abstract lookup oracle and against `rainbowPreprocess`, with exact
  preimage recovery when `h` is injective.
* `Cslib.Crypto.isCostBounded_lookupCost_rainbowAttack`,
  `Cslib.Crypto.isCostBounded_hashCost_rainbowAttack`: pathwise budgets of `τ` lookups and `τ * τ`
  hash evaluations for `rainbowAttack`.
* `Cslib.Crypto.isCostBounded_lookupCost_hellmanAttack`,
  `Cslib.Crypto.isCostBounded_hashCost_hellmanAttack`: pathwise budgets of `τ` lookups and
  `τ * (τ + 3) / 2` hash evaluations for `hellmanAttack`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 18.7, pp. 742–746.
-/

public section

namespace Cslib.Crypto

open Cslib

variable {P Y : Type}

/-! ### Rainbow chains -/

/-- Pure evaluation of `len` columns of a rainbow chain starting at column `start` from `pw`
([BonehShoup2023], Section 18.7, Fig. 18.13b, p. 744; p. 745): column `j` applies
`f_j(x) = g j (h x)`. Columns are 0-indexed (`0, ..., τ - 1` for the book's `g_1, ..., g_τ`). -/
def rainbowChainPure (h : P → Y) (g : ℕ → Y → P) : ℕ → ℕ → P → P
  | _, 0, pw => pw
  | start, len + 1, pw => rainbowChainPure h g (start + 1) len (g start (h pw))

/-- Zero columns leave the password unchanged. -/
@[simp]
theorem rainbowChainPure_zero (h : P → Y) (g : ℕ → Y → P) (start : ℕ) (pw : P) :
    rainbowChainPure h g start 0 pw = pw := by
  rfl

/-- Applying `len + 1` columns from `start` applies column `start` then `len` columns from
`start + 1`. -/
@[simp]
theorem rainbowChainPure_succ (h : P → Y) (g : ℕ → Y → P) (start len : ℕ) (pw : P) :
    rainbowChainPure h g start (len + 1) pw =
      rainbowChainPure h g (start + 1) len (g start (h pw)) := by
  rfl

/-- Splitting a rainbow chain of length `m + n` into `m` columns from `start` followed by `n`
columns from `start + m`. -/
theorem rainbowChainPure_add (h : P → Y) (g : ℕ → Y → P) (start m n : ℕ) (pw : P) :
    rainbowChainPure h g start (m + n) pw =
      rainbowChainPure h g (start + m) n (rainbowChainPure h g start m pw) := by
  induction m generalizing start pw with
  | zero => simp only [Nat.zero_add, Nat.add_zero, rainbowChainPure_zero]
  | succ m ih =>
    rw [Nat.succ_add, rainbowChainPure_succ, ih, rainbowChainPure_succ, Nat.add_right_comm,
      Nat.add_assoc]

/-- With a single column-independent reduction `g₀`, `rainbowChainPure` is `(g₀ ∘ h)^[len]`
(Hellman's chain, [BonehShoup2023], Section 18.7, p. 743; Fig. 18.13a, p. 744). -/
@[simp]
theorem rainbowChainPure_const (h : P → Y) (g₀ : Y → P) (start len : ℕ) (pw : P) :
    rainbowChainPure h (fun _ => g₀) start len pw = (fun x => g₀ (h x))^[len] pw := by
  induction len generalizing start pw with
  | zero => rfl
  | succ len ih =>
    rw [rainbowChainPure_succ, ih, Function.iterate_succ_apply]

/-- Oracle evaluation of `len` columns of a rainbow chain starting at column `start` from `pw`,
querying `h : P → Y` once per column ([BonehShoup2023], Section 18.7, pp. 745–746). -/
def rainbowChain (g : ℕ → Y → P) : ℕ → ℕ → P → OracleComp (fun _ : P => Y) P
  | _, 0, pw => pure pw
  | start, len + 1, pw => do
    let y ← OracleComp.query (spec := fun _ : P => Y) pw
    rainbowChain g (start + 1) len (g start y)

/-- Against `h`, `rainbowChain` computes `rainbowChainPure h`. -/
@[simp]
theorem evalPure_rainbowChain (h : P → Y) (g : ℕ → Y → P) (start len : ℕ) (pw : P) :
    (rainbowChain g start len pw).evalPure h = rainbowChainPure h g start len pw := by
  induction len generalizing start pw with
  | zero => rfl
  | succ len ih =>
    simp only [rainbowChain, OracleComp.evalPure_bind, OracleComp.evalPure_query,
      rainbowChainPure_succ, ih]

/-- Evaluating `len` columns makes at most `len` hash queries on every path. -/
theorem isQueryBounded_rainbowChain (g : ℕ → Y → P) (start len : ℕ) (pw : P) :
    OracleComp.IsQueryBounded (rainbowChain g start len pw) len := by
  induction len generalizing start pw with
  | zero => exact .pure pw 0
  | succ len ih => exact .liftBind pw _ len fun y => ih (start + 1) (g start y)

/-- Along any deterministic run against `h`, `rainbowChain` makes `len` hash queries. -/
@[simp]
theorem length_queriesWith_rainbowChain (h : P → Y) (g : ℕ → Y → P) (start len : ℕ) (pw : P) :
    (OracleComp.queriesWith h (rainbowChain g start len pw)).length = len := by
  induction len generalizing start pw with
  | zero => rfl
  | succ len ih =>
    simp only [rainbowChain, OracleComp.queriesWith_query_bind, List.length_cons, ih]

/-! ### Preprocessing phase `A₀` -/

/-- **Preprocessing algorithm `A₀`** for a rainbow table of chain length `τ` from starting points
`starts` ([BonehShoup2023], Section 18.7, pp. 743, 745; Fig. 18.13, p. 744): computes the endpoint
`z_i = f_{τ-1}(⋯ f_0(pw_i) ⋯)` of each `pw_i` in `starts` and stores `(z_i, pw_i)` keyed by
endpoint for `List.lookup`. -/
def rainbowPreprocess (g : ℕ → Y → P) (τ : ℕ) (starts : List P) :
    OracleComp (fun _ : P => Y) (List (P × P)) :=
  starts.mapM fun pw₀ => (fun z => (z, pw₀)) <$> rainbowChain g 0 τ pw₀

/-- Against `h`, `rainbowPreprocess` pairs each starting point's `τ`-step endpoint with that
starting point. -/
theorem evalPure_rainbowPreprocess (h : P → Y) (g : ℕ → Y → P) (τ : ℕ) (starts : List P) :
    (rainbowPreprocess g τ starts).evalPure h =
      starts.map fun pw₀ => (rainbowChainPure h g 0 τ pw₀, pw₀) := by
  simp only [rainbowPreprocess, OracleComp.evalPure_mapM, OracleComp.evalPure_map,
    evalPure_rainbowChain]

/-- **Cost of `A₀`.** Preprocessing `starts.length` chains of length `τ` makes at most
`starts.length * τ` hash queries on every path ([BonehShoup2023], Section 18.7, pp. 743, 745). -/
theorem isQueryBounded_rainbowPreprocess (g : ℕ → Y → P) (τ : ℕ) (starts : List P) :
    OracleComp.IsQueryBounded (rainbowPreprocess (Y := Y) g τ starts) (starts.length * τ) :=
  OracleComp.IsCostBounded.mapM fun pw₀ _ =>
    (OracleComp.isCostBounded_map_iff _ _ _).mpr (isQueryBounded_rainbowChain g 0 τ pw₀)

/-- Looking an endpoint `z` up in the preprocessed table finds the first starting point in `starts`
whose `τ`-step chain ends at `z`. -/
theorem lookup_evalPure_rainbowPreprocess [DecidableEq P] (h : P → Y) (g : ℕ → Y → P)
    (τ : ℕ) (starts : List P) (z : P) :
    ((rainbowPreprocess g τ starts).evalPure h).lookup z =
      starts.find? fun pw₀ => rainbowChainPure h g 0 τ pw₀ == z := by
  rw [evalPure_rainbowPreprocess, List.lookup_eq_findSome?, List.findSome?_map,
    List.find?_eq_findSome?_guard]
  refine congrArg (List.findSome? · starts) (funext fun pw₀ => ?_)
  simp [Option.guard, @eq_comm _ z]

/-- **Endpoint lookup in `A₀`'s table.** `List.lookup z` on the preprocessed table returns
`some pw₀` if and only if `pw₀`'s `τ`-step chain ends at `z` and no earlier element of `starts`
has endpoint `z`. -/
theorem lookup_evalPure_rainbowPreprocess_eq_some_iff [DecidableEq P] {h : P → Y}
    {g : ℕ → Y → P} {τ : ℕ} {starts : List P} {z pw₀ : P} :
    ((rainbowPreprocess g τ starts).evalPure h).lookup z = some pw₀ ↔
      rainbowChainPure h g 0 τ pw₀ = z ∧
        ∃ before after, starts = before ++ pw₀ :: after ∧
          ∀ pw₁ ∈ before, rainbowChainPure h g 0 τ pw₁ ≠ z := by
  rw [lookup_evalPure_rainbowPreprocess, List.find?_eq_some_iff_append]
  simp only [beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne]

/-- When the `τ`-step endpoints of `starts` are distinct—as guaranteed when `A₀` discards chains
with duplicate endpoints ([BonehShoup2023], Section 18.7, p. 745)—every `pw₀ ∈ starts` is
recovered from its endpoint by `List.lookup`. -/
theorem lookup_evalPure_rainbowPreprocess_of_nodup [DecidableEq P] {h : P → Y}
    {g : ℕ → Y → P} {τ : ℕ} {starts : List P} {pw₀ : P} (hmem : pw₀ ∈ starts)
    (hnodup : (starts.map (rainbowChainPure h g 0 τ)).Nodup) :
    ((rainbowPreprocess g τ starts).evalPure h).lookup (rainbowChainPure h g 0 τ pw₀) =
      some pw₀ := by
  induction starts with
  | nil => cases hmem
  | cons pw₁ rest ih =>
    rw [List.map_cons, List.nodup_cons] at hnodup
    rw [evalPure_rainbowPreprocess, List.map_cons, List.lookup_cons]
    rcases List.mem_cons.mp hmem with rfl | hrest
    · simp only [beq_self_eq_true]
    · rw [beq_false_of_ne fun heq => hnodup.1 (List.mem_map.mpr ⟨pw₀, hrest, heq⟩),
        ← evalPure_rainbowPreprocess]
      exact ih hrest hnodup.2

/-! ### Online inversion interface -/

/-- Summed oracle interface for online table-assisted inversion ([BonehShoup2023], Section 18.7,
p. 742): hash evaluations `P → Y` on the left and endpoint-to-start table lookups `P → Option P` on
the right. -/
abbrev TableAttackSpec (P Y : Type) : OracleSpec (P ⊕ P) :=
  (fun _ : P => Y) ⊕ₒ (fun _ : P => Option P)

namespace TableAttackSpec

/-- Per-call cost charging `1` per hash query (left) and `0` per table lookup (right). -/
def hashCost {P : Type} : P ⊕ P → ℕ :=
  Sum.elim (fun _ => 1) (fun _ => 0)

/-- Per-call cost charging `0` per hash query (left) and `1` per table lookup (right). -/
def lookupCost {P : Type} : P ⊕ P → ℕ :=
  Sum.elim (fun _ => 0) (fun _ => 1)

/-- A left (hash) query has `hashCost` `1`. -/
@[simp]
theorem hashCost_inl (x : P) : hashCost (Sum.inl x) = 1 := by
  rfl

/-- A right (table lookup) query has `hashCost` `0`. -/
@[simp]
theorem hashCost_inr (x : P) : hashCost (Sum.inr x) = 0 := by
  rfl

/-- A left (hash) query has `lookupCost` `0`. -/
@[simp]
theorem lookupCost_inl (x : P) : lookupCost (Sum.inl x) = 0 := by
  rfl

/-- A right (table lookup) query has `lookupCost` `1`. -/
@[simp]
theorem lookupCost_inr (x : P) : lookupCost (Sum.inr x) = 1 := by
  rfl

end TableAttackSpec

/-! ### Online rainbow-table inversion `A₁` (p. 746) -/

/-- Step `k` (`0 ≤ k < τ`, testing column `col = τ - 1 - k`, i.e., loop index `i = τ - k` in
`for i = τ downto 1`) of online rainbow-table inversion `A₁` ([BonehShoup2023], Section 18.7,
p. 746): computes the candidate endpoint `z` from `g (τ - 1 - k) y` across `k` columns, looks `z`
up in the table, and on `some pw₀` reconstructs `pw` across `τ - 1 - k` columns and checks
`h(pw) = y`. -/
@[expose] def rainbowAttackStep [DecidableEq Y] (g : ℕ → Y → P) (τ : ℕ) (y : Y) (k : ℕ) :
    OracleComp (TableAttackSpec P Y) (Option P) := do
  let z ← OracleComp.liftLeft (rainbowChain g (τ - k) k (g (τ - 1 - k) y))
  match ← OracleComp.liftRight (OracleComp.query (spec := fun _ : P => Option P) z) with
  | none => pure none
  | some pw₀ =>
    let pw ← OracleComp.liftLeft (rainbowChain g 0 (τ - 1 - k) pw₀)
    let y' ← OracleComp.liftLeft (OracleComp.query (spec := fun _ : P => Y) pw)
    if y' = y then pure (some pw) else pure none

/-- **Online rainbow-table inversion algorithm `A₁`** ([BonehShoup2023], Section 18.7, p. 746):
searches steps `k = 0, ..., τ - 1` (`i = τ` down to `1`) in order and stops at the first verified
preimage of `y`. -/
@[expose] def rainbowAttack [DecidableEq Y] (g : ℕ → Y → P) (τ : ℕ) (y : Y) :
    OracleComp (TableAttackSpec P Y) (Option P) :=
  (List.range τ).findSomeM? (rainbowAttackStep g τ y)

section RainbowAttack

variable [DecidableEq Y]

/-- Deterministic evaluation of one step of `rainbowAttack`. -/
theorem evalPure_rainbowAttackStep (h : P → Y) (lookup : P → Option P) (g : ℕ → Y → P)
    (τ : ℕ) (y : Y) (k : ℕ) :
    (rainbowAttackStep g τ y k).evalPure (OracleComp.sumPure h lookup) =
      match lookup (rainbowChainPure h g (τ - k) k (g (τ - 1 - k) y)) with
      | none => none
      | some pw₀ =>
        let pw := rainbowChainPure h g 0 (τ - 1 - k) pw₀
        if h pw = y then some pw else none := by
  cases hlk : lookup (rainbowChainPure h g (τ - k) k (g (τ - 1 - k) y)) <;>
    simp [rainbowAttackStep, OracleComp.evalPure_bind, OracleComp.evalPure_liftLeft,
      evalPure_rainbowChain, OracleComp.evalPure_query, hlk, apply_ite]

/-- Deterministic evaluation of `rainbowAttack` against `h` and `lookup`. -/
theorem evalPure_rainbowAttack (h : P → Y) (lookup : P → Option P) (g : ℕ → Y → P)
    (τ : ℕ) (y : Y) :
    (rainbowAttack g τ y).evalPure (OracleComp.sumPure h lookup) =
      (List.range τ).findSome? fun k =>
        match lookup (rainbowChainPure h g (τ - k) k (g (τ - 1 - k) y)) with
        | none => none
        | some pw₀ =>
          let pw := rainbowChainPure h g 0 (τ - 1 - k) pw₀
          if h pw = y then some pw else none := by
  simp only [rainbowAttack, OracleComp.evalPure_findSomeM?, evalPure_rainbowAttackStep]

/-- **Soundness of rainbow-table inversion** ([BonehShoup2023], Section 18.7, line 5 of Algorithm
`A₁`, p. 746): every password output by `rainbowAttack` satisfies `h pw = y`; false alarms from
chain merges or reduction collisions are rejected. -/
theorem rainbowAttack_sound {h : P → Y} {lookup : P → Option P} {g : ℕ → Y → P} {τ : ℕ}
    {y : Y} {pw : P}
    (heval : (rainbowAttack g τ y).evalPure (OracleComp.sumPure h lookup) = some pw) :
    h pw = y := by
  obtain ⟨k, -, hk⟩ :=
    List.exists_of_findSome?_eq_some (evalPure_rainbowAttack h lookup g τ y ▸ heval)
  split at hk
  · cases hk
  · obtain ⟨hcheck, hpw⟩ := Option.ite_none_right_eq_some.mp hk
    exact Option.some.inj hpw ▸ hcheck

/-- **Completeness of rainbow-table inversion on covered points** ([BonehShoup2023], Section 18.7,
pp. 745–746): if `y` is the hash of the column-`col` value (`col < τ`) of a chain starting at `pw₀`
whose `τ`-step endpoint maps to `some pw₀` under `lookup`, then `rainbowAttack` outputs a valid
preimage of `y`. -/
theorem exists_evalPure_rainbowAttack_of_lookup_eq_some {h : P → Y} {lookup : P → Option P}
    {g : ℕ → Y → P} {τ col : ℕ} {pw₀ : P} {y : Y} (hcol : col < τ)
    (hy : h (rainbowChainPure h g 0 col pw₀) = y)
    (hlookup : lookup (rainbowChainPure h g 0 τ pw₀) = some pw₀) :
    ∃ pw', (rainbowAttack g τ y).evalPure (OracleComp.sumPure h lookup) = some pw' ∧
      h pw' = y := by
  cases heval : (rainbowAttack g τ y).evalPure (OracleComp.sumPure h lookup) with
  | some pw' => exact ⟨pw', rfl, rainbowAttack_sound heval⟩
  | none =>
    rw [evalPure_rainbowAttack, List.findSome?_eq_none_iff] at heval
    have hstep := heval (τ - 1 - col) (List.mem_range.mpr (by omega))
    have hsub₁ : τ - 1 - (τ - 1 - col) = col := by omega
    have hadd := rainbowChainPure_add h g 0 col (τ - 1 - col + 1) pw₀
    rw [Nat.zero_add, show col + (τ - 1 - col + 1) = τ by omega, rainbowChainPure_succ, hy] at hadd
    rw [show τ - (τ - 1 - col) = col + 1 by omega, hsub₁, ← hadd, hlookup] at hstep
    simp [hy] at hstep

/-- When `h` is injective, `rainbowAttack` recovers `pw` itself on any covered chain point. -/
theorem evalPure_rainbowAttack_of_injective {h : P → Y} {lookup : P → Option P} {g : ℕ → Y → P}
    {τ col : ℕ} {pw₀ pw : P} {y : Y} (hinj : Function.Injective h) (hcol : col < τ)
    (hpw : rainbowChainPure h g 0 col pw₀ = pw) (hy : h pw = y)
    (hlookup : lookup (rainbowChainPure h g 0 τ pw₀) = some pw₀) :
    (rainbowAttack g τ y).evalPure (OracleComp.sumPure h lookup) = some pw := by
  obtain ⟨pw', heval, hy'⟩ :=
    exists_evalPure_rainbowAttack_of_lookup_eq_some hcol (hpw ▸ hy) hlookup
  exact heval.trans (congrArg some (hinj (hy'.trans hy.symm)))

/-- **Two-phase completeness of `(rainbowPreprocess, rainbowAttack)`** ([BonehShoup2023],
Section 18.7, pp. 745–746): against the endpoint table built by `rainbowPreprocess g τ starts` when
the `τ`-step endpoints of `starts` are distinct, `rainbowAttack` inverts `y = h(pw)` for every
point `pw = rainbowChainPure h g 0 col pw₀` (`pw₀ ∈ starts`, `col < τ`). -/
theorem exists_evalPure_rainbowAttack_rainbowPreprocess [DecidableEq P] {h : P → Y}
    {g : ℕ → Y → P} {τ col : ℕ} {starts : List P} {pw₀ : P} {y : Y}
    (hmem : pw₀ ∈ starts) (hnodup : (starts.map (rainbowChainPure h g 0 τ)).Nodup)
    (hcol : col < τ) (hy : h (rainbowChainPure h g 0 col pw₀) = y) :
    ∃ pw', (rainbowAttack g τ y).evalPure
      (OracleComp.sumPure h (List.lookup · ((rainbowPreprocess g τ starts).evalPure h))) =
        some pw' ∧ h pw' = y :=
  exists_evalPure_rainbowAttack_of_lookup_eq_some hcol hy
    (lookup_evalPure_rainbowPreprocess_of_nodup hmem hnodup)

/-- When `h` is injective and `starts` has distinct `τ`-step endpoints, two-phase rainbow inversion
`(rainbowPreprocess, rainbowAttack)` recovers `pw` itself on every covered chain point. -/
theorem evalPure_rainbowAttack_rainbowPreprocess_of_injective [DecidableEq P] {h : P → Y}
    {g : ℕ → Y → P} {τ col : ℕ} {starts : List P} {pw₀ pw : P} {y : Y}
    (hinj : Function.Injective h) (hmem : pw₀ ∈ starts)
    (hnodup : (starts.map (rainbowChainPure h g 0 τ)).Nodup) (hcol : col < τ)
    (hpw : rainbowChainPure h g 0 col pw₀ = pw) (hy : h pw = y) :
    (rainbowAttack g τ y).evalPure
      (OracleComp.sumPure h (List.lookup · ((rainbowPreprocess g τ starts).evalPure h))) =
        some pw :=
  evalPure_rainbowAttack_of_injective hinj hcol hpw hy
    (lookup_evalPure_rainbowPreprocess_of_nodup hmem hnodup)

omit [DecidableEq Y] in
private theorem lookupCost_liftLeft {α : Type} (oa : OracleComp (fun _ : P => Y) α) :
    OracleComp.IsCostBounded TableAttackSpec.lookupCost
      (OracleComp.liftLeft (spec₂ := fun _ : P => Option P) oa) 0 :=
  OracleComp.IsCostBounded.liftLeft_of_cost_inl_eq_zero TableAttackSpec.lookupCost_inl oa

omit [DecidableEq Y] in
private theorem hashCost_query (x : P) :
    OracleComp.IsCostBounded TableAttackSpec.hashCost
      (OracleComp.liftLeft (spec₂ := fun _ : P => Option P)
        (OracleComp.query (spec := fun _ : P => Y) x)) 1 :=
  (OracleComp.IsCostBounded.query (cost := fun _ : P => 1) x).liftLeft
    fun q => (TableAttackSpec.hashCost_inl q).le

omit [DecidableEq Y] in
private theorem hashCost_chain (g : ℕ → Y → P) (s n : ℕ) (pw : P) :
    OracleComp.IsCostBounded TableAttackSpec.hashCost
      (OracleComp.liftLeft (spec₂ := fun _ : P => Option P) (rainbowChain g s n pw)) n :=
  (isQueryBounded_rainbowChain g s n pw).liftLeft fun q => (TableAttackSpec.hashCost_inl q).le

private theorem isCostBounded_lookupCost_rainbowAttackStep (g : ℕ → Y → P) (τ : ℕ) (y : Y)
    (k : ℕ) :
    OracleComp.IsCostBounded TableAttackSpec.lookupCost (rainbowAttackStep g τ y k) 1 := by
  unfold rainbowAttackStep
  change OracleComp.IsCostBounded _ _ (0 + (1 + 0))
  refine (lookupCost_liftLeft _).bind fun z =>
    (((OracleComp.IsCostBounded.query (cost := fun _ : P => 1) z).liftRight
      fun q => (TableAttackSpec.lookupCost_inr q).le).bind fun
      | none => .pure none 0
      | some _ => ?_)
  change OracleComp.IsCostBounded _ _ (0 + (0 + 0))
  refine (lookupCost_liftLeft _).bind fun _ => (lookupCost_liftLeft _).bind fun _ => ?_
  split_ifs <;> exact .pure _ 0

private theorem isCostBounded_hashCost_rainbowAttackStep (g : ℕ → Y → P) {τ : ℕ} (y : Y) {k : ℕ}
    (hk : k < τ) :
    OracleComp.IsCostBounded TableAttackSpec.hashCost (rainbowAttackStep g τ y k) τ := by
  refine (?_ : OracleComp.IsCostBounded TableAttackSpec.hashCost (rainbowAttackStep g τ y k)
    (k + (0 + ((τ - 1 - k) + (1 + 0))))).mono (by omega)
  unfold rainbowAttackStep
  refine (hashCost_chain g (τ - k) k _).bind fun z =>
    ((OracleComp.IsCostBounded.liftRight_of_cost_inr_eq_zero
      TableAttackSpec.hashCost_inr _).bind fun
      | none => .pure none _
      | some pw₀ => (hashCost_chain g 0 (τ - 1 - k) pw₀).bind fun pw =>
          (hashCost_query pw).bind fun _ => ?_)
  split_ifs <;> exact .pure _ 0

/-- **Pathwise lookup budget of rainbow `A₁`.** `rainbowAttack` makes at most `τ` table lookups on
every path ([BonehShoup2023], Section 18.7, p. 746). -/
theorem isCostBounded_lookupCost_rainbowAttack (g : ℕ → Y → P) (τ : ℕ) (y : Y) :
    OracleComp.IsCostBounded TableAttackSpec.lookupCost (rainbowAttack g τ y) τ := by
  simpa only [rainbowAttack, List.length_range, Nat.mul_one] using
    OracleComp.IsCostBounded.findSomeM? (xs := List.range τ) (n := 1)
      fun k _ => isCostBounded_lookupCost_rainbowAttackStep g τ y k

/-- **Pathwise hash budget of rainbow `A₁`.** Across arbitrary answers (even if every lookup hits
and fails verification), `rainbowAttack` makes at most `τ * τ` hash queries on every path. -/
theorem isCostBounded_hashCost_rainbowAttack (g : ℕ → Y → P) (τ : ℕ) (y : Y) :
    OracleComp.IsCostBounded TableAttackSpec.hashCost (rainbowAttack g τ y) (τ * τ) := by
  simpa only [rainbowAttack, List.length_range] using
    OracleComp.IsCostBounded.findSomeM? (xs := List.range τ) (n := τ)
      fun k hk => isCostBounded_hashCost_rainbowAttackStep g y (List.mem_range.mp hk)

end RainbowAttack

/-! ### Hellman's stateful online attack `A₁` (Fig. 18.13a, p. 744) -/

/-- Remaining `rem` iterations of Hellman's online search `A₁` ([BonehShoup2023], Section 18.7,
p. 744) from current chain element `z`: at `rem = m + 1` (corresponding to `τ - i = m`), looks `z`
up in the table, reconstructs `(g₀ ∘ h)^[m](pw₀)` and checks `h(pw) = y` on a hit, and otherwise
advances `z ← g₀(h(z))`. -/
@[expose] def hellmanLoop [DecidableEq Y] (g₀ : Y → P) (y : Y) :
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
@[expose] def hellmanAttack [DecidableEq Y] (g₀ : Y → P) (τ : ℕ) (y : Y) :
    OracleComp (TableAttackSpec P Y) (Option P) :=
  hellmanLoop g₀ y τ (g₀ y)

section HellmanAttack

variable [DecidableEq Y]

private theorem evalPure_hellmanLoop_succ (h : P → Y) (lookup : P → Option P) (g₀ : Y → P)
    (y : Y) (m : ℕ) (z : P) :
    (hellmanLoop g₀ y (m + 1) z).evalPure (OracleComp.sumPure h lookup) =
      match lookup z with
      | some pw₀ =>
        let pw := (fun x => g₀ (h x))^[m] pw₀
        if h pw = y then some pw
        else (hellmanLoop g₀ y m (g₀ (h z))).evalPure (OracleComp.sumPure h lookup)
      | none => (hellmanLoop g₀ y m (g₀ (h z))).evalPure (OracleComp.sumPure h lookup) := by
  cases hlk : lookup z <;> simp only [hellmanLoop, OracleComp.evalPure_bind,
    OracleComp.evalPure_liftRight, OracleComp.evalPure_liftLeft, OracleComp.evalPure_query,
    evalPure_rainbowChain, rainbowChainPure_const, hlk]
  split_ifs <;> simp [OracleComp.evalPure_bind, OracleComp.evalPure_query]

private theorem hellmanLoop_sound {h : P → Y} {lookup : P → Option P} {g₀ : Y → P} {y : Y}
    {rem : ℕ} {z pw : P}
    (heval : (hellmanLoop g₀ y rem z).evalPure (OracleComp.sumPure h lookup) = some pw) :
    h pw = y := by
  induction rem generalizing z with
  | zero => cases heval
  | succ m ih =>
    rw [evalPure_hellmanLoop_succ] at heval
    cases hlk : lookup z <;> simp only [hlk] at heval
    · exact ih heval
    · split_ifs at heval with hcheck
      exacts [Option.some.inj heval ▸ hcheck, ih heval]

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
    simp_all [evalPure_hellmanLoop_succ]
  | succ d ih =>
    obtain ⟨m, rfl⟩ : ∃ m, rem = m + 1 := ⟨rem - 1, by omega⟩
    have hrec := ih (rem := m) (by omega)
      (by rwa [show m - 1 - d = m + 1 - 1 - (d + 1) by omega]) hlookup
    rw [evalPure_hellmanLoop_succ]
    cases lookup z with
    | none => exact hrec
    | some _ =>
      dsimp only
      split_ifs with hcheck
      exacts [⟨_, rfl, hcheck⟩, hrec]

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
  have hend : (fun x => g₀ (h x))^[τ - 1 - col] (g₀ y) = (fun x => g₀ (h x))^[τ] pw₀ := by
    rw [← hy, ← Function.iterate_succ_apply (fun x => g₀ (h x)) (τ - 1 - col),
      ← Function.iterate_add_apply]
    exact congrArg ((fun x => g₀ (h x))^[·] pw₀) (by omega)
  exact exists_evalPure_hellmanLoop_of_lookup_eq_some (by omega)
    (by rwa [show τ - 1 - (τ - 1 - col) = col by omega]) (hend.symm ▸ hlookup)

/-- When `h` is injective, `hellmanAttack` recovers `pw` itself on any covered chain point. -/
theorem evalPure_hellmanAttack_of_injective {h : P → Y} {lookup : P → Option P} {g₀ : Y → P}
    {τ col : ℕ} {pw₀ pw : P} {y : Y} (hinj : Function.Injective h) (hcol : col < τ)
    (hpw : (fun x => g₀ (h x))^[col] pw₀ = pw) (hy : h pw = y)
    (hlookup : lookup ((fun x => g₀ (h x))^[τ] pw₀) = some pw₀) :
    (hellmanAttack g₀ τ y).evalPure (OracleComp.sumPure h lookup) = some pw := by
  obtain ⟨pw', heval, hy'⟩ :=
    exists_evalPure_hellmanAttack_of_lookup_eq_some hcol (hpw ▸ hy) hlookup
  exact heval.trans (congrArg some (hinj (hy'.trans hy.symm)))

/-- **Two-phase completeness of `(rainbowPreprocess (fun _ => g₀), hellmanAttack)`**
([BonehShoup2023], Section 18.7, pp. 743–744): against the endpoint table built by
`rainbowPreprocess (fun _ => g₀) τ starts` when the `τ`-step endpoints of `starts` are distinct,
`hellmanAttack` inverts `y = h(pw)` for every point `pw = (g₀ ∘ h)^[col](pw₀)` (`pw₀ ∈ starts`,
`col < τ`). -/
theorem exists_evalPure_hellmanAttack_rainbowPreprocess [DecidableEq P] {h : P → Y}
    {g₀ : Y → P} {τ col : ℕ} {starts : List P} {pw₀ : P} {y : Y}
    (hmem : pw₀ ∈ starts)
    (hnodup : (starts.map fun pw => (fun x => g₀ (h x))^[τ] pw).Nodup)
    (hcol : col < τ) (hy : h ((fun x => g₀ (h x))^[col] pw₀) = y) :
    ∃ pw', (hellmanAttack g₀ τ y).evalPure
      (OracleComp.sumPure h
        (List.lookup · ((rainbowPreprocess (fun _ => g₀) τ starts).evalPure h))) = some pw' ∧
      h pw' = y := by
  have hfn : rainbowChainPure h (fun _ => g₀) 0 τ = fun pw => (fun x => g₀ (h x))^[τ] pw :=
    funext (rainbowChainPure_const h g₀ 0 τ)
  refine exists_evalPure_hellmanAttack_of_lookup_eq_some hcol hy ?_
  simpa only [rainbowChainPure_const] using
    lookup_evalPure_rainbowPreprocess_of_nodup (g := fun _ => g₀) hmem (hfn.symm ▸ hnodup)

/-- When `h` is injective and `starts` has distinct `τ`-step endpoints, two-phase Hellman inversion
`(rainbowPreprocess (fun _ => g₀), hellmanAttack)` recovers `pw` itself on every covered chain
point. -/
theorem evalPure_hellmanAttack_rainbowPreprocess_of_injective [DecidableEq P] {h : P → Y}
    {g₀ : Y → P} {τ col : ℕ} {starts : List P} {pw₀ pw : P} {y : Y}
    (hinj : Function.Injective h) (hmem : pw₀ ∈ starts)
    (hnodup : (starts.map fun pw => (fun x => g₀ (h x))^[τ] pw).Nodup)
    (hcol : col < τ) (hpw : (fun x => g₀ (h x))^[col] pw₀ = pw) (hy : h pw = y) :
    (hellmanAttack g₀ τ y).evalPure
      (OracleComp.sumPure h
        (List.lookup · ((rainbowPreprocess (fun _ => g₀) τ starts).evalPure h))) = some pw := by
  obtain ⟨pw', heval, hy'⟩ :=
    exists_evalPure_hellmanAttack_rainbowPreprocess hmem hnodup hcol (hpw ▸ hy)
  exact heval.trans (congrArg some (hinj (hy'.trans hy.symm)))

private theorem isCostBounded_lookupCost_hellmanLoop (g₀ : Y → P) (y : Y) (rem : ℕ) (z : P) :
    OracleComp.IsCostBounded TableAttackSpec.lookupCost (hellmanLoop g₀ y rem z) rem := by
  induction rem generalizing z with
  | zero => exact .pure none 0
  | succ m ih =>
    refine (?_ : OracleComp.IsCostBounded TableAttackSpec.lookupCost (hellmanLoop g₀ y (m + 1) z)
      (1 + (0 + (0 + (0 + m))))).mono (by omega)
    conv_lhs => unfold hellmanLoop
    refine ((OracleComp.IsCostBounded.query (cost := fun _ : P => 1) z).liftRight
      fun q => (TableAttackSpec.lookupCost_inr q).le).bind fun
      | none => ((lookupCost_liftLeft _).bind fun yz => ih (g₀ yz)).mono (by omega)
      | some _ => (lookupCost_liftLeft _).bind fun _ => (lookupCost_liftLeft _).bind fun _ => ?_
    split_ifs
    exacts [.pure _ _, (lookupCost_liftLeft _).bind fun yz => ih (g₀ yz)]

/-- **Pathwise lookup budget of Hellman's `A₁`.** `hellmanAttack` makes at most `τ` table lookups
on every path ([BonehShoup2023], Section 18.7, p. 744). -/
theorem isCostBounded_lookupCost_hellmanAttack (g₀ : Y → P) (τ : ℕ) (y : Y) :
    OracleComp.IsCostBounded TableAttackSpec.lookupCost (hellmanAttack g₀ τ y) τ :=
  isCostBounded_lookupCost_hellmanLoop g₀ y τ (g₀ y)

private theorem isCostBounded_hashCost_hellmanLoop (g₀ : Y → P) (y : Y) (rem : ℕ) (z : P) :
    OracleComp.IsCostBounded TableAttackSpec.hashCost (hellmanLoop g₀ y rem z)
      (rem * (rem + 3) / 2) := by
  induction rem generalizing z with
  | zero => exact .pure none 0
  | succ m ih =>
    rw [show (m + 1) * (m + 1 + 3) = m * (m + 3) + (m + 2) * 2 by ring,
      Nat.add_mul_div_right _ _ Nat.two_pos]
    refine (?_ : OracleComp.IsCostBounded TableAttackSpec.hashCost (hellmanLoop g₀ y (m + 1) z)
      (0 + (m + (1 + (1 + m * (m + 3) / 2))))).mono (by omega)
    conv_lhs => unfold hellmanLoop
    refine (OracleComp.IsCostBounded.liftRight_of_cost_inr_eq_zero
      TableAttackSpec.hashCost_inr _).bind fun
      | none => ((hashCost_query z).bind fun yz => ih (g₀ yz)).mono (by omega)
      | some pw₀ => (hashCost_chain (fun _ => g₀) 0 m pw₀).bind fun pw =>
          (hashCost_query pw).bind fun _ => ?_
    split_ifs
    exacts [.pure _ _, (hashCost_query z).bind fun yz => ih (g₀ yz)]

/-- **Pathwise hash budget of Hellman's `A₁`.** Across arbitrary answers (even if every lookup hits
and fails verification, spending `m + 2` hash queries at remaining depth `m + 1`), `hellmanAttack`
makes at most `∑_{m < τ} (m + 2) = τ * (τ + 3) / 2` hash queries on every path. -/
theorem isCostBounded_hashCost_hellmanAttack (g₀ : Y → P) (τ : ℕ) (y : Y) :
    OracleComp.IsCostBounded TableAttackSpec.hashCost (hellmanAttack g₀ τ y)
      (τ * (τ + 3) / 2) :=
  isCostBounded_hashCost_hellmanLoop g₀ y τ (g₀ y)

end HellmanAttack

end Cslib.Crypto
