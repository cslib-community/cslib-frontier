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

/-!
# Rainbow tables for two-phase hash inversion

Two-phase rainbow-table precomputation and online inversion of a hash function `h : P → Y` from
[BonehShoup2023], Section 18.7 (pp. 742–746, Fig. 18.13b), modeled as oracle programs over `h` and
an endpoint lookup oracle.

Given column reduction functions `g : ℕ → Y → P` defining `f_j(pw) := g j (h pw)` on 0-indexed
columns `j = 0, ..., τ - 1` (corresponding to the book's `g_1, ..., g_τ`):

* `rainbowChainPure` and `rainbowChain` evaluate `len` consecutive columns starting at `start`.
* `rainbowPreprocess` (Algorithm `A₀`, pp. 743, 745–746) maps starting points `starts : List P` to
  endpoint-keyed pairs `(z_i, pw_i)` using `starts.length * τ` hash queries.
* `rainbowAttack` (Algorithm `A₁`, p. 746) runs over `TableAttackSpec P Y`—hash queries on the left
  (`hashCost`) and table lookups on the right (`lookupCost`)—searching steps `k = 0, ..., τ - 1`
  (columns `τ - 1` down to `0`, corresponding to `for i = τ downto 1`) with `List.findSomeM?`,
  reconstructing a candidate preimage on each table hit and verifying `h(pw) = y` before returning
  `some pw`.

Deterministic run-level query counts (`queriesWith`) for both `rainbowAttack` and Hellman's
single-reduction stateful variant (`hellmanAttack`, Fig. 18.13a, p. 744) are proved in
`CslibFrontier.Crypto.RainbowTable.RunCost`.

This formalization differs from the book's presentation as follows:

1. **0-indexed columns.** Reduction functions are indexed `0, ..., τ - 1` rather than `1, ..., τ`;
   loop step `k ∈ {0, ..., τ - 1}` tests column `col = τ - 1 - k` (`i = τ - k` in `for i = τ
   downto 1`).
2. **Explicit starting list.** Sampling `ℓ` random starting points `pw_1, ..., pw_ℓ ∈ P` is
   factored out into the parameter `starts : List P`.
3. **Endpoint-keyed table and abstract lookup oracle.** `rainbowPreprocess` stores `(z_i, pw_i)`
   rather than `(pw_i, z_i)` so that `List.lookup` implements table lookup directly, as in
   `Cslib.Crypto.dictionaryTable`. Online inversion accesses the table through the right-hand
   oracle `P → Option P` of `TableAttackSpec P Y`, separating hash evaluations (`hashCost`) from
   table lookups (`lookupCost`) without claiming constant machine time for `List.lookup`.
4. **Failure output.** Inversion returns `Option P` (`none` for "fail").
5. **Pointwise coverage vs heuristic coverage estimate.** Soundness and inversion on covered chains
   are proved pointwise for arbitrary `h` and `g`; the book's heuristic success-probability
   approximations modeling `h` and `g_j` as random functions (pp. 743–746) and machine-level
   running-time bounds are not claimed (#5752).

## Main definitions

* `Cslib.Crypto.rainbowChainPure`: pure evaluation of `len` columns starting at `start`.
* `Cslib.Crypto.rainbowChain`: oracle program evaluating `len` columns against `h : P → Y`.
* `Cslib.Crypto.rainbowPreprocess`: preprocessing algorithm `A₀` producing `(z_i, pw_i)` pairs.
* `Cslib.Crypto.TableAttackSpec`: summed oracle interface of hash queries and table lookups.
* `Cslib.Crypto.hashCost`, `Cslib.Crypto.lookupCost`: per-call weights counting hash evaluations
  and table lookups.
* `Cslib.Crypto.rainbowAttackStep`, `Cslib.Crypto.rainbowAttack`: online rainbow-table inversion
  algorithm `A₁`.

## Main results

* `Cslib.Crypto.rainbowChainPure_add`, `Cslib.Crypto.rainbowChainPure_const`: chain splitting and
  specialization of constant reduction functions `fun _ => g₀` to `(fun x => g₀ (h x))^[len]`.
* `Cslib.Crypto.evalPure_rainbowChain`, `Cslib.Crypto.isQueryBounded_rainbowChain`,
  `Cslib.Crypto.length_queriesWith_rainbowChain`: deterministic semantics and exact `len` query
  count of `rainbowChain`.
* `Cslib.Crypto.evalPure_rainbowPreprocess`, `Cslib.Crypto.isQueryBounded_rainbowPreprocess`:
  correctness and `starts.length * τ` query bound of `rainbowPreprocess`.
* `Cslib.Crypto.evalPure_rainbowAttack`: deterministic evaluation of `rainbowAttack` via
  `List.findSome?`.
* `Cslib.Crypto.rainbowAttack_sound`: every returned password satisfies `h pw = y` (no false alarms
  are output).
* `Cslib.Crypto.exists_evalPure_rainbowAttack_of_lookup_eq_some`,
  `Cslib.Crypto.evalPure_rainbowAttack_of_injective`: completeness on covered chain entries, and
  exact recovery of `pw` when `h` is injective.
* `Cslib.Crypto.isCostBounded_lookupCost_rainbowAttack`,
  `Cslib.Crypto.isCostBounded_hashCost_rainbowAttack`: pathwise budgets of `τ` lookups and `τ * τ`
  hash evaluations.

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
([BonehShoup2023], Section 18.7, Fig. 18.13b, p. 745): column `j` applies `f_j(x) = g j (h x)`.
Columns are 0-indexed (`0, ..., τ - 1` for the book's `g_1, ..., g_τ`). -/
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
(Hellman's chain, [BonehShoup2023], Fig. 18.13a, p. 743). -/
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
`starts` ([BonehShoup2023], Section 18.7, pp. 743, 745–746): computes the endpoint
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
`starts.length * τ` hash queries on every path ([BonehShoup2023], Section 18.7, pp. 743, 746). -/
theorem isQueryBounded_rainbowPreprocess (g : ℕ → Y → P) (τ : ℕ) (starts : List P) :
    OracleComp.IsQueryBounded (rainbowPreprocess (Y := Y) g τ starts) (starts.length * τ) :=
  OracleComp.IsCostBounded.mapM fun pw₀ _ =>
    (OracleComp.isCostBounded_map_iff _ _ _).mpr (isQueryBounded_rainbowChain g 0 τ pw₀)

/-! ### Online inversion interface and algorithm `A₁` -/

/-- Summed oracle interface for online table-assisted inversion ([BonehShoup2023], Section 18.7,
p. 742): hash evaluations `P → Y` on the left and endpoint-to-start table lookups `P → Option P` on
the right. -/
abbrev TableAttackSpec (P Y : Type) : OracleSpec (P ⊕ P) :=
  (fun _ : P => Y) ⊕ₒ (fun _ : P => Option P)

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

section Attack

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
  simp only [rainbowAttackStep, OracleComp.evalPure_bind, OracleComp.evalPure_liftLeft,
    evalPure_rainbowChain, OracleComp.evalPure_liftRight, OracleComp.evalPure_query]
  cases lookup (rainbowChainPure h g (τ - k) k (g (τ - 1 - k) y)) with
  | none => rfl
  | some pw₀ =>
    simp only [OracleComp.evalPure_bind, OracleComp.evalPure_liftLeft, evalPure_rainbowChain,
      OracleComp.evalPure_query]
    split_ifs <;> rfl

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
  rw [evalPure_rainbowAttack] at heval
  obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some heval
  cases hlk : lookup (rainbowChainPure h g (τ - k) k (g (τ - 1 - k) y)) with
  | none =>
    rw [hlk] at hk
    cases hk
  | some pw₀ =>
    rw [hlk] at hk
    dsimp only at hk
    split_ifs at hk with hcheck
    cases hk
    exact hcheck

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
    have hk_mem : τ - 1 - col ∈ List.range τ := List.mem_range.mpr (by omega)
    have hstep := heval (τ - 1 - col) hk_mem
    have hsub₁ : τ - 1 - (τ - 1 - col) = col := by omega
    have hsub₂ : τ - (τ - 1 - col) = col + 1 := by omega
    have hadd := rainbowChainPure_add h g 0 col (τ - 1 - col + 1) pw₀
    simp only [Nat.zero_add] at hadd
    have hend :
        rainbowChainPure h g (τ - (τ - 1 - col)) (τ - 1 - col) (g (τ - 1 - (τ - 1 - col)) y) =
          rainbowChainPure h g 0 τ pw₀ := by
      rw [hsub₁, hsub₂, ← hy, ← rainbowChainPure_succ, ← hadd]
      congr 1
      omega
    rw [hend, hlookup, hsub₁] at hstep
    simp only [hy, ↓reduceIte, reduceCtorEq] at hstep

/-- When `h` is injective, `rainbowAttack` recovers `pw` itself on any covered chain point. -/
theorem evalPure_rainbowAttack_of_injective {h : P → Y} {lookup : P → Option P} {g : ℕ → Y → P}
    {τ col : ℕ} {pw₀ pw : P} {y : Y} (hinj : Function.Injective h) (hcol : col < τ)
    (hpw : rainbowChainPure h g 0 col pw₀ = pw) (hy : h pw = y)
    (hlookup : lookup (rainbowChainPure h g 0 τ pw₀) = some pw₀) :
    (rainbowAttack g τ y).evalPure (OracleComp.sumPure h lookup) = some pw := by
  obtain ⟨pw', heval, hy'⟩ :=
    exists_evalPure_rainbowAttack_of_lookup_eq_some hcol (hpw ▸ hy) hlookup
  exact heval.trans (congrArg some (hinj (hy'.trans hy.symm)))

private theorem isCostBounded_lookupCost_rainbowAttackStep (g : ℕ → Y → P) (τ : ℕ) (y : Y)
    (k : ℕ) :
    OracleComp.IsCostBounded lookupCost (rainbowAttackStep g τ y k) 1 := by
  unfold rainbowAttackStep
  rw [show (1 : ℕ) = 0 + (1 + 0) from rfl]
  refine (OracleComp.IsCostBounded.liftLeft_of_cost_inl_eq_zero lookupCost_inl _).bind fun z => ?_
  refine ((OracleComp.IsCostBounded.query (cost := fun _ : P => 1) z).liftRight
    fun q => (lookupCost_inr q).le).bind fun hit => ?_
  cases hit with
  | none => exact .pure none 0
  | some pw₀ =>
    rw [show (0 : ℕ) = 0 + (0 + 0) from rfl]
    refine (OracleComp.IsCostBounded.liftLeft_of_cost_inl_eq_zero lookupCost_inl _).bind fun pw =>
      (OracleComp.IsCostBounded.liftLeft_of_cost_inl_eq_zero lookupCost_inl _).bind fun y' => ?_
    split_ifs <;> exact .pure _ 0

private theorem isCostBounded_hashCost_rainbowAttackStep (g : ℕ → Y → P) {τ : ℕ} (y : Y) {k : ℕ}
    (hk : k < τ) :
    OracleComp.IsCostBounded hashCost (rainbowAttackStep g τ y k) τ := by
  refine (?_ : OracleComp.IsCostBounded hashCost (rainbowAttackStep g τ y k)
    (k + (0 + ((τ - 1 - k) + (1 + 0))))).mono (by omega)
  unfold rainbowAttackStep
  refine ((isQueryBounded_rainbowChain g (τ - k) k _).liftLeft
    fun q => (hashCost_inl q).le).bind fun z => ?_
  refine (OracleComp.IsCostBounded.liftRight_of_cost_inr_eq_zero hashCost_inr _).bind fun hit => ?_
  cases hit with
  | none => exact .pure none _
  | some pw₀ =>
    refine ((isQueryBounded_rainbowChain g 0 (τ - 1 - k) pw₀).liftLeft
      fun q => (hashCost_inl q).le).bind fun pw => ?_
    refine ((OracleComp.IsCostBounded.query (cost := fun _ : P => 1) pw).liftLeft
      fun q => (hashCost_inl q).le).bind fun y' => ?_
    split_ifs <;> exact .pure _ 0

/-- **Pathwise lookup budget of `A₁`.** `rainbowAttack` makes at most `τ` table lookups on every
path ([BonehShoup2023], Section 18.7, p. 746). -/
theorem isCostBounded_lookupCost_rainbowAttack (g : ℕ → Y → P) (τ : ℕ) (y : Y) :
    OracleComp.IsCostBounded lookupCost (rainbowAttack g τ y) τ := by
  have h := OracleComp.IsCostBounded.findSomeM? (xs := List.range τ) (n := 1)
    fun k _ => isCostBounded_lookupCost_rainbowAttackStep g τ y k
  simpa only [rainbowAttack, List.length_range, Nat.mul_one] using h

/-- **Pathwise hash budget of `A₁`.** Across arbitrary answers (even if every lookup hits and fails
verification), `rainbowAttack` makes at most `τ * τ` hash queries on every path. -/
theorem isCostBounded_hashCost_rainbowAttack (g : ℕ → Y → P) (τ : ℕ) (y : Y) :
    OracleComp.IsCostBounded hashCost (rainbowAttack g τ y) (τ * τ) := by
  have h := OracleComp.IsCostBounded.findSomeM? (xs := List.range τ) (n := τ)
    fun k hk => isCostBounded_hashCost_rainbowAttackStep g y (List.mem_range.mp hk)
  simpa only [rainbowAttack, List.length_range] using h

end Attack

end Cslib.Crypto
