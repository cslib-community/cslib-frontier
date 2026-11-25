/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.FactorTable
import CslibFrontier.Foundations.Data.List.FoldMax
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Dedup
import Mathlib.Tactic.Ring

/-!
# Variable elimination in a supplied order over explicit factor tables

This module implements pure bucket (variable) elimination in an arbitrary supplied order
`order : List V` over explicit `FactorTable R V` tables, together with intermediate-scope width,
bucket-count, and peak live-table size bounds expressed in terms of the actual intermediate scopes
and live tables produced along `order`. Machine-level Word-RAM running-time bounds over
materialized radix-indexed factor tables live in
`CslibFrontier.Algorithms.WordRAM.VariableElimination`.

An elimination state `ElimState R V` records an accumulated scalar factor `scalar : R` (for
eliminated isolated variables), the current list of live factor tables `live`, and the list of
variables `remaining` not yet summed out. Eliminating a variable `x ∈ remaining` partitions
`live` into `bucket := live.filter (x ∈ ·.scope)` and `rest := live.filter (x ∉ ·.scope)`. If
`bucket` is empty (an isolated variable), `scalar` is multiplied by `(d : R)` with zero new
tables; otherwise a new table on `outScope := (bucket.flatMap scope).dedup.filter (· != x)` is
materialized by summing over `0, ..., d - 1` the product of `bucket`, replacing `bucket` in
`live`.

## Main definitions

* `Cslib.Algorithms.Lean.CSP.ElimState`: live tables, scalar accumulator, and uneliminated
  variables.
* `Cslib.Algorithms.Lean.CSP.ElimStepStats`: exact intermediate-scope and live-table statistics for
  one elimination step.
* `Cslib.Algorithms.Lean.CSP.elimVar`, `Cslib.Algorithms.Lean.CSP.eliminateOrder`: pure variable
  elimination along `order : List V`.
* `Cslib.Algorithms.Lean.CSP.traceOrder`, `Cslib.Algorithms.Lean.CSP.maxJointScopeLen`,
  `Cslib.Algorithms.Lean.CSP.maxOutScopeLen`, `Cslib.Algorithms.Lean.CSP.peakLiveEntries`:
  exact intermediate-scope width and peak live-table memory metrics along `order`.

## Main results

* `Cslib.Algorithms.Lean.CSP.eval_elimVar`,
  `Cslib.Algorithms.Lean.CSP.eval_eliminateOrder`,
  `Cslib.Algorithms.Lean.CSP.result_eliminateOrder_ofCSP`: invariance of the contracted value
  for arbitrary elimination orders `order`, matching `CSP.partitionFunctionOn` /
  `CSP.partitionFunction`.
* `Cslib.Algorithms.Lean.CSP.sum_bucketFactors_le`,
  `Cslib.Algorithms.Lean.CSP.totalArithOps_le_of_intermediate`: amortized bucket-count invariant
  and scalar operation bounds in terms of the actual intermediate scopes.
* `Cslib.Algorithms.Lean.CSP.liveLength_eliminateOrder_le`,
  `Cslib.Algorithms.Lean.CSP.peakLiveEntries_le`: live table count never increases and peak
  live-table entry count is bounded by
  `init.live.length * max maxInitEntries (d ^ maxOutScopeLen)`.
-/

public section

namespace Cslib.Algorithms.Lean.CSP

open Cslib.Logic.PL Cslib.Logic.PL.CSP

/-! ### Elimination state and intermediate-scope statistics -/

section Definitions

variable {R V : Type*}

/-- State of variable elimination: accumulated scalar from isolated variables, current list of
live factor tables, and variables still to be summed out. -/
structure ElimState (R V : Type*) where
  /-- Scalar contribution from isolated variables eliminated so far. -/
  scalar : R
  /-- Currently active factor tables. -/
  live : List (FactorTable R V)
  /-- Variables not yet eliminated. -/
  remaining : List V
  deriving DecidableEq, Repr

/-- Intermediate-scope and live-memory statistics recorded at a single elimination step. -/
structure ElimStepStats where
  /-- Number of live factors participating in this variable's bucket. -/
  bucketFactors : ℕ
  /-- Distinct variables in the joint intermediate bucket scope (0 if inactive/isolated). -/
  jointScopeVars : ℕ
  /-- Distinct variables in the produced table's scope (`jointScopeVars - 1` if active). -/
  outScopeVars : ℕ
  /-- Number of live factors after the step. -/
  liveFactorsAfter : ℕ
  /-- Total stored entries across all live tables after the step. -/
  liveEntriesAfter : ℕ
  /-- Number of scalar arithmetic operations (multiplications and additions) performed at step. -/
  arithOps : ℕ
  deriving DecidableEq, Repr

/-- Evaluate a list of base-`d` digits aligned with a variable list into an assignment `V → ℕ`
(defaulting to `0` outside bounds). -/
@[expose] def assignScope [DecidableEq V] : List V → List ℕ → V → ℕ
  | [], _, _ => 0
  | _, [], _ => 0
  | u :: us, k :: ks, v => if v = u then k else assignScope us ks v

/-- Total number of stored entries across all live tables. -/
@[expose] def liveEntries (live : List (FactorTable R V)) : ℕ :=
  (live.map fun f => f.entries.size).sum

/-- Maximum single-table entry count in `live`. -/
@[expose] def maxTableEntries (live : List (FactorTable R V)) : ℕ :=
  (live.map fun f => f.entries.size).foldl max 0

/-- Maximum factor scope length in `live`. -/
@[expose] def maxScopeLen (live : List (FactorTable R V)) : ℕ :=
  (live.map fun f => f.scope.length).foldl max 0

/-- Initial elimination state for a factor list over a declared variable list. -/
@[expose] def ElimState.ofFactors [One R] (factors : List (FactorTable R V))
    (declared : List V) : ElimState R V :=
  { scalar := 1, live := factors, remaining := declared }

/-- Contracted value represented by an `ElimState`: `scalar * contractionOn d live remaining`. -/
@[expose] def ElimState.eval [Semiring R] [DecidableEq V] (d : ℕ) (s : ElimState R V) : R :=
  s.scalar * FactorTable.contractionOn d s.live s.remaining.toFinset

/-- Scalar product of a state once all variables have been eliminated. -/
@[expose] def ElimState.result [Monoid R] [Zero R] (s : ElimState R V) : R :=
  s.scalar * (s.live.map fun f => f.entries.getD 0 0).prod

/-- Joint deduplicated scope of the factors in a bucket. -/
@[expose] def bucketJointScope [DecidableEq V] (bucket : List (FactorTable R V)) : List V :=
  (bucket.flatMap FactorTable.scope).dedup

/-- Scope of the output table produced by eliminating `x` from `bucket`. -/
@[expose] def bucketOutScope [DecidableEq V] (x : V)
    (bucket : List (FactorTable R V)) : List V :=
  (bucketJointScope bucket).filter fun v => decide (v ≠ x)

/-- Build the output factor table for eliminating `x` from a nonempty `bucket` at domain
size `d`. -/
@[expose] def elimBucketTable [Semiring R] [DecidableEq V] (d : ℕ) (x : V)
    (bucket : List (FactorTable R V)) : FactorTable R V :=
  let outScope := bucketOutScope x bucket
  { scope := outScope
    entries := Array.ofFn fun idx : Fin (d ^ outScope.length) =>
      let digits := lsbDecode d outScope.length idx.1
      let assign := assignScope outScope digits
      ∑ a : Fin d,
        (bucket.map fun f => f.evalAt d fun v => if v = x then a.1 else assign v).prod }

/-- Perform one elementary variable elimination step on `x`. -/
@[expose] def elimVar [Semiring R] [DecidableEq V] (d : ℕ) (x : V)
    (s : ElimState R V) : ElimState R V :=
  if x ∈ s.remaining then
    let bucket := s.live.filter fun f => decide (x ∈ f.scope)
    let rest := s.live.filter fun f => decide (x ∉ f.scope)
    let rem' := s.remaining.filter fun v => decide (v ≠ x)
    if bucket.isEmpty then
      { scalar := s.scalar * (d : R), live := s.live, remaining := rem' }
    else
      { scalar := s.scalar, live := elimBucketTable d x bucket :: rest, remaining := rem' }
  else
    s

/-- Eliminate variables sequentially along a supplied order `order : List V`. -/
@[expose] def eliminateOrder [Semiring R] [DecidableEq V] (d : ℕ) :
    List V → ElimState R V → ElimState R V
  | [], s => s
  | x :: xs, s => eliminateOrder d xs (elimVar d x s)

/-- Statistics for a single elimination step `elimVar d x s`. -/
@[expose] def stepStats [Semiring R] [DecidableEq V] (d : ℕ) (x : V)
    (s : ElimState R V) : ElimStepStats :=
  let s' := elimVar d x s
  if x ∈ s.remaining then
    let bucket := s.live.filter fun f => decide (x ∈ f.scope)
    if bucket.isEmpty then
      { bucketFactors := 0
        jointScopeVars := 0
        outScopeVars := 0
        liveFactorsAfter := s'.live.length
        liveEntriesAfter := liveEntries s'.live
        arithOps := 1 }
    else
      let joint := bucketJointScope bucket
      let out := bucketOutScope x bucket
      { bucketFactors := bucket.length
        jointScopeVars := joint.length
        outScopeVars := out.length
        liveFactorsAfter := s'.live.length
        liveEntriesAfter := liveEntries s'.live
        arithOps := d ^ joint.length * (bucket.length + 1) }
  else
    { bucketFactors := 0
      jointScopeVars := 0
      outScopeVars := 0
      liveFactorsAfter := s'.live.length
      liveEntriesAfter := liveEntries s'.live
      arithOps := 0 }

/-- Sequence of intermediate step statistics produced along `order`. -/
@[expose] def traceOrder [Semiring R] [DecidableEq V] (d : ℕ) :
    List V → ElimState R V → List ElimStepStats
  | [], _ => []
  | x :: xs, s => stepStats d x s :: traceOrder d xs (elimVar d x s)

/-- Maximum joint scope size across all steps along `order`. -/
@[expose] def maxJointScopeLen [Semiring R] [DecidableEq V] (d : ℕ) (order : List V)
    (init : ElimState R V) : ℕ :=
  ((traceOrder d order init).map ElimStepStats.jointScopeVars).foldl max 0

/-- Maximum output table scope size (`outScope.length`) across all steps along `order`. -/
@[expose] def maxOutScopeLen [Semiring R] [DecidableEq V] (d : ℕ) (order : List V)
    (init : ElimState R V) : ℕ :=
  ((traceOrder d order init).map ElimStepStats.outScopeVars).foldl max 0

/-- Peak total entries stored simultaneously in live tables across `order` (including `init`). -/
@[expose] def peakLiveEntries [Semiring R] [DecidableEq V] (d : ℕ) (order : List V)
    (init : ElimState R V) : ℕ :=
  ((traceOrder d order init).map ElimStepStats.liveEntriesAfter).foldl max (liveEntries init.live)

/-- Total arithmetic operations recorded along `order`. -/
@[expose] def totalArithOps [Semiring R] [DecidableEq V] (d : ℕ) (order : List V)
    (init : ElimState R V) : ℕ :=
  ((traceOrder d order init).map ElimStepStats.arithOps).sum

end Definitions

/-! ### Correctness and algebraic invariance -/

section Correctness

variable {R V : Type*}

private theorem assignScope_map [DecidableEq V] (σ : V → ℕ) :
    ∀ (us : List V) {v : V}, v ∈ us → assignScope us (us.map σ) v = σ v
  | [], _, hv => by simp at hv
  | u :: us, v, hv => by
      simp only [List.map_cons, assignScope]
      by_cases hvu : v = u
      · simp [hvu]
      · simp only [hvu, ↓reduceIte]
        exact assignScope_map σ us ((List.mem_cons.mp hv).resolve_left hvu)

private theorem mem_bucketJointScope [DecidableEq V] (bucket : List (FactorTable R V)) (v : V) :
    v ∈ bucketJointScope bucket ↔ ∃ f ∈ bucket, v ∈ f.scope := by
  simp [bucketJointScope, List.mem_dedup]

private theorem mem_bucketOutScope [DecidableEq V] (x : V) (bucket : List (FactorTable R V))
    (v : V) : v ∈ bucketOutScope x bucket ↔ v ≠ x ∧ ∃ f ∈ bucket, v ∈ f.scope := by
  simp only [bucketOutScope, List.mem_filter, mem_bucketJointScope, decide_eq_true_eq]
  exact ⟨fun ⟨⟨f, hf, hv⟩, hne⟩ => ⟨hne, f, hf, hv⟩, fun ⟨hne, f, hf, hv⟩ => ⟨⟨f, hf, hv⟩, hne⟩⟩

private theorem evalAt_elimBucketTable [CommSemiring R] [DecidableEq V] {d : ℕ}
    (x : V) (bucket : List (FactorTable R V)) (σ : V → ℕ)
    (hlt : ∀ v ∈ bucketOutScope x bucket, σ v < d) :
    (elimBucketTable d x bucket).evalAt d σ =
      ∑ a : Fin d,
        (bucket.map fun f => f.evalAt d fun v => if v = x then a.1 else σ v).prod := by
  let outScope := bucketOutScope x bucket
  have hlt_map : ∀ k ∈ outScope.map σ, k < d := by
    intro k hk; rcases List.mem_map.mp hk with ⟨v, hv, rfl⟩; exact hlt v hv
  have hidx : Nat.ofDigits d (outScope.map σ) < d ^ outScope.length := by
    simpa [List.length_map] using ofDigits_lt_pow_length _ hlt_map
  have hdec : lsbDecode d outScope.length (Nat.ofDigits d (outScope.map σ)) = outScope.map σ := by
    simpa [List.length_map] using lsbDecode_ofDigits (outScope.map σ) hlt_map
  rw [FactorTable.evalAt, elimBucketTable, Array.getD]
  dsimp only
  split_ifs with hsz
  · change (Array.ofFn _)[Nat.ofDigits d (outScope.map σ)]'(by simpa [outScope] using hidx) = _
    rw [Array.getElem_ofFn]
    dsimp only; rw [hdec]
    refine Finset.sum_congr rfl fun a _ => congrArg List.prod ?_
    refine List.map_congr_left fun f hf => FactorTable.evalAt_congr fun v hv => ?_
    by_cases hvx : v = x
    · simp [hvx]
    · simp only [hvx, ↓reduceIte]
      exact assignScope_map σ outScope ((mem_bucketOutScope x bucket v).mpr ⟨hvx, f, hf, hv⟩)
  · exact absurd (by simpa [outScope] using hidx) hsz

private theorem evalAt_elimBucketTable_zero [Semiring R] [DecidableEq V] (x : V)
    (bucket : List (FactorTable R V)) (σ : V → ℕ) :
    (elimBucketTable 0 x bucket).evalAt 0 σ = 0 := by
  rw [FactorTable.evalAt, elimBucketTable, Array.getD]
  dsimp only
  split_ifs with hsz
  · change (Array.ofFn _)[Nat.ofDigits 0 (List.map σ (bucketOutScope x bucket))]'hsz = 0
    rw [Array.getElem_ofFn]; simp
  · rfl

/-- Eliminating one variable preserves `ElimState.eval`. -/
theorem eval_elimVar [CommSemiring R] [DecidableEq V] (d : ℕ) (x : V) (s : ElimState R V) :
    (elimVar d x s).eval d = s.eval d := by
  by_cases hx : x ∈ s.remaining
  · let U := s.remaining.toFinset
    let U' := U.erase x
    have hxU : x ∈ U := List.mem_toFinset.mpr hx
    have hrem' : (s.remaining.filter fun v => decide (v ≠ x)).toFinset = U' := by
      ext v; simp [U, U', Finset.mem_erase, and_comm]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · have : IsEmpty (U → Fin 0) := ⟨fun σ => Fin.elim0 (σ ⟨x, hxU⟩)⟩
      have hs0 : s.eval 0 = 0 := by simp [ElimState.eval, FactorTable.contractionOn, U]
      rw [elimVar, hs0]; simp only [hx, ↓reduceIte]
      split_ifs
      · simp [ElimState.eval]
      · rw [ElimState.eval, FactorTable.contractionOn]
        exact (congrArg (s.scalar * ·) (Finset.sum_eq_zero fun σ _ => by
          rw [List.map_cons, List.prod_cons, evalAt_elimBucketTable_zero, zero_mul])).trans
          (mul_zero s.scalar)
    · let eSplit : (U → Fin d) ≃ Fin d × (U' → Fin d) :=
        { toFun := fun σ => (σ ⟨x, hxU⟩, fun v => σ ⟨v.1, Finset.mem_of_mem_erase v.2⟩)
          invFun := fun p v =>
            if h : v.1 = x then p.1 else p.2 ⟨v.1, Finset.mem_erase.mpr ⟨h, v.2⟩⟩
          left_inv := fun σ => funext fun v => by
            by_cases hvx : v.1 = x
            · simp only [hvx, ↓reduceDIte]; exact congrArg σ (Subtype.ext hvx.symm)
            · simp [hvx]
          right_inv := fun p => by
            ext v
            · simp
            · simp [Finset.ne_of_mem_erase v.2] }
      let bucket := s.live.filter fun f => decide (x ∈ f.scope)
      let rest := s.live.filter fun f => decide (x ∉ f.scope)
      have hrest_eq : (s.live.filter fun f => !decide (x ∈ f.scope)) = rest := by
        simp only [decide_not, rest]
      let ext0 : (U' → Fin d) → V → ℕ := fun τ v => if h : v ∈ U' then (τ ⟨v, h⟩).1 else 0
      let ext : (U' → Fin d) → Fin d → V → ℕ := fun τ a v => if v = x then a.1 else ext0 τ v
      have hs_eq : s.eval d = s.scalar * ∑ τ : U' → Fin d,
          ∑ a : Fin d, (s.live.map fun f => f.evalAt d (ext τ a)).prod := by
        rw [ElimState.eval, FactorTable.contractionOn]
        congr 1
        rw [Fintype.sum_equiv eSplit _ (fun p =>
          (s.live.map fun f => f.evalAt d (ext p.2 p.1)).prod)]
        · exact Fintype.sum_prod_type_right _
        · intro σ
          refine congrArg List.prod (List.map_congr_left fun f _ =>
            FactorTable.evalAt_congr fun v _ => ?_)
          by_cases hvx : v = x
          · subst hvx; simp [eSplit, ext, hx]
          · by_cases hvU : v ∈ U
            · have hvU' : v ∈ U' := Finset.mem_erase.mpr ⟨hvx, hvU⟩
              have hvrem : v ∈ s.remaining := List.mem_toFinset.mp hvU
              simp [eSplit, hvx, hvU', hvrem, ext, ext0]
            · have hvrem : v ∉ s.remaining := fun h => hvU (List.mem_toFinset.mpr h)
              have hvU' : v ∉ U' := fun h => hvU (Finset.mem_of_mem_erase h)
              simp [hvx, hvrem, hvU', ext, ext0]
      have hfactor : ∀ τ : U' → Fin d,
          ∑ a : Fin d, (s.live.map fun f => f.evalAt d (ext τ a)).prod =
            (∑ a : Fin d, (bucket.map fun f => f.evalAt d (ext τ a)).prod) *
              (rest.map fun f => f.evalAt d (ext0 τ)).prod := fun τ => by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        have hsplit := ((List.filter_append_perm
          (fun f : FactorTable R V => decide (x ∈ f.scope)) s.live).map
          fun f => f.evalAt d (ext τ a)).prod_eq
        simp only [List.map_append, List.prod_append, hrest_eq] at hsplit
        rw [← hsplit]
        dsimp only [bucket]
        refine congrArg (_ * ·) (congrArg List.prod (List.map_congr_left fun f hf =>
          FactorTable.evalAt_congr fun v hv => ?_))
        have hnx : x ∉ f.scope := by simpa using (List.mem_filter.mp hf).2
        simp [ext, show v ≠ x from fun h => hnx (h ▸ hv)]
      rw [elimVar]; simp only [hx, ↓reduceIte]
      split_ifs with hb
      · have hbnil : bucket = [] := List.isEmpty_iff.mp hb
        have hrest_all : rest = s.live := List.filter_eq_self.mpr fun f hf => by
          simpa using List.filter_eq_nil_iff.1 hbnil f hf
        rw [hs_eq, ElimState.eval, FactorTable.contractionOn, hrem']
        simp only [hbnil, List.map_nil, List.prod_nil, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, mul_one, hfactor, hrest_all]
        rw [← Finset.mul_sum, ← mul_assoc]
      · rw [hs_eq, ElimState.eval, FactorTable.contractionOn, hrem']
        refine congrArg (s.scalar * ·) (Finset.sum_congr rfl fun τ _ => ?_)
        rw [hfactor τ, List.map_cons, List.prod_cons]
        have hlt : ∀ v ∈ bucketOutScope x bucket, ext0 τ v < d := fun v _ => by
          by_cases hv : v ∈ U' <;> simp [ext0, hv, hd]
        simpa [bucket, ext0, ext, hrest_eq] using
          congrArg (· * _) (evalAt_elimBucketTable x bucket (ext0 τ) hlt)
  · simp [elimVar, hx]

/-- Sequential variable elimination preserves `ElimState.eval` for every supplied order. -/
theorem eval_eliminateOrder [CommSemiring R] [DecidableEq V] (d : ℕ) :
    ∀ (order : List V) (s : ElimState R V), (eliminateOrder d order s).eval d = s.eval d
  | [], _ => rfl
  | x :: xs, s => by
      rw [eliminateOrder, eval_eliminateOrder d xs (elimVar d x s), eval_elimVar]

/-- Variable elimination removes exactly the variables appearing in `order` from `remaining`. -/
theorem remaining_toFinset_eliminateOrder [Semiring R] [DecidableEq V] (d : ℕ) :
    ∀ (order : List V) (s : ElimState R V),
      (eliminateOrder d order s).remaining.toFinset = s.remaining.toFinset \ order.toFinset
  | [], s => by simp [eliminateOrder]
  | x :: xs, s => by
      rw [eliminateOrder, remaining_toFinset_eliminateOrder d xs (elimVar d x s),
        List.toFinset_cons]
      by_cases hx : x ∈ s.remaining
      · have hrem : (elimVar d x s).remaining.toFinset = s.remaining.toFinset.erase x := by
          rw [elimVar]; simp only [hx, ↓reduceIte]
          split_ifs <;> · ext v; simp [Finset.mem_erase, and_comm]
        rw [hrem]; ext v; simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]; tauto
      · have hrem : (elimVar d x s).remaining = s.remaining := by simp [elimVar, hx]
        rw [hrem]; ext v
        simp only [Finset.mem_sdiff, Finset.mem_insert, List.mem_toFinset]
        exact ⟨fun ⟨hv, hne⟩ => ⟨hv, fun h => h.elim (fun hEq => hx (hEq ▸ hv)) hne⟩,
          fun ⟨hv, hne⟩ => ⟨hv, fun h => hne (Or.inr h)⟩⟩

/-- Once `s.remaining = []`, `s.eval d` equals the pure scalar table product `s.result`. -/
theorem eval_eq_result_of_remaining_nil [Semiring R] [DecidableEq V] (d : ℕ)
    {s : ElimState R V} (hrem : s.remaining = []) :
    s.eval d = s.result := by
  rw [ElimState.eval, FactorTable.contractionOn, hrem, List.toFinset_nil, ElimState.result,
    Fintype.sum_unique]
  refine congrArg (s.scalar * List.prod ·) (List.map_congr_left fun f _ => ?_)
  rw [FactorTable.evalAt, show (fun v : V => if h : v ∈ (∅ : Finset V) then
    ((default : (∅ : Finset V) → Fin d) ⟨v, h⟩).1 else 0) = fun _ => 0 from funext fun _ => by simp,
    ofDigits_map_zero]

/-- If `order` covers all initial declared variables `init.remaining`, eliminating along `order`
leaves `remaining = []` and its scalar `result` recovers `init.eval d`. -/
theorem result_eliminateOrder_of_subset [CommSemiring R] [DecidableEq V] (d : ℕ)
    {order : List V} {s : ElimState R V}
    (hcover : s.remaining.toFinset ⊆ order.toFinset) :
    (eliminateOrder d order s).result = s.eval d := by
  have hrem_set : (eliminateOrder d order s).remaining.toFinset = ∅ := by
    rw [remaining_toFinset_eliminateOrder d, Finset.sdiff_eq_empty_iff_subset.mpr hcover]
  have hrem_nil : (eliminateOrder d order s).remaining = [] := by
    cases hr : (eliminateOrder d order s).remaining with
    | nil => rfl
    | cons v _ =>
      have : v ∈ (∅ : Finset V) := (Finset.ext_iff.mp hrem_set v).mp (by simp [hr])
      simp at this
  rw [← eval_eq_result_of_remaining_nil d hrem_nil, eval_eliminateOrder]

/-- Contracting a weighted CSP by variable elimination in ANY supplied order `order` covering
`declared` recovers `F.partitionFunctionOn wt declared`. -/
theorem result_eliminateOrder_ofCSP {Rel D : Type*} [CommSemiring R] [DecidableEq V] [Fintype D]
    [Inhabited D] (d : ℕ) (e : D ≃ Fin d) (wt : Rel → List D → R) {F : CSP Rel V}
    {declared order : List V}
    (hvars : F.vars.toFinset ⊆ declared.toFinset)
    (hcover : declared.toFinset ⊆ order.toFinset) :
    (eliminateOrder d order (ElimState.ofFactors (FactorTable.ofCSP d e wt F) declared)).result =
      F.partitionFunctionOn wt declared.toFinset := by
  rw [result_eliminateOrder_of_subset d (order := order)
    (by simpa [ElimState.ofFactors] using hcover)]
  simp only [ElimState.eval, ElimState.ofFactors, one_mul]
  exact FactorTable.contractionOn_ofCSP d e wt hvars

/-- Contracting a weighted CSP in ANY order covering `F.vars` recovers `F.partitionFunction wt`. -/
theorem result_eliminateOrder_ofCSP_vars {Rel D : Type*} [CommSemiring R] [DecidableEq V]
    [Fintype D] [Inhabited D] (d : ℕ) (e : D ≃ Fin d) (wt : Rel → List D → R) (F : CSP Rel V)
    {order : List V} (hcover : F.vars.toFinset ⊆ order.toFinset) :
    (eliminateOrder d order (ElimState.ofFactors (FactorTable.ofCSP d e wt F) F.vars)).result =
      F.partitionFunction wt := by
  have h := result_eliminateOrder_ofCSP d e wt Finset.Subset.rfl hcover
  simpa [CSP.partitionFunction_eq_partitionFunctionOn] using h

end Correctness

/-! ### Live-table size and intermediate-scope operation bounds -/

section IntermediateScopeBounds

variable {R V : Type*}

private theorem list_sum_map_le {α : Type*} (l : List α) (m : α → ℕ) {B : ℕ}
    (hm : ∀ a ∈ l, m a ≤ B) : (l.map m).sum ≤ l.length * B := by
  simpa [smul_eq_mul] using List.sum_le_length_nsmul (l.map m) B fun _ hn => by
    rcases List.mem_map.mp hn with ⟨a, ha, rfl⟩; exact hm a ha

/-- Eliminating one variable never increases the number of live factor tables. -/
theorem length_elimVar_live_le [Semiring R] [DecidableEq V] (d : ℕ) (x : V)
    (s : ElimState R V) : (elimVar d x s).live.length ≤ s.live.length := by
  by_cases hx : x ∈ s.remaining
  · simp only [elimVar, hx, ↓reduceIte]
    split_ifs with hb
    · exact le_rfl
    · simp only [List.length_cons]
      have hlen := List.length_eq_length_filter_add (l := s.live) fun f => decide (x ∈ f.scope)
      have hbpos : 1 ≤ (s.live.filter fun f => decide (x ∈ f.scope)).length := by
        cases h : s.live.filter fun f => decide (x ∈ f.scope) <;> simp_all
      simp only [decide_not]; omega
  · simp [elimVar, hx]

/-- The number of live factor tables never increases along any elimination order. -/
theorem liveLength_eliminateOrder_le [Semiring R] [DecidableEq V] (d : ℕ) :
    ∀ (order : List V) (s : ElimState R V), (eliminateOrder d order s).live.length ≤ s.live.length
  | [], _ => le_rfl
  | x :: xs, s =>
      le_trans (liveLength_eliminateOrder_le d xs (elimVar d x s)) (length_elimVar_live_le d x s)

private theorem bucketFactors_add_live_le [Semiring R] [DecidableEq V] (d : ℕ) (x : V)
    (s : ElimState R V) :
    (stepStats d x s).bucketFactors + (elimVar d x s).live.length ≤ s.live.length + 1 := by
  by_cases hx : x ∈ s.remaining
  · simp only [stepStats, elimVar, hx, ↓reduceIte]
    split_ifs with hb
    · simp
    · have hlen := List.length_eq_length_filter_add (l := s.live) fun f => decide (x ∈ f.scope)
      simp only [decide_not, List.length_cons]; omega
  · simp [stepStats, elimVar, hx]

/-- Amortized bucket-count bound: the sum of bucket sizes across `order` is at most
`init.live.length + order.length`. -/
theorem sum_bucketFactors_le [Semiring R] [DecidableEq V] (d : ℕ) :
    ∀ (order : List V) (init : ElimState R V),
      ((traceOrder d order init).map ElimStepStats.bucketFactors).sum +
          (eliminateOrder d order init).live.length ≤
        init.live.length + order.length
  | [], init => by simp [traceOrder, eliminateOrder]
  | x :: xs, init => by
      have ih := sum_bucketFactors_le d xs (elimVar d x init)
      have hstep := bucketFactors_add_live_le d x init
      simp only [traceOrder, eliminateOrder, List.map_cons, List.sum_cons, List.length_cons]
      omega

/-- Every step along `order` has joint scope size at most `maxJointScopeLen d order init`. -/
theorem mem_traceOrder_joint_le [Semiring R] [DecidableEq V] (d : ℕ)
    (order : List V) (init : ElimState R V) {st : ElimStepStats}
    (hst : st ∈ traceOrder d order init) :
    st.jointScopeVars ≤ maxJointScopeLen d order init :=
  List.mem_le_foldl_max (List.mem_map.mpr ⟨st, hst, rfl⟩)

private theorem mem_traceOrder_out_le [Semiring R] [DecidableEq V] (d : ℕ)
    (order : List V) (init : ElimState R V) {st : ElimStepStats}
    (hst : st ∈ traceOrder d order init) :
    st.outScopeVars ≤ maxOutScopeLen d order init :=
  List.mem_le_foldl_max (List.mem_map.mpr ⟨st, hst, rfl⟩)

/-- Total scalar arithmetic operations along `order` are bounded by the maximum actual
intermediate bucket scope width `maxJointScopeLen d order init` and the amortized bucket factor
sum. -/
theorem totalArithOps_le_of_intermediate [Semiring R] [DecidableEq V] {d : ℕ} (hd : 0 < d)
    (order : List V) (init : ElimState R V) :
    totalArithOps d order init ≤
      order.length +
        (init.live.length + 2 * order.length) * d ^ maxJointScopeLen d order init := by
  let W := maxJointScopeLen d order init
  have hsum : ∀ (ord : List V) (s : ElimState R V),
      (∀ st ∈ traceOrder d ord s, st.jointScopeVars ≤ W) →
      ((traceOrder d ord s).map ElimStepStats.arithOps).sum ≤
        ord.length + (((traceOrder d ord s).map ElimStepStats.bucketFactors).sum + ord.length) *
          d ^ W := by
    intro ord; induction ord with
    | nil => intro s _; simp [traceOrder]
    | cons x xs ih =>
        intro s hW
        have hhead := hW (stepStats d x s) (by simp [traceOrder])
        have htail := ih (elimVar d x s) fun st hst => hW st (by simp [traceOrder, hst])
        have hst : (stepStats d x s).arithOps ≤
            1 + ((stepStats d x s).bucketFactors + 1) * d ^ W := by
          by_cases hx : x ∈ s.remaining
          · simp only [stepStats, hx, ↓reduceIte] at hhead ⊢
            split_ifs with hb
            · simp
            · simp only [hb] at hhead
              refine le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hd hhead)) ?_
              rw [Nat.mul_comm]
              exact Nat.le_add_left _ _
          · simp [stepStats, hx]
        simp only [traceOrder, List.map_cons, List.sum_cons, List.length_cons] at htail ⊢
        calc (stepStats d x s).arithOps + _
            ≤ (1 + ((stepStats d x s).bucketFactors + 1) * d ^ W) +
                (xs.length + (((traceOrder d xs (elimVar d x s)).map
                  ElimStepStats.bucketFactors).sum + xs.length) * d ^ W) :=
              Nat.add_le_add hst htail
          _ = (xs.length + 1) +
                (((stepStats d x s).bucketFactors + ((traceOrder d xs (elimVar d x s)).map
                  ElimStepStats.bucketFactors).sum) + (xs.length + 1)) * d ^ W := by ring
  have h0 := hsum order init fun st hst => mem_traceOrder_joint_le d order init hst
  have hbk := sum_bucketFactors_le d order init
  exact h0.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _)

private theorem maxOutScope_le_sub {R V : Type*} [Semiring R] [DecidableEq V] (d : ℕ)
    (order : List V) (init : ElimState R V) :
    ∀ st ∈ traceOrder d order init, st.outScopeVars ≤ st.jointScopeVars := by
  intro st hst; induction order generalizing init with
  | nil => simp [traceOrder] at hst
  | cons x xs ih =>
      rcases List.mem_cons.mp hst with rfl | hst
      · simp only [stepStats]; split_ifs
        · simp
        · exact List.length_filter_le _ _
        · simp
      · exact ih _ hst

/-- Output table dimension never exceeds the joint bucket dimension along any order. -/
theorem maxOutScopeLen_le_maxJointScopeLen [Semiring R] [DecidableEq V] (d : ℕ) (order : List V)
    (init : ElimState R V) :
    maxOutScopeLen d order init ≤ maxJointScopeLen d order init :=
  List.foldl_max_le (Nat.zero_le _) fun _ hn => by
    rcases List.mem_map.mp hn with ⟨st, hst, rfl⟩
    exact (maxOutScope_le_sub d order init st hst).trans
      (mem_traceOrder_joint_le d order init hst)

private theorem length_filter_ne_add_one {V : Type*} [DecidableEq V] :
    ∀ {l : List V} {x : V}, l.Nodup → x ∈ l →
      (l.filter fun v => decide (v ≠ x)).length + 1 = l.length
  | [], _, _, hx => by simp at hx
  | a :: l, x, hnodup, hx => by
      rcases List.nodup_cons.mp hnodup with ⟨han, hlnodup⟩
      rw [List.filter_cons]
      by_cases hax : a = x
      · subst hax
        have hnone : l.filter (fun v => decide (v ≠ a)) = l :=
          List.filter_eq_self.mpr fun v hv => decide_eq_true fun h => han (h ▸ hv)
        rw [ite_eq_right (by simp), hnone]; simp
      · rw [decide_eq_true hax]; simp only [↓reduceIte, List.length_cons]
        have := length_filter_ne_add_one hlnodup ((List.mem_cons.mp hx).resolve_left (Ne.symm hax))
        omega

/-- For a nonempty bucket of factors containing `x`, the output scope has one fewer variable than
the joint scope. -/
theorem length_bucketOutScope_add_one [DecidableEq V] {x : V} {bucket : List (FactorTable R V)}
    (hb : bucket ≠ []) (hx : ∀ f ∈ bucket, x ∈ f.scope) :
    (bucketOutScope x bucket).length + 1 = (bucketJointScope bucket).length := by
  have hxjoint : x ∈ bucketJointScope bucket := by
    rcases List.exists_mem_of_ne_nil bucket hb with ⟨f, hf⟩
    exact (mem_bucketJointScope bucket x).mpr ⟨f, hf, hx f hf⟩
  exact length_filter_ne_add_one (List.nodup_dedup _) hxjoint

private theorem elimVar_forall_le [Semiring R] [DecidableEq V] (d : ℕ) (x : V)
    (s : ElimState R V) (P : FactorTable R V → Prop) (hs : ∀ f ∈ s.live, P f)
    (hnew : x ∈ s.remaining → ¬(s.live.filter fun f => decide (x ∈ f.scope)).isEmpty = true →
      P (elimBucketTable d x (s.live.filter fun f => decide (x ∈ f.scope)))) :
    ∀ f ∈ (elimVar d x s).live, P f := by
  intro f hf
  by_cases hx : x ∈ s.remaining
  · simp only [elimVar, hx, ↓reduceIte] at hf
    split_ifs at hf with hb
    · exact hs f hf
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact hnew hx hb
      · exact hs f (List.mem_filter.mp hf).1
  · simp only [elimVar, hx, ↓reduceIte] at hf
    exact hs f hf

private theorem each_mem_le_maxTableEntries {live : List (FactorTable R V)} :
    ∀ f ∈ live, f.entries.size ≤ maxTableEntries live := fun f hf =>
  List.mem_le_foldl_max (List.mem_map.mpr ⟨f, hf, rfl⟩)

/-- Every factor in `live` has scope length at most `maxScopeLen live`. -/
theorem each_mem_le_maxScopeLen {live : List (FactorTable R V)} :
    ∀ f ∈ live, f.scope.length ≤ maxScopeLen live := fun f hf =>
  List.mem_le_foldl_max (List.mem_map.mpr ⟨f, hf, rfl⟩)

/-- Eliminating one variable never increases `remaining.length`. -/
theorem length_elimVar_remaining_le [Semiring R] [DecidableEq V] (d : ℕ) (x : V)
    (s : ElimState R V) : (elimVar d x s).remaining.length ≤ s.remaining.length := by
  by_cases hx : x ∈ s.remaining
  · simp only [elimVar, hx, ↓reduceIte]
    split_ifs <;> exact List.length_filter_le _ _
  · simp [elimVar, hx]

/-- One elimination step preserves the scope-length envelope `max S W` whenever its joint scope has
at most `W` variables. -/
theorem scope_length_elimVar_le [Semiring R] [DecidableEq V] (d : ℕ) (x : V) (s : ElimState R V)
    {S W : ℕ} (hs : ∀ f ∈ s.live, f.scope.length ≤ max S W)
    (hstep : (stepStats d x s).jointScopeVars ≤ W) :
    ∀ f ∈ (elimVar d x s).live, f.scope.length ≤ max S W :=
  elimVar_forall_le d x s (·.scope.length ≤ max S W) hs fun hx hb =>
    le_trans (List.length_filter_le _ _)
      (le_trans (by simpa [stepStats, hx, hb] using hstep) (le_max_right S W))

private theorem stepStats_liveEntriesAfter [Semiring R] [DecidableEq V] (d : ℕ) (x : V)
    (s : ElimState R V) :
    (stepStats d x s).liveEntriesAfter = liveEntries (elimVar d x s).live := by
  simp only [stepStats]; split_ifs <;> rfl

/-- Peak live-table entry count across `order` is bounded strictly by `init.live.length` times the
maximum of initial single-table sizes and the maximum output table size `d ^ maxOutScopeLen`. -/
theorem peakLiveEntries_le [Semiring R] [DecidableEq V] {d : ℕ} (hd : 0 < d)
    (order : List V) (init : ElimState R V) :
    peakLiveEntries d order init ≤
      init.live.length * max (maxTableEntries init.live) (d ^ maxOutScopeLen d order init) := by
  let E := maxTableEntries init.live
  let W := maxOutScopeLen d order init
  let B := max E (d ^ W)
  let M := init.live.length
  have hgen : ∀ (ord : List V) (s : ElimState R V) (acc : ℕ),
      acc ≤ M * B → s.live.length ≤ M → (∀ f ∈ s.live, f.entries.size ≤ B) →
      (∀ st ∈ traceOrder d ord s, st.outScopeVars ≤ W) →
      ((traceOrder d ord s).map ElimStepStats.liveEntriesAfter).foldl max acc ≤ M * B := by
    intro ord; induction ord with
    | nil => intro s acc hacc _ _ _; simpa [traceOrder] using hacc
    | cons x xs ih =>
        intro s acc hacc hlen hs hW
        have hs' : ∀ f ∈ (elimVar d x s).live, f.entries.size ≤ B :=
          elimVar_forall_le d x s (·.entries.size ≤ B) hs fun hx hb => by
            have hout : (bucketOutScope x (s.live.filter fun f => decide (x ∈ f.scope))).length ≤
                W := by
              simpa [stepStats, hx, hb] using hW (stepStats d x s) (by simp [traceOrder])
            simp only [elimBucketTable, Array.size_ofFn]
            exact (Nat.pow_le_pow_right hd hout).trans (le_max_right _ _)
        have hlen' : (elimVar d x s).live.length ≤ M := le_trans (length_elimVar_live_le d x s) hlen
        have hlive_after : (stepStats d x s).liveEntriesAfter ≤ M * B := by
          rw [stepStats_liveEntriesAfter]
          exact le_trans (list_sum_map_le _ _ hs') (Nat.mul_le_mul_right B hlen')
        simp only [traceOrder, List.map_cons, List.foldl_cons]
        exact ih (elimVar d x s) (max acc (stepStats d x s).liveEntriesAfter)
          (max_le hacc hlive_after) hlen' hs' fun st hst => hW st (by simp [traceOrder, hst])
  have hinit : ∀ f ∈ init.live, f.entries.size ≤ B := fun f hf =>
    le_trans (each_mem_le_maxTableEntries f hf) (le_max_left E (d ^ W))
  exact hgen order init (liveEntries init.live) (list_sum_map_le _ _ hinit) le_rfl hinit
    fun st hst => mem_traceOrder_out_le d order init hst

/-- At every prefix `order.take k`, live-table entry count is bounded by `peakLiveEntries`. -/
theorem liveEntries_eliminateOrder_take_le [Semiring R] [DecidableEq V] (d : ℕ)
    (order : List V) (init : ElimState R V) (k : ℕ) :
    liveEntries (eliminateOrder d (order.take k) init).live ≤ peakLiveEntries d order init := by
  rw [peakLiveEntries]
  suffices h : ∀ (ord : List V) (s : ElimState R V) (acc k : ℕ), liveEntries s.live ≤ acc →
      liveEntries (eliminateOrder d (ord.take k) s).live ≤
        ((traceOrder d ord s).map ElimStepStats.liveEntriesAfter).foldl max acc from
    h order init (liveEntries init.live) k le_rfl
  intro ord; induction ord with
  | nil => intro s acc k hacc; simpa [eliminateOrder, traceOrder] using hacc
  | cons x xs ih =>
      intro s acc k hacc; cases k with
      | zero =>
          simp only [List.take_zero, eliminateOrder, traceOrder, List.map_cons, List.foldl_cons]
          exact le_trans hacc (le_trans (le_max_left _ _) (List.le_foldl_max_self _ _))
      | succ k' =>
          simp only [List.take_succ_cons, eliminateOrder, traceOrder, List.map_cons,
            List.foldl_cons]
          exact ih (elimVar d x s) (max acc (stepStats d x s).liveEntriesAfter) k'
            (by rw [stepStats_liveEntriesAfter]; exact le_max_right _ _)

end IntermediateScopeBounds

end Cslib.Algorithms.Lean.CSP
