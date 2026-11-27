/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Algorithms.Lean.Query.Bounds
public import Mathlib.Data.Nat.Log

/-!
# Binary Search in the Threshold-Probe Query Model

`Cslib.Algorithms.Lean.lowerBound` finds, by bisection, the first index of `[lo, hi)` at which a
Boolean predicate `t : ℕ → Bool` fails, assuming `t` holds on an initial segment of `[lo, hi)` and
fails on the rest. `Cslib.Query.lowerBoundBy` expresses bisection over any query signature
`Q : Type → Type` in `FreeM Q ℕ` (`Cslib.Algorithms.Lean.Query.FreeM`), and
`Cslib.Query.lowerBoundQ` specializes it to `Cslib.Query.ProbeQuery`, where pure index arithmetic is
uncharged and oracle probes enter only through `FreeM.lift`.

## Main definitions

* `Cslib.Algorithms.Lean.lowerBound`: pure bisection on `[lo, hi)`.
* `Cslib.Query.ProbeQuery`: threshold-probe query signature (`probe (m : ℕ) : ProbeQuery Bool`).
* `Cslib.Query.ProbeQuery.ask`, `Cslib.Query.ProbeQuery.oracleOf`: single-probe helper and oracle
  constructor from `ℕ → Bool`.
* `Cslib.Query.lowerBoundBy`, `Cslib.Query.lowerBoundQ`: bisection on `[lo, hi)` in `FreeM Q ℕ` and
  `FreeM ProbeQuery ℕ`.

## Main results

* `Cslib.Algorithms.Lean.lowerBound_bounds`: `lo ≤ lowerBound t lo hi ≤ max lo hi` for every `t`.
* `Cslib.Algorithms.Lean.lowerBound_spec`: if `t` is antitone on `[lo, hi)`, the result `k`
  satisfies `lo ≤ k ≤ max lo hi`, `t` holds on `[lo, k)` and fails on `[k, hi)`.
* `Cslib.Query.eval_lowerBoundBy`, `Cslib.Query.eval_lowerBoundQ`: `FreeM.eval` agrees with pure
  `lowerBound`.
* `Cslib.Query.cost_lowerBoundBy_le`, `Cslib.Query.cost_lowerBoundQ_le`: if every probe in
  `[lo, hi)` has cost at most `c`, `FreeM.cost` is at most `c * (Nat.log 2 (hi - lo) + 1)` (`0` when
  `hi ≤ lo`).
* `Cslib.Query.countQueries_lowerBoundBy_le`, `Cslib.Query.countQueries_lowerBoundQ_le`,
  `Cslib.Query.upperBound_lowerBoundQ`: bisection makes at most `Nat.log 2 (hi - lo) + 1` queries
  (`0` when `hi ≤ lo`).
-/

public section

namespace Cslib.Algorithms.Lean

/-- Pure bisection for the boundary of a Boolean test on `[lo, hi)`: probe the midpoint
`m = (lo + hi) / 2` and continue on `[m + 1, hi)` if `t m` holds and on `[lo, m)` otherwise.
When `t` holds on an initial segment of `[lo, hi)`, the result is the first index where it fails
(`hi` if none, and `lo` when `hi ≤ lo`). -/
@[expose] def lowerBound (t : ℕ → Bool) (lo hi : ℕ) : ℕ :=
  if _ : lo < hi then
    if t ((lo + hi) / 2) then
      lowerBound t ((lo + hi) / 2 + 1) hi
    else
      lowerBound t lo ((lo + hi) / 2)
  else
    lo
termination_by hi - lo
decreasing_by all_goals omega

/-- On an empty interval (`hi ≤ lo`), `lowerBound` returns `lo`. -/
theorem lowerBound_of_le (t : ℕ → Bool) {lo hi : ℕ} (hle : hi ≤ lo) :
    lowerBound t lo hi = lo := by
  rw [lowerBound, dite_eq_right (Nat.not_lt.mpr hle)]

/-- Unconditional range bounds: for any test `t`, `lowerBound t lo hi` lies in `[lo, max lo hi]`. -/
theorem lowerBound_bounds (t : ℕ → Bool) (lo hi : ℕ) :
    lo ≤ lowerBound t lo hi ∧ lowerBound t lo hi ≤ max lo hi := by
  fun_induction lowerBound t lo hi with
  | case1 lo hi hlt _ ihR => exact ⟨by omega, by omega⟩
  | case2 lo hi hlt _ ihL => exact ⟨ihL.1, by omega⟩
  | case3 => exact ⟨le_refl _, le_max_left _ _⟩

/-- Correctness of `lowerBound`: if `t` is antitone on `[lo, hi)` (once it fails, it keeps
failing), then the result `k` lies in `[lo, max lo hi]`, `t` holds on `[lo, k)` and fails on
`[k, hi)`. -/
theorem lowerBound_spec (t : ℕ → Bool) {lo hi : ℕ}
    (hmono : ∀ m m', lo ≤ m → m ≤ m' → m' < hi → t m' = true → t m = true) :
    lo ≤ lowerBound t lo hi ∧ lowerBound t lo hi ≤ max lo hi ∧
      (∀ m, lo ≤ m → m < lowerBound t lo hi → t m = true) ∧
      (∀ m, lowerBound t lo hi ≤ m → m < hi → t m = false) := by
  fun_induction lowerBound t lo hi with
  | case1 lo hi hlt htm ihR =>
    have hmh : (lo + hi) / 2 < hi := by omega
    obtain ⟨h1, h2, h3, h4⟩ :=
      ihR fun m m' hm hmm' hm' => hmono m m' (by omega) hmm' hm'
    refine ⟨by omega, by omega, fun m hm hmk => ?_, h4⟩
    rcases Nat.lt_or_ge m ((lo + hi) / 2 + 1) with hlt' | hge
    · exact hmono m ((lo + hi) / 2) hm (by omega) hmh htm
    · exact h3 m hge hmk
  | case2 lo hi hlt htm ihL =>
    have hlm : lo ≤ (lo + hi) / 2 := by omega
    obtain ⟨h1, h2, h3, h4⟩ :=
      ihL fun m m' hm hmm' hm' => hmono m m' hm hmm' (by omega)
    refine ⟨h1, by omega, h3, fun m hm hmhi => ?_⟩
    rcases Nat.lt_or_ge m ((lo + hi) / 2) with hlt' | hge
    · exact h4 m hm hlt'
    · exact Bool.eq_false_iff.mpr fun hm_true =>
        htm (hmono ((lo + hi) / 2) m hlm hge hmhi hm_true)
  | case3 =>
    exact ⟨le_refl _, le_max_left _ _, fun _ _ _ => by omega, fun _ _ _ => by omega⟩

end Cslib.Algorithms.Lean

namespace Cslib.Query

open scoped Cardinal
open Cslib.Algorithms.Lean (lowerBound lowerBound_bounds lowerBound_spec)

/-- Threshold-probe query signature: `ProbeQuery.probe m` tests a predicate at `m : ℕ`, returning
`Bool`. -/
inductive ProbeQuery : Type → Type where
  /-- Probe the Boolean predicate at index `m`. -/
  | probe (m : ℕ) : ProbeQuery Bool

/-- Lift `ProbeQuery.probe m` into `FreeM ProbeQuery Bool`. -/
abbrev ProbeQuery.ask (m : ℕ) : FreeM ProbeQuery Bool :=
  FreeM.lift (.probe m)

@[simp] theorem ProbeQuery.eval_ask (oracle : {ι : Type} → ProbeQuery ι → ι) (m : ℕ) :
    (ProbeQuery.ask m).eval oracle = oracle (.probe m) := rfl

/-- Build a `ProbeQuery` oracle from a pure predicate `ℕ → Bool`. -/
@[expose] def ProbeQuery.oracleOf (t : ℕ → Bool) :
    {ι : Type} → ProbeQuery ι → ι
  | _, .probe m => t m

@[simp] theorem ProbeQuery.oracleOf_probe (t : ℕ → Bool) (m : ℕ) :
    ProbeQuery.oracleOf t (.probe m) = t m := rfl

/-- Every `ProbeQuery ι` has response type `ι = Bool`, of cardinality `2`. -/
theorem ProbeQuery.cardResponse_eq_two : ∀ {ι : Type}, ProbeQuery ι → #ι = 2
  | _, .probe _ => Cardinal.mk_bool

theorem ProbeQuery.cardResponse_le_two {ι : Type} (op : ProbeQuery ι) : #ι ≤ 2 :=
  (ProbeQuery.cardResponse_eq_two op).le

/-- Query-monad bisection on `[lo, hi)` parameterized by a probe sub-program
`ask : ℕ → FreeM Q Bool` for any query signature `Q : Type → Type`. -/
@[expose] def lowerBoundBy {Q : Type → Type} (ask : ℕ → FreeM Q Bool) (lo hi : ℕ) :
    FreeM Q ℕ :=
  if _ : lo < hi then do
    let b ← ask ((lo + hi) / 2)
    if b then lowerBoundBy ask ((lo + hi) / 2 + 1) hi else lowerBoundBy ask lo ((lo + hi) / 2)
  else
    pure lo
termination_by hi - lo
decreasing_by all_goals omega

/-- Evaluating `lowerBoundBy ask lo hi` against `oracle` computes pure `lowerBound` for the induced
Boolean predicate `fun m => (ask m).eval oracle`. -/
@[simp] theorem eval_lowerBoundBy {Q : Type → Type} (oracle : {ι : Type} → Q ι → ι)
    (ask : ℕ → FreeM Q Bool) (lo hi : ℕ) :
    (lowerBoundBy ask lo hi).eval oracle =
      lowerBound (fun m => (ask m).eval oracle) lo hi := by
  fun_induction lowerBoundBy ask lo hi with
  | case1 lo hi hlt ihR ihL =>
    rw [lowerBound, dite_eq_left hlt]
    simp only [FreeM.eval_bind]
    by_cases hb : (ask ((lo + hi) / 2)).eval oracle = true
    · simp only [hb, ↓reduceIte, ihR]
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, ihL]
  | case2 lo hi hle =>
    rw [lowerBound, dite_eq_right hle]
    rfl

private theorem log_two_mul_add_one_le {k k' : ℕ} (hpos : 0 < k') (h2 : 2 * k' ≤ k) :
    Nat.log 2 (2 * k') + 1 ≤ Nat.log 2 (2 * k) := by
  rw [← Nat.log_mul_base (by decide) (by omega : 2 * k' ≠ 0)]
  exact Nat.log_mono_right (by omega)

/-- On an empty interval (`hi ≤ lo`), `lowerBoundBy` incurs zero query cost. -/
theorem cost_lowerBoundBy_of_le {Q : Type → Type} {T : Type} [AddMonoid T]
    (oracle : {ι : Type} → Q ι → ι) (weight : {ι : Type} → Q ι → T)
    (ask : ℕ → FreeM Q Bool) {lo hi : ℕ} (hle : hi ≤ lo) :
    (lowerBoundBy ask lo hi).cost oracle weight = 0 := by
  rw [lowerBoundBy, dite_eq_right (Nat.not_lt.mpr hle)]
  rfl

/-- On an empty interval (`hi ≤ lo`), `lowerBoundBy` makes zero queries. -/
theorem countQueries_lowerBoundBy_of_le {Q : Type → Type}
    (oracle : {ι : Type} → Q ι → ι) (ask : ℕ → FreeM Q Bool) {lo hi : ℕ} (hle : hi ≤ lo) :
    (lowerBoundBy ask lo hi).countQueries oracle = 0 :=
  cost_lowerBoundBy_of_le oracle (fun _ => 1) ask hle

/-- **Weighted query-cost bound for `lowerBoundBy`.** If every probe sub-program `ask m` for
`m ∈ [lo, hi)` has weighted cost at most `c`, then `lowerBoundBy ask lo hi` has total query cost at
most `c * (Nat.log 2 (hi - lo) + 1)`. -/
theorem cost_lowerBoundBy_le {Q : Type → Type} (oracle : {ι : Type} → Q ι → ι)
    (weight : {ι : Type} → Q ι → ℕ) (ask : ℕ → FreeM Q Bool) {c lo hi : ℕ}
    (hc : ∀ m, lo ≤ m → m < hi → (ask m).cost oracle weight ≤ c) :
    (lowerBoundBy ask lo hi).cost oracle weight ≤ c * (Nat.log 2 (hi - lo) + 1) := by
  suffices h : (lowerBoundBy ask lo hi).cost oracle weight ≤ c * Nat.log 2 (2 * (hi - lo)) by
    rcases Nat.eq_zero_or_pos (hi - lo) with h0 | hpos
    · simp only [h0, Nat.mul_zero, Nat.log_zero_right] at h; omega
    · rwa [Nat.mul_comm 2, Nat.log_mul_base (by decide) hpos.ne'] at h
  fun_induction lowerBoundBy ask lo hi with
  | case1 lo hi hlt ihR ihL =>
    simp only [FreeM.cost_bind]
    set mid := (lo + hi) / 2
    have hmid_cost : (ask mid).cost oracle weight ≤ c := hc mid (by omega) (by omega)
    have hlog : 1 ≤ Nat.log 2 (2 * (hi - lo)) := by
      rw [Nat.mul_comm 2, Nat.log_mul_base (by decide) (by omega)]; omega
    have hstep : ∀ k', 2 * k' ≤ hi - lo →
        c + c * Nat.log 2 (2 * k') ≤ c * Nat.log 2 (2 * (hi - lo)) := by
      intro k' h2
      rcases Nat.eq_zero_or_pos k' with rfl | hpos
      · simp only [Nat.mul_zero, Nat.log_zero_right, add_zero]
        exact Nat.le_mul_of_pos_right c hlog
      · have hmul := Nat.mul_le_mul_left c (log_two_mul_add_one_le hpos h2)
        rw [Nat.mul_add, Nat.mul_one] at hmul
        omega
    by_cases hb : (ask mid).eval oracle = true
    · simp only [hb, ↓reduceIte]
      have hrec := ihR fun m hm1 hm2 => hc m (by omega) hm2
      have hbound := hstep (hi - (mid + 1)) (by omega)
      omega
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      have hrec := ihL fun m hm1 hm2 => hc m hm1 (by omega)
      have hbound := hstep (mid - lo) (by omega)
      omega
  | case2 =>
    simp only [FreeM.cost_pure, Nat.zero_le]

/-- **Query-count bound for `lowerBoundBy`.** If every probe sub-program `ask m` for `m ∈ [lo, hi)`
makes at most `c` queries, then `lowerBoundBy ask lo hi` makes at most
`c * (Nat.log 2 (hi - lo) + 1)` queries. -/
theorem countQueries_lowerBoundBy_le {Q : Type → Type} (oracle : {ι : Type} → Q ι → ι)
    (ask : ℕ → FreeM Q Bool) {c lo hi : ℕ}
    (hc : ∀ m, lo ≤ m → m < hi → (ask m).countQueries oracle ≤ c) :
    (lowerBoundBy ask lo hi).countQueries oracle ≤ c * (Nat.log 2 (hi - lo) + 1) :=
  cost_lowerBoundBy_le oracle (fun _ => 1) ask hc

/-- Query-monad bisection on `[lo, hi)` over `ProbeQuery`. -/
@[expose] def lowerBoundQ (lo hi : ℕ) : FreeM ProbeQuery ℕ :=
  lowerBoundBy ProbeQuery.ask lo hi

/-- Evaluating `lowerBoundQ lo hi` against `oracle` computes `lowerBound`. -/
@[simp] theorem eval_lowerBoundQ (oracle : {ι : Type} → ProbeQuery ι → ι) (lo hi : ℕ) :
    (lowerBoundQ lo hi).eval oracle = lowerBound (fun m => oracle (.probe m)) lo hi :=
  eval_lowerBoundBy oracle ProbeQuery.ask lo hi

/-- On an empty interval (`hi ≤ lo`), `lowerBoundQ` incurs zero cost. -/
theorem cost_lowerBoundQ_of_le {T : Type} [AddMonoid T]
    (oracle : {ι : Type} → ProbeQuery ι → ι) (weight : {ι : Type} → ProbeQuery ι → T)
    {lo hi : ℕ} (hle : hi ≤ lo) :
    (lowerBoundQ lo hi).cost oracle weight = 0 :=
  cost_lowerBoundBy_of_le oracle weight ProbeQuery.ask hle

/-- On an empty interval (`hi ≤ lo`), `lowerBoundQ` makes zero queries. -/
theorem countQueries_lowerBoundQ_of_le (oracle : {ι : Type} → ProbeQuery ι → ι)
    {lo hi : ℕ} (hle : hi ≤ lo) :
    (lowerBoundQ lo hi).countQueries oracle = 0 :=
  countQueries_lowerBoundBy_of_le oracle ProbeQuery.ask hle

/-- **Weighted query-cost bound for `lowerBoundQ`.** If every probe at `m ∈ [lo, hi)` has weight at
most `c`, then `lowerBoundQ lo hi` has total query cost at most `c * (Nat.log 2 (hi - lo) + 1)`. -/
theorem cost_lowerBoundQ_le (oracle : {ι : Type} → ProbeQuery ι → ι)
    (weight : {ι : Type} → ProbeQuery ι → ℕ) {c lo hi : ℕ}
    (hc : ∀ m, lo ≤ m → m < hi → weight (.probe m) ≤ c) :
    (lowerBoundQ lo hi).cost oracle weight ≤ c * (Nat.log 2 (hi - lo) + 1) :=
  cost_lowerBoundBy_le oracle weight ProbeQuery.ask fun m h1 h2 => by
    simpa only [FreeM.cost_lift] using hc m h1 h2

/-- **Query-count bound for `lowerBoundQ`.** `lowerBoundQ lo hi` makes at most
`Nat.log 2 (hi - lo) + 1` threshold probes against any oracle. -/
theorem countQueries_lowerBoundQ_le (oracle : {ι : Type} → ProbeQuery ι → ι) (lo hi : ℕ) :
    (lowerBoundQ lo hi).countQueries oracle ≤ Nat.log 2 (hi - lo) + 1 := by
  simpa only [FreeM.countQueries_eq_cost_one, one_mul] using
    cost_lowerBoundQ_le oracle (fun _ => 1) (c := 1) fun _ _ _ => le_rfl

/-- `Cslib.Query.UpperBound` formulation of the `⌊log₂ n⌋ + 1` probe bound for `lowerBoundQ`. -/
theorem upperBound_lowerBoundQ :
    UpperBound (fun p : ℕ × ℕ => lowerBoundQ p.1 p.2) (fun p => p.2 - p.1)
      (fun n => Nat.log 2 n + 1) :=
  UpperBound.of_pointwise
    (fun _ _ h => Nat.add_le_add_right (Nat.log_mono_right h) 1)
    fun oracle p => countQueries_lowerBoundQ_le oracle p.1 p.2

end Cslib.Query
