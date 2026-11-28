/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.Select.Defs
public import CslibFrontier.Algorithms.Lean.Query.SumQuery
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Log
import CslibFrontier.Algorithms.Lean.Query.Select.Correctness
import CslibFrontier.Algorithms.Lean.Query.Select.Cost
import CslibFrontier.Algorithms.Lean.Query.FreeM.LiftM
import CslibFrontier.Algorithms.Lean.Query.FreeM.CostHom
import CslibFrontier.Algorithms.Lean.Query.FreeM.Tabulate
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Quota selection with admissibility tests

Items `xs : List α` are partitioned into groups by `g : α → γ`. Each item has a hidden weight
`w : α → W`, injective into a linear order, and is either admissible or not, for a hidden
predicate `adm`. The representative of a group with an admissible item is its lightest admissible
item (`Cslib.Query.IsGroupRepresentative`). Quota selection finds the `k` lightest representatives,
or all of them if there are fewer than `k`, learning weights only by comparisons and admissibility
only by tests. This is the selection step of the batch procedure in the deterministic
linear-comparison minimum spanning forest algorithm of [KhannaPuttermanSong2026], stated there as
Lemma 3.3 (§3.2, p. 16), and a step in the proof of their Theorem 4.1, tracked in #8325.

Programs are `FreeM (CmpTestQuery α)` values, where `CmpTestQuery α` is the sum
(`Cslib.Query.SumQuery`) of comparison queries `LEQuery α` and test queries `TestQuery α`. The
oracle `CmpTestQuery.oracleOf w adm` answers both. The three counts are separate:
comparisons are `SumQuery.countInl`, and tests answered `true` and `false` are
`FreeM.cost oracle (CmpTestQuery.passWeight oracle)` and `FreeM.cost oracle
(CmpTestQuery.failWeight oracle)`. When a failed test of `a` costs `c a`, the failed tests cost
`FreeM.cost oracle (CmpTestQuery.failCost oracle c)`.

The algorithm (`Cslib.Query.quotaSelect`) follows the proof of Lemma 3.3. It splits the items at
the median with the deterministic selection `Cslib.Query.select`. It scans the lower half,
testing items until `k` groups have passed. If they have, it recurses on the lower half.
Otherwise it runs a quota-one search for each passing group on that group's items in the lower
half, and recurses with the remaining quota on the upper half, without the passing groups.

## Source mapping

[KhannaPuttermanSong2026], §3.2, Lemma 3.3, p. 16: "Given an integer `k ≥ 0`, we can select the
`k` lightest representatives, or all representatives if there are fewer than `k`, using
`O(k log(m + 1))` successful admissibility tests and `O(m)` additional weight comparisons."

* Selection: `Cslib.Query.mem_selected_quotaSelect` (an item is selected iff it is a
  representative with fewer than `k` lighter representatives), with
  `Cslib.Query.length_selected_quotaSelect` (`min k` the number of groups with an admissible item)
  and `Cslib.Query.nodup_selected_quotaSelect`. These assume an injective `w` and a
  duplicate-free input.
* Comparisons: `Cslib.Query.countInl_quotaSelect_le`, at most `204 m` for every oracle.
* Successful tests: `Cslib.Query.cost_passWeight_quotaSelect_le`, at most `k (⌈log₂ m⌉ + 1)` for
  every oracle.
* Failed tests, which the source charges separately (p. 15: a failure is stored and reused):
  `Cslib.Query.cost_failCost_quotaSelect` (exactly one failed test per reported failed item, and
  no other, for every oracle, with any cost `c a` per failed test of `a`),
  `Cslib.Query.cost_failWeight_quotaSelect` (its unit-cost case),
  `Cslib.Query.failed_quotaSelect` (the reported items are distinct and inadmissible) and
  `Cslib.Query.cost_failWeight_quotaSelect_le` (at most the number of inadmissible items).
* The property the proof of Lemma 3.2 (p. 15) uses: `Cslib.Query.quotaSelect_guarantee`. The
  source argues its second half by saying that an untested edge could be made admissible without
  changing the run. Here it is proved directly by induction along the recursion: in the branch
  where fewer than `k` groups pass the scan, every untested item of the lower half is in a passing
  group.

Deviations from the proof of Lemma 3.3, none affecting the statement:

* The base case is a list of at most one item, rather than `m ≤ k`.
* The scan runs over the lower half from its end to its front.
* A failed item is not stored and looked up: it is dropped from every list passed to a recursive
  call, so it is never tested again.
* Groups are given by an arbitrary map `g`, and the input is a list; the batch procedure groups
  the edges at a vertex by their other endpoint.
-/

public section

namespace Cslib.Query

/-! ## Test queries -/

/-- Test query: asks whether the item `a` passes a hidden test, returning a `Bool`.

It has the same shape as `Cslib.Query.ProbeQuery` (a Boolean probe at an index `m : ℕ`, so that
`TestQuery ℕ` is `ProbeQuery`) and `Cslib.Query.IndepQuery` (a Boolean test of a finite set).
Neither fits directly: the tested objects here are items of an arbitrary type `α`. -/
inductive TestQuery (α : Type) : Type → Type where
  /-- Ask whether `a` passes the test. -/
  | test (a : α) : TestQuery α Bool

/-- Build a `TestQuery α` oracle from a Boolean predicate. -/
@[expose] def TestQuery.oracleOf {α : Type} (t : α → Bool) :
    {ι : Type} → TestQuery α ι → ι
  | _, .test a => t a

@[simp] theorem TestQuery.oracleOf_test {α : Type} (t : α → Bool) (a : α) :
    TestQuery.oracleOf t (.test a) = t a := rfl

/-- Comparison queries and test queries on the same items. -/
abbrev CmpTestQuery (α : Type) : Type → Type := SumQuery (LEQuery α) (TestQuery α)

namespace CmpTestQuery

variable {α W : Type}

/-- The oracle answering a comparison `a ≤ b` by `w a ≤ w b` and a test of `a` by `adm a`. -/
@[expose] def oracleOf [LinearOrder W] (w : α → W) (adm : α → Prop) [DecidablePred adm] :
    {ι : Type} → CmpTestQuery α ι → ι :=
  SumQuery.combine (LEQuery.oracleOf fun a b => decide (w a ≤ w b))
    (TestQuery.oracleOf fun a => decide (adm a))

/-- Unit weight on the tests that `oracle` answers `true`. -/
@[expose] def passWeight (oracle : {ι : Type} → CmpTestQuery α ι → ι) :
    {ι : Type} → CmpTestQuery α ι → ℕ
  | _, .inl _ => 0
  | _, .inr (.test a) => if oracle (.inr (.test a)) then 1 else 0

/-- Unit weight on the tests that `oracle` answers `false`. -/
@[expose] def failWeight (oracle : {ι : Type} → CmpTestQuery α ι → ι) :
    {ι : Type} → CmpTestQuery α ι → ℕ
  | _, .inl _ => 0
  | _, .inr (.test a) => if oracle (.inr (.test a)) then 0 else 1

/-- Weight `c a` on a test of `a` that `oracle` answers `false`: the cost of a failed test may
depend on the item. -/
@[expose] def failCost (oracle : {ι : Type} → CmpTestQuery α ι → ι) (c : α → ℕ) :
    {ι : Type} → CmpTestQuery α ι → ℕ
  | _, .inl _ => 0
  | _, .inr (.test a) => if oracle (.inr (.test a)) then 0 else c a

end CmpTestQuery

/-! ## The program -/

/-- The result of quota selection: the selected representatives and the items whose test
failed. -/
structure QuotaSelection (α : Type) where
  /-- The selected representatives. -/
  selected : List α
  /-- The items whose admissibility test failed. -/
  failed : List α

variable {α γ : Type} [DecidableEq α] [DecidableEq γ]

/-- Split `xs` around its element `p` of rank `⌊m / 2⌋`, for `m = xs.length`, found by
`Cslib.Query.select`: the elements below `p`, and the others (`p` and the elements above it). -/
private def medianSplit (xs : List α) : FreeM (LEQuery α) (Option (List α × List α)) := do
  match ← select (xs.length / 2) xs with
  | none => return none
  | some p =>
    let (L, E, G) ← partition3 p xs
    return some (L, E ++ G)

/-- Scan `xs` from its last element to its first, testing items until `k` groups have passed a
test. Items of a group that has already passed are skipped. Returns the groups that passed and
the items that failed. -/
private def scanTests (g : α → γ) (k : ℕ) :
    List α → FreeM (CmpTestQuery α) (List γ × List α)
  | [] => return ([], [])
  | x :: xs => do
    let (P, F) ← scanTests g k xs
    if k ≤ P.length ∨ g x ∈ P then return (P, F)
    else if ← SumQuery.liftInr (.test x) then return (g x :: P, F)
    else return (P, x :: F)

/-- **Quota selection with admissibility tests** ([KhannaPuttermanSong2026], §3.2, proof of
Lemma 3.3, p. 16). Among the groups `g x` of the items `xs`, each group with an admissible item
has a representative, its lightest admissible item; `quotaSelect g k xs` selects the `k`
lightest representatives (all of them if there are fewer than `k`).

With `k ≥ 1` and at least two items, it splits `xs` at the median into a lower half `L` and an
upper half `H`, and scans `L`, testing items until `k` groups have passed. If `k` groups pass, all
`k` desired representatives lie in `L`, and it recurses on `L`. Otherwise the groups that passed
are exactly the groups with an admissible item in `L`; it finds the representative of each with a
quota-one search on its items in `L`, and recurses with the remaining quota on the items of `H`
in the other groups. Items whose test failed are dropped before recursing, so no item fails
twice.

The run returns nothing if the median split does not have the sizes `⌊m / 2⌋` and `⌈m / 2⌉`.
This never happens for comparisons by an injective weight on a list without duplicates; the
check makes the recursion well founded and the query bounds hold for every oracle. -/
def quotaSelect (g : α → γ) (k : ℕ) (xs : List α) :
    FreeM (CmpTestQuery α) (QuotaSelection α) :=
  if k = 0 then return ⟨[], []⟩ else
  match _hxs : xs with
  | [] => return ⟨[], []⟩
  | [x] => do
    if ← SumQuery.liftInr (.test x) then return ⟨[x], []⟩ else return ⟨[], [x]⟩
  | _ :: _ :: _ => do
    let some (L, H) ← (medianSplit xs).liftM SumQuery.liftInl | return ⟨[], []⟩
    if L.length ≤ xs.length / 2 ∧ H.length ≤ xs.length - xs.length / 2 then
      let (P, F) ← scanTests g k L
      let L' := L.filter (· ∉ F)
      if k ≤ P.length then
        let r ← quotaSelect g k L'
        return ⟨r.selected, F ++ r.failed⟩
      else
        let rs ← P.mapM fun c => quotaSelect g 1 (L'.filter (g · = c))
        let r ← quotaSelect g (k - P.length) (H.filter (g · ∉ P))
        return ⟨rs.flatMap (·.selected) ++ r.selected, F ++ rs.flatMap (·.failed) ++ r.failed⟩
    else return ⟨[], []⟩
termination_by xs.length
decreasing_by
  all_goals
    rw [← _hxs]
    have : 2 ≤ xs.length := by simp [_hxs]
    first
    | (apply Nat.lt_of_le_of_lt (List.length_filter_le _ _); omega)
    | (apply Nat.lt_of_le_of_lt ((List.length_filter_le _ _).trans (List.length_filter_le _ _))
       omega)

/-! ## The scan -/

omit [DecidableEq α] in
private theorem scanTests_spec (oracle : {ι : Type} → CmpTestQuery α ι → ι) (g : α → γ)
    (c : α → ℕ) (k : ℕ) (xs : List α) :
    SumQuery.countInl oracle (scanTests g k xs) = 0 ∧
    (scanTests g k xs).cost oracle (CmpTestQuery.passWeight oracle) =
      ((scanTests g k xs).eval oracle).1.length ∧
    (scanTests g k xs).cost oracle (CmpTestQuery.failCost oracle c) =
      (((scanTests g k xs).eval oracle).2.map c).sum ∧
    ((scanTests g k xs).eval oracle).1.length ≤ k ∧ ((scanTests g k xs).eval oracle).1.Nodup ∧
    ((scanTests g k xs).eval oracle).2.Sublist xs ∧
    (∀ c ∈ ((scanTests g k xs).eval oracle).1,
      ∃ x ∈ xs, oracle (.inr (.test x)) = true ∧ g x = c) ∧
    (∀ x ∈ ((scanTests g k xs).eval oracle).2, oracle (.inr (.test x)) = false) ∧
    (((scanTests g k xs).eval oracle).1.length < k → ∀ x ∈ xs,
      g x ∈ ((scanTests g k xs).eval oracle).1 ∨ x ∈ ((scanTests g k xs).eval oracle).2) := by
  induction xs with
  | nil => simp [scanTests, SumQuery.countInl]
  | cons x xs ih =>
    rcases h : (scanTests g k xs).eval oracle with ⟨P, F⟩
    rw [h] at ih
    obtain ⟨ih1, ih2, ih3, ih4, ih5, ih6, ih7, ih8, ih9⟩ := ih
    dsimp only at ih2 ih3 ih4 ih5 ih6 ih7 ih8 ih9
    have mem7 : ∀ c ∈ P, ∃ z ∈ x :: xs, oracle (.inr (.test z)) = true ∧ g z = c :=
      fun c hc => by
        obtain ⟨z, hz, h1, h2⟩ := ih7 c hc
        exact ⟨z, List.mem_cons_of_mem _ hz, h1, h2⟩
    by_cases hstop : k ≤ P.length ∨ g x ∈ P
    · simp only [scanTests, SumQuery.countInl_bind, FreeM.cost_bind, FreeM.eval_bind, h, hstop,
        ite_true, SumQuery.countInl_pure, FreeM.cost_pure, FreeM.eval_pure, add_zero, ih1, ih2,
        ih3]
      refine ⟨trivial, trivial, trivial, ih4, ih5, ih6.cons x, mem7, ih8, fun hlt y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · rcases hstop with h' | h'
        · omega
        · exact Or.inl h'
      · exact ih9 hlt y hy
    · have hk : P.length < k := by omega
      have hxP : g x ∉ P := by tauto
      rcases hb : oracle (.inr (.test x)) with _ | _
      · simp only [scanTests, SumQuery.countInl_bind, FreeM.cost_bind, FreeM.eval_bind, h, hstop,
          ite_false, SumQuery.countInl_liftInr, FreeM.cost_lift, FreeM.eval_lift, hb,
          Bool.false_eq_true, SumQuery.countInl_pure, FreeM.cost_pure, FreeM.eval_pure, add_zero,
          ih1, ih2, ih3, CmpTestQuery.passWeight, CmpTestQuery.failCost,
          List.map_cons, List.sum_cons]
        refine ⟨trivial, trivial, Nat.add_comm _ _, ih4, ih5, ih6.cons_cons x, mem7, ?_,
          fun _ y hy => ?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hb
          · exact ih8 y hy
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact Or.inr List.mem_cons_self
          · exact (ih9 hk y hy).imp id (List.mem_cons_of_mem _)
      · simp only [scanTests, SumQuery.countInl_bind, FreeM.cost_bind, FreeM.eval_bind, h, hstop,
          ite_false, SumQuery.countInl_liftInr, FreeM.cost_lift, FreeM.eval_lift, hb,
          SumQuery.countInl_pure, FreeM.cost_pure, FreeM.eval_pure, add_zero, ite_true,
          ih1, ih2, ih3, CmpTestQuery.passWeight, CmpTestQuery.failCost, List.length_cons]
        refine ⟨trivial, trivial, trivial, by omega, List.nodup_cons.mpr ⟨hxP, ih5⟩, ih6.cons x,
          ?_, ih8,
          fun _ y hy => ?_⟩
        · intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact ⟨x, List.mem_cons_self, hb, rfl⟩
          · exact mem7 c hc
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact Or.inl List.mem_cons_self
          · rcases ih9 hk y hy with h' | h'
            · exact Or.inl (List.mem_cons_of_mem _ h')
            · exact Or.inr h'

/-! ## The median split -/

omit [DecidableEq α] in
private theorem medianSplit_countQueries_le (oracle : {ι : Type} → LEQuery α ι → ι)
    (xs : List α) : (medianSplit xs).countQueries oracle ≤ 34 * xs.length := by
  have h1 := select_countQueries_le oracle (xs.length / 2) xs
  simp only [medianSplit, FreeM.countQueries_bind]
  split
  · simp only [FreeM.countQueries_pure]
    omega
  · rename_i p _
    have h2 := partition3_countQueries_le oracle p xs
    simp only [FreeM.countQueries_bind, FreeM.countQueries_pure]
    omega

omit [DecidableEq α] in
/-- Against an oracle comparing by an injective weight, the median split of a nonempty list
without duplicates returns the `⌊m / 2⌋` elements below an element `p` of the list, and the
`m - ⌊m / 2⌋` elements at or above it. -/
private theorem eval_medianSplit {W : Type} [LinearOrder W] (w : α → W)
    (hw : Function.Injective w) (oracle : {ι : Type} → LEQuery α ι → ι)
    (horacle : ∀ a b, oracle (.le a b) = decide (w a ≤ w b)) {xs : List α} (hxs : xs.Nodup)
    (hne : xs ≠ []) :
    ∃ p L H, (medianSplit xs).eval oracle = some (L, H) ∧ L.length = xs.length / 2 ∧
      H.length = xs.length - xs.length / 2 ∧ (∀ x, x ∈ L ↔ x ∈ xs ∧ w x < w p) ∧
      (∀ x, x ∈ H ↔ x ∈ xs ∧ w p ≤ w x) ∧ L.Nodup ∧ H.Nodup := by
  let r : α → α → Prop := fun a b => w a ≤ w b
  have : Std.Total r := ⟨fun a b => le_total (w a) (w b)⟩
  have : IsTrans α r := ⟨fun _ _ _ => le_trans⟩
  have hlen : xs.length / 2 < xs.length := by
    have := List.length_pos_iff.mpr hne
    omega
  obtain ⟨p, hp, hpos⟩ := select_isOrderStatistic r oracle horacle hlen
  have hpart := eval_partition3_of_total r oracle horacle p xs
  set L := xs.filter (fun x => ¬ r p x) with hL
  set H := xs.filter (fun x => r x p ∧ r p x) ++ xs.filter (fun x => ¬ r x p) with hH
  have memL : ∀ x, x ∈ L ↔ x ∈ xs ∧ w x < w p := fun x => by
    simp [hL, r]
  have memH : ∀ x, x ∈ H ↔ x ∈ xs ∧ w p ≤ w x := fun x => by
    simp only [hH, List.mem_append, List.mem_filter, decide_eq_true_eq, r]
    constructor
    · rintro (⟨h, _, h'⟩ | ⟨h, h'⟩)
      · exact ⟨h, h'⟩
      · exact ⟨h, (lt_of_not_ge h').le⟩
    · rintro ⟨h, h'⟩
      by_cases h'' : w x ≤ w p
      · exact Or.inl ⟨h, h'', h'⟩
      · exact Or.inr ⟨h, h''⟩
  have nodupL : L.Nodup := hxs.filter _
  have nodupH : H.Nodup := by
    refine List.nodup_append.mpr ⟨hxs.filter _, hxs.filter _, ?_⟩
    intro a ha b hb hab
    subst hab
    simp only [List.mem_filter, decide_eq_true_eq, r] at ha hb
    exact hb.2 ha.2.1
  have hperm : (L ++ H).Perm xs := by
    refine (List.perm_ext_iff_of_nodup ?_ hxs).mpr fun x => ?_
    · refine List.nodup_append.mpr ⟨nodupL, nodupH, fun a ha b hb hab => ?_⟩
      subst hab
      exact absurd ((memH a).mp hb).2 (not_le.mpr ((memL a).mp ha).2)
    · rw [List.mem_append, memL, memH]
      constructor
      · rintro (h | h)
        · exact h.1
        · exact h.1
      · intro h
        rcases lt_or_ge (w x) (w p) with h' | h'
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr ⟨h, h'⟩
  have hsum : L.length + H.length = xs.length := by
    rw [← List.length_append, hperm.length_eq]
  have hle : L.length ≤ xs.length / 2 := by
    have := hpos.countP_lt_le
    rwa [List.countP_eq_length_filter] at this
  have hge : xs.length / 2 ≤ L.length := by
    have h1 := hpos.lt_countP_le
    rw [List.countP_eq_length_filter] at h1
    have hsub : xs.filter (fun x => r x p) ⊆ p :: L := by
      intro x hx
      simp only [List.mem_filter, decide_eq_true_eq, r] at hx
      rcases eq_or_lt_of_le hx.2 with h | h
      · exact List.mem_cons.mpr (Or.inl (hw h))
      · exact List.mem_cons_of_mem _ ((memL x).mpr ⟨hx.1, h⟩)
    have := ((hxs.filter _).subperm hsub).length_le
    simp only [List.length_cons] at this
    omega
  refine ⟨p, L, H, ?_, by omega, by omega, memL, memH, nodupL, nodupH⟩
  simp only [medianSplit, FreeM.eval_bind, hp, hpart, FreeM.eval_pure, hH]

/-! ## Query bounds -/

omit [DecidableEq α] in
private theorem eval_liftInl {β : Type} (oracle : {ι : Type} → CmpTestQuery α ι → ι)
    (p : FreeM (LEQuery α) β) :
    (p.liftM (SumQuery.liftInl (G := TestQuery α))).eval oracle =
      p.eval fun q => oracle (.inl q) := by
  rw [FreeM.eval_liftM]
  rfl

omit [DecidableEq α] in
private theorem cost_liftInl {β : Type} (oracle : {ι : Type} → CmpTestQuery α ι → ι)
    (wt : {ι : Type} → CmpTestQuery α ι → ℕ) (p : FreeM (LEQuery α) β) :
    (p.liftM (SumQuery.liftInl (G := TestQuery α))).cost oracle wt =
      p.cost (fun q => oracle (.inl q)) (fun q => wt (.inl q)) := by
  rw [FreeM.cost_liftM]
  simp only [SumQuery.liftInl, FreeM.eval_lift, FreeM.cost_lift]

private theorem clog_add_one_le {l m : ℕ} (hm : 2 ≤ m) (hl : l ≤ m - m / 2) :
    Nat.clog 2 l + 1 ≤ Nat.clog 2 m := by
  conv_rhs => rw [Nat.clog_of_two_le one_lt_two hm]
  exact Nat.add_le_add_right (Nat.clog_mono_right 2 (by omega)) 1

omit [DecidableEq α] in
private theorem sum_length_filter_le (g : α → γ) {P : List γ} (hP : P.Nodup) (l : List α) :
    (P.map fun c => (l.filter (g · = c)).length).sum ≤ l.length := by
  induction P generalizing l with
  | nil => simp
  | cons c P ih =>
    obtain ⟨hc, hP⟩ := List.nodup_cons.mp hP
    have h1 : (P.map fun c' => (l.filter (g · = c')).length) =
        P.map fun c' => ((l.filter (g · ≠ c)).filter (g · = c')).length := by
      refine List.map_congr_left fun c' hc' => ?_
      rw [List.filter_filter]
      congr 1
      refine List.filter_congr fun x _ => ?_
      by_cases hx : g x = c'
      · have hne : c' ≠ c := fun h => hc (h ▸ hc')
        simp [hx, hne]
      · simp [hx]
    have h2 := ih hP (l.filter (g · ≠ c))
    have h3 := List.length_eq_length_filter_add (l := l) (fun x => decide (g x = c))
    have : l.filter (fun x => !decide (g x = c)) = l.filter (g · ≠ c) := by
      refine List.filter_congr fun x _ => ?_
      simp
    rw [this] at h3
    simp only [List.map_cons, List.sum_cons, h1]
    omega

private theorem quotaSelect_cost (oracle : {ι : Type} → CmpTestQuery α ι → ι) (g : α → γ)
    (c : α → ℕ) (n : ℕ) : ∀ (k : ℕ) (xs : List α), xs.length = n →
      SumQuery.countInl oracle (quotaSelect g k xs) ≤
        (if k ≤ 1 then 102 else 204) * xs.length ∧
      (quotaSelect g k xs).cost oracle (CmpTestQuery.passWeight oracle) ≤
        k * (Nat.clog 2 xs.length + 1) ∧
      (quotaSelect g k xs).cost oracle (CmpTestQuery.failCost oracle c) =
        (((quotaSelect g k xs).eval oracle).failed.map c).sum := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k xs hn
  subst hn
  by_cases hk : k = 0
  · rw [quotaSelect.eq_def]
    simp [hk, SumQuery.countInl]
  simp only [SumQuery.countInl]
  rcases xs with _ | ⟨x, _ | ⟨y, zs⟩⟩
  · rw [quotaSelect]
    simp [hk]
  · rw [quotaSelect]
    rcases hb : oracle (.inr (.test x)) with _ | _
    · simp [hk, hb, SumQuery.weightInl, CmpTestQuery.passWeight, CmpTestQuery.failCost]
    · simp [hk, hb, SumQuery.weightInl, CmpTestQuery.passWeight, CmpTestQuery.failCost]
      omega
  · rw [quotaSelect]
    simp only [hk, ite_false]
    have hlen : 2 ≤ (x :: y :: zs).length := by simp
    generalize x :: y :: zs = xs at *
    simp only [FreeM.cost_bind, FreeM.eval_bind, cost_liftInl, eval_liftInl]
    have hmsC : (medianSplit xs).cost (fun q => oracle (.inl q))
        (fun q => (SumQuery.inl q : CmpTestQuery α _).weightInl) ≤ 34 * xs.length :=
      medianSplit_countQueries_le _ xs
    have hmsP : (medianSplit xs).cost (fun q => oracle (.inl q))
        (fun q => CmpTestQuery.passWeight oracle (.inl q)) = 0 := FreeM.cost_zero _ _
    have hmsF : (medianSplit xs).cost (fun q => oracle (.inl q))
        (fun q => CmpTestQuery.failCost oracle c (.inl q)) = 0 := FreeM.cost_zero _ _
    rw [hmsP, hmsF, zero_add, zero_add]
    rcases hms : (medianSplit xs).eval (fun q => oracle (.inl q)) with _ | ⟨L, H⟩
    · simp only [FreeM.cost_pure, FreeM.eval_pure, add_zero]
      refine ⟨by split_ifs <;> omega, Nat.zero_le _, by simp⟩
    · simp only
      by_cases hguard : L.length ≤ xs.length / 2 ∧ H.length ≤ xs.length - xs.length / 2
      swap
      · simp only [hguard, ite_false, FreeM.cost_pure, FreeM.eval_pure, add_zero]
        refine ⟨by split_ifs <;> omega, Nat.zero_le _, by simp⟩
      simp only [hguard, ite_true, and_self, FreeM.cost_bind, FreeM.eval_bind]
      obtain ⟨sc1, sc2, sc3, sc4, sc5, sc6, -, -, -⟩ := scanTests_spec oracle g c k L
      rcases hsc : (scanTests g k L).eval oracle with ⟨P, F⟩
      rw [hsc] at sc2 sc3 sc4 sc5 sc6
      simp only [SumQuery.countInl] at sc1
      simp only [sc1, sc2, sc3]
      dsimp only at sc4 sc5 sc6
      set L' := L.filter (· ∉ F) with hL'
      have hL'len : L'.length ≤ xs.length / 2 := (List.length_filter_le _ _).trans hguard.1
      by_cases hkP : k ≤ P.length
      · simp only [hkP, ite_true, FreeM.cost_bind, FreeM.eval_bind, FreeM.cost_pure,
          FreeM.eval_pure, add_zero, zero_add, List.map_append, List.sum_append]
        obtain ⟨c1, c2, c3⟩ := ih L'.length (by omega) k L' rfl
        simp only [SumQuery.countInl] at c1
        have hc : Nat.clog 2 L'.length + 1 ≤ Nat.clog 2 xs.length :=
          clog_add_one_le hlen (by omega)
        have := Nat.mul_le_mul_left k hc
        refine ⟨?_, ?_, by omega⟩
        · split_ifs at c1 ⊢ <;> omega
        · rw [Nat.mul_add, Nat.mul_one]
          omega
      · simp only [hkP, ite_false, FreeM.cost_bind, FreeM.eval_bind, FreeM.cost_pure,
          FreeM.eval_pure, add_zero, zero_add, List.map_append, List.sum_append, FreeM.cost_mapM,
          FreeM.eval_mapM]
        set H' := H.filter (g · ∉ P) with hH'
        have hH'len : H'.length ≤ xs.length - xs.length / 2 :=
          (List.length_filter_le _ _).trans hguard.2
        obtain ⟨d1, d2, d3⟩ := ih H'.length (by omega) (k - P.length) H' rfl
        simp only [SumQuery.countInl] at d1
        have hrec : ∀ c ∈ P, _ := fun c _ =>
          ih (L'.filter (g · = c)).length
            (by have := List.length_filter_le (fun x => decide (g x = c)) L'; omega) 1
            (L'.filter (g · = c)) rfl
        refine ⟨?_, ?_, ?_⟩
        · have hsum : (P.map fun b => (quotaSelect g 1 (L'.filter (g · = b))).cost oracle
              SumQuery.weightInl).sum ≤ 102 * L'.length :=
            calc _ ≤ (P.map fun b => 102 * (L'.filter (g · = b)).length).sum :=
                  List.sum_le_sum fun c hc => (hrec c hc).1
              _ = 102 * (P.map fun b => (L'.filter (g · = b)).length).sum :=
                  List.sum_map_mul_left _ _ _
              _ ≤ 102 * L'.length := Nat.mul_le_mul_left _ (sum_length_filter_le g sc5 L')
          by_cases hk1 : k ≤ 1
          · obtain rfl : P = [] := List.length_eq_zero_iff.mp (by omega)
            simp only [List.map_nil, List.sum_nil, zero_add, List.length_nil,
              Nat.sub_zero] at d1 ⊢
            simp only [hk1, ite_true] at d1 ⊢
            omega
          · split_ifs at d1 ⊢ <;> omega
        · have hc : ∀ l, l ≤ xs.length - xs.length / 2 →
              Nat.clog 2 l + 1 ≤ Nat.clog 2 xs.length :=
            fun l hl => clog_add_one_le hlen hl
          have hsum : (P.map fun b => (quotaSelect g 1 (L'.filter (g · = b))).cost oracle
              (CmpTestQuery.passWeight oracle)).sum ≤ P.length * Nat.clog 2 xs.length := by
            have := List.sum_le_length_nsmul (P.map fun b => (quotaSelect g 1
              (L'.filter (g · = b))).cost oracle (CmpTestQuery.passWeight oracle))
              (Nat.clog 2 xs.length) (by
                simp only [List.mem_map]
                rintro _ ⟨c, hcP, rfl⟩
                have h1 := (hrec c hcP).2.1
                have h2 := hc (L'.filter (g · = c)).length (by
                  have := List.length_filter_le (fun x => decide (g x = c)) L'
                  omega)
                omega)
            simpa using this
          have hH := Nat.mul_le_mul_left (k - P.length) (hc H'.length hH'len)
          have hsplit : P.length * Nat.clog 2 xs.length + (k - P.length) * Nat.clog 2 xs.length =
              k * Nat.clog 2 xs.length := by
            rw [← Nat.add_mul, Nat.add_sub_cancel' sc4]
          rw [Nat.mul_add, Nat.mul_one]
          omega
        · have hsum : (P.map fun b => (quotaSelect g 1 (L'.filter (g · = b))).cost oracle
              (CmpTestQuery.failCost oracle c)).sum = (P.map fun b => (((quotaSelect g 1
                (L'.filter (g · = b))).eval oracle).failed.map c).sum).sum :=
            congrArg List.sum (List.map_congr_left fun c hc => (hrec c hc).2.2)
          simp only [List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map,
            Function.comp_def]
          omega

/-! ## Correctness -/

private theorem eval_quotaSelect_of_two_le (oracle : {ι : Type} → CmpTestQuery α ι → ι)
    (g : α → γ) {k : ℕ} (hk : k ≠ 0) {xs : List α} (hlen : 2 ≤ xs.length) {L H : List α}
    (hms : (medianSplit xs).eval (fun q => oracle (.inl q)) = some (L, H))
    (hguard : L.length ≤ xs.length / 2 ∧ H.length ≤ xs.length - xs.length / 2) {P : List γ}
    {F : List α} (hsc : (scanTests g k L).eval oracle = (P, F)) :
    (quotaSelect g k xs).eval oracle =
      if k ≤ P.length then
        ⟨((quotaSelect g k (L.filter (· ∉ F))).eval oracle).selected,
          F ++ ((quotaSelect g k (L.filter (· ∉ F))).eval oracle).failed⟩
      else
        ⟨(P.map fun c => (quotaSelect g 1 ((L.filter (· ∉ F)).filter (g · = c))).eval
            oracle).flatMap (·.selected) ++
          ((quotaSelect g (k - P.length) (H.filter (g · ∉ P))).eval oracle).selected,
         F ++ (P.map fun c => (quotaSelect g 1 ((L.filter (· ∉ F)).filter (g · = c))).eval
            oracle).flatMap (·.failed) ++
          ((quotaSelect g (k - P.length) (H.filter (g · ∉ P))).eval oracle).failed⟩ := by
  obtain ⟨a, b, t, rfl⟩ : ∃ a b t, xs = a :: b :: t := by
    rcases xs with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp at hlen
    · simp at hlen
    · exact ⟨a, b, t, rfl⟩
  rw [quotaSelect]
  simp only [hk, ite_false, FreeM.eval_bind, eval_liftInl, hms, hguard, and_self, ite_true, hsc]
  split_ifs <;> simp [FreeM.eval_mapM]

section Representatives

variable {W : Type} [LinearOrder W] (g : α → γ) (w : α → W) (adm : α → Prop)
  [DecidablePred adm]

omit [DecidableEq α] [DecidableEq γ] in
/-- `r` is the representative of its group among `xs`: an admissible item of `xs` whose weight is
at most that of every admissible item of `xs` in the same group ([KhannaPuttermanSong2026], §3.2,
p. 14). -/
@[expose] def IsGroupRepresentative (xs : List α) (r : α) : Prop :=
  r ∈ xs ∧ adm r ∧ ∀ y ∈ xs, adm y → g y = g r → w r ≤ w y

omit [DecidableEq α] in
instance (xs : List α) : DecidablePred (IsGroupRepresentative g w adm xs) := fun _ => by
  unfold IsGroupRepresentative
  infer_instance

omit [DecidableEq α] in
/-- The groups of the items of `xs` that contain an admissible item. -/
def admissibleGroups (xs : List α) : Finset γ := ((xs.filter adm).map g).toFinset

omit [DecidableEq α] in
@[simp] theorem mem_admissibleGroups {xs : List α} {c : γ} :
    c ∈ admissibleGroups g adm xs ↔ ∃ x ∈ xs, adm x ∧ g x = c := by
  simp [admissibleGroups, and_assoc]

variable {g w adm}

omit [DecidableEq α] [DecidableEq γ] [DecidablePred adm] in
private theorem IsGroupRepresentative.eq (hw : Function.Injective w) {xs : List α} {x y : α}
    (hx : IsGroupRepresentative g w adm xs x) (hy : IsGroupRepresentative g w adm xs y)
    (hg : g x = g y) : x = y :=
  hw (le_antisymm (hx.2.2 y hy.1 hy.2.1 hg.symm) (hy.2.2 x hx.1 hx.2.1 hg))

omit [DecidableEq α] [DecidableEq γ] [DecidablePred adm] in
private theorem exists_isGroupRepresentative {xs : List α} {x : α} (hx : x ∈ xs) (ha : adm x) :
    ∃ r, IsGroupRepresentative g w adm xs r ∧ g r = g x ∧ w r ≤ w x := by
  classical
  obtain ⟨r, hr, hmin⟩ :=
    Finset.exists_min_image (xs.toFinset.filter fun y => adm y ∧ g y = g x) w
      ⟨x, by simp [hx, ha]⟩
  simp only [Finset.mem_filter, List.mem_toFinset] at hr hmin
  refine ⟨r, ⟨hr.1, hr.2.1, fun y hy hay hgy => hmin y ⟨hy, hay, hgy.trans hr.2.2⟩⟩,
    hr.2.2,
    hmin x ⟨hx, ha, rfl⟩⟩

omit [DecidableEq α] [DecidableEq γ] [DecidablePred adm] in
private theorem IsGroupRepresentative.mono {s t : List α} {x : α}
    (hx : IsGroupRepresentative g w adm s x) (hxt : x ∈ t) (hts : ∀ y ∈ t, y ∈ s) :
    IsGroupRepresentative g w adm t x :=
  ⟨hxt, hx.2.1, fun y hy => hx.2.2 y (hts y hy)⟩

omit [DecidableEq α] [DecidableEq γ] [DecidablePred adm] in
private theorem IsGroupRepresentative.of_subset {s t : List α} {x : α}
    (hx : IsGroupRepresentative g w adm t x) (hts : ∀ y ∈ t, y ∈ s)
    (hout : ∀ y ∈ s, adm y → g y = g x → y ∉ t → w x ≤ w y) :
    IsGroupRepresentative g w adm s x := by
  refine ⟨hts x hx.1, hx.2.1, fun y hy hay hgy => ?_⟩
  by_cases hyt : y ∈ t
  · exact hx.2.2 y hyt hay hgy
  · exact hout y hy hay hgy hyt

/-- Each group with an admissible item has exactly one representative. -/
private theorem card_representatives (hw : Function.Injective w) (s : List α) :
    (s.toFinset.filter (IsGroupRepresentative g w adm s)).card =
      (admissibleGroups g adm s).card := by
  have himg : (s.toFinset.filter (IsGroupRepresentative g w adm s)).image g =
      admissibleGroups g adm s := by
    ext c
    simp only [Finset.mem_image, Finset.mem_filter, List.mem_toFinset, mem_admissibleGroups]
    constructor
    · rintro ⟨r, ⟨_, hr⟩, rfl⟩
      exact ⟨r, hr.1, hr.2.1, rfl⟩
    · rintro ⟨x, hx, ha, rfl⟩
      obtain ⟨r, hr, hgr, -⟩ := exists_isGroupRepresentative (g := g) (w := w) hx ha
      exact ⟨r, ⟨hr.1, hr⟩, hgr⟩
  rw [← himg, Finset.card_image_of_injOn]
  intro a ha b hb hab
  simp only [Finset.coe_filter, List.mem_toFinset, Set.mem_ofPred_eq] at ha hb
  exact ha.2.eq hw hb.2 hab

/-- The quota selection invariant: the output of `quotaSelect g k xs` for comparisons by `w` and
tests by `adm`. -/
private structure Spec (k : ℕ) (xs : List α) (res : QuotaSelection α) : Prop where
  mem_selected : ∀ r, r ∈ res.selected ↔ IsGroupRepresentative g w adm xs r ∧
    (xs.toFinset.filter fun y => IsGroupRepresentative g w adm xs y ∧ w y < w r).card < k
  nodup_selected : res.selected.Nodup
  length_selected : res.selected.length = min k (admissibleGroups g adm xs).card
  nodup_failed : res.failed.Nodup
  failed : ∀ x ∈ res.failed, x ∈ xs ∧ ¬ adm x
  guarantee : ∀ e ∈ xs, e ∉ res.failed →
    (∀ r ∈ res.selected, g r = g e → w r ≤ w e) ∧
    ((∀ r ∈ res.selected, g r ≠ g e) →
      res.selected.length = k ∧ ∀ r ∈ res.selected, w r < w e)

private theorem quotaSelect_spec (hw : Function.Injective w)
    (oracle : {ι : Type} → CmpTestQuery α ι → ι)
    (hcmp : ∀ a b, oracle (.inl (.le a b)) = decide (w a ≤ w b))
    (htest : ∀ a, oracle (.inr (.test a)) = decide (adm a)) (n : ℕ) :
    ∀ (k : ℕ) (xs : List α), xs.length = n → xs.Nodup →
      Spec (g := g) (w := w) (adm := adm) k xs ((quotaSelect g k xs).eval oracle) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k xs hn hxs
  subst hn
  by_cases hk : k = 0
  · rw [quotaSelect.eq_def]
    simp only [hk, ite_true, FreeM.eval_pure]
    exact ⟨fun r => by simp, List.nodup_nil, by simp, List.nodup_nil, by simp,
      fun _ _ _ => ⟨by simp, fun _ => by simp⟩⟩
  rcases xs with _ | ⟨x, _ | ⟨y, zs⟩⟩
  · rw [quotaSelect]
    simp only [hk, ite_false, FreeM.eval_pure]
    refine ⟨fun r => ?_, List.nodup_nil, ?_, List.nodup_nil, by simp, by simp⟩
    · simp [IsGroupRepresentative]
    · simp [admissibleGroups]
  · rw [quotaSelect]
    by_cases hx : adm x
    · have hb : oracle (.inr (.test x)) = true := by simp [htest, hx]
      simp only [hk, ite_false, FreeM.eval_bind, SumQuery.liftInr, FreeM.eval_lift, hb, ite_true,
        FreeM.eval_pure]
      have hrep : IsGroupRepresentative g w adm [x] x :=
        ⟨List.mem_singleton_self x, hx, fun y hy _ _ => by rw [List.mem_singleton.mp hy]⟩
      refine ⟨fun r => ?_, List.nodup_singleton x, ?_, List.nodup_nil, by simp, ?_⟩
      · constructor
        · intro hr
          rw [List.mem_singleton.mp hr]
          refine ⟨hrep, ?_⟩
          rw [Finset.card_eq_zero.mpr]
          · omega
          · simp
        · rintro ⟨hr, -⟩
          exact List.mem_singleton.mpr (List.mem_singleton.mp hr.1)
      · have : admissibleGroups g adm [x] = {g x} := by
          ext c
          simp [hx, eq_comm]
        rw [this, Finset.card_singleton]
        simp only [List.length_singleton]
        omega
      · intro e he _
        rw [List.mem_singleton.mp he]
        exact ⟨fun r hr _ => by rw [List.mem_singleton.mp hr], fun h => absurd rfl (h x
          (List.mem_singleton_self x))⟩
    · have hb : oracle (.inr (.test x)) = false := by simp [htest, hx]
      simp only [hk, ite_false, FreeM.eval_bind, SumQuery.liftInr, FreeM.eval_lift, hb,
        Bool.false_eq_true, FreeM.eval_pure]
      refine ⟨fun r => ?_, List.nodup_nil, ?_, List.nodup_singleton x, ?_, ?_⟩
      · simp only [List.not_mem_nil, false_iff, not_and]
        intro hr
        exact absurd (List.mem_singleton.mp hr.1 ▸ hr.2.1) hx
      · have : admissibleGroups g adm [x] = ∅ := by
          ext c
          simp [hx]
        simp [this]
      · intro y hy
        rw [List.mem_singleton.mp hy]
        exact ⟨List.mem_singleton_self x, hx⟩
      · intro e he hef
        exact absurd (List.mem_singleton.mp he ▸ List.mem_singleton_self x) hef
  · have hlen : 2 ≤ (x :: y :: zs).length := by simp
    generalize x :: y :: zs = xs at *
    obtain ⟨p, L, H, hms, hLlen, hHlen, memL, memH, nodupL, nodupH⟩ :=
      eval_medianSplit w hw (fun q => oracle (.inl q)) hcmp hxs
        (List.ne_nil_of_length_pos (by omega))
    have hguard : L.length ≤ xs.length / 2 ∧ H.length ≤ xs.length - xs.length / 2 :=
      ⟨hLlen.le, hHlen.le⟩
    obtain ⟨-, -, -, sc4, sc5, sc6, sc7, sc8, sc9⟩ := scanTests_spec oracle g (fun _ => 0) k L
    rcases hsc : (scanTests g k L).eval oracle with ⟨P, F⟩
    rw [hsc] at sc4 sc5 sc6 sc7 sc8 sc9
    dsimp only at sc4 sc5 sc6 sc7 sc8 sc9
    rw [eval_quotaSelect_of_two_le oracle g hk hlen hms hguard hsc]
    have hP : ∀ c ∈ P, ∃ x ∈ L, adm x ∧ g x = c := by simpa [htest] using sc7
    have hF : ∀ x ∈ F, ¬ adm x := by simpa [htest] using sc8
    have hLsub : ∀ x ∈ L, x ∈ xs := fun x hx => ((memL x).mp hx).1
    have hHsub : ∀ x ∈ H, x ∈ xs := fun x hx => ((memH x).mp hx).1
    have hLH : ∀ x ∈ L, ∀ y ∈ H, w x < w y := fun x hx y hy =>
      ((memL x).mp hx).2.trans_le ((memH y).mp hy).2
    have hxsLH : ∀ x ∈ xs, x ∈ L ∨ x ∈ H := fun x hx => by
      rcases lt_or_ge (w x) (w p) with h | h
      · exact Or.inl ((memL x).mpr ⟨hx, h⟩)
      · exact Or.inr ((memH x).mpr ⟨hx, h⟩)
    have hLnH : ∀ x ∈ L, x ∉ H := fun x hx hH => lt_irrefl _ (hLH x hx x hH)
    set L' := L.filter (· ∉ F) with hL'
    have memL' : ∀ x, x ∈ L' ↔ x ∈ L ∧ x ∉ F := fun x => by simp [hL']
    have admL' : ∀ x ∈ L, adm x → x ∈ L' := fun x hx ha =>
      (memL' x).mpr ⟨hx, fun hf => hF x hf ha⟩
    have nodupL' : L'.Nodup := nodupL.filter _
    have hL'len : L'.length ≤ L.length := List.length_filter_le _ _
    have repL : ∀ x ∈ L, (IsGroupRepresentative g w adm xs x ↔
        IsGroupRepresentative g w adm L' x) := by
      intro x hx
      constructor
      · intro h
        exact h.mono (admL' x hx h.2.1) fun y hy => hLsub y ((memL' y).mp hy).1
      · intro h
        refine h.of_subset (fun y hy => hLsub y ((memL' y).mp hy).1) fun y hy hay _ hyL' => ?_
        rcases hxsLH y hy with hyL | hyH
        · exact absurd (admL' y hyL hay) hyL'
        · exact (hLH x hx y hyH).le
    have hFsub : ∀ x ∈ F, x ∈ L := fun x hx => sc6.subset hx
    by_cases hkP : k ≤ P.length
    · simp only [hkP, ite_true]
      have IH := ih L'.length (by omega) k L' rfl nodupL'
      set S := ((quotaSelect g k L').eval oracle).selected
      have hGL' : P.toFinset ⊆ admissibleGroups g adm L' := by
        intro c hc
        obtain ⟨x, hx, ha, rfl⟩ := hP c (List.mem_toFinset.mp hc)
        exact (mem_admissibleGroups g adm).mpr ⟨x, admL' x hx ha, ha, rfl⟩
      have hkG : k ≤ (admissibleGroups g adm L').card := by
        have := Finset.card_le_card hGL'
        rw [List.toFinset_card_of_nodup sc5] at this
        omega
      have hGsub : admissibleGroups g adm L' ⊆ admissibleGroups g adm xs := by
        intro c hc
        obtain ⟨x, hx, ha, rfl⟩ := (mem_admissibleGroups g adm).mp hc
        exact (mem_admissibleGroups g adm).mpr ⟨x, hLsub x ((memL' x).mp hx).1, ha, rfl⟩
      have hlenS : S.length = k := by
        rw [IH.length_selected]
        omega
      have hSL : ∀ r ∈ S, r ∈ L := fun r hr =>
        ((memL' r).mp ((IH.mem_selected r).mp hr).1.1).1
      have hrank : ∀ r ∈ L, (xs.toFinset.filter fun y => IsGroupRepresentative g w adm xs y ∧
          w y < w r) = (L'.toFinset.filter fun y => IsGroupRepresentative g w adm L' y ∧
          w y < w r) := by
        intro r hr
        ext y
        simp only [Finset.mem_filter, List.mem_toFinset]
        constructor
        · rintro ⟨hy, hry, hlt⟩
          have hyL : y ∈ L := (hxsLH y hy).resolve_right fun hyH =>
            absurd (hLH r hr y hyH) (not_lt.mpr hlt.le)
          have := (repL y hyL).mp hry
          exact ⟨this.1, this, hlt⟩
        · rintro ⟨hy, hry, hlt⟩
          have hyL := ((memL' y).mp hy).1
          exact ⟨hLsub y hyL, (repL y hyL).mpr hry, hlt⟩
      refine ⟨fun r => ?_, IH.nodup_selected, ?_, ?_, ?_, ?_⟩
      · rw [IH.mem_selected r]
        constructor
        · rintro ⟨hr, hrk⟩
          have hrL := ((memL' r).mp hr.1).1
          exact ⟨(repL r hrL).mpr hr, by rwa [hrank r hrL]⟩
        · rintro ⟨hr, hrk⟩
          rcases hxsLH r hr.1 with hrL | hrH
          · exact ⟨(repL r hrL).mp hr, by rwa [← hrank r hrL]⟩
          · exfalso
            have hsub : L'.toFinset.filter (IsGroupRepresentative g w adm L') ⊆
                xs.toFinset.filter fun y => IsGroupRepresentative g w adm xs y ∧ w y < w r := by
              intro y hy
              simp only [Finset.mem_filter, List.mem_toFinset] at hy ⊢
              have hyL := ((memL' y).mp hy.1).1
              exact ⟨hLsub y hyL, (repL y hyL).mpr hy.2, hLH y hyL r hrH⟩
            have := Finset.card_le_card hsub
            rw [card_representatives hw] at this
            omega
      · rw [hlenS]
        have := Finset.card_le_card hGsub
        omega
      · refine List.nodup_append.mpr ⟨sc6.nodup nodupL, IH.nodup_failed, ?_⟩
        intro a ha b hb hab
        subst hab
        exact ((memL' a).mp (IH.failed a hb).1).2 ha
      · intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact ⟨hLsub z (hFsub z hz), hF z hz⟩
        · obtain ⟨hz1, hz2⟩ := IH.failed z hz
          exact ⟨hLsub z ((memL' z).mp hz1).1, hz2⟩
      · intro e he hef
        rcases hxsLH e he with heL | heH
        · have heL' : e ∈ L' := (memL' e).mpr ⟨heL, fun h => hef (List.mem_append_left _ h)⟩
          exact IH.guarantee e heL' fun h => hef (List.mem_append_right _ h)
        · exact ⟨fun r hr _ => (hLH r (hSL r hr) e heH).le,
            fun _ => ⟨hlenS, fun r hr => hLH r (hSL r hr) e heH⟩⟩
    · simp only [hkP, ite_false]
      have hPk : P.length < k := by omega
      have hexh : ∀ x ∈ L, adm x → g x ∈ P := fun x hx ha =>
        (sc9 hPk x hx).resolve_right fun hf => hF x hf ha
      set H' := H.filter (g · ∉ P) with hH'
      have memH' : ∀ x, x ∈ H' ↔ x ∈ H ∧ g x ∉ P := fun x => by simp [hH']
      have nodupH' : H'.Nodup := nodupH.filter _
      have hH'len : H'.length ≤ H.length := List.length_filter_le _ _
      set f := fun c => (quotaSelect g 1 (L'.filter (g · = c))).eval oracle with hf
      set rH := (quotaSelect g (k - P.length) H').eval oracle with hrH
      have memLc : ∀ c x, x ∈ L'.filter (g · = c) ↔ x ∈ L' ∧ g x = c := fun c x => by
        simp
      have IHc : ∀ c ∈ P, Spec (g := g) (w := w) (adm := adm) 1 (L'.filter (g · = c)) (f c) :=
        fun c _ => ih _ (by
          have := List.length_filter_le (fun x => decide (g x = c)) L'
          omega) 1 _ rfl (nodupL'.filter _)
      have IHH : Spec (g := g) (w := w) (adm := adm) (k - P.length) H' rH :=
        ih H'.length (by omega) _ H' rfl nodupH'
      -- the representatives in `L` and in `H`
      have repLc : ∀ c r, IsGroupRepresentative g w adm (L'.filter (g · = c)) r ↔
          r ∈ L ∧ g r = c ∧ IsGroupRepresentative g w adm xs r := by
        intro c r
        constructor
        · intro h
          have hr := (memLc c r).mp h.1
          have hrL := ((memL' r).mp hr.1).1
          refine ⟨hrL, hr.2, (repL r hrL).mpr ?_⟩
          refine h.of_subset (fun y hy => ((memLc c y).mp hy).1) fun y hy hay hgy hyc => ?_
          exact absurd ((memLc c y).mpr ⟨hy, hgy.trans hr.2⟩) hyc
        · rintro ⟨hrL, hgr, hr⟩
          exact ((repL r hrL).mp hr).mono ((memLc c r).mpr ⟨admL' r hrL hr.2.1, hgr⟩)
            fun y hy => ((memLc c y).mp hy).1
      have repH : ∀ r ∈ H, (IsGroupRepresentative g w adm xs r ↔
          IsGroupRepresentative g w adm H' r) := by
        intro r hr
        constructor
        · intro h
          have hgr : g r ∉ P := by
            intro hgP
            obtain ⟨z, hz, haz, hgz⟩ := hP _ hgP
            exact absurd (h.2.2 z (hLsub z hz) haz hgz) (not_le.mpr (hLH z hz r hr))
          exact h.mono ((memH' r).mpr ⟨hr, hgr⟩) fun y hy => hHsub y ((memH' y).mp hy).1
        · intro h
          have hgr := ((memH' r).mp h.1).2
          refine h.of_subset (fun y hy => hHsub y ((memH' y).mp hy).1)
            fun y hy hay hgy hyH' => ?_
          exfalso
          rcases hxsLH y hy with hyL | hyH
          · exact hgr (hgy ▸ hexh y hyL hay)
          · exact hyH' ((memH' y).mpr ⟨hyH, hgy ▸ hgr⟩)
      have hGL' : admissibleGroups g adm L' = P.toFinset := by
        ext c
        rw [mem_admissibleGroups, List.mem_toFinset]
        constructor
        · rintro ⟨x, hx, ha, rfl⟩
          exact hexh x ((memL' x).mp hx).1 ha
        · intro hc
          obtain ⟨x, hx, ha, rfl⟩ := hP c hc
          exact ⟨x, admL' x hx ha, ha, rfl⟩
      have hrepsL' : (L'.toFinset.filter (IsGroupRepresentative g w adm L')).card = P.length := by
        rw [card_representatives hw, hGL', List.toFinset_card_of_nodup sc5]
      -- the selected items
      have selc : ∀ c ∈ P, ∀ r, r ∈ (f c).selected ↔ r ∈ L ∧ g r = c ∧
          IsGroupRepresentative g w adm xs r := by
        intro c hc r
        rw [(IHc c hc).mem_selected r, ← repLc]
        constructor
        · exact fun h => h.1
        · intro h
          refine ⟨h, ?_⟩
          rw [Finset.card_eq_zero.mpr]
          · exact Nat.one_pos
          · ext y
            simp only [Finset.mem_filter, List.mem_toFinset, Finset.notMem_empty, iff_false,
              not_and]
            intro _ hy hlt
            have := hy.eq hw h (((memLc c y).mp hy.1).2.trans ((memLc c r).mp h.1).2.symm)
            exact lt_irrefl _ (this ▸ hlt)
      have lenc : ∀ c ∈ P, (f c).selected.length = 1 := by
        intro c hc
        rw [(IHc c hc).length_selected]
        have : c ∈ admissibleGroups g adm (L'.filter (g · = c)) := by
          obtain ⟨x, hx, ha, rfl⟩ := hP c hc
          exact (mem_admissibleGroups g adm).mpr
            ⟨x, (memLc _ x).mpr ⟨admL' x hx ha, rfl⟩, ha, rfl⟩
        have := Finset.card_pos.mpr ⟨c, this⟩
        omega
      have memS : ∀ r, r ∈ (P.map f).flatMap (·.selected) ++ rH.selected ↔
          (∃ c ∈ P, r ∈ (f c).selected) ∨ r ∈ rH.selected := fun r => by
        simp [List.mem_flatMap]
      have memFl : ∀ r, r ∈ (P.map f).flatMap (·.failed) ↔ ∃ c ∈ P, r ∈ (f c).failed :=
        fun r => by simp [List.mem_flatMap]
      have selH : ∀ r ∈ rH.selected, r ∈ H' := fun r hr =>
        ((IHH.mem_selected r).mp hr).1.1
      have failc : ∀ c ∈ P, ∀ x ∈ (f c).failed, x ∈ L' ∧ g x = c ∧ ¬ adm x := by
        intro c hc x hx
        obtain ⟨h1, h2⟩ := (IHc c hc).failed x hx
        exact ⟨((memLc c x).mp h1).1, ((memLc c x).mp h1).2, h2⟩
      have hlenS : ((P.map f).flatMap (·.selected) ++ rH.selected).length =
          P.length + rH.selected.length := by
        rw [List.length_append, List.length_flatMap, List.map_map]
        congr 1
        have : P.map ((fun a => a.selected.length) ∘ f) = P.map fun _ => 1 :=
          List.map_congr_left fun c hc => lenc c hc
        rw [this]
        simp
      have rankL : ∀ r ∈ L, IsGroupRepresentative g w adm xs r →
          (xs.toFinset.filter fun y => IsGroupRepresentative g w adm xs y ∧ w y < w r).card ≤
            P.length := by
        intro r hrL _
        rw [← hrepsL']
        refine Finset.card_le_card fun y hy => ?_
        simp only [Finset.mem_filter, List.mem_toFinset] at hy ⊢
        have hyL : y ∈ L := (hxsLH y hy.1).resolve_right fun hyH =>
          absurd (hLH r hrL y hyH) (not_lt.mpr hy.2.2.le)
        have := (repL y hyL).mp hy.2.1
        exact ⟨this.1, this⟩
      have rankH : ∀ r ∈ H, IsGroupRepresentative g w adm xs r →
          (xs.toFinset.filter fun y => IsGroupRepresentative g w adm xs y ∧ w y < w r).card =
            P.length + (H'.toFinset.filter fun y => IsGroupRepresentative g w adm H' y ∧
              w y < w r).card := by
        intro r hrH _
        rw [← hrepsL', ← Finset.card_union_of_disjoint]
        · congr 1
          ext y
          simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_union]
          constructor
          · rintro ⟨hy, hry, hlt⟩
            rcases hxsLH y hy with hyL | hyH
            · have := (repL y hyL).mp hry
              exact Or.inl ⟨this.1, this⟩
            · have := (repH y hyH).mp hry
              exact Or.inr ⟨this.1, this, hlt⟩
          · rintro (⟨hy, hry⟩ | ⟨hy, hry, hlt⟩)
            · have hyL := ((memL' y).mp hy).1
              exact ⟨hLsub y hyL, (repL y hyL).mpr hry, hLH y hyL r hrH⟩
            · have hyH := ((memH' y).mp hy).1
              exact ⟨hHsub y hyH, (repH y hyH).mpr hry, hlt⟩
        · rw [Finset.disjoint_left]
          intro y hy hy'
          simp only [Finset.mem_filter, List.mem_toFinset] at hy hy'
          exact hLnH y ((memL' y).mp hy.1).1 ((memH' y).mp hy'.1).1
      have hGxs : (admissibleGroups g adm xs).card =
          P.length + (admissibleGroups g adm H').card := by
        rw [← List.toFinset_card_of_nodup sc5, ← Finset.card_union_of_disjoint]
        · congr 1
          ext c
          simp only [mem_admissibleGroups, Finset.mem_union, List.mem_toFinset]
          constructor
          · rintro ⟨x, hx, ha, rfl⟩
            rcases hxsLH x hx with hxL | hxH
            · exact Or.inl (hexh x hxL ha)
            · by_cases hgx : g x ∈ P
              · exact Or.inl hgx
              · exact Or.inr ⟨x, (memH' x).mpr ⟨hxH, hgx⟩, ha, rfl⟩
          · rintro (hc | ⟨x, hx, ha, rfl⟩)
            · obtain ⟨x, hx, ha, rfl⟩ := hP c hc
              exact ⟨x, hLsub x hx, ha, rfl⟩
            · exact ⟨x, hHsub x ((memH' x).mp hx).1, ha, rfl⟩
        · rw [Finset.disjoint_left]
          intro c hc hc'
          obtain ⟨x, hx, -, rfl⟩ := (mem_admissibleGroups g adm).mp hc'
          exact ((memH' x).mp hx).2 (List.mem_toFinset.mp hc)
      have exc : ∀ c ∈ P, ∃ r ∈ (f c).selected, g r = c := by
        intro c hc
        obtain ⟨r, hr⟩ := List.length_eq_one_iff.mp (lenc c hc)
        have hmem : r ∈ (f c).selected := by rw [hr]; exact List.mem_singleton_self r
        exact ⟨r, hmem, ((selc c hc r).mp hmem).2.1⟩
      have nodupFl : ∀ (sel : QuotaSelection α → List α),
          (∀ c ∈ P, (sel (f c)).Nodup ∧ ∀ x ∈ sel (f c), g x = c) →
          ((P.map f).flatMap sel).Nodup := by
        intro sel h
        rw [List.flatMap_map]
        refine List.nodup_flatMap.mpr ⟨fun c hc => (h c hc).1,
          sc5.pairwise_of_forall_ne fun a ha b hb hab x hxa hxb => hab ?_⟩
        exact ((h a ha).2 x hxa).symm.trans ((h b hb).2 x hxb)
      refine ⟨fun r => ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [memS]
        constructor
        · rintro (⟨c, hc, hr⟩ | hr)
          · obtain ⟨hrL, -, hrep⟩ := (selc c hc r).mp hr
            exact ⟨hrep, (rankL r hrL hrep).trans_lt hPk⟩
          · obtain ⟨hrep, hrk⟩ := (IHH.mem_selected r).mp hr
            have hrH := ((memH' r).mp hrep.1).1
            have hrep' := (repH r hrH).mpr hrep
            refine ⟨hrep', ?_⟩
            rw [rankH r hrH hrep']
            omega
        · rintro ⟨hrep, hrk⟩
          rcases hxsLH r hrep.1 with hrL | hrH
          · exact Or.inl ⟨g r, hexh r hrL hrep.2.1, (selc _ (hexh r hrL hrep.2.1) r).mpr
              ⟨hrL, rfl, hrep⟩⟩
          · refine Or.inr ((IHH.mem_selected r).mpr ⟨(repH r hrH).mp hrep, ?_⟩)
            rw [rankH r hrH hrep] at hrk
            omega
      · refine List.nodup_append.mpr ⟨nodupFl (·.selected) fun c hc =>
          ⟨(IHc c hc).nodup_selected, fun x hx => ((selc c hc x).mp hx).2.1⟩,
          IHH.nodup_selected, ?_⟩
        intro a ha b hb hab
        subst hab
        · simp only [List.mem_flatMap, List.mem_map] at ha
          obtain ⟨_, ⟨c, hc, rfl⟩, hac⟩ := ha
          exact hLnH a ((selc c hc a).mp hac).1 ((memH' a).mp (selH a hb)).1
      · rw [hlenS, IHH.length_selected, hGxs]
        omega
      · have hX : ((P.map f).flatMap (·.failed)).Nodup := nodupFl (·.failed) fun c hc =>
          ⟨(IHc c hc).nodup_failed, fun x hx => (failc c hc x hx).2.1⟩
        refine List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨sc6.nodup nodupL, hX, ?_⟩,
          IHH.nodup_failed, ?_⟩
        · intro a ha b hb hab
          subst hab
          obtain ⟨c, hc, hac⟩ := (memFl a).mp hb
          exact ((memL' a).mp (failc c hc a hac).1).2 ha
        · intro a ha b hb hab
          subst hab
          have haH := ((memH' a).mp (IHH.failed a hb).1).1
          rcases List.mem_append.mp ha with ha | ha
          · exact hLnH a (hFsub a ha) haH
          · obtain ⟨c, hc, hac⟩ := (memFl a).mp ha
            exact hLnH a ((memL' a).mp (failc c hc a hac).1).1 haH
      · intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · rcases List.mem_append.mp hz with hz | hz
          · exact ⟨hLsub z (hFsub z hz), hF z hz⟩
          · obtain ⟨c, hc, hzc⟩ := (memFl z).mp hz
            obtain ⟨h1, -, h3⟩ := failc c hc z hzc
            exact ⟨hLsub z ((memL' z).mp h1).1, h3⟩
        · obtain ⟨h1, h2⟩ := IHH.failed z hz
          exact ⟨hHsub z ((memH' z).mp h1).1, h2⟩
      · intro e he hef
        have heF : e ∉ F := fun h => hef (List.mem_append_left _ (List.mem_append_left _ h))
        have heX : ∀ c ∈ P, e ∉ (f c).failed := fun c hc h =>
          hef (List.mem_append_left _ (List.mem_append_right _ ((memFl e).mpr ⟨c, hc, h⟩)))
        have heY : e ∉ rH.failed := fun h => hef (List.mem_append_right _ h)
        -- the selected items of a group in `P` lie in `L`; the others lie in `H'`
        have hsel : ∀ r ∈ (P.map f).flatMap (·.selected) ++ rH.selected,
            (r ∈ L ∧ g r ∈ P) ∨ r ∈ H' := by
          intro r hr
          rcases (memS r).mp hr with ⟨c, hc, hrc⟩ | hrH
          · obtain ⟨hrL, hgr, -⟩ := (selc c hc r).mp hrc
            exact Or.inl ⟨hrL, hgr ▸ hc⟩
          · exact Or.inr (selH r hrH)
        have notb : g e ∈ P → ¬ ∀ r ∈ (P.map f).flatMap (·.selected) ++ rH.selected,
            g r ≠ g e := by
          intro hgP h
          obtain ⟨r, hr, hgr⟩ := exc (g e) hgP
          exact h r ((memS r).mpr (Or.inl ⟨g e, hgP, hr⟩)) hgr
        rcases hxsLH e he with heL | heH
        · have hgP : g e ∈ P := (sc9 hPk e heL).resolve_right heF
          have heLc : e ∈ L'.filter (g · = g e) :=
            (memLc _ e).mpr ⟨(memL' e).mpr ⟨heL, heF⟩, rfl⟩
          have IHe := ((IHc (g e) hgP).guarantee e heLc (heX (g e) hgP)).1
          refine ⟨fun r hr hgr => ?_, fun h => absurd h (notb hgP)⟩
          rcases (memS r).mp hr with ⟨c, hc, hrc⟩ | hrH
          · have hgc : c = g e := ((selc c hc r).mp hrc).2.1.symm.trans hgr
            rw [hgc] at hrc
            exact IHe r hrc hgr
          · exact absurd (hgr ▸ hgP) ((memH' r).mp (selH r hrH)).2
        · by_cases hgP : g e ∈ P
          · refine ⟨fun r hr hgr => ?_, fun h => absurd h (notb hgP)⟩
            rcases hsel r hr with ⟨hrL, -⟩ | hrH'
            · exact (hLH r hrL e heH).le
            · exact absurd (hgr ▸ hgP) ((memH' r).mp hrH').2
          · have heH' : e ∈ H' := (memH' e).mpr ⟨heH, hgP⟩
            obtain ⟨IHa, IHb⟩ := IHH.guarantee e heH' heY
            refine ⟨fun r hr hgr => ?_, fun h => ?_⟩
            · rcases (memS r).mp hr with ⟨c, hc, hrc⟩ | hrH
              · exact absurd (hgr ▸ ((selc c hc r).mp hrc).2.1 ▸ hc) hgP
              · exact IHa r hrH hgr
            · obtain ⟨hlenH, hltH⟩ := IHb fun r hr => h r ((memS r).mpr (Or.inr hr))
              refine ⟨by rw [hlenS, hlenH]; omega, fun r hr => ?_⟩
              rcases (memS r).mp hr with ⟨c, hc, hrc⟩ | hrH
              · exact hLH r ((selc c hc r).mp hrc).1 e heH
              · exact hltH r hrH

/-! ## Main results -/

variable (g) {k : ℕ} {xs : List α}

/-- **Quota selection is correct**, a step in the proof of Theorem 4.1 of [KhannaPuttermanSong2026]
(the paper's Lemma 3.3, §3.2, p. 16). Against comparisons by an injective weight `w` and tests by
`adm`, `quotaSelect g k xs` selects exactly the representatives with fewer than `k` lighter
representatives: the `k` lightest representatives, or all of them if there are fewer than `k`. -/
theorem mem_selected_quotaSelect (hw : Function.Injective w) (hxs : xs.Nodup) (r : α) :
    r ∈ ((quotaSelect g k xs).eval (CmpTestQuery.oracleOf w adm)).selected ↔
      IsGroupRepresentative g w adm xs r ∧
        (xs.toFinset.filter fun y => IsGroupRepresentative g w adm xs y ∧ w y < w r).card < k :=
  (quotaSelect_spec hw _ (fun _ _ => rfl) (fun _ => rfl) _ k xs rfl hxs).mem_selected r

/-- Quota selection selects no item twice. -/
theorem nodup_selected_quotaSelect (hw : Function.Injective w) (hxs : xs.Nodup) :
    ((quotaSelect g k xs).eval (CmpTestQuery.oracleOf w adm)).selected.Nodup :=
  (quotaSelect_spec hw _ (fun _ _ => rfl) (fun _ => rfl) _ k xs rfl hxs).nodup_selected

/-- Quota selection selects `min k c` items, where `c` is the number of groups with an admissible
item. -/
theorem length_selected_quotaSelect (hw : Function.Injective w) (hxs : xs.Nodup) :
    ((quotaSelect g k xs).eval (CmpTestQuery.oracleOf w adm)).selected.length =
      min k (admissibleGroups g adm xs).card :=
  (quotaSelect_spec hw _ (fun _ _ => rfl) (fun _ => rfl) _ k xs rfl hxs).length_selected

/-- The items reported as failed are distinct inadmissible items of the input. -/
theorem failed_quotaSelect (hw : Function.Injective w) (hxs : xs.Nodup) :
    ((quotaSelect g k xs).eval (CmpTestQuery.oracleOf w adm)).failed.Nodup ∧
      ∀ x ∈ ((quotaSelect g k xs).eval (CmpTestQuery.oracleOf w adm)).failed, x ∈ xs ∧ ¬ adm x :=
  let h := quotaSelect_spec hw _ (fun _ _ => rfl) (fun _ => rfl) _ k xs rfl hxs
  ⟨h.nodup_failed, h.failed⟩

/-- **The guarantee of quota selection used by the batch procedure** ([KhannaPuttermanSong2026],
§3.2, proof of Lemma 3.2, p. 15). Let `R'` be the items whose test failed. For every input item
`e ∉ R'`, admissible or not: a selected item in the group of `e` weighs at most `w e`; and if no
item of its group is selected, then exactly `k` items are selected, all lighter than `e`.

The source argues the second part by noting that an untested item could be made admissible
without changing the run; here it is proved directly, by induction along the recursion. -/
theorem quotaSelect_guarantee (hw : Function.Injective w) (hxs : xs.Nodup) {e : α} (he : e ∈ xs)
    (hef : e ∉ ((quotaSelect g k xs).eval (CmpTestQuery.oracleOf w adm)).failed) :
    (∀ r ∈ ((quotaSelect g k xs).eval (CmpTestQuery.oracleOf w adm)).selected,
        g r = g e → w r ≤ w e) ∧
      ((∀ r ∈ ((quotaSelect g k xs).eval (CmpTestQuery.oracleOf w adm)).selected, g r ≠ g e) →
        ((quotaSelect g k xs).eval (CmpTestQuery.oracleOf w adm)).selected.length = k ∧
          ∀ r ∈ ((quotaSelect g k xs).eval (CmpTestQuery.oracleOf w adm)).selected, w r < w e) :=
  (quotaSelect_spec hw _ (fun _ _ => rfl) (fun _ => rfl) _ k xs rfl hxs).guarantee e he hef

end Representatives

variable (g : α → γ) (k : ℕ) (xs : List α)

/-- **Comparison bound for quota selection**, a step in the proof of Theorem 4.1 of
[KhannaPuttermanSong2026] (the paper's Lemma 3.3, §3.2, p. 16). For every oracle,
`quotaSelect g k xs` makes at most `204 * xs.length` comparisons. -/
theorem countInl_quotaSelect_le (oracle : {ι : Type} → CmpTestQuery α ι → ι) :
    SumQuery.countInl oracle (quotaSelect g k xs) ≤ 204 * xs.length := by
  have h := (quotaSelect_cost oracle g (fun _ => 0) _ k xs rfl).1
  split_ifs at h <;> omega

/-- **Successful-test bound for quota selection**, a step in the proof of Theorem 4.1 of
[KhannaPuttermanSong2026] (the paper's Lemma 3.3, §3.2, p. 16). For every oracle,
`quotaSelect g k xs` makes at most `k * (⌈log₂ m⌉ + 1)` tests answered `true`, where
`m = xs.length`. -/
theorem cost_passWeight_quotaSelect_le (oracle : {ι : Type} → CmpTestQuery α ι → ι) :
    (quotaSelect g k xs).cost oracle (CmpTestQuery.passWeight oracle) ≤
      k * (Nat.clog 2 xs.length + 1) :=
  (quotaSelect_cost oracle g (fun _ => 0) _ k xs rfl).2.1

/-- For every oracle and every cost `c` of a failed test, the failed tests of `quotaSelect g k xs`
cost `∑ c x` over the items `x` it reports as failed: each reported item failed exactly one test,
and no other test failed. -/
theorem cost_failCost_quotaSelect (oracle : {ι : Type} → CmpTestQuery α ι → ι) (c : α → ℕ) :
    (quotaSelect g k xs).cost oracle (CmpTestQuery.failCost oracle c) =
      (((quotaSelect g k xs).eval oracle).failed.map c).sum :=
  (quotaSelect_cost oracle g c _ k xs rfl).2.2

/-- For every oracle, the tests of `quotaSelect g k xs` answered `false` are as many as the items
it reports as failed. -/
theorem cost_failWeight_quotaSelect (oracle : {ι : Type} → CmpTestQuery α ι → ι) :
    (quotaSelect g k xs).cost oracle (CmpTestQuery.failWeight oracle) =
      ((quotaSelect g k xs).eval oracle).failed.length := by
  have h : (fun {ι} (q : CmpTestQuery α ι) => CmpTestQuery.failWeight oracle q) =
      fun {ι} q => CmpTestQuery.failCost oracle (fun _ => 1) q := by
    funext ι q
    rcases q with q | ⟨a⟩ <;> rfl
  rw [h, cost_failCost_quotaSelect]
  simp

/-- **Failed tests of quota selection**: no item fails twice. Against comparisons by an injective
weight and tests by `adm`, the tests answered `false` are at most the inadmissible items of the
input. -/
theorem cost_failWeight_quotaSelect_le {W : Type} [LinearOrder W] {w : α → W}
    (hw : Function.Injective w) {adm : α → Prop} [DecidablePred adm] {xs : List α}
    (hxs : xs.Nodup) :
    (quotaSelect g k xs).cost (CmpTestQuery.oracleOf w adm)
        (CmpTestQuery.failWeight (CmpTestQuery.oracleOf w adm)) ≤
      (xs.toFinset.filter fun x => ¬ adm x).card := by
  obtain ⟨hnd, hmem⟩ := failed_quotaSelect (k := k) (adm := adm) g hw hxs
  rw [cost_failWeight_quotaSelect, ← List.toFinset_card_of_nodup hnd]
  refine Finset.card_le_card fun x hx => ?_
  have := hmem x (List.mem_toFinset.mp hx)
  simpa using this

end Cslib.Query
