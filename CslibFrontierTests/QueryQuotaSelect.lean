/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.Query.Select.Quota

/-!
# Tests for quota selection with admissibility tests

Concrete runs of `Cslib.Query.quotaSelect` with items `0, 1, 2, …` weighted by themselves:
quota `0`, more groups than the quota, fewer groups than the quota, a group with no admissible
item, and parallel items in one group. Each run is checked against a direct computation of the
`k` lightest representatives, together with the reported failures and the three query counts.
-/

namespace CslibFrontierTests.QueryQuotaSelect

open Cslib Cslib.Query

-- This file checks concrete runs with `#guard`.
set_option linter.hashCommand false

/-- Comparisons by the item itself, tests by `adm`. -/
abbrev oracle (adm : ℕ → Prop) [DecidablePred adm] : {ι : Type} → CmpTestQuery ℕ ι → ι :=
  CmpTestQuery.oracleOf id adm

/-- The selected items of a run, sorted. -/
def selected (g : ℕ → ℕ) (adm : ℕ → Prop) [DecidablePred adm] (k : ℕ) (xs : List ℕ) :
    List ℕ :=
  ((quotaSelect g k xs).eval (oracle adm)).selected.mergeSort

/-- The failed items of a run, sorted. -/
def failed (g : ℕ → ℕ) (adm : ℕ → Prop) [DecidablePred adm] (k : ℕ) (xs : List ℕ) :
    List ℕ :=
  ((quotaSelect g k xs).eval (oracle adm)).failed.mergeSort

/-- The `k` lightest representatives, computed directly: the admissible items lightest in their
group, sorted, and cut to `k`. -/
def reference (g : ℕ → ℕ) (adm : ℕ → Prop) [DecidablePred adm] (k : ℕ) (xs : List ℕ) :
    List ℕ :=
  ((xs.filter fun x => adm x ∧ ∀ y ∈ xs, adm y → g y = g x → x ≤ y).mergeSort).take k

/-- The number of comparisons, successful tests and failed tests of a run. -/
def counts (g : ℕ → ℕ) (adm : ℕ → Prop) [DecidablePred adm] (k : ℕ) (xs : List ℕ) :
    ℕ × ℕ × ℕ :=
  (SumQuery.countInl (oracle adm) (quotaSelect g k xs),
    (quotaSelect g k xs).cost (oracle adm) (CmpTestQuery.passWeight (oracle adm)),
    (quotaSelect g k xs).cost (oracle adm) (CmpTestQuery.failWeight (oracle adm)))

/-- A scrambled list of `0, …, 199`. -/
def scrambled : List ℕ := (List.range 200).map fun i => i * 37 % 200

/-- Groups of ten consecutive items; an item is admissible unless it is divisible by `3`. -/
def g10 (x : ℕ) : ℕ := x / 10

/-- Admissible unless divisible by `3`. -/
def adm3 (x : ℕ) : Prop := x % 3 ≠ 0

instance : DecidablePred adm3 := fun x => inferInstanceAs (Decidable (x % 3 ≠ 0))

/-! ### Quota `0` -/

#guard selected g10 adm3 0 scrambled == []
#guard failed g10 adm3 0 scrambled == []
#guard counts g10 adm3 0 scrambled == (0, 0, 0)

/-! ### More groups than the quota -/

-- `20` groups, each with an admissible item; the five lightest representatives are the
-- smallest admissible item of groups `0, …, 4`.
#guard selected g10 adm3 5 scrambled == [1, 10, 20, 31, 40]
#guard selected g10 adm3 5 scrambled == reference g10 adm3 5 scrambled
#guard [1, 2, 3, 7, 19, 20].all fun k => selected g10 adm3 k scrambled ==
  reference g10 adm3 k scrambled
-- Failed items are distinct and inadmissible, and the counts respect the bounds.
#guard (failed g10 adm3 5 scrambled).all (· % 3 == 0)
#guard (failed g10 adm3 5 scrambled).Nodup
#guard (counts g10 adm3 5 scrambled).1 ≤ 234 * 200
#guard (counts g10 adm3 5 scrambled).2.1 ≤ 5 * (Nat.clog 2 200 + 1)
#guard (counts g10 adm3 5 scrambled).2.2 == (failed g10 adm3 5 scrambled).length

/-! ### Fewer groups than the quota -/

-- All `20` representatives are selected when the quota exceeds the number of groups.
#guard selected g10 adm3 25 scrambled == reference g10 adm3 25 scrambled
#guard (selected g10 adm3 25 scrambled).length == 20

/-! ### A group with no admissible item -/

/-- Group `3` (items `30, …, 39`) has no admissible item; elsewhere `adm3`. -/
def admNo3 (x : ℕ) : Prop := x / 10 ≠ 3 ∧ x % 3 ≠ 0

instance : DecidablePred admNo3 := fun x => inferInstanceAs (Decidable (x / 10 ≠ 3 ∧ x % 3 ≠ 0))

-- Group `3` is skipped: the fourth representative comes from group `4`.
#guard selected g10 admNo3 4 scrambled == [1, 10, 20, 40]
#guard selected g10 admNo3 4 scrambled == reference g10 admNo3 4 scrambled
-- With every group selected, group `3` contributes nothing.
#guard (selected g10 admNo3 30 scrambled).length == 19

/-! ### Parallel items in one group -/

-- One group holds all items: quota selection finds the lightest admissible item.
#guard selected (fun _ => 0) adm3 1 scrambled == [1]
#guard selected (fun _ => 0) adm3 3 scrambled == [1]
-- Items `0` and `3` fail first in a scan from the light end of their group.
#guard selected (fun _ => 0) adm3 1 [3, 0, 7, 4] == [4]
#guard failed (fun _ => 0) adm3 1 [3, 0, 7, 4] == [0, 3]

/-! ### Direct applications of the theorems -/

/-- In `[5, 1, 4]` with one group and all items admissible, `1` is the representative. -/
example : IsGroupRepresentative (fun _ => 0) id (fun _ => True) [5, 1, 4] 1 := by decide

/-- `4` is not the representative of that group. -/
example : ¬ IsGroupRepresentative (fun _ => 0) id (fun _ => True) [5, 1, 4] 4 := by decide

/-- The length theorem applied to a run with two groups and quota `5`. -/
example : ((quotaSelect g10 5 [3, 0, 17, 4]).eval (oracle adm3)).selected.length =
    min 5 (admissibleGroups g10 adm3 [3, 0, 17, 4]).card :=
  length_selected_quotaSelect g10 (adm := adm3) Function.injective_id (by decide)

/-- An oracle answering every comparison and every test `true`: not the comparison oracle of any
injective weight. -/
def allTrue : {ι : Type} → CmpTestQuery ℕ ι → ι :=
  SumQuery.combine (LEQuery.oracleOf fun _ _ => true) (TestQuery.oracleOf fun _ => true)

-- The query bounds hold for every oracle, including `allTrue`.
#guard SumQuery.countInl allTrue (quotaSelect g10 5 scrambled) ≤ 234 * 200
#guard (quotaSelect g10 5 scrambled).cost allTrue (CmpTestQuery.passWeight allTrue) ≤
  5 * (Nat.clog 2 200 + 1)

example : SumQuery.countInl allTrue (quotaSelect g10 5 scrambled) ≤ 234 * scrambled.length :=
  countInl_quotaSelect_le g10 5 scrambled _

end CslibFrontierTests.QueryQuotaSelect
