/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.OptimalBST.Yao
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Optimal binary search trees and Knuth's window algorithm

The dynamic program for optimal binary search trees fills the table of intervals `(i, i + d]` by
increasing length `d`. Each entry scans a window `lo, …, hi` of candidate roots `k` and keeps the
largest one minimizing `T(i, k - 1) + T(k, j)` (`cell`). The cubic algorithm (`plainBST`) scans
every root `i + 1, …, j`. Knuth's algorithm (`knuthBST`) scans only
`root(i, j - 1), …, root(i + 1, j)`, the window allowed by the monotonicity of optimal roots.

Both algorithms return the optimal cost `optCost w 0 n` and the tree `optTree w 0 n` read off the
largest optimal roots: the cubic one for every weight (`plainBST_eq`), and Knuth's when the weight
satisfies the quadrangle inequality and is monotone on intervals (`knuthBST_eq`). Along each
diagonal `d + 1`, Knuth's windows telescope to at most `2 n` candidate roots
(`sum_knuth_window_le`). Without the quadrangle and monotonicity hypotheses Knuth's algorithm can
return a suboptimal cost; see `CslibFrontierTests.OptimalBST`. Checked Word-RAM `O(n³)` and `O(n²)`
running-time bounds are proved in `CslibFrontier.Algorithms.WordRAM.OptimalBST`.

## Main definitions

* `Cslib.Algorithms.Lean.OptimalBST.Entry`, `Table`, `Window`: table entries, tables, and
  candidate-root window rules (`Window.plain`, `Window.knuth`).
* `Cslib.Algorithms.Lean.OptimalBST.scan`, `cell`, `diag`, `table`, `solve`: pure window scan and
  diagonal-by-diagonal dynamic programming.
* `Cslib.Algorithms.Lean.OptimalBST.plainBST`: the cubic dynamic program.
* `Cslib.Algorithms.Lean.OptimalBST.knuthBST`: Knuth's window dynamic program.
* `Cslib.Algorithms.Lean.OptimalBST.Solution`, `Solution.IsOptimal`: the output pair and optimality
  predicate.

## Main results

* `Cslib.Algorithms.Lean.OptimalBST.plainBST_eq`, `isOptimal_plainBST`: correctness of the cubic
  algorithm, for every weight.
* `Cslib.Algorithms.Lean.OptimalBST.knuthBST_eq`, `isOptimal_knuthBST`: correctness of Knuth's
  algorithm under the quadrangle inequality and interval monotonicity.
* `Cslib.Algorithms.Lean.OptimalBST.sum_knuth_window_le`: Knuth's telescoping bound (`≤ 2 n`
  candidate roots per diagonal).
* `Cslib.Algorithms.Lean.OptimalBST.optCost_congr`, `optCost_le_nsmul`: subinterval congruence and
  linear bound `(j - i) • M` on `optCost w i j` from a uniform bound `M` on interval weights.
* `Cslib.Algorithms.Lean.OptimalBST.knuthBST_knuthWeight`: Knuth's optimality theorem for
  nonnegative access and failure weights.

## References

* [D. E. Knuth, *Optimum binary search trees*][Knuth1971]
* [F. F. Yao, *Efficient dynamic programming using quadrangle inequalities*][Yao1980b]
* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Section 15.5][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.OptimalBST

open Finset

variable {β : Type*}

/-! ### Tables and windows -/

/-- A table entry: a cost and a root. -/
@[ext]
structure Entry (β : Type*) where
  /-- The cost of the interval. -/
  cost : β
  /-- The chosen root. -/
  root : ℕ
  deriving DecidableEq

/-- A dynamic-programming table, indexed by the endpoints `i, j` of the key interval
`i + 1, …, j`. -/
abbrev Table (β : Type*) := ℕ → ℕ → Entry β

/-- A rule choosing the window `lo, …, hi` of candidate roots for `(i, j]` from the table. -/
structure Window (β : Type*) where
  /-- The first candidate root. -/
  lo : Table β → ℕ → ℕ → ℕ
  /-- The last candidate root. -/
  hi : Table β → ℕ → ℕ → ℕ

/-- Every root `i + 1, …, j` (the cubic dynamic program). -/
def Window.plain : Window β := ⟨fun _ i _ => i + 1, fun _ _ j => j⟩

/-- Knuth's window `root(i, j - 1), …, root(i + 1, j)`, or the only root `j` when `j = i + 1`. -/
def Window.knuth : Window β :=
  ⟨fun T i j => if i + 1 < j then (T i (j - 1)).root else j,
    fun T i j => if i + 1 < j then (T (i + 1) j).root else j⟩

/-- Overwrite the entry of the interval `(i, i + d]`. -/
def setCell (d : ℕ) (T : Table β) (i : ℕ) (e : Entry β) : Table β :=
  fun a b => if a = i ∧ b = i + d then e else T a b

theorem foldl_setCell (d : ℕ) (F : ℕ → Entry β) : ∀ (l : List ℕ) (U : Table β) (a b : ℕ),
    l.foldl (fun U i => setCell d U i (F i)) U a b = if a ∈ l ∧ b = a + d then F a else U a b
  | [], U, a, b => by simp only [List.foldl_nil, List.not_mem_nil, false_and, ↓reduceIte]
  | x :: l, U, a, b => by
    rw [List.foldl_cons, foldl_setCell d F l, setCell]
    simp only [List.mem_cons]
    split_ifs <;> grind

/-- The output of an optimal-BST algorithm: a cost and a tree. -/
structure Solution (β : Type*) where
  /-- The optimal cost. -/
  cost : β
  /-- A tree attaining it. -/
  tree : BinaryTree ℕ

/-! ### The scan of a window -/

section Scan

variable [LinearOrder β]

/-- Keep the cheaper of the current best entry and candidate `k`, preferring `k` on ties. -/
def bestStep (c : ℕ → β) (best : Entry β) (k : ℕ) : Entry β :=
  if c k ≤ best.cost then ⟨c k, k⟩ else best

/-- Scan the candidates `lo, …, hi` for a largest minimizer of `c`. -/
def scan (c : ℕ → β) (lo hi : ℕ) : Entry β :=
  (List.range' (lo + 1) (hi - lo)).foldl (bestStep c) ⟨c lo, lo⟩

/-- Invariant satisfied by `scan c lo hi` when `lo ≤ hi`: the returned entry is the largest
minimizer of `c` on `[lo, hi]`. -/
def ScanInv (c : ℕ → β) (lo hi : ℕ) (e : Entry β) : Prop :=
  lo ≤ e.root ∧ e.root ≤ hi ∧ e.cost = c e.root ∧ (∀ k, lo ≤ k → k ≤ hi → e.cost ≤ c k) ∧
    ∀ k, e.root < k → k ≤ hi → e.cost < c k

theorem scanInv_foldl (c : ℕ → β) (lo : ℕ) : ∀ m,
    ScanInv c lo (lo + m) ((List.range' (lo + 1) m).foldl (bestStep c) ⟨c lo, lo⟩)
  | 0 => by
    refine ⟨le_rfl, le_rfl, rfl, fun k h₁ h₂ => ?_, fun k h₁ h₂ => ?_⟩
    · obtain rfl : k = lo := by omega
      exact le_rfl
    · exact absurd h₂ (by simp only [List.range'_zero, List.foldl_nil] at h₁; omega)
  | m + 1 => by
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, one_mul,
      Nat.add_right_comm]
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := scanInv_foldl c lo m
    generalize (List.range' (lo + 1) m).foldl (bestStep c) ⟨c lo, lo⟩ = e at *
    unfold bestStep
    split_ifs with h
    · refine ⟨(Nat.le_add_right lo m).trans (Nat.le_succ _), le_rfl, rfl,
        fun k hk₁ hk₂ => (Nat.of_le_succ hk₂).elim (fun hk => h.trans (h₄ k hk₁ hk))
          fun hk => hk ▸ le_rfl,
        fun k hk₁ hk₂ => absurd hk₂ (not_le_of_gt hk₁)⟩
    · refine ⟨h₁, Nat.le_succ_of_le h₂, h₃,
        fun k hk₁ hk₂ => (Nat.of_le_succ hk₂).elim (h₄ k hk₁) fun hk => hk ▸ le_of_not_ge h,
        fun k hk₁ hk₂ => (Nat.of_le_succ hk₂).elim (h₅ k hk₁) fun hk => hk ▸ lt_of_not_ge h⟩

theorem scanInv_scan (c : ℕ → β) {lo hi : ℕ} (h : lo ≤ hi) :
    ScanInv c lo hi (scan c lo hi) := by
  have hinv := scanInv_foldl c lo (hi - lo)
  rwa [Nat.add_sub_of_le h] at hinv

end Scan

/-! ### The table algorithms -/

section Algorithm

variable [AddCommMonoid β] [LinearOrder β]

/-- The cost of root `k` for the keys `i + 1, …, j`, read from the table. -/
def Table.candidate (T : Table β) (i j k : ℕ) : β := (T i (k - 1)).cost + (T k j).cost

/-- The entry for the keys `i + 1, …, j`, scanning the candidate roots `lo, …, hi`. -/
def cell (w : ℕ → ℕ → β) (T : Table β) (i j lo hi : ℕ) : Entry β :=
  let e := scan (T.candidate i j) lo hi
  ⟨w i j + e.cost, e.root⟩

/-- Fill the diagonal of intervals `(i, i + d]` with `i + d ≤ n`, reading only `T`. -/
def diag (w : ℕ → ℕ → β) (W : Window β) (n d : ℕ) (T : Table β) : Table β :=
  (List.range (n + 1 - d)).foldl
    (fun U i => setCell d U i (cell w T i (i + d) (W.lo T i (i + d)) (W.hi T i (i + d)))) T

/-- The table after filling the diagonals `1, …, d`. -/
def table (w : ℕ → ℕ → β) (W : Window β) (n : ℕ) : ℕ → Table β
  | 0 => fun _ _ => ⟨0, 0⟩
  | d + 1 => diag w W n (d + 1) (table w W n d)

/-- Fill the table for the keys `1, …, n` and read off the cost and the tree. -/
def solve (w : ℕ → ℕ → β) (W : Window β) (n : ℕ) : Solution β :=
  let T := table w W n n
  ⟨(T 0 n).cost, buildTree (fun i j => (T i j).root) n 0 n⟩

/-- The cubic dynamic program for optimal binary search trees. -/
def plainBST (w : ℕ → ℕ → β) (n : ℕ) : Solution β := solve w .plain n

/-- Knuth's window dynamic program for optimal binary search trees. -/
def knuthBST (w : ℕ → ℕ → β) (n : ℕ) : Solution β := solve w .knuth n

/-! ### Correctness -/

/-- `T` holds the optimal cost and the largest optimal root of every interval `(a, b]` with
`b ≤ n` and `b - a ≤ d`. -/
def Agrees (w : ℕ → ℕ → β) (n d : ℕ) (T : Table β) : Prop :=
  ∀ a b, b ≤ n → b - a ≤ d → T a b = ⟨optCost w a b, optRoot w a b⟩

/-- A window is valid if, whenever the table is correct on shorter intervals, it lies inside
`(i, j]` and contains the largest optimal root. -/
def Window.Valid (W : Window β) (w : ℕ → ℕ → β) (n : ℕ) : Prop :=
  ∀ d T i, Agrees w n d T → i + d + 1 ≤ n →
    i < W.lo T i (i + d + 1) ∧ W.lo T i (i + d + 1) ≤ optRoot w i (i + d + 1) ∧
      optRoot w i (i + d + 1) ≤ W.hi T i (i + d + 1) ∧ W.hi T i (i + d + 1) ≤ i + d + 1

/-- Any entry satisfying `ScanInv (T.candidate i (i + d + 1)) lo hi` over a window containing
`optRoot w i (i + d + 1)` recovers both `optCost` and `optRoot`. -/
theorem entry_eq_opt_of_scanInv {w : ℕ → ℕ → β} {n d : ℕ} {T : Table β} (hT : Agrees w n d T)
    {i lo hi : ℕ} (hj : i + d + 1 ≤ n) (h₁ : i < lo) (h₂ : lo ≤ optRoot w i (i + d + 1))
    (h₃ : optRoot w i (i + d + 1) ≤ hi) (h₄ : hi ≤ i + d + 1)
    {e : Entry β} (he : ScanInv (T.candidate i (i + d + 1)) lo hi e) :
    (⟨w i (i + d + 1) + e.cost, e.root⟩ : Entry β) =
      ⟨optCost w i (i + d + 1), optRoot w i (i + d + 1)⟩ := by
  have hc : ∀ k, i < k → k ≤ i + d + 1 →
      T.candidate i (i + d + 1) k = splitCost w i (i + d + 1) k := by
    intro k hk₁ hk₂
    rw [Table.candidate, splitCost, hT i (k - 1) (by omega) (by omega),
      hT k (i + d + 1) hj (by omega)]
  obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := he
  have hopt := mem_Ioc.1 (optRoot_mem w (show i < i + d + 1 by omega))
  have hmin : ∀ k ∈ Ioc i (i + d + 1),
      splitCost w i (i + d + 1) e.root ≤ splitCost w i (i + d + 1) k := by
    intro k hk
    calc splitCost w i (i + d + 1) e.root = e.cost := by rw [e₃, hc _ (by omega) (by omega)]
      _ ≤ T.candidate i (i + d + 1) (optRoot w i (i + d + 1)) := e₄ _ h₂ h₃
      _ = splitCost w i (i + d + 1) (optRoot w i (i + d + 1)) := hc _ hopt.1 hopt.2
      _ ≤ splitCost w i (i + d + 1) k := splitCost_optRoot_le w hk
  have hle := le_optRoot w (mem_Ioc.2 ⟨by omega, by omega⟩) hmin
  have heq : e.root = optRoot w i (i + d + 1) := by
    refine le_antisymm hle (not_lt.1 fun hlt => ?_)
    have := e₅ _ hlt h₃
    rw [e₃, hc _ (by omega) (by omega), hc _ hopt.1 hopt.2] at this
    exact absurd (splitCost_optRoot_le w (mem_Ioc.2 ⟨by omega, by omega⟩)) (not_le.2 this)
  ext
  · rw [optCost_eq_optRoot w (by omega), ← heq, e₃, hc _ (by omega) (by omega)]
  · exact heq

/-- A scan over a window containing the largest optimal root computes the correct entry. -/
theorem cell_eq_opt {w : ℕ → ℕ → β} {n d : ℕ} {T : Table β} (hT : Agrees w n d T) {i lo hi : ℕ}
    (hj : i + d + 1 ≤ n) (h₁ : i < lo) (h₂ : lo ≤ optRoot w i (i + d + 1))
    (h₃ : optRoot w i (i + d + 1) ≤ hi) (h₄ : hi ≤ i + d + 1) :
    cell w T i (i + d + 1) lo hi = ⟨optCost w i (i + d + 1), optRoot w i (i + d + 1)⟩ :=
  entry_eq_opt_of_scanInv hT hj h₁ h₂ h₃ h₄ (scanInv_scan _ (h₂.trans h₃))

theorem agrees_diag {w : ℕ → ℕ → β} {W : Window β} {n d : ℕ} (hW : W.Valid w n) {T : Table β}
    (hT : Agrees w n d T) : Agrees w n (d + 1) (diag w W n (d + 1) T) := by
  intro a b hb hab
  rw [diag, foldl_setCell]
  split_ifs with h
  · obtain ⟨ha, rfl⟩ := h
    rw [List.mem_range] at ha
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hW d T a hT (by omega)
    exact cell_eq_opt hT (by omega) h₁ h₂ h₃ h₄
  · exact hT a b hb (not_lt.1 fun hc => h ⟨List.mem_range.2 (by omega), by omega⟩)

theorem agrees_table {w : ℕ → ℕ → β} {W : Window β} {n : ℕ} (hW : W.Valid w n) :
    ∀ d, Agrees w n d (table w W n d)
  | 0 => fun a b _ hab => by
    rw [optCost_of_le w (by omega), optRoot_of_le w (by omega)]
    rfl
  | d + 1 => agrees_diag hW (agrees_table hW d)

theorem Window.valid_plain (w : ℕ → ℕ → β) (n : ℕ) : (Window.plain : Window β).Valid w n := by
  intro d T i _ _
  have := mem_Ioc.1 (optRoot_mem w (show i < i + d + 1 by omega))
  exact ⟨Nat.lt_succ_self i, by simp only [Window.plain]; omega, this.2, le_rfl⟩

theorem solve_eq {w : ℕ → ℕ → β} {W : Window β} {n : ℕ} (hW : W.Valid w n) :
    solve w W n = ⟨optCost w 0 n, optTree w 0 n⟩ := by
  have hT := agrees_table hW n
  simp only [solve]
  generalize table w W n n = T at hT
  have hR : ∀ a b, 0 ≤ a → a < b → b ≤ n → (T a b).root = optRoot w a b := fun a b _ _ hb => by
    rw [hT a b hb (by omega)]
  rw [hT 0 n le_rfl (by omega), optTree, Nat.sub_zero,
    buildTree_congr (R' := optRoot w) hR fun a b _ hab hb => hR a b (Nat.zero_le a) hab hb ▸
      optRoot_mem w hab]

/-- **Correctness of the cubic dynamic program**, for every weight: it returns the optimal cost and
the tree read off the largest optimal roots. -/
theorem plainBST_eq (w : ℕ → ℕ → β) (n : ℕ) :
    plainBST w n = ⟨optCost w 0 n, optTree w 0 n⟩ :=
  solve_eq (Window.valid_plain w n)

end Algorithm

/-! ### Knuth's window validity and telescoping bound -/

section Knuth

variable [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]

/-- Under the quadrangle inequality and interval monotonicity, Knuth's window is valid. -/
theorem Window.valid_knuth {w : ℕ → ℕ → β} (hqi : QuadrangleIneq w)
    (hmono : MonotoneOnIntervals w) (n : ℕ) : (Window.knuth : Window β).Valid w n := by
  intro d T i hT hj
  have hopt := mem_Ioc.1 (optRoot_mem w (show i < i + d + 1 by omega))
  rcases d with _ | e
  · simp only [Window.knuth, add_zero, lt_irrefl, ↓reduceIte]
    simp only [add_zero] at hopt
    omega
  · have hmon := optRoot_mono hqi hmono (show i + 1 < i + (e + 1) + 1 by omega)
    have h₁ := mem_Ioc.1 (optRoot_mem w (show i < i + (e + 1) by omega))
    have h₂ := mem_Ioc.1 (optRoot_mem w (show i + 1 < i + (e + 1) + 1 by omega))
    simp only [Window.knuth, show i + 1 < i + (e + 1) + 1 by omega, ↓reduceIte,
      show i + (e + 1) + 1 - 1 = i + (e + 1) by omega] at hmon ⊢
    rw [hT i (i + (e + 1)) (by omega) (by omega), hT (i + 1) (i + (e + 1) + 1) hj (by omega)]
    dsimp only
    omega

/-- **Correctness of Knuth's algorithm** when the weight satisfies the quadrangle inequality and
is monotone on intervals. -/
theorem knuthBST_eq {w : ℕ → ℕ → β} (hqi : QuadrangleIneq w) (hmono : MonotoneOnIntervals w)
    (n : ℕ) : knuthBST w n = ⟨optCost w 0 n, optTree w 0 n⟩ :=
  solve_eq (Window.valid_knuth hqi hmono n)

private theorem sum_telescope (a : ℕ → ℕ) : ∀ m, (∀ i < m, a i ≤ a (i + 1)) →
    (∑ i ∈ range m, (a (i + 1) - a i + 1)) + a 0 = a m + m
  | 0, _ => by rw [sum_range_zero, zero_add, add_zero]
  | m + 1, h => by
    have ih := sum_telescope a m fun i hi => h i (by omega)
    have := h m (by omega)
    rw [sum_range_succ]
    omega

/-- **Knuth's telescoping bound**: under the quadrangle inequality and interval monotonicity, the
lengths of Knuth's candidate-root windows along diagonal `d + 1` sum to at most `2 n`. -/
theorem sum_knuth_window_le {w : ℕ → ℕ → β} (hqi : QuadrangleIneq w)
    (hmono : MonotoneOnIntervals w) {n d : ℕ} {T : Table β} (hT : Agrees w n d T) :
    ∑ i ∈ range (n + 1 - (d + 1)),
      ((Window.knuth : Window β).hi T i (i + (d + 1)) -
        (Window.knuth : Window β).lo T i (i + (d + 1)) + 1) ≤ 2 * n := by
  rcases d with _ | e
  · simp only [Window.knuth, zero_add, lt_irrefl, ↓reduceIte, Nat.sub_self,
      sum_const, card_range, Nat.nsmul_eq_mul, mul_one]
    omega
  · set m := n + 1 - (e + 1 + 1) with hm
    let a : ℕ → ℕ := fun i => optRoot w i (i + e + 1)
    have hterm : ∀ i ∈ range m, (Window.knuth : Window β).hi T i (i + (e + 1 + 1)) -
        (Window.knuth : Window β).lo T i (i + (e + 1 + 1)) + 1 = a (i + 1) - a i + 1 := by
      intro i hi
      rw [mem_range] at hi
      rw [show i + (e + 1 + 1) = (i + 1) + e + 1 by omega]
      simp only [Window.knuth, show i + 1 < (i + 1) + e + 1 by omega, ↓reduceIte,
        show (i + 1) + e + 1 - 1 = i + e + 1 by omega]
      rw [hT i (i + e + 1) (by omega) (by omega),
        hT (i + 1) ((i + 1) + e + 1) (by omega) (by omega)]
    rw [sum_congr rfl hterm]
    have ha : ∀ i < m, a i ≤ a (i + 1) := fun i _ => by
      have hmon := optRoot_mono hqi hmono (show i + 1 < (i + 1) + e + 1 by omega)
      rw [show (i + 1) + e + 1 - 1 = i + e + 1 by omega] at hmon
      exact hmon.1.trans hmon.2
    have htel := sum_telescope a m ha
    rcases Nat.eq_zero_or_pos m with hm0 | hm₀
    · rw [hm0, sum_range_zero]; omega
    · have h₀ := mem_Ioc.1 (optRoot_mem w (show 0 < 0 + e + 1 by omega))
      have hm' := mem_Ioc.1 (optRoot_mem w (show m < m + e + 1 by omega))
      dsimp only [a] at htel ⊢
      omega

end Knuth

/-! ### Cost bounds and optimality of the output -/

section Optimal

variable [AddCommMonoid β] [LinearOrder β]

/-- `optCost w i j` depends on `w` only through nonempty subintervals `(a, b]` inside `(i, j]`. -/
theorem optCost_congr {w₁ w₂ : ℕ → ℕ → β} {i j : ℕ}
    (h : ∀ a b, i ≤ a → a < b → b ≤ j → w₁ a b = w₂ a b) :
    optCost w₁ i j = optCost w₂ i j := by
  suffices H : ∀ f a b, (∀ x y, a ≤ x → x < y → y ≤ b → w₁ x y = w₂ x y) →
      optCostAux w₁ f a b = optCostAux w₂ f a b from H (j - i) i j h
  intro f
  induction f with
  | zero => intros; rfl
  | succ f ih =>
    intro a b hab
    simp only [optCostAux]
    split_ifs with hlt
    · rw [hab a b le_rfl hlt le_rfl]
      congr 1
      refine inf'_congr _ rfl fun k hk => ?_
      rw [mem_Ioc] at hk
      rw [ih a (k - 1) fun x y h₁ h₂ h₃ => hab x y h₁ h₂ (by omega),
        ih k b fun x y h₁ h₂ h₃ => hab x y (by omega) h₂ h₃]
    · rfl

section OrderedBound

variable [IsOrderedAddMonoid β]

/-- If every nonempty subinterval `(a, b]` with `i ≤ a < b ≤ j` has weight at most `M`, then
`optCost w i j ≤ (j - i) • M` (attained, up to bound, by the right-spine tree). -/
theorem optCost_le_nsmul {w : ℕ → ℕ → β} {M : β} {i j : ℕ}
    (hw : ∀ a b, i ≤ a → a < b → b ≤ j → w a b ≤ M) :
    optCost w i j ≤ (j - i) • M := by
  generalize hd : j - i = d
  induction d generalizing i j with
  | zero => rw [optCost_of_le w (by omega), zero_nsmul]
  | succ d ih =>
    have hij : i < j := by omega
    have hle := optCost_le w (k := i + 1) (mem_Ioc.2 ⟨Nat.lt_succ_self i, hij⟩)
    rw [splitCost, Nat.add_sub_cancel, optCost_of_le w le_rfl, zero_add] at hle
    have hih := ih (i := i + 1) (j := j) (fun a b h₁ h₂ h₃ => hw a b (by omega) h₂ h₃) (by omega)
    calc optCost w i j ≤ w i j + optCost w (i + 1) j := hle
      _ ≤ M + d • M := add_le_add (hw i j le_rfl hij le_rfl) hih
      _ = (d + 1) • M := (succ_nsmul' M d).symm

/-- A solution for the keys `1, …, n` is optimal for the weight `w` if its tree is a binary search
tree on these keys of the returned cost, and no binary search tree on them is cheaper. -/
def Solution.IsOptimal (w : ℕ → ℕ → β) (n : ℕ) (s : Solution β) : Prop :=
  IsBST 0 n s.tree ∧ treeCost w 0 n s.tree = s.cost ∧ ∀ t, IsBST 0 n t → s.cost ≤ treeCost w 0 n t

theorem isOptimal_optTree (w : ℕ → ℕ → β) (n : ℕ) :
    (⟨optCost w 0 n, optTree w 0 n⟩ : Solution β).IsOptimal w n :=
  ⟨isBST_optTree w (Nat.zero_le n), treeCost_optTree w (Nat.zero_le n),
    fun _ ht => optCost_le_treeCost w ht⟩

/-- The cubic dynamic program returns an optimal binary search tree, for every weight. -/
theorem isOptimal_plainBST (w : ℕ → ℕ → β) (n : ℕ) : (plainBST w n).IsOptimal w n := by
  rw [plainBST_eq]
  exact isOptimal_optTree w n

end OrderedBound

end Optimal

section OptimalKnuth

variable [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]

/-- Knuth's algorithm returns an optimal binary search tree when the weight satisfies the
quadrangle inequality and is monotone on intervals. -/
theorem isOptimal_knuthBST {w : ℕ → ℕ → β} (hqi : QuadrangleIneq w)
    (hmono : MonotoneOnIntervals w) (n : ℕ) : (knuthBST w n).IsOptimal w n := by
  rw [knuthBST_eq hqi hmono]
  exact isOptimal_optTree w n

/-- **Knuth's theorem** for nonnegative access weights `p` and failure weights `q`: the window
algorithm returns an optimal binary search tree. -/
theorem knuthBST_knuthWeight {p q : ℕ → β} (hp : ∀ k, 0 ≤ p k) (hq : ∀ g, 0 ≤ q g) (n : ℕ) :
    (knuthBST (knuthWeight p q) n).IsOptimal (knuthWeight p q) n :=
  isOptimal_knuthBST (quadrangleIneq_knuthWeight p q) (monotoneOnIntervals_knuthWeight hp hq) n

end OptimalKnuth

end Cslib.Algorithms.Lean.OptimalBST
