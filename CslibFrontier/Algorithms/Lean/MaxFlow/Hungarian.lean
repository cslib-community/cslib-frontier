/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.HopcroftKarp
public import CslibFrontier.Algorithms.Lean.MaxFlow.WeightedMatching
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Int

/-!
# The Hungarian Method for the Assignment Problem

A pure executable implementation of the **Hungarian method** for the `n × n` assignment problem
with integer costs `c : Fin n × Fin n → ℤ` ([Kuhn1955]; [Munkres1957]; [CLRS2022], §25.3),
growing one alternating tree per row and maintaining a column slack table (the reduced-cost
technique of [EdmondsKarp1972]). It returns a minimum-cost perfect matching together with integral
feasible potentials whose total equals the cost, proving Egerváry's min–max theorem for the
assignment problem ([Schrijver2003], Ch. 17). The `O(n³)` Word-RAM implementation and running-time
bound live in `CslibFrontier.Algorithms.WordRAM.Hungarian`.

## Algorithm and source mapping

Costs are minimized. Row potentials `y`, column potentials `z` and the matching (a column-indexed
mate table `mate`, as in `CslibFrontier.Algorithms.Lean.MaxFlow.HopcroftKarp`) are kept with every
reduced cost `hgRed c y z u v = c (u, v) - y u - z v` nonnegative and every matched edge tight
(reduced cost `0`).

1. **Row reduction:** `y u = min_v c (u, v)` and `z = 0` give feasible potentials.
2. **One phase per row `r` (`hgPhase`):** the alternating tree is grown from the free row `r`.
   `minv j` is the least reduced cost from a tree row to the non-tree column `j`, and `path j` is
   the alternating path from `r` to `j` that attains it. Each round of `hgLoop` picks the
   non-tree column `j₁` of least slack `δ`, then raises the tree rows and lowers the tree columns
   by `δ` (`hgDual`), which keeps feasibility and makes the last edge to `j₁` tight. If `j₁` is
   free, the matching is augmented along `path j₁`. This is an augmenting path in the sense of
   `CslibFrontier.Algorithms.Lean.MaxFlow.AugmentingPath`, so `r` becomes matched. Otherwise `j₁`
   and its mate join the tree and the slacks are relaxed through the new row (`hgExtend`). A round
   that does not augment adds a matched column to the tree, so the phase augments within `n`
   rounds.
3. **Certificate:** after `n` phases the matching is perfect and tight for feasible potentials, so
   weak duality and complementary slackness
   (`CslibFrontier.Algorithms.Lean.MaxFlow.WeightedMatching`)
   show that it has minimum cost and that its cost is `∑ y + ∑ z`.

## Scope

Square instances of the complete bipartite graph with integer costs. Rectangular instances and
forbidden edges have to be encoded by padding and by large costs. Maximum-weight assignment is
obtained by negating costs.

## Main definitions

* `hgRowMin`, `hgRed`: row minima and reduced costs; `HgState`: the state of a phase.
* `hgArgmin`, `hgDual`, `hgRelax`, `hgExtend`, `hgApplyEdges`, `hgInit`, `hgLoop`, `hgPhase`,
  `hgRows`: the steps of one phase and the loop over rows.
* `HungarianOutput`, `hungarian`: the full algorithm.
* `HgOuterBound`, `HgStepInv`: bounded potential, slack, and predecessor-tree invariants on
  nonnegative costs `0 ≤ c (u, v) ≤ W`, used by the Word-RAM implementation.

## Main results

* `hungarian_correct`: the output matching is a minimum-cost perfect matching
  (`IsMinCostPerfectMatching`), the output potentials are feasible (`IsFeasiblePotential`), and
  the matching cost equals the total potential.
* `hungarian_add_const`: adding a uniform constant `S` to all costs shifts row potentials by `S`
  and leaves column potentials and the returned matching unchanged.
* `exists_isMinCostPerfectMatching_potential_eq` (**Egerváry's theorem**, integral form), and
  `isMinCostPerfectMatching_iff_exists_potential` (min–max form): a perfect matching has minimum
  cost iff some integral feasible potentials have total equal to its cost.
* `exists_perm_assignment`: the permutation form `min_σ ∑ u, c (u, σ u) = max (∑ y + ∑ z)`.

## References

* [H. W. Kuhn, *The Hungarian Method for the Assignment Problem*][Kuhn1955]
* [J. Munkres, *Algorithms for the Assignment and Transportation Problems*][Munkres1957]
* [J. Edmonds and R. M. Karp, *Theoretical Improvements in Algorithmic Efficiency for Network Flow
  Problems*][EdmondsKarp1972]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*, 4th ed.][CLRS2022]
* [A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*][Schrijver2003]
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

/-! ### Algorithm -/

section Algorithm

variable {n : ℕ}

/-- Minimum of row `u` of `c`, scanning all `n` columns. -/
@[expose] def hgRowMin (c : Fin n × Fin n → ℤ) (u : Fin n) : ℤ :=
  (List.finRange n).foldl (fun a v => min a (c (u, v))) (c (u, u))

/-- Reduced cost `c (u, v) - y u - z v`. -/
@[expose] def hgRed (c : Fin n × Fin n → ℤ) (y z : Vector ℤ n) (u v : Fin n) : ℤ :=
  c (u, v) - vget y u - vget z v

/-- State of one phase of the Hungarian method (growing an alternating tree from one root). -/
structure HgState (n : ℕ) where
  /-- Row potentials. -/
  y : Vector ℤ n
  /-- Column potentials. -/
  z : Vector ℤ n
  /-- Matched row of each column. -/
  mate : Vector (Option (Fin n)) n
  /-- Columns already in the tree. -/
  used : Vector Bool n
  /-- Rows in the tree. -/
  tree : Vector Bool n
  /-- Slack of each column not in the tree: its minimum reduced cost from a tree row. -/
  minv : Vector ℤ n
  /-- For each column, the tree path reaching it, as `(row, column)` edges, last edge first. -/
  path : Vector (List (Fin n × Fin n)) n

/-- One argmin scan step: keep the unused column of smaller slack. -/
@[expose] def hgArgminStep (s : HgState n) (b : Option (Fin n)) (j : Fin n) : Option (Fin n) :=
  if vget s.used j then b
  else match b with
    | none => some j
    | some k => if vget s.minv j < vget s.minv k then some j else some k

/-- Unused column of minimum slack. -/
@[expose] def hgArgmin (s : HgState n) : Option (Fin n) :=
  (List.finRange n).foldl (hgArgminStep s) none

/-- Dual adjustment by `δ`: raise tree rows, lower tree columns, reduce the slack of the other
columns. -/
@[expose] def hgDual (s : HgState n) (δ : ℤ) : HgState n :=
  { s with
    y := Vector.ofFn fun i => if vget s.tree i then vget s.y i + δ else vget s.y i
    z := Vector.ofFn fun j => if vget s.used j then vget s.z j - δ else vget s.z j
    minv := Vector.ofFn fun j => if vget s.used j then vget s.minv j else vget s.minv j - δ }

/-- Relax the slacks of the unused columns through the new tree row `i`, the mate of the column
`j₁` just added to the tree. -/
@[expose] def hgRelax (s : HgState n) (c : Fin n × Fin n → ℤ) (i j₁ : Fin n) : HgState n :=
  { s with
    minv := Vector.ofFn fun j =>
      if vget s.used j then vget s.minv j else min (vget s.minv j) (hgRed c s.y s.z i j)
    path := Vector.ofFn fun j =>
      if !vget s.used j && decide (hgRed c s.y s.z i j < vget s.minv j) then
        (i, j) :: vget s.path j₁
      else vget s.path j }

/-- Initial state of the phase rooted at the free row `r`. -/
@[expose] def hgInit (c : Fin n × Fin n → ℤ) (y z : Vector ℤ n) (mate : Vector (Option (Fin n)) n)
    (r : Fin n) : HgState n :=
  ⟨y, z, mate, Vector.replicate n false, Vector.ofFn fun i => decide (i = r),
    Vector.ofFn fun j => hgRed c y z r j, Vector.ofFn fun j => [(r, j)]⟩

/-- Add the column `j₁` and its mate `i₀` to the tree, then relax through `i₀`. -/
@[expose] def hgExtend (c : Fin n × Fin n → ℤ) (s : HgState n) (j₁ i₀ : Fin n) : HgState n :=
  hgRelax { s with used := vset s.used j₁ true, tree := vset s.tree i₀ true } c i₀ j₁

/-- Rematch the right end of every edge of `es` to its left end. -/
@[expose] def hgApplyEdges (mate : Vector (Option (Fin n)) n) (es : List (Fin n × Fin n)) :
    Vector (Option (Fin n)) n :=
  es.foldl (fun mt e => vset mt e.2 (some e.1)) mate

/-- The tree-growing loop of one phase: pick the unused column `j₁` of minimum slack `δ`, adjust
the potentials by `δ`, then augment along the tree path of `j₁` if it is free, or add `j₁` and its
mate to the tree and relax. -/
@[expose] def hgLoop (c : Fin n × Fin n → ℤ) : ℕ → HgState n → HgState n
  | 0, s => s
  | fuel + 1, s =>
    match hgArgmin s with
    | none => s
    | some j₁ =>
      let s := hgDual s (vget s.minv j₁)
      match vget s.mate j₁ with
      | none => { s with mate := hgApplyEdges s.mate (vget s.path j₁) }
      | some i₀ => hgLoop c fuel (hgExtend c s j₁ i₀)

/-- One phase: augment the matching by one edge from the free row `r`. -/
@[expose] def hgPhase (c : Fin n × Fin n → ℤ) (y z : Vector ℤ n)
    (mate : Vector (Option (Fin n)) n) (r : Fin n) : HgState n :=
  hgLoop c n (hgInit c y z mate r)

/-- Run one phase per row of the list. -/
@[expose] def hgRows (c : Fin n × Fin n → ℤ) : List (Fin n) → HgState n → HgState n
  | [], s => s
  | r :: rs, s => hgRows c rs (hgPhase c s.y s.z s.mate r)

/-- Phase state before the first phase: potentials `y`, `z` and matching `mate`, with an empty
tree. -/
@[expose] def hgStartState (y z : Vector ℤ n) (mate : Vector (Option (Fin n)) n) : HgState n :=
  ⟨y, z, mate, mate.map fun _ => false, mate.map fun _ => false, z, mate.map fun _ => []⟩

end Algorithm

/-- Output of the Hungarian method: a perfect matching and potentials certifying its optimality. -/
structure HungarianOutput (n : ℕ) where
  /-- The perfect matching. -/
  matching : Finset (Fin n × Fin n)
  /-- Row potentials. -/
  y : Fin n → ℤ
  /-- Column potentials. -/
  z : Fin n → ℤ

/-- **The Hungarian method** for the `n × n` assignment problem with integer costs `c`: row
reduction, then one alternating-tree phase per row, then extraction of the matching. -/
@[expose] def hungarian {n : ℕ} (c : Fin n × Fin n → ℤ) : HungarianOutput n :=
  let y := Vector.ofFn (hgRowMin c)
  let z := Vector.replicate n 0
  let mate := Vector.replicate n none
  let s := hgRows c (List.finRange n) (hgStartState y z mate)
  let matching := (List.finRange n).foldl (hkMatchingStep s.mate) ∅
  ⟨matching, vget s.y, vget s.z⟩

/-! ### Specification of the phase steps -/

section Spec

variable {n : ℕ} {c : Fin n × Fin n → ℤ}

/-- Invariant of the argmin scan after the columns `S`. -/
private def HgArgminOK (s : HgState n) (S : List (Fin n)) (b : Option (Fin n)) : Prop :=
  (b = none → ∀ j ∈ S, vget s.used j = true) ∧
    ∀ k, b = some k → vget s.used k = false ∧ ∀ j ∈ S, vget s.used j = false →
      vget s.minv k ≤ vget s.minv j

private theorem hgArgminOK_nil (s : HgState n) : HgArgminOK s [] none := by
  unfold HgArgminOK
  simp

private theorem hgArgmin_foldl (s : HgState n) (l : List (Fin n)) :
    ∀ (S : List (Fin n)) (b : Option (Fin n)), HgArgminOK s S b →
      HgArgminOK s (S ++ l) (l.foldl (hgArgminStep s) b) := by
  induction l with
  | nil => intro S b h; simpa using h
  | cons x l ih =>
    intro S b h
    rw [List.foldl_cons, show S ++ x :: l = (S ++ [x]) ++ l by simp]
    apply ih
    unfold HgArgminOK at h ⊢
    unfold hgArgminStep
    by_cases hx : vget s.used x = true
    · rw [ite_eq_left hx]
      refine ⟨fun hb j hj => ?_, fun k hk => ?_⟩
      · rcases List.mem_append.mp hj with hj | hj
        · exact h.1 hb j hj
        · exact List.mem_singleton.mp hj ▸ hx
      · obtain ⟨hk1, hk2⟩ := h.2 k hk
        refine ⟨hk1, fun j hj hju => ?_⟩
        rcases List.mem_append.mp hj with hj | hj
        · exact hk2 j hj hju
        · exact absurd ((List.mem_singleton.mp hj ▸ hju).symm.trans hx) Bool.noConfusion
    · rw [ite_eq_right hx]
      have hx' : vget s.used x = false := Bool.eq_false_iff.mpr hx
      cases b with
      | none =>
        refine ⟨(fun hb => nomatch hb), fun k hk => ?_⟩
        cases hk
        refine ⟨hx', fun j hj hju => ?_⟩
        rcases List.mem_append.mp hj with hj | hj
        · exact absurd (hju.symm.trans (h.1 rfl j hj)) Bool.noConfusion
        · rw [List.mem_singleton.mp hj]
      | some k₀ =>
        obtain ⟨hk1, hk2⟩ := h.2 k₀ rfl
        dsimp only
        split_ifs with hlt
        · refine ⟨(fun hb => nomatch hb), fun k hk => ?_⟩
          cases hk
          refine ⟨hx', fun j hj hju => ?_⟩
          rcases List.mem_append.mp hj with hj | hj
          · exact hlt.le.trans (hk2 j hj hju)
          · rw [List.mem_singleton.mp hj]
        · refine ⟨(fun hb => nomatch hb), fun k hk => ?_⟩
          cases hk
          refine ⟨hk1, fun j hj hju => ?_⟩
          rcases List.mem_append.mp hj with hj | hj
          · exact hk2 j hj hju
          · exact List.mem_singleton.mp hj ▸ not_lt.mp hlt

theorem hgArgmin_none {s : HgState n} (h : hgArgmin s = none) :
    ∀ j, vget s.used j = true :=
  fun j => (hgArgmin_foldl s (List.finRange n) [] none (hgArgminOK_nil s)).1 h j (by simp)

theorem hgArgmin_some {s : HgState n} {k : Fin n} (h : hgArgmin s = some k) :
    vget s.used k = false ∧ ∀ j, vget s.used j = false → vget s.minv k ≤ vget s.minv j := by
  obtain ⟨h1, h2⟩ := (hgArgmin_foldl s (List.finRange n) [] none (hgArgminOK_nil s)).2 k h
  exact ⟨h1, fun j hj => h2 j (by simp) hj⟩

/-! #### Field lemmas -/

@[simp] theorem hgDual_mate (s : HgState n) (δ : ℤ) : (hgDual s δ).mate = s.mate := rfl
@[simp] theorem hgDual_used (s : HgState n) (δ : ℤ) : (hgDual s δ).used = s.used := rfl
@[simp] theorem hgDual_tree (s : HgState n) (δ : ℤ) : (hgDual s δ).tree = s.tree := rfl
@[simp] theorem hgDual_path (s : HgState n) (δ : ℤ) : (hgDual s δ).path = s.path := rfl

theorem hgDual_y (s : HgState n) (δ : ℤ) (i : Fin n) :
    vget (hgDual s δ).y i = if vget s.tree i = true then vget s.y i + δ else vget s.y i := by
  simp [hgDual, vget]

theorem hgDual_z (s : HgState n) (δ : ℤ) (j : Fin n) :
    vget (hgDual s δ).z j = if vget s.used j = true then vget s.z j - δ else vget s.z j := by
  simp [hgDual, vget]

theorem hgDual_minv (s : HgState n) (δ : ℤ) (j : Fin n) :
    vget (hgDual s δ).minv j =
      if vget s.used j = true then vget s.minv j else vget s.minv j - δ := by
  simp [hgDual, vget]

@[simp] theorem hgRelax_y (s : HgState n) (i j₁ : Fin n) : (hgRelax s c i j₁).y = s.y := rfl
@[simp] theorem hgRelax_z (s : HgState n) (i j₁ : Fin n) : (hgRelax s c i j₁).z = s.z := rfl
@[simp] theorem hgRelax_mate (s : HgState n) (i j₁ : Fin n) :
    (hgRelax s c i j₁).mate = s.mate := rfl
@[simp] theorem hgRelax_used (s : HgState n) (i j₁ : Fin n) :
    (hgRelax s c i j₁).used = s.used := rfl
@[simp] theorem hgRelax_tree (s : HgState n) (i j₁ : Fin n) :
    (hgRelax s c i j₁).tree = s.tree := rfl

theorem hgRelax_minv (s : HgState n) (i j₁ j : Fin n) :
    vget (hgRelax s c i j₁).minv j =
      if vget s.used j = true then vget s.minv j
      else min (vget s.minv j) (hgRed c s.y s.z i j) := by
  simp [hgRelax, vget]

theorem hgRelax_path (s : HgState n) (i j₁ j : Fin n) :
    vget (hgRelax s c i j₁).path j =
      if vget s.used j = false ∧ hgRed c s.y s.z i j < vget s.minv j then
        (i, j) :: vget s.path j₁
      else vget s.path j := by
  simp only [hgRelax, vget, Vector.getElem_ofFn, Fin.eta]
  exact if_congr ((Bool.and_eq_true _ _).to_iff.trans (and_congr (Bool.not_eq_true' _).to_iff
    decide_eq_true_iff)) rfl rfl

@[simp] theorem hgInit_y (y z : Vector ℤ n) (mate : Vector (Option (Fin n)) n) (r : Fin n) :
    (hgInit c y z mate r).y = y := rfl
@[simp] theorem hgInit_z (y z : Vector ℤ n) (mate : Vector (Option (Fin n)) n) (r : Fin n) :
    (hgInit c y z mate r).z = z := rfl
@[simp] theorem hgInit_mate (y z : Vector ℤ n) (mate : Vector (Option (Fin n)) n) (r : Fin n) :
    (hgInit c y z mate r).mate = mate := rfl

theorem hgInit_used (y z : Vector ℤ n) (mate : Vector (Option (Fin n)) n) (r j : Fin n) :
    vget (hgInit c y z mate r).used j = false := by
  simp [hgInit, vget]

theorem hgInit_tree (y z : Vector ℤ n) (mate : Vector (Option (Fin n)) n) (r i : Fin n) :
    vget (hgInit c y z mate r).tree i = decide (i = r) := by
  simp [hgInit, vget]

theorem hgInit_minv (y z : Vector ℤ n) (mate : Vector (Option (Fin n)) n) (r j : Fin n) :
    vget (hgInit c y z mate r).minv j = hgRed c y z r j := by
  simp [hgInit, vget]

theorem hgInit_path (y z : Vector ℤ n) (mate : Vector (Option (Fin n)) n) (r j : Fin n) :
    vget (hgInit c y z mate r).path j = [(r, j)] := by
  simp [hgInit, vget]

/-! #### Invariants -/

/-- `q` is the stored tree path of column `j` (last edge first): it starts at the root `r`, ends
at `j`, alternates through matched edges, has tight tail edges inside the tree, and its last edge
has reduced cost `0` if `j` is in the tree and `minv j` otherwise. -/
structure HgPath (c : Fin n × Fin n → ℤ) (y z : Vector ℤ n)
    (mate : Vector (Option (Fin n)) n) (used tree : Vector Bool n) (minv : Vector ℤ n)
    (r j : Fin n) (q : List (Fin n × Fin n)) : Prop where
  /-- Stored tree paths are nonempty. -/
  ne_nil : q ≠ []
  /-- The head edge ends at `j` and attains `0` (if `j` is in the tree) or `minv j` (otherwise). -/
  head : ∀ e ∈ q.head?, e.2 = j ∧
    hgRed c y z e.1 e.2 = if vget used j = true then 0 else vget minv j
  /-- The last edge (first in root-to-`j` order) starts at the root `r`. -/
  last : ∀ e ∈ q.getLast?, e.1 = r
  /-- Consecutive edges alternate through matched edges of `mate`. -/
  chain : q.IsChain fun a b => vget mate b.2 = some a.1
  /-- Left endpoints along `q` are distinct. -/
  nodup_fst : (q.map Prod.fst).Nodup
  /-- Right endpoints along `q` are distinct. -/
  nodup_snd : (q.map Prod.snd).Nodup
  /-- Tail edges are tight and end at columns already in the tree. -/
  tail : ∀ e ∈ q.tail, hgRed c y z e.1 e.2 = 0 ∧ vget used e.2 = true
  /-- Every left endpoint along `q` belongs to the tree. -/
  tree : ∀ e ∈ q, vget tree e.1 = true

/-- Invariant of the tree-growing loop of the phase rooted at `r`. -/
structure HgInv (c : Fin n × Fin n → ℤ) (r : Fin n) (y z : Vector ℤ n)
    (mate : Vector (Option (Fin n)) n) (used tree : Vector Bool n) (minv : Vector ℤ n)
    (path : Vector (List (Fin n × Fin n)) n) : Prop where
  /-- `mate` encodes a valid matching. -/
  matching : IsMatching (fun _ => true) (mateMatching mate)
  /-- Potentials `y`, `z` are feasible. -/
  feas : ∀ i j, 0 ≤ hgRed c y z i j
  /-- Matched edges are tight. -/
  tight : ∀ i j, vget mate j = some i → hgRed c y z i j = 0
  /-- The phase root `r` is currently unmatched. -/
  root_free : ∀ j, vget mate j ≠ some r
  /-- Every column in `used` is matched. -/
  used_mate : ∀ j, vget used j = true → ∃ i, vget mate j = some i
  /-- A row is in `tree` iff it is `r` or matched to a column in `used`. -/
  tree_iff : ∀ i, vget tree i = true ↔ i = r ∨ ∃ j, vget used j = true ∧ vget mate j = some i
  /-- `minv j` bounds every reduced cost from a tree row to an unused column `j`. -/
  minv_le : ∀ i j, vget tree i = true → vget used j = false → vget minv j ≤ hgRed c y z i j
  /-- Every column `j` has a valid alternating path from `r` in `path`. -/
  path_ok : ∀ j, HgPath c y z mate used tree minv r j (vget path j)

/-- Invariant between phases. -/
structure HgOuter (c : Fin n × Fin n → ℤ) (y z : Vector ℤ n)
    (mate : Vector (Option (Fin n)) n) : Prop where
  /-- `mate` encodes a valid matching. -/
  matching : IsMatching (fun _ => true) (mateMatching mate)
  /-- Potentials `y`, `z` are feasible. -/
  feas : ∀ i j, 0 ≤ hgRed c y z i j
  /-- Matched edges are tight. -/
  tight : ∀ i j, vget mate j = some i → hgRed c y z i j = 0

private theorem mate_inj {mate : Vector (Option (Fin n)) n}
    (hM : IsMatching (fun _ => true) (mateMatching mate)) {i : Fin n} {j j' : Fin n}
    (h : vget mate j = some i) (h' : vget mate j' = some i) : j = j' :=
  hM.2.1 i j j' (mem_mateMatching.mpr h) (mem_mateMatching.mpr h')

section InvLemmas

variable {r : Fin n} {y z : Vector ℤ n} {mate : Vector (Option (Fin n)) n}
  {used tree : Vector Bool n} {minv : Vector ℤ n} {path : Vector (List (Fin n × Fin n)) n}

theorem HgInv.tree_iff_used (h : HgInv c r y z mate used tree minv path) {i j : Fin n}
    (hm : vget mate j = some i) : vget tree i = true ↔ vget used j = true := by
  rw [h.tree_iff]
  constructor
  · rintro (rfl | ⟨j', hj', hm'⟩)
    · exact absurd hm (h.root_free j)
    · rwa [mate_inj h.matching hm hm']
  · exact fun hj => .inr ⟨j, hj, hm⟩

theorem HgInv.minv_nonneg (h : HgInv c r y z mate used tree minv path) {j : Fin n}
    (hj : vget used j = false) : 0 ≤ vget minv j := by
  obtain ⟨e, l, hq⟩ := List.exists_cons_of_ne_nil (h.path_ok j).ne_nil
  obtain ⟨_, h2⟩ := (h.path_ok j).head e (by simp [hq])
  rw [hj, ite_eq_right Bool.false_ne_true] at h2
  exact h2 ▸ h.feas _ _

private theorem HgPath.mem_cases {used tree : Vector Bool n} {minv : Vector ℤ n} {j : Fin n}
    {q : List (Fin n × Fin n)} (hp : HgPath c y z mate used tree minv r j q) {e : Fin n × Fin n}
    (he : e ∈ q) : e.2 = j ∨ vget used e.2 = true := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hp.ne_nil
  rcases List.mem_cons.mp he with rfl | he
  · exact .inl (hp.head e rfl).1
  · exact .inr (hp.tail e he).2

end InvLemmas

/-! #### The dual adjustment -/

private theorem hgRed_dual (s : HgState n) (δ : ℤ) (i j : Fin n) :
    hgRed c (hgDual s δ).y (hgDual s δ).z i j =
      hgRed c s.y s.z i j - (if vget s.tree i = true then δ else 0) +
        (if vget s.used j = true then δ else 0) := by
  unfold hgRed
  rw [hgDual_y, hgDual_z]
  split_ifs <;> omega

theorem hgInv_dual {r : Fin n} {s : HgState n}
    (h : HgInv c r s.y s.z s.mate s.used s.tree s.minv s.path) {j₁ : Fin n}
    (hj₁ : vget s.used j₁ = false)
    (hmin : ∀ j, vget s.used j = false → vget s.minv j₁ ≤ vget s.minv j) :
    HgInv c r (hgDual s (vget s.minv j₁)).y (hgDual s (vget s.minv j₁)).z s.mate s.used
      s.tree (hgDual s (vget s.minv j₁)).minv s.path := by
  have hδ : 0 ≤ vget s.minv j₁ := h.minv_nonneg hj₁
  refine ⟨h.matching, fun i j => ?_, fun i j hm => ?_, h.root_free, h.used_mate, h.tree_iff,
    fun i j hi hj => ?_, fun j => ?_⟩
  · rw [hgRed_dual]
    have := h.feas i j
    by_cases hi : vget s.tree i = true <;> by_cases hj : vget s.used j = true
    · rw [ite_eq_left hi, ite_eq_left hj]; omega
    · rw [ite_eq_left hi, ite_eq_right hj]
      have h1 := h.minv_le i j hi (Bool.eq_false_iff.mpr hj)
      have h2 := hmin j (Bool.eq_false_iff.mpr hj)
      omega
    · rw [ite_eq_right hi, ite_eq_left hj]; omega
    · rw [ite_eq_right hi, ite_eq_right hj]; omega
  · rw [hgRed_dual, h.tight i j hm]
    have hiff := h.tree_iff_used hm
    by_cases hj : vget s.used j = true
    · rw [ite_eq_left (hiff.mpr hj), ite_eq_left hj]; omega
    · rw [ite_eq_right (fun hi => hj (hiff.mp hi)), ite_eq_right hj]; omega
  · rw [hgDual_minv, hgRed_dual, ite_eq_left hi, hj, ite_eq_right Bool.false_ne_true,
      ite_eq_right Bool.false_ne_true]
    have := h.minv_le i j hi hj
    omega
  · have hp := h.path_ok j
    refine ⟨hp.ne_nil, fun e he => ?_, hp.last, hp.chain, hp.nodup_fst, hp.nodup_snd,
      fun e he => ?_, hp.tree⟩
    · obtain ⟨h1, h2⟩ := hp.head e he
      refine ⟨h1, ?_⟩
      have het := hp.tree e (List.mem_of_mem_head? he)
      rw [hgRed_dual, h2, ite_eq_left het, hgDual_minv, h1]
      split_ifs <;> omega
    · obtain ⟨h1, h2⟩ := hp.tail e he
      have het := hp.tree e (List.mem_of_mem_tail he)
      refine ⟨?_, h2⟩
      rw [hgRed_dual, h1, ite_eq_left het, ite_eq_left h2]
      omega

theorem minv_dual_self (s : HgState n) {j₁ : Fin n} (hj₁ : vget s.used j₁ = false) :
    vget (hgDual s (vget s.minv j₁)).minv j₁ = 0 := by
  rw [hgDual_minv, hj₁, ite_eq_right Bool.false_ne_true, sub_self]

/-! #### Augmenting along a tree path -/

theorem hgAugment {r : Fin n} {y z : Vector ℤ n} {mate : Vector (Option (Fin n)) n}
    {used tree : Vector Bool n} {minv : Vector ℤ n} {path : Vector (List (Fin n × Fin n)) n}
    (h : HgInv c r y z mate used tree minv path) {j₁ : Fin n} (hj₁ : vget used j₁ = false)
    (hz : vget minv j₁ = 0) (hfree : vget mate j₁ = none) :
    HgOuter c y z (hgApplyEdges mate (vget path j₁)) ∧
      matchedLeft (mateMatching (hgApplyEdges mate (vget path j₁))) =
        insert r (matchedLeft (mateMatching mate)) := by
  have hq := h.path_ok j₁
  have hp : IsAugmentingPath (fun _ => true) (mateMatching mate) (vget path j₁).reverse := by
    refine ⟨List.reverse_ne_nil_iff.mpr hq.ne_nil, fun _ _ => rfl,
      by simpa only [List.map_reverse, List.nodup_reverse] using hq.nodup_fst,
      by simpa only [List.map_reverse, List.nodup_reverse] using hq.nodup_snd,
      fun e he hr => ?_, fun e he hv => ?_, ?_⟩
    · rw [List.head?_reverse] at he
      obtain ⟨v, hv⟩ := mem_matchedLeft.mp (hq.last e he ▸ hr)
      exact h.root_free v (mem_mateMatching.mp hv)
    · rw [List.getLast?_reverse] at he
      obtain ⟨u, hu⟩ := mem_matchedRight.mp ((hq.head e he).1 ▸ hv)
      simp [mem_mateMatching, hfree] at hu
    · rw [List.isChain_reverse]
      exact hq.chain.imp fun a b hab => mem_mateMatching.mpr hab
  have hcompat : ∀ u v, (u, v) ∈ mateMatching mate →
      (u ∈ matchedLeft (vget path j₁).toFinset ↔ v ∈ matchedRight (vget path j₁).toFinset) := by
    simpa only [List.toFinset_reverse] using hp.compat_iff h.matching
  have hmatch : mateMatching (hgApplyEdges mate (vget path j₁)) =
      augment (mateMatching mate) (vget path j₁).toFinset :=
    mateMatching_applyEdges mate _ hq.nodup_snd hcompat
  have hM' : IsMatching (fun _ => true) (augment (mateMatching mate) (vget path j₁).toFinset) := by
    simpa only [List.toFinset_reverse] using hp.isMatching_augment h.matching
  refine ⟨⟨hmatch ▸ hM', h.feas, fun i j hm => ?_⟩, ?_⟩
  · rw [hgApplyEdges, vget_foldl_apply mate _ hq.nodup_snd] at hm
    rcases hm with hm | ⟨_, hm⟩
    · obtain ⟨e, l, hql⟩ := List.exists_cons_of_ne_nil hq.ne_nil
      rw [hql] at hm
      rcases List.mem_cons.mp hm with rfl | he
      · simpa [hj₁, hz] using (hq.head (i, j) (by simp [hql])).2
      · exact (hq.tail (i, j) (by simp [hql, he])).1
    · exact h.tight i j hm
  · rw [hmatch, matchedLeft_augment]
    ext u
    simp only [Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro (hu | hu)
      · rcases hp.matchedLeft_toFinset_subset u (by rwa [List.toFinset_reverse]) with
          ⟨e, he, hue⟩ | hu
        · rw [List.head?_reverse] at he
          exact .inl (hue.symm.trans (hq.last e he))
        · exact .inr hu
      · exact .inr hu
    · rintro (rfl | hu)
      · obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp
          (mt List.getLast?_eq_none_iff.mp hq.ne_nil)
        exact .inl (mem_matchedLeft.mpr ⟨e.2, List.mem_toFinset.mpr (hq.last e he ▸
          List.mem_of_getLast? he)⟩)
      · exact .inr hu

/-! #### Growing the tree -/

private theorem vget_vset_true {t : Vector Bool n} {j i : Fin n} :
    vget (vset t j true) i = true ↔ i = j ∨ vget t i = true := by
  by_cases h : i = j
  · simp [h]
  · simp [h, vget_vset_ne _ _ (Ne.symm h)]

theorem hgInv_extend {r : Fin n} {s : HgState n}
    (h : HgInv c r s.y s.z s.mate s.used s.tree s.minv s.path) {j₁ i₀ : Fin n}
    (hj₁ : vget s.used j₁ = false) (hz : vget s.minv j₁ = 0) (hm : vget s.mate j₁ = some i₀) :
    HgInv c r (hgExtend c s j₁ i₀).y (hgExtend c s j₁ i₀).z
      (hgExtend c s j₁ i₀).mate (hgExtend c s j₁ i₀).used
      (hgExtend c s j₁ i₀).tree (hgExtend c s j₁ i₀).minv
      (hgExtend c s j₁ i₀).path := by
  change HgInv c r s.y s.z s.mate (vset s.used j₁ true) (vset s.tree i₀ true)
    (hgRelax { s with used := vset s.used j₁ true, tree := vset s.tree i₀ true } c i₀ j₁).minv
    (hgRelax { s with used := vset s.used j₁ true, tree := vset s.tree i₀ true } c i₀ j₁).path
  have hi₀ : vget s.tree i₀ = false := by
    simpa only [hj₁, Bool.false_eq_true, iff_false, Bool.not_eq_true] using h.tree_iff_used hm
  have hU' : ∀ j, j ≠ j₁ → vget (vset s.used j₁ true) j = vget s.used j := fun j hj =>
    vget_vset_ne _ _ (Ne.symm hj)
  have hp₁ := h.path_ok j₁
  -- Every edge of the path of `j₁` is tight and ends at a column of the enlarged tree.
  have htight : ∀ e ∈ vget s.path j₁,
      hgRed c s.y s.z e.1 e.2 = 0 ∧ vget (vset s.used j₁ true) e.2 = true := by
    intro e he
    obtain ⟨b, l, hql⟩ := List.exists_cons_of_ne_nil hp₁.ne_nil
    rw [hql] at he
    rcases List.mem_cons.mp he with rfl | he
    · have hb := hp₁.head e (by simp [hql])
      rw [hj₁, hz, ite_self] at hb
      exact ⟨hb.2, vget_vset_true.mpr (.inl hb.1)⟩
    · have := hp₁.tail e (by simp [hql, he])
      exact ⟨this.1, vget_vset_true.mpr (.inr this.2)⟩
  refine ⟨h.matching, h.feas, h.tight, h.root_free, fun j hj => ?_, fun i => ?_,
    fun i j hi hj => ?_, fun j => ?_⟩
  · rcases vget_vset_true.mp hj with rfl | hj
    · exact ⟨i₀, hm⟩
    · exact h.used_mate j hj
  · simp only [vget_vset_true, h.tree_iff, or_and_right, exists_or, exists_eq_left, hm,
      Option.some.injEq, @eq_comm _ i₀ i]
    exact or_left_comm
  · have hjj : j ≠ j₁ := by
      rintro rfl
      simp at hj
    rw [hgRelax_minv]
    dsimp only
    rw [hj, ite_eq_right Bool.false_ne_true]
    rcases vget_vset_true.mp hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h.minv_le i j hi (by rwa [← hU' j hjj]))
  · rw [hgRelax_path]
    dsimp only
    split_ifs with hc
    · have hjj : j ≠ j₁ := by
        rintro rfl
        simp at hc
      have hjs : vget s.used j = false := by rw [← hU' j hjj]; exact hc.1
      obtain ⟨b, l, hql⟩ := List.exists_cons_of_ne_nil hp₁.ne_nil
      refine ⟨List.cons_ne_nil _ _, fun e he => ?_, fun e he => ?_, ?_, ?_, ?_,
        fun e he => htight e he, fun e he => ?_⟩
      · obtain rfl : (i₀, j) = e := by
          simpa only [List.head?_cons, Option.mem_def, Option.some.injEq] using he
        refine ⟨rfl, ?_⟩
        rw [hgRelax_minv]
        dsimp only
        rw [hc.1, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true]
        exact (min_eq_right hc.2.le).symm
      · rw [hql, List.getLast?_cons_cons, ← hql] at he
        exact hp₁.last e he
      · rw [hql]
        refine List.IsChain.cons_cons ?_ (hql ▸ hp₁.chain)
        rw [(hp₁.head b (by simp [hql])).1]
        exact hm
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hmem => ?_, hp₁.nodup_fst⟩
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmem
        exact Bool.false_ne_true (hi₀.symm.trans (hp₁.tree e he))
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hmem => ?_, hp₁.nodup_snd⟩
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmem
        rcases hp₁.mem_cases he with h1 | h1
        · exact hjj h1
        · exact Bool.false_ne_true (hjs.symm.trans h1)
      · rcases List.mem_cons.mp he with rfl | he'
        · exact vget_vset_true.mpr (.inl rfl)
        · exact vget_vset_true.mpr (.inr (hp₁.tree e he'))
    · have hp := h.path_ok j
      refine ⟨hp.ne_nil, fun e he => ?_, hp.last, hp.chain, hp.nodup_fst, hp.nodup_snd,
        fun e he => ?_, fun e he => vget_vset_true.mpr (.inr (hp.tree e he))⟩
      · obtain ⟨h1, h2⟩ := hp.head e he
        refine ⟨h1, ?_⟩
        rw [hgRelax_minv]
        dsimp only
        obtain rfl | hjj := eq_or_ne j j₁
        · rw [vget_vset_self, ite_eq_left rfl, h2, hj₁, hz, ite_self]
        · rw [hU' j hjj] at hc ⊢
          cases hju : vget s.used j <;>
            simp only [hju, ite_true, Bool.false_eq_true, ite_false, true_and, not_lt] at h2 hc ⊢
          · rw [h2, min_eq_left hc]
          · exact h2
      · obtain ⟨h1, h2⟩ := hp.tail e he
        exact ⟨h1, vget_vset_true.mpr (.inr h2)⟩

@[simp] theorem hgExtend_y (s : HgState n) (j₁ i₀ : Fin n) : (hgExtend c s j₁ i₀).y = s.y := rfl
@[simp] theorem hgExtend_z (s : HgState n) (j₁ i₀ : Fin n) : (hgExtend c s j₁ i₀).z = s.z := rfl
@[simp] theorem hgExtend_mate (s : HgState n) (j₁ i₀ : Fin n) :
    (hgExtend c s j₁ i₀).mate = s.mate := rfl
@[simp] theorem hgExtend_used (s : HgState n) (j₁ i₀ : Fin n) :
    (hgExtend c s j₁ i₀).used = vset s.used j₁ true := rfl
@[simp] theorem hgExtend_tree (s : HgState n) (j₁ i₀ : Fin n) :
    (hgExtend c s j₁ i₀).tree = vset s.tree i₀ true := rfl

/-! #### Counting tree columns -/

/-- Number of columns in the tree. -/
@[expose] def usedCount (used : Vector Bool n) : ℕ :=
  (Finset.univ.filter fun j => vget used j = true).card

theorem usedCount_le {mate : Vector (Option (Fin n)) n} {used : Vector Bool n}
    (hM : IsMatching (fun _ => true) (mateMatching mate))
    (hu : ∀ j, vget used j = true → ∃ i, vget mate j = some i) :
    usedCount used ≤ (mateMatching mate).card := by
  rw [← card_matchedRight hM]
  refine Finset.card_le_card fun j hj => ?_
  obtain ⟨i, hi⟩ := hu j (Finset.mem_filter.mp hj).2
  exact mem_matchedRight.mpr ⟨i, mem_mateMatching.mpr hi⟩

theorem usedCount_vset {used : Vector Bool n} {j₁ : Fin n}
    (hj₁ : vget used j₁ = false) : usedCount (vset used j₁ true) = usedCount used + 1 := by
  unfold usedCount
  rw [← Finset.card_insert_of_notMem (s := Finset.univ.filter fun j => vget used j = true)
    (a := j₁) (by simp [hj₁])]
  congr 1
  ext j
  rcases eq_or_ne j j₁ with rfl | hj
  · simp
  · simp [hj, vget_vset_ne _ _ hj.symm]

theorem usedCount_all {used : Vector Bool n} (h : ∀ j, vget used j = true) :
    usedCount used = n := by
  unfold usedCount
  rw [Finset.filter_true_of_mem fun j _ => h j]
  simp

theorem card_lt_of_root_free {mate : Vector (Option (Fin n)) n}
    (hM : IsMatching (fun _ => true) (mateMatching mate)) {r : Fin n}
    (hr : ∀ j, vget mate j ≠ some r) : (mateMatching mate).card < n := by
  rw [← card_matchedLeft hM]
  have : r ∉ matchedLeft (mateMatching mate) := by
    intro h
    obtain ⟨v, hv⟩ := mem_matchedLeft.mp h
    exact hr v (mem_mateMatching.mp hv)
  simpa using Finset.card_lt_univ_of_notMem this

theorem exists_free_col_of_root_free {mate : Vector (Option (Fin n)) n}
    (hM : IsMatching (fun _ => true) (mateMatching mate)) {r : Fin n}
    (hr : ∀ j, vget mate j ≠ some r) : ∃ j : Fin n, vget mate j = none := by
  by_contra! hall
  have hlt := card_matchedRight hM ▸ card_lt_of_root_free hM hr
  have huniv : matchedRight (mateMatching mate) = Finset.univ :=
    Finset.eq_univ_of_forall fun j =>
      let ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp (hall j)
      mem_matchedRight.mpr ⟨i, mem_mateMatching.mpr hi⟩
  simp [huniv] at hlt

/-! #### The loop, the phase and the rows -/

private theorem hgLoop_spec {r : Fin n} :
    ∀ (fuel : ℕ) (s : HgState n), HgInv c r s.y s.z s.mate s.used s.tree s.minv s.path →
      (mateMatching s.mate).card < fuel + usedCount s.used →
      HgOuter c (hgLoop c fuel s).y (hgLoop c fuel s).z (hgLoop c fuel s).mate ∧
        matchedLeft (mateMatching (hgLoop c fuel s).mate) =
          insert r (matchedLeft (mateMatching s.mate)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s h hfuel
    have := usedCount_le h.matching h.used_mate
    omega
  | succ fuel ih =>
    intro s h hfuel
    simp only [hgLoop]
    cases ha : hgArgmin s with
    | none =>
      have hall := hgArgmin_none ha
      have h1 := usedCount_all hall
      have h2 := usedCount_le h.matching h.used_mate
      have h3 := card_lt_of_root_free h.matching h.root_free
      omega
    | some j₁ =>
      obtain ⟨hj₁, hmin⟩ := hgArgmin_some ha
      have hD := hgInv_dual h hj₁ hmin
      have hz := minv_dual_self s hj₁
      dsimp only
      rw [hgDual_mate]
      cases hm : vget s.mate j₁ with
      | none =>
        exact hgAugment hD hj₁ hz hm
      | some i₀ =>
        have hE := hgInv_extend (s := hgDual s (vget s.minv j₁)) hD hj₁ hz hm
        have hcnt : usedCount (hgExtend c (hgDual s (vget s.minv j₁)) j₁ i₀).used =
            usedCount s.used + 1 := by
          rw [hgExtend_used, hgDual_used]
          exact usedCount_vset hj₁
        exact ih _ hE (by
          rw [hcnt, hgExtend_mate, hgDual_mate]
          omega)

theorem hgInv_init {y z : Vector ℤ n} {mate : Vector (Option (Fin n)) n} {r : Fin n}
    (h : HgOuter c y z mate) (hr : r ∉ matchedLeft (mateMatching mate)) :
    HgInv c r (hgInit c y z mate r).y (hgInit c y z mate r).z
      (hgInit c y z mate r).mate (hgInit c y z mate r).used
      (hgInit c y z mate r).tree (hgInit c y z mate r).minv
      (hgInit c y z mate r).path := by
  rw [hgInit_y, hgInit_z, hgInit_mate]
  refine ⟨h.matching, h.feas, h.tight, fun j hj => hr ?_, fun j hj => ?_, fun i => ?_,
    fun i j hi _ => ?_, fun j => ?_⟩
  · exact mem_matchedLeft.mpr ⟨j, mem_mateMatching.mpr hj⟩
  · rw [hgInit_used] at hj
    exact absurd hj Bool.false_ne_true
  · simp [hgInit_tree, hgInit_used]
  · rw [hgInit_tree, decide_eq_true_eq] at hi
    subst hi
    rw [hgInit_minv]
  · rw [hgInit_path]
    refine ⟨List.cons_ne_nil _ _, fun e he => ?_, fun e he => ?_, List.isChain_singleton _,
      by simp, by simp, fun e he => ?_, fun e he => ?_⟩
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
      subst he
      simp [hgInit_used, hgInit_minv]
    · simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at he
      subst he
      rfl
    · simp at he
    · simp only [List.mem_singleton] at he
      subst he
      simp [hgInit_tree]

private theorem hgPhase_spec {y z : Vector ℤ n} {mate : Vector (Option (Fin n)) n} {r : Fin n}
    (h : HgOuter c y z mate) (hr : r ∉ matchedLeft (mateMatching mate)) :
    HgOuter c (hgPhase c y z mate r).y (hgPhase c y z mate r).z (hgPhase c y z mate r).mate ∧
      matchedLeft (mateMatching (hgPhase c y z mate r).mate) =
        insert r (matchedLeft (mateMatching mate)) := by
  have hI := hgInv_init h hr
  have hlt := card_lt_of_root_free h.matching (r := r) (fun j hj => hr
    (mem_matchedLeft.mpr ⟨j, mem_mateMatching.mpr hj⟩))
  have h0 : usedCount (hgInit c y z mate r).used = 0 := by
    unfold usedCount
    simp [hgInit_used]
  exact hgLoop_spec n _ hI (by rw [h0, hgInit_mate]; omega)

private theorem hgRows_spec :
    ∀ (rows : List (Fin n)) (s : HgState n), rows.Nodup → HgOuter c s.y s.z s.mate →
      (∀ r ∈ rows, r ∉ matchedLeft (mateMatching s.mate)) →
      HgOuter c (hgRows c rows s).y (hgRows c rows s).z (hgRows c rows s).mate ∧
        matchedLeft (mateMatching (hgRows c rows s).mate) =
          rows.toFinset ∪ matchedLeft (mateMatching s.mate) := by
  intro rows
  induction rows with
  | nil =>
    intro s _ h _
    simp only [hgRows, List.toFinset_nil, Finset.empty_union, and_true]
    exact h
  | cons r rs ih =>
    intro s hnd h hfree
    rw [List.nodup_cons] at hnd
    obtain ⟨hO, hL⟩ := hgPhase_spec h (hfree r List.mem_cons_self)
    obtain ⟨hO', hL'⟩ := ih (hgPhase c s.y s.z s.mate r) hnd.2 hO (by
      intro r' hr' hmem
      rw [hL, Finset.mem_insert] at hmem
      rcases hmem with rfl | hmem
      · exact hnd.1 hr'
      · exact hfree r' (List.mem_cons_of_mem _ hr') hmem)
    simp only [hgRows]
    refine ⟨hO', ?_⟩
    rw [hL', hL]
    ext u
    simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons]
    tauto

/-! #### Bounded potential and predecessor-array invariants -/

/-- Between-phase invariant on nonnegative costs `0 ≤ c (u, v) ≤ W`: potentials satisfy
`0 ≤ y i ≤ W` and `-W ≤ z j ≤ 0`, with `z j = 0` on every unmatched column. -/
structure HgOuterBound (c : Fin n × Fin n → ℤ) (W : ℕ) (y z : Vector ℤ n)
    (mate : Vector (Option (Fin n)) n) : Prop extends HgOuter c y z mate where
  /-- Row potentials are nonnegative and bounded by `W`. -/
  y_bounds : ∀ i, 0 ≤ vget y i ∧ vget y i ≤ W
  /-- Column potentials are nonpositive and bounded below by `-W`. -/
  z_bounds : ∀ j, -(W : ℤ) ≤ vget z j ∧ vget z j ≤ 0
  /-- Unmatched columns have zero potential. -/
  free_z_zero : ∀ j, vget mate j = none → vget z j = 0

/-- Within-phase invariant on nonnegative costs `0 ≤ c (u, v) ≤ W` with predecessor row table
`bestRow : Fin n → Fin n` encoding `s.path` together with `s.mate`. -/
structure HgStepInv (c : Fin n × Fin n → ℤ) (W : ℕ) (r : Fin n) (s : HgState n)
    (bestRow : Fin n → Fin n) : Prop extends
    HgInv c r s.y s.z s.mate s.used s.tree s.minv s.path where
  /-- Row potentials lie in `[0, W]`. -/
  y_bounds : ∀ i, 0 ≤ vget s.y i ∧ vget s.y i ≤ W
  /-- Column potentials lie in `[-W, 0]`. -/
  z_bounds : ∀ j, -(W : ℤ) ≤ vget s.z j ∧ vget s.z j ≤ 0
  /-- Unmatched columns have zero potential. -/
  free_z_zero : ∀ j, vget s.mate j = none → vget s.z j = 0
  /-- Column slacks lie in `[0, 2 * W]`. -/
  minv_bounds : ∀ j, 0 ≤ vget s.minv j ∧ vget s.minv j ≤ 2 * (W : ℤ)
  /-- `bestRow j` is the left endpoint of the head edge of `s.path[j]`. -/
  head_eq : ∀ j, (vget s.path j).head? = some (bestRow j, j)
  /-- When `bestRow j = r`, `s.path[j]` is the single edge `[(r, j)]`. -/
  tail_root : ∀ j, bestRow j = r → (vget s.path j).tail = []
  /-- When `bestRow j` is matched to `j'`, the tail of `s.path[j]` is `s.path[j']`. -/
  tail_mate : ∀ j j', vget s.mate j' = some (bestRow j) → (vget s.path j).tail = vget s.path j'

theorem hgStepInv_init {W : ℕ} {y z : Vector ℤ n} {mate : Vector (Option (Fin n)) n} {r : Fin n}
    (hc : ∀ u v, 0 ≤ c (u, v) ∧ c (u, v) ≤ W)
    (h : HgOuterBound c W y z mate) (hr : r ∉ matchedLeft (mateMatching mate)) :
    HgStepInv c W r (hgInit c y z mate r) (fun _ => r) := by
  have hI := hgInv_init h.toHgOuter hr
  refine ⟨hI, h.y_bounds, h.z_bounds, h.free_z_zero, fun j => ?_, fun j => ?_,
    fun j _ => ?_, fun j j' hm => ?_⟩
  · rw [hgInit_minv]
    have hf := h.feas r j
    have hy := (h.y_bounds r).1
    have hz := (h.z_bounds j).1
    have hcw := (hc r j).2
    unfold hgRed at hf ⊢
    omega
  · simp [hgInit_path]
  · simp [hgInit_path]
  · exact absurd hm (hI.root_free j')

theorem hgStepInv_dual {W : ℕ} {r : Fin n} {s : HgState n} {bestRow : Fin n → Fin n}
    (hc : ∀ u v, 0 ≤ c (u, v) ∧ c (u, v) ≤ W)
    (h : HgStepInv c W r s bestRow) {j₁ : Fin n}
    (hj₁ : vget s.used j₁ = false)
    (hmin : ∀ j, vget s.used j = false → vget s.minv j₁ ≤ vget s.minv j) :
    HgStepInv c W r (hgDual s (vget s.minv j₁)) bestRow := by
  have hD := hgInv_dual h.toHgInv hj₁ hmin
  have hδ : 0 ≤ vget s.minv j₁ := h.toHgInv.minv_nonneg hj₁
  have hfree_z : ∀ j, vget (hgDual s (vget s.minv j₁)).mate j = none →
      vget (hgDual s (vget s.minv j₁)).z j = 0 := by
    intro j hm
    rw [hgDual_mate] at hm
    rw [hgDual_z, h.free_z_zero j hm]
    split_ifs with hu
    · obtain ⟨i, hi⟩ := h.used_mate j hu
      simp [hm] at hi
    · rfl
  obtain ⟨j_free, hj_free⟩ := exists_free_col_of_root_free h.matching h.root_free
  have hz_free : vget (hgDual s (vget s.minv j₁)).z j_free = 0 := hfree_z j_free hj_free
  have hy_bounds : ∀ i, 0 ≤ vget (hgDual s (vget s.minv j₁)).y i ∧
      vget (hgDual s (vget s.minv j₁)).y i ≤ W := by
    intro i
    have hf := hD.feas i j_free
    unfold hgRed at hf
    have := (h.y_bounds i).1
    have := (hc i j_free).2
    exact ⟨by rw [hgDual_y]; split_ifs <;> omega, by omega⟩
  have hz_bounds : ∀ j, -(W : ℤ) ≤ vget (hgDual s (vget s.minv j₁)).z j ∧
      vget (hgDual s (vget s.minv j₁)).z j ≤ 0 := by
    intro j
    refine ⟨?_, by rw [hgDual_z]; have := (h.z_bounds j).2; split_ifs <;> omega⟩
    cases hm : vget s.mate j with
    | none => rw [hfree_z j hm]; omega
    | some i =>
      have ht := hD.tight i j hm
      unfold hgRed at ht
      have := (hy_bounds i).2
      have := (hc i j).1
      omega
  refine ⟨hD, hy_bounds, hz_bounds, hfree_z, fun j => ?_, h.head_eq, h.tail_root, h.tail_mate⟩
  rw [hgDual_minv]
  have := h.minv_bounds j
  split_ifs with hu
  · exact this
  · have := hmin j (by simpa using hu)
    omega

theorem hgStepInv_extend {W : ℕ} {r : Fin n} {s : HgState n} {bestRow : Fin n → Fin n}
    (hc : ∀ u v, 0 ≤ c (u, v) ∧ c (u, v) ≤ W)
    (h : HgStepInv c W r s bestRow) {j₁ i₀ : Fin n}
    (hj₁ : vget s.used j₁ = false) (hz : vget s.minv j₁ = 0) (hm : vget s.mate j₁ = some i₀) :
    HgStepInv c W r (hgExtend c s j₁ i₀)
      (fun j => if vget (vset s.used j₁ true) j = false ∧ hgRed c s.y s.z i₀ j < vget s.minv j
        then i₀ else bestRow j) := by
  have hE := hgInv_extend h.toHgInv hj₁ hz hm
  have hpath_used : ∀ j', vget s.used j' = true →
      vget (hgExtend c s j₁ i₀).path j' = vget s.path j' := by
    intro j' hj'
    simp [hgExtend, hgRelax_path, vget_vset_true, hj']
  have hpath_j₁ : vget (hgExtend c s j₁ i₀).path j₁ = vget s.path j₁ := by
    simp [hgExtend, hgRelax_path]
  refine ⟨hE, h.y_bounds, h.z_bounds, h.free_z_zero, fun j => ?_, fun j => ?_,
    fun j hbr => ?_, fun j j' hm' => ?_⟩
  · let _ := hc
    simp only [hgExtend, hgRelax_minv]
    have hmb := h.minv_bounds j
    split_ifs
    · exact hmb
    · exact ⟨le_min hmb.1 (h.feas i₀ j), (min_le_left _ _).trans hmb.2⟩
  · simp only [hgExtend, hgRelax_path]
    split_ifs
    · rfl
    · exact h.head_eq j
  · simp only [hgExtend, hgRelax_path] at hbr ⊢
    split_ifs at hbr ⊢
    · exact absurd (hbr ▸ hm) (h.root_free j₁)
    · exact h.tail_root j hbr
  · simp only [hgExtend] at *
    rw [hgRelax_path]
    dsimp only at *
    split_ifs with hcond
    · rw [ite_eq_left hcond] at hm'
      obtain rfl := mate_inj h.matching hm' hm
      simpa only [List.tail_cons, hgExtend] using hpath_j₁.symm
    · rw [ite_eq_right hcond] at hm'
      have htree := (h.path_ok j).tree _ (List.mem_of_mem_head? (h.head_eq j))
      rw [h.tail_mate j j' hm']
      exact (hpath_used j' ((h.toHgInv.tree_iff_used hm').mp htree)).symm

private theorem vget_hgApplyEdges_eq_none {mate : Vector (Option (Fin n)) n}
    {es : List (Fin n × Fin n)} {j : Fin n}
    (h : vget (hgApplyEdges mate es) j = none) : vget mate j = none := by
  induction es generalizing mate with
  | nil => exact h
  | cons e es ih =>
    have hm := ih h
    rcases eq_or_ne j e.2 with rfl | hje
    · simp at hm
    · rwa [vget_vset_ne _ _ hje.symm] at hm

theorem hgOuterBound_augment {W : ℕ} {r : Fin n} {s : HgState n} {bestRow : Fin n → Fin n}
    (h : HgStepInv c W r s bestRow) {j₁ : Fin n} (hj₁ : vget s.used j₁ = false)
    (hz : vget s.minv j₁ = 0) (hfree : vget s.mate j₁ = none) :
    HgOuterBound c W s.y s.z (hgApplyEdges s.mate (vget s.path j₁)) ∧
      matchedLeft (mateMatching (hgApplyEdges s.mate (vget s.path j₁))) =
        insert r (matchedLeft (mateMatching s.mate)) := by
  obtain ⟨hO, hL⟩ := hgAugment h.toHgInv hj₁ hz hfree
  exact ⟨⟨hO, h.y_bounds, h.z_bounds, fun j hm => h.free_z_zero j (vget_hgApplyEdges_eq_none hm)⟩,
    hL⟩

theorem HgStepInv.path_eq_singleton {W : ℕ} {r : Fin n} {s : HgState n}
    {bestRow : Fin n → Fin n} (h : HgStepInv c W r s bestRow) {j : Fin n}
    (hfree : ∀ j', vget s.mate j' ≠ some (bestRow j)) :
    vget s.path j = [(bestRow j, j)] := by
  obtain ⟨e, l, hql⟩ := List.exists_cons_of_ne_nil (h.path_ok j).ne_nil
  obtain rfl : e = (bestRow j, j) := by simpa [hql] using h.head_eq j
  have htree := (h.path_ok j).tree _ (List.mem_of_mem_head? (h.head_eq j))
  have hbr : bestRow j = r :=
    ((h.tree_iff _).mp htree).elim id fun ⟨j', _, hm⟩ => absurd hm (hfree j')
  simpa [hql] using congrArg ((bestRow j, j) :: ·) (h.tail_root j hbr)

theorem HgStepInv.path_eq_cons {W : ℕ} {r : Fin n} {s : HgState n}
    {bestRow : Fin n → Fin n} (h : HgStepInv c W r s bestRow) {j j' : Fin n}
    (hm : vget s.mate j' = some (bestRow j)) :
    vget s.path j = (bestRow j, j) :: vget s.path j' := by
  obtain ⟨e, l, hql⟩ := List.exists_cons_of_ne_nil (h.path_ok j).ne_nil
  obtain rfl : e = (bestRow j, j) := by simpa [hql] using h.head_eq j
  simpa [hql] using congrArg ((bestRow j, j) :: ·) (h.tail_mate j j' hm)

theorem HgStepInv.length_path_le {W : ℕ} {r : Fin n} {s : HgState n}
    {bestRow : Fin n → Fin n} (h : HgStepInv c W r s bestRow) (j : Fin n) :
    (vget s.path j).length ≤ n := by
  simpa using (h.path_ok j).nodup_snd.length_le_card

end Spec

/-! ### Correctness and Egerváry's theorem -/

section Main

variable {n : ℕ}

private theorem foldl_min_le (c : Fin n × Fin n → ℤ) (u : Fin n) :
    ∀ (l : List (Fin n)) (a : ℤ),
      l.foldl (fun a v => min a (c (u, v))) a ≤ a ∧
        ∀ v ∈ l, l.foldl (fun a v => min a (c (u, v))) a ≤ c (u, v) := by
  intro l
  induction l with
  | nil => intro a; simp
  | cons x l ih =>
    intro a
    obtain ⟨h1, h2⟩ := ih (min a (c (u, x)))
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨h1.trans (min_le_left _ _), fun v hv => ?_⟩
    rcases hv with rfl | hv
    · exact h1.trans (min_le_right _ _)
    · exact h2 v hv

private theorem foldl_min_ge (c : Fin n × Fin n → ℤ) (u : Fin n) {B : ℤ}
    (hB : ∀ v, B ≤ c (u, v)) :
    ∀ (l : List (Fin n)) {a : ℤ}, B ≤ a → B ≤ l.foldl (fun a v => min a (c (u, v))) a := by
  intro l
  induction l with
  | nil => exact id
  | cons x l ih => exact fun ha => ih (le_min ha (hB x))

theorem hgRowMin_le (c : Fin n × Fin n → ℤ) (u v : Fin n) :
    hgRowMin c u ≤ c (u, v) :=
  (foldl_min_le c u _ _).2 v (List.mem_finRange v)

theorem hgRowMin_bounds {c : Fin n × Fin n → ℤ} {W : ℕ}
    (hc : ∀ u v, 0 ≤ c (u, v) ∧ c (u, v) ≤ W) (u : Fin n) :
    0 ≤ hgRowMin c u ∧ hgRowMin c u ≤ W :=
  ⟨foldl_min_ge c u (fun v => (hc u v).1) _ (hc u u).1,
    (hgRowMin_le c u u).trans (hc u u).2⟩

theorem hgOuter_start (c : Fin n × Fin n → ℤ) :
    HgOuter c (Vector.ofFn (hgRowMin c)) (Vector.replicate n 0) (Vector.replicate n none) := by
  refine ⟨⟨fun _ _ => rfl, fun u v₁ v₂ h₁ _ => ?_, fun u₁ u₂ v h₁ _ => ?_⟩,
    fun i j => ?_, fun i j hm => ?_⟩
  · simp [vget_replicate] at h₁
  · simp [vget_replicate] at h₁
  · have := hgRowMin_le c i j
    simp only [hgRed, vget, Vector.getElem_ofFn, Fin.eta, Vector.getElem_replicate]
    omega
  · simp [vget_replicate] at hm

theorem hgOuterBound_start {c : Fin n × Fin n → ℤ} {W : ℕ}
    (hc : ∀ u v, 0 ≤ c (u, v) ∧ c (u, v) ≤ W) :
    HgOuterBound c W (Vector.ofFn (hgRowMin c)) (Vector.replicate n 0)
      (Vector.replicate n none) := by
  refine ⟨hgOuter_start c, fun i => ?_, fun j => ?_, fun j _ => ?_⟩
  · simpa only [vget, Vector.getElem_ofFn, Fin.eta] using hgRowMin_bounds hc i
  · simp [vget]
  · simp [vget]

private theorem hg_final {c : Fin n × Fin n → ℤ} {s : HgState n}
    (h : HgOuter c s.y s.z s.mate) (hL : matchedLeft (mateMatching s.mate) = Finset.univ) :
    IsMinCostPerfectMatching (fun _ => true) c
        ((List.finRange n).foldl (hkMatchingStep s.mate) ∅) ∧
      IsFeasiblePotential (fun _ => true) c (vget s.y) (vget s.z) ∧
      matchingCost c ((List.finRange n).foldl (hkMatchingStep s.mate) ∅) =
        ∑ u, vget s.y u + ∑ v, vget s.z v := by
  have hM : (List.finRange n).foldl (hkMatchingStep s.mate) ∅ = mateMatching s.mate := by
    ext ⟨u, v⟩
    rw [mem_foldl_hkMatchingStep, mem_mateMatching]
    simp
  rw [hM]
  have hR : matchedRight (mateMatching s.mate) = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [card_matchedRight h.matching, ← card_matchedLeft h.matching, hL, Finset.card_univ]
  have hP : IsPerfectMatching (fun _ => true) (mateMatching s.mate) := ⟨h.matching, hL, hR⟩
  have hf : IsFeasiblePotential (fun _ => true) c (vget s.y) (vget s.z) := by
    intro u v _
    have := h.feas u v
    unfold hgRed at this
    omega
  have ht : ∀ e ∈ mateMatching s.mate, vget s.y e.1 + vget s.z e.2 = c e := by
    rintro ⟨u, v⟩ he
    have := h.tight u v (mem_mateMatching.mp he)
    unfold hgRed at this
    dsimp only
    omega
  exact ⟨hP.isMinCostPerfectMatching_of_tight hf ht, hf,
    ((hP.potential_eq_cost_iff hf).mpr ht).symm⟩

private theorem hungarian_rows (c : Fin n × Fin n → ℤ) :
    HgOuter c (hgRows c (List.finRange n) (hgStartState (Vector.ofFn (hgRowMin c))
        (Vector.replicate n 0) (Vector.replicate n none))).y
      (hgRows c (List.finRange n) (hgStartState (Vector.ofFn (hgRowMin c))
        (Vector.replicate n 0) (Vector.replicate n none))).z
      (hgRows c (List.finRange n) (hgStartState (Vector.ofFn (hgRowMin c))
        (Vector.replicate n 0) (Vector.replicate n none))).mate ∧
    matchedLeft (mateMatching (hgRows c (List.finRange n) (hgStartState
        (Vector.ofFn (hgRowMin c)) (Vector.replicate n 0) (Vector.replicate n none))).mate) =
      Finset.univ := by
  obtain ⟨hO, hL⟩ := hgRows_spec (c := c) (List.finRange n) (hgStartState
    (Vector.ofFn (hgRowMin c)) (Vector.replicate n 0) (Vector.replicate n none))
    (List.nodup_finRange n) (hgOuter_start c)
    (fun r _ hr => by
      obtain ⟨v, hv⟩ := mem_matchedLeft.mp hr
      simp [hgStartState, mem_mateMatching, vget_replicate] at hv)
  refine ⟨hO, ?_⟩
  rw [hL]
  exact Finset.eq_univ_of_forall fun u => Finset.mem_union_left _ (by simp)

/-- **Correctness of the Hungarian method.** The output is a minimum-cost perfect matching of the
complete bipartite graph on `Fin n × Fin n`, the output potentials are feasible, and the cost of
the matching equals the total potential (Egerváry's certificate of optimality). -/
theorem hungarian_correct (c : Fin n × Fin n → ℤ) :
    IsMinCostPerfectMatching (fun _ => true) c (hungarian c).matching ∧
      IsFeasiblePotential (fun _ => true) c (hungarian c).y (hungarian c).z ∧
      matchingCost c (hungarian c).matching =
        ∑ u, (hungarian c).y u + ∑ v, (hungarian c).z v := by
  obtain ⟨hO, hL⟩ := hungarian_rows c
  exact hg_final hO hL

/-! #### Uniform shift invariance -/

private def shiftHgState (S : ℤ) (s : HgState n) : HgState n :=
  { s with y := s.y.map (· + S) }

private theorem hgRowMin_add_const (c : Fin n × Fin n → ℤ) (S : ℤ) (u : Fin n) :
    hgRowMin (fun e => c e + S) u = hgRowMin c u + S := by
  have aux : ∀ (l : List (Fin n)) (a : ℤ),
      l.foldl (fun a v => min a (c (u, v) + S)) (a + S) =
        l.foldl (fun a v => min a (c (u, v))) a + S := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons x l ih =>
      intro a
      have hmin : min (a + S) (c (u, x) + S) = min a (c (u, x)) + S := by
        simp only [min_def]
        split_ifs <;> omega
      simp only [List.foldl_cons, hmin]
      exact ih (min a (c (u, x)))
  exact aux (List.finRange n) (c (u, u))

private theorem hgRed_add_const (c : Fin n × Fin n → ℤ) (S : ℤ) (y z : Vector ℤ n) (u v : Fin n) :
    hgRed (fun e => c e + S) (y.map (· + S)) z u v = hgRed c y z u v := by
  simp only [hgRed, vget, Vector.getElem_map]
  omega

private theorem hgArgmin_shiftHgState (S : ℤ) (s : HgState n) :
    hgArgmin (shiftHgState S s) = hgArgmin s := rfl

private theorem hgDual_shiftHgState (S : ℤ) (s : HgState n) (δ : ℤ) :
    hgDual (shiftHgState S s) δ = shiftHgState S (hgDual s δ) := by
  unfold hgDual shiftHgState
  congr 1
  ext i hi
  simp only [vget, Vector.getElem_ofFn, Vector.getElem_map]
  by_cases ht : s.tree[i] = true
  · simp [ht]; omega
  · simp [ht]

private theorem hgExtend_shiftHgState (c : Fin n × Fin n → ℤ) (S : ℤ) (s : HgState n)
    (j₁ i₀ : Fin n) :
    hgExtend (fun e => c e + S) (shiftHgState S s) j₁ i₀ = shiftHgState S (hgExtend c s j₁ i₀) := by
  simp only [hgExtend, hgRelax, shiftHgState, hgRed_add_const]

private theorem hgInit_add_const (c : Fin n × Fin n → ℤ) (S : ℤ) (y z : Vector ℤ n)
    (mate : Vector (Option (Fin n)) n) (r : Fin n) :
    hgInit (fun e => c e + S) (y.map (· + S)) z mate r = shiftHgState S (hgInit c y z mate r) := by
  simp only [hgInit, shiftHgState, hgRed_add_const]

private theorem hgLoop_add_const (c : Fin n × Fin n → ℤ) (S : ℤ) :
    ∀ (fuel : ℕ) (s : HgState n),
      hgLoop (fun e => c e + S) fuel (shiftHgState S s) = shiftHgState S (hgLoop c fuel s) := by
  intro fuel
  induction fuel with
  | zero => intro s; rfl
  | succ fuel ih =>
    intro s
    unfold hgLoop
    rw [hgArgmin_shiftHgState]
    cases hgArgmin s with
    | none => rfl
    | some j₁ =>
      dsimp only
      have hminv : vget (shiftHgState S s).minv j₁ = vget s.minv j₁ := rfl
      rw [hminv, hgDual_shiftHgState]
      have hmate : vget (shiftHgState S (hgDual s (vget s.minv j₁))).mate j₁ =
          vget s.mate j₁ := rfl
      rw [hmate, hgDual_mate]
      cases vget s.mate j₁ with
      | none => rfl
      | some i₀ =>
        dsimp only
        rw [hgExtend_shiftHgState, ih]

private theorem hgRows_add_const (c : Fin n × Fin n → ℤ) (S : ℤ) :
    ∀ (rows : List (Fin n)) (s : HgState n),
      hgRows (fun e => c e + S) rows (shiftHgState S s) = shiftHgState S (hgRows c rows s) := by
  intro rows
  induction rows with
  | nil => intro s; rfl
  | cons r rs ih =>
    intro s
    simp only [hgRows, hgPhase]
    change hgRows (fun e => c e + S) rs
      (hgLoop (fun e => c e + S) n (hgInit (fun e => c e + S) (s.y.map (· + S)) s.z s.mate r)) = _
    rw [hgInit_add_const, hgLoop_add_const, ih]

/-- Adding a constant `S` to every cost shifts row potentials by `S` and leaves column potentials
and the output matching unchanged. -/
theorem hungarian_add_const (c : Fin n × Fin n → ℤ) (S : ℤ) :
    (hungarian fun e => c e + S).matching = (hungarian c).matching ∧
      (∀ u, (hungarian fun e => c e + S).y u = (hungarian c).y u + S) ∧
      (∀ v, (hungarian fun e => c e + S).z v = (hungarian c).z v) := by
  have hy : Vector.ofFn (hgRowMin fun e => c e + S) =
      (Vector.ofFn (hgRowMin c)).map (· + S) := by
    ext i hi
    simp [hgRowMin_add_const]
  have hrows : hgRows (fun e => c e + S) (List.finRange n)
      (hgStartState (Vector.ofFn (hgRowMin fun e => c e + S))
        (Vector.replicate n 0) (Vector.replicate n none)) =
      shiftHgState S (hgRows c (List.finRange n)
        (hgStartState (Vector.ofFn (hgRowMin c))
          (Vector.replicate n 0) (Vector.replicate n none))) := by
    have hstart : hgStartState (Vector.ofFn (hgRowMin fun e => c e + S))
        (Vector.replicate n 0) (Vector.replicate n none) =
        shiftHgState S (hgStartState (Vector.ofFn (hgRowMin c))
          (Vector.replicate n 0) (Vector.replicate n none)) := by
      simp [hgStartState, shiftHgState, hy]
    rw [hstart]
    exact hgRows_add_const c S (List.finRange n) _
  refine ⟨?_, fun u => ?_, fun v => ?_⟩
  · simp only [hungarian, hrows, shiftHgState]
  · simp only [hungarian, hrows, shiftHgState, vget, Vector.getElem_map]
  · simp only [hungarian, hrows, shiftHgState]

/-- **Egerváry's theorem** for the integral assignment problem: there is a perfect matching of the
complete bipartite graph on `Fin n × Fin n` and integral feasible potentials whose total equals
its cost; in particular the matching has minimum cost. -/
theorem exists_isMinCostPerfectMatching_potential_eq (c : Fin n × Fin n → ℤ) :
    ∃ (M : Finset (Fin n × Fin n)) (y z : Fin n → ℤ),
      IsMinCostPerfectMatching (fun _ => true) c M ∧ IsFeasiblePotential (fun _ => true) c y z ∧
        matchingCost c M = ∑ u, y u + ∑ v, z v :=
  ⟨_, _, _, hungarian_correct c⟩

/-- **Min–max form of Egerváry's theorem**: a perfect matching `M` has minimum cost iff some
integral feasible potentials have total equal to its cost, and then every feasible potential has
total at most `matchingCost c M`. -/
theorem isMinCostPerfectMatching_iff_exists_potential (c : Fin n × Fin n → ℤ)
    {M : Finset (Fin n × Fin n)} (hM : IsPerfectMatching (fun _ => true) M) :
    IsMinCostPerfectMatching (fun _ => true) c M ↔
      ∃ y z : Fin n → ℤ, IsFeasiblePotential (fun _ => true) c y z ∧
        matchingCost c M = ∑ u, y u + ∑ v, z v := by
  constructor
  · intro hmin
    obtain ⟨M', y, z, hM', hf, heq⟩ := exists_isMinCostPerfectMatching_potential_eq c
    refine ⟨y, z, hf, le_antisymm ?_ (hM.potential_le_cost hf)⟩
    rw [← heq]
    exact hmin.2 M' hM'.1
  · rintro ⟨y, z, hf, heq⟩
    refine ⟨hM, fun M' hM' => ?_⟩
    rw [heq]
    exact hM'.potential_le_cost hf

/-- **Assignment problem, permutation form**: some permutation `σ` minimizes `∑ u, c (u, σ u)`
over all permutations, certified by integral feasible potentials with equal total. -/
theorem exists_perm_assignment (c : Fin n × Fin n → ℤ) :
    ∃ (σ : Equiv.Perm (Fin n)) (y z : Fin n → ℤ),
      (∀ τ : Equiv.Perm (Fin n), ∑ u, c (u, σ u) ≤ ∑ u, c (u, τ u)) ∧
        (∀ u v, y u + z v ≤ c (u, v)) ∧ ∑ u, c (u, σ u) = ∑ u, y u + ∑ v, z v := by
  obtain ⟨M, y, z, hmin, hf, heq⟩ := exists_isMinCostPerfectMatching_potential_eq c
  obtain ⟨σ, rfl⟩ := exists_eq_permMatching hmin.1
  refine ⟨σ, y, z, fun τ => ?_, fun u v => hf u v rfl, ?_⟩
  · have := hmin.2 _ (isPerfectMatching_permMatching τ)
    rwa [matchingCost_permMatching, matchingCost_permMatching] at this
  · rwa [matchingCost_permMatching] at heq

end Main

end Cslib.Algorithms.Lean.MaxFlow

