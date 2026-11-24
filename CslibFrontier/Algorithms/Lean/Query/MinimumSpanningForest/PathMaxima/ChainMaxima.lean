/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Query.BinarySearch
public import CslibFrontier.Algorithms.Lean.Query.FreeM.Tabulate
public import Cslib.Algorithms.Lean.Query.Sort.LEQuery
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Chain maxima on a nested hierarchy of blocks

A *hierarchy* on points `X` is given by block labels `lab l x : γ` at each level `l`, nested in the
sense that points in the same block at level `l` are in the same block at level `l + 1`, and by an
optional *parent edge* `sel l c : Option E` of each block `c` at level `l`. The *chain* of a point
`x` is the sequence of parent edges `sel l (lab l x)` of the blocks containing it. A chain query
`⟨x, j⟩` (`Cslib.Query.ChainQuery`) asks for a heaviest edge of the chain of `x` below level `j`,
with weights learned by comparisons in `FreeM (LEQuery E)`.

`Cslib.Query.chainMaxima` follows Komlós's top-down procedure, after [Komlos1985] and in the form
used by [King1997] on a full branching tree. It processes the levels from the top. At level `i` it
keeps, for every query `⟨x, j⟩` with `i < j`, the heaviest chain edge at the levels `i, …, j - 1`.
Within a block `c` at level `i`, the queries still open above `i + 1`, sorted by `j`, have
nondecreasing answers at level `i + 1`, so a single binary search against the parent edge `sel i c`
finds which of them it overtakes. The block costs `⌊log₂ s⌋ + 1` comparisons for `s` such queries,
whatever the oracle answers.

When at most `N l` blocks at level `l` hold a query still open above `l + 1`, and these counts at
least halve from each level to the next, as they do for the levels of Borůvka's algorithm on a
forest, the total is at most `4 N 0 + 2 q` comparisons for `q` queries. This follows Komlós's
counting on a full branching tree as King uses it, done here with `log₂ s ≤ l + s / 2 ^ l` at level
`l` in place of the concavity of the logarithm. The texts of [Komlos1985] and [King1997] were not
consulted for this module, so no locators into them are given; the argument is the standard one, and
this module does not formalize either paper as a cited result.

Chain maxima are a step, tracked in #8325, in the proof of Theorem 4.1 of
[KhannaPuttermanSong2026]: they answer the path-maxima queries of the paper's Lemma 2.9 (§2, p. 12)
along King's route.

## Main definitions

* `Cslib.Query.ChainQuery`: a point and the level below which its chain is queried.
* `Cslib.Query.IsChainMax`: `e` is a heaviest edge of the chain of `x` at the levels `i, …, j - 1`.
* `Cslib.Query.chainMaxima`: Komlós's procedure, answering a list of chain queries.

## Main results

* `Cslib.Query.chainMaxima_correct`: against an oracle comparing weights, `chainMaxima` answers
  every query `⟨x, j⟩` with `0 < j ≤ K` by a heaviest chain edge below level `j`.
* `Cslib.Query.countQueries_chainMaxima_le`: when at most `N l` blocks at level `l` hold a query
  open above level `l + 1` and `2 * N (l + 1) ≤ N l`, `chainMaxima` makes at most
  `4 * N 0 + 2 * qs.length` comparisons, under every oracle.

## References

* [S. Khanna, A. Putterman and J. Song, *A Deterministic Linear Time Algorithm for Minimum
  Spanning Tree*][KhannaPuttermanSong2026], §2, Lemma 2.9, p. 12.
* [J. Komlós, *Linear verification for spanning trees*][Komlos1985]
* [V. King, *A simpler minimum spanning tree verification algorithm*][King1997]
-/

public section

namespace Cslib.Query

/-- A *chain query* asks for a heaviest parent edge of the blocks containing `point` at the
levels `0, …, level - 1`. -/
structure ChainQuery (X : Type) where
  /-- The point whose chain of blocks is queried. -/
  point : X
  /-- The query covers the levels below `level`. -/
  level : ℕ
  deriving DecidableEq

variable {X γ E W : Type} [DecidableEq X] [DecidableEq γ]

section Defs

variable (lab : ℕ → X → γ) (sel : ℕ → γ → Option E)

/-- `e` is a heaviest edge of the chain of `x` at the levels `i, …, j - 1`, for the weights `w`:
it is the parent edge of the block of `x` at one of these levels, and no parent edge of a block of
`x` at these levels is heavier. -/
@[expose] def IsChainMax [LE W] (w : E → W) (x : X) (i j : ℕ) (e : E) : Prop :=
  (∃ l, i ≤ l ∧ l < j ∧ sel l (lab l x) = some e) ∧
    ∀ l, i ≤ l → l < j → ∀ e', sel l (lab l x) = some e' → w e' ≤ w e

variable (qs : List (ChainQuery X))

/-- The queries still open above level `i + 1`. -/
private def live (i : ℕ) : List (ChainQuery X) :=
  qs.filter fun h => i + 1 < h.level

/-- The blocks at level `i` holding a query still open above level `i + 1`. -/
private def liveLabels (i : ℕ) : List γ :=
  ((live qs i).map fun h => lab i h.point).dedup

/-- The queries in block `c` at level `i` still open above level `i + 1`, sorted by level. -/
private def liveIn (i : ℕ) (c : γ) : List (ChainQuery X) :=
  ((live qs i).filter fun h => lab i h.point = c).mergeSort fun a b => a.level ≤ b.level

/-- Compare two optional edges, answering `false` without a comparison when one is missing. -/
private def probe : Option E → Option E → FreeM (LEQuery E) Bool
  | some a, some b => LEQuery.ask a b
  | _, _ => pure false

/-- The binary search in block `c` at level `i`: the number of queries of the block, in their
sorted order, whose current answer is not heavier than the parent edge `sel i c`. -/
private def cutoff (cur : ChainQuery X → Option E) (i : ℕ) (c : γ) : FreeM (LEQuery E) ℕ :=
  lowerBoundBy (fun m => probe ((liveIn lab qs i c)[m]?.bind cur) (sel i c)) 0
    (liveIn lab qs i c).length

/-- One level of Komlós's procedure: from the answers `cur` at the levels above `i`, the answers
at the levels from `i` on. A query ending at level `i + 1` is answered by the parent edge at level
`i`; in each block, the open queries that the parent edge overtakes take it as their answer. -/
private def chainStep (i : ℕ) (cur : ChainQuery X → Option E) :
    FreeM (LEQuery E) (ChainQuery X → Option E) := do
  let t ← FreeM.tabulateList (cutoff lab sel qs cur i) (liveLabels lab qs i)
  return fun h =>
    if h.level = i + 1 ∨
        h ∈ (liveIn lab qs i (lab i h.point)).take ((t (lab i h.point)).getD 0) then
      sel i (lab i h.point)
    else cur h

/-- Komlós's procedure from level `i` up to level `K`. -/
private def chainMaximaFrom (K i : ℕ) : FreeM (LEQuery E) (ChainQuery X → Option E) :=
  if i < K then do chainStep lab sel qs i (← chainMaximaFrom K (i + 1))
  else pure fun _ => none
termination_by K - i

/-- **Chain maxima**, after Komlós's procedure ([Komlos1985]). Answer each chain query of `qs` whose
level is at most `K`, top-down over the levels `K - 1, …, 0` of the hierarchy, by one binary search
per block and level. -/
def chainMaxima (K : ℕ) : FreeM (LEQuery E) (ChainQuery X → Option E) :=
  chainMaximaFrom lab sel qs K 0

end Defs

/-! ## Correctness -/

section Correctness

variable {lab : ℕ → X → γ} {sel : ℕ → γ → Option E}

omit [DecidableEq X] [DecidableEq γ] in
/-- Points in the same block at level `i` are in the same block at every level `l ≥ i`. -/
private theorem lab_eq_of_le (hnest : ∀ l x y, lab l x = lab l y → lab (l + 1) x = lab (l + 1) y)
    {i l : ℕ} {x y : X} (hil : i ≤ l) (h : lab i x = lab i y) : lab l x = lab l y := by
  induction l, hil using Nat.le_induction with
  | base => exact h
  | succ l _ ih => exact hnest l x y ih

variable [LinearOrder W] {w : E → W}

omit [DecidableEq X] [DecidableEq γ] in
/-- Two queries in the same block at level `i`: the chain maximum above `i` ending lower is not
heavier. -/
private theorem IsChainMax.le_of_level_le
    (hnest : ∀ l x y, lab l x = lab l y → lab (l + 1) x = lab (l + 1) y)
    {i j₁ j₂ : ℕ} {x₁ x₂ : X} {e₁ e₂ : E} (hlab : lab i x₁ = lab i x₂) (hj : j₁ ≤ j₂)
    (h₁ : IsChainMax lab sel w x₁ (i + 1) j₁ e₁) (h₂ : IsChainMax lab sel w x₂ (i + 1) j₂ e₂) :
    w e₁ ≤ w e₂ := by
  obtain ⟨l, hil, hlj, hl⟩ := h₁.1
  rw [lab_eq_of_le hnest (by omega : i ≤ l) hlab] at hl
  exact h₂.2 l hil (by omega) e₁ hl

variable (lab sel) in
/-- The answers `cur` are chain maxima from level `i` on, for the queries of `qs` open at `i`. -/
private def Answers (w : E → W) (qs : List (ChainQuery X)) (i : ℕ)
    (cur : ChainQuery X → Option E) : Prop :=
  ∀ h ∈ qs, i < h.level → ∃ e, cur h = some e ∧ IsChainMax lab sel w h.point i h.level e

omit [DecidableEq X] in
private theorem mem_liveIn {qs : List (ChainQuery X)} {i : ℕ} {c : γ} {h : ChainQuery X} :
    h ∈ liveIn lab qs i c ↔ h ∈ qs ∧ i + 1 < h.level ∧ lab i h.point = c := by
  simp only [liveIn, live, List.mem_mergeSort, List.mem_filter, decide_eq_true_eq]
  tauto

omit [DecidableEq X] in
private theorem mem_liveLabels {qs : List (ChainQuery X)} {i : ℕ} {h : ChainQuery X}
    (hq : h ∈ qs) (hlev : i + 1 < h.level) : lab i h.point ∈ liveLabels lab qs i := by
  simp only [liveLabels, live, List.mem_dedup, List.mem_map, List.mem_filter]
  exact ⟨h, ⟨hq, by simpa using hlev⟩, rfl⟩

omit [DecidableEq X] in
private theorem liveIn_sorted (qs : List (ChainQuery X)) (i : ℕ) (c : γ) :
    (liveIn lab qs i c).Pairwise fun a b => a.level ≤ b.level := by
  have := List.pairwise_mergeSort (le := fun a b : ChainQuery X => decide (a.level ≤ b.level))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    ((live qs i).filter fun h => lab i h.point = c)
  simpa [liveIn] using this

/-- One level of Komlós's procedure turns chain maxima above `i` into chain maxima from `i`. -/
private theorem answers_chainStep (oracle : {ι : Type} → LEQuery E ι → ι)
    (horacle : ∀ a b, oracle (.le a b) = decide (w a ≤ w b))
    (hnest : ∀ l x y, lab l x = lab l y → lab (l + 1) x = lab (l + 1) y)
    {qs : List (ChainQuery X)} {i : ℕ}
    (hdef : ∀ h ∈ qs, ∀ l < h.level, (sel l (lab l h.point)).isSome)
    {cur : ChainQuery X → Option E} (hcur : Answers lab sel w qs (i + 1) cur) :
    Answers lab sel w qs i ((chainStep lab sel qs i cur).eval oracle) := by
  intro h hq hih
  obtain ⟨e₀, he₀⟩ := Option.isSome_iff_exists.mp (hdef h hq i hih)
  simp only [chainStep, FreeM.eval_bind, FreeM.eval_pure, FreeM.eval_tabulateList]
  rcases Nat.lt_or_ge (i + 1) h.level with hlev | hlev
  swap
  · -- the query ends at level `i + 1`: its answer is the parent edge at level `i`
    have hj : h.level = i + 1 := by omega
    refine ⟨e₀, by simp [hj, he₀], ⟨i, le_rfl, by omega, he₀⟩, fun l hil hlj e' he' => ?_⟩
    obtain rfl : l = i := by omega
    rw [he₀] at he'
    cases he'
    exact le_rfl
  -- the query stays open above `i + 1`: binary search in its block
  set c := lab i h.point with hc
  have hlab : c ∈ liveLabels lab qs i := mem_liveLabels hq hlev
  set L := liveIn lab qs i c with hL
  have hhL : h ∈ L := mem_liveIn.mpr ⟨hq, hlev, rfl⟩
  -- the current answers along `L`
  have hcurL : ∀ m (hm : m < L.length), ∃ e, cur L[m] = some e ∧
      IsChainMax lab sel w L[m].point (i + 1) L[m].level e ∧ lab i L[m].point = c := by
    intro m hm
    obtain ⟨hmq, hmlev, hmc⟩ := mem_liveIn.mp (List.getElem_mem hm)
    obtain ⟨e, he, hmax⟩ := hcur _ hmq hmlev
    exact ⟨e, he, hmax, hmc⟩
  set tst : ℕ → Bool := fun m => (probe (L[m]?.bind cur) (sel i c)).eval oracle with htst
  have htstm : ∀ m (hm : m < L.length) e, cur L[m] = some e → tst m = decide (w e ≤ w e₀) := by
    intro m hm e he
    simp [htst, List.getElem?_eq_getElem hm, he, he₀, probe, horacle]
  have hmono : ∀ m m', 0 ≤ m → m ≤ m' → m' < L.length → tst m' = true → tst m = true := by
    intro m m' _ hmm' hm' ht
    obtain ⟨e, he, hmax, hmc⟩ := hcurL m (by omega)
    obtain ⟨e', he', hmax', hmc'⟩ := hcurL m' hm'
    rw [htstm m' hm' e' he', decide_eq_true_eq] at ht
    rw [htstm m (by omega) e he, decide_eq_true_eq]
    refine le_trans ?_ ht
    refine hmax.le_of_level_le hnest (hmc.trans hmc'.symm) ?_ hmax'
    rcases hmm'.lt_or_eq with hlt | rfl
    · exact List.pairwise_iff_getElem.mp (liveIn_sorted qs i c) m m' (hmm'.trans_lt hm') hm' hlt
    · exact le_rfl
  obtain ⟨-, -, htrue, hfalse⟩ := Cslib.Algorithms.Lean.lowerBound_spec tst hmono
  set t := Cslib.Algorithms.Lean.lowerBound tst 0 L.length with ht
  have hcut : (cutoff lab sel qs cur i c).eval oracle = t := by
    simp [cutoff, eval_lowerBoundBy, ht, htst, ← hL]
  simp only [hlab, ite_true, hcut, Option.getD_some]
  by_cases htake : h ∈ L.take t
  · -- the parent edge overtakes the current answer
    obtain ⟨p, hp, hpe⟩ := List.mem_iff_getElem.mp htake
    rw [List.getElem_take] at hpe
    have hpt : p < t := by simp at hp; omega
    have hpL : p < L.length := by simp at hp; omega
    obtain ⟨e, he, hmax, -⟩ := hcurL p hpL
    have := htrue p (Nat.zero_le _) hpt
    rw [htstm p hpL e he, decide_eq_true_eq] at this
    simp only [hpe] at he hmax
    refine ⟨e₀, by simp [htake, he₀], ⟨i, le_rfl, hih, he₀⟩, fun l hil hlj e' he' => ?_⟩
    rcases hil.lt_or_eq with hil | rfl
    · exact (hmax.2 l hil hlj e' he').trans this
    · rw [he₀] at he'; cases he'; exact le_rfl
  · -- the current answer stays
    have hdrop : h ∈ L.drop t := by
      rw [← List.take_append_drop t L, List.mem_append] at hhL
      exact hhL.resolve_left htake
    obtain ⟨p, hp, hpe⟩ := List.mem_iff_getElem.mp hdrop
    rw [List.getElem_drop] at hpe
    have hpL : t + p < L.length := by simp at hp; omega
    obtain ⟨e, he, hmax, -⟩ := hcurL (t + p) hpL
    have := hfalse (t + p) (Nat.le_add_right _ _) hpL
    rw [htstm _ hpL e he, decide_eq_false_iff_not, not_le] at this
    simp only [hpe] at he hmax
    refine ⟨e, by simp [htake, he, show h.level ≠ i + 1 by omega], ⟨?_, fun l hil hlj e' he' => ?_⟩⟩
    · obtain ⟨l, hil, hlj, hl⟩ := hmax.1
      exact ⟨l, by omega, hlj, hl⟩
    · rcases hil.lt_or_eq with hil | rfl
      · exact hmax.2 l hil hlj e' he'
      · rw [he₀] at he'; cases he'; exact this.le

/-- Komlós's procedure from level `i` gives chain maxima from level `i` on. -/
private theorem answers_chainMaximaFrom (oracle : {ι : Type} → LEQuery E ι → ι)
    (horacle : ∀ a b, oracle (.le a b) = decide (w a ≤ w b))
    (hnest : ∀ l x y, lab l x = lab l y → lab (l + 1) x = lab (l + 1) y)
    {qs : List (ChainQuery X)} {K : ℕ} (hK : ∀ h ∈ qs, h.level ≤ K)
    (hdef : ∀ h ∈ qs, ∀ l < h.level, (sel l (lab l h.point)).isSome) (i : ℕ) :
    Answers lab sel w qs i ((chainMaximaFrom lab sel qs K i).eval oracle) := by
  fun_induction chainMaximaFrom lab sel qs K i with
  | case1 i hi ih => -- `i < K`
    rw [FreeM.eval_bind]
    exact answers_chainStep oracle horacle hnest hdef ih
  | case2 i hi => -- `K ≤ i`
    intro h hq hlev
    have := hK h hq
    omega

/-- **Correctness of chain maxima.** Against an oracle comparing the weights `w`, if the blocks are
nested, every query of `qs` has level at most `K`, and the chain of every query has a parent edge at
each level below its own, then `chainMaxima` answers every query `⟨x, j⟩` with `0 < j` by a heaviest
edge of the chain of `x` below level `j`. -/
theorem chainMaxima_correct (oracle : {ι : Type} → LEQuery E ι → ι)
    (horacle : ∀ a b, oracle (.le a b) = decide (w a ≤ w b))
    (hnest : ∀ l x y, lab l x = lab l y → lab (l + 1) x = lab (l + 1) y)
    {qs : List (ChainQuery X)} {K : ℕ} (hK : ∀ h ∈ qs, h.level ≤ K)
    (hdef : ∀ h ∈ qs, ∀ l < h.level, (sel l (lab l h.point)).isSome)
    {h : ChainQuery X} (hq : h ∈ qs) (hlev : 0 < h.level) :
    ∃ e, (chainMaxima lab sel qs K).eval oracle h = some e ∧
      IsChainMax lab sel w h.point 0 h.level e :=
  answers_chainMaximaFrom oracle horacle hnest hK hdef 0 h hq hlev

end Correctness

/-! ## Comparison count -/

section Arithmetic

/-- At level `l`, a block holding `s` queries costs `⌊log₂ s⌋ ≤ l + s / 2 ^ l` comparisons
beyond one. -/
private theorem log_le_add_div (s l : ℕ) : Nat.log 2 s ≤ l + s / 2 ^ l := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  by_cases h : Nat.log 2 s ≤ l
  · exact Nat.le_add_right_of_le h
  have h1 := Nat.pow_log_le_self 2 hs.ne'
  have h2 : 2 ^ (Nat.log 2 s - l) ≤ s / 2 ^ l := by
    rw [Nat.le_div_iff_mul_le (by positivity), ← pow_add]
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) h1
  have h3 : Nat.log 2 s - l < 2 ^ (Nat.log 2 s - l) := Nat.lt_two_pow_self
  generalize s / 2 ^ l = d at h2 ⊢
  generalize 2 ^ (Nat.log 2 s - l) = p at h2 h3
  omega

private theorem sum_map_div_le {ι : Type} (f : ι → ℕ) (d : ℕ) :
    ∀ l : List ι, (l.map fun x => f x / d).sum ≤ (l.map f).sum / d
  | [] => by simp
  | a :: l => by
    simp only [List.map_cons, List.sum_cons]
    exact (Nat.add_le_add_left (sum_map_div_le f d l) _).trans Nat.div_add_div_le_add_div

/-- The sizes of the fibres of `f` over its distinct values add up to the length of the list. -/
private theorem sum_length_filter_dedup {ι : Type} (f : ι → γ) (l : List ι) :
    ((l.map f).dedup.map fun c => (l.filter fun h => f h = c).length).sum = l.length := by
  have hc : ∀ c, (l.filter fun h => f h = c).length = (l.map f).count c := by
    intro c
    rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
    rfl
  simp only [hc, List.sum_map_count_dedup_eq_length, List.length_map]

/-- `∑_{l < d} a / 2 ^ l ≤ 2 a`. -/
private theorem sum_div_two_pow_le : ∀ (d a : ℕ), ∑ l ∈ Finset.range d, a / 2 ^ l ≤ 2 * a
  | 0, a => by simp
  | d + 1, a => by
    rw [Finset.sum_range_succ']
    have hs : ∀ l ∈ Finset.range d, a / 2 ^ (l + 1) = a / 2 / 2 ^ l := fun l _ => by
      rw [Nat.div_div_eq_div_mul, pow_succ']
    rw [Finset.sum_congr rfl hs]
    have := sum_div_two_pow_le d (a / 2)
    have : 2 * (a / 2) ≤ a := Nat.mul_div_le a 2
    simp only [pow_zero, Nat.div_one]
    omega

/-- When the counts `N l` at least halve from each level to the next, the counts weighted by
`l + 1` add up to at most `4 N 0`; in general, from level `i` on, to at most `(2 i + 4) N i`. -/
private theorem sum_mul_le_of_halving {N : ℕ → ℕ} (hhalf : ∀ l, 2 * N (l + 1) ≤ N l) :
    ∀ d i, ∑ l ∈ Finset.range d, (i + l + 1) * N (i + l) ≤ (2 * i + 4) * N i
  | 0, i => by simp
  | d + 1, i => by
    rw [Finset.sum_range_succ']
    have hs : ∀ l ∈ Finset.range d,
        (i + (l + 1) + 1) * N (i + (l + 1)) = (i + 1 + l + 1) * N (i + 1 + l) := fun l _ => by
      rw [show i + (l + 1) = i + 1 + l by omega]
    rw [Finset.sum_congr rfl hs]
    have ih := sum_mul_le_of_halving hhalf d (i + 1)
    have h := Nat.mul_le_mul_left (i + 3) (hhalf i)
    simp only [add_zero]
    nlinarith

end Arithmetic

section Cost

variable (lab : ℕ → X → γ) (sel : ℕ → γ → Option E) (qs : List (ChainQuery X))

/-- The comparisons charged to level `i`: `⌊log₂ s⌋ + 1` for each block holding `s` open
queries. -/
private def levelCost (i : ℕ) : ℕ :=
  ((liveLabels lab qs i).map fun c => Nat.log 2 (liveIn lab qs i c).length + 1).sum

omit [DecidableEq X] [DecidableEq γ] in
private theorem countQueries_probe_le (oracle : {ι : Type} → LEQuery E ι → ι) (a b : Option E) :
    (probe a b).countQueries oracle ≤ 1 := by
  cases a <;> cases b <;> simp [probe]

private theorem countQueries_chainStep_le (oracle : {ι : Type} → LEQuery E ι → ι) (i : ℕ)
    (cur : ChainQuery X → Option E) :
    (chainStep lab sel qs i cur).countQueries oracle ≤ levelCost lab qs i := by
  rw [chainStep, FreeM.countQueries_bind, FreeM.countQueries_pure, add_zero,
    FreeM.countQueries_eq_cost_one, FreeM.cost_tabulateList, levelCost]
  refine List.sum_le_sum fun c _ => ?_
  rw [← FreeM.countQueries_eq_cost_one]
  simpa [cutoff] using countQueries_lowerBoundBy_le oracle _ (c := 1) (lo := 0)
    (hi := (liveIn lab qs i c).length) fun m _ _ => countQueries_probe_le oracle _ _

private theorem countQueries_chainMaximaFrom_le (oracle : {ι : Type} → LEQuery E ι → ι)
    (K i : ℕ) :
    (chainMaximaFrom lab sel qs K i).countQueries oracle ≤
      ∑ l ∈ Finset.Ico i K, levelCost lab qs l := by
  fun_induction chainMaximaFrom lab sel qs K i with
  | case1 i hi ih => -- `i < K`
    rw [FreeM.countQueries_bind, Finset.sum_eq_sum_Ico_succ_bot hi]
    have := countQueries_chainStep_le lab sel qs oracle i
      ((chainMaximaFrom lab sel qs K (i + 1)).eval oracle)
    omega
  | case2 i hi => simp -- `K ≤ i`

omit [DecidableEq X] in
private theorem levelCost_le (i : ℕ) :
    levelCost lab qs i ≤ (i + 1) * (liveLabels lab qs i).length + qs.length / 2 ^ i := by
  calc levelCost lab qs i
      ≤ ((liveLabels lab qs i).map fun c => (i + 1) + (liveIn lab qs i c).length / 2 ^ i).sum :=
        List.sum_le_sum fun c _ => by have := log_le_add_div (liveIn lab qs i c).length i; omega
    _ = (i + 1) * (liveLabels lab qs i).length +
          ((liveLabels lab qs i).map fun c => (liveIn lab qs i c).length / 2 ^ i).sum := by
        rw [List.sum_map_add, List.map_const', List.sum_replicate, smul_eq_mul, mul_comm]
    _ ≤ (i + 1) * (liveLabels lab qs i).length + qs.length / 2 ^ i := by
        refine Nat.add_le_add_left ((sum_map_div_le _ _ _).trans (Nat.div_le_div_right ?_)) _
        have := sum_length_filter_dedup (fun h => lab i h.point) (live qs i)
        simp only [liveIn, List.length_mergeSort] at this ⊢
        rw [liveLabels, this]
        exact List.length_filter_le _ _

/-- **Comparison count of chain maxima**, after Komlós's counting ([Komlos1985], [King1997]). If at
each level `l < K` at most `N l` blocks hold a query still open above level `l + 1`, and
`2 * N (l + 1) ≤ N l` for all `l`, then `chainMaxima` makes at most `4 * N 0 + 2 * qs.length`
comparisons, under every oracle. -/
theorem countQueries_chainMaxima_le (oracle : {ι : Type} → LEQuery E ι → ι) {K : ℕ}
    {N : ℕ → ℕ}
    (hN : ∀ l < K, ∃ s : Finset γ, s.card ≤ N l ∧ ∀ h ∈ qs, l + 1 < h.level → lab l h.point ∈ s)
    (hhalf : ∀ l, 2 * N (l + 1) ≤ N l) :
    (chainMaxima lab sel qs K).countQueries oracle ≤ 4 * N 0 + 2 * qs.length := by
  have hlen : ∀ l < K, (liveLabels lab qs l).length ≤ N l := by
    intro l hl
    obtain ⟨s, hs, hmem⟩ := hN l hl
    rw [liveLabels, ← List.toFinset_card_of_nodup (List.nodup_dedup _)]
    refine (Finset.card_le_card fun c hc => ?_).trans hs
    simp only [live, List.mem_toFinset, List.mem_dedup, List.mem_map,
      List.mem_filter, decide_eq_true_eq] at hc
    obtain ⟨h, ⟨hq, hlev⟩, rfl⟩ := hc
    exact hmem h hq hlev
  calc (chainMaxima lab sel qs K).countQueries oracle
      ≤ ∑ l ∈ Finset.range K, levelCost lab qs l := by
        rw [Finset.range_eq_Ico]; exact countQueries_chainMaximaFrom_le lab sel qs oracle K 0
    _ ≤ ∑ l ∈ Finset.range K, ((0 + l + 1) * N (0 + l) + qs.length / 2 ^ l) := by
        refine Finset.sum_le_sum fun l hl => (levelCost_le lab qs l).trans ?_
        have := Nat.mul_le_mul_left (l + 1) (hlen l (Finset.mem_range.mp hl))
        simp only [zero_add]
        omega
    _ ≤ 4 * N 0 + 2 * qs.length := by
        rw [Finset.sum_add_distrib]
        have h1 := sum_mul_le_of_halving hhalf K 0
        have h2 := sum_div_two_pow_le K qs.length
        simp only [mul_zero, zero_add] at h1 ⊢
        omega

end Cost

end Cslib.Query
