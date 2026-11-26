/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.FenwickTree.Lowbit
public import CslibFrontier.DataStructure.PrefixSums.Spec
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.GetD

/-!
# Fenwick Trees (Binary Indexed Trees)

This module formalizes pure universe-polymorphic Fenwick trees (binary indexed trees,
`[Fenwick1994]`, pp. 328–332):

* Over any `[AddCommMonoid α]`: zero-initialized trees `zeros`, point increments `add` (`addLoop`),
  prefix queries `prefixSum`, and `a.size`-step immediate-parent construction `ofArray`
  (`buildLoop`) and `ofList`, together with the loop invariant `BuildInv`.
* Over any `[AddCommGroup α]`: half-open range queries `rangeSum`, point reads `get`, and point
  assignments `set`.

For a bounded-word Word-RAM implementation with checked instruction-count bounds (`O(log n)` per
update and prefix query and `O(n)` initialization), see
`Cslib.DataStructure.FenwickTree.WordRAM`.

## Source Conventions

* **Indexing:** `[Fenwick1994]` indexes frequencies from `0`, using nodes `1 .. n` (where `V[m]`
  holds `F[m - lowbit m + 1 .. m]`) with element `0` held separately (`V[0] = F[0]`, p. 328). Here
  a length-`n` sequence `s : List α` (`0`-indexed positions `0 .. n - 1`) is shifted by `1` into
  nodes `m ∈ [1, n]` (`[Fenwick1994]`, "PRINCIPLES", pp. 328–329, Figure 1 on p. 328 and
  Figures 2–3 on p. 329), stored at `0`-based array slot `t.tree[m - 1]` and aggregating
  `((s.take m).drop (m - lowbit m)).sum`.
* **Out-of-bounds totality:** `prefixSum t len` clamps `len` to `t.size` (matching
  `(s.take len).sum` for all `len : ℕ`), and `add t pos δ` / `set t pos v` leave `t` unchanged
  when `pos ≥ t.size` (matching `PrefixSums.addAt s pos δ` and `s.set pos v`).
* **Algebraic generality and standard extensions:** `[Fenwick1994]` presents cumulative prefix
  queries (`GetCumul`, "THE CUMULATIVE FREQUENCY", Figure 4, p. 330) and upward point increments
  ("UPDATING THE TABLE", pp. 331–332, Figures 5–6 on p. 331) over integer frequencies (plus
  specialized single-frequency extraction in "READING A SINGLE FREQUENCY", Figure 7, p. 332).
  Here `zeros`, `prefixSum`, `add`, and `ofArray` require only `[AddCommMonoid α]`;
  immediate-parent propagation `ofArray`/`ofList` (`m ↦ m + lowbit m`) is standard BIT folklore,
  and `rangeSum`, `get`, and `set` are standard `[AddCommGroup α]` subtraction corollaries of
  `prefixSum` and `add`.

## Main definitions

* `Cslib.DataStructure.FenwickTree`: array-backed Fenwick tree of size `t.size`.
* `Cslib.DataStructure.FenwickTree.Valid`: invariant coupling `t` to `s : List α`.
* `Cslib.DataStructure.FenwickTree.zeros`, `buildLoop`, `ofArray`, `ofList`, `BuildInv`:
  zero initialization and immediate-parent construction with its step invariant.
* `Cslib.DataStructure.FenwickTree.prefixSum`, `addLoop`, `add`: prefix queries and point
  increments over `[AddCommMonoid α]`.
* `Cslib.DataStructure.FenwickTree.rangeSum`, `get`, `set`: half-open range sums, point reads,
  and point assignments over `[AddCommGroup α]`.

## Main results

* `Cslib.DataStructure.FenwickTree.Valid.unique`: `Valid t s` uniquely determines `t` (so any
  valid construction, including `ofList s` and incremental `add` from `zeros`, produces the exact
  same tree).
* `Cslib.DataStructure.FenwickTree.prefixSum_eq`: `prefixSum` computes `(s.take len).sum`.
* `Cslib.DataStructure.FenwickTree.valid_add`: `add` preserves `Valid` for
  `PrefixSums.addAt s pos δ`.
* `Cslib.DataStructure.FenwickTree.valid_ofArray` and `valid_ofList`: `ofArray` and `ofList`
  build valid Fenwick trees via immediate-parent propagation (`BuildInv.step`,
  `BuildInv.parent_add_le_sum`).
* `Cslib.DataStructure.FenwickTree.rangeSum_eq`, `get_eq`, `valid_set`: correctness of range
  sums, point reads, and point assignments over `[AddCommGroup α]`.

## References

* [P. M. Fenwick, *A New Data Structure for Cumulative Frequency Tables*, pp. 328–332][Fenwick1994]
-/

public section

namespace Cslib.DataStructure

/-- Array-backed Fenwick tree (binary indexed tree) over `α`. -/
structure FenwickTree (α : Type*) where
  /-- Internal `0`-indexed storage array where entry `m - 1` holds node `m`'s interval sum. -/
  tree : Array α
  deriving DecidableEq, Repr

namespace FenwickTree

/-- Logical length of the represented sequence. -/
@[expose] def size {α : Type*} (t : FenwickTree α) : ℕ :=
  t.tree.size

/-- Fenwick tree representation invariant: `t` has length `s.length` and each `1`-based node `m`
(`1 ≤ m ≤ t.tree.size`) stores the interval sum `((s.take m).drop (m - lowbit m)).sum`. -/
@[expose] def Valid {α : Type*} [AddCommMonoid α] (t : FenwickTree α) (s : List α) : Prop :=
  t.tree.size = s.length ∧
    ∀ (m : ℕ) (_ : 1 ≤ m) (_ : m ≤ t.tree.size),
      t.tree[m - 1]'(by omega) = ((s.take m).drop (m - lowbit m)).sum

theorem Valid.size_eq {α : Type*} [AddCommMonoid α] {t : FenwickTree α} {s : List α}
    (hv : Valid t s) : t.size = s.length :=
  hv.1

/-- Canonical representation uniqueness: `Valid t s` uniquely determines `t`. -/
theorem Valid.unique {α : Type*} [AddCommMonoid α]
    {t₁ t₂ : FenwickTree α} {s : List α} (h₁ : Valid t₁ s) (h₂ : Valid t₂ s) : t₁ = t₂ := by
  rcases t₁, t₂ with ⟨⟨a₁⟩, ⟨a₂⟩⟩
  congr 1
  refine Array.ext (h₁.1.trans h₂.1.symm) fun i hi₁ hi₂ => ?_
  simpa only [Nat.add_sub_cancel] using
    (h₁.2 (i + 1) (by omega) (Nat.succ_le_of_lt hi₁)).trans
      (h₂.2 (i + 1) (by omega) (Nat.succ_le_of_lt hi₂)).symm

/-- On a natural-number Fenwick tree valid for `s`, every stored cell is at most `s.sum`. -/
theorem Valid.getElem_le_sum {t : FenwickTree ℕ} {s : List ℕ} (hv : Valid t s)
    {i : ℕ} (hi : i < t.tree.size) : t.tree[i] ≤ s.sum := by
  have hm := hv.2 (i + 1) (by omega) (Nat.succ_le_of_lt hi)
  simp only [Nat.add_sub_cancel] at hm
  rw [hm]
  have h1 : ((s.take (i + 1)).drop (i + 1 - lowbit (i + 1))).sum ≤ (s.take (i + 1)).sum := by
    conv_rhs => rw [← List.take_append_drop (i + 1 - lowbit (i + 1)) (s.take (i + 1)),
      List.sum_append]
    omega
  have h2 : (s.take (i + 1)).sum ≤ s.sum := by
    conv_rhs => rw [← List.take_append_drop (i + 1) s, List.sum_append]
    omega
  exact h1.trans h2

/-! ## Bridging `List` slice sums and `Finset.Ico` sums -/

private theorem sum_drop_take_eq_sum_Ico {α : Type*} [AddCommMonoid α]
    (s : List α) {l r : ℕ} (hr : r ≤ s.length) :
    ((s.take r).drop l).sum = ∑ i ∈ Finset.Ico l r, s.getD i 0 := by
  induction r with
  | zero =>
    rw [List.take_zero, List.drop_nil, List.sum_nil, Finset.Ico_eq_empty (by omega),
      Finset.sum_empty]
  | succ r ih =>
    rcases le_or_gt (r + 1) l with hle | hlt
    · have hdrop : (s.take (r + 1)).drop l = [] :=
        List.drop_eq_nil_of_le ((List.length_take_le (r + 1) s).trans hle)
      rw [hdrop, List.sum_nil, Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    · have hrl : l ≤ r := by omega
      have hrs : r < s.length := by omega
      have htake : s.take (r + 1) = s.take r ++ [s[r]'hrs] := by
        rw [List.take_add_one, getElem?_pos s r hrs, Option.toList_some]
      have hlen_r : (s.take r).length = r := List.length_take_of_le (Nat.le_of_lt hrs)
      have hico : Finset.Ico l (r + 1) = insert r (Finset.Ico l r) := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_insert]
        omega
      have hr_not : r ∉ Finset.Ico l r := by grind
      rw [htake, List.drop_append_of_le_length (by rw [hlen_r]; exact hrl),
        List.sum_append, List.sum_singleton, ih (Nat.le_of_lt hrs),
        hico, Finset.sum_insert hr_not, add_comm]
      congr 1
      exact (List.getD_eq_getElem _ _ hrs).symm

private theorem take_eq_take_append_drop {α : Type*} (s : List α) {l r : ℕ} (h : l ≤ r) :
    s.take r = s.take l ++ (s.take r).drop l := by
  simpa only [List.take_take, Nat.min_eq_left h] using (List.take_append_drop l (s.take r)).symm

private theorem valid_iff_sum_Ico {α : Type*} [AddCommMonoid α]
    {t : FenwickTree α} {s : List α} :
    Valid t s ↔ t.tree.size = s.length ∧
      ∀ (m : ℕ) (_ : 1 ≤ m) (_ : m ≤ t.tree.size),
        t.tree[m - 1]'(by omega) = ∑ i ∈ Finset.Ico (m - lowbit m) m, s.getD i 0 := by
  unfold Valid
  exact and_congr_right fun hsz => forall₃_congr fun m _ hm =>
    by rw [sum_drop_take_eq_sum_Ico s (hsz ▸ hm)]

/-! ## Zero-initialized Fenwick tree -/

/-- All-zero Fenwick tree of length `n`. -/
@[expose] def zeros {α : Type*} [Zero α] (n : ℕ) : FenwickTree α :=
  ⟨Array.replicate n 0⟩

@[simp]
theorem size_zeros {α : Type*} [Zero α] (n : ℕ) : (zeros n : FenwickTree α).size = n := by
  simp only [size, zeros, Array.size_replicate]

theorem valid_zeros {α : Type*} [AddCommMonoid α] (n : ℕ) :
    Valid (zeros n : FenwickTree α) (List.replicate n 0) := by
  rw [valid_iff_sum_Ico]
  refine ⟨by simp only [zeros, Array.size_replicate, List.length_replicate],
    fun m _ _ => ?_⟩
  simp [zeros]

/-! ## Prefix queries (`prefixSum`) -/

/-- Downward Fenwick query loop accumulating interval sums along `m, m - lowbit m, …`. -/
@[expose] def prefixSumLoop {α : Type*} [AddCommMonoid α]
    (tree : Array α) (m : ℕ) (acc : α) : α :=
  if hm : 0 < m ∧ m ≤ tree.size then
    prefixSumLoop tree (m - lowbit m) (acc + tree[m - 1]'(by omega))
  else
    acc
termination_by m
decreasing_by exact Nat.sub_lt hm.1 (lowbit_pos hm.1)

/-- Prefix sum of the first `len` elements (`[Fenwick1994]`, "THE CUMULATIVE FREQUENCY", Figure 4,
p. 330). Clamps `len` to `t.size`. -/
@[expose] def prefixSum {α : Type*} [AddCommMonoid α] (t : FenwickTree α) (len : ℕ) : α :=
  prefixSumLoop t.tree (min len t.tree.size) 0

@[simp]
theorem prefixSum_zero {α : Type*} [AddCommMonoid α] (t : FenwickTree α) :
    prefixSum t 0 = 0 := by
  unfold prefixSum
  rw [Nat.zero_min, prefixSumLoop]
  simp only [Nat.lt_irrefl, false_and, ↓reduceDIte]

private theorem prefixSumLoop_eq {α : Type*} [AddCommMonoid α]
    {t : FenwickTree α} {s : List α} (hv : Valid t s)
    {m : ℕ} (hms : m ≤ s.length) (acc : α) :
    prefixSumLoop t.tree m acc = acc + (s.take m).sum := by
  fun_induction prefixSumLoop t.tree m acc with
  | case1 m acc hguard ih =>
    have hlt : m - lowbit m < m := Nat.sub_lt hguard.1 (lowbit_pos hguard.1)
    rw [ih (by omega), hv.2 m hguard.1 hguard.2]
    conv_rhs => rw [take_eq_take_append_drop s (Nat.le_of_lt hlt), List.sum_append]
    rw [add_assoc, add_comm ((s.take m).drop (m - lowbit m)).sum]
  | case2 m acc hguard =>
    obtain rfl : m = 0 := by have := hv.1; omega
    simp only [List.take_zero, List.sum_nil, add_zero]

/-- Functional correctness of `prefixSum` (`[Fenwick1994]`, "THE CUMULATIVE FREQUENCY", Figure 4,
p. 330): on any valid tree for `s`, `prefixSum t len` equals `(s.take len).sum` for all
`len : ℕ`. -/
theorem prefixSum_eq {α : Type*} [AddCommMonoid α]
    {t : FenwickTree α} {s : List α} (hv : Valid t s) (len : ℕ) :
    prefixSum t len = (s.take len).sum := by
  unfold prefixSum
  rw [hv.1, prefixSumLoop_eq hv (Nat.min_le_right len s.length) 0, zero_add]
  rcases le_or_gt len s.length with hle | hgt
  · rw [Nat.min_eq_left hle]
  · rw [Nat.min_eq_right (Nat.le_of_lt hgt), List.take_length,
      List.take_of_length_le (Nat.le_of_lt hgt)]

/-! ## Point increments (`addLoop`, `add`) -/

/-- Upward Fenwick update loop on a backing array: adds `δ` at `0`-based slot `m - 1` along
`m, m + lowbit m, … ≤ n`. -/
@[expose] def addLoop {α : Type*} [AddCommMonoid α]
    (n : ℕ) (m : ℕ) (δ : α) (tree : Array α) : Array α :=
  if _hm : 0 < m ∧ m ≤ n then
    addLoop n (m + lowbit m) δ (tree.modify (m - 1) (· + δ))
  else
    tree
termination_by n + 1 - m
decreasing_by
  have := lowbit_pos _hm.1
  omega

/-- Add `δ` at `0`-based index `pos` (`[Fenwick1994]`, "UPDATING THE TABLE", pp. 331–332,
Figures 5–6 on p. 331). Leaves `t` unchanged when `t.size ≤ pos`. -/
@[expose] def add {α : Type*} [AddCommMonoid α]
    (t : FenwickTree α) (pos : ℕ) (δ : α) : FenwickTree α :=
  if pos < t.tree.size then ⟨addLoop t.tree.size (pos + 1) δ t.tree⟩ else t

@[simp]
theorem addLoop_size {α : Type*} [AddCommMonoid α]
    (n m : ℕ) (δ : α) (tree : Array α) :
    (addLoop n m δ tree).size = tree.size := by
  fun_induction addLoop n m δ tree with
  | case1 m tree _ ih => rw [ih, Array.size_modify]
  | case2 => rfl

private theorem addLoop_getElem {α : Type*} [AddCommMonoid α]
    (n m : ℕ) (δ : α) (tree : Array α)
    {idx : ℕ} (hidx1 : 1 ≤ idx) (hidx_sz : idx ≤ tree.size) :
    (addLoop n m δ tree)[idx - 1]'(by rw [addLoop_size]; omega) =
      if idx ∈ upChain n m then tree[idx - 1]'(by omega) + δ
      else tree[idx - 1]'(by omega) := by
  generalize hrem : n + 1 - m = rem
  induction rem using Nat.strongRecOn generalizing m tree with
  | ind rem ih =>
    generalize_proofs pf_ret pf_tree
    revert pf_ret
    rw [addLoop]
    split_ifs with hm
    · intro pf_ret
      have hlb_pos : 0 < lowbit m := lowbit_pos hm.1
      have hidx_sz' : idx ≤ (tree.modify (m - 1) (· + δ)).size := by
        rw [Array.size_modify]; exact hidx_sz
      rw [@ih (n + 1 - (m + lowbit m)) (by omega) (m + lowbit m)
        (tree.modify (m - 1) (· + δ)) hidx_sz' rfl]
      simp only [Array.getElem_modify]
      conv_rhs => rw [upChain]
      simp only [hm.1, hm.2, and_self, ↓reduceDIte, List.mem_cons]
      by_cases heq : idx = m
      · subst heq
        have hnot_tail : idx ∉ upChain n (idx + lowbit idx) := by
          intro hmem
          have hpw := pairwise_lt_upChain n idx
          rw [upChain] at hpw
          simp only [hm.1, hm.2, and_self, ↓reduceDIte, List.pairwise_cons] at hpw
          exact Nat.lt_irrefl idx (hpw.1 idx hmem)
        simp only [true_or, ↓reduceIte, hnot_tail]
      · have hne_sub : m - 1 ≠ idx - 1 := by omega
        simp only [heq, false_or, hne_sub, ↓reduceIte]
    · intro _
      rw [upChain]
      simp only [hm, ↓reduceDIte, List.not_mem_nil, ↓reduceIte]

/-- `add t pos δ` preserves `Valid` with respect to `PrefixSums.addAt s pos δ`
(`[Fenwick1994]`, "UPDATING THE TABLE", pp. 331–332, Figures 5–6 on p. 331). -/
theorem valid_add {α : Type*} [AddCommMonoid α]
    {t : FenwickTree α} {s : List α} (hv : Valid t s) (pos : ℕ) (δ : α) :
    Valid (add t pos δ) (PrefixSums.addAt s pos δ) := by
  unfold add
  split_ifs with hpos
  · have hpos_s : pos < s.length := hv.1 ▸ hpos
    rw [valid_iff_sum_Ico] at hv ⊢
    refine ⟨by rw [addLoop_size, hv.1, PrefixSums.length_addAt], fun idx hidx1 hidx_sz => ?_⟩
    rw [addLoop_size] at hidx_sz
    rw [addLoop_getElem t.tree.size (pos + 1) δ t.tree hidx1 hidx_sz, hv.2 idx hidx1 hidx_sz]
    have hmem_ico : idx ∈ upChain t.tree.size (pos + 1) ↔
        pos ∈ Finset.Ico (idx - lowbit idx) idx := by
      rw [mem_upChain_iff (by omega : 0 < pos + 1), Finset.mem_Ico]
      omega
    simp only [hmem_ico]
    have hsum_eq :
        ∑ i ∈ Finset.Ico (idx - lowbit idx) idx, (PrefixSums.addAt s pos δ).getD i 0 =
        ∑ i ∈ Finset.Ico (idx - lowbit idx) idx,
          (s.getD i 0 + if i = pos then δ else 0) :=
      Finset.sum_congr rfl fun i _ => by
        rw [PrefixSums.getD_addAt s δ hpos_s i]; split_ifs <;> simp only [add_zero]
    rw [hsum_eq, Finset.sum_add_distrib]
    by_cases hmem : pos ∈ Finset.Ico (idx - lowbit idx) idx
    · rw [ite_eq_left hmem, Finset.sum_eq_single_of_mem pos hmem fun i _ hne => ite_eq_right hne,
        ite_eq_left rfl]
    · rw [ite_eq_right hmem, Finset.sum_eq_zero fun i hi =>
        ite_eq_right fun (h : i = pos) => hmem (h ▸ hi), add_zero]
  · have hge : s.length ≤ pos := by have := hv.1; omega
    rwa [PrefixSums.addAt_of_length_le δ hge]

@[simp]
theorem size_add {α : Type*} [AddCommMonoid α]
    (t : FenwickTree α) (pos : ℕ) (δ : α) :
    (add t pos δ).size = t.size := by
  unfold add size
  split_ifs <;> simp

theorem add_of_size_le {α : Type*} [AddCommMonoid α]
    (t : FenwickTree α) {pos : ℕ} (δ : α) (h : t.size ≤ pos) :
    add t pos δ = t := by
  unfold add size at *
  exact ite_eq_right (by omega)

/-! ## Immediate-parent propagation construction (`buildLoop`, `ofArray`, `ofList`) -/

/-- Immediate-parent propagation loop: for `m = 1 .. n`, adds `tree[m - 1]` into its immediate
Fenwick parent `m + lowbit m` when in range. -/
@[expose] def buildLoop {α : Type*} [AddCommMonoid α]
    (n : ℕ) (m : ℕ) (tree : Array α) : Array α :=
  if hm : 1 ≤ m ∧ m ≤ n ∧ tree.size = n then
    let p := m + lowbit m
    let tree' :=
      if p ≤ n then
        let val := tree[m - 1]'(by omega)
        tree.modify (p - 1) (· + val)
      else
        tree
    buildLoop n (m + 1) tree'
  else
    tree
termination_by n + 1 - m

/-- Construct a Fenwick tree from `a : Array α` by adding each node `m` once into its immediate
Fenwick parent `m + lowbit m`. -/
@[expose] def ofArray {α : Type*} [AddCommMonoid α] (a : Array α) : FenwickTree α :=
  ⟨buildLoop a.size 1 a⟩

/-- Construct a Fenwick tree from `s : List α`. -/
@[expose] def ofList {α : Type*} [AddCommMonoid α] (s : List α) : FenwickTree α :=
  ofArray s.toArray

/-- Loop invariant for immediate-parent propagation after processing nodes `1 .. m - 1`. -/
structure BuildInv {α : Type*} [AddCommMonoid α]
    (s : List α) (m : ℕ) (tree : Array α) : Prop where
  /-- Backing array preserves the length of `s`. -/
  size_eq : tree.size = s.length
  /-- Nodes `< m` already hold their final Fenwick interval sums. -/
  done_eq : ∀ (idx : ℕ) (_ : 1 ≤ idx) (_ : idx < m) (_ : idx ≤ tree.size),
    tree[idx - 1]'(by omega) = ∑ i ∈ Finset.Ico (idx - lowbit idx) idx, s.getD i 0
  /-- Nodes `≥ m` hold `s[idx - 1]` plus contributions from processed immediate children. -/
  todo_eq : ∀ (idx : ℕ) (_ : 1 ≤ idx) (_ : m ≤ idx) (_ : idx ≤ tree.size),
    tree[idx - 1]'(by omega) = s.getD (idx - 1) 0 +
      ∑ c ∈ (fenwickChildren idx).filter (· < m),
        ∑ i ∈ Finset.Ico (c - lowbit c) c, s.getD i 0

/-- Before the first propagation step (`m = 1`), `a` satisfies `BuildInv a.toList 1`. -/
theorem buildInv_init {α : Type*} [AddCommMonoid α] (a : Array α) :
    BuildInv a.toList 1 a := by
  refine ⟨Array.length_toList.symm, fun idx h1 hlt _ => by omega,
    fun idx hidx1 _ hidx_sz => ?_⟩
  have hfilt0 : (fenwickChildren idx).filter (· < 1) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro c hc
    simp only [fenwickChildren, Finset.mem_filter, Finset.mem_Icc] at hc
    omega
  rw [hfilt0, Finset.sum_empty, add_zero]
  have hlt : idx - 1 < a.toList.length := by rw [Array.length_toList]; omega
  rw [List.getD_eq_getElem _ _ hlt, Array.getElem_toList]

/-- Single propagation step advancing `BuildInv s m` to `BuildInv s (m + 1)`. -/
theorem BuildInv.step {α : Type*} [AddCommMonoid α]
    {s : List α} {m : ℕ} {tree : Array α}
    (hm1 : 1 ≤ m) (hms : m ≤ s.length) (hinv : BuildInv s m tree) :
    BuildInv s (m + 1)
      (if m + lowbit m ≤ s.length then
        tree.modify (m + lowbit m - 1) (· + tree[m - 1]'(by have := hinv.size_eq; omega))
      else tree) := by
  have hmt : m ≤ tree.size := hinv.size_eq ▸ hms
  have hm_val : tree[m - 1]'(by omega) =
      ∑ i ∈ Finset.Ico (m - lowbit m) m, s.getD i 0 := by
    rw [hinv.todo_eq m hm1 (Nat.le_refl m) hmt]
    have hfilt : (fenwickChildren m).filter (· < m) = fenwickChildren m :=
      Finset.filter_true_of_mem fun c hc => by
        simp only [fenwickChildren, Finset.mem_filter, Finset.mem_Icc] at hc; omega
    rw [hfilt]
    conv_rhs =>
      rw [← insert_biUnion_fenwickChildren hm1,
        Finset.sum_insert (notMem_biUnion_fenwickChildren m),
        Finset.sum_biUnion (pairwiseDisjoint_fenwickChildren m)]
  set p := m + lowbit m
  have hp_gt : m < p := by
    have := lowbit_pos hm1
    omega
  set tree' :=
    if p ≤ s.length then tree.modify (p - 1) (· + tree[m - 1]'(by omega)) else tree
  have hsz' : tree'.size = s.length := by
    dsimp only [tree']
    split_ifs <;> simp only [Array.size_modify, hinv.size_eq]
  refine ⟨hsz', fun idx hidx1 hidx_lt hidx_sz' => ?_,
    fun idx hidx1 hidx_ge hidx_sz' => ?_⟩
  · have hidx_sz : idx ≤ tree.size := by rw [hinv.size_eq, ← hsz']; exact hidx_sz'
    have htree'_eq : tree'[idx - 1]'(by omega) = tree[idx - 1]'(by omega) := by grind
    rw [htree'_eq]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hidx_lt) with hlt | rfl
    · exact hinv.done_eq idx hidx1 hlt hidx_sz
    · exact hm_val
  · have hidx_sz : idx ≤ tree.size := by rw [hinv.size_eq, ← hsz']; exact hidx_sz'
    by_cases hpeq : idx = p
    · subst hpeq
      have hp_le : p ≤ s.length := hsz' ▸ hidx_sz'
      have htree'_p : tree'[p - 1]'(by omega) =
          tree[p - 1]'(by omega) + tree[m - 1]'(by omega) := by
        generalize_proofs pf1 pf2 pf3
        revert pf1
        dsimp only [tree']
        simp only [hp_le, ↓reduceIte]
        intro pf1
        simp only [Array.getElem_modify, ↓reduceIte]
      rw [htree'_p, hinv.todo_eq p hidx1 (by omega) hidx_sz, hm_val]
      have hm_mem : m ∈ fenwickChildren p := by
        simp only [fenwickChildren, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hm1, by omega⟩, rfl⟩
      have hfilt_eq : (fenwickChildren p).filter (· < m + 1) =
          insert m ((fenwickChildren p).filter (· < m)) := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_insert]
        grind
      rw [hfilt_eq, Finset.sum_insert (by simp), add_assoc]
      exact congrArg (_ + ·) (add_comm _ _)
    · have htree'_ne : tree'[idx - 1]'(by omega) = tree[idx - 1]'(by omega) := by grind
      rw [htree'_ne, hinv.todo_eq idx hidx1 (by omega) hidx_sz]
      have hfilt_eq : (fenwickChildren idx).filter (· < m + 1) =
          (fenwickChildren idx).filter (· < m) := by
        refine Finset.filter_congr fun c hc => ⟨fun hclt => ?_, fun _ => by omega⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hclt with hlt | rfl
        · exact hlt
        · simp only [fenwickChildren, Finset.mem_filter] at hc; exact absurd hc.2.symm hpeq
      rw [hfilt_eq]

/-- At completion (`m = s.length + 1`), `BuildInv` implies `Valid`. -/
theorem BuildInv.to_valid {α : Type*} [AddCommMonoid α]
    {s : List α} {tree : Array α} (hinv : BuildInv s (s.length + 1) tree) :
    Valid ⟨tree⟩ s := by
  rw [valid_iff_sum_Ico]
  refine ⟨hinv.size_eq, fun m hm1 hm => ?_⟩
  dsimp only at hm
  exact hinv.done_eq m hm1 (by have := hinv.size_eq; omega) hm

/-- Over `ℕ`, every intermediate array entry under `BuildInv s m tree` is bounded by `s.sum`. -/
theorem BuildInv.getElem_le_sum {s : List ℕ} {m : ℕ} {tree : Array ℕ}
    (hinv : BuildInv s m tree) {idx : ℕ} (hidx1 : 1 ≤ idx) (hidx_sz : idx ≤ tree.size) :
    tree[idx - 1]'(by omega) ≤ s.sum := by
  have hico_le : (∑ i ∈ Finset.Ico (idx - lowbit idx) idx, s.getD i 0) ≤ s.sum := by
    have hsub : Finset.Ico (idx - lowbit idx) idx ⊆ Finset.Ico 0 s.length := by
      intro i hi
      simp only [Finset.mem_Ico] at hi ⊢
      have := hinv.size_eq
      omega
    calc ∑ i ∈ Finset.Ico (idx - lowbit idx) idx, s.getD i 0
        ≤ ∑ i ∈ Finset.Ico 0 s.length, s.getD i 0 :=
          Finset.sum_le_sum_of_subset hsub
      _ = ((s.take s.length).drop 0).sum :=
          (sum_drop_take_eq_sum_Ico s (Nat.le_refl _)).symm
      _ = s.sum := by simp only [List.take_length, List.drop_zero]
  rcases lt_or_ge idx m with hlt | hge
  · rw [hinv.done_eq idx hidx1 hlt hidx_sz]
    exact hico_le
  · rw [hinv.todo_eq idx hidx1 hge hidx_sz]
    have hfilt_le :
        (∑ c ∈ (fenwickChildren idx).filter (· < m),
          ∑ i ∈ Finset.Ico (c - lowbit c) c, s.getD i 0) ≤
        ∑ c ∈ fenwickChildren idx,
          ∑ i ∈ Finset.Ico (c - lowbit c) c, s.getD i 0 :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hpart :
        s.getD (idx - 1) 0 +
          ∑ c ∈ fenwickChildren idx, ∑ i ∈ Finset.Ico (c - lowbit c) c, s.getD i 0 =
        ∑ i ∈ Finset.Ico (idx - lowbit idx) idx, s.getD i 0 := by
      conv_rhs =>
        rw [← insert_biUnion_fenwickChildren hidx1,
          Finset.sum_insert (notMem_biUnion_fenwickChildren idx),
          Finset.sum_biUnion (pairwiseDisjoint_fenwickChildren idx)]
    omega

/-- Over `ℕ`, adding `tree[m - 1]` into its in-range parent `p = m + lowbit m` never exceeds
`s.sum`. -/
theorem BuildInv.parent_add_le_sum {s : List ℕ} {m : ℕ} {tree : Array ℕ}
    (hm1 : 1 ≤ m) (hms : m ≤ s.length) (hinv : BuildInv s m tree)
    (hp : m + lowbit m ≤ s.length) :
    tree[m + lowbit m - 1]'(by have := hinv.size_eq; omega) +
      tree[m - 1]'(by have := hinv.size_eq; omega) ≤ s.sum := by
  have hinv' := hinv.step hm1 hms
  simp only [hp, ↓reduceIte] at hinv'
  have hp1 : 1 ≤ m + lowbit m := by omega
  have hpsz : m + lowbit m ≤ (tree.modify (m + lowbit m - 1)
      (· + tree[m - 1]'(by have := hinv.size_eq; omega))).size := by
    rw [Array.size_modify, hinv.size_eq]
    exact hp
  have hle := hinv'.getElem_le_sum hp1 hpsz
  simpa only [Array.getElem_modify, ↓reduceIte] using hle

private theorem buildLoop_spec {α : Type*} [AddCommMonoid α]
    (s : List α) (m : ℕ) {tree : Array α}
    (hm1 : 1 ≤ m) (hmn : m ≤ s.length + 1) (hinv : BuildInv s m tree) :
    BuildInv s (s.length + 1) (buildLoop s.length m tree) := by
  fun_induction buildLoop s.length m tree with
  | case1 m tree hguard _ _ ih =>
    exact ih (by omega) (by omega) (hinv.step hm1 hguard.2.1)
  | case2 m tree hguard =>
    obtain rfl : m = s.length + 1 := by have := hinv.size_eq; omega
    exact hinv

/-- `ofArray a` constructs a valid Fenwick tree representing `a.toList`. -/
theorem valid_ofArray {α : Type*} [AddCommMonoid α] (a : Array α) :
    Valid (ofArray a) a.toList := by
  unfold ofArray
  rw [← Array.length_toList (xs := a)]
  exact (buildLoop_spec a.toList 1 (Nat.le_refl 1) (by omega) (buildInv_init a)).to_valid

@[simp]
theorem size_ofArray {α : Type*} [AddCommMonoid α] (a : Array α) :
    (ofArray a).size = a.size := by
  have hv := (valid_ofArray a).1
  simpa only [size, Array.length_toList] using hv

theorem valid_ofList {α : Type*} [AddCommMonoid α] (s : List α) :
    Valid (ofList s) s := by
  change Valid (ofArray s.toArray) s
  simpa only [List.toList_toArray] using valid_ofArray s.toArray

@[simp]
theorem size_ofList {α : Type*} [AddCommMonoid α] (s : List α) :
    (ofList s).size = s.length :=
  (valid_ofList s).size_eq

@[simp]
theorem ofList_nil {α : Type*} [AddCommMonoid α] :
    ofList ([] : List α) = zeros 0 :=
  (valid_ofList []).unique (valid_zeros 0)

/-! ## Group operations (`rangeSum`, `get`, `set`) -/

/-- Half-open range sum `((s.take r).drop l).sum` over `[AddCommGroup α]`, computed as the
difference `prefixSum t r - prefixSum t l` when `l < r`. -/
@[expose] def rangeSum {α : Type*} [AddCommGroup α] (t : FenwickTree α) (l r : ℕ) : α :=
  if l < r then prefixSum t r - prefixSum t l else 0

theorem rangeSum_eq {α : Type*} [AddCommGroup α]
    {t : FenwickTree α} {s : List α} (hv : Valid t s) (l r : ℕ) :
    rangeSum t l r = ((s.take r).drop l).sum := by
  unfold rangeSum
  split_ifs with hlt
  · rw [prefixSum_eq hv r, prefixSum_eq hv l]
    conv_lhs => rw [take_eq_take_append_drop s (Nat.le_of_lt hlt), List.sum_append]
    exact add_sub_cancel_left _ _
  · have hdrop : (s.take r).drop l = [] :=
      List.drop_eq_nil_of_le ((List.length_take_le r s).trans (by omega))
    rw [hdrop, List.sum_nil]

/-- Point query at `0`-based index `pos` (`0` out of bounds). -/
@[expose] def get {α : Type*} [AddCommGroup α] (t : FenwickTree α) (pos : ℕ) : α :=
  rangeSum t pos (pos + 1)

theorem get_eq {α : Type*} [AddCommGroup α]
    {t : FenwickTree α} {s : List α} (hv : Valid t s) (pos : ℕ) :
    get t pos = s.getD pos 0 := by
  unfold get
  rw [rangeSum_eq hv]
  rcases lt_or_ge pos s.length with hlt | hge
  · have htake : s.take (pos + 1) = s.take pos ++ [s[pos]'hlt] := by
      rw [List.take_add_one, getElem?_pos s pos hlt, Option.toList_some]
    have hlen : (s.take pos).length = pos := List.length_take_of_le (Nat.le_of_lt hlt)
    rw [htake, List.drop_append_of_le_length (by rw [hlen]),
      List.drop_eq_nil_of_le (by rw [hlen]), List.nil_append, List.sum_singleton,
      List.getD_eq_getElem _ _ hlt]
  · have hdrop : (s.take (pos + 1)).drop pos = [] :=
      List.drop_eq_nil_of_le ((List.length_take_le' (pos + 1) s).trans hge)
    rw [hdrop, List.sum_nil, List.getD_eq_default _ _ hge]

/-- Point assignment setting `s[pos] := v` (`no-op` when `t.size ≤ pos`). -/
@[expose] def set {α : Type*} [AddCommGroup α]
    (t : FenwickTree α) (pos : ℕ) (v : α) : FenwickTree α :=
  if pos < t.tree.size then add t pos (v - get t pos) else t

theorem valid_set {α : Type*} [AddCommGroup α]
    {t : FenwickTree α} {s : List α} (hv : Valid t s) (pos : ℕ) (v : α) :
    Valid (set t pos v) (s.set pos v) := by
  unfold set
  split_ifs with hpos
  · rw [get_eq hv]
    have hadd := valid_add hv pos (v - s.getD pos 0)
    unfold PrefixSums.addAt at hadd
    rwa [add_sub_cancel] at hadd
  · have hge : s.length ≤ pos := by have := hv.1; omega
    rwa [List.set_eq_of_length_le hge]

@[simp]
theorem size_set {α : Type*} [AddCommGroup α]
    (t : FenwickTree α) (pos : ℕ) (v : α) :
    (set t pos v).size = t.size := by
  unfold set
  split_ifs <;> simp

theorem set_of_size_le {α : Type*} [AddCommGroup α]
    (t : FenwickTree α) {pos : ℕ} (v : α) (h : t.size ≤ pos) :
    set t pos v = t := by
  unfold set size at *
  exact ite_eq_right (by omega)

end FenwickTree

end Cslib.DataStructure
