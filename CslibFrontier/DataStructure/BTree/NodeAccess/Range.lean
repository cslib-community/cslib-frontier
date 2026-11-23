/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.NodeAccess.Basic
public import CslibFrontier.DataStructure.BTree.Height
public import CslibFrontier.DataStructure.BTree.Range

/-!
# External-memory closed-interval queries on classic B-trees

Closed-interval range queries (`rangeR`) over the `PFunctor.FreeM` node-access oracle of
`Cslib.DataStructure.BTree.NodeAccess`. `rangeR` takes only a descent bound `fuel : ℕ`, interval
endpoints `lo hi : α`, and an optional root handle `root : Option H`: empty leaves (`none`) return
`[]` with `0` page reads, and each entered node (`some h`) issues one `readNode` query before
`rangeScan` traverses its separator triples in memory, pruning any child excluded by its adjacent
separators.

When `Denotes s root tr` and `tr.height ≤ fuel`:
1. `eval_rangeR` proves `eval s (rangeR fuel lo hi root) = BTree.range lo hi tr`.
2. `countQueries_rangeR_eq` proves `countQueries s (rangeR fuel lo hi root) = rangeVisits lo hi tr`,
   the structural page-read count on `tr`.
3. `countQueries_rangeR_of_occupied`, `countQueries_rangeR`, and `countQueries_rangeR_le_log` bound
   the page reads by `2 * tr.height + (BTree.range lo hi tr).length` (and
   `2 * (Nat.log t ((tr.size + 1) / 2) + 1) + (BTree.range lo hi tr).length` on `IsWF t tr`):
   a subtree wholly inside `[lo, hi]` reads at most one page per returned entry because every
   occupied node holds at least one key when `2 ≤ t`, while at each depth at most one node
   straddles `lo` and at most one straddles `hi`.

## Main definitions

* `NodeAccess.rangeScan`, `NodeAccess.rangeR`: closed-interval query over `nodeQuery`.
* `NodeAccess.rangeVisits`: pure page-read recurrence on `BTree α β` characterizing `rangeR`'s
  structural query count.

## Main results

* `NodeAccess.eval_rangeR`: `eval` equals `BTree.range` under `Denotes s root tr` and
  `tr.height ≤ fuel`.
* `NodeAccess.countQueries_rangeR_eq`: `countQueries` equals `rangeVisits lo hi tr` under
  `Denotes s root tr` and `tr.height ≤ fuel`.
* `NodeAccess.countQueries_rangeR_of_occupied`, `NodeAccess.countQueries_rangeR`,
  `NodeAccess.countQueries_rangeR_le_log`: output-sensitive `2 * height + k` and logarithmic
  page-read bounds.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 18][CLRS2009]

Adapted from `cslib-community/EpsilonEridani` at commit `1966ab476`
([EpsilonEridani/Algorithms/Lean/BTree/Cost/Range.lean](https://github.com/cslib-community/EpsilonEridani/blob/1966ab476f5db00425c83e19857fd38ba01143c4/EpsilonEridani/Algorithms/Lean/BTree/Cost/Range.lean)),
recast from monadic node-visit annotations to structural `PFunctor.FreeM` page-read queries.
-/

public section

namespace Cslib.DataStructure.BTree.NodeAccess

open PFunctor.FreeM

variable {α β H : Type} [LinearOrder α]

/-- Within-page scan for `rangeR`: traverses an already-read page's entries without issuing extra
page reads for the current node, recursing into children permitted by `[lo, hi]`. -/
@[expose] def rangeScan (rec : Option H → NodeM α β H (List (α × β))) (lo hi : α) :
    Option H → List (PageEntry α β H) → NodeM α β H (List (α × β))
  | first, [] => rec first
  | first, ⟨k, v, c⟩ :: rs => do
    let below ← if lo ≤ k then rec first else pure []
    if k ≤ hi then
      let after ← rangeScan rec lo hi c rs
      pure (below ++ (if lo ≤ k then [(k, v)] else []) ++ after)
    else
      pure below

/-- External-memory closed-interval query `[lo, hi]` over `nodeQuery`. -/
@[expose] def rangeR : ℕ → α → α → Option H → NodeM α β H (List (α × β))
  | 0, _, _, _ => pure []
  | _ + 1, _, _, none => pure []
  | fuel + 1, lo, hi, some h => do
    let page ← readNode h
    rangeScan (rangeR fuel lo hi) lo hi page.first page.rest

/-- Structural page-read count of a pruned closed-interval traversal on `BTree α β`. -/
def rangeVisits (lo hi : α) : BTree α β → ℕ
  | .leaf => 0
  | .node first [] => rangeVisits lo hi first + 1
  | .node first ((k, _, c) :: rest) =>
    (if lo ≤ k then rangeVisits lo hi first else 0) +
      (if k ≤ hi then rangeVisits lo hi (.node c rest) else 1)
termination_by tr => sizeOf tr

@[simp] theorem rangeVisits_leaf (lo hi : α) :
    rangeVisits lo hi (.leaf : BTree α β) = 0 := by
  rw [rangeVisits]

@[simp] theorem rangeVisits_node_nil (lo hi : α) (first : BTree α β) :
    rangeVisits lo hi (.node first []) = rangeVisits lo hi first + 1 := by
  rw [rangeVisits]

@[simp] theorem rangeVisits_node_cons (lo hi k : α) (v : β) (first c : BTree α β)
    (rest : List (BTree.Triple α β)) :
    rangeVisits lo hi (.node first ((k, v, c) :: rest)) =
      (if lo ≤ k then rangeVisits lo hi first else 0) +
        (if k ≤ hi then rangeVisits lo hi (.node c rest) else 1) := by
  rw [rangeVisits]

/-! ### Exact agreement with `BTree.range` and `rangeVisits` -/

private theorem rangeScan_spec {s : Store α β H} {fuel : ℕ} {lo hi : α}
    {r₀ : Option H} {first : BTree α β}
    {rs : List (PageEntry α β H)} {rest : List (BTree.Triple α β)}
    (hdf : Denotes s r₀ first) (hdr : DenotesRest s rs rest)
    (hrec : ∀ c ∈ (BTree.node first rest).children, ∀ r, Denotes s r c → c.height ≤ fuel →
      eval s (rangeR fuel lo hi r) = BTree.range lo hi c ∧
        countQueries s (rangeR fuel lo hi r) = rangeVisits lo hi c)
    (hf : (BTree.node first rest).height ≤ fuel + 1) :
    eval s (rangeScan (rangeR fuel lo hi) lo hi r₀ rs) = BTree.range lo hi (.node first rest) ∧
      1 + countQueries s (rangeScan (rangeR fuel lo hi) lo hi r₀ rs) =
        rangeVisits lo hi (.node first rest) := by
  induction rs generalizing r₀ first rest with
  | nil =>
    cases rest with
    | nil =>
      have hle := BTree.height_first_succ_le (first := first) (rest := [])
      obtain ⟨he, hq⟩ := hrec first List.mem_cons_self r₀ hdf (by omega)
      simp only [rangeScan, BTree.range_node_nil, rangeVisits_node_nil, hq]
      exact ⟨he, by omega⟩
    | cons e rest => exact (denotesRest_nil_cons s e rest hdr).elim
  | cons e rs ih =>
    obtain ⟨k, v, r₁⟩ := e
    cases rest with
    | nil => exact (denotesRest_cons_nil s ⟨k, v, r₁⟩ rs hdr).elim
    | cons e' rest' =>
      obtain ⟨k', v', c⟩ := e'
      obtain ⟨rfl, rfl, hdc, hdr'⟩ :=
        (denotesRest_cons_cons_iff s k k' v v' r₁ c rs rest').mp hdr
      have hle₁ := BTree.height_first_succ_le (first := first) (rest := (k, v, c) :: rest')
      have hle₂ := BTree.height_node_le_height_node_cons
        (first := first) (k := k) (v := v) (c := c) (rest := rest')
      obtain ⟨he₁, hq₁⟩ := hrec first List.mem_cons_self r₀ hdf (by omega)
      obtain ⟨he₂, hq₂⟩ := ih hdc hdr'
        (fun ch hch => hrec ch (BTree.children_node_subset_children_node_cons hch))
        (by omega)
      simp only [rangeScan, BTree.range_node_cons, rangeVisits_node_cons]
      by_cases hlo : lo ≤ k <;> by_cases hhi : k ≤ hi
      · refine ⟨?_, ?_⟩
        · simp only [hlo, hhi, ↓reduceIte, eval_bind, eval_pure, he₁, he₂, List.append_assoc]
        · simp only [hlo, hhi, ↓reduceIte, countQueries_bind, countQueries_pure, hq₁]
          omega
      · refine ⟨?_, ?_⟩
        · simp only [hlo, hhi, ↓reduceIte, eval_bind, eval_pure, he₁, List.append_nil]
        · simp only [hlo, hhi, ↓reduceIte, countQueries_bind, countQueries_pure, hq₁]
          omega
      · refine ⟨?_, ?_⟩
        · simp only [hlo, hhi, ↓reduceIte, eval_bind, eval_pure, he₂, List.nil_append]
        · simp only [hlo, hhi, ↓reduceIte, countQueries_bind, countQueries_pure]
          omega
      · refine ⟨?_, ?_⟩
        · simp only [hlo, hhi, ↓reduceIte, eval_bind, eval_pure, List.nil_append]
        · simp only [hlo, hhi, ↓reduceIte, countQueries_bind, countQueries_pure]

private theorem rangeR_spec {s : Store α β H} {fuel : ℕ} {lo hi : α} {root : Option H}
    {tr : BTree α β} (hd : Denotes s root tr) (hf : tr.height ≤ fuel) :
    eval s (rangeR fuel lo hi root) = BTree.range lo hi tr ∧
      countQueries s (rangeR fuel lo hi root) = rangeVisits lo hi tr := by
  induction tr generalizing fuel root with
  | leaf =>
    cases root with
    | none => cases fuel <;> simp [rangeR]
    | some h => exact (denotes_some_leaf s h hd).elim
  | node first rest ih₁ ih₂ =>
    cases root with
    | none => exact (denotes_none_node s first rest hd).elim
    | some h =>
      have hle := BTree.height_first_succ_le (first := first) (rest := rest)
      cases fuel with
      | zero => omega
      | succ fuel =>
        obtain ⟨hdf, hdr⟩ := (denotes_some_node_iff s h first rest).mp hd
        have hchildren : ∀ c ∈ (BTree.node first rest).children, ∀ r,
            Denotes s r c → c.height ≤ fuel →
            eval s (rangeR fuel lo hi r) = BTree.range lo hi c ∧
              countQueries s (rangeR fuel lo hi r) = rangeVisits lo hi c := by
          intro c hc r hdc hcf
          simp only [BTree.children_node, List.mem_cons, List.mem_map] at hc
          rcases hc with rfl | ⟨e, he, rfl⟩
          · exact ih₁ hdc hcf
          · exact ih₂ e he hdc hcf
        simp only [rangeR, eval_bind, eval_readNode, countQueries_bind, countQueries_readNode]
        exact rangeScan_spec hdf hdr hchildren hf

/-- `rangeR` evaluates to `BTree.range` whenever `root` denotes `tr` and `tr.height ≤ fuel`. -/
theorem eval_rangeR {s : Store α β H} {fuel : ℕ} {root : Option H} {tr : BTree α β}
    (hd : Denotes s root tr) (hf : tr.height ≤ fuel) (lo hi : α) :
    eval s (rangeR fuel lo hi root) = BTree.range lo hi tr :=
  (rangeR_spec hd hf).1

/-- `rangeR` issues `rangeVisits lo hi tr` page reads when `root` denotes `tr` and
`tr.height ≤ fuel`. -/
theorem countQueries_rangeR_eq {s : Store α β H} {fuel : ℕ} {root : Option H} {tr : BTree α β}
    (hd : Denotes s root tr) (hf : tr.height ≤ fuel) (lo hi : α) :
    countQueries s (rangeR fuel lo hi root) = rangeVisits lo hi tr :=
  (rangeR_spec hd hf).2

/-! ### Output-sensitive `2 * height + k` page-read bounds -/

section Bounds

variable {t : ℕ} {lo hi : α} {tr : BTree α β}

/-- When `[lo, hi]` contains every entry of `tr`, each occupied node contributes at least one
returned entry paying for its page read. -/
private theorem rangeVisits_add_rootKeys_le {lo hi : α} {tr : BTree α β} (ht : 2 ≤ t)
    (hc : ∀ c ∈ tr.children, BTree.Occupied t c) (hs : tr.toList.IsSortedAssoc)
    (hin : ∀ p ∈ tr.toList, lo ≤ p.1 ∧ p.1 ≤ hi) :
    rangeVisits lo hi tr + tr.rootKeys ≤ (BTree.range lo hi tr).length + 1 := by
  have occ {c : BTree α β} (ho : BTree.Occupied t c)
      (h : rangeVisits lo hi c + c.rootKeys ≤ (BTree.range lo hi c).length + 1) :
      rangeVisits lo hi c ≤ (BTree.range lo hi c).length := by
    cases c with
    | leaf => simp
    | node _ _ =>
      have := ho.one_le_rootKeys ht (by simp)
      omega
  match tr with
  | .leaf => simp
  | .node first [] =>
    have hfirst : BTree.Occupied t first := hc first (by simp)
    have ih := rangeVisits_add_rootKeys_le ht (fun c h => hfirst.of_mem_children h)
      (by simpa using hs) (fun p hp => hin p (by simpa using hp))
    have := occ hfirst ih
    simp only [rangeVisits_node_nil, BTree.rootKeys_node, List.length_nil, BTree.range_node_nil]
    omega
  | .node first ((k, v, c) :: rest) =>
    obtain ⟨hsf, hsn, -, -⟩ := BTree.isSortedAssoc_toList_node_cons_iff.1 hs
    obtain ⟨hfirst, hcf, hcn⟩ := BTree.occupied_children_node_cons hc
    have hk := hin (k, v) (BTree.mem_toList_node_cons.2 (Or.inr (Or.inl rfl)))
    have ih₁ := rangeVisits_add_rootKeys_le ht hcf hsf
      (fun p hp => hin p (BTree.mem_toList_node_cons.2 (Or.inl hp)))
    have ih₂ := rangeVisits_add_rootKeys_le ht hcn hsn
      (fun p hp => hin p (BTree.mem_toList_node_cons.2 (Or.inr (Or.inr hp))))
    have := occ hfirst ih₁
    simp only [BTree.rootKeys_node, List.length_cons] at ih₂ ⊢
    rw [rangeVisits_node_cons, BTree.length_range_node_cons lo hi]
    simp only [hk.1, hk.2, ↓reduceIte]
    omega
termination_by sizeOf tr

private theorem rangeVisits_le_of_forall_mem (ht : 2 ≤ t) (ho : BTree.Occupied t tr)
    (hs : tr.toList.IsSortedAssoc) (hin : ∀ p ∈ tr.toList, lo ≤ p.1 ∧ p.1 ≤ hi) :
    rangeVisits lo hi tr ≤ (BTree.range lo hi tr).length := by
  have h := rangeVisits_add_rootKeys_le ht (fun c hc => ho.of_mem_children hc) hs hin
  cases tr with
  | leaf => simp
  | node _ _ =>
    have := ho.one_le_rootKeys ht (by simp)
    omega

private theorem rangeVisits_le_of_forall_lo_le {lo hi : α} {tr : BTree α β} (ht : 2 ≤ t)
    (hc : ∀ c ∈ tr.children, BTree.Occupied t c) (hs : tr.toList.IsSortedAssoc)
    (hlo : ∀ p ∈ tr.toList, lo ≤ p.1) :
    rangeVisits lo hi tr ≤ tr.height + (BTree.range lo hi tr).length := by
  match tr with
  | .leaf => simp
  | .node first [] =>
    have hfirst : BTree.Occupied t first := hc first (by simp)
    have ih := rangeVisits_le_of_forall_lo_le (hi := hi) ht
      (fun c h => hfirst.of_mem_children h) (by simpa using hs)
      (fun p hp => hlo p (by simpa using hp))
    have e := BTree.height_first_succ_le (first := first) (rest := [])
    rw [rangeVisits_node_nil, BTree.range_node_nil]
    omega
  | .node first ((k, v, c) :: rest) =>
    obtain ⟨hsf, hsn, hlt, -⟩ := BTree.isSortedAssoc_toList_node_cons_iff.1 hs
    obtain ⟨hfirst, hcf, hcn⟩ := BTree.occupied_children_node_cons hc
    have hk : lo ≤ k := hlo (k, v) (BTree.mem_toList_node_cons.2 (Or.inr (Or.inl rfl)))
    have e₁ := BTree.height_first_succ_le (first := first) (rest := (k, v, c) :: rest)
    have e₂ := BTree.height_node_le_height_node_cons (first := first) (k := k) (v := v) (c := c)
      (rest := rest)
    rw [rangeVisits_node_cons, BTree.length_range_node_cons lo hi]
    by_cases hhi : k ≤ hi
    · have h₁ := rangeVisits_le_of_forall_mem ht hfirst hsf
        (fun p hp => ⟨hlo p (BTree.mem_toList_node_cons.2 (Or.inl hp)),
          ((hlt p hp).trans_le hhi).le⟩)
      have h₂ := rangeVisits_le_of_forall_lo_le (hi := hi) ht hcn hsn
        (fun p hp => hlo p (BTree.mem_toList_node_cons.2 (Or.inr (Or.inr hp))))
      simp only [hk, hhi, ↓reduceIte]
      omega
    · have h₁ := rangeVisits_le_of_forall_lo_le (hi := hi) ht hcf hsf
        (fun p hp => hlo p (BTree.mem_toList_node_cons.2 (Or.inl hp)))
      simp only [hk, hhi, ↓reduceIte]
      omega
termination_by sizeOf tr

private theorem rangeVisits_le_of_forall_le_hi {lo hi : α} {tr : BTree α β} (ht : 2 ≤ t)
    (hc : ∀ c ∈ tr.children, BTree.Occupied t c) (hs : tr.toList.IsSortedAssoc)
    (hhi : ∀ p ∈ tr.toList, p.1 ≤ hi) :
    rangeVisits lo hi tr ≤ tr.height + (BTree.range lo hi tr).length := by
  match tr with
  | .leaf => simp
  | .node first [] =>
    have hfirst : BTree.Occupied t first := hc first (by simp)
    have ih := rangeVisits_le_of_forall_le_hi (lo := lo) ht
      (fun c h => hfirst.of_mem_children h) (by simpa using hs)
      (fun p hp => hhi p (by simpa using hp))
    have e := BTree.height_first_succ_le (first := first) (rest := [])
    rw [rangeVisits_node_nil, BTree.range_node_nil]
    omega
  | .node first ((k, v, c) :: rest) =>
    obtain ⟨hsf, hsn, -, hgt⟩ := BTree.isSortedAssoc_toList_node_cons_iff.1 hs
    obtain ⟨-, hcf, hcn⟩ := BTree.occupied_children_node_cons hc
    have hk : k ≤ hi := hhi (k, v) (BTree.mem_toList_node_cons.2 (Or.inr (Or.inl rfl)))
    have e₁ := BTree.height_first_succ_le (first := first) (rest := (k, v, c) :: rest)
    have e₂ := BTree.height_node_le_height_node_cons (first := first) (k := k) (v := v) (c := c)
      (rest := rest)
    rw [rangeVisits_node_cons, BTree.length_range_node_cons lo hi]
    by_cases hlo : lo ≤ k
    · have h₁ := rangeVisits_le_of_forall_le_hi (lo := lo) ht hcf hsf
        (fun p hp => hhi p (BTree.mem_toList_node_cons.2 (Or.inl hp)))
      have h₂ := rangeVisits_add_rootKeys_le ht hcn hsn
        (fun p hp => ⟨hlo.trans (hgt p hp).le,
          hhi p (BTree.mem_toList_node_cons.2 (Or.inr (Or.inr hp)))⟩)
      simp only [BTree.rootKeys_node] at h₂
      simp only [hk, hlo, ↓reduceIte]
      omega
    · have h₂ := rangeVisits_le_of_forall_le_hi (lo := lo) ht hcn hsn
        (fun p hp => hhi p (BTree.mem_toList_node_cons.2 (Or.inr (Or.inr hp))))
      simp only [hk, hlo, ↓reduceIte]
      omega
termination_by sizeOf tr

/-- Pure page-visit bound `rangeVisits lo hi tr ≤ 2 * tr.height + (BTree.range lo hi tr).length`
on any sorted tree whose children satisfy `Occupied t` for `2 ≤ t`. -/
theorem rangeVisits_le_of_occupied {lo hi : α} {tr : BTree α β} (ht : 2 ≤ t)
    (hc : ∀ c ∈ tr.children, BTree.Occupied t c) (hs : tr.toList.IsSortedAssoc) :
    rangeVisits lo hi tr ≤ 2 * tr.height + (BTree.range lo hi tr).length := by
  match tr with
  | .leaf => simp
  | .node first [] =>
    have hfirst : BTree.Occupied t first := hc first (by simp)
    have ih := rangeVisits_le_of_occupied (lo := lo) (hi := hi) ht
      (fun c h => hfirst.of_mem_children h) (by simpa using hs)
    have e := BTree.height_first_succ_le (first := first) (rest := [])
    rw [rangeVisits_node_nil, BTree.range_node_nil]
    omega
  | .node first ((k, v, c) :: rest) =>
    obtain ⟨hsf, hsn, hlt, hgt⟩ := BTree.isSortedAssoc_toList_node_cons_iff.1 hs
    obtain ⟨-, hcf, hcn⟩ := BTree.occupied_children_node_cons hc
    have e₁ := BTree.height_first_succ_le (first := first) (rest := (k, v, c) :: rest)
    have e₂ := BTree.height_node_le_height_node_cons (first := first) (k := k) (v := v) (c := c)
      (rest := rest)
    rw [rangeVisits_node_cons, BTree.length_range_node_cons lo hi]
    by_cases hlo : lo ≤ k <;> by_cases hhi : k ≤ hi
    · have h₁ := rangeVisits_le_of_forall_le_hi (lo := lo) ht hcf hsf
        (fun p hp => ((hlt p hp).trans_le hhi).le)
      have h₂ := rangeVisits_le_of_forall_lo_le (hi := hi) ht hcn hsn
        (fun p hp => (hlo.trans_lt (hgt p hp)).le)
      simp only [hlo, hhi, ↓reduceIte]
      omega
    · have h₁ := rangeVisits_le_of_occupied (lo := lo) (hi := hi) ht hcf hsf
      simp only [hlo, hhi, ↓reduceIte]
      omega
    · have h₂ := rangeVisits_le_of_occupied (lo := lo) (hi := hi) ht hcn hsn
      simp only [hlo, hhi, ↓reduceIte]
      omega
    · simp only [hlo, hhi, ↓reduceIte]
      omega
termination_by sizeOf tr

/-- `rangeR` issues at most `2 * tr.height + (BTree.range lo hi tr).length` page reads on any
sorted tree with `Occupied t` children (`2 ≤ t`) when `Denotes s root tr` and `tr.height ≤ fuel`. -/
theorem countQueries_rangeR_of_occupied {s : Store α β H} {fuel : ℕ} {root : Option H}
    {tr : BTree α β} (ht : 2 ≤ t) (hc : ∀ c ∈ tr.children, BTree.Occupied t c)
    (hs : tr.toList.IsSortedAssoc) (hd : Denotes s root tr) (hf : tr.height ≤ fuel) (lo hi : α) :
    countQueries s (rangeR fuel lo hi root) ≤ 2 * tr.height + (BTree.range lo hi tr).length := by
  rw [countQueries_rangeR_eq hd hf lo hi]
  exact rangeVisits_le_of_occupied ht hc hs

/-- `rangeR` issues at most `2 * tr.height + (BTree.range lo hi tr).length` page reads on a
well-formed B-tree when `Denotes s root tr` and `tr.height ≤ fuel`. -/
theorem countQueries_rangeR {s : Store α β H} {fuel : ℕ} {root : Option H}
    {tr : BTree α β} (hwf : BTree.IsWF t tr) (hd : Denotes s root tr) (hf : tr.height ≤ fuel)
    (lo hi : α) :
    countQueries s (rangeR fuel lo hi root) ≤ 2 * tr.height + (BTree.range lo hi tr).length :=
  countQueries_rangeR_of_occupied hwf.two_le hwf.occupied_of_mem_children hwf.sorted hd hf lo hi

/-- Logarithmic `O(log_t n + k)` page-read bound for `rangeR` on a well-formed B-tree. -/
theorem countQueries_rangeR_le_log {s : Store α β H} {fuel : ℕ} {root : Option H}
    {tr : BTree α β} (hwf : BTree.IsWF t tr) (hd : Denotes s root tr) (hf : tr.height ≤ fuel)
    (lo hi : α) :
    countQueries s (rangeR fuel lo hi root) ≤
      2 * (Nat.log t ((tr.size + 1) / 2) + 1) + (BTree.range lo hi tr).length :=
  (countQueries_rangeR hwf hd hf lo hi).trans (by have := hwf.height_le_log; omega)

end Bounds

end Cslib.DataStructure.BTree.NodeAccess
