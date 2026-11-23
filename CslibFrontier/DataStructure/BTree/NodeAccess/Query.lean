/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.NodeAccess.Basic
public import CslibFrontier.DataStructure.BTree.Height
public import CslibFrontier.DataStructure.BTree.MinMax
public import CslibFrontier.DataStructure.BTree.PredSucc
public import CslibFrontier.DataStructure.BTree.Rank

/-!
# External-memory point queries on classic B-trees

Point queries (`minR`, `maxR`, `lookupR`, `containsR`, `predR`, `succR`, `rankR`) over the
`PFunctor.FreeM` node-access oracle of `Cslib.DataStructure.BTree.NodeAccess`. Each program takes
only a descent bound `fuel : ℕ` and an optional root handle `root : Option H`: empty leaves
(`none`) return immediately with `0` page reads, and each dereferenced node handle (`some h`)
issues one `readNode` (or `readRankedNode` for `rankR`) query before scanning the returned page in
memory and descending into at most one child.

Consequently:
1. Under **every** store `s` (even cyclic or malformed handle graphs), each query issues at most
   `fuel` page reads.
2. Whenever `Denotes s root tr` (or `DenotesRanked s root tr` for `rankR`) and `tr.height ≤ fuel`,
   `eval` equals the pure `BTree` query (`min?`, `max?`, `lookup`, `contains`, `pred?`, `succ?`,
   `rank`) and `countQueries` is at most `tr.height` (independent of excess `fuel`), hence at most
   `Nat.log t ((tr.size + 1) / 2) + 1` on any well-formed `IsWF t tr`.

## Main definitions

* `NodeAccess.minR`, `NodeAccess.maxScan`, `NodeAccess.maxR`: extremal-entry queries over
  `nodeQuery`.
* `NodeAccess.lookupScan`, `NodeAccess.lookupR`, `NodeAccess.containsR`: key search and membership
  queries over `nodeQuery`.
* `NodeAccess.predScan`, `NodeAccess.predR`, `NodeAccess.succScan`, `NodeAccess.succR`: strict
  predecessor and successor queries over `nodeQuery`.
* `NodeAccess.rankScan`, `NodeAccess.rankR`: strict rank query over `rankedNodeQuery`.

## Main results

* `NodeAccess.countQueries_minR_le_fuel`, `countQueries_maxR_le_fuel`,
  `countQueries_lookupR_le_fuel`, `countQueries_containsR_le_fuel`, `countQueries_predR_le_fuel`,
  `countQueries_succR_le_fuel`, `countQueries_rankR_le_fuel`: universal `≤ fuel` page-read bounds
  over arbitrary stores.
* `NodeAccess.eval_minR`, `eval_maxR`, `eval_lookupR`, `eval_containsR`, `eval_predR`,
  `eval_succR`, `eval_rankR`: agreement with pure `BTree` operations under `Denotes` /
  `DenotesRanked` and `tr.height ≤ fuel`.
* `NodeAccess.countQueries_minR_le`, `countQueries_maxR_le`, `countQueries_lookupR_le`,
  `countQueries_containsR_le`, `countQueries_predR_le`, `countQueries_succR_le`,
  `countQueries_rankR_le`, and their `*_le_log` corollaries: exact `≤ tr.height` and
  `≤ Nat.log t ((tr.size + 1) / 2) + 1` page-read bounds.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 18][CLRS2009]
-/

public section

namespace Cslib.DataStructure.BTree.NodeAccess

open PFunctor.FreeM

section Extremal

variable {α β H : Type}

/-- External-memory minimum query: follow first-child handles, reading at most one page per
level. -/
@[expose] def minR : ℕ → Option H → NodeM α β H (Option (α × β))
  | 0, _ => pure none
  | _ + 1, none => pure none
  | fuel + 1, some h => do
    let page ← readNode h
    match ← minR fuel page.first with
    | some p => pure (some p)
    | none => pure (page.rest.head?.map fun e => (e.key, e.val))

/-- Within-page scan for `maxR`: walks to the last entry of an already-read page without issuing
extra reads, then recurses into the rightmost child. -/
@[expose] def maxScan (rec : Option H → NodeM α β H (Option (α × β))) :
    Option H → List (PageEntry α β H) → NodeM α β H (Option (α × β))
  | first, [] => rec first
  | _, [⟨k, v, c⟩] => do
    match ← rec c with
    | some p => pure (some p)
    | none => pure (some (k, v))
  | _, ⟨_, _, c⟩ :: e :: rs => maxScan rec c (e :: rs)

/-- External-memory maximum query: read each page along the rightmost spine once. -/
@[expose] def maxR : ℕ → Option H → NodeM α β H (Option (α × β))
  | 0, _ => pure none
  | _ + 1, none => pure none
  | fuel + 1, some h => do
    let page ← readNode h
    maxScan (maxR fuel) page.first page.rest

theorem countQueries_minR_le_fuel (s : Store α β H) (fuel : ℕ) (root : Option H) :
    countQueries s (minR fuel root) ≤ fuel := by
  induction fuel generalizing root with
  | zero => simp [minR]
  | succ fuel ih =>
    cases root with
    | none => simp [minR]
    | some h =>
      simp only [minR, countQueries_bind, countQueries_readNode, eval_readNode]
      have hsub := ih (s h).first
      split <;> simp only [countQueries_pure] <;> omega

private theorem countQueries_maxScan_le (s : Store α β H)
    (rec : Option H → NodeM α β H (Option (α × β))) {B : ℕ}
    (hrec : ∀ r, countQueries s (rec r) ≤ B) (first : Option H)
    (rs : List (PageEntry α β H)) :
    countQueries s (maxScan rec first rs) ≤ B := by
  induction rs generalizing first with
  | nil => exact hrec first
  | cons e₁ rs ih =>
    obtain ⟨k₁, v₁, c₁⟩ := e₁
    cases rs with
    | nil =>
      simp only [maxScan, countQueries_bind]
      have hc := hrec c₁
      split <;> simp only [countQueries_pure] <;> omega
    | cons e₂ rs' =>
      exact ih c₁

theorem countQueries_maxR_le_fuel (s : Store α β H) (fuel : ℕ) (root : Option H) :
    countQueries s (maxR fuel root) ≤ fuel := by
  induction fuel generalizing root with
  | zero => simp [maxR]
  | succ fuel ih =>
    cases root with
    | none => simp [maxR]
    | some h =>
      simp only [maxR, countQueries_bind, countQueries_readNode, eval_readNode]
      have hscan := countQueries_maxScan_le s (maxR fuel) ih (s h).first (s h).rest
      omega

private theorem head_map_eq_of_denotesRest {s : Store α β H} {rs : List (PageEntry α β H)}
    {rest : List (BTree.Triple α β)} (hd : DenotesRest s rs rest) :
    (rs.head?.map fun e => (e.key, e.val)) =
      (rest.head?.map fun (e : BTree.Triple α β) => (e.1, e.val)) := by
  cases rs with
  | nil =>
    cases rest with
    | nil => rfl
    | cons e rest => exact (denotesRest_nil_cons s e rest hd).elim
  | cons e rs =>
    obtain ⟨k, v, r⟩ := e
    cases rest with
    | nil => exact (denotesRest_cons_nil s ⟨k, v, r⟩ rs hd).elim
    | cons e' rest =>
      obtain ⟨k', v', c⟩ := e'
      obtain ⟨rfl, rfl, _, _⟩ := (denotesRest_cons_cons_iff s k k' v v' r c rs rest).mp hd
      rfl

/-- `minR` evaluates to `BTree.min?` whenever `root` denotes `tr` and `tr.height ≤ fuel`. -/
theorem eval_minR {s : Store α β H} {fuel : ℕ} {root : Option H} {tr : BTree α β}
    (hd : Denotes s root tr) (hf : tr.height ≤ fuel) :
    eval s (minR fuel root) = BTree.min? tr := by
  induction tr generalizing fuel root with
  | leaf =>
    cases root with
    | none => cases fuel <;> rfl
    | some h => exact (denotes_some_leaf s h hd).elim
  | node first rest ih₁ _ =>
    cases root with
    | none => exact (denotes_none_node s first rest hd).elim
    | some h =>
      have hpos : 1 ≤ (BTree.node first rest).height := by
        have := BTree.height_first_succ_le (first := first) (rest := rest)
        omega
      cases fuel with
      | zero => omega
      | succ fuel =>
        obtain ⟨hdf, hdr⟩ := (denotes_some_node_iff s h first rest).mp hd
        have hf₁ : first.height ≤ fuel := by
          have := BTree.height_first_succ_le (first := first) (rest := rest)
          omega
        simp only [minR, eval_bind, eval_readNode, ih₁ hdf hf₁, BTree.min?_node,
          head_map_eq_of_denotesRest hdr]
        cases BTree.min? first <;> simp only [eval_pure] <;> rfl

/-- `minR` reads at most `tr.height` pages when `root` denotes `tr` and `tr.height ≤ fuel`. -/
theorem countQueries_minR_le {s : Store α β H} {fuel : ℕ} {root : Option H} {tr : BTree α β}
    (hd : Denotes s root tr) (hf : tr.height ≤ fuel) :
    countQueries s (minR fuel root) ≤ tr.height := by
  induction tr generalizing fuel root with
  | leaf =>
    cases root with
    | none => cases fuel <;> simp [minR]
    | some h => exact (denotes_some_leaf s h hd).elim
  | node first rest ih₁ _ =>
    cases root with
    | none => exact (denotes_none_node s first rest hd).elim
    | some h =>
      have hle := BTree.height_first_succ_le (first := first) (rest := rest)
      cases fuel with
      | zero => omega
      | succ fuel =>
        obtain ⟨hdf, _⟩ := (denotes_some_node_iff s h first rest).mp hd
        have hsub := ih₁ (fuel := fuel) hdf (by omega)
        simp only [minR, countQueries_bind, countQueries_readNode, eval_readNode]
        split <;> simp only [countQueries_pure] <;> omega

private theorem maxScan_spec {s : Store α β H} {fuel : ℕ}
    {r₀ : Option H} {first : BTree α β}
    {rs : List (PageEntry α β H)} {rest : List (BTree.Triple α β)}
    (hdf : Denotes s r₀ first) (hdr : DenotesRest s rs rest)
    (hrec : ∀ c ∈ (BTree.node first rest).children, ∀ r, Denotes s r c → c.height ≤ fuel →
      eval s (maxR fuel r) = BTree.max? c ∧ countQueries s (maxR fuel r) ≤ c.height)
    (hf : (BTree.node first rest).height ≤ fuel + 1) :
    eval s (maxScan (maxR fuel) r₀ rs) = BTree.max? (.node first rest) ∧
      1 + countQueries s (maxScan (maxR fuel) r₀ rs) ≤ (BTree.node first rest).height := by
  induction rs generalizing r₀ first rest with
  | nil =>
    cases rest with
    | nil =>
      have hle := BTree.height_first_succ_le (first := first) (rest := [])
      obtain ⟨he, hq⟩ := hrec first List.mem_cons_self r₀ hdf (by omega)
      simp only [maxScan, BTree.max?_node_nil]
      exact ⟨he, by omega⟩
    | cons e rest => exact (denotesRest_nil_cons s e rest hdr).elim
  | cons e₁ rs ih =>
    obtain ⟨k₁, v₁, r₁⟩ := e₁
    cases rest with
    | nil => exact (denotesRest_cons_nil s ⟨k₁, v₁, r₁⟩ rs hdr).elim
    | cons e₁' rest' =>
      obtain ⟨k₁', v₁', c₁⟩ := e₁'
      obtain ⟨rfl, rfl, hdc₁, hdr'⟩ :=
        (denotesRest_cons_cons_iff s k₁ k₁' v₁ v₁' r₁ c₁ rs rest').mp hdr
      cases rs with
      | nil =>
        cases rest' with
        | nil =>
          have hc_mem : c₁ ∈ (BTree.node first [(k₁, v₁, c₁)]).children := by simp
          have hle := BTree.height_succ_le_of_mem_children hc_mem
          obtain ⟨he, hq⟩ := hrec c₁ hc_mem r₁ hdc₁ (by omega)
          simp only [maxScan, eval_bind, countQueries_bind, he, BTree.max?_node_singleton]
          cases BTree.max? c₁ <;> simp only [eval_pure, countQueries_pure] <;>
            exact ⟨rfl, by omega⟩
        | cons e₂' rest'' => exact (denotesRest_nil_cons s e₂' rest'' hdr').elim
      | cons e₂ rs'' =>
        cases rest' with
        | nil => exact (denotesRest_cons_nil s e₂ rs'' hdr').elim
        | cons e₂' rest'' =>
          obtain ⟨k₂', v₂', c₂⟩ := e₂'
          have hhn := BTree.height_node_le_height_node_cons
            (first := first) (k := k₁) (v := v₁) (c := c₁) (rest := (k₂', v₂', c₂) :: rest'')
          obtain ⟨he, hq⟩ := ih hdc₁ hdr'
            (fun ch hch => hrec ch (BTree.children_node_subset_children_node_cons hch))
            (by omega)
          simp only [maxScan]
          rw [BTree.max?_node_cons_cons]
          exact ⟨he, by omega⟩

private theorem maxR_spec {s : Store α β H} {fuel : ℕ} {root : Option H} {tr : BTree α β}
    (hd : Denotes s root tr) (hf : tr.height ≤ fuel) :
    eval s (maxR fuel root) = BTree.max? tr ∧ countQueries s (maxR fuel root) ≤ tr.height := by
  induction tr generalizing fuel root with
  | leaf =>
    cases root with
    | none => cases fuel <;> simp [maxR]
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
            eval s (maxR fuel r) = BTree.max? c ∧ countQueries s (maxR fuel r) ≤ c.height := by
          intro c hc r hdc hcf
          simp only [BTree.children_node, List.mem_cons, List.mem_map] at hc
          rcases hc with rfl | ⟨e, he, rfl⟩
          · exact ih₁ hdc hcf
          · exact ih₂ e he hdc hcf
        simp only [maxR, eval_bind, eval_readNode, countQueries_bind, countQueries_readNode]
        exact maxScan_spec hdf hdr hchildren hf

/-- `maxR` evaluates to `BTree.max?` whenever `root` denotes `tr` and `tr.height ≤ fuel`. -/
theorem eval_maxR {s : Store α β H} {fuel : ℕ} {root : Option H} {tr : BTree α β}
    (hd : Denotes s root tr) (hf : tr.height ≤ fuel) :
    eval s (maxR fuel root) = BTree.max? tr :=
  (maxR_spec hd hf).1

/-- `maxR` reads at most `tr.height` pages when `root` denotes `tr` and `tr.height ≤ fuel`. -/
theorem countQueries_maxR_le {s : Store α β H} {fuel : ℕ} {root : Option H} {tr : BTree α β}
    (hd : Denotes s root tr) (hf : tr.height ≤ fuel) :
    countQueries s (maxR fuel root) ≤ tr.height :=
  (maxR_spec hd hf).2

end Extremal

section OrderedQueries

variable {α β H : Type} [LinearOrder α]

/-- Within-page scan for `lookupR`: scans keys in memory and either returns on equality or
recurses into the single selected child handle. -/
@[expose] def lookupScan (rec : Option H → NodeM α β H (Option β)) (k : α) :
    Option H → List (PageEntry α β H) → NodeM α β H (Option β)
  | first, [] => rec first
  | first, ⟨k', v, c⟩ :: rs =>
    if k ≤ k' then
      if k' ≤ k then pure (some v) else rec first
    else
      lookupScan rec k c rs

/-- External-memory lookup query: reads at most one page per level along the search path. -/
@[expose] def lookupR : ℕ → α → Option H → NodeM α β H (Option β)
  | 0, _, _ => pure none
  | _ + 1, _, none => pure none
  | fuel + 1, k, some h => do
    let page ← readNode h
    lookupScan (lookupR fuel k) k page.first page.rest

/-- External-memory membership test, derived from `lookupR` at the same page-read cost. -/
@[expose] def containsR (fuel : ℕ) (k : α) (root : Option H) : NodeM α β H Bool :=
  Option.isSome <$> lookupR fuel k root

/-- Within-page scan for `predR`: scans keys in memory, retaining smaller separators as fallbacks,
and recurses into at most one child handle. -/
@[expose] def predScan (rec : Option H → NodeM α β H (Option (α × β))) (k : α) :
    Option H → List (PageEntry α β H) → NodeM α β H (Option (α × β))
  | first, [] => rec first
  | first, ⟨k', v, c⟩ :: rs =>
    if k ≤ k' then
      rec first
    else
      (fun res => res.or (some (k', v))) <$> predScan rec k c rs

/-- External-memory strict predecessor query. -/
@[expose] def predR : ℕ → α → Option H → NodeM α β H (Option (α × β))
  | 0, _, _ => pure none
  | _ + 1, _, none => pure none
  | fuel + 1, k, some h => do
    let page ← readNode h
    predScan (predR fuel k) k page.first page.rest

/-- Within-page scan for `succR`: skips keys `≤ k` in memory and recurses into the child before
the first larger separator (or the rightmost child). -/
@[expose] def succScan (rec : Option H → NodeM α β H (Option (α × β))) (k : α) :
    Option H → List (PageEntry α β H) → NodeM α β H (Option (α × β))
  | first, [] => rec first
  | first, ⟨k', v, c⟩ :: rs =>
    if k' ≤ k then
      succScan rec k c rs
    else
      (fun res => res.or (some (k', v))) <$> rec first

/-- External-memory strict successor query. -/
@[expose] def succR : ℕ → α → Option H → NodeM α β H (Option (α × β))
  | 0, _, _ => pure none
  | _ + 1, _, none => pure none
  | fuel + 1, k, some h => do
    let page ← readNode h
    succScan (succR fuel k) k page.first page.rest

/-- Within-page scan for `rankR` in an order-statistic page: accumulates stored child sizes of
skipped children in memory without reading those children's pages. -/
@[expose] def rankScan (rec : Option H → RankedNodeM α β H ℕ) (k : α) :
    RankedChild H → List (RankedPageEntry α β H) → RankedNodeM α β H ℕ
  | ⟨first, _⟩, [] => rec first
  | ⟨first, firstSz⟩, ⟨k', _, rc⟩ :: rs =>
    if k ≤ k' then
      rec first
    else
      (fun n => firstSz + 1 + n) <$> rankScan rec k rc rs

/-- External-memory strict rank query over `rankedNodeQuery`. -/
@[expose] def rankR : ℕ → α → Option H → RankedNodeM α β H ℕ
  | 0, _, _ => pure 0
  | _ + 1, _, none => pure 0
  | fuel + 1, k, some h => do
    let page ← readRankedNode h
    rankScan (rankR fuel k) k page.first page.rest

/-! ### Universal `≤ fuel` bounds -/

private theorem countQueries_lookupScan_le (s : Store α β H)
    (rec : Option H → NodeM α β H (Option β)) (k : α) {B : ℕ}
    (hrec : ∀ r, countQueries s (rec r) ≤ B) (first : Option H)
    (rs : List (PageEntry α β H)) :
    countQueries s (lookupScan rec k first rs) ≤ B := by
  induction rs generalizing first with
  | nil => exact hrec first
  | cons e rs ih =>
    obtain ⟨k', v, c⟩ := e
    simp only [lookupScan]
    split_ifs
    · simp only [countQueries_pure]
      omega
    · exact hrec first
    · exact ih c

theorem countQueries_lookupR_le_fuel (s : Store α β H) (fuel : ℕ) (k : α) (root : Option H) :
    countQueries s (lookupR fuel k root) ≤ fuel := by
  induction fuel generalizing root with
  | zero => simp [lookupR]
  | succ fuel ih =>
    cases root with
    | none => simp [lookupR]
    | some h =>
      simp only [lookupR, countQueries_bind, countQueries_readNode, eval_readNode]
      have hscan := countQueries_lookupScan_le s (lookupR fuel k) k ih (s h).first (s h).rest
      omega

theorem countQueries_containsR_le_fuel (s : Store α β H) (fuel : ℕ) (k : α) (root : Option H) :
    countQueries s (containsR fuel k root) ≤ fuel := by
  simpa only [containsR, countQueries_map] using countQueries_lookupR_le_fuel s fuel k root

private theorem countQueries_predScan_le (s : Store α β H)
    (rec : Option H → NodeM α β H (Option (α × β))) (k : α) {B : ℕ}
    (hrec : ∀ r, countQueries s (rec r) ≤ B) (first : Option H)
    (rs : List (PageEntry α β H)) :
    countQueries s (predScan rec k first rs) ≤ B := by
  induction rs generalizing first with
  | nil => exact hrec first
  | cons e rs ih =>
    obtain ⟨k', v, c⟩ := e
    simp only [predScan]
    split_ifs
    · exact hrec first
    · simpa only [countQueries_map] using ih c

theorem countQueries_predR_le_fuel (s : Store α β H) (fuel : ℕ) (k : α) (root : Option H) :
    countQueries s (predR fuel k root) ≤ fuel := by
  induction fuel generalizing root with
  | zero => simp [predR]
  | succ fuel ih =>
    cases root with
    | none => simp [predR]
    | some h =>
      simp only [predR, countQueries_bind, countQueries_readNode, eval_readNode]
      have hscan := countQueries_predScan_le s (predR fuel k) k ih (s h).first (s h).rest
      omega

private theorem countQueries_succScan_le (s : Store α β H)
    (rec : Option H → NodeM α β H (Option (α × β))) (k : α) {B : ℕ}
    (hrec : ∀ r, countQueries s (rec r) ≤ B) (first : Option H)
    (rs : List (PageEntry α β H)) :
    countQueries s (succScan rec k first rs) ≤ B := by
  induction rs generalizing first with
  | nil => exact hrec first
  | cons e rs ih =>
    obtain ⟨k', v, c⟩ := e
    simp only [succScan]
    split_ifs
    · exact ih c
    · simpa only [countQueries_map] using hrec first

theorem countQueries_succR_le_fuel (s : Store α β H) (fuel : ℕ) (k : α) (root : Option H) :
    countQueries s (succR fuel k root) ≤ fuel := by
  induction fuel generalizing root with
  | zero => simp [succR]
  | succ fuel ih =>
    cases root with
    | none => simp [succR]
    | some h =>
      simp only [succR, countQueries_bind, countQueries_readNode, eval_readNode]
      have hscan := countQueries_succScan_le s (succR fuel k) k ih (s h).first (s h).rest
      omega

private theorem countQueries_rankScan_le (s : RankedStore α β H)
    (rec : Option H → RankedNodeM α β H ℕ) (k : α) {B : ℕ}
    (hrec : ∀ r, countQueries s (rec r) ≤ B) (fc : RankedChild H)
    (rs : List (RankedPageEntry α β H)) :
    countQueries s (rankScan rec k fc rs) ≤ B := by
  induction rs generalizing fc with
  | nil => exact hrec fc.ref
  | cons e rs ih =>
    obtain ⟨k', v, rc⟩ := e
    obtain ⟨first, firstSz⟩ := fc
    simp only [rankScan]
    split_ifs
    · exact hrec first
    · simpa only [countQueries_map] using ih rc

theorem countQueries_rankR_le_fuel (s : RankedStore α β H) (fuel : ℕ) (k : α) (root : Option H) :
    countQueries s (rankR fuel k root) ≤ fuel := by
  induction fuel generalizing root with
  | zero => simp [rankR]
  | succ fuel ih =>
    cases root with
    | none => simp [rankR]
    | some h =>
      simp only [rankR, countQueries_bind, countQueries_readRankedNode, eval_readRankedNode]
      have hscan := countQueries_rankScan_le s (rankR fuel k) k ih (s h).first (s h).rest
      omega

/-! ### Exact pure-model agreement and `≤ tr.height` page-read bounds -/

private theorem lookupScan_spec {s : Store α β H} {fuel : ℕ} {k : α}
    {r₀ : Option H} {first : BTree α β}
    {rs : List (PageEntry α β H)} {rest : List (BTree.Triple α β)}
    (hdf : Denotes s r₀ first) (hdr : DenotesRest s rs rest)
    (hrec : ∀ c ∈ (BTree.node first rest).children, ∀ r, Denotes s r c → c.height ≤ fuel →
      eval s (lookupR fuel k r) = BTree.lookup k c ∧ countQueries s (lookupR fuel k r) ≤ c.height)
    (hf : (BTree.node first rest).height ≤ fuel + 1) :
    eval s (lookupScan (lookupR fuel k) k r₀ rs) = BTree.lookup k (.node first rest) ∧
      1 + countQueries s (lookupScan (lookupR fuel k) k r₀ rs) ≤
        (BTree.node first rest).height := by
  induction rs generalizing r₀ first rest with
  | nil =>
    cases rest with
    | nil =>
      have hle := BTree.height_first_succ_le (first := first) (rest := [])
      obtain ⟨he, hq⟩ := hrec first List.mem_cons_self r₀ hdf (by omega)
      simp only [lookupScan, BTree.lookup_node_nil]
      exact ⟨he, by omega⟩
    | cons e rest => exact (denotesRest_nil_cons s e rest hdr).elim
  | cons e rs ih =>
    obtain ⟨k', v, r₁⟩ := e
    cases rest with
    | nil => exact (denotesRest_cons_nil s ⟨k', v, r₁⟩ rs hdr).elim
    | cons e' rest' =>
      obtain ⟨k'', v', c⟩ := e'
      obtain ⟨rfl, rfl, hdc, hdr'⟩ :=
        (denotesRest_cons_cons_iff s k' k'' v v' r₁ c rs rest').mp hdr
      have hle₁ := BTree.height_first_succ_le (first := first) (rest := (k', v, c) :: rest')
      have hle₂ := BTree.height_node_le_height_node_cons
        (first := first) (k := k') (v := v) (c := c) (rest := rest')
      simp only [lookupScan, BTree.lookup_node_cons]
      by_cases hk₁ : k ≤ k'
      · by_cases hk₂ : k' ≤ k
        · refine ⟨?_, ?_⟩
          · simp only [hk₁, hk₂, ↓reduceIte, eval_pure]
          · simp only [hk₁, hk₂, ↓reduceIte, countQueries_pure]
            omega
        · obtain ⟨he, hq⟩ := hrec first List.mem_cons_self r₀ hdf (by omega)
          simp only [hk₁, hk₂, ↓reduceIte]
          exact ⟨he, by omega⟩
      · obtain ⟨he, hq⟩ := ih hdc hdr'
          (fun ch hch => hrec ch (BTree.children_node_subset_children_node_cons hch))
          (by omega)
        simp only [hk₁, ↓reduceIte]
        exact ⟨he, by omega⟩

private theorem lookupR_spec {s : Store α β H} {fuel : ℕ} {k : α} {root : Option H}
    {tr : BTree α β} (hd : Denotes s root tr) (hf : tr.height ≤ fuel) :
    eval s (lookupR fuel k root) = BTree.lookup k tr ∧
      countQueries s (lookupR fuel k root) ≤ tr.height := by
  induction tr generalizing fuel root with
  | leaf =>
    cases root with
    | none =>
      have hl : BTree.lookup k (.leaf : BTree α β) = none := by
        simp [BTree.lookup_def, BTree.lookupM]
      cases fuel <;> simp [lookupR, hl]
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
            eval s (lookupR fuel k r) = BTree.lookup k c ∧
              countQueries s (lookupR fuel k r) ≤ c.height := by
          intro c hc r hdc hcf
          simp only [BTree.children_node, List.mem_cons, List.mem_map] at hc
          rcases hc with rfl | ⟨e, he, rfl⟩
          · exact ih₁ hdc hcf
          · exact ih₂ e he hdc hcf
        simp only [lookupR, eval_bind, eval_readNode, countQueries_bind, countQueries_readNode]
        exact lookupScan_spec hdf hdr hchildren hf

/-- `lookupR` evaluates to `BTree.lookup` whenever `root` denotes `tr` and `tr.height ≤ fuel`. -/
theorem eval_lookupR {s : Store α β H} {fuel : ℕ} {root : Option H} {tr : BTree α β}
    (hd : Denotes s root tr) (hf : tr.height ≤ fuel) (k : α) :
    eval s (lookupR fuel k root) = BTree.lookup k tr :=
  (lookupR_spec hd hf).1

/-- `lookupR` reads at most `tr.height` pages when `root` denotes `tr` and `tr.height ≤ fuel`. -/
theorem countQueries_lookupR_le {s : Store α β H} {fuel : ℕ} {root : Option H} {tr : BTree α β}
    (hd : Denotes s root tr) (hf : tr.height ≤ fuel) (k : α) :
    countQueries s (lookupR fuel k root) ≤ tr.height :=
  (lookupR_spec hd hf).2

/-- `containsR` evaluates to `BTree.contains` when `root` denotes `tr` and `tr.height ≤ fuel`. -/
theorem eval_containsR {s : Store α β H} {fuel : ℕ} {root : Option H} {tr : BTree α β}
    (hd : Denotes s root tr) (hf : tr.height ≤ fuel) (k : α) :
    eval s (containsR fuel k root) = BTree.contains k tr := by
  simp only [containsR, eval_map, eval_lookupR hd hf k, BTree.contains_eq_isSome_lookup]

/-- `containsR` reads at most `tr.height` pages when `root` denotes `tr` and `tr.height ≤ fuel`. -/
theorem countQueries_containsR_le {s : Store α β H} {fuel : ℕ} {root : Option H} {tr : BTree α β}
    (hd : Denotes s root tr) (hf : tr.height ≤ fuel) (k : α) :
    countQueries s (containsR fuel k root) ≤ tr.height := by
  simpa only [containsR, countQueries_map] using countQueries_lookupR_le hd hf k

private theorem predScan_spec {s : Store α β H} {fuel : ℕ} {k : α}
    {r₀ : Option H} {first : BTree α β}
    {rs : List (PageEntry α β H)} {rest : List (BTree.Triple α β)}
    (hdf : Denotes s r₀ first) (hdr : DenotesRest s rs rest)
    (hrec : ∀ c ∈ (BTree.node first rest).children, ∀ r, Denotes s r c → c.height ≤ fuel →
      eval s (predR fuel k r) = BTree.pred? k c ∧ countQueries s (predR fuel k r) ≤ c.height)
    (hf : (BTree.node first rest).height ≤ fuel + 1) :
    eval s (predScan (predR fuel k) k r₀ rs) = BTree.pred? k (.node first rest) ∧
      1 + countQueries s (predScan (predR fuel k) k r₀ rs) ≤
        (BTree.node first rest).height := by
  induction rs generalizing r₀ first rest with
  | nil =>
    cases rest with
    | nil =>
      have hle := BTree.height_first_succ_le (first := first) (rest := [])
      obtain ⟨he, hq⟩ := hrec first List.mem_cons_self r₀ hdf (by omega)
      simp only [predScan, BTree.pred?_node_nil]
      exact ⟨he, by omega⟩
    | cons e rest => exact (denotesRest_nil_cons s e rest hdr).elim
  | cons e rs ih =>
    obtain ⟨k', v, r₁⟩ := e
    cases rest with
    | nil => exact (denotesRest_cons_nil s ⟨k', v, r₁⟩ rs hdr).elim
    | cons e' rest' =>
      obtain ⟨k'', v', c⟩ := e'
      obtain ⟨rfl, rfl, hdc, hdr'⟩ :=
        (denotesRest_cons_cons_iff s k' k'' v v' r₁ c rs rest').mp hdr
      have hle₁ := BTree.height_first_succ_le (first := first) (rest := (k', v, c) :: rest')
      have hle₂ := BTree.height_node_le_height_node_cons
        (first := first) (k := k') (v := v) (c := c) (rest := rest')
      simp only [predScan, BTree.pred?_node_cons]
      by_cases hk : k ≤ k'
      · obtain ⟨he, hq⟩ := hrec first List.mem_cons_self r₀ hdf (by omega)
        simp only [hk, ↓reduceIte]
        exact ⟨he, by omega⟩
      · obtain ⟨he, hq⟩ := ih hdc hdr'
          (fun ch hch => hrec ch (BTree.children_node_subset_children_node_cons hch))
          (by omega)
        refine ⟨?_, ?_⟩
        · simp only [hk, ↓reduceIte, eval_map, he]
        · simp only [hk, ↓reduceIte, countQueries_map]
          omega

private theorem predR_spec {s : Store α β H} {fuel : ℕ} {k : α} {root : Option H}
    {tr : BTree α β} (hd : Denotes s root tr) (hf : tr.height ≤ fuel) :
    eval s (predR fuel k root) = BTree.pred? k tr ∧
      countQueries s (predR fuel k root) ≤ tr.height := by
  induction tr generalizing fuel root with
  | leaf =>
    cases root with
    | none => cases fuel <;> simp [predR]
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
            eval s (predR fuel k r) = BTree.pred? k c ∧
              countQueries s (predR fuel k r) ≤ c.height := by
          intro c hc r hdc hcf
          simp only [BTree.children_node, List.mem_cons, List.mem_map] at hc
          rcases hc with rfl | ⟨e, he, rfl⟩
          · exact ih₁ hdc hcf
          · exact ih₂ e he hdc hcf
        simp only [predR, eval_bind, eval_readNode, countQueries_bind, countQueries_readNode]
        exact predScan_spec hdf hdr hchildren hf

/-- `predR` evaluates to `BTree.pred?` whenever `root` denotes `tr` and `tr.height ≤ fuel`. -/
theorem eval_predR {s : Store α β H} {fuel : ℕ} {root : Option H} {tr : BTree α β}
    (hd : Denotes s root tr) (hf : tr.height ≤ fuel) (k : α) :
    eval s (predR fuel k root) = BTree.pred? k tr :=
  (predR_spec hd hf).1

/-- `predR` reads at most `tr.height` pages when `root` denotes `tr` and `tr.height ≤ fuel`. -/
theorem countQueries_predR_le {s : Store α β H} {fuel : ℕ} {root : Option H} {tr : BTree α β}
    (hd : Denotes s root tr) (hf : tr.height ≤ fuel) (k : α) :
    countQueries s (predR fuel k root) ≤ tr.height :=
  (predR_spec hd hf).2

private theorem succScan_spec {s : Store α β H} {fuel : ℕ} {k : α}
    {r₀ : Option H} {first : BTree α β}
    {rs : List (PageEntry α β H)} {rest : List (BTree.Triple α β)}
    (hdf : Denotes s r₀ first) (hdr : DenotesRest s rs rest)
    (hrec : ∀ c ∈ (BTree.node first rest).children, ∀ r, Denotes s r c → c.height ≤ fuel →
      eval s (succR fuel k r) = BTree.succ? k c ∧ countQueries s (succR fuel k r) ≤ c.height)
    (hf : (BTree.node first rest).height ≤ fuel + 1) :
    eval s (succScan (succR fuel k) k r₀ rs) = BTree.succ? k (.node first rest) ∧
      1 + countQueries s (succScan (succR fuel k) k r₀ rs) ≤
        (BTree.node first rest).height := by
  induction rs generalizing r₀ first rest with
  | nil =>
    cases rest with
    | nil =>
      have hle := BTree.height_first_succ_le (first := first) (rest := [])
      obtain ⟨he, hq⟩ := hrec first List.mem_cons_self r₀ hdf (by omega)
      simp only [succScan, BTree.succ?_node_nil]
      exact ⟨he, by omega⟩
    | cons e rest => exact (denotesRest_nil_cons s e rest hdr).elim
  | cons e rs ih =>
    obtain ⟨k', v, r₁⟩ := e
    cases rest with
    | nil => exact (denotesRest_cons_nil s ⟨k', v, r₁⟩ rs hdr).elim
    | cons e' rest' =>
      obtain ⟨k'', v', c⟩ := e'
      obtain ⟨rfl, rfl, hdc, hdr'⟩ :=
        (denotesRest_cons_cons_iff s k' k'' v v' r₁ c rs rest').mp hdr
      have hle₁ := BTree.height_first_succ_le (first := first) (rest := (k', v, c) :: rest')
      have hle₂ := BTree.height_node_le_height_node_cons
        (first := first) (k := k') (v := v) (c := c) (rest := rest')
      simp only [succScan, BTree.succ?_node_cons]
      by_cases hk : k' ≤ k
      · obtain ⟨he, hq⟩ := ih hdc hdr'
          (fun ch hch => hrec ch (BTree.children_node_subset_children_node_cons hch))
          (by omega)
        simp only [hk, ↓reduceIte]
        exact ⟨he, by omega⟩
      · obtain ⟨he, hq⟩ := hrec first List.mem_cons_self r₀ hdf (by omega)
        refine ⟨?_, ?_⟩
        · simp only [hk, ↓reduceIte, eval_map, he]
        · simp only [hk, ↓reduceIte, countQueries_map]
          omega

private theorem succR_spec {s : Store α β H} {fuel : ℕ} {k : α} {root : Option H}
    {tr : BTree α β} (hd : Denotes s root tr) (hf : tr.height ≤ fuel) :
    eval s (succR fuel k root) = BTree.succ? k tr ∧
      countQueries s (succR fuel k root) ≤ tr.height := by
  induction tr generalizing fuel root with
  | leaf =>
    cases root with
    | none => cases fuel <;> simp [succR]
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
            eval s (succR fuel k r) = BTree.succ? k c ∧
              countQueries s (succR fuel k r) ≤ c.height := by
          intro c hc r hdc hcf
          simp only [BTree.children_node, List.mem_cons, List.mem_map] at hc
          rcases hc with rfl | ⟨e, he, rfl⟩
          · exact ih₁ hdc hcf
          · exact ih₂ e he hdc hcf
        simp only [succR, eval_bind, eval_readNode, countQueries_bind, countQueries_readNode]
        exact succScan_spec hdf hdr hchildren hf

/-- `succR` evaluates to `BTree.succ?` whenever `root` denotes `tr` and `tr.height ≤ fuel`. -/
theorem eval_succR {s : Store α β H} {fuel : ℕ} {root : Option H} {tr : BTree α β}
    (hd : Denotes s root tr) (hf : tr.height ≤ fuel) (k : α) :
    eval s (succR fuel k root) = BTree.succ? k tr :=
  (succR_spec hd hf).1

/-- `succR` reads at most `tr.height` pages when `root` denotes `tr` and `tr.height ≤ fuel`. -/
theorem countQueries_succR_le {s : Store α β H} {fuel : ℕ} {root : Option H} {tr : BTree α β}
    (hd : Denotes s root tr) (hf : tr.height ≤ fuel) (k : α) :
    countQueries s (succR fuel k root) ≤ tr.height :=
  (succR_spec hd hf).2

private theorem rankScan_spec {s : RankedStore α β H} {fuel : ℕ} {k : α}
    {fc : RankedChild H} {first : BTree α β}
    {rs : List (RankedPageEntry α β H)} {rest : List (BTree.Triple α β)}
    (hdf : DenotesRanked s fc.ref first) (hszf : fc.subSize = first.size)
    (hdr : DenotesRankedRest s rs rest)
    (hrec : ∀ c ∈ (BTree.node first rest).children, ∀ r, DenotesRanked s r c → c.height ≤ fuel →
      eval s (rankR fuel k r) = BTree.rank k c ∧ countQueries s (rankR fuel k r) ≤ c.height)
    (hf : (BTree.node first rest).height ≤ fuel + 1) :
    eval s (rankScan (rankR fuel k) k fc rs) = BTree.rank k (.node first rest) ∧
      1 + countQueries s (rankScan (rankR fuel k) k fc rs) ≤
        (BTree.node first rest).height := by
  induction rs generalizing fc first rest with
  | nil =>
    cases rest with
    | nil =>
      obtain ⟨r₀, sz₀⟩ := fc
      have hle := BTree.height_first_succ_le (first := first) (rest := [])
      obtain ⟨he, hq⟩ := hrec first List.mem_cons_self r₀ hdf (by omega)
      simp only [rankScan, BTree.rank_node_nil]
      exact ⟨he, by omega⟩
    | cons e rest => exact (denotesRankedRest_nil_cons s e rest hdr).elim
  | cons e rs ih =>
    obtain ⟨k', v, rc⟩ := e
    obtain ⟨r₀, sz₀⟩ := fc
    cases hszf
    cases rest with
    | nil => exact (denotesRankedRest_cons_nil s ⟨k', v, rc⟩ rs hdr).elim
    | cons e' rest' =>
      obtain ⟨k'', v', c⟩ := e'
      obtain ⟨rfl, rfl, hdc, hszc, hdr'⟩ :=
        (denotesRankedRest_cons_cons_iff s k' k'' v v' rc c rs rest').mp hdr
      have hle₁ := BTree.height_first_succ_le (first := first) (rest := (k', v, c) :: rest')
      have hle₂ := BTree.height_node_le_height_node_cons
        (first := first) (k := k') (v := v) (c := c) (rest := rest')
      simp only [rankScan, BTree.rank_node_cons]
      by_cases hk : k ≤ k'
      · obtain ⟨he, hq⟩ := hrec first List.mem_cons_self r₀ hdf (by omega)
        simp only [hk, ↓reduceIte]
        exact ⟨he, by omega⟩
      · obtain ⟨he, hq⟩ := ih hdc hszc hdr'
          (fun ch hch => hrec ch (BTree.children_node_subset_children_node_cons hch))
          (by omega)
        refine ⟨?_, ?_⟩
        · simp only [hk, ↓reduceIte, eval_map, he]
          rfl
        · simp only [hk, ↓reduceIte, countQueries_map]
          omega

private theorem rankR_spec {s : RankedStore α β H} {fuel : ℕ} {k : α} {root : Option H}
    {tr : BTree α β} (hd : DenotesRanked s root tr) (hf : tr.height ≤ fuel) :
    eval s (rankR fuel k root) = BTree.rank k tr ∧
      countQueries s (rankR fuel k root) ≤ tr.height := by
  induction tr generalizing fuel root with
  | leaf =>
    cases root with
    | none => cases fuel <;> simp [rankR]
    | some h => exact (denotesRanked_some_leaf s h hd).elim
  | node first rest ih₁ ih₂ =>
    cases root with
    | none => exact (denotesRanked_none_node s first rest hd).elim
    | some h =>
      have hle := BTree.height_first_succ_le (first := first) (rest := rest)
      cases fuel with
      | zero => omega
      | succ fuel =>
        obtain ⟨hdf, hszf, hdr⟩ := (denotesRanked_some_node_iff s h first rest).mp hd
        have hchildren : ∀ c ∈ (BTree.node first rest).children, ∀ r,
            DenotesRanked s r c → c.height ≤ fuel →
            eval s (rankR fuel k r) = BTree.rank k c ∧
              countQueries s (rankR fuel k r) ≤ c.height := by
          intro c hc r hdc hcf
          simp only [BTree.children_node, List.mem_cons, List.mem_map] at hc
          rcases hc with rfl | ⟨e, he, rfl⟩
          · exact ih₁ hdc hcf
          · exact ih₂ e he hdc hcf
        simp only [rankR, eval_bind, eval_readRankedNode, countQueries_bind,
          countQueries_readRankedNode]
        exact rankScan_spec hdf hszf hdr hchildren hf

/-- `rankR` evaluates to `BTree.rank` whenever `root` denotes `tr` in `RankedStore` `s` and
`tr.height ≤ fuel`. -/
theorem eval_rankR {s : RankedStore α β H} {fuel : ℕ} {root : Option H} {tr : BTree α β}
    (hd : DenotesRanked s root tr) (hf : tr.height ≤ fuel) (k : α) :
    eval s (rankR fuel k root) = BTree.rank k tr :=
  (rankR_spec hd hf).1

/-- `rankR` reads at most `tr.height` pages when `root` denotes `tr` and `tr.height ≤ fuel`. -/
theorem countQueries_rankR_le {s : RankedStore α β H} {fuel : ℕ} {root : Option H} {tr : BTree α β}
    (hd : DenotesRanked s root tr) (hf : tr.height ≤ fuel) (k : α) :
    countQueries s (rankR fuel k root) ≤ tr.height :=
  (rankR_spec hd hf).2

/-! ### Logarithmic `O(log_t n)` page-read corollaries on well-formed B-trees -/

theorem countQueries_minR_le_log {t fuel : ℕ} {s : Store α β H} {root : Option H}
    {tr : BTree α β} (hwf : BTree.IsWF t tr) (hd : Denotes s root tr) (hf : tr.height ≤ fuel) :
    countQueries s (minR fuel root) ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  (countQueries_minR_le hd hf).trans hwf.height_le_log

theorem countQueries_maxR_le_log {t fuel : ℕ} {s : Store α β H} {root : Option H}
    {tr : BTree α β} (hwf : BTree.IsWF t tr) (hd : Denotes s root tr) (hf : tr.height ≤ fuel) :
    countQueries s (maxR fuel root) ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  (countQueries_maxR_le hd hf).trans hwf.height_le_log

theorem countQueries_lookupR_le_log {t fuel : ℕ} {s : Store α β H} {root : Option H}
    {tr : BTree α β} (hwf : BTree.IsWF t tr) (hd : Denotes s root tr) (hf : tr.height ≤ fuel)
    (k : α) :
    countQueries s (lookupR fuel k root) ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  (countQueries_lookupR_le hd hf k).trans hwf.height_le_log

theorem countQueries_containsR_le_log {t fuel : ℕ} {s : Store α β H} {root : Option H}
    {tr : BTree α β} (hwf : BTree.IsWF t tr) (hd : Denotes s root tr) (hf : tr.height ≤ fuel)
    (k : α) :
    countQueries s (containsR fuel k root) ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  (countQueries_containsR_le hd hf k).trans hwf.height_le_log

theorem countQueries_predR_le_log {t fuel : ℕ} {s : Store α β H} {root : Option H}
    {tr : BTree α β} (hwf : BTree.IsWF t tr) (hd : Denotes s root tr) (hf : tr.height ≤ fuel)
    (k : α) :
    countQueries s (predR fuel k root) ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  (countQueries_predR_le hd hf k).trans hwf.height_le_log

theorem countQueries_succR_le_log {t fuel : ℕ} {s : Store α β H} {root : Option H}
    {tr : BTree α β} (hwf : BTree.IsWF t tr) (hd : Denotes s root tr) (hf : tr.height ≤ fuel)
    (k : α) :
    countQueries s (succR fuel k root) ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  (countQueries_succR_le hd hf k).trans hwf.height_le_log

theorem countQueries_rankR_le_log {t fuel : ℕ} {s : RankedStore α β H} {root : Option H}
    {tr : BTree α β} (hwf : BTree.IsWF t tr) (hd : DenotesRanked s root tr)
    (hf : tr.height ≤ fuel) (k : α) :
    countQueries s (rankR fuel k root) ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  (countQueries_rankR_le hd hf k).trans hwf.height_le_log

end OrderedQueries

end Cslib.DataStructure.BTree.NodeAccess
