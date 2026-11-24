/-
Copyright (c) 2026 Jesse Alama, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BTree.Basic
public import CslibFrontier.Foundations.Data.PFunctor.Free.Eval

/-!
# External-memory node-access oracle model for classic B-trees

Read-only classic B-tree queries in an external-memory / page-read oracle model built on
`PFunctor.FreeM`. A tree is never passed as an inductive `BTree α β` value to a query program:
instead, a reference is `Option H` over an abstract handle type `H`, where `none` represents an
empty leaf without issuing a page read and `some h` can be inspected only by issuing a `readNode h`
query against a stateless `Store α β H` oracle.

Counting is structural via `PFunctor.FreeM.countQueries`: no program parametric in `H` can inspect
a node's keys or child handles without paying `1` query per node read. For order-statistic `rankR`
queries, which skip subtrees in `O(height)` page reads without reading skipped child pages,
`RankedNodeView` augments each child reference in a page with its subtree entry count
(`RankedStore`, `DenotesRanked`), paired with a forgetful projection `RankedStore.toStore` to the
unaugmented store.

## Main definitions

* `NodeAccess.PageEntry`, `NodeAccess.NodeView`, `NodeAccess.nodeQuery`, `NodeAccess.NodeM`,
  `NodeAccess.Store`, `NodeAccess.readNode`: unaugmented B-tree page entry, page view, polynomial
  query functor, program monad, store oracle, and single-page read operation.
* `NodeAccess.Denotes`, `NodeAccess.DenotesRest`: coupling relation asserting that an `Option H`
  reference in a `Store` represents a pure `BTree α β`.
* `NodeAccess.toRef`, `NodeAccess.canonicalStore`: canonical handle realization witnessing that
  every `BTree α β` admits a faithful `Store`.
* `NodeAccess.RankedChild`, `NodeAccess.RankedPageEntry`, `NodeAccess.RankedNodeView`,
  `NodeAccess.rankedNodeQuery`, `NodeAccess.RankedNodeM`, `NodeAccess.RankedStore`,
  `NodeAccess.readRankedNode`, `NodeAccess.DenotesRanked`, `NodeAccess.DenotesRankedRest`,
  `NodeAccess.canonicalRankedStore`: subtree-size-augmented page model for `O(height)`
  external-memory rank queries.

## Main results

* `NodeAccess.eval_readNode`, `NodeAccess.countQueries_readNode`,
  `NodeAccess.eval_readRankedNode`, `NodeAccess.countQueries_readRankedNode`: single-page read
  evaluation and unit query cost.
* `NodeAccess.denotes_canonicalStore`, `NodeAccess.denotesRanked_canonicalRankedStore`: every
  `BTree α β` is denoted by its canonical handle reference.
* `NodeAccess.DenotesRanked.toDenotes`: forgetting child-size annotations preserves `Denotes`.

## References

* [R. Bayer and E. McCreight, *Organization and Maintenance of Large Ordered
  Indexes*][BayerMcCreight1972]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 18][CLRS2009]
-/

public section

namespace Cslib.DataStructure.BTree.NodeAccess

open PFunctor.FreeM

section Unaugmented

variable {α β H : Type}

/-- Entry in an unaugmented B-tree node page: separator `key`, associated `val`, and following
`child` reference (`none` for an empty leaf). -/
structure PageEntry (α β H : Type) where
  /-- Separator key. -/
  key : α
  /-- Associated value. -/
  val : β
  /-- Handle reference to the child subtree following `key`. -/
  child : Option H
  deriving DecidableEq, Repr

/-- Contents of one B-tree node page: the `first` child reference followed by `rest` page entries,
where `none` represents an empty leaf. -/
structure NodeView (α β H : Type) where
  /-- Handle reference to the subtree preceding all separator keys. -/
  first : Option H
  /-- Ordered `(key, val, child)` entries of the node page. -/
  rest : List (PageEntry α β H)
  deriving DecidableEq, Repr

/-- Polynomial query signature reading one node page by its handle `h : H`. -/
abbrev nodeQuery (α β H : Type) : PFunctor.{0, 0} := ⟨H, fun _ => NodeView α β H⟩

/-- Read-only external-memory computation over `nodeQuery α β H`. -/
abbrev NodeM (α β H γ : Type) : Type := (nodeQuery α β H).FreeM γ

/-- Stateless page store mapping each handle to its `NodeView`. -/
abbrev Store (α β H : Type) : Type := H → NodeView α β H

/-- Issue one page-read query for handle `h : H`. -/
@[expose] def readNode (h : H) : NodeM α β H (NodeView α β H) :=
  PFunctor.FreeM.lift h

@[simp] theorem eval_readNode (s : Store α β H) (h : H) :
    eval s (readNode h) = s h := rfl

@[simp] theorem countQueries_readNode (s : Store α β H) (h : H) :
    countQueries s (readNode h) = 1 := rfl

mutual
/-- `Denotes s ref tr` holds when optional handle `ref` in store `s` represents `tr : BTree α β`. -/
def Denotes (s : Store α β H) : Option H → BTree α β → Prop
  | none, .leaf => True
  | none, .node _ _ => False
  | some _, .leaf => False
  | some h, .node first rest => Denotes s (s h).first first ∧ DenotesRest s (s h).rest rest
termination_by _ tr => sizeOf tr

/-- Entry-by-entry denotation of a node page's `PageEntry` list. -/
def DenotesRest (s : Store α β H) :
    List (PageEntry α β H) → List (BTree.Triple α β) → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | ⟨k, v, r⟩ :: rs, (k', v', c) :: rest =>
    k = k' ∧ v = v' ∧ Denotes s r c ∧ DenotesRest s rs rest
termination_by _ rest => sizeOf rest
end

@[simp] theorem denotes_none_leaf (s : Store α β H) : Denotes s none (.leaf : BTree α β) := by
  rw [Denotes]; trivial

@[simp] theorem denotes_none_node (s : Store α β H) (first : BTree α β)
    (rest : List (BTree.Triple α β)) :
    ¬ Denotes s none (.node first rest) := by
  rw [Denotes]; exact id

@[simp] theorem denotes_some_leaf (s : Store α β H) (h : H) :
    ¬ Denotes s (some h) (.leaf : BTree α β) := by
  rw [Denotes]; exact id

theorem denotes_some_node_iff (s : Store α β H) (h : H) (first : BTree α β)
    (rest : List (BTree.Triple α β)) :
    Denotes s (some h) (.node first rest) ↔
      Denotes s (s h).first first ∧ DenotesRest s (s h).rest rest := by
  rw [Denotes]

@[simp] theorem denotesRest_nil_nil (s : Store α β H) :
    DenotesRest s ([] : List (PageEntry α β H)) ([] : List (BTree.Triple α β)) := by
  rw [DenotesRest]; trivial

@[simp] theorem denotesRest_nil_cons (s : Store α β H) (e : BTree.Triple α β)
    (rest : List (BTree.Triple α β)) :
    ¬ DenotesRest s [] (e :: rest) := by
  cases e; rw [DenotesRest]; exact id

@[simp] theorem denotesRest_cons_nil (s : Store α β H) (e : PageEntry α β H)
    (rs : List (PageEntry α β H)) :
    ¬ DenotesRest s (e :: rs) [] := by
  obtain ⟨_, _, _⟩ := e; rw [DenotesRest]; exact id

theorem denotesRest_cons_cons_iff (s : Store α β H) (k k' : α) (v v' : β)
    (r : Option H) (c : BTree α β) (rs : List (PageEntry α β H))
    (rest : List (BTree.Triple α β)) :
    DenotesRest s (⟨k, v, r⟩ :: rs) ((k', v', c) :: rest) ↔
      k = k' ∧ v = v' ∧ Denotes s r c ∧ DenotesRest s rs rest := by
  rw [DenotesRest]

theorem Denotes.eq_leaf_of_none {s : Store α β H} {tr : BTree α β} (hd : Denotes s none tr) :
    tr = .leaf := by
  cases tr with
  | leaf => rfl
  | node _ _ => exact (denotes_none_node s _ _ hd).elim

theorem DenotesRest.length_eq {s : Store α β H} {rs : List (PageEntry α β H)}
    {rest : List (BTree.Triple α β)} (hd : DenotesRest s rs rest) :
    rs.length = rest.length := by
  induction rs generalizing rest with
  | nil =>
    cases rest with
    | nil => rfl
    | cons e rest => exact (denotesRest_nil_cons s e rest hd).elim
  | cons e rs ih =>
    obtain ⟨k, v, r⟩ := e
    cases rest with
    | nil => exact (denotesRest_cons_nil s ⟨k, v, r⟩ rs hd).elim
    | cons e' rest =>
      obtain ⟨k', v', c⟩ := e'
      obtain ⟨_, _, _, hdr⟩ := (denotesRest_cons_cons_iff s k k' v v' r c rs rest).mp hd
      simp only [List.length_cons, ih hdr]

/-- Canonical reference for a pure `BTree α β` when handles are non-leaf subtrees
(`H := BTree α β`). -/
def toRef : BTree α β → Option (BTree α β)
  | .leaf => none
  | .node first rest => some (.node first rest)

/-- Canonical page store mapping each `BTree α β` handle to its top-level children and keys. -/
def canonicalStore : Store α β (BTree α β)
  | .leaf => ⟨none, []⟩
  | .node first rest => ⟨toRef first, rest.map fun (k, v, c) => ⟨k, v, toRef c⟩⟩

private theorem denotesRest_canonicalStore (rest : List (BTree.Triple α β))
    (ih : ∀ e ∈ rest, Denotes (canonicalStore (α := α) (β := β)) (toRef e.child) e.child) :
    DenotesRest (canonicalStore (α := α) (β := β))
      (rest.map fun (k, v, c) => ⟨k, v, toRef c⟩) rest := by
  induction rest with
  | nil => exact denotesRest_nil_nil _
  | cons e rest ihr =>
    obtain ⟨k, v, c⟩ := e
    rw [List.map_cons, denotesRest_cons_cons_iff]
    exact ⟨rfl, rfl, ih (k, v, c) List.mem_cons_self,
      ihr fun e' he' => ih e' (List.mem_cons_of_mem _ he')⟩

/-- Every `BTree α β` is denoted in `canonicalStore` by `toRef tr`. -/
theorem denotes_canonicalStore (tr : BTree α β) :
    Denotes (canonicalStore (α := α) (β := β)) (toRef tr) tr := by
  induction tr with
  | leaf => exact denotes_none_leaf _
  | node first rest ih₁ ih₂ =>
    rw [toRef, denotes_some_node_iff]
    exact ⟨ih₁, denotesRest_canonicalStore rest ih₂⟩

end Unaugmented

section Ranked

variable {α β H : Type}

/-- Child reference in an order-statistic B-tree page: optional child handle `ref` paired with its
subtree entry count `subSize` (`0` at an empty leaf). -/
structure RankedChild (H : Type) where
  /-- Optional child handle (`none` for an empty leaf). -/
  ref : Option H
  /-- Number of entries in the child subtree. -/
  subSize : ℕ
  deriving DecidableEq, Repr

/-- Entry in an order-statistic B-tree node page: separator `key`, associated `val`, and following
`RankedChild` slot. -/
structure RankedPageEntry (α β H : Type) where
  /-- Separator key. -/
  key : α
  /-- Associated value. -/
  val : β
  /-- Following child reference and its subtree entry count. -/
  child : RankedChild H
  deriving DecidableEq, Repr

/-- Contents of one order-statistic B-tree node page: `first` `RankedChild` and `rest`
`RankedPageEntry` records. -/
structure RankedNodeView (α β H : Type) where
  /-- First child reference and its subtree entry count. -/
  first : RankedChild H
  /-- Ordered `(key, val, child)` entries of the order-statistic page. -/
  rest : List (RankedPageEntry α β H)
  deriving DecidableEq, Repr

/-- Polynomial query signature reading one order-statistic B-tree node page by handle `h : H`. -/
abbrev rankedNodeQuery (α β H : Type) : PFunctor.{0, 0} := ⟨H, fun _ => RankedNodeView α β H⟩

/-- Read-only external-memory computation over `rankedNodeQuery α β H`. -/
abbrev RankedNodeM (α β H γ : Type) : Type := (rankedNodeQuery α β H).FreeM γ

/-- Stateless store mapping each handle to an order-statistic `RankedNodeView`. -/
abbrev RankedStore (α β H : Type) : Type := H → RankedNodeView α β H

/-- Issue one page-read query for handle `h : H` in an order-statistic store. -/
@[expose] def readRankedNode (h : H) : RankedNodeM α β H (RankedNodeView α β H) :=
  PFunctor.FreeM.lift h

@[simp] theorem eval_readRankedNode (s : RankedStore α β H) (h : H) :
    eval s (readRankedNode h) = s h := rfl

@[simp] theorem countQueries_readRankedNode (s : RankedStore α β H) (h : H) :
    countQueries s (readRankedNode h) = 1 := rfl

/-- Forget subtree-size annotations to view a `RankedStore` as an unaugmented `Store`. -/
@[expose] def RankedStore.toStore (s : RankedStore α β H) : Store α β H :=
  fun h => ⟨(s h).first.ref, (s h).rest.map fun e => ⟨e.key, e.val, e.child.ref⟩⟩

mutual
/-- `DenotesRanked s ref tr` holds when optional handle `ref` in `RankedStore` `s` represents `tr`
with exact child subtree sizes recorded at every child slot. -/
def DenotesRanked (s : RankedStore α β H) : Option H → BTree α β → Prop
  | none, .leaf => True
  | none, .node _ _ => False
  | some _, .leaf => False
  | some h, .node first rest =>
    DenotesRanked s (s h).first.ref first ∧ (s h).first.subSize = first.size ∧
      DenotesRankedRest s (s h).rest rest
termination_by _ tr => sizeOf tr

/-- Entry-by-entry denotation of an order-statistic node page's `RankedPageEntry` list. -/
def DenotesRankedRest (s : RankedStore α β H) :
    List (RankedPageEntry α β H) → List (BTree.Triple α β) → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | ⟨k, v, rc⟩ :: rs, (k', v', c) :: rest =>
    k = k' ∧ v = v' ∧ DenotesRanked s rc.ref c ∧ rc.subSize = c.size ∧
      DenotesRankedRest s rs rest
termination_by _ rest => sizeOf rest
end

@[simp] theorem denotesRanked_none_leaf (s : RankedStore α β H) :
    DenotesRanked s none (.leaf : BTree α β) := by
  rw [DenotesRanked]; trivial

@[simp] theorem denotesRanked_none_node (s : RankedStore α β H) (first : BTree α β)
    (rest : List (BTree.Triple α β)) :
    ¬ DenotesRanked s none (.node first rest) := by
  rw [DenotesRanked]; exact id

@[simp] theorem denotesRanked_some_leaf (s : RankedStore α β H) (h : H) :
    ¬ DenotesRanked s (some h) (.leaf : BTree α β) := by
  rw [DenotesRanked]; exact id

theorem denotesRanked_some_node_iff (s : RankedStore α β H) (h : H) (first : BTree α β)
    (rest : List (BTree.Triple α β)) :
    DenotesRanked s (some h) (.node first rest) ↔
      DenotesRanked s (s h).first.ref first ∧ (s h).first.subSize = first.size ∧
        DenotesRankedRest s (s h).rest rest := by
  rw [DenotesRanked]

@[simp] theorem denotesRankedRest_nil_nil (s : RankedStore α β H) :
    DenotesRankedRest s ([] : List (RankedPageEntry α β H)) ([] : List (BTree.Triple α β)) := by
  rw [DenotesRankedRest]; trivial

@[simp] theorem denotesRankedRest_nil_cons (s : RankedStore α β H) (e : BTree.Triple α β)
    (rest : List (BTree.Triple α β)) :
    ¬ DenotesRankedRest s [] (e :: rest) := by
  cases e; rw [DenotesRankedRest]; exact id

@[simp] theorem denotesRankedRest_cons_nil (s : RankedStore α β H) (e : RankedPageEntry α β H)
    (rs : List (RankedPageEntry α β H)) :
    ¬ DenotesRankedRest s (e :: rs) [] := by
  obtain ⟨_, _, _⟩ := e; rw [DenotesRankedRest]; exact id

theorem denotesRankedRest_cons_cons_iff (s : RankedStore α β H) (k k' : α) (v v' : β)
    (rc : RankedChild H) (c : BTree α β) (rs : List (RankedPageEntry α β H))
    (rest : List (BTree.Triple α β)) :
    DenotesRankedRest s (⟨k, v, rc⟩ :: rs) ((k', v', c) :: rest) ↔
      k = k' ∧ v = v' ∧ DenotesRanked s rc.ref c ∧ rc.subSize = c.size ∧
        DenotesRankedRest s rs rest := by
  rw [DenotesRankedRest]

private theorem DenotesRankedRest.toDenotesRest {s : RankedStore α β H}
    {rs : List (RankedPageEntry α β H)} {rest : List (BTree.Triple α β)}
    (hd : DenotesRankedRest s rs rest)
    (ih : ∀ c ∈ rest.map BTree.Triple.child,
      ∀ r, DenotesRanked s r c → Denotes s.toStore r c) :
    DenotesRest s.toStore (rs.map fun e => ⟨e.key, e.val, e.child.ref⟩) rest := by
  induction rs generalizing rest with
  | nil =>
    cases rest with
    | nil => exact denotesRest_nil_nil _
    | cons e rest => exact (denotesRankedRest_nil_cons s e rest hd).elim
  | cons e rs ihr =>
    obtain ⟨k, v, rc⟩ := e
    cases rest with
    | nil => exact (denotesRankedRest_cons_nil s ⟨k, v, rc⟩ rs hd).elim
    | cons e' rest =>
      obtain ⟨k', v', c⟩ := e'
      obtain ⟨rfl, rfl, hdc, _, hdr⟩ :=
        (denotesRankedRest_cons_cons_iff s k k' v v' rc c rs rest).mp hd
      rw [List.map_cons, denotesRest_cons_cons_iff]
      exact ⟨rfl, rfl, ih c (List.mem_cons_self ..) rc.ref hdc,
        ihr hdr fun c' hc' => ih c' (List.mem_cons_of_mem _ hc')⟩

/-- Forgetting subtree-size annotations preserves tree denotation. -/
theorem DenotesRanked.toDenotes {s : RankedStore α β H} {ref : Option H} {tr : BTree α β}
    (hd : DenotesRanked s ref tr) : Denotes s.toStore ref tr := by
  induction tr generalizing ref with
  | leaf =>
    cases ref with
    | none => exact denotes_none_leaf _
    | some h => exact (denotesRanked_some_leaf s h hd).elim
  | node first rest ih₁ ih₂ =>
    cases ref with
    | none => exact (denotesRanked_none_node s first rest hd).elim
    | some h =>
      obtain ⟨hf, _, hr⟩ := (denotesRanked_some_node_iff s h first rest).mp hd
      rw [denotes_some_node_iff]
      refine ⟨ih₁ hf, hr.toDenotesRest fun c hc r hdc => ?_⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
      exact ih₂ e he hdc

/-- Canonical order-statistic store over `H := BTree α β`. -/
def canonicalRankedStore : RankedStore α β (BTree α β)
  | .leaf => ⟨⟨none, 0⟩, []⟩
  | .node first rest =>
    ⟨⟨toRef first, first.size⟩, rest.map fun (k, v, c) => ⟨k, v, ⟨toRef c, c.size⟩⟩⟩

private theorem denotesRankedRest_canonicalRankedStore (rest : List (BTree.Triple α β))
    (ih : ∀ e ∈ rest,
      DenotesRanked (canonicalRankedStore (α := α) (β := β)) (toRef e.child) e.child) :
    DenotesRankedRest (canonicalRankedStore (α := α) (β := β))
      (rest.map fun (k, v, c) => ⟨k, v, ⟨toRef c, c.size⟩⟩) rest := by
  induction rest with
  | nil => exact denotesRankedRest_nil_nil _
  | cons e rest ihr =>
    obtain ⟨k, v, c⟩ := e
    rw [List.map_cons, denotesRankedRest_cons_cons_iff]
    exact ⟨rfl, rfl, ih (k, v, c) List.mem_cons_self, rfl,
      ihr fun e' he' => ih e' (List.mem_cons_of_mem _ he')⟩

/-- Every `BTree α β` is denoted in `canonicalRankedStore` by `toRef tr`. -/
theorem denotesRanked_canonicalRankedStore (tr : BTree α β) :
    DenotesRanked (canonicalRankedStore (α := α) (β := β)) (toRef tr) tr := by
  induction tr with
  | leaf => exact denotesRanked_none_leaf _
  | node first rest ih₁ ih₂ =>
    rw [toRef, denotesRanked_some_node_iff]
    exact ⟨ih₁, rfl, denotesRankedRest_canonicalRankedStore rest ih₂⟩

end Ranked

end Cslib.DataStructure.BTree.NodeAccess
