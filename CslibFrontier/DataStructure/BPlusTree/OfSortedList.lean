/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BPlusTree.Height
public import CslibFrontier.DataStructure.BPlusTree.Insert
public import CslibFrontier.DataStructure.BPlusTree.Lookup
public import CslibFrontier.DataStructure.BTree.OfSortedList

/-!
# Bulk loading of B+-trees

Bottom-up bulk loading of the B+-trees of `Cslib.DataStructure.BPlusTree`: a tree is built from a
list of entries in one pass, level by level from the bottom.

The bottom level cuts the entries into leaves of `t - 1` to `2 * t - 1` entries. `chunkSizes`
chooses the sizes with one look ahead: a leaf of `2 * t - 1` entries unless that would leave
fewer than `t - 1` for the rest, then one of `t - 1`. At most `2 * t - 1` entries, the empty list
included, form a single root leaf. Each leaf after the first is introduced by a separator, which
is a copy of its first key: no entry moves up between leaves.

A level above the leaves is a first tree followed by `(separator, tree)` branches, all of its
trees of one height. A round cuts the branches of a level into groups of `t - 1` to `2 * t - 1`
branches with one branch between consecutive groups: each group becomes a node one level taller,
and the separator of each branch between groups moves up, its child becoming the first child of
the next node. This is the round of the classic loader `Cslib.DataStructure.BTree.ofSortedList`,
and the group sizes are its `Cslib.DataStructure.BTree.groupSizes`. `packM` cuts a level by a list
of sizes, and `buildM` runs rounds until at most `2 * t - 1` branches are left, which become the
root. Below `2` the loader uses minimum degree `2`.

Each operation is defined once over an arbitrary monad `m`, with a node-visit action
`visit : m Unit` that fires once per node built, the leaves included; no comparator is needed,
since the input order is kept. The pure operation is the `Id` instantiation with
`visit := pure ()`. All recursion is structural, on a fuel argument or on a list of sizes, so the
definitions are `@[expose]`d and `decide` evaluates bulk loading on concrete inputs; when the fuel
or the sizes run out, what remains becomes a single leaf or node, which keeps the entries. Costs
are not stated here.

## Main definitions

* `chunkSizes`: the sizes of the leaves.
* `leafBranchesM`, `leafLevelM`: the leaves after the first with their separators, and the bottom
  level.
* `packM`, `buildM`: one round, and all rounds.
* `ofSortedListM`, `ofSortedList`: bulk loading, polymorphic and pure.

## Main results

* `map_ofSortedListM`: a monad morphism commutes with bulk loading.
* `toList_ofSortedList`: bulk loading keeps the entries in order, for every list and every `t`.
* `height_ofSortedList_le`: for `2 ≤ t`, the height is at most `Nat.log t l.length + 1`, for
  every list.
* `isWF_ofSortedList`: on a sorted list and for `2 ≤ t`, the result is well-formed.
* `lookup_ofSortedList`: on a sorted list, lookup is `List.lookup`.

## References

* [R. Bayer and E. McCreight, *Organization and Maintenance of Large Ordered
  Indexes*][BayerMcCreight1972]
* [D. Comer, *The Ubiquitous B-Tree*][Comer1979]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 18][CLRS2009]

The statements here are not taken from a source.
-/

public section

universe w

namespace Cslib.DataStructure

namespace BPlusTree

/-- The sizes of the leaves when `n` entries are cut into leaves of `t - 1` to `2 * t - 1`
entries, with recursion bounded by `fuel`. A leaf has `2 * t - 1` entries unless that would leave
fewer than `t - 1`, then `t - 1`; at most `2 * t - 1` entries form the last leaf. Out of fuel, the
remaining entries form one leaf. The sizes are in bounds for `2 ≤ t`; below that a size can be
`0`. -/
@[expose] def chunkSizes (t : ℕ) : ℕ → ℕ → List ℕ
  | 0, n => [n]
  | fuel + 1, n =>
    if n ≤ 2 * t - 1 then [n]
    else
      let s := if n < 3 * t - 2 then t - 1 else 2 * t - 1
      s :: chunkSizes t fuel (n - s)

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- Cut entries into leaves by a list of sizes, each leaf under a copy of its first key as its
separator. When the sizes run out, the remaining entries form one leaf. A size of `0` gives an
empty leaf under the first remaining key. `visit` fires once per leaf built. -/
@[expose] def leafBranchesM (visit : m Unit) : List ℕ → List (α × β) → m (List (Branch α β))
  | _, [] => pure []
  | [], p :: l => do visit; pure [(p.1, .leaf (p :: l))]
  | s :: ss, p :: l => do
    visit
    let bs ← leafBranchesM visit ss ((p :: l).drop s)
    pure ((p.1, .leaf ((p :: l).take s)) :: bs)

/-- No entries give no leaves. -/
@[simp] theorem leafBranchesM_nil (visit : m Unit) (ss : List ℕ) :
    leafBranchesM visit ss ([] : List (α × β)) = pure [] := by
  -- `leafBranchesM` matches on the sizes as well, so each case unfolds by `rfl`
  cases ss <;> rfl

/-- The bottom level: the first leaf, of the first size, and the later leaves with their
separators. With no sizes, all entries form one leaf. `visit` fires once per leaf built. -/
@[expose] def leafLevelM (visit : m Unit) :
    List ℕ → List (α × β) → m (BPlusTree α β × List (Branch α β))
  | [], l => do visit; pure (.leaf l, [])
  | s :: ss, l => do
    visit
    let bs ← leafBranchesM visit ss (l.drop s)
    pure (.leaf (l.take s), bs)

/-- Cut a level by a list of group sizes: the node over the first group, and the next level's
branches, each a separator moved up with the node over the following group. The last group takes
the remaining branches. `visit` fires once per node built. -/
@[expose] def packM (visit : m Unit) (first : BPlusTree α β) (rest : List (Branch α β)) :
    List ℕ → m (BPlusTree α β × List (Branch α β))
  | [] => do visit; pure (.node first rest, [])
  | s :: ss =>
    match rest.drop s with
    | [] => do visit; pure (.node first rest, [])
    | (k, c) :: rest' => do
      visit
      let p ← packM visit c rest' ss
      pure (.node first (rest.take s), (k, p.1) :: p.2)

/-- With no sizes left, the whole level is one node. -/
@[simp] theorem packM_nil (visit : m Unit) (first : BPlusTree α β) (rest : List (Branch α β)) :
    packM visit first rest [] = (do visit; pure (.node first rest, [])) := rfl

/-- A group of `s` branches becomes a node, and the separator of the branch after it moves up
over the rest. -/
theorem packM_cons (visit : m Unit) (first : BPlusTree α β) (rest : List (Branch α β))
    (s : ℕ) (ss : List ℕ) :
    packM visit first rest (s :: ss) =
      (match rest.drop s with
      | [] => do visit; pure (.node first rest, [])
      | (k, c) :: rest' => do
        visit
        let p ← packM visit c rest' ss
        pure (.node first (rest.take s), (k, p.1) :: p.2)) := rfl

/-- Rounds of bulk loading at minimum degree `t`, at most `fuel` of them: a level with no
branches is its first tree, a level with at most `2 * t - 1` branches becomes the root, and a
longer one is cut by `Cslib.DataStructure.BTree.groupSizes` into the next level. Out of fuel, the
level becomes one node. -/
@[expose] def buildM (t : ℕ) (visit : m Unit) :
    ℕ → BPlusTree α β → List (Branch α β) → m (BPlusTree α β)
  | _, first, [] => pure first
  | fuel, first, e :: es =>
    if (e :: es).length ≤ 2 * t - 1 then do visit; pure (.node first (e :: es))
    else
      match fuel with
      | 0 => do visit; pure (.node first (e :: es))
      | fuel + 1 => do
        let p ← packM visit first (e :: es)
          (BTree.groupSizes t (e :: es).length (e :: es).length)
        buildM t visit fuel p.1 p.2

/-- A level with no branches is its first tree. -/
@[simp] theorem buildM_nil (t : ℕ) (visit : m Unit) (fuel : ℕ) (first : BPlusTree α β) :
    buildM t visit fuel first [] = pure first := by
  -- `buildM` matches on the fuel as well, so each fuel case unfolds by `rfl`
  cases fuel <;> rfl

/-- A round of bulk loading on a level with branches. -/
theorem buildM_cons (t : ℕ) (visit : m Unit) (fuel : ℕ) (first : BPlusTree α β)
    (e : Branch α β) (es : List (Branch α β)) :
    buildM t visit fuel first (e :: es) =
      (if (e :: es).length ≤ 2 * t - 1 then do visit; pure (.node first (e :: es))
      else
        match fuel with
        | 0 => do visit; pure (.node first (e :: es))
        | fuel + 1 => do
          let p ← packM visit first (e :: es)
            (BTree.groupSizes t (e :: es).length (e :: es).length)
          buildM t visit fuel p.1 p.2) := by
  -- `buildM` matches on the fuel as well, so each fuel case unfolds by `rfl`
  cases fuel <;> rfl

/-- Bulk loading at minimum degree `t`, or `2` when `t` is below `2`: the bottom level cut by
`chunkSizes`, then the rounds of `buildM`, with fuel the number of branches of the bottom
level. -/
@[expose] def ofSortedListM (t : ℕ) (visit : m Unit) (l : List (α × β)) : m (BPlusTree α β) := do
  let p ← leafLevelM visit (chunkSizes (max t 2) l.length l.length) l
  buildM (max t 2) visit p.2.length p.1 p.2

/-- Bulk loading cuts the bottom level and runs the rounds of `buildM`, at minimum degree
`max t 2`. -/
theorem ofSortedListM_def (t : ℕ) (visit : m Unit) (l : List (α × β)) :
    ofSortedListM t visit l = (do
      let p ← leafLevelM visit (chunkSizes (max t 2) l.length l.length) l
      buildM (max t 2) visit p.2.length p.1 p.2) := (rfl)

end Polymorphic

section Transfer

open Cslib (IsMonadHom)

variable {α β : Type} {m n : Type → Type*} [Monad m] [Monad n]
  {f : {γ : Type} → m γ → n γ}

/-- A monad morphism commutes with cutting entries into leaves. -/
private theorem map_leafBranchesM (hf : IsMonadHom m n f) (visit : m Unit) (ss : List ℕ)
    (l : List (α × β)) : f (leafBranchesM visit ss l) = leafBranchesM (f visit) ss l := by
  induction ss generalizing l with
  | nil => cases l <;> simp [leafBranchesM, hf.map_bind, hf.map_pure]
  | cons s ss ih => cases l <;> simp [leafBranchesM, hf.map_bind, hf.map_pure, ih]

/-- A monad morphism commutes with cutting the bottom level. -/
private theorem map_leafLevelM (hf : IsMonadHom m n f) (visit : m Unit) (ss : List ℕ)
    (l : List (α × β)) : f (leafLevelM visit ss l) = leafLevelM (f visit) ss l := by
  cases ss <;> simp [leafLevelM, hf.map_bind, hf.map_pure, map_leafBranchesM hf]

/-- A monad morphism commutes with cutting a level. -/
private theorem map_packM (hf : IsMonadHom m n f) (visit : m Unit) (first : BPlusTree α β)
    (rest : List (Branch α β)) (ss : List ℕ) :
    f (packM visit first rest ss) = packM (f visit) first rest ss := by
  induction ss generalizing first rest with
  | nil => simp [packM_nil, hf.map_bind, hf.map_pure]
  | cons s ss ih =>
    rw [packM_cons, packM_cons]
    split <;> simp [hf.map_bind, hf.map_pure, ih]

/-- A monad morphism commutes with the rounds of bulk loading. -/
private theorem map_buildM (hf : IsMonadHom m n f) (t : ℕ) (visit : m Unit) (fuel : ℕ)
    (first : BPlusTree α β) (rest : List (Branch α β)) :
    f (buildM t visit fuel first rest) = buildM t (f visit) fuel first rest := by
  induction fuel generalizing first rest with
  | zero =>
    rcases rest with _ | ⟨e, es⟩
    · simp [hf.map_pure]
    rw [buildM_cons, buildM_cons]
    split <;> simp [hf.map_bind, hf.map_pure]
  | succ fuel ih =>
    rcases rest with _ | ⟨e, es⟩
    · simp [hf.map_pure]
    rw [buildM_cons, buildM_cons]
    split <;> simp [hf.map_bind, hf.map_pure, map_packM hf, ih]

/-- A monad morphism commutes with bulk loading. -/
theorem map_ofSortedListM (hf : IsMonadHom m n f) (t : ℕ) (visit : m Unit)
    (l : List (α × β)) :
    f (ofSortedListM t visit l) = ofSortedListM t (f visit) l := by
  simp [ofSortedListM, hf.map_bind, map_leafLevelM hf, map_buildM hf]

end Transfer

section Pure

variable {α β : Type} {t : ℕ}

/-- Pure bulk loading. -/
@[expose] def ofSortedList (t : ℕ) (l : List (α × β)) : BPlusTree α β :=
  Id.run (ofSortedListM t (pure ()) l)

/-- `ofSortedList` is the `Id` instantiation of `ofSortedListM`. -/
theorem ofSortedList_def (l : List (α × β)) :
    ofSortedList t l = Id.run (ofSortedListM t (pure ()) l) := (rfl)

/-! ### Pure forms of the steps -/

/-- Pure cutting of entries into leaves. -/
private def leafBranches (ss : List ℕ) (l : List (α × β)) : List (Branch α β) :=
  Id.run (leafBranchesM (pure ()) ss l)

/-- Pure cutting of the bottom level. -/
private def leafLevel (ss : List ℕ) (l : List (α × β)) : BPlusTree α β × List (Branch α β) :=
  Id.run (leafLevelM (pure ()) ss l)

/-- Pure cutting of a level by a list of group sizes. -/
private def pack (first : BPlusTree α β) (rest : List (Branch α β)) (ss : List ℕ) :
    BPlusTree α β × List (Branch α β) :=
  Id.run (packM (pure ()) first rest ss)

/-- Pure rounds of bulk loading. -/
private def build (t fuel : ℕ) (first : BPlusTree α β) (rest : List (Branch α β)) :
    BPlusTree α β :=
  Id.run (buildM t (pure ()) fuel first rest)

private theorem leafBranches_nil (ss : List ℕ) :
    leafBranches ss ([] : List (α × β)) = [] := by
  simp [leafBranches]

private theorem leafBranches_nil_cons (p : α × β) (l : List (α × β)) :
    leafBranches [] (p :: l) = [(p.1, .leaf (p :: l))] :=
  -- `Id.run` of `visit; pure` with `visit := pure ()` is the list, by `Id` defeq
  rfl

private theorem leafBranches_cons_cons (s : ℕ) (ss : List ℕ) (p : α × β) (l : List (α × β)) :
    leafBranches (s :: ss) (p :: l) =
      (p.1, .leaf ((p :: l).take s)) :: leafBranches ss ((p :: l).drop s) :=
  -- the `Id` binds reduce by `rfl`
  rfl

private theorem leafLevel_nil (l : List (α × β)) : leafLevel [] l = (.leaf l, []) := rfl

private theorem leafLevel_cons (s : ℕ) (ss : List ℕ) (l : List (α × β)) :
    leafLevel (s :: ss) l = (.leaf (l.take s), leafBranches ss (l.drop s)) := rfl

private theorem pack_nil (first : BPlusTree α β) (rest : List (Branch α β)) :
    pack first rest [] = (.node first rest, []) := rfl

private theorem pack_cons_of_drop_eq_nil {first : BPlusTree α β} {rest : List (Branch α β)}
    {s : ℕ} (ss : List ℕ) (h : rest.drop s = []) :
    pack first rest (s :: ss) = (.node first rest, []) := by
  -- `pack` unfolds through `Id` to the `match` of `packM_cons`
  simp only [pack, packM_cons, h]
  rfl

private theorem pack_cons_of_drop_eq_cons {first : BPlusTree α β} {rest : List (Branch α β)}
    {s : ℕ} {k : α} {c : BPlusTree α β} {rest' : List (Branch α β)} (ss : List ℕ)
    (h : rest.drop s = (k, c) :: rest') :
    pack first rest (s :: ss) =
      (.node first (rest.take s), (k, (pack c rest' ss).1) :: (pack c rest' ss).2) := by
  -- `pack` unfolds through `Id` to the `match` of `packM_cons`
  simp only [pack, packM_cons, h]
  rfl

private theorem build_nil (fuel : ℕ) (first : BPlusTree α β) :
    build t fuel first [] = first := by
  simp [build]

private theorem build_of_length_le {fuel : ℕ} {first : BPlusTree α β}
    {rest : List (Branch α β)} (hne : rest ≠ []) (h : rest.length ≤ 2 * t - 1) :
    build t fuel first rest = .node first rest := by
  obtain ⟨e, es, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [build, buildM_cons, h, ↓reduceIte]
  -- `Id.run` of `visit; pure` with `visit := pure ()` is the node, by `Id` defeq
  rfl

private theorem build_zero_cons (first : BPlusTree α β) (e : Branch α β)
    (es : List (Branch α β)) : build t 0 first (e :: es) = .node first (e :: es) := by
  -- out of fuel, both branches of `buildM` build the node
  simp only [build, buildM_cons]
  split <;> rfl

private theorem build_succ_of_lt {fuel : ℕ} {first : BPlusTree α β} {rest : List (Branch α β)}
    (h : 2 * t - 1 < rest.length) :
    build t (fuel + 1) first rest =
      build t fuel (pack first rest (BTree.groupSizes t rest.length rest.length)).1
        (pack first rest (BTree.groupSizes t rest.length rest.length)).2 := by
  obtain ⟨e, es, rfl⟩ :=
    List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (Nat.zero_lt_of_lt h))
  simp only [build, buildM_cons, Nat.not_le.2 h, ↓reduceIte]
  -- the remaining `match` on the fuel and the `Id` binds reduce by `rfl`
  rfl

private theorem ofSortedList_eq_build (l : List (α × β)) :
    ofSortedList t l =
      build (max t 2) (leafLevel (chunkSizes (max t 2) l.length l.length) l).2.length
        (leafLevel (chunkSizes (max t 2) l.length l.length) l).1
        (leafLevel (chunkSizes (max t 2) l.length l.length) l).2 :=
  -- both sides are `Id.run` of the same computation, by `Id` defeq
  rfl

/-! ### Entries -/

private theorem toList_leafBranches (ss : List ℕ) (l : List (α × β)) :
    ((leafBranches ss l).flatMap fun e => e.child.toList) = l := by
  induction ss generalizing l with
  | nil => cases l <;> simp [leafBranches_nil, leafBranches_nil_cons]
  | cons s ss ih =>
    rcases l with _ | ⟨p, l⟩
    · simp [leafBranches_nil]
    rw [leafBranches_cons_cons, List.flatMap_cons, ih, Branch.child_mk, toList_leaf,
      List.take_append_drop]

private theorem toList_leafLevel (ss : List ℕ) (l : List (α × β)) :
    (leafLevel ss l).1.toList ++ ((leafLevel ss l).2.flatMap fun e => e.child.toList) = l := by
  cases ss with
  | nil => simp [leafLevel_nil]
  | cons s ss => rw [leafLevel_cons, toList_leafBranches, toList_leaf, List.take_append_drop]

/-- Cutting a level keeps its entries in order. -/
private theorem toList_pack (first : BPlusTree α β) (rest : List (Branch α β)) (ss : List ℕ) :
    (pack first rest ss).1.toList ++ ((pack first rest ss).2.flatMap fun e => e.child.toList) =
      first.toList ++ rest.flatMap fun e => e.child.toList := by
  induction ss generalizing first rest with
  | nil => simp [pack_nil]
  | cons s ss ih =>
    rcases h : rest.drop s with _ | ⟨⟨k, c⟩, rest'⟩
    · rw [pack_cons_of_drop_eq_nil ss h]
      simp
    · rw [pack_cons_of_drop_eq_cons ss h]
      have hr : rest = rest.take s ++ (k, c) :: rest' := by
        rw [← h, List.take_append_drop]
      have := ih c rest'
      conv_rhs => rw [hr]
      simp only [toList_node, List.flatMap_cons, List.flatMap_append, List.append_assoc,
        Branch.child_mk, this]

/-- The first tree of a cut level starts with the entries of the level's first tree. -/
private theorem toList_pack_fst (first : BPlusTree α β) (rest : List (Branch α β))
    (ss : List ℕ) : ∃ l, (pack first rest ss).1.toList = first.toList ++ l := by
  cases ss with
  | nil => exact ⟨_, by rw [pack_nil, toList_node]⟩
  | cons s ss =>
    rcases h : rest.drop s with _ | ⟨⟨k, c⟩, rest'⟩
    · exact ⟨_, by rw [pack_cons_of_drop_eq_nil ss h, toList_node]⟩
    · exact ⟨_, by rw [pack_cons_of_drop_eq_cons ss h, toList_node]⟩

/-- The rounds of bulk loading keep the entries of a level in order. -/
private theorem toList_build (fuel : ℕ) (first : BPlusTree α β) (rest : List (Branch α β)) :
    (build t fuel first rest).toList = first.toList ++ rest.flatMap fun e => e.child.toList := by
  induction fuel generalizing first rest with
  | zero => rcases rest with _ | ⟨e, es⟩ <;> simp [build_nil, build_zero_cons]
  | succ fuel ih =>
    rcases Nat.lt_or_ge (2 * t - 1) rest.length with h | h
    · rw [build_succ_of_lt h, ih, toList_pack]
    · rcases rest with _ | ⟨e, es⟩
      · simp [build_nil]
      rw [build_of_length_le (List.cons_ne_nil e es) h, toList_node]

/-- Bulk loading keeps the entries in order, for every list and every `t`. -/
@[simp] theorem toList_ofSortedList (t : ℕ) (l : List (α × β)) :
    (ofSortedList t l).toList = l := by
  rw [ofSortedList_eq_build, toList_build, toList_leafLevel]

/-- Bulk loading keeps the number of entries. -/
@[simp] theorem size_ofSortedList (t : ℕ) (l : List (α × β)) :
    (ofSortedList t l).size = l.length := by
  rw [← length_toList, toList_ofSortedList]

/-! ### Leaf sizes -/

private theorem chunkSizes_of_le {fuel n : ℕ} (h : n ≤ 2 * t - 1) :
    chunkSizes t fuel n = [n] := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [chunkSizes, h, ↓reduceIte]

private theorem chunkSizes_succ_of_lt {fuel n : ℕ} (h : 2 * t - 1 < n) :
    chunkSizes t (fuel + 1) n =
      (if n < 3 * t - 2 then t - 1 else 2 * t - 1) ::
        chunkSizes t fuel (n - (if n < 3 * t - 2 then t - 1 else 2 * t - 1)) := by
  simp only [chunkSizes, Nat.not_le.2 h, ↓reduceIte]

/-- The leaf sizes add up to the number of entries. -/
private theorem sum_chunkSizes (t fuel n : ℕ) : (chunkSizes t fuel n).sum = n := by
  induction fuel generalizing n with
  | zero => simp [chunkSizes]
  | succ fuel ih =>
    rcases Nat.lt_or_ge (2 * t - 1) n with h | h
    · rw [chunkSizes_succ_of_lt h, List.sum_cons, ih]
      split <;> omega
    · simp [chunkSizes_of_le h]

/-- At a minimum degree of at least `2`, the leaves of at least `t - 1` entries all have `t - 1`
to `2 * t - 1` entries, given fuel at least the number of entries. -/
private theorem chunkSizes_bounds (ht : 2 ≤ t) {fuel n : ℕ} (hn : t - 1 ≤ n) (hf : n ≤ fuel) :
    ∀ s ∈ chunkSizes t fuel n, t - 1 ≤ s ∧ s ≤ 2 * t - 1 := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
    rcases Nat.lt_or_ge (2 * t - 1) n with h | h
    · rw [chunkSizes_succ_of_lt h]
      intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · split <;> omega
      · refine ih ?_ ?_ s hs <;> split <;> omega
    · rw [chunkSizes_of_le h]
      intro s hs
      rw [List.mem_singleton.1 hs]
      exact ⟨hn, h⟩

/-- At most `2 * t - 1` entries are loaded into a single leaf. -/
private theorem ofSortedList_of_length_le {l : List (α × β)} (ht : 2 ≤ t)
    (h : l.length ≤ 2 * t - 1) : ofSortedList t l = .leaf l := by
  rw [ofSortedList_eq_build, Nat.max_eq_left ht, chunkSizes_of_le h, leafLevel_cons,
    List.drop_length, leafBranches_nil, List.take_length]
  exact build_nil _ _

/-- Below `2` the loader uses minimum degree `2`. -/
private theorem ofSortedList_max (t : ℕ) (l : List (α × β)) :
    ofSortedList (max t 2) l = ofSortedList t l := by
  simp only [ofSortedList_def, ofSortedListM_def, Nat.max_assoc, Nat.max_self]

/-- Cutting a level by a grouping gives one branch per size. -/
private theorem length_pack {r : ℕ} {ss : List ℕ} {first : BPlusTree α β}
    {rest : List (Branch α β)} (hg : BTree.IsGrouping t r ss) (hr : rest.length = r) :
    (pack first rest ss).2.length = ss.length := by
  induction hg generalizing first rest with
  | last => rfl
  | @cut s r ss _ _ _ ih =>
    rcases hd : rest.drop s with _ | ⟨⟨k, c⟩, rest'⟩
    · have := congrArg List.length hd
      simp only [List.length_drop, List.length_nil] at this
      omega
    · have := congrArg List.length hd
      simp only [List.length_drop, List.length_cons] at this
      rw [pack_cons_of_drop_eq_cons ss hd, List.length_cons, List.length_cons, ih (by omega)]

/-! ### Shape -/

/-- The separator of a branch is the first key of its child. -/
private def HeadKey (e : Branch α β) : Prop := ∃ v l, e.child.toList = (e.1, v) :: l

/-- Cutting a level of height `h` by a grouping gives a level of height `h + 1`. -/
private theorem good_pack {h r : ℕ} {ss : List ℕ} {first : BPlusTree α β}
    {rest : List (Branch α β)} (hg : BTree.IsGrouping t r ss) (hlen : rest.length = r)
    (hf : Good t h first) (hr : ∀ e ∈ rest, Good t h e.child) :
    Good t (h + 1) (pack first rest ss).1 ∧
      ∀ e ∈ (pack first rest ss).2, Good t (h + 1) e.child := by
  induction hg generalizing first rest with
  | last h₁ h₂ =>
    rw [pack_nil]
    exact ⟨good_node hf hr (by omega) (by omega), by simp⟩
  | @cut s r ss h₁ h₂ _ ih =>
    rcases hd : rest.drop s with _ | ⟨⟨k, c⟩, rest'⟩
    · have := congrArg List.length hd
      simp only [List.length_drop, List.length_nil] at this
      omega
    · rw [pack_cons_of_drop_eq_cons ss hd]
      have hmem : ∀ e ∈ rest.drop s, e ∈ rest := fun e he => List.mem_of_mem_drop he
      rw [hd] at hmem
      have hlen' := congrArg List.length hd
      simp only [List.length_drop, List.length_cons] at hlen'
      obtain ⟨hf', hr'⟩ := ih (first := c) (rest := rest') (by omega)
        (hr _ (hmem _ List.mem_cons_self))
        (fun e he => hr e (hmem e (List.mem_cons_of_mem _ he)))
      refine ⟨good_node hf (fun e he => hr e (List.mem_of_mem_take he))
        (by rw [List.length_take]; omega) (by rw [List.length_take]; omega), ?_⟩
      rintro e (_ | ⟨_, he⟩)
      exacts [hf', hr' e he]

/-- The shape of a root at minimum degree `t`: the fields of `IsWF` that do not mention the
order. -/
private structure Shaped (t : ℕ) (tr : BPlusTree α β) : Prop where
  width_le : tr.width ≤ 2 * t - 1
  width_pos : (∀ entries, tr ≠ .leaf entries) → 1 ≤ tr.width
  occupied_of_mem_children : ∀ c ∈ tr.children, Occupied t c
  balanced : Balanced tr

/-- A tree of a level has the shape of a root at a minimum degree of at least `2`. -/
private theorem Good.shaped {h : ℕ} {c : BPlusTree α β} (ht : 2 ≤ t)
    (hf : Good t h c) : Shaped t c where
  width_le := hf.occupied.width_le
  width_pos _ := by have := hf.occupied.le_width; omega
  occupied_of_mem_children _ hc := hf.occupied.of_mem_children hc
  balanced := hf.balanced

/-- The rounds of bulk loading from a level build a tree of root shape, given fuel at least its
number of branches. -/
private theorem shaped_build {h fuel : ℕ} {first : BPlusTree α β} {rest : List (Branch α β)}
    (ht : 2 ≤ t) (hf : Good t h first) (hr : ∀ e ∈ rest, Good t h e.child)
    (hfuel : rest.length ≤ fuel) : Shaped t (build t fuel first rest) := by
  induction fuel generalizing h first rest with
  | zero =>
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hfuel)
    rw [build_nil]
    exact hf.shaped ht
  | succ fuel ih =>
    rcases Nat.lt_or_ge (2 * t - 1) rest.length with hlt | hle
    · rw [build_succ_of_lt hlt]
      have hg := BTree.isGrouping_groupSizes (t := t) (fuel := rest.length) (r := rest.length)
        (by omega) le_rfl
      obtain ⟨hf', hr'⟩ := good_pack hg rfl hf hr
      exact ih hf' hr' (by rw [length_pack hg rfl]; have := hg.two_mul_length_lt ht; omega)
    · rcases rest with _ | ⟨e, es⟩
      · rw [build_nil]
        exact hf.shaped ht
      · rw [build_of_length_le (List.cons_ne_nil e es) hle]
        exact
          { width_le := hle
            width_pos := fun _ => by simp
            occupied_of_mem_children := by
              intro c hc
              simp only [children_node, List.mem_cons, List.mem_map] at hc
              rcases hc with rfl | ⟨e', he', rfl⟩
              · exact hf.occupied
              · exact (hr e' (by simpa using he')).occupied
            balanced := .node hf.balanced (fun e' he' => (hr e' he').balanced)
              fun e' he' => (hr e' he').height_eq.trans hf.height_eq.symm }

/-- At a minimum degree of at least `2`, leaves of `t - 1` to `2 * t - 1` entries whose sizes add
up to the number of entries are trees of the bottom level, each under its first key. -/
private theorem good_leafBranches (ht : 2 ≤ t) {ss : List ℕ} {l : List (α × β)}
    (hss : ∀ s ∈ ss, t - 1 ≤ s ∧ s ≤ 2 * t - 1) (hsum : ss.sum = l.length) :
    ∀ e ∈ leafBranches ss l, Good t 1 e.child ∧ HeadKey e := by
  induction ss generalizing l with
  | nil =>
    cases l with
    | nil => simp [leafBranches_nil]
    | cons p l => simp at hsum
  | cons s ss ih =>
    cases l with
    | nil => simp [leafBranches_nil]
    | cons p l =>
      obtain ⟨h₁, h₂⟩ := hss s List.mem_cons_self
      rw [List.sum_cons] at hsum
      rw [leafBranches_cons_cons]
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · have hlen : ((p :: l).take s).length = s := by rw [List.length_take]; omega
        refine ⟨⟨.leaf, rfl, .leaf (by omega) (by omega)⟩, ?_⟩
        obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
        exact ⟨p.2, l.take s', by simp⟩
      · exact ih (fun s hs => hss s (List.mem_cons_of_mem _ hs))
          (by rw [List.length_drop]; omega) e he

/-- At a minimum degree of at least `2`, more than `2 * t - 1` entries are cut into a bottom
level of occupied leaves, each leaf after the first under its first key. -/
private theorem good_leafLevel (ht : 2 ≤ t) {l : List (α × β)}
    (hlt : 2 * t - 1 < l.length) :
    Good t 1 (leafLevel (chunkSizes t l.length l.length) l).1 ∧
      ∀ e ∈ (leafLevel (chunkSizes t l.length l.length) l).2,
        Good t 1 e.child ∧ HeadKey e := by
  obtain ⟨n, hn⟩ : ∃ n, l.length = n + 1 := ⟨l.length - 1, by omega⟩
  have hc : chunkSizes t l.length l.length =
      (if l.length < 3 * t - 2 then t - 1 else 2 * t - 1) ::
        chunkSizes t n (l.length - (if l.length < 3 * t - 2 then t - 1 else 2 * t - 1)) := by
    have := chunkSizes_succ_of_lt (t := t) (fuel := n) hlt
    rwa [← hn] at this
  rw [hc, leafLevel_cons]
  generalize hsd : (if l.length < 3 * t - 2 then t - 1 else 2 * t - 1) = s
  have hs₁ : t - 1 ≤ s := by rw [← hsd]; split <;> omega
  have hs₂ : s ≤ 2 * t - 1 := by rw [← hsd]; split <;> omega
  have hs₃ : t - 1 ≤ l.length - s := by rw [← hsd]; split <;> omega
  have hlen : (l.take s).length = s := by rw [List.length_take]; omega
  exact ⟨⟨.leaf, rfl, .leaf (by omega) (by omega)⟩,
    good_leafBranches (l := l.drop s) ht (chunkSizes_bounds (fuel := n) ht hs₃ (by omega))
      (by rw [sum_chunkSizes, List.length_drop])⟩

/-- Bulk loading builds a tree of root shape at a minimum degree of at least `2`, for every
list. -/
private theorem shaped_ofSortedList (ht : 2 ≤ t) (l : List (α × β)) :
    Shaped t (ofSortedList t l) := by
  rcases Nat.lt_or_ge (2 * t - 1) l.length with hlt | hle
  · rw [ofSortedList_eq_build, Nat.max_eq_left ht]
    obtain ⟨hf, hr⟩ := good_leafLevel ht hlt
    exact shaped_build ht hf (fun e he => (hr e he).1) le_rfl
  · rw [ofSortedList_of_length_le ht hle]
    exact ⟨hle, fun hne => absurd rfl (hne l), by simp, .leaf⟩

/-- At a minimum degree of at least `2`, bulk loading meets the height bound of well-formed
trees, for every list: the shape does not depend on the keys. -/
theorem height_ofSortedList_le (ht : 2 ≤ t) (l : List (α × β)) :
    (ofSortedList t l).height ≤ Nat.log t l.length + 1 := by
  have hs := shaped_ofSortedList ht l
  simpa using hs.balanced.height_le_log ht hs.width_pos hs.occupied_of_mem_children

/-! ### Separators -/

variable [LinearOrder α]

/-- A node whose children are separated, each branch under the first key of its child, and whose
entries are sorted, is separated. -/
private theorem separated_node {first : BPlusTree α β} {rest : List (Branch α β)}
    (hf : Separated first) (hr : ∀ e ∈ rest, Separated e.child) (hk : ∀ e ∈ rest, HeadKey e)
    (hs : (first.toList ++ rest.flatMap fun e => e.child.toList).IsSortedAssoc) :
    Separated (.node first rest) := by
  obtain ⟨-, hrs, hfr⟩ := List.isSortedAssoc_append_iff.1 hs
  refine .node hf hr (fun e he p hp => ?_) ?_ fun e he p hp => ?_
  · obtain ⟨v, l, hl⟩ := hk e he
    have hc : e.child.toList.IsSortedAssoc := by
      refine hrs.sublist ?_
      rw [List.flatMap_def]
      exact List.sublist_flatten_of_mem
        (List.mem_map_of_mem (f := fun e : Branch α β => e.child.toList) he)
    rw [hl] at hc hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact le_rfl
    · exact ((List.isSortedAssoc_cons_iff.1 hc).1 p hp).le
  · have hp := hrs.pairwise
    rw [List.flatMap_def, List.pairwise_flatten] at hp
    refine (List.pairwise_map.1 hp.2).imp_of_mem fun {a b} _ hb hab p hp => ?_
    obtain ⟨v, l, hl⟩ := hk b hb
    exact hab p hp (b.1, v) (hl ▸ List.mem_cons_self)
  · obtain ⟨v, l, hl⟩ := hk e he
    exact hfr p hp (e.1, v) (List.mem_flatMap.2 ⟨e, he, hl ▸ List.mem_cons_self⟩)

/-- Cutting a level of separated trees with sorted entries, each branch under the first key of
its child, gives such a level. -/
private theorem separated_pack {first : BPlusTree α β} {rest : List (Branch α β)} (ss : List ℕ)
    (hf : Separated first) (hr : ∀ e ∈ rest, Separated e.child) (hk : ∀ e ∈ rest, HeadKey e)
    (hs : (first.toList ++ rest.flatMap fun e => e.child.toList).IsSortedAssoc) :
    Separated (pack first rest ss).1 ∧
      ∀ e ∈ (pack first rest ss).2, Separated e.child ∧ HeadKey e := by
  induction ss generalizing first rest with
  | nil =>
    rw [pack_nil]
    exact ⟨separated_node hf hr hk hs, by simp⟩
  | cons s ss ih =>
    rcases hd : rest.drop s with _ | ⟨⟨k, c⟩, rest'⟩
    · rw [pack_cons_of_drop_eq_nil ss hd]
      exact ⟨separated_node hf hr hk hs, by simp⟩
    · rw [pack_cons_of_drop_eq_cons ss hd]
      have hrest : rest = rest.take s ++ (k, c) :: rest' := by
        rw [← hd, List.take_append_drop]
      have hmem : ∀ e ∈ rest.drop s, e ∈ rest := fun e he => List.mem_of_mem_drop he
      rw [hd] at hmem
      have hs' : ((first.toList ++ (rest.take s).flatMap fun e => e.child.toList) ++
          (c.toList ++ rest'.flatMap fun e => e.child.toList)).IsSortedAssoc := by
        have := hs
        rw [hrest] at this
        simpa only [List.flatMap_append, List.flatMap_cons, List.append_assoc,
          Branch.child_mk] using this
      obtain ⟨hs₁, hs₂, -⟩ := List.isSortedAssoc_append_iff.1 hs'
      obtain ⟨hf', hr'⟩ := ih (first := c) (rest := rest')
        (hr _ (hmem _ List.mem_cons_self))
        (fun e he => hr e (hmem e (List.mem_cons_of_mem _ he)))
        (fun e he => hk e (hmem e (List.mem_cons_of_mem _ he))) hs₂
      refine ⟨separated_node hf (fun e he => hr e (List.mem_of_mem_take he))
        (fun e he => hk e (List.mem_of_mem_take he)) hs₁, ?_⟩
      rintro e (_ | ⟨_, he⟩)
      · refine ⟨hf', ?_⟩
        obtain ⟨v, l, hl⟩ := hk (k, c) (hmem _ List.mem_cons_self)
        obtain ⟨l', hl'⟩ := toList_pack_fst c rest' ss
        exact ⟨v, l ++ l', by rw [Branch.child_mk, hl', show c.toList = (k, v) :: l from hl]; rfl⟩
      · exact hr' e he

/-- The rounds of bulk loading from a level of separated trees with sorted entries, each branch
under the first key of its child, build a separated tree. -/
private theorem separated_build (fuel : ℕ) {first : BPlusTree α β} {rest : List (Branch α β)}
    (hf : Separated first) (hr : ∀ e ∈ rest, Separated e.child) (hk : ∀ e ∈ rest, HeadKey e)
    (hs : (first.toList ++ rest.flatMap fun e => e.child.toList).IsSortedAssoc) :
    Separated (build t fuel first rest) := by
  induction fuel generalizing first rest with
  | zero =>
    rcases rest with _ | ⟨e, es⟩
    · rwa [build_nil]
    rw [build_zero_cons]
    exact separated_node hf hr hk hs
  | succ fuel ih =>
    rcases Nat.lt_or_ge (2 * t - 1) rest.length with hlt | hle
    · rw [build_succ_of_lt hlt]
      obtain ⟨hf', hr'⟩ := separated_pack (BTree.groupSizes t rest.length rest.length) hf hr hk hs
      exact ih hf' (fun e he => (hr' e he).1) (fun e he => (hr' e he).2) (by rwa [toList_pack])
    · rcases rest with _ | ⟨e, es⟩
      · rwa [build_nil]
      rw [build_of_length_le (List.cons_ne_nil e es) hle]
      exact separated_node hf hr hk hs

/-- A tree of the bottom level is a leaf, hence separated. -/
private theorem Good.separated {c : BPlusTree α β} (h : Good t 1 c) : Separated c := by
  obtain ⟨es, rfl⟩ := height_eq_one_iff.1 h.height_eq
  exact .leaf

/-- Bulk loading a sorted list builds a well-formed tree at a minimum degree of at least `2`. -/
theorem isWF_ofSortedList {l : List (α × β)} (ht : 2 ≤ t) (h : l.IsSortedAssoc) :
    IsWF t (ofSortedList t l) :=
  have hs := shaped_ofSortedList ht l
  { two_le := ht
    width_le := hs.width_le
    width_pos := hs.width_pos
    occupied_of_mem_children := hs.occupied_of_mem_children
    balanced := hs.balanced
    separated := by
      rcases Nat.lt_or_ge (2 * t - 1) l.length with hlt | hle
      · rw [ofSortedList_eq_build, Nat.max_eq_left ht]
        obtain ⟨hf, hr⟩ := good_leafLevel ht hlt
        exact separated_build _ hf.separated (fun e he => (hr e he).1.separated)
          (fun e he => (hr e he).2) (by rwa [toList_leafLevel])
      · rw [ofSortedList_of_length_le ht hle]
        exact .leaf
    sorted := by rwa [toList_ofSortedList] }

/-- Lookup in a bulk-loaded sorted list is lookup in the list, for every `t`. -/
@[simp] theorem lookup_ofSortedList {l : List (α × β)} (h : l.IsSortedAssoc) (k : α) :
    lookup k (ofSortedList t l) = l.lookup k := by
  rw [← ofSortedList_max, lookup_eq (isWF_ofSortedList (le_max_right _ _) h), toList_ofSortedList]

end Pure

end BPlusTree

end Cslib.DataStructure
