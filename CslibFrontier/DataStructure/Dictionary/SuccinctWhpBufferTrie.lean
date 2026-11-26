/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.PackedLane
import CslibFrontier.Foundations.Logic.Function.UpdateKernel

/-!
# Bounded-Depth Character Trie Buffer (`BufTrie`) for Deamortized Salt Collisions

This module formalizes the pure model and exact invariants of the constant-depth character trie
(`BufTrie`) used for the growing and shrinking epoch buffers (`BufCur` and `BufOld`) in the
with-high-probability succinct dynamic dictionary ([Bender, Farach-Colton, J. Kuszmaul, and
W. Kuszmaul, SOSA 2024, Section 2.2 Lemma 2.2 and Section 5, pp. 363–373; author copy
pp. 3 and 6][BenderFarachColtonKuszmaulKuszmaul2024]).

Each Stage-1 reduced key `rKey < 2 ^ (cTab * bChar)` is decomposed into `cTab` digits in base
`2 ^ bChar` (`Cslib.DataStructure.laneGet`, `eq_of_forall_laneGet_eq_of_lt`). Augmenting SOSA
2024's `k`-trie for deterministic per-step background draining and cleanup without scanning all
`2 ^ bChar` child slots, a `BufTrie` stores:
* A rooted `2 ^ bChar`-ary trie (root at node `0`, allocated non-root nodes `1 .. nodeAlloc - 1`)
  recording `(nodeParent u, nodeChar u)` for each `1 ≤ u < nodeAlloc` so all dirty child entries can
  be re-zeroed incrementally in `O(1)` logical table updates per clear pop (`bufClearOne`,
  `bufClearSteps`) without scanning `2 ^ bChar` children.
* A sequential append log `0 .. itemAlloc - 1` (`itemLeaf`, `itemBucket`, `itemLoc`) paired with
  per-leaf slot index `nodeLeafItem` (`id + 1`, or `0` if never allocated in this epoch) and flag
  `nodeActive` (`0` if deleted/inactive, non-zero if active), so item `id < itemAlloc` is active iff
  `nodeLeafItem (itemLeaf id) = id + 1 ∧ nodeActive (itemLeaf id) ≠ 0`. Deletion clears
  `nodeActive leaf := 0` while preserving `nodeLeafItem leaf` (so same-epoch re-insertion reuses
  slot `id` with zero allocations), and the background drainer probes `0 .. itemAlloc - 1` via
  `bufCheckSlot` in `O(1)` logical table reads per slot without doubly-linked list pointers.

**Cost convention:** All `O(1)` and `O(cTab)` operation descriptions in this module count logical
table accesses/updates or clear pops (with `cTab` fixed). The definitions use pure `Nat` arithmetic
and functional `ℕ → ℕ` tables; this module does not certify Lean runtime or Word-RAM
instruction/memory cost.

## Main definitions

* `Cslib.DataStructure.Dictionary.SuccinctWhp.BufTrie`, `emptyBufTrie`: pure buffer-trie state.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.bufLookup`, `bufInsert`, `bufDelete`,
  `bufCheckSlot`, `bufClearOne`, `bufClearSteps`: pure buffer operations making `O(cTab)` logical
  table accesses/updates for trie walks and `O(1)` logical table accesses/updates per slot probe or
  clear pop (for fixed `cTab`, over pure `Nat` arithmetic and functional tables; Lean runtime and
  Word-RAM instruction/memory costs are not certified here).
* `Cslib.DataStructure.Dictionary.SuccinctWhp.ValidBufTrie`: structural, map-refinement,
  active-slot, and parent-log invariant for `BufTrie`.

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.validBufTrie_empty`,
  `ValidBufTrie.lookup_eq`, `ValidBufTrie.delete_spec`, `ValidBufTrie.insert_spec`,
  `ValidBufTrie.insert_nodeAlloc_le`, `ValidBufTrie.checkSlot_some`,
  `ValidBufTrie.exists_checkSlot_of_map_some`, `ValidBufTrie.toClearable`,
  `ClearableBufTrie.clearOne_step`, `ClearableBufTrie.clearSteps_spec`: exact map, slot-allocation,
  active-slot scan, and cleanup specifications.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Section 5][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

/-! ## Section 1: Pure `BufTrie` state and logical buffer operations -/

/-- Pure state of a bounded-depth character trie buffer with append-only item log and parent-edge
log for incremental re-zeroing in `O(1)` logical table updates per clear pop. -/
structure BufTrie where
  /-- Number of allocated trie nodes (`1` initially; node `0` is the root). -/
  nodeAlloc : ℕ
  /-- Number of allocated item log slots (`0 .. itemAlloc - 1`). -/
  itemAlloc : ℕ
  /-- Child pointer table: `0` denotes absent, `u ≥ 1` denotes child node `u`. -/
  trieChild : ℕ → ℕ → ℕ
  /-- Parent node of allocated non-root trie node `u ≥ 1`. -/
  nodeParent : ℕ → ℕ
  /-- Character edge from `nodeParent u` to `u`. -/
  nodeChar : ℕ → ℕ
  /-- Epoch-allocated item slot `+ 1` at leaf node `u` (`0` if never allocated in this epoch;
  retained across deletions while `nodeActive` records whether the slot is currently active). -/
  nodeLeafItem : ℕ → ℕ
  /-- Active flag (`0` if deleted/inactive, non-zero if currently active) at leaf node `u`. -/
  nodeActive : ℕ → ℕ
  /-- Leaf trie node associated with item log slot `id`. -/
  itemLeaf : ℕ → ℕ
  /-- Stored bucket index `b` for item log slot `id`. -/
  itemBucket : ℕ → ℕ
  /-- Stored local coordinate `loc` for item log slot `id`. -/
  itemLoc : ℕ → ℕ

/-- Clean empty `BufTrie` (`nodeAlloc = 1`, `itemAlloc = 0`, all tables zero). -/
@[expose] def emptyBufTrie : BufTrie where
  nodeAlloc := 1
  itemAlloc := 0
  trieChild := fun _ _ => 0
  nodeParent := fun _ => 0
  nodeChar := fun _ => 0
  nodeLeafItem := fun _ => 0
  nodeActive := fun _ => 0
  itemLeaf := fun _ => 0
  itemBucket := fun _ => 0
  itemLoc := fun _ => 0

/-- Walk `rem` digits starting at digit offset `off` from trie node `cur`, returning `some leaf` or
`none` if a zero child pointer is met. -/
@[expose] def bufWalk (bChar : ℕ) (child : ℕ → ℕ → ℕ) (rKey : ℕ) : ℕ → ℕ → ℕ → Option ℕ
  | 0, _, cur => some cur
  | rem + 1, off, cur =>
    let ch := laneGet bChar rKey off
    let nxt := child cur ch
    if nxt = 0 then none
    else bufWalk bChar child rKey rem (off + 1) nxt

/-- Lookup `rKey` in `tr`, returning `some (b, loc)` if present or `none` if absent. -/
@[expose] def bufLookup (cTab bChar : ℕ) (tr : BufTrie) (rKey : ℕ) : Option (ℕ × ℕ) :=
  match bufWalk bChar tr.trieChild rKey cTab 0 0 with
  | none => none
  | some leaf =>
    let id1 := tr.nodeLeafItem leaf
    if id1 = 0 ∨ tr.nodeActive leaf = 0 then none
    else some (tr.itemBucket (id1 - 1), tr.itemLoc (id1 - 1))

/-- Whether `rKey` has ever been assigned a leaf item slot in `tr` during the current epoch. -/
@[expose] def bufEverPresent (cTab bChar : ℕ) (tr : BufTrie) (rKey : ℕ) : Bool :=
  match bufWalk bChar tr.trieChild rKey cTab 0 0 with
  | none => false
  | some leaf => tr.nodeLeafItem leaf != 0

/-- Walk and allocate missing trie nodes along `rem` digits starting at `off` from `cur`, returning
`(tr', leaf)`. -/
@[expose] def bufEnsurePath (bChar rKey : ℕ) : ℕ → ℕ → BufTrie → ℕ → BufTrie × ℕ
  | 0, _, tr, cur => (tr, cur)
  | rem + 1, off, tr, cur =>
    let ch := laneGet bChar rKey off
    let nxt := tr.trieChild cur ch
    if nxt = 0 then
      let u := tr.nodeAlloc
      let child' := Function.update tr.trieChild cur (Function.update (tr.trieChild cur) ch u)
      let tr1 : BufTrie :=
        { tr with
          nodeAlloc := u + 1
          trieChild := child'
          nodeParent := Function.update tr.nodeParent u cur
          nodeChar := Function.update tr.nodeChar u ch
          nodeLeafItem := Function.update tr.nodeLeafItem u 0 }
      bufEnsurePath bChar rKey rem (off + 1) tr1 u
    else
      bufEnsurePath bChar rKey rem (off + 1) tr nxt

/-- Insert or overwrite `rKey ↦ (b, loc)` in `tr`:
* If `rKey`'s leaf already has an allocated epoch slot `id = id1 - 1` (active or previously
  deleted), reactivates and updates `(itemBucket, itemLoc)` in place without incrementing
  `itemAlloc` or `nodeAlloc`.
* Otherwise allocates `id := tr1.itemAlloc` (`itemAlloc + 1`) and links `leaf ↔ id`. -/
@[expose] def bufInsert (cTab bChar : ℕ) (tr : BufTrie) (rKey b loc : ℕ) : BufTrie :=
  let p := bufEnsurePath bChar rKey cTab 0 tr 0
  let tr1 := p.1
  let leaf := p.2
  let id1 := tr1.nodeLeafItem leaf
  if id1 = 0 then
    let id := tr1.itemAlloc
    { tr1 with
      itemAlloc := id + 1
      nodeLeafItem := Function.update tr1.nodeLeafItem leaf (id + 1)
      nodeActive := Function.update tr1.nodeActive leaf 1
      itemLeaf := Function.update tr1.itemLeaf id leaf
      itemBucket := Function.update tr1.itemBucket id b
      itemLoc := Function.update tr1.itemLoc id loc }
  else
    let id := id1 - 1
    { tr1 with
      nodeActive := Function.update tr1.nodeActive leaf 1
      itemBucket := Function.update tr1.itemBucket id b
      itemLoc := Function.update tr1.itemLoc id loc }

/-- Delete `rKey` from `tr` in `O(cTab)` logical table accesses and at most one flag update
(clearing `nodeActive leaf := 0` while preserving its epoch slot `nodeLeafItem leaf` so
re-insertions of `rKey` allocate zero new slots; pure functional model, not certified Lean or
Word-RAM execution cost). -/
@[expose] def bufDelete (cTab bChar : ℕ) (tr : BufTrie) (rKey : ℕ) : BufTrie :=
  match bufWalk bChar tr.trieChild rKey cTab 0 0 with
  | none => tr
  | some leaf =>
    if tr.nodeLeafItem leaf = 0 ∨ tr.nodeActive leaf = 0 then tr
    else { tr with nodeActive := Function.update tr.nodeActive leaf 0 }

/-- Scan probe at item slot `id < tr.itemAlloc` using `O(1)` logical table reads (pure functional
model, not certified Lean or Word-RAM execution cost): returns `some (b, loc)` iff item `id` is
still active (`nodeLeafItem (itemLeaf id) = id + 1 ∧ nodeActive (itemLeaf id) ≠ 0`). -/
@[expose] def bufCheckSlot (tr : BufTrie) (id : ℕ) : Option (ℕ × ℕ) :=
  if id < tr.itemAlloc then
    let leaf := tr.itemLeaf id
    if tr.nodeLeafItem leaf = id + 1 ∧ tr.nodeActive leaf ≠ 0 then
      some (tr.itemBucket id, tr.itemLoc id)
    else none
  else none

/-- One elementary cleanup pop using `O(1)` logical table reads/updates (pure functional model, not
certified Lean or Word-RAM execution cost): zeroes `itemAlloc := 0` on every step, pops one
allocated non-root node `u = nodeAlloc - 1` and re-zeroes `trieChild (nodeParent u) (nodeChar u)`
and `nodeLeafItem u` when `1 < nodeAlloc`, and sets `nodeAlloc := 1` and `nodeLeafItem 0 := 0` when
`nodeAlloc ≤ 1`. -/
@[expose] def bufClearOne (tr : BufTrie) : BufTrie :=
  if 1 < tr.nodeAlloc then
    let u := tr.nodeAlloc - 1
    let p := tr.nodeParent u
    let ch := tr.nodeChar u
    let child' := Function.update tr.trieChild p (Function.update (tr.trieChild p) ch 0)
    { tr with
      nodeAlloc := u
      itemAlloc := 0
      trieChild := child'
      nodeLeafItem := Function.update tr.nodeLeafItem u 0 }
  else
    { tr with
      nodeAlloc := 1
      itemAlloc := 0
      nodeLeafItem := Function.update tr.nodeLeafItem 0 0 }

/-- Execute `k` elementary `bufClearOne` pops. -/
@[expose] def bufClearSteps : ℕ → BufTrie → BufTrie
  | 0, tr => tr
  | k + 1, tr => bufClearSteps k (bufClearOne tr)

/-! ## Section 2: Exact structural and map invariant (`ValidBufTrie`) -/

/-- Structural, parent-log, and map-refinement invariant for `BufTrie` at character count `cTab`
and character bit-width `bChar`. -/
def ValidBufTrie (cTab bChar : ℕ) (tr : BufTrie)
    (mapFn : ℕ → Option (ℕ × ℕ)) : Prop :=
  1 ≤ tr.nodeAlloc ∧
  (∀ u, tr.nodeAlloc ≤ u → tr.nodeLeafItem u = 0) ∧
  (∀ k, 2 ^ (cTab * bChar) ≤ k → mapFn k = none) ∧
  (∀ k < 2 ^ (cTab * bChar), mapFn k = bufLookup cTab bChar tr k) ∧
  ∃ depth : ℕ → ℕ,
    depth 0 = 0 ∧
    (∀ u, 1 ≤ u → u < tr.nodeAlloc →
      tr.nodeParent u < u ∧
      tr.nodeChar u < 2 ^ bChar ∧
      depth u = depth (tr.nodeParent u) + 1 ∧
      depth u ≤ cTab ∧
      tr.trieChild (tr.nodeParent u) (tr.nodeChar u) = u) ∧
    (∀ v ch, tr.trieChild v ch ≠ 0 ↔
      (1 ≤ tr.trieChild v ch ∧
       tr.trieChild v ch < tr.nodeAlloc ∧
       tr.nodeParent (tr.trieChild v ch) = v ∧
       tr.nodeChar (tr.trieChild v ch) = ch)) ∧
    (∀ u < tr.nodeAlloc, tr.nodeLeafItem u ≠ 0 →
      depth u = cTab ∧
      tr.nodeLeafItem u ≤ tr.itemAlloc ∧
      tr.itemLeaf (tr.nodeLeafItem u - 1) = u ∧
      ∃ k < 2 ^ (cTab * bChar), bufWalk bChar tr.trieChild k cTab 0 0 = some u)

/-- `emptyBufTrie` satisfies `ValidBufTrie` for the empty map. -/
theorem validBufTrie_empty (cTab bChar : ℕ) :
    ValidBufTrie cTab bChar emptyBufTrie (fun _ => none) := by
  refine ⟨le_rfl, fun _ _ => rfl, fun _ _ => rfl, fun k _ => ?_, fun _ => 0, rfl,
    fun u _ hlt => absurd hlt (by dsimp [emptyBufTrie]; omega),
    fun v ch => by simp [emptyBufTrie], fun u _ hnz => by simp [emptyBufTrie] at hnz⟩
  cases cTab <;> simp [bufLookup, bufWalk, emptyBufTrie]

/-- Lookup on a `ValidBufTrie` agrees with `mapFn` on `< 2 ^ (cTab * bChar)`. -/
theorem ValidBufTrie.lookup_eq {cTab bChar rKey : ℕ} {tr : BufTrie}
    {mapFn : ℕ → Option (ℕ × ℕ)} (hv : ValidBufTrie cTab bChar tr mapFn)
    (hk : rKey < 2 ^ (cTab * bChar)) :
    bufLookup cTab bChar tr rKey = mapFn rKey :=
  (hv.2.2.2.1 rKey hk).symm

/-- Allocation and index-range projections of `ValidBufTrie` for Word-RAM packed-array safety. -/
theorem ValidBufTrie.bounds {cTab bChar : ℕ} {tr : BufTrie}
    {mapFn : ℕ → Option (ℕ × ℕ)} (hv : ValidBufTrie cTab bChar tr mapFn) :
    1 ≤ tr.nodeAlloc ∧
    (∀ u, tr.nodeAlloc ≤ u → tr.nodeLeafItem u = 0) ∧
    (∀ v ch, tr.trieChild v ch ≠ 0 → tr.trieChild v ch < tr.nodeAlloc) ∧
    (∀ u < tr.nodeAlloc, tr.nodeLeafItem u ≠ 0 → tr.nodeLeafItem u ≤ tr.itemAlloc) := by
  obtain ⟨halloc, hzero, _, _, _, _, _, hiff, hleaf⟩ := hv
  exact ⟨halloc, hzero, fun v ch hnz => ((hiff v ch).mp hnz).2.1,
    fun u hu hnz => (hleaf u hu hnz).2.1⟩

/-- Walk depth and injectivity lemma: under `ValidBufTrie`'s edge invariant, `bufWalk` from a node
`cur < nodeAlloc` of depth `off` reaches a node `< nodeAlloc` of depth `off + rem`, and any two
walks of length `rem` from depth `off` reaching the same node started at the same `cur` and read
the exact same `rem` digits. -/
private theorem bufWalk_props {bChar nodeAlloc : ℕ} {child : ℕ → ℕ → ℕ}
    {nodeParent nodeChar depth : ℕ → ℕ}
    (hp_edge : ∀ u, 1 ≤ u → u < nodeAlloc → depth u = depth (nodeParent u) + 1)
    (hiff : ∀ v ch, child v ch ≠ 0 ↔
      (1 ≤ child v ch ∧ child v ch < nodeAlloc ∧
       nodeParent (child v ch) = v ∧ nodeChar (child v ch) = ch)) :
    ∀ (rem off cur leaf : ℕ) (k : ℕ),
      cur < nodeAlloc → depth cur = off →
      bufWalk bChar child k rem off cur = some leaf →
      leaf < nodeAlloc ∧ depth leaf = off + rem ∧
      ∀ (cur₂ k₂ : ℕ), cur₂ < nodeAlloc → depth cur₂ = off →
        bufWalk bChar child k₂ rem off cur₂ = some leaf →
        cur = cur₂ ∧ (∀ j < rem, laneGet bChar k (off + j) = laneGet bChar k₂ (off + j)) := by
  intro rem
  induction rem with
  | zero =>
    intro off cur leaf k hcur _ hw
    simp only [bufWalk, Option.some.injEq] at hw
    subst hw
    refine ⟨hcur, by omega, fun cur₂ k₂ _ _ hw₂ => ?_⟩
    simp only [bufWalk, Option.some.injEq] at hw₂
    exact ⟨hw₂.symm, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ rem ih =>
    intro off cur leaf k _ hdep hw
    dsimp only [bufWalk] at hw
    split at hw
    · cases hw
    · rename_i h0
      obtain ⟨h1_ge, h1_lt, hp1, hc1⟩ := (hiff cur _).mp h0
      obtain ⟨hleaf_lt, _, huniq⟩ :=
        ih (off + 1) _ leaf k h1_lt (by rw [hp_edge _ h1_ge h1_lt, hp1, hdep]) hw
      refine ⟨hleaf_lt, by omega, fun cur₂ k₂ _ hdep₂ hw₂ => ?_⟩
      dsimp only [bufWalk] at hw₂
      split at hw₂
      · cases hw₂
      · rename_i h0₂
        obtain ⟨h2_ge, h2_lt, hp2, hc2⟩ := (hiff cur₂ _).mp h0₂
        obtain ⟨hnxt_eq, hdigits⟩ :=
          huniq _ k₂ h2_lt (by rw [hp_edge _ h2_ge h2_lt, hp2, hdep₂]) hw₂
        refine ⟨by rw [← hp1, hnxt_eq, hp2], fun j hj => ?_⟩
        rcases j with _ | j'
        · simpa only [Nat.add_zero] using (by rw [← hc1, hnxt_eq, hc2])
        · simpa only [Nat.add_assoc, Nat.add_comm 1 j'] using hdigits j' (by omega)

/-- Root-to-leaf walk injectivity: under `ValidBufTrie`'s edge invariant, distinct keys
`< 2 ^ (cTab * bChar)` never reach the same leaf node. -/
private theorem bufWalk_root_ne_of_ne {cTab bChar nodeAlloc : ℕ} {child : ℕ → ℕ → ℕ}
    {nodeParent nodeChar depth : ℕ → ℕ}
    (halloc : 1 ≤ nodeAlloc) (hd0 : depth 0 = 0)
    (hp_edge : ∀ u, 1 ≤ u → u < nodeAlloc → depth u = depth (nodeParent u) + 1)
    (hiff : ∀ v ch, child v ch ≠ 0 ↔
      (1 ≤ child v ch ∧ child v ch < nodeAlloc ∧
       nodeParent (child v ch) = v ∧ nodeChar (child v ch) = ch))
    {k₁ k₂ leaf₁ leaf₂ : ℕ}
    (hk₁ : k₁ < 2 ^ (cTab * bChar)) (hk₂ : k₂ < 2 ^ (cTab * bChar)) (hne : k₁ ≠ k₂)
    (hw₁ : bufWalk bChar child k₁ cTab 0 0 = some leaf₁)
    (hw₂ : bufWalk bChar child k₂ cTab 0 0 = some leaf₂) :
    leaf₁ ≠ leaf₂ := by
  intro hl_eq; subst hl_eq
  have hdig := ((bufWalk_props hp_edge hiff cTab 0 0 leaf₁ k₂ halloc hd0 hw₂).2.2
    0 k₁ halloc hd0 hw₁).2
  exact hne (eq_of_forall_laneGet_eq_of_lt hk₁ hk₂ fun d hd => by
    simpa only [Nat.zero_add] using (hdig d hd).symm)

/-- Monotonicity of `bufWalk`: adding new edges (without changing non-zero child pointers) preserves
every successful walk. -/
private theorem bufWalk_mono {bChar : ℕ} {child₁ child₂ : ℕ → ℕ → ℕ}
    (hmono : ∀ v ch, child₁ v ch ≠ 0 → child₂ v ch = child₁ v ch) :
    ∀ rem off cur leaf k,
      bufWalk bChar child₁ k rem off cur = some leaf →
      bufWalk bChar child₂ k rem off cur = some leaf := by
  intro rem
  induction rem with
  | zero => intro _ _ _ _ hw; exact hw
  | succ rem ih =>
    intro off cur leaf k hw
    dsimp only [bufWalk] at hw ⊢
    split at hw
    · cases hw
    · rename_i h0
      simp only [hmono _ _ h0, h0, ↓reduceIte]
      exact ih (off + 1) _ leaf k hw

/-- When every non-zero child pointer strictly increases node index (`v < child v ch`), `bufWalk`
never decreases the node index (`cur ≤ leaf`). -/
private theorem bufWalk_le_leaf {bChar : ℕ} {child : ℕ → ℕ → ℕ}
    (hinc : ∀ v ch, child v ch ≠ 0 → v < child v ch) :
    ∀ rem off cur leaf k,
      bufWalk bChar child k rem off cur = some leaf →
      cur ≤ leaf := by
  intro rem
  induction rem with
  | zero => intro _ _ _ _ hw; simp only [bufWalk, Option.some.injEq] at hw; omega
  | succ rem ih =>
    intro off cur leaf k hw
    dsimp only [bufWalk] at hw
    split at hw
    · cases hw
    · rename_i h0
      exact (hinc _ _ h0).le.trans (ih (off + 1) _ leaf k hw)

/-- If `bufWalk` fails in `child₁` (`= none`) and succeeds in an extension `child₂` (`= some leaf`)
where every newly added edge points to a node `≥ bound` and `child₂` strictly increases node
indices, then `bound ≤ leaf`. -/
private theorem bufWalk_ge_of_none {bChar bound : ℕ} {child₁ child₂ : ℕ → ℕ → ℕ}
    (hnew : ∀ v ch, child₂ v ch ≠ child₁ v ch → bound ≤ child₂ v ch)
    (hinc : ∀ v ch, child₂ v ch ≠ 0 → v < child₂ v ch) :
    ∀ rem off cur leaf k,
      bufWalk bChar child₁ k rem off cur = none →
      bufWalk bChar child₂ k rem off cur = some leaf →
      bound ≤ leaf := by
  intro rem
  induction rem with
  | zero => intro _ _ _ _ hw₁ _; simp [bufWalk] at hw₁
  | succ rem ih =>
    intro off cur leaf k hw₁ hw₂
    dsimp only [bufWalk] at hw₁ hw₂
    split at hw₂
    · cases hw₂
    · rename_i h0₂
      by_cases heq : child₂ cur (laneGet bChar k off) = child₁ cur (laneGet bChar k off)
      · simp only [heq ▸ h0₂, ↓reduceIte] at hw₁
        exact ih (off + 1) _ leaf k (heq ▸ hw₁) hw₂
      · exact (hnew cur _ heq).trans (bufWalk_le_leaf hinc rem (off + 1) _ leaf k hw₂)

/-- Exact specification of `bufDelete`: preserves `ValidBufTrie` for
`Function.update mapFn rKey none`, leaves `nodeAlloc`, `itemAlloc`, and `bufEverPresent` unchanged,
and never activates an inactive item slot. -/
theorem ValidBufTrie.delete_spec {cTab bChar rKey : ℕ} {tr : BufTrie}
    {mapFn : ℕ → Option (ℕ × ℕ)} (hv : ValidBufTrie cTab bChar tr mapFn)
    (hk : rKey < 2 ^ (cTab * bChar)) :
    let tr' := bufDelete cTab bChar tr rKey
    ValidBufTrie cTab bChar tr' (Function.update mapFn rKey none) ∧
    tr'.nodeAlloc = tr.nodeAlloc ∧
    tr'.itemAlloc = tr.itemAlloc ∧
    bufEverPresent cTab bChar tr' = bufEverPresent cTab bChar tr ∧
    (∀ id, bufCheckSlot tr id = none → bufCheckSlot tr' id = none) := by
  have ⟨halloc, hzero, hout, hmap, depth, hd0, hedge, hiff, hleaf⟩ := hv
  have hp_edge : ∀ u, 1 ≤ u → u < tr.nodeAlloc → depth u = depth (tr.nodeParent u) + 1 :=
    fun u h1 h2 => (hedge u h1 h2).2.2.1
  have hnoop : mapFn rKey = none → Function.update mapFn rKey none = mapFn := fun hmr =>
    Function.update_eq_self_iff.mpr hmr.symm
  dsimp only [bufDelete]
  cases hw : bufWalk bChar tr.trieChild rKey cTab 0 0 with
  | none =>
    rw [hnoop (by rw [hmap rKey hk]; simp [bufLookup, hw])]
    exact ⟨hv, rfl, rfl, rfl, fun _ h => h⟩
  | some leaf =>
    dsimp only
    by_cases hcond : tr.nodeLeafItem leaf = 0 ∨ tr.nodeActive leaf = 0
    · simp only [hcond, ↓reduceIte]
      rw [hnoop (by rw [hmap rKey hk]; simp [bufLookup, hw, hcond])]
      exact ⟨hv, trivial, trivial, trivial, fun _ h => h⟩
    · simp only [hcond, ↓reduceIte]
      refine ⟨⟨halloc, hzero, fun k hk_ge => by
        rw [Function.update_of_ne (by omega)]; exact hout k hk_ge, ?_,
        depth, hd0, hedge, hiff, hleaf⟩, trivial, trivial, rfl, fun id hnone => ?_⟩
      · intro k hk_lt
        by_cases heq : k = rKey
        · subst heq; simp [bufLookup, hw]
        · rw [Function.update_of_ne heq, hmap k hk_lt]
          dsimp only [bufLookup]
          cases hwk : bufWalk bChar tr.trieChild k cTab 0 0 with
          | none => rfl
          | some leaf_k =>
            simp only [Function.update_of_ne
              (bufWalk_root_ne_of_ne halloc hd0 hp_edge hiff hk_lt hk heq hwk hw)]
      · by_cases hid : id < tr.itemAlloc
        · simp only [bufCheckSlot, hid, ↓reduceIte] at hnone ⊢
          by_cases hleaf_eq : tr.itemLeaf id = leaf
          · simp [hleaf_eq]
          · simpa only [Function.update_of_ne hleaf_eq] using hnone
        · simp [bufCheckSlot, hid]

/-- Structural trie invariant bundled for internal maintenance across `bufEnsurePath` and
`bufInsert`. -/
private structure BufTrieInv (cTab bChar : ℕ) (tr : BufTrie) (depth : ℕ → ℕ) : Prop where
  alloc : 1 ≤ tr.nodeAlloc
  zero : ∀ u, tr.nodeAlloc ≤ u → tr.nodeLeafItem u = 0
  d0 : depth 0 = 0
  edge : ∀ u, 1 ≤ u → u < tr.nodeAlloc →
    tr.nodeParent u < u ∧ tr.nodeChar u < 2 ^ bChar ∧
    depth u = depth (tr.nodeParent u) + 1 ∧ depth u ≤ cTab ∧
    tr.trieChild (tr.nodeParent u) (tr.nodeChar u) = u
  iff : ∀ v ch, tr.trieChild v ch ≠ 0 ↔
    (1 ≤ tr.trieChild v ch ∧ tr.trieChild v ch < tr.nodeAlloc ∧
     tr.nodeParent (tr.trieChild v ch) = v ∧ tr.nodeChar (tr.trieChild v ch) = ch)
  leaf : ∀ u < tr.nodeAlloc, tr.nodeLeafItem u ≠ 0 →
    depth u = cTab ∧ tr.nodeLeafItem u ≤ tr.itemAlloc ∧
    tr.itemLeaf (tr.nodeLeafItem u - 1) = u ∧
    ∃ k < 2 ^ (cTab * bChar), bufWalk bChar tr.trieChild k cTab 0 0 = some u

private theorem BufTrieInv.child_lt {cTab bChar : ℕ} {tr : BufTrie} {depth : ℕ → ℕ}
    (hinv : BufTrieInv cTab bChar tr depth) (v c : ℕ) (hnz : tr.trieChild v c ≠ 0) :
    v < tr.trieChild v c := by
  obtain ⟨h1, h2, h3, _⟩ := (hinv.iff v c).mp hnz
  have := (hinv.edge _ h1 h2).1
  omega

/-- Allocating one fresh trie node at `u := tr.nodeAlloc` along an absent edge `(cur, ch)`
preserves `BufTrieInv` and all existing non-zero child pointers. -/
private theorem BufTrieInv.allocStep {cTab bChar cur ch off : ℕ} {tr : BufTrie} {depth : ℕ → ℕ}
    (hinv : BufTrieInv cTab bChar tr depth) (hcur : cur < tr.nodeAlloc) (hdep : depth cur = off)
    (hoff : off + 1 ≤ cTab) (h0 : tr.trieChild cur ch = 0) (hch : ch < 2 ^ bChar) :
    let u := tr.nodeAlloc
    let tr' : BufTrie :=
      { tr with
        nodeAlloc := u + 1
        trieChild := Function.update tr.trieChild cur (Function.update (tr.trieChild cur) ch u)
        nodeParent := Function.update tr.nodeParent u cur
        nodeChar := Function.update tr.nodeChar u ch
        nodeLeafItem := Function.update tr.nodeLeafItem u 0 }
    let depth' := Function.update depth u (off + 1)
    BufTrieInv cTab bChar tr' depth' ∧
    (∀ v c, tr.trieChild v c ≠ 0 → tr'.trieChild v c = tr.trieChild v c) := by
  intro u tr' depth'
  have hmono : ∀ v c, tr.trieChild v c ≠ 0 → tr'.trieChild v c = tr.trieChild v c :=
    fun v c hnz => Function.update_update_apply_of_ne fun ⟨hv, hc⟩ => hnz (hv ▸ hc ▸ h0)
  refine ⟨⟨by dsimp [tr']; omega,
    fun w hw_ge => by
      dsimp only [tr'] at hw_ge ⊢
      rw [Function.update_of_ne (by omega)]; exact hinv.zero w (by omega),
    by
      dsimp only [depth']
      rw [Function.update_of_ne (by have := hinv.alloc; omega)]; exact hinv.d0,
    ?_, ?_, ?_⟩, hmono⟩
  · intro w hw1 hw_lt
    dsimp only [tr', depth'] at hw_lt ⊢
    by_cases hw_eq : w = u
    · subst hw_eq
      simp only [Function.update_self]
      rw [Function.update_of_ne (Nat.ne_of_lt hcur), hdep]
      exact ⟨hcur, hch, rfl, hoff, by simp⟩
    · obtain ⟨hp_lt, hc_lt, hd_eq, hd_le, hchild_eq⟩ := hinv.edge w hw1 (by omega)
      simp only [Function.update_of_ne hw_eq,
        Function.update_of_ne (by omega : tr.nodeParent w ≠ u)]
      exact ⟨hp_lt, hc_lt, hd_eq, hd_le,
        by change tr'.trieChild (tr.nodeParent w) (tr.nodeChar w) = w
           rw [hmono _ _ (by omega), hchild_eq]⟩
  · intro v c
    dsimp only [tr']
    by_cases hvc : v = cur ∧ c = ch
    · rcases hvc with ⟨rfl, rfl⟩
      simp only [Function.update_self]
      exact ⟨fun _ => ⟨hinv.alloc, by omega, trivial, trivial⟩,
        fun _ => by have := hinv.alloc; omega⟩
    · rw [Function.update_update_apply_of_ne hvc]
      refine ⟨fun hnz => ?_, fun ⟨h1, _⟩ => by omega⟩
      obtain ⟨h1, h2, h3, h4⟩ := (hinv.iff v c).mp hnz
      rw [Function.update_of_ne (by omega : tr.trieChild v c ≠ u),
        Function.update_of_ne (by omega : tr.trieChild v c ≠ u)]
      exact ⟨h1, by omega, h3, h4⟩
  · intro w hw_lt hnz
    dsimp only [tr', depth'] at hw_lt hnz ⊢
    have hw_ne_u : w ≠ u := fun heq => by subst heq; simp at hnz
    simp only [Function.update_of_ne hw_ne_u] at hnz ⊢
    obtain ⟨hd_w, hle_item, hil_w, k, hk_lt, hwk⟩ := hinv.leaf w (by omega) hnz
    exact ⟨hd_w, hle_item, hil_w, k, hk_lt, bufWalk_mono hmono cTab 0 0 w k hwk⟩

/-- Structural invariant preserved along `bufEnsurePath`. -/
private theorem bufEnsurePath_props {cTab bChar rKey : ℕ} :
    ∀ (rem off : ℕ) (tr : BufTrie) (cur : ℕ) (depth : ℕ → ℕ),
      off + rem = cTab →
      BufTrieInv cTab bChar tr depth →
      cur < tr.nodeAlloc →
      depth cur = off →
      let p := bufEnsurePath bChar rKey rem off tr cur
      let tr1 := p.1
      let leaf := p.2
      tr.nodeAlloc ≤ tr1.nodeAlloc ∧
      tr1.nodeAlloc ≤ tr.nodeAlloc + rem ∧
      tr1.itemAlloc = tr.itemAlloc ∧
      tr1.itemLeaf = tr.itemLeaf ∧
      tr1.itemBucket = tr.itemBucket ∧
      tr1.itemLoc = tr.itemLoc ∧
      tr1.nodeActive = tr.nodeActive ∧
      (∀ u < tr.nodeAlloc, tr1.nodeLeafItem u = tr.nodeLeafItem u) ∧
      (∀ u, tr.nodeAlloc ≤ u → tr1.nodeLeafItem u = 0) ∧
      (∀ v ch, tr.trieChild v ch ≠ 0 → tr1.trieChild v ch = tr.trieChild v ch) ∧
      (∀ v ch, tr1.trieChild v ch ≠ tr.trieChild v ch → tr.nodeAlloc ≤ tr1.trieChild v ch) ∧
      ((bufWalk bChar tr.trieChild rKey rem off cur = some leaf ∧ tr1 = tr) ∨
       (bufWalk bChar tr.trieChild rKey rem off cur = none ∧ tr.nodeAlloc ≤ leaf)) ∧
      leaf < tr1.nodeAlloc ∧
      bufWalk bChar tr1.trieChild rKey rem off cur = some leaf ∧
      ∃ depth1 : ℕ → ℕ,
        BufTrieInv cTab bChar tr1 depth1 ∧ depth1 leaf = cTab := by
  intro rem
  induction rem with
  | zero =>
    intro off tr cur depth hsum hinv hcur hdep
    dsimp only [bufEnsurePath]
    refine ⟨le_rfl, by omega, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, hinv.zero,
      fun _ _ _ => rfl, fun _ _ hne => absurd rfl hne,
      Or.inl ⟨by simp [bufWalk], rfl⟩, hcur, by simp [bufWalk], depth, hinv, by omega⟩
  | succ rem ih =>
    intro off tr cur depth hsum hinv hcur hdep
    dsimp only [bufEnsurePath]
    set ch := laneGet bChar rKey off
    set nxt := tr.trieChild cur ch
    by_cases h0 : nxt = 0
    · simp only [h0, ↓reduceIte]
      set u := tr.nodeAlloc
      obtain ⟨hinv_step, hmono_step⟩ :=
        hinv.allocStep hcur hdep (by omega) h0 (laneGet_lt bChar rKey off)
      set tr_step : BufTrie :=
        { tr with
          nodeAlloc := u + 1
          trieChild := Function.update tr.trieChild cur (Function.update (tr.trieChild cur) ch u)
          nodeParent := Function.update tr.nodeParent u cur
          nodeChar := Function.update tr.nodeChar u ch
          nodeLeafItem := Function.update tr.nodeLeafItem u 0 }
      set depth_step := Function.update depth u (off + 1)
      have hih := ih (off + 1) tr_step u depth_step (by omega) hinv_step
        (by dsimp [tr_step]; omega) (by dsimp [depth_step]; simp)
      dsimp only at hih ⊢
      rcases hih with ⟨ha_le, ha_ub, hia, hil, hib, hiloc, hact, hpres1, hz_ge1,
        hmono1, hnew1, _, hleaf_lt, hw_rem, depth1, hinv1, hd1_leaf⟩
      have hna_step : tr_step.nodeAlloc = u + 1 := rfl
      rw [hna_step] at ha_le ha_ub
      refine ⟨by omega, by omega, hia, hil, hib, hiloc, hact, ?_, ?_, ?_, ?_, ?_,
        hleaf_lt, ?_, depth1, hinv1, hd1_leaf⟩
      · intro w hw_lt
        rw [hpres1 w (by rw [hna_step]; omega)]
        dsimp [tr_step]; rw [Function.update_of_ne (by omega)]
      · intro w hw_ge
        by_cases hw_eq : w = u
        · subst hw_eq; rw [hpres1 u (by rw [hna_step]; omega)]; simp [tr_step]
        · exact hz_ge1 w (by rw [hna_step]; omega)
      · intro v c hnz
        rw [hmono1 v c (by rw [hmono_step v c hnz]; exact hnz), hmono_step v c hnz]
      · intro v c hne
        by_cases hne1 : (bufEnsurePath bChar rKey rem (off + 1) tr_step u).1.trieChild v c ≠
            tr_step.trieChild v c
        · have := hnew1 v c hne1; rw [hna_step] at this; omega
        · rw [not_ne_iff.mp hne1] at hne ⊢
          have hvc : v = cur ∧ c = ch :=
            by_contra fun hvc => hne (Function.update_update_apply_of_ne hvc)
          rcases hvc with ⟨rfl, rfl⟩; simp [tr_step]
      · exact Or.inr ⟨by simp [bufWalk, ch, nxt, h0],
          bufWalk_le_leaf hinv1.child_lt rem (off + 1) u _ rKey hw_rem⟩
      · have hu0 : u ≠ 0 := by have := hinv.alloc; omega
        have htr_ch : tr_step.trieChild cur ch = u := by simp [tr_step]
        simpa only [bufWalk, ch, hmono1 cur ch (htr_ch ▸ hu0), htr_ch, hu0, ↓reduceIte] using hw_rem
    · simp only [h0, ↓reduceIte]
      obtain ⟨h1_ge, h1_lt, hp1, _⟩ := (hinv.iff cur ch).mp h0
      rcases ih (off + 1) tr nxt depth (by omega) hinv h1_lt
          (by rw [(hinv.edge nxt h1_ge h1_lt).2.2.1, hp1, hdep]) with
        ⟨ha_le, ha_ub, hia, hil, hib, hiloc, hact, hpres1, hz_ge1,
         hmono1, hnew1, hwalk_or, hleaf_lt, hw_rem, depth1, hinv1, hd1_leaf⟩
      refine ⟨ha_le, by omega, hia, hil, hib, hiloc, hact, hpres1, hz_ge1, hmono1, hnew1, ?_,
        hleaf_lt, ?_, depth1, hinv1, hd1_leaf⟩
      · rcases hwalk_or with ⟨hw_ok, htr_eq⟩ | ⟨hw_none, hge_leaf⟩
        · exact Or.inl ⟨by simp [bufWalk, ch, nxt, h0, hw_ok], htr_eq⟩
        · exact Or.inr ⟨by simp [bufWalk, ch, nxt, h0, hw_none], hge_leaf⟩
      · simpa only [bufWalk, ch, nxt, hmono1 cur ch h0, h0, ↓reduceIte] using hw_rem

/-- Exact specification of `bufInsert`:
* Preserves `ValidBufTrie` for `Function.update mapFn rKey (some (b, loc))`;
* Allocates at most `cTab` trie nodes, increments `itemAlloc` by exactly `1` when
  `bufEverPresent cTab bChar tr rKey = false`, and leaves `itemAlloc` unchanged when
  `bufEverPresent cTab bChar tr rKey = true`;
* Sets `bufEverPresent` at `rKey` to `true` and preserves `bufEverPresent` on all other keys
  `< 2 ^ (cTab * bChar)`;
* Whenever `bufEverPresent cTab bChar tr rKey = true` (including re-insertion of a previously
  deleted key in the same epoch!), leaves `nodeAlloc` and `itemAlloc` completely unchanged;
* When `mapFn rKey ≠ none` (updating an active item's `(b, loc)` in place), also leaves inactive
  scan slots (`bufCheckSlot _ id = none`) unchanged. -/
theorem ValidBufTrie.insert_spec {cTab bChar rKey b loc : ℕ} {tr : BufTrie}
    {mapFn : ℕ → Option (ℕ × ℕ)} (hv : ValidBufTrie cTab bChar tr mapFn)
    (hk : rKey < 2 ^ (cTab * bChar)) :
    let tr' := bufInsert cTab bChar tr rKey b loc
    ValidBufTrie cTab bChar tr' (Function.update mapFn rKey (some (b, loc))) ∧
    tr.nodeAlloc ≤ tr'.nodeAlloc ∧
    tr'.nodeAlloc ≤ tr.nodeAlloc + cTab ∧
    tr'.itemAlloc =
      (if bufEverPresent cTab bChar tr rKey then tr.itemAlloc else tr.itemAlloc + 1) ∧
    (∀ k < 2 ^ (cTab * bChar),
      bufEverPresent cTab bChar tr' k =
        if k = rKey then true else bufEverPresent cTab bChar tr k) ∧
    (bufEverPresent cTab bChar tr rKey = true →
      tr'.nodeAlloc = tr.nodeAlloc ∧ tr'.itemAlloc = tr.itemAlloc) ∧
    (mapFn rKey ≠ none →
      tr'.nodeAlloc = tr.nodeAlloc ∧
      tr'.itemAlloc = tr.itemAlloc ∧
      ∀ id, bufCheckSlot tr id = none → bufCheckSlot tr' id = none) := by
  have ⟨halloc, hzero, hout, hmap, depth, hd0, hedge, hiff, hleaf⟩ := hv
  dsimp only [bufInsert]
  have hens := bufEnsurePath_props (cTab := cTab) (bChar := bChar) (rKey := rKey)
    cTab 0 tr 0 depth (Nat.zero_add cTab) ⟨halloc, hzero, hd0, hedge, hiff, hleaf⟩ halloc hd0
  dsimp only at hens
  generalize bufEnsurePath bChar rKey cTab 0 tr 0 = p at hens ⊢
  rcases p with ⟨tr1, leaf⟩
  dsimp only at hens ⊢
  rcases hens with ⟨ha_le, ha_ub, hia, hil, hib, hiloc, hact1, hpres1, hz_ge1,
    hmono1, hnew1, hwalk_or, hleaf_lt, hw_rKey, depth1, hinv1, hd1_leaf⟩
  have hp_edge1 : ∀ u, 1 ≤ u → u < tr1.nodeAlloc → depth1 u = depth1 (tr1.nodeParent u) + 1 :=
    fun u h1 h2 => (hinv1.edge u h1 h2).2.2.1
  by_cases hid1 : tr1.nodeLeafItem leaf = 0
  · simp only [hid1, ↓reduceIte]
    obtain ⟨hever_false, hmap_none⟩ :
        bufEverPresent cTab bChar tr rKey = false ∧ mapFn rKey = none := by
      rw [hmap rKey hk]
      rcases hwalk_or with ⟨hw_old, htr_eq⟩ | ⟨hw_none, _⟩
      · simp [bufEverPresent, bufLookup, hw_old, htr_eq ▸ hid1]
      · simp [bufEverPresent, bufLookup, hw_none]
    have hother : ∀ k < 2 ^ (cTab * bChar), k ≠ rKey →
        (∀ l, bufWalk bChar tr.trieChild k cTab 0 0 = some l →
          bufWalk bChar tr1.trieChild k cTab 0 0 = some l ∧ l < tr.nodeAlloc ∧ l ≠ leaf ∧
          Function.update tr1.nodeLeafItem leaf (tr1.itemAlloc + 1) l = tr.nodeLeafItem l) ∧
        (bufWalk bChar tr.trieChild k cTab 0 0 = none →
          ∀ l, bufWalk bChar tr1.trieChild k cTab 0 0 = some l →
            Function.update tr1.nodeLeafItem leaf (tr1.itemAlloc + 1) l = 0) := by
      intro k hk_lt heq
      refine ⟨fun l hwk_old => ?_, fun hwk_old l hwk1 => ?_⟩
      · have hwk1 := bufWalk_mono hmono1 cTab 0 0 l k hwk_old
        have hne_leaf := bufWalk_root_ne_of_ne hinv1.alloc hinv1.d0 hp_edge1 hinv1.iff
          hk_lt hk heq hwk1 hw_rKey
        have hlk_lt := (bufWalk_props (fun u h1 h2 => (hedge u h1 h2).2.2.1) hiff
          cTab 0 0 l k halloc hd0 hwk_old).1
        exact ⟨hwk1, hlk_lt, hne_leaf, by rw [Function.update_of_ne hne_leaf, hpres1 l hlk_lt]⟩
      · have hne_leaf := bufWalk_root_ne_of_ne hinv1.alloc hinv1.d0 hp_edge1 hinv1.iff
          hk_lt hk heq hwk1 hw_rKey
        have hge_old := bufWalk_ge_of_none hnew1 hinv1.child_lt cTab 0 0 l k hwk_old hwk1
        rw [Function.update_of_ne hne_leaf, hz_ge1 l hge_old]
    refine ⟨?_, ha_le, ha_ub, by simp [hever_false, hia], ?_,
      fun hev => absurd hev (by rw [hever_false]; decide), fun hne => absurd hmap_none hne⟩
    · refine ⟨by dsimp; have := hinv1.alloc; omega,
        fun u hu_ge => by
          dsimp at hu_ge ⊢; rw [Function.update_of_ne (by omega)]; exact hinv1.zero u hu_ge,
        fun k hk_ge => by rw [Function.update_of_ne (by omega)]; exact hout k hk_ge,
        ?_, depth1, hinv1.d0, hinv1.edge, hinv1.iff, ?_⟩
      · intro k hk_lt
        by_cases heq : k = rKey
        · subst heq; simp [bufLookup, hw_rKey]
        · rw [Function.update_of_ne heq, hmap k hk_lt]
          dsimp only [bufLookup]
          have ⟨hsome, hnone⟩ := hother k hk_lt heq
          cases hwk_old : bufWalk bChar tr.trieChild k cTab 0 0 with
          | some leaf_k =>
            obtain ⟨hwk1, hlk_lt, hne_leaf, hli_eq⟩ := hsome leaf_k hwk_old
            rw [hwk1]; simp only [hli_eq, Function.update_of_ne hne_leaf, hact1]
            by_cases hcond_k : tr.nodeLeafItem leaf_k = 0 ∨ tr.nodeActive leaf_k = 0
            · simp [hcond_k]
            · simp only [hcond_k, ↓reduceIte]; push Not at hcond_k
              have hle_ia := (hleaf leaf_k hlk_lt hcond_k.1).2.1
              have hid_ne : tr.nodeLeafItem leaf_k - 1 ≠ tr1.itemAlloc := by omega
              simp only [Function.update_of_ne hid_ne, hib, hiloc]
          | none =>
            cases hwk1 : bufWalk bChar tr1.trieChild k cTab 0 0 with
            | none => rfl
            | some leaf_k => simp [hnone hwk_old leaf_k hwk1]
      · intro u hu_lt hnz'
        dsimp only at hu_lt hnz' ⊢
        by_cases hu_eq : u = leaf
        · subst hu_eq; simp only [Function.update_self, Nat.add_sub_cancel]
          exact ⟨hd1_leaf, le_rfl, trivial, rKey, hk, hw_rKey⟩
        · rw [Function.update_of_ne hu_eq] at hnz' ⊢
          obtain ⟨hd_u, hle_u, hil_u, k, hk_lt, hwk⟩ := hinv1.leaf u hu_lt hnz'
          exact ⟨hd_u, by omega,
            by rw [Function.update_of_ne (by omega : tr1.nodeLeafItem u - 1 ≠ tr1.itemAlloc),
              hil_u], k, hk_lt, hwk⟩
    · intro k hk_lt
      by_cases heq : k = rKey
      · subst heq; simp [bufEverPresent, hw_rKey]
      · simp only [heq, ↓reduceIte, bufEverPresent]
        have ⟨hsome, hnone⟩ := hother k hk_lt heq
        cases hwk_old : bufWalk bChar tr.trieChild k cTab 0 0 with
        | some leaf_k =>
          obtain ⟨hwk1, _, _, hli_eq⟩ := hsome leaf_k hwk_old
          rw [hwk1]; simp [hli_eq]
        | none =>
          cases hwk1 : bufWalk bChar tr1.trieChild k cTab 0 0 with
          | none => rfl
          | some leaf_k => simp [hnone hwk_old leaf_k hwk1]
  · simp only [hid1, ↓reduceIte]
    have htr1_eq : tr1 = tr := by
      rcases hwalk_or with ⟨_, htr_eq⟩ | ⟨_, hge_leaf⟩
      · exact htr_eq
      · exact absurd (hz_ge1 leaf hge_leaf) hid1
    obtain ⟨_, _, hil_leaf, _⟩ := hinv1.leaf leaf hleaf_lt hid1
    have hever_true : bufEverPresent cTab bChar tr rKey = true := by
      rw [← htr1_eq]; simp [bufEverPresent, hw_rKey, hid1]
    refine ⟨?_, ha_le, ha_ub, by simp [hever_true, hia], ?_,
      fun _ => ⟨by rw [htr1_eq], hia⟩, fun hmap_ne => ?_⟩
    · refine ⟨by dsimp; exact hinv1.alloc, hinv1.zero,
        fun k hk_ge => by rw [Function.update_of_ne (by omega)]; exact hout k hk_ge,
        ?_, depth1, hinv1.d0, hinv1.edge, hinv1.iff, hinv1.leaf⟩
      intro k hk_lt
      by_cases heq : k = rKey
      · subst heq; simp [bufLookup, hw_rKey, hid1]
      · rw [Function.update_of_ne heq, hmap k hk_lt, ← htr1_eq]; dsimp only [bufLookup]
        cases hwk1 : bufWalk bChar tr1.trieChild k cTab 0 0 with
        | none => rfl
        | some leaf_k =>
          have hne_leaf := bufWalk_root_ne_of_ne hinv1.alloc hinv1.d0 hp_edge1 hinv1.iff
            hk_lt hk heq hwk1 hw_rKey
          dsimp only; simp only [Function.update_of_ne hne_leaf]
          by_cases hcond_k : tr1.nodeLeafItem leaf_k = 0 ∨ tr1.nodeActive leaf_k = 0
          · simp [hcond_k]
          · simp only [hcond_k, ↓reduceIte]; push Not at hcond_k
            have hlk_lt := (bufWalk_props hp_edge1 hinv1.iff cTab 0 0 leaf_k k
              hinv1.alloc hinv1.d0 hwk1).1
            have hil_k := (hinv1.leaf leaf_k hlk_lt hcond_k.1).2.2.1
            simp only [Function.update_of_ne (fun heq_id =>
              hne_leaf (by rw [← hil_k, heq_id, hil_leaf]) :
              tr1.nodeLeafItem leaf_k - 1 ≠ tr1.nodeLeafItem leaf - 1)]
    · intro k _
      by_cases heq : k = rKey
      · simp [heq, bufEverPresent, hw_rKey, hid1]
      · rw [ite_eq_right heq, ← htr1_eq]
        rfl
    · have hact_nz : tr1.nodeActive leaf ≠ 0 := fun hact0 =>
        hmap_ne (by rw [hmap rKey hk, ← htr1_eq]; simp [bufLookup, hw_rKey, hact0])
      refine ⟨congrArg BufTrie.nodeAlloc htr1_eq, hia, fun id hnone => ?_⟩
      by_cases hid : id < tr.itemAlloc
      · rw [← htr1_eq] at hnone
        simp only [bufCheckSlot, hia, hid, ↓reduceIte] at hnone ⊢
        by_cases hleaf_eq : tr1.itemLeaf id = leaf
        · rw [hleaf_eq] at hnone ⊢
          simp only [Function.update_self]
          by_cases hli_eq : tr1.nodeLeafItem leaf = id + 1
          · simp [hli_eq, hact_nz] at hnone
          · simp [hli_eq]
        · have hid_ne : id ≠ tr1.nodeLeafItem leaf - 1 := fun h => hleaf_eq (h ▸ hil_leaf)
          simpa only [Function.update_of_ne hleaf_eq, Function.update_of_ne hid_ne] using hnone
      · simp [bufCheckSlot, hia, hid]

/-- Forward scan specification: if `bufCheckSlot tr id = some (b, loc)`, then `id < tr.itemAlloc`
and some active key `k < 2 ^ (cTab * bChar)` maps to `(b, loc)` in `mapFn` (with leaf
`tr.itemLeaf id`). -/
theorem ValidBufTrie.checkSlot_some {cTab bChar id b loc : ℕ} {tr : BufTrie}
    {mapFn : ℕ → Option (ℕ × ℕ)} (hv : ValidBufTrie cTab bChar tr mapFn)
    (hchk : bufCheckSlot tr id = some (b, loc)) :
    id < tr.itemAlloc ∧
    ∃ k < 2 ^ (cTab * bChar),
      bufWalk bChar tr.trieChild k cTab 0 0 = some (tr.itemLeaf id) ∧
      mapFn k = some (b, loc) := by
  obtain ⟨_, hzero, _, hmap, _, _, _, _, hleaf⟩ := hv
  dsimp only [bufCheckSlot] at hchk
  split at hchk
  · rename_i hid
    set leaf := tr.itemLeaf id
    split at hchk
    · rename_i hcond
      obtain ⟨hli, hact⟩ := hcond
      simp only [Option.some.injEq, Prod.mk.injEq] at hchk
      have hleaf_lt : leaf < tr.nodeAlloc :=
        Nat.lt_of_not_ge fun hge => by have := hzero leaf hge; omega
      obtain ⟨_, _, _, k, hk_lt, hwk⟩ := hleaf leaf hleaf_lt (by omega)
      exact ⟨hid, k, hk_lt, hwk, by rw [hmap k hk_lt]; simp [bufLookup, hwk, hli, hact, hchk]⟩
    · cases hchk
  · cases hchk

/-- Converse scan specification: every active key `mapFn k = some (b, loc)` has an active scan slot
`id < tr.itemAlloc` with `bufCheckSlot tr id = some (b, loc)`. In particular, once
`∀ id < tr.itemAlloc, bufCheckSlot tr id = none`, `mapFn` is identically `none`. -/
theorem ValidBufTrie.exists_checkSlot_of_map_some {cTab bChar k b loc : ℕ} {tr : BufTrie}
    {mapFn : ℕ → Option (ℕ × ℕ)} (hv : ValidBufTrie cTab bChar tr mapFn)
    (hmk : mapFn k = some (b, loc)) :
    ∃ id < tr.itemAlloc, bufCheckSlot tr id = some (b, loc) := by
  obtain ⟨halloc, _, hout, hmap, depth, hd0, hedge, hiff, hleaf⟩ := hv
  have hk_lt : k < 2 ^ (cTab * bChar) :=
    Nat.lt_of_not_ge fun hge => by simp [hout k hge] at hmk
  rw [hmap k hk_lt] at hmk
  dsimp only [bufLookup] at hmk
  split at hmk
  · cases hmk
  · rename_i leaf hwk
    split_ifs at hmk with hcond
    push Not at hcond
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hmk).symm
    have hleaf_lt := (bufWalk_props (fun u h1 h2 => (hedge u h1 h2).2.2.1) hiff
      cTab 0 0 leaf k halloc hd0 hwk).1
    obtain ⟨_, hle_ia, hil_eq, _⟩ := hleaf leaf hleaf_lt hcond.1
    refine ⟨tr.nodeLeafItem leaf - 1, by omega, ?_⟩
    simp [bufCheckSlot, show tr.nodeLeafItem leaf - 1 < tr.itemAlloc by omega, hil_eq,
      Nat.sub_add_cancel (Nat.pos_of_ne_zero hcond.1), hcond.2]

/-! ## Section 3: Incremental single-pop cleanup (`ClearableBufTrie`, `clearSteps_spec`) -/

/-- Structural parent-log invariant maintained across intermediate `bufClearOne` steps while
re-zeroing `BufOld` in the second half of an epoch. -/
def ClearableBufTrie (tr : BufTrie) : Prop :=
  1 ≤ tr.nodeAlloc ∧
  (∀ u, tr.nodeAlloc ≤ u → tr.nodeLeafItem u = 0) ∧
  (∀ u, 1 ≤ u → u < tr.nodeAlloc →
    tr.nodeParent u < u ∧ tr.trieChild (tr.nodeParent u) (tr.nodeChar u) = u) ∧
  (∀ v ch, tr.trieChild v ch ≠ 0 →
    1 ≤ tr.trieChild v ch ∧ tr.trieChild v ch < tr.nodeAlloc ∧
    tr.nodeParent (tr.trieChild v ch) = v ∧ tr.nodeChar (tr.trieChild v ch) = ch)

/-- Every `ValidBufTrie` satisfies `ClearableBufTrie`. -/
theorem ValidBufTrie.toClearable {cTab bChar : ℕ} {tr : BufTrie}
    {mapFn : ℕ → Option (ℕ × ℕ)} (hv : ValidBufTrie cTab bChar tr mapFn) :
    ClearableBufTrie tr := by
  obtain ⟨halloc, hzero, _, _, _, _, hedge, hiff, _⟩ := hv
  exact ⟨halloc, hzero, fun u h1 h2 => ⟨(hedge u h1 h2).1, (hedge u h1 h2).2.2.2.2⟩,
    fun v ch hnz => (hiff v ch).mp hnz⟩

/-- Allocation and parent-index projections of `ClearableBufTrie` for Word-RAM packed-array
safety. -/
theorem ClearableBufTrie.bounds {tr : BufTrie} (hc : ClearableBufTrie tr) :
    1 ≤ tr.nodeAlloc ∧
    (∀ u, 1 ≤ u → u < tr.nodeAlloc → tr.nodeParent u < u) := by
  obtain ⟨halloc, _, hedge, _⟩ := hc
  exact ⟨halloc, fun u h1 h2 => (hedge u h1 h2).1⟩

/-- One step of `bufClearOne` preserves `ClearableBufTrie` and decrements `nodeAlloc` toward `1`. -/
theorem ClearableBufTrie.clearOne_step {tr : BufTrie} (hc : ClearableBufTrie tr) :
    ClearableBufTrie (bufClearOne tr) ∧
    (bufClearOne tr).nodeAlloc = max 1 (tr.nodeAlloc - 1) := by
  obtain ⟨halloc, hzero, hedge, hchild⟩ := hc
  dsimp only [bufClearOne]
  by_cases hgt : 1 < tr.nodeAlloc
  · simp only [hgt, ↓reduceIte]
    set u := tr.nodeAlloc - 1; set p := tr.nodeParent u; set ch := tr.nodeChar u
    refine ⟨⟨by dsimp; omega, fun w hw_ge => by
        dsimp only at hw_ge ⊢
        by_cases hw_eq : w = u
        · subst hw_eq; simp
        · rw [Function.update_of_ne hw_eq]; exact hzero w (by omega),
      fun w hw1 hw_lt => by
        dsimp only at hw_lt ⊢
        obtain ⟨hp_w, hc_w⟩ := hedge w hw1 (by omega)
        refine ⟨hp_w, ?_⟩
        by_cases hvc : tr.nodeParent w = p ∧ tr.nodeChar w = ch
        · have : w = u := by rw [← hc_w, hvc.1, hvc.2, (hedge u (by omega) (by omega)).2]
          omega
        · rw [Function.update_update_apply_of_ne hvc, hc_w],
      fun v c hnz => by
        dsimp only at hnz ⊢
        by_cases hvc : v = p ∧ c = ch
        · rcases hvc with ⟨rfl, rfl⟩; simp at hnz
        · rw [Function.update_update_apply_of_ne hvc] at hnz ⊢
          obtain ⟨h1, h2, h3, h4⟩ := hchild v c hnz
          have hne_u : tr.trieChild v c ≠ u := fun heq => hvc ⟨h3 ▸ heq ▸ rfl, h4 ▸ heq ▸ rfl⟩
          exact ⟨h1, by omega, h3, h4⟩⟩, by omega⟩
  · simp only [hgt, ↓reduceIte]
    refine ⟨⟨le_rfl, fun w hw_ge => by
      dsimp only at hw_ge ⊢; rw [Function.update_of_ne (by omega)]; exact hzero w (by omega),
      fun _ _ h2 => by dsimp only at h2; omega,
      fun v c hnz => by
        dsimp only at hnz ⊢; obtain ⟨h1, h2, _⟩ := hchild v c hnz; omega⟩, by omega⟩

/-- When `ClearableBufTrie tr` holds with `tr.nodeAlloc = 1`, one final `bufClearOne` step yields a
completely clean `ValidBufTrie cTab bChar _ (fun _ => none)` with `nodeAlloc = 1` and
`itemAlloc = 0`. -/
private theorem ClearableBufTrie.clearOne_of_one (cTab bChar : ℕ) {tr : BufTrie}
    (hc : ClearableBufTrie tr) (ha1 : tr.nodeAlloc = 1) :
    let tr' := bufClearOne tr
    ValidBufTrie cTab bChar tr' (fun _ => none) ∧
    tr'.nodeAlloc = 1 ∧
    tr'.itemAlloc = 0 := by
  obtain ⟨_, hzero, _, hchild⟩ := hc
  have hchild0 : ∀ v c, tr.trieChild v c = 0 := fun v c => by_contra fun hnz => by
    obtain ⟨h1, h2, _⟩ := hchild v c hnz; omega
  dsimp only [bufClearOne]
  simp only [show ¬ (1 < tr.nodeAlloc) by omega, ↓reduceIte]
  have hz_all (w : ℕ) : Function.update tr.nodeLeafItem 0 0 w = 0 :=
    if hw0 : w = 0 then by simp [hw0]
    else (Function.update_of_ne hw0 0 tr.nodeLeafItem).trans (hzero w (by omega))
  refine ⟨⟨le_rfl, fun w _ => hz_all w, fun _ _ => rfl, fun k _ => ?_, fun _ => 0, rfl,
    fun _ _ h2 => by dsimp only at h2; omega,
    fun v ch => by simp [hchild0 v ch],
    fun u _ hnz => absurd (hz_all u) hnz⟩, trivial, trivial⟩
  cases cTab <;> simp [bufLookup, bufWalk, hchild0]

/-- Executing `k ≥ tr.nodeAlloc` elementary `bufClearOne` steps on any `ClearableBufTrie` produces a
clean empty `ValidBufTrie` (`mapFn = fun _ => none`, `nodeAlloc = 1`, `itemAlloc = 0`). -/
theorem ClearableBufTrie.clearSteps_spec (cTab bChar : ℕ) :
    ∀ (k : ℕ) {tr : BufTrie},
      ClearableBufTrie tr →
      tr.nodeAlloc ≤ k →
      let tr' := bufClearSteps k tr
      ValidBufTrie cTab bChar tr' (fun _ => none) ∧
      tr'.nodeAlloc = 1 ∧
      tr'.itemAlloc = 0 := by
  intro k
  induction k with
  | zero => intro tr hc hle; have := hc.1; omega
  | succ k ih =>
    intro tr hc hle
    dsimp only [bufClearSteps]
    by_cases ha1 : tr.nodeAlloc = 1
    · obtain ⟨hv1, ha1', hi0'⟩ := hc.clearOne_of_one cTab bChar ha1
      rcases k with _ | k
      · exact ⟨hv1, ha1', hi0'⟩
      · exact ih hv1.toClearable (by omega)
    · obtain ⟨hc1, ha_nxt⟩ := hc.clearOne_step
      exact ih hc1 (by have := hc.1; omega)

/-- `bufInsert` preserves the linear bound `nodeAlloc ≤ 1 + cTab * itemAlloc` across all
insertions, overwrites, and reactivations. -/
theorem ValidBufTrie.insert_nodeAlloc_le {cTab bChar rKey b loc : ℕ} {tr : BufTrie}
    {mapFn : ℕ → Option (ℕ × ℕ)} (hv : ValidBufTrie cTab bChar tr mapFn)
    (hk : rKey < 2 ^ (cTab * bChar)) (hlin : tr.nodeAlloc ≤ 1 + cTab * tr.itemAlloc) :
    let tr' := bufInsert cTab bChar tr rKey b loc
    tr'.nodeAlloc ≤ 1 + cTab * tr'.itemAlloc := by
  dsimp only
  obtain ⟨_, _, ha_ub, hia, _, hreuse, _⟩ := hv.insert_spec (b := b) (loc := loc) hk
  by_cases hev : bufEverPresent cTab bChar tr rKey = true
  · obtain ⟨ha_eq, hia_eq⟩ := hreuse hev; rw [ha_eq, hia_eq]; exact hlin
  · simp only [hev, Bool.false_eq_true, ↓reduceIte] at hia
    rw [hia, Nat.mul_add, Nat.mul_one]
    omega

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
