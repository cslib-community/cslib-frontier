/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Memory.Copy
public import CslibFrontier.DataStructure.Memory.Frame
public import CslibFrontier.DataStructure.Memory.Triple
public import Mathlib.Order.Interval.Set.Basic
import CslibFrontier.Tactic.WramOmega

/-!
# Framed correctness-and-cost triples and block framing over memory

This module extends `Cslib.DataStructure.Memory.Triple` with non-overlapping block copy
(`Triple.copy`), introduces the explicit modification-set framing predicate `Memory.Modifies`,
packages framed triples as `FramedTriple` with generic heap-frame preservation
(`FramedTriple.frame`, `FramedTriple.frame_mem`, `FramedTriple.mem_eq_of_frontier_eq`), and
provides `Cslib.WordRAM.Block` disjointness, strided slot framing (`Block.slot`), and consecutive
list-write initialization (`Block.writeList`).

## Main definitions

* `Cslib.DataStructure.Memory.Modifies`: frontier-monotone frame protecting allocated cells outside
  a set `S`.
* `Cslib.DataStructure.Memory.FramedTriple`: `Triple` bundled with `Memory.Modifies S s s'`.
* `Cslib.WordRAM.Block.Disjoint`: address-disjointness of two memory blocks.
* `Cslib.WordRAM.Block.slot`: strided record-array slice at `base + stride * idx`.
* `Cslib.WordRAM.Block.writeList`: write a list of words consecutively starting at `base`.

## Main results

* `Cslib.DataStructure.Memory.Triple.copy`: triple specification for `Memory.copy`.
* `Cslib.DataStructure.Memory.FramedTriple.frame`,
  `Cslib.DataStructure.Memory.FramedTriple.frame_mem`, and
  `Cslib.DataStructure.Memory.FramedTriple.mem_eq_of_frontier_eq`: automatic preservation of heap
  predicates depending only on allocated cells disjoint from `S`, and full-memory frame extraction
  when the frontier is unchanged.
* `Cslib.WordRAM.Block.slot_disjoint_of_ne`: distinct indices of a strided array are disjoint.
* `Cslib.WordRAM.Block.framedTriple_writeList`: admissibility, cost, frame, readback, and
  well-formedness preservation for `Block.writeList`.
-/

@[expose] public section

namespace Cslib.DataStructure.Memory

open Cslib.WordRAM

variable {w : ℕ} {α β : Type}

/-! ## Non-overlapping copy triple -/

/-- Non-overlapping block copy triple: copies `n` words at cost `2 * n`. -/
theorem Triple.copy {s : State} {src dst n : ℕ} (hdisj : src + n ≤ dst ∨ dst + n ≤ src)
    (hsrc : src + n ≤ s.frontier) (hdst : dst + n ≤ s.frontier)
    (hfit : ∀ i < n, Fits w (s.mem (src + i)))
    {Q : Unit → State → Prop}
    (hQ : Q () ⟨Cslib.WordRAM.ArrayCopy.copyPrefix s.mem src dst n, s.frontier⟩) :
    Triple w s (Memory.copy src dst n) (2 * n) Q := by
  refine triple_iff.mpr ⟨validHistory_copy src dst n s hdisj hsrc hdst hfit,
    (totalCost_copy src dst n s).le, ?_⟩
  rw [show (spec w).clientResult s (Memory.copy src dst n) = () from rfl,
    clientState_copy src dst n s hdisj]
  exact hQ

/-! ## Modification-set framing predicate -/

/-- Transition from `s` to `s'` preserves the frontier's monotonicity and leaves all cells below
`s.frontier` outside `S` unchanged. -/
protected def Modifies (S : Set ℕ) (s s' : State) : Prop :=
  s.frontier ≤ s'.frontier ∧ ∀ a < s.frontier, a ∉ S → s'.mem a = s.mem a

namespace Modifies

/-- Reflexivity of `Memory.Modifies`. -/
theorem refl (S : Set ℕ) (s : State) : Memory.Modifies S s s :=
  ⟨le_rfl, fun _ _ _ => rfl⟩

/-- Transitivity of `Memory.Modifies` over a fixed set `S`. -/
theorem trans {S : Set ℕ} {s₁ s₂ s₃ : State} (h₁ : Memory.Modifies S s₁ s₂)
    (h₂ : Memory.Modifies S s₂ s₃) : Memory.Modifies S s₁ s₃ :=
  ⟨h₁.1.trans h₂.1, fun a ha haS =>
    (h₂.2 a (lt_of_lt_of_le ha h₁.1) haS).trans (h₁.2 a ha haS)⟩

/-- Sequential composition of `Memory.Modifies` across different sets takes their union. -/
theorem union {S₁ S₂ : Set ℕ} {s₁ s₂ s₃ : State}
    (h₁ : Memory.Modifies S₁ s₁ s₂) (h₂ : Memory.Modifies S₂ s₂ s₃) :
    Memory.Modifies (S₁ ∪ S₂) s₁ s₃ :=
  ⟨h₁.1.trans h₂.1, fun a ha haU =>
    (h₂.2 a (lt_of_lt_of_le ha h₁.1) fun h2 => haU (Or.inr h2)).trans
      (h₁.2 a ha fun h1 => haU (Or.inl h1))⟩

/-- Enlarging the permitted modification set weakens `Memory.Modifies`. -/
theorem mono {S₁ S₂ : Set ℕ} {s s' : State} (hsub : S₁ ⊆ S₂) (h : Memory.Modifies S₁ s s') :
    Memory.Modifies S₂ s s' :=
  ⟨h.1, fun a ha haS₂ => h.2 a ha fun haS₁ => haS₂ (hsub haS₁)⟩

/-- Writing cell `a` modifies at most `{a}`. -/
theorem write (s : State) (a v : ℕ) :
    Memory.Modifies {a} s ⟨Function.update s.mem a v, s.frontier⟩ :=
  ⟨le_rfl, fun b _ hb => Function.update_of_ne (by simpa using hb) v s.mem⟩

/-- Writing entry `i < b.length` of `b` modifies at most `Set.Ico b.base (b.base + b.length)`. -/
theorem set (s : State) (b : Block) {i : ℕ} (hi : i < b.length) (v : ℕ) :
    Memory.Modifies (Set.Ico b.base (b.base + b.length)) s
      ⟨Function.update s.mem (b.base + i) v, s.frontier⟩ :=
  (write s (b.base + i) v).mono fun _ ha => by
    have he : _ = b.base + i := ha
    subst he
    exact ⟨Nat.le_add_right _ _, by omega⟩

/-- Zeroed allocation modifies no cell below the old frontier. -/
theorem alloc (s : State) (k : ℕ) :
    Memory.Modifies ∅ s ⟨clear s.mem s.frontier k, s.frontier + k⟩ :=
  ⟨Nat.le_add_right _ _, fun _ ha _ => clear_of_not_owns (by wram_omega)⟩

/-- Dirty allocation modifies no cell below the old frontier. -/
theorem allocDirty (s : State) (k : ℕ) : Memory.Modifies ∅ s ⟨s.mem, s.frontier + k⟩ :=
  ⟨Nat.le_add_right _ _, fun _ _ _ => rfl⟩

/-- An allocated cell outside `S` retains its value. -/
theorem mem_eq_of_not_mem {S : Set ℕ} {s s' : State} (h : Memory.Modifies S s s') {a : ℕ}
    (ha : a < s.frontier) (haS : a ∉ S) : s'.mem a = s.mem a :=
  h.2 a ha haS

/-- Every allocated cell in a region `D` disjoint from `S` retains its value. -/
theorem mem_eq_of_disjoint {S D : Set ℕ} {s s' : State} (h : Memory.Modifies S s s')
    (hdisj : Disjoint S D) {a : ℕ} (ha : a < s.frontier) (haD : a ∈ D) :
    s'.mem a = s.mem a :=
  h.2 a ha (Set.disjoint_right.mp hdisj haD)

end Modifies

/-! ## Framed triples -/

/-- A `Triple` bundled with `Memory.Modifies S s s'` for automatic frame preservation. -/
abbrev FramedTriple (w : ℕ) (s : State) (p : Prog α) (c : ℕ) (S : Set ℕ)
    (Q : α → State → Prop) : Prop :=
  Triple w s p c fun a s' => Memory.Modifies S s s' ∧ Q a s'

/-- Unfold `FramedTriple` along the unique run of `p`. -/
theorem framedTriple_iff {s : State} {p : Prog α} {c : ℕ} {S : Set ℕ} {Q : α → State → Prop} :
    FramedTriple w s p c S Q ↔
      (spec w).ValidHistory s ((spec w).clientHistory s p) ∧
      (spec w).totalCost charge s ((spec w).clientHistory s p) ≤ c ∧
      Memory.Modifies S s ((spec w).clientState s p) ∧
      Q ((spec w).clientResult s p) ((spec w).clientState s p) := by
  rw [FramedTriple, triple_iff]

namespace FramedTriple

variable {s : State} {c c' : ℕ} {S S' : Set ℕ}

/-- Extract the underlying `Triple` (forgetting framing). -/
theorem triple {Q : α → State → Prop} {p : Prog α} (h : FramedTriple w s p c S Q) :
    Triple w s p c Q :=
  Triple.mono h le_rfl fun _ _ hq => hq.2

/-- Extract admissibility of the run. -/
theorem validHistory {Q : α → State → Prop} {p : Prog α} (h : FramedTriple w s p c S Q) :
    (spec w).ValidHistory s ((spec w).clientHistory s p) :=
  (framedTriple_iff.mp h).1

/-- Extract the cost bound. -/
theorem cost_le {Q : α → State → Prop} {p : Prog α} (h : FramedTriple w s p c S Q) :
    (spec w).totalCost charge s ((spec w).clientHistory s p) ≤ c :=
  (framedTriple_iff.mp h).2.1

/-- Extract frontier monotonicity. -/
theorem frontier_le {Q : α → State → Prop} {p : Prog α} (h : FramedTriple w s p c S Q) :
    s.frontier ≤ ((spec w).clientState s p).frontier :=
  (framedTriple_iff.mp h).2.2.1.1

/-- Extract the `Memory.Modifies` frame guarantee. -/
theorem modifies {Q : α → State → Prop} {p : Prog α} (h : FramedTriple w s p c S Q) :
    Memory.Modifies S s ((spec w).clientState s p) :=
  (framedTriple_iff.mp h).2.2.1

/-- Extract the postcondition. -/
theorem post {Q : α → State → Prop} {p : Prog α} (h : FramedTriple w s p c S Q) :
    Q ((spec w).clientResult s p) ((spec w).clientState s p) :=
  (framedTriple_iff.mp h).2.2.2

/-- If a framed run does not advance the frontier, every cell outside `S` retains its initial
value, including cells at or above `s.frontier`. -/
theorem mem_eq_of_frontier_eq {Q : α → State → Prop} {p : Prog α}
    (h : FramedTriple w s p c S Q)
    (hfr : ((spec w).clientState s p).frontier = s.frontier) :
    ∀ a, a ∉ S → ((spec w).clientState s p).mem a = s.mem a := by
  intro a haS
  by_cases ha : a < s.frontier
  · exact h.modifies.mem_eq_of_not_mem ha haS
  · exact mem_clientState_of_frontier_le s p h.validHistory (hfr ▸ Nat.le_of_not_lt ha)

/-- Weaken the cost bound and postcondition. -/
theorem mono {Q Q' : α → State → Prop} {p : Prog α} (h : FramedTriple w s p c S Q)
    (hc : c ≤ c') (hQ : ∀ a s', Q a s' → Q' a s') : FramedTriple w s p c' S Q' :=
  Triple.mono h hc fun a s' ⟨hm, hq⟩ => ⟨hm, hQ a s' hq⟩

/-- Enlarge the permitted modification set. -/
theorem frame_mono {Q : α → State → Prop} {p : Prog α} (h : FramedTriple w s p c S Q)
    (hsub : S ⊆ S') : FramedTriple w s p c S' Q :=
  Triple.mono h le_rfl fun _ _ ⟨hm, hq⟩ => ⟨hm.mono hsub, hq⟩

/-- Returning a value costs nothing and modifies nothing. -/
theorem pure {Q : α → State → Prop} {a : α} (h : Q a s) : FramedTriple w s (Pure.pure a) c S Q :=
  Triple.pure ⟨Modifies.refl S s, h⟩

/-- Read an allocated cell, then continue. -/
theorem read_bind {Q : α → State → Prop} {a : ℕ} {k : ℕ → Prog α} (ha : a < s.frontier)
    (h : FramedTriple w s (k (s.mem a)) c S Q) :
    FramedTriple w s (Memory.read a >>= k) (c + 1) S Q :=
  Triple.read_bind ha h

/-- Read an allocated cell as a standalone framed program. -/
theorem read {Q : ℕ → State → Prop} {a : ℕ} (ha : a < s.frontier) (h : Q (s.mem a) s) :
    FramedTriple w s (Memory.read a) 1 S Q :=
  read_bind ha (pure h)

/-- Write a word to an allocated cell and continue, adding `{a}` to the modified set. -/
theorem write_bind {Q : α → State → Prop} {a v : ℕ} {k : Unit → Prog α} (ha : a < s.frontier)
    (hv : Fits w v) (h : FramedTriple w ⟨Function.update s.mem a v, s.frontier⟩ (k ()) c S Q) :
    FramedTriple w s (Memory.write a v >>= k) (c + 1) (insert a S) Q :=
  Triple.write_bind ha hv (Triple.mono h le_rfl fun _ _ ⟨hm, hq⟩ =>
    ⟨by rw [← Set.singleton_union]; exact (Modifies.write s a v).union hm, hq⟩)

/-- Write a word to an allocated cell already inside `S`, then continue. -/
theorem write_bind_of_mem {Q : α → State → Prop} {a v : ℕ} {k : Unit → Prog α}
    (ha : a < s.frontier) (hv : Fits w v) (haS : a ∈ S)
    (h : FramedTriple w ⟨Function.update s.mem a v, s.frontier⟩ (k ()) c S Q) :
    FramedTriple w s (Memory.write a v >>= k) (c + 1) S Q :=
  (write_bind ha hv h).frame_mono (Set.insert_subset_iff.mpr ⟨haS, Set.Subset.rfl⟩)

/-- Write a word to an allocated cell as a standalone framed program. -/
theorem write {Q : Unit → State → Prop} {a v : ℕ} (ha : a < s.frontier) (hv : Fits w v)
    (haS : a ∈ S) (h : Q () ⟨Function.update s.mem a v, s.frontier⟩) :
    FramedTriple w s (Memory.write a v) 1 S Q :=
  write_bind_of_mem ha hv haS (pure h)

/-- Allocate `k` zeroed cells at the frontier, then continue. -/
theorem alloc_bind {Q : α → State → Prop} {k : ℕ} {next : ℕ → Prog α}
    (hk : Fits w (s.frontier + k))
    (h : FramedTriple w ⟨clear s.mem s.frontier k, s.frontier + k⟩ (next s.frontier) c S Q) :
    FramedTriple w s (Memory.alloc k >>= next) (c + (k + 1)) S Q :=
  Triple.alloc_bind hk (Triple.mono h le_rfl fun _ _ ⟨hm, hq⟩ =>
    ⟨by rw [← Set.empty_union S]; exact (Modifies.alloc s k).union hm, hq⟩)

/-- Allocate `k` dirty cells at the frontier, then continue. -/
theorem allocDirty_bind {Q : α → State → Prop} {k : ℕ} {next : ℕ → Prog α}
    (hk : Fits w (s.frontier + k))
    (h : FramedTriple w ⟨s.mem, s.frontier + k⟩ (next s.frontier) c S Q) :
    FramedTriple w s (Memory.allocDirty k >>= next) (c + 1) S Q :=
  Triple.allocDirty_bind hk (Triple.mono h le_rfl fun _ _ ⟨hm, hq⟩ =>
    ⟨by rw [← Set.empty_union S]; exact (Modifies.allocDirty s k).union hm, hq⟩)

/-- Allocate a zeroed block of `k` cells, then continue with the block handle. -/
theorem allocBlock_bind {Q : α → State → Prop} {k : ℕ} {next : Block → Prog α}
    (hk : Fits w (s.frontier + k))
    (h : FramedTriple w ⟨clear s.mem s.frontier k, s.frontier + k⟩
      (next ⟨s.frontier, k⟩) c S Q) :
    FramedTriple w s (Memory.allocBlock k >>= next) (c + (k + 1)) S Q :=
  Triple.allocBlock_bind hk (Triple.mono h le_rfl fun _ _ ⟨hm, hq⟩ =>
    ⟨by rw [← Set.empty_union S]; exact (Modifies.alloc s k).union hm, hq⟩)

/-- Allocate a dirty block of `k` cells, then continue with the block handle. -/
theorem allocBlockDirty_bind {Q : α → State → Prop} {k : ℕ} {next : Block → Prog α}
    (hk : Fits w (s.frontier + k))
    (h : FramedTriple w ⟨s.mem, s.frontier + k⟩ (next ⟨s.frontier, k⟩) c S Q) :
    FramedTriple w s (Memory.allocBlockDirty k >>= next) (c + 1) S Q :=
  Triple.allocBlockDirty_bind hk (Triple.mono h le_rfl fun _ _ ⟨hm, hq⟩ =>
    ⟨by rw [← Set.empty_union S]; exact (Modifies.allocDirty s k).union hm, hq⟩)

/-- Read entry `i` of an allocated block, then continue. -/
theorem get_bind {Q : α → State → Prop} {b : Block} {i : ℕ} {k : ℕ → Prog α}
    (hb : b.Allocated s) (hi : i < b.length)
    (h : FramedTriple w s (k (s.mem (b.base + i))) c S Q) :
    FramedTriple w s (b.get i >>= k) (c + 1) S Q :=
  read_bind (hb.lt_frontier hi) h

/-- Read entry `i` of an allocated block as a standalone framed program. -/
theorem get {Q : ℕ → State → Prop} {b : Block} {i : ℕ} (hb : b.Allocated s) (hi : i < b.length)
    (h : Q (s.mem (b.base + i)) s) : FramedTriple w s (b.get i) 1 S Q :=
  get_bind hb hi (pure h)

/-- Write `v` to entry `i` of an allocated block inside `S`, then continue. -/
theorem set_bind {Q : α → State → Prop} {b : Block} {i v : ℕ} {k : Unit → Prog α}
    (hb : b.Allocated s) (hi : i < b.length) (hv : Fits w v)
    (hsub : Set.Ico b.base (b.base + b.length) ⊆ S)
    (h : FramedTriple w ⟨Function.update s.mem (b.base + i) v, s.frontier⟩ (k ()) c S Q) :
    FramedTriple w s (b.set i v >>= k) (c + 1) S Q :=
  write_bind_of_mem (hb.lt_frontier hi) hv (hsub ⟨Nat.le_add_right _ _, by omega⟩) h

/-- Write `v` to entry `i` of an allocated block as a standalone framed program. -/
theorem set {Q : Unit → State → Prop} {b : Block} {i v : ℕ} (hb : b.Allocated s)
    (hi : i < b.length) (hv : Fits w v) (hsub : Set.Ico b.base (b.base + b.length) ⊆ S)
    (h : Q () ⟨Function.update s.mem (b.base + i) v, s.frontier⟩) :
    FramedTriple w s (b.set i v) 1 S Q :=
  set_bind hb hi hv hsub (pure h)

/-- Sequential composition of framed triples takes the union of modification sets. -/
theorem bind {p : Prog α} {k : α → Prog β} {c₁ c₂ : ℕ} {S₁ S₂ : Set ℕ} {Q : β → State → Prop}
    (h : FramedTriple w s p c₁ S₁ fun a s' => FramedTriple w s' (k a) c₂ S₂ Q) :
    FramedTriple w s (p >>= k) (c₁ + c₂) (S₁ ∪ S₂) Q :=
  Triple.bind (Triple.mono h le_rfl fun _ _ ⟨hm₁, hk⟩ =>
    Triple.mono hk le_rfl fun _ _ ⟨hm₂, hq⟩ => ⟨hm₁.union hm₂, hq⟩)

/-- Sequential composition of framed triples within a single shared modification set `S`. -/
theorem bind_same {p : Prog α} {k : α → Prog β} {c₁ c₂ : ℕ} {Q : β → State → Prop}
    (h : FramedTriple w s p c₁ S fun a s' => FramedTriple w s' (k a) c₂ S Q) :
    FramedTriple w s (p >>= k) (c₁ + c₂) S Q :=
  (bind h).frame_mono (Set.union_self S).subset

/-- Branching rule for `FramedTriple`. -/
theorem ite {Q : α → State → Prop} {cond : Prop} [Decidable cond] {p₁ p₂ : Prog α}
    (h₁ : cond → FramedTriple w s p₁ c S Q) (h₂ : ¬cond → FramedTriple w s p₂ c S Q) :
    FramedTriple w s (if cond then p₁ else p₂) c S Q :=
  Triple.ite h₁ h₂

/-- Dependent branching rule for `FramedTriple`. -/
theorem dite {Q : α → State → Prop} {cond : Prop} [Decidable cond]
    {p₁ : cond → Prog α} {p₂ : ¬cond → Prog α}
    (h₁ : ∀ h : cond, FramedTriple w s (p₁ h) c S Q)
    (h₂ : ∀ h : ¬cond, FramedTriple w s (p₂ h) c S Q) :
    FramedTriple w s (if h : cond then p₁ h else p₂ h) c S Q :=
  Triple.dite h₁ h₂

/-- Map the answer of a `FramedTriple` without changing its cost or frame. -/
theorem map (f : α → β) {p : Prog α} {Q : β → State → Prop}
    (h : FramedTriple w s p c S fun a s' => Q (f a) s') :
    FramedTriple w s (f <$> p) c S Q :=
  Triple.map f h

/-- Non-overlapping block copy with `FramedTriple` specification. -/
theorem copy {src dst n : ℕ} (hdisj : src + n ≤ dst ∨ dst + n ≤ src)
    (hsrc : src + n ≤ s.frontier) (hdst : dst + n ≤ s.frontier)
    (hfit : ∀ i < n, Fits w (s.mem (src + i))) {Q : Unit → State → Prop}
    (hQ : Q () ⟨Cslib.WordRAM.ArrayCopy.copyPrefix s.mem src dst n, s.frontier⟩) :
    FramedTriple w s (Memory.copy src dst n) (2 * n) (Set.Ico dst (dst + n)) Q := by
  refine Triple.copy hdisj hsrc hdst hfit ⟨⟨le_rfl, fun a _ ha => ?_⟩, hQ⟩
  change Cslib.WordRAM.ArrayCopy.copyPrefix s.mem src dst n a = s.mem a
  exact Cslib.WordRAM.ArrayCopy.copyPrefix_outside (by
    simp only [Set.mem_Ico] at ha
    exact ha)

/-- Any `FramedTriple` preserves `WellFormed w`. -/
theorem wellFormed {Q : α → State → Prop} {p : Prog α} (hwf : WellFormed w s)
    (h : FramedTriple w s p c S Q) :
    FramedTriple w s p c S fun a s' => Q a s' ∧ WellFormed w s' := by
  refine Triple.mono (Triple.wellFormed hwf h) le_rfl fun _ _ ⟨⟨hm, hq⟩, hwf'⟩ => ⟨hm, hq, hwf'⟩

/-- Any `FramedTriple` preserves `ZeroAbove`. -/
theorem zeroAbove {Q : α → State → Prop} {p : Prog α} (hz : ZeroAbove s)
    (h : FramedTriple w s p c S Q) :
    FramedTriple w s p c S fun a s' => Q a s' ∧ ZeroAbove s' := by
  refine Triple.mono (Triple.zeroAbove hz h) le_rfl fun _ _ ⟨⟨hm, hq⟩, hz'⟩ => ⟨hm, hq, hz'⟩

/-- Automatic preservation of any raw-memory heap predicate `R` supported on allocated cells
`D` disjoint from `S`. -/
theorem frame_mem {Q : α → State → Prop} {p : Prog α} {D : Set ℕ} {R : (ℕ → ℕ) → Prop}
    (h : FramedTriple w s p c S Q) (hR : R s.mem)
    (hdep : ∀ m₁ m₂, (∀ a ∈ D, m₁ a = m₂ a) → R m₁ → R m₂)
    (hdisj : Disjoint S D) (halloc : ∀ a ∈ D, a < s.frontier) :
    FramedTriple w s p c S fun a s' => Q a s' ∧ R s'.mem := by
  obtain ⟨hv, hc, hm, hq⟩ := framedTriple_iff.mp h
  exact framedTriple_iff.mpr ⟨hv, hc, hm, hq, hdep s.mem _
    (fun a haD => (hm.mem_eq_of_disjoint hdisj (halloc a haD) haD).symm) hR⟩

/-- Automatic preservation of any frontier-invariant state predicate `R` supported on allocated
cells `D` disjoint from `S`. -/
theorem frame {Q : α → State → Prop} {p : Prog α} {D : Set ℕ} {R : State → Prop}
    (h : FramedTriple w s p c S Q) (hR : R s)
    (hdep : ∀ s₁ s₂, (∀ a ∈ D, s₁.mem a = s₂.mem a) → R s₁ → R s₂)
    (hdisj : Disjoint S D) (halloc : ∀ a ∈ D, a < s.frontier) :
    FramedTriple w s p c S fun a s' => Q a s' ∧ R s' := by
  obtain ⟨hv, hc, hm, hq⟩ := framedTriple_iff.mp h
  exact framedTriple_iff.mpr ⟨hv, hc, hm, hq, hdep s _
    (fun a haD => (hm.mem_eq_of_disjoint hdisj (halloc a haD) haD).symm) hR⟩

end FramedTriple

end Cslib.DataStructure.Memory

/-! ## Block disjointness, strided slots, and multi-field writes -/

namespace Cslib.WordRAM.Block

open Cslib.DataStructure

/-- Two blocks are disjoint when no address is owned by both. -/
def Disjoint (b₁ b₂ : Block) : Prop := ∀ a, ¬(b₁.Owns a ∧ b₂.Owns a)

/-- Characterization of block disjointness by emptiness or non-overlapping endpoints. -/
theorem disjoint_iff {b₁ b₂ : Block} :
    b₁.Disjoint b₂ ↔ b₁.length = 0 ∨ b₂.length = 0 ∨
      b₁.base + b₁.length ≤ b₂.base ∨ b₂.base + b₂.length ≤ b₁.base := by
  constructor
  · intro h
    by_cases h1 : b₁.length = 0
    · exact Or.inl h1
    · by_cases h2 : b₂.length = 0
      · exact Or.inr (Or.inl h2)
      · by_cases h12 : b₁.base + b₁.length ≤ b₂.base
        · exact Or.inr (Or.inr (Or.inl h12))
        · by_cases h21 : b₂.base + b₂.length ≤ b₁.base
          · exact Or.inr (Or.inr (Or.inr h21))
          · exfalso
            have ha := h (max b₁.base b₂.base)
            apply ha
            refine ⟨⟨le_max_left _ _, ?_⟩, ⟨le_max_right _ _, ?_⟩⟩ <;> omega
  · rintro (h | h | h | h) a ⟨⟨h1a, h1b⟩, ⟨h2a, h2b⟩⟩ <;> omega

instance instDecidableDisjoint (b₁ b₂ : Block) : Decidable (b₁.Disjoint b₂) :=
  decidable_of_iff' _ disjoint_iff

/-- Symmetry of block disjointness. -/
@[symm] theorem Disjoint.symm {b₁ b₂ : Block} (h : b₁.Disjoint b₂) : b₂.Disjoint b₁ :=
  fun a ⟨h2, h1⟩ => h a ⟨h1, h2⟩

/-- `b₁` ending at or before `b₂.base` implies `b₁.Disjoint b₂`. -/
theorem disjoint_of_le_left {b₁ b₂ : Block} (h : b₁.base + b₁.length ≤ b₂.base) :
    b₁.Disjoint b₂ :=
  disjoint_iff.mpr (Or.inr (Or.inr (Or.inl h)))

/-- `b₂` ending at or before `b₁.base` implies `b₁.Disjoint b₂`. -/
theorem disjoint_of_le_right {b₁ b₂ : Block} (h : b₂.base + b₂.length ≤ b₁.base) :
    b₁.Disjoint b₂ :=
  disjoint_iff.mpr (Or.inr (Or.inr (Or.inr h)))

/-- An allocated block is disjoint from any block allocated at the current frontier. -/
theorem disjoint_of_allocated_frontier {b : Block} {s : Memory.State} (hb : b.Allocated s)
    (k : ℕ) : b.Disjoint ⟨s.frontier, k⟩ :=
  disjoint_of_le_left hb

/-- Block disjointness matches `Set` disjointness of half-open address intervals. -/
theorem disjoint_ico_iff {b₁ b₂ : Block} :
    _root_.Disjoint (Set.Ico b₁.base (b₁.base + b₁.length))
      (Set.Ico b₂.base (b₂.base + b₂.length)) ↔ b₁.Disjoint b₂ := by
  rw [Set.disjoint_left]
  exact ⟨fun h a ⟨ha₁, ha₂⟩ => h ha₁ ha₂, fun h a ha₁ ha₂ => h a ⟨ha₁, ha₂⟩⟩

/-- Block disjointness matches `Finset` disjointness of `Block.footprint`. -/
theorem disjoint_footprint_iff {b₁ b₂ : Block} :
    _root_.Disjoint b₁.footprint b₂.footprint ↔ b₁.Disjoint b₂ := by
  rw [Finset.disjoint_left]
  simp only [Block.mem_footprint]
  exact ⟨fun h a ⟨ha₁, ha₂⟩ => h ha₁ ha₂, fun h a ha₁ ha₂ => h a ⟨ha₁, ha₂⟩⟩

/-- An allocated block stays allocated under `Memory.Modifies`. -/
theorem allocated_of_modifies {b : Block} {S : Set ℕ} {s s' : Memory.State}
    (hb : b.Allocated s) (hmod : Memory.Modifies S s s') : b.Allocated s' :=
  hb.mono hmod.1

/-- An allocated block disjoint from `S` retains every cell across `Memory.Modifies S s s'`. -/
theorem mem_eq_of_modifies_disjoint {b : Block} {S : Set ℕ} {s s' : Memory.State}
    (hb : b.Allocated s) (hmod : Memory.Modifies S s s')
    (hdisj : _root_.Disjoint S (Set.Ico b.base (b.base + b.length))) :
    ∀ a, b.Owns a → s'.mem a = s.mem a := fun a ha =>
  hmod.mem_eq_of_disjoint hdisj (by wram_omega [hb, ha]) ha

/-- An allocated block disjoint from `S` keeps its `entries` list unchanged across
`Memory.Modifies S s s'`. -/
theorem entries_eq_of_modifies_disjoint {b : Block} {n : ℕ} {S : Set ℕ} {s s' : Memory.State}
    (hb : b.Allocated s) (hn : n ≤ b.length) (hmod : Memory.Modifies S s s')
    (hdisj : _root_.Disjoint S (Set.Ico b.base (b.base + b.length))) :
    b.entries n s'.mem = b.entries n s.mem :=
  b.entries_congr n fun i hi =>
    mem_eq_of_modifies_disjoint hb hmod hdisj _ (owns_add (by omega))

/-- A `HoldsList` assertion on an allocated block disjoint from `S` survives
`Memory.Modifies S s s'`. -/
theorem holdsList_of_modifies_disjoint {base : ℕ} {xs : List ℕ} {S : Set ℕ} {s s' : Memory.State}
    (hb : (Block.mk base xs.length).Allocated s) (hh : HoldsList base xs s.mem)
    (hmod : Memory.Modifies S s s')
    (hdisj : _root_.Disjoint S (Set.Ico base (base + xs.length))) :
    HoldsList base xs s'.mem :=
  HoldsList.frame hh fun _ hlo hhi =>
    mem_eq_of_modifies_disjoint hb hmod hdisj _ ⟨hlo, hhi⟩

/-- Specialized block framing: writing inside a disjoint block `b'` preserves `b.mem`. -/
theorem mem_eq_of_modifies_block {b b' : Block} {s s' : Memory.State}
    (hb : b.Allocated s) (hd : b.Disjoint b')
    (hmod : Memory.Modifies (Set.Ico b'.base (b'.base + b'.length)) s s') :
    ∀ a, b.Owns a → s'.mem a = s.mem a :=
  mem_eq_of_modifies_disjoint hb hmod (disjoint_ico_iff.mpr hd.symm)

/-- Specialized block framing: writing inside a disjoint block `b'` preserves `b.entries`. -/
theorem entries_eq_of_modifies_block {b b' : Block} {n : ℕ} {s s' : Memory.State}
    (hb : b.Allocated s) (hn : n ≤ b.length) (hd : b.Disjoint b')
    (hmod : Memory.Modifies (Set.Ico b'.base (b'.base + b'.length)) s s') :
    b.entries n s'.mem = b.entries n s.mem :=
  entries_eq_of_modifies_disjoint hb hn hmod (disjoint_ico_iff.mpr hd.symm)

/-! ### Strided record-array framing -/

/-- The `idx`-th record slot of stride `stride` starting at `base`. -/
def slot (base stride idx : ℕ) : Block := ⟨base + stride * idx, stride⟩

@[simp] theorem slot_base (base stride idx : ℕ) :
    (slot base stride idx).base = base + stride * idx := rfl

@[simp] theorem slot_length (base stride idx : ℕ) :
    (slot base stride idx).length = stride := rfl

/-- Distinct indices in a strided record array occupy disjoint blocks. -/
theorem slot_disjoint_of_ne {base stride i j : ℕ} (hne : i ≠ j) :
    (slot base stride i).Disjoint (slot base stride j) := by
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · refine disjoint_of_le_left ?_
    calc
      (slot base stride i).base + (slot base stride i).length
          = base + stride * (i + 1) := by
            simp only [slot, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
      _ ≤ base + stride * j := Nat.add_le_add_left (Nat.mul_le_mul_left stride hij) base
      _ = (slot base stride j).base := rfl
  · exact absurd rfl hne
  · refine disjoint_of_le_right ?_
    calc
      (slot base stride j).base + (slot base stride j).length
          = base + stride * (j + 1) := by
            simp only [slot, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
      _ ≤ base + stride * i := Nat.add_le_add_left (Nat.mul_le_mul_left stride hij) base
      _ = (slot base stride i).base := rfl

/-- Slot `idx < n` of an `n`-element strided array lies below the frontier when the whole array
does. -/
theorem slot_allocated_of_lt {base stride n idx : ℕ} {s : Memory.State}
    (halloc : base + stride * n ≤ s.frontier) (hidx : idx < n) :
    (slot base stride idx).Allocated s := by
  calc
    (slot base stride idx).base + (slot base stride idx).length
        = base + stride * (idx + 1) := by
          simp only [slot, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    _ ≤ base + stride * n := Nat.add_le_add_left (Nat.mul_le_mul_left stride hidx) base
    _ ≤ s.frontier := halloc

/-- Modifying a different strided slot `j ≠ i` preserves all cells of slot `i`. -/
theorem slot_mem_eq_of_modifies_other {base stride i j : ℕ} {s s' : Memory.State}
    (hi : (slot base stride i).Allocated s) (hne : i ≠ j)
    (hmod : Memory.Modifies
      (Set.Ico (slot base stride j).base ((slot base stride j).base + stride)) s s') :
    ∀ a, (slot base stride i).Owns a → s'.mem a = s.mem a :=
  mem_eq_of_modifies_block hi (slot_disjoint_of_ne hne) hmod

/-- Modifying a different strided slot `j ≠ i` preserves `entries` of slot `i`. -/
theorem slot_entries_eq_of_modifies_other {base stride n i j : ℕ} {s s' : Memory.State}
    (hi : (slot base stride i).Allocated s) (hn : n ≤ stride) (hne : i ≠ j)
    (hmod : Memory.Modifies
      (Set.Ico (slot base stride j).base ((slot base stride j).base + stride)) s s') :
    (slot base stride i).entries n s'.mem = (slot base stride i).entries n s.mem :=
  entries_eq_of_modifies_block hi hn (slot_disjoint_of_ne hne) hmod

/-! ### Consecutive multi-field list writes -/

/-- Write the list of words `vs` into consecutive cells `base` through `base + vs.length - 1`. -/
def writeList : ℕ → List ℕ → Memory.Prog Unit
  | _, [] => pure ()
  | base, v :: vs => do
    Memory.write base v
    writeList (base + 1) vs

@[simp] theorem writeList_nil (base : ℕ) : writeList base [] = pure () := rfl

@[simp] theorem writeList_cons (base v : ℕ) (vs : List ℕ) :
    writeList base (v :: vs) = (Memory.write base v >>= fun _ => writeList (base + 1) vs) := rfl

/-- `writeList` preserves the frontier. -/
theorem clientState_writeList_frontier (w base : ℕ) (vs : List ℕ) (s : Memory.State) :
    ((Memory.spec w).clientState s (writeList base vs)).frontier = s.frontier := by
  induction vs generalizing base s with
  | nil => rfl
  | cons v vs ih =>
    rw [writeList_cons, (Memory.spec w).clientState_bind]
    exact ih (base + 1) ⟨Function.update s.mem base v, s.frontier⟩

private theorem mem_writeList_of_not_mem (w base : ℕ) (vs : List ℕ) (s : Memory.State)
    {a : ℕ} (ha : a ∉ Set.Ico base (base + vs.length)) :
    ((Memory.spec w).clientState s (writeList base vs)).mem a = s.mem a := by
  induction vs generalizing base s with
  | nil => rfl
  | cons v vs ih =>
    rw [writeList_cons, (Memory.spec w).clientState_bind]
    have hnot : a ∉ Set.Ico (base + 1) (base + 1 + vs.length) := by
      simp only [Set.mem_Ico, List.length_cons, not_and, not_lt] at ha ⊢
      omega
    have hstep : (Memory.spec w).clientState s (Memory.write base v) =
        ⟨Function.update s.mem base v, s.frontier⟩ := rfl
    rw [hstep, ih (base + 1) ⟨Function.update s.mem base v, s.frontier⟩ hnot]
    have hne : a ≠ base := by
      simp only [Set.mem_Ico, List.length_cons, not_and, not_lt] at ha
      omega
    exact Function.update_of_ne hne v s.mem

/-- After `writeList`, `[base, base + vs.length)` realizes `vs`. -/
theorem holdsList_writeList (w base : ℕ) (vs : List ℕ) (s : Memory.State) :
    HoldsList base vs ((Memory.spec w).clientState s (writeList base vs)).mem := by
  induction vs generalizing base s with
  | nil => exact holdsList_nil base _
  | cons v vs ih =>
    rw [writeList_cons, (Memory.spec w).clientState_bind]
    refine holdsList_cons_iff.mpr ⟨?_, ih (base + 1) ⟨Function.update s.mem base v, s.frontier⟩⟩
    change ((Memory.spec w).clientState ⟨Function.update s.mem base v, s.frontier⟩
      (writeList (base + 1) vs)).mem base = v
    have hnot : base ∉ Set.Ico (base + 1) (base + 1 + vs.length) := by
      simp only [Set.mem_Ico, not_and, not_lt]
      omega
    rw [mem_writeList_of_not_mem w (base + 1) vs ⟨Function.update s.mem base v, s.frontier⟩ hnot]
    simp

/-- `writeList` is admissible when `[base, base + vs.length)` is allocated and every written
word fits `w`. -/
theorem validHistory_writeList (w base : ℕ) (vs : List ℕ) (s : Memory.State)
    (hbound : base + vs.length ≤ s.frontier) (hfit : ∀ v ∈ vs, Fits w v) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writeList base vs)) := by
  induction vs generalizing base s with
  | nil => trivial
  | cons v vs ih =>
    simp only [List.length_cons] at hbound
    rw [writeList_cons, (Memory.spec w).clientHistory_bind,
      StateTransitionSpec.validHistory_append, StateTransitionSpec.run_runClient]
    refine ⟨⟨⟨by omega, hfit v List.mem_cons_self⟩, trivial⟩, ?_⟩
    exact ih (base + 1) ⟨Function.update s.mem base v, s.frontier⟩ (by dsimp only; omega)
      fun x hx => hfit x (List.mem_cons_of_mem _ hx)

/-- `writeList` costs exactly `vs.length` memory units. -/
theorem totalCost_writeList (w base : ℕ) (vs : List ℕ) (s : Memory.State) :
    (Memory.spec w).totalCost Memory.charge s
      ((Memory.spec w).clientHistory s (writeList base vs)) = vs.length := by
  induction vs generalizing base s with
  | nil => rfl
  | cons v vs ih =>
    rw [writeList_cons, (Memory.spec w).clientHistory_bind,
      StateTransitionSpec.totalCost_append, StateTransitionSpec.run_runClient, ih]
    change 1 + vs.length = vs.length + 1
    omega

/-- General `FramedTriple` specification for `Block.writeList`, including fixed-frontier and
`WellFormed w` preservation. -/
theorem framedTriple_writeList {w base : ℕ} {vs : List ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hbound : base + vs.length ≤ s.frontier)
    (hfit : ∀ v ∈ vs, Fits w v) :
    Memory.FramedTriple w s (writeList base vs) vs.length (Set.Ico base (base + vs.length))
      fun _ s' => s'.frontier = s.frontier ∧ HoldsList base vs s'.mem ∧
        Memory.WellFormed w s' := by
  have hft : Memory.FramedTriple w s (writeList base vs) vs.length
      (Set.Ico base (base + vs.length)) fun _ s' =>
        s'.frontier = s.frontier ∧ HoldsList base vs s'.mem :=
    Memory.framedTriple_iff.mpr ⟨validHistory_writeList w base vs s hbound hfit,
      (totalCost_writeList w base vs s).le,
      ⟨(clientState_writeList_frontier w base vs s).ge,
        fun a _ ha => mem_writeList_of_not_mem w base vs s ha⟩,
      clientState_writeList_frontier w base vs s,
      holdsList_writeList w base vs s⟩
  exact (hft.wellFormed hwf).mono le_rfl fun _ _ ⟨⟨hfr, hhold⟩, hwf'⟩ => ⟨hfr, hhold, hwf'⟩

end Cslib.WordRAM.Block
