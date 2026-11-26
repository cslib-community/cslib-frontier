/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.CRDT.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Replicated Counters and Sets (`GCounter`, `PNCounter`, `TwoPhaseSet`, `ORSet`) & Impossibility

This module formalizes concrete state-based (`CvRDT`) and operation-based (`CmRDT`) data types
together with their functional specifications and untagged set impossibility steps toward #7502
(after Shapiro, Preguiça, Baquero, and Zawirski [ShapiroPreguicaBaqueroZawirski2011], §§4.1–4.2,
pp. 11–12, and [ShapiroPreguicaBaqueroZawirski2011R], §§3.1, 3.3, Specifications 6, 7, 11, 12, 15,
pp. 14–16, 21–27):

1. **`GCounter P` (Grow-Only Counter, Specification 6):**
   Per-replica vector `counts : P → ℕ` with pointwise `max` semilattice merge and query
   `∑ p : P, counts p`, proving `SemilatticeSup` / `OrderBot`, `CvRDT` and `CmRDT` instances,
   monotonicity of `GCounter.value`, and exact multi-replica global sum convergence
   (`GCounter.value_sup_of_local_counts`, avoiding the lost-update anomaly of merging a single
   scalar counter via `max`).

2. **`PNCounter P` (Positive-Negative Counter, Specification 7):**
   Paired `(pos, neg)` `GCounter`s evaluating to `(pos.value : ℤ) - (neg.value : ℤ)`, proving
   unconditional commutativity of increments and decrements and exact net-count evaluation.

3. **Grow-Only Set (`gsetCvRDT`, `gsetCmRDT`) and `TwoPhaseSet α` (`2P-Set`, Specification 12):**
   `(added, removed)` pair of `Finset α`s with query `added \ removed`, proving `CvRDT` and `CmRDT`
   convergence, concurrent remove-wins (`TwoPhaseSet.remove_wins_concurrent`), and monotonic
   tombstone permanence (`TwoPhaseSet.not_mem_elements_of_le_of_removed`: once tombstoned, an
   element can never re-enter `elements` at any semilattice successor).

4. **`ORSet` (Observed-Remove Set with Unique `P × ℕ` Tags, Specification 15 & Figure 14):**
   * **State-based `ORSetCv P α` (`CvRDT`):** `(entries, tombstones)` over `TaggedElem P α`, where
     `add p seq x` inserts fresh `⟨x, p, seq⟩` and `removeObserved x` tombstones only currently
     observed tags of `x`, proving both concurrent add-wins (`ORSetCv.mem_sup_removeObserved_add`)
     and sequential re-addition after removal (`ORSetCv.mem_add_after_removeObserved`).
   * **Op-based `orsetCmRDT` (`CmRDT`) & Causal Add-Wins Theorem:** over any valid causal history
     (`ORSetCausalHistory`) where `add` allocates unique `(replica, seq)` tags and `remove(x)`
     collects the tags of `x` present in its source replica's causally delivered state, concurrent
     downstream effects commute (`ORSetCausalHistory.concurrentCommute`) and every causal
     linearization evaluates to `orsetSurvivingTags`
     (`ORSetCausalHistory.foldl_eq_survivingTags`), satisfying the exact **Causal Add-Wins
     Specification** (`ORSetCausalHistory.mem_elements_iff_causal_add_wins`):
     `x ∈ orsetElements state ↔ ∃ e_add ∈ H, (∃ p n, opOf e_add = .add p n x) ∧
     ¬ ∃ e_rem ∈ H, opOf e_rem = .remove x ∧ prec e_add e_rem`.

5. **Untagged Set Impossibility (`not_exists_untagged_finset_merge`,
   `untagged_insert_erase_ne_erase_insert`):**
   Proves that no commutative binary merge `Finset α → Finset α → Finset α` on plain untagged sets
   (`[Nonempty α]`) can simultaneously propagate a fresh `add` to an untouched peer at `∅`
   (`x ∈ merge ∅ (insert x ∅)`) and propagate a sequential `remove`-after-`add` to a peer still
   holding `{x}` (`x ∉ merge {x} (({x} : Finset α).erase x)`), because both executions present the
   same unordered pair of untagged states `{∅, {x}}`, alongside op-based non-commutativity of naïve
   `insert` and `erase` ([ShapiroPreguicaBaqueroZawirski2011R], §3.3 Figure 11, p. 21).

## Main definitions

* `Cslib.Distributed.CRDT.GCounter`: state-based / op-based grow-only counter (`P → ℕ`).
* `Cslib.Distributed.CRDT.PNCounter`,
  `Cslib.Distributed.CRDT.PNCounterOp`: paired increment/decrement counter evaluating in `ℤ`.
* `Cslib.Distributed.CRDT.gsetCvRDT`,
  `Cslib.Distributed.CRDT.gsetCmRDT`: grow-only set CRDTs on `Finset α`.
* `Cslib.Distributed.CRDT.SetOp`,
  `Cslib.Distributed.CRDT.TwoPhaseSet`: two-phase set `(added, removed)` with permanent tombstones.
* `Cslib.Distributed.CRDT.TaggedElem`,
  `Cslib.Distributed.CRDT.ORSetOp`,
  `Cslib.Distributed.CRDT.ORSetCv`,
  `Cslib.Distributed.CRDT.ORSetEff`,
  `Cslib.Distributed.CRDT.orsetEffect`,
  `Cslib.Distributed.CRDT.orsetElements`,
  `Cslib.Distributed.CRDT.orsetCmRDT`,
  `Cslib.Distributed.CRDT.orsetSurvivingTags`,
  `Cslib.Distributed.CRDT.ORSetCausalHistory`: state-based and op-based Observed-Remove Set.

## Main results

* `Cslib.Distributed.CRDT.GCounter.cmrdt_effectsCommute`,
  `Cslib.Distributed.CRDT.GCounter.mono_value`, and
  `Cslib.Distributed.CRDT.GCounter.value_sup_of_local_counts`: `GCounter` commutativity,
  monotonicity, and exact global sum convergence.
* `Cslib.Distributed.CRDT.PNCounter.cmrdt_effectsCommute` and
  `Cslib.Distributed.CRDT.PNCounter.value_sup_of_local_counts`: `PNCounter` commutativity and exact
  global difference convergence.
* `Cslib.Distributed.CRDT.TwoPhaseSet.not_mem_elements_of_le_of_removed` and
  `Cslib.Distributed.CRDT.TwoPhaseSet.remove_wins_concurrent`: permanent tombstones and concurrent
  remove-wins in `TwoPhaseSet`.
* `Cslib.Distributed.CRDT.ORSetCv.mem_sup_removeObserved_add` and
  `Cslib.Distributed.CRDT.ORSetCv.mem_add_after_removeObserved`: state-based `ORSetCv` concurrent
  add-wins and sequential re-add after remove.
* `Cslib.Distributed.CRDT.ORSetCausalHistory.concurrentCommute`,
  `Cslib.Distributed.CRDT.ORSetCausalHistory.foldl_eq_survivingTags`, and
  `Cslib.Distributed.CRDT.ORSetCausalHistory.mem_elements_iff_causal_add_wins`: op-based `OR-Set`
  concurrent commutativity and exact causal add-wins specification step.
* `Cslib.Distributed.CRDT.not_exists_untagged_finset_merge` and
  `Cslib.Distributed.CRDT.untagged_insert_erase_ne_erase_insert`: untagged `Finset` merge
  impossibility and op-based `insert`/`erase` non-commutativity.

## References

* [M. Shapiro, N. Preguiça, C. Baquero, M. Zawirski, *Conflict-free Replicated Data
  Types*][ShapiroPreguicaBaqueroZawirski2011]
* [M. Shapiro, N. Preguiça, C. Baquero, M. Zawirski, *A comprehensive study of Convergent and
  Commutative Replicated Data Types*][ShapiroPreguicaBaqueroZawirski2011R]
-/

public section

namespace Cslib.Distributed.CRDT

/-! ### `GCounter`: Grow-Only Counter -/

/-- Replicated grow-only counter (`G-Counter`, [ShapiroPreguicaBaqueroZawirski2011], §4.1, p. 11;
[ShapiroPreguicaBaqueroZawirski2011R], §3.1.2, Specification 6, pp. 14–16) allocating one
natural-number slot per replica `p : P` (avoiding the lost-update anomaly of merging a single scalar
counter via `max`). -/
@[ext]
structure GCounter (P : Type*) where
  /-- Per-replica increment counts. -/
  counts : P → ℕ

instance {P : Type*} [Fintype P] : DecidableEq (GCounter P) :=
  fun a b => decidable_of_iff (a.counts = b.counts)
    ⟨GCounter.ext, congrArg GCounter.counts⟩

instance {P : Type*} : SemilatticeSup (GCounter P) where
  le a b := a.counts ≤ b.counts
  sup a b := ⟨a.counts ⊔ b.counts⟩
  le_refl a := le_refl a.counts
  le_trans _ _ _ := le_trans
  le_antisymm _ _ hab hba := GCounter.ext (le_antisymm hab hba)
  le_sup_left a b := le_sup_left (a := a.counts) (b := b.counts)
  le_sup_right a b := le_sup_right (a := a.counts) (b := b.counts)
  sup_le _ _ _ := sup_le

instance {P : Type*} : OrderBot (GCounter P) where
  bot := ⟨0⟩
  bot_le _ := fun _ => Nat.zero_le _

namespace GCounter

/-- Initial zero `GCounter`. -/
@[expose]
def zero (P : Type*) : GCounter P := ⊥

@[simp]
theorem counts_zero {P : Type*} (p : P) : (zero P).counts p = 0 := rfl

@[simp]
theorem counts_sup {P : Type*} (a b : GCounter P) (p : P) :
    (a ⊔ b).counts p = max (a.counts p) (b.counts p) := rfl

/-- Increment replica `p`'s entry by `1`. -/
@[expose]
def inc {P : Type*} [DecidableEq P] (p : P) (c : GCounter P) : GCounter P :=
  ⟨Function.update c.counts p (c.counts p + 1)⟩

/-- Total counter value `∑ p : P, c.counts p`. -/
@[expose]
def value {P : Type*} [Fintype P] (c : GCounter P) : ℕ :=
  ∑ p : P, c.counts p

theorem le_inc {P : Type*} [DecidableEq P] (p : P) (c : GCounter P) : c ≤ c.inc p := fun r => by
  simp only [inc, Function.update_apply]
  split_ifs with hr <;> simp [hr]

theorem inc_comm {P : Type*} [DecidableEq P] (p q : P) (c : GCounter P) :
    (c.inc p).inc q = (c.inc q).inc p := by
  rcases eq_or_ne p q with rfl | hpq
  · rfl
  · exact GCounter.ext (by
      simp [inc, Function.update_of_ne hpq, Function.update_of_ne hpq.symm,
        Function.update_comm hpq.symm])

@[simp]
theorem value_zero {P : Type*} [Fintype P] : (zero P).value = 0 :=
  Finset.sum_const_zero

@[simp]
theorem value_inc {P : Type*} [Fintype P] [DecidableEq P] (p : P) (c : GCounter P) :
    (c.inc p).value = c.value + 1 := by
  simp only [value, inc, ← Finset.add_sum_erase _ _ (Finset.mem_univ p), Function.update_self]
  rw [Finset.sum_congr rfl fun x hx => Function.update_of_ne (Finset.ne_of_mem_erase hx) _ _]
  omega

/-- Monotonicity of `GCounter.value` with respect to the semilattice order. -/
theorem mono_value {P : Type*} [Fintype P] : Monotone (value (P := P)) :=
  fun _ _ hab => Finset.sum_le_sum fun p _ => hab p

/-- State-based `CvRDT` instance for `GCounter P`. -/
@[expose]
def cvrdt (P : Type*) [Fintype P] [DecidableEq P] : CvRDT (GCounter P) P ℕ where
  init := zero P
  query := value
  update := inc
  update_infl := le_inc

/-- Op-based `CmRDT` instance for `GCounter P` where replica `p` broadcasts `p` to increment slot
`p` downstream. -/
@[expose]
def cmrdt (P : Type*) [Fintype P] [DecidableEq P] : CmRDT (GCounter P) P P ℕ where
  init := zero P
  query := value
  prepare p _ := p
  effect := inc

theorem cmrdt_effectsCommute {P : Type*} [Fintype P] [DecidableEq P] :
    EffectsCommute (cmrdt P).effect :=
  fun p q c => inc_comm q p c

/-- Exact multi-replica sum specification step (toward #7502, after
[ShapiroPreguicaBaqueroZawirski2011R], §3.1.2, Specification 6, pp. 15–16): when each replica `p`
holds its own originated count `(rep p).counts p = k p` and no replica over-counts any peer
(`(rep q).counts p ≤ k p`), the global semilattice merge evaluates to `∑ p : P, k p`. -/
theorem value_sup_of_local_counts {P : Type*} [Fintype P] [Nonempty P]
    (rep : P → GCounter P) (k : P → ℕ)
    (hown : ∀ p, (rep p).counts p = k p)
    (hle : ∀ q p, (rep q).counts p ≤ k p) :
    (Finset.univ.sup' Finset.univ_nonempty rep).value = ∑ p : P, k p := by
  have hsup_eq : Finset.univ.sup' Finset.univ_nonempty rep = ⟨k⟩ :=
    le_antisymm (Finset.sup'_le _ _ fun q _ p => hle q p) fun p => by
      simpa only [← hown p] using Finset.le_sup' rep (Finset.mem_univ p) p
  rw [hsup_eq]
  rfl

end GCounter

/-! ### `PNCounter`: Positive-Negative Counter -/

/-- Update operations on a `PNCounter P`: increment or decrement at source replica `p`. -/
inductive PNCounterOp (P : Type*) where
  /-- Increment originated at replica `p`. -/
  | inc (p : P)
  /-- Decrement originated at replica `p`. -/
  | dec (p : P)
  deriving @[expose] DecidableEq

/-- Replicated increment/decrement counter (`PN-Counter`, [ShapiroPreguicaBaqueroZawirski2011],
§4.1, p. 11; [ShapiroPreguicaBaqueroZawirski2011R], §3.1.3, Specification 7, pp. 15–16) pairing
grow-only `pos` and `neg` `GCounter`s. -/
@[ext]
structure PNCounter (P : Type*) where
  /-- Per-replica increment totals. -/
  pos : GCounter P
  /-- Per-replica decrement totals. -/
  neg : GCounter P

instance {P : Type*} [Fintype P] : DecidableEq (PNCounter P) :=
  fun a b => decidable_of_iff (a.pos = b.pos ∧ a.neg = b.neg)
    ⟨fun ⟨h1, h2⟩ => PNCounter.ext h1 h2,
     fun h => ⟨congrArg PNCounter.pos h, congrArg PNCounter.neg h⟩⟩

instance {P : Type*} : SemilatticeSup (PNCounter P) where
  le a b := a.pos ≤ b.pos ∧ a.neg ≤ b.neg
  sup a b := ⟨a.pos ⊔ b.pos, a.neg ⊔ b.neg⟩
  le_refl a := ⟨le_refl a.pos, le_refl a.neg⟩
  le_trans _ _ _ h₁ h₂ := ⟨le_trans h₁.1 h₂.1, le_trans h₁.2 h₂.2⟩
  le_antisymm _ _ h₁ h₂ := PNCounter.ext (le_antisymm h₁.1 h₂.1) (le_antisymm h₁.2 h₂.2)
  le_sup_left _ _ := ⟨le_sup_left, le_sup_left⟩
  le_sup_right _ _ := ⟨le_sup_right, le_sup_right⟩
  sup_le _ _ _ h₁ h₂ := ⟨sup_le h₁.1 h₂.1, sup_le h₁.2 h₂.2⟩

instance {P : Type*} : OrderBot (PNCounter P) where
  bot := ⟨⊥, ⊥⟩
  bot_le _ := ⟨bot_le, bot_le⟩

namespace PNCounter

/-- Initial zero `PNCounter`. -/
@[expose]
def zero (P : Type*) : PNCounter P := ⊥

/-- Increment `pos` at replica `p`. -/
@[expose]
def inc {P : Type*} [DecidableEq P] (p : P) (c : PNCounter P) : PNCounter P :=
  ⟨c.pos.inc p, c.neg⟩

/-- Increment `neg` (decrementing net value) at replica `p`. -/
@[expose]
def dec {P : Type*} [DecidableEq P] (p : P) (c : PNCounter P) : PNCounter P :=
  ⟨c.pos, c.neg.inc p⟩

/-- Apply a `PNCounterOp` to `c`. -/
@[expose]
def applyOp {P : Type*} [DecidableEq P] : PNCounterOp P → PNCounter P → PNCounter P
  | .inc p, c => c.inc p
  | .dec p, c => c.dec p

/-- Signed integer value `(c.pos.value : ℤ) - (c.neg.value : ℤ)`. -/
@[expose]
def value {P : Type*} [Fintype P] (c : PNCounter P) : ℤ :=
  (c.pos.value : ℤ) - (c.neg.value : ℤ)

theorem le_applyOp {P : Type*} [DecidableEq P] (op : PNCounterOp P) (c : PNCounter P) :
    c ≤ c.applyOp op := by
  cases op with
  | inc p => exact ⟨GCounter.le_inc p c.pos, le_refl c.neg⟩
  | dec p => exact ⟨le_refl c.pos, GCounter.le_inc p c.neg⟩

theorem applyOp_comm {P : Type*} [DecidableEq P] (op₁ op₂ : PNCounterOp P) (c : PNCounter P) :
    (c.applyOp op₁).applyOp op₂ = (c.applyOp op₂).applyOp op₁ := by
  cases op₁ <;> cases op₂ <;> simp [applyOp, inc, dec, GCounter.inc_comm]

@[simp]
theorem value_zero {P : Type*} [Fintype P] : (zero P).value = 0 := by
  change ((GCounter.zero P).value : ℤ) - ((GCounter.zero P).value : ℤ) = 0
  simp

@[simp]
theorem value_inc {P : Type*} [Fintype P] [DecidableEq P] (p : P) (c : PNCounter P) :
    (c.inc p).value = c.value + 1 := by
  simp only [value, inc, GCounter.value_inc]
  omega

@[simp]
theorem value_dec {P : Type*} [Fintype P] [DecidableEq P] (p : P) (c : PNCounter P) :
    (c.dec p).value = c.value - 1 := by
  simp only [value, dec, GCounter.value_inc]
  omega

/-- State-based `CvRDT` instance for `PNCounter P`. -/
@[expose]
def cvrdt (P : Type*) [Fintype P] [DecidableEq P] : CvRDT (PNCounter P) (PNCounterOp P) ℤ where
  init := zero P
  query := value
  update := applyOp
  update_infl := le_applyOp

/-- Op-based `CmRDT` instance for `PNCounter P`. -/
@[expose]
def cmrdt (P : Type*) [Fintype P] [DecidableEq P] :
    CmRDT (PNCounter P) (PNCounterOp P) (PNCounterOp P) ℤ where
  init := zero P
  query := value
  prepare op _ := op
  effect := applyOp

theorem cmrdt_effectsCommute {P : Type*} [Fintype P] [DecidableEq P] :
    EffectsCommute (cmrdt P).effect :=
  fun op₁ op₂ c => applyOp_comm op₂ op₁ c

/-- Exact multi-replica net difference specification step (toward #7502, after
[ShapiroPreguicaBaqueroZawirski2011R], §3.1.3, Specification 7, pp. 15–16). -/
theorem value_sup_of_local_counts {P : Type*} [Fintype P] [Nonempty P]
    (rep : P → PNCounter P) (incK decK : P → ℕ)
    (hpos_own : ∀ p, (rep p).pos.counts p = incK p)
    (hpos_le : ∀ q p, (rep q).pos.counts p ≤ incK p)
    (hneg_own : ∀ p, (rep p).neg.counts p = decK p)
    (hneg_le : ∀ q p, (rep q).neg.counts p ≤ decK p) :
    (Finset.univ.sup' Finset.univ_nonempty rep).value =
      ((∑ p : P, incK p : ℕ) : ℤ) - ((∑ p : P, decK p : ℕ) : ℤ) := by
  rw [value, Finset.apply_sup'_eq_sup'_comp Finset.univ_nonempty PNCounter.pos (fun _ _ => rfl),
    Finset.apply_sup'_eq_sup'_comp Finset.univ_nonempty PNCounter.neg (fun _ _ => rfl)]
  dsimp only [Function.comp_def]
  rw [GCounter.value_sup_of_local_counts _ incK hpos_own hpos_le,
    GCounter.value_sup_of_local_counts _ decK hneg_own hneg_le]

end PNCounter

/-! ### `GSet` and `TwoPhaseSet` (`2P-Set`) -/

/-- State-based Grow-Only Set (`G-Set`, [ShapiroPreguicaBaqueroZawirski2011R], §3.3.1,
Specification 11, p. 22) over Mathlib's `SemilatticeSup (Finset α)`. -/
@[expose]
def gsetCvRDT (α : Type*) [DecidableEq α] : CvRDT (Finset α) α (Finset α) where
  init := ∅
  query := id
  update := insert
  update_infl := Finset.subset_insert

/-- Op-based Grow-Only Set (`G-Set`, [ShapiroPreguicaBaqueroZawirski2011R], §3.3.1, pp. 21–22). -/
@[expose]
def gsetCmRDT (α : Type*) [DecidableEq α] : CmRDT (Finset α) α α (Finset α) where
  init := ∅
  query := id
  prepare x _ := x
  effect := insert

theorem gsetCmRDT_effectsCommute {α : Type*} [DecidableEq α] :
    EffectsCommute (gsetCmRDT α).effect :=
  fun x y s => Finset.insert_comm x y s

/-- Set mutation operations (`add` and `remove`). -/
inductive SetOp (α : Type*) where
  /-- Add `x` to the set. -/
  | add (x : α)
  /-- Remove `x` from the set. -/
  | remove (x : α)
  deriving @[expose] DecidableEq

/-- State-based Two-Phase Set (`2P-Set`, [ShapiroPreguicaBaqueroZawirski2011R], §3.3.2,
Specification 12, p. 22) combining an `added` set and a permanent `removed` tombstone set. -/
@[ext]
structure TwoPhaseSet (α : Type*) where
  /-- Elements ever added. -/
  added : Finset α
  /-- Tombstone set of elements ever removed. -/
  removed : Finset α
  deriving @[expose] DecidableEq

instance {α : Type*} [DecidableEq α] : SemilatticeSup (TwoPhaseSet α) where
  le a b := a.added ⊆ b.added ∧ a.removed ⊆ b.removed
  sup a b := ⟨a.added ∪ b.added, a.removed ∪ b.removed⟩
  le_refl a := ⟨Finset.Subset.refl a.added, Finset.Subset.refl a.removed⟩
  le_trans _ _ _ h₁ h₂ := ⟨Finset.Subset.trans h₁.1 h₂.1, Finset.Subset.trans h₁.2 h₂.2⟩
  le_antisymm _ _ h₁ h₂ :=
    TwoPhaseSet.ext (Finset.Subset.antisymm h₁.1 h₂.1) (Finset.Subset.antisymm h₁.2 h₂.2)
  le_sup_left _ _ := ⟨Finset.subset_union_left, Finset.subset_union_left⟩
  le_sup_right _ _ := ⟨Finset.subset_union_right, Finset.subset_union_right⟩
  sup_le _ _ _ h₁ h₂ := ⟨Finset.union_subset h₁.1 h₂.1, Finset.union_subset h₁.2 h₂.2⟩

instance {α : Type*} [DecidableEq α] : OrderBot (TwoPhaseSet α) where
  bot := ⟨∅, ∅⟩
  bot_le _ := ⟨Finset.empty_subset _, Finset.empty_subset _⟩

namespace TwoPhaseSet

variable {α : Type*} [DecidableEq α]

/-- Initial empty `TwoPhaseSet`. -/
@[expose]
def empty : TwoPhaseSet α := ⊥

/-- Currently visible elements `s.added \ s.removed`. -/
@[expose]
def elements (s : TwoPhaseSet α) : Finset α :=
  s.added \ s.removed

/-- Add `x` to `s.added`. -/
@[expose]
def add (x : α) (s : TwoPhaseSet α) : TwoPhaseSet α :=
  ⟨insert x s.added, s.removed⟩

/-- Tombstone `x` in `s.removed`. -/
@[expose]
def remove (x : α) (s : TwoPhaseSet α) : TwoPhaseSet α :=
  ⟨s.added, insert x s.removed⟩

/-- Apply `SetOp` to `TwoPhaseSet`. -/
@[expose]
def applyOp : SetOp α → TwoPhaseSet α → TwoPhaseSet α
  | .add x, s => s.add x
  | .remove x, s => s.remove x

theorem le_applyOp (op : SetOp α) (s : TwoPhaseSet α) : s ≤ s.applyOp op := by
  cases op with
  | add x => exact ⟨Finset.subset_insert x s.added, Finset.Subset.refl s.removed⟩
  | remove x => exact ⟨Finset.Subset.refl s.added, Finset.subset_insert x s.removed⟩

theorem applyOp_comm (op₁ op₂ : SetOp α) (s : TwoPhaseSet α) :
    (s.applyOp op₁).applyOp op₂ = (s.applyOp op₂).applyOp op₁ := by
  cases op₁ <;> cases op₂ <;> simp [applyOp, add, remove, Finset.insert_comm]

/-- State-based `CvRDT` instance for `TwoPhaseSet α`. -/
@[expose]
def cvrdt : CvRDT (TwoPhaseSet α) (SetOp α) (Finset α) where
  init := empty
  query := elements
  update := applyOp
  update_infl := le_applyOp

/-- Op-based `CmRDT` instance for `TwoPhaseSet α`. -/
@[expose]
def cmrdt : CmRDT (TwoPhaseSet α) (SetOp α) (SetOp α) (Finset α) where
  init := empty
  query := elements
  prepare op _ := op
  effect := applyOp

theorem cmrdt_effectsCommute : EffectsCommute (cmrdt (α := α)).effect :=
  fun op₁ op₂ s => applyOp_comm op₂ op₁ s

/-- Monotonic tombstone permanence step (toward #7502, after
[ShapiroPreguicaBaqueroZawirski2011R], §3.3.2, pp. 22–23): once `x ∈ s.removed`, `x` remains
tombstoned and absent from `s'.elements` in every semilattice successor `s' ≥ s` (including after
any subsequent `add x` or merge). -/
theorem not_mem_elements_of_le_of_removed {s s' : TwoPhaseSet α} {x : α}
    (hrem : x ∈ s.removed) (hle : s ≤ s') :
    x ∈ s'.removed ∧ x ∉ s'.elements :=
  ⟨hle.2 hrem, fun hmem => (Finset.mem_sdiff.mp hmem).2 (hle.2 hrem)⟩

@[simp]
theorem not_mem_readd_after_remove (s : TwoPhaseSet α) (x : α) :
    x ∉ ((s.remove x).add x).elements :=
  (not_mem_elements_of_le_of_removed (Finset.mem_insert_self x s.removed)
    (le_applyOp (.add x) (s.remove x))).2

/-- Remove-wins under concurrent `add x` and `remove x` in `TwoPhaseSet α`. -/
theorem remove_wins_concurrent (s₁ s₂ : TwoPhaseSet α) (x : α) :
    x ∉ ((s₁.add x) ⊔ (s₂.remove x)).elements :=
  (not_mem_elements_of_le_of_removed (Finset.mem_insert_self x s₂.removed) le_sup_right).2

end TwoPhaseSet

/-! ### `ORSet`: Observed-Remove Set with Unique `(P × ℕ)` Tags -/

/-- A uniquely tagged set entry `(elem, replica, seq)` in an Observed-Remove Set (`OR-Set`,
[ShapiroPreguicaBaqueroZawirski2011R], §3.3.5, Specification 15, p. 26), pairing `elem : α` with a
source-generated `(replica, seq) : P × ℕ` tag. -/
@[ext]
structure TaggedElem (P α : Type*) where
  /-- Added set element. -/
  elem : α
  /-- Originating replica identity. -/
  replica : P
  /-- Per-replica sequence number uniquely tagging this `add`. -/
  seq : ℕ
  deriving @[expose] DecidableEq

/-- Operations on an Observed-Remove Set: `add p seq x` (adding `x` with fresh source tag
`(p, seq)`) and `remove x` (removing all currently observed tags of `x` at the source replica). -/
inductive ORSetOp (P α : Type*) where
  /-- Add `x` tagged with fresh `(p, seq)`. -/
  | add (p : P) (seq : ℕ) (x : α)
  /-- Remove all currently observed tags of `x`. -/
  | remove (x : α)
  deriving @[expose] DecidableEq

/-- State-based Observed-Remove Set (`ORSetCv`, [ShapiroPreguicaBaqueroZawirski2011R], §3.3.5,
p. 27) maintaining `entries` and `tombstones` over `TaggedElem P α`. -/
@[ext]
structure ORSetCv (P α : Type*) where
  /-- All tagged entries ever added. -/
  entries : Finset (TaggedElem P α)
  /-- Tagged entries explicitly observed and tombstoned by `remove`. -/
  tombstones : Finset (TaggedElem P α)
  deriving @[expose] DecidableEq

instance {P α : Type*} [DecidableEq P] [DecidableEq α] : SemilatticeSup (ORSetCv P α) where
  le a b := a.entries ⊆ b.entries ∧ a.tombstones ⊆ b.tombstones
  sup a b := ⟨a.entries ∪ b.entries, a.tombstones ∪ b.tombstones⟩
  le_refl a := ⟨Finset.Subset.refl a.entries, Finset.Subset.refl a.tombstones⟩
  le_trans _ _ _ h₁ h₂ := ⟨Finset.Subset.trans h₁.1 h₂.1, Finset.Subset.trans h₁.2 h₂.2⟩
  le_antisymm _ _ h₁ h₂ :=
    ORSetCv.ext (Finset.Subset.antisymm h₁.1 h₂.1) (Finset.Subset.antisymm h₁.2 h₂.2)
  le_sup_left _ _ := ⟨Finset.subset_union_left, Finset.subset_union_left⟩
  le_sup_right _ _ := ⟨Finset.subset_union_right, Finset.subset_union_right⟩
  sup_le _ _ _ h₁ h₂ := ⟨Finset.union_subset h₁.1 h₂.1, Finset.union_subset h₁.2 h₂.2⟩

instance {P α : Type*} [DecidableEq P] [DecidableEq α] : OrderBot (ORSetCv P α) where
  bot := ⟨∅, ∅⟩
  bot_le _ := ⟨Finset.empty_subset _, Finset.empty_subset _⟩

namespace ORSetCv

variable {P α : Type*} [DecidableEq P] [DecidableEq α]

/-- Initial empty state-based `ORSetCv`. -/
@[expose]
def empty : ORSetCv P α := ⊥

/-- Visible set elements `(s.entries \ s.tombstones).image TaggedElem.elem`. -/
@[expose]
def elements (s : ORSetCv P α) : Finset α :=
  (s.entries \ s.tombstones).image TaggedElem.elem

/-- Add `x` with tag `(p, seq)` to `s.entries`. -/
@[expose]
def add (p : P) (seq : ℕ) (x : α) (s : ORSetCv P α) : ORSetCv P α :=
  ⟨insert ⟨x, p, seq⟩ s.entries, s.tombstones⟩

/-- Remove `x` by tombstoning **only** the tags of `x` currently observed in `s.entries`. -/
@[expose]
def removeObserved (x : α) (s : ORSetCv P α) : ORSetCv P α :=
  ⟨s.entries, s.tombstones ∪ s.entries.filter (fun t => t.elem = x)⟩

/-- Apply `ORSetOp` to `ORSetCv`. -/
@[expose]
def applyOp : ORSetOp P α → ORSetCv P α → ORSetCv P α
  | .add p seq x, s => s.add p seq x
  | .remove x, s => s.removeObserved x

theorem le_applyOp (op : ORSetOp P α) (s : ORSetCv P α) : s ≤ s.applyOp op := by
  cases op with
  | add p seq x => exact ⟨Finset.subset_insert _ s.entries, Finset.Subset.refl _⟩
  | remove x => exact ⟨Finset.Subset.refl _, Finset.subset_union_left⟩

/-- State-based `CvRDT` instance for `ORSetCv P α`. -/
@[expose]
def cvrdt : CvRDT (ORSetCv P α) (ORSetOp P α) (Finset α) where
  init := empty
  query := elements
  update := applyOp
  update_infl := le_applyOp

@[simp]
theorem not_mem_removeObserved (s : ORSetCv P α) (x : α) :
    x ∉ (s.removeObserved x).elements := by
  simp only [elements, removeObserved, Finset.mem_image, Finset.mem_sdiff, Finset.mem_union,
    Finset.mem_filter]
  rintro ⟨t, ⟨ht_ent, ht_not⟩, rfl⟩
  exact ht_not (Or.inr ⟨ht_ent, rfl⟩)

/-- State-based concurrent add-wins step (toward #7502, after
[ShapiroPreguicaBaqueroZawirski2011R], §3.3.5, Figure 14, p. 27): if `s₂` adds `x` with a fresh tag
`⟨x, p, seq⟩` not observed at `s₁` and not already tombstoned, merging `s₁.removeObserved x` with
`s₂.add p seq x` retains `x`. -/
theorem mem_sup_removeObserved_add {s₁ s₂ : ORSetCv P α} {p : P} {seq : ℕ} {x : α}
    (hunobs : ⟨x, p, seq⟩ ∉ s₁.entries)
    (hnot_tomb₁ : ⟨x, p, seq⟩ ∉ s₁.tombstones)
    (hnot_tomb₂ : ⟨x, p, seq⟩ ∉ s₂.tombstones) :
    x ∈ ((s₁.removeObserved x) ⊔ (s₂.add p seq x)).elements := by
  simp only [elements, Finset.mem_image, Finset.mem_sdiff]
  refine ⟨⟨x, p, seq⟩, ⟨Finset.mem_union_right _ (Finset.mem_insert_self _ _), fun htomb => ?_⟩,
    rfl⟩
  rcases Finset.mem_union.mp htomb with ht₁ | ht₂
  · exact (Finset.mem_union.mp ht₁).elim hnot_tomb₁ fun h => hunobs (Finset.mem_filter.mp h).1
  · exact hnot_tomb₂ ht₂

/-- State-based sequential re-add after remove: unlike `TwoPhaseSet`, adding `x` with a fresh tag
`⟨x, p, seq⟩` after `s.removeObserved x` restores `x ∈ elements`. -/
theorem mem_add_after_removeObserved {s : ORSetCv P α} {p : P} {seq : ℕ} {x : α}
    (hfresh_ent : ⟨x, p, seq⟩ ∉ s.entries)
    (hfresh_tomb : ⟨x, p, seq⟩ ∉ s.tombstones) :
    x ∈ ((s.removeObserved x).add p seq x).elements := by
  simp only [elements, add, removeObserved, Finset.mem_image, Finset.mem_sdiff,
    Finset.mem_union, Finset.mem_filter]
  refine ⟨⟨x, p, seq⟩, ⟨Finset.mem_insert_self _ _, ?_⟩, rfl⟩
  rintro (htomb | ⟨hent, _⟩)
  · exact hfresh_tomb htomb
  · exact hfresh_ent hent

end ORSetCv

/-- Downstream effect payloads of the op-based Observed-Remove Set (`OR-Set`,
[ShapiroPreguicaBaqueroZawirski2011R], §3.3.5, Specification 15, p. 26). -/
inductive ORSetEff (P α : Type*) where
  /-- Downstream insertion of a uniquely tagged entry `t`. -/
  | addTag (t : TaggedElem P α)
  /-- Downstream removal of the finite set `R` of tagged entries observed at the source replica. -/
  | removeTags (R : Finset (TaggedElem P α))
  deriving @[expose] DecidableEq

/-- Downstream state transformer of the op-based `OR-Set` on `Finset (TaggedElem P α)`. -/
@[expose]
def orsetEffect {P α : Type*} [DecidableEq P] [DecidableEq α] :
    ORSetEff P α → Finset (TaggedElem P α) → Finset (TaggedElem P α)
  | .addTag t, s => insert t s
  | .removeTags R, s => s \ R

/-- Query extracting visible `α` elements from an op-based `OR-Set` payload. -/
@[expose]
def orsetElements {P α : Type*} [DecidableEq α] (s : Finset (TaggedElem P α)) : Finset α :=
  s.image TaggedElem.elem

/-- Op-based `CmRDT` instance for the Observed-Remove Set (`OR-Set`, Specification 15,
[ShapiroPreguicaBaqueroZawirski2011R], §3.3.5, p. 26). -/
@[expose]
def orsetCmRDT (P α : Type*) [DecidableEq P] [DecidableEq α] :
    CmRDT (Finset (TaggedElem P α)) (ORSetOp P α) (ORSetEff P α) (Finset α) where
  init := ∅
  query := orsetElements
  prepare op s :=
    match op with
    | .add p seq x => .addTag ⟨x, p, seq⟩
    | .remove x => .removeTags (s.filter (fun t => t.elem = x))
  effect := orsetEffect

/-- Set of tagged entries surviving in causal history `H` under causal precedence `prec`: tagged
entries `⟨x, p, seq⟩` generated by an `add p seq x` event `e ∈ H` not causally followed (`prec`)
by any `remove x` event `r ∈ H`. -/
@[expose]
def orsetSurvivingTags {P α Ev : Type*} [DecidableEq P] [DecidableEq α]
    (prec : Ev → Ev → Prop) [DecidableRel prec]
    (opOf : Ev → ORSetOp P α) (H : Finset Ev) : Finset (TaggedElem P α) :=
  H.biUnion fun e =>
    match opOf e with
    | .add p seq x =>
        if ∃ r ∈ H, opOf r = .remove x ∧ prec e r then ∅ else {⟨x, p, seq⟩}
    | .remove _ => ∅

@[simp]
theorem mem_orsetSurvivingTags_iff {P α Ev : Type*} [DecidableEq P] [DecidableEq α]
    {prec : Ev → Ev → Prop} [DecidableRel prec]
    {opOf : Ev → ORSetOp P α} {H : Finset Ev} {t : TaggedElem P α} :
    t ∈ orsetSurvivingTags prec opOf H ↔
      ∃ e ∈ H, opOf e = .add t.replica t.seq t.elem ∧
        ¬ ∃ r ∈ H, opOf r = .remove t.elem ∧ prec e r := by
  simp only [orsetSurvivingTags, Finset.mem_biUnion]
  constructor
  · rintro ⟨e, heH, hmem⟩
    cases hop : opOf e with
    | add p seq x =>
      rw [hop] at hmem
      dsimp only at hmem
      split_ifs at hmem with hrem
      · simp at hmem
      · obtain rfl := Finset.mem_singleton.mp hmem
        exact ⟨e, heH, hop, hrem⟩
    | remove x => simp [hop] at hmem
  · rintro ⟨e, heH, hop, hnot_rem⟩
    exact ⟨e, heH, by simp [hop, hnot_rem]⟩

/-- Well-formed finite causally closed `OR-Set` execution history `H : Finset Ev` under strict
partial order `prec` ([ShapiroPreguicaBaqueroZawirski2011R], §3.3.5, Specification 15, p. 26):
1. `H` is causally closed (`IsCausallyClosed prec H`);
2. distinct `add` events in `H` allocate distinct `(replica, seq)` tags (`unique_add_tag`);
3. each `add p n x` prepares `.addTag ⟨x, p, n⟩`; and
4. each `remove x` event `e ∈ H` prepares `.removeTags` from the tags of `x` present in its source
   replica's state after some causal linearization `l_src` of `e`'s causal past
   `H.filter (fun u => prec u e)`. -/
structure ORSetCausalHistory (P α Ev : Type*) [DecidableEq P] [DecidableEq α] [DecidableEq Ev]
    (prec : Ev → Ev → Prop) [DecidableRel prec] (H : Finset Ev) where
  /-- Causal closure of `H`. -/
  closed : IsCausallyClosed prec H
  /-- Client operation invoked at each event. -/
  opOf : Ev → ORSetOp P α
  /-- Downstream effect prepared at the source of each event. -/
  effOf : Ev → ORSetEff P α
  /-- Uniqueness of `(replica, seq)` tags across `add` events in `H`. -/
  unique_add_tag :
    ∀ e₁ ∈ H, ∀ e₂ ∈ H, ∀ p₁ n₁ x₁ p₂ n₂ x₂,
      opOf e₁ = .add p₁ n₁ x₁ → opOf e₂ = .add p₂ n₂ x₂ → p₁ = p₂ → n₁ = n₂ → e₁ = e₂
  /-- Prepare specification for `add` events. -/
  eff_add : ∀ e ∈ H, ∀ p n x, opOf e = .add p n x → effOf e = .addTag ⟨x, p, n⟩
  /-- Prepare specification for `remove` events against the source replica's delivered causal
  past `H.filter (fun u => prec u e)`. -/
  eff_remove :
    ∀ e ∈ H, ∀ x, opOf e = .remove x →
      ∃ l_src : List Ev,
        IsCausalLinearization prec (H.filter (fun u => prec u e)) l_src ∧
        effOf e = .removeTags
          ((l_src.foldl (fun s u => orsetEffect (effOf u) s) ∅).filter (fun t => t.elem = x))

section ORSetProofs

variable {P α Ev : Type*} [DecidableEq P] [DecidableEq α] [DecidableEq Ev]
  {prec : Ev → Ev → Prop} [IsStrictOrder Ev prec] [DecidableRel prec]

/-- Restricting an `ORSetCausalHistory` to any causally closed subset `H' ⊆ H` preserves all
history invariants because `H'.filter (prec · e) = H.filter (prec · e)` for every `e ∈ H'`. -/
private def ORSetCausalHistory.restrict {H H' : Finset Ev}
    (hH : ORSetCausalHistory P α Ev prec H) (hsub : H' ⊆ H)
    (hclosed' : IsCausallyClosed prec H') :
    ORSetCausalHistory P α Ev prec H' where
  closed := hclosed'
  opOf := hH.opOf
  effOf := hH.effOf
  unique_add_tag e₁ he₁ e₂ he₂ := hH.unique_add_tag e₁ (hsub he₁) e₂ (hsub he₂)
  eff_add e he := hH.eff_add e (hsub he)
  eff_remove e he x hop := by
    have hfilt : H'.filter (fun u => prec u e) = H.filter (fun u => prec u e) := by
      ext u
      simp only [Finset.mem_filter]
      exact ⟨fun ⟨hu, hp⟩ => ⟨hsub hu, hp⟩, fun ⟨_, hp⟩ => ⟨hclosed' e he u hp, hp⟩⟩
    rw [hfilt]
    exact hH.eff_remove e (hsub he) x hop

omit [DecidableEq Ev] in
private theorem isCausallyClosed_past {H : Finset Ev} (hclosed : IsCausallyClosed prec H)
    (e : Ev) : IsCausallyClosed prec (H.filter (fun u => prec u e)) := by
  intro u hu v hvu
  obtain ⟨huH, hue⟩ := Finset.mem_filter.mp hu
  exact Finset.mem_filter.mpr ⟨hclosed u huH v hvu, _root_.trans hvu hue⟩

omit [DecidableEq Ev] in
private theorem card_past_lt {H : Finset Ev} {e : Ev} (he : e ∈ H) :
    (H.filter (fun u => prec u e)).card < H.card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ H)]
  exact ⟨e, he, fun hmem => irrefl e (Finset.mem_filter.mp hmem).2⟩

private theorem orset_main_ind (n : ℕ) :
    ∀ (H : Finset Ev) (hH : ORSetCausalHistory P α Ev prec H), H.card = n →
      ConcurrentCommute orsetEffect prec hH.effOf (H : Set Ev) ∧
      ∀ l : List Ev, IsCausalLinearization prec H l →
        l.foldl (fun s e => orsetEffect (hH.effOf e) s) ∅ =
          orsetSurvivingTags prec hH.opOf H := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro H hH hcard
    -- Step 1: By strong induction on strict causal pasts `P_e ⊂ H`, identify `effOf e` for every
    -- `remove x` event `e ∈ H` directly in terms of `orsetSurvivingTags`.
    have hrem_eq (e : Ev) (he : e ∈ H) (x : α) (hop : hH.opOf e = .remove x) :
        hH.effOf e = .removeTags
          ((orsetSurvivingTags prec hH.opOf (H.filter (fun u => prec u e))).filter
            (fun t => t.elem = x)) := by
      let P_e := H.filter (fun u => prec u e)
      obtain ⟨l_src, hl_src, heff⟩ := hH.eff_remove e he x hop
      have hfold : l_src.foldl (fun s u => orsetEffect (hH.effOf u) s) ∅ =
          orsetSurvivingTags prec hH.opOf P_e :=
        (ih P_e.card (hcard ▸ card_past_lt he) P_e
          (hH.restrict (Finset.filter_subset _ H) (isCausallyClosed_past hH.closed e))
          rfl).2 l_src hl_src
      rwa [hfold] at heff
    -- Step 2: Prove `ConcurrentCommute` on `H`.
    have h_add_rem (a : Ev) (haH : a ∈ H) (r : Ev) (hrH : r ∈ H) (p : P) (n : ℕ) (xa xr : α)
        (hop_a : hH.opOf a = .add p n xa) (hop_r : hH.opOf r = .remove xr)
        (hnot_prec : ¬ prec a r) (s : Finset (TaggedElem P α)) :
        orsetEffect (hH.effOf a) (orsetEffect (hH.effOf r) s) =
          orsetEffect (hH.effOf r) (orsetEffect (hH.effOf a) s) := by
      rw [hH.eff_add a haH p n xa hop_a, hrem_eq r hrH xr hop_r]
      simp only [orsetEffect]
      refine (Finset.insert_sdiff_of_notMem s fun hmem => ?_).symm
      obtain ⟨hsurv, -⟩ := Finset.mem_filter.mp hmem
      obtain ⟨u, huP, hu_op, -⟩ := mem_orsetSurvivingTags_iff.mp hsurv
      exact hnot_prec (hH.unique_add_tag u (Finset.mem_filter.mp huP).1 a haH p n xa p n xa
        hu_op hop_a rfl rfl ▸ (Finset.mem_filter.mp huP).2)
    have hcomm : ConcurrentCommute orsetEffect prec hH.effOf (H : Set Ev) := by
      intro e₁ he₁ e₂ he₂ _ hn₁₂ hn₂₁ s
      cases hop₁ : hH.opOf e₁ with
      | add p₁ n₁ x₁ =>
        cases hop₂ : hH.opOf e₂ with
        | add p₂ n₂ x₂ =>
          rw [hH.eff_add e₁ he₁ p₁ n₁ x₁ hop₁, hH.eff_add e₂ he₂ p₂ n₂ x₂ hop₂]
          exact Finset.insert_comm _ _ s
        | remove x₂ =>
          exact h_add_rem e₁ he₁ e₂ he₂ p₁ n₁ x₁ x₂ hop₁ hop₂ hn₁₂ s
      | remove x₁ =>
        cases hop₂ : hH.opOf e₂ with
        | add p₂ n₂ x₂ =>
          exact (h_add_rem e₂ he₂ e₁ he₁ p₂ n₂ x₂ x₁ hop₂ hop₁ hn₂₁ s).symm
        | remove x₂ =>
          rw [hrem_eq e₁ he₁ x₁ hop₁, hrem_eq e₂ he₂ x₂ hop₂]
          exact sdiff_sdiff_comm
    -- Step 3: Prove every causal linearization `l` of `H` folds to `orsetSurvivingTags`.
    refine ⟨hcomm, fun l hl => ?_⟩
    rcases l.eq_nil_or_concat with rfl | ⟨initL, e_last, hconcat⟩
    · obtain rfl : H = ∅ := Finset.ext fun e => by simpa using (hl.2.1 e).symm
      simp [orsetSurvivingTags]
    · rw [List.concat_eq_append] at hconcat
      subst hconcat
      have he_last_mem_l : e_last ∈ initL ++ [e_last] :=
        List.mem_append_right initL List.mem_cons_self
      have he_last_H : e_last ∈ H := (hl.2.1 e_last).mp he_last_mem_l
      obtain ⟨hnodup_init, _, hdisj⟩ := List.nodup_append.mp hl.1
      have he_not_init : e_last ∉ initL := fun h => hdisj e_last h e_last List.mem_cons_self rfl
      -- `e_last` is `prec`-maximal in `H` as the final entry of `initL ++ [e_last]`.
      have he_max (y : Ev) (hyH : y ∈ H) (hprec : prec e_last y) : False := by
        have hy_l : y ∈ initL ++ [e_last] := (hl.2.1 y).mpr hyH
        have hidx_lt := hl.2.2 e_last he_last_mem_l y hy_l hprec
        have hidx_y := List.idxOf_lt_length_of_mem hy_l
        simp only [List.idxOf_append_of_notMem he_not_init, List.idxOf_cons_self, Nat.add_zero,
          List.length_append, List.length_singleton] at hidx_lt hidx_y
        omega
      let H' := H.erase e_last
      have hH'_sub : H' ⊆ H := Finset.erase_subset e_last H
      have hH'_closed : IsCausallyClosed prec H' := fun u hu v hvu =>
        let ⟨_, huH⟩ := Finset.mem_erase.mp hu
        Finset.mem_erase.mpr ⟨fun hveq => he_max u huH (hveq ▸ hvu), hH.closed u huH v hvu⟩
      have hlin_init : IsCausalLinearization prec H' initL := by
        refine ⟨hnodup_init, fun u => ?_, fun u₁ hu₁ u₂ hu₂ hprec => ?_⟩
        · simp only [H', Finset.mem_erase, ← hl.2.1 u, List.mem_append, List.mem_singleton]
          exact ⟨fun h => ⟨fun h' => he_not_init (h' ▸ h), Or.inl h⟩,
            fun ⟨hne, h⟩ => h.resolve_right hne⟩
        · have hlt_app := hl.2.2 u₁ (List.mem_append_left _ hu₁)
            u₂ (List.mem_append_left _ hu₂) hprec
          rwa [List.idxOf_append_of_mem hu₁, List.idxOf_append_of_mem hu₂] at hlt_app
      have hfold_init : initL.foldl (fun s e => orsetEffect (hH.effOf e) s) ∅ =
          orsetSurvivingTags prec hH.opOf H' :=
        (ih H'.card (hcard ▸ Finset.card_erase_lt_of_mem he_last_H) H'
          (hH.restrict hH'_sub hH'_closed) rfl).2 initL hlin_init
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hfold_init]
      -- Compare `orsetEffect (effOf e_last) (orsetSurvivingTags H')` with `orsetSurvivingTags H`.
      cases hop_last : hH.opOf e_last with
      | add p₀ n₀ x₀ =>
        rw [hH.eff_add e_last he_last_H p₀ n₀ x₀ hop_last]
        simp only [orsetEffect]
        ext t
        simp only [Finset.mem_insert, mem_orsetSurvivingTags_iff]
        constructor
        · rintro (rfl | ⟨u, huH', hu_op, hnot_r⟩)
          · exact ⟨e_last, he_last_H, hop_last, fun ⟨r, hrH, _, hprec⟩ => he_max r hrH hprec⟩
          · refine ⟨u, hH'_sub huH', hu_op, fun ⟨r, hrH, hr_op, hprec⟩ => ?_⟩
            rcases eq_or_ne r e_last with rfl | hre
            · nomatch hop_last.symm.trans hr_op
            · exact hnot_r ⟨r, Finset.mem_erase.mpr ⟨hre, hrH⟩, hr_op, hprec⟩
        · rintro ⟨u, huH, hu_op, hnot_r⟩
          rcases eq_or_ne u e_last with rfl | hue
          · cases hop_last.symm.trans hu_op
            exact Or.inl (TaggedElem.ext rfl rfl rfl)
          · exact Or.inr ⟨u, Finset.mem_erase.mpr ⟨hue, huH⟩, hu_op,
              fun ⟨r, hrH', hr_op, hprec⟩ => hnot_r ⟨r, hH'_sub hrH', hr_op, hprec⟩⟩
      | remove x₀ =>
        rw [hrem_eq e_last he_last_H x₀ hop_last]
        simp only [orsetEffect]
        ext t
        simp only [Finset.mem_sdiff, Finset.mem_filter, mem_orsetSurvivingTags_iff]
        constructor
        · rintro ⟨⟨u, huH', hu_op, hnot_r'⟩, hnot_filt⟩
          refine ⟨u, hH'_sub huH', hu_op, fun ⟨r, hrH, hr_op, hprec⟩ => ?_⟩
          rcases eq_or_ne r e_last with rfl | hre
          · cases hop_last.symm.trans hr_op
            exact hnot_filt ⟨⟨u, ⟨hH'_sub huH', hprec⟩, hu_op,
              fun ⟨r', ⟨hr'H, hr'_last⟩, hr'_op, hp'⟩ =>
                hnot_r' ⟨r', Finset.mem_erase.mpr ⟨fun e => irrefl r (e ▸ hr'_last), hr'H⟩,
                  hr'_op, hp'⟩⟩, rfl⟩
          · exact hnot_r' ⟨r, Finset.mem_erase.mpr ⟨hre, hrH⟩, hr_op, hprec⟩
        · rintro ⟨u, huH, hu_op, hnot_r⟩
          have hue : u ≠ e_last := fun heq => by cases hop_last.symm.trans (heq ▸ hu_op)
          refine ⟨⟨u, Finset.mem_erase.mpr ⟨hue, huH⟩, hu_op,
            fun ⟨r, hrH', hr_op, hprec⟩ => hnot_r ⟨r, hH'_sub hrH', hr_op, hprec⟩⟩, ?_⟩
          rintro ⟨⟨u', ⟨hu'H, hu'_prec⟩, hu'_op, _⟩, htelem⟩
          exact hnot_r ⟨e_last, he_last_H, htelem ▸ hop_last,
            hH.unique_add_tag u' hu'H u huH t.replica t.seq t.elem t.replica t.seq t.elem
              hu'_op hu_op rfl rfl ▸ hu'_prec⟩

/-- Op-based `OR-Set` concurrent commutativity step (toward #7502, after
[ShapiroPreguicaBaqueroZawirski2011R], §3.3.5, Specification 15, pp. 26–27): in any well-formed
causal history `hH`, concurrent downstream `OR-Set` effects commute. -/
theorem ORSetCausalHistory.concurrentCommute {H : Finset Ev}
    (hH : ORSetCausalHistory P α Ev prec H) :
    ConcurrentCommute orsetEffect prec hH.effOf (H : Set Ev) :=
  (orset_main_ind H.card H hH rfl).1

/-- Op-based `OR-Set` exact tag-state evaluation step (toward #7502, after
[ShapiroPreguicaBaqueroZawirski2011R], §3.3.5, Specification 15, pp. 26–27): every causal
linearization `l` of `H` evaluates to `orsetSurvivingTags prec hH.opOf H`. -/
theorem ORSetCausalHistory.foldl_eq_survivingTags {H : Finset Ev}
    (hH : ORSetCausalHistory P α Ev prec H) {l : List Ev}
    (hl : IsCausalLinearization prec H l) :
    l.foldl (fun s e => orsetEffect (hH.effOf e) s) ∅ =
      orsetSurvivingTags prec hH.opOf H :=
  (orset_main_ind H.card H hH rfl).2 l hl

/-- Op-based `OR-Set` **Causal Add-Wins Specification** step (toward #7502, after
[ShapiroPreguicaBaqueroZawirski2011R], §3.3.5, Specification 15 & Figure 14, pp. 26–27): after any
causal linearization `l` of `H`, element `x` belongs to `orsetElements` iff `H` contains an
`add p n x` event `e_add` that is not causally followed (`prec`) by any `remove x` event
`e_rem ∈ H`. -/
theorem ORSetCausalHistory.mem_elements_iff_causal_add_wins {H : Finset Ev}
    (hH : ORSetCausalHistory P α Ev prec H) {l : List Ev}
    (hl : IsCausalLinearization prec H l) (x : α) :
    x ∈ orsetElements (l.foldl (fun s e => orsetEffect (hH.effOf e) s) ∅) ↔
      ∃ e_add ∈ H, (∃ p n, hH.opOf e_add = .add p n x) ∧
        ¬ ∃ e_rem ∈ H, hH.opOf e_rem = .remove x ∧ prec e_add e_rem := by
  simp only [hH.foldl_eq_survivingTags hl, orsetElements, Finset.mem_image,
    mem_orsetSurvivingTags_iff]
  exact ⟨fun ⟨t, ⟨e, heH, hop, hnot_r⟩, htx⟩ => ⟨e, heH, htx ▸ ⟨⟨t.replica, t.seq, hop⟩, hnot_r⟩⟩,
    fun ⟨e, heH, ⟨p, n, hop⟩, hnot_r⟩ => ⟨⟨x, p, n⟩, ⟨e, heH, hop, hnot_r⟩, rfl⟩⟩

end ORSetProofs

/-! ### Untagged Set Merge Impossibility and Naïve Op-Based Non-Commutativity -/

/-- Untagged set state-merge impossibility (original to this library, formalizing the untagged
add/remove conflict motivation of [ShapiroPreguicaBaqueroZawirski2011R], §3.3, p. 21):
over any nonempty element type `α`, there is no binary commutative merge operation
`merge : Finset α → Finset α → Finset α` on plain untagged sets that simultaneously:
1. propagates a fresh `add` (`insert x ∅ = {x}`) to an untouched peer at `∅`
   (`∀ x, x ∈ merge ∅ (insert x ∅)`), and
2. propagates a sequential `remove`-after-`add` (`({x} : Finset α).erase x = ∅`) to a peer still
   holding `{x}` (`∀ x, x ∉ merge {x} (({x} : Finset α).erase x)`),
because without per-addition tags or tombstones both executions yield the same unordered pair of
replica states `{∅, {x}}`. -/
theorem not_exists_untagged_finset_merge {α : Type*} [DecidableEq α] [Nonempty α] :
    ¬ ∃ (merge : Finset α → Finset α → Finset α),
        Std.Commutative merge ∧
        (∀ x : α, x ∈ merge ∅ (insert x ∅)) ∧
        (∀ x : α, x ∉ merge {x} (({x} : Finset α).erase x)) := by
  rintro ⟨merge, hcomm, hadd, hrem⟩
  obtain ⟨x⟩ := ‹Nonempty α›
  have hr := hrem x
  rw [Finset.erase_singleton, hcomm.comm {x} ∅] at hr
  exact hr (hadd x)

/-- Naïve op-based untagged `insert`/`erase` non-commutativity step (toward #7502, after
[ShapiroPreguicaBaqueroZawirski2011R], §3.3, Figure 11, p. 21). -/
theorem untagged_insert_erase_ne_erase_insert {α : Type*} [DecidableEq α] (x : α) :
    (insert x (∅ : Finset α)).erase x ≠ insert x ((∅ : Finset α).erase x) := by
  simp

end Cslib.Distributed.CRDT
