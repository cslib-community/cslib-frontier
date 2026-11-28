/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

-- upstream: local-only (tests)

import CslibFrontier.DataStructure.Memory.TripleFrame
import CslibFrontier.Tactic.Realize

/-!
# Client tests for `Memory.TripleFrame`

Exercises multi-block `FramedTriple.frame` preservation, `FramedTriple.mem_eq_of_frontier_eq`,
strided `Block.slot` framing across updates to other indices, `Block.writeList` multi-field
initialization (including `Realizes .exact` compilation of a fixed-arity list), boundary
witnesses for adjacent blocks and `ZeroAbove`, allocation/copy/branch combinators, and
`Classical.choice`-free `#print axioms` checks.
-/

namespace CslibFrontierTests.DataStructure.Memory.TripleFrame

open Cslib.DataStructure
open Cslib.DataStructure.Memory
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ## 1. Disjoint multi-block `FramedTriple.frame` preservation -/

private def updateFirstBlock (b₁ : Block) : Prog Unit := do
  b₁.set 0 42
  b₁.set 2 99

example {w : ℕ} {s : State} (h42 : Fits w 42) (h99 : Fits w 99)
    (b₁ b₂ : Block) (hb₁ : b₁.Allocated s) (hb₂ : b₂.Allocated s)
    (h1len : 3 ≤ b₁.length) (hd : b₁.Disjoint b₂)
    (h2hold : Block.HoldsList b₂.base [5, 6] s.mem) (h2len : 2 ≤ b₂.length) :
    FramedTriple w s (updateFirstBlock b₁) 2 (Set.Ico b₁.base (b₁.base + b₁.length))
      fun _ s' =>
        s'.mem b₁.base = 42 ∧
        s'.mem (b₁.base + 2) = 99 ∧
        Block.HoldsList b₂.base [5, 6] s'.mem ∧
        b₂.entries 2 s'.mem = b₂.entries 2 s.mem := by
  have hbase : FramedTriple w s (updateFirstBlock b₁) 2
      (Set.Ico b₁.base (b₁.base + b₁.length))
      fun _ s' => s'.mem b₁.base = 42 ∧ s'.mem (b₁.base + 2) = 99 := by
    unfold updateFirstBlock
    refine FramedTriple.set_bind hb₁ (by omega) h42 Set.Subset.rfl ?_
    refine FramedTriple.set (b := b₁) (i := 2) (v := 99) hb₁ (by omega) h99 Set.Subset.rfl ?_
    refine ⟨?_, ?_⟩
    · change Function.update (Function.update s.mem (b₁.base + 0) 42) (b₁.base + 2) 99 b₁.base = 42
      rw [Function.update_of_ne (by omega)]
      simp
    · change Function.update (Function.update s.mem (b₁.base + 0) 42) (b₁.base + 2) 99
        (b₁.base + 2) = 99
      simp
  have hframed := hbase.frame_mem
    (D := Set.Ico b₂.base (b₂.base + b₂.length))
    (R := fun m => Block.HoldsList b₂.base [5, 6] m)
    h2hold
    (fun m₁ m₂ heq hm => Block.HoldsList.frame hm fun a hlo hhi =>
      (heq a ⟨hlo, by simp only [List.length_cons, List.length_nil] at hhi; omega⟩).symm)
    (Block.disjoint_ico_iff.mpr hd)
    (fun a ⟨hlo, hhi⟩ => lt_of_lt_of_le hhi hb₂)
  refine Triple.mono hframed le_rfl fun _ _ ⟨hm, ⟨h0, h2⟩, hhold⟩ => ⟨hm, h0, h2, hhold, ?_⟩
  exact Block.entries_eq_of_modifies_block hb₂ h2len hd.symm hm

-- `Modifies` in `Cslib.WordRAM` coexists cleanly with `protected Memory.Modifies`, and
-- `Block.Disjoint.symm` supports both `hd.symm` and the `symm` tactic.
example (b₁ b₂ : Block) (hd : b₁.Disjoint b₂) :
    b₂.Disjoint b₁ ∧ ∀ m, Cslib.WordRAM.Modifies ∅ m m := by
  refine ⟨?_, fun m => Cslib.WordRAM.Modifies.refl ∅ m⟩
  symm
  exact hd

-- Using the `frame` lemma directly on a `State` predicate.
example {w : ℕ} {s : State} (h42 : Fits w 42) (b₁ b₂ : Block)
    (hb₁ : b₁.Allocated s) (hb₂ : b₂.Allocated s) (h1len : 1 ≤ b₁.length)
    (h2len : 1 ≤ b₂.length) (hd : b₁.Disjoint b₂) (hval : s.mem b₂.base = 77) :
    FramedTriple w s (b₁.set 0 42) 1 (Set.Ico b₁.base (b₁.base + b₁.length))
      fun _ s' => s'.mem b₁.base = 42 ∧ s'.mem b₂.base = 77 := by
  have hb : FramedTriple w s (b₁.set 0 42) 1 (Set.Ico b₁.base (b₁.base + b₁.length))
      fun _ s' => s'.mem b₁.base = 42 :=
    FramedTriple.set hb₁ (by omega) h42 Set.Subset.rfl (by simp)
  exact hb.frame (D := {b₂.base}) (R := fun st => st.mem b₂.base = 77) hval
    (fun s₁ s₂ heq hs => (heq b₂.base rfl).symm.trans hs)
    (Set.disjoint_singleton_right.mpr fun hm => hd b₂.base ⟨hm, ⟨le_rfl, by omega⟩⟩)
    (fun a ha => by subst ha; exact hb₂.lt_frontier h2len)

/-! ## 2. Strided `Block.slot` framing across updates to other indices -/

example {w base stride n i j : ℕ} {s : State} (hwf : WellFormed w s)
    (halloc : base + stride * n ≤ s.frontier) (hi : i < n) (hj : j < n) (hne : i ≠ j)
    (vs : List ℕ) (hlen : vs.length = stride) (hfit : ∀ v ∈ vs, Fits w v) :
    let bJ := Block.slot base stride j
    let bI := Block.slot base stride i
    FramedTriple w s (Block.writeList bJ.base vs) stride (Set.Ico bJ.base (bJ.base + stride))
      fun _ s' =>
        Block.HoldsList bJ.base vs s'.mem ∧
        bI.entries stride s'.mem = bI.entries stride s.mem ∧
        WellFormed w s' := by
  intro bJ bI
  have hbJ : bJ.Allocated s := Block.slot_allocated_of_lt halloc hj
  have hbI : bI.Allocated s := Block.slot_allocated_of_lt halloc hi
  have hwl := Block.framedTriple_writeList (base := bJ.base) (vs := vs) hwf
    (by simp only [bJ, Block.slot] at hbJ ⊢; rw [hlen]; exact hbJ) hfit
  rw [hlen] at hwl
  have hkeep : ∀ a ∈ Set.Ico bI.base (bI.base + stride), a < s.frontier := by
    intro a ⟨_, hhi⟩
    simp only [bI, Block.slot] at hbI ⊢
    exact lt_of_lt_of_le hhi hbI
  have hframed := hwl.frame_mem
    (D := Set.Ico bI.base (bI.base + stride))
    (R := fun m => bI.entries stride m = bI.entries stride s.mem)
    rfl
    (fun m₁ m₂ heq hm => (bI.entries_congr stride fun k hk =>
      (heq (bI.base + k) ⟨Nat.le_add_right _ _, by omega⟩).symm).trans hm)
    (Block.disjoint_ico_iff.mpr (Block.slot_disjoint_of_ne hne.symm))
    hkeep
  refine hframed.mono le_rfl fun _ s' ⟨⟨_, hhold, hwf'⟩, hent⟩ => ⟨hhold, hent, hwf'⟩

/-! ## 3. `Block.writeList` multi-field initialization and `Realizes .exact` -/

example {w base : ℕ} {s : State} (hwf : WellFormed w s) (hbound : base + 3 ≤ s.frontier)
    (h0 : Fits w 10) (h1 : Fits w 20) (h2 : Fits w 30) :
    FramedTriple w s (Block.writeList base [10, 20, 30]) 3 (Set.Ico base (base + 3))
      fun _ s' =>
        s'.frontier = s.frontier ∧
        s'.mem base = 10 ∧
        s'.mem (base + 1) = 20 ∧
        s'.mem (base + 2) = 30 ∧
        WellFormed w s' := by
  have hwl := Block.framedTriple_writeList (base := base) (vs := [10, 20, 30]) hwf hbound
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> assumption)
  refine hwl.mono le_rfl fun _ s' ⟨hfr, hhold, hwf'⟩ =>
    ⟨hfr, hhold.get 0 (by simp), hhold.get 1 (by simp), hhold.get 2 (by simp), hwf'⟩

/-- Fixed-arity 3-word `Block.writeList` compiles uniformly to `Realizes .exact` (`work = 0`). -/
theorem realizes_writeList3 :
    Realizes .exact (fun d : ℕ × ℕ × ℕ × ℕ => Block.writeList d.1 [d.2.1, d.2.2.1, d.2.2.2])
      WordEncoding.encode WordEncoding.encode
      (fun w d _ => Fits w (d.1 + 2)) (fun _ _ => 0) := by
  realize rewriting [Block.writeList_cons, Block.writeList_nil]
  all_goals exact h.of_le (by omega)

/-! ## 4. Allocation, `ZeroAbove`, `copy`, and `ite` combinators -/

example {w : ℕ} {s : State} (hz : ZeroAbove s)
    (hfit : Fits w (s.frontier + 4)) (h7 : Fits w 7) :
    FramedTriple w s (do
      let b ← allocBlockDirty 4
      b.set 1 7
      pure b) 2 ∅ fun b s' =>
        b = ⟨s.frontier, 4⟩ ∧
        b.Allocated s' ∧
        s'.mem (b.base + 0) = 0 ∧
        s'.mem (b.base + 1) = 7 ∧
        ZeroAbove s' := by
  have h1 : FramedTriple w s (do
      let b ← allocBlockDirty 4
      b.set 1 7
      pure b) 2 (Set.Ico s.frontier (s.frontier + 4)) fun b s' =>
        b = ⟨s.frontier, 4⟩ ∧ b.Allocated s' ∧ s'.mem (b.base + 0) = 0 ∧
        s'.mem (b.base + 1) = 7 ∧ ZeroAbove s' := by
    refine FramedTriple.allocBlockDirty_bind hfit ?_
    have hs1 : (Block.mk s.frontier 4).Allocated ⟨s.mem, s.frontier + 4⟩ := le_rfl
    refine FramedTriple.set_bind hs1 (by dsimp only; omega) h7 Set.Subset.rfl ?_
    refine FramedTriple.pure ?_
    refine ⟨rfl, le_rfl, ?_, ?_, (hz.allocDirty 4).write (by dsimp only; omega)⟩
    · change Function.update s.mem (s.frontier + 1) 7 (s.frontier + 0) = 0
      rw [Function.update_of_ne (by omega)]
      exact hz (s.frontier + 0) (by omega)
    · change Function.update s.mem (s.frontier + 1) 7 (s.frontier + 1) = 7
      simp
  exact Triple.mono h1 le_rfl fun _ _ ⟨hm, hq⟩ =>
    ⟨⟨hm.1, fun a ha _ => hm.2 a ha (by simp only [Set.mem_Ico, not_and, not_lt]; omega)⟩, hq⟩

example {w src dst n : ℕ} {s : State} (hdisj : src + n ≤ dst ∨ dst + n ≤ src)
    (hsrc : src + n ≤ s.frontier) (hdst : dst + n ≤ s.frontier)
    (hfit : ∀ i < n, Fits w (s.mem (src + i))) (hb : Bool) :
    FramedTriple w s (if hb then Memory.copy src dst n else pure ()) (2 * n)
      (Set.Ico dst (dst + n)) fun _ s' =>
        s'.frontier = s.frontier := by
  refine FramedTriple.ite (fun _ => ?_) (fun _ => FramedTriple.pure rfl)
  exact FramedTriple.copy hdisj hsrc hdst hfit rfl

/-! ## 5. Boundary witnesses (`mem_eq_of_frontier_eq`, adjacent blocks, `ZeroAbove`) -/

-- `FramedTriple.mem_eq_of_frontier_eq` protects cells at or above `s.frontier` when the
-- frontier does not advance.
example {w base : ℕ} {s : State} (hwf : WellFormed w s) (hbound : base + 2 ≤ s.frontier)
    (h0 : Fits w 1) (h1 : Fits w 2) (a : ℕ) (ha : s.frontier ≤ a) :
    ((spec w).clientState s (Block.writeList base [1, 2])).mem a = s.mem a := by
  have hwl := Block.framedTriple_writeList (base := base) (vs := [1, 2]) hwf hbound
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl <;> assumption)
  have hnot : a ∉ Set.Ico base (base + [1, 2].length) := by
    simp only [Set.mem_Ico, List.length_cons, List.length_nil, not_and, not_lt]
    omega
  exact hwl.mem_eq_of_frontier_eq hwl.post.1 a hnot

-- Adjacent blocks touching at `b₁.base + b₁.length = b₂.base` are disjoint.
example {b₁ b₂ : Block} (hadj : b₁.base + b₁.length = b₂.base) :
    b₁.Disjoint b₂ ∧ b₂.Disjoint b₁ := by
  have hd : b₁.Disjoint b₂ := Block.disjoint_of_le_left hadj.le
  exact ⟨hd, hd.symm⟩

-- `ZeroAbove` boundary at `a = s.frontier`, preserved across `allocDirty`.
example {s : State} (hz : ZeroAbove s) (k : ℕ) :
    s.mem s.frontier = 0 ∧
    ∀ s' : State, s' = ⟨s.mem, s.frontier + k⟩ → s'.mem s'.frontier = 0 :=
  ⟨hz s.frontier le_rfl, fun _ hs' => hs' ▸ (hz.allocDirty k) (s.frontier + k) le_rfl⟩

/-! ## 6. Axiom checks (`#print axioms`) -/

/-- info: 'Cslib.WordRAM.Block.slot_disjoint_of_ne' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.Block.slot_disjoint_of_ne

end CslibFrontierTests.DataStructure.Memory.TripleFrame
