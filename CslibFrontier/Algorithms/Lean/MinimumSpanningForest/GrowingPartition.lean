/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

-- upstream: candidate
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.Partition

/-!
# Bounded growth of corrupted Prim components

A search takes a minimum current-key edge of the boundary until it exhausts its edge budget,
has no boundary, or reaches a designated stopping vertex. Previously chosen keys are frozen.
The resulting component is a genuine Prim prefix for its final key function, even though the
minimum queries used different key functions over time.

The boundary minimum here is specified by minimization over a finite set. The key-update policy
is a parameter. This module proves correctness independently of the implementation and cost
of heap operations.

See [Pettie and Ramachandran, §3.2][PettieRamachandran2002].
-/

public section

namespace Cslib.Multigraph.PrimPartition

open Finset

variable {V E W : Type*} [LinearOrder W]

/-- A key update may depend on the reached vertices, extracted labels, and old keys.
It only increases keys and leaves all extracted labels at their extraction values. -/
structure KeyPolicy (V E W : Type*) [LinearOrder W] where
  /-- Current key function used for the next boundary minimum. -/
  update : Finset V → Finset E → (E → W) → E → W
  /-- Keys may only increase. -/
  raises : ∀ C D key e, key e ≤ update C D key e
  /-- An extracted label keeps its recorded key. -/
  frozen : ∀ C D key e, e ∈ D → update C D key e = key e

/-- Exact Prim growth is an admissible choice of policy. -/
def KeyPolicy.exact : KeyPolicy V E W :=
  ⟨fun _ _ key => key, fun _ _ _ _ => le_rfl, fun _ _ _ _ _ => rfl⟩

variable [DecidableEq V] [DecidableEq E]

/-- Invariant of a partial Prim search. Raising the remaining keys further preserves the
entire prefix whenever the extracted labels keep their recorded keys. -/
structure SearchState (ends : E → Sym2 V) (w : E → W) (S : Finset E) where
  /-- Vertices reached so far. -/
  vertices : Finset V
  /-- Labels of the edges used to grow the component. -/
  chosen : Finset E
  /-- Current keys, including the frozen values of extracted labels. -/
  key : E → W
  /-- The keys are upper bounds on original weights. -/
  raised : ∀ e ∈ S, w e ≤ key e
  /-- Every recorded extraction still witnesses a Prim prefix at all admissible final keys. -/
  stable : ∀ k : E → W, (∀ f ∈ S, key f ≤ k f) → (∀ f ∈ chosen, k f = key f) →
    PrimPrefix ends S k vertices

variable {ends : E → Sym2 V} {w : E → W} {S : Finset E}

namespace SearchState

/-- Start a search at one live vertex with the original input weights. -/
@[expose] def start (v : V) : SearchState ends w S where
  vertices := {v}
  chosen := ∅
  key := w
  raised _ _ := le_rfl
  stable _ _ _ := by simpa using PrimPrefix.start (ends := ends) (S := S) _

/-- A least boundary edge, oriented out of the reached set. -/
structure Exit (ends : E → Sym2 V) (S : Finset E) (C : Finset V) (key : E → W) where
  edge : E
  inside : V
  outside : V
  active : edge ∈ S
  left_mem : inside ∈ C
  right_notMem : outside ∉ C
  inc : ends edge = s(inside, outside)
  minimum : ∀ f ∈ S, ∀ x ∈ C, ∀ y ∉ C, ends f = s(x, y) → key edge ≤ key f

/-- Select a minimum-key outgoing edge when one exists. -/
noncomputable def minExit (ends : E → Sym2 V) (S : Finset E) (C : Finset V) (k : E → W) :
    Option (Exit ends S C k) := by
  classical
  let B := S.filter fun e => e ∈ (toGraph ends).edgeCut (C : Set V)
  by_cases hB : B.Nonempty
  · have h := B.exists_min_image k hB
    let e := h.choose
    obtain ⟨he, hmin⟩ := h.choose_spec
    have hm : e ∈ S ∧ e ∈ (toGraph ends).edgeCut (C : Set V) := mem_filter.1 he
    have cut := Graph.mem_edgeCut_iff.1 hm.2
    let a := cut.choose
    let b := cut.choose_spec.choose
    have pair := cut.choose_spec.choose_spec
    exact some ⟨e, a, b, hm.1, pair.2.1, pair.2.2, pair.1,
      fun f hf x hx y hy hxy => hmin f
        (mem_filter.2 ⟨hf, Graph.mem_edgeCut_iff.2 ⟨x, y, hxy, hx, hy⟩⟩)⟩
  · exact none

omit [DecidableEq V] [DecidableEq E] in
/-- A nonempty cut always yields an oriented minimum. -/
theorem exists_minExit {ends : E → Sym2 V} {S : Finset E} {C : Finset V} (k : E → W)
    (h : ∃ e ∈ S, e ∈ (toGraph ends).edgeCut (C : Set V)) :
    ∃ x, minExit ends S C k = some x := by
  classical
  have ne : (S.filter (fun e => e ∈ (toGraph ends).edgeCut (C : Set V))).Nonempty := by
    obtain ⟨e, he, hc⟩ := h
    exact ⟨e, mem_filter.mpr ⟨he, hc⟩⟩
  unfold minExit
  simp [ne]

/-- Add a least boundary edge at the new keys. The key update may come from a stateful
heap computation. Only the values on active and previously extracted labels matter. -/
@[expose] def takeExit (q : SearchState ends w S) (newKey : E → W)
    (rise : ∀ e ∈ S, q.key e ≤ newKey e) (fixed : ∀ e ∈ q.chosen, newKey e = q.key e)
    (x : Exit ends S q.vertices newKey) : SearchState ends w S where
  vertices := insert x.outside q.vertices
  chosen := insert x.edge q.chosen
  key := newKey
  raised e he := (q.raised e he).trans (rise e he)
  stable k higher frozen := by
    have prior := q.stable k (fun e he => (rise e he).trans (higher e he))
      (fun e he => (frozen e (mem_insert_of_mem he)).trans (fixed e he))
    rw [coe_insert]
    apply PrimPrefix.step prior x.left_mem x.right_notMem x.active x.inc
    intro f hf a ha b hb hab
    rw [frozen x.edge (mem_insert_self ..)]
    exact (x.minimum f hf a ha b hb hab).trans (higher f hf)

private def take (q : SearchState ends w S) (p : KeyPolicy V E W)
    (x : Exit ends S q.vertices (p.update q.vertices q.chosen q.key)) : SearchState ends w S :=
  q.takeExit (p.update q.vertices q.chosen q.key) (fun e _ => p.raises _ _ _ e)
    (fun e he => p.frozen _ _ _ e he) x

/-- Grow up to `fuel` additional vertices. Reaching a stopping vertex ends this search
immediately, after including the vertex just reached. The empty-boundary case handles
components smaller than the size limit. -/
noncomputable def grow (p : KeyPolicy V E W) (stop : V → Bool) :
    ℕ → SearchState ends w S → SearchState ends w S
  | 0, q => q
  | fuel + 1, q =>
    match minExit ends S q.vertices (p.update q.vertices q.chosen q.key) with
    | none => q
    | some x =>
      let r := q.take p x
      if stop x.outside then r else grow p stop fuel r

/-- The search respects its prescribed vertex budget at every stopping condition. -/
theorem card_grow_le (p : KeyPolicy V E W) (stop : V → Bool) (fuel : ℕ) (q : SearchState ends w S) :
    (grow p stop fuel q).vertices.card ≤ q.vertices.card + fuel := by
  induction fuel generalizing q with
  | zero => simp [grow]
  | succ n ih =>
    rw [grow]
    split
    · omega
    next x _ =>
      have h : (q.take p x).vertices.card = q.vertices.card + 1 :=
        card_insert_of_notMem x.right_notMem
      dsimp only
      split
      · omega
      · have := ih (q.take p x)
        omega

/-- The final vertex set and weight function passed to the partition routine. -/
def part (q : SearchState ends w S) : PartitionPart V E W := ⟨q.vertices, q.key⟩

omit [DecidableEq V] [DecidableEq E] in
theorem primPrefix (q : SearchState ends w S) : PrimPrefix ends S q.part.key q.part.vertices :=
  q.stable q.key (fun _ _ => le_rfl) (fun _ _ => rfl)

end SearchState

/-- A bounded Prim component builder. Its internal state can include a priority queue.
It returns the final keys and an extraction history certified by `SearchState.stable`. -/
structure Grower (V E W : Type*) [LinearOrder W] (w : E → W) where
  /-- Search from a live seed, stopping on arrival at an old component or at the size limit. -/
  run : (ends : E → Sym2 V) → (S : Finset E) → ℕ → Finset V → V → SearchState ends w S
  /-- The initial seed and all subsequently added vertices fit the requested size limit. -/
  bound : ∀ ends S extra dead seed, (run ends S extra dead seed).vertices.card ≤ extra + 1

/-- Finite minimization with a key-update policy instantiates the component builder. -/
noncomputable def KeyPolicy.grower (p : KeyPolicy V E W) (w : E → W) : Grower V E W w where
  run ends S extra dead v := SearchState.grow p (fun x => decide (x ∈ dead)) extra
    (SearchState.start (ends := ends) (S := S) (w := w) v)
  bound ends S extra dead v := by
    have h := SearchState.card_grow_le (ends := ends) (w := w) (S := S) p
      (fun x => decide (x ∈ dead)) extra (SearchState.start v)
    simpa [SearchState.start, Nat.add_comm] using h

/-- Grow components in the current quotient, trying the original vertices in order.
The map `rep` follows each original vertex into the current quotient. Reaching a dead
representative immediately ends a component. A contraction sends all reached vertices and
previous dead representatives into the next dead set. The size limit is `extra + 1`. -/
@[expose] noncomputable def partition (p : Grower V E W w) (extra : ℕ) (ends : E → Sym2 V)
    (S : Finset E) (rep : V → V) (dead : Finset V) : List V → List (PartitionPart V E W)
  | [] => []
  | v :: rest =>
    if rep v ∈ dead then partition p extra ends S rep dead rest else
    let q := p.run ends S extra dead (rep v)
    let c := contract ends (internalEdges ends S q.part.vertices)
    q.part :: partition p extra (q.part.nextEnds ends S) (q.part.remaining ends w S)
      (c ∘ rep) ((dead ∪ q.vertices).image c) rest

/-- The output of the live/dead loop satisfies the hypotheses of robust contraction at
every stage. In particular `Valid.msf_eq` applies to the complete sequence. -/
theorem valid_partition (p : Grower V E W w) (extra : ℕ) (rep : V → V) (dead : Finset V)
    (vertices : List V) : Valid w ends S (partition p extra ends S rep dead vertices) := by
  induction vertices generalizing ends S rep dead with
  | nil => exact .nil
  | cons v rest ih =>
    rw [partition]
    split
    · exact ih ..
    · exact .cons (SearchState.primPrefix _) (SearchState.raised _) (ih ..)

/-- Every component submitted to a small-graph decision tree has at most `extra + 1`
vertices. Counting includes the old representative when the search attaches to a conglomerate. -/
theorem size_partition (p : Grower V E W w) (extra : ℕ) (rep : V → V) (dead : Finset V)
    (vertices : List V) :
    ∀ part ∈ partition p extra ends S rep dead vertices,
      ∃ C : Finset V, part.vertices = C ∧ C.card ≤ extra + 1 := by
  induction vertices generalizing ends S rep dead with
  | nil => simp [partition]
  | cons v rest ih =>
    rw [partition]
    split
    · exact ih rep dead
    · intro part hp
      rcases List.mem_cons.1 hp with rfl | h
      · refine ⟨_, rfl, ?_⟩
        exact p.bound ends S extra dead (rep v)
      · exact ih _ _ _ h

end Cslib.Multigraph.PrimPartition
