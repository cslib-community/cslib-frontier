/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

-- upstream: candidate
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.HeapPrimMarks
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Size of the terminal quotient in the live/dead partition

A full-size component creates a dead class containing at least the requested number of
original vertices. A short search attaches to an existing dead class, or exhausts its
boundary and becomes isolated. Counting only non-isolated representatives therefore also
handles disconnected inputs and disconnections caused by earlier marks.

See [Pettie and Ramachandran, Lemma 3.3(c) and §5][PettieRamachandran2002].
-/

public section

namespace Cslib.Multigraph

open Finset

variable {V E W : Type*} [LinearOrder W]

private theorem PrimPrefix.joins_inside {ends : E → Sym2 V} {S : Finset E} {C : Set V}
    {key : E → W} (p : PrimPrefix ends S key C) :
    ∀ a ∈ C, ∀ b ∈ C, Joins ends (internalEdges ends S C) a b := by
  induction p with
  | start v => rintro _ rfl _ rfl; exact Joins.refl _
  | @step C e u v _ hu hv he hab _ ih =>
    let J := internalEdges ends S (insert v C)
    have sub : (internalEdges ends S C : Set E) ⊆ J := fun _ hg =>
      mem_internalEdges.2 ⟨(mem_internalEdges.1 hg).1,
        fun z hz => Set.mem_insert_of_mem _ ((mem_internalEdges.1 hg).2 z hz)⟩
    have new : e ∈ J := mem_internalEdges.2 ⟨he, by simp [hab, Sym2.mem_iff, hu]⟩
    have up (a : V) (ha : a ∈ C) : Joins ends J a v :=
      ((ih a ha u hu).mono sub).trans (Joins.of_mem new hab)
    intro a ha b hb
    rcases Set.mem_insert_iff.1 ha with haEq | haC
    · subst a
      rcases Set.mem_insert_iff.1 hb with hbEq | hbC
      · exact hbEq ▸ Joins.refl _
      · exact (up b hbC).symm
    · rcases Set.mem_insert_iff.1 hb with hbEq | hbC
      · subst b
        exact up a haC
      · exact (ih a haC b hbC).mono sub

/-- A Prim prefix contracts precisely its reached vertices into a single class.
Every vertex outside the prefix is alone in its class, including an isolated vertex. -/
theorem PrimPrefix.contract_eq_iff {ends : E → Sym2 V} {S : Finset E} {C : Set V} {key : E → W}
    (p : PrimPrefix ends S key C) {x y : V} :
    contract ends (internalEdges ends S C) x = contract ends (internalEdges ends S C) y ↔
      x = y ∨ x ∈ C ∧ y ∈ C := by
  rw [contract_eq_contract_iff]
  constructor
  · intro path
    induction path with
    | refl => exact Or.inl rfl
    | @tail b z _ step ih =>
      obtain ⟨g, hg, hgz⟩ := step
      have inside := (mem_internalEdges.1 hg).2
      have hb := inside b (by simp [hgz])
      have hz := inside z (by simp [hgz])
      rcases ih with rfl | ⟨hx, _⟩
      · exact Or.inr ⟨hb, hz⟩
      · exact Or.inr ⟨hx, hz⟩
  · rintro (rfl | ⟨hx, hy⟩)
    · exact Joins.refl _
    · exact p.joins_inside _ hx _ hy

private theorem support_of_joins {ends : E → Sym2 V} {S : Finset E} {x y : V}
    (path : Joins ends S x y) (hx : x ∈ support ends S) : y ∈ support ends S := by
  induction path with
  | refl => exact hx
  | @tail a b _ step ih =>
    obtain ⟨e, he, hab⟩ := step
    by_cases h : a = b
    · exact h ▸ ih
    · exact mem_support.2 ⟨e, he, by simpa [hab] using h, by simp [hab]⟩

namespace PrimPartition

variable [DecidableEq E] [DecidableEq V] {w : E → W}

/-- A search starts at its seed and stops on filling the requested size, reaching a dead
representative, or exhausting its boundary. -/
@[expose] def Grower.Complete (p : Grower V E W w) : Prop :=
  ∀ (ends : E → Sym2 V) (S : Finset E) (extra : ℕ) (dead : Finset V) (v : V), v ∉ dead →
    let q := p.run ends S extra dead v
    v ∈ q.vertices ∧ (q.vertices.card = extra + 1 ∨ (∃ x ∈ q.vertices, x ∈ dead) ∨
      ∀ e ∈ S, e ∉ (toGraph ends).edgeCut (q.vertices : Set V))

/-- The labeled graph passed to the dense-case solver after all bounded components
have been contracted and their marks removed. -/
@[expose] noncomputable def terminalGraph (w : E → W) (ends : E → Sym2 V) (S : Finset E) :
    List (PartitionPart V E W) → (E → Sym2 V) × Finset E
  | [] => (ends, S)
  | p :: ps => terminalGraph w (p.nextEnds ends S) (p.remaining ends w S) ps

/-- Non-isolated representatives at the terminal dense-case call. -/
@[expose] noncomputable def terminalSupport (w : E → W) (ends : E → Sym2 V) (S : Finset E)
    (parts : List (PartitionPart V E W)) : Finset V :=
  let g := terminalGraph w ends S parts
  support g.1 g.2

omit [DecidableEq V] in
/-- Marks and internal edges are removed as the partition advances. -/
theorem terminalGraph_subset (w : E → W) (ends : E → Sym2 V) (S : Finset E)
    (parts : List (PartitionPart V E W)) : (terminalGraph w ends S parts).2 ⊆ S := by
  induction parts generalizing ends S with
  | nil => exact Subset.rfl
  | cons p ps ih => exact (ih _ _).trans (p.remaining_subset ends w S)

omit [DecidableEq V] in
private theorem lift_active {ends : E → Sym2 V} {S : Finset E} (q : SearchState ends w S)
    {y : V} (hy : y ∈ support (q.part.nextEnds ends S) (q.part.remaining ends w S)) :
    let c := contract ends (internalEdges ends S q.part.vertices)
    ∃ (a b : V) (e : E), e ∈ S ∧ ends e = s(a, b) ∧ c a = y ∧ c a ≠ c b := by
  let c := contract ends (internalEdges ends S q.part.vertices)
  obtain ⟨e, he, nd, inc⟩ := mem_support.1 hy
  obtain ⟨a, b, hab⟩ : ∃ a b, ends e = s(a, b) :=
    Sym2.inductionOn (ends e) fun a b => ⟨a, b, rfl⟩
  have hab' : (q.part.nextEnds ends S) e = s(c a, c b) := by
    simp [PartitionPart.nextEnds, c, hab]
  have ab : c a ≠ c b := by simpa [hab'] using nd
  have heS := q.part.remaining_subset ends w S he
  rcases Sym2.mem_iff.1 (hab' ▸ inc) with rfl | rfl
  · exact ⟨a, b, e, heS, hab, rfl, ab⟩
  · exact ⟨b, a, e, heS, hab.trans Sym2.eq_swap, rfl, ab.symm⟩

private theorem sum_fibers {X Y : Finset V} (f : V → V) (r : ℕ)
    (large : ∀ y ∈ Y, r ≤ (X.filter fun x => f x = y).card) : r * Y.card ≤ X.card := by
  calc
    _ = ∑ _ ∈ Y, r := by simp [Nat.mul_comm]
    _ ≤ ∑ y ∈ Y, (X.filter fun x => f x = y).card := sum_le_sum large
    _ = (X.filter fun x => f x ∈ Y).card := sum_card_fiberwise_eq_card_filter ..
    _ ≤ X.card := card_filter_le _ _

/-- Each non-isolated terminal class contains at least `extra + 1` original vertices. Their
classes are disjoint, giving the vertex bound for the dense-case call even on disconnected input. -/
theorem terminalSupport_mul_le (p : Grower V E W w) (complete : p.Complete)
    (extra : ℕ) (ends : E → Sym2 V) (S : Finset E) :
    let X := support ends S
    (extra + 1) * (terminalSupport w ends S (partition p extra ends S id ∅ X.toList)).card ≤
      X.card := by
  let X := support ends S
  have loop (es : E → Sym2 V) (A : Finset E) (rep : V → V) (dead : Finset V) (todo : List V)
      (covers : ∀ u ∈ support es A, u ∈ X.image rep)
      (large : ∀ u ∈ support es A, u ∈ dead → extra + 1 ≤ (X.filter fun x => rep x = u).card)
      (future : ∀ u ∈ support es A, u ∉ dead → ∃ x ∈ todo, rep x = u) :
      (extra + 1) * (terminalSupport w es A (partition p extra es A rep dead todo)).card ≤
        X.card := by
    induction todo generalizing es A rep dead with
    | nil =>
      apply sum_fibers rep _ (Y := support es A)
      intro u hu
      exact large u hu (by by_contra no; obtain ⟨x, hx, _⟩ := future u hu no; cases hx)
    | cons v vs ih =>
      rw [partition]
      split
      next old =>
        apply ih es A rep dead covers large
        intro u hu live
        obtain ⟨x, hx, same⟩ := future u hu live
        rcases List.mem_cons.1 hx with rfl | hr
        · exact False.elim (live (same ▸ old))
        · exact ⟨x, hr, same⟩
      next fresh =>
        let q := p.run es A extra dead (rep v)
        let c := contract es (internalEdges es A q.part.vertices)
        let es' := q.part.nextEnds es A
        let A' := q.part.remaining es w A
        let dead' := (dead ∪ q.vertices).image c
        have color {x y : V} : c x = c y ↔ x = y ∨ x ∈ q.vertices ∧ y ∈ q.vertices :=
          q.primPrefix.contract_eq_iff
        obtain ⟨seed, finish⟩ := complete es A extra dead (rep v) fresh
        change rep v ∈ q.vertices at seed
        have original {x : V} {y : V} (hy : y ∈ support es' A') (hxy : c x = y) :
            x ∈ support es A := by
          obtain ⟨a, b, e, he, h, eq, ne⟩ := lift_active q hy
          have ha : a ∈ support es A := mem_support.2 ⟨e, he, by
            simpa [h] using (fun h' => ne (congrArg c h')), by simp [h]⟩
          apply support_of_joins _ ha
          have pth := contract_eq_contract_iff.1 (eq.trans hxy.symm)
          exact pth.mono fun f hf => (mem_internalEdges.1 hf).1
        apply ih es' A' (c ∘ rep) dead'
        · intro y hy
          obtain ⟨a, _, _, _, _, eq, _⟩ := lift_active q hy
          obtain ⟨x, hx, rfl⟩ := mem_image.1 (covers a (original hy eq))
          exact mem_image.2 ⟨x, hx, eq⟩
        · intro y hy hd
          obtain ⟨z, hz, eq⟩ := mem_image.1 hd
          have inherited (x : V) (hx : x ∈ dead) (hxy : c x = y) :
              extra + 1 ≤ (X.filter fun v => (c ∘ rep) v = y).card := by
            apply (large x (original hy hxy) hx).trans (card_le_card ?_)
            intro a ha
            obtain ⟨haX, right⟩ := mem_filter.1 ha
            exact mem_filter.2 ⟨haX, (congrArg c right).trans hxy⟩
          rcases mem_union.1 hz with old | new
          · exact inherited z old eq
          have onC (x : V) (hx : x ∈ q.vertices) : c x = y := (color.2 (Or.inr ⟨hx, new⟩)).trans eq
          rcases finish with full | linked | emptyCut
          · change q.vertices.card = extra + 1 at full
            rw [← full]
            apply card_le_card_of_surjOn rep
            intro a ha
            obtain ⟨x, hx, eqx⟩ := mem_image.1 (covers a (original hy (onC a ha)))
            exact ⟨x, mem_filter.2 ⟨hx, (congrArg c eqx).trans (onC a ha)⟩, eqx⟩
          · obtain ⟨x, hx, old⟩ := linked
            exact inherited x old (onC x hx)
          · obtain ⟨a, b, e, he, inc, ay, ab⟩ := lift_active q hy
            have haC : a ∈ q.vertices := by
              rcases color.1 (ay.trans eq.symm) with rfl | ⟨ha, _⟩
              · exact new
              · exact ha
            have hbC : b ∉ q.vertices := fun hb => ab (color.2 (Or.inr ⟨haC, hb⟩))
            exact False.elim (emptyCut e he (Graph.mem_edgeCut_iff.2 ⟨a, b, inc, haC, hbC⟩))
        · intro y hy alive
          obtain ⟨a, _, _, _, _, eq, _⟩ := lift_active q hy
          have unseen : a ∉ dead := fun ha => alive (mem_image.2 ⟨a, mem_union_left _ ha, eq⟩)
          obtain ⟨x, hx, eqx⟩ := future a (original hy eq) unseen
          rcases List.mem_cons.1 hx with rfl | hr
          · exact False.elim (alive (mem_image.2
              ⟨_, mem_union_right _ seed, (congrArg c eqx).trans eq⟩))
          · exact ⟨x, hr, (congrArg c eqx).trans eq⟩
  exact loop ends S id ∅ X.toList (fun u hu => mem_image_of_mem id hu)
    (by simp) (fun u hu _ => ⟨u, mem_toList.2 hu, rfl⟩)

/-- The concrete heap search satisfies the three stopping conditions, so the terminal
quotient bound applies without any caller-supplied completion certificate. -/
theorem HeapPrim.complete {V E W : Type} [DecidableEq V] [LinearOrder E] [LinearOrder W]
    (w : E → W) (t : ℕ) : (HeapPrim.grower (V := V) t w).Complete :=
  fun ends S extra dead v _ => HeapPrim.grower_complete w t ends S extra dead v

end PrimPartition
end Cslib.Multigraph
