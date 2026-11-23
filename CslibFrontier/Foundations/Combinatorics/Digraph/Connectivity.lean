/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/Digraph/Connectivity.lean`)

public import CslibFrontier.Init
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.List.Chain
import CslibFrontier.Foundations.Combinatorics.Multidigraph.Connectivity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod

/-!
# Directed paths, cuts and separators in digraphs

Pure graph-theoretic notions for Menger's theorem in directed graphs `Digraph V`:

* Simple directed `s`–`t` paths `Digraph.IsDipath` (duplicate-free vertex lists from `s` to `t`
  forming an adjacency chain).
* Arc cuts (`Digraph.IsArcCut`), outgoing arc cuts `δ^out(S)` (`Digraph.outArcs`), vertex cuts
  (`Digraph.IsVertexCut`), and `A`–`B` vertex separators (`Digraph.IsSeparator`).
* Pairwise arc-disjointness (`Digraph.ArcDisjoint`) and internal vertex-disjointness
  (`Digraph.InternallyDisjoint`).
* Weak duality and closed-set cut/separator certificates, derived from the general multidigraph
  theorems (`Cslib.Multidigraph`) along `Cslib.Multidigraph.Arc G`.

## Main definitions

* `Digraph.IsDipath`, `Digraph.ArcDisjoint`, `Digraph.InternallyDisjoint`: simple directed paths
  and disjointness predicates.
* `Digraph.IsArcCut`, `Digraph.IsVertexCut`, `Digraph.IsSeparator`, `Digraph.outArcs`: directed
  arc and vertex cuts / separators.

## Main results

* `Digraph.isVertexCut_iff_isSeparator`: single-terminal vertex cuts in terms of `IsSeparator`.
* `Digraph.isArcCut_outArcs`, `Digraph.isSeparator_of_forall_adj`,
  `Digraph.isVertexCut_of_forall_adj`: certificates for arc cuts, separators and vertex cuts.
* `Digraph.card_le_card_of_arcDisjoint_of_isArcCut`,
  `Digraph.card_le_card_of_internallyDisjoint_of_isVertexCut`,
  `Digraph.card_le_card_of_disjoint_of_isSeparator`: weak duality for arc-disjoint,
  internally disjoint, and vertex-disjoint directed paths.

## References

* [K. Menger, *Zur allgemeinen Kurventheorie*][Menger1927]
* [A. Schrijver, *A Course in Combinatorial Optimization*][Schrijver2017], §4.1
-/

public section

namespace Digraph

open Cslib

variable {V : Type*}

/-- `p` is a simple directed `s`–`t` path in `G`: a duplicate-free vertex list starting at `s` and
ending at `t` whose consecutive pairs are arcs of `G`. -/
@[expose] def IsDipath (G : Digraph V) (s t : V) (p : List V) : Prop :=
  p.Nodup ∧ p.head? = some s ∧ p.getLast? = some t ∧ p.IsChain G.Adj

instance instDecidableIsDipath [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj] (s t : V)
    (p : List V) : Decidable (G.IsDipath s t p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The consecutive pairs `p.zip p.tail` of `p` satisfy `r` iff `p` is an `r`-chain. -/
theorem isChain_iff_forall_mem_zip_tail {r : V → V → Prop} :
    ∀ {p : List V}, p.IsChain r ↔ ∀ e ∈ p.zip p.tail, r e.1 e.2
  | [] => by simp
  | [x] => by simp
  | x :: y :: rest => by
    rw [List.isChain_cons_cons, List.tail_cons, List.zip_cons_cons, List.forall_mem_cons,
      isChain_iff_forall_mem_zip_tail, List.tail_cons]

/-- Lift a vertex dipath `p` in `G` to an arc dipath in `(Multidigraph.arcSrc G, arcTgt G)`. -/
private def liftDipath {G : Digraph V} {s t : V} {p : List V} (hp : G.IsDipath s t p) :
    {q : List (Multidigraph.Arc G) //
      Multidigraph.IsDipath (Multidigraph.arcSrc G) (Multidigraph.arcTgt G) s t q ∧
      s :: q.map (Multidigraph.arcTgt G) = p ∧
      q.map Subtype.val = p.zip p.tail} :=
  ⟨(p.zip p.tail).pmap (fun e he => ⟨e, he⟩) (isChain_iff_forall_mem_zip_tail.mp hp.2.2.2),
    Multidigraph.isDipath_pmap_zip_tail (Multidigraph.arcSrc G) (Multidigraph.arcTgt G)
      (fun e he => ⟨e, he⟩) (fun _ _ => ⟨rfl, rfl⟩) hp.1 hp.2.1 hp.2.2.1
      (isChain_iff_forall_mem_zip_tail.mp hp.2.2.2)⟩

private theorem isDipath_of_multidigraph {G : Digraph V} {s t : V} {q : List (Multidigraph.Arc G)}
    (hq : Multidigraph.IsDipath (Multidigraph.arcSrc G) (Multidigraph.arcTgt G) s t q) :
    G.IsDipath s t (s :: q.map (Multidigraph.arcTgt G)) := by
  have hc := hq.isChain_toDigraph
  rw [Multidigraph.toDigraph_arcSrc_arcTgt] at hc
  exact ⟨hq.2.1, rfl, hq.getLast?_vertices, hc⟩

/-- The vertex lists `P i` are pairwise arc-disjoint: no directed step `(u, v)` occurs as a
consecutive pair in two distinct lists. -/
@[expose] def ArcDisjoint {ι : Type*} (P : ι → List V) : Prop :=
  Pairwise fun i j => ∀ e ∈ (P i).zip (P i).tail, e ∉ (P j).zip (P j).tail

/-- The vertex lists `P i` are pairwise internally disjoint with respect to `s` and `t`: two
distinct lists share no vertex other than `s` and `t`. -/
@[expose] def InternallyDisjoint {ι : Type*} (s t : V) (P : ι → List V) : Prop :=
  Pairwise fun i j => ∀ v ∈ P i, v ∈ P j → v = s ∨ v = t

/-- `C` is an `s`–`t` arc cut of `G`: every simple directed `s`–`t` path of `G` uses an arc in
`C`. -/
@[expose] def IsArcCut (G : Digraph V) (s t : V) (C : Finset (V × V)) : Prop :=
  ∀ p, G.IsDipath s t p → ∃ e ∈ p.zip p.tail, e ∈ C

/-- `T` is an `s`–`t` vertex cut of `G`: it avoids `s` and `t`, and every simple directed `s`–`t`
path of `G` visits a vertex of `T`. -/
@[expose] def IsVertexCut (G : Digraph V) (s t : V) (T : Finset V) : Prop :=
  s ∉ T ∧ t ∉ T ∧ ∀ p, G.IsDipath s t p → ∃ v ∈ p, v ∈ T

/-- `Y` separates `A` from `B` in `G`: every simple directed `A`–`B` path visits a vertex of `Y`.
A vertex of `A ∩ B` must lie in `Y`, because of its trivial one-vertex path. -/
@[expose] def IsSeparator (G : Digraph V) (A B Y : Set V) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ B → ∀ p, G.IsDipath a b p → ∃ v ∈ p, v ∈ Y

theorem isVertexCut_iff_isSeparator {G : Digraph V} {s t : V} {T : Finset V} :
    G.IsVertexCut s t T ↔ s ∉ T ∧ t ∉ T ∧ G.IsSeparator {s} {t} ↑T := by
  refine ⟨fun ⟨hs, ht, h⟩ => ⟨hs, ht, ?_⟩, fun ⟨hs, ht, h⟩ => ⟨hs, ht, ?_⟩⟩
  · rintro _ rfl _ rfl p hp
    exact h p hp
  · intro p hp
    exact h (Set.mem_singleton s) (Set.mem_singleton t) p hp

theorem IsSeparator.mono {G : Digraph V} {A B Y Y' : Set V} (h : G.IsSeparator A B Y)
    (hY : Y ⊆ Y') : G.IsSeparator A B Y' :=
  fun _ ha _ hb p hp => (h ha hb p hp).imp fun _ hx => ⟨hx.1, hY hx.2⟩

theorem isSeparator_of_subset_left {G : Digraph V} {A B Y : Set V} (h : A ⊆ Y) :
    G.IsSeparator A B Y := by
  intro a ha _ _ p ⟨_, hps, _, _⟩
  exact ⟨a, List.mem_of_head? hps, h ha⟩

/-- The arcs of `G` leaving a vertex set `S` (Schrijver's `δ^out(S)`). -/
@[expose] def outArcs [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset (V × V) :=
  (S ×ˢ (Finset.univ \ S)).filter fun e => G.Adj e.1 e.2

theorem mem_outArcs [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    {S : Finset V} {e : V × V} :
    e ∈ G.outArcs S ↔ e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2 := by
  simp only [outArcs, Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ,
    true_and, and_assoc]

/-- `G.outArcs S` is an `s`–`t` arc cut whenever `s ∈ S` and `t ∉ S`. -/
theorem isArcCut_outArcs [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    {s t : V} {S : Finset V} (hs : s ∈ S) (ht : t ∉ S) : G.IsArcCut s t (G.outArcs S) := by
  intro p hp
  obtain ⟨q, hq, -, hzip⟩ := liftDipath hp
  obtain ⟨e, he, he_out⟩ :=
    Multidigraph.isArcCut_outArcs (Multidigraph.arcSrc G) (Multidigraph.arcTgt G) hs ht q hq
  rw [Multidigraph.mem_outArcs] at he_out
  exact ⟨e.1, hzip ▸ List.mem_map_of_mem he, mem_outArcs.mpr ⟨he_out.1, he_out.2, e.2⟩⟩

/-- **Closed-set certificate for directed separators.** If `S` holds on `A \ Y`, fails on `B \ Y`,
and every arc leaving `S` enters `Y`, then `Y` separates `A` from `B`. -/
theorem isSeparator_of_forall_adj {G : Digraph V} {A B Y : Set V} (S : V → Prop)
    (hstep : ∀ ⦃u v⦄, G.Adj u v → S u → v ∉ Y → S v)
    (hA : ∀ a ∈ A, a ∉ Y → S a) (hB : ∀ b ∈ B, b ∉ Y → ¬ S b) :
    G.IsSeparator A B Y := by
  intro a ha b hb p hp
  obtain ⟨q, hq, hverts, -⟩ := liftDipath hp
  rw [← hverts]
  exact Multidigraph.isSeparator_of_forall_src_tgt (Multidigraph.arcSrc G) (Multidigraph.arcTgt G)
    S (fun e => hstep e.2) hA hB ha hb q hq

/-- Closed-set certificate for a vertex cut: if `s ∈ S`, `t ∉ S`, `T` avoids `s` and `t`, and
every arc leaving `S` ends in `T`, then `T` is an `s`–`t` vertex cut. -/
theorem isVertexCut_of_forall_adj {G : Digraph V} {s t : V} {S T : Finset V} (hs : s ∈ S)
    (ht : t ∉ S) (hsT : s ∉ T) (htT : t ∉ T) (hST : ∀ u ∈ S, ∀ v, G.Adj u v → v ∉ S → v ∈ T) :
    G.IsVertexCut s t T := by
  refine ⟨hsT, htT, fun p hp => ?_⟩
  obtain ⟨q, hq, hverts, -⟩ := liftDipath hp
  rw [← hverts]
  exact (Multidigraph.isVertexCut_of_forall_src_tgt (Multidigraph.arcSrc G) (Multidigraph.arcTgt G)
    hs ht hsT htT fun e hu => hST e.1.1 hu e.1.2 e.2).2.2 q hq

/-- **Weak duality for arc-disjoint paths**: `k` pairwise arc-disjoint directed `s`–`t` paths need
at least `k` arcs in every `s`–`t` arc cut. -/
theorem card_le_card_of_arcDisjoint_of_isArcCut {G : Digraph V} {s t : V} {k : ℕ}
    {P : Fin k → List V} (hP : ∀ i, G.IsDipath s t (P i)) (hdisj : ArcDisjoint P)
    {C : Finset (V × V)} (hC : G.IsArcCut s t C) : k ≤ C.card := by
  classical
  let Q : Fin k → List (Multidigraph.Arc G) := fun i => (liftDipath (hP i)).1
  have hQ : ∀ i, Multidigraph.IsDipath (Multidigraph.arcSrc G) (Multidigraph.arcTgt G) s t (Q i) :=
    fun i => (liftDipath (hP i)).2.1
  have hQdisj : Pairwise fun i j => (Q i).Disjoint (Q j) := fun i j hij e hei hej =>
    hdisj hij e.1 ((liftDipath (hP i)).2.2.2 ▸ List.mem_map_of_mem hei)
      ((liftDipath (hP j)).2.2.2 ▸ List.mem_map_of_mem hej)
  let C' : Finset (Multidigraph.Arc G) := C.subtype fun e => G.Adj e.1 e.2
  have hC' : Multidigraph.IsArcCut (Multidigraph.arcSrc G) (Multidigraph.arcTgt G) s t C' := by
    intro q hq
    obtain ⟨e, he, heC⟩ := hC _ (isDipath_of_multidigraph hq)
    rw [hq.zip_tail_vertices, List.mem_map] at he
    obtain ⟨a, ha, rfl⟩ := he
    exact ⟨a, ha, Finset.mem_subtype.mpr heC⟩
  have hle : C'.card ≤ C.card := by
    rw [← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
    refine Finset.card_le_card fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_subtype.mp hy
  exact (Multidigraph.card_le_card_of_disjoint_of_isArcCut _ _ hQ hQdisj hC').trans hle

/-- **Weak duality for internally disjoint paths**: `k` pairwise internally disjoint directed
`s`–`t` paths need at least `k` vertices in every `s`–`t` vertex cut. -/
theorem card_le_card_of_internallyDisjoint_of_isVertexCut {G : Digraph V} {s t : V} {k : ℕ}
    {P : Fin k → List V} (hP : ∀ i, G.IsDipath s t (P i)) (hdisj : InternallyDisjoint s t P)
    {T : Finset V} (hT : G.IsVertexCut s t T) : k ≤ T.card := by
  let Q : Fin k → List (Multidigraph.Arc G) := fun i => (liftDipath (hP i)).1
  have hQ : ∀ i, Multidigraph.IsDipath (Multidigraph.arcSrc G) (Multidigraph.arcTgt G) s t (Q i) :=
    fun i => (liftDipath (hP i)).2.1
  have hverts : ∀ i, s :: (Q i).map (Multidigraph.arcTgt G) = P i :=
    fun i => (liftDipath (hP i)).2.2.1
  have hQdisj : Multidigraph.InternallyDisjoint (Multidigraph.arcTgt G) s t Q :=
    fun i j hij v hvi hvj => by
      rw [hverts i] at hvi
      rw [hverts j] at hvj
      exact hdisj hij v hvi hvj
  have hT' : Multidigraph.IsVertexCut (Multidigraph.arcSrc G) (Multidigraph.arcTgt G) s t T :=
    ⟨hT.1, hT.2.1, fun q hq => hT.2.2 _ (isDipath_of_multidigraph hq)⟩
  exact Multidigraph.card_le_card_of_internallyDisjoint_of_isVertexCut _ _ hQ hQdisj hT'

/-- **Weak duality for vertex-disjoint `A`–`B` paths**: `k` pairwise vertex-disjoint directed
`A`–`B` paths need at least `k` vertices in every `A`–`B` separator. -/
theorem card_le_card_of_disjoint_of_isSeparator {G : Digraph V} {A B : Set V} {k : ℕ}
    {P : Fin k → List V} (hP : ∀ i, ∃ a ∈ A, ∃ b ∈ B, G.IsDipath a b (P i))
    (hdisj : Pairwise fun i j => (P i).Disjoint (P j))
    {Y : Finset V} (hY : G.IsSeparator A B ↑Y) : k ≤ Y.card := by
  choose a ha b hb hPi using hP
  let Q : Fin k → List (Multidigraph.Arc G) := fun i => (liftDipath (hPi i)).1
  have hQ : ∀ i,
      Multidigraph.IsDipath (Multidigraph.arcSrc G) (Multidigraph.arcTgt G) (a i) (b i) (Q i) :=
    fun i => (liftDipath (hPi i)).2.1
  have hverts : ∀ i, a i :: (Q i).map (Multidigraph.arcTgt G) = P i :=
    fun i => (liftDipath (hPi i)).2.2.1
  have hQdisj : Pairwise fun i j =>
      (a i :: (Q i).map (Multidigraph.arcTgt G)).Disjoint
        (a j :: (Q j).map (Multidigraph.arcTgt G)) :=
    fun i j hij => by dsimp only; rw [hverts i, hverts j]; exact hdisj hij
  have hY' : Multidigraph.IsSeparator (Multidigraph.arcSrc G) (Multidigraph.arcTgt G) A B ↑Y :=
    fun _ hx _ hy _ hq => hY hx hy _ (isDipath_of_multidigraph hq)
  exact Multidigraph.card_le_card_of_disjoint_of_isSeparator _ _ ha hb hQ hQdisj hY'

end Digraph
