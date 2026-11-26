/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.FunctionalGraph
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Heavy nodes and pieces of a tree by stages

A tree by stages (`Cslib.StagedTree`) is a rooted tree given by the parents of its nodes, in which
every node has a stage: the root alone is at the top stage, the depth, and every other node is one
stage below its parent. A node `q` is below a node `p` (`Cslib.StagedTree.Below`) if `p` is `q` or
an ancestor of `q`.

For two weights `g` and `u` on the nodes, two budgets `M` and `Y` and a number `k`, a node `p` is
heavy (`Cslib.StagedTree.Heavy`) if it is the root or if the weights below it satisfy
`g / (4 M) + u / (2 Y) > 1 / k`. Parents of heavy nodes are heavy, and, as the sets below the nodes
of one stage are disjoint, every stage has fewer than `k` heavy nodes other than the root when
`g` adds up to at most `M` and `u` to at most `Y`. The heads (`Cslib.StagedTree.IsHead`) are the
root and the children of heavy nodes. The piece of a node (`Cslib.StagedTree.piece`) is the number
of the first head on the way up from it (`Cslib.StagedTree.pieceHead`), where the heads are
numbered in increasing order (`Cslib.StagedTree.headRank`). So the nodes of a piece are one heavy
node or lie below a light node, and a sum over a piece is at most a value at one node or a sum
below a light node (`Cslib.StagedTree.sum_piece_le`). If the root has at most `C` children and
every other node at most `b`, there are fewer than `1 + C + b d k` pieces for the depth `d`
(`Cslib.StagedTree.piece_lt`), and the edges between a piece and the other nodes all meet one
node (`Cslib.StagedTree.exists_piece_boundary`).

## Main definitions

* `Cslib.StagedTree`: a rooted tree by stages.
* `Cslib.StagedTree.Below`, `Cslib.StagedTree.sumBelow`, `Cslib.StagedTree.children`: the nodes
  below a node, the sum of a function over them, and the children of a node.
* `Cslib.StagedTree.Heavy`, `Cslib.StagedTree.IsHead`: heavy nodes and the heads of pieces.
* `Cslib.StagedTree.pieceHead`, `Cslib.StagedTree.headRank`, `Cslib.StagedTree.piece`: the head
  of the piece of a node, the number of a head, and the piece of a node.

## Main results

* `Cslib.StagedTree.sumBelow_children_le`: a sum over the children of the nodes below a node is
  at most the sum over the nodes below it.
* `Cslib.StagedTree.light_given_le`, `Cslib.StagedTree.light_units_le`: the weights below a light
  node.
* `Cslib.StagedTree.sum_piece_le`: a sum over a piece.
* `Cslib.StagedTree.piece_lt`, `Cslib.StagedTree.piece_lt_card`: the number of pieces.
* `Cslib.StagedTree.exists_piece_boundary`: the edges out of a piece meet one node.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition J.2, p. 52, and its proof ("Heavy nodes and pieces", p. 53); module `Paper.Heavy`
-/

public section

namespace Cslib

open Finset Function

/-- A rooted tree by stages on the nodes `α`: every node has a parent and a stage, the root alone
is at the top stage `depth`, and every other node is one stage below its parent. The parent of the
root is not used. -/
structure StagedTree (α : Type*) where
  /-- The parent of a node. -/
  parent : α → α
  /-- The stage of a node. -/
  stage : α → ℕ
  /-- The stage of the root. -/
  depth : ℕ
  /-- The root. -/
  root : α
  stage_le (p : α) : stage p ≤ depth
  stage_eq_depth_iff {p : α} : stage p = depth ↔ p = root
  stage_parent {p : α} : p ≠ root → stage (parent p) = stage p + 1

namespace StagedTree

variable {α : Type*} (T : StagedTree α)

/-- The node `q` is below the node `p`: `p` is `q` or an ancestor of `q`, so it is reached from `q`
in `stage p - stage q` steps up. -/
@[expose] def Below (q p : α) : Prop :=
  T.stage q ≤ T.stage p ∧ T.parent^[T.stage p - T.stage q] q = p

instance [DecidableEq α] : DecidableRel T.Below := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

section Sums

variable [Fintype α] [DecidableEq α]

/-- The sum of `f` over the nodes below `p`. -/
@[expose] def sumBelow (f : α → ℕ) (p : α) : ℕ := ∑ q ∈ univ.filter (T.Below · p), f q

/-- The children of a node: the nodes other than the root whose parent it is. -/
@[expose] def children (p : α) : Finset α := univ.filter fun q => q ≠ T.root ∧ T.parent q = p

end Sums

variable {T}

private theorem stage_lt_depth {p : α} (hp : p ≠ T.root) : T.stage p < T.depth :=
  (T.stage_le p).lt_of_ne (hp ∘ T.stage_eq_depth_iff.1)

private theorem below_refl (p : α) : T.Below p p := ⟨le_rfl, by rw [Nat.sub_self]; rfl⟩

private theorem below_parent {p : α} (hp : p ≠ T.root) : T.Below p (T.parent p) :=
  ⟨by rw [T.stage_parent hp]; omega, by rw [T.stage_parent hp, Nat.add_sub_cancel_left]; rfl⟩

private theorem below_trans {a b c : α} (h : T.Below a b) (h' : T.Below b c) : T.Below a c :=
  ⟨h.1.trans h'.1, by rw [← Nat.sub_add_sub_cancel h'.1 h.1, iterate_add_apply, h.2, h'.2]⟩

section Sums

variable [Fintype α] [DecidableEq α]

private theorem sumBelow_mono (f : α → ℕ) {q p : α} (h : T.Below q p) :
    T.sumBelow f q ≤ T.sumBelow f p :=
  sum_le_sum_of_subset fun _ hr => mem_filter.2 ⟨mem_univ _, below_trans (mem_filter.1 hr).2 h⟩

/-- The sets below the nodes of one stage are disjoint. -/
private theorem sum_sumBelow_le (f : α → ℕ) (s : ℕ) :
    ∑ p ∈ univ.filter (T.stage · = s), T.sumBelow f p ≤ ∑ q, f q := by
  simp only [sumBelow]
  rw [← sum_biUnion fun p hp p' hp' hne => disjoint_left.2 fun q h h' => hne ?_]
  · exact sum_le_sum_of_subset (subset_univ _)
  simp only [coe_filter, Set.mem_ofPred_eq, mem_filter, mem_univ, true_and] at hp hp' h h'
  rw [← h.2, ← h'.2, hp, hp']

/-- A sum over the children of the nodes below `p` is at most the sum over the nodes below `p`. -/
theorem sumBelow_children_le (f : α → ℕ) (p : α) :
    T.sumBelow (fun q => ∑ c ∈ T.children q, f c) p ≤ T.sumBelow f p := by
  simp only [sumBelow]
  rw [← sum_biUnion fun q _ q' _ hne => disjoint_left.2 fun c hc hc' => hne ?_]
  · refine sum_le_sum_of_subset fun c hc => ?_
    obtain ⟨q, hq, hc⟩ := mem_biUnion.1 hc
    simp only [children, mem_filter, mem_univ, true_and] at hq hc ⊢
    exact below_trans (hc.2 ▸ below_parent hc.1) hq
  · simp only [children, mem_filter, mem_univ, true_and] at hc hc'
    exact hc.2.symm.trans hc'.2

end Sums

/-! ### Heavy nodes and pieces -/

variable (T) [Fintype α] [LinearOrder α] (g u : α → ℕ) (M Y k : ℕ)

/-- A node is heavy for the weights `g` and `u`, the budgets `M` and `Y` and the number `k` if it
is the root or if `sumBelow g p / (4 M) + sumBelow u p / (2 Y) > 1 / k`, multiplied out:
`8 M Y < k (2 Y · sumBelow g p + 4 M · sumBelow u p)`. -/
@[expose] def Heavy (p : α) : Prop :=
  p = T.root ∨ 8 * M * Y < k * (T.sumBelow g p * (2 * Y) + T.sumBelow u p * (4 * M))

instance : DecidablePred (T.Heavy g u M Y k) := fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The heads of the pieces: the root and the children of heavy nodes. -/
@[expose] def IsHead (p : α) : Prop := p = T.root ∨ T.Heavy g u M Y k (T.parent p)

instance : DecidablePred (T.IsHead g u M Y k) := fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The head of the piece of a node: the first head on the way up from it (`stage p` is at most
`depth`, and the root is a head). -/
@[expose] def pieceHead (p : α) : α :=
  (FunctionalGraph.absorb T.parent (T.IsHead g u M Y k))^[T.depth - T.stage p] p

/-- The number of a head: the number of heads that are smaller in the order of `α`. -/
@[expose] def headRank (p : α) : ℕ := (univ.filter fun q => q < p ∧ T.IsHead g u M Y k q).card

/-- The piece of a node: the number of the head of its piece. -/
@[expose] def piece (p : α) : ℕ := T.headRank g u M Y k (T.pieceHead g u M Y k p)

variable {T g u M Y k}

private theorem heavy_parent {p : α} (hp : p ≠ T.root) (h : T.Heavy g u M Y k p) :
    T.Heavy g u M Y k (T.parent p) :=
  Or.inr <| (h.resolve_left hp).trans_le <| by
    gcongr <;> exact sumBelow_mono _ (below_parent hp)

private theorem isHead_of_heavy {p : α} (h : T.Heavy g u M Y k p) : T.IsHead g u M Y k p :=
  (eq_or_ne p T.root).imp id fun hp => heavy_parent hp h

/-- Every stage has fewer than `k` heavy nodes other than the root. -/
private theorem card_heavy_lt (hk : 0 < k) (hg : ∑ q, g q ≤ M) (hu : ∑ q, u q ≤ Y) (s : ℕ) :
    ((univ.filter fun p => p ≠ T.root ∧ T.Heavy g u M Y k p).filter (T.stage · = s)).card < k := by
  set S := (univ.filter fun p => p ≠ T.root ∧ T.Heavy g u M Y k p).filter (T.stage · = s)
  have hS : S ⊆ univ.filter (T.stage · = s) := filter_subset_filter _ (subset_univ _)
  have h : S.card * (8 * M * Y + 1) ≤ k * (M * (2 * Y) + Y * (4 * M)) := calc
    S.card * (8 * M * Y + 1) = ∑ _p ∈ S, (8 * M * Y + 1) := by rw [sum_const, smul_eq_mul]
    _ ≤ ∑ p ∈ S, k * (T.sumBelow g p * (2 * Y) + T.sumBelow u p * (4 * M)) :=
      sum_le_sum fun p hp => by
        simp only [S, mem_filter, mem_univ, true_and] at hp
        exact hp.1.2.resolve_left hp.1.1
    _ = k * ((∑ p ∈ S, T.sumBelow g p) * (2 * Y) + (∑ p ∈ S, T.sumBelow u p) * (4 * M)) := by
      rw [← mul_sum, sum_add_distrib, sum_mul, sum_mul]
    _ ≤ _ := by
      gcongr
      · exact (sum_le_sum_of_subset hS).trans ((sum_sumBelow_le g s).trans hg)
      · exact (sum_le_sum_of_subset hS).trans ((sum_sumBelow_le u s).trans hu)
  by_contra hc
  nlinarith [Nat.mul_le_mul_right (8 * M * Y + 1) (not_lt.1 hc), Nat.zero_le (k * M * Y)]

private theorem pieceHead_of_isHead {p : α} (h : T.IsHead g u M Y k p) :
    T.pieceHead g u M Y k p = p :=
  FunctionalGraph.absorb_iterate_of_pos _ _ h _

private theorem pieceHead_parent {p : α} (h : ¬T.IsHead g u M Y k p) :
    T.pieceHead g u M Y k p = T.pieceHead g u M Y k (T.parent p) := by
  have hr : p ≠ T.root := fun e => h (Or.inl e)
  have := stage_lt_depth hr
  rw [pieceHead, pieceHead, T.stage_parent hr,
    show T.depth - T.stage p = T.depth - (T.stage p + 1) + 1 by omega, iterate_succ_apply,
    FunctionalGraph.absorb, ite_eq_right h]

/-- The head of the piece of `p` is a head above `p`, and it is `p` or a light node. -/
private theorem pieceHead_spec (p : α) : T.IsHead g u M Y k (T.pieceHead g u M Y k p) ∧
    T.Below p (T.pieceHead g u M Y k p) ∧
    (T.pieceHead g u M Y k p = p ∨ ¬T.Heavy g u M Y k (T.pieceHead g u M Y k p)) := by
  by_cases h : T.IsHead g u M Y k p
  · rw [pieceHead_of_isHead h]
    exact ⟨h, below_refl p, Or.inl rfl⟩
  · have hr : p ≠ T.root := fun e => h (Or.inl e)
    obtain ⟨h1, h2, h3⟩ := pieceHead_spec (T.parent p)
    rw [pieceHead_parent h]
    exact ⟨h1, below_trans (below_parent hr) h2,
      Or.inr (h3.elim (fun e hh => h (Or.inr (e ▸ hh))) id)⟩
termination_by T.depth - T.stage p
decreasing_by
  have := stage_lt_depth hr
  rw [T.stage_parent hr]
  omega

private theorem headRank_injOn : Set.InjOn (T.headRank g u M Y k) {p | T.IsHead g u M Y k p} :=
  StrictMonoOn.injOn fun x hx y _ hxy => card_lt_card <| (ssubset_iff_of_subset fun q hq => by
    simp only [mem_filter, mem_univ, true_and] at hq ⊢
    exact ⟨hq.1.trans hxy, hq.2⟩).2 ⟨x, by simp_all, by simp⟩

private theorem piece_of_isHead {p : α} (h : T.IsHead g u M Y k p) :
    T.piece g u M Y k p = T.headRank g u M Y k p := by
  rw [piece, pieceHead_of_isHead h]

private theorem piece_lt_card_heads (p : α) :
    T.piece g u M Y k p < (univ.filter (T.IsHead g u M Y k)).card :=
  card_lt_card <| (ssubset_iff_of_subset fun _ hq => mem_filter.2 ⟨mem_univ _,
    (mem_filter.1 hq).2.2⟩).2 ⟨_, mem_filter.2 ⟨mem_univ _, (pieceHead_spec p).1⟩, by simp⟩

/-- The pieces are numbered below the number of nodes. -/
theorem piece_lt_card (p : α) : T.piece g u M Y k p < Fintype.card α :=
  (piece_lt_card_heads p).trans_le ((card_filter_le _ _).trans_eq card_univ)

/-- **The number of pieces** ("each stage has fewer than `k` heavy nodes", "so there are at most
`kΛ` pieces"): if the root has at most `C` children and every other node at most `b`, the pieces
are numbered below `1 + C + b d k` for the depth `d`. -/
theorem piece_lt (hk : 0 < k) (hg : ∑ q, g q ≤ M) (hu : ∑ q, u q ≤ Y) {b C : ℕ}
    (hb : ∀ p, p ≠ T.root → (T.children p).card ≤ b) (hC : (T.children T.root).card ≤ C)
    (p : α) : T.piece g u M Y k p < 1 + C + b * (T.depth * k) := by
  set S := univ.filter fun y => y ≠ T.root ∧ T.Heavy g u M Y k y
  have hS : S.card ≤ k * T.depth := by
    refine (card_le_mul_card_image S k fun s _ => (card_heavy_lt hk hg hu s).le).trans
      (Nat.mul_le_mul_left k ((card_le_card fun s hs => ?_).trans (card_range _).le))
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hs
    exact mem_range.2 (stage_lt_depth (mem_filter.1 hy).2.1)
  have hH : univ.filter (T.IsHead g u M Y k) ⊆
      insert T.root (T.children T.root ∪ S.biUnion T.children) := by
    intro q hq
    rcases (mem_filter.1 hq).2 with rfl | hh
    · exact mem_insert_self _ _
    rcases eq_or_ne q T.root with rfl | hr
    · exact mem_insert_self _ _
    refine mem_insert_of_mem ?_
    rcases eq_or_ne (T.parent q) T.root with hpr | hpr
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hr, hpr⟩)
    · exact mem_union_right _ (mem_biUnion.2
        ⟨_, mem_filter.2 ⟨mem_univ _, hpr, hh⟩, mem_filter.2 ⟨mem_univ _, hr, rfl⟩⟩)
  have hB : (S.biUnion T.children).card ≤ S.card * b := card_biUnion_le.trans
    ((sum_le_card_nsmul _ _ _ fun y hy => hb y (mem_filter.1 hy).2.1).trans_eq (smul_eq_mul _ _))
  calc _ < _ := piece_lt_card_heads p
    _ ≤ _ := card_le_card hH
    _ ≤ (T.children T.root ∪ S.biUnion T.children).card + 1 := card_insert_le _ _
    _ ≤ C + S.card * b + 1 := by
      gcongr
      exact (card_union_le _ _).trans (add_le_add hC hB)
    _ ≤ _ := by nlinarith [Nat.mul_le_mul_right b hS]

/-- **A sum over a piece**: if `f` is at most `B` at every node and its sum below every light node
is at most `B`, then so is its sum over the nodes of the piece `n`, since these are one heavy node
or lie below a light node. -/
theorem sum_piece_le (f : α → ℕ) {B : ℕ} (hB : ∀ p, f p ≤ B)
    (hl : ∀ x, ¬T.Heavy g u M Y k x → T.sumBelow f x ≤ B) (n : ℕ) :
    ∑ p ∈ univ.filter (T.piece g u M Y k · = n), f p ≤ B := by
  rcases (univ.filter (T.piece g u M Y k · = n)).eq_empty_or_nonempty with he | ⟨p₀, hp₀⟩
  · rw [he, sum_empty]
    exact Nat.zero_le _
  set x := T.pieceHead g u M Y k p₀
  have hx : ∀ p ∈ univ.filter (T.piece g u M Y k · = n), T.pieceHead g u M Y k p = x :=
    fun p hp => headRank_injOn (pieceHead_spec p).1 (pieceHead_spec p₀).1
      ((mem_filter.1 hp).2.trans (mem_filter.1 hp₀).2.symm)
  by_cases hh : T.Heavy g u M Y k x
  · refine (sum_le_sum_of_subset (t := {x}) fun p hp => mem_singleton.2 ?_).trans
      (by rw [sum_singleton]; exact hB x)
    have h := (pieceHead_spec (T := T) (g := g) (u := u) (M := M) (Y := Y) (k := k) p).2.2
    rw [hx p hp] at h
    exact (h.resolve_right (not_not.2 hh)).symm
  · exact (sum_le_sum_of_subset fun p hp =>
      mem_filter.2 ⟨mem_univ _, hx p hp ▸ (pieceHead_spec p).2.1⟩).trans (hl x hh)

private theorem light_le {x : α} (hx : ¬T.Heavy g u M Y k x) :
    k * (T.sumBelow g x * (2 * Y) + T.sumBelow u x * (4 * M)) ≤ 8 * M * Y :=
  not_lt.1 fun h => hx (Or.inr h)

/-- Below a light node `g` adds up to at most `4 M / k`. -/
theorem light_given_le (hY : 0 < Y) {x : α} (hx : ¬T.Heavy g u M Y k x) :
    k * T.sumBelow g x ≤ 4 * M :=
  Nat.le_of_mul_le_mul_right (c := 2 * Y) (by
    rw [mul_assoc]
    exact (Nat.mul_le_mul_left k (Nat.le_add_right _ _)).trans
      ((light_le hx).trans_eq (show 8 * M * Y = 4 * M * (2 * Y) by ring)))
    (by omega)

/-- Below a light node `u` adds up to at most `2 Y / k`. -/
theorem light_units_le (hM : 0 < M) {x : α} (hx : ¬T.Heavy g u M Y k x) :
    k * T.sumBelow u x ≤ 2 * Y :=
  Nat.le_of_mul_le_mul_right (c := 4 * M) (by
    rw [mul_assoc]
    exact (Nat.mul_le_mul_left k (Nat.le_add_left _ _)).trans
      ((light_le hx).trans_eq (show 8 * M * Y = 2 * Y * (4 * M) by ring)))
    (by omega)

/-- **The boundary of a piece**: the edges between a node and its parent of which exactly one end
is in the piece `n` all meet one node, the head of the piece (there are no such edges if no node is
in the piece `n`). -/
theorem exists_piece_boundary (n : ℕ) : ∃ x, ∀ q, q ≠ T.root →
    ¬(T.piece g u M Y k q = n ↔ T.piece g u M Y k (T.parent q) = n) →
      q = x ∨ T.parent q = x := by
  have key : ∀ q, q ≠ T.root → ¬(T.piece g u M Y k q = n ↔ T.piece g u M Y k (T.parent q) = n) →
      ∃ y, T.IsHead g u M Y k y ∧ T.headRank g u M Y k y = n ∧ (q = y ∨ T.parent q = y) := by
    intro q hr hne
    have hq : T.IsHead g u M Y k q := by
      by_contra h
      exact hne (by rw [piece, pieceHead_parent h]; rfl)
    have hp := isHead_of_heavy (hq.resolve_left hr)
    by_cases h1 : T.piece g u M Y k q = n
    · exact ⟨q, hq, (piece_of_isHead hq).symm.trans h1, Or.inl rfl⟩
    · exact ⟨_, hp, (piece_of_isHead hp).symm.trans (by tauto), Or.inr rfl⟩
  by_cases hex : ∃ y, T.IsHead g u M Y k y ∧ T.headRank g u M Y k y = n
  · obtain ⟨x, hx, hxn⟩ := hex
    refine ⟨x, fun q hr hne => ?_⟩
    obtain ⟨y, hy, hyn, h⟩ := key q hr hne
    rwa [headRank_injOn hx hy (hxn.trans hyn.symm)]
  · exact ⟨T.root, fun q hr hne => absurd ((key q hr hne).imp fun y h => ⟨h.1, h.2.1⟩) hex⟩

end StagedTree

end Cslib
