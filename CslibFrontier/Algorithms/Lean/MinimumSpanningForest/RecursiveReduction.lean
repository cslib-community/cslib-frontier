/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

-- upstream: candidate
public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.PartitionCharge
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Recursive minimum spanning forest reduction

The recursive control flow of [Pettie and Ramachandran, §5][PettieRamachandran2002] partitions
the non-isolated vertices, sparsifies using an MSF of each small component and the terminal
quotient, applies two simultaneous Borůvka passes, and recurses on the resulting graph. We
prove correctness and termination on the number of active non-loop labels. The component grower
and the two kinds of MSF subroutine are parameters of the reduction.
-/

public section

namespace Cslib.Multigraph.PettieRamachandran

open Finset

variable {E V W : Type*} [LinearOrder W]

/-- Active edge labels with distinct endpoints. -/
noncomputable def nonloops (ends : E → Sym2 V) (S : Finset E) : Finset E := by
  classical exact S.filter fun e => ¬ (ends e).IsDiag

/-- Membership in the active non-loop edge set. -/
theorem mem_nonloops {ends : E → Sym2 V} {S : Finset E} {e : E} :
    e ∈ nonloops ends S ↔ e ∈ S ∧ ¬ (ends e).IsDiag := by
  classical exact mem_filter

@[simp] theorem support_nonloops (ends : E → Sym2 V) (S : Finset E) :
    support ends (nonloops ends S) = support ends S := by
  classical exact support_filter_not_isDiag ends S

theorem msf_nonloops (ends : E → Sym2 V) (w : E → W) (S : Finset E) :
    msf ends w (nonloops ends S) = msf ends w S := by
  classical exact msf_filter_not_isDiag w ends S

/-- A simultaneous Borůvka pass selects the minimum-weight leaving edge at every vertex with
a nonempty singleton cut. Distinct weights ensure each such choice is unique. -/
noncomputable def boruvkaEdges (ends : E → Sym2 V) (w : E → W) (S : Finset E) : Finset E := by
  classical
  exact S.filter fun e => ∃ v : V, e ∈ (toGraph ends).edgeCut {v} ∧
    ∀ f ∈ S, f ∈ (toGraph ends).edgeCut {v} → w e ≤ w f

theorem boruvkaEdges_subset_msf (ends : E → Sym2 V) (w : E → W) (S : Finset E) :
    boruvkaEdges ends w S ⊆ msf ends w S := by
  classical
  intro e he
  obtain ⟨heS, v, hcut, least⟩ := mem_filter.1 he
  exact mem_msf_of_mem_edgeCut w heS hcut least

private theorem boruvkaEdges_nonempty {ends : E → Sym2 V} {w : E → W} {S : Finset E}
    (h : (nonloops ends S).Nonempty) : (boruvkaEdges ends w S).Nonempty := by
  classical
  obtain ⟨e, he⟩ := h
  obtain ⟨heS, hn⟩ := mem_nonloops.1 he
  obtain ⟨a, b, hab⟩ : ∃ a b, ends e = s(a, b) :=
    Sym2.inductionOn (ends e) fun a b => ⟨a, b, rfl⟩
  have hne : a ≠ b := by simpa [hab] using hn
  let B := S.filter fun f => f ∈ (toGraph ends).edgeCut ({a} : Set V)
  have heB : e ∈ B := mem_filter.2
    ⟨heS, Graph.mem_edgeCut_iff.2 ⟨a, b, hab, rfl, Ne.symm hne⟩⟩
  obtain ⟨f, hf, less⟩ := B.exists_min_image w ⟨e, heB⟩
  obtain ⟨hfS, hfcut⟩ := mem_filter.1 hf
  exact ⟨f, mem_filter.2 ⟨hfS, a, hfcut, fun g hg cut => less g (mem_filter.2 ⟨hg, cut⟩)⟩⟩

variable [DecidableEq E]

/-- A contraction step keeps chosen labels for reconstruction and updates the endpoints
of the remaining active labels. -/
structure Pass (V E : Type*) where
  /-- Original labels selected during this pass. -/
  chosen : Finset E
  /-- Endpoint map after contraction. -/
  ends : E → Sym2 V
  /-- Unselected labels that still have distinct endpoints. -/
  remaining : Finset E

/-- Apply one simultaneous Borůvka pass and discard the loops it creates. -/
noncomputable def boruvka (ends : E → Sym2 V) (w : E → W) (S : Finset E) : Pass V E :=
  let F := boruvkaEdges ends w S
  let next := Sym2.map (contract ends (F : Set E)) ∘ ends
  ⟨F, next, nonloops next (S \ F)⟩

theorem boruvka_msf (ends : E → Sym2 V) (w : E → W) (S : Finset E) (hw : Function.Injective w) :
    (boruvka ends w S).chosen ∪ msf (boruvka ends w S).ends w (boruvka ends w S).remaining =
      msf ends w S := by
  dsimp only [boruvka]
  rw [msf_nonloops]
  exact (msf_eq_union_msf_map w hw (boruvkaEdges_subset_msf ends w S)
    (fun _ _ => contract_eq_contract_iff)).symm

private theorem remaining_subset (ends : E → Sym2 V) (w : E → W) (S : Finset E) :
    (boruvka ends w S).remaining ⊆ S := fun _ he => (mem_sdiff.1 (mem_nonloops.1 he).1).1

private theorem remaining_card_lt {ends : E → Sym2 V} {w : E → W} {S : Finset E}
    (h : (boruvkaEdges ends w S).Nonempty) : (boruvka ends w S).remaining.card < S.card := by
  apply card_lt_card ((ssubset_iff_of_subset (remaining_subset ends w S)).2 ?_)
  obtain ⟨e, he⟩ := h
  exact ⟨e, msf_subset w (boruvkaEdges_subset_msf ends w S he),
    fun hg => (mem_sdiff.1 (mem_nonloops.1 hg).1).2 he⟩

omit [DecidableEq E] in
private theorem boruvka_partner (ends : E → Sym2 V) (w : E → W) (S : Finset E)
    {u : V} (hu : u ∈ support ends S) :
    ∃ v ∈ support ends S, v ≠ u ∧
      contract ends (boruvkaEdges ends w S : Set E) v =
        contract ends (boruvkaEdges ends w S) u := by
  classical
  obtain ⟨e, he, nd, inc⟩ := mem_support.1 hu
  obtain ⟨a, b, hab⟩ : ∃ a b, ends e = s(a, b) :=
    Sym2.inductionOn (ends e) fun a b => ⟨a, b, rfl⟩
  have ab : a ≠ b := by simpa [hab] using nd
  have cut : e ∈ (toGraph ends).edgeCut ({u} : Set V) := by
    rcases (Sym2.mem_iff.mp (hab ▸ inc)) with rfl | rfl
    · exact Graph.mem_edgeCut_iff.2 ⟨u, b, hab, rfl, ab.symm⟩
    · exact Graph.mem_edgeCut_iff.2 ⟨u, a, hab.trans Sym2.eq_swap, rfl, ab⟩
  let B := S.filter fun f => f ∈ (toGraph ends).edgeCut ({u} : Set V)
  have heB : e ∈ B := mem_filter.2 ⟨he, cut⟩
  obtain ⟨g, hg, least⟩ := B.exists_min_image w ⟨e, heB⟩
  obtain ⟨hgS, hgcut⟩ := mem_filter.1 hg
  obtain ⟨a, v, hav, ha, hv⟩ := Graph.mem_edgeCut_iff.1 hgcut
  change a = u at ha
  subst a
  change ends g = s(u, v) at hav
  have hgB : g ∈ boruvkaEdges ends w S :=
    mem_filter.2 ⟨hgS, u, hgcut, fun f hf hcut => least f (mem_filter.2 ⟨hf, hcut⟩)⟩
  refine ⟨v, mem_support.2 ⟨g, hgS, ?_, by simp [hav]⟩, hv, ?_⟩
  · simpa [hav] using Ne.symm hv
  · exact contract_eq_contract_iff.2 ((Joins.of_mem hgB hav).symm)

/-- A simultaneous pass halves the number of non-isolated vertices. Every non-isolated input
vertex shares a quotient class with a distinct partner across its chosen singleton cut. -/
theorem boruvka_support_le (ends : E → Sym2 V) (w : E → W) (S : Finset E) :
    2 * (support (boruvka ends w S).ends (boruvka ends w S).remaining).card ≤
      (support ends S).card := by
  classical
  let X := support ends S
  let B := boruvka ends w S
  let q := contract ends (boruvkaEdges ends w S : Set E)
  have into : support B.ends B.remaining ⊆ X.image q := by
    intro u hu
    obtain ⟨e, he, nd, inc⟩ := mem_support.1 hu
    obtain ⟨a, b, hab⟩ : ∃ a b, ends e = s(a, b) :=
      Sym2.inductionOn (ends e) fun a b => ⟨a, b, rfl⟩
    have hp : B.ends e = s(q a, q b) := by simp [B, boruvka, q, hab]
    have hqa : q a ≠ q b := by simpa [hp] using nd
    have hd : ¬ (ends e).IsDiag := by simpa [hab] using (fun h => hqa (congrArg q h))
    have hin := remaining_subset ends w S he
    rcases (Sym2.mem_iff.mp (hp ▸ inc)) with rfl | rfl
    · exact mem_image_of_mem _ (mem_support.2 ⟨e, hin, hd, by simp [hab]⟩)
    · exact mem_image_of_mem _ (mem_support.2 ⟨e, hin, hd, by simp [hab]⟩)
  have paired : ∀ u ∈ X.image q, 2 ≤ (X.filter fun v => q v = u).card := by
    intro u hu
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hu
    obtain ⟨b, hb, distinct, eq⟩ := boruvka_partner ends w S ha
    have two : ({a, b} : Finset V) ⊆ X.filter (fun x => q x = q a) := by
      intro z hz
      rcases mem_insert.1 hz with rfl | hz
      · exact mem_filter.2 ⟨ha, rfl⟩
      · obtain rfl := mem_singleton.1 hz
        exact mem_filter.2 ⟨hb, eq⟩
    simpa [distinct.symm] using card_le_card two
  calc
    _ ≤ 2 * (X.image q).card := Nat.mul_le_mul_left _ (card_le_card into)
    _ = ∑ _ ∈ X.image q, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ u ∈ X.image q, (X.filter fun v => q v = u).card := sum_le_sum paired
    _ = _ := (card_eq_sum_card_image q X).symm

/-- One Borůvka pass halves the number of edges in the residual minimum spanning forest.
Every non-isolated vertex is incident to a chosen edge, and each chosen label reduces the
forest rank by one. The graph may be disconnected. -/
theorem boruvka_rank_le (ends : E → Sym2 V) (w : E → W) (S : Finset E)
    (hw : Function.Injective w) :
    2 * (msf (boruvka ends w S).ends w (boruvka ends w S).remaining).card ≤
      (msf ends w S).card := by
  classical
  let b := boruvka ends w S
  let X := b.chosen.biUnion fun e => (ends e).toFinset
  have cover : support ends S ⊆ X := by
    intro x hx
    obtain ⟨v, _, ne, eq⟩ := boruvka_partner ends w S hx
    have path : Joins ends (b.chosen : Set E) x v := contract_eq_contract_iff.mp eq.symm
    obtain ⟨g, hg, hcut⟩ := path.exists_mem_edgeCut (P := {x}) rfl ne
    obtain ⟨u, v, hab, hu, _⟩ := Graph.mem_edgeCut_iff.mp hcut
    change u = x at hu
    subst u
    exact mem_biUnion.mpr ⟨g, hg, Sym2.mem_toFinset.mpr
      (by change ends g = s(x, v) at hab; simp [hab])⟩
  have size : X.card ≤ b.chosen.card * 2 := by
    apply Finset.card_biUnion_le_card_mul
    intro e _
    rw [Sym2.card_toFinset]
    split <;> omega
  have rank : (msf ends w S).card ≤ (support ends S).card - 1 :=
    (isAcyclic_msf w hw).card_le fun e he x hx =>
      mem_support.mpr ⟨e, msf_subset w he, fun loop => notMem_msf_of_isDiag w loop he, hx⟩
  have disj : Disjoint b.chosen (msf b.ends w b.remaining) :=
    disjoint_left.mpr fun _ h hm => (mem_sdiff.mp (mem_nonloops.mp (msf_subset w hm)).1).2 h
  have total : b.chosen.card + (msf b.ends w b.remaining).card = (msf ends w S).card := by
    rw [← card_union_of_disjoint disj, boruvka_msf _ _ _ hw]
  have hx := card_le_card cover
  change 2 * (msf b.ends w b.remaining).card ≤ _
  omega

omit [DecidableEq E] in
private theorem empty_msf {ends : E → Sym2 V} {w : E → W} {S : Finset E}
    (h : ¬ (nonloops ends S).Nonempty) : msf ends w S = ∅ := by
  rw [← msf_nonloops, not_nonempty_iff_eq_empty.1 h]
  exact subset_empty.1 (msf_subset w)

/-- Algorithms used on bounded local components and on the terminal contracted graph. -/
structure Solvers (V E W : Type*) [LinearOrder W] (w : E → W) where
  /-- MSF subroutine for bounded local components. -/
  small : (E → Sym2 V) → Finset E → Finset E
  /-- MSF subroutine for the terminal quotient, with the edge budget of the current round. -/
  dense : ℕ → (E → Sym2 V) → Finset E → Finset E
  /-- Correctness of the small-component subroutine at the input weights. -/
  small_eq : ∀ ends S, small ends S = msf ends w S
  /-- Correctness of the terminal quotient subroutine at the input weights. -/
  dense_eq : ∀ m ends S, dense m ends S = msf ends w S

variable {w : E → W}

/-- Compute candidate labels by invoking the two supplied subroutines at their respective
local or terminal topologies. No MSF of the original graph is required. -/
noncomputable def candidates (alg : Solvers V E W w) (budget : ℕ) (ends : E → Sym2 V)
    (S : Finset E) :
    List (PartitionPart V E W) → Finset E
  | [] => alg.dense budget ends S
  | p :: rest =>
    alg.small ends (internalEdges ends S p.vertices) ∪
      candidates alg budget (p.nextEnds ends S) (p.remaining ends w S) rest ∪ p.marks ends w S

private theorem candidates_eq (alg : Solvers V E W w) (budget : ℕ) (ends : E → Sym2 V)
    (S : Finset E) (parts : List (PartitionPart V E W)) :
    candidates alg budget ends S parts = (PrimPartition.collect w ends S parts).forests ∪
      (PrimPartition.collect w ends S parts).marked := by
  induction parts generalizing ends S with
  | nil => simp [candidates, PrimPartition.collect, alg.dense_eq]
  | cons p rest ih =>
    simp only [candidates, alg.small_eq, ih, PrimPartition.collect]
    ac_rfl

variable [DecidableEq V]

/-- The bounded Prim components actually processed by a recursive round. -/
@[expose] noncomputable def roundParts (grower : PrimPartition.Grower V E W w)
    (ends : E → Sym2 V) (S : Finset E) : List (PartitionPart V E W) :=
  let A := nonloops ends S
  let X := support ends A
  PrimPartition.partition grower X.card.log2.log2.log2 ends A id ∅ X.toList

/-- The original labels marked by boundary corruption during one full round. -/
noncomputable def roundMarks (grower : PrimPartition.Grower V E W w) (ends : E → Sym2 V)
    (S : Finset E) : Finset E :=
  (PrimPartition.collect w ends (nonloops ends S) (roundParts grower ends S)).marked

/-- Transfer a per-search soft-heap guarantee to the actual marked set used by a round.
The denominator multiplies the number of marks and each original label pays at most twice. -/
theorem round_mark_budget (grower : PrimPartition.Grower V E W w) (denominator : ℕ)
    (localBound : ∀ (ends : E → Sym2 V) (S : Finset E) (extra : ℕ) (dead : Finset V) (seed : V),
      seed ∉ dead → let q := grower.run ends S extra dead seed
        denominator * (q.part.marks ends w S).card ≤
          (PrimPartition.touched ends S q.vertices dead).card)
    (ends : E → Sym2 V) (S : Finset E) :
    denominator * (roundMarks grower ends S).card ≤ 2 * (nonloops ends S).card := by
  unfold roundMarks roundParts
  exact PrimPartition.marks_le_twice_edges _ _ _ (fun h s d v => localBound h s _ d v) _ _ _

private noncomputable def sparseGraph (grower : PrimPartition.Grower V E W w)
    (alg : Solvers V E W w) (ends : E → Sym2 V) (S : Finset E) : Finset E :=
  candidates alg (nonloops ends S).card ends (nonloops ends S) (roundParts grower ends S)

private theorem sparse_subset (grower : PrimPartition.Grower V E W w) (alg : Solvers V E W w)
    (ends : E → Sym2 V) (S : Finset E) : sparseGraph grower alg ends S ⊆ nonloops ends S := by
  rw [sparseGraph, candidates_eq]
  exact union_subset PrimPartition.forests_subset PrimPartition.marked_subset

private theorem sparse_msf (grower : PrimPartition.Grower V E W w) (alg : Solvers V E W w)
    (hw : Function.Injective w) (ends : E → Sym2 V) (S : Finset E) :
    msf ends w (sparseGraph grower alg ends S) = msf ends w S := by
  rw [sparseGraph, candidates_eq, roundParts, (PrimPartition.valid_partition ..).msf_eq hw,
    msf_nonloops]

/-- One recursion round. Both Borůvka passes run on the sparsified graph, first on its
original endpoints and then on the quotient produced by the first pass. -/
noncomputable def round (grower : PrimPartition.Grower V E W w) (alg : Solvers V E W w)
    (ends : E → Sym2 V) (S : Finset E) : Pass V E :=
  let b₁ := boruvka ends w (sparseGraph grower alg ends S)
  let b₂ := boruvka b₁.ends w b₁.remaining
  ⟨b₁.chosen ∪ b₂.chosen, b₂.ends, b₂.remaining⟩

theorem round_msf (grower : PrimPartition.Grower V E W w) (alg : Solvers V E W w)
    (hw : Function.Injective w) (ends : E → Sym2 V) (S : Finset E) :
    (round grower alg ends S).chosen ∪
      msf (round grower alg ends S).ends w (round grower alg ends S).remaining = msf ends w S := by
  dsimp only [round]
  rw [union_assoc, boruvka_msf _ _ _ hw, boruvka_msf _ _ _ hw, sparse_msf _ _ hw]

/-- Two Borůvka passes in a recursive round leave at most a quarter of the original
non-isolated vertices, with no connectedness hypothesis. -/
theorem round_support_le (grower : PrimPartition.Grower V E W w) (alg : Solvers V E W w)
    (ends : E → Sym2 V) (S : Finset E) :
    4 * (support (round grower alg ends S).ends (round grower alg ends S).remaining).card ≤
      (support ends S).card := by
  let C := sparseGraph grower alg ends S
  let b := boruvka ends w C
  have sub : support ends C ⊆ support ends S := by
    intro x hx
    obtain ⟨e, he, hd, hxe⟩ := mem_support.1 hx
    exact mem_support.2 ⟨e, (mem_nonloops.1 (sparse_subset grower alg ends S he)).1, hd, hxe⟩
  have h₁ := boruvka_support_le ends w C
  have h₂ := boruvka_support_le b.ends w b.remaining
  have h₃ := card_le_card sub
  change 2 * (support b.ends b.remaining).card ≤ (support ends C).card at h₁
  change 4 * (support (boruvka b.ends w b.remaining).ends
    (boruvka b.ends w b.remaining).remaining).card ≤ _
  omega

omit [DecidableEq V] in
private theorem boruvka_excess (ends : E → Sym2 V) (w : E → W) (S : Finset E)
    (hw : Function.Injective w) (k : ℕ) (h : S.card ≤ (msf ends w S).card + k) :
    (boruvka ends w S).remaining.card ≤
      (msf (boruvka ends w S).ends w (boruvka ends w S).remaining).card + k := by
  let b := boruvka ends w S
  have sub : b.chosen ⊆ S := (boruvkaEdges_subset_msf ends w S).trans (msf_subset w)
  have residual : b.remaining ⊆ S \ b.chosen := fun _ he => (mem_nonloops.1 he).1
  have disj : Disjoint b.chosen (msf b.ends w b.remaining) := disjoint_left.2 fun _ he hm =>
    (mem_sdiff.1 (residual (msf_subset w hm))).2 he
  have rank : b.chosen.card + (msf b.ends w b.remaining).card = (msf ends w S).card := by
    rw [← card_union_of_disjoint disj, boruvka_msf _ _ _ hw]
  have remove := card_le_card residual
  have total := card_sdiff_add_card_eq_card sub
  change b.remaining.card ≤ (msf b.ends w b.remaining).card + k
  omega

/-- The final edge count is at most one forest of the surviving quotient plus the
number of corrupted boundary labels. A Borůvka pass contracts one independent label for
each unit of lost forest rank. -/
theorem round_card_le_rank (grower : PrimPartition.Grower V E W w) (alg : Solvers V E W w)
    (hw : Function.Injective w) (ends : E → Sym2 V) (S : Finset E) :
    (round grower alg ends S).remaining.card ≤
      (msf (round grower alg ends S).ends w (round grower alg ends S).remaining).card +
        (roundMarks grower ends S).card := by
  let A := nonloops ends S
  let R := PrimPartition.collect w ends A (roundParts grower ends S)
  let G := sparseGraph grower alg ends S
  let b := boruvka ends w G
  let c := boruvka b.ends w b.remaining
  have splitG : G = R.forests ∪ R.marked := candidates_eq ..
  have hF : R.forests ⊆ G := by rw [splitG]; exact subset_union_left
  have rankF := (PrimPartition.isAcyclic_forests (ends := ends) (S := A)
    (ps := roundParts grower ends S) hw).card_le_spanningForest hF (isSpanningForest_msf w hw)
  have countG : G.card ≤ (msf ends w G).card + R.marked.card := by
    calc
      _ = (R.forests ∪ R.marked).card := congrArg Finset.card splitG
      _ ≤ R.forests.card + R.marked.card := card_union_le _ _
      _ ≤ _ := Nat.add_le_add_right rankF _
  have count := boruvka_excess b.ends w b.remaining hw _ (boruvka_excess ends w G hw _ countG)
  exact count

/-- Vertex-count form of the residual edge bound. -/
theorem round_card_le (grower : PrimPartition.Grower V E W w) (alg : Solvers V E W w)
    (hw : Function.Injective w) (ends : E → Sym2 V) (S : Finset E) :
    (round grower alg ends S).remaining.card ≤
      (support (round grower alg ends S).ends (round grower alg ends S).remaining).card - 1 +
        (roundMarks grower ends S).card := by
  let r := round grower alg ends S
  have rank : (msf r.ends w r.remaining).card ≤ (support r.ends r.remaining).card - 1 :=
    (isAcyclic_msf w hw).card_le fun e he x hx =>
      mem_support.mpr ⟨e, msf_subset w he, fun loop => notMem_msf_of_isDiag w loop he, hx⟩
  exact (round_card_le_rank grower alg hw ends S).trans (Nat.add_le_add_right rank _)

/-- With at most one marked label per four active input labels, a round halves the edge
count on arbitrary input, including disconnected multigraphs. -/
theorem round_half_of_mark_bound (grower : PrimPartition.Grower V E W w) (alg : Solvers V E W w)
    (hw : Function.Injective w) (ends : E → Sym2 V) (S : Finset E)
    (corrupt : 4 * (roundMarks grower ends S).card ≤ (nonloops ends S).card) :
    2 * (round grower alg ends S).remaining.card ≤ (nonloops ends S).card := by
  let G := sparseGraph grower alg ends S
  let b := boruvka ends w G
  let c := boruvka b.ends w b.remaining
  have rankG : (msf ends w G).card ≤ (nonloops ends S).card :=
    card_le_card ((msf_subset w).trans (sparse_subset grower alg ends S))
  have first : 2 * (msf b.ends w b.remaining).card ≤ (msf ends w G).card :=
    boruvka_rank_le ends w G hw
  have second : 2 * (msf c.ends w c.remaining).card ≤ (msf b.ends w b.remaining).card :=
    boruvka_rank_le b.ends w b.remaining hw
  have edges := round_card_le_rank grower alg hw ends S
  change c.remaining.card ≤ (msf c.ends w c.remaining).card + _ at edges
  change 2 * c.remaining.card ≤ _
  omega

/-- On a graph with an active non-loop label, a complete round strictly reduces the number
of active non-loop labels. This justifies recursion, including on disconnected input. -/
theorem round_card_lt (grower : PrimPartition.Grower V E W w) (alg : Solvers V E W w)
    (hw : Function.Injective w) (ends : E → Sym2 V) (S : Finset E)
    (h : (nonloops ends S).Nonempty) :
    (nonloops (round grower alg ends S).ends (round grower alg ends S).remaining).card <
      (nonloops ends S).card := by
  let C := sparseGraph grower alg ends S
  let b := boruvka ends w C
  obtain ⟨e, he⟩ := boruvkaEdges_nonempty (w := w) h
  have hm := boruvkaEdges_subset_msf ends w S he
  have hmC : e ∈ msf ends w C := by rwa [sparse_msf grower alg hw]
  have hC := msf_subset w hmC
  have act : (nonloops ends C).Nonempty :=
    ⟨e, mem_nonloops.2 ⟨hC, fun hd => notMem_msf_of_isDiag w hd hmC⟩⟩
  have h₁ : b.remaining.card < C.card := remaining_card_lt (boruvkaEdges_nonempty act)
  have h₂ := card_le_card (remaining_subset b.ends w b.remaining)
  have h₃ := card_le_card (sparse_subset grower alg ends S)
  have h₄ : (nonloops (round grower alg ends S).ends (round grower alg ends S).remaining).card ≤
      (boruvka b.ends w b.remaining).remaining.card :=
    card_le_card (fun _ he => (mem_nonloops.1 he).1)
  exact h₄.trans_lt ((h₂.trans_lt h₁).trans_le h₃)

/-- Run the recursive §5 reduction until no non-loop label remains. The decision-tree and
dense-case calls occur on the graphs produced by the live/dead partition at each level. -/
@[expose] noncomputable def reduceMSF (grower : PrimPartition.Grower V E W w)
    (alg : Solvers V E W w) (hw : Function.Injective w) (ends : E → Sym2 V)
    (S : Finset E) : Finset E :=
  if _h : (nonloops ends S).Nonempty then
    let r := round grower alg ends S
    r.chosen ∪ reduceMSF grower alg hw r.ends r.remaining
  else ∅
termination_by (nonloops ends S).card
decreasing_by exact round_card_lt grower alg hw ends S (by assumption)

/-- The recursive result consists of precisely the original minimum spanning forest labels. -/
theorem reduceMSF_eq (grower : PrimPartition.Grower V E W w) (alg : Solvers V E W w)
    (hw : Function.Injective w) (ends : E → Sym2 V) (S : Finset E) :
    reduceMSF grower alg hw ends S = msf ends w S := by
  rw [reduceMSF]
  split
  next h =>
    dsimp only
    rw [reduceMSF_eq grower alg hw]
    exact round_msf grower alg hw ends S
  next h => exact (empty_msf h).symm
termination_by (nonloops ends S).card
decreasing_by exact round_card_lt grower alg hw ends S (by assumption)

end Cslib.Multigraph.PettieRamachandran
