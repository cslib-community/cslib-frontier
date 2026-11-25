/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Weight-capped compressions of multigraphs

`CslibFrontier/Computability/Circuit/Frontier/Layouts/Compression.lean` compresses a multigraph of
maximum degree `d` into connected blocks with at most `d` edges leaving each block, without
bounding the size or weight of a block. When a partition of the quotient must also balance vertex
weights—such as input reads in a 3-way tensor cut, or vertex and boundary counts in recursive
carving bisections—blocks cannot be allowed to absorb a macroscopic fraction of the total weight.

`CappedCompression G w d M` adds a weight cap `M` on `(B.map w).sum` for a vertex weight
`w : V → ℕ`. Merging terminates at a *weight-saturated* compression (`Saturated`): any two distinct
blocks joined by an edge either have more than `d` edges leaving their union, or have combined
weight strictly above `M`.

For budget `d = 3`, call a block *heavy* when its weight exceeds `M / 2`. At most
`2 (∑ v, w v) / (M + 1)` blocks are heavy, and every non-heavy block of quotient degree `1` or `2`
must send every incident quotient edge to a heavy block (otherwise it could merge with its
neighbour, since `2 + 3 - 2 = 3`). Because each heavy block has quotient degree at most `3`, at
most `4` times as many blocks have quotient degree `1` or `2` as there are heavy blocks
(`Saturated.card_deg_one_two_mul_le`). Together with the cycle-rank and minimum-degree-two Euler
counts on connected blocks, this bounds the number of degree-three quotient blocks up to
`O((∑ w) / M)`.

## Main definitions

* `Cslib.Circuits.Frontier.Multigraph.CappedCompression`: a partition into nonempty connected
  blocks of cut at most `d` and weight at most `M`.
* `Cslib.Circuits.Frontier.Multigraph.CappedCompression.Saturated`: no weight-valid merge applies.
* `Cslib.Circuits.Frontier.Multigraph.CappedCompression.quotient`: the loopless quotient multigraph
  on the blocks.

## Main results

* `Cslib.Circuits.Frontier.Multigraph.CappedCompression.exists_saturated`: merging terminates when
  every single vertex has degree at most `d` and weight at most `M`.
* `Cslib.Circuits.Frontier.Multigraph.CappedCompression.Saturated.card_deg_one_two_mul_le`,
  `Cslib.Circuits.Frontier.Multigraph.CappedCompression.Saturated.mul_card_deg_one_two_le`: the
  number of degree-`1` and degree-`2` blocks is `O((∑ v, w v) / M)`.
* `Cslib.Circuits.Frontier.Multigraph.CappedCompression.card_deg_three_le_of_connected`: in a
  connected subcubic multigraph, `#Q₃ ≤ 2 β₁ + #Q₁`.
* `Cslib.Circuits.Frontier.Multigraph.CappedCompression.card_deg_three_add_le_of_two_le_deg`: in a
  loopless multigraph of minimum degree at least `2` with `2 |E| + b = 3 |V|`,
  `#Q₃ + b ≤ |V| + #Q₁`.
-/

public section

namespace Cslib.Circuits.Frontier.Multigraph

open Set

variable {V E : Type*}

/-- A *weight-capped compression* of `G` with vertex weights `w`, cut budget `d`, and block-weight
cap `M`. Each block lists its vertices without duplicates, induces a connected subgraph, has at
most `d` edges leaving it, and has total weight at most `M`. -/
structure CappedCompression (G : Multigraph V E) (w : V → ℕ) (d M : ℕ) where
  /-- The blocks of vertices. -/
  blocks : Finset (List V)
  /-- Every vertex belongs to a block. -/
  exists_mem : ∀ v, ∃ B ∈ blocks, v ∈ B
  /-- Blocks sharing a vertex are equal. -/
  eq_of_mem : ∀ B ∈ blocks, ∀ B' ∈ blocks, ∀ v ∈ B, v ∈ B' → B = B'
  /-- Each block lists its vertices without duplicates. -/
  nodup : ∀ B ∈ blocks, B.Nodup
  /-- Each block is nonempty. -/
  ne_nil : ∀ B ∈ blocks, B ≠ []
  /-- Each block induces a connected subgraph of `G`. -/
  connected : ∀ B ∈ blocks, (G.induce {v | v ∈ B}).toSimpleGraph.Connected
  /-- At most `d` edges leave each block. -/
  ncard_edgeCut_le : ∀ B ∈ blocks, (G.edgeCut {v | v ∈ B}).ncard ≤ d
  /-- Each block has total `w`-weight at most `M`. -/
  weight_le : ∀ B ∈ blocks, (B.map w).sum ≤ M

namespace CappedCompression

variable {G : Multigraph V E} {w : V → ℕ} {d M : ℕ}

/-- Singletons form a valid weight-capped compression when `G.MaxDegreeLE d` and `w v ≤ M`. -/
private def singletons [Fintype V] [DecidableEq V] [Finite E] (hG : G.MaxDegreeLE d)
    (hw : ∀ v, w v ≤ M) : CappedCompression G w d M where
  blocks := Finset.univ.image fun v => [v]
  exists_mem v := ⟨[v], Finset.mem_image_of_mem _ (Finset.mem_univ v), List.mem_singleton_self v⟩
  eq_of_mem := by simp
  nodup := by simp
  ne_nil := by simp
  connected := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
      forall_apply_eq_imp_iff]
    intro v
    exact { preconnected := fun ⟨_, ha⟩ ⟨_, hb⟩ => by
              simp only [mem_ofPred_eq, List.mem_singleton] at ha hb
              subst ha hb
              exact .refl _
            nonempty := ⟨⟨v, List.mem_singleton_self v⟩⟩ }
  ncard_edgeCut_le := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
      forall_apply_eq_imp_iff, List.mem_singleton]
    intro v
    refine (ncard_le_ncard fun e he => ?_).trans (hG v)
    simp only [mem_edgeCut, mem_ofPred_eq] at he
    rw [mem_incidenceSet]
    tauto
  weight_le := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
      forall_apply_eq_imp_iff, List.map_singleton, List.sum_singleton]
    exact hw

/-- If two connected vertex sets are joined by an edge, their union induces a connected
subgraph. -/
private theorem connected_union_of_edgeCut_inter {S T : Set V}
    (hS : (G.induce S).toSimpleGraph.Connected) (hT : (G.induce T).toSimpleGraph.Connected)
    (hjoin : (G.edgeCut S ∩ G.edgeCut T).Nonempty) :
    (G.induce (S ∪ T)).toSimpleGraph.Connected := by
  obtain ⟨e, heS, heT⟩ := hjoin
  obtain ⟨u₀, hu₀⟩ := hS.nonempty
  let inL : (G.induce S).toSimpleGraph →g (G.induce (S ∪ T)).toSimpleGraph :=
    { toFun := fun x => ⟨x.1, Or.inl x.2⟩
      map_rel' := fun hab => by
        rw [toSimpleGraph_induce] at hab ⊢
        exact hab }
  let inR : (G.induce T).toSimpleGraph →g (G.induce (S ∪ T)).toSimpleGraph :=
    { toFun := fun x => ⟨x.1, Or.inr x.2⟩
      map_rel' := fun hab => by
        rw [toSimpleGraph_induce] at hab ⊢
        exact hab }
  have bridge : ∃ (a : S) (b : T),
      (G.induce (S ∪ T)).toSimpleGraph.Reachable (inL a) (inR b) := by
    by_cases hsS : G.src e ∈ S
    · have htS : G.tgt e ∉ S := fun ht => heS (iff_of_true hsS ht)
      by_cases hsT : G.src e ∈ T
      · exact ⟨⟨G.src e, hsS⟩, ⟨G.src e, hsT⟩, .refl _⟩
      · have htT : G.tgt e ∈ T := by
          by_contra htT
          exact heT (iff_of_false hsT htT)
        let e' : {f // G.src f ∈ S ∪ T ∧ G.tgt f ∈ S ∪ T} := ⟨e, Or.inl hsS, Or.inr htT⟩
        exact ⟨⟨G.src e, hsS⟩, ⟨G.tgt e, htT⟩, (G.induce (S ∪ T)).reachable_src_tgt e'⟩
    · have htS : G.tgt e ∈ S := by
        by_contra htS
        exact heS (iff_of_false hsS htS)
      by_cases htT : G.tgt e ∈ T
      · exact ⟨⟨G.tgt e, htS⟩, ⟨G.tgt e, htT⟩, .refl _⟩
      · have hsT : G.src e ∈ T := by
          by_contra hsT
          exact heT (iff_of_false hsT htT)
        let e' : {f // G.src f ∈ S ∪ T ∧ G.tgt f ∈ S ∪ T} := ⟨e, Or.inr hsT, Or.inl htS⟩
        exact ⟨⟨G.tgt e, htS⟩, ⟨G.src e, hsT⟩, ((G.induce (S ∪ T)).reachable_src_tgt e').symm⟩
  obtain ⟨a₀, b₀, hab₀⟩ := bridge
  have reach_a₀ : ∀ z : {v // v ∈ S ∪ T},
      (G.induce (S ∪ T)).toSimpleGraph.Reachable (inL a₀) z := by
    rintro ⟨v, hvS | hvT⟩
    · exact (hS.preconnected a₀ ⟨v, hvS⟩).map inL
    · exact hab₀.trans ((hT.preconnected b₀ ⟨v, hvT⟩).map inR)
  exact { preconnected := fun x y => (reach_a₀ x).symm.trans (reach_a₀ y)
          nonempty := ⟨⟨u₀, Or.inl hu₀⟩⟩ }

variable (c : CappedCompression G w d M)

/-- Merging two distinct blocks joined by an edge whose union satisfies both the cut budget and the
weight cap strictly decreases the number of blocks. -/
private theorem exists_merge {B B' : List V} (hB : B ∈ c.blocks) (hB' : B' ∈ c.blocks)
    (hne : B ≠ B') (hjoin : (G.edgeCut {v | v ∈ B} ∩ G.edgeCut {v | v ∈ B'}).Nonempty)
    (hcut : (G.edgeCut ({v | v ∈ B} ∪ {v | v ∈ B'})).ncard ≤ d)
    (hwt : (B.map w).sum + (B'.map w).sum ≤ M) :
    ∃ c' : CappedCompression G w d M, c'.blocks.card < c.blocks.card := by
  classical
  have hd (v : V) (hv : v ∈ B) : v ∉ B' := fun hv' => hne (c.eq_of_mem B hB B' hB' v hv hv')
  have hrest (C : List V) (hC : C ∈ c.blocks) (hCB : C ≠ B) (hCB' : C ≠ B') (v : V)
      (hv : v ∈ C) : v ∉ B ∧ v ∉ B' :=
    ⟨fun h => hCB (c.eq_of_mem C hC B hB v hv h),
      fun h => hCB' (c.eq_of_mem C hC B' hB' v hv h)⟩
  have hmem {C : List V} : C ∈ insert (B ++ B') ((c.blocks.erase B).erase B') ↔
      C = B ++ B' ∨ (C ≠ B' ∧ C ≠ B ∧ C ∈ c.blocks) := by
    simp only [Finset.mem_insert, Finset.mem_erase]
  have hcard : (insert (B ++ B') ((c.blocks.erase B).erase B')).card + 1 = c.blocks.card := by
    have hnot : B ++ B' ∉ (c.blocks.erase B).erase B' := by
      intro h
      simp only [Finset.mem_erase] at h
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil B (c.ne_nil B hB)
      exact h.2.1 (c.eq_of_mem _ h.2.2 B hB v (List.mem_append_left _ hv) hv)
    rw [Finset.card_insert_of_notMem hnot, Finset.card_erase_of_mem
      (Finset.mem_erase.2 ⟨hne.symm, hB'⟩), Finset.card_erase_of_mem hB]
    have := Finset.one_lt_card.2 ⟨B, hB, B', hB', hne⟩
    omega
  have happ (L L' : List V) : {v | v ∈ L ++ L'} = {v | v ∈ L} ∪ {v | v ∈ L'} :=
    Set.ext fun _ => List.mem_append
  have hall {P : List V → Prop} (h₁ : P (B ++ B')) (h₂ : ∀ C ∈ c.blocks, P C) :
      ∀ C ∈ insert (B ++ B') ((c.blocks.erase B).erase B'), P C := by
    simp only [hmem]
    rintro C (rfl | ⟨-, -, hC⟩)
    exacts [h₁, h₂ C hC]
  refine ⟨{ blocks := insert (B ++ B') ((c.blocks.erase B).erase B')
            exists_mem := ?_, eq_of_mem := ?_
            nodup := hall (List.nodup_append.2 ⟨c.nodup B hB, c.nodup B' hB',
              fun a ha b hb hab => hd a ha (hab ▸ hb)⟩) c.nodup
            ne_nil := hall (List.append_ne_nil_of_left_ne_nil (c.ne_nil B hB) _) c.ne_nil
            connected := hall (by
              rw [happ]
              exact connected_union_of_edgeCut_inter (c.connected B hB) (c.connected B' hB') hjoin)
              c.connected
            ncard_edgeCut_le := hall (by rwa [happ]) c.ncard_edgeCut_le
            weight_le := hall (by simpa [List.map_append, List.sum_append] using hwt) c.weight_le },
    Nat.lt_of_succ_le hcard.le⟩
  · intro v
    obtain ⟨C, hC, hv⟩ := c.exists_mem v
    by_cases h : C = B ∨ C = B'
    · refine ⟨B ++ B', Finset.mem_insert_self _ _, ?_⟩
      rcases h with rfl | rfl <;> simp [hv]
    · rw [not_or] at h
      exact ⟨C, hmem.2 (Or.inr ⟨h.2, h.1, hC⟩), hv⟩
  · simp only [hmem]
    rintro C (rfl | ⟨hC₁, hC₂, hC⟩) C' (rfl | ⟨hC₁', hC₂', hC'⟩) v hv hv'
    · rfl
    · rw [List.mem_append] at hv
      have := hrest C' hC' hC₂' hC₁' v hv'
      tauto
    · rw [List.mem_append] at hv'
      have := hrest C hC hC₂ hC₁ v hv
      tauto
    · exact c.eq_of_mem C hC C' hC' v hv hv'

/-- A weight-capped compression is *saturated* when any two distinct blocks joined by an edge
either exceed the cut budget `d` or exceed the weight cap `M` upon merging. -/
def Saturated : Prop :=
  ∀ B ∈ c.blocks, ∀ B' ∈ c.blocks, B ≠ B' →
    (G.edgeCut {v | v ∈ B} ∩ G.edgeCut {v | v ∈ B'}).Nonempty →
      d < (G.edgeCut ({v | v ∈ B} ∪ {v | v ∈ B'})).ncard ∨
        M < (B.map w).sum + (B'.map w).sum

/-- **Merging terminates.** Every finite multigraph of maximum degree `d` with vertex weights
bounded by `M` admits a saturated weight-capped compression. -/
theorem exists_saturated [Finite V] [Finite E] (hG : G.MaxDegreeLE d) (hw : ∀ v, w v ≤ M) :
    ∃ c : CappedCompression G w d M, c.Saturated := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨c, -, hmin⟩ := (measure fun c : CappedCompression G w d M => c.blocks.card).wf.has_min
    univ ⟨singletons hG hw, trivial⟩
  refine ⟨c, fun B hB B' hB' hne hjoin => ?_⟩
  by_contra! h
  obtain ⟨c', hc'⟩ := c.exists_merge hB hB' hne hjoin h.1 h.2
  exact hmin c' trivial hc'

/-! ### The quotient and block weights -/

/-- The block containing a vertex `v`. -/
noncomputable def blockOf (v : V) : c.blocks :=
  ⟨(c.exists_mem v).choose, (c.exists_mem v).choose_spec.1⟩

/-- Every vertex belongs to its assigned block. -/
theorem mem_blockOf (v : V) : v ∈ (c.blockOf v).1 :=
  (c.exists_mem v).choose_spec.2

/-- A vertex belongs to a block `B` if and only if `c.blockOf v = B`. -/
theorem mem_iff_blockOf_eq {v : V} {B : c.blocks} : v ∈ B.1 ↔ c.blockOf v = B :=
  ⟨fun h => Subtype.ext (c.eq_of_mem _ (c.blockOf v).2 _ B.2 v (c.mem_blockOf v) h),
    fun h => h ▸ c.mem_blockOf v⟩

private theorem preimage_blockOf_singleton (B : c.blocks) : c.blockOf ⁻¹' {B} = {v | v ∈ B.1} := by
  ext v
  simp [c.mem_iff_blockOf_eq]

/-- There are at most as many blocks as vertices. -/
theorem card_blocks_le [Finite V] : c.blocks.card ≤ Nat.card V := by
  calc c.blocks.card = Nat.card c.blocks := by simp
    _ ≤ Nat.card V := Nat.card_le_card_of_surjective c.blockOf fun B =>
      let ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ (c.ne_nil B.1 B.2)
      ⟨v, c.mem_iff_blockOf_eq.mp hv⟩

/-- Distinct blocks are disjoint. -/
theorem disjoint_of_ne {B B' : c.blocks} (h : B ≠ B') :
    Disjoint {v | v ∈ B.1} {v | v ∈ B'.1} :=
  disjoint_left.mpr fun _ hv hv' =>
    h ((c.mem_iff_blockOf_eq.mp hv).symm.trans (c.mem_iff_blockOf_eq.mp hv'))

/-- The total `w`-weight of a block. -/
@[expose] def blockWeight (B : c.blocks) : ℕ :=
  (B.1.map w).sum

/-- Every block has `blockWeight` at most `M`. -/
theorem blockWeight_le (B : c.blocks) : c.blockWeight B ≤ M :=
  c.weight_le B.1 B.2

/-- The cardinality of `{v | v ∈ B.1}` equals `B.1.length`. -/
theorem ncard_block_eq_length (B : c.blocks) : {v | v ∈ B.1}.ncard = B.1.length := by
  classical
  have : {v | v ∈ B.1} = (B.1.toFinset : Set V) := by ext; simp
  rw [this, ncard_coe_finset, List.toFinset_card_of_nodup (c.nodup B.1 B.2)]

/-- Summing `blockWeight` over a set of blocks equals summing `w` over the vertices in their
preimage. -/
theorem sum_blockWeight_eq [Fintype V] [DecidableEq V] (S : Finset c.blocks) :
    ∑ B ∈ S, c.blockWeight B = ∑ v ∈ Finset.univ.filter (fun v => c.blockOf v ∈ S), w v := by
  classical
  have hB (B : c.blocks) : c.blockWeight B =
      ∑ v ∈ Finset.univ.filter (fun v => c.blockOf v = B), w v := by
    have hfin : B.1.toFinset = Finset.univ.filter (fun v => c.blockOf v = B) := by
      ext v
      simp [c.mem_iff_blockOf_eq]
    rw [blockWeight, ← List.sum_toFinset _ (c.nodup B.1 B.2), hfin]
  simp_rw [hB]
  rw [← Finset.sum_biUnion]
  · congr 1
    ext v
    simp
  · intro B _ B' _ hne
    refine Finset.disjoint_left.mpr fun v hv hv' => hne ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv hv'
    exact hv.symm.trans hv'

/-- The block weights sum to the total vertex weight. -/
theorem sum_blockWeight_univ [Fintype V] :
    ∑ B : c.blocks, c.blockWeight B = ∑ v : V, w v := by
  classical
  simpa using c.sum_blockWeight_eq Finset.univ

/-- The *external* edges: those between distinct blocks. -/
@[expose] def external : Set E :=
  {e | c.blockOf (G.src e) ≠ c.blockOf (G.tgt e)}

/-- The *quotient* multigraph on `c.blocks`, whose edges are `c.external`. -/
@[expose] noncomputable def quotient : Multigraph c.blocks c.external where
  src e := c.blockOf (G.src e.1)
  tgt e := c.blockOf (G.tgt e.1)

@[simp] theorem quotient_src (e : c.external) : c.quotient.src e = c.blockOf (G.src e.1) :=
  rfl

@[simp] theorem quotient_tgt (e : c.external) : c.quotient.tgt e = c.blockOf (G.tgt e.1) :=
  rfl

/-- The quotient multigraph is loopless. -/
theorem quotient_loopless : c.quotient.Loopless :=
  fun e => e.2

private theorem edgeCut_preimage (T : Set c.blocks) :
    G.edgeCut (c.blockOf ⁻¹' T) = Subtype.val '' c.quotient.edgeCut T := by
  ext e
  simp only [mem_edgeCut, mem_preimage, mem_image, Subtype.exists, exists_and_right,
    exists_eq_right, quotient_src, quotient_tgt]
  exact ⟨fun h => ⟨fun h' => h (by rw [h']), h⟩, fun ⟨_, h⟩ => h⟩

/-- Cuts of unions of whole blocks equal the corresponding cuts in the quotient. -/
theorem ncard_edgeCut_preimage (T : Set c.blocks) :
    (G.edgeCut (c.blockOf ⁻¹' T)).ncard = (c.quotient.edgeCut T).ncard := by
  rw [c.edgeCut_preimage, ncard_image_of_injective _ Subtype.val_injective]

/-- Pairs of disjoint block-unions have the same cross-edges in `G` as in `c.quotient`. -/
theorem ncard_crossEdges_preimage [Finite E] {S T : Set c.blocks} (hST : Disjoint S T) :
    (G.edgeCut (c.blockOf ⁻¹' S) ∩ G.edgeCut (c.blockOf ⁻¹' T)).ncard =
      (c.quotient.edgeCut S ∩ c.quotient.edgeCut T).ncard := by
  have h1 := G.ncard_edgeCut_union_add (hST.preimage c.blockOf) (toFinite _) (toFinite _)
  have h2 := c.quotient.ncard_edgeCut_union_add hST (toFinite _) (toFinite _)
  rw [← preimage_union, c.ncard_edgeCut_preimage, c.ncard_edgeCut_preimage,
    c.ncard_edgeCut_preimage] at h1
  omega

/-- The degree of a block in the quotient is the number of edges leaving it in `G`. -/
theorem ncard_incidenceSet_quotient (B : c.blocks) :
    (c.quotient.incidenceSet B).ncard = (G.edgeCut {v | v ∈ B.1}).ncard := by
  rw [← edgeCut_singleton _ c.quotient_loopless, ← c.ncard_edgeCut_preimage,
    c.preimage_blockOf_singleton]

/-- Every block in the quotient has degree at most `d`. -/
theorem quotient_maxDegreeLE [Finite E] : c.quotient.MaxDegreeLE d := fun B =>
  (c.ncard_incidenceSet_quotient B).trans_le (c.ncard_edgeCut_le _ B.2)

/-- In a connected multigraph with at least two blocks, every block has positive degree in the
quotient. -/
theorem incidenceSet_quotient_nonempty [Finite E] (hG : G.toSimpleGraph.Connected)
    (two : 1 < Nat.card c.blocks) (B : c.blocks) :
    (c.quotient.incidenceSet B).Nonempty := by
  have := Finite.one_lt_card_iff_nontrivial.mp two
  obtain ⟨B', hB'⟩ := exists_ne B
  obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ (c.ne_nil _ B.2)
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ (c.ne_nil _ B'.2)
  have hne : (G.edgeCut {z | z ∈ B.1}).Nonempty := by
    refine Multigraph.edgeCut_nonempty hG (S := {z | z ∈ B.1}) (v := v) hu fun h => hB' ?_
    rw [mem_ofPred_eq, c.mem_iff_blockOf_eq] at h
    exact (c.mem_iff_blockOf_eq.mp hv).symm.trans h
  rw [← ncard_pos (toFinite _), c.ncard_incidenceSet_quotient]
  exact hne.ncard_pos

/-! ### Euler and degree counts for budget three -/

section DegreeThree

variable {c : CappedCompression G w 3 M}

/-- **Low-degree blocks are scarce.** In a saturated budget-`3` compression with weight cap `M`,
every block of quotient degree `1` or `2` is either heavy (`M / 2 < blockWeight B`) or sends an
external edge to a heavy block. Since each heavy block has quotient degree at most `3`,
`(M / 2 + 1) * #{B | deg_Q(B) ∈ {1, 2}} ≤ 4 * ∑ v, w v`. -/
theorem Saturated.card_deg_one_two_mul_le [Fintype V] [Finite E] (hc : c.Saturated) :
    (M / 2 + 1) * (Finset.univ.filter fun B : c.blocks =>
        1 ≤ (c.quotient.incidenceSet B).ncard ∧ (c.quotient.incidenceSet B).ncard ≤ 2).card ≤
      4 * ∑ v : V, w v := by
  classical
  have := Fintype.ofFinite E
  set H : Finset c.blocks := Finset.univ.filter fun B => M / 2 < c.blockWeight B
  set L : Finset c.blocks := Finset.univ.filter fun B =>
    1 ≤ (c.quotient.incidenceSet B).ncard ∧ (c.quotient.incidenceSet B).ncard ≤ 2
  have hLH : (L \ H).card ≤ 3 * H.card := by
    have hex (B : c.blocks) (hB : B ∈ L \ H) :
        ∃ e : c.external, e ∈ c.quotient.incidenceSet B ∧
          ∃ B' ∈ H, e ∈ c.quotient.incidenceSet B' := by
      simp only [L, H, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
        not_lt] at hB
      obtain ⟨⟨h1, h2⟩, hle⟩ := hB
      obtain ⟨e, he⟩ := nonempty_of_ncard_ne_zero (by omega : (c.quotient.incidenceSet B).ncard ≠ 0)
      set B' : c.blocks := if c.quotient.src e = B then c.quotient.tgt e else c.quotient.src e
      have hloop := c.quotient_loopless e
      obtain ⟨hne, heB'⟩ : B' ≠ B ∧ e ∈ c.quotient.incidenceSet B' := by
        dsimp only [B']
        split_ifs with hs
        exacts [⟨fun h => hloop (hs.trans h.symm), Or.inr rfl⟩, ⟨hs, Or.inl rfl⟩]
      refine ⟨e, he, B', ?_, heB'⟩
      simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
      have hmemCut (B₀ : c.blocks) (h : e ∈ c.quotient.incidenceSet B₀) :
          e.1 ∈ G.edgeCut {v | v ∈ B₀.1} := by
        simp only [mem_edgeCut, mem_ofPred_eq, c.mem_iff_blockOf_eq, ← c.quotient_src e,
          ← c.quotient_tgt e]
        rcases h with hs | ht
        · exact fun h => hloop (hs.trans (h.mp hs).symm)
        · exact fun h => hloop ((h.mpr ht).trans ht.symm)
      have hjoin : (G.edgeCut {v | v ∈ B.1} ∩ G.edgeCut {v | v ∈ B'.1}).Nonempty :=
        ⟨e.1, hmemCut B he, hmemCut B' heB'⟩
      rcases hc B.1 B.2 B'.1 B'.2 (fun h => hne (Subtype.ext h.symm)) hjoin with hcut | hwt
      · exfalso
        have hu := G.ncard_edgeCut_union_add (c.disjoint_of_ne hne.symm) (toFinite _) (toFinite _)
        have hdB : (G.edgeCut {v | v ∈ B.1}).ncard ≤ 2 :=
          (c.ncard_incidenceSet_quotient B).symm.trans_le h2
        have hdB' : (G.edgeCut {v | v ∈ B'.1}).ncard ≤ 3 := c.ncard_edgeCut_le B'.1 B'.2
        have hjpos := hjoin.ncard_pos
        omega
      · change M < c.blockWeight B + c.blockWeight B' at hwt
        omega
    choose f hfB hfH using hex
    let incH : Finset c.external :=
      H.biUnion fun B' => (c.quotient.incidenceSet B').toFinset
    have hmaps (B) (hB : B ∈ L \ H) : f B hB ∈ incH :=
      let ⟨B', hB'H, heB'⟩ := hfH B hB
      Finset.mem_biUnion.mpr ⟨B', hB'H, Set.mem_toFinset.mpr heB'⟩
    have hinj' (B₁) (h₁ : B₁ ∈ L \ H) (B₂) (h₂ : B₂ ∈ L \ H) (heq : f B₁ h₁ = f B₂ h₂) :
        B₁ = B₂ := by
      obtain ⟨B', hB'H, heB'⟩ := hfH B₁ h₁
      have he₁ := hfB B₁ h₁
      have he₂ := heq ▸ hfB B₂ h₂
      have hB'1 : B' ≠ B₁ := fun h => (Finset.mem_sdiff.mp h₁).2 (h ▸ hB'H)
      have hB'2 : B' ≠ B₂ := fun h => (Finset.mem_sdiff.mp h₂).2 (h ▸ hB'H)
      rcases heB' with hs' | ht'
      · exact (he₁.resolve_left fun h => hB'1 (hs'.symm.trans h)).symm.trans
          (he₂.resolve_left fun h => hB'2 (hs'.symm.trans h))
      · exact (he₁.resolve_right fun h => hB'1 (ht'.symm.trans h)).symm.trans
          (he₂.resolve_right fun h => hB'2 (ht'.symm.trans h))
    have hcard_le : (L \ H).card ≤ incH.card := by
      have hc := Fintype.card_le_of_injective (fun x : {B // B ∈ L \ H} =>
        (⟨f x.1 x.2, hmaps x.1 x.2⟩ : incH)) fun x y h =>
          Subtype.ext (hinj' x.1 x.2 y.1 y.2 (congrArg Subtype.val h))
      rwa [Fintype.card_coe, Fintype.card_coe] at hc
    refine hcard_le.trans ((Finset.card_biUnion_le_card_mul _ _ 3 fun B' _ => ?_).trans_eq
      (Nat.mul_comm _ _))
    rw [← Set.ncard_eq_toFinset_card']
    exact c.quotient_maxDegreeLE B'
  have hL_le : L.card ≤ 4 * H.card := by
    have := Finset.card_sdiff_add_card_inter L H
    have := Finset.card_le_card (Finset.inter_subset_right (s₁ := L) (s₂ := H))
    omega
  have hH_wt : (M / 2 + 1) * H.card ≤ ∑ v : V, w v := by
    rw [← c.sum_blockWeight_univ, mul_comm, ← smul_eq_mul]
    exact (H.card_nsmul_le_sum _ _ fun B hB => (Finset.mem_filter.mp hB).2).trans
      (Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _)
  have := Nat.mul_le_mul_left (M / 2 + 1) hL_le
  linarith

/-- **Low-degree blocks are scarce**, with the weight cap itself as the factor:
`M * #{B | deg_Q(B) ∈ {1, 2}} ≤ 8 * ∑ v, w v`. -/
theorem Saturated.mul_card_deg_one_two_le [Fintype V] [Finite E] (hc : c.Saturated) :
    M * (Finset.univ.filter fun B : c.blocks =>
        1 ≤ (c.quotient.incidenceSet B).ncard ∧ (c.quotient.incidenceSet B).ncard ≤ 2).card ≤
      8 * ∑ v : V, w v := by
  have := hc.card_deg_one_two_mul_le
  have := Nat.mul_le_mul_right (Finset.univ.filter fun B : c.blocks =>
    1 ≤ (c.quotient.incidenceSet B).ncard ∧ (c.quotient.incidenceSet B).ncard ≤ 2).card
    (show M ≤ 2 * (M / 2 + 1) by omega)
  linarith

/-- Sum of block sizes is `|V|`, and each connected block `B` absorbs at least `|B| - 1` internal
edges (and at least `|B|` internal edges if `G.edgeCut B = ∅` and all vertices in `B` have degree
at least `2`). -/
private theorem sum_internal_edges_ge [Finite V] [Finite E] (hloop : G.Loopless) :
    Nat.card V ≤ (Finset.univ.filter fun B : c.blocks =>
        0 < (c.quotient.incidenceSet B).ncard).card +
      (Finset.univ.filter fun B : c.blocks =>
        (c.quotient.incidenceSet B).ncard = 0 ∧
          ∃ v ∈ B.1, (G.incidenceSet v).ncard < 2).card +
      (Nat.card E - Nat.card c.external) := by
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  let intEdges (B : c.blocks) : Finset E :=
    Finset.univ.filter fun e => G.src e ∈ B.1 ∧ G.tgt e ∈ B.1
  have hdisj : (↑(Finset.univ : Finset c.blocks) : Set c.blocks).PairwiseDisjoint intEdges := by
    intro B₁ _ B₂ _ hne
    refine Finset.disjoint_left.mpr fun e he₁ he₂ => ?_
    simp only [intEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he₁ he₂
    exact hne ((c.mem_iff_blockOf_eq.mp he₁.1).symm.trans (c.mem_iff_blockOf_eq.mp he₂.1))
  have hunion : (Finset.univ.biUnion intEdges : Set E) = c.externalᶜ := by
    ext e
    simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and, intEdges,
      Finset.mem_filter, external, mem_compl_iff, mem_ofPred_eq, not_not]
    exact ⟨fun ⟨B, hs, ht⟩ => (c.mem_iff_blockOf_eq.mp hs).trans
      (c.mem_iff_blockOf_eq.mp ht).symm,
      fun h => ⟨c.blockOf (G.src e), c.mem_blockOf _, h ▸ c.mem_blockOf _⟩⟩
  have hint_card : ∑ B : c.blocks, (intEdges B).card = Nat.card E - Nat.card c.external := by
    rw [← Finset.card_biUnion hdisj, ← ncard_coe_finset, hunion]
    have h1 := ncard_add_ncard_compl c.external
    rw [Nat.card_coe_set_eq]
    omega
  have hv_sum : ∑ B : c.blocks, {v | v ∈ B.1}.ncard = Nat.card V := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ,
      Finset.card_eq_sum_card_fiberwise (f := c.blockOf) (t := Finset.univ) fun _ _ =>
        Finset.mem_coe.2 (Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [← c.preimage_blockOf_singleton, ← ncard_coe_finset]
    congr 1
    ext
    simp
  have hB_le (B : c.blocks) :
      {v | v ∈ B.1}.ncard ≤ (intEdges B).card +
        (if 0 < (c.quotient.incidenceSet B).ncard then 1 else 0) +
        (if (c.quotient.incidenceSet B).ncard = 0 ∧
            ∃ v ∈ B.1, (G.incidenceSet v).ncard < 2 then 1 else 0) := by
    have he_eq : Nat.card {e // G.src e ∈ {v | v ∈ B.1} ∧ G.tgt e ∈ {v | v ∈ B.1}} =
        (intEdges B).card := by
      change Nat.card ↑{e : E | G.src e ∈ B.1 ∧ G.tgt e ∈ B.1} = (intEdges B).card
      rw [Nat.card_coe_set_eq, ← ncard_coe_finset]
      congr 1
      ext e
      simp [intEdges]
    have hconn_le : {v | v ∈ B.1}.ncard ≤ (intEdges B).card + 1 := by
      have hcB := (G.induce {v | v ∈ B.1}).card_le_card_add_one_of_connected (c.connected B.1 B.2)
      rw [Nat.card_coe_set_eq] at hcB
      omega
    by_cases hpos : 0 < (c.quotient.incidenceSet B).ncard
    · simp only [hpos, ite_true]
      omega
    · have h0 : (c.quotient.incidenceSet B).ncard = 0 := by omega
      by_cases hlow : ∃ v ∈ B.1, (G.incidenceSet v).ncard < 2
      · simp only [h0, lt_self_iff_false, ite_false, hlow, and_self, ite_true]
        omega
      · simp only [h0, lt_self_iff_false, ite_false, hlow, and_false, add_zero]
        push Not at hlow
        have hcut0 : G.edgeCut {v | v ∈ B.1} = ∅ := by
          rw [← ncard_eq_zero (hs := toFinite _), ← c.ncard_incidenceSet_quotient]
          exact h0
        have hclosed := G.edgeCut_eq_empty_iff.mp hcut0
        -- On the closed block, `G` and `G.induce B` have the same degrees; apply the handshake.
        have hdeg (v : {v | v ∈ B.1}) :
            (G.incidenceSet v.1).ncard = ((G.induce {v | v ∈ B.1}).incidenceSet v).ncard := by
          rw [← ncard_image_of_injective _ Subtype.val_injective]
          congr 1
          ext e
          constructor
          · intro he
            have hW : G.src e ∈ B.1 ∧ G.tgt e ∈ B.1 := by
              rcases he with h | h
              · exact ⟨h ▸ v.2, (hclosed e).mp (h ▸ v.2)⟩
              · exact ⟨(hclosed e).mpr (h ▸ v.2), h ▸ v.2⟩
            exact ⟨⟨e, hW⟩, he.imp Subtype.ext Subtype.ext, rfl⟩
          · rintro ⟨e', he', rfl⟩
            exact he'.imp (congrArg Subtype.val) (congrArg Subtype.val)
        have hhs := (G.induce {v | v ∈ B.1}).sum_ncard_incidenceSet (hloop.induce _)
        simp only [← hdeg, he_eq] at hhs
        have h2 : 2 * {v | v ∈ B.1}.ncard ≤ ∑ v : {v | v ∈ B.1}, (G.incidenceSet v.1).ncard := by
          rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, ← Finset.card_univ, mul_comm,
            ← smul_eq_mul]
          exact Finset.card_nsmul_le_sum _ _ _ fun v _ => hlow v.1 v.2
        omega
  have hsum := Finset.sum_le_sum fun B (_ : B ∈ Finset.univ) => hB_le B
  rw [hv_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, hint_card,
    ← Finset.card_filter, ← Finset.card_filter] at hsum
  omega

/-- Partition `c.blocks` by quotient degree `0, 1, 2, 3`, and relate `2 * |c.external|` to the
degree counts. -/
private theorem degree_partition_identities [Finite V] [Finite E] :
    let q0 := (Finset.univ.filter fun B : c.blocks => (c.quotient.incidenceSet B).ncard = 0).card
    let q1 := (Finset.univ.filter fun B : c.blocks => (c.quotient.incidenceSet B).ncard = 1).card
    let q2 := (Finset.univ.filter fun B : c.blocks => (c.quotient.incidenceSet B).ncard = 2).card
    let q3 := (Finset.univ.filter fun B : c.blocks => (c.quotient.incidenceSet B).ncard = 3).card
    (Finset.univ.filter fun B : c.blocks => 0 < (c.quotient.incidenceSet B).ncard).card =
      q1 + q2 + q3 ∧
    Nat.card c.blocks = q0 + q1 + q2 + q3 ∧
    2 * Nat.card c.external = q1 + 2 * q2 + 3 * q3 := by
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  dsimp only
  have hle3 (B : c.blocks) : (c.quotient.incidenceSet B).ncard ≤ 3 := c.quotient_maxDegreeLE B
  have hsum_deg := c.quotient.sum_ncard_incidenceSet c.quotient_loopless
  -- Pointwise identities for a degree `k ≤ 3`, summed over the blocks below.
  have hpt : ∀ k ≤ 3,
      ((if 0 < k then 1 else 0) =
        (if k = 1 then 1 else 0) + (if k = 2 then 1 else 0) + (if k = 3 then 1 else 0)) ∧
      ((1 : ℕ) = (if k = 0 then 1 else 0) + (if k = 1 then 1 else 0) +
        (if k = 2 then 1 else 0) + (if k = 3 then 1 else 0)) ∧
      k = (if k = 1 then 1 else 0) + 2 * (if k = 2 then 1 else 0) +
        3 * (if k = 3 then 1 else 0) := by
    decide
  refine ⟨?_, ?_, ?_⟩
  · have h := Finset.sum_congr (s₁ := (Finset.univ : Finset c.blocks)) rfl fun B _ =>
      (hpt _ (hle3 B)).1
    simp only [Finset.sum_add_distrib, ← Finset.card_filter] at h
    exact h
  · have h := Finset.sum_congr (s₁ := (Finset.univ : Finset c.blocks)) rfl fun B _ =>
      (hpt _ (hle3 B)).2.1
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      Finset.sum_add_distrib, ← Finset.card_filter] at h
    rwa [Nat.card_eq_fintype_card]
  · have h := Finset.sum_congr (s₁ := (Finset.univ : Finset c.blocks)) rfl fun B _ =>
      (hpt _ (hle3 B)).2.2
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter] at h
    omega

/-- **Degree-three count for connected subcubic multigraphs.** When `G` is loopless, connected, and
compressed into at least two blocks, `#Q₃ ≤ 2 * G.cycleRank + #Q₁`. -/
theorem card_deg_three_le_of_connected [Finite V] [Finite E] (hloop : G.Loopless)
    (hconn : G.toSimpleGraph.Connected) (two : 1 < Nat.card c.blocks) :
    (Finset.univ.filter fun B : c.blocks => (c.quotient.incidenceSet B).ncard = 3).card ≤
      2 * G.cycleRank +
        (Finset.univ.filter fun B : c.blocks => (c.quotient.incidenceSet B).ncard = 1).card := by
  classical
  have hq0 : (Finset.univ.filter fun B : c.blocks =>
      (c.quotient.incidenceSet B).ncard = 0 ∧
        ∃ v ∈ B.1, (G.incidenceSet v).ncard < 2).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro B _ ⟨h0, _⟩
    exact absurd h0 (c.incidenceSet_quotient_nonempty hconn two B).ncard_pos.ne'
  have hint := c.sum_internal_edges_ge hloop
  rw [hq0, add_zero] at hint
  obtain ⟨hpos, _, hdeg⟩ := c.degree_partition_identities
  have hle_ext : Nat.card c.external ≤ Nat.card E := Finite.card_subtype_le _
  have hconnE := G.card_le_card_add_one_of_connected hconn
  rw [cycleRank]
  omega

/-- **Degree-three count under minimum degree two.** When `G` is loopless with minimum degree at
least `2` and `2 * |E| + b = 3 * |V|` (for instance `G = H.induce X` inside a loopless cubic
multigraph `H` with `b = |H.edgeCut X|` and greedy-flip minimum degree `≥ 2`),
`#Q₃ + b ≤ |V| + #Q₁`. -/
theorem card_deg_three_add_le_of_two_le_deg [Finite V] [Finite E] (hloop : G.Loopless)
    (hmin : ∀ v : V, 2 ≤ (G.incidenceSet v).ncard) {b : ℕ}
    (hhand : 2 * Nat.card E + b = 3 * Nat.card V) :
    (Finset.univ.filter fun B : c.blocks => (c.quotient.incidenceSet B).ncard = 3).card + b ≤
      Nat.card V +
        (Finset.univ.filter fun B : c.blocks => (c.quotient.incidenceSet B).ncard = 1).card := by
  classical
  have hq0 : (Finset.univ.filter fun B : c.blocks =>
      (c.quotient.incidenceSet B).ncard = 0 ∧
        ∃ v ∈ B.1, (G.incidenceSet v).ncard < 2).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro B _ ⟨_, v, _, hv⟩
    exact absurd hv (not_lt.mpr (hmin v))
  have hint := c.sum_internal_edges_ge hloop
  rw [hq0, add_zero] at hint
  obtain ⟨hpos, _, hdeg⟩ := c.degree_partition_identities
  have hle_ext : Nat.card c.external ≤ Nat.card E := Finite.card_subtype_le _
  omega

end DegreeThree

end CappedCompression

end Cslib.Circuits.Frontier.Multigraph
