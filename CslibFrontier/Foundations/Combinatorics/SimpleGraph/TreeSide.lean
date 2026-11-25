/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Acyclic.lean`)

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Acyclic

/-!
# Splitting a tree along an edge by path length

For a tree `T` (`hT : T.IsTree`) on an arbitrary vertex type `ι` (without requiring `[Fintype ι]`),
`hT.treeSide u v` is the set of vertices strictly closer to `u` than to `v` along `hT.pathTo`.
Along an edge `T.Adj u v`, the two sides `hT.treeSide u v` and `hT.treeSide v u` are complements
(`treeSide_compl_of_adj`), `(u, v)` is the unique edge crossing from `hT.treeSide u v` to its
complement (`eq_of_mem_treeSide_of_adj_notMem`), subtrees attached to distinct neighbours of `t`
are disjoint (`disjoint_treeSide_of_adj`), and `hT.treeSide t p` decomposes as `insert t` of the
child subtrees `hT.treeSide c t` over all neighbours `c ≠ p` of `t`
(`treeSide_eq_insert_biUnion`).

## Main definitions

* `SimpleGraph.IsTree.treeSide`: the vertices of `T` strictly closer to `u` than to `v`.

## Main results

* `SimpleGraph.IsTree.treeSide_compl_of_adj`: along an edge `T.Adj u v`, `hT.treeSide v u` is the
  complement of `hT.treeSide u v`.
* `SimpleGraph.IsTree.self_mem_treeSide_of_adj`: `u ∈ hT.treeSide u v` when `T.Adj u v`.
* `SimpleGraph.IsTree.disjoint_treeSide_of_adj`: distinct neighbours `u ≠ v` of `t` have disjoint
  subtrees `hT.treeSide u t` and `hT.treeSide v t`.
* `SimpleGraph.IsTree.treeSide_eq_insert_biUnion`: child decomposition of `hT.treeSide t p`.
* `SimpleGraph.IsTree.eq_of_mem_treeSide_of_adj_notMem`: along an edge `T.Adj v p`, `(v, p)` is the
  unique edge of `T` crossing from `hT.treeSide v p` to its complement.
-/

public section

open Set

namespace SimpleGraph.IsTree

variable {ι : Type*} {T : SimpleGraph ι} (hT : T.IsTree)

private theorem length_walk_pos_of_ne {u v : ι} (h : u ≠ v) (p : T.Walk u v) : 0 < p.length := by
  cases p with
  | nil => exact absurd rfl h
  | cons _ _ => exact Nat.succ_pos _

/-- The vertices of `T` strictly closer to `u` than to `v`. When `T.Adj u v`, this is the connected
component of `T - uv` containing `u`. -/
@[expose] def treeSide (u v : ι) : Set ι :=
  {w : ι | (hT.pathTo w u).length < (hT.pathTo w v).length}

@[simp] theorem mem_treeSide {u v w : ι} :
    w ∈ hT.treeSide u v ↔ (hT.pathTo w u).length < (hT.pathTo w v).length := Iff.rfl

/-- Along an edge `T.Adj u v`, the two sides `treeSide u v` and `treeSide v u` are complements. -/
theorem treeSide_compl_of_adj {u v : ι} (huv : T.Adj u v) :
    hT.treeSide v u = (hT.treeSide u v)ᶜ := by
  ext w
  simp only [treeSide, mem_ofPred_eq, mem_compl_iff, not_lt]
  rcases (hT.adj_iff_parent w).mp huv with ⟨hu, rfl⟩ | ⟨hv, rfl⟩
  · have hlen := hT.length_pathTo_parent w hu
    omega
  · have hlen := hT.length_pathTo_parent w hv
    omega

/-- For an edge `T.Adj u v`, `u` lies on its own side `treeSide u v`. -/
theorem self_mem_treeSide_of_adj {u v : ι} (huv : T.Adj u v) : u ∈ hT.treeSide u v := by
  simp only [treeSide, mem_ofPred_eq, pathTo_self, Walk.length_nil]
  exact length_walk_pos_of_ne huv.ne' _

/-- Subtrees attached to distinct neighbours `u ≠ v` of `t` are disjoint. -/
theorem disjoint_treeSide_of_adj {t u v : ι} (hu : T.Adj t u) (hv : T.Adj t v) (huv : u ≠ v) :
    Disjoint (hT.treeSide u t) (hT.treeSide v t) := by
  refine Set.disjoint_left.mpr fun w hwu hwv => huv ?_
  simp only [treeSide, mem_ofPred_eq] at hwu hwv
  have hpu : hT.parent w t = u := by
    rcases (hT.adj_iff_parent w).mp hu with ⟨_, hp⟩ | ⟨huw, hp⟩
    · exact hp
    · exfalso
      have := hT.length_pathTo_parent w huw
      rw [hp] at this
      omega
  have hpv : hT.parent w t = v := by
    rcases (hT.adj_iff_parent w).mp hv with ⟨_, hp⟩ | ⟨hvw, hp⟩
    · exact hp
    · exfalso
      have := hT.length_pathTo_parent w hvw
      rw [hp] at this
      omega
  exact hpu.symm.trans hpv

/-- **Child decomposition of a tree side.** For any edge `T.Adj t p`, `treeSide t p` consists of
`t` together with the disjoint subtrees `treeSide c t` over all neighbours `c ≠ p` of `t`. -/
theorem treeSide_eq_insert_biUnion {t p : ι} (hp : T.Adj t p) :
    hT.treeSide t p = insert t (⋃ c ∈ {c : ι | T.Adj t c ∧ c ≠ p}, hT.treeSide c t) := by
  have hcompl : hT.treeSide t p = (hT.treeSide p t)ᶜ := by
    rw [hT.treeSide_compl_of_adj hp, compl_compl]
  ext w
  simp only [mem_insert_iff, mem_iUnion, mem_ofPred_eq]
  constructor
  · intro hw
    by_cases hwt : w = t
    · exact Or.inl hwt
    · right
      have htw : t ≠ w := Ne.symm hwt
      refine ⟨hT.parent w t, ⟨hT.adj_parent w htw, ?_⟩, ?_⟩
      · intro hcp
        have hlen := hT.length_pathTo_parent w htw
        rw [hcp] at hlen
        have hwp : w ∈ hT.treeSide p t := by
          simp only [treeSide, mem_ofPred_eq]
          omega
        rw [hcompl] at hw
        exact hw hwp
      · simp only [treeSide, mem_ofPred_eq]
        have hlen := hT.length_pathTo_parent w htw
        omega
  · rintro (rfl | ⟨c, ⟨htc, hcp⟩, hwc⟩)
    · exact hT.self_mem_treeSide_of_adj hp
    · rw [hcompl, mem_compl_iff]
      exact Set.disjoint_left.mp (hT.disjoint_treeSide_of_adj htc hp hcp) hwc

/-- An edge `T.Adj v p` separates `hT.treeSide v p` from its complement: the only edge of `T`
crossing from `z ∈ hT.treeSide v p` to `y ∉ hT.treeSide v p` is `(z, y) = (v, p)`. -/
theorem eq_of_mem_treeSide_of_adj_notMem {v p z y : ι} (hadj : T.Adj v p)
    (hz : z ∈ hT.treeSide v p) (hy : y ∉ hT.treeSide v p) (hzy : T.Adj z y) :
    z = v ∧ y = p := by
  suffices h : ∀ n (v p : ι), T.Adj v p → (hT.pathTo z v).length = n →
      z ∈ hT.treeSide v p → y ∉ hT.treeSide v p → z = v ∧ y = p from
    h (hT.pathTo z v).length v p hadj rfl hz hy
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro v p hadj_vp hlen hz_vp hy_vp
    by_cases hzv : z = v
    · subst hzv
      refine ⟨rfl, Classical.byContradiction fun hyp => ?_⟩
      have hy_sub : hT.treeSide y z ⊆ hT.treeSide z p := by
        intro w hw
        rw [hT.treeSide_eq_insert_biUnion hadj_vp]
        exact Set.mem_insert_of_mem z (mem_iUnion₂.mpr ⟨y, ⟨hzy, hyp⟩, hw⟩)
      exact hy_vp (hy_sub (hT.self_mem_treeSide_of_adj hzy.symm))
    · exfalso
      have hz_decomp : z ∈ insert v (⋃ c ∈ {c : ι | T.Adj v c ∧ c ≠ p}, hT.treeSide c v) := by
        rwa [← hT.treeSide_eq_insert_biUnion hadj_vp]
      rcases mem_insert_iff.mp hz_decomp with rfl | hz_union
      · exact hzv rfl
      · obtain ⟨c, ⟨hadj_vc, hcp⟩, hzc⟩ := mem_iUnion₂.mp hz_union
        have hc_sub : hT.treeSide c v ⊆ hT.treeSide v p := by
          intro w hw
          rw [hT.treeSide_eq_insert_biUnion hadj_vp]
          exact Set.mem_insert_of_mem v (mem_iUnion₂.mpr ⟨c, ⟨hadj_vc, hcp⟩, hw⟩)
        have hlt : (hT.pathTo z c).length < n := by
          rw [← hlen]
          exact hzc
        obtain ⟨_, rfl⟩ := ih _ hlt c v hadj_vc.symm rfl hzc (fun hyc => hy_vp (hc_sub hyc))
        exact hy_vp (hT.self_mem_treeSide_of_adj hadj_vp)

end SimpleGraph.IsTree
