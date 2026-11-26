/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Contraction.Threshold
public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Basic

/-!
# Dynamic Soft-Heap Robust Contraction and Edge Deduplication

Steps toward Theorem 5.8 of [PettieRamachandran2002] (#8624). Defines `DynamicDJPTree` and proves
this module's dynamic Soft-Heap adaptation of static Lemma 2.1 (§2.2, p. 18; preceding Soft Heaps
in §2.4, p. 19), Definition 3.1 (DJP-contractible subgraphs, §3.1, p. 20), and Lemma 3.2
(§3.1, p. 20), generalizing Lemma 3.2's distinct-weight subset inclusion to multigraphs with
duplicate `ℕ` weights via `WeaklySupported` / `IsMinSpanningForest`. Also proves the combinatorial
stopping-rule step `maxsize_le_card_biUnion_of_stop` toward Lemma 3.3(c) (§3.2, pp. 21–22) and
parallel-edge / self-loop deduplication (`dedupSimpleEdges`) preserving `IsMinSpanningForest`.

## Main definitions

* `Cslib.Query.MinimumSpanningForest.djpVerts`,
  `Cslib.Query.MinimumSpanningForest.DynamicDJPTree`: dynamic Soft-Heap DJP component state and
  monotonic key-corruption invariants.
* `Cslib.Query.MinimumSpanningForest.dedupSimpleEdges`: parallel-edge and self-loop removal via
  `allPairs n`.

## Main results

* `Cslib.Query.MinimumSpanningForest.DynamicDJPTree.rel_treeEdges_filter_of_border`: dynamic
  Soft-Heap border-edge path property adapting [PettieRamachandran2002], Lemma 2.1.
* `Cslib.Query.MinimumSpanningForest.weaklySupported_of_dynamicDJPTree`,
  `Cslib.Query.MinimumSpanningForest.isMinSpanningForest_of_dynamicDJPTree`: dynamic Soft-Heap
  contraction lifting adapting [PettieRamachandran2002], Definition 3.1 and Lemma 3.2.
* `Cslib.Query.MinimumSpanningForest.maxsize_le_card_biUnion_of_stop`: combinatorial stopping-rule
  step toward Lemma 3.3(c) of [PettieRamachandran2002] (without formalizing the full `Partition`
  procedure, and allowing isolated singletons for disconnected inputs).
* `Cslib.Query.MinimumSpanningForest.dedupSimpleEdges_isSimple`,
  `Cslib.Query.MinimumSpanningForest.isMinSpanningForest_of_dedupSimpleEdges`: simple-graph
  deduplication preserves MSF optimality.
-/

public section

namespace Cslib.Query.MinimumSpanningForest

open Cslib.DataStructure DisjointSet
open Cslib.Algorithms.Lean.Kruskal

/-! ## Dynamic Soft-Heap DJP Invariant -/

/-- Prefix vertex set of the first `k` steps of a dynamic DJP tree starting at `root`. -/
@[expose] def djpVerts {n numSteps : ℕ} (root : Fin n) (vOut : Fin numSteps → Fin n) :
    ℕ → Finset (Fin n)
  | 0 => {root}
  | k + 1 =>
    if hk : k < numSteps then insert (vOut ⟨k, hk⟩) (djpVerts root vOut k)
    else djpVerts root vOut k

theorem mem_djpVerts_mono {n numSteps : ℕ} (root : Fin n) (vOut : Fin numSteps → Fin n)
    {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) {x : Fin n} (hx : x ∈ djpVerts root vOut k₁) :
    x ∈ djpVerts root vOut k₂ := by
  induction hk with
  | refl => exact hx
  | step _ ih =>
    dsimp only [djpVerts]
    split_ifs
    · exact Finset.mem_insert_of_mem ih
    · exact ih

theorem vOut_mem_djpVerts_succ {n numSteps : ℕ} (root : Fin n)
    (vOut : Fin numSteps → Fin n) (s : Fin numSteps) :
    vOut s ∈ djpVerts root vOut (s.val + 1) := by
  dsimp only [djpVerts]
  simp only [s.isLt, ↓reduceDIte]
  exact Finset.mem_insert_self _ _

/-- Dynamic Soft-Heap DJP tree recording popped edges `edge s`, Soft-Heap pop keys `wPop s`,
and monotonic DJP step invariants ([PettieRamachandran2002], Section 2.4 and Lemma 2.1). -/
structure DynamicDJPTree (n : ℕ) where
  /-- Number of DJP growth steps executed. -/
  numSteps : ℕ
  /-- Starting root vertex of the dynamic DJP component. -/
  root : Fin n
  /-- Real edge inserted at step `s`. -/
  edge : Fin numSteps → WeightedEdge n ℕ
  /-- Corrupted Soft-Heap pop key recorded at step `s`. -/
  wPop : Fin numSteps → ℕ
  /-- Endpoint already inside the tree prior to step `s`. -/
  vIn : Fin numSteps → Fin n
  /-- Newly added endpoint outside the tree prior to step `s`. -/
  vOut : Fin numSteps → Fin n
  edge_weight_le_wPop : ∀ s : Fin numSteps, (edge s).weight ≤ wPop s
  ends_match : ∀ s : Fin numSteps,
    ((edge s).u = vIn s ∧ (edge s).v = vOut s) ∨ ((edge s).v = vIn s ∧ (edge s).u = vOut s)
  vIn_mem : ∀ s : Fin numSteps, vIn s ∈ djpVerts root vOut s.val
  vOut_not_mem : ∀ s : Fin numSteps, vOut s ∉ djpVerts root vOut s.val
  djp_future : ∀ s s' : Fin numSteps, s.val < s'.val →
    ((edge s').u ∈ djpVerts root vOut s.val ↔ (edge s').v ∉ djpVerts root vOut s.val) →
    wPop s ≤ wPop s'

/-- Vertex set at step `k` of a `DynamicDJPTree`. -/
abbrev DynamicDJPTree.treeVerts {n : ℕ} (D : DynamicDJPTree n) (k : ℕ) :
    Finset (Fin n) :=
  djpVerts D.root D.vOut k

/-- List of edges added during a `DynamicDJPTree`. -/
@[expose] def DynamicDJPTree.treeEdges {n : ℕ} (D : DynamicDJPTree n) :
    List (WeightedEdge n ℕ) :=
  (List.finRange D.numSteps).map D.edge

/-- Multigraph endpoint lookup for `DynamicDJPTree`. -/
@[expose] def DynamicDJPTree.ends {n : ℕ} (D : DynamicDJPTree n) (s : Fin D.numSteps) :
    Sym2 (Fin n) :=
  s((D.edge s).u, (D.edge s).v)

theorem DynamicDJPTree.mem_treeVerts_of_edge {n : ℕ} (D : DynamicDJPTree n)
    (s : Fin D.numSteps) :
    (D.edge s).u ∈ D.treeVerts (s.val + 1) ∧ (D.edge s).v ∈ D.treeVerts (s.val + 1) := by
  have hi := mem_djpVerts_mono D.root D.vOut (Nat.le_succ s.val) (D.vIn_mem s)
  have ho := vOut_mem_djpVerts_succ D.root D.vOut s
  rcases D.ends_match s with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · exact ⟨hu ▸ hi, hv ▸ ho⟩
  · exact ⟨hu ▸ ho, hv ▸ hi⟩

theorem DynamicDJPTree.joins_treeVerts {n : ℕ} (D : DynamicDJPTree n) {x : Fin n}
    (hx : x ∈ D.treeVerts D.numSteps) :
    Cslib.Multigraph.Joins D.ends Set.univ D.root x := by
  have hgen : ∀ k : ℕ, k ≤ D.numSteps → ∀ y ∈ D.treeVerts k,
      Cslib.Multigraph.Joins D.ends Set.univ D.root y := by
    intro k hk
    induction k with
    | zero =>
      intro y hy
      simp only [DynamicDJPTree.treeVerts, djpVerts, Finset.mem_singleton] at hy
      subst hy; exact .refl _
    | succ k ih =>
      intro y hy
      dsimp only [DynamicDJPTree.treeVerts, djpVerts] at hy
      have hkn : k < D.numSteps := Nat.lt_of_succ_le hk
      simp only [hkn, ↓reduceDIte] at hy
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · let s : Fin D.numSteps := ⟨k, hkn⟩
        have hconn_in := ih hkn.le (D.vIn s) (D.vIn_mem s)
        have hs_ends : D.ends s = s(D.vIn s, D.vOut s) := by
          dsimp only [DynamicDJPTree.ends]
          rcases D.ends_match s with ⟨hu, hv⟩ | ⟨hv, hu⟩
          · rw [hu, hv]
          · rw [hu, hv, Sym2.eq_swap]
        exact hconn_in.trans (Cslib.Multigraph.Joins.of_mem (Set.mem_univ s) hs_ends)
      · exact ih hkn.le y hy'
  exact hgen D.numSteps le_rfl x hx

/-- Dynamic Soft-Heap border-edge path property toward Theorem 5.8 of [PettieRamachandran2002]
(#8624), adapting static Lemma 2.1 (§2.2, p. 18) to Soft-Heap `wPop` bounds (§2.4, p. 19): any
two tree vertices `x, y ∈ D.treeVerts D.numSteps` with uncorrupted external border edges `e₁, e₂`
are connected in `D.treeEdges` using only edges of actual weight at most
`max e₁.weight e₂.weight`. -/
theorem DynamicDJPTree.rel_treeEdges_filter_of_border {n : ℕ} (D : DynamicDJPTree n) {x y : Fin n}
    (hx : x ∈ D.treeVerts D.numSteps) (hy : y ∈ D.treeVerts D.numSteps)
    (e₁ e₂ : WeightedEdge n ℕ)
    (he₁_cut : (e₁.u = x ∧ e₁.v ∉ D.treeVerts D.numSteps) ∨
      (e₁.v = x ∧ e₁.u ∉ D.treeVerts D.numSteps))
    (he₂_cut : (e₂.u = y ∧ e₂.v ∉ D.treeVerts D.numSteps) ∨
      (e₂.v = y ∧ e₂.u ∉ D.treeVerts D.numSteps))
    (huncorr₁ : ∀ s : Fin D.numSteps,
      (e₁.u ∈ D.treeVerts s.val ↔ e₁.v ∉ D.treeVerts s.val) → D.wPop s ≤ e₁.weight)
    (huncorr₂ : ∀ s : Fin D.numSteps,
      (e₂.u ∈ D.treeVerts s.val ↔ e₂.v ∉ D.treeVerts s.val) → D.wPop s ≤ e₂.weight) :
    (edgePartition (D.treeEdges.filter fun e =>
      decide (e.weight ≤ max e₁.weight e₂.weight))).rel x y = true := by
  classical
  let valid : Finset (Finset (Fin D.numSteps)) :=
    Finset.univ.filter fun P => Cslib.Multigraph.Joins D.ends (P : Set (Fin D.numSteps)) x y
  have huniv_valid : Finset.univ ∈ valid := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa using (D.joins_treeVerts hx).symm.trans (D.joins_treeVerts hy)
  obtain ⟨P, hP_mem, hP_min⟩ := Finset.exists_min_image valid Finset.card ⟨Finset.univ, huniv_valid⟩
  have hP_conn : Cslib.Multigraph.Joins D.ends (P : Set (Fin D.numSteps)) x y :=
    (Finset.mem_filter.mp hP_mem).2
  by_cases hPe : P = ∅
  · subst hPe
    rw [Finset.coe_empty, Cslib.Multigraph.joins_empty_iff] at hP_conn
    subst hP_conn
    exact (edgePartition _).refl _
  · have hP_ne : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hPe
    let key : Fin D.numSteps → ℕ := fun s => D.wPop s * (D.numSteps + 1) + s.val
    obtain ⟨sStar, hsStar_mem, hsStar_max⟩ := Finset.exists_max_image P key hP_ne
    let A := D.treeVerts sStar.val
    have hnot_erase :
        ¬ Cslib.Multigraph.Joins D.ends ((P.erase sStar : Finset _) : Set _) x y := by
      intro hc
      have her_mem : P.erase sStar ∈ valid := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
      have hcard := hP_min (P.erase sStar) her_mem
      have hlt := Finset.card_erase_lt_of_mem hsStar_mem
      omega
    have hno_cross : ∀ s' ∈ P.erase sStar, (D.edge s').u ∈ A ↔ (D.edge s').v ∈ A := by
      intro s' hs'
      have hs'_mem := Finset.mem_of_mem_erase hs'
      have hs'_ne : s' ≠ sStar := Finset.ne_of_mem_erase hs'
      by_contra hnot
      have hcross : (D.edge s').u ∈ A ↔ (D.edge s').v ∉ A := by
        constructor
        · intro hu hv; exact hnot ⟨fun _ => hv, fun _ => hu⟩
        · intro hnv
          by_contra hnu
          exact hnot ⟨fun hu => absurd hu hnu, fun hv => absurd hv hnv⟩
      have hgt : sStar.val < s'.val := by
        by_contra hle
        have hle' : s'.val + 1 ≤ sStar.val := by
          have : s'.val ≠ sStar.val := fun h => hs'_ne (Fin.ext h)
          omega
        have hm := D.mem_treeVerts_of_edge s'
        have hm1 := mem_djpVerts_mono D.root D.vOut hle' hm.1
        have hm2 := mem_djpVerts_mono D.root D.vOut hle' hm.2
        exact absurd hm2 (hcross.mp hm1)
      have hw := D.djp_future sStar s' hgt hcross
      have hk_max := hsStar_max s' hs'_mem
      dsimp only [key] at hk_max
      have hmul := Nat.mul_le_mul_right (D.numSteps + 1) hw
      omega
    have hcut_inv : ∀ {u v : Fin n},
        Cslib.Multigraph.Joins D.ends ((P.erase sStar : Finset _) : Set _) u v →
        (u ∈ A ↔ v ∈ A) := by
      have hstep : ∀ {u v : Fin n}, u ∈ A → v ∉ A →
          ¬ Cslib.Multigraph.Joins D.ends ((P.erase sStar : Finset _) : Set _) u v := by
        intro u v hu hv hj
        obtain ⟨s', hs', hcut'⟩ := hj.exists_mem_edgeCut (P := (A : Set (Fin n))) hu hv
        obtain ⟨a, b, hab, ha, hb⟩ := Graph.mem_edgeCut_iff.1 hcut'
        change D.ends s' = s(a, b) at hab
        have hc' := hno_cross s' hs'
        dsimp only [DynamicDJPTree.ends] at hab
        rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hb (hc'.mp ha)
        · exact hb (hc'.mpr ha)
      exact fun {u v} h => ⟨fun hu => by by_contra hv; exact hstep hu hv h,
        fun hv => by by_contra hu; exact hstep hv hu h.symm⟩
    have hxy_opp : (x ∈ A ∧ y ∉ A) ∨ (y ∈ A ∧ x ∉ A) := by
      have hP_ins : Cslib.Multigraph.Joins D.ends
          (insert sStar ((P.erase sStar : Finset _) : Set _)) x y := by
        rw [← Finset.coe_insert, Finset.insert_erase hsStar_mem]
        exact hP_conn
      rcases Cslib.Multigraph.joins_insert_iff.mp hP_ins with h | ⟨a, b, hab, hxa, hby⟩
      · exact absurd h hnot_erase
      · have hs_ends : D.ends sStar = s(D.vIn sStar, D.vOut sStar) := by
          dsimp only [DynamicDJPTree.ends]
          rcases D.ends_match sStar with ⟨hu, hv⟩ | ⟨hv, hu⟩
          · rw [hu, hv]
          · rw [hu, hv, Sym2.eq_swap]
        have hsStar_inA : D.vIn sStar ∈ A := D.vIn_mem sStar
        have hsStar_notA : D.vOut sStar ∉ A := D.vOut_not_mem sStar
        rcases Sym2.eq_iff.mp (hab.symm.trans hs_ends) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact .inl ⟨(hcut_inv hxa).mpr hsStar_inA, fun hy => hsStar_notA ((hcut_inv hby).mpr hy)⟩
        · exact .inr ⟨(hcut_inv hby).mp hsStar_inA, fun hx => hsStar_notA ((hcut_inv hxa).mp hx)⟩
    have hw_bound : D.wPop sStar ≤ max e₁.weight e₂.weight := by
      have hsubA : A ⊆ D.treeVerts D.numSteps := fun z hz =>
        mem_djpVerts_mono D.root D.vOut sStar.isLt.le hz
      have mk_cross : ∀ {z : Fin n} {e : WeightedEdge n ℕ}, z ∈ A →
          ((e.u = z ∧ e.v ∉ D.treeVerts D.numSteps) ∨
            (e.v = z ∧ e.u ∉ D.treeVerts D.numSteps)) →
          (e.u ∈ A ↔ e.v ∉ A) := fun hzA hcut => by
        rcases hcut with ⟨rfl, hnv⟩ | ⟨rfl, hnu⟩
        · exact ⟨fun _ hv => hnv (hsubA hv), fun _ => hzA⟩
        · exact ⟨fun hu => absurd (hsubA hu) hnu, fun hnv => absurd hzA hnv⟩
      rcases hxy_opp with ⟨hxA, _⟩ | ⟨hyA, _⟩
      · exact le_trans (huncorr₁ sStar (mk_cross hxA he₁_cut)) (le_max_left _ _)
      · exact le_trans (huncorr₂ sStar (mk_cross hyA he₂_cut)) (le_max_right _ _)
    have hP_sub_w : ∀ s ∈ P, (D.edge s).weight ≤ max e₁.weight e₂.weight := fun s hs => by
      have hk := hsStar_max s hs
      dsimp only [key] at hk
      have hpop : D.wPop s ≤ D.wPop sStar := by
        by_contra hgt
        have h1 : D.wPop sStar + 1 ≤ D.wPop s := Nat.lt_of_not_ge hgt
        have hmul := Nat.mul_le_mul_right (D.numSteps + 1) h1
        rw [Nat.add_mul, Nat.one_mul] at hmul
        have hsStar_lt : sStar.val < D.numSteps + 1 := Nat.lt_succ_of_lt sStar.isLt
        omega
      exact (D.edge_weight_le_wPop s).trans (hpop.trans hw_bound)
    let W := max e₁.weight e₂.weight
    let F := D.treeEdges.filter fun e => decide (e.weight ≤ W)
    have hconn_filt : ∀ a b : Fin n,
        Cslib.Multigraph.Joins D.ends (P : Set (Fin D.numSteps)) a b →
        (edgePartition F).rel a b = true := by
      intro a b hab
      induction hab with
      | refl => exact (edgePartition F).refl _
      | @tail c d _ hstep ih =>
        obtain ⟨s, hsP, hends⟩ := hstep
        have he_mem : D.edge s ∈ F :=
          List.mem_filter.mpr ⟨List.mem_map.mpr ⟨s, List.mem_finRange s, rfl⟩,
            decide_eq_true (hP_sub_w s hsP)⟩
        have hrel_s : (edgePartition F).rel (D.edge s).u (D.edge s).v = true :=
          rel_edgePartitionFrom_of_mem (Partition.discrete n) he_mem
        dsimp only [DynamicDJPTree.ends] at hends
        rcases Sym2.eq_iff.mp hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (edgePartition F).trans ih hrel_s
        · exact (edgePartition F).trans ih ((edgePartition F).symm hrel_s)
    exact hconn_filt x y hP_conn

/-! ## Dynamic Soft-Heap Contraction Lifting and Stopping Rule -/

private theorem filter_contractEdgeList {n n' : ℕ} (c : Fin n → Fin n')
    (w : ℕ) (xs : List (WeightedEdge n ℕ)) :
    (contractEdgeList c xs).filter (fun e => decide (e.weight ≤ w)) =
      contractEdgeList c (xs.filter fun e => decide (e.weight ≤ w)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [contractEdgeList]
    rw [List.map_cons, List.filter_cons, List.filter_cons]
    have hwt : (contractEdge c x).weight = x.weight := rfl
    cases hp : decide (x.weight ≤ w)
    · simp only [hwt, hp, Bool.false_eq_true, ↓reduceIte]; exact ih
    · simp only [hwt, hp, ↓reduceIte, List.map_cons]; exact congrArg (contractEdge c x :: ·) ih

/-- Dynamic Soft-Heap contraction lifting toward Theorem 5.8 of [PettieRamachandran2002] (#8624),
adapting Definition 3.1 and Lemma 3.2 (§3.1, p. 20; which applies static Lemma 2.1 to a
raised-weight graph) onto `DynamicDJPTree` and generalizing Lemma 3.2's distinct-weight subset
inclusion to multigraphs with duplicate `ℕ` weights via `WeaklySupported`: given internal edges
`C` containing `D.treeEdges`, corrupted border `M_C`, external edges `H_edges` (uncorrupted across
`D.treeVerts`), MSF `F_C` of `C`, and contraction-MSF lift `H_lift` of `H_edges`, every edge of
`es` is weakly supported by `F_C ++ H_lift ++ M_C`. -/
theorem weaklySupported_of_dynamicDJPTree {n n' : ℕ}
    (es C M_C H_edges F_C H_lift : List (WeightedEdge n ℕ))
    (D : DynamicDJPTree n) (c : Fin n → Fin n')
    (hpart : (C ++ M_C ++ H_edges).Perm es)
    (hD_sub : D.treeEdges.Subperm C)
    (hH_no_int : ∀ e ∈ H_edges,
      ¬ (e.u ∈ D.treeVerts D.numSteps ∧ e.v ∈ D.treeVerts D.numSteps))
    (huncorr : ∀ e ∈ H_edges, ∀ s : Fin D.numSteps,
      (e.u ∈ D.treeVerts s.val ↔ e.v ∉ D.treeVerts s.val) → D.wPop s ≤ e.weight)
    (hc : ∀ x y : Fin n,
      c x = c y ↔ x = y ∨ (x ∈ D.treeVerts D.numSteps ∧ y ∈ D.treeVerts D.numSteps))
    (hFC : IsMinSpanningForest C F_C)
    (hHL_sub : H_lift.Subperm H_edges)
    (hHL_msf : IsMinSpanningForest (contractEdgeList c H_edges) (contractEdgeList c H_lift)) :
    ∀ e ∈ es, WeaklySupported (F_C ++ H_lift ++ M_C) e := by
  intro e he
  have hmem : e ∈ C ∨ e ∈ M_C ∨ e ∈ H_edges := by
    have hp := hpart.symm.subset he
    simpa [List.mem_append, or_assoc] using hp
  have hFC_thresh := (isMinSpanningForest_iff_threshold_partition C F_C).mp hFC
  have hHL_thresh := (isMinSpanningForest_iff_threshold_partition
    (contractEdgeList c H_edges) (contractEdgeList c H_lift)).mp hHL_msf
  rcases hmem with heC | heM | heH
  · dsimp only [WeaklySupported]
    have hC_rel : (edgePartition (C.filter fun f => decide (f.weight ≤ e.weight))).rel
        e.u e.v = true :=
      rel_edgePartitionFrom_of_mem (Partition.discrete n)
        (List.mem_filter.mpr ⟨heC, decide_eq_true le_rfl⟩)
    rw [← hFC_thresh.2 e.weight] at hC_rel
    have hsub : (F_C.filter fun f => decide (f.weight ≤ e.weight)).Subperm
        ((F_C ++ H_lift ++ M_C).filter fun f => decide (f.weight ≤ e.weight)) :=
      ((List.sublist_append_left F_C H_lift).subperm.trans
        (List.sublist_append_left (F_C ++ H_lift) M_C).subperm).filter _
    exact edgePartition_mono_subperm hsub hC_rel
  · exact rel_edgePartitionFrom_of_mem (Partition.discrete n)
      (List.mem_filter.mpr ⟨List.mem_append_right _ heM, decide_eq_true le_rfl⟩)
  · dsimp only [WeaklySupported]
    let w := e.weight
    let U := (F_C ++ H_lift ++ M_C).filter fun f => decide (f.weight ≤ w)
    let H' := H_lift.filter fun f => decide (f.weight ≤ w)
    have hc_H : (edgePartition (contractEdgeList c H')).rel (c e.u) (c e.v) = true := by
      have h1 : (edgePartition (contractEdgeList c (H_edges.filter fun f =>
          decide (f.weight ≤ w)))).rel (c e.u) (c e.v) = true :=
        rel_edgePartitionFrom_of_mem (Partition.discrete n')
          (List.mem_map_of_mem (f := contractEdge c)
            (List.mem_filter.mpr ⟨heH, decide_eq_true le_rfl⟩))
      rw [← filter_contractEdgeList, ← hHL_thresh.2 w, filter_contractEdgeList] at h1
      exact h1
    let EndOf (x : Fin n) : Prop :=
      ∃ h ∈ H_edges, h.weight ≤ w ∧ (h.u = x ∨ h.v = x)
    have hbridge : ∀ x y : Fin n, c x = c y → EndOf x → EndOf y →
        (edgePartition U).rel x y = true := by
      intro x y hcxy hxE hyE
      rcases (hc x y).mp hcxy with rfl | ⟨hxV, hyV⟩
      · exact (edgePartition U).refl _
      · obtain ⟨h₁, hh₁, hw₁, hx₁⟩ := hxE
        obtain ⟨h₂, hh₂, hw₂, hy₂⟩ := hyE
        have mk_cut : ∀ (z : Fin n) (f : WeightedEdge n ℕ),
            z ∈ D.treeVerts D.numSteps → f ∈ H_edges → (f.u = z ∨ f.v = z) →
            (f.u = z ∧ f.v ∉ D.treeVerts D.numSteps) ∨
              (f.v = z ∧ f.u ∉ D.treeVerts D.numSteps) := fun z f hzV hf hzf => by
          rcases hzf with rfl | rfl
          · exact .inl ⟨rfl, fun hv => hH_no_int f hf ⟨hzV, hv⟩⟩
          · exact .inr ⟨rfl, fun hu => hH_no_int f hf ⟨hu, hzV⟩⟩
        have h21 := D.rel_treeEdges_filter_of_border hxV hyV h₁ h₂
          (mk_cut x h₁ hxV hh₁ hx₁) (mk_cut y h₂ hyV hh₂ hy₂)
          (huncorr h₁ hh₁) (huncorr h₂ hh₂)
        have hD_rel := edgePartition_filter_mono_subperm hD_sub (max_le hw₁ hw₂) h21
        rw [← hFC_thresh.2 w] at hD_rel
        have hU_sub : (F_C.filter fun f => decide (f.weight ≤ w)).Subperm U :=
          ((List.sublist_append_left F_C H_lift).subperm.trans
            (List.sublist_append_left (F_C ++ H_lift) M_C).subperm).filter _
        exact edgePartition_mono_subperm hU_sub hD_rel
    rw [rel_edgePartition_iff_eqvGen] at hc_H
    have hgen : ∀ x' y' : Fin n',
        Relation.EqvGen (fun a b => ∃ f ∈ contractEdgeList c H', a = f.u ∧ b = f.v) x' y' →
        x' = y' ∨ ∃ a b : Fin n, c a = x' ∧ c b = y' ∧
          EndOf a ∧ EndOf b ∧ (edgePartition U).rel a b = true := by
      intro x' y' hxy
      induction hxy with
      | refl _ => exact .inl rfl
      | rel a' b' hab =>
        obtain ⟨f, hf, rfl, rfl⟩ := hab
        simp only [contractEdgeList, List.mem_map] at hf
        obtain ⟨h, hhH, rfl⟩ := hf
        have hh_mem := List.mem_filter.mp hhH
        have hh_edge : h ∈ H_edges := hHL_sub.subset hh_mem.1
        have hh_w : h.weight ≤ w := decide_eq_true_eq.mp hh_mem.2
        have hh_U : h ∈ U := List.mem_filter.mpr ⟨List.mem_append_left _
          (List.mem_append_right _ hh_mem.1), hh_mem.2⟩
        exact .inr ⟨h.u, h.v, rfl, rfl, ⟨h, hh_edge, hh_w, .inl rfl⟩,
          ⟨h, hh_edge, hh_w, .inr rfl⟩, rel_edgePartitionFrom_of_mem (Partition.discrete n) hh_U⟩
      | symm _ _ _ ih =>
        rcases ih with rfl | ⟨a, b, ha, hb, oa, ob, hrel⟩
        · exact .inl rfl
        · exact .inr ⟨b, a, hb, ha, ob, oa, (edgePartition U).symm hrel⟩
      | trans _ _ _ _ _ ih1 ih2 =>
        rcases ih1 with rfl | ⟨a, y₁, ha, hy₁, oa, oy₁, h1⟩
        · exact ih2
        · rcases ih2 with rfl | ⟨y₂, b, hy₂, hb, oy₂, ob, h2⟩
          · exact .inr ⟨a, y₁, ha, hy₁, oa, oy₁, h1⟩
          · have hb12 := hbridge y₁ y₂ (hy₁.trans hy₂.symm) oy₁ oy₂
            exact .inr ⟨a, b, ha, hb, oa, ob,
              (edgePartition U).trans h1 ((edgePartition U).trans hb12 h2)⟩
    have heuEnd : EndOf e.u := ⟨e, heH, le_rfl, .inl rfl⟩
    have hevEnd : EndOf e.v := ⟨e, heH, le_rfl, .inr rfl⟩
    rcases hgen _ _ hc_H with heqc | ⟨a, b, ha, hb, oa, ob, hab⟩
    · exact hbridge e.u e.v heqc heuEnd hevEnd
    · exact (edgePartition U).trans (hbridge e.u a ha.symm heuEnd oa)
        ((edgePartition U).trans hab (hbridge b e.v hb ob hevEnd))

/-- Step toward Theorem 5.8 of [PettieRamachandran2002] (#8624): any MSF `F` of the dynamic-DJP
contracted support list `F_C ++ H_lift ++ M_C` is an MSF of `es` (generalizing Lemma 3.2,
§3.1, p. 20 to multigraphs with duplicate `ℕ` weights via `WeaklySupported`). -/
theorem isMinSpanningForest_of_dynamicDJPTree {n n' : ℕ}
    (es C M_C H_edges F_C H_lift F : List (WeightedEdge n ℕ))
    (D : DynamicDJPTree n) (c : Fin n → Fin n')
    (hpart : (C ++ M_C ++ H_edges).Perm es)
    (hD_sub : D.treeEdges.Subperm C)
    (hH_no_int : ∀ e ∈ H_edges,
      ¬ (e.u ∈ D.treeVerts D.numSteps ∧ e.v ∈ D.treeVerts D.numSteps))
    (huncorr : ∀ e ∈ H_edges, ∀ s : Fin D.numSteps,
      (e.u ∈ D.treeVerts s.val ↔ e.v ∉ D.treeVerts s.val) → D.wPop s ≤ e.weight)
    (hc : ∀ x y : Fin n,
      c x = c y ↔ x = y ∨ (x ∈ D.treeVerts D.numSteps ∧ y ∈ D.treeVerts D.numSteps))
    (hFC : IsMinSpanningForest C F_C)
    (hHL_sub : H_lift.Subperm H_edges)
    (hHL_msf : IsMinSpanningForest (contractEdgeList c H_edges) (contractEdgeList c H_lift))
    (hF : IsMinSpanningForest (F_C ++ H_lift ++ M_C) F) :
    IsMinSpanningForest es F := by
  have hsub_base : (F_C ++ H_lift ++ M_C).Subperm es := by
    have hp : (F_C ++ H_lift ++ M_C).Subperm (C ++ H_edges ++ M_C) :=
      (hFC.1.1.append hHL_sub).append (List.Subperm.refl _)
    have hp2 : (C ++ H_edges ++ M_C).Perm (C ++ M_C ++ H_edges) := by
      rw [List.append_assoc, List.append_assoc]
      exact List.Perm.append_left C List.perm_append_comm
    exact hp.trans (hp2.trans hpart).subperm
  exact isMinSpanningForest_of_weakSupport es (F_C ++ H_lift ++ M_C) F hsub_base
    (weaklySupported_of_dynamicDJPTree es C M_C H_edges F_C H_lift D c hpart hD_sub
      hH_no_int huncorr hc hFC hHL_sub hHL_msf) hF

/-- Combinatorial stopping-rule step toward Lemma 3.3(c) of [PettieRamachandran2002] (#8624;
§3.2, pp. 21–22, without formalizing the full `Partition` procedure): every connected conglomerate
`I` of stopped vertex sets either reaches size at least `maxsize` or forms an isolated singleton
(generalizing connected inputs to disconnected graphs). -/
theorem maxsize_le_card_biUnion_of_stop {n k maxsize : ℕ}
    (V_comp : Fin k → Finset (Fin n))
    (hstop : ∀ i : Fin k,
      maxsize ≤ (V_comp i).card ∨
      (∃ j : Fin k, j.val < i.val ∧ (V_comp i ∩ V_comp j).Nonempty) ∨
      ¬ ∃ i' : Fin k, i' ≠ i ∧ (V_comp i ∩ V_comp i').Nonempty)
    (I : Finset (Fin k)) (hI_ne : I.Nonempty)
    (hclosed : ∀ i ∈ I, ∀ j : Fin k, (V_comp i ∩ V_comp j).Nonempty → j ∈ I)
    (hI_conn : ∀ J : Finset (Fin k), J.Nonempty → J ⊂ I →
      ∃ a ∈ J, ∃ b ∈ I \ J, (V_comp a ∩ V_comp b).Nonempty) :
    maxsize ≤ (I.biUnion V_comp).card ∨
      (I.card = 1 ∧ ∃ i₀ ∈ I, ¬ ∃ j : Fin k, j ≠ i₀ ∧ (V_comp i₀ ∩ V_comp j).Nonempty) := by
  by_cases hbig : ∃ i ∈ I, maxsize ≤ (V_comp i).card
  · obtain ⟨i, hi, hcard⟩ := hbig
    exact .inl (hcard.trans (Finset.card_le_card (Finset.subset_biUnion_of_mem V_comp hi)))
  · let key : Fin k → ℕ := fun i => i.val
    obtain ⟨i₀, hi₀, hi₀_min⟩ := Finset.exists_min_image I key hI_ne
    have hno_big : ¬ (maxsize ≤ (V_comp i₀).card) := fun h => hbig ⟨i₀, hi₀, h⟩
    have hno_prev : ¬ ∃ j : Fin k, j.val < i₀.val ∧ (V_comp i₀ ∩ V_comp j).Nonempty := by
      rintro ⟨j, hjlt, hinter⟩
      have hjI := hclosed i₀ hi₀ j hinter
      have hmin := hi₀_min j hjI
      dsimp only [key] at hmin
      omega
    have hiso : ¬ ∃ i' : Fin k, i' ≠ i₀ ∧ (V_comp i₀ ∩ V_comp i').Nonempty := by
      rcases hstop i₀ with h | h | h
      · exact absurd h hno_big
      · exact absurd h hno_prev
      · exact h
    have hsingleton : I.card = 1 := by
      by_contra hne
      have hssub : ({i₀} : Finset (Fin k)) ⊂ I := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.singleton_subset_iff.mpr hi₀, fun heq => ?_⟩
        rw [← heq, Finset.card_singleton] at hne
        exact hne rfl
      obtain ⟨a, ha, b, hb, hinter⟩ := hI_conn {i₀} (Finset.singleton_nonempty i₀) hssub
      rw [Finset.mem_singleton] at ha
      subst ha
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hb
      exact hiso ⟨b, hb.2, hinter⟩
    exact .inr ⟨hsingleton, i₀, hi₀, hiso⟩

/-! ## Edge Deduplication to Simple Graphs -/

private def canonicalPair {n : ℕ} (e : WeightedEdge n ℕ) : Fin n × Fin n :=
  if e.u.val < e.v.val then (e.u, e.v) else (e.v, e.u)

private def minByPairAux {n : ℕ} (p : Fin n × Fin n) :
    List (WeightedEdge n ℕ) → Option (WeightedEdge n ℕ)
  | [] => none
  | e :: rest =>
    let tail := minByPairAux p rest
    if canonicalPair e = p then
      match tail with
      | none => some e
      | some best => some (if e.weight ≤ best.weight then e else best)
    else tail

private theorem minByPairAux_eq_foldr {n : ℕ} (p : Fin n × Fin n)
    (es : List (WeightedEdge n ℕ)) :
    minByPairAux p es = es.foldr (fun e tail =>
      if (if e.u.val < e.v.val then (e.u, e.v) else (e.v, e.u)) = p then
        match tail with
        | none => some e
        | some best => some (if e.weight ≤ best.weight then e else best)
      else tail) none := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
    simp only [minByPairAux, canonicalPair, List.foldr_cons, ih]

/-- Remove self-loops and keep a minimum-weight edge per unordered vertex pair via
`allPairs n`. -/
@[expose] def dedupSimpleEdges {n : ℕ} (es : List (WeightedEdge n ℕ)) :
    List (WeightedEdge n ℕ) :=
  (allPairs n).filterMap fun p => es.foldr (fun e tail =>
    if (if e.u.val < e.v.val then (e.u, e.v) else (e.v, e.u)) = p then
      match tail with
      | none => some e
      | some best => some (if e.weight ≤ best.weight then e else best)
    else tail) none

private theorem dedupSimpleEdges_eq_filterMap {n : ℕ} (es : List (WeightedEdge n ℕ)) :
    dedupSimpleEdges es = (allPairs n).filterMap fun p => minByPairAux p es := by
  dsimp only [dedupSimpleEdges]
  exact congrArg (fun f => (allPairs n).filterMap f)
    (funext fun p => (minByPairAux_eq_foldr p es).symm)

private theorem minByPairAux_spec {n : ℕ} (p : Fin n × Fin n) (es : List (WeightedEdge n ℕ)) :
    (∀ e, minByPairAux p es = some e →
      e ∈ es ∧ canonicalPair e = p ∧ ∀ f ∈ es, canonicalPair f = p → e.weight ≤ f.weight) ∧
    (∀ f ∈ es, canonicalPair f = p → ∃ e, minByPairAux p es = some e) := by
  induction es with
  | nil =>
    refine ⟨fun _ h => by simp [minByPairAux] at h, fun _ hf => by cases hf⟩
  | cons x rest ih =>
    constructor
    · intro e he
      dsimp only [minByPairAux] at he
      split_ifs at he with hpx
      · cases htail : minByPairAux p rest with
        | none =>
          rw [htail] at he
          cases he
          refine ⟨List.mem_cons_self, hpx, fun f hf hfp => ?_⟩
          rcases List.mem_cons.mp hf with rfl | hfr
          · exact le_rfl
          · exfalso; obtain ⟨g, hg⟩ := ih.2 f hfr hfp; simp [htail] at hg
        | some best =>
          rw [htail] at he
          obtain ⟨hb_mem, hb_p, hb_min⟩ := ih.1 best htail
          cases he
          split_ifs with hxw
          · refine ⟨List.mem_cons_self, hpx, fun f hf hfp => ?_⟩
            rcases List.mem_cons.mp hf with rfl | hfr
            · exact le_rfl
            · exact hxw.trans (hb_min f hfr hfp)
          · refine ⟨List.mem_cons_of_mem _ hb_mem, hb_p, fun f hf hfp => ?_⟩
            rcases List.mem_cons.mp hf with rfl | hfr
            · omega
            · exact hb_min f hfr hfp
      · obtain ⟨hm, hp, hmin⟩ := ih.1 e he
        refine ⟨List.mem_cons_of_mem _ hm, hp, fun f hf hfp => ?_⟩
        rcases List.mem_cons.mp hf with rfl | hfr
        · exact absurd hfp hpx
        · exact hmin f hfr hfp
    · intro f hf hfp
      dsimp only [minByPairAux]
      split_ifs with hpx
      · cases htail : minByPairAux p rest with
        | none => exact ⟨x, rfl⟩
        | some best => exact ⟨_, rfl⟩
      · rcases List.mem_cons.mp hf with rfl | hfr
        · exact absurd hfp hpx
        · exact ih.2 f hfr hfp

private theorem dedupSimpleEdges_nodup {n : ℕ} (es : List (WeightedEdge n ℕ)) :
    (dedupSimpleEdges es).Nodup := by
  rw [dedupSimpleEdges_eq_filterMap]
  refine (nodup_allPairs n).filterMap fun a₁ a₂ b ha hb => ?_
  exact ((minByPairAux_spec a₁ es).1 b ha).2.1.symm.trans
    ((minByPairAux_spec a₂ es).1 b hb).2.1

theorem dedupSimpleEdges_subperm {n : ℕ} (es : List (WeightedEdge n ℕ)) :
    (dedupSimpleEdges es).Subperm es := by
  refine List.subperm_of_subset (dedupSimpleEdges_nodup es) fun e he => ?_
  rw [dedupSimpleEdges_eq_filterMap, List.mem_filterMap] at he
  obtain ⟨p, _, hp⟩ := he
  exact ((minByPairAux_spec p es).1 e hp).1

private theorem ne_of_canonicalPair_in_allPairs {n : ℕ} {e : WeightedEdge n ℕ}
    {p : Fin n × Fin n} (hp : p ∈ allPairs n) (hcp : canonicalPair e = p) : e.u ≠ e.v := by
  have hlt := allPairs_lt hp
  intro heq
  dsimp only [canonicalPair] at hcp
  rw [heq] at hcp
  simp only [Nat.lt_irrefl, ↓reduceIte] at hcp
  have h1 : e.v.val = p.1.val := congrArg (fun q : Fin n × Fin n => q.1.val) hcp
  have h2 : e.v.val = p.2.val := congrArg (fun q : Fin n × Fin n => q.2.val) hcp
  omega

theorem dedupSimpleEdges_isSimple {n : ℕ} (es : List (WeightedEdge n ℕ)) :
    IsSimple (edgeEnds (dedupSimpleEdges es)) := by
  rw [isSimple_iff]
  refine ⟨fun i => ?_, fun i₁ i₂ hij => ?_⟩
  · have hmem : (dedupSimpleEdges es)[i.val] ∈
        (allPairs n).filterMap (fun p => minByPairAux p es) := by
      rw [← dedupSimpleEdges_eq_filterMap]
      exact List.getElem_mem i.isLt
    rw [List.mem_filterMap] at hmem
    obtain ⟨p, hp_all, hp⟩ := hmem
    have hcp := ((minByPairAux_spec p es).1 _ hp).2.1
    dsimp only [edgeEnds]
    rw [Sym2.mk_isDiag_iff]
    exact ne_of_canonicalPair_in_allPairs hp_all hcp
  · have hm1 : (dedupSimpleEdges es)[i₁.val] ∈
        (allPairs n).filterMap (fun p => minByPairAux p es) := by
      rw [← dedupSimpleEdges_eq_filterMap]
      exact List.getElem_mem i₁.isLt
    have hm2 : (dedupSimpleEdges es)[i₂.val] ∈
        (allPairs n).filterMap (fun p => minByPairAux p es) := by
      rw [← dedupSimpleEdges_eq_filterMap]
      exact List.getElem_mem i₂.isLt
    rw [List.mem_filterMap] at hm1 hm2
    obtain ⟨p₁, hp1_all, hp1⟩ := hm1
    obtain ⟨p₂, hp2_all, hp2⟩ := hm2
    have hcp1 := ((minByPairAux_spec p₁ es).1 _ hp1).2.1
    have hcp2 := ((minByPairAux_spec p₂ es).1 _ hp2).2.1
    have hne : (dedupSimpleEdges es)[i₁.val].u ≠ (dedupSimpleEdges es)[i₁.val].v :=
      ne_of_canonicalPair_in_allPairs hp1_all hcp1
    have hcp_eq : canonicalPair (dedupSimpleEdges es)[i₁.val] =
        canonicalPair (dedupSimpleEdges es)[i₂.val] := by
      dsimp only [edgeEnds] at hij
      rcases Sym2.eq_iff.mp hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · dsimp only [canonicalPair]; rw [h1, h2]
      · have hne_val : (dedupSimpleEdges es)[i₁.val].u.val ≠
            (dedupSimpleEdges es)[i₁.val].v.val := fun h => hne (Fin.ext h)
        have h1v := congrArg Fin.val h1
        have h2v := congrArg Fin.val h2
        dsimp only [canonicalPair]
        by_cases ha : (dedupSimpleEdges es)[i₁.val].u.val <
            (dedupSimpleEdges es)[i₁.val].v.val
        · have hb : ¬ (dedupSimpleEdges es)[i₂.val].u.val <
              (dedupSimpleEdges es)[i₂.val].v.val := by omega
          simp only [ha, hb, ↓reduceIte]
          exact Prod.ext h1 h2
        · have hb : (dedupSimpleEdges es)[i₂.val].u.val <
              (dedupSimpleEdges es)[i₂.val].v.val := by omega
          simp only [ha, hb, ↓reduceIte]
          exact Prod.ext h2 h1
    have hp_eq : p₁ = p₂ := hcp1.symm.trans (hcp_eq.trans hcp2)
    subst hp_eq
    rw [hp1] at hp2
    exact Fin.ext ((dedupSimpleEdges_nodup es).getElem_inj_iff.mp (Option.some.inj hp2))

theorem simpleGraph_weakSupport {n : ℕ} (es : List (WeightedEdge n ℕ)) :
    ∀ e ∈ es, WeaklySupported (dedupSimpleEdges es) e := by
  intro e he
  dsimp only [WeaklySupported]
  by_cases huv : e.u = e.v
  · rw [huv]; exact (edgePartition _).refl _
  · let p := canonicalPair e
    have hp_all : p ∈ allPairs n := by
      rw [mem_allPairs_iff]
      have hne : e.u.val ≠ e.v.val := fun h => huv (Fin.ext h)
      dsimp only [p, canonicalPair]
      split_ifs with huv_lt
      · exact huv_lt
      · exact Nat.lt_of_le_of_ne (not_lt.mp huv_lt) hne.symm
    obtain ⟨e', he'⟩ := (minByPairAux_spec p es).2 e he rfl
    obtain ⟨_, hcp', hmin'⟩ := (minByPairAux_spec p es).1 e' he'
    have hw' : e'.weight ≤ e.weight := hmin' e he rfl
    have he'_mem : e' ∈ (dedupSimpleEdges es).filter fun f => decide (f.weight ≤ e.weight) := by
      rw [List.mem_filter, decide_eq_true_eq]
      rw [dedupSimpleEdges_eq_filterMap]
      exact ⟨List.mem_filterMap.mpr ⟨p, hp_all, he'⟩, hw'⟩
    have hrel := rel_edgePartitionFrom_of_mem (Partition.discrete n) he'_mem
    have hcp_eq : canonicalPair e' = canonicalPair e := hcp'
    dsimp only [canonicalPair] at hcp_eq
    split_ifs at hcp_eq with h1 h2 <;> simp only [Prod.mk.injEq] at hcp_eq
    · rw [← hcp_eq.1, ← hcp_eq.2]; exact hrel
    · rw [← hcp_eq.2, ← hcp_eq.1]; exact (edgePartition _).symm hrel
    · rw [← hcp_eq.1, ← hcp_eq.2]; exact (edgePartition _).symm hrel
    · rw [← hcp_eq.2, ← hcp_eq.1]; exact hrel

theorem isMinSpanningForest_of_dedupSimpleEdges {n : ℕ} (es F : List (WeightedEdge n ℕ))
    (hF : IsMinSpanningForest (dedupSimpleEdges es) F) :
    IsMinSpanningForest es F :=
  isMinSpanningForest_of_weakSupport es (dedupSimpleEdges es) F
    (dedupSimpleEdges_subperm es) (simpleGraph_weakSupport es) hF

end Cslib.Query.MinimumSpanningForest
