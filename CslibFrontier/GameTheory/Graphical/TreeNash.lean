/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.TreeSide
public import CslibFrontier.GameTheory.Graphical.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Computing Nash equilibria in tree and acyclic graphical games

This module formalizes the two-pass dynamic programming algorithm **`TreeNash`** and its
`τ`-grid approximation **`ApproximateTreeNash`** from [Kearns2007], §7.3 (Figure 7.1, Theorem 7.3,
Lemma 7.4, and the equilibrium correctness/completeness step of Theorem 7.5, pp. 164–168), together
with the forest extension to arbitrary finite acyclic graphs.

## Orientation and subtree semantics

Given a tree `G : SimpleGraph ι` (`hT : G.IsTree`) rooted at `r : ι`, Kearns's convention places `r`
at the bottom and the leaves at the top ([Kearns2007], §7.3, p. 164):
* for `v ≠ r`, `hT.parent r v` is the unique **downstream neighbor** ("child" `W` of `V`);
* `UpstreamNeighbors hT r v = {u : ι // u ≠ r ∧ hT.parent r u = v}` is the set of **upstream
  neighbors** ("parents" `U_1, …, U_k` of `V`);
* `hT.treeSide v (hT.parent r v)` is the upstream vertex set `UP_G(v)` (containing `v` and isolated
  from the rest of `G` once the strategy of `hT.parent r v` is fixed,
  `SimpleGraph.IsTree.eq_of_mem_treeSide_of_adj_notMem`).

## Parameterized two-pass dynamic program

Both exact `TreeNash` and discretized `ApproximateTreeNash` are instances of one parameterized
two-pass recurrence over `(allowed : ∀ i, Set (S i → ℝ))` and additive best-response slack `ε : ℝ`:
* **Downstream pass** (`treePassTable`, `IsTreePassWitness`, `rootPassTable`, `IsRootPassWitness`):
  starting at leaves (where `UpstreamNeighbors` is empty, `treePassTable_of_isEmpty`) and moving
  toward `r` by decreasing `Fintype.card ι - (hT.pathTo r v).length`, vertex `v ≠ r` marks
  `(xw, xv)` valid iff `xw` and `xv` lie in `allowed` and some upstream witness `u` satisfies all
  upstream tables `treePassTable … c.1 xv (u c)` while making `xv` a local `ε`-best response to
  `(xw, u)`.
* **Subtree invariant** (`treePassTable_iff_exists_subtreeEquilibrium`): `treePassTable` holds at
  `v ≠ r` iff `(xw, xv)` extends to a profile in `allowed` that is locally an `ε`-best response at
  every vertex of `hT.treeSide v (hT.parent r v)`.
* **Upstream pass** (`IsTreePassOutput`, `treePassUpstream`): any nondeterministic witness selection
  from `r` upstream produces an `ε`-Nash equilibrium in `allowed`, and conversely every `ε`-Nash
  equilibrium in `allowed` is represented by the tables and witness sets
  (`isTreePassOutput_iff_isApproxNash`).

## Main results

* `Cslib.GameTheory.GraphicalGame.isTreeNashOutput_iff_isMixedNash`,
  `Cslib.GameTheory.GraphicalGame.treeNash_isMixedNash`: **[Kearns2007], Theorem 7.3 (p. 166)** —
  exact `TreeNash` computes a mixed Nash equilibrium of any finite tree graphical game with nonempty
  action sets, and its downstream tables and witness sets represent *all* mixed Nash equilibria.
* `Cslib.GameTheory.GraphicalGame.acyclicNash_isMixedNash`,
  `Cslib.GameTheory.GraphicalGame.isMixedNash_iff_component_treeNash`: extension of `TreeNash` to
  arbitrary finite acyclic graphical games (forests) via connected tree components.
* `Cslib.GameTheory.GraphicalGame.sum_abs_prod_sub_prod_le`: product-distribution `L₁` telescoping
  bound `∑ u, |∏ j, p j (u j) - ∏ j, q j (u j)| ≤ ∑ j, ∑ a, |p j a - q j a|`.
* `Cslib.GameTheory.GraphicalGame.isApproxNash_of_l1_le`,
  `Cslib.GameTheory.GraphicalGame.isApproxNash_nearestGridStrategy`: **[Kearns2007], Lemma 7.4
  (p. 167)** — rounding an exact Nash equilibrium of a degree-`d`, `[0, 1]`-payoff binary graphical
  game to the `L₁`-nearest strategy on the `(τ = 1 / m)`-grid yields a `(d * τ)`-Nash equilibrium.
* `Cslib.GameTheory.GraphicalGame.approxTreeNash_isApproxNash`,
  `Cslib.GameTheory.GraphicalGame.exists_approxTreeNashOutput_of_isMixedNash`: equilibrium
  correctness and `L₁`-closeness completeness step of **[Kearns2007], Theorem 7.5 (pp. 167–168)**
  (formalizing the mathematical equilibrium guarantees of `ApproximateTreeNash`; machine
  running-time bounds remain separate).

## References

* [M. Kearns, *Graphical Games*, Chapter 7 of *Algorithmic Game Theory*][Kearns2007]
-/

public section

open Finset Function Set

/-! ### Rooted upstream decomposition -/

namespace Cslib.GameTheory

/-- Upstream neighbors ("parents" in Kearns's upside-down tree convention, [Kearns2007], §7.3,
p. 164) of vertex `v` when the tree `G` is rooted at `r`: all non-root vertices `u` whose step
toward `r` is `v`. -/
abbrev UpstreamNeighbors {ι : Type*} {G : SimpleGraph ι} (hT : G.IsTree) (r v : ι) : Type _ :=
  {u : ι // u ≠ r ∧ hT.parent r u = v}

/-- Every upstream neighbor `c` of `v` in a tree rooted at `r` has `hT.parent r c.1 = v`. -/
theorem UpstreamNeighbors.parent_eq {ι : Type*} {G : SimpleGraph ι} {hT : G.IsTree} {r v : ι}
    (c : UpstreamNeighbors hT r v) : hT.parent r c.1 = v :=
  c.2.2

private theorem not_mem_treeSide_other {ι : Type*} {G : SimpleGraph ι} {hT : G.IsTree} {u v : ι}
    (h : G.Adj u v) : v ∉ hT.treeSide u v := by
  have hm := hT.self_mem_treeSide_of_adj h.symm
  rwa [hT.treeSide_compl_of_adj h] at hm

private theorem upstream_unique_of_mem_treeSide {ι : Type*} {G : SimpleGraph ι} {hT : G.IsTree}
    {r v : ι} {c c' : UpstreamNeighbors hT r v} {z : ι}
    (hz : z ∈ hT.treeSide c.1 v) (hz' : z ∈ hT.treeSide c'.1 v) : c = c' :=
  by_contra fun hne => Set.disjoint_left.mp
    (hT.disjoint_treeSide_of_adj ((hT.adj_iff_parent r).mpr (Or.inr c.2))
      ((hT.adj_iff_parent r).mpr (Or.inr c'.2)) fun h => hne (Subtype.ext h)) hz hz'

namespace GraphicalGame

section TreePass

variable {ι : Type*} {S : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)]

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)] in
/-- Assemble a neighbor mixed-strategy profile at the root `r` from strategies on
`UpstreamNeighbors hT r r`. -/
def assembleRootNeighbors {G : SimpleGraph ι} (hT : G.IsTree) (r : ι)
    (u : ∀ c : UpstreamNeighbors hT r r, S c.1 → ℝ) :
    ∀ j : G.neighborSet r, S j.1 → ℝ :=
  fun j => u ⟨j.1, ((hT.adj_iff_parent r).mp j.2).resolve_left fun h => h.1 rfl⟩

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)] in
@[simp] theorem assembleRootNeighbors_restrict {G : SimpleGraph ι} (hT : G.IsTree) (r : ι)
    (p : ∀ i, S i → ℝ) :
    assembleRootNeighbors hT r (fun c => p c.1) = fun j : G.neighborSet r => p j.1 := by
  rfl

omit [Fintype ι] [∀ i, Fintype (S i)] in
/-- Assemble a neighbor mixed-strategy profile at a non-root vertex `v ≠ r` from the strategy `xw`
of its unique downstream neighbor `hT.parent r v` and strategies `u` of `UpstreamNeighbors hT r v`.
-/
noncomputable def assembleNeighbors {G : SimpleGraph ι} (hT : G.IsTree) (r : ι) {v : ι}
    (_hv : v ≠ r) (xw : S (hT.parent r v) → ℝ) (u : ∀ c : UpstreamNeighbors hT r v, S c.1 → ℝ) :
    ∀ j : G.neighborSet v, S j.1 → ℝ :=
  fun j =>
    if hj : j.1 = hT.parent r v then
      hj ▸ xw
    else
      u ⟨j.1, ((hT.adj_iff_parent r).mp j.2).resolve_left fun h => hj h.2.symm⟩

omit [Fintype ι] [∀ i, Fintype (S i)] in
@[simp] theorem assembleNeighbors_restrict {G : SimpleGraph ι} (hT : G.IsTree) (r : ι) {v : ι}
    (hv : v ≠ r) (p : ∀ i, S i → ℝ) :
    assembleNeighbors hT r hv (p (hT.parent r v)) (fun c => p c.1) =
      fun j : G.neighborSet v => p j.1 := by
  ext ⟨j, hj⟩ a
  rcases eq_or_ne j (hT.parent r v) with rfl | hjp <;> simp [assembleNeighbors, *]

/-- Downstream dynamic-programming table `T(w, v)` of parameterized `TreeNash` ([Kearns2007],
Figure 7.1 Step (ii), p. 165) passed from non-root vertex `v` to its downstream neighbor
`w = hT.parent r v`. -/
def treePassTable (M : GraphicalGame ι S) (hT : M.graph.IsTree) (r : ι)
    (allowed : ∀ i, Set (S i → ℝ)) (ε : ℝ) (v : ι)
    (xw : S (hT.parent r v) → ℝ) (xv : S v → ℝ) : Prop :=
  if hv : v = r then
    False
  else
    xw ∈ allowed (hT.parent r v) ∧ xv ∈ allowed v ∧
      ∃ u : ∀ c : UpstreamNeighbors hT r v, S c.1 → ℝ,
        (∀ c : UpstreamNeighbors hT r v,
          treePassTable M hT r allowed ε c.1 (UpstreamNeighbors.parent_eq c |>.symm ▸ xv) (u c)) ∧
        M.IsApproxBestResponse ε v xv (assembleNeighbors hT r hv xw u)
termination_by Fintype.card ι - (hT.pathTo r v).length
decreasing_by
  have hlt := (hT.isPath_pathTo r c.1).length_lt
  have hstep := hT.length_pathTo_parent r c.2.1
  rw [c.2.2] at hstep
  omega

/-- Witness predicate for `treePassTable` at `v ≠ r` ([Kearns2007], Figure 7.1 Step (ii)(d)2,
pp. 165–166): `u` belongs to the witness list of `(xw, xv)` iff every upstream table entry
`T(xv, u c)` holds and `xv` is locally an `ε`-best response to `(xw, u)`. -/
@[expose] def IsTreePassWitness (M : GraphicalGame ι S) (hT : M.graph.IsTree) (r : ι)
    (allowed : ∀ i, Set (S i → ℝ)) (ε : ℝ) {v : ι} (hv : v ≠ r)
    (xw : S (hT.parent r v) → ℝ) (xv : S v → ℝ)
    (u : ∀ c : UpstreamNeighbors hT r v, S c.1 → ℝ) : Prop :=
  xw ∈ allowed (hT.parent r v) ∧ xv ∈ allowed v ∧
    (∀ c : UpstreamNeighbors hT r v,
      treePassTable M hT r allowed ε c.1 (UpstreamNeighbors.parent_eq c |>.symm ▸ xv) (u c)) ∧
    M.IsApproxBestResponse ε v xv (assembleNeighbors hT r hv xw u)

theorem treePassTable_iff_exists_witness {M : GraphicalGame ι S} {hT : M.graph.IsTree} {r : ι}
    {allowed : ∀ i, Set (S i → ℝ)} {ε : ℝ} {v : ι} (hv : v ≠ r)
    {xw : S (hT.parent r v) → ℝ} {xv : S v → ℝ} :
    treePassTable M hT r allowed ε v xw xv ↔
      ∃ u, IsTreePassWitness M hT r allowed ε hv xw xv u := by
  rw [treePassTable]
  simp only [hv, ↓reduceDIte, IsTreePassWitness, exists_and_left]

/-- **Leaf base case** ([Kearns2007], Figure 7.1 Step (ii)(c), p. 165): when `v ≠ r` has no upstream
neighbors, `treePassTable` holds iff `xw ∈ allowed (hT.parent r v)`, `xv ∈ allowed v`, and `xv` is
locally an `ε`-best response to `xw`. -/
theorem treePassTable_of_isEmpty {M : GraphicalGame ι S} {hT : M.graph.IsTree} {r : ι}
    {allowed : ∀ i, Set (S i → ℝ)} {ε : ℝ} {v : ι} (hv : v ≠ r)
    [IsEmpty (UpstreamNeighbors hT r v)]
    {xw : S (hT.parent r v) → ℝ} {xv : S v → ℝ} :
    treePassTable M hT r allowed ε v xw xv ↔
      xw ∈ allowed (hT.parent r v) ∧ xv ∈ allowed v ∧
        M.IsApproxBestResponse ε v xv (assembleNeighbors hT r hv xw isEmptyElim) := by
  rw [treePassTable_iff_exists_witness hv]
  exact ⟨fun ⟨u, hxw, hxv, _, hbr⟩ => ⟨hxw, hxv, Subsingleton.elim u isEmptyElim ▸ hbr⟩,
    fun ⟨hxw, hxv, hbr⟩ => ⟨isEmptyElim, hxw, hxv, isEmptyElim, hbr⟩⟩

/-- Witness predicate at the root `r` ([Kearns2007], §7.3, p. 166). -/
@[expose] def IsRootPassWitness (M : GraphicalGame ι S) (hT : M.graph.IsTree) (r : ι)
    (allowed : ∀ i, Set (S i → ℝ)) (ε : ℝ) (xr : S r → ℝ)
    (u : ∀ c : UpstreamNeighbors hT r r, S c.1 → ℝ) : Prop :=
  xr ∈ allowed r ∧
    (∀ c : UpstreamNeighbors hT r r,
      treePassTable M hT r allowed ε c.1 (UpstreamNeighbors.parent_eq c |>.symm ▸ xr) (u c)) ∧
    M.IsApproxBestResponse ε r xr (assembleRootNeighbors hT r u)

/-- One-dimensional root table `T(z)` at the root `r` ([Kearns2007], §7.3, p. 166). -/
@[expose] def rootPassTable (M : GraphicalGame ι S) (hT : M.graph.IsTree) (r : ι)
    (allowed : ∀ i, Set (S i → ℝ)) (ε : ℝ) (xr : S r → ℝ) : Prop :=
  ∃ u, IsRootPassWitness M hT r allowed ε xr u

/-- Nondeterministic upstream-pass output predicate ([Kearns2007], Figure 7.1 Step (iii),
pp. 165–166): `p` is produced by choosing a valid root entry `p r`, a root witness, and valid
witnesses at every non-root vertex `v ≠ r` upstream. -/
@[expose] def IsTreePassOutput (M : GraphicalGame ι S) (hT : M.graph.IsTree) (r : ι)
    (allowed : ∀ i, Set (S i → ℝ)) (ε : ℝ) (p : ∀ i, S i → ℝ) : Prop :=
  IsRootPassWitness M hT r allowed ε (p r) (fun c => p c.1) ∧
    ∀ v (hv : v ≠ r),
      IsTreePassWitness M hT r allowed ε hv (p (hT.parent r v)) (p v) (fun c => p c.1)

/-! ### Subtree equilibrium invariant and master two-pass equivalence -/

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)] in
private theorem eq_of_eq_rec_symm {i j : ι} (h : i = j) (y : ∀ k, S k → ℝ) (x : S j → ℝ)
    (hy : y i = (h.symm ▸ x)) : y j = x := by
  cases h
  exact hy

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)] in
private theorem eq_rec_symm_self {i j : ι} (h : i = j) (y : ∀ k, S k → ℝ) :
    (h.symm ▸ y j : S i → ℝ) = y i := by
  cases h
  rfl

omit [Fintype ι] [DecidableEq ι] in
private theorem upstream_neighbor_iff {G : SimpleGraph ι} (hT : G.IsTree) (r : ι) {v c : ι}
    (hv : v ≠ r) :
    (G.Adj v c ∧ c ≠ hT.parent r v) ↔ (c ≠ r ∧ hT.parent r c = v) :=
  ⟨fun ⟨hadj, hne⟩ => ((hT.adj_iff_parent r).mp hadj).resolve_left fun h => hne h.2.symm,
   fun ⟨hcr, hpar⟩ => ⟨(hT.adj_iff_parent r).mpr (Or.inr ⟨hcr, hpar⟩), fun heq => by
     have h1 := hT.length_pathTo_parent r hv
     have h2 := hT.length_pathTo_parent r hcr
     rw [hpar, heq] at h2; omega⟩⟩

/-- **Subtree table invariant** ([Kearns2007], §7.3, pp. 164–166): for `v ≠ r`, `treePassTable`
accepts `(xw, xv)` if and only if there exists a profile `q` assigning `xw` to `hT.parent r v`, `xv`
to `v`, strategies from `allowed` across `UP_G(v) = hT.treeSide v (hT.parent r v)`, and making every
vertex `z ∈ hT.treeSide v (hT.parent r v)` locally an `ε`-best response to `q`. -/
theorem treePassTable_iff_exists_subtreeEquilibrium {M : GraphicalGame ι S}
    {hT : M.graph.IsTree} {r : ι} {allowed : ∀ i, Set (S i → ℝ)} {ε : ℝ} {v : ι} (hv : v ≠ r)
    {xw : S (hT.parent r v) → ℝ} {xv : S v → ℝ} :
    treePassTable M hT r allowed ε v xw xv ↔
      xw ∈ allowed (hT.parent r v) ∧
        ∃ q : ∀ i, S i → ℝ,
          q (hT.parent r v) = xw ∧
          q v = xv ∧
          (∀ z ∈ hT.treeSide v (hT.parent r v), q z ∈ allowed z) ∧
          (∀ z ∈ hT.treeSide v (hT.parent r v),
            M.IsApproxBestResponse ε z (q z) (fun j => q j.1)) := by
  -- Well-founded induction on `Fintype.card ι - (hT.pathTo r v).length`.
  generalize hn : Fintype.card ι - (hT.pathTo r v).length = n
  induction n using Nat.strong_induction_on generalizing v with
  | ind n ih =>
    rw [treePassTable_iff_exists_witness hv]
    have hadj_vp : M.graph.Adj v (hT.parent r v) := hT.adj_parent r hv
    have hp_notMem : hT.parent r v ∉ hT.treeSide v (hT.parent r v) :=
      not_mem_treeSide_other hadj_vp
    have hlt_up : ∀ c : UpstreamNeighbors hT r v,
        Fintype.card ι - (hT.pathTo r c.1).length < n := fun c => by
      have hlt := (hT.isPath_pathTo r c.1).length_lt
      have hstep := hT.length_pathTo_parent r c.2.1
      rw [c.2.2] at hstep; omega
    have hsub_up : ∀ c : UpstreamNeighbors hT r v,
        hT.treeSide c.1 v ⊆ hT.treeSide v (hT.parent r v) := fun c w hw => by
      rw [hT.treeSide_eq_insert_biUnion hadj_vp]
      exact Set.mem_insert_of_mem v
        (mem_iUnion₂.mpr ⟨c.1, (upstream_neighbor_iff hT r hv).mpr c.2, hw⟩)
    constructor
    · rintro ⟨u, hxw, hxv, hchild, hbr_v⟩
      -- Extract subtree equilibria for each upstream neighbor `c` by IH.
      have hchild_eq : ∀ c : UpstreamNeighbors hT r v,
          ∃ qc : ∀ i, S i → ℝ, qc v = xv ∧ qc c.1 = u c ∧
            (∀ z ∈ hT.treeSide c.1 v, qc z ∈ allowed z) ∧
            (∀ z ∈ hT.treeSide c.1 v, M.IsApproxBestResponse ε z (qc z) (fun j => qc j.1)) := by
        rintro ⟨c, hc_ne, rfl⟩
        exact ((ih _ (hlt_up ⟨c, hc_ne, rfl⟩) hc_ne rfl).mp (hchild ⟨c, hc_ne, rfl⟩)).2
      classical
      choose qc hqc_par hqc_c hqc_allow hqc_br using hchild_eq
      -- Glue `qc` across the disjoint upstream subtrees, placing `xv` at `v` and `xw` elsewhere
      -- when `i = hT.parent r v`.
      let q : ∀ i, S i → ℝ := fun i =>
        if hiv : i = v then hiv ▸ xv
        else if hip : i = hT.parent r v then hip ▸ xw
        else if hex : ∃ c : UpstreamNeighbors hT r v, i ∈ hT.treeSide c.1 v then
          qc (Classical.choose hex) i
        else fun _ => 0
      have hq_p : q (hT.parent r v) = xw := by simp [q, hadj_vp.ne']
      have hq_v : q v = xv := by simp [q]
      have hq_on_child : ∀ (c : UpstreamNeighbors hT r v) {z : ι},
          z ∈ hT.treeSide c.1 v → q z = qc c z := fun c z hz => by
        have hzv : z ≠ v := fun h =>
          not_mem_treeSide_other ((hT.adj_iff_parent r).mpr (Or.inr c.2)).symm (h ▸ hz)
        have hzp : z ≠ hT.parent r v := fun h => hp_notMem (hsub_up c (h ▸ hz))
        have hex : ∃ c' : UpstreamNeighbors hT r v, z ∈ hT.treeSide c'.1 v := ⟨c, hz⟩
        simp only [q, hzv, hzp, hex, ↓reduceDIte]
        rw [upstream_unique_of_mem_treeSide (Classical.choose_spec hex) hz]
      refine ⟨hxw, q, hq_p, hq_v, fun z hz => ?_, fun z hz => ?_⟩
      · rw [hT.treeSide_eq_insert_biUnion hadj_vp] at hz
        rcases mem_insert_iff.mp hz with rfl | hz_union
        · rwa [hq_v]
        · obtain ⟨c₀, hc₀, hzc⟩ := mem_iUnion₂.mp hz_union
          let c : UpstreamNeighbors hT r v := ⟨c₀, (upstream_neighbor_iff hT r hv).mp hc₀⟩
          simpa only [hq_on_child c hzc] using hqc_allow c z hzc
      · rw [hT.treeSide_eq_insert_biUnion hadj_vp] at hz
        rcases mem_insert_iff.mp hz with rfl | hz_union
        · have hnbr : (fun j : M.graph.neighborSet z => q j.1) =
              assembleNeighbors hT r hv xw u := by
            ext ⟨j, hj⟩ a
            rcases eq_or_ne j (hT.parent r z) with rfl | hjp
            · simp [assembleNeighbors, hq_p]
            · simp only [assembleNeighbors, hjp, ↓reduceDIte]
              let c : UpstreamNeighbors hT r z :=
                ⟨j, ((hT.adj_iff_parent r).mp hj).resolve_left fun h => hjp h.2.symm⟩
              rw [hq_on_child c (hT.self_mem_treeSide_of_adj hj.symm), hqc_c c]
          rwa [hq_v, hnbr]
        · obtain ⟨c₀, hc₀, hzc⟩ := mem_iUnion₂.mp hz_union
          let c : UpstreamNeighbors hT r v := ⟨c₀, (upstream_neighbor_iff hT r hv).mp hc₀⟩
          have hnbr : (fun j : M.graph.neighborSet z => q j.1) =
              (fun j : M.graph.neighborSet z => qc c j.1) := by
            ext ⟨j, hj⟩ a
            by_cases hjc : j ∈ hT.treeSide c.1 v
            · rw [hq_on_child c hjc]
            · have hadj_cv' : M.graph.Adj c.1 v := by simpa [c.2.2] using hT.adj_parent r c.2.1
              obtain ⟨_, rfl⟩ := hT.eq_of_mem_treeSide_of_adj_notMem hadj_cv' hzc hjc hj
              rw [hq_v, hqc_par c]
          simpa only [hq_on_child c hzc, hnbr] using hqc_br c z hzc
    · rintro ⟨hxw, q, hq_p, hq_v, hq_allow, hq_br⟩
      have hv_mem : v ∈ hT.treeSide v (hT.parent r v) := hT.self_mem_treeSide_of_adj hadj_vp
      refine ⟨fun c => q c.1, hxw, hq_v ▸ hq_allow v hv_mem, fun c => ?_, ?_⟩
      · have hsub := hsub_up c
        rcases c with ⟨c, hc_ne, rfl⟩
        exact (ih _ (hlt_up ⟨c, hc_ne, rfl⟩) hc_ne rfl).mpr ⟨hq_v ▸ hq_allow _ hv_mem, q, hq_v,
          rfl, fun z hz => hq_allow z (hsub hz), fun z hz => hq_br z (hsub hz)⟩
      · simpa only [← hq_p, assembleNeighbors_restrict, ← hq_v] using hq_br v hv_mem

/-- **Root table characterization** ([Kearns2007], §7.3, p. 166): `rootPassTable` accepts `xr` iff
`xr` extends to an `ε`-Nash equilibrium `q` of `M` with `q r = xr` and `∀ i, q i ∈ allowed i`. -/
theorem rootPassTable_iff_exists_isApproxNash {M : GraphicalGame ι S} {hT : M.graph.IsTree}
    {r : ι} {allowed : ∀ i, Set (S i → ℝ)} {ε : ℝ} {xr : S r → ℝ} :
    rootPassTable M hT r allowed ε xr ↔
      ∃ q : ∀ i, S i → ℝ, q r = xr ∧ (∀ i, q i ∈ allowed i) ∧ M.IsApproxNash ε q := by
  -- Partition `ι \ {r}` into the disjoint subtrees `hT.treeSide c.1 r` over
  -- `c : UpstreamNeighbors hT r r`.
  have hcover : ∀ z : ι, z ≠ r →
      ∃ c : UpstreamNeighbors hT r r, z ∈ hT.treeSide c.1 r := fun z hzr => by
    refine ⟨⟨hT.parent z r, ((hT.adj_iff_parent r).mp (hT.adj_parent z hzr.symm)).resolve_left
      fun h => h.1 rfl⟩, ?_⟩
    simp only [SimpleGraph.IsTree.mem_treeSide]
    have hlen := hT.length_pathTo_parent z hzr.symm
    omega
  constructor
  · rintro ⟨u, hxr, hchild, hbr_r⟩
    have hchild_eq : ∀ c : UpstreamNeighbors hT r r,
        ∃ qc : ∀ i, S i → ℝ,
          qc r = xr ∧
          qc c.1 = u c ∧
          (∀ z ∈ hT.treeSide c.1 r, qc z ∈ allowed z) ∧
          (∀ z ∈ hT.treeSide c.1 r, M.IsApproxBestResponse ε z (qc z) (fun j => qc j.1)) := by
      rintro ⟨c, hc_ne, hc_par⟩
      obtain ⟨_, qc, hqc_p, hqc_c, hqc_allow, hqc_br⟩ :=
        (treePassTable_iff_exists_subtreeEquilibrium hc_ne).mp (hchild ⟨c, hc_ne, hc_par⟩)
      rw [hc_par] at hqc_allow hqc_br
      exact ⟨qc, eq_of_eq_rec_symm hc_par qc xr hqc_p, hqc_c, hqc_allow, hqc_br⟩
    classical
    choose qc hqc_r hqc_c hqc_allow hqc_br using hchild_eq
    let q : ∀ i, S i → ℝ := fun i =>
      if hir : i = r then hir ▸ xr
      else qc (Classical.choose (hcover i hir)) i
    have hq_r : q r = xr := by simp [q]
    have hq_on_child : ∀ (c : UpstreamNeighbors hT r r) {z : ι},
        z ∈ hT.treeSide c.1 r → q z = qc c z := fun c z hz => by
      have hzr : z ≠ r := fun h =>
        not_mem_treeSide_other ((hT.adj_iff_parent r).mpr (Or.inr c.2)).symm (h ▸ hz)
      simp only [q, hzr, ↓reduceDIte]
      rw [upstream_unique_of_mem_treeSide (Classical.choose_spec (hcover z hzr)) hz]
    refine ⟨q, hq_r, fun i => ?_, M.isApproxNash_iff_local.mpr fun z => ?_⟩
    · rcases eq_or_ne i r with rfl | hir
      · rwa [hq_r]
      · have hic := Classical.choose_spec (hcover i hir)
        simpa only [hq_on_child _ hic] using hqc_allow _ i hic
    · rcases eq_or_ne z r with rfl | hzr
      · have hnbr : (fun j : M.graph.neighborSet z => q j.1) = assembleRootNeighbors hT z u := by
          ext ⟨j, hj⟩ a
          unfold assembleRootNeighbors
          let c : UpstreamNeighbors hT z z :=
            ⟨j, ((hT.adj_iff_parent z).mp hj).resolve_left fun h => h.1 rfl⟩
          rw [hq_on_child c (hT.self_mem_treeSide_of_adj hj.symm), hqc_c c]
        rwa [hq_r, hnbr]
      · let c := Classical.choose (hcover z hzr)
        have hzc := Classical.choose_spec (hcover z hzr)
        have hadj_cr : M.graph.Adj c.1 r := ((hT.adj_iff_parent r).mpr (Or.inr c.2)).symm
        have hnbr : (fun j : M.graph.neighborSet z => q j.1) =
            (fun j : M.graph.neighborSet z => qc c j.1) := by
          ext ⟨j, hj⟩ a
          by_cases hjc : j ∈ hT.treeSide c.1 r
          · rw [hq_on_child c hjc]
          · obtain ⟨_, rfl⟩ := hT.eq_of_mem_treeSide_of_adj_notMem hadj_cr hzc hjc hj
            rw [hq_r, hqc_r c]
        simpa only [hq_on_child c hzc, hnbr] using hqc_br c z hzc
  · rintro ⟨q, rfl, hq_allow, hq_nash⟩
    have hloc := M.isApproxNash_iff_local.mp hq_nash
    refine ⟨fun c => q c.1, hq_allow r, fun ⟨c, hc_ne, hc_par⟩ => ?_, ?_⟩
    · rw [eq_rec_symm_self hc_par q]
      exact (treePassTable_iff_exists_subtreeEquilibrium hc_ne).mpr
        ⟨hq_allow _, q, rfl, rfl, fun z _ => hq_allow z, fun z _ => hloc z⟩
    · simpa only [assembleRootNeighbors_restrict] using hloc r

/-- **Master two-pass equivalence**: a strategy profile `p` is produced by a nondeterministic
upstream pass through `treePassTable` and `rootPassTable` if and only if `∀ i, p i ∈ allowed i`
and `M.IsApproxNash ε p`. -/
theorem isTreePassOutput_iff_isApproxNash {M : GraphicalGame ι S} {hT : M.graph.IsTree}
    {r : ι} {allowed : ∀ i, Set (S i → ℝ)} {ε : ℝ} {p : ∀ i, S i → ℝ} :
    IsTreePassOutput M hT r allowed ε p ↔ (∀ i, p i ∈ allowed i) ∧ M.IsApproxNash ε p := by
  rw [M.isApproxNash_iff_local]
  constructor
  · rintro ⟨⟨hpr, _, hbr_r⟩, hv_all⟩
    refine ⟨fun i => if hir : i = r then hir ▸ hpr else (hv_all i hir).2.1, fun i => ?_⟩
    rcases eq_or_ne i r with rfl | hir
    · simpa only [assembleRootNeighbors_restrict] using hbr_r
    · simpa only [assembleNeighbors_restrict] using (hv_all i hir).2.2.2
  · rintro ⟨hp_allow, hp_loc⟩
    have htab : ∀ (v : ι) (c : UpstreamNeighbors hT r v),
        treePassTable M hT r allowed ε c.1 (c.parent_eq.symm ▸ p v) (p c.1) := by
      rintro v ⟨c, hc_ne, hc_par⟩
      rw [eq_rec_symm_self hc_par p]
      exact (treePassTable_iff_exists_subtreeEquilibrium hc_ne).mpr
        ⟨hp_allow _, p, rfl, rfl, fun z _ => hp_allow z, fun z _ => hp_loc z⟩
    refine ⟨⟨hp_allow r, htab r, ?_⟩, fun v hv => ⟨hp_allow _, hp_allow v, htab v, ?_⟩⟩
    · simpa only [assembleRootNeighbors_restrict] using hp_loc r
    · simpa only [assembleNeighbors_restrict] using hp_loc v

/-! ### Constructive upstream pass -/

private structure NodeChoice (M : GraphicalGame ι S) (hT : M.graph.IsTree) (r : ι)
    (allowed : ∀ i, Set (S i → ℝ)) (ε : ℝ) (i : ι) where
  val : S i → ℝ
  witness : ∀ c : UpstreamNeighbors hT r i, S c.1 → ℝ
  val_mem : val ∈ allowed i
  valid : ∀ c : UpstreamNeighbors hT r i,
    treePassTable M hT r allowed ε c.1 (UpstreamNeighbors.parent_eq c |>.symm ▸ val) (witness c)

private def NodeChoice.ofEq {M : GraphicalGame ι S} {hT : M.graph.IsTree} {r : ι}
    {allowed : ∀ i, Set (S i → ℝ)} {ε : ℝ} {i j : ι} (h : i = j)
    (nc : NodeChoice M hT r allowed ε j) : NodeChoice M hT r allowed ε i :=
  h ▸ nc

@[simp] private theorem NodeChoice.ofEq_rfl {M : GraphicalGame ι S} {hT : M.graph.IsTree} {r : ι}
    {allowed : ∀ i, Set (S i → ℝ)} {ε : ℝ} {i : ι} (nc : NodeChoice M hT r allowed ε i) :
    NodeChoice.ofEq rfl nc = nc := rfl

private noncomputable def treePassNode {M : GraphicalGame ι S} (hT : M.graph.IsTree) {r : ι}
    {allowed : ∀ i, Set (S i → ℝ)} {ε : ℝ} {xr : S r → ℝ}
    (hroot : rootPassTable M hT r allowed ε xr) (i : ι) :
    NodeChoice M hT r allowed ε i :=
  if hi : i = r then
    let hex_r : ∃ u, IsRootPassWitness M hT r allowed ε xr u := hroot
    NodeChoice.ofEq hi
      ⟨xr, Classical.choose hex_r, (Classical.choose_spec hex_r).1,
        (Classical.choose_spec hex_r).2.1⟩
  else
    let parChoice := treePassNode hT hroot (hT.parent r i)
    let ci : UpstreamNeighbors hT r (hT.parent r i) := ⟨i, hi, rfl⟩
    let xi : S i → ℝ := parChoice.witness ci
    have htab : treePassTable M hT r allowed ε i parChoice.val xi := parChoice.valid ci
    let hex := (treePassTable_iff_exists_witness hi).mp htab
    ⟨xi, Classical.choose hex, (Classical.choose_spec hex).2.1,
      (Classical.choose_spec hex).2.2.1⟩
termination_by (hT.pathTo r i).length
decreasing_by
  have hstep := hT.length_pathTo_parent r hi
  omega

/-- Constructive upstream pass ([Kearns2007], Figure 7.1 Step (iii), p. 165): given a valid root
entry `xr` (`rootPassTable M hT r allowed ε xr`), recursively assigns strategies from `r` to the
leaves using chosen witnesses at each vertex. -/
noncomputable def treePassUpstream {M : GraphicalGame ι S} (hT : M.graph.IsTree) {r : ι}
    {allowed : ∀ i, Set (S i → ℝ)} {ε : ℝ} {xr : S r → ℝ}
    (hroot : rootPassTable M hT r allowed ε xr) (i : ι) : S i → ℝ :=
  (treePassNode hT hroot i).val

@[simp] theorem treePassUpstream_root {M : GraphicalGame ι S} (hT : M.graph.IsTree) {r : ι}
    {allowed : ∀ i, Set (S i → ℝ)} {ε : ℝ} {xr : S r → ℝ}
    (hroot : rootPassTable M hT r allowed ε xr) :
    treePassUpstream hT hroot r = xr := by
  rw [treePassUpstream, treePassNode]
  simp

theorem isTreePassOutput_treePassUpstream {M : GraphicalGame ι S} (hT : M.graph.IsTree) {r : ι}
    {allowed : ∀ i, Set (S i → ℝ)} {ε : ℝ} {xr : S r → ℝ}
    (hroot : rootPassTable M hT r allowed ε xr) :
    IsTreePassOutput M hT r allowed ε (treePassUpstream hT hroot) := by
  have hwit_fun : ∀ i : ι,
      (fun c : UpstreamNeighbors hT r i => treePassUpstream hT hroot c.1) =
        (treePassNode hT hroot i).witness := fun i => funext fun ⟨c, hc_ne, hc_par⟩ => by
    subst hc_par
    rw [treePassUpstream, treePassNode]
    simp only [hc_ne, ↓reduceDIte]
  refine ⟨?_, fun v hv => ?_⟩
  · simpa only [treePassUpstream_root, hwit_fun r, treePassNode, ↓reduceDIte, NodeChoice.ofEq_rfl]
      using Classical.choose_spec hroot
  · rw [hwit_fun v]
    let par := treePassNode hT hroot (hT.parent r v)
    change IsTreePassWitness M hT r allowed ε hv par.val (treePassNode hT hroot v).val
      (treePassNode hT hroot v).witness
    rw [treePassNode]
    simp only [hv, ↓reduceDIte]
    exact Classical.choose_spec ((treePassTable_iff_exists_witness hv).mp (par.valid ⟨v, hv, rfl⟩))

theorem treePassUpstream_isApproxNash {M : GraphicalGame ι S} (hT : M.graph.IsTree) {r : ι}
    {allowed : ∀ i, Set (S i → ℝ)} {ε : ℝ} {xr : S r → ℝ}
    (hroot : rootPassTable M hT r allowed ε xr) :
    (∀ i, treePassUpstream hT hroot i ∈ allowed i) ∧
      M.IsApproxNash ε (treePassUpstream hT hroot) :=
  isTreePassOutput_iff_isApproxNash.mp (isTreePassOutput_treePassUpstream hT hroot)

/-! ### Exact `TreeNash` on trees ([Kearns2007], Theorem 7.3, p. 166) -/

/-- Exact root table `T(z)` of algorithm `TreeNash` ([Kearns2007], §7.3, p. 166). -/
@[expose] def treeNashRootTable (M : GraphicalGame ι S) (hT : M.graph.IsTree) (r : ι)
    (xr : S r → ℝ) : Prop :=
  rootPassTable M hT r (fun i => {x : S i → ℝ | IsMixedStrategy x}) 0 xr

/-- Nondeterministic output predicate of exact `TreeNash` ([Kearns2007], Theorem 7.3, p. 166). -/
@[expose] def IsTreeNashOutput (M : GraphicalGame ι S) (hT : M.graph.IsTree) (r : ι)
    (p : ∀ i, S i → ℝ) : Prop :=
  IsTreePassOutput M hT r (fun i => {x : S i → ℝ | IsMixedStrategy x}) 0 p

/-- **`TreeNash` completeness** ([Kearns2007], Theorem 7.3, second sentence, p. 166): the downstream
tables and witness sets of `TreeNash` represent *all* mixed Nash equilibria of `(G, M)`. -/
theorem isTreeNashOutput_iff_isMixedNash {M : GraphicalGame ι S} (hT : M.graph.IsTree) (r : ι)
    {p : ∀ i, S i → ℝ} :
    M.IsTreeNashOutput hT r p ↔ M.toCostGame.IsMixedNash p := by
  rw [IsTreeNashOutput, isTreePassOutput_iff_isApproxNash, M.isApproxNash_zero_iff]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- When every player has a nonempty finite action set, the exact root table `treeNashRootTable` is
nonempty ([Kearns2007], §7.3, p. 166). -/
theorem exists_treeNashRootTable (M : GraphicalGame ι S) (hT : M.graph.IsTree) (r : ι)
    [∀ i, Nonempty (S i)] :
    ∃ xr, M.treeNashRootTable hT r xr := by
  obtain ⟨p, hp⟩ := M.toCostGame.exists_isMixedNash
  exact ⟨p r, rootPassTable_iff_exists_isApproxNash.mpr
    ⟨p, rfl, hp.1, M.isApproxNash_zero_iff.mpr hp⟩⟩

/-- Algorithm **`TreeNash`** ([Kearns2007], Figure 7.1 & Theorem 7.3, pp. 165–166): computes an
exact mixed Nash equilibrium of a finite tree graphical game by running the downstream table pass to
root `r` followed by the upstream witness pass. -/
noncomputable def treeNash (M : GraphicalGame ι S) (hT : M.graph.IsTree) (r : ι)
    [∀ i, Nonempty (S i)] : ∀ i, S i → ℝ :=
  treePassUpstream hT (Classical.choose_spec (M.exists_treeNashRootTable hT r))

/-- **`TreeNash` soundness** ([Kearns2007], Theorem 7.3, first sentence, p. 166): `M.treeNash hT r`
is a mixed Nash equilibrium of `(G, M)` (and is produced by `TreeNash`'s tables and witnesses). -/
theorem treeNash_isTreeNashOutput (M : GraphicalGame ι S) (hT : M.graph.IsTree) (r : ι)
    [∀ i, Nonempty (S i)] :
    M.IsTreeNashOutput hT r (M.treeNash hT r) :=
  isTreePassOutput_treePassUpstream hT (Classical.choose_spec (M.exists_treeNashRootTable hT r))

/-- **`TreeNash` soundness** ([Kearns2007], Theorem 7.3, p. 166): `M.treeNash hT r` is an exact
mixed Nash equilibrium of `M.toCostGame`. -/
theorem treeNash_isMixedNash (M : GraphicalGame ι S) (hT : M.graph.IsTree) (r : ι)
    [∀ i, Nonempty (S i)] :
    M.toCostGame.IsMixedNash (M.treeNash hT r) :=
  (M.isTreeNashOutput_iff_isMixedNash hT r).mp (M.treeNash_isTreeNashOutput hT r)

/-! ### Forest extension: acyclic graphical games (`M.graph.IsAcyclic`) -/

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)] in
/-- Restrict a graphical game `M` to an adjacency-closed set of players `U : Set ι` (such as a
connected component). -/
def induceSubgame (M : GraphicalGame ι S) (U : Set ι)
    (hclosed : ∀ ⦃i j : ι⦄, i ∈ U → M.graph.Adj i j → j ∈ U) :
    GraphicalGame U (fun i : U => S i.1) where
  graph := M.graph.induce U
  localPayoff i u := M.localPayoff i.1 fun j =>
    u ⟨⟨j.1, j.2.elim (fun h => h.symm ▸ i.2) (fun hadj => hclosed i.2 hadj)⟩,
      j.2.imp Subtype.ext id⟩

private theorem localDeviationPayoff_induceSubgame (M : GraphicalGame ι S) (U : Set ι)
    [Fintype U] (hclosed : ∀ ⦃i j : ι⦄, i ∈ U → M.graph.Adj i j → j ∈ U)
    (i : U) (a : S i.1) (p : ∀ k, S k → ℝ) :
    (M.induceSubgame U hclosed).localDeviationPayoff i a (fun j => p j.1.1) =
      M.localDeviationPayoff i.1 a (fun j => p j.1) := by
  classical
  rw [localDeviationPayoff_def, localDeviationPayoff_def]
  let e : (M.induceSubgame U hclosed).graph.neighborSet i ≃ M.graph.neighborSet i.1 :=
    ⟨fun j => ⟨j.1.1, j.2⟩, fun j => ⟨⟨j.1, hclosed i.2 j.2⟩, j.2⟩, fun _ => rfl, fun _ => rfl⟩
  let ePi := Equiv.piCongrLeft' (fun j => S j.1.1) e
  refine Fintype.sum_equiv ePi _ _ fun u => congrArg₂ (· * ·)
    (Fintype.prod_equiv e _ _ fun j => by simp [ePi, e]) ?_
  rw [localNeighborPayoff_def, localNeighborPayoff_def]
  refine congrArg (M.localPayoff i.1) (funext fun ⟨k, hk⟩ => ?_)
  by_cases hki : k = i.1
  · simp [hki]
  · have hne : (⟨k, hclosed i.2 (hk.resolve_left hki)⟩ : U) ≠ i :=
      fun h => hki (congrArg Subtype.val h)
    simp only [hki, hne, ↓reduceDIte]; rfl

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)] in
/-- Restriction of a graphical game `M` to a connected component `C : M.graph.ConnectedComponent`.
-/
noncomputable def componentGame (M : GraphicalGame ι S) (C : M.graph.ConnectedComponent) :
    GraphicalGame C.supp (fun i : C.supp => S i.1) :=
  M.induceSubgame C.supp fun _ _ hi hadj =>
    (SimpleGraph.ConnectedComponent.mem_supp_iff C _).mpr
      ((SimpleGraph.ConnectedComponent.mem_supp_iff C _).mp hi ▸
        SimpleGraph.ConnectedComponent.eq.mpr hadj.symm.reachable)

omit [Fintype ι] [DecidableEq ι] [∀ i, Fintype (S i)] in
/-- When `M.graph` is acyclic, every connected component induces a tree. -/
theorem isTree_componentGame {M : GraphicalGame ι S} (hA : M.graph.IsAcyclic)
    (C : M.graph.ConnectedComponent) :
    (M.componentGame C).graph.IsTree :=
  ⟨C.connected_toSimpleGraph, hA.induce C.supp⟩

/-- **Forest decomposition of `ε`-Nash equilibria**: a profile `p` is an `ε`-Nash equilibrium of `M`
if and only if its restriction to every connected component `C` of `M.graph` is an `ε`-Nash
equilibrium of `M.componentGame C`. -/
theorem isApproxNash_iff_forall_componentGame {M : GraphicalGame ι S} {ε : ℝ}
    {p : ∀ i, S i → ℝ} :
    M.IsApproxNash ε p ↔
      ∀ C : M.graph.ConnectedComponent, by
        classical
        exact (M.componentGame C).IsApproxNash ε (fun i : C.supp => p i.1) := by
  classical
  simp only [isApproxNash_iff_local, IsApproxBestResponse]
  have hpay : ∀ (C : M.graph.ConnectedComponent) (i : C.supp) b,
      (M.componentGame C).localDeviationPayoff i b (fun j => p j.1.1) =
        M.localDeviationPayoff i.1 b (fun j => p j.1) :=
    fun C i b => M.localDeviationPayoff_induceSubgame C.supp _ i b p
  refine ⟨fun h C i => by simpa only [hpay] using h i.1, fun h i => ?_⟩
  let C := M.graph.connectedComponentMk i
  have hi : i ∈ C.supp := (SimpleGraph.ConnectedComponent.mem_supp_iff C i).mpr rfl
  simpa only [hpay C ⟨i, hi⟩] using h C ⟨i, hi⟩

/-- On an acyclic graphical game `M` (`hA : M.graph.IsAcyclic`), running `TreeNash` independently on
each connected tree component characterizes *all* mixed Nash equilibria of `M`. -/
theorem isMixedNash_iff_component_treeNash {M : GraphicalGame ι S} (hA : M.graph.IsAcyclic)
    (rootOf : ∀ C : M.graph.ConnectedComponent, C.supp) {p : ∀ i, S i → ℝ} :
    M.toCostGame.IsMixedNash p ↔
      ∀ C : M.graph.ConnectedComponent, by
        classical
        exact (M.componentGame C).IsTreeNashOutput (M.isTree_componentGame hA C) (rootOf C)
          (fun i : C.supp => p i.1) := by
  classical
  rw [← M.isApproxNash_zero_iff, M.isApproxNash_iff_forall_componentGame]
  refine forall_congr' fun C => ?_
  rw [(M.componentGame C).isApproxNash_zero_iff,
    (M.componentGame C).isTreeNashOutput_iff_isMixedNash (M.isTree_componentGame hA C) (rootOf C)]

/-- Two-pass **`TreeNash` on acyclic graphical games (forests)**: runs `treeNash` independently on
every connected tree component of `M.graph`. -/
noncomputable def acyclicNash (M : GraphicalGame ι S) (hA : M.graph.IsAcyclic)
    [∀ i, Nonempty (S i)] : ∀ i, S i → ℝ := by
  classical
  exact fun i =>
    let C := M.graph.connectedComponentMk i
    let rC : C.supp := ⟨C.nonempty_supp.some, C.nonempty_supp.some_mem⟩
    (M.componentGame C).treeNash (M.isTree_componentGame hA C) rC
      ⟨i, (SimpleGraph.ConnectedComponent.mem_supp_iff C i).mpr rfl⟩

/-- **Soundness of `acyclicNash`**: on any finite acyclic graphical game with nonempty action sets,
`M.acyclicNash hA` is an exact mixed Nash equilibrium of `M.toCostGame`. -/
theorem acyclicNash_isMixedNash (M : GraphicalGame ι S) (hA : M.graph.IsAcyclic)
    [∀ i, Nonempty (S i)] :
    M.toCostGame.IsMixedNash (M.acyclicNash hA) := by
  classical
  let rootOf : ∀ C : M.graph.ConnectedComponent, C.supp :=
    fun C => ⟨C.nonempty_supp.some, C.nonempty_supp.some_mem⟩
  rw [M.isMixedNash_iff_component_treeNash hA rootOf]
  intro C
  convert (M.componentGame C).treeNash_isTreeNashOutput (M.isTree_componentGame hA C) (rootOf C)
    using 1
  ext ⟨i, hi⟩ a
  obtain rfl := (SimpleGraph.ConnectedComponent.mem_supp_iff C i).mp hi
  rfl

end TreePass

/-! ### `L₁` product perturbation and `τ`-grid rounding ([Kearns2007], Lemma 7.4, p. 167) -/

section ApproxGrid

/-- **Product-distribution `L₁` telescoping bound**: the `L₁` distance between two finite product
probability distributions is bounded by the sum of the coordinatewise `L₁` distances. -/
theorem sum_abs_prod_sub_prod_le.{u₁, u₂} {α : Type u₁} [Fintype α] [DecidableEq α]
    {T : α → Type u₂} [∀ j : α, Fintype (T j)]
    {p q : ∀ j, T j → ℝ}
    (hp_nonneg : ∀ j a, 0 ≤ p j a) (hp_sum : ∀ j, ∑ a, p j a = 1)
    (hq_nonneg : ∀ j a, 0 ≤ q j a) (hq_sum : ∀ j, ∑ a, q j a = 1) :
    ∑ u : (∀ j : α, T j), |∏ j : α, p j (u j) - ∏ j : α, q j (u j)| ≤
      ∑ j : α, ∑ a : T j, |p j a - q j a| := by
  -- Induction on `n = Fintype.card α`.
  generalize hcard : Fintype.card α = n
  induction n generalizing α with
  | zero =>
    have : IsEmpty α := Fintype.card_eq_zero_iff.mp hcard
    simp
  | succ n ih =>
    obtain ⟨j₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card α)
    let α' := {j : α // j ≠ j₀}
    have hcard' : Fintype.card α' = n := by
      have hc := Fintype.card_subtype_compl (fun j : α => j = j₀)
      rw [Fintype.card_subtype_eq] at hc
      dsimp only [α', Ne] at hc ⊢
      omega
    have herase : univ.erase j₀ = univ.filter (fun j : α => j ≠ j₀) := Finset.ext fun _ => by simp
    let e := (Equiv.piSplitAt j₀ T).symm
    have hprod_split : ∀ (r : ∀ j, T j → ℝ) (a : T j₀) (v : ∀ j : α', T j.1),
        ∏ j : α, r j (e (a, v) j) = r j₀ a * ∏ j : α', r j.1 (v j) := fun r a v => by
      have he_j0 : e (a, v) j₀ = a := by simp [e]
      rw [← Finset.mul_prod_erase univ (fun j => r j (e (a, v) j)) (mem_univ j₀),
        he_j0, herase, Finset.prod_subtype _ (fun _ => mem_filter_univ _)]
      exact congrArg _ (prod_congr rfl fun ⟨j, hj⟩ _ => by simp [e, hj])
    have hrest_sum : ∑ v : (∀ j : α', T j.1), ∏ j : α', p j.1 (v j) = 1 := by
      rw [← Fintype.prod_sum (fun j : α' => p j.1)]
      exact prod_eq_one fun j _ => hp_sum j.1
    have hrest_nn : ∀ v : (∀ j : α', T j.1), 0 ≤ ∏ j : α', p j.1 (v j) :=
      fun v => prod_nonneg fun j _ => hp_nonneg j.1 (v j)
    rw [← Fintype.sum_equiv e _
      (fun u => |∏ j : α, p j (u j) - ∏ j : α, q j (u j)|) (fun _ => rfl),
      Fintype.sum_prod_type]
    calc ∑ a : T j₀, ∑ v : (∀ j : α', T j.1),
          |∏ j : α, p j (e (a, v) j) - ∏ j : α, q j (e (a, v) j)|
        ≤ ∑ a : T j₀, ∑ v : (∀ j : α', T j.1),
            (|p j₀ a - q j₀ a| * (∏ j : α', p j.1 (v j)) +
              q j₀ a * |∏ j : α', p j.1 (v j) - ∏ j : α', q j.1 (v j)|) := by
          refine sum_le_sum fun a _ => sum_le_sum fun v _ => ?_
          have hlin : p j₀ a * (∏ j : α', p j.1 (v j)) - q j₀ a * (∏ j : α', q j.1 (v j)) =
              (p j₀ a - q j₀ a) * (∏ j : α', p j.1 (v j)) +
                q j₀ a * ((∏ j : α', p j.1 (v j)) - (∏ j : α', q j.1 (v j))) := by ring
          rw [hprod_split p a v, hprod_split q a v, hlin]
          exact (abs_add_le _ _).trans <| by
            rw [abs_mul, abs_mul, abs_of_nonneg (hrest_nn v), abs_of_nonneg (hq_nonneg j₀ a)]
      _ = (∑ a : T j₀, |p j₀ a - q j₀ a|) * (∑ v : (∀ j : α', T j.1), ∏ j : α', p j.1 (v j)) +
          (∑ a : T j₀, q j₀ a) *
            (∑ v : (∀ j : α', T j.1), |∏ j : α', p j.1 (v j) - ∏ j : α', q j.1 (v j)|) := by
          simp only [sum_add_distrib, ← mul_sum, ← sum_mul]
      _ ≤ ∑ a : T j₀, |p j₀ a - q j₀ a| + ∑ j : α', ∑ a : T j.1, |p j.1 a - q j.1 a| := by
          rw [hrest_sum, hq_sum j₀, mul_one, one_mul]
          linarith [ih (T := fun j => T j.1) (p := fun j => p j.1) (q := fun j => q j.1)
            (fun j => hp_nonneg j.1) (fun j => hp_sum j.1)
            (fun j => hq_nonneg j.1) (fun j => hq_sum j.1) hcard']
      _ = ∑ j : α, ∑ a : T j, |p j a - q j a| := by
          rw [← Finset.add_sum_erase univ (fun j => ∑ a : T j, |p j a - q j a|) (mem_univ j₀),
            herase, Finset.sum_subtype _ (fun _ => mem_filter_univ _)]

/-- Expectation difference of a `[0, 1]`-valued function against two probability distributions is
at most half their `L₁` distance (i.e., their total variation distance). -/
private theorem sum_sub_mul_le_half_sum_abs {Ω : Type*} [Fintype Ω] {P Q f : Ω → ℝ}
    (hP : ∑ ω, P ω = 1) (hQ : ∑ ω, Q ω = 1) (hf : ∀ ω, 0 ≤ f ω ∧ f ω ≤ 1) :
    ∑ ω, (Q ω - P ω) * f ω ≤ (1 / 2 : ℝ) * ∑ ω, |Q ω - P ω| := by
  have hshift : ∑ ω, (Q ω - P ω) * f ω = ∑ ω, (Q ω - P ω) * (f ω - 1 / 2) := by
    have : ∑ ω, ((Q ω - P ω) * f ω - (Q ω - P ω) * (f ω - 1 / 2)) =
        ∑ ω, (Q ω - P ω) * (1 / 2 : ℝ) := sum_congr rfl fun _ _ => by ring
    rw [sum_sub_distrib, ← sum_mul, sum_sub_distrib, hQ, hP, sub_self, zero_mul] at this
    linarith
  rw [hshift]
  calc ∑ ω, (Q ω - P ω) * (f ω - 1 / 2)
      ≤ ∑ ω, |Q ω - P ω| * (1 / 2) := sum_le_sum fun ω _ => (le_abs_self _).trans <| by
        obtain ⟨hf0, hf1⟩ := hf ω
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_nonneg _)
    _ = (1 / 2 : ℝ) * ∑ ω, |Q ω - P ω| := by rw [← sum_mul, mul_comm]

/-- **General `L₁` Nash perturbation lemma** ([Kearns2007], Lemma 7.4 over arbitrary finite action
sets, p. 167): if `M` has `[0, 1]` payoffs and maximum degree at most `d`, `p` is an exact mixed
Nash equilibrium of `M`, and `q` is a mixed strategy profile with `∑ a, |p i a - q i a| ≤ τ` and
support inclusion `0 < q i a → 0 < p i a` for every player `i`, then `q` is a `(d * τ)`-Nash
equilibrium of `M`. -/
theorem isApproxNash_of_l1_le {ι : Type*} {S : ι → Type*} [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (S i)] (M : GraphicalGame ι S) [DecidableRel M.graph.Adj]
    {d : ℕ} {τ : ℝ} {p q : ∀ i, S i → ℝ}
    (hpay : ∀ i u, 0 ≤ M.localPayoff i u ∧ M.localPayoff i u ≤ 1)
    (hdeg : ∀ i, M.graph.degree i ≤ d)
    (hp : M.toCostGame.IsMixedNash p)
    (hq : ∀ i, IsMixedStrategy (q i))
    (hl1 : ∀ i, ∑ a : S i, |p i a - q i a| ≤ τ)
    (hsupp : ∀ i a, 0 < q i a → 0 < p i a) :
    M.IsApproxNash ((d : ℝ) * τ) q := by
  refine ⟨hq, fun i a => ?_⟩
  -- Bound the product distribution `L₁` distance on `M.graph.neighborSet i` by `d * τ`.
  let P_nbr : (∀ j : M.graph.neighborSet i, S j.1) → ℝ := fun u => ∏ j, p j.1 (u j)
  let Q_nbr : (∀ j : M.graph.neighborSet i, S j.1) → ℝ := fun u => ∏ j, q j.1 (u j)
  have hP_sum : ∑ u, P_nbr u = 1 := by
    rw [← Fintype.prod_sum (fun j : M.graph.neighborSet i => p j.1)]
    exact prod_eq_one fun j _ => (hp.1 j.1).sum_eq_one
  have hQ_sum : ∑ u, Q_nbr u = 1 := by
    rw [← Fintype.prod_sum (fun j : M.graph.neighborSet i => q j.1)]
    exact prod_eq_one fun j _ => (hq j.1).sum_eq_one
  have hTV_le : ∑ u, |Q_nbr u - P_nbr u| ≤ (d : ℝ) * τ := by
    rw [sum_congr rfl fun u _ => abs_sub_comm _ _]
    calc ∑ u, |P_nbr u - Q_nbr u|
        ≤ ∑ j : M.graph.neighborSet i, ∑ c : S j.1, |p j.1 c - q j.1 c| :=
          sum_abs_prod_sub_prod_le (fun j => (hp.1 j.1).nonneg) (fun j => (hp.1 j.1).sum_eq_one)
            (fun j => (hq j.1).nonneg) (fun j => (hq j.1).sum_eq_one)
      _ ≤ ∑ _j : M.graph.neighborSet i, τ := sum_le_sum fun j _ => hl1 j.1
      _ = (Fintype.card (M.graph.neighborSet i) : ℝ) * τ := by
          rw [sum_const, card_univ, nsmul_eq_mul]
      _ ≤ (d : ℝ) * τ := mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr (M.graph.card_neighborSet_eq_degree i ▸ hdeg i))
          ((sum_nonneg fun _ _ => abs_nonneg _).trans (hl1 i))
  -- Deviation payoff change from `p` to `q` for any pure strategy `c : S i`.
  have hdev_dir : ∀ {A B : _ → ℝ} (c : S i), ∑ u, A u = 1 → ∑ u, B u = 1 →
      ∑ u, |B u - A u| ≤ (d : ℝ) * τ →
      ∑ u, B u * M.localNeighborPayoff i c u - ∑ u, A u * M.localNeighborPayoff i c u ≤
        (1 / 2 : ℝ) * ((d : ℝ) * τ) := fun {A B} c hA hB hTV => by
    rw [← sum_sub_distrib, sum_congr rfl fun u _ => (sub_mul ..).symm]
    exact (sum_sub_mul_le_half_sum_abs hA hB
      (fun u => localNeighborPayoff_def M i c u ▸ hpay i _)).trans
      (mul_le_mul_of_nonneg_left hTV (by norm_num))
  have hdev_diff : ∀ c : S i,
      M.deviationPayoff q i c - M.deviationPayoff p i c ≤ (1 / 2 : ℝ) * ((d : ℝ) * τ) ∧
      M.deviationPayoff p i c - M.deviationPayoff q i c ≤ (1 / 2 : ℝ) * ((d : ℝ) * τ) := fun c => by
    rw [M.deviationPayoff_eq_localDeviationPayoff (fun k _ => (hq k).sum_eq_one) c,
      M.deviationPayoff_eq_localDeviationPayoff (fun k _ => (hp.1 k).sum_eq_one) c,
      M.localDeviationPayoff_def, M.localDeviationPayoff_def]
    exact ⟨hdev_dir c hP_sum hQ_sum hTV_le,
      hdev_dir c hQ_sum hP_sum (by simpa only [abs_sub_comm] using hTV_le)⟩
  -- For every `b` with `0 < q i b`, `0 < p i b`, so `b` attains `M.expectedPayoff p i` at `p`.
  have hpointwise : ∀ b : S i,
      q i b * M.deviationPayoff q i a ≤
        q i b * (M.deviationPayoff q i b + (d : ℝ) * τ) := fun b => by
    rcases eq_or_lt_of_le ((hq i).nonneg b) with hqb0 | hqb_pos
    · rw [← hqb0, zero_mul, zero_mul]
    · have hcost_eq := hp.deviationCost_eq_of_pos i (hsupp i b hqb_pos)
      have hcost_le := hp.2 i a
      simp only [toCostGame_deviationCost, toCostGame_expectedCost] at hcost_eq hcost_le
      exact mul_le_mul_of_nonneg_left (by linarith [(hdev_diff a).1, (hdev_diff b).2]) hqb_pos.le
  calc M.deviationPayoff q i a
      = ∑ b : S i, q i b * M.deviationPayoff q i a := by
        rw [← sum_mul, (hq i).sum_eq_one, one_mul]
    _ ≤ ∑ b : S i, q i b * (M.deviationPayoff q i b + (d : ℝ) * τ) :=
        sum_le_sum fun b _ => hpointwise b
    _ = M.expectedPayoff q i + (d : ℝ) * τ := by
        simp only [mul_add, sum_add_distrib, ← sum_mul, (hq i).sum_eq_one, one_mul,
          M.sum_mul_deviationPayoff_eq_expectedPayoff q (hq i).sum_eq_one]

/-! ### Discretized `τ`-grid on `Bool` (`τ = 1 / m`) -/

/-- The discretized **`τ`-grid** `{0, τ, 2τ, …, 1}` (`τ = 1 / m`) of binary mixed strategies
([Kearns2007], §7.3.1, p. 167). -/
@[expose] def binaryTauGrid (m : ℕ) : Set (Bool → ℝ) :=
  {x : Bool → ℝ | IsMixedStrategy x ∧ ∃ k : ℕ, k ≤ m ∧ x false = (k : ℝ) / (m : ℝ)}

/-- Nearest mixed strategy on `binaryTauGrid m` (in `L₁` norm) to `x : Bool → ℝ` ([Kearns2007],
Lemma 7.4, p. 167), defined explicitly via rounding `m * x false` to the nearest integer in
`{0, …, m}`. -/
noncomputable def nearestGridStrategy (m : ℕ) (x : Bool → ℝ) : Bool → ℝ :=
  let k : ℕ := min m ⌊(m : ℝ) * x false + 1 / 2⌋₊
  fun b => if b then 1 - (k : ℝ) / (m : ℝ) else (k : ℝ) / (m : ℝ)

@[simp] theorem nearestGridStrategy_false (m : ℕ) (x : Bool → ℝ) :
    nearestGridStrategy m x false = ((min m ⌊(m : ℝ) * x false + 1 / 2⌋₊ : ℕ) : ℝ) / (m : ℝ) := by
  simp [nearestGridStrategy]

@[simp] theorem nearestGridStrategy_true (m : ℕ) (x : Bool → ℝ) :
    nearestGridStrategy m x true =
      1 - ((min m ⌊(m : ℝ) * x false + 1 / 2⌋₊ : ℕ) : ℝ) / (m : ℝ) := by
  simp [nearestGridStrategy]

theorem nearestGridStrategy_mem_binaryTauGrid {m : ℕ} (hm : 1 ≤ m) (x : Bool → ℝ) :
    nearestGridStrategy m x ∈ binaryTauGrid m := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  let k : ℕ := min m ⌊(m : ℝ) * x false + 1 / 2⌋₊
  have hk_le : k ≤ m := min_le_left _ _
  have hdiv_le : (k : ℝ) / (m : ℝ) ≤ 1 := (div_le_one hm_pos).mpr (Nat.cast_le.mpr hk_le)
  refine ⟨isMixedStrategy_iff.mpr ⟨fun b => ?_, by simp [nearestGridStrategy]⟩, k, hk_le, rfl⟩
  cases b
  · simp only [nearestGridStrategy, Bool.false_eq_true, ↓reduceIte]; positivity
  · simp only [nearestGridStrategy, ↓reduceIte]; linarith

/-- For a mixed strategy `x : Bool → ℝ` and `1 ≤ m`, `⌊m * x false + 1 / 2⌋₊ ≤ m`. -/
private theorem floor_mul_add_half_le {m : ℕ} {x : Bool → ℝ} (hx : IsMixedStrategy x) :
    ⌊(m : ℝ) * x false + 1 / 2⌋₊ ≤ m := by
  have hx1 : x false ≤ 1 := by
    have hsum := hx.sum_eq_one
    simp only [Fintype.sum_bool] at hsum
    linarith [hx.nonneg true]
  exact Nat.lt_succ_iff.mp ((Nat.floor_lt' (Nat.succ_ne_zero m)).mpr (by push_cast; nlinarith))

private theorem abs_mul_sub_floor_le_half {m : ℕ} {x : Bool → ℝ} (hx : IsMixedStrategy x) :
    |(m : ℝ) * x false - (⌊(m : ℝ) * x false + 1 / 2⌋₊ : ℝ)| ≤ 1 / 2 := by
  have hx0 : 0 ≤ x false := hx.nonneg false
  have h1 := Nat.floor_le (by positivity : 0 ≤ (m : ℝ) * x false + 1 / 2)
  have h2 := Nat.lt_floor_add_one ((m : ℝ) * x false + 1 / 2)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem l1_bool_eq_two_abs {x y : Bool → ℝ} (hx : IsMixedStrategy x)
    (hy : IsMixedStrategy y) :
    ∑ b : Bool, |x b - y b| = 2 * |x false - y false| := by
  have hsum_x : x true + x false = 1 := by simpa only [Fintype.sum_bool] using hx.sum_eq_one
  have hsum_y : y true + y false = 1 := by simpa only [Fintype.sum_bool] using hy.sum_eq_one
  rw [Fintype.sum_bool, show x true - y true = -(x false - y false) by linarith, abs_neg]; ring

/-- **`L₁` error bound of `nearestGridStrategy`**: on `Bool`, rounding to `binaryTauGrid m` changes
each coordinate by at most `1 / (2 * m)`, hence changes the distribution in `L₁` norm by at most
`1 / m = τ`. -/
theorem l1_nearestGridStrategy_le {m : ℕ} (hm : 1 ≤ m) {x : Bool → ℝ} (hx : IsMixedStrategy x) :
    ∑ b : Bool, |x b - nearestGridStrategy m x b| ≤ 1 / (m : ℝ) := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have h1 : x false - (⌊(m : ℝ) * x false + 1 / 2⌋₊ : ℝ) / m =
      ((m : ℝ) * x false - ⌊(m : ℝ) * x false + 1 / 2⌋₊) / m := by field_simp
  rw [l1_bool_eq_two_abs hx (nearestGridStrategy_mem_binaryTauGrid hm x).1,
    nearestGridStrategy_false, min_eq_right (floor_mul_add_half_le hx), h1, abs_div,
    abs_of_pos hm_pos, mul_div_assoc', div_le_div_iff_of_pos_right hm_pos]
  linarith [abs_mul_sub_floor_le_half (m := m) hx]

/-- **`L₁` optimality of `nearestGridStrategy`** ([Kearns2007], Lemma 7.4, p. 167):
`nearestGridStrategy m x` minimizes the `L₁` distance to `x` over all strategies `y` in
`binaryTauGrid m`. -/
theorem l1_nearestGridStrategy_le_of_mem {m : ℕ} (hm : 1 ≤ m) {x y : Bool → ℝ}
    (hx : IsMixedStrategy x) (hy : y ∈ binaryTauGrid m) :
    ∑ b : Bool, |x b - nearestGridStrategy m x b| ≤ ∑ b : Bool, |x b - y b| := by
  obtain ⟨hy_mix, j, _, hy_false⟩ := hy
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  let r := ⌊(m : ℝ) * x false + 1 / 2⌋₊
  have hr_abs : |(m : ℝ) * x false - (r : ℝ)| ≤ 1 / 2 := abs_mul_sub_floor_le_half hx
  have hr_bounds := abs_le.mp hr_abs
  have hscaled : |(m : ℝ) * x false - (r : ℝ)| ≤ |(m : ℝ) * x false - (j : ℝ)| := by
    rcases lt_trichotomy j r with hj_lt | rfl | hr_lt
    · have : (j : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hj_lt
      exact hr_abs.trans ((by linarith [hr_bounds.1] : (1 / 2 : ℝ) ≤ _).trans (le_abs_self _))
    · exact le_rfl
    · have : (r : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hr_lt
      exact hr_abs.trans ((by linarith [hr_bounds.2] : (1 / 2 : ℝ) ≤ (j : ℝ) - _).trans
        (abs_sub_comm (j : ℝ) _ ▸ le_abs_self _))
  have h1 : x false - (r : ℝ) / (m : ℝ) = ((m : ℝ) * x false - (r : ℝ)) / (m : ℝ) := by field_simp
  have h2 : x false - (j : ℝ) / (m : ℝ) = ((m : ℝ) * x false - (j : ℝ)) / (m : ℝ) := by field_simp
  rw [l1_bool_eq_two_abs hx (nearestGridStrategy_mem_binaryTauGrid hm x).1,
    l1_bool_eq_two_abs hx hy_mix, hy_false, nearestGridStrategy_false,
    min_eq_right (floor_mul_add_half_le hx), h1, h2, abs_div, abs_div, abs_of_pos hm_pos]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hscaled hm_pos.le) (by norm_num)

/-- Rounding a binary mixed strategy `x` to `binaryTauGrid m` (`1 ≤ m`) never introduces a new
action into its support, because pure strategies `(0, 1)` and `(1, 0)` already lie on the grid. -/
theorem pos_of_nearestGridStrategy_pos {m : ℕ} (hm : 1 ≤ m) {x : Bool → ℝ}
    (hx : IsMixedStrategy x) {b : Bool} (hb : 0 < nearestGridStrategy m x b) :
    0 < x b := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hsum : x true + x false = 1 := by simpa only [Fintype.sum_bool] using hx.sum_eq_one
  by_contra! hb_le
  have hb0 : x b = 0 := le_antisymm hb_le (hx.nonneg b)
  cases b
  · -- `b = false`: `x false = 0` implies `⌊1 / 2⌋₊ = 0`, so `nearestGridStrategy m x false = 0`.
    have h0 : ⌊(m : ℝ) * x false + 1 / 2⌋₊ = 0 :=
      Nat.floor_eq_zero.mpr (by rw [hb0]; norm_num)
    simp only [nearestGridStrategy, Bool.false_eq_true, ↓reduceIte, h0, min_zero, Nat.cast_zero,
      zero_div, lt_self_iff_false] at hb
  · -- `b = true`: `x true = 0` implies `x false = 1`, so `⌊m + 1 / 2⌋₊ = m` and `q true = 0`.
    have hxf1 : x false = 1 := by linarith
    have hrm : ⌊(m : ℝ) * x false + 1 / 2⌋₊ = m :=
      le_antisymm (floor_mul_add_half_le hx) (Nat.le_floor (by rw [hxf1]; linarith))
    simp only [nearestGridStrategy, ↓reduceIte, hrm, min_self, div_self hm_pos.ne', sub_self,
      lt_self_iff_false] at hb

/-- **`τ`-grid Nash perturbation lemma** ([Kearns2007], Lemma 7.4, p. 167): let `M` be a binary
graphical game of maximum degree at most `d` with payoffs in `[0, 1]`, and let `p` be an exact
mixed Nash equilibrium of `M`. For any grid resolution `1 ≤ m` (`τ = 1 / m`), the `L₁`-nearest
`τ`-grid profile `fun i => nearestGridStrategy m (p i)` is a `(d * (1 / m))`-Nash equilibrium of
`M`. -/
theorem isApproxNash_nearestGridStrategy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : GraphicalGame ι (fun _ => Bool)) [DecidableRel M.graph.Adj]
    {d m : ℕ} (hm : 1 ≤ m)
    (hpay : ∀ (i : ι) (u : ClosedNeighborhood M.graph i → Bool),
      0 ≤ M.localPayoff i u ∧ M.localPayoff i u ≤ 1)
    (hdeg : ∀ i, M.graph.degree i ≤ d)
    {p : ι → Bool → ℝ} (hp : M.toCostGame.IsMixedNash p) :
    M.IsApproxNash ((d : ℝ) * (1 / (m : ℝ))) (fun i => nearestGridStrategy m (p i)) :=
  M.isApproxNash_of_l1_le hpay hdeg hp
    (fun i => (nearestGridStrategy_mem_binaryTauGrid hm (p i)).1)
    (fun i => l1_nearestGridStrategy_le hm (hp.1 i))
    (fun i _ hb => pos_of_nearestGridStrategy_pos hm (hp.1 i) hb)

/-! ### Discretized `ApproximateTreeNash` step ([Kearns2007], §7.3.1, pp. 167–168) -/

/-- Nondeterministic output predicate of discretized **`ApproximateTreeNash`** ([Kearns2007],
§7.3.1, p. 167) on a binary tree graphical game at grid resolution `m` (`τ = 1 / m`) and slack `ε`.
-/
@[expose] def IsApproxTreeNashOutput {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : GraphicalGame ι (fun _ => Bool)) (hT : M.graph.IsTree) (r : ι) (m : ℕ) (ε : ℝ)
    (q : ι → Bool → ℝ) : Prop :=
  IsTreePassOutput M hT r (fun _ => binaryTauGrid m) ε q

/-- Equilibrium completeness step, not the full polynomial-time endpoint, for discretized
`ApproximateTreeNash` (a step of [Kearns2007], Theorem 7.5, pp. 167–168, without the machine
running-time bound): with grid resolution `m = max 1 ⌈(d : ℝ) / ε⌉₊` (`τ = 1 / m ≤ ε / d`), for
every exact mixed Nash equilibrium `p` of a degree-`d`, `[0, 1]`-payoff binary tree graphical game
`M`, the `τ`-grid tables and witnesses of `ApproximateTreeNash` contain an `ε`-Nash equilibrium `q`
within `L₁` distance `1 / m` of `p`. -/
theorem exists_approxTreeNashOutput_of_isMixedNash {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : GraphicalGame ι (fun _ => Bool)) [DecidableRel M.graph.Adj]
    (hT : M.graph.IsTree) (r : ι) {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hpay : ∀ (i : ι) (u : ClosedNeighborhood M.graph i → Bool),
      0 ≤ M.localPayoff i u ∧ M.localPayoff i u ≤ 1)
    (hdeg : ∀ i, M.graph.degree i ≤ d)
    {p : ι → Bool → ℝ} (hp : M.toCostGame.IsMixedNash p) :
    let m := max 1 ⌈(d : ℝ) / ε⌉₊
    ∃ q : ι → Bool → ℝ,
      M.IsApproxTreeNashOutput hT r m ε q ∧
      M.IsApproxNash ε q ∧
      ∀ i, ∑ b : Bool, |p i b - q i b| ≤ 1 / (m : ℝ) := by
  intro m
  have hm1 : 1 ≤ m := le_max_left 1 _
  have hdτ_le : (d : ℝ) * (1 / (m : ℝ)) ≤ ε := by
    rw [mul_one_div, div_le_iff₀ (Nat.cast_pos.mpr hm1)]
    have hceil : (d : ℝ) / ε ≤ (m : ℝ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right 1 _))
    linarith [(div_le_iff₀ hε).mp hceil]
  let q : ι → Bool → ℝ := fun i => nearestGridStrategy m (p i)
  have hq_approx : M.IsApproxNash ε q :=
    IsApproxNash.mono M (M.isApproxNash_nearestGridStrategy hm1 hpay hdeg hp) hdτ_le
  exact ⟨q, isTreePassOutput_iff_isApproxNash.mpr
    ⟨fun i => nearestGridStrategy_mem_binaryTauGrid hm1 (p i), hq_approx⟩,
    hq_approx, fun i => l1_nearestGridStrategy_le hm1 (hp.1 i)⟩

/-- Nonemptiness of the discretized `ApproximateTreeNash` root table at resolution
`m = max 1 ⌈(d : ℝ) / ε⌉₊`. -/
theorem exists_approxTreeNashRootTable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : GraphicalGame ι (fun _ => Bool)) [DecidableRel M.graph.Adj]
    (hT : M.graph.IsTree) (r : ι) {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hpay : ∀ (i : ι) (u : ClosedNeighborhood M.graph i → Bool),
      0 ≤ M.localPayoff i u ∧ M.localPayoff i u ≤ 1)
    (hdeg : ∀ i, M.graph.degree i ≤ d) :
    ∃ xr, rootPassTable M hT r (fun _ => binaryTauGrid (max 1 ⌈(d : ℝ) / ε⌉₊)) ε xr := by
  obtain ⟨p, hp⟩ := M.toCostGame.exists_isMixedNash
  obtain ⟨q, hq_out, _, _⟩ := M.exists_approxTreeNashOutput_of_isMixedNash hT r hε hpay hdeg hp
  exact ⟨q r, fun c => q c.1, hq_out.1⟩

/-- Discretized algorithm **`ApproximateTreeNash`** ([Kearns2007], §7.3.1, p. 167): runs the
two-pass dynamic program restricted to `binaryTauGrid (max 1 ⌈(d : ℝ) / ε⌉₊)` with `ε`-best
responses. -/
noncomputable def approxTreeNash {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : GraphicalGame ι (fun _ => Bool)) [DecidableRel M.graph.Adj]
    (hT : M.graph.IsTree) (r : ι) {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hpay : ∀ (i : ι) (u : ClosedNeighborhood M.graph i → Bool),
      0 ≤ M.localPayoff i u ∧ M.localPayoff i u ≤ 1)
    (hdeg : ∀ i, M.graph.degree i ≤ d) : ι → Bool → ℝ :=
  treePassUpstream hT
    (Classical.choose_spec (M.exists_approxTreeNashRootTable hT r hε hpay hdeg))

/-- Equilibrium correctness step, not the full polynomial-time endpoint, for discretized
`ApproximateTreeNash` (a step of [Kearns2007], Theorem 7.5, pp. 167–168, without the machine
running-time bound): `approxTreeNash` outputs a `τ`-grid `ε`-Nash equilibrium of `M`. -/
theorem approxTreeNash_isApproxNash {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : GraphicalGame ι (fun _ => Bool)) [DecidableRel M.graph.Adj]
    (hT : M.graph.IsTree) (r : ι) {d : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hpay : ∀ (i : ι) (u : ClosedNeighborhood M.graph i → Bool),
      0 ≤ M.localPayoff i u ∧ M.localPayoff i u ≤ 1)
    (hdeg : ∀ i, M.graph.degree i ≤ d) :
    (∀ i, M.approxTreeNash hT r hε hpay hdeg i ∈ binaryTauGrid (max 1 ⌈(d : ℝ) / ε⌉₊)) ∧
      M.IsApproxNash ε (M.approxTreeNash hT r hε hpay hdeg) :=
  treePassUpstream_isApproxNash hT
    (Classical.choose_spec (M.exists_approxTreeNashRootTable hT r hε hpay hdeg))

end ApproxGrid

end GraphicalGame

end Cslib.GameTheory
