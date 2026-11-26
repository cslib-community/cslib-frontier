/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.Byzantine.RecursiveOralMessages
public import CslibFrontier.Computability.Distributed.ByzantineGraph.Basic
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Connectivity.VertexConnectivity
import CslibFrontier.Algorithms.Lean.MaxFlow.Menger
import CslibFrontier.Tactic.FinsetCard

/-!
# Vertex-separator impossibility and synchronous Boolean consensus on graphs

For deterministic synchronous protocols on an undirected communication graph `G : SimpleGraph P`
with a uniform fixed decision round `R`, this module proves the `2t` vertex-separator lower bound
of [Fischer, Lynch and Merritt][FischerLynchMerritt1985] (Theorem 1, §3.2, pp. 62–63) for Boolean
consensus (`GraphProtocol.not_solvesByzantineAgreement_of_isVertexSeparator`), and establishes the
synchronous Boolean consensus adaptation of the `|P| > 3t` and `(2t + 1)`-vertex-connectivity
characterization (`exists_solvesByzantineAgreement_of_le_iff`,
`exists_solvesByzantineAgreement_iff`):

* `|P| ≤ 1` is solved without communication by `GraphProtocol.ownInput`.
* When `3t < |P|` and `G` is `(2t + 1)`-vertex-connected, `purifiedOM` adapts disjoint-path
  purification (after [Dolev][Dolev1982], §2 Theorem 1, p. 19) to relay simulated trees of
  `Cslib.Distributed.Byzantine.om` ([Lamport, Shostak and Pease][LamportShostakPease1982]) across
  paths supplied by Menger's theorem (`SimpleGraph.IsVertexConnected`; [Diestel2025],
  Theorem 3.3.6 (i); [Menger1927]).
* When `2 ≤ |P| ≤ 3t` or `G` is not `(2t + 1)`-vertex-connected, impossibility follows from the
  node and separator covering bounds ([Fischer, Lynch and Merritt][FischerLynchMerritt1985],
  Theorem 1, §3.1–3.2, pp. 61–63; [Pease, Shostak and Lamport][PeaseShostakLamport1980]).

**Distinction from Dolev's broadcast problem.** [Dolev][Dolev1982] (§1 `Agreement B`, pp. 15–16,
and §5 Corollary 10, p. 29) characterizes *designated-sender Byzantine broadcast*, in which a
single transmitter sends a value to all receivers and validity requires agreeing on that
transmitter's value whenever it is reliable (together with *Crusader Agreement*, `Agreement A`,
§4 Theorem 7, p. 26). By contrast, `GraphProtocol.SolvesByzantineAgreement` gives every process a
Boolean input and requires validity only when all correct processes share the same input (the
Boolean consensus formulation of [Fischer, Lynch and Merritt][FischerLynchMerritt1985], §3, p. 61).
Dolev's designated-sender broadcast and Crusader agreement models are not formalized here.

## Impossibility on graphs of connectivity at most `2t`

Suppose a vertex set `C` with `|C| ≤ 2t` separates `u` from `v` in `G`
(`G.IsVertexSeparator u v C`). Split `C` into two subsets `C₁, C₂` of size at most `t` each, let
`A` be the vertices reachable from `u` avoiding `C`, and let `B = (A ∪ C)ᶜ` (which contains `v`
and has no `G`-edges to `A`). Take the two-sheeted covering network `P × Bool`, where `(p, b)` runs
process `p` on input `b` and only edges between `B` and `C₂` cross between sheets:

1. With `C₂` faulty and all honest inputs `false` (sheet `false`), validity forces `(u, false)` to
   decide `false`.
2. With `C₂` faulty and all honest inputs `true` (sheet `true`), validity forces `(v, true)` to
   decide `true`.
3. With `C₁` faulty, placing `A ∪ C₂` in sheet `false` and `B` in sheet `true` respects every
   `G`-edge between correct processes: no edge joins `A` to `B`, while edges between `B` and `C₂`
   are the cross-wired edges of the cover. Both `u` and `v` are correct, contradicting agreement.

Combining this separator bound with the complete-graph node bound (`2 ≤ |P| ≤ 3t`, transferred via
`GraphProtocol.not_solvesByzantineAgreement`) excludes every graph on `|P| ≥ 2` processes that is
not `(2t + 1)`-vertex-connected
(`GraphProtocol.not_solvesByzantineAgreement_of_not_isVertexConnected`), including disconnected
graphs at `t = 0` and complete graphs of order `2 ≤ |P| ≤ 2t + 1`.

## Sufficiency via internally vertex-disjoint path purification

Given a routing table `routes : DisjointPaths G (2 * t + 1)` of `2t + 1` simple paths with pairwise
disjoint internal vertices between every pair of distinct processes, `purifiedOM t routes`
simulates `t + 1` virtual rounds of `Cslib.Distributed.Byzantine.om` in epochs of
`epochLen P = max 1 (|P| - 1)` physical rounds. Within each epoch, processes forward their simulated
`OM(t)` trees along simple walks of length at most `epochLen P`; at the end of the epoch, each
recipient purifies incoming trees from every sender `u` by pointwise strict majority across its
`2t + 1` internally disjoint paths from `u`. Whenever both endpoints are correct, at most
`|F| ≤ t` paths meet `F` internally, so at least `t + 1` paths deliver `u`'s true tree entry. The
resulting frozen tree is faithful in the sense of `Byzantine.omResolve_eq_of_notMem` and
`Byzantine.omResolve_eq_omResolve`, solving Byzantine agreement whenever `3t < |P|`. As in
`Byzantine.om`, processes transmit full simulated trees each round (`Msg` is unbounded, as the
model allows). Menger's global vertex-connectivity theorem
(`isVertexConnected_iff_forall_exists_injective_internallyDisjoint`) supplies
`DisjointPaths G (2 * t + 1)` from `G.IsVertexConnected (2 * t + 1)`, completing the exact
equivalence `exists_solvesByzantineAgreement_iff`.

## Main definitions

* `Cslib.Distributed.ByzantineGraph.DisjointPaths`: routing system of `k` simple paths with
  pairwise disjoint internal vertices between every pair of distinct processes in `G` (distinct
  paths on non-adjacent pairs; adjacent pairs may repeat the direct edge `[u, v]`).
* `Cslib.Distributed.ByzantineGraph.epochLen`: physical round length `max 1 (|P| - 1)` of one
  multi-hop relay epoch.
* `Cslib.Distributed.ByzantineGraph.PurifiedOMState`: process state in `purifiedOM` (`omTree` and
  walk-forwarding buffer `buf`).
* `Cslib.Distributed.ByzantineGraph.purifiedOM`: synchronous `OM(t)` over `2t + 1` internally
  vertex-disjoint paths.

## Main results

* `GraphProtocol.not_solvesByzantineAgreement_of_isVertexSeparator`: no protocol solves Byzantine
  agreement against `t` faults when two vertices are separated by at most `2t` vertices.
* `GraphProtocol.not_solvesByzantineAgreement_of_vertexCut`: explicit partition form of the `2t`
  vertex-cut impossibility bound.
* `GraphProtocol.not_solvesByzantineAgreement_of_not_isVertexConnected`: no protocol on `|P| ≥ 2`
  processes solves Byzantine agreement against `t` faults unless `G` is `(2t + 1)`-vertex-connected.
* `Cslib.Distributed.ByzantineGraph.solvesByzantineAgreement_purifiedOM`: `purifiedOM t routes`
  solves Byzantine agreement against `t` faults among `|P| > 3t` processes in any
  `R ≥ (t + 1) * epochLen P` rounds.
* `Cslib.Distributed.ByzantineGraph.isVertexConnected_iff_card_gt_and_nonempty_disjointPaths`:
  Menger bridge between `G.IsVertexConnected k` and `DisjointPaths G k`.
* `Cslib.Distributed.ByzantineGraph.exists_solvesByzantineAgreement_of_le_iff`,
  `Cslib.Distributed.ByzantineGraph.exists_solvesByzantineAgreement_iff`: Byzantine agreement
  against `t` faults on `G` is solvable iff `|P| ≤ 1` or `3t < |P|` and
  `G.IsVertexConnected (2 * t + 1)`.

## References

* [R. Diestel, *Graph Theory*][Diestel2025], §1.4 and §3.3 (Theorem 3.3.6 (i))
* [D. Dolev, *The Byzantine generals strike again*][Dolev1982], §1 (pp. 15–16) and §2 (Theorem 1,
  p. 19)
* [M. J. Fischer, N. A. Lynch, M. Merritt, *Easy impossibility proofs for distributed consensus
  problems*][FischerLynchMerritt1985], §2–3 (Theorem 1, pp. 60–63)
* [L. Lamport, R. Shostak, M. Pease, *The Byzantine generals problem*][LamportShostakPease1982]
* [K. Menger, *Zur allgemeinen Kurventheorie*][Menger1927]
* [M. Pease, R. Shostak, L. Lamport, *Reaching agreement in the presence of
  faults*][PeaseShostakLamport1980]
-/

public section

namespace Cslib.Distributed.ByzantineGraph

open Cslib.BitString

/-! ### Connectivity impossibility via two-sheeted cross-wired coverings -/

namespace GraphProtocol

variable {P S M : Type*} [DecidableEq P] {G : SimpleGraph P} (π : GraphProtocol G S M)

private theorem not_solvesByzantineAgreement_of_bipartition_cut {t R : ℕ}
    {C₁ C₂ : Finset P} (hC₁ : C₁.card ≤ t) (hC₂ : C₂.card ≤ t) (inB : P → Bool)
    {u v : P} (huC₁ : u ∉ C₁) (huC₂ : u ∉ C₂) (huB : inB u = false)
    (hvC₁ : v ∉ C₁) (hvC₂ : v ∉ C₂) (hvB : inB v = true)
    (hBC₂ : ∀ x ∈ C₂, inB x = false)
    (hcut : ∀ x y, G.Adj x y → inB x = true → inB y = false → y ∈ C₁ ∨ y ∈ C₂) :
    ¬ π.SolvesByzantineAgreement t R := by
  intro h
  -- Two-sheeted covering network `P × Bool`: only edges between `B` (`inB = true`) and `C₂` cross
  -- sheets.
  let cross : P → P → Bool :=
    fun i j => (inB i && decide (j ∈ C₂)) || (decide (i ∈ C₂) && inB j)
  let nbr : P × Bool → P → P × Bool := fun p j => (j, p.2 ^^ cross p.1 j)
  let cover := π.coverState Prod.fst Prod.snd nbr
  let adv : (P → Bool) → ℕ → ∀ j i : P, G.Adj j i → M :=
    fun σ r j i hji => π.send r j (cover r (nbr (i, σ i) j)) i hji
  have key (F : Finset P) (σ : P → Bool)
      (hσ : ∀ i ∉ F, ∀ j ∉ F, G.Adj j i → (σ i ^^ cross i j) = σ j) (i : P) (hi : i ∉ F) :
      π.decision F (adv σ) σ R i = π.output i (cover R (i, σ i)) :=
    congrArg (π.output i) (π.state_eq_coverState Prod.fst Prod.snd nbr F (adv σ) σ
      (fun i => (i, σ i)) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun i hi j hj hji => Prod.ext rfl (hσ i hi j hj hji)) (fun _ _ _ _ _ _ => rfl) R i hi)
  have hcross_not_C₂ (i : P) (hi : i ∉ C₂) (j : P) (hj : j ∉ C₂) : cross i j = false := by
    simp [cross, hi, hj]
  -- Run 1 (`F = C₂`, all inputs `false`): `(u, false)` decides `false`.
  have h₀ := h.validity C₂ hC₂ (adv fun _ => false) (fun _ => false) false (fun _ _ => rfl) u huC₂
  rw [key C₂ _ (fun i hi j hj _ => by rw [hcross_not_C₂ i hi j hj]; rfl) u huC₂] at h₀
  -- Run 2 (`F = C₂`, all inputs `true`): `(v, true)` decides `true`.
  have h₁ := h.validity C₂ hC₂ (adv fun _ => true) (fun _ => true) true (fun _ _ => rfl) v hvC₂
  rw [key C₂ _ (fun i hi j hj _ => by rw [hcross_not_C₂ i hi j hj]; rfl) v hvC₂] at h₁
  -- Run 3 (`F = C₁`, sheet `inB`): `u` (in sheet `false`) and `v` (in sheet `true`) are both
  -- correct and every edge between correct processes matches the cover's wiring.
  have hcompat : ∀ i ∉ C₁, ∀ j ∉ C₁, G.Adj j i → (inB i ^^ cross i j) = inB j := by
    intro i hi j hj hji
    cases hbi : inB i <;> cases hbj : inB j
    · simp [cross, hbi, hbj]
    · simp [cross, hbi, hbj, (hcut j i hji hbj hbi).resolve_left hi]
    · simp [cross, hbi, hbj, (hcut i j hji.symm hbi hbj).resolve_left hj]
    · rw [hcross_not_C₂ i (fun h => Bool.noConfusion (hbi.symm.trans (hBC₂ i h))) j
        (fun h => Bool.noConfusion (hbj.symm.trans (hBC₂ j h)))]
      rfl
  have h₂ := h.agreement C₁ hC₁ (adv inB) inB u huC₁ v hvC₁
  rw [key C₁ inB hcompat u huC₁, key C₁ inB hcompat v hvC₁, huB, hvB, h₀, h₁] at h₂
  exact Bool.false_ne_true h₂

private theorem exists_split_card_le {C : Finset P} {t : ℕ} (hcard : C.card ≤ 2 * t) :
    ∃ C₁ C₂ : Finset P, C₁ ⊆ C ∧ C₂ ⊆ C ∧ C ⊆ C₁ ∪ C₂ ∧ C₁.card ≤ t ∧ C₂.card ≤ t := by
  by_cases ht : C.card ≤ t
  · exact ⟨C, ∅, Finset.Subset.refl C, Finset.empty_subset _, Finset.subset_union_left, ht,
      Nat.zero_le t⟩
  · obtain ⟨C₁, hC₁sub, hC₁card⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_le ht)
    exact ⟨C₁, C \ C₁, hC₁sub, Finset.sdiff_subset, by finset_card, hC₁card.le, by finset_card⟩

/-- **Vertex-separator impossibility bound for synchronous Boolean consensus**
([Fischer, Lynch and Merritt][FischerLynchMerritt1985], Theorem 1, §3, p. 61; connectivity proof in
§3.2, pp. 62–63): in the deterministic synchronous fixed-decision-round model on an undirected
graph `G`, if `C` separates `u` from `v` in `G` and `|C| ≤ 2t`, then no protocol on `G` solves
Boolean Byzantine agreement against at most `t` static faults in any fixed round count `R`. -/
theorem not_solvesByzantineAgreement_of_isVertexSeparator {t R : ℕ} {u v : P} {C : Finset P}
    (hsep : G.IsVertexSeparator u v C) (hcard : C.card ≤ 2 * t) :
    ¬ π.SolvesByzantineAgreement t R := by
  classical
  obtain ⟨C₁, C₂, hC₁sub, hC₂sub, hCcov, hC₁, hC₂⟩ := exists_split_card_le hcard
  obtain ⟨huC, hvC, hsep'⟩ := SimpleGraph.isVertexSeparator_iff_isSeparator.mp hsep
  let reachU : Set P := G.reachAvoiding {u} ↑C
  let inB : P → Bool := fun x => decide (x ∉ reachU ∧ x ∉ C)
  have huR : u ∈ reachU := SimpleGraph.mem_reachAvoiding_of_mem rfl huC
  have hvR : v ∉ reachU :=
    (SimpleGraph.isSeparator_iff_forall_notMem_reachAvoiding.mp hsep') v rfl
  refine π.not_solvesByzantineAgreement_of_bipartition_cut hC₁ hC₂ inB
    (fun h => huC (hC₁sub h)) (fun h => huC (hC₂sub h)) (by simp [inB, huR])
    (fun h => hvC (hC₁sub h)) (fun h => hvC (hC₂sub h)) (by simp [inB, hvR, hvC])
    (fun x hx => by simp [inB, hC₂sub hx]) fun x y hxy hx hy => ?_
  simp only [inB, decide_eq_true_eq, decide_eq_false_iff_not, not_and_or, not_not] at hx hy
  rcases hy with hyR | hyC
  · exact False.elim (hx.1 (SimpleGraph.mem_reachAvoiding_of_adj hyR hxy.symm hx.2))
  · exact Finset.mem_union.mp (hCcov hyC)

/-- Explicit `(A, B, C)` vertex-partition specialization of
`not_solvesByzantineAgreement_of_isVertexSeparator` (matching the disconnection of `G` into
nonempty `A` and `B` by a set `C` of at most `2t` vertices in
[Fischer, Lynch and Merritt][FischerLynchMerritt1985], §3.2, p. 63): if `P` partitions into
nonempty sets `A` and `B` and a separator `C` (possibly `C = ∅`, including at `t = 0` when `G` is
disconnected) with `|C| ≤ 2t` and no edge of `G` connecting `A` and `B`, then no protocol on `G`
solves synchronous fixed-round Boolean Byzantine agreement against `t` faults. -/
theorem not_solvesByzantineAgreement_of_vertexCut [Fintype P] {t R : ℕ} {A B C : Finset P}
    (hA : A.Nonempty) (hB : B.Nonempty) (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) (huniv : A ∪ B ∪ C = Finset.univ)
    (hab : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) (hcard : C.card ≤ 2 * t) :
    ¬ π.SolvesByzantineAgreement t R := by
  obtain ⟨u, hu⟩ := hA
  obtain ⟨v, hv⟩ := hB
  have hsep : G.IsVertexSeparator u v C :=
    SimpleGraph.isVertexSeparator_of_forall_adj hu (Finset.disjoint_right.mp hAB hv)
      (Finset.disjoint_left.mp hAC hu) (Finset.disjoint_left.mp hBC hv) fun x hx y hxy hyA => by
        have hy : y ∈ A ∪ B ∪ C := huniv.symm ▸ Finset.mem_univ y
        simp only [Finset.mem_union] at hy
        exact hy.resolve_left fun h => h.elim hyA fun hyB => hab x hx y hyB hxy
  exact π.not_solvesByzantineAgreement_of_isVertexSeparator hsep hcard

/-- Global `(2t + 1)`-vertex-connectivity necessity for synchronous fixed-round Boolean consensus
on `|P| ≥ 2` processes, combining the separator lower bound
`not_solvesByzantineAgreement_of_isVertexSeparator`
([Fischer, Lynch and Merritt][FischerLynchMerritt1985], Theorem 1, §3.2, pp. 62–63) when `G` admits
a separator of size at most `2t` with the node bound `not_solvesByzantineAgreement` (§3.1,
pp. 61–62) when `2 ≤ |P| ≤ 2t + 1`. -/
theorem not_solvesByzantineAgreement_of_not_isVertexConnected [Fintype P] {t R : ℕ}
    (h2 : 2 ≤ Fintype.card P) (hconn : ¬ G.IsVertexConnected (2 * t + 1)) :
    ¬ π.SolvesByzantineAgreement t R := by
  rw [SimpleGraph.isVertexConnected_iff_forall_isVertexSeparator,
    ENat.card_eq_coe_fintype_card] at hconn
  by_cases hgt : 2 * t + 1 < Fintype.card P
  · push Not at hconn
    obtain ⟨u, v, -, C, hsep, hlt⟩ := hconn (by exact_mod_cast hgt)
    exact π.not_solvesByzantineAgreement_of_isVertexSeparator hsep (by omega)
  · exact π.not_solvesByzantineAgreement h2 (by omega)

end GraphProtocol

/-! ### Purified `OM(t)` along `2t + 1` internally vertex-disjoint paths -/

/-- A routing system of `k` simple paths in `G` with pairwise disjoint internal vertices between
every ordered pair of distinct vertices. Because `SimpleGraph.InternallyDisjoint` constrains only
vertices strictly outside `{u, v}`, non-adjacent pairs have `k` distinct paths
(`SimpleGraph.injective_of_internallyDisjoint_of_not_adj`), whereas adjacent pairs `u — v` may
repeat the direct edge `[u, v]` (which has no internal vertices to corrupt, and why
`k < Fintype.card P` appears explicitly alongside `Nonempty (DisjointPaths G k)` in
`isVertexConnected_iff_card_gt_and_nonempty_disjointPaths`). -/
structure DisjointPaths {P : Type*} (G : SimpleGraph P) (k : ℕ) where
  /-- `path u v huv m`: the `m`-th path from `u` to `v`. -/
  path : ∀ u v : P, u ≠ v → Fin k → G.Walk u v
  /-- Every routed walk is a simple path. -/
  isPath : ∀ u v (huv : u ≠ v) m, (path u v huv m).IsPath
  /-- For each distinct pair `u ≠ v`, the `k` paths share no internal vertices. -/
  internallyDisjoint : ∀ u v (huv : u ≠ v), SimpleGraph.InternallyDisjoint (path u v huv)

/-- Number of physical synchronous rounds in one multi-hop forwarding epoch on `P`:
`max 1 (Fintype.card P - 1)`, which is positive and bounds the length of every simple path in `G`.
-/
@[expose] def epochLen (P : Type*) [Fintype P] : ℕ :=
  max 1 (Fintype.card P - 1)

theorem epochLen_pos (P : Type*) [Fintype P] : 0 < epochLen P := by
  unfold epochLen
  omega

private theorem walk_length_le_epochLen {P : Type*} [Fintype P] {G : SimpleGraph P} {u v : P}
    {w : G.Walk u v} (hw : w.IsPath) : w.length ≤ epochLen P := by
  have hnd := hw.support_nodup.length_le_card
  rw [SimpleGraph.Walk.length_support] at hnd
  unfold epochLen
  omega

/-- Local state of a process in `purifiedOM`: its simulated complete-graph `OM(t)` relay tree
`omTree`, paired with the current epoch's multi-hop walk-forwarding buffer `buf`. -/
structure PurifiedOMState (P : Type*) where
  /-- Simulated `OM(t)` tree (`List P → Bool`). -/
  omTree : List P → Bool
  /-- Current epoch's forwarding buffer (`List P → List P → Bool`), indexed by `w.support.tail`. -/
  buf : List P → List P → Bool

/-- Synchronous `OM(t)` simulated on `G` along `2t + 1` pairwise internally vertex-disjoint paths
([Dolev1982]; [LamportShostakPease1982]).

Each virtual round `v` of `Cslib.Distributed.Byzantine.om` runs across an epoch of
`L = epochLen P` physical rounds:
* During steps `0, …, L - 1` of epoch `v`, processes forward tree snapshots along simple walks of
  `G`, writing `j :: w` at step `w.length` from neighbour `j`.
* At the final physical step (`step + 1 = L`) of epoch `v`, each process `i` reconstructs the tree
  of every other process `u ≠ i` by pointwise `strictMajorityOn` across the `2t + 1` paths
  `routes.path i u`, and updates the depth-`(v + 1)` entries `u :: τ` (`τ.length = v`) of `omTree`.
* The decision is the strict majority over all commanders `c` of
  `Byzantine.omResolve i s.omTree t [c]`.
-/
@[expose] def purifiedOM {P : Type*} [Fintype P] [DecidableEq P] {G : SimpleGraph P}
    [DecidableRel G.Adj] (t : ℕ) (routes : DisjointPaths G (2 * t + 1)) :
    GraphProtocol G (PurifiedOMState P) (List P → List P → Bool) where
  init _ b := { omTree := fun _ => b, buf := fun _ _ => b }
  send r _ s _ _ :=
    if r % epochLen P = 0 then fun _ => s.omTree else s.buf
  update r i s msg :=
    let L := epochLen P
    let v := r / L
    let step := r % L
    let cur : List P → List P → Bool := if step = 0 then fun _ => s.omTree else s.buf
    let nextBuf : List P → List P → Bool := fun
      | [], τ => cur [] τ
      | j :: w, τ =>
        if w.length = step then
          if hji : G.Adj j i then msg j hji w τ else cur (j :: w) τ
        else cur (j :: w) τ
    let nextTree : List P → Bool :=
      if step + 1 = L then fun
        | [] => s.omTree []
        | u :: τ =>
          if τ.length = v then
            if hu : u = i then s.omTree τ
            else strictMajorityOn Finset.univ fun m =>
              nextBuf (routes.path i u (Ne.symm hu) m).support.tail τ
          else s.omTree (u :: τ)
      else s.omTree
    { omTree := nextTree, buf := nextBuf }
  output i s := strictMajorityOn Finset.univ fun c => Byzantine.omResolve i s.omTree t [c]

private theorem epoch_add_mod {P : Type*} [Fintype P] {v s : ℕ} (hs : s < epochLen P) :
    (v * epochLen P + s) % epochLen P = s := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]

private theorem epoch_add_div {P : Type*} [Fintype P] {v s : ℕ} (hs : s < epochLen P) :
    (v * epochLen P + s) / epochLen P = v := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (epochLen_pos P), Nat.div_eq_of_lt hs, zero_add]

section PurifiedOMProof

variable {P : Type*} [Fintype P] [DecidableEq P] {G : SimpleGraph P} [DecidableRel G.Adj]
  {t : ℕ} (routes : DisjointPaths G (2 * t + 1)) (F : Finset P)
  (adv : ℕ → ∀ j i : P, G.Adj j i → List P → List P → Bool) (x : P → Bool)

private theorem purifiedOM_state_succ_omTree (r : ℕ) (i : P) :
    ((purifiedOM t routes).state F adv x (r + 1) i).omTree =
      if r % epochLen P + 1 = epochLen P then fun
        | [] => ((purifiedOM t routes).state F adv x r i).omTree []
        | u :: τ =>
          if τ.length = r / epochLen P then
            if hu : u = i then ((purifiedOM t routes).state F adv x r i).omTree τ
            else strictMajorityOn Finset.univ fun m =>
              ((purifiedOM t routes).state F adv x (r + 1) i).buf
                (routes.path i u (Ne.symm hu) m).support.tail τ
          else ((purifiedOM t routes).state F adv x r i).omTree (u :: τ)
      else ((purifiedOM t routes).state F adv x r i).omTree := rfl

private theorem purifiedOM_state_succ_buf_nil (r : ℕ) (i : P) :
    ((purifiedOM t routes).state F adv x (r + 1) i).buf [] =
      (if r % epochLen P = 0 then
        fun _ => ((purifiedOM t routes).state F adv x r i).omTree
      else ((purifiedOM t routes).state F adv x r i).buf) [] := rfl

private theorem purifiedOM_state_succ_buf_cons (r : ℕ) (i j : P) (w τ : List P) :
    ((purifiedOM t routes).state F adv x (r + 1) i).buf (j :: w) τ =
      let cur := if r % epochLen P = 0 then
        fun _ => ((purifiedOM t routes).state F adv x r i).omTree
      else ((purifiedOM t routes).state F adv x r i).buf
      if w.length = r % epochLen P then
        if hji : G.Adj j i then
          (if j ∈ F then adv r j i hji
           else if r % epochLen P = 0 then
             fun _ => ((purifiedOM t routes).state F adv x r j).omTree
           else ((purifiedOM t routes).state F adv x r j).buf) w τ
        else cur (j :: w) τ
      else cur (j :: w) τ := rfl

private theorem purifiedOM_omTree_nil (i : P) :
    ∀ r, ((purifiedOM t routes).state F adv x r i).omTree [] = x i
  | 0 => rfl
  | r + 1 => by
    rw [purifiedOM_state_succ_omTree]
    split_ifs <;> exact purifiedOM_omTree_nil i r

private theorem purifiedOM_omTree_epoch_offset (v : ℕ) (i : P) :
    ∀ {s : ℕ}, s < epochLen P →
      ((purifiedOM t routes).state F adv x (v * epochLen P + s) i).omTree =
        ((purifiedOM t routes).state F adv x (v * epochLen P) i).omTree
  | 0, _ => rfl
  | s + 1, hs => by
    have hs' : s < epochLen P := by omega
    rw [← Nat.add_assoc, purifiedOM_state_succ_omTree,
      ite_eq_right (by rw [epoch_add_mod hs']; omega)]
    exact purifiedOM_omTree_epoch_offset v i hs'

private def curBuf (v s : ℕ) (i : P) : List P → List P → Bool :=
  if s = 0 then fun _ => ((purifiedOM t routes).state F adv x (v * epochLen P) i).omTree
  else ((purifiedOM t routes).state F adv x (v * epochLen P + s) i).buf

private theorem curBuf_succ {v s : ℕ} (i : P) :
    curBuf routes F adv x v (s + 1) i =
      ((purifiedOM t routes).state F adv x ((v * epochLen P + s) + 1) i).buf := by
  unfold curBuf
  rw [ite_eq_right (Nat.succ_ne_zero s), ← Nat.add_assoc]

/-- The buffer `purifiedOM` reads at step `s < epochLen P` of epoch `v` is `curBuf v s`. -/
private theorem cur_eq_curBuf {v s : ℕ} (hs : s < epochLen P) (i : P) :
    (if (v * epochLen P + s) % epochLen P = 0 then
        fun _ => ((purifiedOM t routes).state F adv x (v * epochLen P + s) i).omTree
      else ((purifiedOM t routes).state F adv x (v * epochLen P + s) i).buf) =
      curBuf routes F adv x v s i := by
  unfold curBuf
  rw [epoch_add_mod hs]
  by_cases hs0 : s = 0 <;> simp only [hs0, ↓reduceIte, add_zero]

private theorem curBuf_succ_nil {v s : ℕ} (hs : s < epochLen P) (i : P) :
    curBuf routes F adv x v (s + 1) i [] = curBuf routes F adv x v s i [] := by
  rw [curBuf_succ, purifiedOM_state_succ_buf_nil, cur_eq_curBuf routes F adv x hs]

private theorem curBuf_succ_cons_ne {v s : ℕ} (hs : s < epochLen P) (i j : P) {w : List P}
    (hw : w.length ≠ s) (τ : List P) :
    curBuf routes F adv x v (s + 1) i (j :: w) τ =
      curBuf routes F adv x v s i (j :: w) τ := by
  rw [curBuf_succ, purifiedOM_state_succ_buf_cons]
  dsimp only
  rw [cur_eq_curBuf routes F adv x hs i, epoch_add_mod hs, ite_eq_right hw]

private theorem curBuf_succ_cons_eq {v s : ℕ} (hs : s < epochLen P) (i : P) {j : P}
    (hji : G.Adj j i) (hj : j ∉ F) {w : List P} (hw : w.length = s) (τ : List P) :
    curBuf routes F adv x v (s + 1) i (j :: w) τ = curBuf routes F adv x v s j w τ := by
  rw [curBuf_succ, purifiedOM_state_succ_buf_cons]
  dsimp only
  rw [cur_eq_curBuf routes F adv x hs j, epoch_add_mod hs, ite_eq_left hw,
    dite_eq_left_of_eq_true (eq_true hji), ite_eq_right hj]

private theorem curBuf_freeze (v : ℕ) (i : P) (w : List P) :
    ∀ {s d : ℕ}, w.length ≤ s → s + d ≤ epochLen P →
      curBuf routes F adv x v (s + d) i w = curBuf routes F adv x v s i w
  | s, 0, _, _ => rfl
  | s, d + 1, hws, hsd => by
    rw [show s + (d + 1) = (s + d) + 1 by omega]
    have hstep : curBuf routes F adv x v ((s + d) + 1) i w =
        curBuf routes F adv x v (s + d) i w := by
      match w with
      | [] => exact curBuf_succ_nil routes F adv x (by omega) i
      | j :: w' =>
        funext τ
        exact curBuf_succ_cons_ne routes F adv x (by omega) i j
          (by simp only [List.length_cons] at hws; omega) τ
    exact hstep.trans (curBuf_freeze v i w hws (by omega))

private theorem curBuf_walk (v : ℕ) :
    ∀ {i u : P} (W : G.Walk i u), W.length ≤ epochLen P → (∀ z ∈ W.support, z ∉ F) →
      curBuf routes F adv x v W.length i W.support.tail =
        ((purifiedOM t routes).state F adv x (v * epochLen P) u).omTree
  | _, _, .nil, _, _ => rfl
  | i, u, @SimpleGraph.Walk.cons _ _ _ j _ hij W', hlen, hsupp => by
    have hlen' : W'.length < epochLen P := Nat.lt_of_succ_le hlen
    have htail : (SimpleGraph.Walk.cons hij W').support.tail = j :: W'.support.tail := by
      cases W' <;> rfl
    have htail_len : W'.support.tail.length = W'.length := by
      simp [SimpleGraph.Walk.length_support]
    funext τ
    rw [htail, SimpleGraph.Walk.length_cons,
      curBuf_succ_cons_eq routes F adv x hlen' i hij.symm
        (hsupp j (List.mem_cons_of_mem _ W'.start_mem_support)) htail_len τ,
      curBuf_walk v W' hlen'.le fun z hz => hsupp z (List.mem_cons_of_mem _ hz)]

private theorem curBuf_epochLen_walk (v : ℕ) {i u : P} {W : G.Walk i u} (hW : W.IsPath)
    (hsupp : ∀ z ∈ W.support, z ∉ F) :
    curBuf routes F adv x v (epochLen P) i W.support.tail =
      ((purifiedOM t routes).state F adv x (v * epochLen P) u).omTree := by
  have hlen := walk_length_le_epochLen hW
  have htail_le : W.support.tail.length ≤ W.length := by
    rw [List.length_tail, SimpleGraph.Walk.length_support, Nat.add_sub_cancel]
  have hfr := curBuf_freeze routes F adv x v i W.support.tail htail_le
    (show W.length + (epochLen P - W.length) ≤ epochLen P by omega)
  rw [Nat.add_sub_of_le hlen] at hfr
  exact hfr.trans (curBuf_walk routes F adv x v W hlen hsupp)

private theorem purifiedOM_omTree_epoch_succ (hF : F.card ≤ t) (v : ℕ) {i u : P}
    (hi : i ∉ F) (hu : u ∉ F) {τ : List P} (hτ : τ.length = v) :
    ((purifiedOM t routes).state F adv x ((v + 1) * epochLen P) i).omTree (u :: τ) =
      ((purifiedOM t routes).state F adv x (v * epochLen P) u).omTree τ := by
  have hL := epochLen_pos P
  have hpred_lt : epochLen P - 1 < epochLen P := by omega
  have hr_eq : (v + 1) * epochLen P = (v * epochLen P + (epochLen P - 1)) + 1 := by
    rw [Nat.add_mul, one_mul]; omega
  have hmod := epoch_add_mod (v := v) hpred_lt
  have hdiv := epoch_add_div (v := v) hpred_lt
  have hbuf : curBuf routes F adv x v (epochLen P) i =
      ((purifiedOM t routes).state F adv x ((v + 1) * epochLen P) i).buf := by
    rw [curBuf, ite_eq_right (by omega), Nat.add_mul, one_mul]
  conv_lhs => rw [hr_eq]
  rw [purifiedOM_state_succ_omTree, hmod, hdiv, ite_eq_left (by omega)]
  dsimp only
  rw [ite_eq_left hτ, ← hr_eq]
  split_ifs with hu_eq
  · subst hu_eq
    rw [purifiedOM_omTree_epoch_offset routes F adv x v u hpred_lt]
  · rw [← hbuf]
    let W := routes.path i u (Ne.symm hu_eq)
    let bad : Finset (Fin (2 * t + 1)) :=
      Finset.univ.filter fun m => ∃ z ∈ (W m).support, z ∈ F
    have hbad_le : bad.card ≤ F.card := by
      let pick : Fin (2 * t + 1) → P := fun m =>
        if hm : ∃ z ∈ (W m).support, z ∈ F then Classical.choose hm else u
      have hpick : ∀ m ∈ bad, pick m ∈ (W m).support ∧ pick m ∈ F := fun m hm => by
        simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hm
        simp only [pick, dite_eq_left_of_eq_true (eq_true hm)]
        exact Classical.choose_spec hm
      refine Finset.card_le_card_of_injOn pick (fun m hm => (hpick m hm).2)
        fun m₁ hm₁ m₂ hm₂ heq => Classical.byContradiction fun hne => ?_
      have h₁ := hpick m₁ hm₁
      rcases routes.internallyDisjoint i u (Ne.symm hu_eq) hne _ h₁.1
          (heq ▸ (hpick m₂ hm₂).1) with h_end | h_end
      exacts [hi (h_end ▸ h₁.2), hu (h_end ▸ h₁.2)]
    refine strictMajorityOn_eq_of_forall_notMem (F := bad) (fun m _ hm => ?_)
      (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    exact congrFun (curBuf_epochLen_walk routes F adv x v (routes.isPath i u (Ne.symm hu_eq) m)
      fun z hz hzF => hm (Finset.mem_filter.mpr ⟨Finset.mem_univ m, z, hz, hzF⟩)) τ

private theorem purifiedOM_omTree_freeze (i : P) (σ : List P) :
    ∀ d, ((purifiedOM t routes).state F adv x (σ.length * epochLen P + d) i).omTree σ =
      ((purifiedOM t routes).state F adv x (σ.length * epochLen P) i).omTree σ
  | 0 => rfl
  | d + 1 => by
    rw [← Nat.add_assoc]
    cases σ with
    | nil => rw [purifiedOM_omTree_nil, purifiedOM_omTree_nil]
    | cons u τ =>
      have hne : τ.length ≠ ((u :: τ).length * epochLen P + d) / epochLen P := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (epochLen_pos P), List.length_cons]
        exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_left _ _))
      rw [purifiedOM_state_succ_omTree]
      split_ifs <;> simp only [hne, ↓reduceIte, purifiedOM_omTree_freeze i (u :: τ) d]

private def frozenTree (i : P) (σ : List P) : Bool :=
  ((purifiedOM t routes).state F adv x (σ.length * epochLen P) i).omTree σ

private theorem frozenTree_cons (hF : F.card ≤ t) {p : P} (hp : p ∉ F) {q : P} (hq : q ∉ F)
    (τ : List P) :
    frozenTree routes F adv x p (q :: τ) = frozenTree routes F adv x q τ := by
  simp only [frozenTree, List.length_cons]
  exact purifiedOM_omTree_epoch_succ routes F adv x hF τ.length hp hq rfl

private theorem omResolve_purifiedOM_eq_frozenTree {R : ℕ}
    (hR : (t + 1) * epochLen P ≤ R) (i c : P) :
    Byzantine.omResolve i ((purifiedOM t routes).state F adv x R i).omTree t [c] =
      Byzantine.omResolve i (frozenTree routes F adv x i) t [c] := by
  refine Byzantine.omResolve_congr i t [c] fun τ hτ => ?_
  have hle : τ.length * epochLen P ≤ R :=
    (Nat.mul_le_mul_right _ (by simp only [List.length_singleton] at hτ; omega)).trans hR
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd, purifiedOM_omTree_freeze]
  rfl

end PurifiedOMProof

/-- **Synchronous Boolean consensus via disjoint-path oral messages** (consensus adaptation
combining path purification after [Dolev][Dolev1982], §2 Theorem 1, p. 19, with recursive oral
messages `Byzantine.om` of [Lamport, Shostak and Pease][LamportShostakPease1982], §3 Theorem 1,
p. 390; not Dolev's designated-sender broadcast theorem, §5 Corollary 10, p. 29): given a routing
table `routes : DisjointPaths G (2 * t + 1)`, `purifiedOM t routes` solves synchronous Boolean
Byzantine agreement on `G` against `t` faults among `|P| > 3t` processes in any
`R ≥ (t + 1) * epochLen P` rounds. -/
theorem solvesByzantineAgreement_purifiedOM {P : Type*} [Fintype P] [DecidableEq P]
    {G : SimpleGraph P} [DecidableRel G.Adj] (t : ℕ) (routes : DisjointPaths G (2 * t + 1))
    (hn : 3 * t < Fintype.card P) {R : ℕ} (hR : (t + 1) * epochLen P ≤ R) :
    (purifiedOM t routes).SolvesByzantineAgreement t R where
  agreement F hF adv x i hi j hj := by
    refine congrArg (strictMajorityOn Finset.univ) (funext fun c => ?_)
    rw [omResolve_purifiedOM_eq_frozenTree routes F adv x hR i c,
      omResolve_purifiedOM_eq_frozenTree routes F adv x hR j c]
    exact Byzantine.omResolve_eq_omResolve
      (fun _ hp _ hq τ => frozenTree_cons routes F adv x hF hp hq τ) t c [] List.not_mem_nil
      (by simpa using hF) (by simpa using hn) i hi j hj
  validity F hF adv x v hv i hi := by
    refine strictMajorityOn_eq_of_forall_notMem (F := F) (fun c _ hc => ?_) ?_
    · rw [omResolve_purifiedOM_eq_frozenTree routes F adv x hR i c,
        Byzantine.omResolve_eq_of_notMem
          (fun _ hp _ hq τ => frozenTree_cons routes F adv x hF hp hq τ) t c [] hc
          (by simpa using hF)
          (by simp only [List.toFinset_nil, Finset.compl_empty, Finset.card_univ]; omega) i hi]
      unfold frozenTree
      rw [List.length_nil, Nat.zero_mul, purifiedOM_omTree_nil, hv c hc]
    · rw [Finset.card_univ]
      omega

/-! ### Menger bridge and synchronous Boolean consensus characterization -/

/-- Bridge between `SimpleGraph.IsVertexConnected k` and `DisjointPaths G k` via Menger's global
vertex-connectivity theorem (`isVertexConnected_iff_forall_exists_injective_internallyDisjoint`;
[Diestel2025], Theorem 3.3.6 (i); [Menger1927]): a finite simple graph `G` is `k`-vertex-connected
if and only if `k < |P|` and `DisjointPaths G k` is nonempty. -/
theorem isVertexConnected_iff_card_gt_and_nonempty_disjointPaths {P : Type*} [Fintype P]
    (G : SimpleGraph P) (k : ℕ) :
    G.IsVertexConnected k ↔ k < Fintype.card P ∧ Nonempty (DisjointPaths G k) := by
  constructor
  · intro hconn
    obtain ⟨hcard, hpaths⟩ :=
      Cslib.Algorithms.Lean.MaxFlow.isVertexConnected_iff_forall_exists_injective_internallyDisjoint
        G k |>.mp hconn
    rw [ENat.card_eq_coe_fintype_card] at hcard
    choose W _ hW hdisj using fun (u v : P) (huv : u ≠ v) => hpaths huv
    exact ⟨by exact_mod_cast hcard, ⟨⟨W, hW, hdisj⟩⟩⟩
  · rintro ⟨hcard, ⟨routes⟩⟩
    refine SimpleGraph.isVertexConnected_of_forall_exists_internallyDisjoint ?_ fun u v huv =>
      ⟨routes.path u v huv, routes.isPath u v huv, routes.internallyDisjoint u v huv⟩
    simpa [ENat.card_eq_coe_fintype_card] using hcard

private theorem card_le_one_or_of_solvesByzantineAgreement {P S M : Type*} [Fintype P]
    [DecidableEq P] {G : SimpleGraph P} {t R : ℕ} {π : GraphProtocol G S M}
    (h : π.SolvesByzantineAgreement t R) :
    Fintype.card P ≤ 1 ∨ (3 * t < Fintype.card P ∧ G.IsVertexConnected (2 * t + 1)) := by
  by_cases h1 : Fintype.card P ≤ 1
  · exact Or.inl h1
  · refine Or.inr ⟨?_, ?_⟩
    · by_contra h3
      exact π.not_solvesByzantineAgreement (by omega) (by omega) h
    · by_contra hconn
      exact π.not_solvesByzantineAgreement_of_not_isVertexConnected (by omega) hconn h

private def uliftProtocol.{u, s₀, m₀, v, w} {P : Type u} {G : SimpleGraph P}
    {S : Type s₀} {M : Type m₀} (π : GraphProtocol G S M) :
    GraphProtocol G (ULift.{v} S) (ULift.{w} M) where
  init i b := .up (π.init i b)
  send r i s j hij := .up (π.send r i s.down j hij)
  update r i s m := .up (π.update r i s.down fun j hji => (m j hji).down)
  output i s := π.output i s.down

private theorem uliftProtocol_state.{u, s₀, m₀, v, w} {P : Type u} [DecidableEq P]
    {G : SimpleGraph P} {S : Type s₀} {M : Type m₀} (π : GraphProtocol G S M)
    (F : Finset P) (adv : ℕ → ∀ j i : P, G.Adj j i → ULift.{w} M) (x : P → Bool) :
    ∀ r i, ((uliftProtocol.{u, s₀, m₀, v, w} π).state F adv x r i).down =
      π.state F (fun r j i hji => (adv r j i hji).down) x r i
  | 0, _ => rfl
  | r + 1, i => by
    dsimp only [GraphProtocol.state]
    change π.update r i ((uliftProtocol π).state F adv x r i).down _ =
      π.update r i (π.state F _ x r i) _
    congr 1
    · exact uliftProtocol_state π F adv x r i
    · funext j hji
      by_cases hj : j ∈ F <;> simp only [hj, ↓reduceIte]
      exact congrArg (fun s => π.send r j s i hji) (uliftProtocol_state π F adv x r j)

private theorem solvesByzantineAgreement_ulift.{u, s₀, m₀, v, w} {P : Type u} [DecidableEq P]
    {G : SimpleGraph P} {S : Type s₀} {M : Type m₀} {π : GraphProtocol G S M} {t R : ℕ}
    (h : π.SolvesByzantineAgreement t R) :
    (uliftProtocol.{u, s₀, m₀, v, w} π).SolvesByzantineAgreement t R where
  agreement F hF adv x i hi j hj := by
    change π.output i ((uliftProtocol π).state F adv x R i).down =
      π.output j ((uliftProtocol π).state F adv x R j).down
    rw [uliftProtocol_state, uliftProtocol_state]
    exact h.agreement F hF _ x i hi j hj
  validity F hF adv x b hb i hi := by
    change π.output i ((uliftProtocol π).state F adv x R i).down = b
    rw [uliftProtocol_state]
    exact h.validity F hF _ x b hb i hi

/-- **Synchronous Boolean consensus characterization at fixed round bound** (Boolean consensus
adaptation on `SimpleGraph P`, rather than Dolev's designated-sender broadcast characterization in
[Dolev][Dolev1982], §1 pp. 15–16 and §5 Corollary 10, p. 29). For any `R ≥ (t + 1) * epochLen P`,
some protocol on `G` solves synchronous Boolean Byzantine agreement against `t` faults in `R`
rounds if and only if `|P| ≤ 1` or both `3t < |P|` and `G` is `(2t + 1)`-vertex-connected:
`GraphProtocol.ownInput` handles `|P| ≤ 1`; `purifiedOM` handles `3t < |P|` on `(2t + 1)`-connected
graphs (adapting path purification after [Dolev][Dolev1982], §2 Theorem 1, p. 19, with
`Byzantine.om` of [LamportShostakPease1982] and Menger's theorem [Diestel2025]); and the node and
separator bounds exclude `2 ≤ |P| ≤ 3t` and graphs of connectivity at most `2t`
([FischerLynchMerritt1985], Theorem 1, §3.1–3.2, pp. 61–63; [PeaseShostakLamport1980]). Whether
fewer than `(t + 1) * epochLen P` rounds suffice on a specific graph is not addressed here. -/
theorem exists_solvesByzantineAgreement_of_le_iff.{u} {P : Type u} [Fintype P] [DecidableEq P]
    (G : SimpleGraph P) (t : ℕ) {R : ℕ} (hR : (t + 1) * epochLen P ≤ R) :
    (∃ (S M : Type u) (π : GraphProtocol G S M), π.SolvesByzantineAgreement t R) ↔
      Fintype.card P ≤ 1 ∨ (3 * t < Fintype.card P ∧ G.IsVertexConnected (2 * t + 1)) := by
  constructor
  · rintro ⟨_, _, _, h⟩
    exact card_le_one_or_of_solvesByzantineAgreement h
  · rintro (h1 | ⟨hn, hconn⟩)
    · have : Subsingleton P := Fintype.card_le_one_iff_subsingleton.mp h1
      exact ⟨ULift.{u} Bool, ULift.{u} Unit, uliftProtocol (GraphProtocol.ownInput G),
        solvesByzantineAgreement_ulift (GraphProtocol.solvesByzantineAgreement_ownInput G t R)⟩
    · classical
      obtain ⟨-, ⟨routes⟩⟩ :=
        (isVertexConnected_iff_card_gt_and_nonempty_disjointPaths G (2 * t + 1)).mp hconn
      exact ⟨PurifiedOMState P, List P → List P → Bool, purifiedOM t routes,
        solvesByzantineAgreement_purifiedOM t routes hn hR⟩

/-- **Synchronous Boolean consensus characterization on finite simple graphs** (Boolean consensus
adaptation on `SimpleGraph P`, rather than Dolev's designated-sender broadcast characterization in
[Dolev][Dolev1982], §1 pp. 15–16 and §5 Corollary 10, p. 29). Some protocol on `G` solves
synchronous Boolean Byzantine agreement against `t` faults in some fixed round count `R` if and
only if `|P| ≤ 1` or both `3t < |P|` and `G` is `(2t + 1)`-vertex-connected:
`GraphProtocol.ownInput` handles `|P| ≤ 1`; `purifiedOM` handles `3t < |P|` on `(2t + 1)`-connected
graphs (after [Dolev][Dolev1982], §2 Theorem 1, p. 19; [LamportShostakPease1982]; [Diestel2025]);
and the node and separator bounds exclude `2 ≤ |P| ≤ 3t` and graphs of connectivity at most `2t`
([FischerLynchMerritt1985], Theorem 1, §3.1–3.2, pp. 61–63; [PeaseShostakLamport1980]). -/
theorem exists_solvesByzantineAgreement_iff.{u} {P : Type u} [Fintype P] [DecidableEq P]
    (G : SimpleGraph P) (t : ℕ) :
    (∃ (S M : Type u) (R : ℕ) (π : GraphProtocol G S M), π.SolvesByzantineAgreement t R) ↔
      Fintype.card P ≤ 1 ∨ (3 * t < Fintype.card P ∧ G.IsVertexConnected (2 * t + 1)) := by
  constructor
  · rintro ⟨_, _, _, _, h⟩
    exact card_le_one_or_of_solvesByzantineAgreement h
  · intro h
    obtain ⟨S, M, π, hsol⟩ := (exists_solvesByzantineAgreement_of_le_iff G t le_rfl).mpr h
    exact ⟨S, M, (t + 1) * epochLen P, π, hsol⟩

end Cslib.Distributed.ByzantineGraph
