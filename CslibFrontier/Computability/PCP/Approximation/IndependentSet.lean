/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Approximation.FGLSSRuntime
public import CslibFrontier.Computability.PCP.Approximation.MaxExactThreeSAT
public import CslibFrontier.Computability.Complexity.Classes.PCP.Robustness
public import CslibFrontier.Computability.Complexity.Problems.Clique
public import CslibFrontier.Computability.Complexity.Problems.VertexCover
import CslibFrontier.Computability.PCP.Completeness
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.IndepNum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Tactic.LinarithCast

/-!
# Independent Set, Clique and Vertex Cover are NP-hard to approximate

The values of a graph (`Cslib.Complexity.Graph`, read on its declared vertices) are its
independence number `Graph.indepNum`, its clique number `Graph.cliqueNum` and its vertex cover
number `Graph.vertexCoverNum`, the extreme targets of the decision problems `IndependentSet`,
`Clique` and `VertexCover`. The gap problems ask, for an instance `(G, k)`:

* `GapIndependentSet s`: is `indepNum G ≥ k`, or `indepNum G ≤ s * k`?
* `GapClique s`: is `cliqueNum G ≥ k`, or `cliqueNum G ≤ s * k`?
* `GapVertexCover r`: is `vertexCoverNum G ≤ k`, or `vertexCoverNum G ≥ r * k`?

The yes-instances of the first two are exactly `IndependentSet` and `Clique`.

For Independent Set and Clique, the reduction of Feige, Goldwasser, Lovász, Safra and Szegedy
[FeigeGoldwasserLovaszSafraSzegedy1996] ([Goldreich2007DraftR5], Exercise 9.18; [Arora and Barak,
Chapter 11][AroraBarak09]) maps an instance `a` of a nonadaptive `(1, s)`-PCP verifier `V` to its
explicit accepting-view conflict graph `V.fglssEdgeList a` paired with target `2 ^ V.coins a`
(`Cslib.Complexity.PCPVerifier.fglssToIndependentSet`). By `PCPVerifier.fglssGraphIso` and the
independence-number identity `PCPVerifier.exists_acceptCount_eq_indepNum_fglssGraph`, members have
independence number `2 ^ V.coins a` and non-members have independence number at most
`s * 2 ^ V.coins a`; when `V` uses `O(log n)` coins and `O(1)` queries, the reduction runs in
polynomial time (`PCPVerifier.computableInPolyTime_fglssToIndependentSet`,
`polyTimeReducible_GapIndependentSet_of_mem_PCPWith`). Combining the PCP theorem
`NP = PCP(log n, 1)` (`Cslib.Complexity.NP_eq_PCP_log`) with constant-fold independent repetition
(`Cslib.Complexity.PCPWith_one`) and graph complementation
(`polyTimeReducible_GapIndependentSet_GapClique`) shows that for **every constant `0 < s < 1`**,
`GapIndependentSet s` and `GapClique s` are NP-hard (`GapIndependentSet_npHard`, `GapClique_npHard`)
and lie outside `PromiseP` unless `P = NP`. Size-dependent subconstant gaps are not addressed here.

Karp's graph of a formula (`Cslib.Complexity.SAT.toIndependentSet`: a vertex for each occurrence of
a literal, edges inside clauses and between complementary occurrences) also gives a gap-preserving
reduction from MAX-3SAT (`Cslib.Complexity.GapThreeSAT`) [Arora, Lund, Motwani, Sudan and
Szegedy][AroraLundMotwaniSudanSzegedy1998]: an independent set picks consistent literals in distinct
clauses, so it has at most as many vertices as some assignment satisfies clauses
(`Cslib.Complexity.SAT.exists_card_add_countUnsat_le`).

A vertex cover is the complement of an independent set, so `vertexCoverNum G = n - indepNum G` for
the number `n` of distinct declared vertices (`Graph.vertexCoverNum_eq_card_sub_indepNum`). For a
formula with `m` clauses of exactly three, not necessarily distinct, literals
(`Cslib.Complexity.GapExactThreeSAT`), Karp's graph has `n = 3 m` vertices, a satisfiable formula
has a cover of `2 m` vertices, and if every assignment satisfies at most `s * m` clauses every
cover has at least `(3 - s) * m = (1 + (1 - s) / 2) * 2 m` vertices [Arora and Barak, Chapter
11][AroraBarak09]. From the gap `1 - 1 / (3 * 2 ^ 77)` of MAX-E3SAT
(`Cslib.Complexity.GapExactThreeSAT_npHard`), it is NP-hard to approximate the vertex cover number
within `1 + 1 / (3 * 2 ^ 78)`.

With thresholds proportional to the number `n` of vertices instead of an input target
(`Cslib.Complexity.GapVertexCoverFraction`, Goldreich's `gapVC_{s,L}`), the same graph has a cover
of `(2 / 3) n` vertices or none of fewer than `(1 - s / 3) n` vertices, so `gapVC_{s,L}` is NP-hard
for `s = 2 / 3` and `L = 2 / 3 + 1 / (18 * 2 ^ 77)` [Goldreich2007DraftR5], Exercise 10.4.

## Main definitions

* `Cslib.Complexity.GapIndependentSet`, `Cslib.Complexity.GapClique`,
  `Cslib.Complexity.GapVertexCover`: the gap problems.
* `Cslib.Complexity.GapVertexCoverFraction`: vertex cover with thresholds proportional to the
  number of vertices.
* `Cslib.Complexity.PCPVerifier.fglssToIndependentSet`: the FGLSS reduction from a PCP verifier to
  `IndependentSetInstance`.

## Main results

* `Cslib.Complexity.SAT.card_toFinset_vertices_toIndependentSet`: Karp's graph of a formula with
  clauses of three literals has three vertices per clause.
* `Cslib.Complexity.SAT.indepNum_toIndependentSet_le`: the independence number of Karp's graph is
  at most `(1 - unsatVal φ) * m`.
* `Cslib.Complexity.yes_GapIndependentSet`, `Cslib.Complexity.yes_GapClique`: the yes-instances.
* `Cslib.Complexity.PCPVerifier.indepNum_fglssEdgeList`,
  `Cslib.Complexity.PCPVerifier.computableInPolyTime_fglssToIndependentSet`,
  `Cslib.Complexity.polyTimeReducible_GapIndependentSet_of_mem_PCPWith`: the FGLSS gap-preserving
  reduction from `PCP_{1, s}(log n, q)` to `GapIndependentSet s`.
* `Cslib.Complexity.polyTimeReducible_GapThreeSAT_GapIndependentSet`,
  `Cslib.Complexity.polyTimeReducible_GapIndependentSet_GapClique`,
  `Cslib.Complexity.polyTimeReducible_GapExactThreeSAT_GapVertexCover`,
  `Cslib.Complexity.polyTimeReducible_GapExactThreeSAT_GapVertexCoverFraction`: the formula-graph
  and complement gap-preserving reductions.
* `Cslib.Complexity.GapIndependentSet_npHard`, `Cslib.Complexity.GapClique_npHard`: NP-hardness of
  approximating maximum independent set and maximum clique within every constant factor `0 < s < 1`.
* `Cslib.Complexity.GapVertexCover_npHard`, `Cslib.Complexity.GapVertexCoverFraction_npHard`:
  constant-factor inapproximability of minimum vertex cover.
* `Cslib.Complexity.GapIndependentSet_notMem_PromiseP`,
  `Cslib.Complexity.GapClique_notMem_PromiseP`,
  `Cslib.Complexity.GapVertexCover_notMem_PromiseP`: unless `P = NP`, no polynomial-time algorithm
  separates the gap problems.

## References

* [S. Arora, C. Lund, R. Motwani, M. Sudan, M. Szegedy, *Proof verification and the hardness of
  approximation problems*][AroraLundMotwaniSudanSzegedy1998]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 11][AroraBarak09]
* [U. Feige, S. Goldwasser, L. Lovász, S. Safra, M. Szegedy, *Interactive proofs and the hardness
  of approximating cliques*][FeigeGoldwasserLovaszSafraSzegedy1996]
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft
  r5][Goldreich2007DraftR5], Exercise 9.18, Definition 10.4 and Exercise 10.4
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Karp's graph of a formula -/

namespace SAT

/-- Every occurrence of a formula whose clauses have exactly three literals is a vertex of
Karp's graph, and there are `3 m` of them for `m` clauses. -/
theorem card_toFinset_vertices_toIndependentSet {φ : CNF ℕ} (h3 : ∀ c ∈ φ, c.length = 3) :
    (toIndependentSet φ).graph.vertices.toFinset.card = 3 * φ.length := by
  have hset : (toIndependentSet φ).graph.vertices.toFinset =
      (Finset.range φ.length ×ˢ Finset.range 3).image fun p => Nat.pair p.1 p.2 := by
    ext v
    rw [List.mem_toFinset, Finset.mem_image]
    simp only [toIndependentSet, List.mem_map]
    constructor
    · rintro ⟨⟨i, j, l⟩, ho, rfl⟩
      obtain ⟨hi, hj, -⟩ := mem_occurrences.1 ho
      exact ⟨(i, j), Finset.mem_product.2 ⟨Finset.mem_range.2 hi,
        Finset.mem_range.2 ((h3 _ (List.getElem_mem hi)) ▸ hj)⟩, rfl⟩
    · rintro ⟨⟨i, j⟩, hij, rfl⟩
      obtain ⟨hi, hj⟩ := by simpa only [Finset.mem_product, Finset.mem_range] using hij
      have hj' : j < φ[i].length := (h3 _ (List.getElem_mem hi)).symm ▸ hj
      exact ⟨⟨i, j, φ[i][j]⟩, mem_occurrences.2 ⟨hi, hj', rfl⟩, rfl⟩
  rw [hset, Finset.card_image_of_injective _ fun p q h => Prod.ext (Nat.pair_eq_pair.1 h).1
    (Nat.pair_eq_pair.1 h).2, Finset.card_product, Finset.card_range, Finset.card_range,
    Nat.mul_comm]

private theorem toIndependentSet_m (φ : CNF ℕ) : (toIndependentSet φ).m = φ.length :=
  rfl

/-- **The independence number of Karp's graph is at most the largest number of clauses an
assignment satisfies**, which is at most `(1 - unsatVal φ) * m` for `m` clauses. -/
theorem indepNum_toIndependentSet_le (φ : CNF ℕ) :
    ((toIndependentSet φ).graph.indepNum : ℝ) ≤ (1 - φ.unsatVal) * φ.length := by
  obtain ⟨σ, hσ⟩ := (le_indepNum_toIndependentSet_iff φ _).1 le_rfl
  have hcast : ((toIndependentSet φ).graph.indepNum : ℝ) + φ.countUnsat σ ≤ φ.length := mod_cast hσ
  have hle : φ.unsatVal * φ.length ≤ φ.countUnsat σ := by
    rcases Nat.eq_zero_or_pos φ.length with h0 | h0
    · simp [h0]
    · exact (le_div_iff₀ (mod_cast h0)).mp (φ.unsatVal_le σ)
  linarith

/-- A cover of Karp's graph of a formula whose clauses have three literals is the complement of an
independent set among the `3 m` vertices. -/
private theorem vertexCoverNum_toIndependentSet {φ : CNF ℕ} (h3 : ∀ c ∈ φ, c.length = 3) :
    ((toIndependentSet φ).graph.vertexCoverNum : ℝ) =
      3 * φ.length - (toIndependentSet φ).graph.indepNum := by
  have hle := Graph.indepNum_le_card (toIndependentSet φ).graph
  rw [Graph.vertexCoverNum_eq_card_sub_indepNum, Nat.cast_sub hle,
    card_toFinset_vertices_toIndependentSet h3]
  push_cast; ring

end SAT

/-! ### Gap problems -/

/-- The gap problem of **maximum independent set** with soundness `s`: on an instance `x`,
the yes-instances have an independent set of `x.m` declared vertices, and the no-instances have no
independent set of more than `s * x.m` declared vertices. -/
noncomputable def GapIndependentSet (s : ℝ) : PromiseProblem IndependentSetInstance :=
  PromiseProblem.gapMax (fun x => x.graph.indepNum) (fun x => x.m) (fun x => s * x.m)

/-- The gap problem of **maximum clique** with soundness `s`: on an instance `x`, the
yes-instances have a clique of `x.m` declared vertices, and the no-instances have no clique of more
than `s * x.m` declared vertices. -/
noncomputable def GapClique (s : ℝ) : PromiseProblem CliqueInstance :=
  PromiseProblem.gapMax (fun x => x.graph.cliqueNum) (fun x => x.m) (fun x => s * x.m)

/-- The gap problem of **minimum vertex cover** with ratio `r`: on an instance `x`, the
yes-instances have a vertex cover of at most `x.k` declared vertices, and the no-instances have no
vertex cover of fewer than `r * x.k` declared vertices. -/
noncomputable def GapVertexCover (r : ℝ) : PromiseProblem VertexCoverInstance :=
  PromiseProblem.gapMin (fun x => x.graph.vertexCoverNum) (fun x => x.k) (fun x => r * x.k)

/-- The gap problem `gapVC_{s,L}` of **minimum vertex cover with thresholds proportional to the
number of vertices** [Goldreich2007DraftR5], Definition 10.4 and Section 10.1.1.2: the yes-instances
are the graphs with a vertex cover of at most `s * n` declared vertices, and the no-instances are
the graphs with no vertex cover of at most `L * n` declared vertices, for the number `n` of distinct
declared vertices. The draft requires `s ≤ L`; otherwise the no-instances are empty here. Unlike
`GapVertexCover`, the instance carries no target. -/
noncomputable def GapVertexCoverFraction (s L : ℝ) : PromiseProblem Graph where
  yes := {G | (G.vertexCoverNum : ℝ) ≤ s * G.vertices.toFinset.card}
  no := {G | s ≤ L ∧ L * G.vertices.toFinset.card < G.vertexCoverNum}
  disjoint := Set.disjoint_left.2 fun _ hyes hno =>
    lt_irrefl _ ((hyes.trans (mul_le_mul_of_nonneg_right hno.1 (Nat.cast_nonneg _))).trans_lt hno.2)

variable {s r : ℝ}

/-- The yes-instances of `GapIndependentSet` are the members of `IndependentSet`. -/
theorem yes_GapIndependentSet : (GapIndependentSet s).yes = IndependentSet := by
  ext ⟨G, k⟩
  simp only [GapIndependentSet, PromiseProblem.mem_yes_gapMax, Nat.cast_le, Graph.le_indepNum_iff,
    mem_IndependentSet_iff]

/-- The yes-instances of `GapClique` are the members of `Clique`. -/
theorem yes_GapClique : (GapClique s).yes = Clique := by
  ext ⟨G, k⟩
  simp only [GapClique, PromiseProblem.mem_yes_gapMax, Nat.cast_le, Graph.le_cliqueNum_iff,
    mem_Clique_iff]

/-! ### Reductions -/

namespace PCPVerifier

variable {α : Type} (V : PCPVerifier α)

/-- The independence number of the explicit FGLSS edge-list graph equals that of `V.fglssGraph`. -/
theorem indepNum_fglssEdgeList (a : α) :
    (V.fglssEdgeList a).indepNum = (V.fglssGraph a).indepNum :=
  (V.fglssGraphIso a).symm.indepNum_eq

/-- Nonadaptive FGLSS reduction map (after [FeigeGoldwasserLovaszSafraSzegedy1996], Section 3;
[Goldreich2007DraftR5], Exercise 9.18) from an instance `a` of a nonadaptive PCP verifier `V` to
`IndependentSetInstance`: the explicit accepting-view conflict graph `V.fglssEdgeList a` paired with
target `2 ^ V.coins a`. -/
def fglssToIndependentSet (a : α) : IndependentSetInstance :=
  ⟨V.fglssEdgeList a, 2 ^ V.coins a⟩

/-- Under a logarithmic coin bound and a constant query bound on valid random strings, the FGLSS
reduction `V.fglssToIndependentSet` is computable in polynomial time. -/
theorem computableInPolyTime_fglssToIndependentSet {enc : α ↪ List Bool} (hV : V.PolyTime enc)
    {c d : ℕ} (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    (hq : ∀ a ρ, ρ.length = V.coins a → (V.queries (a, ρ)).length ≤ d) :
    ComputableInPolyTime V.fglssToIndependentSet enc encIndependentSetInstance := by
  have hgraph := V.computableInPolyTime_fglssEdgeList hV hcoins hq
  have htarget : ComputableInPolyTime (fun a => 2 ^ V.coins a) enc encNat :=
    ComputableInPolyTime.binary_two_pow.comp
      (.binary_to_unary_bounded hV.coins (by fun_prop) hcoins)
  unfold fglssToIndependentSet
  fun_prop

end PCPVerifier

/-- Nonadaptive FGLSS gap-reduction step toward [Goldreich2007DraftR5], Exercise 9.18 (#4772) and
[Arora and Barak, Chapter 11][AroraBarak09] (#4711), after [FeigeGoldwasserLovaszSafraSzegedy1996],
Section 3: every problem in `PCP_{1, s}(log n, q)` (for nonadaptive `PCPVerifier`) with constant
query bound `q` and soundness `s < 1` reduces in polynomial time to `GapIndependentSet s` via
`PCPVerifier.fglssToIndependentSet`. -/
theorem polyTimeReducible_GapIndependentSet_of_mem_PCPWith {α : Type} {enc : α ↪ List Bool}
    {A : Set α} {q : ℕ} (hs1 : s < 1)
    (hA : A ∈ PCPWith 1 s (fun n => Nat.log 2 n + 1) (fun _ => q) enc) :
    PromiseProblem.PolyTimeReducible enc encIndependentSetInstance (.ofSet A)
      (GapIndependentSet s) := by
  obtain ⟨V, c_r, c_q, hV, hpcp⟩ := hA
  refine ⟨V.fglssToIndependentSet,
    V.computableInPolyTime_fglssToIndependentSet hV hpcp.coins_le hpcp.length_queries_le,
    fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨π, hπ⟩ := hpcp.complete a ha
    have hacc : V.acceptCount a π = 2 ^ V.coins a :=
      (V.acceptCount_eq_two_pow_iff a π).mpr ((V.one_le_acceptProb_iff a π).mp hπ)
    have hind : (V.fglssGraph a).indepNum = 2 ^ V.coins a :=
      le_antisymm (V.indepNum_fglssGraph_le a)
        (hacc ▸ PCPVerifier.acceptCount_le_indepNum_fglssGraph π)
    simp only [GapIndependentSet, PromiseProblem.mem_yes_gapMax, PCPVerifier.fglssToIndependentSet,
      PCPVerifier.indepNum_fglssEdgeList, hind, le_rfl]
  · obtain ⟨π, hπ⟩ := V.exists_acceptCount_eq_indepNum_fglssGraph a
    have hpos : (0 : ℝ) < 2 ^ V.coins a := by positivity
    have hprob : (V.acceptCount a π : ℝ) ≤ s * (2 ^ V.coins a : ℕ) := by
      simpa only [PCPVerifier.acceptProb, div_le_iff₀ hpos, Nat.cast_pow, Nat.cast_ofNat] using
        hpcp.sound a ha π
    refine (PromiseProblem.mem_no_gapMax_of_lt
      (show s * (2 ^ V.coins a : ℕ) < (2 ^ V.coins a : ℕ) by push_cast; nlinarith)).2 ?_
    dsimp only [PCPVerifier.fglssToIndependentSet]
    rwa [PCPVerifier.indepNum_fglssEdgeList, ← hπ]

/-- **MAX-3SAT reduces to maximum independent set with the same gap**, by Karp's graph: a
satisfiable formula has an independent set with a vertex in each clause, and an independent set
gives an assignment satisfying as many clauses. -/
theorem polyTimeReducible_GapThreeSAT_GapIndependentSet (hs : s < 1) :
    PromiseProblem.PolyTimeReducible encCNF encIndependentSetInstance (GapThreeSAT s)
      (GapIndependentSet s) := by
  refine ⟨SAT.toIndependentSet, SAT.computableInPolyTime_toIndependentSet,
    fun φ hφ => yes_GapIndependentSet.symm ▸ (SAT.toIndependentSet_mem_iff φ).2
      (yes_GapThreeSAT ▸ hφ).2, fun φ hφ => ?_⟩
  obtain ⟨-, hval⟩ := (mem_no_GapThreeSAT hs).1 hφ
  have hm : (0 : ℝ) < φ.length := mod_cast CNF.length_pos_of_unsatVal_pos (by linarith)
  have hα := SAT.indepNum_toIndependentSet_le φ
  exact (PromiseProblem.mem_no_gapMax_of_lt (show s * (φ.length : ℝ) < φ.length by nlinarith)).2
    (show ((SAT.toIndependentSet φ).graph.indepNum : ℝ) ≤ s * φ.length by nlinarith)

/-- **Maximum independent set reduces to maximum clique with the same gap**, by complementing the
graph on its declared vertices. -/
theorem polyTimeReducible_GapIndependentSet_GapClique :
    PromiseProblem.PolyTimeReducible encIndependentSetInstance encCliqueInstance
      (GapIndependentSet s) (GapClique s) :=
  ⟨independentSetToClique, computableInPolyTime_independentSetToClique,
    fun x hx => by simpa [GapIndependentSet, GapClique, independentSetToClique,
      Graph.cliqueNum_compl] using hx,
    fun x hx => by simpa [GapIndependentSet, GapClique, independentSetToClique,
      Graph.cliqueNum_compl] using hx⟩

/-- **MAX-E3SAT reduces to minimum vertex cover**: Karp's graph of a formula with `m` clauses of
three, not necessarily distinct, literals has `3 m` vertices, so the target `m` of an independent
set becomes the target `2 m` of a vertex cover (`IndependentSet.toVertexCover`), and soundness `s`
for MAX-E3SAT becomes the ratio `1 + (1 - s) / 2` for vertex covers. -/
theorem polyTimeReducible_GapExactThreeSAT_GapVertexCover (hs : s < 1) :
    PromiseProblem.PolyTimeReducible encCNF encVertexCoverInstance (GapExactThreeSAT s)
      (GapVertexCover (1 + (1 - s) / 2)) := by
  have hred (φ : CNF ℕ) (h3 : ∀ c ∈ φ, c.length = 3) :
      IndependentSet.toVertexCover (SAT.toIndependentSet φ) =
        ⟨(SAT.toIndependentSet φ).graph, 2 * φ.length⟩ := by
    have hle : φ.length ≤ 3 * φ.length := by omega
    rw [IndependentSet.toVertexCover, SAT.card_toFinset_vertices_toIndependentSet h3,
      SAT.toIndependentSet_m, ite_eq_left hle]
    congr 1
    omega
  refine ⟨fun φ => IndependentSet.toVertexCover (SAT.toIndependentSet φ),
    IndependentSet.computableInPolyTime_toVertexCover.comp
      SAT.computableInPolyTime_toIndependentSet, fun φ hφ => ?_, fun φ hφ => ?_⟩
  · obtain ⟨h3, hsat⟩ := yes_GapExactThreeSAT ▸ hφ
    have hα : (φ.length : ℝ) ≤ (SAT.toIndependentSet φ).graph.indepNum :=
      mod_cast Graph.le_indepNum_iff.2 ((SAT.toIndependentSet_mem_iff φ).2 hsat)
    simp only [GapVertexCover, PromiseProblem.mem_yes_gapMin, hred φ h3,
      SAT.vertexCoverNum_toIndependentSet h3]
    cast_linarith
  · obtain ⟨h3, hval⟩ := (mem_no_GapExactThreeSAT hs).1 hφ
    have hm : (0 : ℝ) < φ.length := mod_cast CNF.length_pos_of_unsatVal_pos (by linarith)
    have hα := SAT.indepNum_toIndependentSet_le φ
    simp only [GapVertexCover, PromiseProblem.mem_no_gapMin, hred φ h3,
      SAT.vertexCoverNum_toIndependentSet h3]
    push_cast
    constructor <;> nlinarith

/-- **MAX-E3SAT reduces to vertex cover with thresholds proportional to the number of vertices**:
Karp's graph of a formula with `m` clauses of three, not necessarily distinct, literals has
`n = 3 m` vertices, a satisfiable formula has a cover of `2 m = (2 / 3) n` vertices, and if every
assignment satisfies at most `s * m` clauses every cover has at least `(3 - s) m = (1 - s / 3) n`
vertices, more than `L * n` for `L < 1 - s / 3`. -/
theorem polyTimeReducible_GapExactThreeSAT_GapVertexCoverFraction (hs : s < 1) {L : ℝ}
    (hL : 2 / 3 ≤ L) (hLs : L < 1 - s / 3) :
    PromiseProblem.PolyTimeReducible encCNF encGraph (GapExactThreeSAT s)
      (GapVertexCoverFraction (2 / 3) L) := by
  refine ⟨fun φ => (SAT.toIndependentSet φ).graph,
    by have h := SAT.computableInPolyTime_toIndependentSet; fun_prop,
    fun φ hφ => ?_, fun φ hφ => ?_⟩
  · obtain ⟨h3, hsat⟩ := yes_GapExactThreeSAT ▸ hφ
    have hα : (φ.length : ℝ) ≤ (SAT.toIndependentSet φ).graph.indepNum :=
      mod_cast Graph.le_indepNum_iff.2 ((SAT.toIndependentSet_mem_iff φ).2 hsat)
    simp only [GapVertexCoverFraction, Set.mem_ofPred_eq, SAT.vertexCoverNum_toIndependentSet h3,
      SAT.card_toFinset_vertices_toIndependentSet h3]
    cast_linarith
  · obtain ⟨h3, hval⟩ := (mem_no_GapExactThreeSAT hs).1 hφ
    have hm : (0 : ℝ) < φ.length := mod_cast CNF.length_pos_of_unsatVal_pos (by linarith)
    have hα := SAT.indepNum_toIndependentSet_le φ
    simp only [GapVertexCoverFraction, Set.mem_ofPred_eq, SAT.vertexCoverNum_toIndependentSet h3,
      SAT.card_toFinset_vertices_toIndependentSet h3]
    exact ⟨hL, by cast_nlinarith⟩

/-! ### Inapproximability -/

/-- **Constant-factor NP-hardness of maximum independent set** ([Goldreich2007DraftR5],
Exercise 9.18, final claim; constant-factor specialization after
[FeigeGoldwasserLovaszSafraSzegedy1996], Section 3 and [AroraLundMotwaniSudanSzegedy1998]): for
every fixed constant `0 < s < 1`, distinguishing graphs with an independent set of `k` declared
vertices from graphs without an independent set of more than `s * k` declared vertices is NP-hard.
The proof amplifies `NP = PCP(log n, 1)` (`Cslib.Complexity.NP_eq_PCP_log`) to soundness `s` by
independent verifier repetition (`Cslib.Complexity.PCPWith_one`) and applies the nonadaptive FGLSS
reduction (`Cslib.Complexity.polyTimeReducible_GapIndependentSet_of_mem_PCPWith`). Size-dependent
subconstant gaps (#4772, #4711) remain open. -/
theorem GapIndependentSet_npHard (hs0 : 0 < s) (hs1 : s < 1) :
    PromiseProblem.NPHard encIndependentSetInstance (GapIndependentSet s) := by
  intro _ enc A hA
  rw [NP_eq_PCP_log, ← PCPWith_one hs0 hs1] at hA
  exact polyTimeReducible_GapIndependentSet_of_mem_PCPWith hs1 hA

/-- **Constant-factor NP-hardness of maximum clique** ([Goldreich2007DraftR5], Exercise 9.18, final
claim; constant-factor specialization after [FeigeGoldwasserLovaszSafraSzegedy1996], Section 3 and
[AroraLundMotwaniSudanSzegedy1998]): for every fixed constant `0 < s < 1`, distinguishing graphs
with a clique of `k` declared vertices from graphs without a clique of more than `s * k` declared
vertices is NP-hard. The gap of maximum independent set transfers to the complement graph;
size-dependent subconstant gaps (#4772, #4711) remain open. -/
theorem GapClique_npHard (hs0 : 0 < s) (hs1 : s < 1) :
    PromiseProblem.NPHard encCliqueInstance (GapClique s) :=
  (GapIndependentSet_npHard hs0 hs1).trans polyTimeReducible_GapIndependentSet_GapClique

/-- **Minimum vertex cover is NP-hard to approximate** within `1 + 1 / (3 * 2 ^ 78)`
[AroraLundMotwaniSudanSzegedy1998]: given a graph and a target `k`, distinguishing graphs with a
vertex cover of at most `k` vertices from graphs without a vertex cover of fewer than
`(1 + 1 / (3 * 2 ^ 78)) * k` vertices is NP-hard. -/
theorem GapVertexCover_npHard :
    PromiseProblem.NPHard encVertexCoverInstance
      (GapVertexCover (1 + 1 / (3 * 2 ^ 78))) := by
  have h : (1 + (1 - (1 - 1 / (3 * 2 ^ 77))) / 2 : ℝ) = 1 + 1 / (3 * 2 ^ 78) := by norm_num
  exact fun _ enc A hA => (GapExactThreeSAT_npHard enc A hA).trans
    (h ▸ polyTimeReducible_GapExactThreeSAT_GapVertexCover (by norm_num))

/-- **Minimum vertex cover is NP-hard to approximate relative to the number of vertices**
([Goldreich2007DraftR5], Exercise 10.4, a weak version of Theorem 10.7): for the constants
`s = 2 / 3 < L = 2 / 3 + 1 / (18 * 2 ^ 77) < 1`, distinguishing graphs with a vertex cover of at
most `s * n` of their `n` vertices from graphs with none of at most `L * n` vertices is NP-hard. As
the exercise asks, the proof uses the PCP Theorem (Theorem 9.16, here through the MAX-3SAT gap
`GapExactThreeSAT_npHard`), but it passes through Karp's graph of a formula rather than the
FGLSS clique reduction of the draft's guideline. -/
theorem GapVertexCoverFraction_npHard :
    PromiseProblem.NPHard encGraph
      (GapVertexCoverFraction (2 / 3) (2 / 3 + 1 / (18 * 2 ^ 77))) :=
  fun _ enc A hA => (GapExactThreeSAT_npHard enc A hA).trans
    (polyTimeReducible_GapExactThreeSAT_GapVertexCoverFraction (by norm_num) (by norm_num)
      (by norm_num))

/-- Unless `P = NP`, for every `0 < s < 1`, no polynomial-time algorithm distinguishes graphs with
an independent set of `k` declared vertices from graphs without one of more than `s * k` declared
vertices. -/
theorem GapIndependentSet_notMem_PromiseP (hs0 : 0 < s) (hs1 : s < 1) {β : Type}
    {enc : β ↪ List Bool} (h : P enc ≠ NP enc) :
    GapIndependentSet s ∉ PromiseP encIndependentSetInstance :=
  (GapIndependentSet_npHard hs0 hs1).notMem_PromiseP h

/-- Unless `P = NP`, for every `0 < s < 1`, no polynomial-time algorithm distinguishes graphs with a
clique of `k` declared vertices from graphs without one of more than `s * k` declared vertices. -/
theorem GapClique_notMem_PromiseP (hs0 : 0 < s) (hs1 : s < 1) {β : Type} {enc : β ↪ List Bool}
    (h : P enc ≠ NP enc) :
    GapClique s ∉ PromiseP encCliqueInstance :=
  (GapClique_npHard hs0 hs1).notMem_PromiseP h

/-- Unless `P = NP`, no polynomial-time algorithm distinguishes graphs with a vertex cover of at
most `k` vertices from graphs without one of fewer than `(1 + 1 / (3 * 2 ^ 78)) * k` vertices. -/
theorem GapVertexCover_notMem_PromiseP {β : Type} {enc : β ↪ List Bool} (h : P enc ≠ NP enc) :
    GapVertexCover (1 + 1 / (3 * 2 ^ 78)) ∉ PromiseP encVertexCoverInstance :=
  GapVertexCover_npHard.notMem_PromiseP h

end Cslib.Complexity
