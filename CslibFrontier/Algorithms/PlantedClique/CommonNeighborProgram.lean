/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.PlantedClique.Program
public import CslibFrontier.Algorithms.PlantedClique.Representation
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.CommonNeighborhood
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.ListsUpTo
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Foundations.Data.List.RowMajor
import Mathlib.Data.List.GetD

/-!
# A uniform common-neighbor wrapper for clique recovery

For a fixed seed size, the wrapper enumerates distinct vertex lists of that length, restricts
the input to their common neighbors, calls a supplied recovery function with the reduced target
size, lifts its output identifiers, and checks the resulting clique. It returns the first
verified candidate, or the empty list when no candidate is accepted.

This implements the enumeration and verification mechanism of Algorithm B in Section 2.3 of
[Alon, Krivelevich, Sudakov][AlonKrivelevichSudakov1998]. Lists enumerate each seed set in several
orders, which does not change the common neighborhood. The fallback is the empty list, rather
than an arbitrary target-sized set. The native certificate is uniform in the dense input;
the seed size is fixed before the machine is chosen. No polynomial-time claim treats a varying
seed size as part of the input.

The deterministic success lemma is a step toward the probabilistic theorem: it uses a successful
planted seed and uniqueness of the target-sized clique. Those are mathematical obligations of
the random-graph analysis, not premises of the runtime certificate.
-/

public section

namespace Cslib.Algorithms.PlantedClique

open Turing.MultiTapeTM

namespace RecoveryInput

/-- Declared vertices outside the seed list that are adjacent to every seed entry, in increasing
identifier order. Repeated seed entries impose the same adjacency condition. -/
@[expose] def commonVertices (x : RecoveryInput) (seed : List ℕ) : List ℕ :=
  (List.range x.vertexCount).filter fun v =>
    !(seed.any fun t => decide (v = t)) && seed.all (fun t => x.adjacent t v)

/-- The dense subgraph on a list of identifiers, relabeled in list order, with a supplied target
size. The symmetric decoder remains total on arbitrary identifier lists. -/
@[expose] def inducedInput (x : RecoveryInput) (vertices : List ℕ) (k : ℕ) : RecoveryInput where
  vertexCount := vertices.length
  cliqueSize := k
  adjacencyBits := vertices.flatMap fun i => vertices.map (x.adjacent i)

/-- Check that a list consists of exactly the requested number of distinct declared vertices
and that each pair of distinct identifiers is adjacent. -/
@[expose] def validatesClique (x : RecoveryInput) (candidate : List ℕ) : Bool :=
  decide (candidate.length = x.cliqueSize) && decide candidate.Nodup &&
    candidate.all (fun i => decide (i < x.vertexCount)) &&
      candidate.all (fun i => candidate.all fun j => decide (i = j) || x.adjacent i j)

/-- Common-neighbor restriction computes only declared vertex identifiers. -/
theorem mem_commonVertices_lt (x : RecoveryInput) (seed : List ℕ) {v : ℕ}
    (hv : v ∈ x.commonVertices seed) : v < x.vertexCount :=
  List.mem_range.mp (List.mem_filter.mp hv).1

/-- A common-neighbor list contains no repeated identifier. -/
theorem nodup_commonVertices (x : RecoveryInput) (seed : List ℕ) :
    (x.commonVertices seed).Nodup :=
  List.nodup_range.filter _

/-- The increasing inclusion of the stored common-neighbor vertices into the original graph. -/
@[expose] def commonVertexEmbedding (x : RecoveryInput) (seed : List ℕ) :
    Fin (x.commonVertices seed).length ↪o Fin x.vertexCount :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨(x.commonVertices seed).get i,
      x.mem_commonVertices_lt seed (List.get_mem _ _)⟩)
    (fun _ _ hij => (List.pairwise_lt_range.filter _).rel_get_of_lt hij)

/-- Every stored common-neighbor identifier occurs exactly once in the increasing inclusion. -/
theorem image_commonVertexEmbedding (x : RecoveryInput) (seed : List ℕ) :
    Finset.univ.image (x.commonVertexEmbedding seed) =
      vertexSet x.vertexCount (x.commonVertices seed) := by
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and, vertexSet, Finset.mem_filter]
  constructor
  · rintro ⟨i, rfl⟩
    exact List.get_mem _ _
  · intro hv
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
    exact ⟨i, Fin.ext hi⟩

/-- The runtime list denotes the finite common neighborhood of its seed set. -/
theorem vertexSet_commonVertices (x : RecoveryInput) (seed : List ℕ)
    (hbound : ∀ i ∈ seed, i < x.vertexCount) :
    vertexSet x.vertexCount (x.commonVertices seed) =
      x.graph.commonNeighborhood (vertexSet x.vertexCount seed) := by
  ext v
  have hleft : v ∈ vertexSet x.vertexCount (x.commonVertices seed) ↔
      v.val ∉ seed ∧ ∀ t ∈ seed, x.adjacent t v = true := by
    have hnot : (∀ t ∈ seed, ¬v.val = t) ↔ v.val ∉ seed := by
      constructor
      · exact fun h hv => h _ hv rfl
      · intro h t ht heq
        exact h (heq.symm ▸ ht)
    simp [vertexSet, commonVertices, List.all_eq_true, hnot]
  rw [hleft, SimpleGraph.mem_commonNeighborhood]
  simp only [vertexSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hv, hall⟩
    exact ⟨hv, fun t ht => hall t ht⟩
  · rintro ⟨hv, hall⟩
    exact ⟨hv, fun t ht => hall ⟨t, hbound t ht⟩ ht⟩

/-- Reading the dense induced input agrees with graph pullback along the identifier list.
The embedding premise records that the listed identifiers are distinct declared vertices. -/
theorem graph_inducedInput (x : RecoveryInput) (vertices : List ℕ) (k : ℕ)
    (e : Fin vertices.length ↪ Fin x.vertexCount)
    (he : ∀ i, (e i).val = vertices.get i) :
    (x.inducedInput vertices k).graph = x.graph.comap e := by
  have hread (i j : Fin vertices.length) :
      (vertices.flatMap fun a => vertices.map (x.adjacent a)).getD
        (i.val * vertices.length + j.val) false = x.adjacent (vertices.get i) (vertices.get j) := by
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_flatMap_mul_add vertices _ vertices.length
        (fun a _ => List.length_map _) i.isLt j.isLt]
    simp
  ext i j
  change Fin vertices.length at i j
  change (i.val != j.val && (vertices.flatMap fun a => vertices.map (x.adjacent a)).getD
    (min i.val j.val * vertices.length + max i.val j.val) false) = true ↔
      x.graph.Adj (e i) (e j)
  rcases le_total i.val j.val with hij | hij
  · rw [min_eq_left hij, max_eq_right hij, hread, ← he i, ← he j]
    simp only [Bool.and_eq_true, bne_iff_ne]
    exact ⟨And.right, fun h => ⟨fun hv => h.ne (congrArg e (Fin.ext hv)), h⟩⟩
  · rw [min_eq_right hij, max_eq_left hij, hread, ← he j, ← he i]
    simp only [Bool.and_eq_true, bne_iff_ne]
    change (i.val ≠ j.val ∧ x.graph.Adj (e j) (e i)) ↔ x.graph.Adj (e i) (e j)
    exact ⟨fun h => h.2.symm, fun h => ⟨fun hv => h.ne (congrArg e (Fin.ext hv)), h.symm⟩⟩

/-- The verifier accepts exactly lists of distinct declared identifiers representing a clique
with the requested cardinality. -/
theorem validatesClique_eq_true_iff (x : RecoveryInput) (candidate : List ℕ) :
    x.validatesClique candidate = true ↔ candidate.Nodup ∧
      (∀ i ∈ candidate, i < x.vertexCount) ∧
      x.graph.IsClique (vertexSet x.vertexCount candidate : Set (Fin x.vertexCount)) ∧
      (vertexSet x.vertexCount candidate).card = x.cliqueSize := by
  have hraw : x.validatesClique candidate = true ↔
      candidate.length = x.cliqueSize ∧ candidate.Nodup ∧
        (∀ i ∈ candidate, i < x.vertexCount) ∧
        ∀ i ∈ candidate, ∀ j ∈ candidate, i = j ∨ x.adjacent i j = true := by
    simp [validatesClique, List.all_eq_true, and_assoc]
  rw [hraw]
  constructor
  · rintro ⟨hlen, hnodup, hbound, hpairs⟩
    refine ⟨hnodup, hbound, ?_, (card_vertexSet_of_nodup candidate hnodup hbound).trans hlen⟩
    intro i hi j hj hij
    have hi' : i.val ∈ candidate := by simpa only [vertexSet, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_univ, true_and] using hi
    have hj' : j.val ∈ candidate := by simpa only [vertexSet, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_univ, true_and] using hj
    rcases hpairs i hi' j hj' with heq | hAdj
    · exact (hij (Fin.ext heq)).elim
    · exact hAdj
  · rintro ⟨hnodup, hbound, hclique, hcard⟩
    refine ⟨(card_vertexSet_of_nodup candidate hnodup hbound).symm.trans hcard,
      hnodup, hbound, ?_⟩
    intro i hi j hj
    by_cases hij : i = j
    · exact Or.inl hij
    · right
      exact hclique (by simpa [vertexSet] using hi) (by simpa [vertexSet] using hj)
        (show (⟨i, hbound i hi⟩ : Fin x.vertexCount) ≠ ⟨j, hbound j hj⟩ from
          fun h => hij (congrArg Fin.val h))

/-- Common-neighbor restriction is native polynomial-time for arbitrary encoded seed lists. -/
@[fun_prop] theorem computableInPolyTime_commonVertices {α : Type} {encIn : α ↪ List Bool}
    {input : α → RecoveryInput} {seed : α → List ℕ}
    (hx : ComputableInPolyTime input encIn encRecoveryInput)
    (hseed : ComputableInPolyTime seed encIn (encList encUnary)) :
    ComputableInPolyTime (fun a => (input a).commonVertices (seed a))
      encIn (encList encUnary) := by
  unfold commonVertices
  fun_prop

/-- Building every row of the induced dense input is native polynomial-time, including the
stored adjacency word and its new unary dimensions. -/
@[fun_prop] theorem computableInPolyTime_inducedInput {α : Type} {encIn : α ↪ List Bool}
    {input : α → RecoveryInput} {vertices : α → List ℕ} {k : α → ℕ}
    (hx : ComputableInPolyTime input encIn encRecoveryInput)
    (hv : ComputableInPolyTime vertices encIn (encList encUnary))
    (hk : ComputableInPolyTime k encIn encUnary) :
    ComputableInPolyTime (fun a => (input a).inducedInput (vertices a) (k a))
      encIn encRecoveryInput := by
  have hbits : ComputableInPolyTime
      (fun a => (vertices a).flatMap fun i => (vertices a).map ((input a).adjacent i))
      encIn encBits :=
    ComputableInPolyTime.listToBits.comp (by fun_prop)
  unfold inducedInput
  fun_prop

/-- The full size, distinctness, range and pairwise-adjacency verifier is polynomial-time. -/
@[fun_prop] theorem computableInPolyTime_validatesClique {α : Type} {encIn : α ↪ List Bool}
    {input : α → RecoveryInput} {candidate : α → List ℕ}
    (hx : ComputableInPolyTime input encIn encRecoveryInput)
    (hc : ComputableInPolyTime candidate encIn (encList encUnary)) :
    ComputableInPolyTime (fun a => (input a).validatesClique (candidate a)) encIn encBool := by
  have hn := ComputableInPolyTime.decide_nodup hc
  unfold validatesClique
  fun_prop

end RecoveryInput

private def seedLists (n s : ℕ) : List (List ℕ) :=
  ((List.range n).listsUpTo s).filter fun seed => decide (seed.length = s) && decide seed.Nodup

private theorem mem_seedLists {n s : ℕ} {seed : List ℕ} :
    seed ∈ seedLists n s ↔ seed.length = s ∧ seed.Nodup ∧ ∀ v ∈ seed, v < n := by
  simp only [seedLists, List.mem_filter, List.mem_listsUpTo, List.mem_range,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨_, hbound⟩, hlen, hnodup⟩
    exact ⟨hlen, hnodup, hbound⟩
  · rintro ⟨hlen, hnodup, hbound⟩
    exact ⟨⟨hlen.le, hbound⟩, hlen, hnodup⟩

/-- Try one seed: recover in its common-neighbor graph, lift valid local identifiers, and return
the canonical increasing list of the union with the seed. -/
@[expose] def commonNeighborCandidate (solve : RecoveryInput → List ℕ)
    (x : RecoveryInput) (seed : List ℕ) : List ℕ :=
  let vertices := x.commonVertices seed
  let selected := solve (x.inducedInput vertices (x.cliqueSize - seed.length))
  (List.range x.vertexCount).filter fun v =>
    (seed.any fun t => decide (v = t)) ||
      selected.any fun j => decide (j < vertices.length) && decide (v = vertices.getD j 0)

/-- Enumerate all distinct seeds of a fixed size, try the supplied recovery function on their
common-neighbor graphs, and return the first verified target-sized clique, or the empty list. -/
def commonNeighborRecover (solve : RecoveryInput → List ℕ) (s : ℕ)
    (x : RecoveryInput) : List ℕ :=
  (((seedLists x.vertexCount s).map (commonNeighborCandidate solve x)).find?
    x.validatesClique).getD []

/-- Every single-seed output is a list of distinct declared identifiers. -/
theorem commonNeighborCandidate_nodup (solve : RecoveryInput → List ℕ)
    (x : RecoveryInput) (seed : List ℕ) : (commonNeighborCandidate solve x seed).Nodup :=
  List.nodup_range.filter _

/-- Lifting and canonicalizing a single-seed output never creates an undeclared vertex. -/
theorem mem_commonNeighborCandidate_lt (solve : RecoveryInput → List ℕ)
    (x : RecoveryInput) (seed : List ℕ) {v : ℕ}
    (hv : v ∈ commonNeighborCandidate solve x seed) : v < x.vertexCount :=
  List.mem_range.mp (List.mem_filter.mp hv).1

/-- A single-seed candidate denotes precisely the seed set together with the lifted bounded
identifiers produced by the reduced solver. Invalid local identifiers do not name vertices. -/
theorem vertexSet_commonNeighborCandidate (solve : RecoveryInput → List ℕ)
    (x : RecoveryInput) (seed : List ℕ) :
    vertexSet x.vertexCount (commonNeighborCandidate solve x seed) =
      vertexSet x.vertexCount seed ∪
        (vertexSet (x.commonVertices seed).length
          (solve (x.inducedInput (x.commonVertices seed) (x.cliqueSize - seed.length)))).image
            (x.commonVertexEmbedding seed) := by
  ext v
  simp only [vertexSet, Finset.mem_filter, Finset.mem_univ, true_and,
    commonNeighborCandidate, List.mem_filter, List.mem_range, v.isLt,
    Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq, Bool.and_eq_true,
    Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨t, ht, heq⟩ | ⟨j, hj, hbound, heq⟩)
    · exact Or.inl (heq.symm ▸ ht)
    · right
      refine ⟨⟨j, hbound⟩, hj, Fin.ext ?_⟩
      exact (List.getD_eq_get _ 0 (⟨j, hbound⟩ : Fin (x.commonVertices seed).length)).symm.trans
        heq.symm
  · rintro (hv | ⟨i, hi, rfl⟩)
    · exact Or.inl ⟨v, hv, rfl⟩
    · exact Or.inr ⟨i, hi, i.isLt, (List.getD_eq_get _ 0 i).symm⟩

/-- Recovering exactly the retained planted vertices makes a single planted-seed attempt
return the whole planted set. This deterministic step imposes no assumption on other seeds. -/
theorem commonNeighborCandidate_eq_of_recovery (solve : RecoveryInput → List ℕ)
    (x : RecoveryInput) (seed : List ℕ) (S : Finset (Fin x.vertexCount))
    (hbound : ∀ i ∈ seed, i < x.vertexCount) (hseed : vertexSet x.vertexCount seed ⊆ S)
    (hclique : x.graph.IsClique (S : Set (Fin x.vertexCount)))
    (hrec : vertexSet (x.commonVertices seed).length
      (solve (x.inducedInput (x.commonVertices seed) (x.cliqueSize - seed.length))) =
        Finset.univ.filter fun i => x.commonVertexEmbedding seed i ∈ S) :
    vertexSet x.vertexCount (commonNeighborCandidate solve x seed) = S := by
  rw [vertexSet_commonNeighborCandidate, hrec, ← Finset.filter_image (p := fun v => v ∈ S),
    x.image_commonVertexEmbedding seed, x.vertexSet_commonVertices seed hbound,
    Finset.filter_mem_eq_inter, Finset.inter_comm,
    x.graph.inter_commonNeighborhood_eq_sdiff hseed hclique,
    Finset.union_sdiff_of_subset hseed]

open scoped Classical in
/-- The canonical common-neighborhood recovery event used in probability estimates implies
success of the actual list program. Increasing enumeration identifies the canonical finite
graph with the runtime induced input, including its reduced target size. -/
theorem commonNeighborCandidate_recoverInput_eq_of_recover
    (x : RecoveryInput) (seed : List ℕ) (S : Finset (Fin x.vertexCount))
    (hcard : S.card = x.cliqueSize) (hnodup : seed.Nodup)
    (hbound : ∀ i ∈ seed, i < x.vertexCount) (hseed : vertexSet x.vertexCount seed ⊆ S)
    (hclique : x.graph.IsClique (S : Set (Fin x.vertexCount)))
    (hrec : let U := x.graph.commonNeighborhood (vertexSet x.vertexCount seed)
      let e := U.orderEmbOfFin rfl
      recover (x.graph.comap e) (S.card - (vertexSet x.vertexCount seed).card) =
        Finset.univ.filter fun i => e i ∈ S) :
    vertexSet x.vertexCount (commonNeighborCandidate recoverInput x seed) = S := by
  classical
  apply commonNeighborCandidate_eq_of_recovery recoverInput x seed S hbound hseed hclique
  let U := x.graph.commonNeighborhood (vertexSet x.vertexCount seed)
  have hlen : U.card = (x.commonVertices seed).length := by
    dsimp only [U]
    rw [← x.vertexSet_commonVertices seed hbound]
    exact card_vertexSet_of_nodup _ (x.nodup_commonVertices seed)
      (fun v hv => x.mem_commonVertices_lt seed hv)
  have he : x.commonVertexEmbedding seed = U.orderEmbOfFin hlen := by
    apply Finset.orderEmbOfFin_unique' hlen
    intro i
    dsimp only [U]
    rw [← x.vertexSet_commonVertices seed hbound]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, List.get_mem _ _⟩
  have hcanon : ∀ m (hm : U.card = m),
      recover (x.graph.comap (U.orderEmbOfFin hm))
        (S.card - (vertexSet x.vertexCount seed).card) =
          Finset.univ.filter fun i => U.orderEmbOfFin hm i ∈ S := by
    intro m hm
    subst m
    exact hrec
  have hrec' := hcanon _ hlen
  rw [← he, hcard, card_vertexSet_of_nodup seed hnodup hbound] at hrec'
  have hout := vertexSet_eq_of_toFinset_eq_image
    (toFinset_recoverInput
      (x.inducedInput (x.commonVertices seed) (x.cliqueSize - seed.length)))
  change vertexSet (x.commonVertices seed).length
      (recoverInput (x.inducedInput (x.commonVertices seed) (x.cliqueSize - seed.length))) =
    recover (x.inducedInput (x.commonVertices seed) (x.cliqueSize - seed.length)).graph
      (x.cliqueSize - seed.length) at hout
  have hclass := congrArg
    (fun G : SimpleGraph (Fin (x.commonVertices seed).length) =>
      @recover _ G (fun _ _ => Classical.propDecidable _) (x.cliqueSize - seed.length))
    (x.graph_inducedInput _ (x.cliqueSize - seed.length)
      (x.commonVertexEmbedding seed).toEmbedding (fun _ => rfl))
  simp only [recover_eq_classical] at hout hrec'
  exact hout.trans (hclass.trans hrec')

/-- A deterministic step of the common-neighbor argument: a successful enumerated seed yields
the planted set when it is the unique target-sized clique. Probability estimates must discharge
the successful-seed and uniqueness premises separately. -/
theorem commonNeighborRecover_eq_of_successful_seed
    (solve : RecoveryInput → List ℕ) (s : ℕ) (x : RecoveryInput)
    (S : Finset (Fin x.vertexCount)) (hcard : S.card = x.cliqueSize)
    (hclique : x.graph.IsClique (S : Set (Fin x.vertexCount)))
    (hunique : ∀ Q : Finset (Fin x.vertexCount),
      x.graph.IsClique (Q : Set (Fin x.vertexCount)) → Q.card = S.card → Q = S)
    (seed : List ℕ) (hlen : seed.length = s) (hnodup : seed.Nodup)
    (hbound : ∀ v ∈ seed, v < x.vertexCount)
    (hsuccess : vertexSet x.vertexCount (commonNeighborCandidate solve x seed) = S) :
    vertexSet x.vertexCount (commonNeighborRecover solve s x) = S := by
  have hvalid : x.validatesClique (commonNeighborCandidate solve x seed) = true := by
    rw [x.validatesClique_eq_true_iff]
    exact ⟨commonNeighborCandidate_nodup solve x seed,
      fun v hv => mem_commonNeighborCandidate_lt solve x seed hv,
      hsuccess.symm ▸ hclique, hsuccess.symm ▸ hcard⟩
  have hsome : (((seedLists x.vertexCount s).map (commonNeighborCandidate solve x)).find?
      x.validatesClique).isSome := by
    rw [List.find?_isSome]
    exact ⟨_, List.mem_map.mpr ⟨seed, mem_seedLists.mpr ⟨hlen, hnodup, hbound⟩, rfl⟩,
      hvalid⟩
  unfold commonNeighborRecover
  cases hfind : ((seedLists x.vertexCount s).map (commonNeighborCandidate solve x)).find?
      x.validatesClique with
  | none => simp [hfind] at hsome
  | some candidate =>
    simp only [Option.getD_some]
    have hspec := (x.validatesClique_eq_true_iff candidate).mp (List.find?_some hfind)
    exact hunique _ hspec.2.2.1 (hspec.2.2.2.trans hcard.symm)

private def canonicalReducedSuccess {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S T : Finset (Fin n)) : Prop :=
  let U := G.commonNeighborhood T
  let e := U.orderEmbOfFin rfl
  @recover U.card (G.comap e) (fun _ _ => Classical.propDecidable _) (S.card - T.card) =
    Finset.univ.filter fun i => e i ∈ S

private theorem canonicalReducedSuccess_congr {n : ℕ} (G H : SimpleGraph (Fin n))
    [dG : DecidableRel G.Adj] [dH : DecidableRel H.Adj] (S T : Finset (Fin n)) (h : G = H) :
    canonicalReducedSuccess G S T ↔ canonicalReducedSuccess H S T := by
  subst H
  cases Subsingleton.elim dG dH
  rfl

/-- The represented wrapper recovers a unique planted clique when the canonical reduced
algorithm succeeds for one planted seed. This is the deterministic implication used by the
common-neighbor probability bound; all seed enumeration and representation obligations are
discharged here. -/
theorem commonNeighborRecover_ofGraph_eq_of_recover {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (S T : Finset (Fin n)) (hT : T ⊆ S) (hclique : G.IsClique (S : Set (Fin n)))
    (hunique : ∀ Q : Finset (Fin n), G.IsClique (Q : Set (Fin n)) → Q.card = S.card → Q = S)
    (hrec : let U := G.commonNeighborhood T
      let e := U.orderEmbOfFin rfl
      recover (G.comap e) (S.card - T.card) = Finset.univ.filter fun i => e i ∈ S) :
    vertexSet n
      (commonNeighborRecover recoverInput T.card (RecoveryInput.ofGraph G S.card)) = S := by
  classical
  let x : RecoveryInput := ⟨n, S.card, (RecoveryInput.ofGraph G S.card).adjacencyBits⟩
  have hgraph : x.graph = G := RecoveryInput.graph_ofGraph G S.card
  let seed := (T.sort (· ≤ ·)).map Fin.val
  have hset : vertexSet n seed = T := by
    apply vertexSet_eq_of_toFinset_eq_image
    ext i
    simp [seed]
  have hlen : seed.length = T.card := by simp [seed]
  have hnodup : seed.Nodup := (T.sort_nodup _).map Fin.val_injective
  have hbound : ∀ v ∈ seed, v < n := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    exact i.isLt
  have hclique' : x.graph.IsClique (S : Set (Fin n)) := by
    simpa only [hgraph] using hclique
  change vertexSet n (commonNeighborRecover recoverInput T.card x) = S
  apply commonNeighborRecover_eq_of_successful_seed recoverInput T.card x S rfl hclique'
    (by simpa only [hgraph] using hunique) seed hlen hnodup hbound
  apply commonNeighborCandidate_recoverInput_eq_of_recover x seed S rfl hnodup hbound
    (by change vertexSet n seed ⊆ S; exact hset.symm ▸ hT) hclique'
  simp only [recover_eq_classical] at hrec ⊢
  change canonicalReducedSuccess x.graph S (vertexSet n seed)
  change canonicalReducedSuccess G S T at hrec
  rw [hset]
  exact (canonicalReducedSuccess_congr x.graph G S T hgraph).mpr hrec

private theorem computableInPolyTime_seedLists (s : ℕ) :
    ComputableInPolyTime (fun n => seedLists n s) encUnary (encList (encList encUnary)) := by
  unfold seedLists
  apply ComputableInPolyTime.filterWithInput (ComputableInPolyTime.listsUpTo (by fun_prop) s)
  have hn := ComputableInPolyTime.decide_nodup
    (ComputableInPolyTime.snd encUnary (encList encUnary))
  fun_prop

/-- A uniformly certified base solver gives a uniformly certified single-seed attempt. -/
@[fun_prop] theorem computableInPolyTime_commonNeighborCandidate
    {solve : RecoveryInput → List ℕ}
    (hsolve : ComputableInPolyTime solve encRecoveryInput (encList encUnary))
    {α : Type} {encIn : α ↪ List Bool} {input : α → RecoveryInput} {seed : α → List ℕ}
    (hx : ComputableInPolyTime input encIn encRecoveryInput)
    (hseed : ComputableInPolyTime seed encIn (encList encUnary)) :
    ComputableInPolyTime (fun a => commonNeighborCandidate solve (input a) (seed a))
      encIn (encList encUnary) := by
  dsimp only [commonNeighborCandidate]
  have hv := RecoveryInput.computableInPolyTime_commonVertices hx hseed
  have hsub := RecoveryInput.computableInPolyTime_inducedInput hx hv
    (show ComputableInPolyTime (fun a => (input a).cliqueSize - (seed a).length)
      encIn encUnary by fun_prop)
  have hselected := hsolve.comp hsub
  fun_prop

/-- For each fixed seed size, one native polynomial-time machine performs the entire common-
neighbor search whenever the supplied base function has a uniform native certificate. -/
theorem computableInPolyTime_commonNeighborRecover (s : ℕ)
    {solve : RecoveryInput → List ℕ}
    (hsolve : ComputableInPolyTime solve encRecoveryInput (encList encUnary)) :
    ComputableInPolyTime (commonNeighborRecover solve s)
      encRecoveryInput (encList encUnary) := by
  unfold commonNeighborRecover
  apply ComputableInPolyTime.optionGetDWithInput
  · apply ComputableInPolyTime.findWithInput
    · apply ComputableInPolyTime.mapWithInput
        (computableInPolyTime_seedLists s |>.comp (by fun_prop))
      exact computableInPolyTime_commonNeighborCandidate hsolve (by fun_prop) (by fun_prop)
    · fun_prop
  · fun_prop

end Cslib.Algorithms.PlantedClique
