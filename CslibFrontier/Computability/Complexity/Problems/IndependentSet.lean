/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph
public import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
public import CslibFrontier.Computability.Complexity.Reduction
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Logics.Propositional.CNF.ModelCount
public import Mathlib.Combinatorics.SimpleGraph.Clique
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Foundations.Data.List.OfFn

/-!
# Independent sets

`IndependentSet` is the set of graphs, given by a list of vertices and a list of edges, together
with a number `m`, such that the graph has an independent set of `m` declared vertices [Arora and
Barak, Section 2.4][AroraBarak09]. Graphs are read on their declared vertices through
`Cslib.Complexity.Graph.induced`, and independent sets through `SimpleGraph.IsNIndepSet`.

The reduction `SAT.toIndependentSet` from `SAT` is Karp's: one vertex for each occurrence of a
literal, edges between occurrences in the same clause and between complementary occurrences, and
`m` the number of clauses [Karp1972]. An independent set with one vertex in each clause picks a
literal in each clause without contradictions, which is exactly a satisfying assignment.

Vertices and target sizes use binary encoding (`encNat`). A certificate masks the declared vertex
list at first occurrences so duplicate vertex entries cannot inflate the selected set, and checks
the selected count in binary without unary expansion of `m`. The verifier is an instance of the
subset-witness verifier `Cslib.Complexity.subsetVerifier`, which handles the certificate length.

The same problem as a class of finite structures, closed under isomorphism and without an
encoding, with the target size given by a unary relation, is
`Cslib.Logic.FO.sizedGraph.IndependentSet`. There loops are ignored, edges need not be symmetric,
and the reductions between independent set, clique and vertex cover are quantifier-free
first-order interpretations.

## Main definitions

* `Cslib.Complexity.IndependentSetInstance`, `Cslib.Complexity.IndependentSet`.
* `Cslib.Complexity.IndependentSet.verifier`.
* `Cslib.Complexity.SAT.toIndependentSet`.
* `Cslib.Complexity.Graph.indepNum`: the independence number (`G.induced.indepNum`).

## Main results

* `Cslib.Complexity.mem_IndependentSet_iff`: independent sets as subsets of `ℕ` contained in the
  declared vertices.
* `Cslib.Complexity.SAT.toIndependentSet_mem_iff`: `toIndependentSet φ ∈ IndependentSet ↔ φ ∈ SAT`.
* `Cslib.Complexity.SAT.le_indepNum_toIndependentSet_iff`: the independence number of Karp's
  graph is the maximum number of clauses satisfied by one assignment.
* `Cslib.Complexity.SAT.exists_card_add_countUnsat_le`: an independent set of Karp's graph gives an
  assignment satisfying as many clauses.
* `Cslib.Complexity.Graph.le_indepNum_iff`: the independence number is the largest target of
  `IndependentSet`.
* `Cslib.Complexity.SAT.computableInPolyTime_toIndependentSet`: Karp's reduction is
  polynomial-time.
* `Cslib.Complexity.IndependentSet.isVerifier`, `Cslib.Complexity.IndependentSet.mem_NP`:
  `IndependentSet ∈ NP encIndependentSetInstance`.
* `Cslib.Complexity.polyTimeReducible_SAT_IndependentSet`,
  `Cslib.Complexity.IndependentSet_npHard`, `Cslib.Complexity.IndependentSet_npComplete`:
  `IndependentSet` is `NP`-complete.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-- An instance `(graph, m)` of **Independent Set**. -/
@[ext]
structure IndependentSetInstance where
  /-- The graph in which to find an independent set. -/
  graph : Graph
  /-- The target number of declared vertices. -/
  m : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Framed `encGraph` followed by binary target `encNat`, encoding `IndependentSetInstance`. -/
enc_structure encIndependentSetInstance : IndependentSetInstance where
  graph : encGraph,
  m : encNat

attribute [fun_prop] encIndependentSetInstance_graph_polyTime
  encIndependentSetInstance_m_polyTime encIndependentSetInstance_mk_polyTime

/-- The graphs with an independent set of `m` of their vertices
[Arora and Barak, Section 2.4][AroraBarak09]. -/
def IndependentSet : Set IndependentSetInstance :=
  {x | ∃ S : Finset {v // v ∈ x.graph.vertices}, x.graph.induced.IsNIndepSet x.m S}

/-- Membership in `IndependentSet` as a finite set of `m` declared vertices that is independent in
`x.graph.toSimpleGraph`. -/
theorem mem_IndependentSet_iff {x : IndependentSetInstance} :
    x ∈ IndependentSet ↔
      ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.graph.vertices) ∧
        x.graph.toSimpleGraph.IsNIndepSet x.m S := by
  simpa only [IndependentSet, Set.mem_ofPred_eq, SimpleGraph.isNIndepSet_iff,
    SimpleGraph.IsIndepSet, Graph.induced_adj] using
    Graph.exists_subtype_pairwise_iff (P := fun u v => ¬x.graph.toSimpleGraph.Adj u v)

@[simp]
theorem mem_IndependentSet_iff_mk {G : Graph} {m : ℕ} :
    (⟨G, m⟩ : IndependentSetInstance) ∈ IndependentSet ↔
      ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ G.vertices) ∧ G.toSimpleGraph.IsNIndepSet m S :=
  mem_IndependentSet_iff

namespace SAT

/-! ### Karp's reduction -/

/-- The vertex of an occurrence. -/
def _root_.Cslib.Logic.PL.Occurrence.vertex (o : Occurrence ℕ) : ℕ := Nat.pair o.clause o.pos

/-- Two occurrences conflict when they are in the same clause or are complementary. -/
def _root_.Cslib.Logic.PL.Occurrence.Conflict (o o' : Occurrence ℕ) : Prop :=
  (o.clause = o'.clause ∧ o.pos ≠ o'.pos) ∨ (o.lit.1 = o'.lit.1 ∧ o.lit.2 ≠ o'.lit.2)

instance : DecidableRel Occurrence.Conflict := fun _ _ => by
  unfold Occurrence.Conflict; infer_instance

/-- Karp's reduction from `SAT` to `IndependentSet`. -/
def toIndependentSet (φ : CNF ℕ) : IndependentSetInstance :=
  ⟨⟨(occurrences φ).map Occurrence.vertex,
    (occurrences φ).flatMap fun o =>
      ((occurrences φ).filter fun o' => decide (o.Conflict o')).map
        fun o' => (o.vertex, o'.vertex)⟩,
    φ.length⟩

theorem _root_.Cslib.Logic.PL.Occurrence.Conflict.symm {o o' : Occurrence ℕ}
    (h : o.Conflict o') : o'.Conflict o :=
  h.imp (fun ⟨h₁, h₂⟩ => ⟨h₁.symm, h₂.symm⟩) fun ⟨h₁, h₂⟩ => ⟨h₁.symm, h₂.symm⟩

private theorem _root_.Cslib.Logic.PL.Occurrence.Conflict.ne {o o' : Occurrence ℕ}
    (h : o.Conflict o') : o ≠ o' := by
  rintro rfl
  exact h.elim (fun h => h.2 rfl) fun h => h.2 rfl

/-- An occurrence is determined by its vertex. -/
private theorem vertex_injOn {φ : CNF ℕ} {o o' : Occurrence ℕ} (ho : o ∈ occurrences φ)
    (ho' : o' ∈ occurrences φ) (h : o.vertex = o'.vertex) : o = o' := by
  obtain ⟨i, j, l⟩ := o
  obtain ⟨i', j', l'⟩ := o'
  obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 h
  obtain ⟨_, _, hl⟩ := mem_occurrences.1 ho
  obtain ⟨_, _, hl'⟩ := mem_occurrences.1 ho'
  simp only at hl hl'
  rw [hl, hl']

/-- In the graph of Karp's reduction, two occurrences are adjacent exactly when they conflict. -/
theorem adj_toIndependentSet_iff {φ : CNF ℕ} {o o' : Occurrence ℕ} (ho : o ∈ occurrences φ)
    (ho' : o' ∈ occurrences φ) :
    (toIndependentSet φ).graph.toSimpleGraph.Adj o.vertex o'.vertex ↔ o.Conflict o' := by
  have hedge {p p'} (hp : p ∈ occurrences φ) (hp' : p' ∈ occurrences φ) :
      (p.vertex, p'.vertex) ∈ (toIndependentSet φ).graph.edges ↔ p.Conflict p' := by
    simp only [toIndependentSet, List.mem_flatMap, List.mem_map, List.mem_filter,
      decide_eq_true_eq, Prod.mk.injEq]
    exact ⟨fun ⟨q, hq, q', ⟨hq', hc⟩, h₁, h₂⟩ =>
      vertex_injOn hq hp h₁ ▸ vertex_injOn hq' hp' h₂ ▸ hc,
      fun hc => ⟨p, hp, p', ⟨hp', hc⟩, rfl, rfl⟩⟩
  simp only [Graph.toSimpleGraph_adj, ne_eq, hedge ho ho', hedge ho' ho]
  exact ⟨fun ⟨_, h⟩ => h.elim id Occurrence.Conflict.symm,
    fun h => ⟨fun hv => h.ne (vertex_injOn ho ho' hv), Or.inl h⟩⟩

/-- **An independent set of Karp's graph gives an assignment satisfying as many clauses**: the
assignment making the chosen positive literals true satisfies the clause of every chosen
occurrence, and distinct chosen occurrences lie in distinct clauses. -/
theorem exists_card_add_countUnsat_le {φ : CNF ℕ} {S : Finset ℕ}
    (hSV : ∀ v ∈ S, v ∈ (toIndependentSet φ).graph.vertices)
    (hS : (toIndependentSet φ).graph.toSimpleGraph.IsIndepSet (S : Set ℕ)) :
    ∃ σ : ℕ → Bool, S.card + φ.countUnsat σ ≤ φ.length := by
  classical
  have hocc : ∀ v ∈ S, ∃ o ∈ occurrences φ, o.vertex = v := fun v hv => by
    simpa [toIndependentSet] using hSV v hv
  choose! occ hocc_mem hocc_vertex using hocc
  have hadj : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬(occ u).Conflict (occ v) := fun u hu v hv huv hc =>
    hS hu hv huv (by
      simpa only [hocc_vertex u hu, hocc_vertex v hv] using
        (adj_toIndependentSet_iff (hocc_mem u hu) (hocc_mem v hv)).2 hc)
  -- Distinct chosen occurrences lie in distinct clauses.
  have hinj : Set.InjOn (fun v => (occ v).clause) S := fun u hu v hv h => by
    by_contra huv
    refine hadj u hu v hv huv (Or.inl ⟨h, fun hj => huv ?_⟩)
    rw [← hocc_vertex u hu, ← hocc_vertex v hv]
    simp [Occurrence.vertex, h, hj]
  -- The assignment making the chosen positive literals true.
  let σ : ℕ → Bool := fun x => decide (∃ v ∈ S, (occ v).lit = (x, true))
  -- It satisfies the clause of every chosen occurrence.
  have hsat : ∀ v ∈ S, ((φ.zipIdx.filter fun c => c.1.eval σ).map Prod.snd).contains
      (occ v).clause = true := by
    intro v hv
    have hov := hocc_mem v hv
    rcases hocc : occ v with ⟨i, j, x, b⟩
    obtain ⟨hi, hj, hl : (x, b) = φ[i][j]⟩ := mem_occurrences.1 (hocc ▸ hov)
    have heval : φ[i].eval σ = true := by
      rw [Clause.eval_eq_true_iff]
      refine ⟨(x, b), hl ▸ List.getElem_mem hj, ?_⟩
      cases b
      · simp only [σ, decide_eq_false_iff_not, not_exists, not_and]
        intro v' hv' hv'x
        have hne : v ≠ v' := by
          rintro rfl
          simp [hocc] at hv'x
        exact hadj v hv v' hv' hne (hocc ▸ Or.inr ⟨by simp [hv'x], by simp [hv'x]⟩)
      · simp only [σ, decide_eq_true_eq]
        exact ⟨v, hv, by rw [hocc]⟩
    simp only [List.contains_iff_mem, List.mem_map, List.mem_filter]
    exact ⟨(φ[i], i), ⟨List.mem_zipIdx_iff_getElem?.2 (by simp [hi]), heval⟩, rfl⟩
  refine ⟨σ, ?_⟩
  have hcard : S.card ≤ φ.countP fun c => c.eval σ :=
    calc S.card = (S.image fun v => (occ v).clause).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ ((φ.zipIdx.filter fun c => c.1.eval σ).map Prod.snd).toFinset.card :=
          Finset.card_le_card fun i hi => by
            obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hi
            exact List.mem_toFinset.2 (List.contains_iff_mem.1 (hsat v hv))
      _ ≤ ((φ.zipIdx.filter fun c => c.1.eval σ).map Prod.snd).length := List.toFinset_card_le _
      _ = φ.countP fun c => c.eval σ := by
          rw [List.length_map, ← List.countP_eq_length_filter]
          conv_rhs => rw [← List.zipIdx_map_fst 0 φ, List.countP_map]
          rfl
  have hsplit := List.length_eq_countP_add_countP (fun c : Clause ℕ => c.eval σ) (l := φ)
  have hunsat : φ.countUnsat σ = φ.countP fun c => ¬(c.eval σ = true) :=
    List.countP_congr fun c _ => by simp
  omega

private theorem countSat_mem_IndependentSet (φ : CNF ℕ) (σ : ℕ → Bool) :
    (⟨(toIndependentSet φ).graph, φ.countP (Clause.eval σ)⟩ : IndependentSetInstance) ∈
      IndependentSet := by
  classical
  let I := Finset.univ.filter fun i : Fin φ.length => φ[i].eval σ = true
  have hcl (i : I) : ∃ j : Fin φ[i.val].length, σ φ[i.val][j].1 = φ[i.val][j].2 := by
    obtain ⟨l, hl, hσl⟩ := (Clause.eval_eq_true_iff _ _).1 (Finset.mem_filter.1 i.property).2
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
    exact ⟨⟨j, hj⟩, hσl⟩
  choose J hJ using hcl
  let o : I → Occurrence ℕ := fun i => ⟨i.val, J i, φ[i.val][J i]⟩
  have ho (i : I) : o i ∈ occurrences φ := mem_occurrences.2 ⟨i.val.isLt, (J i).isLt, rfl⟩
  have hoinj : Function.Injective fun i => (o i).vertex :=
    fun _ _ h => Subtype.ext (Fin.ext (Nat.pair_eq_pair.1 h).1)
  rw [mem_IndependentSet_iff]
  refine ⟨Finset.univ.image fun i => (o i).vertex,
    Finset.forall_mem_image.2 fun i _ => List.mem_map.2 ⟨o i, ho i, rfl⟩, ⟨?_, ?_⟩⟩
  · intro u hu w hw huw hadj
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨i', -, rfl⟩ := Finset.mem_image.1 hw
    rcases (adj_toIndependentSet_iff (ho i) (ho i')).1 hadj with ⟨h, -⟩ | ⟨hx, hb⟩
    · exact huw (congrArg (fun k => (o k).vertex) (Subtype.ext (Fin.ext h)))
    · have h₁ := hJ i
      have h₂ := hJ i'
      simp only [o] at hx hb
      exact hb ((hx ▸ h₁).symm.trans h₂)
  · rw [Finset.card_image_of_injective _ hoinj, Finset.card_univ, Fintype.card_coe,
      List.countP_eq_card_filter_getElem]

/-- **Correctness of Karp's reduction.** A formula is satisfiable exactly when its graph has an
independent set as large as the number of clauses. -/
theorem toIndependentSet_mem_iff (φ : CNF ℕ) : toIndependentSet φ ∈ IndependentSet ↔ φ ∈ SAT := by
  refine ⟨fun h => ?_, fun ⟨σ, hσ⟩ => by
    have hs := countSat_mem_IndependentSet φ σ
    rwa [List.countP_eq_length.2 ((CNF.eval_eq_true_iff _ _).1 hσ)] at hs⟩
  obtain ⟨S, hSV, hS⟩ := mem_IndependentSet_iff.1 h
  obtain ⟨σ, hσ⟩ := exists_card_add_countUnsat_le hSV hS.isIndepSet
  have : S.card = φ.length := hS.card_eq
  exact ⟨σ, CNF.countUnsat_eq_zero_iff.1 (by omega)⟩

/-! ### Polynomial-time reduction -/

/-- Computing the binary vertex label of an occurrence from its unary indices is polynomial-time. -/
@[fun_prop]
theorem _root_.Cslib.Logic.PL.Occurrence.computableInPolyTime_vertex :
    ComputableInPolyTime Occurrence.vertex encOccurrence encNat := by
  unfold Occurrence.vertex
  exact unary_to_binary.comp (by fun_prop)

/-- Testing whether two occurrences conflict is polynomial-time. -/
@[fun_prop]
theorem _root_.Cslib.Logic.PL.Occurrence.computableInPolyTime_conflict :
    ComputableInPolyTime (fun p : Occurrence ℕ × Occurrence ℕ => decide (p.1.Conflict p.2))
      (encPair encOccurrence encOccurrence) encBool := by
  unfold Occurrence.Conflict
  fun_prop

/-- Karp's reduction `toIndependentSet` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_toIndependentSet :
    ComputableInPolyTime toIndependentSet encCNF encIndependentSetInstance := by
  fun_prop [toIndependentSet]

end SAT

namespace IndependentSet

/-- The verifier for `IndependentSet`: select distinct declared vertices from the certificate mask,
check that their count equals `m`, and check that no two distinct selected vertices are adjacent. -/
def verifier : IndependentSetInstance × List Bool → Bool :=
  fun (x, w) => Graph.verifySubset (fun G u v => !G.adjBool u v) ((x.graph, x.m), w)

/-- `IndependentSet.verifier` verifies `IndependentSet` with certificates as long as the encoded
instance. -/
theorem isVerifier :
    IsVerifier encIndependentSetInstance Polynomial.X verifier IndependentSet := fun x => by
  simpa only [IndependentSet, Set.mem_ofPred_eq, SimpleGraph.isNIndepSet_iff,
    SimpleGraph.IsIndepSet, Graph.induced_adj, verifier, encIndependentSetInstance_apply] using
    Graph.isVerifier_verifySubset (P := fun G u v => ¬G.toSimpleGraph.Adj u v)
      (fun G u v _ => by rw [Bool.not_eq_true', Graph.adjBool_eq_false_iff]) (x.graph, x.m)

/-- The `IndependentSet` verifier is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier
      (encPair encIndependentSetInstance encBits) encBool := by
  fun_prop [verifier]

/-- `IndependentSet` belongs to `NP`. -/
theorem mem_NP : IndependentSet ∈ NP encIndependentSetInstance :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

end IndependentSet

/-- `SAT` reduces to `IndependentSet` in polynomial time via `SAT.toIndependentSet`. -/
theorem polyTimeReducible_SAT_IndependentSet :
    PolyTimeReducible encCNF encIndependentSetInstance SAT IndependentSet :=
  ⟨SAT.toIndependentSet, SAT.computableInPolyTime_toIndependentSet,
    fun φ => (SAT.toIndependentSet_mem_iff φ).symm⟩

/-- `IndependentSet` is `NP`-hard. -/
theorem IndependentSet_npHard : NPHard encIndependentSetInstance IndependentSet :=
  CookLevin.SAT_npHard.trans polyTimeReducible_SAT_IndependentSet

/-- **`IndependentSet` is NP-complete** [Arora and Barak, Section 2.4][AroraBarak09]. -/
theorem IndependentSet_npComplete : NPComplete encIndependentSetInstance IndependentSet :=
  ⟨IndependentSet.mem_NP, IndependentSet_npHard⟩

/-! ### The independence number -/

namespace Graph

/-- The **independence number** of a graph: the largest number of declared vertices that are
pairwise non-adjacent. -/
noncomputable def indepNum (G : Graph) : ℕ := G.induced.indepNum

variable {G : Graph} {k k' : ℕ}

/-- Fewer vertices of an independent set are independent. -/
theorem mem_IndependentSet_of_le (h : (⟨G, k⟩ : IndependentSetInstance) ∈ IndependentSet)
    (hk : k' ≤ k) : (⟨G, k'⟩ : IndependentSetInstance) ∈ IndependentSet := by
  obtain ⟨S, hS, hcard : S.card = k⟩ := h
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (hcard ▸ hk)
  exact ⟨T, hS.mono (Finset.coe_subset.2 hTS), hT⟩

/-- The independence number is the size of an independent set. -/
theorem indepNum_mem_IndependentSet (G : Graph) :
    (⟨G, G.indepNum⟩ : IndependentSetInstance) ∈ IndependentSet :=
  G.induced.exists_isNIndepSet_indepNum

/-- **The independence number is the largest target of `IndependentSet`.** -/
theorem le_indepNum_iff : k ≤ G.indepNum ↔ (⟨G, k⟩ : IndependentSetInstance) ∈ IndependentSet :=
  ⟨mem_IndependentSet_of_le G.indepNum_mem_IndependentSet,
    fun ⟨_, hS, (hcard : _ = k)⟩ => hcard ▸ hS.card_le_indepNum⟩

/-- The independence number is at most the number of distinct declared vertices. -/
theorem indepNum_le_card (G : Graph) : G.indepNum ≤ G.vertices.toFinset.card := by
  rw [indepNum, ← G.induced.cliqueNum_compl, ← G.natCard_vertexSubtype]
  exact G.inducedᶜ.cliqueNum_le_natCard

/-- An independent set has at most as many vertices as the distinct declared vertices. -/
theorem le_card_of_mem_IndependentSet (h : (⟨G, k⟩ : IndependentSetInstance) ∈ IndependentSet) :
    k ≤ G.vertices.toFinset.card :=
  (le_indepNum_iff.2 h).trans G.indepNum_le_card

end Graph

/-- The graph in Karp's reduction has an independent set of size at least `k` exactly when one
assignment leaves at most `φ.length - k` clauses unsatisfied and `k ≤ φ.length`. -/
theorem SAT.le_indepNum_toIndependentSet_iff (φ : CNF ℕ) (k : ℕ) :
    k ≤ (toIndependentSet φ).graph.indepNum ↔
      ∃ σ : ℕ → Bool, k + φ.countUnsat σ ≤ φ.length := by
  rw [Graph.le_indepNum_iff, mem_IndependentSet_iff]
  refine ⟨fun ⟨S, hSV, hS⟩ => ?_, fun ⟨σ, hσ⟩ => ?_⟩
  · obtain ⟨σ, h⟩ := exists_card_add_countUnsat_le hSV hS.isIndepSet
    have hs : S.card = k := hS.card_eq
    exact ⟨σ, hs ▸ h⟩
  · have : φ.length = φ.countP (Clause.eval σ) + φ.countUnsat σ :=
      List.length_eq_countP_add_countP (Clause.eval σ) (l := φ)
    exact mem_IndependentSet_iff.1
      (Graph.mem_IndependentSet_of_le (countSat_mem_IndependentSet φ σ) (by omega))

end Cslib.Complexity
