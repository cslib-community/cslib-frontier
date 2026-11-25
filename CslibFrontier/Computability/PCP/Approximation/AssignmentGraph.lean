/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Approximation.AssignmentConsistency
public import CslibFrontier.Computability.PCP.Approximation.IndependentSet
public import CslibFrontier.Foundations.Data.BitString.Enumeration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# The assignment graph of a 3CNF formula

Arora and Barak [Lemma 18.16][AroraBarak07] turn a 3CNF formula `φ` with `m` clauses into a
graph on `n = 7 m` vertices whose largest independent set has `val(φ) m = val(φ) n / 7` vertices,
where `val(φ)` is the largest proportion of the clauses an assignment satisfies. Each clause gets a
cluster of seven vertices, one for each assignment to its three variables that satisfies it; two
vertices are adjacent when they lie in the same cluster or their partial assignments disagree on a
shared variable. An assignment gives an independent set with one vertex in each satisfied cluster,
and an independent set gives consistent partial assignments, in distinct clusters, that extend to
one assignment satisfying all their clauses.

Here a partial assignment is a list of literals `(x, b)`, read as `x := b`
(`Cslib.Complexity.SAT.consistentLits`). The local satisfying assignments of a clause
(`Cslib.Complexity.SAT.clauseAssignments`) give values to the variables of its literals position by
position and keep those that are consistent and satisfy the clause. There are at most seven
(`Cslib.Complexity.SAT.length_clauseAssignments_le`), exactly seven when the three variables are
distinct; with fewer, the first one is repeated, as the draft does when it "treats one of them as
repeated". The draft does not treat clauses without literals: their seven vertices are adjacent to
every other vertex, and a formula all of whose clauses are empty (including the formula without
clauses) maps to the empty graph, as the lemma requires.

## Main definitions

* `Cslib.Complexity.SAT.assignmentGraph`: the assignment graph of a formula.

## Main results

* `Cslib.Complexity.SAT.card_toFinset_vertices_assignmentGraph`: seven vertices per clause.
* `Cslib.Complexity.SAT.length_sub_countUnsat_le_indepNum_assignmentGraph`,
  `Cslib.Complexity.SAT.exists_card_add_countUnsat_le_of_assignmentGraph`: assignments and
  independent sets of the assignment graph give each other.
* `Cslib.Complexity.SAT.indepNum_assignmentGraph`: the independence number is `val(φ) n / 7`.
* `Cslib.Complexity.SAT.computableInPolyTime_assignmentGraph`: the graph is polynomial-time.
* `Cslib.Complexity.SAT.exists_computableInPolyTime_indepNum_eq`: Arora–Barak Lemma 18.16.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak07]
-/

@[expose] public section

namespace Cslib.Complexity.SAT

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-- The partial assignment that gives the variables of the literals of `c` the values `bs`,
position by position. -/
def assignLits (c : Clause ℕ) (bs : List Bool) : List (Literal ℕ) :=
  (c.map Prod.fst).zip bs

/-- The **local satisfying assignments** of a clause: the values of the variables of its (at most
three) literals, as consistent partial assignments that satisfy the clause. The values are drawn
for three positions, so a clause with fewer literals lists each of them several times. -/
def clauseAssignments (c : Clause ℕ) : List (List (Literal ℕ)) :=
  ((BitString.enumList 3).filter fun bs =>
      consistentLits (assignLits c bs) (assignLits c bs) && c.any (assignLits c bs).contains).map
    (assignLits c)

/-- The partial assignment of the `k`-th vertex of the cluster of a clause: the `k`-th local
satisfying assignment, repeating the first one when there are fewer. -/
def clusterLabel (c : Clause ℕ) (k : ℕ) : List (Literal ℕ) :=
  ((clauseAssignments c).drop k ++ clauseAssignments c).headD []

/-- A vertex record of the assignment graph: the vertex at position `pos` of the cluster of the
clause `lits` with index `clause`, labelled by the partial assignment `label`. -/
@[ext]
structure AssignmentRecord where
  /-- The index of the clause. -/
  clause : ℕ
  /-- The position of the vertex in the cluster of the clause. -/
  pos : ℕ
  /-- The clause. -/
  lits : Clause ℕ
  /-- The partial assignment of the vertex. -/
  label : List (Literal ℕ)
  deriving DecidableEq, Inhabited, Repr

/-- Unary indices, then the clause and the label as lists of binary literals. -/
enc_structure encAssignmentRecord : AssignmentRecord where
  clause : encUnary, pos : encUnary, lits : (encList (encPair encNat encBool)),
  label : (encList (encPair encNat encBool))

attribute [fun_prop] encAssignmentRecord_clause_polyTime encAssignmentRecord_pos_polyTime
  encAssignmentRecord_lits_polyTime encAssignmentRecord_label_polyTime
  encAssignmentRecord_mk_polyTime

/-- The vertex records of the assignment graph: seven per clause. -/
def assignmentRecords (φ : CNF ℕ) : List AssignmentRecord :=
  φ.zipIdx.flatMap fun p => (List.range 7).map fun k => ⟨p.2, k, p.1, clusterLabel p.1 k⟩

/-- The vertex of a record. -/
def recordVertex (r : AssignmentRecord) : ℕ := Nat.pair r.clause r.pos

/-- Two records are joined in the assignment graph when they lie in the same cluster, when one of
them belongs to an empty clause, or when their partial assignments are inconsistent. -/
def recordConflict (r r' : AssignmentRecord) : Bool :=
  (r.clause == r'.clause && !(r.pos == r'.pos)) || r.lits.isEmpty || r'.lits.isEmpty ||
    !consistentLits r.label r'.label

/-- The **assignment graph** of a formula [Arora and Barak, Lemma 18.16][AroraBarak07]: seven
vertices per clause, labelled by its local satisfying assignments, joined inside clusters and
across inconsistent labels. A formula all of whose clauses are empty gives the empty graph. -/
def assignmentGraph (φ : CNF ℕ) : Graph :=
  if φ.all List.isEmpty then ⟨[], []⟩ else
    ⟨(assignmentRecords φ).map recordVertex,
      (assignmentRecords φ).flatMap fun r =>
        ((assignmentRecords φ).filter (recordConflict r)).map fun r' =>
          (recordVertex r, recordVertex r')⟩

/-! ### Local satisfying assignments -/

private theorem consistentLits_comm (ρ ρ' : List (Literal ℕ)) :
    consistentLits ρ ρ' = consistentLits ρ' ρ := by
  rw [Bool.eq_iff_iff, consistentLits_eq_true_iff, consistentLits_eq_true_iff]
  exact ⟨fun h l hl l' hl' he => (h l' hl' l hl he.symm).symm,
    fun h l hl l' hl' he => (h l' hl' l hl he.symm).symm⟩

private theorem assignLits_map_append (c : Clause ℕ) (f : Literal ℕ → Bool) (t : List Bool) :
    assignLits c (c.map f ++ t) = c.map fun l => (l.1, f l) := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    simp only [assignLits, List.map_cons, List.cons_append, List.zip_cons_cons] at ih ⊢
    rw [ih]

private theorem mem_clauseAssignments {c : Clause ℕ} {ρ : List (Literal ℕ)} :
    ρ ∈ clauseAssignments c ↔ ∃ bs : List Bool, bs.length = 3 ∧
      consistentLits (assignLits c bs) (assignLits c bs) = true ∧
      (∃ l ∈ c, l ∈ assignLits c bs) ∧ assignLits c bs = ρ := by
  simp only [clauseAssignments, List.mem_map, List.mem_filter, BitString.mem_enumList,
    Bool.and_eq_true, List.any_eq_true, List.contains_iff_mem, and_assoc]

/-- A local satisfying assignment is consistent and makes a literal of the clause true. -/
private theorem consistentLits_and_exists_of_mem_clauseAssignments {c : Clause ℕ}
    {ρ : List (Literal ℕ)}
    (h : ρ ∈ clauseAssignments c) : consistentLits ρ ρ = true ∧ ∃ l ∈ c, l ∈ ρ := by
  obtain ⟨bs, -, hcons, hsat, rfl⟩ := mem_clauseAssignments.1 h
  exact ⟨hcons, hsat⟩

/-- Restrictions of one assignment are consistent. -/
private theorem consistentLits_map_map (σ : ℕ → Bool) (c c' : Clause ℕ) :
    consistentLits (c.map fun l => (l.1, σ l.1)) (c'.map fun l => (l.1, σ l.1)) = true := by
  rw [consistentLits_eq_true_iff]
  simp only [List.mem_map]
  rintro _ ⟨l, -, rfl⟩ _ ⟨l', -, rfl⟩ (he : l.1 = l'.1)
  simp [he]

/-- The restriction of an assignment satisfying a clause of at most three literals is a local
satisfying assignment. -/
theorem map_mem_clauseAssignments {c : Clause ℕ} (hc : c.length ≤ 3) {σ : ℕ → Bool}
    (hσ : c.eval σ = true) : (c.map fun l => (l.1, σ l.1)) ∈ clauseAssignments c := by
  refine mem_clauseAssignments.2 ⟨c.map (fun l => σ l.1) ++ List.replicate (3 - c.length) false,
    by simp; omega, ?_, ?_, assignLits_map_append ..⟩ <;> rw [assignLits_map_append]
  · exact consistentLits_map_map σ c c
  · obtain ⟨l, hl, hσl⟩ := (Clause.eval_eq_true_iff _ _).1 hσ
    refine ⟨l, hl, List.mem_map.2 ⟨l, hl, ?_⟩⟩
    simp [hσl]

/-- A clause of at most three literals has at most seven local satisfying assignments: the values
falsifying every literal are excluded. -/
theorem length_clauseAssignments_le {c : Clause ℕ} (hc : c.length ≤ 3) :
    (clauseAssignments c).length ≤ 7 := by
  rw [clauseAssignments, List.length_map]
  have hlt : (List.filter (fun bs => consistentLits (assignLits c bs) (assignLits c bs) &&
      c.any (assignLits c bs).contains) (BitString.enumList 3)).length <
      (BitString.enumList 3).length := by
    refine List.length_filter_lt_length_iff_exists.2 ⟨_, BitString.mem_enumList.2
      (?_ : (c.map (fun l => !l.2) ++ List.replicate (3 - c.length) false).length = 3), ?_⟩
    · simp only [List.length_append, List.length_map, List.length_replicate]
      omega
    · rw [assignLits_map_append]
      simp only [Bool.and_eq_true, List.any_eq_true, List.contains_iff_mem, not_and, not_exists]
      intro hcons l hl hmem
      have := (consistentLits_eq_true_iff.1 hcons) l hmem (l.1, !l.2) (List.mem_map.2 ⟨l, hl, rfl⟩)
        rfl
      cases l
      simp at this
  rw [BitString.length_enumList] at hlt
  omega

private theorem clauseAssignments_ne_nil {c : Clause ℕ} (hc : c.length ≤ 3) (hne : c ≠ []) :
    clauseAssignments c ≠ [] := by
  obtain ⟨l, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  refine List.ne_nil_of_mem (map_mem_clauseAssignments hc (σ := fun _ => l.2) ?_)
  exact (Clause.eval_eq_true_iff _ _).2 ⟨l, List.mem_cons_self .., by simp⟩

private theorem clusterLabel_mem {c : Clause ℕ} (h : clauseAssignments c ≠ []) (k : ℕ) :
    clusterLabel c k ∈ clauseAssignments c := by
  unfold clusterLabel
  rcases hd : (clauseAssignments c).drop k with _ | ⟨a, t⟩
  · obtain ⟨b, u, hb⟩ := List.exists_cons_of_ne_nil h
    rw [hb]
    simp
  · simp only [List.cons_append, List.headD_cons]
    exact List.mem_of_mem_drop (hd ▸ List.mem_cons_self ..)

private theorem clusterLabel_eq_getElem {c : Clause ℕ} {k : ℕ}
    (hk : k < (clauseAssignments c).length) :
    clusterLabel c k = (clauseAssignments c)[k] := by
  unfold clusterLabel
  rw [List.drop_eq_getElem_cons hk]
  rfl

/-! ### The graph -/

/-- The records of the assignment graph: a clause index, a position below seven, the clause and
the label. -/
theorem mem_assignmentRecords {φ : CNF ℕ} {r : AssignmentRecord} :
    r ∈ assignmentRecords φ ↔
      ∃ (i : ℕ) (hi : i < φ.length), ∃ k < 7, r = ⟨i, k, φ[i], clusterLabel φ[i] k⟩ := by
  simp only [assignmentRecords, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨⟨c, i⟩, hci, k, hk, rfl⟩
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff] at hci
    obtain ⟨hi, hc⟩ := hci
    refine ⟨i, hi, k, hk, ?_⟩
    simp only at hc ⊢
    rw [hc]
  · rintro ⟨i, hi, k, hk, rfl⟩
    exact ⟨(φ[i], i), List.mem_zipIdx_iff_getElem?.2 (by simp [hi]), k, hk, rfl⟩

private theorem eq_of_recordVertex_eq {φ : CNF ℕ} {r r' : AssignmentRecord}
    (hr : r ∈ assignmentRecords φ) (hr' : r' ∈ assignmentRecords φ)
    (h : recordVertex r = recordVertex r') : r = r' := by
  obtain ⟨i, hi, k, -, rfl⟩ := mem_assignmentRecords.1 hr
  obtain ⟨i', hi', k', -, rfl⟩ := mem_assignmentRecords.1 hr'
  obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 h
  rfl

private theorem recordConflict_comm (r r' : AssignmentRecord) :
    recordConflict r r' = recordConflict r' r := by
  unfold recordConflict
  rw [consistentLits_comm, Bool.beq_comm (a := r.clause), Bool.beq_comm (a := r.pos)]
  cases r.lits.isEmpty <;> cases r'.lits.isEmpty <;> simp

private theorem assignmentGraph_of_not_all {φ : CNF ℕ} (hφ : ¬φ.all List.isEmpty = true) :
    assignmentGraph φ = ⟨(assignmentRecords φ).map recordVertex,
      (assignmentRecords φ).flatMap fun r =>
        ((assignmentRecords φ).filter (recordConflict r)).map fun r' =>
          (recordVertex r, recordVertex r')⟩ :=
  ite_eq_right hφ

/-- Two vertices of the assignment graph are adjacent exactly when their records are distinct
and conflict. -/
theorem adj_assignmentGraph_iff {φ : CNF ℕ} (hφ : ¬φ.all List.isEmpty = true)
    {r r' : AssignmentRecord} (hr : r ∈ assignmentRecords φ)
    (hr' : r' ∈ assignmentRecords φ) :
    (assignmentGraph φ).toSimpleGraph.Adj (recordVertex r) (recordVertex r') ↔
      r ≠ r' ∧ recordConflict r r' = true := by
  have hedge : ∀ {q q'}, q ∈ assignmentRecords φ → q' ∈ assignmentRecords φ →
      ((recordVertex q, recordVertex q') ∈ (assignmentGraph φ).edges ↔
        recordConflict q q' = true) := by
    intro q q' hq hq'
    rw [assignmentGraph_of_not_all hφ]
    simp only [List.mem_flatMap, List.mem_map, List.mem_filter, Prod.mk.injEq]
    constructor
    · rintro ⟨p, hp, p', ⟨hp', hc⟩, h₁, h₂⟩
      rwa [← eq_of_recordVertex_eq hp hq h₁, ← eq_of_recordVertex_eq hp' hq' h₂]
    · intro hc
      exact ⟨q, hq, q', ⟨hq', hc⟩, rfl, rfl⟩
  rw [Graph.toSimpleGraph_adj, hedge hr hr', hedge hr' hr, recordConflict_comm r' r, or_self]
  exact and_congr_left fun _ => ⟨fun h he => h (he ▸ rfl),
    fun h he => h (eq_of_recordVertex_eq hr hr' he)⟩

/-- The assignment graph of a formula with a nonempty clause has seven vertices per clause. -/
theorem card_toFinset_vertices_assignmentGraph {φ : CNF ℕ} (hφ : ¬φ.all List.isEmpty = true) :
    (assignmentGraph φ).vertices.toFinset.card = 7 * φ.length := by
  have hset : (assignmentGraph φ).vertices.toFinset =
      (Finset.range φ.length ×ˢ Finset.range 7).image fun p => Nat.pair p.1 p.2 := by
    ext v
    rw [assignmentGraph_of_not_all hφ, List.mem_toFinset, Finset.mem_image]
    simp only [List.mem_map, mem_assignmentRecords, Finset.mem_product, Finset.mem_range,
      Prod.exists]
    constructor
    · rintro ⟨r, ⟨i, hi, k, hk, rfl⟩, rfl⟩
      exact ⟨i, k, ⟨hi, hk⟩, rfl⟩
    · rintro ⟨i, k, ⟨hi, hk⟩, rfl⟩
      exact ⟨_, ⟨i, hi, k, hk, rfl⟩, rfl⟩
  rw [hset, Finset.card_image_of_injective _ fun p q h => Prod.ext (Nat.pair_eq_pair.1 h).1
    (Nat.pair_eq_pair.1 h).2, Finset.card_product, Finset.card_range, Finset.card_range,
    Nat.mul_comm]

/-- The clauses an assignment satisfies, counted by index. -/
private theorem card_filter_eval_eq (φ : CNF ℕ) (σ : ℕ → Bool) :
    (Finset.univ.filter fun j : Fin φ.length => φ[j].eval σ = true).card =
      φ.length - φ.countUnsat σ := by
  rw [CNF.countUnsat_eq_card]
  have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun j : Fin φ.length => φ[j].eval σ = true)
  simp only [Finset.card_univ, Fintype.card_fin, Bool.not_eq_true] at this
  omega

/-- **An assignment gives an independent set with a vertex for each clause it satisfies**: the
vertex of the clause labelled by the restriction of the assignment. -/
theorem length_sub_countUnsat_le_indepNum_assignmentGraph {φ : CNF ℕ}
    (h3 : ∀ c ∈ φ, c.length ≤ 3) (hφ : ¬φ.all List.isEmpty = true) (σ : ℕ → Bool) :
    φ.length - φ.countUnsat σ ≤ (assignmentGraph φ).indepNum := by
  classical
  have hk : ∀ i : Fin φ.length, ∃ k < 7,
      φ[i].eval σ = true → clusterLabel φ[i] k = φ[i].map fun l => (l.1, σ l.1) := by
    intro i
    by_cases hs : φ[i].eval σ = true
    · have h3i := h3 _ (List.getElem_mem i.2)
      obtain ⟨k, hkl, hk⟩ := List.getElem_of_mem (map_mem_clauseAssignments h3i hs)
      exact ⟨k, hkl.trans_le (length_clauseAssignments_le h3i),
        fun _ => (clusterLabel_eq_getElem hkl).trans hk⟩
    · exact ⟨0, by norm_num, fun h => absurd h hs⟩
  choose K hK7 hK using hk
  let r : Fin φ.length → AssignmentRecord :=
    fun i => ⟨i, K i, φ[i], clusterLabel φ[i] (K i)⟩
  have hr : ∀ i, r i ∈ assignmentRecords φ :=
    fun i => mem_assignmentRecords.2 ⟨i, i.2, K i, hK7 i, rfl⟩
  have hinj : Function.Injective fun i => recordVertex (r i) :=
    fun i j h => Fin.ext (Nat.pair_eq_pair.1 h).1
  set T : Finset (Fin φ.length) := Finset.univ.filter fun j : Fin φ.length => φ[j].eval σ = true
  rw [← card_filter_eval_eq, ← Finset.card_image_of_injective T hinj, Graph.le_indepNum_iff,
    mem_IndependentSet_iff_mk]
  refine ⟨T.image fun i => recordVertex (r i), fun v hv => ?_, ⟨fun u hu w hw huw hadj => ?_, rfl⟩⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
    rw [assignmentGraph_of_not_all hφ]
    exact List.mem_map.2 ⟨_, hr i, rfl⟩
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hu)
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hw)
    have hij : (i : ℕ) ≠ j := fun h => huw (by rw [Fin.ext h])
    have hi' : φ[i].eval σ = true := (Finset.mem_filter.1 hi).2
    have hj' : φ[j].eval σ = true := (Finset.mem_filter.1 hj).2
    have hne : ∀ c : Clause ℕ, c.eval σ = true → c.isEmpty = false := by
      rintro (_ | ⟨l, c⟩) h
      · simp [Clause.eval] at h
      · rfl
    have hc := ((adj_assignmentGraph_iff hφ (hr i) (hr j)).1 hadj).2
    have hb : ((i : ℕ) == j) = false := beq_eq_false_iff_ne.2 hij
    simp only [recordConflict, r, hK i hi', hK j hj', consistentLits_map_map, hne _ hi', hne _ hj',
      hb, Bool.false_and, Bool.or_false, Bool.not_true] at hc
    exact Bool.false_ne_true hc

/-- **An independent set of the assignment graph gives an assignment satisfying as many clauses**:
the vertices lie in distinct clusters, and their consistent labels extend to one assignment. -/
theorem exists_card_add_countUnsat_le_of_assignmentGraph {φ : CNF ℕ}
    (h3 : ∀ c ∈ φ, c.length ≤ 3) (hφ : ¬φ.all List.isEmpty = true) {S : Finset ℕ}
    (hSV : ∀ v ∈ S, v ∈ (assignmentGraph φ).vertices)
    (hS : (assignmentGraph φ).toSimpleGraph.IsIndepSet (S : Set ℕ)) :
    ∃ σ : ℕ → Bool, S.card + φ.countUnsat σ ≤ φ.length := by
  classical
  have hrec : ∀ v ∈ S, ∃ r ∈ assignmentRecords φ, recordVertex r = v := fun v hv =>
    List.mem_map.1 (by simpa only [assignmentGraph_of_not_all hφ] using hSV v hv)
  choose! R hR hRv using hrec
  have hnc : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → recordConflict (R u) (R v) = false := by
    intro u hu v hv huv
    have hne : R u ≠ R v := fun h => huv (by rw [← hRv u hu, ← hRv v hv, h])
    have := hS (Finset.mem_coe.2 hu) (Finset.mem_coe.2 hv) huv
    rw [← hRv u hu, ← hRv v hv, adj_assignmentGraph_iff hφ (hR u hu) (hR v hv)] at this
    simpa [hne] using this
  by_cases hE : ∃ v ∈ S, (R v).lits = []
  · -- A vertex of an empty clause is adjacent to every other vertex.
    obtain ⟨v, hv, hvE⟩ := hE
    have hall : ∀ w ∈ S, w = v := fun w hw => by
      by_contra hwv
      simpa [recordConflict, hvE] using hnc v hv w hw (Ne.symm hwv)
    have hS1 : S.card ≤ 1 :=
      Finset.card_le_one.2 fun a ha b hb => (hall a ha).trans (hall b hb).symm
    obtain ⟨c, hc, hce⟩ : ∃ c ∈ φ, c ≠ [] := by
      simpa [List.all_eq_true, List.isEmpty_iff] using hφ
    obtain ⟨l, t, rfl⟩ := List.exists_cons_of_ne_nil hce
    refine ⟨fun _ => l.2, ?_⟩
    have hlt : φ.countUnsat (fun _ => l.2) < φ.length := by
      rw [CNF.countUnsat, List.countP_eq_length_filter]
      refine List.length_filter_lt_length_iff_exists.2 ⟨_, hc, ?_⟩
      simp [Clause.eval, Literal.eval]
    omega
  push Not at hE
  -- The records of the chosen vertices.
  have hRm : ∀ v ∈ S, ∃ (i : ℕ) (hi : i < φ.length), ∃ k < 7,
      R v = ⟨i, k, φ[i], clusterLabel φ[i] k⟩ := fun v hv => mem_assignmentRecords.1 (hR v hv)
  choose! I hI K hK hRe using hRm
  have hlab : ∀ v (hv : v ∈ S), (R v).label ∈ clauseAssignments (φ[I v]'(hI v hv)) := by
    intro v hv
    have hne := hE v hv
    rw [hRe v hv] at hne ⊢
    exact clusterLabel_mem (clauseAssignments_ne_nil (h3 _ (List.getElem_mem _)) hne) _
  let σ : ℕ → Bool := fun x => decide (∃ v ∈ S, (x, true) ∈ (R v).label)
  -- Every chosen label agrees with `σ`.
  have hagree : ∀ v ∈ S, ∀ l ∈ (R v).label, σ l.1 = l.2 := by
    intro v hv l hl
    obtain ⟨x, b⟩ := l
    cases b
    · simp only [σ, decide_eq_false_iff_not, not_exists, not_and]
      intro w hw hwx
      by_cases hvw : v = w
      · subst hvw
        have := (consistentLits_eq_true_iff.1
          (consistentLits_and_exists_of_mem_clauseAssignments (hlab v hv)).1) _ hl _ hwx rfl
        simp at this
      · have hcons := hnc v hv w hw hvw
        simp only [recordConflict, Bool.or_eq_false_iff, Bool.not_eq_false'] at hcons
        have := (consistentLits_eq_true_iff.1 hcons.2) _ hl _ hwx rfl
        simp at this
    · exact decide_eq_true ⟨v, hv, hl⟩
  -- Hence `σ` satisfies the clause of every chosen vertex.
  have hsat : ∀ v (hv : v ∈ S), (φ[I v]'(hI v hv)).eval σ = true := by
    intro v hv
    obtain ⟨l, hl, hlρ⟩ := (consistentLits_and_exists_of_mem_clauseAssignments (hlab v hv)).2
    exact (Clause.eval_eq_true_iff _ _).2 ⟨l, hl, hagree v hv l hlρ⟩
  -- Distinct chosen vertices lie in distinct clusters.
  have hinj : Set.InjOn I S := by
    intro u hu v hv h
    by_contra huv
    have hc := hnc u hu v hv huv
    have hk : K u ≠ K v := fun hk => huv (by
      rw [← hRv u hu, ← hRv v hv, hRe u hu, hRe v hv]
      simp [h, hk])
    rw [hRe u hu, hRe v hv] at hc
    simp [recordConflict, h, hk] at hc
  refine ⟨σ, ?_⟩
  have hle : S.card ≤ ((Finset.univ.filter fun j : Fin φ.length => φ[j].eval σ = true).map
      Fin.valEmbedding).card := by
    refine Finset.card_le_card_of_injOn I (fun v hv => ?_) hinj
    exact Finset.mem_map.2 ⟨⟨I v, hI v hv⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hsat v hv⟩, rfl⟩
  have := CNF.countUnsat_le_length σ φ
  rw [Finset.card_map] at hle
  have h2 := card_filter_eval_eq φ σ
  omega

/-- **The independence number of the assignment graph.** For a formula `φ` with at most three
literals per clause, the assignment graph on `n` vertices has independence number `val(φ) n / 7`,
where `val(φ) = 1 - unsatVal φ` is the largest proportion of the clauses of `φ` that an assignment
satisfies. -/
theorem indepNum_assignmentGraph {φ : CNF ℕ} (h3 : ∀ c ∈ φ, c.length ≤ 3) :
    ((assignmentGraph φ).indepNum : ℝ) =
      (1 - φ.unsatVal) * (assignmentGraph φ).vertices.toFinset.card / 7 := by
  by_cases hφ : φ.all List.isEmpty = true
  · have h0 := Graph.indepNum_le_card (assignmentGraph φ)
    simp only [assignmentGraph, hφ, ite_true] at h0 ⊢
    simp only [List.toFinset_nil, Finset.card_empty, CharP.cast_eq_zero, mul_zero, zero_div,
      Nat.cast_eq_zero] at h0 ⊢
    omega
  have h7 : (1 - φ.unsatVal) * ((7 * φ.length : ℕ) : ℝ) / 7 = (1 - φ.unsatVal) * φ.length := by
    push_cast
    ring
  rw [card_toFinset_vertices_assignmentGraph hφ, h7]
  have hm : 0 < φ.length := List.length_pos_iff.2 (by rintro rfl; simp at hφ)
  have hm' : (0 : ℝ) < φ.length := by exact_mod_cast hm
  apply le_antisymm
  · obtain ⟨S, hSV, hS⟩ := mem_IndependentSet_iff.1
      (Graph.indepNum_mem_IndependentSet (assignmentGraph φ))
    obtain ⟨σ, hσ⟩ := exists_card_add_countUnsat_le_of_assignmentGraph h3 hφ hSV hS.isIndepSet
    have hc : S.card = (assignmentGraph φ).indepNum := hS.card_eq
    have hle := (le_div_iff₀ hm').1 (φ.unsatVal_le σ)
    have hcast : (S.card : ℝ) + φ.countUnsat σ ≤ φ.length := by exact_mod_cast hσ
    rw [← hc]
    nlinarith
  · obtain ⟨σ, hσ⟩ := φ.exists_countUnsat_div_eq_unsatVal
    have h := length_sub_countUnsat_le_indepNum_assignmentGraph h3 hφ σ
    rw [← hσ, sub_mul, div_mul_cancel₀ _ hm'.ne', one_mul,
      ← Nat.cast_sub (CNF.countUnsat_le_length σ φ)]
    exact_mod_cast h

/-! ### Polynomial time -/

/-- Encoding of a literal `(x, b)` over `ℕ`: the variable index `x` in little-endian binary
(`encNat`), framed, followed by the polarity bit `b` (`encBool`). -/
private abbrev encLit : Literal ℕ ↪ List Bool :=
  encPair encNat encBool

private theorem computableInPolyTime_assignLits (bs : List Bool) :
    ComputableInPolyTime (fun c : Clause ℕ => assignLits c bs) (encList encLit)
      (encList encLit) := by
  fun_prop [assignLits]

@[fun_prop]
private theorem computableInPolyTime_clauseAssignments :
    ComputableInPolyTime clauseAssignments (encList encLit) (encList (encList encLit)) := by
  have := computableInPolyTime_assignLits
  unfold clauseAssignments
  fun_prop

private theorem computableInPolyTime_clusterLabel (k : ℕ) :
    ComputableInPolyTime (fun c => clusterLabel c k) (encList encLit) (encList encLit) := by
  unfold clusterLabel
  fun_prop

private theorem computableInPolyTime_assignmentRecords :
    ComputableInPolyTime assignmentRecords encCNF
      (encList encAssignmentRecord) := by
  have := computableInPolyTime_clusterLabel
  unfold assignmentRecords
  fun_prop

@[fun_prop]
private theorem computableInPolyTime_recordVertex :
    ComputableInPolyTime recordVertex
      encAssignmentRecord encNat := by
  unfold recordVertex
  exact unary_to_binary.comp (by fun_prop)

/-- The assignment graph is polynomial-time: it lists seven records per clause, each with a
label among the local satisfying assignments of the clause, and tests every pair of records. -/
@[fun_prop]
theorem computableInPolyTime_assignmentGraph :
    ComputableInPolyTime assignmentGraph encCNF encGraph := by
  have := computableInPolyTime_assignmentRecords
  unfold assignmentGraph recordConflict
  fun_prop

/-! ### Arora–Barak Lemma 18.16 -/

/-- **Arora–Barak Lemma 18.16** [Arora and Barak, Lemma 18.16][AroraBarak07]. There is a
polynomial-time transformation `f` of formulas into graphs such that, for every 3CNF formula `φ`
with `m` clauses, `f φ` is a graph on `n` vertices whose largest independent set has
`val(φ) n / 7` vertices, and `n = 7 m` as in the draft's construction. Here the 3CNF formulas are
those with at most three literals per clause, `val(φ) = 1 - unsatVal φ` is the largest proportion
of the clauses, counted with multiplicity, that an assignment satisfies, and `n` is the number of
distinct declared vertices. The vertex count `7 m` holds when some clause is nonempty; a formula
all of whose clauses are empty (including the formula without clauses), which the draft's proof
does not treat, gives the graph without vertices, as the value equation then requires. The
transformation is `Cslib.Complexity.SAT.assignmentGraph`. -/
theorem exists_computableInPolyTime_indepNum_eq :
    ∃ f : CNF ℕ → Graph, ComputableInPolyTime f encCNF encGraph ∧
      ∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ 3) →
        ((∃ c ∈ φ, c ≠ []) → (f φ).vertices.toFinset.card = 7 * φ.length) ∧
        ((∀ c ∈ φ, c = []) → (f φ).vertices = []) ∧
        ((f φ).indepNum : ℝ) = (1 - φ.unsatVal) * (f φ).vertices.toFinset.card / 7 := by
  refine ⟨assignmentGraph, computableInPolyTime_assignmentGraph, fun φ h3 =>
    ⟨fun hne => card_toFinset_vertices_assignmentGraph ?_, fun hall => ?_,
      indepNum_assignmentGraph h3⟩⟩
  · simpa [List.all_eq_true, List.isEmpty_iff] using hne
  · have h : φ.all List.isEmpty = true := by simpa [List.all_eq_true, List.isEmpty_iff] using hall
    simp [assignmentGraph, h]

end Cslib.Complexity.SAT
