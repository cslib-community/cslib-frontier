/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Digraph.Layered.MinIsolation
public import Mathlib.Combinatorics.Quiver.Path.Weight
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Fin
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Vertex-chain subdivision of a weighted layered graph

A vertex of weight `w` is replaced by a chain of `w` edges, followed by the original
outgoing edges. Slots beyond its weight are isolated. This prepares weighted paths for
the unweighted scans in #6747. The subdivision is an ordinary digraph: weighted routes
need not have equal lengths. This vertex-chain variant is an original construction.

`pathEquiv` identifies original paths with subdivided paths ending at any valid auxiliary
offset. Expansion charges each departure vertex's weight plus one per original edge. For
fixed endpoints the original layer difference fixes that edge count, so minimizing expanded
length is equivalent to minimizing internal vertex weight. Original empty paths are handled
separately: they expand only along the final partial source chain.

## Main results

* `pathEquiv`: exact path correspondence, including auxiliary targets.
* `existsUnique_shortest_of_isMinIsolating`: unique unweighted shortest paths from each root.
* `card_vertex`: exactly `Nat.card V * (bound + 1)` slots, giving polynomial size when the
  original size and weight bound are polynomial.

The consumer `CslibFrontier.Algorithms.Reachability.MinIsolation.Subdivision` transfers this
to the existing scan transcript contract. Native adjacency certificates are in
`CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Subdivision`.
-/

public section

namespace Cslib.LayeredDigraph.Subdivision

/-- A vertex and a bounded position in its subdivision chain. -/
@[ext] structure Vertex (V : Type*) (bound : ℕ) where
  /-- The original vertex whose chain contains this position. -/
  vertex : V
  /-- The chain position; positions above the vertex weight are unused. -/
  offset : Fin (bound + 1)
  deriving DecidableEq

/-- The rectangular carrier, with one slot index for each original vertex. -/
def equivProd (V : Type*) (bound : ℕ) : Vertex V bound ≃ V × Fin (bound + 1) where
  toFun v := (v.vertex, v.offset)
  invFun v := ⟨v.1, v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem equivProd_apply {V : Type*} {bound : ℕ} (v : Vertex V bound) :
    equivProd V bound v = (v.vertex, v.offset) := by
  rfl

instance {V : Type*} [Fintype V] (bound : ℕ) : Fintype (Vertex V bound) :=
  Fintype.ofEquiv _ (equivProd V bound).symm

variable {V : Type*} (G : LayeredDigraph V) (weight : V → ℕ) (bound : ℕ)

/-- The entry of an original vertex's chain. -/
abbrev root (v : V) : Vertex V bound := ⟨v, 0⟩

/-- Chain steps precede each original outgoing edge. Unused offsets are isolated. -/
abbrev graph : Digraph (Vertex V bound) where
  Adj a b :=
    (a.vertex = b.vertex ∧ b.offset.val = a.offset.val + 1 ∧
      b.offset.val ≤ weight a.vertex) ∨
    (a.offset.val = weight a.vertex ∧ b.offset.val = 0 ∧ G.Adj a.vertex b.vertex)

/-- One arrow for every adjacent pair in the subdivision. -/
abbrev toQuiver : Quiver (Vertex V bound) where
  Hom a b := PLift ((graph G weight bound).Adj a b)

instance (a b : Vertex V bound) :
    Subsingleton (@Quiver.Hom _ (toQuiver G weight bound) a b) :=
  inferInstanceAs (Subsingleton (PLift ((graph G weight bound).Adj a b)))

/-- Paths in the subdivision's ordinary directed graph. -/
abbrev Path (a b : Vertex V bound) := @Quiver.Path _ (toQuiver G weight bound) a b

variable {G weight bound}

/-- Every reached chain position is at most its vertex weight. -/
theorem offset_le {s : V} {v : Vertex V bound}
    (p : Path G weight bound (root bound s) v) : v.offset.val ≤ weight v.vertex := by
  induction p with
  | nil => exact Nat.zero_le _
  | @cons a b p e ih =>
    rcases e.down with ⟨h, _, hi⟩ | ⟨_, h, _⟩
    · rwa [h] at hi
    · rw [h]; exact Nat.zero_le _

/-- The deterministic prefix of a vertex chain, ending at position `i`. -/
def chain (v : V) (i : ℕ) (hi : i ≤ weight v) (hb : i ≤ bound) :
    Path G weight bound (root bound v) ⟨v, ⟨i, Nat.lt_succ_of_le hb⟩⟩ := by
  letI := toQuiver G weight bound
  induction i with
  | zero => exact .nil
  | succ i ih => exact (ih (by omega) (by omega)).cons ⟨Or.inl ⟨rfl, rfl, hi⟩⟩

/-- Expand each original edge through its departure vertex's chain. -/
def expand (hw : ∀ v, weight v ≤ bound) {a b : V} (p : G.Path a b) :
    Path G weight bound (root bound a) (root bound b) := by
  letI := G.toQuiver
  letI := toQuiver G weight bound
  induction p with
  | nil => exact .nil
  | @cons b c p e ih =>
    exact (ih.comp (chain b (weight b) le_rfl (hw b))).cons ⟨Or.inr ⟨rfl, rfl, e.down⟩⟩

/-- Contract chain edges and keep exactly the original graph edges. -/
noncomputable def contract {a b : Vertex V bound}
    (p : Path G weight bound a b) : G.Path a.vertex b.vertex := by
  classical
  letI := G.toQuiver
  induction p with
  | nil => exact .nil
  | @cons a b p e ih =>
    by_cases h : a.vertex = b.vertex
    · exact h ▸ ih
    · have he : G.Adj a.vertex b.vertex := e.down.elim (fun he => (h he.1).elim) (fun he => he.2.2)
      exact ih.cons ⟨he⟩

private theorem contract_cons_eq {s a b : Vertex V bound}
    (p : Path G weight bound s a) (e : PLift ((graph G weight bound).Adj a b))
    (h : a.vertex = b.vertex) :
    contract (@Quiver.Path.cons _ (toQuiver G weight bound) _ _ _ p e) = h ▸ contract p := by
  classical
  simp only [contract, dite_eq_left h]

private theorem contract_cons_ne {s a b : Vertex V bound}
    (p : Path G weight bound s a) (e : PLift ((graph G weight bound).Adj a b))
    (h : a.vertex ≠ b.vertex) :
    contract (@Quiver.Path.cons _ (toQuiver G weight bound) _ _ _ p e) =
      @Quiver.Path.cons _ G.toQuiver _ _ _ (contract p)
        ⟨e.down.elim (fun he => (h he.1).elim) (fun he => he.2.2)⟩ := by
  classical
  simp only [contract, dite_eq_right h]

private theorem contract_comp {a b c : Vertex V bound}
    (p : Path G weight bound a b) (q : Path G weight bound b c) :
    contract (@Quiver.Path.comp _ (toQuiver G weight bound) _ _ _ p q) =
      LayeredDigraph.Path.comp (contract p) (contract q) := by
  classical
  let _ := G.toQuiver
  let _ := toQuiver G weight bound
  induction q with
  | nil => rfl
  | @cons b c q e ih =>
    rw [Quiver.Path.comp_cons]
    by_cases h : b.vertex = c.vertex
    · rw [contract_cons_eq _ _ h, contract_cons_eq _ _ h, ih]
      cases b with | mk b bi =>
        cases c with | mk c ci =>
          change b = c at h
          subst c
          rfl
    · rw [contract_cons_ne _ _ h, contract_cons_ne _ _ h]
      exact congrArg (fun r => @Quiver.Path.cons V G.toQuiver _ _ _ r _) ih

private theorem contract_chain (v : V) (i : ℕ) (hi : i ≤ weight v) (hb : i ≤ bound) :
    contract (chain (G := G) v i hi hb) = @Quiver.Path.nil V G.toQuiver v :=
  LayeredDigraph.Path.eq_of_layer_le_succ (Nat.le_succ _) _ _

/-- Expanding and contracting recovers the path, not just its endpoints. -/
theorem contract_expand (hw : ∀ v, weight v ≤ bound) {a b : V} (p : G.Path a b) :
    contract (expand hw p) = p := by
  classical
  let _ := G.toQuiver
  let _ := toQuiver G weight bound
  induction p with
  | nil => rfl
  | @cons b c p e ih =>
    have hne : b ≠ c := by
      intro h
      have he := G.layer_adj e.down
      rw [h] at he
      omega
    change contract (@Quiver.Path.cons _ (toQuiver G weight bound) (root bound a)
      ⟨b, ⟨weight b, Nat.lt_succ_of_le (hw b)⟩⟩ (root bound c)
      ((expand hw p).comp (chain b (weight b) le_rfl (hw b)))
        ⟨Or.inr ⟨rfl, rfl, e.down⟩⟩) = p.cons e
    rw [contract_cons_ne _ _ hne, contract_comp, contract_chain]
    exact congrArg (fun r => @Quiver.Path.cons V G.toQuiver a b c r e) ih

private theorem chain_step (v : V) (a b : Fin (bound + 1))
    (e : PLift ((graph G weight bound).Adj ⟨v, a⟩ ⟨v, b⟩))
    (ha : a.val ≤ weight v) (hb : b.val ≤ weight v)
    (hoff : b.val = a.val + 1) :
    @Quiver.Path.cons _ (toQuiver G weight bound) _ _ _
      (chain v a.val ha (Nat.le_of_lt_succ a.isLt)) e =
      chain v b.val hb (Nat.le_of_lt_succ b.isLt) := by
  have hn : a.val + 1 < bound + 1 := by have := b.isLt; omega
  have hbi : b = ⟨a.val + 1, hn⟩ := Fin.ext hoff
  subst b
  rfl

/-- Every subdivided path is an expanded original path followed by a final chain prefix.
The statement includes auxiliary endpoints, not only the original graph's vertices. -/
theorem normal_form (hw : ∀ v, weight v ≤ bound) {s : V} {v : Vertex V bound}
    (p : Path G weight bound (root bound s) v) :
    p = @Quiver.Path.comp _ (toQuiver G weight bound) _ _ _
      (expand hw (contract p))
      (chain v.vertex v.offset.val (offset_le p) (Nat.le_of_lt_succ v.offset.isLt)) := by
  classical
  let _ := G.toQuiver
  let _ := toQuiver G weight bound
  induction p with
  | nil => rfl
  | @cons a b p e ih =>
    by_cases h : a.vertex = b.vertex
    · have he : b.offset.val = a.offset.val + 1 := by
        rcases e.down with he | he
        · exact he.2.1
        · have hl := G.layer_adj he.2.2
          rw [h] at hl
          omega
      rw [contract_cons_eq _ _ h]
      cases a with | mk a ai =>
        cases b with | mk b bi =>
          change a = b at h
          subst b
          change p.cons e = (expand hw (contract p)).comp _
          calc
            p.cons e = ((expand hw (contract p)).comp
                (chain a ai.val (offset_le p) (Nat.le_of_lt_succ ai.isLt))).cons e :=
              congrArg (fun q => q.cons e) ih
            _ = (expand hw (contract p)).comp
                ((chain a ai.val (offset_le p) (Nat.le_of_lt_succ ai.isLt)).cons e) := rfl
            _ = _ := congrArg (fun q => (expand hw (contract p)).comp q)
              (chain_step a ai bi e (offset_le p) (offset_le (p.cons e)) he)
    · have he : a.offset.val = weight a.vertex ∧ b.offset.val = 0 ∧ G.Adj a.vertex b.vertex :=
        e.down.elim (fun he => (h he.1).elim) id
      rw [contract_cons_ne _ _ h]
      cases a with | mk a ai =>
        cases b with | mk b bi =>
          obtain ⟨ha, hb, hab⟩ := he
          have hai : ai = ⟨weight a, Nat.lt_succ_of_le (hw a)⟩ := Fin.ext ha
          have hbi : bi = 0 := Fin.ext hb
          subst ai
          subst bi
          conv_lhs => rw [ih]
          rfl

/-- Original paths correspond bijectively to subdivided paths ending at any valid offset. -/
noncomputable def pathEquiv (hw : ∀ v, weight v ≤ bound) (s : V) (v : Vertex V bound)
    (hv : v.offset.val ≤ weight v.vertex) :
    G.Path s v.vertex ≃ Path G weight bound (root bound s) v where
  toFun p := @Quiver.Path.comp _ (toQuiver G weight bound) _ _ _ (expand hw p)
    (chain v.vertex v.offset.val hv (Nat.le_of_lt_succ v.offset.isLt))
  invFun := contract
  left_inv p := by
    rw [contract_comp, contract_chain, contract_expand]
    rfl
  right_inv p := (normal_form hw p).symm

private theorem nonempty_path_iff_reachable {W : Type*} (r : W → W → Prop) (a b : W) :
    Nonempty (@Quiver.Path W ⟨fun u v => PLift (r u v)⟩ a b) ↔
      Relation.ReflTransGen r a b := by
  let _ : Quiver W := ⟨fun u v => PLift (r u v)⟩
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact .refl
    | cons _ e ih => exact ih.tail e.down
  · intro h
    induction h with
    | refl => exact ⟨.nil⟩
    | tail _ e ih => exact ih.map (fun p => p.cons ⟨e⟩)

/-- Reachability between subdivision roots is exactly reachability between the original
vertices, for every weight assignment within the subdivision bound. -/
theorem reachable_root_iff (hw : ∀ v, weight v ≤ bound) (s t : V) :
    Relation.ReflTransGen (graph G weight bound).Adj (root bound s) (root bound t) ↔
      Relation.ReflTransGen G.Adj s t := by
  let e := pathEquiv (G := G) hw s (root bound t) (Nat.zero_le _)
  rw [← nonempty_path_iff_reachable, ← nonempty_path_iff_reachable]
  exact ⟨fun h => h.map e.symm, fun h => h.map e⟩

/-- The rectangular subdivision has at most the number of vertices times one plus the
uniform weight bound; unused positions remain isolated. -/
theorem card_vertex : Nat.card (Vertex V bound) = Nat.card V * (bound + 1) := by
  rw [Nat.card_congr (equivProd V bound), Nat.card_prod, Nat.card_fin]

private theorem length_chain (v : V) (i : ℕ) (hi : i ≤ weight v) (hb : i ≤ bound) :
    @Quiver.Path.length _ (toQuiver G weight bound) _ _ (chain v i hi hb) = i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change @Quiver.Path.length _ (toQuiver G weight bound) _ _
      (chain v i (by omega) (by omega)) + 1 = i + 1
    rw [ih]

/-- Expansion replaces departure weight by literal unweighted edges, with one extra edge
per original edge. The formula includes the empty path. -/
theorem length_expand (hw : ∀ v, weight v ≤ bound) {a b : V} (p : G.Path a b) :
    @Quiver.Path.length _ (toQuiver G weight bound) _ _ (expand hw p) =
      @Quiver.Path.addWeightOfEPs V G.toQuiver ℕ _ (fun v _ => weight v + 1) _ _ p := by
  let _ := G.toQuiver
  let _ := toQuiver G weight bound
  induction p with
  | nil => exact (Quiver.Path.addWeightOfEPs_nil _ _).symm
  | @cons b c p e ih =>
    change ((expand hw p).comp (chain b (weight b) le_rfl (hw b))).length + 1 = _
    rw [Quiver.Path.length_comp, length_chain, ih, Quiver.Path.addWeightOfEPs_cons]
    omega

/-- The path bijection preserves length as departure cost plus the final partial chain. -/
theorem length_pathEquiv (hw : ∀ v, weight v ≤ bound) (s : V) (v : Vertex V bound)
    (hv : v.offset.val ≤ weight v.vertex) (p : G.Path s v.vertex) :
    @Quiver.Path.length _ (toQuiver G weight bound) _ _ (pathEquiv hw s v hv p) =
      @Quiver.Path.addWeightOfEPs V G.toQuiver ℕ _ (fun u _ => weight u + 1) _ _ p +
        v.offset.val := by
  let _ := toQuiver G weight bound
  change @Quiver.Path.length _ (toQuiver G weight bound) _ _
    (@Quiver.Path.comp _ (toQuiver G weight bound) _ _ _ _ _) = _
  rw [Quiver.Path.length_comp, length_expand, length_chain]

private theorem departureCost_eq {a b : V} (p : G.Path a b) (h : a ≠ b) :
    @Quiver.Path.addWeightOfEPs V G.toQuiver ℕ _ (fun u _ => weight u + 1) _ _ p =
      p.internalWeight weight + weight a + p.length := by
  let _ := G.toQuiver
  induction p with
  | nil => exact (h rfl).elim
  | @cons b c p e ih =>
    by_cases hab : a = b
    · subst b
      have hp : p = Quiver.Path.nil :=
        LayeredDigraph.Path.eq_of_layer_le_succ (Nat.le_succ _) _ _
      subst p
      simp [Quiver.Path.addWeightOfEPs_cons, Quiver.Path.addWeightOfEPs_nil,
        LayeredDigraph.Path.internalWeight, LayeredDigraph.Path.internalVertices,
        Quiver.Path.vertices_cons, Quiver.Path.vertices_nil, LayeredDigraph.Path.length]
    · have hp : G.layer a < G.layer b := by
        have hl := LayeredDigraph.Path.layer_end (G := G) p
        change G.layer b = G.layer a + p.length at hl
        have hn : p.length ≠ 0 := fun hz => hab (p.eq_of_length_zero hz)
        omega
      have he : G.layer b < G.layer c := by have := G.layer_adj e.down; omega
      have hw := LayeredDigraph.Path.internalWeight_comp weight p
        (LayeredDigraph.Path.ofAdj e.down) hp he
      have hz : (LayeredDigraph.Path.ofAdj e.down).internalWeight weight = 0 := rfl
      change LayeredDigraph.Path.internalWeight weight (p.cons e) = _ at hw
      rw [hz, Nat.add_zero] at hw
      rw [Quiver.Path.addWeightOfEPs_cons, ih hab, hw]
      change _ = _ + weight a + (p.length + 1)
      dsimp only [LayeredDigraph.Path.length] at *
      omega

/-- For a fixed pair of endpoints and final offset, expansion orders paths by internal weight. -/
theorem length_pathEquiv_le_iff (hw : ∀ v, weight v ≤ bound) (s : V) (v : Vertex V bound)
    (hv : v.offset.val ≤ weight v.vertex) (p q : G.Path s v.vertex) :
    @Quiver.Path.length _ (toQuiver G weight bound) _ _ (pathEquiv hw s v hv p) ≤
      @Quiver.Path.length _ (toQuiver G weight bound) _ _ (pathEquiv hw s v hv q) ↔
      p.internalWeight weight ≤ q.internalWeight weight := by
  let _ := G.toQuiver
  let _ := toQuiver G weight bound
  by_cases heq : s = v.vertex
  · have hsame := LayeredDigraph.Path.eq_of_layer_le_succ
      (by rw [heq]; exact Nat.le_succ _) p q
    simp [hsame]
  · rw [length_pathEquiv, length_pathEquiv, departureCost_eq p heq, departureCost_eq q heq]
    have hp := LayeredDigraph.Path.layer_end p
    have hq := LayeredDigraph.Path.layer_end q
    have hlen : p.length = q.length := by
      change G.layer v.vertex = G.layer s + p.length at hp
      change G.layer v.vertex = G.layer s + q.length at hq
      omega
    dsimp only [LayeredDigraph.Path.length] at *
    omega

/-- Min-isolation of the original vertex weights gives a unique shortest unweighted path
from each original source to every reachable subdivision vertex, including auxiliary slots.
Zero weights are allowed: the original outgoing edge still contributes one positive step. -/
theorem existsUnique_shortest_of_isMinIsolating (hw : ∀ v, weight v ≤ bound)
    (hG : G.IsMinIsolating weight) (s : V) (v : Vertex V bound)
    (hv : Nonempty (Path G weight bound (root bound s) v)) :
    ∃! p : Path G weight bound (root bound s) v,
      ∀ q : Path G weight bound (root bound s) v,
        @Quiver.Path.length _ (toQuiver G weight bound) _ _ p ≤
          @Quiver.Path.length _ (toQuiver G weight bound) _ _ q := by
  let _ := G.toQuiver
  let _ := toQuiver G weight bound
  obtain ⟨p₀⟩ := hv
  let E := pathEquiv (G := G) hw s v (offset_le p₀)
  refine (E.existsUnique_congr fun p => ?_).mp (hG s v.vertex ⟨contract p₀⟩)
  rw [isMinOn_univ_iff]
  constructor
  · intro h q
    have hle := (length_pathEquiv_le_iff hw s v (offset_le p₀) p (E.symm q)).mpr (h _)
    change (E p).length ≤ (E (E.symm q)).length at hle
    simpa only [E.apply_symm_apply] using hle
  · intro h q
    exact (length_pathEquiv_le_iff hw s v (offset_le p₀) p q).mp (h (E q))

end Cslib.LayeredDigraph.Subdivision
