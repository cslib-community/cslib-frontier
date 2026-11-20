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

/-!
# Vertex-chain subdivision of a weighted layered graph

A vertex of weight `w` is replaced by a chain of `w` edges, followed by the original
outgoing edges. Slots beyond its weight are isolated. This prepares weighted paths for
the unweighted scans in #6747. The subdivision is an ordinary digraph: weighted routes
need not have equal lengths.
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
theorem normalForm (hw : ∀ v, weight v ≤ bound) {s : V} {v : Vertex V bound}
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

end Cslib.LayeredDigraph.Subdivision
