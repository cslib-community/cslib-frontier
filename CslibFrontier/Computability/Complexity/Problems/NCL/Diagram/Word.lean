/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Basic
public import Mathlib.Data.List.OfFn

/-!
# Diagrams as words

A word lists the layers of a diagram from top to bottom (`Cslib.Complexity.NCL.Word`). Each layer
(`Cslib.Complexity.NCL.Slice`) acts on a stack of wires at an offset: a generator replaces some
wires by new ones, a crossing exchanges two neighbouring wires. Running a word
(`Cslib.Complexity.NCL.Word.run`) numbers the edges in order of creation and lists the vertices,
so a word is the data of a constraint graph with edges named by natural numbers.

Every diagram is flattened to a word (`Cslib.Complexity.NCL.Diagram.toWord`), and running the
word gives the graph of the diagram up to the numbering of its edges
(`Cslib.Complexity.NCL.Diagram.run_toWord`): the edges of the diagram are named by
`Cslib.Complexity.NCL.Diagram.name`, the wires on top by the given numbers and the wires created
inside in order of creation.

## Main definitions

* `Cslib.Complexity.NCL.Slice`, `Cslib.Complexity.NCL.Word`, `Cslib.Complexity.NCL.Word.run`.
* `Cslib.Complexity.NCL.Diagram.toWord`: the layers of a diagram.
* `Cslib.Complexity.NCL.Diagram.vertexList`: the vertices of a diagram, in the order of its
  layers.

## Main results

* `Cslib.Complexity.NCL.Diagram.run_toWord`: running the word of a diagram builds its graph.
-/

public section

namespace Cslib.Complexity.NCL

/-- One layer of a diagram, acting on a stack of wires. -/
inductive Slice
  /-- A generator taking the wires `a` from offset `k` and leaving the wires `b`, made of the
  vertices `vs` on its own wires. -/
  | gen (k : ℕ) (a b : List Color) (vs : List (Vertex (Fin a.length ⊕ Fin b.length)))
  /-- The wires at offsets `k` and `k + 1` cross. -/
  | swap (k : ℕ)
  deriving @[expose] DecidableEq

/-- The state of a run: the edges on the current wires, the next edge number, and the vertices
built so far. -/
structure Word.State where
  /-- The edge on each current wire. -/
  wires : List ℕ
  /-- The number of the next new edge. -/
  next : ℕ
  /-- The vertices built so far. -/
  verts : List (Vertex ℕ)

/-- Run one layer. -/
@[expose] def Slice.run : Slice → Word.State → Word.State
  | .gen k a b us, ⟨w, c, vs⟩ =>
    ⟨w.take k ++ List.ofFn (fun j : Fin b.length => c + j) ++ w.drop (k + a.length),
      c + b.length,
      vs ++ us.map (Vertex.map
        (Sum.elim (fun i : Fin a.length => w.getD (k + i) 0) (fun j : Fin b.length => c + j)))⟩
  | .swap k, ⟨w, c, vs⟩ => ⟨w.take k ++ [w.getD (k + 1) 0, w.getD k 0] ++ w.drop (k + 2), c, vs⟩

/-- A word: the layers of a diagram, from top to bottom. -/
abbrev Word := List Slice

/-- Run the layers of a word in order. -/
@[expose]
def Word.run (w : Word) (st : Word.State) : Word.State := w.foldl (fun st sl => sl.run st) st

theorem Word.run_append (w₁ w₂ : Word) (st : Word.State) :
    Word.run (w₁ ++ w₂) st = Word.run w₂ (Word.run w₁ st) :=
  List.foldl_append ..

namespace Diagram

variable {Γ : List Color → List Color → Type} (I : Interp Γ) {a b c d : List Color}

/-- The layers of a diagram whose top wires start at offset `k`. -/
@[expose] def toWord : {a b : List Color} → Diagram Γ a b → ℕ → Word
  | a, b, gen g, k => [.gen k a b (I.verts g)]
  | _, _, id _, _ => []
  | _, _, swap .., k => [.swap k]
  | _, _, comp D₁ D₂, k => toWord D₁ k ++ toWord D₂ k
  | _, _, @tensor _ _ b _ _ D₁ D₂, k => toWord D₁ k ++ toWord D₂ (k + b.length)

/-- The number of wires created inside a diagram. -/
@[expose] def innerCount : {a b : List Color} → Diagram Γ a b → ℕ
  | _, b, gen _ => b.length
  | _, _, id _ => 0
  | _, _, swap .. => 0
  | _, _, comp D₁ D₂ => innerCount D₁ + innerCount D₂
  | _, _, tensor D₁ D₂ => innerCount D₁ + innerCount D₂

/-- The position of a created wire in the order of creation. -/
@[expose] def idx : {a b : List Color} → (D : Diagram Γ a b) → D.Inner → ℕ
  | _, b, gen _, j => (show Fin b.length from j).val
  | _, _, id _, e => e.elim
  | _, _, swap .., e => e.elim
  | _, _, comp D₁ D₂, e => Sum.elim (idx D₁) (fun e => innerCount D₁ + idx D₂ e) e
  | _, _, tensor D₁ D₂, e => Sum.elim (idx D₁) (fun e => innerCount D₁ + idx D₂ e) e

/-- The number of each edge: the given number of a top wire, or `c` plus the position of a
created wire. -/
@[expose] def name (D : Diagram Γ a b) (top : Fin a.length → ℕ) (c : ℕ) : D.Edge → ℕ :=
  Sum.elim top fun e => c + idx D e

private theorem sumElim_lt (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (h₁ : ∀ e, idx D₁ e < innerCount D₁) (h₂ : ∀ e, idx D₂ e < innerCount D₂) :
    ∀ e : D₁.Inner ⊕ D₂.Inner,
      Sum.elim (idx D₁) (fun e => innerCount D₁ + idx D₂ e) e < innerCount D₁ + innerCount D₂
  | .inl e => Nat.lt_of_lt_of_le (h₁ e) (Nat.le_add_right _ _)
  | .inr e => Nat.add_lt_add_left (h₂ e) _

theorem idx_lt : {a b : List Color} → (D : Diagram Γ a b) → (e : D.Inner) → idx D e < innerCount D
  | _, _, gen _, j => j.isLt
  | _, _, id _, e => e.elim
  | _, _, swap .., e => e.elim
  | _, _, comp D₁ D₂, e => sumElim_lt D₁ D₂ (idx_lt D₁) (idx_lt D₂) e
  | _, _, tensor D₁ D₂, e => sumElim_lt D₁ D₂ (idx_lt D₁) (idx_lt D₂) e

private theorem idx_sumElim_injective (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (h₁ : Function.Injective (idx D₁)) (h₂ : Function.Injective (idx D₂)) :
    Function.Injective (Sum.elim (idx D₁) fun e => innerCount D₁ + idx D₂ e) := by
  rintro (e | e) (e' | e') h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
  · rw [h₁ h]
  · have := idx_lt D₁ e
    omega
  · have := idx_lt D₁ e'
    omega
  · rw [h₂ (Nat.add_left_cancel h)]

private theorem idx_injective :
    {a b : List Color} → (D : Diagram Γ a b) → Function.Injective (idx D)
  | _, _, gen _ => fun _ _ h => Fin.ext h
  | _, _, id _ => fun e => e.elim
  | _, _, swap .. => fun e => e.elim
  | _, _, comp D₁ D₂ => idx_sumElim_injective D₁ D₂ (idx_injective D₁) (idx_injective D₂)
  | _, _, tensor D₁ D₂ => idx_sumElim_injective D₁ D₂ (idx_injective D₁) (idx_injective D₂)

/-- The numbering of the edges of a diagram: the top wires first, then the created wires in the
order of creation. -/
@[expose] def num (D : Diagram Γ a b) : D.Edge → ℕ := name D Fin.val a.length

/-- Every edge name precedes the next unused name, when the incoming names do. -/
theorem name_lt (D : Diagram Γ a b) (top : Fin a.length → ℕ) (k : ℕ)
    (htop : ∀ i, top i < k) (e : D.Edge) : name D top k e < k + innerCount D := by
  rcases e with i | e
  · exact (htop i).trans_le (Nat.le_add_right _ _)
  · exact Nat.add_lt_add_left (idx_lt D e) k

/-- The edge numbers are bounded by the top wires and the wires created inside. -/
theorem num_lt (D : Diagram Γ a b) (e : D.Edge) :
    D.num e < a.length + innerCount D := name_lt D Fin.val a.length (fun i => i.isLt) e

theorem num_injective (D : Diagram Γ a b) : Function.Injective D.num := by
  rintro (i | e) (i' | e') h <;> simp only [num, name, Sum.elim_inl, Sum.elim_inr] at h
  · rw [Fin.ext h]
  · omega
  · omega
  · rw [idx_injective D (Nat.add_left_cancel h)]

/-- The vertices of a diagram, in the order of its layers. -/
@[expose] def vertexList : {a b : List Color} → (D : Diagram Γ a b) → List (Vertex D.Edge)
  | _, _, gen g => I.verts g
  | _, _, id _ => []
  | _, _, swap .. => []
  | _, _, comp D₁ D₂ =>
    (vertexList D₁).map (Vertex.map (compLeft D₁ D₂)) ++
      (vertexList D₂).map (Vertex.map (compRight D₁ D₂))
  | _, _, tensor D₁ D₂ =>
    (vertexList D₁).map (Vertex.map (tensorLeft D₁ D₂)) ++
      (vertexList D₂).map (Vertex.map (tensorRight D₁ D₂))

/-! ### Running the word of a diagram -/

variable {I}

private theorem take_prefix {P L S : List ℕ} {k : ℕ} (h : P.length = k) :
    (P ++ L ++ S).take k = P := by
  rw [List.append_assoc]
  exact List.take_left' h

private theorem drop_prefix {P S : List ℕ} {k n : ℕ} (h : P.length = k) (f : Fin n → ℕ) :
    (P ++ List.ofFn f ++ S).drop (k + n) = S :=
  List.drop_left' (by simp [h])

private theorem getD_prefix {P S : List ℕ} {k n : ℕ} (h : P.length = k) (f : Fin n → ℕ)
    (i : Fin n) : (P ++ List.ofFn f ++ S).getD (k + i) 0 = f i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, List.getElem?_append_left, h]

theorem name_compLeft (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c) (top : Fin a.length → ℕ)
    (k : ℕ) (x : D₁.Edge) : name (comp D₁ D₂) top k (compLeft D₁ D₂ x) = name D₁ top k x := by
  rcases x with i | e <;> rfl

theorem name_compRight (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c) (top : Fin a.length → ℕ)
    (k : ℕ) (x : D₂.Edge) :
    name (comp D₁ D₂) top k (compRight D₁ D₂ x) =
      name D₂ (fun j => name D₁ top k (D₁.bottom j)) (k + innerCount D₁) x := by
  rcases x with i | e
  · exact name_compLeft D₁ D₂ top k _
  · exact (Nat.add_assoc ..).symm

theorem name_tensorLeft (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (top : Fin (a ++ c).length → ℕ) (k : ℕ) (x : D₁.Edge) :
    name (tensor D₁ D₂) top k (tensorLeft D₁ D₂ x) =
      name D₁ (fun i => top ((List.appendIndexEquiv a c) (.inl i))) k x := by
  rcases x with i | e <;> rfl

theorem name_tensorRight (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (top : Fin (a ++ c).length → ℕ) (k : ℕ) (x : D₂.Edge) :
    name (tensor D₁ D₂) top k (tensorRight D₁ D₂ x) =
      name D₂ (fun j => top ((List.appendIndexEquiv a c) (.inr j))) (k + innerCount D₁) x := by
  rcases x with i | e
  · rfl
  · exact (Nat.add_assoc ..).symm

/-- **Running the word of a diagram builds its graph.** Started on a stack whose wires from offset
`k` carry the edges `top`, with `c` the next edge number, the run replaces those wires by the
bottom wires of the diagram, creates its inner edges `c, c + 1, …`, and adds its vertices, all
named by `Cslib.Complexity.NCL.Diagram.name`. -/
theorem run_toWord {a b : List Color} (D : Diagram Γ a b) (k : ℕ) (P S : List ℕ)
    (hP : P.length = k) (top : Fin a.length → ℕ) (c : ℕ) (vs : List (Vertex ℕ)) :
    Word.run (toWord I D k) ⟨P ++ List.ofFn top ++ S, c, vs⟩ =
      ⟨P ++ List.ofFn (fun j => name D top c (D.bottom j)) ++ S, c + innerCount D,
        vs ++ (vertexList I D).map (Vertex.map (name D top c))⟩ := by
  induction D generalizing k P S c vs with
  | gen g =>
    simp only [toWord, Word.run, List.foldl_cons, List.foldl_nil, Slice.run, take_prefix hP,
      drop_prefix hP, getD_prefix hP, vertexList]
    rfl
  | id a =>
    simp [toWord, Word.run, innerCount, vertexList, name, bottom]
  | swap x y =>
    subst hP
    simp [toWord, Word.run, Slice.run, innerCount, vertexList, name, bottom, List.ofFn_succ,
      Fin.rev]
  | comp D₁ D₂ ih₁ ih₂ =>
    rw [toWord, Word.run_append, ih₁ k P S hP top c vs, ih₂ k P S hP]
    simp only [bottom_comp, name_compRight, innerCount, Nat.add_assoc, vertexList, List.map_append,
      List.map_map, List.append_assoc, Vertex.map_comp_map (name_compLeft D₁ D₂ top c),
      Vertex.map_comp_map (name_compRight D₁ D₂ top c)]
  | @tensor a b c' d D₁ D₂ ih₁ ih₂ =>
    rw [toWord, Word.run_append, List.ofFn_appendIndexEquiv a c' top, ← List.append_assoc P,
      List.append_assoc (P ++ _), ih₁ k P _ hP, ← List.append_assoc,
      ih₂ (k + b.length) _ S (by simp [hP])]
    simp only [Word.State.mk.injEq]
    refine ⟨?_, Nat.add_assoc .., ?_⟩
    · rw [List.ofFn_appendIndexEquiv b d
        (fun j => name (tensor D₁ D₂) top c ((tensor D₁ D₂).bottom j))]
      simp only [bottom_tensor_left, bottom_tensor_right, name_tensorLeft, name_tensorRight,
        List.append_assoc]
    · simp only [vertexList, List.map_append, List.map_map, List.append_assoc,
        Vertex.map_comp_map (name_tensorLeft D₁ D₂ top c),
        Vertex.map_comp_map (name_tensorRight D₁ D₂ top c)]

/-- The vertex list and the graph contain the same vertices, for any vertex predicate. -/
theorem forall_mem_vertexList_iff {a b : List Color} (D : Diagram Γ a b)
    (P : Vertex D.Edge → Prop) :
    (∀ v ∈ vertexList I D, P v) ↔ ∀ v, P (D.graph I v) := by
  induction D with
  | gen g =>
    refine ⟨fun h i => h _ (List.getElem_mem _), fun h v hv => ?_⟩
    obtain ⟨i, rfl⟩ := List.get_of_mem hv
    exact h i
  | id _ | swap _ _ => simp [vertexList, graph, Vtx]
  | comp D₁ D₂ ih₁ ih₂ | tensor D₁ D₂ ih₁ ih₂ =>
    simp only [vertexList, List.forall_mem_append, List.forall_mem_map, graph, Vtx, Sum.forall,
      Sum.elim_inl, Sum.elim_inr]
    exact and_congr (ih₁ _) (ih₂ _)

/-- The vertices of the list impose precisely the graph's legality constraints. -/
theorem forall_vertexList_iff {a b : List Color} (D : Diagram Γ a b) (s : D.Edge → Bool) :
    (∀ v ∈ vertexList I D, v.Sat s) ↔ (D.graph I).Legal s :=
  forall_mem_vertexList_iff D (fun v => v.Sat s)

/-- Decide legality directly on the diagram's explicit vertex list. -/
@[expose, instance_reducible]
def decidableLegal {a b : List Color} (D : Diagram Γ a b) (s : D.Edge → Bool) :
    Decidable ((D.graph I).Legal s) :=
  decidable_of_iff _ (forall_vertexList_iff D s)

/-- **The word of a closed diagram builds its graph**: the run numbers the edges `0, 1, …` in
order of creation, and an orientation of the numbered edges satisfies every listed vertex exactly
when it is a configuration of the diagram, read through the numbering. -/
theorem run_toWord_closed (D : Diagram Γ [] []) :
    Word.run (toWord I D 0) ⟨[], 0, []⟩ =
      ⟨[], innerCount D, (vertexList I D).map (Vertex.map (name D Fin.elim0 0))⟩ := by
  simpa using run_toWord D 0 [] [] rfl Fin.elim0 0 []

theorem forall_run_toWord_iff (D : Diagram Γ [] []) (s : ℕ → Bool) :
    (∀ v ∈ (Word.run (toWord I D 0) ⟨[], 0, []⟩).verts, v.Sat s) ↔
      (D.graph I).Legal (s ∘ name D Fin.elim0 0) := by
  rw [run_toWord_closed, ← forall_vertexList_iff]
  simp

end Diagram

end Cslib.Complexity.NCL
