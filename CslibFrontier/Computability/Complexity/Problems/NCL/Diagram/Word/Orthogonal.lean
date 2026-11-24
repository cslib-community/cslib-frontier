/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.Plane
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridLayout
import Mathlib.Algebra.Order.Group.Nat

/-!
# Orthogonal drawings of plane words

Every checked plane word admits a layered integer-grid drawing. Each layer contains one
three-port cell, vertical bypasses, and two disjoint routing bands. Its outer port columns are
`4 * i`; successive layers therefore glue at equal columns. The cell retains the exact vertex
and the permutation of its weighted ports. `Word.Geometric` joins the edge paths and transports
them to the exact compiled graph.

## Main definitions

* `Cslib.Complexity.NCL.Slice.OrthogonalDrawing`: a cell drawing with its exact port incidences.
* `Cslib.Complexity.NCL.Word.OrthogonalDrawing`: vertically composed cell drawings.

## Main results

* `Cslib.Complexity.NCL.Word.orthogonalDrawing`: every well-typed checked plane word has an
  orthogonal drawing.
-/

public section

namespace Cslib.Complexity.NCL

open Diagram

/-- A grid drawing of one plane layer, including its precise colored port incidences. -/
structure Slice.OrthogonalDrawing (sl : Slice) (source target : List Color) where
  /-- Unchanged prefix wires. -/
  left : List Color
  /-- Cell input colors. -/
  inputs : List Color
  /-- Cell output colors. -/
  outputs : List Color
  /-- Unchanged suffix wires. -/
  right : List Color
  /-- The constraint vertex drawn in this layer. -/
  vertex : Vertex (Fin inputs.length ⊕ Fin outputs.length)
  /-- The exact layer, including vertex data. -/
  layer_eq : sl = .gen left.length inputs outputs [vertex]
  /-- The input stack. -/
  source_eq : source = left ++ inputs ++ right
  /-- The output stack. -/
  target_eq : target = left ++ outputs ++ right
  /-- The vertex uses each colored port once, with the declared reference direction. -/
  ports : vertex.ports.Perm (genVertex inputs outputs 0).ports
  /-- An explicit disjoint routing around the three-port cell. -/
  layout : GridLayout.Layer left.length inputs.length outputs.length right.length

private theorem Vertex.IsAndOr.length_ports {E : Type*} {v : Vertex E} (h : v.IsAndOr) :
    v.ports.length = 3 := by
  rcases h with ⟨a, b, c, _, hp⟩ | ⟨a, b, c, _, hp⟩
  all_goals exact hp.length_eq

/-- A successfully checked layer supplies its exact grid drawing. -/
theorem Slice.orthogonalDrawing {sl : Slice} {source target : List Color}
    (hP : sl.checkPlane = true) (hT : sl.typeRun source = some target) :
    Nonempty (sl.OrthogonalDrawing source target) := by
  cases sl with
  | swap k => cases hP
  | gen k a b vs =>
    simp only [Slice.checkPlane, Bool.and_eq_true, beq_iff_eq] at hP
    obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hP.1
    have hs := hP.2
    simp only [Prim.checkStandard, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at hs
    have hp : v.ports.Perm (genVertex a b 0).ports := by
      have hh := of_decide_eq_true hs.2.2
      simpa only [Prim.interp, List.flatMap_cons, List.flatMap_nil, List.append_nil] using hh
    have hv := ((Vertex.checkAndOr_eq_true_iff v).mp hs.1).length_ports
    have harity : a.length + b.length = 3 := by
      have hh := hp.length_eq
      simp only [genVertex, List.length_append, List.length_map, List.length_finRange] at hh
      omega
    simp only [Slice.typeRun] at hT
    split_ifs at hT with ht
    · have hl : (source.take k).length = k := by simp [List.length_take]; omega
      have ha := ht.2
      have hsource : source = source.take k ++ a ++ source.drop (k + a.length) := by
        calc
          source = source.take (k + a.length) ++ source.drop (k + a.length) :=
            (List.take_append_drop ..).symm
          _ = _ := by rw [List.take_add, ha]
      have htarget := Option.some.inj hT
      refine ⟨⟨source.take k, a, b, source.drop (k + a.length), v, ?_, hsource,
        htarget.symm, hp, GridLayout.layer _ _ _ _ harity⟩⟩
      rw [hl]

/-- A plane word drawn as consecutive rectangular layers with matching ordered interfaces. -/
inductive Word.OrthogonalDrawing : Word → List Color → List Color → Type
  /-- The empty drawing has equal boundaries. -/
  | nil (a : List Color) : OrthogonalDrawing [] a a
  /-- Place the next cell drawing below its predecessor. -/
  | cons {sl : Slice} {w : Word} {a b c : List Color} :
      sl.OrthogonalDrawing a b → OrthogonalDrawing w b c → OrthogonalDrawing (sl :: w) a c

/-- Every well-typed plane word has an orthogonal integer-grid drawing. -/
theorem Word.orthogonalDrawing {w : Word} {a b : List Color}
    (hP : w.checkPlane = true) (hT : w.WellTyped a b) :
    Nonempty (w.OrthogonalDrawing a b) := by
  induction w generalizing a with
  | nil =>
    have hab : a = b := Option.some.inj hT
    subst b
    exact ⟨.nil a⟩
  | cons sl w ih =>
    have hp := hP
    simp only [Word.checkPlane, List.all_cons, Bool.and_eq_true] at hp
    change (sl.typeRun a).bind (fun cs => Word.typeRun w cs) = some b at hT
    cases ht : sl.typeRun a with
    | none => simp only [ht, Option.bind_none] at hT; cases hT
    | some cs =>
      have hw : Word.WellTyped w cs b := by
        simpa only [Word.WellTyped, ht, Option.bind_some] using hT
      obtain ⟨layer⟩ := Slice.orthogonalDrawing hp.1 ht
      obtain ⟨rest⟩ := ih hp.2 hw
      exact ⟨.cons layer rest⟩

end Cslib.Complexity.NCL
