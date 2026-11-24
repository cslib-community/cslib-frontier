/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.Origin
import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Vertices
import Mathlib.Logic.Equiv.Sum
import CslibFrontier.Foundations.Data.Nat.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinal bounds for planarization origins

Each syntactic crossing owns at most 286 output vertices. Original source positions own at most
one vertex, and nonrepeated cap labels own at most sixteen vertices. Arbitrary row assignments
inherit the weighted sum of these three local bounds.

## Main results

* `Planar.crossingOrigin_fiber_le`: the local crossover bound for actual planarized vertices.
* `Planar.Embedding.sourceVertexOrigin_fiber_le`: at most one vertex per original source position.
* `Planar.Embedding.capVertexOrigin_fiber_le`: at most sixteen vertices per distinct cap label.
* `Planar.Embedding.planeVertexOrigin_fiber_le`: the three bounds on the actual closed diagram.
* `Planar.Embedding.planeVertexOrigin_row_fiber_le`: the resulting budget under any row assignment.
-/

public section

namespace Cslib.Complexity.NCL.Planar

open Diagram
open scoped BigOperators

private theorem card_fiber_castAdd {A B : Type*} [Finite A] [Finite B] {n m : ℕ}
    (f : A → Fin n) (g : B → Fin m) (i : Fin n) :
    Nat.card {v : A ⊕ B //
      Sum.elim (fun a => (f a).castAdd m) (fun b => Fin.natAdd n (g b)) v = i.castAdd m} =
      Nat.card {a // f a = i} := by
  rw [Nat.card_subtype_sum]
  simp only [Sum.elim_inl, Sum.elim_inr]
  let : IsEmpty {b // Fin.natAdd n (g b) = i.castAdd m} := ⟨fun b => by
    have he := congrArg Fin.val b.property
    have hi := i.isLt
    change n + (g b.val).val = i.val at he
    omega⟩
  simp only [Nat.card_of_isEmpty, Nat.add_zero]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun a => ⟨
    fun he => Fin.ext (congrArg (fun z : Fin (n + m) => z.val) he),
    fun he => congrArg (Fin.castAdd m) he⟩)

private theorem card_fiber_natAdd {A B : Type*} [Finite A] [Finite B] {n m : ℕ}
    (f : A → Fin n) (g : B → Fin m) (i : Fin m) :
    Nat.card {v : A ⊕ B //
      Sum.elim (fun a => (f a).castAdd m) (fun b => Fin.natAdd n (g b)) v = Fin.natAdd n i} =
      Nat.card {b // g b = i} := by
  rw [Nat.card_subtype_sum]
  simp only [Sum.elim_inl, Sum.elim_inr]
  let : IsEmpty {a // (f a).castAdd m = Fin.natAdd n i} := ⟨fun a => by
    have he := congrArg Fin.val a.property
    have ha := (f a.val).isLt
    change (f a.val).val = n + i.val at he
    omega⟩
  simp only [Nat.card_of_isEmpty, Nat.zero_add]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun b => ⟨
    fun he => Fin.ext (Nat.add_left_cancel (congrArg (fun z : Fin (n + m) => z.val) he)),
    fun he => congrArg (Fin.natAdd n) he⟩)

private theorem card_vtx {Γ : List Color → List Color → Type} (I : Interp Γ)
    {a b : List Color} (D : Diagram Γ a b) :
    Nat.card (D.Vtx I) = (vertexList I D).length :=
  (Nat.card_congr (vertexEquiv I D)).trans (Nat.card_fin _)

private theorem card_fiber_comp_le {A I R : Type*} [Finite A] [Finite I]
    (origin : A → I) (row : I → R) (r : R) (B : ℕ)
    (hB : ∀ i, Nat.card {a // origin a = i} ≤ B) :
    Nat.card {a // row (origin a) = r} ≤ B * Nat.card {i // row i = r} := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have he := Equiv.sigmaSubtypeFiberEquivSubtype origin
    (p := fun a => row (origin a) = r) (q := fun i => row i = r) (fun _ => Iff.rfl)
  calc
    Nat.card {a // row (origin a) = r} =
        Nat.card (Σ i : {i // row i = r}, {a // origin a = i.val}) := (Nat.card_congr he).symm
    _ = ∑ i : {i // row i = r}, Nat.card {a // origin a = i.val} := Nat.card_sigma
    _ ≤ ∑ _i : {i // row i = r}, B := Finset.sum_le_sum (fun i _ => hB i.val)
    _ = B * Nat.card {i // row i = r} := by simp [Nat.card_eq_fintype_card, Nat.mul_comm]

/-- Each syntactic crossing owns at most the 286 vertices of its crossover implementation. -/
theorem crossingOrigin_fiber_le {Γ : List Color → List Color → Type}
    (H : ∀ {a b : List Color}, Γ a b → Diagram Prim a b) :
    ∀ {a b : List Color} (D : Diagram Γ a b)
      (h : D.checkGens (fun _ => false) = true) (i : Fin (swapCount D)),
      Nat.card {v : (planarizeAlong H D).Vtx Prim.interp // crossingOrigin H D h v = i} ≤ 286 := by
  intro a b D
  induction D with
  | gen g => intro h; cases h
  | id a => intro h i; exact i.elim0
  | swap c d =>
    intro h i
    have hc : Nat.card ((planarizeAlong H (Diagram.swap c d)).Vtx Prim.interp) ≤ 286 := by
      change Nat.card ((Crossover.diagram c d).Vtx Prim.interp) ≤ 286
      rw [card_vtx]
      exact Crossover.length_vertexList_le c d
    exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans hc
  | comp D₁ D₂ ih₁ ih₂ | tensor D₁ D₂ ih₁ ih₂ =>
    intro h i
    have h₁ := (Bool.and_eq_true_iff.mp h).1
    have h₂ := (Bool.and_eq_true_iff.mp h).2
    change Nat.card {v : (planarizeAlong H D₁).Vtx Prim.interp ⊕
        (planarizeAlong H D₂).Vtx Prim.interp //
      Sum.elim (fun v => (crossingOrigin H D₁ h₁ v).castAdd (swapCount D₂))
        (fun v => Fin.natAdd (swapCount D₁) (crossingOrigin H D₂ h₂ v)) v = i} ≤ 286
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [card_fiber_castAdd]
      exact ih₁ h₁ j
    · rw [card_fiber_natAdd]
      exact ih₂ h₂ j

namespace Embedding

private theorem sourceVertexOrigin_injective {E : Type*} (c : Port E → Color) :
    ∀ vs : List (Vertex E), Function.Injective (sourceVertexOrigin c vs) := by
  intro vs
  induction vs with
  | nil => intro v; exact v.elim
  | cons v vs ih =>
    change Function.Injective (Sum.elim (fun _ : Fin 1 => (0 : Fin (vs.length + 1)))
      (fun w => (sourceVertexOrigin c vs w).succ))
    intro x y he
    rcases x with x | x <;> rcases y with y | y
    · exact congrArg Sum.inl (Subsingleton.elim x y)
    · have hv := congrArg Fin.val he
      change 0 = (sourceVertexOrigin c vs y).val + 1 at hv
      omega
    · have hv := congrArg Fin.val he
      change (sourceVertexOrigin c vs x).val + 1 = 0 at hv
      omega
    · apply congrArg Sum.inr
      apply ih
      apply Fin.ext
      have hv := congrArg Fin.val he
      change (sourceVertexOrigin c vs x).val + 1 = (sourceVertexOrigin c vs y).val + 1 at hv
      omega

/-- An original source-list position contributes at most one planarized vertex. -/
theorem sourceVertexOrigin_fiber_le {E : Type*} (c : Port E → Color)
    (vs : List (Vertex E)) (i : Fin vs.length) :
    Nat.card {v : (planarizeAlong Cell.expand (Sources.vertices c vs).diagram).Vtx Prim.interp //
      sourceVertexOrigin c vs v = i} ≤ 1 := by
  let f : {v : (planarizeAlong Cell.expand (Sources.vertices c vs).diagram).Vtx Prim.interp //
      sourceVertexOrigin c vs v = i} → Fin 1 := fun _ => 0
  have hf : Function.Injective f := by
    intro x y _
    exact Subtype.ext (sourceVertexOrigin_injective c vs (x.property.trans y.property.symm))
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

private theorem capVertexOrigin_mem {E : Type*} (c : E → Color) :
    ∀ (es : List E) (v : (planarizeAlong Cell.expand (Sinks.caps c es).diagram).Vtx Prim.interp),
      capVertexOrigin c es v ∈ es := by
  intro es
  induction es with
  | nil => intro v; exact v.elim
  | cons e es ih =>
    intro v
    rcases v with v | v
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem e (ih v)

/-- A nonrepeated cap label contributes at most the sixteen vertices of its wire cap. -/
theorem capVertexOrigin_fiber_le {E : Type*} (c : E → Color) :
    ∀ (es : List E), es.Nodup → ∀ e : E,
      Nat.card {v : (planarizeAlong Cell.expand (Sinks.caps c es).diagram).Vtx Prim.interp //
        capVertexOrigin c es v = e} ≤ 16 := by
  intro es
  induction es with
  | nil =>
    intro _ e
    change Nat.card {v : Empty // capVertexOrigin c [] v = e} ≤ 16
    simp only [Nat.card_of_isEmpty, Nat.zero_le]
  | cons e₀ es ih =>
    intro hn e
    have hn₀ := (List.nodup_cons.mp hn).1
    have hnt := (List.nodup_cons.mp hn).2
    change Nat.card {v : (Gadgets.Wire.cap (c e₀)).Vtx Prim.interp ⊕
        (planarizeAlong Cell.expand (Sinks.caps c es).diagram).Vtx Prim.interp //
      Sum.elim (fun _ => e₀) (capVertexOrigin c es) v = e} ≤ 16
    rw [Nat.card_subtype_sum]
    simp only [Sum.elim_inl, Sum.elim_inr]
    by_cases he : e₀ = e
    · subst e
      let : IsEmpty {v : (planarizeAlong Cell.expand (Sinks.caps c es).diagram).Vtx Prim.interp //
          capVertexOrigin c es v = e₀} :=
        ⟨fun v => hn₀ (v.property ▸ capVertexOrigin_mem c es v.val)⟩
      have hc : Nat.card ((Gadgets.Wire.cap (c e₀)).Vtx Prim.interp) ≤ 16 := by
        rw [card_vtx]
        exact Gadgets.Wire.cap_length_vertexList_le (c e₀)
      have hb : Nat.card {v : (Gadgets.Wire.cap (c e₀)).Vtx Prim.interp // e₀ = e₀} ≤ 16 :=
        (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans hc
      simpa only [Nat.card_of_isEmpty, Nat.add_zero] using hb
    · let : IsEmpty {v : (Gadgets.Wire.cap (c e₀)).Vtx Prim.interp // e₀ = e} :=
        ⟨fun v => he v.property⟩
      simpa only [Nat.card_of_isEmpty, Nat.zero_add] using ih hnt e

/-- An arbitrary origin-to-row assignment has its actual vertex fibers bounded by the number of
source, cap and crossing origins assigned to that row, with their respective local constants. -/
theorem planeVertexOrigin_row_fiber_le {m : ℕ} (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    {R : Type*}
    (row : VertexOrigin vs.length m (swapCount (routing vs (color vs) hw).diagram) → R) (r : R) :
    Nat.card {v : (planeDiagram vs hw).Vtx Prim.interp // row (planeVertexOrigin vs hw v) = r} ≤
      Nat.card {i : Fin vs.length // row (.vertex i) = r} +
        16 * Nat.card {e : Fin m // row (.cap e) = r} +
        286 * Nat.card {i : Fin (swapCount (routing vs (color vs) hw).diagram) //
          row (.crossing i) = r} := by
  change Nat.card {v :
      (planarizeAlong Cell.expand (Sources.vertices (fun p => color vs p.edge) vs).diagram).Vtx
        Prim.interp ⊕
      ((planarizeAlong Cell.expand (routing vs (color vs) hw).diagram).Vtx Prim.interp ⊕
        (planarizeAlong Cell.expand (Sinks.caps (color vs) (List.finRange m)).diagram).Vtx
          Prim.interp) //
    row (Sum.elim (fun v => .vertex (sourceVertexOrigin (fun p => color vs p.edge) vs v))
      (Sum.elim
        (fun v => .crossing (crossingOrigin Cell.expand _
          (routing vs (color vs) hw).noGens v))
        (fun v => .cap (capVertexOrigin (color vs) (List.finRange m) v))) v) = r} ≤ _
  rw [Nat.card_subtype_sum, Nat.card_subtype_sum]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hs := card_fiber_comp_le (sourceVertexOrigin (fun p => color vs p.edge) vs)
    (fun i => row (.vertex i)) r 1 (sourceVertexOrigin_fiber_le _ vs)
  have hc := card_fiber_comp_le (capVertexOrigin (color vs) (List.finRange m))
    (fun e => row (.cap e)) r 16
    (capVertexOrigin_fiber_le _ _ (List.nodup_finRange m))
  have hx := card_fiber_comp_le
    (crossingOrigin Cell.expand _ (routing vs (color vs) hw).noGens)
    (fun i => row (.crossing i)) r 286
    (crossingOrigin_fiber_le Cell.expand _ (routing vs (color vs) hw).noGens)
  simp only [Nat.one_mul] at hs
  omega

/-- Every actual planarized vertex origin has the uniform local source, cap or crossover bound. -/
theorem planeVertexOrigin_fiber_le {m : ℕ} (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    (o : VertexOrigin vs.length m (swapCount (routing vs (color vs) hw).diagram)) :
    Nat.card {v : (planeDiagram vs hw).Vtx Prim.interp // planeVertexOrigin vs hw v = o} ≤
      match o with
      | .vertex _ => 1
      | .cap _ => 16
      | .crossing _ => 286 := by
  classical
  have h := planeVertexOrigin_row_fiber_le vs hw id o
  cases o <;> simpa [Nat.card_eq_fintype_card, Fintype.card_subtype_eq] using h

end Embedding

end Cslib.Complexity.NCL.Planar
