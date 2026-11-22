/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Labeling

/-!
# Legal configurations with prescribed boundary directions

`Realization` packages an explicit orientation, its legality, and the directions on both
boundaries. Stacking and juxtaposition glue these witnesses using `glueComp` and `glueTensor`.
This constructs initial configurations of parametric circuits from fixed local configurations.

## Main definitions

* `Cslib.Complexity.NCL.Diagram.Realization`: a legal orientation with prescribed boundaries.
* `Cslib.Complexity.NCL.Diagram.Realization.comp`,
  `Cslib.Complexity.NCL.Diagram.Realization.tensor`: compose explicit configurations.
* `Cslib.Complexity.NCL.Diagram.Realization.zeros`: the constant-false configuration.

## Main results

* `Cslib.Complexity.NCL.Diagram.Realization.comp_orient_compLeft`,
  `Cslib.Complexity.NCL.Diagram.Realization.comp_orient_compRight`: stacking preserves the
  orientations of both parts.

## References

* The application to constraint logic follows [Hearn and Demaine][HearnDemaine2005].
-/

public section

namespace Cslib.Complexity.NCL.Diagram

variable {Γ : List Color → List Color → Type} {I : Interp Γ} {a b c d : List Color}

/-- An explicit legal orientation of a diagram with the given top and bottom directions. -/
structure Realization (I : Interp Γ) (D : Diagram Γ a b) (x y : List Bool) where
  /-- The direction of every edge. -/
  orient : D.Edge → Bool
  /-- Every vertex satisfies its inflow constraint. -/
  legal : (D.graph I).Legal orient
  /-- The prescribed top directions. -/
  top_eq : D.topList orient = x
  /-- The prescribed bottom directions. -/
  bot_eq : D.botList orient = y

namespace Realization

variable {D : Diagram Γ a b} {x y z : List Bool}

/-- Read an incoming wire from its prescribed boundary list. -/
theorem orient_top (s : Realization I D x y) (i : Fin a.length) :
    s.orient (.inl i) = x[i.val]! := by
  calc
    _ = (D.topList s.orient)[i.val]! := by
      simp only [topList, List.getElem!_eq_getElem?_getD, List.getElem?_ofFn,
        dite_eq_left i.isLt, Option.getD_some, Function.comp_apply, Fin.eta]
    _ = _ := congrArg (fun xs => xs[i.val]!) s.top_eq

private def labeling {D : Diagram Γ a b} (s : Realization I D x y) : Labeling D x y :=
  ⟨s.orient, s.top_eq, s.bot_eq⟩

private theorem agrees {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c}
    (s : Realization I D₁ x y) (t : Realization I D₂ y z) (j : Fin b.length) :
    t.orient (.inl j) = s.orient (D₁.bottom j) :=
  congrFun (List.ofFn_inj.1 (t.top_eq.trans s.bot_eq.symm)) j

/-- Stack configurations that agree on their shared boundary. -/
@[expose] def comp {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c}
    (s : Realization I D₁ x y) (t : Realization I D₂ y z) :
    Realization I (D₁.comp D₂) x z where
  orient := glueComp D₁ D₂ s.orient t.orient
  legal := by exact legal_glueComp s.legal t.legal (agrees s t)
  top_eq := by exact ((labeling s).comp (labeling t)).top_eq
  bot_eq := by exact ((labeling s).comp (labeling t)).bot_eq

@[simp] theorem comp_orient_compLeft {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c}
    (s : Realization I D₁ x y) (t : Realization I D₂ y z) :
    (s.comp t).orient ∘ compLeft D₁ D₂ = s.orient :=
  funext fun e => glueComp_compLeft _ _ _ _ e

@[simp] theorem comp_orient_compRight {D₁ : Diagram Γ a b} {D₂ : Diagram Γ b c}
    (s : Realization I D₁ x y) (t : Realization I D₂ y z) :
    (s.comp t).orient ∘ compRight D₁ D₂ = t.orient :=
  funext fun e => glueComp_compRight _ _ _ _ (agrees s t) e

/-- Juxtapose two configurations. -/
@[expose] def tensor {D₁ : Diagram Γ a b} {D₂ : Diagram Γ c d} {x₁ y₁ x₂ y₂ : List Bool}
    (s : Realization I D₁ x₁ y₁) (t : Realization I D₂ x₂ y₂) :
    Realization I (D₁.tensor D₂) (x₁ ++ x₂) (y₁ ++ y₂) where
  orient := glueTensor D₁ D₂ s.orient t.orient
  legal := legal_glueTensor s.legal t.legal
  top_eq := by exact ((labeling s).tensor (labeling t)).top_eq
  bot_eq := by exact ((labeling s).tensor (labeling t)).bot_eq

@[simp] theorem tensor_orient_tensorLeft {D₁ : Diagram Γ a b} {D₂ : Diagram Γ c d}
    {x₁ y₁ x₂ y₂ : List Bool} (s : Realization I D₁ x₁ y₁) (t : Realization I D₂ x₂ y₂) :
    (s.tensor t).orient ∘ tensorLeft D₁ D₂ = s.orient :=
  funext fun e => glueTensor_tensorLeft _ _ _ _ e

@[simp] theorem tensor_orient_tensorRight {D₁ : Diagram Γ a b} {D₂ : Diagram Γ c d}
    {x₁ y₁ x₂ y₂ : List Bool} (s : Realization I D₁ x₁ y₁) (t : Realization I D₂ x₂ y₂) :
    (s.tensor t).orient ∘ tensorRight D₁ D₂ = t.orient :=
  funext fun e => glueTensor_tensorRight _ _ _ _ e

/-- Straight wires carrying the given directions. -/
@[expose] def id (a : List Color) (x : List Bool) (h : x.length = a.length) :
    Realization I (Diagram.id a) x x where
  orient := Sum.elim (fun i => x.get (i.cast h.symm)) Empty.elim
  legal := fun v => v.elim
  top_eq := by exact (Labeling.id (Γ := Γ) a x h).top_eq
  bot_eq := by exact (Labeling.id (Γ := Γ) a x h).bot_eq

/-- A crossing exchanges the directions of its two wires. -/
@[expose] def swap (a b : Color) (x y : Bool) :
    Realization I (Diagram.swap a b) [x, y] [y, x] where
  orient := Sum.elim (fun i => if i.val = 0 then x else y) Empty.elim
  legal := fun v => v.elim
  top_eq := rfl
  bot_eq := rfl

/-- Route a wire left across a bundle, preserving all directions. -/
@[expose] def moveLeft (x : Color) (bit : Bool) (r : List Color) (rs : List Bool)
    (hrs : rs.length = r.length) : (l : List Color) → (ls : List Bool) →
    ls.length = l.length →
    Realization I (Diagram.moveLeft l x r) (ls ++ bit :: rs) (bit :: (ls ++ rs))
  | [], [], _ => .id _ _ (by simp [hrs])
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | y :: l, b :: ls, h => by
    have hfirst := (Realization.id (I := I) [y] [b] rfl).tensor
      (moveLeft x bit r rs hrs l ls (Nat.succ_injective h))
    have hlast := (swap y x b bit).tensor
      (Realization.id (I := I) (l ++ r) (ls ++ rs)
        (by simp [Nat.succ_injective h, hrs]))
    exact hfirst.comp hlast

/-- Use a legal constant-false orientation, recording both boundary readings. -/
@[expose] def zeros (D : Diagram Γ a b) (h : (D.graph I).Legal (fun _ => false)) :
    Realization I D (List.replicate a.length false) (List.replicate b.length false) where
  orient := fun _ => false
  legal := h
  top_eq := by simp [topList, Function.comp_def]
  bot_eq := by simp [botList, Function.comp_def]

end Realization

end Cslib.Complexity.NCL.Diagram
