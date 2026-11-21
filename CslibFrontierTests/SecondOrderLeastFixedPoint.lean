/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Logics.SecondOrder.LeastFixedPoint

/-! # Checked fixed points on mixed second-order tuples -/

set_option linter.privateModule false

namespace CslibFrontierTests.SecondOrderLeastFixedPoint

open FirstOrder Language Cslib.Logic Cslib.Logic.SO.LFP

private def shape : Shape where
  elements := 1
  relations := 1
  arity _ := 1

private def recur {L : Language} :
    BoundedFormula Bool [shape] (L.sum (ESO.varLanguage shape.arity)) 1 :=
  .atom .head (fun _ => .var (.inr 0)) (fun i => .inr ⟨i, rfl⟩)

/-- The least solution of `X(a, R) = X(a, R)` excludes every mixed tuple. -/
example {L : Language} [L.Structure Bool] (r : L.Relations 1) :
    ¬ (BoundedFormula.lfp (s := shape) (fun _ => .var (.inl true)) (fun _ => r) recur :
      BoundedFormula Bool [] L 0).Realize (fun v => nomatch v) id Fin.elim0 := by
  have hpos : (recur (L := L)).Positive
      (Polarities.bind (Polarities.unrestricted []) shape) := by
    simp [recur, BoundedFormula.Positive, Polarities.bind]
  intro h
  have hm := (BoundedFormula.realize_lfp (s := shape) (terms := fun _ => .var (.inl true))
    (relations := fun _ => r) hpos (fun v => nomatch v) id Fin.elim0).mp h
  let F := (recur (L := L)).operator hpos (fun v => nomatch v) id Fin.elim0
  have hpre : F ∅ ⊆ ∅ := by
    intro _ hh
    exact hh
  have hfixed : F.lfp ⊆ ∅ := F.lfp_le hpre
  exact hfixed hm

private def contains {L : Language} :
    BoundedFormula Bool [shape] (L.sum (ESO.varLanguage shape.arity)) 1 :=
  let r : (L.sum (ESO.varLanguage shape.arity)).Relations 1 := .inr ⟨⟨0, by decide⟩, rfl⟩
  .ofSO (.ofFirstOrder (r.boundedFormula₁ (.var (.inr 0))))

/-- A body can test membership of its bound element in its bound relation. -/
example {L : Language} [L.Structure Bool] (r : L.Relations 1)
    (hr : Structure.RelMap r fun _ => true) :
    (BoundedFormula.lfp (s := shape) (fun _ => .var (.inl true)) (fun _ => r) contains :
      BoundedFormula Bool [] L 0).Realize (fun v => nomatch v) id Fin.elim0 := by
  have hpos : (contains (L := L)).Positive
      (Polarities.bind (Polarities.unrestricted []) shape) := trivial
  apply (BoundedFormula.realize_lfp (s := shape) (terms := fun _ => .var (.inl true))
    (relations := fun _ => r) hpos (fun v => nomatch v) id Fin.elim0).2
  let F := (contains (L := L)).operator hpos (fun v => nomatch v) id Fin.elim0
  change SO.MixedTuple.realize _ _ _ ∈ F.lfp
  rw [← F.map_lfp]
  change Structure.RelMap r _
  convert hr using 1
  apply iff_of_eq
  congr 1
  funext i
  change Fin 1 at i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

/-- A negated recursive atom is excluded by the positivity check. -/
example {L : Language} (r : L.Relations 1) :
    ¬ (BoundedFormula.lfp (s := shape) (fun _ => .var (.inl true)) (fun _ => r)
      (.imp recur (.ofSO (.ofFirstOrder ⊥))) :
      BoundedFormula Bool [] L 0).WellFormed := by
  simp [recur, BoundedFormula.WellFormed, BoundedFormula.Positive, Polarities.bind,
    Polarities.flip]

end CslibFrontierTests.SecondOrderLeastFixedPoint
