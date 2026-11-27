/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Segment

/-!
# Translating finite polygonal routes

Translation acts on every listed point and every actual segment, preserves the route
parameter and its two ends, and leaves outgoing germs unchanged.

## Main results

* `Cslib.Polygonal.Route.translate_line`: literal translation of a single cut line.
* `Cslib.Polygonal.Route.support_translate`: the full translated support is the translated image.
-/

public section

namespace Cslib.Polygonal.Route

/-- Translate every point of a finite polygonal route by the same plane vector. -/
@[expose] def translate (p : Route) (z : ℂ) : Route where
  bends := p.bends
  point := fun i => z + p.point i

/-- Translation commutes with the actual affine segment evaluation. -/
@[simp] theorem eval_translate (p : Route) (z : ℂ) (i : Fin p.segments) (t : ℝ) :
    (p.translate z).eval i t = z + p.eval i t := by
  simp only [eval, translate, AffineMap.lineMap_apply_module', add_sub_add_left_eq_sub]
  ac_rfl

/-- Translation moves either endpoint by the same plane vector. -/
@[simp] theorem endpoint_translate (p : Route) (z : ℂ) (b : Bool) :
    (p.translate z).endpoint b = z + p.endpoint b := by
  cases b <;> rfl

/-- Translation preserves the actual outgoing end vectors, including both loop ends. -/
@[simp] theorem germ_translate (p : Route) (z : ℂ) (b : Bool) :
    (p.translate z).germ b = p.germ b := by
  cases b <;> simp only [germ, translate, start, finish, Bool.false_eq_true, ↓reduceIte,
    add_sub_add_left_eq_sub]
  rfl

/-- Translating a literal one-segment cut retains that one-segment representation. -/
theorem translate_line (a b z : ℂ) :
    (line a b).translate z = line (z + a) (z + b) := by
  unfold translate line
  congr 1
  funext i
  change z + (if i = 0 then a else b) = if i = 0 then z + a else z + b
  split <;> rfl

/-- Translation carries the entire continuous support to its translated image. -/
theorem support_translate (p : Route) (z : ℂ) :
    (p.translate z).support = (fun w => z + w) '' p.support := by
  ext w
  constructor
  · intro hw
    obtain ⟨i, t, ht, heq⟩ := ((p.translate z).mem_support_iff w).mp hw
    refine ⟨p.eval i t, p.at_mem_support i ht, ?_⟩
    exact (eval_translate p z i t).symm.trans heq
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨i, t, ht, heq⟩ := (p.mem_support_iff v).mp hv
    exact ((p.translate z).mem_support_iff _).mpr
      ⟨i, t, ht, (eval_translate p z i t).trans (congrArg (fun x => z + x) heq)⟩

/-- Translating a simple route preserves simplicity at every real segment parameter. -/
theorem IsSimple.translate {p : Route} (hp : p.IsSimple) (z : ℂ) :
    (p.translate z).IsSimple := by
  intro i j s t hs ht heq
  change Fin p.segments at i j
  rw [eval_translate p z i s, eval_translate p z j t, add_right_inj] at heq
  exact hp i j s t hs ht heq

end Cslib.Polygonal.Route
