/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Measure
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Interface
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Activation
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Simulation

/-!
# Routing syntactic swaps through wire relations

Replace every swap by two independent W vertices. The first segment of each original edge is
its original creation point; new segments are labeled by following the routed wires. Copying
these labels extends an old orientation, and reading the first segments abstracts a new one.

For forward generators, abstract legality follows inductively from the output direction bounds.
Canonical extensions of an old reversal are comparable, so creation-order activation supplies
the routed path. This construction applies to arbitrary open diagrams.

## Main definitions

* `Cslib.Complexity.NCL.Planar.Routed`: source generators and explicit crossings.
* `Cslib.Complexity.NCL.Planar.Route.diagram`: the routed syntax.
* `Cslib.Complexity.NCL.Planar.Route.enc`, `Cslib.Complexity.NCL.Planar.Route.abs`: the maps.

## Main results

* `Cslib.Complexity.NCL.Planar.Route.simulation`: the reachability simulation.
* `Cslib.Complexity.NCL.Planar.Route.planar`: routed syntax contains no swaps.
* `Cslib.Complexity.NCL.Planar.Route.forget_bottom`: wire labels follow the original drawing.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Planar

/-- Source generators together with explicit crossing wire relations. -/
inductive Routed (Γ : List Color → List Color → Type) : List Color → List Color → Type
  | base {a b : List Color} (g : Γ a b) : Routed Γ a b
  | cross (c d : Color) : Routed Γ [c, d] [d, c]

namespace Routed

variable {Γ : List Color → List Color → Type}

/-- Keep the source vertex data and interpret a crossing as two independent W vertices. -/
@[expose] def interp (I : Diagram.Interp Γ) : Diagram.Interp (Routed Γ) := ⟨fun
  | .base g => I.verts g
  | .cross c d => Prim.cross c d⟩

private theorem forward {I : Diagram.Interp Γ} (hI : I.Forward) : (interp I).Forward := by
  rintro a b (g | ⟨c, d⟩) v hv p hp
  · exact hI g v hv p hp
  · simp only [interp, Prim.cross, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp <;>
      rcases hp with rfl | rfl <;> rfl

end Routed

namespace Route

open Diagram
variable {Γ : List Color → List Color → Type} {a b c d : List Color}

/-- Replace each syntactic swap by a crossing generator, preserving the rest of the drawing. -/
abbrev diagram : {a b : List Color} → Diagram Γ a b → Diagram (Routed Γ) a b
  | _, _, .gen g => .gen (.base g)
  | _, _, .id a => .id a
  | _, _, .swap c d => .gen (.cross c d)
  | _, _, .comp D₁ D₂ => (diagram D₁).comp (diagram D₂)
  | _, _, .tensor D₁ D₂ => (diagram D₁).tensor (diagram D₂)

/-- The original wire births among all wires created by the routed diagram. -/
@[expose] def originalInner : {a b : List Color} → (D : Diagram Γ a b) → D.Inner → (diagram D).Inner
  | _, _, .gen _, e => e
  | _, _, .id _, e => e.elim
  | _, _, .swap .., e => e.elim
  | _, _, .comp D₁ D₂, e => Sum.map (originalInner D₁) (originalInner D₂) e
  | _, _, .tensor D₁ D₂, e => Sum.map (originalInner D₁) (originalInner D₂) e

/-- The first segment of each original edge. -/
@[expose] def original (D : Diagram Γ a b) : D.Edge → (diagram D).Edge :=
  Sum.map id (originalInner D)

private theorem originalInner_injective (D : Diagram Γ a b) :
    Function.Injective (originalInner D) := by
  induction D with
  | gen _ => exact Function.injective_id
  | id _ | swap _ _ => exact fun e _ _ => e.elim
  | comp _ _ ih₁ ih₂ | tensor _ _ ih₁ ih₂ => exact ih₁.sumMap ih₂

private theorem original_injective (D : Diagram Γ a b) : Function.Injective (original D) :=
  Function.injective_id.sumMap (originalInner_injective D)

/-- Label each routed segment by the original edge that it subdivides. -/
@[expose] def forget : {a b : List Color} → (D : Diagram Γ a b) → (diagram D).Edge → D.Edge
  | _, _, .gen _ => _root_.id
  | _, _, .id _ => _root_.id
  | _, _, .swap .. => Sum.elim Sum.inl (fun j => Sum.inl j.rev)
  | _, _, .comp D₁ D₂ => Sum.elim Sum.inl (Sum.elim
      (fun e => compLeft D₁ D₂ (forget D₁ (.inr e)))
      (fun e => compRight D₁ D₂ (forget D₂ (.inr e))))
  | _, _, .tensor D₁ D₂ => Sum.elim Sum.inl (Sum.elim
      (fun e => tensorLeft D₁ D₂ (forget D₁ (.inr e)))
      (fun e => tensorRight D₁ D₂ (forget D₂ (.inr e))))

/-- Top wires retain their original labels. -/
@[simp] private theorem forget_top (D : Diagram Γ a b) (i : Fin a.length) :
    forget D (.inl i) = .inl i := by cases D <;> rfl

private theorem forget_compLeft (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c) (e : (diagram D₁).Edge) :
    forget (D₁.comp D₂) (compLeft (diagram D₁) (diagram D₂) e) =
      compLeft D₁ D₂ (forget D₁ e) := by
  cases e with
  | inl i => exact congrArg (compLeft D₁ D₂) (forget_top D₁ i).symm
  | inr _ => rfl

private theorem forget_tensorLeft (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (e : (diagram D₁).Edge) :
    forget (D₁.tensor D₂) (tensorLeft (diagram D₁) (diagram D₂) e) =
      tensorLeft D₁ D₂ (forget D₁ e) := by
  cases e with
  | inl i => exact congrArg (tensorLeft D₁ D₂) (forget_top D₁ i).symm
  | inr _ => rfl

private theorem forget_tensorRight (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (e : (diagram D₂).Edge) :
    forget (D₁.tensor D₂) (tensorRight (diagram D₁) (diagram D₂) e) =
      tensorRight D₁ D₂ (forget D₂ e) := by
  cases e with
  | inl i => exact congrArg (tensorRight D₁ D₂) (forget_top D₂ i).symm
  | inr _ => rfl

/-- Each output segment has the label of the original output wire. -/
theorem forget_bottom (D : Diagram Γ a b) (j : Fin b.length) :
    forget D ((diagram D).bottom j) = D.bottom j := by
  induction D with
  | gen _ | id _ | swap _ _ => rfl
  | comp D₁ D₂ ih₁ ih₂ =>
    change forget (D₁.comp D₂) (((diagram D₁).comp (diagram D₂)).bottom j) = _
    rw [bottom_comp, bottom_comp]
    rcases he : (diagram D₂).bottom j with k | e
    · change forget (D₁.comp D₂) (compLeft (diagram D₁) (diagram D₂) ((diagram D₁).bottom k)) = _
      have hj := he ▸ ih₂ j
      rw [forget_top] at hj
      rw [forget_compLeft, ih₁, ← hj]
      rfl
    · change compRight D₁ D₂ (forget D₂ (.inr e)) = _
      rw [← he, ih₂]
  | @tensor a b c d D₁ D₂ ih₁ ih₂ =>
    rcases (List.appendIndexEquiv b d).surjective j with ⟨k | k, rfl⟩
    · rw [bottom_tensor_left, forget_tensorLeft, ih₁, bottom_tensor_left]
    · rw [bottom_tensor_right, forget_tensorRight, ih₂, bottom_tensor_right]

private theorem forget_compRight (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c) (e : (diagram D₂).Edge) :
    forget (D₁.comp D₂) (compRight (diagram D₁) (diagram D₂) e) =
      compRight D₁ D₂ (forget D₂ e) := by
  cases e with
  | inl i =>
    change forget (D₁.comp D₂) (compLeft (diagram D₁) (diagram D₂) ((diagram D₁).bottom i)) = _
    rw [forget_compLeft, forget_bottom, forget_top]
    rfl
  | inr e => rfl

private theorem forget_original (D : Diagram Γ a b) (e : D.Edge) : forget D (original D e) = e := by
  induction D with
  | gen _ => cases e <;> rfl
  | id _ | swap _ _ => cases e with | inl _ => rfl | inr e => exact e.elim
  | comp D₁ D₂ ih₁ ih₂ =>
    rcases e with i | e | e
    · rfl
    · exact congrArg (compLeft D₁ D₂) (ih₁ (.inr e))
    · exact congrArg (compRight D₁ D₂) (ih₂ (.inr e))
  | tensor D₁ D₂ ih₁ ih₂ =>
    rcases e with i | e | e
    · rfl
    · exact congrArg (tensorLeft D₁ D₂) (ih₁ (.inr e))
    · exact congrArg (tensorRight D₁ D₂) (ih₂ (.inr e))

/-- Give each routed segment the direction of its original edge. -/
@[expose] def enc (D : Diagram Γ a b) (s : D.Edge → Bool) : (diagram D).Edge → Bool := s ∘ forget D

/-- Restriction to the upper routed diagram commutes with encoding. -/
theorem enc_compLeft (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c)
    (s : (D₁.comp D₂).Edge → Bool) :
    enc (D₁.comp D₂) s ∘ compLeft (diagram D₁) (diagram D₂) =
      enc D₁ (s ∘ compLeft D₁ D₂) :=
  funext fun e => congrArg s (forget_compLeft D₁ D₂ e)

/-- Restriction to the lower routed diagram commutes with encoding. -/
theorem enc_compRight (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c)
    (s : (D₁.comp D₂).Edge → Bool) :
    enc (D₁.comp D₂) s ∘ compRight (diagram D₁) (diagram D₂) =
      enc D₂ (s ∘ compRight D₁ D₂) :=
  funext fun e => congrArg s (forget_compRight D₁ D₂ e)

/-- Restriction to the left routed diagram commutes with encoding. -/
theorem enc_tensorLeft (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (s : (D₁.tensor D₂).Edge → Bool) :
    enc (D₁.tensor D₂) s ∘ tensorLeft (diagram D₁) (diagram D₂) =
      enc D₁ (s ∘ tensorLeft D₁ D₂) :=
  funext fun e => congrArg s (forget_tensorLeft D₁ D₂ e)

/-- Restriction to the right routed diagram commutes with encoding. -/
theorem enc_tensorRight (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (s : (D₁.tensor D₂).Edge → Bool) :
    enc (D₁.tensor D₂) s ∘ tensorRight (diagram D₁) (diagram D₂) =
      enc D₂ (s ∘ tensorRight D₁ D₂) :=
  funext fun e => congrArg s (forget_tensorRight D₁ D₂ e)

/-- Read the first segment of each original edge. -/
@[expose]
def abs (D : Diagram Γ a b) (t : (diagram D).Edge → Bool) : D.Edge → Bool := t ∘ original D

private theorem abs_enc (D : Diagram Γ a b) (s : D.Edge → Bool) : abs D (enc D s) = s :=
  funext fun e => congrArg s (forget_original D e)

private theorem legal_enc (I : Interp Γ) (D : Diagram Γ a b) {s : D.Edge → Bool}
    (hs : (D.graph I).Legal s) : ((diagram D).graph (Routed.interp I)).Legal (enc D s) := by
  induction D with
  | gen g => exact hs
  | id _ => exact fun v => v.elim
  | swap c d =>
    exact (genLegal_iff (Prim.cross c d) _).1 ((Prim.genLegal_cross c d _).2 ⟨le_rfl, le_rfl⟩)
  | comp D₁ D₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := (legal_comp_iff D₁ D₂ s).1 hs
    exact (legal_comp_iff (diagram D₁) (diagram D₂) _).2
      ⟨(enc_compLeft D₁ D₂ s).symm ▸ ih₁ h₁, (enc_compRight D₁ D₂ s).symm ▸ ih₂ h₂⟩
  | tensor D₁ D₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := (legal_tensor_iff D₁ D₂ s).1 hs
    exact (legal_tensor_iff (diagram D₁) (diagram D₂) _).2
      ⟨(enc_tensorLeft D₁ D₂ s).symm ▸ ih₁ h₁, (enc_tensorRight D₁ D₂ s).symm ▸ ih₂ h₂⟩

private def Sound (I : Interp Γ) (D : Diagram Γ a b) : Prop :=
  ∀ {s : D.Edge → Bool} {t : (diagram D).Edge → Bool},
    ((diagram D).graph (Routed.interp I)).Legal t →
    (∀ i, t (.inl i) ≤ s (.inl i)) →
    (∀ e, t (.inr (originalInner D e)) = s (.inr e)) →
    (D.graph I).Legal s ∧ ∀ j, t ((diagram D).bottom j) ≤ s (D.bottom j)

private theorem sound_comp {I : Interp Γ} (D₁ : Diagram Γ a b) (D₂ : Diagram Γ b c)
    (ih₁ : Sound I D₁) (ih₂ : Sound I D₂) : Sound I (D₁.comp D₂) := by
  intro s t ht htop hborn
  obtain ⟨h₁, h₂⟩ := (legal_comp_iff (diagram D₁) (diagram D₂) t).1 ht
  have hr₁ := ih₁ (s := s ∘ compLeft D₁ D₂) h₁ htop (fun e => hborn (.inl e))
  have hr₂ := ih₂ (s := s ∘ compRight D₁ D₂) h₂ hr₁.2 (fun e => hborn (.inr e))
  refine ⟨(legal_comp_iff D₁ D₂ s).2 ⟨hr₁.1, hr₂.1⟩, fun j => ?_⟩
  rw [bottom_comp, bottom_comp]
  exact hr₂.2 j

private theorem sound_tensor {I : Interp Γ} (D₁ : Diagram Γ a b) (D₂ : Diagram Γ c d)
    (ih₁ : Sound I D₁) (ih₂ : Sound I D₂) : Sound I (D₁.tensor D₂) := by
  intro s t ht htop hborn
  obtain ⟨h₁, h₂⟩ := (legal_tensor_iff (diagram D₁) (diagram D₂) t).1 ht
  have hr₁ := ih₁ (s := s ∘ tensorLeft D₁ D₂) h₁
    (fun i => htop ((List.appendIndexEquiv a c) (.inl i)))
    (fun e => hborn (.inl e))
  have hr₂ := ih₂ (s := s ∘ tensorRight D₁ D₂) h₂
    (fun i => htop ((List.appendIndexEquiv a c) (.inr i))) (fun e => hborn (.inr e))
  refine ⟨(legal_tensor_iff D₁ D₂ s).2 ⟨hr₁.1, hr₂.1⟩, fun j => ?_⟩
  rcases (List.appendIndexEquiv b d).surjective j with ⟨k | k, rfl⟩
  · rw [bottom_tensor_left, bottom_tensor_left]
    exact hr₁.2 k
  · rw [bottom_tensor_right, bottom_tensor_right]
    exact hr₂.2 k

private theorem sound_bound {I : Interp Γ} (hI : I.Forward) (D : Diagram Γ a b) :
    Sound I D := by
  induction D with
  | gen g =>
    exact fun ht htop hborn => ⟨legal_top_mono hI (gen g) ht htop hborn, fun j => (hborn j).le⟩
  | id _ => exact fun _ htop _ => ⟨fun v => v.elim, htop⟩
  | swap c d =>
    intro s t ht htop _
    have hc := (Prim.genLegal_cross c d t).1 ((genLegal_iff (Prim.cross c d) t).2 ht)
    exact ⟨fun v => v.elim,
      Fin.cases (hc.2.trans (htop 1)) (Fin.cases (hc.1.trans (htop 0)) fun k => k.elim0)⟩
  | comp D₁ D₂ ih₁ ih₂ => exact sound_comp D₁ D₂ ih₁ ih₂
  | tensor D₁ D₂ ih₁ ih₂ => exact sound_tensor D₁ D₂ ih₁ ih₂

private theorem legal_abs {I : Interp Γ} (hI : I.Forward) (D : Diagram Γ a b)
    {t : (diagram D).Edge → Bool} (ht : ((diagram D).graph (Routed.interp I)).Legal t) :
    (D.graph I).Legal (abs D t) :=
  (sound_bound hI D ht (fun _ => le_rfl) (fun _ => rfl)).1

private theorem step_abs {I : Interp Γ} (hI : I.Forward) (D : Diagram Γ a b)
    {s t : (diagram D).Edge → Bool} (h : ((diagram D).graph (Routed.interp I)).Step s t) :
    Relation.ReflGen (D.graph I).Step (abs D s) (abs D t) := by
  obtain ⟨hs, ht, y, rfl⟩ := h
  by_cases hy : y ∈ Set.range (original D)
  · obtain ⟨e, rfl⟩ := hy
    exact .single ⟨legal_abs hI D hs, legal_abs hI D ht, e,
      reverse_comp_of_injective (original_injective D) s e⟩
  · rw [show abs D (reverse s y) = abs D s from
      reverse_comp_of_not_mem_range s fun e h => hy ⟨e, h⟩]

private theorem reachable_enc_reverse {I : Interp Γ} (hI : I.Forward) (D : Diagram Γ a b)
    (s : D.Edge → Bool) (e : D.Edge) (he : s e = false)
    (hs : (D.graph I).Legal s) (ht : (D.graph I).Legal (reverse s e)) :
    ((diagram D).graph (Routed.interp I)).Reachable (enc D s) (enc D (reverse s e)) := by
  have hle : ∀ y, enc D s y ≤ enc D (reverse s e) y := fun y => by
    change s (forget D y) ≤ reverse s e (forget D y)
    by_cases hy : forget D y = e
    · simp [hy, reverse_self, he]
    · rw [reverse_of_ne s hy]
  exact Relation.ReflTransGen.mono (fun _ _ h => h.2) _ _
    (reachable_of_le_within (Routed.forward hI) (diagram D) (legal_enc I D hs)
      (legal_enc I D ht) hle (P := fun _ => True) fun _ _ _ => trivial)

private theorem step_enc {I : Interp Γ} (hI : I.Forward) (D : Diagram Γ a b)
    {s t : D.Edge → Bool} (h : (D.graph I).Step s t) :
    ((diagram D).graph (Routed.interp I)).Reachable (enc D s) (enc D t) := by
  obtain ⟨hs, ht, e, rfl⟩ := h
  cases he : s e
  · exact reachable_enc_reverse hI D s e he hs ht
  · simpa only [reverse_reverse] using (reachable_enc_reverse hI D (reverse s e) e
      (by simp [he]) ht (by simpa only [reverse_reverse] using hs)).symm

/-- Replacing swaps by wire relations preserves reachability for forward generators. -/
@[expose] def simulation {I : Interp Γ} (hI : I.Forward) (D : Diagram Γ a b) :
    ConstraintGraph.Simulation (D.graph I) ((diagram D).graph (Routed.interp I)) where
  abs := abs D
  enc := enc D
  abs_enc := by exact abs_enc D
  legal_abs := by exact legal_abs hI D
  legal_enc := by exact legal_enc I D
  step_abs := by exact step_abs hI D
  step_enc := by exact step_enc hI D

end Route
end Cslib.Complexity.NCL.Planar

namespace Cslib.Complexity.NCL.Planar

open Diagram
variable {Γ : List Color → List Color → Type} {a b : List Color}

/-- Routing replaces every syntactic swap by a generator. -/
theorem Route.planar (D : Diagram Γ a b) : (Route.diagram D).Planar := by
  induction D with
  | gen _ | id _ | swap _ _ => trivial
  | comp _ _ ih₁ ih₂ | tensor _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩

end Cslib.Complexity.NCL.Planar
