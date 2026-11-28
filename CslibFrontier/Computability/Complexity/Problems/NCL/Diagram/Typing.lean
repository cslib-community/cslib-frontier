/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word

/-!
# Type checking diagram words

The type checker follows the colors on the current wires. A generator consumes its declared
input colors and creates its output colors; a crossing exchanges two existing wires.

## Main definitions

* `Cslib.Complexity.NCL.Slice.typeRun`: check one layer on a color stack.
* `Cslib.Complexity.NCL.Word.WellTyped`: a word transforms one boundary into another.

## Main results

* `Cslib.Complexity.NCL.Diagram.wellTyped_toWord`: every emitted diagram word is well typed.
-/

public section

namespace Cslib.Complexity.NCL

/-- Check a layer against the current wire colors and return the resulting colors. -/
@[expose] def Slice.typeRun : Slice → List Color → Option (List Color)
  | .gen k a b _, cs =>
    if k + a.length ≤ cs.length ∧ (cs.drop k).take a.length = a then
      some (cs.take k ++ b ++ cs.drop (k + a.length))
    else none
  | .swap k, cs =>
    match cs[k]?, cs[k + 1]? with
    | some x, some y => some (cs.take k ++ [y, x] ++ cs.drop (k + 2))
    | _, _ => none

/-- Check a word by threading the current color stack through its layers. -/
@[expose] def Word.typeRun (w : Word) (cs : List Color) : Option (List Color) :=
  w.foldlM (fun cs sl => sl.typeRun cs) cs

/-- The word checks from the input boundary to the output boundary. -/
@[expose] def Word.WellTyped (w : Word) (a b : List Color) : Prop := w.typeRun a = some b

instance (w : Word) (a b : List Color) : Decidable (w.WellTyped a b) :=
  inferInstanceAs (Decidable (w.typeRun a = some b))

theorem Word.typeRun_append (w₁ w₂ : Word) (cs : List Color) :
    (w₁ ++ w₂).typeRun cs = (w₁.typeRun cs).bind w₂.typeRun := by
  exact List.foldlM_append ..

private theorem Slice.typeRun_gen (P a b S : List Color) (k : ℕ) (hP : P.length = k)
    (vs : List (Vertex (Fin a.length ⊕ Fin b.length))) :
    (Slice.gen k a b vs).typeRun (P ++ a ++ S) = some (P ++ b ++ S) := by
  have ha : ((P ++ a ++ S).drop k).take a.length = a := by
    rw [List.append_assoc]
    simp [← hP]
  rw [Slice.typeRun, ite_eq_left ⟨by simp only [List.length_append, hP]; omega, ha⟩,
    show (P ++ a ++ S).take k = P from List.append_assoc P a S ▸ List.take_left' hP,
    List.drop_left' (by simp [hP])]

private theorem Slice.typeRun_swap (P S : List Color) (x y : Color) (k : ℕ)
    (hP : P.length = k) :
    (Slice.swap k).typeRun (P ++ [x, y] ++ S) = some (P ++ [y, x] ++ S) := by
  simp only [Slice.typeRun, show (P ++ [x, y] ++ S)[k]? = some x by simp [hP],
    show (P ++ [x, y] ++ S)[k + 1]? = some y by simp [hP],
    show (P ++ [x, y] ++ S).take k = P from List.append_assoc P [x, y] S ▸ List.take_left' hP,
    show (P ++ [x, y] ++ S).drop (k + 2) = S from List.drop_left' (by simp [hP])]

namespace Diagram

variable {Γ : List Color → List Color → Type} (I : Interp Γ)

/-- A diagram checks on any matching segment of a larger color stack. -/
theorem typeRun_toWord {a b : List Color} (D : Diagram Γ a b) (k : ℕ) (P S : List Color)
    (hP : P.length = k) :
    (D.toWord I k).typeRun (P ++ a ++ S) = some (P ++ b ++ S) := by
  induction D generalizing k P S with
  | gen g =>
    simpa [toWord, Word.typeRun] using Slice.typeRun_gen P _ _ S k hP (I.verts g)
  | id _ => rfl
  | swap x y =>
    simpa [toWord, Word.typeRun] using Slice.typeRun_swap P S x y k hP
  | comp D₁ D₂ ih₁ ih₂ =>
    rw [toWord, Word.typeRun_append, ih₁ k P S hP, Option.bind_some, ih₂ k P S hP]
  | @tensor a b c d D₁ D₂ ih₁ ih₂ =>
    have h₁ := ih₁ k P (c ++ S) hP
    have h₂ := ih₂ (k + b.length) (P ++ b) S (by simp [hP])
    simp only [List.append_assoc] at h₁ h₂ ⊢
    rw [toWord, Word.typeRun_append, h₁, Option.bind_some, h₂]

/-- The word emitted from a diagram has its declared input and output types. -/
theorem wellTyped_toWord {a b : List Color} (D : Diagram Γ a b) :
    (D.toWord I 0).WellTyped a b := by
  simpa only [Word.WellTyped, List.nil_append, List.append_nil] using
    typeRun_toWord I D 0 [] [] rfl

end Diagram

end Cslib.Complexity.NCL
